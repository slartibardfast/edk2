/*
Copyright (c) 2022-2023 xCuri0 <zkqri0@gmail.com>
Copyright (c) 2026 David Connolly <david@connol.ly>
SPDX-License-Identifier: MIT

Developed with assistance from Claude (Anthropic)

ReBarDXE v7 - ECAM with BAR relocation + in-place growth + eviction

Strategy:
  At ReadyToBoot we first build a map of every above-4G MMIO region
  on the PCI bus.  Then for each ReBAR-capable device:

    - "Large" BARs (VRAM, >= REBAR_MIN_SIZE_IDX): resize and relocate
      to fresh naturally-aligned addresses in high MMIO space.

    - "Small" BARs (doorbell/register, < REBAR_MIN_SIZE_IDX): attempt
      to grow IN-PLACE by checking the collision map for free room above
      the current base, and verifying natural alignment.  The GOP driver
      holds live pointers into these BARs, so they must not move.

  New in v7: when in-place growth collides with small non-ReBAR BARs
  on bus 0 (e.g. PCH SMBus/HDA/XHCI), those colliders are evicted to
  below-4G MMIO space before retrying.  This clears the growth path
  without touching display-critical BARs, and actually fixes devices
  like XHCI that shouldn't be above 4G in the first place.

  Bridge prefetchable windows are updated to cover both relocated and
  in-place-grown BARs.  The GOP FrameBufferBase is patched if BAR0
  was relocated.
*/

#include <Uefi.h>
#include <Library/UefiLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/DebugLib.h>
#include <Library/IoLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/PrintLib.h>
#include <IndustryStandard/Pci.h>
#include <IndustryStandard/Acpi.h>
#include <Protocol/GraphicsOutput.h>
#include <Guid/Acpi.h>
#include <Guid/EventGroup.h>

/* ------------------------------------------------------------------ */
/*  PCI Extended Capability helpers                                    */
/* ------------------------------------------------------------------ */

#define PCI_EXT_CAP_ID(header)      ((header) & 0x0000ffff)
#define PCI_EXT_CAP_NEXT(header)    (((header) >> 20) & 0xffc)

#define PCI_EXT_CAP_ID_REBAR       0x15
#define PCI_REBAR_CAP              0x04
#define PCI_REBAR_CTRL             0x08
#define PCI_REBAR_CAP_SIZES        0x00FFFFF0
#define PCI_REBAR_CTRL_BAR_IDX     0x00000007
#define PCI_REBAR_CTRL_NBAR_MASK   0x000000E0
#define PCI_REBAR_CTRL_NBAR_SHIFT  5
#define PCI_REBAR_CTRL_BAR_SIZE    0x00001F00
#define PCI_REBAR_CTRL_BAR_SHIFT   8

#define PCI_CFG_SPACE_SIZE         256
#define PCI_CFG_SPACE_EXP_SIZE     4096

#define PCI_POSSIBLE_ERROR(val)    ((val) == 0xffffffff)

/* ------------------------------------------------------------------ */
/*  PCI standard offsets                                               */
/* ------------------------------------------------------------------ */

#define PCI_CMD_REG                0x04
#define PCI_CMD_MEMORY_SPACE       0x0002

#define PCI_HEADER_TYPE_OFFSET     0x0E
#define PCI_HEADER_TYPE_MULTI_FUNC 0x80
#define PCI_HEADER_TYPE_BRIDGE_VAL 0x01

#define PCI_BRIDGE_SECONDARY_BUS   0x19
#define PCI_BRIDGE_SUBORDINATE_BUS 0x1A

/* Bridge prefetchable memory window registers */
#define PCI_PREF_BASE_LIMIT        0x24
#define PCI_PREF_BASE_UPPER32      0x28
#define PCI_PREF_LIMIT_UPPER32     0x2C

/* BAR type bits */
#define PCI_BAR_IO_SPACE           0x01
#define PCI_BAR_64BIT              0x04
#define PCI_BAR_PREFETCHABLE       0x08
#define PCI_BAR_64BIT_PREF         (PCI_BAR_64BIT | PCI_BAR_PREFETCHABLE)

/* ------------------------------------------------------------------ */
/*  Vendor / device IDs for quirks and blacklist                       */
/* ------------------------------------------------------------------ */

#define PCI_VENDOR_ID_ATI          0x1002
#define PCI_VENDOR_ID_INTEL        0x8086
#define PCI_DEVICE_ID_INTEL_7S_XHCI 0x1e31

/* ------------------------------------------------------------------ */
/*  Tunables                                                           */
/* ------------------------------------------------------------------ */

/*
 * Maximum ReBAR size index.  2^(n+20) bytes:
 *   n=13 -> 8 GB    n=14 -> 16 GB
 * Sandy Bridge 36-bit PA: n=14 is the practical ceiling.
 */
static UINT8 reBarState = 14;

/*
 * Minimum current BAR size index for the "relocate" path.
 * BARs below this threshold use in-place growth instead.
 * Index 4 = 16 MB — filters doorbell/register BARs.
 */
#define REBAR_MIN_SIZE_IDX         4

/* ------------------------------------------------------------------ */
/*  MMIO space allocator (above 4 GB)                                  */
/* ------------------------------------------------------------------ */

/*
 * Bump allocator starting at 36 GB.  On Sandy Bridge with 32 GB RAM,
 * TOUUD sits around ~34.5 GB (PCI hole remap).  36 GB clears that
 * with margin, leaving ~28 GB of MMIO runway to the 36-bit ceiling.
 * A 16 GB BAR aligned at 0xC_0000_0000 (48 GB) fits comfortably.
 */
#define MMIO_ALLOC_BASE            0x900000000ULL   /* 36 GB */
#define MMIO_ALLOC_LIMIT           0xFFFFFFFFFULL   /* 36-bit PA = 64 GB */

static UINT64 gMmioNext = MMIO_ALLOC_BASE;

/* ------------------------------------------------------------------ */
/*  Below-4G eviction allocator                                        */
/* ------------------------------------------------------------------ */

/*
 * When in-place growth collides with small PCH BARs (SMBus, HDA, XHCI)
 * that coreboot placed above 4G, we evict them to this below-4G gap.
 * On Sandy Bridge, coreboot's MMIO region 0x82A0_0000 - 0xEFFF_FFFF
 * has a gap around 0xEFA0_0000 (between PCH allocations and the GPU's
 * non-prefetchable BAR at 0xEFE0_0000).  ~4 MB of headroom for ~81 KB.
 */
#define EVICT_BELOW4G_BASE     0xEFA00000ULL
#define EVICT_BELOW4G_LIMIT    0xEFDFFFFFULL   /* stop before GPU non-pref */

static UINT64 gEvictBump = EVICT_BELOW4G_BASE;

/* ------------------------------------------------------------------ */
/*  MMIO occupancy map (above 4 GB)                                    */
/* ------------------------------------------------------------------ */

#define MAX_MMIO_REGIONS 64

typedef struct {
    UINT64  Base;
    UINT64  Size;
    UINT8   Bus;
    UINT8   Dev;
    UINT8   Func;
    UINT8   BarIndex;
} MMIO_REGION;

static MMIO_REGION gMmioMap[MAX_MMIO_REGIONS];
static UINTN       gMmioMapCount = 0;

/* ------------------------------------------------------------------ */
/*  ECAM base from MCFG                                                */
/* ------------------------------------------------------------------ */

static UINT64 gEcamBase = 0;
static UINT8  gStartBus = 0;
static UINT8  gEndBus   = 255;

#pragma pack(1)
typedef struct {
    UINT64 BaseAddress;
    UINT16 PciSegmentGroupNumber;
    UINT8  StartBusNumber;
    UINT8  EndBusNumber;
    UINT32 Reserved;
} MCFG_ENTRY;

typedef struct {
    EFI_ACPI_DESCRIPTION_HEADER Header;
    UINT64 Reserved;
} MCFG_TABLE;
#pragma pack()

/* Bridge location for chain traversal */
#define MAX_BRIDGE_DEPTH 8

typedef struct {
    UINT8 Bus;
    UINT8 Dev;
    UINT8 Func;
} BRIDGE_LOC;

/* Per-BAR info for the device being set up */
#define MAX_PREF_BARS 6

typedef struct {
    UINT8   BarIndex;
    UINT8   CurrentSize;    /* ReBAR n (size = 2^(n+20)), 0 if no ReBAR entry */
    UINT8   NewSize;        /* target ReBAR n (0 = no change) */
    UINT64  NewSizeBytes;   /* final size in bytes after any resize */
    UINT64  OldAddr;
    UINT64  NewAddr;
    BOOLEAN Relocated;      /* TRUE = relocated, FALSE = kept in place */
} PREF_BAR_INFO;

/* ================================================================== */
/*  Utility                                                            */
/* ================================================================== */

static INTN fls(UINT32 x)
{
    INTN r = -1;
    while (x) {
        r++;
        x >>= 1;
    }
    return r;
}

static VOID SizeStr(UINT8 n, CHAR8 *buf, UINTN bufLen)
{
    if (n >= 10) {
        UINT32 gb = 1U << (n - 10);
        AsciiSPrint(buf, bufLen, "%d GB", gb);
    } else {
        UINT32 mb = 1U << n;
        AsciiSPrint(buf, bufLen, "%d MB", mb);
    }
}

/* ================================================================== */
/*  ECAM MMIO accessors                                                */
/* ================================================================== */

static UINT64 EcamAddr(UINT8 bus, UINT8 dev, UINT8 func, UINT16 reg)
{
    return gEcamBase
         + ((UINT64)bus  << 20)
         + ((UINT64)dev  << 15)
         + ((UINT64)func << 12)
         + reg;
}

static UINT32 EcamRead32 (UINT8 b, UINT8 d, UINT8 f, UINT16 r) { return MmioRead32 (EcamAddr(b,d,f,r)); }
static VOID   EcamWrite32(UINT8 b, UINT8 d, UINT8 f, UINT16 r, UINT32 v) { MmioWrite32(EcamAddr(b,d,f,r), v); }
static UINT16 EcamRead16 (UINT8 b, UINT8 d, UINT8 f, UINT16 r) { return MmioRead16 (EcamAddr(b,d,f,r)); }
static VOID   EcamWrite16(UINT8 b, UINT8 d, UINT8 f, UINT16 r, UINT16 v) { MmioWrite16(EcamAddr(b,d,f,r), v); }
static UINT8  EcamRead8  (UINT8 b, UINT8 d, UINT8 f, UINT16 r) { return MmioRead8  (EcamAddr(b,d,f,r)); }

/* ================================================================== */
/*  PCI Extended Capability search                                     */
/* ================================================================== */

static UINT16 FindExtCap(UINT8 bus, UINT8 dev, UINT8 func, UINT16 cap)
{
    UINT32 header;
    UINT16 pos = PCI_CFG_SPACE_SIZE;
    INTN   ttl = (PCI_CFG_SPACE_EXP_SIZE - PCI_CFG_SPACE_SIZE) / 8;

    header = EcamRead32(bus, dev, func, pos);
    if (header == 0 || PCI_POSSIBLE_ERROR(header))
        return 0;

    while (ttl-- > 0) {
        if (PCI_EXT_CAP_ID(header) == cap)
            return pos;
        pos = PCI_EXT_CAP_NEXT(header);
        if (pos < PCI_CFG_SPACE_SIZE)
            break;
        header = EcamRead32(bus, dev, func, pos);
    }
    return 0;
}

/* ================================================================== */
/*  ReBAR helpers                                                      */
/* ================================================================== */

static INTN RebarFindPos(UINT8 bus, UINT8 dev, UINT8 func,
                         UINT16 epos, UINT8 bar)
{
    UINT32 ctrl;
    UINTN  nbars, i;
    INTN   pos = epos;

    ctrl  = EcamRead32(bus, dev, func, pos + PCI_REBAR_CTRL);
    nbars = (ctrl & PCI_REBAR_CTRL_NBAR_MASK) >> PCI_REBAR_CTRL_NBAR_SHIFT;

    for (i = 0; i < nbars; i++, pos += 8) {
        ctrl = EcamRead32(bus, dev, func, pos + PCI_REBAR_CTRL);
        if ((ctrl & PCI_REBAR_CTRL_BAR_IDX) == bar)
            return pos;
    }
    return -1;
}

static UINT32 RebarGetSizes(UINT8 bus, UINT8 dev, UINT8 func,
                            UINT16 epos, UINT16 vid, UINT16 did,
                            UINT8 bar)
{
    INTN pos = RebarFindPos(bus, dev, func, epos, bar);
    if (pos < 0)
        return 0;

    UINT32 cap = EcamRead32(bus, dev, func, pos + PCI_REBAR_CAP);
    cap &= PCI_REBAR_CAP_SIZES;

    /* Sapphire RX 5600 XT Pulse quirk */
    if (vid == PCI_VENDOR_ID_ATI && did == 0x731f &&
        bar == 0 && cap == 0x7000)
        cap = 0x3f000;

    return cap >> 4;
}

static UINT8 RebarGetCurrentSize(UINT8 bus, UINT8 dev, UINT8 func,
                                 UINT16 epos, UINT8 bar)
{
    INTN pos = RebarFindPos(bus, dev, func, epos, bar);
    if (pos < 0)
        return 0;

    UINT32 ctrl = EcamRead32(bus, dev, func, pos + PCI_REBAR_CTRL);
    return (UINT8)((ctrl & PCI_REBAR_CTRL_BAR_SIZE) >> PCI_REBAR_CTRL_BAR_SHIFT);
}

static VOID RebarSetSize(UINT8 bus, UINT8 dev, UINT8 func,
                         UINT16 epos, UINT8 bar, UINT8 size)
{
    INTN pos = RebarFindPos(bus, dev, func, epos, bar);
    if (pos < 0)
        return;

    UINT32 ctrl = EcamRead32(bus, dev, func, pos + PCI_REBAR_CTRL);
    ctrl &= ~PCI_REBAR_CTRL_BAR_SIZE;
    ctrl |= (UINT32)size << PCI_REBAR_CTRL_BAR_SHIFT;
    EcamWrite32(bus, dev, func, pos + PCI_REBAR_CTRL, ctrl);
}

/* ================================================================== */
/*  BAR inspection                                                     */
/* ================================================================== */

static BOOLEAN IsBar64Pref(UINT8 bus, UINT8 dev, UINT8 func, UINT8 barIndex)
{
    UINT32 bar = EcamRead32(bus, dev, func, 0x10 + barIndex * 4);
    return ((bar & 0x0F) == PCI_BAR_64BIT_PREF);
}

static BOOLEAN IsBar64(UINT8 bus, UINT8 dev, UINT8 func, UINT8 barIndex)
{
    UINT32 bar = EcamRead32(bus, dev, func, 0x10 + barIndex * 4);
    if (bar & PCI_BAR_IO_SPACE)
        return FALSE;
    return ((bar & 0x06) == PCI_BAR_64BIT);
}

static UINT64 ReadBar64Addr(UINT8 bus, UINT8 dev, UINT8 func, UINT8 barIndex)
{
    UINT16 off = 0x10 + barIndex * 4;
    UINT32 lo  = EcamRead32(bus, dev, func, off);
    UINT32 hi  = EcamRead32(bus, dev, func, off + 4);
    return ((UINT64)hi << 32) | (lo & ~(UINT64)0xF);
}

static VOID WriteBar64Addr(UINT8 bus, UINT8 dev, UINT8 func,
                           UINT8 barIndex, UINT64 addr)
{
    UINT16 off = 0x10 + barIndex * 4;
    UINT32 lo  = EcamRead32(bus, dev, func, off);
    UINT32 typeBits = lo & 0x0F;

    EcamWrite32(bus, dev, func, off,     (UINT32)(addr & 0xFFFFFFF0) | typeBits);
    EcamWrite32(bus, dev, func, off + 4, (UINT32)(addr >> 32));
}

static UINT64 ProbeBar64Size(UINT8 bus, UINT8 dev, UINT8 func, UINT8 barIndex)
{
    UINT16 off = 0x10 + barIndex * 4;

    UINT32 origLo = EcamRead32(bus, dev, func, off);
    UINT32 origHi = EcamRead32(bus, dev, func, off + 4);

    EcamWrite32(bus, dev, func, off,     0xFFFFFFFF);
    EcamWrite32(bus, dev, func, off + 4, 0xFFFFFFFF);

    UINT32 sizeLo = EcamRead32(bus, dev, func, off);
    UINT32 sizeHi = EcamRead32(bus, dev, func, off + 4);

    EcamWrite32(bus, dev, func, off,     origLo);
    EcamWrite32(bus, dev, func, off + 4, origHi);

    UINT64 mask = ((UINT64)sizeHi << 32) | (sizeLo & ~(UINT64)0xF);
    if (mask == 0)
        return 0;
    return (~mask) + 1;
}

/* ================================================================== */
/*  MMIO occupancy map                                                 */
/* ================================================================== */

static VOID MmioMapAdd(UINT8 bus, UINT8 dev, UINT8 func,
                       UINT8 barIndex, UINT64 base, UINT64 size)
{
    if (base < 0x100000000ULL || size == 0)
        return;

    if (gMmioMapCount >= MAX_MMIO_REGIONS) {
        DEBUG((DEBUG_WARN, "ReBarDXE: MMIO map full, dropping %02x:%02x.%x BAR%d\n",
               bus, dev, func, barIndex));
        return;
    }

    gMmioMap[gMmioMapCount].Base     = base;
    gMmioMap[gMmioMapCount].Size     = size;
    gMmioMap[gMmioMapCount].Bus      = bus;
    gMmioMap[gMmioMapCount].Dev      = dev;
    gMmioMap[gMmioMapCount].Func     = func;
    gMmioMap[gMmioMapCount].BarIndex = barIndex;
    gMmioMapCount++;
}

static VOID MmioMapCollectDevice(UINT8 bus, UINT8 dev, UINT8 func)
{
    UINT8 hdrType = EcamRead8(bus, dev, func, PCI_HEADER_TYPE_OFFSET) & 0x7F;
    UINT8 maxBar  = (hdrType == PCI_HEADER_TYPE_BRIDGE_VAL) ? 2 : 6;

    for (UINT8 bar = 0; bar < maxBar; bar++) {
        UINT32 barReg = EcamRead32(bus, dev, func, 0x10 + bar * 4);

        if (barReg & PCI_BAR_IO_SPACE)
            continue;

        if (!IsBar64(bus, dev, func, bar))
            continue;

        UINT64 addr = ReadBar64Addr(bus, dev, func, bar);
        if (addr < 0x100000000ULL || addr == 0) {
            bar++;  /* 64-bit, skip upper half */
            continue;
        }

        /* Get size: prefer ReBAR CTRL, fall back to probe */
        UINT16 epos = FindExtCap(bus, dev, func, PCI_EXT_CAP_ID_REBAR);
        UINT64 size = 0;

        if (epos) {
            INTN rpos = RebarFindPos(bus, dev, func, epos, bar);
            if (rpos >= 0) {
                UINT8 sizeIdx = RebarGetCurrentSize(bus, dev, func, epos, bar);
                size = 1ULL << (sizeIdx + 20);
            }
        }

        if (size == 0) {
            UINT16 cmd = EcamRead16(bus, dev, func, PCI_CMD_REG);
            EcamWrite16(bus, dev, func, PCI_CMD_REG, cmd & ~PCI_CMD_MEMORY_SPACE);
            size = ProbeBar64Size(bus, dev, func, bar);
            EcamWrite16(bus, dev, func, PCI_CMD_REG, cmd);
        }

        MmioMapAdd(bus, dev, func, bar, addr, size);
        bar++;  /* 64-bit BAR consumes two indices */
    }
}

static BOOLEAN MmioMapCollides(UINT64 base, UINT64 size,
                               UINT8 exBus, UINT8 exDev,
                               UINT8 exFunc, UINT8 exBar)
{
    UINT64 end = base + size;

    for (UINTN i = 0; i < gMmioMapCount; i++) {
        if (gMmioMap[i].Bus == exBus && gMmioMap[i].Dev == exDev &&
            gMmioMap[i].Func == exFunc && gMmioMap[i].BarIndex == exBar)
            continue;

        UINT64 mEnd = gMmioMap[i].Base + gMmioMap[i].Size;
        if (base < mEnd && end > gMmioMap[i].Base)
            return TRUE;
    }
    return FALSE;
}

static UINT64 MmioMapNextAbove(UINT64 base,
                               UINT8 exBus, UINT8 exDev,
                               UINT8 exFunc, UINT8 exBar)
{
    UINT64 nearest = MMIO_ALLOC_LIMIT + 1;

    for (UINTN i = 0; i < gMmioMapCount; i++) {
        if (gMmioMap[i].Bus == exBus && gMmioMap[i].Dev == exDev &&
            gMmioMap[i].Func == exFunc && gMmioMap[i].BarIndex == exBar)
            continue;

        if (gMmioMap[i].Base > base && gMmioMap[i].Base < nearest)
            nearest = gMmioMap[i].Base;
    }
    return nearest;
}

static VOID MmioMapDump(VOID)
{
    DEBUG((DEBUG_INFO, "ReBarDXE: MMIO map (%d entries above 4G):\n", gMmioMapCount));
    for (UINTN i = 0; i < gMmioMapCount; i++) {
        DEBUG((DEBUG_INFO, "ReBarDXE:   %02x:%02x.%x BAR%d  0x%lx - 0x%lx (0x%lx)\n",
               gMmioMap[i].Bus, gMmioMap[i].Dev, gMmioMap[i].Func,
               gMmioMap[i].BarIndex,
               gMmioMap[i].Base,
               gMmioMap[i].Base + gMmioMap[i].Size - 1,
               gMmioMap[i].Size));
    }
}

static VOID MmioMapRemoveEntry(UINTN idx)
{
    if (idx >= gMmioMapCount)
        return;
    for (UINTN j = idx; j + 1 < gMmioMapCount; j++)
        gMmioMap[j] = gMmioMap[j + 1];
    gMmioMapCount--;
}

/* ================================================================== */
/*  MMIO bump allocator                                                */
/* ================================================================== */

static UINT64 MmioAlloc(UINT64 size)
{
    UINT64 mask    = size - 1;
    UINT64 aligned = (gMmioNext + mask) & ~mask;

    if (aligned + size - 1 > MMIO_ALLOC_LIMIT) {
        DEBUG((DEBUG_ERROR, "ReBarDXE: MMIO alloc of 0x%lx would exceed 36-bit limit\n", size));
        return 0;
    }

    gMmioNext = aligned + size;
    return aligned;
}

/* ================================================================== */
/*  Bridge chain discovery                                             */
/* ================================================================== */

static UINTN FindBridgeChain(UINT8 targetBus, BRIDGE_LOC *chain, UINTN maxDepth)
{
    UINTN depth     = 0;
    UINT8 searchBus = 0;

    while (depth < maxDepth && searchBus != targetBus) {
        BOOLEAN found = FALSE;

        for (UINT8 dev = 0; dev < 32 && !found; dev++) {
            for (UINT8 func = 0; func < 8 && !found; func++) {
                UINT16 vid = EcamRead16(searchBus, dev, func, 0);
                if (vid == 0xFFFF) {
                    if (func == 0) break;
                    continue;
                }

                UINT8 hdr = EcamRead8(searchBus, dev, func, PCI_HEADER_TYPE_OFFSET);

                if ((hdr & 0x7F) != PCI_HEADER_TYPE_BRIDGE_VAL)
                    goto next_func;

                {
                    UINT8 sec = EcamRead8(searchBus, dev, func, PCI_BRIDGE_SECONDARY_BUS);
                    UINT8 sub = EcamRead8(searchBus, dev, func, PCI_BRIDGE_SUBORDINATE_BUS);

                    if (targetBus >= sec && targetBus <= sub) {
                        chain[depth].Bus  = searchBus;
                        chain[depth].Dev  = dev;
                        chain[depth].Func = func;
                        depth++;
                        searchBus = sec;
                        found = TRUE;
                    }
                }

            next_func:
                if (func == 0 && !(hdr & PCI_HEADER_TYPE_MULTI_FUNC))
                    break;
            }
        }

        if (!found)
            break;
    }
    return depth;
}

/* ================================================================== */
/*  Bridge prefetchable window                                         */
/* ================================================================== */

static VOID ReadBridgePrefWindow(UINT8 bus, UINT8 dev, UINT8 func,
                                 UINT64 *base, UINT64 *limit)
{
    UINT32 bl = EcamRead32(bus, dev, func, PCI_PREF_BASE_LIMIT);
    UINT32 bu = EcamRead32(bus, dev, func, PCI_PREF_BASE_UPPER32);
    UINT32 lu = EcamRead32(bus, dev, func, PCI_PREF_LIMIT_UPPER32);

    UINT16 bLow = (UINT16)(bl & 0xFFFF);
    UINT16 lLow = (UINT16)(bl >> 16);

    *base  = ((UINT64)bu << 32) | ((UINT64)(bLow & 0xFFF0) << 16);
    *limit = ((UINT64)lu << 32) | ((UINT64)(lLow & 0xFFF0) << 16) | 0xFFFFF;
}

static VOID WriteBridgePrefWindow(UINT8 bus, UINT8 dev, UINT8 func,
                                  UINT64 base, UINT64 limit)
{
    UINT16 bLow = (UINT16)((base  >> 16) & 0xFFF0) | 0x1;
    UINT16 lLow = (UINT16)((limit >> 16) & 0xFFF0) | 0x1;

    UINT32 bl = ((UINT32)lLow << 16) | bLow;
    UINT32 bu = (UINT32)(base  >> 32);
    UINT32 lu = (UINT32)(limit >> 32);

    EcamWrite32(bus, dev, func, PCI_PREF_BASE_LIMIT,   bl);
    EcamWrite32(bus, dev, func, PCI_PREF_BASE_UPPER32,  bu);
    EcamWrite32(bus, dev, func, PCI_PREF_LIMIT_UPPER32, lu);
}

/* ================================================================== */
/*  GOP framebuffer fixup                                              */
/* ================================================================== */

static VOID TryFixupGop(UINT64 oldBar0, UINT64 oldSize, UINT64 newBar0)
{
    EFI_GRAPHICS_OUTPUT_PROTOCOL *gop = NULL;
    EFI_STATUS status;

    status = gBS->LocateProtocol(&gEfiGraphicsOutputProtocolGuid,
                                 NULL, (VOID **)&gop);
    if (EFI_ERROR(status) || gop == NULL || gop->Mode == NULL) {
        DEBUG((DEBUG_INFO, "ReBarDXE: GOP not found, skipping framebuffer fixup\n"));
        return;
    }

    UINT64 fb = gop->Mode->FrameBufferBase;
    DEBUG((DEBUG_INFO, "ReBarDXE: GOP FrameBufferBase = 0x%lx\n", fb));

    if (fb >= oldBar0 && fb < oldBar0 + oldSize) {
        UINT64 offset = fb - oldBar0;
        gop->Mode->FrameBufferBase = newBar0 + offset;
        DEBUG((DEBUG_INFO, "ReBarDXE: GOP FrameBufferBase updated -> 0x%lx\n",
               gop->Mode->FrameBufferBase));
    }
}

/* ================================================================== */
/*  Device blacklist                                                   */
/* ================================================================== */

static BOOLEAN IsBlacklisted(UINT16 vid, UINT16 did)
{
    if (vid == PCI_VENDOR_ID_INTEL && did == PCI_DEVICE_ID_INTEL_7S_XHCI)
        return TRUE;
    return FALSE;
}

/* ================================================================== */
/*  In-place growth: find max safe size for a small BAR                */
/* ================================================================== */

/*
 * For a BAR at 'addr' with ReBAR supported sizes bitmask,
 * find the largest supported size <= reBarState that:
 *   (a) addr is naturally aligned to
 *   (b) doesn't collide with any other MMIO region
 *       (or colliders can be evicted to below 4G)
 *   (c) doesn't exceed the 36-bit PA limit
 *
 * Returns the size index n (0 = no growth possible).
 */

/* Forward declaration */
static BOOLEAN TryEvictColliders(UINT64 base, UINT64 size,
                                 UINT8 exBus, UINT8 exDev,
                                 UINT8 exFunc, UINT8 exBar);

static UINT8 FindMaxInPlaceSize(UINT64 addr, UINT32 sizes,
                                UINT8 currentSizeIdx,
                                UINT8 bus, UINT8 dev, UINT8 func,
                                UINT8 bar)
{
    UINT64 nextOccupied = MmioMapNextAbove(addr, bus, dev, func, bar);
    UINT64 headroom     = nextOccupied - addr;

    DEBUG((DEBUG_INFO, "ReBarDXE:     in-place: addr=0x%lx, headroom=0x%lx (next=0x%lx)\n",
           addr, headroom, nextOccupied));

    UINT8 maxIdx = MIN((UINT8)fls(sizes), reBarState);

    for (UINT8 n = maxIdx; n > currentSizeIdx; n--) {
        if (!(sizes & (1U << n)))
            continue;

        UINT64 candidateSize = 1ULL << (n + 20);
        CHAR8 sBuf[16];
        SizeStr(n, sBuf, sizeof(sBuf));

        /* Alignment: addr must be a multiple of candidateSize */
        if (addr & (candidateSize - 1)) {
            DEBUG((DEBUG_INFO, "ReBarDXE:     %a: not aligned\n", sBuf));
            continue;
        }

        /* Bounds: must fit within 36-bit PA */
        if (addr + candidateSize - 1 > MMIO_ALLOC_LIMIT) {
            DEBUG((DEBUG_INFO, "ReBarDXE:     %a: exceeds 36-bit PA\n", sBuf));
            continue;
        }

        /* Collision: check against entire MMIO map */
        if (MmioMapCollides(addr, candidateSize, bus, dev, func, bar)) {
            DEBUG((DEBUG_INFO, "ReBarDXE:     %a: collides — attempting eviction\n", sBuf));

            if (TryEvictColliders(addr, candidateSize, bus, dev, func, bar)) {
                DEBUG((DEBUG_INFO, "ReBarDXE:     %a: eviction succeeded!\n", sBuf));
                return n;
            }

            DEBUG((DEBUG_INFO, "ReBarDXE:     %a: eviction failed, skipping\n", sBuf));
            continue;
        }

        DEBUG((DEBUG_INFO, "ReBarDXE:     %a: OK\n", sBuf));
        return n;
    }

    return 0;
}

/* ================================================================== */
/*  Collider eviction: relocate small bus-0 BARs below 4G              */
/* ================================================================== */

/*
 * When in-place growth of a doorbell BAR is blocked by small PCH BARs
 * (SMBus, HDA, XHCI etc.) that coreboot placed above 4G, evict them
 * to below-4G MMIO space.  Only bus-0 devices with small BARs are
 * eligible — no bridge chain to update, no display-critical pointers.
 *
 * Returns TRUE if all colliders were evicted, FALSE if any couldn't be.
 */
static BOOLEAN TryEvictColliders(UINT64 base, UINT64 size,
                                 UINT8 exBus, UINT8 exDev,
                                 UINT8 exFunc, UINT8 exBar)
{
    UINT64 end = base + size;

    /* ---- First pass: verify all colliders are evictable ---- */
    for (UINTN i = 0; i < gMmioMapCount; i++) {
        /* Skip the BAR we're trying to grow */
        if (gMmioMap[i].Bus == exBus && gMmioMap[i].Dev == exDev &&
            gMmioMap[i].Func == exFunc && gMmioMap[i].BarIndex == exBar)
            continue;

        UINT64 mEnd = gMmioMap[i].Base + gMmioMap[i].Size;
        if (!(base < mEnd && end > gMmioMap[i].Base))
            continue;  /* no overlap */

        /* Collider found — check if safe to evict */
        if (gMmioMap[i].Bus != 0) {
            DEBUG((DEBUG_INFO, "ReBarDXE:     collider %02x:%02x.%x BAR%d not on bus 0\n",
                   gMmioMap[i].Bus, gMmioMap[i].Dev, gMmioMap[i].Func,
                   gMmioMap[i].BarIndex));
            return FALSE;
        }

        if (gMmioMap[i].Size >= (1ULL << (REBAR_MIN_SIZE_IDX + 20))) {
            DEBUG((DEBUG_INFO, "ReBarDXE:     collider %02x:%02x.%x BAR%d too large (0x%lx)\n",
                   gMmioMap[i].Bus, gMmioMap[i].Dev, gMmioMap[i].Func,
                   gMmioMap[i].BarIndex, gMmioMap[i].Size));
            return FALSE;
        }

        DEBUG((DEBUG_INFO, "ReBarDXE:     collider %02x:%02x.%x BAR%d "
               "@ 0x%lx (0x%lx) — evictable\n",
               gMmioMap[i].Bus, gMmioMap[i].Dev, gMmioMap[i].Func,
               gMmioMap[i].BarIndex, gMmioMap[i].Base, gMmioMap[i].Size));
    }

    /* ---- Second pass: evict all colliders below 4G ---- */
    for (UINTN i = 0; i < gMmioMapCount; /* incremented conditionally */) {
        if (gMmioMap[i].Bus == exBus && gMmioMap[i].Dev == exDev &&
            gMmioMap[i].Func == exFunc && gMmioMap[i].BarIndex == exBar) {
            i++;
            continue;
        }

        UINT64 mEnd = gMmioMap[i].Base + gMmioMap[i].Size;
        if (!(base < mEnd && end > gMmioMap[i].Base)) {
            i++;
            continue;
        }

        /* Compute aligned below-4G address */
        UINT64 sz      = gMmioMap[i].Size;
        UINT64 aligned  = (gEvictBump + sz - 1) & ~(sz - 1);

        if (aligned + sz - 1 > EVICT_BELOW4G_LIMIT) {
            DEBUG((DEBUG_ERROR, "ReBarDXE:     below-4G eviction space exhausted!\n"));
            return FALSE;
        }

        UINT8  b   = gMmioMap[i].Bus;
        UINT8  d   = gMmioMap[i].Dev;
        UINT8  f   = gMmioMap[i].Func;
        UINT8  bar = gMmioMap[i].BarIndex;
        UINT64 old = gMmioMap[i].Base;

        /* Disable memory decode while we move the BAR */
        UINT16 cmd = EcamRead16(b, d, f, PCI_CMD_REG);
        EcamWrite16(b, d, f, PCI_CMD_REG, cmd & ~PCI_CMD_MEMORY_SPACE);

        /* Write new below-4G address (low 32 = addr | type bits, high 32 = 0) */
        WriteBar64Addr(b, d, f, bar, aligned);

        /* Re-enable memory decode */
        EcamWrite16(b, d, f, PCI_CMD_REG, cmd);

        gEvictBump = aligned + sz;

        DEBUG((DEBUG_INFO, "ReBarDXE:     EVICTED %02x:%02x.%x BAR%d: "
               "0x%lx -> 0x%lx (%d bytes)\n",
               b, d, f, bar, old, aligned, (UINT32)sz));

        /* Remove from above-4G MMIO map (entry no longer above 4G) */
        MmioMapRemoveEntry(i);
        /* don't increment i — entries shifted down */
    }

    return TRUE;
}

/* ================================================================== */
/*  Per-device ReBAR setup                                             */
/* ================================================================== */

static VOID SetupDevice(UINT8 bus, UINT8 dev, UINT8 func,
                        UINT16 vid, UINT16 did)
{
    CHAR8 sizeBuf[16], sizeBuf2[16];

    if (IsBlacklisted(vid, did)) {
        DEBUG((DEBUG_INFO, "ReBarDXE: %02x:%02x.%x [%04x:%04x] blacklisted\n",
               bus, dev, func, vid, did));
        return;
    }

    UINT16 epos = FindExtCap(bus, dev, func, PCI_EXT_CAP_ID_REBAR);
    if (epos == 0)
        return;

    DEBUG((DEBUG_INFO, "ReBarDXE: %02x:%02x.%x [%04x:%04x] ReBAR @ 0x%x\n",
           bus, dev, func, vid, did, epos));

    /* -------------------------------------------------------------- */
    /* Phase 1: Collect info on every 64-bit prefetchable BAR          */
    /* -------------------------------------------------------------- */

    PREF_BAR_INFO bars[MAX_PREF_BARS];
    UINTN         barCount = 0;
    BOOLEAN       anyWork  = FALSE;

    for (UINT8 bar = 0; bar < 6; bar++) {
        if (!IsBar64Pref(bus, dev, func, bar))
            continue;

        UINT8  curSizeIdx   = 0;
        UINT64 curSizeBytes = 0;
        INTN   rpos = RebarFindPos(bus, dev, func, epos, bar);

        if (rpos >= 0) {
            curSizeIdx   = RebarGetCurrentSize(bus, dev, func, epos, bar);
            curSizeBytes = 1ULL << (curSizeIdx + 20);
        }

        bars[barCount].BarIndex     = bar;
        bars[barCount].CurrentSize  = curSizeIdx;
        bars[barCount].NewSize      = 0;
        bars[barCount].NewSizeBytes = curSizeBytes;
        bars[barCount].OldAddr      = ReadBar64Addr(bus, dev, func, bar);
        bars[barCount].NewAddr      = 0;
        bars[barCount].Relocated    = FALSE;

        if (rpos < 0) {
            /* No ReBAR entry — keep as-is */
            barCount++;
            bar++;
            continue;
        }

        UINT32 sizes = RebarGetSizes(bus, dev, func, epos, vid, did, bar);

        if (curSizeIdx >= REBAR_MIN_SIZE_IDX) {
            /* ---- LARGE BAR: resize + relocate ---- */
            UINT8 maxSize = (UINT8)fls(sizes);
            UINT8 target  = MIN(maxSize, reBarState);

            for (UINT8 n = target; n > curSizeIdx; n--) {
                if (sizes & (1U << n)) {
                    bars[barCount].NewSize      = n;
                    bars[barCount].NewSizeBytes = 1ULL << (n + 20);
                    bars[barCount].Relocated    = TRUE;
                    anyWork = TRUE;

                    SizeStr(curSizeIdx, sizeBuf,  sizeof(sizeBuf));
                    SizeStr(n,          sizeBuf2, sizeof(sizeBuf2));
                    DEBUG((DEBUG_INFO, "ReBarDXE:   BAR%d %a -> %a (relocate)\n",
                           bar, sizeBuf, sizeBuf2));
                    break;
                }
            }
        } else {
            /* ---- SMALL BAR: try in-place growth ---- */
            SizeStr(curSizeIdx, sizeBuf, sizeof(sizeBuf));
            DEBUG((DEBUG_INFO, "ReBarDXE:   BAR%d %a — checking in-place growth\n",
                   bar, sizeBuf));

            UINT8 inPlaceSize = FindMaxInPlaceSize(
                bars[barCount].OldAddr, sizes, curSizeIdx,
                bus, dev, func, bar);

            if (inPlaceSize > 0) {
                bars[barCount].NewSize      = inPlaceSize;
                bars[barCount].NewSizeBytes = 1ULL << (inPlaceSize + 20);
                bars[barCount].Relocated    = FALSE;
                anyWork = TRUE;

                SizeStr(inPlaceSize, sizeBuf2, sizeof(sizeBuf2));
                DEBUG((DEBUG_INFO, "ReBarDXE:   BAR%d %a -> %a (in-place)\n",
                       bar, sizeBuf, sizeBuf2));
            } else {
                DEBUG((DEBUG_INFO, "ReBarDXE:   BAR%d %a — no safe growth found\n",
                       bar, sizeBuf));
            }
        }

        barCount++;
        bar++;  /* 64-bit BAR consumes two indices */
    }

    if (barCount == 0 || !anyWork) {
        DEBUG((DEBUG_INFO, "ReBarDXE:   nothing to do\n"));
        return;
    }

    /* -------------------------------------------------------------- */
    /* Phase 2: Find the bridge chain                                  */
    /* -------------------------------------------------------------- */

    BRIDGE_LOC chain[MAX_BRIDGE_DEPTH];
    UINTN      depth = FindBridgeChain(bus, chain, MAX_BRIDGE_DEPTH);

    DEBUG((DEBUG_INFO, "ReBarDXE:   bridge chain (%d deep):", depth));
    for (UINTN i = 0; i < depth; i++)
        DEBUG((DEBUG_INFO, " %02x:%02x.%x", chain[i].Bus, chain[i].Dev, chain[i].Func));
    DEBUG((DEBUG_INFO, "\n"));

    if (depth == 0) {
        DEBUG((DEBUG_ERROR, "ReBarDXE:   no bridge chain, aborting\n"));
        return;
    }

    /* -------------------------------------------------------------- */
    /* Phase 3: Disable memory decode                                  */
    /* -------------------------------------------------------------- */

    UINT16 origCmd = EcamRead16(bus, dev, func, PCI_CMD_REG);
    EcamWrite16(bus, dev, func, PCI_CMD_REG, origCmd & ~PCI_CMD_MEMORY_SPACE);
    DEBUG((DEBUG_INFO, "ReBarDXE:   decode disabled (cmd 0x%04x -> 0x%04x)\n",
           origCmd, origCmd & ~PCI_CMD_MEMORY_SPACE));

    /* -------------------------------------------------------------- */
    /* Phase 4: Write new ReBAR sizes                                  */
    /* -------------------------------------------------------------- */

    for (UINTN i = 0; i < barCount; i++) {
        if (bars[i].NewSize > 0) {
            SizeStr(bars[i].NewSize, sizeBuf, sizeof(sizeBuf));
            DEBUG((DEBUG_INFO, "ReBarDXE:   BAR%d ReBAR CTRL <- %d (%a)\n",
                   bars[i].BarIndex, bars[i].NewSize, sizeBuf));
            RebarSetSize(bus, dev, func, epos, bars[i].BarIndex, bars[i].NewSize);
        }
    }

    /* -------------------------------------------------------------- */
    /* Phase 5: Allocate/relocate large BARs, keep small in place      */
    /* -------------------------------------------------------------- */

    /* Sort: relocated BARs first, largest first (best alignment) */
    for (UINTN i = 0; i < barCount; i++) {
        for (UINTN j = i + 1; j < barCount; j++) {
            BOOLEAN iRelo = bars[i].Relocated;
            BOOLEAN jRelo = bars[j].Relocated;

            if ((!iRelo && jRelo) ||
                (iRelo == jRelo && bars[j].NewSizeBytes > bars[i].NewSizeBytes))
            {
                PREF_BAR_INFO tmp = bars[i];
                bars[i] = bars[j];
                bars[j] = tmp;
            }
        }
    }

    UINT64 windowBase  = MAX_UINT64;
    UINT64 windowLimit = 0;

    for (UINTN i = 0; i < barCount; i++) {
        if (bars[i].Relocated) {
            UINT64 addr = MmioAlloc(bars[i].NewSizeBytes);
            if (addr == 0) {
                DEBUG((DEBUG_ERROR, "ReBarDXE:   MMIO alloc failed for BAR%d!\n",
                       bars[i].BarIndex));
                EcamWrite16(bus, dev, func, PCI_CMD_REG, origCmd);
                return;
            }

            bars[i].NewAddr = addr;
            WriteBar64Addr(bus, dev, func, bars[i].BarIndex, addr);

            SizeStr(bars[i].NewSize, sizeBuf, sizeof(sizeBuf));
            DEBUG((DEBUG_INFO, "ReBarDXE:   BAR%d relocated 0x%lx -> 0x%lx (%a)\n",
                   bars[i].BarIndex, bars[i].OldAddr, addr, sizeBuf));
        } else {
            bars[i].NewAddr = bars[i].OldAddr;

            if (bars[i].NewSize > 0) {
                SizeStr(bars[i].NewSize, sizeBuf, sizeof(sizeBuf));
                DEBUG((DEBUG_INFO, "ReBarDXE:   BAR%d grown in-place at 0x%lx (%a)\n",
                       bars[i].BarIndex, bars[i].OldAddr, sizeBuf));
            } else {
                DEBUG((DEBUG_INFO, "ReBarDXE:   BAR%d unchanged at 0x%lx\n",
                       bars[i].BarIndex, bars[i].OldAddr));
            }
        }

        /* Accumulate bridge window bounds */
        if (bars[i].NewAddr < windowBase)
            windowBase = bars[i].NewAddr;
        if (bars[i].NewAddr + bars[i].NewSizeBytes - 1 > windowLimit)
            windowLimit = bars[i].NewAddr + bars[i].NewSizeBytes - 1;
    }

    DEBUG((DEBUG_INFO, "ReBarDXE:   pref window needed: 0x%lx - 0x%lx\n",
           windowBase, windowLimit));

    /* -------------------------------------------------------------- */
    /* Phase 6: Update bridge chain prefetchable windows               */
    /* -------------------------------------------------------------- */

    for (UINTN i = 0; i < depth; i++) {
        UINT64 oldBase, oldLimit;
        ReadBridgePrefWindow(chain[i].Bus, chain[i].Dev, chain[i].Func,
                             &oldBase, &oldLimit);

        WriteBridgePrefWindow(chain[i].Bus, chain[i].Dev, chain[i].Func,
                              windowBase, windowLimit);

        DEBUG((DEBUG_INFO, "ReBarDXE:   bridge %02x:%02x.%x pref: "
               "0x%lx-0x%lx -> 0x%lx-0x%lx\n",
               chain[i].Bus, chain[i].Dev, chain[i].Func,
               oldBase, oldLimit, windowBase, windowLimit));
    }

    /* -------------------------------------------------------------- */
    /* Phase 7: Fix up GOP framebuffer pointer                         */
    /* -------------------------------------------------------------- */

    for (UINTN i = 0; i < barCount; i++) {
        if (bars[i].BarIndex == 0 && bars[i].Relocated && bars[i].NewSize > 0) {
            UINT64 oldSize = 1ULL << (bars[i].CurrentSize + 20);
            TryFixupGop(bars[i].OldAddr, oldSize, bars[i].NewAddr);
            break;
        }
    }

    /* -------------------------------------------------------------- */
    /* Phase 8: Re-enable memory decode                                */
    /* -------------------------------------------------------------- */

    EcamWrite16(bus, dev, func, PCI_CMD_REG, origCmd);
    DEBUG((DEBUG_INFO, "ReBarDXE:   decode re-enabled (cmd 0x%04x)\n", origCmd));
}

/* ================================================================== */
/*  Two-pass bus scan                                                  */
/* ================================================================== */

static VOID ScanAllDevices(VOID)
{
    UINT16 bus;
    UINT8  dev, func;
    UINTN  found = 0, rebar = 0;

    DEBUG((DEBUG_INFO, "ReBarDXE: === Pass 1: Building MMIO map ===\n"));
    DEBUG((DEBUG_INFO, "ReBarDXE: Scanning bus %d-%d, ECAM @ 0x%lx\n",
           gStartBus, gEndBus, gEcamBase));

    for (bus = gStartBus; bus <= gEndBus; bus++) {
        for (dev = 0; dev < 32; dev++) {
            for (func = 0; func < 8; func++) {
                UINT16 vid = EcamRead16(bus, dev, func, 0);
                if (vid == 0xFFFF)
                    continue;

                found++;
                MmioMapCollectDevice(bus, dev, func);

                if (FindExtCap(bus, dev, func, PCI_EXT_CAP_ID_REBAR))
                    rebar++;

                if (func == 0) {
                    UINT8 hdr = EcamRead8(bus, dev, func, PCI_HEADER_TYPE_OFFSET);
                    if (!(hdr & PCI_HEADER_TYPE_MULTI_FUNC))
                        break;
                }
            }
        }
    }

    DEBUG((DEBUG_INFO, "ReBarDXE: Found %d devices, %d with ReBAR\n", found, rebar));
    MmioMapDump();

    /* --- Pass 2: configure ReBAR devices --- */
    DEBUG((DEBUG_INFO, "ReBarDXE: === Pass 2: Configuring ReBAR ===\n"));

    for (bus = gStartBus; bus <= gEndBus; bus++) {
        for (dev = 0; dev < 32; dev++) {
            for (func = 0; func < 8; func++) {
                UINT16 vid = EcamRead16(bus, dev, func, 0);
                if (vid == 0xFFFF)
                    continue;

                UINT16 did = EcamRead16(bus, dev, func, 2);
                SetupDevice(bus, dev, func, vid, did);

                if (func == 0) {
                    UINT8 hdr = EcamRead8(bus, dev, func, PCI_HEADER_TYPE_OFFSET);
                    if (!(hdr & PCI_HEADER_TYPE_MULTI_FUNC))
                        break;
                }
            }
        }
    }

    DEBUG((DEBUG_INFO, "ReBarDXE: Scan complete\n"));
}

/* ================================================================== */
/*  MCFG / ACPI table lookup                                           */
/* ================================================================== */

static EFI_STATUS FindMcfg(VOID)
{
    EFI_ACPI_2_0_ROOT_SYSTEM_DESCRIPTION_POINTER *rsdp = NULL;
    EFI_ACPI_DESCRIPTION_HEADER *xsdt;
    MCFG_TABLE *mcfg = NULL;
    UINTN i, entryCount;

    for (i = 0; i < gST->NumberOfTableEntries; i++) {
        if (CompareGuid(&gST->ConfigurationTable[i].VendorGuid,
                        &gEfiAcpi20TableGuid)) {
            rsdp = gST->ConfigurationTable[i].VendorTable;
            break;
        }
    }

    if (!rsdp) {
        DEBUG((DEBUG_ERROR, "ReBarDXE: ACPI RSDP not found\n"));
        return EFI_NOT_FOUND;
    }

    DEBUG((DEBUG_INFO, "ReBarDXE: RSDP @ 0x%p, XSDT @ 0x%lx\n",
           rsdp, rsdp->XsdtAddress));

    xsdt = (EFI_ACPI_DESCRIPTION_HEADER *)(UINTN)rsdp->XsdtAddress;
    if (!xsdt)
        return EFI_NOT_FOUND;

    entryCount = (xsdt->Length - sizeof(*xsdt)) / sizeof(UINT64);
    UINT64 *tables = (UINT64 *)((UINT8 *)xsdt + sizeof(*xsdt));

    for (i = 0; i < entryCount; i++) {
        EFI_ACPI_DESCRIPTION_HEADER *tbl =
            (EFI_ACPI_DESCRIPTION_HEADER *)(UINTN)tables[i];
        if (tbl->Signature == SIGNATURE_32('M','C','F','G')) {
            mcfg = (MCFG_TABLE *)tbl;
            break;
        }
    }

    if (!mcfg) {
        DEBUG((DEBUG_ERROR, "ReBarDXE: MCFG table not found\n"));
        return EFI_NOT_FOUND;
    }

    UINTN mcfgEntries = (mcfg->Header.Length - sizeof(MCFG_TABLE)) / sizeof(MCFG_ENTRY);
    if (mcfgEntries == 0) {
        DEBUG((DEBUG_ERROR, "ReBarDXE: MCFG has no entries\n"));
        return EFI_NOT_FOUND;
    }

    MCFG_ENTRY *entry = (MCFG_ENTRY *)((UINT8 *)mcfg + sizeof(MCFG_TABLE));
    gEcamBase = entry->BaseAddress;
    gStartBus = entry->StartBusNumber;
    gEndBus   = entry->EndBusNumber;

    DEBUG((DEBUG_INFO, "ReBarDXE: MCFG: ECAM=0x%lx, Bus %d-%d\n",
           gEcamBase, gStartBus, gEndBus));

    return EFI_SUCCESS;
}

/* ================================================================== */
/*  ReadyToBoot handler                                                */
/* ================================================================== */

static VOID EFIAPI ReadyToBootHandler(IN EFI_EVENT Event, IN VOID *Context)
{
    EFI_STATUS status;
    CHAR8 sizeBuf[16];

    DEBUG((DEBUG_INFO, "ReBarDXE: ReadyToBoot event triggered\n"));

    status = FindMcfg();
    if (EFI_ERROR(status)) {
        DEBUG((DEBUG_ERROR, "ReBarDXE: Failed to find MCFG: %r\n", status));
        goto done;
    }

    SizeStr(reBarState, sizeBuf, sizeof(sizeBuf));
    DEBUG((DEBUG_INFO, "ReBarDXE: max BAR size = %a, MMIO alloc base = 0x%lx\n",
           sizeBuf, gMmioNext));

    ScanAllDevices();

done:
    gBS->CloseEvent(Event);
    DEBUG((DEBUG_INFO, "ReBarDXE: ReadyToBoot handler complete\n"));
}

/* ================================================================== */
/*  Driver entry point                                                 */
/* ================================================================== */

EFI_STATUS EFIAPI rebarInit(
    IN EFI_HANDLE       imageHandle,
    IN EFI_SYSTEM_TABLE *systemTable)
{
    EFI_STATUS status;
    EFI_EVENT  event;
    CHAR8      sizeBuf[16];

    SizeStr(reBarState, sizeBuf, sizeof(sizeBuf));

    DEBUG((DEBUG_INFO, "==================================================\n"));
    DEBUG((DEBUG_INFO, "ReBarDXE: Driver loaded, version 7-evict\n"));
    DEBUG((DEBUG_INFO, "ReBarDXE: max BAR size = %a (reBarState=%d)\n",
           sizeBuf, reBarState));
    DEBUG((DEBUG_INFO, "ReBarDXE: MMIO alloc range: 0x%lx - 0x%lx\n",
           MMIO_ALLOC_BASE, MMIO_ALLOC_LIMIT));
    DEBUG((DEBUG_INFO, "ReBarDXE: Below-4G evict range: 0x%lx - 0x%lx\n",
           EVICT_BELOW4G_BASE, EVICT_BELOW4G_LIMIT));
    DEBUG((DEBUG_INFO, "==================================================\n"));

    status = gBS->CreateEventEx(
        EVT_NOTIFY_SIGNAL,
        TPL_CALLBACK,
        ReadyToBootHandler,
        NULL,
        &gEfiEventReadyToBootGuid,
        &event);

    if (EFI_ERROR(status)) {
        DEBUG((DEBUG_ERROR, "ReBarDXE: CreateEventEx failed: %r\n", status));
        return status;
    }

    DEBUG((DEBUG_INFO, "ReBarDXE: Waiting for ReadyToBoot...\n"));
    return EFI_SUCCESS;
}