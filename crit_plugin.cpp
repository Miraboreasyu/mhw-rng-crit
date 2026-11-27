// ============================================================================
//  MHW RNG Official Plugin: Attack Critical Hit & Affinity Controller (`rng_crit.dll`)
//  Version : 1.0.0 (SDK v3.4 Hybrid Architecture)
//
//  Targets (Verified on MHW:I 15.23 Steam build 15539686, ImageBase = 0x140000000):
//    1. Kernel RNG Slot `RVA 0x01F606D6` (`FUN_141f605f0 -> CALL MtRandom::nrand`):
//       Action-start crit seed roll (`[uPlayer+0x8818]` / `+0x881C`). Hooked via
//       MIRA's `RegisterSlotHookEx` to bind deterministic `CondID` streams &
//       lifecycle synchronization (`$rng seed` / `$rng reset` / snapshots).
//    2. Plugin-Internal Quiescence-Safe Detour `RVA 0x01F51380` (`FUN_141f51380`):
//       The single unified hit-time critical evaluator & multiplier caller for
//       all melee, ranged (`uShellPl`), kinsect, and clutch-claw hits.
//       Only intercepts the local main player (`([uPlayer + 0x8938] & 1) != 0`);
//       remote coop players pass straight through to vanilla logic.
//
//  Key Features:
//    - Affinity Source: `auto` (live game calculation via `0x1411c1f50` + `0x1411b9950`,
//      including Weakness Exploit & tenderize) OR manual `rate <-100..100>` override
//      (works even on 0% / negative / 100% weapons!).
//    - 5 Crit Distribution Modes backed by MIRA `CondID` streams:
//        1. `random`  (CondID 1)      : Pure independent Bernoulli roll per hit (zero pity)
//        2. `ratio m:n [block|spread]` / `seq <pat>` : Exact hit-accurate m-crit/n-noncrit cycle
//        3. `mv_bank [mv] [res]`      : Motion-Value priority credit bank (saves crits for big hits)
//        4. `mv_tier [lo hi dLo dHi]` : Separate CondID streams (10/11/12) + affinity deltas by MV
//        5. `bag [N]` / `prd`         : Deterministic shuffle bag (w/ carry) & Dota-style PRD
// ============================================================================
#include "mhw_rng_api.h"
#include "mhw_rng_math.h"
#include "mhw_1523_world.h"
#include "mhw_world_api.h"
#include "mhw_crit_api.h"

#include <windows.h>
#include <intrin.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <cctype>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <string>
#include <vector>

namespace {

// ============================================================================
//  Verified MHW:I 15.23 RVAs & Structure Offsets
// ============================================================================
constexpr std::uint32_t kRvaCritSeed       = 0x01F606D6U; // FUN_141f605f0 -> CALL MtRandom::nrand
constexpr std::uint32_t kRvaApplyCrit      = 0x01F51380U; // FUN_141f51380 (unique crit evaluator)
constexpr std::uint32_t kRvaGetHitSubInfo  = 0x012DBE00U; // FUN_1412dbe00
constexpr std::uint32_t kRvaCalcWeaponAff  = 0x011C1F50U; // FUN_1411c1f50
constexpr std::uint32_t kRvaCalcTotalAff   = 0x011B9950U; // FUN_1411b9950
constexpr std::uint32_t kRvaGetPosCritMult = 0x011C0940U; // FUN_1411c0940
constexpr std::uint32_t kRvaGetNegCritMult = 0x011C0620U; // FUN_1411c0620

constexpr std::uint8_t kPrologueApplyCrit[5] = { 0x48, 0x89, 0x5C, 0x24, 0x08 }; // mov qword ptr [rsp+8], rbx

constexpr std::uintptr_t kOffCritCtxPlayer    = 0x0008U;
constexpr std::uintptr_t kOffHitInfoAtkNode   = 0x0038U; // HitInfo -> attacking cNode*
constexpr std::uintptr_t kOffNodeOrigAtkParam = 0x00A8U; // cNode   -> immutable original cAttackParam*
constexpr std::uintptr_t kOffHitSubCritFlag   = 0x0040U; // == 1 triggers crit-draw flag
constexpr std::uintptr_t kOffPlayerWeapon     = mhw1523::kOffPlayerWeapon;
constexpr std::uintptr_t kOffPlayerStatusMgr  = mhw1523::kOffPlayerStatusMgr;
constexpr std::uintptr_t kOffPlayerCritCursor = mhw1523::kOffPlayerCritCursor;
constexpr std::uintptr_t kOffPlayerLocalFlags = mhw1523::kOffPlayerLocalFlags;
constexpr std::uintptr_t kOffWeaponValidMask  = 0x000CU; // (mask & 0x0E) != 0 -> valid weapon obj
constexpr std::uintptr_t kOffWeaponType       = 0x09F8U; // uint32_t weapon type id
constexpr std::uintptr_t kOffWeaponType3Flag  = 0x2398U; // uint8_t  type 3 alt-MV flag (0x142122e20)
constexpr std::uintptr_t kOffWeaponType9Mode  = 0x2368U; // uint32_t type 9 mode check (0x142133810)
constexpr std::uintptr_t kOffWeaponType9Timer = 0x2470U; // float    type 9 timer (0x142133810)
constexpr std::uintptr_t kOffWeaponType9Flag  = 0x2474U; // uint8_t  type 9 flag (0x142133810)
constexpr std::uintptr_t kOffAtkParamMV       = 0x0020U; // orig: float raw MV; mutable copy: pre-crit raw damage
constexpr std::uintptr_t kOffAtkParamCritRes  = 0x0160U; // int8_t: +1 pos, 0 norm, -1 neg
constexpr std::uintptr_t kOffAtkParamAltMV    = 0x0264U; // float weapon-specific alt/bonus MV

// MIRA Condition IDs allocated under `kRvaCritSeed` (`0x01F606D6`)
constexpr std::uint32_t kCondSeedSlot = 0U;
constexpr std::uint32_t kCondRandom   = 1U;
constexpr std::uint32_t kCondBag      = 2U;
constexpr std::uint32_t kCondPrd      = 3U;
constexpr std::uint32_t kCondMvBank   = 4U;
constexpr std::size_t   kMaxTierCuts  = 7U;
constexpr std::size_t   kMaxTiers     = kMaxTierCuts + 1U; // Up to 8 tiers -> CondIDs 10..17
constexpr std::uint32_t kCondTierBase = 10U;

using DrawDetFn       = std::uint32_t(__fastcall*)(std::uint32_t callSiteRva, std::uint32_t condId);
using ApplyCritFn     = void(__fastcall*)(void* critCtx, void* atkParam,
                                          std::uint8_t isWeakPoint, std::uint8_t force100Crit,
                                          std::uint8_t isTenderized, std::uint8_t extraFlag);
using GetHitSubInfoFn = void*(__fastcall*)(void* hitInfo);
using CalcWeaponAffFn = float(__fastcall*)(void* statusMgr);
using CalcTotalAffFn  = float(__fastcall*)(void* statusMgr, float weaponAff,
                                           std::uint8_t isWeakPoint, std::uint8_t hitDrawFlag,
                                           std::uint8_t isTenderized, std::uint8_t extraFlag);
using GetCritMultFn   = float(__fastcall*)(void* statusMgr);

// ============================================================================
//  Crit Mode & Runtime State Types
// ============================================================================
enum class CritMode : std::uint8_t {
    kVanilla = 0, // Pure game behavior (bypasses crit hook override)
    kObserve = 1, // Vanilla result + per-hit MV/affinity/crit telemetry
    kRandom  = 2, // True independent per-hit roll via MIRA CondID 1
    kRatio   = 3, // Exact m:n hit cycle (`block` / `spread` / custom `seq`)
    kMvBank  = 4, // Motion-Value priority credit bank
    kMvTier  = 5, // Per-MV-tier independent CondID streams & affinity delta
    kBag     = 6, // Fractional-carry deterministic shuffle bag
    kPrd     = 7  // Progressive pseudo-random distribution (bounded miss streak)
};

enum class RatioStyle : std::uint8_t {
    kBlock  = 0, // m crits then n non-crits
    kSpread = 1, // Evenly paced Bresenham m:n
    kCustom = 2  // User custom sequence pattern
};

enum class TierAffKind : std::uint8_t {
    kDelta = 0, // Relative +/-% delta on top of active rate
    kFixed = 1  // Absolute fixed% rate for that MV tier
};

struct BagBucket {
    bool         valid     = false;
    int          affPct    = 0;  // 1..99
    std::uint64_t lruTick  = 0ULL;
    double       fracCarry = 0.0;
    std::size_t  size      = 10U;
    std::size_t  cursor    = 10U;
    std::array<std::uint8_t, 64> slots{};
};

struct PrdBucket {
    bool          valid      = false;
    int           affPct     = 0; // 1..99
    std::uint64_t lruTick    = 0ULL;
    std::uint32_t missStreak = 0U;
};

struct LocalPrngSlot {
    bool          used       = false;
    std::uint32_t condId     = 0U;
    std::uint64_t epoch      = 0ULL;
    std::uint64_t masterSeed = 0ULL;
    std::uint32_t state[4]{};
};

// ============================================================================
//  Globals (Strict Leaf Mutex Discipline: NEVER call g_host while holding g_stateMx)
// ============================================================================
const MhwRngHostApi*              g_host       = nullptr;
MhwRngPluginId                    g_selfId     = 0U;
MhwRngHookHandle                  g_hookSeed   = kMhwRngInvalidHandle;
MhwRngHookHandle                  g_hookLife   = kMhwRngInvalidHandle;
std::atomic<DrawDetFn>            g_drawDetFn{ nullptr };

std::atomic<bool>                 g_shuttingDown{ false };
std::atomic<std::int32_t>         g_inFlightCrit{ 0 };
ApplyCritFn                       g_origApplyCrit = nullptr;
std::uintptr_t                    g_detourSite    = 0;
std::uintptr_t                    g_trampPage     = 0;
std::uint8_t                      g_detourOrig5[5]{};
std::uint8_t                      g_detourJmp5[5]{};
bool                              g_detourActive  = false;

std::mutex                        g_stateMx;
CritMode                          g_mode                = CritMode::kVanilla;
bool                              g_rateOverrideEnabled = false;
int                               g_rateOverridePct     = 100;
bool                              g_verbose             = false;
bool                              g_autoResetOnQuest    = true;
MhwRngHookHandle                  g_worldEvTitle        = kMhwRngInvalidHandle;
MhwRngHookHandle                  g_worldEvQuest        = kMhwRngInvalidHandle;

// Ratio / Sequence params & runtime state
std::uint32_t                     g_ratioM         = 1U;
std::uint32_t                     g_ratioN         = 1U;
RatioStyle                        g_ratioStyle     = RatioStyle::kBlock;
std::size_t                       g_ratioCursor    = 0U;
std::uint64_t                     g_bresenhamAcc   = 0ULL;
std::vector<std::int8_t>          g_customSeq;

// MV Bank params & runtime state
double                            g_mvThreshold    = 50.0;
double                            g_bankReserve    = 1.0;
double                            g_bankCredit     = 0.0;

// MV Tier params (1..7 ascending cutoffs -> 2..8 CondID streams 10..17; default 0% delta)
std::size_t                       g_tierCutCount   = 2U;
std::array<double, kMaxTierCuts>  g_tierCuts       = { 25.0, 60.0, 0.0, 0.0, 0.0, 0.0, 0.0 };
TierAffKind                       g_tierAffKind    = TierAffKind::kDelta;
std::array<int, kMaxTiers>        g_tierAffVals    = { 0, 0, 0, 0, 0, 0, 0, 0 };

// Bag & PRD params + LRU state
std::size_t                       g_bagSize        = 10U;
std::array<BagBucket, 8>          g_bagBuckets{};
std::array<PrdBucket, 8>          g_prdBuckets{};
std::uint64_t                     g_lruSeq         = 0ULL;

// Fallback deterministic PRNG slots (used before first 0x01F606D6 action roll captures DrawDeterministic)
std::array<LocalPrngSlot, 16>     g_localPrngSlots{};

// Telemetry
std::uint64_t                     g_totalHits      = 0ULL;
std::uint64_t                     g_posCrits       = 0ULL;
std::uint64_t                     g_negCrits       = 0ULL;
double                            g_mvSum          = 0.0;
double                            g_mvCritSum      = 0.0;
bool                              g_lastHitValid   = false;
float                             g_lastMv         = 0.0f;
int                               g_lastLiveAff    = 0;
int                               g_lastEffAff     = 0;
std::int8_t                       g_lastOutcome    = 0;
float                             g_lastMult       = 1.0f;

// Cached PRD constants C(p) for p = 1..99 (index 0 unused)
std::once_flag                    g_prdOnce;
std::array<double, 100>           g_prdConstants{};

// ============================================================================
//  Deterministic Math Helpers (Exact MHW Xorshift128 + PRD Solver)
// ============================================================================
using mhw_sdk::SplitMix64;
using mhw_sdk::DeriveMhwXorshift128;
using mhw_sdk::StepMhwXorshift128;

double PrdExpectedRate(double c) noexcept {
    double probFail = 1.0;
    double sumE     = 0.0;
    const int maxN  = static_cast<int>(std::ceil(1.0 / c)) + 1;
    for (int n = 1; n <= maxN; ++n) {
        const double pn = (std::min)(1.0, c * static_cast<double>(n));
        sumE += probFail * pn * static_cast<double>(n);
        probFail *= (1.0 - pn);
        if (pn >= 1.0) break;
    }
    return (sumE > 0.0) ? (1.0 / sumE) : 1.0;
}

void EnsurePrdTable() noexcept {
    std::call_once(g_prdOnce, []() {
        g_prdConstants.fill(1.0);
        for (int p = 1; p < 100; ++p) {
            const double target = static_cast<double>(p) / 100.0;
            double lo = 1e-6;
            double hi = 1.0;
            for (int iter = 0; iter < 52; ++iter) {
                const double mid = 0.5 * (lo + hi);
                if (PrdExpectedRate(mid) < target) {
                    lo = mid;
                } else {
                    hi = mid;
                }
            }
            g_prdConstants[static_cast<std::size_t>(p)] = 0.5 * (lo + hi);
        }
    });
}

std::uint32_t DrawFromKernelOrFallback(std::uint32_t condId,
                                       std::uint64_t masterSeed,
                                       std::uint64_t epoch) noexcept {
    if (const DrawDetFn fn = g_drawDetFn.load(std::memory_order_acquire)) {
        return fn(kRvaCritSeed, condId);
    }
    std::lock_guard<std::mutex> lk(g_stateMx);
    LocalPrngSlot* chosen = nullptr;
    for (auto& s : g_localPrngSlots) {
        if (s.used && s.condId == condId) {
            chosen = &s;
            break;
        }
        if (!s.used && !chosen) {
            chosen = &s;
        }
    }
    if (!chosen) chosen = &g_localPrngSlots[0];
    if (!chosen->used || chosen->condId != condId ||
        chosen->epoch != epoch || chosen->masterSeed != masterSeed) {
        chosen->used       = true;
        chosen->condId     = condId;
        chosen->epoch      = epoch;
        chosen->masterSeed = masterSeed;
        DeriveMhwXorshift128(masterSeed ^ (epoch * 0x9E3779B97F4A7C15ULL),
                             kRvaCritSeed, condId, chosen->state);
    }
    return StepMhwXorshift128(chosen->state);
}

// ============================================================================
//  Self-Contained Strict-W^X 5-Byte Detour + Hot-Unload Drain for 0x141f51380
// ============================================================================
bool InRel32(std::uintptr_t from, std::uintptr_t to) noexcept {
    const std::int64_t d = static_cast<std::int64_t>(to) - static_cast<std::int64_t>(from);
    return d >= INT32_MIN && d <= INT32_MAX;
}

void EmitAbsJmp14(std::uint8_t* dst, std::uintptr_t target) noexcept {
    dst[0] = 0xFF;
    dst[1] = 0x25;
    dst[2] = 0x00;
    dst[3] = 0x00;
    dst[4] = 0x00;
    dst[5] = 0x00;
    const auto t64 = static_cast<std::uint64_t>(target);
    std::memcpy(dst + 6U, &t64, 8);
}

std::uintptr_t AllocNearPage(std::uintptr_t anchor, std::size_t size) noexcept {
    SYSTEM_INFO si{};
    ::GetSystemInfo(&si);
    const std::uintptr_t gran  = si.dwAllocationGranularity ? si.dwAllocationGranularity : 0x10000ULL;
    const std::uintptr_t sysLo = reinterpret_cast<std::uintptr_t>(si.lpMinimumApplicationAddress);
    const std::uintptr_t sysHi = reinterpret_cast<std::uintptr_t>(si.lpMaximumApplicationAddress);

    const std::uintptr_t minAddr = (std::max<std::uintptr_t>)(
        (anchor > 0x7E000000ULL) ? (anchor - 0x7E000000ULL) : 0x10000ULL,
        (std::max<std::uintptr_t>)(gran, sysLo));
    const std::uintptr_t maxAddr = (std::min<std::uintptr_t>)(anchor + 0x7E000000ULL, sysHi);
    if (maxAddr <= minAddr + size) return 0;

    std::uintptr_t cur = anchor;
    for (int iter = 0; iter < 1000000 && cur > minAddr; ++iter) {
        MEMORY_BASIC_INFORMATION mbi{};
        if (::VirtualQuery(reinterpret_cast<LPCVOID>(cur - 1U), &mbi, sizeof(mbi)) == 0) break;
        const auto regBase = reinterpret_cast<std::uintptr_t>(mbi.BaseAddress);
        const auto regEnd  = regBase + mbi.RegionSize;
        if (mbi.State == MEM_FREE) {
            const std::uintptr_t lo = (std::max)(minAddr, regBase);
            const std::uintptr_t hi = (std::min)(cur, regEnd);
            if (hi >= lo + size) {
                std::uintptr_t cand = (hi - size) & ~(gran - 1ULL);
                for (int tries = 0; tries < 4096 && cand >= lo; ++tries) {
                    if (cand + size <= hi) {
                        if (void* p = ::VirtualAlloc(reinterpret_cast<void*>(cand), size,
                                                     MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE)) {
                            return reinterpret_cast<std::uintptr_t>(p);
                        }
                    }
                    if (cand < gran) break;
                    cand -= gran;
                }
            }
        }
        if (regBase <= minAddr || regBase >= cur) break;
        cur = regBase;
    }

    cur = anchor;
    for (int iter = 0; iter < 1000000 && cur + size <= maxAddr; ++iter) {
        MEMORY_BASIC_INFORMATION mbi{};
        if (::VirtualQuery(reinterpret_cast<LPCVOID>(cur), &mbi, sizeof(mbi)) == 0) break;
        const auto regBase = reinterpret_cast<std::uintptr_t>(mbi.BaseAddress);
        const auto regEnd  = regBase + mbi.RegionSize;
        if (mbi.State == MEM_FREE) {
            const std::uintptr_t lo = (std::max)(minAddr, regBase);
            const std::uintptr_t hi = (std::min)(maxAddr, regEnd);
            std::uintptr_t cand = (lo + gran - 1ULL) & ~(gran - 1ULL);
            for (int tries = 0; tries < 4096 && cand + size <= hi; ++tries) {
                if (void* p = ::VirtualAlloc(reinterpret_cast<void*>(cand), size,
                                             MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE)) {
                    return reinterpret_cast<std::uintptr_t>(p);
                }
                cand += gran;
            }
        }
        if (regEnd <= cur || regEnd >= maxAddr) break;
        cur = regEnd;
    }

    void* rejected[32]{};
    int rejectedCnt = 0;
    std::uintptr_t chosen = 0;
    for (int probe = 0; probe < 32; ++probe) {
        void* p = ::VirtualAlloc(nullptr, size, MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE);
        if (!p) break;
        const auto addr = reinterpret_cast<std::uintptr_t>(p);
        if (addr >= minAddr && addr + size <= maxAddr) {
            chosen = addr;
            break;
        }
        rejected[rejectedCnt++] = p;
    }
    for (int i = 0; i < rejectedCnt; ++i) {
        ::VirtualFree(rejected[i], 0, MEM_RELEASE);
    }
    return chosen;
}

bool CompareAndPatch5BytesSafe(std::uintptr_t site,
                               const std::uint8_t expected5[5],
                               const std::uint8_t new5[5]) noexcept {
    DWORD oldProt = 0;
    if (!::VirtualProtect(reinterpret_cast<void*>(site), 8, PAGE_EXECUTE_READWRITE, &oldProt)) {
        return false;
    }
    bool patched = false;
    if ((site & 0x7ULL) == 0ULL) {
        auto* qwordPtr = reinterpret_cast<volatile LONG64*>(site);
        LONG64 cur = *qwordPtr;
        for (;;) {
            if (std::memcmp(&cur, expected5, 5) != 0) {
                patched = false;
                break;
            }
            LONG64 desired = cur;
            std::memcpy(&desired, new5, 5);
            const LONG64 prev = _InterlockedCompareExchange64(qwordPtr, desired, cur);
            if (prev == cur) {
                patched = true;
                break;
            }
            cur = prev;
        }
    } else if (std::memcmp(reinterpret_cast<const void*>(site), expected5, 5) == 0) {
        std::memcpy(reinterpret_cast<void*>(site), new5, 5);
        patched = true;
    }
    DWORD tmp = 0;
    ::VirtualProtect(reinterpret_cast<void*>(site), 8, oldProt, &tmp);
    if (patched) {
        ::FlushInstructionCache(::GetCurrentProcess(), reinterpret_cast<void*>(site), 8);
    }
    return patched;
}

// ============================================================================
//  SEH-Guarded Game Struct Reads & Calls
// ============================================================================
bool TryReadBoolLocalPlayerSEH(std::uintptr_t critCtx,
                               std::uintptr_t& outPlayer,
                               std::uintptr_t& outStatusMgr,
                               bool& outIsLocal) noexcept {
    outPlayer    = 0ULL;
    outStatusMgr = 0ULL;
    outIsLocal   = false;
    __try {
        outPlayer = *reinterpret_cast<const std::uintptr_t*>(critCtx + kOffCritCtxPlayer);
        if (outPlayer < 0x10000ULL) return false;
        const auto flags = *reinterpret_cast<const std::uint8_t*>(outPlayer + kOffPlayerLocalFlags);
        outIsLocal   = ((flags & 1U) != 0U);
        outStatusMgr = *reinterpret_cast<const std::uintptr_t*>(outPlayer + kOffPlayerStatusMgr);
        return true;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        outPlayer    = 0ULL;
        outStatusMgr = 0ULL;
        outIsLocal   = false;
        return false;
    }
}

bool TryReadFloatSEH(std::uintptr_t addr, float& outVal) noexcept {
    outVal = 0.0f;
    __try {
        outVal = *reinterpret_cast<const float*>(addr);
        return true;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return false;
    }
}

bool TryReadInt8SEH(std::uintptr_t addr, std::int8_t& outVal) noexcept {
    outVal = 0;
    __try {
        outVal = *reinterpret_cast<const std::int8_t*>(addr);
        return true;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return false;
    }
}

bool TryReadOriginalMotionValueSEH(void* critCtx, std::uintptr_t uPlayer, float& outMv) noexcept {
    outMv = 0.0f;
    if (!critCtx) return false;
    __try {
        void** const pHitInfo = *reinterpret_cast<void***>(critCtx);
        if (reinterpret_cast<std::uintptr_t>(pHitInfo) < 0x10000ULL) return false;
        const auto hitInfo = reinterpret_cast<std::uintptr_t>(*pHitInfo);
        if (hitInfo < 0x10000ULL) return false;
        const auto atkNode = *reinterpret_cast<const std::uintptr_t*>(hitInfo + kOffHitInfoAtkNode);
        if (atkNode < 0x10000ULL) return false;
        const auto origAtkParam = *reinterpret_cast<const std::uintptr_t*>(atkNode + kOffNodeOrigAtkParam);
        if (origAtkParam < 0x10000ULL) return false;

        float mv = *reinterpret_cast<const float*>(origAtkParam + kOffAtkParamMV);
        if (uPlayer >= 0x10000ULL) {
            const auto uWep = *reinterpret_cast<const std::uintptr_t*>(uPlayer + kOffPlayerWeapon);
            if (uWep >= 0x10000ULL &&
                (*reinterpret_cast<const std::uint8_t*>(uWep + kOffWeaponValidMask) & 0x0EU) != 0U) {
                const std::uint32_t wepType = *reinterpret_cast<const std::uint32_t*>(uWep + kOffWeaponType);
                if (wepType == 3U && *reinterpret_cast<const std::uint8_t*>(uWep + kOffWeaponType3Flag) != 0U) {
                    const float altMv = *reinterpret_cast<const float*>(origAtkParam + kOffAtkParamAltMV);
                    if (std::isfinite(altMv) && altMv > 0.0f) mv = altMv;
                } else if (wepType == 9U &&
                           (*reinterpret_cast<const float*>(uWep + kOffWeaponType9Timer) > 0.0f ||
                            *reinterpret_cast<const std::uint8_t*>(uWep + kOffWeaponType9Flag) != 0U) &&
                           *reinterpret_cast<const std::uint32_t*>(uWep + kOffWeaponType9Mode) == 0U) {
                    const float altMv = *reinterpret_cast<const float*>(origAtkParam + kOffAtkParamAltMV);
                    if (std::isfinite(altMv) && altMv > 0.0f) mv += altMv;
                }
            }
        }
        if (!std::isfinite(mv) || mv < 0.0f || mv > 10000.0f) return false;
        outMv = mv;
        return true;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        outMv = 0.0f;
        return false;
    }
}

void AdvancePlayerCritCursorSEH(std::uintptr_t uPlayer) noexcept {
    __try {
        auto* pCur = reinterpret_cast<std::uint32_t*>(uPlayer + kOffPlayerCritCursor);
        const std::uint32_t next = *pCur + 1U;
        *pCur = (next >= 32U) ? 0U : next;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
    }
}

bool ComputeLiveAffinitySEH(std::uintptr_t exeBase,
                            void* critCtx,
                            std::uintptr_t statusMgr,
                            std::uint8_t isWeakPoint,
                            std::uint8_t force100Crit,
                            std::uint8_t isTenderized,
                            std::uint8_t extraFlag,
                            int& outAffPct) noexcept {
    outAffPct = 0;
    if (force100Crit != 0U) {
        outAffPct = 100;
        return true;
    }
    if (!statusMgr || !exeBase) return false;
    __try {
        std::uint8_t hitDrawFlag = 0U;
        void** pHitInfo = *reinterpret_cast<void***>(critCtx);
        if (pHitInfo) {
            void* hitInfo = *pHitInfo;
            if (hitInfo) {
                const auto fnGetSub = reinterpret_cast<GetHitSubInfoFn>(exeBase + kRvaGetHitSubInfo);
                void* subInfo = fnGetSub(hitInfo);
                if (subInfo) {
                    const std::uint32_t v = *reinterpret_cast<const std::uint32_t*>(
                        reinterpret_cast<std::uintptr_t>(subInfo) + kOffHitSubCritFlag);
                    if (v == 1U) hitDrawFlag = 1U;
                }
            }
        }
        const auto fnWepAff   = reinterpret_cast<CalcWeaponAffFn>(exeBase + kRvaCalcWeaponAff);
        const auto fnTotalAff = reinterpret_cast<CalcTotalAffFn>(exeBase + kRvaCalcTotalAff);
        const float wepAff    = fnWepAff(reinterpret_cast<void*>(statusMgr));
        const float totAff    = fnTotalAff(reinterpret_cast<void*>(statusMgr), wepAff,
                                           isWeakPoint, hitDrawFlag, isTenderized, extraFlag);
        outAffPct = static_cast<int>(totAff);
        return true;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        outAffPct = 0;
        return false;
    }
}

bool ApplyCritOutcomeSEH(std::uintptr_t exeBase,
                         void* atkParam,
                         std::uintptr_t statusMgr,
                         std::int8_t outcome,
                         float baseMv,
                         float& outMult) noexcept {
    outMult = 1.0f;
    if (!atkParam) return false;
    __try {
        const auto atkAddr = reinterpret_cast<std::uintptr_t>(atkParam);
        if (outcome > 0) {
            float mult = 1.25f;
            if (exeBase && statusMgr) {
                const auto fnPos = reinterpret_cast<GetCritMultFn>(exeBase + kRvaGetPosCritMult);
                mult = fnPos(reinterpret_cast<void*>(statusMgr));
            }
            *reinterpret_cast<std::int8_t*>(atkAddr + kOffAtkParamCritRes) = 1;
            *reinterpret_cast<float*>(atkAddr + kOffAtkParamMV)            = baseMv * mult;
            outMult = mult;
        } else if (outcome < 0) {
            float mult = 0.75f;
            if (exeBase && statusMgr) {
                const auto fnNeg = reinterpret_cast<GetCritMultFn>(exeBase + kRvaGetNegCritMult);
                mult = fnNeg(reinterpret_cast<void*>(statusMgr));
            }
            *reinterpret_cast<std::int8_t*>(atkAddr + kOffAtkParamCritRes) = -1;
            *reinterpret_cast<float*>(atkAddr + kOffAtkParamMV)            = baseMv * mult;
            outMult = mult;
        } else {
            *reinterpret_cast<std::int8_t*>(atkAddr + kOffAtkParamCritRes) = 0;
            outMult = 1.0f;
        }
        return true;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return false;
    }
}

// ============================================================================
//  State Reset & String Utilities
// ============================================================================
std::string LowerAscii(const char* s) {
    if (!s) return {};
    std::string out(s);
    for (char& c : out) {
        c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    }
    return out;
}

void ResetRuntimeStreamsLocked() noexcept {
    g_ratioCursor  = 0U;
    g_bresenhamAcc = 0ULL;
    g_bankCredit   = 0.0;
    for (auto& b : g_bagBuckets) b = BagBucket{};
    for (auto& p : g_prdBuckets) p = PrdBucket{};
    for (auto& s : g_localPrngSlots) s = LocalPrngSlot{};
    g_lruSeq = 0ULL;
}

void ResetTelemetryLocked() noexcept {
    g_totalHits    = 0ULL;
    g_posCrits     = 0ULL;
    g_negCrits     = 0ULL;
    g_mvSum        = 0.0;
    g_mvCritSum    = 0.0;
    g_lastHitValid = false;
    g_lastMv       = 0.0f;
    g_lastLiveAff  = 0;
    g_lastEffAff   = 0;
    g_lastOutcome  = 0;
    g_lastMult     = 1.0f;
}

const char* ModeName(CritMode m, bool en) noexcept {
    switch (m) {
        case CritMode::kVanilla: return en ? "vanilla" : u8"原版";
        case CritMode::kObserve: return en ? "observe" : u8"观测";
        case CritMode::kRandom:  return en ? "random"  : u8"纯随机";
        case CritMode::kRatio:   return en ? "ratio"   : u8"定比/序列";
        case CritMode::kMvBank:  return en ? "mv_bank" : u8"动作值预算";
        case CritMode::kMvTier:  return en ? "mv_tier" : u8"动作值分档";
        case CritMode::kBag:     return en ? "bag"     : u8"洗牌袋";
        case CritMode::kPrd:     return en ? "prd"     : u8"PRD保底";
        default:                 return "?";
    }
}

BagBucket& FindOrAllocBagBucketLocked(int absAffPct, std::size_t bagSize) noexcept {
    BagBucket* empty = nullptr;
    BagBucket* lru   = &g_bagBuckets[0];
    for (auto& b : g_bagBuckets) {
        if (b.valid && b.affPct == absAffPct && b.size == bagSize) {
            b.lruTick = ++g_lruSeq;
            return b;
        }
        if (!b.valid && !empty) empty = &b;
        if (b.valid && (!lru->valid || b.lruTick < lru->lruTick)) lru = &b;
    }
    BagBucket* dst = empty ? empty : lru;
    *dst           = BagBucket{};
    dst->valid     = true;
    dst->affPct    = absAffPct;
    dst->size      = bagSize;
    dst->cursor    = bagSize; // Triggers immediate refill
    dst->lruTick   = ++g_lruSeq;
    return *dst;
}

PrdBucket& FindOrAllocPrdBucketLocked(int absAffPct) noexcept {
    PrdBucket* empty = nullptr;
    PrdBucket* lru   = &g_prdBuckets[0];
    for (auto& b : g_prdBuckets) {
        if (b.valid && b.affPct == absAffPct) {
            b.lruTick = ++g_lruSeq;
            return b;
        }
        if (!b.valid && !empty) empty = &b;
        if (b.valid && (!lru->valid || b.lruTick < lru->lruTick)) lru = &b;
    }
    PrdBucket* dst = empty ? empty : lru;
    *dst           = PrdBucket{};
    dst->valid     = true;
    dst->affPct    = absAffPct;
    dst->lruTick   = ++g_lruSeq;
    return *dst;
}

// ============================================================================
//  Detour Entry Point: `FUN_141f51380` (`RVA 0x01F51380`)
// ============================================================================
struct InFlightGuard {
    InFlightGuard() noexcept  { g_inFlightCrit.fetch_add(1, std::memory_order_acq_rel); }
    ~InFlightGuard() noexcept { g_inFlightCrit.fetch_sub(1, std::memory_order_acq_rel); }
};

struct ConfigSnap {
    CritMode                        mode                 = CritMode::kVanilla;
    bool                            rateOverrideEnabled  = false;
    int                             rateOverridePct      = 100;
    bool                            verbose              = false;
    double                          mvThreshold          = 50.0;
    double                          bankReserve          = 1.0;
    std::size_t                     tierCutCount         = 2U;
    std::array<double, kMaxTierCuts> tierCuts{};
    TierAffKind                     tierAffKind          = TierAffKind::kDelta;
    std::array<int, kMaxTiers>      tierAffVals{};
    std::size_t                     bagSize              = 10U;
};

void __fastcall Hook_ApplyCrit(void* critCtx,
                               void* atkParam,
                               std::uint8_t isWeakPoint,
                               std::uint8_t force100Crit,
                               std::uint8_t isTenderized,
                               std::uint8_t extraFlag) {
    InFlightGuard flight;
    const ApplyCritFn origFn = g_origApplyCrit;
    if (!origFn) return;

    const MhwRngHostApi* host = g_host;
    if (g_shuttingDown.load(std::memory_order_acquire) || !host || !critCtx || !atkParam) {
        origFn(critCtx, atkParam, isWeakPoint, force100Crit, isTenderized, extraFlag);
        return;
    }

    const std::uint32_t engMode = host->GetEngineMode();
    if (engMode == kMhwRngModeOff) {
        origFn(critCtx, atkParam, isWeakPoint, force100Crit, isTenderized, extraFlag);
        return;
    }

    std::uintptr_t uPlayer   = 0ULL;
    std::uintptr_t statusMgr = 0ULL;
    bool           isLocal   = false;
    if (!TryReadBoolLocalPlayerSEH(reinterpret_cast<std::uintptr_t>(critCtx),
                                   uPlayer, statusMgr, isLocal) ||
        !isLocal) {
        // Remote coop player replicas or malformed ctx: strictly pass through vanilla!
        origFn(critCtx, atkParam, isWeakPoint, force100Crit, isTenderized, extraFlag);
        return;
    }

    ConfigSnap cfg{};
    {
        std::lock_guard<std::mutex> lk(g_stateMx);
        cfg.mode                = g_mode;
        cfg.rateOverrideEnabled = g_rateOverrideEnabled;
        cfg.rateOverridePct     = g_rateOverridePct;
        cfg.verbose             = g_verbose;
        cfg.mvThreshold         = g_mvThreshold;
        cfg.bankReserve         = g_bankReserve;
        cfg.tierCutCount        = g_tierCutCount;
        cfg.tierCuts            = g_tierCuts;
        cfg.tierAffKind         = g_tierAffKind;
        cfg.tierAffVals         = g_tierAffVals;
        cfg.bagSize             = g_bagSize;
    }

    if (cfg.mode == CritMode::kVanilla) {
        origFn(critCtx, atkParam, isWeakPoint, force100Crit, isTenderized, extraFlag);
        return;
    }

    const std::uintptr_t exeBase = host->exeBase;
    float preCritRawDmg = 0.0f;
    (void)TryReadFloatSEH(reinterpret_cast<std::uintptr_t>(atkParam) + kOffAtkParamMV, preCritRawDmg);
    float trueMvF = 0.0f;
    const bool hasTrueMv = TryReadOriginalMotionValueSEH(critCtx, uPlayer, trueMvF);
    const double mvVal = hasTrueMv
                             ? static_cast<double>(trueMvF)
                             : ((std::isfinite(preCritRawDmg) && preCritRawDmg > 0.0f)
                                    ? static_cast<double>(preCritRawDmg)
                                    : 0.0);

    int liveAff = 0;
    (void)ComputeLiveAffinitySEH(exeBase, critCtx, statusMgr,
                                 isWeakPoint, force100Crit, isTenderized, extraFlag,
                                 liveAff);

    // Observe mode (either kernel kMhwRngModeObserveOnly OR plugin `observe`): run vanilla & record stats
    if (engMode == kMhwRngModeObserveOnly || cfg.mode == CritMode::kObserve) {
        origFn(critCtx, atkParam, isWeakPoint, force100Crit, isTenderized, extraFlag);
        std::int8_t res = 0;
        (void)TryReadInt8SEH(reinterpret_cast<std::uintptr_t>(atkParam) + kOffAtkParamCritRes, res);
        float mvAfter = preCritRawDmg;
        (void)TryReadFloatSEH(reinterpret_cast<std::uintptr_t>(atkParam) + kOffAtkParamMV, mvAfter);
        const float mult = (preCritRawDmg > 0.0001f) ? (mvAfter / preCritRawDmg) : 1.0f;

        std::uint64_t hitNo = 0ULL;
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            ++g_totalHits;
            hitNo = g_totalHits;
            if (res > 0) ++g_posCrits;
            else if (res < 0) ++g_negCrits;
            g_mvSum += mvVal;
            if (res > 0) g_mvCritSum += mvVal;
            g_lastHitValid = true;
            g_lastMv       = static_cast<float>(mvVal);
            g_lastLiveAff  = liveAff;
            g_lastEffAff   = liveAff;
            g_lastOutcome  = res;
            g_lastMult     = mult;
        }
        if (cfg.verbose) {
            const bool en = MhwRng_HostIsEnglish(host);
            const char* tag = (res > 0) ? (en ? "CRIT+" : u8"正会心")
                            : (res < 0) ? (en ? "CRIT-" : u8"负会心")
                                        : (en ? "NORM"  : u8"普通");
            host->ChatPrintfAsync(en ? "[crit #%llu][OBS] MV=%.1f Aff=%d%% -> %s (x%.2f)"
                                     : u8"[会心 #%llu][观测] 动作值=%.1f 会心=%d%% -> %s (x%.2f)",
                                  static_cast<unsigned long long>(hitNo),
                                  mvVal, liveAff, tag, static_cast<double>(mult));
        }
        return;
    }

    // Active Takeover / Selective Mode
    const int effAffRaw = cfg.rateOverrideEnabled ? cfg.rateOverridePct : liveAff;
    const int effAff    = (std::max)(-100, (std::min)(100, effAffRaw));
    const std::uint64_t masterSeed = host->GetMasterSeed();
    const std::uint64_t epoch      = host->GetEpoch();

    // Draw deterministic RNG value(s) OUTSIDE g_stateMx to keep g_stateMx a strict leaf mutex
    std::uint32_t preDrawU32 = 0U;
    std::array<std::uint32_t, 64> bagShuffleDraws{};
    int           tierEffAff = effAff;
    std::size_t   tierIdx    = 0U;
    std::uint32_t tierCond   = kCondTierBase;

    if (cfg.mode == CritMode::kRandom) {
        if (effAff != 0 && std::abs(effAff) < 100) {
            preDrawU32 = DrawFromKernelOrFallback(kCondRandom, masterSeed, epoch);
        }
    } else if (cfg.mode == CritMode::kMvTier) {
        while (tierIdx < cfg.tierCutCount && mvVal >= cfg.tierCuts[tierIdx]) {
            ++tierIdx;
        }
        tierCond = kCondTierBase + static_cast<std::uint32_t>(tierIdx);
        const int rawSpec = cfg.tierAffVals[tierIdx];
        const int combined = (cfg.tierAffKind == TierAffKind::kFixed) ? rawSpec : (effAff + rawSpec);
        tierEffAff = (std::max)(-100, (std::min)(100, combined));
        if (tierEffAff != 0 && std::abs(tierEffAff) < 100) {
            preDrawU32 = DrawFromKernelOrFallback(tierCond, masterSeed, epoch);
        }
    } else if (cfg.mode == CritMode::kPrd) {
        EnsurePrdTable();
        if (effAff != 0 && std::abs(effAff) < 100) {
            preDrawU32 = DrawFromKernelOrFallback(kCondPrd, masterSeed, epoch);
        }
    } else if (cfg.mode == CritMode::kBag) {
        const int absAff = std::abs(effAff);
        if (absAff > 0 && absAff < 100) {
            bool needRefill = false;
            {
                std::lock_guard<std::mutex> lk(g_stateMx);
                const BagBucket& b = FindOrAllocBagBucketLocked(absAff, cfg.bagSize);
                needRefill = (b.cursor >= b.size);
            }
            if (needRefill) {
                for (std::size_t i = 0; i < cfg.bagSize; ++i) {
                    bagShuffleDraws[i] = DrawFromKernelOrFallback(kCondBag, masterSeed, epoch);
                }
            }
        }
    }

    std::int8_t   outcome         = 0;
    double        bankSnapshot    = 0.0;
    RatioStyle    ratioStyleSnap  = RatioStyle::kBlock;
    std::size_t   ratioStepOne    = 0U;
    std::size_t   ratioPeriodSnap = 0U;
    std::uint32_t ratioMSnap      = 0U;
    std::uint32_t ratioNSnap      = 0U;
    {
        std::lock_guard<std::mutex> lk(g_stateMx);
        const std::int8_t critSign = (effAff < 0) ? -1 : 1;
        const int absAff           = std::abs(effAff);

        switch (g_mode) {
            case CritMode::kRandom: {
                if (absAff == 0) outcome = 0;
                else if (absAff >= 100) outcome = critSign;
                else outcome = ((preDrawU32 % 100U) < static_cast<std::uint32_t>(absAff)) ? critSign : 0;
                break;
            }
            case CritMode::kMvTier: {
                const int tSign = (tierEffAff < 0) ? -1 : 1;
                const int tAbs  = std::abs(tierEffAff);
                if (tAbs == 0) outcome = 0;
                else if (tAbs >= 100) outcome = static_cast<std::int8_t>(tSign);
                else outcome = ((preDrawU32 % 100U) < static_cast<std::uint32_t>(tAbs))
                                   ? static_cast<std::int8_t>(tSign)
                                   : 0;
                break;
            }
            case CritMode::kRatio: {
                if (g_ratioStyle == RatioStyle::kCustom && !g_customSeq.empty()) {
                    const std::size_t idx = g_ratioCursor % g_customSeq.size();
                    g_ratioCursor = idx + 1U;
                    outcome         = g_customSeq[idx];
                    ratioStyleSnap  = RatioStyle::kCustom;
                    ratioStepOne    = idx + 1U;
                    ratioPeriodSnap = g_customSeq.size();
                } else {
                    const std::uint32_t m = g_ratioM;
                    const std::uint32_t n = g_ratioN;
                    const std::uint32_t period = m + n;
                    if (period == 0U) {
                        outcome = 0;
                    } else if (g_ratioStyle == RatioStyle::kSpread) {
                        const std::size_t idx = g_ratioCursor % period;
                        g_ratioCursor = idx + 1U;
                        g_bresenhamAcc += m;
                        if (g_bresenhamAcc >= period) {
                            g_bresenhamAcc -= period;
                            outcome = critSign;
                        } else {
                            outcome = 0;
                        }
                        ratioStyleSnap  = RatioStyle::kSpread;
                        ratioStepOne    = idx + 1U;
                        ratioPeriodSnap = period;
                        ratioMSnap      = m;
                        ratioNSnap      = n;
                    } else {
                        const std::size_t idx = g_ratioCursor % period;
                        g_ratioCursor = idx + 1U;
                        outcome = (idx < m) ? critSign : 0;
                        ratioStyleSnap  = RatioStyle::kBlock;
                        ratioStepOne    = idx + 1U;
                        ratioPeriodSnap = period;
                        ratioMSnap      = m;
                        ratioNSnap      = n;
                    }
                }
                break;
            }
            case CritMode::kMvBank: {
                if (absAff == 0) {
                    outcome = 0;
                } else if (absAff >= 100) {
                    outcome = critSign;
                } else {
                    g_bankCredit += static_cast<double>(absAff) / 100.0;
                    const double overflowThresh = 1.0 + g_bankReserve;
                    const bool isHighMv         = (mvVal >= g_mvThreshold);
                    if (isHighMv) {
                        if (g_bankCredit >= 0.5) {
                            g_bankCredit -= 1.0;
                            outcome = critSign;
                        } else {
                            outcome = 0;
                        }
                    } else {
                        if (g_bankCredit >= overflowThresh) {
                            g_bankCredit -= 1.0;
                            outcome = critSign;
                        } else {
                            outcome = 0;
                        }
                    }
                    g_bankCredit = (std::max)(-1.0, (std::min)(overflowThresh + 2.0, g_bankCredit));
                }
                bankSnapshot = g_bankCredit;
                break;
            }
            case CritMode::kBag: {
                if (absAff == 0) {
                    outcome = 0;
                } else if (absAff >= 100) {
                    outcome = critSign;
                } else {
                    BagBucket& b = FindOrAllocBagBucketLocked(absAff, g_bagSize);
                    if (b.cursor >= b.size) {
                        const double exact =
                            (static_cast<double>(b.size) * static_cast<double>(absAff)) / 100.0 + b.fracCarry;
                        int crits = static_cast<int>(std::floor(exact + 1e-9));
                        crits = (std::max)(0, (std::min)(static_cast<int>(b.size), crits));
                        b.fracCarry = exact - static_cast<double>(crits);
                        for (std::size_t i = 0; i < b.size; ++i) {
                            b.slots[i] = (i < static_cast<std::size_t>(crits)) ? 1U : 0U;
                        }
                        for (std::size_t i = b.size; i > 1U; --i) {
                            const std::size_t j = bagShuffleDraws[b.size - i] % i;
                            std::swap(b.slots[i - 1U], b.slots[j]);
                        }
                        b.cursor = 0U;
                    }
                    outcome = (b.slots[b.cursor++] != 0U) ? critSign : 0;
                }
                break;
            }
            case CritMode::kPrd: {
                if (absAff == 0) {
                    outcome = 0;
                } else if (absAff >= 100) {
                    outcome = critSign;
                } else {
                    PrdBucket& p = FindOrAllocPrdBucketLocked(absAff);
                    const double c = g_prdConstants[static_cast<std::size_t>(absAff)];
                    const double thresh = (std::min)(1.0, c * static_cast<double>(p.missStreak + 1U));
                    const double u = static_cast<double>(preDrawU32 % 1000000U) / 1000000.0;
                    if (u < thresh) {
                        p.missStreak = 0U;
                        outcome = critSign;
                    } else {
                        ++p.missStreak;
                        outcome = 0;
                    }
                }
                break;
            }
            default:
                outcome = 0;
                break;
        }
    }

    AdvancePlayerCritCursorSEH(uPlayer);
    float appliedMult = 1.0f;
    (void)ApplyCritOutcomeSEH(exeBase, atkParam, statusMgr, outcome, preCritRawDmg, appliedMult);

    std::uint64_t hitNo = 0ULL;
    {
        std::lock_guard<std::mutex> lk(g_stateMx);
        ++g_totalHits;
        hitNo = g_totalHits;
        if (outcome > 0) ++g_posCrits;
        else if (outcome < 0) ++g_negCrits;
        g_mvSum += mvVal;
        if (outcome > 0) g_mvCritSum += mvVal;
        g_lastHitValid = true;
        g_lastMv       = static_cast<float>(mvVal);
        g_lastLiveAff  = liveAff;
        g_lastEffAff   = (cfg.mode == CritMode::kMvTier) ? tierEffAff : effAff;
        g_lastOutcome  = outcome;
        g_lastMult     = appliedMult;
    }

    if (cfg.verbose) {
        const bool en = MhwRng_HostIsEnglish(host);
        const char* tag = (outcome > 0) ? (en ? "CRIT+" : u8"正会心")
                        : (outcome < 0) ? (en ? "CRIT-" : u8"负会心")
                                        : (en ? "NORM"  : u8"普通");
        if (cfg.mode == CritMode::kMvBank) {
            host->ChatPrintfAsync(
                en ? "[crit #%llu][%s] MV=%.1f Aff=%d%% -> %s (x%.2f, bank=%.2f)"
                   : u8"[会心 #%llu][%s] 动作值=%.1f 会心=%d%% -> %s (x%.2f, 额度=%.2f)",
                static_cast<unsigned long long>(hitNo),
                ModeName(cfg.mode, en), mvVal, effAff, tag,
                static_cast<double>(appliedMult), bankSnapshot);
        } else if (cfg.mode == CritMode::kMvTier) {
            host->ChatPrintfAsync(
                en ? "[crit #%llu][%s T%zu/C%u] MV=%.1f Aff=%d%% -> %s (x%.2f)"
                   : u8"[会心 #%llu][%s 档%zu/槽%u] 动作值=%.1f 会心=%d%% -> %s (x%.2f)",
                static_cast<unsigned long long>(hitNo),
                ModeName(cfg.mode, en), tierIdx + 1U, tierCond, mvVal, tierEffAff,
                tag, static_cast<double>(appliedMult));
        } else if (cfg.mode == CritMode::kRatio) {
            if (ratioStyleSnap == RatioStyle::kCustom) {
                host->ChatPrintfAsync(
                    en ? "[crit #%llu][Seq %zu/%zu] MV=%.1f -> %s (x%.2f)"
                       : u8"[会心 #%llu][序列 %zu/%zu] 动作值=%.1f -> %s (x%.2f)",
                    static_cast<unsigned long long>(hitNo),
                    ratioStepOne, ratioPeriodSnap, mvVal, tag,
                    static_cast<double>(appliedMult));
            } else {
                host->ChatPrintfAsync(
                    en ? "[crit #%llu][Ratio %u:%u %zu/%zu] MV=%.1f -> %s (x%.2f)"
                       : u8"[会心 #%llu][定比 %u:%u 步%zu/%zu] 动作值=%.1f -> %s (x%.2f)",
                    static_cast<unsigned long long>(hitNo),
                    ratioMSnap, ratioNSnap, ratioStepOne, ratioPeriodSnap,
                    mvVal, tag, static_cast<double>(appliedMult));
            }
        } else {
            host->ChatPrintfAsync(
                en ? "[crit #%llu][%s] MV=%.1f Aff=%d%% -> %s (x%.2f)"
                   : u8"[会心 #%llu][%s] 动作值=%.1f 会心=%d%% -> %s (x%.2f)",
                static_cast<unsigned long long>(hitNo),
                ModeName(cfg.mode, en), mvVal, effAff,
                tag, static_cast<double>(appliedMult));
        }
    }
}

bool InstallCritDetour(std::uintptr_t exeBase) noexcept {
    if (g_detourActive) return true;
    const std::uintptr_t site = exeBase + kRvaApplyCrit;
    const auto* cur = reinterpret_cast<const std::uint8_t*>(site);
    const bool matchesOrig = (std::memcmp(cur, kPrologueApplyCrit, 5) == 0);
    const bool isRelJmp    = (cur[0] == 0xE9);
    if (!matchesOrig && !isRelJmp) {
        if (g_host) {
            g_host->Log(g_selfId, "[crit] Unexpected prologue at 0x%llX (%02X %02X %02X %02X %02X)",
                        static_cast<unsigned long long>(site), cur[0], cur[1], cur[2], cur[3], cur[4]);
        }
        return false;
    }

    const std::uintptr_t page = AllocNearPage(site, 0x1000U);
    if (!page || !InRel32(site + 5U, page)) {
        if (page) ::VirtualFree(reinterpret_cast<void*>(page), 0, MEM_RELEASE);
        return false;
    }
    std::memset(reinterpret_cast<void*>(page), 0xCC, 0x1000U);
    auto* out = reinterpret_cast<std::uint8_t*>(page);
    EmitAbsJmp14(out, reinterpret_cast<std::uintptr_t>(&Hook_ApplyCrit));

    const std::uintptr_t trampAddr = page + 16U;
    auto* tramp = out + 16U;
    if (isRelJmp && !matchesOrig) {
        std::int32_t prevRel = 0;
        std::memcpy(&prevRel, cur + 1U, 4);
        const auto prevTarget = static_cast<std::uintptr_t>(
            static_cast<std::int64_t>(site + 5U) + prevRel);
        EmitAbsJmp14(tramp, prevTarget);
    } else {
        std::memcpy(tramp, kPrologueApplyCrit, 5);
        EmitAbsJmp14(tramp + 5U, site + 5U);
    }

    DWORD oldProt = 0;
    if (!::VirtualProtect(reinterpret_cast<void*>(page), 0x1000U, PAGE_EXECUTE_READ, &oldProt)) {
        ::VirtualFree(reinterpret_cast<void*>(page), 0, MEM_RELEASE);
        return false;
    }
    ::FlushInstructionCache(::GetCurrentProcess(), reinterpret_cast<void*>(page), 0x1000U);

    std::memcpy(g_detourOrig5, cur, 5);
    g_detourJmp5[0] = 0xE9;
    const auto rel = static_cast<std::int32_t>(
        static_cast<std::int64_t>(page) - static_cast<std::int64_t>(site + 5U));
    std::memcpy(g_detourJmp5 + 1U, &rel, 4);

    _InterlockedExchangePointer(reinterpret_cast<void* volatile*>(&g_origApplyCrit),
                                reinterpret_cast<void*>(trampAddr));

    if (!CompareAndPatch5BytesSafe(site, g_detourOrig5, g_detourJmp5)) {
        _InterlockedExchangePointer(reinterpret_cast<void* volatile*>(&g_origApplyCrit), nullptr);
        ::VirtualFree(reinterpret_cast<void*>(page), 0, MEM_RELEASE);
        return false;
    }

    g_detourSite   = site;
    g_trampPage    = page;
    g_detourActive = true;
    return true;
}

void UninstallCritDetour() noexcept {
    if (!g_detourActive) return;
    g_shuttingDown.store(true, std::memory_order_release);

    const bool unpatched = CompareAndPatch5BytesSafe(g_detourSite, g_detourJmp5, g_detourOrig5);
    for (int i = 0; i < 500 && g_inFlightCrit.load(std::memory_order_acquire) > 0; ++i) {
        ::_mm_pause();
        if (i > 16) ::Sleep(1);
    }

    const bool drained = (g_inFlightCrit.load(std::memory_order_acquire) == 0);
    if (unpatched && drained) {
        _InterlockedExchangePointer(reinterpret_cast<void* volatile*>(&g_origApplyCrit), nullptr);
        if (g_trampPage) {
            ::VirtualFree(reinterpret_cast<void*>(g_trampPage), 0, MEM_RELEASE);
        }
    } else if (!unpatched && g_trampPage && g_origApplyCrit) {
        // Another plugin chained after us: redirect relay directly to original trampoline & leave relay alive
        DWORD oldProt = 0;
        if (::VirtualProtect(reinterpret_cast<void*>(g_trampPage), 64U, PAGE_READWRITE, &oldProt)) {
            EmitAbsJmp14(reinterpret_cast<std::uint8_t*>(g_trampPage),
                         reinterpret_cast<std::uintptr_t>(g_origApplyCrit));
            DWORD tmp = 0;
            ::VirtualProtect(reinterpret_cast<void*>(g_trampPage), 64U, oldProt, &tmp);
            ::FlushInstructionCache(::GetCurrentProcess(), reinterpret_cast<void*>(g_trampPage), 64U);
        }
    }
    g_trampPage    = 0;
    g_detourSite   = 0;
    g_detourActive = false;
}

// ============================================================================
//  MIRA Kernel Slot Hook & Lifecycle Listeners (`0x01F606D6`)
// ============================================================================
void __fastcall OnCritSeedPre(const MhwRngDrawContext* ctx,
                              MhwRngHookDecision* ioDecision,
                              void*) {
    if (ctx && ctx->DrawDeterministic) {
        g_drawDetFn.store(ctx->DrawDeterministic, std::memory_order_release);
    }
    if (!ioDecision) return;
    CritMode mode = CritMode::kVanilla;
    {
        std::lock_guard<std::mutex> lk(g_stateMx);
        mode = g_mode;
    }
    if (mode == CritMode::kVanilla || mode == CritMode::kObserve) {
        const bool isTakeover =
            g_host &&
            g_host->structSize >= offsetof(MhwRngHostApi, GetEngineMode) + sizeof(g_host->GetEngineMode) &&
            g_host->GetEngineMode &&
            g_host->GetEngineMode() == kMhwRngModeTakeover;
        ioDecision->action = isTakeover ? kMhwRngActionContinue : kMhwRngActionBypass;
        return;
    }
    ioDecision->action = kMhwRngActionClaimCondition;
    ioDecision->condId = kCondSeedSlot;
}

void __fastcall OnCritSeedPost(const MhwRngDrawContext* ctx,
                               MhwRngHookDecision*,
                               void*) {
    if (ctx && ctx->DrawDeterministic) {
        g_drawDetFn.store(ctx->DrawDeterministic, std::memory_order_release);
    }
}

void __fastcall OnKernelLifecycle(const MhwRngEventInfo* info, void*) {
    if (!info) return;
    if (info->eventKind == kMhwRngEventClearAllRules) {
        std::lock_guard<std::mutex> lk(g_stateMx);
        g_mode                = CritMode::kVanilla;
        g_rateOverrideEnabled = false;
        g_rateOverridePct     = 100;
        ResetRuntimeStreamsLocked();
        ResetTelemetryLocked();
    } else if (info->eventKind == kMhwRngEventEpochReset ||
               info->eventKind == kMhwRngEventMasterSeed ||
               info->eventKind == kMhwRngEventStateRestored) {
        std::lock_guard<std::mutex> lk(g_stateMx);
        ResetRuntimeStreamsLocked();
    }
}

void __fastcall OnWorldEvent(const MhwRngCustomEvent* ev, void*) {
    if (!ev || !ev->topic) return;
    std::lock_guard<std::mutex> lk(g_stateMx);
    if (!g_autoResetOnQuest) return;
    ResetRuntimeStreamsLocked();
    ResetTelemetryLocked();
}

bool __fastcall FormatCritSlotStatus(const MhwRngSlotSnapshot* snap,
                                     char* outBuf,
                                     std::size_t bufCap,
                                     void*) {
    if (!snap || !outBuf || bufCap == 0U) return false;
    CritMode      mode     = CritMode::kVanilla;
    bool          ovrOn    = false;
    int           ovrPct   = 0;
    std::uint64_t hits     = 0ULL;
    std::uint64_t pos      = 0ULL;
    std::uint64_t neg      = 0ULL;
    double        bank     = 0.0;
    {
        std::lock_guard<std::mutex> lk(g_stateMx);
        mode   = g_mode;
        ovrOn  = g_rateOverrideEnabled;
        ovrPct = g_rateOverridePct;
        hits   = g_totalHits;
        pos    = g_posCrits;
        neg    = g_negCrits;
        bank   = g_bankCredit;
    }
    const bool en = MhwRng_HostIsEnglish(g_host);
    const double pct = (hits > 0ULL) ? (100.0 * static_cast<double>(pos) / static_cast<double>(hits)) : 0.0;
    char rateBuf[32]{};
    if (ovrOn) std::snprintf(rateBuf, sizeof(rateBuf), "%d%%", ovrPct);
    else       std::snprintf(rateBuf, sizeof(rateBuf), "%s", en ? "auto" : u8"实时");

    if (mode == CritMode::kMvBank) {
        std::snprintf(outBuf, bufCap,
                      en ? "crit:%s rate:%s hits:%llu(+%llu/-%llu %.1f%%) bank:%.2f"
                         : u8"会心:%s 率:%s 命中:%llu(+%llu/-%llu %.1f%%) 额:%.2f",
                      ModeName(mode, en), rateBuf,
                      static_cast<unsigned long long>(hits),
                      static_cast<unsigned long long>(pos),
                      static_cast<unsigned long long>(neg),
                      pct, bank);
    } else {
        std::snprintf(outBuf, bufCap,
                      en ? "crit:%s rate:%s hits:%llu(+%llu/-%llu %.1f%%)"
                         : u8"会心:%s 率:%s 命中:%llu(+%llu/-%llu %.1f%%)",
                      ModeName(mode, en), rateBuf,
                      static_cast<unsigned long long>(hits),
                      static_cast<unsigned long long>(pos),
                      static_cast<unsigned long long>(neg),
                      pct);
    }
    return true;
}

// ============================================================================
//  Command Helpers & Status / Help Output
// ============================================================================
bool ParseIntStrict(const char* s, int& outVal) noexcept {
    if (!s || s[0] == '\0') return false;
    char* end = nullptr;
    const long v = std::strtol(s, &end, 10);
    if (!end || *end != '\0') return false;
    if (v < -100000L || v > 100000L) return false;
    outVal = static_cast<int>(v);
    return true;
}

bool ParseDoubleStrict(const char* s, double& outVal) noexcept {
    if (!s || s[0] == '\0') return false;
    char* end = nullptr;
    const double v = std::strtod(s, &end);
    if (!end || *end != '\0' || !std::isfinite(v)) return false;
    outVal = v;
    return true;
}

bool ParseRatioPair(const char* s, std::uint32_t& outM, std::uint32_t& outN) noexcept {
    if (!s || s[0] == '\0') return false;
    const char* sep = std::strchr(s, ':');
    if (!sep) sep = std::strchr(s, '/');
    if (!sep) sep = std::strchr(s, ',');
    if (!sep || sep == s || sep[1] == '\0') return false;
    char* end1 = nullptr;
    char* end2 = nullptr;
    const unsigned long m = std::strtoul(s, &end1, 10);
    const unsigned long n = std::strtoul(sep + 1, &end2, 10);
    if (end1 != sep || !end2 || *end2 != '\0') return false;
    if (m + n == 0UL || m > 10000UL || n > 10000UL) return false;
    outM = static_cast<std::uint32_t>(m);
    outN = static_cast<std::uint32_t>(n);
    return true;
}

bool ParseCustomSeqPattern(const char* s, std::vector<std::int8_t>& outSeq) {
    if (!s || s[0] == '\0') return false;
    outSeq.clear();
    for (const char* p = s; *p != '\0'; ++p) {
        const char ch = *p;
        if (ch == ',' || ch == ' ') continue;
        if (ch == '1' || ch == '+')      outSeq.push_back(1);
        else if (ch == '0' || ch == '.') outSeq.push_back(0);
        else if (ch == '-')              outSeq.push_back(-1);
        else                             return false;
        if (outSeq.size() >= 256U) break;
    }
    return !outSeq.empty();
}

bool ParseTierIntList(const char* csv, std::vector<int>& outVals) {
    outVals.clear();
    if (!csv || csv[0] == '\0') return false;
    const char* p = csv;
    while (*p != '\0') {
        const char* comma = std::strchr(p, ',');
        std::string tok = comma ? std::string(p, comma) : std::string(p);
        int v = 0;
        if (!ParseIntStrict(tok.c_str(), v)) return false;
        outVals.push_back(v);
        if (!comma) break;
        p = comma + 1;
        if (*p == '\0') return false; // trailing comma
    }
    return !outVals.empty();
}

bool StartsWithNoCase(const std::string& s, const char* prefix) noexcept {
    const std::size_t n = std::strlen(prefix);
    return s.size() >= n && s.compare(0U, n, prefix) == 0;
}

std::string FormatTierSummary(std::size_t cutCount,
                              const std::array<double, kMaxTierCuts>& cuts,
                              TierAffKind kind,
                              const std::array<int, kMaxTiers>& vals,
                              bool en) {
    std::string out;
    const std::size_t nTiers = cutCount + 1U;
    char seg[96]{};
    for (std::size_t i = 0U; i < nTiers; ++i) {
        if (i > 0U) out += " | ";
        char rangeBuf[36]{};
        if (i == 0U) {
            std::snprintf(rangeBuf, sizeof(rangeBuf), "<%.1f", cuts[0]);
        } else if (i == cutCount) {
            std::snprintf(rangeBuf, sizeof(rangeBuf), ">=%.1f", cuts[cutCount - 1U]);
        } else {
            std::snprintf(rangeBuf, sizeof(rangeBuf), "%.1f~%.1f", cuts[i - 1U], cuts[i]);
        }
        char rateBuf[24]{};
        if (kind == TierAffKind::kFixed) {
            std::snprintf(rateBuf, sizeof(rateBuf), "=%d%%", vals[i]);
        } else {
            std::snprintf(rateBuf, sizeof(rateBuf), "%+d%%", vals[i]);
        }
        std::snprintf(seg, sizeof(seg),
                      en ? "%s(%s,C%u)" : u8"%s(%s,槽%u)",
                      rangeBuf, rateBuf,
                      static_cast<unsigned>(kCondTierBase + i));
        out += seg;
    }
    return out;
}

void EnsureActiveKernelMode() noexcept {
    if (!g_host) return;
    const std::uint32_t m = g_host->GetEngineMode();
    if (m == kMhwRngModeOff) {
        g_host->SetTakeoverEnabled(true); // Promotes Off -> Selective cleanly
    } else if (m == kMhwRngModeObserveOnly) {
        const bool en = MhwRng_HostIsEnglish(g_host);
        g_host->ChatPrint(en ? "[crit] Note: kernel is in ObserveOnly ($rng observe); switch to $rng selective or $rng on to apply overrides."
                             : u8"[crit] 提示: 当前微内核处于仅观测模式 ($rng observe)，请执行 $rng selective 或 $rng on 以使会心接管生效。");
    }
}

void PrintActiveRateOverrideReminder(bool en) noexcept {
    if (!g_host) return;
    bool ovrOn = false;
    int  ovrPct = 0;
    {
        std::lock_guard<std::mutex> lk(g_stateMx);
        ovrOn  = g_rateOverrideEnabled;
        ovrPct = g_rateOverridePct;
    }
    if (!ovrOn) return;
    g_host->ChatPrintf(
        en ? "[crit] Note: forced affinity override (%d%%) is still active; run `$rng crit rate auto` to follow live panel+WEX."
           : u8"[会心] 提示: 当前仍生效强制会心率覆写 (%d%%)，输入 `$rng crit rate auto` 可恢复跟随实时面板+弱特。",
        ovrPct);
}

void PrintCritStatus() {
    if (!g_host) return;
    CritMode      mode     = CritMode::kVanilla;
    bool          ovrOn    = false;
    int           ovrPct   = 0;
    bool          verbose  = false;
    std::uint32_t ratM     = 1U;
    std::uint32_t ratN     = 1U;
    RatioStyle    ratStyle = RatioStyle::kBlock;
    std::size_t   seqLen   = 0U;
    double                          mvTh     = 50.0;
    double                          bankRes  = 1.0;
    double                          bankCur  = 0.0;
    std::size_t                     tCutsN   = 2U;
    std::array<double, kMaxTierCuts> tCuts{};
    TierAffKind                     tKind    = TierAffKind::kDelta;
    std::array<int, kMaxTiers>      tVals{};
    std::size_t                     bagSz    = 10U;
    std::uint64_t                   hits     = 0ULL;
    std::uint64_t                   pos      = 0ULL;
    std::uint64_t                   neg      = 0ULL;
    double                          mvSum    = 0.0;
    double                          mvCrit   = 0.0;
    bool                            autoReset = true;
    bool                            hasLast  = false;
    float                           lMv      = 0.0f;
    int                             lLive    = 0;
    int                             lEff     = 0;
    std::int8_t                     lOut     = 0;
    float                           lMult    = 1.0f;
    {
        std::lock_guard<std::mutex> lk(g_stateMx);
        mode      = g_mode;
        ovrOn     = g_rateOverrideEnabled;
        ovrPct    = g_rateOverridePct;
        verbose   = g_verbose;
        autoReset = g_autoResetOnQuest;
        ratM     = g_ratioM;
        ratN     = g_ratioN;
        ratStyle = g_ratioStyle;
        seqLen   = g_customSeq.size();
        mvTh     = g_mvThreshold;
        bankRes  = g_bankReserve;
        bankCur  = g_bankCredit;
        tCutsN   = g_tierCutCount;
        tCuts    = g_tierCuts;
        tKind    = g_tierAffKind;
        tVals    = g_tierAffVals;
        bagSz    = g_bagSize;
        hits     = g_totalHits;
        pos      = g_posCrits;
        neg      = g_negCrits;
        mvSum    = g_mvSum;
        mvCrit   = g_mvCritSum;
        hasLast  = g_lastHitValid;
        lMv      = g_lastMv;
        lLive    = g_lastLiveAff;
        lEff     = g_lastEffAff;
        lOut     = g_lastOutcome;
        lMult    = g_lastMult;
    }

    const bool en        = MhwRng_HostIsEnglish(g_host);
    const double critPct = (hits > 0ULL) ? (100.0 * static_cast<double>(pos) / static_cast<double>(hits)) : 0.0;
    const double mvPct   = (mvSum > 0.0) ? (100.0 * mvCrit / mvSum) : 0.0;
    char rateStr[32]{};
    if (ovrOn) std::snprintf(rateStr, sizeof(rateStr), "%d%%", ovrPct);
    else       std::snprintf(rateStr, sizeof(rateStr), "%s", en ? "auto (live panel+WEX)" : u8"auto (实时面板+弱特)");

    g_host->ChatPrintf(en ? "[crit] Mode:%s | Rate:%s | Verbose:%s | AutoReset:%s | Hook:%s"
                          : u8"[会心] 模式:%s | 会心率:%s | 详细播报:%s | 自动重置:%s | 钩子:%s",
                       ModeName(mode, en),
                       rateStr,
                       verbose ? "on" : "off",
                       autoReset ? "on" : "off",
                       g_detourActive ? "active" : "inactive");
    char worldBuf[128]{};
    if (MhwWorld_TryFormatSummary(g_host, worldBuf, sizeof(worldBuf), en)) {
        g_host->ChatPrintf(en ? "[crit] World context: %s" : u8"[会心] 世界上下文: %s", worldBuf);
    }

    if (mode == CritMode::kRatio) {
        if (ratStyle == RatioStyle::kCustom) {
            g_host->ChatPrintf(en ? "[crit] Sequence length: %zu steps (custom loop)"
                                  : u8"[会心] 序列长度: %zu 跳 (自定义循环)",
                               seqLen);
        } else {
            g_host->ChatPrintf(en ? "[crit] Ratio: %u:%u (%s)"
                                  : u8"[会心] 比例: %u:%u (%s)",
                               ratM, ratN,
                               (ratStyle == RatioStyle::kSpread) ? (en ? "spread" : u8"交错")
                                                                 : (en ? "block"  : u8"块状"));
        }
    } else if (mode == CritMode::kMvBank) {
        g_host->ChatPrintf(en ? "[crit] MV Bank: highMV>=%.1f | reserve=%.2f (low-MV overflow>=%.2f) | current=%.2f"
                              : u8"[会心] 预算池: 高动作值>=%.1f | 大招预留=%.2f (小招溢出线>=%.2f) | 当前额度=%.2f",
                           mvTh, bankRes, 1.0 + bankRes, bankCur);
    } else if (mode == CritMode::kMvTier) {
        const std::string summary = FormatTierSummary(tCutsN, tCuts, tKind, tVals, en);
        g_host->ChatPrintf(en ? "[crit] MV Tier (%zu streams): %s"
                              : u8"[会心] 分档流 (%zu 档): %s",
                           tCutsN + 1U, summary.c_str());
    } else if (mode == CritMode::kBag) {
        g_host->ChatPrintf(en ? "[crit] Bag size: %zu (w/ fractional carry & per-rate LRU cache)"
                              : u8"[会心] 洗牌袋大小: %zu (带余数进位守恒)", bagSz);
    }

    g_host->ChatPrintf(en ? "[crit] Stats: hits=%llu | +crit=%llu | -crit=%llu | hitCrit%%=%.1f%% | mvWeightedCrit%%=%.1f%%"
                          : u8"[会心] 统计: 总命中=%llu | 正会心=%llu | 负会心=%llu | 刀数会心率=%.1f%% | MV加权会心率=%.1f%%",
                       static_cast<unsigned long long>(hits),
                       static_cast<unsigned long long>(pos),
                       static_cast<unsigned long long>(neg),
                       critPct, mvPct);

    if (hasLast) {
        const char* tag = (lOut > 0) ? (en ? "CRIT+" : u8"正会心")
                        : (lOut < 0) ? (en ? "CRIT-" : u8"负会心")
                                     : (en ? "NORM"  : u8"普通");
        g_host->ChatPrintf(en ? "[crit] Last hit: MV=%.1f | live=%d%% | eff=%d%% -> %s (x%.2f)"
                              : u8"[会心] 上一跳: 动作值=%.1f | 游戏实时=%d%% | 生效=%d%% -> %s (x%.2f)",
                           static_cast<double>(lMv), lLive, lEff, tag, static_cast<double>(lMult));
    }
}

void PrintCritHelp() {
    if (!g_host) return;
    const bool en = MhwRng_HostIsEnglish(g_host);
    g_host->ChatPrint(en ? "[crit] Commands ($rng crit <subcmd>):" : u8"[会心] 指令列表 ($rng crit <子命令>):");
    g_host->ChatPrint(en ? "  off | vanilla                - Restore pure vanilla crit logic"
                         : u8"  off | vanilla                - 恢复纯原版暴击逻辑");
    g_host->ChatPrint(en ? "  observe                      - Keep vanilla crits + track hit MV & crit%"
                         : u8"  observe                      - 原版结果仅观测并统计动作值/会心率");
    g_host->ChatPrint(en ? "  rate <auto|-100..100>        - Follow live panel+WEX (`auto`) or force fixed%"
                         : u8"  rate <auto|-100..100>        - 跟随实时面板+弱特 (`auto`) 或无视面板强制设定会心率");
    g_host->ChatPrint(en ? "  random                       - Independent per-hit RNG via MIRA CondID 1 (no pity)"
                         : u8"  random                       - 纯随机无保底 (破除原版32跳位移相关性)");
    g_host->ChatPrint(en ? "  ratio <m:n> [block|spread]   - Exact m crits / n non-crits on real hits"
                         : u8"  ratio <m:n> [block|spread]   - 严格按真命中计 m次会心/n次不会心 (块状/均匀交错)");
    g_host->ChatPrint(en ? "  seq <10+-...>                - Custom looping crit pattern (e.g. 11010, ++-0)"
                         : u8"  seq <10+-...>                - 自定义循环暴击序列 (如 11010 或 ++-0)");
    g_host->ChatPrint(en ? "  mv_bank [mvTh=50] [res=1.0]  - High-MV priority budget bank (long-run rate conserved)"
                         : u8"  mv_bank [阈值=50] [预留=1.0] - 高动作值优先预算池 (小招攒暴击, 大招优先必暴)");
    g_host->ChatPrint(en ? "  mv_tier [c1 c2 ..] [delta=|rate=] - Split MV into independent CondID streams (10..17)"
                         : u8"  mv_tier [分界1 分界2..] [delta=|rate=] - 按动作值分档路由独立流 (槽10..17, 默认0%偏移)");
    g_host->ChatPrint(en ? "  bag [size=10] | prd          - Shuffle bag (w/ carry) or progressive PRD pity"
                         : u8"  bag [容量=10] | prd          - 确定性洗牌袋 (带小数进位) 或 PRD 渐进保底");
    g_host->ChatPrint(en ? "  verbose [on|off] | reset     - Toggle per-hit chat log | reset stats & stream state"
                         : u8"  verbose [on|off] | reset     - 开关每跳播报 | 重置统计与内部游标/预算池");
    g_host->ChatPrint(en ? "  autoreset [on|off]           - Auto reset stats/streams on quest enter or title return"
                         : u8"  autoreset [on|off]           - 进出任务/回标题时自动重置统计与流状态");
}

// Handles `random`, `ratio`, `seq`, `mv_bank`, `mv_tier`, `bag`, `prd`, `observe`, `vanilla`/`off`
bool HandleModeSubcommand(const std::string& mName, int remArgc, const char* const* remArgv) {
    const bool en = MhwRng_HostIsEnglish(g_host);

    if (mName == "off" || mName == "vanilla") {
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            g_mode = CritMode::kVanilla;
            ResetRuntimeStreamsLocked();
        }
        g_host->ChatPrint(en ? "[crit] Switched to vanilla crit mode."
                             : u8"[会心] 已切回原版会心逻辑。");
        return true;
    }

    if (mName == "observe" || mName == "obs") {
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            g_mode = CritMode::kObserve;
        }
        g_host->ChatPrint(en ? "[crit] Switched to Observe mode (vanilla roll + MV/crit telemetry)."
                             : u8"[会心] 已切换为观测模式 (原版判定 + 实时动作值/会心率统计)。");
        return true;
    }

    if (mName == "random" || mName == "pure") {
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            g_mode = CritMode::kRandom;
            ResetRuntimeStreamsLocked();
        }
        EnsureActiveKernelMode();
        g_host->ChatPrint(en ? "[crit] Mode: Pure Random (independent per-hit CondID 1, zero pity)."
                             : u8"[会心] 已启用纯随机无保底模式 (每跳独立内核 CondID 1 采样)。");
        PrintActiveRateOverrideReminder(en);
        return true;
    }

    if (mName == "ratio") {
        if (remArgc < 1 || !remArgv || !remArgv[0]) {
            g_host->ChatPrint(en ? "[crit] Usage: $rng crit ratio <m:n> [block|spread]"
                                 : u8"[会心] 用法: $rng crit ratio <m:n> [block|spread]");
            return true;
        }
        std::uint32_t m = 0U, n = 0U;
        if (!ParseRatioPair(remArgv[0], m, n)) {
            g_host->ChatPrintf(en ? "[crit] Invalid m:n ratio: '%s'" : u8"[会心] 无效比例格式: '%s'", remArgv[0]);
            return true;
        }
        RatioStyle st = RatioStyle::kBlock;
        if (remArgc >= 2 && remArgv[1]) {
            const std::string s = LowerAscii(remArgv[1]);
            if (s == "spread" || s == "even" || s == "bresenham") st = RatioStyle::kSpread;
            else if (s == "block" || s == "seq")                 st = RatioStyle::kBlock;
            else {
                g_host->ChatPrintf(en ? "[crit] Unknown ratio style '%s' (use block|spread)."
                                      : u8"[会心] 未知排布方式 '%s' (请用 block|spread)。", remArgv[1]);
                return true;
            }
        }
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            g_mode       = CritMode::kRatio;
            g_ratioM     = m;
            g_ratioN     = n;
            g_ratioStyle = st;
            ResetRuntimeStreamsLocked();
        }
        EnsureActiveKernelMode();
        g_host->ChatPrintf(en ? "[crit] Mode: Exact Ratio %u:%u (%s, counted on actual hits only)."
                              : u8"[会心] 已启用定比模式 %u:%u (%s，仅真实命中计次，翻滚空挥不消耗)。",
                           m, n,
                           (st == RatioStyle::kSpread) ? (en ? "spread" : u8"均匀交错")
                                                       : (en ? "block"  : u8"连续块状"));
        return true;
    }

    if (mName == "seq") {
        if (remArgc < 1 || !remArgv || !remArgv[0]) {
            g_host->ChatPrint(en ? "[crit] Usage: $rng crit seq <10+-...> (e.g. 11010, ++-0)"
                                 : u8"[会心] 用法: $rng crit seq <10+-...> (例: 11010 或 ++-0)");
            return true;
        }
        std::vector<std::int8_t> pat;
        if (!ParseCustomSeqPattern(remArgv[0], pat)) {
            g_host->ChatPrintf(en ? "[crit] Invalid sequence pattern '%s' (use 1/+, 0/., -)."
                                  : u8"[会心] 无效序列 '%s' (仅支持 1/+, 0/., -)。", remArgv[0]);
            return true;
        }
        const std::size_t seqLen = pat.size();
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            g_mode       = CritMode::kRatio;
            g_ratioStyle = RatioStyle::kCustom;
            g_customSeq  = std::move(pat);
            ResetRuntimeStreamsLocked();
        }
        EnsureActiveKernelMode();
        g_host->ChatPrintf(en ? "[crit] Mode: Custom Crit Sequence (%zu-step loop: '%s')."
                              : u8"[会心] 已启用自定义暴击序列 (%zu 步循环: '%s')。",
                           seqLen, remArgv[0]);
        return true;
    }

    if (mName == "mv_bank" || mName == "bank" || mName == "mv") {
        double mvTh = 50.0;
        double res  = 1.0;
        if (remArgc >= 1 && remArgv[0] && !ParseDoubleStrict(remArgv[0], mvTh)) {
            g_host->ChatPrintf(en ? "[crit] Invalid MV threshold '%s'." : u8"[会心] 无效动作值阈值 '%s'。", remArgv[0]);
            return true;
        }
        if (remArgc >= 2 && remArgv[1] && !ParseDoubleStrict(remArgv[1], res)) {
            g_host->ChatPrintf(en ? "[crit] Invalid reserve value '%s'." : u8"[会心] 无效预留额度 '%s'。", remArgv[1]);
            return true;
        }
        mvTh = (std::max)(1.0, (std::min)(500.0, mvTh));
        res  = (std::max)(0.0, (std::min)(10.0, res));
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            g_mode        = CritMode::kMvBank;
            g_mvThreshold = mvTh;
            g_bankReserve = res;
            ResetRuntimeStreamsLocked();
        }
        EnsureActiveKernelMode();
        g_host->ChatPrintf(en ? "[crit] Mode: High-MV Credit Bank (highMV >= %.1f, reserve = %.2f, low-MV overflow >= %.2f)."
                              : u8"[会心] 已启用动作值预算池 (高动作值 >= %.1f 优先必暴，大招预留 = %.2f，小招溢出线 = %.2f)。",
                           mvTh, res, 1.0 + res);
        PrintActiveRateOverrideReminder(en);
        return true;
    }

    if (mName == "mv_tier" || mName == "tier") {
        std::vector<double> cuts;
        bool hasDelta = false;
        bool hasRate  = false;
        std::vector<int> affVals;

        for (int i = 0; i < remArgc; ++i) {
            if (!remArgv || !remArgv[i]) continue;
            const std::string low = LowerAscii(remArgv[i]);
            if (StartsWithNoCase(low, "delta=")) {
                if (hasDelta || hasRate) {
                    g_host->ChatPrint(en ? "[crit] Only one of `delta=...` or `rate=...` may be specified."
                                         : u8"[会心] `delta=...` 与 `rate=...` 不可混用或重复指定。");
                    return true;
                }
                if (!ParseTierIntList(remArgv[i] + 6, affVals)) {
                    g_host->ChatPrintf(en ? "[crit] Invalid delta list '%s' (expected comma-separated integers in -100..100)."
                                          : u8"[会心] 无效偏移列表 '%s' (请传逗号分隔整数，范围 -100..100)。",
                                       remArgv[i]);
                    return true;
                }
                hasDelta = true;
            } else if (StartsWithNoCase(low, "rate=")) {
                if (hasDelta || hasRate) {
                    g_host->ChatPrint(en ? "[crit] Only one of `delta=...` or `rate=...` may be specified."
                                         : u8"[会心] `delta=...` 与 `rate=...` 不可混用或重复指定。");
                    return true;
                }
                if (!ParseTierIntList(remArgv[i] + 5, affVals)) {
                    g_host->ChatPrintf(en ? "[crit] Invalid rate list '%s' (expected comma-separated integers in -100..100)."
                                          : u8"[会心] 无效会心率列表 '%s' (请传逗号分隔整数，范围 -100..100)。",
                                       remArgv[i]);
                    return true;
                }
                hasRate = true;
            } else {
                double cut = 0.0;
                if (!ParseDoubleStrict(remArgv[i], cut) || cut <= 0.0 || cut > 10000.0) {
                    g_host->ChatPrintf(en ? "[crit] Invalid MV cutoff '%s' (use positive numbers + optional delta=/rate=)."
                                          : u8"[会心] 无效动作值分界 '%s' (裸数字须为正动作值分界，会心设置请用 delta= 或 rate=)。",
                                       remArgv[i]);
                    return true;
                }
                if (!cuts.empty() && cut <= cuts.back()) {
                    g_host->ChatPrintf(en ? "[crit] MV cutoffs must be strictly ascending (%.1f <= %.1f)."
                                          : u8"[会心] 动作值分界必须严格递增 (%.1f <= %.1f)。",
                                       cut, cuts.back());
                    return true;
                }
                if (cuts.size() >= kMaxTierCuts) {
                    g_host->ChatPrintf(en ? "[crit] Too many MV cutoffs (max %zu cutoffs / %zu tiers)."
                                          : u8"[会心] 动作值分界点过多 (最多 %zu 个分界 / %zu 档)。",
                                       kMaxTierCuts, kMaxTiers);
                    return true;
                }
                cuts.push_back(cut);
            }
        }

        if (cuts.empty()) {
            cuts.push_back(25.0);
            cuts.push_back(60.0);
        }
        const std::size_t nTiers = cuts.size() + 1U;
        const TierAffKind kind   = hasRate ? TierAffKind::kFixed : TierAffKind::kDelta;

        if (hasDelta || hasRate) {
            if (affVals.size() != nTiers) {
                g_host->ChatPrintf(
                    en ? "[crit] Tier value count mismatch: %zu MV cutoffs define %zu tiers, got %zu values."
                       : u8"[会心] 档位数量不匹配: %zu 个分界对应 %zu 档，但传入了 %zu 个数值。",
                    cuts.size(), nTiers, affVals.size());
                return true;
            }
            for (std::size_t idx = 0U; idx < affVals.size(); ++idx) {
                if (affVals[idx] < -100 || affVals[idx] > 100) {
                    g_host->ChatPrintf(
                        en ? "[crit] Tier #%zu value %d%% out of range [-100..100]."
                           : u8"[会心] 第 %zu 档数值 %d%% 超出允许范围 [-100..100]。",
                        idx + 1U, affVals[idx]);
                    return true;
                }
            }
        } else {
            affVals.assign(nTiers, 0);
        }

        std::array<double, kMaxTierCuts> cutArr{};
        std::array<int, kMaxTiers>       valArr{};
        for (std::size_t i = 0U; i < cuts.size(); ++i) cutArr[i] = cuts[i];
        for (std::size_t i = 0U; i < nTiers; ++i)      valArr[i] = affVals[i];

        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            g_mode         = CritMode::kMvTier;
            g_tierCutCount = cuts.size();
            g_tierCuts     = cutArr;
            g_tierAffKind  = kind;
            g_tierAffVals  = valArr;
            ResetRuntimeStreamsLocked();
        }
        EnsureActiveKernelMode();
        const std::string summary = FormatTierSummary(cuts.size(), cutArr, kind, valArr, en);
        g_host->ChatPrintf(en ? "[crit] Mode: MV Tier (%zu streams): %s"
                              : u8"[会心] 已启用动作值分档独立流 (%zu 档): %s",
                           nTiers, summary.c_str());
        if (kind == TierAffKind::kDelta) {
            PrintActiveRateOverrideReminder(en);
        }
        return true;
    }

    if (mName == "bag") {
        int sz = 10;
        if (remArgc >= 1 && remArgv[0] && !ParseIntStrict(remArgv[0], sz)) {
            g_host->ChatPrintf(en ? "[crit] Invalid bag size '%s'." : u8"[会心] 无效洗牌袋容量 '%s'。", remArgv[0]);
            return true;
        }
        sz = (std::max)(2, (std::min)(64, sz));
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            g_mode    = CritMode::kBag;
            g_bagSize = static_cast<std::size_t>(sz);
            ResetRuntimeStreamsLocked();
        }
        EnsureActiveKernelMode();
        g_host->ChatPrintf(en ? "[crit] Mode: Deterministic Shuffle Bag (size=%d, fractional carry)."
                              : u8"[会心] 已启用确定性洗牌袋模式 (袋容=%d，带小数进位守恒)。", sz);
        PrintActiveRateOverrideReminder(en);
        return true;
    }

    if (mName == "prd") {
        EnsurePrdTable();
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            g_mode = CritMode::kPrd;
            ResetRuntimeStreamsLocked();
        }
        EnsureActiveKernelMode();
        g_host->ChatPrint(en ? "[crit] Mode: Progressive Pseudo-Random Distribution (PRD, bounded miss streak)."
                             : u8"[会心] 已启用 PRD 渐进保底模式 (限制最大连黑次数并保持真实会心率)。");
        PrintActiveRateOverrideReminder(en);
        return true;
    }

    return false;
}

// ============================================================================
//  Chat Command Handler & Multi-Level Tab Completer (`$rng crit ...`)
// ============================================================================
void __fastcall Cmd_Crit(int argc, const char* const* argv, const char*, void*) {
    if (!g_host) return;
    if (argc <= 0) {
        PrintCritStatus();
        return;
    }
    const bool en         = MhwRng_HostIsEnglish(g_host);
    const std::string sub = LowerAscii(argv[0]);

    if (sub == "status" || sub == "st") {
        PrintCritStatus();
        return;
    }
    if (sub == "help" || sub == "?") {
        PrintCritHelp();
        return;
    }
    if (sub == "rate") {
        if (argc < 2 || !argv[1]) {
            g_host->ChatPrint(en ? "[crit] Usage: $rng crit rate <auto|-100..100>"
                                 : u8"[会心] 用法: $rng crit rate <auto|-100..100>");
            return;
        }
        const std::string arg = LowerAscii(argv[1]);
        if (arg == "auto" || arg == "panel" || arg == "game") {
            std::lock_guard<std::mutex> lk(g_stateMx);
            g_rateOverrideEnabled = false;
            g_host->ChatPrint(en ? "[crit] Affinity source: auto (live game panel + Weakness Exploit)."
                                 : u8"[会心] 会心率来源已设为: auto (实时游戏面板+弱点特效)。");
            return;
        }
        int pct = 0;
        if (!ParseIntStrict(argv[1], pct) || pct < -100 || pct > 100) {
            g_host->ChatPrintf(en ? "[crit] Invalid rate '%s' (expected auto or -100..100)."
                                  : u8"[会心] 无效会心率 '%s' (请输入 auto 或 -100..100)。", argv[1]);
            return;
        }
        bool switchedFromVanilla = false;
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            g_rateOverrideEnabled = true;
            g_rateOverridePct     = pct;
            if (g_mode == CritMode::kVanilla || g_mode == CritMode::kObserve) {
                g_mode = CritMode::kRandom;
                ResetRuntimeStreamsLocked();
                switchedFromVanilla = true;
            }
        }
        EnsureActiveKernelMode();
        if (switchedFromVanilla) {
            g_host->ChatPrintf(en ? "[crit] Forced affinity set to %d%% (auto-enabled Pure Random mode)."
                                  : u8"[会心] 已强制覆写会心率为 %d%% (并自动启用纯随机模式)。", pct);
        } else {
            g_host->ChatPrintf(en ? "[crit] Forced affinity set to %d%%."
                                  : u8"[会心] 已强制覆写目标会心率为 %d%%。", pct);
        }
        return;
    }

    if (sub == "verbose" || sub == "v") {
        bool nextVal = true;
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            if (argc >= 2 && argv[1]) {
                const std::string v = LowerAscii(argv[1]);
                if (v == "on" || v == "1" || v == "true")       nextVal = true;
                else if (v == "off" || v == "0" || v == "false") nextVal = false;
                else {
                    g_host->ChatPrint(en ? "[crit] Usage: $rng crit verbose [on|off]"
                                         : u8"[会心] 用法: $rng crit verbose [on|off]");
                    return;
                }
            } else {
                nextVal = !g_verbose;
            }
            g_verbose = nextVal;
        }
        g_host->ChatPrintf(en ? "[crit] Per-hit verbose chat logging: %s."
                              : u8"[会心] 每跳会心详细播报: %s。",
                           nextVal ? "on" : "off");
        return;
    }

    if (sub == "autoreset" || sub == "ar") {
        bool nextVal = true;
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            if (argc >= 2 && argv[1]) {
                const std::string v = LowerAscii(argv[1]);
                if (v == "on" || v == "1" || v == "true")       nextVal = true;
                else if (v == "off" || v == "0" || v == "false") nextVal = false;
                else {
                    g_host->ChatPrint(en ? "[crit] Usage: $rng crit autoreset [on|off]"
                                         : u8"[会心] 用法: $rng crit autoreset [on|off]");
                    return;
                }
            } else {
                nextVal = !g_autoResetOnQuest;
            }
            g_autoResetOnQuest = nextVal;
        }
        g_host->ChatPrintf(en ? "[crit] Auto reset stats/streams on quest enter or title return: %s."
                              : u8"[会心] 进出任务/回标题自动重置统计与流状态: %s。",
                           nextVal ? "on" : "off");
        return;
    }

    if (sub == "reset") {
        {
            std::lock_guard<std::mutex> lk(g_stateMx);
            ResetRuntimeStreamsLocked();
            ResetTelemetryLocked();
        }
        g_host->ChatPrint(en ? "[crit] Reset hit telemetry, budget bank, bag/PRD state & local cursors."
                             : u8"[会心] 已重置命中统计、动作值预算池与洗牌袋/PRD 状态。");
        return;
    }

    if (sub == "mode") {
        if (argc < 2 || !argv[1]) {
            PrintCritStatus();
            return;
        }
        const std::string mName = LowerAscii(argv[1]);
        if (HandleModeSubcommand(mName, argc - 2, (argc > 2) ? (argv + 2) : nullptr)) {
            return;
        }
        g_host->ChatPrintf(en ? "[crit] Unknown crit mode '%s'. Run `$rng crit help`."
                              : u8"[会心] 未知会心模式 '%s'，请运行 `$rng crit help`。", argv[1]);
        return;
    }

    if (HandleModeSubcommand(sub, argc - 1, (argc > 1) ? (argv + 1) : nullptr)) {
        return;
    }

    g_host->ChatPrintf(en ? "[crit] Unknown subcommand '%s'. Run `$rng crit help`."
                          : u8"[会心] 未知子命令 '%s'，请运行 `$rng crit help`。", argv[0]);
}

void AddModeParamCandidates(const std::string& mName,
                            int paramIdx,
                            MhwRngCompletionSinkFn addCand,
                            void* sinkCtx) {
    if (paramIdx == 0) {
        if (mName == "ratio") {
            static const char* const kRatios[] = { "1:1", "2:1", "3:1", "3:2", "1:2" };
            for (const char* r : kRatios) addCand(r, sinkCtx);
        } else if (mName == "seq") {
            static const char* const kSeqs[] = { "10", "110", "11010", "++-0" };
            for (const char* s : kSeqs) addCand(s, sinkCtx);
        } else if (mName == "mv_bank" || mName == "bank" || mName == "mv") {
            static const char* const kMvTh[] = { "30", "50", "80", "100" };
            for (const char* t : kMvTh) addCand(t, sinkCtx);
        } else if (mName == "mv_tier" || mName == "tier") {
            static const char* const kTierLo[] = { "25", "50", "delta=", "rate=" };
            for (const char* l : kTierLo) addCand(l, sinkCtx);
        } else if (mName == "bag") {
            static const char* const kBagSz[] = { "5", "10", "20" };
            for (const char* b : kBagSz) addCand(b, sinkCtx);
        }
    } else if (paramIdx == 1) {
        if (mName == "ratio") {
            addCand("block", sinkCtx);
            addCand("spread", sinkCtx);
        } else if (mName == "mv_bank" || mName == "bank" || mName == "mv") {
            addCand("0.5", sinkCtx);
            addCand("1.0", sinkCtx);
            addCand("2.0", sinkCtx);
        } else if (mName == "mv_tier" || mName == "tier") {
            static const char* const kTierNext[] = { "60", "100", "125", "200", "delta=", "rate=" };
            for (const char* t : kTierNext) addCand(t, sinkCtx);
        }
    } else if (paramIdx >= 2 && (mName == "mv_tier" || mName == "tier")) {
        static const char* const kTierMore[] = { "125", "200", "delta=", "rate=" };
        for (const char* t : kTierMore) addCand(t, sinkCtx);
    }
}

void __fastcall Complete_Crit(const char*,
                              int argc,
                              const char* const* argv,
                              const char*,
                              MhwRngCompletionSinkFn addCand,
                              void* sinkCtx,
                              void*) {
    if (!addCand) return;
    if (argc == 0) {
        static const char* const kTop[] = {
            "status", "help", "off", "vanilla", "observe", "rate", "mode",
            "random", "ratio", "seq", "mv_bank", "mv_tier", "bag", "prd",
            "verbose", "autoreset", "reset"
        };
        for (const char* t : kTop) addCand(t, sinkCtx);
        return;
    }
    if (!argv || !argv[0]) return;
    const std::string a0 = LowerAscii(argv[0]);

    if (argc == 1) {
        if (a0 == "rate") {
            static const char* const kRates[] = { "auto", "0", "25", "50", "75", "100", "-30", "-100" };
            for (const char* r : kRates) addCand(r, sinkCtx);
        } else if (a0 == "verbose" || a0 == "v" || a0 == "autoreset" || a0 == "ar") {
            addCand("on", sinkCtx);
            addCand("off", sinkCtx);
        } else if (a0 == "mode") {
            static const char* const kModes[] = {
                "vanilla", "observe", "random", "ratio", "seq", "mv_bank", "mv_tier", "bag", "prd"
            };
            for (const char* m : kModes) addCand(m, sinkCtx);
        } else {
            AddModeParamCandidates(a0, 0, addCand, sinkCtx);
        }
        return;
    }

    if (a0 == "mode" && argv[1]) {
        const std::string mName = LowerAscii(argv[1]);
        AddModeParamCandidates(mName, argc - 2, addCand, sinkCtx);
    } else {
        AddModeParamCandidates(a0, argc - 1, addCand, sinkCtx);
    }
}

// ============================================================================
//  MIRA v3.5 Companion Service (`"mhw.crit"`, v1)
// ============================================================================

void CopyTruncCrit(char* dst, std::size_t cap, const char* src) noexcept {
    if (!dst || cap == 0U) return;
    if (!src) {
        dst[0] = '\0';
        return;
    }
    std::size_t i = 0U;
    while (i + 1U < cap && src[i] != '\0') {
        dst[i] = src[i];
        ++i;
    }
    dst[i] = '\0';
}

bool WriteBufExactCrit(char* dst, std::size_t cap, const std::string& val) noexcept {
    if (!dst) return true;
    if (cap == 0U) return false;
    CopyTruncCrit(dst, cap, val.c_str());
    return (val.size() + 1U <= cap);
}

std::string FormatCleanDoubleCrit(double v) {
    char buf[48]{};
    std::snprintf(buf, sizeof(buf), "%.6g", v);
    return std::string(buf);
}

std::vector<std::string> SplitWhitespaceCrit(const char* text) {
    std::vector<std::string> toks;
    if (!text) return toks;
    const char* p = text;
    while (*p != '\0') {
        while (*p != '\0' && std::isspace(static_cast<unsigned char>(*p))) ++p;
        if (*p == '\0') break;
        const char* start = p;
        while (*p != '\0' && !std::isspace(static_cast<unsigned char>(*p))) ++p;
        toks.emplace_back(start, static_cast<std::size_t>(p - start));
    }
    return toks;
}

std::uint64_t __fastcall Svc_CritGetTotalHits() {
    std::lock_guard<std::mutex> lk(g_stateMx);
    return g_totalHits;
}

bool __fastcall Svc_CritGetConfigSnapshot(char*       outModeCmd,
                                          std::size_t modeCap,
                                          char*       outRateStr,
                                          std::size_t rateCap) {
    CritMode                         mode     = CritMode::kVanilla;
    bool                             ovrOn    = false;
    int                              ovrPct   = 100;
    std::uint32_t                    ratM     = 1U;
    std::uint32_t                    ratN     = 1U;
    RatioStyle                       ratStyle = RatioStyle::kBlock;
    std::vector<std::int8_t>         seq;
    double                           mvTh     = 50.0;
    double                           bankRes  = 1.0;
    std::size_t                      tCutCnt  = 2U;
    std::array<double, kMaxTierCuts> tCuts{};
    TierAffKind                      tKind    = TierAffKind::kDelta;
    std::array<int, kMaxTiers>       tVals{};
    std::size_t                      bagSz    = 10U;
    {
        std::lock_guard<std::mutex> lk(g_stateMx);
        mode     = g_mode;
        ovrOn    = g_rateOverrideEnabled;
        ovrPct   = g_rateOverridePct;
        ratM     = g_ratioM;
        ratN     = g_ratioN;
        ratStyle = g_ratioStyle;
        seq      = g_customSeq;
        mvTh     = g_mvThreshold;
        bankRes  = g_bankReserve;
        tCutCnt  = g_tierCutCount;
        tCuts    = g_tierCuts;
        tKind    = g_tierAffKind;
        tVals    = g_tierAffVals;
        bagSz    = g_bagSize;
    }

    std::string modeStr;
    switch (mode) {
        case CritMode::kVanilla:
            modeStr = "vanilla";
            break;
        case CritMode::kObserve:
            modeStr = "observe";
            break;
        case CritMode::kRandom:
            modeStr = "random";
            break;
        case CritMode::kRatio:
            if (ratStyle == RatioStyle::kCustom && !seq.empty()) {
                modeStr = "seq ";
                modeStr.reserve(4U + seq.size());
                for (std::int8_t v : seq) {
                    modeStr.push_back(v > 0 ? '1' : (v < 0 ? '-' : '0'));
                }
            } else {
                modeStr = "ratio " + std::to_string(ratM) + ":" + std::to_string(ratN) +
                          (ratStyle == RatioStyle::kSpread ? " spread" : " block");
            }
            break;
        case CritMode::kMvBank:
            modeStr = "mv_bank " + FormatCleanDoubleCrit(mvTh) + " " + FormatCleanDoubleCrit(bankRes);
            break;
        case CritMode::kMvTier: {
            modeStr = "mv_tier";
            for (std::size_t i = 0U; i < tCutCnt && i < kMaxTierCuts; ++i) {
                modeStr.push_back(' ');
                modeStr += FormatCleanDoubleCrit(tCuts[i]);
            }
            modeStr += (tKind == TierAffKind::kFixed) ? " rate=" : " delta=";
            const std::size_t nTiers = (std::min)(tCutCnt + 1U, kMaxTiers);
            for (std::size_t i = 0U; i < nTiers; ++i) {
                if (i > 0U) modeStr.push_back(',');
                modeStr += std::to_string(tVals[i]);
            }
            break;
        }
        case CritMode::kBag:
            modeStr = "bag " + std::to_string(bagSz);
            break;
        case CritMode::kPrd:
            modeStr = "prd";
            break;
    }

    const std::string rateStr = ovrOn ? std::to_string(ovrPct) : std::string("auto");

    bool ok = true;
    ok &= WriteBufExactCrit(outModeCmd, modeCap, modeStr);
    ok &= WriteBufExactCrit(outRateStr, rateCap, rateStr);
    return ok;
}

bool __fastcall Svc_CritApplyConfig(const char* modeCmd,
                                    const char* rateStr,
                                    char*       outErr,
                                    std::size_t errCap) {
    if (outErr && errCap > 0U) outErr[0] = '\0';

    // 1. Parse rateStr unlocked (`auto` or integer in `-100..100`)
    bool ovrOn  = false;
    int  ovrPct = 100;
    {
        const auto rateToks = SplitWhitespaceCrit(rateStr);
        if (rateToks.size() > 1U) {
            CopyTruncCrit(outErr, errCap, "invalid rate string (expected `auto` or single integer in -100..100)");
            return false;
        }
        if (rateToks.size() == 1U) {
            const std::string low = LowerAscii(rateToks[0].c_str());
            if (low == "auto" || low == "panel" || low == "game") {
                ovrOn = false;
            } else {
                int pct = 0;
                if (!ParseIntStrict(rateToks[0].c_str(), pct) || pct < -100 || pct > 100) {
                    const std::string msg = "invalid rate `" + rateToks[0] + "` (expected auto or -100..100)";
                    CopyTruncCrit(outErr, errCap, msg.c_str());
                    return false;
                }
                ovrOn  = true;
                ovrPct = pct;
            }
        }
    }

    // 2. Parse modeCmd unlocked (all 8 modes + `off` alias, optional leading `mode`)
    auto toks = SplitWhitespaceCrit(modeCmd);
    if (toks.size() >= 2U && LowerAscii(toks[0].c_str()) == "mode") {
        toks.erase(toks.begin());
    }

    CritMode                         nextMode     = CritMode::kVanilla;
    std::uint32_t                    nextRatM     = 1U;
    std::uint32_t                    nextRatN     = 1U;
    RatioStyle                       nextRatStyle = RatioStyle::kBlock;
    std::vector<std::int8_t>         nextSeq;
    double                           nextMvTh     = 50.0;
    double                           nextBankRes  = 1.0;
    std::size_t                      nextTierCnt  = 2U;
    std::array<double, kMaxTierCuts> nextTierCuts = { 25.0, 60.0, 0.0, 0.0, 0.0, 0.0, 0.0 };
    TierAffKind                      nextTierKind = TierAffKind::kDelta;
    std::array<int, kMaxTiers>       nextTierVals = { 0, 0, 0, 0, 0, 0, 0, 0 };
    std::size_t                      nextBagSz    = 10U;

    if (!toks.empty()) {
        const std::string mName = LowerAscii(toks[0].c_str());
        if (mName == "off" || mName == "vanilla") {
            if (toks.size() > 1U) {
                CopyTruncCrit(outErr, errCap, "unexpected extra args for vanilla mode");
                return false;
            }
            nextMode = CritMode::kVanilla;
        } else if (mName == "observe" || mName == "obs") {
            if (toks.size() > 1U) {
                CopyTruncCrit(outErr, errCap, "unexpected extra args for observe mode");
                return false;
            }
            nextMode = CritMode::kObserve;
        } else if (mName == "random" || mName == "pure") {
            if (toks.size() > 1U) {
                CopyTruncCrit(outErr, errCap, "unexpected extra args for random mode");
                return false;
            }
            nextMode = CritMode::kRandom;
        } else if (mName == "ratio") {
            if (toks.size() < 2U || toks.size() > 3U) {
                CopyTruncCrit(outErr, errCap, "expected `ratio <m:n> [block|spread]`");
                return false;
            }
            if (!ParseRatioPair(toks[1].c_str(), nextRatM, nextRatN)) {
                const std::string msg = "invalid ratio `" + toks[1] + "`";
                CopyTruncCrit(outErr, errCap, msg.c_str());
                return false;
            }
            nextRatStyle = RatioStyle::kBlock;
            if (toks.size() == 3U) {
                const std::string st = LowerAscii(toks[2].c_str());
                if (st == "spread" || st == "even" || st == "bresenham") nextRatStyle = RatioStyle::kSpread;
                else if (st == "block" || st == "seq")                   nextRatStyle = RatioStyle::kBlock;
                else {
                    const std::string msg = "unknown ratio style `" + toks[2] + "` (expected block|spread)";
                    CopyTruncCrit(outErr, errCap, msg.c_str());
                    return false;
                }
            }
            nextMode = CritMode::kRatio;
        } else if (mName == "seq") {
            if (toks.size() != 2U) {
                CopyTruncCrit(outErr, errCap, "expected `seq <pattern>`");
                return false;
            }
            if (!ParseCustomSeqPattern(toks[1].c_str(), nextSeq)) {
                const std::string msg = "invalid seq pattern `" + toks[1] + "`";
                CopyTruncCrit(outErr, errCap, msg.c_str());
                return false;
            }
            nextMode     = CritMode::kRatio;
            nextRatStyle = RatioStyle::kCustom;
        } else if (mName == "mv_bank" || mName == "bank" || mName == "mv") {
            if (toks.size() > 3U) {
                CopyTruncCrit(outErr, errCap, "expected `mv_bank [mvTh] [reserve]`");
                return false;
            }
            double mvTh = 50.0;
            double res  = 1.0;
            if (toks.size() >= 2U && !ParseDoubleStrict(toks[1].c_str(), mvTh)) {
                const std::string msg = "invalid mv_bank threshold `" + toks[1] + "`";
                CopyTruncCrit(outErr, errCap, msg.c_str());
                return false;
            }
            if (toks.size() >= 3U && !ParseDoubleStrict(toks[2].c_str(), res)) {
                const std::string msg = "invalid mv_bank reserve `" + toks[2] + "`";
                CopyTruncCrit(outErr, errCap, msg.c_str());
                return false;
            }
            nextMode    = CritMode::kMvBank;
            nextMvTh    = (std::max)(1.0, (std::min)(500.0, mvTh));
            nextBankRes = (std::max)(0.0, (std::min)(10.0, res));
        } else if (mName == "mv_tier" || mName == "tier") {
            std::vector<double> cuts;
            std::vector<int>    affVals;
            bool hasDelta = false;
            bool hasRate  = false;
            for (std::size_t i = 1U; i < toks.size(); ++i) {
                const std::string low = LowerAscii(toks[i].c_str());
                if (StartsWithNoCase(low, "delta=")) {
                    if (hasDelta || hasRate) {
                        CopyTruncCrit(outErr, errCap, "duplicate or conflicting delta=/rate= in mv_tier");
                        return false;
                    }
                    if (!ParseTierIntList(toks[i].c_str() + 6, affVals)) {
                        const std::string msg = "invalid mv_tier delta list `" + toks[i] + "`";
                        CopyTruncCrit(outErr, errCap, msg.c_str());
                        return false;
                    }
                    hasDelta = true;
                } else if (StartsWithNoCase(low, "rate=")) {
                    if (hasDelta || hasRate) {
                        CopyTruncCrit(outErr, errCap, "duplicate or conflicting delta=/rate= in mv_tier");
                        return false;
                    }
                    if (!ParseTierIntList(toks[i].c_str() + 5, affVals)) {
                        const std::string msg = "invalid mv_tier rate list `" + toks[i] + "`";
                        CopyTruncCrit(outErr, errCap, msg.c_str());
                        return false;
                    }
                    hasRate = true;
                } else {
                    double cut = 0.0;
                    if (!ParseDoubleStrict(toks[i].c_str(), cut) || cut <= 0.0 || cut > 10000.0) {
                        const std::string msg = "invalid mv_tier cutoff `" + toks[i] + "`";
                        CopyTruncCrit(outErr, errCap, msg.c_str());
                        return false;
                    }
                    if (!cuts.empty() && cut <= cuts.back()) {
                        CopyTruncCrit(outErr, errCap, "mv_tier cutoffs must be strictly ascending");
                        return false;
                    }
                    if (cuts.size() >= kMaxTierCuts) {
                        CopyTruncCrit(outErr, errCap, "too many mv_tier cutoffs (max 7)");
                        return false;
                    }
                    cuts.push_back(cut);
                }
            }
            if (cuts.empty()) {
                cuts.push_back(25.0);
                cuts.push_back(60.0);
            }
            const std::size_t nTiers = cuts.size() + 1U;
            if (hasDelta || hasRate) {
                if (affVals.size() != nTiers) {
                    CopyTruncCrit(outErr, errCap, "mv_tier value count mismatch");
                    return false;
                }
                for (int v : affVals) {
                    if (v < -100 || v > 100) {
                        CopyTruncCrit(outErr, errCap, "mv_tier value out of range [-100..100]");
                        return false;
                    }
                }
            } else {
                affVals.assign(nTiers, 0);
            }
            nextMode     = CritMode::kMvTier;
            nextTierCnt  = cuts.size();
            nextTierCuts.fill(0.0);
            nextTierVals.fill(0);
            for (std::size_t i = 0U; i < cuts.size(); ++i) nextTierCuts[i] = cuts[i];
            for (std::size_t i = 0U; i < nTiers; ++i)      nextTierVals[i] = affVals[i];
            nextTierKind = hasRate ? TierAffKind::kFixed : TierAffKind::kDelta;
        } else if (mName == "bag") {
            if (toks.size() > 2U) {
                CopyTruncCrit(outErr, errCap, "expected `bag [size]`");
                return false;
            }
            int sz = 10;
            if (toks.size() == 2U && !ParseIntStrict(toks[1].c_str(), sz)) {
                const std::string msg = "invalid bag size `" + toks[1] + "`";
                CopyTruncCrit(outErr, errCap, msg.c_str());
                return false;
            }
            nextMode  = CritMode::kBag;
            nextBagSz = static_cast<std::size_t>((std::max)(2, (std::min)(64, sz)));
        } else if (mName == "prd") {
            if (toks.size() > 1U) {
                CopyTruncCrit(outErr, errCap, "unexpected extra args for prd mode");
                return false;
            }
            EnsurePrdTable();
            nextMode = CritMode::kPrd;
        } else {
            const std::string msg = "unknown crit mode `" + toks[0] + "`";
            CopyTruncCrit(outErr, errCap, msg.c_str());
            return false;
        }
    }

    // 3. Atomic commit under leaf mutex (zero `g_host` calls!)
    {
        std::lock_guard<std::mutex> lk(g_stateMx);
        g_rateOverrideEnabled = ovrOn;
        g_rateOverridePct     = ovrOn ? ovrPct : 100;
        g_mode                = nextMode;
        if (nextMode == CritMode::kRatio) {
            g_ratioStyle = nextRatStyle;
            if (nextRatStyle == RatioStyle::kCustom) {
                g_customSeq = std::move(nextSeq);
            } else {
                g_ratioM = nextRatM;
                g_ratioN = nextRatN;
            }
        } else if (nextMode == CritMode::kMvBank) {
            g_mvThreshold = nextMvTh;
            g_bankReserve = nextBankRes;
        } else if (nextMode == CritMode::kMvTier) {
            g_tierCutCount = nextTierCnt;
            g_tierCuts     = nextTierCuts;
            g_tierAffKind  = nextTierKind;
            g_tierAffVals  = nextTierVals;
        } else if (nextMode == CritMode::kBag) {
            g_bagSize = nextBagSz;
        }
        ResetRuntimeStreamsLocked();
        ResetTelemetryLocked();
    }

    if (nextMode != CritMode::kVanilla && nextMode != CritMode::kObserve &&
        g_host && g_host->GetEngineMode() == kMhwRngModeOff) {
        g_host->SetTakeoverEnabled(true);
    }
    return true;
}

const MhwCritServiceApi kCritServiceApi = {
    sizeof(MhwCritServiceApi),
    kMhwCritApiVersion,
    &Svc_CritGetTotalHits,
    &Svc_CritGetConfigSnapshot,
    &Svc_CritApplyConfig
};

const MhwRngPluginDescriptor kPluginDesc = {
    kMhwRngApiVersion,
    "crit",
    u8"攻击会心控制插件",
    "1.1.0",
    u8"无视面板设定会心率，并支持纯随机/m:n序列/动作值预算池/分档流/洗牌袋/PRD保底"
};

} // namespace

// ============================================================================
//  Plugin Entry Points
// ============================================================================
MHW_RNG_PLUGIN_EXPORT const MhwRngPluginDescriptor* MhwRngPlugin_GetInfo() {
    return &kPluginDesc;
}

MHW_RNG_PLUGIN_EXPORT bool MhwRngPlugin_Init(const MhwRngHostApi* host, MhwRngPluginId selfId) {
    if (!host || host->apiVersion != kMhwRngApiVersion || !host->exeBase) return false;
    g_shuttingDown.store(false, std::memory_order_release);
    g_host   = host;
    g_selfId = selfId;
    EnsurePrdTable();

    MhwRng_RegisterPluginInfoBi(
        host, selfId,
        u8"攻击会心控制插件",
        "Attack Crit & Affinity Controller",
        u8"可设目标会心率与纯随机/m:n序列/高动作值优先预算池/分档流/洗牌袋/PRD保底",
        "Custom affinity override + pure RNG, exact m:n, high-MV bank/tier, shuffle bag & PRD modes");

    MhwRng_RegisterSiteMetaBi(
        host, selfId,
        kRvaCritSeed,
        "pl.crit_seed",
        u8"玩家动作起手会心种子抽取 (搭配命中钩子 0x1F51380 实现会心分配控制)",
        "Player action-start crit seed roll (paired with 0x1F51380 hit-time evaluator)",
        &FormatCritSlotStatus,
        nullptr);

    MhwRngHookDesc hk{};
    hk.structSize = sizeof(hk);
    hk.rva        = kRvaCritSeed;
    hk.priority   = 0;
    hk.flags      = kMhwRngHookPre | kMhwRngHookPost | kMhwRngHookObserveOnly;
    hk.preFn      = &OnCritSeedPre;
    hk.postFn     = &OnCritSeedPost;
    g_hookSeed    = host->RegisterSlotHookEx(selfId, &hk);
    g_hookLife    = host->RegisterLifecycleHook(selfId, &OnKernelLifecycle, nullptr);
    g_worldEvTitle = MhwRng_HostSubscribeEvent(host, selfId, kMhwWorldEvTitleReturn, &OnWorldEvent, nullptr);
    g_worldEvQuest = MhwRng_HostSubscribeEvent(host, selfId, kMhwWorldEvQuestEnter,  &OnWorldEvent, nullptr);

    MhwRng_RegisterSubcommandBi(
        host, selfId,
        "crit",
        "$rng crit [rate auto|-100..100|random|ratio m:n|seq pat|mv_bank|mv_tier|bag|prd|observe|off]",
        u8"控制玩家攻击会心率与分配模式 (m:n/纯随机/高动作值优先/洗牌袋/PRD)",
        "Control player affinity override & crit modes (random/ratio/mv_bank/mv_tier/bag/prd)",
        &Cmd_Crit,
        nullptr);
    MhwRng_RegisterSubcommandCompleter(host, selfId, "crit", &Complete_Crit, nullptr);

    if (!InstallCritDetour(host->exeBase)) {
        host->Log(selfId, "[crit] Failed to install crit evaluator detour at RVA 0x%07X", kRvaApplyCrit);
        return false;
    }
    MhwRng_HostRegisterService(host, selfId, kMhwCritServiceName, kMhwCritApiVersion, &kCritServiceApi);
    return true;
}

MHW_RNG_PLUGIN_EXPORT void MhwRngPlugin_Shutdown() {
    UninstallCritDetour();
    const MhwRngHostApi* hostCopy = nullptr;
    MhwRngPluginId       selfCopy = 0U;
    MhwRngHookHandle     ev1      = kMhwRngInvalidHandle;
    MhwRngHookHandle     ev2      = kMhwRngInvalidHandle;
    {
        std::lock_guard<std::mutex> lk(g_stateMx);
        hostCopy              = g_host;
        selfCopy              = g_selfId;
        ev1                   = g_worldEvTitle;
        ev2                   = g_worldEvQuest;
        g_worldEvTitle        = kMhwRngInvalidHandle;
        g_worldEvQuest        = kMhwRngInvalidHandle;
        g_mode                = CritMode::kVanilla;
        g_rateOverrideEnabled = false;
        g_rateOverridePct     = 100;
        g_verbose             = false;
        g_autoResetOnQuest    = true;
        g_customSeq.clear();
        ResetRuntimeStreamsLocked();
        ResetTelemetryLocked();
        g_host                = nullptr;
        g_selfId              = 0U;
    }
    MhwRng_HostUnregisterService(hostCopy, selfCopy, kMhwCritServiceName);
    MhwRng_HostUnsubscribeEvent(hostCopy, selfCopy, ev1);
    MhwRng_HostUnsubscribeEvent(hostCopy, selfCopy, ev2);
    g_drawDetFn.store(nullptr, std::memory_order_release);
    g_hookSeed = kMhwRngInvalidHandle;
    g_hookLife = kMhwRngInvalidHandle;
}
