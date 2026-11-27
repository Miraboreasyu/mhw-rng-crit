#pragma once
// ============================================================================
//  MIRA Optional Critical Hit & Affinity Controller Service ABI (`rng_crit.dll`)
//  Service Name : "mhw.crit" (v1)
//
//  Strict Pure-POD C ABI (zero `<windows.h>` dependency).
//  Allows peer plugins (e.g. deterministic TAS recorders/replayers) to query
//  cumulative local-player hit counts, export canonical crit mode & affinity
//  rate configurations across all 8 modes, and apply them atomically & quietly.
// ============================================================================
#include "mhw_rng_api.h"

#include <cstddef>
#include <cstdint>

constexpr const char*   kMhwCritServiceName    = "mhw.crit";
constexpr std::uint32_t kMhwCritApiVersion     = 1U;
constexpr std::uint32_t kMhwCritServiceVersion = kMhwCritApiVersion;

#pragma pack(push, 8)
struct MhwCritServiceApi {
    std::uint32_t structSize; // sizeof(MhwCritServiceApi)
    std::uint32_t apiVersion; // == kMhwCritApiVersion (1)

    // Returns live cumulative local-player hit counter (`g_totalHits`).
    std::uint64_t (__fastcall *GetTotalHits)();

    // Exports canonical `modeCmd` for all 8 modes:
    //   - "vanilla"
    //   - "observe"
    //   - "random"
    //   - "ratio <m>:<n> <block|spread>"
    //   - "seq <pat>"
    //   - "mv_bank <mv> <res>"
    //   - "mv_tier <cut1> [cut2 ...] <delta|rate>=<v1,v2,...>"
    //   - "bag <N>"
    //   - "prd"
    // Exports canonical `rateStr`: "auto" or "<int>" (-100..100).
    // Passing `nullptr` for an output buffer skips it without failing.
    // Non-null buffers with `cap > 0` are always NUL-terminated; returns
    // `false` if any non-null buffer is too small.
    bool (__fastcall *GetConfigSnapshot)(
        char*       outModeCmd,
        std::size_t modeCap,
        char*       outRateStr,
        std::size_t rateCap);

    // Atomically validates and applies `rateStr` ("auto" or "-100..100") and
    // `modeCmd` (without `rateStr` overriding `modeCmd`), resets runtime
    // streams & telemetry, and runs quietly (zero chat output).
    // On parse error, live crit state is NOT modified and `outErr` is set.
    bool (__fastcall *ApplyConfig)(
        const char* modeCmd,
        const char* rateStr,
        char*       outErr,
        std::size_t errCap);
};
#pragma pack(pop)

// ---- Inline Service Convenience Helpers (Graceful No-Op when `rng_crit.dll` is unloaded) ----

inline bool MhwCrit_TryGetTotalHits(const MhwRngHostApi* host,
                                    std::uint64_t* outHits) noexcept {
    if (!host || !outHits) return false;
    MhwRngServiceGuard<MhwCritServiceApi> crit(host, kMhwCritServiceName, kMhwCritApiVersion);
    if (!crit || !crit->GetTotalHits) return false;
    *outHits = crit->GetTotalHits();
    return true;
}

inline bool MhwCrit_TryGetConfigSnapshot(const MhwRngHostApi* host,
                                         char*       outModeCmd,
                                         std::size_t modeCap,
                                         char*       outRateStr,
                                         std::size_t rateCap) noexcept {
    if (!host) return false;
    MhwRngServiceGuard<MhwCritServiceApi> crit(host, kMhwCritServiceName, kMhwCritApiVersion);
    if (!crit || !crit->GetConfigSnapshot) return false;
    return crit->GetConfigSnapshot(outModeCmd, modeCap, outRateStr, rateCap);
}

inline bool MhwCrit_TryApplyConfig(const MhwRngHostApi* host,
                                   const char* modeCmd,
                                   const char* rateStr,
                                   char*       outErr,
                                   std::size_t errCap) noexcept {
    if (!host) return false;
    MhwRngServiceGuard<MhwCritServiceApi> crit(host, kMhwCritServiceName, kMhwCritApiVersion);
    if (!crit || !crit->ApplyConfig) return false;
    return crit->ApplyConfig(modeCmd, rateStr, outErr, errCap);
}
