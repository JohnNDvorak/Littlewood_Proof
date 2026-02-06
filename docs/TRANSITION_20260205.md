# Littlewood Formalization: Transition Document

**Date**: 2026-02-05
**Session End**: Tasks 48-58 completed
**Next Session**: Ready to continue with Aristotle integration or architectural improvements

---

## Project Location

```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
```

## Quick Verification

```bash
# Verify environment
lake exe cache get
lake build Littlewood.Main.Littlewood 2>&1 | grep -c sorry
# Expected: 11

# Full verification
./scripts/verify_build.sh
# Expected: All checks pass
```

---

## Current Build State

| Metric | Value |
|--------|-------|
| Total sorry warnings | 11 |
| Project sorries | 8 |
| External sorries (Wiener.lean) | 3 (dead code, not on critical path) |
| Lean version | 4.27.0-rc1 |
| Mathlib | f897ebcf72cd16f89ab4577d0c826cd14afaafc7 |

### Build-Visible Sorries (8 project)

```
# CriticalAssumptions.lean (5 hypothesis instances)
Line 70:  ExplicitFormulaPsiHyp      - Needs Perron's formula
Line 93:  ZetaCriticalLineBoundHyp   - Needs Phragmén-Lindelöf
Line 116: HardyFirstMomentUpperHyp   - Needs Hardy Z moment bounds
Line 141: OmegaThetaToPiLiHyp        - ARCHITECTURAL ISSUE (see below)
Line 163: ExplicitFormulaThetaHyp    - Needs Perron's formula

# Bridge sorries (2 oscillation extraction)
Bridge/ExplicitFormulaOscillation.lean:74       - PsiOscillationFromCriticalZerosHyp
Bridge/ThetaExplicitFormulaOscillation.lean:57  - ThetaOscillationSqrtHyp

# Aristotle (1 mathematical content)
Aristotle/HardyApproxFunctionalEq.lean:113      - approx_functional_eq
```

---

## What Was Accomplished This Session

### Sorries Closed (5 total)

| File | Before | After | Fix |
|------|:------:|:-----:|-----|
| GammaGrowthBoundsV2.lean | 4 | 0 | `exact gamma_half_growth`, `exact hC₁_sinh`, compact set min, `exact stirling_normalized_gamma_bounded_large_t` |
| ZetaIntegralRep.lean | 1 | 0 | `exact hs` (hypothesis was in scope) |

### Files Created

| File | Purpose |
|------|---------|
| `Bridge/GammaGrowthWiring.lean` | Wires GammaGrowthBoundsV2 for critical path (hasGammaGrowth_half, etc.) |
| `Tests/WiringSimulation.lean` | Validates all instance resolutions and theorem typechecking |
| `docs/project_snapshot_20260205.md` | Complete state snapshot |
| `docs/resumption_guide.md` | Quick reference for new sessions |

### Key Findings

1. **OmegaThetaToPiLiHyp Architectural Issue** (Task 57):
   - Current hypothesis requires `∀ f` but only `f = √x` is ever used
   - PsiDominance.lean lemmas require **unbounded oscillation** (`∀ K, ∃ x, |ψ-x| > K√x`)
   - But Ω± notation only gives **bounded limsup/liminf**
   - **Solution path**: Create weaker `OmegaThetaToPiLiSqrtHyp` for specific case

2. **PartialSummation.lean** (Task 51):
   - 2 sorries are genuine mathematical gaps, not budget exhaustion
   - `pi_sub_li_decomposition` is PROVED
   - Hypotheses too weak (need amplitude bounds, not just sign changes)

---

## Architecture Overview

### Main Theorems

```
littlewood_psi   : ψ(x) - x = Ω±(√x)        [Main/Littlewood.lean]
littlewood_pi_li : π(x) - li(x) = Ω±(√x/log x)  [Main/LittlewoodPi.lean]
```

### Critical Path

```
ExplicitFormulaPsiHyp + ZetaCriticalLineBoundHyp + HardyFirstMomentUpperHyp
    └─→ Hardy chain (Aristotle, 0 sorries except approx_functional_eq)
        └─→ HardyCriticalLineZerosHyp (auto-wired)
            └─→ PsiOscillationFromCriticalZerosHyp (1 bridge sorry)
                └─→ PsiOscillationSqrtHyp (0 sorries)
                    └─→ littlewood_psi ✓

ExplicitFormulaThetaHyp + HardyCriticalLineZerosHyp
    └─→ ThetaOscillationSqrtHyp (1 bridge sorry)

ThetaOscillationSqrtHyp + OmegaThetaToPiLiHyp
    └─→ PiLiOscillationSqrtHyp (0 sorries)
        └─→ littlewood_pi_li ✓
```

### Key File Locations

| Purpose | File |
|---------|------|
| Critical sorries | `Littlewood/CriticalAssumptions.lean` |
| All hypothesis instances | `Littlewood/Assumptions.lean` |
| Bridge wiring | `Littlewood/Bridge/*.lean` |
| Aristotle proofs | `Littlewood/Aristotle/*.lean` |
| Main ψ theorem | `Littlewood/Main/Littlewood.lean` |
| Main π theorem | `Littlewood/Main/LittlewoodPi.lean` |
| Verification tests | `Littlewood/Tests/WiringSimulation.lean` |

---

## Aristotle Files Status

### Fully Proved (0 sorries) - Key Files

| File | Content |
|------|---------|
| GammaGrowthBoundsV2.lean | Stirling bounds, HasGammaGrowth, step_up/down |
| ZetaLogDerivInfra.lean | -ζ'/ζ pole structure (10 theorems) |
| ZetaIntegralRep.lean | Zeta integral representation |
| ContourIntegrationV2.lean | Cauchy rectangle, residue |
| HardyZMeanSquare.lean | Hardy Z mean square lower bound |
| DiagonalIntegralBound.lean | ∫|S_N|² ≥ c·T·log T |

### With Sorries (not on main build path)

| File | Sorries | Notes |
|------|:-------:|-------|
| HardyApproxFunctionalEq.lean | 1 | `approx_functional_eq` - CRITICAL |
| PhragmenLindelof.lean | 3 | gamma_growth blocks the rest |
| ZeroCounting.lean | 2 | Argument principle application |
| PartialSummation.lean | 2 | Weak hypotheses |
| HardyApproxFunctionalEqV2.lean | 3 | Reference file |

---

## Priority for Next Work

### High Priority

1. **approx_functional_eq** (HardyApproxFunctionalEq.lean:113)
   - Closes Hardy chain → auto-discharges HardyCriticalLineZerosHyp
   - Needs: Riemann-Siegel formula with error bound O(t^{-1/4})
   - Aristotle has partial work in V2/V3/V4 files

2. **gamma_growth** (PhragmenLindelof.lean:170)
   - Enables ZetaCriticalLineBoundHyp
   - Needs: Fractional stepping for Gamma (currently only integer steps)
   - GammaGrowthBoundsV2 has base case at σ=1/2

### Medium Priority

3. **ExplicitFormulaPsiHyp/ThetaHyp**
   - Needs: Perron's formula with contour integration
   - Aristotle has PerronFormulaV3.lean (definitions only)
   - Blocked on Mathlib vertical line integrals

4. **OmegaThetaToPiLiHyp architectural fix**
   - Option A: Create OmegaThetaToPiLiSqrtHyp (specific case)
   - Option B: Use unbounded oscillation from explicit formula
   - See Task 57 analysis in project_snapshot_20260205.md

### Lower Priority

5. **Bridge sorries** (oscillation extraction)
   - Depend on ExplicitFormula hypotheses being closed
   - Mathematical content, not infrastructure

---

## Commands Reference

```bash
# Build main target
lake build Littlewood.Main.Littlewood

# Count sorries
lake build Littlewood.Main.Littlewood 2>&1 | grep -c sorry

# Build specific Aristotle file
lake build Littlewood.Aristotle.FileName

# Full verification
./scripts/verify_build.sh

# Search for definition/theorem
grep -r "theorem.*name\|def.*name" Littlewood/ --include="*.lean"

# Check what imports a file
grep -r "import.*FileName" Littlewood/ --include="*.lean"
```

---

## Documentation Files

| File | Purpose |
|------|---------|
| `docs/AristotleStatus.md` | Aristotle file tracking and prompt status |
| `docs/sorry_manifest.txt` | Machine-readable sorry list |
| `docs/project_snapshot_20260205.md` | State snapshot from this session |
| `docs/resumption_guide.md` | Quick reference for sessions |
| `docs/wiring_readiness.md` | Per-hypothesis integration instructions |

---

## Things NOT to Modify

- `PrimeNumberTheoremAnd/` - External dependency (3 dead-code sorries)
- `Littlewood/_deprecated/` - Old files, not imported
- Mathlib files

---

## Session Context for AI Assistant

When starting a new session, you can say:

> "I'm working on the Littlewood formalization at `/Users/john.n.dvorak/Documents/Git/Littlewood_Proof/`. Please read `docs/TRANSITION_20260205.md` for the current state. The project has 11 sorries (8 project + 3 external). Key priorities are closing `approx_functional_eq` and investigating the `OmegaThetaToPiLiHyp` architectural issue."

The assistant should then:
1. Read this transition document
2. Run `./scripts/verify_build.sh` to confirm state
3. Read `docs/AristotleStatus.md` for Aristotle file details
4. Proceed with requested work

---

## Git Status

```bash
# Check current state
git status
git log --oneline -5
```

Note: This project is NOT a git repo according to the environment, so changes are only on local filesystem.

---

**End of Transition Document**
