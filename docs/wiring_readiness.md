# Wiring Readiness Report

**Last updated**: 2026-02-04

## Overview

5 critical hypotheses in `CriticalAssumptions.lean` must be closed to complete
the proof of Littlewood's theorem. Each has a bridge file that auto-wires when
the underlying Aristotle proof is complete.

## Hypothesis 1: ExplicitFormulaPsiHyp

| Field | Value |
|-------|-------|
| Location | CriticalAssumptions.lean:70 |
| Aristotle target | Aristotle/ExplicitFormula.lean (Prompt 9) |
| Bridge | Bridge/ExplicitFormulaOscillation.lean |
| Bridge sorries | 1 (oscillation extraction) |
| Auto-wires? | Yes, once sorry closed |
| Verification | `lake build Littlewood.Bridge.ExplicitFormulaOscillation` |

**Activation steps:**
1. Close `explicit_formula_for_psi` sorry in Aristotle/ExplicitFormula.lean
2. Import in CriticalAssumptions.lean, remove sorry instance
3. Bridge auto-provides `PsiOscillationFromCriticalZerosHyp` (still has 1 own sorry)

**Blockers:** Requires Perron's formula (Prompts 6-8 chain). Mathlib lacks vertical line
integral infrastructure.

**Dependency chain:** Prompt 6 (contour) → Prompt 7 (rectangle Cauchy) → Prompt 8 (Perron) → Prompt 9 (explicit formula)

## Hypothesis 2: ZetaCriticalLineBoundHyp

| Field | Value |
|-------|-------|
| Location | CriticalAssumptions.lean:93 |
| Aristotle target | Aristotle/PhragmenLindelof.lean |
| Bridge | Bridge/PhragmenLindelofWiring.lean |
| Bridge sorries | 0 (READY) |
| Auto-wires? | Yes |
| Verification | `lake build Littlewood.Bridge.PhragmenLindelofWiring` |

**Activation steps:**
1. Close `gamma_growth` sorry in PhragmenLindelof.lean (unblocks rest)
2. Close `zeta_convexity_bound` sorry
3. Import PhragmenLindelofWiring in CriticalAssumptions.lean
4. Remove sorry instance — bridge auto-discharges

**Blockers:** `gamma_growth` (Stirling approximation for Gamma). GammaGrowthBounds.lean
has ingredients but needs ~200 lines assembly. `zeta_convexity_bound` blocked by gamma_growth.

**When gamma_growth closes:** zeta_critical_line_bound and zeta_convexity_bound should
follow quickly. PhragmenLindelofWiring is pre-built and ready.

## Hypothesis 3: HardyFirstMomentUpperHyp

| Field | Value |
|-------|-------|
| Location | CriticalAssumptions.lean:116 |
| Aristotle target | Aristotle/HardyZFirstMoment.lean (conditional) |
| Bridge | Bridge/HardyCriticalLineWiring.lean (via HardySetupV2Instance) |
| Bridge sorries | 0 |
| Auto-wires? | Yes (combined with ZetaCriticalLineBoundHyp) |
| Verification | `lake build Littlewood.Bridge.HardyCriticalLineWiring` |

**Activation steps:**
1. Close `approx_functional_eq` sorry (HardyApproxFunctionalEq.lean)
2. This feeds MeanSquareBridge → HardySetupV2Instance
3. Close HardyFirstMomentUpperHyp directly or via conditional theorem
4. Combined with ZetaCriticalLineBoundHyp, HardyCriticalLineWiring auto-fires

**Blockers:**
- `approx_functional_eq` (1 sorry) — needs error bound ‖R(t)‖ = O(t^(-1/4))
- HardyZFirstMoment conditional has 4 unproved prerequisites
- Van der Corput bounds needed for main term integral

**Note:** HardyCriticalLineWiring produces `HardyCriticalLineZerosHyp` which feeds
BOTH the ψ and θ oscillation bridges.

## Hypothesis 4: OmegaThetaToPiLiHyp

| Field | Value |
|-------|-------|
| Location | CriticalAssumptions.lean:141 |
| Aristotle target | Aristotle/PartialSummation.lean |
| Bridge | Bridge/PsiToPiLiOscillation.lean |
| Bridge sorries | TBD |
| Auto-wires? | Manual activation needed |
| Verification | `lake build Littlewood.Bridge.PsiToPiLiOscillation` |

**Activation steps:**
1. Close PartialSummation sorries (amplitude quantification)
2. Or: prove transfer directly with Vinogradov-Korobov bounds
3. Import and remove sorry instance

**Blockers:** Requires error bound quantification. PsiOscillationPiLi.lean (0 sorries)
proves a weaker version (sign changes, not Ω±) with stronger hypotheses.

**Alternative route:** If PartialSummation.lean closes with compatible definitions,
can bypass this hypothesis.

## Hypothesis 5: ExplicitFormulaThetaHyp

| Field | Value |
|-------|-------|
| Location | CriticalAssumptions.lean:163 |
| Aristotle target | Same as ExplicitFormulaPsiHyp (same zero sum) |
| Bridge | Bridge/ThetaExplicitFormulaOscillation.lean |
| Bridge sorries | 1 (oscillation extraction, same as ψ version) |
| Auto-wires? | Yes, once sorry closed |
| Verification | `lake build Littlewood.Bridge.ThetaExplicitFormulaOscillation` |

**Activation steps:**
1. Close ExplicitFormulaPsiHyp first (same Perron infrastructure)
2. Adapt ψ formula to θ (differs only in error term: O(√x) vs O(log x))
3. Uses PsiThetaBound.lean (|ψ-θ| ≤ 10√x, proved)

**Blockers:** Same as Hypothesis 1. Shares the Perron formula dependency chain.

## Priority for Next Aristotle Work

| Priority | Target | Impact | Effort |
|----------|--------|--------|--------|
| 1 | `approx_functional_eq` | Closes Hardy chain sorry | HIGH — error bound proof |
| 2 | `gamma_growth` | Unblocks ZetaCriticalLineBoundHyp | MEDIUM — Stirling assembly |
| 3 | Prompts 6-9 chain | Closes ExplicitFormulaPsiHyp + ThetaHyp | HIGH — sequential chain |
| 4 | OmegaThetaToPiLiHyp | Closes oscillation transfer | MEDIUM — error quantification |

## Quick Reference: When Aristotle Delivers

### If gamma_growth closes:
```
PhragmenLindelof.lean → 0 sorries (gamma_growth done)
  → zeta_convexity_bound follows
  → Import PhragmenLindelofWiring in CriticalAssumptions
  → ZetaCriticalLineBoundHyp auto-closes
  → Combined with HardyFirstMomentUpperHyp → HardyCriticalLineZerosHyp
```

### If approx_functional_eq closes:
```
HardyApproxFunctionalEq.lean → 0 sorries
  → MeanSquareBridge auto-fires
  → HardySetupV2Instance mean_square_lower field closes
  → Still needs: first moment upper bound
```

### If explicit_formula_for_psi closes:
```
ExplicitFormula.lean → 0 sorries
  → Uncomment instance in ExplicitFormula.lean
  → Import in CriticalAssumptions
  → ExplicitFormulaPsiHyp closes
  → ExplicitFormulaOscillation bridge auto-fires (still 1 own sorry)
```
