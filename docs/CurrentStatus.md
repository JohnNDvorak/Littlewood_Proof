# Littlewood Proof: Current Status

**Date**: 2026-02-04 (audited, post-architecture change)

## Sorry Count Summary

### Main target: `lake build Littlewood.Main.Littlewood` — **11 warnings, 8 project**

| Location | Sorries | Notes |
|----------|---------|-------|
| CriticalAssumptions.lean | 5 | Critical path hypotheses |
| Bridge/ExplicitFormulaOscillation.lean | 1 | ψ oscillation extraction |
| Bridge/ThetaExplicitFormulaOscillation.lean | 1 | θ oscillation extraction |
| Aristotle/HardyApproxFunctionalEq.lean | 1 | Approximate functional equation (Hardy chain) |
| PrimeNumberTheoremAnd (dependency) | 3 | **NOT on critical path** (dead code in Wiener.lean) |
| **Total warnings** | **11** | **8 project + 3 external** |

### Full build: `lake build` — **17 warnings, 14 project**

| Location | Sorries | Notes |
|----------|---------|-------|
| CriticalAssumptions.lean | 5 | Critical path hypotheses |
| Bridge/ | 2 | ExplicitFormulaOscillation + ThetaExplicitFormulaOscillation |
| Aristotle/ | 7 | HardyApproxFunctionalEq(1) + PhragmenLindelof(3) + ZeroCounting(2) + PartialSummation(1) |
| PrimeNumberTheoremAnd (dependency) | 3 | NOT on critical path |
| **Total warnings** | **17** | **14 project + 3 external** |

### External Dependency: NOT on Critical Path

The 3 PrimeNumberTheoremAnd/Wiener.lean sorries are **dead code**:
- `prelim_decay_2` (line 320): Fourier decay bound — unused by exported API
- `prelim_decay_3` (line 339): Stronger Fourier decay — unused by exported API
- `auto_cheby` (line 3889): Chebyshev property inference — used only in unexported theorem

We import `WeakPNT''` and `chebyshev_asymptotic` from `PrimeNumberTheoremAnd.Consequences`,
which have complete proofs independent of these sorry-backed theorems.

### Infrastructure: `lake build Littlewood.Assumptions` — adds ~52 sorries

Assumptions.lean provides sorry-backed instances for non-critical hypothesis
classes (zero counting, weighted average, Landau lemma, etc.). These are NOT
imported by the main theorems and are scaffolding for future extensions.

## Architecture Change: θ Explicit Formula (2026-02-04)

**PsiToThetaOscillation.lean is DEPRECATED.** The old ψ→θ oscillation transfer
was mathematically problematic: |ψ(x) - θ(x)| ~ √x absorbs the Ω₊ signal
at the √x scale, making the transfer unsound.

**Replacement:** Direct explicit formula for θ.
- `ExplicitFormulas/ExplicitFormulaTheta.lean` — defines `chebyshevTheta0` (normalized θ)
  and `ExplicitFormulaThetaHyp` class: θ₀(x) = x - Σ_ρ x^ρ/ρ + O(√x)
- `Bridge/ThetaExplicitFormulaOscillation.lean` — wires HardyCriticalLineZerosHyp +
  ExplicitFormulaThetaHyp → ThetaOscillationSqrtHyp (1 sorry)
- `CriticalAssumptions.lean` — now has 5 sorry instances (added ExplicitFormulaThetaHyp)

**Net effect:** Sorry count 10→11 for main target, but each sorry encodes
well-understood mathematical content. The old bridge encoded a dubious step.

## Critical Path Sorries (8 project sorries for main target)

### For `littlewood_psi` (6 sorries):

| # | Sorry | Location | Mathematical Content | Wiring Status |
|---|-------|----------|---------------------|---------------|
| 1 | `ExplicitFormulaPsiHyp` | CriticalAssumptions | ψ₀(x) = x - Σ_ρ x^ρ/ρ + O(log x) | Direct in CriticalAssumptions |
| 2 | `ZetaCriticalLineBoundHyp` | CriticalAssumptions | \|ζ(1/2+it)\| ≤ C\|t\|^{1/4+ε} | PhragmenLindelofWiring.lean READY |
| 3 | `HardyFirstMomentUpperHyp` | CriticalAssumptions | \|∫₁ᵀ Z(t) dt\| ≤ C·T^{1/2+ε} | HardyFirstMomentWiring.lean PLACEHOLDER |
| 4 | `approx_functional_eq` | Aristotle | ∫Z² ≥ k·∫\|S\|² - C·T | FULLY AUTO via MeanSquareBridge |
| 5 | ExplicitFormulaOscillation | Bridge | ∞ zeros + explicit formula → ψ Ω±(√x) | Depends on #1 |

### For `littlewood_pi_li` (all ψ sorries above, plus 3):

| # | Sorry | Location | Mathematical Content | Wiring Status |
|---|-------|----------|---------------------|---------------|
| 6 | `ExplicitFormulaThetaHyp` | CriticalAssumptions | θ₀(x) = x - Σ_ρ x^ρ/ρ + O(√x) | Direct in CriticalAssumptions |
| 7 | ThetaExplicitFormulaOscillation | Bridge | ∞ zeros + explicit formula → θ Ω±(√x) | Depends on #6 |
| 8 | `OmegaThetaToPiLiHyp` | CriticalAssumptions | θ Ω±(f) → π-li Ω±(f/log) | Depends on PartialSummation |

## CRITICAL: Aristotle Prompt 3 Exponent Mismatch

**ZetaCriticalLineBoundHyp requires exponent 1/4 + ε:**
```lean
class ZetaCriticalLineBoundHyp : Prop where
  bound : ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∀ t : ℝ, |t| ≥ 2 →
    ‖riemannZeta (1/2 + I * t)‖ ≤ C * |t| ^ (1/4 + ε)
```

**Aristotle's `zeta_critical_line_bound` proves exponent 1/2 — INSUFFICIENT.**

**Correct target: `zeta_convexity_bound` at σ = 1/2** (gives 1/4+ε).
**Bridge/PhragmenLindelofWiring.lean** is pre-built and verified (0 wiring sorries).
**Dependency chain:** `gamma_growth` (Stirling) → `zeta_convexity_bound` → bridge → hypothesis.

## Complete Dependency Tree

```
littlewood_psi : ψ(x) - x = Ω±(√x)
  └── Schmidt.psi_oscillation_sqrt
      └── [PsiOscillationSqrtHyp]   ← auto-resolved
          └── PsiOscillationWiring.lean (0 sorry)
              └── [PsiOscillationFromCriticalZerosHyp]   ← auto-resolved
                  └── ExplicitFormulaOscillation.lean (1 SORRY)
                      ├── [HardyCriticalLineZerosHyp]   ← auto-resolved
                      │   └── HardyCriticalLineWiring.lean (0 sorry)
                      │       ├── [ZetaCriticalLineBoundHyp]     (SORRY in CriticalAssumptions)
                      │       ├── [HardyFirstMomentUpperHyp]     (SORRY in CriticalAssumptions)
                      │       └── HardyInfiniteZerosV2 (Aristotle, 0 sorry)
                      │           └── HardySetupV2Instance (0 sorry)
                      │               └── MeanSquareBridge (0 sorry)
                      │                   └── DiagonalIntegralBound (0 sorry)
                      │                       └── approx_functional_eq (1 SORRY in Aristotle)
                      └── [ExplicitFormulaPsiHyp]        (SORRY in CriticalAssumptions)

littlewood_pi_li : π(x) - li(x) = Ω±(√x / log x)
  └── PiLiOscillationSqrtHyp.oscillation
      └── [PiLiOscillationSqrtHyp]   ← auto-resolved
          └── PsiToPiLiOscillation.lean (0 sorry)
              ├── [ThetaOscillationSqrtHyp]    ← auto-resolved
              │   └── ThetaExplicitFormulaOscillation.lean (1 SORRY)
              │       ├── [HardyCriticalLineZerosHyp]  ← auto-resolved (full ψ chain above)
              │       └── [ExplicitFormulaThetaHyp]     (SORRY in CriticalAssumptions)
              └── [OmegaThetaToPiLiHyp]                 (SORRY in CriticalAssumptions)
```

## Bridge Chain (complete)

```
ExplicitFormulaOscillation.lean:
  [HardyCriticalLineZerosHyp] [ExplicitFormulaPsiHyp] → PsiOscillationFromCriticalZerosHyp (1 sorry)

PsiOscillationWiring.lean:
  [PsiOscillationFromCriticalZerosHyp] → PsiOscillationSqrtHyp (0 sorry)

ThetaExplicitFormulaOscillation.lean:
  [HardyCriticalLineZerosHyp] [ExplicitFormulaThetaHyp] → ThetaOscillationSqrtHyp (1 sorry)

PsiToPiLiOscillation.lean:
  [ThetaOscillationSqrtHyp] [OmegaThetaToPiLiHyp] → PiLiOscillationSqrtHyp (0 sorry)

HardyCriticalLineWiring.lean:
  [ZetaCriticalLineBoundHyp] [HardyFirstMomentUpperHyp] → HardyCriticalLineZerosHyp (0 sorry)

PhragmenLindelofWiring.lean (READY, not yet imported):
  zeta_convexity_bound at σ=1/2 → ZetaCriticalLineBoundHyp (0 wiring sorry)

PsiToThetaOscillation.lean: DEPRECATED (mathematically problematic)
```

## Hardy Chain Status (Structurally Complete)

```
DiagonalIntegralBound: ∫|S_N|² ≥ c·T·log T                (0 sorries)
  → HardyApproxFunctionalEq: ∫Z² ≥ k·∫|S|² - CT           (1 sorry)
  → MeanSquarePartialSumAsymptotic                          (0 sorries)
  → OscillatorySumBound                                     (0 sorries)
  → MeanSquareBridge: ∫Z² ≥ c'·T·log T                     (0 sorries)
  → HardySetupV2Instance: ALL 6 FIELDS PROVED               (0 sorries)
  → HardyInfiniteZerosV2: ALL 5 LEMMAS PROVED               (0 sorries)
  → HardyCriticalLineWiring → HardyCriticalLineZerosHyp     (0 sorries)
  → ExplicitFormulaOscillation → PsiOscillationFromCriticalZerosHyp (1 sorry)
  → PsiOscillationWiring → PsiOscillationSqrtHyp            (0 sorries)
  → littlewood_psi                                          (0 sorries)
```

## Wiring Readiness for Aristotle

| Aristotle Target | Hypothesis Discharged | Wiring Status | Bridge File |
|---|---|---|---|
| `approx_functional_eq` | mean_square_lower (implicit) | **FULLY AUTO** — 0 bridge sorries | MeanSquareBridge.lean |
| `zeta_convexity_bound` | ZetaCriticalLineBoundHyp | **READY** — 0 wiring sorries | PhragmenLindelofWiring.lean |
| HardyFirstMoment 4 prereqs | HardyFirstMomentUpperHyp | **PLACEHOLDER** — needs 4 prereqs | HardyFirstMomentWiring.lean |
| ExplicitFormulaPsi (Prompts 6-9) | ExplicitFormulaPsiHyp | **PLACEHOLDER** — Perron's formula chain | Aristotle/ExplicitFormula.lean |
| ExplicitFormulaTheta | ExplicitFormulaThetaHyp | **DIRECT** — same Perron argument as ψ | CriticalAssumptions.lean |
| `psi_oscillation_implies_pi_li_oscillation` | OmegaThetaToPiLiHyp | **BLOCKED** — li mismatch + amplitude | Not yet created |

## Aristotle Module: Active Sorries

| File | Sorries | Topic | Critical Path? |
|------|---------|-------|----------------|
| HardyApproxFunctionalEq.lean | 1 | Approximate functional equation | YES (Hardy chain) |
| PhragmenLindelof.lean | 3 | Convexity bounds, Gamma growth | YES (feeds ZetaCriticalLineBoundHyp) |
| ZeroCounting.lean | 2 | N(T) argument principle + asymptotic | No |
| PartialSummation.lean | 1 | π(x) - li(x) via partial summation | No (alternative route) |

## Aristotle Placeholder Files (Prompts 6-9: Explicit Formula Chain)

Target: close ExplicitFormulaPsiHyp via Perron's formula approach.

| Prompt | File | Content | Status |
|--------|------|---------|--------|
| 6 | Aristotle/ContourIntegration.lean | Vertical line integrals | PLACEHOLDER (definition only) |
| 7 | Aristotle/RectangleCauchy.lean | Cauchy residue theorem for rectangles | PLACEHOLDER (header only) |
| 8 | Aristotle/PerronFormula.lean | Perron's formula: ∫(-ζ'/ζ)x^s/s = ψ₀(x) | PLACEHOLDER (header only) |
| 9 | Aristotle/ExplicitFormula.lean | explicit_formula_for_psi (target theorem) | PLACEHOLDER (1 sorry) |

## HardyFirstMoment Wiring Assessment

**Bridge/HardyFirstMomentWiring.lean exists as PLACEHOLDER** (documentation only, no imports).

- `hardyZ_first_moment_bound_conditional` is PROVED (0 sorry) in HardyZFirstMoment.lean
- Needs 4 prerequisites: integrability of MainTerm/ErrorTerm + integral bounds
- `OscillatorySumBound.oscillatory_sum_integral_bound` is PROVED (0 sorry) — partial progress
- **Blockers**: `approx_functional_eq` must close first; definition mismatch between
  `HardyZFirstMoment.MainTerm` and `HardyApproxFunctionalEq.hardySum`; van der Corput
  bounds not available
- **Recommendation**: Activate wiring file after `approx_functional_eq` is closed

## li Definition Equivalence

**Project li** (Basic/LogarithmicIntegral.lean):
```lean
noncomputable def logarithmicIntegral (x : ℝ) : ℝ := ∫ t in Ioc 2 x, 1 / log t
```

**Aristotle li** (Aristotle/PartialSummation.lean):
```lean
noncomputable def li (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t
```

**These are EQUAL for x ≥ 2.** The `Ioc`-based set integral equals the interval integral
when the lower bound ≤ upper. LogarithmicIntegral.lean:273 proves this equivalence.

## Build Status

- `lake build Littlewood.Main.Littlewood`: 11 sorry warnings (8 project + 3 external)
- Full `lake build`: 17 sorry warnings (14 project + 3 external)
- `lake build Littlewood.Assumptions`: adds ~52 infrastructure sorries
- `lake build Littlewood.Tests.CriticalPathTest`: compiles, tracks critical path
- `lake build Littlewood.Bridge.PhragmenLindelofWiring`: compiles (standalone, not imported)
- All .lean files compile
- ~34,600 lines of Lean code across 186 files
- Both main theorems resolve with NO explicit typeclass parameters

## Scoreboard (sorry count for main target)

```
2026-02-03: 69 sorries (initial state, Assumptions.lean imported)
2026-02-03: 10 sorries (split to CriticalAssumptions, dropped Assumptions import)
2026-02-04: 11 sorries (architecture: ExplicitFormulaThetaHyp replaces PsiToThetaOscillation)
```
