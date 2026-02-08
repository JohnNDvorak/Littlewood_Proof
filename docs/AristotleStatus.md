# Aristotle Module: Status Tracker

**Date**: 2026-02-08 (Overnight + follow-up wiring: counts refreshed, transfer/plumbing infrastructure added)

## Overview

The Aristotle module contains AI-generated proofs (from Harmonic's Aristotle and
Anthropic's Claude) that work toward closing the sorry-backed hypothesis instances.
Files are organized in `Littlewood/Aristotle/`.

- **Total files**: 129
- **Files imported from `Littlewood.lean`**: 103
- **Orphan files**: 26
- **Files with active sorries (build-visible)**: 2
- **Sorry-free files**: 126 (97.7%)
- **Total build-visible Aristotle sorries**: 3
- **Budget-exhaustion sorry track record**: 22/22 CLOSED (all resolved)
- **Total project sorries (build)**: 7 (1 critical + 3 bridge + 3 Aristotle)
- **External sorries**: 3 (PrimeNumberTheoremAnd/Wiener.lean, not on critical path)

## Recent Achievements (Session 14)

| Achievement | Details |
|------------|---------|
| **`ThetaToPiLiTransferInfra.lean` added** | Added exact θ→(π-li) decomposition identity in project notation: `π-li = (θ-x)/log x + remainder` |
| **Hardy first-moment plumbing tightened** | Added/imported `Bridge/HardyFirstMomentWiring.lean` and documented the two remaining hypotheses (`MainTermFirstMomentBoundHyp`, `ErrorTermFirstMomentBoundHyp`) |
| **No-axiom integrity check** | Active Lean files (excluding `.bak`) contain no `axiom` declarations; only backups had old axiom stubs |
| **Build baseline preserved** | `lake build` still reports 10 sorry warnings (7 project + 3 external) |

## Recent Achievements (Session 13)

| Achievement | Details |
|------------|---------|
| **Stale import comments fixed in `Littlewood.lean`** | Updated stale Aristotle sorry-count comments (e.g. PhragmenLindelof/PartialSummation now marked 0 sorries where appropriate) |
| **`RemainderTermAnalysis.lean` fixed and wired** | Replaced all 4 `exact?` placeholders with concrete lemmas; module compiles and is now imported |
| **9 additional orphan Aristotle files wired** | Added imports for VanDerCorputInfra, DirichletPhaseAlignment, ZeroCountingRectangle, ContourIntegrationV2, ZetaLogDerivInfra, HardySetupRequirements, GammaGrowthGeneral, ZetaBoundGtOne, RiemannSiegelBound |
| **Build baseline preserved** | `lake build` still passes with 10 sorry warnings (7 project + 3 external) |

## Recent Achievements (Session 12)

| Achievement | Details |
|------------|---------|
| **`OmegaThetaToPiLiHyp` moved out of `CriticalAssumptions`** | New bridge-owned placeholder instance in `Bridge/OmegaThetaToPiLiWiring.lean` |
| **Critical/bridge split improved** | Project total unchanged at 7, but split changed: critical 2 → 1, bridge 2 → 3 |
| **Build validation** | `lake build Littlewood.Main.Littlewood` passes with new bridge wiring |

## Previous Achievements (Session 11)

| Achievement | Details |
|------------|---------|
| **5 orphan Aristotle files wired into build** | HardyZIdentities, ZetaAnalyticProperties, OscillationInfraV2, ExplicitFormulaPerron, ZetaBoundFunctionalEq — all 0 sorries, now available in build tree |
| **ZetaAnalyticProperties chi conflict fixed** | Moved `chi` definition inside `Aristotle.ZetaAnalyticProperties` namespace to avoid conflict with `MeanSquare.lean` root-level `chi` |
| **RemainderTermAnalysis was previously skipped** | Later resolved and imported in Session 13 (all `exact?` placeholders closed). |
| **Sorry count unchanged** | 10 build warnings (7 project + 3 external) |
| **Aristotle files in build** | 76 → 81 |
| **Orphan files** | 55 → 50 |

## Previous Achievements (Session 10)

| Achievement | Details |
|------------|---------|
| **`ExplicitFormulaPsiHyp` REMOVED from critical path** | tsum `∑' ρ : zetaNontrivialZeros, x^ρ/ρ` is FALSE (not absolutely convergent → tsum = 0 in Lean/Mathlib). Removed sorry instance from CriticalAssumptions.lean; content folded into ExplicitFormulaOscillation bridge sorry. |
| **`ExplicitFormulaThetaHyp` REMOVED from critical path** | Same tsum issue. Removed sorry instance; content folded into ThetaExplicitFormulaOscillation bridge sorry. |
| **Bridge instances simplified** | ExplicitFormulaOscillation and ThetaExplicitFormulaOscillation now depend only on `[HardyCriticalLineZerosHyp]` (was `[HardyCriticalLineZerosHyp] [ExplicitFormula*Hyp]`). |
| **Project sorry count** | 12 → 10 build warnings, 9 → 7 project sorries |

## Previous Achievements (Session 8)

| Achievement | Details |
|------------|---------|
| **`psi_oscillation_implies_pi_li_oscillation` REMOVED** | Theorem was FALSE as stated: hypotheses require only sign changes, not amplitude bounds. If ψ(x)-x oscillates with tiny amplitude, θ(x)-x ≈ -√x < 0 always. Removed to eliminate spurious sorry. |
| **`zetaZeroCount_asymp` statement FIXED** | Changed from wrong `log T` to correct `log(T/2πe)`. Old formula off by Θ(T). |
| **`riemann_von_mangoldt` annotated** | Marked as vacuously proved (C depends on T). |
| **Project sorry count** | 13 → 12 build warnings, 10 → 9 project sorries |
| **Orphan file audit** | 76 Aristotle files in build, 55 orphans (most intentional: deprecated, V2/V3 variants, name conflicts) |

## Previous Achievements (Session 7)

| Achievement | Details |
|------------|---------|
| **`zeta_pl_interpolation` PROVED** | PL + Gaussian damping + Gammaℝ factorization. Applies PL.vertical_strip with F(s) = (s-1)ζ(s)·exp((s-it₀)²)·exp(-λs) |
| **`inv_gammaR_bound_ext` PROVED** | Extended inverse Gammaℝ bound to Re ∈ [-1/2, 3/2] (wider strip needed for PL application) |
| **`ZetaCriticalLineBoundHyp` AUTO-WIRED** | Via PhragmenLindelofWiring.lean: zeta_pl_interpolation → zeta_convexity_bound → zeta_critical_line_bound → instance |
| **PhragmenLindelof.lean** | 1 sorry → 0 sorries (file now clean) |
| **Project sorry count** | 15 → 13 build warnings, 12 → 10 project sorries |

## Previous Achievements (Session 6)

| Achievement | Details |
|------------|---------|
| **`inv_gammaR_bound` PROVED** | Gamma reflection formula approach: ‖Gammaℝ(s)⁻¹‖ ≤ exp(π\|Im s\|/2). Uses Γ(z)Γ(1-z)=π/sin(πz), convexity of Γ on [1,2], norm_cpow_eq_rpow_re_of_pos |
| **`sub_one_mul_zeta_growth` PROVED** | ‖(s-1)ζ(s)‖ ≤ A·exp(\|Im s\|) for Re(s) ∈ [δ,2]. Cascades from inv_gammaR_bound + completedRiemannZeta₀_bounded_on_strip |
| **PhragmenLindelof.lean** | 2 sorries → 1 sorry (only `zeta_pl_interpolation` remains) |
| **5 new Aristotle files integrated** | ZetaBoundFunctionalEq, RemainderTermAnalysis, ZeroCountingV2, HardyZIdentities, OscillationInfraV2 — all sorry-free |
| **Project sorry count** | 16 → 15 build warnings, 13 → 12 project sorries |

## Previous Achievements (Session 5)

| Achievement | Details |
|------------|---------|
| **`completedRiemannZeta₀_bounded_on_strip` PROVED** | KEY BOTTLENECK closed. Entire function Λ₀(s) bounded on vertical strips via Mellin norm bound: ‖mellin f w‖ ≤ ∫ t^{Re(w)-1}·‖f(t)‖, pointwise t^σ ≤ t^a + t^b, MellinConvergent endpoint integrals |
| **`sub_one_mul_zeta_growth` statement corrected** | Changed from exp(π\|t\|/4) to exp(\|t\|) — polynomial from Stirling can't be absorbed into exp(π\|t\|/4) with fixed constant |

## Previous Achievements (Session 4)

| Achievement | Details |
|------------|---------|
| **ExplicitFormulaPerron integrated** | Sorry-free. Defines chebyshevPsi, ZetaExplicitData, ExplicitFormulaPsiHyp, PerronFormulaHyp, explicitFormulaIntegrand |
| **ZetaAnalyticProperties integrated** | Sorry-free (2 budget sorries closed). Functional equation, zeros isolated, zeros finite in rectangles, analytic at s!=1, Re(zeta)>0 for Re(s)>=2, log zeta bounded on line 2 |
| **DirichletPhaseAlignment integrated** | Sorry-free. Dirichlet simultaneous approximation (fully proved), phase alignment infrastructure |
| **ZeroCountingRectangle integrated** | Sorry-free. Rectangle integral, limit_mul_zeta_sub_one, tendsto_mul_sq_deriv_of_simple_pole, residue_zeta_log_deriv_at_one |
| **PhragmenLindelof refactored** | gamma_growth and zeta_critical_line_bound CLOSED. zeta_convexity_bound structurally proved modulo zeta_pl_interpolation |
| **Budget sorries all closed** | 22/22 budget-exhaustion sorries (exact? timeouts) have been resolved |

## Active Sorries (Build-Visible)

| File | Sorries | Content | Difficulty | Bridge Ready? |
|------|---------|---------|------------|---------------|
| **HardyApproxFunctionalEq.lean** | 1 | `approx_functional_eq`: ∫Z² ≥ k·∫\|S\|² - C·T | Deep | FULLY AUTO (MeanSquareBridge) |
| **ZeroCounting.lean** | 2 | `zetaZeroCount_via_argument` (argument principle), `zetaZeroCount_asymp` (statement FIXED: uses log(T/2πe)) | Deep | Not on critical path |
| ~~**PartialSummation.lean**~~ | ~~0~~ | ~~`psi_oscillation_implies_pi_li_oscillation` REMOVED — was FALSE as stated~~ | N/A | N/A |

## Critical Path Analysis

```
littlewood_psi                          littlewood_pi_li
       ↑                                      ↑
PsiOscillationSqrtHyp [auto]          PiLiOscillationSqrtHyp [auto]
       ↑                                      ↑
PsiOscillationFromCriticalZeros        ThetaOscillationSqrt
  [Bridge, 1 sorry]                     [Bridge, 1 sorry]
       ↑                                      ↑
HardyCriticalLineZerosHyp [auto]       ├── HardyCriticalLineZerosHyp [auto]
  ↑          ↑                          └── OmegaThetaToPiLiHyp [Bridge, 1 sorry]
ZetaCritical  HardyFirst
LineBoundHyp  MomentUpper
 [AUTO]       [SORRY]
```

NOTE: ExplicitFormulaPsiHyp and ExplicitFormulaThetaHyp REMOVED from critical path
(tsum formulation was FALSE). Their content is folded into the bridge sorries.

### Nearest to Closing

1. **ZetaCriticalLineBoundHyp** — CLOSED (auto-wired via PhragmenLindelofWiring.lean).

2. **OmegaThetaToPiLiHyp** (`Bridge/OmegaThetaToPiLiWiring.lean`) — Transfer plumbing is now formalized via `Aristotle/ThetaToPiLiTransferInfra.lean` and `omegaThetaToPiLi_from_remainder_small`. The remaining blocker is a single analytic estimate class: `ThetaPiLiRemainderSmallHyp` (`thetaPiLiRemainder =o(f/log)`).

3. **HardyFirstMomentUpperHyp** — Conditional theorem and measurability wiring proved; 2 remaining integral-bound prerequisites are isolated in `Bridge/HardyFirstMomentWiring.lean` (`MainTermFirstMomentBoundHyp`, `ErrorTermFirstMomentBoundHyp`).

## Aristotle Bridge Files (all sorry-free)

| File | Content |
|------|---------|
| **Bridge/GammaGrowthWiring.lean** | hasGammaGrowth for σ=1/2, 1, 3/2, n/2+k, all n>0 |
| **Bridge/GammaGrowthComplete.lean** | hasGammaGrowth_all, upper/lower growth for all σ>0 |
| **Bridge/StirlingRatioPL.lean** | stirling_ratio_bounded_on_strip via PL |

## Key Sorry-Free Files (recent additions)

| File | Content |
|------|---------|
| **ZetaBoundFunctionalEq.lean** | ζ bounded in Re(s)≥1+δ, χ(s) factor, functional equation ζ(s)=χ(s)ζ(1-s) |
| **RemainderTermAnalysis.lean** | ψ, li, remainder definitions; Cauchy-Schwarz for integrals; ∫1/log⁴ bound; remainder² analysis |
| **ZeroCountingV2.lean** | ζ zeros isolated, ζ≠0 near s=1, zeros finite in compact/rect |
| **HardyZIdentities.lean** | S partial sum, hardy_square_bound, pointwise identity, integrability |
| **OscillationInfraV2.lean** | IsOmegaPlus/Minus/PlusMinus (alt defs), DirichletInfra, sum_diverges |
| **ExplicitFormulaPerron.lean** | chebyshevPsi, ZetaExplicitData, ExplicitFormulaPsiHyp class, PerronFormulaHyp class |
| **ZetaAnalyticProperties.lean** | Functional equation, zeros isolated/finite, analytic at s≠1, Re(ζ)>0 for Re(s)≥2, log ζ bounded on σ=2 |
| **DirichletPhaseAlignment.lean** | Simultaneous Dirichlet approximation (PROVED), phase alignment for zero sum oscillation |
| **ZeroCountingRectangle.lean** | (s-1)ζ(s)→1, (s-1)²ζ'(s)→-1, residue of ζ'/ζ at s=1 |
| **ContourIntegrationV2.lean** | Cauchy rectangle theorem, residue at simple pole, segment integrals |
| **ZetaLogDerivInfra.lean** | All 10 theorems proved: pole structure of -ζ'/ζ, analytic orders |
| **VanDerCorputInfra.lean** | Van der Corput first/second derivative infrastructure for oscillatory integrals |
| **GammaGrowthGeneral.lean** | General Gamma growth bounds used by strip/contour arguments |
| **ZetaBoundGtOne.lean** | Additional `Re(s)>1` zeta growth/boundedness infrastructure |
| **RiemannSiegelBound.lean** | Riemann-Siegel style Hardy Z control lemmas |
| **HardySetupRequirements.lean** | Documentation-only checklist module (now imported for visibility) |
| **ThetaToPiLiTransferInfra.lean** | Exact θ→(π-li) decomposition identity in project notation, hypothesis-free |

## What Aristotle Needs Next

### Priority 1: Bridge oscillation extraction
Prove IsOmegaPlusMinus from explicit formula + Hardy zeros using Dirichlet phase alignment.
Infrastructure exists in DirichletPhaseAlignment.lean; needs wiring to Littlewood types.

**OBSTRUCTION ANALYSIS (Session 10)**:
- ExplicitFormulaPsiHyp/ThetaHyp REMOVED from bridge dependencies (tsum was FALSE).
- Bridge sorries now absorb the full oscillation extraction: truncated explicit formula
  + Dirichlet phase alignment + anti-alignment.
- DirichletPhaseAlignment.lean (now imported) proves alignment (Ω₋ direction) but only for
  `IsOmegaOscillation` (∀ M, ∃ x, f x ≥ M·g x), not `IsOmegaPlusMinus`.
- Anti-alignment (Ω₊ direction) requires inhomogeneous Dirichlet approximation or
  mean-value argument — neither proved in the codebase.
- Closing the bridge sorry requires: (i) truncated explicit formula (needs Perron's
  formula, not in Mathlib), (ii) phase alignment adapted for IsOmegaPlusMinus,
  (iii) anti-alignment for the opposite direction.

### Priority 2: `approx_functional_eq` (HardyApproxFunctionalEq.lean:113)
Approximate functional equation for Z(t)². Feeds Hardy first moment chain.

**OBSTRUCTION**: Requires the approximate functional equation Z(t) ≈ 2·Re(S_N(t)) + O(t^{-1/4}),
which is deep analytic number theory (Riemann-Siegel formula). Not available in Mathlib.

### Priority 3: Perron formula chain (Prompts 6-9)
ContourIntegration → RectangleCauchy → PerronFormula → ExplicitFormula.
Blocked on vertical line integrals (not in Mathlib).

### Priority 4: OmegaThetaToPiLiHyp (Bridge/OmegaThetaToPiLiWiring.lean:26)
Transfer θ(x)-x = Ω±(f) to π(x)-li(x) = Ω±(f/log x).

**OBSTRUCTION**: The exact decomposition is now in-tree and the perturbative Ω± transfer lemma is proved. The unresolved content is proving `thetaPiLiRemainder =o(f/log)` for all `f` with `√x ≤ f(x)` eventually; existing absolute θ-error bounds still leave a remainder term too large at `f=√x`.

## RiemannVonMangoldt Infrastructure Note

**RiemannVonMangoldt.lean**: ALL theorems are VACUOUSLY proved (C depends on T).
`riemann_von_mangoldt_conditional` is genuine but requires 3 unproved hypotheses
(Stirling, Backlund, Argument Principle).

**RiemannVonMangoldtV2.lean**: `NZeros` is a FORMULA (type ℝ), not the actual zero count.
`N_eq_main_plus_S` proves self-consistency of the formula, NOT that it equals `zetaZeroCount`.
The connection between the formula and the actual zero count IS the argument principle
(the content of the `zetaZeroCount_via_argument` sorry).

## zetaZeroCount_asymp Note

**FIXED**: The statement at ZeroCounting.lean:132 now correctly uses `log(T/2πe)`:
```
(fun T => (zetaZeroCount T : ℝ) - (T / (2 * π)) * log (T / (2πe))) =O[atTop] (fun T => log T)
```
The old statement using `log T` was wrong by a Θ(T) term. The `riemann_von_mangoldt`
at line 123 is vacuously proved (C defined as |error|/log T) — annotated as such.
