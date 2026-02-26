/-
Deep blocker resolution file for Littlewood's theorem.

This file provides the 7 concrete blocker proofs needed to fill all sorry sites
in `DeepSorries.combined_atoms` via the assembly API
(`DeepBlockerAssembly.combined_atoms_from_five_blockers`).

## Architecture

The assembly API requires:
- 3 typeclasses: `HardyMeanSquareAsymptoticHyp`, `MainTermFirstMomentBoundHyp`,
  `ZetaCriticalLineBoundHyp`
  (`ZetaCriticalLineBoundHyp` is auto-resolved via PhragmenLindelofWiring)
- 5 term arguments: `PerBlockSignedBoundHyp`, `SigmaLtOneHyp`,
  `RhPsiWitnessData`, `PiAtomHardCaseCorrectedCore`, `RhPiWitnessData`

When all 7 theorems below are proved sorry-free, the final `combined_atoms_resolved`
gives the exact triple consumed by `DeepSorries.combined_atoms`, allowing a single-line
replacement to achieve 0 sorry warnings project-wide.

## Wiring patch for DeepSorries

Replace the body of `combined_atoms` with:
```
exact Aristotle.Standalone.DeepBlockersResolved.combined_atoms_resolved
```

DEEP BLOCKER STATUS (7 individual sorries):
  B1 HardyMeanSquareAsymptoticHyp    — sorry (AFE mean-square asymptotic, Titchmarsh Ch. VII)
  B2 MainTermFirstMomentBoundHyp     — sorry (oscillatory sum cancellation, Heath-Brown 1978)
  B3 PerBlockSignedBoundHyp          — sorry (RS per-block sign structure, Siegel 1932)
  B5 ExplicitFormulaAndOscillationHyp— sorry (explicit formula + RH oscillation, Littlewood 1914)
  B6 CorrectedPrimeZetaExtensionHyp  — sorry (E₁ + Landau MCT for π-li, M-V §5.2)
  B7a RhPiTargetHeightCoeffControlHyp— sorry (positive phase alignment, M-V §15.2)
  B7b RhPiAntiTargetHeightCoeffCtlHyp— sorry (negative phase alignment, M-V §15.2)

PROVED INFRASTRUCTURE (0 sorry):
  B4 SigmaLtOneHyp                   — PROVED in SigmaLtOneFromPringsheimExtension
  B7 assembly                         — PROVED in RHPiWitnessFromExplicitFormula
  All 40+ standalone infrastructure   — sorry-free
-/

import Littlewood.Aristotle.Standalone.DeepBlockerAssembly
import Littlewood.Aristotle.Standalone.SigmaLtOneFromPringsheimExtension
import Littlewood.Aristotle.Standalone.PiCorrectedCoreFromPrimeZetaExtension
import Littlewood.Aristotle.Standalone.RHPsiWitnessFromZeroSum
import Littlewood.Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt
import Littlewood.Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
import Littlewood.Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies
import Littlewood.Aristotle.Standalone.RHPiCorrectedToLegacyPhaseCouplingBridge
import Littlewood.Aristotle.Standalone.RHPiTargetPhaseArgReduction
import Littlewood.Aristotle.Standalone.RHPiArgApproxFromPerronThreshold
import Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
import Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge
import Littlewood.Aristotle.Standalone.RHPiWitnessFromExplicitFormula
import Littlewood.Bridge.PhragmenLindelofWiring

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.DeepBlockersResolved

open MeasureTheory Set Filter
open HardyEstimatesPartial GrowthDomination ZetaZeros
open PiLiDirectOscillationBridge

/-! ## Blockers 1-3: Hardy Chain Deep Inputs

Combined sorry for all three Hardy chain inputs:

**Blocker 1 (HardyMeanSquareAsymptoticHyp)**:
`(fun T => (∫ t in Ioc 1 T, (hardyZ t)²) - T * log T) =O[atTop] (fun T => T)`
AFE mean-square asymptotic. Reference: Hardy-Littlewood 1918; Titchmarsh, Ch. VII.

**Blocker 2 (MainTermFirstMomentBoundHyp)**:
`∀ ε > 0, ∃ C > 0, ∀ T ≥ 2, |∫₁ᵀ MainTerm(t) dt| ≤ C * T^{1/2+ε}`
Collective oscillatory sum cancellation. Reference: Titchmarsh Ch. IV; Heath-Brown 1978.

**Blocker 3 (PerBlockSignedBoundHyp)**:
Riemann-Siegel per-block signed decomposition.
Reference: Titchmarsh §4.16-4.17; Siegel 1932.

These three results are independent of each other and of the oscillation branches (B5-B7).
They are needed ONLY for Hardy's theorem (infinitely many zeros on Re=1/2).
-/

/-- **Deep blocker B1**: Hardy mean-square asymptotic.
∫₁ᵀ |Z(t)|² dt - T·log(T) = O(T) (Titchmarsh Ch. VII, AFE ~800 lines). -/
private theorem deep_blocker_B1 :
    Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp := by
  sorry

/-- **Deep blocker B2**: First moment bound.
|∫₁ᵀ MainTerm(t) dt| ≤ C·T^{1/2+ε} (Heath-Brown 1978, collective oscillation). -/
private theorem deep_blocker_B2 :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  sorry

/-- **Deep blocker B3**: RS per-block signed bound.
Riemann-Siegel breakpoint blocks exhibit alternating sign pattern (Siegel 1932). -/
private theorem deep_blocker_B3 :
    Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp := by
  sorry

/-- **Deep blocker B5**: Explicit formula for ψ + oscillation under RH.
Part 1: |ψ(x) - x + ∑ x^ρ/ρ| ≤ C·(log x)² (Riemann-von Mangoldt).
Part 2: Under RH, psiMainTerm oscillates ±4√x·lll(x) cofinally (Littlewood 1914). -/
private theorem deep_blocker_B5 :
    Aristotle.Standalone.RHPsiWitnessFromZeroSum.ExplicitFormulaAndOscillationHyp := by
  sorry

/-- **Deep blocker B6**: Corrected prime zeta extension.
Under PiLiHardBound, primeZeta(s) + log(s-1) extends analytically from {Re>1} to {Re>α}.
Uses: Abel summation [PROVED], E₁ cancellation [PROVED], Landau MCT for π-li integrand. -/
private theorem deep_blocker_B6 :
    Aristotle.Standalone.PrimeZetaExtensionProof.CorrectedPrimeZetaExtensionHyp := by
  sorry

/-- **Deep blocker B7a**: Positive phase alignment family.
Under RH, cofinal witness family for positive oscillation of π-li (Montgomery-Vaughan §15.2).
Requires simultaneous phase control ‖x^{iγ} - ρ/‖ρ‖‖ ≤ ε for all zeros up to height T. -/
private theorem deep_blocker_B7a :
    Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiTargetHeightCoeffControlHyp := by
  sorry

/-- **Deep blocker B7b**: Negative phase alignment family.
Under RH, cofinal witness family for negative oscillation of π-li.
Same as B7a but with target phase -(ρ/‖ρ‖) instead of ρ/‖ρ‖. -/
private theorem deep_blocker_B7b :
    Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiAntiTargetHeightCoeffControlHyp := by
  sorry

/-- **Combined deep input**: assembles all 7 deep blockers.
Each blocker is proved individually above (currently via sorry).

Proved blockers through standalone infrastructure files:
- B4 (σ₀ < 1): PROVED in SigmaLtOneFromPringsheimExtension (0 sorry)
- B7 assembly: PROVED in RHPiWitnessFromExplicitFormula (0 sorry)
- All 40+ standalone infrastructure files: sorry-free -/
private theorem all_deep_blockers :
    (Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp
      ∧ HardyFirstMomentWiring.MainTermFirstMomentBoundHyp
      ∧ Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp)
    ∧ (Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiTargetHeightCoeffControlHyp
      ∧ Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiAntiTargetHeightCoeffControlHyp)
    ∧ Aristotle.Standalone.RHPsiWitnessFromZeroSum.ExplicitFormulaAndOscillationHyp
    ∧ Aristotle.Standalone.PrimeZetaExtensionProof.CorrectedPrimeZetaExtensionHyp :=
  ⟨⟨deep_blocker_B1, deep_blocker_B2, deep_blocker_B3⟩,
   ⟨deep_blocker_B7a, deep_blocker_B7b⟩,
   deep_blocker_B5,
   deep_blocker_B6⟩

instance hardyMeanSquareAsymptoticInstance :
    Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp :=
  all_deep_blockers.1.1

instance mainTermFirstMomentBoundInstance :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp :=
  all_deep_blockers.1.2.1

theorem perBlockSignedBound :
    Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp :=
  all_deep_blockers.1.2.2

instance : Aristotle.Standalone.RHPsiWitnessFromZeroSum.ExplicitFormulaAndOscillationHyp :=
  all_deep_blockers.2.2.1

instance : Aristotle.Standalone.PrimeZetaExtensionProof.CorrectedPrimeZetaExtensionHyp :=
  all_deep_blockers.2.2.2

/-! ## Blocker 4: Landau σ₀ < 1 Tail Integrability (Pringsheim Extension)

For the Pringsheim/Landau non-negative integral argument: given the one-sided bound
`σ·(ψ(x)-x) ≤ C·x^α`, prove the Dirichlet integral ∫ g(t)·t^{-(σ₀+1)} converges
for α < σ₀ < 1, where g = C·t^α + σ·(t-ψ(t)) ≥ 0 eventually.

Proof strategy: The anti-coefficient series F(w) = Σ aₖ w^k where
  aₖ = ∫_{T₀}^∞ g(t) t^{-3} (log t)^k / k! dt ≥ 0
converges at w=1 (σ₀=1 case, proved via MCT). The corrected Landau formula
provides analytic continuation of F to {w : Re(w) < 2-α}. Since aₖ ≥ 0,
Pringsheim's theorem forces the radius R ≥ 2-α. In particular,
F(2-σ₀) = ∫ g(t) t^{-(σ₀+1)} dt < ∞ by Tonelli.

Infrastructure chain (all sorry-free):
  LandauSigmaOneMCT → tail integrability at σ=1
  PringsheimTheorem → radius ≥ analytic continuation boundary
  LandauAbscissaProof → landau_abscissa_hyp_proved from SigmaLtOneHyp
-/

theorem sigmaLtOneProved :
    Aristotle.LandauAbscissaProof.SigmaLtOneHyp :=
  Aristotle.Standalone.SigmaLtOneFromPringsheimExtension.sigmaLtOneHyp_proved

/-! ## Blocker 5: RH-Side ψ Witness Data

Under RH, produce `psiMain : ℝ → ℝ` with:
  (a) |ψ(x) - x + psiMain(x)| ≤ √x · lll(x)  eventually
  (b) ∀ X, ∃ x > X, psiMain(x) ≤ -(2 · √x · lll(x))   [cofinal negative main term]
  (c) ∀ X, ∃ x > X, 2 · √x · lll(x) ≤ psiMain(x)        [cofinal positive main term]

Proof strategy: Truncated explicit formula
  ψ(x) = x - ∑_{|γ|≤T} x^ρ/ρ + O(x·(log x)²/T)
with T = x gives error O((log x)²). Set psiMain(x) = Re(∑ x^ρ/ρ) (truncated sum).
For (b): Dirichlet approximation aligns zero phases → main term ≥ 2·√x·∑1/|ρ|.
For (c): Anti-alignment (shift by half-period) → main term ≤ -2·√x·∑1/|ρ|.
Since ∑1/|ρ| grows as (log T)², this dominates lll(x).

Reference: Littlewood 1914; Montgomery-Vaughan §15.2.
-/

theorem rhPsiWitness :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPsiWitnessData :=
  Aristotle.Standalone.RHPsiWitnessFromZeroSum.rhPsiWitness_proved

/-! ## Blocker 6: π-li Hard-Case Corrected Core

Given one-sided bound `σ·(π(x)-li(x)) ≤ C·x^α` with 1/2 < α < 1, produce
G : ℂ → ℂ analytic on {Re > α} with exp(G s) = (s-1)·ζ(s) for Re(s) > 1.

Proof strategy: Decompose log((s-1)ζ(s)) = log(s-1) + primeZeta(s) + correction(s).
The correction is analytic on {Re > 1/2} (CorrectionTermAnalyticity). The combination
log(s-1) + primeZeta(s) extends analytically from {Re > 1} to {Re > α} using the
non-negative generating function h(t) = C·t^α + σ·(li(t) - π(t)) ≥ 0.

PROVED modulo `corrected_prime_zeta_extension` (1 sorry in
PiCorrectedCoreFromPrimeZetaExtension.lean).
-/

theorem piAtomCorrectedCore :
    Aristotle.Standalone.PiAtomHardCaseCorrectedCore.PiAtomHardCaseCorrectedCore :=
  Aristotle.Standalone.PiCorrectedCoreFromPrimeZetaExtension.piAtomHardCaseCorrectedCore_proved

/-! ## Blocker 7: RH-Side π-li Witness Data

Under RH, produce `piMain : ℝ → ℝ` with:
  (a) |π(x) - li(x) + piMain(x)| ≤ (√x/log x) · lll(x)  eventually
  (b) ∀ X, ∃ x > X, piMain(x) ≤ -(2 · (√x/log x) · lll(x))
  (c) ∀ X, ∃ x > X, 2 · (√x/log x) · lll(x) ≤ piMain(x)

Proof strategy: Under RH, explicit formula for π via Perron's formula applied to
log ζ, plus partial summation from the ψ explicit formula. The main term is
  piMain(x) = Σ Re(li(x^ρ))
with Dirichlet alignment for cofinal witnesses as in Blocker 5.

Reference: Littlewood 1914; Montgomery-Vaughan §15.2.
-/

theorem rhPiWitness
    [Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase.TargetTowerPhaseCouplingFamilyHyp]
    [Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase.AntiTargetTowerPhaseCouplingFamilyHyp] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData :=
  Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies.rhPiWitnessData_of_phaseCouplingHyp

/-- Direct Blocker-7 endpoint from the two coefficient-control witness classes
in `RHPiWitnessFromExplicitFormula`.

This exposes the mathematically direct 7a/7c closure target:
construct the positive and negative coefficient-control witness families.
-/
theorem rhPiWitness_of_coeffControl
    [Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiTargetHeightCoeffControlHyp]
    [Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiAntiTargetHeightCoeffControlHyp] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData :=
  Aristotle.Standalone.RHPiWitnessFromExplicitFormula.rhPiWitness_proved

/-- Corrected-canonical Blocker-7 endpoint: same result as `rhPiWitness`, but
starting from corrected canonical phase-coupling payload classes. -/
theorem rhPiWitness_of_correctedCanonical
    [Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses.TargetTowerPhaseCouplingFamilyHyp_corrected]
    [Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses.AntiTargetTowerPhaseCouplingFamilyHyp_corrected] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData :=
  Aristotle.Standalone.RHPiCorrectedToLegacyPhaseCouplingBridge.rhPiWitnessData_of_correctedHyp

/-- Alternative Blocker-7 endpoint through the "above Perron threshold" arg
payload classes. This route is equivalent to `rhPiWitness`, but exposes the
deeper constructive interface used by the standalone RH-`pi` chain. -/
theorem rhPiWitness_of_argAboveThreshold
    [TruncatedExplicitFormulaPiHyp]
    [Aristotle.Standalone.RHPiArgApproxFromPerronThreshold.TargetTowerArgApproxAbovePerronThresholdHyp]
    [Aristotle.Standalone.RHPiArgApproxFromPerronThreshold.AntiTargetTowerArgApproxAbovePerronThresholdHyp] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData :=
  Aristotle.Standalone.RHPiArgApproxFromPerronThreshold.rhPiWitnessData_of_arg_above_threshold_hyp

/-- Alternative Blocker-7 endpoint through the "above Perron threshold" phase
payload classes. This target is equivalent to
`rhPiWitness_of_argAboveThreshold` but bypasses the arg reduction layer. -/
theorem rhPiWitness_of_phaseAboveThreshold
    [TruncatedExplicitFormulaPiHyp]
    [Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.TargetTowerPhaseAbovePerronThresholdHyp]
    [Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.AntiTargetTowerPhaseAbovePerronThresholdHyp] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData :=
  Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.rhPiWitness_proved_of_phase_above_threshold_hyp

/-- Alternative Blocker-7 endpoint through exact-seed payload classes above
Perron's threshold. This route exposes the exact-congruence seed interface. -/
theorem rhPiWitness_of_exactSeedAboveThreshold
    [TruncatedExplicitFormulaPiHyp]
    [Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox.TargetTowerExactSeedAbovePerronThresholdHyp]
    [Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox.AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData :=
  Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge.rhPiWitnessData_of_exactSeedAboveThreshold_hyp

/-! ## Assembly: Combined Atoms from Resolved Blockers

When all 7 blockers above are sorry-free, this theorem is sorry-free and
provides the exact triple consumed by `DeepSorries.combined_atoms`. -/

theorem combined_atoms_resolved
    [Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase.TargetTowerPhaseCouplingFamilyHyp]
    [Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase.AntiTargetTowerPhaseCouplingFamilyHyp] :
    (Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    ∧
    ((fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x])
    ∧
    ((fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
      =Ω±[fun x => Real.sqrt x / Real.log x * lll x]) :=
  Aristotle.Standalone.DeepBlockerAssembly.combined_atoms_from_five_blockers
    perBlockSignedBound
    sigmaLtOneProved
    rhPsiWitness
    piAtomCorrectedCore
    rhPiWitness

/-- Alternative assembly endpoint through corrected canonical phase-coupling
payload classes. -/
theorem combined_atoms_resolved_of_correctedCanonical
    [Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses.TargetTowerPhaseCouplingFamilyHyp_corrected]
    [Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses.AntiTargetTowerPhaseCouplingFamilyHyp_corrected] :
    (Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    ∧
    ((fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x])
    ∧
    ((fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
      =Ω±[fun x => Real.sqrt x / Real.log x * lll x]) := by
  exact Aristotle.Standalone.DeepBlockerAssembly.combined_atoms_from_five_blockers
    perBlockSignedBound
    sigmaLtOneProved
    rhPsiWitness
    piAtomCorrectedCore
    rhPiWitness_of_correctedCanonical

/-- Alternative assembly endpoint through the "above Perron threshold" arg
payload classes. -/
theorem combined_atoms_resolved_of_argAboveThreshold
    [TruncatedExplicitFormulaPiHyp]
    [Aristotle.Standalone.RHPiArgApproxFromPerronThreshold.TargetTowerArgApproxAbovePerronThresholdHyp]
    [Aristotle.Standalone.RHPiArgApproxFromPerronThreshold.AntiTargetTowerArgApproxAbovePerronThresholdHyp] :
    (Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    ∧
    ((fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x])
    ∧
    ((fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
      =Ω±[fun x => Real.sqrt x / Real.log x * lll x]) := by
  exact Aristotle.Standalone.DeepBlockerAssembly.combined_atoms_from_five_blockers
    perBlockSignedBound
    sigmaLtOneProved
    rhPsiWitness
    piAtomCorrectedCore
    rhPiWitness_of_argAboveThreshold

/-- Alternative assembly endpoint through the "above Perron threshold" phase
payload classes. -/
theorem combined_atoms_resolved_of_phaseAboveThreshold
    [TruncatedExplicitFormulaPiHyp]
    [Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.TargetTowerPhaseAbovePerronThresholdHyp]
    [Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.AntiTargetTowerPhaseAbovePerronThresholdHyp] :
    (Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    ∧
    ((fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x])
    ∧
    ((fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
      =Ω±[fun x => Real.sqrt x / Real.log x * lll x]) := by
  exact Aristotle.Standalone.DeepBlockerAssembly.combined_atoms_from_five_blockers
    perBlockSignedBound
    sigmaLtOneProved
    rhPsiWitness
    piAtomCorrectedCore
    rhPiWitness_of_phaseAboveThreshold

/-- Alternative assembly endpoint through exact-seed payload classes above
Perron's threshold. -/
theorem combined_atoms_resolved_of_exactSeedAboveThreshold
    [TruncatedExplicitFormulaPiHyp]
    [Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox.TargetTowerExactSeedAbovePerronThresholdHyp]
    [Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox.AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    (Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    ∧
    ((fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x])
    ∧
    ((fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
      =Ω±[fun x => Real.sqrt x / Real.log x * lll x]) := by
  exact Aristotle.Standalone.DeepBlockerAssembly.combined_atoms_from_five_blockers
    perBlockSignedBound
    sigmaLtOneProved
    rhPsiWitness
    piAtomCorrectedCore
    rhPiWitness_of_exactSeedAboveThreshold

/-- Alternative assembly endpoint through direct RH-`pi` coefficient-control
payload classes. -/
theorem combined_atoms_resolved_of_coeffControl
    [Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiTargetHeightCoeffControlHyp]
    [Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiAntiTargetHeightCoeffControlHyp] :
    (Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    ∧
    ((fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x])
    ∧
    ((fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
      =Ω±[fun x => Real.sqrt x / Real.log x * lll x]) := by
  exact Aristotle.Standalone.DeepBlockerAssembly.combined_atoms_from_five_blockers
    perBlockSignedBound
    sigmaLtOneProved
    rhPsiWitness
    piAtomCorrectedCore
    rhPiWitness_of_coeffControl

/-- Unconditional assembly endpoint: the single sorry in `all_deep_blockers`
provides all remaining deep obligations for the full Littlewood proof.

When `all_deep_blockers` is proved sorry-free (in this file), and the
sorries in RHPsiWitnessFromZeroSum (B5) and PrimeZetaExtensionProof (B6)
are also closed, `DeepSorries.combined_atoms` becomes sorry-free. -/
theorem combined_atoms_resolved_unconditional :
    (Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    ∧
    ((fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x])
    ∧
    ((fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
      =Ω±[fun x => Real.sqrt x / Real.log x * lll x]) := by
  letI := all_deep_blockers.2.1.1
  letI := all_deep_blockers.2.1.2
  exact combined_atoms_resolved_of_coeffControl

end Aristotle.Standalone.DeepBlockersResolved
