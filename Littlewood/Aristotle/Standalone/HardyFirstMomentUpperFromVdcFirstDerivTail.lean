import Mathlib
import Littlewood.Bridge.HardyFirstMomentWiring
import Littlewood.Bridge.HardyChainHyp

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyFirstMomentUpperFromVdcFirstDerivTail

open Complex Real Set Filter Topology MeasureTheory
open HardyEstimatesPartial

/--
Construct `HardyFirstMomentUpperHyp` from an explicit van-der-Corput tail package
for cosine modes and a pointwise inverse-sqrt bound for the RS error term.

This theorem is fully proved and `sorry`-free; it isolates the remaining deep
analytic obligations as explicit assumptions.
-/
theorem hardyFirstMomentUpperHyp_of_vdcFirstDeriv_tail_and_errorPointwiseInvSqrt
    (hPhaseDiff :
      ∀ n : ℕ, Differentiable ℝ (HardyFirstMomentWiring.hardyPhaseReal n))
    (hPhaseDerivDiff :
      ∀ n : ℕ, Differentiable ℝ (deriv (HardyFirstMomentWiring.hardyPhaseReal n)))
    (hPhaseSecondCont :
      ∀ n : ℕ, Continuous (deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n))))
    (hDerivLowerTail :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.Icc (hardyStart n + Real.sqrt (n + 1)) T,
          m / Real.sqrt (n + 1)
            ≤ deriv (HardyFirstMomentWiring.hardyPhaseReal n) t)
    (hSecondNonnegTail :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.Icc (hardyStart n + Real.sqrt (n + 1)) T,
          0 ≤ deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t)
    (hErrPointwise :
      ∃ C > 0, ∀ t : ℝ, t ≥ 1 →
        |ErrorTerm t| ≤ C / Real.sqrt t) :
    HardyFirstMomentUpperHyp := by
  let hCos : HardyFirstMomentWiring.HardyCosIntegralSqrtModeBoundHyp :=
    HardyFirstMomentWiring.hardyCosIntegralSqrtModeBound_of_vdcFirstDeriv_tail
      hPhaseDiff hPhaseDerivDiff hPhaseSecondCont hDerivLowerTail hSecondNonnegTail
  let hMain : HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
    let _ : HardyFirstMomentWiring.HardyCosIntegralSqrtModeBoundHyp := hCos
    infer_instance
  let hErr : HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp :=
    HardyFirstMomentWiring.errorTermFirstMomentBound_of_pointwise_invSqrt hErrPointwise
  let _ : HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := hMain
  let _ : HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp := hErr
  exact HardyFirstMomentWiring.hardyFirstMomentUpper_from_two_bounds

/--
Exact `HardySetupV2.first_moment_upper` field shape from the explicit VdC-tail
and pointwise error assumptions above.
-/
theorem hardy_first_moment_upper_for_setup_v2_of_vdcFirstDeriv_tail_and_errorPointwiseInvSqrt
    (hPhaseDiff :
      ∀ n : ℕ, Differentiable ℝ (HardyFirstMomentWiring.hardyPhaseReal n))
    (hPhaseDerivDiff :
      ∀ n : ℕ, Differentiable ℝ (deriv (HardyFirstMomentWiring.hardyPhaseReal n)))
    (hPhaseSecondCont :
      ∀ n : ℕ, Continuous (deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n))))
    (hDerivLowerTail :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.Icc (hardyStart n + Real.sqrt (n + 1)) T,
          m / Real.sqrt (n + 1)
            ≤ deriv (HardyFirstMomentWiring.hardyPhaseReal n) t)
    (hSecondNonnegTail :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.Icc (hardyStart n + Real.sqrt (n + 1)) T,
          0 ≤ deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t)
    (hErrPointwise :
      ∃ C > 0, ∀ t : ℝ, t ≥ 1 →
        |ErrorTerm t| ≤ C / Real.sqrt t) :
    ∀ ε : ℝ, ε > 0 →
      ∃ C : ℝ, C > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧
        ∀ T : ℝ, T ≥ T₀ →
          |∫ t in Ioc 1 T, hardyZ t| ≤ C * T ^ (1 / 2 + ε) := by
  let hFirst :
      HardyFirstMomentUpperHyp :=
    hardyFirstMomentUpperHyp_of_vdcFirstDeriv_tail_and_errorPointwiseInvSqrt
      hPhaseDiff hPhaseDerivDiff hPhaseSecondCont hDerivLowerTail hSecondNonnegTail
      hErrPointwise
  intro ε hε
  exact hFirst.bound ε hε

end Aristotle.Standalone.HardyFirstMomentUpperFromVdcFirstDerivTail

