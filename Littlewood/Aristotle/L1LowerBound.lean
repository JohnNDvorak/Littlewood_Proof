/-
L1 Lower Bound for Hardy's Z function — Aristotle output.

Proves l1_lower_bound and mean_square_lower_bound for a MODEL function Z(t) = t.
The proofs demonstrate the technique (nlinarith + log inequalities) but use a mock
definition. The real Hardy Z function ζ(1/2+it)·exp(iθ(t)) would require the
approximate functional equation and convexity bounds.

Integration note:
- MockHardyZ.hardyZ t = t (identity, not the real Hardy Z)
- mean_square_lower_bound: proved for Z(t)=t (∫t² ~ T³/3 ≥ c·T·log T)
- l1_lower_bound: proved for Z(t)=t (∫|t| ~ T²/2 ≥ c·T)
- Neither proof transfers to the real hardyZ without additional analytic input

To close the real l1_lower_bound sorry in HardySetupInstance.lean, one needs EITHER:
  (a) mean_square_lower_bound for real Z + pointwise bound |Z(t)| = O(t^ε), or
  (b) a direct L1 lower bound from the approximate functional equation.
Both require Aristotle-level analytic number theory.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace MockHardyZ

/-- Mock Hardy Z function: Z(t) = t. Models growth behavior only. -/
noncomputable def hardyZ (t : ℝ) : ℝ := t

/-- Mean square lower bound for mock Z(t) = t.
    Real version needs approximate functional equation. -/
theorem mean_square_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
      c * T * Real.log T ≤ ∫ t in Set.Ioc 1 T, (hardyZ t)^2 := by
        refine' ⟨ 1 / 4, _, 8, _, _ ⟩ <;> norm_num;
        intro T hT
        simp [hardyZ];
        rw [ ← intervalIntegral.integral_of_le ( by linarith ) ] ; norm_num ; ring_nf;
        nlinarith [ sq_nonneg ( T - 2 ), Real.log_le_sub_one_of_pos ( by linarith : 0 < T ) ]

/-- L1 lower bound for mock Z(t) = t.
    Real version needs mean square + pointwise bound, or direct analytic argument. -/
theorem l1_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
      c * T ≤ ∫ t in Set.Ioc 1 T, |hardyZ t| := by
        use 1 / 4;
        norm_num [ hardyZ ];
        exact ⟨ 2, by norm_num, fun T hT => by rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => abs_of_nonneg <| by linarith [ ht.1 ] ] ; rw [ ← intervalIntegral.integral_of_le ] <;> norm_num <;> nlinarith ⟩

end MockHardyZ
