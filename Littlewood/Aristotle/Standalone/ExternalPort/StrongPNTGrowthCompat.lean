import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTGrowthCompat

open scoped Real
open Filter

/-- External-port adaptation of the strongpnt growth auxiliary (`IBound_aux1`):
for any `k` and any positive threshold `X₀`, there is a uniform linear majorant
for `(log X)^k` on `[X₀, ∞)`. -/
theorem log_pow_nat_le_const_mul_port
    (X₀ : ℝ) (hX₀ : 0 < X₀) (k : ℕ) :
    ∃ C ≥ (1 : ℝ), ∀ X : ℝ, X ≥ X₀ → Real.log X ^ k ≤ C * X := by
  have ⟨M, hM⟩ :=
    Filter.eventually_atTop.mp
      (isLittleO_log_rpow_rpow_atTop k zero_lt_one).eventuallyLE
  let f : ℝ → ℝ := fun X => Real.log X ^ k / X
  let I1 : Set ℝ := Set.Icc X₀ M
  have h0_not_mem : (0 : ℝ) ∉ I1 := by
    exact Set.notMem_Icc_of_lt hX₀
  have hf_cont : ContinuousOn f I1 := by
    refine
      ((Real.continuousOn_log.pow k).mono (Set.subset_compl_singleton_iff.mpr h0_not_mem)).div
        continuous_id.continuousOn ?_
    intro x hx
    exact ne_of_mem_of_not_mem hx h0_not_mem
  have ⟨C₁, hC₁⟩ := (isCompact_Icc.exists_bound_of_continuousOn hf_cont)
  refine ⟨max C₁ 1, le_max_right C₁ 1, ?_⟩
  intro X hX
  have hX_pos : 0 < X := lt_of_lt_of_le hX₀ hX
  by_cases hXM : X ≤ M
  · rw [← div_le_iff₀ hX_pos]
    calc
      f X ≤ ‖f X‖ := le_abs_self _
      _ ≤ C₁ := hC₁ X ⟨hX, hXM⟩
      _ ≤ max C₁ 1 := le_max_left C₁ 1
  · calc
      Real.log X ^ k ≤ ‖Real.log X ^ k‖ := le_abs_self _
      _ ≤ ‖X ^ (1 : ℕ)‖ := by
            exact_mod_cast hM X (by linarith [hXM])
      _ = 1 * X := by
        rw [pow_one, one_mul]
        exact abs_of_nonneg hX_pos.le
      _ ≤ max C₁ 1 * X := by
        exact mul_le_mul_of_nonneg_right (le_max_right C₁ 1) hX_pos.le

/-- Corollary form convenient for downstream endpoint rewrites. -/
theorem log_pow_nat_eventually_linear_port (k : ℕ) :
    ∃ C : ℝ, ∀ᶠ X in atTop, Real.log X ^ k ≤ C * X := by
  rcases log_pow_nat_le_const_mul_port 1 zero_lt_one k with ⟨C, hC, hCbound⟩
  refine ⟨C, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with X hX
  exact hCbound X hX

end Aristotle.Standalone.ExternalPort.StrongPNTGrowthCompat
