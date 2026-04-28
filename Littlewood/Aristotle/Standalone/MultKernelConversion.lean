/-
# Mult-weighted kernel conversion for Littlewood explicit formula

Ported from Aristotle job 72860394 (0 sorry, 102 lines).

Proves the per-term and aggregate kernel conversion bound:
  |Σ m(ρ)·e^{η/2}·[exact term] - e^{η/2}·Σ m(ρ)·sin(γη)/γ|
  ≤ (e^{η/2}/2)·Σ m(ρ)/γ²

This is step 2 of 3 in the mult→Abel bridge.

Co-authored-by: Aristotle (Harmonic)
Co-authored-by: Claude (Anthropic)
-/

import Mathlib

open Real Finset BigOperators

noncomputable section

namespace Littlewood.Classical.MultKernelConversion

/-- |a cos θ + b sin θ| ≤ √(a² + b²). -/
lemma abs_add_mul_cos_sin_le (a b θ : ℝ) :
    |a * Real.cos θ + b * Real.sin θ| ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (a * Real.sin θ - b * Real.cos θ),
    Real.sin_sq_add_cos_sq θ]

/-- Per-term algebraic identity for the kernel difference. -/
lemma kernel_diff_identity (γ η : ℝ) (hγ : γ ≠ 0) :
    (Real.cos (γ * η) / 2 + γ * Real.sin (γ * η)) / (1 / 4 + γ ^ 2) -
    Real.sin (γ * η) / γ =
    (γ / 2 * Real.cos (γ * η) + (-(1 : ℝ) / 4) * Real.sin (γ * η)) /
    (γ * (1 / 4 + γ ^ 2)) := by
  field_simp
  ring

/-- √(γ²/4 + 1/16) ≤ (1/4+γ²)/(2γ) for γ > 0. -/
lemma sqrt_coeff_le (γ : ℝ) (hγ : 0 < γ) :
    Real.sqrt ((γ / 2) ^ 2 + (1 / 4) ^ 2) ≤ (1 / 4 + γ ^ 2) / (2 * γ) := by
  rw [Real.sqrt_le_left] <;> try positivity
  field_simp
  nlinarith

/-- Per-term kernel bound: |exact_term - sin(γη)/γ| ≤ 1/(2γ²). -/
theorem per_term_kernel_bound (γ η : ℝ) (hγ : 0 < γ) :
    |(Real.cos (γ * η) / 2 + γ * Real.sin (γ * η)) / (1 / 4 + γ ^ 2) -
     Real.sin (γ * η) / γ| ≤ 1 / (2 * γ ^ 2) := by
  rw [kernel_diff_identity _ _ hγ.ne.symm]
  rw [abs_div]
  rw [abs_of_nonneg (by positivity : 0 ≤ γ * (1 / 4 + γ ^ 2)),
      div_le_div_iff₀ (by positivity) (by positivity)]
  exact le_trans (mul_le_mul_of_nonneg_right (abs_add_mul_cos_sin_le _ _ _) (by positivity))
    (by nlinarith [Real.sqrt_nonneg ((γ / 2) ^ 2 + (1 / 4) ^ 2),
        Real.mul_self_sqrt (by positivity : 0 ≤ (γ / 2) ^ 2 + (1 / 4) ^ 2),
        sqrt_coeff_le γ hγ,
        mul_div_cancel₀ (1 / 4 + γ ^ 2) (by positivity : (2 * γ) ≠ 0)])

/-- Aggregate mult-weighted kernel conversion bound. -/
theorem kernel_conversion {ι : Type*} (S : Finset ι)
    (m : ι → ℝ) (γ : ι → ℝ) (η : ℝ)
    (hm : ∀ i ∈ S, 0 ≤ m i)
    (hγ : ∀ i ∈ S, 0 < γ i) :
    |∑ i ∈ S, m i * (Real.exp (η / 2) *
      ((Real.cos (γ i * η) / 2 + γ i * Real.sin (γ i * η)) /
       (1 / 4 + (γ i) ^ 2))) -
     Real.exp (η / 2) * ∑ i ∈ S, m i * (Real.sin (γ i * η) / γ i)| ≤
    Real.exp (η / 2) / 2 * ∑ i ∈ S, m i / (γ i) ^ 2 := by
  simp_all +decide
  convert (Finset.abs_sum_le_sum_abs _ _) |> le_trans <|
    Finset.sum_le_sum fun i hi => ?_ using 1
  convert rfl using 2
  any_goals try infer_instance
  rotate_left; rotate_left
  use fun i => m i * Real.exp (η / 2) *
    ((Real.cos (γ i * η) / 2 + γ i * Real.sin (γ i * η)) /
     (4⁻¹ + γ i ^ 2) - Real.sin (γ i * η) / γ i)
  use fun i => m i * Real.exp (η / 2) * (1 / (2 * γ i ^ 2))
  exact S
  · rw [abs_mul, abs_of_nonneg (mul_nonneg (hm i hi) (Real.exp_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (by simpa using per_term_kernel_bound (γ i) η (hγ i hi))
      (mul_nonneg (hm i hi) (Real.exp_nonneg _))
  · simp +decide only [mul_sub, mul_assoc, sum_sub_distrib, Finset.mul_sum _ _ _, mul_left_comm]
  · rw [Finset.mul_sum _ _ _]
    exact Finset.sum_congr rfl fun _ _ => by ring

end Littlewood.Classical.MultKernelConversion
