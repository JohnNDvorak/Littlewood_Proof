/-
Copyright (c) 2026 Littlewood Proof Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Littlewood.Aristotle.Standalone.HadamardLiouvilleArgument

/-!
# Hadamard Phase 4.5b: Subquadratic growth ⟹ linear

Generalizes the Liouville-type argument from `HadamardLiouvilleArgument.lean`.

If `g : ℂ → ℂ` is entire and satisfies `‖g s‖ ≤ C · (‖s‖ + 1)^α` for some
`0 ≤ α < 2`, then `g` is a polynomial of degree at most 1, i.e., `g(s) = A + B · s`.

The proof reuses `cauchy_second_deriv_bound` and `entire_second_deriv_zero_imp_linear`
from the original file. The only new ingredient is showing that the Cauchy bound
`C · (R + a)^α / R²` tends to 0 as `R → ∞` when `α < 2`.

## Application
With `α = 3/2`, this applies to the Hadamard factorization: the logarithm of
`ξ(s)/P(s)` grows like `|s|^{3/2}`, hence is linear.

Co-authored-by: Claude (Anthropic)
-/

set_option maxHeartbeats 3200000

noncomputable section

open Complex Metric Filter Set Function Topology Asymptotics Real

/-- Subquadratic growth: `‖g s‖ ≤ C · (‖s‖ + 1)^α` for all `s`. -/
def SubquadraticGrowth (g : ℂ → ℂ) (α C : ℝ) : Prop :=
  ∀ s : ℂ, ‖g s‖ ≤ C * (‖s‖ + 1) ^ α

/-! ## Key lemma: `(R + a)^α / R² → 0` when `0 ≤ α < 2` -/

/-- Auxiliary: `(R + a)^α / R² → 0` as `R → ∞`, for `0 ≤ α < 2` and `a ≥ 0`.
Here `R²` is the ℕ-power `R ^ (2 : ℕ)`.

Proof: bound `(R+a)^α ≤ (2R)^α = 2^α · R^α` for `R ≥ a`. Then
`(R+a)^α / R^2 ≤ 2^α · R^{-(2-α)} → 0`. -/
private theorem tendsto_rpow_alpha_div_sq (a : ℝ) (_ha : 0 ≤ a) (α : ℝ) (hα : α < 2)
    (hα_nn : 0 ≤ α) :
    Filter.Tendsto (fun R : ℝ => (R + a) ^ α / R ^ (2 : ℕ))
      atTop (nhds 0) := by
  have h2α : 0 < 2 - α := by linarith
  -- R^(-(2-α)) → 0
  have h_neg_rpow : Tendsto (fun R : ℝ => R ^ (-(2 - α))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop h2α
  -- 2^α · R^(-(2-α)) → 0
  have h_scaled : Tendsto (fun R : ℝ => 2 ^ α * R ^ (-(2 - α))) atTop (nhds 0) := by
    rw [show (0 : ℝ) = 2 ^ α * 0 from (mul_zero _).symm]
    exact tendsto_const_nhds.mul h_neg_rpow
  -- Squeeze between 0 and 2^α · R^(-(2-α))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_scaled
  · -- Lower bound: 0 ≤ ratio (eventually, for R ≥ 1)
    filter_upwards [Filter.eventually_ge_atTop 1] with R hR
    exact div_nonneg (rpow_nonneg (by linarith) α) (pow_nonneg (by linarith) 2)
  · -- Upper bound: (R+a)^α / R^2 ≤ 2^α · R^(-(2-α)), eventually for R ≥ max a 1
    filter_upwards [Filter.eventually_ge_atTop (max a 1)] with R hR
    have hR_ge_a : a ≤ R := le_of_max_le_left hR
    have hR_pos : 0 < R := lt_of_lt_of_le one_pos (le_of_max_le_right hR)
    -- (R + a) ≤ 2R
    have h2R : R + a ≤ 2 * R := by linarith
    -- (R + a)^α ≤ (2R)^α since α ≥ 0
    have hrpow : (R + a) ^ α ≤ (2 * R) ^ α :=
      rpow_le_rpow (by linarith) h2R hα_nn
    rw [mul_rpow (by norm_num : (0:ℝ) ≤ 2) hR_pos.le] at hrpow
    -- Key: R^α / R^(2:ℕ) = R^(-(2-α))
    -- We have R^(2:ℕ) = R * R for R : ℝ
    -- R^α / (R * R) = R^α * R^(-1) * R^(-1) = R^(α - 2) = R^(-(2-α))
    -- Key: R^α / R^2 = R^(-(2-α))
    -- R^(2:ℕ) and R^(2:ℝ) are the same by rpow_natCast
    have hR_ne : R ≠ 0 := ne_of_gt hR_pos
    -- Convert ℕ-pow to ℝ-pow for the calc
    have hR2_eq : (R ^ (2 : ℕ) : ℝ) = R ^ (2 : ℝ) := (rpow_natCast R 2).symm
    calc (R + a) ^ α / R ^ (2 : ℕ)
        ≤ 2 ^ α * R ^ α / R ^ (2 : ℕ) :=
          div_le_div_of_nonneg_right hrpow (pow_nonneg hR_pos.le 2)
      _ = 2 ^ α * R ^ α / R ^ (2 : ℝ) := by rw [← hR2_eq]
      _ = 2 ^ α * (R ^ α / R ^ (2 : ℝ)) := mul_div_assoc _ _ _
      _ = 2 ^ α * R ^ (α - 2) := by
          congr 1; rw [← rpow_sub hR_pos]
      _ = 2 ^ α * R ^ (-(2 - α)) := by ring_nf

/-- Growth bound for `g` on a circle of radius `R` centered at `s`, under
subquadratic growth. -/
theorem subquadratic_growth_on_circle (g : ℂ → ℂ) (α C : ℝ) (hC : 0 < C)
    (hα : 0 ≤ α) (hgrowth : SubquadraticGrowth g α C)
    (s : ℂ) (R : ℝ) (_hR : 1 ≤ R) :
    ∀ z ∈ sphere s R, ‖g z‖ ≤ C * (R + ‖s‖ + 1) ^ α := by
  intro z hz
  rw [mem_sphere_iff_norm] at hz
  have hzn : ‖z‖ ≤ R + ‖s‖ := by
    calc ‖z‖ = ‖(z - s) + s‖ := by ring_nf
    _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
    _ = R + ‖s‖ := by rw [hz]
  have h1 : ‖z‖ + 1 ≤ R + ‖s‖ + 1 := by linarith
  calc ‖g z‖ ≤ C * (‖z‖ + 1) ^ α := hgrowth z
    _ ≤ C * (R + ‖s‖ + 1) ^ α := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact rpow_le_rpow (by positivity) h1 hα

/-- For any entire function with subquadratic growth (0 ≤ α < 2), `g''(s) = 0`. -/
theorem subquadratic_second_deriv_vanishes (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (α C : ℝ) (hα : α < 2) (hα_nn : 0 ≤ α) (hC : 0 < C)
    (hgrowth : SubquadraticGrowth g α C) (s : ℂ) :
    iteratedDeriv 2 g s = 0 := by
  rw [← norm_le_zero_iff]
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  have htends := tendsto_rpow_alpha_div_sq (‖s‖ + 1) (by positivity) α hα hα_nn
  rw [Metric.tendsto_atTop] at htends
  obtain ⟨R₀, hR₀⟩ := htends (ε / (2 * C)) (by positivity)
  set R := max R₀ 1 with hR_def
  have hR_pos : 0 < R := by positivity
  have hR_ge : 1 ≤ R := le_max_right _ _
  have hR_ge₀ : R₀ ≤ R := le_max_left _ _
  have hcirc := subquadratic_growth_on_circle g α C hC hα_nn hgrowth s R hR_ge
  have hcauchy := cauchy_second_deriv_bound g hg s R hR_pos
      (C * (R + ‖s‖ + 1) ^ α) hcirc
  have hsmall := hR₀ R hR_ge₀
  rw [Real.dist_eq] at hsmall
  simp only [sub_zero] at hsmall
  have hval_nn : 0 ≤ (R + (‖s‖ + 1)) ^ α / R ^ (2 : ℕ) :=
    div_nonneg (rpow_nonneg (by linarith [norm_nonneg s]) α) (pow_nonneg hR_pos.le 2)
  rw [abs_of_nonneg hval_nn] at hsmall
  have hRsa : R + ‖s‖ + 1 = R + (‖s‖ + 1) := by ring
  rw [hRsa] at hcauchy
  have hlt : 2 * (C * (R + (‖s‖ + 1)) ^ α) / R ^ 2 < ε := by
    calc 2 * (C * (R + (‖s‖ + 1)) ^ α) / R ^ 2
        = 2 * C * ((R + (‖s‖ + 1)) ^ α / R ^ 2) := by ring
      _ < 2 * C * (ε / (2 * C)) := by
          apply mul_lt_mul_of_pos_left _ (by positivity)
          exact hsmall
      _ = ε := by field_simp
  linarith [hcauchy]

/-- **Subquadratic Liouville theorem**: An entire function with `‖g s‖ ≤ C(‖s‖+1)^α`
    for `0 ≤ α < 2` is affine-linear. -/
theorem subquadratic_growth_imp_linear (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (α C : ℝ) (hα : α < 2) (hα_nn : 0 ≤ α) (hC : 0 < C)
    (hgrowth : SubquadraticGrowth g α C) :
    ∃ A B : ℂ, ∀ s, g s = A + B * s :=
  entire_second_deriv_zero_imp_linear g hg
    (fun s => subquadratic_second_deriv_vanishes g hg α C hα hα_nn hC hgrowth s)

end
