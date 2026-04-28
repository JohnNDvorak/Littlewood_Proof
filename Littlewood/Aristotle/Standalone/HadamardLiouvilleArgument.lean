/-
Copyright (c) 2026 Littlewood Proof Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Hadamard Factorization Phase 4.5: Liouville-type argument

If an entire function `g : ℂ → ℂ` satisfies a sublinear-logarithmic growth bound
`|g(s)| ≤ C · (|s| + 1) · (log(|s| + 1) + 1)`, then `g` is a polynomial of degree at most 1,
i.e., `g(s) = A + B · s` for some constants `A, B : ℂ`.

## Proof sketch

1. **Cauchy estimate**: For the 2nd derivative at center `c` on a disc of radius `R`,
   `‖iteratedDeriv 2 g c‖ ≤ 2! · max|g| / R²` (Mathlib: `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`).
2. **Growth on circles**: Triangle inequality gives `max|g|` on `{z : ‖z - s‖ = R}`
   is at most `C · (R + ‖s‖ + 1) · (log(R + ‖s‖ + 1) + 1)`.
3. **Send R → ∞**: The ratio `(R + a) · log(R + a) / R²` tends to 0, so `g''(s) = 0`.
4. **g'' ≡ 0 implies g linear**: `g'` has derivative 0 everywhere, hence constant by
   `is_const_of_deriv_eq_zero`. Then `g(s) = g(0) + g'(0) · s`.
-/

noncomputable section

open Complex Metric Filter Set Function Topology Asymptotics

/-- The growth hypothesis: `‖g s‖ ≤ C · (‖s‖ + 1) · (log(‖s‖ + 1) + 1)` for all `s`. -/
def SublinearLogGrowth (g : ℂ → ℂ) (C : ℝ) : Prop :=
  ∀ s : ℂ, ‖g s‖ ≤ C * (‖s‖ + 1) * (Real.log (‖s‖ + 1) + 1)

/-! ## Step 1: Cauchy bound on 2nd derivative

This is a direct application of Mathlib's `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`.
-/

/-- Cauchy's estimate for the 2nd derivative of an entire function at center `c`. -/
theorem cauchy_second_deriv_bound (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (c : ℂ) (R : ℝ) (hR : 0 < R) (M : ℝ)
    (hM : ∀ z ∈ sphere c R, ‖g z‖ ≤ M) :
    ‖iteratedDeriv 2 g c‖ ≤ 2 * M / R ^ 2 := by
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR
    hg.diffContOnCl hM
  simp [Nat.factorial] at this
  linarith

/-! ## Step 2: Growth bound on circles

For `z` with `‖z - s‖ = R`, we have `‖z‖ ≤ R + ‖s‖`, so the growth bound gives
`‖g z‖ ≤ C · (R + ‖s‖ + 1) · (log(R + ‖s‖ + 1) + 1)`.
-/

/-- Growth bound for `g` on a circle of radius `R` centered at `s`. -/
theorem growth_on_circle (g : ℂ → ℂ) (C : ℝ) (hC : 0 < C)
    (hgrowth : SublinearLogGrowth g C)
    (s : ℂ) (R : ℝ) (_hR : 1 ≤ R) :
    ∀ z ∈ sphere s R, ‖g z‖ ≤
      C * (R + ‖s‖ + 1) * (Real.log (R + ‖s‖ + 1) + 1) := by
  intro z hz
  rw [mem_sphere_iff_norm] at hz
  have hzn : ‖z‖ ≤ R + ‖s‖ := by
    calc ‖z‖ = ‖(z - s) + s‖ := by ring_nf
    _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
    _ = R + ‖s‖ := by rw [hz]
  have h1 : ‖z‖ + 1 ≤ R + ‖s‖ + 1 := by linarith
  have h2 : 0 < ‖z‖ + 1 := by positivity
  have hlog : Real.log (‖z‖ + 1) + 1 ≤ Real.log (R + ‖s‖ + 1) + 1 := by
    linarith [Real.log_le_log h2 h1]
  calc ‖g z‖ ≤ C * (‖z‖ + 1) * (Real.log (‖z‖ + 1) + 1) := hgrowth z
    _ ≤ C * (R + ‖s‖ + 1) * (Real.log (R + ‖s‖ + 1) + 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hC.le) hlog
          (by linarith [Real.log_nonneg (by linarith [norm_nonneg z] : 1 ≤ ‖z‖ + 1)])
          (mul_nonneg hC.le (by linarith))

/-! ## Step 3: Second derivative vanishes

Combine the Cauchy bound with the growth estimate. For fixed `s`, the bound
`2 · C · (R + ‖s‖ + 1) · (log(R + ‖s‖ + 1) + 1) / R²` tends to 0 as `R → ∞`.
-/

/-- Auxiliary: `(R + a) * (log(R + a) + 1) / R ^ 2 → 0` as `R → ∞`, for fixed `a ≥ 0`. -/
private theorem tendsto_growth_div_sq (a : ℝ) (ha : 0 ≤ a) :
    Filter.Tendsto (fun R : ℝ => (R + a) * (Real.log (R + a) + 1) / R ^ 2)
      atTop (nhds 0) := by
  -- Decompose: f(R) = [(R+a)/R] * [log(R+a)/R + 1/R]
  have heq : (fun R : ℝ => (R + a) * (Real.log (R + a) + 1) / R ^ 2)
      =ᶠ[atTop] (fun R => (R + a) / R * (Real.log (R + a) / R + 1 / R)) := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    field_simp
  -- (R+a)/R → 1
  have h_ratio : Tendsto (fun R : ℝ => (R + a) / R) atTop (nhds 1) := by
    have : (fun R : ℝ => 1 + a / R) =ᶠ[atTop] (fun R => (R + a) / R) := by
      filter_upwards [eventually_gt_atTop 0] with R hR; field_simp
    exact (show Tendsto (fun R : ℝ => 1 + a / R) atTop (nhds 1) from by
      conv => rhs; rw [show (1 : ℝ) = 1 + 0 from (add_zero 1).symm]
      exact tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).congr' this
  -- log(R+a)/(R+a) → 0 by composition with log(x)/x → 0
  have h_log_self : Tendsto (fun R : ℝ => Real.log (R + a) / (R + a)) atTop (nhds 0) := by
    have hlogR : Tendsto (fun R : ℝ => Real.log R / R) atTop (nhds 0) := by
      have h := isLittleO_log_rpow_atTop one_pos
      simp only [Real.rpow_one] at h; exact h.tendsto_div_nhds_zero
    exact hlogR.comp (tendsto_atTop_add_const_right _ a tendsto_id)
  -- log(R+a)/R → 0: factor as [log(R+a)/(R+a)] * [(R+a)/R] → 0 * 1 = 0
  have h_log_R : Tendsto (fun R : ℝ => Real.log (R + a) / R) atTop (nhds 0) := by
    have hev : (fun R : ℝ => Real.log (R + a) / R) =ᶠ[atTop]
        (fun R => Real.log (R + a) / (R + a) * ((R + a) / R)) := by
      filter_upwards [eventually_gt_atTop 0] with R hR
      have hRa : R + a ≠ 0 := by linarith
      field_simp
    rw [show (0 : ℝ) = 0 * 1 from (zero_mul 1).symm]
    exact (h_log_self.mul h_ratio).congr' hev.symm
  -- 1/R → 0
  have h_inv : Tendsto (fun R : ℝ => 1 / R) atTop (nhds 0) := by
    simp_rw [one_div]; exact tendsto_inv_atTop_zero
  -- log(R+a)/R + 1/R → 0 + 0 = 0
  have h_sum : Tendsto (fun R : ℝ => Real.log (R + a) / R + 1 / R) atTop (nhds 0) := by
    rw [show (0 : ℝ) = 0 + 0 from (add_zero 0).symm]
    exact h_log_R.add h_inv
  -- Product: (R+a)/R * (log(R+a)/R + 1/R) → 1 * 0 = 0
  have h_prod : Tendsto (fun R : ℝ => (R + a) / R *
      (Real.log (R + a) / R + 1 / R)) atTop (nhds 0) := by
    rw [show (0 : ℝ) = 1 * 0 from (mul_zero 1).symm]
    exact h_ratio.mul h_sum
  exact h_prod.congr' heq.symm

/-- For any entire function with sublinear-log growth, `g''(s) = 0` for all `s`. -/
theorem second_deriv_vanishes (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (C : ℝ) (hC : 0 < C) (hgrowth : SublinearLogGrowth g C) (s : ℂ) :
    iteratedDeriv 2 g s = 0 := by
  rw [← norm_le_zero_iff]
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  -- The function (R + a) * (log(R + a) + 1) / R^2 → 0
  have htends := tendsto_growth_div_sq (‖s‖ + 1) (by positivity)
  rw [Metric.tendsto_atTop] at htends
  obtain ⟨R₀, hR₀⟩ := htends (ε / (2 * C)) (by positivity)
  set R := max R₀ 1 with hR_def
  have hR_pos : 0 < R := by positivity
  have hR_ge : 1 ≤ R := le_max_right _ _
  have hR_ge₀ : R₀ ≤ R := le_max_left _ _
  -- Circle growth bound (in terms of R + ‖s‖ + 1)
  have hcirc := growth_on_circle g C hC hgrowth s R hR_ge
  have hcauchy := cauchy_second_deriv_bound g hg s R hR_pos
      (C * (R + ‖s‖ + 1) * (Real.log (R + ‖s‖ + 1) + 1)) hcirc
  -- Get the tendsto bound
  have hsmall := hR₀ R hR_ge₀
  rw [Real.dist_eq] at hsmall
  simp only [sub_zero] at hsmall
  have hval_nn : 0 ≤ (R + (‖s‖ + 1)) * (Real.log (R + (‖s‖ + 1)) + 1) / R ^ 2 := by
    apply div_nonneg
    · apply mul_nonneg
      · linarith [norm_nonneg s]
      · linarith [Real.log_nonneg (by linarith [norm_nonneg s] : 1 ≤ R + (‖s‖ + 1))]
    · positivity
  rw [abs_of_nonneg hval_nn] at hsmall
  -- Now combine: ‖g''(s)‖ ≤ 2 * M / R^2 < ε
  have hRsa : R + ‖s‖ + 1 = R + (‖s‖ + 1) := by ring
  rw [hRsa] at hcauchy
  have hlt : 2 * (C * (R + (‖s‖ + 1)) * (Real.log (R + (‖s‖ + 1)) + 1)) / R ^ 2 < ε := by
    calc 2 * (C * (R + (‖s‖ + 1)) * (Real.log (R + (‖s‖ + 1)) + 1)) / R ^ 2
        = 2 * C * ((R + (‖s‖ + 1)) * (Real.log (R + (‖s‖ + 1)) + 1) / R ^ 2) := by ring
      _ < 2 * C * (ε / (2 * C)) := mul_lt_mul_of_pos_left hsmall (by positivity)
      _ = ε := by field_simp
  linarith [hcauchy]

/-! ## Step 4: g'' = 0 everywhere implies g is linear

If `g'' ≡ 0` and `g` is entire, then `g' ≡ g'(0)` (constant), and
`g(s) = g(0) + g'(0) · s`.
-/

/-- If an entire function has second derivative identically zero, it is affine-linear. -/
theorem entire_second_deriv_zero_imp_linear (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (h_dd : ∀ s, iteratedDeriv 2 g s = 0) :
    ∃ A B : ℂ, ∀ s, g s = A + B * s := by
  -- Extract: iteratedDeriv 2 g = deriv (deriv g) via iteratedDeriv_succ
  have hderiv2 : ∀ x, deriv (deriv g) x = 0 := by
    intro x
    have h := h_dd x
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
    exact h
  -- g' is differentiable (complex entire ⟹ C^∞)
  have hg' : Differentiable ℂ (deriv g) :=
    (hg.contDiff (n := 2)).differentiable_deriv_two
  -- g' is constant
  have hg'_const : ∀ s, deriv g s = deriv g 0 :=
    fun s => is_const_of_deriv_eq_zero hg' hderiv2 s 0
  -- Set up constants
  set B := deriv g 0
  set A := g 0
  -- h(s) = g(s) - A - B * s has derivative 0
  have hd_sub : Differentiable ℂ (fun s => g s - A - B * s) :=
    (hg.sub (differentiable_const A)).sub ((differentiable_const B).mul differentiable_id)
  have hd_zero : ∀ s, deriv (fun s => g s - A - B * s) s = 0 := by
    intro s
    have : HasDerivAt (fun s => g s - A - B * s) (deriv g s - 0 - B) s := by
      apply HasDerivAt.sub
      · exact (hg.differentiableAt.hasDerivAt).sub (hasDerivAt_const s A)
      · exact hasDerivAt_const_mul B
    rw [this.deriv, sub_zero, hg'_const s, sub_self]
  -- h is identically h(0) = 0
  have hconst : ∀ s, g s - A - B * s = g 0 - A - B * 0 :=
    fun s => is_const_of_deriv_eq_zero hd_sub hd_zero s 0
  refine ⟨A, B, fun s => ?_⟩
  have h := hconst s
  -- RHS: g 0 - A - B * 0 = g 0 - g 0 - 0 = 0
  -- so g s - A - B * s = 0, i.e., g s = A + B * s
  linear_combination h

/-! ## Main theorem -/

/-- **Hadamard Phase 4.5**: An entire function with sublinear-logarithmic growth is linear. -/
theorem sublinear_log_growth_imp_linear (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (C : ℝ) (hC : 0 < C) (hgrowth : SublinearLogGrowth g C) :
    ∃ A B : ℂ, ∀ s, g s = A + B * s :=
  entire_second_deriv_zero_imp_linear g hg
    (fun s => second_deriv_vanishes g hg C hC hgrowth s)

end
