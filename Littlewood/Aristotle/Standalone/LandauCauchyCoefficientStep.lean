import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LandauCauchyCoefficientStep

open scoped BigOperators

/-- Coefficient norm at `1` for a complex formal multilinear series. -/
def coeffAtOne (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) : ℝ :=
  ‖p n (fun _ : Fin n => (1 : ℂ))‖

/--
Cauchy-coefficient bound extracted from a positive convergence radius.

For a one-variable complex formal power series `p`, if `r` is strictly below
the radius of convergence, then the coefficient functional at `1` satisfies
a geometric Cauchy bound `≤ C / r^n`.
-/
theorem coeff_eval_one_norm_le_div_pow_of_lt_radius
    (p : FormalMultilinearSeries ℂ ℂ ℂ) {r : NNReal}
    (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ‖p n (fun _ : Fin n => (1 : ℂ))‖ ≤ C / (r : ℝ) ^ n := by
  obtain ⟨C, hC, hCauchy⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hr0 hr
  refine ⟨C, hC, ?_⟩
  intro n
  calc
    ‖p n (fun _ : Fin n => (1 : ℂ))‖
      ≤ ‖p n‖ * ∏ _i : Fin n, ‖(1 : ℂ)‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖p n‖ := by simp
    _ ≤ C / (r : ℝ) ^ n := hCauchy n

/--
Summability consequence of the Cauchy coefficient bound.

If `0 ≤ w < r`, then `∑ ‖pₙ(1,…,1)‖ w^n` is summable by comparison with the
geometric series in ratio `w / r`.
-/
theorem summable_coeff_eval_one_mul_pow_of_lt_radius
    (p : FormalMultilinearSeries ℂ ℂ ℂ) {r : NNReal}
    (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (w : ℝ) (hw_nonneg : 0 ≤ w) (hw_lt : w < (r : ℝ)) :
    Summable (fun n : ℕ => ‖p n (fun _ : Fin n => (1 : ℂ))‖ * w ^ n) := by
  obtain ⟨C, hC, hcoeff⟩ := coeff_eval_one_norm_le_div_pow_of_lt_radius p hr0 hr
  let q : ℝ := w / r
  have hr0_real : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hq_nonneg : 0 ≤ q := by
    exact div_nonneg hw_nonneg hr0_real.le
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact (div_lt_one hr0_real).2 hw_lt

  have hgeom : Summable (fun n : ℕ => C * q ^ n) :=
    (summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left C

  have hterm_nonneg :
      ∀ n : ℕ, 0 ≤ ‖p n (fun _ : Fin n => (1 : ℂ))‖ * w ^ n := by
    intro n
    exact mul_nonneg (norm_nonneg _) (pow_nonneg hw_nonneg _)

  have hterm_le :
      ∀ n : ℕ, ‖p n (fun _ : Fin n => (1 : ℂ))‖ * w ^ n ≤ C * q ^ n := by
    intro n
    have hw_pow_nonneg : 0 ≤ w ^ n := pow_nonneg hw_nonneg _
    have hmul := mul_le_mul_of_nonneg_right (hcoeff n) hw_pow_nonneg
    -- Rewrite `(C / r^n) * w^n` as `C * (w/r)^n`.
    have hrewrite : (C / (r : ℝ) ^ n) * w ^ n = C * q ^ n := by
      dsimp [q]
      rw [div_pow]
      ring
    exact hmul.trans_eq hrewrite

  exact Summable.of_nonneg_of_le hterm_nonneg hterm_le hgeom

/--
Packaged Cauchy majorant data:
there is a positive constant `B` such that coefficient norms satisfy
`coeffAtOne p n ≤ B / r^n`, and therefore the weighted series with any
`0 ≤ w < r` is summable.
-/
theorem exists_cauchy_majorant_and_summable
    (p : FormalMultilinearSeries ℂ ℂ ℂ) {r : NNReal}
    (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (w : ℝ) (hw_nonneg : 0 ≤ w) (hw_lt : w < (r : ℝ)) :
    ∃ B : ℝ, 0 < B ∧
      (∀ n : ℕ, coeffAtOne p n ≤ B / (r : ℝ) ^ n) ∧
      Summable (fun n : ℕ => coeffAtOne p n * w ^ n) := by
  obtain ⟨B, hB, hcoeff⟩ := coeff_eval_one_norm_le_div_pow_of_lt_radius p hr0 hr
  refine ⟨B, hB, ?_, ?_⟩
  · intro n
    simpa [coeffAtOne] using hcoeff n
  · simpa [coeffAtOne] using
      summable_coeff_eval_one_mul_pow_of_lt_radius p hr0 hr w hw_nonneg hw_lt

end Aristotle.Standalone.LandauCauchyCoefficientStep
