import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LandauSigmaLessThanOneTonelliTaylor

open MeasureTheory Set

/--
Tonelli/Fubini transfer step for Landau's `σ₀ < 1` branch.

For each cutoff `N`, suppose Tonelli/Fubini gives a nonnegative Taylor anti-coefficient
expansion
`I_N ≤ ∑' k, A N k * w^k`, and assume `A N k ≤ a k` for a global coefficient family.
Then the same partial integral is majorized by the global Taylor majorant
`∑' k, a k * w^k`.
-/
theorem tonelli_taylor_majorant_of_anticoeff_domination
    (g : ℝ → ℝ) (T₀ σ₀ w : ℝ)
    (A : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (hw_nonneg : 0 ≤ w)
    (hA_nonneg : ∀ N k : ℕ, 0 ≤ A N k)
    (hA_dom : ∀ N k : ℕ, A N k ≤ a k)
    (ha_summable : Summable (fun k : ℕ => a k * w ^ k))
    (h_tonelli :
      ∀ N : ℕ,
        ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖
          ≤ ∑' k : ℕ, A N k * w ^ k) :
    ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖
        ≤ ∑' k : ℕ, a k * w ^ k := by
  intro N
  have hAterm_nonneg : ∀ k : ℕ, 0 ≤ A N k * w ^ k := by
    intro k
    exact mul_nonneg (hA_nonneg N k) (pow_nonneg hw_nonneg _)
  have hAterm_le : ∀ k : ℕ, A N k * w ^ k ≤ a k * w ^ k := by
    intro k
    exact mul_le_mul_of_nonneg_right (hA_dom N k) (pow_nonneg hw_nonneg _)
  have hA_summable : Summable (fun k : ℕ => A N k * w ^ k) :=
    Summable.of_nonneg_of_le hAterm_nonneg hAterm_le ha_summable
  have htsum_le :
      (∑' k : ℕ, A N k * w ^ k) ≤ (∑' k : ℕ, a k * w ^ k) :=
    Summable.tsum_le_tsum hAterm_le hA_summable ha_summable
  exact (h_tonelli N).trans htsum_le

/--
Landau `σ₀ < 1` bounded-partial-integrals theorem from:
1) Tonelli/Fubini anti-coefficient expansion,
2) nonnegativity of anti-coefficients,
3) Cauchy coefficient majorant at center `2`.

Assumptions encode the classical chain:
`I_N ≤ ∑ A_{N,k}(2-σ₀)^k`, `A_{N,k} ≤ a_k`, `a_k ≤ B/(2-α)^k`.
Since `α < σ₀ < 1`, the ratio `(2-σ₀)/(2-α)` is in `[0,1)`, so the right-hand
side is uniformly bounded by a geometric series.
-/
theorem partial_integrals_bounded_of_tonelli_fubini_cauchy_majorant
    (g : ℝ → ℝ) (T₀ α σ₀ B : ℝ)
    (hσ₀ : α < σ₀) (hσ₀_lt1 : σ₀ < 1)
    (hB_nonneg : 0 ≤ B)
    (A : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (hA_nonneg : ∀ N k : ℕ, 0 ≤ A N k)
    (hA_dom : ∀ N k : ℕ, A N k ≤ a k)
    (ha_nonneg : ∀ k : ℕ, 0 ≤ a k)
    (ha_cauchy : ∀ k : ℕ, a k ≤ B / (2 - α) ^ k)
    (h_tonelli :
      ∀ N : ℕ,
        ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖
          ≤ ∑' k : ℕ, A N k * (2 - σ₀) ^ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖ ≤ M := by
  let R : ℝ := 2 - α
  let w : ℝ := 2 - σ₀
  let q : ℝ := w / R
  have hR_pos : 0 < R := by
    dsimp [R]
    linarith
  have hw_nonneg : 0 ≤ w := by
    dsimp [w]
    linarith
  have hw_lt_R : w < R := by
    dsimp [w, R]
    linarith
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hw_nonneg hR_pos.le
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact (div_lt_one hR_pos).2 hw_lt_R

  have hgeom_summable : Summable (fun k : ℕ => B * q ^ k) :=
    (summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left B

  have ha_term_le_geom : ∀ k : ℕ, a k * w ^ k ≤ B * q ^ k := by
    intro k
    have hpow_nonneg : 0 ≤ w ^ k := pow_nonneg hw_nonneg _
    have hmul :
        a k * w ^ k ≤ (B / R ^ k) * w ^ k :=
      mul_le_mul_of_nonneg_right (ha_cauchy k) hpow_nonneg
    have hrewrite : (B / R ^ k) * w ^ k = B * q ^ k := by
      calc
        (B / R ^ k) * w ^ k = B * (w ^ k / R ^ k) := by ring
        _ = B * (w / R) ^ k := by rw [div_pow]
        _ = B * q ^ k := by simp [q]
    exact hmul.trans_eq hrewrite

  have ha_term_nonneg : ∀ k : ℕ, 0 ≤ a k * w ^ k := by
    intro k
    exact mul_nonneg (ha_nonneg k) (pow_nonneg hw_nonneg _)

  have ha_summable : Summable (fun k : ℕ => a k * w ^ k) :=
    Summable.of_nonneg_of_le ha_term_nonneg ha_term_le_geom hgeom_summable

  have htonelli_majorant :
      ∀ N : ℕ,
        ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖
          ≤ ∑' k : ℕ, a k * w ^ k := by
    refine tonelli_taylor_majorant_of_anticoeff_domination g T₀ σ₀ w A a
      hw_nonneg hA_nonneg hA_dom ha_summable ?_
    intro N
    simpa [w] using h_tonelli N

  have htsum_le_geom :
      (∑' k : ℕ, a k * w ^ k) ≤ (∑' k : ℕ, B * q ^ k) :=
    Summable.tsum_le_tsum ha_term_le_geom ha_summable hgeom_summable

  let M : ℝ := B * (1 - q)⁻¹
  have hM_nonneg : 0 ≤ M := by
    have h_one_sub_nonneg : 0 ≤ 1 - q := by linarith [le_of_lt hq_lt_one]
    dsimp [M]
    exact mul_nonneg hB_nonneg (inv_nonneg.mpr h_one_sub_nonneg)

  have hgeom_eval : (∑' k : ℕ, B * q ^ k) = M := by
    dsimp [M]
    rw [tsum_mul_left]
    simp [tsum_geometric_of_lt_one hq_nonneg hq_lt_one]

  refine ⟨M, hM_nonneg, ?_⟩
  intro N
  calc
    ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖
      ≤ ∑' k : ℕ, a k * w ^ k := htonelli_majorant N
    _ ≤ ∑' k : ℕ, B * q ^ k := htsum_le_geom
    _ = M := hgeom_eval

end Aristotle.Standalone.LandauSigmaLessThanOneTonelliTaylor
