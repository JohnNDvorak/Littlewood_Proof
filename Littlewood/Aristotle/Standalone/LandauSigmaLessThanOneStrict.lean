import Littlewood.Aristotle.PringsheimPsiAtom

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LandauSigmaLessThanOneStrict

open MeasureTheory Set

/--
Geometric majorant step for the hard `σ₀ < 1` Landau branch.

Assume the partial integral at exponent `-(σ₀+1)` is majorized by a nonnegative
Taylor series at center `2`, with coefficients satisfying the Cauchy bound
`aₖ ≤ B / (2-α)^k`. Since `α < σ₀ < 1`, the ratio
`(2-σ₀)/(2-α)` is in `[0,1)`, so the majorant series is geometric and gives a
uniform bound on all partial integrals.
-/
theorem partial_integrals_bounded_sigma_lt_one_of_taylor_majorant
    (C α σ_sign σ₀ T₀ B : ℝ)
    (hσ₀ : α < σ₀) (hσ₀_lt1 : σ₀ < 1)
    (hB_nonneg : 0 ≤ B)
    (a : ℕ → ℝ)
    (ha_nonneg : ∀ k : ℕ, 0 ≤ a k)
    (ha_cauchy : ∀ k : ℕ, a k ≤ B / (2 - α) ^ k)
    (h_taylor_majorant : ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)),
        ‖PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))‖
          ≤ ∑' k : ℕ, a k * (2 - σ₀) ^ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)),
        ‖PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))‖ ≤ M := by
  let q : ℝ := (2 - σ₀) / (2 - α)
  have hα_lt1 : α < 1 := by linarith
  have hden_pos : 0 < 2 - α := by linarith
  have hnum_nonneg : 0 ≤ 2 - σ₀ := by linarith
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hnum_nonneg hden_pos.le
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact (div_lt_one hden_pos).2 (by linarith [hσ₀])

  have hgeom_summable : Summable (fun k : ℕ => B * q ^ k) :=
    (summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left B

  have hterm_le : ∀ k : ℕ, a k * (2 - σ₀) ^ k ≤ B * q ^ k := by
    intro k
    have hk : a k ≤ B / (2 - α) ^ k := ha_cauchy k
    have hpow_nonneg : 0 ≤ (2 - σ₀) ^ k := pow_nonneg hnum_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hk hpow_nonneg
    have hrewrite : (B / (2 - α) ^ k) * (2 - σ₀) ^ k = B * q ^ k := by
      dsimp [q]
      rw [div_pow]
      ring
    exact hmul.trans_eq hrewrite

  have hleft_nonneg : ∀ k : ℕ, 0 ≤ a k * (2 - σ₀) ^ k := by
    intro k
    exact mul_nonneg (ha_nonneg k) (pow_nonneg hnum_nonneg _)

  have hleft_summable : Summable (fun k : ℕ => a k * (2 - σ₀) ^ k) :=
    Summable.of_nonneg_of_le hleft_nonneg hterm_le hgeom_summable

  have htsum_le :
      (∑' k : ℕ, a k * (2 - σ₀) ^ k) ≤ (∑' k : ℕ, B * q ^ k) :=
    Summable.tsum_le_tsum hterm_le hleft_summable hgeom_summable

  let M : ℝ := B * (1 - q)⁻¹
  have hM_nonneg : 0 ≤ M := by
    have h_one_sub_nonneg : 0 ≤ 1 - q := by linarith [le_of_lt hq_lt_one]
    dsimp [M]
    exact mul_nonneg hB_nonneg (inv_nonneg.mpr h_one_sub_nonneg)

  refine ⟨M, hM_nonneg, ?_⟩
  intro N
  calc
    ∫ t in Ioc T₀ (T₀ + (N : ℝ)),
        ‖PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))‖
        ≤ ∑' k : ℕ, a k * (2 - σ₀) ^ k := h_taylor_majorant N
    _ ≤ ∑' k : ℕ, B * q ^ k := htsum_le
    _ = M := by
      dsimp [M]
      rw [tsum_mul_left]
      simp [tsum_geometric_of_lt_one hq_nonneg hq_lt_one]

end Aristotle.Standalone.LandauSigmaLessThanOneStrict
