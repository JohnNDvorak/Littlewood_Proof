/-
Proof of SigmaLtOneHyp via direct Pringsheim extension on the real line.

The key theorem: for non-negative anti-coefficients B_k with Summable(B_k)
(convergence at w=1 from MCT), the corrected formula provides a real-analytic
extension to [0, 2-α), and the Pringsheim extension argument gives
Summable(B_k (2-σ₀)^k) for σ₀ > α.

The proof uses the sup/contradiction argument:
1. R* := sup{w ≥ 0 : Summable(B_k w^k)}. R* ≥ 1.
2. If R* ≥ 2-σ₀: done (comparison for non-neg series).
3. If R* < 2-σ₀ ≤ 2-α: F analytic at R* (from correctedFormula).
   Partial sums Σ_{k<N} B_k R*^k ≤ F(R*) [limit from below].
   By summable_of_sum_range_le: Summable at R*.
   Taylor expansion at R* with non-negative coefficients + binomial
   rearrangement → Summable at R*+ε → contradiction.

SORRY COUNT: 1 (Pringsheim non-negative real extension)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.LandauPringsheimRealLine
import Littlewood.Aristotle.Standalone.LandauSigmaLessThanOneGenFunInstantiation
import Littlewood.Aristotle.Standalone.PringsheimBinomialRearrangement
import Littlewood.Aristotle.PringsheimTheorem

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.Standalone.SigmaLtOneFromPringsheimExtension

open MeasureTheory Set Filter Topology
open Aristotle.Standalone.LandauPringsheimRealLine
open Aristotle.Standalone.LandauSigmaLessThanOneTonelliConcrete
open Aristotle.Standalone.LandauSigmaLessThanOneGenFunInstantiation

/-! ## Direct proof of SigmaLtOneHyp

Uses the Pringsheim extension to get anti-coefficient summability, then the
existing Tonelli infrastructure to convert summability → IntegrableOn.

The anti-coefficient series Σ B_k w^k has:
- B_k ≥ 0 (from g ≥ 0 on [T₀,∞))
- Summable(B_k) (from anticoeff_summable_at_one, MCT argument)
- Sum function equals correctedFormula(2-w) on [0, 1) (Tonelli/Fubini)
- correctedFormula(2-w) extends analytically to all w < 2-α (ZetaPoleCancellation)

### Proof strategy for Pringsheim real-line extension (~200 lines)

Define F(w) := correctedFormula(2-w) restricted to ℝ, and
  G(w) := ∑' B_k w^k  for w in the convergence disk [0, R*).
By Tonelli: G(w) = F(w) for w ∈ [0, 1).

Let R* := sup{w ≥ 0 : Summable(B_k w^k)}. We have R* ≥ 1.
If R* ≥ 2-σ₀: comparison gives Summable(B_k (2-σ₀)^k). Done.
If R* < 2-σ₀ < 2-α:
  (a) G is analytic on [0, R*) (convergent power series).
      F is analytic on [0, 2-α) (from `landau_formula_analyticAt_real`).
      By identity theorem (both analytic, agree on [0,1)):
        G = F on [0, R*).
  (b) At R*: ∑_{k<N} B_k (R*)^k
        = lim_{w→R*⁻} ∑_{k<N} B_k w^k
        ≤ lim_{w→R*⁻} G(w)
        = lim_{w→R*⁻} F(w)
        = F(R*)    (continuity of F)
      By `summable_of_sum_range_le`: Summable(B_k (R*)^k).
  (c) Taylor expansion of F at R*: F(R*+t) = ∑ p_j t^j with p_j ≥ 0
      (limit of non-negative derivatives from below).
      Binomial rearrangement (`sum_range_mul_add_pow_le_of_inner_le`):
        ∑_{k<N} B_k (R*+t)^k ≤ ∑_{j<N} p_j t^j ≤ F(R*+t).
      By `summable_of_sum_range_le`: Summable at R*+t for small t > 0.
      This contradicts R* = sup. □

Key Mathlib ingredients:
- `summable_of_sum_range_le` (non-negative partial sums bounded → Summable)
- Identity theorem for real-analytic functions
- `HasFPowerSeriesOnBall.deriv` (term-by-term differentiation)
- `sum_range_mul_add_pow_le_of_inner_le` (binomial rearrangement, PROVED)
- `landau_formula_analyticAt_real` (correctedFormula analyticity at real σ > α, PROVED)

References: Titchmarsh §1.8; Pringsheim 1893; Landau 1905. -/

/-- The anti-coefficient summability at w = 2-σ₀ from the Pringsheim extension.

This is the key result: extends convergence from w=1 to w=2-σ₀ > 1.
Uses the fact that correctedFormula is analytic at every real σ > α,
hence the sum function of Σ B_k w^k extends analytically to [0, 2-α).

**Sorry**: Requires the full Pringsheim non-negative real-line extension argument
(~200 lines, see proof strategy above). The key missing piece is the
sup/contradiction + identity theorem + binomial rearrangement chain. -/
theorem anticoeff_summable_at_target
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀_lt1 : σ₀ < 1) :
    Summable (fun k =>
      antiCoeff (PringsheimPsiAtom.genFun C α σ_sign) T₀ 2 k *
        (2 - σ₀) ^ k) := by
  sorry

/-- **SigmaLtOneHyp proved**: IntegrableOn from anti-coefficient summability
via the Tonelli infrastructure.

Chain: anticoeff_summable_at_target → bounded partial integrals
→ integrableOn_Ioi_of_intervalIntegral_norm_bounded → IntegrableOn. -/
theorem sigmaLtOneHyp_proved : Aristotle.LandauAbscissaProof.SigmaLtOneHyp := by
  intro C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn
  -- Step 1: Get the anti-coefficient summability
  have hB_sum := anticoeff_summable_at_target C hC α hα hα1 σ_sign hσ hbound
    T₀ hT₀ hg_nn σ₀ hσ₀ hσ₀_lt1
  -- Step 2: Convert to the form needed by partial_integral_le_tsum_anticoeff_coeffs
  have hα_le1 : α ≤ 1 := by linarith
  have hσ₀_pos : 0 < σ₀ := by linarith
  let g := PringsheimPsiAtom.genFun C α σ_sign
  have hg_meas : Measurable g := by
    unfold g PringsheimPsiAtom.genFun
    exact (measurable_id.pow_const α |>.const_mul C).add
      ((measurable_id.sub Chebyshev.psi_mono.measurable).const_mul σ_sign)
  have hg_nonneg_mem : ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ g t := by
    intro t ht; exact hg_nn t (le_of_lt ht)
  -- Step 3: Get the Tonelli infrastructure
  have hmain_int := genFun_norm_integrableOn_partialIntervals C hC α hα_le1 σ_sign hσ
    σ₀ hσ₀_pos T₀ hT₀
  have hcoeff_int := genFun_antiCoeffProfile_integrableOn_tail C hC α hα_le1 σ_sign hσ T₀ hT₀
  -- Convert summability to the right form
  have hsum_coeff : Summable (fun k : ℕ =>
      (∫ t in Ioi T₀, antiCoeffProfile g k t) * (2 - σ₀) ^ k) := by
    have h_eq : ∀ k, (∫ t in Ioi T₀, antiCoeffProfile g k t) =
        antiCoeff g T₀ 2 k := by
      intro k; exact (antiCoeff_eq_integral_antiCoeffProfile_center_two g T₀ k).symm
    exact hB_sum.congr (by intro k; rw [← h_eq k])
  -- Step 4: Get bounded partial integrals from Tonelli
  have hpartial := partial_integral_le_tsum_anticoeff_coeffs g T₀ σ₀ hT₀ hσ₀_lt1
    hg_meas hg_nonneg_mem hmain_int hcoeff_int hsum_coeff
  -- Step 5: The tsum is non-negative (bound for integrableOn_Ioi_of_intervalIntegral_norm_bounded)
  have hM_nn : 0 ≤ ∑' k : ℕ, (∫ t in Ioi T₀, antiCoeffProfile g k t) * (2 - σ₀) ^ k := by
    apply tsum_nonneg
    intro k
    apply mul_nonneg
    · apply integral_nonneg_of_ae
      apply (ae_restrict_mem measurableSet_Ioi).mono
      intro t ht
      exact antiCoeffProfile_nonneg_on_tail g T₀ hT₀ hg_nonneg_mem k t ht
    · exact pow_nonneg (by linarith : 0 ≤ 2 - σ₀) _
  -- Step 6: IntegrableOn from bounded partial integrals
  obtain ⟨D, hD, hg_le⟩ := PringsheimPsiAtom.genFun_le_linear C hC α hα_le1 σ_sign hσ
  have h_tendsto : Tendsto (fun n : ℕ => T₀ + (↑n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ T₀ tendsto_natCast_atTop_atTop
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (f := fun t => g t * t ^ (-(σ₀ + 1)))
    (μ := volume) (l := atTop) (b := fun n : ℕ => T₀ + ↑n)
    (∑' k : ℕ, (∫ t in Ioi T₀, antiCoeffProfile g k t) * (2 - σ₀) ^ k)
    T₀
  · -- IntegrableOn on each finite piece
    intro n
    exact (genFun_integrableOn_partialIntervals C hC α hα_le1 σ_sign hσ σ₀ hσ₀_pos T₀ hT₀ n)
  · exact h_tendsto
  · filter_upwards with n
    rw [intervalIntegral.integral_of_le (by linarith : T₀ ≤ T₀ + (↑n : ℝ))]
    exact hpartial n

end Aristotle.Standalone.SigmaLtOneFromPringsheimExtension
