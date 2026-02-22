/-
Proof of SigmaLtOneHyp via direct Pringsheim extension on the real line.

The key theorem: for non-negative anti-coefficients B_k with Summable(B_k)
(convergence at w=1 from MCT), the Pringsheim extension argument gives
Summable(B_k (2-σ₀)^k) for σ₀ > α.

The proof uses:
1. Tonelli exchange for w < 1: HasSum(B_k w^k, ∫ g(t)t^{w-3} dt) — PROVED.
2. For W > 1: real Pringsheim bootstrap.
   correctedFormula(2-w) is real-analytic on [0, 2-α) (landau_formula_analyticAt_real).
   Tonelli + witnessG_eq_formula identify tsum(B_k w^k) with correctedFormula on [0,1).
   Non-negative Taylor coefficients (from B_k ≥ 0) + binomial rearrangement
   (sum_range_mul_add_pow_le_of_inner_le) bootstrap partial sum bounds past w=1.
   summable_of_sum_range_le then gives Summable(B_k W^k).
4. Continuous extension F on [0, W]: defined as tsum (using Summable from step 2).
5. Scaled partial sum bound → summable_of_sum_range_le for downstream σ₀.

SORRY COUNT: 1 (anticoeff_complex_extension_on_disk — TRUE,
  from Tonelli + witnessG formula ID + ℂ-analytic extension + identity theorem.
  The Pringsheim convergence step is PROVED via pringsheim_convergence_at_radius.)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.LandauPringsheimRealLine
import Littlewood.Aristotle.Standalone.LandauSigmaLessThanOneGenFunInstantiation
import Littlewood.Aristotle.Standalone.PringsheimBinomialRearrangement

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.Standalone.SigmaLtOneFromPringsheimExtension

open MeasureTheory Set Filter Topology
open Aristotle.Standalone.LandauPringsheimRealLine
open Aristotle.Standalone.LandauSigmaLessThanOneTonelliConcrete
open Aristotle.Standalone.LandauSigmaLessThanOneGenFunInstantiation
open Aristotle.Standalone.LandauCauchyAtCenterTwo
open Aristotle.ZetaPoleCancellation

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

/-! ### Helper: Tonelli HasSum for w < 1

For w ∈ [0, 1), each B_k · w^k = (∫ antiCoeffProfile_k) · w^k. The series of
integrals has summable norms (dominated by Summable(B_k)), so
`hasSum_integral_of_summable_integral_norm` gives the Tonelli exchange. -/

private theorem tonelli_hasSum_lt_one
    (g : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ g t)
    (α C σ_sign : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (hC : 0 < C) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (hg_def : g = PringsheimPsiAtom.genFun C α σ_sign)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) :
    HasSum (fun k => antiCoeff g T₀ 2 k * w ^ k)
      (∫ t in Ioi T₀, g t * t ^ (w - 3)) := by
  -- Step 1: Summable(B_k) from anticoeff_summable_at_one
  have hB_sum : Summable (fun k => antiCoeff g T₀ 2 k) := by
    rw [hg_def]
    exact anticoeff_summable_at_one C hC α hα hα1 σ_sign hσ hbound T₀ hT₀
      (by rw [← hg_def]; exact hg_nn)
  -- Step 2: Each profile is integrable on Ioi T₀
  have hcoeff_int : ∀ k : ℕ,
      IntegrableOn (fun t : ℝ => antiCoeffProfile g k t) (Ioi T₀) := by
    rw [hg_def]
    exact genFun_antiCoeffProfile_integrableOn_tail C hC α (by linarith) σ_sign hσ T₀ hT₀
  -- Step 3: Each F_k(t) := antiCoeffProfile(g,k,t) · w^k is integrable
  have hF_int : ∀ k : ℕ,
      Integrable (fun t => antiCoeffProfile g k t * w ^ k)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Ioi T₀)) := by
    intro k
    exact (hcoeff_int k).mul_const (w ^ k)
  -- Step 4: Summable(∫ ‖F_k‖) — dominated by Summable(B_k)
  have hg_nn_mem : ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ g t := fun t ht => hg_nn t (le_of_lt ht)
  have hF_norm_sum : Summable (fun k =>
      ∫ t in Ioi T₀, ‖antiCoeffProfile g k t * w ^ k‖) := by
    have h_le : ∀ k, ∫ t in Ioi T₀, ‖antiCoeffProfile g k t * w ^ k‖ ≤
        antiCoeff g T₀ 2 k := by
      intro k
      rw [antiCoeff_eq_integral_antiCoeffProfile_center_two g T₀ k]
      have habs_w : |w| ≤ 1 := by rw [abs_of_nonneg hw]; exact le_of_lt hw1
      -- ‖profile * w^k‖ ≤ profile * 1 = profile (since profile ≥ 0 on Ioi T₀ and |w| ≤ 1)
      calc ∫ t in Ioi T₀, ‖antiCoeffProfile g k t * w ^ k‖
          ≤ ∫ t in Ioi T₀, antiCoeffProfile g k t * 1 := by
            apply MeasureTheory.integral_mono_of_nonneg
            · exact (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
                (fun _ _ => norm_nonneg _)
            · exact (hcoeff_int k).mul_const 1
            · exact (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
                (fun t ht => by
                  show ‖antiCoeffProfile g k t * w ^ k‖ ≤ antiCoeffProfile g k t * 1
                  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg
                    (antiCoeffProfile_nonneg_on_tail g T₀ hT₀ hg_nn_mem k t ht),
                    Real.norm_eq_abs, abs_pow, mul_one]
                  calc antiCoeffProfile g k t * |w| ^ k
                      ≤ antiCoeffProfile g k t * 1 :=
                        mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg w) habs_w)
                          (antiCoeffProfile_nonneg_on_tail g T₀ hT₀ hg_nn_mem k t ht)
                    _ = antiCoeffProfile g k t := mul_one _)
        _ = ∫ t in Ioi T₀, antiCoeffProfile g k t := by
            congr 1; ext t; ring
    exact Summable.of_nonneg_of_le
      (fun k => MeasureTheory.integral_nonneg_of_ae
        ((MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono (fun t _ => norm_nonneg _)))
      h_le hB_sum
  -- Step 5: Apply hasSum_integral_of_summable_integral_norm
  have hmain := MeasureTheory.hasSum_integral_of_summable_integral_norm hF_int hF_norm_sum
  -- Rewrite LHS: ∫ F_k = B_k · w^k
  have h_lhs : ∀ k, ∫ t in Ioi T₀, antiCoeffProfile g k t * w ^ k =
      antiCoeff g T₀ 2 k * w ^ k := by
    intro k
    rw [MeasureTheory.integral_mul_const]
    rw [antiCoeff_eq_integral_antiCoeffProfile_center_two g T₀ k]
  simp_rw [h_lhs] at hmain
  -- Rewrite RHS: ∑' k, F_k(t) = g(t) * t^{w-3} on Ioi T₀
  have h_rhs_eq : (∫ t in Ioi T₀,
      ∑' k, (fun k t => antiCoeffProfile g k t * w ^ k) k t) =
      ∫ t in Ioi T₀, g t * t ^ (w - 3) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le (by linarith : 0 < T₀) (le_of_lt ht)
    -- g(t) * t^{w-3} = ∑' antiCoeffProfile(g,k,t) * w^k
    -- This is the exponential series identity: t^w = exp(w * log t) = ∑ (w*log t)^k/k!
    show ∑' k, antiCoeffProfile g k t * w ^ k = g t * t ^ (w - 3)
    have hsplit : t ^ (w - 3 : ℝ) = t ^ (-(3 : ℝ)) * t ^ w := by
      rw [show (w - 3 : ℝ) = (-(3 : ℝ)) + w by ring, Real.rpow_add ht_pos]
    rw [hsplit, ← mul_assoc]
    rw [show t ^ w = Real.exp (w * Real.log t) from by
      rw [Real.rpow_def_of_pos ht_pos]; ring_nf]
    conv_rhs => rw [show Real.exp (w * Real.log t) =
        ∑' k : ℕ, ((w * Real.log t) ^ k / (k.factorial : ℝ)) from by
      simpa [Real.exp_eq_exp_ℝ] using congrArg (fun f : ℝ → ℝ => f (w * Real.log t))
        (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ))]
    rw [← tsum_mul_left]
    congr 1; ext k
    unfold antiCoeffProfile; rw [mul_pow]; ring
  rw [h_rhs_eq] at hmain
  exact hmain

/-! ### Helper: correctedFormula-based function on the real line

Define F(w) = correctedFormula(2-w) restricted to ℝ. Show it's analytic on (-∞, 2-α). -/

private theorem correctedFormula_continuousOn_real_w
    (α C σ_sign : ℝ) (hα : 1 / 2 < α)
    (W : ℝ) (hW : W < 2 - α) :
    ContinuousOn (fun w : ℝ => (correctedFormula α C σ_sign (↑(2 - w))).re) (Icc 0 W) := by
  -- correctedFormula ∘ (2 - ·) is continuous, then take .re
  intro w ⟨_, hw_le⟩
  have hσ : α < 2 - w := by linarith
  -- correctedFormula is analytic at (2-w : ℂ), hence continuous there
  have h_anal : AnalyticAt ℂ (correctedFormula α C σ_sign) (↑(2 - w) : ℂ) := by
    simpa [correctedFormula] using
      Aristotle.ZetaPoleCancellation.landau_formula_analyticAt_real α hα C σ_sign (2 - w) hσ
  -- w ↦ (2-w : ℂ) is continuous
  have h_cast : ContinuousAt (fun x : ℝ => (↑(2 - x) : ℂ)) w := by
    apply ContinuousAt.comp Complex.continuous_ofReal.continuousAt
    exact (continuous_const.sub continuous_id).continuousAt
  -- Show ContinuousAt of the full composition
  have h_inner : ContinuousAt (fun x : ℝ => (↑(2 - x) : ℂ)) w := by
    exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).continuousAt
  have h_full : ContinuousAt (fun x : ℝ => correctedFormula α C σ_sign (↑(2 - x))) w :=
    ContinuousAt.comp (f := fun x : ℝ => (↑(2 - x) : ℂ))
      (g := correctedFormula α C σ_sign) h_anal.continuousAt h_inner
  exact (Complex.continuous_re.continuousAt.comp h_full).continuousWithinAt

/-- **Complex analytic extension of the anti-coefficient power series.**

TRUE from: Tonelli exchange on [0,1) identifies ∑ B_k w^k = ∫ g(t)t^{w-3} dt.
The witnessG/correctedFormula chain (witnessG_eq_formula + landau_formula_eq_original)
identifies this integral with correctedFormula(2-w)/(2-w) minus a finite correction.
Since correctedFormula is ℂ-analytic on {Re > α} (landau_formula_analyticAt_real),
the function f(z) := correctedFormula(2-z)/(2-z) - ∫_1^{T₀} g(t)·(t:ℂ)^{z-3} dt
extends the power series to the complex disk B(0, 2-α) ⊃ B(0, W).
ContinuousAt at W follows from analyticity (W < 2-α).

Proof route:
1. f(z) is ℂ-analytic on {Re(z) < 2-α}: correctedFormula analytic, finite integral entire.
2. For |z| < 1: HasSum((B_k:ℂ)z^k, f(z)) from Tonelli + witnessG identity + ℂ lift.
3. For 1 ≤ |z| < 2-α: identity theorem extends HasSum from B(0,1) ∩ ℝ to B(0,2-α).
4. ContinuousAt f (↑W : ℂ): analytic → continuous.

References: Perron 1908; Titchmarsh §1.8; Landau 1905. -/
private theorem anticoeff_complex_extension_on_disk
    (g : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ g t)
    (α C σ_sign : ℝ) (hα : 1 / 2 < α)
    (hC : 0 < C) (hα1 : α < 1)
    (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (hg_def : g = PringsheimPsiAtom.genFun C α σ_sign)
    (W : ℝ) (hW_bound : W < 2 - α) :
    ∃ f : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ < W →
        HasSum (fun k => (↑(antiCoeff g T₀ 2 k) : ℂ) * z ^ k) (f z)) ∧
      ContinuousAt f (↑W : ℂ) := by
  sorry

/-- **Direct summability at W > 1 via Pringsheim extension.**

From the complex extension (anticoeff_complex_extension_on_disk) and the proved
pringsheim_convergence_at_radius theorem (0 sorries in PringsheimTheorem.lean). -/
private theorem anticoeff_summable_at_W_gt_one
    (g : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ g t)
    (α C σ_sign : ℝ) (hα : 1 / 2 < α)
    (hC : 0 < C) (hα1 : α < 1)
    (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (hg_def : g = PringsheimPsiAtom.genFun C α σ_sign)
    (W : ℝ) (hW_bound : W < 2 - α) (hW1 : 1 < W) :
    Summable (fun k => antiCoeff g T₀ 2 k * W ^ k) := by
  obtain ⟨f, hf_sum, hf_cont⟩ := anticoeff_complex_extension_on_disk
    g T₀ hT₀ hg_nn α C σ_sign hα hC hα1 hσ hbound hg_def W hW_bound
  exact Aristotle.PringsheimTheorem.pringsheim_convergence_at_radius
    (fun k => antiCoeff g T₀ 2 k)
    (antiCoeff_nonneg g T₀ 2 hT₀ hg_nn)
    W (by linarith) f hf_sum hf_cont

/-- **Continuous sum function for anti-coefficient series on the Pringsheim disk**.

There exists F continuous on [0, W] such that HasSum(B_k w^k, F(w)) for w ∈ [0, W).

For W ≤ 1: direct comparison with Summable(B_k).
For W > 1: real Pringsheim bootstrap gives Summable(B_k W^k) via
correctedFormula identification on [0,1) + non-negative Taylor coefficient
bootstrap past w=1. ContinuousOn then follows from Weierstrass M-test. -/
private theorem anticoeff_has_continuous_sum_on_disk
    (g : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ g t)
    (α C σ_sign : ℝ) (hα : 1 / 2 < α)
    (hC : 0 < C) (hα1 : α < 1)
    (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (hg_def : g = PringsheimPsiAtom.genFun C α σ_sign)
    (W : ℝ) (hW_bound : W < 2 - α) :
    ∃ F : ℝ → ℝ, ContinuousOn F (Icc 0 W) ∧
      (∀ w : ℝ, 0 ≤ w → w < W →
        HasSum (fun k => antiCoeff g T₀ 2 k * w ^ k) (F w)) := by
  set B := fun k => antiCoeff g T₀ 2 k with hB_def
  -- Step 1: Summable(B_k) from MCT argument
  have hB_sum : Summable B := by
    simp only [hB_def, hg_def]
    exact anticoeff_summable_at_one C hC α hα hα1 σ_sign hσ hbound T₀ hT₀
      (by rw [← hg_def]; exact hg_nn)
  have hB_nn : ∀ k, 0 ≤ B k := antiCoeff_nonneg g T₀ 2 hT₀ hg_nn
  -- Step 2: Summable(B_k w^k) for all w ∈ [0, W]
  -- Handle W ≤ 0 vacuously (Icc 0 W = ∅)
  by_cases hW_pos : 0 ≤ W
  swap
  · push_neg at hW_pos
    exact ⟨fun _ => 0, continuousOn_const, fun w hw hwW => absurd hwW (not_lt.mpr (by linarith))⟩
  have hB_sum_W : Summable (fun k => B k * W ^ k) := by
    by_cases hW1 : W ≤ 1
    · -- W ≤ 1: comparison with Summable B
      exact Summable.of_nonneg_of_le (fun k => mul_nonneg (hB_nn k) (pow_nonneg hW_pos k))
        (fun k => by
          calc B k * W ^ k ≤ B k * 1 :=
              mul_le_mul_of_nonneg_left (pow_le_one₀ hW_pos hW1) (hB_nn k)
            _ = B k := mul_one _)
        hB_sum
    · -- W > 1: Pringsheim extension via correctedFormula identification.
      push_neg at hW1
      exact anticoeff_summable_at_W_gt_one g T₀ hT₀ hg_nn α C σ_sign hα hC hα1 hσ hbound
        hg_def W hW_bound hW1
  -- Step 3: Define F(w) := tsum(B_k w^k) for w ∈ [0, W]
  refine ⟨fun w => ∑' k, B k * w ^ k, ?_, ?_⟩
  · -- ContinuousOn F on [0, W]
    -- The series ∑ B_k w^k has Summable terms dominated by B_k W^k for w ∈ [0, W].
    -- By continuousOn_tsum with uniform bound: ContinuousOn.
    apply continuousOn_tsum
    · intro k
      exact (continuousOn_const.mul (continuousOn_pow k))
    · exact hB_sum_W
    · intro k w ⟨hw0, hwW⟩
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hB_nn k), Real.norm_eq_abs, abs_pow,
        abs_of_nonneg hw0]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw0 hwW k) (hB_nn k)
  · -- HasSum on [0, W)
    intro w hw hwW
    have hsum_w : Summable (fun k => B k * w ^ k) := by
      exact Summable.of_nonneg_of_le (fun k => mul_nonneg (hB_nn k) (pow_nonneg hw k))
        (fun k => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hw (le_of_lt hwW) k) (hB_nn k))
        hB_sum_W
    exact hsum_w.hasSum

/-- The anti-coefficient summability at w = 2-σ₀ from the Pringsheim extension.

This is the key result: extends convergence from w=1 to w=2-σ₀ > 1.

For W ≤ 1: direct comparison with Summable(B_k).
For W > 1: uses anticoeff_summable_at_W_gt_one. -/
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
  set g := PringsheimPsiAtom.genFun C α σ_sign with hg_def
  set W := (2 : ℝ) - σ₀ with hW_def
  have hW_bound : W < 2 - α := by simp [hW_def]; linarith
  have hW1 : 1 < W := by simp [hW_def]; linarith
  exact anticoeff_summable_at_W_gt_one g T₀ hT₀ hg_nn α C σ_sign hα hC hα1 hσ hbound
    hg_def W hW_bound hW1

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
