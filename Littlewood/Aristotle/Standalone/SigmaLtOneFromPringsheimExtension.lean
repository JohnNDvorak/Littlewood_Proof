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

SORRY COUNT: 0 — All sub-components proved.
  finite_integral_analyticAt: parametric integral analyticity via complexification.
  IntegrableOn conditions: bounded on compact + O(t^{w-2}) tail decay.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.LandauPringsheimRealLine
import Littlewood.Aristotle.Standalone.LandauSigmaLessThanOneGenFunInstantiation
import Littlewood.Aristotle.Standalone.PringsheimBinomialRearrangement
import Littlewood.Aristotle.Standalone.PringsheimRealBootstrap

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

/-! ### Direct summability at W > 1 via Pringsheim extension

TRUE: The convergence radius of the anti-coefficient power series ∑ B_k w^k
is at least 2-α (distance from center σ=2 to the pole at σ=α).

Proof: Tonelli identifies ∑' B_k w^k with correctedFormula expression on [0,1).
correctedFormula is real-analytic on [0, 2-α). Real Pringsheim bootstrap extends
summability from w=1 to w=W. References: Pringsheim 1893; Landau 1905. -/

/-- The correctedFormula-based function is real-analytic at any w < 2-α.
This follows from `landau_formula_analyticAt_real` and composition with w ↦ 2-w. -/
private lemma correctedFormula_analyticAt_real_w
    (α C σ_sign : ℝ) (hα : 1 / 2 < α)
    (w : ℝ) (hw : w < 2 - α) :
    AnalyticAt ℝ (fun w : ℝ => (correctedFormula α C σ_sign (↑(2 - w))).re) w := by
  have hσ_real : α < 2 - w := by linarith
  -- correctedFormula is ℂ-analytic at (2-w : ℂ)
  have h_anal_C : AnalyticAt ℂ (correctedFormula α C σ_sign) (↑(2 - w) : ℂ) := by
    simpa [correctedFormula] using
      Aristotle.ZetaPoleCancellation.landau_formula_analyticAt_real α hα C σ_sign (2 - w) hσ_real
  -- f(z) = correctedFormula(2 - z) is ℂ-analytic at (w : ℂ)
  have h_comp : AnalyticAt ℂ (fun z : ℂ => correctedFormula α C σ_sign (2 - z)) (↑w) := by
    have h_sub : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) - z) (↑w) :=
      analyticAt_const.sub analyticAt_id
    exact h_anal_C.comp_of_eq h_sub (by push_cast; ring)
  -- Apply re_ofReal to get ℝ-analyticity
  have h_re := h_comp.re_ofReal
  -- Match function: (2 : ℂ) - ↑x = ↑(2 - x)
  convert h_re using 1
  ext x; congr 1; push_cast; ring

/-! ### Direct summability at W > 1 via Pringsheim extension (correctedFormula approach)

The Tonelli integral ∫_{T₀}^∞ g(t) t^{w-3} dt converges for w < 1 but DIVERGES
for w ≥ 1 (since g(t) = O(t)). The Lean integral returns 0 for non-integrable
functions, so the function w ↦ ∫ g·t^{w-3} is NOT analytic at w ≥ 1.

Instead, we define F via the correctedFormula, which IS analytic on all of (0, 2-α):
  F(w) = correctedFormula(2-w).re / (2-w) - ∫_{Icc 1 T₀} g(t)·t^{w-3} dt

For w < 1: F agrees with the Tonelli integral ∫_{Ioi T₀} g·t^{w-3} via:
  correctedFormula(2-w) = witnessG(2-w) = (2-w)·∫_{Ioi 1} g·t^{w-3}  (bridge)
  ∫_{Ioi 1} = ∫_{Icc 1 T₀} + ∫_{Ioi T₀}  (splitting)

For w ≥ 1: F is the analytic extension defined by the correctedFormula.

SORRY COUNT: 1
  finite_integral_analyticAt — parametric integral of analytic integrand on compact domain
  TRUE: t^{w-3} = exp((w-3)·log t) is analytic in w; uniform convergence of Taylor series
  on [1, T₀] gives ∫ g·t^{w-3} dt analytic via termwise integration.

References: Titchmarsh §1.8; standard parametric integral theory. -/

set_option maxHeartbeats 6400000 in
/-- Finite integral `∫_{Icc 1 T₀} g(t)·t^{w-3} dt` is real-analytic in w.

Proof: complexify to `Φ(z) = ∫ (g t : ℂ) * (↑t)^(z-3) dt`, show Φ is ℂ-differentiable
via parametric differentiation (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`),
then holomorphic → analytic (`Differentiable.analyticAt`), bridge `Φ(↑w) = ↑(f(w))`
via `Complex.ofReal_cpow`, and restrict to ℝ via `AnalyticAt.re_ofReal`. -/
private theorem finite_integral_analyticAt
    (g : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_meas : Measurable g)
    (hg_bound : ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 1 ≤ t → |g t| ≤ D * t)
    (w₀ : ℝ) :
    AnalyticAt ℝ (fun w => ∫ t in Icc 1 T₀, g t * t ^ (w - 3)) w₀ := by
  obtain ⟨D, hD, hg_le⟩ := hg_bound
  -- Step 1: Define the complexified integrand
  set Φ : ℂ → ℂ := fun z => ∫ t in Icc (1 : ℝ) T₀,
    ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ (z - 3) with hΦ_def
  -- Step 2: Show Φ is ℂ-differentiable everywhere
  have hΦ_diff : Differentiable ℂ Φ := by
    intro z₀
    -- Use hasDerivAt_integral_of_dominated_loc_of_deriv_le
    set s := Metric.ball z₀ 1
    set μ := MeasureTheory.Measure.restrict MeasureTheory.volume (Icc (1 : ℝ) T₀)
    -- The derivative of (g t : ℂ) * (↑t)^(z-3) w.r.t. z is
    -- (g t : ℂ) * Complex.log(↑t) * (↑t)^(z-3)
    -- Bound: on [1,T₀] × ball(z₀,1), ‖F'(z,t)‖ ≤ D*T₀ * log(T₀) * M for suitable M
    set M := max (T₀ ^ (z₀.re + 1 - 3)) 1 with hM_def
    set bound_val := D * T₀ * Real.log T₀ * M with hbound_def
    have hM_pos : 0 < M := lt_max_of_lt_right one_pos
    -- HasDerivAt for each t
    have h_deriv : ∀ t : ℝ, 1 ≤ t → t ≤ T₀ →
        ∀ z : ℂ, HasDerivAt (fun z => ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ (z - 3))
          (((g t : ℝ) : ℂ) * Complex.log (↑t) * (↑t : ℂ) ^ (z - 3)) z := by
      intro t ht1 _htT₀ z
      have ht_pos : (0 : ℝ) < t := by linarith
      have ht_ne : (↑t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht_pos)
      -- HasDerivAt for z ↦ (↑t)^(z-3) via const_cpow
      have h_sub : HasDerivAt (fun z : ℂ => z - 3) 1 z := by
        exact (hasDerivAt_id z).sub_const 3
      have h_cpow : HasDerivAt (fun z : ℂ => (↑t : ℂ) ^ (z - 3))
          ((↑t : ℂ) ^ (z - 3) * Complex.log (↑t) * 1) z := by
        exact HasDerivAt.const_cpow h_sub (Or.inl ht_ne)
      simp only [mul_one] at h_cpow
      exact (h_cpow.const_mul _).congr_deriv (by ring)
    -- Norm bound on derivative
    have h_norm_bound : ∀ t : ℝ, t ∈ Icc 1 T₀ → ∀ z ∈ s,
        ‖((g t : ℝ) : ℂ) * Complex.log (↑t) * (↑t : ℂ) ^ (z - 3)‖ ≤ bound_val := by
      intro t ⟨ht1, htT₀⟩ z hz
      have ht_pos : (0 : ℝ) < t := by linarith
      -- ‖(g t : ℂ)‖ = |g t| ≤ D * t ≤ D * T₀
      have h1 : ‖((g t : ℝ) : ℂ)‖ ≤ D * T₀ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (hg_le t ht1).trans (by nlinarith)
      -- ‖Complex.log(↑t)‖ ≤ |log(t)| = log(t) ≤ log(T₀)
      have h2 : ‖Complex.log (↑t)‖ ≤ Real.log T₀ := by
        rw [show Complex.log (↑t) = ↑(Real.log t) from by
          rw [Complex.ofReal_log (le_of_lt ht_pos)]]
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_nonneg ht1)]
        exact Real.log_le_log ht_pos htT₀
      -- ‖(↑t)^(z-3)‖ = t^(Re(z)-3) ≤ M
      have h3 : ‖(↑t : ℂ) ^ (z - 3)‖ ≤ M := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos (z - 3)]
        -- t^(Re(z-3)) = t^(z.re - 3)
        have hre : (z - 3).re = z.re - 3 := by simp
        rw [hre]
        by_cases hexp : z.re - 3 ≥ 0
        · -- t^(z.re-3) ≤ T₀^(z.re-3) ≤ T₀^(z₀.re+1-3) ≤ M
          calc t ^ (z.re - 3) ≤ T₀ ^ (z.re - 3) :=
                Real.rpow_le_rpow (by linarith) htT₀ hexp
            _ ≤ T₀ ^ (z₀.re + 1 - 3) := by
                apply Real.rpow_le_rpow_of_exponent_le (by linarith)
                have h_dist : dist z z₀ < 1 := Metric.mem_ball.mp hz
                have h_abs_re : |z.re - z₀.re| ≤ dist z z₀ := by
                  calc |z.re - z₀.re| = |(z - z₀).re| := by congr 1
                    _ ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
                    _ = dist z z₀ := (dist_eq_norm z z₀).symm
                linarith [(abs_le.mp (h_abs_re.trans h_dist.le)).2]
            _ ≤ M := le_max_left _ _
        · -- z.re - 3 < 0, so t^(z.re-3) ≤ 1^(z.re-3) = 1 ≤ M
          push_neg at hexp
          calc t ^ (z.re - 3) ≤ 1 :=
                Real.rpow_le_one_of_one_le_of_nonpos ht1 (le_of_lt hexp)
            _ ≤ M := le_max_right _ _
      calc ‖((g t : ℝ) : ℂ) * Complex.log (↑t) * (↑t : ℂ) ^ (z - 3)‖
          = ‖((g t : ℝ) : ℂ)‖ * ‖Complex.log (↑t)‖ * ‖(↑t : ℂ) ^ (z - 3)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ (D * T₀) * Real.log T₀ * M := by
            have : 0 ≤ Real.log T₀ := Real.log_nonneg (by linarith)
            gcongr
        _ = bound_val := by ring
    -- AEStronglyMeasurable helpers (cpow via ContinuousOn on [1,T₀])
    have h_slit : ∀ t : ℝ, t ∈ Icc 1 T₀ → (↑t : ℂ) ∈ Complex.slitPlane := by
      intro t ⟨ht1, _⟩; left; simp [Complex.ofReal_re]; linarith
    have h_cpow_cont : ∀ z : ℂ, ContinuousOn
        (fun t : ℝ => (↑t : ℂ) ^ (z - 3)) (Icc 1 T₀) :=
      fun z => (Complex.continuous_ofReal.continuousOn.cpow_const (fun t ht => h_slit t ht))
    have h_g_aesm : AEStronglyMeasurable (fun t : ℝ => ((g t : ℝ) : ℂ)) μ :=
      (Complex.measurable_ofReal.comp hg_meas).aestronglyMeasurable
    have h_aesm : ∀ z : ℂ, AEStronglyMeasurable
        (fun t : ℝ => ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ (z - 3)) μ :=
      fun z => h_g_aesm.mul ((h_cpow_cont z).aestronglyMeasurable measurableSet_Icc)
    -- Apply the parametric integral theorem
    have h_result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds z₀ one_pos)
      -- hF_meas: AEStronglyMeasurable for each z
      (Eventually.of_forall fun z => h_aesm z)
      -- hF_int: Integrable at z₀
      (by
        refine Integrable.mono'
          (integrableOn_const (C := D * T₀ * M) (hs := isCompact_Icc.measure_lt_top.ne))
          (h_aesm z₀) ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ⟨ht1, htT₀⟩
        have ht_pos : (0 : ℝ) < t := by linarith
        calc ‖((g t : ℝ) : ℂ) * (↑t : ℂ) ^ (z₀ - 3)‖
            = ‖((g t : ℝ) : ℂ)‖ * ‖(↑t : ℂ) ^ (z₀ - 3)‖ := norm_mul _ _
          _ ≤ (D * T₀) * M := by
              apply mul_le_mul
              · rw [Complex.norm_real, Real.norm_eq_abs]
                exact (hg_le t ht1).trans (by nlinarith)
              · rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
                simp only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im]
                by_cases hexp : z₀.re - 3 ≥ 0
                · exact (Real.rpow_le_rpow (by linarith) htT₀ hexp).trans
                    ((Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans
                      (le_max_left _ _))
                · push_neg at hexp
                  exact (Real.rpow_le_one_of_one_le_of_nonpos ht1 hexp.le).trans (le_max_right _ _)
              · exact norm_nonneg _
              · positivity)
      -- hF'_meas: derivative measurable at z₀
      ((h_g_aesm.mul ((Complex.continuous_ofReal.continuousOn.clog
          (fun t ht => h_slit t ht)).aestronglyMeasurable measurableSet_Icc)).mul
        ((h_cpow_cont z₀).aestronglyMeasurable measurableSet_Icc))
      -- h_bound: norm of derivative bounded
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht z hz
        exact h_norm_bound t ht z hz)
      -- bound_integrable: constant is integrable on compact set
      (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))
      -- h_diff: HasDerivAt for each t
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ⟨ht1, htT₀⟩ z _hz
        exact h_deriv t ht1 htT₀ z)
    exact h_result.2.differentiableAt
  -- Step 3: AnalyticAt ℂ Φ z₀
  have hΦ_anal : AnalyticAt ℂ Φ (↑w₀) := hΦ_diff.analyticAt (↑w₀)
  -- Step 4: Bridge Φ(↑w) = ↑(f(w))
  have h_bridge : (fun w : ℝ => (Φ (↑w)).re) = fun w => ∫ t in Icc 1 T₀, g t * t ^ (w - 3) := by
    ext w
    show (∫ t in Icc (1 : ℝ) T₀, ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ ((↑w : ℂ) - 3)).re =
      ∫ t in Icc 1 T₀, g t * t ^ (w - 3)
    rw [show (↑w : ℂ) - (3 : ℂ) = ((w - 3 : ℝ) : ℂ) from by push_cast; ring]
    have h_eq : ∀ t ∈ Icc (1 : ℝ) T₀,
        ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ ((w - 3 : ℝ) : ℂ) =
        ((g t * t ^ (w - 3) : ℝ) : ℂ) := by
      intro t ⟨ht1, _⟩
      rw [show (↑t : ℂ) ^ ((w - 3 : ℝ) : ℂ) = ((t ^ (w - 3) : ℝ) : ℂ) from
        (Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ t) _).symm,
        ← Complex.ofReal_mul]
    rw [setIntegral_congr_fun measurableSet_Icc h_eq]
    have : ∫ x in Icc (1 : ℝ) T₀, ((g x * x ^ (w - 3) : ℝ) : ℂ) =
        (↑(∫ x in Icc 1 T₀, g x * x ^ (w - 3)) : ℂ) := integral_ofReal
    rw [this, Complex.ofReal_re]
  -- Step 5: AnalyticAt ℝ via re_ofReal
  rw [← h_bridge]
  exact hΦ_anal.re_ofReal

-- Bridge: correctedFormula(2-w).re / (2-w) = ∫_{Ioi 1} genFun·t^{w-3} for w < 1.
-- Chain: correctedFormula = witnessG [formula matching] → dirichletIntegral [def]
--        → ↑(∫ genFun · t^{w-3}) [cpow bridge + integral_ofReal] → .re / (2-w).
set_option maxHeartbeats 3200000 in
private theorem correctedFormula_div_eq_integral
    (α C σ_sign : ℝ) (hα : 1 / 2 < α) (hC : 0 < C) (hα1 : α < 1)
    (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (w : ℝ) (_hw : 0 ≤ w) (hw1 : w < 1) :
    (correctedFormula α C σ_sign (↑(2 - w))).re / (2 - w) =
    ∫ t in Ioi (1 : ℝ), PringsheimPsiAtom.genFun C α σ_sign t * t ^ (w - 3) := by
  have h2w_gt1 : (1 : ℝ) < 2 - w := by linarith
  have h2w_ne : (2 : ℝ) - w ≠ 0 := by linarith
  -- Step 1: correctedFormula = witnessG (formula matching)
  have h_cf_eq : correctedFormula α C σ_sign (↑(2 - w)) =
      PringsheimPsiAtom.witnessG C α σ_sign (↑(2 - w)) := by
    unfold correctedFormula
    rw [Aristotle.ZetaPoleCancellation.landau_formula_eq_original α C (2 - w) h2w_gt1 σ_sign,
      ← PringsheimPsiAtom.witnessG_eq_formula C hC α hα σ_sign hσ hbound
        (↑(2 - w)) (by simp; linarith) (by simp; linarith)]
  -- Step 2: dirichletIntegral = ↑(real integral) via cpow bridge
  -- Define the real integral for cleaner type inference
  set I := ∫ t in Ioi (1 : ℝ),
    PringsheimPsiAtom.genFun C α σ_sign t * t ^ (w - 3) with hI_def
  have h_di_real : PringsheimPsiAtom.dirichletIntegral C α σ_sign (↑(2 - w)) =
      (I : ℂ) := by
    unfold PringsheimPsiAtom.dirichletIntegral
    have h_eq : ∀ t ∈ Ioi (1 : ℝ),
        ((↑(PringsheimPsiAtom.genFun C α σ_sign t) : ℂ) *
          (↑t : ℂ) ^ (-((↑(2 - w) : ℂ) + 1))) =
        ((PringsheimPsiAtom.genFun C α σ_sign t * t ^ (w - 3) : ℝ) : ℂ) := by
      intro t ht
      have ht0 : 0 ≤ t := by linarith [show (1 : ℝ) < t from ht]
      have h_exp : (-(((↑(2 - w) : ℂ)) + (1 : ℂ)) : ℂ) = ((w - 3 : ℝ) : ℂ) := by
        push_cast; ring
      rw [h_exp, show (↑t : ℂ) ^ ((w - 3 : ℝ) : ℂ) = ((t ^ (w - 3) : ℝ) : ℂ) from
        (Complex.ofReal_cpow ht0 (w - 3)).symm]
      push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi h_eq]
    exact integral_ofReal
  -- Step 3: combine and simplify
  rw [h_cf_eq]
  show (PringsheimPsiAtom.witnessG C α σ_sign (↑(2 - w))).re / (2 - w) = I
  unfold PringsheimPsiAtom.witnessG
  rw [h_di_real, show ((↑(2 - w) : ℂ) * (I : ℂ)) = ((2 - w) * I : ℝ) from by push_cast; ring]
  simp [Complex.ofReal_re, mul_div_cancel_left₀ _ h2w_ne]

set_option maxHeartbeats 3200000 in
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
  set B := fun k => antiCoeff g T₀ 2 k
  have hB_sum : Summable B := by
    show Summable (fun k => antiCoeff g T₀ 2 k)
    rw [hg_def]
    exact anticoeff_summable_at_one C hC α hα hα1 σ_sign hσ hbound T₀ hT₀
      (by rw [← hg_def]; exact hg_nn)
  have hB_nn : ∀ k, 0 ≤ B k := antiCoeff_nonneg g T₀ 2 hT₀ hg_nn
  -- F(w) = correctedFormula(2-w).re / (2-w) - ∫_{Icc 1 T₀} g t * t^{w-3}
  -- This is analytic on (0, 2-α) since correctedFormula is analytic and finite integral is analytic.
  -- For w < 1: F agrees with ∫_{Ioi T₀} g t * t^{w-3} (Tonelli integral).
  set F := fun w : ℝ =>
    (correctedFormula α C σ_sign (↑(2 - w))).re / (2 - w) -
    ∫ t in Icc 1 T₀, g t * t ^ (w - 3) with hF_def
  have hF_anal : ∀ w, 0 < w → w ≤ W → AnalyticAt ℝ F w := by
    intro w hw hw_le
    have hwα : w < 2 - α := lt_of_le_of_lt hw_le hW_bound
    have h2w_ne : (2 : ℝ) - w ≠ 0 := by linarith
    have hΦ_anal := correctedFormula_analyticAt_real_w α C σ_sign hα w hwα
    have hΦdiv_anal : AnalyticAt ℝ
        (fun w : ℝ => (correctedFormula α C σ_sign (↑(2 - w))).re / (2 - w)) w :=
      hΦ_anal.div (analyticAt_const.sub analyticAt_id) h2w_ne
    have hg_meas : Measurable g := by
      rw [hg_def]; unfold PringsheimPsiAtom.genFun
      exact (measurable_id.pow_const α |>.const_mul C).add
        ((measurable_id.sub Chebyshev.psi_mono.measurable).const_mul σ_sign)
    have hg_bound := PringsheimPsiAtom.genFun_le_linear C hC α (le_of_lt hα1) σ_sign hσ
    exact hΦdiv_anal.sub (finite_integral_analyticAt g T₀ hT₀ hg_meas
      (by rw [hg_def]; exact hg_bound) w)
  have hF_hasSum : ∀ w, 0 ≤ w → w < 1 →
      HasSum (fun k => B k * w ^ k) (F w) := by
    intro w hw hw1
    have hTonelli := tonelli_hasSum_lt_one g T₀ hT₀ hg_nn α C σ_sign hα hα1 hC hσ
      hbound hg_def w hw hw1
    suffices h_eq : F w = ∫ t in Ioi T₀, g t * t ^ (w - 3) from h_eq ▸ hTonelli
    -- Bridge: correctedFormula(2-w).re / (2-w) = ∫_{Ioi 1} g·t^{w-3}
    have h_bridge := correctedFormula_div_eq_integral α C σ_sign hα hC hα1 hσ hbound w hw hw1
    -- Unpack F(w) and substitute the bridge
    show (correctedFormula α C σ_sign (↑(2 - w))).re / (2 - w) -
      ∫ t in Icc 1 T₀, g t * t ^ (w - 3) =
      ∫ t in Ioi T₀, g t * t ^ (w - 3)
    rw [hg_def, h_bridge, ← hg_def]
    -- Integral splitting: ∫_{Ioi 1} f - ∫_{Icc 1 T₀} f = ∫_{Ioi T₀} f
    -- Icc 1 T₀ and Ioi T₀ are disjoint, union = Ici 1
    have h_disj : Disjoint (Icc (1 : ℝ) T₀) (Ioi T₀) :=
      Set.disjoint_left.mpr (fun _ ⟨_, ht⟩ h => not_lt.mpr ht h)
    -- IntegrableOn conditions: bounded on compact, O(t^{w-2}) on semi-infinite
    have hα1_le : α ≤ 1 := le_of_lt hα1
    obtain ⟨D, hD, hle⟩ := PringsheimPsiAtom.genFun_le_linear C hC α hα1_le σ_sign hσ
    have hg_meas : Measurable g := by
      rw [hg_def]; unfold PringsheimPsiAtom.genFun
      exact (measurable_id.pow_const α |>.const_mul C).add
        ((measurable_id.sub Chebyshev.psi_mono.measurable).const_mul σ_sign)
    have hf_Icc : IntegrableOn (fun t => g t * t ^ (w - 3)) (Icc 1 T₀) := by
      apply Measure.integrableOn_of_bounded (isCompact_Icc.measure_lt_top.ne)
        ((hg_meas.mul (measurable_id.pow_const _)).aestronglyMeasurable) (M := D * T₀)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ⟨ht1, htT₀⟩
      rw [Real.norm_eq_abs, abs_mul]
      have ht_pos : 0 < t := by linarith
      have h_abs_g : |g t| ≤ D * t := by rw [hg_def]; exact hle t ht1
      have h_abs_rpow : |t ^ (w - 3)| ≤ 1 := by
        rw [abs_of_pos (Real.rpow_pos_of_pos ht_pos _)]
        exact Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
      calc |g t| * |t ^ (w - 3)|
          ≤ (D * t) * 1 := mul_le_mul h_abs_g h_abs_rpow (abs_nonneg _) (by positivity)
        _ = D * t := mul_one _
        _ ≤ D * T₀ := by nlinarith [hD]
    have hf_Ioi_T₀ : IntegrableOn (fun t => g t * t ^ (w - 3)) (Ioi T₀) := by
      have h_bound : IntegrableOn (fun t : ℝ => D * t ^ (w - 2)) (Ioi T₀) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith : w - 2 < -1)
          (by linarith : (0 : ℝ) < T₀)).const_mul D
      apply h_bound.mono'
      · exact (hg_meas.mul (measurable_id.pow_const _)).aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht1 : 1 ≤ t := by linarith [show T₀ < t from ht]
        have ht_pos : 0 < t := by linarith
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht_pos _)]
        calc |g t| * t ^ (w - 3)
            ≤ D * t * t ^ (w - 3) := by
              rw [hg_def]
              exact mul_le_mul_of_nonneg_right (hle t ht1) (Real.rpow_nonneg ht_pos.le _)
          _ = D * (t ^ (1 : ℝ) * t ^ (w - 3)) := by rw [Real.rpow_one]; ring
          _ = D * t ^ (1 + (w - 3)) := by rw [← Real.rpow_add ht_pos]
          _ = D * t ^ (w - 2) := by ring_nf
    -- ∫_{Ici 1} = ∫_{Icc 1 T₀} + ∫_{Ioi T₀}
    have h_split := setIntegral_union h_disj measurableSet_Ioi hf_Icc hf_Ioi_T₀
    -- ∫_{Ioi 1} = ∫_{Ici 1} (singleton {1} has measure zero for Lebesgue)
    rw [Icc_union_Ioi_eq_Ici hT₀, integral_Ici_eq_integral_Ioi] at h_split
    linarith
  exact Aristotle.Standalone.PringsheimRealBootstrap.pringsheim_real_extension
    B hB_nn hB_sum F hF_hasSum W hW1 hF_anal

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
