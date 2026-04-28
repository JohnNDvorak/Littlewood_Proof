/-
# Gamma half-top variation bound — helper lemmas

Core lemmas for the `GammaHalfTopVariationBoundHyp` instance.
The integrand `Im(logDeriv Gammaℝ(x+iT))` is bounded by a constant
for `x ∈ [1/2, 2]` and `T ≥ 14`, using the digamma asymptotic expansion.
-/

import Littlewood.ZetaZeros.RvMRightEdge
import Littlewood.Aristotle.DigammaAsymptotic

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 800000
set_option autoImplicit false

open Complex Set MeasureTheory Topology Filter
open scoped Real ComplexConjugate

noncomputable section

namespace ZetaZeros.GammaHalfTopBound

/-! ### Step 1: Im(logDeriv Gammaℝ(s)) = (1/2) · Im(ψ(s/2)) -/

/-
PROBLEM
The imaginary part of `logDeriv Gammaℝ(s)` equals `(1/2) · Im(logDeriv Gamma(s/2))`
    for `Re(s) > 0`, since `-(1/2)·log π` is real.

PROVIDED SOLUTION
Use `RvMRightEdge.logDeriv_GammaR_eq s hs` to rewrite:
  logDeriv Gammaℝ s = -(1/2) * Complex.log ↑π + (1/2) * logDeriv Complex.Gamma (s/2)

Then take Im of both sides. The first term `-(1/2) * Complex.log ↑π` is real (since π > 0, Complex.log ↑π is real), so its Im is 0. For the second term, `Im((1/2) * w) = (1/2) * Im(w)`.

Key steps:
1. rw [RvMRightEdge.logDeriv_GammaR_eq s hs]
2. simp [Complex.add_im, Complex.mul_im] to simplify Im of the sum
3. Show Im(Complex.log ↑π) = 0 (since π > 0, ↑π is a positive real, and Complex.log of a positive real has Im = 0, via Complex.ofReal_log or Complex.log_ofReal_re)
4. Use Complex.ofReal_log (le_of_lt Real.pi_pos) or show that arg(↑π) = 0
-/
theorem im_logDeriv_GammaR_eq (s : ℂ) (hs : 0 < s.re) :
    (logDeriv Gammaℝ s).im = (1 / 2) * (logDeriv Complex.Gamma (s / 2)).im := by
  rw [ RvMRightEdge.logDeriv_GammaR_eq s hs ] ; norm_num [ Complex.ext_iff ] ; ring;
  norm_num [ Complex.log_im ];
  rw [ Complex.arg_ofReal_of_nonneg Real.pi_pos.le ]

/-! ### Step 2: |Im(ψ(z))| ≤ π/2 + C/‖z‖ -/

/-
PROBLEM
For `z` with `Re(z) ≥ 1/4`, `|Im(z)| ≥ 1`, `Gamma z ≠ 0`:
    `|Im(logDeriv Gamma z)| ≤ π/2 + C/‖z‖`.

    Proof: |Im(ψ(z))| ≤ |Im(log z)| + ‖ψ(z) - log z‖
           ≤ |arg z| + C/‖z‖
           ≤ π/2 + C/‖z‖     (since Re z > 0 implies |arg z| < π/2).

PROVIDED SOLUTION
Use `DigammaAsymptotic.digamma_log_bound` which gives:
  ∃ C > 0, ∀ s, s.re ≥ 1/4 → |s.im| ≥ 1 → Gamma s ≠ 0 → ‖deriv Gamma s / Gamma s - Complex.log s‖ ≤ C / ‖s‖

Note: logDeriv Gamma z = deriv Gamma z / Gamma z (this is logDeriv_apply).

We need: |Im(logDeriv Gamma z)| ≤ π/2 + C/‖z‖.

Key argument:
  |Im(ψ(z))| = |Im(log z + (ψ(z) - log z))|
             ≤ |Im(log z)| + |Im(ψ(z) - log z)|
             ≤ |Im(log z)| + ‖ψ(z) - log z‖    (since |Im(w)| ≤ ‖w‖)
             ≤ |arg z| + C/‖z‖

For Re(z) ≥ 1/4 > 0, we have |arg z| ≤ π/2 (since arg of a number with positive real part is in (-π/2, π/2)). Actually, we need |arg z| < π/2, which gives |Im(log z)| < π/2 and so ≤ π/2.

More precisely: (Complex.log z).im = Complex.arg z, and Complex.abs_arg_le_pi gives |arg z| ≤ π. For Re z > 0, use Complex.arg_lt_pi_div_two or the fact that arg of z with Re z > 0 satisfies |arg z| < π/2.
-/
theorem im_digamma_bound :
    ∃ C > 0, ∀ z : ℂ, z.re ≥ 1/4 → |z.im| ≥ 1 → Complex.Gamma z ≠ 0 →
      |(logDeriv Complex.Gamma z).im| ≤ Real.pi / 2 + C / ‖z‖ := by
  -- Let's choose any $C > 0$ from the provided solution.
  obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ z : ℂ, z.re ≥ 1 / 4 → |z.im| ≥ 1 → Gamma z ≠ 0 → ‖deriv Gamma z / Gamma z - Complex.log z‖ ≤ C / ‖z‖ := by
    exact?;
  use C, hC_pos; intros z hz_re hz_im hz_nonzero; specialize hC z hz_re hz_im hz_nonzero; simp_all +decide [ logDeriv_apply ] ;
  -- Since $|Im(\log z)| \leq \pi/2$ for $Re(z) \geq 1/4$, we have $|Im(\psi(z))| \leq \pi/2 + C/‖z‖$.
  have h_im_log : |Complex.im (Complex.log z)| ≤ Real.pi / 2 := by
    rw [ Complex.log_im ];
    rw [ abs_le ] ; constructor <;> rw [ Complex.arg ] <;> norm_num at *;
    · split_ifs <;> linarith [ Real.neg_pi_div_two_le_arcsin ( z.im / ‖z‖ ), Real.arcsin_le_pi_div_two ( z.im / ‖z‖ ) ];
    · split_ifs <;> linarith [ Real.arcsin_le_pi_div_two ( z.im / ‖z‖ ), Real.neg_pi_div_two_le_arcsin ( z.im / ‖z‖ ) ];
  exact abs_le.mpr ⟨ by have := abs_le.mp h_im_log; have := abs_le.mp ( show |( deriv Gamma z / Gamma z - log z |> Complex.im )| ≤ C / ‖z‖ from by simpa using Complex.abs_im_le_norm ( deriv Gamma z / Gamma z - log z ) |> le_trans <| hC ) ; norm_num at * ; linarith, by have := abs_le.mp h_im_log; have := abs_le.mp ( show |( deriv Gamma z / Gamma z - log z |> Complex.im )| ≤ C / ‖z‖ from by simpa using Complex.abs_im_le_norm ( deriv Gamma z / Gamma z - log z ) |> le_trans <| hC ) ; norm_num at * ; linarith ⟩ ;

/-! ### Step 3: Pointwise bound on |Im(logDeriv Gammaℝ(x+iT))| -/

/-
PROBLEM
For `x ∈ [1/2, 2]` and `T ≥ 14`, `|Im(logDeriv Gammaℝ(x+iT))| ≤ K`.

PROVIDED SOLUTION
Use `im_logDeriv_GammaR_eq` and `im_digamma_bound`.

For x ∈ [1/2, 2] and T ≥ 14, let s = (↑x : ℂ) + (↑T : ℂ) * I.
Then Re(s) = x ≥ 1/2 > 0, so by im_logDeriv_GammaR_eq:
  |Im(logDeriv Gammaℝ s)| = |(1/2) * Im(logDeriv Gamma (s/2))|
                           = (1/2) * |Im(logDeriv Gamma z)|

where z = s/2 = x/2 + (T/2)*I. Check:
- Re(z) = x/2 ≥ 1/4 ✓
- |Im(z)| = T/2 ≥ 7 ≥ 1 ✓
- Gamma z ≠ 0 (since Re(z) = x/2 > 0, use Complex.Gamma_ne_zero_of_re_pos) ✓

By im_digamma_bound with constant C₀:
  |Im(logDeriv Gamma z)| ≤ π/2 + C₀/‖z‖ ≤ π/2 + C₀/(T/2) ≤ π/2 + C₀/7

So |Im(logDeriv Gammaℝ s)| ≤ (1/2) * (π/2 + C₀/7) = π/4 + C₀/14.

Set K = π/4 + C₀/14 (or any upper bound).

Note: ‖z‖ = ‖x/2 + (T/2)*I‖ ≥ |Im(z)| = T/2 ≥ 7, so C₀/‖z‖ ≤ C₀/7.
-/
theorem im_logDeriv_GammaR_pointwise_bound :
    ∃ K : ℝ, ∀ x T : ℝ, 1/2 ≤ x → x ≤ 2 → 14 ≤ T →
      |(logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im| ≤ K := by
  -- Use `im_logDeriv_GammaR_eq` and `im_digamma_bound` to find `K`.
  obtain ⟨C₀, hC₀_pos, hC₀⟩ : ∃ C₀ > 0, ∀ z : ℂ, z.re ≥ 1 / 4 → |z.im| ≥ 1 → Complex.Gamma z ≠ 0 → |(logDeriv Complex.Gamma z).im| ≤ Real.pi / 2 + C₀ / ‖z‖ := by
    apply im_digamma_bound;
  refine' ⟨ Real.pi / 4 + C₀ / 7, fun x T hx₁ hx₂ hx₃ => _ ⟩ ; rw [ im_logDeriv_GammaR_eq ] ; norm_num [ Complex.normSq, Complex.norm_def ] at *;
  · refine' le_trans ( mul_le_mul_of_nonneg_left ( hC₀ _ _ _ _ ) ( by positivity ) ) _ <;> norm_num [ Complex.div_re, Complex.div_im ] <;> ring <;> norm_num [ hx₁, hx₂, hx₃ ];
    · linarith;
    · rw [ abs_of_nonneg ] <;> linarith;
    · exact Complex.Gamma_ne_zero_of_re_pos ( by norm_num [ Complex.add_re, Complex.mul_re ] ; linarith );
    · rw [ ← div_eq_mul_inv, div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg ( x ^ 2 * ( 1 / 4 ) + T ^ 2 * ( 1 / 4 ) ), Real.mul_self_sqrt ( by positivity : 0 ≤ x ^ 2 * ( 1 / 4 ) + T ^ 2 * ( 1 / 4 ) ), mul_le_mul_of_nonneg_left hx₃ hC₀_pos.le ];
  · norm_num; linarith

/-! ### Step 4: Integrability -/

/-
PROBLEM
The function `x ↦ (logDeriv Gammaℝ (x + T*I)).im` is integrable on `[1/2, 2]`.

PROVIDED SOLUTION
The function x ↦ (logDeriv Gammaℝ (↑x + ↑T * I)).im is continuous on [1/2, 2] for T ≥ 14, because:
1. The map x ↦ ↑x + ↑T * I is continuous (continuous_ofReal composed with addition of constant)
2. Gammaℝ is differentiable (hence logDeriv is defined and continuous) on the open set {s | Re(s) > 0}
3. For x ∈ [1/2, 2], Re(↑x + ↑T * I) = x ≥ 1/2 > 0, so we stay in the right half-plane
4. Im is continuous

Actually a simpler approach: use the pointwise bound `im_logDeriv_GammaR_pointwise_bound`. Any bounded measurable function on a finite interval is integrable. Use `IntervalIntegrable.mono_fun` or `Measure.integrableOn_of_bounded` or `intervalIntegrable_const` and comparison.

Alternatively, use ContinuousOn.intervalIntegrable:
- logDeriv Gammaℝ is holomorphic on {Re > 0} (since Gammaℝ is meromorphic and nonzero there)
- For T ≥ 14, the line segment {x + iT : x ∈ [1/2, 2]} ⊂ {Re > 0}
- Composition with continuous Im gives a continuous real-valued function
- Continuous functions on compact intervals are integrable
-/
theorem im_logDeriv_GammaR_intervalIntegrable (T : ℝ) (hT : 14 ≤ T) :
    IntervalIntegrable
      (fun x : ℝ => (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im)
      MeasureTheory.volume (1/2 : ℝ) 2 := by
  apply_rules [ ContinuousOn.intervalIntegrable ];
  refine' ContinuousOn.congr _ _;
  exact fun x => ( 1 / 2 ) * ( logDeriv Complex.Gamma ( ( x : ℂ ) / 2 + T * Complex.I / 2 ) |> Complex.im );
  · refine' ContinuousOn.mul continuousOn_const _;
    -- The logarithmic derivative of the Gamma function is continuous on the right half-plane.
    have h_logDeriv_cont : ContinuousOn (fun z : ℂ => logDeriv Gamma z) {z : ℂ | 0 < z.re} := by
      have h_cont : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := by
        intro z hz
        have h_gamma_diff : DifferentiableAt ℂ Gamma z := by
          apply_rules [ Complex.differentiableAt_Gamma ];
          exact fun m => ne_of_apply_ne Complex.re <| by norm_num; linarith [ hz.out ] ;
        exact h_gamma_diff.differentiableWithinAt;
      refine' ContinuousOn.div _ _ _;
      · have h_cont : DifferentiableOn ℂ (deriv Gamma) {z : ℂ | 0 < z.re} := by
          apply_rules [ DifferentiableOn.deriv, h_cont ];
          exact isOpen_lt continuous_const Complex.continuous_re;
        exact h_cont.continuousOn;
      · exact h_cont.continuousOn;
      · exact?;
    exact Complex.continuous_im.comp_continuousOn ( h_logDeriv_cont.comp ( Continuous.continuousOn <| by continuity ) fun x hx => by norm_num [ Complex.add_re, Complex.div_re, Complex.mul_re ] ; linarith [ Set.mem_Icc.mp <| by norm_num at hx; exact hx ] );
  · intro x hx; convert im_logDeriv_GammaR_eq ( x + T * Complex.I ) ( by norm_num [ Complex.ext_iff ] ; cases Set.mem_uIcc.mp hx <;> linarith ) using 1 ; ring;

/-! ### Step 5: Integral bound -/

/-
PROBLEM
The integral `∫_{1/2}^{2} Im(logDeriv Gammaℝ(x+iT)) dx` is bounded by a constant.
    Combined with `log T ≥ log 14 > 0`, this gives the `O(log T)` bound.

PROVIDED SOLUTION
Use `im_logDeriv_GammaR_pointwise_bound` to get constant K bounding the integrand.
Use `im_logDeriv_GammaR_intervalIntegrable` for integrability.

Step 1: Bound the integral using the pointwise bound:
  |∫_{1/2}^{2} Im(logDeriv Gammaℝ(x+iT)) dx| ≤ ∫_{1/2}^{2} |Im(logDeriv Gammaℝ(x+iT))| dx
                                                ≤ ∫_{1/2}^{2} K dx = K * (3/2)

Use `intervalIntegral.norm_integral_le_of_norm_le` or `abs_integral_le_integral_abs` and then bound by K * (2 - 1/2).

Step 2: Multiply by 1/π:
  |-(1/π) * ∫| = (1/π) * |∫| ≤ (1/π) * K * (3/2)

Step 3: Bound by C * log T. Since T ≥ 14, log T ≥ log 14 > 0. Set C = (K * 3/2) / (π * log 14) + 1.
Then (1/π) * K * (3/2) ≤ C * log 14 ≤ C * log T.

Or more simply: the constant bound K₀ = (1/π) * K * (3/2) satisfies K₀ ≤ (K₀ / log 14) * log T for T ≥ 14 since log is monotone. Use C = K₀ / log 14 + 1 for safety (or just K₀ / log 14 if you can prove the exact inequality).
-/
theorem gamma_half_top_integral_bounded :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im)| ≤ C * Real.log T := by
  -- Use the pointwise bound to find such a constant $K$.
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ T : ℝ, 14 ≤ T → |∫ x in (1/2 : ℝ)..2, (logDeriv Gammaℝ (x + T * Complex.I)).im| ≤ K := by
    obtain ⟨ K, hK ⟩ := im_logDeriv_GammaR_pointwise_bound;
    use K * (2 - 1 / 2);
    intro T hT; rw [ intervalIntegral.integral_of_le ( by linarith ) ];
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
    exacts [ fun _ => K, Filter.Eventually.of_forall fun _ => norm_nonneg _, Continuous.integrableOn_Ioc ( by continuity ), Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun x hx => hK x T hx.1.le hx.2 hT, by norm_num [ mul_comm ] ];
  norm_num [ abs_mul, abs_of_nonneg, Real.pi_pos.le ] at *;
  use K / Real.pi / Real.log 14;
  field_simp;
  exact fun T hT => mul_le_mul ( hK T hT ) ( Real.log_le_log ( by norm_num ) hT ) ( by positivity ) ( by linarith [ abs_le.mp ( hK 14 ( by norm_num ) ) ] )

end ZetaZeros.GammaHalfTopBound