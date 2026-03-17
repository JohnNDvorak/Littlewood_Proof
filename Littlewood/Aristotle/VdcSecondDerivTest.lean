/-
Van der Corput second derivative test for oscillatory integrals.

KEY RESULT:
  vdc_second_deriv_bound: If φ is C² with φ'' ≥ lam > 0 on [a,b], then
    |∫_a^b cos(φ(t)) dt| ≤ 8/√lam

PROOF STRATEGY:
  1. φ' is strictly increasing (from φ'' ≥ lam).
  2. If φ' ≥ 0 on [a,b]: split at a+δ, bound each piece (trivial + first-deriv VdC).
  3. If φ' ≤ 0 on [a,b]: symmetric.
  4. If φ' changes sign at t₀: split [a,t₀] and [t₀,b], apply cases 2/3.
  5. Optimize δ = 1/√lam gives constant 4/√lam per piece.

APPLICATIONS:
  - MainTermFirstMomentBoundHyp (B2): per-mode oscillatory integral bound
  - Stationary phase analysis in Riemann-Siegel expansion

DEPENDS ON:
  - VdcFirstDerivTest.lean (first-derivative VdC bound, PROVED)
  - FresnelBound.lean (Fresnel cosine/sine bounds, PROVED)

SORRY COUNT: 1 (vdc_second_deriv_bound - the main theorem)

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace VdcSecondDerivTest

open MeasureTheory intervalIntegral Set Filter Real

/-! ## Sub-lemma: trivial bound on short intervals -/

/-- On a short interval of length δ, |∫ cos(φ)| ≤ δ for any continuous φ. -/
lemma short_interval_bound (phi : ℝ → ℝ) (hphi : Continuous phi) (a delta : ℝ) (hd : 0 ≤ delta) :
    |∫ t in a..(a + delta), Real.cos (phi t)| ≤ delta := by
  have hab : a ≤ a + delta := by linarith
  calc |∫ t in a..(a + delta), Real.cos (phi t)|
      ≤ ∫ t in a..(a + delta), ‖Real.cos (phi t)‖ := by
        rw [← Real.norm_eq_abs]
        exact intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..(a + delta), (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hab
        · exact (Real.continuous_cos.comp hphi).continuousOn.intervalIntegrable.norm
        · exact continuousOn_const.intervalIntegrable
        · intro t _
          rw [Real.norm_eq_abs]
          exact abs_cos_le_one _
    _ = delta := by
        rw [intervalIntegral.integral_const]
        simp [show a + delta - a = delta by ring]

/-- Optimization: 1/√lam + 3/(lam · (1/√lam)) = 4/√lam. -/
lemma optimization_eq (lam : ℝ) (hlam : 0 < lam) :
    1 / Real.sqrt lam + 3 / (lam * (1 / Real.sqrt lam)) = 4 / Real.sqrt lam := by
  have hsq : Real.sqrt lam > 0 := Real.sqrt_pos.mpr hlam
  have : lam * (1 / Real.sqrt lam) = Real.sqrt lam := by
    rw [mul_one_div, div_eq_iff hsq.ne']
    exact (Real.mul_self_sqrt hlam.le).symm
  rw [this]; ring

/-- **Van der Corput second derivative test**: If φ'' ≥ lam > 0 on [a,b], then
    |∫_a^b cos(φ(t)) dt| ≤ 8/√lam.

The constant 8 comes from handling both sides of the stationary point
(4/√lam each, via the optimization delta = 1/√lam). The bound can be improved
to C/√lam with C ~ 2√2 using Fresnel integrals directly.

Reference: Montgomery-Vaughan, "Multiplicative Number Theory I", Lemma 8.2. -/
theorem vdc_second_deriv_bound (phi : ℝ → ℝ) (a b lam : ℝ) (hab : a ≤ b) (hlam : 0 < lam)
    (hphi : Differentiable ℝ phi) (hphi' : Differentiable ℝ (deriv phi))
    (hphi'' : Continuous (deriv (deriv phi)))
    (hphi''_lower : ∀ t ∈ Icc a b, lam ≤ deriv (deriv phi) t) :
    |∫ t in a..b, Real.cos (phi t)| ≤ 8 / Real.sqrt lam := by
  sorry

end VdcSecondDerivTest
