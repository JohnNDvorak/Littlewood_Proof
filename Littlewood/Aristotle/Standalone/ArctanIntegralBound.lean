import Mathlib

/-!
# Arctangent integral bound: sub-lemma A for Backlund's S(T) = O(log T)

The integral ∫_{1/2}^{2} (-T)/((σ-a)² + T²) dσ = arctan((2-a)/T) - arctan((1/2-a)/T).
Since arctan ∈ (-π/2, π/2), the difference lies in (-π, π), so the absolute value ≤ π.

This is a concrete calculus fact used in bounding the variation of arg(ζ'/ζ) along
horizontal segments of the RvM rectangle.
-/

set_option maxHeartbeats 1600000

open Real MeasureTheory Set intervalIntegral

noncomputable section

namespace ArctanIntegralBound

/-! ### FTC for the arctan antiderivative -/

/-- The function σ ↦ -T/((σ-a)² + T²) has antiderivative σ ↦ arctan((σ-a)/T)
when T ≠ 0. This is d/dσ[arctan((σ-a)/T)] = (1/T)/(1+((σ-a)/T)²) = T/((σ-a)²+T²). -/
private lemma hasDerivAt_arctan_shifted (a T σ : ℝ) (hT : T ≠ 0) :
    HasDerivAt (fun x => arctan ((x - a) / T)) (T / ((σ - a) ^ 2 + T ^ 2)) σ := by
  have hT2 : T ^ 2 ≠ 0 := pow_ne_zero 2 hT
  have hT2_pos : 0 < (σ - a) ^ 2 + T ^ 2 := by positivity
  -- Chain rule: d/dσ arctan((σ-a)/T) = 1/(1+((σ-a)/T)²) · (1/T)
  have h1 := Real.hasDerivAt_arctan ((σ - a) / T)
  have h2 : HasDerivAt (fun x => (x - a) / T) (1 / T) σ := by
    have := (hasDerivAt_id σ).sub (hasDerivAt_const σ a)
    simpa using this.div_const T
  have h3 := h1.comp σ h2
  -- h3 : HasDerivAt (arctan ∘ (· - a)/T) (1/(1+((σ-a)/T)²) · (1/T)) σ
  convert h3 using 1
  field_simp
  ring

/-- The integral evaluates via FTC to the arctan difference. -/
private lemma integral_eq_arctan_diff (a T : ℝ) (hT : T ≠ 0) :
    ∫ σ in (1/2 : ℝ)..(2 : ℝ), T / ((σ - a) ^ 2 + T ^ 2) =
      arctan ((2 - a) / T) - arctan (((1 : ℝ)/2 - a) / T) := by
  have hcont : Continuous (fun σ => T / ((σ - a) ^ 2 + T ^ 2)) := by
    apply Continuous.div continuous_const
    · exact ((continuous_id.sub continuous_const).pow 2).add continuous_const
    · intro x; positivity
  exact integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_arctan_shifted a T x hT)
    hcont.continuousOn.intervalIntegrable

/-! ### The arctan difference is bounded by π -/

/-- arctan(b) - arctan(c) ∈ (-π, π) for any b, c. -/
private lemma abs_arctan_sub_lt_pi (b c : ℝ) : |arctan b - arctan c| < π := by
  have h1 := neg_pi_div_two_lt_arctan b
  have h2 := arctan_lt_pi_div_two b
  have h3 := neg_pi_div_two_lt_arctan c
  have h4 := arctan_lt_pi_div_two c
  rw [abs_lt]
  constructor <;> linarith

/-! ### Main theorem -/

/-- **Arctangent integral bound.** The integral of T/((σ-a)²+T²) over [1/2, 2]
is bounded by π in absolute value, for any a ∈ ℝ and T ≠ 0. -/
theorem arctan_integral_bound (a T : ℝ) (hT : T ≠ 0) :
    |∫ σ in (1/2 : ℝ)..(2 : ℝ), T / ((σ - a) ^ 2 + T ^ 2)| ≤ π := by
  rw [integral_eq_arctan_diff a T hT]
  exact le_of_lt (abs_arctan_sub_lt_pi _ _)

/-- Variant with negated integrand (the form appearing in ζ'/ζ bounds). -/
theorem arctan_integral_bound_neg (a T : ℝ) (hT : T ≠ 0) :
    |∫ σ in (1/2 : ℝ)..(2 : ℝ), (-T) / ((σ - a) ^ 2 + T ^ 2)| ≤ π := by
  simp only [neg_div]
  rw [intervalIntegral.integral_neg]
  rw [abs_neg]
  exact arctan_integral_bound a T hT

end ArctanIntegralBound
