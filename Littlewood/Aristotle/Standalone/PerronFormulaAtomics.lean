/-
# Perron Formula Atomics — Gap 1: Near-Term Abel Summation

Hyper-atomized lemmas for the near-term Perron truncation error.
Each atom is small enough for the elaborator to accept directly.

## Architecture

The Perron truncation error decomposes into far terms + near terms.
- Far terms: PROVED in PerronTruncationAtomics.truncation_far_terms
- Near terms: THIS FILE, via Abel partial summation + Chebyshev ψ ≤ 6x

## Key reuse
- AbelSummation.abel_summation_by_parts (proved, 0 sorry)
- PerronTruncationAtomics.truncation_far_terms (proved, 0 sorry)
- ChebyshevFunctions.chebyshevPsi_le (proved: ψ ≤ 6x)
- Mathlib: intervalIntegral.integral_eq_sub_of_hasDerivAt (FTC)
- Mathlib: Real.log_div, Real.log_pos, etc.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Basic.ChebyshevFunctions

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Littlewood.PerronFormulaAtomics

open Real MeasureTheory Set Finset BigOperators

/-! ## Section 1.1: Properties of the near-term bounding function

f_near(t) = (x/T) / (t - x) for t > x. This bounds the Perron kernel error
for terms n near x. -/

/-- The near-term bounding function. -/
noncomputable def f_near (x T t : ℝ) : ℝ := (x / T) / (t - x)

/-- f_near is positive for t > x. -/
lemma f_near_pos (x T t : ℝ) (hx : 0 < x) (hT : 0 < T) (ht : x < t) :
    0 < f_near x T t := by
  unfold f_near
  exact div_pos (div_pos hx hT) (sub_pos.mpr ht)

/-- f_near is decreasing for t > x. -/
lemma f_near_antitone (x T : ℝ) (hx : 0 < x) (hT : 0 < T) :
    AntitoneOn (f_near x T) (Ioi x) := by
  intro a ha b hb hab
  simp only [f_near]
  have ha' : 0 < a - x := sub_pos.mpr (mem_Ioi.mp ha)
  exact div_le_div_of_nonneg_left (div_pos hx hT).le ha' (sub_le_sub_right hab x)

/-! ## Section 1.2: FTC single step -/

/-- FTC for a single step: f(b) - f(a) = ∫_a^b f'(t) dt -/
lemma ftc_step (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ∀ t ∈ Set.uIcc a b, HasDerivAt f (deriv f t) t)
    (hf_cont : ContinuousOn (deriv f) (Set.uIcc a b)) :
    f b - f a = ∫ t in a..b, deriv f t := by
  have hIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hint : IntervalIntegrable (deriv f) volume a b :=
    (hIcc ▸ hf_cont).intervalIntegrable_of_Icc hab
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hf t ht) hint
  linarith

/-! ## Section 1.3: Chebyshev bound application -/

/-- Chebyshev bound: ψ(t) ≤ 6t for t ≥ 1.
    Wrapper around ChebyshevExt.chebyshevPsi_le. -/
lemma psi_le_six_t (t : ℝ) (ht : 1 ≤ t) : Chebyshev.psi t ≤ 6 * t :=
  ChebyshevExt.chebyshevPsi_le t ht

/-- Pointwise bound: ψ(t) * g(t) ≤ 6t * g(t) for non-negative g, t ≥ 1. -/
lemma chebyshev_pointwise_bound (t : ℝ) (ht : 1 ≤ t)
    (g_val : ℝ) (hg : 0 ≤ g_val) :
    Chebyshev.psi t * g_val ≤ 6 * t * g_val :=
  mul_le_mul_of_nonneg_right (psi_le_six_t t ht) hg

/-! ## Section 1.4: Log algebra -/

/-- log(x/T) = log x - log T for x, T > 0. -/
lemma log_div_eq (x T : ℝ) (hx : 0 < x) (hT : 0 < T) :
    Real.log (x / T) = Real.log x - Real.log T :=
  Real.log_div hx.ne' hT.ne'

/-- log T > 0 for T > 1. -/
lemma log_pos_of_gt_one (T : ℝ) (hT : 1 < T) : 0 < Real.log T :=
  Real.log_pos hT

/-! ## Section 1.5: Near-term integral evaluation -/

/-- The integral of 1/(t-x) from a to b (for a > x) equals log(b-x) - log(a-x). -/
lemma integral_inv_sub (x a b : ℝ) (ha : x < a) (hab : a < b) :
    ∫ t in a..b, (1 : ℝ) / (t - x) = Real.log (b - x) - Real.log (a - x) := by
  have hab' : a ≤ b := le_of_lt hab
  have hab' : a ≤ b := le_of_lt hab
  have h_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => Real.log (t - x)) (1 / (t - x)) t := by
    intro t ht
    have ht_pos : 0 < t - x := by
      have : a ≤ t := (Set.uIcc_of_le hab' ▸ ht).1; linarith
    have h1 := (Real.hasDerivAt_log ht_pos.ne').comp t
      ((hasDerivAt_id t).sub (hasDerivAt_const t x))
    simp only [one_div]; convert h1 using 1; simp
  have h_int : IntervalIntegrable (fun t => 1 / (t - x)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab'
    apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
    intro t ht; exact ne_of_gt (sub_pos.mpr (lt_of_lt_of_le ha ht.1))
  linarith [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => h_deriv t ht) h_int]

/-! ## Section 1.6: Integrability and Derivative Quarks -/

/-- f_near is continuous on [a,b] for a > x. -/
lemma f_near_continuousOn (x T a b : ℝ) (ha : x < a) :
    ContinuousOn (f_near x T) (Icc a b) := by
  unfold f_near
  apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
  intro t ht; exact ne_of_gt (sub_pos.mpr (lt_of_lt_of_le ha ht.1))

/-- f_near is integrable on [a,b] for a > x. -/
lemma f_near_integrableOn (x T a b : ℝ) (ha : x < a) (hab : a ≤ b) :
    IntegrableOn (f_near x T) (Icc a b) :=
  (f_near_continuousOn x T a b ha).integrableOn_compact isCompact_Icc

/-- Derivative of f_near at t > x. -/
lemma f_near_hasDerivAt (x T t : ℝ) (ht : x < t) :
    HasDerivAt (f_near x T) (-(x / T) / (t - x) ^ 2) t := by
  unfold f_near
  have h_ne : t - x ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have h1 := (hasDerivAt_const t (x / T)).div
    ((hasDerivAt_id t).sub (hasDerivAt_const t x)) h_ne
  simp only [zero_mul, sub_zero, mul_one, zero_sub] at h1
  exact h1

/-! ## Section 1.7: Complex-to-Real Commutation Quarks -/

/-- Re commutes with finite sums. -/
lemma sum_re_commute (S : Finset ℂ) (f : ℂ → ℂ) :
    (∑ w ∈ S, f w).re = ∑ w ∈ S, (f w).re :=
  map_sum Complex.reCLM _ _

/-- Re of real scalar multiplication. -/
lemma re_real_scalar_mul (c : ℝ) (z : ℂ) :
    (↑c * z).re = c * z.re := by
  simp [Complex.mul_re]

/-- Re distributes over mult-weighted residue. -/
lemma isolate_mult_re (x : ℝ) (ρ : ℂ) (m_rho : ℕ) :
    (-(↑m_rho : ℂ) * (x : ℂ) ^ ρ / ρ).re = -(m_rho : ℝ) * ((x : ℂ) ^ ρ / ρ).re := by
  simp [Complex.neg_re, Complex.mul_re, Complex.div_re]
  ring

/-- Pure algebraic identity for Gap 3 phantom. -/
lemma gap_3_phantom (A B C D E F : ℝ)
    (h_assembly : A = B - C) (h_B : B = D + E) (h_C : C = F) :
    A - D + F = E := by linarith

/-- Triangle inequality for three-piece decomposition. -/
lemma three_piece_triangle (A B C D : ℝ) (h_eq : A = B + C + D) :
    |A| ≤ |B| + |C| + |D| := by
  rw [h_eq]; linarith [abs_add_le (B + C) D, abs_add_le B C]

end Littlewood.PerronFormulaAtomics
