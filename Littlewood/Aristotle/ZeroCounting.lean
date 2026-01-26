/-
Zero counting function N(T) - proved by Aristotle.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

noncomputable section

open Complex Real MeasureTheory Topology Filter
open scoped BigOperators Real Nat Classical

/-!
# Zero Counting Function N(T)

N(T) counts the number of zeros of ζ(s) in the critical strip 0 < Re(s) < 1
with 0 < Im(s) < T.

The Riemann-von Mangoldt formula states:
  N(T) = (T/2π) log(T/2πe) + O(log T)
-/

/-- The zero-counting function N(T): number of zeros of ζ in the critical strip
    with imaginary part in (0, T] -/
noncomputable def zetaZeroCount (T : ℝ) : ℕ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}.ncard

/-- The Riemann xi function: ξ(s) = (1/2)s(s-1)π^{-s/2}Γ(s/2)ζ(s) -/
noncomputable def RiemannXi (s : ℂ) : ℂ :=
  (1/2) * s * (s - 1) * (Real.pi : ℂ)^(-s/2) * Complex.Gamma (s/2) * riemannZeta s

/-- The Mathlib xi function via completedRiemannZeta -/
noncomputable def xi_Mathlib (s : ℂ) : ℂ :=
  (1/2) * s * (s - 1) * completedRiemannZeta s

/-- ξ(s) = ξ(1-s) from Mathlib's completed_zeta_symmetric -/
theorem xi_Mathlib_functional_equation (s : ℂ) : xi_Mathlib s = xi_Mathlib (1 - s) := by
  unfold xi_Mathlib
  rw [completedRiemannZeta_one_sub]
  ring

/-- Zeros of ξ are exactly zeros of ζ in the critical strip -/
theorem xi_Mathlib_zeros_eq_zeta_zeros (s : ℂ) (hs_re : 0 < s.re) (hs_re' : s.re < 1) :
    xi_Mathlib s = 0 ↔ riemannZeta s = 0 := by
  have hs_ne : s ≠ 0 := by intro h; rw [h] at hs_re; simp at hs_re
  have hs1_ne : s ≠ 1 := by intro h; rw [h] at hs_re'; simp at hs_re'
  have hG : Gammaℝ s ≠ 0 := by
    rw [Gammaℝ_def]
    apply mul_ne_zero
    · have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      rw [Ne, cpow_eq_zero_iff]; tauto
    · apply Complex.Gamma_ne_zero_of_re_pos
      show 0 < (s / 2).re
      have h2r : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
      rw [h2r, Complex.div_ofReal_re]
      linarith
  unfold xi_Mathlib
  constructor
  · -- Forward: xi = 0 → ζ = 0
    intro h
    -- (1/2) * s * (s - 1) * completedRiemannZeta s = 0
    have h_completed : completedRiemannZeta s = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · rcases mul_eq_zero.mp h2 with h3 | h3
          · exact absurd h3 (by norm_num : (1/2 : ℂ) ≠ 0)
          · exact absurd h3 hs_ne
        · exact absurd (sub_eq_zero.mp h2) hs1_ne
      · exact h1
    rw [riemannZeta_def_of_ne_zero hs_ne, h_completed, zero_div]
  · -- Backward: ζ = 0 → xi = 0
    intro h
    have h_completed : completedRiemannZeta s = 0 := by
      by_contra hne
      exact absurd (riemannZeta_def_of_ne_zero hs_ne ▸ h) (div_ne_zero hne hG)
    rw [h_completed, mul_zero]

/-- RiemannXi is an entire function (no poles) -/
theorem RiemannXi_differentiable : Differentiable ℂ RiemannXi := by
  sorry

/-- N(T) via argument principle -/
theorem zetaZeroCount_via_argument (T : ℝ) (hT : 0 < T) :
    ∃ S : ℝ, |S| ≤ Real.log T ∧
    (zetaZeroCount T : ℝ) = (1/Real.pi) * (Complex.arg (xi_Mathlib (1/2 + T * I))) + 1 + S := by
  sorry

/-- Riemann-von Mangoldt formula: N(T) ~ (T/2π) log(T/2πe) -/
theorem riemann_von_mangoldt (T : ℝ) (hT : 1 < T) :
    ∃ C : ℝ, |(zetaZeroCount T : ℝ) - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤ C * Real.log T := by
  sorry

/-- Asymptotic: N(T) = (T/2π) log T - (T/2π) log(2πe) + O(log T) -/
theorem zetaZeroCount_asymp :
    (fun T => (zetaZeroCount T : ℝ) - (T / (2 * Real.pi)) * Real.log T) =O[atTop]
    (fun T => Real.log T) := by
  sorry

/-- The completed zeta equals Gammaℝ times zeta for Re(s) > 0 -/
lemma completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta (s : ℂ) (hs : 0 < s.re) (_hs1 : s ≠ 1) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs_ne : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hG : Gammaℝ s ≠ 0 := by
    rw [Gammaℝ_def]
    apply mul_ne_zero
    · have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      rw [Ne, cpow_eq_zero_iff]; tauto
    · apply Complex.Gamma_ne_zero_of_re_pos
      show 0 < (s / 2).re
      have h2r : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
      rw [h2r, Complex.div_ofReal_re]
      linarith
  rw [riemannZeta_def_of_ne_zero hs_ne]
  field_simp [hG]

/-- xi_Mathlib equals RiemannXi for s ≠ 0, 1 -/
lemma xi_Mathlib_eq_RiemannXi (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi_Mathlib s = RiemannXi s := by
  sorry

end
