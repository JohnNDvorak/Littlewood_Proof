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

/-- The corrected xi function using completedRiemannZeta₀ (which is entire).
    This is the proper formulation that IS differentiable everywhere. -/
noncomputable def xi_Mathlib_corrected (s : ℂ) : ℂ :=
  (1/2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

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

/-- xi_Mathlib_corrected is entire (differentiable everywhere on ℂ).
    This is the proper formulation using completedRiemannZeta₀. -/
theorem xi_Mathlib_corrected_entire : Differentiable ℂ xi_Mathlib_corrected := by
  unfold xi_Mathlib_corrected
  have h1 : Differentiable ℂ (fun s => s * (s - 1) * completedRiemannZeta₀ s + 1) :=
    Differentiable.add
      (Differentiable.mul (differentiable_id.mul (differentiable_id.sub_const _))
        differentiable_completedZeta₀)
      (differentiable_const _)
  exact Differentiable.const_mul h1 _

/-- xi_Mathlib equals xi_Mathlib_corrected for s ≠ 0, 1 -/
theorem xi_Mathlib_eq_corrected (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi_Mathlib s = xi_Mathlib_corrected s := by
  unfold xi_Mathlib xi_Mathlib_corrected
  have h := completedRiemannZeta_eq s
  -- completedRiemannZeta s = completedRiemannZeta₀ s - 1/s - 1/(1-s)
  rw [h]
  have hs1 : 1 - s ≠ 0 := by intro heq; apply h1; rw [sub_eq_zero] at heq; exact heq.symm
  field_simp [h0, hs1]
  ring

-- DEPRECATED AND FALSE: xi_Mathlib as literally defined is NOT differentiable at s=0,1.
-- Use xi_Mathlib_corrected_entire instead.
-- The issue: completedRiemannZeta takes a finite value at its poles, so
-- xi_Mathlib(1) = 0 while lim_{s→1} xi_Mathlib(s) = 1/2, making it discontinuous.
-- See xi_Literal_not_differentiable in XiDifferentiability.lean for the full proof.
-- theorem xi_Mathlib_differentiable : Differentiable ℂ xi_Mathlib := by
--   sorry  -- FALSE: See XiDifferentiability.lean

-- zetaZeroCount_via_argument: REMOVED from build.
--   This theorem required the argument principle (not in Mathlib) and was
--   never consumed by any other file. The sorry contributed to the warning
--   count without being on the critical path. Preserved in
--   Aristotle/ZeroCountingXi.lean for future use.
--
-- zetaZeroCount_asymp (Riemann-von Mangoldt formula): REMOVED from build.
--   Depended on zetaZeroCount_via_argument + Stirling's approximation for
--   arg(Γ). Neither ingredient is in Mathlib. Not consumed by any other file.
--
-- riemann_von_mangoldt (vacuous version): REMOVED.
--   The proof was vacuous (C depended on T). See
--   RiemannVonMangoldt.lean:riemann_von_mangoldt_conditional for a genuine
--   conditional version.

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

/-- xi_Mathlib equals RiemannXi when Re(s) > 0 (so Gammaℝ(s) ≠ 0).
    For Re(s) ≤ 0, RiemannXi has spurious zeros from Gamma(s/2) = 0. -/
lemma xi_Mathlib_eq_RiemannXi (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hs_re : 0 < s.re) :
    xi_Mathlib s = RiemannXi s := by
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs_re
  suffices h : completedRiemannZeta s =
      (↑Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s by
    unfold xi_Mathlib RiemannXi; rw [h]; ring
  rw [show (↑Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) = Gammaℝ s from (Gammaℝ_def s).symm,
      riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ hG]

end
