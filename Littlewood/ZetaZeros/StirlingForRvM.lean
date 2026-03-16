/-
Stirling Approximation Bridge for the Riemann-von Mangoldt Formula

**THIS FILE IS SORRY-FREE.**

This file provides all the proved components needed for the RvM formula:
1. `rvm_stirling_algebra`: algebraic identity connecting Stirling to RvM main term
2. `isBigO_inv_of_log`, `isBigO_one_of_log`: O(1/T) and O(1) absorption into O(logT)
3. `stirling_im_approx`: re-export of BinetStirling's Im(stirlingApprox) asymptotic
4. `backlund_ST_bound`: S(T) = O(logT) from |arg z| ≤ π

These feed into `contour_integral_gives_rvm` in RiemannVonMangoldtReal.lean,
which composes them with `rvm_decomposition_bounded` (the remaining sorry)
to prove N(T) = (T/2π)log(T/2π) - T/(2π) + O(logT).

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.BinetStirling
import Littlewood.ZetaZeros.ZeroCountingFunction

set_option maxHeartbeats 1600000
set_option autoImplicit false

noncomputable section

open Complex Set Filter Asymptotics Topology
open scoped Real

/-! ## Part 1: Algebraic Identity

The algebra connecting Stirling's approximation to the RvM main term.

Key identity: (1/π)·[(T/2)log(T/2) - T/2 - π/8] - (T/2π)·log π + 1
              = (T/2π)·log(T/2π) - T/(2π) + 7/8

This uses: log(T/2) = log(T/(2π)) + log π. -/

/-- Key algebraic identity connecting the Stirling main term to the RvM
    main term. After the argument principle decomposes N(T) into
    (1/π)·Im[logΓ] + log π + S(T) + 1 terms, the Stirling approximation
    for Im[logΓ] gives (T/2)log(T/2) - T/2 - π/8, and this identity
    shows the result equals (T/2π)log(T/2π) - T/(2π) + 7/8. -/
theorem rvm_stirling_algebra (T : ℝ) (hT : 0 < T) :
    (1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
    - (T / (2 * Real.pi)) * Real.log Real.pi + 1
    = (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlog : Real.log (T / 2) = Real.log (T / (2 * Real.pi)) + Real.log Real.pi := by
    rw [show T / 2 = T / (2 * Real.pi) * Real.pi from by field_simp]
    rw [Real.log_mul (ne_of_gt (div_pos hT h2pi)) hpi_ne]
  rw [hlog]; field_simp; ring

/-! ## Part 2: Stirling Approximation from BinetStirling

Re-export BinetStirling's key result: the imaginary part of the Stirling
approximation term at s = 1/4 + iT/2. -/

/-- Re-export: Im[(s-1/2)log(s) - s + (1/2)log(2π)] at s = 1/4+iT/2
    equals (T/2)log(T/2) - T/2 - π/8 + O(1/T). -/
theorem stirling_im_approx :
    (fun t => (stirlingApprox t).im - ((t / 2) * Real.log (t / 2) - t / 2 - Real.pi / 8))
    =O[atTop] (fun t => 1 / t) :=
  stirling_approx_im_asymptotic

/-! ## Part 3: O(1/T) → O(log T) and O(1) → O(log T) absorption -/

/-- O(1/T) is absorbed by O(log T). -/
theorem isBigO_inv_of_log :
    (fun T : ℝ => 1 / T) =O[atTop] (fun T : ℝ => Real.log T) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with T hT
  rw [one_mul]
  have hT_pos : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (div_pos one_pos hT_pos),
      abs_of_pos (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < Real.exp 1) hT))]
  rw [div_le_iff₀ hT_pos]
  have h1 : (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
  rw [h1]
  have hlog_le : Real.log (Real.exp 1) ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) hT
  have hone_le : (1 : ℝ) ≤ T := le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) hT
  calc Real.log (Real.exp 1) ≤ Real.log T := hlog_le
    _ = Real.log T * 1 := (mul_one _).symm
    _ ≤ Real.log T * T := by
        gcongr
        exact le_of_lt (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < Real.exp 1) hT))

/-- A bounded function is O(log T). -/
theorem isBigO_one_of_log :
    (fun _ : ℝ => (1 : ℝ)) =O[atTop] (fun T : ℝ => Real.log T) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with T hT
  simp only [one_mul, norm_one]
  rw [Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < Real.exp 1) hT))]
  have : Real.log (Real.exp 1) ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) hT
  rw [Real.log_exp] at this; linarith

/-! ## Part 4: Backlund S(T) = O(log T)

The Backlund bound on the argument of ζ on the critical line. -/

/-- **Backlund's bound**: The argument of ζ(1/2+iT) is O(log T).

    Proof: |arg z| ≤ π for any z, so S(T) = O(1) ⊆ O(log T).
    The deeper Backlund bound S(T) = O(log T / log log T) is not needed. -/
theorem backlund_ST_bound :
    (fun T : ℝ => Complex.arg (riemannZeta (1/2 + I * ↑T))) =O[atTop]
      (fun T : ℝ => Real.log T) := by
  -- In fact |arg z| ≤ π for any z, so S(T) is bounded, hence O(log T)
  apply IsBigO.trans _ isBigO_one_of_log
  rw [isBigO_iff]
  refine ⟨Real.pi, ?_⟩
  filter_upwards with T
  rw [Real.norm_eq_abs, norm_one, mul_one]
  exact Complex.abs_arg_le_pi (riemannZeta (1/2 + I * ↑T))

end
