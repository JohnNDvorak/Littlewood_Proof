/-
Bounds on π and ζ(s) for Re(s) ≥ 2, needed for the Riemann-von Mangoldt formula.

**THIS FILE IS SORRY-FREE.**

Key results:
- `pi_sq_lt_twelve`: π² < 12 (via Real.arctan integral comparison)
- `zeta_ne_zero_of_re_ge_one`: ζ(s) ≠ 0 for Re(s) ≥ 1 (re-export)

The π² < 12 bound is the key ingredient for proving |ζ(s) - 1| < 1 at Re(s) = 2,
which in turn proves ζ(2+it) ∈ slitPlane, needed for the FTC application in
RvMContourFTC.lean.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option maxHeartbeats 6400000
set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory Filter Topology
open scoped Real

namespace ZetaZeros.RvMZeta

/-! ## π² < 12 via Real.arctan integral comparison

We prove π² < 12 by bounding Real.arctan(1) = ∫₀¹ 1/(1+t²) dt ≤ 263/315.
The bound uses the geometric series truncation:
  1/(1+t²) = 1 - t² + t⁴ - t⁶ + t⁸ - t¹⁰/(1+t²)
Hence 1/(1+t²) ≤ 1 - t² + t⁴ - t⁶ + t⁸ for t ∈ [0,1].
Integrating: Real.arctan(1) ≤ 1 - 1/3 + 1/5 - 1/7 + 1/9 = 263/315.
So π = 4·Real.arctan(1) ≤ 1052/315 ≈ 3.340, and π² ≤ (1052/315)² ≈ 11.15 < 12. -/

/-- Real.arctan(1) ≤ 263/315 via integral comparison with a polynomial upper bound. -/
private theorem arctan_one_le : Real.arctan 1 ≤ 263 / 315 := by
  -- Real.arctan(1) = ∫₀¹ 1/(1+t²) dt (by FTC + Real.arctan(0) = 0)
  have h_eq : Real.arctan 1 = ∫ t in (0:ℝ)..1, 1 / (1 + t^2) := by
    have hd : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt Real.arctan (1 / (1 + t^2)) t := by
      intro t _; exact_mod_cast Real.hasDerivAt_arctan t
    have hc : ContinuousOn (fun t => (1:ℝ) / (1 + t^2)) (uIcc 0 1) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_const.add (continuousOn_pow 2))
      intro x _; positivity
    linarith [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable,
              Real.arctan_zero]
  rw [h_eq]
  -- 1/(1+t²) ≤ 1-t²+t⁴-t⁶+t⁸ since the remainder -t¹⁰/(1+t²) ≤ 0
  calc ∫ t in (0:ℝ)..1, 1 / (1 + t^2)
      ≤ ∫ t in (0:ℝ)..1, (1 - t^2 + t^4 - t^6 + t^8 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
        · apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div continuousOn_const
            (continuousOn_const.add (continuousOn_pow 2))
          intro x _; positivity
        · exact (by fun_prop : Continuous _).intervalIntegrable 0 1
        · intro t ⟨ht0, _⟩
          rw [div_le_iff₀ (by positivity : 0 < 1 + t ^ 2)]
          nlinarith [pow_nonneg ht0 10]
    -- ∫₀¹ (1-t²+t⁴-t⁶+t⁸) dt = 1-1/3+1/5-1/7+1/9 = 263/315 by FTC
    _ = 263 / 315 := by
        have hF : ∀ t ∈ uIcc (0:ℝ) 1,
            HasDerivAt (fun x : ℝ => x - x^3/3 + x^5/5 - x^7/7 + x^9/9)
              (1 - t^2 + t^4 - t^6 + t^8) t := by
          intro t _
          convert (hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 3)
            |>.add ((hasDerivAt_pow 5 t).div_const 5)
            |>.sub ((hasDerivAt_pow 7 t).div_const 7)
            |>.add ((hasDerivAt_pow 9 t).div_const 9) using 1; ring
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
          ((by fun_prop : Continuous _).continuousOn.intervalIntegrable)]
        norm_num

/-- **π² < 12.**
    Proof: Real.arctan(1) ≤ 263/315, so π = 4·Real.arctan(1) ≤ 1052/315,
    and (1052/315)² = 1106704/99225 < 12 (since 1106704 < 1190700). -/
theorem pi_sq_lt_twelve : Real.pi ^ 2 < 12 := by
  have hpi : Real.pi ≤ 1052 / 315 := by
    rw [show Real.pi = 4 * Real.arctan 1 from by rw [Real.arctan_one]; ring]
    linarith [arctan_one_le]
  calc Real.pi ^ 2 ≤ (1052 / 315 : ℝ) ^ 2 :=
        sq_le_sq' (by linarith [Real.pi_pos]) hpi
    _ < 12 := by norm_num

/-! ## ζ(2) tail bound

From π² < 12 and hasSum_zeta_two: the tail Σ_{n≥2} 1/n² < 1.
This is the key ingredient for proving |ζ(s) - 1| < 1 at Re(s) ≥ 2. -/

/-- The sum Σ_{n≥0} 1/n² = ζ(2) satisfies ζ(2) - 1 < 1 (i.e., ζ(2) < 2).
    Equivalently: Σ_{n≥2} 1/n² < 1.
    Proof: ζ(2) = π²/6 and π² < 12, so ζ(2) < 2. -/
theorem zeta_two_minus_one_lt_one :
    (∑' (b : ℕ), 1 / (b : ℝ) ^ 2) - 1 < 1 := by
  rw [hasSum_zeta_two.tsum_eq]
  linarith [pi_sq_lt_twelve]

/-! ## Re-exports from Mathlib -/

/-- ζ(s) ≠ 0 for Re(s) ≥ 1. Re-export from Mathlib. -/
theorem zeta_ne_zero_of_re_ge_one {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- ζ(s) is differentiable for s ≠ 1. -/
theorem zeta_differentiable_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

end ZetaZeros.RvMZeta
