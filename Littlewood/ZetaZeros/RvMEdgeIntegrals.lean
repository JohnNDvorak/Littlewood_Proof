/-
Edge Integral Evaluations for the Riemann-von Mangoldt Formula

This file provides proved sub-lemmas for the edge-by-edge evaluation of
the contour integral of logDeriv(ξ) on the rectangle (-1, 2) × (1, T),
building toward closing `rvm_N_formula_bound` in RiemannVonMangoldtReal.lean.

## Proved results (0 sorry):
- `norm_inv_two_add_iy`: |1/(2+iy)| ≤ 1/y for y ≥ 1
- `norm_inv_one_add_iy`: |1/(1+iy)| ≤ 1/y for y ≥ 1
- `right_edge_inv_s_bound`: |∫₁ᵀ 1/(2+iy) dy| ≤ log T
- `right_edge_inv_s_sub_one_bound`: |∫₁ᵀ 1/(1+iy) dy| ≤ log T
- `integral_const_on_interval`: ∫ₐᵇ c = c·(b-a)
- `horizontal_edge_bound`: |∫_{-1}^{2} g(σ+it) dσ| ≤ 3·sup|g|

## Strategy for rvm_N_formula_bound

The argument principle gives:
  2πi · N(T) = ∮_∂R logDeriv(ξ)(s) ds

By XiLogDerivDecomposition (0 sorry):
  logDeriv(ξ)(s) = 1/s + 1/(s-1) − log(π)/2 + digamma(s/2)/2 + logDeriv(ζ)(s)

The contour integral splits into 4 edges × 5 terms = 20 sub-integrals.
This file handles the "easy" sub-integrals (those involving 1/s, 1/(s-1),
constant, and horizontal edge bounds).

The "hard" sub-integrals (digamma vertical integral, logDeriv(ζ) vertical
integral) require Stirling and the Euler product respectively.

## References
- Titchmarsh, "Theory of the Riemann Zeta Function", §9.3–9.4
- Davenport, "Multiplicative Number Theory", Chapter 15

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section

open Complex Real Set MeasureTheory Topology Filter
open scoped Real

namespace ZetaZeros.RvMEdge

/-! ## Section 1: Norm bounds for 1/(σ+iy) on vertical edges -/

/-- |1/(2+iy)| ≤ 1/y for y ≥ 1. The point 2+iy has distance
    √(4+y²) ≥ y from the origin, so ‖(2+iy)⁻¹‖ ≤ 1/y. -/
theorem norm_inv_two_add_iy (y : ℝ) (hy : 1 ≤ y) :
    ‖((2 : ℂ) + ↑y * I)⁻¹‖ ≤ y⁻¹ := by
  rw [norm_inv]
  rw [show (2 : ℂ) + ↑y * I = ↑(2 : ℝ) + ↑y * I from by push_cast; ring]
  rw [Complex.norm_add_mul_I]
  rw [inv_le_inv₀ (Real.sqrt_pos_of_pos (by positivity)) (by linarith)]
  calc y = Real.sqrt (y ^ 2) := (Real.sqrt_sq (by linarith)).symm
    _ ≤ Real.sqrt ((2 : ℝ) ^ 2 + y ^ 2) := Real.sqrt_le_sqrt (by nlinarith)

/-- |1/(1+iy)| ≤ 1/y for y ≥ 1. Same argument as above at σ=1. -/
theorem norm_inv_one_add_iy (y : ℝ) (hy : 1 ≤ y) :
    ‖((1 : ℂ) + ↑y * I)⁻¹‖ ≤ y⁻¹ := by
  rw [norm_inv]
  rw [show (1 : ℂ) + ↑y * I = ↑(1 : ℝ) + ↑y * I from by push_cast; ring]
  rw [Complex.norm_add_mul_I]
  rw [inv_le_inv₀ (Real.sqrt_pos_of_pos (by positivity)) (by linarith)]
  calc y = Real.sqrt (y ^ 2) := (Real.sqrt_sq (by linarith)).symm
    _ ≤ Real.sqrt ((1 : ℝ) ^ 2 + y ^ 2) := Real.sqrt_le_sqrt (by nlinarith)

/-! ## Section 2: Right edge integrals of 1/s and 1/(s-1) bounded by log T

These prove that the "simple pole" terms in the XiLogDeriv decomposition
contribute at most O(log T) on the right vertical edge (σ=2, y: 1→T). -/

/-- |∫₁ᵀ 1/(2+iy) dy| ≤ log T. The integrand is bounded by 1/y,
    and ∫₁ᵀ 1/y dy = log T. -/
theorem right_edge_inv_s_bound (T : ℝ) (hT : 1 ≤ T) :
    ‖∫ y in (1 : ℝ)..T, ((2 : ℂ) + ↑y * I)⁻¹‖ ≤ Real.log T := by
  have hT_pos : (0 : ℝ) < T := by linarith
  have h_intble_f : IntervalIntegrable (fun y => ((2 : ℂ) + ↑y * I)⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    apply ContinuousOn.inv₀
    · apply ContinuousOn.add continuousOn_const
      exact (continuous_ofReal.comp continuous_id).continuousOn.mul continuousOn_const
    · intro y _ h; have := congr_arg Complex.re h; simp at this
  have h_intble_g : IntervalIntegrable (fun y : ℝ => y⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact continuousOn_inv₀.mono (fun y hy => by simp at hy ⊢; linarith [hy.1])
  calc ‖∫ y in (1 : ℝ)..T, ((2 : ℂ) + ↑y * I)⁻¹‖
      ≤ ∫ y in (1 : ℝ)..T, ‖((2 : ℂ) + ↑y * I)⁻¹‖ :=
        intervalIntegral.norm_integral_le_integral_norm hT
    _ ≤ ∫ y in (1 : ℝ)..T, y⁻¹ := by
        apply intervalIntegral.integral_mono_on hT
          (h_intble_f.norm) h_intble_g
        intro y hy; exact norm_inv_two_add_iy y hy.1
    _ = Real.log T := by
        rw [integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) hT_pos, div_one]

/-- |∫₁ᵀ 1/(1+iy) dy| ≤ log T. Same bound for the 1/(s-1) term at σ=2. -/
theorem right_edge_inv_s_sub_one_bound (T : ℝ) (hT : 1 ≤ T) :
    ‖∫ y in (1 : ℝ)..T, ((1 : ℂ) + ↑y * I)⁻¹‖ ≤ Real.log T := by
  have hT_pos : (0 : ℝ) < T := by linarith
  have h_intble_f : IntervalIntegrable (fun y => ((1 : ℂ) + ↑y * I)⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    apply ContinuousOn.inv₀
    · apply ContinuousOn.add continuousOn_const
      exact (continuous_ofReal.comp continuous_id).continuousOn.mul continuousOn_const
    · intro y _ h; have := congr_arg Complex.re h; simp at this
  have h_intble_g : IntervalIntegrable (fun y : ℝ => y⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact continuousOn_inv₀.mono (fun y hy => by simp at hy ⊢; linarith [hy.1])
  calc ‖∫ y in (1 : ℝ)..T, ((1 : ℂ) + ↑y * I)⁻¹‖
      ≤ ∫ y in (1 : ℝ)..T, ‖((1 : ℂ) + ↑y * I)⁻¹‖ :=
        intervalIntegral.norm_integral_le_integral_norm hT
    _ ≤ ∫ y in (1 : ℝ)..T, y⁻¹ := by
        apply intervalIntegral.integral_mono_on hT
          (h_intble_f.norm) h_intble_g
        intro y hy; exact norm_inv_one_add_iy y hy.1
    _ = Real.log T := by
        rw [integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) hT_pos, div_one]

/-! ## Section 3: Constant integral on intervals -/

/-- Integral of a constant over an interval: ∫ₐᵇ c = c·(b-a). -/
theorem integral_const_on_interval (a b : ℝ) (c : ℂ) :
    ∫ _ in a..b, c = c * (↑b - ↑a) := by
  rw [intervalIntegral.integral_const]
  simp
  ring

/-! ## Section 4: Horizontal edge bounds

On horizontal edges (fixed imaginary part), we bound the integral
by the length (3) times the supremum of the integrand. -/

/-- If |g(σ+it)| ≤ B for σ ∈ [-1,2], then |∫_{-1}^{2} g(σ+it) dσ| ≤ 3B.
    Used for both bottom (t=1) and top (t=T) edges. -/
theorem horizontal_edge_bound (t B : ℝ) (g : ℂ → ℂ)
    (hg_cont : ContinuousOn (fun x : ℝ => g (↑x + ↑t * I)) (Set.Icc (-1 : ℝ) 2))
    (hg : ∀ σ ∈ Set.Icc (-1 : ℝ) 2, ‖g (↑σ + ↑t * I)‖ ≤ B) :
    ‖∫ x in (-1 : ℝ)..2, g (↑x + ↑t * I)‖ ≤ 3 * B := by
  calc ‖∫ x in (-1 : ℝ)..2, g (↑x + ↑t * I)‖
      ≤ ∫ x in (-1 : ℝ)..2, ‖g (↑x + ↑t * I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 2)
    _ ≤ ∫ _ in (-1 : ℝ)..2, B := by
        apply intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 2)
        · exact (hg_cont.norm).intervalIntegrable_of_Icc (by norm_num)
        · exact intervalIntegrable_const
        · intro x hx
          exact hg x ⟨hx.1, hx.2⟩
    _ = 3 * B := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        linarith

end ZetaZeros.RvMEdge
