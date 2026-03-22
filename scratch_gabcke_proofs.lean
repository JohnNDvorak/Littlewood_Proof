/-
scratch_gabcke_proofs.lean — Agent 2v4 research on sorry #1 (gabcke_next_order_bound)

## What sorry #1 needs

gabcke_next_order_bound (RSExpansionProof.lean:3158):
  ∀ k t, hardyStart k ≤ t → t ≤ hardyStart(k+1) → t > 0 →
    |ErrorTerm t - (-1)^k · (2π/t)^{1/4} · Ψ(blockParam k t)|
    ≤ (2π/t)^{1/4} · (1/4) · t^{-1/2}

## Decomposition

The bound factors as: amplitude × next-order-coefficient
  amplitude = (2π/t)^{1/4}
  next-order = (1/4) · t^{-1/2}

The FresnelSaddlePointInfra already proves:
  - quartic_coefficient: φ⁽⁴⁾(w₀)/24 = π²/t
  - quartic_ratio_le_quarter: π/(2t) ≤ 1/4 for t ≥ 2π
  - next_order_factorization: (2π/t)^{1/4} · (1/4) · t^{-1/2} = (1/4)·(2π)^{1/4}·t^{-3/4}
  - gabcke_coefficient_chain: full verification

## The genuine content

What remains is connecting ErrorTerm to the saddle-point expansion.
The argument (Siegel 1932 §3, Gabcke 1979 Satz 1):

1. ErrorTerm = Re(e^{iθ} · contour_integral)
   where the contour integral is ∫_C Γ(s)·(2πi)^{-s} ds on a vertical line

2. Deform contour to pass through saddle w₀ = √(t/(2π))

3. At the saddle, expand the phase to get:
   - Leading: Fresnel integral → gives (2π/t)^{1/4} · Ψ(p)
   - Next order: cubic + quartic corrections → bounded by (1/4) · t^{-1/2}

4. The bound |c₁(p)| ≤ 1/4 is the Gabcke content (his Tabelle 1 gives ≈ 0.083)

## AXLE-verified sub-lemmas below (8 of 9 PASS, 1 needs t ≥ 4π)
-/

import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Real Nat Classical Pointwise
set_option maxHeartbeats 800000

noncomputable section

open Complex Real Set Filter MeasureTheory

/-! ## Sub-lemma 1: cos perturbation bound [AXLE PASS]
    |cos(α + δ) - cos(α)| ≤ |δ| for all α, δ.
    Used when the phase at the saddle picks up a correction δ. -/

theorem cos_sub_cos_le_abs (α δ : ℝ) :
    |Real.cos (α + δ) - Real.cos α| ≤ |δ| := by
  have key : LipschitzWith 1 Real.cos := Real.lipschitzWith_cos
  have h := key.dist_le_mul (α + δ) α
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, show α + δ - α = δ from by ring] at h
  exact h

/-! ## Sub-lemma 2: |sin(x)| ≤ |x| [AXLE PASS]
    From Lipschitz bound. -/

theorem sin_abs_le (x : ℝ) : |Real.sin x| ≤ |x| := by
  have h := Real.lipschitzWith_sin.dist_le_mul x 0
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, Real.sin_zero, sub_zero] at h
  exact h

/-! ## Sub-lemma 3: rpow product identities [AXLE PASS] -/

/-- t^{-1/4} · t^{-1/2} = t^{-3/4} for t > 0. -/
theorem rpow_neg_quarter_mul_neg_half (t : ℝ) (ht : 0 < t) :
    t ^ (-(1 : ℝ)/4) * t ^ (-(1 : ℝ)/2) = t ^ (-(3 : ℝ)/4) := by
  rw [← Real.rpow_add ht]
  congr 1; ring

/-- (2π/t)^{1/4} = (2π)^{1/4} · t^{-1/4} for t > 0. -/
theorem two_pi_div_rpow_split (t : ℝ) (ht : 0 < t) :
    (2 * Real.pi / t) ^ ((1 : ℝ)/4) =
    (2 * Real.pi) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) := by
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [Real.div_rpow h2pi ht.le]
  rw [div_eq_mul_inv]
  congr 1
  rw [← Real.rpow_neg ht.le]
  congr 1; ring

/-- The full amplitude product:
    (2π/t)^{1/4} · (1/4) · t^{-1/2} = (1/4) · (2π)^{1/4} · t^{-3/4}. -/
theorem amplitude_next_order_product (t : ℝ) (ht : 0 < t) :
    (2 * Real.pi / t) ^ ((1 : ℝ)/4) * ((1 : ℝ)/4 * t ^ (-(1 : ℝ)/2)) =
    (1 : ℝ)/4 * (2 * Real.pi) ^ ((1 : ℝ)/4) * t ^ (-(3 : ℝ)/4) := by
  rw [two_pi_div_rpow_split t ht]
  rw [show (2 * Real.pi) ^ ((1:ℝ)/4) * t ^ (-(1:ℝ)/4) * ((1:ℝ)/4 * t ^ (-(1:ℝ)/2)) =
      (1:ℝ)/4 * (2 * Real.pi) ^ ((1:ℝ)/4) * (t ^ (-(1:ℝ)/4) * t ^ (-(1:ℝ)/2)) from by ring]
  rw [rpow_neg_quarter_mul_neg_half t ht]

/-! ## Sub-lemma 4: (2π)^{1/4} < 2 [AXLE PASS]
    Needed for constant compatibility: (1/4)·(2π)^{1/4} < 1/2. -/

theorem two_pi_rpow_quarter_lt_two : (2 * Real.pi) ^ ((1 : ℝ)/4) < 2 := by
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have h16_eq : (16 : ℝ) ^ ((1 : ℝ)/4) = 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) from by norm_num,
        ← Real.rpow_natCast (2 : ℝ) 4,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    simp only [Nat.cast_ofNat]; norm_num
  rw [← h16_eq]
  exact Real.rpow_lt_rpow (by positivity) (by linarith) (by norm_num)

/-! ## Sub-lemma 5: Hermite polynomial H₃ bound [AXLE PASS]
    |x³ - 3x| ≤ 2 for |x| ≤ √3.
    This bounds the Fresnel coefficient c₁(p) (Gabcke 1979 eq. 3.12). -/

theorem hermite3_bound (x : ℝ) (hx : |x| ≤ Real.sqrt 3) :
    |x ^ 3 - 3 * x| ≤ 2 := by
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h_abs_sq : |x| * |x| ≤ 3 := by
    calc |x| * |x| ≤ Real.sqrt 3 * Real.sqrt 3 := mul_le_mul hx hx (abs_nonneg x) (by positivity)
      _ = 3 := hsq3
  have h_sq : x ^ 2 ≤ 3 := by
    have : x ^ 2 = |x| * |x| := by have := sq_abs x; rw [sq] at this; linarith
    linarith
  have h_factor : x ^ 3 - 3 * x = x * (x ^ 2 - 3) := by ring
  rw [h_factor, abs_mul]
  have h_neg : x ^ 2 - 3 ≤ 0 := by linarith
  rw [abs_of_nonpos h_neg]
  have habs := abs_nonneg x
  have h_x2 : x ^ 2 = |x| * |x| := by have := sq_abs x; rw [sq] at this; linarith
  suffices h : |x| * (3 - |x| * |x|) ≤ 2 by rw [h_x2]; linarith
  -- 2 - |x|(3 - |x|²) = (|x|-1)²(|x|+2) ≥ 0
  have key : 0 ≤ (|x| - 1) ^ 2 * (|x| + 2) := by positivity
  nlinarith

/-! ## Sub-lemma 6: Steepest descent c₁ coefficient [AXLE PASS with t ≥ 4π]
    The coefficient from the cubic/quartic phase corrections.
    Note: needs t ≥ 4π (not just 2π) for the bound to hold. Since
    hardyStart(0) = 2π and hardyStart(1) = 8π > 4π, this covers all
    blocks k ≥ 1. Block k=0 can be handled separately. -/

theorem steepest_descent_c1_bound (t : ℝ) (ht : 4 * Real.pi ≤ t) :
    3 / (64 * t) + 5 * Real.pi / (96 * t ^ 2) ≤ 1 / (16 * t) := by
  have ht_pos : 0 < t := by linarith [Real.pi_pos]
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  rw [div_add_div _ _ (show (64 * t : ℝ) ≠ 0 by positivity) (show (96 * t ^ 2 : ℝ) ≠ 0 by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (t - 4 * Real.pi)]

/-! ## Sub-lemma 7: rpow monotonicity [AXLE PASS]
    t^{-1/2} ≤ (2π)^{-1/2} for t ≥ 2π. -/

theorem rpow_neg_half_le_on_block (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    t ^ (-(1 : ℝ)/2) ≤ (2 * Real.pi) ^ (-(1 : ℝ)/2) := by
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  exact Real.rpow_le_rpow_of_nonpos h2pi_pos ht (by norm_num)

/-! ## Sub-lemma 8: Saddle scale lower bound [AXLE PASS]
    w₀ = √(t/(2π)) ≥ k+1 when t ≥ 2π(k+1)². -/

theorem saddle_scale_lower_bound (k : ℕ) (t : ℝ)
    (ht : 2 * Real.pi * ((k : ℝ) + 1) ^ 2 ≤ t) :
    (k : ℝ) + 1 ≤ Real.sqrt (t / (2 * Real.pi)) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have h2pi : 0 < 2 * Real.pi := by positivity
  rw [show (k : ℝ) + 1 = Real.sqrt (((k : ℝ) + 1) ^ 2) from
      (Real.sqrt_sq hk.le).symm]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ h2pi]
  linarith

/-! ## Mathlib availability check -/

-- Gaussian integral (steepest descent leading term)
#check integral_gaussian

-- Taylor remainder bound (for bounding higher-order terms)
#check taylor_mean_remainder_bound

-- Circle integral norm bound
#check circleIntegral.norm_integral_le_of_norm_le_const

/-! ## Summary of research findings for sorry #1

### What exists (FresnelSaddlePointInfra + RSExpansionProof):
1. Coefficient chain: quartic → ratio → ≤ 1/4 (PROVED)
2. Amplitude factorization: (2π/t)^{1/4} · C·t^{-1/2} = C·(2π)^{1/4}·t^{-3/4} (PROVED)
3. Constant compatibility: C₁ = 1/4 satisfies C₁·(2π)^{1/4} ≤ 1/2 (PROVED)
4. Phase matching: (-1)^k · Ψ(p) matches the RS phase (PROVED, definitional)
5. Cos perturbation: |cos(α+δ) - cos(α)| ≤ |δ| (PROVED here, sub-lemma 1)
6. Phase error bounds: various O(p²/(k+1)²) estimates (PROVED in RSExpansionProof)

### AXLE-verified sub-lemmas in this file (8 PASS):
1. cos_sub_cos_le_abs — cos perturbation Lipschitz bound
2. sin_abs_le — |sin(x)| ≤ |x|
3. rpow_neg_quarter_mul_neg_half — rpow exponent addition
4. two_pi_div_rpow_split — amplitude split into (2π)^{1/4} · t^{-1/4}
5. amplitude_next_order_product — full (2π/t)^{1/4}·(1/4)·t^{-1/2} factorization
6. two_pi_rpow_quarter_lt_two — (2π)^{1/4} < 2
7. hermite3_bound — H₃ polynomial bound |x³-3x| ≤ 2 on [-√3,√3]
8. steepest_descent_c1_bound — c₁ coefficient ≤ 1/(16t) for t ≥ 4π
9. rpow_neg_half_le_on_block — t^{-1/2} monotonicity
10. saddle_scale_lower_bound — w₀ ≥ k+1 on block k

### What's MISSING (the irreducible content):
The sorry needs a connection from ErrorTerm to the saddle-point integral.
Specifically, one needs either:

(A) **Direct approach**: A theorem that ErrorTerm(t) can be written as
    (-1)^k · (2π/t)^{1/4} · [Ψ(p) + R(t,p)]
    where |R(t,p)| ≤ (1/4) · t^{-1/2}.
    This requires the full Siegel contour integral representation
    and steepest-descent evaluation.

(B) **Modular approach**: Factor through an intermediate representation:
    Step 1: ErrorTerm = Re(e^{iθ} · contour_integral)  [exists: errorTerm_eq_re_remainder]
    Step 2: contour_integral ~ saddle_expansion         [MISSING: needs contour deformation]
    Step 3: saddle_expansion remainder ≤ (1/4)·t^{-1/2}  [partially proved in infrastructure]

    Step 2 is the hard part. It requires:
    - Defining the Siegel contour (vertical line Re(s) = 1/2)
    - Deforming to the steepest-descent path through w₀
    - Bounding the remainder of the Taylor expansion at the saddle
    - Mathlib has NO steepest descent lemma and NO contour deformation

### Mathlib availability:
- CircleIntegral: circle contour integrals ✓
- norm_integral_le_of_norm_le_const: ‖∮‖ ≤ 2πR·C ✓
- hasFPowerSeriesOnBall: power series from Cauchy ✓
- taylor_mean_remainder_bound: Taylor remainder ✓
- integral_exp_neg_mul_sq: Gaussian integral ✓
- LipschitzWith for cos, sin ✓
- NO vertical line integrals (only placeholder in ContourIntegration.lean)
- NO steepest descent lemma
- NO general contour deformation

### Recommendation:
Sorry #1 is genuinely IRREDUCIBLE without either:
  (a) A hypothesis bridge (axiom for the contour deformation step), or
  (b) Building ~500 lines of steepest-descent infrastructure from scratch

The most pragmatic path is (a): introduce a hypothesis
  `ContourDeformationHyp` that encapsulates the Siegel integral representation
  ErrorTerm = (-1)^k · (2π/t)^{1/4} · [Ψ(p) + c₁(p)·(2π/t)^{1/2} + O(t^{-1})]
and then use the existing coefficient chain + the sub-lemmas here to close the bound.

The sub-lemmas above provide all the algebraic/analytic scaffolding needed
once the contour representation step is available.
-/

end
