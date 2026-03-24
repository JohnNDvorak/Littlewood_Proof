/-
Fresnel integral evaluation for SiegelSaddleExpansionHyp.

We prove the regularized Fresnel integral:
  ∫ exp(-(ε - I·π)·u²) du = (π/(ε - I·π))^(1/2)  for ε > 0
and the truncated Fresnel tail bound:
  ‖∫_A^B exp(i·π·u²) du‖ ≤ 1/(π·A)  for 0 < A ≤ B.

The regularized integral follows from Mathlib's `integral_gaussian_complex`.
The tail bound follows from integration by parts.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.mathlibStandardSet false

noncomputable section

namespace FresnelSaddleProof

open MeasureTheory Set Complex Filter Real Topology

/-! ## Section 1: Regularized Fresnel integral -/

/-- The regularized Fresnel parameter: b = ε - I·π has positive real part for ε > 0. -/
private theorem regularized_fresnel_re_pos (ε : ℝ) (hε : 0 < ε) :
    0 < (↑ε - I * ↑π : ℂ).re := by
  simp [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im]
  exact hε

/-- **Regularized Fresnel integral**: for ε > 0,
    ∫ exp(-(ε - I·π)·u²) du = (π/(ε - I·π))^(1/2).

    This is a direct application of Mathlib's `integral_gaussian_complex`. -/
private theorem regularized_fresnel_integral (ε : ℝ) (hε : 0 < ε) :
    ∫ x : ℝ, cexp (-(↑ε - I * ↑π) * ↑x ^ 2) =
      (↑π / (↑ε - I * ↑π)) ^ (1 / 2 : ℂ) :=
  integral_gaussian_complex (regularized_fresnel_re_pos ε hε)

/-- The regularized Fresnel integrand equals exp(-εu²)·exp(iπu²). -/
private theorem regularized_fresnel_split (ε : ℝ) (u : ℝ) :
    cexp (-(↑ε - I * ↑π) * ↑u ^ 2) =
      cexp (-(↑ε * ↑u ^ 2)) * cexp (I * ↑π * ↑u ^ 2) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## Section 2: The Fresnel limit value

We show that as ε → 0+, (π/(ε - iπ))^(1/2) → (1 + I) / √2.

The key computation:
  π/(-iπ) = -1/i = i
  i^(1/2) = exp(iπ/4) = (1+i)/√2
-/

/-- `(1 + I) / √2` is a square root of `I`. -/
private theorem fresnel_value_sq :
    ((1 + I) / (↑(Real.sqrt 2) : ℂ)) ^ 2 = I := by
  field_simp
  ring_nf
  norm_num [Complex.ext_iff, sq] at *

/-- The Fresnel limit value has positive real part. -/
private theorem fresnel_value_re_pos :
    (0 : ℝ) < ((1 + I) / (↑(Real.sqrt 2) : ℂ)).re := by
  norm_num [div_eq_mul_inv]

/-
PROBLEM
π / (0 - I * π) = I.

PROVIDED SOLUTION
π / (0 - I*π) = π / (-I*π) = 1/(-I) = I. Simplify using field_simp then ring or norm_num. Key: -I*π ≠ 0 since I ≠ 0 and π ≠ 0.
-/
private theorem pi_div_neg_I_pi : (↑π / (0 - I * ↑π) : ℂ) = I := by
  norm_num [ div_eq_iff, Complex.ext_iff, Real.pi_ne_zero ]

/-
PROBLEM
I is in the slit plane.

PROVIDED SOLUTION
I is in the slit plane because I.im = 1 > 0 (the slit plane is {z : ℂ | 0 < z.re ∨ z.im ≠ 0}). Use Complex.slitPlane definition and show I.im = 1 ≠ 0.
-/
private theorem I_mem_slitPlane : Complex.I ∈ Complex.slitPlane := by
  exact Or.inr <| by norm_num [ Complex.ext_iff ] ;

/-
PROBLEM
cpow I (1/2) = (1+I)/√2.

PROVIDED SOLUTION
I^(1/2) = exp((1/2) * log I). log I = iπ/2 (since |I| = 1 and arg I = π/2). So I^(1/2) = exp(iπ/4) = cos(π/4) + i sin(π/4) = 1/√2 + i/√2 = (1+i)/√2. Use Complex.cpow_def, Complex.log_I, and compute exp(I*π/4). May need Complex.exp_eq_cos_add_sin or similar.
-/
private theorem cpow_I_half :
    (I : ℂ) ^ (1 / 2 : ℂ) = (1 + I) / (↑(Real.sqrt 2) : ℂ) := by
      rw [ Complex.cpow_def, Complex.log_I ] ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring ; norm_num;
      norm_num [ mul_div, Real.sqrt_div_self ]

/-
PROBLEM
As ε → 0+, the regularized Fresnel integral converges to (1+I)/√2.
    This is the fundamental Fresnel integral evaluation.

PROVIDED SOLUTION
The map ε ↦ (π/(ε - Iπ))^(1/2) is continuous at ε = 0 (from the right), and at ε = 0, π/(0 - Iπ) = I (by pi_div_neg_I_pi), and I^(1/2) = (1+I)/√2 (by cpow_I_half).

Strategy: show the function ε ↦ (π/(ε - Iπ))^(1/2) is continuous at 0 by:
1. ε ↦ (↑ε - I*↑π) is continuous (obvious)
2. ε ↦ ↑π / (↑ε - I*↑π) is continuous at 0 since (0 - I*↑π) ≠ 0
3. z ↦ z^(1/2) is continuous at I since I ∈ slitPlane (by I_mem_slitPlane)
4. The composition is continuous at 0, and its value at 0 is I^(1/2) = (1+I)/√2

Use Filter.Tendsto.comp and Continuous.tendsto. The nhdsWithin filter is weaker than nhds, so continuity at 0 implies tendsto from the right.

Key lemmas: cpow_I_half, pi_div_neg_I_pi, I_mem_slitPlane, Complex.continuousAt_cpow_const (for z ↦ z^w continuous at z when z ∈ slitPlane).
-/
private theorem fresnel_integral_limit :
    Filter.Tendsto (fun ε : ℝ => (↑π / (↑ε - I * ↑π)) ^ (1 / 2 : ℂ))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((1 + I) / (↑(Real.sqrt 2) : ℂ))) := by
        convert Filter.Tendsto.cpow ( tendsto_const_nhds.div ( Continuous.continuousWithinAt ( show Continuous fun ε : ℝ => ( ε : ℂ ) - I * Real.pi by continuity ) ) _ ) tendsto_const_nhds _ using 2 <;> norm_num [ Complex.slitPlane ];
        · convert ( Eq.symm <| cpow_I_half ) using 1 ; ring_nf ; norm_num [ mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero ];
        · norm_num [ div_neg, Complex.normSq, Complex.div_re, Complex.div_im, Real.pi_ne_zero ]

/-! ## Section 3: Truncated Fresnel integral and tail bound -/

/-- exp(iπu²) is continuous as a function ℝ → ℂ. -/
private theorem fresnel_integrand_continuous :
    Continuous (fun u : ℝ => cexp (I * ↑π * (↑u : ℂ) ^ 2)) := by
  continuity

/-- The truncated Fresnel integral is well-defined. -/
private theorem fresnel_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => cexp (I * ↑π * (↑u : ℂ) ^ 2))
      MeasureTheory.volume a b :=
  fresnel_integrand_continuous.intervalIntegrable a b

/-
PROBLEM
**Truncated Fresnel tail bound**: For 0 < A ≤ B,
    ‖∫ u in A..B, exp(iπu²) du‖ ≤ 1/(π·A).

    Proof: integration by parts. Write exp(iπu²) = (2iπu)⁻¹ · d/du[exp(iπu²)].
    ∫_A^B exp(iπu²) du = [exp(iπu²)/(2iπu)]_A^B - ∫_A^B -exp(iπu²)/(2iπu²) du.
    Boundary: ‖exp(iπB²)/(2iπB) - exp(iπA²)/(2iπA)‖ ≤ 1/(2πA) + 1/(2πB) ≤ 1/(πA).
    Integral: ‖∫_A^B exp(iπu²)/(2iπu²) du‖ ≤ ∫_A^B 1/(2πu²) du = 1/(2π)(1/A-1/B) ≤ 1/(2πA).
    Total: ≤ 1/(πA) (with some room to spare).

PROVIDED SOLUTION
The Fresnel integral ∫_A^B exp(iπu²) du satisfies the bound ‖·‖ ≤ 1/(πA) by integration by parts.

Key idea: exp(iπu²) = 1/(2iπu) · d/du[exp(iπu²)]. So by integration by parts:
∫_A^B exp(iπu²) du = [exp(iπu²)/(2iπu)]_A^B + ∫_A^B exp(iπu²)/(2iπu²) du

The boundary term has norm ≤ 1/(2πA) + 1/(2πB) ≤ 1/(πA).
The integral has norm ≤ ∫_A^B 1/(2πu²) du = (1/A - 1/B)/(2π) ≤ 1/(2πA).

Total ≤ 1/(πA) + 1/(2πA) > 1/(πA), so this doesn't quite work with the exact bound.

Alternative approach: more carefully, the boundary + integral gives:
|boundary| ≤ 1/(2πB) + 1/(2πA) and |integral| ≤ 1/(2πA) - 1/(2πB).
Total ≤ 1/(2πA) + 1/(2πB) + 1/(2πA) - 1/(2πB) = 1/(πA). ✓

Actually the standard bound is: write f(u) = exp(iπu²), then ∫_A^B f du = f(B)/(2iπB) - f(A)/(2iπA) + ∫_A^B f(u)/(2iπu²) du.
|boundary| = |f(B)/(2iπB) - f(A)/(2iπA)| ≤ 1/(2πA) + 1/(2πB).
|integral| ≤ ∫_A^B 1/(2πu²) du = [−1/(2πu)]_A^B = 1/(2πA) − 1/(2πB).
Total ≤ 1/(2πA) + 1/(2πB) + 1/(2πA) − 1/(2πB) = 1/(πA). ✓

However, this argument involves integration by parts for complex-valued functions, which is nontrivial in Mathlib.

Simpler approach: use the second mean value theorem for integrals, or directly bound using the antiderivative. Note that exp(iπu²)/(2iπu) is an "approximate antiderivative" of exp(iπu²).

Even simpler: use `intervalIntegral.norm_integral_le_of_norm_le` with a bound function, but that gives ‖∫‖ ≤ (B-A) since the integrand has norm 1, which is worse.

The cleanest Lean approach might be: prove the integration by parts identity first, then bound each piece.

Actually, for a cleaner proof path, note that we can write:
∫_A^B exp(iπu²) du = ∫_A^B (1/(2iπu)) · (2iπu · exp(iπu²)) du
= ∫_A^B (1/(2iπu)) · d/du[exp(iπu²)] du
= [exp(iπu²)/(2iπu)]_A^B - ∫_A^B (-1/(2iπu²)) · exp(iπu²) du

Using intervalIntegral.integral_mul_deriv_of_le or intervalIntegral.integral_parts.

This is somewhat involved. Let me suggest: use norm_integral_le_of_norm_le with bound 1 to get ‖∫_A^B‖ ≤ B - A first (not useful for large B). For the saddle point context, maybe a simpler bound suffices. Actually let's just try to use the integration by parts approach directly.
-/
private theorem fresnel_tail_bound (A B : ℝ) (hA : 0 < A) (hAB : A ≤ B) :
    ‖∫ u in A..B, cexp (I * ↑π * (↑u : ℂ) ^ 2)‖ ≤ 1 / (π * A) := by
      -- By integration by parts, we have:
      have h_parts : ∫ u in A..B, (Complex.exp (I * Real.pi * u ^ 2)) =
                     (Complex.exp (I * Real.pi * B ^ 2)) / (2 * I * Real.pi * B) -
                     (Complex.exp (I * Real.pi * A ^ 2)) / (2 * I * Real.pi * A) +
                     ∫ u in A..B, (Complex.exp (I * Real.pi * u ^ 2)) / (2 * I * Real.pi * u ^ 2) := by
                       rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
                       rotate_right;
                       use fun x => ( Complex.exp ( I * Real.pi * x ^ 2 ) ) / ( 2 * I * Real.pi * x ) + ∫ u in A..x, ( Complex.exp ( I * Real.pi * u ^ 2 ) ) / ( 2 * I * Real.pi * u ^ 2 );
                       · norm_num ; ring;
                       · intro x hx
                         have h_int_deriv : HasDerivAt (fun x => ∫ u in A..x, (Complex.exp (I * Real.pi * u ^ 2)) / (2 * I * Real.pi * u ^ 2)) ((Complex.exp (I * Real.pi * x ^ 2)) / (2 * I * Real.pi * x ^ 2)) x := by
                           apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
                           · apply_rules [ ContinuousOn.intervalIntegrable ];
                             exact continuousOn_of_forall_continuousAt fun y hy => ContinuousAt.div ( Continuous.continuousAt <| by continuity ) ( Continuous.continuousAt <| by continuity ) <| mul_ne_zero ( mul_ne_zero ( mul_ne_zero two_ne_zero Complex.I_ne_zero ) <| Complex.ofReal_ne_zero.mpr Real.pi_ne_zero ) <| pow_ne_zero 2 <| Complex.ofReal_ne_zero.mpr <| by cases Set.mem_uIcc.mp hy <;> linarith [ Set.mem_Icc.mp <| by simpa [ hAB ] using hx ] ;
                           · exact Measurable.stronglyMeasurable ( by exact Measurable.mul ( Complex.continuous_exp.measurable.comp ( by exact Continuous.measurable ( by continuity ) ) ) ( Measurable.inv ( by exact Continuous.measurable ( by continuity ) ) ) ) |> fun h => h.stronglyMeasurableAtFilter;
                           · exact ContinuousAt.div ( Continuous.continuousAt <| by continuity ) ( Continuous.continuousAt <| by continuity ) <| mul_ne_zero ( mul_ne_zero ( mul_ne_zero two_ne_zero <| Complex.I_ne_zero ) <| Complex.ofReal_ne_zero.mpr <| by positivity ) <| pow_ne_zero 2 <| Complex.ofReal_ne_zero.mpr <| by cases Set.mem_uIcc.mp hx <;> linarith;
                         convert HasDerivAt.add ( HasDerivAt.div ( HasDerivAt.comp x ( Complex.hasDerivAt_exp _ ) <| HasDerivAt.const_mul _ <| hasDerivAt_pow 2 _ |> HasDerivAt.comp_ofReal ) ( HasDerivAt.const_mul _ <| hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) _ ) h_int_deriv using 1 <;> norm_num;
                         · field_simp
                           ring;
                           norm_num [ show x ≠ 0 by cases Set.mem_uIcc.mp hx <;> linarith ];
                         · cases Set.mem_uIcc.mp hx <;> linarith;
                       · exact Continuous.intervalIntegrable ( by continuity ) _ _;
      -- Applying the triangle inequality and the fact that |exp(iθ)| = 1, we get:
      have h_triangle : ‖∫ u in A..B, (Complex.exp (I * Real.pi * u ^ 2))‖ ≤
                         ‖(Complex.exp (I * Real.pi * B ^ 2)) / (2 * I * Real.pi * B)‖ +
                         ‖(Complex.exp (I * Real.pi * A ^ 2)) / (2 * I * Real.pi * A)‖ +
                         ∫ u in A..B, ‖(Complex.exp (I * Real.pi * u ^ 2)) / (2 * I * Real.pi * u ^ 2)‖ := by
                           rw [ h_parts ];
                           refine' le_trans ( norm_add_le _ _ ) ( add_le_add ( norm_sub_le _ _ ) ( by simpa only [ intervalIntegral.integral_of_le hAB ] using MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℂ ) ) );
      -- Evaluating the norms, we have:
      have h_norms : ‖(Complex.exp (I * Real.pi * B ^ 2)) / (2 * I * Real.pi * B)‖ = 1 / (2 * Real.pi * B) ∧
                     ‖(Complex.exp (I * Real.pi * A ^ 2)) / (2 * I * Real.pi * A)‖ = 1 / (2 * Real.pi * A) ∧
                     ∫ u in A..B, ‖(Complex.exp (I * Real.pi * u ^ 2)) / (2 * I * Real.pi * u ^ 2)‖ = ∫ u in A..B, 1 / (2 * Real.pi * u ^ 2) := by
                       norm_num [ Complex.norm_exp, abs_mul, abs_of_pos, hA, hAB ];
                       norm_cast ; norm_num [ mul_assoc, mul_comm, mul_left_comm, ← intervalIntegral.integral_const_mul ];
                       exact ⟨ by rw [ abs_of_nonneg ( by linarith ), abs_of_nonneg ( by positivity ) ], Or.inl ( by positivity ), by rw [ abs_of_nonneg ( by positivity ) ] ⟩;
      -- Evaluating the remaining integral, we have:
      have h_integral : ∫ u in A..B, 1 / (2 * Real.pi * u ^ 2) = (1 / (2 * Real.pi)) * (1 / A - 1 / B) := by
        group;
        rw [ intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_zpow ] <;> norm_num ; linarith;
        exact Set.notMem_uIcc_of_lt ( by linarith ) ( by linarith );
      ring_nf at *; nlinarith [ inv_pos.mpr hA, inv_pos.mpr ( show 0 < B by linarith ), Real.pi_gt_three, mul_inv_cancel₀ ( ne_of_gt hA ), mul_inv_cancel₀ ( ne_of_gt ( show 0 < B by linarith ) ), mul_inv_cancel₀ ( ne_of_gt Real.pi_pos ) ] ;

/-
PROBLEM
Symmetric tail bound: for 0 < A ≤ B,
    ‖∫ u in A..B, exp(iπu²) du + ∫ u in (-B)..(-A), exp(iπu²) du‖ ≤ 2/(πA).

PROVIDED SOLUTION
By triangle inequality, ‖sum‖ ≤ ‖∫ A..B‖ + ‖∫ (-B)..(-A)‖. By substitution u ↦ -u, ∫ (-B)..(-A) exp(iπu²) du = ∫ A..B exp(iπu²) du (since u² = (-u)²). So ‖∫ (-B)..(-A)‖ = ‖∫ A..B‖ ≤ 1/(πA) (by fresnel_tail_bound). Total ≤ 2/(πA).
-/
private theorem fresnel_symmetric_tail_bound (A B : ℝ) (hA : 0 < A) (hAB : A ≤ B) :
    ‖(∫ u in A..B, cexp (I * ↑π * (↑u : ℂ) ^ 2)) +
     (∫ u in (-B)..(-A), cexp (I * ↑π * (↑u : ℂ) ^ 2))‖ ≤
      2 / (π * A) := by
        rw [ ← intervalIntegral.integral_comp_neg ] ; norm_num ; ring_nf ; norm_num [ div_neg, neg_div, neg_neg, hA.ne', hAB ] ;
        convert fresnel_tail_bound A B hA hAB using 1 ; ring

end FresnelSaddleProof