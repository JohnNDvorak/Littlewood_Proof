/-
Riemann-Siegel remainder first moment bound.

KEY RESULT:
  rs_remainder_first_moment_quarter :
    ∃ C > 0, ∀ T ≥ 2, |∫ t in Ioc 1 T, ErrorTerm t| ≤ C * T ^ (1/4 : ℝ)

This provides ErrorTermFirstMomentBoundHyp via the trivial
bound T^{1/4} ≤ T^{1/2+ε} for any ε > 0.

PROOF SKETCH (for the sorry):
1. |ErrorTerm(t)| ≤ C₀·t^{-1/4} (standard Riemann-Siegel bound, Titchmarsh §4.16)
2. ErrorTerm(t) = (-1)^{N-1}·Ψ(p)·(t/(2π))^{-1/4} + O(t^{-3/4})
   where N = ⌊√(t/(2π))⌋ and p depends on the fractional part.
3. On [2πk², 2π(k+1)²], N(t) = k, so ErrorTerm has sign (-1)^{k-1}.
4. Split ∫₁ᵀ ErrorTerm at the breakpoints 2πk².
5. Each piece: ∫_{2πk²}^{2π(k+1)²} ErrorTerm(t) dt ≈ (-1)^{k-1}·c_k
   with c_k = O(k^{1/2}) (integral of t^{-1/4} over interval of length ~4πk).
6. By Abel summation (alternating_sum_le_last), |∑ (-1)^{k-1} c_k| ≤ c_K = O(K^{1/2}).
7. K = ⌊√(T/(2π))⌋ ≈ T^{1/2}, so |∫₁ᵀ ErrorTerm| = O(T^{1/4}).

REFERENCES:
  - Titchmarsh, "Theory of the Riemann Zeta Function", §4.16, §7.6
  - Edwards, "Riemann's Zeta Function", §7.7

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.RSRemainderAlternating
import Littlewood.Aristotle.RiemannSiegelSignCancellation
import Littlewood.Bridge.HardyFirstMomentWiring

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace RiemannSiegelFirstMoment

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-! ## Atomic sorry: RS remainder first moment is O(T^{1/4}) -/

/-- **Atomic sorry**: The ErrorTerm integral admits an alternating √(n+1) decomposition.

MATHEMATICAL CONTENT:
1. Split ∫₁ᵀ ErrorTerm at breakpoints t_k = 2π(k+1)² where N(t) = ⌊√(t/(2π))⌋ jumps.
2. On [t_k, t_{k+1}], the RS remainder has sign ≈ (-1)^k and the integral
   has amplitude O(k^{1/2}) (from ∫ t^{-1/4} over interval of length ~4πk).
3. Combine: |∫ ErrorTerm| ≤ A·|∑ (-1)^k √(k+1)| + B for a bounded error B.
4. N = ⌊√(T/(2π))⌋ satisfies (N+1) ≤ T^{1/2}.

REFERENCES:
  - Titchmarsh, "Theory of the Riemann Zeta Function", §4.16
  - Edwards, "Riemann's Zeta Function", §7.7 -/
theorem errorTerm_alternatingSqrt_decomposition :
    ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
      ∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B := by
  exact Aristotle.RSRemainderAlternating.errorTerm_alternatingSqrt_decomposition

/-- **Atomic sorry**: The signed integral of the Riemann-Siegel remainder
is O(T^{1/4}).

This is STRONGER than the trivial bound O(T^{3/4}) from absolute values.
The improvement comes from the alternating sign structure of the RS remainder:

1. The RS remainder R(t) = Z(t) - MainTerm(t) satisfies
   R(t) = (-1)^{N(t)-1} · Ψ(p(t)) · t^{-1/4} + O(t^{-3/4})
   where the sign flips at each breakpoint t = 2πk².

2. Splitting the integral at these breakpoints gives an alternating
   sum with terms of size O(k^{1/2}).

3. Abel summation (alternating_sum_le_last) bounds the partial
   sums by the last term: O(K^{1/2}) where K ≈ √(T/(2π)).

4. This gives |∫₁ᵀ R(t) dt| = O(T^{1/4}).

The atomic sorry encapsulates:
  - The Riemann-Siegel formula with leading correction term
  - The alternating sign decomposition of the integral
  - Abel summation for alternating series with increasing terms -/
theorem rs_remainder_first_moment_quarter :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, ErrorTerm t| ≤ C * T ^ (1 / 4 : ℝ) :=
  RiemannSiegelSignCancellation.errorTerm_firstMoment_quarter_of_alternatingSqrt
    errorTerm_alternatingSqrt_decomposition

/-! ## Wiring: O(T^{1/4}) → ErrorTermFirstMomentBoundHyp -/

/-- T^{1/4} ≤ T^{1/2+ε} for T ≥ 1 and ε > 0. -/
private lemma rpow_quarter_le_half_plus_eps (T : ℝ) (hT : T ≥ 1) (ε : ℝ) (hε : ε > 0) :
    T ^ (1 / 4 : ℝ) ≤ T ^ (1 / 2 + ε) :=
  Real.rpow_le_rpow_of_exponent_le hT (by linarith)

/-- The RS remainder first moment O(T^{1/4}) bound implies the
ErrorTermFirstMomentBoundHyp hypothesis (O(T^{1/2+ε}) for all ε > 0).

This is a trivial consequence: T^{1/4} ≤ T^{1/2+ε} for T ≥ 1 and ε > 0. -/
theorem errorTermFirstMomentBound_from_quarter :
    HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp := by
  obtain ⟨C, hC, hbound⟩ := rs_remainder_first_moment_quarter
  refine ⟨?_⟩
  intro ε hε
  refine ⟨C, hC, ?_⟩
  intro T hT
  calc |∫ t in Ioc 1 T, ErrorTerm t|
      ≤ C * T ^ (1 / 4 : ℝ) := hbound T hT
    _ ≤ C * T ^ (1 / 2 + ε) := by
        exact mul_le_mul_of_nonneg_left
          (rpow_quarter_le_half_plus_eps T (by linarith) ε hε)
          (le_of_lt hC)

end RiemannSiegelFirstMoment

/-! ## Typeclass wiring -/

/-- Wire the RS remainder first moment bound into the typeclass instance.
This provides `ErrorTermFirstMomentBoundHyp`, which is consumed by
`hardyFirstMomentUpper_from_two_bounds` in HardyFirstMomentWiring. -/
instance : HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp :=
  RiemannSiegelFirstMoment.errorTermFirstMomentBound_from_quarter
