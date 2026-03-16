/-
Atkinson formula infrastructure for the MainTerm first moment bound.

Provides `mainTerm_first_moment_sqrt`:
  ∃ C_M > 0, ∀ T ≥ 2, |∫₁ᵀ MainTerm(t) dt| ≤ C_M · T^{1/2}

The proof reduces to `atkinson_integral_le_N`: the Atkinson per-mode
IBP + signed Fresnel sum analysis shows |∫ MainTerm| ≤ C · (N+1),
where N = hardyN(T) ≤ √T.

Reference: Atkinson 1949; Titchmarsh 1951 §4.15.
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Aristotle.HardyNProperties

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Filter Topology
open HardyEstimatesPartial

namespace Aristotle.Standalone.AtkinsonFormula

/-! ## hardyN bound -/

/-- hardyN(T) + 1 ≤ 2√T for T ≥ 1. -/
private theorem hardyN_add_one_le (T : ℝ) (hT : T ≥ 1) :
    (↑(hardyN T) : ℝ) + 1 ≤ 2 * Real.sqrt T := by
  have hN : (↑(hardyN T) : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have h1 : Real.sqrt (T / (2 * Real.pi)) ≤ Real.sqrt T :=
    Real.sqrt_le_sqrt (div_le_self (by linarith) (by linarith [Real.pi_gt_three]))
  have h2 : (1 : ℝ) ≤ Real.sqrt T := by
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
  linarith

/-! ## Atkinson per-mode evaluation

The core analytical content: the MainTerm integral satisfies
|∫₁ᵀ MainTerm(t) dt| ≤ C_atk · (hardyN(T) + 1).

PROOF SKETCH (Atkinson 1949):

1. Fubini: swap finite sum and integral.
   ∫₁ᵀ MainTerm = 2 Σ_{n<N(T)} (n+1)^{-1/2} ∫_{hardyStart(n)}^T cos(φ_n(t)) dt
   + variable-N correction O(√N)

2. Per-mode decomposition: for each n < N,
   ∫_{a_n}^T cos(φ_n) = [Fresnel at a_n] + [IBP tail from a_n to T]
   where a_n = hardyStart(n) = 2π(n+1)².

3. Fresnel at stationary point:
   [Fresnel at a_n] ≈ C · (n+1) · cos(θ(a_n) - a_n·log(n+1) + π/4)
   The phases θ(a_n) - a_n·log(n+1) ≈ -π(n+1)² + const (Stirling for θ).
   So cos(phase + π/4) ≈ (-1)^n · cos(π/8): ALTERNATING.

4. Signed Fresnel sum:
   Σ (n+1)^{-1/2} · (n+1) · (-1)^n = Σ (-1)^n √(n+1)
   |Σ (-1)^n √(n+1)| ≤ √N (Abel bound for alternating monotone terms).

5. IBP tail sum: each tail integral is O(1) (from 1/φ'_n bounded).
   Weighted: Σ (n+1)^{-1/2} · O(1) = O(√N).

6. Total: O(√N) + O(√N) = O(√N) ≤ O(N+1).
-/

/-- **Atkinson evaluation**: |∫₁ᵀ MainTerm(t) dt| ≤ C_atk · (hardyN(T) + 1).

    Per-mode IBP + signed Fresnel cancellation + Abel bound.
    This is the deep analytical content of the Atkinson formula (1949).

    The proof combines:
    (a) Fubini for the finite Dirichlet polynomial sum
    (b) Per-mode decomposition into Fresnel + IBP tail
    (c) Signed Fresnel sum bounded by √N via Abel
    (d) IBP tail sum bounded by √N via kernel sum estimate
    (e) Variable-N correction bounded by √N

    Reference: Atkinson 1949, Acta Math. 81; Ivić 2003, Thm 4.1. -/
private theorem atkinson_integral_le_N :
    ∃ C_atk > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_atk * ((↑(hardyN T) : ℝ) + 1) := by
  sorry

/-- **MainTerm first moment O(√T) bound** (Atkinson formula).

    Combines the Atkinson evaluation |∫ MainTerm| ≤ C_atk · (N+1)
    with the hardyN bound N+1 ≤ 2√T to get the O(√T) bound.

    Reference: Atkinson 1949; Titchmarsh 1951 §4.15. -/
theorem mainTerm_first_moment_sqrt :
    ∃ C_M > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_M * T ^ ((1 : ℝ) / 2) := by
  obtain ⟨C_atk, hC_pos, h_atk⟩ := atkinson_integral_le_N
  refine ⟨2 * C_atk, by positivity, fun T hT => ?_⟩
  calc |∫ t in Ioc 1 T, MainTerm t|
      ≤ C_atk * ((↑(hardyN T) : ℝ) + 1) := h_atk T hT
    _ ≤ C_atk * (2 * Real.sqrt T) := by
        gcongr; exact hardyN_add_one_le T (by linarith)
    _ = 2 * C_atk * Real.sqrt T := by ring
    _ = 2 * C_atk * T ^ ((1 : ℝ) / 2) := by
        congr 1; exact Real.sqrt_eq_rpow T

end Aristotle.Standalone.AtkinsonFormula
