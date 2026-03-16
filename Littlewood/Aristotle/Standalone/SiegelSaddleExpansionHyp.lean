/-
Hypothesis bridge for the Siegel saddle-point expansion remainder bound.

This encapsulates the irreducible steepest-descent content of Gabcke 1979 Satz 1:
on each Riemann-Siegel block, the remainder after extracting the leading correction
is bounded by (2π/t)^{1/4} · (1/4) · t^{-1/2}.

The hypothesis class `SiegelSaddleExpansionHyp` isolates the sorry to a single
instance declaration, so that RSExpansionProof.lean can close its
`gabcke_next_order_bound` sorry via the bridge theorem `gabcke_from_hyp`.

## Mathematical content

The saddle-point remainder is:
  R(k,t) = [ErrorTerm(t) - (-1)^k · (2π/t)^{1/4} · Ψ(blockParam k t)] / (2π/t)^{1/4}

The hypothesis asserts |R(k,t)| ≤ (1/4) · t^{-1/2} for t in block k with t > 0.
This is the content of Siegel's steepest-descent expansion through the saddle
w₀ = √(t/2π), with the bound coming from the Fresnel coefficient |c₁(p)| ≤ 1/4
(Gabcke 1979, Tabelle 1).

Closing this sorry requires ~500 lines of steepest-descent infrastructure:
contour deformation, Taylor expansion at the saddle, Fresnel coefficient evaluation.

SORRY COUNT: 1

Reference: Siegel 1932 §3; Gabcke 1979 Satz 1, Tabelle 1.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.Standalone.FresnelSaddlePointInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

set_option linter.dupNamespace false

namespace Aristotle.Standalone.SiegelSaddleExpansionHyp

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.RSBlockParam Aristotle.ErrorTermExpansion
open Aristotle.Standalone.FresnelSaddlePointInfra

/-! ## Definition: saddle-point remainder -/

/-- The saddle-point remainder on block k at parameter t:
    R(k,t) = [ErrorTerm(t) - (-1)^k · (2π/t)^{1/4} · Ψ(blockParam k t)] / (2π/t)^{1/4}

    This is the "next-order correction" after extracting the leading Riemann-Siegel
    correction term. The steepest-descent analysis shows this is O(t^{-1/2}). -/
def saddlePointRemainder (k : ℕ) (t : ℝ) : ℝ :=
  (ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
    rsPsi (blockParam k t)) / (2 * Real.pi / t) ^ ((1 : ℝ) / 4)

/-! ## Hypothesis class -/

/-- **Siegel saddle-point expansion hypothesis** (Gabcke 1979 Satz 1).

    On each block [hardyStart k, hardyStart(k+1)], the saddle-point remainder
    satisfies |R(k,t)| ≤ (1/4) · t^{-1/2}. The constant 1/4 bounds the
    Fresnel coefficient |c₁(p)| for p ∈ [0,1] (Gabcke computed ≈ 0.083).

    Closing the sorry on the instance requires steepest-descent contour
    deformation infrastructure not currently available in Mathlib. -/
class SiegelSaddleExpansionHyp : Prop where
  remainder_bound : ∀ k : ℕ, ∀ t : ℝ,
    hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
      |saddlePointRemainder k t| ≤ (1 / 4) * t ^ (-(1 : ℝ) / 2)

/-! ## Sorry'd instance -/

/-- **Instance** (sorry'd): The steepest-descent analysis confirms the bound.
    Closing requires: contour deformation to saddle w₀ = √(t/2π),
    Taylor expansion of the phase, Fresnel coefficient evaluation.
    See SteepestDescentContour.lean (Phase B) for the planned infrastructure. -/
instance : SiegelSaddleExpansionHyp := by
  constructor
  intro k t hlo hhi hpos
  sorry

/-! ## Bridge theorem -/

/-- Two-pi-over-t to the 1/4 is positive when t > 0. -/
private theorem two_pi_div_t_rpow_pos (t : ℝ) (ht : 0 < t) :
    0 < (2 * Real.pi / t) ^ ((1 : ℝ) / 4) :=
  rpow_pos_of_pos (div_pos (by positivity) ht) _

/-- **Bridge theorem**: derives the exact statement of `gabcke_next_order_bound`
    from `SiegelSaddleExpansionHyp`.

    The key algebraic step is:
      |E(t) - leading(t)| = |R(k,t)| · (2π/t)^{1/4}
                           ≤ (1/4) · t^{-1/2} · (2π/t)^{1/4}
                           = (2π/t)^{1/4} · (1/4) · t^{-1/2} -/
theorem gabcke_from_hyp [SiegelSaddleExpansionHyp] :
    ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤
        (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * ((1 / 4) * t ^ (-(1 : ℝ) / 2)) := by
  intro k t hlo hhi hpos
  have h_amp_pos := two_pi_div_t_rpow_pos t hpos
  -- Unfold saddlePointRemainder: |E - leading| = |R| · amp
  have h_eq : ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
      rsPsi (blockParam k t) =
      saddlePointRemainder k t * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) := by
    unfold saddlePointRemainder
    rw [div_mul_cancel₀]
    exact ne_of_gt h_amp_pos
  rw [h_eq, abs_mul, abs_of_pos h_amp_pos, mul_comm]
  exact mul_le_mul_of_nonneg_left
    (SiegelSaddleExpansionHyp.remainder_bound k t hlo hhi hpos)
    h_amp_pos.le

end Aristotle.Standalone.SiegelSaddleExpansionHyp
