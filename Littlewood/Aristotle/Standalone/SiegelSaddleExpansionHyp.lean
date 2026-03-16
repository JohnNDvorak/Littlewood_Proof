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

## Decomposition (Agent 1v2, 2026-03-16)

The sorry is decomposed via a Gabcke constant bound:

1. **Contour saddle-point bound** (`contour_saddle_bound`): On each block,
   |R(k,t)| ≤ fresnelC1Bound · t^{-1/2}. This is the steepest-descent content:
   contour deformation + Taylor expansion + Gaussian integration.

2. **Fresnel coefficient bound** (`fresnel_c1_bound_le_quarter`):
   fresnelC1Bound ≤ 1/4. Proved by norm_num (0.083 ≤ 0.25).

The instance proof combines these with transitivity.

SORRY COUNT: 1 (contour_saddle_bound; numerical bound is proved)

Reference: Siegel 1932 S3; Gabcke 1979 Satz 1, Tabelle 1.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.Standalone.FresnelSaddlePointInfra
import Littlewood.Aristotle.Standalone.SteepestDescentContour

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

set_option linter.dupNamespace false

namespace Aristotle.Standalone.SiegelSaddleExpansionHyp

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.RSBlockParam Aristotle.ErrorTermExpansion
open Aristotle.Standalone.FresnelSaddlePointInfra
open Aristotle.Standalone.SteepestDescentContour

/-! ## Definition: saddle-point remainder -/

/-- The saddle-point remainder on block k at parameter t:
    R(k,t) = [ErrorTerm(t) - (-1)^k · (2π/t)^{1/4} · Ψ(blockParam k t)] / (2π/t)^{1/4}

    This is the "next-order correction" after extracting the leading Riemann-Siegel
    correction term. The steepest-descent analysis shows this is O(t^{-1/2}). -/
def saddlePointRemainder (k : ℕ) (t : ℝ) : ℝ :=
  (ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
    rsPsi (blockParam k t)) / (2 * Real.pi / t) ^ ((1 : ℝ) / 4)

/-! ## Gabcke constant

The steepest-descent expansion at w₀ = √(t/2π) produces subleading coefficients
c₁(p), c₂(p), ... where p = blockParam k t. Gabcke 1979, Tabelle 1 shows that
sup_{p in [0,1]} |c₁(p)| approximately equals 0.083. We use the conservative
bound 1/4.

Rather than defining c₁(p) explicitly (which requires the exact Gabcke formula
involving scaled Hermite polynomials), we introduce `fresnelC1Bound` as the
supremum, and decompose the proof into:
  (a) |R(k,t)| ≤ fresnelC1Bound · t^{-1/2}  (steepest descent -- sorry)
  (b) fresnelC1Bound ≤ 1/4                    (numerical -- proved)
-/

/-- The supremum of |c₁(p)| over p in [0,1]. Gabcke 1979, Tabelle 1 gives
    this value as approximately 0.083. -/
def fresnelC1Bound : ℝ := 0.083

/-- The Gabcke constant is positive. -/
theorem fresnelC1Bound_pos : 0 < fresnelC1Bound := by
  unfold fresnelC1Bound; norm_num

/-! ## Sorry: Contour saddle-point bound (steepest descent) -/

/-- **Contour saddle-point bound** (Siegel 1932, Gabcke 1979 Satz 1).

    On each Riemann-Siegel block, the saddle-point remainder is bounded
    by fresnelC1Bound · t^{-1/2}. This encodes:
    (a) The contour integral representation of ErrorTerm
    (b) Deformation to the steepest-descent path through w₀ = √(t/2π)
    (c) Taylor expansion of the phase to cubic order
    (d) Gaussian integration of the quadratic part (Fresnel integral)
    (e) Bounding the subleading coefficient |c₁(p)| ≤ fresnelC1Bound

    IRREDUCIBILITY: Mathlib has no steepest-descent lemma and no
    general contour deformation theorem. This is the genuine
    analytic content of the Riemann-Siegel formula. -/
private theorem contour_saddle_bound (k : ℕ) (t : ℝ)
    (hlo : hardyStart k ≤ t) (hhi : t ≤ hardyStart (k + 1)) (hpos : 0 < t) :
    |saddlePointRemainder k t| ≤ fresnelC1Bound * t ^ (-(1 : ℝ) / 2) := by
  sorry

/-! ## Proved: Fresnel coefficient numerical bound -/

/-- **Fresnel coefficient numerical bound**: 0.083 ≤ 1/4. -/
private theorem fresnel_c1_bound_le_quarter : fresnelC1Bound ≤ 1 / 4 := by
  unfold fresnelC1Bound; norm_num

/-! ## Hypothesis class -/

/-- **Siegel saddle-point expansion hypothesis** (Gabcke 1979 Satz 1).

    On each block [hardyStart k, hardyStart(k+1)], the saddle-point remainder
    satisfies |R(k,t)| ≤ (1/4) · t^{-1/2}. -/
class SiegelSaddleExpansionHyp : Prop where
  remainder_bound : ∀ k : ℕ, ∀ t : ℝ,
    hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
      |saddlePointRemainder k t| ≤ (1 / 4) * t ^ (-(1 : ℝ) / 2)

/-! ## Instance: closed from contour bound + numerical bound -/

/-- **Instance**: derived from the contour saddle-point bound and the
    Fresnel coefficient numerical evaluation.
    Step 1: contour_saddle_bound gives |R| ≤ 0.083 · t^{-1/2}
    Step 2: fresnel_c1_bound_le_quarter gives 0.083 ≤ 1/4
    Transitivity: |R| ≤ (1/4) · t^{-1/2}. -/
instance : SiegelSaddleExpansionHyp := by
  constructor
  intro k t hlo hhi hpos
  have h_contour := contour_saddle_bound k t hlo hhi hpos
  have h_c1 := fresnel_c1_bound_le_quarter
  have h_tpow_nn : (0 : ℝ) ≤ t ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hpos.le _
  calc |saddlePointRemainder k t|
      ≤ fresnelC1Bound * t ^ (-(1 : ℝ) / 2) := h_contour
    _ ≤ (1 / 4) * t ^ (-(1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right h_c1 h_tpow_nn

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
