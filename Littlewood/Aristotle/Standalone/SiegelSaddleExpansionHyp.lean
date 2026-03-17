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

## Decomposition (Agent saddle-point, 2026-03-16)

The sorry is decomposed into three layers:

1. **RS formula remainder bound** (`rs_formula_remainder_bound`): The standard
   Riemann-Siegel formula with error bound — SORRY (irreducible steepest-descent):
   |ErrorTerm(t) - (-1)^k · (2π/t)^{1/4} · Ψ(p)| ≤ C_RS · t^{-3/4}

2. **Division by amplitude** (`contour_saddle_bound`): Algebraic derivation of
   |R(k,t)| ≤ fresnelC1Bound · t^{-1/2} from (1) by dividing by (2π/t)^{1/4}.
   PROVED via rpow_three_quarter_div_amp.

3. **Fresnel coefficient bound** (`fresnel_c1_bound_le_quarter`):
   fresnelC1Bound ≤ 1/4. Proved by norm_num (0.083 ≤ 0.25).

The instance proof combines (2)+(3) with transitivity.

SORRY COUNT: 1 (rs_formula_remainder_bound; algebraic wiring and numerical bounds proved)

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

/-! ## Decomposition of the contour saddle-point bound

The sorry is decomposed into:
1. **RS formula remainder bound** (`rs_formula_remainder_bound`): The Riemann-Siegel
   formula in standard form — on each block, the error term minus its leading
   Riemann-Siegel correction is O(t^{-3/4}). This is the irreducible steepest-descent
   content.

2. **Division by amplitude** (`contour_saddle_from_rs_formula`): The algebraic step
   of dividing by (2π/t)^{1/4} to convert the t^{-3/4} bound into the t^{-1/2}
   bound on `saddlePointRemainder`. PROVED.

The RS formula remainder constant is C_RS = fresnelC1Bound · (2π)^{1/4}, chosen so
that C_RS / (2π)^{1/4} = fresnelC1Bound exactly.

SORRY COUNT: 1 (rs_formula_remainder_bound)
-/

/-- The RS formula remainder constant: fresnelC1Bound · (2π)^{1/4}.
    This is the constant in the standard Riemann-Siegel remainder bound
    |ErrorTerm(t) - leading(t)| ≤ C_RS · t^{-3/4}. -/
def rsRemainderConstant : ℝ := fresnelC1Bound * (2 * Real.pi) ^ ((1 : ℝ) / 4)

/-- The RS remainder constant is positive. -/
theorem rsRemainderConstant_pos : 0 < rsRemainderConstant := by
  unfold rsRemainderConstant
  exact mul_pos fresnelC1Bound_pos (rpow_pos_of_pos (by positivity) _)

/-- Key identity: C_RS / (2π)^{1/4} = fresnelC1Bound.
    This is the algebraic bridge between the standard RS remainder form
    and the normalized saddlePointRemainder form. -/
theorem rsRemainderConstant_div_amp :
    rsRemainderConstant / (2 * Real.pi) ^ ((1 : ℝ) / 4) = fresnelC1Bound := by
  unfold rsRemainderConstant
  exact mul_div_cancel_right₀ _ (ne_of_gt (rpow_pos_of_pos (by positivity : (0:ℝ) < 2 * Real.pi) _))

/-! ## Sorry: RS formula remainder bound (standard form)

This is the Riemann-Siegel formula with error bound in standard form:

  |ErrorTerm(t) - (-1)^k · (2π/t)^{1/4} · Ψ(blockParam k t)| ≤ C_RS · t^{-3/4}

where C_RS = fresnelC1Bound · (2π)^{1/4} ≈ 0.131.

This is equivalent to `contour_saddle_bound` after dividing by (2π/t)^{1/4},
but stated in the standard notation of the Riemann-Siegel formula
(Siegel 1932 §3; Gabcke 1979 Satz 1).

The proof requires:
(a) The contour integral representation of ErrorTerm via the Siegel integral
(b) Contour deformation to the steepest-descent path through w₀ = √(t/2π)
(c) Taylor expansion of the phase at the saddle point to quadratic order
(d) Gaussian/Fresnel integration of the leading term (Mathlib: integral_gaussian_complex)
(e) Bounding the higher-order remainder via quartic Taylor coefficient

IRREDUCIBILITY: Steps (a)-(b) require contour deformation infrastructure
that Mathlib does not provide. This is the genuine analytic content. -/
private theorem rs_formula_remainder_bound (k : ℕ) (t : ℝ)
    (hlo : hardyStart k ≤ t) (hhi : t ≤ hardyStart (k + 1)) (hpos : 0 < t) :
    |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
      rsPsi (blockParam k t)| ≤ rsRemainderConstant * t ^ (-(3 : ℝ) / 4) := by
  sorry

/-! ## Proved: Division by amplitude

Converting the RS formula remainder bound (|E - lead| ≤ C_RS · t^{-3/4})
into the saddlePointRemainder bound (|R| ≤ fresnelC1Bound · t^{-1/2})
by dividing both sides by (2π/t)^{1/4}.

Key rpow identity: t^{-3/4} / (2π/t)^{1/4} = t^{-1/2} / (2π)^{1/4}. -/

/-- rpow identity: t^{-3/4} / (2π/t)^{1/4} = t^{-1/2} / (2π)^{1/4}. -/
private theorem rpow_three_quarter_div_amp (t : ℝ) (ht : 0 < t) :
    t ^ (-(3:ℝ)/4) / ((2 * Real.pi / t) ^ ((1:ℝ)/4)) =
    t ^ (-(1:ℝ)/2) / (2 * Real.pi) ^ ((1:ℝ)/4) := by
  have h2pi_pos : (0:ℝ) < 2 * Real.pi := by positivity
  have h_amp_pos : 0 < (2 * Real.pi / t) ^ ((1:ℝ)/4) :=
    rpow_pos_of_pos (div_pos h2pi_pos ht) _
  have h_2pi14_pos : 0 < (2 * Real.pi) ^ ((1:ℝ)/4) := rpow_pos_of_pos h2pi_pos _
  have h_eq : t ^ (-(3:ℝ)/4) * (2 * Real.pi) ^ ((1:ℝ)/4) =
      t ^ (-(1:ℝ)/2) * (2 * Real.pi / t) ^ ((1:ℝ)/4) := by
    rw [Real.div_rpow (by positivity : (0:ℝ) ≤ 2 * Real.pi) ht.le]
    rw [show t ^ (-(1:ℝ)/2) * ((2 * Real.pi) ^ ((1:ℝ)/4) / t ^ ((1:ℝ)/4))
        = (2 * Real.pi) ^ ((1:ℝ)/4) * (t ^ (-(1:ℝ)/2) / t ^ ((1:ℝ)/4)) from by ring]
    rw [show t ^ (-(1:ℝ)/2) / t ^ ((1:ℝ)/4) = t ^ (-(1:ℝ)/2) * (t ^ ((1:ℝ)/4))⁻¹ from div_eq_mul_inv _ _]
    rw [show (t ^ ((1:ℝ)/4))⁻¹ = t ^ (-(1:ℝ)/4) from by
      rw [← Real.rpow_neg ht.le]; congr 1; ring]
    rw [← Real.rpow_add ht, show -(1:ℝ)/2 + -(1:ℝ)/4 = -(3:ℝ)/4 from by ring]
    ring
  exact div_eq_div_iff h_amp_pos.ne' h_2pi14_pos.ne' |>.mpr h_eq

/-- **Contour saddle-point bound** (Siegel 1932, Gabcke 1979 Satz 1).
    PROVED from rs_formula_remainder_bound by dividing by the amplitude factor.

    Chain: |R(k,t)| = |E - lead| / amp ≤ C_RS · t^{-3/4} / amp
           = C_RS · t^{-1/2} / (2π)^{1/4} = fresnelC1Bound · t^{-1/2}. -/
private theorem contour_saddle_bound (k : ℕ) (t : ℝ)
    (hlo : hardyStart k ≤ t) (hhi : t ≤ hardyStart (k + 1)) (hpos : 0 < t) :
    |saddlePointRemainder k t| ≤ fresnelC1Bound * t ^ (-(1 : ℝ) / 2) := by
  have h2pi_pos : (0:ℝ) < 2 * Real.pi := by positivity
  have h_amp_pos : 0 < (2 * Real.pi / t) ^ ((1:ℝ)/4) :=
    rpow_pos_of_pos (div_pos h2pi_pos hpos) _
  have h_2pi14_pos : 0 < (2 * Real.pi) ^ ((1:ℝ)/4) := rpow_pos_of_pos h2pi_pos _
  -- Step 1: |R| = |E - lead| / amp
  unfold saddlePointRemainder
  rw [abs_div, abs_of_pos h_amp_pos]
  -- Step 2: Apply RS formula remainder bound
  have h_rs := rs_formula_remainder_bound k t hlo hhi hpos
  -- Step 3: |E - lead| / amp ≤ C_RS · t^{-3/4} / amp
  have h1 : |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
      rsPsi (blockParam k t)| / (2 * Real.pi / t) ^ ((1 : ℝ) / 4) ≤
      rsRemainderConstant * t ^ (-(3 : ℝ) / 4) / (2 * Real.pi / t) ^ ((1 : ℝ) / 4) :=
    div_le_div_of_nonneg_right h_rs h_amp_pos.le
  -- Step 4: Factor and use rpow identity
  have h2 : rsRemainderConstant * t ^ (-(3 : ℝ) / 4) / (2 * Real.pi / t) ^ ((1 : ℝ) / 4) =
      rsRemainderConstant * (t ^ (-(3:ℝ)/4) / (2 * Real.pi / t) ^ ((1:ℝ)/4)) := by ring
  rw [h2, rpow_three_quarter_div_amp t hpos] at h1
  -- Step 5: rsRemainderConstant * (t^{-1/2} / (2π)^{1/4}) = fresnelC1Bound * t^{-1/2}
  have h3 : rsRemainderConstant * (t ^ (-(1:ℝ)/2) / (2 * Real.pi) ^ ((1:ℝ)/4)) =
      fresnelC1Bound * t ^ (-(1:ℝ)/2) := by
    unfold rsRemainderConstant
    have h_ne : (2 * Real.pi) ^ ((1:ℝ)/4) ≠ 0 := ne_of_gt h_2pi14_pos
    field_simp
  linarith

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
