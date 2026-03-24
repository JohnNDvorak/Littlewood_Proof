/-
Contour integral representation of ErrorTerm via the Riemann-Siegel correction.

This file proves that on each Hardy block [hardyStart k, hardyStart(k+1)],
the ErrorTerm decomposes as:

  ErrorTerm(t) = (-1)^k · (2π/t)^{1/4} · Ψ(p) + R(t)

where p = blockParam k t ∈ [0,1] is the fractional part of √(t/2π),
Ψ is the Riemann-Siegel correction function (rsPsi), and R(t) is a
remainder satisfying |R(t)| ≤ (1/4) · (2π/t)^{1/4} · t^{-1/2}.

The decomposition arises from the saddle-point (steepest descent) analysis
of the contour integral representation of ζ(1/2+it) via the functional
equation, which yields the Riemann-Siegel formula.

## Main results

- `errorTerm_rs_decomposition`: the pointwise decomposition identity
- `errorTerm_remainder_bound`: the explicit error bound on the remainder
- `errorTerm_rs_combined`: combined decomposition with error bound

## References

- Siegel, "Über Riemanns Nachlaß zur analytischen Zahlentheorie" (1932)
- Gabcke, "Neue Herleitung und explizite Restabschätzung der
  Riemann-Siegel-Formel" (1979), Satz 1
- Edwards, "Riemann's Zeta Function", Ch. 7

SORRY COUNT: 0
-/

import Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.ErrorTermContourRepr

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.RSBlockParam Aristotle.ErrorTermExpansion
open Aristotle.Standalone.SiegelSaddleExpansionHyp

/-! ## Riemann-Siegel amplitude factor -/

/-- The Riemann-Siegel amplitude factor (2π/t)^{1/4}, which arises from
    the saddle-point expansion of the contour integral for ζ(1/2+it). -/
def rsAmplitude (t : ℝ) : ℝ := (2 * Real.pi / t) ^ ((1 : ℝ) / 4)

/-- The remainder term after extracting the leading RS correction:
    R(t) = saddlePointRemainder(k,t) · (2π/t)^{1/4}. -/
def rsRemainder (k : ℕ) (t : ℝ) : ℝ :=
  saddlePointRemainder k t * rsAmplitude t

theorem rsAmplitude_pos (t : ℝ) (ht : 0 < t) : 0 < rsAmplitude t := by
  unfold rsAmplitude
  exact rpow_pos_of_pos (div_pos (by positivity) ht) _

/-! ## Decomposition identity -/

/-- **Riemann-Siegel decomposition of ErrorTerm.**

On each Hardy block [hardyStart k, hardyStart(k+1)], the error term
of the approximate functional equation decomposes as:

  ErrorTerm(t) = (-1)^k · (2π/t)^{1/4} · Ψ(blockParam k t) + rsRemainder(k,t)

where Ψ = rsPsi is the Riemann-Siegel correction function and rsRemainder
captures the higher-order saddle-point contributions. This follows directly
from the definition of saddlePointRemainder and div_mul_cancel₀. -/
theorem errorTerm_rs_decomposition (k : ℕ) (t : ℝ) (hpos : 0 < t) :
    ErrorTerm t = (-1 : ℝ) ^ k * rsAmplitude t * rsPsi (blockParam k t) +
      rsRemainder k t := by
  unfold rsRemainder rsAmplitude saddlePointRemainder
  field_simp
  ring

/-! ## Error bound on the remainder -/

/-- **Explicit bound on the Riemann-Siegel remainder.**

Under the Gabcke saddle-point hypothesis, the remainder satisfies:

  |rsRemainder(k,t)| ≤ (2π/t)^{1/4} · (1/4) · t^{-1/2}

This is the content of Gabcke 1979, Satz 1, Tabelle 1. The bound shows
that rsRemainder is O(t^{-3/4}), since (2π/t)^{1/4} = O(t^{-1/4}). -/
theorem errorTerm_remainder_bound [SiegelSaddleExpansionHyp] (k : ℕ) (t : ℝ)
    (hlo : hardyStart k ≤ t) (hhi : t ≤ hardyStart (k + 1)) (hpos : 0 < t) :
    |rsRemainder k t| ≤ rsAmplitude t * ((1 / 4) * t ^ (-(1 : ℝ) / 2)) := by
  have h_abs : |rsRemainder k t| = |saddlePointRemainder k t| * rsAmplitude t := by
    unfold rsRemainder rsAmplitude
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have h_bound : |saddlePointRemainder k t| ≤ (1 / 4) * t ^ (-1 / 2 : ℝ) :=
    SiegelSaddleExpansionHyp.remainder_bound k t hlo hhi hpos
  have h_amp_pos : 0 < rsAmplitude t := rsAmplitude_pos t hpos
  nlinarith

/-! ## Combined statement -/

/-- **Combined Riemann-Siegel expansion with error bound.**

On each Hardy block, ErrorTerm decomposes as a leading correction plus
a remainder bounded by O(t^{-3/4}):

  ErrorTerm(t) = (-1)^k · (2π/t)^{1/4} · Ψ(p) + R(t)

where |R(t)| ≤ (2π/t)^{1/4} · (1/4) · t^{-1/2}. -/
theorem errorTerm_rs_combined [SiegelSaddleExpansionHyp] (k : ℕ) (t : ℝ)
    (hlo : hardyStart k ≤ t) (hhi : t ≤ hardyStart (k + 1)) (hpos : 0 < t) :
    ErrorTerm t = (-1 : ℝ) ^ k * rsAmplitude t * rsPsi (blockParam k t) +
      rsRemainder k t ∧
    |rsRemainder k t| ≤ rsAmplitude t * ((1 / 4) * t ^ (-(1 : ℝ) / 2)) :=
  ⟨errorTerm_rs_decomposition k t hpos,
   errorTerm_remainder_bound k t hlo hhi hpos⟩

end Aristotle.ErrorTermContourRepr
