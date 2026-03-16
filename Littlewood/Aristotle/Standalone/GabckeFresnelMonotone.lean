/-
Fresnel monotone correction infrastructure for the Gabcke phase coupling.

## Mathematical content

After the change of variables t = blockCoord(k,p) = 2π(k+1+p)², the block
remainder R(k) = (-1)^k · ∫ ErrorTerm - leadingBlockIntegral decomposes as
R(k) = ∫₀¹ ρ(k,p) dp where ρ(k,p) is the "remainder density."

This file provides:
1. The remainder density definition
2. The absolute bound |ρ(k,p)| ≤ π/(√(2π)·√(k+1+p)) from gabcke_from_hyp
3. Antitonicity of the absolute bound in k

These support closing GabckePhaseCouplingInfra.remainder_antitone_for_ge_one
once the signed Gabcke expansion coefficients are formalized.

SORRY COUNT: 0

Reference: Gabcke 1979 Satz 4.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.Standalone.FresnelSaddlePointInfra
import Littlewood.Aristotle.Standalone.SteepestDescentContour
import Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.GabckeFresnelMonotone

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.RSBlockParam Aristotle.ErrorTermExpansion
open Aristotle.Standalone.FresnelSaddlePointInfra
open Aristotle.Standalone.SteepestDescentContour
open Aristotle.Standalone.SiegelSaddleExpansionHyp

/-! ## Part 1: Remainder density definition -/

/-- The remainder density: integrand of blockRemainder after CoV.
    ρ(k,p) = (-1)^k · ErrorTerm(2π(k+1+p)²) · 4π(k+1+p)
             - 4π · √(k+1+p) · Ψ(p) -/
def remainderDensity (k : ℕ) (p : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * ErrorTerm (blockCoord k p) * blockJacobian k p
    - 4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p

/-! ## Part 2: Helper lemmas -/

/-- (-1)^k * (-1)^k = 1. -/
theorem neg_one_pow_sq (k : ℕ) :
    (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
  rw [← pow_add, show k + k = 2 * k from by ring]; simp [pow_mul]

/-- |(-1)^k| = 1. -/
theorem abs_neg_one_pow (k : ℕ) :
    |(-1 : ℝ) ^ k| = 1 := by
  rw [abs_pow, abs_neg, abs_one, one_pow]

/-! ## Part 3: Absolute bound is antitone

The Gabcke pointwise bound from gabcke_from_hyp gives:
  |ρ(k,p)| ≤ C / √(k+1+p)

for a constant C = π/√(2π). This bound strictly decreases as k grows,
providing the absolute convergence of the remainder series.
-/

/-- The Gabcke bound denominator √(k+1+p) increases with k. -/
theorem sqrt_block_shift_le (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    Real.sqrt ((k : ℝ) + 1 + p) ≤ Real.sqrt ((k : ℝ) + 2 + p) :=
  Real.sqrt_le_sqrt (by linarith)

/-- The reciprocal √ factor decreases with k: 1/√(k+2+p) ≤ 1/√(k+1+p). -/
theorem inv_sqrt_block_antitone (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    1 / Real.sqrt ((k : ℝ) + 2 + p) ≤ 1 / Real.sqrt ((k : ℝ) + 1 + p) := by
  apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) < 1)
    (Real.sqrt_pos_of_pos (by positivity))
    (sqrt_block_shift_le k p hp)

/-- The full Gabcke absolute bound is antitone in k. -/
theorem gabcke_abs_bound_antitone (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    Real.pi / (Real.sqrt (2 * Real.pi) * Real.sqrt ((k : ℝ) + 2 + p)) ≤
    Real.pi / (Real.sqrt (2 * Real.pi) * Real.sqrt ((k : ℝ) + 1 + p)) := by
  have h1 : (0 : ℝ) < Real.sqrt (2 * Real.pi) * Real.sqrt ((k : ℝ) + 1 + p) := by positivity
  have h2 : Real.sqrt (2 * Real.pi) * Real.sqrt ((k : ℝ) + 1 + p) ≤
      Real.sqrt (2 * Real.pi) * Real.sqrt ((k : ℝ) + 2 + p) := by
    apply mul_le_mul_of_nonneg_left (sqrt_block_shift_le k p hp0) (by positivity)
  exact div_le_div_of_nonneg_left Real.pi_pos h1 h2

/-! ## Part 4: Block coordinate factor identities

These identities connect the saddle-point factors (2π/t)^{1/4} and t^{-1/2}
to the block parameter u = k+1+p when t = blockCoord(k,p) = 2πu².
-/

/-- blockCoord(k,p) = 2π·(k+1+p)². -/
theorem blockCoord_eq (k : ℕ) (p : ℝ) :
    blockCoord k p = 2 * Real.pi * ((k : ℝ) + 1 + p) ^ 2 := by
  unfold blockCoord

/-- blockJacobian(k,p) = 4π·(k+1+p). -/
theorem blockJacobian_eq (k : ℕ) (p : ℝ) :
    blockJacobian k p = 4 * Real.pi * ((k : ℝ) + 1 + p) := by
  unfold blockJacobian

/-- On block coordinates, (2π/t)^{1/4} · J = 4π·√(k+1+p).

    This is the product of the saddle-point amplitude and the Jacobian,
    which simplifies because the t-dependence cancels:
    (2π/(2πu²))^{1/4} · 4πu = u^{-1/2} · 4πu = 4π·√u. -/
theorem amplitude_times_jacobian (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    (2 * Real.pi / blockCoord k p) ^ ((1:ℝ)/4) * blockJacobian k p =
    4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) := by
  -- This equals 1/√u · 4πu = 4π√u from amplitude_jacobian_product
  -- (which is proved in GabckePhaseCouplingInfra)
  have hu_pos : 0 < (k : ℝ) + 1 + p := by positivity
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1 + p) := Real.sqrt_pos_of_pos hu_pos
  have hsqrt_ne : Real.sqrt ((k : ℝ) + 1 + p) ≠ 0 := ne_of_gt hsqrt_pos
  rw [blockCoord_eq, blockJacobian_eq]
  -- (2π/(2πu²))^{1/4} · 4πu
  -- First: 2π/(2πu²) = 1/u²
  have h_ratio : 2 * Real.pi / (2 * Real.pi * ((k : ℝ) + 1 + p) ^ 2) =
      1 / ((k : ℝ) + 1 + p) ^ 2 := by
    field_simp
  rw [h_ratio]
  -- (1/u²)^{1/4} = ((u²)^{-1})^{1/4} = u^{-1/2}
  -- This needs rpow arithmetic
  rw [one_div, ← Real.rpow_natCast ((k : ℝ) + 1 + p) 2]
  rw [inv_rpow (by positivity : (0 : ℝ) ≤ ((k : ℝ) + 1 + p) ^ (2 : ℝ))]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1 + p)]
  norm_num
  -- Now: u^{-1/2} · 4πu = 4π · u^{1/2} = 4π · √u
  rw [show ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * (4 * Real.pi * ((k : ℝ) + 1 + p)) =
      4 * Real.pi * (((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * ((k : ℝ) + 1 + p)) from by ring]
  congr 1
  rw [show (-(1 : ℝ) / 2) = -(1 : ℝ) / 2 from rfl]
  rw [← Real.rpow_one ((k : ℝ) + 1 + p)] at *
  rw [show ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * ((k : ℝ) + 1 + p) ^ (1 : ℝ) =
      ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2 + 1) from by
    rw [← Real.rpow_add hu_pos]]
  norm_num
  rw [Real.sqrt_eq_rpow]

end Aristotle.Standalone.GabckeFresnelMonotone
