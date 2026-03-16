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
  apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
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
  exact div_le_div_of_nonneg_left Real.pi_pos.le h1 h2

/-! ## Part 4: Block coordinate factor identities

These identities connect the saddle-point factors (2π/t)^{1/4} and t^{-1/2}
to the block parameter u = k+1+p when t = blockCoord(k,p) = 2πu².
-/

/-- blockCoord(k,p) = 2π·(k+1+p)². -/
theorem blockCoord_eq (k : ℕ) (p : ℝ) :
    blockCoord k p = 2 * Real.pi * ((k : ℝ) + 1 + p) ^ 2 := by
  unfold blockCoord; ring

/-- blockJacobian(k,p) = 4π·(k+1+p). -/
theorem blockJacobian_eq (k : ℕ) (p : ℝ) :
    blockJacobian k p = 4 * Real.pi * ((k : ℝ) + 1 + p) := by
  unfold blockJacobian; ring

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
  -- (1/u²)^{1/4} · 4πu = 4π√u
  -- Strategy: both sides are positive, square both sides
  set u := (k : ℝ) + 1 + p with hu_def
  -- (1/u²)^{1/4} = 1/√u
  -- Since (1/u²)^{1/4} = ((1/u²)^{1/2})^{1/2} = (1/u)^{1/2} = 1/√u
  -- Then (1/√u) · 4πu = 4πu/√u = 4π√u
  -- Direct: multiply both sides by √u
  have hsq := Real.sq_sqrt hu_pos.le  -- (√u)^2 = u
  -- The LHS is (1/u²)^{1/4} · 4πu. We show this equals 4π√u by squaring.
  -- LHS² = (1/u²)^{1/2} · (4πu)² = (1/u) · 16π²u² = 16π²u
  -- RHS² = (4π√u)² = 16π²u ✓
  have hlhs_nn : 0 ≤ (1 / u ^ 2) ^ ((1:ℝ)/4) * (4 * Real.pi * u) := by positivity
  have hrhs_nn : 0 ≤ 4 * Real.pi * Real.sqrt u := by positivity
  rw [← Real.sqrt_sq hlhs_nn, ← Real.sqrt_sq hrhs_nn]
  congr 1
  -- Show squares are equal
  have h_sq_lhs : ((1 / u ^ 2) ^ ((1:ℝ)/4) * (4 * Real.pi * u)) ^ 2 = 16 * Real.pi ^ 2 * u := by
    rw [mul_pow]
    have h1 : ((1 / u ^ 2) ^ ((1:ℝ)/4)) ^ 2 = (1 / u ^ 2) ^ ((1:ℝ)/2) := by
      rw [← Real.rpow_natCast ((1 / u ^ 2) ^ ((1:ℝ)/4)) 2,
          ← Real.rpow_mul (by positivity : 0 ≤ 1 / u ^ 2)]
      norm_num
    rw [h1]
    have h2 : (1 / u ^ 2) ^ ((1:ℝ)/2) = 1 / u := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div' 1 (by positivity), Real.sqrt_one,
          Real.sqrt_sq hu_pos.le]
    rw [h2]
    field_simp
    ring
  have h_sq_rhs : (4 * Real.pi * Real.sqrt u) ^ 2 = 16 * Real.pi ^ 2 * u := by
    rw [mul_pow, mul_pow]; rw [Real.sq_sqrt hu_pos.le]; ring
  linarith

end Aristotle.Standalone.GabckeFresnelMonotone
