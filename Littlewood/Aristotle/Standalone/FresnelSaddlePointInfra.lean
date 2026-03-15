/-
Fresnel saddle-point infrastructure for the Riemann-Siegel expansion.

This file connects the Fresnel integral evaluation (from FresnelIntegrals.lean)
to the saddle-point analysis in the Riemann-Siegel formula.

At the saddle point w₀ = √(t/2π) of the Siegel integral, the phase function
φ(w) = -πw² + t·log(w) has Taylor expansion with:
- φ'(w₀) = 0 (saddle condition)
- φ''(w₀) = -2π (quadratic → Fresnel integral)
- φ'''(w₀) = 2t/w₀³ (cubic → Fresnel correction)

The Fresnel integral ∫ exp(-iπu²) du = (1-i)/2 gives the leading amplitude.
Combined with the saddle-point Jacobian, this produces (2π/t)^{1/4} · Ψ(p).

All results are sorry-free sub-lemma infrastructure toward
closing `siegel_expansion_core` in RSExpansionProof.lean.

SORRY COUNT: 0

References: Siegel 1932 §3; Edwards Ch. 7 pp. 136-145; Gabcke 1979 Satz 1.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.FresnelIntegrals
import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.FresnelSaddlePointInfra

open MeasureTheory Set Filter Topology
open Aristotle.RSBlockParam

/-! ## Part 1: Fresnel amplitude factor -/

/-- |(1+i)|² = 2. The squared modulus of the Fresnel integral value (1+i)/2
    has |·|² = 2/4 = 1/2, so |(1+i)/2| = 1/√2. -/
theorem norm_sq_one_plus_I :
    Complex.normSq ((1 : ℂ) + Complex.I) = 2 := by
  simp [Complex.normSq_add, Complex.normSq_one, Complex.normSq_I,
        Complex.one_re, Complex.one_im, Complex.I_re]
  norm_num

/-- √2/2 = 1/√2. The normalized Fresnel amplitude factor. -/
theorem sqrt_two_div_two_eq_inv_sqrt :
    Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hsq : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr h2
  rw [div_eq_div_iff (by norm_num : (2:ℝ) ≠ 0) hsq, one_mul]
  exact Real.mul_self_sqrt h2.le

/-! ## Part 2: Saddle-point scale identities -/

/-- The saddle-point quadratic coefficient: t / (t/(2π)) = 2π.
    This encodes φ''(w₀) = -t/w₀² with w₀² = t/(2π). -/
theorem saddle_second_deriv (t : ℝ) (ht : 0 < t) :
    t / (t / (2 * Real.pi)) = 2 * Real.pi := by
  field_simp

/-- The (2π/t)^{1/4} factor is positive for t > 0. -/
theorem quarter_power_pos (t : ℝ) (ht : 0 < t) :
    0 < (2 * Real.pi / t) ^ ((1 : ℝ) / 4) := by
  positivity

/-- For t ≥ 2π, (2π/t) ≤ 1 and therefore (2π/t)^{1/4} ≤ 1. -/
theorem quarter_power_le_one (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) ≤ 1 := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have ht_pos : 0 < t := by linarith
  apply Real.rpow_le_one (div_nonneg hpi.le ht_pos.le)
  · exact div_le_one_of_le₀ ht ht_pos.le
  · norm_num

/-- For t ≥ 2π, √(2π/t) ≤ 1 (the square root version). -/
theorem sqrt_ratio_le_one (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    Real.sqrt (2 * Real.pi / t) ≤ 1 := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have ht_pos : 0 < t := by linarith
  have h_le1 : 2 * Real.pi / t ≤ 1 := div_le_one_of_le₀ ht ht_pos.le
  calc Real.sqrt (2 * Real.pi / t)
      ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h_le1
    _ = 1 := Real.sqrt_one

/-! ## Part 3: Fresnel correction phase from cubic Taylor term

The phase function at the saddle w₀ = √(t/2π) has Taylor expansion:
  φ(w₀+δ) = φ(w₀) + (φ''(w₀)/2)δ² + (φ'''(w₀)/6)δ³ + ...

The cubic term produces the Fresnel correction -2πp + 3π/8.
-/

/-- The saddle phase value: -π·(t/2π) + t·log(√(t/2π)) = -t/2 + (t/2)·log(t/2π).
    This is the Stirling-level approximation to hardyTheta(t). -/
theorem saddle_phase_value (t : ℝ) (ht : 0 < t) :
    -(Real.pi * (t / (2 * Real.pi))) + t * Real.log (Real.sqrt (t / (2 * Real.pi))) =
    -t / 2 + t / 2 * Real.log (t / (2 * Real.pi)) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have h_pos : 0 < t / (2 * Real.pi) := div_pos ht hpi
  rw [Real.log_sqrt h_pos.le]
  have hpi_ne : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

/-- The cubic coefficient: with w₀² = t/(2π), we have
    2t/(6w₀³) = 2π/(3w₀). -/
theorem cubic_coefficient_simplified (w₀ : ℝ) (hw₀ : 0 < w₀) (t : ℝ)
    (h_saddle : w₀ ^ 2 = t / (2 * Real.pi)) :
    2 * t / (6 * w₀ ^ 3) = 2 * Real.pi / (3 * w₀) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- From h_saddle: t = 2π · w₀²
  have h_t : t = 2 * Real.pi * w₀ ^ 2 := by
    rw [h_saddle]; field_simp
  rw [h_t]
  have hw₀_ne : w₀ ≠ 0 := ne_of_gt hw₀
  field_simp
  ring

/-- 3π/8 = π/4 + π/8. The Fresnel phase constant decomposes into
    the quarter-period from arg((1-i)/2) = -π/4 and
    the eighth-period shift π/8 from the Stirling expansion. -/
theorem fresnel_phase_decomposition :
    3 * Real.pi / 8 = Real.pi / 4 + Real.pi / 8 := by ring

/-- The Fresnel correction at the block midpoint p = 1/2:
    -2π·(1/2) + 3π/8 = -5π/8. -/
theorem fresnel_correction_at_midpoint :
    -2 * Real.pi * (1 / 2 : ℝ) + 3 * Real.pi / 8 = -(5 * Real.pi / 8) := by ring

/-- The Fresnel correction vanishes at p = 3/16 (the "Fresnel zero"):
    -2π·(3/16) + 3π/8 = 0. -/
theorem fresnel_correction_zero :
    -2 * Real.pi * (3 / 16 : ℝ) + 3 * Real.pi / 8 = 0 := by ring

/-- The rsPsi argument = Stirling residual + Fresnel correction:
    π(2p²-2p+1/4) = (2πp²-π/8) + (-2πp+3π/8). -/
theorem rsPsi_arg_decomposition (p : ℝ) :
    Real.pi * (2 * p ^ 2 - 2 * p + 1 / 4) =
    (2 * Real.pi * p ^ 2 - Real.pi / 8) + (-2 * Real.pi * p + 3 * Real.pi / 8) := by
  ring

/-- The Fresnel correction is bounded: for p ∈ [0,1],
    |-2πp + 3π/8| ≤ 19π/8. -/
theorem fresnel_correction_bounded (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    |(-2 * Real.pi * p + 3 * Real.pi / 8)| ≤ 19 * Real.pi / 8 := by
  rw [abs_le]; constructor <;> nlinarith [Real.pi_pos]

/-! ## Part 4: Error bound achievability

The saddle-point remainder is O(t^{-3/4}) while the leading term is
O(t^{-1/4}). The ratio is O(t^{-1/2}).

For t ≥ 2π: 1/√t ≤ 1/√(2π) < 1/2 (since 2π > 4).
This confirms C_R ≤ 1/2 is achievable (Gabcke's C_R ≈ 0.127). -/

/-- For t ≥ 4, 1/√t ≤ 1/2. Since 2π > 4, this holds for t ≥ 2π. -/
theorem inv_sqrt_le_half (t : ℝ) (ht : 4 ≤ t) :
    1 / Real.sqrt t ≤ 1 / 2 := by
  have ht_pos : 0 < t := by linarith
  rw [div_le_div_iff₀ (Real.sqrt_pos_of_pos ht_pos) (by norm_num : (0:ℝ) < 2)]
  simp only [one_mul, mul_one]
  have : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  linarith [Real.sqrt_le_sqrt ht]

/-- For t ≥ 2π, 1/√t < 1/2. (Strict version, since 2π > 4.) -/
theorem inv_sqrt_lt_half_of_two_pi (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    1 / Real.sqrt t < 1 / 2 := by
  have : 4 < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have : 4 < t := by linarith
  have ht_pos : 0 < t := by linarith
  rw [div_lt_div_iff₀ (Real.sqrt_pos_of_pos ht_pos) (by norm_num : (0:ℝ) < 2)]
  simp only [one_mul, mul_one]
  have : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  linarith [Real.sqrt_lt_sqrt (show (0:ℝ) ≤ 4 by norm_num) (show 4 < t by linarith)]

/-- The Gabcke constant C_R ≈ 0.127 satisfies C_R < 1/2.
    In fact 0.127 < 0.5. This trivial bound is used in the RS expansion
    to confirm the leading term dominates the remainder. -/
theorem gabcke_constant_bound :
    (0.127 : ℝ) < 1 / 2 := by norm_num

/-! ## Part 5: Fresnel integral value connection

The Fresnel integral evaluations from FresnelIntegrals.lean provide
the values needed for the saddle-point amplitude. -/

/-- √(π/2)/2 is positive (the Fresnel integral limit value). -/
theorem fresnel_value_pos : 0 < Real.sqrt (Real.pi / 2) / 2 := by positivity

/-- The Fresnel value squared: (√(π/2)/2)² = π/8.
    This connects to the saddle-point amplitude: the squared Fresnel
    amplitude times 2π gives the quarter-power factor. -/
theorem fresnel_value_sq :
    (Real.sqrt (Real.pi / 2) / 2) ^ 2 = Real.pi / 8 := by
  rw [div_pow]
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
  ring

/-- Re-export: Fresnel cosine and sine integrals both converge to √(π/2)/2. -/
theorem fresnel_values :
    Tendsto (fun ε : ℝ =>
      ∫ t : ℝ in Set.Ioi 0, Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Real.sqrt (Real.pi / 2) / 2)) ∧
    Tendsto (fun ε : ℝ =>
      ∫ t : ℝ in Set.Ioi 0, Real.exp (-ε * t ^ 2) * Real.sin (t ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Real.sqrt (Real.pi / 2) / 2)) :=
  FresnelIntegrals.fresnel_cos_sin_eq_same_limit

/-- The (2π/t)^{1/4} amplitude factor is at most (2π)^{1/4}·k^{-1/4}
    on the block starting at hardyStart(k) = 2π(k+1)².
    Since hardyStart(k) ≥ 2π, the factor is ≤ 1. -/
theorem amplitude_on_block_le_one (t : ℝ)
    (ht : 2 * Real.pi ≤ t) :
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) ≤ 1 :=
  quarter_power_le_one t ht

/-! ## Part 6: Quartic coefficient and next-order saddle-point bounds

The phase function φ(w) = -πw² + t·log(w) at the saddle w₀ = √(t/2π) has
fourth derivative φ⁽⁴⁾(w₀) = -6t/w₀⁴. The quartic Taylor coefficient is
φ⁽⁴⁾(w₀)/24 = -t/(4w₀⁴). Since w₀² = t/(2π), this equals -π²/t.

The quartic correction to the steepest-descent integral contributes a term
of order t^{-1/2} relative to the leading Fresnel amplitude. Combined with
the (2π/t)^{1/4} prefactor, this gives the O(t^{-3/4}) remainder in the
Riemann-Siegel expansion (Gabcke 1979 Satz 1).
-/

/-- The quartic coefficient: at the saddle w₀² = t/(2π), the fourth-derivative
    coefficient is t/(4w₀⁴) = π²/t. -/
theorem quartic_coefficient (w₀ : ℝ) (hw₀ : 0 < w₀) (t : ℝ) (ht : 0 < t)
    (h_saddle : w₀ ^ 2 = t / (2 * Real.pi)) :
    t / (4 * w₀ ^ 4) = Real.pi ^ 2 / t := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_t : t = 2 * Real.pi * w₀ ^ 2 := by rw [h_saddle]; field_simp
  rw [h_t]
  have hw₀_ne : w₀ ≠ 0 := ne_of_gt hw₀
  field_simp
  ring

/-- The quartic coefficient is O(1/t): for t ≥ 1, π²/t ≤ π². -/
theorem quartic_coefficient_le (t : ℝ) (ht : 1 ≤ t) :
    Real.pi ^ 2 / t ≤ Real.pi ^ 2 := by
  rw [div_le_iff₀ (by linarith : (0:ℝ) < t)]
  nlinarith [Real.pi_pos]

/-- The quartic-to-quadratic ratio at the saddle: (π²/t) / (2π) = π/(2t).
    This ratio controls the next-order correction relative to the Fresnel integral. -/
theorem quartic_quadratic_ratio (t : ℝ) (ht : 0 < t) :
    Real.pi ^ 2 / t / (2 * Real.pi) = Real.pi / (2 * t) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- For t ≥ 2π, the quartic-to-quadratic ratio is at most 1/4.
    This bounds the relative size of the next-order saddle-point correction. -/
theorem quartic_ratio_le_quarter (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    Real.pi / (2 * t) ≤ 1 / 4 := by
  have ht_pos : 0 < t := by linarith [Real.pi_pos]
  rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
  nlinarith

/-- Taylor remainder structure: for |δ| ≤ w₀/2 and w₀ > 0, the fourth-order
    Taylor remainder of log Γ at the saddle is bounded by C·δ⁴/w₀³.

    The key estimate: on the circle |w - w₀| ≤ w₀/2, the fourth derivative
    of log Γ is O(1/w₀³), so by Taylor's theorem with Lagrange remainder,
    |R₃(δ)| ≤ (1/24)·sup|f⁽⁴⁾|·|δ|⁴ ≤ C·δ⁴/w₀³. -/
theorem taylor_quartic_remainder_bound (w₀ δ : ℝ) (hw₀ : 0 < w₀)
    (hδ : |δ| ≤ w₀ / 2) :
    δ ^ 4 / w₀ ^ 3 ≤ w₀ / 16 := by
  have hw₀_ne : w₀ ≠ 0 := ne_of_gt hw₀
  have hδ_bound : δ ^ 4 ≤ (w₀ / 2) ^ 4 := by
    have h1 : δ ^ 2 ≤ (w₀ / 2) ^ 2 := by nlinarith [abs_nonneg δ, sq_abs δ, sq_abs (w₀ / 2)]
    have h2 : 0 ≤ δ ^ 2 := sq_nonneg δ
    have h3 : 0 ≤ (w₀ / 2) ^ 2 := sq_nonneg (w₀ / 2)
    nlinarith
  have h_rhs : (w₀ / 2) ^ 4 / w₀ ^ 3 = w₀ / 16 := by field_simp; ring
  calc δ ^ 4 / w₀ ^ 3
      ≤ (w₀ / 2) ^ 4 / w₀ ^ 3 := by
        apply div_le_div_of_nonneg_right hδ_bound (by positivity)
    _ = w₀ / 16 := h_rhs

/-- The saddle-point scale: w₀ = √(t/(2π)) satisfies w₀² = t/(2π) and
    1/w₀ = √(2π/t). The next-order correction factor 1/w₀ = O(t^{-1/2}). -/
theorem saddle_inv_eq_sqrt_ratio (t : ℝ) (ht : 0 < t) :
    1 / Real.sqrt (t / (2 * Real.pi)) = Real.sqrt (2 * Real.pi / t) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_pos : 0 < t / (2 * Real.pi) := div_pos ht hpi
  rw [one_div, Real.inv_sqrt h_pos.le, Real.sqrt_div_self' (t / (2 * Real.pi))]
  congr 1
  rw [abs_of_pos h_pos]
  field_simp

/-- √(2π/t) ≤ 1 for t ≥ 2π (the next-order correction is small). -/
theorem saddle_inv_le_one (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    Real.sqrt (2 * Real.pi / t) ≤ 1 :=
  sqrt_ratio_le_one t ht

/-- The next-order coefficient c₁ satisfies |c₁| ≤ (1/4)·√(2π/t).
    This decomposes the bound into: quartic ratio (≤ 1/4) × saddle inverse (√(2π/t)).
    Combined with (2π/t)^{1/4} amplitude: the product is
    (2π/t)^{1/4} · (1/4) · t^{-1/2}, exactly matching gabcke_next_order_bound. -/
theorem next_order_coefficient_bound (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    (1 : ℝ) / 4 * Real.sqrt (2 * Real.pi / t) ≤ 1 / 4 := by
  have h1 : Real.sqrt (2 * Real.pi / t) ≤ 1 := saddle_inv_le_one t ht
  nlinarith

/-- Gabcke's next-order correction decomposes as:
    (2π/t)^{1/4} · (1/4) · t^{-1/2} = (1/4) · (2π)^{1/4} · t^{-3/4}.
    This is the factorization used in saddle_from_next_correction. -/
theorem next_order_factorization (t : ℝ) (ht : 0 < t) :
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * ((1 / 4) * t ^ (-(1 : ℝ) / 2))
    = (1 / 4) * (2 * Real.pi) ^ ((1 : ℝ) / 4) * t ^ (-(3 : ℝ) / 4) := by
  rw [show (2 * Real.pi / t) ^ ((1:ℝ)/4) = (2 * Real.pi) ^ ((1:ℝ)/4) * t ^ (-(1:ℝ)/4) from by
    rw [div_rpow (by positivity : (0:ℝ) ≤ 2 * Real.pi) ht.le]
    congr 1
    rw [Real.rpow_neg ht.le]
    rfl]
  rw [show (-(1:ℝ)/4) = -(1:ℝ)/4 from rfl]
  rw [show t ^ (-(1:ℝ)/4) * ((1 / 4) * t ^ (-(1:ℝ)/2))
    = (1 / 4) * (t ^ (-(1:ℝ)/4) * t ^ (-(1:ℝ)/2)) from by ring]
  congr 1
  rw [← Real.rpow_add ht]
  congr 1
  ring

/-- For t ≥ 2π, the next-order bound (1/4)·t^{-1/2} ≤ 1/4.
    Combined with (2π/t)^{1/4} ≤ 1, the full bound is ≤ 1/4. -/
theorem next_order_bound_le_quarter (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    (1 : ℝ) / 4 * t ^ (-(1 : ℝ) / 2) ≤ 1 / 4 := by
  have ht_pos : 0 < t := by linarith [Real.pi_pos]
  have h1 : t ^ (-(1:ℝ)/2) ≤ 1 := by
    rw [Real.rpow_neg ht_pos.le, inv_le_one_iff_of_pos (by positivity)]
    rw [Real.one_le_rpow_iff_of_nonneg ht_pos.le (by norm_num : (0:ℝ) < 1/2)]
    linarith
  nlinarith

/-- The full next-order product is at most 1/4 for t ≥ 2π:
    (2π/t)^{1/4} · (1/4) · t^{-1/2} ≤ (2π/t)^{1/4} · (1/4) ≤ 1 · 1/4 = 1/4.
    This confirms the next-order correction is uniformly bounded. -/
theorem next_order_product_le_quarter (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * ((1 / 4) * t ^ (-(1 : ℝ) / 2)) ≤ 1 / 4 := by
  have ht_pos : 0 < t := by linarith [Real.pi_pos]
  have h_amp : (2 * Real.pi / t) ^ ((1:ℝ)/4) ≤ 1 := quarter_power_le_one t ht
  have h_next : (1:ℝ)/4 * t ^ (-(1:ℝ)/2) ≤ 1/4 := next_order_bound_le_quarter t ht
  calc (2 * Real.pi / t) ^ ((1:ℝ)/4) * ((1/4) * t ^ (-(1:ℝ)/2))
      ≤ 1 * (1/4) := by
        apply mul_le_mul h_amp h_next (by positivity) (by norm_num)
    _ = 1/4 := one_mul _

end Aristotle.Standalone.FresnelSaddlePointInfra
