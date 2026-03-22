import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.GabckeNextOrderBridge

open HardyEstimatesPartial Aristotle.RSBlockParam Aristotle.ErrorTermExpansion

/-- The saddle amplitude `(2π/t)^(1/4)` is positive for `t > 0`. -/
private theorem two_pi_div_t_rpow_pos (t : ℝ) (ht : 0 < t) :
    0 < (2 * Real.pi / t) ^ ((1 : ℝ) / 4) := by
  exact Real.rpow_pos_of_pos (div_pos (by positivity) ht) _

/-- Algebraic bridge from a normalized saddle remainder bound to the standard
Gabcke next-order estimate used on RS blocks.

This theorem is intentionally placed below both `SiegelSaddleExpansionHyp` and
`RSExpansionProof`, so either file can reuse it without introducing an import
cycle. -/
theorem gabcke_next_order_bound_of_normalized_remainder
    (hrem : ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → 0 < t →
        |(ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
            rsPsi (blockParam k t)) /
          (2 * Real.pi / t) ^ ((1 : ℝ) / 4)| ≤
          (1 / 4) * t ^ (-(1 : ℝ) / 2)) :
    ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → 0 < t →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
            rsPsi (blockParam k t)| ≤
          (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * ((1 / 4) * t ^ (-(1 : ℝ) / 2)) := by
  intro k t hlo hhi hpos
  set amp : ℝ := (2 * Real.pi / t) ^ ((1 : ℝ) / 4)
  set numer : ℝ :=
    ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
      rsPsi (blockParam k t)
  have h_amp_pos : 0 < amp := by
    subst amp
    exact two_pi_div_t_rpow_pos t hpos
  have h_amp_ne : amp ≠ 0 := ne_of_gt h_amp_pos
  have hcore : |numer / amp| ≤ (1 / 4) * t ^ (-(1 : ℝ) / 2) := by
    simpa [numer, amp] using hrem k t hlo hhi hpos
  have h_eq : numer = (numer / amp) * amp := by
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ h_amp_ne, mul_one]
  rw [h_eq, abs_mul, abs_of_pos h_amp_pos, mul_comm]
  exact mul_le_mul_of_nonneg_left hcore h_amp_pos.le

end Aristotle.Standalone.GabckeNextOrderBridge
