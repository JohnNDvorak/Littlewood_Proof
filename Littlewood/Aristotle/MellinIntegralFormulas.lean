/-
Mellin integral formulas for the Landau oscillation argument.

This file evaluates Mellin-type integrals over (1, ∞) needed for the
Dirichlet integral construction in the proof of Littlewood's theorem.

## Main Results

* `mellin_x` : ∫_{Ioi 1} t · t^{-(s+1)} = 1/(s-1) for Re(s) > 1
* `mellin_rpow_alpha` : ∫_{Ioi 1} t^α · t^{-(s+1)} = 1/(s-α) for Re(s) > α

These are building blocks for the formula verification step in the
non-negative Dirichlet integral argument (NonNegDirichletIntegral.lean).

SORRY COUNT: 0

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
Co-authored-by: Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Littlewood.Aristotle.PsiIntegralRepresentation

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.MellinIntegralFormulas

open Complex Filter Topology MeasureTheory Set

/-! ## Mellin integral: ∫_{Ioi 1} t · t^{-(s+1)} = 1/(s-1) -/

/-- ∫_{Ioi 1} t · t^{-(s+1)} dt = 1/(s-1) for Re(s) > 1.

The integrand simplifies to t^{-s} via `cpow_add`, and the evaluation
uses `integral_Ioi_cpow_of_lt`. -/
theorem mellin_x (s : ℂ) (hs : 1 < s.re) :
    ∫ t in Ioi (1 : ℝ), (↑t : ℂ) * (↑t : ℂ) ^ (-(s + 1)) = 1 / (s - 1) := by
  -- Reduce: t · t^{-(s+1)} = t^{-s} on (1, ∞)
  have h_eq : ∀ t ∈ Ioi (1 : ℝ),
      (↑t : ℂ) * (↑t : ℂ) ^ (-(s + 1)) = (↑t : ℂ) ^ (-s) := by
    intro t ht
    have ht_ne : (↑t : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    conv_lhs => lhs; rw [← cpow_one (↑t : ℂ)]
    rw [← cpow_add _ _ ht_ne, show (1 : ℂ) + (-(s + 1)) = -s from by ring]
  rw [setIntegral_congr_fun measurableSet_Ioi h_eq]
  -- Evaluate: ∫_{Ioi 1} t^{-s} = -1^{-s+1}/(-s+1) = 1/(s-1)
  rw [integral_Ioi_cpow_of_lt (show (-s).re < -1 by simp; linarith) one_pos]
  simp only [ofReal_one, one_cpow]
  -- Goal: -1 / (-s + 1) = 1 / (s - 1)
  have hs1 : (s : ℂ) - 1 ≠ 0 := by
    intro h; have := congr_arg re h; simp at this; linarith
  have hns1 : -s + 1 ≠ (0 : ℂ) := by
    rwa [show -s + 1 = -(s - 1) from by ring, neg_ne_zero]
  rw [div_eq_div_iff hns1 hs1]; ring

/-! ## Mellin integral: ∫_{Ioi 1} t^α · t^{-(s+1)} = 1/(s-α) -/

/-- ∫_{Ioi 1} t^α · t^{-(s+1)} dt = 1/(s-α) for Re(s) > α.

Generalizes `mellin_x` to arbitrary real exponent α. -/
theorem mellin_rpow_alpha (α : ℝ) (s : ℂ) (hs : α < s.re) :
    ∫ t in Ioi (1 : ℝ), (↑t : ℂ) ^ (↑α : ℂ) * (↑t : ℂ) ^ (-(s + 1)) =
      1 / (s - ↑α) := by
  -- Reduce: t^α · t^{-(s+1)} = t^{α-s-1} on (1, ∞)
  have h_eq : ∀ t ∈ Ioi (1 : ℝ),
      (↑t : ℂ) ^ (↑α : ℂ) * (↑t : ℂ) ^ (-(s + 1)) =
        (↑t : ℂ) ^ ((↑α : ℂ) - s - 1) := by
    intro t ht
    have ht_ne : (↑t : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    rw [← cpow_add _ _ ht_ne]; congr 1; ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_eq]
  -- Evaluate
  have hre : ((↑α : ℂ) - s - 1).re < -1 := by
    simp only [sub_re, ofReal_re, one_re]; linarith
  rw [integral_Ioi_cpow_of_lt hre one_pos]
  simp only [ofReal_one, one_cpow]
  -- Goal: -1 / ((↑α) - s - 1 + 1) = 1 / (s - ↑α)
  have hsα : s - (↑α : ℂ) ≠ 0 := by
    intro h; have := congr_arg re h; simp at this; linarith
  have hden : (↑α : ℂ) - s - 1 + 1 ≠ (0 : ℂ) := by
    rwa [show (↑α : ℂ) - s - 1 + 1 = -(s - ↑α) from by ring, neg_ne_zero]
  rw [div_eq_div_iff hden hsα]; ring

end Aristotle.MellinIntegralFormulas
