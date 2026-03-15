/-
Infrastructure for the small-T contour bound (T ∈ [2,16]).

On the compact interval [2,16], the (logT)²/√T factor is bounded between
positive constants. So any bound of the form |R(x,T)| ≤ f(x) on [2,16]
can be absorbed into the √x·(logT)²/√T shape by choosing the constant
C₀ = f(x)·max_{T∈[2,16]} √T/(logT)².

Key results:
1. (logT)²/√T ≥ c > 0 on [2,16]
2. √T/(logT)² ≤ M on [2,16]
3. Absorption: f(x) ≤ C₀·(√x·(logT)²/√T) when f(x) ≤ C₀·c·√x

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace SmallTContourInfra

open Real

-- ============================================================
-- Part 1: Bounds on (logT)²/√T for T ∈ [2,16]
-- ============================================================

/-- log 2 > 0: since 2 > 1. -/
theorem log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num : (1:ℝ) < 2)

/-- (log 2)² > 0: square of positive. -/
theorem log_two_sq_pos : 0 < (Real.log 2) ^ 2 :=
  sq_pos_of_pos log_two_pos

/-- √2 > 0. -/
theorem sqrt_two_pos : 0 < Real.sqrt 2 :=
  Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2)

/-- (log T)²/√T > 0 for T > 1: log T > 0 and √T > 0. -/
theorem logT_sq_div_sqrtT_pos (T : ℝ) (hT : 1 < T) :
    0 < (Real.log T) ^ 2 / Real.sqrt T := by
  exact div_pos (sq_pos_of_pos (Real.log_pos hT)) (Real.sqrt_pos_of_pos (by linarith))

/-- For T ∈ [2,16], (logT)²/√T ≥ (log2)²/√16 = (log2)²/4.
    Proof: logT ≥ log2 since T ≥ 2, and √T ≤ √16 = 4 since T ≤ 16. -/
theorem logT_sq_div_sqrtT_lower_bound (T : ℝ) (hT_low : 2 ≤ T) (hT_high : T ≤ 16) :
    (Real.log 2) ^ 2 / 4 ≤ (Real.log T) ^ 2 / Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  have h_sqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos_of_pos hT_pos
  have h_log_le : Real.log 2 ≤ Real.log T :=
    Real.log_le_log (by norm_num : (0:ℝ) < 2) hT_low
  have h_log_nn : 0 ≤ Real.log 2 := le_of_lt log_two_pos
  have h_sq_le : (Real.log 2) ^ 2 ≤ (Real.log T) ^ 2 :=
    sq_le_sq' (by linarith) h_log_le
  have h_sqrt_le : Real.sqrt T ≤ 4 := by
    calc Real.sqrt T ≤ Real.sqrt 16 := Real.sqrt_le_sqrt (by linarith)
      _ = 4 := by rw [show (16:ℝ) = 4^2 from by norm_num,
                       Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
  -- (log2)²/4 ≤ (logT)²/√T because (log2)² ≤ (logT)² and √T ≤ 4
  calc (Real.log 2) ^ 2 / 4
      ≤ (Real.log T) ^ 2 / 4 := by
        apply div_le_div_of_nonneg_right h_sq_le (by norm_num : (0:ℝ) ≤ 4)
    _ ≤ (Real.log T) ^ 2 / Real.sqrt T := by
        exact div_le_div_of_nonneg_left
          (sq_pos_of_pos (Real.log_pos (by linarith : (1:ℝ) < T))).le
          h_sqrtT_pos h_sqrt_le

/-- **Absorption lemma**: if |R| ≤ B·√x and (log2)²/4 ≤ (logT)²/√T,
    then |R| ≤ (B·4/(log2)²)·(√x·(logT)²/√T).
    This converts any O(√x) bound into the desired √x·(logT)²/√T shape. -/
theorem absorb_into_contour_shape (R x T B : ℝ)
    (hR : |R| ≤ B * Real.sqrt x)
    (h_lower : (Real.log 2) ^ 2 / 4 ≤ (Real.log T) ^ 2 / Real.sqrt T)
    (hB : 0 ≤ B) (hx : 0 ≤ x) :
    |R| ≤ (B * 4 / (Real.log 2) ^ 2) *
      (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  have hlog2_sq : 0 < (Real.log 2) ^ 2 := log_two_sq_pos
  have h_factor : B * Real.sqrt x =
      (B * 4 / (Real.log 2) ^ 2) * (Real.sqrt x * ((Real.log 2) ^ 2 / 4)) := by
    field_simp
  calc |R| ≤ B * Real.sqrt x := hR
    _ = (B * 4 / (Real.log 2) ^ 2) * (Real.sqrt x * ((Real.log 2) ^ 2 / 4)) := h_factor
    _ ≤ (B * 4 / (Real.log 2) ^ 2) *
        (Real.sqrt x * ((Real.log T) ^ 2 / Real.sqrt T)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left h_lower (Real.sqrt_nonneg x)
    _ = (B * 4 / (Real.log 2) ^ 2) *
        (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by ring

end SmallTContourInfra
