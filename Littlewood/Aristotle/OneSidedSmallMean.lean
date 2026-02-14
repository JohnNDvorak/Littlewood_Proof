/-
Generalized one-sided mean value lemma.

Strengthens `one_sided_zero_abs_mean` from AlmostPeriodicMeanValue.lean:
instead of requiring f ≤ 0 eventually, only requires f < ε eventually
for all ε > 0 (combined with Cesàro mean → 0).

This fixes the "bridge lemma FALSE" issue noted in project memory.

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.OneSidedSmallMean

open Filter MeasureTheory Topology Real

/-- IntervalIntegrable of the positive part max(f, 0). -/
private lemma ii_pos_part {f : ℝ → ℝ} {a b : ℝ}
    (h : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => max (f x) 0) volume a b :=
  ⟨h.1.pos_part, h.2.pos_part⟩

/-- IntervalIntegrable of f² for bounded f. -/
private lemma ii_sq {f : ℝ → ℝ} {a b : ℝ} (B : ℝ)
    (hB : ∀ u, |f u| ≤ B)
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => (f x) ^ 2) volume a b := by
  constructor
  · exact Integrable.mono (hf.norm.const_mul B).1 (hf.1.aestronglyMeasurable.pow 2)
      (by filter_upwards with x
          simp only [Real.norm_eq_abs, abs_pow, abs_mul, abs_abs]
          rw [abs_of_nonneg (le_trans (abs_nonneg _) (hB x))]
          rw [show |f x| ^ 2 = |f x| * |f x| from sq (|f x|)]
          exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _))
  · exact Integrable.mono (hf.norm.const_mul B).2 (hf.2.aestronglyMeasurable.pow 2)
      (by filter_upwards with x
          simp only [Real.norm_eq_abs, abs_pow, abs_mul, abs_abs]
          rw [abs_of_nonneg (le_trans (abs_nonneg _) (hB x))]
          rw [show |f x| ^ 2 = |f x| * |f x| from sq (|f x|)]
          exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _))

/-- Auxiliary: if 0 < ε and f < ε on [a,b] with a ≤ b, then ∫_a^b max(f,0) ≤ ε·(b-a). -/
private lemma integral_pos_part_le_of_lt
    (f : ℝ → ℝ) (a b ε : ℝ) (hε : 0 < ε) (hab : a ≤ b)
    (hf_int : IntervalIntegrable f volume a b)
    (hf_bound : ∀ u, a ≤ u → u ≤ b → f u < ε) :
    ∫ u in a..b, max (f u) 0 ≤ ε * (b - a) := by
  have h_max_le : ∀ u, a ≤ u → u ≤ b → max (f u) 0 ≤ ε := by
    intro u hu1 hu2
    exact max_le (hf_bound u hu1 hu2).le hε.le
  calc ∫ u in a..b, max (f u) 0
      ≤ ∫ u in a..b, ε := by
        apply intervalIntegral.integral_mono_on hab (ii_pos_part hf_int)
          intervalIntegrable_const
        intro u hu; exact h_max_le u hu.1 hu.2
    _ = ε * (b - a) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- |f| = 2·max(f,0) - f pointwise. -/
private lemma abs_eq_two_pos_part_sub (x : ℝ) : |x| = 2 * max x 0 - x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [abs_of_nonpos hx, max_eq_right hx]; ring
  · rw [abs_of_pos hx, max_eq_left hx.le]; ring

/-- **Generalized one-sided abs mean**: If f : ℝ → ℝ satisfies
(i)   |f(u)| ≤ B for all u,
(ii)  ∀ ε > 0, eventually f(u) < ε,
(iii) f is interval-integrable,
(iv)  (1/T)∫₀ᵀ f → 0,
then (1/T)∫₀ᵀ |f| → 0.

Proof idea: |f| = 2·max(f,0) - f. The mean of f → 0 by (iv).
The mean of max(f,0) is small because f < ε eventually, so
∫₀^T max(f,0) = ∫₀^{u₀} max(f,0) + ∫_{u₀}^T max(f,0) ≤ B·u₀ + ε·T.
For T large, B·u₀/T is small. -/
theorem one_sided_eventually_small_abs_mean
    (f : ℝ → ℝ) (B : ℝ) (hB_pos : 0 < B)
    (hB : ∀ u, |f u| ≤ B)
    (hf_small : ∀ ε : ℝ, ε > 0 → ∀ᶠ u in atTop, f u < ε)
    (hf_int : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hf_mean : Tendsto (fun T => (1 / T) * ∫ u in (0 : ℝ)..T, f u) atTop (nhds 0)) :
    Tendsto (fun T => (1 / T) * ∫ u in (0 : ℝ)..T, |f u|) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  -- Use ε = η/4 for the tail bound and the mean bound
  have hε : (0:ℝ) < η / 4 := by linarith
  obtain ⟨u₀', hu₀'⟩ := Filter.eventually_atTop.mp (hf_small (η / 4) hε)
  -- WLOG u₀ ≥ 0
  set u₀ := max u₀' 0 with hu₀_def
  have hu₀ : ∀ b, u₀ ≤ b → f b < η / 4 := fun b hb => hu₀' b (le_trans (le_max_left _ _) hb)
  have hu₀_nn : (0 : ℝ) ≤ u₀ := le_max_right _ _
  obtain ⟨T_m, hT_m⟩ := Metric.tendsto_atTop.mp hf_mean (η / 4) hε
  -- T₀ chosen so that 2B·|u₀|/T₀ < η/4, i.e., T₀ > 8B·|u₀|/η
  -- We use 8B(|u₀|+1)/η + 1 to handle u₀ = 0 and ensure strict inequality
  refine ⟨max (max u₀ T_m) (8 * B * (|u₀| + 1) / η + 1), fun T hT => ?_⟩
  have hT_ge_u₀ : u₀ ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)
  have hT_ge_Tm : T_m ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hT)
  have hT_big : 8 * B * (|u₀| + 1) / η + 1 ≤ T :=
    le_trans (le_max_right (max u₀ T_m) _) hT
  have h_threshold_pos : (0:ℝ) < 8 * B * (|u₀| + 1) / η + 1 := by positivity
  have hT_pos : (0 : ℝ) < T := by linarith
  rw [Real.dist_eq, sub_zero]
  have h_nn : 0 ≤ (1 / T) * ∫ u in (0:ℝ)..T, |f u| := by
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg_of_forall hT_pos.le (fun u => abs_nonneg _)
  rw [abs_of_nonneg h_nn]
  -- Use |f| = 2·max(f,0) - f
  have h_abs_eq : ∀ u, |f u| = 2 * max (f u) 0 - f u := fun u => abs_eq_two_pos_part_sub (f u)
  simp_rw [h_abs_eq]
  rw [show (1 / T) * ∫ u in (0:ℝ)..T, (2 * max (f u) 0 - f u) =
    (1 / T) * (2 * ∫ u in (0:ℝ)..T, max (f u) 0) - (1 / T) * ∫ u in (0:ℝ)..T, f u from by
    rw [intervalIntegral.integral_sub (ii_pos_part (hf_int 0 T) |>.const_mul 2) (hf_int 0 T),
        intervalIntegral.integral_const_mul]; ring]
  -- Split ∫max(f,0) at u₀
  have h_max_split : ∫ u in (0:ℝ)..T, max (f u) 0 =
      (∫ u in (0:ℝ)..u₀, max (f u) 0) + (∫ u in u₀..T, max (f u) 0) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (ii_pos_part (hf_int 0 u₀)) (ii_pos_part (hf_int u₀ T))).symm
  rw [h_max_split, mul_add, mul_add]
  -- Bound ∫₀^u₀ max(f,0) ≤ B·|u₀|
  have h_max_le_B : ∀ u, max (f u) 0 ≤ B := by
    intro u; exact max_le ((abs_le.mp (hB u)).2) hB_pos.le
  have h_int1_bound : |∫ u in (0:ℝ)..u₀, max (f u) 0| ≤ B * |u₀| := by
    have h_norm_le : ∀ u, u ∈ Set.uIoc 0 u₀ → ‖max (f u) 0‖ ≤ B := by
      intro u _
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact h_max_le_B u
    have h := intervalIntegral.norm_integral_le_of_norm_le_const h_norm_le
    rw [Real.norm_eq_abs, sub_zero] at h
    linarith [mul_comm B |u₀|]
  -- Bound ∫_{u₀}^T max(f,0) ≤ (η/4)·(T - u₀)
  have h_int2_bound : ∫ u in u₀..T, max (f u) 0 ≤ (η / 4) * (T - u₀) :=
    integral_pos_part_le_of_lt f u₀ T (η / 4) hε hT_ge_u₀ (hf_int u₀ T)
      (fun u hu1 _hu2 => hu₀ u hu1)
  -- Bound |(1/T)∫f| < η/4
  have h_mean_bound : |(1 / T) * ∫ u in (0:ℝ)..T, f u| < η / 4 := by
    have h := hT_m T hT_ge_Tm; rwa [Real.dist_eq, sub_zero] at h
  -- Bound 2B|u₀|/T < η/4
  -- From hT_big: T ≥ 8B(|u₀|+1)/η + 1, so T > 8B(|u₀|+1)/η ≥ 8B|u₀|/η
  -- Thus η/4 * T > η/4 * 8B|u₀|/η = 2B|u₀|
  have h_BuT : 2 * (1 / T) * (B * |u₀|) < η / 4 := by
    rw [show 2 * (1 / T) * (B * |u₀|) = 2 * B * |u₀| / T from by ring]
    rw [div_lt_iff₀ hT_pos]
    -- Goal: 2B|u₀| < (η/4) * T
    have h8 : 8 * B * |u₀| ≤ 8 * B * (|u₀| + 1) := by nlinarith [abs_nonneg u₀]
    have h_div_lt : 8 * B * |u₀| / η < T := by
      calc 8 * B * |u₀| / η ≤ 8 * B * (|u₀| + 1) / η := by
              apply div_le_div_of_nonneg_right h8 (by linarith)
        _ < 8 * B * (|u₀| + 1) / η + 1 := by linarith
        _ ≤ T := hT_big
    calc 2 * B * |u₀| = (η / 4) * (8 * B * |u₀| / η) := by field_simp; ring
      _ < (η / 4) * T := by
            apply mul_lt_mul_of_pos_left h_div_lt (by linarith)
  -- Combine: LHS ≤ 2·(1/T)·(B·|u₀|) + 2·(1/T)·((η/4)·(T-u₀)) + |(1/T)∫f|
  --         < η/4 + η/2 + η/4 = η
  calc (1 / T) * (2 * ∫ u in (0:ℝ)..u₀, max (f u) 0) +
      (1 / T) * (2 * ∫ u in u₀..T, max (f u) 0) -
      (1 / T) * ∫ u in (0:ℝ)..T, f u
    ≤ 2 * (1 / T) * (B * |u₀|) +
      2 * (1 / T) * ((η / 4) * (T - u₀)) +
      |(1 / T) * ∫ u in (0:ℝ)..T, f u| := by
        have h1 : (1 / T) * (2 * ∫ u in (0:ℝ)..u₀, max (f u) 0) ≤
            2 * (1 / T) * (B * |u₀|) := by
          rw [show 2 * (1 / T) * (B * |u₀|) = (1 / T) * (2 * (B * |u₀|)) from by ring]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact le_trans (le_abs_self _) h_int1_bound
        have h2 : (1 / T) * (2 * ∫ u in u₀..T, max (f u) 0) ≤
            2 * (1 / T) * ((η / 4) * (T - u₀)) := by
          rw [show 2 * (1 / T) * ((η / 4) * (T - u₀)) = (1 / T) * (2 * ((η / 4) * (T - u₀))) from by ring]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left h_int2_bound (by norm_num)
        linarith [neg_abs_le ((1 / T) * ∫ u in (0:ℝ)..T, f u)]
    _ < η / 4 + η / 2 + η / 4 := by
        have h_p2 : 2 * (1 / T) * ((η / 4) * (T - u₀)) ≤ η / 2 := by
          rw [show 2 * (1 / T) * ((η / 4) * (T - u₀)) =
            (η / 2) * ((T - u₀) / T) from by ring]
          apply mul_le_of_le_one_right (by linarith)
          rw [div_le_one hT_pos]; linarith [hu₀_nn]
        linarith
    _ = η := by ring

/-- Corollary: under the same conditions, the L² Cesàro mean → 0. -/
theorem one_sided_eventually_small_l2_mean
    (f : ℝ → ℝ) (B : ℝ) (hB_pos : 0 < B)
    (hB : ∀ u, |f u| ≤ B)
    (hf_small : ∀ ε : ℝ, ε > 0 → ∀ᶠ u in atTop, f u < ε)
    (hf_int : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hf_mean : Tendsto (fun T => (1 / T) * ∫ u in (0 : ℝ)..T, f u) atTop (nhds 0)) :
    Tendsto (fun T => (1 / T) * ∫ u in (0 : ℝ)..T, (f u) ^ 2) atTop (nhds 0) := by
  have h_abs := one_sided_eventually_small_abs_mean f B hB_pos hB hf_small hf_int hf_mean
  have h_pw : ∀ u, (f u) ^ 2 ≤ B * |f u| := by
    intro u
    rw [show (f u) ^ 2 = |f u| ^ 2 from (sq_abs (f u)).symm, sq]
    exact mul_le_mul_of_nonneg_right (hB u) (abs_nonneg _)
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp h_abs (η / B) (div_pos hη hB_pos)
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT_pos : (0:ℝ) < T := by linarith [le_max_right T₀ 1]
  have hT_ge : T₀ ≤ T := le_trans (le_max_left _ _) hT
  rw [Real.dist_eq, sub_zero]
  have h_nn : 0 ≤ (1 / T) * ∫ u in (0:ℝ)..T, (f u) ^ 2 := by
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg_of_forall hT_pos.le (fun u => sq_nonneg _)
  rw [abs_of_nonneg h_nn]
  have h_abs_nn : 0 ≤ (1 / T) * ∫ u in (0:ℝ)..T, |f u| := by
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg_of_forall hT_pos.le (fun u => abs_nonneg _)
  have h_abs_bound := hT₀ T hT_ge
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h_abs_nn] at h_abs_bound
  -- (1/T)∫f² ≤ B·(1/T)∫|f|
  have h_int_bound : (1 / T) * ∫ u in (0:ℝ)..T, (f u) ^ 2 ≤
      B * ((1 / T) * ∫ u in (0:ℝ)..T, |f u|) := by
    rw [show B * ((1 / T) * ∫ u in (0:ℝ)..T, |f u|) =
      (1 / T) * (B * ∫ u in (0:ℝ)..T, |f u|) from by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hT_pos.le
      (ii_sq B hB (hf_int 0 T)) ((hf_int 0 T).norm.const_mul B)
    intro u _; exact h_pw u
  calc (1 / T) * ∫ u in (0:ℝ)..T, (f u) ^ 2
      ≤ B * ((1 / T) * ∫ u in (0:ℝ)..T, |f u|) := h_int_bound
    _ < B * (η / B) := mul_lt_mul_of_pos_left h_abs_bound hB_pos
    _ = η := mul_div_cancel₀ η (ne_of_gt hB_pos)

end Aristotle.OneSidedSmallMean
