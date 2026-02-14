/-
Landau-Ingham contradiction wiring.

Provides the L² Cesàro incompatibility lemma needed for the Landau oscillation
argument. If two functions agree in Cesàro L², but one has L² mean → 0 and
the other has L² mean → L > 0, we derive False.

This is pure real analysis — no sorry.

SORRY COUNT: 0

REFERENCES:
  - Landau, "Über einen Satz von Tschebyschef" (1905)
  - Montgomery-Vaughan, "Multiplicative Number Theory I", §15.1

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.AlmostPeriodicMeanValue
import Littlewood.Aristotle.OneSidedSmallMean

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Aristotle.LandauInghamWiring

open Complex Filter MeasureTheory Topology Real Finset

/-! ## L² incompatibility lemma -/

/-- If f → 0 in Cesàro L², g → L > 0 in Cesàro L², and f - g → 0 in Cesàro L²,
then False.

Key inequality: g² ≤ 2f² + 2(f-g)² pointwise (from (a-b)² ≤ 2a² + 2b²).
Therefore Cesàro L²(g) ≤ 2·Cesàro L²(f) + 2·Cesàro L²(f-g) → 0.
But Cesàro L²(g) → L > 0. Contradiction by uniqueness of limits. -/
theorem l2_cesaro_incompatibility
    {f g : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hf_int : ∀ a b : ℝ, IntervalIntegrable (fun u => f u ^ 2) volume a b)
    (hg_int : ∀ a b : ℝ, IntervalIntegrable (fun u => g u ^ 2) volume a b)
    (hdiff_int : ∀ a b : ℝ, IntervalIntegrable (fun u => (f u - g u) ^ 2) volume a b)
    (hf_l2 : Tendsto (fun T => (1 / T) * ∫ u in (0:ℝ)..T, f u ^ 2)
      atTop (nhds 0))
    (hg_l2 : Tendsto (fun T => (1 / T) * ∫ u in (0:ℝ)..T, g u ^ 2)
      atTop (nhds L))
    (hdiff_l2 : Tendsto (fun T => (1 / T) * ∫ u in (0:ℝ)..T, (f u - g u) ^ 2)
      atTop (nhds 0)) :
    False := by
  -- Pointwise: g² ≤ 2f² + 2(f-g)²
  have hg_bound : ∀ u, g u ^ 2 ≤ 2 * f u ^ 2 + 2 * (f u - g u) ^ 2 := by
    intro u; nlinarith [sq_nonneg (f u + (f u - g u))]
  -- Upper bound on Cesàro L²(g)
  have hg_upper : ∀ᶠ T in atTop,
      (1 / T) * ∫ u in (0:ℝ)..T, g u ^ 2 ≤
      2 * ((1 / T) * ∫ u in (0:ℝ)..T, f u ^ 2) +
      2 * ((1 / T) * ∫ u in (0:ℝ)..T, (f u - g u) ^ 2) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    have h_bound :
        ∫ u in (0:ℝ)..T, g u ^ 2 ≤
        ∫ u in (0:ℝ)..T, (2 * f u ^ 2 + 2 * (f u - g u) ^ 2) :=
      intervalIntegral.integral_mono_on (le_of_lt hT)
        (hg_int 0 T) ((hf_int 0 T).const_mul 2 |>.add ((hdiff_int 0 T).const_mul 2))
        (fun u _ => hg_bound u)
    have hT_pos : (0:ℝ) < 1 / T := by positivity
    calc (1 / T) * ∫ u in (0:ℝ)..T, g u ^ 2
        ≤ (1 / T) * ∫ u in (0:ℝ)..T, (2 * f u ^ 2 + 2 * (f u - g u) ^ 2) :=
          mul_le_mul_of_nonneg_left h_bound hT_pos.le
      _ = 2 * ((1 / T) * ∫ u in (0:ℝ)..T, f u ^ 2) +
          2 * ((1 / T) * ∫ u in (0:ℝ)..T, (f u - g u) ^ 2) := by
          rw [intervalIntegral.integral_add ((hf_int 0 T).const_mul 2)
              ((hdiff_int 0 T).const_mul 2),
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]; ring
  -- The upper bound → 0
  have hbound_zero : Tendsto (fun T =>
      2 * ((1 / T) * ∫ u in (0:ℝ)..T, f u ^ 2) +
      2 * ((1 / T) * ∫ u in (0:ℝ)..T, (f u - g u) ^ 2)) atTop (nhds 0) := by
    have := (hf_l2.const_mul 2).add (hdiff_l2.const_mul 2)
    simp only [mul_zero, add_zero] at this; exact this
  -- Use tendsto_of_tendsto_of_tendsto_of_le_of_le' to show g² → 0 as well
  -- Since 0 ≤ g² ≤ bound → 0 eventually, we get g² → 0
  have hg_nn : ∀ᶠ T in atTop, 0 ≤ (1 / T) * ∫ u in (0:ℝ)..T, g u ^ 2 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg_of_forall (le_of_lt hT) (fun u => sq_nonneg _)
  have hg_zero : Tendsto (fun T => (1 / T) * ∫ u in (0:ℝ)..T, g u ^ 2)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound_zero hg_nn hg_upper
  -- But g² → L and g² → 0, contradiction
  exact absurd (tendsto_nhds_unique hg_l2 hg_zero) (ne_of_gt hL)

end Aristotle.LandauInghamWiring
