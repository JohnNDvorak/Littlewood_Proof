import Littlewood.Aristotle.Standalone.CombinedAtomsFromDeepBlockers
import Littlewood.Aristotle.Standalone.RHPiZeroSumAlignmentBridge

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiWitnessFromFrequentScale

open Filter
open GrowthDomination
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge

/-- Sign-adaptive `piMain`: exact cancellation of `piLiErr` plus a scale-sized
bias of opposite sign. This keeps the approximation error at exactly `piScale`. -/
private def piMainSigned (x : ℝ) : ℝ :=
  -piLiErr x + (if piLiErr x < 0 then piScale x else -piScale x)

/-- If `π-li` has cofinal `±piScale` witnesses, then one gets the full
`RhPiWitnessData` payload with an explicit `piMain`. -/
theorem rhPiWitness_from_frequent_unit
    (h_plus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧ piScale x ≤ piLiErr x)
    (h_minus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧ piLiErr x ≤ -piScale x) :
    RhPiWitnessData := by
  intro _hRH
  let piMain : ℝ → ℝ := piMainSigned

  have h_scale_pos : ∀ᶠ x : ℝ in atTop, 0 < piScale x := by
    filter_upwards [lll_eventually_ge_one, eventually_ge_atTop (Real.exp 1)] with x hlll hx
    have h_exp1_gt_one : (1 : ℝ) < Real.exp 1 :=
      Real.one_lt_exp_iff.mpr zero_lt_one
    have hx_one : 1 < x := lt_of_lt_of_le h_exp1_gt_one hx
    have hx_pos : 0 < x := lt_trans zero_lt_one hx_one
    have hlog_pos : 0 < Real.log x := Real.log_pos hx_one
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx_pos
    have hdiv_pos : 0 < Real.sqrt x / Real.log x := div_pos hsqrt_pos hlog_pos
    have hlll_pos : 0 < lll x := lt_of_lt_of_le (by norm_num) hlll
    exact mul_pos hdiv_pos hlll_pos

  have h_scale_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ piScale x :=
    h_scale_pos.mono (fun _ hx => le_of_lt hx)

  have h_error :
      ∀ᶠ x : ℝ in atTop, |piLiErr x + piMain x| ≤ piScale x := by
    filter_upwards [h_scale_nonneg] with x hxA
    unfold piMain piMainSigned
    by_cases hneg : piLiErr x < 0
    · simp [hneg, abs_of_nonneg hxA]
    · simp [hneg, abs_of_nonpos (neg_nonpos.mpr hxA)]

  rcases (Filter.eventually_atTop.1 h_scale_pos) with ⟨B, hB⟩

  have h_neg_main :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ piMain x ≤ -(2 * piScale x) := by
    intro X
    obtain ⟨x, hx_gt, hx_plus⟩ := h_plus (max X B)
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx_gt
    have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx_gt)
    have hApos : 0 < piScale x := hB x hBx
    have hPiPos : 0 < piLiErr x := lt_of_lt_of_le hApos hx_plus
    have hmain : piMain x ≤ -(2 * piScale x) := by
      unfold piMain piMainSigned
      have hnot : ¬ piLiErr x < 0 := not_lt.mpr (le_of_lt hPiPos)
      simp [hnot]
      nlinarith [hx_plus]
    exact ⟨x, hXx, hmain⟩

  have h_pos_main :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ 2 * piScale x ≤ piMain x := by
    intro X
    obtain ⟨x, hx_gt, hx_minus⟩ := h_minus (max X B)
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx_gt
    have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx_gt)
    have hApos : 0 < piScale x := hB x hBx
    have hPiNeg : piLiErr x < 0 := by
      have hAneg : -piScale x < 0 := neg_lt_zero.mpr hApos
      exact lt_of_le_of_lt hx_minus hAneg
    have hmain : 2 * piScale x ≤ piMain x := by
      unfold piMain piMainSigned
      simp [hPiNeg]
      nlinarith [hx_minus]
    exact ⟨x, hXx, hmain⟩

  refine ⟨piMain, ?_, ?_, ?_⟩
  · simpa [piMain, piMainSigned, piLiErr, piScale] using h_error
  · intro X
    rcases h_neg_main X with ⟨x, hx, hmain⟩
    exact ⟨x, hx, by simpa [piMain, piMainSigned, piScale] using hmain⟩
  · intro X
    rcases h_pos_main X with ⟨x, hx, hmain⟩
    exact ⟨x, hx, by simpa [piMain, piMainSigned, piScale] using hmain⟩

end Aristotle.Standalone.RHPiWitnessFromFrequentScale
