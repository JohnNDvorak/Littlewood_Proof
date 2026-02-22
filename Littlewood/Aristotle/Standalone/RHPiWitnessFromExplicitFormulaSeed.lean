import Littlewood.Aristotle.Standalone.CombinedAtomsFromDeepBlockers
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.ZetaZeros.SupremumRealPart

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.RHPiWitnessFromExplicitFormulaSeed

open Filter
open GrowthDomination
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers

/-- The `π(x) - li(x)` error term in the RH witness construction. -/
private def piLiErr (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral x

/-- The comparison scale in the RH π-branch. -/
private def piScale (x : ℝ) : ℝ :=
  Real.sqrt x / Real.log x * lll x

/-- Seed data for the RH π-branch:
1. eventual `(log x)^2` explicit-formula error for some `piMain`,
2. cofinal `±4` aligned main-term witnesses for the same `piMain`. -/
def RhPiWitnessSeedData : Prop :=
  ∀ (_hRH : ZetaZeros.RiemannHypothesis),
    ∃ piMain : ℝ → ℝ,
      (∀ᶠ x in atTop, |piLiErr x + piMain x| ≤ (Real.log x) ^ 2) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧ piMain x ≤ -(4 * piScale x)) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧ 4 * piScale x ≤ piMain x)

/-- Growth domination needed for the π explicit-formula error transfer:
`(log x)^2 ≤ (√x / log x) * lll x` eventually. -/
private lemma log_sq_eventually_le_piScale :
    ∀ᶠ x in atTop, (Real.log x) ^ 2 ≤ piScale x := by
  filter_upwards [log_le_rpow_eventually (1 / 6 : ℝ) (by positivity),
    lll_eventually_ge_one, eventually_ge_atTop (Real.exp 1)] with x hlog hlll hx
  have h_exp1_gt_one : (1 : ℝ) < Real.exp 1 := by
    simpa using (Real.one_lt_exp_iff.mpr zero_lt_one)
  have hx_one : 1 < x := lt_of_lt_of_le h_exp1_gt_one hx
  have hx_pos : 0 < x := lt_trans zero_lt_one hx_one
  have hx_nonneg : (0 : ℝ) ≤ x := le_of_lt hx_pos
  have hlog_pos : 0 < Real.log x := Real.log_pos hx_one
  have hlog_nonneg : 0 ≤ Real.log x := le_of_lt hlog_pos
  have hpow :
      (Real.log x) ^ 3 ≤ (x ^ (1 / 6 : ℝ)) ^ 3 := by
    exact pow_le_pow_left₀ hlog_nonneg hlog 3
  have hpow_eq : (x ^ (1 / 6 : ℝ)) ^ 3 = Real.sqrt x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx_nonneg]
    have h123 : (1 / 6 : ℝ) * (↑(3 : ℕ) : ℝ) = (1 / 2 : ℝ) := by norm_num
    rw [h123, Real.sqrt_eq_rpow]
  have hcube :
      (Real.log x) ^ 3 ≤ Real.sqrt x * lll x := by
    calc
      (Real.log x) ^ 3 ≤ (x ^ (1 / 6 : ℝ)) ^ 3 := hpow
      _ = Real.sqrt x := hpow_eq
      _ ≤ Real.sqrt x * lll x :=
        le_mul_of_one_le_right (Real.sqrt_nonneg x) hlll
  have hmul :
      (Real.log x) ^ 2 * Real.log x ≤ Real.sqrt x * lll x := by
    simpa [pow_succ, pow_two, mul_assoc] using hcube
  have hdiv :
      (Real.log x) ^ 2 ≤ (Real.sqrt x * lll x) / Real.log x := by
    exact (le_div_iff₀ hlog_pos).2 hmul
  simpa [piScale, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv

/-- Blocker 7a in seeded form:
from eventual `(log x)^2` control, derive the target
`(√x/log x) * lll x` explicit-formula error bound. -/
theorem rh_pi_explicit_formula_error_of_seed
    (hSeed : RhPiWitnessSeedData)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∃ piMain : ℝ → ℝ,
      (∀ᶠ x in atTop,
        |(piLiErr x) + piMain x|
          ≤ piScale x) := by
  rcases hSeed hRH with ⟨piMain, h_logsq, _h_main_neg, _h_main_pos⟩
  refine ⟨piMain, ?_⟩
  filter_upwards [h_logsq, log_sq_eventually_le_piScale] with x hx_logsq hx_dom
  exact le_trans hx_logsq hx_dom

/-- If the same `piMain` has eventual error at `piScale` and cofinal `±4`
main-term witnesses, then `π-li` has cofinal `±3` oscillation at `piScale`. -/
private theorem rh_pi_minus_li_oscillates_large_of_error_and_main
    (piMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |piLiErr x + piMain x| ≤ piScale x)
    (h_main_neg : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piMain x ≤ -(4 * piScale x))
    (h_main_pos : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      4 * piScale x ≤ piMain x) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piLiErr x ≤ -(3 * piScale x)) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      3 * piScale x ≤ piLiErr x) := by
  rcases (Filter.eventually_atTop.1 h_error) with ⟨B, hB⟩
  constructor
  · intro X
    rcases h_main_pos (max X B) with ⟨x, hx_gt, hx_main⟩
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx_gt
    have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx_gt)
    have h_err_x : |piLiErr x + piMain x| ≤ piScale x := hB x hBx
    have h_upper : piLiErr x + piMain x ≤ piScale x := (abs_le.mp h_err_x).2
    refine ⟨x, hXx, ?_⟩
    nlinarith
  · intro X
    rcases h_main_neg (max X B) with ⟨x, hx_gt, hx_main⟩
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx_gt
    have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx_gt)
    have h_err_x : |piLiErr x + piMain x| ≤ piScale x := hB x hBx
    have h_lower : -piScale x ≤ piLiErr x + piMain x := (abs_le.mp h_err_x).1
    refine ⟨x, hXx, ?_⟩
    nlinarith

/-- Blocker 7c in seeded form:
cofinal `±3` oscillation for `π-li` from seed data. -/
theorem rh_pi_minus_li_oscillates_large_of_seed
    (hSeed : RhPiWitnessSeedData)
    (hRH : ZetaZeros.RiemannHypothesis) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      (piLiErr x) ≤ -(3 * piScale x)) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      3 * piScale x ≤ (piLiErr x)) := by
  rcases hSeed hRH with ⟨piMain, h_logsq, h_main_neg, h_main_pos⟩
  have h_error : ∀ᶠ x in atTop, |piLiErr x + piMain x| ≤ piScale x := by
    filter_upwards [h_logsq, log_sq_eventually_le_piScale] with x hx_logsq hx_dom
    exact le_trans hx_logsq hx_dom
  exact rh_pi_minus_li_oscillates_large_of_error_and_main
    piMain h_error h_main_neg h_main_pos

/-- Main-term extraction:
from eventual `piScale` error and cofinal `±3` oscillation of `π-li`,
derive cofinal `±2` oscillation for `piMain`. -/
private theorem rh_pi_main_term_oscillates_of_error_and_osc
    (piMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |piLiErr x + piMain x| ≤ piScale x)
    (h_osc :
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧
        piLiErr x ≤ -(3 * piScale x)) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧
        3 * piScale x ≤ piLiErr x)) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piMain x ≤ -(2 * piScale x)) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * piScale x ≤ piMain x) := by
  rcases (Filter.eventually_atTop.1 h_error) with ⟨B, hB⟩
  rcases h_osc with ⟨h_osc_neg, h_osc_pos⟩
  constructor
  · intro X
    rcases h_osc_pos (max X B) with ⟨x, hx_gt, hx_pos⟩
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx_gt
    have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx_gt)
    have h_err_x : |piLiErr x + piMain x| ≤ piScale x := hB x hBx
    have h_upper : piLiErr x + piMain x ≤ piScale x := (abs_le.mp h_err_x).2
    refine ⟨x, hXx, ?_⟩
    nlinarith
  · intro X
    rcases h_osc_neg (max X B) with ⟨x, hx_gt, hx_neg⟩
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx_gt
    have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx_gt)
    have h_err_x : |piLiErr x + piMain x| ≤ piScale x := hB x hBx
    have h_lower : -piScale x ≤ piLiErr x + piMain x := (abs_le.mp h_err_x).1
    refine ⟨x, hXx, ?_⟩
    nlinarith

/-- Full RH-side π witness payload from seed data.

This is a sorry-free bridge theorem that packages Blocker 7 into a single
importable statement once the seeded analytic inputs are provided. -/
theorem rhPiWitness_proved_of_seed
    (hSeed : RhPiWitnessSeedData) :
    RhPiWitnessData := by
  intro hRH
  rcases hSeed hRH with ⟨piMain, h_logsq, h_main_neg, h_main_pos⟩
  have h_error : ∀ᶠ x in atTop,
      |piLiErr x + piMain x| ≤ piScale x := by
    filter_upwards [h_logsq, log_sq_eventually_le_piScale] with x hx_logsq hx_dom
    exact le_trans hx_logsq hx_dom
  have h_osc :
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧
        piLiErr x ≤ -(3 * piScale x)) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧
        3 * piScale x ≤ piLiErr x) :=
    rh_pi_minus_li_oscillates_large_of_error_and_main
      piMain h_error h_main_neg h_main_pos
  have h_main2 :
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧
        piMain x ≤ -(2 * piScale x)) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧
        2 * piScale x ≤ piMain x) :=
    rh_pi_main_term_oscillates_of_error_and_osc piMain h_error h_osc
  refine ⟨piMain, ?_, h_main2.1, h_main2.2⟩
  simpa [piLiErr, piScale]
    using h_error

end Aristotle.Standalone.RHPiWitnessFromExplicitFormulaSeed
