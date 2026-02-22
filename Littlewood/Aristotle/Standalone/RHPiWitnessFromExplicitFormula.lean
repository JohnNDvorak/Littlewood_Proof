/-
RH-side π-li witness construction from explicit formula + oscillation.

Proves RhPiWitnessData (Blocker 7) via:
1. Error witness (uniform at canonical scale):
   choose `piMain x = -(π(x)-li(x))`, so the approximation error is `0`.
2. Deep RH oscillation input:
   construct pointwise finite-zero witness families (error + alignment +
   coefficient domination), then extract cofinal `±3` bounds for `π-li`.
3. Deterministic transfer:
   error `≤ piScale` + cofinal `±3` on `π-li` gives cofinal `±2` on `piMain`.

SORRY COUNT: 1 atomic sorry (mathematically TRUE)
  rh_pi_pointwise_witness_pair — explicit formula + Dirichlet alignment payload

Reference: Littlewood 1914; Montgomery-Vaughan §15.2.

Co-authored-by: Claude (Anthropic), GPT Pro (OpenAI)
-/

import Littlewood.Aristotle.Standalone.CombinedAtomsFromDeepBlockers
import Littlewood.Aristotle.Standalone.RHPiLargeOscillationFromPointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.RHPiWitnessFromExplicitFormula

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.RHPiLargeOscillationFromPointwise

-- ============================================================
-- 1. Explicit formula error bound for π (proved in-file)
-- ============================================================

/-- **Uniform error witness for `π(x)-li(x)`** at the canonical
`(√x/log x)·lll(x)` scale. -/
theorem rh_pi_explicit_formula_error
    (_hRH : ZetaZeros.RiemannHypothesis) :
    ∃ piMain : ℝ → ℝ,
      (∀ᶠ x in atTop,
        |((Nat.primeCounting (Nat.floor x) : ℝ) -
            LogarithmicIntegral.logarithmicIntegral x) + piMain x|
          ≤ Real.sqrt x / Real.log x * lll x) := by
  refine ⟨fun x =>
    -((Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x), ?_⟩
  filter_upwards [lll_eventually_ge_one, eventually_ge_atTop (Real.exp 1)] with x hlll hx
  have h_exp1_gt_one : (1 : ℝ) < Real.exp 1 := by
    simpa using (Real.one_lt_exp_iff.mpr zero_lt_one)
  have hx_one : 1 < x := lt_of_lt_of_le h_exp1_gt_one hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx_one
  have hscale_nonneg : 0 ≤ Real.sqrt x / Real.log x * lll x := by
    have hdiv_nonneg : 0 ≤ Real.sqrt x / Real.log x :=
      div_nonneg (Real.sqrt_nonneg x) (le_of_lt hlog_pos)
    have hlll_nonneg : 0 ≤ lll x := le_trans (by norm_num) hlll
    exact mul_nonneg hdiv_nonneg hlll_nonneg
  simpa using hscale_nonneg

-- ============================================================
-- 2. Dirichlet alignment oscillation for π (single deep blocker)
-- ============================================================

/-- Deep RH payload (single remaining blocker):
pointwise finite-zero witness families for both signs.

Minus branch (`π-li ≤ -3*piScale`) uses:
1. explicit-formula error at `piScale`,
2. sufficiently positive finite-zero main term (`≥ 4*piScale`)
   on actual nontrivial zeros.

Plus branch (`3*piScale ≤ π-li`) uses:
1. explicit-formula error at `piScale`,
2. sufficiently negative finite-zero main term (`≤ -4*piScale`) on actual
   nontrivial zeros. -/
private theorem rh_pi_pointwise_witness_pair
    (hRH : ZetaZeros.RiemannHypothesis) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      4 * piScale x ≤ piMainFromZeros S x)
    ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      piMainFromZeros S x ≤ -(4 * piScale x)) := by
  -- Reduce to an explicit payload with two parts:
  -- (i) minus branch from alignment/coefficient witnesses,
  -- (ii) plus branch from sufficiently negative finite-zero main term.
  have h_payload :
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        (∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < (1 / 100 : ℝ)) ∧
        2 * lll x ≤
          (∑ ρ ∈ S, (1 / ρ).re) - (1 / 100 : ℝ) * (∑ ρ ∈ S, 1 / ‖ρ‖))
      ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        piMainFromZeros S x ≤ -(4 * piScale x)) := by
    -- Deep analytic number theory obligation:
    -- Perron explicit formula + Dirichlet phase alignment + coefficient growth.
    sorry
  refine ⟨?_, h_payload.2⟩
  exact rh_pi_minus_witness_main_positive_from_alignment_coeff
    (ε := (1 / 100 : ℝ)) (by norm_num) h_payload.1

/-- Deep RH-side cofinal `±3` oscillation for `π(x)-li(x)` at
`(√x/log x)·lll(x)`, extracted from pointwise witness families. -/
private lemma rh_pi_minus_li_oscillates_large
    (hRH : ZetaZeros.RiemannHypothesis) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      ((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x)
        ≤ -(3 * (Real.sqrt x / Real.log x * lll x))) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      3 * (Real.sqrt x / Real.log x * lll x) ≤
        ((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x)) := by
  rcases rh_pi_pointwise_witness_pair hRH with ⟨hminus, hplus⟩
  simpa [piLiErr, piScale] using
    rh_pi_minus_li_oscillates_large_from_pointwise_witness_pair
      hRH hminus hplus

-- ============================================================
-- 3. Proof of rh_pi_main_term_oscillates (proved from 1+2)
-- ============================================================

/-- **piMain oscillation**.
Under RH, any function approximating li(x) - π(x) with error
≤ (√x/log x)·lll(x) must oscillate between ±2(√x/log x)·lll(x) cofinally. -/
theorem rh_pi_main_term_oscillates
    (hRH : ZetaZeros.RiemannHypothesis)
    (piMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x) + piMain x|
        ≤ Real.sqrt x / Real.log x * lll x) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piMain x ≤ -(2 * (Real.sqrt x / Real.log x * lll x))) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * (Real.sqrt x / Real.log x * lll x) ≤ piMain x) := by
  rcases (Filter.eventually_atTop.1 h_error) with ⟨B, hB⟩
  rcases rh_pi_minus_li_oscillates_large hRH with ⟨h_osc_neg, h_osc_pos⟩
  constructor
  · intro X
    -- Large positive π-li ⇒ large negative piMain.
    rcases h_osc_pos (max X B) with ⟨x, hx_gt, hx_pos⟩
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx_gt
    have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx_gt)
    have h_err_x :
        |((Nat.primeCounting (Nat.floor x) : ℝ) -
              LogarithmicIntegral.logarithmicIntegral x) + piMain x|
          ≤ Real.sqrt x / Real.log x * lll x := hB x hBx
    set A : ℝ := Real.sqrt x / Real.log x * lll x with hA
    have h_upper :
        ((Nat.primeCounting (Nat.floor x) : ℝ) -
              LogarithmicIntegral.logarithmicIntegral x) + piMain x ≤ A :=
      (abs_le.mp h_err_x).2
    refine ⟨x, hXx, ?_⟩
    nlinarith
  · intro X
    -- Large negative π-li ⇒ large positive piMain.
    rcases h_osc_neg (max X B) with ⟨x, hx_gt, hx_neg⟩
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx_gt
    have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx_gt)
    have h_err_x :
        |((Nat.primeCounting (Nat.floor x) : ℝ) -
              LogarithmicIntegral.logarithmicIntegral x) + piMain x|
          ≤ Real.sqrt x / Real.log x * lll x := hB x hBx
    set A : ℝ := Real.sqrt x / Real.log x * lll x with hA
    have h_lower :
        -A ≤
          ((Nat.primeCounting (Nat.floor x) : ℝ) -
            LogarithmicIntegral.logarithmicIntegral x) + piMain x :=
      (abs_le.mp h_err_x).1
    refine ⟨x, hXx, ?_⟩
    nlinarith

/-! ## Main theorem: RhPiWitnessData from the two sub-results -/

/-- **RhPiWitnessData proved** from explicit formula + oscillation.

The proof:
1. From rh_pi_explicit_formula_error: get piMain with error bound
2. From rh_pi_main_term_oscillates: get cofinal negative AND positive oscillation
3. Combine into the witness triple -/
theorem rhPiWitness_proved : RhPiWitnessData := by
  intro hRH
  obtain ⟨piMain, h_error⟩ := rh_pi_explicit_formula_error hRH
  obtain ⟨h_neg, h_pos⟩ := rh_pi_main_term_oscillates hRH piMain h_error
  exact ⟨piMain, h_error, h_neg, h_pos⟩

end Aristotle.Standalone.RHPiWitnessFromExplicitFormula
