/-
RH-side π-li witness construction from explicit formula + oscillation.

Proves RhPiWitnessData (Blocker 7) via:
1. Error witness (uniform at canonical scale):
   choose `piMain x = -(π(x)-li(x))`, so the approximation error is `0`.
2. Deep RH oscillation input:
   construct pointwise finite-zero witness families with:
   - explicit-formula error at `piScale`,
   - sufficiently positive finite-zero main term (`≥ 4*piScale`) for one branch,
   - sufficiently negative finite-zero main term (`≤ -4*piScale`) for the other.
   Then extract cofinal `±3` bounds for `π-li`.
3. Deterministic transfer:
   error `≤ piScale` + cofinal `±3` on `π-li` gives cofinal `±2` on `piMain`.

SORRY COUNT: 2 atomic sorries (mathematically TRUE)
  rh_pi_pointwise_witness_main_positive — RH finite-zero witness family (positive main)
  rh_pi_pointwise_witness_main_negative — RH finite-zero witness family (negative main)

Reference: Littlewood 1914; Montgomery-Vaughan §15.2.

Co-authored-by: Claude (Anthropic), GPT Pro (OpenAI)
-/

import Littlewood.Aristotle.Standalone.CombinedAtomsFromDeepBlockers
import Littlewood.Aristotle.Standalone.RHPiLargeOscillationFromPointwise
import Littlewood.Aristotle.Standalone.RHPiTargetPhaseWitnessBuilders

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
open Aristotle.Standalone.RHPiTargetPhaseWitnessBuilders

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
  have h_exp1_gt_one : (1 : ℝ) < Real.exp 1 :=
    Real.one_lt_exp_iff.mpr zero_lt_one
  have hx_one : 1 < x := lt_of_lt_of_le h_exp1_gt_one hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx_one
  have hscale_nonneg : 0 ≤ Real.sqrt x / Real.log x * lll x := by
    have hdiv_nonneg : 0 ≤ Real.sqrt x / Real.log x :=
      div_nonneg (Real.sqrt_nonneg x) (le_of_lt hlog_pos)
    have hlll_nonneg : 0 ≤ lll x := le_trans (by norm_num) hlll
    exact mul_nonneg hdiv_nonneg hlll_nonneg
  have hleft_zero :
      |((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x) +
        -((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x)| = 0 := by
    simp
  rw [hleft_zero]
  exact hscale_nonneg

-- ============================================================
-- 2. Dirichlet alignment oscillation for π (two deep blockers)
-- ============================================================

private def RhPiPointwiseMainPositiveWitnessFamily : Prop :=
  ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
    (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
    |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
    4 * piScale x ≤ piMainFromZeros S x

private def RhPiPointwiseMainNegativeWitnessFamily : Prop :=
  ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
    (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
    |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
    piMainFromZeros S x ≤ -(4 * piScale x)

/-- Deep RH payload #1:
pointwise finite-zero witness family with sufficiently positive
finite-zero main term (`≥ 4*piScale`). -/
private theorem rh_pi_pointwise_witness_main_positive
    (_hRH : ZetaZeros.RiemannHypothesis) :
    RhPiPointwiseMainPositiveWitnessFamily := by
  -- Deep analytic number theory obligation:
  -- Under RH, Perron explicit formula and finite-zero phase analysis must yield
  -- cofinal pointwise witnesses with:
  --   (i) explicit-formula error bounded by `piScale`,
  --   (ii) phase-target control strong enough to force
  --       `4 * piScale ≤ piMainFromZeros` through deterministic transfer.
  have h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ S,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖)) := by
    sorry
  exact rh_pi_positive_main_witness_family_from_phase_target h_witness

/-- Deep RH payload #2:
pointwise finite-zero witness family with sufficiently negative
finite-zero main term (`≤ -4*piScale`). -/
private theorem rh_pi_pointwise_witness_main_negative
    (_hRH : ZetaZeros.RiemannHypothesis) :
    RhPiPointwiseMainNegativeWitnessFamily := by
  -- Deep analytic number theory obligation:
  -- Under RH, Perron explicit formula and finite-zero phase anti-alignment must
  -- yield cofinal pointwise witnesses with:
  --   (i) explicit-formula error bounded by `piScale`,
  --   (ii) anti-target phase control strong enough to force
  --       `piMainFromZeros ≤ -4 * piScale` through deterministic transfer.
  have h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ S,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖)) := by
    sorry
  exact rh_pi_negative_main_witness_family_from_phase_target h_witness

/-- Pair packaging of the two deep RH pointwise witness families. -/
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
  exact ⟨rh_pi_pointwise_witness_main_positive hRH,
    rh_pi_pointwise_witness_main_negative hRH⟩

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
