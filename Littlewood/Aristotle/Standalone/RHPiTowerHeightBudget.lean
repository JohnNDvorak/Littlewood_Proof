import Littlewood.ZetaZeros.ZeroCountingFunction

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiTowerHeightBudget

open Filter
open ZetaZeros

private def tripleExp (t : ℝ) : ℝ :=
  Real.exp (Real.exp (Real.exp t))

private lemma tripleExp_monotone : Monotone tripleExp := by
  intro a b hab
  exact Real.exp_le_exp.mpr <|
    Real.exp_le_exp.mpr <|
      Real.exp_le_exp.mpr hab

private lemma tripleExp_unbounded :
    ∀ X : ℝ, ∃ B : ℝ, X ≤ tripleExp B := by
  intro X
  have h_tendsto : Filter.Tendsto tripleExp atTop atTop := by
    unfold tripleExp
    exact Real.tendsto_exp_atTop.comp
      (Real.tendsto_exp_atTop.comp Real.tendsto_exp_atTop)
  have h_event : ∀ᶠ B in atTop, X ≤ tripleExp B :=
    (Filter.tendsto_atTop.1 h_tendsto) X
  rcases (Filter.eventually_atTop.1 h_event) with ⟨B, hB⟩
  exact ⟨B, hB B (le_rfl)⟩

/-- Quantitative unboundedness of `N(T)/(T+1)` from `ZeroCountingLowerBoundHyp`.

This is the exact coefficient scale feeding the RH target-height tower budget.
-/
theorem zero_count_div_unbounded
    [ZeroCountingLowerBoundHyp] :
    ∀ B : ℝ, ∃ T : ℝ, 4 ≤ T ∧ B ≤ (N T : ℝ) / (T + 1) := by
  intro B
  rcases zeroCountingFunction_lower_bound with ⟨T0, hT0⟩
  let B0 : ℝ := max B 0
  let T : ℝ := max (max T0 4) (Real.exp (6 * Real.pi * B0))
  have hT_ge_T0 : T0 ≤ T := by
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hT_ge4 : 4 ≤ T := by
    exact le_trans (le_max_right T0 4) (le_max_left _ _)
  have hT_ge1 : (1 : ℝ) ≤ T := by linarith [hT_ge4]
  have hT1_pos : 0 < T + 1 := by linarith
  have hB_le_B0 : B ≤ B0 := le_max_left _ _

  have hN_lower : T / (3 * Real.pi) * Real.log T ≤ N T := hT0 T hT_ge_T0
  have hN_div :
      (T / (3 * Real.pi) * Real.log T) / (T + 1)
        ≤ (N T : ℝ) / (T + 1) := by
    exact div_le_div_of_nonneg_right hN_lower (le_of_lt hT1_pos)

  have hratio : (1 / 2 : ℝ) ≤ T / (T + 1) := by
    have hx1 : (1 : ℝ) ≤ T := hT_ge1
    have hx1_pos : 0 < T + 1 := by linarith
    refine (le_div_iff₀ hx1_pos).2 ?_
    nlinarith [hx1]

  have hlog_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT_ge1
  have hbase_nonneg : 0 ≤ (1 / (3 * Real.pi)) * Real.log T := by
    exact mul_nonneg (by positivity) hlog_nonneg
  have hmul_ratio :
      (1 / 2 : ℝ) * ((1 / (3 * Real.pi)) * Real.log T)
        ≤ (T / (T + 1)) * ((1 / (3 * Real.pi)) * Real.log T) := by
    exact mul_le_mul_of_nonneg_right hratio hbase_nonneg

  have hfactor :
      (T / (T + 1)) * ((1 / (3 * Real.pi)) * Real.log T)
        = (T / (3 * Real.pi) * Real.log T) / (T + 1) := by
    field_simp [hT1_pos.ne']

  have hcoef_le :
      (1 / (6 * Real.pi)) * Real.log T
        ≤ (N T : ℝ) / (T + 1) := by
    have hleft :
        (1 / (6 * Real.pi)) * Real.log T
          = (1 / 2 : ℝ) * ((1 / (3 * Real.pi)) * Real.log T) := by ring
    calc
      (1 / (6 * Real.pi)) * Real.log T
          = (1 / 2 : ℝ) * ((1 / (3 * Real.pi)) * Real.log T) := hleft
      _ ≤ (T / (T + 1)) * ((1 / (3 * Real.pi)) * Real.log T) := hmul_ratio
      _ = (T / (3 * Real.pi) * Real.log T) / (T + 1) := hfactor
      _ ≤ (N T : ℝ) / (T + 1) := hN_div

  have hExp_le : Real.exp (6 * Real.pi * B0) ≤ T := by
    exact le_max_right _ _
  have hlog_ge : 6 * Real.pi * B0 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos _) hExp_le
    simpa [Real.log_exp] using h
  have hB0_le_log :
      B0 ≤ (1 / (6 * Real.pi)) * Real.log T := by
    have h6pi_pos : 0 < (6 * Real.pi : ℝ) := by positivity
    have h' : B0 ≤ Real.log T / (6 * Real.pi) := by
      refine (le_div_iff₀ h6pi_pos).2 ?_
      nlinarith [hlog_ge]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'

  refine ⟨T, hT_ge4, ?_⟩
  exact hB_le_B0.trans (hB0_le_log.trans hcoef_le)

/-- The RH target-height tower cap can be made arbitrarily large
from zero-count growth.

This isolates the quantitative "height budget" fact needed by the
`RHPiWitnessFromExplicitFormula` tower witness construction.
-/
theorem tower_cap_unbounded
    [ZeroCountingLowerBoundHyp] :
    ∀ X : ℝ, ∃ T : ℝ, 4 ≤ T ∧
      X ≤ Real.exp (Real.exp (Real.exp (((N T : ℝ) / (T + 1)) / 2))) := by
  intro X
  rcases tripleExp_unbounded X with ⟨B, hXB⟩
  rcases zero_count_div_unbounded (2 * B) with ⟨T, hT4, hTbound⟩
  have hhalf : B ≤ ((N T : ℝ) / (T + 1)) / 2 := by
    nlinarith [hTbound]
  refine ⟨T, hT4, ?_⟩
  exact le_trans hXB <| tripleExp_monotone hhalf

/-- Same tower-cap unboundedness with an explicit `(1-ε)` factor in the exponent,
matching the RH π target-height witness shape. -/
theorem tower_cap_unbounded_with_eps
    [ZeroCountingLowerBoundHyp] :
    ∀ X ε : ℝ, 0 < ε → ε < 1 →
      ∃ T : ℝ, 4 ≤ T ∧
        X ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))) := by
  intro X ε hεpos hεlt
  have hfac_pos : 0 < 1 - ε := by linarith
  rcases tripleExp_unbounded X with ⟨B, hXB⟩
  rcases zero_count_div_unbounded (2 * B / (1 - ε)) with ⟨T, hT4, hTbound⟩
  have hhalf :
      B ≤ (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2) := by
    have hmul :
        2 * B ≤ (1 - ε) * ((N T : ℝ) / (T + 1)) := by
      have hmul' :
          (1 - ε) * (2 * B / (1 - ε))
            ≤ (1 - ε) * ((N T : ℝ) / (T + 1)) :=
        mul_le_mul_of_nonneg_left hTbound (le_of_lt hfac_pos)
      have hcancel : (1 - ε) * (2 * B / (1 - ε)) = 2 * B := by
        field_simp [hfac_pos.ne']
      calc
        2 * B = (1 - ε) * (2 * B / (1 - ε)) := by simpa [hcancel]
        _ ≤ (1 - ε) * ((N T : ℝ) / (T + 1)) := hmul'
    nlinarith
  refine ⟨T, hT4, ?_⟩
  exact le_trans hXB <| tripleExp_monotone hhalf

end Aristotle.Standalone.RHPiTowerHeightBudget
