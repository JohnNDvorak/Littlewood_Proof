/-
# Littlewood's Theorem: RH-False Branch

When RH fails, there exists a zero with Re(ρ) > 1/2. Schmidt's oscillation
theorem gives ψ(x) - x = Ω±(x^{Θ-ε}) for any ε > 0, with Θ > 1/2.
Since x^{Θ-ε} eventually dominates √x · log log log x (for ε small), the
Ω± monotonicity lemma upgrades to the full Littlewood strength.

Steps:
  1. From ¬RH: Θ > 1/2 (via zetaZeroSupRealPart_gt_half_of_not_RH)
  2. Choose ε = (Θ - 1/2)/4, so α := Θ - ε > 1/2
  3. From SchmidtPsiOscillationHyp: ψ-x = Ω±(x^α)
  4. √x · lll x ≤ x^α eventually (since α > 1/2 and lll x = o(x^δ) for any δ)
  5. From Ω± monotonicity: ψ-x = Ω±(√x · lll x)

SORRY COUNT: 0 (uses hypothesis classes SchmidtPsiOscillationHyp, FirstZeroOrdinateHyp)
-/

import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.ZetaZeros.SupremumRealPart
import Littlewood.Basic.OmegaNotation
import Littlewood.CoreLemmas.GrowthDomination
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Real Filter Topology Asymptotics
open Schmidt ZetaZeros GrowthDomination

namespace Aristotle.LittlewoodRHFalse

/-- log x ≤ x^δ eventually, for any δ > 0.
Extracted from `isLittleO_log_rpow_atTop`. -/
private theorem log_le_rpow_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in atTop, Real.log x ≤ x ^ δ := by
  have h_bound : ∀ᶠ x in atTop, ‖Real.log x‖ ≤ 1 * ‖x ^ δ‖ :=
    (isLittleO_log_rpow_atTop hδ).bound one_pos
  filter_upwards [h_bound, eventually_ge_atTop 1] with x hbound hx1
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hrpow_nn : 0 ≤ x ^ δ := Real.rpow_nonneg (le_trans zero_le_one hx1) δ
  rwa [Real.norm_of_nonneg hlog_nn, Real.norm_of_nonneg hrpow_nn, one_mul] at hbound

/-- log log log x ≤ x^δ eventually, for any δ > 0.
Follows from log x ≤ x^δ eventually and lll x ≤ log x for large x. -/
private theorem lll_le_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in atTop, lll x ≤ x ^ δ := by
  filter_upwards [log_le_rpow_eventually δ hδ,
                   eventually_ge_atTop (Real.exp (Real.exp (Real.exp 1)))] with x hlog hx_large
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx_large
  -- exp(exp 1) ≤ log x
  have hlog_large : Real.exp (Real.exp 1) ≤ Real.log x := by
    have h1 : Real.log (Real.exp (Real.exp (Real.exp 1))) ≤ Real.log x :=
      Real.log_le_log (Real.exp_pos _) hx_large
    rwa [Real.log_exp] at h1
  have hlog_pos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hlog_large
  -- exp 1 ≤ log(log x)
  have hloglog_large : Real.exp 1 ≤ Real.log (Real.log x) := by
    have h1 : Real.log (Real.exp (Real.exp 1)) ≤ Real.log (Real.log x) :=
      Real.log_le_log (Real.exp_pos _) hlog_large
    rwa [Real.log_exp] at h1
  have hloglog_pos : 0 < Real.log (Real.log x) :=
    lt_of_lt_of_le (Real.exp_pos _) hloglog_large
  -- Chain: lll x = log(log(log x)) ≤ log(log x) ≤ log x ≤ x^δ
  -- using log a ≤ a for a ≥ 0 (Real.log_le_self)
  calc lll x = Real.log (Real.log (Real.log x)) := rfl
    _ ≤ Real.log (Real.log x) := Real.log_le_self hloglog_pos.le
    _ ≤ Real.log x := Real.log_le_self hlog_pos.le
    _ ≤ x ^ δ := hlog

/-- When RH fails, x^{Θ-ε} eventually dominates √x · lll x for small ε. -/
private theorem rpow_dominates_sqrt_lll_of_not_RH
    [FirstZeroOrdinateHyp]
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    ∃ ε : ℝ, 0 < ε ∧
    ∀ᶠ x in atTop, Real.sqrt x * lll x ≤ x ^ (Θ - ε) := by
  have hΘ := zetaZeroSupRealPart_gt_half_of_not_RH hRH
  -- Choose ε = (Θ - 1/2) / 4, δ = (3Θ - 3/2) / 4 = Θ - ε - 1/2
  refine ⟨(Θ - 1/2) / 4, by linarith, ?_⟩
  -- Need: √x · lll x ≤ x^{Θ - (Θ-1/2)/4} eventually
  -- The exponent Θ - (Θ-1/2)/4 = (3Θ+1/2)/4 > 1/2 since Θ > 1/2
  -- Let δ = (3Θ+1/2)/4 - 1/2 = (3Θ-3/2)/4 > 0
  have hδ : 0 < (3*Θ - 3/2) / 4 := by linarith
  filter_upwards [lll_le_rpow ((3*Θ - 3/2) / 4) hδ, eventually_ge_atTop 1] with x hlll hx1
  calc Real.sqrt x * lll x
      ≤ Real.sqrt x * x ^ ((3*Θ - 3/2) / 4) :=
        mul_le_mul_of_nonneg_left hlll (Real.sqrt_nonneg x)
    _ = x ^ (1/2 : ℝ) * x ^ ((3*Θ - 3/2) / 4) := by rw [Real.sqrt_eq_rpow]
    _ = x ^ (1/2 + (3*Θ - 3/2) / 4) :=
        (Real.rpow_add (lt_of_lt_of_le one_pos hx1) _ _).symm
    _ = x ^ (Θ - (Θ - 1/2) / 4) := by ring_nf

/-- When RH fails, ψ(x) - x = Ω±(√x · log log log x).

Uses Schmidt oscillation (Ω±(x^{Θ-ε})) + domination + Ω± monotonicity. -/
theorem littlewood_psi_rh_false
    [SchmidtPsiOscillationHyp] [FirstZeroOrdinateHyp]
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x)
    =Ω±[fun x => Real.sqrt x * lll x] := by
  obtain ⟨ε, hε, hdom⟩ := rpow_dominates_sqrt_lll_of_not_RH hRH
  have hschmidt := SchmidtPsiOscillationHyp.oscillation ε hε
  exact hschmidt.of_eventually_ge hdom sqrt_mul_lll_eventually_nonneg

end Aristotle.LittlewoodRHFalse
