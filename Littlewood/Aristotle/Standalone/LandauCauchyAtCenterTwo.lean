import Littlewood.Aristotle.ZetaPoleCancellation
import Littlewood.Aristotle.Standalone.LandauCauchyCoefficientStep

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LandauCauchyAtCenterTwo

open Aristotle.ZetaPoleCancellation
open Aristotle.Standalone.LandauCauchyCoefficientStep

/-- The corrected Landau formula used in the pole-cancellation argument. -/
def correctedFormula (α C σ_sign : ℝ) (s : ℂ) : ℂ :=
  s * (↑C : ℂ) / (s - (↑α : ℂ)) +
    (↑σ_sign : ℂ) * (1 + deriv zrf s / zrf s)

/-- The corrected formula is analytic at the center `s = 2`. -/
theorem correctedFormula_analyticAt_two
    (α C σ_sign : ℝ) (hα : 1 / 2 < α) (hα2 : α < 2) :
    AnalyticAt ℂ (correctedFormula α C σ_sign) (2 : ℂ) := by
  -- `2 > α`, so the real-axis analyticity theorem applies.
  have h2 : α < (2 : ℝ) := hα2
  simpa [correctedFormula] using
    (landau_formula_analyticAt_real α hα C σ_sign 2 h2)

/-- Extract a power-series witness at `s = 2` for the corrected formula. -/
theorem correctedFormula_exists_powerSeries_at_two
    (α C σ_sign : ℝ) (hα : 1 / 2 < α) (hα2 : α < 2) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (correctedFormula α C σ_sign) p (2 : ℂ) := by
  simpa [AnalyticAt] using correctedFormula_analyticAt_two α C σ_sign hα hα2

/--
Cauchy majorant package at center `2`.

Fix a power-series witness `p` for the corrected formula at `2`.
For any `r` below the radius and any `w` with `0 ≤ w < r`, this returns:
1. coefficient nonnegativity (`aₙ := coeffAtOne p n ≥ 0`),
2. Cauchy majorant (`aₙ ≤ B / r^n`),
3. geometric summability (`∑ aₙ w^n` summable).
-/
theorem correctedFormula_cauchy_majorant_data
    (α C σ_sign : ℝ) (_hα : 1 / 2 < α) (_hα2 : α < 2)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (correctedFormula α C σ_sign) p (2 : ℂ))
    {r : NNReal} (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (w : ℝ) (hw_nonneg : 0 ≤ w) (hw_lt : w < (r : ℝ)) :
    ∃ B : ℝ, 0 < B ∧
      (∀ n : ℕ, 0 ≤ coeffAtOne p n) ∧
      (∀ n : ℕ, coeffAtOne p n ≤ B / (r : ℝ) ^ n) ∧
      Summable (fun n : ℕ => coeffAtOne p n * w ^ n) := by
  -- `hp` pins down that `p` is the expansion of the corrected formula at `2`;
  -- the Cauchy/summability conclusions come from radius control.
  have _ : HasFPowerSeriesAt (correctedFormula α C σ_sign) p (2 : ℂ) := hp
  obtain ⟨B, hB, hbound, hsum⟩ :=
    exists_cauchy_majorant_and_summable p hr0 hr w hw_nonneg hw_lt
  refine ⟨B, hB, ?_, hbound, hsum⟩
  intro n
  exact norm_nonneg _

end Aristotle.Standalone.LandauCauchyAtCenterTwo
