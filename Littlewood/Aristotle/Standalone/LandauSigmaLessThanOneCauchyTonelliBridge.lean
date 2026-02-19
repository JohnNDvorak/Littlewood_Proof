import Littlewood.Aristotle.Standalone.LandauCauchyAtCenterTwo
import Littlewood.Aristotle.Standalone.LandauSigmaLessThanOneTonelliTaylor

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LandauSigmaLessThanOneCauchyTonelliBridge

open MeasureTheory Set
open Aristotle.Standalone.LandauCauchyCoefficientStep
open Aristotle.Standalone.LandauCauchyAtCenterTwo
open Aristotle.Standalone.LandauSigmaLessThanOneTonelliTaylor

/--
Bridge theorem for the Landau `σ₀ < 1` branch:
combine Tonelli anti-coefficient domination with Cauchy majorant data from a
power-series witness.

Inputs:
1) partial-integral Tonelli estimate through local anti-coefficients `A N k`,
2) domination `A N k ≤ coeffAtOne p k`,
3) radius datum for `p` giving summability of `∑ coeffAtOne p k * w^k`.

Output: a uniform bound on all partial integrals.
-/
theorem partial_integrals_bounded_of_tonelli_and_radius
    (g : ℝ → ℝ) (T₀ σ₀ w : ℝ)
    (A : ℕ → ℕ → ℝ)
    (p : FormalMultilinearSeries ℂ ℂ ℂ) {r : NNReal}
    (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (hw_nonneg : 0 ≤ w) (hw_lt : w < (r : ℝ))
    (hA_nonneg : ∀ N k : ℕ, 0 ≤ A N k)
    (hA_dom : ∀ N k : ℕ, A N k ≤ coeffAtOne p k)
    (h_tonelli : ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖
        ≤ ∑' k : ℕ, A N k * w ^ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖ ≤ M := by
  have hsumm :
      Summable (fun n : ℕ => coeffAtOne p n * w ^ n) :=
    summable_coeff_eval_one_mul_pow_of_lt_radius p hr0 hr w hw_nonneg hw_lt

  have hmajor :
      ∀ N : ℕ,
        ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖
          ≤ ∑' k : ℕ, coeffAtOne p k * w ^ k :=
    tonelli_taylor_majorant_of_anticoeff_domination
      g T₀ σ₀ w A (coeffAtOne p)
      hw_nonneg hA_nonneg hA_dom hsumm h_tonelli

  refine ⟨∑' k : ℕ, coeffAtOne p k * w ^ k, ?_, hmajor⟩
  refine tsum_nonneg ?_
  intro k
  exact mul_nonneg (norm_nonneg _) (pow_nonneg hw_nonneg _)

/--
Corrected-formula specialization of
`partial_integrals_bounded_of_tonelli_and_radius`.

This packages the Cauchy side through
`correctedFormula_cauchy_majorant_data`, so the only remaining analytic input is
the Tonelli anti-coefficient domination estimate.
-/
theorem correctedFormula_partial_integrals_bounded_of_tonelli
    (α C σ_sign : ℝ) (hα : 1 / 2 < α) (hα2 : α < 2)
    (g : ℝ → ℝ) (T₀ σ₀ w : ℝ)
    (A : ℕ → ℕ → ℝ)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (correctedFormula α C σ_sign) p (2 : ℂ))
    {r : NNReal} (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (hw_nonneg : 0 ≤ w) (hw_lt : w < (r : ℝ))
    (hA_nonneg : ∀ N k : ℕ, 0 ≤ A N k)
    (hA_dom : ∀ N k : ℕ, A N k ≤ coeffAtOne p k)
    (h_tonelli : ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖
        ≤ ∑' k : ℕ, A N k * w ^ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖ ≤ M := by
  -- Pull Cauchy/summability data from the corrected formula witness.
  obtain ⟨_B, _hB, _ha_nonneg, _ha_cauchy, hsumm⟩ :=
    correctedFormula_cauchy_majorant_data
      α C σ_sign hα hα2 p hp hr0 hr w hw_nonneg hw_lt

  have hmajor :
      ∀ N : ℕ,
        ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖
          ≤ ∑' k : ℕ, coeffAtOne p k * w ^ k :=
    tonelli_taylor_majorant_of_anticoeff_domination
      g T₀ σ₀ w A (coeffAtOne p)
      hw_nonneg hA_nonneg hA_dom hsumm h_tonelli

  refine ⟨∑' k : ℕ, coeffAtOne p k * w ^ k, ?_, hmajor⟩
  refine tsum_nonneg ?_
  intro k
  exact mul_nonneg (norm_nonneg _) (pow_nonneg hw_nonneg _)

end Aristotle.Standalone.LandauSigmaLessThanOneCauchyTonelliBridge

