import Littlewood.Aristotle.Standalone.LandauCoefficientDominationConstructive
import Littlewood.Aristotle.Standalone.LandauSigmaLtOneFromAnticoeffSeries
import Littlewood.Aristotle.Standalone.LandauSigmaLtOneFromAnticoeffHasSum
import Littlewood.CoreLemmas.GrowthDomination

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.LandauSigmaLtOneFromAnticoeffPowerSeries

open Filter MeasureTheory Set
open GrowthDomination
open Aristotle.Standalone.LandauCoefficientDominationConstructive
open Aristotle.Standalone.LandauSigmaLtOneFromAnticoeffSeries
open Aristotle.Standalone.LandauSigmaLtOneFromAnticoeffHasSum

/--
Concrete `σ₀ < 1` Landau input:
for each parameter tuple, the corrected formula has a local expansion at center
`2` whose coefficients are exactly the anti-coefficient integrals, and the
radius reaches `w = 2 - σ₀`.
-/
def SigmaLtOneCorrectedFormulaAnticoeffPowerSeriesRadiusHyp : Prop :=
  ∀ (C : ℝ), 0 < C →
    ∀ (α : ℝ), 1 / 2 < α → α < 1 →
      ∀ (σ_sign : ℝ), σ_sign = 1 ∨ σ_sign = -1 →
        (∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α) →
          ∀ (σ₀ : ℝ), α < σ₀ → σ₀ < 1 →
            ∀ (T₀ : ℝ), 1 ≤ T₀ →
              (∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t) →
                ∃ (r : NNReal),
                  0 < r ∧
                    ((r : ENNReal) < (antiCoeffScalarSeries C α σ_sign T₀).radius) ∧
                      2 - σ₀ < (r : ℝ) ∧
                        HasFPowerSeriesAt
                          (Aristotle.Standalone.LandauCauchyAtCenterTwo.correctedFormula
                            α C σ_sign)
                          (antiCoeffScalarSeries C α σ_sign T₀)
                          (2 : ℂ)

/--
Build the anti-coefficient-series hypothesis from a direct
`HasFPowerSeriesAt` witness for `antiCoeffScalarSeries`.
-/
theorem sigmaLtOneCorrectedFormulaAnticoeffSeriesHyp_of_powerSeriesRadius
    (hPower : SigmaLtOneCorrectedFormulaAnticoeffPowerSeriesRadiusHyp) :
    SigmaLtOneCorrectedFormulaAnticoeffSeriesHyp := by
  intro C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn
  rcases hPower C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn with
    ⟨r, hr0, hr, hw_lt, hanti⟩
  let p : FormalMultilinearSeries ℂ ℂ ℂ := antiCoeffScalarSeries C α σ_sign T₀
  refine ⟨p, r, ?_, ?_, hr0, ?_, hw_lt⟩
  · simpa [p] using hanti
  · simpa [p] using hanti
  · simpa [p] using hr

/--
Convert direct anti-coefficient power-series data into the explicit
`HasSum`-near-zero formulation.
-/
theorem sigmaLtOneCorrectedFormulaAnticoeffHasSumRadiusHyp_of_powerSeriesRadius
    (hPower : SigmaLtOneCorrectedFormulaAnticoeffPowerSeriesRadiusHyp) :
    SigmaLtOneCorrectedFormulaAnticoeffHasSumRadiusHyp := by
  intro C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn
  rcases hPower C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn with
    ⟨r, hr0, hr, hw_lt, hanti⟩
  refine ⟨r, hr0, hr, hw_lt, ?_⟩
  rw [hasFPowerSeriesAt_iff] at hanti
  refine hanti.mono ?_
  intro w hw
  simpa [antiCoeffScalarSeries, FormalMultilinearSeries.coeff_ofScalars] using hw

/--
Direct bridge to `LandauAbscissaHyp` from anti-coefficient power-series radius
data at center `2`.
-/
theorem landauAbscissaHyp_of_anticoeffPowerSeriesRadius
    (hPower : SigmaLtOneCorrectedFormulaAnticoeffPowerSeriesRadiusHyp) :
    PringsheimPsiAtom.LandauAbscissaHyp :=
  landauAbscissaHyp_of_anticoeffSeries
    (sigmaLtOneCorrectedFormulaAnticoeffSeriesHyp_of_powerSeriesRadius hPower)

/--
Direct non-RH `ψ` oscillation from anti-coefficient power-series radius data.
-/
theorem psi_omega_lll_of_not_RH_from_anticoeffPowerSeriesRadius
    (hPower : SigmaLtOneCorrectedFormulaAnticoeffPowerSeriesRadiusHyp)
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x] :=
  psi_omega_lll_of_not_RH_from_anticoeffSeries
    (sigmaLtOneCorrectedFormulaAnticoeffSeriesHyp_of_powerSeriesRadius hPower) hRH

end Aristotle.Standalone.LandauSigmaLtOneFromAnticoeffPowerSeries

