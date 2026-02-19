import Littlewood.Aristotle.Standalone.LandauCoefficientDominationConstructive
import Littlewood.Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination
import Littlewood.CoreLemmas.GrowthDomination

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.LandauSigmaLtOneFromAnticoeffSeries

open Filter MeasureTheory Set
open GrowthDomination
open Aristotle.Standalone.LandauCoefficientDominationConstructive

/--
`σ₀ < 1` Landau input in a constructive anti-coefficient-series form.

Compared to `SigmaLtOneCorrectedFormulaDominationHyp`, this replaces explicit
coefficient inequalities by a direct local power-series witness whose
coefficients are exactly the anti-coefficient integrals.
-/
def SigmaLtOneCorrectedFormulaAnticoeffSeriesHyp : Prop :=
  ∀ (C : ℝ), 0 < C →
    ∀ (α : ℝ), 1 / 2 < α → α < 1 →
      ∀ (σ_sign : ℝ), σ_sign = 1 ∨ σ_sign = -1 →
        (∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α) →
          ∀ (σ₀ : ℝ), α < σ₀ → σ₀ < 1 →
            ∀ (T₀ : ℝ), 1 ≤ T₀ →
              (∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t) →
                ∃ (p : FormalMultilinearSeries ℂ ℂ ℂ) (r : NNReal),
                  HasFPowerSeriesAt
                    (Aristotle.Standalone.LandauCauchyAtCenterTwo.correctedFormula α C σ_sign)
                    p (2 : ℂ) ∧
                    HasFPowerSeriesAt
                      (Aristotle.Standalone.LandauCauchyAtCenterTwo.correctedFormula α C σ_sign)
                      (antiCoeffScalarSeries C α σ_sign T₀) (2 : ℂ) ∧
                    0 < r ∧
                    (r : ENNReal) < p.radius ∧
                    2 - σ₀ < (r : ℝ)

/--
Build `SigmaLtOneCorrectedFormulaDominationHyp` from an anti-coefficient local
power-series witness.
-/
theorem sigmaLtOneCorrectedFormulaDominationHyp_of_anticoeffSeries
    (hSeries : SigmaLtOneCorrectedFormulaAnticoeffSeriesHyp) :
    Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination.SigmaLtOneCorrectedFormulaDominationHyp := by
  intro C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn
  rcases hSeries C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn with
    ⟨p, r, hp, hanti, hr0, hr, hw_lt⟩
  refine ⟨p, r, hp, hr0, hr, hw_lt, ?_⟩
  exact hcoeff_dom_of_anticoeff_powerSeries C α σ_sign T₀ hT₀ hg_nn p hp hanti

/--
Direct bridge to `LandauAbscissaHyp` from the anti-coefficient-series shape.
-/
theorem landauAbscissaHyp_of_anticoeffSeries
    (hSeries : SigmaLtOneCorrectedFormulaAnticoeffSeriesHyp) :
    PringsheimPsiAtom.LandauAbscissaHyp :=
  Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination.landauAbscissaHyp_of_correctedFormula_domination
    (sigmaLtOneCorrectedFormulaDominationHyp_of_anticoeffSeries hSeries)

/--
Direct non-RH `ψ`-oscillation bridge from anti-coefficient-series data.
-/
theorem psi_omega_lll_of_not_RH_from_anticoeffSeries
    (hSeries : SigmaLtOneCorrectedFormulaAnticoeffSeriesHyp)
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x] :=
  Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination.psi_omega_lll_of_not_RH_from_correctedFormula_domination
    (sigmaLtOneCorrectedFormulaDominationHyp_of_anticoeffSeries hSeries) hRH

end Aristotle.Standalone.LandauSigmaLtOneFromAnticoeffSeries
