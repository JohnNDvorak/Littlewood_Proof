import Littlewood.Aristotle.Standalone.LandauCoefficientDominationConstructive
import Littlewood.Aristotle.Standalone.LandauSigmaLtOneFromAnticoeffSeries
import Littlewood.CoreLemmas.GrowthDomination

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics Topology

namespace Aristotle.Standalone.LandauSigmaLtOneFromAnticoeffHasSum

open Filter MeasureTheory Set
open Aristotle.Standalone.LandauCoefficientDominationConstructive
open Aristotle.Standalone.LandauSigmaLtOneFromAnticoeffSeries
open Aristotle.Standalone.LandauSigmaLessThanOneTonelliConcrete
open GrowthDomination

/--
Concrete `σ₀ < 1` Landau input:
for each parameter tuple, the anti-coefficient series around center `2` is given
by a local `HasSum` identity and has radius large enough to reach `w = 2 - σ₀`.
-/
def SigmaLtOneCorrectedFormulaAnticoeffHasSumRadiusHyp : Prop :=
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
                        (∀ᶠ w in 𝓝 (0 : ℂ),
                          HasSum
                            (fun n : ℕ =>
                              w ^ n •
                                ((∫ t in Ioi T₀,
                                  antiCoeffProfile
                                    (PringsheimPsiAtom.genFun C α σ_sign) n t) : ℂ))
                            (Aristotle.Standalone.LandauCauchyAtCenterTwo.correctedFormula
                              α C σ_sign (2 + w)))

/--
Build the anti-coefficient-series hypothesis used by the constructive Landau chain
from the explicit `HasSum`+radius formulation.
-/
theorem sigmaLtOneCorrectedFormulaAnticoeffSeriesHyp_of_hasSumRadius
    (hHasSum : SigmaLtOneCorrectedFormulaAnticoeffHasSumRadiusHyp) :
    SigmaLtOneCorrectedFormulaAnticoeffSeriesHyp := by
  intro C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn
  rcases hHasSum C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn with
    ⟨r, hr0, hr, hw_lt, hseries⟩
  let p : FormalMultilinearSeries ℂ ℂ ℂ := antiCoeffScalarSeries C α σ_sign T₀
  have hanti :
      HasFPowerSeriesAt
        (Aristotle.Standalone.LandauCauchyAtCenterTwo.correctedFormula α C σ_sign)
        p (2 : ℂ) :=
    hasFPowerSeriesAt_correctedFormula_of_anticoeff_hasSum C α σ_sign T₀ hseries
  refine ⟨p, r, ?_, hanti, hr0, ?_, hw_lt⟩
  · simpa [p] using hanti
  · simpa [p] using hr

/--
Direct bridge to the exact `LandauAbscissaHyp` payload from the concrete
anti-coefficient `HasSum`+radius hypothesis.
-/
theorem landauAbscissaHyp_of_anticoeffHasSumRadius
    (hHasSum : SigmaLtOneCorrectedFormulaAnticoeffHasSumRadiusHyp) :
    PringsheimPsiAtom.LandauAbscissaHyp :=
  landauAbscissaHyp_of_anticoeffSeries
    (sigmaLtOneCorrectedFormulaAnticoeffSeriesHyp_of_hasSumRadius hHasSum)

/--
Direct non-RH `ψ` oscillation from the concrete anti-coefficient `HasSum`+radius
hypothesis.
-/
theorem psi_omega_lll_of_not_RH_from_anticoeffHasSumRadius
    (hHasSum : SigmaLtOneCorrectedFormulaAnticoeffHasSumRadiusHyp)
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x] :=
  psi_omega_lll_of_not_RH_from_anticoeffSeries
    (sigmaLtOneCorrectedFormulaAnticoeffSeriesHyp_of_hasSumRadius hHasSum) hRH

end Aristotle.Standalone.LandauSigmaLtOneFromAnticoeffHasSum
