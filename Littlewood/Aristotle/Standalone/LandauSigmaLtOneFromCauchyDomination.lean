import Littlewood.Aristotle.LandauAbscissaProof
import Littlewood.Aristotle.LandauSchmidtDirect
import Littlewood.Aristotle.NonNegDirichletIntegral
import Littlewood.Aristotle.Standalone.LandauSigmaLessThanOneGenFunInstantiation
import Littlewood.Aristotle.Standalone.LandauCauchyAtCenterTwo
import Littlewood.Aristotle.Standalone.LandauPringsheimRealLine
import Littlewood.CoreLemmas.GrowthDomination

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination

open Filter MeasureTheory Set
open GrowthDomination
open Aristotle.Standalone.LandauSigmaLessThanOneGenFunInstantiation
open Aristotle.Standalone.LandauCauchyCoefficientStep
open Aristotle.Standalone.LandauSigmaLessThanOneTonelliConcrete

/--
Standalone `σ₀ < 1` Landau tail-integrability step from explicit Cauchy
coefficient domination data.

This theorem turns the concrete anti-coefficient obligations
(`hcoeff_dom`) into full `IntegrableOn` on `(T₀, ∞)`.
-/
theorem tail_integrableOn_sigma_lt_one_of_cauchy_domination
    (C : ℝ) (hC : 0 < C)
    (α : ℝ) (hα : 1 / 2 < α) (_hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀_lt1 : σ₀ < 1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t)
    (p : FormalMultilinearSeries ℂ ℂ ℂ) {r : NNReal}
    (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (hw_lt : 2 - σ₀ < (r : ℝ))
    (hcoeff_dom : ∀ k : ℕ,
      (∫ t in Ioi T₀,
        antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) ≤ coeffAtOne p k) :
    IntegrableOn
      (fun t : ℝ => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
      (Ioi T₀) := by
  have hα1_le : α ≤ 1 := by linarith
  have hσ₀_pos : 0 < σ₀ := by linarith
  have hg_nonneg_mem :
      ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t := by
    intro t ht
    exact hg_nn t (le_of_lt ht)
  obtain ⟨M, _hM_nonneg, hM⟩ :=
    genFun_partial_integrals_bounded_of_anticoeff_cauchy_domination
      C hC α hα1_le σ_sign hσ σ₀ hσ₀_pos hσ₀_lt1
      T₀ hT₀ hg_nonneg_mem p hr0 hr hw_lt hcoeff_dom
  have h_tendsto : Tendsto (fun n : ℕ => T₀ + (↑n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ T₀ tendsto_natCast_atTop_atTop
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (f := fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
    (μ := volume) (l := atTop) (b := fun n : ℕ => T₀ + ↑n) M T₀
  · intro n
    exact genFun_integrableOn_partialIntervals
      C hC α hα1_le σ_sign hσ σ₀ hσ₀_pos T₀ hT₀ n
  · exact h_tendsto
  · filter_upwards with n
    rw [intervalIntegral.integral_of_le (by linarith : T₀ ≤ T₀ + (↑n : ℝ))]
    exact hM n

/--
Deep Landau input, made explicit at the anti-coefficient/Cauchy-domination level.

This is strictly stronger/more concrete than `LandauAbscissaProof.SigmaLtOneHyp`:
it specifies the exact Cauchy-majorant domination obligation needed to produce
tail convergence.
-/
def SigmaLtOneCauchyDominationHyp : Prop :=
  ∀ (C : ℝ), 0 < C →
    ∀ (α : ℝ), 1 / 2 < α → α < 1 →
      ∀ (σ_sign : ℝ), σ_sign = 1 ∨ σ_sign = -1 →
        (∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α) →
          ∀ (σ₀ : ℝ), α < σ₀ → σ₀ < 1 →
            ∀ (T₀ : ℝ), 1 ≤ T₀ →
              (∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t) →
                ∃ (p : FormalMultilinearSeries ℂ ℂ ℂ) (r : NNReal),
                  0 < r ∧
                    (r : ENNReal) < p.radius ∧
                      2 - σ₀ < (r : ℝ) ∧
                        (∀ k : ℕ,
                          (∫ t in Ioi T₀,
                            antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t)
                            ≤ coeffAtOne p k)

/--
Construct `LandauAbscissaProof.SigmaLtOneHyp` from explicit Cauchy-domination
data.
-/
theorem sigmaLtOneHyp_of_cauchy_domination
    (hDom : SigmaLtOneCauchyDominationHyp) :
    Aristotle.LandauAbscissaProof.SigmaLtOneHyp := by
  intro C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn
  rcases hDom C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn with
    ⟨p, r, hr0, hr, hw_lt, hcoeff_dom⟩
  exact tail_integrableOn_sigma_lt_one_of_cauchy_domination
    C hC α hα hα1 σ_sign hσ σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn
    p hr0 hr hw_lt hcoeff_dom

/--
`σ₀ < 1` hypothesis in a corrected-formula-faithful shape:
the dominating coefficients come from an actual local power series of the
corrected Landau formula at center `2`.
-/
def SigmaLtOneCorrectedFormulaDominationHyp : Prop :=
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
                    0 < r ∧
                    (r : ENNReal) < p.radius ∧
                    2 - σ₀ < (r : ℝ) ∧
                    (∀ k : ℕ,
                      (∫ t in Ioi T₀,
                        antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t)
                        ≤ coeffAtOne p k)

/--
Build `LandauAbscissaProof.SigmaLtOneHyp` from corrected-formula local
power-series domination data.
-/
theorem sigmaLtOneHyp_of_correctedFormula_domination
    (hDom : SigmaLtOneCorrectedFormulaDominationHyp) :
    Aristotle.LandauAbscissaProof.SigmaLtOneHyp := by
  intro C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn
  rcases hDom C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn with
    ⟨p, r, hp, hr0, hr, hw_lt, hcoeff_dom⟩
  exact Aristotle.Standalone.LandauPringsheimRealLine.tail_integrableOn_sigma_lt_one_pringsheim
    C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn
    p hp hr0 hr hw_lt hcoeff_dom

/--
Direct bridge to the exact Landau abscissa payload used by `PringsheimPsiAtom`.
-/
theorem landauAbscissaHyp_of_correctedFormula_domination
    (hDom : SigmaLtOneCorrectedFormulaDominationHyp) :
    PringsheimPsiAtom.LandauAbscissaHyp :=
  Aristotle.LandauAbscissaProof.landau_abscissa_hyp_proved
    (sigmaLtOneHyp_of_correctedFormula_domination hDom)

/--
Direct non-RH `ψ`-oscillation bridge from corrected-formula sigma<1 domination.

This packages the same chain used in `DeepSorries`:
`SigmaLtOne` → `LandauAbscissaHyp` → `pringsheim_psi_atom` →
`psi_dirichlet_integral` → `LandauSchmidtDirect`.
-/
theorem psi_omega_lll_of_not_RH_from_correctedFormula_domination
    (hDom : SigmaLtOneCorrectedFormulaDominationHyp)
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x] := by
  exact Aristotle.LandauSchmidtDirect.psi_omega_lll_of_not_RH
    (Aristotle.NonNegDirichletIntegral.psi_dirichlet_integral
      (Aristotle.PringsheimPsiAtom.pringsheim_psi_atom
        (landauAbscissaHyp_of_correctedFormula_domination hDom)))
    hRH

/-- Direct bridge from `SigmaLtOneHyp` to `LandauAbscissaHyp` (bypasses coefficient
domination). -/
theorem landauAbscissaHyp_of_sigmaLtOne
    (hyp : Aristotle.LandauAbscissaProof.SigmaLtOneHyp) :
    PringsheimPsiAtom.LandauAbscissaHyp :=
  Aristotle.LandauAbscissaProof.landau_abscissa_hyp_proved hyp

/-- Direct non-RH `ψ`-oscillation bridge from `SigmaLtOneHyp`. -/
theorem psi_omega_lll_of_not_RH_from_sigmaLtOne
    (hyp : Aristotle.LandauAbscissaProof.SigmaLtOneHyp)
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x] :=
  Aristotle.LandauSchmidtDirect.psi_omega_lll_of_not_RH
    (Aristotle.NonNegDirichletIntegral.psi_dirichlet_integral
      (Aristotle.PringsheimPsiAtom.pringsheim_psi_atom
        (landauAbscissaHyp_of_sigmaLtOne hyp)))
    hRH

end Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination
