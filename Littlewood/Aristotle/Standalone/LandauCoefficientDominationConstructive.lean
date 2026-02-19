import Littlewood.Aristotle.Standalone.LandauCauchyAtCenterTwo
import Littlewood.Aristotle.Standalone.LandauSigmaLessThanOneTonelliConcrete
import Littlewood.Aristotle.PringsheimPsiAtom

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Topology

namespace Aristotle.Standalone.LandauCoefficientDominationConstructive

open Filter MeasureTheory Set
open Aristotle.Standalone.LandauCauchyAtCenterTwo
open Aristotle.Standalone.LandauSigmaLessThanOneTonelliConcrete
open Aristotle.Standalone.LandauCauchyCoefficientStep

/--
Scalar formal series whose coefficients are Landau anti-coefficients on the tail
`(T₀, ∞)` at center `2`.
-/
def antiCoeffScalarSeries
    (C α σ_sign T₀ : ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun k : ℕ =>
    ((∫ t in Ioi T₀,
      antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) : ℂ))

private theorem antiCoeffProfile_nonneg_ae
    (C α σ_sign T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t)
    (k : ℕ) :
    0 ≤ᵐ[volume.restrict (Ioi T₀)] fun t : ℝ =>
      antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t := by
  refine (ae_restrict_mem measurableSet_Ioi).mono ?_
  intro t ht
  have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hfac_pos : 0 < (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  unfold antiCoeffProfile
  exact mul_nonneg
    (mul_nonneg (hg_nn t (le_of_lt ht)) (Real.rpow_nonneg (le_of_lt ht_pos) _))
    (div_nonneg (pow_nonneg hlog_nonneg _) hfac_pos.le)

private theorem antiCoeff_integral_nonneg
    (C α σ_sign T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t)
    (k : ℕ) :
    0 ≤ ∫ t in Ioi T₀,
      antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t := by
  exact integral_nonneg_of_ae
    (antiCoeffProfile_nonneg_ae C α σ_sign T₀ hT₀ hg_nn k)

/--
Build the anti-coefficient local power-series witness at center `2` from an
eventual `HasSum` identity in `w = s - 2`.
-/
theorem hasFPowerSeriesAt_correctedFormula_of_anticoeff_hasSum
    (C α σ_sign T₀ : ℝ)
    (hseries :
      ∀ᶠ w in 𝓝 (0 : ℂ),
        HasSum
          (fun n : ℕ =>
            w ^ n •
              ((∫ t in Ioi T₀,
                antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) n t) : ℂ))
          (correctedFormula α C σ_sign (2 + w))) :
    HasFPowerSeriesAt (correctedFormula α C σ_sign)
      (antiCoeffScalarSeries C α σ_sign T₀) (2 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  refine hseries.mono ?_
  intro w hw
  simpa [antiCoeffScalarSeries, FormalMultilinearSeries.coeff_ofScalars] using hw

/--
Constructive coefficient domination for Landau's anti-coefficients.

If the corrected Landau formula has:
1. a local power series witness `p` at center `2`, and
2. a local power series witness at the same center whose coefficients are exactly
   the anti-coefficient integrals on `(T₀, ∞)`,

then each anti-coefficient integral is bounded by `coeffAtOne p k`.

This is the exact `hcoeff_dom` obligation used in the standalone `σ₀ < 1` bridge.
-/
theorem hcoeff_dom_of_anticoeff_powerSeries
    (C α σ_sign T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (correctedFormula α C σ_sign) p (2 : ℂ))
    (hanti :
      HasFPowerSeriesAt (correctedFormula α C σ_sign)
        (antiCoeffScalarSeries C α σ_sign T₀) (2 : ℂ)) :
    ∀ k : ℕ,
      (∫ t in Ioi T₀,
        antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) ≤ coeffAtOne p k := by
  have hp_eq :
      p = antiCoeffScalarSeries C α σ_sign T₀ :=
    hp.eq_formalMultilinearSeries hanti
  intro k
  have hnonneg :
      0 ≤ ∫ t in Ioi T₀,
        antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t :=
    antiCoeff_integral_nonneg C α σ_sign T₀ hT₀ hg_nn k
  have hcoeff_eval :
      coeffAtOne p k =
        ‖((∫ t in Ioi T₀,
          antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) : ℂ)‖ := by
    rw [hp_eq, coeffAtOne, antiCoeffScalarSeries]
    simpa using congrArg norm
      (FormalMultilinearSeries.ofScalars_apply_eq
        (E := ℂ)
        (c := fun n : ℕ =>
          ((∫ t in Ioi T₀,
            antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) n t) : ℂ))
        (x := (1 : ℂ)) (n := k))
  have habs_to_norm :
      |∫ t in Ioi T₀,
        antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t|
        =
      ‖((∫ t in Ioi T₀,
        antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) : ℂ)‖ := by
    let I : ℝ :=
      ∫ t in Ioi T₀, antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t
    calc
      |I| = ‖I‖ := by rw [Real.norm_eq_abs]
      _ = ‖((I : ℂ))‖ := by simpa using (Complex.norm_real I).symm
      _ =
          ‖∫ t in Ioi T₀,
              ((antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t : ℝ) : ℂ)‖ := by
            congr 1
            dsimp [I]
            symm
            exact
              integral_ofReal
                (μ := volume.restrict (Ioi T₀))
                (f := fun t : ℝ =>
                  antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t)
  calc
    (∫ t in Ioi T₀,
      antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t)
        ≤
      |∫ t in Ioi T₀,
        antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t| := by
          simpa [abs_of_nonneg hnonneg] using
            (le_rfl :
              (∫ t in Ioi T₀,
                antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t)
                ≤
              (∫ t in Ioi T₀,
                antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t))
    _ =
      ‖((∫ t in Ioi T₀,
        antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) : ℂ)‖ := habs_to_norm
    _ = coeffAtOne p k := hcoeff_eval.symm

/--
Constructive coefficient domination from an explicit anti-coefficient `HasSum`
identity near center `2`.
-/
theorem hcoeff_dom_of_anticoeff_hasSum
    (C α σ_sign T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (correctedFormula α C σ_sign) p (2 : ℂ))
    (hseries :
      ∀ᶠ w in 𝓝 (0 : ℂ),
        HasSum
          (fun n : ℕ =>
            w ^ n •
              ((∫ t in Ioi T₀,
                antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) n t) : ℂ))
          (correctedFormula α C σ_sign (2 + w))) :
    ∀ k : ℕ,
      (∫ t in Ioi T₀,
        antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) ≤ coeffAtOne p k := by
  have hanti :
      HasFPowerSeriesAt (correctedFormula α C σ_sign)
        (antiCoeffScalarSeries C α σ_sign T₀) (2 : ℂ) :=
    hasFPowerSeriesAt_correctedFormula_of_anticoeff_hasSum C α σ_sign T₀ hseries
  exact hcoeff_dom_of_anticoeff_powerSeries C α σ_sign T₀ hT₀ hg_nn p hp hanti

end Aristotle.Standalone.LandauCoefficientDominationConstructive
