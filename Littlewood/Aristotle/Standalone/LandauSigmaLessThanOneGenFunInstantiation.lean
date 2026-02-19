import Littlewood.Aristotle.PringsheimPsiAtom
import Littlewood.Aristotle.Standalone.LandauSigmaLessThanOneTonelliConcrete

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LandauSigmaLessThanOneGenFunInstantiation

open MeasureTheory Set
open Aristotle.Standalone.LandauSigmaLessThanOneTonelliConcrete
open Aristotle.Standalone.LandauCauchyCoefficientStep

/-- Measurability of Landau's generating function `genFun`. -/
private theorem genFun_measurable (C α σ_sign : ℝ) :
    Measurable (fun t : ℝ => PringsheimPsiAtom.genFun C α σ_sign t) := by
  unfold PringsheimPsiAtom.genFun
  exact (measurable_id.pow_const α |>.const_mul C).add
    ((measurable_id.sub Chebyshev.psi_mono.measurable).const_mul σ_sign)

/-- Measurability of the Landau integrand on partial intervals. -/
private theorem genFun_integrand_measurable (C α σ_sign σ₀ : ℝ) :
    Measurable (fun t : ℝ => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))) := by
  exact (genFun_measurable C α σ_sign).mul (measurable_id.pow_const _)

/--
`IntegrableOn` of the Landau integrand on each finite interval `(T₀, T₀+N]`.

This is the concrete `hmain_int` side needed by the Tonelli/Cauchy bridge.
-/
theorem genFun_integrableOn_partialIntervals
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα1 : α ≤ 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (σ₀ : ℝ) (hσ₀_pos : 0 < σ₀)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀) :
    ∀ N : ℕ,
      IntegrableOn
        (fun t : ℝ => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
        (Ioc T₀ (T₀ + (N : ℝ))) := by
  obtain ⟨D, hD, hle⟩ := PringsheimPsiAtom.genFun_le_linear C hC α hα1 σ_sign hσ
  intro N
  apply Measure.integrableOn_of_bounded (measure_Ioc_lt_top.ne)
    ((genFun_integrand_measurable C α σ_sign σ₀).aestronglyMeasurable) (M := D * (T₀ + (N : ℝ)))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht_pos : 0 < t := by linarith [hT₀, ht.1]
  have ht1 : 1 ≤ t := by linarith [hT₀, ht.1]
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |PringsheimPsiAtom.genFun C α σ_sign t| * |t ^ (-(σ₀ + 1))|
        ≤ (D * t) * 1 := by
          apply mul_le_mul (hle t ht1) ?_ (abs_nonneg _) (by positivity)
          rw [abs_of_pos (Real.rpow_pos_of_pos ht_pos _)]
          exact Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
    _ = D * t := by ring
    _ ≤ D * (T₀ + (N : ℝ)) := by
          exact mul_le_mul_of_nonneg_left ht.2 (le_of_lt hD)

/-- The norm-integrable version of `genFun_integrableOn_partialIntervals`. -/
theorem genFun_norm_integrableOn_partialIntervals
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα1 : α ≤ 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (σ₀ : ℝ) (hσ₀_pos : 0 < σ₀)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀) :
    ∀ N : ℕ,
      IntegrableOn
        (fun t : ℝ => ‖PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))‖)
        (Ioc T₀ (T₀ + (N : ℝ))) := by
  intro N
  exact (genFun_integrableOn_partialIntervals C hC α hα1 σ_sign hσ σ₀ hσ₀_pos T₀ hT₀ N).norm

/--
Integrability of Landau anti-coefficient profiles on the full tail.

For each `k`, the profile
`antiCoeffProfile (genFun C α σ_sign) k t = g(t) t^{-3} (log t)^k / k!`
is dominated by `K * t^{-3/2}` on `t > T₀`, hence integrable on `(T₀, ∞)`.
-/
theorem genFun_antiCoeffProfile_integrableOn_tail
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα1 : α ≤ 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀) :
    ∀ k : ℕ,
      IntegrableOn
        (fun t : ℝ => antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t)
        (Ioi T₀) := by
  have hg_meas : Measurable (fun t : ℝ => PringsheimPsiAtom.genFun C α σ_sign t) :=
    genFun_measurable C α σ_sign
  intro k
  obtain ⟨D, hD, hD_bound⟩ := PringsheimPsiAtom.genFun_le_linear C hC α hα1 σ_sign hσ
  let p : ℝ := (2 * ((k : ℝ) + 1))⁻¹
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  let K : ℝ := D * ((1 / p) ^ k / (k.factorial : ℝ))
  have hdom_int : IntegrableOn (fun t : ℝ => K * t ^ (-(3 / 2 : ℝ))) (Ioi T₀) := by
    exact (integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (c := T₀)
      (by norm_num) (by linarith)).const_mul K
  refine hdom_int.mono' ?_ ?_
  · exact ((hg_meas.mul (measurable_id.pow_const (-(3 : ℝ)))).mul
      ((Real.measurable_log.pow_const k).div_const (k.factorial : ℝ))).aestronglyMeasurable.restrict
  · refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
    have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hfac_pos : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hfrac_nonneg : 0 ≤ (Real.log t) ^ k / (k.factorial : ℝ) :=
      div_nonneg (pow_nonneg hlog_nonneg _) hfac_pos.le
    have hpow_nonneg : 0 ≤ t ^ (-(3 : ℝ)) := Real.rpow_nonneg (le_of_lt ht_pos) _
    have hgen : |PringsheimPsiAtom.genFun C α σ_sign t| ≤ D * t := hD_bound t ht1
    have hlog_le : Real.log t ≤ t ^ p / p := Real.log_le_rpow_div ht_pos.le hp_pos
    have hlog_pow_le : (Real.log t) ^ k ≤ (t ^ p / p) ^ k :=
      pow_le_pow_left₀ hlog_nonneg hlog_le k
    have hpk_le : p * (k : ℝ) ≤ (1 / 2 : ℝ) := by
      have hk_le : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
      have hmul_le :
          p * (k : ℝ) ≤ p * ((k : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_left hk_le (le_of_lt hp_pos)
      have hp_eval : p * ((k : ℝ) + 1) = (1 / 2 : ℝ) := by
        have hk1_ne : (k : ℝ) + 1 ≠ 0 := by positivity
        dsimp [p]
        field_simp [hk1_ne]
      exact hmul_le.trans_eq hp_eval
    have hpow_tp_le : (t ^ p) ^ k ≤ t ^ (1 / 2 : ℝ) := by
      have hpow_eq : (t ^ p) ^ k = t ^ (p * (k : ℝ)) := by
        simpa [mul_comm] using (Real.rpow_mul_natCast (le_of_lt ht_pos) p k).symm
      rw [hpow_eq]
      exact Real.rpow_le_rpow_of_exponent_le ht1 hpk_le
    have hpow_div_le :
        (t ^ p / p) ^ k ≤ (1 / p) ^ k * t ^ (1 / 2 : ℝ) := by
      rw [div_eq_mul_inv, mul_pow]
      have hconst_nonneg : 0 ≤ (1 / p) ^ k := by positivity
      have hmul := mul_le_mul_of_nonneg_right hpow_tp_le hconst_nonneg
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    rw [Real.norm_eq_abs]
    unfold antiCoeffProfile
    rw [abs_mul, abs_mul, abs_of_nonneg hpow_nonneg, abs_of_nonneg hfrac_nonneg]
    calc
      |PringsheimPsiAtom.genFun C α σ_sign t| * t ^ (-(3 : ℝ)) * ((Real.log t) ^ k / (k.factorial : ℝ))
          ≤ (D * t) * t ^ (-(3 : ℝ)) * ((Real.log t) ^ k / (k.factorial : ℝ)) := by
            gcongr
      _ ≤ (D * t) * t ^ (-(3 : ℝ)) * (((t ^ p / p) ^ k) / (k.factorial : ℝ)) := by
            gcongr
      _ ≤ (D * t) * t ^ (-(3 : ℝ)) * ((((1 / p) ^ k) * t ^ (1 / 2 : ℝ)) / (k.factorial : ℝ)) := by
            have hleft_nonneg : 0 ≤ (D * t) * t ^ (-(3 : ℝ)) := by
              exact mul_nonneg
                (mul_nonneg (le_of_lt hD) (le_of_lt ht_pos))
                (Real.rpow_nonneg (le_of_lt ht_pos) _)
            have hdiv_le :
                ((t ^ p / p) ^ k) / (k.factorial : ℝ)
                  ≤ (((1 / p) ^ k) * t ^ (1 / 2 : ℝ)) / (k.factorial : ℝ) :=
              div_le_div_of_nonneg_right hpow_div_le hfac_pos.le
            exact mul_le_mul_of_nonneg_left hdiv_le hleft_nonneg
      _ = K * t ^ (-(3 / 2 : ℝ)) := by
            dsimp [K]
            have h_t : t * t ^ (-(3 : ℝ)) * t ^ (1 / 2 : ℝ) = t ^ (-(3 / 2 : ℝ)) := by
              calc
                t * t ^ (-(3 : ℝ)) * t ^ (1 / 2 : ℝ)
                    = (t ^ (1 : ℝ) * t ^ (-(3 : ℝ))) * t ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
                _ = t ^ ((1 : ℝ) + (-(3 : ℝ))) * t ^ (1 / 2 : ℝ) := by
                      rw [← Real.rpow_add ht_pos]
                _ = t ^ (-(2 : ℝ)) * t ^ (1 / 2 : ℝ) := by ring_nf
                _ = t ^ (-(2 : ℝ) + (1 / 2 : ℝ)) := by rw [← Real.rpow_add ht_pos]
                _ = t ^ (-(3 / 2 : ℝ)) := by ring_nf
            calc
              (D * t) * t ^ (-(3 : ℝ)) * (((1 / p) ^ k * t ^ (1 / 2 : ℝ)) / (k.factorial : ℝ))
                  = D * ((1 / p) ^ k / (k.factorial : ℝ)) * (t * t ^ (-(3 : ℝ)) * t ^ (1 / 2 : ℝ)) := by
                    ring
              _ = D * ((1 / p) ^ k / (k.factorial : ℝ)) * t ^ (-(3 / 2 : ℝ)) := by rw [h_t]
              _ = D * ((1 / p) ^ k / (k.factorial : ℝ)) * t ^ (-(3 / 2 : ℝ)) := rfl

/--
Landau `genFun` specialization of the concrete Tonelli/Cauchy bound.

This discharges the `hmain_int` obligation automatically; the remaining
assumption is the deep anti-coefficient domination obligation (`hcoeff_dom`)
plus radius/Cauchy inputs.
-/
theorem genFun_partial_integrals_bounded_of_anticoeff_cauchy_domination
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα1 : α ≤ 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (σ₀ : ℝ) (hσ₀_pos : 0 < σ₀) (hσ₀_lt1 : σ₀ < 1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nonneg : ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t)
    (p : FormalMultilinearSeries ℂ ℂ ℂ) {r : NNReal}
    (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (hw_lt : 2 - σ₀ < (r : ℝ))
    (hcoeff_dom : ∀ k : ℕ,
      (∫ t in Ioi T₀,
        antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) ≤ coeffAtOne p k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)),
        ‖PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))‖ ≤ M := by
  refine partial_integrals_bounded_of_anticoeff_cauchy_domination
    (g := PringsheimPsiAtom.genFun C α σ_sign)
    T₀ σ₀ hT₀ hσ₀_lt1
    (genFun_measurable C α σ_sign)
    hg_nonneg
    (genFun_norm_integrableOn_partialIntervals C hC α hα1 σ_sign hσ σ₀ hσ₀_pos T₀ hT₀)
    (genFun_antiCoeffProfile_integrableOn_tail C hC α hα1 σ_sign hσ T₀ hT₀)
    p hr0 hr hw_lt hcoeff_dom

end Aristotle.Standalone.LandauSigmaLessThanOneGenFunInstantiation
