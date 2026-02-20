import Littlewood.Aristotle.Standalone.LandauSigmaLessThanOneTonelliLIntegral
import Littlewood.Aristotle.Standalone.LandauCauchyCoefficientStep

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LandauSigmaLessThanOneTonelliConcrete

open MeasureTheory Set
open Aristotle.Standalone.LandauCauchyCoefficientStep

/--
Anti-coefficient profile used in Landau's `σ₀ < 1` Tonelli expansion,
centered at `2`:
`g(t) * t^{-3} * (log t)^k / k!`.
-/
def antiCoeffProfile (g : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  g t * t ^ (-(3 : ℝ)) * ((Real.log t) ^ k / (k.factorial : ℝ))

private theorem antiCoeffProfile_measurable
    (g : ℝ → ℝ) (hg_meas : Measurable g) (k : ℕ) :
    Measurable (fun t : ℝ => antiCoeffProfile g k t) := by
  exact (hg_meas.mul (measurable_id.pow_const (-(3 : ℝ)))).mul
    ((Real.measurable_log.pow_const k).div_const (k.factorial : ℝ))

theorem antiCoeffProfile_nonneg_on_tail
    (g : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nonneg : ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ g t)
    (k : ℕ) :
    ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ antiCoeffProfile g k t := by
  intro t ht
  have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hfac_pos : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hpow_log_nonneg : 0 ≤ (Real.log t) ^ k := pow_nonneg hlog_nonneg _
  have hfrac_nonneg : 0 ≤ (Real.log t) ^ k / (k.factorial : ℝ) :=
    div_nonneg hpow_log_nonneg hfac_pos.le
  unfold antiCoeffProfile
  exact mul_nonneg
    (mul_nonneg (hg_nonneg t ht) (Real.rpow_nonneg (le_of_lt ht_pos) _))
    hfrac_nonneg

private lemma integrand_eq_tsum_anticoeff
    (g : ℝ → ℝ) (σ₀ t : ℝ) (ht : 0 < t) :
    g t * t ^ (-(σ₀ + 1)) =
      ∑' k : ℕ, antiCoeffProfile g k t * (2 - σ₀) ^ k := by
  have hsplit : t ^ (-(σ₀ + 1 : ℝ)) = t ^ (-(3 : ℝ)) * t ^ (2 - σ₀) := by
    have hexp : -(σ₀ + 1 : ℝ) = (-(3 : ℝ)) + (2 - σ₀) := by ring
    rw [hexp, Real.rpow_add ht]
  calc
    g t * t ^ (-(σ₀ + 1 : ℝ))
        = g t * (t ^ (-(3 : ℝ)) * t ^ (2 - σ₀)) := by rw [hsplit]
    _ = (g t * t ^ (-(3 : ℝ))) * Real.exp ((2 - σ₀) * Real.log t) := by
          rw [Real.rpow_def_of_pos ht (2 - σ₀)]
          have hmul : Real.log t * (2 - σ₀) = (2 - σ₀) * Real.log t := by ring
          rw [hmul]
          ring
    _ = (g t * t ^ (-(3 : ℝ))) *
          (∑' k : ℕ, (((2 - σ₀) * Real.log t) ^ k / (k.factorial : ℝ))) := by
          have hExp :
              Real.exp ((2 - σ₀) * Real.log t) =
                ∑' k : ℕ, (((2 - σ₀) * Real.log t) ^ k / (k.factorial : ℝ)) := by
            simpa [Real.exp_eq_exp_ℝ] using congrArg (fun f : ℝ → ℝ => f ((2 - σ₀) * Real.log t))
              (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ))
          rw [hExp]
    _ = ∑' k : ℕ,
          (g t * t ^ (-(3 : ℝ))) * (((2 - σ₀) * Real.log t) ^ k / (k.factorial : ℝ)) := by
          rw [← tsum_mul_left]
    _ = ∑' k : ℕ, antiCoeffProfile g k t * (2 - σ₀) ^ k := by
          refine tsum_congr ?_
          intro k
          unfold antiCoeffProfile
          rw [mul_pow]
          ring_nf

/--
Pointwise Tonelli expansion on the positive tail.

For `t > T₀ ≥ 1`, `σ₀ < 1`, and `g(t) ≥ 0`, the Landau integrand equals the
weighted anti-coefficient series in `ENNReal` form.
-/
theorem pointwise_norm_eq_tsum_anticoeff_on_tail
    (g : ℝ → ℝ) (T₀ σ₀ : ℝ)
    (hT₀ : 1 ≤ T₀) (hσ₀_lt1 : σ₀ < 1)
    (hg_nonneg : ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ g t) :
    ∀ t : ℝ, t ∈ Ioi T₀ →
      ENNReal.ofReal ‖g t * t ^ (-(σ₀ + 1))‖ =
        ∑' k : ℕ, ENNReal.ofReal (antiCoeffProfile g k t * (2 - σ₀) ^ k) := by
  intro t ht
  have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hw_nonneg : 0 ≤ 2 - σ₀ := by linarith
  have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1

  have hmain_nonneg : 0 ≤ g t * t ^ (-(σ₀ + 1)) := by
    exact mul_nonneg (hg_nonneg t ht) (Real.rpow_nonneg (le_of_lt ht_pos) _)

  have hterm_nonneg : ∀ k : ℕ, 0 ≤ antiCoeffProfile g k t * (2 - σ₀) ^ k := by
    intro k
    have hfac_pos : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hpow_log_nonneg : 0 ≤ (Real.log t) ^ k := pow_nonneg hlog_nonneg _
    have hfrac_nonneg : 0 ≤ (Real.log t) ^ k / (k.factorial : ℝ) :=
      div_nonneg hpow_log_nonneg hfac_pos.le
    have hanti_nonneg : 0 ≤ antiCoeffProfile g k t := by
      unfold antiCoeffProfile
      exact mul_nonneg
        (mul_nonneg (hg_nonneg t ht) (Real.rpow_nonneg (le_of_lt ht_pos) _))
        hfrac_nonneg
    exact mul_nonneg hanti_nonneg (pow_nonneg hw_nonneg _)

  have hterm_summable : Summable (fun k : ℕ => antiCoeffProfile g k t * (2 - σ₀) ^ k) := by
    have hsum_base : Summable (fun k : ℕ => (((2 - σ₀) * Real.log t) ^ k / (k.factorial : ℝ))) :=
      Real.summable_pow_div_factorial _
    have hsum_scaled :
        Summable (fun k : ℕ =>
          (g t * t ^ (-(3 : ℝ))) * (((2 - σ₀) * Real.log t) ^ k / (k.factorial : ℝ))) :=
      hsum_base.mul_left (g t * t ^ (-(3 : ℝ)))
    refine hsum_scaled.congr ?_
    intro k
    unfold antiCoeffProfile
    rw [mul_pow]
    ring

  calc
    ENNReal.ofReal ‖g t * t ^ (-(σ₀ + 1))‖
        = ENNReal.ofReal (g t * t ^ (-(σ₀ + 1))) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hmain_nonneg]
    _ = ENNReal.ofReal (∑' k : ℕ, antiCoeffProfile g k t * (2 - σ₀) ^ k) := by
          rw [integrand_eq_tsum_anticoeff g σ₀ t ht_pos]
    _ = ∑' k : ℕ, ENNReal.ofReal (antiCoeffProfile g k t * (2 - σ₀) ^ k) := by
          exact ENNReal.ofReal_tsum_of_nonneg hterm_nonneg hterm_summable

/--
Concrete Tonelli-lintegral majorant for Landau's `σ₀ < 1` branch.

This instantiates the abstract `partial_lintegral_le_tsum_tail_coeffs` theorem
with the explicit anti-coefficient profile.
-/
theorem partial_lintegral_le_tsum_anticoeff_tail
    (g : ℝ → ℝ) (T₀ σ₀ : ℝ)
    (hT₀ : 1 ≤ T₀) (hσ₀_lt1 : σ₀ < 1)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ g t) :
    ∀ N : ℕ,
      ∫⁻ t in Ioc T₀ (T₀ + (N : ℝ)),
        ENNReal.ofReal ‖g t * t ^ (-(σ₀ + 1))‖
        ≤
      ∑' k : ℕ,
        ∫⁻ t in Ioi T₀,
          ENNReal.ofReal (antiCoeffProfile g k t * (2 - σ₀) ^ k) := by
  refine Aristotle.Standalone.LandauSigmaLessThanOneTonelliLIntegral.partial_lintegral_le_tsum_tail_coeffs
    g T₀ σ₀ (fun k t => antiCoeffProfile g k t * (2 - σ₀) ^ k) ?_ ?_
  · intro k
    exact (antiCoeffProfile_measurable g hg_meas k).mul_const ((2 - σ₀) ^ k)
  · intro t ht
    exact le_of_eq (pointwise_norm_eq_tsum_anticoeff_on_tail g T₀ σ₀ hT₀ hσ₀_lt1 hg_nonneg t ht)

/--
Concrete real-integral Tonelli majorant with weighted anti-coefficients.

This is the `intervalIntegral` version of
`partial_lintegral_le_tsum_anticoeff_tail`.
-/
theorem partial_integral_le_tsum_anticoeff_weighted_tail
    (g : ℝ → ℝ) (T₀ σ₀ : ℝ)
    (hT₀ : 1 ≤ T₀) (hσ₀_lt1 : σ₀ < 1)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ g t)
    (hmain_int : ∀ N : ℕ,
      IntegrableOn (fun t : ℝ => ‖g t * t ^ (-(σ₀ + 1))‖) (Ioc T₀ (T₀ + (N : ℝ))))
    (hterm_int : ∀ k : ℕ,
      IntegrableOn (fun t : ℝ => antiCoeffProfile g k t * (2 - σ₀) ^ k) (Ioi T₀))
    (hsum : Summable (fun k : ℕ => ∫ t in Ioi T₀, antiCoeffProfile g k t * (2 - σ₀) ^ k)) :
    ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)),
        ‖g t * t ^ (-(σ₀ + 1))‖
        ≤
      ∑' k : ℕ, ∫ t in Ioi T₀, antiCoeffProfile g k t * (2 - σ₀) ^ k := by
  have hpow_nonneg : 0 ≤ 2 - σ₀ := by linarith
  refine Aristotle.Standalone.LandauSigmaLessThanOneTonelliLIntegral.partial_integral_le_tsum_tail_coeffs
    g T₀ σ₀ (fun k t => antiCoeffProfile g k t * (2 - σ₀) ^ k) ?_ ?_ ?_ hmain_int hterm_int hsum
  · intro k
    exact (antiCoeffProfile_measurable g hg_meas k).mul_const ((2 - σ₀) ^ k)
  · intro k t ht
    exact mul_nonneg
      (antiCoeffProfile_nonneg_on_tail g T₀ hT₀ hg_nonneg k t ht)
      (pow_nonneg hpow_nonneg _)
  · intro t ht
    exact le_of_eq (pointwise_norm_eq_tsum_anticoeff_on_tail g T₀ σ₀ hT₀ hσ₀_lt1 hg_nonneg t ht)

/--
Factorized real-integral coefficient form:
`A_k := ∫_{t>T₀} antiCoeffProfile g k t`, then
`∫_{(T₀,T₀+N]} … ≤ ∑ A_k * (2-σ₀)^k`.
-/
theorem partial_integral_le_tsum_anticoeff_coeffs
    (g : ℝ → ℝ) (T₀ σ₀ : ℝ)
    (hT₀ : 1 ≤ T₀) (hσ₀_lt1 : σ₀ < 1)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ g t)
    (hmain_int : ∀ N : ℕ,
      IntegrableOn (fun t : ℝ => ‖g t * t ^ (-(σ₀ + 1))‖) (Ioc T₀ (T₀ + (N : ℝ))))
    (hcoeff_int : ∀ k : ℕ, IntegrableOn (fun t : ℝ => antiCoeffProfile g k t) (Ioi T₀))
    (hsum_coeff :
      Summable (fun k : ℕ => (∫ t in Ioi T₀, antiCoeffProfile g k t) * (2 - σ₀) ^ k)) :
    ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)),
        ‖g t * t ^ (-(σ₀ + 1))‖
        ≤
      ∑' k : ℕ, (∫ t in Ioi T₀, antiCoeffProfile g k t) * (2 - σ₀) ^ k := by
  have hterm_int : ∀ k : ℕ,
      IntegrableOn (fun t : ℝ => antiCoeffProfile g k t * (2 - σ₀) ^ k) (Ioi T₀) := by
    intro k
    exact (hcoeff_int k).mul_const ((2 - σ₀) ^ k)
  have hsum_term :
      Summable (fun k : ℕ => ∫ t in Ioi T₀, antiCoeffProfile g k t * (2 - σ₀) ^ k) := by
    refine hsum_coeff.congr ?_
    intro k
    simpa using
      (MeasureTheory.integral_mul_const ((2 - σ₀) ^ k)
        (fun t : ℝ => antiCoeffProfile g k t) (μ := volume.restrict (Ioi T₀))).symm
  intro N
  calc
    ∫ t in Ioc T₀ (T₀ + (N : ℝ)),
        ‖g t * t ^ (-(σ₀ + 1))‖
        ≤
      ∑' k : ℕ, ∫ t in Ioi T₀, antiCoeffProfile g k t * (2 - σ₀) ^ k :=
      partial_integral_le_tsum_anticoeff_weighted_tail
        g T₀ σ₀ hT₀ hσ₀_lt1 hg_meas hg_nonneg hmain_int hterm_int hsum_term N
    _ = ∑' k : ℕ, (∫ t in Ioi T₀, antiCoeffProfile g k t) * (2 - σ₀) ^ k := by
      refine tsum_congr ?_
      intro k
      symm
      simpa using
        (MeasureTheory.integral_mul_const ((2 - σ₀) ^ k)
          (fun t : ℝ => antiCoeffProfile g k t) (μ := volume.restrict (Ioi T₀))).symm

/--
Concrete bounded-partial-integrals consequence:

if the factorized anti-coefficients are dominated by Cauchy coefficients of a
power series with positive radius control, then all partial integrals are
uniformly bounded.
-/
theorem partial_integrals_bounded_of_anticoeff_cauchy_domination
    (g : ℝ → ℝ) (T₀ σ₀ : ℝ)
    (hT₀ : 1 ≤ T₀) (hσ₀_lt1 : σ₀ < 1)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ g t)
    (hmain_int : ∀ N : ℕ,
      IntegrableOn (fun t : ℝ => ‖g t * t ^ (-(σ₀ + 1))‖) (Ioc T₀ (T₀ + (N : ℝ))))
    (hcoeff_int : ∀ k : ℕ, IntegrableOn (fun t : ℝ => antiCoeffProfile g k t) (Ioi T₀))
    (p : FormalMultilinearSeries ℂ ℂ ℂ) {r : NNReal}
    (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (hw_lt : 2 - σ₀ < (r : ℝ))
    (hcoeff_dom : ∀ k : ℕ,
      (∫ t in Ioi T₀, antiCoeffProfile g k t) ≤ coeffAtOne p k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖ ≤ M := by
  let w : ℝ := 2 - σ₀
  have hw_nonneg : 0 ≤ w := by
    dsimp [w]
    linarith
  have hA_nonneg : ∀ k : ℕ, 0 ≤ ∫ t in Ioi T₀, antiCoeffProfile g k t := by
    intro k
    have hnonneg_ae :
        0 ≤ᵐ[volume.restrict (Ioi T₀)] fun t : ℝ => antiCoeffProfile g k t := by
      refine (ae_restrict_mem measurableSet_Ioi).mono ?_
      intro t ht
      exact antiCoeffProfile_nonneg_on_tail g T₀ hT₀ hg_nonneg k t ht
    exact MeasureTheory.integral_nonneg_of_ae hnonneg_ae

  have hsum_coeffAtOne :
      Summable (fun k : ℕ => coeffAtOne p k * w ^ k) := by
    exact summable_coeff_eval_one_mul_pow_of_lt_radius p hr0 hr w hw_nonneg (by simpa [w] using hw_lt)

  have hterm_nonneg :
      ∀ k : ℕ, 0 ≤ (∫ t in Ioi T₀, antiCoeffProfile g k t) * w ^ k := by
    intro k
    exact mul_nonneg (hA_nonneg k) (pow_nonneg hw_nonneg _)

  have hterm_le :
      ∀ k : ℕ,
        (∫ t in Ioi T₀, antiCoeffProfile g k t) * w ^ k
          ≤ coeffAtOne p k * w ^ k := by
    intro k
    exact mul_le_mul_of_nonneg_right (hcoeff_dom k) (pow_nonneg hw_nonneg _)

  have hsum_coeff :
      Summable (fun k : ℕ => (∫ t in Ioi T₀, antiCoeffProfile g k t) * w ^ k) :=
    Summable.of_nonneg_of_le hterm_nonneg hterm_le hsum_coeffAtOne

  have hpartial :
      ∀ N : ℕ,
        ∫ t in Ioc T₀ (T₀ + (N : ℝ)),
          ‖g t * t ^ (-(σ₀ + 1))‖
          ≤
        ∑' k : ℕ, (∫ t in Ioi T₀, antiCoeffProfile g k t) * w ^ k := by
    intro N
    simpa [w] using
      partial_integral_le_tsum_anticoeff_coeffs
        g T₀ σ₀ hT₀ hσ₀_lt1 hg_meas hg_nonneg hmain_int hcoeff_int hsum_coeff N

  refine ⟨∑' k : ℕ, (∫ t in Ioi T₀, antiCoeffProfile g k t) * w ^ k, ?_, ?_⟩
  · exact tsum_nonneg hterm_nonneg
  · intro N
    exact hpartial N

/--
Same bound as `partial_lintegral_le_tsum_anticoeff_tail`, rewritten into explicit
coefficient form `A_k * (2 - σ₀)^k` with
`A_k = ∫⁻_{t>T₀} ofReal (antiCoeffProfile g k t)`.
-/
theorem partial_lintegral_le_tsum_anticoeff_coeffs
    (g : ℝ → ℝ) (T₀ σ₀ : ℝ)
    (hT₀ : 1 ≤ T₀) (hσ₀_lt1 : σ₀ < 1)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ g t) :
    ∀ N : ℕ,
      ∫⁻ t in Ioc T₀ (T₀ + (N : ℝ)),
        ENNReal.ofReal ‖g t * t ^ (-(σ₀ + 1))‖
        ≤
      ∑' k : ℕ,
        (∫⁻ t in Ioi T₀, ENNReal.ofReal (antiCoeffProfile g k t)) *
          ENNReal.ofReal ((2 - σ₀) ^ k) := by
  have hpow_nonneg : 0 ≤ 2 - σ₀ := by linarith
  have hbase := partial_lintegral_le_tsum_anticoeff_tail
    g T₀ σ₀ hT₀ hσ₀_lt1 hg_meas hg_nonneg
  intro N
  refine (hbase N).trans ?_
  refine le_of_eq ?_
  refine tsum_congr ?_
  intro k
  calc
    ∫⁻ t in Ioi T₀, ENNReal.ofReal (antiCoeffProfile g k t * (2 - σ₀) ^ k)
      = ∫⁻ t in Ioi T₀,
          (ENNReal.ofReal (antiCoeffProfile g k t)) * ENNReal.ofReal ((2 - σ₀) ^ k) := by
            refine setLIntegral_congr_fun measurableSet_Ioi ?_
            intro t ht
            have hanti_nonneg : 0 ≤ antiCoeffProfile g k t :=
              antiCoeffProfile_nonneg_on_tail g T₀ hT₀ hg_nonneg k t ht
            simpa using (ENNReal.ofReal_mul (q := (2 - σ₀) ^ k) hanti_nonneg)
    _ = (∫⁻ t in Ioi T₀, ENNReal.ofReal (antiCoeffProfile g k t)) *
          ENNReal.ofReal ((2 - σ₀) ^ k) := by
            rw [MeasureTheory.lintegral_mul_const _]
            exact (Measurable.ennreal_ofReal (antiCoeffProfile_measurable g hg_meas k))

end Aristotle.Standalone.LandauSigmaLessThanOneTonelliConcrete
