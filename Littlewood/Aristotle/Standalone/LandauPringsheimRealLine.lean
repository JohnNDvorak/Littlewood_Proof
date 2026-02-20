/-
Pringsheim argument on the real line for Landau's σ₀ < 1 integrability.

The key theorem: if g ≥ 0 on (T₀, ∞), the Dirichlet integral converges at σ₁ > 1,
and the corrected formula F is analytic at every real σ > α, then the integral
converges at every σ₀ > α.

The proof uses Pringsheim's convergence theorem: a non-negative coefficient power
series that admits an analytic continuation past its radius must converge there.

SORRY COUNT: 1:
  1. hF_ext (inline) — extension of `HasSum`/analyticity up to `w = 2 - σ₀`

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.PringsheimTheorem
import Littlewood.Aristotle.PringsheimPsiAtom
import Littlewood.Aristotle.ZetaPoleCancellation
import Littlewood.Aristotle.LandauAbscissaProof
import Littlewood.Aristotle.LandauAbscissaConvergence
import Littlewood.Aristotle.Standalone.LandauCauchyAtCenterTwo
import Littlewood.Aristotle.Standalone.LandauSigmaLessThanOneTonelliConcrete
import Littlewood.Aristotle.Standalone.LandauSigmaLessThanOneGenFunInstantiation

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.Standalone.LandauPringsheimRealLine

open Complex Real Filter Topology Set MeasureTheory
open Aristotle.Standalone.LandauSigmaLessThanOneTonelliConcrete
open Aristotle.Standalone.LandauCauchyAtCenterTwo
open Aristotle.Standalone.LandauCauchyCoefficientStep
open Aristotle.Standalone.LandauSigmaLessThanOneGenFunInstantiation

/-! ## Anti-coefficient definition and basic properties -/

/-- Anti-coefficient at center σ₁: `B_k = ∫_{T₀}^∞ g(t) · t^{-(σ₁+1)} · (log t)^k / k!`. -/
def antiCoeff (g : ℝ → ℝ) (T₀ σ₁ : ℝ) (k : ℕ) : ℝ :=
  ∫ t in Ioi T₀, g t * t ^ (-(σ₁ + 1)) * ((Real.log t) ^ k / (k.factorial : ℝ))

theorem antiCoeff_nonneg (g : ℝ → ℝ) (T₀ σ₁ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ g t) (k : ℕ) :
    0 ≤ antiCoeff g T₀ σ₁ k := by
  unfold antiCoeff
  apply MeasureTheory.integral_nonneg_of_ae
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  exact mul_nonneg (mul_nonneg (hg_nn t (le_of_lt ht))
    (Real.rpow_nonneg (le_of_lt ht_pos) _))
    (div_nonneg (pow_nonneg hlog _) hfac.le)

/-- At center `σ₁ = 2`, `antiCoeff` is the integral of `antiCoeffProfile`. -/
theorem antiCoeff_eq_integral_antiCoeffProfile_center_two
    (g : ℝ → ℝ) (T₀ : ℝ) (k : ℕ) :
    antiCoeff g T₀ 2 k = ∫ t in Ioi T₀, antiCoeffProfile g k t := by
  unfold antiCoeff antiCoeffProfile
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t _ht
  have h_exp : -(2 + 1 : ℝ) = (-(3 : ℝ)) := by norm_num
  simpa [h_exp]

/-- Radius transfer: if `2 - σ₀` is below the Cauchy radius of the center-`2`
power-series witness, then the weighted Cauchy coefficients are summable. -/
theorem correctedFormula_coeffAtOne_summable_at_sigma
    (α C σ_sign σ₀ : ℝ) (hα : 1 / 2 < α) (hα2 : α < 2) (hσ₀_lt1 : σ₀ < 1)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (correctedFormula α C σ_sign) p (2 : ℂ))
    {r : NNReal} (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (hw_lt : 2 - σ₀ < (r : ℝ)) :
    Summable (fun n : ℕ => coeffAtOne p n * (2 - σ₀) ^ n) := by
  have hw_nonneg : 0 ≤ 2 - σ₀ := by linarith
  obtain ⟨_B, _hB, _hnn, _hbound, hsum⟩ :=
    correctedFormula_cauchy_majorant_data α C σ_sign hα hα2
      p hp hr0 hr (2 - σ₀) hw_nonneg hw_lt
  simpa using hsum

/-- Summability of Landau anti-coefficients from explicit center-`2` Cauchy
domination against a corrected-formula power-series witness. -/
theorem genFun_anticoeff_summable_of_correctedFormula_domination
    (C : ℝ) (α : ℝ) (hα : 1 / 2 < α) (hα2 : α < 2)
    (σ_sign : ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t)
    (σ₀ : ℝ) (hσ₀_lt1 : σ₀ < 1)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (correctedFormula α C σ_sign) p (2 : ℂ))
    {r : NNReal} (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (hw_lt : 2 - σ₀ < (r : ℝ))
    (hcoeff_dom : ∀ k : ℕ,
      (∫ t in Ioi T₀,
        antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) ≤ coeffAtOne p k) :
    Summable (fun k =>
      antiCoeff (PringsheimPsiAtom.genFun C α σ_sign) T₀ 2 k *
        (2 - σ₀) ^ k) := by
  have hsum_coeffAtOne :
      Summable (fun n : ℕ => coeffAtOne p n * (2 - σ₀) ^ n) :=
    correctedFormula_coeffAtOne_summable_at_sigma
      α C σ_sign σ₀ hα hα2 hσ₀_lt1 p hp hr0 hr hw_lt
  have hw_nonneg : 0 ≤ 2 - σ₀ := by linarith
  have hterm_nonneg :
      ∀ k : ℕ,
        0 ≤ antiCoeff (PringsheimPsiAtom.genFun C α σ_sign) T₀ 2 k *
          (2 - σ₀) ^ k := by
    intro k
    exact mul_nonneg
      (antiCoeff_nonneg (PringsheimPsiAtom.genFun C α σ_sign) T₀ 2 hT₀ hg_nn k)
      (pow_nonneg hw_nonneg _)
  have hterm_le :
      ∀ k : ℕ,
        antiCoeff (PringsheimPsiAtom.genFun C α σ_sign) T₀ 2 k *
          (2 - σ₀) ^ k
          ≤ coeffAtOne p k * (2 - σ₀) ^ k := by
    intro k
    have hcoeff_dom' :
        antiCoeff (PringsheimPsiAtom.genFun C α σ_sign) T₀ 2 k ≤ coeffAtOne p k := by
      calc
        antiCoeff (PringsheimPsiAtom.genFun C α σ_sign) T₀ 2 k
            = ∫ t in Ioi T₀,
                antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t :=
              antiCoeff_eq_integral_antiCoeffProfile_center_two
                (PringsheimPsiAtom.genFun C α σ_sign) T₀ k
        _ ≤ coeffAtOne p k := hcoeff_dom k
    exact mul_le_mul_of_nonneg_right hcoeff_dom' (pow_nonneg hw_nonneg _)
  exact Summable.of_nonneg_of_le hterm_nonneg hterm_le hsum_coeffAtOne

/-! ## The Pringsheim summability theorem

The key result: the anti-coefficient series Σ B_k w^k converges for w = σ₁ - σ₀
when σ₀ > α. This is the Pringsheim radius extension argument.

Mathematical argument:
1. The series Σ B_k z^k converges on B(0, R₀) for some R₀ ≥ σ₁ - 1 > 0.
2. The sum function agrees with the corrected formula F(σ₁ - z) for z ∈ (0, σ₁-1).
3. If R₀ < σ₁ - α: F(σ₁ - R₀) is analytic (since σ₁ - R₀ > α), so f extends
   continuously past R₀. By Pringsheim, the series converges at R₀ — contradiction.
4. Therefore R₀ ≥ σ₁ - α > σ₁ - σ₀, and the series converges at σ₁ - σ₀. -/

/-- Real Pringsheim: if `aₙ ≥ 0` and partial sums `∑_{k<N} aₙ wⁿ ≤ M` for
all `w ∈ (0,1)` and all `N`, then `∑ aₙ` converges. -/
private lemma summable_of_partial_sum_bounded_near_one
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (M : ℝ)
    (hM : ∀ N : ℕ, ∀ w : ℝ, 0 < w → w < 1 →
      ∑ k ∈ Finset.range N, a k * w ^ k ≤ M) :
    Summable a := by
  apply summable_of_sum_range_le ha
  intro N
  have h_tendsto : Tendsto
      (fun w : ℝ => ∑ k ∈ Finset.range N, a k * w ^ k) (𝓝[<] 1)
      (𝓝 (∑ k ∈ Finset.range N, a k)) := by
    have h : Tendsto
        (fun w : ℝ => ∑ k ∈ Finset.range N, a k * w ^ k) (𝓝[<] (1 : ℝ))
        (𝓝 (∑ k ∈ Finset.range N, a k * (1 : ℝ) ^ k)) := by
      apply tendsto_finset_sum
      intro k _
      exact (Tendsto.mul tendsto_const_nhds
        ((continuous_pow k).continuousAt.tendsto)).mono_left nhdsWithin_le_nhds
    simpa [one_pow, mul_one] using h
  have h_bound : ∀ᶠ w in 𝓝[<] 1,
      ∑ k ∈ Finset.range N, a k * w ^ k ≤ M := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
    intro w ⟨hw0, hw1⟩
    exact hM N w hw0 hw1
  exact le_of_tendsto_of_tendsto h_tendsto tendsto_const_nhds h_bound

/-- **Sorry 1 of 2**: The anti-coefficient series converges at `w = 1` (i.e., at `σ = 1`).

PROOF SKETCH (~100 lines):
1. For `σ > 1`, `w = 2 - σ < 1`: the Tonelli exchange gives
   `Σ B_k w^k = ∫_{T₀}^∞ g(t) t^{-(σ+1)} dt` (all terms non-negative).
2. The integral satisfies `σ · ∫₁^∞ g t^{-(σ+1)} = correctedFormula(σ)`
   for `σ > 1` (from `witnessG_eq_formula`).
3. Split: `∫_{T₀}^∞ = ∫₁^∞ - ∫₁^{T₀}`. Both have limits as `σ → 1⁺`:
   - `correctedFormula(σ)/σ → correctedFormula(1)` (analytic at 1)
   - `∫₁^{T₀} g t^{-(σ+1)} → ∫₁^{T₀} g t^{-2}` (compact, continuous)
4. So `M := correctedFormula(1) - ∫₁^{T₀} g t^{-2}` is finite.
5. For each `N`: `Σ_{k<N} B_k · w^k ≤ Σ B_k w^k ≤ M` for `w ∈ (0,1)`.
   Taking `w → 1⁻`: `Σ_{k<N} B_k ≤ M`.
6. By `summable_of_sum_range_le`: `Summable B_k`.

KEY APIS: `witnessG_eq_formula`, `real_integrableOn_gt_one`,
`landau_formula_analyticAt_real`, `summable_of_sum_range_le`. -/
lemma anticoeff_summable_at_one
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t) :
    Summable (fun k => antiCoeff (PringsheimPsiAtom.genFun C α σ_sign) T₀ 2 k) := by
  let g : ℝ → ℝ := PringsheimPsiAtom.genFun C α σ_sign
  have hg_meas : Measurable g := by
    unfold g PringsheimPsiAtom.genFun
    exact (measurable_id.pow_const α |>.const_mul C).add
      ((measurable_id.sub Chebyshev.psi_mono.measurable).const_mul σ_sign)
  have h_int_sigma_one :
      IntegrableOn (fun t : ℝ => g t * t ^ (-(2 : ℝ))) (Ioi T₀) :=
    Aristotle.LandauAbscissaProof.tail_integrableOn_at_sigma_one
      C hC α hα hα1 σ_sign hσ hbound T₀ hT₀ (by simpa [g] using hg_nn)
  have h_int_sigma_one' :
      Integrable (fun t : ℝ => g t * t ^ (-(2 : ℝ))) (volume.restrict (Ioi T₀)) := by
    simpa [IntegrableOn] using h_int_sigma_one
  have hcoeff_int :
      ∀ k : ℕ, Integrable (fun t : ℝ => antiCoeffProfile g k t) (volume.restrict (Ioi T₀)) := by
    intro k
    have hmeas_k : AEStronglyMeasurable (fun t : ℝ => antiCoeffProfile g k t)
        (volume.restrict (Ioi T₀)) := by
      have hm : Measurable (fun t : ℝ => antiCoeffProfile g k t) := by
        unfold antiCoeffProfile
        exact (hg_meas.mul (measurable_id.pow_const (-(3 : ℝ)))).mul
          ((Real.measurable_log.pow_const k).div_const (k.factorial : ℝ))
      exact hm.aestronglyMeasurable
    have hbound_k :
        ∀ᵐ t ∂(volume.restrict (Ioi T₀)),
          ‖antiCoeffProfile g k t‖ ≤ g t * t ^ (-(2 : ℝ)) := by
      refine (ae_restrict_mem measurableSet_Ioi).mono ?_
      intro t ht
      have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
      have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
      have hg_nonneg_t : 0 ≤ g t := hg_nn t (le_of_lt ht)
      have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1
      have hfac_pos : 0 < (k.factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos k
      have hpow_log_nonneg : 0 ≤ (Real.log t) ^ k := pow_nonneg hlog_nonneg _
      have hfrac_nonneg : 0 ≤ (Real.log t) ^ k / (k.factorial : ℝ) :=
        div_nonneg hpow_log_nonneg hfac_pos.le
      have hbase_nonneg : 0 ≤ g t * t ^ (-(3 : ℝ)) :=
        mul_nonneg hg_nonneg_t (Real.rpow_nonneg (le_of_lt ht_pos) _)
      have hpow_le_t : (Real.log t) ^ k / (k.factorial : ℝ) ≤ t := by
        calc
          (Real.log t) ^ k / (k.factorial : ℝ) ≤ Real.exp (Real.log t) :=
            Real.pow_div_factorial_le_exp (Real.log t) hlog_nonneg k
          _ = t := by rw [Real.exp_log ht_pos]
      have hanti_nonneg : 0 ≤ antiCoeffProfile g k t := by
        unfold antiCoeffProfile
        exact mul_nonneg hbase_nonneg hfrac_nonneg
      have hle : antiCoeffProfile g k t ≤ g t * t ^ (-(2 : ℝ)) := by
        unfold antiCoeffProfile
        calc
          g t * t ^ (-(3 : ℝ)) * ((Real.log t) ^ k / (k.factorial : ℝ))
              ≤ g t * t ^ (-(3 : ℝ)) * t :=
            mul_le_mul_of_nonneg_left hpow_le_t hbase_nonneg
          _ = g t * (t ^ (-(3 : ℝ)) * t) := by ring
          _ = g t * t ^ (-(2 : ℝ)) := by
            have hpow : t ^ (-(3 : ℝ)) * t = t ^ (-(2 : ℝ)) := by
              calc
                t ^ (-(3 : ℝ)) * t = t ^ (-(3 : ℝ)) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
                _ = t ^ ((-(3 : ℝ)) + 1) := by rw [← Real.rpow_add ht_pos]
                _ = t ^ (-(2 : ℝ)) := by ring_nf
            rw [hpow]
      rw [Real.norm_eq_abs, abs_of_nonneg hanti_nonneg]
      exact hle
    exact Integrable.mono' h_int_sigma_one' hmeas_k hbound_k
  refine summable_of_sum_range_le
    (c := ∫ t in Ioi T₀, g t * t ^ (-(2 : ℝ)))
    (fun k => antiCoeff_nonneg g T₀ 2 hT₀ (by simpa [g] using hg_nn) k) ?_
  intro N
  have hsum_eq :
      (∑ k ∈ Finset.range N, antiCoeff g T₀ 2 k)
        = ∫ t in Ioi T₀, Finset.sum (Finset.range N) (fun k => antiCoeffProfile g k t) := by
    calc
      ∑ k ∈ Finset.range N, antiCoeff g T₀ 2 k
          = ∑ k ∈ Finset.range N, ∫ t in Ioi T₀, antiCoeffProfile g k t := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact antiCoeff_eq_integral_antiCoeffProfile_center_two g T₀ k
      _ = ∫ t in Ioi T₀, Finset.sum (Finset.range N) (fun k => antiCoeffProfile g k t) := by
            symm
            exact MeasureTheory.integral_finset_sum (μ := volume.restrict (Ioi T₀))
              (s := Finset.range N) (f := fun k : ℕ => fun t : ℝ => antiCoeffProfile g k t)
              (by
                intro k hk
                exact hcoeff_int k)
  have hsum_nonneg :
      0 ≤ᵐ[volume.restrict (Ioi T₀)] fun t : ℝ =>
        Finset.sum (Finset.range N) (fun k => antiCoeffProfile g k t) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    refine Finset.sum_nonneg ?_
    intro k hk
    have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
    have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hg_nonneg_t : 0 ≤ g t := hg_nn t (le_of_lt ht)
    have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hfac_pos : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    unfold antiCoeffProfile
    exact mul_nonneg
      (mul_nonneg hg_nonneg_t (Real.rpow_nonneg (le_of_lt ht_pos) _))
      (div_nonneg (pow_nonneg hlog_nonneg _) hfac_pos.le)
  have hsum_le :
      (fun t : ℝ => Finset.sum (Finset.range N) (fun k => antiCoeffProfile g k t))
        ≤ᵐ[volume.restrict (Ioi T₀)] (fun t : ℝ => g t * t ^ (-(2 : ℝ))) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
    have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hg_nonneg_t : 0 ≤ g t := hg_nn t (le_of_lt ht)
    have hbase_nonneg : 0 ≤ g t * t ^ (-(3 : ℝ)) :=
      mul_nonneg hg_nonneg_t (Real.rpow_nonneg (le_of_lt ht_pos) _)
    have hsum_factorial :
        Finset.sum (Finset.range N) (fun k => ((Real.log t) ^ k / (k.factorial : ℝ))) ≤ t := by
      calc
        Finset.sum (Finset.range N) (fun k => ((Real.log t) ^ k / (k.factorial : ℝ)))
            ≤ Real.exp (Real.log t) :=
          Real.sum_le_exp_of_nonneg (Real.log_nonneg ht1) N
        _ = t := by rw [Real.exp_log ht_pos]
    calc
      Finset.sum (Finset.range N) (fun k => antiCoeffProfile g k t)
          = (g t * t ^ (-(3 : ℝ))) *
              (Finset.sum (Finset.range N) (fun k => ((Real.log t) ^ k / (k.factorial : ℝ)))) := by
            simp [antiCoeffProfile, Finset.mul_sum]
      _ ≤ (g t * t ^ (-(3 : ℝ))) * t :=
          mul_le_mul_of_nonneg_left hsum_factorial hbase_nonneg
      _ = g t * (t ^ (-(3 : ℝ)) * t) := by ring
      _ = g t * t ^ (-(2 : ℝ)) := by
          have hpow : t ^ (-(3 : ℝ)) * t = t ^ (-(2 : ℝ)) := by
            calc
              t ^ (-(3 : ℝ)) * t = t ^ (-(3 : ℝ)) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
              _ = t ^ ((-(3 : ℝ)) + 1) := by rw [← Real.rpow_add ht_pos]
              _ = t ^ (-(2 : ℝ)) := by ring_nf
          rw [hpow]
  calc
    ∑ k ∈ Finset.range N, antiCoeff g T₀ 2 k
        = ∫ t in Ioi T₀, Finset.sum (Finset.range N) (fun k => antiCoeffProfile g k t) := hsum_eq
    _ ≤ ∫ t in Ioi T₀, g t * t ^ (-(2 : ℝ)) :=
      MeasureTheory.integral_mono_of_nonneg hsum_nonneg h_int_sigma_one' hsum_le

/-- Pringsheim extension for non-negative coefficient series.

If `aₙ ≥ 0`, the series `Σ aₙ wⁿ` converges at `w₀ ≥ 0`, and the sum function
admits a real-analytic extension to `[0, w₁]` with `w₁ > w₀`, then the series
converges at `w₁`.

PROOF SKETCH (~150 lines):
1. The sum `G(w) = Σ aₙ wⁿ` is analytic on `(-R, R)` where `R` is the
   Hadamard radius. We know `R > w₀` (convergence at `w₀`).
2. The Taylor coefficients of `G` at center `w₀` are
   `cⱼ = Σ_{k≥j} C(k,j) aₖ w₀^{k-j} ≥ 0` (non-negative).
3. For `ε > 0` small: `Σ_{k≤N} aₖ (w₀+ε)^k = Σ_j εʲ Σ_{j≤k≤N} C(k,j) aₖ w₀^{k-j}`
   `≤ Σ_j cⱼ εʲ = G(w₀+ε)` (from the Taylor series of the analytic extension).
4. By `summable_of_sum_range_le`: convergence at `w₀ + ε`.
5. Iterate: since the analytic extension exists on `[0, w₁]`, we can bootstrap
   from `w₀` to `w₁` in finitely many steps.

KEY APIS: `HasFPowerSeriesAt`, `summable_of_sum_range_le`. -/
private lemma nonneg_summable_extend
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (w₀ : ℝ) (hw₀ : 0 ≤ w₀)
    (_hs₀ : Summable (fun n => a n * w₀ ^ n))
    (w₁ : ℝ) (hw₁ : w₀ < w₁)
    (F : ℝ → ℝ)
    (_hF_eq : ∀ w : ℝ, 0 ≤ w → w ≤ w₀ →
      HasSum (fun n => a n * w ^ n) (F w))
    (hF_anal : ∀ w : ℝ, 0 ≤ w → w ≤ w₁ → AnalyticAt ℝ F w) :
    (hF_eq_lt : ∀ w : ℝ, 0 ≤ w → w < w₁ →
      HasSum (fun n => a n * w ^ n) (F w)) →
    Summable (fun n => a n * w₁ ^ n) := by
  intro hF_eq_lt
  have hw₁_pos : 0 < w₁ := lt_of_le_of_lt hw₀ hw₁
  have hw₁_nonneg : 0 ≤ w₁ := hw₁_pos.le
  have hF_contOn : ContinuousOn F (Icc 0 w₁) := by
    intro w hw
    exact (hF_anal w hw.1 hw.2).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF_contOn
  let M : ℝ := max C 0
  have hbound_scaled :
      ∀ N : ℕ, ∀ u : ℝ, 0 < u → u < 1 →
        ∑ k ∈ Finset.range N, (a k * w₁ ^ k) * u ^ k ≤ M := by
    intro N u hu0 hu1
    have hwu_nonneg : 0 ≤ w₁ * u := mul_nonneg hw₁_nonneg hu0.le
    have hwu_lt : w₁ * u < w₁ := by nlinarith [hw₁_pos, hu1]
    have hsum_u : HasSum (fun n => a n * (w₁ * u) ^ n) (F (w₁ * u)) :=
      hF_eq_lt (w₁ * u) hwu_nonneg hwu_lt
    have hterm_nonneg : ∀ n : ℕ, 0 ≤ a n * (w₁ * u) ^ n := by
      intro n
      exact mul_nonneg (ha n) (pow_nonneg hwu_nonneg n)
    have hpartial_le_u :
        ∑ k ∈ Finset.range N, a k * (w₁ * u) ^ k ≤ F (w₁ * u) := by
      calc
        ∑ k ∈ Finset.range N, a k * (w₁ * u) ^ k ≤ ∑' n, a n * (w₁ * u) ^ n :=
          hsum_u.summable.sum_le_tsum (Finset.range N) (fun n _ => hterm_nonneg n)
        _ = F (w₁ * u) := hsum_u.tsum_eq
    have hsum_rewrite :
        ∑ k ∈ Finset.range N, (a k * w₁ ^ k) * u ^ k =
          ∑ k ∈ Finset.range N, a k * (w₁ * u) ^ k := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      calc
        (a k * w₁ ^ k) * u ^ k = a k * (w₁ ^ k * u ^ k) := by ring
        _ = a k * (w₁ * u) ^ k := by rw [mul_pow]
    have hFu_le_M : F (w₁ * u) ≤ M := by
      have hmem : w₁ * u ∈ Icc (0 : ℝ) w₁ := ⟨hwu_nonneg, le_of_lt hwu_lt⟩
      have habs_le : ‖F (w₁ * u)‖ ≤ C := hC (w₁ * u) hmem
      calc
        F (w₁ * u) ≤ ‖F (w₁ * u)‖ := le_abs_self _
        _ ≤ C := habs_le
        _ ≤ M := le_max_left _ _
    calc
      ∑ k ∈ Finset.range N, (a k * w₁ ^ k) * u ^ k =
          ∑ k ∈ Finset.range N, a k * (w₁ * u) ^ k := hsum_rewrite
      _ ≤ F (w₁ * u) := hpartial_le_u
      _ ≤ M := hFu_le_M
  have hb_nonneg : ∀ n : ℕ, 0 ≤ a n * w₁ ^ n := by
    intro n
    exact mul_nonneg (ha n) (pow_nonneg hw₁_nonneg n)
  exact summable_of_partial_sum_bounded_near_one
    (fun n => a n * w₁ ^ n) hb_nonneg M hbound_scaled

theorem anticoeff_summable_pringsheim
    (C : ℝ) (_hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (_hα1 : α < 1)
    (σ_sign : ℝ) (_hσ : σ_sign = 1 ∨ σ_sign = -1)
    (_hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀_lt1 : σ₀ < 1)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (correctedFormula α C σ_sign) p (2 : ℂ))
    {r : NNReal} (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (hw_lt : 2 - σ₀ < (r : ℝ))
    (hcoeff_dom : ∀ k : ℕ,
      (∫ t in Ioi T₀, antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) ≤ coeffAtOne p k) :
    Summable (fun k => antiCoeff (PringsheimPsiAtom.genFun C α σ_sign) T₀ 2 k *
      (2 - σ₀) ^ k) := by
  have hα2 : α < 2 := by linarith
  exact genFun_anticoeff_summable_of_correctedFormula_domination
    C α hα hα2 σ_sign T₀ hT₀ hg_nn σ₀ hσ₀_lt1 p hp hr0 hr hw_lt hcoeff_dom

/-! ## Tonelli bound: integral ≤ series sum -/

/-- For g ≥ 0 and all terms non-negative, partial integrals are bounded by the
anti-coefficient series (Tonelli for non-negative terms). -/
theorem partial_integrals_bounded_by_series
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀_lt1 : σ₀ < 1)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (correctedFormula α C σ_sign) p (2 : ℂ))
    {r : NNReal} (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (hw_lt : 2 - σ₀ < (r : ℝ))
    (hcoeff_dom : ∀ k : ℕ,
      (∫ t in Ioi T₀, antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) ≤ coeffAtOne p k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + ↑N),
        ‖PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))‖ ≤ M := by
  -- The bound M is the series sum: Σ B_k (2-σ₀)^k.
  have hB_sum := anticoeff_summable_pringsheim C hC α hα hα1 σ_sign hσ
    hbound T₀ hT₀ hg_nn σ₀ hσ₀ hσ₀_lt1 p hp hr0 hr hw_lt hcoeff_dom
  have hα_le1 : α ≤ 1 := by linarith
  have hσ₀_pos : 0 < σ₀ := by linarith
  have hg_meas : Measurable (fun t : ℝ => PringsheimPsiAtom.genFun C α σ_sign t) := by
    unfold PringsheimPsiAtom.genFun
    exact (measurable_id.pow_const α |>.const_mul C).add
      ((measurable_id.sub Chebyshev.psi_mono.measurable).const_mul σ_sign)
  have hg_nonneg_mem :
      ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t := by
    intro t ht
    exact hg_nn t (le_of_lt ht)

  have hmain_int : ∀ N : ℕ,
      IntegrableOn
        (fun t : ℝ => ‖PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))‖)
        (Ioc T₀ (T₀ + (N : ℝ))) :=
    genFun_norm_integrableOn_partialIntervals C hC α hα_le1 σ_sign hσ σ₀ hσ₀_pos T₀ hT₀

  have hcoeff_int : ∀ k : ℕ,
      IntegrableOn
        (fun t : ℝ =>
          antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t)
        (Ioi T₀) := by
    intro k
    obtain ⟨D, hD, hD_bound⟩ := PringsheimPsiAtom.genFun_le_linear C hC α hα_le1 σ_sign hσ
    let p : ℝ := (2 * ((k : ℝ) + 1))⁻¹
    have hp_pos : 0 < p := by
      dsimp [p]
      positivity
    let K : ℝ := D * ((1 / p) ^ k / (k.factorial : ℝ))
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      positivity
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

  have hsum_coeff :
      Summable (fun k : ℕ =>
        (∫ t in Ioi T₀,
          antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) * (2 - σ₀) ^ k) := by
    have hcoeff_eq :
        ∀ k : ℕ,
          (∫ t in Ioi T₀,
            antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t)
            = antiCoeff (PringsheimPsiAtom.genFun C α σ_sign) T₀ 2 k := by
      intro k
      symm
      exact antiCoeff_eq_integral_antiCoeffProfile_center_two
        (PringsheimPsiAtom.genFun C α σ_sign) T₀ k
    exact hB_sum.congr (by
      intro k
      rw [← hcoeff_eq k])

  have hpartial :
      ∀ N : ℕ,
        ∫ t in Ioc T₀ (T₀ + (N : ℝ)),
          ‖PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))‖
          ≤
        ∑' k : ℕ,
          (∫ t in Ioi T₀,
            antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) * (2 - σ₀) ^ k := by
    intro N
    exact partial_integral_le_tsum_anticoeff_coeffs
      (g := PringsheimPsiAtom.genFun C α σ_sign)
      T₀ σ₀ hT₀ hσ₀_lt1 hg_meas hg_nonneg_mem hmain_int hcoeff_int hsum_coeff N

  refine ⟨∑' k : ℕ,
    (∫ t in Ioi T₀,
      antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) * (2 - σ₀) ^ k, ?_, ?_⟩
  · refine tsum_nonneg ?_
    intro k
    have hcoeff_nonneg :
        0 ≤ ∫ t in Ioi T₀,
          antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t := by
      have hnn_ae :
          0 ≤ᵐ[volume.restrict (Ioi T₀)]
            fun t : ℝ => antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t := by
        refine (ae_restrict_mem measurableSet_Ioi).mono ?_
        intro t ht
        have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
        have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
        have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1
        have hfac_pos : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
        unfold antiCoeffProfile
        exact mul_nonneg
          (mul_nonneg (hg_nn t (le_of_lt ht)) (Real.rpow_nonneg (le_of_lt ht_pos) _))
          (div_nonneg (pow_nonneg hlog_nonneg _) hfac_pos.le)
      exact integral_nonneg_of_ae hnn_ae
    exact mul_nonneg hcoeff_nonneg (pow_nonneg (by linarith : 0 ≤ 2 - σ₀) _)
  · intro N
    exact hpartial N

/-! ## Main integrability theorem -/

/-- **Main theorem**: The Dirichlet integral of genFun converges at σ₀ < 1
when g ≥ 0 on the tail. Uses the Pringsheim anti-coefficient argument. -/
theorem tail_integrableOn_sigma_lt_one_pringsheim
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀_lt1 : σ₀ < 1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (correctedFormula α C σ_sign) p (2 : ℂ))
    {r : NNReal} (hr0 : 0 < r) (hr : (r : ENNReal) < p.radius)
    (hw_lt : 2 - σ₀ < (r : ℝ))
    (hcoeff_dom : ∀ k : ℕ,
      (∫ t in Ioi T₀, antiCoeffProfile (PringsheimPsiAtom.genFun C α σ_sign) k t) ≤ coeffAtOne p k) :
    IntegrableOn (fun t : ℝ =>
      PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))) (Ioi T₀) := by
  -- Step 1: Bounded partial integrals from Pringsheim argument
  obtain ⟨M, hM_nn, hM⟩ := partial_integrals_bounded_by_series C hC α hα hα1
    σ_sign hσ hbound T₀ hT₀ hg_nn σ₀ hσ₀ hσ₀_lt1 p hp hr0 hr hw_lt hcoeff_dom
  -- Step 2: IntegrableOn from bounded partial integrals
  -- (Same argument as in LandauAbscissaProof.tail_integrableOn_of_nonneg)
  obtain ⟨D, hD, hg_le⟩ := PringsheimPsiAtom.genFun_le_linear C hC α
    (by linarith : α ≤ 1) σ_sign hσ
  have hσ₀_pos : 0 < σ₀ := by linarith
  have h_tendsto : Tendsto (fun n : ℕ => T₀ + (↑n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ T₀ tendsto_natCast_atTop_atTop
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (f := fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
    (μ := volume) (l := atTop) (b := fun n : ℕ => T₀ + ↑n) M T₀
  · -- IntegrableOn on each finite piece
    intro n
    apply Measure.integrableOn_of_bounded (measure_Ioc_lt_top.ne)
    · exact (((measurable_id.pow_const α |>.const_mul C).add
        ((measurable_id.sub Chebyshev.psi_mono.measurable).const_mul σ_sign)).mul
        (measurable_id.pow_const (-(σ₀ + 1)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ⟨ht1, htN⟩
      have ht_pos : 0 < t := by linarith
      have ht1' : 1 ≤ t := by linarith
      rw [Real.norm_eq_abs, abs_mul]
      calc |PringsheimPsiAtom.genFun C α σ_sign t| * |t ^ (-(σ₀ + 1))|
          ≤ (D * t) * 1 := by
            apply mul_le_mul (hg_le t ht1')
              (by rw [abs_of_pos (rpow_pos_of_pos ht_pos _)]
                  exact rpow_le_one_of_one_le_of_nonpos ht1' (by linarith))
              (abs_nonneg _) (by positivity)
        _ = D * t := mul_one _
        _ ≤ D * (T₀ + ↑n) := by nlinarith
  · exact h_tendsto
  · filter_upwards with n
    rw [intervalIntegral.integral_of_le (by linarith : T₀ ≤ T₀ + (↑n : ℝ))]
    exact hM n

end Aristotle.Standalone.LandauPringsheimRealLine
