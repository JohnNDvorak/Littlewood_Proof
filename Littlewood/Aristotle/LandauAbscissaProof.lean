/-
Proof of LandauAbscissaHyp (Landau's abscissa of convergence theorem).

For g(t) = C·t^α + σ·(t - ψ(t)) ≥ 0 eventually, the Dirichlet integral
∫₁^∞ g(t)·t^{-(σ₀+1)} dt converges for α < σ₀ ≤ 1.

## Proof Strategy

Split the integral at T₀ where g becomes non-negative:
  ∫₁^∞ = ∫₁^{T₀} + ∫_{T₀}^∞

**Compact part** [1, T₀]: Bounded integrand on finite-measure set → trivially integrable.

**Tail** [T₀, ∞) where g ≥ 0: The corrected formula
  F(s) = s·C/(s-α) + σ·(1 + zrf'/zrf(s))
is analytic on {Re(s) > α} (including at s = 1 where poles cancel). For σ > 1,
the formula equals s times the Dirichlet integral. By MCT (σ ↘ 1), the tail
converges at σ = 1. For σ₀ < 1, the Tonelli/Cauchy argument extends convergence:
the Taylor "anti-coefficients" a_k = ∫ g·t^{-2}·(log t)^k are non-negative and
bounded by Cauchy estimates from the analyticity at σ = 1, giving a convergent
geometric bound for Σ a_k·(1-σ₀)^k/k! = ∫ g·t^{-(σ₀+1)}.

## References

* Landau, "Über einen Satz von Tschebyschef" (1905), Satz 15
* Hardy-Riesz, "The General Theory of Dirichlet's Series", Ch. 1

SORRY COUNT: 0 (parameterized on SigmaLtOneHyp)
The σ₀ < 1 tail integrability is taken as a hypothesis and supplied externally.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.LandauAbscissaConvergence
import Littlewood.Aristotle.PringsheimPsiAtom
import Littlewood.Aristotle.Standalone.LandauSigmaOneMCT

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.LandauAbscissaProof

open Complex Real Filter Topology MeasureTheory Set

/-! ## Helper: compact part integrability

On the finite interval (1, T₀], the integrand is bounded (genFun ≤ D·t on [1,T₀]
and t^{-(σ₀+1)} ≤ 1), so IntegrableOn follows from finite measure + boundedness. -/

/-- genFun is measurable (chebyshevPsi is monotone hence measurable). -/
private theorem genFun_measurable (C α σ_sign : ℝ) :
    Measurable (fun t : ℝ => PringsheimPsiAtom.genFun C α σ_sign t) := by
  unfold PringsheimPsiAtom.genFun
  exact (measurable_id.pow_const α |>.const_mul C).add
    ((measurable_id.sub Chebyshev.psi_mono.measurable).const_mul σ_sign)

/-- The integrand is measurable on Ioi 1. -/
private theorem integrand_measurable (C α σ_sign σ₀ : ℝ) :
    Measurable (fun t : ℝ => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))) := by
  exact (genFun_measurable C α σ_sign).mul (measurable_id.pow_const _)

/-- IntegrableOn on the compact part (1, T₀]. -/
private theorem compact_part_integrableOn (C : ℝ) (hC : 0 < C)
    (α : ℝ) (hα1 : α ≤ 1) (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (σ₀ : ℝ) (hσ₀_pos : 0 < σ₀) (T₀ : ℝ) (_hT₀ : 1 ≤ T₀) :
    IntegrableOn (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
      (Ioc 1 T₀) := by
  -- Use: bounded AEStronglyMeasurable function on finite-measure set → integrable
  obtain ⟨D, _hD, hle⟩ := PringsheimPsiAtom.genFun_le_linear C hC α hα1 σ_sign hσ
  apply Measure.integrableOn_of_bounded (measure_Ioc_lt_top.ne)
    ((integrand_measurable C α σ_sign σ₀).aestronglyMeasurable) (M := D * T₀)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ⟨ht1, htT₀⟩
  have ht_pos : 0 < t := by linarith
  have ht1' : 1 ≤ t := by linarith
  rw [Real.norm_eq_abs, abs_mul]
  have h_rpow_le : |t ^ (-(σ₀ + 1))| ≤ 1 := by
    rw [abs_of_pos (rpow_pos_of_pos ht_pos _)]
    exact rpow_le_one_of_one_le_of_nonpos ht1' (by linarith)
  calc |PringsheimPsiAtom.genFun C α σ_sign t| * |t ^ (-(σ₀ + 1))|
      ≤ (D * t) * 1 :=
        mul_le_mul (hle t ht1') h_rpow_le (abs_nonneg _) (by positivity)
    _ = D * t := mul_one _
    _ ≤ D * T₀ := by nlinarith

/-! ## Helper: tail integrability

On [T₀, ∞) where g ≥ 0, the Dirichlet integral converges by the Landau
abscissa argument. This is the deep mathematical content.

**Proof sketch for the tail:**

For σ > 1 (known convergence), the real integral equals the corrected formula:
  ∫₁^∞ g(t) t^{-(σ+1)} = witnessG(σ)/σ

The corrected formula is analytic at σ = 1 (from ZetaPoleCancellation), so as
σ ↘ 1, the formula → finite limit L. By MCT on the tail (g ≥ 0, t > 1,
integrand increases as σ decreases), the tail integral at σ = 1 is finite.

For σ₀ ∈ (α, 1), the Taylor expansion at σ = 1 with non-negative "anti-coefficients"
  aₖ = ∫ g(t) t^{-2} (log t)^k dt ≥ 0
gives (by Tonelli for non-negative terms):
  ∫ g t^{-(σ₀+1)} = Σ aₖ (1-σ₀)^k / k!
The Taylor series of the corrected formula converges at σ₀ (radius ≥ 1-α),
and by Cauchy estimates aₖ ≤ k! M / r^k, so the sum is bounded by M·r/(r-(1-σ₀)) < ∞.
-/

/-! ### SigmaLtOneHyp and tail integrability helpers -/

/-- Hypothesis: tail integrability for σ₀ < 1 (Pringsheim/Tonelli argument).
This is the deep analytical content that requires the Pringsheim singularity
theorem on the real line combined with a Tonelli interchange. Supplied externally. -/
def SigmaLtOneHyp : Prop :=
  ∀ (C : ℝ), 0 < C → ∀ (α : ℝ), 1 / 2 < α → α < 1 →
  ∀ (σ_sign : ℝ), σ_sign = 1 ∨ σ_sign = -1 →
  (∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α) →
  ∀ (σ₀ : ℝ), α < σ₀ → σ₀ < 1 →
  ∀ (T₀ : ℝ), 1 ≤ T₀ →
  (∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t) →
  IntegrableOn (fun t : ℝ =>
    PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))) (Ioi T₀)

private theorem integrand_nonneg_on_tail (C α σ_sign σ₀ : ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t)
    (t : ℝ) (ht : t ∈ Ioi T₀) :
    0 ≤ PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)) := by
  have ht' : T₀ < t := mem_Ioi.mp ht
  apply mul_nonneg (hg_nn t (le_of_lt ht'))
  exact rpow_nonneg (by linarith : (0 : ℝ) ≤ t) _

/-- **Uniform lintegral bound** for the Dirichlet tail family as `σ → 1⁺`.

For `σ_n = 1 + 1/(n+1) > 1`, the corrected formula `witnessG(σ_n)` equals
the Dirichlet integral (by `witnessG_eq_formula`), and pole cancellation
(`ZetaPoleCancellation.landau_formula_analyticAt_real`) keeps it bounded as
`σ_n → 1`. Splitting off the compact part `(1, T₀]` gives a uniform bound
on the tail lintegrals.

SORRY: formula identity for σ > 1 + pole cancellation continuity at σ = 1. -/
private theorem dirichlet_tail_uniform_lintegral_bound
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (T₀ : ℝ) (_hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t) :
    ∃ M : ENNReal, M ≠ ⊤ ∧ ∀ n : ℕ,
      ∫⁻ t in Ioi T₀,
        ENNReal.ofReal (PringsheimPsiAtom.genFun C α σ_sign t *
          t ^ (-(2 + (1 : ℝ) / (↑n + 1)))) ≤ M := by
  let σn : ℕ → ℝ := fun n => 1 + (1 : ℝ) / (↑n + 1)
  let f : ℕ → ℝ → ℝ := fun n t =>
    PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σn n + 1))
  let corrected : ℂ → ℂ := fun s =>
    s * (↑C : ℂ) / (s - (↑α : ℂ)) +
      (↑σ_sign : ℂ) * (1 + deriv ZetaPoleCancellation.zrf s / ZetaPoleCancellation.zrf s)
  let correctedReal : ℝ → ℂ := fun x => corrected (x : ℂ)

  have hT₀ : 1 ≤ T₀ := _hT₀
  have hα1_le : α ≤ 1 := le_of_lt hα1
  have h_subset_tail : Ioi T₀ ⊆ Ioi (1 : ℝ) := by
    intro t ht
    exact lt_of_le_of_lt hT₀ ht
  have h_subset_head : Ioc 1 T₀ ⊆ Ioi (1 : ℝ) := by
    intro t ht
    exact ht.1
  have h_inter :
      Ioi (1 : ℝ) ∩ Ioc 1 T₀ = Ioc 1 T₀ := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨hx.1, hx⟩
  have h_diff :
      Ioi (1 : ℝ) \ Ioc 1 T₀ = Ioi T₀ := by
    ext x
    constructor
    · intro hx
      by_cases hxT : x ≤ T₀
      · exfalso
        exact hx.2 ⟨hx.1, hxT⟩
      · exact lt_of_not_ge hxT
    · intro hx
      refine ⟨lt_of_le_of_lt hT₀ hx, ?_⟩
      intro hmem
      exact not_lt_of_ge hmem.2 hx

  obtain ⟨D, hD, hle⟩ := PringsheimPsiAtom.genFun_le_linear C hC α hα1_le σ_sign hσ

  have h_integrable_gt_one :
      ∀ β : ℝ, 1 < β →
        IntegrableOn (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(β + 1)))
          (Ioi 1) := by
    intro β hβ
    have h_bound : IntegrableOn (fun t : ℝ => D * t ^ (-β)) (Ioi 1) := by
      exact (integrableOn_Ioi_rpow_of_lt (by linarith : -β < -1)
        (by norm_num : (0 : ℝ) < 1)).const_mul D
    apply h_bound.mono'
    · exact ((measurable_id.pow_const α |>.const_mul C).add
        ((measurable_id.sub Chebyshev.psi_mono.measurable).const_mul σ_sign) |>.mul
          (measurable_id.pow_const (-(β + 1)))).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := by linarith [show (1 : ℝ) < t from ht]
      have ht_pos : 0 < t := by linarith [show (1 : ℝ) < t from ht]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos ht_pos _)]
      calc |PringsheimPsiAtom.genFun C α σ_sign t| * t ^ (-(β + 1))
          ≤ D * t * t ^ (-(β + 1)) := by
            exact mul_le_mul_of_nonneg_right (hle t ht1) (rpow_nonneg (by linarith) _)
        _ = D * (t ^ (1 : ℝ) * t ^ (-(β + 1))) := by
            rw [rpow_one]
            ring
        _ = D * t ^ (1 + (-(β + 1))) := by
            rw [← rpow_add ht_pos]
        _ = D * t ^ (-β) := by ring_nf

  have h_corr_cont : ContinuousOn correctedReal (Set.Icc (1 : ℝ) 2) := by
    intro x hx
    have hxα : α < x := by linarith [hα1, hx.1]
    have h_anal := ZetaPoleCancellation.landau_formula_analyticAt_real α hα C σ_sign x hxα
    exact (h_anal.continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt

  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2)).exists_bound_of_continuousOn
    h_corr_cont
  have hK_nonneg : 0 ≤ K := by
    exact le_trans (norm_nonneg _) (hK 1 (by simp))

  let H : ℝ := ∫ t in Ioc 1 T₀, (D * T₀)
  have hH_nonneg : 0 ≤ H := by
    unfold H
    exact setIntegral_nonneg measurableSet_Ioc (fun _ _ => by positivity)

  have h_tail_nonneg :
      ∀ n : ℕ, 0 ≤ᵐ[volume.restrict (Ioi T₀)] fun t => f n t := by
    intro n
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    exact integrand_nonneg_on_tail C α σ_sign (σn n) T₀ hT₀ hg_nn t ht

  have h_head_abs_bound :
      ∀ n : ℕ, |∫ t in Ioc 1 T₀, f n t| ≤ H := by
    intro n
    have hfi : IntegrableOn (f n) (Ioc 1 T₀) :=
      (h_integrable_gt_one (σn n) (by
        have hdiv_pos : 0 < (1 : ℝ) / (↑n + 1) := by positivity
        linarith)).mono_set h_subset_head
    have hfi_abs : IntegrableOn (fun t => |f n t|) (Ioc 1 T₀) := hfi.norm
    have hfi_const : IntegrableOn (fun _ : ℝ => D * T₀) (Ioc 1 T₀) := by
      exact MeasureTheory.integrableOn_const (measure_Ioc_lt_top.ne)
    have h_ae_le :
        (fun t => |f n t|) ≤ᵐ[volume.restrict (Ioc 1 T₀)] fun _ => D * T₀ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht_pos : 0 < t := lt_trans zero_lt_one ht.1
      have ht1 : 1 ≤ t := le_of_lt ht.1
      rw [abs_mul]
      have hpow : |t ^ (-(σn n + 1))| ≤ 1 := by
        rw [abs_of_pos (rpow_pos_of_pos ht_pos _)]
        exact rpow_le_one_of_one_le_of_nonpos ht1 (by
          have hσn_pos : 0 < σn n := by
            have hdiv_pos : 0 < (1 : ℝ) / (↑n + 1) := by positivity
            linarith
          linarith)
      calc
        |PringsheimPsiAtom.genFun C α σ_sign t| * |t ^ (-(σn n + 1))|
            ≤ (D * t) * 1 := by
              exact mul_le_mul (hle t ht1) hpow (abs_nonneg _) (by positivity)
        _ = D * t := by ring
        _ ≤ D * T₀ := by
              exact mul_le_mul_of_nonneg_left ht.2 (le_of_lt hD)
    have h_int_abs_le :
        ∫ t in Ioc 1 T₀, |f n t| ≤ ∫ t in Ioc 1 T₀, D * T₀ := by
      exact MeasureTheory.integral_mono_ae hfi_abs hfi_const h_ae_le
    have h_abs_int :
        |∫ t in Ioc 1 T₀, f n t| ≤ ∫ t in Ioc 1 T₀, |f n t| := by
      simpa using MeasureTheory.abs_integral_le_integral_abs (μ := volume.restrict (Ioc 1 T₀))
        (f := f n)
    exact h_abs_int.trans (by simpa [H] using h_int_abs_le)

  have h_total_abs_bound :
      ∀ n : ℕ, |∫ t in Ioi (1 : ℝ), f n t| ≤ K := by
    intro n
    have hσn_gt1 : 1 < σn n := by
      have hdiv_pos : 0 < (1 : ℝ) / (↑n + 1) := by positivity
      linarith
    have hσn_ge1 : (1 : ℝ) ≤ σn n := by linarith
    have hσn_le2 : σn n ≤ 2 := by
      have hden : (1 : ℝ) ≤ (↑n + 1) := by nlinarith
      have hdiv_le : (1 : ℝ) / (↑n + 1) ≤ 1 := by
        have hden_pos : 0 < (↑n + 1 : ℝ) := by positivity
        have haux :
            (1 : ℝ) / (↑n + 1) ≤ (1 : ℝ) / 1 :=
          (one_div_le_one_div hden_pos zero_lt_one).2 hden
        simpa using haux
      linarith
    have hσn_mem : σn n ∈ Set.Icc (1 : ℝ) 2 := ⟨hσn_ge1, hσn_le2⟩
    have h_corr_bound : ‖correctedReal (σn n)‖ ≤ K := hK (σn n) hσn_mem

    have h_formula :
        PringsheimPsiAtom.witnessG C α σ_sign (σn n) =
          (↑(σn n) : ℂ) * (↑C : ℂ) / ((↑(σn n) : ℂ) - (↑α : ℂ)) +
          (↑σ_sign : ℂ) * ((↑(σn n) : ℂ) / ((↑(σn n) : ℂ) - 1)) +
          (↑σ_sign : ℂ) * (deriv riemannZeta (↑(σn n) : ℂ) / riemannZeta (↑(σn n) : ℂ)) := by
      simpa using PringsheimPsiAtom.witnessG_eq_formula C hC α hα σ_sign hσ hbound
        (σn n) hσn_gt1 (lt_of_lt_of_le hα1 hσn_ge1)
    have h_wit_eq_corr :
        PringsheimPsiAtom.witnessG C α σ_sign (σn n) = correctedReal (σn n) := by
      rw [h_formula]
      simpa [corrected, correctedReal] using
        (ZetaPoleCancellation.landau_formula_eq_original α C (σn n) hσn_gt1 σ_sign).symm
    have h_wit_bound :
        ‖PringsheimPsiAtom.witnessG C α σ_sign (σn n)‖ ≤ K := by
      simpa [h_wit_eq_corr] using h_corr_bound

    have h_dirichlet_eq :
        PringsheimPsiAtom.dirichletIntegral C α σ_sign (σn n : ℂ) =
          ((∫ t in Ioi (1 : ℝ), f n t) : ℂ) := by
      unfold PringsheimPsiAtom.dirichletIntegral
      have h_eq :
          ∀ t ∈ Ioi (1 : ℝ),
            ((↑(PringsheimPsiAtom.genFun C α σ_sign t) : ℂ) *
              (↑t : ℂ) ^ (-(((σn n : ℂ)) + 1))) =
              ((PringsheimPsiAtom.genFun C α σ_sign t * Real.rpow t (-(σn n + 1)) : ℝ) : ℂ) := by
        intro t ht
        have ht0 : 0 ≤ t := by linarith [show (1 : ℝ) < t from ht]
        have h_exp : (-(((σn n : ℂ)) + (1 : ℂ)) : ℂ) = ((-(σn n + 1) : ℝ) : ℂ) := by
          norm_num
        have hpow :
            (↑t : ℂ) ^ (-(((σn n : ℂ)) + 1)) =
              ((Real.rpow t (-(σn n + 1)) : ℝ) : ℂ) := by
          rw [h_exp]
          simpa using (Complex.ofReal_cpow ht0 (-(σn n + 1))).symm
        rw [hpow]
        norm_num
      rw [setIntegral_congr_fun measurableSet_Ioi h_eq]
      simpa [f] using
        (integral_ofReal (μ := volume.restrict (Ioi (1 : ℝ)))
          (f := fun t => PringsheimPsiAtom.genFun C α σ_sign t * Real.rpow t (-(σn n + 1))))

    have h_dirichlet_le_wit :
        ‖PringsheimPsiAtom.dirichletIntegral C α σ_sign (σn n : ℂ)‖
          ≤ ‖PringsheimPsiAtom.witnessG C α σ_sign (σn n)‖ := by
      have h_wit_mul :
          PringsheimPsiAtom.witnessG C α σ_sign (σn n) =
            ((σn n : ℂ) * PringsheimPsiAtom.dirichletIntegral C α σ_sign (σn n : ℂ)) := by
        rfl
      rw [h_wit_mul, norm_mul]
      have hσ_norm : (1 : ℝ) ≤ ‖(σn n : ℂ)‖ := by
        have hσ_nonneg : 0 ≤ σn n := by linarith [hσn_ge1]
        have habs_ge : (1 : ℝ) ≤ |σn n| := by
          simpa [abs_of_nonneg hσ_nonneg] using hσn_ge1
        simpa [Complex.norm_real, Real.norm_eq_abs] using habs_ge
      nlinarith [norm_nonneg (PringsheimPsiAtom.dirichletIntegral C α σ_sign (σn n : ℂ))]
    have h_dirichlet_bound :
        ‖PringsheimPsiAtom.dirichletIntegral C α σ_sign (σn n : ℂ)‖ ≤ K :=
      le_trans h_dirichlet_le_wit h_wit_bound
    have h_abs_eq :
        |∫ t in Ioi (1 : ℝ), f n t| =
          ‖PringsheimPsiAtom.dirichletIntegral C α σ_sign (σn n : ℂ)‖ := by
      let Ireal : ℝ := ∫ t, f n t ∂(volume.restrict (Ioi (1 : ℝ)))
      have h_cast_int :
          (∫ t, (↑(f n t) : ℂ) ∂(volume.restrict (Ioi (1 : ℝ)))) =
            (Ireal : ℂ) := by
        simpa [Ireal] using (integral_ofReal (μ := volume.restrict (Ioi (1 : ℝ))) (f := f n))
      have h_cast_norm :
          ‖∫ t, (↑(f n t) : ℂ) ∂(volume.restrict (Ioi (1 : ℝ)))‖ =
            |Ireal| := by
        rw [h_cast_int]
        simpa [Complex.norm_real, Real.norm_eq_abs]
      calc
        |∫ t in Ioi (1 : ℝ), f n t|
            = ‖∫ t, (↑(f n t) : ℂ) ∂(volume.restrict (Ioi (1 : ℝ)))‖ := by
                simpa [Ireal] using h_cast_norm.symm
        _ = ‖PringsheimPsiAtom.dirichletIntegral C α σ_sign (σn n : ℂ)‖ := by
            rw [h_dirichlet_eq]
    simpa [h_abs_eq] using h_dirichlet_bound

  have h_tail_real_bound :
      ∀ n : ℕ, ∫ t in Ioi T₀, f n t ≤ K + H := by
    intro n
    have hfi : IntegrableOn (f n) (Ioi 1) :=
      h_integrable_gt_one (σn n) (by
        have hdiv_pos : 0 < (1 : ℝ) / (↑n + 1) := by positivity
        linarith)
    have hsplit0 := MeasureTheory.integral_inter_add_diff (f := f n)
      (s := Ioi (1 : ℝ)) (t := Ioc 1 T₀) measurableSet_Ioc hfi
    have hsplit :
        (∫ t in Ioc 1 T₀, f n t ∂volume) + (∫ t in Ioi T₀, f n t ∂volume) =
          (∫ t in Ioi (1 : ℝ), f n t ∂volume) := by
      simpa [h_inter, h_diff] using hsplit0
    have htail_nonneg :
        0 ≤ ∫ t in Ioi T₀, f n t ∂volume := by
      exact MeasureTheory.integral_nonneg_of_ae (h_tail_nonneg n)
    have h_eq :
        (∫ t in Ioi T₀, f n t ∂volume) =
          (∫ t in Ioi (1 : ℝ), f n t ∂volume) - (∫ t in Ioc 1 T₀, f n t ∂volume) := by
      exact (eq_sub_iff_add_eq').2 hsplit
    have h_abs_tail :
        |∫ t in Ioi T₀, f n t ∂volume|
          ≤ |∫ t in Ioi (1 : ℝ), f n t ∂volume| + |∫ t in Ioc 1 T₀, f n t ∂volume| := by
      rw [h_eq]
      simpa using abs_sub (∫ t in Ioi (1 : ℝ), f n t ∂volume) (∫ t in Ioc 1 T₀, f n t ∂volume)
    have h_tail_le :
        (∫ t in Ioi T₀, f n t ∂volume)
          ≤ |∫ t in Ioi (1 : ℝ), f n t ∂volume| + |∫ t in Ioc 1 T₀, f n t ∂volume| := by
      simpa [abs_of_nonneg htail_nonneg] using h_abs_tail
    exact le_trans h_tail_le (by linarith [h_total_abs_bound n, h_head_abs_bound n])

  let M : ENNReal := ENNReal.ofReal (K + H)
  refine ⟨M, by simp [M], ?_⟩
  intro n
  have hfi_tail : IntegrableOn (f n) (Ioi T₀) :=
    (h_integrable_gt_one (σn n) (by
      have hdiv_pos : 0 < (1 : ℝ) / (↑n + 1) := by positivity
      linarith)).mono_set h_subset_tail
  have hlin_eq :
      ENNReal.ofReal (∫ t in Ioi T₀, f n t) =
        ∫⁻ t in Ioi T₀, ENNReal.ofReal (f n t) := by
    simpa using MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := volume.restrict (Ioi T₀)) (f := f n) hfi_tail (h_tail_nonneg n)
  have h_ofReal_le :
      ENNReal.ofReal (∫ t in Ioi T₀, f n t) ≤ M := by
    refine ENNReal.ofReal_le_ofReal ?_
    simpa [M] using h_tail_real_bound n
  calc
    ∫⁻ t in Ioi T₀,
        ENNReal.ofReal (PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(2 + (1 : ℝ) / (↑n + 1))))
      = ∫⁻ t in Ioi T₀, ENNReal.ofReal (f n t) := by
          refine setLIntegral_congr_fun measurableSet_Ioi ?_
          intro t ht
          change ENNReal.ofReal (PringsheimPsiAtom.genFun C α σ_sign t *
            t ^ (-(2 + (1 : ℝ) / (↑n + 1)))) =
              ENNReal.ofReal (PringsheimPsiAtom.genFun C α σ_sign t *
                t ^ (-(σn n + 1)))
          have h_exp : -(2 + (1 : ℝ) / (↑n + 1)) = -(σn n + 1) := by
            simp [σn]
            ring
          rw [h_exp]
    _ = ENNReal.ofReal (∫ t in Ioi T₀, f n t) := by
          exact hlin_eq.symm
    _ ≤ M := h_ofReal_le

/-- **Landau abscissa bound at σ₀ = 1** via monotone convergence.

Uses `LandauSigmaOneMCT.integrableOn_rpow_neg_two_of_dirichlet_tail_family`:
the family `g(t)·t^{-(2+1/(n+1))}` increases to `g(t)·t^{-2}` with uniform
lintegral bound, so MCT gives IntegrableOn at the limit exponent `-2`. -/
theorem tail_integrableOn_at_sigma_one
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t) :
    IntegrableOn (fun t : ℝ =>
      PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(2 : ℝ))) (Ioi T₀) := by
  obtain ⟨M, hM, hbound_n⟩ := dirichlet_tail_uniform_lintegral_bound
    C hC α hα hα1 σ_sign hσ hbound T₀ hT₀ hg_nn
  exact Aristotle.Standalone.LandauSigmaOneMCT.integrableOn_rpow_neg_two_of_dirichlet_tail_family
    (PringsheimPsiAtom.genFun C α σ_sign) T₀ hT₀
    (genFun_measurable C α σ_sign)
    (fun t ht => hg_nn t (le_of_lt ht))
    M hM hbound_n

/-- **Landau abscissa bound at σ₀ < 1** via Pringsheim singularity extension.

The Dirichlet integral `∫ g(t)·t^{-(σ₀+1)} dt` converges for `α < σ₀ < 1`
by the following argument:

1. At σ = 1, IntegrableOn is proved by MCT (`tail_integrableOn_at_sigma_one`).
2. The corrected formula `F(s) = s·C/(s-α) + σ·(1 + zrf'/zrf(s))` is analytic
   on `{Re(s) > α}` (from `landau_formula_analyticAt_real`).
3. The Taylor "anti-coefficients" at center `σ₁ = 2` are non-negative (since g ≥ 0).
4. By Pringsheim's singularity theorem, the radius of convergence of the non-negative
   coefficient series extends to `2 - α` (since F is analytic at every real point > α).
5. For `σ₀ > α`, we have `2 - σ₀ < 2 - α`, so the series converges at `w = 2 - σ₀`.
6. By Tonelli, the integral at σ₀ equals the series evaluation, hence finite.

Dispatched via SigmaLtOneHyp (supplied externally). -/
private theorem tail_integrableOn_sigma_lt_one (hyp : SigmaLtOneHyp)
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀_lt1 : σ₀ < 1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t) :
    IntegrableOn (fun t : ℝ =>
      PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))) (Ioi T₀) :=
  hyp C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn

/-- **Landau abscissa bound** (Satz 15 analytical core):
The partial integrals of the non-negative generating function are uniformly bounded.

**Case σ₀ = 1**: MCT from σ > 1 (`tail_integrableOn_at_sigma_one`) gives
IntegrableOn, hence bounded partial integrals.

**Case σ₀ < 1**: Tonelli/Cauchy argument. The Taylor "anti-coefficients"
`aₖ = ∫ g·t⁻³·(log t)^k/k!` at center `σ₁ = 2` are non-negative, bounded by
Cauchy estimates from analyticity of the corrected formula on `B(2, 2-α)`.
For `w = 2-σ₀ < 2-α`: `∫ g·t^{-(σ₀+1)} ≤ Σ aₖ·w^k < ∞` by Tonelli.

The σ₀ < 1 case uses `tail_integrableOn_sigma_lt_one` (via SigmaLtOneHyp). -/
private theorem partial_integrals_bounded (hyp : SigmaLtOneHyp)
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (_hα1 : α ≤ 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (_hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀1 : σ₀ ≤ 1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + ↑N),
        ‖PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))‖ ≤ M := by
  by_cases hσ₀_eq : σ₀ = 1
  · -- Case σ₀ = 1: MCT gives IntegrableOn → bounded partial integrals
    subst hσ₀_eq
    have hα_lt1 : α < 1 := by linarith [hσ₀]
    have h_int := tail_integrableOn_at_sigma_one C hC α hα hα_lt1 σ_sign hσ
      _hbound T₀ hT₀ hg_nn
    -- -(1 + 1) = -2 in the exponent
    have h_int' : IntegrableOn (fun t : ℝ =>
        PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(1 + 1 : ℝ))) (Ioi T₀) := by
      convert h_int using 3; norm_num
    -- Extract bounded partial integrals from IntegrableOn
    refine ⟨∫ t in Ioi T₀,
        ‖PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(1 + 1 : ℝ))‖,
      integral_nonneg (fun _ => norm_nonneg _), fun N => ?_⟩
    exact setIntegral_mono_set h_int'.norm
      (ae_of_all _ (fun _ => norm_nonneg _))
      (Eventually.of_forall (fun t ht => Ioc_subset_Ioi_self ht))
  · -- Case σ₀ < 1: Pringsheim singularity extension gives IntegrableOn
    have hα_lt1 : α < 1 := by linarith [hσ₀]
    have hσ₀_lt1 : σ₀ < 1 := lt_of_le_of_ne hσ₀1 hσ₀_eq
    have h_int := tail_integrableOn_sigma_lt_one hyp C hC α hα hα_lt1 σ_sign hσ
      _hbound σ₀ hσ₀ hσ₀_lt1 T₀ hT₀ hg_nn
    refine ⟨∫ t in Ioi T₀,
        ‖PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))‖,
      integral_nonneg (fun _ => norm_nonneg _), fun N => ?_⟩
    exact setIntegral_mono_set h_int.norm
      (ae_of_all _ (fun _ => norm_nonneg _))
      (Eventually.of_forall (fun t ht => Ioc_subset_Ioi_self ht))

private theorem tail_integrableOn_of_nonneg (hyp : SigmaLtOneHyp)
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀1 : σ₀ ≤ 1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t) :
    IntegrableOn (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
      (Ioi T₀) := by
  obtain ⟨D, hD, hg_le⟩ := PringsheimPsiAtom.genFun_le_linear C hC α hα1 σ_sign hσ
  obtain ⟨M, hM_nn, hM⟩ := partial_integrals_bounded hyp C hC α hα hα1 σ_sign hσ hbound
    σ₀ hσ₀ hσ₀1 T₀ hT₀ hg_nn
  -- Apply the bounded-partial-integrals criterion
  have h_tendsto : Tendsto (fun n : ℕ => T₀ + (↑n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ T₀ tendsto_natCast_atTop_atTop
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (f := fun t =>
    PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
    (μ := volume) (l := atTop) (b := fun n : ℕ => T₀ + ↑n) M T₀
  · -- IntegrableOn on each finite piece Ioc T₀ (T₀ + n)
    intro n
    apply Measure.integrableOn_of_bounded (measure_Ioc_lt_top.ne)
      ((integrand_measurable C α σ_sign σ₀).aestronglyMeasurable) (M := D * (T₀ + ↑n))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ⟨ht1, htN⟩
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
  · -- b n = T₀ + n → ∞
    exact h_tendsto
  · -- Partial integral of norm ≤ M
    filter_upwards with n
    rw [intervalIntegral.integral_of_le (by linarith : T₀ ≤ T₀ + (↑n : ℝ))]
    exact hM n

/-! ## Main theorem assembly -/

/-- **Core lemma**: If g ≥ 0 eventually and the corrected formula is analytic at
real σ₀ > α, then the Dirichlet integral converges at σ₀.

Splits the integral at T₀ into compact + tail:
- Compact (1, T₀]: bounded × finite measure → integrable
- Tail (T₀, ∞): g ≥ 0, use Landau's abscissa argument -/
theorem nonneg_dirichlet_integral_of_formula_analytic (hyp : SigmaLtOneHyp)
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀1 : σ₀ ≤ 1) :
    IntegrableOn (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
      (Ioi 1) := by
  have hσ₀_pos : 0 < σ₀ := by linarith
  -- Extract T₀ from the eventual non-negativity
  have hnn := PringsheimPsiAtom.genFun_nonneg_eventually α C hC σ_sign hσ hbound
  rw [Filter.Eventually, Filter.mem_atTop_sets] at hnn
  obtain ⟨T₀_raw, hT₀_raw⟩ := hnn
  -- Ensure T₀ ≥ 1 (so Ioi 1 ⊇ Ioi T₀)
  set T₀ := max T₀_raw 1 with hT₀_def
  have hT₀ : 1 ≤ T₀ := le_max_right _ _
  have hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t := by
    intro t ht
    exact hT₀_raw t (le_trans (le_max_left _ _) ht)
  -- Split: Ioi 1 = Ioc 1 T₀ ∪ Ioi T₀
  have h_split : Ioi (1 : ℝ) = Ioc 1 T₀ ∪ Ioi T₀ := by
    ext x; simp only [mem_Ioi, mem_Ioc, mem_union, mem_Ioi]
    constructor
    · intro hx; by_cases hxT : x ≤ T₀
      · exact Or.inl ⟨hx, hxT⟩
      · exact Or.inr (by linarith)
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · linarith
  rw [h_split]
  apply IntegrableOn.union
  · -- Compact part: (1, T₀]
    exact compact_part_integrableOn C hC α hα1 σ_sign hσ σ₀ hσ₀_pos T₀ hT₀
  · -- Tail: (T₀, ∞) where g ≥ 0
    exact tail_integrableOn_of_nonneg hyp C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀1
      T₀ hT₀ hg_nn

/-! ## Main theorems -/

/-- **Landau's abscissa of convergence theorem** — proves `RealIntegrabilityHyp`.

Combines the non-negative tail argument with the compact piece to get
full integrability on (1, ∞). -/
theorem real_integrability_hyp (hyp : SigmaLtOneHyp) :
    LandauAbscissaConvergence.RealIntegrabilityHyp := by
  intro C hC α hα σ_sign hσ hbound σ₀ hσ₀ hσ₀1
  exact nonneg_dirichlet_integral_of_formula_analytic hyp C hC α hα (by linarith) σ_sign hσ
    hbound σ₀ hσ₀ hσ₀1

/-- **LandauAbscissaHyp** — the main result, proved from RealIntegrabilityHyp.
Takes `SigmaLtOneHyp` as a parameter (the Pringsheim/Tonelli deep content). -/
theorem landau_abscissa_hyp_proved (hyp : SigmaLtOneHyp) :
    PringsheimPsiAtom.LandauAbscissaHyp :=
  LandauAbscissaConvergence.landau_abscissa_hyp (real_integrability_hyp hyp)

end Aristotle.LandauAbscissaProof
