/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Littlewood.CoreLemmas.LandauLemma

/-!
# Landau's Lemma — Proof

This file proves Landau's fundamental lemma: for a Dirichlet integral
∫₁^∞ A(x)x^{-s} dx with A ≥ 0, if the integral converges for Re(s) > σ_c
but diverges at s = σ_c, then the function cannot be analytic at σ_c.

## Main Results

* `Landau.dirichletIntegral_not_analyticAt` — The singularity theorem: if A ≥ 0
  and the Dirichlet integral diverges at σ_c, it cannot be analytic there.
* `Landau.landauLemmaHyp_of` — Construction of `LandauLemmaHyp` from natural hypotheses.
* `Landau.integrable_at_limit_of_bounded` — MCT lemma: uniformly bounded non-negative
  integrals force integrability at the limit.

## Proof Strategy for `not_analytic_at`

Suppose for contradiction that F(s) = dirichletIntegral A s is analytic at σ_c.
Then F is continuous at σ_c, hence bounded in a neighborhood.
For real σ > σ_c, ‖F(σ)‖ = ∫ A(x) x^{-σ} dx (since A ≥ 0, the integrand is
non-negative). So the real integral is bounded for σ near σ_c.
By monotone convergence (via lintegral MCT on the sequence σ_n = σ_c + 1/(n+1)),
the integral at σ_c converges — contradicting the divergence hypothesis.

## References

* Landau, "Über einen Satz von Tschebyschef" (1905), Satz 15
* Montgomery-Vaughan, "Multiplicative Number Theory I", Lemma 15.1
-/

set_option maxHeartbeats 800000

open Complex Real Filter Topology Set MeasureTheory

namespace Landau

/-! ## Key lemma: cpow for positive reals with real exponents -/

/-- For x > 0 and σ real, (x : ℂ) ^ (-(σ : ℂ)) = ↑(x ^ (-σ)). -/
lemma cpow_neg_ofReal_eq (x : ℝ) (hx : 0 < x) (σ : ℝ) :
    (x : ℂ) ^ (-(σ : ℂ)) = ↑(x ^ (-σ) : ℝ) := by
  rw [show -(σ : ℂ) = ((-σ : ℝ) : ℂ) from by push_cast; ring]
  exact (Complex.ofReal_cpow hx.le _).symm

/-- The integrand of dirichletIntegral, for real s = σ, equals the real integrand cast to ℂ. -/
lemma dirichletIntegral_integrand_real (A : ℝ → ℝ) (x : ℝ) (hx : 1 < x) (σ : ℝ) :
    A x * (x : ℂ) ^ (-(σ : ℂ)) = ↑(A x * x ^ (-σ) : ℝ) := by
  rw [cpow_neg_ofReal_eq x (by linarith) σ, ofReal_mul]

/-! ## The dirichletIntegral at real s equals the real integral cast to ℂ -/

/-- For real σ, the complex dirichletIntegral equals the cast of the real integral. -/
lemma dirichletIntegral_ofReal (A : ℝ → ℝ) (σ : ℝ) :
    dirichletIntegral A (σ : ℂ) =
      ↑(∫ x in Ioi 1, A x * x ^ (-σ) : ℝ) := by
  unfold dirichletIntegral
  have h_eq : (fun x => A x * (x : ℂ) ^ (-(σ : ℂ))) =ᵐ[volume.restrict (Ioi 1)]
      (fun x => (↑(A x * x ^ (-σ)) : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact dirichletIntegral_integrand_real A x hx σ
  rw [integral_congr_ae h_eq]
  exact integral_ofReal

/-! ## Non-negative real integral gives non-negative values -/

/-- The real integral ∫ A(x) x^{-σ} dx is non-negative when A ≥ 0 on Ioi 1. -/
lemma integral_nonneg_of_A_nonneg (A : ℝ → ℝ) (σ : ℝ)
    (hA_nonneg : ∀ x ∈ Ioi (1:ℝ), 0 ≤ A x) :
    0 ≤ ∫ x in Ioi 1, A x * x ^ (-σ) := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (hA_nonneg x hx)
    (rpow_nonneg (le_of_lt (show (0 : ℝ) < x from lt_trans one_pos hx)) _)

/-! ## Norm of dirichletIntegral at real σ equals the real integral -/

/-- When A ≥ 0, ‖dirichletIntegral A σ‖ = ∫ A(x) x^{-σ} dx. -/
lemma norm_dirichletIntegral_eq (A : ℝ → ℝ) (σ : ℝ)
    (hA_nonneg : ∀ x ∈ Ioi (1:ℝ), 0 ≤ A x) :
    ‖dirichletIntegral A (σ : ℂ)‖ = ∫ x in Ioi 1, A x * x ^ (-σ) := by
  rw [dirichletIntegral_ofReal A σ, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg_of_A_nonneg A σ hA_nonneg)]

/-! ## The integral is monotone in σ -/

/-- For A ≥ 0 and x ≥ 1, if σ₁ ≥ σ₂, then A(x) x^{-σ₁} ≤ A(x) x^{-σ₂}. -/
lemma integrand_antitone_sigma (A : ℝ → ℝ) (x : ℝ) (hx : 1 ≤ x)
    (hA : 0 ≤ A x) (σ₁ σ₂ : ℝ) (hσ : σ₂ ≤ σ₁) :
    A x * x ^ (-σ₁) ≤ A x * x ^ (-σ₂) := by
  apply mul_le_mul_of_nonneg_left _ hA
  apply rpow_le_rpow_of_exponent_le hx
  linarith

/-! ## MCT argument: bounded integrals imply integrability at the limit -/

/-- **Monotone convergence bound**: If A ≥ 0, A is measurable, and the real integrals
    ∫ A(x) x^{-σ} dx are uniformly bounded by M for all σ > σ_c, then the integral
    at σ_c is also integrable.

    Proof: Define σ_n = σ_c + 1/(n+1). The functions f_n(x) = A(x) x^{-σ_n} increase
    pointwise to f(x) = A(x) x^{-σ_c} as n → ∞. By lintegral MCT, the Lebesgue integral
    of f is the supremum of the Lebesgue integrals of f_n, each of which is ≤ M.
    Hence ∫⁻ f ≤ M < ∞, so f is integrable. -/
lemma integrable_at_limit_of_bounded
    (A : ℝ → ℝ) (σ_c : ℝ)
    (hA_nonneg : ∀ x ∈ Ioi (1:ℝ), 0 ≤ A x)
    (hA_meas : Measurable A)
    (h_integrable : ∀ σ : ℝ, σ_c < σ →
      Integrable (fun x => A x * x ^ (-σ)) (volume.restrict (Ioi 1)))
    (M : ℝ) (hM : ∀ σ : ℝ, σ_c < σ →
      ∫ x in Ioi 1, A x * x ^ (-σ) ≤ M) :
    Integrable (fun x => A x * x ^ (-σ_c)) (volume.restrict (Ioi 1)) := by
  have h_integrable_sigma_c : ∫⁻ x in Set.Ioi 1, ENNReal.ofReal (A x * x ^ (-σ_c)) ≤ ENNReal.ofReal M := by
    have h_integrable_sigma_c : ∀ n : ℕ, ∫⁻ x in Set.Ioi 1, ENNReal.ofReal (A x * x ^ (-(σ_c + 1 / (n + 1)))) ≤ ENNReal.ofReal M := by
      intro n
      have h_integrable_sigma_c : ∫⁻ x in Set.Ioi 1, ENNReal.ofReal (A x * x ^ (-(σ_c + 1 / (n + 1)))) = ENNReal.ofReal (∫ x in Set.Ioi 1, A x * x ^ (-(σ_c + 1 / (n + 1)))) := by
        rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ]
        · exact h_integrable _ ( by norm_num; linarith )
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using mul_nonneg ( hA_nonneg x hx ) ( Real.rpow_nonneg ( by linarith [ hx.out ] ) _ )
      exact h_integrable_sigma_c.symm ▸ ENNReal.ofReal_le_ofReal ( hM _ ( lt_add_of_pos_right _ ( by positivity ) ) )
    have h_integrable_sigma_c : Filter.Tendsto (fun n : ℕ => ∫⁻ x in Set.Ioi 1, ENNReal.ofReal (A x * x ^ (-(σ_c + 1 / (n + 1))))) Filter.atTop (nhds (∫⁻ x in Set.Ioi 1, ENNReal.ofReal (A x * x ^ (-σ_c)))) := by
      refine' MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone _ _ _
      · exact fun n => Measurable.aemeasurable ( by measurability )
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx
        refine' fun n m hnm => ENNReal.ofReal_le_ofReal _
        exact mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow_of_exponent_le hx.out.le <| by gcongr ) <| hA_nonneg x hx
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx
        refine' ENNReal.tendsto_ofReal _
        exact tendsto_const_nhds.mul ( tendsto_const_nhds.rpow ( Filter.Tendsto.neg <| tendsto_const_nhds.add <| tendsto_one_div_add_atTop_nhds_zero_nat ) <| Or.inl <| by linarith [ hx.out ] ) |> fun h => h.trans <| by norm_num
    exact le_of_tendsto' h_integrable_sigma_c fun n => by aesop
  refine' ⟨ _, _ ⟩
  · exact MeasureTheory.AEStronglyMeasurable.mul ( hA_meas.aestronglyMeasurable ) ( measurable_id.pow_const _ |> Measurable.aestronglyMeasurable )
  · rw [ hasFiniteIntegral_iff_norm ]
    refine' lt_of_le_of_lt ( MeasureTheory.setLIntegral_mono' measurableSet_Ioi fun x hx => _ ) ( lt_of_le_of_lt h_integrable_sigma_c ENNReal.ofReal_lt_top )
    rw [ Real.norm_of_nonneg ( mul_nonneg ( hA_nonneg x hx ) ( Real.rpow_nonneg ( by linarith [ hx.out ] ) _ ) ) ]

/-! ## Main theorem: not analytic at σ_c -/

/-- **Landau's Lemma (singularity direction)**: If A ≥ 0, the Dirichlet integral
    converges for σ > σ_c (real), diverges at σ = σ_c, then the dirichletIntegral
    function cannot be analytic at the real point σ_c. -/
theorem dirichletIntegral_not_analyticAt
    (A : ℝ → ℝ) (σ_c : ℝ)
    (hA_nonneg : ∀ x ∈ Ioi (1:ℝ), 0 ≤ A x)
    (hA_meas : Measurable A)
    (h_not_integrable : ¬ Integrable
      (fun x => A x * x ^ (-σ_c)) (volume.restrict (Ioi 1)))
    (h_integrable_real : ∀ σ : ℝ, σ_c < σ →
      Integrable (fun x => A x * x ^ (-σ)) (volume.restrict (Ioi 1))) :
    ¬AnalyticAt ℂ (dirichletIntegral A) (σ_c : ℂ) := by
  intro h_analytic
  -- Step 1: Analytic ⟹ continuous ⟹ bounded near σ_c
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp h_analytic.continuousAt 1 one_pos
  -- Step 2: For σ ∈ (σ_c, σ_c + ε), ‖F(σ)‖ < ‖F(σ_c)‖ + 1
  have h_bound : ∀ σ : ℝ, σ_c < σ → σ < σ_c + ε →
      ∫ x in Ioi 1, A x * x ^ (-σ) < ‖dirichletIntegral A (σ_c : ℂ)‖ + 1 := by
    intro σ hσ_lo hσ_hi
    have h_dist : dist (↑σ : ℂ) (↑σ_c : ℂ) < ε := by
      rw [Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
      linarith
    rw [← norm_dirichletIntegral_eq A σ hA_nonneg]
    calc ‖dirichletIntegral A (↑σ)‖
        = ‖dirichletIntegral A (↑σ_c) +
            (dirichletIntegral A (↑σ) - dirichletIntegral A (↑σ_c))‖ := by ring_nf
      _ ≤ ‖dirichletIntegral A (↑σ_c)‖ +
            ‖dirichletIntegral A (↑σ) - dirichletIntegral A (↑σ_c)‖ := norm_add_le _ _
      _ = ‖dirichletIntegral A (↑σ_c)‖ +
            dist (dirichletIntegral A (↑σ)) (dirichletIntegral A (↑σ_c)) := by
          rw [dist_eq_norm]
      _ < ‖dirichletIntegral A (↑σ_c)‖ + 1 := by linarith [hball h_dist]
  -- Step 3: The real integral is uniformly bounded for all σ > σ_c
  set M := max (‖dirichletIntegral A (σ_c : ℂ)‖ + 1)
               (∫ x in Ioi 1, A x * x ^ (-(σ_c + ε / 2)))
  have h_real_bound : ∀ σ : ℝ, σ_c < σ → ∫ x in Ioi 1, A x * x ^ (-σ) ≤ M := by
    intro σ hσ
    by_cases hlt : σ < σ_c + ε
    · exact le_max_left _ _ |>.trans' (le_of_lt (h_bound σ hσ hlt))
    · push_neg at hlt
      calc ∫ x in Ioi 1, A x * x ^ (-σ)
          ≤ ∫ x in Ioi 1, A x * x ^ (-(σ_c + ε / 2)) := by
            apply integral_mono_of_nonneg
            · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
              exact mul_nonneg (hA_nonneg x hx)
                (rpow_nonneg (le_of_lt (lt_trans one_pos hx)) _)
            · exact h_integrable_real (σ_c + ε / 2) (by linarith)
            · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
              exact integrand_antitone_sigma A x (le_of_lt hx) (hA_nonneg x hx)
                σ (σ_c + ε / 2) (by linarith)
        _ ≤ M := le_max_right _ _
  -- Step 4: Apply MCT to get integrability at σ_c — contradiction
  exact h_not_integrable (integrable_at_limit_of_bounded A σ_c hA_nonneg hA_meas
    h_integrable_real M h_real_bound)

/-! ## Main construction of LandauLemmaHyp -/

/--
**Landau's Lemma**: If A(x) ≥ 0 for x > 1, A is measurable, the Dirichlet integral
∫₁^∞ A(x)x^{-s} dx converges for Re(s) > σ_c but diverges at s = σ_c (on the real axis),
then the dirichletIntegral function:
1. Is analytic for Re(s) > σ_c (given as hypothesis, from parametric integral theory)
2. Is NOT analytic at s = σ_c (proved via the MCT/blowup argument)

The `h_analytic` hypothesis follows from standard parametric integral analyticity
(differentiation under the integral sign + Cauchy integral formula). It is separated
as a hypothesis for modularity — the deep content of Landau's lemma is in the
singularity direction (`not_analytic_at`), which is proved here unconditionally.
-/
theorem landauLemmaHyp_of
    (A : ℝ → ℝ) (σ_c : ℝ)
    (hA_nonneg : ∀ x ∈ Ioi (1:ℝ), 0 ≤ A x)
    (hA_meas : Measurable A)
    -- Real integrability for σ > σ_c
    (h_integrable_real : ∀ σ : ℝ, σ_c < σ →
      Integrable (fun x => A x * x ^ (-σ)) (volume.restrict (Ioi 1)))
    -- Non-integrability at σ_c
    (h_not_integrable : ¬ Integrable
      (fun x => A x * x ^ (-σ_c)) (volume.restrict (Ioi 1)))
    -- Analyticity for Re(s) > σ_c (from parametric integral theory)
    (h_analytic : ∀ s : ℂ, σ_c < s.re → AnalyticAt ℂ (dirichletIntegral A) s) :
    LandauLemmaHyp A σ_c :=
  ⟨h_analytic,
   dirichletIntegral_not_analyticAt A σ_c hA_nonneg hA_meas
     h_not_integrable h_integrable_real⟩

end Landau
