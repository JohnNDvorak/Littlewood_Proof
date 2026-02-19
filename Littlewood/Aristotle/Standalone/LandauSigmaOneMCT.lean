import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LandauSigmaOneMCT

open Filter MeasureTheory Set

/--
Abstract Landau/MCT tail step at the boundary `σ = 1`.

For a nonnegative tail function `g`, assume a uniform bound on the family
`∫_{(T₀,∞)} g(t) t^{-(2 + 1/(n+1))} dt` as `n → ∞`. Since the exponents increase
to `-2`, monotone convergence yields integrability of `g(t) t^{-2}` on `(T₀,∞)`.
-/
theorem integrableOn_rpow_neg_two_of_dirichlet_tail_family
    (g : ℝ → ℝ)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (h_meas : Measurable g)
    (h_nonneg : ∀ t : ℝ, T₀ < t → 0 ≤ g t)
    (M : ENNReal) (hM : M ≠ ⊤)
    (h_bound : ∀ n : ℕ,
      ∫⁻ t in Ioi T₀, ENNReal.ofReal (g t * t ^ (-(2 + (1 : ℝ) / (n + 1)))) ≤ M) :
    IntegrableOn (fun t : ℝ => g t * t ^ (-(2 : ℝ))) (Ioi T₀) := by
  let μ : Measure ℝ := volume.restrict (Ioi T₀)
  let f : ℕ → ℝ → ENNReal :=
    fun n t => ENNReal.ofReal (g t * t ^ (-(2 + (1 : ℝ) / (n + 1))))
  let F : ℝ → ENNReal := fun t => ENNReal.ofReal (g t * t ^ (-(2 : ℝ)))

  have h_meas_f : ∀ n : ℕ, AEMeasurable (f n) μ := by
    intro n
    refine (Measurable.ennreal_ofReal ?_).aemeasurable
    exact h_meas.mul (measurable_id.pow_const _)

  have h_mono : ∀ᵐ t ∂μ, Monotone fun n => f n t := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    intro n m hnm
    have ht1 : 1 < t := lt_of_le_of_lt hT₀ ht
    have ht1le : (1 : ℝ) ≤ t := le_of_lt ht1
    have hg0 : 0 ≤ g t := h_nonneg t ht
    have hdiv : (1 : ℝ) / (m + 1) ≤ (1 : ℝ) / (n + 1) :=
      Nat.one_div_le_one_div (α := ℝ) hnm
    have hexp :
        -(2 + (1 : ℝ) / (n + 1)) ≤ -(2 + (1 : ℝ) / (m + 1)) := by
      linarith
    have hpow :
        t ^ (-(2 + (1 : ℝ) / (n + 1))) ≤ t ^ (-(2 + (1 : ℝ) / (m + 1))) :=
      Real.rpow_le_rpow_of_exponent_le ht1le hexp
    have hmul :
        g t * t ^ (-(2 + (1 : ℝ) / (n + 1)))
          ≤ g t * t ^ (-(2 + (1 : ℝ) / (m + 1))) :=
      mul_le_mul_of_nonneg_left hpow hg0
    exact ENNReal.ofReal_le_ofReal hmul

  have h_tendsto : ∀ᵐ t ∂μ, Tendsto (fun n => f n t) atTop (nhds (F t)) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one (lt_of_le_of_lt hT₀ ht)
    have htnz : t ≠ 0 := ne_of_gt ht0
    have h_exp :
        Tendsto (fun n : ℕ => -(2 + (1 : ℝ) / (n + 1))) atTop (nhds (-(2 : ℝ))) := by
      have h_div : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds.add h_div).neg
    have h_pow :
        Tendsto (fun n : ℕ => t ^ (-(2 + (1 : ℝ) / (n + 1)))) atTop (nhds (t ^ (-(2 : ℝ)))) := by
      exact (Real.continuousAt_const_rpow htnz).tendsto.comp h_exp
    have h_mul :
        Tendsto (fun n : ℕ => g t * t ^ (-(2 + (1 : ℝ) / (n + 1)))) atTop
          (nhds (g t * t ^ (-(2 : ℝ)))) :=
      Filter.Tendsto.const_mul (g t) h_pow
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp h_mul

  have h_int_tendsto :
      Tendsto (fun n : ℕ => ∫⁻ t, f n t ∂μ) atTop (nhds (∫⁻ t, F t ∂μ)) :=
    MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone h_meas_f h_mono h_tendsto

  have h_le_M : ∫⁻ t, F t ∂μ ≤ M := by
    refine le_of_tendsto h_int_tendsto ?_
    exact Filter.Eventually.of_forall (fun n => by
      simpa [μ, f] using h_bound n)

  have h_lintegral_lt_top : ∫⁻ t, F t ∂μ < ⊤ := by
    exact lt_of_le_of_lt h_le_M (lt_top_iff_ne_top.mpr hM)

  have h_nonneg_ae : 0 ≤ᵐ[μ] fun t : ℝ => g t * t ^ (-(2 : ℝ)) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    exact mul_nonneg (h_nonneg t ht) (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one (lt_of_le_of_lt hT₀ ht))) _)

  have h_hasFinite :
      HasFiniteIntegral (fun t : ℝ => g t * t ^ (-(2 : ℝ))) μ := by
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal h_nonneg_ae]
    simpa [F] using h_lintegral_lt_top

  have h_int : Integrable (fun t : ℝ => g t * t ^ (-(2 : ℝ))) μ := by
    refine ⟨?_, h_hasFinite⟩
    exact (h_meas.mul (measurable_id.pow_const _)).aestronglyMeasurable

  simpa [MeasureTheory.IntegrableOn, μ] using h_int

end Aristotle.Standalone.LandauSigmaOneMCT
