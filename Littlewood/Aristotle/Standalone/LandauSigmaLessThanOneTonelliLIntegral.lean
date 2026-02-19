import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LandauSigmaLessThanOneTonelliLIntegral

open MeasureTheory Set

/--
Tonelli/Fubini majorant step in `lintegral` form for Landau's `σ₀ < 1` branch.

Assume:
1. a pointwise tail majorant by a nonnegative series
   `‖g(t)t^{-(σ₀+1)}‖ ≤ ∑' k term k t` on `t > T₀`;
2. measurability of each `term k`.

Then, on each partial interval `(T₀, T₀+N]`, the lintegral of the Landau
integrand is bounded by the tsum of global tail lintegrals of the coefficients.

This isolates the Tonelli interchange + set-monotonicity step used in the
`σ₀ < 1` proof skeleton.
-/
theorem partial_lintegral_le_tsum_tail_coeffs
    (g : ℝ → ℝ) (T₀ σ₀ : ℝ)
    (term : ℕ → ℝ → ℝ)
    (hterm_meas : ∀ k : ℕ, Measurable (term k))
    (hmajorant : ∀ t : ℝ, t ∈ Ioi T₀ →
      ENNReal.ofReal ‖g t * t ^ (-(σ₀ + 1))‖ ≤
        ∑' k : ℕ, ENNReal.ofReal (term k t)) :
    ∀ N : ℕ,
      ∫⁻ t in Ioc T₀ (T₀ + (N : ℝ)),
        ENNReal.ofReal ‖g t * t ^ (-(σ₀ + 1))‖
        ≤
      ∑' k : ℕ, ∫⁻ t in Ioi T₀, ENNReal.ofReal (term k t) := by
  intro N
  have hsubset : Ioc T₀ (T₀ + (N : ℝ)) ⊆ Ioi T₀ := by
    intro t ht
    exact ht.1

  have hstep1 :
      ∫⁻ t in Ioc T₀ (T₀ + (N : ℝ)),
        ENNReal.ofReal ‖g t * t ^ (-(σ₀ + 1))‖
        ≤
      ∫⁻ t in Ioc T₀ (T₀ + (N : ℝ)),
        (∑' k : ℕ, ENNReal.ofReal (term k t)) := by
    refine lintegral_mono_ae ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono ?_
    intro t ht
    exact hmajorant t (hsubset ht)

  have hstep2 :
      ∫⁻ t in Ioc T₀ (T₀ + (N : ℝ)),
        (∑' k : ℕ, ENNReal.ofReal (term k t))
        =
      ∑' k : ℕ, ∫⁻ t in Ioc T₀ (T₀ + (N : ℝ)), ENNReal.ofReal (term k t) := by
    rw [lintegral_tsum]
    intro k
    exact (Measurable.ennreal_ofReal (hterm_meas k)).aemeasurable

  have hstep3 :
      (∑' k : ℕ, ∫⁻ t in Ioc T₀ (T₀ + (N : ℝ)), ENNReal.ofReal (term k t))
        ≤
      (∑' k : ℕ, ∫⁻ t in Ioi T₀, ENNReal.ofReal (term k t)) := by
    apply ENNReal.tsum_le_tsum
    intro k
    exact lintegral_mono_set hsubset

  exact hstep1.trans (by simpa [hstep2] using hstep3)

/--
Real-valued version of `partial_lintegral_le_tsum_tail_coeffs`.

Assume additionally that the relevant integrals are finite:
- `‖g(t)t^{-(σ₀+1)}‖` is integrable on each partial interval `(T₀, T₀+N]`;
- each coefficient profile `term k` is integrable on the full tail `(T₀, ∞)`.

Then each partial interval integral is bounded by the global Taylor/anti-coefficient
majorant in real form.
-/
theorem partial_integral_le_tsum_tail_coeffs
    (g : ℝ → ℝ) (T₀ σ₀ : ℝ)
    (term : ℕ → ℝ → ℝ)
    (hterm_meas : ∀ k : ℕ, Measurable (term k))
    (hterm_nonneg : ∀ k : ℕ, ∀ t : ℝ, t ∈ Ioi T₀ → 0 ≤ term k t)
    (hmajorant : ∀ t : ℝ, t ∈ Ioi T₀ →
      ENNReal.ofReal ‖g t * t ^ (-(σ₀ + 1))‖ ≤
        ∑' k : ℕ, ENNReal.ofReal (term k t))
    (hmain_int : ∀ N : ℕ,
      IntegrableOn (fun t : ℝ => ‖g t * t ^ (-(σ₀ + 1))‖) (Ioc T₀ (T₀ + (N : ℝ))))
    (hterm_int : ∀ k : ℕ, IntegrableOn (term k) (Ioi T₀))
    (hsum : Summable (fun k : ℕ => ∫ t in Ioi T₀, term k t)) :
    ∀ N : ℕ,
      ∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖
        ≤
      ∑' k : ℕ, ∫ t in Ioi T₀, term k t := by
  intro N
  have hlin :=
    partial_lintegral_le_tsum_tail_coeffs g T₀ σ₀ term hterm_meas hmajorant N

  have hmain_nonneg :
      0 ≤ᵐ[volume.restrict (Ioc T₀ (T₀ + (N : ℝ)))] fun t : ℝ =>
        ‖g t * t ^ (-(σ₀ + 1))‖ := by
    exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)

  have hleft :
      ENNReal.ofReal
          (∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖)
        =
      ∫⁻ t in Ioc T₀ (T₀ + (N : ℝ)),
        ENNReal.ofReal ‖g t * t ^ (-(σ₀ + 1))‖ := by
    simpa using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := volume.restrict (Ioc T₀ (T₀ + (N : ℝ))))
        (f := fun t : ℝ => ‖g t * t ^ (-(σ₀ + 1))‖)
        (hmain_int N)
        hmain_nonneg)

  have hterm_nonneg_ae :
      ∀ k : ℕ, 0 ≤ᵐ[volume.restrict (Ioi T₀)] fun t : ℝ => term k t := by
    intro k
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    exact hterm_nonneg k t ht

  have hterm_integral_nonneg :
      ∀ k : ℕ, 0 ≤ ∫ t in Ioi T₀, term k t := by
    intro k
    exact MeasureTheory.integral_nonneg_of_ae (hterm_nonneg_ae k)

  have hright_k :
      ∀ k : ℕ,
        ENNReal.ofReal (∫ t in Ioi T₀, term k t)
          =
        ∫⁻ t in Ioi T₀, ENNReal.ofReal (term k t) := by
    intro k
    simpa using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := volume.restrict (Ioi T₀))
        (f := term k)
        (hterm_int k)
        (hterm_nonneg_ae k))

  have hright :
      ENNReal.ofReal (∑' k : ℕ, ∫ t in Ioi T₀, term k t)
        =
      ∑' k : ℕ, ∫⁻ t in Ioi T₀, ENNReal.ofReal (term k t) := by
    calc
      ENNReal.ofReal (∑' k : ℕ, ∫ t in Ioi T₀, term k t)
          = ∑' k : ℕ, ENNReal.ofReal (∫ t in Ioi T₀, term k t) := by
              exact ENNReal.ofReal_tsum_of_nonneg hterm_integral_nonneg hsum
      _ = ∑' k : ℕ, ∫⁻ t in Ioi T₀, ENNReal.ofReal (term k t) := by
            congr 1
            ext k
            exact hright_k k

  have henn :
      ENNReal.ofReal
        (∫ t in Ioc T₀ (T₀ + (N : ℝ)), ‖g t * t ^ (-(σ₀ + 1))‖)
        ≤
      ENNReal.ofReal (∑' k : ℕ, ∫ t in Ioi T₀, term k t) := by
    rw [hleft, hright]
    exact hlin

  have hsum_nonneg : 0 ≤ ∑' k : ℕ, ∫ t in Ioi T₀, term k t :=
    tsum_nonneg hterm_integral_nonneg
  exact (ENNReal.ofReal_le_ofReal_iff hsum_nonneg).1 henn

end Aristotle.Standalone.LandauSigmaLessThanOneTonelliLIntegral
