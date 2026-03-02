import Littlewood.Aristotle.Standalone.RHPiTargetPhaseArgReduction
import Littlewood.Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
import Littlewood.Aristotle.Standalone.RHPiWitnessFromExplicitFormula

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiInhomogeneousApproxObstruction

open scoped BigOperators
open Complex ZetaZeros
open Aristotle.Standalone.RHPiTargetPhaseArgReduction
open Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
open Aristotle.Standalone.RHPiWitnessFromExplicitFormula

/--
Necessary compatibility condition for one-parameter inhomogeneous phase fitting
on a finite family.

If `t * γᵢ` approximates `φᵢ` modulo `2π` with error `ε` for all `i`, then every
integer relation `∑ mᵢ γᵢ = 0` forces an approximate congruence
`∑ mᵢ φᵢ ≈ 0 (mod 2π)` with a quantitative loss `ε * ∑ |mᵢ|`.
-/
theorem inhomogeneous_one_param_compatibility_necessary
    {ι : Type*} [Fintype ι]
    {γ φ : ι → ℝ} {t ε : ℝ}
    (hApprox :
      ∀ i : ι, ∃ k : ℤ,
        ‖t * γ i - φ i - (k : ℝ) * (2 * Real.pi)‖ ≤ ε)
    {m : ι → ℤ}
    (hRel : (∑ i, (m i : ℝ) * γ i) = 0) :
    ∃ k : ℤ,
      ‖(∑ i, (m i : ℝ) * φ i) + (k : ℝ) * (2 * Real.pi)‖
        ≤ ε * (∑ i, |(m i : ℝ)|) := by
  classical
  let kFun : ι → ℤ := fun i => Classical.choose (hApprox i)
  have hkFun :
      ∀ i : ι,
        ‖t * γ i - φ i - (kFun i : ℝ) * (2 * Real.pi)‖ ≤ ε := by
    intro i
    exact Classical.choose_spec (hApprox i)
  let k : ℤ := ∑ i, m i * kFun i
  refine ⟨k, ?_⟩

  let err : ι → ℝ := fun i => t * γ i - φ i - (kFun i : ℝ) * (2 * Real.pi)

  have hkReal :
      (k : ℝ) = ∑ i, (m i : ℝ) * (kFun i : ℝ) := by
    simp [k, Int.cast_sum, Int.cast_mul]

  have hkTerm :
      (k : ℝ) * (2 * Real.pi)
        = ∑ i, (m i : ℝ) * ((kFun i : ℝ) * (2 * Real.pi)) := by
    calc
      (k : ℝ) * (2 * Real.pi)
          = (∑ i, (m i : ℝ) * (kFun i : ℝ)) * (2 * Real.pi) := by rw [hkReal]
      _ = ∑ i, ((m i : ℝ) * (kFun i : ℝ)) * (2 * Real.pi) := by rw [Finset.sum_mul]
      _ = ∑ i, (m i : ℝ) * ((kFun i : ℝ) * (2 * Real.pi)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring

  have hExpr1 :
      (∑ i, (m i : ℝ) * φ i) + (k : ℝ) * (2 * Real.pi)
        = ∑ i, (m i : ℝ) * (φ i + (kFun i : ℝ) * (2 * Real.pi)) := by
    calc
      (∑ i, (m i : ℝ) * φ i) + (k : ℝ) * (2 * Real.pi)
          = (∑ i, (m i : ℝ) * φ i) +
              (∑ i, (m i : ℝ) * ((kFun i : ℝ) * (2 * Real.pi))) := by
                rw [hkTerm]
      _ = ∑ i, ((m i : ℝ) * φ i + (m i : ℝ) * ((kFun i : ℝ) * (2 * Real.pi))) := by
            rw [← Finset.sum_add_distrib]
      _ = ∑ i, (m i : ℝ) * (φ i + (kFun i : ℝ) * (2 * Real.pi)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring

  have hPoint :
      ∀ i : ι,
        φ i + (kFun i : ℝ) * (2 * Real.pi) = t * γ i - err i := by
    intro i
    simp [err]
    ring

  have hExpr2 :
      ∑ i, (m i : ℝ) * (φ i + (kFun i : ℝ) * (2 * Real.pi))
        = ∑ i, (m i : ℝ) * (t * γ i - err i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hPoint]

  have hExpr3 :
      ∑ i, (m i : ℝ) * (t * γ i - err i)
        = (∑ i, (m i : ℝ) * (t * γ i)) - ∑ i, (m i : ℝ) * err i := by
    calc
      ∑ i, (m i : ℝ) * (t * γ i - err i)
          = ∑ i, (((m i : ℝ) * (t * γ i)) - ((m i : ℝ) * err i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = (∑ i, (m i : ℝ) * (t * γ i)) - ∑ i, (m i : ℝ) * err i := by
            rw [Finset.sum_sub_distrib]

  have hExpr4 :
      (∑ i, (m i : ℝ) * (t * γ i)) = t * (∑ i, (m i : ℝ) * γ i) := by
    calc
      (∑ i, (m i : ℝ) * (t * γ i))
          = ∑ i, t * ((m i : ℝ) * γ i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = t * (∑ i, (m i : ℝ) * γ i) := by rw [← Finset.mul_sum]

  have hCollapse :
      (∑ i, (m i : ℝ) * φ i) + (k : ℝ) * (2 * Real.pi)
        = -(∑ i, (m i : ℝ) * err i) := by
    calc
      (∑ i, (m i : ℝ) * φ i) + (k : ℝ) * (2 * Real.pi)
          = ∑ i, (m i : ℝ) * (φ i + (kFun i : ℝ) * (2 * Real.pi)) := hExpr1
      _ = ∑ i, (m i : ℝ) * (t * γ i - err i) := hExpr2
      _ = (∑ i, (m i : ℝ) * (t * γ i)) - ∑ i, (m i : ℝ) * err i := hExpr3
      _ = t * (∑ i, (m i : ℝ) * γ i) - ∑ i, (m i : ℝ) * err i := by rw [hExpr4]
      _ = -(∑ i, (m i : ℝ) * err i) := by simp [hRel]

  have hTermBound :
      ∀ i : ι, ‖(m i : ℝ) * err i‖ ≤ |(m i : ℝ)| * ε := by
    intro i
    have hi : ‖err i‖ ≤ ε := by
      simpa [err] using hkFun i
    calc
      ‖(m i : ℝ) * err i‖ = |(m i : ℝ)| * ‖err i‖ := by
            simp [Real.norm_eq_abs, norm_mul]
      _ ≤ |(m i : ℝ)| * ε := mul_le_mul_of_nonneg_left hi (abs_nonneg _)

  have hSumBound :
      ‖∑ i, (m i : ℝ) * err i‖ ≤ ∑ i, |(m i : ℝ)| * ε := by
    calc
      ‖∑ i, (m i : ℝ) * err i‖ ≤ ∑ i, ‖(m i : ℝ) * err i‖ := norm_sum_le _ _
      _ ≤ ∑ i, |(m i : ℝ)| * ε := Finset.sum_le_sum (fun i hi => hTermBound i)

  have hSumRewrite :
      (∑ i, |(m i : ℝ)| * ε) = ε * (∑ i, |(m i : ℝ)|) := by
    calc
      (∑ i, |(m i : ℝ)| * ε) = ∑ i, ε * |(m i : ℝ)| := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = ε * (∑ i, |(m i : ℝ)|) := by rw [Finset.mul_sum]

  calc
    ‖(∑ i, (m i : ℝ) * φ i) + (k : ℝ) * (2 * Real.pi)‖
        = ‖-(∑ i, (m i : ℝ) * err i)‖ := by rw [hCollapse]
    _ = ‖∑ i, (m i : ℝ) * err i‖ := by simp
    _ ≤ ∑ i, |(m i : ℝ)| * ε := hSumBound
    _ = ε * (∑ i, |(m i : ℝ)|) := hSumRewrite

/--
`TargetTowerArgApproxFamily` implies a quantitative compatibility condition for
any integer relation among the ordinates in the selected finite zero set.

This records a necessary consistency property of the inhomogeneous target phases
inside the current RH-`pi` arg-approximation payload.
-/
theorem targetTowerArgApproxFamily_implies_relation_compatibility
    (hTargetArg : TargetTowerArgApproxFamily) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ x T ε : ℝ,
      X < x ∧
      4 ≤ T ∧
      1 < x ∧
      0 < ε ∧ ε < 1 ∧
      (∀ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
        (∑ i, (m i : ℝ) * i.1.im = 0) →
        ∃ k : ℤ,
          ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖
            ≤ ε * (∑ i, |(m i : ℝ)|)) := by
  intro hRH X
  rcases hTargetArg hRH X with
    ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, harg, hxUpper⟩
  refine ⟨x, T, ε, hXx, hT4, hx1, hεpos, hεlt, ?_⟩
  intro m hRel
  let S : Finset ℂ := (finite_zeros_le T).toFinset
  let γ : {ρ // ρ ∈ S} → ℝ := fun i => i.1.im
  let φ : {ρ // ρ ∈ S} → ℝ := fun i => Complex.arg i.1
  have hApprox :
      ∀ i : {ρ // ρ ∈ S}, ∃ k : ℤ,
        ‖Real.log x * γ i - φ i - (k : ℝ) * (2 * Real.pi)‖ ≤ ε := by
    intro i
    simpa [S, γ, φ] using harg i.1 i.2
  have hRel' : (∑ i, (m i : ℝ) * γ i) = 0 := by
    simpa [γ] using hRel
  rcases inhomogeneous_one_param_compatibility_necessary
      (γ := γ) (φ := φ) (t := Real.log x) (ε := ε)
      hApprox (m := m) hRel' with
    ⟨k, hk⟩
  exact ⟨k, by simpa [S, γ, φ] using hk⟩

/--
`AntiTargetTowerArgApproxFamily` implies the analogous quantitative
compatibility condition for integer relations among the selected zero ordinates,
with phase targets shifted by `π`.

This is the anti-target counterpart of
`targetTowerArgApproxFamily_implies_relation_compatibility`.
-/
theorem antiTargetTowerArgApproxFamily_implies_relation_compatibility
    (hAntiTargetArg : AntiTargetTowerArgApproxFamily) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ x T ε : ℝ,
      X < x ∧
      4 ≤ T ∧
      1 < x ∧
      0 < ε ∧ ε < 1 ∧
      (∀ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
        (∑ i, (m i : ℝ) * i.1.im = 0) →
        ∃ k : ℤ,
          ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) + (k : ℝ) * (2 * Real.pi)‖
            ≤ ε * (∑ i, |(m i : ℝ)|)) := by
  intro hRH X
  rcases hAntiTargetArg hRH X with
    ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, harg, hxUpper⟩
  refine ⟨x, T, ε, hXx, hT4, hx1, hεpos, hεlt, ?_⟩
  intro m hRel
  let S : Finset ℂ := (finite_zeros_le T).toFinset
  let γ : {ρ // ρ ∈ S} → ℝ := fun i => i.1.im
  let φ : {ρ // ρ ∈ S} → ℝ := fun i => Complex.arg i.1 + Real.pi
  have hApprox :
      ∀ i : {ρ // ρ ∈ S}, ∃ k : ℤ,
        ‖Real.log x * γ i - φ i - (k : ℝ) * (2 * Real.pi)‖ ≤ ε := by
    intro i
    simpa [S, γ, φ] using harg i.1 i.2
  have hRel' : (∑ i, (m i : ℝ) * γ i) = 0 := by
    simpa [γ] using hRel
  rcases inhomogeneous_one_param_compatibility_necessary
      (γ := γ) (φ := φ) (t := Real.log x) (ε := ε)
      hApprox (m := m) hRel' with
    ⟨k, hk⟩
  exact ⟨k, by simpa [S, γ, φ] using hk⟩

/--
Convert target phase-closeness at a finite-zero point into an argument-congruence
bound with explicit linear loss `π/2`.
-/
lemma exists_int_arg_bound_of_target_phase_close
    {x ε : ℝ} (hx : 1 < x) (hεlt : ε < 1)
    {ρ : ℂ}
    (hphase : ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) :
    ∃ k : ℤ,
      ‖Real.log x * ρ.im - Complex.arg ρ - (k : ℝ) * (2 * Real.pi)‖
        ≤ (Real.pi / 2) * ε := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hρne : ρ ≠ 0 := by
    intro h0
    have hpow : (x : ℂ) ^ (Complex.I * ρ.im) = 1 := by simp [h0]
    have htarget0 : ρ / ‖ρ‖ = 0 := by simp [h0]
    have hnorm1 : ‖(1 : ℂ) - 0‖ ≤ ε := by
      simpa [hpow, htarget0] using hphase
    have h1le : (1 : ℝ) ≤ ε := by simpa using hnorm1
    exact (not_le_of_gt hεlt) h1le

  have hcpow :
      (x : ℂ) ^ (Complex.I * ρ.im)
        = Complex.exp ((Real.log x * ρ.im) * Complex.I) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (cpow_I_im_eq_exp_I_log_mul (x := x) (y := ρ.im) hx_pos)
  have hunit : ρ / ‖ρ‖ = Complex.exp (Complex.arg ρ * Complex.I) :=
    unit_dir_eq_exp_arg hρne

  let θ : ℝ := Real.log x * ρ.im
  let φ : ℝ := Complex.arg ρ
  have hcloseExp :
      ‖Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)‖ ≤ ε := by
    simpa [θ, φ, hcpow, hunit]
      using hphase

  have hmul :
      Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)
        = Complex.exp (φ * Complex.I) *
            (Complex.exp ((θ - φ) * Complex.I) - 1) := by
    calc
      Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)
          = Complex.exp ((φ + (θ - φ)) * Complex.I) - Complex.exp (φ * Complex.I) := by
              congr 1
              ring
      _ = Complex.exp (φ * Complex.I + (θ - φ) * Complex.I) - Complex.exp (φ * Complex.I) := by
            congr 1
            ring
      _ = Complex.exp (φ * Complex.I) * Complex.exp ((θ - φ) * Complex.I)
            - Complex.exp (φ * Complex.I) := by rw [Complex.exp_add]
      _ = Complex.exp (φ * Complex.I) *
            (Complex.exp ((θ - φ) * Complex.I) - 1) := by ring
  have hcloseOne :
      ‖Complex.exp (Complex.I * (θ - φ)) - 1‖ ≤ ε := by
    have hmul_le :
        ‖Complex.exp (φ * Complex.I) *
            (Complex.exp ((θ - φ) * Complex.I) - 1)‖ ≤ ε := by
      simpa [hmul] using hcloseExp
    have hcloseOne' :
        ‖Complex.exp ((θ - φ) * Complex.I) - 1‖ ≤ ε := by
      simpa [norm_mul, Complex.norm_exp_I_mul_ofReal] using hmul_le
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcloseOne'

  rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos (θ - φ) (-Real.pi) with
    ⟨n, hnIoc, -⟩
  let δ : ℝ := (θ - φ) + (n : ℤ) • (2 * Real.pi)
  have hδIoc : δ ∈ Set.Ioc (-Real.pi) Real.pi := by
    have htmp : δ ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      simpa [δ] using hnIoc
    refine ⟨htmp.1, ?_⟩
    linarith [htmp.2]
  have hδ_abs_le_pi : |δ| ≤ Real.pi := by
    exact abs_le.2 ⟨hδIoc.1.le, hδIoc.2⟩
  have hδ_half_nonneg : 0 ≤ |δ| / 2 := by positivity
  have hδ_half_le : |δ| / 2 ≤ Real.pi / 2 := by
    nlinarith [hδ_abs_le_pi]
  have hsin_lower : (2 / Real.pi) * (|δ| / 2) ≤ Real.sin (|δ| / 2) :=
    Real.mul_le_sin hδ_half_nonneg hδ_half_le

  have hperiod :
      Complex.exp (Complex.I * δ) = Complex.exp (Complex.I * (θ - φ)) := by
    have hperiod' :
        Complex.exp ((((θ - φ : ℝ) : ℂ) - ((-n : ℤ) • (2 * (Real.pi : ℂ)))) * Complex.I)
          = Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I) := by
      simpa using
        (Complex.exp_mul_I_periodic.sub_zsmul_eq (x := ((θ - φ : ℂ))) (n := (-n)))
    have hδ_as_sub :
        ((δ : ℝ) : ℂ) = ((θ - φ : ℝ) : ℂ) - ((-n : ℤ) • (2 * (Real.pi : ℂ))) := by
      simp [δ]
    have hperiod'' :
        Complex.exp (((δ : ℝ) : ℂ) * Complex.I)
          = Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I) := by
      simpa [hδ_as_sub] using hperiod'
    simpa [mul_comm, mul_left_comm, mul_assoc] using hperiod''
  have hcloseδ :
      ‖Complex.exp (Complex.I * δ) - 1‖ ≤ ε := by
    simpa [hperiod] using hcloseOne
  have hnorm_sin :
      ‖2 * Real.sin (δ / 2)‖ ≤ ε := by
    simpa [Complex.norm_exp_I_mul_ofReal_sub_one] using hcloseδ
  have hsin_abs_le : |Real.sin (δ / 2)| ≤ ε / 2 := by
    have hnorm_sin' : |2 * Real.sin (δ / 2)| ≤ ε := by simpa [Real.norm_eq_abs] using hnorm_sin
    have htwo_pos : (0 : ℝ) < 2 := by positivity
    have htmp : 2 * |Real.sin (δ / 2)| ≤ ε := by
      simpa [abs_mul, abs_of_pos htwo_pos, mul_comm, mul_left_comm, mul_assoc] using hnorm_sin'
    nlinarith
  have hsin_abs_eq :
      |Real.sin (δ / 2)| = Real.sin (|δ| / 2) := by
    have h_abs_arg : |δ / 2| ≤ Real.pi := by
      calc
        |δ / 2| = |δ| / 2 := by simp [abs_div]
        _ ≤ Real.pi / 2 := hδ_half_le
        _ ≤ Real.pi := by nlinarith [Real.pi_pos]
    simpa [abs_div] using
      (Real.abs_sin_eq_sin_abs_of_abs_le_pi (x := δ / 2) h_abs_arg)

  have hδ_over_pi_le : |δ| / Real.pi ≤ ε / 2 := by
    have hrewrite : |δ| / Real.pi = (2 / Real.pi) * (|δ| / 2) := by
      field_simp [Real.pi_ne_zero]
    calc
      |δ| / Real.pi = (2 / Real.pi) * (|δ| / 2) := hrewrite
      _ ≤ Real.sin (|δ| / 2) := hsin_lower
      _ = |Real.sin (δ / 2)| := by rw [hsin_abs_eq]
      _ ≤ ε / 2 := hsin_abs_le
  have hδ_bound : |δ| ≤ (Real.pi / 2) * ε := by
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hmul := (mul_le_mul_iff_of_pos_left hpi_pos).2 hδ_over_pi_le
    have hL : Real.pi * (|δ| / Real.pi) = |δ| := by
      field_simp [Real.pi_ne_zero]
    have hR : Real.pi * (ε / 2) = (Real.pi / 2) * ε := by ring
    simpa [hL, hR] using hmul
  refine ⟨-n, ?_⟩
  have hδ_rewrite :
      δ = (Real.log x * ρ.im - Complex.arg ρ) - ((-n : ℤ) : ℝ) * (2 * Real.pi) := by
    simp [δ]
    ring
  calc
    ‖Real.log x * ρ.im - Complex.arg ρ - ((-n : ℤ) : ℝ) * (2 * Real.pi)‖
        = ‖δ‖ := by rw [hδ_rewrite]
    _ = |δ| := by simp [Real.norm_eq_abs]
    _ ≤ (Real.pi / 2) * ε := hδ_bound

private lemma exists_int_arg_bound_from_exp_close
    {θ φ ε : ℝ}
    (hcloseExp :
      ‖Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)‖ ≤ ε) :
    ∃ k : ℤ,
      ‖θ - φ - (k : ℝ) * (2 * Real.pi)‖ ≤ (Real.pi / 2) * ε := by
  have hmul :
      Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)
        = Complex.exp (φ * Complex.I) *
            (Complex.exp ((θ - φ) * Complex.I) - 1) := by
    calc
      Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)
          = Complex.exp ((φ + (θ - φ)) * Complex.I) - Complex.exp (φ * Complex.I) := by
              congr 1
              ring
      _ = Complex.exp (φ * Complex.I + (θ - φ) * Complex.I) - Complex.exp (φ * Complex.I) := by
            congr 1
            ring
      _ = Complex.exp (φ * Complex.I) * Complex.exp ((θ - φ) * Complex.I)
            - Complex.exp (φ * Complex.I) := by rw [Complex.exp_add]
      _ = Complex.exp (φ * Complex.I) *
            (Complex.exp ((θ - φ) * Complex.I) - 1) := by ring
  have hcloseOne :
      ‖Complex.exp (Complex.I * (θ - φ)) - 1‖ ≤ ε := by
    have hmul_le :
        ‖Complex.exp (φ * Complex.I) *
            (Complex.exp ((θ - φ) * Complex.I) - 1)‖ ≤ ε := by
      simpa [hmul] using hcloseExp
    have hcloseOne' :
        ‖Complex.exp ((θ - φ) * Complex.I) - 1‖ ≤ ε := by
      simpa [norm_mul, Complex.norm_exp_I_mul_ofReal] using hmul_le
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcloseOne'

  rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos (θ - φ) (-Real.pi) with
    ⟨n, hnIoc, -⟩
  let δ : ℝ := (θ - φ) + (n : ℤ) • (2 * Real.pi)
  have hδIoc : δ ∈ Set.Ioc (-Real.pi) Real.pi := by
    have htmp : δ ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      simpa [δ] using hnIoc
    refine ⟨htmp.1, ?_⟩
    linarith [htmp.2]
  have hδ_abs_le_pi : |δ| ≤ Real.pi := by
    exact abs_le.2 ⟨hδIoc.1.le, hδIoc.2⟩
  have hδ_half_nonneg : 0 ≤ |δ| / 2 := by positivity
  have hδ_half_le : |δ| / 2 ≤ Real.pi / 2 := by
    nlinarith [hδ_abs_le_pi]
  have hsin_lower : (2 / Real.pi) * (|δ| / 2) ≤ Real.sin (|δ| / 2) :=
    Real.mul_le_sin hδ_half_nonneg hδ_half_le

  have hperiod :
      Complex.exp (Complex.I * δ) = Complex.exp (Complex.I * (θ - φ)) := by
    have hperiod' :
        Complex.exp ((((θ - φ : ℝ) : ℂ) - ((-n : ℤ) • (2 * (Real.pi : ℂ)))) * Complex.I)
          = Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I) := by
      simpa using
        (Complex.exp_mul_I_periodic.sub_zsmul_eq (x := ((θ - φ : ℂ))) (n := (-n)))
    have hδ_as_sub :
        ((δ : ℝ) : ℂ) = ((θ - φ : ℝ) : ℂ) - ((-n : ℤ) • (2 * (Real.pi : ℂ))) := by
      simp [δ]
    have hperiod'' :
        Complex.exp (((δ : ℝ) : ℂ) * Complex.I)
          = Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I) := by
      simpa [hδ_as_sub] using hperiod'
    simpa [mul_comm, mul_left_comm, mul_assoc] using hperiod''
  have hcloseδ :
      ‖Complex.exp (Complex.I * δ) - 1‖ ≤ ε := by
    simpa [hperiod] using hcloseOne
  have hnorm_sin :
      ‖2 * Real.sin (δ / 2)‖ ≤ ε := by
    simpa [Complex.norm_exp_I_mul_ofReal_sub_one] using hcloseδ
  have hsin_abs_le : |Real.sin (δ / 2)| ≤ ε / 2 := by
    have hnorm_sin' : |2 * Real.sin (δ / 2)| ≤ ε := by simpa [Real.norm_eq_abs] using hnorm_sin
    have htwo_pos : (0 : ℝ) < 2 := by positivity
    have htmp : 2 * |Real.sin (δ / 2)| ≤ ε := by
      simpa [abs_mul, abs_of_pos htwo_pos, mul_comm, mul_left_comm, mul_assoc] using hnorm_sin'
    nlinarith
  have hsin_abs_eq :
      |Real.sin (δ / 2)| = Real.sin (|δ| / 2) := by
    have h_abs_arg : |δ / 2| ≤ Real.pi := by
      calc
        |δ / 2| = |δ| / 2 := by simp [abs_div]
        _ ≤ Real.pi / 2 := hδ_half_le
        _ ≤ Real.pi := by nlinarith [Real.pi_pos]
    simpa [abs_div] using
      (Real.abs_sin_eq_sin_abs_of_abs_le_pi (x := δ / 2) h_abs_arg)

  have hδ_over_pi_le : |δ| / Real.pi ≤ ε / 2 := by
    have hrewrite : |δ| / Real.pi = (2 / Real.pi) * (|δ| / 2) := by
      field_simp [Real.pi_ne_zero]
    calc
      |δ| / Real.pi = (2 / Real.pi) * (|δ| / 2) := hrewrite
      _ ≤ Real.sin (|δ| / 2) := hsin_lower
      _ = |Real.sin (δ / 2)| := by rw [hsin_abs_eq]
      _ ≤ ε / 2 := hsin_abs_le
  have hδ_bound : |δ| ≤ (Real.pi / 2) * ε := by
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hmul := (mul_le_mul_iff_of_pos_left hpi_pos).2 hδ_over_pi_le
    have hL : Real.pi * (|δ| / Real.pi) = |δ| := by
      field_simp [Real.pi_ne_zero]
    have hR : Real.pi * (ε / 2) = (Real.pi / 2) * ε := by ring
    simpa [hL, hR] using hmul
  refine ⟨-n, ?_⟩
  have hδ_rewrite :
      δ = (θ - φ) - ((-n : ℤ) : ℝ) * (2 * Real.pi) := by
    simp [δ]
  calc
    ‖θ - φ - ((-n : ℤ) : ℝ) * (2 * Real.pi)‖
        = ‖δ‖ := by rw [hδ_rewrite]
    _ = |δ| := by simp [Real.norm_eq_abs]
    _ ≤ (Real.pi / 2) * ε := hδ_bound

/--
Convert anti-target phase-closeness at a finite-zero point into an
argument-congruence bound with explicit linear loss `π/2`.
-/
lemma exists_int_arg_bound_of_antitarget_phase_close
    {x ε : ℝ} (hx : 1 < x) (hεlt : ε < 1)
    {ρ : ℂ}
    (hphase : ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) :
    ∃ k : ℤ,
      ‖Real.log x * ρ.im - (Complex.arg ρ + Real.pi) - (k : ℝ) * (2 * Real.pi)‖
        ≤ (Real.pi / 2) * ε := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hρne : ρ ≠ 0 := by
    intro h0
    have hpow : (x : ℂ) ^ (Complex.I * ρ.im) = 1 := by simp [h0]
    have htarget0 : (-(ρ / ‖ρ‖)) = 0 := by simp [h0]
    have hnorm1 : ‖(1 : ℂ) - 0‖ ≤ ε := by
      simpa [hpow, htarget0] using hphase
    have h1le : (1 : ℝ) ≤ ε := by simpa using hnorm1
    exact (not_le_of_gt hεlt) h1le
  have hcpow :
      (x : ℂ) ^ (Complex.I * ρ.im)
        = Complex.exp ((Real.log x * ρ.im) * Complex.I) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (cpow_I_im_eq_exp_I_log_mul (x := x) (y := ρ.im) hx_pos)
  have hunit : (-(ρ / ‖ρ‖)) = Complex.exp ((Complex.arg ρ + Real.pi) * Complex.I) := by
    exact neg_unit_dir_eq_exp_arg_add_pi hρne
  have hcloseExp :
      ‖Complex.exp ((Real.log x * ρ.im) * Complex.I) -
          Complex.exp ((Complex.arg ρ + Real.pi) * Complex.I)‖ ≤ ε := by
    simpa [hcpow, hunit] using hphase
  have hcloseExp' :
      ‖Complex.exp (((Real.log x * ρ.im : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((Complex.arg ρ + Real.pi : ℝ) : ℂ) * Complex.I)‖ ≤ ε := by
    simpa [mul_assoc] using hcloseExp
  rcases exists_int_arg_bound_from_exp_close
      (θ := Real.log x * ρ.im)
      (φ := Complex.arg ρ + Real.pi)
      (ε := ε) hcloseExp' with
    ⟨k, hk⟩
  exact ⟨k, hk⟩

/--
Target phase-coupling family implies a quantitative relation-compatibility
condition with explicit loss `(π/2)·ε`.
-/
theorem targetTowerPhaseCouplingFamily_implies_relation_compatibility_piOverTwo
    (hTargetPhase : TargetTowerPhaseCouplingFamily) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ x T ε : ℝ,
      X < x ∧
      4 ≤ T ∧
      1 < x ∧
      0 < ε ∧ ε < 1 ∧
      (∀ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
        (∑ i, (m i : ℝ) * i.1.im = 0) →
        ∃ k : ℤ,
          ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖
            ≤ ((Real.pi / 2) * ε) * (∑ i, |(m i : ℝ)|)) := by
  intro hRH X
  rcases hTargetPhase hRH X with
    ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hxUpper⟩
  refine ⟨x, T, ε, hXx, hT4, hx1, hεpos, hεlt, ?_⟩
  intro m hRel
  let S : Finset ℂ := (finite_zeros_le T).toFinset
  let γ : {ρ // ρ ∈ S} → ℝ := fun i => i.1.im
  let φ : {ρ // ρ ∈ S} → ℝ := fun i => Complex.arg i.1
  have hApprox :
      ∀ i : {ρ // ρ ∈ S}, ∃ k : ℤ,
        ‖Real.log x * γ i - φ i - (k : ℝ) * (2 * Real.pi)‖ ≤ (Real.pi / 2) * ε := by
    intro i
    simpa [S, γ, φ] using
      exists_int_arg_bound_of_target_phase_close (x := x) (ε := ε)
        hx1 hεlt (hphase i.1 i.2)
  have hRel' : (∑ i, (m i : ℝ) * γ i) = 0 := by
    simpa [γ] using hRel
  rcases inhomogeneous_one_param_compatibility_necessary
      (γ := γ) (φ := φ) (t := Real.log x) (ε := (Real.pi / 2) * ε)
      hApprox (m := m) hRel' with
    ⟨k, hk⟩
  exact ⟨k, by simpa [S, γ, φ, mul_assoc, mul_left_comm, mul_comm] using hk⟩

/--
Anti-target phase-coupling family implies the analogous quantitative relation
compatibility with the same `(π/2)·ε` loss and shifted targets `arg + π`.
-/
theorem antiTargetTowerPhaseCouplingFamily_implies_relation_compatibility_piOverTwo
    (hAntiTargetPhase : AntiTargetTowerPhaseCouplingFamily) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ x T ε : ℝ,
      X < x ∧
      4 ≤ T ∧
      1 < x ∧
      0 < ε ∧ ε < 1 ∧
      (∀ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
        (∑ i, (m i : ℝ) * i.1.im = 0) →
        ∃ k : ℤ,
          ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) + (k : ℝ) * (2 * Real.pi)‖
            ≤ ((Real.pi / 2) * ε) * (∑ i, |(m i : ℝ)|)) := by
  intro hRH X
  rcases hAntiTargetPhase hRH X with
    ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hxUpper⟩
  refine ⟨x, T, ε, hXx, hT4, hx1, hεpos, hεlt, ?_⟩
  intro m hRel
  let S : Finset ℂ := (finite_zeros_le T).toFinset
  let γ : {ρ // ρ ∈ S} → ℝ := fun i => i.1.im
  let φ : {ρ // ρ ∈ S} → ℝ := fun i => Complex.arg i.1 + Real.pi
  have hApprox :
      ∀ i : {ρ // ρ ∈ S}, ∃ k : ℤ,
        ‖Real.log x * γ i - φ i - (k : ℝ) * (2 * Real.pi)‖ ≤ (Real.pi / 2) * ε := by
    intro i
    simpa [S, γ, φ] using
      exists_int_arg_bound_of_antitarget_phase_close (x := x) (ε := ε)
        hx1 hεlt (hphase i.1 i.2)
  have hRel' : (∑ i, (m i : ℝ) * γ i) = 0 := by
    simpa [γ] using hRel
  rcases inhomogeneous_one_param_compatibility_necessary
      (γ := γ) (φ := φ) (t := Real.log x) (ε := (Real.pi / 2) * ε)
      hApprox (m := m) hRel' with
    ⟨k, hk⟩
  exact ⟨k, by simpa [S, γ, φ, mul_assoc, mul_left_comm, mul_comm] using hk⟩

/--
Obstruction criterion directly at the positive phase-coupling class boundary.
-/
theorem not_targetTowerPhaseCouplingFamily_of_uniform_relation_gap_piOverTwo
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              < ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ TargetTowerPhaseCouplingFamily := by
  intro hTarget
  rcases targetTowerPhaseCouplingFamily_implies_relation_compatibility_piOverTwo hTarget hRH 0 with
    ⟨x, T, ε, hXx, hT4, hx1, hεpos, hεlt, hCompat⟩
  rcases hObs T with ⟨m, hRel, hGap⟩
  rcases hCompat m hRel with ⟨k, hk⟩
  have hεle : ε ≤ 1 := le_of_lt hεlt
  have hsum_nonneg : 0 ≤ (∑ i, |(m i : ℝ)|) := by
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hmul :
      ((Real.pi / 2) * ε) * (∑ i, |(m i : ℝ)|)
        ≤ (Real.pi / 2) * (∑ i, |(m i : ℝ)|) := by
    have hpi2_nonneg : 0 ≤ Real.pi / 2 := by positivity
    calc
      ((Real.pi / 2) * ε) * (∑ i, |(m i : ℝ)|)
          = (Real.pi / 2) * (ε * (∑ i, |(m i : ℝ)|)) := by ring
      _ ≤ (Real.pi / 2) * (1 * (∑ i, |(m i : ℝ)|)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hεle hsum_nonneg) hpi2_nonneg
      _ = (Real.pi / 2) * (∑ i, |(m i : ℝ)|) := by ring
  have hk' :
      ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖
        ≤ (Real.pi / 2) * (∑ i, |(m i : ℝ)|) := by
    exact le_trans hk hmul
  exact (not_lt_of_ge hk') (hGap k)

/--
Obstruction criterion directly at the anti-target phase-coupling class boundary.
-/
theorem not_antiTargetTowerPhaseCouplingFamily_of_uniform_relation_gap_piOverTwo
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              <
                ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) +
                    (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ AntiTargetTowerPhaseCouplingFamily := by
  intro hAntiTarget
  rcases antiTargetTowerPhaseCouplingFamily_implies_relation_compatibility_piOverTwo hAntiTarget hRH 0 with
    ⟨x, T, ε, hXx, hT4, hx1, hεpos, hεlt, hCompat⟩
  rcases hObs T with ⟨m, hRel, hGap⟩
  rcases hCompat m hRel with ⟨k, hk⟩
  have hεle : ε ≤ 1 := le_of_lt hεlt
  have hsum_nonneg : 0 ≤ (∑ i, |(m i : ℝ)|) := by
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hmul :
      ((Real.pi / 2) * ε) * (∑ i, |(m i : ℝ)|)
        ≤ (Real.pi / 2) * (∑ i, |(m i : ℝ)|) := by
    have hpi2_nonneg : 0 ≤ Real.pi / 2 := by positivity
    calc
      ((Real.pi / 2) * ε) * (∑ i, |(m i : ℝ)|)
          = (Real.pi / 2) * (ε * (∑ i, |(m i : ℝ)|)) := by ring
      _ ≤ (Real.pi / 2) * (1 * (∑ i, |(m i : ℝ)|)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hεle hsum_nonneg) hpi2_nonneg
      _ = (Real.pi / 2) * (∑ i, |(m i : ℝ)|) := by ring
  have hk' :
      ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) + (k : ℝ) * (2 * Real.pi)‖
        ≤ (Real.pi / 2) * (∑ i, |(m i : ℝ)|) := by
    exact le_trans hk hmul
  exact (not_lt_of_ge hk') (hGap k)

/--
Positive Blocker-7 coefficient-control payload implies the same quantitative
relation-compatibility condition with explicit loss `(π/2)·ε`.
-/
theorem targetHeightCoeffControlHyp_implies_relation_compatibility_piOverTwo
    (hTargetCoeff : RhPiTargetHeightCoeffControlHyp) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ x T ε : ℝ,
      X < x ∧
      4 ≤ T ∧
      1 < x ∧
      0 < ε ∧ ε < 1 ∧
      (∀ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
        (∑ i, (m i : ℝ) * i.1.im = 0) →
        ∃ k : ℤ,
          ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖
            ≤ ((Real.pi / 2) * ε) * (∑ i, |(m i : ℝ)|)) := by
  intro hRH X
  rcases hTargetCoeff.witness hRH X with
    ⟨x, hXx, T, hT4, hx1, _herr, ε, hεpos, hεlt, hphase, _hcoeff⟩
  refine ⟨x, T, ε, hXx, hT4, hx1, hεpos, hεlt, ?_⟩
  intro m hRel
  let S : Finset ℂ := (finite_zeros_le T).toFinset
  let γ : {ρ // ρ ∈ S} → ℝ := fun i => i.1.im
  let φ : {ρ // ρ ∈ S} → ℝ := fun i => Complex.arg i.1
  have hApprox :
      ∀ i : {ρ // ρ ∈ S}, ∃ k : ℤ,
        ‖Real.log x * γ i - φ i - (k : ℝ) * (2 * Real.pi)‖ ≤ (Real.pi / 2) * ε := by
    intro i
    simpa [S, γ, φ] using
      exists_int_arg_bound_of_target_phase_close (x := x) (ε := ε)
        hx1 hεlt (hphase i.1 i.2)
  have hRel' : (∑ i, (m i : ℝ) * γ i) = 0 := by
    simpa [γ] using hRel
  rcases inhomogeneous_one_param_compatibility_necessary
      (γ := γ) (φ := φ) (t := Real.log x) (ε := (Real.pi / 2) * ε)
      hApprox (m := m) hRel' with
    ⟨k, hk⟩
  exact ⟨k, by simpa [S, γ, φ, mul_assoc, mul_left_comm, mul_comm] using hk⟩

/--
Negative Blocker-7 coefficient-control payload implies the shifted
relation-compatibility condition with the same `(π/2)·ε` loss.
-/
theorem antiTargetHeightCoeffControlHyp_implies_relation_compatibility_piOverTwo
    (hAntiTargetCoeff : RhPiAntiTargetHeightCoeffControlHyp) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ x T ε : ℝ,
      X < x ∧
      4 ≤ T ∧
      1 < x ∧
      0 < ε ∧ ε < 1 ∧
      (∀ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
        (∑ i, (m i : ℝ) * i.1.im = 0) →
        ∃ k : ℤ,
          ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) + (k : ℝ) * (2 * Real.pi)‖
            ≤ ((Real.pi / 2) * ε) * (∑ i, |(m i : ℝ)|)) := by
  intro hRH X
  rcases hAntiTargetCoeff.witness hRH X with
    ⟨x, hXx, T, hT4, hx1, _herr, ε, hεpos, hεlt, hphase, _hcoeff⟩
  refine ⟨x, T, ε, hXx, hT4, hx1, hεpos, hεlt, ?_⟩
  intro m hRel
  let S : Finset ℂ := (finite_zeros_le T).toFinset
  let γ : {ρ // ρ ∈ S} → ℝ := fun i => i.1.im
  let φ : {ρ // ρ ∈ S} → ℝ := fun i => Complex.arg i.1 + Real.pi
  have hApprox :
      ∀ i : {ρ // ρ ∈ S}, ∃ k : ℤ,
        ‖Real.log x * γ i - φ i - (k : ℝ) * (2 * Real.pi)‖ ≤ (Real.pi / 2) * ε := by
    intro i
    simpa [S, γ, φ] using
      exists_int_arg_bound_of_antitarget_phase_close (x := x) (ε := ε)
        hx1 hεlt (hphase i.1 i.2)
  have hRel' : (∑ i, (m i : ℝ) * γ i) = 0 := by
    simpa [γ] using hRel
  rcases inhomogeneous_one_param_compatibility_necessary
      (γ := γ) (φ := φ) (t := Real.log x) (ε := (Real.pi / 2) * ε)
      hApprox (m := m) hRel' with
    ⟨k, hk⟩
  exact ⟨k, by simpa [S, γ, φ, mul_assoc, mul_left_comm, mul_comm] using hk⟩

/--
Obstruction criterion directly at the positive Blocker-7 coefficient-control
class boundary.
-/
theorem not_RhPiTargetHeightCoeffControlHyp_of_uniform_relation_gap_piOverTwo
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              < ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ RhPiTargetHeightCoeffControlHyp := by
  intro hTargetCoeff
  rcases targetHeightCoeffControlHyp_implies_relation_compatibility_piOverTwo
      hTargetCoeff hRH 0 with
    ⟨x, T, ε, hXx, hT4, hx1, hεpos, hεlt, hCompat⟩
  rcases hObs T with ⟨m, hRel, hGap⟩
  rcases hCompat m hRel with ⟨k, hk⟩
  have hεle : ε ≤ 1 := le_of_lt hεlt
  have hsum_nonneg : 0 ≤ (∑ i, |(m i : ℝ)|) := by
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hmul :
      ((Real.pi / 2) * ε) * (∑ i, |(m i : ℝ)|)
        ≤ (Real.pi / 2) * (∑ i, |(m i : ℝ)|) := by
    have hpi2_nonneg : 0 ≤ Real.pi / 2 := by positivity
    calc
      ((Real.pi / 2) * ε) * (∑ i, |(m i : ℝ)|)
          = (Real.pi / 2) * (ε * (∑ i, |(m i : ℝ)|)) := by ring
      _ ≤ (Real.pi / 2) * (1 * (∑ i, |(m i : ℝ)|)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hεle hsum_nonneg) hpi2_nonneg
      _ = (Real.pi / 2) * (∑ i, |(m i : ℝ)|) := by ring
  have hk' :
      ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖
        ≤ (Real.pi / 2) * (∑ i, |(m i : ℝ)|) := by
    exact le_trans hk hmul
  exact (not_lt_of_ge hk') (hGap k)

/--
Obstruction criterion directly at the anti-target Blocker-7 coefficient-control
class boundary.
-/
theorem not_RhPiAntiTargetHeightCoeffControlHyp_of_uniform_relation_gap_piOverTwo
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              <
                ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) +
                    (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ RhPiAntiTargetHeightCoeffControlHyp := by
  intro hAntiTargetCoeff
  rcases antiTargetHeightCoeffControlHyp_implies_relation_compatibility_piOverTwo
      hAntiTargetCoeff hRH 0 with
    ⟨x, T, ε, hXx, hT4, hx1, hεpos, hεlt, hCompat⟩
  rcases hObs T with ⟨m, hRel, hGap⟩
  rcases hCompat m hRel with ⟨k, hk⟩
  have hεle : ε ≤ 1 := le_of_lt hεlt
  have hsum_nonneg : 0 ≤ (∑ i, |(m i : ℝ)|) := by
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hmul :
      ((Real.pi / 2) * ε) * (∑ i, |(m i : ℝ)|)
        ≤ (Real.pi / 2) * (∑ i, |(m i : ℝ)|) := by
    have hpi2_nonneg : 0 ≤ Real.pi / 2 := by positivity
    calc
      ((Real.pi / 2) * ε) * (∑ i, |(m i : ℝ)|)
          = (Real.pi / 2) * (ε * (∑ i, |(m i : ℝ)|)) := by ring
      _ ≤ (Real.pi / 2) * (1 * (∑ i, |(m i : ℝ)|)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hεle hsum_nonneg) hpi2_nonneg
      _ = (Real.pi / 2) * (∑ i, |(m i : ℝ)|) := by ring
  have hk' :
      ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) + (k : ℝ) * (2 * Real.pi)‖
        ≤ (Real.pi / 2) * (∑ i, |(m i : ℝ)|) := by
    exact le_trans hk hmul
  exact (not_lt_of_ge hk') (hGap k)

/-- Forward form: any positive Blocker-7 coeff-control witness excludes a
uniform `π/2`-scaled positive relation-gap obstruction. -/
theorem no_uniform_relation_gap_piOverTwo_of_RhPiTargetHeightCoeffControlHyp
    (hTargetCoeff : RhPiTargetHeightCoeffControlHyp)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ¬ (∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              < ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖)) := by
  intro hObs
  exact
    (not_RhPiTargetHeightCoeffControlHyp_of_uniform_relation_gap_piOverTwo hRH hObs)
      hTargetCoeff

/-- Forward form: any anti-target Blocker-7 coeff-control witness excludes a
uniform `π/2`-scaled anti-target relation-gap obstruction. -/
theorem no_uniform_relation_gap_piOverTwo_of_RhPiAntiTargetHeightCoeffControlHyp
    (hAntiTargetCoeff : RhPiAntiTargetHeightCoeffControlHyp)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ¬ (∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              <
                ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) +
                    (k : ℝ) * (2 * Real.pi)‖)) := by
  intro hObs
  exact
    (not_RhPiAntiTargetHeightCoeffControlHyp_of_uniform_relation_gap_piOverTwo hRH hObs)
      hAntiTargetCoeff

/--
If a fixed finite family of frequencies/targets has an integer relation
obstruction with quantitative gap `sum |m_i|`, then there is no one-parameter
inhomogeneous approximation with tolerance `< 1` for all coordinates.
-/
theorem no_inhomogeneous_fit_of_relation_gap
    {ι : Type*} [Fintype ι]
    {γ φ : ι → ℝ} {t ε : ℝ}
    (hεlt : ε < 1)
    (hApprox :
      ∀ i : ι, ∃ k : ℤ,
        ‖t * γ i - φ i - (k : ℝ) * (2 * Real.pi)‖ ≤ ε)
    (hObs :
      ∃ m : ι → ℤ,
        (∑ i, (m i : ℝ) * γ i = 0) ∧
        (∀ k : ℤ,
          (∑ i, |(m i : ℝ)|)
            < ‖(∑ i, (m i : ℝ) * φ i) + (k : ℝ) * (2 * Real.pi)‖)) :
    False := by
  rcases hObs with ⟨m, hRel, hGap⟩
  rcases inhomogeneous_one_param_compatibility_necessary
      (γ := γ) (φ := φ) (t := t) (ε := ε) hApprox (m := m) hRel with
    ⟨k, hk⟩
  have hεle : ε ≤ 1 := le_of_lt hεlt
  have hsum_nonneg : 0 ≤ (∑ i, |(m i : ℝ)|) := by
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hmul :
      ε * (∑ i, |(m i : ℝ)|) ≤ (∑ i, |(m i : ℝ)|) := by
    calc
      ε * (∑ i, |(m i : ℝ)|) ≤ 1 * (∑ i, |(m i : ℝ)|) :=
        mul_le_mul_of_nonneg_right hεle hsum_nonneg
      _ = (∑ i, |(m i : ℝ)|) := by ring
  have hk' :
      ‖(∑ i, (m i : ℝ) * φ i) + (k : ℝ) * (2 * Real.pi)‖
        ≤ (∑ i, |(m i : ℝ)|) := by
    exact le_trans hk hmul
  exact (not_lt_of_ge hk') (hGap k)

/--
Target-branch obstruction criterion: if every finite-zero cutoff `T` admits an
integer relation among ordinates whose target phases violate the quantitative
compatibility inequality by a fixed unit-scale gap, then
`TargetTowerArgApproxFamily` is impossible.
-/
theorem not_targetTowerArgApproxFamily_of_uniform_relation_gap
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            (∑ i, |(m i : ℝ)|)
              < ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ TargetTowerArgApproxFamily := by
  intro hTarget
  rcases targetTowerArgApproxFamily_implies_relation_compatibility hTarget hRH 0 with
    ⟨x, T, ε, hXx, hT4, hx1, hεpos, hεlt, hCompat⟩
  rcases hObs T with ⟨m, hRel, hGap⟩
  rcases hCompat m hRel with ⟨k, hk⟩
  have hεle : ε ≤ 1 := le_of_lt hεlt
  have hsum_nonneg : 0 ≤ (∑ i, |(m i : ℝ)|) := by
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hmul :
      ε * (∑ i, |(m i : ℝ)|) ≤ (∑ i, |(m i : ℝ)|) := by
    calc
      ε * (∑ i, |(m i : ℝ)|) ≤ 1 * (∑ i, |(m i : ℝ)|) :=
        mul_le_mul_of_nonneg_right hεle hsum_nonneg
      _ = (∑ i, |(m i : ℝ)|) := by ring
  have hk' :
      ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖
        ≤ (∑ i, |(m i : ℝ)|) := by
    exact le_trans hk hmul
  exact (not_lt_of_ge hk') (hGap k)

/--
Anti-target obstruction criterion: if every finite-zero cutoff `T` admits an
integer relation among ordinates whose shifted target phases (`arg + π`) violate
the same quantitative compatibility inequality, then
`AntiTargetTowerArgApproxFamily` is impossible.
-/
theorem not_antiTargetTowerArgApproxFamily_of_uniform_relation_gap
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            (∑ i, |(m i : ℝ)|)
              <
                ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) +
                    (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ AntiTargetTowerArgApproxFamily := by
  intro hAntiTarget
  rcases antiTargetTowerArgApproxFamily_implies_relation_compatibility hAntiTarget hRH 0 with
    ⟨x, T, ε, hXx, hT4, hx1, hεpos, hεlt, hCompat⟩
  rcases hObs T with ⟨m, hRel, hGap⟩
  rcases hCompat m hRel with ⟨k, hk⟩
  have hεle : ε ≤ 1 := le_of_lt hεlt
  have hsum_nonneg : 0 ≤ (∑ i, |(m i : ℝ)|) := by
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hmul :
      ε * (∑ i, |(m i : ℝ)|) ≤ (∑ i, |(m i : ℝ)|) := by
    calc
      ε * (∑ i, |(m i : ℝ)|) ≤ 1 * (∑ i, |(m i : ℝ)|) :=
        mul_le_mul_of_nonneg_right hεle hsum_nonneg
      _ = (∑ i, |(m i : ℝ)|) := by ring
  have hk' :
      ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) + (k : ℝ) * (2 * Real.pi)‖
        ≤ (∑ i, |(m i : ℝ)|) := by
    exact le_trans hk hmul
  exact (not_lt_of_ge hk') (hGap k)

end Aristotle.Standalone.RHPiInhomogeneousApproxObstruction
