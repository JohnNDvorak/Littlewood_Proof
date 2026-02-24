import Littlewood.Aristotle.Standalone.RHPiTargetPhaseArgReduction

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiInhomogeneousApproxObstruction

open scoped BigOperators
open Complex ZetaZeros
open Aristotle.Standalone.RHPiTargetPhaseArgReduction

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

end Aristotle.Standalone.RHPiInhomogeneousApproxObstruction
