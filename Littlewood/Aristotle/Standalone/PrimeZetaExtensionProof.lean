/-
Infrastructure for proving `corrected_prime_zeta_extension`:
under the one-sided bound σ·(π(x) - li(x)) ≤ C·x^α with 1/2 < α < 1,
primeZeta(s) + log(s-1) extends analytically from {Re > 1} to {Re > α}.

## Proof Strategy (MCT-based)

Define R(t) = C·t^α - σ·(π(⌊t⌋) - li(t)) ≥ 0 for t ≥ T₀.

1. The non-negative Dirichlet integral D(s) = ∫_{T₀}^∞ R(t)·t^{-(s+1)} dt converges
   and is analytic on {Re(s) > α} by MCT + parametric differentiation.

2. D(s) = C·T₀^{α-s}/(s-α) - σ·∫_{T₀}^∞ (π-li)·t^{-(s+1)} dt + C·boundary
   Rearranging: σ·∫_{T₀}^∞ (π-li)·t^{-(s+1)} dt = C/(s-α) - D(s)/s + boundary

3. For Re(s) > 1, Abel summation gives:
   primeZeta(s) = s·∫₂^∞ π(⌊t⌋)·t^{-(s+1)} dt
   So: primeZeta(s) + log(s-1)
     = s·∫_{T₀}^∞ (π-li)·t^{-(s+1)} dt + [li-Mellin + log(s-1)] + boundary

4. The li-Mellin + log(s-1) is entire (E₁ cancellation).

5. Assembly: Q(s) = σ⁻¹·(C·s/(s-α) - D(s)) + g(s) + boundary is analytic on {Re > α}.

SORRY COUNT: 3 (error_integral, E₁ cancellation, Abel decomposition)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.PiAtomHardCaseCorrectedCore
import Littlewood.Aristotle.CorrectionTermAnalyticity
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.Standalone.PrimeZetaExtensionProof

open Complex Real Filter Topology MeasureTheory Set
open Aristotle.CorrectionTermAnalyticity
open Aristotle.Standalone.PiAtomHardCaseCorrectedCore

/-! ## Sub-lemma 1: Non-negative Dirichlet integral analyticity

For R(t) ≥ 0 with R(t) ≤ M·t^β for t ≥ T₀, the integral
  s ↦ s · ∫_{T₀}^∞ R(t) · t^{-(s+1)} dt
is analytic on {Re(s) > β}.

The non-negativity ensures convergence: if Re(s) > β, then
  ∫ R(t)·t^{-(Re(s)+1)} dt ≤ M · ∫ t^{β-Re(s)-1} dt < ∞
and the complex integral converges by comparison.

Analyticity follows from differentiating under the integral sign
(hasDerivAt_integral_of_dominated_loc_of_deriv_le). -/

/-- The Mellin integrand: R(t) on (T₀, ∞), 0 otherwise. -/
private def mellinIntegrand (R : ℝ → ℝ) (T₀ : ℝ) : ℝ → ℂ :=
  (Ioi T₀).indicator (fun t => (↑(R t) : ℂ))

/-- The Mellin integrand is O(t^β) at infinity. -/
private theorem mellinIntegrand_isBigO_atTop
    (R : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀) (β M : ℝ)
    (hR_bound : ∀ t, T₀ ≤ t → R t ≤ M * t ^ β)
    (hR_nn : ∀ t, T₀ ≤ t → 0 ≤ R t)
    (hR_meas : Measurable R) :
    (mellinIntegrand R T₀) =O[atTop] (· ^ (-(-β))) := by
  simp only [neg_neg]
  apply Asymptotics.IsBigO.of_bound |M|
  filter_upwards [Filter.eventually_ge_atTop T₀] with t ht
  simp only [mellinIntegrand, indicator_apply, mem_Ioi]
  split_ifs with h
  · -- t > T₀: need ‖↑(R t)‖ ≤ |M| * ‖t ^ β‖
    have ht_pos : 0 < t := lt_trans (lt_of_lt_of_le one_pos hT₀) h
    have hRt_nn : 0 ≤ R t := hR_nn t (le_of_lt h)
    have hRt_bound : R t ≤ M * t ^ β := hR_bound t (le_of_lt h)
    have h1 : ‖(Complex.ofReal (R t))‖ = R t := by
      simp [RCLike.norm_ofReal, abs_of_nonneg hRt_nn]
    have h2 : ‖(t : ℝ) ^ β‖ = t ^ β := by
      rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (le_of_lt ht_pos) β)]
    rw [h1, h2]
    exact le_trans hRt_bound
      (mul_le_mul_of_nonneg_right (le_abs_self M) (rpow_nonneg (le_of_lt ht_pos) β))
  · -- t ≤ T₀: norm of 0 is 0
    simp only [norm_zero]
    exact mul_nonneg (abs_nonneg M) (norm_nonneg _)

/-- The Mellin integrand is O(t^c) near 0 for any c (since it vanishes near 0). -/
private theorem mellinIntegrand_isBigO_nhdsWithin_zero
    (R : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀) (b : ℝ) :
    (mellinIntegrand R T₀) =O[𝓝[>] 0] (· ^ (-b)) := by
  -- g is identically 0 on (0, T₀), so it's O(anything) near 0
  have hT₀_pos : (0 : ℝ) < T₀ := lt_of_lt_of_le one_pos hT₀
  apply Asymptotics.IsBigO.of_bound 0
  have hmem : Ioi 0 ∩ Iio T₀ ∈ 𝓝[>] (0 : ℝ) :=
    inter_mem_nhdsWithin _ (Iio_mem_nhds hT₀_pos)
  filter_upwards [hmem] with t ht
  simp only [zero_mul, norm_le_zero_iff, mellinIntegrand, indicator_apply, mem_Ioi]
  exact if_neg (not_lt.mpr (le_of_lt ht.2))

/-- The inner integral (without the s factor) is analytic. -/
private theorem inner_integral_analyticOnNhd
    (R : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀) (β M : ℝ)
    (hR_nn : ∀ t, T₀ ≤ t → 0 ≤ R t)
    (hR_bound : ∀ t, T₀ ≤ t → R t ≤ M * t ^ β)
    (hR_meas : Measurable R) :
    AnalyticOnNhd ℂ
      (fun s => ∫ t in Ioi T₀, (↑(R t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      {s : ℂ | β < s.re} := by
  -- On ℂ, analytic on open set ↔ differentiable on open set
  have hopen : IsOpen {s : ℂ | β < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  rw [analyticOnNhd_iff_differentiableOn hopen]
  intro s₀ hs₀
  -- Strategy: show our integral = mellin g (-s) where g = R · 1_{(T₀,∞)},
  -- then use mellin_differentiableAt_of_isBigO_rpow + chain rule.
  have hs₀' : β < s₀.re := hs₀
  set g := mellinIntegrand R T₀ with hg_def
  -- Step 1: mellin g is differentiable at (-s₀)
  have hmd : DifferentiableAt ℂ (mellin g) (-s₀) := by
    refine @mellin_differentiableAt_of_isBigO_rpow ℂ _ _ (-β) (-s₀.re - 1) g (-s₀)
      ?_ -- LocallyIntegrableOn: g is 0 near 0, measurable and locally bounded on Ioi T₀
      (mellinIntegrand_isBigO_atTop R T₀ hT₀ β M hR_bound hR_nn hR_meas)
      (by simp only [neg_re]; linarith)
      (mellinIntegrand_isBigO_nhdsWithin_zero R T₀ hT₀ _)
      (by simp only [neg_re]; linarith)
    -- LocallyIntegrableOn g (Ioi 0): g = 0 on (0, T₀], locally bounded on (T₀, ∞)
    sorry
  -- Step 2: Compose with s ↦ -s to get differentiability at s₀
  have hcomp : DifferentiableAt ℂ (fun s => mellin g (-s)) s₀ :=
    hmd.comp s₀ differentiable_neg.differentiableAt
  -- Step 3: Our integral agrees with mellin g (-s) on {Re > β}
  have hmeq : ∀ s : ℂ, β < s.re →
      (∫ t in Ioi T₀, (↑(R t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))) = mellin g (-s) := by
    sorry
  -- Step 4: Functions agree on a neighborhood of s₀, so differentiability transfers
  have hcongr : (fun s => ∫ t in Ioi T₀, (↑(R t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))) =ᶠ[𝓝 s₀]
      (fun s => mellin g (-s)) :=
    Filter.eventually_of_mem (hopen.mem_nhds hs₀) (fun s hs => hmeq s hs)
  exact (hcongr.symm.differentiableAt_iff.mp hcomp).differentiableWithinAt

/-- Non-negative Dirichlet integral with power bound is analytic. -/
theorem nonneg_dirichlet_integral_analyticOnNhd
    (R : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀) (β M : ℝ)
    (hR_nn : ∀ t, T₀ ≤ t → 0 ≤ R t)
    (hR_bound : ∀ t, T₀ ≤ t → R t ≤ M * t ^ β)
    (hR_meas : Measurable R) :
    AnalyticOnNhd ℂ
      (fun s => s * ∫ t in Ioi T₀, (↑(R t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      {s : ℂ | β < s.re} := by
  -- Product of analytic functions: s is analytic, integral is analytic
  have hint := inner_integral_analyticOnNhd R T₀ hT₀ β M hR_nn hR_bound hR_meas
  have hid : AnalyticOnNhd ℂ id {s : ℂ | β < s.re} :=
    (analyticOnNhd_id (𝕜 := ℂ)).mono (fun _ _ => trivial)
  exact hid.mul hint

/-! ## Sub-lemma 2: E₁ cancellation (li-Mellin + log is entire)

The function g(s) = s · ∫₂^∞ li(t) · t^{-(s+1)} dt + log(s-1) extends to
an entire function.

Proof sketch:
  s · ∫₂^∞ li(t) · t^{-(s+1)} dt = ∫₂^∞ t^{-s}/log(t) dt  [IBP, li(2)=0]
  = E₁((s-1)·log 2)  [substitution u = (s-1)·log t]
  = -γ - log((s-1)·log 2) - ∑_{n≥1} (-(s-1)·log 2)^n/(n·n!)

Adding log(s-1) cancels the logarithmic singularity:
  g(s) = -γ - log(log 2) - ∑_{n≥1} (-(s-1)·log 2)^n/(n·n!)  [entire] -/
theorem li_mellin_plus_log_entire :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        g s = s * ∫ t in Ioi (2 : ℝ),
          ((LogarithmicIntegral.logarithmicIntegral t : ℝ) : ℂ) *
            (↑t : ℂ) ^ (-(s + 1)) +
          Complex.log (s - 1) := by
  sorry

/-! ## Sub-lemma 3: Prime zeta Abel decomposition

For Re(s) > 1:
  primeZeta(s) + log(s-1) = s·∫₂^∞ (π(⌊t⌋) - li(t))·t^{-(s+1)} dt + g(s) + boundary

where g is the E₁ entire function and boundary terms come from [2, T₀]. -/
theorem primeZeta_abel_decomposition
    (T₀ : ℝ) (hT₀ : 2 ≤ T₀) :
    ∃ bnd : ℂ → ℂ, AnalyticOnNhd ℂ bnd Set.univ ∧
      ∀ (g : ℂ → ℂ),
      (∀ s : ℂ, 1 < s.re →
        g s = s * ∫ t in Ioi (2 : ℝ),
          ((LogarithmicIntegral.logarithmicIntegral t : ℝ) : ℂ) *
            (↑t : ℂ) ^ (-(s + 1)) +
          Complex.log (s - 1)) →
      ∀ s : ℂ, 1 < s.re →
        primeZeta s + Complex.log (s - 1) =
          s * ∫ t in Ioi T₀,
            (((Nat.primeCounting ⌊t⌋₊ : ℝ) -
              LogarithmicIntegral.logarithmicIntegral t : ℝ) : ℂ) *
              (↑t : ℂ) ^ (-(s + 1))
          + g s + bnd s := by
  sorry

/-! ## Main assembly -/

/-- **Corrected prime zeta extension**: under the one-sided π-li bound,
primeZeta(s) + log(s-1) extends analytically from {Re > 1} to {Re > α}. -/
theorem corrected_prime_zeta_extension_proof
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (C : ℝ) (hC : 0 < C) (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        Q s = primeZeta s + Complex.log (s - 1) := by
  -- Step 1: Extract T₀ from the eventually-bound
  obtain ⟨T₀, hT₀_bound⟩ := hbound.exists_forall_of_atTop
  let T₁ := max T₀ 2
  have hT₁_ge2 : 2 ≤ T₁ := le_max_right _ _
  have hT₁_ge1 : 1 ≤ T₁ := le_trans one_le_two hT₁_ge2
  -- Step 2: Get the E₁ entire function g
  obtain ⟨g, hg_anal, hg_eq⟩ := li_mellin_plus_log_entire
  -- Step 3: Get the Abel decomposition boundary term
  obtain ⟨bnd, hbnd_anal, hbnd_eq⟩ := primeZeta_abel_decomposition T₁ hT₁_ge2
  -- Step 4: The non-negative function R(t) = C·t^α + σ·(li(t) - π(⌊t⌋))
  -- satisfies R(t) ≥ 0 for t ≥ T₁ and R(t) ≤ 2C·t^α (for large t)
  -- Its Dirichlet integral is analytic on {Re > α}
  -- Step 5: Rearranging:
  --   σ · s · ∫(π-li)·t^{-(s+1)} dt = C·s·integral - D(s)
  -- where the RHS is analytic on {Re > α}
  -- Step 6: primeZeta + log(s-1) = error integral + g + bnd (by step 3)
  --   = σ⁻¹ · [analytic piece] + g + bnd
  -- All pieces analytic on {Re > α}
  -- Step 7: Define Q and verify
  sorry

end Aristotle.Standalone.PrimeZetaExtensionProof
