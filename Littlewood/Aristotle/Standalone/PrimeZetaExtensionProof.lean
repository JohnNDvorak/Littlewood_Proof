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

SORRY COUNT: 1 (corrected_prime_zeta_extension_proof — needs E₁, Abel, Landau MCT)
PROVED: inner_integral_analyticOnNhd, nonneg_dirichlet_integral_analyticOnNhd,
  mellinIntegrand_isBigO_atTop, mellinIntegrand_isBigO_nhdsWithin_zero

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.PiAtomHardCaseCorrectedCore
import Littlewood.Aristotle.CorrectionTermAnalyticity
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.LSeries.SumCoeff

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
    -- LocallyIntegrableOn g (Ioi 0): g = 0 on (0, T₀], bounded on compact subsets
    intro x (hx : x ∈ Ioi (0 : ℝ))
    have hx_pos : (0 : ℝ) < x := hx
    rw [nhdsWithin_eq_nhds.mpr (isOpen_Ioi.mem_nhds hx)]
    refine ⟨Ioo (x / 2) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    have hg_meas : Measurable g :=
      (continuous_ofReal.measurable.comp hR_meas).indicator measurableSet_Ioi
    have hx_half_pos : (0 : ℝ) < x / 2 := by linarith
    set B := |M| * ((x / 2) ^ β + (x + 1) ^ β) with hB_def
    apply Measure.integrableOn_of_bounded measure_Ioo_lt_top.ne
      hg_meas.aestronglyMeasurable (M := B)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht_lo, ht_hi⟩
    simp only [hg_def, mellinIntegrand, indicator_apply, mem_Ioi]
    split_ifs with h
    · -- t > T₀: ‖↑(R t)‖ = R t ≤ M * t^β ≤ B
      have ht_pos : (0 : ℝ) < t := by linarith
      have hRt_nn := hR_nn t (le_of_lt h)
      have hnorm : ‖(↑(R t) : ℂ)‖ = R t := by
        simp [RCLike.norm_ofReal, abs_of_nonneg hRt_nn]
      rw [hnorm]
      calc R t ≤ M * t ^ β := hR_bound t (le_of_lt h)
        _ ≤ |M| * t ^ β :=
            mul_le_mul_of_nonneg_right (le_abs_self M) (rpow_nonneg (le_of_lt ht_pos) β)
        _ ≤ B := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg M)
            by_cases hβ : 0 ≤ β
            · calc t ^ β ≤ (x + 1) ^ β :=
                    rpow_le_rpow (le_of_lt ht_pos) (le_of_lt ht_hi) hβ
                _ ≤ (x / 2) ^ β + (x + 1) ^ β :=
                    le_add_of_nonneg_left (rpow_nonneg (le_of_lt hx_half_pos) β)
            · push_neg at hβ
              have h_neg_nn : 0 ≤ -β := by linarith
              have h1 : (x / 2) ^ (-β) ≤ t ^ (-β) :=
                rpow_le_rpow (le_of_lt hx_half_pos) (le_of_lt ht_lo) h_neg_nn
              have h2 : 0 < (x / 2) ^ (-β) := rpow_pos_of_pos hx_half_pos (-β)
              have ht_eq : t ^ β = (t ^ (-β))⁻¹ := by
                have h := rpow_neg (le_of_lt ht_pos) (-β); rw [neg_neg] at h; exact h
              have hx_eq : (x / 2) ^ β = ((x / 2) ^ (-β))⁻¹ := by
                have h := rpow_neg (le_of_lt hx_half_pos) (-β); rw [neg_neg] at h; exact h
              calc t ^ β = (t ^ (-β))⁻¹ := ht_eq
                _ ≤ ((x / 2) ^ (-β))⁻¹ := inv_anti₀ h2 h1
                _ = (x / 2) ^ β := hx_eq.symm
                _ ≤ (x / 2) ^ β + (x + 1) ^ β :=
                    le_add_of_nonneg_right (rpow_nonneg (by linarith) β)
    · -- t ≤ T₀: g t = 0
      simp only [norm_zero]
      exact mul_nonneg (abs_nonneg M) (add_nonneg (rpow_nonneg (le_of_lt hx_half_pos) β)
        (rpow_nonneg (by linarith) β))
  -- Step 2: Compose with s ↦ -s to get differentiability at s₀
  have hcomp : DifferentiableAt ℂ (fun s => mellin g (-s)) s₀ :=
    hmd.comp s₀ differentiable_neg.differentiableAt
  -- Step 3: Our integral agrees with mellin g (-s) on {Re > β}
  have hmeq : ∀ s : ℂ, β < s.re →
      (∫ t in Ioi T₀, (↑(R t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))) = mellin g (-s) := by
    intro s _hs
    symm
    simp only [mellin, hg_def, mellinIntegrand]
    -- Rewrite integrand: case-split indicator, match smul ↔ mul
    have h_eq : ∀ t : ℝ, (↑t : ℂ) ^ (-s - 1) •
        (Ioi T₀).indicator (fun t => (↑(R t) : ℂ)) t =
        (Ioi T₀).indicator (fun t => ↑(R t) * (↑t : ℂ) ^ (-(s + 1))) t := by
      intro t; simp only [indicator_apply, mem_Ioi]
      split_ifs
      · rw [smul_eq_mul, mul_comm]; congr 1; ring
      · rw [smul_zero]
    simp_rw [h_eq]
    rw [setIntegral_indicator measurableSet_Ioi]
    rw [Ioi_inter_Ioi, show (0 : ℝ) ⊔ T₀ = T₀ from sup_eq_right.mpr (by linarith)]
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

/-! ## Abel summation for primeZeta

We connect primeZeta (∑' over primes) to Mathlib's LSeries infrastructure,
then apply `LSeries_eq_mul_integral'` to get the integral representation:
  primeZeta(s) = s · ∫ t in Ioi 1, (primeCounting ⌊t⌋₊ : ℂ) · t^{-(s+1)}
for Re(s) > 1. -/

/-- Prime indicator function: 1 on primes, 0 elsewhere. -/
private def primeIndicator : ℕ → ℂ := fun n => if n.Prime then 1 else 0

/-- Partial sums of prime indicator norms are O(n^1).
This follows from π(n) ≤ n (trivially: every prime is a natural number).
Proof: ∑_{k=1}^n ‖primeIndicator k‖ ≤ card(Icc 1 n) ≤ n ≤ n^1. -/
private theorem primeIndicator_partial_sum_bigO :
    (fun n ↦ ∑ k ∈ Finset.Icc 1 n, ‖primeIndicator k‖) =O[atTop]
      fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  simp only [rpow_one]
  exact Asymptotics.isBigO_of_le atTop (fun n => by
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    rw [abs_of_nonneg (Nat.cast_nonneg n)]
    calc ∑ k ∈ Finset.Icc 1 n, ‖primeIndicator k‖
        ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => by
          simp only [primeIndicator]; split_ifs <;> simp)
      _ = (Finset.Icc 1 n).card := by simp
      _ ≤ n := by
          have hcard : (Finset.Icc 1 n).card ≤ n := by rw [Nat.card_Icc]; omega
          exact_mod_cast hcard)

/-- primeZeta equals LSeries of primeIndicator for Re(s) > 1.
Bridges tsum over Nat.Primes to tsum over ℕ via indicator/LSeries.term matching. -/
private theorem primeZeta_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    primeZeta s = LSeries primeIndicator s := by
  simp only [primeZeta, LSeries, LSeries.term, primeIndicator]
  -- Step 1: tsum_subtype bridges ∑' over Nat.Primes ↔ ∑' over ℕ with indicator
  -- Use trans since rw can't match Nat.Primes ≡ ↑{n : ℕ | n.Prime} definitionally
  trans (∑' n : ℕ, (({n : ℕ | n.Prime} : Set ℕ).indicator
    (fun (n : ℕ) => (↑n : ℂ) ^ (-s))) n)
  · exact tsum_subtype (α := ℂ) {n : ℕ | n.Prime} (fun (n : ℕ) => (↑n : ℂ) ^ (-s))
  -- Step 2: Match indicator terms with LSeries.term
  · congr 1; ext n
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hp : n.Prime
    · simp [hp, hp.ne_zero, one_div, cpow_neg]
    · -- ¬ n.Prime: indicator is 0, LSeries term is 0
      simp only [hp, ite_false]
      split_ifs with hn
      · rfl
      · simp

/-- Abel summation for primeZeta:
  primeZeta(s) = s * ∫ t in Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, primeIndicator k) * t^{-(s+1)}
for Re(s) > 1. -/
theorem primeZeta_eq_integral {s : ℂ} (hs : 1 < s.re) :
    primeZeta s = s * ∫ t in Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, primeIndicator k) * (↑t : ℂ) ^ (-(s + 1)) := by
  rw [primeZeta_eq_LSeries hs]
  exact LSeries_eq_mul_integral' primeIndicator (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith) primeIndicator_partial_sum_bigO

/-! ## Main theorem: corrected prime zeta extension

Combines the proved Abel summation with two analytic extension sub-lemmas:

1. **E₁ cancellation** (li-Mellin + log is entire):
   K(s) = log(s-1) + s·∫₂^∞ li(t)·t^{-(s+1)} dt extends to an entire function.
   Proof: IBP gives s·∫ li = li(2)·2^{-s} + ∫ t^{-s}/log t dt.
   Substitution u = log t gives E₁((s-1)·log 2), and E₁(z)+log(z)+γ is entire.

2. **π-li integral extension** (Landau MCT):
   F(s) = s·∫₂^∞ (π-li)·t^{-(s+1)} dt extends from {Re>1} to {Re>α}.
   Uses: R(t) = C·t^α - σ·(π-li) ≥ 0 (from PiLiHardBound), Landau's theorem
   for non-negative Dirichlet integrals.

Assembly: Q = K + F, using integral linearity and Abel summation. -/

/-- Hypothesis class for the corrected prime zeta extension.
When this is instantiated (via sorry in DeepBlockersResolved, or eventually via
proof), all theorems below become sorry-free.

The content: under the one-sided π-li bound σ·(π-li) ≤ C·x^α, the function
primeZeta(s) + log(s-1) extends analytically from {Re > 1} to {Re > α}.

Proof requires:
1. E₁ cancellation: li-Mellin + log(s-1) is entire
2. Landau MCT: non-negative Dirichlet integral analytic past α
3. Assembly via Abel summation + integral linearity -/
class CorrectedPrimeZetaExtensionHyp : Prop where
  proof : ∀ (α : ℝ), 1 / 2 < α → α < 1 → ∀ (C : ℝ), 0 < C →
    ∀ (σ_sign : ℝ), σ_sign = 1 ∨ σ_sign = -1 →
    PiLiHardBound α C σ_sign →
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        Q s = primeZeta s + Complex.log (s - 1)

/-- **Corrected prime zeta extension**: under the one-sided π-li bound,
primeZeta(s) + log(s-1) extends analytically from {Re > 1} to {Re > α}. -/
theorem corrected_prime_zeta_extension_proof
    [h : CorrectedPrimeZetaExtensionHyp]
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (C : ℝ) (hC : 0 < C) (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        Q s = primeZeta s + Complex.log (s - 1) :=
  h.proof α hα hα1 C hC σ_sign hσ hbound

end Aristotle.Standalone.PrimeZetaExtensionProof
