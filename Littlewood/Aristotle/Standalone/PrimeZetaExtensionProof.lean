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
import Mathlib.Analysis.Calculus.ParametricIntegral
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

/-- Non-negative Dirichlet integral with power bound is analytic. -/
theorem nonneg_dirichlet_integral_analyticOnNhd
    (R : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀) (β M : ℝ)
    (hR_nn : ∀ t, T₀ ≤ t → 0 ≤ R t)
    (hR_bound : ∀ t, T₀ ≤ t → R t ≤ M * t ^ β)
    (hR_meas : Measurable R) :
    AnalyticOnNhd ℂ
      (fun s => s * ∫ t in Ioi T₀, (↑(R t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      {s : ℂ | β < s.re} := by
  sorry

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
