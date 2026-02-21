/-
Construction of PiAtomHardCaseCorrectedCore from the corrected prime zeta extension.

The corrected core requires: given σ*(π(x) - li(x)) ≤ C*x^α with 1/2 < α < 1,
construct G analytic on {Re > α} with exp(G) = (s-1)*ζ(s) for Re(s) > 1.

## Proof Strategy

For Re(s) > 1:
  log((s-1)*ζ(s)) = log(s-1) + log ζ(s)
                   = log(s-1) + H_zeta_log(s)
                   = log(s-1) + primeZeta(s) + correctionTerm(s)

The correctionTerm is analytic on {Re > 1/2} ⊃ {Re > α} (CorrectionTermAnalyticity).
The key claim: log(s-1) + primeZeta(s) extends analytically from {Re > 1}
to {Re > α}. This uses the non-negative generating function
  h(t) = C*t^α + σ*(li(t) - π(t)) ≥ 0   (eventually)
whose Dirichlet integral extends to {Re > α} by MCT + non-negativity.
The li-Mellin transform has a -log(s-1) singularity at s=1 that exactly
cancels the log(s-1) term (via the exponential integral identity:
E₁(z) + log(z) is entire).

SORRY COUNT: 1 atomic sorry
  corrected_prime_zeta_extension — analytic continuation of primeZeta + log(s-1)
  TRUE: follows from MCT (non-negative Dirichlet integral), E₁ identity
  (li-Mellin + log(s-1) cancellation), and algebraic assembly.

Previously decomposed into 3 sub-sorries (MCT, E₁, assembly), but the
assembly sorry (6c) was FALSE (took D, K without their formulas). Merged
into a single true sorry with clear mathematical statement.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.PiAtomHardCaseCorrectedCore
import Littlewood.Aristotle.CorrectionTermAnalyticity

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.PiCorrectedCoreFromPrimeZetaExtension

open Complex Real Filter Topology Set
open Aristotle.CorrectionTermAnalyticity
open Aristotle.LandauLogZetaObstruction
open Aristotle.Standalone.PiAtomHardCaseCorrectedCore

/-! ## Corrected prime zeta extension (analytic continuation)

Under the one-sided bound σ·(π(x) - li(x)) ≤ C·x^α, the function
primeZeta(s) + log(s-1) extends analytically from {Re > 1} to {Re > α}.

Proof sketch:
1. Define h(t) = C·t^α + σ·(li(t) - π(t)) ≥ 0 eventually.
2. The Dirichlet integral D(s) = s · ∫₂^∞ h(t)·t^{-(s+1)} dt converges for
   Re(s) > α by MCT (h ≥ 0) and is analytic by parametric differentiation.
3. K(s) := log(s-1) + s · ∫₂^∞ li(t)·t^{-(s+1)} dt is analytic on {Re > α}
   because the li-Mellin transform has a -log(s-1) singularity at s=1 that
   exactly cancels log(s-1) (exponential integral identity: E₁(z) + log z is entire).
4. Assembly: Q(s) = K(s) - D(s)/σ + s·C·2^{α-s}/(σ·(s-α)) + boundary
   is analytic on {Re > α} and equals primeZeta(s) + log(s-1) for Re(s) > 1.

Reference: Montgomery-Vaughan §5.2, Titchmarsh §3.15. -/

/-- **Corrected prime zeta extension**: under the one-sided π-li bound,
primeZeta(s) + log(s-1) extends analytically from {Re > 1} to {Re > α}. -/
theorem corrected_prime_zeta_extension
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (C : ℝ) (hC : 0 < C) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hbound : PiLiHardBound α C σ) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        Q s = primeZeta s + Complex.log (s - 1) := by
  sorry

/-! ## Formula verification helpers -/

private lemma s_minus_one_ne_zero {s : ℂ} (hs : 1 < s.re) : s - 1 ≠ 0 := by
  intro h
  have : s.re = 1 := by
    have := congr_arg Complex.re h
    simp at this
    linarith
  linarith

/-! ## Main theorem: PiAtomHardCaseCorrectedCore -/

/-- **PiAtomHardCaseCorrectedCore proved** from the corrected prime zeta extension.

Constructs G(s) = Q(s) + correctionTerm(s), where:
- Q is the analytic extension of primeZeta + log(s-1) to {Re > α}
- correctionTerm is the higher-order Euler product correction, analytic on {Re > 1/2}

The formula exp(G(s)) = (s-1)*ζ(s) on {Re > 1} follows from:
  G = Q + correction = [primeZeta + log(s-1)] + correction = log(s-1) + H_zeta_log
  exp(G) = exp(log(s-1)) * exp(H_zeta_log) = (s-1) * ζ(s) -/
theorem piAtomHardCaseCorrectedCore_proved :
    PiAtomHardCaseCorrectedCore := by
  intro α hα hα1 C hC σ hσ hbound
  obtain ⟨Q, hQ_anal, hQ_eq⟩ := corrected_prime_zeta_extension α hα hα1 C hC σ hσ hbound
  -- G(s) = Q(s) + correctionTerm(s)
  refine ⟨fun s => Q s + correctionTerm s, ?_, ?_⟩
  · -- Analyticity: Q analytic on {Re > α}, correction analytic on {Re > α}
    exact hQ_anal.add
      ((correctionTerm_analyticOnNhd α hα).mono (fun s hs => by exact hs))
  · -- Formula: exp(G(s)) = (s-1)*ζ(s) for Re(s) > 1
    intro s hs
    show exp (Q s + correctionTerm s) = (s - 1) * riemannZeta s
    -- Step 1: Q(s) + correction(s) = [primeZeta(s) + log(s-1)] + correction(s)
    have hQs := hQ_eq s hs
    -- Step 2: primeZeta + correction = H_zeta_log (from CorrectionTermAnalyticity)
    have hH := (H_zeta_log_eq_add hs).symm
    -- Step 3: So G(s) = log(s-1) + H_zeta_log(s)
    have hG_eq : Q s + correctionTerm s = Complex.log (s - 1) + H_zeta_log s := by
      rw [hQs, ← hH]; ring
    -- Step 4: exp(log(s-1) + H_zeta_log) = exp(log(s-1)) * exp(H_zeta_log)
    rw [hG_eq, Complex.exp_add]
    -- Step 5: exp(log(s-1)) = s-1  and  exp(H_zeta_log) = ζ(s)
    rw [Complex.exp_log (s_minus_one_ne_zero hs), H_zeta_log_exp_eq hs]

end Aristotle.Standalone.PiCorrectedCoreFromPrimeZetaExtension
