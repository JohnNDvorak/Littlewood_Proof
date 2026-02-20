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

SORRY COUNT: 1 (corrected_prime_zeta_extension)

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

/-! ## The corrected prime zeta extension

The key sorry: given the one-sided π-li bound, extend
  Q(s) := primeZeta(s) + Complex.log(s - 1)
analytically from {Re > 1} to {Re > α}.

### Proof strategy (~300 lines)

Define h(t) = C·t^α + σ·(li(t) - Π(t)) where Π(t) = Σ_{p^k ≤ t} 1/k.
The π-li bound gives h(t) ≥ 0 eventually (Π(t) - π(t) = O(√t/log t)).

1. **MCT convergence**: The non-negative Dirichlet integral
     D(s) = s · ∫_{T₀}^∞ h(t) · t^{-(s+1)} dt
   converges for Re(s) > α by monotone convergence + non-negativity.

2. **Parametric differentiation**: D is analytic on {Re > α} (same technique
   as PringsheimPsiAtom.witnessG_analyticOnNhd).

3. **li+log cancellation**: The function
     K(s) := log(s-1) + s · ∫_{T₀}^∞ li(t) · t^{-(s+1)} dt
   is entire. Proof: integration by parts gives
     s · ∫ li(t) · t^{-(s+1)} = li(T₀)·T₀^{-s} + ∫ t^{-s}/log(t) dt
   and with the substitution t = eᵘ:
     ∫ t^{-s}/log(t) dt = E₁((s-1)·log T₀)
   where E₁(z) + log(z) is entire (standard). So K(s) = log(s-1) + E₁(...) + ...
   has cancelling log singularities.

4. **Assembly**: primeZeta(s) = s · ∫ Π(t) · t^{-(s+1)} dt for Re(s) > 1.
   Using h: σ·primeZeta(s) = σ·s·∫ li·t^{-s-1} + s·C/(s-α) - D(s) + corrections.
   So Q(s) = log(s-1) + primeZeta(s) = K(s)/σ + [explicit analytic terms] - D(s)/σ.
   All terms are analytic on {Re > α}. -/

theorem corrected_prime_zeta_extension
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (C : ℝ) (hC : 0 < C) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hbound : PiLiHardBound α C σ) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        Q s = primeZeta s + Complex.log (s - 1) :=
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
