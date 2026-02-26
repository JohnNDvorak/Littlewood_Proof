/-
Decomposition of PiAtomHardCaseCorrectedCore into two clean sub-lemmas.

The monolithic sorry at `piAtomHardCaseCorrectedCore_direct` in
`CorrectedPrimeZetaExtensionDirect.lean` is decomposed into:

1. **ζ zero-free on {Re > α}** (`zrf_ne_zero_of_piLiHardBound`):
   Under PiLiHardBound(α, C, σ), the function zrf(s) = (s-1)ζ(s) is
   non-vanishing on {Re > α}. This follows from:
   (a) π→ψ partial summation transfer: PiLiHardBound → ψ bound
   (b) Landau–Pringsheim convergence (B4, PROVED): ψ bound → genFun integral converges
   (c) Algebraic identity: convergence → ζ'/ζ has no poles → ζ zero-free

2. **Holomorphic logarithm on half-plane** (`analytic_log_on_halfPlane`):
   For f entire and non-vanishing on {Re > α}, ∃ g analytic on {Re > α}
   with exp(g) = f. This is standard complex analysis:
   the half-plane is convex (hence simply connected), so every non-vanishing
   holomorphic function has a holomorphic logarithm.

The assembly (`piAtomHardCaseCorrectedCore_of_zeroFreeAndLog`) is PROVED:
apply (2) to zrf (which is entire by `zrf_analyticAt`) using (1) for
non-vanishing, then verify exp(G(s)) = (s-1)ζ(s) for Re(s) > 1.

SORRY COUNT: 1 (zrf_ne_zero_of_piLiHardBound)
analytic_log_on_halfPlane is PROVED via covering map lift in HolomorphicLogOnHalfPlane.lean.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ZetaPoleCancellation
import Littlewood.Aristotle.Standalone.PiAtomHardCaseCorrectedCore
import Littlewood.Aristotle.Standalone.HolomorphicLogOnHalfPlane

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.PiAtomCoreFromZetaZeroFree

open Complex Filter Topology Set
open Aristotle.ZetaPoleCancellation
open Aristotle.Standalone.PiAtomHardCaseCorrectedCore

/-! ## Sub-lemma 1: ζ zero-free on {Re > α} under PiLiHardBound

Under the one-sided bound σ*(π(x) - li(x)) ≤ C*x^α with 1/2 < α < 1,
the Riemann zeta function has no zeros in the half-plane {Re(s) > α}.

**Proof sketch** (ψ-pathway):
1. PiLiHardBound → one-sided ψ-bound via partial summation (θ-ψ transfer)
2. ψ-bound → Dirichlet integral ∫ genFun*t^{-(σ₀+1)} converges for σ₀ > α
   (from SigmaLtOneHyp, PROVED via Pringsheim extension)
3. The algebraic identity gives ζ'/ζ(s) = [integral - C*s/(s-α) - σ*s/(s-1)] / σ,
   which is analytic for Re(s) > α, s ≠ 1. Hence ζ has no zeros.

Equivalently, zrf(s) = (s-1)*ζ(s) ≠ 0 on {Re > α}.
At s = 1: zrf(1) = 1 ≠ 0 (residue value).
At s ≠ 1 with Re(s) > α: ζ(s) ≠ 0 from the Landau argument.

Reference: Landau 1905; Montgomery-Vaughan §5.2. -/
theorem zrf_ne_zero_of_piLiHardBound
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (C : ℝ) (hC : 0 < C)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign) :
    ∀ s : ℂ, α < s.re → zrf s ≠ 0 := by
  sorry

/-! ## Sub-lemma 2: Holomorphic logarithm on half-plane

If f is analytic and non-vanishing on {Re > α}, then there exists an analytic
function g on {Re > α} with exp(g) = f.

**Proof**: The half-plane {Re > α} is convex, hence simply connected.
By the Monodromy Theorem (or direct construction via path integral of f'/f),
every non-vanishing holomorphic function on a simply connected domain admits
a holomorphic logarithm.

Alternative construction: Fix a base point s₀ = 2. Define
  g(s) = log(f(2)) + ∫_{2}^{s} f'(w)/f(w) dw
along the straight-line path [2, s] (which lies in the convex set {Re > α}).
Then exp(g(s)) = f(s) by the ODE theory of exp.

Reference: Conway, "Functions of One Complex Variable", §IV.6, Theorem 6.13. -/
theorem analytic_log_on_halfPlane (α : ℝ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f {s : ℂ | α < s.re})
    (hf_ne : ∀ s : ℂ, α < s.re → f s ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, α < s.re → exp (g s) = f s :=
  Aristotle.Standalone.analytic_log_on_halfPlane' α f hf hf_ne

/-! ## Assembly: PiAtomHardCaseCorrectedCore from the two sub-lemmas

Apply `analytic_log_on_halfPlane` to `zrf` (which is entire) using
`zrf_ne_zero_of_piLiHardBound` for non-vanishing. This gives G with
exp(G(s)) = zrf(s) = (s-1)*ζ(s) on {Re > α} ⊃ {Re > 1}. -/
theorem piAtomHardCaseCorrectedCore_of_zeroFreeAndLog :
    PiAtomHardCaseCorrectedCore := by
  intro α hα hα1 C hC σ_sign hσ hbound
  -- Step 1: zrf is non-vanishing on {Re > α}
  have h_ne := zrf_ne_zero_of_piLiHardBound α hα hα1 C hC σ_sign hσ hbound
  -- Step 2: zrf is analytic on {Re > α} (in fact, entire)
  have h_anal : AnalyticOnNhd ℂ zrf {s : ℂ | α < s.re} :=
    fun s _ => zrf_analyticAt s
  -- Step 3: Apply holomorphic log to get G with exp(G) = zrf on {Re > α}
  obtain ⟨G, hG_anal, hG_eq⟩ := analytic_log_on_halfPlane α zrf h_anal h_ne
  -- Step 4: G is the desired witness
  exact ⟨G, hG_anal, fun s hs => by
    have hs_α : α < s.re := by linarith
    -- exp(G(s)) = zrf(s) = (s-1)*ζ(s) since s ≠ 1
    have hs1 : s ≠ 1 := by
      intro h; have := congr_arg Complex.re h; simp at this; linarith
    rw [hG_eq s hs_α, zrf_of_ne hs1]⟩

end Aristotle.Standalone.PiAtomCoreFromZetaZeroFree
