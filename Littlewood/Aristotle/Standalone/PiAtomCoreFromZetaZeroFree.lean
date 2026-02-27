/-
Decomposition of PiAtomHardCaseCorrectedCore into clean sub-lemmas.

The monolithic sorry at `piAtomHardCaseCorrectedCore_direct` in
`CorrectedPrimeZetaExtensionDirect.lean` is decomposed into:

1. **ζ zero-free on {Re > α}** (`zrf_ne_zero_of_piLiHardBound`):
   Under PiLiHardBound(α, C, σ), the function zrf(s) = (s-1)ζ(s) is
   non-vanishing on {Re > α}. This is PROVED from two sub-lemmas:
   (a) `pi_to_psi_transfer` (SORRY): PiLiHardBound → ψ bound with α' > α
   (b) ψ bound → witnessG analytic (ALL PROVED via SigmaLtOneHyp + LandauAbscissaHyp)
   (c) `zrf_ne_zero_of_witnessG_analytic` (PROVED via ZetaZeroFreeFromWitnessG): witnessG analytic → zrf ≠ 0
   The assembly for Re(s) ≥ 1 is trivially handled by ζ non-vanishing (Mathlib).

2. **Holomorphic logarithm on half-plane** (`analytic_log_on_halfPlane`):
   PROVED via covering map lift in HolomorphicLogOnHalfPlane.lean.

The assembly (`piAtomHardCaseCorrectedCore_of_zeroFreeAndLog`) is PROVED:
apply (2) to zrf (which is entire by `zrf_analyticAt`) using (1) for
non-vanishing, then verify exp(G(s)) = (s-1)ζ(s) for Re(s) > 1.

SORRY COUNT: 1 (pi_to_psi_transfer)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ZetaPoleCancellation
import Littlewood.Aristotle.Standalone.PiAtomHardCaseCorrectedCore
import Littlewood.Aristotle.Standalone.HolomorphicLogOnHalfPlane
import Littlewood.Aristotle.Standalone.SigmaLtOneFromPringsheimExtension
import Littlewood.Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination
import Littlewood.Aristotle.Standalone.ZetaZeroFreeFromWitnessG

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.PiAtomCoreFromZetaZeroFree

open Complex Filter Topology Set
open Aristotle.ZetaPoleCancellation
open Aristotle.Standalone.PiAtomHardCaseCorrectedCore
open Aristotle.PringsheimPsiAtom

/-! ## Sub-sorry 1a: π → ψ transfer via partial summation

Under PiLiHardBound(α, C, σ), for any α' ∈ (α, 1), derive a one-sided ψ bound:
  σ*(ψ(x) - x) ≤ C'*x^{α'}

The proof uses the prime-counting decomposition:
  π(x) - li(x) = (ψ(x)-x)/log(x) + O(√x/log(x)) + lower order terms
from PartialSummationPiLi.lean. Multiplying by log(x) and absorbing the
log(x) factor into the worse exponent α' > α (since x^α*log(x) ≤ C'*x^{α'}
eventually) gives the ψ bound.

Reference: Ingham, "The Distribution of Prime Numbers", Ch. 1. -/
theorem pi_to_psi_transfer
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (C : ℝ) (hC : 0 < C)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign)
    (α' : ℝ) (hα' : α < α') (hα'1 : α' < 1) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C' * x ^ α' := by
  sorry

/-! ## Sub-sorry 1c: witnessG analytic → zrf ≠ 0 (Landau zero-free argument)

If the witness function G(s) = s·∫₁^∞ g(t)·t^{-(s+1)} dt is analytic on {Re > α'}
(where g is the generating function from the ψ bound), then zrf has no zeros
in {Re > α'}.

**Proof sketch** (identity theorem + ODE uniqueness):
1. For Re(s) > 1: witnessG(s) = s·C'/(s-α') + σ·s/(s-1) + σ·ζ'/ζ(s)
   (from `witnessG_eq_formula`)
2. Rewrite via `corrected_logDeriv_eq`:
   witnessG(s) = s·C'/(s-α') + σ·(1 + zrf'/zrf(s))
3. Define φ(s) = (witnessG(s) - s·C'/(s-α') - σ) / σ, analytic on {Re > α'}.
4. For Re(s) > 1: φ(s) = zrf'(s)/zrf(s), so φ(s)·zrf(s) = zrf'(s).
5. Both sides are analytic on {Re > α'} and agree on {Re > 1}.
   By the identity theorem: φ·zrf = zrf' on all of {Re > α'}.
6. If zrf(s₀) = 0 for some s₀ with Re(s₀) > α': from step 5,
   deriv zrf(s₀) = φ(s₀)·0 = 0. By Leibniz rule on higher derivatives,
   all derivatives vanish at s₀. Since zrf is analytic, zrf ≡ 0 near s₀.
7. zrf entire and ≡ 0 near s₀ → zrf ≡ 0 everywhere. But zrf(1) = 1. □

Reference: Landau 1905; Montgomery-Vaughan §5.2. -/
theorem zrf_ne_zero_of_witnessG_analytic
    (α' : ℝ) (hα' : 1 / 2 < α') (hα'1 : α' < 1)
    (C' : ℝ) (hC' : 0 < C')
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C' * x ^ α')
    (h_anal : AnalyticOnNhd ℂ (witnessG C' α' σ_sign) {s : ℂ | α' < s.re}) :
    ∀ s : ℂ, α' < s.re → zrf s ≠ 0 :=
  Aristotle.Standalone.ZetaZeroFreeFromWitnessG.zrf_ne_zero_of_witnessG_analytic'
    α' hα' hα'1 C' hC' σ_sign hσ hbound h_anal

/-! ## Sub-lemma 1: ζ zero-free on {Re > α} under PiLiHardBound

Assembly of the zero-free argument from the two sub-sorries and proved
infrastructure.

For Re(s) ≥ 1: handled by ζ non-vanishing (`riemannZeta_ne_zero_of_one_le_re`).
For α < Re(s) < 1: pick α' ∈ (α, Re(s)), transfer π→ψ, chain through
SigmaLtOneHyp (PROVED) → LandauAbscissaHyp → witnessG analytic, then apply
the zero-free argument. -/
theorem zrf_ne_zero_of_piLiHardBound
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (C : ℝ) (hC : 0 < C)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign) :
    ∀ s : ℂ, α < s.re → zrf s ≠ 0 := by
  intro s hs
  -- Case split: Re(s) ≥ 1 vs α < Re(s) < 1
  by_cases h_ge : 1 ≤ s.re
  · -- Re(s) ≥ 1: use ζ non-vanishing on the closed half-plane {Re ≥ 1}
    rcases eq_or_ne s 1 with rfl | hs1
    · -- s = 1: zrf(1) = 1 ≠ 0
      simp
    · -- s ≠ 1, Re(s) ≥ 1: zrf(s) = (s-1)*ζ(s), both factors nonzero
      rw [zrf_of_ne hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1)
        (riemannZeta_ne_zero_of_one_le_re h_ge)
  · -- α < Re(s) < 1: Landau argument via witnessG
    push_neg at h_ge -- h_ge : s.re < 1
    -- Pick intermediate exponent α' ∈ (α, Re(s))
    obtain ⟨α', hαα', hα's⟩ := exists_between hs
    have hα'1 : α' < 1 := lt_trans hα's h_ge
    have hα'_half : 1 / 2 < α' := lt_trans hα hαα'
    -- Step 1: π → ψ transfer (sorry)
    obtain ⟨C', hC', hψ⟩ :=
      pi_to_psi_transfer α hα hα1 C hC σ_sign hσ hbound α' hαα' hα'1
    -- Step 2: ψ bound → witnessG analytic (ALL PROVED)
    -- SigmaLtOneHyp (B4) → LandauAbscissaHyp → witnessG analytic on {Re > α'}
    have h_landau : LandauAbscissaHyp :=
      Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination.landauAbscissaHyp_of_sigmaLtOne
        Aristotle.Standalone.SigmaLtOneFromPringsheimExtension.sigmaLtOneHyp_proved
    have h_anal := witnessG_analyticOnNhd h_landau C' hC' α' hα'_half σ_sign hσ hψ
    -- Step 3: witnessG analytic → zrf ≠ 0 (sorry)
    exact zrf_ne_zero_of_witnessG_analytic
      α' hα'_half hα'1 C' hC' σ_sign hσ hψ h_anal s hα's

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
