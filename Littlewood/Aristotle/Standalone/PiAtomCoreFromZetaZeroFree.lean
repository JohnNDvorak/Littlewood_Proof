/-
Decomposition of PiAtomHardCaseCorrectedCore into clean sub-lemmas.

The monolithic sorry at `piAtomHardCaseCorrectedCore_direct` in
`CorrectedPrimeZetaExtensionDirect.lean` is decomposed into:

1. **ζ zero-free on {Re > α}** (`zrf_ne_zero_of_piLiHardBound`):
   Under PiLiHardBound(α, C, σ), the function zrf(s) = (s-1)ζ(s) is
   non-vanishing on {Re > α}. Proved from:
   (a) Re(s) ≥ 1: ζ non-vanishing via Mathlib (PROVED)
   (b) α < Re(s) < 1: π-based Landau zero-free argument (SORRY: `pi_landau_zeroFree`)
       Uses the Dirichlet integral of piGenFun = C·t^α - σ·(π(⌊t⌋)-li(t)),
       which converges for Re(s) > α by non-negativity (Landau/Pringsheim),
       giving analytic continuation of the combination P(s) - M_li(s),
       hence log((s-1)ζ(s)) extends analytically, hence ζ zero-free.

   NOTE: The previous approach via `pi_to_psi_transfer` (PiLiHardBound → ψ bound
   via Abel summation → witnessG analytic → zrf ≠ 0) was **architecturally wrong**:
   the Abel summation identity θ(x)-x = (π(x)-li(x))·log(x) - ∫(π-li)/t - 1
   introduces an integral error term bounded only by O(x/log x) (Chebyshev),
   which exceeds x^{α'} for any α' < 1. PNT would fix this but is not in Mathlib.
   The correct π-based Landau argument works directly with the π generating function.

2. **Holomorphic logarithm on half-plane** (`analytic_log_on_halfPlane`):
   PROVED via covering map lift in HolomorphicLogOnHalfPlane.lean.

The assembly (`piAtomHardCaseCorrectedCore_of_zeroFreeAndLog`) is PROVED:
apply (2) to zrf (which is entire by `zrf_analyticAt`) using (1) for
non-vanishing, then verify exp(G(s)) = (s-1)ζ(s) for Re(s) > 1.

SORRY COUNT: 0 (wired to PiPringsheimExtension.lean, which has 2 internal sorries)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ZetaPoleCancellation
import Littlewood.Aristotle.Standalone.PiAtomHardCaseCorrectedCore
import Littlewood.Aristotle.Standalone.HolomorphicLogOnHalfPlane
import Littlewood.Aristotle.Standalone.SigmaLtOneFromPringsheimExtension
import Littlewood.Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination
import Littlewood.Aristotle.Standalone.ZetaZeroFreeFromWitnessG
import Littlewood.Aristotle.CorrectionTermAnalyticity
import Littlewood.Aristotle.Standalone.PiPringsheimExtension

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.PiAtomCoreFromZetaZeroFree

open Complex Filter Topology Set
open Aristotle.ZetaPoleCancellation
open Aristotle.Standalone.PiAtomHardCaseCorrectedCore
open Aristotle.PringsheimPsiAtom
open Aristotle.CorrectionTermAnalyticity
open Aristotle.LandauLogZetaObstruction

/-! ## Sub-sorry 1a′: Analytic extension of primeZeta + log(s-1)

Under PiLiHardBound(α, C, σ), the function primeZeta(s) + log(s-1) extends
analytically from {Re > 1} to {Re > α}.

This is the Pringsheim/Landau argument for the π counting function:
the Dirichlet integral of the non-negative generating function
h(t) = C·t^α - σ·(π(⌊t⌋) - li(t)) converges for Re(s) > α,
giving analytic continuation of the prime zeta function minus
the Mellin transform of li, hence of primeZeta + log(s-1).

Reference: Landau 1905; Montgomery-Vaughan §5.2. -/
theorem primeZeta_plus_log_extends_of_piLiHardBound
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (C : ℝ) (hC : 0 < C)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        Q s = primeZeta s + Complex.log (s - 1) :=
  Aristotle.Standalone.PiPringsheimExtension.primeZeta_plus_log_extends_of_piLiHardBound
    α hα hα1 C hC σ_sign hσ hbound

/-! ## Sub-sorry 1a: π-based Landau zero-free argument

Under PiLiHardBound(α, C, σ), for α < Re(s) < 1, prove zrf(s) ≠ 0.

**Proof** (identity theorem, from `primeZeta_plus_log_extends_of_piLiHardBound`):
1. Get Q analytic on {Re > α} with Q(s) = primeZeta(s) + log(s-1) on {Re > 1}.
2. G(s) = Q(s) + correctionTerm(s) is analytic on {Re > α} (correctionTerm
   is analytic on {Re > 1/2} ⊃ {Re > α}).
3. For Re(s) > 1: exp(G(s)) = exp(H_zeta_log(s) + log(s-1))
     = ζ(s)·(s-1) = zrf(s).
4. Identity theorem: exp∘G - zrf ≡ 0 on {Re > α}.
5. Hence zrf(s) = exp(G(s)) ≠ 0.

Reference: Landau 1905; Montgomery-Vaughan §5.2. -/
theorem pi_landau_zeroFree
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (C : ℝ) (hC : 0 < C)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign)
    (s : ℂ) (hs : α < s.re) (hs1 : s.re < 1) :
    zrf s ≠ 0 := by
  -- Step 1: Get Q extending primeZeta + log(s-1) to {Re > α}
  obtain ⟨Q, hQ_anal, hQ_eq⟩ := primeZeta_plus_log_extends_of_piLiHardBound
    α hα hα1 C hC σ_sign hσ hbound
  -- Step 2: correctionTerm is analytic on {Re > α} since α > 1/2
  have hCT_anal : AnalyticOnNhd ℂ correctionTerm {z : ℂ | α < z.re} :=
    correctionTerm_analyticOnNhd α hα
  -- Step 3: exp(Q + correctionTerm) - zrf is analytic on {Re > α}
  have hh_anal : AnalyticOnNhd ℂ (fun z => exp (Q z + correctionTerm z) - zrf z)
      {z : ℂ | α < z.re} := by
    intro z hz
    exact (analyticAt_cexp.comp ((hQ_anal z hz).add (hCT_anal z hz))).sub (zrf_analyticAt z)
  -- Step 4: Base point s₀ = 2 is in {Re > α}
  have h2_in : (2 : ℂ) ∈ {z : ℂ | α < z.re} := by
    show α < (2 : ℂ).re; simp; linarith
  -- Step 5: exp(G) - zrf = 0 on {Re > 1} ⊇ nhd of 2
  have hh_ev : (fun z => exp (Q z + correctionTerm z) - zrf z) =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have h_open : IsOpen {z : ℂ | (1 : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h2_mem : (2 : ℂ) ∈ {z : ℂ | (1 : ℝ) < z.re} := by
      show (1 : ℝ) < (2 : ℂ).re; simp
    filter_upwards [h_open.mem_nhds h2_mem] with z hz
    simp only [Pi.zero_apply]
    have hz_ne1 : z ≠ 1 := by
      intro heq; subst heq; simp at hz
    have hsub_ne : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne1
    -- Q(z) + correctionTerm(z) = (primeZeta(z) + log(z-1)) + correctionTerm(z)
    rw [hQ_eq z hz]
    -- Rearrange: (primeZeta + log(z-1)) + correctionTerm = (primeZeta + correctionTerm) + log(z-1)
    have h_rearr : primeZeta z + log (z - 1) + correctionTerm z =
        (primeZeta z + correctionTerm z) + log (z - 1) := by ring
    rw [h_rearr]
    -- primeZeta + correctionTerm = H_zeta_log (by H_zeta_log_eq_add)
    rw [← H_zeta_log_eq_add hz]
    -- exp(H_zeta_log(z) + log(z-1)) = exp(H_zeta_log(z)) * exp(log(z-1))
    rw [exp_add]
    -- = ζ(z) * (z-1) = zrf(z)
    rw [H_zeta_log_exp_eq hz, exp_log hsub_ne, zrf_of_ne hz_ne1]
    ring
  -- Step 6: Identity theorem → exp(G) - zrf ≡ 0 on {Re > α}
  have hh_zero : EqOn (fun z => exp (Q z + correctionTerm z) - zrf z) 0 {z : ℂ | α < z.re} :=
    hh_anal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_re_gt α).isPreconnected h2_in hh_ev
  -- Step 7: At s, exp(G(s)) = zrf(s), hence zrf(s) ≠ 0
  have h_at_s := hh_zero hs
  simp only [Pi.zero_apply] at h_at_s
  rw [sub_eq_zero] at h_at_s
  rw [← h_at_s]
  exact exp_ne_zero _

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

For Re(s) ≥ 1: handled by ζ non-vanishing (`riemannZeta_ne_zero_of_one_le_re`).
For α < Re(s) < 1: handled by `pi_landau_zeroFree` (sorry). -/
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
  · -- α < Re(s) < 1: π-based Landau zero-free argument
    push_neg at h_ge
    exact pi_landau_zeroFree α hα hα1 C hC σ_sign hσ hbound s hs h_ge

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
