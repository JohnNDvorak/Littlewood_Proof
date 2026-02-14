/-
Direct proof infrastructure for the Landau-Schmidt oscillation theorem.

Under ¬RH, there exists a nontrivial zero ρ₀ with Re(ρ₀) > 1/2.
By the functional equation symmetry (zero_one_sub_zero), we can always
find such a zero. The Landau non-negative Dirichlet integral argument
then gives ψ(x) - x = Ω±(x^α) for any α ∈ (1/2, Re(ρ₀)).

## Main Results

* `exists_zero_re_gt_half_of_not_RH` : ¬RH → ∃ zero with Re > 1/2
* `landau_dirichlet_extension` : One-sided bound → ζ'/ζ has analytic extension (SORRY)
* `psi_omega_rpow_of_zero_above` : Zero with Re > α → ψ-x = Ω±(x^α) (PROVED)
* `psi_omega_lll_of_not_RH` : ¬RH → ψ-x = Ω±(√x · lll x) (PROVED)
* `pi_li_omega_lll_of_not_RH` : ¬RH → π-li = Ω±(√x/log x · lll x) (SORRY)

## Architecture

The Landau contradiction is cleanly decomposed:
  1. `landau_dirichlet_extension` (SORRY): The analytical core — under a one-sided
     bound on ψ, the Landau non-negative Dirichlet integral converges and provides
     an analytic function agreeing with ζ'/ζ in a punctured neighborhood.
  2. `zeta_logDeriv_no_analytic_extension` (PROVED, ZetaLogDerivNonAnalytic.lean):
     Any analytic F agreeing with ζ'/ζ near a zero → False.
  3. The contradiction follows in 2 lines (steps 1+2).

## Mathematical References

* Landau, "Über einen Satz von Tschebyschef" (1905)
* Schmidt, "Über die Anzahl der Primzahlen unter gegebener Grenze" (1903)
* Montgomery-Vaughan, "Multiplicative Number Theory I", §15.1
-/

import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.ZetaZeros.SupremumRealPart
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.Basic.OmegaNotation
import Littlewood.Basic.LogarithmicIntegral
import Littlewood.Aristotle.ZetaLogDerivNonAnalytic

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.LandauSchmidtDirect

open Filter Topology Asymptotics Complex
open ZetaZeros GrowthDomination

/-- Under ¬RH, there exists a nontrivial zero with Re > 1/2.
Proof: ¬RH gives ρ with Re(ρ) ≠ 1/2. If Re(ρ) > 1/2, done.
If Re(ρ) < 1/2, then 1-ρ is also a zero (functional equation)
and Re(1-ρ) = 1 - Re(ρ) > 1/2. -/
theorem exists_zero_re_gt_half_of_not_RH
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    ∃ ρ ∈ zetaNontrivialZeros, (1 : ℝ) / 2 < ρ.re := by
  unfold ZetaZeros.RiemannHypothesis at hRH
  push_neg at hRH
  obtain ⟨ρ, hρ, hne⟩ := hRH
  by_cases h : (1 : ℝ) / 2 < ρ.re
  · exact ⟨ρ, hρ, h⟩
  · push_neg at h
    have hlt : ρ.re < 1 / 2 := lt_of_le_of_ne h hne
    refine ⟨1 - ρ, zero_one_sub_zero hρ, ?_⟩
    simp only [Complex.sub_re, Complex.one_re]
    linarith

/-! ## Landau Dirichlet integral extension

The core analytical step: under a one-sided bound on ψ, the Landau non-negative
Dirichlet integral converges and provides an analytic extension of ζ'/ζ.

### Proof sketch (Landau 1905)

**Upper case** (σ = 1): Given ψ(x) - x ≤ C·x^α,
  define g(t) = C·t^α + t - ψ(t) ≥ 0 for large t.
  G(s) = s·∫₁^∞ g(t)·t^{-(s+1)} dt converges for Re(s) > α.
  On Re(s) > 1: G(s) = sC/(s-α) + s/(s-1) + ζ'/ζ(s).
  So F(s) := G(s) - sC/(s-α) - s/(s-1) is analytic on Re(s) > α
  and equals ζ'/ζ(s) on Re(s) > 1.
  By the identity principle, F = ζ'/ζ in a punctured neighborhood of any
  point s₀ with Re(s₀) > α (using connectedness of {Re > α} minus isolated poles).

**Lower case** (σ = -1): Given ψ(x) - x ≥ -C·x^α,
  define g(t) = C·t^α + ψ(t) - t ≥ 0.
  Same construction with F(s) = sC/(s-α) - s/(s-1) - G(s).

### Required ingredients (not in Mathlib)

1. Convergence of ∫₁^∞ f(t)·t^{-s-1} dt when f = O(t^α) and Re(s) > α
2. Analyticity of the resulting function (differentiation under the integral)
3. Identity principle on {Re > α} minus discrete pole set (connected by dim ≥ 2)
-/

/-- **Landau's Dirichlet integral extension**: Under a one-sided bound on ψ,
there exists an analytic function at any point s₀ in the extended half-plane
that agrees with ζ'/ζ in a punctured neighborhood.

This is the SOLE analytical sorry in the Landau-Schmidt argument.
The logical deduction (pole obstruction → contradiction) is fully proved.

SORRY: Requires non-negative Dirichlet integral convergence (Landau 1905),
analyticity of parametric integrals, and the identity principle on punctured
half-planes. See proof sketch above. -/
private theorem landau_dirichlet_extension
    (α : ℝ) (hα : 1 / 2 < α) (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (_hσ : σ = 1 ∨ σ = -1)
    (h_bound : ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α)
    (s₀ : ℂ) (hs₀_re : α < s₀.re) (hs₀_ne : s₀ ≠ 1) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, F s = deriv riemannZeta s / riemannZeta s := by
  sorry

/-! ## Landau contradictions — PROVED from the extension + pole obstruction -/

/-- **Landau upper contradiction**: If there exists a zero with Re > α and
ψ(x) - x is eventually bounded above by C·x^α, we get a contradiction.

PROVED: 2-line derivation from `landau_dirichlet_extension` (sorry, analytical core)
and `zeta_logDeriv_no_analytic_extension` (proved, pole obstruction). -/
private theorem landau_upper_contradiction
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ zetaNontrivialZeros)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_re : α < ρ₀.re)
    (C : ℝ) (hC : 0 < C)
    (h_bound : ∀ᶠ x in atTop, chebyshevPsi x - x ≤ C * x ^ α) :
    False := by
  -- Convert the bound to signed form (σ = 1)
  have h_signed : ∀ᶠ x in atTop, 1 * (chebyshevPsi x - x) ≤ C * x ^ α := by
    simpa only [one_mul] using h_bound
  -- Get the analytic extension at ρ₀
  obtain ⟨F, hF_anal, hF_eq⟩ := landau_dirichlet_extension α hα_half C hC 1
    (Or.inl rfl) h_signed ρ₀ hα_re
    (ZetaLogDerivNonAnalytic.nontrivial_zero_ne_one ρ₀ hρ₀)
  -- F is analytic at ρ₀ but agrees with ζ'/ζ which has a pole — contradiction
  exact ZetaLogDerivNonAnalytic.zeta_logDeriv_no_analytic_extension ρ₀ hρ₀ F hF_anal hF_eq

/-- **Landau lower contradiction**: If there exists a zero with Re > α and
ψ(x) - x is eventually bounded below by -C·x^α, we get a contradiction.

PROVED: Same structure as the upper case with σ = -1. -/
private theorem landau_lower_contradiction
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ zetaNontrivialZeros)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_re : α < ρ₀.re)
    (C : ℝ) (hC : 0 < C)
    (h_bound : ∀ᶠ x in atTop, -(C * x ^ α) ≤ chebyshevPsi x - x) :
    False := by
  -- Convert: -(C·x^α) ≤ ψ-x means (-1)·(ψ-x) ≤ C·x^α
  have h_signed : ∀ᶠ x in atTop, (-1) * (chebyshevPsi x - x) ≤ C * x ^ α := by
    filter_upwards [h_bound] with x hx
    linarith
  -- Get the analytic extension at ρ₀
  obtain ⟨F, hF_anal, hF_eq⟩ := landau_dirichlet_extension α hα_half C hC (-1)
    (Or.inr rfl) h_signed ρ₀ hα_re
    (ZetaLogDerivNonAnalytic.nontrivial_zero_ne_one ρ₀ hρ₀)
  -- F is analytic at ρ₀ but agrees with ζ'/ζ which has a pole — contradiction
  exact ZetaLogDerivNonAnalytic.zeta_logDeriv_no_analytic_extension ρ₀ hρ₀ F hF_anal hF_eq

/-! ## Schmidt oscillation — PROVED from Landau contradictions -/

/-- Schmidt's oscillation theorem (for ψ): If there exists a nontrivial zero ρ₀
with Re(ρ₀) > α > 1/2, then ψ(x) - x = Ω±(x^α).
PROVED from the two Landau contradictions above. -/
theorem psi_omega_rpow_of_zero_above
    (α : ℝ) (hα : 1 / 2 < α)
    (hzero : ∃ ρ ∈ zetaNontrivialZeros, α < ρ.re) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => x ^ α] := by
  obtain ⟨ρ₀, hρ₀, hα_re⟩ := hzero
  constructor
  -- Ω₊: ψ(x) - x ≥ c · x^α infinitely often
  · by_contra h_not
    have h_not_freq : ¬ ∃ᶠ x in atTop, chebyshevPsi x - x ≥ 1 * x ^ α := by
      intro hfreq; exact h_not ⟨1, one_pos, hfreq⟩
    have h_upper : ∀ᶠ x in atTop, chebyshevPsi x - x ≤ 1 * x ^ α :=
      (Filter.not_frequently.mp h_not_freq).mono fun _ hx => le_of_lt (not_le.mp hx)
    exact landau_upper_contradiction ρ₀ hρ₀ α hα hα_re 1 one_pos h_upper
  -- Ω₋: ψ(x) - x ≤ -c · x^α infinitely often
  · by_contra h_not
    have h_not_freq : ¬ ∃ᶠ x in atTop, chebyshevPsi x - x ≤ -(1 * x ^ α) := by
      intro hfreq; exact h_not ⟨1, one_pos, by simpa [neg_mul] using hfreq⟩
    have h_lower : ∀ᶠ x in atTop, -(1 * x ^ α) ≤ chebyshevPsi x - x :=
      (Filter.not_frequently.mp h_not_freq).mono fun _ hx => le_of_lt (not_le.mp hx)
    exact landau_lower_contradiction ρ₀ hρ₀ α hα hα_re 1 one_pos h_lower

/-- Under ¬RH, ψ(x) - x = Ω±(√x · lll x).
PROVED from Schmidt oscillation + growth domination. -/
theorem psi_omega_lll_of_not_RH (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x] := by
  obtain ⟨ρ₀, hρ₀, hρ₀_re⟩ := exists_zero_re_gt_half_of_not_RH hRH
  -- Choose α = (1/2 + Re(ρ₀))/2, so 1/2 < α < Re(ρ₀)
  set α := (1 / 2 + ρ₀.re) / 2 with hα_def
  have hα_half : 1 / 2 < α := by rw [hα_def]; linarith
  have hα_re : α < ρ₀.re := by rw [hα_def]; linarith
  -- ψ-x = Ω±(x^α) by Schmidt
  have hΩ := psi_omega_rpow_of_zero_above α hα_half ⟨ρ₀, hρ₀, hα_re⟩
  -- √x · lll x ≤ x^α eventually (growth domination)
  have h_dom := sqrt_mul_lll_le_rpow α hα_half
  -- √x · lll x ≥ 0 eventually
  have h_nn := sqrt_mul_lll_eventually_nonneg
  -- Transfer: Ω±(x^α) → Ω±(√x · lll x)
  exact hΩ.of_eventually_ge h_dom h_nn

/-- **π-li Landau oscillation under ¬RH**: π(x) - li(x) = Ω±(√x/log x · lll x).

This requires an independent Landau argument for the prime-counting function,
not derivable from the ψ oscillation by partial summation (the integral error
term O(x/log²x) dominates √x·lll x/log x).

PROOF SKETCH: Apply the Landau non-negative Dirichlet integral argument
to the generating function log ζ(s) = ∑ Λ(n)/(n^s·log n) and the integral
representation involving π(x). -/
theorem pi_li_omega_lll_of_not_RH (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  sorry

end Aristotle.LandauSchmidtDirect
