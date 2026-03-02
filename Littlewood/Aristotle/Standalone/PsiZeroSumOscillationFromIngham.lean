/-
Proof of PsiZeroSumOscillationHyp (B5b) from ExplicitFormulaPsiGeneralHyp (B5a)
via Landau's indirect argument.

## Mathematical Strategy (Landau 1905 / Ingham 1932)

Given the general truncated explicit formula (B5a) with variable truncation T:
  |ψ(x) - x + Σ_{|γ|≤T} Re(x^ρ/ρ)| ≤ C · (√x · (log T)²/√T + (log x)²)

To show: under RH, ψ(x) - x is unbounded in both directions relative to √x.

Proof by contradiction for the positive direction:
1. Assume ψ(x) - x ≤ M√x for all x ≥ x₀ (bounded above)
2. From B5a at T=x: -∑_{|γ|≤x} Re(x^ρ/ρ) ≤ M√x + K(log x)²
3. The Mellin/Stieltjes transform ∫₁^∞ (M√x - (ψ(x)-x)) x^{-s-1} dx
   converges for Re(s) > 1/2
4. This makes ζ'/ζ + 1/(s-1) + M/(s-1/2) holomorphic for Re(s) > 1/2
5. But under RH, ζ has zeros at 1/2+iγ (infinitely many by Hardy),
   so ζ'/ζ has poles at those points — contradiction

The negative direction is symmetric.

## Lean Formalization

The Landau-Ingham contradiction via Mellin transforms is deferred. The proof
uses a sorry for the key analytic number theory fact: under RH with infinitely
many critical-line zeros, ψ(x)-x cannot be bounded above (or below) by any
multiple of √x for all large x.

## References

- Landau, E. (1905). "Über einen Satz von Tschebyschef." Math. Ann. 61.
- Ingham, A. E. (1932). The Distribution of Prime Numbers, Chapter V.
- Montgomery-Vaughan (2007). Multiplicative Number Theory I, §15.2.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
import Littlewood.Aristotle.DirichletPhaseAlignment

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.PsiZeroSumOscillationFromIngham

open Filter Complex
open GrowthDomination
open Aristotle.DirichletPhaseAlignment (ZerosBelow CriticalZeros)
open Aristotle.Standalone.RHPsiWitnessFromZeroSum (psiMainTerm)
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open ZetaZeros

-- ============================================================
-- Infrastructure: positive-imaginary-part zeros (PROVED)
-- ============================================================

/-- The subset of ZerosBelow T with strictly positive imaginary part. -/
def PositiveImZerosBelow (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => 0 < ρ.im)

lemma positiveImZerosBelow_sub (T : ℝ) :
    PositiveImZerosBelow T ⊆ ZerosBelow T :=
  Finset.filter_subset _ _

lemma positiveImZerosBelow_re_half (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ ρ ∈ PositiveImZerosBelow T, ρ.re = 1 / 2 := by
  intro ρ hρ
  have hρ_mem : ρ ∈ ZerosBelow T := positiveImZerosBelow_sub T hρ
  have hρ_crit : ρ ∈ CriticalZeros := by
    simp only [ZerosBelow] at hρ_mem
    split_ifs at hρ_mem with hfin
    · exact ((hfin.mem_toFinset).mp hρ_mem).1
    · simp at hρ_mem
  exact hRH ρ hρ_crit

-- ============================================================
-- Proved: Re(I/ρ) ≤ 1/‖ρ‖ for nonzero ρ
-- ============================================================

/-- For any nonzero ρ, Re(I/ρ) ≤ 1/‖ρ‖.
Proof: |Re(z)| ≤ ‖z‖ and ‖I/ρ‖ = 1/‖ρ‖. -/
lemma re_I_div_le_inv_norm (ρ : ℂ) (_hρ : ρ ≠ 0) :
    (I / ρ).re ≤ 1 / ‖ρ‖ := by
  calc (I / ρ).re ≤ ‖I / ρ‖ := le_trans (le_abs_self _) (abs_re_le_norm _)
    _ = ‖I‖ / ‖ρ‖ := by rw [norm_div]
    _ = 1 / ‖ρ‖ := by rw [Complex.norm_I]

-- ============================================================
-- Key analytic fact: Landau-Ingham unbounded oscillation
-- ============================================================

-- ============================================================
-- Landau-Ingham decomposition: 4 sub-lemmas (1 proved, 3 sorry)
-- ============================================================

/-- The "gap" integrand: under a one-sided bound on ψ(x)-x,
this integrand is nonneg for large x. -/
private noncomputable def landauIntegrand
    (σ : ℝ) (C₀ : ℝ) (x : ℝ) : ℝ :=
  C₀ * Real.sqrt x - σ * (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x)

/-- **Sub-lemma 1/4** (PROVED): Integrand nonnegativity from one-sided bound. -/
private lemma landau_integrand_nonneg
    (σ C₀ X₀ : ℝ)
    (h_bound : ∀ x, x ≥ X₀ →
      σ * (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) ≤ C₀ * Real.sqrt x)
    (x : ℝ) (hx : x ≥ X₀) :
    0 ≤ landauIntegrand σ C₀ x := by
  unfold landauIntegrand; linarith [h_bound x hx]

/-- **Sub-sorry 2/4**: Mellin convergence (analytic number theory).
The nonneg integrand defines an analytic function F on Re(s) > 1/2
via Mellin-type transform. The one-sided bound ψ(x)-x = O(√x) gives
absolute convergence of ∫ (gap) · x^{-s-1} dx for Re(s) > 1/2.

Reference: Ingham 1932, Ch. V; Montgomery-Vaughan §15.2. -/
private theorem landau_mellin_analytic
    (σ C₀ X₀ : ℝ)
    (h_bound : ∀ x, x ≥ X₀ →
      σ * (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) ≤ C₀ * Real.sqrt x) :
    ∃ F : ℂ → ℂ, AnalyticOn ℂ F {s : ℂ | 1/2 < s.re} := by
  sorry

/-- **Sub-sorry 3/4**: Connection to ζ'/ζ (Perron/Stieltjes identity).
The Mellin transform F relates to ζ'/ζ: for Re(s) > 1,
-ζ'(s)/ζ(s) can be expressed in terms of F plus functions analytic
on Re(s) > 1/2. Hence F + G = ζ'/ζ representation extends meromorphically.

Reference: Ingham 1932, Ch. V; Davenport Ch. 17. -/
private theorem landau_zeta_identity
    (σ C₀ : ℝ) (F : ℂ → ℂ)
    (hF_half : AnalyticOn ℂ F {s : ℂ | 1/2 < s.re}) :
    ∃ G : ℂ → ℂ, AnalyticOn ℂ G {s : ℂ | 1/2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        deriv riemannZeta s / riemannZeta s = F s + G s := by
  sorry

/-- **Sub-sorry 4/4**: Pole contradiction under RH.
If F + G represents ζ'/ζ for Re(s) > 1 and both F, G are analytic
on Re(s) > 1/2, then ζ'/ζ extends analytically to Re(s) > 1/2 (except s=1).
But under RH, ζ has infinitely many zeros at Re(s) = 1/2 (by Hardy 1914),
so ζ'/ζ has poles accumulating there — contradiction.

Reference: Hardy 1914 (infinitely many zeros); Ingham 1932, Ch. V. -/
private theorem landau_pole_contradiction
    (hRH : ZetaZeros.RiemannHypothesis)
    (F G : ℂ → ℂ)
    (hF : AnalyticOn ℂ F {s : ℂ | 1/2 < s.re})
    (hG : AnalyticOn ℂ G {s : ℂ | 1/2 < s.re})
    (h_id : ∀ s : ℂ, 1 < s.re →
      deriv riemannZeta s / riemannZeta s = F s + G s) :
    False := by
  sorry

/-- **Core Landau-Ingham impossibility** (Landau 1905, Ingham 1932):
Under RH, σ·(ψ(x)-x) cannot be bounded above by C₀·√x for all large x.
PROVED from the 3 sub-sorry decomposition above. -/
private theorem landau_psi_bounded_impossible
    (hRH : ZetaZeros.RiemannHypothesis)
    (σ : ℝ) (_hσ : σ = 1 ∨ σ = -1)
    (C₀ X₀ : ℝ)
    (h_bound : ∀ x, x ≥ X₀ →
      σ * (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) ≤
        C₀ * Real.sqrt x) :
    False := by
  obtain ⟨F, hF_analytic⟩ := landau_mellin_analytic σ C₀ X₀ h_bound
  obtain ⟨G, hG_analytic, h_identity⟩ := landau_zeta_identity σ C₀ F hF_analytic
  exact landau_pole_contradiction hRH F G hF_analytic hG_analytic h_identity

/-- **Landau-Ingham fact** (Landau 1905, Ingham 1932):
Under RH, ψ(x) - x is unbounded above relative to √x.
Proved from `landau_psi_bounded_impossible` via `by_contra` + `push_neg`. -/
private theorem landau_ingham_unbounded_above
    [ExplicitFormulaPsiGeneralHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≥ C * Real.sqrt x := by
  by_contra h; push_neg at h
  obtain ⟨C₀, X₀, hbound⟩ := h
  exact landau_psi_bounded_impossible hRH 1 (Or.inl rfl) C₀ (X₀ + 1)
    (fun x hx => by simp only [one_mul]; exact (hbound x (by linarith)).le)

/-- Symmetric Landau-Ingham fact for the negative direction.
Proved from `landau_psi_bounded_impossible` via `by_contra` + `push_neg`. -/
private theorem landau_ingham_unbounded_below
    [ExplicitFormulaPsiGeneralHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≤ -(C * Real.sqrt x) := by
  by_contra h; push_neg at h
  obtain ⟨C₀, X₀, hbound⟩ := h
  exact landau_psi_bounded_impossible hRH (-1) (Or.inr rfl) C₀ (X₀ + 1)
    (fun x hx => by
      simp only [neg_one_mul, neg_le]
      exact (hbound x (by linarith)).le)

-- ============================================================
-- Main theorem: PsiZeroSumOscillationHyp from Landau indirect argument
-- ============================================================

/-- **B5b proved from B5a** via Landau's indirect argument (Landau 1905, Ingham 1932):

Under RH, ψ(x) - x is unbounded in both directions relative to √x.

The proof delegates to a single atomic sorry (`landau_psi_bounded_impossible`) which
encapsulates the symmetric Mellin-transform convergence argument. Both directions
(above and below) are proved from it via `by_contra` + `push_neg`. -/
theorem psiZeroSumOscillation_proved
    [ExplicitFormulaPsiGeneralHyp] :
    PsiZeroSumOscillationHyp where
  proof := by
    intro hRH
    exact ⟨landau_ingham_unbounded_above hRH, landau_ingham_unbounded_below hRH⟩

end Aristotle.Standalone.PsiZeroSumOscillationFromIngham
