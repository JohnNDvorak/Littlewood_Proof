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
import Littlewood.Aristotle.ZetaLogDerivInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.PsiZeroSumOscillationFromIngham

open Filter Complex Topology
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

-- NOTE: The former sorry's `landau_mellin_analytic` and `landau_zeta_identity`
-- have been REMOVED. `landau_zeta_identity` was mathematically impossible:
-- it required F + G = ζ'/ζ on {Re > 1} with both F, G analytic on {Re > 1/2},
-- but ζ'/ζ has a simple pole at s = 1 ∈ {Re > 1/2} (proved in
-- `landau_pole_contradiction` below). The Landau-Ingham impossibility is now
-- captured as a single atomic sorry in `landau_psi_bounded_impossible`.

/-- **Sub-lemma 4/4** (PROVED): Pole contradiction.
If F + G represents ζ'/ζ for Re(s) > 1 and both F, G are analytic
on Re(s) > 1/2, then F + G is continuous at s = 1. But ζ'/ζ has a
simple pole at s = 1 (from `neg_zeta_logderiv_pole_at_one`).
Multiplying by (s-1): limit is 0 (from continuity) but also -1 (from pole).
Contradiction via `tendsto_nhds_unique`.

Note: RH is not needed — the hypotheses are already inconsistent due to
the s = 1 pole alone. The `hRH` parameter is kept for interface compatibility. -/
private theorem landau_pole_contradiction
    (hRH : ZetaZeros.RiemannHypothesis)
    (F G : ℂ → ℂ)
    (hF : AnalyticOn ℂ F {s : ℂ | 1/2 < s.re})
    (hG : AnalyticOn ℂ G {s : ℂ | 1/2 < s.re})
    (h_id : ∀ s : ℂ, 1 < s.re →
      deriv riemannZeta s / riemannZeta s = F s + G s) :
    False := by
  -- The set {Re > 1/2} is open and contains 1
  have hS_open : IsOpen {s : ℂ | (1 : ℝ) / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h1_mem : (1 : ℂ) ∈ {s : ℂ | (1 : ℝ) / 2 < s.re} := by
    show (1 : ℝ) / 2 < (1 : ℂ).re; simp [Complex.one_re]; norm_num
  -- F + G is continuous at s = 1
  have hFG_contAt : ContinuousAt (fun s => F s + G s) (1 : ℂ) :=
    (hF.continuousOn.continuousAt (hS_open.mem_nhds h1_mem)).add
      (hG.continuousOn.continuousAt (hS_open.mem_nhds h1_mem))
  -- Pole data: -ζ'/ζ(s) = g(s)/(s-1) near s = 1, g analytic, g(1) = 1
  obtain ⟨g, hg_an, hg1, hg_eq⟩ :=
    Aristotle.ZetaLogDerivInfra.neg_zeta_logderiv_pole_at_one
  -- The filter 𝓝[{Re > 1}] 1 is nontrivial (1 is on the boundary of {Re > 1})
  have hL_neBot : (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)).NeBot := by
    refine Filter.NeBot.mk ?_
    intro hbot
    have h_empty : (∅ : Set ℂ) ∈ 𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ) := by
      rw [hbot]; exact Filter.mem_bot
    rw [mem_nhdsWithin] at h_empty
    obtain ⟨U, hU_open, h1U, hU_sub⟩ := h_empty
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU_open 1 h1U
    exact absurd (hU_sub ⟨hball (by
        simp only [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left, Complex.norm_real]
        rw [Real.norm_of_nonneg (half_pos hε).le]
        linarith),
      show 1 < ((1 : ℂ) + (↑(ε / 2) : ℂ)).re from by
        simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]; linarith⟩)
      (by simp)
  -- 𝓝[{Re > 1}] 1 ≤ 𝓝[{1}ᶜ] 1 (since Re(s) > 1 implies s ≠ 1)
  have hL_le : 𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ) ≤ 𝓝[{(1 : ℂ)}ᶜ] (1 : ℂ) :=
    nhdsWithin_mono (1 : ℂ) (fun (s : ℂ) (hs : s ∈ {s : ℂ | 1 < s.re}) =>
      show s ∈ {(1 : ℂ)}ᶜ from by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h; subst h; exact absurd hs (by simp [Complex.one_re]))
  -- On 𝓝[{Re > 1}] 1, eventually: (s-1) * (F s + G s) = -g s
  have h_eq_L : ∀ᶠ s in 𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ),
      (s - 1) * (F s + G s) = -g s := by
    filter_upwards [hg_eq.filter_mono hL_le, self_mem_nhdsWithin]
      with s hpole (hs_re : s ∈ {s : ℂ | 1 < s.re})
    have hs_ne : s ≠ (1 : ℂ) := by
      intro h; subst h
      exact absurd hs_re (by simp [Set.mem_setOf_eq, Complex.one_re])
    have hs_sub_ne : s - 1 ≠ 0 := sub_ne_zero_of_ne hs_ne
    -- F s + G s = ζ'/ζ(s) = -(g(s)/(s-1)), so (s-1)*(F+G) = -g(s)
    have h_fg : F s + G s = -(g s / (s - 1)) := by
      rw [(h_id s hs_re).symm]
      exact neg_eq_iff_eq_neg.mp (by rwa [neg_div] at hpole)
    rw [h_fg, mul_neg, neg_inj]
    field_simp [hs_sub_ne]
  -- Limit 1: (s-1)*(F+G)(s) → 0 as s → 1
  have h_lim_0 : Filter.Tendsto (fun s => (s - 1) * (F s + G s))
      (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)) (𝓝 0) := by
    have h_sub : Filter.Tendsto (fun s : ℂ => s - 1) (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
      rw [show (0 : ℂ) = 1 - 1 from by ring]
      exact tendsto_id.sub tendsto_const_nhds
    have h_prod := h_sub.mul hFG_contAt
    rw [show (0 : ℂ) * (F (1 : ℂ) + G (1 : ℂ)) = 0 from zero_mul _] at h_prod
    exact h_prod.mono_left nhdsWithin_le_nhds
  -- Limit 2: (s-1)*(F+G)(s) → -1 (equals -g(s) eventually, g(1) = 1)
  have h_lim_neg1 : Filter.Tendsto (fun s => (s - 1) * (F s + G s))
      (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)) (𝓝 (-1)) := by
    have hg_lim : Filter.Tendsto (fun s => -g s)
        (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)) (𝓝 (-1)) := by
      have h4 := hg_an.continuousAt.neg.tendsto
      rw [hg1] at h4
      exact h4.mono_left nhdsWithin_le_nhds
    exact (Filter.tendsto_congr' h_eq_L).mpr hg_lim
  -- Contradiction: 0 = -1
  exact absurd (tendsto_nhds_unique h_lim_0 h_lim_neg1) (by norm_num)

/-- **Sole B5b sorry**: Core Landau-Ingham impossibility (Landau 1905, Ingham 1932).
Under RH, σ·(ψ(x)-x) cannot be bounded above by C₀·√x for all large x.

The proof strategy (not yet formalized):
1. The one-sided bound makes ∫₁^∞ (C₀√x - σ(ψ(x)-x)) x^{-s-1} dx converge
   for Re(s) > 1/2 (Mellin convergence from nonneg integrand).
2. This Mellin transform relates to ζ'/ζ + σ/(s-1) + C₀/(s-1/2) via
   Perron/Stieltjes identities on {Re > 1}.
3. The s = 1 pole cancellation (σ/(s-1) absorbs ζ'/ζ pole) gives a function
   analytic on {Re > 1/2}, but under RH, ζ'/ζ has poles at s = 1/2 + iγ
   from zeros — contradicting the analytic extension.

Note: `landau_pole_contradiction` (proved above) handles step 3 for the
case where the pole cancellation fails to produce an analytic extension.
The correct Ingham argument uses pole cancellation (see PringsheimPsiAtom.lean). -/
private theorem landau_psi_bounded_impossible
    (hRH : ZetaZeros.RiemannHypothesis)
    (σ : ℝ) (_hσ : σ = 1 ∨ σ = -1)
    (C₀ X₀ : ℝ)
    (h_bound : ∀ x, x ≥ X₀ →
      σ * (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) ≤
        C₀ * Real.sqrt x) :
    False := by
  sorry

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
