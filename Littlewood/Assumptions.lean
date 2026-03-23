/-
# Littlewood Formalization: Documented Assumptions

This file provides instances for all hypothesis classes used in the formalization.
Each represents a classical theorem from analytic number theory not yet in Mathlib.

## Mathematical Status
These are PROVED theorems in classical mathematics—assumptions only because
their Lean proofs await Mathlib infrastructure.

## Current Status (2026-02-03)
- Total instance sorries: 56 (in this file), down from 60
- Proved/Wired instances:
  - ZeroConjZeroHyp, ZeroOneSubZeroHyp (in ZeroCountingFunction.lean)
  - ZetaLogDerivPoleHyp (proved here via analyticOrderAt arithmetic)
  - HardyCriticalLineZerosHyp (wired via HardyCriticalLineWiring bridge)
  - PsiOscillationFromCriticalZerosHyp (wired via ExplicitFormulaOscillation bridge, 1 sorry)
  - PsiOscillationSqrtHyp (wired via PsiOscillationWiring bridge, 0 sorries)
  - ThetaOscillationSqrtHyp (wired via ThetaExplicitFormulaOscillation bridge, 1 sorry)
  - PiLiOscillationSqrtHyp (wired via PsiToPiLiOscillation bridge, 0 sorries)
- Active Aristotle sorries: 8 across 5 files + 1 in CoreLemmas/LandauLemma
  Note: + 3 from PrimeNumberTheoremAnd dependency.
  Definitive count from `lake build` sorry warnings.

## Class Organization Rationale
Classes are kept separate (not merged) because:
1. Each has different mathematical content and dependencies
2. Progress can be tracked independently
3. Future Mathlib additions may enable individual proofs
4. Clear mapping to classical theorems in references

## Automation Attempt (Task 15)
Tactics tried: exact?, apply?, simp?, decide, positivity, linarith, nlinarith, ring
Result: All remaining sorries encode non-trivial mathematical theorems
(explicit formulas, zero density, Landau lemma, etc.) that require
substantial mathematical development, not simple automation.

## Organization
Instances are organized by mathematical domain:
1. Explicit Formula (Perron, Mellin)
2. Weighted Average Formula
3. Schmidt/Oscillation
4. Zero Density
5. Zeta Zero Supremum
6. Zero Counting
7. Landau Lemma Family

## Note on Instance Location
Instances with REAL PROOFS (no sorry):
- Littlewood/ZetaZeros/ZeroCountingFunction.lean:
  - ZeroConjZeroHyp (proved via riemannZeta_conj)
  - ZeroOneSubZeroHyp (proved via riemannZeta_one_sub functional equation)

This file provides a CENTRALIZED view of remaining assumptions.

## References
- [IK] Iwaniec & Kowalski, Analytic Number Theory
- [MV] Montgomery & Vaughan, Multiplicative Number Theory
- [T] Titchmarsh, Theory of the Riemann Zeta Function
-/

-- Import critical path instances (1 critical sorry + bridge wiring)
import Littlewood.CriticalAssumptions
-- Import files that DEFINE non-critical hypothesis classes
import Littlewood.CoreLemmas.WeightedAverageFormula
import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.ZetaZeros.ZeroDensity
import Littlewood.ZetaZeros.SupremumRealPart
import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.CoreLemmas.LandauLemma
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace Littlewood.Assumptions

open ExplicitFormula Conversion
open scoped Topology

-- ============================================================
-- SECTION 1: Explicit Formula Hypotheses
-- ============================================================
-- These relate to Perron's formula, Mellin transforms, and
-- the representation of ψ(x) via contour integrals.
-- Reference: [MV] Chapter 5, [IK] Chapter 5
-- ============================================================
-- ExplicitFormulaPsiHyp: provided by CriticalAssumptions.lean

-- Dead instances removed (2026-03-22):
-- ExplicitFormulaPsiSmoothedHyp, ExplicitFormulaIntegralHyp,
-- ExplicitFormulaDoubleIntegralHyp, PsiMellinHyp, MellinContourShiftHyp,
-- ZeroSumBoundRHHyp, PsiErrorBoundHyp — all unused outside this file.

instance : PsiErrorBoundRHHyp := by
  refine ⟨?_⟩
  intro hRH x hx
  sorry

-- WARNING: OmegaPsiToThetaHyp is FALSE as stated for f = sqrt(x).
-- The Omega_plus direction fails because |psi-theta| ~ sqrt(x) absorbs the signal.
-- See docs/CurrentStatus.md for analysis.
-- Kept for backward compatibility but NOT USED by main theorems (replaced by
-- ThetaOscillationSqrtHyp in the littlewood_pi_li chain).
instance : OmegaPsiToThetaHyp := by
  refine ⟨?_⟩
  intro f hf h
  sorry

-- OmegaThetaToPiLiHyp: provided by Bridge/OmegaThetaToPiLiWiring.lean

-- ============================================================
-- SECTION 2: Weighted Average Formula Hypotheses
-- ============================================================
-- These relate to the weighted average approach to oscillation.
-- Reference: [MV] Chapter 15
-- ============================================================
instance : WeightedAverage.WeightedAverageFormulaRHHyp := by
  refine ⟨?_⟩
  intro x hx δ hδ_lower hδ_upper hRH
  sorry

instance : WeightedAverage.IntegralPsiMinusXHyp := by
  refine ⟨?_⟩
  intro x hx
  sorry

instance : WeightedAverage.RhoToGammaErrorHyp := by
  refine ⟨?_⟩
  intro hRH
  sorry

instance : WeightedAverage.SumOverPositiveOrdinatesHyp := by
  refine ⟨?_⟩
  intro f hf
  sorry

instance : WeightedAverage.ZeroSumTailHyp := by
  refine ⟨?_⟩
  intro x T hT
  sorry

instance : WeightedAverage.MainSumBoundHyp := by
  refine ⟨?_⟩
  intro x M hM
  sorry

instance : WeightedAverage.AlignedSumLargeHyp := by
  refine ⟨?_⟩
  intro M hM n hn halign x hx
  sorry

-- ============================================================
-- SECTION 3: Schmidt/Littlewood Oscillation Hypotheses
-- ============================================================
-- These relate to Schmidt's 1983 refinement and the core
-- oscillation results for ψ and θ.
-- Reference: [MV] Chapter 15, Schmidt 1983
-- ============================================================
instance : Schmidt.SchmidtPsiOscillationHyp := by
  refine ⟨?_⟩
  intro ε hε
  sorry

-- PsiOscillationSqrtHyp: discharged automatically by PsiOscillationWiring.lean
-- (from PsiOscillationFromCriticalZerosHyp, which is provided by
-- ExplicitFormulaOscillation.lean from HardyCriticalLineZerosHyp + ExplicitFormulaPsiHyp)

instance : Schmidt.MellinPsiIdentityHyp := by
  refine ⟨?_⟩
  intro s hs
  sorry

instance : Schmidt.OmegaMinusNecessityHyp := by
  refine ⟨?_⟩
  intro ε hε hcontra
  sorry

instance : Schmidt.OmegaPlusNecessityHyp := by
  refine ⟨?_⟩
  intro ε hε hcontra
  sorry

-- ZetaCriticalLineBoundHyp: provided by CriticalAssumptions.lean
-- HardyFirstMomentUpperHyp: provided by CriticalAssumptions.lean
-- HardyCriticalLineZerosHyp: auto-wired via HardyCriticalLineWiring.lean

-- PsiOscillationFromCriticalZerosHyp: discharged by Bridge/ExplicitFormulaOscillation.lean
-- (from HardyCriticalLineZerosHyp + ExplicitFormulaPsiHyp, with 1 sorry for the
-- oscillation extraction — the genuine analytic content)

instance : Schmidt.ThetaOscillationMinusHyp := by
  refine ⟨?_⟩
  sorry

instance : Schmidt.ThetaOscillationRHHyp := by
  refine ⟨?_⟩
  intro hRH
  sorry

-- ThetaOscillationSqrtHyp: discharged by Bridge/ThetaExplicitFormulaOscillation.lean
-- (from HardyCriticalLineZerosHyp + ExplicitFormulaThetaHyp, with 1 sorry for
-- oscillation extraction. Same argument as ExplicitFormulaOscillation for ψ.
-- PsiToThetaOscillation.lean is DEPRECATED — see ThetaExplicitFormulaOscillation.)

-- PiLiOscillationSqrtHyp: discharged by Bridge/PsiToPiLiOscillation.lean
-- (from ThetaOscillationSqrtHyp + OmegaThetaToPiLiHyp, with 0 sorries)

-- ============================================================
-- SECTION 4: Zero Density Hypotheses
-- ============================================================
-- These relate to summability over zeros and density estimates.
-- Reference: [MV] Chapter 10, [IK] Chapter 10
-- ============================================================
instance : ZetaZeros.Density.ZeroCountingSummabilityHyp := by
  refine ⟨?_, ?_⟩
  · intro α hα
    sorry
  · sorry

instance : ZetaZeros.Density.ZeroCountingSumInvGammaAsymptoticHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.Density.ZeroCountingSumOneEqHyp := by
  refine ⟨?_⟩
  intro T
  sorry

instance : ZetaZeros.Density.ZeroCountingTailSqAsymptoticHyp := by
  refine ⟨?_⟩
  sorry

instance (hRH : ZetaZeros.RiemannHypothesis') :
    ZetaZeros.Density.RiemannHypothesisInvRhoAsymptoticHyp hRH := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.Density.ZeroCountingSummableXPowRhoDivHyp := by
  refine ⟨?_⟩
  intro x hx
  sorry

-- ============================================================
-- SECTION 5: Zeta Zero Supremum Hypotheses
-- ============================================================
-- These relate to Θ = sup{Re(ρ)} and error bounds.
-- Reference: [MV] Chapter 12-13
-- ============================================================
instance : ZetaZeros.ZeroFreeRegionHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ZetaZeroSupRealPartDichotomyHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ChebyshevErrorBoundZeroFreeHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ChebyshevErrorBoundThetaHyp := by
  refine ⟨?_⟩
  intro x hx
  sorry

-- ============================================================
-- SECTION 6: Zero Counting Hypotheses
-- ============================================================
-- These relate to N(T), the zero counting function.
-- Reference: [T] Chapter 9, [MV] Chapter 14
-- ============================================================
instance : ZetaZeros.ZeroCountingTendstoHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ZeroCountingCrudeBoundHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ZeroCountingSpecialValuesHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ZeroCountingFifteenHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ZeroCountingAsymptoticHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ZeroCountingRvmExplicitHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ZeroCountingAsymptoticRatioHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ZeroCountingMainTermHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ZeroCountingLowerBoundHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ZeroCountingLocalDensityHyp := by
  refine ⟨?_⟩
  sorry

instance : ZetaZeros.ZeroGapsLowerBoundHyp := by
  refine ⟨?_⟩
  sorry

-- NOTE: ZetaZeros.ZeroConjZeroHyp is PROVED in ZeroCountingFunction.lean
-- (instance zeroConjZeroHyp_of_riemannZeta)

-- NOTE: ZetaZeros.ZeroOneSubZeroHyp is PROVED in ZeroCountingFunction.lean
-- (instance zeroOneSubZeroHyp_of_riemannZeta)

-- ============================================================
-- SECTION 7: Landau Lemma Hypotheses
-- ============================================================
-- These relate to Dirichlet series singularity detection.
-- Landau's lemma: non-negative Dirichlet series have singularity
-- at their abscissa of convergence.
-- Reference: [T] Chapter 9.5
-- ============================================================
instance (A : ℝ → ℝ) (σ_c : ℝ) : Landau.LandauLemmaHyp A σ_c := by
  refine ⟨?_, ?_⟩
  · intro s hs
    sorry
  · sorry

instance (A : ℝ → ℝ) (σ_c : ℝ) : Landau.DirichletIntegralConvergesHyp A σ_c := by
  refine ⟨?_⟩
  intro s hs
  sorry

instance (A : ℝ → ℝ) (σ_c : ℝ) : Landau.DirichletIntegralAnalyticHyp A σ_c := by
  refine ⟨?_⟩
  intro s hs
  sorry

instance (A : ℝ → ℝ) (σ_c : ℝ) : Landau.DirichletIntegralDerivHyp A σ_c := by
  refine ⟨?_⟩
  intro s hs k
  sorry

instance (A : ℝ → ℝ) (σ_c : ℝ) : Landau.DirichletIntegralPowerSeriesHyp A σ_c := by
  refine ⟨?_⟩
  intro hσ
  sorry

instance (A : ℝ → ℝ) (σ_c : ℝ) : Landau.RadiusExceedsAbscissaHyp A σ_c := by
  refine ⟨?_⟩
  intro hσ hanalytic
  sorry

instance (A : ℝ → ℝ) (σ₀ : ℝ) : Landau.LandauExtensionHyp A σ₀ := by
  refine ⟨?_⟩
  intro hanalytic
  sorry

instance (a : ℕ → ℂ) (σ_c : ℂ) : Landau.LandauLemmaSeriesHyp a σ_c := by
  refine ⟨?_⟩
  sorry

-- PROVED: The logarithmic derivative -ζ'/ζ has a pole at any zero of ζ.
-- Proof: analyticOrderAt arithmetic + identity theorem for analytic functions.
instance : Landau.ZetaLogDerivPoleHyp := by
  refine ⟨?_⟩
  intro ρ hρ hh
  -- hρ : riemannZeta ρ = 0, hh : AnalyticAt ℂ (fun s => -deriv ζ s / ζ s) ρ, Goal: False
  have hne1 : ρ ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hρ)
  have hζ_diff_on : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) :=
    fun z hz => (differentiableAt_riemannZeta (Set.mem_compl_singleton_iff.mp hz)).differentiableWithinAt
  have hζ : AnalyticAt ℂ riemannZeta ρ :=
    hζ_diff_on.analyticAt (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hne1))
  have hζ' : AnalyticAt ℂ (deriv riemannZeta) ρ := hζ.deriv
  -- analyticOrderAt riemannZeta ρ is positive (ζ(ρ) = 0) and finite (identity theorem)
  have hord_pos : 0 < analyticOrderAt riemannZeta ρ := by
    rw [pos_iff_ne_zero]; exact analyticOrderAt_ne_zero.mpr ⟨hζ, hρ⟩
  have hord_ne_top : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    have hζ_aon : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) :=
      hζ_diff_on.analyticOnNhd isOpen_compl_singleton
    have hconn : IsPreconnected ({(1 : ℂ)}ᶜ) :=
      (isConnected_compl_singleton_of_one_lt_rank
        (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) 1).isPreconnected
    exact hζ_aon.analyticOrderAt_ne_top_of_isPreconnected hconn
      (Set.mem_compl_singleton_iff.mpr (by norm_num : (0 : ℂ) ≠ 1))
      (Set.mem_compl_singleton_iff.mpr hne1)
      (by rw [ne_eq, analyticOrderAt_eq_top]; intro h
          exact absurd h.self_of_nhds (by rw [riemannZeta_zero]; norm_num))
  -- On a punctured neighborhood, ζ(s) ≠ 0 (isolated zeros)
  have hpunc : ∀ᶠ s in 𝓝[≠] ρ, riemannZeta s ≠ 0 := by
    rcases hζ.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.mpr h) hord_ne_top
    · exact h
  -- h * ζ agrees with -ζ' on punctured nhd (where ζ ≠ 0, (-ζ'/ζ)·ζ = -ζ')
  have hprod_eq_punc : ∀ᶠ s in 𝓝[≠] ρ,
      (fun s => -deriv riemannZeta s / riemannZeta s) s * riemannZeta s =
      -deriv riemannZeta s := by
    filter_upwards [hpunc] with s hs
    rw [neg_div, neg_mul, neg_inj]
    exact div_mul_cancel₀ (deriv riemannZeta s) hs
  -- Their difference d = h·ζ - (-ζ') is analytic and vanishes on 𝓝[≠] ρ
  have hd_an : AnalyticAt ℂ
      (fun s => (fun s => -deriv riemannZeta s / riemannZeta s) s *
        riemannZeta s - (-deriv riemannZeta s)) ρ :=
    (hh.mul hζ).sub hζ'.neg
  have hd_punc : ∀ᶠ s in 𝓝[≠] ρ,
      (fun s => -deriv riemannZeta s / riemannZeta s) s *
        riemannZeta s - (-deriv riemannZeta s) = 0 := by
    filter_upwards [hprod_eq_punc] with s hs; rw [hs, sub_self]
  -- By isolation of zeros: d ≡ 0 on full 𝓝 ρ
  have hd_full : ∀ᶠ s in 𝓝 ρ,
      (fun s => -deriv riemannZeta s / riemannZeta s) s *
        riemannZeta s - (-deriv riemannZeta s) = 0 := by
    rcases hd_an.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact h
    · exfalso
      have : ∀ᶠ s in 𝓝[≠] ρ, False := by
        filter_upwards [h, hd_punc] with s h1 h2; exact h1 h2
      exact (this.exists).elim fun _ h => h
  -- So h * ζ =ᶠ[𝓝 ρ] -ζ', hence their analytic orders agree
  have hprod_full : (fun s => (fun s => -deriv riemannZeta s / riemannZeta s) s *
      riemannZeta s) =ᶠ[𝓝 ρ] (fun s => -deriv riemannZeta s) := by
    filter_upwards [hd_full] with s hs
    exact sub_eq_zero.mp hs
  have hord_eq : analyticOrderAt
      (fun s => (fun s => -deriv riemannZeta s / riemannZeta s) s * riemannZeta s) ρ =
      analyticOrderAt (fun s => -deriv riemannZeta s) ρ :=
    analyticOrderAt_congr hprod_full
  -- LHS = analyticOrderAt h + analyticOrderAt ζ (by analyticOrderAt_mul)
  have hord_mul : analyticOrderAt
      (fun s => (fun s => -deriv riemannZeta s / riemannZeta s) s * riemannZeta s) ρ =
      analyticOrderAt (fun s => -deriv riemannZeta s / riemannZeta s) ρ +
      analyticOrderAt riemannZeta ρ :=
    analyticOrderAt_mul hh hζ
  -- analyticOrderAt (-ζ') = analyticOrderAt ζ' (negation by unit doesn't change order)
  have hord_neg : analyticOrderAt (fun s => -deriv riemannZeta s) ρ =
      analyticOrderAt (deriv riemannZeta) ρ := by
    have h1 : (fun s : ℂ => -deriv riemannZeta s) =
        (fun _ : ℂ => (-1 : ℂ)) * deriv riemannZeta := by
      ext s; simp [Pi.mul_apply, neg_one_mul]
    have hconst : AnalyticAt ℂ (fun _ : ℂ => (-1 : ℂ)) ρ := analyticAt_const
    rw [h1, analyticOrderAt_mul hconst hζ',
      hconst.analyticOrderAt_eq_zero.mpr (by norm_num : (-1 : ℂ) ≠ 0), zero_add]
  -- analyticOrderAt ζ' + 1 = analyticOrderAt ζ (derivative reduces order by 1)
  have hord_deriv : analyticOrderAt (deriv riemannZeta) ρ + 1 =
      analyticOrderAt riemannZeta ρ := by
    have := hζ.analyticOrderAt_deriv_add_one
    simp only [hρ, sub_zero] at this; exact this
  -- Chain: ord(h) + ord(ζ) = ord(h·ζ) = ord(-ζ') = ord(ζ') and ord(ζ') + 1 = ord(ζ)
  -- So (ord(h) + ord(ζ)) + 1 = ord(ζ), rewrite as (ord(h) + 1) + ord(ζ) = 0 + ord(ζ)
  have hchain : analyticOrderAt (fun s => -deriv riemannZeta s / riemannZeta s) ρ +
      analyticOrderAt riemannZeta ρ = analyticOrderAt (deriv riemannZeta) ρ := by
    rw [← hord_mul, hord_eq, hord_neg]
  have key : (analyticOrderAt (fun s => -deriv riemannZeta s / riemannZeta s) ρ + 1) +
      analyticOrderAt riemannZeta ρ = 0 + analyticOrderAt riemannZeta ρ := by
    rw [zero_add, add_assoc, add_comm 1, ← add_assoc, hchain, hord_deriv]
  have cancel := WithTop.add_right_cancel hord_ne_top key
  exact absurd cancel (ne_of_gt ENat.add_one_pos)

end Littlewood.Assumptions
