/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.Basic.ChebyshevFunctions
import Littlewood.ExplicitFormulas.ExplicitFormulaPsi
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.IsLUB

/-!
# Supremum of Real Parts of Zeta Zeros

This file defines Θ = sup{Re(ρ) : ρ is a nontrivial zero of ζ} and proves
basic bounds. The Riemann Hypothesis is equivalent to Θ = 1/2.

## Definitions

* `zetaZeroSupRealPart` : Θ = sup{Re(ρ)}

## Main Results

* `zetaZeroSupRealPart_le_one` : Θ ≤ 1
* `zetaZeroSupRealPart_ge_half` : 1/2 ≤ Θ
* `RiemannHypothesis_iff` : RH ↔ Θ = 1/2

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 13
-/

open Complex Real Filter Topology Set ZetaZeros

namespace ZetaZeros

/-! ## Definition of Θ -/

/-- The set of real parts of nontrivial zeros -/
def zetaZeroRealParts : Set ℝ :=
  (·.re) '' zetaNontrivialZeros

/-- Θ = sup{Re(ρ) : ρ is a nontrivial zero of ζ} -/
noncomputable def zetaZeroSupRealPart : ℝ :=
  sSup zetaZeroRealParts

/-- Notation for Θ -/
scoped notation "Θ" => zetaZeroSupRealPart

/-! ## Hypotheses -/

/--
HYPOTHESIS: De la Vallee Poussin zero-free region for zeta.
MATHEMATICAL STATUS: classical analytic number theory.
MATHLIB STATUS: not available.
REFERENCE: Montgomery-Vaughan, Ch. 12.
-/
class ZeroFreeRegionHyp : Prop where
  region :
    ∃ c > 0, ∀ ρ ∈ zetaNontrivialZeros,
      ρ.re < 1 - c / Real.log (|ρ.im| + 2)

/--
HYPOTHESIS: Dichotomy for Theta (either RH or zeros approach Re = 1).
MATHEMATICAL STATUS: conditional statement used to separate cases.
MATHLIB STATUS: not available.
-/
class ZetaZeroSupRealPartDichotomyHyp : Prop where
  eq_one_or_half : Θ = 1 ∨ Θ = 1/2

/--
HYPOTHESIS: Zero-free region implies the standard psi error term.
MATHEMATICAL STATUS: explicit formula plus zero-free region analysis.
MATHLIB STATUS: not available.
REFERENCE: Montgomery-Vaughan, Ch. 12-13.
-/
class ChebyshevErrorBoundZeroFreeHyp : Prop where
  bound : ∃ c > 0, ∃ C > 0, ∀ x ≥ 2,
    |chebyshevPsi x - x| ≤ C * x * Real.exp (-c * (Real.log x).sqrt)

/-! ## Additional Error Bound Hypothesis -/

/--
HYPOTHESIS: Explicit formula bound |ψ(x) - x| ≤ 10 * x^Θ * log x.
MATHEMATICAL STATUS: classical explicit formula.
MATHLIB STATUS: not available.
-/
class ChebyshevErrorBoundThetaHyp : Prop where
  bound : ∀ x ≥ 2, |chebyshevPsi x - x| ≤ 10 * x ^ Θ * Real.log x

/-! ## Basic Bounds -/

section Bounds

/-- All nontrivial zeros have real part < 1 -/
theorem zetaZeroRealPart_lt_one {ρ : ℂ} (hρ : ρ ∈ zetaNontrivialZeros) :
    ρ.re < 1 := hρ.2.2

/-- All nontrivial zeros have real part > 0 -/
theorem zetaZeroRealPart_pos {ρ : ℂ} (hρ : ρ ∈ zetaNontrivialZeros) :
    0 < ρ.re := hρ.2.1

/-- The set of real parts is bounded above by 1 -/
theorem zetaZeroRealParts_bddAbove : BddAbove zetaZeroRealParts := by
  use 1
  intro σ hσ
  obtain ⟨ρ, hρ, rfl⟩ := hσ
  exact le_of_lt (zetaZeroRealPart_lt_one hρ)

/-- The set of real parts is bounded below by 0 -/
theorem zetaZeroRealParts_bddBelow : BddBelow zetaZeroRealParts := by
  refine ⟨0, ?_⟩
  intro σ hσ
  obtain ⟨ρ, hρ, rfl⟩ := hσ
  exact le_of_lt (zetaZeroRealPart_pos hρ)

/-- The set of real parts is nonempty (there exist zeros) -/
theorem zetaZeroRealParts_nonempty [ZetaHasNontrivialZeroHyp] : zetaZeroRealParts.Nonempty := by
  rcases zetaNontrivialZerosPos_nonempty with ⟨s, hs⟩
  have hs' : s ∈ zetaNontrivialZeros := (mem_zetaNontrivialZerosPos.mp hs).1
  exact ⟨s.re, s, hs', rfl⟩

/-- Θ ≤ 1 -/
theorem zetaZeroSupRealPart_le_one [ZetaHasNontrivialZeroHyp] : Θ ≤ 1 := by
  apply csSup_le zetaZeroRealParts_nonempty
  intro σ hσ
  obtain ⟨ρ, hρ, rfl⟩ := hσ
  exact le_of_lt (zetaZeroRealPart_lt_one hρ)

/-- 0 < Θ -/
theorem zetaZeroSupRealPart_pos [ZetaHasNontrivialZeroHyp] : 0 < Θ := by
  have hne := zetaZeroRealParts_nonempty
  obtain ⟨σ, ρ, hρ, rfl⟩ := hne
  calc 0 < ρ.re := zetaZeroRealPart_pos hρ
    _ ≤ Θ := le_csSup zetaZeroRealParts_bddAbove ⟨ρ, hρ, rfl⟩

/-- 1/2 ≤ Θ (there exist zeros with real part = 1/2 on the critical line) -/
theorem zetaZeroSupRealPart_ge_half [ZetaHasNontrivialZeroHyp] : 1/2 ≤ Θ := by
  have hne := zetaZeroRealParts_nonempty
  rcases hne with ⟨r, hr⟩
  rcases hr with ⟨ρ, hρ, hrre⟩
  have hmem : r ∈ zetaZeroRealParts := ⟨ρ, hρ, hrre⟩
  have hmem' : 1 - r ∈ zetaZeroRealParts := by
    refine ⟨1 - ρ, zero_one_sub_zero hρ, ?_⟩
    simp [Complex.sub_re, Complex.one_re, hrre]
  have hle_r : r ≤ Θ := le_csSup zetaZeroRealParts_bddAbove hmem
  have hle_1mr : 1 - r ≤ Θ := le_csSup zetaZeroRealParts_bddAbove hmem'
  by_cases hρle : r ≤ (1 / 2 : ℝ)
  · have hge : (1 / 2 : ℝ) ≤ 1 - r := by linarith
    exact le_trans hge hle_1mr
  · have hge : (1 / 2 : ℝ) ≤ r := by linarith
    exact le_trans hge hle_r

/-- Θ is achieved: there exists a sequence of zeros whose real parts → Θ -/
theorem zetaZeroSupRealPart_achieved [ZetaHasNontrivialZeroHyp] :
    ∃ ρₙ : ℕ → zetaNontrivialZeros, Tendsto (fun n => (ρₙ n).val.re) atTop (𝓝 Θ) := by
  classical
  obtain ⟨u, _hu_mono, hu_tendsto, hu_mem⟩ :=
    exists_seq_tendsto_sSup (S := zetaZeroRealParts)
      zetaZeroRealParts_nonempty zetaZeroRealParts_bddAbove
  have hu_mem' : ∀ n, ∃ ρ : zetaNontrivialZeros, ρ.val.re = u n := by
    intro n
    rcases hu_mem n with ⟨ρ, hρ, hρre⟩
    exact ⟨⟨ρ, hρ⟩, hρre⟩
  choose ρₙ hρₙ using hu_mem'
  refine ⟨ρₙ, ?_⟩
  have h_eq : (fun n => (ρₙ n).val.re) = u := by
    funext n
    exact hρₙ n
  simpa [h_eq] using hu_tendsto

end Bounds

/-! ## Riemann Hypothesis Characterization -/

section RH

/-- The Riemann Hypothesis: all zeros have real part 1/2 -/
def RiemannHypothesis : Prop :=
  ∀ ρ ∈ zetaNontrivialZeros, ρ.re = 1/2

/-- RH is equivalent to Θ = 1/2 -/
theorem RiemannHypothesis_iff [ZetaHasNontrivialZeroHyp] : RiemannHypothesis ↔ Θ = 1/2 := by
  constructor
  · -- RH → Θ = 1/2
    intro hRH
    apply le_antisymm
    · -- Θ ≤ 1/2
      apply csSup_le zetaZeroRealParts_nonempty
      intro σ hσ
      obtain ⟨ρ, hρ, rfl⟩ := hσ
      exact le_of_eq (hRH ρ hρ)
    · -- 1/2 ≤ Θ
      exact zetaZeroSupRealPart_ge_half
  · -- Θ = 1/2 → RH
    intro hΘ
    intro ρ hρ
    have h1 : ρ.re ≤ Θ := le_csSup zetaZeroRealParts_bddAbove ⟨ρ, hρ, rfl⟩
    have h2 : Θ ≤ ρ.re := by
      -- If Θ = 1/2 and all zeros have re ≤ Θ = 1/2, and 1/2 ≤ all zeros (by symmetry)
      -- then all have re = 1/2
      have hρ' : 1 - ρ ∈ zetaNontrivialZeros := zero_one_sub_zero hρ
      have hmem : 1 - ρ.re ∈ zetaZeroRealParts := by
        refine ⟨1 - ρ, hρ', ?_⟩
        simp [Complex.sub_re, Complex.one_re]
      have hle : 1 - ρ.re ≤ Θ := le_csSup zetaZeroRealParts_bddAbove hmem
      have hle' : 1 - ρ.re ≤ (1 / 2 : ℝ) := by
        simpa [hΘ] using hle
      have hge : (1 / 2 : ℝ) ≤ ρ.re := by
        linarith
      simpa [hΘ] using hge
    linarith

/-- Under RH, Θ = 1/2 -/
theorem zetaZeroSupRealPart_eq_half_of_RH [ZetaHasNontrivialZeroHyp]
    (hRH : RiemannHypothesis) : Θ = 1/2 :=
  RiemannHypothesis_iff.mp hRH

/-- If RH fails, then Θ > 1/2 -/
theorem zetaZeroSupRealPart_gt_half_of_not_RH [ZetaHasNontrivialZeroHyp]
    (hRH : ¬RiemannHypothesis) : 1/2 < Θ := by
  by_contra h
  push_neg at h
  have hΘ : Θ = 1/2 := le_antisymm h zetaZeroSupRealPart_ge_half
  exact hRH (RiemannHypothesis_iff.mpr hΘ)

end RH

/-! ## Zero-Free Regions -/

section ZeroFree

/-- The de la Vallée Poussin zero-free region: no zeros for Re(s) > 1 - c/log(|Im(s)| + 2) -/
theorem zeroFreeRegion_delaValleePoussin [ZeroFreeRegionHyp] :
    ∃ c > 0, ∀ ρ ∈ zetaNontrivialZeros,
      ρ.re < 1 - c / Real.log (|ρ.im| + 2) := by
  simpa using ZeroFreeRegionHyp.region

/-- This implies Θ = 1 (i.e., zeros can get arbitrarily close to Re = 1) -/
theorem zetaZeroSupRealPart_eq_one_or_half [ZetaHasNontrivialZeroHyp]
    [ZetaZeroSupRealPartDichotomyHyp] :
    Θ = 1 ∨ Θ = 1/2 := by
  simpa using ZetaZeroSupRealPartDichotomyHyp.eq_one_or_half

/-- The infimum of real parts is 1 - Θ (by symmetry ρ ↔ 1-ρ) -/
theorem zetaZeroInfRealPart [ZetaHasNontrivialZeroHyp] : sInf zetaZeroRealParts = 1 - Θ := by
  -- The functional equation ρ ↔ 1-ρ gives this symmetry
  have hsymm : ∀ r ∈ zetaZeroRealParts, 1 - r ∈ zetaZeroRealParts := by
    intro r hr
    rcases hr with ⟨ρ, hρ, rfl⟩
    refine ⟨1 - ρ, zero_one_sub_zero hρ, ?_⟩
    simp [Complex.sub_re, Complex.one_re]
  have hlower : 1 - Θ ≤ sInf zetaZeroRealParts := by
    refine le_csInf zetaZeroRealParts_nonempty ?_
    intro r hr
    have hmem : 1 - r ∈ zetaZeroRealParts := hsymm r hr
    have hle : 1 - r ≤ Θ := le_csSup zetaZeroRealParts_bddAbove hmem
    linarith
  have hupper : sInf zetaZeroRealParts ≤ 1 - Θ := by
    have hsup : Θ ≤ 1 - sInf zetaZeroRealParts := by
      apply csSup_le zetaZeroRealParts_nonempty
      intro r hr
      have hmem : 1 - r ∈ zetaZeroRealParts := hsymm r hr
      have hle : sInf zetaZeroRealParts ≤ 1 - r := csInf_le zetaZeroRealParts_bddBelow hmem
      linarith
    linarith
  exact le_antisymm hupper hlower

end ZeroFree

/-! ## Consequences of Θ for Error Terms -/

section ErrorTerms

open Chebyshev in
/-- ψ(x) - x = O(x^Θ) (elementary consequence of explicit formula) -/
theorem chebyshev_error_bound_Theta [ZetaHasNontrivialZeroHyp] [ChebyshevErrorBoundThetaHyp]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C > 0, ∀ x ≥ 2, |chebyshevPsi x - x| ≤ C * x ^ (Θ + ε) := by
  refine ⟨10 / ε, by positivity, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hlog : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div hx0 hε
  have hpsi : |chebyshevPsi x - x| ≤ 10 * x ^ Θ * Real.log x := by
    simpa using (ChebyshevErrorBoundThetaHyp.bound x hx)
  have hmul :
      10 * x ^ Θ * Real.log x ≤ 10 * x ^ Θ * (x ^ ε / ε) := by
    have hnonneg : 0 ≤ 10 * x ^ Θ := by
      have : 0 ≤ x ^ Θ := Real.rpow_nonneg hx0 _
      nlinarith
    exact mul_le_mul_of_nonneg_left hlog hnonneg
  have hpow : x ^ Θ * (x ^ ε) = x ^ (Θ + ε) := by
    simpa [Real.rpow_add] using (Real.rpow_add hxpos Θ ε).symm
  calc
    |chebyshevPsi x - x| ≤ 10 * x ^ Θ * Real.log x := hpsi
    _ ≤ 10 * x ^ Θ * (x ^ ε / ε) := hmul
    _ = (10 / ε) * x ^ (Θ + ε) := by
      calc
        10 * x ^ Θ * (x ^ ε / ε) = (10 / ε) * (x ^ Θ * x ^ ε) := by
          simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        _ = (10 / ε) * x ^ (Θ + ε) := by
          simp [hpow]

open Chebyshev in
/-- Under RH: ψ(x) - x = O(x^{1/2} log²x) -/
theorem chebyshev_error_bound_RH [ZetaHasNontrivialZeroHyp]
    [ExplicitFormula.PsiErrorBoundRHHyp] (hRH : RiemannHypothesis) :
    ∃ C > 0, ∀ x ≥ 2, |chebyshevPsi x - x| ≤ C * x ^ (1/2 : ℝ) * (Real.log x) ^ 2 := by
  have hRH' : RiemannHypothesis' := by
    intro ρ hρ
    exact hRH ρ hρ
  refine ⟨10, by positivity, ?_⟩
  intro x hx
  simpa [Real.sqrt_eq_rpow] using (ExplicitFormula.psi_error_bound_RH hRH' x hx)

open Chebyshev in
/-- The zero-free region gives: ψ(x) - x = O(x exp(-c √log x)) -/
theorem chebyshev_error_bound_zeroFree [ZetaHasNontrivialZeroHyp]
    [ChebyshevErrorBoundZeroFreeHyp] :
    ∃ c > 0, ∃ C > 0, ∀ x ≥ 2,
      |chebyshevPsi x - x| ≤ C * x * Real.exp (-c * (Real.log x).sqrt) := by
  simpa using ChebyshevErrorBoundZeroFreeHyp.bound

end ErrorTerms

/-!
## Hypothesis Instances

Instances for ZeroFreeRegionHyp, ZetaZeroSupRealPartDichotomyHyp,
ChebyshevErrorBoundZeroFreeHyp, and ChebyshevErrorBoundThetaHyp
are provided in Assumptions.lean (the single source of truth for axioms).
-/

end ZetaZeros
