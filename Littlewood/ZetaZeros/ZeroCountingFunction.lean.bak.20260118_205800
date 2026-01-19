/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-!
# Zero Counting Function N(T)

This file defines the zero counting function N(T), which counts the number of
nontrivial zeros of the Riemann zeta function with imaginary part in (0, T].

## Definitions

* `zetaNontrivialZeros` : The set of nontrivial zeros of ζ(s)
* `zeroCountingFunction T` : N(T), the number of zeros with 0 < Im(ρ) ≤ T

## Main Results

* `zeroCountingFunction_asymptotic` : N(T) = (T/2π) log(T/2π) - T/2π + O(log T)
* `zeroCountingFunction_local_density` :
  N(T+h) - N(T) = O((h + 1) (log (T + h) + 1))

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 14
* Titchmarsh, "The Theory of the Riemann Zeta-Function", Chapter 9
-/

open Complex Real Filter Topology Set

namespace ZetaZeros

theorem logDeriv_sub_const (x a : ℂ) :
    logDeriv (fun z : ℂ => z - a) x = 1 / (x - a) := by
  have hderiv : deriv (fun z : ℂ => z - a) x = (1 : ℂ) := by
    simpa [deriv_id] using
      (deriv_sub_const (f := fun z : ℂ => z) (x := x) (c := a))
  simp [logDeriv_apply, hderiv]

/-! ## The Set of Nontrivial Zeros -/

/-- A nontrivial zero of ζ(s) is a zero with 0 < Re(s) < 1.
    These are the zeros in the critical strip. -/
def zetaNontrivialZeros : Set ℂ :=
  { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 }

/-- The set of nontrivial zeros with positive imaginary part -/
def zetaNontrivialZerosPos : Set ℂ :=
  { s ∈ zetaNontrivialZeros | 0 < s.im }

/-- The imaginary parts of nontrivial zeros (the "ordinates") -/
def zetaZeroOrdinates : Set ℝ :=
  (·.im) '' zetaNontrivialZerosPos

/-- Membership in zetaNontrivialZeros implies the defining properties -/
theorem mem_zetaNontrivialZeros {s : ℂ} :
    s ∈ zetaNontrivialZeros ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := Iff.rfl

/-- Membership in zetaNontrivialZerosPos implies positive imaginary part -/
theorem mem_zetaNontrivialZerosPos {s : ℂ} :
    s ∈ zetaNontrivialZerosPos ↔ s ∈ zetaNontrivialZeros ∧ 0 < s.im := by
  unfold zetaNontrivialZerosPos
  simp only [Set.mem_sep_iff]

/-- Completed Riemann xi-function (up to the standard scalar factor). -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta s

theorem riemannXi_zero_iff_completed {s : ℂ} (hpos : 0 < s.re) (hlt : s.re < 1) :
    riemannXi s = 0 ↔ completedRiemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    have : s.re = 0 := by simpa [h] using (rfl : ((0 : ℂ).re = (0 : ℝ)))
    exact (ne_of_gt hpos) this
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have hs : s = 1 := sub_eq_zero.mp h
    have : s.re = 1 := by simpa [hs]
    exact (ne_of_lt hlt) this
  have hmul_ne : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1
  constructor
  · intro hxi
    have hzero :
        s * (s - 1) = 0 ∨ completedRiemannZeta s = 0 := by
      simpa [riemannXi, mul_eq_zero] using hxi
    cases hzero with
    | inl hmul => exact (hmul_ne hmul).elim
    | inr hz => exact hz
  · intro hz
    simp [riemannXi, hz]

theorem logDeriv_riemannXi (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hcomp : completedRiemannZeta s ≠ 0) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hmul_ne : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1'
  have hmul1 :
      logDeriv (fun z : ℂ => z * (z - 1)) s =
        logDeriv (fun z : ℂ => z) s + logDeriv (fun z : ℂ => z - 1) s := by
    have hdf : DifferentiableAt ℂ (fun z : ℂ => z) s := differentiableAt_id
    have hdg : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := by
      simpa [sub_eq_add_neg] using (differentiableAt_id.add differentiableAt_const)
    simpa using
      (logDeriv_mul (x := s) (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1)
        hs0 hs1' hdf hdg)
  have hmul2 :
      logDeriv riemannXi s =
        logDeriv (fun z : ℂ => z * (z - 1)) s + logDeriv completedRiemannZeta s := by
    have hdf : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1)) s := by
      have hdf1 : DifferentiableAt ℂ (fun z : ℂ => z) s := differentiableAt_id
      have hdf2 : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := by
        simpa [sub_eq_add_neg] using (differentiableAt_id.add differentiableAt_const)
      simpa [sub_eq_add_neg] using hdf1.mul hdf2
    have hdg : DifferentiableAt ℂ completedRiemannZeta s :=
      differentiableAt_completedZeta hs0 hs1
    simpa [riemannXi] using
      (logDeriv_mul (x := s)
        (f := fun z : ℂ => z * (z - 1))
        (g := completedRiemannZeta) hmul_ne hcomp hdf hdg)
  calc
    logDeriv riemannXi s
        = logDeriv (fun z : ℂ => z * (z - 1)) s +
            logDeriv completedRiemannZeta s := hmul2
    _ = (1 / s + 1 / (s - 1)) + logDeriv completedRiemannZeta s := by
        simp [hmul1, logDeriv_sub_const, logDeriv_id, add_assoc]
    _ = 1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
        simp [add_assoc]

theorem completedRiemannZeta_eq_zero_iff_riemannZeta {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro hs0
    have : s.re = 0 := by
      simpa [hs0] using (rfl : ((0 : ℂ).re = (0 : ℝ)))
    exact (ne_of_gt hs) this
  have hzeta := riemannZeta_def_of_ne_zero (s := s) hs0
  constructor
  · intro h
    rw [hzeta, h, zero_div]
  · intro h
    have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
    have hzeta_mul : riemannZeta s * Gammaℝ s = completedRiemannZeta s := by
      have hzeta' := congrArg (fun z => z * Gammaℝ s) hzeta
      simpa [div_eq_mul_inv, mul_assoc, hGamma] using hzeta'
    have : riemannZeta s * Gammaℝ s = 0 := by
      simpa [h]
    simpa [hzeta_mul] using this

theorem mem_zetaNontrivialZeros_iff_completed {s : ℂ} :
    s ∈ zetaNontrivialZeros ↔ completedRiemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro hs
    rcases (mem_zetaNontrivialZeros.1 hs) with ⟨hzeta, hpos, hlt⟩
    have hcomp : completedRiemannZeta s = 0 :=
      (completedRiemannZeta_eq_zero_iff_riemannZeta hpos).2 hzeta
    exact ⟨hcomp, hpos, hlt⟩
  · rintro ⟨hcomp, hpos, hlt⟩
    have hzeta : riemannZeta s = 0 :=
      (completedRiemannZeta_eq_zero_iff_riemannZeta hpos).1 hcomp
    exact (mem_zetaNontrivialZeros).2 ⟨hzeta, hpos, hlt⟩

theorem mem_zetaNontrivialZeros_iff_xi {s : ℂ} :
    s ∈ zetaNontrivialZeros ↔ riemannXi s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro hs
    rcases (mem_zetaNontrivialZeros.1 hs) with ⟨hzeta, hpos, hlt⟩
    have hcomp : completedRiemannZeta s = 0 :=
      (completedRiemannZeta_eq_zero_iff_riemannZeta hpos).2 hzeta
    have hxi : riemannXi s = 0 := (riemannXi_zero_iff_completed hpos hlt).2 hcomp
    exact ⟨hxi, hpos, hlt⟩
  · rintro ⟨hxi, hpos, hlt⟩
    have hcomp : completedRiemannZeta s = 0 :=
      (riemannXi_zero_iff_completed hpos hlt).1 hxi
    exact (mem_zetaNontrivialZeros_iff_completed).2 ⟨hcomp, hpos, hlt⟩

/-! ## The Zero Counting Function -/

/-- N(T) counts the nontrivial zeros ρ with 0 < Im(ρ) ≤ T.
    Since ζ has infinitely many zeros, we need to be careful about well-definedness.
    For any finite T, there are only finitely many zeros with Im(ρ) ≤ T. -/
noncomputable def zeroCountingFunction (T : ℝ) : ℕ :=
  (zetaNontrivialZerosPos ∩ { s : ℂ | s.im ≤ T }).ncard

/-- Notation for N(T) -/
scoped notation "N" => zeroCountingFunction

/-- The set being counted by N(T) -/
def zerosUpTo (T : ℝ) : Set ℂ :=
  zetaNontrivialZerosPos ∩ { s : ℂ | s.im ≤ T }

/-- N(T) is the cardinality of zerosUpTo(T) -/
theorem zeroCountingFunction_eq_ncard (T : ℝ) : N T = (zerosUpTo T).ncard := rfl

/-- Zeros of the completed zeta in the critical strip up to height `T`. -/
def completedZerosUpTo (T : ℝ) : Set ℂ :=
  { s : ℂ |
      completedRiemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T }

/-- Zeros of the completed xi-function in the critical strip up to height `T`. -/
def xiZerosUpTo (T : ℝ) : Set ℂ :=
  { s : ℂ | riemannXi s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T }

theorem zerosUpTo_eq_completed (T : ℝ) : zerosUpTo T = completedZerosUpTo T := by
  ext s
  constructor
  · intro hs
    rcases (by simpa [zerosUpTo] using hs : s ∈ zetaNontrivialZerosPos ∧ s.im ≤ T) with
      ⟨hzpos, hImle⟩
    rcases (mem_zetaNontrivialZerosPos.1 hzpos) with ⟨hzeta, hImpos⟩
    rcases (mem_zetaNontrivialZeros.1 hzeta) with ⟨hzeta0, hRepos, hRelt⟩
    have hcomp : completedRiemannZeta s = 0 :=
      (completedRiemannZeta_eq_zero_iff_riemannZeta hRepos).2 hzeta0
    exact ⟨hcomp, hRepos, hRelt, hImpos, hImle⟩
  · rintro ⟨hcomp, hRepos, hRelt, hImpos, hImle⟩
    have hzeta : riemannZeta s = 0 :=
      (completedRiemannZeta_eq_zero_iff_riemannZeta hRepos).1 hcomp
    have hzetaMem : s ∈ zetaNontrivialZeros :=
      (mem_zetaNontrivialZeros).2 ⟨hzeta, hRepos, hRelt⟩
    have hzpos : s ∈ zetaNontrivialZerosPos :=
      (mem_zetaNontrivialZerosPos).2 ⟨hzetaMem, hImpos⟩
    exact by
      simpa [zerosUpTo] using (And.intro hzpos hImle)

theorem zerosUpTo_eq_xi (T : ℝ) : zerosUpTo T = xiZerosUpTo T := by
  ext s
  constructor
  · intro hs
    rcases (by simpa [zerosUpTo] using hs : s ∈ zetaNontrivialZerosPos ∧ s.im ≤ T) with
      ⟨hzpos, hImle⟩
    rcases (mem_zetaNontrivialZerosPos.1 hzpos) with ⟨hzeta, hImpos⟩
    rcases (mem_zetaNontrivialZeros_iff_xi.1 hzeta) with ⟨hxi, hRepos, hRelt⟩
    exact ⟨hxi, hRepos, hRelt, hImpos, hImle⟩
  · rintro ⟨hxi, hRepos, hRelt, hImpos, hImle⟩
    have hzeta : s ∈ zetaNontrivialZeros :=
      (mem_zetaNontrivialZeros_iff_xi).2 ⟨hxi, hRepos, hRelt⟩
    have hzpos : s ∈ zetaNontrivialZerosPos :=
      (mem_zetaNontrivialZerosPos).2 ⟨hzeta, hImpos⟩
    simpa [zerosUpTo] using (And.intro hzpos hImle)

/-- The set zerosUpTo is monotone in T -/
theorem zerosUpTo_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : zerosUpTo T₁ ⊆ zerosUpTo T₂ := by
  intro s hs
  unfold zerosUpTo at hs ⊢
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hs ⊢
  exact ⟨hs.1, le_trans hs.2 h⟩

/-! ## Finiteness of Zeros in Bounded Regions -/

/-- There is a punctured neighborhood of `1` on which `ζ` is nonzero. -/
private lemma riemannZeta_ne_zero_punctured_nhds_one :
    ∃ ε > 0, ∀ s, s ≠ (1 : ℂ) → dist s 1 < ε → riemannZeta s ≠ 0 := by
  have hres := riemannZeta_residue_one
  have hne :
      ((fun s => (s - 1) * riemannZeta s) ⁻¹' ({0}ᶜ : Set ℂ)) ∈ 𝓝[≠] (1 : ℂ) := by
    have h0 : ({0}ᶜ : Set ℂ) ∈ 𝓝 (1 : ℂ) := by
      simpa using (compl_singleton_mem_nhds (show (1 : ℂ) ≠ 0 by exact one_ne_zero))
    exact (tendsto_def.1 hres) ({0}ᶜ) h0
  rcases (Metric.mem_nhdsWithin_iff.1 hne) with ⟨ε, εpos, hε⟩
  refine ⟨ε, εpos, ?_⟩
  intro s hs hdist
  have hs' : s ∈ Metric.ball (1 : ℂ) ε ∩ ({x : ℂ | x ≠ 1}) := by
    refine ⟨?_, ?_⟩
    · simpa [Metric.mem_ball] using hdist
    · simpa [Set.mem_setOf_eq] using hs
  have hmem := hε hs'
  have hprod : (s - 1) * riemannZeta s ≠ 0 := by
    simpa [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using hmem
  intro hz
  apply hprod
  simp [hz]

/-- There are only finitely many zeros with imaginary part ≤ T.
    This is a consequence of ζ being meromorphic with isolated zeros. -/
theorem finite_zeros_le (T : ℝ) : (zerosUpTo T).Finite := by
  classical
  by_cases hT : T ≤ 0
  · have hEmpty : zerosUpTo T = ∅ := by
      ext z
      constructor
      · intro hz
        rcases (by simpa [zerosUpTo] using hz : z ∈ zetaNontrivialZerosPos ∧ z.im ≤ T) with
          ⟨hzpos, hzT⟩
        rcases (mem_zetaNontrivialZerosPos.1 hzpos) with ⟨_, hzIm⟩
        linarith
      · intro hz
        cases hz
    simpa [hEmpty] using (Set.finite_empty : (∅ : Set ℂ).Finite)
  · have hTpos : 0 < T := lt_of_not_ge hT
    obtain ⟨ε, εpos, hε⟩ := riemannZeta_ne_zero_punctured_nhds_one
    set U : Set ℂ := {s : ℂ | s ≠ 1}
    set Z : Set ℂ := riemannZeta ⁻¹' ({0} : Set ℂ)
    set K : Set ℂ :=
      Metric.closedBall (0 : ℂ) (1 + T) ∩ (Metric.ball (1 : ℂ) ε)ᶜ
    have hsubsetZ : zerosUpTo T ⊆ Z := by
      intro z hz
      rcases (by simpa [zerosUpTo] using hz : z ∈ zetaNontrivialZerosPos ∧ z.im ≤ T) with
        ⟨hzpos, _⟩
      rcases (mem_zetaNontrivialZerosPos.1 hzpos) with ⟨hznon, _⟩
      rcases (mem_zetaNontrivialZeros.1 hznon) with ⟨hzeta, _, _⟩
      simpa [Z, hzeta]
    have hsubsetK : zerosUpTo T ⊆ K := by
      intro z hz
      rcases (by simpa [zerosUpTo] using hz : z ∈ zetaNontrivialZerosPos ∧ z.im ≤ T) with
        ⟨hzpos, hzT⟩
      rcases (mem_zetaNontrivialZerosPos.1 hzpos) with ⟨hznon, hzIm⟩
      rcases (mem_zetaNontrivialZeros.1 hznon) with ⟨hzeta, hzRe, hzReLt⟩
      have hzRe' : |z.re| ≤ 1 := by
        have hzRe0 : 0 ≤ z.re := le_of_lt hzRe
        have hzReEq : |z.re| = z.re := abs_of_nonneg hzRe0
        linarith [hzReLt, hzReEq]
      have hzIm' : |z.im| ≤ T := by
        have hzIm0 : 0 ≤ z.im := le_of_lt hzIm
        have hzImEq : |z.im| = z.im := abs_of_nonneg hzIm0
        linarith [hzT, hzImEq]
      have hnorm : ‖z‖ ≤ 1 + T := by
        have hnorm' := norm_le_abs_re_add_abs_im z
        linarith [hnorm', hzRe', hzIm']
      have hball : z ∈ Metric.closedBall (0 : ℂ) (1 + T) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
      have hz_ne_one : z ≠ (1 : ℂ) := by
        intro h
        have : z.im = 0 := by simpa [h]
        linarith
      have hnotball : z ∉ Metric.ball (1 : ℂ) ε := by
        intro hzball
        have hdist : dist z 1 < ε := by
          simpa [Metric.mem_ball] using hzball
        exact (hε z hz_ne_one hdist) hzeta
      exact ⟨hball, hnotball⟩
    have hconn : IsConnected U := by
      simpa [U] using
        (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat)
          (1 : ℂ))
    have hdiff : DifferentiableOn ℂ riemannZeta U := by
      intro s hs
      exact (differentiableAt_riemannZeta hs).differentiableWithinAt
    have han : AnalyticOnNhd ℂ riemannZeta U := by
      simpa [U] using
        (analyticOnNhd_iff_differentiableOn (isOpen_compl_singleton : IsOpen U)).2 hdiff
    have h2 : riemannZeta (2 : ℂ) ≠ 0 := by
      have h2re : 1 < (2 : ℂ).re := by norm_num
      exact riemannZeta_ne_zero_of_one_lt_re h2re
    have hcod : Zᶜ ∈ Filter.codiscreteWithin U := by
      have hx : (2 : ℂ) ∈ U := by simp [U]
      simpa [Z] using
        (AnalyticOnNhd.preimage_zero_mem_codiscreteWithin (f := riemannZeta) (U := U)
          (x := 2) han h2 hx hconn)
    have hdiscZU : IsDiscrete (Z ∩ U) :=
      isDiscrete_of_codiscreteWithin (U := U) (s := Z) hcod
    have hdisc_subset :
        ∀ {s t : Set ℂ}, IsDiscrete s → t ⊆ s → IsDiscrete t := by
      intro s t hs hts
      refine IsDiscrete.of_nhdsWithin ?_
      intro x hx
      have hx' : x ∈ s := hts hx
      have hnhds : 𝓝[s] x = pure x := hs.nhdsWithin x hx'
      have hle : 𝓝[t] x ≤ 𝓝[s] x := nhdsWithin_mono x hts
      simpa [hnhds] using hle
    have hKsubsetU : K ⊆ U := by
      intro z hz
      have hzball : z ∉ Metric.ball (1 : ℂ) ε := hz.2
      intro h
      apply hzball
      simpa [h] using (Metric.mem_ball_self (x := (1 : ℂ)) εpos)
    have hdiscK : IsDiscrete (Z ∩ K) := by
      apply hdisc_subset hdiscZU
      intro z hz
      exact ⟨hz.1, hKsubsetU hz.2⟩
    have hKcomp : IsCompact K := by
      exact (isCompact_closedBall (0 : ℂ) (1 + T)).inter_right
        (Metric.isOpen_ball.isClosed_compl)
    have hcontK : ContinuousOn riemannZeta K := by
      intro z hz
      have hzball : z ∉ Metric.ball (1 : ℂ) ε := hz.2
      have hz_ne_one : z ≠ (1 : ℂ) := by
        intro h
        apply hzball
        simpa [h] using (Metric.mem_ball_self (x := (1 : ℂ)) εpos)
      exact (differentiableAt_riemannZeta hz_ne_one).continuousAt.continuousWithinAt
    let S' : Set K := {x : K | riemannZeta x = 0}
    have hcontK' : Continuous (fun x : K => riemannZeta x) :=
      (continuousOn_iff_continuous_restrict).1 hcontK
    have hclosedS' : IsClosed S' := by
      have : S' = (fun x : K => riemannZeta x) ⁻¹' ({0} : Set ℂ) := by
        ext x
        simp [S']
      simpa [this] using (isClosed_singleton.preimage hcontK')
    haveI : CompactSpace K := (isCompact_iff_compactSpace.mp hKcomp)
    have hS'comp : IsCompact S' := IsClosed.isCompact hclosedS'
    have hScomp : IsCompact ((↑) '' S' : Set ℂ) :=
      (Subtype.isCompact_iff).1 hS'comp
    have himage : ((↑) '' S' : Set ℂ) = Z ∩ K := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : riemannZeta x = 0 := by
          simpa [S'] using hx
        exact ⟨by simpa [Z, hx'], x.property⟩
      · rintro ⟨hz0, hzK⟩
        refine ⟨⟨z, hzK⟩, ?_, rfl⟩
        simpa [S', Z] using hz0
    have hZKcomp : IsCompact (Z ∩ K) := by
      simpa [himage] using hScomp
    have hfin : (Z ∩ K).Finite := IsCompact.finite hZKcomp hdiscK
    exact hfin.subset fun z hz => ⟨hsubsetZ hz, hsubsetK hz⟩

/-- N(T) is well-defined (finite) for all T -/
theorem zeroCountingFunction_finite (T : ℝ) : (zeroCountingFunction T : ℕ∞) < ⊤ := by
  exact WithTop.coe_lt_top _

/-- The set zerosUpTo(T) is finite for all T -/
theorem zerosUpTo_finite (T : ℝ) : (zerosUpTo T).Finite := finite_zeros_le T

/-- The completed-zeta zero set in the strip is finite up to height `T`. -/
theorem completedZerosUpTo_finite (T : ℝ) : (completedZerosUpTo T).Finite := by
  simpa [zerosUpTo_eq_completed] using (zerosUpTo_finite T)

/-- The xi zero set in the strip is finite up to height `T`. -/
theorem xiZerosUpTo_finite (T : ℝ) : (xiZerosUpTo T).Finite := by
  simpa [zerosUpTo_eq_xi] using (zerosUpTo_finite T)

/-! ## Hypotheses -/

class ZeroCountingTendstoHyp : Prop where
  tendsto_atTop : Tendsto (fun T => (N T : ℝ)) atTop atTop

/-! ## Basic Properties -/

section BasicProperties

theorem zeroCountingFunction_nonneg (T : ℝ) : 0 ≤ N T := Nat.zero_le _

theorem zeroCountingFunction_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : N T₁ ≤ N T₂ := by
  apply Set.ncard_le_ncard (zerosUpTo_mono h) (finite_zeros_le T₂)

theorem zeroCountingFunction_neg (T : ℝ) (hT : T ≤ 0) : N T = 0 := by
  simp only [zeroCountingFunction]
  have : zetaNontrivialZerosPos ∩ { s : ℂ | s.im ≤ T } = ∅ := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro ⟨hs, him⟩
    simp only [mem_zetaNontrivialZerosPos] at hs
    linarith [hs.2]
  simp [this]

/-- N(0) = 0, since we only count zeros with positive imaginary part -/
theorem zeroCountingFunction_zero : N 0 = 0 :=
  zeroCountingFunction_neg 0 (le_refl 0)

/-- N(T) is always finite as a natural number -/
theorem zeroCountingFunction_nat (T : ℝ) : ∃ n : ℕ, N T = n := ⟨N T, rfl⟩

/-- Antitonicity is equivalent to monotonicity for N(T) -/
theorem zeroCountingFunction_antimono {T₁ T₂ : ℝ} (h : T₂ ≤ T₁) : N T₂ ≤ N T₁ :=
  zeroCountingFunction_mono h

/-- N(T) = 0 for all negative T -/
theorem zeroCountingFunction_neg_eq_zero {T : ℝ} (hT : T < 0) : N T = 0 :=
  zeroCountingFunction_neg T (le_of_lt hT)

/-- The zero counting function casted to ℝ is nonnegative -/
theorem zeroCountingFunction_cast_nonneg (T : ℝ) : 0 ≤ (N T : ℝ) := Nat.cast_nonneg _

/-- The zero counting function casted to ℝ is monotone -/
theorem zeroCountingFunction_cast_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : (N T₁ : ℝ) ≤ (N T₂ : ℝ) :=
  Nat.cast_le.mpr (zeroCountingFunction_mono h)

/-- If T₁ ≤ T₂, then the set of zeros up to T₁ is a subset of zeros up to T₂ -/
theorem zerosUpTo_subset_of_le {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : zerosUpTo T₁ ⊆ zerosUpTo T₂ :=
  zerosUpTo_mono h

/-- N(T) = 0 iff there are no zeros with imaginary part in (0, T] -/
theorem zeroCountingFunction_eq_zero_iff (T : ℝ) : N T = 0 ↔ zerosUpTo T = ∅ :=
  Set.ncard_eq_zero (zerosUpTo_finite T)

/-- N(T) → ∞ as T → ∞ -/
theorem zeroCountingFunction_tendsto_atTop [ZeroCountingTendstoHyp] :
    Tendsto (fun T => (N T : ℝ)) atTop atTop := by
  simpa using ZeroCountingTendstoHyp.tendsto_atTop

end BasicProperties

class ZeroCountingCrudeBoundHyp : Prop where
  crude_bound : ∃ C : ℝ, ∀ {T : ℝ}, 4 ≤ T → (N T : ℝ) ≤ C * T * Real.log T

class ZeroCountingSpecialValuesHyp : Prop where
  fourteen : N 14 = 0

class ZeroCountingFifteenHyp : Prop where
  fifteen : N 15 = 1

class FirstZeroOrdinateHyp : Prop where
  bounds :
    ∃ γ₁ ∈ zetaZeroOrdinates, 14.13 < γ₁ ∧ γ₁ < 14.14 ∧
      ∀ γ ∈ zetaZeroOrdinates, γ₁ ≤ γ

/-! ### Global instances (axioms) -/

/-- AXIOM: N(15) = 1. -/
axiom zeroCountingFifteen_axiom : N 15 = 1

instance instZeroCountingFifteenHyp : ZeroCountingFifteenHyp :=
  ⟨zeroCountingFifteen_axiom⟩

/-- AXIOM: the first zero ordinate lies in (14.13, 14.14). -/
axiom firstZeroOrdinate_bounds_axiom :
    ∃ γ₁ ∈ zetaZeroOrdinates, 14.13 < γ₁ ∧ γ₁ < 14.14 ∧
      ∀ γ ∈ zetaZeroOrdinates, γ₁ ≤ γ

instance instFirstZeroOrdinateHyp : FirstZeroOrdinateHyp :=
  ⟨firstZeroOrdinate_bounds_axiom⟩

instance instZeroCountingSpecialValuesHyp : ZeroCountingSpecialValuesHyp := by
  refine ⟨?_⟩
  rcases firstZeroOrdinate_bounds_axiom with ⟨γ₁, _, hγ₁low, _, hγ₁min⟩
  apply (zeroCountingFunction_eq_zero_iff 14).2
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hz' : z ∈ zetaNontrivialZerosPos ∧ z.im ≤ 14 := by
    simpa [zerosUpTo] using hz
  have hzpos : z ∈ zetaNontrivialZerosPos := hz'.1
  have hle : z.im ≤ 14 := hz'.2
  have hzord : z.im ∈ zetaZeroOrdinates := ⟨z, hzpos, rfl⟩
  have h14lt : (14 : ℝ) < γ₁ := by
    have h14 : (14 : ℝ) < 14.13 := by norm_num
    exact lt_trans h14 hγ₁low
  have hlt : z.im < γ₁ := lt_of_le_of_lt hle h14lt
  exact (not_le_of_gt hlt) (hγ₁min _ hzord)

/-! ## Specific Bounds -/

section SpecificBounds

/-- N(T) ≤ C * T * log T for T ≥ 4 -/
theorem zeroCountingFunction_crude_bound [ZeroCountingCrudeBoundHyp] :
    ∃ C : ℝ, ∀ {T : ℝ}, 4 ≤ T → (N T : ℝ) ≤ C * T * Real.log T := by
  simpa using ZeroCountingCrudeBoundHyp.crude_bound

/-- N(14) = 0 (the first zero is at T ≈ 14.13...) -/
theorem zeroCountingFunction_fourteen : N 14 = 0 := by
  simpa using ZeroCountingSpecialValuesHyp.fourteen

/-- N(15) = 1 (the first zero is at T ≈ 14.13...) -/
theorem zeroCountingFunction_fifteen : N 15 = 1 := by
  simpa using ZeroCountingFifteenHyp.fifteen

/-- The first zero ordinate γ₁ ≈ 14.134725... -/
theorem firstZeroOrdinate_bounds :
    ∃ γ₁ ∈ zetaZeroOrdinates, 14.13 < γ₁ ∧ γ₁ < 14.14 ∧
      ∀ γ ∈ zetaZeroOrdinates, γ₁ ≤ γ := by
  simpa using FirstZeroOrdinateHyp.bounds

end SpecificBounds

class ZeroCountingAsymptoticHyp : Prop where
  asymptotic :
    (fun T => (N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π))
    =O[atTop] (fun T => Real.log T)

class ZeroCountingRvmExplicitHyp : Prop where
  bound :
    ∃ C T0 : ℝ, ∀ T ≥ T0,
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * Real.log T

class ZeroCountingAsymptoticRatioHyp : Prop where
  asymptotic' :
    Tendsto (fun T => (N T : ℝ) / ((T / (2 * π)) * Real.log (T / (2 * π)))) atTop (𝓝 1)

class ZeroCountingMainTermHyp : Prop where
  mainTerm :
    Tendsto (fun T => (N T : ℝ) / (T / (2 * π) * Real.log T)) atTop (𝓝 1)

class ZeroCountingLowerBoundHyp : Prop where
  lower_bound : ∃ T0 : ℝ, ∀ T ≥ T0, T / (3 * π) * Real.log T ≤ N T

/-! ### Global instances (axioms) -/

/-- AXIOM: explicit Riemann–von Mangoldt bound. -/
axiom zeroCountingRvmExplicit_axiom :
    ∃ C T0 : ℝ, ∀ T ≥ T0,
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * Real.log T

instance instZeroCountingRvmExplicitHyp : ZeroCountingRvmExplicitHyp :=
  ⟨zeroCountingRvmExplicit_axiom⟩

instance instZeroCountingAsymptoticHyp : ZeroCountingAsymptoticHyp := by
  classical
  refine ⟨?_⟩
  rcases ZeroCountingRvmExplicitHyp.bound with ⟨C, T0, hC⟩
  let C0 : ℝ := max C 0
  refine (Asymptotics.isBigO_iff.2 ?_)
  refine ⟨C0, ?_⟩
  refine (eventually_ge_atTop (max T0 1)).mono ?_
  intro T hT
  have hT0 : T0 ≤ T := le_trans (le_max_left _ _) hT
  have h1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hlogabs : |Real.log T| = Real.log T := by
    exact abs_of_nonneg (Real.log_nonneg h1)
  have hbound := hC T hT0
  have hC_le : C * Real.log T ≤ C0 * Real.log T := by
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg h1)
  have hbound' :
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C0 * Real.log T := hbound.trans hC_le
  simpa [Real.norm_eq_abs, hlogabs] using hbound'


/-! ## Asymptotic Formula -/

section Asymptotics

open Asymptotics

/-- The Riemann-von Mangoldt formula: N(T) = (T/2π) log(T/2π) - T/2π + O(log T) -/
theorem zeroCountingFunction_asymptotic :
    (fun T => (N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π))
    =O[atTop] (fun T => Real.log T) := by
  simpa using ZeroCountingAsymptoticHyp.asymptotic

/-- Main term approximation -/
theorem zeroCountingFunction_asymptotic' [ZeroCountingMainTermHyp] :
    Tendsto (fun T => (N T : ℝ) / ((T / (2 * π)) * Real.log (T / (2 * π)))) atTop (𝓝 1) := by
  classical
  set c : ℝ := Real.log (2 * π)
  have hlog : Tendsto (fun T => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have hdiv : Tendsto (fun T => c / Real.log T) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop (g := fun T => Real.log T) hlog c
  have hlog_ne : ∀ᶠ T in atTop, Real.log T ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact ne_of_gt (Real.log_pos (by linarith))
  have hlog_div :
      (fun T => Real.log (T / (2 * π))) =ᶠ[atTop] (fun T => Real.log T - c) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hTne : T ≠ 0 := by linarith
    have h2pi_ne : (2 * π : ℝ) ≠ 0 := by
      have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
      exact ne_of_gt h2pi_pos
    simp [c, Real.log_div hTne h2pi_ne]
  have hratio_base :
      Tendsto (fun T => (Real.log T - c) / Real.log T) atTop (𝓝 1) := by
    have hcongr :
        (fun T => (Real.log T - c) / Real.log T) =ᶠ[atTop]
          (fun T => 1 - c / Real.log T) := by
      refine hlog_ne.mono ?_
      intro T hT
      calc
        (Real.log T - c) / Real.log T
            = Real.log T / Real.log T - c / Real.log T := by
                simp [sub_div]
        _ = 1 - c / Real.log T := by
                simp [div_self hT]
    have hlim : Tendsto (fun T => 1 - c / Real.log T) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hdiv)
    exact hlim.congr' hcongr.symm
  have hratio_inv :
      Tendsto (fun T => (Real.log T - c) / Real.log T)⁻¹ atTop (𝓝 1) := by
    simpa using
      (tendsto_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).comp hratio_base
  have hratio :
      Tendsto (fun T => Real.log T / Real.log (T / (2 * π))) atTop (𝓝 1) := by
    have hratio' : Tendsto (fun T => Real.log T / (Real.log T - c)) atTop (𝓝 1) := by
      refine hratio_inv.congr' ?_
      refine Filter.Eventually.of_forall ?_
      intro T
      simp [inv_div]
    refine hratio'.congr' ?_
    refine hlog_div.mono ?_
    intro T hT
    simp [hT]
  have hmain : Tendsto (fun T => (N T : ℝ) / (T / (2 * π) * Real.log T)) atTop (𝓝 1) := by
    simpa using ZeroCountingMainTermHyp.mainTerm
  have hmul :
      Tendsto
        (fun T =>
          (N T : ℝ) / (T / (2 * π) * Real.log T) *
            (Real.log T / Real.log (T / (2 * π)))) atTop (𝓝 1) := by
    simpa using hmain.mul hratio
  have hcongr :
      (fun T => (N T : ℝ) / ((T / (2 * π)) * Real.log (T / (2 * π)))) =ᶠ[atTop]
        (fun T =>
          (N T : ℝ) / (T / (2 * π) * Real.log T) *
            (Real.log T / Real.log (T / (2 * π)))) := by
    filter_upwards [eventually_gt_atTop (2 * π)] with T hT
    have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
    have hT_gt_one : (1 : ℝ) < T := by
      nlinarith [Real.pi_gt_three, hT]
    have hlogT : Real.log T ≠ 0 := by
      exact ne_of_gt (Real.log_pos hT_gt_one)
    have hlogDiv : Real.log (T / (2 * π)) ≠ 0 := by
      have hpos : 1 < T / (2 * π) := by
        have : (2 * π : ℝ) < T := hT
        exact (one_lt_div h2pi_pos).2 this
      exact ne_of_gt (Real.log_pos hpos)
    field_simp [hlogT, hlogDiv, mul_comm, mul_left_comm, mul_assoc]
  exact hmul.congr' hcongr.symm

/-- For large T, N(T) ~ (T/2π) log T -/
theorem zeroCountingFunction_mainTerm [ZeroCountingMainTermHyp] :
    Tendsto (fun T => (N T : ℝ) / (T / (2 * π) * Real.log T)) atTop (𝓝 1) := by
  simpa using ZeroCountingMainTermHyp.mainTerm

noncomputable instance zeroCountingAsymptoticRatioHyp_of_mainTerm
    [ZeroCountingMainTermHyp] :
    ZeroCountingAsymptoticRatioHyp := by
  classical
  exact ⟨zeroCountingFunction_asymptotic'⟩

noncomputable instance zeroCountingMainTermHyp_of_asymptotic :
    ZeroCountingMainTermHyp := by
  classical
  refine ⟨?_⟩
  set g : ℝ → ℝ := fun T => (T / (2 * π)) * Real.log (T / (2 * π))
  set c : ℝ := Real.log (2 * π)
  have h_asymp :
      (fun T => (N T : ℝ) - g T + T / (2 * π)) =O[atTop] (fun T => Real.log T) := by
    simpa [g] using zeroCountingFunction_asymptotic
  have hlog : Tendsto (fun T => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have hdiv : Tendsto (fun T => c / Real.log T) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop (g := fun T => Real.log T) hlog c
  have hlog_ne : ∀ᶠ T in atTop, Real.log T ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact ne_of_gt (Real.log_pos (by linarith))
  have hlog_div :
      (fun T => Real.log (T / (2 * π))) =ᶠ[atTop] (fun T => Real.log T - c) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hTne : T ≠ 0 := by linarith
    have h2pi_ne : (2 * π : ℝ) ≠ 0 := by
      have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
      exact ne_of_gt h2pi_pos
    simp [c, Real.log_div hTne h2pi_ne]
  have hratio_base :
      Tendsto (fun T => (Real.log T - c) / Real.log T) atTop (𝓝 1) := by
    have hcongr :
        (fun T => (Real.log T - c) / Real.log T) =ᶠ[atTop]
          (fun T => 1 - c / Real.log T) := by
      refine hlog_ne.mono ?_
      intro T hT
      calc
        (Real.log T - c) / Real.log T
            = Real.log T / Real.log T - c / Real.log T := by
                simp [sub_div]
        _ = 1 - c / Real.log T := by
                simp [div_self hT]
    have hlim : Tendsto (fun T => 1 - c / Real.log T) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hdiv)
    exact hlim.congr' hcongr.symm
  have hlogratio :
      Tendsto (fun T => Real.log (T / (2 * π)) / Real.log T) atTop (𝓝 1) := by
    refine hratio_base.congr' ?_
    refine hlog_div.mono ?_
    intro T hT
    simp [hT]
  have hdiv_atTop : Tendsto (fun T => T / (2 * π)) atTop atTop :=
    (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop).atTop_div_const
      (by nlinarith [Real.pi_pos])
  have hlogratio_atTop :
      Tendsto (fun T => g T / Real.log T) atTop atTop := by
    have hmul :
        Tendsto
          (fun T =>
            (T / (2 * π)) * (Real.log (T / (2 * π)) / Real.log T)) atTop atTop :=
      (Filter.Tendsto.atTop_mul_pos (C := 1) (by linarith) hdiv_atTop hlogratio)
    have hcongr :
        (fun T => g T / Real.log T) =ᶠ[atTop]
          (fun T => (T / (2 * π)) * (Real.log (T / (2 * π)) / Real.log T)) := by
      refine Filter.Eventually.of_forall ?_
      intro T
      simp [g, mul_div_assoc]
    exact hmul.congr' hcongr.symm
  have hlog_div_zero : Tendsto (fun T => Real.log T / g T) atTop (𝓝 0) := by
    have hinv := tendsto_inv_atTop_zero.comp hlogratio_atTop
    have hcongr :
        (fun T => Real.log T / g T) =ᶠ[atTop]
          (fun T => (g T / Real.log T)⁻¹) := by
      refine Filter.Eventually.of_forall ?_
      intro T
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    exact hinv.congr' hcongr.symm
  have h_g_ne : ∀ᶠ T in atTop, g T ≠ 0 := by
    filter_upwards [eventually_gt_atTop (2 * π)] with T hT
    have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
    have hTpos : 0 < T := by linarith
    have hlogpos : 0 < Real.log (T / (2 * π)) := by
      have hpos : 1 < T / (2 * π) := (one_lt_div h2pi_pos).2 hT
      exact Real.log_pos hpos
    have hpos : 0 < g T := by
      exact mul_pos (div_pos hTpos h2pi_pos) hlogpos
    exact ne_of_gt hpos
  have hlog_o : (fun T => Real.log T) =o[atTop] g := by
    refine (isLittleO_iff_tendsto' ?_).2 hlog_div_zero
    filter_upwards [h_g_ne] with T hT
    intro hzero
    exact (hT hzero).elim
  have hlog_div_atTop : Tendsto (fun T => Real.log (T / (2 * π))) atTop atTop :=
    Real.tendsto_log_atTop.comp hdiv_atTop
  have hlin_div_zero : Tendsto (fun T => (T / (2 * π)) / g T) atTop (𝓝 0) := by
    have hinv := tendsto_inv_atTop_zero.comp hlog_div_atTop
    have hcongr :
        (fun T => (T / (2 * π)) / g T) =ᶠ[atTop]
          (fun T => (Real.log (T / (2 * π)))⁻¹) := by
      filter_upwards [eventually_gt_atTop (2 * π)] with T hT
      have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
      have hTpos : 0 < T := by linarith
      have hTne : (T / (2 * π) : ℝ) ≠ 0 := by
        exact ne_of_gt (div_pos hTpos h2pi_pos)
      simpa [g] using
        (div_mul_cancel_left₀ (a := (T / (2 * π) : ℝ))
          (b := Real.log (T / (2 * π))) hTne)
    exact hinv.congr' hcongr.symm
  have hlin_o : (fun T => T / (2 * π)) =o[atTop] g := by
    refine (isLittleO_iff_tendsto' ?_).2 hlin_div_zero
    filter_upwards [h_g_ne] with T hT
    intro hzero
    exact (hT hzero).elim
  have hE_o :
      (fun T => (N T : ℝ) - g T + T / (2 * π)) =o[atTop] g :=
    h_asymp.trans_isLittleO hlog_o
  have hdiff : (fun T => (N T : ℝ) - g T) =o[atTop] g := by
    simpa [g] using hE_o.sub hlin_o
  have hratio0 : Tendsto (fun T => ((N T : ℝ) - g T) / g T) atTop (𝓝 0) :=
    hdiff.tendsto_div_nhds_zero
  have hratio : Tendsto (fun T => (N T : ℝ) / g T) atTop (𝓝 1) := by
    have hcongr :
        (fun T => (N T : ℝ) / g T) =ᶠ[atTop]
          (fun T => ((N T : ℝ) - g T) / g T + 1) := by
      refine h_g_ne.mono ?_
      intro T hT
      calc
        (N T : ℝ) / g T
            = ((N T : ℝ) - g T + g T) / g T := by
                simp
        _ = ((N T : ℝ) - g T) / g T + g T / g T := by
                simpa [add_div] using (add_div ((N T : ℝ) - g T) (g T) (g T))
        _ = ((N T : ℝ) - g T) / g T + 1 := by
                simp [hT]
    have hsum :
        Tendsto (fun T => ((N T : ℝ) - g T) / g T + 1) atTop (𝓝 1) := by
      simpa using (hratio0.add tendsto_const_nhds)
    exact hsum.congr' hcongr.symm
  have hmul :
      Tendsto
        (fun T => (N T : ℝ) / g T * (Real.log (T / (2 * π)) / Real.log T))
        atTop (𝓝 1) := by
    simpa using hratio.mul hlogratio
  have hcongr :
      (fun T => (N T : ℝ) / (T / (2 * π) * Real.log T)) =ᶠ[atTop]
        (fun T => (N T : ℝ) / g T * (Real.log (T / (2 * π)) / Real.log T)) := by
    filter_upwards [eventually_gt_atTop (2 * π)] with T hT
    have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
    have hlogT : Real.log T ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by nlinarith [Real.pi_gt_three, hT]))
    have hlogDiv : Real.log (T / (2 * π)) ≠ 0 := by
      have hpos : 1 < T / (2 * π) := (one_lt_div h2pi_pos).2 hT
      exact ne_of_gt (Real.log_pos hpos)
    have hcalc :
        (N T : ℝ) / (T / (2 * π) * Real.log T) =
          (N T : ℝ) / ((T / (2 * π)) * Real.log (T / (2 * π))) *
            (Real.log (T / (2 * π)) / Real.log T) := by
      field_simp [hlogT, hlogDiv, mul_comm, mul_left_comm, mul_assoc]
    simpa [g] using hcalc
  exact hmul.congr' hcongr.symm

/-! ### Explicit error term (big-O) -/

lemma zeroCountingFunction_rvm_eventually_bound :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * |Real.log T| := by
  rcases (Asymptotics.isBigO_iff.1 zeroCountingFunction_asymptotic) with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  simpa [Real.norm_eq_abs] using hC

lemma zeroCountingFunction_rvm_eventually_bound_log :
    ∃ C T0 : ℝ, ∀ T ≥ T0,
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * Real.log T := by
  rcases zeroCountingFunction_rvm_eventually_bound with ⟨C, hC⟩
  rcases (Filter.eventually_atTop.1 hC) with ⟨T0, hT0⟩
  refine ⟨C, max T0 1, ?_⟩
  intro T hT
  have hT0' : T0 ≤ T := le_trans (le_max_left _ _) hT
  have h1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hlogabs : |Real.log T| = Real.log T := by
    exact abs_of_nonneg (Real.log_nonneg h1)
  have hbound :=
    hT0 T hT0'
  simpa [hlogabs] using hbound

/-- Riemann–von Mangoldt with explicit `O(log T)` error term. -/
theorem zeroCountingFunction_rvm_explicit :
    ∃ C T0 : ℝ, ∀ T ≥ T0,
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * Real.log T := by
  simpa using zeroCountingFunction_rvm_eventually_bound_log

theorem zeroCountingFunction_rvm_explicit_hyp :
    ∃ C T0 : ℝ, ∀ T ≥ T0,
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * Real.log T := by
  simpa using ZeroCountingRvmExplicitHyp.bound

/-- Lower bound: eventually N(T) ≥ T/(3π) log T. -/
theorem zeroCountingFunction_lower_bound [ZeroCountingLowerBoundHyp] :
    ∃ T0 : ℝ, ∀ T ≥ T0, T / (3 * π) * Real.log T ≤ N T := by
  simpa using ZeroCountingLowerBoundHyp.lower_bound

instance zeroCountingTendstoHyp_of_lower_bound [ZeroCountingLowerBoundHyp] :
    ZeroCountingTendstoHyp := by
  refine ⟨?_⟩
  refine tendsto_atTop_atTop.2 ?_
  intro b
  have hmul : Tendsto (fun T : ℝ => T * Real.log T) atTop atTop :=
    (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop)
  have hpos : 0 < (1 / (3 * π) : ℝ) := by
    have hdenom : 0 < (3 * π : ℝ) := by nlinarith [Real.pi_pos]
    exact one_div_pos.mpr hdenom
  have hconst :
      Tendsto (fun T : ℝ => (1 / (3 * π)) * (T * Real.log T)) atTop atTop :=
    (Tendsto.const_mul_atTop hpos hmul)
  rcases (tendsto_atTop_atTop.1 hconst b) with ⟨T0, hT0⟩
  rcases zeroCountingFunction_lower_bound with ⟨T1, hT1⟩
  refine ⟨max T0 T1, ?_⟩
  intro T hT
  have hT0' : T0 ≤ T := le_trans (le_max_left _ _) hT
  have hT1' : T1 ≤ T := le_trans (le_max_right _ _) hT
  have hb : b ≤ (1 / (3 * π)) * (T * Real.log T) := hT0 T hT0'
  have hlow :
      (1 / (3 * π)) * (T * Real.log T) ≤ N T := by
    have hlow' := hT1 T hT1'
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlow'
  exact hb.trans hlow

/-- Upper bound: `N(T) ≤ C * T * log T` for `T ≥ 4`. -/
theorem zeroCountingFunction_upper_bound :
    ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T → (N T : ℝ) ≤ C * T * Real.log T := by
  rcases zeroCountingFunction_rvm_explicit with ⟨C, T0, hC⟩
  set C0 : ℝ := max C 0
  let T1 : ℝ := max T0 4
  let C1 : ℝ := (1 / (2 * π)) + C0
  let Csmall : ℝ := (N T1 : ℝ) / (4 * Real.log 4)
  let Cfinal : ℝ := max C1 Csmall
  refine ⟨Cfinal, ?_⟩
  intro T hT
  have hlog4pos : 0 < Real.log 4 := by
    have h : (1 : ℝ) < 4 := by linarith
    exact Real.log_pos h
  have hlog4pos' : 0 < (4 * Real.log 4 : ℝ) := by
    nlinarith [hlog4pos]
  have hTpos : 0 < T := by linarith [hT]
  by_cases hlarge : T1 ≤ T
  · have hT0 : T0 ≤ T := le_trans (le_max_left _ _) hlarge
    have hlogpos : 0 ≤ Real.log T := by
      exact Real.log_nonneg (by linarith [hT] : (1 : ℝ) ≤ T)
    have hErr : |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C0 * Real.log T := by
      have h := hC T hT0
      have hC_le : C * Real.log T ≤ C0 * Real.log T := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlogpos
      exact h.trans hC_le
    have hmain :
        (N T : ℝ) ≤
          (T / (2 * π)) * Real.log (T / (2 * π)) - T / (2 * π) + C0 * Real.log T := by
      have h_upper := (abs_le.mp hErr).2
      linarith
    have hpi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
    have hpi1 : (1 : ℝ) ≤ 2 * π := by
      have hpi3 : (3 : ℝ) < π := pi_gt_three
      linarith
    have hdivle : T / (2 * π) ≤ T := by
      exact div_le_self (le_of_lt hTpos) hpi1
    have hlogle : Real.log (T / (2 * π)) ≤ Real.log T := by
      exact Real.log_le_log (div_pos hTpos hpi_pos) hdivle
    have hmul :
        (T / (2 * π)) * Real.log (T / (2 * π)) ≤ (T / (2 * π)) * Real.log T := by
      have hnonneg : 0 ≤ T / (2 * π) := by
        exact le_of_lt (div_pos hTpos hpi_pos)
      exact mul_le_mul_of_nonneg_left hlogle hnonneg
    have hnonneg_div : 0 ≤ T / (2 * π) := by
      exact le_of_lt (div_pos hTpos hpi_pos)
    have hstep :
        (N T : ℝ) ≤ (T / (2 * π)) * Real.log T + C0 * Real.log T := by
      linarith [hmain, hmul, hnonneg_div]
    have hstep' :
        (N T : ℝ) ≤ C1 * T * Real.log T := by
      have hlogpos' : 0 ≤ C0 * Real.log T := by
        exact mul_nonneg (le_max_right _ _) hlogpos
      have hT1' : (1 : ℝ) ≤ T := by linarith [hT]
      have hmul_le :
          C0 * Real.log T ≤ C0 * Real.log T * T := by
        have hnonneg : 0 ≤ C0 * Real.log T := hlogpos'
        have hT1'' : (1 : ℝ) ≤ T := hT1'
        have hmul := mul_le_mul_of_nonneg_left hT1'' hnonneg
        simpa [mul_one, mul_assoc] using hmul
      calc
        (N T : ℝ) ≤ (T / (2 * π)) * Real.log T + C0 * Real.log T := hstep
        _ ≤ (T / (2 * π)) * Real.log T + C0 * Real.log T * T := by
              linarith [hmul_le]
        _ = C1 * T * Real.log T := by
              dsimp [C1]
              calc
                (T / (2 * π)) * Real.log T + C0 * Real.log T * T
                    = (1 / (2 * π)) * (T * Real.log T) + C0 * (T * Real.log T) := by
                        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
                _ = ((1 / (2 * π)) + C0) * (T * Real.log T) := by
                        symm
                        simp [mul_add, add_mul, mul_assoc, add_comm, add_left_comm, add_assoc]
                _ = ((1 / (2 * π)) + C0) * T * Real.log T := by
                        simp [mul_assoc]
    have hCfinal : C1 ≤ Cfinal := by
      exact le_max_left _ _
    have hmul :
        C1 * T * Real.log T ≤ Cfinal * T * Real.log T := by
      have hnonneg : 0 ≤ T * Real.log T := by
        exact mul_nonneg (le_of_lt hTpos) hlogpos
      have hmul' := mul_le_mul_of_nonneg_right hCfinal hnonneg
      simpa [mul_left_comm, mul_assoc] using hmul'
    exact hstep'.trans hmul
  · have hTle : T ≤ T1 := le_of_not_ge hlarge
    have hmono : N T ≤ N T1 := zeroCountingFunction_mono hTle
    have hle : (N T : ℝ) ≤ (N T1 : ℝ) := by exact_mod_cast hmono
    have hlog4le : Real.log 4 ≤ Real.log T := by
      have h4pos : 0 < (4 : ℝ) := by linarith
      exact Real.log_le_log h4pos hT
    have hlogpos : 0 ≤ Real.log T := by
      exact le_trans (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4)) hlog4le
    have hTlog : 4 * Real.log 4 ≤ T * Real.log T := by
      have hT_nonneg : 0 ≤ T := by linarith [hT]
      have hlog4_nonneg : 0 ≤ Real.log 4 := by exact le_of_lt hlog4pos
      exact
        mul_le_mul hT hlog4le hlog4_nonneg hT_nonneg
    have hCsmall_nonneg : 0 ≤ Csmall := by
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hlog4pos')
    have hsmall :
        (N T1 : ℝ) ≤ Csmall * T * Real.log T := by
      have hmul := mul_le_mul_of_nonneg_left hTlog hCsmall_nonneg
      have hne : (4 * Real.log 4 : ℝ) ≠ 0 := by linarith [hlog4pos]
      have hleft :
          Csmall * (4 * Real.log 4) = (N T1 : ℝ) := by
        simpa [Csmall] using
          (div_mul_cancel₀ (a := (N T1 : ℝ)) (b := 4 * Real.log 4) hne)
      have hright :
          Csmall * (T * Real.log T) = Csmall * T * Real.log T := by
        simp [mul_assoc]
      simpa [hleft, hright] using hmul
    have hCfinal : Csmall ≤ Cfinal := by
      exact le_max_right _ _
    have hmul :
        Csmall * T * Real.log T ≤ Cfinal * T * Real.log T := by
      have hnonneg : 0 ≤ T * Real.log T := by
        exact mul_nonneg (le_of_lt hTpos) hlogpos
      have hmul' := mul_le_mul_of_nonneg_right hCfinal hnonneg
      simpa [mul_left_comm, mul_assoc] using hmul'
    exact (hle.trans hsmall).trans hmul

/-- Upper bound from the main term: `N(T) ≤ C * T * log T` for `T ≥ 4`. -/
theorem zeroCountingFunction_upper_bound_of_mainTerm :
    ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T → (N T : ℝ) ≤ C * T * Real.log T := by
  have hmain : Tendsto (fun T => (N T : ℝ) / (T / (2 * π) * Real.log T)) atTop (𝓝 1) :=
    zeroCountingFunction_mainTerm
  have hlt : ∀ᶠ T in atTop,
      (N T : ℝ) / (T / (2 * π) * Real.log T) < 2 :=
    (tendsto_order.1 hmain).2 _ (by norm_num)
  have hpos : ∀ᶠ T in (atTop : Filter ℝ), 0 < (T / (2 * π)) * Real.log T := by
    have hT : ∀ᶠ T in (atTop : Filter ℝ), 1 < T := eventually_gt_atTop (1 : ℝ)
    refine hT.mono ?_
    intro T hT
    have hlogpos : 0 < Real.log T := Real.log_pos hT
    have hpi : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
    have hTpos : 0 < T := lt_trans (by exact zero_lt_one) hT
    have hdivpos : 0 < T / (2 * π) := div_pos hTpos hpi
    exact mul_pos hdivpos hlogpos
  have hupper : ∀ᶠ T in atTop, (N T : ℝ) ≤ (1 / π) * T * Real.log T := by
    refine (hlt.and hpos).mono ?_
    intro T hT
    have hratio :
        (N T : ℝ) / (T / (2 * π) * Real.log T) < 2 := hT.1
    have hpos' : 0 < (T / (2 * π)) * Real.log T := hT.2
    have hmul :
        (N T : ℝ) < 2 * ((T / (2 * π)) * Real.log T) :=
      (div_lt_iff₀ hpos').1 hratio
    have hcoeff :
        2 * ((T / (2 * π)) * Real.log T) = (1 / π) * T * Real.log T := by
      field_simp [Real.pi_ne_zero, mul_comm, mul_left_comm, mul_assoc]
    have hmul' : (N T : ℝ) < (1 / π) * T * Real.log T := by
      simpa [hcoeff] using hmul
    exact le_of_lt hmul'
  rcases (eventually_atTop.1 hupper) with ⟨T0, hT0⟩
  set C1 : ℝ := 1 / π
  let T1 : ℝ := max T0 4
  let Csmall : ℝ := (N T1 : ℝ) / (4 * Real.log 4)
  let Cfinal : ℝ := max C1 Csmall
  refine ⟨Cfinal, ?_⟩
  intro T hT
  have hlog4pos : 0 < Real.log 4 := by
    have h : (1 : ℝ) < 4 := by linarith
    exact Real.log_pos h
  have hlog4pos' : 0 < (4 * Real.log 4 : ℝ) := by
    nlinarith [hlog4pos]
  have hTpos : 0 < T := by linarith [hT]
  by_cases hlarge : T1 ≤ T
  · have hT0' : T0 ≤ T := le_trans (le_max_left _ _) hlarge
    have hbound : (N T : ℝ) ≤ C1 * T * Real.log T := by
      have h := hT0 T hT0'
      simpa [C1] using h
    have hCfinal : C1 ≤ Cfinal := by
      exact le_max_left _ _
    have hlogpos : 0 ≤ Real.log T := by
      exact Real.log_nonneg (by linarith [hT] : (1 : ℝ) ≤ T)
    have hmul :
        C1 * T * Real.log T ≤ Cfinal * T * Real.log T := by
      have hnonneg : 0 ≤ T * Real.log T := by
        exact mul_nonneg (le_of_lt hTpos) hlogpos
      have hmul' := mul_le_mul_of_nonneg_right hCfinal hnonneg
      simpa [mul_left_comm, mul_assoc] using hmul'
    exact hbound.trans hmul
  · have hTle : T ≤ T1 := le_of_not_ge hlarge
    have hmono : N T ≤ N T1 := zeroCountingFunction_mono hTle
    have hle : (N T : ℝ) ≤ (N T1 : ℝ) := by exact_mod_cast hmono
    have hlog4le : Real.log 4 ≤ Real.log T := by
      have h4pos : 0 < (4 : ℝ) := by linarith
      exact Real.log_le_log h4pos hT
    have hlogpos : 0 ≤ Real.log T := by
      exact le_trans (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4)) hlog4le
    have hTlog : 4 * Real.log 4 ≤ T * Real.log T := by
      have hT_nonneg : 0 ≤ T := by linarith [hT]
      have hlog4_nonneg : 0 ≤ Real.log 4 := by exact le_of_lt hlog4pos
      exact
        mul_le_mul hT hlog4le hlog4_nonneg hT_nonneg
    have hCsmall_nonneg : 0 ≤ Csmall := by
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hlog4pos')
    have hsmall :
        (N T1 : ℝ) ≤ Csmall * T * Real.log T := by
      have hmul := mul_le_mul_of_nonneg_left hTlog hCsmall_nonneg
      have hne : (4 * Real.log 4 : ℝ) ≠ 0 := by linarith [hlog4pos]
      have hleft :
          Csmall * (4 * Real.log 4) = (N T1 : ℝ) := by
        simpa [Csmall] using
          (div_mul_cancel₀ (a := (N T1 : ℝ)) (b := 4 * Real.log 4) hne)
      have hright :
          Csmall * (T * Real.log T) = Csmall * T * Real.log T := by
        simp [mul_assoc]
      simpa [hleft, hright] using hmul
    have hCfinal : Csmall ≤ Cfinal := by
      exact le_max_right _ _
    have hmul :
        Csmall * T * Real.log T ≤ Cfinal * T * Real.log T := by
      have hnonneg : 0 ≤ T * Real.log T := by
        exact mul_nonneg (le_of_lt hTpos) hlogpos
      have hmul' := mul_le_mul_of_nonneg_right hCfinal hnonneg
      simpa [mul_left_comm, mul_assoc] using hmul'
    exact (hle.trans hsmall).trans hmul

noncomputable instance zeroCountingCrudeBoundHyp_of_asymptotic :
    ZeroCountingCrudeBoundHyp := by
  classical
  rcases zeroCountingFunction_upper_bound with ⟨C, hC⟩
  exact ⟨C, fun {T} hT => hC T hT⟩

noncomputable instance zeroCountingCrudeBoundHyp_of_mainTerm :
    ZeroCountingCrudeBoundHyp := by
  classical
  rcases zeroCountingFunction_upper_bound_of_mainTerm with ⟨C, hC⟩
  exact ⟨C, fun {T} hT => hC T hT⟩

noncomputable instance zeroCountingLowerBoundHyp_of_mainTerm :
    ZeroCountingLowerBoundHyp := by
  classical
  refine ⟨?_⟩
  have hmain : Tendsto (fun T => (N T : ℝ) / (T / (2 * π) * Real.log T)) atTop (𝓝 1) :=
    zeroCountingFunction_mainTerm
  have hlt : ∀ᶠ T in atTop, (2 / 3 : ℝ) <
      (N T : ℝ) / (T / (2 * π) * Real.log T) :=
    (tendsto_order.1 hmain).1 _ (by norm_num)
  have hpos : ∀ᶠ T in (atTop : Filter ℝ), 0 < (T / (2 * π)) * Real.log T := by
    have hT : ∀ᶠ T in (atTop : Filter ℝ), 1 < T := eventually_gt_atTop (1 : ℝ)
    refine hT.mono ?_
    intro T hT
    have hlogpos : 0 < Real.log T := Real.log_pos hT
    have hpi : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
    have hTpos : 0 < T := lt_trans (by exact zero_lt_one) hT
    have hdivpos : 0 < T / (2 * π) := div_pos hTpos hpi
    exact mul_pos hdivpos hlogpos
  have hlow : ∀ᶠ T in atTop, T / (3 * π) * Real.log T ≤ N T := by
    refine (hlt.and hpos).mono ?_
    intro T hT
    have hratio : (2 / 3 : ℝ) < (N T : ℝ) / (T / (2 * π) * Real.log T) := hT.1
    have hpos' : 0 < (T / (2 * π)) * Real.log T := hT.2
    have hmul : (2 / 3 : ℝ) * ((T / (2 * π)) * Real.log T) < (N T : ℝ) :=
      (lt_div_iff₀ hpos').1 hratio
    have hcoeff :
        (2 / 3 : ℝ) * ((T / (2 * π)) * Real.log T)
          = T / (3 * π) * Real.log T := by
      field_simp [Real.pi_ne_zero, mul_comm, mul_left_comm, mul_assoc]
    have hmul' : T / (3 * π) * Real.log T < (N T : ℝ) := by
      simpa [hcoeff] using hmul
    exact le_of_lt hmul'
  rcases (eventually_atTop.1 hlow) with ⟨T0, hT0⟩
  exact ⟨T0, fun T hT => hT0 T hT⟩

end Asymptotics

class ZeroCountingLocalDensityHyp : Prop where
  local_density :
    ∃ C T0 : ℝ, ∀ {T h : ℝ}, T0 ≤ T → 0 ≤ h →
      (N (T + h) : ℝ) - N T ≤ C * (h + 1) * (Real.log (T + h) + 1)

/-! ### Global instances -/

noncomputable instance zeroCountingLocalDensityHyp_of_asymptotic :
    ZeroCountingLocalDensityHyp := by
  classical
  rcases zeroCountingFunction_rvm_explicit with ⟨C, T0, hC⟩
  set C0 : ℝ := max C 0
  let T1 : ℝ := max T0 4
  let Cfinal : ℝ := (1 / (2 * π)) + 2 * C0
  refine ⟨Cfinal, T1, ?_⟩
  intro T h hT hh
  set g : ℝ → ℝ := fun x =>
    (x / (2 * π)) * Real.log (x / (2 * π)) - x / (2 * π)
  have hT0 : T0 ≤ T := le_trans (le_max_left _ _) hT
  have hT4 : (4 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := by linarith [hT4]
  have hThpos : 0 < T + h := by linarith [hT4, hh]
  have hTle : T ≤ T + h := by linarith [hh]
  have hlogT_nonneg : 0 ≤ Real.log T := by
    exact Real.log_nonneg (by linarith [hT4])
  have hlogTh_nonneg : 0 ≤ Real.log (T + h) := by
    exact Real.log_nonneg (by linarith [hT4, hh])
  have hlog_le : Real.log T ≤ Real.log (T + h) := by
    exact Real.log_le_log hTpos hTle
  have hT0' : T0 ≤ T + h := le_trans hT0 hTle
  have hErrTh' : |(N (T + h) : ℝ) - g (T + h)| ≤ C * Real.log (T + h) := by
    simpa [g, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hC (T + h) hT0'
  have hErrTh : |(N (T + h) : ℝ) - g (T + h)| ≤ C0 * Real.log (T + h) := by
    have hC_le : C * Real.log (T + h) ≤ C0 * Real.log (T + h) := by
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlogTh_nonneg
    exact hErrTh'.trans hC_le
  have hErrT' : |(N T : ℝ) - g T| ≤ C * Real.log T := by
    simpa [g, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hC T hT0
  have hErrT : |(N T : ℝ) - g T| ≤ C0 * Real.log T := by
    have hC_le : C * Real.log T ≤ C0 * Real.log T := by
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlogT_nonneg
    exact hErrT'.trans hC_le
  have hUpper : (N (T + h) : ℝ) ≤ g (T + h) + C0 * Real.log (T + h) := by
    have hUpper := (abs_le.mp hErrTh).2
    linarith
  have hLower : g T - C0 * Real.log T ≤ (N T : ℝ) := by
    have hLower := (abs_le.mp hErrT).1
    linarith
  have hdiff :
      (N (T + h) : ℝ) - N T ≤ (g (T + h) - g T) + C0 * Real.log (T + h) + C0 * Real.log T := by
    linarith [hUpper, hLower]
  have hErrSum :
      C0 * Real.log (T + h) + C0 * Real.log T ≤ 2 * C0 * Real.log (T + h) := by
    have hC0_nonneg : 0 ≤ C0 := le_max_right _ _
    have hmul : C0 * Real.log T ≤ C0 * Real.log (T + h) := by
      exact mul_le_mul_of_nonneg_left hlog_le hC0_nonneg
    linarith
  have hdiff' :
      (N (T + h) : ℝ) - N T ≤ (g (T + h) - g T) + 2 * C0 * Real.log (T + h) := by
    linarith [hdiff, hErrSum]
  have hlog_diff :
      T * (Real.log (T + h) - Real.log T) ≤ h := by
    have hlog_eq : Real.log (T + h) - Real.log T = Real.log ((T + h) / T) := by
      symm
      exact Real.log_div (by linarith [hThpos]) (by linarith [hTpos])
    have hlog_le :
        Real.log ((T + h) / T) ≤ (T + h) / T - 1 := by
      exact Real.log_le_sub_one_of_pos (div_pos hThpos hTpos)
    have hlog_le' : Real.log (T + h) - Real.log T ≤ h / T := by
      calc
        Real.log (T + h) - Real.log T = Real.log ((T + h) / T) := hlog_eq
        _ ≤ (T + h) / T - 1 := hlog_le
        _ = h / T := by
          have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
          calc
            (T + h) / T - 1 = (T + h) / T - T / T := by simp [hTne]
            _ = ((T + h) - T) / T := by
                  simpa using (sub_div (T + h) T T).symm
            _ = h / T := by simp
    have hTnonneg : 0 ≤ T := le_of_lt hTpos
    have hmul := mul_le_mul_of_nonneg_left hlog_le' hTnonneg
    have hmul' : T * (h / T) = h := by
      have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
      calc
        T * (h / T) = (T * h) / T := by
          symm
          exact mul_div_assoc T h T
        _ = h := by
          simpa using (mul_div_cancel_left₀ h hTne)
    simpa [hmul'] using hmul
  have hdiff_log :
      (T + h) * Real.log (T + h) - T * Real.log T ≤ h * Real.log (T + h) + h := by
    calc
      (T + h) * Real.log (T + h) - T * Real.log T
          = (T * Real.log (T + h) + h * Real.log (T + h)) - T * Real.log T := by
              simp [add_mul]
      _ = (T * Real.log (T + h) - T * Real.log T) + h * Real.log (T + h) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = T * (Real.log (T + h) - Real.log T) + h * Real.log (T + h) := by
              simp [mul_sub, add_assoc, add_left_comm, add_comm]
      _ ≤ h + h * Real.log (T + h) := by
          have hsum := add_le_add_right hlog_diff (h * Real.log (T + h))
          simpa [add_comm, add_left_comm, add_assoc] using hsum
      _ = h * Real.log (T + h) + h := by
          simpa [add_comm] using rfl
  have hpi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
  have hlog2pi1_nonneg : 0 ≤ Real.log (2 * π) + 1 := by
    have h2pi_ge : (1 : ℝ) ≤ 2 * π := by
      have hpi3 : (3 : ℝ) < π := pi_gt_three
      linarith
    have hlog2pi_nonneg : 0 ≤ Real.log (2 * π) := Real.log_nonneg h2pi_ge
    linarith
  have g_rewrite (x : ℝ) (hx : 0 < x) :
      g x = (x / (2 * π)) * Real.log x - (x / (2 * π)) * (Real.log (2 * π) + 1) := by
    have hx_ne : (x : ℝ) ≠ 0 := by linarith
    have h2pi_ne : (2 * π : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
    have hlog_div : Real.log (x / (2 * π)) = Real.log x - Real.log (2 * π) :=
      Real.log_div hx_ne h2pi_ne
    calc
      g x = (x / (2 * π)) * (Real.log x - Real.log (2 * π)) - x / (2 * π) := by
        simp [g, hlog_div]
      _ = (x / (2 * π)) * Real.log x - (x / (2 * π)) * (Real.log (2 * π) + 1) := by
        simp [mul_sub, mul_add, mul_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hfactor1 :
      (T + h) / (2 * π) * Real.log (T + h) - T / (2 * π) * Real.log T
        = (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T) := by
    calc
      (T + h) / (2 * π) * Real.log (T + h) - T / (2 * π) * Real.log T
          = (1 / (2 * π)) * ((T + h) * Real.log (T + h))
              - (1 / (2 * π)) * (T * Real.log T) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T) := by
            symm
            simp [mul_sub]
  have hfactor2 :
      T / (2 * π) * (Real.log (2 * π) + 1)
        - (T + h) / (2 * π) * (Real.log (2 * π) + 1)
        = -(h / (2 * π)) * (Real.log (2 * π) + 1) := by
    calc
      T / (2 * π) * (Real.log (2 * π) + 1)
          - (T + h) / (2 * π) * (Real.log (2 * π) + 1)
          = (1 / (2 * π)) * (T * (Real.log (2 * π) + 1))
              - (1 / (2 * π)) * ((T + h) * (Real.log (2 * π) + 1)) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (1 / (2 * π)) * (T * (Real.log (2 * π) + 1)
            - (T + h) * (Real.log (2 * π) + 1)) := by
            symm
            simp [mul_sub]
      _ = (1 / (2 * π)) * (-(h * (Real.log (2 * π) + 1))) := by
            nlinarith
      _ = -(h / (2 * π)) * (Real.log (2 * π) + 1) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hcalc :
      g (T + h) - g T =
        (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T)
          - (h / (2 * π)) * (Real.log (2 * π) + 1) := by
    calc
      g (T + h) - g T
          = (T + h) / (2 * π) * Real.log (T + h)
              - (T + h) / (2 * π) * (Real.log (2 * π) + 1)
              - (T / (2 * π) * Real.log T - T / (2 * π) * (Real.log (2 * π) + 1)) := by
            simp [g_rewrite (T + h) hThpos, g_rewrite T hTpos]
      _ = ((T + h) / (2 * π) * Real.log (T + h) - T / (2 * π) * Real.log T)
            + (T / (2 * π) * (Real.log (2 * π) + 1)
              - (T + h) / (2 * π) * (Real.log (2 * π) + 1)) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T)
            + (-(h / (2 * π)) * (Real.log (2 * π) + 1)) := by
            simp [hfactor1, hfactor2]
      _ = (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T)
            - (h / (2 * π)) * (Real.log (2 * π) + 1) := by
            simp [sub_eq_add_neg, add_comm]
  have hneg :
      0 ≤ (h / (2 * π)) * (Real.log (2 * π) + 1) := by
    have hdiv_nonneg : 0 ≤ h / (2 * π) := by
      exact div_nonneg hh (le_of_lt hpi_pos)
    exact mul_nonneg hdiv_nonneg hlog2pi1_nonneg
  have hcalc' :
      g (T + h) - g T ≤
        (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T) := by
    calc
      g (T + h) - g T
          = (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T)
              - (h / (2 * π)) * (Real.log (2 * π) + 1) := hcalc
      _ ≤ (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T) := by
            exact sub_le_self _ hneg
  have hcoeff_nonneg : 0 ≤ (1 / (2 * π) : ℝ) := by
    exact one_div_nonneg.mpr (le_of_lt hpi_pos)
  have hdiff_g :
      g (T + h) - g T ≤ (1 / (2 * π)) * (h * Real.log (T + h) + h) := by
    have hbound :
        (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T)
          ≤ (1 / (2 * π)) * (h * Real.log (T + h) + h) := by
      exact mul_le_mul_of_nonneg_left hdiff_log hcoeff_nonneg
    exact le_trans hcalc' hbound
  have hdiff'' :
      (N (T + h) : ℝ) - N T ≤ (1 / (2 * π)) * (h * Real.log (T + h) + h)
        + 2 * C0 * Real.log (T + h) := by
    have hstep :
        (g (T + h) - g T) + 2 * C0 * Real.log (T + h)
          ≤ (1 / (2 * π)) * (h * Real.log (T + h) + h) + 2 * C0 * Real.log (T + h) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left hdiff_g (2 * C0 * Real.log (T + h)))
    exact le_trans hdiff' hstep
  have hlog1_nonneg : 0 ≤ Real.log (T + h) + 1 := by
    exact add_nonneg hlogTh_nonneg zero_le_one
  have hh_le : h ≤ h + 1 := by
    exact le_add_of_nonneg_right zero_le_one
  have hterm1 :
      (1 / (2 * π)) * (h * Real.log (T + h) + h)
        ≤ (1 / (2 * π)) * (h + 1) * (Real.log (T + h) + 1) := by
    have hmul : h * (Real.log (T + h) + 1) ≤ (h + 1) * (Real.log (T + h) + 1) := by
      exact mul_le_mul_of_nonneg_right hh_le hlog1_nonneg
    have hrewrite : h * Real.log (T + h) + h = h * (Real.log (T + h) + 1) := by
      calc
        h * Real.log (T + h) + h = h * Real.log (T + h) + h * 1 := by simp
        _ = h * (Real.log (T + h) + 1) := by
          symm
          simp [mul_add, mul_one]
    have hmul' :
        (1 / (2 * π)) * (h * (Real.log (T + h) + 1))
          ≤ (1 / (2 * π)) * ((h + 1) * (Real.log (T + h) + 1)) := by
      exact mul_le_mul_of_nonneg_left hmul hcoeff_nonneg
    calc
      (1 / (2 * π)) * (h * Real.log (T + h) + h)
          = (1 / (2 * π)) * (h * (Real.log (T + h) + 1)) := by
            simp [hrewrite]
      _ ≤ (1 / (2 * π)) * (h + 1) * (Real.log (T + h) + 1) := by
            simpa [mul_assoc] using hmul'
  have hlog_le' :
      Real.log (T + h) ≤ (h + 1) * (Real.log (T + h) + 1) := by
    have hnonneg : 0 ≤ h * Real.log (T + h) + h + 1 := by
      have hmul_nonneg : 0 ≤ h * Real.log (T + h) := by
        exact mul_nonneg hh hlogTh_nonneg
      have hsum : 0 ≤ h * Real.log (T + h) + h := add_nonneg hmul_nonneg hh
      exact add_nonneg hsum zero_le_one
    have hstep :
        Real.log (T + h) ≤ Real.log (T + h) + (h * Real.log (T + h) + h + 1) :=
      le_add_of_nonneg_right hnonneg
    have hrewrite :
        Real.log (T + h) + (h * Real.log (T + h) + h + 1)
          = (h + 1) * (Real.log (T + h) + 1) := by
      symm
      calc
        (h + 1) * (Real.log (T + h) + 1)
            = h * Real.log (T + h) + Real.log (T + h) + h + 1 := by
                simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm]
        _ = Real.log (T + h) + (h * Real.log (T + h) + h + 1) := by
                simp [add_assoc, add_left_comm, add_comm]
    simpa [hrewrite] using hstep
  have hterm2 :
      2 * C0 * Real.log (T + h)
        ≤ 2 * C0 * (h + 1) * (Real.log (T + h) + 1) := by
    have hC0_nonneg : 0 ≤ C0 := le_max_right _ _
    have h2C0_nonneg : 0 ≤ 2 * C0 := by
      have h2_nonneg : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg h2_nonneg hC0_nonneg
    have hmul := mul_le_mul_of_nonneg_left hlog_le' h2C0_nonneg
    simpa [mul_assoc] using hmul
  have hsum :
      (1 / (2 * π)) * (h * Real.log (T + h) + h) + 2 * C0 * Real.log (T + h)
        ≤ (1 / (2 * π)) * (h + 1) * (Real.log (T + h) + 1)
          + 2 * C0 * (h + 1) * (Real.log (T + h) + 1) := by
    exact add_le_add hterm1 hterm2
  have hsum' :
      (1 / (2 * π)) * (h + 1) * (Real.log (T + h) + 1)
        + 2 * C0 * (h + 1) * (Real.log (T + h) + 1)
        = Cfinal * (h + 1) * (Real.log (T + h) + 1) := by
    dsimp [Cfinal]
    ring
  have hfinal :
      (1 / (2 * π)) * (h * Real.log (T + h) + h) + 2 * C0 * Real.log (T + h)
        ≤ Cfinal * (h + 1) * (Real.log (T + h) + 1) := by
    calc
      (1 / (2 * π)) * (h * Real.log (T + h) + h) + 2 * C0 * Real.log (T + h)
          ≤ (1 / (2 * π)) * (h + 1) * (Real.log (T + h) + 1)
            + 2 * C0 * (h + 1) * (Real.log (T + h) + 1) := hsum
      _ = Cfinal * (h + 1) * (Real.log (T + h) + 1) := hsum'
  exact le_trans hdiff'' hfinal

/-- A unit-interval count bound; via pigeonhole this yields a lower bound on some gap. -/
class ZeroGapsLowerBoundHyp : Prop where
  gaps_lower_bound :
    ∃ C T0 : ℝ, ∀ {T : ℝ}, T0 ≤ T →
      (N (T + 1) : ℝ) - N T ≤ C * (Real.log (T + 1) + 1)

/-! ### Global instances -/

noncomputable instance zeroGapsLowerBoundHyp_of_local_density :
    ZeroGapsLowerBoundHyp := by
  classical
  rcases ZeroCountingLocalDensityHyp.local_density with ⟨C, T0, hC⟩
  let C' : ℝ := 2 * C
  refine ⟨C', T0, ?_⟩
  intro T hT
  have h := hC (T := T) (h := 1) hT (by linarith)
  have hrewrite :
      C * (1 + 1) * (Real.log (T + 1) + 1) = C' * (Real.log (T + 1) + 1) := by
    dsimp [C']
    nlinarith
  have h' := h
  rw [hrewrite] at h'
  exact h'

/-! ## Local Density -/

section LocalDensity

/-- The number of zeros in an interval [T, T+h] is O((h + 1) (log (T + h) + 1)) -/
theorem zeroCountingFunction_local_density :
    ∃ C T0 : ℝ, ∀ {T h : ℝ}, T0 ≤ T → 0 ≤ h →
      (N (T + h) : ℝ) - N T ≤ C * (h + 1) * (Real.log (T + h) + 1) := by
  simpa using ZeroCountingLocalDensityHyp.local_density

/-- Unit interval zero count bound (implies a lower bound on some gap). -/
theorem zeroGaps_lower_bound :
    ∃ C T0 : ℝ, ∀ {T : ℝ}, T0 ≤ T →
      (N (T + 1) : ℝ) - N T ≤ C * (Real.log (T + 1) + 1) := by
  simpa using ZeroGapsLowerBoundHyp.gaps_lower_bound

end LocalDensity

class ZeroConjZeroHyp : Prop where
  conj_zero : ∀ {ρ : ℂ}, ρ ∈ zetaNontrivialZeros → starRingEnd ℂ ρ ∈ zetaNontrivialZeros

class ZeroOneSubZeroHyp : Prop where
  one_sub_zero : ∀ {ρ : ℂ}, ρ ∈ zetaNontrivialZeros → 1 - ρ ∈ zetaNontrivialZeros

section Conjugation

open scoped ComplexConjugate

lemma riemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have hs' : 1 < (conj s).re := by simpa [Complex.conj_re] using hs
  calc
    riemannZeta (conj s) = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ conj s := by
      simpa using (zeta_eq_tsum_one_div_nat_add_one_cpow (s := conj s) hs')
    _ = ∑' n : ℕ, conj (1 / (n + 1 : ℂ) ^ s) := by
      refine tsum_congr ?_
      intro n
      have harg0 : arg (n + 1 : ℂ) = 0 := by
        simpa using (Complex.natCast_arg (n := n + 1))
      have hpi : (0 : ℝ) ≠ π := by simpa [ne_comm] using Real.pi_ne_zero
      have harg : arg (n + 1 : ℂ) ≠ π := by simpa [harg0] using hpi
      have hcpow : conj ((n + 1 : ℂ) ^ s) = (n + 1 : ℂ) ^ conj s := by
        have h := Complex.cpow_conj (x := (n + 1 : ℂ)) (n := s) harg
        simpa [Complex.conj_natCast] using h.symm
      calc
        1 / (n + 1 : ℂ) ^ conj s = 1 / conj ((n + 1 : ℂ) ^ s) := by
          simpa [hcpow]
        _ = conj (1 / (n + 1 : ℂ) ^ s) := by
          symm
          simpa using (RCLike.conj_div (K := ℂ) (x := 1) (y := (n + 1 : ℂ) ^ s))
    _ = conj (∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s) := by
      symm
      simpa using (conj_tsum (f := fun n : ℕ => 1 / (n + 1 : ℂ) ^ s))
    _ = conj (riemannZeta s) := by
      have h := congrArg conj (zeta_eq_tsum_one_div_nat_add_one_cpow (s := s) hs)
      simpa using h.symm

theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  let f : ℂ → ℂ := riemannZeta
  let g : ℂ → ℂ := fun z => conj (riemannZeta (conj z))
  let U : Set ℂ := ({(1 : ℂ)}ᶜ)
  have hUo : IsOpen U := by
    simpa [U] using (isOpen_compl_singleton : IsOpen ({(1 : ℂ)}ᶜ))
  have hf : AnalyticOnNhd ℂ f U := by
    refine DifferentiableOn.analyticOnNhd
      (fun z hz => DifferentiableAt.differentiableWithinAt ?_) hUo
    exact differentiableAt_riemannZeta (by simpa [U] using hz)
  have hg : AnalyticOnNhd ℂ g U := by
    refine DifferentiableOn.analyticOnNhd
      (fun z hz => DifferentiableAt.differentiableWithinAt ?_) hUo
    have hz' : conj z ≠ (1 : ℂ) := by
      intro h
      have hz1 : z ≠ (1 : ℂ) := by simpa [U] using hz
      have h' : z = (1 : ℂ) := by simpa using (congrArg conj h)
      exact hz1 h'
    have hdiff : DifferentiableAt ℂ riemannZeta (conj z) :=
      differentiableAt_riemannZeta hz'
    have hconj :
        DifferentiableAt ℂ (conj ∘ riemannZeta ∘ conj) (conj (conj z)) :=
      (DifferentiableAt.conj_conj (f := riemannZeta) (x := conj z) hdiff)
    simpa [g, Function.comp] using hconj
  have hU : IsPreconnected U := by
    have hconn : IsConnected ({(1 : ℂ)}ᶜ) :=
      isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)
    simpa [U] using hconn.isPreconnected
  have h2U : (2 : ℂ) ∈ U := by simp [U]
  have hV : {z : ℂ | 1 < re z} ∈ 𝓝 (2 : ℂ) :=
    (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hfg : f =ᶠ[𝓝 (2 : ℂ)] g := by
    refine eventually_of_mem hV ?_
    intro z hz
    have h1 : riemannZeta (conj z) = conj (riemannZeta z) :=
      riemannZeta_conj_of_one_lt_re (s := z) hz
    have h1' : conj (riemannZeta (conj z)) = riemannZeta z := by
      simpa using (congrArg conj h1)
    simpa [f, g] using h1'.symm
  have hEq : EqOn f g U := hf.eqOn_of_preconnected_of_eventuallyEq hg hU h2U hfg
  have hEq' : f s = g s := hEq (by simpa [U] using hs)
  have hEq'' : conj (f s) = conj (g s) := congrArg conj hEq'
  simpa [f, g] using hEq''.symm

instance zeroConjZeroHyp_of_riemannZeta : ZeroConjZeroHyp := by
  refine ⟨?_⟩
  intro ρ hρ
  rcases hρ with ⟨hzero, hre_pos, hre_lt⟩
  have hne : ρ ≠ (1 : ℂ) := by
    intro hEq
    have hEqRe : ρ.re = (1 : ℝ) := by
      have := congrArg Complex.re hEq
      simpa using this
    linarith
  have hconj : riemannZeta (conj ρ) = conj (riemannZeta ρ) :=
    riemannZeta_conj (s := ρ) hne
  have hzero' : riemannZeta (conj ρ) = 0 := by
    simpa [hzero] using hconj
  have hρ' : conj ρ ∈ zetaNontrivialZeros := by
    refine ⟨hzero', ?_, ?_⟩
    · simpa [Complex.conj_re] using hre_pos
    · simpa [Complex.conj_re] using hre_lt
  simpa using hρ'

end Conjugation

instance zeroOneSubZeroHyp_of_riemannZeta : ZeroOneSubZeroHyp := by
  refine ⟨?_⟩
  intro ρ hρ
  rcases hρ with ⟨hzero, hre_pos, hre_lt⟩
  have hne_neg : ∀ n : ℕ, ρ ≠ -n := by
    intro n hEq
    have hEqRe : ρ.re = -(n : ℝ) := by
      have := congrArg Complex.re hEq
      simpa using this
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    linarith
  have hne_one : ρ ≠ 1 := by
    intro hEq
    have hEqRe : ρ.re = (1 : ℝ) := by
      have := congrArg Complex.re hEq
      simpa using this
    linarith
  have hFE := riemannZeta_one_sub (s := ρ) hne_neg hne_one
  have hzero' : riemannZeta (1 - ρ) = 0 := by
    simpa [hzero] using hFE
  refine ⟨hzero', ?_, ?_⟩
  ·
    have hpos : (0 : ℝ) < (1 : ℝ) - ρ.re := sub_pos.mpr hre_lt
    simpa [Complex.sub_re, Complex.one_re] using hpos
  ·
    have hlt : (1 : ℝ) - ρ.re < 1 := sub_lt_self 1 hre_pos
    simpa [Complex.sub_re, Complex.one_re] using hlt

/-! ## Symmetry -/

section Symmetry

/-- Zeros come in conjugate pairs: if ρ is a zero, so is ρ̄ -/
theorem zero_conj_zero {ρ : ℂ} (hρ : ρ ∈ zetaNontrivialZeros) :
    starRingEnd ℂ ρ ∈ zetaNontrivialZeros := by
  simpa using (ZeroConjZeroHyp.conj_zero (ρ := ρ) hρ)

/-- The functional equation implies ρ is a zero iff 1 - ρ is a zero -/
theorem zero_one_sub_zero {ρ : ℂ} (hρ : ρ ∈ zetaNontrivialZeros) :
    1 - ρ ∈ zetaNontrivialZeros := by
  simpa using (ZeroOneSubZeroHyp.one_sub_zero (ρ := ρ) hρ)

/-- Combining: ρ, ρ̄, 1-ρ, 1-ρ̄ are all zeros (when distinct) -/
theorem zero_symmetry {ρ : ℂ} (hρ : ρ ∈ zetaNontrivialZeros) :
    starRingEnd ℂ ρ ∈ zetaNontrivialZeros ∧ 1 - ρ ∈ zetaNontrivialZeros ∧
    1 - starRingEnd ℂ ρ ∈ zetaNontrivialZeros := by
  refine ⟨zero_conj_zero hρ, zero_one_sub_zero hρ, ?_⟩
  -- conj(1 - ρ) = 1 - conj(ρ), so this follows from applying conj to (1-ρ)
  have h := zero_conj_zero (zero_one_sub_zero hρ)
  simp only [map_sub, map_one] at h
  exact h

end Symmetry

/-! ## Riemann Hypothesis Statement -/

/-- The Riemann Hypothesis: all nontrivial zeros have real part 1/2 -/
def RiemannHypothesis' : Prop :=
  ∀ ρ ∈ zetaNontrivialZeros, ρ.re = 1/2

/-- RH implies all zeros are on the critical line -/
theorem rh_implies_critical_line (hRH : RiemannHypothesis') (ρ : ℂ)
    (hρ : ρ ∈ zetaNontrivialZeros) : ρ.re = 1/2 :=
  hRH ρ hρ

/-- Under RH, zero symmetry simplifies: ρ and ρ̄ are the only pair -/
theorem rh_zero_pair (hRH : RiemannHypothesis') {ρ : ℂ}
    (hρ : ρ ∈ zetaNontrivialZeros) : 1 - ρ = starRingEnd ℂ ρ := by
  have hre : ρ.re = 1/2 := hRH ρ hρ
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, hre]
    linarith
  · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

end ZetaZeros
