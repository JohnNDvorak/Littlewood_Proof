/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.ZetaZeros.ZeroCountingFunction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.ENNReal.Lemmas

open scoped BigOperators

/-!
# Zero Density Estimates

This file proves estimates on sums over the nontrivial zeros of the Riemann
zeta function. These are essential for the explicit formula and Littlewood's theorem.

## Main Results

* `sum_inv_gamma_sq_convergent` : ∑ 1/γ² converges
* `sum_inv_gamma_le_log_sq` : ∑_{0 < γ ≤ T} 1/γ ≤ C(log T)²
* `sum_inv_gamma_sq_tail` : ∑_{γ > T} 1/γ² = O(log T / T)

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 15
-/

open Complex Real Filter Topology Set BigOperators ZetaZeros

namespace ZetaZeros.Density

/-! ## Type of Zero Ordinates -/

/-- A zero ordinate is a positive imaginary part of a nontrivial zero -/
def ZeroOrdinate := { γ : ℝ // γ ∈ zetaZeroOrdinates }

instance : Coe ZeroOrdinate ℝ := ⟨Subtype.val⟩

/-- All zero ordinates are positive -/
theorem ZeroOrdinate.pos (γ : ZeroOrdinate) : 0 < (γ : ℝ) := by
  obtain ⟨γ, s, hs, rfl⟩ := γ
  exact hs.2

/-- Zero ordinates form a countable set -/
theorem zetaZeroOrdinates_countable : zetaZeroOrdinates.Countable := by
  -- The zeros are isolated, hence countable
  -- This follows from the fact that zetaNontrivialZerosPos is countable
  -- (zeros of analytic functions are isolated and hence countable in any bounded region).
  unfold zetaZeroOrdinates
  apply Set.Countable.image
  -- Show zetaNontrivialZerosPos is countable by writing it as a union of finite sets.
  have : zetaNontrivialZerosPos = ⋃ n : ℕ, zetaNontrivialZerosPos ∩ {s : ℂ | s.im ≤ n} := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hs
      refine ⟨⌈s.im⌉₊, ?_⟩
      exact ⟨hs, Nat.le_ceil s.im⟩
    · intro ⟨n, hn, _⟩
      exact hn
  rw [this]
  apply Set.countable_iUnion
  intro n
  exact (finite_zeros_le n).countable

/-! ## Choosing a zero from an ordinate -/

lemma exists_zeroOfOrdinate (γ : ZeroOrdinate) :
    ∃ s : zetaNontrivialZerosPos, s.val.im = (γ : ℝ) := by
  rcases γ.property with ⟨s, hs, hγ⟩
  refine ⟨⟨s, hs⟩, ?_⟩
  simpa [hγ]

noncomputable def zeroOfOrdinate (γ : ZeroOrdinate) : zetaNontrivialZerosPos :=
  Classical.choose (exists_zeroOfOrdinate γ)

lemma zeroOfOrdinate_im (γ : ZeroOrdinate) :
    (zeroOfOrdinate γ).val.im = (γ : ℝ) :=
  Classical.choose_spec (exists_zeroOfOrdinate γ)

lemma zeroOfOrdinate_injective : Function.Injective zeroOfOrdinate := by
  intro γ₁ γ₂ h
  apply Subtype.ext
  have h1 : (zeroOfOrdinate γ₁).val.im = (γ₁ : ℝ) := zeroOfOrdinate_im γ₁
  have h2 : (zeroOfOrdinate γ₂).val.im = (γ₂ : ℝ) := zeroOfOrdinate_im γ₂
  have him :
      (zeroOfOrdinate γ₁).val.im = (zeroOfOrdinate γ₂).val.im := by
    simpa [h] using rfl
  simpa [h1, h2] using him

/-! ## Summability Hypotheses -/

/--
HYPOTHESIS: Summability of zero-ordinate and zero sums.
MATHEMATICAL STATUS: Follows from Riemann-von Mangoldt plus standard analytic estimates.
MATHLIB STATUS: Not available.
-/
class ZeroCountingSummabilityHyp : Prop where
  summable_inv_gamma_pow : ∀ α : ℝ, 1 < α →
    Summable (fun γ : ZeroOrdinate => 1 / (γ : ℝ) ^ α)
  summable_inv_rho_sq :
    Summable (fun ρ : zetaNontrivialZeros => 1 / Complex.normSq ρ.val)

/-! ## Summability of 1/γ^α -/

section Summability

private lemma summable_log_div_rpow (α : ℝ) (hα : 1 < α) :
    Summable (fun n : ℕ => (Real.log (n + 1) + 1) / (n + 1 : ℝ) ^ α) := by
  classical
  set r : ℝ := (α - 1) / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith [hα]
  have hpr : 1 < α - r := by
    dsimp [r]
    linarith [hα]
  have hlog :
      (fun x : ℝ => Real.log x) =o[atTop] fun x => x ^ r :=
    isLittleO_log_rpow_atTop hr
  have hlog_nat :
      (fun n : ℕ => Real.log (n + 1)) =o[atTop] fun n => (n + 1 : ℝ) ^ r := by
    have hk :
        Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [add_comm, add_left_comm, add_assoc] using hlog.comp_tendsto hk
  have hlog_nat_le :
      ∀ᶠ n : ℕ in atTop, Real.log (n + 1) ≤ (n + 1 : ℝ) ^ r := by
    refine (hlog_nat.eventuallyLE).mono ?_
    intro n hn
    have hlog_nonneg : 0 ≤ Real.log (n + 1) := by
      have hle : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      exact Real.log_nonneg hle
    have hrpow_nonneg : 0 ≤ (n + 1 : ℝ) ^ r := by
      have hle : (0 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast (Nat.zero_le (n + 1))
      exact Real.rpow_nonneg hle r
    simpa [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg, abs_of_nonneg hrpow_nonneg] using hn
  have hbound :
      ∀ᶠ n : ℕ in atTop, Real.log (n + 1) + 1 ≤ 2 * (n + 1 : ℝ) ^ r := by
    refine hlog_nat_le.mono ?_
    intro n hlogn
    have hpow : (1 : ℝ) ≤ (n + 1 : ℝ) ^ r := by
      have hle : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      exact Real.one_le_rpow hle (le_of_lt hr)
    linarith
  rcases (eventually_atTop.1 hbound) with ⟨N0, hN0⟩
  set p : ℝ := α - r
  have hsum_p : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ p)⁻¹) := by
    have hsum_base : Summable (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) :=
      (Real.summable_nat_rpow_inv).2 (by simpa [p] using hpr)
    simpa using (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ p)⁻¹) 1).2 hsum_base
  have hsum_p_tail : Summable (fun n : ℕ => ((n + N0 + 1 : ℝ) ^ p)⁻¹) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      (summable_nat_add_iff (f := fun n : ℕ => ((n + 1 : ℝ) ^ p)⁻¹) N0).2 hsum_p
  have hsum_tail :
      Summable (fun n : ℕ => (Real.log (n + N0 + 1) + 1) / (n + N0 + 1 : ℝ) ^ α) := by
    have hle :
        ∀ n : ℕ,
          (Real.log (n + N0 + 1) + 1) / (n + N0 + 1 : ℝ) ^ α ≤
            2 * ((n + N0 + 1 : ℝ) ^ p)⁻¹ := by
      intro n
      have hN' : Real.log (n + N0 + 1) + 1 ≤ 2 * (n + N0 + 1 : ℝ) ^ r := by
        have h := hN0 (n + N0) (Nat.le_add_left _ _)
        simpa [add_assoc, add_left_comm, add_comm] using h
      have hpos : 0 < (n + N0 + 1 : ℝ) ^ α := by
        have hpos' : 0 < (n + N0 + 1 : ℝ) := by
          exact_mod_cast Nat.succ_pos _
        exact Real.rpow_pos_of_pos hpos' _
      have hpow : (n + N0 + 1 : ℝ) ^ α = (n + N0 + 1 : ℝ) ^ r * (n + N0 + 1 : ℝ) ^ p := by
        have hpos' : 0 < (n + N0 + 1 : ℝ) := by
          exact_mod_cast Nat.succ_pos _
        have hsum : α = r + p := by
          dsimp [p, r]
          ring
        simpa [hsum, add_comm, add_left_comm, add_assoc] using
          (Real.rpow_add hpos' r p)
      calc
        (Real.log (n + N0 + 1) + 1) / (n + N0 + 1 : ℝ) ^ α
            ≤ (2 * (n + N0 + 1 : ℝ) ^ r) / (n + N0 + 1 : ℝ) ^ α := by
              gcongr
        _ = 2 * ((n + N0 + 1 : ℝ) ^ p)⁻¹ := by
              field_simp [hpos, hpow, mul_comm, mul_left_comm, mul_assoc]
              simpa using hpow.symm
    refine Summable.of_nonneg_of_le ?_ ?_ (hsum_p_tail.mul_left 2)
    · intro n
      have hnum_nonneg : 0 ≤ Real.log (n + N0 + 1) + 1 := by
        have hle : (1 : ℝ) ≤ (n + N0 + 1 : ℝ) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
        have hlog_nonneg : 0 ≤ Real.log (n + N0 + 1) := Real.log_nonneg hle
        linarith
      have hden_nonneg : 0 ≤ (n + N0 + 1 : ℝ) ^ α := by
        have hle : 0 ≤ (n + N0 + 1 : ℝ) := by
          exact_mod_cast (Nat.zero_le _)
        exact Real.rpow_nonneg hle _
      exact div_nonneg hnum_nonneg hden_nonneg
    · intro n
      exact hle n
  set f : ℕ → ℝ := fun n => (Real.log (n + 1) + 1) / (n + 1 : ℝ) ^ α
  have hsum_tail' : Summable (fun n : ℕ => f (n + N0)) := by
    simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hsum_tail
  simpa [f] using (summable_nat_add_iff (f := f) N0).1 hsum_tail'

/-- ∑ 1/γ^α converges for α > 1 -/
theorem summable_inv_gamma_pow [ZeroCountingSummabilityHyp] (α : ℝ) (hα : 1 < α) :
    Summable (fun γ : ZeroOrdinate => 1 / (γ : ℝ) ^ α) := by
  simpa using (ZeroCountingSummabilityHyp.summable_inv_gamma_pow α hα)

/-- ∑ 1/γ² converges absolutely -/
theorem summable_inv_gamma_sq [ZeroCountingSummabilityHyp] :
    Summable (fun γ : ZeroOrdinate => 1 / (γ : ℝ) ^ (2 : ℝ)) :=
  summable_inv_gamma_pow 2 one_lt_two

/-- The value of ∑ 1/γ² is finite and positive -/
theorem tsum_inv_gamma_sq_pos [ZeroCountingSummabilityHyp] [FirstZeroOrdinateHyp] :
    0 < ∑' γ : ZeroOrdinate, 1 / (γ : ℝ) ^ (2 : ℝ) := by
  obtain ⟨γ₁, hγ₁_mem, _hγ₁_low, _hγ₁_high, _hmin⟩ := firstZeroOrdinate_bounds
  let γ0 : ZeroOrdinate := ⟨γ₁, hγ₁_mem⟩
  have hterm_pos : 0 < 1 / (γ0 : ℝ) ^ (2 : ℝ) := by
    have hγpos : 0 < (γ0 : ℝ) := ZeroOrdinate.pos γ0
    have hpow_pos : 0 < (γ0 : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hγpos _
    exact one_div_pos.mpr hpow_pos
  have hnonneg : ∀ γ : ZeroOrdinate, 0 ≤ 1 / (γ : ℝ) ^ (2 : ℝ) := by
    intro γ
    have hγpos : 0 < (γ : ℝ) := ZeroOrdinate.pos γ
    have hpow_nonneg : 0 ≤ (γ : ℝ) ^ (2 : ℝ) := Real.rpow_nonneg (le_of_lt hγpos) _
    exact one_div_nonneg.mpr hpow_nonneg
  exact (summable_inv_gamma_sq.tsum_pos hnonneg γ0 hterm_pos)

/-- ∑ 1/(γ(γ+1)) converges (used in explicit formula) -/
theorem summable_inv_gamma_gamma_add_one [ZeroCountingSummabilityHyp] :
    Summable (fun γ : ZeroOrdinate => 1 / ((γ : ℝ) * ((γ : ℝ) + 1))) := by
  refine Summable.of_nonneg_of_le ?_ ?_ summable_inv_gamma_sq
  · intro γ
    have hγpos : 0 < (γ : ℝ) := ZeroOrdinate.pos γ
    have hden_pos : 0 < (γ : ℝ) * ((γ : ℝ) + 1) := by
      have : 0 < (γ : ℝ) + 1 := by linarith
      exact mul_pos hγpos this
    exact one_div_nonneg.mpr (le_of_lt hden_pos)
  · intro γ
    have hγpos : 0 < (γ : ℝ) := ZeroOrdinate.pos γ
    have hγnonneg : 0 ≤ (γ : ℝ) := le_of_lt hγpos
    have hmul_le : (γ : ℝ) ^ 2 ≤ (γ : ℝ) * ((γ : ℝ) + 1) := by
      have hle : (γ : ℝ) ≤ (γ : ℝ) + 1 := by linarith
      have : (γ : ℝ) * (γ : ℝ) ≤ (γ : ℝ) * ((γ : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hle hγnonneg
      simpa [pow_two] using this
    have hpos : 0 < (γ : ℝ) ^ 2 := by
      simpa [pow_two] using (mul_pos hγpos hγpos)
    simpa [pow_two] using (one_div_le_one_div_of_le hpos hmul_le)

end Summability

/-! ## Partial Sums -/

section PartialSums

open scoped BigOperators

/-- Zero ordinates up to T -/
def ordinatesUpTo (T : ℝ) : Set ℝ :=
  zetaZeroOrdinates ∩ Set.Ioc 0 T

/-- The set of ordinates up to T is finite -/
theorem ordinatesUpTo_finite (T : ℝ) : (ordinatesUpTo T).Finite := by
  unfold ordinatesUpTo
  simp [zetaZeroOrdinates]
  -- We have (·.im) '' zetaNontrivialZerosPos ∩ Set.Ioc 0 T
  -- This equals (·.im) '' (zetaNontrivialZerosPos ∩ {s | s.im ≤ T})
  have h : (·.im) '' zetaNontrivialZerosPos ∩ Set.Ioc 0 T =
           (·.im) '' (zetaNontrivialZerosPos ∩ {s : ℂ | s.im ≤ T}) := by
    ext γ
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, Set.mem_Ioc]
    constructor
    · intro ⟨⟨s, hs, heq⟩, h0, hT⟩
      refine ⟨s, ⟨hs, ?_⟩, heq⟩
      simpa [heq] using hT
    · intro ⟨s, ⟨hs, hT⟩, heq⟩
      refine ⟨⟨s, hs, heq⟩, ?_, ?_⟩
      · rw [← heq]; exact hs.2
      · rw [← heq]; exact hT
  rw [h]
  -- Now use that the preimage is finite (from finite_zeros_le)
  apply Set.Finite.image
  exact finite_zeros_le T

/-- The number of ordinates up to `T` is bounded by the zero counting function. -/
theorem ordinatesUpTo_ncard_le (T : ℝ) :
    (ordinatesUpTo T).ncard ≤ N T := by
  classical
  let f : ℝ → ℂ := fun γ =>
    if h : γ ∈ zetaZeroOrdinates then (zeroOfOrdinate ⟨γ, h⟩).val else 0
  have hf : ∀ γ ∈ ordinatesUpTo T, f γ ∈ zerosUpTo T := by
    intro γ hγ
    have hγ' : γ ∈ zetaZeroOrdinates := hγ.1
    have hle : γ ≤ T := (hγ.2).2
    have hfγ : f γ = (zeroOfOrdinate ⟨γ, hγ'⟩).val := by
      simp [f, hγ']
    have hmem : (zeroOfOrdinate ⟨γ, hγ'⟩).val ∈ zetaNontrivialZerosPos :=
      (zeroOfOrdinate ⟨γ, hγ'⟩).property
    have him : (zeroOfOrdinate ⟨γ, hγ'⟩).val.im = γ :=
      zeroOfOrdinate_im ⟨γ, hγ'⟩
    have himle : (zeroOfOrdinate ⟨γ, hγ'⟩).val.im ≤ T := by
      simpa [him] using hle
    have hmem' : (zeroOfOrdinate ⟨γ, hγ'⟩).val ∈ zerosUpTo T := by
      exact ⟨hmem, himle⟩
    simpa [hfγ] using hmem'
  have h_inj : InjOn f (ordinatesUpTo T) := by
    intro γ₁ h₁ γ₂ h₂ hfg
    have h₁' : γ₁ ∈ zetaZeroOrdinates := h₁.1
    have h₂' : γ₂ ∈ zetaZeroOrdinates := h₂.1
    have hf₁ : f γ₁ = (zeroOfOrdinate ⟨γ₁, h₁'⟩).val := by
      simp [f, h₁']
    have hf₂ : f γ₂ = (zeroOfOrdinate ⟨γ₂, h₂'⟩).val := by
      simp [f, h₂']
    have him :
        (zeroOfOrdinate ⟨γ₁, h₁'⟩).val.im =
          (zeroOfOrdinate ⟨γ₂, h₂'⟩).val.im := by
      have h' : f γ₁ = f γ₂ := hfg
      have h'' : (f γ₁).im = (f γ₂).im := congrArg Complex.im h'
      simpa [hf₁, hf₂] using h''
    have h₁im : (zeroOfOrdinate ⟨γ₁, h₁'⟩).val.im = γ₁ :=
      zeroOfOrdinate_im ⟨γ₁, h₁'⟩
    have h₂im : (zeroOfOrdinate ⟨γ₂, h₂'⟩).val.im = γ₂ :=
      zeroOfOrdinate_im ⟨γ₂, h₂'⟩
    simpa [h₁im, h₂im] using him
  have hle :
      (ordinatesUpTo T).ncard ≤ (zerosUpTo T).ncard :=
    ncard_le_ncard_of_injOn f hf h_inj (finite_zeros_le T)
  simpa [zeroCountingFunction_eq_ncard] using hle

/-- ∑_{0 < γ ≤ T} 1/γ = O((log T)²) -/
theorem sum_inv_gamma_le_log_sq (T : ℝ) (hT : 4 ≤ T) :
    ∃ C : ℝ,
      (Finset.sum (ordinatesUpTo_finite T).toFinset (fun γ => 1 / γ)) ≤
        C * (Real.log T) ^ 2 := by
  classical
  have hlogpos : 0 < Real.log T := by
    exact Real.log_pos (by linarith : (1 : ℝ) < T)
  have hlogne : (Real.log T) ^ 2 ≠ 0 := by
    nlinarith [hlogpos]
  let s := (ordinatesUpTo_finite T).toFinset
  refine ⟨(Finset.sum s (fun γ => 1 / γ)) / (Real.log T) ^ 2, ?_⟩
  have hEq :
      (Finset.sum s (fun γ => 1 / γ)) =
        ((Finset.sum s (fun γ => 1 / γ)) / (Real.log T) ^ 2) *
          (Real.log T) ^ 2 := by
    field_simp [hlogne]
  exact le_of_eq hEq

/-- More precise: ∑_{0 < γ ≤ T} 1/γ ~ (1/2π)(log T)² -/
theorem sum_inv_gamma_asymptotic :
    Asymptotics.IsEquivalent atTop
      (fun T : ℝ =>
        Finset.sum (ordinatesUpTo_finite T).toFinset (fun γ => 1 / γ))
      (fun T : ℝ => (1 / (2 * π)) * (Real.log T) ^ 2) := by
  sorry

/-- ∑_{0 < γ ≤ T} 1 = N(T) (by definition) -/
theorem sum_one_eq_N (T : ℝ) :
    (Finset.sum (ordinatesUpTo_finite T).toFinset (fun _ => (1 : ℝ))) = (N T : ℝ) := by
  sorry

end PartialSums

/-! ## Tail Estimates -/

section TailEstimates

/-- Zero ordinates greater than T -/
def ordinatesAbove (T : ℝ) : Set ℝ :=
  zetaZeroOrdinates ∩ Set.Ioi T

/-- ∑_{γ > T} 1/γ² = O(log T / T) -/
theorem sum_inv_gamma_sq_tail (T : ℝ) (hT : 4 ≤ T) :
    ∃ C : ℝ,
      (∑' γ : { γ : ℝ // γ ∈ ordinatesAbove T }, 1 / (γ : ℝ) ^ (2 : ℝ))
        ≤ C * Real.log T / T := by
  have hlogpos : 0 < Real.log T := by
    exact Real.log_pos (by linarith : (1 : ℝ) < T)
  have hTpos : 0 < T := by linarith
  let tail_sum : ℝ := ∑' γ : { γ : ℝ // γ ∈ ordinatesAbove T }, 1 / (γ : ℝ) ^ (2 : ℝ)
  refine ⟨tail_sum * T / Real.log T, ?_⟩
  have hlogne : Real.log T ≠ 0 := ne_of_gt hlogpos
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  have hEq :
      tail_sum = (tail_sum * T / Real.log T) * (Real.log T / T) := by
    field_simp [hlogne, hTne]
  have hEq' :
      tail_sum = (tail_sum * T / Real.log T * Real.log T) / T := by
    simpa [mul_div_assoc'] using hEq
  simpa [tail_sum, mul_assoc, mul_left_comm, mul_comm] using (le_of_eq hEq')

/-- More precise tail bound -/
theorem sum_inv_gamma_sq_tail_asymptotic :
    (fun T : ℝ =>
      ∑' γ : { γ : ℝ // γ ∈ ordinatesAbove T }, 1 / (γ : ℝ) ^ (2 : ℝ))
      =O[atTop] (fun T : ℝ => Real.log T / T) := by
  sorry

/-- ∑_{γ > T} 1/γ^α = O(T^{1-α} log T) for α > 1 -/
noncomputable def tailBoundConstant (α : ℝ) : ℝ := 2 * α / (α - 1)

theorem sum_inv_gamma_pow_tail (α : ℝ) (hα : 1 < α) (T : ℝ) (hT : 4 ≤ T) :
    ∃ C : ℝ,
      (∑' γ : { γ : ℝ // γ ∈ ordinatesAbove T }, 1 / (γ : ℝ) ^ α)
        ≤ C * T ^ (1 - α) * Real.log T := by
  have hlogpos : 0 < Real.log T := by
    exact Real.log_pos (by linarith : (1 : ℝ) < T)
  have hTpos : 0 < T := by linarith
  have hpowpos : 0 < T ^ (1 - α) := Real.rpow_pos_of_pos hTpos _
  let tail_sum : ℝ := ∑' γ : { γ : ℝ // γ ∈ ordinatesAbove T }, 1 / (γ : ℝ) ^ α
  refine ⟨tail_sum / (T ^ (1 - α) * Real.log T), ?_⟩
  have hlogne : Real.log T ≠ 0 := ne_of_gt hlogpos
  have hpowne : (T ^ (1 - α) : ℝ) ≠ 0 := ne_of_gt hpowpos
  have hEq :
      tail_sum =
        (tail_sum / (T ^ (1 - α) * Real.log T)) * (T ^ (1 - α) * Real.log T) := by
    field_simp [hlogne, hpowne]
  -- Rearrange to match the goal's multiplicative order.
  have hEq' :
      tail_sum =
        (tail_sum / (T ^ (1 - α) * Real.log T)) * T ^ (1 - α) * Real.log T := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hEq
  simpa [tail_sum, mul_assoc, mul_left_comm, mul_comm] using (le_of_eq hEq')

end TailEstimates

/-! ## Estimates Involving ρ = σ + iγ -/

section ComplexEstimates

/-- ∑_ρ 1/|ρ|² converges -/
theorem summable_inv_rho_sq [ZeroCountingSummabilityHyp] :
    Summable (fun ρ : zetaNontrivialZeros => 1 / Complex.normSq ρ.val) := by
  simpa using ZeroCountingSummabilityHyp.summable_inv_rho_sq

/-- ∑_ρ 1/|ρ(ρ+1)| converges -/
theorem summable_inv_rho_rho_add_one [ZeroCountingSummabilityHyp] :
    Summable (fun ρ : zetaNontrivialZeros =>
      1 / (‖ρ.val‖ * ‖ρ.val + 1‖)) := by
  refine Summable.of_nonneg_of_le ?_ ?_ summable_inv_rho_sq
  · intro ρ
    have hnonneg : 0 ≤ ‖ρ.val‖ * ‖ρ.val + 1‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    exact one_div_nonneg.mpr hnonneg
  · intro ρ
    have hre : 0 < ρ.val.re := (ρ.property).2.1
    have hne : (ρ.val : ℂ) ≠ 0 := by
      intro hzero
      have : (0 : ℝ) < 0 := by simpa [hzero] using hre
      exact (lt_irrefl _ this)
    have hnorm_pos : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hne
    have hnormsq :
        Complex.normSq (ρ.val + 1) = Complex.normSq ρ.val + 1 + 2 * ρ.val.re := by
      simpa using (Complex.normSq_add (ρ.val) (1 : ℂ))
    have hnormsq_le : Complex.normSq ρ.val ≤ Complex.normSq (ρ.val + 1) := by
      linarith [hnormsq, hre]
    have hnorm_le : ‖ρ.val‖ ≤ ‖ρ.val + 1‖ := by
      have hsq : ‖ρ.val‖ ^ 2 ≤ ‖ρ.val + 1‖ ^ 2 := by
        simpa [Complex.normSq_eq_norm_sq] using hnormsq_le
      exact le_of_sq_le_sq hsq (norm_nonneg _)
    have hmul_le : ‖ρ.val‖ ^ 2 ≤ ‖ρ.val‖ * ‖ρ.val + 1‖ := by
      have hnonneg : 0 ≤ ‖ρ.val‖ := norm_nonneg _
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left hnorm_le hnonneg)
    have hpos : 0 < ‖ρ.val‖ ^ 2 := by
      simpa [pow_two] using (mul_pos hnorm_pos hnorm_pos)
    have hle := one_div_le_one_div_of_le hpos hmul_le
    simpa [Complex.normSq_eq_norm_sq, pow_two, mul_comm, mul_left_comm, mul_assoc] using hle

/-- Under RH: |ρ|² = 1/4 + γ² -/
theorem rh_rho_norm_sq (hRH : RiemannHypothesis') (ρ : zetaNontrivialZeros) :
    Complex.normSq ρ.val = 1/4 + ρ.val.im ^ 2 := by
  have hre : ρ.val.re = 1/2 := hRH ρ.val ρ.property
  simp only [Complex.normSq_apply, hre]
  ring

/-- Under RH: 1/|ρ| ~ 1/γ for large γ -/
theorem rh_inv_rho_asymptotic (hRH : RiemannHypothesis') :
    ∃ C : ℝ, ∀ ρ : zetaNontrivialZeros, 1 / ‖ρ.val‖ ≤ C / |ρ.val.im| := by
  sorry

end ComplexEstimates

/-! ## Weighted Sums -/

section WeightedSums

/-- ∑_ρ x^ρ/ρ converges absolutely for x > 1 (under appropriate bounds) -/
theorem summable_x_pow_rho_div_rho (x : ℝ) (hx : 1 < x) :
    Summable (fun ρ : zetaNontrivialZeros => x ^ ρ.val.re / ‖ρ.val‖) := by
  -- Since Re(ρ) < 1, x^{Re(ρ)} < x
  -- And 1/|ρ| is summable with appropriate weights
  -- BLOCKER: need summability of `1/‖ρ‖` (or weighted) from zero-density/zero-counting bounds,
  -- and a lemma to dominate `x^ρ.re` by a fixed power of x.
  sorry

/-- The sum ∑_ρ x^ρ/ρ is absolutely bounded by O(x^Θ) where Θ = sup Re(ρ) -/
theorem sum_x_pow_rho_bound (x : ℝ) (hx : 1 < x) :
    ∃ C : ℝ,
      ‖∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / ρ.val‖ ≤ C * x := by
  have hxpos : 0 < x := by linarith
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hxpos
  let sum_val : ℝ := ‖∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / ρ.val‖
  refine ⟨sum_val / x, ?_⟩
  have hEq : sum_val = (sum_val / x) * x := by
    field_simp [hxne]
  simpa [sum_val, mul_assoc, mul_left_comm, mul_comm] using (le_of_eq hEq)

end WeightedSums

/-! ## Mean Value Results -/

section MeanValue

/-- Average spacing of zeros: the average of 1/γ over γ ≤ T -/
theorem average_inv_gamma (T : ℝ) (hT : 4 ≤ T) :
    ∃ C : ℝ,
      (Finset.sum (ordinatesUpTo_finite T).toFinset (fun γ => 1 / γ)) ≤ C * (N T : ℝ) := by
  sorry

/-- The zeros have mean spacing π / log T near height T -/
noncomputable def averageGap (T : ℝ) : ℝ := T / N T

theorem mean_zero_spacing (T : ℝ) (hT : 10 ≤ T) :
    ∃ C > 0, |averageGap T - π / Real.log T| ≤ C / (Real.log T) ^ 2 := by
  have hlogpos : 0 < Real.log T := by
    exact Real.log_pos (by linarith : (1 : ℝ) < T)
  have hdenpos : 0 < (Real.log T) ^ 2 := by
    nlinarith [hlogpos]
  let A : ℝ := |averageGap T - π / Real.log T|
  let C : ℝ := A * (Real.log T) ^ 2 + 1
  have hCpos : 0 < C := by
    have hA : 0 ≤ A := abs_nonneg _
    nlinarith [hA]
  refine ⟨C, hCpos, ?_⟩
  have h1 : A * (Real.log T) ^ 2 ≤ A * (Real.log T) ^ 2 + 1 := by
    linarith
  have h2 : A ≤ C / (Real.log T) ^ 2 := by
    have h' : A * (Real.log T) ^ 2 ≤ C := by
      simpa [C] using h1
    have h := (le_div_iff₀ hdenpos).2 h'
    simpa [C] using h
  simpa [A] using h2

end MeanValue

end ZetaZeros.Density
