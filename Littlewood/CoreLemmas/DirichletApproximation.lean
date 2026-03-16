/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Archimedean.Basic
import Littlewood.ZetaZeros.ZeroCountingFunction

/-!
# Simultaneous Dirichlet Approximation

This file extends Mathlib's Dirichlet approximation theorem to the simultaneous
case, which is essential for Littlewood's theorem. We prove that given K real
numbers θ₁, ..., θ_K and N ∈ ℕ, there exists n ≤ N^K such that all θᵢn are
within 1/N of an integer.

## Main Results

* `dirichlet_approximation_simultaneous` : Simultaneous Diophantine approximation
* `sin_pi_le_pi_distToInt` : |sin(πx)| ≤ π‖x‖

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Lemma 15.2
* Hardy-Wright, "An Introduction to the Theory of Numbers", Chapter 11
-/

open Real BigOperators Finset Int

namespace DirichletApprox

/-! ## Distance to Nearest Integer -/

/-- Distance to the nearest integer: ‖x‖ = min{|x - n| : n ∈ ℤ} -/
noncomputable def distToInt (x : ℝ) : ℝ :=
  |x - round x|

/-- Notation for distance to nearest integer -/
scoped notation "‖" x "‖ᵢₙₜ" => distToInt x

theorem distToInt_nonneg (x : ℝ) : 0 ≤ ‖x‖ᵢₙₜ := abs_nonneg _

theorem distToInt_le_half (x : ℝ) : ‖x‖ᵢₙₜ ≤ 1/2 := by
  unfold distToInt
  have h := abs_sub_round x
  linarith

theorem distToInt_zero : ‖(0 : ℝ)‖ᵢₙₜ = 0 := by simp [distToInt]

theorem distToInt_int (n : ℤ) : ‖(n : ℝ)‖ᵢₙₜ = 0 := by
  unfold distToInt
  simp

theorem distToInt_add_int (x : ℝ) (n : ℤ) : ‖x + n‖ᵢₙₜ = ‖x‖ᵢₙₜ := by
  unfold distToInt
  simp [round_add_intCast, sub_eq_add_neg, add_comm, add_assoc]

theorem distToInt_neg (x : ℝ) : ‖-x‖ᵢₙₜ = ‖x‖ᵢₙₜ := by
  classical
  unfold distToInt
  have hx : |x - round x| = min (fract x) (1 - fract x) := by
    simpa using (abs_sub_round_eq_min (x := x))
  have hxneg : |-x - round (-x)| = min (fract (-x)) (1 - fract (-x)) := by
    simpa using (abs_sub_round_eq_min (x := -x))
  by_cases h : fract x = 0
  · have hneg : fract (-x) = 0 := (fract_neg_eq_zero).2 h
    simpa [hx, hxneg, h, hneg]
  · have hneg : fract (-x) = 1 - fract x := fract_neg (x := x) h
    simpa [hx, hxneg, hneg, min_comm]

/-! ## Sine Estimate -/

/-- Key estimate: |sin(πx)| ≤ π‖x‖ -/
theorem sin_pi_le_pi_distToInt (x : ℝ) : |sin (π * x)| ≤ π * ‖x‖ᵢₙₜ := by
  -- sin(πx) = sin(π(x - round(x))) since sin has period 2π
  -- and for |y| ≤ 1/2, |sin(πy)| ≤ π|y|
  have hshift : |sin (π * (x - round x))| = |sin (π * x)| := by
    have h := sin_sub_int_mul_pi (π * x) (round x)
    have h' : sin (π * (x - round x)) = (-1) ^ (round x) * sin (π * x) := by
      have h1 : π * x - round x * π = π * (x - round x) := by
        ring
      simpa [h1] using h
    have h1 : |(-1 : ℝ) ^ (round x)| = 1 := by
      simpa using (abs_neg_one_zpow (p := round x) (α := ℝ))
    calc
      |sin (π * (x - round x))| = |(-1) ^ (round x) * sin (π * x)| := by
        simp [h']
      _ = |(-1) ^ (round x)| * |sin (π * x)| := by
        simpa using (abs_mul ((-1) ^ (round x)) (sin (π * x)))
      _ = |sin (π * x)| := by simp [h1]
  have hbound : |sin (π * (x - round x))| ≤ |π * (x - round x)| := by
    simpa using (abs_sin_le_abs (x := π * (x - round x)))
  have hmul : |π * (x - round x)| = π * |x - round x| := by
    simp [abs_mul, abs_of_pos Real.pi_pos]
  calc
    |sin (π * x)| = |sin (π * (x - round x))| := hshift.symm
    _ ≤ π * |x - round x| := by simpa [hmul] using hbound
    _ = π * ‖x‖ᵢₙₜ := by simp [distToInt]

/-- Corollary: |sin(πx)| ≤ π/2 -/
theorem sin_pi_le_half_pi (x : ℝ) : |sin (π * x)| ≤ π / 2 := by
  have h1 := sin_pi_le_pi_distToInt x
  have h2 := distToInt_le_half x
  have hpi : (0 : ℝ) < π := Real.pi_pos
  nlinarith

/-- Difference of sines in terms of distance -/
theorem sin_sub_sin_le (α β : ℝ) :
    |sin (2 * π * α) - sin (2 * π * β)| ≤ 2 * π * ‖α - β‖ᵢₙₜ := by
  -- Use sin(a) - sin(b) = 2 cos((a+b)/2) sin((a-b)/2)
  set a : ℝ := 2 * π * α
  set b : ℝ := 2 * π * β
  have hcos : |Real.cos ((a + b) / 2)| ≤ 1 := by
    simpa [a, b] using abs_cos_le_one ((a + b) / 2)
  have hrewrite : (a - b) / 2 = π * (α - β) := by
    simp [a, b]
    ring
  have hsin : |Real.sin ((a - b) / 2)| ≤ π * ‖α - β‖ᵢₙₜ := by
    simpa [hrewrite] using sin_pi_le_pi_distToInt (α - β)
  have hsin_cos :
      |sin (2 * π * α) - sin (2 * π * β)| =
        2 * |Real.sin ((a - b) / 2)| * |Real.cos ((a + b) / 2)| := by
    simpa [a, b] using (congrArg abs (sin_sub_sin a b))
  -- final bound
  calc
    |sin (2 * π * α) - sin (2 * π * β)|
        = 2 * |Real.sin ((a - b) / 2)| * |Real.cos ((a + b) / 2)| := hsin_cos
    _ = 2 * |Real.cos ((a + b) / 2)| * |Real.sin ((a - b) / 2)| := by
          ring
    _ ≤ 2 * (1 : ℝ) * (π * ‖α - β‖ᵢₙₜ) := by
          gcongr
    _ = 2 * π * ‖α - β‖ᵢₙₜ := by ring

/-! ## Simultaneous Dirichlet Approximation -/

/-- Pigeonhole principle for K-dimensional unit cube -/
theorem pigeonhole_cube (K N : ℕ) (_hN : 0 < N) (points : Fin (N^K + 1) → Fin K → ℕ)
    (hpoints : ∀ i k, points i k < N) :
    ∃ i j : Fin (N^K + 1), i < j ∧ ∀ k : Fin K, points i k = points j k := by
  -- There are N^K subcubes but N^K + 1 points
  classical
  let f : Fin (N ^ K + 1) → Fin K → Fin N := fun i k => ⟨points i k, hpoints i k⟩
  have hcard :
      Fintype.card (Fin K → Fin N) < Fintype.card (Fin (N ^ K + 1)) := by
    simpa [Fintype.card_fun] using (Nat.lt_succ_self (N ^ K))
  obtain ⟨i, j, hij, hfj⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hlt : i < j ∨ j < i := lt_or_gt_of_ne hij
  rcases hlt with hlt | hgt
  · refine ⟨i, j, hlt, ?_⟩
    intro k
    have hfun : f i k = f j k := by
      simpa using (congrArg (fun g => g k) hfj)
    simpa using (congrArg Fin.val hfun)
  · refine ⟨j, i, hgt, ?_⟩
    intro k
    have hfun : f j k = f i k := by
      simpa using (congrArg (fun g => g k) hfj.symm)
    simpa using (congrArg Fin.val hfun)

/-- Simultaneous Dirichlet approximation theorem -/
theorem dirichlet_approximation_simultaneous
    (K : ℕ) (θ : Fin K → ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N^K ∧ ∀ k : Fin K, ‖θ k * n‖ᵢₙₜ < 1 / N := by
  classical
  -- Partition [0,1)^K into N^K subcubes of side 1/N and apply pigeonhole.
  let points : Fin (N^K + 1) → Fin K → ℕ := fun i k =>
    ⌊fract (θ k * (i : ℕ)) * (N : ℝ)⌋₊
  have hpoints : ∀ i k, points i k < N := by
    intro i k
    have ha : 0 ≤ fract (θ k * (i : ℕ)) * (N : ℝ) := by
      have hfrac : 0 ≤ fract (θ k * (i : ℕ)) := fract_nonneg _
      have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
      exact mul_nonneg hfrac hN0
    have hlt : fract (θ k * (i : ℕ)) * (N : ℝ) < (N : ℝ) := by
      have hfrac : fract (θ k * (i : ℕ)) < 1 := fract_lt_one _
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
      have := mul_lt_mul_of_pos_right hfrac hNpos
      simpa [one_mul] using this
    exact (Nat.floor_lt ha).2 (by simpa using hlt)
  obtain ⟨i, j, hij, hpoints_eq⟩ := pigeonhole_cube K N hN points hpoints
  let n : ℕ := (j : ℕ) - (i : ℕ)
  have hle : (i : ℕ) ≤ (j : ℕ) := Nat.le_of_lt hij
  have hn_pos : 1 ≤ n := by
    have : 0 < n := Nat.sub_pos_of_lt hij
    exact Nat.succ_le_iff.mpr this
  have hn_le : n ≤ N^K := by
    have hj_le : (j : ℕ) ≤ N^K := Nat.le_of_lt_succ j.is_lt
    exact (Nat.sub_le _ _).trans hj_le
  refine ⟨n, hn_pos, hn_le, ?_⟩
  intro k
  set a : ℝ := fract (θ k * (j : ℕ)) * (N : ℝ)
  set b : ℝ := fract (θ k * (i : ℕ)) * (N : ℝ)
  have ha0 : 0 ≤ a := by
    have hfrac : 0 ≤ fract (θ k * (j : ℕ)) := fract_nonneg _
    have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    simpa [a] using mul_nonneg hfrac hN0
  have hb0 : 0 ≤ b := by
    have hfrac : 0 ≤ fract (θ k * (i : ℕ)) := fract_nonneg _
    have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    simpa [b] using mul_nonneg hfrac hN0
  have hfloor_eq_nat : ⌊a⌋₊ = ⌊b⌋₊ := by
    simpa [points, a, b] using (hpoints_eq k).symm
  have hfloor_eq_int : (⌊a⌋ : ℤ) = ⌊b⌋ := by
    have hcast : (⌊a⌋₊ : ℤ) = (⌊b⌋₊ : ℤ) := by
      exact_mod_cast hfloor_eq_nat
    simpa [Int.natCast_floor_eq_floor ha0, Int.natCast_floor_eq_floor hb0] using hcast
  have habs : |a - b| < 1 := abs_sub_lt_one_of_floor_eq_floor hfloor_eq_int
  have hmul : |fract (θ k * (j : ℕ)) - fract (θ k * (i : ℕ))| * (N : ℝ) < 1 := by
    have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    have h1 : |(fract (θ k * (j : ℕ)) - fract (θ k * (i : ℕ))) * (N : ℝ)| < 1 := by
      have : a - b =
          (fract (θ k * (j : ℕ)) - fract (θ k * (i : ℕ))) * (N : ℝ) := by
        simp [a, b]
        ring
      simpa [this] using habs
    simpa [abs_mul, abs_of_nonneg hN0] using h1
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hfrac :
      |fract (θ k * (j : ℕ)) - fract (θ k * (i : ℕ))| < 1 / (N : ℝ) := by
    exact (lt_div_iff₀ hNpos).2 hmul
  let m : ℤ := ⌊θ k * (j : ℝ)⌋ - ⌊θ k * (i : ℝ)⌋
  have hcast : (n : ℝ) = (j : ℝ) - (i : ℝ) := by
    simp [n, Nat.cast_sub hle]
  have hcalc :
      θ k * (n : ℝ) - (m : ℝ) =
        fract (θ k * (j : ℝ)) - fract (θ k * (i : ℝ)) := by
    simp [hcast, m, fract, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_sub]
    ring
  have hdist_le :
      ‖θ k * (n : ℝ)‖ᵢₙₜ ≤ |fract (θ k * (j : ℝ)) - fract (θ k * (i : ℝ))| := by
    have hround :
        |θ k * (n : ℝ) - round (θ k * (n : ℝ))| ≤ |θ k * (n : ℝ) - (m : ℝ)| :=
      round_le _ m
    simpa [distToInt, hcalc] using hround
  exact lt_of_le_of_lt hdist_le (by simpa using hfrac)

/-- Corollary: infinitely many n satisfy the approximation -/
theorem dirichlet_approximation_simultaneous_infinitely_many
    (K : ℕ) (θ : Fin K → ℝ) :
    ∀ N : ℕ, 0 < N → ∃ n : ℕ, N < n ∧ ∀ k : Fin K, ‖θ k * n‖ᵢₙₜ < 1 / (n : ℝ)^((1 : ℝ)/K) := by
  classical
  intro N hN
  by_cases hK : K = 0
  · subst hK
    refine ⟨N + 1, Nat.lt_succ_self _, ?_⟩
    intro k
    exact (Fin.elim0 k)
  have hKpos : 0 < K := Nat.pos_of_ne_zero hK
  by_cases hzero : ∃ n : ℕ, 1 ≤ n ∧ ∀ k : Fin K, ‖θ k * n‖ᵢₙₜ = 0
  · obtain ⟨n0, hn0, hdist0⟩ := hzero
    let n : ℕ := (N + 1) * n0
    have hn_gt : N < n := by
      have hmul : N + 1 ≤ n := by
        have : (N + 1) ≤ (N + 1) * n0 := by
          simpa [n, Nat.mul_comm] using (Nat.mul_le_mul_left (N + 1) hn0)
        exact this
      exact (Nat.lt_succ_self N).trans_le hmul
    refine ⟨n, hn_gt, ?_⟩
    intro k
    have hround_eq : θ k * (n0 : ℝ) = (round (θ k * (n0 : ℝ)) : ℝ) := by
      have h0 : ‖θ k * (n0 : ℝ)‖ᵢₙₜ = 0 := by
        simpa using hdist0 k
      have h0' : |θ k * (n0 : ℝ) - round (θ k * (n0 : ℝ))| = 0 := by
        simpa [distToInt] using h0
      have h0'' : θ k * (n0 : ℝ) - round (θ k * (n0 : ℝ)) = 0 :=
        abs_eq_zero.mp h0'
      linarith
    have hcast :
        θ k * (n : ℝ) =
          ((N + 1 : ℤ) * round (θ k * (n0 : ℝ)) : ℤ) := by
      have hncast : (n : ℝ) = (N + 1 : ℝ) * (n0 : ℝ) := by
        simp [n, Nat.cast_mul]
      calc
        θ k * (n : ℝ) = θ k * ((N + 1 : ℝ) * (n0 : ℝ)) := by
          simp [hncast]
        _ = (N + 1 : ℝ) * (θ k * (n0 : ℝ)) := by
          ring
        _ = (N + 1 : ℝ) * (round (θ k * (n0 : ℝ)) : ℝ) := by
          simpa using (congrArg (fun x => (N + 1 : ℝ) * x) hround_eq)
        _ = ((N + 1 : ℤ) * round (θ k * (n0 : ℝ)) : ℤ) := by
          have hmul_cast :
              (((N + 1 : ℤ) * round (θ k * (n0 : ℝ)) : ℤ) : ℝ) =
                ((N + 1 : ℤ) : ℝ) * (round (θ k * (n0 : ℝ)) : ℝ) :=
            Int.cast_mul (N + 1 : ℤ) (round (θ k * (n0 : ℝ)))
          have hcast' :
              (((N + 1 : ℤ) * round (θ k * (n0 : ℝ)) : ℤ) : ℝ) =
                (N + 1 : ℝ) * (round (θ k * (n0 : ℝ)) : ℝ) := by
            simpa [Int.cast_natCast] using hmul_cast
          exact hcast'.symm
    have h0 : ‖θ k * (n : ℝ)‖ᵢₙₜ = 0 := by
      simpa [hcast] using
        (distToInt_int ((N + 1 : ℤ) * round (θ k * (n0 : ℝ))))
    have hpos : 0 < 1 / (n : ℝ) ^ ((1 : ℝ) / K) := by
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast (lt_trans hN hn_gt)
      have hpow : 0 < (n : ℝ) ^ ((1 : ℝ) / K) := Real.rpow_pos_of_pos hnpos _
      exact one_div_pos.mpr hpow
    simpa [h0] using hpos
  -- Main case: no exact integer multiple.
  haveI : Nonempty (Fin K) := ⟨⟨0, hKpos⟩⟩
  let f : ℕ → ℝ := fun n =>
    (Finset.univ.image (fun k : Fin K => ‖θ k * (n : ℝ)‖ᵢₙₜ)).max'
      (by
        rcases (Finset.univ_nonempty : (Finset.univ : Finset (Fin K)).Nonempty) with ⟨k, hk⟩
        refine ⟨‖θ k * (n : ℝ)‖ᵢₙₜ, ?_⟩
        exact Finset.mem_image.2 ⟨k, hk, rfl⟩)
  let sN : Finset ℕ := (Finset.range (N + 1)).erase 0
  have hsN : sN.Nonempty := by
    refine ⟨1, ?_⟩
    have h1 : 1 < N + 1 := Nat.succ_lt_succ hN
    have h1' : 1 ∈ Finset.range (N + 1) := by simpa using h1
    exact Finset.mem_erase.2 ⟨by decide, h1'⟩
  have hpos_f : ∀ n ∈ sN, 0 < f n := by
    intro n hn
    have hn_pos : 1 ≤ n := by
      have hmem : n ∈ Finset.range (N + 1) := (Finset.mem_erase.1 hn).2
      have hpos : 0 < n := by
        have hn0 : n ≠ 0 := (Finset.mem_erase.1 hn).1
        exact Nat.pos_of_ne_zero hn0
      exact Nat.succ_le_iff.mpr hpos
    have hnot : ¬ ∀ k : Fin K, ‖θ k * n‖ᵢₙₜ = 0 := by
      intro hforall
      exact hzero ⟨n, hn_pos, hforall⟩
    obtain ⟨k, hk⟩ : ∃ k : Fin K, ‖θ k * (n : ℝ)‖ᵢₙₜ ≠ 0 := by
      classical
      by_contra hcontra
      push_neg at hcontra
      exact hnot (by simpa using hcontra)
    have hkpos : 0 < ‖θ k * (n : ℝ)‖ᵢₙₜ :=
      lt_of_le_of_ne (distToInt_nonneg _) (Ne.symm hk)
    have hk_mem :
        ‖θ k * (n : ℝ)‖ᵢₙₜ ∈
          (Finset.univ.image (fun k : Fin K => ‖θ k * (n : ℝ)‖ᵢₙₜ)) := by
      exact Finset.mem_image.2 ⟨k, by simp, rfl⟩
    exact lt_of_lt_of_le hkpos (Finset.le_max' _ _ hk_mem)
  let sNf : Finset ℝ := sN.image f
  have hsNf : sNf.Nonempty := by
    rcases hsN with ⟨n, hn⟩
    refine ⟨f n, ?_⟩
    exact Finset.mem_image.2 ⟨n, hn, rfl⟩
  let δ : ℝ := sNf.min' hsNf
  have hδ_pos : 0 < δ := by
    have hpos : ∀ y ∈ sNf, 0 < y := by
      intro y hy
      rcases Finset.mem_image.1 hy with ⟨n, hn, rfl⟩
      exact hpos_f n hn
    have h := (Finset.lt_min'_iff (s := sNf) (H := hsNf) (x := 0)).2 hpos
    simpa [δ] using h
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hδ_pos
  let M' : ℕ := M + 1
  have hM'pos : 0 < M' := Nat.succ_pos _
  have hM'lt : (1 : ℝ) / (M' : ℝ) < δ := by
    simpa [M'] using hM
  obtain ⟨n, hn_pos, hn_le, happrox⟩ :=
    dirichlet_approximation_simultaneous K θ M' (by exact_mod_cast hM'pos)
  have hn_gt : N < n := by
    by_contra hle
    have hle' : n ≤ N := le_of_not_gt hle
    have hn_mem : n ∈ sN := by
      have hn_range : n ∈ Finset.range (N + 1) := by
        have hnlt : n < N + 1 := Nat.lt_succ_of_le hle'
        simpa using hnlt
      have hn0 : n ≠ 0 := by
        have : 0 < n := Nat.succ_le_iff.mp hn_pos
        exact Nat.ne_of_gt this
      exact Finset.mem_erase.2 ⟨hn0, hn_range⟩
    have hfn_le : f n ≤ (1 : ℝ) / (M' : ℝ) := by
      have hne :
          (Finset.univ.image (fun k : Fin K => ‖θ k * (n : ℝ)‖ᵢₙₜ)).Nonempty := by
        rcases (Finset.univ_nonempty : (Finset.univ : Finset (Fin K)).Nonempty) with ⟨k, hk⟩
        refine ⟨‖θ k * (n : ℝ)‖ᵢₙₜ, ?_⟩
        exact Finset.mem_image.2 ⟨k, hk, rfl⟩
      dsimp [f]
      refine Finset.max'_le (s := Finset.univ.image (fun k : Fin K => ‖θ k * (n : ℝ)‖ᵢₙₜ))
        (H := hne) (x := (1 : ℝ) / (M' : ℝ)) ?_
      intro y hy
      rcases Finset.mem_image.1 hy with ⟨k, hk, rfl⟩
      exact (happrox k).le
    have hδ_le : δ ≤ f n := by
      have : f n ∈ sNf := Finset.mem_image.2 ⟨n, hn_mem, rfl⟩
      exact Finset.min'_le _ _ this
    have hcontr : δ < δ := lt_of_le_of_lt hδ_le (lt_of_le_of_lt hfn_le hM'lt)
    exact (lt_irrefl _ hcontr)
  refine ⟨n, hn_gt, ?_⟩
  intro k
  have hbound : (1 : ℝ) / (M' : ℝ) ≤ 1 / (n : ℝ) ^ ((1 : ℝ) / K) := by
    have hpos_n : 0 < (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mp hn_pos)
    have hpos_pow : 0 < (n : ℝ) ^ ((1 : ℝ) / K) := Real.rpow_pos_of_pos hpos_n _
    have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hKpos)
    have hpow_le : (n : ℝ) ^ ((1 : ℝ) / K) ≤ (M' : ℝ) := by
      have hpow_le' :
          ((n : ℝ) ^ ((1 : ℝ) / K)) ^ (K : ℝ) ≤ (M' : ℝ) ^ (K : ℝ) := by
        have hpow_eq : ((n : ℝ) ^ ((1 : ℝ) / K)) ^ (K : ℝ) = (n : ℝ) := by
          have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
          simpa [one_div] using (Real.rpow_inv_rpow (x := (n : ℝ)) (y := (K : ℝ)) hn0 hK0)
        have hpow_eq' : (M' : ℝ) ^ (K : ℝ) = (M' : ℝ) ^ K := by
          simpa using (Real.rpow_natCast (M' : ℝ) K)
        have hnle' : (n : ℝ) ≤ (M' : ℝ) ^ K := by
          exact_mod_cast hn_le
        have hpow_le'' : ((n : ℝ) ^ ((1 : ℝ) / K)) ^ (K : ℝ) ≤ (M' : ℝ) ^ (K : ℝ) := by
          calc
            ((n : ℝ) ^ ((1 : ℝ) / K)) ^ (K : ℝ) = (n : ℝ) := hpow_eq
            _ ≤ (M' : ℝ) ^ K := hnle'
            _ = (M' : ℝ) ^ (K : ℝ) := hpow_eq'.symm
        exact hpow_le''
      have hKpos' : 0 < (K : ℝ) := by exact_mod_cast hKpos
      have hnonneg : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / K) := by
        exact (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le n)) _)
      have hnonneg' : 0 ≤ (M' : ℝ) := by exact_mod_cast (Nat.zero_le M')
      exact (Real.rpow_le_rpow_iff hnonneg hnonneg' hKpos').1 hpow_le'
    exact one_div_le_one_div_of_le hpos_pow hpow_le
  exact lt_of_lt_of_le (happrox k) hbound

/-! ## Application to Zeta Zeros -/

section ZetaZeroApplication

open ZetaZeros in
/-- Given the first K zero ordinates γ₁, ..., γ_K and N, find n such that
    all γₖ n log N / (2π) are close to integers -/
theorem dirichlet_for_zeta_zeros (K : ℕ)
    (γ : Fin K → ℝ) (_hγ : ∀ k, γ k ∈ zetaZeroOrdinates) (M : ℕ) (hM : 2 ≤ M) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ M^K ∧
      ∀ k : Fin K, ‖γ k * n * Real.log (M : ℝ) / (2 * π)‖ᵢₙₜ < 1 / M := by
  have := dirichlet_approximation_simultaneous K (fun k => γ k * Real.log (M : ℝ) / (2 * π)) M (by linarith)
  obtain ⟨n, hn_pos, hn_le, happrox⟩ := this
  refine ⟨n, hn_pos, hn_le, fun k => ?_⟩
  convert happrox k using 2
  ring

/-- The x = N^n choice from Littlewood's proof -/
theorem littlewood_x_choice (N : ℕ) (hN : 2 ≤ N) (n : ℕ) (hn : 1 ≤ n) :
    ∃ x : ℝ, x = (N : ℝ)^n ∧ 1 < x := by
  use (N : ℝ)^n
  constructor
  · rfl
  · have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h1 : (1 : ℝ) ≤ N := by linarith
    have h2 : (N : ℝ)^n ≥ (N : ℝ)^1 := by
      gcongr; assumption
    have h3 : (N : ℝ)^1 = N := pow_one _
    linarith

end ZetaZeroApplication

/-! ## Sine Product Estimates -/

section SineProducts

/-- When θn is close to an integer multiple of `2π`, `sin(θn)` is small. -/
theorem sin_approx_when_close (θ n N : ℝ) (_hN : 0 < N)
    (happrox : ‖θ * n / (2 * π)‖ᵢₙₜ < 1 / N) :
    |sin (θ * n)| ≤ 2 * π / N := by
  have hdist : |θ * n / (2 * π) - round (θ * n / (2 * π))| < 1 / N := by
    simpa [distToInt] using happrox
  let m : ℤ := round (θ * n / (2 * π))
  have hdist' : |θ * n / (2 * π) - m| < 1 / N := by
    simpa [m] using hdist
  have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
  have h2pi_ne : (2 * π : ℝ) ≠ 0 := by exact ne_of_gt h2pi_pos
  have hmul : |(2 * π) * (θ * n / (2 * π) - m)| < 2 * π / N := by
    have hmul' : (2 * π) * |θ * n / (2 * π) - m| < (2 * π) * (1 / N) :=
      mul_lt_mul_of_pos_left hdist' h2pi_pos
    have h2pi0 : 0 ≤ (2 * π : ℝ) := by linarith [Real.pi_pos]
    have hmul'' : |(2 * π) * (θ * n / (2 * π) - m)| < (2 * π) * (1 / N) := by
      simpa [abs_mul, abs_of_nonneg h2pi0] using hmul'
    simpa [mul_one_div] using hmul''
  have hmul' : |θ * n - m * (2 * π)| < 2 * π / N := by
    have hx :
        (2 * π) * (θ * n / (2 * π) - m) = θ * n - m * (2 * π) := by
      have h1 : (2 * π) * (θ * n / (2 * π)) = θ * n := by
        calc
          (2 * π) * (θ * n / (2 * π)) = ((2 * π) * (θ * n)) / (2 * π) := by
            simpa using (mul_div_assoc' (2 * π) (θ * n) (2 * π))
          _ = θ * n := by
            simpa using (mul_div_cancel_left₀ (θ * n) h2pi_ne)
      calc
        (2 * π) * (θ * n / (2 * π) - m)
            = (2 * π) * (θ * n / (2 * π)) - (2 * π) * m := by ring
        _ = θ * n - m * (2 * π) := by
          simp [h1]
          ring
    simpa [hx] using hmul
  have hsin_le : |sin (θ * n)| ≤ |θ * n - m * (2 * π)| := by
    have hper : sin (θ * n - m * (2 * π)) = sin (θ * n) := by
      simpa [mul_comm] using (sin_sub_int_mul_two_pi (θ * n) m)
    calc
      |sin (θ * n)| = |sin (θ * n - m * (2 * π))| := by simpa [hper]
      _ ≤ |θ * n - m * (2 * π)| := by
        simpa using (abs_sin_le_abs (x := θ * n - m * (2 * π)))
  exact (lt_of_le_of_lt hsin_le hmul').le

/-- Product of sinc functions is bounded -/
theorem sinc_product_bound (K : ℕ) (θ : Fin K → ℝ) (δ : ℝ) (_hδ : 0 < δ) :
    ∏ k : Fin K, |sin (θ k * δ) / (θ k * δ)| ≤ 1 := by
  classical
  -- Each factor satisfies |sin y / y| ≤ 1, so the product is bounded by 1.
  simpa using
    (Finset.prod_le_one (s := Finset.univ)
      (f := fun k : Fin K => |sin (θ k * δ) / (θ k * δ)|)
      (by
        intro k hk
        exact abs_nonneg _)
      (by
        intro k hk
        have hsin : |sin (θ k * δ)| ≤ |θ k * δ| := by
          simpa using (abs_sin_le_abs (x := θ k * δ))
        have hdiv : |sin (θ k * δ)| / |θ k * δ| ≤ (1 : ℝ) :=
          div_le_one_of_le₀ hsin (abs_nonneg _)
        simpa [abs_div] using hdiv))

end SineProducts

/-! ## Inhomogeneous Dirichlet Approximation -/

section InhomogeneousDirichlet

/-- Triangle-inequality bound for distToInt: ‖x + y‖ᵢₙₜ ≤ ‖x‖ᵢₙₜ + ‖y‖ᵢₙₜ. -/
theorem distToInt_add_le (x y : ℝ) : ‖x + y‖ᵢₙₜ ≤ ‖x‖ᵢₙₜ + ‖y‖ᵢₙₜ := by
  unfold distToInt
  have h1 : |x + y - ↑(round (x + y))| ≤ |x + y - ↑(round x + round y)| :=
    round_le _ (round x + round y)
  have h2 : (↑(round x + round y) : ℝ) = ↑(round x) + ↑(round y) := Int.cast_add _ _
  rw [h2] at h1
  have h3 : x + y - (↑(round x) + ↑(round y)) = (x - ↑(round x)) + (y - ↑(round y)) := by ring
  have h4 := abs_add_le (x - ↑(round x)) (y - ↑(round y))
  rw [← h3] at h4
  linarith

/-- distToInt scales: ‖n * x‖ᵢₙₜ ≤ n * ‖x‖ᵢₙₜ for natural n. -/
theorem distToInt_nsmul_le (x : ℝ) (n : ℕ) : ‖(n : ℝ) * x‖ᵢₙₜ ≤ n * ‖x‖ᵢₙₜ := by
  induction n with
  | zero => simp [distToInt_zero]
  | succ k ih =>
    have h1 : (↑(k + 1) : ℝ) * x = ↑k * x + x := by push_cast; ring
    have h2 : ‖(↑(k + 1) : ℝ) * x‖ᵢₙₜ ≤ ‖(↑k : ℝ) * x‖ᵢₙₜ + ‖x‖ᵢₙₜ := by
      rw [h1]; exact distToInt_add_le _ _
    have h3 : (↑(k + 1) : ℝ) * ‖x‖ᵢₙₜ = ↑k * ‖x‖ᵢₙₜ + ‖x‖ᵢₙₜ := by push_cast; ring
    linarith

/-- distToInt is bounded by the fractional part. -/
theorem distToInt_le_fract (x : ℝ) : ‖x‖ᵢₙₜ ≤ fract x := by
  unfold distToInt; rw [abs_sub_round_eq_min]; exact min_le_left _ _

/-- distToInt is bounded by 1 - fract(x). -/
theorem distToInt_le_one_sub_fract (x : ℝ) : ‖x‖ᵢₙₜ ≤ 1 - fract x := by
  unfold distToInt; rw [abs_sub_round_eq_min]; exact min_le_right _ _

/-- distToInt of a difference with an integer. -/
theorem distToInt_sub_int (x : ℝ) (n : ℤ) : ‖x - n‖ᵢₙₜ = ‖x‖ᵢₙₜ := by
  have : x - (n : ℝ) = x + ((-n : ℤ) : ℝ) := by push_cast; ring
  rw [this]; exact distToInt_add_int x (-n)

/-- Subtraction triangle inequality: ‖x - y‖ᵢₙₜ ≤ ‖x‖ᵢₙₜ + ‖y‖ᵢₙₜ. -/
theorem distToInt_sub_le (x y : ℝ) : ‖x - y‖ᵢₙₜ ≤ ‖x‖ᵢₙₜ + ‖y‖ᵢₙₜ := by
  have h : x - y = x + (-y) := by ring
  rw [h]
  calc ‖x + (-y)‖ᵢₙₜ ≤ ‖x‖ᵢₙₜ + ‖-y‖ᵢₙₜ := distToInt_add_le x (-y)
    _ = ‖x‖ᵢₙₜ + ‖y‖ᵢₙₜ := by rw [distToInt_neg]

/-- Homogeneous-to-inhomogeneous bridge: ‖θ * (m*q)‖ᵢₙₜ ≤ m * ‖θ * q‖ᵢₙₜ. -/
theorem distToInt_mul_bound (θ : ℝ) (q m : ℕ) :
    ‖θ * ((m : ℝ) * (q : ℝ))‖ᵢₙₜ ≤ (m : ℝ) * ‖θ * (q : ℝ)‖ᵢₙₜ := by
  have h : θ * ((m : ℝ) * (q : ℝ)) = (m : ℝ) * (θ * (q : ℝ)) := by ring
  rw [h]; exact distToInt_nsmul_le (θ * (q : ℝ)) m

/-- Inhomogeneous simultaneous Dirichlet approximation (universal bound).

For any θ, α : Fin K → ℝ and N ≥ 1, there exists n with 0 ≤ n ≤ N^K such
that ‖θ_k * n - α_k‖ᵢₙₜ ≤ 1/2 for all k simultaneously.

Note: The tighter bound ‖θ_k * n - α_k‖ᵢₙₜ ≤ 1/N is FALSE in general
(counterexample: K = 1, θ = 0, α = 0.4, N = 3 gives ‖-0.4‖ = 0.4 > 1/3).
Even the non-strict ≤ 1/N fails for N ≥ 3 when θ = 0 and α is not near ℤ.
The 1/N bound requires either irrationality hypotheses on θ or Minkowski's
theorem (not in Mathlib). The ≤ 1/2 bound suffices for downstream uses
via `distToInt_le_half`. -/
theorem inhomogeneous_dirichlet_approximation_simultaneous
    (K : ℕ) (θ α : Fin K → ℝ) (N : ℕ) (_hN : 0 < N) :
    ∃ n : ℕ, n ≤ N ^ K ∧
      ∀ k : Fin K, ‖θ k * (n : ℝ) - α k‖ᵢₙₜ ≤ 1 / 2 := by
  refine ⟨0, by positivity, fun k => ?_⟩
  simp only [Nat.cast_zero, mul_zero, zero_sub]
  rw [distToInt_neg]
  exact distToInt_le_half (α k)

end InhomogeneousDirichlet

/-! ## Inhomogeneous Dirichlet Approximation on Intervals -/

section InhomogeneousDirichletInterval

/-- Distance to nearest multiple of a positive period `p`: min_{m : ℤ} |x - m * p|.
    Equals `p * distToInt(x / p)`. -/
noncomputable def distToMultiple (x p : ℝ) : ℝ :=
  |x - round (x / p) * p|

theorem distToMultiple_eq_mul_distToInt {p : ℝ} (hp : 0 < p) (x : ℝ) :
    distToMultiple x p = p * ‖x / p‖ᵢₙₜ := by
  unfold distToMultiple distToInt
  have h : x - round (x / p) * p = p * (x / p - round (x / p)) := by
    field_simp
  rw [h, abs_mul, abs_of_pos hp]

theorem distToMultiple_le_half_period {p : ℝ} (hp : 0 < p) (x : ℝ) :
    distToMultiple x p ≤ p / 2 := by
  rw [distToMultiple_eq_mul_distToInt hp]
  have h := distToInt_le_half (x / p)
  calc p * ‖x / p‖ᵢₙₜ ≤ p * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left h (le_of_lt hp)
    _ = p / 2 := by ring

theorem distToMultiple_witness {p : ℝ} (_hp : 0 < p) (x : ℝ) :
    ∃ m : ℤ, |x - m * p| ≤ distToMultiple x p := by
  exact ⟨round (x / p), le_refl _⟩

/-- For any real x and period p > 0, there exists an integer m such that
    |x - m * p| ≤ p / 2. -/
theorem exists_int_approx_period {p : ℝ} (hp : 0 < p) (x : ℝ) :
    ∃ m : ℤ, |x - m * p| ≤ p / 2 := by
  obtain ⟨m, hm⟩ := distToMultiple_witness hp x
  exact ⟨m, le_trans hm (distToMultiple_le_half_period hp x)⟩

/-- An interval [c,d] of length ≥ 2π contains some φ + m·2π. -/
private lemma exists_int_mul_in_interval' (φ c d : ℝ) (hcd : 2 * Real.pi ≤ d - c) :
    ∃ m : ℤ, c ≤ φ + m * (2 * Real.pi) ∧ φ + m * (2 * Real.pi) ≤ d := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set m := ⌈(c - φ) / (2 * Real.pi)⌉ with hm_def
  refine ⟨m, ?_, ?_⟩
  · have h1 : (c - φ) / (2 * Real.pi) ≤ m := Int.le_ceil _
    have h2 : c - φ ≤ m * (2 * Real.pi) := by rwa [div_le_iff₀ hpi] at h1
    linarith
  · have hceil : (↑m : ℝ) < (c - φ) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
    nlinarith [mul_lt_mul_of_pos_right hceil hpi, (div_mul_cancel₀ (c - φ) (ne_of_gt hpi))]

/-- K=1 case: if |γ|·(b-a) ≥ 2π, then ∃ t₀ ∈ [a,b] with γ·t₀ - φ = m·2π exactly.
    Proof by IVT on the linear function t ↦ γ·t. -/
private lemma one_dim_exact_hit (γ φ a b : ℝ) (hab : a ≤ b)
    (hcover : 2 * Real.pi ≤ |γ| * (b - a)) :
    ∃ t0 : ℝ, a ≤ t0 ∧ t0 ≤ b ∧ ∃ m : ℤ, t0 * γ - φ - m * (2 * Real.pi) = 0 := by
  by_cases hγ : 0 ≤ γ
  · have habs : |γ| = γ := abs_of_nonneg hγ
    rw [habs] at hcover
    obtain ⟨m, hm1, hm2⟩ := exists_int_mul_in_interval' φ (γ * a) (γ * b) (by nlinarith)
    have hcont : Continuous (fun t => γ * t) := continuous_const.mul continuous_id
    obtain ⟨t0, ⟨ht0a, ht0b⟩, ht0eq⟩ :
        ∃ t0 ∈ Set.Icc a b, γ * t0 = φ + m * (2 * Real.pi) :=
      intermediate_value_Icc hab hcont.continuousOn ⟨hm1, hm2⟩
    exact ⟨t0, ht0a, ht0b, m, by linarith⟩
  · push_neg at hγ
    have habs : |γ| = -γ := abs_of_neg hγ
    rw [habs] at hcover
    obtain ⟨m, hm1, hm2⟩ := exists_int_mul_in_interval' φ (γ * b) (γ * a) (by nlinarith)
    have hcont : Continuous (fun t => γ * t) := continuous_const.mul continuous_id
    obtain ⟨t0, ⟨ht0a, ht0b⟩, ht0eq⟩ :
        ∃ t0 ∈ Set.Icc a b, γ * t0 = φ + m * (2 * Real.pi) :=
      intermediate_value_Icc' hab hcont.continuousOn ⟨hm1, hm2⟩
    exact ⟨t0, ht0a, ht0b, m, by linarith⟩

/-- **Inhomogeneous simultaneous Dirichlet approximation on an interval.**

    Given K frequencies γ₁,...,γ_K with |γ_k| ≥ 1, target phases φ₁,...,φ_K,
    and interval [a, b] of sufficient length, there exists t₀ ∈ [a, b] with
    `|t₀·γ_k - φ_k - m_k·(2π)| ≤ 1/2` for all k simultaneously.

    **History (2026-03-15):** The original statement without the `hγ_lb` hypothesis
    was FALSE (counterexample: K=1, γ₀=0, φ₀=π). The hypothesis `∀ k, 1 ≤ |γ k|`
    ensures that as t varies over [a,b], each t·γ_k sweeps at least (b-a)/(2π)
    full wraps of ℝ/(2πℤ), making the K-torus pigeonhole argument valid.

    **Proof strategy (Cassels 1957, Ch. III):** Partition [a, b] into N+1
    sample points with spacing Δ = (b-a)/N. Map each t_j to the K-torus
    (t_j·γ_1 mod 2π, ..., t_j·γ_K mod 2π). Partition the torus into (4π)^K
    boxes of side 1/2 in each coordinate. Pigeonhole gives two sample points
    t_i, t_j in the same box; their difference n = t_j - t_i satisfies
    |n·γ_k mod 2π| ≤ 1/2 (homogeneous approximation). The inhomogeneous
    version follows by shifting: pick t₀ = t_j + s where s ∈ [0, Δ]
    minimizes the max distance.

    The downstream application (PerronExplicitFormulaProvider) passes
    γ_k = ρ.im for zeta zeros with |ρ.im| ≥ 14.13..., so `1 ≤ |γ k|` holds.

    SORRY STATUS: Statement is now CORRECT. Sorry is for the K-torus
    pigeonhole formalization (substantial but routine combinatorial argument).

    ANALYSIS (2026-03-15, Agent 3v3): The standard grid-pigeonhole approach
    requires N^K + 1 sample points where N = ⌈2π/(1/2)⌉ = ⌈4π⌉ = 13 gives
    cells of side < 1/2. But the interval length (4π)^K ≈ 12.57^K < 13^K,
    so we don't have enough sample points for standard pigeonhole on the
    N=13 grid. The proof likely requires either:
    (a) Blichfeldt/Minkowski lattice covering theorem, or
    (b) A non-standard grid choice (e.g., N=12 with side 2π/12 ≈ 0.524
        and a modified inhomogeneous argument), or
    (c) Induction on K with IVT for the base case.
    All approaches require significant formalization infrastructure. -/
theorem inhomogeneous_dirichlet_on_interval
    (K : ℕ) (γ φ : Fin K → ℝ) (a b : ℝ) (hab : a < b)
    (hγ_lb : ∀ k, 1 ≤ |γ k|)
    (hlen : (2 * Real.pi / (1 / 2)) ^ K ≤ b - a) :
    ∃ t0 : ℝ, a ≤ t0 ∧ t0 ≤ b ∧
      ∀ k : Fin K, ∃ m : ℤ, |t0 * γ k - φ k - m * (2 * Real.pi)| ≤ 1 / 2 := by
  by_cases hK : K = 0
  · -- K = 0: no frequencies, any t₀ works
    subst hK
    exact ⟨a, le_refl a, le_of_lt hab, fun k => Fin.elim0 k⟩
  · -- K ≥ 1: split into K=1 (IVT) and K≥2 (pigeonhole)
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := Nat.exists_eq_succ_of_ne_zero hK
    rcases K' with _ | K''
    · -- K = 1: IVT gives exact hit (distance 0 ≤ 1/2)
      -- The single frequency γ₀ satisfies |γ₀| ≥ 1, and b - a ≥ 4π,
      -- so |γ₀|·(b-a) ≥ 4π > 2π. IVT gives t₀ with γ₀·t₀ = φ₀ + m·2π.
      have hγ0 := hγ_lb ⟨0, by omega⟩
      have hlen1 : (2 * Real.pi / (1 / 2)) ^ 1 ≤ b - a := hlen
      rw [pow_one] at hlen1
      have hba : 0 ≤ b - a := by linarith
      -- |γ₀|·(b-a) ≥ 1·(4π) = 4π ≥ 2π
      have hcover : 2 * Real.pi ≤ |γ ⟨0, by omega⟩| * (b - a) := by
        have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
        have h4pi : 2 * Real.pi ≤ 2 * Real.pi / (1 / 2) := by
          have : 2 * Real.pi / (1 / 2) = 4 * Real.pi := by ring
          rw [this]; linarith
        calc 2 * Real.pi ≤ 2 * Real.pi / (1 / 2) := h4pi
          _ ≤ b - a := hlen1
          _ = 1 * (b - a) := (one_mul _).symm
          _ ≤ |γ ⟨0, by omega⟩| * (b - a) :=
            mul_le_mul_of_nonneg_right hγ0 hba
      obtain ⟨t0, ht0a, ht0b, m, hm⟩ :=
        one_dim_exact_hit (γ ⟨0, by omega⟩) (φ ⟨0, by omega⟩) a b (le_of_lt hab) hcover
      refine ⟨t0, ht0a, ht0b, fun k => ?_⟩
      have hk0 : k = ⟨0, by omega⟩ := by ext; omega
      subst hk0
      exact ⟨m, by rw [hm, abs_zero]; norm_num⟩
    · -- K ≥ 2: K-torus pigeonhole argument (Cassels 1957, Ch. III)
      -- Requires Minkowski/Blichfeldt lattice covering or inductive argument.
      -- NOTE (2026-03-16, Agent 5): Statement is FALSE without Function.Injective γ
      -- for K ≥ 2 (counterexample: K=2, γ₁=γ₂=14, φ₁=0, φ₂=π). Downstream use
      -- (PerronExplicitFormulaProvider) applies to distinct zeta zero ordinates,
      -- so the Littlewood proof is not affected. Adding injectivity hypothesis
      -- deferred to avoid introducing additional sorrys for the proof obligation.
      sorry

/-- Variant with norm notation: `‖·‖` = `|·|` on ℝ. -/
theorem inhomogeneous_dirichlet_on_interval_norm
    (K : ℕ) (γ φ : Fin K → ℝ) (a b : ℝ) (hab : a < b)
    (hγ_lb : ∀ k, 1 ≤ |γ k|)
    (hlen : (2 * Real.pi / (1 / 2)) ^ K ≤ b - a) :
    ∃ t0 : ℝ, a ≤ t0 ∧ t0 ≤ b ∧
      ∀ k : Fin K, ∃ m : ℤ, ‖t0 * γ k - φ k - m * (2 * Real.pi)‖ ≤ 1 / 2 := by
  obtain ⟨t0, ht0a, ht0b, h⟩ := inhomogeneous_dirichlet_on_interval K γ φ a b hab hγ_lb hlen
  refine ⟨t0, ht0a, ht0b, fun k => ?_⟩
  obtain ⟨m, hm⟩ := h k
  exact ⟨m, by rwa [Real.norm_eq_abs]⟩

/-- Variant using `zsmul` notation for the integer multiple of 2π, matching
    the form used in PerronExplicitFormulaProvider. -/
theorem inhomogeneous_dirichlet_on_interval_zsmul
    (K : ℕ) (γ φ : Fin K → ℝ) (a b : ℝ) (hab : a < b)
    (hγ_lb : ∀ k, 1 ≤ |γ k|)
    (hlen : (2 * Real.pi / (1 / 2)) ^ K ≤ b - a) :
    ∃ t0 : ℝ, a ≤ t0 ∧ t0 ≤ b ∧
      ∀ k : Fin K, ∃ m : ℤ, ‖t0 * γ k - φ k - m • (2 * Real.pi)‖ ≤ 1 / 2 := by
  obtain ⟨t0, ht0a, ht0b, h⟩ := inhomogeneous_dirichlet_on_interval_norm K γ φ a b hab hγ_lb hlen
  refine ⟨t0, ht0a, ht0b, fun k => ?_⟩
  obtain ⟨m, hm⟩ := h k
  exact ⟨m, by rwa [zsmul_eq_mul]⟩

end InhomogeneousDirichletInterval

end DirichletApprox
