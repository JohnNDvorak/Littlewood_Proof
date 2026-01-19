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
  -- Partition [0,1)^K into N^K subcubes of side 1/N
  -- Consider the N^K + 1 points (θ₁n mod 1, ..., θ_K n mod 1) for n = 0, 1, ..., N^K
  -- By pigeonhole, two points lie in the same subcube
  -- Their difference gives the required n
  -- TODO: Use `pigeonhole_cube` on `points i k = ⌊fract (θ k * i) * N⌋`, then show
  -- `|fract (θ k * j) - fract (θ k * i)| < 1 / N` and convert to `distToInt` using
  -- `Int.fract_eq_iff` plus `round_le`.
  sorry

/-- Corollary: infinitely many n satisfy the approximation -/
theorem dirichlet_approximation_simultaneous_infinitely_many
    (K : ℕ) (θ : Fin K → ℝ) :
    ∀ N : ℕ, 0 < N → ∃ n : ℕ, N < n ∧ ∀ k : Fin K, ‖θ k * n‖ᵢₙₜ < 1 / (n : ℝ)^((1 : ℝ)/K) := by
  -- TODO: Apply `dirichlet_approximation_simultaneous` with a growing parameter and
  -- compare `1 / N` to `1 / n^(1/K)` using `n ≤ N^K`.
  sorry

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

/-- When θn is close to an integer, sin(θn) ≈ ±sin(θ/N) -/
theorem sin_approx_when_close (θ n N : ℝ) (hN : 0 < N)
    (happrox : ‖θ * n / (2 * π)‖ᵢₙₜ < 1 / N) :
    ∃ ε : ℝ, |ε| ≤ 2 * π / N ∧
      |sin (θ * n) - sin (θ / N)| ≤ |ε| ∨ |sin (θ * n) + sin (θ / N)| ≤ |ε| := by
  -- TODO: Use periodicity and `sin_sub_sin_le` with `happrox` to show
  -- `|sin (θ * n)| ≤ 2 * π / N`, then choose the sign to compare to `sin (θ / N)`.
  sorry

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

end DirichletApprox
