/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

open Real BigOperators Finset

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
  sorry

theorem distToInt_add_int (x : ℝ) (n : ℤ) : ‖x + n‖ᵢₙₜ = ‖x‖ᵢₙₜ := by
  sorry

theorem distToInt_neg (x : ℝ) : ‖-x‖ᵢₙₜ = ‖x‖ᵢₙₜ := by
  sorry

/-! ## Sine Estimate -/

/-- Key estimate: |sin(πx)| ≤ π‖x‖ -/
theorem sin_pi_le_pi_distToInt (x : ℝ) : |sin (π * x)| ≤ π * ‖x‖ᵢₙₜ := by
  -- sin(πx) = sin(π(x - round(x))) since sin has period 2π
  -- and for |y| ≤ 1/2, |sin(πy)| ≤ π|y|
  sorry

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
  sorry

/-! ## Simultaneous Dirichlet Approximation -/

/-- Pigeonhole principle for K-dimensional unit cube -/
theorem pigeonhole_cube (K N : ℕ) (hN : 0 < N) (points : Fin (N^K + 1) → Fin K → ℕ)
    (hpoints : ∀ i k, points i k < N) :
    ∃ i j : Fin (N^K + 1), i < j ∧ ∀ k : Fin K, points i k = points j k := by
  -- There are N^K subcubes but N^K + 1 points
  sorry

/-- Simultaneous Dirichlet approximation theorem -/
theorem dirichlet_approximation_simultaneous
    (K : ℕ) (θ : Fin K → ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N^K ∧ ∀ k : Fin K, ‖θ k * n‖ᵢₙₜ < 1 / N := by
  -- Partition [0,1)^K into N^K subcubes of side 1/N
  -- Consider the N^K + 1 points (θ₁n mod 1, ..., θ_K n mod 1) for n = 0, 1, ..., N^K
  -- By pigeonhole, two points lie in the same subcube
  -- Their difference gives the required n
  sorry

/-- Corollary: infinitely many n satisfy the approximation -/
theorem dirichlet_approximation_simultaneous_infinitely_many
    (K : ℕ) (θ : Fin K → ℝ) :
    ∀ N : ℕ, 0 < N → ∃ n : ℕ, N < n ∧ ∀ k : Fin K, ‖θ k * n‖ᵢₙₜ < 1 / (n : ℝ)^((1 : ℝ)/K) := by
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
  sorry

/-- Product of sinc functions is bounded -/
theorem sinc_product_bound (K : ℕ) (θ : Fin K → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∏ k : Fin K, |sin (θ k * δ) / (θ k * δ)| ≤ 1 := by
  sorry

end SineProducts

end DirichletApprox
