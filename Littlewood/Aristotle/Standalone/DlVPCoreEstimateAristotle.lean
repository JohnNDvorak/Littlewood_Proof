/-
# de la Vallée Poussin Core Estimate

The core analytic estimate for de la Vallée Poussin's zero-free region:
if ρ = β + iγ is a nontrivial zeta zero (0 < β < 1, γ > 0), then for σ ∈ (1, 2]:

    4/(σ - β) ≤ 3/(σ - 1) + A · log(γ + 2)

for a universal constant A ≥ 1.

## Proof structure

The proof reduces to the de la Vallée Poussin quantitative zero-free region
(`zeta_zero_free_region`) via elementary algebra (`dlvp_from_zfr`).

The zero-free region states that any nontrivial zero β + iγ of ζ with
γ > 0 satisfies 1 - β ≥ c/log(γ + 2) for a universal constant c > 0.
The core estimate then follows because the maximum of
4/(σ-β) - 3/(σ-1) over σ ∈ (1,2] is bounded by 1/(4(1-β)) ≤ log(γ+2)/(4c).

## Status

- `riemannZeta_norm_product_ge_one`: Proved ✓
  (Mertens' 3-4-1 product inequality from `norm_LFunction_product_ge_one`)
- `dlvp_from_zfr`: Proved ✓ (pure algebra)
- `dlVP_core_estimate`: Proved from `zeta_zero_free_region` ✓
- `zeta_zero_free_region`: **Sorry** — requires the Hadamard factorization
  of ζ'/ζ(s) to bound the logarithmic derivative, which provides
  O(log |t|) bounds not obtainable from Cauchy estimates or the Dirichlet
  series bound alone.
-/

import Mathlib

set_option maxHeartbeats 12800000

open Complex Real Filter Topology Asymptotics

noncomputable section

/-! ## Helper: product norm bound for the Riemann zeta function

For σ > 1 and any real y, the Mertens-type inequality holds:
  ‖ζ(σ)³ · ζ(σ + iy)⁴ · ζ(σ + 2iy)‖ ≥ 1
Follows from `DirichletCharacter.norm_LFunction_product_ge_one` for the trivial character mod 1.
-/
lemma riemannZeta_norm_product_ge_one {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    ‖riemannZeta (↑σ) ^ 3 * riemannZeta (↑σ + ↑y * I) ^ 4 *
      riemannZeta (↑σ + 2 * ↑y * I)‖ ≥ 1 := by
  convert DirichletCharacter.norm_LFunction_product_ge_one
    (1 : DirichletCharacter ℂ 1) (show 0 < (σ - 1) from by linarith) y using 1
  norm_num [DirichletCharacter.LFunction_modOne_eq]
  ring

/-! ## Key helper: quantitative zero-free region

The de la Vallée Poussin zero-free region: any nontrivial zero β + iγ of ζ
with γ > 0 satisfies 1 - β ≥ c / log(γ + 2) for some universal constant c > 0.

The classical proof (Davenport Ch. 14) applies the 3-4-1 trigonometric identity
3 + 4 cos θ + cos 2θ ≥ 0 to the Dirichlet series -ζ'/ζ(s) = Σ Λ(n)/n^s
to obtain the non-negativity of the combination
  3·(-Re ζ'/ζ(σ)) + 4·(-Re ζ'/ζ(σ+iγ)) + (-Re ζ'/ζ(σ+2iγ)) ≥ 0.
Bounding each term using the Hadamard factorization of ζ'/ζ(s) yields
  -Re ζ'/ζ(σ) ≤ 1/(σ-1) + C₁,
  -Re ζ'/ζ(σ+iγ) ≤ -1/(σ-β) + C₂ log(γ+2),
  -Re ζ'/ζ(σ+2iγ) ≤ C₃ log(γ+2),
which combine to give 4/(σ-β) ≤ 3/(σ-1) + A log(γ+2), and choosing
σ = 1 + 1/(A log(γ+2)) yields 1 - β ≥ c/log(γ+2).

The Hadamard factorization of ζ is NOT currently available in Mathlib
(it requires the partial fraction expansion of ζ'/ζ in terms of zeros),
so this lemma remains as sorry. -/
lemma zeta_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ β γ : ℝ,
      0 < γ → β < 1 →
      riemannZeta (↑β + ↑γ * I) = 0 →
      1 - β ≥ c / Real.log (γ + 2) := by
  sorry

/-! ## Algebraic reduction

The core estimate 4/(σ-β) ≤ 3/(σ-1) + (1/c)·L follows from 1-β ≥ c/L
by elementary algebra. The key bound is:

  4/(σ-β) - 3/(σ-1) = (σ+3β-4)/((σ-β)(σ-1))

When σ+3β ≤ 4, this is ≤ 0. When σ+3β > 4, we have σ-1 > 3(1-β)
and σ-β > 4(1-β), so the expression is at most 1/(4(1-β)) ≤ L/(4c).
-/
lemma dlvp_from_zfr (β σ c L : ℝ)
    (hβ : β < 1) (hσ1 : 1 < σ) (_hσ2 : σ ≤ 2) (hc : 0 < c) (hL : 0 < L)
    (hα : 1 - β ≥ c / L) :
    4 / (σ - β) ≤ 3 / (σ - 1) + (1 / c) * L := by
  field_simp at *
  rw [div_add', div_le_div_iff₀] <;> try nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hσ1.le hc.le,
    mul_le_mul_of_nonneg_left _hσ2 hc.le,
    mul_le_mul_of_nonneg_left hσ1.le hL.le,
    mul_le_mul_of_nonneg_left _hσ2 hL.le]

/-! ## Main theorem -/

/-- **Core analytic estimate for de la Vallée Poussin.**

If ρ = β + iγ is a nontrivial zero of ζ with 0 < β < 1 and γ > 0,
then for any σ > 1 with σ ≤ 2:

    4 / (σ - β) ≤ 3 / (σ - 1) + A · log(γ + 2)

for a universal constant A ≥ 1.

Classical, standard result. Reference: Davenport, "Multiplicative Number
Theory", Chapter 14, eqs. (4)-(7). -/
theorem dlVP_core_estimate :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ β γ σ : ℝ,
      β < 1 → 0 < γ →
      riemannZeta (↑β + ↑γ * I) = 0 →
      1 < σ → σ ≤ 2 →
      4 / (σ - β) ≤ 3 / (σ - 1) + A * Real.log (γ + 2) := by
  obtain ⟨c, hc_pos, hzfr⟩ := zeta_zero_free_region
  refine ⟨max 1 (1 / c), le_max_left _ _, fun β γ σ hβ hγ hζ hσ1 hσ2 => ?_⟩
  have hL_pos : 0 < Real.log (γ + 2) := Real.log_pos (by linarith)
  have hα := hzfr β γ hγ hβ hζ
  calc 4 / (σ - β)
      ≤ 3 / (σ - 1) + (1 / c) * Real.log (γ + 2) :=
        dlvp_from_zfr β σ c (Real.log (γ + 2)) hβ hσ1 hσ2 hc_pos hL_pos hα
    _ ≤ 3 / (σ - 1) + max 1 (1 / c) * Real.log (γ + 2) := by
        gcongr; exact le_max_right _ _

end
