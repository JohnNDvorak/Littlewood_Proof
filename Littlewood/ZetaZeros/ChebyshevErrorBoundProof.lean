/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Littlewood.ZetaZeros.SupremumRealPart
import Littlewood.ZetaZeros.ErrorBoundOptimization

/-!
# Proof of ChebyshevErrorBoundZeroFreeHyp

This file derives `ChebyshevErrorBoundZeroFreeHyp` (the PNT error bound
|ψ(x) - x| ≤ C·x·exp(-c·√(log x))) from `ZeroFreeRegionHyp` and
a truncated explicit formula hypothesis `TruncatedPsiBoundHyp`.

## Strategy

1. From `ZeroFreeRegionHyp`: all zeros satisfy Re(ρ) < 1 - c₀/log(|Im(ρ)|+2).
2. For height T, all zeros with |Im(ρ)| ≤ T satisfy Re(ρ) < 1 - c₀/log(T+2).
3. `TruncatedPsiBoundHyp` bounds |ψ(x) - x| using the zero-free width δ and
   truncation height T.
4. Choose T = exp(√(log x)) - 2 to optimize, giving δ = c₀/√(log x).
5. Each term in the bound is ≤ C·x·exp(-c·√(log x)) after absorbing
   polynomial factors into the exponential.

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapters 12-13
-/

open Real ZetaZeros Filter

namespace ZetaZeros

/-! ## Truncated Explicit Formula Hypothesis -/

/--
HYPOTHESIS: Truncated explicit formula bound.
For x ≥ 2, T ≥ 2, if all zeros with |Im(ρ)| ≤ T have Re(ρ) < 1 - δ (for δ > 0),
then |ψ(x) - x| is bounded by:
  A · x · exp(-δ · log x) · (log(T+2))² + A · x · (log x)² / T

This encodes the content of the truncated von Mangoldt explicit formula
combined with zero counting bounds ∑_{|γ|≤T} 1/|ρ| ≤ C·(log T)².

MATHEMATICAL STATUS: classical analytic number theory (Perron's formula +
  zero counting function N(T) ~ (T/2π) log(T/2π)).
MATHLIB STATUS: not available.
REFERENCE: Montgomery-Vaughan, Ch. 12-13.
-/
class TruncatedPsiBoundHyp : Prop where
  bound : ∃ A > 0, ∀ (x : ℝ), x ≥ 2 → ∀ (T : ℝ), T ≥ 2 → ∀ (δ : ℝ), 0 < δ →
    (∀ ρ ∈ zetaNontrivialZeros, |ρ.im| ≤ T → ρ.re < 1 - δ) →
    |chebyshevPsi x - x| ≤
      A * x * Real.exp (-δ * Real.log x) * (Real.log (T + 2)) ^ 2 +
      A * x * (Real.log x) ^ 2 / T

/-! ## Intermediate lemmas -/

/-- From the zero-free region: zeros with |Im(ρ)| ≤ T have Re(ρ) < 1 - c₀/log(T+2). -/
lemma zeroFreeRegion_strip (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hzfr : ∀ ρ ∈ zetaNontrivialZeros, ρ.re < 1 - c₀ / Real.log (|ρ.im| + 2))
    (T : ℝ) (_hT : 2 ≤ T)
    (ρ : ℂ) (hρ : ρ ∈ zetaNontrivialZeros) (hγ : |ρ.im| ≤ T) :
    ρ.re < 1 - c₀ / Real.log (T + 2) := by
  have h1 := hzfr ρ hρ
  have hlog_ρ_pos : 0 < Real.log (|ρ.im| + 2) := by
    apply Real.log_pos; linarith [abs_nonneg ρ.im]
  have hlog_le : Real.log (|ρ.im| + 2) ≤ Real.log (T + 2) := by
    apply Real.log_le_log
    · linarith [abs_nonneg ρ.im]
    · linarith
  have hdiv : c₀ / Real.log (T + 2) ≤ c₀ / Real.log (|ρ.im| + 2) :=
    div_le_div_of_nonneg_left hc₀.le hlog_ρ_pos hlog_le
  linarith

/-- Bridge lemma: from ZFR and truncated explicit formula, derive the explicit
formula with optimal T = exp(√(log x)) - 2 for large x.

For x with log x ≥ threshold, choose T = exp(√(log x)) - 2:
- T ≥ 2 (since √(log x) ≥ log 4)
- δ = c₀/√(log x) > 0
- All zeros with |γ| ≤ T have Re(ρ) < 1 - δ
- Bound simplifies to the form needed by optimization_main -/
lemma explicit_formula_with_optimal_T
    (c₀ A : ℝ) (hc₀ : 0 < c₀) (hA : 0 < A)
    (hzfr : ∀ ρ ∈ zetaNontrivialZeros, ρ.re < 1 - c₀ / Real.log (|ρ.im| + 2))
    (htrunc : ∀ (x : ℝ), x ≥ 2 → ∀ (T : ℝ), T ≥ 2 → ∀ (δ : ℝ), 0 < δ →
      (∀ ρ ∈ zetaNontrivialZeros, |ρ.im| ≤ T → ρ.re < 1 - δ) →
      |chebyshevPsi x - x| ≤
        A * x * Real.exp (-δ * Real.log x) * (Real.log (T + 2)) ^ 2 +
        A * x * (Real.log x) ^ 2 / T)
    (x : ℝ) (hx : x ≥ 2)
    (hlog : Real.log x ≥ max (4 * c₀ ^ 2) ((Real.log 4) ^ 2)) :
    |chebyshevPsi x - x| ≤
      A * x * Real.exp (-c₀ * (Real.log x).sqrt) * Real.log x +
      A * x * (Real.log x) ^ 2 / (Real.exp (Real.log x).sqrt - 2) := by
  -- Choose T = exp(√(log x)) - 2, δ = c₀ / √(log x)
  set u := (Real.log x).sqrt
  -- Key facts
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hlogx_pos
  have hu_ne : u ≠ 0 := ne_of_gt hu_pos
  have hu_nn : 0 ≤ u := hu_pos.le
  have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hu_ge_log4 : Real.log 4 ≤ u := by
    rw [← Real.sqrt_sq hlog4_nn]
    exact Real.sqrt_le_sqrt (le_trans (le_max_right _ _) hlog)
  have hu_sq : u ^ 2 = Real.log x := Real.sq_sqrt hlogx_nn
  -- T = exp(u) - 2 ≥ 2
  have hT_ge : 2 ≤ Real.exp u - 2 := by
    linarith [(Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 4)).1 hu_ge_log4]
  -- δ = c₀/u > 0
  have hδ_pos : 0 < c₀ / u := div_pos hc₀ hu_pos
  -- Zero-free region: ∀ ρ with |γ| ≤ T, Re(ρ) < 1 - c₀/u
  have hzfr_strip : ∀ ρ ∈ zetaNontrivialZeros, |ρ.im| ≤ Real.exp u - 2 →
      ρ.re < 1 - c₀ / u := by
    intro ρ hρ hγ
    have h := zeroFreeRegion_strip c₀ hc₀ hzfr (Real.exp u - 2) hT_ge ρ hρ hγ
    simp only [show Real.exp u - 2 + 2 = Real.exp u from by ring, Real.log_exp] at h
    exact h
  -- Apply htrunc with T = exp(u) - 2 and δ = c₀/u
  have hbound := htrunc x hx (Real.exp u - 2) hT_ge (c₀ / u) hδ_pos hzfr_strip
  -- Simplify the bound: δ * log x = c₀ * u
  have hδ_eq : c₀ / u * Real.log x = c₀ * u := by
    rw [div_mul_eq_mul_div, show c₀ * Real.log x / u = c₀ * (Real.log x / u) from by ring]
    congr 1
    rw [div_eq_iff hu_ne, ← sq]
    exact hu_sq.symm
  -- Simplify: log(T + 2) = u
  have hlog_T2 : Real.log (Real.exp u - 2 + 2) = u := by
    rw [show Real.exp u - 2 + 2 = Real.exp u from by ring, Real.log_exp]
  -- Now simplify the bound
  have hexp_eq : Real.exp (-(c₀ / u) * Real.log x) = Real.exp (-c₀ * u) := by
    congr 1
    rw [show -(c₀ / u) * Real.log x = -(c₀ / u * Real.log x) from by ring, hδ_eq]
    ring
  rw [hexp_eq, hlog_T2, hu_sq] at hbound
  exact hbound

/-- The key optimization lemma: combining truncated explicit formula with the zero-free
region and choosing T = exp(√(log x)) - 2 gives the exp(-c·√(log x)) bound. -/
lemma chebyshev_error_optimization
    (c₀ A : ℝ) (hc₀ : 0 < c₀) (hA : 0 < A)
    (hzfr : ∀ ρ ∈ zetaNontrivialZeros, ρ.re < 1 - c₀ / Real.log (|ρ.im| + 2))
    (htrunc : ∀ (x : ℝ), x ≥ 2 → ∀ (T : ℝ), T ≥ 2 → ∀ (δ : ℝ), 0 < δ →
      (∀ ρ ∈ zetaNontrivialZeros, |ρ.im| ≤ T → ρ.re < 1 - δ) →
      |chebyshevPsi x - x| ≤
        A * x * Real.exp (-δ * Real.log x) * (Real.log (T + 2)) ^ 2 +
        A * x * (Real.log x) ^ 2 / T) :
    ∃ c > 0, ∃ C > 0, ∀ x ≥ 2,
      |chebyshevPsi x - x| ≤ C * x * Real.exp (-c * (Real.log x).sqrt) := by
  -- Apply the standalone optimization_main theorem
  apply ChebyshevErrorBoundOpt.optimization_main
    (fun x => chebyshevPsi x - x) c₀ A hc₀ hA
  -- Goal 1: crude bound
  · intro x hx
    exact ChebyshevErrorBound.chebyshev_psi_crude_bound hx
  -- Goal 2: explicit formula for large x
  · intro x hx hlog
    exact explicit_formula_with_optimal_T c₀ A hc₀ hA hzfr htrunc x hx hlog

/-! ## Main Instance -/

/-- The zero-free region implies the Chebyshev error bound exp(-c·√(log x)). -/
instance chebyshevErrorBound_of_zeroFreeRegion
    [ZeroFreeRegionHyp] [TruncatedPsiBoundHyp] : ChebyshevErrorBoundZeroFreeHyp where
  bound := by
    obtain ⟨c₀, hc₀, hzfr⟩ := ZeroFreeRegionHyp.region
    obtain ⟨A, hA, htrunc⟩ := TruncatedPsiBoundHyp.bound
    exact chebyshev_error_optimization c₀ A hc₀ hA hzfr htrunc

end ZetaZeros
