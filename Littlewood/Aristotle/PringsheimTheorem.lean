/-
Pringsheim's theorem: a power series with non-negative real coefficients
has its radius of convergence as a singularity on the positive real axis.

## Main Result

* `pringsheim_contradiction` : If f(z) = ∑ aₙ zⁿ with aₙ ≥ 0 converges on
    B(0, R) and diverges at z = R, then f cannot be analytically continued past R.

## Proof Sketch

The proof is by contradiction: if f extends analytically past R, then by continuity
at R, the partial sums ∑_{n<N} aₙ Rⁿ are bounded by |f(R)|. Since all terms are
non-negative, the series converges at R — contradicting the divergence hypothesis.

## References

* Titchmarsh, "The Theory of Functions", §1.8
* Pringsheim, "Über Funktionen, welche in gewissen Punkten endliche Differentialquotienten
  jeder endlichen Ordnung, aber keine Taylor'sche Reihenentwickelung besitzen" (1893)

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.PringsheimTheorem

open Complex Real Filter Topology Set Finset

/-! ## Pringsheim's theorem

The key insight: for a power series with non-negative coefficients,
convergence on B(0, R) plus continuity at R forces convergence at R. -/

/-- Real summability from complex summability for non-negative real coefficients.
If ∑ (↑(aₙ · tⁿ)) converges in ℂ, then ∑ (aₙ · tⁿ) converges in ℝ. -/
private lemma real_summable_of_complex_hasSum
    (a : ℕ → ℝ) (t : ℝ) (_ht : 0 ≤ t)
    (hsum : Summable (fun n => (a n : ℂ) * (↑t : ℂ) ^ n)) :
    Summable (fun n => a n * t ^ n) := by
  have h_eq : ∀ n, (a n : ℂ) * (↑t : ℂ) ^ n = ↑(a n * t ^ n) := by
    intro n
    rw [ofReal_mul, ofReal_pow]
  simp_rw [h_eq] at hsum
  exact (summable_ofReal.mp hsum)

/-- The complex power series sum equals the real sum cast to ℂ. -/
private lemma complex_tsum_eq_ofReal_tsum
    (a : ℕ → ℝ) (t : ℝ) (_ht : 0 ≤ t) :
    ∑' n, (a n : ℂ) * (↑t : ℂ) ^ n = ↑(∑' n, a n * t ^ n) := by
  have h_eq : (fun n => (a n : ℂ) * (↑t : ℂ) ^ n) = (fun n => (↑(a n * t ^ n) : ℂ)) := by
    ext n; push_cast; ring
  rw [h_eq, ofReal_tsum]

/-- Partial sums of a non-negative summable series are bounded by the full sum. -/
private lemma partial_sum_le_tsum (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (R : ℝ) (hR : 0 < R) (hs : Summable (fun n => a n * R ^ n)) (N : ℕ) :
    ∑ n ∈ range N, a n * R ^ n ≤ ∑' n, a n * R ^ n :=
  hs.sum_le_tsum (range N) (fun n _ => mul_nonneg (ha n) (pow_nonneg hR.le n))

/-- **Pringsheim's theorem**: A power series f(z) = ∑ aₙ zⁿ with non-negative
real coefficients that diverges at z = R cannot have an analytic continuation
to a neighborhood of the real point z = R.

More precisely: if f is defined on B(0, R) by the power series, and f has a
continuous extension to z = R (e.g., from analyticity), then the series actually
converges at z = R. -/
theorem pringsheim_convergence_at_radius
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (R : ℝ) (hR : 0 < R)
    -- f is defined by the power series on B(0, R)
    (f : ℂ → ℂ)
    (hf_sum : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => (a n : ℂ) * z ^ n) (f z))
    -- f has a continuous extension to z = R (weaker than analyticity)
    (hf_cont : ContinuousAt f (↑R : ℂ)) :
    Summable (fun n => a n * R ^ n) := by
  -- Strategy: show partial sums are bounded by |f(R)|, conclude by monotone convergence.
  -- Step 1: For t ∈ (0, R), the real sum equals (f ↑t).re
  have hf_real : ∀ t : ℝ, 0 ≤ t → t < R →
      (f (↑t : ℂ)).re = ∑' n, a n * t ^ n := by
    intro t ht htR
    have h_norm : ‖(↑t : ℂ)‖ < R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]; exact htR
    have hs := (hf_sum (↑t) h_norm).tsum_eq.symm
    -- hs : f ↑t = ∑' n, ↑(a n) * ↑t ^ n
    conv_lhs => rw [hs]
    rw [complex_tsum_eq_ofReal_tsum a t ht, ofReal_re]
  -- Step 2: For t ∈ (0, R), partial sums are bounded by (f ↑t).re
  have hf_partial_le : ∀ t : ℝ, 0 ≤ t → t < R → ∀ N : ℕ,
      ∑ n ∈ range N, a n * t ^ n ≤ (f (↑t : ℂ)).re := by
    intro t ht htR N
    have h_norm : ‖(↑t : ℂ)‖ < R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]; exact htR
    have hsummable : Summable (fun n => a n * t ^ n) :=
      real_summable_of_complex_hasSum a t ht (hf_sum (↑t) h_norm).summable
    rw [hf_real t ht htR]
    exact hsummable.sum_le_tsum (range N) (fun n _ => mul_nonneg (ha n) (pow_nonneg ht n))
  -- Step 3: For each N, ∑_{n<N} aₙ Rⁿ ≤ (f ↑R).re by passing to the limit t → R⁻
  have hbound : ∀ N : ℕ, ∑ n ∈ range N, a n * R ^ n ≤ (f (↑R : ℂ)).re := by
    intro N
    -- LHS is a continuous function of t, taking limit as t → R from below
    have h_lhs_tendsto : Tendsto
        (fun t : ℝ => ∑ n ∈ range N, a n * t ^ n) (𝓝[<] R)
        (𝓝 (∑ n ∈ range N, a n * R ^ n)) := by
      apply tendsto_finset_sum
      intro n _
      exact (continuousAt_const.mul (continuous_pow n).continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds
    -- RHS is continuous
    have h_rhs_tendsto : Tendsto
        (fun t : ℝ => (f (↑t : ℂ)).re) (𝓝[<] R) (𝓝 ((f (↑R : ℂ)).re)) := by
      exact (Complex.continuous_re.continuousAt.comp
        (hf_cont.comp Complex.continuous_ofReal.continuousAt)).tendsto.mono_left
        nhdsWithin_le_nhds
    -- The inequality holds for t ∈ (R/2, R) (each such t satisfies 0 ≤ t and t < R)
    have h_ineq : ∀ᶠ t in 𝓝[<] R,
        ∑ n ∈ range N, a n * t ^ n ≤ (f (↑t : ℂ)).re := by
      have h_mem : Ioo (R / 2) R ∈ 𝓝[<] R :=
        Ioo_mem_nhdsLT (by linarith)
      filter_upwards [h_mem] with t ⟨ht_lower, ht_upper⟩
      exact hf_partial_le t (by linarith) ht_upper N
    exact le_of_tendsto_of_tendsto h_lhs_tendsto h_rhs_tendsto h_ineq
  -- Step 4: Bounded partial sums of non-negative series → summable
  exact summable_of_sum_range_le
    (fun n => mul_nonneg (ha n) (pow_nonneg hR.le n))
    (fun N => hbound N)

/-- **Pringsheim's theorem** (contradiction form): A power series with
non-negative coefficients that diverges at its radius of convergence
cannot be analytically continued past that radius. -/
theorem pringsheim_contradiction
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (R : ℝ) (hR : 0 < R)
    (f : ℂ → ℂ)
    (hf_sum : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => (a n : ℂ) * z ^ n) (f z))
    (hdiv : ¬Summable (fun n => a n * R ^ n))
    (hf_ext : AnalyticAt ℂ f (↑R : ℂ)) :
    False :=
  hdiv (pringsheim_convergence_at_radius a ha R hR f hf_sum hf_ext.continuousAt)

end Aristotle.PringsheimTheorem
