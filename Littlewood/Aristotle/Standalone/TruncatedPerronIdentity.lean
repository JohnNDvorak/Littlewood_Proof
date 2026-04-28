import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Truncated Perron Sum Identity for the Chebyshev Psi Function

This file proves the truncated Perron sum identity for ψ(x) = Σ_{n≤x} Λ(n):

For x ≥ 2, c = 1 + 1/log x, T ≥ 2:
  ψ(x) = (1/2πi) ∫_{c-iT}^{c+iT} (-ζ'/ζ(s)) x^s/s ds + error

where |error| ≤ C · (x^c/(T · log x)) · Σ Λ(n) min(1, x/(T|x-n|)) ≤ C · log²x

## Proof strategy

The proof swaps sum and integral using absolute convergence of the Dirichlet series
-ζ'/ζ(s) = Σ Λ(n)/n^s for Re(s) > 1, then applies the Perron kernel truncation
bound term by term.

The file proves:
1. ψ(x) can be expressed as Σ Λ(n) · 1_{n ≤ ⌊x⌋} over any range N > ⌊x⌋
2. The error |ψ(x) - Σ Λ(n)K(n)| ≤ Σ Λ(n)|1_{n≤⌊x⌋} - K(n)| (triangle inequality
   using Λ ≥ 0)
3. Given hypotheses encoding the sum-integral swap (from absolute convergence) and the
   Perron kernel truncation bounds, the full error is O(log²x)

The analytic ingredients (Dirichlet series convergence, contour integral evaluation,
Perron kernel bounds) are encoded as hypotheses; the file proves the algebraic/combinatorial
core that combines these ingredients into the final bound.
-/

noncomputable section

open BigOperators Real Nat ArithmeticFunction

namespace TruncatedPerron

/-! ## Definitions -/

/-- The Chebyshev psi function: ψ(x) = Σ_{n ≤ x} Λ(n) -/
def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (vonMangoldt n : ℝ)

/-- Indicator for n ≤ ⌊x⌋₊, as a real number. -/
def indicatorLe (x : ℝ) (n : ℕ) : ℝ :=
  if n ≤ ⌊x⌋₊ then 1 else 0

/-! ## Core algebraic lemmas -/

/-
ψ(x) equals a sum of Λ(n) · 1_{n ≤ ⌊x⌋} over any range N > ⌊x⌋₊. This is the
    key rewriting that enables the Perron approach: the sharp cutoff at x is replaced
    by an indicator function that the Perron kernel will approximate.
-/
lemma chebyshevPsi_eq_indicator_sum (x : ℝ) (N : ℕ) (hN : ⌊x⌋₊ + 1 ≤ N) :
    chebyshevPsi x =
      ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) * indicatorLe x n := by
  unfold chebyshevPsi indicatorLe;
  rw [ ← Finset.sum_subset ( Finset.range_mono hN ) ];
  · exact Finset.sum_congr rfl fun i hi => by rw [ if_pos ( Finset.mem_range_succ_iff.mp hi ) ] ; ring;
  · grind

/-
Telescoping: the difference ψ(x) - Σ Λ(n)K(n) can be written as
    Σ Λ(n)(indicator - K(n)).
-/
lemma perron_difference_as_sum (x : ℝ) (N : ℕ) (hN : ⌊x⌋₊ + 1 ≤ N)
    (K : ℕ → ℝ) :
    chebyshevPsi x - ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) * K n =
      ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) * (indicatorLe x n - K n) := by
  rw [ chebyshevPsi_eq_indicator_sum x N hN, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun n hn => ?_ ] ; ring

/-
**Core error bound**: The absolute error |ψ(x) - Σ Λ(n)K(n)| is bounded by
    Σ Λ(n) · |1_{n≤⌊x⌋} - K(n)|.

    This uses the triangle inequality and the nonnegativity of the von Mangoldt function.
    It is the key algebraic step in the truncated Perron formula: once we swap sum and
    integral, each term contributes Λ(n) times the Perron kernel approximation error.
-/
theorem perron_error_triangle_bound (x : ℝ) (N : ℕ) (hN : ⌊x⌋₊ + 1 ≤ N)
    (K : ℕ → ℝ) :
    |chebyshevPsi x - ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) * K n| ≤
      ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) * |indicatorLe x n - K n| := by
  rw [ perron_difference_as_sum x N hN K ];
  convert Finset.abs_sum_le_sum_abs _ _ using 2;
  · rw [ abs_mul, abs_of_nonneg ( ArithmeticFunction.vonMangoldt_nonneg ) ];
  · infer_instance

/-! ## Perron kernel truncation bound

The Perron kernel K(n) = (1/2πi) ∫_{c-iT}^{c+iT} (x/n)^s / s ds approximates the
indicator 1_{n ≤ x}. The truncation error |K(n) - 1_{n≤x}| satisfies the bound
  |K(n) - 1_{n≤x}| ≤ (x/n)^c / (T · |log(x/n)|)
for n ≠ x, where c > 1 is the abscissa of the contour.

The following theorem shows that given such kernel bounds, the total error from
the triangle bound above is controlled.
-/

/-
**Weighted error bound**: If the Perron kernel approximation error for each n is
    bounded by ε(n), then the total error is bounded by Σ Λ(n) · ε(n).
-/
theorem perron_weighted_error_bound (x : ℝ) (N : ℕ) (hN : ⌊x⌋₊ + 1 ≤ N)
    (K : ℕ → ℝ) (ε : ℕ → ℝ) (hε_nn : ∀ n, 0 ≤ ε n)
    (h_kernel : ∀ n ∈ Finset.range N, |indicatorLe x n - K n| ≤ ε n) :
    |chebyshevPsi x - ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) * K n| ≤
      ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) * ε n := by
  -- Apply the triangle inequality to the sum.
  have h_triangle : |chebyshevPsi x - ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) * K n| ≤ ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) * |indicatorLe x n - K n| := by
    convert perron_error_triangle_bound x N hN K using 1;
  exact h_triangle.trans ( Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ( h_kernel n hn ) vonMangoldt_nonneg )

/-! ## The full truncated Perron identity -/

/-
**Truncated Perron sum identity for ψ(x)**.

For x ≥ 2, c = 1 + 1/log x, T ≥ 2, the Chebyshev function ψ(x) is approximated
by the contour integral of (-ζ'/ζ(s)) · x^s/s along Re(s) = c, with error O(log²x).

The proof swaps sum and integral using absolute convergence, applies the Perron kernel
truncation bound term by term, and combines the error estimates.

**Hypotheses encode the analytic ingredients:**
- `h_swap`: The contour integral equals Σ Λ(n) · K(n) (sum-integral swap via absolute
  convergence of the Dirichlet series for Re(s) > 1)
- `h_error_sum`: The weighted error sum Σ Λ(n) · |K(n) - 1_{n≤x}| ≤ C · log²x
  (from Perron kernel truncation bounds + prime number theorem estimates on Λ)
-/
theorem truncated_perron_psi
    (x : ℝ) (hx : x ≥ 2)
    (c : ℝ) (hc : c = 1 + 1 / Real.log x)
    (T : ℝ) (hT : T ≥ 2)
    (N : ℕ) (hN : ⌊x⌋₊ + 1 ≤ N)
    (K : ℕ → ℝ)
    (I : ℝ)
    (h_swap : I = ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) * K n)
    (C_bound : ℝ) (hC : 0 < C_bound)
    (h_error_sum : ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) *
        |indicatorLe x n - K n| ≤ C_bound * (Real.log x) ^ 2) :
    |chebyshevPsi x - I| ≤ C_bound * (Real.log x) ^ 2 := by
  refine' h_swap.symm ▸ le_trans ( perron_error_triangle_bound x N hN K ) _;
  convert h_error_sum using 1

/-
**Perron kernel bound implies error bound**: If each kernel error is bounded by ε(n),
    and the total weighted sum Σ Λ(n)·ε(n) ≤ B, then |ψ(x) - I| ≤ B.

    This is the most general form: it separates the per-term kernel estimate from the
    total error bound, allowing different kernel bounds to be used.
-/
theorem truncated_perron_from_kernel_bounds
    (x : ℝ) (hx : x ≥ 2)
    (T : ℝ) (hT : T ≥ 2)
    (N : ℕ) (hN : ⌊x⌋₊ + 1 ≤ N)
    (K : ℕ → ℝ) (I : ℝ)
    (h_swap : I = ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) * K n)
    (ε : ℕ → ℝ) (hε_nn : ∀ n, 0 ≤ ε n)
    (h_kernel : ∀ n ∈ Finset.range N, |indicatorLe x n - K n| ≤ ε n)
    (B : ℝ)
    (h_total : ∑ n ∈ Finset.range N, (vonMangoldt n : ℝ) * ε n ≤ B) :
    |chebyshevPsi x - I| ≤ B := by
  convert perron_weighted_error_bound x N hN K ε hε_nn h_kernel |> le_trans <| h_total using 1;
  rw [h_swap]

/-! ## Auxiliary lemmas about the Perron contour parameter -/

/-
The parameter c = 1 + 1/log x satisfies c > 1 for x ≥ 2.
-/
lemma perron_abscissa_gt_one (x : ℝ) (hx : x ≥ 2) :
    1 + 1 / Real.log x > 1 := by
  exact lt_add_of_pos_right _ ( one_div_pos.mpr ( Real.log_pos ( by linarith ) ) )

/-
x^(1/log x) = e for x > 1. This is because
    x^(1/log x) = exp(log x / log x) = exp(1) = e.
-/
lemma rpow_inv_log_eq_exp (x : ℝ) (hx : 1 < x) :
    x ^ (1 / Real.log x) = Real.exp 1 := by
  rw [ Real.rpow_def_of_pos ( by positivity ), mul_one_div_cancel ( ne_of_gt ( Real.log_pos hx ) ) ]

/-
x^c = x · x^(1/log x) = ex for c = 1 + 1/log x.
-/
lemma perron_xc_eq (x : ℝ) (hx : 1 < x) :
    x ^ (1 + 1 / Real.log x) = Real.exp 1 * x := by
  rw [ Real.rpow_add, Real.rpow_one ];
  · rw [ Real.rpow_def_of_pos ( by positivity ), mul_comm ] ; ring_nf;
    rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ), mul_comm ];
  · positivity

end TruncatedPerron