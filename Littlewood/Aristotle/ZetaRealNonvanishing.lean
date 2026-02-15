/-
Nonvanishing of the Riemann zeta function on the real interval (0, 1).

This is needed for the Landau non-negative Dirichlet integral argument:
the formula sC/(s-α) + σs/(s-1) + σζ'/ζ(s) must be analytic on (α, 1) ⊂ ℝ,
which requires ζ(s) ≠ 0 there.

## Main Result

* `riemannZeta_ne_zero_of_real_mem_Ioo` : ζ(↑x) ≠ 0 for x ∈ (0, 1)

## Proof Strategy

The proof uses the Dirichlet eta function η(s) = Σ (-1)^{n+1}/n^s:
1. η(s) = (1 - 2^{1-s}) ζ(s) for s ≠ 1 (algebraic identity)
2. η(s) > 0 for real s > 0 (alternating series with decreasing terms)
3. 1 - 2^{1-s} < 0 for s ∈ (0, 1) (since 2^{1-s} > 1)
4. Therefore ζ(s) = η(s) / (1 - 2^{1-s}) < 0, so ζ(s) ≠ 0.

SORRY COUNT: 1 (paired eta sum identity via analytic continuation)

REFERENCES:
  - Titchmarsh, "The Theory of the Riemann Zeta-Function", §1.4
  - Hardy-Wright, "An Introduction to the Theory of Numbers", §22.2

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Uniqueness
import Littlewood.Aristotle.HalfPlaneConnected

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.ZetaRealNonvanishing

open Complex Real Filter Topology Metric Set

/-! ## Helper: sign of 1 - 2^{1-x}

For x ∈ (0,1): 1-x > 0, so 2^{1-x} > 2^0 = 1, hence 1 - 2^{1-x} < 0. -/

private theorem one_sub_two_pow_neg (x : ℝ) (_hx0 : 0 < x) (hx1 : x < 1) :
    1 - (2 : ℝ) ^ (1 - x) < 0 := by
  have h1 := rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (show (0 : ℝ) < 1 - x by linarith)
  rw [rpow_zero] at h1
  linarith

/-! ## Paired eta function term positivity

Each term (2k+1)^{-x} - (2k+2)^{-x} is positive for real x > 0,
since t ↦ t^{-x} is strictly decreasing for x > 0. -/

private theorem paired_term_pos (x : ℝ) (hx : 0 < x) (k : ℕ) :
    0 < (2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 2) ^ (-x) := by
  have hk1 : (0 : ℝ) < 2 * k + 1 := by positivity
  have hk2 : (0 : ℝ) < 2 * k + 2 := by positivity
  rw [rpow_neg hk1.le, rpow_neg hk2.le]
  have h1 : 0 < (2 * (k : ℝ) + 1) ^ x := rpow_pos_of_pos hk1 x
  have hlt : (2 * (k : ℝ) + 1) ^ x < (2 * (k : ℝ) + 2) ^ x :=
    rpow_lt_rpow hk1.le (by linarith) hx
  linarith [(inv_lt_inv₀ (rpow_pos_of_pos hk2 x) h1).mpr hlt]

/-! ## Summability of the paired eta series

**Strategy**: Prove partial sums ∑_{k<N} f(k) ≤ 1 by induction,
using the stronger inductive hypothesis:
  ∑_{k<N} f(k) + (2N)^{-x} ≤ 1  for N ≥ 1
Then apply `summable_of_sum_range_le`. -/

private theorem paired_partial_sum_aux (x : ℝ) (hx : 0 < x) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ((2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 2) ^ (-x)) +
      (2 * (↑n + 1 : ℝ)) ^ (-x) ≤ 1 := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one]
    simp only [Nat.cast_zero]
    -- Goal: (2*0+1)^(-x) - (2*0+2)^(-x) + (2*(0+1))^(-x) ≤ 1
    have h1 : (2 * (0 : ℝ) + 2) ^ (-x) = (2 * ((0 : ℝ) + 1)) ^ (-x) := by
      congr 1; ring
    rw [h1, sub_add_cancel]
    have h2 : (2 * (0 : ℝ) + 1) = 1 := by ring
    rw [h2, one_rpow]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    -- Cancel: f(m+1) + (2(m+2))^{-x} = (2m+3)^{-x}
    have h_eq : (2 * (↑(m + 1) : ℝ) + 2) ^ (-x) = (2 * (↑(m + 1) + 1 : ℝ)) ^ (-x) := by
      congr 1; push_cast; ring
    -- After cancel: sum_{k<m+1} f(k) + (2(m+1)+1)^{-x}
    -- Monotonicity: (2(m+1)+1)^{-x} ≤ (2(m+1))^{-x}
    have hlo : (0 : ℝ) < 2 * (↑m + 1 : ℝ) := by positivity
    have hhi : (0 : ℝ) < 2 * (↑(m + 1) : ℝ) + 1 := by positivity
    have hlt : 2 * (↑m + 1 : ℝ) < 2 * (↑(m + 1) : ℝ) + 1 := by push_cast; linarith
    have h_mono : (2 * (↑(m + 1) : ℝ) + 1) ^ (-x) ≤ (2 * (↑m + 1 : ℝ)) ^ (-x) := by
      rw [rpow_neg hhi.le, rpow_neg hlo.le]
      exact le_of_lt ((inv_lt_inv₀ (rpow_pos_of_pos hhi x)
        (rpow_pos_of_pos hlo x)).mpr (rpow_lt_rpow hlo.le hlt hx))
    linarith [h_eq, h_mono]

private theorem paired_partial_sum_le_one (x : ℝ) (hx : 0 < x) (N : ℕ) :
    ∑ k ∈ Finset.range N,
      ((2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 2) ^ (-x)) ≤ 1 := by
  rcases N with _ | n
  · simp
  · have := paired_partial_sum_aux x hx n
    have h_tail : (0 : ℝ) ≤ (2 * (↑n + 1 : ℝ)) ^ (-x) :=
      rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * (↑n + 1 : ℝ)) (-x)
    linarith

private theorem paired_sum_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun k : ℕ => (2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 2) ^ (-x)) :=
  summable_of_sum_range_le
    (fun k => le_of_lt (paired_term_pos x hx k))
    (paired_partial_sum_le_one x hx)

/-! ## Complex paired eta sum — analyticity on {Re > 0}

The complex paired eta sum F(s) = ∑' k, [(2k+1)^{-s} - (2k+2)^{-s}] is analytic
on {Re(s) > 0}. Proof via norm bound + `differentiableOn_tsum_of_summable_norm`.

The MVT gives ‖(↑a)^{-s} - (↑(a+1))^{-s}‖ ≤ ‖s‖·a^{-(Re(s)+1)}, summable for Re(s) > 0. -/

/-- Each complex paired term is differentiable at every s with Re(s) > 0. -/
private theorem cpaired_differentiableAt (k : ℕ) (s : ℂ) (_hs : s.re > 0) :
    DifferentiableAt ℂ
      (fun w => (↑(2 * (k : ℝ) + 1) : ℂ) ^ (-w) - (↑(2 * (k : ℝ) + 2) : ℂ) ^ (-w)) s := by
  have h1 : (↑(2 * (k : ℝ) + 1) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have h2 : (↑(2 * (k : ℝ) + 2) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  exact (differentiableAt_id.neg.const_cpow (Or.inl h1)).sub
    (differentiableAt_id.neg.const_cpow (Or.inl h2))

/-- Norm bound for complex paired terms via MVT:
‖(↑(2k+1))^{-s} - (↑(2k+2))^{-s}‖ ≤ ‖s‖ · (2k+1)^{-(s.re+1)} -/
private theorem cpaired_norm_le (k : ℕ) (s : ℂ) (hs : s.re > 0) :
    ‖(↑(2 * (k : ℝ) + 1) : ℂ) ^ (-s) - (↑(2 * (k : ℝ) + 2) : ℂ) ^ (-s)‖ ≤
      ‖s‖ * (2 * (k : ℝ) + 1) ^ (-(s.re + 1)) := by
  set a := (2 * (k : ℝ) + 1)
  set b := (2 * (k : ℝ) + 2)
  have ha : 0 < a := by positivity
  have hab : a ≤ b := by linarith
  have hba : b - a = 1 := by ring
  have hs_ne : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hns_ne : (-s) ≠ 0 := neg_ne_zero.mpr hs_ne
  -- f(t) = (↑t)^{-s} is differentiable at each t ∈ [a,b] (each t > 0)
  have hf_ptwise : ∀ t ∈ Icc a b, DifferentiableAt ℝ (fun t : ℝ => (↑t : ℂ) ^ (-s)) t := by
    intro t ht
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le ha ht.1)) hns_ne).differentiableAt
  -- Derivative bound: ‖f'(t)‖ ≤ ‖s‖ · a^{-(Re(s)+1)}
  have hbound : ∀ t ∈ Icc a b, ‖deriv (fun t : ℝ => (↑t : ℂ) ^ (-s)) t‖ ≤
      ‖s‖ * a ^ (-(s.re + 1)) := by
    intro t ⟨hat, _⟩
    have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le ha hat
    rw [(hasDerivAt_ofReal_cpow_const ht_pos.ne' hns_ne).deriv, norm_mul,
      norm_cpow_eq_rpow_re_of_pos ht_pos]
    show ‖-s‖ * t ^ (-s - 1).re ≤ ‖s‖ * a ^ (-(s.re + 1))
    rw [norm_neg, show (-s - 1).re = -(s.re + 1) by simp [sub_re, neg_re, one_re]; ring]
    -- t^{-(σ+1)} ≤ a^{-(σ+1)} since a ≤ t and -(σ+1) ≤ 0
    exact mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_nonpos ha hat (by linarith)) (norm_nonneg _)
  -- Apply MVT (convex version uses deriv, not derivWithin)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hf_ptwise hbound (convex_Icc a b)
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  rw [show ‖b - a‖ = (1 : ℝ) from by rw [Real.norm_eq_abs, hba, abs_one], mul_one] at hmvt
  rwa [norm_sub_rev] at hmvt

/-- The complex paired eta sum is AnalyticOnNhd ℂ on {Re > 0}. -/
private theorem cpaired_sum_analyticOnNhd :
    AnalyticOnNhd ℂ
      (fun s => ∑' k : ℕ, ((↑(2 * (k : ℝ) + 1) : ℂ) ^ (-s) - (↑(2 * (k : ℝ) + 2) : ℂ) ^ (-s)))
      {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀_re : (0 : ℝ) < s₀.re := hs₀
  set r := s₀.re / 2 with hr_def
  set σ := s₀.re / 2 with hσ_def
  have hr : 0 < r := by linarith
  -- Ball inclusion: ball s₀ r ⊆ {Re > 0}
  have hball_sub : ball s₀ r ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      rw [← Complex.sub_re]; exact abs_re_le_norm _
    have h2 := mem_ball_iff_norm.mp hs
    have h3 := (abs_le.mp (h1.trans h2.le)).1
    simp only [mem_setOf_eq]; linarith
  -- Re(s) ≥ σ on the ball
  have hball_re : ∀ s ∈ ball s₀ r, σ ≤ s.re := by
    intro s hs
    have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      rw [← Complex.sub_re]; exact abs_re_le_norm _
    have h2 := mem_ball_iff_norm.mp hs
    have h3 := (abs_le.mp (h1.trans h2.le)).1
    linarith
  -- ‖s‖ ≤ ‖s₀‖ + r on the ball
  have hball_norm : ∀ s ∈ ball s₀ r, ‖s‖ ≤ ‖s₀‖ + r := by
    intro s hs
    calc ‖s‖ = ‖s₀ + (s - s₀)‖ := by ring_nf
      _ ≤ ‖s₀‖ + ‖s - s₀‖ := norm_add_le _ _
      _ ≤ ‖s₀‖ + r := by linarith [mem_ball_iff_norm.mp hs]
  set C := ‖s₀‖ + r
  -- Summable bound: (2k+1)^{-(σ+1)} ≤ (k+1)^{-(σ+1)} since 2k+1 ≥ k+1
  have hk_pos : ∀ k : ℕ, (0 : ℝ) ≤ 2 * (k : ℝ) + 1 :=
    fun k => by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hinj : Function.Injective (fun (k : ℕ) => (2 * k + 1 : ℕ)) := by
    intro a b h; simp only at h; omega
  have hu : Summable (fun k : ℕ => C * (2 * (k : ℝ) + 1) ^ (-(σ + 1))) := by
    have hσ1 : 1 < σ + 1 := by linarith
    have hbase : Summable (fun k : ℕ => (2 * (k : ℝ) + 1) ^ (-(σ + 1))) := by
      refine ((summable_one_div_nat_rpow.mpr hσ1).comp_injective hinj).congr fun k => ?_
      simp only [Function.comp_apply, one_div]
      rw [show ((2 * ↑k + 1 : ℕ) : ℝ) = 2 * (↑k : ℝ) + 1 from by push_cast; ring,
        ← rpow_neg (hk_pos k)]
    exact hbase.hasSum.mul_left C |>.summable
  -- Each term differentiable on ball
  have hf_diff : ∀ k : ℕ, DifferentiableOn ℂ
      (fun s => (↑(2 * (k : ℝ) + 1) : ℂ) ^ (-s) - (↑(2 * (k : ℝ) + 2) : ℂ) ^ (-s))
      (ball s₀ r) :=
    fun k s hs => (cpaired_differentiableAt k s (hball_sub hs)).differentiableWithinAt
  -- Norm bound on ball
  have hF_le : ∀ k : ℕ, ∀ s ∈ ball s₀ r,
      ‖(↑(2 * (k : ℝ) + 1) : ℂ) ^ (-s) - (↑(2 * (k : ℝ) + 2) : ℂ) ^ (-s)‖ ≤
        C * (2 * (k : ℝ) + 1) ^ (-(σ + 1)) := by
    intro k s hs
    calc _ ≤ ‖s‖ * (2 * (k : ℝ) + 1) ^ (-(s.re + 1)) := cpaired_norm_le k s (hball_sub hs)
      _ ≤ C * (2 * (k : ℝ) + 1) ^ (-(σ + 1)) :=
          mul_le_mul (hball_norm s hs)
            (rpow_le_rpow_of_exponent_le
              (show (1 : ℝ) ≤ 2 * (k : ℝ) + 1 from by
                have := Nat.cast_nonneg (α := ℝ) k; linarith)
              (show -(s.re + 1) ≤ -(σ + 1) from by linarith [hball_re s hs]))
            (rpow_nonneg (hk_pos k) _)
            (show (0 : ℝ) ≤ C from by linarith [norm_nonneg s₀])
  exact (differentiableOn_tsum_of_summable_norm hu hf_diff isOpen_ball hF_le).analyticAt
    (isOpen_ball.mem_nhds (mem_ball_self hr))

/-! ## Algebraic identity on {Re > 1}

For Re(s) > 1: ∑' k, [(2k+1)^{-s} - (2k+2)^{-s}] = (1-2^{1-s})·ζ(s).
Uses parity split of the zeta Dirichlet series. -/

private theorem cpaired_eq_eta_re_gt_one (s : ℂ) (hs : 1 < s.re) :
    ∑' k : ℕ, ((↑(2 * (k : ℝ) + 1) : ℂ) ^ (-s) - (↑(2 * (k : ℝ) + 2) : ℂ) ^ (-s)) =
      (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := by
  -- ζ(s) = ∑' n, (n+1)^{-s}
  have hζ := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have h_term : ∀ n : ℕ, (1 : ℂ) / (↑n + 1) ^ s = (↑n + 1 : ℂ) ^ (-s) := by
    intro n; rw [one_div, cpow_neg]
  simp_rw [h_term] at hζ
  have hζ_summable : Summable (fun n : ℕ => (↑n + 1 : ℂ) ^ (-s)) :=
    ((summable_one_div_nat_cpow.mpr hs).comp_injective
      (fun (a b : ℕ) (h : a + 1 = b + 1) => Nat.succ.inj h)).congr fun n => by
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, h_term]
  set f : ℕ → ℂ := fun n => (↑n + 1 : ℂ) ^ (-s)
  -- Even/odd index identification
  have hf_even : ∀ k : ℕ, f (2 * k) = (↑(2 * (k : ℝ) + 1) : ℂ) ^ (-s) := by
    intro k; simp only [f]; congr 1; push_cast; ring
  have hf_odd : ∀ k : ℕ, f (2 * k + 1) = (↑(2 * (k : ℝ) + 2) : ℂ) ^ (-s) := by
    intro k; simp only [f]; congr 1; push_cast; ring
  have he : Summable (fun k => f (2 * k)) := hζ_summable.comp_injective
    (mul_right_injective₀ (two_ne_zero' ℕ))
  have ho : Summable (fun k => f (2 * k + 1)) := hζ_summable.comp_injective
    ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  -- Rewrite paired terms as f(2k) - f(2k+1)
  have h_paired_eq : ∀ k : ℕ,
      (↑(2 * (k : ℝ) + 1) : ℂ) ^ (-s) - (↑(2 * (k : ℝ) + 2) : ℂ) ^ (-s) =
        f (2 * k) - f (2 * k + 1) := by
    intro k; rw [hf_even, hf_odd]
  simp_rw [h_paired_eq]
  -- HasSum.sub to split the tsum of differences
  rw [(he.hasSum.sub ho.hasSum).tsum_eq]
  -- Parity split: ∑ f(2k) + ∑ f(2k+1) = ζ(s)
  have h_split := tsum_even_add_odd he ho
  rw [← hζ] at h_split
  -- Factor odd sum: ∑' k, f(2k+1) = 2^{-s} · ζ(s)
  have h_odd_factor : ∑' k : ℕ, f (2 * k + 1) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    have h_rewrite : ∀ k : ℕ, f (2 * k + 1) = (2 : ℂ) ^ (-s) * ((↑k + 1 : ℂ) ^ (-s)) := by
      intro k
      rw [hf_odd]
      rw [show (↑(2 * (k : ℝ) + 2) : ℂ) = (↑(2 : ℝ)) * (↑((k : ℝ) + 1)) from by
        push_cast; ring]
      rw [mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
      push_cast; ring
    simp_rw [h_rewrite]; rw [tsum_mul_left, ← hζ]
  -- Even sum from parity: ∑ f(2k) = ζ - 2^{-s}·ζ
  have h_even_sum : ∑' k : ℕ, f (2 * k) =
      riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [h_odd_factor] at h_split; exact eq_sub_of_add_eq h_split
  rw [h_even_sum, h_odd_factor]
  -- Goal: (ζ - 2^{-s}·ζ) - 2^{-s}·ζ = (1 - 2^{1-s})·ζ
  have h2s : (2 : ℂ) ^ ((1 : ℂ) - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = -s + 1 from by ring]
    rw [cpow_add (-s) 1 (by norm_num : (2 : ℂ) ≠ 0), cpow_one, mul_comm]
  rw [h2s]; ring

/-! ## Identity principle: extend to {Re > 0} \ {1} -/

private theorem cpaired_eq_eta (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ∑' k : ℕ, ((↑(2 * (k : ℝ) + 1) : ℂ) ^ (-s) - (↑(2 * (k : ℝ) + 2) : ℂ) ^ (-s)) =
      (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := by
  set U := {w : ℂ | 0 < w.re} \ {(1 : ℂ)}
  have hF : AnalyticOnNhd ℂ
      (fun w => ∑' k : ℕ, ((↑(2*(k:ℝ)+1) : ℂ)^(-w) - (↑(2*(k:ℝ)+2) : ℂ)^(-w))) U :=
    cpaired_sum_analyticOnNhd.mono diff_subset
  -- RHS analyticity: (1 - 2^{1-w}) * ζ(w) is analytic on {Re > 0} \ {1}
  have h_zeta_analytic : AnalyticOnNhd ℂ riemannZeta {t | t ≠ 1} :=
    DifferentiableOn.analyticOnNhd
      (fun t (ht : t ≠ 1) => (differentiableAt_riemannZeta ht).differentiableWithinAt)
      isOpen_ne
  have h_factor_analytic : AnalyticOnNhd ℂ (fun w => 1 - (2 : ℂ) ^ ((1 : ℂ) - w)) univ :=
    DifferentiableOn.analyticOnNhd (fun w _ =>
      ((differentiableAt_const (1 : ℂ)).sub
        (((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow
          (Or.inl (by norm_num : (2:ℂ) ≠ 0)))).differentiableWithinAt) isOpen_univ
  have hG : AnalyticOnNhd ℂ
      (fun w => (1 - (2 : ℂ) ^ ((1 : ℂ) - w)) * riemannZeta w) U := by
    intro w ⟨_, hw_ne⟩
    simp only [mem_singleton_iff] at hw_ne
    exact (h_factor_analytic w (mem_univ w)).mul (h_zeta_analytic w hw_ne)
  have hU_pc : IsPreconnected U :=
    HalfPlaneConnected.halfPlane_diff_singleton_isPreconnected 0 1
  set z₀ : ℂ := 2
  have hz₀ : z₀ ∈ U :=
    ⟨by show (0 : ℝ) < z₀.re; simp [z₀],
     by simp only [mem_singleton_iff, z₀]; norm_num⟩
  have hev : (fun w => ∑' k : ℕ, ((↑(2*(k:ℝ)+1) : ℂ)^(-w) - (↑(2*(k:ℝ)+2) : ℂ)^(-w))) =ᶠ[𝓝 z₀]
      (fun w => (1 - (2:ℂ)^((1:ℂ) - w)) * riemannZeta w) :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{w : ℂ | 1 < w.re},
       (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
         (show (1 : ℝ) < z₀.re by simp [z₀]),
       fun w hw => cpaired_eq_eta_re_gt_one w hw⟩
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hU_pc hz₀ hev ⟨hs, by simpa using hs1⟩

/-! ## Paired eta sum identity — bridge to real -/

private theorem paired_sum_identity (x : ℝ) (hx0 : 0 < x) (hx1 : x ≠ 1) :
    ∑' k : ℕ, ((2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 2) ^ (-x)) =
      (1 - (2 : ℝ) ^ (1 - x)) * (riemannZeta (↑x : ℂ)).re := by
  have hx_ne : (↑x : ℂ) ≠ 1 := by exact_mod_cast hx1
  have hx_re : (↑x : ℂ).re > 0 := by simp; exact hx0
  have h_cpaired := cpaired_eq_eta (↑x) hx_re hx_ne
  -- Bridge (↑a)^{-(↑x)} = ↑(a^{-x}) for a > 0
  have h_bridge : ∀ (a : ℝ), 0 < a → (↑a : ℂ) ^ (-(↑x : ℂ)) = ↑(a ^ (-x)) := by
    intro a ha
    rw [show -(↑x : ℂ) = (↑(-x) : ℂ) from by push_cast; ring]
    exact (ofReal_cpow ha.le (-x)).symm
  -- Each paired term is real
  have h_term : ∀ k : ℕ,
      (↑(2*(k:ℝ)+1) : ℂ)^(-(↑x:ℂ)) - (↑(2*(k:ℝ)+2) : ℂ)^(-(↑x:ℂ)) =
        ↑((2*(k:ℝ)+1)^(-x) - (2*(k:ℝ)+2)^(-x)) := by
    intro k
    rw [h_bridge _ (by positivity), h_bridge _ (by positivity)]
    push_cast; ring
  simp_rw [h_term] at h_cpaired
  -- Bridge (1-2^{1-s}) to real
  have h2 : (2 : ℂ) ^ ((1 : ℂ) - ↑x) = ↑((2 : ℝ) ^ (1 - x)) := by
    rw [show (1 : ℂ) - (↑x : ℂ) = (↑((1 : ℝ) - x) : ℂ) from by push_cast; ring]
    exact (ofReal_cpow (by norm_num : (0:ℝ) ≤ 2) (1 - x)).symm
  rw [h2] at h_cpaired
  -- h_cpaired : ∑' k, ↑(f k) = (1 - ↑(2^{1-x})) * ζ(↑x)
  -- Rewrite 1 - ↑(2^{1-x}) as ↑(1 - 2^{1-x})
  rw [show (1 : ℂ) - ↑((2 : ℝ) ^ (1 - x)) = (↑((1 : ℝ) - (2 : ℝ) ^ (1 - x)) : ℂ) from by
    push_cast; ring] at h_cpaired
  -- Use ofReal_tsum to go from ∑' k, ↑(f k) to ↑(∑' k, f k)
  rw [← ofReal_tsum] at h_cpaired
  -- h_cpaired : ↑(∑' k, f k) = ↑(1-2^{1-x}) * ζ(↑x)
  -- Take .re of both sides
  have h_re := congr_arg Complex.re h_cpaired
  simp only [ofReal_re] at h_re
  rwa [re_ofReal_mul] at h_re

/-! ## Main result: ζ(x) < 0 for x ∈ (0, 1)

From the eta identity: η(x) = (1-2^{1-x})·ζ(x).
Since η(x) > 0 and (1-2^{1-x}) < 0, we get ζ(x) < 0. -/

private theorem zeta_neg_on_unit_interval (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (riemannZeta (↑x : ℂ)).re < 0 := by
  have hsum := paired_sum_summable x hx0
  have heq := paired_sum_identity x hx0 (ne_of_lt hx1)
  have h_factor_neg := one_sub_two_pow_neg x hx0 hx1
  -- Paired sum is positive: each term positive + summable
  have h_term_pos : ∀ k : ℕ, 0 < (2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 2) ^ (-x) :=
    paired_term_pos x hx0
  have h_pos : (0 : ℝ) < ∑' (k : ℕ), ((2 * (↑k : ℝ) + 1) ^ (-x) - (2 * (↑k : ℝ) + 2) ^ (-x)) :=
    hsum.tsum_pos (fun k => le_of_lt (h_term_pos k)) 0 (h_term_pos 0)
  -- positive = (negative) · ζ(x).re implies ζ(x).re < 0
  by_contra h_nn
  push_neg at h_nn
  linarith [mul_nonpos_of_nonpos_of_nonneg (le_of_lt h_factor_neg) h_nn]

/-! ## Public API -/

/-- The Riemann zeta function does not vanish on the real interval (0, 1).
This is equivalent to saying ζ has no real zeros between 0 and 1. -/
theorem riemannZeta_ne_zero_of_real_mem_Ioo (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (↑x : ℂ) ≠ 0 := by
  intro h
  have := zeta_neg_on_unit_interval x hx0 hx1
  rw [h] at this
  simp at this

/-- Combined with Mathlib's `riemannZeta_ne_zero_of_one_le_re`: ζ(s) ≠ 0
for all real s > 0 (including the junk value at s = 1). -/
theorem riemannZeta_ne_zero_of_real_pos (x : ℝ) (hx : 0 < x) :
    riemannZeta (↑x : ℂ) ≠ 0 := by
  by_cases h1 : x < 1
  · exact riemannZeta_ne_zero_of_real_mem_Ioo x hx h1
  · push_neg at h1
    exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith)

/-- ζ'/ζ is analytic at any real point s ∈ (α, 1) with 0 < α. -/
theorem zeta_logDeriv_analyticAt_real (x : ℝ) (hx0 : 0 < x) (hx_ne : (↑x : ℂ) ≠ 1) :
    AnalyticAt ℂ (fun s => deriv riemannZeta s / riemannZeta s) (↑x : ℂ) := by
  have h_ne := riemannZeta_ne_zero_of_real_pos x hx0
  -- ζ is differentiable on the open set {s | s ≠ 1}
  have h_diffOn : DifferentiableOn ℂ riemannZeta {s | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  -- ζ is analytic on {s | s ≠ 1} via Cauchy integral formula
  have h_analytic := h_diffOn.analyticOnNhd isOpen_ne
  have h_at : AnalyticAt ℂ riemannZeta (↑x : ℂ) := h_analytic (↑x) hx_ne
  exact h_at.deriv.div h_at h_ne

end Aristotle.ZetaRealNonvanishing
