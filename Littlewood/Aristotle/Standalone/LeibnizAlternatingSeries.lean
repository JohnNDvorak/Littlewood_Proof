/-
Leibniz alternating series bound and block structure infrastructure.
SORRY COUNT: 0
Co-authored-by: Claude (Anthropic)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup
set_option relaxedAutoImplicit false
set_option autoImplicit false
noncomputable section
namespace LeibnizAlternatingSeries
open Finset Real

/-- Paired partial sum nonneg: each pair a(2i)-a(2i+1) ≥ 0 for antitone a. -/
theorem paired_partial_sum_nonneg (a : ℕ → ℝ) (ha : Antitone a) (n : ℕ) :
    0 ≤ ∑ i ∈ Finset.range n, (a (2 * i) - a (2 * i + 1)) :=
  Finset.sum_nonneg fun i _ => sub_nonneg.mpr (ha (by omega))

/-- Inductive upper bound: a(2m) ≤ a(0) - ∑_{i<m}(a(2i)-a(2i+1)). -/
theorem inductive_bound (a : ℕ → ℝ) (ha : Antitone a) (m : ℕ) :
    a (2 * m) ≤ a 0 - ∑ i ∈ Finset.range m, (a (2 * i) - a (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have h_anti : a (2 * j + 1) ≥ a (2 * (j + 1)) := ha (by omega)
    linarith

/-- Paired partial sum ≤ a(0): from inductive bound + a(2n) ≥ 0. -/
theorem paired_partial_sum_le_first (a : ℕ → ℝ) (ha : Antitone a)
    (ha_nn : ∀ k, 0 ≤ a k) (n : ℕ) :
    ∑ i ∈ Finset.range n, (a (2 * i) - a (2 * i + 1)) ≤ a 0 := by
  linarith [inductive_bound a ha n, ha_nn (2 * n)]

/-- Leibniz paired-sum bound: |∑_{i<n}(a(2i)-a(2i+1))| ≤ a(0). -/
theorem leibniz_paired_bound (a : ℕ → ℝ) (ha : Antitone a)
    (ha_nn : ∀ k, 0 ≤ a k) (n : ℕ) :
    |∑ i ∈ Finset.range n, (a (2 * i) - a (2 * i + 1))| ≤ a 0 := by
  rw [abs_le]; constructor
  · linarith [paired_partial_sum_nonneg a ha n,
              paired_partial_sum_le_first a ha ha_nn n]
  · exact paired_partial_sum_le_first a ha ha_nn n

/-- (-1)^(2k) = 1: even power of -1. -/
theorem neg_one_pow_even (k : ℕ) : (-1 : ℝ) ^ (2 * k) = 1 :=
  (even_two_mul k).neg_one_pow

/-- (-1)^(2k+1) = -1: odd power of -1. -/
theorem neg_one_pow_odd (k : ℕ) : (-1 : ℝ) ^ (2 * k + 1) = -1 :=
  Odd.neg_one_pow ⟨k, rfl⟩

/-- (-1)^k squared is 1. -/
theorem neg_one_pow_sq (k : ℕ) : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
  rw [← pow_add]; exact Even.neg_one_pow ⟨k, by omega⟩

/-- |(-1)^k · a| = |a|. -/
theorem abs_neg_one_pow_mul (k : ℕ) (a : ℝ) :
    |(-1 : ℝ) ^ k * a| = |a| := by
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- T^{1/2} = √T. -/
theorem rpow_half_eq_sqrt (T : ℝ) (_hT : 0 < T) :
    T ^ ((1 : ℝ) / 2) = Real.sqrt T :=
  (Real.sqrt_eq_rpow T).symm

/-- M ≤ M · T^{1/2} for T ≥ 1, M ≥ 0. -/
theorem le_mul_rpow_half (M T : ℝ) (hT : 1 ≤ T) (hM : 0 ≤ M) :
    M ≤ M * T ^ ((1 : ℝ) / 2) := by
  have hT_pos : 0 < T := by linarith
  have h1 : (1 : ℝ) ≤ T ^ ((1 : ℝ) / 2) := by
    rw [rpow_half_eq_sqrt T hT_pos, Real.one_le_sqrt]; exact hT
  nlinarith

/-- √T ≥ 1 for T ≥ 1. -/
theorem sqrt_ge_one (T : ℝ) (hT : 1 ≤ T) : 1 ≤ Real.sqrt T := by
  rw [Real.one_le_sqrt]; exact hT

/-- log T ≤ √T for T ≥ 16. -/
theorem log_le_sqrt_of_ge_sixteen (T : ℝ) (hT : 16 ≤ T) :
    Real.log T ≤ Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  rw [← Real.exp_le_exp]
  calc Real.exp (Real.log T) = T := Real.exp_log hT_pos
    _ = (Real.sqrt T) ^ 2 := (Real.sq_sqrt hT_pos.le).symm
    _ ≤ Real.exp (Real.sqrt T) := by
        have h4 : (4 : ℝ) ≤ Real.sqrt T := by
          calc (4 : ℝ) = Real.sqrt 16 := by
                rw [show (16 : ℝ) = 4 ^ 2 from by norm_num,
                    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
            _ ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
        have hst := Real.sum_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt T) 4
        simp [Finset.sum_range_succ, Nat.factorial] at hst
        nlinarith [sq_nonneg (Real.sqrt T - 4)]

/-- Telescoping sum: ∑_{i<n} (a(i)-a(i+1)) = a(0) - a(n). -/
theorem telescoping_sum (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (a i - a (i + 1)) = a 0 - a n := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- Telescoping bound: ∑_{i<n}(a(i)-a(i+1)) ≤ a(0) for nonneg a. -/
theorem telescoping_le_first (a : ℕ → ℝ) (ha_nn : ∀ k, 0 ≤ a k) (n : ℕ) :
    ∑ i ∈ Finset.range n, (a i - a (i + 1)) ≤ a 0 := by
  rw [telescoping_sum]; linarith [ha_nn n]

/-- Eventually logx > 0. -/
theorem log_eventually_pos : ∀ᶠ x in Filter.atTop, (0 : ℝ) < Real.log x := by
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  exact Real.log_pos (by linarith)

/-- Eventually √x/logx > 0. -/
theorem sqrt_div_log_eventually_pos : ∀ᶠ x in Filter.atTop,
    (0 : ℝ) < Real.sqrt x / Real.log x := by
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  exact div_pos (Real.sqrt_pos_of_pos (by linarith)) (Real.log_pos (by linarith))

/-- Division by logx preserves eventually-bounds. -/
theorem eventually_div_log_bound (f B : ℝ → ℝ)
    (h : ∀ᶠ x in Filter.atTop, |f x| ≤ B x) :
    ∀ᶠ x in Filter.atTop, |f x| / Real.log x ≤ B x / Real.log x := by
  filter_upwards [h, log_eventually_pos] with x hx hlx
  exact div_le_div_of_nonneg_right hx hlx.le

/-- |a/b| = |a|/b for b > 0. -/
theorem abs_div_of_pos (a b : ℝ) (hb : 0 < b) : |a / b| = |a| / b := by
  rw [abs_div, abs_of_pos hb]

-- ============================================================
-- Alternating series: (-1)^i sums via paired sums
-- ============================================================

/-- Convert alternating sum over 2n terms to paired differences. -/
theorem alternating_sum_even (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), (-1 : ℝ) ^ i * a i
      = ∑ j ∈ Finset.range n, (a (2 * j) - a (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ (f := fun j => a (2 * j) - a (2 * j + 1))]
    have h_idx : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [h_idx, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (-1 : ℝ) ^ (2 * m) = 1 := (even_two_mul m).neg_one_pow
    have h2 : (-1 : ℝ) ^ (2 * m + 1) = -1 := Odd.neg_one_pow ⟨m, rfl⟩
    rw [h1, h2, one_mul, neg_one_mul]; ring

/-- Alternating sum over 2n+1 terms = paired sum + last even term. -/
theorem alternating_sum_odd (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℝ) ^ i * a i
      = ∑ j ∈ Finset.range n, (a (2 * j) - a (2 * j + 1)) + a (2 * n) := by
  rw [Finset.sum_range_succ, (even_two_mul n).neg_one_pow, one_mul, alternating_sum_even]

/-- Alternating partial sum bound (even length): |∑_{i<2n} (-1)^i·a(i)| ≤ a(0). -/
theorem alternating_sum_even_bound (a : ℕ → ℝ) (ha : Antitone a)
    (ha_nn : ∀ k, 0 ≤ a k) (n : ℕ) :
    |∑ i ∈ Finset.range (2 * n), (-1 : ℝ) ^ i * a i| ≤ a 0 := by
  rw [alternating_sum_even]; exact leibniz_paired_bound a ha ha_nn n

/-- Alternating partial sum bound (odd length): |∑_{i<2n+1} (-1)^i·a(i)| ≤ a(0). -/
theorem alternating_sum_odd_bound (a : ℕ → ℝ) (ha : Antitone a)
    (ha_nn : ∀ k, 0 ≤ a k) (n : ℕ) :
    |∑ i ∈ Finset.range (2 * n + 1), (-1 : ℝ) ^ i * a i| ≤ a 0 := by
  rw [alternating_sum_odd, abs_le]; constructor
  · linarith [paired_partial_sum_nonneg a ha n, ha_nn (2 * n), ha_nn 0]
  · linarith [inductive_bound a ha n]

/-- Alternating partial sum bound (any length): |∑_{i<N} (-1)^i·a(i)| ≤ a(0). -/
theorem alternating_partial_sum_le_first (a : ℕ → ℝ) (ha : Antitone a)
    (ha_nn : ∀ k, 0 ≤ a k) (N : ℕ) :
    |∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * a i| ≤ a 0 := by
  rcases Nat.even_or_odd' N with ⟨n, rfl | rfl⟩
  · exact alternating_sum_even_bound a ha ha_nn n
  · exact alternating_sum_odd_bound a ha ha_nn n

-- ============================================================
-- Approximate Leibniz: perturbation of antitone by bounded error
-- ============================================================

/-- If |a(k) - M(k)| ≤ δ for all k, and M is antitone and nonneg, then
    |∑_{i<n} (-1)^i a(i)| ≤ M(0) + n·δ. -/
theorem leibniz_approx_antitone_nδ (a M : ℕ → ℝ) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hM_anti : Antitone M) (hM_nn : ∀ k, 0 ≤ M k)
    (h_approx : ∀ k, |a k - M k| ≤ δ) (n : ℕ) :
    |∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * a i| ≤ M 0 + n * δ := by
  have split : ∀ i, (-1 : ℝ) ^ i * a i = (-1 : ℝ) ^ i * M i + (-1 : ℝ) ^ i * (a i - M i) := by
    intro i; ring
  simp_rw [split, Finset.sum_add_distrib]
  calc |∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * M i +
        ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (a i - M i)|
      ≤ |∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * M i| +
        |∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (a i - M i)| := abs_add_le _ _
    _ ≤ M 0 + ∑ i ∈ Finset.range n, |(-1 : ℝ) ^ i * (a i - M i)| := by
        gcongr
        · exact alternating_partial_sum_le_first M hM_anti hM_nn n
        · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ M 0 + ∑ i ∈ Finset.range n, δ := by
        gcongr with i _; rw [abs_neg_one_pow_mul]; exact h_approx i
    _ = M 0 + n * δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

-- ============================================================
-- Block sum / integral auxiliary lemmas
-- ============================================================

/-- Sum of nonneg terms is monotone in the range. -/
theorem sum_range_mono_of_nonneg (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.range m, a i ≤ ∑ i ∈ Finset.range n, a i := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hmn
  · intros i _ _; exact ha i

/-- Tail of a sum: ∑_{i<n} - ∑_{i<m} = ∑ over the complement. -/
theorem sum_range_sub (a : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    ∑ i ∈ Finset.range n, a i - ∑ i ∈ Finset.range m, a i =
    ∑ i ∈ (Finset.range n).filter (· ≥ m), a i := by
  rw [← Finset.sum_sdiff_eq_sub (Finset.range_mono hmn)]
  congr 1; ext i
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_filter, ge_iff_le]
  omega

end LeibnizAlternatingSeries
