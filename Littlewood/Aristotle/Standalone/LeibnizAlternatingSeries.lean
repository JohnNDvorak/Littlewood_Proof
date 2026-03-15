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

end LeibnizAlternatingSeries
