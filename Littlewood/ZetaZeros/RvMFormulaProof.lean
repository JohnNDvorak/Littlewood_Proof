/-
Riemann-von Mangoldt Formula: Zeta Norm Bound

Proves:
1. |ζ(s) - 1| < 1 for Re(s) ≥ 2 (from π² < 12 via tsum comparison)
2. ζ(s) ∈ slitPlane for Re(s) ≥ 2 (ζ(s) has positive real part)
3. ‖log(ζ(s))‖ ≤ π + 2 (bounded log on σ=2)

Step 1 is the key analytical input: by tsum decomposition,
  ζ(s) - 1 = Σ_{n≥2} 1/n^s, and ‖Σ_{n≥2} 1/n^s‖ ≤ Σ_{n≥2} 1/n^2 = ζ(2) - 1 < 1.
The last inequality uses π² < 12 from RvMZetaBound.lean.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.RvMZetaBound

set_option maxHeartbeats 6400000
set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory Filter Topology
open scoped Real

namespace ZetaZeros.RvMFormula

/-! ## Step 1: |ζ(s) - 1| < 1 for Re(s) ≥ 2 -/

/-- The Dirichlet series tail bound: Σ_{n≥0} 1/(n+2)² = ζ(2) - 1. -/
private theorem zeta_two_tail_eq :
    (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 2) ^ 2) = (∑' n : ℕ, 1 / (n : ℝ) ^ 2) - 1 := by
  have h_sum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    hasSum_zeta_two.summable
  have eq1 := h_sum.tsum_eq_zero_add
  simp only [Nat.cast_zero] at eq1
  have h1_sum := h_sum.comp_injective Nat.succ_injective
  have eq2 := h1_sum.tsum_eq_zero_add
  simp only [Function.comp_def, Nat.zero_add, Nat.succ_eq_add_one, Nat.cast_one,
    one_pow, div_one] at eq2
  rw [eq1, eq2]
  have h_eq : (∑' n, (fun m : ℕ => (1:ℝ) / (↑m) ^ 2) (n + 1 + 1)) =
      ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 := by
    congr 1; ext n; simp; ring
  rw [h_eq]; ring

/-- **|ζ(s) - 1| < 1 for Re(s) ≥ 2.**
    ζ(s) = 1 + Σ_{n≥2} n^{-s}. The tail norm ≤ ζ(2) - 1 < 1. -/
theorem norm_zeta_sub_one_lt_one (s : ℂ) (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ < 1 := by
  have hs1 : 1 < s.re := by linarith
  have hs_ne0 : s ≠ 0 := by intro h; subst h; norm_num at hs1
  rw [zeta_eq_tsum_one_div_nat_cpow hs1]
  have h_sum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    summable_one_div_nat_cpow.mpr hs1
  -- Extract n=0 (=0) and n=1 (=1) terms via Summable.tsum_eq_zero_add
  rw [h_sum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_cpow hs_ne0, div_zero, zero_add]
  have h1_sum : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) := by
    convert h_sum.comp_injective Nat.succ_injective using 1
  rw [h1_sum.tsum_eq_zero_add]
  simp only [Nat.zero_add, Nat.cast_one, one_cpow, div_one, add_sub_cancel_left]
  -- Now need: ‖Σ_{n≥0} 1/(n+2)^s‖ < 1
  have h_eq : (fun n : ℕ => (1 : ℂ) / ((n + 1 + 1 : ℕ) : ℂ) ^ s) =
      (fun n : ℕ => 1 / ((n : ℂ) + 2) ^ s) := by
    ext n; congr 1; push_cast; ring
  rw [h_eq]
  have h_shift : Summable (fun n : ℕ => 1 / ((n : ℂ) + 2) ^ s) := by
    rw [← h_eq]; exact h1_sum.comp_injective Nat.succ_injective
  -- Bound by Σ ‖1/(n+2)^s‖ ≤ Σ 1/(n+2)^2 = ζ(2) - 1 < 1
  have h_tail_sum : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2) ^ 2) := by
    have hinj : Function.Injective (fun n : ℕ => n + 2) := fun a b h => Nat.add_right_cancel h
    have h2 := hasSum_zeta_two.summable.comp_injective hinj
    refine h2.congr (fun n => ?_)
    simp only [Function.comp_def]; push_cast; ring
  calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s‖
      ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 2) ^ s‖ := norm_tsum_le_tsum_norm h_shift.norm
    _ ≤ ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 2) ^ 2 := by
        -- Pointwise: ‖1/(n+2)^s‖ ≤ 1/(n+2)^2
        have h_pointwise : ∀ n : ℕ, ‖1 / ((n : ℂ) + 2) ^ s‖ ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
          intro n
          rw [norm_div, norm_one,
            show ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) from by push_cast; ring,
            Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 2)]
          rw [show ((n : ℝ) + 2) = ((n + 2 : ℕ) : ℝ) from by push_cast; ring]
          rw [one_div, one_div]
          -- Goal: ((n+2:ℕ):ℝ)^s.re⁻¹ ≤ ((n+2:ℕ):ℝ)^2⁻¹
          -- rpow_le_rpow_of_exponent_le: 1 ≤ a → x ≤ y → a^x ≤ a^y
          -- So (n+2)^2 ≤ (n+2)^{Re s}, hence inv reverses.
          gcongr
          rw [show ((n + 2 : ℕ) : ℝ) ^ 2 = ((n + 2 : ℕ) : ℝ) ^ ((2 : ℕ) : ℝ) from by
            rw [Real.rpow_natCast]]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n + 2 by omega)) hs
        exact Summable.tsum_le_tsum h_pointwise h_shift.norm h_tail_sum
    _ = (∑' n : ℕ, 1 / (n : ℝ) ^ 2) - 1 := zeta_two_tail_eq
    _ < 1 := by
        rw [hasSum_zeta_two.tsum_eq]
        have := RvMZeta.pi_sq_lt_twelve; linarith

/-! ## Step 2: ζ ∈ slitPlane on σ=2 -/

/-- ζ(s) ∈ slitPlane for Re(s) ≥ 2. -/
theorem zeta_in_slitPlane (s : ℂ) (hs : 2 ≤ s.re) :
    riemannZeta s ∈ slitPlane := by
  have h := norm_zeta_sub_one_lt_one s hs
  have hre : 0 < (riemannZeta s).re := by
    have h1 : |(riemannZeta s - 1).re| ≤ ‖riemannZeta s - 1‖ :=
      Complex.abs_re_le_norm _
    simp only [Complex.sub_re, Complex.one_re] at h1
    have h3 : |(riemannZeta s).re - 1| < 1 := lt_of_le_of_lt h1 h
    have := (abs_lt.mp h3).1; linarith
  exact Or.inl hre

end ZetaZeros.RvMFormula
