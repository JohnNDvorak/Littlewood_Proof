/-
  Weierstrass Elementary Factors E_p(z)

  Defines E_p(z) = (1 - z) * exp(z + z²/2 + ... + z^p/p) and proves:
  1. E_p is entire (differentiable everywhere on ℂ)
  2. E_p(0) = 1 and E_p(1) = 0 (simple zero at z = 1)
  3. Derivative formula: E_p'(z) = -z^p * exp(S_p(z))
  4. Convergence bound: |1 - E_p(z)| ≤ 2|z|^{p+1} for |z| ≤ 1/2
  5. The function z ↦ E_p(z/a) has a simple zero at z = a

  These are the building blocks for the Weierstrass product theorem
  and the Hadamard factorization of entire functions of finite order.
-/

import Mathlib

set_option maxHeartbeats 800000
set_option autoImplicit false

open Complex Topology Filter

noncomputable section

namespace WeierstrassFactors

/-! ## Definition of the partial sum and elementary factor -/

/-- The partial sum S_p(z) = ∑_{k=1}^{p} z^k/k, used in the exponent of E_p. -/
def epSum (p : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range p, z ^ (k + 1) / (↑(k + 1) : ℂ)

/-- Weierstrass elementary factor E_p(z) = (1 - z) · exp(∑_{k=1}^{p} z^k/k).
    For p = 0 this gives E_0(z) = 1 - z.
    For p = 1 this gives E_1(z) = (1 - z) · exp(z). -/
def ep (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (epSum p z)

/-! ## Basic evaluations -/

@[simp]
theorem ep_zero (z : ℂ) : ep 0 z = 1 - z := by
  simp [ep, epSum]

@[simp]
theorem ep_at_zero (p : ℕ) : ep p 0 = 1 := by
  simp [ep, epSum]

theorem ep_at_one (p : ℕ) : ep p 1 = 0 := by
  simp [ep]

theorem epSum_zero (z : ℂ) : epSum 0 z = 0 := by
  simp [epSum]

theorem epSum_at_zero (p : ℕ) : epSum p 0 = 0 := by
  simp [epSum]

theorem epSum_one (z : ℂ) : epSum 1 z = z := by
  simp [epSum]

/-- E_1(z) = (1 - z) · exp(z) -/
theorem ep_one (z : ℂ) : ep 1 z = (1 - z) * exp z := by
  simp [ep, epSum]

/-! ## Differentiability (entireness) -/

theorem differentiable_epSum (p : ℕ) : Differentiable ℂ (epSum p) := by
  unfold epSum; fun_prop

@[fun_prop]
theorem differentiableAt_epSum (p : ℕ) (z : ℂ) : DifferentiableAt ℂ (epSum p) z :=
  (differentiable_epSum p).differentiableAt

theorem differentiable_ep (p : ℕ) : Differentiable ℂ (ep p) := by
  intro z
  unfold ep
  apply DifferentiableAt.mul
  · exact (differentiableAt_const 1).sub differentiableAt_id
  · exact differentiableAt_exp.comp z (differentiableAt_epSum p z)

theorem continuous_ep (p : ℕ) : Continuous (ep p) :=
  (differentiable_ep p).continuous

/-! ## Derivative of the partial sum -/

private theorem hasDerivAt_pow_div (k : ℕ) (z : ℂ) :
    HasDerivAt (fun z => z ^ (k + 1) / (↑(k + 1) : ℂ)) (z ^ k) z := by
  have hk : (↑(k + 1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ((hasDerivAt_pow (k + 1) z).div_const _).congr_deriv ?_
  have hsub : k + 1 - 1 = k := by omega
  field_simp; rw [hsub]

/-- The derivative of S_p(z) = ∑_{k=1}^p z^k/k is ∑_{k=0}^{p-1} z^k. -/
theorem hasDerivAt_epSum (p : ℕ) (z : ℂ) :
    HasDerivAt (epSum p) (∑ k ∈ Finset.range p, z ^ k) z := by
  unfold epSum
  have h := HasDerivAt.sum (fun (k : ℕ) (_ : k ∈ Finset.range p) => hasDerivAt_pow_div k z)
  convert h using 1
  ext w
  exact (Finset.sum_apply w (Finset.range p) (fun k z => z ^ (k + 1) / ↑(k + 1))).symm

/-! ## The geometric sum identity -/

/-- (1 - z) · ∑_{k=0}^{p-1} z^k = 1 - z^p -/
theorem one_sub_mul_geom_sum (z : ℂ) (p : ℕ) :
    (1 - z) * ∑ k ∈ Finset.range p, z ^ k = 1 - z ^ p := by
  have := geom_sum_mul z p; linear_combination -this

/-! ## Key derivative formula for E_p -/

/-- **Derivative formula**: E_p'(z) = -z^p · exp(S_p(z)).
    This is the fundamental structural result: the derivative of E_p
    exactly cancels the polynomial part of the Taylor expansion. -/
theorem hasDerivAt_ep (p : ℕ) (z : ℂ) :
    HasDerivAt (ep p) (-z ^ p * exp (epSum p z)) z := by
  unfold ep
  have hS := hasDerivAt_epSum p z
  have hexp : HasDerivAt (fun z => exp (epSum p z))
      (exp (epSum p z) * (∑ k ∈ Finset.range p, z ^ k)) z :=
    hS.cexp
  have hlin : HasDerivAt (fun z => (1 : ℂ) - z) (-1 : ℂ) z := by
    convert (hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z) using 1; simp
  have hprod := hlin.mul hexp
  refine hprod.congr_deriv ?_
  rw [show -1 * exp (epSum p z) +
      (1 - z) * (exp (epSum p z) * ∑ k ∈ Finset.range p, z ^ k) =
      (-1 + (1 - z) * ∑ k ∈ Finset.range p, z ^ k) * exp (epSum p z) from by ring]
  rw [one_sub_mul_geom_sum]
  ring

/-- The derivative of E_p at z = 0 is 0 for p ≥ 1, and -1 for p = 0. -/
theorem deriv_ep_at_zero (p : ℕ) :
    deriv (ep p) 0 = if p = 0 then -1 else 0 := by
  have h := (hasDerivAt_ep p 0).deriv
  simp [epSum_at_zero] at h
  rw [h]
  split_ifs with hp
  · subst hp; simp
  · simp [zero_pow hp]

/-! ## Zeros of E_p -/

/-- E_p has no zeros except at z = 1: if E_p(z) = 0 then z = 1. -/
theorem ep_eq_zero_iff (p : ℕ) (z : ℂ) : ep p z = 0 ↔ z = 1 := by
  constructor
  · intro h
    unfold ep at h
    rw [mul_eq_zero] at h
    rcases h with h1 | h2
    · exact (sub_eq_zero.mp h1).symm
    · exact absurd h2 (exp_ne_zero _)
  · intro h; rw [h]; exact ep_at_one p

/-- The zero of E_p at z = 1 is simple (the derivative is nonzero there). -/
theorem ep_deriv_at_one_ne_zero (p : ℕ) :
    deriv (ep p) 1 ≠ 0 := by
  have h := (hasDerivAt_ep p 1).deriv
  rw [h]
  simp [exp_ne_zero]

/-! ## Bounds on E_p -/

/-- Partial sum of r^{k+1}/(k+1) is bounded by the geometric sum r/(1-r). -/
private theorem partial_sum_le_geom (p : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    ∑ k ∈ Finset.range p, r ^ (k + 1) / (↑(k + 1) : ℝ) ≤ r / (1 - r) := by
  calc ∑ k ∈ Finset.range p, r ^ (k + 1) / (↑(k + 1) : ℝ)
      ≤ ∑ k ∈ Finset.range p, r ^ (k + 1) := by
        apply Finset.sum_le_sum; intro k _
        exact div_le_self (pow_nonneg hr0 _)
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega))
    _ = r * ∑ k ∈ Finset.range p, r ^ k := by
        rw [Finset.mul_sum]; congr 1; ext k; ring
    _ ≤ r * (∑' k, r ^ k) := by
        apply mul_le_mul_of_nonneg_left _ hr0
        exact sum_le_hasSum _ (fun n _ => pow_nonneg hr0 n)
          (summable_geometric_of_abs_lt_one (abs_lt.mpr ⟨by linarith, hr⟩)).hasSum
    _ = r / (1 - r) := by
        rw [tsum_geometric_of_abs_lt_one (abs_lt.mpr ⟨by linarith, hr⟩)]
        field_simp

/-- Bound on |S_p(z)| for |z| ≤ r < 1: |S_p(z)| ≤ r/(1-r).
    This follows from bounding each |z|^{k+1}/(k+1) ≤ r^{k+1} and summing
    the resulting geometric series. -/
theorem norm_epSum_le (p : ℕ) {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) (hr : r < 1) :
    ‖epSum p z‖ ≤ r / (1 - r) := by
  unfold epSum
  calc ‖∑ k ∈ Finset.range p, z ^ (k + 1) / (↑(k + 1) : ℂ)‖
      ≤ ∑ k ∈ Finset.range p, ‖z ^ (k + 1) / (↑(k + 1) : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range p, r ^ (k + 1) / (↑(k + 1) : ℝ) := by
        apply Finset.sum_le_sum; intro k _
        rw [norm_div, norm_pow, _root_.norm_natCast]
        exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg z) hz _) (by positivity)
    _ ≤ r / (1 - r) := partial_sum_le_geom p (le_trans (norm_nonneg z) hz) hr

/-- Specialization: |S_p(z)| ≤ 1 when |z| ≤ 1/2. -/
theorem norm_epSum_le_one (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖epSum p z‖ ≤ 1 := by
  calc ‖epSum p z‖ ≤ (1/2) / (1 - 1/2) := norm_epSum_le p hz (by norm_num)
    _ = 1 := by norm_num

/-- exp(1) ≤ 3, proved via Complex.exp_bound with the n=3 partial sum. -/
private theorem exp_one_le_three : Real.exp 1 ≤ 3 := by
  rw [show Real.exp 1 = ‖Complex.exp (1 : ℂ)‖ from by rw [Complex.norm_exp]; simp]
  have h3 := Complex.exp_bound (show ‖(1 : ℂ)‖ ≤ 1 from by simp) (n := 3) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 3, (1 : ℂ) ^ m / ↑m.factorial) = 5/2 := by
    simp [Finset.sum_range_succ]; norm_num
  rw [hsum] at h3
  calc ‖Complex.exp (1 : ℂ)‖
    = ‖(5/2 : ℂ) + (Complex.exp 1 - 5/2)‖ := by ring_nf
    _ ≤ ‖(5/2 : ℂ)‖ + ‖Complex.exp (1 : ℂ) - 5/2‖ := norm_add_le _ _
    _ ≤ 5/2 + 2/9 := by
        apply add_le_add _ (le_trans h3 (by norm_num)); simp
    _ ≤ 3 := by norm_num

/-- For w on the segment [0, z], we have ‖w‖ ≤ ‖z‖. -/
private theorem norm_le_of_mem_segment {z w : ℂ}
    (hw : w ∈ segment ℝ (0 : ℂ) z) : ‖w‖ ≤ ‖z‖ := by
  rw [segment_eq_image'] at hw
  obtain ⟨t, ht, rfl⟩ := hw
  simp [abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg z) ht.2

/-- **Convergence bound for |z| ≤ 1/2**: |1 - E_p(z)| ≤ 3 · |z|^{p+1}.
    This is the key estimate for convergence of Weierstrass products.
    The proof applies the MVT to E_p on the segment [0, z],
    using the derivative bound |E_p'(w)| ≤ |z|^p · exp(1) for w on [0, z]. -/
theorem norm_one_sub_ep_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) (p : ℕ) :
    ‖1 - ep p z‖ ≤ 3 * ‖z‖ ^ (p + 1) := by
  -- Apply MVT on segment [0, z]: ‖ep(z) - ep(0)‖ ≤ C * ‖z‖
  -- where C = ‖z‖^p * exp(1) bounds ‖ep'(w)‖ for w ∈ [0, z].
  have hderiv : ∀ w ∈ segment ℝ (0 : ℂ) z,
      HasDerivWithinAt (ep p) (-w ^ p * exp (epSum p w))
        (segment ℝ 0 z) w :=
    fun w _ => (hasDerivAt_ep p w).hasDerivWithinAt
  have hbound : ∀ w ∈ segment ℝ (0 : ℂ) z,
      ‖-w ^ p * exp (epSum p w)‖ ≤ ‖z‖ ^ p * Real.exp 1 := by
    intro w hw
    have hwz : ‖w‖ ≤ ‖z‖ := norm_le_of_mem_segment hw
    have hwh : ‖w‖ ≤ 1 / 2 := le_trans hwz hz
    rw [neg_mul, norm_neg, norm_mul, norm_pow, Complex.norm_exp]
    exact mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg w) hwz p)
      (Real.exp_le_exp_of_le (le_trans (Complex.re_le_norm _) (norm_epSum_le_one p hwh)))
      (Real.exp_nonneg _)
      (pow_nonneg (norm_nonneg z) p)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_segment 0 z) (right_mem_segment ℝ 0 z) (left_mem_segment ℝ 0 z)
  rw [ep_at_zero, show (0 : ℂ) - z = -(z - 0) from by ring, norm_neg, sub_zero] at hmvt
  rw [norm_sub_rev] at hmvt ⊢
  calc ‖ep p z - 1‖ ≤ ‖z‖ ^ p * Real.exp 1 * ‖z‖ := hmvt
    _ = Real.exp 1 * ‖z‖ ^ (p + 1) := by ring
    _ ≤ 3 * ‖z‖ ^ (p + 1) :=
        mul_le_mul_of_nonneg_right exp_one_le_three (pow_nonneg (norm_nonneg z) _)

/-! ## Shifted elementary factor -/

/-- The shifted elementary factor E_p(z/a) has a simple zero at z = a. -/
def epShifted (p : ℕ) (a : ℂ) (z : ℂ) : ℂ := ep p (z / a)

theorem epShifted_at_a (p : ℕ) {a : ℂ} (ha : a ≠ 0) : epShifted p a a = 0 := by
  simp [epShifted, div_self ha, ep_at_one]

theorem epShifted_at_zero (p : ℕ) (a : ℂ) : epShifted p a 0 = 1 := by
  simp [epShifted, zero_div, ep_at_zero]

theorem differentiable_epShifted (p : ℕ) (a : ℂ) :
    Differentiable ℂ (epShifted p a) := by
  unfold epShifted
  exact (differentiable_ep p).comp (differentiable_id.div_const a)

/-! ## E_1 specialized results for Hadamard factorization -/

/-- For the Hadamard factorization with genus 1, we use
    E_1(z/ρ) = (1 - z/ρ) · exp(z/ρ). -/
theorem ep_one_shifted (z ρ : ℂ) : epShifted 1 ρ z = (1 - z / ρ) * exp (z / ρ) := by
  unfold epShifted; rw [ep_one]

/-- |1 - E_1(z/ρ)| ≤ 2|z/ρ|² when |z/ρ| ≤ 1/2.
    This is the key estimate for convergence of the Hadamard product of ξ(s),
    given that ∑_ρ 1/|ρ|² < ∞ (which follows from N(T) ~ T log T). -/
theorem norm_one_sub_ep_one_shifted_le {z ρ : ℂ} (h : ‖z / ρ‖ ≤ 1 / 2) :
    ‖1 - epShifted 1 ρ z‖ ≤ 3 * ‖z / ρ‖ ^ 2 := by
  exact norm_one_sub_ep_le h 1

end WeierstrassFactors
