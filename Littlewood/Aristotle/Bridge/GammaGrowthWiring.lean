/-
Bridge file: Wire GammaGrowthBoundsV2 for critical path needs

GammaGrowthBoundsV2 provides:
- gamma_half_growth: bounds at σ = 1/2 (PROVED, 0 sorries)
- gamma_growth_step_up: propagates σ → σ+1 (PROVED)
- gamma_growth_step_down: propagates σ+1 → σ (PROVED)
- HasGammaGrowth: definition matching PhragmenLindelof.gamma_growth

Co-authored-by: Claude Code <noreply@anthropic.com>
-/

import Littlewood.Aristotle.GammaGrowthBoundsV2

open Aristotle.GammaGrowthBoundsV2
open Real Complex

set_option maxHeartbeats 3200000

namespace Aristotle.Bridge.GammaGrowthWiring

/-- gamma_half_growth implies HasGammaGrowth (1/2) -/
theorem hasGammaGrowth_half : HasGammaGrowth (1/2) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ := gamma_half_growth
  use C₁, C₂, hC₁, hC₂
  intro t ht
  specialize h t ht
  simp only [sub_self, Real.rpow_zero, mul_one]
  have eq1 : (↑(1/2 : ℝ) : ℂ) + ↑t * I = (1/2 : ℂ) + ↑t * I := by norm_num
  simp only [eq1]
  exact h

/-- HasGammaGrowth for 3/2 = 1/2 + 1 -/
theorem hasGammaGrowth_three_halves : HasGammaGrowth (3/2) := by
  have h : (3:ℝ)/2 = 1/2 + 1 := by norm_num
  rw [h]
  exact gamma_growth_step_up (1/2) hasGammaGrowth_half

/-- Stepping up n times from 1/2 gives HasGammaGrowth (1/2 + n) -/
theorem hasGammaGrowth_half_add_nat (n : ℕ) : HasGammaGrowth (1/2 + n) := by
  induction n with
  | zero => simp only [Nat.cast_zero, add_zero]; exact hasGammaGrowth_half
  | succ k ih =>
    have h : (1:ℝ)/2 + (k + 1 : ℕ) = (1/2 + k) + 1 := by push_cast; ring
    rw [h]
    exact gamma_growth_step_up (1/2 + k) ih

/-- Export: The gamma growth bound at σ = 1/2 -/
theorem gamma_growth_at_half :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ t : ℝ, 1 ≤ |t| →
      C₁ * Real.exp (-Real.pi * |t| / 2) ≤ ‖Complex.Gamma (1/2 + t * Complex.I)‖ ∧
      ‖Complex.Gamma (1/2 + t * Complex.I)‖ ≤ C₂ * Real.exp (-Real.pi * |t| / 2) :=
  gamma_half_growth

/-- Helper: conj(u*I) = -(u*I) for u : ℝ -/
private lemma conj_ofReal_mul_I (u : ℝ) :
    starRingEnd ℂ (↑u * I) = -(↑u * I) := by
  simp [map_mul, conj_ofReal, conj_I]

/-- Helper: ‖Γ(-(u*I))‖ = ‖Γ(u*I)‖ for u : ℝ -/
private lemma gamma_neg_I_norm (u : ℝ) :
    ‖Complex.Gamma (-(↑u * I))‖ = ‖Complex.Gamma (↑u * I)‖ := by
  rw [← conj_ofReal_mul_I u, Complex.Gamma_conj]
  exact norm_star _

/-- Helper: ‖sin(π*(1+u*I))‖ = Real.sinh(π*u) for u > 0 -/
private lemma norm_sin_shift (u : ℝ) (hu : 0 < u) :
    ‖Complex.sin (↑Real.pi * (1 + ↑u * I))‖ = Real.sinh (Real.pi * u) := by
  have h1 : ↑Real.pi * (1 + ↑u * I) = ↑Real.pi * ↑u * I + ↑Real.pi := by ring
  rw [h1, Complex.sin_add_pi, norm_neg]
  have h2 : ↑Real.pi * ↑u * I = ↑(Real.pi * u) * I := by push_cast; ring
  rw [h2, Complex.sin_mul_I, norm_mul, Complex.norm_I, mul_one]
  rw [← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hu))]

/-- Key identity: ‖Γ(1 + u*I)‖² = π*u / sinh(π*u) for u > 0 with u ≥ 1 -/
private lemma gamma_one_norm_sq_pos (u : ℝ) (hu : 1 ≤ u) :
    ‖Complex.Gamma (1 + ↑u * I)‖ ^ 2 = Real.pi * u / Real.sinh (Real.pi * u) := by
  have hu_pos : 0 < u := by linarith
  have hpu_pos : 0 < Real.pi * u := mul_pos Real.pi_pos hu_pos
  have hsinh_pos : 0 < Real.sinh (Real.pi * u) := Real.sinh_pos_iff.mpr hpu_pos
  have h_uI_ne : (↑u : ℂ) * I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hu_pos)) Complex.I_ne_zero
  have hGamma_rec : Complex.Gamma (↑u * I + 1) = ↑u * I * Complex.Gamma (↑u * I) :=
    Complex.Gamma_add_one _ h_uI_ne
  have h_norm_rec : ‖Complex.Gamma (1 + ↑u * I)‖ = u * ‖Complex.Gamma (↑u * I)‖ := by
    have h_comm : (1 : ℂ) + ↑u * I = ↑u * I + 1 := by ring
    rw [h_comm, hGamma_rec, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_I, Real.norm_eq_abs, abs_of_pos hu_pos, mul_one]
  have h_norm_sq_eq : ‖Complex.Gamma (1 + ↑u * I)‖ ^ 2 =
      u ^ 2 * ‖Complex.Gamma (↑u * I)‖ ^ 2 := by
    rw [h_norm_rec, mul_pow]
  have h_refl : Complex.Gamma (1 + ↑u * I) * Complex.Gamma (-(↑u * I)) =
      ↑Real.pi / Complex.sin (↑Real.pi * (1 + ↑u * I)) := by
    have := Complex.Gamma_mul_Gamma_one_sub (1 + ↑u * I)
    rw [show 1 - (1 + ↑u * I) = -(↑u * I) from by ring] at this
    exact this
  have h_norm_product : ‖Complex.Gamma (1 + ↑u * I)‖ * ‖Complex.Gamma (-(↑u * I))‖ =
      Real.pi / Real.sinh (Real.pi * u) := by
    have h := congr_arg (fun z => ‖z‖) h_refl
    simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
               abs_of_pos Real.pi_pos, norm_sin_shift u hu_pos] at h
    exact h
  rw [gamma_neg_I_norm] at h_norm_product
  rw [h_norm_sq_eq]
  rw [h_norm_rec] at h_norm_product
  have h_gamma_sq : u * ‖Complex.Gamma (↑u * I)‖ ^ 2 = Real.pi / Real.sinh (Real.pi * u) := by
    rw [sq]; linarith [h_norm_product]
  have h_expand : u ^ 2 * ‖Complex.Gamma (↑u * I)‖ ^ 2 =
      u * (u * ‖Complex.Gamma (↑u * I)‖ ^ 2) := by ring
  rw [h_expand, h_gamma_sq]
  field_simp

/-- General case: reduce to positive via conjugation -/
private lemma gamma_norm_abs_reduce (t : ℝ) :
    ‖Complex.Gamma (1 + ↑t * I)‖ = ‖Complex.Gamma (1 + ↑|t| * I)‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · push_neg at ht
    rw [abs_of_neg ht]
    have hconj : starRingEnd ℂ (1 + ↑t * I) = 1 + ↑(-t) * I := by
      simp [map_add, map_mul, map_one, conj_ofReal, conj_I]
    calc ‖Complex.Gamma (1 + ↑t * I)‖
        = ‖starRingEnd ℂ (Complex.Gamma (1 + ↑t * I))‖ := (norm_star _).symm
      _ = ‖Complex.Gamma (starRingEnd ℂ (1 + ↑t * I))‖ := by rw [Complex.Gamma_conj]
      _ = ‖Complex.Gamma (1 + ↑(-t) * I)‖ := by rw [hconj]

/-- Main identity: ‖Γ(1 + t*I)‖² = π*|t| / sinh(π*|t|) for |t| ≥ 1 -/
private lemma gamma_one_norm_sq (t : ℝ) (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (1 + t * Complex.I)‖ ^ 2 = Real.pi * |t| / Real.sinh (Real.pi * |t|) := by
  have h : ‖Complex.Gamma (1 + ↑t * I)‖ = ‖Complex.Gamma (1 + ↑|t| * I)‖ :=
    gamma_norm_abs_reduce t
  rw [h]
  exact gamma_one_norm_sq_pos |t| ht

/-- Upper and lower bounds on π*x/sinh(πx) for x ≥ 1.
    Lower: sinh(πx) ≤ exp(πx) → π*x/sinh(πx) ≥ π*x*exp(-πx)
    Upper: sinh(πx) ≥ exp(πx)/4 for x ≥ 1 → π*x/sinh(πx) ≤ 4*π*x*exp(-πx) -/
private lemma pi_over_sinh_bounds (x : ℝ) (hx : 1 ≤ x) :
    Real.pi * x * Real.exp (-Real.pi * x) ≤
      Real.pi * x / Real.sinh (Real.pi * x) ∧
    Real.pi * x / Real.sinh (Real.pi * x) ≤
      4 * Real.pi * x * Real.exp (-Real.pi * x) := by
  have hx_pos : 0 < x := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpx_pos : 0 < Real.pi * x := mul_pos hpi_pos hx_pos
  have h_exp_pos : 0 < Real.exp (Real.pi * x) := Real.exp_pos _
  have h_exp_neg_pos : 0 < Real.exp (-(Real.pi * x)) := Real.exp_pos _
  have h_sinh_pos : 0 < Real.sinh (Real.pi * x) := Real.sinh_pos_iff.mpr hpx_pos
  -- sinh(πx) = (exp(πx) - exp(-πx))/2
  have h_sinh_eq : Real.sinh (Real.pi * x) = (Real.exp (Real.pi * x) - Real.exp (-(Real.pi * x))) / 2 := by
    rw [Real.sinh_eq]
  -- Upper bound on sinh: sinh(πx) ≤ exp(πx)/2 ≤ exp(πx)
  have h_sinh_le : Real.sinh (Real.pi * x) ≤ Real.exp (Real.pi * x) := by
    rw [h_sinh_eq]; linarith
  -- Lower bound on sinh: sinh(πx) ≥ exp(πx)/4 for x ≥ 1
  -- Since exp(-πx) ≤ exp(-π) < 1 < exp(πx)/2 for x ≥ 1,
  -- sinh(πx) = (exp(πx) - exp(-πx))/2 ≥ (exp(πx) - exp(πx)/2)/2 = exp(πx)/4
  -- Actually simpler: exp(-πx) ≤ 1 for πx ≥ 0,
  -- so sinh(πx) ≥ (exp(πx) - 1)/2. For exp(πx) ≥ 2 (which holds for πx ≥ π ≥ 1),
  -- (exp(πx) - 1)/2 ≥ exp(πx)/4.
  have h_sinh_ge : Real.exp (Real.pi * x) / 4 ≤ Real.sinh (Real.pi * x) := by
    rw [h_sinh_eq]
    -- Need: exp(πx)/4 ≤ (exp(πx) - exp(-πx))/2
    -- i.e., exp(πx)/2 ≤ 2*(exp(πx) - exp(-πx))/4 = exp(πx)/2 - exp(-πx)/2
    -- Wait, let's just do: exp(πx)/4 ≤ (exp(πx) - exp(-πx))/2
    -- ↔ exp(πx)/2 ≤ 2*exp(πx) - 2*exp(-πx)  -- multiply by 4
    -- ↔ exp(πx) ≤ 4*exp(πx) - 4*exp(-πx)
    -- This is not quite right. Let me be more careful.
    -- exp(πx)/4 ≤ (exp(πx) - exp(-πx))/2
    -- ↔ exp(πx) ≤ 2*(exp(πx) - exp(-πx))  -- multiply by 4
    -- ↔ exp(πx) ≤ 2*exp(πx) - 2*exp(-πx)
    -- ↔ 2*exp(-πx) ≤ exp(πx)
    -- ↔ 2 ≤ exp(2πx)  -- multiply by exp(πx)
    -- This holds for 2πx ≥ ln 2, i.e., x ≥ ln 2 / (2π) ≈ 0.11, so for x ≥ 1 it's fine.
    have h_key : 2 * Real.exp (-(Real.pi * x)) ≤ Real.exp (Real.pi * x) := by
      have h2 : Real.pi * x ≥ Real.pi := by nlinarith
      have := Real.add_one_le_exp (Real.pi * x)
      nlinarith [Real.exp_pos (-(Real.pi * x)),
                 Real.exp_le_one_iff.mpr (by linarith : -(Real.pi * x) ≤ 0),
                 Real.pi_gt_three]
    linarith
  have h_exp_neg_eq : Real.exp (-Real.pi * x) = (Real.exp (Real.pi * x))⁻¹ := by
    rw [show -Real.pi * x = -(Real.pi * x) by ring, Real.exp_neg]
  have hsinh_pos := h_sinh_pos
  have hsinh_le_exp := h_sinh_le
  have h_neg_eq : -Real.pi * x = -(Real.pi * x) := by ring
  constructor
  · rw [le_div_iff₀ hsinh_pos]
    -- Goal: π * x * exp(-π * x) * sinh(πx) ≤ π * x
    -- Since exp(-πx) * sinh(πx) ≤ exp(-πx) * exp(πx) = 1
    have h1 : Real.exp (-(Real.pi * x)) * Real.sinh (Real.pi * x) ≤ 1 := by
      calc Real.exp (-(Real.pi * x)) * Real.sinh (Real.pi * x)
          ≤ Real.exp (-(Real.pi * x)) * Real.exp (Real.pi * x) := by nlinarith [hsinh_le_exp]
        _ = 1 := by rw [← Real.exp_add]; simp
    have h1' : Real.exp (-Real.pi * x) * Real.sinh (Real.pi * x) ≤ 1 := by
      rw [h_neg_eq]; exact h1
    nlinarith
  · rw [div_le_iff₀ hsinh_pos]
    -- Goal: π * x ≤ 4 * (π * x) * exp(-π * x) * sinh(πx)
    suffices h : 1 ≤ 4 * Real.exp (-Real.pi * x) * Real.sinh (Real.pi * x) by nlinarith
    rw [h_neg_eq]
    -- 4*exp(-)*sinh = 2*(1 - exp(-2πx)) and exp(-2πx) ≤ 1/2
    have hprod : Real.exp (Real.pi * x) * Real.exp (-(Real.pi * x)) = 1 := by
      rw [← Real.exp_add]; simp
    have hsinh_eq : 2 * Real.sinh (Real.pi * x) =
        Real.exp (Real.pi * x) - Real.exp (-(Real.pi * x)) := by
      have := Real.sinh_eq (Real.pi * x); linarith
    have h_key : 4 * Real.exp (-(Real.pi * x)) * Real.sinh (Real.pi * x) =
        2 * (1 - Real.exp (-(Real.pi * x)) ^ 2) := by
      nlinarith [hprod]
    rw [h_key]
    have h_exp_sq_le : Real.exp (-(Real.pi * x)) ^ 2 ≤ 1/2 := by
      have h2 : 2 ≤ Real.exp (2 * (Real.pi * x)) := by
        have h_ge_pi : Real.pi * x ≥ Real.pi := by nlinarith
        have h_ge_one : 1 ≤ 2 * (Real.pi * x) := by nlinarith [Real.pi_gt_three]
        have := Real.add_one_le_exp (2 * (Real.pi * x))
        linarith
      have hprod2 : Real.exp (-(Real.pi * x)) ^ 2 * Real.exp (2 * (Real.pi * x)) = 1 := by
        rw [sq, ← Real.exp_add, ← Real.exp_add]; simp; ring_nf
      nlinarith [Real.exp_pos (2 * (Real.pi * x))]
    linarith

/-- Auxiliary: if a² ≤ b² and 0 ≤ a and 0 ≤ b then a ≤ b -/
private lemma le_of_sq_le_sq' {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [sq_nonneg (b - a)]

/-- Auxiliary: rpow squaring lemma for |t|^(1/2) -/
private lemma rpow_half_sq (x : ℝ) (hx : 0 < x) :
    (x ^ ((1:ℝ) - 1/2)) ^ 2 = x := by
  rw [← Real.rpow_natCast (x ^ ((1:ℝ) - 1/2)) 2,
      ← Real.rpow_mul (le_of_lt hx)]
  norm_num

/-- Auxiliary: exp squaring lemma -/
private lemma exp_half_sq (x : ℝ) :
    Real.exp (-Real.pi * x / 2) ^ 2 = Real.exp (-Real.pi * x) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- HasGammaGrowth at σ = 1. -/
theorem hasGammaGrowth_one : HasGammaGrowth 1 := by
  -- We need: ∃ C₁ C₂ > 0, ∀ t, 1 ≤ |t| →
  --   C₁ * |t|^(1-1/2) * exp(-π|t|/2) ≤ ‖Γ(1+it)‖ ≤ C₂ * |t|^(1-1/2) * exp(-π|t|/2)
  -- Strategy: from gamma_one_norm_sq and pi_over_sinh_bounds, extract square root bounds
  use Real.sqrt Real.pi, 2 * Real.sqrt Real.pi
  refine ⟨Real.sqrt_pos.mpr Real.pi_pos,
         mul_pos two_pos (Real.sqrt_pos.mpr Real.pi_pos), ?_⟩
  intro t ht
  have h_norm_sq := gamma_one_norm_sq t ht
  have h_sinh_bnd := pi_over_sinh_bounds |t| ht
  have h_t_pos : 0 < |t| := by linarith
  -- The key squared bounds
  have h_sq_lower : Real.pi * |t| * Real.exp (-Real.pi * |t|) ≤
      ‖Complex.Gamma (1 + t * Complex.I)‖ ^ 2 := by
    rw [h_norm_sq]; exact h_sinh_bnd.1
  have h_sq_upper : ‖Complex.Gamma (1 + t * Complex.I)‖ ^ 2 ≤
      4 * Real.pi * |t| * Real.exp (-Real.pi * |t|) := by
    rw [h_norm_sq]; exact h_sinh_bnd.2
  -- Cast equivalence
  have h_one_cast : (1 : ℂ) + ↑t * I = ↑(1:ℝ) + ↑t * I := by push_cast; ring
  -- Compute squared targets using auxiliary lemmas
  have h_rpow_sq := rpow_half_sq |t| h_t_pos
  have h_exp_sq := exp_half_sq |t|
  -- Lower bound target squared
  have h_lower_target_sq : (Real.sqrt Real.pi * |t| ^ ((1:ℝ) - 1/2) *
      Real.exp (-Real.pi * |t| / 2)) ^ 2 =
      Real.pi * |t| * Real.exp (-Real.pi * |t|) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, h_rpow_sq, h_exp_sq]
  -- Upper bound target squared
  have h_upper_target_sq : (2 * Real.sqrt Real.pi * |t| ^ ((1:ℝ) - 1/2) *
      Real.exp (-Real.pi * |t| / 2)) ^ 2 =
      4 * Real.pi * |t| * Real.exp (-Real.pi * |t|) := by
    rw [show 2 * Real.sqrt Real.pi * |t| ^ ((1:ℝ) - 1/2) *
        Real.exp (-Real.pi * |t| / 2) =
        2 * (Real.sqrt Real.pi * |t| ^ ((1:ℝ) - 1/2) *
        Real.exp (-Real.pi * |t| / 2)) by ring,
        mul_pow, h_lower_target_sq]
    norm_num; ring
  constructor
  · -- Lower bound: ‖Γ(1+it)‖ ≥ √π · |t|^(1/2) · exp(-π|t|/2)
    -- We know ‖Γ‖² ≥ target², both non-negative, so ‖Γ‖ ≥ target
    have h_gamma_nn : 0 ≤ ‖Complex.Gamma (↑(1:ℝ) + ↑t * I)‖ := norm_nonneg _
    have h_target_nn : 0 ≤ Real.sqrt Real.pi * |t| ^ ((1:ℝ) - 1/2) *
        Real.exp (-Real.pi * |t| / 2) := by positivity
    apply le_of_sq_le_sq' h_target_nn (by rw [← h_one_cast]; exact norm_nonneg _)
    rw [h_lower_target_sq, ← h_one_cast]
    exact h_sq_lower
  · -- Upper bound: ‖Γ(1+it)‖ ≤ 2√π · |t|^(1/2) · exp(-π|t|/2)
    have h_target_nn : 0 ≤ 2 * Real.sqrt Real.pi * |t| ^ ((1:ℝ) - 1/2) *
        Real.exp (-Real.pi * |t| / 2) := by positivity
    apply le_of_sq_le_sq' (by rw [← h_one_cast]; exact norm_nonneg _) h_target_nn
    rw [h_upper_target_sq, ← h_one_cast]
    exact h_sq_upper

/-- HasGammaGrowth for all positive natural numbers, via step_up from 1 -/
theorem hasGammaGrowth_nat_pos (n : ℕ) (hn : 0 < n) : HasGammaGrowth n := by
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      -- n = 1
      have h_eq : (↑(Nat.succ 0) : ℝ) = 1 := by push_cast; ring
      rw [h_eq]
      exact hasGammaGrowth_one
    | succ m =>
      have hm : 0 < m + 1 := Nat.succ_pos m
      have ih_k := ih hm
      have h : (↑(m + 1 + 1) : ℝ) = (↑(m + 1) : ℝ) + 1 := by push_cast; ring
      rw [h]
      exact gamma_growth_step_up (↑(m + 1)) ih_k

end Aristotle.Bridge.GammaGrowthWiring
