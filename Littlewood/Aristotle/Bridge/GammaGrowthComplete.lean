/-
Bridge file: Complete gamma_growth for all σ > 0.

Depends on stirling_ratio_bounded_on_strip (Phragmén-Lindelöf, in StirlingRatioPL.lean).

Co-authored-by: Claude Code <noreply@anthropic.com>
-/

import Littlewood.Aristotle.GammaGrowthBoundsV2
import Littlewood.Aristotle.GammaGrowthGeneral
import Littlewood.Aristotle.Bridge.GammaGrowthWiring
import Littlewood.Aristotle.Bridge.StirlingRatioPL

open Complex Real MeasureTheory Set Filter Topology Asymptotics
open scoped BigOperators Real Nat Classical

set_option maxHeartbeats 3200000
set_option maxRecDepth 4000

noncomputable section

namespace Aristotle.Bridge.GammaGrowthComplete

open Aristotle.GammaGrowthBoundsV2
open Aristotle.GammaGrowthGeneral
open Aristotle.Bridge.GammaGrowthWiring
open Aristotle.Bridge.StirlingRatioPL

/-!
## Step 1: |Γ(s)| ≤ Γ(Re s) for Re(s) > 0
-/

theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs]
  unfold Complex.GammaIntegral
  calc ‖∫ x in Ioi (0:ℝ), ↑((-x).exp) * (↑x : ℂ) ^ (s - 1)‖
      ≤ ∫ x in Ioi (0:ℝ), ‖↑((-x).exp) * (↑x : ℂ) ^ (s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (0:ℝ), (-x).exp * x ^ (s.re - 1) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        rw [Set.mem_Ioi] at hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _),
            Complex.norm_cpow_eq_rpow_re_of_pos hx (s - 1)]
        simp [Complex.sub_re]
    _ = Real.Gamma s.re := (Real.Gamma_eq_integral hs).symm

/-!
## Step 2: HasGammaUpperGrowth on [1/2, 3/2] from stirling_ratio bound + kernel bound
-/

private theorem hasGammaUpperGrowth_in_strip (σ : ℝ) (hσ₁ : 1/2 ≤ σ) (hσ₂ : σ ≤ 3/2) :
    HasGammaUpperGrowth σ := by
  have hσ_pos : 0 < σ := by linarith
  obtain ⟨B, hB_pos, hB⟩ := stirling_ratio_bounded_on_strip 0 (by norm_num : (0:ℝ) < 1/2 + (0:ℤ))
  obtain ⟨C₁_k, C₂_k, hC₁_k, hC₂_k, hkernel⟩ := stirling_kernel_bound σ hσ_pos
  refine ⟨B * C₂_k, mul_pos hB_pos hC₂_k, fun t ht => ?_⟩
  set s := (↑σ + ↑t * I : ℂ) with hs_def
  have hre : s.re = σ := by
    simp [hs_def, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have him : s.im = t := by
    simp [hs_def, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hre₁ : 1/2 + (0:ℤ) ≤ s.re := by simp [hre]; linarith
  have hre₂ : s.re ≤ 1/2 + (0:ℤ) + 1 := by simp [hre]; linarith
  have him₁ : 1 ≤ |s.im| := by rw [him]; linarith
  -- ‖stirling_ratio s‖ ≤ B, and ratio = Γ/kernel
  have h_ratio := hB s hre₁ hre₂ him₁
  have h_kernel := (hkernel t ht).2
  have h_norm_ratio : ‖stirling_ratio s‖ = ‖Complex.Gamma s‖ / ‖stirling_kernel s‖ := by
    unfold stirling_ratio; exact norm_div _ _
  have h_kernel_pos : 0 < ‖stirling_kernel s‖ := by
    have h_lower := (hkernel t ht).1
    have : 0 < C₁_k * |t| ^ (σ - 1 / 2) * rexp (-π * |t| / 2) := by positivity
    linarith
  -- From ‖ratio‖ = ‖Γ‖/‖kernel‖ ≤ B, get ‖Γ‖ ≤ B * ‖kernel‖
  have h_gamma_le : ‖Complex.Gamma s‖ ≤ B * ‖stirling_kernel s‖ := by
    rw [h_norm_ratio] at h_ratio
    rwa [div_le_iff₀ h_kernel_pos] at h_ratio
  calc ‖Complex.Gamma s‖
      ≤ B * ‖stirling_kernel s‖ := h_gamma_le
    _ ≤ B * (C₂_k * |t| ^ (σ - 1/2) * rexp (-π * |t| / 2)) :=
        mul_le_mul_of_nonneg_left h_kernel (le_of_lt hB_pos)
    _ = B * C₂_k * |t| ^ (σ - 1/2) * rexp (-π * |t| / 2) := by ring

/-!
## Step 3: HasGammaUpperGrowth stepping
-/

private theorem hasGammaUpperGrowth_step_down (σ : ℝ) (hσ : 0 < σ)
    (h : HasGammaUpperGrowth (σ + 1)) : HasGammaUpperGrowth σ := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun t ht => ?_⟩
  set s := (↑σ + ↑t * I : ℂ) with hs_def
  have hs_ne : s ≠ 0 := by
    intro h_eq
    have hre := congr_arg Complex.re h_eq
    simp [hs_def, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre
    linarith
  have h_func := Complex.Gamma_add_one s hs_ne
  have hs1 : s + 1 = ↑(σ + 1) + ↑t * I := by
    simp [hs_def, Complex.ofReal_add]; ring
  have hs_norm_pos : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr hs_ne
  -- ‖Γ(s)‖ = ‖Γ(s+1)‖ / ‖s‖ via Γ(s+1) = s·Γ(s)
  have h_norm_eq : ‖Complex.Gamma s‖ = ‖Complex.Gamma (↑(σ+1) + ↑t * I)‖ / ‖s‖ := by
    have hmul : ‖Complex.Gamma (↑(σ+1) + ↑t * I)‖ = ‖s‖ * ‖Complex.Gamma s‖ := by
      rw [← hs1, h_func, norm_mul]
    rw [hmul, mul_div_cancel_left₀ _ (ne_of_gt hs_norm_pos)]
  -- |t| ≤ ‖s‖
  have h_im_le : |t| ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s
    simp [hs_def, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] at this
    linarith
  have ht_pos : (0 : ℝ) < |t| := by linarith
  -- Chain: ‖Γ(s)‖ = ‖Γ(s+1)‖/‖s‖ ≤ ‖Γ(s+1)‖/|t| ≤ C·|t|^{σ+1/2}·exp/|t| = C·|t|^{σ-1/2}·exp
  have h1 : ‖Complex.Gamma s‖ ≤ ‖Complex.Gamma (↑(σ+1) + ↑t * I)‖ / |t| := by
    rw [h_norm_eq]
    apply div_le_div_of_nonneg_left (norm_nonneg _) ht_pos h_im_le
  have h3 : ‖Complex.Gamma (↑(σ+1) + ↑t * I)‖ / |t| ≤
      C * |t| ^ (σ + 1 - 1/2) * rexp (-π * |t| / 2) / |t| :=
    div_le_div_of_nonneg_right (hbound t ht) (le_of_lt ht_pos)
  have h4 : C * |t| ^ (σ + 1 - 1/2) * rexp (-π * |t| / 2) / |t| =
      C * |t| ^ (σ - 1/2) * rexp (-π * |t| / 2) := by
    have h_abs_pos : (0:ℝ) < |t| := ht_pos
    rw [show σ + 1 - 1/2 = (σ - 1/2) + 1 from by ring,
        rpow_add h_abs_pos, rpow_one]
    field_simp
  linarith

private theorem hasGammaUpperGrowth_step_up (σ : ℝ) (hσ : 0 < σ)
    (h : HasGammaUpperGrowth σ) : HasGammaUpperGrowth (σ + 1) := by
  obtain ⟨C, hC, hbound⟩ := h
  have hσ1 : (0 : ℝ) < σ + 1 := by linarith
  refine ⟨(|σ| + 1) * C, mul_pos (by positivity) hC, fun t ht => ?_⟩
  set s := (↑σ + ↑t * I : ℂ) with hs_def
  have hs_ne : s ≠ 0 := by
    intro h_eq
    have hre := congr_arg Complex.re h_eq
    simp [hs_def, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre
    linarith
  have h_func := Complex.Gamma_add_one s hs_ne
  have hs1 : s + 1 = ↑(σ + 1) + ↑t * I := by
    simp [hs_def, Complex.ofReal_add]; ring
  have ht_pos : (0 : ℝ) < |t| := by linarith
  -- ‖s‖ ≤ |σ| + |t| ≤ (|σ|+1)*|t| for |t| ≥ 1
  have h_s_norm_le : ‖s‖ ≤ (|σ| + 1) * |t| := by
    calc ‖s‖ = ‖(↑σ : ℂ) + ↑t * I‖ := by rfl
      _ ≤ ‖(↑σ : ℂ)‖ + ‖↑t * I‖ := norm_add_le _ _
      _ = |σ| + |t| := by
          rw [Complex.norm_real, Complex.norm_mul, Complex.norm_real,
              Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (|σ| + 1) * |t| := by
          have h1 : |σ| * |t| ≥ |σ| * 1 := mul_le_mul_of_nonneg_left ht (abs_nonneg σ)
          nlinarith
  -- ‖Γ(s+1)‖ = ‖s‖ * ‖Γ(s)‖
  have h_norm_eq : ‖Complex.Gamma (↑(σ+1) + ↑t * I)‖ = ‖s‖ * ‖Complex.Gamma s‖ := by
    rw [← hs1, h_func, norm_mul]
  rw [h_norm_eq]
  have h_bound_s := hbound t ht
  -- |t| * |t|^{σ-1/2} = |t|^{σ+1/2}
  have h_rpow : |t| * |t| ^ (σ - 1/2) = |t| ^ (σ + 1 - 1/2) := by
    rw [show σ + 1 - 1/2 = 1 + (σ - 1/2) from by ring,
        rpow_add ht_pos, rpow_one]
  calc ‖s‖ * ‖Complex.Gamma s‖
      ≤ (|σ| + 1) * |t| * (C * |t| ^ (σ - 1/2) * rexp (-π * |t| / 2)) :=
        mul_le_mul h_s_norm_le h_bound_s (norm_nonneg _) (by positivity)
    _ = (|σ| + 1) * C * (|t| * |t| ^ (σ - 1/2)) * rexp (-π * |t| / 2) := by ring
    _ = (|σ| + 1) * C * |t| ^ (σ + 1 - 1/2) * rexp (-π * |t| / 2) := by
        rw [h_rpow]

/-!
## Step 4: HasGammaUpperGrowth for all σ > 0
-/

private theorem hasGammaUpperGrowth_strip_ext (n : ℕ) (σ : ℝ)
    (hσ₁ : 1/2 ≤ σ) (hσ₂ : σ ≤ 3/2 + ↑n) : HasGammaUpperGrowth σ := by
  induction n generalizing σ with
  | zero => exact hasGammaUpperGrowth_in_strip σ hσ₁ (by push_cast at hσ₂; linarith)
  | succ m ih =>
    by_cases h : σ ≤ 3/2 + ↑m
    · exact ih σ hσ₁ h
    · push_neg at h
      have h_prev := ih (σ - 1) (by linarith) (by push_cast at h hσ₂ ⊢; linarith)
      rw [show σ = (σ - 1) + 1 from by ring]
      exact hasGammaUpperGrowth_step_up (σ - 1) (by linarith) h_prev

theorem hasGammaUpperGrowth_all (σ : ℝ) (hσ : 0 < σ) : HasGammaUpperGrowth σ := by
  by_cases h₁ : σ < 1/2
  · exact hasGammaUpperGrowth_step_down σ hσ
      (hasGammaUpperGrowth_in_strip (σ + 1) (by linarith) (by linarith))
  · push_neg at h₁
    exact hasGammaUpperGrowth_strip_ext ⌈σ - 3/2⌉₊ σ h₁ (by
      have := Nat.le_ceil (σ - 3/2)
      push_cast at this ⊢; linarith)

/-!
## Step 5: HasGammaLowerGrowth stepping
-/

private theorem hasGammaLowerGrowth_step_up (σ : ℝ) (hσ : 0 < σ)
    (h : HasGammaLowerGrowth σ) : HasGammaLowerGrowth (σ + 1) := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun t ht => ?_⟩
  set s := (↑σ + ↑t * I : ℂ) with hs_def
  have hs_ne : s ≠ 0 := by
    intro h_eq; have := congr_arg Complex.re h_eq
    simp [hs_def, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] at this; linarith
  have h_func := Complex.Gamma_add_one s hs_ne
  have hs1 : s + 1 = ↑(σ + 1) + ↑t * I := by
    simp [hs_def, Complex.ofReal_add]; ring
  have ht_pos : (0 : ℝ) < |t| := by linarith
  have h_im_le : |t| ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s
    simp [hs_def, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] at this; linarith
  have h_norm_eq : ‖Complex.Gamma (↑(σ+1) + ↑t * I)‖ = ‖s‖ * ‖Complex.Gamma s‖ := by
    rw [← hs1, h_func, norm_mul]
  rw [h_norm_eq]
  have h_base := hbound t ht
  have h_rpow : |t| * |t| ^ (σ - 1/2) = |t| ^ (σ + 1 - 1/2) := by
    rw [show σ + 1 - 1/2 = 1 + (σ - 1/2) from by ring, rpow_add ht_pos, rpow_one]
  calc C * |t| ^ (σ + 1 - 1/2) * rexp (-π * |t| / 2)
      = C * (|t| * |t| ^ (σ - 1/2)) * rexp (-π * |t| / 2) := by rw [h_rpow]
    _ = |t| * (C * |t| ^ (σ - 1/2) * rexp (-π * |t| / 2)) := by ring
    _ ≤ ‖s‖ * ‖Complex.Gamma s‖ :=
        mul_le_mul h_im_le h_base (by positivity) (norm_nonneg _)

/-!
## Step 5b: HasGammaLowerGrowth on (0, 1) via reflection formula
-/

private theorem hasGammaLowerGrowth_reflection (σ : ℝ) (hσ : 0 < σ) (hσ₁ : σ < 1) :
    HasGammaLowerGrowth σ := by
  -- Γ(s)·Γ(1-s) = π/sin(πs), so |Γ(s)| ≥ π/(|sin(πs)|·|Γ(1-s)|)
  obtain ⟨_, C₂_sin, _, hC₂_sin, hsin⟩ := complex_sin_growth σ
  obtain ⟨C_up, hC_up, h_upper⟩ := hasGammaUpperGrowth_all (1 - σ) (by linarith)
  refine ⟨π / (C₂_sin * C_up), div_pos Real.pi_pos (mul_pos hC₂_sin hC_up), fun t ht => ?_⟩
  set s := (↑σ + ↑t * I : ℂ) with hs_def
  have ht_pos : (0 : ℝ) < |t| := by linarith
  have hre_s : 0 < s.re := by
    simp [hs_def, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]; linarith
  have h_one_sub_re : 0 < (1 - s).re := by
    simp [hs_def, Complex.sub_re, Complex.add_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; linarith
  -- Both Gamma factors nonzero (Re > 0)
  have h_Gs_ne := Complex.Gamma_ne_zero_of_re_pos hre_s
  have h_G1s_ne := Complex.Gamma_ne_zero_of_re_pos h_one_sub_re
  -- sin(πs) ≠ 0: if it were 0, then Γ(s)·Γ(1-s) = π/0 = 0, contradicting nonzero product
  have h_sin_ne : Complex.sin (↑π * s) ≠ 0 := by
    intro h_eq
    have h_prod := Complex.Gamma_mul_Gamma_one_sub s
    rw [h_eq, div_zero] at h_prod
    exact mul_ne_zero h_Gs_ne h_G1s_ne h_prod
  -- Norm product: ‖Γ(s)‖ * ‖Γ(1-s)‖ = π / ‖sin(πs)‖
  have h_norm_prod : ‖Complex.Gamma s‖ * ‖Complex.Gamma (1 - s)‖ =
      π / ‖Complex.sin (↑π * s)‖ := by
    calc ‖Complex.Gamma s‖ * ‖Complex.Gamma (1 - s)‖
        = ‖Complex.Gamma s * Complex.Gamma (1 - s)‖ := (norm_mul _ _).symm
      _ = ‖↑π / Complex.sin (↑π * s)‖ := by rw [Complex.Gamma_mul_Gamma_one_sub]
      _ = π / ‖Complex.sin (↑π * s)‖ := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h_sin_pos : (0 : ℝ) < ‖Complex.sin (↑π * s)‖ := norm_pos_iff.mpr h_sin_ne
  have h_G1s_pos : (0 : ℝ) < ‖Complex.Gamma (1 - s)‖ := norm_pos_iff.mpr h_G1s_ne
  -- Upper bound on sin: ‖sin(πs)‖ ≤ C₂_sin * exp(π|t|)
  have h_sin_upper := (hsin t ht).2
  -- Upper bound on Γ(1-s): 1-s = (1-σ) + (-t)*I
  have h_one_sub_eq : (1 - s) = ↑(1 - σ) + ↑(-t) * I := by
    simp [hs_def, Complex.ofReal_neg, Complex.ofReal_sub]; ring
  have h_gamma_upper : ‖Complex.Gamma (1 - s)‖ ≤
      C_up * |t| ^ ((1 - σ) - 1/2) * rexp (-π * |t| / 2) := by
    rw [h_one_sub_eq]; have := h_upper (-t) (by rwa [abs_neg]); rwa [abs_neg] at this
  -- Product upper bound: ‖sin(πs)‖ * ‖Γ(1-s)‖ ≤ C₂_sin·exp(π|t|)·C_up·|t|^{1/2-σ}·exp(-π|t|/2)
  have h_prod_upper : ‖Complex.sin (↑π * s)‖ * ‖Complex.Gamma (1 - s)‖ ≤
      C₂_sin * rexp (π * |t|) * (C_up * |t| ^ ((1 - σ) - 1/2) * rexp (-π * |t| / 2)) :=
    mul_le_mul h_sin_upper h_gamma_upper (norm_nonneg _) (by positivity)
  -- Key equation: ‖Γ(s)‖ * (‖sin(πs)‖ * ‖Γ(1-s)‖) = π
  have h_prod_pos : (0 : ℝ) < ‖Complex.sin (↑π * s)‖ * ‖Complex.Gamma (1 - s)‖ :=
    mul_pos h_sin_pos h_G1s_pos
  have h_key : ‖Complex.Gamma s‖ * (‖Complex.sin (↑π * s)‖ * ‖Complex.Gamma (1 - s)‖) = π := by
    calc ‖Complex.Gamma s‖ * (‖Complex.sin (↑π * s)‖ * ‖Complex.Gamma (1 - s)‖)
        = ‖Complex.Gamma s‖ * ‖Complex.Gamma (1 - s)‖ * ‖Complex.sin (↑π * s)‖ := by ring
      _ = π / ‖Complex.sin (↑π * s)‖ * ‖Complex.sin (↑π * s)‖ := by rw [h_norm_prod]
      _ = π := div_mul_cancel₀ _ (ne_of_gt h_sin_pos)
  -- Strategy: show C_low * |t|^{σ-1/2} * exp(-π|t|/2) * (‖sin‖*‖Γ(1-s)‖) ≤ π,
  --   then divide by (‖sin‖*‖Γ(1-s)‖) > 0.
  -- Auxiliary: rpow and exp cancellation
  have h_rpow_one : |t| ^ (σ - 1/2) * |t| ^ ((1 - σ) - 1/2) = 1 := by
    rw [← rpow_add (by positivity : (0:ℝ) < |t|)]
    rw [show σ - 1/2 + ((1 - σ) - 1/2) = 0 from by ring, rpow_zero]
  have h_exp_one : rexp (-π * |t| / 2) * (rexp (π * |t|) * rexp (-π * |t| / 2)) = 1 := by
    rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    have : -π * |t| / 2 + π * |t| + -π * |t| / 2 = 0 := by ring
    rw [this, Real.exp_zero]
  -- The product C_low * ... * denom simplifies to π
  have h_prod_simplify :
      π / (C₂_sin * C_up) * |t| ^ (σ - 1/2) * rexp (-π * |t| / 2) *
      (C₂_sin * rexp (π * |t|) * (C_up * |t| ^ ((1 - σ) - 1/2) * rexp (-π * |t| / 2))) = π := by
    have h_coeff : π / (C₂_sin * C_up) * (C₂_sin * C_up) = π :=
      div_mul_cancel₀ _ (ne_of_gt (mul_pos hC₂_sin hC_up))
    calc π / (C₂_sin * C_up) * |t| ^ (σ - 1/2) * rexp (-π * |t| / 2) *
          (C₂_sin * rexp (π * |t|) * (C_up * |t| ^ ((1 - σ) - 1/2) * rexp (-π * |t| / 2)))
        = (π / (C₂_sin * C_up) * (C₂_sin * C_up)) *
          (|t| ^ (σ - 1/2) * |t| ^ ((1 - σ) - 1/2)) *
          (rexp (-π * |t| / 2) * (rexp (π * |t|) * rexp (-π * |t| / 2))) := by ring
      _ = π * 1 * 1 := by rw [h_coeff, h_rpow_one, h_exp_one]
      _ = π := by ring
  -- Now: C_low * ... * (‖sin‖ * ‖Γ(1-s)‖) ≤ C_low * ... * denom = π = ‖Γ(s)‖ * (‖sin‖ * ‖Γ(1-s)‖)
  have h_lhs_le : π / (C₂_sin * C_up) * |t| ^ (σ - 1/2) * rexp (-π * |t| / 2) *
      (‖Complex.sin (↑π * s)‖ * ‖Complex.Gamma (1 - s)‖) ≤ π := by
    calc _ ≤ π / (C₂_sin * C_up) * |t| ^ (σ - 1/2) * rexp (-π * |t| / 2) *
            (C₂_sin * rexp (π * |t|) * (C_up * |t| ^ ((1 - σ) - 1/2) * rexp (-π * |t| / 2))) :=
            mul_le_mul_of_nonneg_left h_prod_upper (by positivity)
      _ = π := h_prod_simplify
  -- Divide by (‖sin‖ * ‖Γ(1-s)‖) > 0 to get C_low * ... ≤ ‖Γ(s)‖
  have h_le_gamma_prod : π / (C₂_sin * C_up) * |t| ^ (σ - 1/2) * rexp (-π * |t| / 2) *
      (‖Complex.sin (↑π * s)‖ * ‖Complex.Gamma (1 - s)‖) ≤
      ‖Complex.Gamma s‖ * (‖Complex.sin (↑π * s)‖ * ‖Complex.Gamma (1 - s)‖) := by
    linarith
  have h_ne := ne_of_gt h_prod_pos
  calc π / (C₂_sin * C_up) * |t| ^ (σ - 1/2) * rexp (-π * |t| / 2)
      = π / (C₂_sin * C_up) * |t| ^ (σ - 1/2) * rexp (-π * |t| / 2) *
        (‖Complex.sin (↑π * s)‖ * ‖Complex.Gamma (1 - s)‖) /
        (‖Complex.sin (↑π * s)‖ * ‖Complex.Gamma (1 - s)‖) :=
          (mul_div_cancel_right₀ _ h_ne).symm
    _ ≤ (‖Complex.Gamma s‖ * (‖Complex.sin (↑π * s)‖ * ‖Complex.Gamma (1 - s)‖)) /
        (‖Complex.sin (↑π * s)‖ * ‖Complex.Gamma (1 - s)‖) :=
          div_le_div_of_nonneg_right h_le_gamma_prod (le_of_lt h_prod_pos)
    _ = ‖Complex.Gamma s‖ := mul_div_cancel_right₀ _ h_ne

/-!
## Step 5c: HasGammaLowerGrowth extending via step-up
-/

private theorem hasGammaLowerGrowth_ext (n : ℕ) (σ : ℝ)
    (hσ₁ : 0 < σ) (hσ₂ : σ ≤ 1 + ↑n) : HasGammaLowerGrowth σ := by
  induction n generalizing σ with
  | zero =>
    push_cast at hσ₂
    by_cases h : σ < 1
    · exact hasGammaLowerGrowth_reflection σ hσ₁ h
    · -- σ = 1: use hasGammaGrowth_one which provides both bounds
      push_neg at h
      have hσ_eq : σ = 1 := by linarith
      rw [hσ_eq]
      obtain ⟨C₁, _, hC₁, _, hboth⟩ := hasGammaGrowth_one
      exact ⟨C₁, hC₁, fun t ht => (hboth t ht).1⟩
  | succ m ih =>
    by_cases h : σ ≤ 1 + ↑m
    · exact ih σ hσ₁ h
    · push_neg at h
      have h_prev := ih (σ - 1) (by linarith) (by push_cast at h hσ₂ ⊢; linarith)
      rw [show σ = (σ - 1) + 1 from by ring]
      exact hasGammaLowerGrowth_step_up (σ - 1) (by linarith) h_prev

theorem hasGammaLowerGrowth_all (σ : ℝ) (hσ : 0 < σ) : HasGammaLowerGrowth σ := by
  exact hasGammaLowerGrowth_ext ⌈σ - 1⌉₊ σ hσ (by
    have := Nat.le_ceil (σ - 1)
    push_cast at this ⊢; linarith)

/-!
## Step 6: HasGammaGrowth for all σ > 0
-/

theorem hasGammaGrowth_all (σ : ℝ) (hσ : 0 < σ) : HasGammaGrowth σ := by
  obtain ⟨C_up, hC_up, h_upper⟩ := hasGammaUpperGrowth_all σ hσ
  obtain ⟨C_low, hC_low, h_lower⟩ := hasGammaLowerGrowth_all σ hσ
  exact ⟨C_low, C_up, hC_low, hC_up, fun t ht => ⟨h_lower t ht, h_upper t ht⟩⟩

end Aristotle.Bridge.GammaGrowthComplete

end
