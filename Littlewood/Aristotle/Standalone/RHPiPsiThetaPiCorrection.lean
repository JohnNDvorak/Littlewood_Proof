/-
# Constructive helper lemmas for the θ/prime-power correction route

Decomposes the Gap A correction `piLiErr - ((ψ-x)/logx - √x/logx)` into:
1. `thetaPiLiRemainder` (the Abel summation integral remainder)
2. `(θ(√x) - √x)/logx` (the prime-power k=2 correction)
3. Higher prime-power tail k≥3 (bounded constructively here)

The conditional assembly `pi_li_from_psi_correction_of_bounds` provides the
full O(√x/(logx)²) bound given hypotheses on terms 1 and 2.

This file does NOT touch any active wiring files.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ThetaToPiLiTransferInfra
import Littlewood.Aristotle.PsiThetaCanonicalBound
import Littlewood.Aristotle.PsiThetaBound
import Littlewood.Aristotle.Standalone.AbelSummationPsiPi
import Littlewood.Aristotle.Standalone.RHPiZeroSumAlignmentBridge

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.RHPiPsiThetaPiCorrection

open Real Filter Asymptotics Finset
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.ThetaToPiLiTransferInfra
open Aristotle.PsiThetaCanonicalBound

/-! ## Section 1: Definitional bridges -/

private lemma dirichlet_psi_eq_local (x : ℝ) :
    Aristotle.DirichletPhaseAlignment.chebyshevPsi x = PsiThetaBound.psi x := by
  unfold Aristotle.DirichletPhaseAlignment.chebyshevPsi PsiThetaBound.psi; rfl

lemma dirichlet_psi_eq_canonical (x : ℝ) :
    Aristotle.DirichletPhaseAlignment.chebyshevPsi x = chebyshevPsi x := by
  rw [dirichlet_psi_eq_local, psi_eq_chebyshevPsi]

lemma piLiErr_eq_theta_main_plus_remainder (x : ℝ) (hx : 2 < x) :
    piLiErr x = (chebyshevTheta x - x) / Real.log x + thetaPiLiRemainder x := by
  unfold piLiErr; exact pi_li_eq_theta_main_plus_remainder x hx

lemma canonical_psi_sub_theta_eq_sum (x : ℝ) (hx : 2 ≤ x) :
    chebyshevPsi x - chebyshevTheta x =
      ∑ k ∈ Finset.Icc 2 (Nat.floor (Real.logb 2 x)),
        chebyshevTheta (x ^ (1 / k : ℝ)) := by
  have h := PsiThetaBound.psi_sub_theta_eq_sum_k_ge_2 x hx
  rw [psi_eq_chebyshevPsi, theta_eq_chebyshevTheta] at h
  simp_rw [theta_eq_chebyshevTheta] at h; exact h

/-! ## Section 2: Tail infrastructure -/

lemma tail_nonneg (x : ℝ) :
    0 ≤ ∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
      chebyshevTheta (x ^ (1 / k : ℝ)) :=
  Finset.sum_nonneg (fun _ _ => Chebyshev.theta_nonneg _)

/-- For k ∈ Icc 3 ⌊log₂x⌋ with x ≥ 4: x^{1/k} ≥ 2. -/
private lemma rpow_inv_ge_two (x : ℝ) (hx : 4 ≤ x) (k : ℕ)
    (hk : k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x))) :
    2 ≤ x ^ (1 / (k : ℝ)) := by
  have hk_bounds := Finset.mem_Icc.mp hk
  have hk3 : 3 ≤ k := hk_bounds.1
  have hk_le : k ≤ Nat.floor (Real.logb 2 x) := hk_bounds.2
  have hx_pos : 0 < x := by linarith
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  -- k ≤ ⌊log₂x⌋ ≤ log₂x, so 2^(k:ℝ) ≤ x
  have hk_le_logb : (k : ℝ) ≤ Real.logb 2 x :=
    le_trans (Nat.cast_le.mpr hk_le)
      (Nat.floor_le (Real.logb_nonneg (by norm_num) (by linarith)))
  have h2k_le_x : (2 : ℝ) ^ (k : ℝ) ≤ x := by
    calc (2 : ℝ) ^ (k : ℝ)
        ≤ (2 : ℝ) ^ (Real.logb 2 x) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hk_le_logb
      _ = x := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  -- ((2:ℝ)^(k:ℝ))^(1/k) ≤ x^(1/k) by monotonicity
  have h_mono : ((2 : ℝ) ^ (k : ℝ)) ^ (1 / (k : ℝ)) ≤ x ^ (1 / (k : ℝ)) :=
    Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h2k_le_x (by positivity)
  -- ((2:ℝ)^(k:ℝ))^(1/k) = 2^(k·(1/k)) = 2^1 = 2
  have h_simp : ((2 : ℝ) ^ (k : ℝ)) ^ (1 / (k : ℝ)) = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        show (k : ℝ) * (1 / (k : ℝ)) = 1 from mul_div_cancel₀ _ (ne_of_gt hk_pos),
        Real.rpow_one]
  linarith

/-- The k≥3 tail bounded by (2/log2)·logx·x^{1/3}.
This is the key per-term bound using PsiThetaBound.theta_le_two_mul. -/
theorem tail_le_logx_times_cube_root (x : ℝ) (hx : 4 ≤ x) :
    ∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
      chebyshevTheta (x ^ (1 / k : ℝ)) ≤
    2 * (Real.logb 2 x * x ^ (1 / 3 : ℝ)) := by
  calc ∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
          chebyshevTheta (x ^ (1 / k : ℝ))
      ≤ ∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
          2 * x ^ (1 / k : ℝ) := by
        apply Finset.sum_le_sum; intro k hk
        rw [← theta_eq_chebyshevTheta]
        exact le_trans (PsiThetaBound.theta_le_two_mul _ (rpow_inv_ge_two x hx k hk))
          (by nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ x) (1/(k:ℝ))])
    _ = 2 * ∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
          x ^ (1 / k : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 2 * (Real.logb 2 x * x ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (PsiThetaBound.sum_pow_le_log_mul_pow_third x (by linarith)) (by norm_num)

/-- (logx)² ≤ x^{1/6} eventually. From log = o(x^{1/12}). -/
private lemma log_sq_le_rpow_sixth_eventually :
    ∀ᶠ x in atTop, (Real.log x) ^ 2 ≤ x ^ (1 / 6 : ℝ) := by
  have h := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 12 by norm_num)
  have h1 := h.def (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h1, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx_pos : 0 < x := by linarith
  rw [one_mul] at hx
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hrpow_nn : 0 ≤ x ^ ((1 : ℝ) / 12) := Real.rpow_nonneg hx_pos.le _
  have hlog_le : Real.log x ≤ x ^ ((1 : ℝ) / 12) := by
    calc Real.log x = ‖Real.log x‖ := (Real.norm_of_nonneg hlog_nn).symm
      _ ≤ ‖x ^ ((1 : ℝ) / 12)‖ := hx
      _ = x ^ ((1 : ℝ) / 12) := Real.norm_of_nonneg hrpow_nn
  calc (Real.log x) ^ 2 ≤ (x ^ ((1 : ℝ) / 12)) ^ 2 := by nlinarith
    _ = x ^ (1 / 6 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]; norm_num

/-- Hypothesis 3: The k≥3 tail divided by logx is eventually O(√x/(logx)²). -/
theorem tail_hypothesis :
    ∃ C₃ > (0 : ℝ), ∀ᶠ x in atTop,
      (∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
          chebyshevTheta (x ^ (1 / k : ℝ))) / Real.log x ≤
        C₃ * (Real.sqrt x / (Real.log x) ^ 2) := by
  refine ⟨4, by norm_num, ?_⟩
  filter_upwards [log_sq_le_rpow_sixth_eventually,
                   Filter.eventually_ge_atTop (4 : ℝ),
                   AbelSummationPsiPi.log_eventually_pos]
    with x h_logsq hx4 hlog_pos
  have hx_pos : 0 < x := by linarith
  have hlog_sq_pos : 0 < (Real.log x) ^ 2 := sq_pos_of_pos hlog_pos
  -- x^{1/3}·(logx)² ≤ x^{1/3}·x^{1/6} = x^{1/2} = √x
  have h_cube_root_bound : x ^ (1 / 3 : ℝ) * (Real.log x) ^ 2 ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    calc x ^ (1 / 3 : ℝ) * (Real.log x) ^ 2
        ≤ x ^ (1 / 3 : ℝ) * x ^ (1 / 6 : ℝ) :=
          mul_le_mul_of_nonneg_left h_logsq (Real.rpow_nonneg hx_pos.le _)
      _ = x ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hx_pos]; norm_num
  have h_tail := tail_le_logx_times_cube_root x hx4
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt_nn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  -- 2/log2 ≤ 4 since log2 > 0.693 > 0.5
  have h_ratio : 2 / Real.log 2 ≤ 4 := by
    rw [div_le_iff₀ hlog2_pos]; linarith [Real.log_two_gt_d9]
  -- Transform: tail/logx ≤ 4·√x/(logx)² ↔ tail·logx ≤ 4·√x (clear denominators)
  rw [div_le_iff₀ hlog_pos]
  have h_rhs : 4 * (Real.sqrt x / (Real.log x) ^ 2) * Real.log x =
      4 * Real.sqrt x / Real.log x := by
    field_simp [ne_of_gt hlog_pos]
  rw [h_rhs, le_div_iff₀ hlog_pos]
  -- Goal: tail · logx ≤ 4 · √x
  have key : 2 / Real.log 2 * (x ^ (1 / 3 : ℝ) * (Real.log x) ^ 2) ≤ 4 * Real.sqrt x :=
    calc 2 / Real.log 2 * (x ^ (1 / 3 : ℝ) * (Real.log x) ^ 2)
        ≤ 2 / Real.log 2 * Real.sqrt x :=
          mul_le_mul_of_nonneg_left h_cube_root_bound (by positivity)
      _ ≤ 4 * Real.sqrt x :=
          mul_le_mul_of_nonneg_right h_ratio hsqrt_nn
  calc (∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
          chebyshevTheta (x ^ (1 / k : ℝ))) * Real.log x
      ≤ (2 * (Real.logb 2 x * x ^ (1 / 3 : ℝ))) * Real.log x :=
        mul_le_mul_of_nonneg_right h_tail hlog_pos.le
    _ = 2 / Real.log 2 * (x ^ (1 / 3 : ℝ) * (Real.log x) ^ 2) := by
        rw [show Real.logb 2 x = Real.log x / Real.log 2 from rfl]; ring
    _ ≤ 4 * Real.sqrt x := key

/-! ## Section 3: Algebraic decomposition -/

private lemma sum_icc_split (x : ℝ) (hx : 4 ≤ x) :
    ∑ k ∈ Finset.Icc 2 (Nat.floor (Real.logb 2 x)),
      chebyshevTheta (x ^ (1 / k : ℝ)) =
    chebyshevTheta (x ^ (1 / 2 : ℝ)) +
    ∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
      chebyshevTheta (x ^ (1 / k : ℝ)) := by
  have h2le : 2 ≤ Nat.floor (Real.logb 2 x) := by
    rw [Nat.le_floor_iff (Real.logb_nonneg (by norm_num) (by linarith))]
    exact (Real.le_logb_iff_rpow_le (by norm_num) (by linarith)).mpr (by norm_num; linarith)
  have h_eq : Finset.Icc 2 (Nat.floor (Real.logb 2 x)) =
      {2} ∪ Finset.Icc 3 (Nat.floor (Real.logb 2 x)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
  have h_disj : Disjoint ({2} : Finset ℕ) (Finset.Icc 3 (Nat.floor (Real.logb 2 x))) := by
    simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_Icc]; intro k hk; omega
  rw [h_eq, Finset.sum_union h_disj, Finset.sum_singleton]; norm_cast

private lemma rpow_half_eq_sqrt (x : ℝ) (_hx : 0 ≤ x) :
    x ^ (1 / 2 : ℝ) = Real.sqrt x := by
  rw [show (1 : ℝ) / 2 = 1 / 2 from rfl, ← Real.sqrt_eq_rpow]

theorem correction_decomposition (x : ℝ) (hx : 4 ≤ x) :
    piLiErr x - ((Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) /
      Real.log x - Real.sqrt x / Real.log x) =
    thetaPiLiRemainder x
      - (chebyshevTheta (Real.sqrt x) - Real.sqrt x) / Real.log x
      - (∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
          chebyshevTheta (x ^ (1 / k : ℝ))) / Real.log x := by
  have h_pi := piLiErr_eq_theta_main_plus_remainder x (by linarith)
  have h_psi := dirichlet_psi_eq_canonical x
  have h_decomp := canonical_psi_sub_theta_eq_sum x (by linarith)
  have h_split := sum_icc_split x hx
  have h_sqrt := rpow_half_eq_sqrt x (by linarith)
  rw [h_pi, h_psi]
  have key : chebyshevPsi x - x =
      (chebyshevTheta x - x) + (chebyshevPsi x - chebyshevTheta x) := by ring
  rw [key, h_decomp, h_split, h_sqrt]; ring

/-! ## Section 4: Conditional assembly -/

private lemma abs_sub_sub_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| := by
  have h1 : a - b - c = a + (-(b + c)) := by ring
  calc |a - b - c| = |a + (-(b + c))| := congr_arg _ h1
    _ ≤ |a| + |-(b + c)| := abs_add_le a (-(b + c))
    _ = |a| + |b + c| := by rw [abs_neg]
    _ ≤ |a| + (|b| + |c|) := by linarith [abs_add_le b c]
    _ = |a| + |b| + |c| := by ring

theorem pi_li_from_psi_correction_of_bounds
    (h_remainder : ∃ C₁ > (0 : ℝ), ∀ᶠ x in atTop,
        |thetaPiLiRemainder x| ≤ C₁ * (Real.sqrt x / (Real.log x) ^ 2))
    (h_theta_sqrt_div : ∃ C₂ > (0 : ℝ), ∀ᶠ x in atTop,
        |(chebyshevTheta (Real.sqrt x) - Real.sqrt x) / Real.log x| ≤
          C₂ * (Real.sqrt x / (Real.log x) ^ 2))
    (h_tail : ∃ C₃ > (0 : ℝ), ∀ᶠ x in atTop,
        (∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
            chebyshevTheta (x ^ (1 / k : ℝ))) / Real.log x ≤
          C₃ * (Real.sqrt x / (Real.log x) ^ 2)) :
    ∃ D > (0 : ℝ), ∀ᶠ x in atTop,
      1 < x ∧
      |piLiErr x - ((Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) /
        Real.log x - Real.sqrt x / Real.log x)| ≤
        D * (Real.sqrt x / (Real.log x) ^ 2) := by
  obtain ⟨C₁, hC₁_pos, h_rem⟩ := h_remainder
  obtain ⟨C₂, hC₂_pos, h_theta⟩ := h_theta_sqrt_div
  obtain ⟨C₃, hC₃_pos, h_tail_ev⟩ := h_tail
  refine ⟨C₁ + C₂ + C₃, by linarith, ?_⟩
  filter_upwards [h_rem, h_theta, h_tail_ev,
       Filter.eventually_ge_atTop (4 : ℝ),
       AbelSummationPsiPi.log_eventually_pos]
      with x h_rem_x h_theta_x h_tail_x hx4 hlog_pos
  refine ⟨by linarith, ?_⟩
  rw [correction_decomposition x hx4]
  have h_tail_abs :
      |(∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
          chebyshevTheta (x ^ (1 / k : ℝ))) / Real.log x| ≤
        C₃ * (Real.sqrt x / (Real.log x) ^ 2) := by
    rw [abs_of_nonneg (div_nonneg (tail_nonneg x) hlog_pos.le)]; exact h_tail_x
  calc |thetaPiLiRemainder x -
          (chebyshevTheta (Real.sqrt x) - Real.sqrt x) / Real.log x -
          (∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
            chebyshevTheta (x ^ (1 / k : ℝ))) / Real.log x|
      ≤ |thetaPiLiRemainder x| +
        |(chebyshevTheta (Real.sqrt x) - Real.sqrt x) / Real.log x| +
        |(∑ k ∈ Finset.Icc 3 (Nat.floor (Real.logb 2 x)),
            chebyshevTheta (x ^ (1 / k : ℝ))) / Real.log x| :=
          abs_sub_sub_le _ _ _
    _ ≤ C₁ * (Real.sqrt x / (Real.log x) ^ 2) +
        C₂ * (Real.sqrt x / (Real.log x) ^ 2) +
        C₃ * (Real.sqrt x / (Real.log x) ^ 2) :=
          add_le_add (add_le_add h_rem_x h_theta_x) h_tail_abs
    _ = (C₁ + C₂ + C₃) * (Real.sqrt x / (Real.log x) ^ 2) := by ring

end Aristotle.Standalone.RHPiPsiThetaPiCorrection
