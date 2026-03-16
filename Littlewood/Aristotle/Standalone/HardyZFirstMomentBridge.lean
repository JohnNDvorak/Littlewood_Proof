/-
Bridge for the Hardy Z first moment bound: |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2}.

PROOF STRUCTURE:
  Z(t) = MainTerm(t) + ErrorTerm(t). The sorry is reduced to a single
  per-mode uniform VdC bound (Van der Corput oscillatory cancellation).

  (A) |∫ ErrorTerm| ≤ C_E·√T: from RSExpansionProof.errorTerm_first_moment_sqrt.
  (B) |∫ MainTerm| ≤ C_M·√T: via per-mode VdC + hardyN ≤ √T.

Reference: Titchmarsh 1951 §4.15; Ingham 1932 §5.2; Ivić 2003 §4.2.
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.Standalone.RSExpansionProof

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set

namespace Aristotle.Standalone.HardyZFirstMomentBridge

open HardyEstimatesPartial

/-- Per-mode uniform VdC bound: |∫ hardyCos_n| ≤ B for all n and T ≥ 2. -/
private theorem per_mode_uniform_vdc_bound :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc (hardyStart n) T, hardyCos n t| ≤ B := by
  sorry

private lemma rpow_neg_half_le_one' (n : ℕ) :
    (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
  calc (n + 1 : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ (1 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
    _ = 1 := by simp [Real.one_rpow]

private theorem mainTerm_first_moment_sqrt
    (hmode : ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc (hardyStart n) T, hardyCos n t| ≤ B) :
    ∃ C_M > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_M * T ^ ((1 : ℝ) / 2) := by
  obtain ⟨B, hB, hmode_bd⟩ := hmode
  refine ⟨2 * B, by positivity, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have h_main_eq : ∫ t in Ioc 1 T, MainTerm t = hardySumInt T := by
    rw [show (fun t => MainTerm t) = hardySum from MainTerm_eq_hardySum]
    exact hardySum_integral_eq T hT1
  rw [h_main_eq]; unfold hardySumInt
  rw [abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
  have h_sum_le : |∑ n ∈ Finset.range (hardyN T),
      ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
        ∫ t in Ioc (hardyStart n) T, hardyCos n t| ≤
      B * (hardyN T : ℝ) := by
    calc |∑ n ∈ Finset.range (hardyN T),
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (hardyStart n) T, hardyCos n t|
        ≤ ∑ n ∈ Finset.range (hardyN T),
          |((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (hardyStart n) T, hardyCos n t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.range (hardyN T), B := by
          apply Finset.sum_le_sum; intro n _hn
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)))]
          calc (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
                |∫ t in Ioc (hardyStart n) T, hardyCos n t|
              ≤ 1 * B :=
                mul_le_mul (rpow_neg_half_le_one' n) (hmode_bd n T hT) (abs_nonneg _) zero_le_one
            _ = B := one_mul B
      _ = (hardyN T : ℝ) * B := by simp [Finset.sum_const, Finset.card_range]
      _ = B * (hardyN T : ℝ) := mul_comm _ _
  have hN_le : (hardyN T : ℝ) ≤ T ^ ((1 : ℝ) / 2) := by
    linarith [Aristotle.HardyNProperties.hardyN_le_sqrt T hT]
  calc 2 * |∑ n ∈ Finset.range (hardyN T),
        ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
          ∫ t in Ioc (hardyStart n) T, hardyCos n t|
      ≤ 2 * (B * (hardyN T : ℝ)) :=
        mul_le_mul_of_nonneg_left h_sum_le (by norm_num)
    _ ≤ 2 * (B * T ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hN_le (le_of_lt hB)) (by norm_num)
    _ = 2 * B * T ^ ((1 : ℝ) / 2) := by ring

/-- **Hardy Z first moment O(√T) bridge**.
    |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2} for all T ≥ 2.
    Downstream: HardyZFirstMomentIBP.hardyZ_first_moment_sublinear. -/
theorem hardyZ_first_moment_sqrt :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, hardyZ t| ≤ C * T ^ ((1 : ℝ) / 2) := by
  obtain ⟨C_E, hCE, h_error⟩ :=
    Aristotle.Standalone.RSExpansionProof.errorTerm_first_moment_sqrt
  obtain ⟨C_M, hCM, h_main⟩ := mainTerm_first_moment_sqrt per_mode_uniform_vdc_bound
  refine ⟨C_M + C_E, by positivity, fun T hT => ?_⟩
  have h_Z_split : ∀ t, hardyZ t = MainTerm t + ErrorTerm t := fun t => by
    unfold ErrorTerm; ring
  have h_main_intble : IntegrableOn MainTerm (Ioc 1 T) := mainTerm_integrable T
  have h_error_intble : IntegrableOn ErrorTerm (Ioc 1 T) := errorTerm_integrable T
  have h_int_eq : ∫ t in Ioc 1 T, hardyZ t =
      (∫ t in Ioc 1 T, MainTerm t) + (∫ t in Ioc 1 T, ErrorTerm t) := by
    rw [show (fun t => hardyZ t) = (fun t => MainTerm t + ErrorTerm t) from
      funext h_Z_split]
    exact integral_add h_main_intble h_error_intble
  calc |∫ t in Ioc 1 T, hardyZ t|
      = |(∫ t in Ioc 1 T, MainTerm t) + (∫ t in Ioc 1 T, ErrorTerm t)| := by
        rw [h_int_eq]
    _ ≤ |∫ t in Ioc 1 T, MainTerm t| + |∫ t in Ioc 1 T, ErrorTerm t| :=
        abs_add_le _ _
    _ ≤ C_M * T ^ ((1 : ℝ) / 2) + C_E * T ^ ((1 : ℝ) / 2) := by
        linarith [h_main T hT, h_error T hT]
    _ = (C_M + C_E) * T ^ ((1 : ℝ) / 2) := by ring

end Aristotle.Standalone.HardyZFirstMomentBridge
