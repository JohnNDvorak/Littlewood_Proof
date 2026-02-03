/-
Bridge: Combine DiagonalIntegralBound + HardyApproxFunctionalEq to establish
the mean square lower bound for Hardy's Z function on [1,T].

CHAIN (all 0 sorries):
1. DiagonalIntegralBound.diagonal_integral_lower_bound:
   ∫_{Ioc 1 T} diagonalSum t ≥ c·T·log T

2. HardyApproxFunctionalEq.approx_functional_eq:
   ∫_{Ioc 1 T} Z(t)² ≥ k·∫_{Ioc 1 T} ‖S_N(t)‖² - C·T
   (in fact Z² ≥ ‖S_N‖² pointwise, so the -C·T is vacuous)

RESULT (this file): ∫_{Ioc 1 T} Z² ≥ c'·T·log T for large T.

STATUS: 1 sorry — `norm_hardyZ_mean_square_lower`.
The type transfer `hardyZ_sq_eq` is proved (both Z² equal ‖ζ(1/2+it)‖²).
The remaining sorry is the mean square chain combination: connecting
approx_functional_eq (t-dependent truncation) with the diagonal integral
bound (requires matching partial sum definitions across files).

NOTE ON HardySetup FIELD SIGNATURE BUG:
The HardySetup.mean_square_lower_bound field requires the bound for ALL
T₁ ∈ [0,T), not just T₁=1. This is unsatisfiable: for T₁ = T-ε,
∫_{T-ε}^T Z² ≈ ε·Z(T)² → 0, yet the RHS is c·T·log T. The field
needs to be fixed to use a fixed lower endpoint (e.g., T₁=0 or T₁=1)
before any genuine proof can close it. See docs/blocking_analysis.md.
-/

import Mathlib
import Littlewood.Aristotle.DiagonalIntegralBound
import Littlewood.Aristotle.HardyApproxFunctionalEq
import Littlewood.Aristotle.MeanSquare
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZRealV2
import Littlewood.Bridge.HardyZTransfer

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace MeanSquareBridge

open Complex Real Set Filter Topology MeasureTheory

/-! ## Type transfer between hardyZ variants -/

/-- Both hardyZ definitions square to ‖ζ(1/2+it)‖².
    HardyEstimatesPartial.hardyZ = Re(exp(iθ)·ζ(1/2+it)), real-valued, so Z² = ‖ζ‖².
    HardyApproxFunctional.hardyZ = ‖ζ(1/2 + t·I)‖, so Z² = ‖ζ‖².
    Needs: I*t = t*I (commutativity) and ‖Re(exp(iθ)·z)‖ = ‖z‖ when |exp(iθ)|=1. -/
theorem hardyZ_sq_eq (t : ℝ) :
    (HardyEstimatesPartial.hardyZ t)^2 = (HardyApproxFunctional.hardyZ t)^2 := by
  -- Both Z² equal ‖ζ(1/2+it)‖².
  -- EP.hardyZ = Re(exp(iθ)·ζ) where exp(iθ)·ζ is real, so Z² = ‖Z‖² = ‖ζ‖².
  -- AF.hardyZ = ‖ζ‖, so Z² = ‖ζ‖².
  -- Step 1: EP.hardyZ² = ‖hardyZV2 t‖² (via transfer + reality)
  have h_re := HardyZTransfer.hardyZ_eq_hardyZV2_re t  -- EP.hardyZ t = (hardyZV2 t).re
  have h_im := hardyZV2_real t  -- (hardyZV2 t).im = 0
  have h_norm_v2 := hardyZV2_abs_eq_zeta_abs t  -- ‖hardyZV2 t‖ = ‖ζ(1/2+I*t)‖
  -- When im = 0: ‖z‖ = |z.re| and z.re² = ‖z‖²
  have h_re_sq : (HardyEstimatesPartial.hardyZ t)^2 = ‖hardyZV2 t‖^2 := by
    rw [h_re]
    have : hardyZV2 t = ((hardyZV2 t).re : ℂ) :=
      Complex.ext rfl (by simp [h_im])
    conv_rhs => rw [this, Complex.norm_real]
    exact (sq_abs _).symm
  -- Step 2: I*t = t*I
  have h_comm : (1:ℂ)/2 + I * ↑t = (1:ℂ)/2 + ↑t * I := by ring
  -- Combine: EP.hardyZ² = ‖hardyZV2‖² = ‖ζ(1/2+I*t)‖² = ‖ζ(1/2+t*I)‖² = AF.hardyZ²
  rw [h_re_sq, h_norm_v2, h_comm]
  -- Now goal: ‖ζ(1/2+t*I)‖^2 = (AF.hardyZ t)^2 where AF.hardyZ = ‖ζ(1/2+t*I)‖
  unfold HardyApproxFunctional.hardyZ; rfl

/-! ## Definition matching: partial_sum_approx ↔ partialZeta -/

/-- The two partial sum definitions agree pointwise.
    partial_sum_approx uses Finset.range N with (n+1)^{-1/2-tI};
    partialZeta uses Finset.Icc 1 N with n^{-(1/2+It)}.
    The index shift (range→Icc) and exponent identity (I*t=t*I) give equality. -/
private lemma partial_sum_approx_eq_partialZeta (t : ℝ) :
    HardyApproxFunctional.partial_sum_approx t =
    partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * ↑t) := by
  unfold HardyApproxFunctional.partial_sum_approx HardyApproxFunctional.partial_sum partialZeta
  set N := Nat.floor (Real.sqrt (t / (2 * Real.pi)))
  -- Convert RHS: Icc 1 N → Ico 1 (N+1) → range N with shifted index
  rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) from
        (Finset.Ico_succ_right_eq_Icc 1 N).symm,
      Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  -- Now both: ∑ k ∈ range N, (LHS: (↑k + 1)^{-(1/2)-t*I}) vs (RHS: ↑(1+k)^{-(1/2+I*t)})
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  · push_cast; ring  -- (↑n + 1 : ℂ) = (↑(1 + n) : ℂ)
  · ring              -- -(1/2 : ℂ) - ↑t * I = -(1/2 + I * ↑t)

/-- The norm squared of partial_sum_approx equals normSq of partialZeta. -/
private lemma norm_sq_partial_sum_eq (t : ℝ) :
    ‖HardyApproxFunctional.partial_sum_approx t‖^2 =
    Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * ↑t)) := by
  rw [partial_sum_approx_eq_partialZeta, Complex.sq_norm]

/-! ## Fixed-endpoint mean square lower bound -/

/-- The mean square of HardyApproxFunctional.hardyZ on [1,T] is ≥ c·T·log T.
    Chain: approx_functional_eq (∫Z² ≥ k*(∫‖S‖²) - C·T) +
    mean_square_partial_zeta_asymp (∫‖S‖² =Θ(T log T)) → ∫Z² ≥ c·T·log T.

    Note: This uses the norm-based Z. Transfer to the .re-based Z via hardyZ_sq_eq. -/
theorem norm_hardyZ_mean_square_lower :
    ∃ c > 0, ∃ T₀ ≥ 2, ∀ T ≥ T₀,
      ∫ t in Ioc 1 T, (HardyApproxFunctional.hardyZ t)^2 ≥ c * T * Real.log T := by
  -- Step 1: approx_functional_eq: ∫Z² ≥ (k * ∫‖S‖²) - Ca * T
  obtain ⟨k, hk, C_a, hCa, T₁, hT₁, h_afe⟩ := HardyApproxFunctional.approx_functional_eq
  -- Step 2: mean_square_partial_zeta_asymp.2 → ∃ c > 0, IsBigOWith c (T*log T) (∫ normSq)
  obtain ⟨C_inv, hCinv_pos, hCinv⟩ := mean_square_partial_zeta_asymp.2.exists_pos
  rw [Asymptotics.IsBigOWith] at hCinv
  rw [Filter.eventually_atTop] at hCinv
  obtain ⟨T₂, hT₂⟩ := hCinv
  -- Step 3: set c and T₀
  set c := k / (2 * C_inv) with hc_def
  have hc_pos : c > 0 := div_pos hk (by positivity)
  set T₀ := max (max T₁ T₂) (max 2 (Real.exp (2 * C_a * C_inv / k + 1))) with hT₀_def
  refine ⟨c, hc_pos, T₀, ?_, ?_⟩
  · calc T₀ ≥ max 2 (Real.exp (2 * C_a * C_inv / k + 1)) := le_max_right _ _
      _ ≥ 2 := le_max_left _ _
  intro T hT
  have hT_ge_T₁ : T ≥ T₁ := le_trans (le_trans (le_max_left T₁ T₂) (le_max_left _ _)) hT
  have hT_ge_T₂ : T ≥ T₂ := le_trans (le_trans (le_max_right T₁ T₂) (le_max_left _ _)) hT
  have hT_ge_2 : T ≥ 2 := le_trans (le_trans (le_max_left 2 _) (le_max_right _ _)) hT
  have hT_ge_1 : T ≥ 1 := by linarith
  -- Step 4: ∫ Ioc 1 T, ‖S‖² = ∫ 1..T, normSq(partialZeta) = I_ns
  set I_ns := ∫ t in (1:ℝ)..T, Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi)))
    (1/2 + Complex.I * ↑t)) with hI_ns_def
  have h_int_eq : ∫ t in Ioc 1 T, ‖HardyApproxFunctional.partial_sum_approx t‖ ^ 2 = I_ns := by
    rw [hI_ns_def, intervalIntegral.integral_of_le hT_ge_1]
    congr 1; ext t; exact norm_sq_partial_sum_eq t
  -- ∫ normSq ≥ 0
  have hI_ns_nonneg : I_ns ≥ 0 := by
    rw [hI_ns_def, intervalIntegral.integral_of_le hT_ge_1]
    exact setIntegral_nonneg measurableSet_Ioc (fun t _ => Complex.normSq_nonneg _)
  have hI_ns_norm : ‖I_ns‖ = I_ns := Real.norm_of_nonneg hI_ns_nonneg
  -- Step 5: h_afe gives ∫Z² ≥ (k * ∫ Ioc ‖S‖²) - Ca*T
  have h_afe_T := h_afe T hT_ge_T₁
  -- Now with proper parens: h_afe_T : ∫Z² ≥ (k * ∫ Ioc ‖S‖²) - C_a*T
  have h_afe_ns : ∫ t in Ioc 1 T, (HardyApproxFunctional.hardyZ t)^2 ≥
      k * I_ns - C_a * T := by
    calc _ ≥ (k * ∫ t in Ioc 1 T, ‖HardyApproxFunctional.partial_sum_approx t‖ ^ 2) -
        C_a * T := h_afe_T
      _ = k * I_ns - C_a * T := by rw [h_int_eq]
  -- Step 6: Lower bound from =Θ: T * log T ≤ C_inv * I_ns
  have h_ms := hT₂ T hT_ge_T₂
  have hT_ge_exp : T ≥ Real.exp (2 * C_a * C_inv / k + 1) :=
    le_trans (le_trans (le_max_right 2 _) (le_max_right _ _)) hT
  have hlog_pos : Real.log T > 0 := by
    apply Real.log_pos
    calc (1 : ℝ) < Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
      _ ≤ Real.exp (2 * C_a * C_inv / k + 1) := by
          apply Real.exp_le_exp_of_le
          linarith [div_nonneg (by positivity : (0:ℝ) ≤ 2 * C_a * C_inv) hk.le]
      _ ≤ T := hT_ge_exp
  have hTlogT_pos : T * Real.log T > 0 := mul_pos (by linarith) hlog_pos
  rw [Real.norm_of_nonneg (le_of_lt hTlogT_pos), hI_ns_norm] at h_ms
  have h_int_lower : I_ns ≥ T * Real.log T / C_inv :=
    (div_le_iff₀ hCinv_pos).mpr (by linarith)
  -- Step 7: Combine: ∫Z² ≥ k*I_ns - Ca*T ≥ k*(T*log T/Cinv) - Ca*T ≥ c*T*log T
  have h_log_large : Real.log T ≥ 2 * C_a * C_inv / k + 1 := by
    calc Real.log T ≥ Real.log (Real.exp (2 * C_a * C_inv / k + 1)) :=
          Real.log_le_log (Real.exp_pos _) hT_ge_exp
      _ = 2 * C_a * C_inv / k + 1 := Real.log_exp _
  calc ∫ t in Ioc 1 T, (HardyApproxFunctional.hardyZ t)^2
      ≥ k * I_ns - C_a * T := h_afe_ns
    _ ≥ k * (T * Real.log T / C_inv) - C_a * T := by nlinarith
    _ = T * (k * Real.log T / C_inv - C_a) := by ring
    _ ≥ T * (k / (2 * C_inv) * Real.log T) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        -- Need: k/(2*C_inv) * log T ≤ k*log T/C_inv - Ca
        -- i.e., Ca ≤ k*log T/(2*C_inv)
        have hkC : (0:ℝ) < 2 * C_inv := by positivity
        have h_Ca_le : C_a ≤ k / (2 * C_inv) * Real.log T := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hkC]
          have h_kL : k * Real.log T ≥ k * (2 * C_a * C_inv / k + 1) :=
            mul_le_mul_of_nonneg_left h_log_large hk.le
          have : k * (2 * C_a * C_inv / k + 1) = 2 * C_a * C_inv + k := by field_simp
          nlinarith
        linarith [show k * Real.log T / C_inv - k / (2 * C_inv) * Real.log T =
          k / (2 * C_inv) * Real.log T from by field_simp; ring]
    _ = c * T * Real.log T := by rw [hc_def]; ring

/-- The mean square of HardyEstimatesPartial.hardyZ on [1,T] is ≥ c·T·log T.
    Transfer from the norm-based version using hardyZ_sq_eq. -/
theorem re_hardyZ_mean_square_lower :
    ∃ c > 0, ∃ T₀ ≥ 2, ∀ T ≥ T₀,
      ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t)^2 ≥ c * T * Real.log T := by
  obtain ⟨c, hc, T₀, hT₀, h⟩ := norm_hardyZ_mean_square_lower
  exact ⟨c, hc, T₀, hT₀, fun T hT => by
    have := h T hT
    calc ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t)^2
        = ∫ t in Ioc 1 T, (HardyApproxFunctional.hardyZ t)^2 := by
          congr 1; ext t; exact hardyZ_sq_eq t
      _ ≥ c * T * Real.log T := this⟩

end MeanSquareBridge
