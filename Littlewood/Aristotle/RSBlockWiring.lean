/-
Wiring layer from `RiemannSiegelBoundProp` to the crude
`ErrorTerm` first-moment bound `O(T^(3/4))`.

This file does not prove the deep Riemann-Siegel sign structure; it only
packages the pointwise RS-size input into the block-amplitude/global-crude
integral bound pipeline.
-/

import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.RiemannSiegelBound
import Littlewood.Aristotle.IntervalPartition

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.RSBlockWiring

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-- The local Riemann-Siegel approximation error used in
`Aristotle.RiemannSiegelBound.RiemannSiegelBoundProp`. -/
noncomputable def rsApproxError (t : ℝ) : ℝ :=
  ‖Aristotle.RiemannSiegelBound.hardyZ t -
      2 *
        (Complex.exp (Complex.I * Aristotle.RiemannSiegelBound.hardyTheta t) *
          Aristotle.RiemannSiegelBound.hardySum
            (Int.natAbs ⌊Real.sqrt (t / (2 * Real.pi))⌋) t).re‖

/-- Bridge hypothesis from the local RS approximation expression to the
project `ErrorTerm`. -/
class ErrorTermRsApproxBridgeHyp : Prop where
  bound : ∀ t : ℝ, t ≥ 2 → |ErrorTerm t| ≤ rsApproxError t

/-- Pointwise `t^(-1/4)` bound for `ErrorTerm` on `[2,∞)` obtained by wiring
`ErrorTermRsApproxBridgeHyp` with `RiemannSiegelBoundProp`. -/
lemma errorTerm_pointwise_quarter_on_ge_two
    [Aristotle.RiemannSiegelBound.RiemannSiegelBoundProp]
    [ErrorTermRsApproxBridgeHyp] :
    ∃ C_rs > 0, ∀ t : ℝ, t ≥ 2 →
      |ErrorTerm t| ≤ C_rs * t ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨C_rs, hC_rs, hRS⟩ :=
    Aristotle.RiemannSiegelBound.RiemannSiegelBoundProp.bound
  refine ⟨C_rs, hC_rs, ?_⟩
  intro t ht
  have hBridge : |ErrorTerm t| ≤ rsApproxError t :=
    ErrorTermRsApproxBridgeHyp.bound t ht
  have hRS_t : rsApproxError t ≤ C_rs * t ^ (-(1 / 4 : ℝ)) := by
    simpa [rsApproxError] using hRS t ht
  exact le_trans hBridge hRS_t

/-- Crude global first-moment bound for `ErrorTerm`, wired from
`RiemannSiegelBoundProp` plus a bridge hypothesis.

This yields `|∫_1^T ErrorTerm| = O(T^(3/4))` for `T ≥ 2`. -/
theorem errorTerm_first_moment_crude_wired
    [Aristotle.RiemannSiegelBound.RiemannSiegelBoundProp]
    [ErrorTermRsApproxBridgeHyp] :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, ErrorTerm t| ≤ C * T ^ (3 / 4 : ℝ) := by
  obtain ⟨C_rs, hC_rs, hpoint2⟩ := errorTerm_pointwise_quarter_on_ge_two

  let K : ℝ := |∫ t in Ioc 1 (2 : ℝ), ErrorTerm t|
  let D : ℝ := (4 / 3 : ℝ) * C_rs
  let C : ℝ := K + D

  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact abs_nonneg _
  have hC_pos : 0 < C := by
    dsimp [C]
    linarith

  refine ⟨C, hC_pos, ?_⟩
  intro T hT

  have hT1 : (1 : ℝ) ≤ T := by linarith
  have h2T : (2 : ℝ) ≤ T := by linarith

  have hErrInt_all : IntegrableOn ErrorTerm (Ioc 1 T) :=
    errorTerm_integrable T

  have hErrInt_head : IntegrableOn ErrorTerm (Ioc 1 (2 : ℝ)) := by
    refine hErrInt_all.mono_set ?_
    intro x hx
    exact ⟨hx.1, le_trans hx.2 h2T⟩

  have hErrInt_tail : IntegrableOn ErrorTerm (Ioc (2 : ℝ) T) := by
    refine hErrInt_all.mono_set ?_
    intro x hx
    exact ⟨lt_trans (by norm_num) hx.1, hx.2⟩

  have hsplit :
      ∫ t in Ioc 1 T, ErrorTerm t ∂volume =
        ∫ t in Ioc 1 (2 : ℝ), ErrorTerm t ∂volume
          + ∫ t in Ioc (2 : ℝ) T, ErrorTerm t ∂volume :=
    Aristotle.IntervalPartition.integral_split_at
      ErrorTerm 1 (2 : ℝ) T (by norm_num) h2T hErrInt_head hErrInt_tail

  have hTailInt :
      IntervalIntegrable ErrorTerm volume 2 T := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2T).2 hErrInt_tail

  have hPowInt :
      IntervalIntegrable (fun t : ℝ => C_rs * t ^ (-(1 / 4 : ℝ))) volume 2 T := by
    refine (intervalIntegral.intervalIntegrable_rpow' (a := 2) (b := T)
      (r := (-(1 / 4 : ℝ))) (by norm_num)).const_mul C_rs

  have hMono :
      ∫ t in 2..T, |ErrorTerm t|
        ≤ ∫ t in 2..T, C_rs * t ^ (-(1 / 4 : ℝ)) := by
    refine intervalIntegral.integral_mono_on h2T hTailInt.norm hPowInt ?_
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) T := by
      simpa [Set.uIcc_of_le h2T] using ht
    exact hpoint2 t htIcc.1

  have hAbsTail :
      |∫ t in 2..T, ErrorTerm t| ≤ ∫ t in 2..T, |ErrorTerm t| := by
    simpa [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_integral_norm
        (f := ErrorTerm) h2T)

  have hRpowRaw :
      ∫ t in 2..T, t ^ (-(1 / 4 : ℝ))
        = (T ^ ((-(1 / 4 : ℝ)) + 1) - (2 : ℝ) ^ ((-(1 / 4 : ℝ)) + 1))
            / ((-(1 / 4 : ℝ)) + 1) := by
    simpa using
      (integral_rpow (a := 2) (b := T) (r := (-(1 / 4 : ℝ)))
        (Or.inl (by norm_num : (-1 : ℝ) < (-(1 / 4 : ℝ)))))

  have hConstMul :
      ∫ t in 2..T, C_rs * t ^ (-(1 / 4 : ℝ))
        = C_rs * ∫ t in 2..T, t ^ (-(1 / 4 : ℝ)) := by
    simpa using
      (intervalIntegral.integral_const_mul (a := 2) (b := T) (μ := volume)
        C_rs (fun t : ℝ => t ^ (-(1 / 4 : ℝ))))

  have hRpowLe :
      ∫ t in 2..T, t ^ (-(1 / 4 : ℝ))
        ≤ (4 / 3 : ℝ) * T ^ (3 / 4 : ℝ) := by
    have hRpowRaw' :
        ∫ t in 2..T, t ^ (-(1 / 4 : ℝ))
          = (T ^ (3 / 4 : ℝ) - (2 : ℝ) ^ (3 / 4 : ℝ)) / (3 / 4 : ℝ) := by
      have h34 : ((-(1 / 4 : ℝ)) + 1) = (3 / 4 : ℝ) := by norm_num
      have htmp := hRpowRaw
      rw [h34] at htmp
      simpa using htmp
    calc
      ∫ t in 2..T, t ^ (-(1 / 4 : ℝ))
          = (T ^ (3 / 4 : ℝ) - (2 : ℝ) ^ (3 / 4 : ℝ)) / (3 / 4 : ℝ) := hRpowRaw'
      _ ≤ (T ^ (3 / 4 : ℝ)) / (3 / 4 : ℝ) := by
            have hnum : T ^ (3 / 4 : ℝ) - (2 : ℝ) ^ (3 / 4 : ℝ) ≤ T ^ (3 / 4 : ℝ) := by
              have h2pow_nonneg : 0 ≤ (2 : ℝ) ^ (3 / 4 : ℝ) := by positivity
              linarith
            have hden : (0 : ℝ) < (3 / 4 : ℝ) := by norm_num
            exact (div_le_div_iff_of_pos_right hden).2 hnum
      _ = (4 / 3 : ℝ) * T ^ (3 / 4 : ℝ) := by ring

  have hScale :
      ∫ t in 2..T, C_rs * t ^ (-(1 / 4 : ℝ))
        ≤ D * T ^ (3 / 4 : ℝ) := by
    calc
      ∫ t in 2..T, C_rs * t ^ (-(1 / 4 : ℝ))
          = C_rs * ∫ t in 2..T, t ^ (-(1 / 4 : ℝ)) := hConstMul
      _ ≤ C_rs * ((4 / 3 : ℝ) * T ^ (3 / 4 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hRpowLe (le_of_lt hC_rs)
      _ = D * T ^ (3 / 4 : ℝ) := by
            dsimp [D]
            ring

  have hTailBound :
      |∫ t in Ioc (2 : ℝ) T, ErrorTerm t|
        ≤ D * T ^ (3 / 4 : ℝ) := by
    calc
      |∫ t in Ioc (2 : ℝ) T, ErrorTerm t|
          = |∫ t in 2..T, ErrorTerm t| := by
              rw [← intervalIntegral.integral_of_le h2T]
      _ ≤ ∫ t in 2..T, |ErrorTerm t| := hAbsTail
      _ ≤ ∫ t in 2..T, C_rs * t ^ (-(1 / 4 : ℝ)) := hMono
      _ ≤ D * T ^ (3 / 4 : ℝ) := hScale

  have hTotalAux :
      |∫ t in Ioc 1 T, ErrorTerm t|
        ≤ K + D * T ^ (3 / 4 : ℝ) := by
    calc
      |∫ t in Ioc 1 T, ErrorTerm t|
          = |(∫ t in Ioc 1 (2 : ℝ), ErrorTerm t)
              + (∫ t in Ioc (2 : ℝ) T, ErrorTerm t)| := by
                simp [hsplit]
      _ ≤ |∫ t in Ioc 1 (2 : ℝ), ErrorTerm t| + |∫ t in Ioc (2 : ℝ) T, ErrorTerm t| := by
            simpa [Real.norm_eq_abs] using
              (norm_add_le
                (∫ t in Ioc 1 (2 : ℝ), ErrorTerm t)
                (∫ t in Ioc (2 : ℝ) T, ErrorTerm t))
      _ ≤ K + D * T ^ (3 / 4 : ℝ) := by
            dsimp [K]
            gcongr

  have hPow_ge_one : (1 : ℝ) ≤ T ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow (by linarith : (1 : ℝ) ≤ T) (by norm_num)

  have hK_mul : K ≤ K * T ^ (3 / 4 : ℝ) := by
    nlinarith [hK_nonneg, hPow_ge_one]

  calc
    |∫ t in Ioc 1 T, ErrorTerm t|
        ≤ K + D * T ^ (3 / 4 : ℝ) := hTotalAux
    _ ≤ K * T ^ (3 / 4 : ℝ) + D * T ^ (3 / 4 : ℝ) := by
          exact add_le_add hK_mul le_rfl
    _ = (K + D) * T ^ (3 / 4 : ℝ) := by ring
    _ = C * T ^ (3 / 4 : ℝ) := by rfl

end Aristotle.RSBlockWiring
