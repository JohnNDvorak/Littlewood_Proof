/-
Proof of HardyMeanSquareAsymptoticHyp from the classical second moment theorem.

The classical second moment theorem for ζ on the critical line:
  ∫₀ᵀ |ζ(1/2+it)|² dt = T·log(T) + O(T)
(Titchmarsh Ch. VII, Theorem 7.2)

is proved by combining:
  1. partial_zeta_mean_square_half_coeff (PROVED): ∫₁ᵀ |S_N|² = ½·T·log T + O(T)
     Uses normSq decomposition + harmonicSum integral + exact log formula + offDiag bound
  2. afe_mean_square_bridge (SORRY): ∫₁ᵀ |ζ|² = 2·∫₁ᵀ |S_N|² + O(T)
     The AFE mean-value consequence (Ingham 1926, Titchmarsh §7.2)
  3. Assembly: ms(T) = ms(1) + ∫₁ᵀ |ζ|² = K + T·log T + O(T)

and then bridged to HardyMeanSquareAsymptoticHyp: ∫₁ᵀ Z(t)² = T·log T + O(T)
via Z(t)² = |ζ(1/2+it)|² (Z-is-real + HardyZTransfer).

SORRY COUNT: 1
  - afe_integral_remainder_bound (mean-value integration of AFE pointwise error)
    This is the sole remaining B1 sorry: ∫₁ᵀ ‖|ζ|²-2|S_N|²‖ = O(T).
  NOTE: afe_mean_square_bridge is FULLY PROVED from afe_integral_remainder_bound.
  Integrability lemmas (h_zeta_int, h_partial_int) are PROVED.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ZetaMeanSquare
import Littlewood.Aristotle.HardyMeanSquareAsymptoticLeaf
import Littlewood.Bridge.HardyZTransfer
import Littlewood.Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp
import Littlewood.Aristotle.MeanSquare

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment

open Filter Asymptotics MeasureTheory Set Real

/-- Exact formula: ∫₁ᵀ log t = T·log T − T + 1 (integration by parts / FTC). -/
private lemma integral_log_exact (T : ℝ) (hT : 1 ≤ T) :
    ∫ t in (1:ℝ)..T, Real.log t = T * Real.log T - T + 1 := by
  aesop

/-- Coefficient extraction: ∫₁ᵀ |S_N(1/2+it)|² = ½·T·log T + O(T).

Proof combines:
  1. normSq decomposition: |S_N|² = H_{N(t)} + offDiag(t).re
  2. integral_harmonicSum_sub_half_log_isBigO: ∫(H_N − ½ log) = O(T)
  3. Exact formula: ∫ ½ log t = ½(T log T − T + 1)
  4. Off-diagonal bound: |∫ offDiag| ≤ 8N² ≤ 8T -/
private lemma partial_zeta_mean_square_half_coeff :
    (fun T => (∫ t in (1:ℝ)..T,
        Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * t)))
      - 2⁻¹ * T * Real.log T)
    =O[atTop] (fun T => T) := by
  -- Extract BigO witness from harmonicSum integral
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := integral_harmonicSum_sub_half_log_isBigO.exists_nonneg
  rw [IsBigOWith] at hC₁
  -- Integrability: diagonal (monotone) and off-diagonal (piecewise continuous)
  have h_diag_int : ∀ T : ℝ, IntervalIntegrable
      (fun t => ∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) MeasureTheory.volume 1 T := by
    intro T; apply MonotoneOn.intervalIntegrable
    intro t _ u _ htu
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (Nat.floor_mono (Real.sqrt_le_sqrt
        (div_le_div_of_nonneg_right htu (by positivity)))))
      (fun _ _ _ => by positivity)
  have h_offdiag_int : ∀ T : ℝ, IntervalIntegrable
      (fun t => (offDiagSsq t).re) MeasureTheory.volume 1 T := by
    intro T
    exact ⟨Complex.reCLM.integrable_comp (offDiagSsq_intervalIntegrable 1 T).1,
           Complex.reCLM.integrable_comp (offDiagSsq_intervalIntegrable 1 T).2⟩
  have h_half_log_int : ∀ T : ℝ, 1 ≤ T → IntervalIntegrable
      (fun t => 2⁻¹ * Real.log t) MeasureTheory.volume 1 T := by
    intro T hT
    exact (continuousOn_const.mul (Real.continuousOn_log.mono (fun t ht => by
      rw [Set.uIcc_of_le hT] at ht; exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
    )).intervalIntegrable
  -- Build pointwise bound
  refine .of_bound (C₁ + 1/2 + 8) ?_
  filter_upwards [hC₁, eventually_ge_atTop 1] with T hHS hT1
  -- Step 1: Rewrite integrand via normSq decomposition + harmonicSum bridge
  have h_eq : ∀ t, Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * t)) =
    harmonicSum (N_truncation t) + (offDiagSsq t).re := by
    intro t
    have := normSq_partialZeta_eq t
    rw [sum_Icc_eq_harmonicSum, N_t_eq_N_truncation] at this
    exact this
  -- Use integral_congr to rewrite integrand (keeps subtraction outside)
  have h_int_eq : ∫ t in (1:ℝ)..T,
      Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * t)) =
      ∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) + (offDiagSsq t).re) :=
    intervalIntegral.integral_congr (fun t _ => h_eq t)
  -- Check: the goal here should be ‖(∫ harm+offDiag) - ½TlogT‖ ≤ ...
  -- with subtraction OUTSIDE the integral (thanks to parenthesized statement)
  rw [h_int_eq]
  -- Verify the goal after rw
  change ‖(∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) + (offDiagSsq t).re)) -
      2⁻¹ * T * Real.log T‖ ≤ (C₁ + 1 / 2 + 8) * ‖T‖
  have h_harm : ∀ t, (∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) = harmonicSum (N_truncation t) := by
    intro t; rw [sum_Icc_eq_harmonicSum, N_t_eq_N_truncation]
  -- Integrability in harmonicSum form
  have h1' : IntervalIntegrable
      (fun t => harmonicSum (N_truncation t)) MeasureTheory.volume 1 T := by
    have h1 := h_diag_int T; simp_rw [h_harm] at h1; exact h1
  have h3 := h_half_log_int T hT1
  have h2 := h_offdiag_int T
  have h_sub_int : IntervalIntegrable
      (fun t => harmonicSum (N_truncation t) - 2⁻¹ * Real.log t) MeasureTheory.volume 1 T :=
    h1'.sub h3
  -- Step 3: Split ∫(harm + offDiag) into three pieces
  -- ∫(harm + offDiag) = ∫harm + ∫offDiag  [integral_add]
  -- ∫harm = ∫(harm-½log+½log) = ∫(harm-½log) + ∫(½log)  [congr + integral_add]
  -- Step 3: Use integral_add to split, then combine via linarith
  -- ∫(harm + offDiag) = ∫harm + ∫offDiag
  have step1 := intervalIntegral.integral_add h1' h2
  -- ∫((harm-½log) + ½log) = ∫(harm-½log) + ∫(½log)
  have step2 := intervalIntegral.integral_add h_sub_int h3
  -- ∫harm = ∫((harm-½log)+½log) by pointwise equality
  have h_congr : ∫ t in (1:ℝ)..T, harmonicSum (N_truncation t) =
      ∫ t in (1:ℝ)..T, ((harmonicSum (N_truncation t) - 2⁻¹ * Real.log t) + 2⁻¹ * Real.log t) :=
    intervalIntegral.integral_congr (fun t _ => (sub_add_cancel _ _).symm)
  -- Step 4: Exact formula for ∫ ½·log t
  have h_log : ∫ t in (1:ℝ)..T, (2⁻¹ * Real.log t) = 2⁻¹ * (T * Real.log T - T + 1) := by
    conv_lhs => rw [show (fun t => 2⁻¹ * Real.log t) = (fun t => (2:ℝ)⁻¹ * Real.log t) from rfl]
    rw [intervalIntegral.integral_const_mul, integral_log_exact T hT1]
  -- Name the sub-integrals for step 5
  -- We avoid using let/set since linarith can't unfold them
  -- Instead, we derive the key identity directly
  -- ∫(harm+offDiag) - ½TlogT
  --   = (∫harm + ∫offDiag) - ½TlogT                                [step1]
  --   = (∫((harm-½log)+½log) + ∫offDiag) - ½TlogT                  [h_congr]
  --   = (∫(harm-½log) + ∫(½log) + ∫offDiag) - ½TlogT               [step2]
  --   = ∫(harm-½log) + ½(TlogT-T+1) + ∫offDiag - ½TlogT            [h_log]
  --   = ∫(harm-½log) + ½(1-T) + ∫offDiag                            [arith]
  -- Normalize bound-variable names (integral_add/congr produce x vs t)
  have step1' : ∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) + (offDiagSsq t).re) =
      (∫ t in (1:ℝ)..T, harmonicSum (N_truncation t)) +
      ∫ t in (1:ℝ)..T, (offDiagSsq t).re := step1
  have step2' : ∫ t in (1:ℝ)..T,
      ((harmonicSum (N_truncation t) - 2⁻¹ * Real.log t) + 2⁻¹ * Real.log t) =
      (∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t)) +
      ∫ t in (1:ℝ)..T, (2⁻¹ * Real.log t) := step2
  -- Combine via rw chain
  have h_rw : (∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) + (offDiagSsq t).re)) -
      2⁻¹ * T * Real.log T =
    (∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t)) +
    2⁻¹ * (1 - T) +
    (∫ t in (1:ℝ)..T, (offDiagSsq t).re) := by
    rw [step1', h_congr, step2', h_log]; ring
  rw [h_rw]
  -- Step 6: Triangle inequality and bound each piece
  have hT_nn : (0:ℝ) ≤ T := by linarith
  -- Bound 1: harmonicSum integral
  have hA : |∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t)| ≤
      C₁ * |T| := by simpa only [Real.norm_eq_abs] using hHS
  -- Bound 2: ½·(1-T)
  have hB : |2⁻¹ * (1 - T)| ≤ (1/2) * |T| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹)]
    have : |1 - T| ≤ |T| := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_of_nonneg hT_nn]; linarith
    linarith
  -- Bound 3: off-diagonal integral
  have hC : |∫ t in (1:ℝ)..T, (offDiagSsq t).re| ≤ 8 * |T| := by
    have h_int := offDiagSsq_intervalIntegrable 1 T
    have h_re_eq : ∫ t in (1:ℝ)..T, (offDiagSsq t).re =
        (∫ t in (1:ℝ)..T, offDiagSsq t).re :=
      Complex.reCLM.intervalIntegral_comp_comm h_int
    have h_N_sq : (N_t T : ℝ)^2 ≤ T := by
      have h1 : (N_t T : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) :=
        Nat.floor_le (Real.sqrt_nonneg _)
      have h4 : (N_t T : ℝ)^2 ≤ Real.sqrt (T / (2 * Real.pi)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
      linarith [Real.sq_sqrt (show (0:ℝ) ≤ T / (2 * Real.pi) by positivity),
        show T / (2 * Real.pi) ≤ T from div_le_self (by linarith) (by nlinarith [Real.pi_gt_three])]
    rw [h_re_eq]
    calc |(∫ t in (1:ℝ)..T, offDiagSsq t).re|
        ≤ ‖∫ t in (1:ℝ)..T, offDiagSsq t‖ := Complex.abs_re_le_norm _
      _ ≤ 8 * (N_t T : ℝ)^2 := norm_integral_offDiagSsq_le T hT1
      _ ≤ 8 * |T| := by nlinarith [abs_of_nonneg hT_nn]
  -- Combine via triangle inequality (avoiding let/set — use full expressions)
  have tri1 := abs_add_le
    ((∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t)) + 2⁻¹ * (1 - T))
    (∫ t in (1:ℝ)..T, (offDiagSsq t).re)
  have tri2 := abs_add_le
    (∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t))
    (2⁻¹ * (1 - T))
  simp only [Real.norm_eq_abs] at *
  linarith

-- ==============================================================================
-- BLOCK B1: APPROXIMATE FUNCTIONAL EQUATION BRIDGE
-- ==============================================================================

/-- Integral of the AFE remainder is O(T).
Uses Cauchy-Schwarz (Hölder's inequality) and `partial_zeta_mean_square_half_coeff`.
This is the mean-value integration of the pointwise AFE bound. -/
private lemma afe_integral_remainder_bound :
    (fun T => ∫ t in (1:ℝ)..T,
      ‖‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖^2 -
       2 * Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi)))
         (1/2 + Complex.I * t))‖)
    =O[atTop] (fun T => T) := by
  sorry

/-- The mean-value consequence of the approximate functional equation.

On the critical line, the AFE gives ζ(1/2+it) = S_N(t) + χ(t)·conj(S_N(t)) + R(t)
with |χ|=1 and |R(t)| ≪ t^{-1/4}. Expanding |ζ|² and integrating:
  ∫|ζ|² = 2∫|S_N|² + O(T)
The O(T) absorbs cross-terms (Cauchy-Schwarz) and the oscillatory ∫Re(χ̄·S_N²).

Proved by combining `afe_integral_remainder_bound` (integral of AFE error is O(T))
with the triangle inequality for integrals.

Reference: Titchmarsh §7.2; Ingham (1926). -/
private theorem afe_mean_square_bridge :
    (fun T => (∫ t in (1:ℝ)..T, ‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖^2) -
      2 * (∫ t in (1:ℝ)..T, Complex.normSq
        (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * t))))
    =O[atTop] (fun T => T) := by
  -- Step 1: Prove Integrability
  have h_zeta_int : ∀ T, IntervalIntegrable
      (fun t : ℝ => ‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖^2) volume 1 T := by
    -- ζ is continuous away from s=1; 1/2+it ≠ 1 since Re = 1/2 ≠ 1
    have h_ne_one : ∀ t : ℝ, ↑(1/2 : ℝ) + Complex.I * ↑t ≠ (1 : ℂ) := by
      intro t h; have h_re := congr_arg Complex.re h; simp at h_re
    have h_cont : Continuous (fun t : ℝ => riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)) := by
      rw [continuous_iff_continuousAt]; intro t
      exact ContinuousAt.comp
        (g := riemannZeta) (f := fun t : ℝ => (↑(1/2 : ℝ) : ℂ) + Complex.I * (↑t : ℂ))
        (differentiableAt_riemannZeta (h_ne_one t)).continuousAt
        (by fun_prop)
    intro T
    exact (h_cont.norm.pow 2).continuousOn.intervalIntegrable
  have h_partial_int : ∀ T, IntervalIntegrable
      (fun t : ℝ => Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi)))
        (1/2 + Complex.I * t))) volume 1 T := by
    intro T
    -- Decompose normSq into diag + offDiag via normSq_partialZeta_eq
    have h_eq : (fun t : ℝ => Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi)))
        (1/2 + Complex.I * t))) =
        (fun t => harmonicSum (N_truncation t) + (offDiagSsq t).re) := by
      ext t
      have := normSq_partialZeta_eq t
      rw [sum_Icc_eq_harmonicSum, N_t_eq_N_truncation] at this
      exact this
    rw [h_eq]
    -- Diagonal part: monotone hence integrable
    have h_diag : IntervalIntegrable (fun t => harmonicSum (N_truncation t)) volume 1 T := by
      have h1 : IntervalIntegrable
          (fun t => ∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) volume 1 T := by
        apply MonotoneOn.intervalIntegrable
        intro t _ u _ htu
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right (Nat.floor_mono (Real.sqrt_le_sqrt
            (div_le_div_of_nonneg_right htu (by positivity)))))
          (fun _ _ _ => by positivity)
      simp_rw [sum_Icc_eq_harmonicSum, N_t_eq_N_truncation] at h1
      exact h1
    -- Off-diagonal part: CLM composition of integrable function
    have h_offdiag : IntervalIntegrable (fun t => (offDiagSsq t).re) volume 1 T :=
      ⟨Complex.reCLM.integrable_comp (offDiagSsq_intervalIntegrable 1 T).1,
       Complex.reCLM.integrable_comp (offDiagSsq_intervalIntegrable 1 T).2⟩
    exact h_diag.add h_offdiag
  -- Step 2: Asymptotic transitivity: ‖∫f‖ ≤ ∫‖f‖ =O T
  refine IsBigO.trans ?_ afe_integral_remainder_bound
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  simp only [one_mul]
  -- Step 3: Combine the two integrals into one
  have h_combine : (∫ t in (1:ℝ)..T, ‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖^2) -
      2 * (∫ t in (1:ℝ)..T, Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi)))
        (1/2 + Complex.I * t))) =
      ∫ t in (1:ℝ)..T, (‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖^2 -
      2 * Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi)))
        (1/2 + Complex.I * t))) := by
    rw [← intervalIntegral.integral_const_mul 2]
    rw [← intervalIntegral.integral_sub (h_zeta_int T) ((h_partial_int T).const_mul 2)]
  rw [h_combine]
  -- Step 4: Triangle inequality for integrals + norm of nonneg integral
  exact (intervalIntegral.norm_integral_le_integral_norm
    (f := fun t => ‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖^2 -
      2 * Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi)))
        (1/2 + Complex.I * t))) hT).trans
    (le_of_eq (Real.norm_of_nonneg (intervalIntegral.integral_nonneg_of_forall hT
      (fun t => norm_nonneg _))).symm)

/-- EP.hardyZ² = Decomp.hardyZ² (direct proof via Z-is-real).

EP.hardyZ(t) = Re(exp(iθ)·ζ(1/2+It)) is real-valued (hardyZV2_real), so
  EP.hardyZ(t)² = ‖hardyZV2 t‖² = ‖ζ(1/2+It)‖² = Decomp.hardyZ(t)².
-/
private lemma ep_sq_eq_decomp_sq (t : ℝ) :
    (HardyEstimatesPartial.hardyZ t) ^ 2 =
      (HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ t) ^ 2 := by
  -- Step 1: EP.hardyZ = (hardyZV2 t).re
  have h_re := HardyZTransfer.hardyZ_eq_hardyZV2_re t
  -- Step 2: hardyZV2 is real (im = 0)
  have h_im := hardyZV2_real t
  -- Step 3: ‖hardyZV2 t‖ = ‖ζ(1/2 + I*t)‖
  have h_norm := hardyZV2_abs_eq_zeta_abs t
  -- EP.hardyZ² = .re² = ‖hardyZV2‖² (since im = 0)
  have h_ep_sq : (HardyEstimatesPartial.hardyZ t) ^ 2 = ‖hardyZV2 t‖ ^ 2 := by
    rw [h_re]
    have h_eq : hardyZV2 t = ((hardyZV2 t).re : ℂ) :=
      Complex.ext rfl (by simp [h_im])
    conv_rhs => rw [h_eq, Complex.norm_real]
    exact (sq_abs _).symm
  -- Decomp.hardyZ² = ‖ζ(1/2 + I*t)‖² = ‖hardyZV2 t‖²
  have h_decomp_sq : (HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ t) ^ 2 =
      ‖hardyZV2 t‖ ^ 2 := by
    unfold HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ
    rw [← h_norm]
  rw [h_ep_sq, h_decomp_sq]

/-- The integral of EP.hardyZ² over Ioc 1 T equals mean_square_zeta(1/2) T minus a constant. -/
private lemma integral_ep_hardyZ_sq (T : ℝ) (hT : 1 ≤ T) :
    ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2 =
      mean_square_zeta (1 / 2) T - mean_square_zeta (1 / 2) 1 := by
  have h_congr : ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2 =
      ∫ t in Ioc 1 T, (HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ t) ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioc (fun t _ => ep_sq_eq_decomp_sq t)
  rw [h_congr]
  exact HardyApproxFunctionalEqMeanValueLowerDecomp.integral_Ioc_one_eq_mean_square_sub T hT

/-- Classical second moment of ζ on the critical line:
  ∫₀ᵀ |ζ(1/2+it)|² dt = T·log T + O(T)

Proved by combining:
  1. afe_mean_square_bridge: ∫₁ᵀ |ζ|² = 2·∫₁ᵀ |S_N|² + O(T)
  2. partial_zeta_mean_square_half_coeff: ∫₁ᵀ |S_N|² = ½·T·log T + O(T)
  3. mean_square_zeta split: ms(T) = ms(1) + ∫₁ᵀ |ζ|²

Reference: Titchmarsh, "The Theory of the Riemann Zeta-Function", Theorem 7.2. -/
private theorem zeta_mean_square_half :
    (fun T => mean_square_zeta (1 / 2) T - T * Real.log T) =O[atTop] (fun T => T) := by
  -- Extract BigO witnesses
  obtain ⟨C_afe, hC_afe_nn, hC_afe⟩ := afe_mean_square_bridge.exists_nonneg
  obtain ⟨C_pz, hC_pz_nn, hC_pz⟩ := partial_zeta_mean_square_half_coeff.exists_nonneg
  rw [IsBigOWith] at hC_afe hC_pz
  set K := mean_square_zeta (1 / 2) 1
  refine .of_bound (C_afe + 2 * C_pz + |K|) ?_
  filter_upwards [hC_afe, hC_pz, eventually_ge_atTop 1] with T h_afe h_pz hT1
  simp only [Real.norm_eq_abs] at h_afe h_pz ⊢
  -- Connect mean_square_zeta to ∫₁ᵀ ‖ζ‖²
  have h_ms_split : mean_square_zeta (1/2) T = K +
      ∫ t in (1:ℝ)..T, ‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖ ^ 2 := by
    have h1 := integral_ep_hardyZ_sq T hT1
    have h_congr : ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2 =
        ∫ t in Ioc 1 T, ‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖ ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
      rw [ep_sq_eq_decomp_sq]
      unfold HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ
      push_cast; ring
    rw [h_congr] at h1
    have h_ioc_eq : ∫ t in (1:ℝ)..T, ‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖ ^ 2 =
        ∫ t in Ioc 1 T, ‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖ ^ 2 :=
      intervalIntegral.integral_of_le hT1
    linarith [h_ioc_eq]
  have hT_nn : (0:ℝ) ≤ T := by linarith
  have hT_abs : |T| ≥ 1 := by rwa [abs_of_nonneg hT_nn]
  -- Name the two integrals to avoid parsing issues
  -- (integrals are greedy — they absorb everything after the comma)
  let Z := ∫ t in (1:ℝ)..T, ‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖ ^ 2
  let B := ∫ t in (1:ℝ)..T, Complex.normSq
      (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * t))
  -- Algebraic identity: ms - TlogT = K + (Z-2B) + 2(B - ½TlogT)
  -- h_ms_split says ms = K + Z, so ms - TlogT = K + Z - TlogT = K + (Z-2B) + 2B - TlogT
  have h_decomp : mean_square_zeta (1/2) T - T * Real.log T =
      K + (Z - 2 * B) + 2 * (B - 2⁻¹ * T * Real.log T) := by
    -- Z is definitionally equal to the integral in h_ms_split
    show _ = K + (Z - 2 * B) + 2 * (B - 2⁻¹ * T * Real.log T)
    linarith [h_ms_split]
  -- Use conv to rewrite the LHS of the goal
  conv_lhs => rw [h_decomp]
  -- Triangle inequality: |K + a + 2b| ≤ |K| + |a| + 2|b|
  have tri1 := abs_add_le (K + (Z - 2 * B)) (2 * (B - 2⁻¹ * T * Real.log T))
  have tri2 := abs_add_le K (Z - 2 * B)
  have h_2abs : |2 * (B - 2⁻¹ * T * Real.log T)| = 2 * |B - 2⁻¹ * T * Real.log T| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hK_le : |K| ≤ |K| * |T| := le_mul_of_one_le_right (abs_nonneg K) hT_abs
  -- Bridge h_afe and h_pz: use change to make linarith see Z and B
  change |Z - 2 * B| ≤ _ at h_afe
  change |B - 2⁻¹ * T * Real.log T| ≤ _ at h_pz
  linarith

/-- **Main result**: HardyMeanSquareAsymptoticHyp from the classical second moment.

Proves `∫₁ᵀ Z(t)² - T·log T = O(T)` from `∫₀ᵀ |ζ(1/2+it)|² - T·log T = O(T)`. -/
theorem hardyMeanSquareAsymptoticHyp_proved :
    Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp where
  bound := by
    set K := mean_square_zeta (1 / 2) 1
    -- Extract concrete BigO witnesses from the classical second moment
    obtain ⟨C, hC_nn, hC⟩ := zeta_mean_square_half.exists_nonneg
    rw [IsBigOWith] at hC
    -- Build the target BigO bound with constant C + |K|
    refine .of_bound (C + |K|) ?_
    filter_upwards [hC, eventually_ge_atTop 1] with T hms hT1
    -- Rewrite the integral using the bridge chain
    rw [integral_ep_hardyZ_sq T hT1]
    -- Goal: ‖(ms(T) - K) - T*logT‖ ≤ (C + |K|) * ‖T‖
    -- Rewrite as (ms(T) - T*logT) + (-K) and apply triangle inequality
    have h_rw : mean_square_zeta (1 / 2) T - K - T * Real.log T =
        (mean_square_zeta (1 / 2) T - T * Real.log T) + (-K) := by ring
    rw [h_rw]
    have hT_nn : (0 : ℝ) ≤ T := by linarith
    calc ‖mean_square_zeta (1 / 2) T - T * Real.log T + -K‖
        ≤ ‖mean_square_zeta (1 / 2) T - T * Real.log T‖ + ‖(-K : ℝ)‖ := norm_add_le _ _
      _ = ‖mean_square_zeta (1 / 2) T - T * Real.log T‖ + |K| := by
          simp only [Real.norm_eq_abs, abs_neg]
      _ ≤ C * ‖T‖ + |K| := by linarith [hms]
      _ ≤ C * ‖T‖ + |K| * ‖T‖ := by
          have : ‖T‖ ≥ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hT_nn]; linarith
          nlinarith [abs_nonneg K]
      _ = (C + |K|) * ‖T‖ := by ring

end Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment
