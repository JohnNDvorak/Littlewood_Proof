import Mathlib
import Littlewood.Aristotle.BinetStirling
import Littlewood.Aristotle.CosPiSqSign
import Littlewood.Aristotle.DigammaBinetBound
import Littlewood.Aristotle.GammaSeqLocallyUniform
import Littlewood.Aristotle.HardyCosSmooth
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.Standalone.HolomorphicLogOnHalfPlane
import Littlewood.Aristotle.Standalone.SumInvSqPlusSqBound

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.StationaryPhaseStartValue

open Complex MeasureTheory Set Real Filter Topology Asymptotics
open HardyEstimatesPartial
open Aristotle.HardyNProperties
open Aristotle.DigammaBinetBound
open GammaSeqLocalUniform

/-- The Stirling main term for `log Γ`. -/
noncomputable def stirlingTerm (s : ℂ) : ℂ :=
  (s - 1 / 2) * Complex.log s - s + 1 / 2 * Complex.log (2 * Real.pi)

/-- The explicit stationary-phase anchor. -/
noncomputable def hardyStationaryAnchor : ℂ :=
  Complex.exp (-Complex.I * (Real.pi / 8 : ℂ))

lemma hardyStationaryAnchor_re_pos : 0 < hardyStationaryAnchor.re := by
  rw [hardyStationaryAnchor, Complex.exp_re]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Real.cos_pi_div_eight]
  have hinner : 0 < 2 + Real.sqrt 2 := by positivity
  have hsqrt_pos : 0 < Real.sqrt (2 + Real.sqrt 2) := by
    exact Real.sqrt_pos.2 hinner
  nlinarith

/-- The cubic Gauss correction after extracting the telescoping `1/(2w)` main
term from the digamma Gauss series. -/
abbrev gaussStirlingCorrectionTerm (w : ℂ) : ℂ :=
  GammaSeqLocalUniform.gaussTerm w + 1 / (2 * w) - 1 / (2 * (w + 1))

private lemma add_natCast_ne_zero (s : ℂ) (hs : 0 < s.re) (j : ℕ) :
    s + (j : ℂ) ≠ 0 := by
  apply ne_of_apply_ne re
  simp only [add_re, natCast_re, zero_re]
  linarith [Nat.cast_nonneg (α := ℝ) j]

private lemma hardyStart_half (n : ℕ) :
    hardyStart n / 2 = Real.pi * ((n : ℝ) + 1) ^ 2 := by
  rw [hardyStart_formula]
  ring

private lemma exp_neg_pi_sq_mul_I_aux (m : ℕ) :
    Complex.exp ((((-Real.pi) * (m : ℝ) ^ 2 : ℝ) : ℂ) * Complex.I)
      = ((((-1 : ℝ) ^ m : ℝ)) : ℂ) := by
  set x : ℝ := (-Real.pi) * (m : ℝ) ^ 2
  have hx : x = -((m ^ 2 : ℕ) * Real.pi) := by
    dsimp [x]
    norm_num [pow_two]
    ring
  change Complex.exp ((x : ℂ) * Complex.I) = ((((-1 : ℝ) ^ m : ℝ)) : ℂ)
  apply Complex.ext
  · calc
      (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x := by
        simpa using (Complex.exp_ofReal_mul_I_re (x := x))
      _ = ((-1 : ℝ) ^ m) := by
        rw [hx, Real.cos_neg, Real.cos_nat_mul_pi, CosPiSqSign.neg_one_pow_nat_sq]
      _ = ((((-1 : ℝ) ^ m : ℝ) : ℂ)).re := by
        simpa using (Complex.ofReal_re (((-1 : ℝ) ^ m : ℝ))).symm
  · calc
      (Complex.exp ((x : ℂ) * Complex.I)).im = Real.sin x := by
        simpa using (Complex.exp_ofReal_mul_I_im (x := x))
      _ = 0 := by
        rw [hx, Real.sin_neg, Real.sin_nat_mul_pi]
        norm_num
      _ = ((((-1 : ℝ) ^ m : ℝ) : ℂ)).im := by
        simpa using (Complex.ofReal_im (((-1 : ℝ) ^ m : ℝ))).symm

private lemma exp_neg_pi_sq_mul_I (m : ℕ) :
    Complex.exp (Complex.I * ((-(Real.pi * (m : ℝ) ^ 2)) : ℂ))
      = ((((-1 : ℝ) ^ m : ℝ)) : ℂ) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using (exp_neg_pi_sq_mul_I_aux m)

private lemma gaussStirlingCorrectionTerm_bound_of_norm_ge_100_div_99 (w : ℂ)
    (hw : (100 : ℝ) / 99 ≤ ‖w‖) :
    ‖gaussStirlingCorrectionTerm w‖ ≤ (100 : ℝ) / ‖w‖ ^ 3 := by
  have hw_pos : (0 : ℝ) < ‖w‖ := lt_of_lt_of_le (by positivity) hw
  have hw_ne : w ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt hw_pos)
  set z : ℂ := 1 / w with hz_def
  have hz_norm : ‖z‖ = 1 / ‖w‖ := by
    rw [hz_def, norm_div, norm_one]
  have hz_le : ‖z‖ ≤ (99 : ℝ) / 100 := by
    rw [hz_norm]
    have htmp : 1 / ‖w‖ ≤ 1 / ((100 : ℝ) / 99) :=
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (100 : ℝ) / 99) hw
    norm_num at htmp ⊢
    exact htmp
  have hz_lt_one : ‖z‖ < 1 := by
    linarith
  have h_inv_le : (1 - ‖z‖)⁻¹ ≤ (100 : ℝ) := by
    rw [show (100 : ℝ) = ((1 : ℝ) / 100)⁻¹ by norm_num]
    apply inv_anti₀
    · linarith
    · linarith
  have h_logTaylor :
      Complex.logTaylor 3 z = z - z ^ 2 / 2 := by
    norm_num [Complex.logTaylor, Finset.sum_range_succ]
    ring_nf
  have h_one_add_ne : 1 + z ≠ 0 := by
    intro hz
    have : ‖z‖ = 1 := by
      have hz' : z = (-1 : ℂ) := by
        have hz0 : z + 1 = 0 := by simpa [add_comm] using hz
        simpa using (eq_neg_of_add_eq_zero_left hz0)
      simpa [hz']
    linarith
  have h_one_add_inv :
      ‖(1 + z)⁻¹‖ ≤ (1 - ‖z‖)⁻¹ := by
    simpa [one_mul] using Complex.norm_one_add_mul_inv_le (t := (1 : ℝ))
      (by simp) hz_lt_one
  have h_one_add_inv' : ‖(1 + z)⁻¹‖ ≤ (100 : ℝ) := by
    exact le_trans h_one_add_inv h_inv_le
  have h_remainder :
      ‖Complex.log (1 + z) - Complex.logTaylor 3 z‖ ≤
        ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := by
    convert Complex.norm_log_sub_logTaylor_le 2 hz_lt_one using 1 <;> norm_num
  have h_remainder' :
      ‖Complex.log (1 + z) - Complex.logTaylor 3 z‖ ≤
        (100 : ℝ) / 3 * ‖z‖ ^ 3 := by
    calc
      ‖Complex.log (1 + z) - Complex.logTaylor 3 z‖
          ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := h_remainder
      _ ≤ ‖z‖ ^ 3 * 100 / 3 := by
            gcongr
      _ = (100 : ℝ) / 3 * ‖z‖ ^ 3 := by ring
  have h_tail :
      ‖z ^ 3 / (2 * (1 + z))‖ ≤ (50 : ℝ) * ‖z‖ ^ 3 := by
    calc
      ‖z ^ 3 / (2 * (1 + z))‖
          = ‖z‖ ^ 3 * ‖(2 : ℂ) * (1 + z)‖⁻¹ := by
              rw [div_eq_mul_inv, norm_mul, norm_inv, norm_mul, norm_pow]
      _ = ‖z‖ ^ 3 * ((2 : ℝ) * ‖1 + z‖)⁻¹ := by
            norm_num
      _ ≤ ‖z‖ ^ 3 * ((2 : ℝ) * (1 - ‖z‖))⁻¹ := by
            have htmp : 1 - ‖z‖ ≤ ‖1 + z‖ := by
              have htmp' : ‖(1 : ℂ)‖ - ‖-z‖ ≤ ‖(1 : ℂ) - (-z)‖ := by
                simpa using (norm_sub_norm_le (1 : ℂ) (-z))
              simpa using htmp'
            have hden : (2 : ℝ) * (1 - ‖z‖) ≤ (2 : ℝ) * ‖1 + z‖ := by
              nlinarith
            have hden_pos : (0 : ℝ) < (2 : ℝ) * (1 - ‖z‖) := by
              have hz_pos : (0 : ℝ) < 1 - ‖z‖ := sub_pos.mpr hz_lt_one
              positivity
            have hinv :
                ((2 : ℝ) * ‖1 + z‖)⁻¹ ≤ ((2 : ℝ) * (1 - ‖z‖))⁻¹ := by
              exact inv_anti₀ hden_pos hden
            exact mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = ‖z‖ ^ 3 * ((1 - ‖z‖)⁻¹ / 2) := by
            field_simp [sub_ne_zero.mpr (ne_of_gt (sub_pos.2 hz_lt_one))]
      _ ≤ ‖z‖ ^ 3 * (100 / 2) := by
            gcongr
      _ = (50 : ℝ) * ‖z‖ ^ 3 := by ring
  have hrewrite :
      gaussStirlingCorrectionTerm w =
        (Complex.log (1 + z) - Complex.logTaylor 3 z) - z ^ 3 / (2 * (1 + z)) := by
    have hw1_ne : w + 1 ≠ 0 := by
      intro hw1
      have : ‖w‖ = 1 := by
        have hw' : w = (-1 : ℂ) := by
          have hw0 : w + 1 = 0 := hw1
          simpa using (eq_neg_of_add_eq_zero_left hw0)
        simpa [hw']
      linarith
    have hz_sq :
        1 / (2 * w) - 1 / (2 * (w + 1))
          = z ^ 2 / (2 * (1 + z)) := by
      dsimp [z]
      field_simp [hw_ne, hw1_ne]
      ring
    calc
      gaussStirlingCorrectionTerm w
          = Complex.log (1 + 1 / w) - 1 / w
              + (1 / (2 * w) - 1 / (2 * (w + 1))) := by
                simp [gaussStirlingCorrectionTerm, GammaSeqLocalUniform.gaussTerm,
                  sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = Complex.log (1 + z) - z + z ^ 2 / (2 * (1 + z)) := by
            rw [hz_sq]
      _ = (Complex.log (1 + z) - Complex.logTaylor 3 z) - z ^ 3 / (2 * (1 + z)) := by
            have hz_alg :
                z ^ 2 / (2 * (1 + z)) = z ^ 2 / 2 - z ^ 3 / (2 * (1 + z)) := by
              field_simp [h_one_add_ne]
              ring
            rw [h_logTaylor, hz_alg]
            ring
  calc
    ‖gaussStirlingCorrectionTerm w‖
        = ‖(Complex.log (1 + z) - Complex.logTaylor 3 z) - z ^ 3 / (2 * (1 + z))‖ := by
            rw [hrewrite]
    _ ≤ ‖Complex.log (1 + z) - Complex.logTaylor 3 z‖ + ‖z ^ 3 / (2 * (1 + z))‖ := norm_sub_le _ _
    _ ≤ (100 : ℝ) / 3 * ‖z‖ ^ 3 + (50 : ℝ) * ‖z‖ ^ 3 := by
          gcongr
    _ ≤ (100 : ℝ) * ‖z‖ ^ 3 := by
          have hz3_nonneg : 0 ≤ ‖z‖ ^ 3 := by positivity
          nlinarith
    _ = (100 : ℝ) / ‖w‖ ^ 3 := by
          rw [hz_norm]
          field_simp [ne_of_gt hw_pos]

private lemma norm_le_norm_add_natCast (s : ℂ) (hsre : 0 ≤ s.re) (n : ℕ) :
    ‖s‖ ≤ ‖s + (n : ℂ)‖ := by
  have hsq : ‖s‖ ^ 2 ≤ ‖s + (n : ℂ)‖ ^ 2 := by
    have := Aristotle.DigammaBinetBound.norm_sq_add_natCast_ge s hsre n
    nlinarith [sq_nonneg (n : ℝ)]
  have habs : |‖s‖| ≤ |‖s + (n : ℂ)‖| := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using habs

private lemma inv_norm_add_natCast_sq_le_inv_natCast_sq_of_re_nonneg
    (s : ℂ) (hsre : 0 ≤ s.re) {j : ℕ} (hj : 1 ≤ j) :
    1 / ‖s + (j : ℂ)‖ ^ 2 ≤ 1 / (j : ℝ) ^ 2 := by
  have h_step1 :
      1 / ‖s + (j : ℂ)‖ ^ 2 ≤ 1 / (‖s‖ ^ 2 + (j : ℝ) ^ 2) := by
    have hden_pos : (0 : ℝ) < ‖s‖ ^ 2 + (j : ℝ) ^ 2 := by positivity
    exact one_div_le_one_div_of_le hden_pos
      (Aristotle.DigammaBinetBound.norm_sq_add_natCast_ge s hsre j)
  have hj_pos : (0 : ℝ) < (j : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hj)
  have h_step2 :
      1 / (‖s‖ ^ 2 + (j : ℝ) ^ 2) ≤ 1 / (j : ℝ) ^ 2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hj_pos)
    nlinarith [sq_nonneg ‖s‖]
  exact le_trans h_step1 h_step2

private lemma summable_inv_norm_add_natCast_sq_of_re_nonneg
    (s : ℂ) (hsre : 0 ≤ s.re) :
    Summable (fun n : ℕ => (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2) := by
  let f : ℕ → ℝ := fun n => (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2
  have hshift : Summable (fun n : ℕ => f (n + 1)) := by
    have hbound : ∀ n : ℕ, f (n + 1) ≤ 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
      intro n
      simpa [f] using
        inv_norm_add_natCast_sq_le_inv_natCast_sq_of_re_nonneg (s := s) hsre
          (j := n + 1) (Nat.succ_le_succ (Nat.zero_le _))
    have hsum : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      exact (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
    exact Summable.of_nonneg_of_le (fun n => by positivity) hbound hsum
  exact (summable_nat_add_iff 1).1 hshift

private lemma tsum_inv_norm_add_natCast_sq_le_four_div_norm_of_re_nonneg_norm_ge_one
    (s : ℂ) (hsre : 0 ≤ s.re) (hnorm : 1 ≤ ‖s‖) :
    (∑' n : ℕ, (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2) ≤ (4 : ℝ) / ‖s‖ := by
  let f : ℕ → ℝ := fun n => (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2
  let g : ℕ → ℝ := fun n => (1 : ℝ) / (‖s‖ ^ 2 + (n : ℝ) ^ 2)
  have hsumm_f : Summable f :=
    summable_inv_norm_add_natCast_sq_of_re_nonneg s hsre
  have hsumm_g : Summable g := by
    have hshift : Summable (fun n : ℕ => g (n + 1)) := by
      have hbound : ∀ n : ℕ, g (n + 1) ≤ 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
        intro n
        apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2)
        nlinarith [sq_nonneg ‖s‖]
      have hsum : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
        exact (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
      exact Summable.of_nonneg_of_le (fun n => by positivity) hbound hsum
    exact (summable_nat_add_iff 1).1 hshift
  have hcomp : ∀ n : ℕ, f n ≤ g n := by
    intro n
    have hden_pos : (0 : ℝ) < ‖s‖ ^ 2 + (n : ℝ) ^ 2 := by positivity
    simpa [f, g] using one_div_le_one_div_of_le hden_pos
      (Aristotle.DigammaBinetBound.norm_sq_add_natCast_ge s hsre n)
  have hle_tsum : (∑' n : ℕ, f n) ≤ ∑' n : ℕ, g n := hsumm_f.tsum_le_tsum hcomp hsumm_g
  have hmajor : (∑' n : ℕ, g n) ≤ (1 + Real.pi / 2) / ‖s‖ :=
    sum_inv_sq_plus_sq_bound ‖s‖ hnorm
  have hconst : (1 + Real.pi / 2 : ℝ) ≤ 4 := by
    nlinarith [Real.pi_le_four]
  have hnorm_pos : (0 : ℝ) < ‖s‖ := lt_of_lt_of_le zero_lt_one hnorm
  calc
    (∑' n : ℕ, f n) ≤ ∑' n : ℕ, g n := hle_tsum
    _ ≤ (1 + Real.pi / 2) / ‖s‖ := hmajor
    _ ≤ (4 : ℝ) / ‖s‖ := by
          exact div_le_div_of_nonneg_right hconst hnorm_pos.le

private lemma summable_inv_norm_add_natCast_cu_of_re_nonneg_norm_ge_one
    (s : ℂ) (hsre : 0 ≤ s.re) (hnorm : 1 ≤ ‖s‖) :
    Summable (fun n : ℕ => (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 3) := by
  have hsumm_sq :
      Summable (fun n : ℕ => (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2) :=
    summable_inv_norm_add_natCast_sq_of_re_nonneg s hsre
  have hnorm_pos : (0 : ℝ) < ‖s‖ := lt_of_lt_of_le zero_lt_one hnorm
  refine Summable.of_nonneg_of_le (fun _ => by positivity) ?_ (hsumm_sq.mul_left (1 / ‖s‖))
  intro n
  have hbound :
      1 / ‖s + (n : ℂ)‖ ≤ 1 / ‖s‖ := by
    exact one_div_le_one_div_of_le hnorm_pos
      (norm_le_norm_add_natCast s hsre n)
  calc
    1 / ‖s + (n : ℂ)‖ ^ 3
        = (1 / ‖s + (n : ℂ)‖) * (1 / ‖s + (n : ℂ)‖ ^ 2) := by
            ring
    _ ≤ (1 / ‖s‖) * (1 / ‖s + (n : ℂ)‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_right hbound (by positivity)

private lemma tsum_inv_norm_add_natCast_cu_le_four_div_sq_norm_of_re_nonneg_norm_ge_one
    (s : ℂ) (hsre : 0 ≤ s.re) (hnorm : 1 ≤ ‖s‖) :
    (∑' n : ℕ, (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 3) ≤ (4 : ℝ) / ‖s‖ ^ 2 := by
  have hsumm_cu :
      Summable (fun n : ℕ => (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 3) :=
    summable_inv_norm_add_natCast_cu_of_re_nonneg_norm_ge_one s hsre hnorm
  have hsumm_sq :
      Summable (fun n : ℕ => (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2) :=
    summable_inv_norm_add_natCast_sq_of_re_nonneg s hsre
  have hnorm_pos : (0 : ℝ) < ‖s‖ := lt_of_lt_of_le zero_lt_one hnorm
  have hbound : ∀ n : ℕ,
      (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 3 ≤
        (1 / ‖s‖) * ((1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2) := by
    intro n
    have hnorm_le' :
        1 / ‖s + (n : ℂ)‖ ≤ 1 / ‖s‖ := by
      exact one_div_le_one_div_of_le hnorm_pos
        (norm_le_norm_add_natCast s hsre n)
    calc
      (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 3
          = (1 / ‖s + (n : ℂ)‖) * ((1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2) := by
              ring
      _ ≤ (1 / ‖s‖) * ((1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_right hnorm_le' (by positivity)
  have htsum_le :
      (∑' n : ℕ, (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 3) ≤
        ∑' n : ℕ, (1 / ‖s‖) * ((1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2) :=
    hsumm_cu.tsum_le_tsum hbound (hsumm_sq.mul_left (1 / ‖s‖))
  calc
    (∑' n : ℕ, (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 3)
        ≤ ∑' n : ℕ, (1 / ‖s‖) * ((1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2) := htsum_le
    _ = (1 / ‖s‖) * (∑' n : ℕ, (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2) := by
          simp [tsum_mul_left]
    _ ≤ (1 / ‖s‖) * ((4 : ℝ) / ‖s‖) := by
          gcongr
          exact tsum_inv_norm_add_natCast_sq_le_four_div_norm_of_re_nonneg_norm_ge_one s hsre hnorm
    _ = (4 : ℝ) / ‖s‖ ^ 2 := by
          field_simp [ne_of_gt hnorm_pos]

/-- The Stirling-model phase at the stationary point already carries the
expected alternating anchor `(-1)^(n+1) * exp(-iπ/8)` up to `O((n+1)⁻²)`. -/
theorem stirlingStartAnchor_asymptotic :
    ∃ C > 0, ∀ n : ℕ,
      ‖Complex.exp
          (Complex.I *
            (((stirlingApprox (hardyStart n)).im
                - (hardyStart n / 2) * Real.log (Real.pi * ((n : ℝ) + 1) ^ 2)) : ℂ))
        - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖
          ≤ C / ((n : ℝ) + 1) ^ 2 := by
  obtain ⟨C0, hC0evt⟩ := stirling_approx_im_asymptotic.bound
  rcases Filter.eventually_atTop.mp hC0evt with ⟨T0, hT0⟩
  let N : ℕ := Nat.ceil (max 1 (T0 / (2 * Real.pi)))
  let C : ℝ := max (2 * (N : ℝ) ^ 2) (C0 / (2 * Real.pi))
  have hN_pos : 1 ≤ N := by
    have hN_real : (1 : ℝ) ≤ (N : ℝ) := by
      exact le_trans (le_max_left _ _) (Nat.le_ceil _)
    exact_mod_cast hN_real
  have hC_pos : 0 < C := by
    apply lt_of_lt_of_le (show (0 : ℝ) < 2 * (N : ℝ) ^ 2 by
      have hN_real : (1 : ℝ) ≤ N := by exact_mod_cast hN_pos
      nlinarith)
    exact le_max_left _ _
  refine ⟨C, hC_pos, ?_⟩
  intro n
  set m : ℝ := (n : ℝ) + 1
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hm_ge_one : 1 ≤ m := by
    dsimp [m]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  let phase : ℝ :=
    (stirlingApprox (hardyStart n)).im
      - (hardyStart n / 2) * Real.log (Real.pi * m ^ 2)
  let target : ℝ := -(Real.pi * m ^ 2) - Real.pi / 8
  have htarget_exp :
      Complex.exp (Complex.I * (target : ℂ))
        = ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor) := by
    have htarget :
        target = -(Real.pi * (((n : ℝ) + 1) ^ 2)) - Real.pi / 8 := by
      simp [target, m]
    have hsplit :
        Complex.I * (target : ℂ)
          = Complex.I * ((-(Real.pi * (((n : ℝ) + 1) ^ 2)) : ℝ) : ℂ)
              + Complex.I * ((-(Real.pi / 8 : ℝ)) : ℂ) := by
      rw [htarget, sub_eq_add_neg, Complex.ofReal_add, mul_add]
      simp
    have hfirst :
        Complex.exp (Complex.I * ((-(Real.pi * (((n : ℝ) + 1) ^ 2)) : ℝ) : ℂ))
          = ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ)) := by
      simpa using (exp_neg_pi_sq_mul_I (n + 1))
    have hsecond :
        Complex.exp (Complex.I * ((-(Real.pi / 8 : ℝ)) : ℂ)) = hardyStationaryAnchor := by
      simp [hardyStationaryAnchor, mul_comm, mul_left_comm, mul_assoc]
    rw [hsplit, Complex.exp_add, hfirst, hsecond]
  by_cases hlarge : (N : ℝ) ≤ m
  · have hT0_le : T0 ≤ hardyStart n := by
      have hN_ge : max 1 (T0 / (2 * Real.pi)) ≤ (N : ℝ) := Nat.le_ceil _
      have hquot : T0 / (2 * Real.pi) ≤ m := by
        have h1 : T0 / (2 * Real.pi) ≤ max 1 (T0 / (2 * Real.pi)) := le_max_right _ _
        exact le_trans h1 (le_trans hN_ge hlarge)
      have hm_le_sq : m ≤ m ^ 2 := by
        nlinarith
      have hmul : T0 ≤ m * (2 * Real.pi) := by
        exact (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).1 hquot
      rw [hardyStart_formula]
      calc
        T0 ≤ 2 * Real.pi * m := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        _ ≤ 2 * Real.pi * m ^ 2 := by
          nlinarith [Real.pi_pos, hm_le_sq]
        _ = 2 * Real.pi * ((n : ℝ) + 1) ^ 2 := by simp [m]
    have happrox := hT0 (hardyStart n) hT0_le
    have hphase_main :
        ‖phase - target‖
          ≤ (C0 / (2 * Real.pi)) / m ^ 2 := by
      have hrewrite :
          phase - target
            = (stirlingApprox (hardyStart n)).im
                - (((hardyStart n) / 2) * Real.log ((hardyStart n) / 2)
                    - (hardyStart n) / 2 - Real.pi / 8) := by
        dsimp [phase, target, m]
        rw [hardyStart_half]
        ring_nf
      have happrox' : ‖phase - target‖ ≤ C0 * ‖(1 : ℝ) / hardyStart n‖ := by
        rw [hrewrite]
        exact happrox
      rw [hardyStart_formula] at happrox'
      have hm_sq_pos : 0 < m ^ 2 := sq_pos_of_pos hm_pos
      have habs :
          ‖(1 : ℝ) / (2 * Real.pi * m ^ 2)‖ = 1 / (2 * Real.pi * m ^ 2) := by
        rw [Real.norm_eq_abs, abs_of_pos]
        positivity
      calc
        ‖phase - target‖ ≤ C0 * ‖(1 : ℝ) / (2 * Real.pi * m ^ 2)‖ := happrox'
        _ = C0 / (2 * Real.pi * m ^ 2) := by rw [habs]; ring
        _ = (C0 / (2 * Real.pi)) / m ^ 2 := by
              field_simp [Real.pi_ne_zero, ne_of_gt hm_sq_pos]
    have hfactor :
        Complex.exp (phase * Complex.I)
          - Complex.exp (target * Complex.I)
            = Complex.exp (target * Complex.I)
                * (Complex.exp ((phase - target) * Complex.I) - 1) := by
      calc
        Complex.exp (phase * Complex.I) - Complex.exp (target * Complex.I)
            = Complex.exp (target * Complex.I + (phase - target) * Complex.I)
                - Complex.exp (target * Complex.I) := by
                  congr 1
                  ring
        _ = Complex.exp (target * Complex.I) * Complex.exp ((phase - target) * Complex.I)
              - Complex.exp (target * Complex.I) := by
                rw [Complex.exp_add]
        _ = Complex.exp (target * Complex.I)
              * (Complex.exp ((phase - target) * Complex.I) - 1) := by
                ring
    have hmain :
        ‖Complex.exp (Complex.I * (phase : ℂ))
            - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖
          ≤ C / m ^ 2 := by
      calc
        ‖Complex.exp (Complex.I * (phase : ℂ))
            - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖
            = ‖Complex.exp (phase * Complex.I)
                - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖ := by
                  simp [mul_comm]
        _ = ‖Complex.exp (phase * Complex.I)
                - Complex.exp (target * Complex.I)‖ := by
                  rw [← htarget_exp]
                  simp [mul_comm]
        _ = ‖Complex.exp (target * Complex.I)
              * (Complex.exp ((phase - target) * Complex.I) - 1)‖ := by
                rw [hfactor]
        _ = ‖Complex.exp (target * Complex.I)‖
              * ‖Complex.exp ((phase - target) * Complex.I) - 1‖ := by
                rw [norm_mul]
        _ = ‖Complex.exp ((phase - target) * Complex.I) - 1‖ := by
                simp [Complex.norm_exp_I_mul_ofReal]
        _ ≤ ‖phase - target‖ := by
              simpa [mul_comm] using
                (Real.norm_exp_I_mul_ofReal_sub_one_le (x := phase - target))
        _ ≤ (C0 / (2 * Real.pi)) / m ^ 2 := hphase_main
        _ ≤ C / m ^ 2 := by
              exact div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg m)
    simpa [phase, m] using hmain
  · have hsmall : m < N := lt_of_not_ge hlarge
    have hnorm_anchor : ‖hardyStationaryAnchor‖ = 1 := by
      rw [hardyStationaryAnchor]
      simpa [mul_comm] using (Complex.norm_exp_I_mul_ofReal (-(Real.pi / 8)))
    have hnorm_target :
        ‖(((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor‖ = 1 := by
      rw [norm_mul, hnorm_anchor]
      simp
    have hdiff_two :
        ‖Complex.exp (Complex.I * (phase : ℂ))
            - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖ ≤ 2 := by
      calc
        ‖Complex.exp (Complex.I * (phase : ℂ))
            - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖
            ≤ ‖Complex.exp (Complex.I * (phase : ℂ))‖
              + ‖(((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor‖ := by
                exact norm_sub_le _ _
        _ = 1 + 1 := by
              rw [hnorm_target]
              simp [Complex.norm_exp_I_mul_ofReal]
        _ = 2 := by norm_num
    have hN_sq : m ^ 2 < (N : ℝ) ^ 2 := by
      have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN_pos
      nlinarith
    have hsmall_bound : 2 ≤ (2 * (N : ℝ) ^ 2) / m ^ 2 := by
      have hm_sq_pos : 0 < m ^ 2 := sq_pos_of_pos hm_pos
      have hNN : m ^ 2 ≤ (N : ℝ) ^ 2 := le_of_lt hN_sq
      have hratio : 1 ≤ (N : ℝ) ^ 2 / m ^ 2 := by
        rw [one_le_div hm_sq_pos]
        exact hNN
      have htwo : 2 ≤ 2 * ((N : ℝ) ^ 2 / m ^ 2) := by
        nlinarith
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htwo
    have hmain :
        ‖Complex.exp (Complex.I * (phase : ℂ))
            - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖
          ≤ C / m ^ 2 := by
      calc
        ‖Complex.exp (Complex.I * (phase : ℂ))
            - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖
            ≤ 2 := hdiff_two
        _ ≤ (2 * (N : ℝ) ^ 2) / m ^ 2 := hsmall_bound
        _ ≤ C / m ^ 2 := by
              exact div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg m)
    simpa [phase, m] using hmain

private lemma gamma_ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    s ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp only [neg_re, natCast_re] at hre
  linarith [Nat.cast_nonneg (α := ℝ) m]

private theorem analyticOnNhd_Gamma_re_pos :
    AnalyticOnNhd ℂ Complex.Gamma {s : ℂ | 0 < s.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const continuous_re)
  intro s hs
  exact (Complex.differentiableAt_Gamma s (gamma_ne_neg_nat_of_re_pos hs)).differentiableWithinAt

private def gammaLog : ℂ → ℂ :=
  Classical.choose <|
    Aristotle.Standalone.analytic_log_on_halfPlane' 0 Complex.Gamma
      analyticOnNhd_Gamma_re_pos
      (fun s hs => Complex.Gamma_ne_zero_of_re_pos hs)

private theorem gammaLog_analytic :
    AnalyticOnNhd ℂ gammaLog {s : ℂ | 0 < s.re} :=
  (Classical.choose_spec <|
    Aristotle.Standalone.analytic_log_on_halfPlane' 0 Complex.Gamma
      analyticOnNhd_Gamma_re_pos
      (fun s hs => Complex.Gamma_ne_zero_of_re_pos hs)).1

private theorem exp_gammaLog_eq (s : ℂ) (hs : 0 < s.re) :
    Complex.exp (gammaLog s) = Complex.Gamma s :=
  (Classical.choose_spec <|
    Aristotle.Standalone.analytic_log_on_halfPlane' 0 Complex.Gamma
      analyticOnNhd_Gamma_re_pos
      (fun s hs => Complex.Gamma_ne_zero_of_re_pos hs)).2 s hs

private lemma exp_I_mul_im_gammaLog_eq_gamma_div_norm {s : ℂ} (hs : 0 < s.re) :
    Complex.exp (Complex.I * ((gammaLog s).im : ℂ))
      = Complex.Gamma s / ↑‖Complex.Gamma s‖ := by
  have hne : ((Real.exp (gammaLog s).re : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hdecomp :
      Complex.exp (gammaLog s)
        = (Real.exp (gammaLog s).re : ℂ) * Complex.exp (Complex.I * ((gammaLog s).im : ℂ)) := by
    calc
      Complex.exp (gammaLog s)
          = Complex.exp ((gammaLog s).re + Complex.I * ((gammaLog s).im : ℂ)) := by
              congr 1
              simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
                (Complex.re_add_im (gammaLog s)).symm
      _ = Complex.exp ((gammaLog s).re) * Complex.exp (Complex.I * ((gammaLog s).im : ℂ)) := by
            rw [Complex.exp_add]
      _ = (Real.exp (gammaLog s).re : ℂ) * Complex.exp (Complex.I * ((gammaLog s).im : ℂ)) := by
            rw [Complex.ofReal_exp]
  calc
    Complex.exp (Complex.I * ((gammaLog s).im : ℂ))
        = ((Real.exp (gammaLog s).re : ℂ) * Complex.exp (Complex.I * ((gammaLog s).im : ℂ))) /
            (Real.exp (gammaLog s).re : ℂ) := by
              field_simp [hne]
    _ = Complex.exp (gammaLog s) / ↑‖Complex.exp (gammaLog s)‖ := by
          rw [hdecomp, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_exp_I_mul_ofReal]
          norm_num
    _ = Complex.Gamma s / ↑‖Complex.Gamma s‖ := by
          simpa [exp_gammaLog_eq s hs]

private lemma stirlingTerm_ofReal (x : ℝ) (hx : 0 < x) :
    stirlingTerm x = ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * Real.pi) : ℝ) := by
  rw [stirlingTerm]
  rw [← Complex.ofReal_log (le_of_lt hx)]
  rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by
    push_cast
    ring]
  rw [← Complex.ofReal_log (by positivity : 0 ≤ 2 * Real.pi)]
  norm_num

private lemma exp_I_mul_im_gammaLog_sub_stirlingTerm_eq_one_of_pos (x : ℝ) (hx : 0 < x) :
    Complex.exp (Complex.I * (((gammaLog x - stirlingTerm x).im) : ℂ)) = 1 := by
  have hgamma_phase :
      Complex.exp (Complex.I * ((gammaLog x).im : ℂ))
        = 1 := by
    calc
      Complex.exp (Complex.I * ((gammaLog x).im : ℂ))
          = Complex.Gamma x / ↑‖Complex.Gamma x‖ :=
            exp_I_mul_im_gammaLog_eq_gamma_div_norm hx
      _ = 1 := by
            rw [Complex.Gamma_ofReal]
            have hΓpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
            have hΓne : (Real.Gamma x : ℂ) ≠ 0 := by
              exact Complex.ofReal_ne_zero.mpr hΓpos.ne'
            rw [Complex.norm_real, Real.norm_of_nonneg hΓpos.le, div_eq_iff hΓne]
            norm_num
  have hstirling_real : (stirlingTerm x).im = 0 := by
    rw [stirlingTerm_ofReal x hx]
    simp
  calc
    Complex.exp (Complex.I * (((gammaLog x - stirlingTerm x).im) : ℂ))
        = Complex.exp (Complex.I * ((gammaLog x).im : ℂ)) := by
              rw [sub_im, hstirling_real, sub_zero]
    _ = 1 := hgamma_phase

private lemma norm_exp_I_sub_exp_I_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ ‖a - b‖ := by
  have hmul :
      Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))
        = Complex.exp (Complex.I * (b : ℂ)) *
          (Complex.exp (Complex.I * ((a - b) : ℂ)) - 1) := by
    calc
      Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))
          = Complex.exp (Complex.I * ((b + (a - b)) : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) := by
              congr 1
              ring
      _ = Complex.exp (Complex.I * (b : ℂ) + Complex.I * ((a - b) : ℂ))
            - Complex.exp (Complex.I * (b : ℂ)) := by
              congr 1
              ring
      _ = Complex.exp (Complex.I * (b : ℂ)) * Complex.exp (Complex.I * ((a - b) : ℂ))
            - Complex.exp (Complex.I * (b : ℂ)) := by
              rw [Complex.exp_add]
      _ = Complex.exp (Complex.I * (b : ℂ)) *
            (Complex.exp (Complex.I * ((a - b) : ℂ)) - 1) := by
              ring
  calc
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖
        = ‖Complex.exp (Complex.I * (b : ℂ)) *
            (Complex.exp (Complex.I * ((a - b) : ℂ)) - 1)‖ := by
              rw [hmul]
    _ = ‖Complex.exp (Complex.I * (b : ℂ))‖
          * ‖Complex.exp (Complex.I * ((a - b) : ℂ)) - 1‖ := by
            rw [norm_mul]
    _ = ‖Complex.exp (Complex.I * ((a - b) : ℂ)) - 1‖ := by
          simp [Complex.norm_exp_I_mul_ofReal]
    _ ≤ ‖a - b‖ := by
          simpa using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

private theorem differentiableAt_gammaLog {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ gammaLog s :=
  (gammaLog_analytic s hs).differentiableAt

private theorem deriv_gammaLog_eq (s : ℂ) (hs : 0 < s.re) :
    deriv gammaLog s = deriv Complex.Gamma s / Complex.Gamma s := by
  have hdiff : DifferentiableAt ℂ gammaLog s := differentiableAt_gammaLog hs
  have hcomp :
      HasDerivAt (fun z => Complex.exp (gammaLog z))
        (Complex.exp (gammaLog s) * deriv gammaLog s) s := by
    simpa using (Complex.hasDerivAt_exp (gammaLog s)).comp s hdiff.hasDerivAt
  have hEq :
      (fun z => Complex.exp (gammaLog z)) =ᶠ[𝓝 s] Complex.Gamma := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    simpa using exp_gammaLog_eq z hz
  have hGamma :
      HasDerivAt Complex.Gamma (deriv Complex.Gamma s) s :=
    (Complex.differentiableAt_Gamma s (gamma_ne_neg_nat_of_re_pos hs)).hasDerivAt
  have hmul : Complex.exp (gammaLog s) * deriv gammaLog s = deriv Complex.Gamma s := by
    exact (hcomp.congr_of_eventuallyEq hEq.symm).unique hGamma
  have hGamma_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  rw [eq_div_iff hGamma_ne]
  simpa [exp_gammaLog_eq s hs, mul_comm] using hmul

private theorem hasDerivAt_gammaLog (s : ℂ) (hs : 0 < s.re) :
    HasDerivAt gammaLog (deriv Complex.Gamma s / Complex.Gamma s) s := by
  simpa [deriv_gammaLog_eq s hs] using (differentiableAt_gammaLog hs).hasDerivAt

private theorem hasDerivAt_stirlingTerm (s : ℂ) (hs : 0 < s.re) :
    HasDerivAt stirlingTerm (Complex.log s - 1 / (2 * s)) s := by
  have hs_slit : s ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hs
  have hs_ne : s ≠ 0 := Complex.slitPlane_ne_zero hs_slit
  change HasDerivAt
    (fun x => (x - 1 / 2) * Complex.log x - x + 1 / 2 * Complex.log (2 * Real.pi))
    (Complex.log s - 1 / (2 * s)) s
  have hlog : HasDerivAt Complex.log s⁻¹ s := Complex.hasDerivAt_log hs_slit
  have hprod :
      HasDerivAt (fun z => (z - 1 / 2) * Complex.log z)
        (((1 : ℂ) * Complex.log s) + (s - 1 / 2) * s⁻¹) s := by
    simpa using ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).mul hlog
  have hmain := (hprod.sub (hasDerivAt_id s)).add_const ((1 / 2 : ℂ) * Complex.log (2 * Real.pi))
  have hsimp :
      Complex.log s + (s - (2 : ℂ)⁻¹) * s⁻¹ - 1 = Complex.log s - s⁻¹ * (2 : ℂ)⁻¹ := by
    field_simp [hs_ne]
    ring
  simpa [hsimp] using hmain

private theorem hasSum_half_inv_telescope (s : ℂ) (hs : 0 < s.re) (hnorm : 1 ≤ ‖s‖) :
    HasSum
      (fun n : ℕ =>
        1 / (2 * (s + (n : ℂ))) - 1 / (2 * (s + ((n + 1 : ℕ) : ℂ))))
      (1 / (2 * s)) := by
  have hsre : 0 ≤ s.re := le_of_lt hs
  have hsumm_norm :
      Summable
        (fun n : ℕ =>
          ‖1 / (2 * (s + (n : ℂ))) - 1 / (2 * (s + ((n + 1 : ℕ) : ℂ)))‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
      ((summable_inv_norm_add_natCast_sq_of_re_nonneg s hsre).mul_left (1 / 2))
    intro n
    have hsn : s + (n : ℂ) ≠ 0 := add_natCast_ne_zero s hs n
    have hsn1 : s + ((n + 1 : ℕ) : ℂ) ≠ 0 := add_natCast_ne_zero s hs (n + 1)
    have hsre_n : 0 ≤ (s + (n : ℂ)).re := by
      simp only [add_re, natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hmono : ‖s + (n : ℂ)‖ ≤ ‖s + ((n + 1 : ℕ) : ℂ)‖ := by
      simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
        (norm_le_norm_add_natCast (s := s + (n : ℂ)) hsre_n 1)
    have hnorm_pos : 0 < ‖s + (n : ℂ)‖ := by
      exact norm_pos_iff.mpr hsn
    have hnorm_pos1 : 0 < ‖s + ((n + 1 : ℕ) : ℂ)‖ := by
      exact norm_pos_iff.mpr hsn1
    calc
      ‖1 / (2 * (s + (n : ℂ))) - 1 / (2 * (s + ((n + 1 : ℕ) : ℂ)))‖
          = ‖1 / ((2 : ℂ) * (s + (n : ℂ)) * (s + ((n + 1 : ℕ) : ℂ)))‖ := by
              have hEq :
                  1 / (2 * (s + (n : ℂ))) - 1 / (2 * (s + ((n + 1 : ℕ) : ℂ)))
                    = 1 / ((2 : ℂ) * (s + (n : ℂ)) * (s + ((n + 1 : ℕ) : ℂ))) := by
                  field_simp [hsn, hsn1]
                  norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
              rw [hEq]
      _ = 1 / (2 * ‖s + (n : ℂ)‖ * ‖s + ((n + 1 : ℕ) : ℂ)‖) := by
            rw [norm_div, norm_one, norm_mul, norm_mul]
            norm_num
      _ = (1 / 2) * ((1 : ℝ) / ‖s + (n : ℂ)‖) * ((1 : ℝ) / ‖s + ((n + 1 : ℕ) : ℂ)‖) := by
            field_simp [hnorm_pos.ne', hnorm_pos1.ne']
      _ ≤ (1 / 2) * ((1 : ℝ) / ‖s + (n : ℂ)‖) * ((1 : ℝ) / ‖s + (n : ℂ)‖) := by
            have hInv : (1 : ℝ) / ‖s + ((n + 1 : ℕ) : ℂ)‖ ≤ (1 : ℝ) / ‖s + (n : ℂ)‖ :=
              one_div_le_one_div_of_le hnorm_pos hmono
            have hpref : 0 ≤ (1 / 2) * ((1 : ℝ) / ‖s + (n : ℂ)‖) := by positivity
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hInv hpref
      _ = (1 / 2) * ((1 : ℝ) / ‖s + (n : ℂ)‖ ^ 2) := by
            ring
  rw [hasSum_iff_tendsto_nat_of_summable_norm hsumm_norm]
  have hpartial :
      ∀ N : ℕ,
        ∑ i ∈ Finset.range N,
            (1 / (2 * (s + (i : ℂ))) - 1 / (2 * (s + ((i + 1 : ℕ) : ℂ))))
          = 1 / (2 * s) - 1 / (2 * (s + (N : ℂ))) := by
    intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  simp_rw [hpartial]
  have h_inv_tend :
      Tendsto (fun N : ℕ => 1 / (2 * (s + (N : ℂ)))) atTop (𝓝 0) := by
    have hbase :
        Tendsto (fun N : ℕ => (s + (N : ℂ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv₀_cobounded.comp
        ((tendsto_const_add_cobounded s).comp tendsto_natCast_atTop_cobounded)
    have hhalf :
        Tendsto (fun N : ℕ => (1 / 2 : ℂ) * (s + (N : ℂ))⁻¹) atTop (𝓝 0) := by
      simpa using hbase.const_mul ((1 / 2 : ℂ))
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hhalf
  simpa using (tendsto_const_nhds.sub h_inv_tend)

private theorem summable_gaussTerm_of_norm_ge_100_div_99
    (s : ℂ) (hs : 0 < s.re) (hbig : (100 : ℝ) / 99 ≤ ‖s‖) :
    Summable (fun n : ℕ => GammaSeqLocalUniform.gaussTerm (s + (n : ℂ))) := by
  have hsre : 0 ≤ s.re := le_of_lt hs
  refine Summable.of_norm_bounded
    ((summable_inv_norm_add_natCast_sq_of_re_nonneg s hsre).mul_left (50 : ℝ)) ?_
  intro n
  have hnorm_ge : (100 : ℝ) / 99 ≤ ‖s + (n : ℂ)‖ := by
    exact le_trans hbig (norm_le_norm_add_natCast s hsre n)
  simpa [GammaSeqLocalUniform.gaussTerm] using
    (Aristotle.DigammaBinetBound.gauss_term_bound_of_norm_ge_100_div_99
      (w := s + (n : ℂ)) hnorm_ge)

private theorem summable_gaussStirlingCorrectionTerm_of_norm_ge_100_div_99
    (s : ℂ) (hs : 0 < s.re) (hbig : (100 : ℝ) / 99 ≤ ‖s‖) :
    Summable (fun n : ℕ => gaussStirlingCorrectionTerm (s + (n : ℂ))) := by
  have hsre : 0 ≤ s.re := le_of_lt hs
  have hnorm : 1 ≤ ‖s‖ := by
    linarith
  refine Summable.of_norm_bounded
    ((summable_inv_norm_add_natCast_cu_of_re_nonneg_norm_ge_one s hsre hnorm).mul_left (100 : ℝ))
    ?_
  intro n
  have hnorm_ge : (100 : ℝ) / 99 ≤ ‖s + (n : ℂ)‖ := by
    exact le_trans hbig (norm_le_norm_add_natCast s hsre n)
  simpa [div_eq_mul_inv, mul_assoc] using
    (gaussStirlingCorrectionTerm_bound_of_norm_ge_100_div_99 (w := s + (n : ℂ)) hnorm_ge)

private theorem gammaLog_sub_stirlingTerm_deriv_eq_tsum
    (s : ℂ) (hs : 0 < s.re) (hbig : (100 : ℝ) / 99 ≤ ‖s‖) :
    deriv (fun z => gammaLog z - stirlingTerm z) s
      = ∑' n : ℕ, gaussStirlingCorrectionTerm (s + (n : ℂ)) := by
  have hnorm : 1 ≤ ‖s‖ := by
    linarith
  have hsumm_gauss :
      Summable (fun n : ℕ => GammaSeqLocalUniform.gaussTerm (s + (n : ℂ))) :=
    summable_gaussTerm_of_norm_ge_100_div_99 s hs hbig
  have hgauss :
      deriv Complex.Gamma s / Complex.Gamma s - Complex.log s
        = ∑' n : ℕ, GammaSeqLocalUniform.gaussTerm (s + (n : ℂ)) := by
    exact GammaSeqLocalUniform.gauss_series_identity s hs
      (Complex.Gamma_ne_zero_of_re_pos hs) hsumm_gauss
  have hgauss_hasSum :
      HasSum (fun n : ℕ => GammaSeqLocalUniform.gaussTerm (s + (n : ℂ)))
        (deriv Complex.Gamma s / Complex.Gamma s - Complex.log s) :=
    hsumm_gauss.hasSum_iff.2 hgauss.symm
  have htel :
      HasSum
        (fun n : ℕ =>
          1 / (2 * (s + (n : ℂ))) - 1 / (2 * (s + ((n + 1 : ℕ) : ℂ))))
        (1 / (2 * s)) :=
    hasSum_half_inv_telescope s hs hnorm
  have hcorr :
      HasSum (fun n : ℕ => gaussStirlingCorrectionTerm (s + (n : ℂ)))
        ((deriv Complex.Gamma s / Complex.Gamma s - Complex.log s) + 1 / (2 * s)) := by
    simpa [gaussStirlingCorrectionTerm, GammaSeqLocalUniform.gaussTerm,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hgauss_hasSum.add htel
  have hderiv :
      HasDerivAt (fun z => gammaLog z - stirlingTerm z)
        (deriv Complex.Gamma s / Complex.Gamma s - (Complex.log s - 1 / (2 * s))) s :=
    (hasDerivAt_gammaLog s hs).sub (hasDerivAt_stirlingTerm s hs)
  calc
    deriv (fun z => gammaLog z - stirlingTerm z) s
        = deriv Complex.Gamma s / Complex.Gamma s - (Complex.log s - 1 / (2 * s)) := hderiv.deriv
    _ = (deriv Complex.Gamma s / Complex.Gamma s - Complex.log s) + 1 / (2 * s) := by
          ring
    _ = ∑' n : ℕ, gaussStirlingCorrectionTerm (s + (n : ℂ)) := by
          symm
          exact hcorr.tsum_eq

private theorem deriv_gammaLog_sub_stirlingTerm_bound
    (s : ℂ) (hs : 0 < s.re) (hbig : (100 : ℝ) / 99 ≤ ‖s‖) :
    ‖deriv (fun z => gammaLog z - stirlingTerm z) s‖ ≤ (400 : ℝ) / ‖s‖ ^ 2 := by
  have hsre : 0 ≤ s.re := le_of_lt hs
  have hnorm : 1 ≤ ‖s‖ := by
    linarith
  have hsumm_corr :
      Summable (fun n : ℕ => gaussStirlingCorrectionTerm (s + (n : ℂ))) :=
    summable_gaussStirlingCorrectionTerm_of_norm_ge_100_div_99 s hs hbig
  have hsumm_major :
      Summable (fun n : ℕ => (100 : ℝ) / ‖s + (n : ℂ)‖ ^ 3) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      (summable_inv_norm_add_natCast_cu_of_re_nonneg_norm_ge_one s hsre hnorm).mul_left (100 : ℝ)
  have hterm :
      ∀ n : ℕ, ‖gaussStirlingCorrectionTerm (s + (n : ℂ))‖ ≤ (100 : ℝ) / ‖s + (n : ℂ)‖ ^ 3 := by
    intro n
    have hnorm_ge : (100 : ℝ) / 99 ≤ ‖s + (n : ℂ)‖ := by
      exact le_trans hbig (norm_le_norm_add_natCast s hsre n)
    exact gaussStirlingCorrectionTerm_bound_of_norm_ge_100_div_99 (w := s + (n : ℂ)) hnorm_ge
  have htsum_le :
      (∑' n : ℕ, ‖gaussStirlingCorrectionTerm (s + (n : ℂ))‖)
        ≤ ∑' n : ℕ, (100 : ℝ) / ‖s + (n : ℂ)‖ ^ 3 :=
    hsumm_corr.norm.tsum_le_tsum hterm hsumm_major
  rw [gammaLog_sub_stirlingTerm_deriv_eq_tsum s hs hbig]
  calc
    ‖∑' n : ℕ, gaussStirlingCorrectionTerm (s + (n : ℂ))‖
        ≤ ∑' n : ℕ, ‖gaussStirlingCorrectionTerm (s + (n : ℂ))‖ :=
          norm_tsum_le_tsum_norm hsumm_corr.norm
    _ ≤ ∑' n : ℕ, (100 : ℝ) / ‖s + (n : ℂ)‖ ^ 3 := htsum_le
    _ = (100 : ℝ) * (∑' n : ℕ, (1 : ℝ) / ‖s + (n : ℂ)‖ ^ 3) := by
          simp [div_eq_mul_inv, mul_assoc, tsum_mul_left]
    _ ≤ (100 : ℝ) * ((4 : ℝ) / ‖s‖ ^ 2) := by
          gcongr
          exact tsum_inv_norm_add_natCast_cu_le_four_div_sq_norm_of_re_nonneg_norm_ge_one s hsre hnorm
    _ = (400 : ℝ) / ‖s‖ ^ 2 := by ring

private lemma stirlingTerm_quarter_line (t : ℝ) :
    stirlingTerm (1 / 4 + Complex.I * (t / 2)) = stirlingApprox t := by
  unfold stirlingTerm stirlingApprox
  congr 1 <;> ring

private lemma lineMap_large_real_to_quarter_line_re_ge
    {y θ : ℝ} (hy : 1 / 4 ≤ y) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    1 / 4 ≤
      (AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ).re := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ 1 := hθ.2
  simp [AffineMap.lineMap_apply, hθ0, hθ1]
  nlinarith

private lemma lineMap_large_real_to_quarter_line_norm_lower
    {y θ : ℝ} (hy : 0 ≤ y) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    y / 2 ≤ ‖AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ‖ := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ 1 := hθ.2
  rcases le_total θ (1 / 2 : ℝ) with hθle | hθge
  · have hre :
        y / 2 ≤ (AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ).re := by
      simp [AffineMap.lineMap_apply, hθ0, hθ1]
      nlinarith
    have hre_nonneg :
        0 ≤ (AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ).re := by
      linarith
    have habs :
        y / 2 ≤
          |(AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ).re| := by
      rw [abs_of_nonneg hre_nonneg]
      exact hre
    exact le_trans habs (Complex.abs_re_le_norm _)
  · have him :
        y / 2 ≤ (AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ).im := by
      simp [AffineMap.lineMap_apply, hθ0, hθ1]
      nlinarith
    have him_nonneg :
        0 ≤ (AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ).im := by
      linarith
    have habs :
        y / 2 ≤
          |(AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ).im| := by
      rw [abs_of_nonneg him_nonneg]
      exact him
    exact le_trans habs (Complex.abs_im_le_norm _)

private theorem gammaLog_sub_stirlingTerm_phase_at_hardyStart_asymptotic :
    ∃ C > 0, ∀ n : ℕ,
      ‖Complex.exp
          (Complex.I *
            ((((gammaLog (1 / 4 + Complex.I * ((hardyStart n / 2) : ℂ)) -
                  stirlingTerm (1 / 4 + Complex.I * ((hardyStart n / 2) : ℂ))).im) : ℂ)))
        - 1‖
          ≤ C / ((n : ℝ) + 1) ^ 2 := by
  let C : ℝ := 3200 / Real.pi
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro n
  set m : ℝ := (n : ℝ) + 1
  set y : ℝ := Real.pi * m ^ 2
  set s : ℂ := 1 / 4 + Complex.I * (y : ℂ)
  set x : ℂ := (y : ℂ)
  let g : ℂ → ℂ := fun z => gammaLog z - stirlingTerm z
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hm_ge_one : 1 ≤ m := by
    dsimp [m]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hy_pos : 0 < y := by
    dsimp [y]
    positivity
  have hy_ge_quarter : 1 / 4 ≤ y := by
    dsimp [y]
    nlinarith [Real.pi_gt_three, hm_ge_one]
  have hy_half_big : (100 : ℝ) / 99 ≤ y / 2 := by
    dsimp [y]
    nlinarith [Real.pi_gt_three, hm_ge_one]
  have hdiff_on : ∀ z ∈ segment ℝ x s, DifferentiableAt ℂ g z := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨θ, hθ, rfl⟩
    have hre : 0 < (AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ).re := by
      have hre_ge :
          1 / 4 ≤
            (AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ).re :=
        lineMap_large_real_to_quarter_line_re_ge hy_ge_quarter hθ
      linarith
    exact (differentiableAt_gammaLog hre).sub
      (hasDerivAt_stirlingTerm _ hre).differentiableAt
  have hbound_on : ∀ z ∈ segment ℝ x s, ‖deriv g z‖ ≤ (1600 : ℝ) / y ^ 2 := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨θ, hθ, rfl⟩
    have hre : 0 < (AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ).re := by
      have hre_ge :
          1 / 4 ≤
            (AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ).re :=
        lineMap_large_real_to_quarter_line_re_ge hy_ge_quarter hθ
      linarith
    have hnorm_lower :
        y / 2 ≤ ‖AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ‖ :=
      lineMap_large_real_to_quarter_line_norm_lower hy_pos.le hθ
    have hbig :
        (100 : ℝ) / 99 ≤ ‖AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ‖ := by
      exact le_trans hy_half_big hnorm_lower
    have hy_half_pos : 0 < y / 2 := by positivity
    calc
      ‖deriv g (AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ)‖
          ≤ (400 : ℝ) /
              ‖AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ‖ ^ 2 := by
                simpa [g] using
                  deriv_gammaLog_sub_stirlingTerm_bound
                    (AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ) hre hbig
      _ ≤ (400 : ℝ) / (y / 2) ^ 2 := by
            have hInv :
                (1 : ℝ) /
                    ‖AffineMap.lineMap (y : ℂ) (1 / 4 + Complex.I * (y : ℂ)) θ‖ ^ 2
                  ≤ (1 : ℝ) / (y / 2) ^ 2 := by
              apply one_div_le_one_div_of_le (sq_pos_of_pos hy_half_pos)
              nlinarith [hnorm_lower]
            gcongr
      _ = (1600 : ℝ) / y ^ 2 := by
            field_simp [ne_of_gt hy_pos]
            ring
  have hmvt :
      ‖g s - g x‖ ≤ ((1600 : ℝ) / y ^ 2) * ‖s - x‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (f := g) (s := segment ℝ x s) hdiff_on hbound_on (convex_segment x s)
      (left_mem_segment ℝ x s) (right_mem_segment ℝ x s)
  have hdist : ‖s - x‖ ≤ 2 * y := by
    have hrew : s - x = (((1 / 4 : ℝ) - y : ℝ) : ℂ) + Complex.I * (y : ℂ) := by
      simp [s, x]
      ring
    rw [hrew]
    calc
      ‖(((1 / 4 : ℝ) - y : ℝ) : ℂ) + Complex.I * (y : ℂ)‖
          ≤ ‖((((1 / 4 : ℝ) - y : ℝ) : ℂ))‖ + ‖Complex.I * (y : ℂ)‖ := norm_add_le _ _
      _ = |(1 / 4 : ℝ) - y| + y := by
            rw [Complex.norm_real, norm_mul, Complex.norm_I, Complex.norm_real]
            simp [Real.norm_eq_abs, abs_of_nonneg hy_pos.le]
      _ = (y - 1 / 4) + y := by
            have hnonpos : (1 / 4 : ℝ) - y ≤ 0 := by linarith
            rw [abs_of_nonpos hnonpos]
            ring
      _ ≤ 2 * y := by linarith
  have hdelta : ‖g s - g x‖ ≤ (3200 : ℝ) / y := by
    calc
      ‖g s - g x‖ ≤ ((1600 : ℝ) / y ^ 2) * ‖s - x‖ := hmvt
      _ ≤ ((1600 : ℝ) / y ^ 2) * (2 * y) := by
            gcongr
      _ = (3200 : ℝ) / y := by
            field_simp [ne_of_gt hy_pos]
            ring
  have hphase_x :
      Complex.exp (Complex.I * (((g x).im) : ℂ)) = 1 := by
    simpa [g, x] using exp_I_mul_im_gammaLog_sub_stirlingTerm_eq_one_of_pos y hy_pos
  have him_le : ‖(g s).im - (g x).im‖ ≤ ‖g s - g x‖ := by
    simpa [Real.norm_eq_abs, sub_im] using (Complex.abs_im_le_norm (g s - g x))
  have hmain : ‖Complex.exp (Complex.I * (((g s).im) : ℂ)) - 1‖ ≤ C / m ^ 2 := by
    calc
    ‖Complex.exp (Complex.I * (((g s).im) : ℂ)) - 1‖
        = ‖Complex.exp (Complex.I * (((g s).im) : ℂ))
            - Complex.exp (Complex.I * (((g x).im) : ℂ))‖ := by
              rw [hphase_x]
    _ ≤ ‖(g s).im - (g x).im‖ := by
          simpa using norm_exp_I_sub_exp_I_le (a := (g s).im) (b := (g x).im)
    _ ≤ ‖g s - g x‖ := him_le
    _ ≤ (3200 : ℝ) / y := hdelta
    _ = C / m ^ 2 := by
          dsimp [C, y]
          field_simp [Real.pi_ne_zero, ne_of_gt hm_pos]
  have hhalfC :
      ((hardyStart n : ℂ) / 2) = ((Real.pi * (((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    exact_mod_cast hardyStart_half n
  have harg_eq :
      (1 / 4 + Complex.I * ((hardyStart n : ℂ) / 2))
        = 1 / 4 + Complex.I * ((Real.pi * (((n : ℝ) + 1) ^ 2) : ℂ)) := by
    rw [hhalfC]
    push_cast
    rfl
  rw [harg_eq]
  simpa [g, s, y, m, sub_im] using hmain

theorem hardyCosExp_at_hardyStart_asymptotic :
    ∃ C > 0, ∀ n : ℕ,
      ‖HardyCosSmooth.hardyCosExp n (hardyStart n) -
          ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖
        ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨Cphase, hCphase_pos, hphase⟩ :=
    gammaLog_sub_stirlingTerm_phase_at_hardyStart_asymptotic
  obtain ⟨Cmodel, hCmodel_pos, hmodel⟩ := stirlingStartAnchor_asymptotic
  let C : ℝ := Cphase + Cmodel
  refine ⟨C, add_pos hCphase_pos hCmodel_pos, ?_⟩
  intro n
  set m : ℝ := (n : ℝ) + 1
  set t : ℝ := hardyStart n
  set y : ℝ := Real.pi * m ^ 2
  set s : ℂ := 1 / 4 + Complex.I * (y : ℂ)
  let g : ℂ → ℂ := fun z => gammaLog z - stirlingTerm z
  let phaseErr : ℂ := Complex.exp (Complex.I * (((g s).im) : ℂ))
  let phaseModel : ℂ :=
    Complex.exp (Complex.I * (((stirlingApprox t).im) : ℂ)) *
      Complex.exp (-Complex.I * (((t / 2) * Real.log (Real.pi * m ^ 2)) : ℂ))
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hm_ge_one : 1 ≤ m := by
    dsimp [m]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hy_pos : 0 < y := by
    dsimp [y]
    positivity
  have ht_half : t / 2 = y := by
    simpa [t, y, m] using hardyStart_half n
  have hs_eq : s = 1 / 4 + Complex.I * ((t / 2) : ℂ) := by
    simpa [s] using congrArg (fun r : ℝ => (1 / 4 : ℂ) + Complex.I * (r : ℂ)) ht_half.symm
  have hs_re : 0 < s.re := by
    dsimp [s]
    norm_num
  have hstir : stirlingTerm s = stirlingApprox t := by
    rw [hs_eq]
    exact stirlingTerm_quarter_line t
  have hsplit_im : (gammaLog s).im = (g s).im + (stirlingApprox t).im := by
    have hsplit : gammaLog s = g s + stirlingTerm s := by
      dsimp [g]
      ring
    calc
      (gammaLog s).im = (g s + stirlingTerm s).im := by rw [hsplit]
      _ = (g s).im + (stirlingTerm s).im := by simp
      _ = (g s).im + (stirlingApprox t).im := by rw [hstir]
  have hhardy :
      HardyCosSmooth.hardyCosExp n t = phaseErr * phaseModel := by
    dsimp [phaseErr, phaseModel]
    have hgamma_eq :
        Complex.Gamma (1 / 4 + Complex.I * ((t / 2) : ℂ)) /
            ↑‖Complex.Gamma (1 / 4 + Complex.I * ((t / 2) : ℂ))‖
          = Complex.exp (Complex.I * ((gammaLog s).im : ℂ)) := by
      simpa [hs_eq] using (exp_I_mul_im_gammaLog_eq_gamma_div_norm hs_re).symm
    calc
      HardyCosSmooth.hardyCosExp n t
          = (Complex.Gamma (1 / 4 + Complex.I * ((t / 2) : ℂ)) /
                ↑‖Complex.Gamma (1 / 4 + Complex.I * ((t / 2) : ℂ))‖) *
              Complex.exp (-Complex.I * (((t / 2) * Real.log (Real.pi * m ^ 2)) : ℂ)) := by
                simp [HardyCosSmooth.hardyCosExp, m]
      _ = Complex.exp (Complex.I * ((gammaLog s).im : ℂ)) *
              Complex.exp (-Complex.I * (((t / 2) * Real.log (Real.pi * m ^ 2)) : ℂ)) := by
                rw [hgamma_eq]
      _ = Complex.exp (Complex.I * ((((g s).im + (stirlingApprox t).im) : ℝ) : ℂ)) *
            Complex.exp (-Complex.I * (((t / 2) * Real.log (Real.pi * m ^ 2)) : ℂ)) := by
              rw [hsplit_im]
      _ = (Complex.exp (Complex.I * (((g s).im) : ℂ)) *
              Complex.exp (Complex.I * (((stirlingApprox t).im) : ℂ))) *
            Complex.exp (-Complex.I * (((t / 2) * Real.log (Real.pi * m ^ 2)) : ℂ)) := by
              rw [show Complex.I * ((((g s).im + (stirlingApprox t).im) : ℝ) : ℂ)
                    = Complex.I * (((g s).im) : ℂ) + Complex.I * (((stirlingApprox t).im) : ℂ) by
                      simp [Complex.ofReal_add, mul_add]]
              rw [Complex.exp_add]
      _ = phaseErr * phaseModel := by
            simp [phaseErr, phaseModel, mul_assoc]
  have hphaseModel_norm : ‖phaseModel‖ = 1 := by
    dsimp [phaseModel]
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      Complex.norm_exp_ofReal_mul_I (-((t / 2) * Real.log (Real.pi * m ^ 2)))
  have hphase' : ‖phaseErr - 1‖ ≤ Cphase / m ^ 2 := by
    have hphase_raw := hphase n
    have hhalfC :
        ((hardyStart n : ℂ) / 2) = ((Real.pi * (((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
      exact_mod_cast hardyStart_half n
    have harg_eq :
        (1 / 4 + Complex.I * ((hardyStart n : ℂ) / 2))
          = 1 / 4 + Complex.I * ((Real.pi * (((n : ℝ) + 1) ^ 2) : ℂ)) := by
      rw [hhalfC]
      push_cast
      rfl
    rw [harg_eq] at hphase_raw
    simpa [phaseErr, g, s, y, m, sub_im] using hphase_raw
  have hphaseModel_eq :
      phaseModel =
        Complex.exp
          (Complex.I *
            (((stirlingApprox t).im - (t / 2) * Real.log (Real.pi * m ^ 2)) : ℂ)) := by
    dsimp [phaseModel]
    rw [← Complex.exp_add]
    congr 1
    ring
  have hmodel' :
      ‖phaseModel - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖
        ≤ Cmodel / m ^ 2 := by
    rw [hphaseModel_eq]
    simpa [t, m] using hmodel n
  have hmain_sq :
      ‖HardyCosSmooth.hardyCosExp n t -
          ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖
        ≤ C / m ^ 2 := by
    calc
      ‖HardyCosSmooth.hardyCosExp n t -
          ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖
          = ‖phaseErr * phaseModel -
              ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖ := by
                rw [hhardy]
      _ = ‖(phaseErr * phaseModel - phaseModel)
              + (phaseModel - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor))‖ := by
                ring
      _ ≤ ‖phaseErr * phaseModel - phaseModel‖
            + ‖phaseModel - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖ := by
              exact norm_add_le _ _
      _ = ‖phaseErr - 1‖
            + ‖phaseModel - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖ := by
              rw [show phaseErr * phaseModel - phaseModel = (phaseErr - 1) * phaseModel by ring,
                norm_mul, hphaseModel_norm, mul_one]
      _ ≤ Cphase / m ^ 2 + Cmodel / m ^ 2 := add_le_add hphase' hmodel'
      _ = C / m ^ 2 := by
            dsimp [C]
            ring
  calc
    ‖HardyCosSmooth.hardyCosExp n (hardyStart n) -
        ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖
        = ‖HardyCosSmooth.hardyCosExp n t -
            ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * hardyStationaryAnchor)‖ := by
              simp [t]
    _ ≤ C / m ^ 2 := hmain_sq
    _ ≤ C / m := by
          have hInv : (1 : ℝ) / m ^ 2 ≤ 1 / m := by
            apply one_div_le_one_div_of_le hm_pos
            nlinarith [hm_ge_one]
          have hC_nonneg : 0 ≤ C := by
            dsimp [C]
            positivity
          have hmul := mul_le_mul_of_nonneg_left hInv hC_nonneg
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

end Aristotle.StationaryPhaseStartValue
