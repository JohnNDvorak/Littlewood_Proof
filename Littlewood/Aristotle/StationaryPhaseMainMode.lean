import Mathlib
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.ComplexVdC
import Littlewood.Aristotle.HardyCosExpOmega
import Littlewood.Aristotle.HardyCosSmooth
import Littlewood.Aristotle.OffResonanceSmoothVdC
import Littlewood.Aristotle.StationaryPhaseStartValue

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.StationaryPhaseMainMode

open MeasureTheory Set Real Filter Topology intervalIntegral Complex
open HardyEstimatesPartial
open Aristotle.RSBlockParam
open Aristotle.HardyCosExpOmega
open Aristotle.OffResonanceSmoothVdC
open ThetaDerivAsymptotic
open ThetaDerivMonotone

/-- The branch-free Hardy mode written in the Riemann-Siegel block parameter. -/
def blockMode (n : ℕ) (p : ℝ) : ℂ :=
  HardyCosSmooth.hardyCosExp n (blockCoord n p)

/-- The corresponding angular velocity in block parameter coordinates. -/
def blockOmega (n : ℕ) (p : ℝ) : ℝ :=
  (thetaDeriv (blockCoord n p) - Real.log ((n : ℝ) + 1)) * blockJacobian n p

lemma blockCoord_sub_hardyStart (n : ℕ) (p : ℝ) :
    blockCoord n p - hardyStart n
      = 4 * Real.pi * ((n : ℝ) + 1) * p + 2 * Real.pi * p ^ 2 := by
  unfold blockCoord hardyStart
  ring

lemma blockJacobian_eq_affine (n : ℕ) (p : ℝ) :
    blockJacobian n p = 4 * Real.pi * ((n : ℝ) + 1) + 4 * Real.pi * p := by
  unfold blockJacobian
  ring

lemma blockMode_zero (n : ℕ) :
    blockMode n 0 = HardyCosSmooth.hardyCosExp n (hardyStart n) := by
  simp [blockMode, blockCoord_zero]

theorem blockMode_zero_asymptotic :
    ∃ C > 0, ∀ n : ℕ,
      ‖blockMode n 0 -
          ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
            Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)‖
        ≤ C / ((n : ℝ) + 1) := by
  simpa [blockMode_zero] using
    Aristotle.StationaryPhaseStartValue.hardyCosExp_at_hardyStart_asymptotic

/-- Exact `p = 2` phase-shift identity: the `p = 2` block is the
`(n+2)`-zero block multiplied by the exact phase mismatch coming from the
change in the logarithmic factor. -/
private lemma blockMode_p2_shifted_zero_factor (n : ℕ) :
    blockMode n 2 =
      blockMode (n + 2) 0 *
        Complex.exp
          (Complex.I *
            (((hardyStart (n + 2) *
                (Real.log (((n + 2 : ℕ) : ℝ) + 1) - Real.log ((n : ℝ) + 1)) : ℝ) : ℂ))) := by
  have hcoord : blockCoord n 2 = hardyStart (n + 2) := by
    unfold blockCoord hardyStart
    push_cast
    ring_nf
  have hcoord' : blockCoord (n + 2) 0 = hardyStart (n + 2) := by
    unfold blockCoord hardyStart
    push_cast
    ring_nf
  have hleft :
      blockMode n 2 =
        Complex.exp
          (Complex.I *
            (((hardyTheta (hardyStart (n + 2)) -
                hardyStart (n + 2) * Real.log ((n : ℝ) + 1)) : ℝ) : ℂ)) := by
    dsimp [blockMode]
    rw [hcoord, HardyCosSmooth.hardyCosExp_eq_cexp_phaseArg,
      HardyCosSmooth.hardyPhaseArg_eq_hardyTheta_sub_log]
  have hright :
      blockMode (n + 2) 0 =
        Complex.exp
          (Complex.I *
            (((hardyTheta (hardyStart (n + 2)) -
                hardyStart (n + 2) * Real.log (((n + 2 : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) := by
    dsimp [blockMode]
    rw [hcoord', HardyCosSmooth.hardyCosExp_eq_cexp_phaseArg,
      HardyCosSmooth.hardyPhaseArg_eq_hardyTheta_sub_log]
  have hsplit :
      (hardyTheta (hardyStart (n + 2)) -
          hardyStart (n + 2) * Real.log ((n : ℝ) + 1) : ℝ)
        = (hardyTheta (hardyStart (n + 2)) -
            hardyStart (n + 2) * Real.log (((n + 2 : ℕ) : ℝ) + 1) : ℝ)
            + hardyStart (n + 2) *
                (Real.log (((n + 2 : ℕ) : ℝ) + 1) - Real.log ((n : ℝ) + 1)) := by
    ring
  calc
    blockMode n 2
        = Complex.exp
            (Complex.I *
              (((hardyTheta (hardyStart (n + 2)) -
                  hardyStart (n + 2) * Real.log ((n : ℝ) + 1)) : ℝ) : ℂ)) := hleft
    _ = Complex.exp
          (Complex.I *
            (((hardyTheta (hardyStart (n + 2)) -
                hardyStart (n + 2) * Real.log (((n + 2 : ℕ) : ℝ) + 1)
                + hardyStart (n + 2) *
                    (Real.log (((n + 2 : ℕ) : ℝ) + 1) - Real.log ((n : ℝ) + 1)) : ℝ) : ℂ))) := by
          rw [hsplit]
    _ = Complex.exp
          (Complex.I *
            (((hardyTheta (hardyStart (n + 2)) -
                hardyStart (n + 2) * Real.log (((n + 2 : ℕ) : ℝ) + 1) : ℝ) : ℂ))) *
        Complex.exp
          (Complex.I *
            (((hardyStart (n + 2) *
                (Real.log (((n + 2 : ℕ) : ℝ) + 1) - Real.log ((n : ℝ) + 1)) : ℝ) : ℂ))) := by
          have hmul :
              Complex.I *
                  (((hardyTheta (hardyStart (n + 2)) -
                      hardyStart (n + 2) * Real.log (((n + 2 : ℕ) : ℝ) + 1)
                      + hardyStart (n + 2) *
                          (Real.log (((n + 2 : ℕ) : ℝ) + 1) - Real.log ((n : ℝ) + 1)) : ℝ) : ℂ))
                = Complex.I *
                    (((hardyTheta (hardyStart (n + 2)) -
                        hardyStart (n + 2) * Real.log (((n + 2 : ℕ) : ℝ) + 1) : ℝ) : ℂ))
                  + Complex.I *
                    (((hardyStart (n + 2) *
                        (Real.log (((n + 2 : ℕ) : ℝ) + 1) - Real.log ((n : ℝ) + 1)) : ℝ) : ℂ)) := by
            push_cast
            ring_nf
          rw [hmul, Complex.exp_add]
    _ = blockMode (n + 2) 0 *
          Complex.exp
            (Complex.I *
              (((hardyStart (n + 2) *
                  (Real.log (((n + 2 : ℕ) : ℝ) + 1) - Real.log ((n : ℝ) + 1)) : ℝ) : ℂ))) := by
          simpa [hright, mul_comm, mul_left_comm, mul_assoc]

lemma blockMode_norm (n : ℕ) (p : ℝ) : ‖blockMode n p‖ = 1 := by
  rw [blockMode, HardyCosSmooth.hardyCosExp_eq_cexp_phaseArg, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

lemma blockOmega_zero (n : ℕ) :
    blockOmega n 0
      = 4 * Real.pi * ((n : ℝ) + 1)
          * (thetaDeriv (hardyStart n) - Real.log ((n : ℝ) + 1)) := by
  simp [blockOmega, blockCoord_zero, blockJacobian]
  ring

theorem blockOmega_zero_bound :
    ∃ C > 0, ∀ n : ℕ, |blockOmega n 0| ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C0, hC0, htheta⟩ := theta_deriv_at_stationary_point
  refine ⟨4 * Real.pi * C0, mul_pos (by positivity) hC0, ?_⟩
  intro n
  have htheta' :
      |thetaDeriv (hardyStart n) - Real.log ((n : ℝ) + 1)|
        ≤ C0 / ((n : ℝ) + 1) ^ 2 := by
    simpa [hardyStart] using htheta n
  rw [blockOmega_zero]
  have hn1_pos : 0 < ((n : ℝ) + 1) := by positivity
  calc
    |4 * Real.pi * ((n : ℝ) + 1)
        * (thetaDeriv (hardyStart n) - Real.log ((n : ℝ) + 1))|
      = 4 * Real.pi * ((n : ℝ) + 1)
          * |thetaDeriv (hardyStart n) - Real.log ((n : ℝ) + 1)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ ≤ 4 * Real.pi * ((n : ℝ) + 1) * (C0 / ((n : ℝ) + 1) ^ 2) := by
          gcongr
    _ = (4 * Real.pi * C0) / ((n : ℝ) + 1) := by
          field_simp [ne_of_gt hn1_pos]

private lemma abs_log_one_add_sub_self_le_sq {u : ℝ} (hu : 0 ≤ u) :
    |Real.log (1 + u) - u| ≤ u ^ 2 := by
  have hu1_pos : 0 < 1 + u := by linarith
  have hlog_le : Real.log (1 + u) ≤ u := by
    linarith [Real.log_le_sub_one_of_pos hu1_pos]
  have hlog_ge : u / (1 + u) ≤ Real.log (1 + u) := by
    have hbase := Real.one_sub_inv_le_log_of_pos hu1_pos
    have hrew : 1 - (1 + u)⁻¹ = u / (1 + u) := by
      field_simp [show (1 + u) ≠ 0 by linarith]
      ring
    simpa [hrew] using hbase
  have hdiff_nonneg : 0 ≤ u - Real.log (1 + u) := by
    linarith
  have hdiff_le : u - Real.log (1 + u) ≤ u ^ 2 := by
    have hstep :
        u - Real.log (1 + u) ≤ u - u / (1 + u) := by
      linarith
    have hrew : u - u / (1 + u) = u ^ 2 / (1 + u) := by
      field_simp [show (1 + u) ≠ 0 by linarith]
      ring
    have hfrac : u ^ 2 / (1 + u) ≤ u ^ 2 := by
      have hu_sq_nonneg : 0 ≤ u ^ 2 := by positivity
      have hmul : u ^ 2 ≤ u ^ 2 * (1 + u) := by
        nlinarith [hu_sq_nonneg, hu]
      exact (div_le_iff₀ hu1_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    calc
      u - Real.log (1 + u) ≤ u - u / (1 + u) := hstep
      _ = u ^ 2 / (1 + u) := hrew
      _ ≤ u ^ 2 := hfrac
  have habs :
      |Real.log (1 + u) - u| = u - Real.log (1 + u) := by
    have hnonpos : Real.log (1 + u) - u ≤ 0 := by
      linarith
    rw [abs_of_nonpos hnonpos]
    ring
  rw [habs]
  exact hdiff_le

/-- The local `p ≤ 2` logarithmic remainder estimate used by the
`[0,2]` block-omega model. This is the only non-asymptotic arithmetic input
in the proof of `blockOmega_linear_model_upto_two_eventually`. -/
private lemma blockOmega_linear_model_upto_two_inner_bound
    {m p : ℝ} (hm_pos : 0 < m) (hm_ge_one : 1 ≤ m) (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    |(m + p) * (Real.log (1 + p / m) - p / m) + p ^ 2 / m| ≤ 16 / m := by
  have hu_nonneg : 0 ≤ p / m := by positivity
  have hu_bound :
      |Real.log (1 + p / m) - p / m| ≤ (p / m) ^ 2 :=
    abs_log_one_add_sub_self_le_sq hu_nonneg
  have hp_sq_div_nonneg : 0 ≤ p ^ 2 / m := by positivity
  have hp_div_nonneg : 0 ≤ p / m := by positivity
  have hp_div_le : p / m ≤ 2 / m := by
    exact div_le_div_of_nonneg_right hp2 (le_of_lt hm_pos)
  have hp_div_sq_le : (p / m) ^ 2 ≤ (2 / m) ^ 2 := by
    have hsq' : (p / m) ^ 2 ≤ (2 / m) ^ 2 := by
      nlinarith [hp_div_nonneg, hp_div_le]
    simpa [sq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsq'
  have hp_sq_le_four : p ^ 2 ≤ 4 := by
    nlinarith
  have hm_sq_pos : 0 < m ^ 2 := by positivity
  calc
    |(m + p) * (Real.log (1 + p / m) - p / m) + p ^ 2 / m|
        ≤ |(m + p) * (Real.log (1 + p / m) - p / m)| + |p ^ 2 / m| := by
              exact abs_add_le _ _
    _ = (m + p) * |Real.log (1 + p / m) - p / m| + p ^ 2 / m := by
          rw [abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hp_sq_div_nonneg]
    _ ≤ (m + p) * (p / m) ^ 2 + p ^ 2 / m := by
          gcongr
    _ ≤ (m + p) * (2 / m) ^ 2 + 4 / m := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left hp_div_sq_le (by linarith)
          · exact div_le_div_of_nonneg_right hp_sq_le_four (le_of_lt hm_pos)
    _ ≤ (m + 2) * (2 / m) ^ 2 + 4 / m := by
          gcongr
    _ = (8 * m + 8) / m ^ 2 := by
          have hm_ne : m ≠ 0 := ne_of_gt hm_pos
          field_simp [hm_ne]
          ring
    _ ≤ 16 / m := by
          refine (div_le_iff₀ (by positivity : 0 < m ^ 2)).2 ?_
          rw [div_eq_mul_inv]
          have hm_ne : m ≠ 0 := ne_of_gt hm_pos
          field_simp [hm_ne]
          nlinarith [hm_ge_one]

/-- The local `p ≤ 2` logarithmic remainder estimate used by the
`[0,2]` block-omega model. This is the only non-asymptotic arithmetic input
in the proof of `blockOmega_linear_model_upto_two_eventually`. -/
private lemma blockOmega_linear_model_upto_two_main_bound
    {m p : ℝ} (hm_pos : 0 < m) (hm_ge_one : 1 ≤ m) (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    |4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p|
      ≤ 64 * Real.pi / m := by
  have hsplit :
      4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p
        = 4 * Real.pi *
            ((m + p) * (Real.log (1 + p / m) - p / m) + p ^ 2 / m) := by
    have hm_ne : m ≠ 0 := ne_of_gt hm_pos
    field_simp [hm_ne]
    ring
  have hinner :=
    blockOmega_linear_model_upto_two_inner_bound hm_pos hm_ge_one hp0 hp2
  calc
    |4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p|
        = |4 * Real.pi *
            ((m + p) * (Real.log (1 + p / m) - p / m) + p ^ 2 / m)| := by
              rw [hsplit]
    _ = 4 * Real.pi *
          |(m + p) * (Real.log (1 + p / m) - p / m) + p ^ 2 / m| := by
            rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ 4 * Real.pi * (16 / m) := by
          gcongr
    _ = 64 * Real.pi / m := by ring

/-- On the first stationary block `p ∈ [0,1]`, the branch-free angular velocity
is the quadratic-model velocity `4πp` up to `O((n+1)⁻¹)`, uniformly for all
sufficiently large modes. This is the local linearization input for the
branch-free stationary-phase model. -/
theorem blockOmega_linear_model_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ p ∈ Icc (0 : ℝ) 1,
        |blockOmega n p - 4 * Real.pi * p| ≤ C / ((n : ℝ) + 1) := by
  have h_asymp := theta_deriv_asymptotic
  rw [Asymptotics.isBigO_iff] at h_asymp
  obtain ⟨C0, hC0⟩ := h_asymp
  rw [Filter.eventually_atTop] at hC0
  obtain ⟨T0, hT0⟩ := hC0
  obtain ⟨N0, hN0⟩ :
      ∃ N0 : ℕ, ∀ n ≥ N0, 2 * Real.pi * ((n : ℝ) + 1) ^ 2 ≥ T0 := by
    obtain ⟨M, hM⟩ := exists_nat_ge (max T0 0 / (2 * Real.pi))
    refine ⟨M, fun n hn => ?_⟩
    calc
      T0 ≤ max T0 0 := le_max_left _ _
      _ = 2 * Real.pi * (max T0 0 / (2 * Real.pi)) := by
            field_simp [Real.pi_ne_zero]
      _ ≤ 2 * Real.pi * (M : ℝ) := by
            exact mul_le_mul_of_nonneg_left hM (by positivity)
      _ ≤ 2 * Real.pi * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (by positivity)
      _ ≤ 2 * Real.pi * ((n : ℝ) + 1) ^ 2 := by
            gcongr
            nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.zero_le n]
  refine ⟨2 * |C0| + 12 * Real.pi, by positivity, N0, ?_⟩
  intro n hn p hp
  set m : ℝ := (n : ℝ) + 1
  set t : ℝ := blockCoord n p
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hm_ge_one : 1 ≤ m := by
    dsimp [m]
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.zero_le n]
  have hp0 : 0 ≤ p := hp.1
  have hp1 : p ≤ 1 := hp.2
  have hmp_pos : 0 < m + p := by
    linarith
  have ht_eq : t = 2 * Real.pi * (m + p) ^ 2 := by
    dsimp [t, m]
    unfold blockCoord
    ring
  have hJ_eq : blockJacobian n p = 4 * Real.pi * (m + p) := by
    dsimp [m]
    unfold blockJacobian
    ring
  have ht_ge_T0 : T0 ≤ t := by
    calc
      T0 ≤ 2 * Real.pi * m ^ 2 := hN0 n hn
      _ ≤ 2 * Real.pi * (m + p) ^ 2 := by
            gcongr
            nlinarith
      _ = t := ht_eq.symm
  have htheta :
      |thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))|
        ≤ |C0| / t := by
    have hraw := hT0 t ht_ge_T0
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hraw
    have ht_pos : 0 < t := by
      rw [ht_eq]
      positivity
    calc
      |thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))|
          ≤ C0 * |1 / t| := hraw
      _ ≤ |C0| * |1 / t| := by
            gcongr
            exact le_abs_self C0
      _ = |C0| / t := by
            rw [abs_of_pos (div_pos one_pos ht_pos), one_div, div_eq_mul_inv]
  have htheta_block :
      |blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))|
        ≤ 2 * |C0| / m := by
    have ht_pos : 0 < t := by
      rw [ht_eq]
      positivity
    have hratio :
        blockJacobian n p / t = 2 / (m + p) := by
      rw [hJ_eq, ht_eq]
      field_simp [Real.pi_ne_zero, ne_of_gt hmp_pos]
      ring
    have hJ_nonneg : 0 ≤ blockJacobian n p := by
      rw [hJ_eq]
      positivity
    calc
      |blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))|
          = blockJacobian n p *
              |thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))| := by
                rw [abs_mul, abs_of_nonneg hJ_nonneg]
      _ ≤ blockJacobian n p * (|C0| / t) := by
            gcongr
      _ = |C0| * (blockJacobian n p / t) := by
            rw [div_eq_mul_inv]
            ring
      _ = |C0| * (2 / (m + p)) := by rw [hratio]
      _ ≤ |C0| * (2 / m) := by
            have hrec : 1 / (m + p) ≤ 1 / m := by
              exact one_div_le_one_div_of_le hm_pos (by linarith)
            have hC_nonneg : 0 ≤ |C0| := abs_nonneg C0
            have htwo : 2 / (m + p) ≤ 2 / m := by
              have htwo' :=
                mul_le_mul_of_nonneg_left hrec (show 0 ≤ (2 : ℝ) by positivity)
              simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htwo'
            exact mul_le_mul_of_nonneg_left htwo hC_nonneg
      _ = 2 * |C0| / m := by ring
  have hmain_eq :
      blockJacobian n p *
          ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m)
        = 4 * Real.pi * (m + p) * Real.log (1 + p / m) := by
    have hdiv :
        t / (2 * Real.pi) = (m + p) ^ 2 := by
      rw [ht_eq]
      field_simp [Real.pi_ne_zero]
    have hm_ne : m ≠ 0 := ne_of_gt hm_pos
    calc
      blockJacobian n p * ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m)
          = 4 * Real.pi * (m + p) *
              ((1 / 2 : ℝ) * Real.log ((m + p) ^ 2) - Real.log m) := by
                rw [hJ_eq, hdiv]
      _ = 4 * Real.pi * (m + p) * (Real.log (m + p) - Real.log m) := by
            rw [Real.log_pow]
            ring
      _ = 4 * Real.pi * (m + p) * Real.log ((m + p) / m) := by
            rw [← Real.log_div (ne_of_gt hmp_pos) hm_ne]
      _ = 4 * Real.pi * (m + p) * Real.log (1 + p / m) := by
            congr 2
            field_simp [hm_ne]
  have hmain_bound :
      |4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p|
        ≤ 12 * Real.pi / m := by
    have hu_nonneg : 0 ≤ p / m := by positivity
    have hu_bound :
        |Real.log (1 + p / m) - p / m| ≤ (p / m) ^ 2 :=
      abs_log_one_add_sub_self_le_sq hu_nonneg
    have hsplit :
        4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p
          = 4 * Real.pi *
              ((m + p) * (Real.log (1 + p / m) - p / m) + p ^ 2 / m) := by
      have hm_ne : m ≠ 0 := ne_of_gt hm_pos
      field_simp [hm_ne]
      ring
    have hinner :
        |(m + p) * (Real.log (1 + p / m) - p / m) + p ^ 2 / m| ≤ 3 / m := by
      have hp_sq_div_nonneg : 0 ≤ p ^ 2 / m := by
        positivity
      have hp_div_nonneg : 0 ≤ p / m := by
        positivity
      have hp_div_le : p / m ≤ 1 / m := by
        exact div_le_div_of_nonneg_right hp1 (le_of_lt hm_pos)
      have hp_div_sq_le : (p / m) ^ 2 ≤ 1 / m ^ 2 := by
        have hsq' : (p / m) ^ 2 ≤ (1 / m) ^ 2 := by
          nlinarith [hp_div_nonneg, hp_div_le]
        simpa [sq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsq'
      have hp_sq_le_one : p ^ 2 ≤ 1 := by
        nlinarith
      calc
        |(m + p) * (Real.log (1 + p / m) - p / m) + p ^ 2 / m|
            ≤ |(m + p) * (Real.log (1 + p / m) - p / m)| + |p ^ 2 / m| := by
                  exact abs_add_le _ _
        _ = (m + p) * |Real.log (1 + p / m) - p / m| + p ^ 2 / m := by
              rw [abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hp_sq_div_nonneg]
        _ ≤ (m + p) * (p / m) ^ 2 + p ^ 2 / m := by
              gcongr
        _ ≤ (m + p) * (1 / m ^ 2) + 1 / m := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul_of_nonneg_left hp_div_sq_le (by linarith)
              · exact div_le_div_of_nonneg_right hp_sq_le_one (le_of_lt hm_pos)
        _ ≤ (m + 1) * (1 / m ^ 2) + 1 / m := by
              gcongr
        _ ≤ 3 / m := by
              have hm_sq_pos : 0 < m ^ 2 := by positivity
              calc
                (m + 1) * (1 / m ^ 2) + 1 / m = (2 * m + 1) / m ^ 2 := by
                    field_simp [ne_of_gt hm_pos]
                    ring
                _ ≤ 3 / m := by
                    refine (div_le_iff₀ hm_sq_pos).2 ?_
                    rw [div_eq_mul_inv]
                    have hm_ne : m ≠ 0 := ne_of_gt hm_pos
                    field_simp [hm_ne]
                    nlinarith [hm_ge_one]
    calc
      |4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p|
          = |4 * Real.pi *
              ((m + p) * (Real.log (1 + p / m) - p / m) + p ^ 2 / m)| := by
                rw [hsplit]
      _ = 4 * Real.pi *
            |(m + p) * (Real.log (1 + p / m) - p / m) + p ^ 2 / m| := by
              rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ 4 * Real.pi * (3 / m) := by
            gcongr
      _ = 12 * Real.pi / m := by ring
  have hrewrite :
      blockOmega n p - 4 * Real.pi * p
        = blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
          + (4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p) := by
    calc
      blockOmega n p - 4 * Real.pi * p
          = blockJacobian n p * (thetaDeriv t - Real.log m) - 4 * Real.pi * p := by
              simp [blockOmega, t, m, mul_comm, mul_left_comm, mul_assoc]
      _ = blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
          + blockJacobian n p *
              ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m)
          - 4 * Real.pi * p := by
              ring
      _ = blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
          + (4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p) := by
              rw [hmain_eq]
              ring
  calc
    |blockOmega n p - 4 * Real.pi * p|
        ≤ |blockJacobian n p *
              (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))|
            + |4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p| := by
              rw [hrewrite]
              exact abs_add_le _ _
    _ ≤ 2 * |C0| / m + 12 * Real.pi / m := by
          exact add_le_add htheta_block hmain_bound
    _ = (2 * |C0| + 12 * Real.pi) / m := by
          ring
    _ ≤ (2 * |C0| + 12 * Real.pi) / ((n : ℝ) + 1) := by
          simp [m]

/-- The same block-omega linear model remains valid up to the second stationary
start `p = 2`, with a larger but still uniform `O((n+1)⁻¹)` constant. This is
the exact `hOmega2` input needed by the second-start increment route. -/
theorem blockOmega_linear_model_upto_two_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ p ∈ Icc (0 : ℝ) 2,
        |blockOmega n p - 4 * Real.pi * p| ≤ C / ((n : ℝ) + 1) := by
  have h_asymp := theta_deriv_asymptotic
  rw [Asymptotics.isBigO_iff] at h_asymp
  obtain ⟨C0, hC0⟩ := h_asymp
  rw [Filter.eventually_atTop] at hC0
  obtain ⟨T0, hT0⟩ := hC0
  obtain ⟨N0, hN0⟩ :
      ∃ N0 : ℕ, ∀ n ≥ N0, 2 * Real.pi * ((n : ℝ) + 1) ^ 2 ≥ T0 := by
    obtain ⟨M, hM⟩ := exists_nat_ge (max T0 0 / (2 * Real.pi))
    refine ⟨M, fun n hn => ?_⟩
    calc
      T0 ≤ max T0 0 := le_max_left _ _
      _ = 2 * Real.pi * (max T0 0 / (2 * Real.pi)) := by
            field_simp [Real.pi_ne_zero]
      _ ≤ 2 * Real.pi * (M : ℝ) := by
            exact mul_le_mul_of_nonneg_left hM (by positivity)
      _ ≤ 2 * Real.pi * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (by positivity)
      _ ≤ 2 * Real.pi * ((n : ℝ) + 1) ^ 2 := by
            gcongr
            nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.zero_le n]
  refine ⟨2 * |C0| + 64 * Real.pi, by positivity, N0, ?_⟩
  intro n hn p hp
  set m : ℝ := (n : ℝ) + 1
  set t : ℝ := blockCoord n p
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hm_ge_one : 1 ≤ m := by
    dsimp [m]
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.zero_le n]
  have hp0 : 0 ≤ p := hp.1
  have hp2 : p ≤ 2 := hp.2
  have hmp_pos : 0 < m + p := by
    linarith
  have ht_eq : t = 2 * Real.pi * (m + p) ^ 2 := by
    dsimp [t, m]
    unfold blockCoord
    ring
  have hJ_eq : blockJacobian n p = 4 * Real.pi * (m + p) := by
    dsimp [m]
    unfold blockJacobian
    ring
  have ht_ge_T0 : T0 ≤ t := by
    calc
      T0 ≤ 2 * Real.pi * m ^ 2 := hN0 n hn
      _ ≤ 2 * Real.pi * (m + p) ^ 2 := by
            gcongr
            nlinarith
      _ = t := ht_eq.symm
  have htheta :
      |thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))|
        ≤ |C0| / t := by
    have hraw := hT0 t ht_ge_T0
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hraw
    have ht_pos : 0 < t := by
      rw [ht_eq]
      positivity
    calc
      |thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))|
          ≤ C0 * |1 / t| := hraw
      _ ≤ |C0| * |1 / t| := by
            gcongr
            exact le_abs_self C0
      _ = |C0| / t := by
            rw [abs_of_pos (div_pos one_pos ht_pos), one_div, div_eq_mul_inv]
  have htheta_block :
      |blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))|
        ≤ 2 * |C0| / m := by
    have ht_pos : 0 < t := by
      rw [ht_eq]
      positivity
    have hratio :
        blockJacobian n p / t = 2 / (m + p) := by
      rw [hJ_eq, ht_eq]
      field_simp [Real.pi_ne_zero, ne_of_gt hmp_pos]
      ring
    have hJ_nonneg : 0 ≤ blockJacobian n p := by
      rw [hJ_eq]
      positivity
    calc
      |blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))|
          = blockJacobian n p *
              |thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))| := by
                rw [abs_mul, abs_of_nonneg hJ_nonneg]
      _ ≤ blockJacobian n p * (|C0| / t) := by
            gcongr
      _ = |C0| * (blockJacobian n p / t) := by
            rw [div_eq_mul_inv]
            ring
      _ = |C0| * (2 / (m + p)) := by rw [hratio]
      _ ≤ |C0| * (2 / m) := by
            have hrec : 1 / (m + p) ≤ 1 / m := by
              exact one_div_le_one_div_of_le hm_pos (by linarith)
            have hC_nonneg : 0 ≤ |C0| := abs_nonneg C0
            have htwo : 2 / (m + p) ≤ 2 / m := by
              have htwo' :=
                mul_le_mul_of_nonneg_left hrec (show 0 ≤ (2 : ℝ) by positivity)
              simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htwo'
            exact mul_le_mul_of_nonneg_left htwo hC_nonneg
      _ = 2 * |C0| / m := by ring
  have hmain_eq :
      blockJacobian n p *
          ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m)
        = 4 * Real.pi * (m + p) * Real.log (1 + p / m) := by
    have hdiv :
        t / (2 * Real.pi) = (m + p) ^ 2 := by
      rw [ht_eq]
      field_simp [Real.pi_ne_zero]
    have hm_ne : m ≠ 0 := ne_of_gt hm_pos
    calc
      blockJacobian n p * ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m)
          = 4 * Real.pi * (m + p) *
              ((1 / 2 : ℝ) * Real.log ((m + p) ^ 2) - Real.log m) := by
                rw [hJ_eq, hdiv]
      _ = 4 * Real.pi * (m + p) * (Real.log (m + p) - Real.log m) := by
            rw [Real.log_pow]
            ring
      _ = 4 * Real.pi * (m + p) * Real.log ((m + p) / m) := by
            rw [← Real.log_div (ne_of_gt hmp_pos) hm_ne]
      _ = 4 * Real.pi * (m + p) * Real.log (1 + p / m) := by
            congr 2
            field_simp [hm_ne]
  have hmain_bound :
      |4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p|
        ≤ 64 * Real.pi / m := by
    exact blockOmega_linear_model_upto_two_main_bound hm_pos hm_ge_one hp0 hp2
  have hrewrite :
      blockOmega n p - 4 * Real.pi * p
        = blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
          + (4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p) := by
    calc
      blockOmega n p - 4 * Real.pi * p
          = blockJacobian n p * (thetaDeriv t - Real.log m) - 4 * Real.pi * p := by
              simp [blockOmega, t, m, mul_comm, mul_left_comm, mul_assoc]
      _ = blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
          + blockJacobian n p *
              ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m)
          - 4 * Real.pi * p := by
              ring
      _ = blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
          + (4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p) := by
              rw [hmain_eq]
              ring
  calc
    |blockOmega n p - 4 * Real.pi * p|
        ≤ |blockJacobian n p *
              (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))|
            + |4 * Real.pi * (m + p) * Real.log (1 + p / m) - 4 * Real.pi * p| := by
              rw [hrewrite]
              exact abs_add_le _ _
    _ ≤ 2 * |C0| / m + 64 * Real.pi / m := by
          exact add_le_add htheta_block hmain_bound
    _ = (2 * |C0| + 64 * Real.pi) / m := by
          ring
    _ ≤ (2 * |C0| + 64 * Real.pi) / ((n : ℝ) + 1) := by
          simp [m]

/-- On the tail `p ≥ 1`, the branch-free angular velocity stays uniformly
positive for all sufficiently large modes. This is the first genuinely
branch-free tail input for the resonant-mode stationary-phase route. -/
theorem blockOmega_tail_lower_eventually :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ p : ℝ, 1 ≤ p → 2 * Real.pi ≤ blockOmega n p := by
  have h_asymp := theta_deriv_asymptotic
  rw [Asymptotics.isBigO_iff] at h_asymp
  obtain ⟨C0, hC0⟩ := h_asymp
  rw [Filter.eventually_atTop] at hC0
  obtain ⟨T0, hT0⟩ := hC0
  obtain ⟨N1, hN1⟩ :
      ∃ N1 : ℕ, ∀ n ≥ N1, 2 * Real.pi * (((n : ℝ) + 1) + 1) ^ 2 ≥ T0 := by
    obtain ⟨M, hM⟩ := exists_nat_ge (max T0 0 / (2 * Real.pi))
    refine ⟨M, fun n hn => ?_⟩
    calc
      T0 ≤ max T0 0 := le_max_left _ _
      _ = 2 * Real.pi * (max T0 0 / (2 * Real.pi)) := by
            field_simp [Real.pi_ne_zero]
      _ ≤ 2 * Real.pi * (M : ℝ) := by
            exact mul_le_mul_of_nonneg_left hM (by positivity)
      _ ≤ 2 * Real.pi * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (by positivity)
      _ ≤ 2 * Real.pi * ((((n : ℝ) + 1) + 1) ^ 2) := by
            gcongr
            nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.zero_le n]
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, ∀ n ≥ N2, 2 * |C0| / ((n : ℝ) + 1) ≤ 2 * Real.pi := by
    obtain ⟨M, hM⟩ := exists_nat_ge (|C0| / Real.pi)
    refine ⟨M, fun n hn => ?_⟩
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hn1_pos : 0 < ((n : ℝ) + 1) := by positivity
    have hC_bound : |C0| ≤ Real.pi * ((n : ℝ) + 1) := by
      calc
        |C0| ≤ Real.pi * (M : ℝ) := by
          rw [show |C0| = Real.pi * (|C0| / Real.pi) by
            field_simp [Real.pi_ne_zero]]
          exact mul_le_mul_of_nonneg_left hM (le_of_lt hpi_pos)
        _ ≤ Real.pi * (n : ℝ) := by
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (le_of_lt hpi_pos)
        _ ≤ Real.pi * ((n : ℝ) + 1) := by
          nlinarith
    rw [div_le_iff₀ hn1_pos]
    nlinarith
  refine ⟨max N1 N2, ?_⟩
  intro n hn p hp
  set m : ℝ := (n : ℝ) + 1
  set t : ℝ := blockCoord n p
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hp_nonneg : 0 ≤ p := by linarith
  have hmp_pos : 0 < m + p := by linarith
  have ht_eq : t = 2 * Real.pi * (m + p) ^ 2 := by
    dsimp [t, m]
    unfold blockCoord
    ring
  have hJ_eq : blockJacobian n p = 4 * Real.pi * (m + p) := by
    dsimp [m]
    unfold blockJacobian
    ring
  have ht_ge_T0 : T0 ≤ t := by
    calc
      T0 ≤ 2 * Real.pi * (m + 1) ^ 2 := by
        simpa [m] using hN1 n (le_trans (le_max_left _ _) hn)
      _ ≤ 2 * Real.pi * (m + p) ^ 2 := by
            have hmp : m + 1 ≤ m + p := by linarith
            gcongr
      _ = t := ht_eq.symm
  have htheta :
      |thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))|
        ≤ |C0| / t := by
    have hraw := hT0 t ht_ge_T0
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hraw
    have ht_pos : 0 < t := by
      rw [ht_eq]
      positivity
    calc
      |thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))|
          ≤ C0 * |1 / t| := hraw
      _ ≤ |C0| * |1 / t| := by
            gcongr
            exact le_abs_self C0
      _ = |C0| / t := by
            rw [abs_of_pos (div_pos one_pos ht_pos), one_div, div_eq_mul_inv]
  have htheta_block :
      |blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))|
        ≤ 2 * |C0| / m := by
    have hratio :
        blockJacobian n p / t = 2 / (m + p) := by
      rw [hJ_eq, ht_eq]
      field_simp [Real.pi_ne_zero, ne_of_gt hmp_pos]
      ring
    have hJ_nonneg : 0 ≤ blockJacobian n p := by
      rw [hJ_eq]
      positivity
    calc
      |blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))|
          = blockJacobian n p *
              |thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))| := by
                rw [abs_mul, abs_of_nonneg hJ_nonneg]
      _ ≤ blockJacobian n p * (|C0| / t) := by
            gcongr
      _ = |C0| * (blockJacobian n p / t) := by
            rw [div_eq_mul_inv]
            ring
      _ = |C0| * (2 / (m + p)) := by rw [hratio]
      _ ≤ |C0| * (2 / m) := by
            have hrec : 1 / (m + p) ≤ 1 / m := by
              exact one_div_le_one_div_of_le hm_pos (by linarith)
            have htwo : 2 / (m + p) ≤ 2 / m := by
              have htwo' :=
                mul_le_mul_of_nonneg_left hrec (show 0 ≤ (2 : ℝ) by positivity)
              simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htwo'
            exact mul_le_mul_of_nonneg_left htwo (abs_nonneg C0)
      _ = 2 * |C0| / m := by ring
  have hmain :
      4 * Real.pi * p
        ≤ blockJacobian n p *
            ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m) := by
    have hdiv :
        t / (2 * Real.pi) = (m + p) ^ 2 := by
      rw [ht_eq]
      field_simp [Real.pi_ne_zero]
    have hm_ne : m ≠ 0 := ne_of_gt hm_pos
    have hu_pos : 0 < p / m := by
      positivity
    have hlog_lower : p / (m + p) ≤ Real.log (1 + p / m) := by
      have hbase := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + p / m by positivity)
      have hrew : 1 - (1 + p / m)⁻¹ = p / (m + p) := by
        field_simp [hm_ne]
        ring
      simpa [hrew] using hbase
    have hmain_eq :
        blockJacobian n p *
            ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m)
          = 4 * Real.pi * (m + p) * Real.log (1 + p / m) := by
      calc
        blockJacobian n p * ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m)
            = 4 * Real.pi * (m + p) *
                ((1 / 2 : ℝ) * Real.log ((m + p) ^ 2) - Real.log m) := by
                  rw [hJ_eq, hdiv]
        _ = 4 * Real.pi * (m + p) * (Real.log (m + p) - Real.log m) := by
              rw [Real.log_pow]
              ring
        _ = 4 * Real.pi * (m + p) * Real.log ((m + p) / m) := by
              rw [← Real.log_div (ne_of_gt hmp_pos) hm_ne]
        _ = 4 * Real.pi * (m + p) * Real.log (1 + p / m) := by
              congr 2
              field_simp [hm_ne]
    rw [hmain_eq]
    have hfactor_nonneg : 0 ≤ 4 * Real.pi * (m + p) := by positivity
    calc
      4 * Real.pi * p = (4 * Real.pi * (m + p)) * (p / (m + p)) := by
            field_simp [ne_of_gt hmp_pos]
      _ ≤ (4 * Real.pi * (m + p)) * Real.log (1 + p / m) := by
            exact mul_le_mul_of_nonneg_left hlog_lower hfactor_nonneg
  have hmain_asymp :
      4 * Real.pi * p - 2 * |C0| / m ≤ blockOmega n p := by
    have hrewrite :
        blockOmega n p
          = blockJacobian n p *
              (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
            + blockJacobian n p *
                ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m) := by
      calc
        blockOmega n p
            = blockJacobian n p * (thetaDeriv t - Real.log m) := by
                simp [blockOmega, t, m, mul_comm, mul_left_comm, mul_assoc]
        _ = blockJacobian n p *
              (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
            + blockJacobian n p *
                ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m) := by
                ring
    have hlower_err :
        -(2 * |C0| / m)
          ≤ blockJacobian n p *
              (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))) := by
      have habs := htheta_block
      linarith [abs_le.mp habs |>.1]
    rw [hrewrite]
    linarith
  have htail_err :
      2 * |C0| / m ≤ 2 * Real.pi := by
    simpa [m] using hN2 n (le_trans (le_max_right _ _) hn)
  have hp_ge : 2 * Real.pi ≤ 4 * Real.pi * p - 2 * |C0| / m := by
    nlinarith [hp, htail_err, Real.pi_pos]
  exact le_trans hp_ge hmain_asymp

/-- A strengthened tail lower bound: for `p ≥ 1`, the branch-free angular
velocity grows at least linearly in `p` for all sufficiently large modes. -/
theorem blockOmega_tail_linear_lower_eventually :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ p : ℝ, 1 ≤ p → 2 * Real.pi * p ≤ blockOmega n p := by
  have h_asymp := theta_deriv_asymptotic
  rw [Asymptotics.isBigO_iff] at h_asymp
  obtain ⟨C0, hC0⟩ := h_asymp
  rw [Filter.eventually_atTop] at hC0
  obtain ⟨T0, hT0⟩ := hC0
  obtain ⟨N1, hN1⟩ :
      ∃ N1 : ℕ, ∀ n ≥ N1, 2 * Real.pi * (((n : ℝ) + 1) + 1) ^ 2 ≥ T0 := by
    obtain ⟨M, hM⟩ := exists_nat_ge (max T0 0 / (2 * Real.pi))
    refine ⟨M, fun n hn => ?_⟩
    calc
      T0 ≤ max T0 0 := le_max_left _ _
      _ = 2 * Real.pi * (max T0 0 / (2 * Real.pi)) := by
            field_simp [Real.pi_ne_zero]
      _ ≤ 2 * Real.pi * (M : ℝ) := by
            exact mul_le_mul_of_nonneg_left hM (by positivity)
      _ ≤ 2 * Real.pi * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (by positivity)
      _ ≤ 2 * Real.pi * (((n : ℝ) + 1) + 1) ^ 2 := by
            gcongr
            nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.zero_le n]
  obtain ⟨N2, hN2⟩ :
      ∃ N2 : ℕ, ∀ n ≥ N2, 2 * |C0| / ((n : ℝ) + 1) ≤ 2 * Real.pi := by
    obtain ⟨M, hM⟩ := exists_nat_ge (|C0| / Real.pi)
    refine ⟨M, ?_⟩
    intro n hn
    have hm_pos : 0 < ((n : ℝ) + 1) := by positivity
    have hC_le : |C0| ≤ Real.pi * ((n : ℝ) + 1) := by
      calc
        |C0| ≤ Real.pi * (M : ℝ) := by
          rw [show |C0| = Real.pi * (|C0| / Real.pi) by
            field_simp [Real.pi_ne_zero]]
          exact mul_le_mul_of_nonneg_left hM (by positivity)
        _ ≤ Real.pi * ((n : ℝ) + 1) := by
          have hMn : (M : ℝ) ≤ (n : ℝ) + 1 := by
            have hMn' : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            linarith
          exact mul_le_mul_of_nonneg_left hMn (by positivity)
    rw [div_le_iff₀ hm_pos]
    nlinarith
  refine ⟨max N1 N2, ?_⟩
  intro n hn p hp
  set m : ℝ := (n : ℝ) + 1
  set t : ℝ := blockCoord n p
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hmp_pos : 0 < m + p := by
    linarith
  have ht_eq : t = 2 * Real.pi * (m + p) ^ 2 := by
    dsimp [t, m]
    unfold blockCoord
    ring
  have hJ_eq : blockJacobian n p = 4 * Real.pi * (m + p) := by
    dsimp [m]
    unfold blockJacobian
    ring
  have ht_ge_T0 : t ≥ T0 := by
    calc
      T0 ≤ 2 * Real.pi * (m + 1) ^ 2 := by
        simpa [m] using hN1 n (le_trans (le_max_left _ _) hn)
      _ ≤ 2 * Real.pi * (m + p) ^ 2 := by
            have hmp : m + 1 ≤ m + p := by linarith
            gcongr
      _ = t := ht_eq.symm
  have htheta_block :
      |thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))| ≤ |C0| / t := by
    have hbase := hT0 t ht_ge_T0
    have ht_pos : 0 < t := by
      rw [ht_eq]
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hbase
    calc
      |thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))|
          ≤ C0 * |1 / t| := hbase
      _ ≤ |C0| * |1 / t| := by
            gcongr
            exact le_abs_self C0
      _ = |C0| / t := by
            rw [abs_of_pos (div_pos one_pos ht_pos), one_div, div_eq_mul_inv]
  have htheta_term :
      |blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))|
        ≤ 2 * |C0| / m := by
    have hratio :
        blockJacobian n p / t = 2 / (m + p) := by
      rw [hJ_eq, ht_eq]
      field_simp [Real.pi_ne_zero, ne_of_gt hmp_pos]
      ring
    have hJ_nonneg : 0 ≤ blockJacobian n p := by
      rw [hJ_eq]
      positivity
    calc
      |blockJacobian n p *
            (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))|
          = blockJacobian n p *
              |thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))| := by
                rw [abs_mul, abs_of_nonneg hJ_nonneg]
      _ ≤ blockJacobian n p * (|C0| / t) := by
            gcongr
      _ = |C0| * (blockJacobian n p / t) := by
            rw [div_eq_mul_inv]
            ring
      _ = |C0| * (2 / (m + p)) := by rw [hratio]
      _ ≤ |C0| * (2 / m) := by
            have hrec : 1 / (m + p) ≤ 1 / m := by
              exact one_div_le_one_div_of_le hm_pos (by linarith)
            have htwo : 2 / (m + p) ≤ 2 / m := by
              have htwo' :=
                mul_le_mul_of_nonneg_left hrec (show 0 ≤ (2 : ℝ) by positivity)
              simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htwo'
            exact mul_le_mul_of_nonneg_left htwo (abs_nonneg C0)
      _ = 2 * |C0| / m := by ring
  have hmain :
      4 * Real.pi * p
        ≤ blockJacobian n p *
            ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m) := by
    have hdiv :
        t / (2 * Real.pi) = (m + p) ^ 2 := by
      rw [ht_eq]
      field_simp [Real.pi_ne_zero]
    have hm_ne : m ≠ 0 := ne_of_gt hm_pos
    have hlog_lower : p / (m + p) ≤ Real.log (1 + p / m) := by
      have hbase := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + p / m by positivity)
      have hrew : 1 - (1 + p / m)⁻¹ = p / (m + p) := by
        field_simp [hm_ne]
        ring
      simpa [hrew] using hbase
    have hmain_eq :
        blockJacobian n p *
            ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m)
          = 4 * Real.pi * (m + p) * Real.log (1 + p / m) := by
      calc
        blockJacobian n p * ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m)
            = 4 * Real.pi * (m + p) *
                ((1 / 2 : ℝ) * Real.log ((m + p) ^ 2) - Real.log m) := by
                  rw [hJ_eq, hdiv]
        _ = 4 * Real.pi * (m + p) * (Real.log (m + p) - Real.log m) := by
              rw [Real.log_pow]
              ring
        _ = 4 * Real.pi * (m + p) * Real.log ((m + p) / m) := by
              rw [← Real.log_div (ne_of_gt hmp_pos) hm_ne]
        _ = 4 * Real.pi * (m + p) * Real.log (1 + p / m) := by
              congr 2
              field_simp [hm_ne]
    rw [hmain_eq]
    have hfactor_nonneg : 0 ≤ 4 * Real.pi * (m + p) := by positivity
    calc
      4 * Real.pi * p = (4 * Real.pi * (m + p)) * (p / (m + p)) := by
            field_simp [ne_of_gt hmp_pos]
      _ ≤ (4 * Real.pi * (m + p)) * Real.log (1 + p / m) := by
            exact mul_le_mul_of_nonneg_left hlog_lower hfactor_nonneg
  have hmain_asymp :
      4 * Real.pi * p - 2 * |C0| / m ≤ blockOmega n p := by
    have hrewrite :
        blockOmega n p
          = blockJacobian n p *
              (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
            + blockJacobian n p *
                ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m) := by
      calc
        blockOmega n p
            = blockJacobian n p * (thetaDeriv t - Real.log m) := by
                simp [blockOmega, t, m, mul_comm, mul_left_comm, mul_assoc]
        _ = blockJacobian n p *
              (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
            + blockJacobian n p *
                ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log m) := by
                ring
    have hlower_err :
        -(2 * |C0| / m)
          ≤ blockJacobian n p *
              (thetaDeriv t - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))) := by
      have habs := htheta_term
      linarith [abs_le.mp habs |>.1]
    rw [hrewrite]
    linarith
  have hErr : 2 * |C0| / m ≤ 2 * Real.pi := by
    simpa [m] using hN2 n (le_trans (le_max_right _ _) hn)
  have hp_err : 2 * |C0| / m ≤ 2 * Real.pi * p := by
    nlinarith [hErr, hp, Real.pi_pos]
  calc
    2 * Real.pi * p ≤ 4 * Real.pi * p - 2 * |C0| / m := by
      nlinarith [hp_err, Real.pi_pos]
    _ ≤ blockOmega n p := hmain_asymp

private lemma blockOmega_hasDerivAt (n : ℕ) (p : ℝ) :
    HasDerivAt (blockOmega n)
      (deriv thetaDeriv (blockCoord n p) * (blockJacobian n p) ^ 2
        + (thetaDeriv (blockCoord n p) - Real.log ((n : ℝ) + 1))
            * (4 * Real.pi)) p := by
  have hbase :=
    (thetaDeriv_hasDerivAt (blockCoord n p)).scomp p (blockCoord_hasDerivAt n p)
  have hcomp :
      HasDerivAt (fun x : ℝ => thetaDeriv (blockCoord n x))
        (deriv thetaDeriv (blockCoord n p) * blockJacobian n p) p := by
    refine hbase.congr_deriv ?_
    rw [smul_eq_mul, (thetaDeriv_hasDerivAt (blockCoord n p)).deriv]
    ring
  have hsub :
      HasDerivAt
        (fun x : ℝ => thetaDeriv (blockCoord n x) - Real.log ((n : ℝ) + 1))
        (deriv thetaDeriv (blockCoord n p) * blockJacobian n p) p := by
    have hsub0 := hcomp.sub (hasDerivAt_const p (Real.log ((n : ℝ) + 1)))
    refine hsub0.congr_deriv ?_
    ring
  have hJ : HasDerivAt (blockJacobian n) (4 * Real.pi) p := by
    unfold blockJacobian
    simpa using
      (((hasDerivAt_id p).const_add ((n : ℝ) + 1)).const_mul (4 * Real.pi))
  have hmul0 :
      HasDerivAt
        (blockJacobian n * fun x : ℝ =>
          thetaDeriv (blockCoord n x) - Real.log ((n : ℝ) + 1))
        (4 * Real.pi * (thetaDeriv (blockCoord n p) - Real.log ((n : ℝ) + 1))
          + blockJacobian n p
              * (deriv thetaDeriv (blockCoord n p) * blockJacobian n p)) p :=
    hJ.mul hsub
  have hmul :
      HasDerivAt
        (blockJacobian n * fun x : ℝ =>
          thetaDeriv (blockCoord n x) - Real.log ((n : ℝ) + 1))
        (deriv thetaDeriv (blockCoord n p) * (blockJacobian n p) ^ 2
          + (thetaDeriv (blockCoord n p) - Real.log ((n : ℝ) + 1)) * (4 * Real.pi)) p := by
    refine hmul0.congr_deriv ?_
    ring
  have hmul' :
      HasDerivAt
        (fun x : ℝ =>
          (thetaDeriv (blockCoord n x) - Real.log ((n : ℝ) + 1)) * blockJacobian n x)
        (deriv thetaDeriv (blockCoord n p) * (blockJacobian n p) ^ 2
          + (thetaDeriv (blockCoord n p) - Real.log ((n : ℝ) + 1)) * (4 * Real.pi)) p := by
    refine hmul.congr_of_eventuallyEq <| Filter.Eventually.of_forall ?_
    intro x
    simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
  simpa [blockOmega] using hmul'

private lemma blockOmega_deriv_eq (n : ℕ) (p : ℝ) :
    deriv (blockOmega n) p
      = deriv thetaDeriv (blockCoord n p) * (blockJacobian n p) ^ 2
        + (thetaDeriv (blockCoord n p) - Real.log ((n : ℝ) + 1))
            * (4 * Real.pi) := by
  exact (blockOmega_hasDerivAt n p).deriv

private lemma blockOmega_differentiable (n : ℕ) : Differentiable ℝ (blockOmega n) := by
  intro p
  exact (blockOmega_hasDerivAt n p).differentiableAt

private lemma continuous_thetaDeriv : Continuous thetaDeriv := by
  exact continuous_iff_continuousAt.mpr fun t => (thetaDeriv_hasDerivAt t).continuousAt

private lemma blockOmega_continuous_deriv (n : ℕ) : Continuous (deriv (blockOmega n)) := by
  have h :
      deriv (blockOmega n)
        = fun p : ℝ =>
            deriv thetaDeriv (blockCoord n p) * (blockJacobian n p) ^ 2
              + (thetaDeriv (blockCoord n p) - Real.log ((n : ℝ) + 1))
                  * (4 * Real.pi) := by
    ext p
    exact blockOmega_deriv_eq n p
  rw [h]
  let h1 :
      Continuous fun p : ℝ =>
        deriv thetaDeriv (blockCoord n p) * (blockJacobian n p) ^ 2 :=
    (continuous_deriv_thetaDeriv.comp (blockCoord_continuous n)).mul
      ((blockJacobian_continuous n).pow 2)
  let h2 :
      Continuous fun p : ℝ =>
        (thetaDeriv (blockCoord n p) - Real.log ((n : ℝ) + 1)) * (4 * Real.pi) :=
    ((continuous_thetaDeriv.comp (blockCoord_continuous n)).sub continuous_const).mul
      continuous_const
  exact h1.add h2

private lemma blockOmega_deriv_nonneg_of_tail
    {n : ℕ} {p : ℝ}
    (hp : 1 ≤ p)
    (hgap : 0 ≤ thetaDeriv (blockCoord n p) - Real.log ((n : ℝ) + 1)) :
    0 ≤ deriv (blockOmega n) p := by
  rw [blockOmega_deriv_eq]
  have htd_nonneg :
      0 ≤ deriv thetaDeriv (blockCoord n p) := by
    have hcoord_pos : 0 < blockCoord n p := by
      unfold blockCoord
      positivity
    exact deriv_thetaDeriv_nonneg (blockCoord n p) hcoord_pos
  have hJ_sq_nonneg : 0 ≤ (blockJacobian n p) ^ 2 := by positivity
  have hmain_nonneg :
      0 ≤ (thetaDeriv (blockCoord n p) - Real.log ((n : ℝ) + 1)) * (4 * Real.pi) := by
    have hpi_nonneg : 0 ≤ 4 * Real.pi := by positivity
    exact mul_nonneg hgap hpi_nonneg
  nlinarith

theorem blockMode_hasDerivAt (n : ℕ) (p : ℝ) :
    HasDerivAt (blockMode n) (Complex.I * (blockOmega n p : ℂ) * blockMode n p) p := by
  have h :=
    HasDerivAt.scomp p
      (hardyCosExp_angular_velocity n (blockCoord n p))
      (blockCoord_hasDerivAt n p)
  simpa [blockMode, blockOmega, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h

private lemma blockMode_continuous (n : ℕ) : Continuous (blockMode n) := by
  simpa [blockMode] using
    (HardyCosSmooth.continuous_hardyCosExp_complex n).comp (blockCoord_continuous n)

/-- The block-parameter tail integral of the branch-free mode is uniformly
bounded for `p ≥ 1` and large mode number. This isolates the oscillatory tail
as a pure complex-VdC statement in the branch-free coordinates. -/
theorem blockMode_tail_param_integral_uniform_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ P : ℝ, 1 ≤ P →
        ‖∫ p in Ioc 1 P, blockMode n p‖ ≤ C := by
  obtain ⟨N0, hTail⟩ := blockOmega_tail_lower_eventually
  refine ⟨3 / (2 * Real.pi), by positivity, N0, ?_⟩
  intro n hn P hP
  by_cases hPle : P ≤ 1
  · have hEmpty : Ioc (1 : ℝ) P = ∅ := by
      exact Set.Ioc_eq_empty (not_lt_of_ge hPle)
    have hC_nonneg : 0 ≤ 3 / (2 * Real.pi) := by positivity
    simpa [hEmpty] using hC_nonneg
  · have h1P : 1 ≤ P := hP
    have hbound :=
      Aristotle.ComplexVdC.complex_vdc_angular
        (blockMode n) (blockOmega n) 1 P (2 * Real.pi)
        h1P (by positivity)
        (fun p hp => blockMode_hasDerivAt n p)
        (fun p hp => le_of_eq (blockMode_norm n p))
        (blockOmega_differentiable n)
        (blockOmega_continuous_deriv n)
        (fun p hpIcc => hTail n hn p hpIcc.1)
        (fun p hpIcc => by
          have hgap : 0 ≤ thetaDeriv (blockCoord n p) - Real.log ((n : ℝ) + 1) := by
            have hJ_pos : 0 < blockJacobian n p := by
              exact blockJacobian_pos n (le_trans (by norm_num) hpIcc.1)
            have hω_pos : 0 < blockOmega n p := by
              exact lt_of_lt_of_le (by positivity) (hTail n hn p hpIcc.1)
            have : 0 ≤ blockOmega n p / blockJacobian n p := by
              exact div_nonneg (le_of_lt hω_pos) (le_of_lt hJ_pos)
            simpa [blockOmega, div_eq_mul_inv, ne_of_gt hJ_pos] using this
          exact blockOmega_deriv_nonneg_of_tail hpIcc.1 hgap)
    simpa [← intervalIntegral.integral_of_le h1P] using hbound

/-- A decaying tail bound for the branch-free block primitive: once the tail
starts at parameter `P ≥ 1`, the oscillatory integral gains the expected
`1 / P` factor from the linear lower bound on the block angular velocity. -/
theorem blockMode_tail_param_integral_decay_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ P Q : ℝ, 1 ≤ P → P ≤ Q →
        ‖∫ p in Ioc P Q, blockMode n p‖ ≤ C / P := by
  obtain ⟨N0, hTail⟩ := blockOmega_tail_linear_lower_eventually
  refine ⟨3 / (2 * Real.pi), by positivity, N0, ?_⟩
  intro n hn P Q hP hPQ
  have hP_pos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hm_pos : 0 < 2 * Real.pi * P := by positivity
  have hbound :=
    Aristotle.ComplexVdC.complex_vdc_angular
      (blockMode n) (blockOmega n) P Q (2 * Real.pi * P)
      hPQ hm_pos
      (fun p hp => blockMode_hasDerivAt n p)
      (fun p hp => le_of_eq (blockMode_norm n p))
      (blockOmega_differentiable n)
      (blockOmega_continuous_deriv n)
      (fun p hpIcc => by
        have hP_le_p : P ≤ p := hpIcc.1
        have hp_ge_one : 1 ≤ p := le_trans hP hP_le_p
        have hmul : 2 * Real.pi * P ≤ 2 * Real.pi * p := by
          nlinarith [hP_le_p, Real.pi_pos]
        exact le_trans hmul (hTail n hn p hp_ge_one))
      (fun p hpIcc => by
        have hp_ge_one : 1 ≤ p := le_trans hP hpIcc.1
        have hgap : 0 ≤ thetaDeriv (blockCoord n p) - Real.log ((n : ℝ) + 1) := by
          have hJ_pos : 0 < blockJacobian n p := by
            exact blockJacobian_pos n (le_trans (by norm_num) hp_ge_one)
          have hω_pos : 0 < blockOmega n p := by
            exact lt_of_lt_of_le (by positivity) (hTail n hn p hp_ge_one)
          have : 0 ≤ blockOmega n p / blockJacobian n p := by
            exact div_nonneg (le_of_lt hω_pos) (le_of_lt hJ_pos)
          simpa [blockOmega, div_eq_mul_inv, ne_of_gt hJ_pos] using this
        exact blockOmega_deriv_nonneg_of_tail hp_ge_one hgap)
  calc
    ‖∫ p in Ioc P Q, blockMode n p‖
        = ‖∫ p in P..Q, blockMode n p‖ := by
            rw [← intervalIntegral.integral_of_le hPQ]
    _ ≤ 3 / (2 * Real.pi * P) := hbound
    _ = (3 / (2 * Real.pi)) / P := by
          field_simp [Real.pi_ne_zero, ne_of_gt hP_pos]

/-- Jacobian-weighted branch-free tail bound in block coordinates. The extra
`blockJacobian` factor costs one logarithm, but the new `1 / P` primitive decay
keeps the whole estimate controlled once the tail starts at parameter `P ≥ 1`. -/
theorem blockMode_jacobian_tail_integral_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ P Q : ℝ, 1 ≤ P → P ≤ Q →
        ‖∫ p in Ioc P Q, blockMode n p * blockJacobian n p‖
          ≤ C * (((n : ℝ) + 1) / P + (1 + Real.log (Q / P))) := by
  obtain ⟨C0, hC0, N0, hDecay⟩ := blockMode_tail_param_integral_decay_eventually
  refine ⟨4 * Real.pi * C0, by positivity, N0, ?_⟩
  intro n hn P Q hP hPQ
  have hP_pos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hQ_pos : 0 < Q := lt_of_lt_of_le hP_pos hPQ
  let f : ℝ → ℂ := blockMode n
  let v : ℝ → ℂ := fun x => -(∫ t in x..Q, f t)
  have hf_cont : Continuous f := by
    simpa [f] using blockMode_continuous n
  have hf_int : IntervalIntegrable f volume P Q := hf_cont.intervalIntegrable _ _
  have hxp_int : IntervalIntegrable (fun x : ℝ => x • f x) volume P Q := by
    exact (continuous_id.smul hf_cont).intervalIntegrable _ _
  have hv_deriv : ∀ x ∈ Set.uIcc P Q, HasDerivAt v (f x) x := by
    intro x hx
    have hIntx : IntervalIntegrable f volume x Q := hf_cont.intervalIntegrable _ _
    have hmeas : StronglyMeasurableAtFilter f (𝓝 x) volume :=
      hf_cont.stronglyMeasurableAtFilter volume (𝓝 x)
    have hcontx : ContinuousAt f x := hf_cont.continuousAt
    simpa [v, f] using (intervalIntegral.integral_hasDerivAt_left hIntx hmeas hcontx).neg
  have hv_cont : ContinuousOn v (Set.uIcc P Q) := by
    intro x hx
    exact (hv_deriv x hx).continuousAt.continuousWithinAt
  have hparts :
      ∫ x in P..Q, x • f x
        = Q • v Q - P • v P - ∫ x in P..Q, (1 : ℝ) • v x := by
    simpa [f] using
      (intervalIntegral.integral_smul_deriv_eq_deriv_smul
        (u := fun x : ℝ => x) (u' := fun _ : ℝ => (1 : ℝ))
        (v := v) (v' := f)
        (fun x hx => by simpa using hasDerivAt_id x)
        hv_deriv
        (by
          simpa using
            (continuous_const.intervalIntegrable P Q :
              IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume P Q))
        hf_int)
  have hprim :
      ‖∫ x in P..Q, f x‖ ≤ C0 / P := by
    simpa [f, ← intervalIntegral.integral_of_le hPQ] using hDecay n hn P Q hP hPQ
  have hvP_bound : ‖v P‖ ≤ C0 / P := by
    simpa [v] using hprim
  have hv_bound :
      ∀ x ∈ Icc P Q, ‖v x‖ ≤ C0 / x := by
    intro x hx
    have hx_one : 1 ≤ x := le_trans hP hx.1
    have hxQ : x ≤ Q := hx.2
    have hdecay_x :
        ‖∫ t in Ioc x Q, f t‖ ≤ C0 / x := by
      simpa [f] using hDecay n hn x Q hx_one hxQ
    simpa [v, ← intervalIntegral.integral_of_le hxQ] using hdecay_x
  have hv_int : IntervalIntegrable v volume P Q := hv_cont.intervalIntegrable
  have hInv_int : IntervalIntegrable (fun x : ℝ => C0 / x) volume P Q := by
    have hOneDiv_int : IntervalIntegrable (fun x : ℝ => 1 / x) volume P Q := by
      refine intervalIntegrable_one_div ?_ ?_
      · intro x hx
        have hxIcc : x ∈ Set.Icc P Q := by
          simpa [Set.uIcc_of_le hPQ] using hx
        exact ne_of_gt (lt_of_lt_of_le hP_pos hxIcc.1)
      · simpa [Set.uIcc_of_le hPQ] using
          (continuousOn_id : ContinuousOn (fun x : ℝ => x) (Set.Icc P Q))
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      hOneDiv_int.const_mul C0
  have hv_tail :
      ‖∫ x in P..Q, (1 : ℝ) • v x‖ ≤ C0 * Real.log (Q / P) := by
    calc
      ‖∫ x in P..Q, (1 : ℝ) • v x‖ = ‖∫ x in P..Q, v x‖ := by simp
      _ ≤ ∫ x in P..Q, ‖v x‖ := by
            simpa [Real.norm_eq_abs] using
              (intervalIntegral.norm_integral_le_integral_norm (f := v) hPQ)
      _ ≤ ∫ x in P..Q, C0 / x := by
            refine intervalIntegral.integral_mono_on hPQ hv_int.norm hInv_int ?_
            intro x hx
            exact hv_bound x hx
      _ = C0 * Real.log (Q / P) := by
            rw [show (fun x : ℝ => C0 / x) = fun x : ℝ => C0 * (1 / x) by
              funext x
              simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]]
            rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hP_pos hQ_pos]
  have hLinear :
      ∫ x in P..Q, f x * blockJacobian n x
        = (4 * Real.pi * ((n : ℝ) + 1)) • (∫ x in P..Q, f x)
          + (4 * Real.pi : ℝ) • (∫ x in P..Q, x • f x) := by
    have hInt1 :
        IntervalIntegrable
          (fun x : ℝ => (4 * Real.pi * ((n : ℝ) + 1) : ℝ) • f x) volume P Q := by
      exact hf_int.continuousOn_smul <|
        by
          simpa [Set.uIcc_of_le hPQ] using
            (continuousOn_const :
              ContinuousOn (fun _ : ℝ => (4 * Real.pi * ((n : ℝ) + 1) : ℝ)) (Set.Icc P Q))
    have hInt2 :
        IntervalIntegrable (fun x : ℝ => (4 * Real.pi : ℝ) • (x • f x)) volume P Q := by
      exact hxp_int.continuousOn_smul <|
        by
          simpa [Set.uIcc_of_le hPQ] using
            (continuousOn_const :
              ContinuousOn (fun _ : ℝ => (4 * Real.pi : ℝ)) (Set.Icc P Q))
    have hrepr :
        (fun x : ℝ => f x * blockJacobian n x)
          = fun x : ℝ =>
              (4 * Real.pi * ((n : ℝ) + 1)) • f x
                + (4 * Real.pi : ℝ) • (x • f x) := by
      funext x
      simp [f, blockJacobian_eq_affine, mul_add, add_mul,
        mul_comm, mul_left_comm, mul_assoc]
    calc
      ∫ x in P..Q, f x * blockJacobian n x
          = ∫ x in P..Q,
              (4 * Real.pi * ((n : ℝ) + 1)) • f x
                + (4 * Real.pi : ℝ) • (x • f x) := by
                  rw [hrepr]
      _ = (∫ x in P..Q, (4 * Real.pi * ((n : ℝ) + 1)) • f x)
            + ∫ x in P..Q, (4 * Real.pi : ℝ) • (x • f x) := by
              simpa using
                (intervalIntegral.integral_add hInt1 hInt2)
      _ = (4 * Real.pi * ((n : ℝ) + 1)) • (∫ x in P..Q, f x)
            + (4 * Real.pi : ℝ) • (∫ x in P..Q, x • f x) := by
              rw [intervalIntegral.integral_smul,
                intervalIntegral.integral_smul]
  have hI2 :
      ‖∫ x in P..Q, x • f x‖ ≤ C0 * (1 + Real.log (Q / P)) := by
    have hVQ : v Q = 0 := by simp [v]
    have hPV : ‖P • v P‖ ≤ C0 := by
      calc
        ‖P • v P‖ = |P| * ‖v P‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = P * ‖v P‖ := by rw [abs_of_pos hP_pos]
        _ ≤ P * (C0 / P) := by gcongr
        _ = C0 := by field_simp [ne_of_gt hP_pos]
    calc
      ‖∫ x in P..Q, x • f x‖
          = ‖Q • v Q - P • v P - ∫ x in P..Q, (1 : ℝ) • v x‖ := by
              rw [hparts]
      _ ≤ ‖Q • v Q - P • v P‖ + ‖∫ x in P..Q, (1 : ℝ) • v x‖ := by
            exact norm_sub_le _ _
      _ = ‖P • v P‖ + ‖∫ x in P..Q, (1 : ℝ) • v x‖ := by
            rw [hVQ]
            simp
      _ ≤ C0 + C0 * Real.log (Q / P) := by
            gcongr
      _ = C0 * (1 + Real.log (Q / P)) := by ring
  calc
    ‖∫ p in Ioc P Q, blockMode n p * blockJacobian n p‖
        = ‖∫ p in P..Q, blockMode n p * blockJacobian n p‖ := by
            rw [← intervalIntegral.integral_of_le hPQ]
    _ = ‖(4 * Real.pi * ((n : ℝ) + 1)) • (∫ x in P..Q, f x)
          + (4 * Real.pi : ℝ) • (∫ x in P..Q, x • f x)‖ := by
            rw [hLinear]
    _ ≤ ‖(4 * Real.pi * ((n : ℝ) + 1)) • (∫ x in P..Q, f x)‖
          + ‖(4 * Real.pi : ℝ) • (∫ x in P..Q, x • f x)‖ := norm_add_le _ _
    _ = |4 * Real.pi * ((n : ℝ) + 1)| * ‖∫ x in P..Q, f x‖
          + |4 * Real.pi| * ‖∫ x in P..Q, x • f x‖ := by
            rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs]
    _ = (4 * Real.pi * ((n : ℝ) + 1)) * ‖∫ x in P..Q, f x‖
          + (4 * Real.pi) * ‖∫ x in P..Q, x • f x‖ := by
            rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ ≤ (4 * Real.pi * ((n : ℝ) + 1)) * (C0 / P)
          + (4 * Real.pi) * (C0 * (1 + Real.log (Q / P))) := by
            gcongr
    _ = (4 * Real.pi * C0) * (((n : ℝ) + 1) / P + (1 + Real.log (Q / P))) := by
          ring

/-- The real quadratic phase `-2πp²` on the first stationary block. -/
private def quadraticPhase (p : ℝ) : ℝ :=
  -(2 * Real.pi * p ^ 2)

/-- The quadratic model factor `exp(-i·2πp²)` used to compensate the first
stationary block. -/
private def quadraticRotator (p : ℝ) : ℂ :=
  Complex.exp ((quadraticPhase p : ℂ) * Complex.I)

/-- The first-block mode after dividing out the quadratic-model oscillation. -/
private def blockModeQuadraticComp (n : ℕ) (p : ℝ) : ℂ :=
  blockMode n p * quadraticRotator p

private lemma quadraticRotator_zero : quadraticRotator 0 = 1 := by
  simp [quadraticRotator, quadraticPhase]

private lemma quadraticRotator_norm (p : ℝ) : ‖quadraticRotator p‖ = 1 := by
  simpa [quadraticRotator, quadraticPhase, mul_comm, mul_left_comm, mul_assoc] using
    Complex.norm_exp_ofReal_mul_I (quadraticPhase p)

private lemma quadraticPhase_hasDerivAt (p : ℝ) :
    HasDerivAt quadraticPhase (-(4 * Real.pi * p)) p := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * p) p := by
    simpa [pow_two] using ((hasDerivAt_id p).pow 2)
  have hmul : HasDerivAt (fun x : ℝ => 2 * Real.pi * x ^ 2)
      ((2 * Real.pi) * (2 * p)) p := by
    simpa [pow_two, mul_assoc] using (HasDerivAt.const_mul (2 * Real.pi) hpow)
  convert hmul.neg using 1 <;> ring

private lemma quadraticRotator_hasDerivAt (p : ℝ) :
    HasDerivAt quadraticRotator
      (quadraticRotator p * (-Complex.I * (((4 * Real.pi * p : ℝ)) : ℂ))) p := by
  have hphaseC :
      HasDerivAt (fun x : ℝ => (quadraticPhase x : ℂ))
        (((-(4 * Real.pi * p) : ℝ)) : ℂ) p := by
    exact HasDerivAt.ofReal_comp (quadraticPhase_hasDerivAt p)
  have harg :
      HasDerivAt (fun x : ℝ => (quadraticPhase x : ℂ) * Complex.I)
        ((((-(4 * Real.pi * p) : ℝ)) : ℂ) * Complex.I) p := by
    simpa [mul_assoc] using hphaseC.mul_const Complex.I
  change HasDerivAt (fun x : ℝ => Complex.exp ((quadraticPhase x : ℂ) * Complex.I))
    (quadraticRotator p * (-Complex.I * (((4 * Real.pi * p : ℝ)) : ℂ))) p
  simpa [quadraticRotator, quadraticPhase, mul_assoc, mul_left_comm, mul_comm] using harg.cexp

private lemma blockModeQuadraticComp_norm (n : ℕ) (p : ℝ) :
    ‖blockModeQuadraticComp n p‖ = 1 := by
  rw [blockModeQuadraticComp, norm_mul, blockMode_norm, quadraticRotator_norm, mul_one]

private lemma pack_coeff_sub (a b : ℝ) (F G : ℂ) :
    Complex.I * (a : ℂ) * F * G + F * (G * (-Complex.I * (b : ℂ)))
      = Complex.I * ((a - b : ℝ) : ℂ) * (F * G) := by
  calc
    Complex.I * (a : ℂ) * F * G + F * (G * (-Complex.I * (b : ℂ)))
        = F * (G * (Complex.I * (a : ℂ))) - F * (G * (Complex.I * (b : ℂ))) := by
            simp [sub_eq_add_neg, mul_left_comm, mul_comm]
    _ = F * (G * (Complex.I * (a : ℂ)) - G * (Complex.I * (b : ℂ))) := by
          rw [← mul_sub]
    _ = F * (G * (Complex.I * (((a - b : ℝ) : ℂ)))) := by
          congr 1
          calc
            G * (Complex.I * (a : ℂ)) - G * (Complex.I * (b : ℂ))
                = (G * Complex.I) * ((a : ℂ) - (b : ℂ)) := by
                    rw [mul_sub]
                    simp [mul_assoc]
            _ = G * (Complex.I * (((a - b : ℝ) : ℂ))) := by
                    simp [mul_assoc]
    _ = Complex.I * ((a - b : ℝ) : ℂ) * (F * G) := by
          simp [mul_assoc, mul_left_comm, mul_comm]

private theorem blockModeQuadraticComp_hasDerivAt (n : ℕ) (p : ℝ) :
    HasDerivAt (blockModeQuadraticComp n)
      (Complex.I * ((blockOmega n p - 4 * Real.pi * p : ℝ) : ℂ)
        * blockModeQuadraticComp n p) p := by
  have h := (blockMode_hasDerivAt n p).mul (quadraticRotator_hasDerivAt p)
  have hrewrite :
      Complex.I * ((blockOmega n p : ℂ)) * blockMode n p * quadraticRotator p
        + blockMode n p
            * (quadraticRotator p * (-Complex.I * (((4 * Real.pi * p : ℝ)) : ℂ)))
      = Complex.I * ((blockOmega n p - 4 * Real.pi * p : ℝ) : ℂ)
          * blockModeQuadraticComp n p := by
    rw [blockModeQuadraticComp]
    simpa using pack_coeff_sub (blockOmega n p) (4 * Real.pi * p)
      (blockMode n p) (quadraticRotator p)
  exact hrewrite ▸ h

/-- On the first stationary block, after removing the quadratic-model oscillation,
the mode is uniformly stable up to `O((n+1)⁻¹)`. -/
theorem blockMode_quadratic_comp_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ p ∈ Icc (0 : ℝ) 1,
        ‖blockModeQuadraticComp n p - blockMode n 0‖ ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, N0, hOmega⟩ := blockOmega_linear_model_eventually
  refine ⟨C, hC, N0, ?_⟩
  intro n hn p hp
  have hderiv :
      ∀ x ∈ Icc (0 : ℝ) p,
        HasDerivWithinAt (blockModeQuadraticComp n)
          (Complex.I * ((blockOmega n x - 4 * Real.pi * x : ℝ) : ℂ)
            * blockModeQuadraticComp n x)
          (Icc (0 : ℝ) p) x := by
    intro x hx
    exact (blockModeQuadraticComp_hasDerivAt n x).hasDerivWithinAt
  have hbound :
      ∀ x ∈ Ico (0 : ℝ) p,
        ‖Complex.I * ((blockOmega n x - 4 * Real.pi * x : ℝ) : ℂ)
            * blockModeQuadraticComp n x‖ ≤ C / ((n : ℝ) + 1) := by
    intro x hx
    have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, le_trans (le_of_lt hx.2) hp.2⟩
    have hω := hOmega n hn x hx01
    calc
      ‖Complex.I * ((blockOmega n x - 4 * Real.pi * x : ℝ) : ℂ)
          * blockModeQuadraticComp n x‖
          = ‖Complex.I‖ * ‖(((blockOmega n x - 4 * Real.pi * x : ℝ)) : ℂ)‖
              * ‖blockModeQuadraticComp n x‖ := by
                rw [norm_mul, norm_mul]
      _ = |blockOmega n x - 4 * Real.pi * x| := by
            rw [Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
              blockModeQuadraticComp_norm, mul_one]
      _ ≤ C / ((n : ℝ) + 1) := hω
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (f := blockModeQuadraticComp n) (a := 0) (b := p)
      hderiv hbound p ⟨hp.1, le_rfl⟩
  calc
    ‖blockModeQuadraticComp n p - blockMode n 0‖
        = ‖blockModeQuadraticComp n p - blockModeQuadraticComp n 0‖ := by
            simp [blockModeQuadraticComp, quadraticRotator_zero]
    _ ≤ (C / ((n : ℝ) + 1)) * (p - 0) := hmv
    _ ≤ C / ((n : ℝ) + 1) := by
          have hCn_nonneg : 0 ≤ C / ((n : ℝ) + 1) := by positivity
          nlinarith [hp.1, hp.2]

/-- Equivalent first-block model statement in the more natural form
`blockMode n p ≈ blockMode n 0 * exp(i·2πp²)`. -/
theorem blockMode_quadratic_model_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ p ∈ Icc (0 : ℝ) 1,
        ‖blockMode n p
            - blockMode n 0
                * Complex.exp (Complex.I * (((2 * Real.pi * p ^ 2 : ℝ)) : ℂ))‖
          ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, N0, hcomp⟩ := blockMode_quadratic_comp_eventually
  refine ⟨C, hC, N0, ?_⟩
  intro n hn p hp
  let e : ℂ := Complex.exp (Complex.I * (((2 * Real.pi * p ^ 2 : ℝ)) : ℂ))
  change ‖blockMode n p - blockMode n 0 * e‖ ≤ C / ((n : ℝ) + 1)
  have hexp_norm :
      ‖e‖ = 1 := by
    dsimp [e]
    exact Complex.norm_exp_I_mul_ofReal (2 * Real.pi * p ^ 2)
  have hrepr :
      blockMode n p
        - blockMode n 0 * e
      = (blockModeQuadraticComp n p - blockMode n 0) * e := by
    have hcancel :
        quadraticRotator p * e = 1 := by
      have hsum :
          ((quadraticPhase p : ℂ) * Complex.I) + Complex.I * (((2 * Real.pi * p ^ 2 : ℝ)) : ℂ) = 0 := by
        let a : ℝ := 2 * Real.pi * p ^ 2
        have hcomm : Complex.I * ((a : ℝ) : ℂ) = (((a : ℝ) : ℂ) * Complex.I) := by
          rw [mul_comm]
        have hzero : ((-(a : ℝ) : ℂ) + ((a : ℝ) : ℂ)) = 0 := by
          norm_num [a]
        calc
          ((quadraticPhase p : ℂ) * Complex.I) + Complex.I * (((2 * Real.pi * p ^ 2 : ℝ)) : ℂ)
              = ((-(a : ℝ) : ℂ) * Complex.I) + (((a : ℝ) : ℂ) * Complex.I) := by
                  rw [show (quadraticPhase p : ℂ) = ((-(a : ℝ) : ℂ) : ℂ) by
                    simp [quadraticPhase, a]]
                  rw [hcomm]
          _ = (((-(a : ℝ) : ℂ) + ((a : ℝ) : ℂ)) * Complex.I) := by
                rw [← add_mul]
          _ = 0 := by simp [hzero]
      calc
        quadraticRotator p * e
            = Complex.exp (((quadraticPhase p : ℂ) * Complex.I)
                + Complex.I * (((2 * Real.pi * p ^ 2 : ℝ)) : ℂ)) := by
                  simp [quadraticRotator, e, Complex.exp_add]
        _ = 1 := by rw [hsum, Complex.exp_zero]
    calc
      blockMode n p - blockMode n 0 * e
        = blockMode n p * 1
            - blockMode n 0 * e := by
              ring
      _ = blockMode n p
            * (quadraticRotator p * e) - blockMode n 0 * e := by
              rw [hcancel]
      _ = (blockMode n p * quadraticRotator p - blockMode n 0) * e := by
              ring
      _ = (blockModeQuadraticComp n p - blockMode n 0) * e := by
              rfl
  calc
    ‖blockMode n p
        - blockMode n 0 * e‖
        = ‖(blockModeQuadraticComp n p - blockMode n 0)
            * e‖ := by
              rw [hrepr]
    _ = ‖blockModeQuadraticComp n p - blockMode n 0‖ := by
          rw [norm_mul, hexp_norm, mul_one]
    _ ≤ C / ((n : ℝ) + 1) := hcomp n hn p hp

/-- Endpoint specialization of the first-block quadratic model at `p = 1`. -/
theorem blockMode_one_minus_zero_asymptotic :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ‖blockMode n 1 - blockMode n 0‖ ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, N0, hquad⟩ := blockMode_quadratic_model_eventually
  refine ⟨C, hC, N0, ?_⟩
  intro n hn
  have h := hquad n hn 1 (by simp)
  have hexp :
      Complex.exp (Complex.I * (((2 * Real.pi * (1 : ℝ) ^ 2 : ℝ)) : ℂ)) = 1 := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using Complex.exp_two_pi_mul_I
  calc
    ‖blockMode n 1 - blockMode n 0‖
        = ‖blockMode n 1
            - blockMode n 0
                * Complex.exp (Complex.I * (((2 * Real.pi * (1 : ℝ) ^ 2 : ℝ)) : ℂ))‖ := by
              rw [hexp, mul_one]
    _ ≤ C / ((n : ℝ) + 1) := h

/-- Endpoint anchor asymptotic at `p = 1`, extracted from the first-block model
and the stationary-point anchor at `p = 0`. -/
theorem blockMode_one_anchor_asymptotic :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ‖blockMode n 1
          - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
              Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)‖
        ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C1, hC1, N1, hOne⟩ := blockMode_one_minus_zero_asymptotic
  obtain ⟨C0, hC0, hZero⟩ := blockMode_zero_asymptotic
  refine ⟨C1 + C0, add_pos hC1 hC0, N1, ?_⟩
  intro n hn
  let a : ℂ :=
    ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
      Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)
  have hOne' := hOne n hn
  have hZero' : ‖blockMode n 0 - a‖ ≤ C0 / ((n : ℝ) + 1) := by
    simpa [a] using hZero n
  have hsplit :
      blockMode n 1 - a = (blockMode n 1 - blockMode n 0) + (blockMode n 0 - a) := by
    ring_nf
  have hn1_pos : 0 < ((n : ℝ) + 1) := by positivity
  calc
    ‖blockMode n 1 - a‖
        = ‖(blockMode n 1 - blockMode n 0) + (blockMode n 0 - a)‖ := by
            exact congrArg norm hsplit
    _ ≤ ‖blockMode n 1 - blockMode n 0‖ + ‖blockMode n 0 - a‖ := norm_add_le _ _
    _ ≤ C1 / ((n : ℝ) + 1) + C0 / ((n : ℝ) + 1) := by
          gcongr
    _ = (C1 + C0) / ((n : ℝ) + 1) := by
          field_simp [ne_of_gt hn1_pos]

/-- If the second stationary-block start differs from the first by `O((n+1)⁻¹)`,
then the second-start block mode inherits the same stationary anchor. This is
the direct bridge needed by the Atkinson shift-1 upper-prefix route. -/
theorem blockMode_two_minus_zero_asymptotic_of_blockMode_two_minus_one_asymptotic
    (hInc :
      ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ‖blockMode n 2 - blockMode n 1‖ ≤ C / ((n : ℝ) + 1)) :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ‖blockMode n 2 - blockMode n 0‖ ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C21, hC21, N21, h21⟩ := hInc
  obtain ⟨C10, hC10, N10, h10⟩ := blockMode_one_minus_zero_asymptotic
  refine ⟨C21 + C10, add_pos hC21 hC10, max N21 N10, ?_⟩
  intro n hn
  have hn21 : N21 ≤ n := le_trans (le_max_left _ _) hn
  have hn10 : N10 ≤ n := le_trans (le_max_right _ _) hn
  have h21' := h21 n hn21
  have h10' := h10 n hn10
  have hsplit :
      blockMode n 2 - blockMode n 0
        = (blockMode n 2 - blockMode n 1) + (blockMode n 1 - blockMode n 0) := by
    ring_nf
  have hn1_pos : 0 < ((n : ℝ) + 1) := by positivity
  calc
    ‖blockMode n 2 - blockMode n 0‖
        = ‖(blockMode n 2 - blockMode n 1) + (blockMode n 1 - blockMode n 0)‖ := by
            exact congrArg norm hsplit
    _ ≤ ‖blockMode n 2 - blockMode n 1‖ + ‖blockMode n 1 - blockMode n 0‖ := norm_add_le _ _
    _ ≤ C21 / ((n : ℝ) + 1) + C10 / ((n : ℝ) + 1) := by
          gcongr
    _ = (C21 + C10) / ((n : ℝ) + 1) := by
          field_simp [ne_of_gt hn1_pos]

/-- If the second-start mode is `O((n+1)⁻¹)` away from the stationary-point
mode, then it inherits the same stationary anchor. -/
theorem blockMode_two_anchor_asymptotic_of_blockMode_two_minus_zero_asymptotic
    (h20 :
      ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ‖blockMode n 2 - blockMode n 0‖ ≤ C / ((n : ℝ) + 1)) :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ‖blockMode n 2
          - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
              Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)‖
        ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C20, hC20, N20, h20'⟩ := h20
  obtain ⟨C0, hC0, hZero⟩ := blockMode_zero_asymptotic
  refine ⟨C20 + C0, add_pos hC20 hC0, N20, ?_⟩
  intro n hn
  let a : ℂ :=
    ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
      Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)
  have h20n := h20' n hn
  have hZero' : ‖blockMode n 0 - a‖ ≤ C0 / ((n : ℝ) + 1) := by
    simpa [a] using hZero n
  have hsplit :
      blockMode n 2 - a = (blockMode n 2 - blockMode n 0) + (blockMode n 0 - a) := by
    ring_nf
  have hn1_pos : 0 < ((n : ℝ) + 1) := by positivity
  calc
    ‖blockMode n 2 - a‖
        = ‖(blockMode n 2 - blockMode n 0) + (blockMode n 0 - a)‖ := by
            exact congrArg norm hsplit
    _ ≤ ‖blockMode n 2 - blockMode n 0‖ + ‖blockMode n 0 - a‖ := norm_add_le _ _
    _ ≤ C20 / ((n : ℝ) + 1) + C0 / ((n : ℝ) + 1) := by
          gcongr
    _ = (C20 + C0) / ((n : ℝ) + 1) := by
          field_simp [ne_of_gt hn1_pos]

/-- If the second stationary-block start differs from the first by `O((n+1)⁻¹)`,
then the second-start block mode inherits the same stationary anchor. This is
the direct bridge needed by the Atkinson shift-1 upper-prefix route. -/
theorem blockMode_two_anchor_asymptotic_of_blockMode_two_minus_one_asymptotic
    (hInc :
      ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ‖blockMode n 2 - blockMode n 1‖ ≤ C / ((n : ℝ) + 1)) :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ‖blockMode n 2
          - ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
              Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)‖
        ≤ C / ((n : ℝ) + 1) := by
  exact blockMode_two_anchor_asymptotic_of_blockMode_two_minus_zero_asymptotic
    (blockMode_two_minus_zero_asymptotic_of_blockMode_two_minus_one_asymptotic hInc)

/-- Conditional `[0,2]` extension of the compensated quadratic model. This is
the smallest local stationary-phase helper below the second-start increment
theorem: if the linear phase model is available uniformly up to `p = 2`, then
the same quadratic-model stabilization argument already used on `[0,1]`
propagates to `[0,2]`. -/
private theorem blockMode_quadratic_comp_upto_two_of_blockOmega_linear_model_eventually
    (hOmega2 :
      ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ∀ p ∈ Icc (0 : ℝ) 2,
          |blockOmega n p - 4 * Real.pi * p| ≤ C / ((n : ℝ) + 1)) :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ p ∈ Icc (0 : ℝ) 2,
        ‖blockModeQuadraticComp n p - blockMode n 0‖ ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C0, hC0, N0, hOmega⟩ := hOmega2
  refine ⟨2 * C0, by positivity, N0, ?_⟩
  intro n hn p hp
  have hderiv :
      ∀ x ∈ Icc (0 : ℝ) p,
        HasDerivWithinAt (blockModeQuadraticComp n)
          (Complex.I * ((blockOmega n x - 4 * Real.pi * x : ℝ) : ℂ)
            * blockModeQuadraticComp n x)
          (Icc (0 : ℝ) p) x := by
    intro x hx
    exact (blockModeQuadraticComp_hasDerivAt n x).hasDerivWithinAt
  have hbound :
      ∀ x ∈ Ico (0 : ℝ) p,
        ‖Complex.I * ((blockOmega n x - 4 * Real.pi * x : ℝ) : ℂ)
            * blockModeQuadraticComp n x‖ ≤ C0 / ((n : ℝ) + 1) := by
    intro x hx
    have hx02 : x ∈ Icc (0 : ℝ) 2 := ⟨hx.1, le_trans (le_of_lt hx.2) hp.2⟩
    have hω := hOmega n hn x hx02
    calc
      ‖Complex.I * ((blockOmega n x - 4 * Real.pi * x : ℝ) : ℂ)
          * blockModeQuadraticComp n x‖
          = ‖Complex.I‖ * ‖(((blockOmega n x - 4 * Real.pi * x : ℝ)) : ℂ)‖
              * ‖blockModeQuadraticComp n x‖ := by
                rw [norm_mul, norm_mul]
      _ = |blockOmega n x - 4 * Real.pi * x| := by
            rw [Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
              blockModeQuadraticComp_norm, mul_one]
      _ ≤ C0 / ((n : ℝ) + 1) := hω
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (f := blockModeQuadraticComp n) (a := 0) (b := p)
      hderiv hbound p ⟨hp.1, le_rfl⟩
  calc
    ‖blockModeQuadraticComp n p - blockMode n 0‖
        = ‖blockModeQuadraticComp n p - blockModeQuadraticComp n 0‖ := by
            simp [blockModeQuadraticComp, quadraticRotator_zero]
    _ ≤ (C0 / ((n : ℝ) + 1)) * (p - 0) := hmv
    _ ≤ (C0 / ((n : ℝ) + 1)) * 2 := by
          have hCn_nonneg : 0 ≤ C0 / ((n : ℝ) + 1) := by positivity
          nlinarith [hp.1, hp.2]
    _ = (2 * C0) / ((n : ℝ) + 1) := by
          ring

/-- Conditional `[0,2]` quadratic-model form corresponding to
`blockMode_quadratic_comp_upto_two_of_blockOmega_linear_model_eventually`. -/
private theorem blockMode_quadratic_model_upto_two_of_blockOmega_linear_model_eventually
    (hOmega2 :
      ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ∀ p ∈ Icc (0 : ℝ) 2,
          |blockOmega n p - 4 * Real.pi * p| ≤ C / ((n : ℝ) + 1)) :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ p ∈ Icc (0 : ℝ) 2,
        ‖blockMode n p
            - blockMode n 0
                * Complex.exp (Complex.I * (((2 * Real.pi * p ^ 2 : ℝ)) : ℂ))‖
          ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, N0, hcomp⟩ :=
    blockMode_quadratic_comp_upto_two_of_blockOmega_linear_model_eventually hOmega2
  refine ⟨C, hC, N0, ?_⟩
  intro n hn p hp
  let e : ℂ := Complex.exp (Complex.I * (((2 * Real.pi * p ^ 2 : ℝ)) : ℂ))
  change ‖blockMode n p - blockMode n 0 * e‖ ≤ C / ((n : ℝ) + 1)
  have hexp_norm :
      ‖e‖ = 1 := by
    dsimp [e]
    exact Complex.norm_exp_I_mul_ofReal (2 * Real.pi * p ^ 2)
  have hrepr :
      blockMode n p
        - blockMode n 0 * e
      = (blockModeQuadraticComp n p - blockMode n 0) * e := by
    have hcancel :
        quadraticRotator p * e = 1 := by
      have hsum :
          ((quadraticPhase p : ℂ) * Complex.I) + Complex.I * (((2 * Real.pi * p ^ 2 : ℝ)) : ℂ) = 0 := by
        let a : ℝ := 2 * Real.pi * p ^ 2
        have hcomm : Complex.I * ((a : ℝ) : ℂ) = (((a : ℝ) : ℂ) * Complex.I) := by
          rw [mul_comm]
        have hzero : ((-(a : ℝ) : ℂ) + ((a : ℝ) : ℂ)) = 0 := by
          norm_num [a]
        calc
          ((quadraticPhase p : ℂ) * Complex.I) + Complex.I * (((2 * Real.pi * p ^ 2 : ℝ)) : ℂ)
              = ((-(a : ℝ) : ℂ) * Complex.I) + (((a : ℝ) : ℂ) * Complex.I) := by
                  rw [show (quadraticPhase p : ℂ) = ((-(a : ℝ) : ℂ) : ℂ) by
                    simp [quadraticPhase, a]]
                  rw [hcomm]
          _ = (((-(a : ℝ) : ℂ) + ((a : ℝ) : ℂ)) * Complex.I) := by
                rw [← add_mul]
          _ = 0 := by simp [hzero]
      calc
        quadraticRotator p * e
            = Complex.exp (((quadraticPhase p : ℂ) * Complex.I)
                + Complex.I * (((2 * Real.pi * p ^ 2 : ℝ)) : ℂ)) := by
                  simp [quadraticRotator, e, Complex.exp_add]
        _ = 1 := by rw [hsum, Complex.exp_zero]
    calc
      blockMode n p - blockMode n 0 * e
        = blockMode n p * 1 - blockMode n 0 * e := by ring
      _ = blockMode n p * (quadraticRotator p * e) - blockMode n 0 * e := by
            rw [hcancel]
      _ = (blockMode n p * quadraticRotator p - blockMode n 0) * e := by
            ring
      _ = (blockModeQuadraticComp n p - blockMode n 0) * e := by
            rfl
  calc
    ‖blockMode n p - blockMode n 0 * e‖
        = ‖(blockModeQuadraticComp n p - blockMode n 0) * e‖ := by
            rw [hrepr]
    _ = ‖blockModeQuadraticComp n p - blockMode n 0‖ := by
          rw [norm_mul, hexp_norm, mul_one]
    _ ≤ C / ((n : ℝ) + 1) := hcomp n hn p hp

/-- Conditional endpoint control at the second stationary start. If the linear
block-omega model extends to `p = 2`, then the quadratic model yields the
second-start mode up to the stationary-point mode with `O((n+1)⁻¹)` error. -/
theorem blockMode_two_minus_zero_asymptotic_of_blockOmega_linear_model_upto_two_eventually
    (hOmega2 :
      ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ∀ p ∈ Icc (0 : ℝ) 2,
          |blockOmega n p - 4 * Real.pi * p| ≤ C / ((n : ℝ) + 1)) :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ‖blockMode n 2 - blockMode n 0‖ ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, N0, hquad⟩ :=
    blockMode_quadratic_model_upto_two_of_blockOmega_linear_model_eventually hOmega2
  refine ⟨C, hC, N0, ?_⟩
  intro n hn
  have h := hquad n hn 2 (by simp)
  have hexp :
      Complex.exp (Complex.I * (((2 * Real.pi * (2 : ℝ) ^ 2 : ℝ)) : ℂ)) = 1 := by
    have harg :
        Complex.I * (((2 * Real.pi * (2 : ℝ) ^ 2 : ℝ)) : ℂ)
          = (4 : ℕ) * (2 * Real.pi * Complex.I) := by
      norm_num [pow_two]
      ring
    rw [harg]
    exact Complex.exp_nat_mul_two_pi_mul_I 4
  calc
    ‖blockMode n 2 - blockMode n 0‖
        = ‖blockMode n 2
            - blockMode n 0
                * Complex.exp (Complex.I * (((2 * Real.pi * (2 : ℝ) ^ 2 : ℝ)) : ℂ))‖ := by
              rw [hexp, mul_one]
    _ ≤ C / ((n : ℝ) + 1) := h

/-- Conditional second-start increment theorem. This is the smallest build-clean
helper immediately below the missing external stationary-phase input for the
first Atkinson small-shift route. -/
theorem blockMode_two_minus_one_asymptotic_of_blockOmega_linear_model_upto_two_eventually
    (hOmega2 :
      ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ∀ p ∈ Icc (0 : ℝ) 2,
          |blockOmega n p - 4 * Real.pi * p| ≤ C / ((n : ℝ) + 1)) :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ‖blockMode n 2 - blockMode n 1‖ ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C20, hC20, N20, h20⟩ :=
    blockMode_two_minus_zero_asymptotic_of_blockOmega_linear_model_upto_two_eventually hOmega2
  obtain ⟨C10, hC10, N10, h10⟩ := blockMode_one_minus_zero_asymptotic
  refine ⟨C20 + C10, add_pos hC20 hC10, max N20 N10, ?_⟩
  intro n hn
  have hn20 : N20 ≤ n := le_trans (le_max_left _ _) hn
  have hn10 : N10 ≤ n := le_trans (le_max_right _ _) hn
  have h20' := h20 n hn20
  have h10' := h10 n hn10
  have hsplit :
      blockMode n 2 - blockMode n 1
        = (blockMode n 2 - blockMode n 0) + (blockMode n 0 - blockMode n 1) := by
    ring_nf
  have hrev :
      ‖blockMode n 0 - blockMode n 1‖ = ‖blockMode n 1 - blockMode n 0‖ := by
    rw [show blockMode n 0 - blockMode n 1 = -(blockMode n 1 - blockMode n 0) by ring]
    rw [norm_neg]
  have hn1_pos : 0 < ((n : ℝ) + 1) := by positivity
  calc
    ‖blockMode n 2 - blockMode n 1‖
        = ‖(blockMode n 2 - blockMode n 0) + (blockMode n 0 - blockMode n 1)‖ := by
            exact congrArg norm hsplit
    _ ≤ ‖blockMode n 2 - blockMode n 0‖ + ‖blockMode n 0 - blockMode n 1‖ := norm_add_le _ _
    _ = ‖blockMode n 2 - blockMode n 0‖ + ‖blockMode n 1 - blockMode n 0‖ := by
          rw [hrev]
    _ ≤ C20 / ((n : ℝ) + 1) + C10 / ((n : ℝ) + 1) := by
          gcongr
    _ = (C20 + C10) / ((n : ℝ) + 1) := by
          field_simp [ne_of_gt hn1_pos]

/-- The second stationary-block start differs from the first by
`O((n+1)⁻¹)`. This is the exact stationary-phase theorem consumed by the
first Atkinson small-shift upper-prefix route. -/
theorem blockMode_two_minus_one_asymptotic :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ‖blockMode n 2 - blockMode n 1‖ ≤ C / ((n : ℝ) + 1) := by
  exact
    blockMode_two_minus_one_asymptotic_of_blockOmega_linear_model_upto_two_eventually
      blockOmega_linear_model_upto_two_eventually

/-- The quadratic stationary-phase model kernel on the first block. -/
def quadraticKernel (p : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((2 * Real.pi * p ^ 2 : ℝ)) : ℂ))

/-- The zeroth quadratic-model moment on the initial segment `[0, P]` of the
first stationary block. -/
def firstBlockQuadraticMassUpTo (P : ℝ) : ℂ :=
  ∫ p in Ioc (0 : ℝ) P, quadraticKernel p

/-- The first quadratic-model moment on the initial segment `[0, P]` of the
first stationary block. -/
def firstBlockQuadraticMomentUpTo (P : ℝ) : ℂ :=
  ∫ p in Ioc (0 : ℝ) P, ((p : ℂ) * quadraticKernel p)

/-- Linear main coefficient contributed by the quadratic model on `[0, P]`. -/
def firstBlockQuadraticSlopeUpTo (P : ℝ) : ℂ :=
  (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMassUpTo P)

/-- Affine offset contributed by the quadratic model on `[0, P]`. -/
def firstBlockQuadraticOffsetUpTo (P : ℝ) : ℂ :=
  (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMomentUpTo P)

/-- The zeroth moment of the quadratic model on the first stationary block. -/
def firstBlockQuadraticMass : ℂ :=
  ∫ p in Ioc (0 : ℝ) 1, quadraticKernel p

/-- The first moment of the quadratic model on the first stationary block. -/
def firstBlockQuadraticMoment : ℂ :=
  ∫ p in Ioc (0 : ℝ) 1, ((p : ℂ) * quadraticKernel p)

/-- Linear main coefficient contributed by the quadratic model on the first
stationary block. -/
def firstBlockQuadraticSlope : ℂ :=
  (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMass)

/-- Affine offset contributed by the quadratic model on the first stationary
block. -/
def firstBlockQuadraticOffset : ℂ :=
  (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMoment)

private lemma quadraticKernel_continuous : Continuous quadraticKernel := by
  unfold quadraticKernel
  continuity

private lemma firstBlockQuadraticModelIntegral_upto_eq (n : ℕ) {P : ℝ}
    (hP0 : 0 ≤ P) :
    ∫ p in Ioc (0 : ℝ) P, blockMode n 0 * quadraticKernel p * blockJacobian n p
      = blockMode n 0 *
          ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMassUpTo P)
            + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMomentUpTo P)) := by
  have hIntMass : IntegrableOn quadraticKernel (Ioc (0 : ℝ) P) := by
    exact quadraticKernel_continuous.integrableOn_Ioc
  have hIntMoment :
      IntegrableOn (fun p : ℝ => ((p : ℂ) * quadraticKernel p)) (Ioc (0 : ℝ) P) := by
    exact (Complex.continuous_ofReal.mul quadraticKernel_continuous).integrableOn_Ioc
  calc
    ∫ p in Ioc (0 : ℝ) P, blockMode n 0 * quadraticKernel p * blockJacobian n p
        = blockMode n 0 * ∫ p in Ioc (0 : ℝ) P, quadraticKernel p * blockJacobian n p := by
            rw [← MeasureTheory.integral_const_mul]
            congr 1
            ext p
            ring
    _ = blockMode n 0 *
          (∫ p in Ioc (0 : ℝ) P,
              ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * quadraticKernel p)
                + (((4 * Real.pi : ℝ) : ℂ) * (((p : ℂ) * quadraticKernel p))))) := by
          congr 1
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with p hp
          rw [blockJacobian_eq_affine]
          have hcast :
              (((4 * Real.pi * ((n : ℝ) + 1) + 4 * Real.pi * p : ℝ) : ℂ))
                = (((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ)
                    + (((4 * Real.pi : ℝ) : ℂ) * (p : ℂ))) := by
            push_cast
            ring
          rw [hcast]
          ring
    _ = blockMode n 0 *
          ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMassUpTo P)
            + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMomentUpTo P)) := by
          rw [MeasureTheory.integral_add (hIntMass.const_mul _) (hIntMoment.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          simp [firstBlockQuadraticMassUpTo, firstBlockQuadraticMomentUpTo]

private lemma firstBlockQuadraticModelIntegral_eq (n : ℕ) :
    ∫ p in Ioc (0 : ℝ) 1, blockMode n 0 * quadraticKernel p * blockJacobian n p
      = blockMode n 0 *
          ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMass)
            + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMoment)) := by
  have hIntMass : IntegrableOn quadraticKernel (Ioc (0 : ℝ) 1) := by
    exact quadraticKernel_continuous.integrableOn_Ioc
  have hIntMoment : IntegrableOn (fun p : ℝ => ((p : ℂ) * quadraticKernel p)) (Ioc (0 : ℝ) 1) := by
    exact (Complex.continuous_ofReal.mul quadraticKernel_continuous).integrableOn_Ioc
  calc
    ∫ p in Ioc (0 : ℝ) 1, blockMode n 0 * quadraticKernel p * blockJacobian n p
        = blockMode n 0 * ∫ p in Ioc (0 : ℝ) 1, quadraticKernel p * blockJacobian n p := by
            rw [← MeasureTheory.integral_const_mul]
            congr 1
            ext p
            ring
    _ = blockMode n 0 *
          (∫ p in Ioc (0 : ℝ) 1,
              ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * quadraticKernel p)
                + (((4 * Real.pi : ℝ) : ℂ) * (((p : ℂ) * quadraticKernel p))))) := by
          congr 1
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with p hp
          rw [blockJacobian_eq_affine]
          have hcast :
              (((4 * Real.pi * ((n : ℝ) + 1) + 4 * Real.pi * p : ℝ) : ℂ))
                = (((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ)
                    + (((4 * Real.pi : ℝ) : ℂ) * (p : ℂ))) := by
            push_cast
            ring
          rw [hcast]
          ring
    _ = blockMode n 0 *
          ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMass)
            + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMoment)) := by
          rw [MeasureTheory.integral_add (hIntMass.const_mul _) (hIntMoment.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          simp [firstBlockQuadraticMass, firstBlockQuadraticMoment]

lemma firstBlockQuadraticCoeff_eq (n : ℕ) :
    ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMass)
      + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMoment))
      = (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlope)
          + firstBlockQuadraticOffset) := by
  simp [firstBlockQuadraticSlope, firstBlockQuadraticOffset]
  ring

private lemma firstBlockQuadraticCoeff_norm_le (n : ℕ) :
    ‖(((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlope) + firstBlockQuadraticOffset)‖
      ≤ (‖firstBlockQuadraticSlope‖ + ‖firstBlockQuadraticOffset‖) * ((n : ℝ) + 1) := by
  have hn1_ge_one : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    nlinarith
  have hn1_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
  calc
    ‖(((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlope) + firstBlockQuadraticOffset)‖
        ≤ ‖((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlope)‖ + ‖firstBlockQuadraticOffset‖ :=
          norm_add_le _ _
    _ = ((n : ℝ) + 1) * ‖firstBlockQuadraticSlope‖ + ‖firstBlockQuadraticOffset‖ := by
          rw [norm_mul]
          have hnorm : ‖((((n : ℝ) + 1 : ℝ) : ℂ))‖ = (n : ℝ) + 1 := by
            rw [Complex.norm_real, Real.norm_of_nonneg hn1_nonneg]
          rw [hnorm]
    _ ≤ ((n : ℝ) + 1) * ‖firstBlockQuadraticSlope‖
          + ((n : ℝ) + 1) * ‖firstBlockQuadraticOffset‖ := by
            have hOff_nonneg : 0 ≤ ‖firstBlockQuadraticOffset‖ := norm_nonneg _
            have hOff :
                ‖firstBlockQuadraticOffset‖
                  ≤ ((n : ℝ) + 1) * ‖firstBlockQuadraticOffset‖ := by
              nlinarith
            linarith
    _ = (‖firstBlockQuadraticSlope‖ + ‖firstBlockQuadraticOffset‖) * ((n : ℝ) + 1) := by
          ring

lemma firstBlockQuadraticCoeffUpTo_eq (n : ℕ) (P : ℝ) :
    ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMassUpTo P)
      + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMomentUpTo P))
      = (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
          + firstBlockQuadraticOffsetUpTo P) := by
  simp [firstBlockQuadraticSlopeUpTo, firstBlockQuadraticOffsetUpTo]
  ring

private lemma firstBlockQuadraticCoeffUpTo_norm_le (n : ℕ) (P : ℝ) :
    ‖(((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
        + firstBlockQuadraticOffsetUpTo P)‖
      ≤ (‖firstBlockQuadraticSlopeUpTo P‖ + ‖firstBlockQuadraticOffsetUpTo P‖) * ((n : ℝ) + 1) := by
  have hn1_ge_one : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    nlinarith
  have hn1_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
  calc
    ‖(((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
        + firstBlockQuadraticOffsetUpTo P)‖
        ≤ ‖((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)‖
            + ‖firstBlockQuadraticOffsetUpTo P‖ :=
          norm_add_le _ _
    _ = ((n : ℝ) + 1) * ‖firstBlockQuadraticSlopeUpTo P‖ + ‖firstBlockQuadraticOffsetUpTo P‖ := by
          rw [norm_mul]
          have hnorm : ‖((((n : ℝ) + 1 : ℝ) : ℂ))‖ = (n : ℝ) + 1 := by
            rw [Complex.norm_real, Real.norm_of_nonneg hn1_nonneg]
          rw [hnorm]
    _ ≤ ((n : ℝ) + 1) * ‖firstBlockQuadraticSlopeUpTo P‖
          + ((n : ℝ) + 1) * ‖firstBlockQuadraticOffsetUpTo P‖ := by
            have hOff :
                ‖firstBlockQuadraticOffsetUpTo P‖
                  ≤ ((n : ℝ) + 1) * ‖firstBlockQuadraticOffsetUpTo P‖ := by
              have hOff_nonneg : 0 ≤ ‖firstBlockQuadraticOffsetUpTo P‖ := norm_nonneg _
              nlinarith
            linarith
    _ = (‖firstBlockQuadraticSlopeUpTo P‖ + ‖firstBlockQuadraticOffsetUpTo P‖)
          * ((n : ℝ) + 1) := by
          ring

private lemma firstBlockQuadraticMassUpTo_norm_le {P : ℝ} (hP : P ∈ Icc (0 : ℝ) 1) :
    ‖firstBlockQuadraticMassUpTo P‖ ≤ 1 := by
  have hvol_finite : volume (Ioc (0 : ℝ) P) < ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hbound :
      ∀ p ∈ Ioc (0 : ℝ) P, ‖quadraticKernel p‖ ≤ (1 : ℝ) := by
    intro p hp
    have hnorm : ‖quadraticKernel p‖ = 1 := by
      unfold quadraticKernel
      exact Complex.norm_exp_I_mul_ofReal (2 * Real.pi * p ^ 2)
    simpa [hnorm]
  calc
    ‖firstBlockQuadraticMassUpTo P‖
        = ‖∫ p in Ioc (0 : ℝ) P, quadraticKernel p‖ := rfl
    _ ≤ volume.real (Ioc (0 : ℝ) P) := by
          simpa [one_mul] using norm_setIntegral_le_of_norm_le_const hvol_finite hbound
    _ = P := by
          rw [measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hP.1)]
          ring
    _ ≤ 1 := hP.2

private lemma firstBlockQuadraticMomentUpTo_norm_le {P : ℝ} (hP : P ∈ Icc (0 : ℝ) 1) :
    ‖firstBlockQuadraticMomentUpTo P‖ ≤ 1 := by
  have hvol_finite : volume (Ioc (0 : ℝ) P) < ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hbound :
      ∀ p ∈ Ioc (0 : ℝ) P, ‖(p : ℂ) * quadraticKernel p‖ ≤ (1 : ℝ) := by
    intro p hp
    have hp_nonneg : 0 ≤ p := le_of_lt hp.1
    have hp_le_one : p ≤ 1 := le_trans hp.2 hP.2
    calc
      ‖(p : ℂ) * quadraticKernel p‖ = ‖(p : ℂ)‖ * ‖quadraticKernel p‖ := by rw [norm_mul]
      _ = |p| * 1 := by
            have hnorm : ‖quadraticKernel p‖ = 1 := by
              unfold quadraticKernel
              exact Complex.norm_exp_I_mul_ofReal (2 * Real.pi * p ^ 2)
            simp [Complex.norm_real, hnorm]
      _ = p := by simp [abs_of_nonneg hp_nonneg]
      _ ≤ 1 := hp_le_one
  calc
    ‖firstBlockQuadraticMomentUpTo P‖
        = ‖∫ p in Ioc (0 : ℝ) P, ((p : ℂ) * quadraticKernel p)‖ := rfl
    _ ≤ volume.real (Ioc (0 : ℝ) P) := by
          simpa [one_mul] using norm_setIntegral_le_of_norm_le_const hvol_finite hbound
    _ = P := by
          rw [measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hP.1)]
          ring
    _ ≤ 1 := hP.2

private lemma blockCoord_image_uIcc_upto_subset (k : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    blockCoord k '' uIcc 0 P ⊆ Icc (hardyStart k) (blockCoord k P) := by
  intro t ht
  obtain ⟨p, hp, rfl⟩ := ht
  have hp' : p ∈ Icc 0 P := by
    simpa [uIcc_of_le hP] using hp
  have hmono := (blockCoord_strictMonoOn_nonneg k).monotoneOn
  refine ⟨?_, ?_⟩
  · simpa [blockCoord_zero] using
      hmono (by simp : (0 : ℝ) ∈ Ici 0) hp'.1 hp'.1
  · exact hmono hp'.1 (by simpa using hP) hp'.2

/-- Real change of variables from the height variable `t` to the block
parameter `p`, valid on every initial segment `[0, P]` with `P ≥ 0`. -/
theorem block_integral_cov_upto (k : ℕ) (P : ℝ) (hP : 0 ≤ P) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc (hardyStart k) (blockCoord k P))) :
    ∫ t in Ioc (hardyStart k) (blockCoord k P), g t
      = ∫ p in Ioc 0 P, g (blockCoord k p) * blockJacobian k p := by
  rw [← integral_of_le (show hardyStart k ≤ blockCoord k P by
      simpa [blockCoord_zero] using
        (blockCoord_strictMonoOn_nonneg k).monotoneOn
          (by simp : (0 : ℝ) ∈ Ici 0) (by simpa using hP) hP),
    ← integral_of_le hP, ← blockCoord_zero k]
  exact (integral_comp_mul_deriv'
    (a := 0) (b := P) (f := blockCoord k) (f' := blockJacobian k)
    (fun x _ => blockCoord_hasDerivAt k x)
    ((blockJacobian_continuous k).continuousOn)
    (hg.mono (blockCoord_image_uIcc_upto_subset k hP))).symm

/-- Complex change of variables from the height variable `t` to the block
parameter `p`, valid on every initial segment `[0, P]` with `P ≥ 0`. -/
theorem block_integral_cov_complex_upto (k : ℕ) (P : ℝ) (hP : 0 ≤ P) (g : ℝ → ℂ)
    (hg : ContinuousOn g (Icc (hardyStart k) (blockCoord k P))) :
    ∫ t in Ioc (hardyStart k) (blockCoord k P), g t
      = ∫ p in Ioc 0 P, g (blockCoord k p) * blockJacobian k p := by
  have hle : hardyStart k ≤ blockCoord k P := by
    simpa [blockCoord_zero] using
      (blockCoord_strictMonoOn_nonneg k).monotoneOn
        (by simp : (0 : ℝ) ∈ Ici 0) (by simpa using hP) hP
  have hInt_left : IntegrableOn g (Ioc (hardyStart k) (blockCoord k P)) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1
      (hg.intervalIntegrable_of_Icc hle)
  have hRhsCont :
      ContinuousOn (fun p : ℝ => g (blockCoord k p) * blockJacobian k p) (Icc 0 P) := by
    refine (hg.comp (blockCoord_continuous k).continuousOn ?_).mul
      ((Complex.continuous_ofReal.comp (blockJacobian_continuous k)).continuousOn)
    intro p hp
    exact blockCoord_image_uIcc_upto_subset k hP ⟨p, by simpa [uIcc_of_le hP] using hp, rfl⟩
  have hInt_right :
      IntegrableOn (fun p : ℝ => g (blockCoord k p) * blockJacobian k p) (Ioc 0 P) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hP).1
      (hRhsCont.intervalIntegrable_of_Icc hP)
  have hre_left :
      (∫ t in Ioc (hardyStart k) (blockCoord k P), g t).re
        = ∫ t in Ioc (hardyStart k) (blockCoord k P), (g t).re := by
    simpa using
      (integral_re (μ := volume.restrict (Ioc (hardyStart k) (blockCoord k P)))
        (f := g) hInt_left).symm
  have hre_right :
      (∫ p in Ioc 0 P, g (blockCoord k p) * blockJacobian k p).re
        = ∫ p in Ioc 0 P, (g (blockCoord k p) * blockJacobian k p).re := by
    simpa using
      (integral_re (μ := volume.restrict (Ioc 0 P))
        (f := fun p : ℝ => g (blockCoord k p) * blockJacobian k p) hInt_right).symm
  have him_left :
      (∫ t in Ioc (hardyStart k) (blockCoord k P), g t).im
        = ∫ t in Ioc (hardyStart k) (blockCoord k P), (g t).im := by
    simpa using
      (integral_im (μ := volume.restrict (Ioc (hardyStart k) (blockCoord k P)))
        (f := g) hInt_left).symm
  have him_right :
      (∫ p in Ioc 0 P, g (blockCoord k p) * blockJacobian k p).im
        = ∫ p in Ioc 0 P, (g (blockCoord k p) * blockJacobian k p).im := by
    simpa using
      (integral_im (μ := volume.restrict (Ioc 0 P))
        (f := fun p : ℝ => g (blockCoord k p) * blockJacobian k p) hInt_right).symm
  have hgre : ContinuousOn (fun t : ℝ => (g t).re) (Icc (hardyStart k) (blockCoord k P)) :=
    continuous_re.continuousOn.comp (t := Set.univ) hg (fun _ _ => by trivial)
  have hgim : ContinuousOn (fun t : ℝ => (g t).im) (Icc (hardyStart k) (blockCoord k P)) :=
    continuous_im.continuousOn.comp (t := Set.univ) hg (fun _ _ => by trivial)
  apply Complex.ext
  · rw [hre_left, hre_right]
    calc
      ∫ t in Ioc (hardyStart k) (blockCoord k P), (g t).re
        = ∫ p in Ioc 0 P, (g (blockCoord k p)).re * blockJacobian k p := by
            exact block_integral_cov_upto k P hP (fun t => (g t).re) hgre
      _ = ∫ p in Ioc 0 P, (g (blockCoord k p) * blockJacobian k p).re := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with p hp
            simp [mul_comm]
  · rw [him_left, him_right]
    calc
      ∫ t in Ioc (hardyStart k) (blockCoord k P), (g t).im
        = ∫ p in Ioc 0 P, (g (blockCoord k p)).im * blockJacobian k p := by
            exact block_integral_cov_upto k P hP (fun t => (g t).im) hgim
      _ = ∫ p in Ioc 0 P, (g (blockCoord k p) * blockJacobian k p).im := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with p hp
            simp [mul_comm]

/-- Exact branch-free reparametrization of the complex Hardy mode integral from
`hardyStart n` to `T` by the block parameter `p = sqrt(T/(2π)) - (n+1)`. -/
theorem hardyCosExp_integral_eq_blockParamIntegral (n : ℕ) {T : ℝ}
    (hT : hardyStart n ≤ T) :
    ∫ t in Ioc (hardyStart n) T, HardyCosSmooth.hardyCosExp n t
      = ∫ p in Ioc 0 (blockParam n T),
          HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p := by
  have hTnn : 0 ≤ T := le_trans (hardyStart_nonneg n) hT
  have hP : 0 ≤ blockParam n T := blockParam_nonneg n T hT
  have hcoord : blockCoord n (blockParam n T) = T := blockCoord_blockParam n T hTnn
  have hcont :
      ContinuousOn (HardyCosSmooth.hardyCosExp n)
        (Icc (hardyStart n) (blockCoord n (blockParam n T))) :=
    (HardyCosSmooth.continuous_hardyCosExp_complex n).continuousOn
  simpa [hcoord] using
    block_integral_cov_complex_upto n (blockParam n T) hP
      (fun t => HardyCosSmooth.hardyCosExp n t) hcont

/-- Exact branch-free reparametrization of the complex Hardy mode integral
between two block-parameter points `P ≤ Q`. -/
theorem hardyCosExp_integral_eq_blockParamIntegral_between (n : ℕ) {P Q : ℝ}
    (hP : 0 ≤ P) (hPQ : P ≤ Q) :
    ∫ t in Ioc (blockCoord n P) (blockCoord n Q), HardyCosSmooth.hardyCosExp n t
      = ∫ p in Ioc P Q, HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p := by
  have hcoordP :
      hardyStart n ≤ blockCoord n P := by
    simpa [blockCoord_zero] using
      (blockCoord_strictMonoOn_nonneg n).monotoneOn
        (by simp : (0 : ℝ) ∈ Ici 0) (by simpa using hP) hP
  have hcoordQ :
      hardyStart n ≤ blockCoord n Q := by
    have hQ : 0 ≤ Q := le_trans hP hPQ
    simpa [blockCoord_zero] using
      (blockCoord_strictMonoOn_nonneg n).monotoneOn
        (by simp : (0 : ℝ) ∈ Ici 0) (by simpa using hQ) hQ
  have hcoord_le :
      blockCoord n P ≤ blockCoord n Q := by
    exact (blockCoord_strictMonoOn_nonneg n).monotoneOn
      (by simpa using hP) (by simpa using le_trans hP hPQ) hPQ
  have hCovP := hardyCosExp_integral_eq_blockParamIntegral n hcoordP
  have hCovQ := hardyCosExp_integral_eq_blockParamIntegral n hcoordQ
  have hParamP : blockParam n (blockCoord n P) = P := by
    simpa using blockParam_blockCoord n P hP
  have hParamQ : blockParam n (blockCoord n Q) = Q := by
    simpa using blockParam_blockCoord n Q (le_trans hP hPQ)
  rw [hParamP] at hCovP
  rw [hParamQ] at hCovQ
  have hIntA :
      IntervalIntegrable (HardyCosSmooth.hardyCosExp n) volume (hardyStart n) (blockCoord n P) :=
    (HardyCosSmooth.continuous_hardyCosExp_complex n).intervalIntegrable _ _
  have hIntB :
      IntervalIntegrable (HardyCosSmooth.hardyCosExp n) volume (blockCoord n P) (blockCoord n Q) :=
    (HardyCosSmooth.continuous_hardyCosExp_complex n).intervalIntegrable _ _
  have hsplit_t :
      ∫ t in Ioc (hardyStart n) (blockCoord n Q), HardyCosSmooth.hardyCosExp n t
        = (∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t)
            + ∫ t in Ioc (blockCoord n P) (blockCoord n Q), HardyCosSmooth.hardyCosExp n t := by
    rw [← intervalIntegral.integral_of_le hcoordQ,
      ← intervalIntegral.integral_of_le hcoordP,
      ← intervalIntegral.integral_of_le hcoord_le]
    convert (intervalIntegral.integral_add_adjacent_intervals hIntA hIntB).symm using 1
  have hcontBlock :
      Continuous (fun p : ℝ =>
        HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p) := by
    exact ((HardyCosSmooth.continuous_hardyCosExp_complex n).comp (blockCoord_continuous n)).mul
      (Complex.continuous_ofReal.comp (blockJacobian_continuous n))
  have hIntP :
      IntervalIntegrable
        (fun p : ℝ => HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p)
        volume 0 P := hcontBlock.intervalIntegrable _ _
  have hIntQ :
      IntervalIntegrable
        (fun p : ℝ => HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p)
        volume P Q := hcontBlock.intervalIntegrable _ _
  have hsplit_p :
      ∫ p in Ioc (0 : ℝ) Q, HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p
        = (∫ p in Ioc (0 : ℝ) P, HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p)
            + ∫ p in Ioc P Q, HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p := by
    rw [← intervalIntegral.integral_of_le (le_trans hP hPQ),
      ← intervalIntegral.integral_of_le hP,
      ← intervalIntegral.integral_of_le hPQ]
    convert (intervalIntegral.integral_add_adjacent_intervals hIntP hIntQ).symm using 1
  calc
    ∫ t in Ioc (blockCoord n P) (blockCoord n Q), HardyCosSmooth.hardyCosExp n t
        = (∫ t in Ioc (hardyStart n) (blockCoord n Q), HardyCosSmooth.hardyCosExp n t)
            - ∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t := by
              apply eq_sub_iff_add_eq.mpr
              simpa [add_assoc, add_left_comm, add_comm] using hsplit_t.symm
    _ = (∫ p in Ioc (0 : ℝ) Q, HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p)
          - ∫ p in Ioc (0 : ℝ) P,
              HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p := by
            rw [hCovQ, hCovP]
    _ = ∫ p in Ioc P Q, HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p := by
          apply sub_eq_iff_eq_add.mpr
          simpa [add_assoc, add_left_comm, add_comm] using hsplit_p

/-- Jacobian-weighted branch-free tail bound transferred to the actual Hardy
mode integral in the `t` variable. -/
theorem hardyCosExp_tail_integral_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ P Q : ℝ, 1 ≤ P → P ≤ Q →
        ‖∫ t in Ioc (blockCoord n P) (blockCoord n Q), HardyCosSmooth.hardyCosExp n t‖
          ≤ C * (((n : ℝ) + 1) / P + (1 + Real.log (Q / P))) := by
  obtain ⟨C, hC, N0, hTail⟩ := blockMode_jacobian_tail_integral_bound_eventually
  refine ⟨C, hC, N0, ?_⟩
  intro n hn P Q hP hPQ
  rw [hardyCosExp_integral_eq_blockParamIntegral_between n (le_trans (by norm_num) hP) hPQ]
  simpa [blockMode] using hTail n hn P Q hP hPQ

lemma blockCoord_add_sub_eq (n k : ℕ) (p : ℝ) :
    blockCoord n (p + ((k : ℝ) - n)) = blockCoord k p := by
  unfold blockCoord
  ring

lemma blockJacobian_add_sub_eq (n k : ℕ) (p : ℝ) :
    blockJacobian n (p + ((k : ℝ) - n)) = blockJacobian k p := by
  unfold blockJacobian
  ring

lemma hardyStart_eq_blockCoord_shift (n k : ℕ) :
    hardyStart k = blockCoord n ((k : ℝ) - n) := by
  simpa [blockCoord_zero] using (blockCoord_add_sub_eq n k 0).symm

lemma hardyStart_succ_eq_blockCoord_shift (n k : ℕ) :
    hardyStart (k + 1) = blockCoord n (((k : ℝ) - n) + 1) := by
  simpa [blockCoord_one, add_assoc, add_comm, add_left_comm] using
    (blockCoord_add_sub_eq n k 1).symm

/-- Exact reparametrization of the `k`-th complete Hardy block for mode `n < k`
as the shifted block-parameter interval `p ∈ (k-n, k-n+1]`. -/
theorem hardyCosExp_completeBlock_eq_shifted_blockParamIntegral (n k : ℕ)
    (hnk : n < k) :
    ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), HardyCosSmooth.hardyCosExp n t
      = ∫ p in Ioc ((k : ℝ) - (n : ℝ)) (((k : ℝ) - (n : ℝ)) + 1),
          HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p := by
  have hP : 0 ≤ (k : ℝ) - (n : ℝ) := by
    have hkn : (n : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.le_of_lt hnk
    nlinarith
  have hPQ : (k : ℝ) - (n : ℝ) ≤ ((k : ℝ) - (n : ℝ)) + 1 := by linarith
  convert hardyCosExp_integral_eq_blockParamIntegral_between n hP hPQ using 1
  · rw [← hardyStart_eq_blockCoord_shift n k, ← hardyStart_succ_eq_blockCoord_shift n k]

/-- Re-express the contribution of the shifted mode `k-j` on the `k`-th complete
Hardy block over the common block parameter interval `u ∈ (0, 1]`. This is the
exact `j = k - n` reduction used for collective near-diagonal analysis. -/
theorem hardyCosExp_completeBlock_eq_common_blockParamIntegral (k j : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
        HardyCosSmooth.hardyCosExp (k - j) t
      = ∫ u in Ioc (0 : ℝ) 1,
          HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) * blockJacobian k u := by
  let n : ℕ := k - j
  have hnk : n < k := by
    dsimp [n]
    omega
  have hcast : ((k : ℝ) - (n : ℝ)) = (j : ℝ) := by
    dsimp [n]
    rw [Nat.cast_sub hjk]
    ring
  have hshifted :=
    hardyCosExp_completeBlock_eq_shifted_blockParamIntegral n k hnk
  have hshifted' :
      ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          HardyCosSmooth.hardyCosExp n t
        = ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
            HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p := by
    simpa [hcast, n, add_comm, add_left_comm, add_assoc] using hshifted
  let f : ℝ → ℂ := fun p =>
    HardyCosSmooth.hardyCosExp n (blockCoord n p) * blockJacobian n p
  have hcomp :
      ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1), f p
        = ∫ u in Ioc (0 : ℝ) 1, f (u + j) := by
    calc
      ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1), f p
          = ∫ p in (j : ℝ)..((j : ℝ) + 1), f p := by
              rw [← intervalIntegral.integral_of_le (by linarith : (j : ℝ) ≤ (j : ℝ) + 1)]
      _ = ∫ u in (0 : ℝ)..1, f (u + j) := by
            symm
            simpa [add_assoc, add_comm, add_left_comm] using
              (intervalIntegral.integral_comp_add_right (f := f) (a := (0 : ℝ)) (b := 1)
                (d := (j : ℝ)))
      _ = ∫ u in Ioc (0 : ℝ) 1, f (u + j) := by
            rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hf :
      ∀ u : ℝ,
        f (u + j)
          = HardyCosSmooth.hardyCosExp n (blockCoord k u) * blockJacobian k u := by
    intro u
    dsimp [f]
    rw [show u + (j : ℝ) = u + ((k : ℝ) - (n : ℝ)) by rw [hcast]]
    rw [blockCoord_add_sub_eq n k u, blockJacobian_add_sub_eq n k u]
  calc
    ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
        HardyCosSmooth.hardyCosExp (k - j) t
      = ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1), f p := by
          simpa [n] using hshifted'
    _ = ∫ u in Ioc (0 : ℝ) 1, f (u + j) := hcomp
    _ = ∫ u in Ioc (0 : ℝ) 1,
          HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) * blockJacobian k u := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
            simpa [n] using hf u

/-- Real-part form of `hardyCosExp_completeBlock_eq_common_blockParamIntegral`. -/
theorem hardyCos_completeBlock_eq_common_blockParamIntegral (k j : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos (k - j) t
      = ∫ u in Ioc (0 : ℝ) 1,
          hardyCos (k - j) (blockCoord k u) * blockJacobian k u := by
  let n : ℕ := k - j
  have hExp := hardyCosExp_completeBlock_eq_common_blockParamIntegral k j hj hjk
  have hleft_le : hardyStart k ≤ hardyStart (k + 1) := hardyStart_le_succ' k
  have hIntLeft :
      IntegrableOn (fun t : ℝ => HardyCosSmooth.hardyCosExp n t)
        (Ioc (hardyStart k) (hardyStart (k + 1))) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hleft_le]
    exact (HardyCosSmooth.continuous_hardyCosExp_complex n).intervalIntegrable _ _
  have hIntRight :
      IntegrableOn
        (fun u : ℝ => HardyCosSmooth.hardyCosExp n (blockCoord k u) * blockJacobian k u)
        (Ioc (0 : ℝ) 1) := by
    have hcont :
        Continuous fun u : ℝ =>
          HardyCosSmooth.hardyCosExp n (blockCoord k u) * blockJacobian k u := by
      exact ((HardyCosSmooth.continuous_hardyCosExp_complex n).comp (blockCoord_continuous k)).mul
        (Complex.continuous_ofReal.comp (blockJacobian_continuous k))
    simpa using hcont.integrableOn_Ioc
  have hLeftRe :
      ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos n t
        = (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp n t).re := by
    calc
      ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos n t
          = ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
              (HardyCosSmooth.hardyCosExp n t).re := by
                refine MeasureTheory.integral_congr_ae ?_
                filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
                exact HardyCosSmooth.hardyCos_eq_re_hardyCosExp n t
      _ = (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp n t).re := by
              simpa using integral_re hIntLeft
  have hRightRe :
      ∫ u in Ioc (0 : ℝ) 1, hardyCos n (blockCoord k u) * blockJacobian k u
        = (∫ u in Ioc (0 : ℝ) 1,
            HardyCosSmooth.hardyCosExp n (blockCoord k u) * blockJacobian k u).re := by
    calc
      ∫ u in Ioc (0 : ℝ) 1, hardyCos n (blockCoord k u) * blockJacobian k u
          = ∫ u in Ioc (0 : ℝ) 1,
              (HardyCosSmooth.hardyCosExp n (blockCoord k u) * blockJacobian k u).re := by
                refine MeasureTheory.integral_congr_ae ?_
                filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
                have hcos := HardyCosSmooth.hardyCos_eq_re_hardyCosExp n (blockCoord k u)
                rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hcos]
                ring
      _ = (∫ u in Ioc (0 : ℝ) 1,
            HardyCosSmooth.hardyCosExp n (blockCoord k u) * blockJacobian k u).re := by
              simpa using integral_re hIntRight
  calc
    ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos (k - j) t
        = (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp n t).re := by
              simpa [n] using hLeftRe
    _ = (∫ u in Ioc (0 : ℝ) 1,
            HardyCosSmooth.hardyCosExp n (blockCoord k u) * blockJacobian k u).re := by
          rw [hExp]
    _ = ∫ u in Ioc (0 : ℝ) 1, hardyCos (k - j) (blockCoord k u) * blockJacobian k u := by
          simpa [n] using hRightRe.symm

/-- Branch-free shifted-tail bound for the contribution of mode `n < k` on the
complete `k`-th Hardy block, expressed in the natural shift variable `k-n`. -/
theorem hardyCosExp_completeBlock_shifted_tail_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ k n : ℕ, n < k → N0 ≤ n →
      ‖∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), HardyCosSmooth.hardyCosExp n t‖
        ≤ C * (((n : ℝ) + 1) / ((k : ℝ) - (n : ℝ))
            + (1 + Real.log ((((k : ℝ) - (n : ℝ)) + 1) / ((k : ℝ) - (n : ℝ))))) := by
  obtain ⟨C, hC, N0, hTail⟩ := hardyCosExp_tail_integral_bound_eventually
  refine ⟨C, hC, N0, ?_⟩
  intro k n hnk hn
  have hP : 1 ≤ (k : ℝ) - (n : ℝ) := by
    have hkn : ((n : ℝ) + 1) ≤ (k : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hnk
    nlinarith
  have hPQ : (k : ℝ) - (n : ℝ) ≤ ((k : ℝ) - (n : ℝ)) + 1 := by linarith
  convert hTail n hn ((k : ℝ) - (n : ℝ)) (((k : ℝ) - (n : ℝ)) + 1) hP hPQ using 1
  · rw [← hardyStart_eq_blockCoord_shift n k, ← hardyStart_succ_eq_blockCoord_shift n k]

/-- Real-part form of `hardyCosExp_completeBlock_shifted_tail_bound_eventually`. -/
theorem hardyCos_completeBlock_shifted_tail_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ k n : ℕ, n < k → N0 ≤ n →
      |∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos n t|
        ≤ C * (((n : ℝ) + 1) / ((k : ℝ) - (n : ℝ))
            + (1 + Real.log ((((k : ℝ) - (n : ℝ)) + 1) / ((k : ℝ) - (n : ℝ))))) := by
  obtain ⟨C, hC, N0, hTail⟩ := hardyCosExp_completeBlock_shifted_tail_bound_eventually
  refine ⟨C, hC, N0, ?_⟩
  intro k n hnk hn
  have hle : hardyStart k ≤ hardyStart (k + 1) := by
    exact hardyStart_le_succ' k
  have hInt :
      IntegrableOn (fun t : ℝ => HardyCosSmooth.hardyCosExp n t)
        (Ioc (hardyStart k) (hardyStart (k + 1))) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    exact (HardyCosSmooth.continuous_hardyCosExp_complex n).intervalIntegrable _ _
  have hIntCos :
      ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos n t
        = (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp n t).re := by
    calc
      ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos n t
          = ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
              (HardyCosSmooth.hardyCosExp n t).re := by
                refine MeasureTheory.integral_congr_ae ?_
                filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
                exact HardyCosSmooth.hardyCos_eq_re_hardyCosExp n t
      _ = (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp n t).re := by
              simpa using integral_re hInt
  calc
    |∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos n t|
        = |(∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp n t).re| := by
              rw [hIntCos]
    _ ≤ ‖∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp n t‖ := Complex.abs_re_le_norm _
    _ ≤ C * (((n : ℝ) + 1) / ((k : ℝ) - (n : ℝ))
            + (1 + Real.log ((((k : ℝ) - (n : ℝ)) + 1) / ((k : ℝ) - (n : ℝ))))) := by
          exact hTail k n hnk hn

/-- Prefix-block version of `hardyCosExp_firstBlock_linear_model_eventually`:
the branch-free Hardy mode on `[hardyStart n, blockCoord n P]` is uniformly
close to the quadratic model for every `P ∈ [0,1]`. -/
theorem hardyCosExp_firstBlock_linear_model_upto_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ P ∈ Icc (0 : ℝ) 1,
        ‖(∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t)
            - blockMode n 0 *
                ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMassUpTo P)
                  + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMomentUpTo P))‖
          ≤ C := by
  obtain ⟨C0, hC0, N0, hquad⟩ := blockMode_quadratic_model_eventually
  refine ⟨8 * Real.pi * C0, by positivity, N0, ?_⟩
  intro n hn P hP
  have hT :
      hardyStart n ≤ blockCoord n P := by
    simpa [blockCoord_zero] using
      (blockCoord_strictMonoOn_nonneg n).monotoneOn
        (by simp : (0 : ℝ) ∈ Ici 0) (by simpa using hP.1) hP.1
  have hCov := hardyCosExp_integral_eq_blockParamIntegral n hT
  have hParam : blockParam n (blockCoord n P) = P := by
    simpa using blockParam_blockCoord n P hP.1
  rw [hParam] at hCov
  have hCov' :
      ∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t
        = ∫ p in Ioc (0 : ℝ) P, blockMode n p * blockJacobian n p := by
    simpa [blockMode] using hCov
  have hModelEq := firstBlockQuadraticModelIntegral_upto_eq n hP.1
  have hIntActual :
      IntegrableOn (fun p : ℝ => blockMode n p * blockJacobian n p) (Ioc (0 : ℝ) P) := by
    have hcont :
        Continuous (fun p : ℝ => blockMode n p * blockJacobian n p) := by
      exact ((HardyCosSmooth.continuous_hardyCosExp_complex n).comp (blockCoord_continuous n)).mul
        (Complex.continuous_ofReal.comp (blockJacobian_continuous n))
    simpa [blockMode] using hcont.integrableOn_Ioc
  have hIntModel :
      IntegrableOn (fun p : ℝ => blockMode n 0 * quadraticKernel p * blockJacobian n p)
        (Ioc (0 : ℝ) P) := by
    have hcont :
        Continuous (fun p : ℝ => blockMode n 0 * quadraticKernel p * blockJacobian n p) := by
      exact ((continuous_const.mul quadraticKernel_continuous).mul
        (Complex.continuous_ofReal.comp (blockJacobian_continuous n)))
    simpa using hcont.integrableOn_Ioc
  have hrepr :
      (∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t)
        - blockMode n 0 *
            ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMassUpTo P)
              + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMomentUpTo P))
      = ∫ p in Ioc (0 : ℝ) P,
          (blockMode n p - blockMode n 0 * quadraticKernel p) * blockJacobian n p := by
    rw [hCov', ← hModelEq, ← MeasureTheory.integral_sub hIntActual hIntModel]
    congr 1
    ext p
    ring
  have hvol_finite : volume (Ioc (0 : ℝ) P) < ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hbound :
      ∀ p ∈ Ioc (0 : ℝ) P,
        ‖(blockMode n p - blockMode n 0 * quadraticKernel p) * blockJacobian n p‖
          ≤ 8 * Real.pi * C0 := by
    intro p hp
    have hpIcc : p ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hp.1, le_trans hp.2 hP.2⟩
    have hdiff :
        ‖blockMode n p - blockMode n 0 * quadraticKernel p‖ ≤ C0 / ((n : ℝ) + 1) := by
      simpa [quadraticKernel] using hquad n hn p hpIcc
    have hJ_nonneg : 0 ≤ blockJacobian n p := by
      rw [blockJacobian_eq_affine]
      have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      nlinarith [le_of_lt Real.pi_pos, hp.1]
    have hJ_bound : blockJacobian n p ≤ 8 * Real.pi * ((n : ℝ) + 1) := by
      rw [blockJacobian_eq_affine]
      have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      have hp_le_one : p ≤ 1 := le_trans hp.2 hP.2
      nlinarith [hp_le_one, Real.pi_pos]
    calc
      ‖(blockMode n p - blockMode n 0 * quadraticKernel p) * blockJacobian n p‖
          = ‖blockMode n p - blockMode n 0 * quadraticKernel p‖
              * ‖(((blockJacobian n p : ℝ) : ℂ))‖ := by
                rw [norm_mul]
      _ = ‖blockMode n p - blockMode n 0 * quadraticKernel p‖ * |blockJacobian n p| := by
            simpa using congrArg
              (fun x : ℝ => ‖blockMode n p - blockMode n 0 * quadraticKernel p‖ * x)
              (Complex.norm_real (blockJacobian n p))
      _ = ‖blockMode n p - blockMode n 0 * quadraticKernel p‖ * blockJacobian n p := by
            rw [abs_of_nonneg hJ_nonneg]
      _ ≤ (C0 / ((n : ℝ) + 1)) * (8 * Real.pi * ((n : ℝ) + 1)) := by
            gcongr
      _ = 8 * Real.pi * C0 := by
            have hn1_pos : 0 < ((n : ℝ) + 1) := by positivity
            field_simp [ne_of_gt hn1_pos]
  calc
    ‖(∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t)
        - blockMode n 0 *
            ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMassUpTo P)
              + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMomentUpTo P))‖
        = ‖∫ p in Ioc (0 : ℝ) P,
            (blockMode n p - blockMode n 0 * quadraticKernel p) * blockJacobian n p‖ := by
              rw [hrepr]
    _ ≤ 8 * Real.pi * C0 * volume.real (Ioc (0 : ℝ) P) := by
          exact norm_setIntegral_le_of_norm_le_const hvol_finite hbound
    _ = 8 * Real.pi * C0 * P := by
          rw [measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hP.1)]
          ring
    _ ≤ 8 * Real.pi * C0 := by
          have hC_nonneg : 0 ≤ 8 * Real.pi * C0 := by positivity
          exact mul_le_of_le_one_right hC_nonneg hP.2

/-- Prefix-block version of `hardyCosExp_firstBlock_anchor_main_term_eventually`. -/
theorem hardyCosExp_firstBlock_anchor_main_term_upto_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ P ∈ Icc (0 : ℝ) 1,
        ‖(∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t)
            - (((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                  Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
                (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
                  + firstBlockQuadraticOffsetUpTo P))‖
          ≤ C := by
  obtain ⟨C1, hC1, N0, hLinear⟩ := hardyCosExp_firstBlock_linear_model_upto_eventually
  obtain ⟨C2, hC2, hStart⟩ := blockMode_zero_asymptotic
  let K : ℝ := 8 * Real.pi + 1
  refine ⟨C1 + C2 * K, add_pos hC1 (mul_pos hC2 (by positivity)), N0, ?_⟩
  intro n hn P hP
  let a : ℂ :=
    ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
      Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)
  let L : ℂ :=
    (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
      + firstBlockQuadraticOffsetUpTo P)
  have hCoeffEq :
      ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMassUpTo P)
        + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMomentUpTo P)) = L := by
    simpa [L] using firstBlockQuadraticCoeffUpTo_eq n P
  have hLinear' :
      ‖(∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t)
          - blockMode n 0 * L‖ ≤ C1 := by
    have htmp := hLinear n hn P hP
    rwa [hCoeffEq] at htmp
  have hSlope :
      ‖firstBlockQuadraticSlopeUpTo P‖ ≤ 4 * Real.pi := by
    calc
      ‖firstBlockQuadraticSlopeUpTo P‖
          = ‖(((4 * Real.pi : ℝ) : ℂ))‖ * ‖firstBlockQuadraticMassUpTo P‖ := by
              rw [firstBlockQuadraticSlopeUpTo, norm_mul]
      _ = |4 * Real.pi| * ‖firstBlockQuadraticMassUpTo P‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]
      _ = (4 * Real.pi) * ‖firstBlockQuadraticMassUpTo P‖ := by
            rw [abs_of_nonneg (by positivity)]
      _ ≤ (4 * Real.pi) * 1 := by
            have hmass := firstBlockQuadraticMassUpTo_norm_le hP
            nlinarith [Real.pi_pos, norm_nonneg (firstBlockQuadraticMassUpTo P)]
      _ = 4 * Real.pi := by ring
  have hOffset :
      ‖firstBlockQuadraticOffsetUpTo P‖ ≤ 4 * Real.pi := by
    calc
      ‖firstBlockQuadraticOffsetUpTo P‖
          = ‖(((4 * Real.pi : ℝ) : ℂ))‖ * ‖firstBlockQuadraticMomentUpTo P‖ := by
              rw [firstBlockQuadraticOffsetUpTo, norm_mul]
      _ = |4 * Real.pi| * ‖firstBlockQuadraticMomentUpTo P‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]
      _ = (4 * Real.pi) * ‖firstBlockQuadraticMomentUpTo P‖ := by
            rw [abs_of_nonneg (by positivity)]
      _ ≤ (4 * Real.pi) * 1 := by
            have hmoment := firstBlockQuadraticMomentUpTo_norm_le hP
            nlinarith [Real.pi_pos, norm_nonneg (firstBlockQuadraticMomentUpTo P)]
      _ = 4 * Real.pi := by ring
  have hCoeff :
      ‖L‖ ≤ K * ((n : ℝ) + 1) := by
    have hbase := firstBlockQuadraticCoeffUpTo_norm_le n P
    have hK' :
        ‖firstBlockQuadraticSlopeUpTo P‖ + ‖firstBlockQuadraticOffsetUpTo P‖ ≤ K := by
      dsimp [K]
      nlinarith [hSlope, hOffset]
    have hn1_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    calc
      ‖L‖ ≤ (‖firstBlockQuadraticSlopeUpTo P‖ + ‖firstBlockQuadraticOffsetUpTo P‖)
            * ((n : ℝ) + 1) := by
              simpa [L] using hbase
      _ ≤ K * ((n : ℝ) + 1) := by
            exact mul_le_mul_of_nonneg_right hK' hn1_nonneg
  have hStart' : ‖blockMode n 0 - a‖ ≤ C2 / ((n : ℝ) + 1) := by
    simpa [a] using hStart n
  have hAnchor :
      ‖blockMode n 0 * L - a * L‖ ≤ C2 * K := by
    calc
      ‖blockMode n 0 * L - a * L‖ = ‖(blockMode n 0 - a) * L‖ := by ring_nf
      _ = ‖blockMode n 0 - a‖ * ‖L‖ := by rw [norm_mul]
      _ ≤ (C2 / ((n : ℝ) + 1)) * (K * ((n : ℝ) + 1)) := by
            gcongr
      _ = C2 * K := by
            have hn1_pos : 0 < ((n : ℝ) + 1) := by positivity
            field_simp [ne_of_gt hn1_pos]
  have hsplit :
      ((∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t) - a * L)
        = ((∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t)
            - blockMode n 0 * L)
          + (blockMode n 0 * L - a * L) := by
              ring
  calc
    ‖(∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t) - a * L‖
        = ‖((∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t)
              - blockMode n 0 * L)
            + (blockMode n 0 * L - a * L)‖ := by
              rw [hsplit]
    _ ≤ ‖(∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t)
            - blockMode n 0 * L‖
          + ‖blockMode n 0 * L - a * L‖ := norm_add_le _ _
    _ ≤ C1 + C2 * K := by
          gcongr

/-- Real-part form of `hardyCosExp_firstBlock_anchor_main_term_upto_eventually`. -/
theorem hardyCos_firstBlock_anchor_main_term_upto_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ P ∈ Icc (0 : ℝ) 1,
        |(∫ t in Ioc (hardyStart n) (blockCoord n P), hardyCos n t)
            - ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                  Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
                (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
                  + firstBlockQuadraticOffsetUpTo P)).re)| ≤ C := by
  obtain ⟨C, hC, N0, hmain⟩ := hardyCosExp_firstBlock_anchor_main_term_upto_eventually
  refine ⟨C, hC, N0, ?_⟩
  intro n hn P hP
  have hmain' := hmain n hn P hP
  have hle : hardyStart n ≤ blockCoord n P := by
    simpa [blockCoord_zero] using
      (blockCoord_strictMonoOn_nonneg n).monotoneOn
        (by simp : (0 : ℝ) ∈ Ici 0) (by simpa using hP.1) hP.1
  have hInt :
      IntegrableOn (fun t : ℝ => HardyCosSmooth.hardyCosExp n t)
        (Ioc (hardyStart n) (blockCoord n P)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    exact (HardyCosSmooth.continuous_hardyCosExp_complex n).intervalIntegrable _ _
  have hIntCos :
      ∫ t in Ioc (hardyStart n) (blockCoord n P), hardyCos n t
        = (∫ t in Ioc (hardyStart n) (blockCoord n P),
            HardyCosSmooth.hardyCosExp n t).re := by
    calc
      ∫ t in Ioc (hardyStart n) (blockCoord n P), hardyCos n t
          = ∫ t in Ioc (hardyStart n) (blockCoord n P),
              (HardyCosSmooth.hardyCosExp n t).re := by
                refine MeasureTheory.integral_congr_ae ?_
                filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
                exact HardyCosSmooth.hardyCos_eq_re_hardyCosExp n t
      _ = (∫ t in Ioc (hardyStart n) (blockCoord n P),
            HardyCosSmooth.hardyCosExp n t).re := by
              simpa using integral_re hInt
  let target : ℂ :=
    (((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
        Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
      (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
        + firstBlockQuadraticOffsetUpTo P))
  have hsplit :
      (∫ t in Ioc (hardyStart n) (blockCoord n P), hardyCos n t) - target.re
        = ((∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t)
            - target).re := by
    rw [hIntCos]
    simp [target]
  calc
    |(∫ t in Ioc (hardyStart n) (blockCoord n P), hardyCos n t) - target.re|
        = |((∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t)
            - target).re| := by
              rw [hsplit]
    _ ≤ ‖(∫ t in Ioc (hardyStart n) (blockCoord n P), HardyCosSmooth.hardyCosExp n t)
            - target‖ := Complex.abs_re_le_norm _
    _ ≤ C := hmain'

/-- On the first stationary block, the exact Hardy mode integral is uniformly
close to the quadratic-model integral with linear-in-`(n+1)` main term. -/
theorem hardyCosExp_firstBlock_linear_model_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ‖(∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t)
          - blockMode n 0 *
              ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMass)
                + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMoment))‖
        ≤ C := by
  obtain ⟨C0, hC0, N0, hquad⟩ := blockMode_quadratic_model_eventually
  refine ⟨8 * Real.pi * C0, by positivity, N0, ?_⟩
  intro n hn
  have hT :
      hardyStart n ≤ blockCoord n 1 := by
    simpa [blockCoord_zero] using
      (blockCoord_strictMonoOn_nonneg n).monotoneOn
        (by simp : (0 : ℝ) ∈ Ici 0) (by simp : (1 : ℝ) ∈ Ici 0) (by norm_num : (0 : ℝ) ≤ 1)
  have hCov := hardyCosExp_integral_eq_blockParamIntegral n hT
  have hParam : blockParam n (blockCoord n 1) = 1 := by
    simpa using blockParam_blockCoord n 1 (by positivity)
  rw [hParam] at hCov
  have hCov' :
      ∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t
        = ∫ p in Ioc (0 : ℝ) 1, blockMode n p * blockJacobian n p := by
    simpa [blockMode] using hCov
  have hModelEq := firstBlockQuadraticModelIntegral_eq n
  have hIntActual :
      IntegrableOn (fun p : ℝ => blockMode n p * blockJacobian n p) (Ioc (0 : ℝ) 1) := by
    have hcont :
        Continuous (fun p : ℝ => blockMode n p * blockJacobian n p) := by
      exact ((HardyCosSmooth.continuous_hardyCosExp_complex n).comp (blockCoord_continuous n)).mul
        (Complex.continuous_ofReal.comp (blockJacobian_continuous n))
    simpa [blockMode] using hcont.integrableOn_Ioc
  have hIntModel :
      IntegrableOn (fun p : ℝ => blockMode n 0 * quadraticKernel p * blockJacobian n p)
        (Ioc (0 : ℝ) 1) := by
    have hcont :
        Continuous (fun p : ℝ => blockMode n 0 * quadraticKernel p * blockJacobian n p) := by
      exact ((continuous_const.mul quadraticKernel_continuous).mul
        (Complex.continuous_ofReal.comp (blockJacobian_continuous n)))
    simpa using hcont.integrableOn_Ioc
  have hrepr :
      (∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t)
        - blockMode n 0 *
            ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMass)
              + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMoment))
      = ∫ p in Ioc (0 : ℝ) 1,
          (blockMode n p - blockMode n 0 * quadraticKernel p) * blockJacobian n p := by
    rw [hCov', ← hModelEq, ← MeasureTheory.integral_sub hIntActual hIntModel]
    congr 1
    ext p
    ring
  have hvol_finite : volume (Ioc (0 : ℝ) 1) < ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hbound :
      ∀ p ∈ Ioc (0 : ℝ) 1,
        ‖(blockMode n p - blockMode n 0 * quadraticKernel p) * blockJacobian n p‖
          ≤ 8 * Real.pi * C0 := by
    intro p hp
    have hpIcc : p ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hp.1, hp.2⟩
    have hdiff :
        ‖blockMode n p - blockMode n 0 * quadraticKernel p‖ ≤ C0 / ((n : ℝ) + 1) := by
      simpa [quadraticKernel] using hquad n hn p hpIcc
    have hJ_nonneg : 0 ≤ blockJacobian n p := by
      rw [blockJacobian_eq_affine]
      have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      nlinarith [le_of_lt Real.pi_pos, hp.1]
    have hJ_bound : blockJacobian n p ≤ 8 * Real.pi * ((n : ℝ) + 1) := by
      rw [blockJacobian_eq_affine]
      have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      nlinarith [hp.2, Real.pi_pos]
    calc
      ‖(blockMode n p - blockMode n 0 * quadraticKernel p) * blockJacobian n p‖
          = ‖blockMode n p - blockMode n 0 * quadraticKernel p‖
              * ‖(((blockJacobian n p : ℝ) : ℂ))‖ := by
                rw [norm_mul]
      _ = ‖blockMode n p - blockMode n 0 * quadraticKernel p‖ * |blockJacobian n p| := by
            simpa using congrArg
              (fun x : ℝ => ‖blockMode n p - blockMode n 0 * quadraticKernel p‖ * x)
              (Complex.norm_real (blockJacobian n p))
      _ = ‖blockMode n p - blockMode n 0 * quadraticKernel p‖ * blockJacobian n p := by
            rw [abs_of_nonneg hJ_nonneg]
      _ ≤ (C0 / ((n : ℝ) + 1)) * (8 * Real.pi * ((n : ℝ) + 1)) := by
            gcongr
      _ = 8 * Real.pi * C0 := by
            have hn1_pos : 0 < ((n : ℝ) + 1) := by positivity
            field_simp [ne_of_gt hn1_pos]
  calc
    ‖(∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t)
        - blockMode n 0 *
            ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMass)
              + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMoment))‖
        = ‖∫ p in Ioc (0 : ℝ) 1,
            (blockMode n p - blockMode n 0 * quadraticKernel p) * blockJacobian n p‖ := by
              rw [hrepr]
    _ ≤ 8 * Real.pi * C0 * volume.real (Ioc (0 : ℝ) 1) := by
          exact norm_setIntegral_le_of_norm_le_const hvol_finite hbound
    _ = 8 * Real.pi * C0 := by
          rw [measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (show 0 ≤ (1 : ℝ) - 0 by norm_num)]
          norm_num

/-- The first stationary block already exhibits the alternating branch-free
main term, with `blockMode n 0` replaced by its stationary-point anchor. -/
theorem hardyCosExp_firstBlock_anchor_main_term_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ‖(∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t)
          - (((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
              (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlope)
                + firstBlockQuadraticOffset))‖
        ≤ C := by
  obtain ⟨C1, hC1, N0, hLinear⟩ := hardyCosExp_firstBlock_linear_model_eventually
  obtain ⟨C2, hC2, hStart⟩ := blockMode_zero_asymptotic
  let K : ℝ := ‖firstBlockQuadraticSlope‖ + ‖firstBlockQuadraticOffset‖ + 1
  refine ⟨C1 + C2 * K, add_pos hC1 (mul_pos hC2 (by positivity)), N0, ?_⟩
  intro n hn
  let a : ℂ :=
    ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
      Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)
  let L : ℂ :=
    (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlope) + firstBlockQuadraticOffset)
  have hCoeffEq :
      ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * firstBlockQuadraticMass)
        + (((4 * Real.pi : ℝ) : ℂ) * firstBlockQuadraticMoment)) = L := by
    simpa [L] using firstBlockQuadraticCoeff_eq n
  have hLinear' :
      ‖(∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t)
          - blockMode n 0 * L‖ ≤ C1 := by
    have htmp := hLinear n hn
    rwa [hCoeffEq] at htmp
  have hCoeff :
      ‖L‖ ≤ K * ((n : ℝ) + 1) := by
    have hbase := firstBlockQuadraticCoeff_norm_le n
    have hK : ‖firstBlockQuadraticSlope‖ + ‖firstBlockQuadraticOffset‖ ≤ K := by
      dsimp [K]
      nlinarith
    have hn1_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    calc
      ‖L‖ ≤ (‖firstBlockQuadraticSlope‖ + ‖firstBlockQuadraticOffset‖) * ((n : ℝ) + 1) := by
            simpa [L] using hbase
      _ ≤ K * ((n : ℝ) + 1) := by
            exact mul_le_mul_of_nonneg_right hK hn1_nonneg
  have hStart' : ‖blockMode n 0 - a‖ ≤ C2 / ((n : ℝ) + 1) := by
    simpa [a] using hStart n
  have hAnchor :
      ‖blockMode n 0 * L - a * L‖ ≤ C2 * K := by
    calc
      ‖blockMode n 0 * L - a * L‖ = ‖(blockMode n 0 - a) * L‖ := by
            ring_nf
      _ = ‖blockMode n 0 - a‖ * ‖L‖ := by rw [norm_mul]
      _ ≤ (C2 / ((n : ℝ) + 1)) * (K * ((n : ℝ) + 1)) := by
            gcongr
      _ = C2 * K := by
            have hn1_pos : 0 < ((n : ℝ) + 1) := by positivity
            field_simp [ne_of_gt hn1_pos]
  have hsplit :
      ((∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t) - a * L)
        = ((∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t)
            - blockMode n 0 * L)
          + (blockMode n 0 * L - a * L) := by
              ring
  calc
    ‖(∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t) - a * L‖
        = ‖((∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t)
              - blockMode n 0 * L)
            + (blockMode n 0 * L - a * L)‖ := by
              rw [hsplit]
    _ ≤ ‖(∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t)
            - blockMode n 0 * L‖
          + ‖blockMode n 0 * L - a * L‖ := norm_add_le _ _
    _ ≤ C1 + C2 * K := by
          gcongr

/-- Real-part form of `hardyCosExp_firstBlock_anchor_main_term_eventually`:
the resonant cosine mode on its complete first block already carries the
alternating branch-free affine main term with uniformly bounded error. -/
theorem hardyCos_firstBlock_anchor_main_term_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      |(∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
          - ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
              (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlope)
                + firstBlockQuadraticOffset)).re)| ≤ C := by
  obtain ⟨C, hC, N0, hmain⟩ := hardyCosExp_firstBlock_anchor_main_term_eventually
  refine ⟨C, hC, N0, ?_⟩
  intro n hn
  have hmain' := hmain n hn
  have hIntExp :
      ∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), HardyCosSmooth.hardyCosExp n t
        = ∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t := by
    simp [blockCoord_one]
  have hIntCos :
      ∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t
        = (∫ t in Ioc (hardyStart n) (hardyStart (n + 1)),
            HardyCosSmooth.hardyCosExp n t).re := by
    have hInt :
        IntegrableOn (fun t : ℝ => HardyCosSmooth.hardyCosExp n t)
          (Ioc (hardyStart n) (hardyStart (n + 1))) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (hardyStart_le_succ' n)]
      exact (HardyCosSmooth.continuous_hardyCosExp_complex n).intervalIntegrable _ _
    calc
      ∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t
          = ∫ t in Ioc (hardyStart n) (hardyStart (n + 1)),
              (HardyCosSmooth.hardyCosExp n t).re := by
                refine MeasureTheory.integral_congr_ae ?_
                filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
                exact HardyCosSmooth.hardyCos_eq_re_hardyCosExp n t
      _ = (∫ t in Ioc (hardyStart n) (hardyStart (n + 1)),
            HardyCosSmooth.hardyCosExp n t).re := by
              simpa using integral_re hInt
  let target : ℂ :=
    (((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
        Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
      (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlope)
        + firstBlockQuadraticOffset))
  have hsplit :
      (∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t) - target.re
        = ((∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t)
            - target).re := by
    rw [hIntCos, hIntExp]
    simp [target]
  calc
    |(∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t) - target.re|
        = |((∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t)
            - target).re| := by
              rw [hsplit]
    _ ≤ ‖(∫ t in Ioc (hardyStart n) (blockCoord n 1), HardyCosSmooth.hardyCosExp n t)
            - target‖ := Complex.abs_re_le_norm _
    _ ≤ C := hmain'


end Aristotle.StationaryPhaseMainMode
