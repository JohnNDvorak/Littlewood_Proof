import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.CoreLemmas.GrowthDomination

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiReciprocalNormGrowth

open scoped BigOperators
open ZetaZeros
open GrowthDomination

/-- If `ρ` is counted by `zerosUpTo T`, then `1/(T+1) ≤ 1/‖ρ‖`. -/
private lemma inv_bound_of_mem_zerosUpTo
    {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ zerosUpTo T) :
    1 / (T + 1) ≤ 1 / ‖ρ‖ := by
  have hρ' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hρ
  have hzpos : ρ ∈ zetaNontrivialZerosPos := hρ'.1
  have him_le : ρ.im ≤ T := hρ'.2
  rcases (mem_zetaNontrivialZerosPos.1 hzpos) with ⟨hzeta, him_pos⟩
  have hre_pos : 0 < ρ.re := hzeta.2.1
  have hre_lt_one : ρ.re < 1 := hzeta.2.2
  have hρ_ne : ρ ≠ 0 := by
    intro h0
    have : (0 : ℝ) < 0 := by simp [h0] at hre_pos
    exact (lt_irrefl 0) this
  have hnorm_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
  have hnorm_le : ‖ρ‖ ≤ T + 1 := by
    have h_abs_re : |ρ.re| = ρ.re := abs_of_nonneg (le_of_lt hre_pos)
    have h_im_nonneg : 0 ≤ ρ.im := le_of_lt him_pos
    have h_abs_im : |ρ.im| = ρ.im := abs_of_nonneg h_im_nonneg
    calc
      ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ = ρ.re + ρ.im := by rw [h_abs_re, h_abs_im]
      _ ≤ 1 + T := by linarith
      _ = T + 1 := by ring
  have hT1_pos : 0 < T + 1 := by linarith
  exact one_div_le_one_div_of_le hnorm_pos hnorm_le

/-- Lower bound for the reciprocal-norm sum over zeros up to height `T`. -/
theorem sum_inv_norm_ge_zero_count_div
    (T : ℝ) (_hT : 4 ≤ T) :
    (N T : ℝ) / (T + 1)
      ≤ Finset.sum (finite_zeros_le T).toFinset (fun ρ => 1 / ‖ρ‖) := by
  let S : Finset ℂ := (finite_zeros_le T).toFinset
  have hconst :
      ∀ ρ ∈ S, 1 / (T + 1) ≤ (1 / ‖ρ‖) := by
    intro ρ hρ
    exact inv_bound_of_mem_zerosUpTo (by simpa [S] using hρ)
  have hsum_const_le :
      Finset.sum S (fun _ => (1 / (T + 1)))
        ≤ Finset.sum S (fun ρ => (1 / ‖ρ‖)) := by
    exact Finset.sum_le_sum (fun ρ hρ => hconst ρ hρ)
  have hcard : (S.card : ℝ) = (N T : ℝ) := by
    unfold S
    have hcardNat :
        (finite_zeros_le T).toFinset.card = N T := by
      have hn :
          (zerosUpTo T).ncard = (finite_zeros_le T).toFinset.card :=
        Set.ncard_eq_toFinset_card (zerosUpTo T) (finite_zeros_le T)
      simpa [zeroCountingFunction_eq_ncard] using hn.symm
    exact_mod_cast hcardNat
  have hconst_eval :
      Finset.sum S (fun _ => (1 / (T + 1)))
        = (N T : ℝ) / (T + 1) := by
    calc
      Finset.sum S (fun _ => (1 / (T + 1)))
          = (S.card : ℝ) * (1 / (T + 1)) := by simp
      _ = (N T : ℝ) * (1 / (T + 1)) := by simpa using congrArg (fun z : ℝ => z * (1 / (T + 1))) hcard
      _ = (N T : ℝ) / (T + 1) := by ring
  calc
    (N T : ℝ) / (T + 1) = Finset.sum S (fun _ => (1 / (T + 1))) := by
      symm
      exact hconst_eval
    _ ≤ Finset.sum S (fun ρ => (1 / ‖ρ‖)) := hsum_const_le
    _ = Finset.sum (finite_zeros_le T).toFinset (fun ρ => (1 / ‖ρ‖)) := by
      rfl

/-- Membership in the canonical zero finset up to `T` is a nontrivial zero; under
RH it lies on the critical line. -/
lemma mem_zero_finset_critical_line
    (hRH : ∀ ρ ∈ zetaNontrivialZeros, ρ.re = 1 / 2) {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (finite_zeros_le T).toFinset) :
    ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2 := by
  have hz : ρ ∈ zerosUpTo T := by
    simpa using hρ
  have hz' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hz
  have hzeta : ρ ∈ zetaNontrivialZeros :=
    (mem_zetaNontrivialZerosPos.1 hz'.1).1
  exact ⟨hzeta, hRH ρ hzeta⟩

private lemma half_le_div_self_add_one {x : ℝ} (hx : 1 ≤ x) :
    (1 / 2 : ℝ) ≤ x / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  refine (le_div_iff₀ hx1).2 ?_
  nlinarith [hx]

/-- Coefficient-domination transfer: if one controls
`(N T)/(T+1)`, then one gets the exact finite-zero coefficient shape used by the
RH π target-phase witnesses. -/
theorem coeff_domination_of_zero_count_div
    {x T ε : ℝ}
    (hε : ε < 1)
    (hN : 2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)))
    (hT : 4 ≤ T) :
    2 * lll x
      ≤ (1 - ε) *
          Finset.sum (finite_zeros_le T).toFinset (fun ρ => 1 / ‖ρ‖) := by
  have hsum :
      ((N T : ℝ) / (T + 1))
        ≤ Finset.sum (finite_zeros_le T).toFinset (fun ρ => 1 / ‖ρ‖) :=
    sum_inv_norm_ge_zero_count_div T hT
  have hfac_nonneg : 0 ≤ 1 - ε := by linarith
  have hmul :
      (1 - ε) * ((N T : ℝ) / (T + 1))
        ≤ (1 - ε) *
            Finset.sum (finite_zeros_le T).toFinset (fun ρ => 1 / ‖ρ‖) :=
    mul_le_mul_of_nonneg_left hsum hfac_nonneg
  exact le_trans hN hmul

/-- Quantitative unboundedness of reciprocal-norm finite sums from
`ZeroCountingLowerBoundHyp`. -/
theorem sum_inv_norm_unbounded
    [ZeroCountingLowerBoundHyp] :
    ∀ B : ℝ, ∃ T : ℝ, 4 ≤ T ∧
      B ≤ Finset.sum (finite_zeros_le T).toFinset (fun ρ => 1 / ‖ρ‖) := by
  intro B
  rcases zeroCountingFunction_lower_bound with ⟨T0, hT0⟩
  let B0 : ℝ := max B 0
  let T : ℝ := max (max T0 4) (Real.exp (6 * Real.pi * B0))
  have hT_ge_T0 : T0 ≤ T := by
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hT_ge4 : 4 ≤ T := by
    exact le_trans (le_max_right T0 4) (le_max_left _ _)
  have hT_ge1 : (1 : ℝ) ≤ T := by linarith [hT_ge4]
  have hT1_pos : 0 < T + 1 := by linarith
  have hB_le_B0 : B ≤ B0 := le_max_left _ _

  have hN_lower : T / (3 * Real.pi) * Real.log T ≤ N T := hT0 T hT_ge_T0
  have hN_div :
      (T / (3 * Real.pi) * Real.log T) / (T + 1)
        ≤ (N T : ℝ) / (T + 1) := by
    exact div_le_div_of_nonneg_right hN_lower (le_of_lt hT1_pos)

  have hratio : (1 / 2 : ℝ) ≤ T / (T + 1) :=
    half_le_div_self_add_one hT_ge1
  have hlog_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT_ge1
  have hbase_nonneg : 0 ≤ (1 / (3 * Real.pi)) * Real.log T := by
    exact mul_nonneg (by positivity) hlog_nonneg
  have hmul_ratio :
      (1 / 2 : ℝ) * ((1 / (3 * Real.pi)) * Real.log T)
        ≤ (T / (T + 1)) * ((1 / (3 * Real.pi)) * Real.log T) := by
    exact mul_le_mul_of_nonneg_right hratio hbase_nonneg

  have hfactor :
      (T / (T + 1)) * ((1 / (3 * Real.pi)) * Real.log T)
        = (T / (3 * Real.pi) * Real.log T) / (T + 1) := by
    field_simp [hT1_pos.ne']

  have hcoef_le :
      (1 / (6 * Real.pi)) * Real.log T
        ≤ (N T : ℝ) / (T + 1) := by
    have hleft :
        (1 / (6 * Real.pi)) * Real.log T
          = (1 / 2 : ℝ) * ((1 / (3 * Real.pi)) * Real.log T) := by ring
    calc
      (1 / (6 * Real.pi)) * Real.log T
          = (1 / 2 : ℝ) * ((1 / (3 * Real.pi)) * Real.log T) := hleft
      _ ≤ (T / (T + 1)) * ((1 / (3 * Real.pi)) * Real.log T) := hmul_ratio
      _ = (T / (3 * Real.pi) * Real.log T) / (T + 1) := hfactor
      _ ≤ (N T : ℝ) / (T + 1) := hN_div

  have hsum_lower :
      (N T : ℝ) / (T + 1)
        ≤ Finset.sum (finite_zeros_le T).toFinset (fun ρ => (1 / ‖ρ‖)) :=
    sum_inv_norm_ge_zero_count_div T hT_ge4

  have hExp_le : Real.exp (6 * Real.pi * B0) ≤ T := by
    exact le_max_right _ _
  have hlog_ge : 6 * Real.pi * B0 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos _) hExp_le
    simpa [Real.log_exp] using h
  have hB0_le_log :
      B0 ≤ (1 / (6 * Real.pi)) * Real.log T := by
    have h6pi_pos : 0 < (6 * Real.pi : ℝ) := by positivity
    have h' : B0 ≤ Real.log T / (6 * Real.pi) := by
      refine (le_div_iff₀ h6pi_pos).2 ?_
      nlinarith [hlog_ge]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'

  refine ⟨T, hT_ge4, ?_⟩
  exact hB_le_B0.trans (hB0_le_log.trans (hcoef_le.trans hsum_lower))

end Aristotle.Standalone.RHPiReciprocalNormGrowth
