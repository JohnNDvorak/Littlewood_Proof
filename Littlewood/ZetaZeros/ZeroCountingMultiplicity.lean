import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.Aristotle.ZetaLogDerivInfra

set_option autoImplicit false

/-!
# Multiplicity-counted zero counting for zeta zeros

This module is the additive, multiplicity-counted companion to
`Littlewood.ZetaZeros.ZeroCountingFunction`. It leaves the existing distinct-count
surface intact and exposes a parallel `Nmult` API for downstream RvM work.
-/

noncomputable section

namespace ZetaZeros

open Filter
open scoped BigOperators Real

/-- `Nmult(T)` counts nontrivial zeta zeros with `0 < Im(ρ) ≤ T`, with multiplicity. -/
noncomputable def zeroCountingFunctionMult (T : ℝ) : ℕ :=
  ∑ ρ ∈ (finite_zeros_le T).toFinset, (analyticOrderAt riemannZeta ρ).toNat

/-- Notation for the multiplicity-counted zero counting function. -/
scoped notation "Nmult" => zeroCountingFunctionMult

theorem zeroCountingFunctionMult_eq_sum (T : ℝ) :
    Nmult T = ∑ ρ ∈ (finite_zeros_le T).toFinset, (analyticOrderAt riemannZeta ρ).toNat := by
  rfl

theorem zeroCountingFunction_eq_finset_card (T : ℝ) :
    N T = (finite_zeros_le T).toFinset.card := by
  rw [zeroCountingFunction_eq_ncard]
  simpa [zerosUpTo] using (Set.ncard_eq_toFinset_card (zerosUpTo T) (finite_zeros_le T))

private theorem analyticOrderAt_toNat_pos_of_mem_zerosUpTo {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zerosUpTo T) :
    0 < (analyticOrderAt riemannZeta ρ).toNat := by
  have hρ' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hρ
  rcases mem_zetaNontrivialZerosPos.mp hρ'.1 with ⟨hzeta, _⟩
  rcases mem_zetaNontrivialZeros.mp hzeta with ⟨hzero, _, hre_lt⟩
  have hρ_ne_one : ρ ≠ 1 := by
    intro h1
    rw [h1] at hre_lt
    norm_num at hre_lt
  rcases Aristotle.ZetaLogDerivInfra.zeta_analytic_order_finite_pos ρ hzero hρ_ne_one with
    ⟨n, hn, horder⟩
  simpa [horder] using hn

theorem zeroCountingFunction_le_zeroCountingFunctionMult (T : ℝ) :
    N T ≤ Nmult T := by
  rw [zeroCountingFunction_eq_finset_card, zeroCountingFunctionMult_eq_sum, Finset.card_eq_sum_ones]
  simpa using
    (Finset.card_nsmul_le_sum ((finite_zeros_le T).toFinset)
      (fun ρ => (analyticOrderAt riemannZeta ρ).toNat) 1
      (by
        intro ρ hρ
        exact Nat.succ_le_of_lt
          (analyticOrderAt_toNat_pos_of_mem_zerosUpTo (by simpa [zerosUpTo] using hρ))))

theorem zeroCountingFunction_le_zeroCountingFunctionMult_real (T : ℝ) :
    (N T : ℝ) ≤ (Nmult T : ℝ) := by
  exact_mod_cast zeroCountingFunction_le_zeroCountingFunctionMult T

theorem zeroCountingFunctionMult_sub_nonneg (T : ℝ) :
    0 ≤ (Nmult T : ℝ) - (N T : ℝ) := by
  exact sub_nonneg.mpr (zeroCountingFunction_le_zeroCountingFunctionMult_real T)

theorem zeroCountingFunction_abs_sub_zeroCountingFunctionMult (T : ℝ) :
    |(N T : ℝ) - (Nmult T : ℝ)| = (Nmult T : ℝ) - (N T : ℝ) := by
  have hsub : (N T : ℝ) - (Nmult T : ℝ) ≤ 0 := by
    exact sub_nonpos.mpr (zeroCountingFunction_le_zeroCountingFunctionMult_real T)
  rw [abs_of_nonpos hsub]
  ring

theorem zeroCountingFunctionMult_eq_zero_iff (T : ℝ) :
    Nmult T = 0 ↔ zerosUpTo T = ∅ := by
  constructor
  · intro hN
    by_contra hzero
    rcases Set.nonempty_iff_ne_empty.mpr hzero with ⟨ρ, hρ⟩
    have hρ_finset : ρ ∈ (finite_zeros_le T).toFinset := by
      simpa using hρ
    have hterm_pos : 0 < (analyticOrderAt riemannZeta ρ).toNat :=
      analyticOrderAt_toNat_pos_of_mem_zerosUpTo hρ
    have hterm_le : (analyticOrderAt riemannZeta ρ).toNat ≤ Nmult T := by
      unfold zeroCountingFunctionMult
      exact Finset.single_le_sum
        (f := fun ζ => (analyticOrderAt riemannZeta ζ).toNat)
        (fun _ _ => Nat.zero_le _) hρ_finset
    have hsum_pos : 0 < Nmult T := lt_of_lt_of_le hterm_pos hterm_le
    omega
  · intro hzero
    have hfinset_empty : (finite_zeros_le T).toFinset = ∅ := by
      exact (Set.Finite.toFinset_eq_empty (h := finite_zeros_le T)).2 hzero
    simp [zeroCountingFunctionMult, hfinset_empty]

theorem finite_zero_finset_eq_empty_of_zeroCountingFunctionMult_eq_zero {T : ℝ}
    (hT : Nmult T = 0) :
    (finite_zeros_le T).toFinset = ∅ := by
  exact
    (Set.Finite.toFinset_eq_empty (h := finite_zeros_le T)).2
      ((zeroCountingFunctionMult_eq_zero_iff T).mp hT)

class ZeroOrdinateLowerBoundHyp : Prop where
  lower_bound : ∀ ρ ∈ zetaNontrivialZerosPos, (1 : ℝ) < ρ.im

theorem zero_ord_lower_bound [ZeroOrdinateLowerBoundHyp] :
    ∀ ρ ∈ zetaNontrivialZerosPos, (1 : ℝ) < ρ.im :=
  ZeroOrdinateLowerBoundHyp.lower_bound

class ZeroCountingMultTendstoHyp : Prop where
  tendsto_atTop : Tendsto (fun T => (Nmult T : ℝ)) atTop atTop

class ZeroCountingMultRvmExplicitHyp : Prop where
  bound :
    ∃ C T0 : ℝ, ∀ T ≥ T0,
      |(Nmult T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * Real.log T

class ZeroCountingMultAsymptoticHyp : Prop where
  asymptotic :
    (fun T => (Nmult T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π))
    =O[atTop] (fun T => Real.log T)

class ZeroCountingMultMainTermHyp : Prop where
  mainTerm :
    Tendsto (fun T => (Nmult T : ℝ) / (T / (2 * π) * Real.log T)) atTop (nhds 1)

class ZeroCountingMultLowerBoundHyp : Prop where
  lower_bound : ∃ T0 : ℝ, ∀ T ≥ T0, T / (3 * π) * Real.log T ≤ Nmult T

theorem zeroCountingFunctionMult_tendsto_atTop [ZeroCountingMultTendstoHyp] :
    Tendsto (fun T => (Nmult T : ℝ)) atTop atTop := by
  simpa using ZeroCountingMultTendstoHyp.tendsto_atTop

theorem zeroCountingFunctionMult_rvm_explicit_hyp [ZeroCountingMultRvmExplicitHyp] :
    ∃ C T0 : ℝ, ∀ T ≥ T0,
      |(Nmult T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * Real.log T := by
  simpa using ZeroCountingMultRvmExplicitHyp.bound

theorem zeroCountingFunctionMult_lower_bound [ZeroCountingMultLowerBoundHyp] :
    ∃ T0 : ℝ, ∀ T ≥ T0, T / (3 * π) * Real.log T ≤ Nmult T := by
  simpa using ZeroCountingMultLowerBoundHyp.lower_bound

noncomputable instance zeroCountingMultLowerBoundHyp_of_rvmExplicit
    [ZeroCountingMultRvmExplicitHyp] :
    ZeroCountingMultLowerBoundHyp := by
  classical
  rcases zeroCountingFunctionMult_rvm_explicit_hyp with ⟨C, T0, hC⟩
  let C0 : ℝ := max C 0
  let T1 : ℝ := max T0 (12 * π * C0)
  let T2 : ℝ := Real.exp (6 * (Real.log (2 * π) + 1))
  refine ⟨max T1 T2, ?_⟩
  intro T hT
  have hT0 : T0 ≤ T := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)
  have hC0_nonneg : 0 ≤ C0 := le_max_right _ _
  have hT12C0 : 12 * π * C0 ≤ T := by
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hT)
  have hTC0 : 6 * π * C0 ≤ T := by
    have hhalf : 6 * π * C0 ≤ 12 * π * C0 := by
      nlinarith [Real.pi_pos, hC0_nonneg]
    exact hhalf.trans hT12C0
  have hTT2 : T2 ≤ T := by
    exact le_trans (le_max_right _ _) hT
  have hT_one : (1 : ℝ) ≤ T := by
    have hT2_gt_one : 1 < T2 := by
      have hexp_pos : 0 < 3 * (Real.log (2 * π) + 1) := by
        have hlog_pos : 0 < Real.log (2 * π) := by
          have h2pi_gt_one : (1 : ℝ) < 2 * π := by
            nlinarith [Real.pi_gt_three]
          exact Real.log_pos h2pi_gt_one
        linarith
      have hT2_gt_one' : 1 < Real.exp (6 * (Real.log (2 * π) + 1)) := by
        simpa using Real.one_lt_exp_iff.mpr (by linarith [hexp_pos])
      simpa [T2] using hT2_gt_one'
    linarith
  have hlog_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT_one
  have hlog_ge :
      6 * (Real.log (2 * π) + 1) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos _) hTT2
    simpa [T2, Real.log_exp] using this
  have hErr : |(Nmult T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
      ≤ C0 * Real.log T := by
    have hbase := hC T hT0
    have hC_le : C * Real.log T ≤ C0 * Real.log T := by
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlog_nonneg
    exact hbase.trans hC_le
  have hmain_lower :
      (T / (2 * π)) * Real.log (T / (2 * π)) - T / (2 * π) - C0 * Real.log T
        ≤ Nmult T := by
    have hleft := (abs_le.mp hErr).1
    linarith
  have hC0_term :
      C0 * Real.log T ≤ T / (12 * π) * Real.log T := by
    have hfactor : C0 ≤ T / (12 * π) := by
      have h12pi_pos : 0 < (12 * π : ℝ) := by positivity
      refine (le_div_iff₀ h12pi_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hT12C0
    exact mul_le_mul_of_nonneg_right hfactor hlog_nonneg
  have hconst_term :
      (T / (2 * π)) * (Real.log (2 * π) + 1) ≤ T / (12 * π) * Real.log T := by
    have hthree : Real.log (2 * π) + 1 ≤ Real.log T / 6 := by
      refine (le_div_iff₀ (by norm_num : (0 : ℝ) < 6)).2 ?_
      linarith
    have hscale_nonneg : 0 ≤ T / (2 * π) := by
      have hT_nonneg : 0 ≤ T := by linarith
      have h2pi_pos : 0 < (2 * π : ℝ) := by positivity
      exact div_nonneg hT_nonneg h2pi_pos.le
    have hmul := mul_le_mul_of_nonneg_left hthree hscale_nonneg
    have hrewrite :
        (T / (2 * π)) * (Real.log T / 6) = T / (12 * π) * Real.log T := by
      field_simp [Real.pi_ne_zero]
      ring
    exact hmul.trans_eq hrewrite
  have hsplit :
      T / (3 * π) * Real.log T
        ≤ (T / (2 * π)) * Real.log (T / (2 * π)) - T / (2 * π) - C0 * Real.log T := by
    have hlog_div :
        Real.log (T / (2 * π)) = Real.log T - Real.log (2 * π) := by
      have hT_ne : T ≠ 0 := by positivity
      have h2pi_ne : (2 * π : ℝ) ≠ 0 := by positivity
      rw [Real.log_div hT_ne h2pi_ne]
    have hsum_terms :
        (T / (2 * π)) * (Real.log (2 * π) + 1) + C0 * Real.log T
          ≤ T / (6 * π) * Real.log T := by
      calc
        (T / (2 * π)) * (Real.log (2 * π) + 1) + C0 * Real.log T
            ≤ T / (12 * π) * Real.log T + T / (12 * π) * Real.log T := by
              exact add_le_add hconst_term hC0_term
        _ = T / (6 * π) * Real.log T := by ring
    calc
      T / (3 * π) * Real.log T
          = (T / (2 * π)) * Real.log T - T / (6 * π) * Real.log T := by ring
      _ ≤ (T / (2 * π)) * Real.log T
            - (T / (2 * π)) * (Real.log (2 * π) + 1)
            - C0 * Real.log T := by
              calc
                (T / (2 * π)) * Real.log T - T / (6 * π) * Real.log T
                    ≤ (T / (2 * π)) * Real.log T
                      - ((T / (2 * π)) * (Real.log (2 * π) + 1) + C0 * Real.log T) := by
                        exact sub_le_sub_left hsum_terms ((T / (2 * π)) * Real.log T)
                _ = (T / (2 * π)) * Real.log T
                      - (T / (2 * π)) * (Real.log (2 * π) + 1)
                      - C0 * Real.log T := by ring
      _ = (T / (2 * π)) * Real.log (T / (2 * π)) - T / (2 * π) - C0 * Real.log T := by
            rw [hlog_div]
            ring
  exact hsplit.trans hmain_lower

instance zeroCountingMultTendstoHyp_of_lower_bound [ZeroCountingMultLowerBoundHyp] :
    ZeroCountingMultTendstoHyp := by
  refine ⟨?_⟩
  refine Filter.tendsto_atTop_atTop.2 ?_
  intro b
  have hmul : Tendsto (fun T : ℝ => T * Real.log T) Filter.atTop Filter.atTop :=
    (Filter.tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop)
  have hpos : 0 < (1 / (3 * π) : ℝ) := by
    have hdenom : 0 < (3 * π : ℝ) := by nlinarith [Real.pi_pos]
    exact one_div_pos.mpr hdenom
  have hconst :
      Tendsto (fun T : ℝ => (1 / (3 * π)) * (T * Real.log T)) Filter.atTop Filter.atTop :=
    (Filter.Tendsto.const_mul_atTop hpos hmul)
  rcases (Filter.tendsto_atTop_atTop.1 hconst b) with ⟨T0, hT0⟩
  rcases zeroCountingFunctionMult_lower_bound with ⟨T1, hT1⟩
  refine ⟨max T0 T1, ?_⟩
  intro T hT
  have hT0' : T0 ≤ T := le_trans (le_max_left _ _) hT
  have hT1' : T1 ≤ T := le_trans (le_max_right _ _) hT
  have hb : b ≤ (1 / (3 * π)) * (T * Real.log T) := hT0 T hT0'
  have hlow :
      (1 / (3 * π)) * (T * Real.log T) ≤ Nmult T := by
    have hlow' := hT1 T hT1'
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlow'
  exact hb.trans hlow

instance zetaHasNontrivialZero_of_mult_tendsto [ZeroCountingMultTendstoHyp] :
    ZetaHasNontrivialZeroHyp := by
  refine ⟨?_⟩
  have htend := ZeroCountingMultTendstoHyp.tendsto_atTop
  rw [Filter.tendsto_atTop_atTop] at htend
  rcases htend 1 with ⟨T, hT⟩
  have hNT : 1 ≤ (Nmult T : ℝ) := hT T le_rfl
  have hNT' : 0 < Nmult T := by
    have : (1 : ℕ) ≤ Nmult T := by exact_mod_cast hNT
    omega
  have hne : (zerosUpTo T).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have := (zeroCountingFunctionMult_eq_zero_iff T).mpr hempty
    omega
  rcases hne with ⟨s, hs⟩
  exact ⟨s, (Set.mem_inter_iff _ _ _).mp hs |>.1⟩

end ZetaZeros
