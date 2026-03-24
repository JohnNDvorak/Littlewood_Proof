/-
Instance of CriticalZeroSumDivergesHyp: Under RH, ∑_{0<γ≤T} γ/(1/4+γ²) → ∞.

The proof uses:
1. N(T) ≥ T/(3π) log T for large T (ZeroCountingLowerBoundHyp)
2. γ/(1/4+γ²) ≥ 1/(2γ) for γ ≥ 1 (gamma_div_bound, already proved)
3. All zero ordinates > 1 (ZeroOrdinateLowerBoundHyp)
4. PositiveImZerosBelow T contains at least N(T) distinct zeros

Key argument: each weight γ/(1/4+γ²) ≥ 1/(2γ) ≥ 1/(2T) for γ ∈ (0,T],
so the sum ≥ N(T)/(2T) ≥ log(T)/(6π) → ∞.
-/

import Mathlib
import Littlewood.Aristotle.Standalone.PsiZeroSumOscillationFromIngham
import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.ZetaZeros.ZeroCountingMultiplicity

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped Classical

open Aristotle.DirichletPhaseAlignment (CriticalZeros ZerosBelow HardyCriticalLineZerosHyp)
open Aristotle.Standalone.PsiZeroSumOscillationFromIngham
  (PositiveImZerosBelow CriticalZeroSumDivergesHyp gamma_div_bound)
open ZetaZeros

namespace CriticalZeroSumDivergesProof

/-! ## Bridge lemmas connecting PositiveImZerosBelow T with zerosUpTo T -/

/-- CriticalZeros and zetaNontrivialZeros are the same set. -/
lemma criticalZeros_eq : CriticalZeros = zetaNontrivialZeros := by
  ext ρ
  simp only [CriticalZeros, zetaNontrivialZeros, Set.mem_setOf_eq]

/-- Membership in ZerosBelow T when finiteness holds. -/
lemma mem_zerosBelow [HardyCriticalLineZerosHyp] (T : ℝ) (ρ : ℂ) :
    ρ ∈ ZerosBelow T ↔ ρ ∈ CriticalZeros ∧ |ρ.im| ≤ T := by
  unfold ZerosBelow
  rw [dif_pos (HardyCriticalLineZerosHyp.zeros_finite T)]
  simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq]

/-- Elements of zerosUpTo T are in PositiveImZerosBelow T (for T ≥ 0). -/
lemma zerosUpTo_toFinset_subset_positiveImZerosBelow
    [HardyCriticalLineZerosHyp] {T : ℝ} (_hT : 0 ≤ T) :
    (finite_zeros_le T).toFinset ⊆ PositiveImZerosBelow T := by
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ
  -- ρ ∈ zerosUpTo T means ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T
  have hρ_mem : ρ ∈ zerosUpTo T := hρ
  simp only [zerosUpTo, Set.mem_inter_iff, Set.mem_setOf_eq] at hρ_mem
  obtain ⟨hρ_pos, hρ_le⟩ := hρ_mem
  have hρ_nt : ρ ∈ zetaNontrivialZeros := (mem_zetaNontrivialZerosPos.mp hρ_pos).1
  have hρ_im_pos : 0 < ρ.im := (mem_zetaNontrivialZerosPos.mp hρ_pos).2
  -- Show ρ ∈ PositiveImZerosBelow T
  unfold PositiveImZerosBelow
  rw [Finset.mem_filter]
  constructor
  · -- ρ ∈ ZerosBelow T
    rw [mem_zerosBelow]
    refine ⟨criticalZeros_eq ▸ hρ_nt, ?_⟩
    rw [abs_of_pos hρ_im_pos]
    exact hρ_le
  · -- 0 < ρ.im
    exact hρ_im_pos

/-- N(T) ≤ card(PositiveImZerosBelow T) for T ≥ 0. -/
lemma N_le_card_positiveImZerosBelow
    [HardyCriticalLineZerosHyp] {T : ℝ} (hT : 0 ≤ T) :
    N T ≤ (PositiveImZerosBelow T).card := by
  rw [zeroCountingFunction_eq_ncard, Set.ncard_eq_toFinset_card _ (finite_zeros_le T)]
  exact Finset.card_le_card (zerosUpTo_toFinset_subset_positiveImZerosBelow hT)

/-- Elements of PositiveImZerosBelow T have imaginary part ≤ T. -/
lemma positiveImZerosBelow_im_le
    [HardyCriticalLineZerosHyp] {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ PositiveImZerosBelow T) : |ρ.im| ≤ T := by
  unfold PositiveImZerosBelow at hρ
  rw [Finset.mem_filter] at hρ
  exact ((mem_zerosBelow T ρ).mp hρ.1).2

/-- Elements of PositiveImZerosBelow T have positive imaginary part. -/
lemma positiveImZerosBelow_im_pos
    [HardyCriticalLineZerosHyp] {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ PositiveImZerosBelow T) : 0 < ρ.im := by
  unfold PositiveImZerosBelow at hρ
  exact (Finset.mem_filter.mp hρ).2

/-- Elements of PositiveImZerosBelow T have imaginary part ≤ T (non-abs version). -/
lemma positiveImZerosBelow_im_le_T
    [HardyCriticalLineZerosHyp] {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ PositiveImZerosBelow T) : ρ.im ≤ T := by
  have him_pos := positiveImZerosBelow_im_pos hρ
  have habs := positiveImZerosBelow_im_le hρ
  rwa [abs_of_pos him_pos] at habs

/-- Elements of PositiveImZerosBelow T are in zetaNontrivialZerosPos. -/
lemma positiveImZerosBelow_mem_zetaNontrivialZerosPos
    [HardyCriticalLineZerosHyp] {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ PositiveImZerosBelow T) : ρ ∈ zetaNontrivialZerosPos := by
  unfold PositiveImZerosBelow at hρ
  rw [Finset.mem_filter] at hρ
  obtain ⟨hρ_zb, hρ_im⟩ := hρ
  rw [mem_zerosBelow] at hρ_zb
  rw [mem_zetaNontrivialZerosPos]
  exact ⟨criticalZeros_eq ▸ hρ_zb.1, hρ_im⟩

/-! ## Lower bound on the weighted sum -/

/-- Key bound: for ρ with Im(ρ) > 1 and Im(ρ) ≤ T:
    ρ.im / (1/4 + ρ.im^2) ≥ 1/(2*T). -/
lemma weight_lower_bound {T : ℝ} {ρ : ℂ}
    (hρ_im_ge : 1 ≤ ρ.im) (hρ_im_le : ρ.im ≤ T) :
    1 / (2 * T) ≤ ρ.im / (1/4 + ρ.im ^ 2) := by
  have hγ_pos : 0 < ρ.im := by linarith
  have hT_pos : 0 < T := by linarith
  calc 1 / (2 * T) ≤ 1 / (2 * ρ.im) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
      _ ≤ ρ.im / (1/4 + ρ.im ^ 2) := gamma_div_bound ρ.im hρ_im_ge

/-- The weighted sum over PositiveImZerosBelow T is at least N(T)/(2T) for T ≥ 2.
    Uses that all zero ordinates are > 1 (ZeroOrdinateLowerBoundHyp). -/
lemma sum_weight_ge_N_div_2T
    [HardyCriticalLineZerosHyp] [ZetaZeros.ZeroOrdinateLowerBoundHyp]
    {T : ℝ} (hT : 2 ≤ T) :
    (N T : ℝ) / (2 * T) ≤
      ∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2) := by
  have hT_pos : (0 : ℝ) < T := by linarith
  have h2T_pos : (0 : ℝ) < 2 * T := by linarith
  -- Each term is ≥ 1/(2T)
  have hterm : ∀ ρ ∈ PositiveImZerosBelow T,
      1 / (2 * T) ≤ ρ.im / (1/4 + ρ.im ^ 2) := by
    intro ρ hρ
    have him_pos := positiveImZerosBelow_im_pos hρ
    have him_le := positiveImZerosBelow_im_le_T hρ
    have hρ_nnz := positiveImZerosBelow_mem_zetaNontrivialZerosPos hρ
    have him_gt_one : (1 : ℝ) < ρ.im := ZetaZeros.ZeroOrdinateLowerBoundHyp.lower_bound ρ hρ_nnz
    exact weight_lower_bound (le_of_lt him_gt_one) him_le
  -- Sum ≥ card * (1/(2T))
  have hsum : (PositiveImZerosBelow T).card • (1 / (2 * T)) ≤
      ∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2) :=
    Finset.card_nsmul_le_sum _ _ _ hterm
  -- card ≥ N(T)
  have hcard : N T ≤ (PositiveImZerosBelow T).card :=
    N_le_card_positiveImZerosBelow (by linarith)
  -- Combine
  calc (N T : ℝ) / (2 * T)
      = (N T : ℝ) * (1 / (2 * T)) := by ring
    _ ≤ ((PositiveImZerosBelow T).card : ℝ) * (1 / (2 * T)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcard
        · positivity
    _ = (PositiveImZerosBelow T).card • (1 / (2 * T)) := by
        rw [nsmul_eq_mul]
    _ ≤ ∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2) := hsum

/-- Combining with N(T) ≥ T/(3π) log T: sum ≥ log(T)/(6π). -/
lemma sum_weight_ge_log_div
    [HardyCriticalLineZerosHyp] [ZetaZeros.ZeroOrdinateLowerBoundHyp]
    [ZeroCountingLowerBoundHyp]
    {T : ℝ} (hT : 2 ≤ T) (hT0 : ∀ T0 : ℝ, T0 ≤ T → T / (3 * Real.pi) * Real.log T ≤ N T) :
    Real.log T / (6 * Real.pi) ≤
      ∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2) := by
  have hT_pos : (0 : ℝ) < T := by linarith
  have h2T_pos : (0 : ℝ) < 2 * T := by linarith
  have hN_lower : T / (3 * Real.pi) * Real.log T ≤ N T := hT0 T le_rfl
  calc Real.log T / (6 * Real.pi)
      = (T / (3 * Real.pi) * Real.log T) / (2 * T) := by
        have hT_ne : T ≠ 0 := ne_of_gt hT_pos
        field_simp
        ring
    _ ≤ (N T : ℝ) / (2 * T) := by
        apply div_le_div_of_nonneg_right hN_lower (by positivity)
    _ ≤ ∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2) :=
        sum_weight_ge_N_div_2T hT

/-! ## Main instance -/

instance
    [HardyCriticalLineZerosHyp] [ZetaZeros.ZeroOrdinateLowerBoundHyp]
    [ZeroCountingLowerBoundHyp] :
    CriticalZeroSumDivergesHyp where
  proof := by
    intro hRH M
    -- Get T₀ from the lower bound hypothesis
    obtain ⟨T₀, hT₀⟩ := ZeroCountingLowerBoundHyp.lower_bound
    -- Choose T large enough that log(T)/(6π) ≥ M and T ≥ T₀ and T ≥ 2
    -- We need T ≥ exp(6πM) and T ≥ T₀ and T ≥ 2
    set T := max (max T₀ 2) (Real.exp (6 * Real.pi * max M 0 + 1)) with hT_def
    refine ⟨T, ?_, ?_⟩
    · -- T ≥ 2
      exact le_trans (le_max_right T₀ 2) (le_max_left _ _)
    · -- M ≤ sum
      have hT_ge_T₀ : T₀ ≤ T := le_trans (le_max_left T₀ 2) (le_max_left _ _)
      have hT_ge_2 : (2 : ℝ) ≤ T := le_trans (le_max_right T₀ 2) (le_max_left _ _)
      have hT_ge_exp : Real.exp (6 * Real.pi * max M 0 + 1) ≤ T := le_max_right _ _
      have hN_lower : T / (3 * Real.pi) * Real.log T ≤ N T := by
        exact_mod_cast hT₀ T hT_ge_T₀
      have hlog_ge : 6 * Real.pi * max M 0 + 1 ≤ Real.log T := by
        calc 6 * Real.pi * max M 0 + 1
            = Real.log (Real.exp (6 * Real.pi * max M 0 + 1)) := by
                rw [Real.log_exp]
          _ ≤ Real.log T := by
                apply Real.log_le_log (Real.exp_pos _) hT_ge_exp
      have hM_le : M ≤ Real.log T / (6 * Real.pi) := by
        have hpi_pos : (0 : ℝ) < 6 * Real.pi := by positivity
        rw [le_div_iff₀ hpi_pos]
        calc M * (6 * Real.pi) ≤ max M 0 * (6 * Real.pi) := by
              apply mul_le_mul_of_nonneg_right (le_max_left M 0) (le_of_lt hpi_pos)
          _ = 6 * Real.pi * max M 0 := by ring
          _ ≤ 6 * Real.pi * max M 0 + 1 := le_add_of_nonneg_right (by norm_num)
          _ ≤ Real.log T := hlog_ge
      calc M ≤ Real.log T / (6 * Real.pi) := hM_le
        _ ≤ ∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2) :=
            sum_weight_ge_log_div hT_ge_2 (fun T₁ hT₁ => by
              -- Need: T / (3π) * log T ≤ N T, using the fact that T₁ ≤ T
              -- But the function T₁ here is bound by hT₁
              -- We need N(T) ≥ T/(3π) log T. We have T₀ ≤ T.
              exact_mod_cast hT₀ T hT_ge_T₀)

end CriticalZeroSumDivergesProof
