/-
Assembly of the oscillatory piece O(T) bound.

Proves: ∫₁ᵀ (MainTerm² - 2·partialMsIntegrand) = O(T)

Strategy (global VdC):
1. Rewrite integrand as 2·Re(oscSum²) via oscPiece_eq_two_re_sq
2. Decompose ∫ oscSum² into pair-indexed global integrals (block decomposition)
3. Bound each pair integral via first-block trivial + global VdC
4. Sum over pairs: O(T)

SORRY COUNT: 1 (norm_integral_oscSum_sq_le_linear)
WARNING COUNT: 1

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.OscPieceIdentities
import Littlewood.Aristotle.Standalone.OscSumSquaredBigO
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.HardyCosSmooth

set_option maxHeartbeats 3200000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.OscPieceBigOAssembly

open scoped Classical
open MeasureTheory Set Real Filter Topology HardyEstimatesPartial Asymptotics
open Aristotle.Standalone.OscPieceIdentities
open Aristotle.Standalone.OscSumSquaredBigO
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
open Aristotle.HardyNProperties
open HardyCosSmooth

/-! ## Helper lemmas -/

/-- hardyStart is monotone. -/
lemma hardyStart_mono {m n : ℕ} (hmn : m ≤ n) : hardyStart m ≤ hardyStart n := by
  rw [hardyStart_formula, hardyStart_formula]; gcongr

/-- Pair product of hardyCosExp is intervalIntegrable on any interval. -/
lemma pair_ii (j l : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => hardyCosExp j t * hardyCosExp l t) volume a b :=
  ((continuous_hardyCosExp_complex j).mul (continuous_hardyCosExp_complex l)).intervalIntegrable _ _

/-- oscSum on block K equals the truncated sum with K+1 terms. -/
lemma oscSum_on_block (K : ℕ) (t : ℝ)
    (ht : hardyStart K ≤ t) (ht' : t < hardyStart (K + 1)) :
    oscSum t = ∑ n ∈ Finset.range (K + 1),
      (((n + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) * hardyCosExp n t := by
  simp only [oscSum, hardyN_constant_on_block K t ht ht']

/-- oscSum agrees with the truncated sum ae on any sub-interval of block K. -/
lemma oscSum_ae_eq_on_block (K : ℕ) (a b : ℝ)
    (ha : hardyStart K ≤ a) (hb : b ≤ hardyStart (K + 1)) (hab : a ≤ b) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b →
      oscSum t = ∑ n ∈ Finset.range (K + 1),
        (((n + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) * hardyCosExp n t := by
  have h_ne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ hardyStart (K + 1) := by
    rw [ae_iff]; simp only [not_not]; exact volume_singleton
  exact h_ne.mono fun t ht htmem => by
    have h_cases := Set.mem_uIoc.mp htmem
    have h_at : a < t := by rcases h_cases with h | h; exact h.1; linarith [h.1, h.2]
    have h_tb : t ≤ b := by rcases h_cases with h | h; exact h.2; linarith [h.1, h.2]
    exact oscSum_on_block K t (ha.trans h_at.le) (lt_of_le_of_ne (h_tb.trans hb) ht)

/-- On a single block, ∫ oscSum² = ∑∑ aⱼaₗ ∫ FⱼFₗ. -/
lemma integral_oscSum_sq_block (K : ℕ) (a b : ℝ)
    (ha : hardyStart K ≤ a) (hb : b ≤ hardyStart (K + 1)) (hab : a ≤ b) :
    ∫ t in a..b, (oscSum t) ^ 2 =
    ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
      (((j + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) * (((l + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
      ∫ t in a..b, hardyCosExp j t * hardyCosExp l t := by
  -- ae-rewrite oscSum(t)² = ∑∑ a_j a_l (F_j F_l)
  have h_ae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b →
      (oscSum t) ^ 2 =
      ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
        (((j + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) * (((l + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        (hardyCosExp j t * hardyCosExp l t) := by
    exact (oscSum_ae_eq_on_block K a b ha hb hab).mono fun t ht htmem => by
      rw [ht htmem, sq, Finset.sum_mul_sum]
      congr 1; ext j; congr 1; ext l; ring
  rw [intervalIntegral.integral_congr_ae h_ae]
  -- Integrability of each weighted pair
  have h_ii : ∀ j l : ℕ, IntervalIntegrable (fun t =>
      (((j + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) * (((l + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
      (hardyCosExp j t * hardyCosExp l t)) volume a b := fun j l =>
    (continuous_const.mul ((continuous_hardyCosExp_complex j).mul
      (continuous_hardyCosExp_complex l))).intervalIntegrable _ _
  -- Distribute ∫ over ∑∑
  rw [intervalIntegral.integral_finset_sum (fun j _ =>
    (continuous_finset_sum _ (fun l _ =>
      continuous_const.mul ((continuous_hardyCosExp_complex j).mul
        (continuous_hardyCosExp_complex l)))).intervalIntegrable _ _)]
  congr 1; ext j
  rw [intervalIntegral.integral_finset_sum (fun l _ => h_ii j l)]
  congr 1; ext l
  rw [intervalIntegral.integral_const_mul]

/-! ## oscSum² integrability on block sequences -/

/-- oscSum² is IntervalIntegrable on any sub-interval of a single block. -/
lemma oscSum_sq_ii_block (K : ℕ) (a b : ℝ)
    (ha : hardyStart K ≤ a) (hb : b ≤ hardyStart (K + 1)) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (oscSum t) ^ 2) volume a b := by
  have h_trunc_ii : IntervalIntegrable (fun t =>
      (∑ n ∈ Finset.range (K + 1),
        (((n + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) * hardyCosExp n t) ^ 2) volume a b := by
    refine ((continuous_finset_sum _ (fun n _ =>
      continuous_const.mul (continuous_hardyCosExp_complex n))).pow 2).intervalIntegrable _ _
  exact h_trunc_ii.congr_ae
    ((ae_restrict_iff' measurableSet_uIoc).mpr
     ((oscSum_ae_eq_on_block K a b ha hb hab).mono fun t ht =>
       fun htmem => by dsimp only; congr 1; exact (ht htmem).symm))

/-- oscSum² is IntervalIntegrable on [hardyStart 0, hardyStart K]. -/
lemma oscSum_sq_ii_prefix (K : ℕ) :
    IntervalIntegrable (fun t => (oscSum t) ^ 2) volume (hardyStart 0) (hardyStart K) := by
  induction K with
  | zero => simp [IntervalIntegrable]
  | succ K ih =>
    exact ih.trans (oscSum_sq_ii_block K (hardyStart K) (hardyStart (K + 1))
      le_rfl le_rfl (hardyStart_mono (by omega)))

/-! ## Block decomposition theorem -/

/-- Inductive step for block decomposition: extend from block K to block K+1. -/
theorem block_decomp_succ (K : ℕ) (T : ℝ)
    (hT : hardyStart (K + 1) ≤ T) (hT_le : T ≤ hardyStart (K + 2))
    (ih : ∫ t in (hardyStart 0)..(hardyStart (K + 1)), (oscSum t) ^ 2 =
      ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
        (((j + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) * (((l + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        ∫ t in (hardyStart (max j l))..(hardyStart (K + 1)),
          hardyCosExp j t * hardyCosExp l t) :
    ∫ t in (hardyStart 0)..T, (oscSum t) ^ 2 =
    ∑ j ∈ Finset.range (K + 2), ∑ l ∈ Finset.range (K + 2),
      (((j + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) * (((l + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
      ∫ t in (hardyStart (max j l))..T, hardyCosExp j t * hardyCosExp l t := by
  -- Split integral at hardyStart (K+1)
  have h_split := intervalIntegral.integral_add_adjacent_intervals
    (oscSum_sq_ii_prefix (K + 1))
    (oscSum_sq_ii_block (K + 1) (hardyStart (K + 1)) T le_rfl hT_le hT)
  rw [← h_split, ih, integral_oscSum_sq_block (K + 1) (hardyStart (K + 1)) T le_rfl hT_le hT]
  -- Vanishing: new pairs have zero integral on [hS(max j l), hS(K+1)]
  have h_van : ∀ j l : ℕ, j < K + 2 → l < K + 2 → K + 1 ≤ max j l →
      (((j+1:ℝ)^(-(1/2:ℝ)):ℝ):ℂ) * (((l+1:ℝ)^(-(1/2:ℝ)):ℝ):ℂ) *
      ∫ t in (hardyStart (max j l))..(hardyStart (K+1)), hardyCosExp j t * hardyCosExp l t = 0 := by
    intro j l _ _ hm
    rw [show max j l = K + 1 from by omega, intervalIntegral.integral_same, mul_zero]
  -- Extend inner sums from range(K+1) to range(K+2)
  have h_ri :
      ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
        (((j+1:ℝ)^(-(1/2:ℝ)):ℝ):ℂ) * (((l+1:ℝ)^(-(1/2:ℝ)):ℝ):ℂ) *
        ∫ t in (hardyStart (max j l))..(hardyStart (K+1)), hardyCosExp j t * hardyCosExp l t =
      ∑ j ∈ Finset.range (K + 2), ∑ l ∈ Finset.range (K + 2),
        (((j+1:ℝ)^(-(1/2:ℝ)):ℝ):ℂ) * (((l+1:ℝ)^(-(1/2:ℝ)):ℝ):ℂ) *
        ∫ t in (hardyStart (max j l))..(hardyStart (K+1)), hardyCosExp j t * hardyCosExp l t := by
    -- First extend inner sums
    have h_step1 :
        ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
          (((j+1:ℝ)^(-(1/2:ℝ)):ℝ):ℂ) * (((l+1:ℝ)^(-(1/2:ℝ)):ℝ):ℂ) *
          ∫ t in (hardyStart (max j l))..(hardyStart (K+1)), hardyCosExp j t * hardyCosExp l t =
        ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 2),
          (((j+1:ℝ)^(-(1/2:ℝ)):ℝ):ℂ) * (((l+1:ℝ)^(-(1/2:ℝ)):ℝ):ℂ) *
          ∫ t in (hardyStart (max j l))..(hardyStart (K+1)), hardyCosExp j t * hardyCosExp l t :=
      Finset.sum_congr rfl fun j hj => by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun l hl hl' => ?_
        have hj' := Finset.mem_range.mp hj
        have hl1 := Finset.mem_range.mp hl
        have hl2 : K + 1 ≤ l := by rwa [Finset.mem_range, not_lt] at hl'
        exact h_van j l (by omega) hl1 (le_trans hl2 (le_max_right j l))
    -- Then extend outer sum
    rw [h_step1]
    exact Finset.sum_subset (Finset.range_mono (by omega)) fun j hj hj' => by
      have hj1 := Finset.mem_range.mp hj
      have hj2 : K + 1 ≤ j := by rwa [Finset.mem_range, not_lt] at hj'
      exact Finset.sum_eq_zero fun l hl => by
        have hl1 := Finset.mem_range.mp hl
        exact h_van j l hj1 hl1 (le_trans hj2 (le_max_left j l))
  rw [h_ri, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j hj
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro l hl
  simp only [Finset.mem_range] at hj hl
  rw [← mul_add]; congr 1
  by_cases hjK : j ≤ K ∧ l ≤ K
  · exact intervalIntegral.integral_add_adjacent_intervals (pair_ii j l _ _) (pair_ii j l _ _)
  · simp only [not_and_or, not_le] at hjK
    rw [show max j l = K + 1 from by omega, intervalIntegral.integral_same, zero_add]

/-- **Block decomposition of ∫ oscSum²**: the integral from hardyStart 0 to T
    (where T is in block K) equals a double sum of pair integrals. -/
theorem block_decomposition_oscSum_sq (K : ℕ) (T : ℝ)
    (hT : hardyStart K ≤ T) (hT_le : T ≤ hardyStart (K + 1)) :
    ∫ t in (hardyStart 0)..T, (oscSum t) ^ 2 =
    ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
      (((j + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) * (((l + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
      ∫ t in (hardyStart (max j l))..T, hardyCosExp j t * hardyCosExp l t := by
  induction K generalizing T with
  | zero =>
    have h := integral_oscSum_sq_block 0 (hardyStart 0) T le_rfl hT_le hT
    refine h.trans ?_
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro l hl
    simp only [Finset.mem_range] at hj hl
    congr 1; congr 1
    show hardyStart 0 = hardyStart (max j l)
    congr 1; omega
  | succ K ih =>
    exact block_decomp_succ K T hT hT_le
      (ih (hardyStart (K + 1)) (hardyStart_mono (Nat.le_succ K)) le_rfl)

/-! ## Pair integral bounds -/

/-- Trivial bound for any pair integral on a single block: ‖∫ FⱼFₗ‖ ≤ block length. -/
lemma pair_integral_trivial_block_bound (j l k : ℕ) :
    ‖∫ t in (hardyStart k)..(hardyStart (k + 1)),
      hardyCosExp j t * hardyCosExp l t‖
    ≤ 2 * Real.pi * (2 * (k : ℝ) + 3) := by
  have hab : hardyStart k ≤ hardyStart (k + 1) := by
    rw [hardyStart_formula, hardyStart_formula]; gcongr; linarith
  calc ‖∫ t in (hardyStart k)..(hardyStart (k + 1)),
        hardyCosExp j t * hardyCosExp l t‖
      ≤ ∫ t in (hardyStart k)..(hardyStart (k + 1)),
        ‖hardyCosExp j t * hardyCosExp l t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in (hardyStart k)..(hardyStart (k + 1)), (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hab
        · exact (((continuous_hardyCosExp_complex j).mul
            (continuous_hardyCosExp_complex l)).norm).intervalIntegrable _ _
        · exact intervalIntegrable_const
        · exact fun t _ => norm_product_hardyCosExp j l t
    _ = hardyStart (k + 1) - hardyStart k := by
        simp [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    _ = 2 * Real.pi * (2 * (k : ℝ) + 3) := block_length k

/-- Global diagonal VdC bound. -/
theorem global_diagonal_vdc_bound :
    ∃ K₂ : ℕ, ∀ j : ℕ, K₂ ≤ j →
      ∀ T : ℝ, hardyStart (j + 1) ≤ T →
        ‖∫ t in (hardyStart (j + 1))..T,
          hardyCosExp j t * hardyCosExp j t‖
            ≤ 3 / Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) := by
  obtain ⟨K₀, hK₀⟩ := productOmega_lower_bound_eventually
  refine ⟨K₀, fun j hj T hT => ?_⟩
  have hj1_pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hj2_pos : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have hratio_gt : 1 < ((j : ℝ) + 2) / ((j : ℝ) + 1) := by
    rw [one_lt_div hj1_pos]; linarith
  have hlog_pos : 0 < Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) :=
    Real.log_pos hratio_gt
  have hjj1 : j < j + 1 := Nat.lt_succ_self j
  set m := Real.log (((j : ℝ) + 2) ^ 2 / (((j : ℝ) + 1) * ((j : ℝ) + 1))) / 2 with hm_def
  have hm_pos : 0 < m := by
    rw [hm_def]; apply div_pos
    · apply Real.log_pos; rw [one_lt_div (by positivity)]; nlinarith
    · norm_num
  have ha_pos : 0 < hardyStart (j + 1) := by rw [hardyStart_formula]; positivity
  have hω_lower : ∀ t ∈ Set.Icc (hardyStart (j + 1)) T,
      m ≤ productOmega j j t := by
    intro t ⟨ht_lo, _⟩
    have hhs_le : hardyStart (j + 1) ≤ hardyStart (j + 1 + 1) := by
      rw [hardyStart_formula, hardyStart_formula]; gcongr
    have hbase := hK₀ (j + 1) (by omega : K₀ ≤ j + 1) j j hjj1 hjj1
      (hardyStart (j + 1)) le_rfl hhs_le
    have hcast : ((j + 1 : ℕ) + 1 : ℝ) = (j : ℝ) + 2 := by push_cast; ring
    rw [show (↑(j + 1) + 1 : ℝ) = (↑j + 2 : ℝ) from hcast] at hbase
    exact le_trans hbase (productOmega_le_of_le j j _ t ha_pos ht_lo)
  have h_bound := Aristotle.ComplexVdC.complex_vdc_angular
    (fun t => hardyCosExp j t * hardyCosExp j t) (productOmega j j)
    (hardyStart (j + 1)) T m hT hm_pos
    (fun t _ht => product_angular_velocity j j t)
    (fun t _ht => norm_product_hardyCosExp j j t)
    (differentiable_productOmega j j)
    (continuous_deriv_productOmega j j)
    hω_lower
    (fun t ht => deriv_productOmega_nonneg j j t (lt_of_lt_of_le ha_pos ht.1))
  have h_ratio_eq : ((j : ℝ) + 2) ^ 2 / (((j : ℝ) + 1) * ((j : ℝ) + 1)) =
      (((j : ℝ) + 2) / ((j : ℝ) + 1)) ^ 2 := by field_simp
  calc ‖∫ t in (hardyStart (j + 1))..T,
          hardyCosExp j t * hardyCosExp j t‖
      ≤ 3 / m := h_bound
    _ = 6 / Real.log (((j : ℝ) + 2) ^ 2 / (((j : ℝ) + 1) * ((j : ℝ) + 1))) := by
        rw [hm_def]; ring
    _ = 6 / (2 * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) := by
        rw [h_ratio_eq, Real.log_pow]; ring
    _ = 3 / Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) := by
        rw [show (6 : ℝ) / (2 * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) =
          3 / Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) from by ring]

/-! ## Main theorem infrastructure -/

/-- Block index exists for T ≥ hardyStart 0. -/
lemma exists_block_of_ge_hardyStart0 (T : ℝ) (hT : hardyStart 0 ≤ T) :
    ∃ K : ℕ, hardyStart K ≤ T ∧ T ≤ hardyStart (K + 1) := by
  have hT_nn : (0 : ℝ) ≤ T := le_trans (by rw [hardyStart_formula]; positivity) hT
  set N := hardyN T with hN_def
  have hN_pos : 0 < N := by
    rw [hN_def]; exact (hardyN_lt_iff 0 T hT_nn).mpr hT
  refine ⟨N - 1, ?_, ?_⟩
  · exact (hardyN_lt_iff (N - 1) T hT_nn).mp (by omega)
  · by_contra h_not
    push_neg at h_not
    have : N < hardyN T := (hardyN_lt_iff N T hT_nn).mpr (by
      have := hardyStart_mono (show N ≤ N - 1 + 1 from by omega)
      linarith)
    omega

/-- (K+1)² ≤ T/(2π) when hardyStart K ≤ T. -/
lemma block_index_sq_le (K : ℕ) (T : ℝ) (hT : hardyStart K ≤ T) :
    ((K + 1 : ℝ)) ^ 2 ≤ T / (2 * Real.pi) := by
  rw [hardyStart_formula] at hT
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  rw [le_div_iff₀ hpi]
  nlinarith

/-- oscSum = 0 for t < hardyStart 0 (since hardyN t = 0, empty sum). -/
lemma oscSum_eq_zero_of_lt_hardyStart0 (t : ℝ) (ht : t < hardyStart 0) :
    oscSum t = 0 := by
  unfold oscSum
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have h_hS0_pos : (0:ℝ) < hardyStart 0 := by rw [hardyStart_formula]; positivity
  have h_div : t / (2 * Real.pi) < 1 := by
    rw [hardyStart_formula] at ht; rw [div_lt_one hpi]
    push_cast at ht; linarith
  have h_sqrt_lt : Real.sqrt (t / (2 * Real.pi)) < 1 := by
    rw [Real.sqrt_lt' one_pos]; norm_num; exact h_div
  have : hardyN t = 0 := by
    simp only [hardyN]; exact Nat.floor_eq_zero.mpr h_sqrt_lt
  rw [this]; simp

/-- oscSum² is IntervalIntegrable on [1, T] for T in block K. -/
lemma oscSum_sq_ii_one_T (K : ℕ) (T : ℝ)
    (hT : hardyStart K ≤ T) (hT_le : T ≤ hardyStart (K + 1)) :
    IntervalIntegrable (fun t => (oscSum t) ^ 2) volume 1 T := by
  have h_hS0 : (1 : ℝ) ≤ hardyStart 0 := by
    rw [hardyStart_formula]; push_cast; nlinarith [pi_gt_three]
  have h_init : IntervalIntegrable (fun t => (oscSum t) ^ 2) volume 1 (hardyStart 0) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h_hS0]
    rw [integrableOn_Ioc_iff_integrableOn_Ioo' (by simp [Real.volume_singleton])]
    exact IntegrableOn.congr_fun integrableOn_zero
      (fun t ht => by simp [oscSum_eq_zero_of_lt_hardyStart0 t ht.2])
      measurableSet_Ioo
  exact h_init.trans ((oscSum_sq_ii_prefix K).trans
    (oscSum_sq_ii_block K (hardyStart K) T le_rfl hT_le hT))

/-! ## Pair integral trivial bounds -/

/-- Trivial bound: norm of any pair integral over [a, T] is ≤ T
    when a ≥ 0 and integrand has norm ≤ 1. -/
lemma norm_pair_integral_le_T (j l : ℕ) (a T : ℝ) (ha : 0 ≤ a) (haT : a ≤ T) :
    ‖∫ t in a..T, hardyCosExp j t * hardyCosExp l t‖ ≤ T := by
  calc ‖∫ t in a..T, hardyCosExp j t * hardyCosExp l t‖
      ≤ ∫ t in a..T, ‖hardyCosExp j t * hardyCosExp l t‖ :=
        intervalIntegral.norm_integral_le_integral_norm haT
    _ ≤ ∫ t in a..T, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on haT
        · exact (((continuous_hardyCosExp_complex j).mul
            (continuous_hardyCosExp_complex l)).norm).intervalIntegrable _ _
        · exact intervalIntegrable_const
        · exact fun t _ => norm_product_hardyCosExp j l t
    _ = T - a := by simp [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    _ ≤ T := by linarith

/-! ## Key norm bound -/

/-- ∫₁ᵀ oscSum² = ∫_{hS 0}^T oscSum² since oscSum vanishes on [1, hS 0]. -/
lemma integral_oscSum_sq_from_one (K : ℕ) (T : ℝ)
    (hT : hardyStart K ≤ T) (hT' : T ≤ hardyStart (K + 1)) :
    ∫ t in (1:ℝ)..T, (oscSum t) ^ 2 =
    ∫ t in (hardyStart 0)..T, (oscSum t) ^ 2 := by
  have h_hS0 : (1 : ℝ) ≤ hardyStart 0 := by
    rw [hardyStart_formula]; push_cast; nlinarith [pi_gt_three]
  -- Integrability on [1, hS 0] (reuse from oscSum_sq_ii_one_T construction)
  have h_ii_init : IntervalIntegrable (fun t => (oscSum t) ^ 2) volume 1 (hardyStart 0) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h_hS0]
    rw [integrableOn_Ioc_iff_integrableOn_Ioo' (by simp [Real.volume_singleton])]
    exact IntegrableOn.congr_fun integrableOn_zero
      (fun t ht => by simp [oscSum_eq_zero_of_lt_hardyStart0 t ht.2])
      measurableSet_Ioo
  have h_ii_rest : IntervalIntegrable (fun t => (oscSum t) ^ 2) volume (hardyStart 0) T :=
    (oscSum_sq_ii_prefix K).trans (oscSum_sq_ii_block K (hardyStart K) T le_rfl hT' hT)
  -- ∫₁^{hS 0} oscSum² = 0 since oscSum = 0 ae on (1, hS 0)
  have h_init_zero : ∫ t in (1:ℝ)..(hardyStart 0), (oscSum t) ^ 2 = 0 := by
    have h_ae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc 1 (hardyStart 0) →
        (oscSum t) ^ 2 = (0 : ℂ) := by
      have h_ne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ hardyStart 0 := by
        rw [ae_iff]; simp only [not_not]; exact volume_singleton
      exact h_ne.mono fun t ht htmem => by
        rw [Set.uIoc_of_le h_hS0] at htmem
        simp [oscSum_eq_zero_of_lt_hardyStart0 t (lt_of_le_of_ne htmem.2 ht)]
    rw [intervalIntegral.integral_congr_ae h_ae, intervalIntegral.integral_zero]
  -- Split: ∫₁ᵀ = ∫₁^{hS 0} + ∫_{hS 0}^T, first part = 0
  rw [← intervalIntegral.integral_add_adjacent_intervals h_ii_init h_ii_rest,
      h_init_zero, zero_add]

/-- The norm of a weighted complex Finset double sum is bounded by the
    sum of norms times absolute weights. -/
lemma norm_weighted_double_sum_le (N : ℕ) (a : ℕ → ℝ) (I : ℕ → ℕ → ℂ)
    (ha : ∀ j, 0 ≤ a j) :
    ‖∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
      (a j : ℂ) * (a l : ℂ) * I j l‖ ≤
    ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
      a j * a l * ‖I j l‖ := by
  calc ‖∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        (a j : ℂ) * (a l : ℂ) * I j l‖
      ≤ ∑ j ∈ Finset.range N, ‖∑ l ∈ Finset.range N,
          (a j : ℂ) * (a l : ℂ) * I j l‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          ‖(a j : ℂ) * (a l : ℂ) * I j l‖ := by
        gcongr with j; exact norm_sum_le _ _
    _ = ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          a j * a l * ‖I j l‖ := by
        congr 1; ext j; congr 1; ext l
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg (ha j), Real.norm_of_nonneg (ha l)]

/-- Inverse square root sum bound (local copy since OscSumSquaredBigO's is private). -/
lemma sum_inv_sqrt_le (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k : ℝ) + 1) ^ (-(1:ℝ)/2) ≤ 2 * Real.sqrt ↑N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h_rpow : ((n : ℝ) + 1) ^ (-(1:ℝ)/2) = 1 / Real.sqrt ((n : ℝ) + 1) := by
      rw [show -(1:ℝ)/2 = -((1:ℝ)/2) from by ring, Real.rpow_neg (le_of_lt hn1_pos),
          ← Real.sqrt_eq_rpow]; simp [one_div]
    rw [h_rpow]
    have h_sqrt_pos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hn1_pos
    have h_prod : (Real.sqrt (↑n + 1) - Real.sqrt ↑n) *
        (Real.sqrt (↑n + 1) + Real.sqrt ↑n) = 1 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ ↑n + 1 by positivity),
                 Real.sq_sqrt (show (0:ℝ) ≤ (↑n : ℝ) by positivity),
                 sq_nonneg (Real.sqrt (↑n + 1)), sq_nonneg (Real.sqrt ↑n)]
    have h_key : 1 / Real.sqrt ((n : ℝ) + 1) ≤
        2 * (Real.sqrt (↑n + 1) - Real.sqrt ↑n) := by
      rw [div_le_iff₀ h_sqrt_pos]
      have h_diff_nn : 0 ≤ Real.sqrt (↑n + 1) - Real.sqrt ↑n := by
        linarith [Real.sqrt_le_sqrt (show (↑n : ℝ) ≤ ↑n + 1 by linarith)]
      calc 1 = (Real.sqrt (↑n + 1) - Real.sqrt ↑n) *
                (Real.sqrt (↑n + 1) + Real.sqrt ↑n) := h_prod.symm
        _ ≤ (Real.sqrt (↑n + 1) - Real.sqrt ↑n) *
              (2 * Real.sqrt (↑n + 1)) := by
            exact mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg (↑n : ℝ)]) h_diff_nn
        _ = 2 * (Real.sqrt (↑n + 1) - Real.sqrt ↑n) * Real.sqrt (↑n + 1) := by ring
    have h_cast : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
    rw [h_cast]; linarith

/-- Norm of pair integral ≤ T - hS(m), i.e. length of the interval. -/
lemma norm_pair_integral_le_diff (j l : ℕ) (a T : ℝ) (haT : a ≤ T) :
    ‖∫ t in a..T, hardyCosExp j t * hardyCosExp l t‖ ≤ T - a := by
  calc ‖∫ t in a..T, hardyCosExp j t * hardyCosExp l t‖
      ≤ ∫ t in a..T, ‖hardyCosExp j t * hardyCosExp l t‖ :=
        intervalIntegral.norm_integral_le_integral_norm haT
    _ ≤ ∫ t in a..T, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on haT
        · exact (((continuous_hardyCosExp_complex j).mul
            (continuous_hardyCosExp_complex l)).norm).intervalIntegrable _ _
        · exact intervalIntegrable_const
        · exact fun t _ => norm_product_hardyCosExp j l t
    _ = T - a := by simp [intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- Sum of block lengths: ∑_{m=0}^{K} block_length(m) = hS(K+1) - hS(0). -/
lemma sum_block_lengths (K : ℕ) :
    ∑ m ∈ Finset.range (K + 1), (hardyStart (m + 1) - hardyStart m) =
    hardyStart (K + 1) - hardyStart 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]; ring

/-- Block lengths are increasing: BL(m) ≤ BL(K) for m ≤ K. -/
lemma block_length_le_block_length {m K : ℕ} (hm : m ≤ K) :
    hardyStart (m + 1) - hardyStart m ≤ hardyStart (K + 1) - hardyStart K := by
  have hm_le : (m : ℝ) ≤ (K : ℝ) := Nat.cast_le.mpr hm
  have := block_length m; have := block_length K; nlinarith [Real.pi_pos]

/-- BL(K) ≤ 6π(K+1). -/
lemma block_length_le_six_pi (K : ℕ) :
    hardyStart (K + 1) - hardyStart K ≤ 6 * Real.pi * ((K : ℝ) + 1) := by
  have := block_length K
  have hpi := Real.pi_pos
  have hK := Nat.cast_nonneg (α := ℝ) K
  nlinarith

/-- Diagonal VdC per-term bound: a_j² · 3/log((j+2)/(j+1)) ≤ 6.
    Uses log(r) ≥ 1 - 1/r (from exp bound), giving log((j+2)/(j+1)) ≥ 1/(j+2). -/
lemma diag_vdc_term_le_six (j : ℕ) :
    ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) * ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) *
    (3 / Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) ≤ 6 := by
  have hj1_pos : (0 : ℝ) < (j + 1 : ℝ) := by positivity
  have hj2_pos : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  -- a² = (j+1)⁻¹
  have ha : ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) * ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) =
      ((j + 1 : ℝ))⁻¹ := by
    rw [← Real.rpow_add hj1_pos]; norm_num; rw [Real.rpow_neg_one]
  -- log ≥ (j+2)⁻¹
  have hlog_lower : ((j : ℝ) + 2)⁻¹ ≤ Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) := by
    have h_exp := Real.add_one_le_exp (-Real.log (((j:ℝ) + 2) / ((j:ℝ) + 1)))
    rw [Real.exp_neg, Real.exp_log (div_pos hj2_pos (by linarith : (0:ℝ) < (j:ℝ)+1)),
        inv_div] at h_exp
    have h_sub : 1 - ((j:ℝ) + 1) / ((j:ℝ) + 2) = ((j:ℝ) + 2)⁻¹ := by field_simp; ring
    linarith
  have hlog_pos : 0 < Real.log (((j:ℝ) + 2) / ((j:ℝ) + 1)) :=
    lt_of_lt_of_le (by positivity) hlog_lower
  rw [ha, inv_mul_le_iff₀ hj1_pos, div_le_iff₀ hlog_pos]
  -- Goal: 3 ≤ (↑j+1) * 6 * log(...)
  calc (3 : ℝ) ≤ 6 * ((j:ℝ) + 1) / ((j:ℝ) + 2) := by
        rw [le_div_iff₀ hj2_pos]; nlinarith [Nat.cast_nonneg (α := ℝ) j]
    _ = 6 * ((j:ℝ) + 1) * ((j:ℝ) + 2)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ 6 * ((j:ℝ) + 1) * Real.log (((j:ℝ) + 2) / ((j:ℝ) + 1)) := by gcongr
    _ = (↑j + 1) * 6 * Real.log ((↑j + 2) / (↑j + 1)) := by ring

/-- For off-diagonal pairs, the VdC log ratio is larger:
    log((l+2)²/((j+1)(l+1))) ≥ log((l+1)/(j+1)). -/
lemma vdc_log_ratio_ge (j l : ℕ) (hjl : j < l) :
    Real.log (((l : ℝ) + 1) / ((j : ℝ) + 1)) ≤
    Real.log (((l : ℝ) + 2) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) := by
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hl1 : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  apply Real.log_le_log (div_pos hl1 hj1)
  -- (l+1)/(j+1) ≤ (l+2)²/((j+1)(l+1)) ⟺ (l+1)² ≤ (l+2)²
  rw [div_le_div_iff₀ hj1 (mul_pos hj1 hl1)]
  -- Goal: (l+1) * ((j+1)*(l+1)) ≤ (l+2)^2 * (j+1)
  have : ((l : ℝ) + 1) ^ 2 ≤ ((l : ℝ) + 2) ^ 2 :=
    sq_le_sq' (by nlinarith) (by linarith)
  nlinarith

/-- Off-diagonal VdC constant comparison:
    6/log((l+2)²/((j+1)(l+1))) ≤ 6/log((l+1)/(j+1)). -/
lemma vdc_off_diag_const_le (j l : ℕ) (hjl : j < l) :
    6 / Real.log (((l : ℝ) + 2) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) ≤
    6 / Real.log (((l : ℝ) + 1) / ((j : ℝ) + 1)) := by
  have hlog_pos : 0 < Real.log (((l : ℝ) + 1) / ((j : ℝ) + 1)) :=
    Real.log_pos (by rw [one_lt_div (by positivity)]; exact_mod_cast Nat.succ_lt_succ hjl)
  exact div_le_div_of_nonneg_left (le_of_lt (by norm_num : (0:ℝ) < 6))
    hlog_pos (vdc_log_ratio_ge j l hjl)

/-- log(n+2) ≤ n+1 for all n : ℕ. From exp(n+1) ≥ 1+(n+1) ≥ n+2. -/
lemma log_le_nat (n : ℕ) : Real.log ((n : ℝ) + 2) ≤ (n : ℝ) + 1 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have := Real.add_one_le_exp ((n : ℝ) + 1)
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Integral splitting at block boundary: for j < l ≤ K with hS(K) ≤ T,
    the pair integral from hS(l) splits into first-block + tail. -/
lemma pair_integral_split (j l K : ℕ) (T : ℝ)
    (hjl : j < l) (hlK : l < K) (hT : hardyStart K ≤ T) :
    ‖∫ t in (hardyStart l)..T, hardyCosExp j t * hardyCosExp l t‖ ≤
    (hardyStart (l + 1) - hardyStart l) +
    ‖∫ t in (hardyStart (l + 1))..T, hardyCosExp j t * hardyCosExp l t‖ := by
  have hl1_le_T : hardyStart (l + 1) ≤ T :=
    (hardyStart_mono (by omega : l + 1 ≤ K)).trans hT
  have hl_le_l1 : hardyStart l ≤ hardyStart (l + 1) := hardyStart_mono (by omega)
  have h_split := intervalIntegral.integral_add_adjacent_intervals
    (pair_ii j l (hardyStart l) (hardyStart (l + 1)))
    (pair_ii j l (hardyStart (l + 1)) T)
  calc ‖∫ t in (hardyStart l)..T, hardyCosExp j t * hardyCosExp l t‖
      = ‖(∫ t in (hardyStart l)..(hardyStart (l + 1)), hardyCosExp j t * hardyCosExp l t) +
        (∫ t in (hardyStart (l + 1))..T, hardyCosExp j t * hardyCosExp l t)‖ := by
        congr 1; exact h_split.symm
    _ ≤ ‖∫ t in (hardyStart l)..(hardyStart (l + 1)), hardyCosExp j t * hardyCosExp l t‖ +
        ‖∫ t in (hardyStart (l + 1))..T, hardyCosExp j t * hardyCosExp l t‖ :=
        norm_add_le _ _
    _ ≤ (hardyStart (l + 1) - hardyStart l) +
        ‖∫ t in (hardyStart (l + 1))..T, hardyCosExp j t * hardyCosExp l t‖ := by
        gcongr; exact norm_pair_integral_le_diff j l _ _ hl_le_l1

/-- Diagonal integral splitting at block boundary. -/
lemma diag_integral_split (j K : ℕ) (T : ℝ)
    (hjK : j < K) (hT : hardyStart K ≤ T) :
    ‖∫ t in (hardyStart j)..T, hardyCosExp j t * hardyCosExp j t‖ ≤
    (hardyStart (j + 1) - hardyStart j) +
    ‖∫ t in (hardyStart (j + 1))..T, hardyCosExp j t * hardyCosExp j t‖ := by
  have hj1_le_T : hardyStart (j + 1) ≤ T := (hardyStart_mono (by omega : j + 1 ≤ K)).trans hT
  have hj_le_j1 : hardyStart j ≤ hardyStart (j + 1) := hardyStart_mono (by omega)
  have h_split := intervalIntegral.integral_add_adjacent_intervals
    (pair_ii j j (hardyStart j) (hardyStart (j + 1)))
    (pair_ii j j (hardyStart (j + 1)) T)
  calc ‖∫ t in (hardyStart j)..T, hardyCosExp j t * hardyCosExp j t‖
      = ‖(∫ t in (hardyStart j)..(hardyStart (j + 1)), hardyCosExp j t * hardyCosExp j t) +
        (∫ t in (hardyStart (j + 1))..T, hardyCosExp j t * hardyCosExp j t)‖ := by
        congr 1; exact h_split.symm
    _ ≤ ‖∫ t in (hardyStart j)..(hardyStart (j + 1)), hardyCosExp j t * hardyCosExp j t‖ +
        ‖∫ t in (hardyStart (j + 1))..T, hardyCosExp j t * hardyCosExp j t‖ :=
        norm_add_le _ _
    _ ≤ (hardyStart (j + 1) - hardyStart j) +
        ‖∫ t in (hardyStart (j + 1))..T, hardyCosExp j t * hardyCosExp j t‖ := by
        gcongr; exact norm_pair_integral_le_diff j j _ _ hj_le_j1

/-- Per-pair bound for diagonal with VdC: a_j² · ‖∫_{hS j}^T‖ ≤ 6π + 6 when j < K, K₂ ≤ j. -/
lemma diag_pair_vdc_bound (K₂ : ℕ)
    (hK₂ : ∀ j : ℕ, K₂ ≤ j → ∀ T : ℝ, hardyStart (j + 1) ≤ T →
      ‖∫ t in (hardyStart (j + 1))..T, hardyCosExp j t * hardyCosExp j t‖ ≤
      3 / Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)))
    (j K : ℕ) (T : ℝ) (hjK : j < K) (hK₂j : K₂ ≤ j)
    (hT : hardyStart K ≤ T) :
    ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) * ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) *
    ‖∫ t in (hardyStart j)..T, hardyCosExp j t * hardyCosExp j t‖ ≤ 30 := by
  have hj1_pos : (0 : ℝ) < (j + 1 : ℝ) := by positivity
  -- a² = (j+1)⁻¹
  have ha : ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) * ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) =
      ((j + 1 : ℝ))⁻¹ := by
    rw [← Real.rpow_add hj1_pos]; norm_num; rw [Real.rpow_neg_one]
  -- Split integral at hS(j+1)
  have h_split := diag_integral_split j K T hjK hT
  have hj1_le_T : hardyStart (j + 1) ≤ T := (hardyStart_mono (by omega : j + 1 ≤ K)).trans hT
  -- VdC tail bound
  have h_vdc := hK₂ j hK₂j T hj1_le_T
  -- BL(j) ≤ 6π(j+1)
  have h_bl := block_length_le_six_pi j
  calc ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) * ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) *
        ‖∫ t in (hardyStart j)..T, hardyCosExp j t * hardyCosExp j t‖
      ≤ (j + 1 : ℝ)⁻¹ * ((hardyStart (j + 1) - hardyStart j) +
        3 / Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) := by
        rw [ha]; gcongr; linarith
    _ = (j + 1 : ℝ)⁻¹ * (hardyStart (j + 1) - hardyStart j) +
        (j + 1 : ℝ)⁻¹ * (3 / Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) := by ring
    _ ≤ 6 * Real.pi + 6 := by
        have h1 : (j + 1 : ℝ)⁻¹ * (hardyStart (j + 1) - hardyStart j) ≤ 6 * Real.pi := by
          rw [inv_mul_le_iff₀ hj1_pos]; linarith
        have h2 : (j + 1 : ℝ)⁻¹ * (3 / Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) ≤ 6 := by
          rw [← ha]; exact diag_vdc_term_le_six j
        linarith
    _ ≤ 30 := by nlinarith [Real.pi_lt_four]

/-- Weighted double sum with VdC: the full ∑∑ bound for Case 2 (K ≥ K₀).
    Bound: ≤ (4K₀ + 2C_off + 17)T. -/
lemma vdc_double_sum_bound
    (K₁ K₂ : ℕ)
    (hK₁ : ∀ j l : ℕ, j < l → K₁ ≤ l → ∀ T : ℝ, hardyStart (l + 1) ≤ T →
      ‖∫ t in (hardyStart (l + 1))..T, hardyCosExp j t * hardyCosExp l t‖ ≤
      6 / Real.log (((l : ℝ) + 2) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))))
    (hK₂ : ∀ j : ℕ, K₂ ≤ j → ∀ T : ℝ, hardyStart (j + 1) ≤ T →
      ‖∫ t in (hardyStart (j + 1))..T, hardyCosExp j t * hardyCosExp j t‖ ≤
      3 / Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)))
    (C_off : ℝ) (hC_off_pos : 0 < C_off)
    (hC_off : ∀ N : ℕ, 1 ≤ N →
      ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 < p.2),
        ((p.1 + 1 : ℝ) ^ (-(1:ℝ)/2)) * ((p.2 + 1 : ℝ) ^ (-(1:ℝ)/2)) /
          Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1))
      ≤ C_off * (N : ℝ) * Real.log ((N : ℝ) + 1))
    (K₀ : ℕ) (hK₀ : K₀ = max K₁ K₂)
    (K : ℕ) (T : ℝ) (hT : hardyStart K ≤ T) (hT' : T ≤ hardyStart (K + 1))
    (hK₀_le_K : K₀ ≤ K) :
    ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
      ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) * ((l + 1 : ℝ) ^ (-(1/2 : ℝ))) *
      ‖∫ t in (hardyStart (max j l))..T, hardyCosExp j t * hardyCosExp l t‖
    ≤ (4 * ↑K₀ + 2 * C_off + 17) * T := by
  have hT_pos : (0 : ℝ) < T := lt_of_lt_of_le (by rw [hardyStart_formula]; positivity) hT
  have hKsq := block_index_sq_le K T hT
  have hK1_pos : (0 : ℝ) < (↑K + 1 : ℝ) := by positivity
  have hK1_le_T2pi : (↑K + 1 : ℝ) ≤ T / (2 * Real.pi) := by nlinarith
  have hBL := block_length_le_six_pi K
  have hpi := Real.pi_pos
  have hK₁_le_K₀ : K₁ ≤ K₀ := by rw [hK₀]; exact le_max_left _ _
  have hK₂_le_K₀ : K₂ ≤ K₀ := by rw [hK₀]; exact le_max_right _ _
  -- Abbreviation for weights
  set a := fun j : ℕ => ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) with ha_def
  -- nonneg helper
  have hg_nn : ∀ (j l : ℕ), 0 ≤ a j * a l *
      ‖∫ t in (hardyStart (max j l))..T, hardyCosExp j t * hardyCosExp l t‖ :=
    fun j l => mul_nonneg (mul_nonneg (by positivity) (by positivity)) (norm_nonneg _)
  -- hS(K+1) ≤ 4T
  have hS_le_4T : hardyStart (K + 1) ≤ 4 * T := by
    have : hardyStart (K + 1) ≤ 4 * hardyStart K := by
      simp only [hardyStart_formula]; push_cast
      nlinarith [hpi, Nat.cast_nonneg (α := ℝ) K]
    linarith
  -- Convert double sum to product sum and split by max < K₀
  set S := Finset.range (K + 1) ×ˢ Finset.range (K + 1)
  rw [show ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
      a j * a l * ‖∫ t in (hardyStart (max j l))..T, hardyCosExp j t * hardyCosExp l t‖ =
      ∑ p ∈ S, a p.1 * a p.2 *
      ‖∫ t in (hardyStart (max p.1 p.2))..T, hardyCosExp p.1 t * hardyCosExp p.2 t‖
    from (Finset.sum_product' _ _ _).symm]
  -- Split: small (max < K₀) + large (max ≥ K₀)
  calc ∑ p ∈ S, a p.1 * a p.2 *
        ‖∫ t in (hardyStart (max p.1 p.2))..T, hardyCosExp p.1 t * hardyCosExp p.2 t‖
      = (∑ p ∈ S.filter (fun p => max p.1 p.2 < K₀), a p.1 * a p.2 *
          ‖∫ t in (hardyStart (max p.1 p.2))..T, hardyCosExp p.1 t * hardyCosExp p.2 t‖) +
        (∑ p ∈ S.filter (fun p => ¬ (max p.1 p.2 < K₀)), a p.1 * a p.2 *
          ‖∫ t in (hardyStart (max p.1 p.2))..T, hardyCosExp p.1 t * hardyCosExp p.2 t‖) :=
        (Finset.sum_filter_add_sum_filter_not S (fun p => max p.1 p.2 < K₀) _).symm
    _ ≤ 4 * ↑K₀ * T + (2 * C_off + 17) * T := by
        apply add_le_add
        · -- SMALL PAIRS: max < K₀ implies j,l < K₀, trivial bound ≤ 4K₀T
          calc ∑ p ∈ S.filter (fun p => max p.1 p.2 < K₀), a p.1 * a p.2 *
                ‖∫ t in (hardyStart (max p.1 p.2))..T, hardyCosExp p.1 t * hardyCosExp p.2 t‖
              ≤ ∑ p ∈ S.filter (fun p => max p.1 p.2 < K₀), a p.1 * a p.2 * T := by
                apply Finset.sum_le_sum; intro p hp
                gcongr
                have ⟨hp_S, _⟩ := Finset.mem_filter.mp hp
                have ⟨hj, hl⟩ := Finset.mem_product.mp hp_S
                exact norm_pair_integral_le_T p.1 p.2 _ T
                  (by rw [hardyStart_formula]; positivity)
                  ((hardyStart_mono (show max p.1 p.2 ≤ K by omega)).trans hT)
            _ ≤ ∑ p ∈ Finset.range K₀ ×ˢ Finset.range K₀, a p.1 * a p.2 * T := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro p hp
                  have ⟨_, hp_max⟩ := Finset.mem_filter.mp hp
                  rw [Finset.mem_product]
                  exact ⟨Finset.mem_range.mpr (lt_of_le_of_lt (le_max_left _ _) hp_max),
                         Finset.mem_range.mpr (lt_of_le_of_lt (le_max_right _ _) hp_max)⟩
                · intro p _ _; exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
                    (le_of_lt hT_pos)
            _ = T * (∑ j ∈ Finset.range K₀, a j) ^ 2 := by
                trans (T * ∑ j ∈ Finset.range K₀, ∑ l ∈ Finset.range K₀, a j * a l)
                · rw [Finset.mul_sum]; rw [show
                    ∑ p ∈ Finset.range K₀ ×ˢ Finset.range K₀, a p.1 * a p.2 * T =
                    ∑ j ∈ Finset.range K₀, ∑ l ∈ Finset.range K₀, T * (a j * a l) from by
                      rw [← Finset.sum_product']
                      congr 1; ext p; simp only [mul_comm T, mul_assoc]]
                  congr 1; ext j; rw [Finset.mul_sum]
                · congr 1; rw [sq, Finset.sum_mul]; congr 1; ext j; rw [Finset.mul_sum]
            _ ≤ T * (4 * ↑K₀) := by
                gcongr
                calc (∑ j ∈ Finset.range K₀, a j) ^ 2
                    ≤ (2 * Real.sqrt ↑K₀) ^ 2 := by
                      apply sq_le_sq'
                      · linarith [Real.sqrt_nonneg (↑K₀ : ℝ),
                          Finset.sum_nonneg (fun j (_ : j ∈ Finset.range K₀) =>
                            show (0:ℝ) ≤ a j from by positivity)]
                      · have : ∀ j, a j = ((j : ℝ) + 1) ^ (-(1:ℝ)/2) := fun j => by
                          simp only [ha_def]; norm_num
                        simp_rw [this]; exact sum_inv_sqrt_le K₀
                  _ = 4 * ↑K₀ := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
            _ = 4 * ↑K₀ * T := by ring
        · -- LARGE PAIRS: max ≥ K₀. Split into diagonal and off-diagonal.
          -- Further split: diag (p.1 = p.2) + offdiag (p.1 ≠ p.2)
          set large := S.filter (fun p => ¬ (max p.1 p.2 < K₀))
          calc ∑ p ∈ large, a p.1 * a p.2 *
                ‖∫ t in (hardyStart (max p.1 p.2))..T, hardyCosExp p.1 t * hardyCosExp p.2 t‖
              = (∑ p ∈ large.filter (fun p => p.1 = p.2), a p.1 * a p.2 *
                  ‖∫ t in (hardyStart (max p.1 p.2))..T, hardyCosExp p.1 t * hardyCosExp p.2 t‖) +
                (∑ p ∈ large.filter (fun p => ¬ (p.1 = p.2)), a p.1 * a p.2 *
                  ‖∫ t in (hardyStart (max p.1 p.2))..T, hardyCosExp p.1 t * hardyCosExp p.2 t‖) :=
                (Finset.sum_filter_add_sum_filter_not large (fun p => p.1 = p.2) _).symm
            _ ≤ 5 * T + (2 * C_off + 12) * T := by
                apply add_le_add
                · -- DIAGONAL: j = l ≥ K₀. Each term ≤ 30, count ≤ K+1, so ≤ 30(K+1) ≤ 5T
                  have h_diag_per_pair : ∀ q : ℕ × ℕ, q ∈ large.filter (fun p => p.1 = p.2) →
                      a q.1 * a q.2 *
                      ‖∫ t in (hardyStart (max q.1 q.2))..T,
                        hardyCosExp q.1 t * hardyCosExp q.2 t‖ ≤ 30 := by
                    intro q hq
                    have hq_mem := Finset.mem_filter.mp hq
                    have hq_large_mem := Finset.mem_filter.mp hq_mem.1
                    have hq_S := Finset.mem_product.mp hq_large_mem.1
                    have hj : q.1 < K + 1 := Finset.mem_range.mp hq_S.1
                    have hq_eq : q.1 = q.2 := hq_mem.2
                    have hq_ge : K₀ ≤ q.1 := by
                      rw [hq_eq, max_self] at hq_large_mem; omega
                    rw [show q.2 = q.1 from hq_eq.symm, max_self]
                    have hK₂_le : K₂ ≤ q.1 := le_trans hK₂_le_K₀ hq_ge
                    simp only [ha_def]
                    by_cases hjK : q.1 < K
                    · convert diag_pair_vdc_bound K₂ hK₂ q.1 K T hjK hK₂_le hT using 2
                    · have hqK : q.1 = K := by omega
                      rw [hqK]
                      have ha_sq : ((↑K + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * ((↑K + 1 : ℝ) ^ (-(1 / 2 : ℝ))) = ((K + 1 : ℝ))⁻¹ := by
                        rw [← Real.rpow_add (by positivity : (0:ℝ) < (↑K + 1))]; norm_num
                        rw [Real.rpow_neg_one]
                      calc ((↑K + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * ((↑K + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
                              ‖∫ t in (hardyStart K)..T, hardyCosExp K t * hardyCosExp K t‖
                          ≤ ((K + 1 : ℝ))⁻¹ * (hardyStart (K + 1) - hardyStart K) := by
                            rw [ha_sq]; gcongr
                            calc ‖∫ t in (hardyStart K)..T,
                                  hardyCosExp K t * hardyCosExp K t‖
                                ≤ T - hardyStart K := norm_pair_integral_le_diff K K _ _ hT
                              _ ≤ hardyStart (K + 1) - hardyStart K := by linarith
                        _ ≤ ((K + 1 : ℝ))⁻¹ * (6 * Real.pi * ((K : ℝ) + 1)) := by gcongr
                        _ = 6 * Real.pi := by field_simp
                        _ ≤ 30 := by nlinarith [Real.pi_lt_four]
                  have h_diag_card : (large.filter (fun p => p.1 = p.2)).card ≤ K + 1 := by
                    calc (large.filter (fun p => p.1 = p.2)).card
                        ≤ (Finset.range (K + 1)).card := by
                          apply Finset.card_le_card_of_injOn Prod.fst
                          · intro p hp
                            exact (Finset.mem_product.mp
                              (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
                          · intro p₁ hp₁ p₂ hp₂ heq
                            have h1 := (Finset.mem_filter.mp hp₁).2
                            have h2 := (Finset.mem_filter.mp hp₂).2
                            exact Prod.ext heq (by rw [← h1, ← h2, heq])
                      _ = K + 1 := Finset.card_range _
                  calc ∑ p ∈ large.filter (fun p => p.1 = p.2), a p.1 * a p.2 *
                        ‖∫ t in (hardyStart (max p.1 p.2))..T, hardyCosExp p.1 t * hardyCosExp p.2 t‖
                      ≤ ∑ _ ∈ large.filter (fun p => p.1 = p.2), (30 : ℝ) :=
                        Finset.sum_le_sum h_diag_per_pair
                    _ ≤ 30 * ((K : ℝ) + 1) := by
                        rw [Finset.sum_const, nsmul_eq_mul]
                        have : (↑(large.filter (fun p => p.1 = p.2)).card : ℝ) ≤ ↑(K + 1) :=
                          Nat.cast_le.mpr h_diag_card
                        push_cast at this ⊢; nlinarith
                    _ ≤ 30 * (T / (2 * Real.pi)) := by gcongr
                    _ ≤ 5 * T := by
                        rw [show 30 * (T / (2 * Real.pi)) = 30 / (2 * Real.pi) * T from by ring]
                        gcongr; rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
                        nlinarith [Real.pi_gt_three]
                · -- OFF-DIAGONAL: j ≠ l, max ≥ K₀. Bound ≤ (2C_off + 12)T.
                  set offdiag := large.filter (fun p => ¬ (p.1 = p.2))
                  -- Per-pair bound for j < l: ‖∫_{hS l}^T‖ ≤ BL(l) + 6/log((l+1)/(j+1))
                  have h_ppb : ∀ p : ℕ × ℕ, p ∈ offdiag →
                      ‖∫ t in (hardyStart (max p.1 p.2))..T,
                        hardyCosExp p.1 t * hardyCosExp p.2 t‖ ≤
                      (hardyStart (K + 1) - hardyStart K) +
                      6 / Real.log (((max p.1 p.2 : ℝ) + 1) / ((min p.1 p.2 : ℝ) + 1)) := by
                    intro p hp
                    have hp_ne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
                    have hp_large := (Finset.mem_filter.mp hp).1
                    have hp_S := (Finset.mem_filter.mp hp_large).1
                    have hp_ge : ¬ max p.1 p.2 < K₀ := (Finset.mem_filter.mp hp_large).2
                    have ⟨h1, h2⟩ := Finset.mem_product.mp hp_S
                    have hj_lt := Finset.mem_range.mp h1
                    have hl_lt := Finset.mem_range.mp h2
                    have hK₁_le_max : K₁ ≤ max p.1 p.2 := le_trans hK₁_le_K₀ (by omega)
                    have hmax_le_K : max p.1 p.2 ≤ K := by omega
                    rcases Nat.lt_or_gt_of_ne hp_ne with h_lt | h_gt
                    · -- p.1 < p.2
                      have h_le := le_of_lt h_lt
                      rw [max_eq_right h_le]  -- ℕ-level max in hardyStart
                      have h_le_r : (↑p.1 : ℝ) ≤ ↑p.2 := Nat.cast_le.mpr h_le
                      simp only [max_eq_right h_le_r, min_eq_left h_le_r]  -- ℝ-level in log
                      have hp2_le : p.2 ≤ K := by rwa [max_eq_right h_le] at hmax_le_K
                      have hK₁p2 : K₁ ≤ p.2 := by rwa [max_eq_right h_le] at hK₁_le_max
                      by_cases hp2K : p.2 < K
                      · -- Interior: use pair_integral_split + VdC
                        calc ‖∫ t in (hardyStart p.2)..T,
                                hardyCosExp p.1 t * hardyCosExp p.2 t‖
                            ≤ (hardyStart (p.2 + 1) - hardyStart p.2) +
                              ‖∫ t in (hardyStart (p.2 + 1))..T,
                                hardyCosExp p.1 t * hardyCosExp p.2 t‖ :=
                              pair_integral_split p.1 p.2 K T h_lt hp2K hT
                          _ ≤ (hardyStart (p.2 + 1) - hardyStart p.2) +
                              6 / Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1)) := by
                              gcongr
                              exact le_trans (hK₁ p.1 p.2 h_lt hK₁p2 T
                                ((hardyStart_mono (show p.2 + 1 ≤ K from hp2K)).trans hT))
                                (vdc_off_diag_const_le p.1 p.2 h_lt)
                          _ ≤ _ := by linarith [block_length_le_block_length hp2_le]
                      · -- Boundary: p.2 = K
                        have hp2K_eq : p.2 = K := le_antisymm hp2_le (by omega)
                        rw [hp2K_eq]
                        have h_log_pos : 0 < Real.log (((K : ℝ) + 1) / ((p.1 : ℝ) + 1)) :=
                          Real.log_pos (by rw [one_lt_div (by positivity)]; norm_cast; omega)
                        calc ‖∫ t in (hardyStart K)..T,
                                hardyCosExp p.1 t * hardyCosExp K t‖
                            ≤ T - hardyStart K := norm_pair_integral_le_diff p.1 K _ T hT
                          _ ≤ hardyStart (K + 1) - hardyStart K := by linarith
                          _ ≤ _ := le_add_of_nonneg_right (div_nonneg (by norm_num) (le_of_lt h_log_pos))
                    · -- p.1 > p.2: swap integrand via mul_comm
                      have h_le := le_of_lt h_gt
                      rw [max_eq_left h_le]  -- ℕ-level max in hardyStart
                      have h_le_r : (↑p.2 : ℝ) ≤ ↑p.1 := Nat.cast_le.mpr h_le
                      simp only [max_eq_left h_le_r, min_eq_right h_le_r]  -- ℝ-level in log
                      have hp1_le : p.1 ≤ K := by rwa [max_eq_left h_le] at hmax_le_K
                      have hK₁p1 : K₁ ≤ p.1 := by rwa [max_eq_left h_le] at hK₁_le_max
                      rw [show ‖∫ t in (hardyStart p.1)..T, hardyCosExp p.1 t * hardyCosExp p.2 t‖ =
                        ‖∫ t in (hardyStart p.1)..T, hardyCosExp p.2 t * hardyCosExp p.1 t‖ from by
                        congr 1; exact intervalIntegral.integral_congr (fun t _ => mul_comm _ _)]
                      by_cases hp1K : p.1 < K
                      · calc ‖∫ t in (hardyStart p.1)..T,
                                hardyCosExp p.2 t * hardyCosExp p.1 t‖
                            ≤ (hardyStart (p.1 + 1) - hardyStart p.1) +
                              ‖∫ t in (hardyStart (p.1 + 1))..T,
                                hardyCosExp p.2 t * hardyCosExp p.1 t‖ :=
                              pair_integral_split p.2 p.1 K T h_gt hp1K hT
                          _ ≤ (hardyStart (p.1 + 1) - hardyStart p.1) +
                              6 / Real.log (((p.1 : ℝ) + 1) / ((p.2 : ℝ) + 1)) := by
                              gcongr
                              exact le_trans (hK₁ p.2 p.1 h_gt hK₁p1 T
                                ((hardyStart_mono (show p.1 + 1 ≤ K from hp1K)).trans hT))
                                (vdc_off_diag_const_le p.2 p.1 h_gt)
                          _ ≤ _ := by linarith [block_length_le_block_length hp1_le]
                      · have hp1K_eq : p.1 = K := le_antisymm hp1_le (Nat.not_lt.mp hp1K)
                        rw [hp1K_eq]
                        have h_log_pos : 0 < Real.log (((K : ℝ) + 1) / ((p.2 : ℝ) + 1)) :=
                          Real.log_pos (by
                            rw [one_lt_div (by positivity : (0:ℝ) < (↑p.2 : ℝ) + 1)]
                            have : p.2 < K := hp1K_eq ▸ h_gt
                            exact_mod_cast Nat.succ_lt_succ this)
                        calc ‖∫ t in (hardyStart K)..T,
                                hardyCosExp p.2 t * hardyCosExp K t‖
                            ≤ T - hardyStart K := norm_pair_integral_le_diff p.2 K _ T hT
                          _ ≤ hardyStart (K + 1) - hardyStart K := by linarith
                          _ ≤ _ := le_add_of_nonneg_right (div_nonneg (by norm_num) (le_of_lt h_log_pos))
                  -- Now bound the sum
                  calc ∑ p ∈ offdiag, a p.1 * a p.2 *
                        ‖∫ t in (hardyStart (max p.1 p.2))..T,
                          hardyCosExp p.1 t * hardyCosExp p.2 t‖
                      ≤ ∑ p ∈ offdiag,
                          (a p.1 * a p.2 * (hardyStart (K + 1) - hardyStart K) +
                           a p.1 * a p.2 *
                             (6 / Real.log (((max p.1 p.2 : ℝ) + 1) / ((min p.1 p.2 : ℝ) + 1)))) := by
                        apply Finset.sum_le_sum; intro p hp
                        have h_bound := h_ppb p hp
                        have h_aa : 0 ≤ a p.1 * a p.2 := mul_nonneg (by positivity) (by positivity)
                        calc a p.1 * a p.2 *
                              ‖∫ t in (hardyStart (max p.1 p.2))..T,
                                hardyCosExp p.1 t * hardyCosExp p.2 t‖
                            ≤ a p.1 * a p.2 * ((hardyStart (K + 1) - hardyStart K) +
                                6 / Real.log (((max p.1 p.2 : ℝ) + 1) / ((min p.1 p.2 : ℝ) + 1))) :=
                              mul_le_mul_of_nonneg_left h_bound h_aa
                          _ = a p.1 * a p.2 * (hardyStart (K + 1) - hardyStart K) +
                              a p.1 * a p.2 *
                                (6 / Real.log (((max p.1 p.2 : ℝ) + 1) / ((min p.1 p.2 : ℝ) + 1))) := by
                              ring
                    _ = (∑ p ∈ offdiag, a p.1 * a p.2 * (hardyStart (K + 1) - hardyStart K)) +
                        (∑ p ∈ offdiag, a p.1 * a p.2 *
                          (6 / Real.log (((max p.1 p.2 : ℝ) + 1) / ((min p.1 p.2 : ℝ) + 1)))) :=
                        by rw [← Finset.sum_add_distrib]
                    _ ≤ 12 * T + (2 * C_off) * T := by
                        apply add_le_add
                        · -- BL sum: factor out BL(K), bound weight sum by (∑a)² ≤ 4(K+1)
                          have h_factor : ∑ p ∈ offdiag,
                              a p.1 * a p.2 * (hardyStart (K + 1) - hardyStart K) =
                            (hardyStart (K + 1) - hardyStart K) * ∑ p ∈ offdiag, a p.1 * a p.2 := by
                            rw [Finset.mul_sum]; congr 1; funext p; ring
                          rw [h_factor]
                          have h_wt_le : ∑ p ∈ offdiag, a p.1 * a p.2 ≤
                              (∑ j ∈ Finset.range (K + 1), a j) ^ 2 := by
                            calc ∑ p ∈ offdiag, a p.1 * a p.2
                                ≤ ∑ p ∈ S, a p.1 * a p.2 :=
                                  Finset.sum_le_sum_of_subset_of_nonneg
                                    (fun p hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
                                    (fun p _ _ => mul_nonneg (by positivity) (by positivity))
                              _ = (∑ j ∈ Finset.range (K + 1), a j) ^ 2 := by
                                  rw [Finset.sum_product]
                                  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sq]
                          have h_exp_eq : ∀ k : ℕ, a k = ((k : ℝ) + 1) ^ (-(1:ℝ)/2) := fun k => by
                            simp only [ha_def]; norm_num
                          have h_sq_le : (∑ j ∈ Finset.range (K + 1), a j) ^ 2 ≤ 4 * (↑K + 1) := by
                            simp_rw [h_exp_eq]
                            calc (∑ j ∈ Finset.range (K + 1), ((↑j + 1 : ℝ) ^ (-(1:ℝ)/2))) ^ 2
                                ≤ (2 * Real.sqrt ↑(K + 1)) ^ 2 := by
                                  apply sq_le_sq'
                                  · linarith [Real.sqrt_nonneg (↑(K+1) : ℝ),
                                      Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (K + 1)) =>
                                        show (0:ℝ) ≤ ((↑j + 1 : ℝ) ^ (-(1:ℝ)/2)) from by positivity)]
                                  · exact sum_inv_sqrt_le (K + 1)
                              _ = 4 * ↑(K + 1) := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
                              _ = 4 * (↑K + 1) := by push_cast; ring
                          calc (hardyStart (K + 1) - hardyStart K) * ∑ p ∈ offdiag, a p.1 * a p.2
                              ≤ (6 * Real.pi * (↑K + 1)) * (4 * (↑K + 1)) :=
                                mul_le_mul hBL (le_trans h_wt_le h_sq_le)
                                  (Finset.sum_nonneg (fun p _ => mul_nonneg (by positivity) (by positivity)))
                                  (by linarith [Real.pi_pos])
                            _ = 24 * Real.pi * (↑K + 1) ^ 2 := by ring
                            _ ≤ 24 * Real.pi * (T / (2 * Real.pi)) := by
                                gcongr
                            _ = 12 * T := by field_simp; ring
                        · -- VdC sum: factor out 6, split by p.1<p.2 vs p.2<p.1, use bijection
                          have h_factor6 : ∑ p ∈ offdiag, a p.1 * a p.2 *
                              (6 / Real.log (((max p.1 p.2 : ℝ) + 1) / ((min p.1 p.2 : ℝ) + 1))) =
                            6 * ∑ p ∈ offdiag, a p.1 * a p.2 /
                              Real.log (((max p.1 p.2 : ℝ) + 1) / ((min p.1 p.2 : ℝ) + 1)) := by
                            rw [Finset.mul_sum]; congr 1; funext p; ring
                          rw [h_factor6]
                          rw [show ∑ p ∈ offdiag, a p.1 * a p.2 /
                                Real.log (((max p.1 p.2 : ℝ) + 1) / ((min p.1 p.2 : ℝ) + 1)) =
                              (∑ p ∈ offdiag.filter (fun p => p.1 < p.2), a p.1 * a p.2 /
                                Real.log (((max p.1 p.2 : ℝ) + 1) / ((min p.1 p.2 : ℝ) + 1))) +
                              (∑ p ∈ offdiag.filter (fun p => ¬(p.1 < p.2)), a p.1 * a p.2 /
                                Real.log (((max p.1 p.2 : ℝ) + 1) / ((min p.1 p.2 : ℝ) + 1))) from
                            (Finset.sum_filter_add_sum_filter_not _ _ _).symm]
                          -- Simplify max/min using have lemmas (not conv)
                          have h_A_simp : ∑ p ∈ offdiag.filter (fun p => p.1 < p.2),
                              a p.1 * a p.2 /
                                Real.log (((max p.1 p.2 : ℝ) + 1) / ((min p.1 p.2 : ℝ) + 1)) =
                            ∑ p ∈ offdiag.filter (fun p => p.1 < p.2),
                              a p.1 * a p.2 /
                                Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1)) := by
                            apply Finset.sum_congr rfl; intro p hp
                            have h_lt := (Finset.mem_filter.mp hp).2
                            simp only [max_eq_right (Nat.cast_le.mpr (le_of_lt h_lt)),
                              min_eq_left (Nat.cast_le.mpr (le_of_lt h_lt))]
                          have h_B_simp : ∑ p ∈ offdiag.filter (fun p => ¬(p.1 < p.2)),
                              a p.1 * a p.2 /
                                Real.log (((max p.1 p.2 : ℝ) + 1) / ((min p.1 p.2 : ℝ) + 1)) =
                            ∑ p ∈ offdiag.filter (fun p => ¬(p.1 < p.2)),
                              a p.1 * a p.2 /
                                Real.log (((p.1 : ℝ) + 1) / ((p.2 : ℝ) + 1)) := by
                            apply Finset.sum_congr rfl; intro p hp
                            have hp_mem := Finset.mem_filter.mp hp
                            have hp_ne := (Finset.mem_filter.mp hp_mem.1).2
                            have h_gt := Nat.lt_of_le_of_ne (Nat.not_lt.mp hp_mem.2) (Ne.symm hp_ne)
                            simp only [max_eq_left (Nat.cast_le.mpr (le_of_lt h_gt)),
                              min_eq_right (Nat.cast_le.mpr (le_of_lt h_gt))]
                          rw [h_A_simp, h_B_simp]
                          -- Part B sum = Part A sum via bijection (j,l) ↦ (l,j)
                          have h_B_eq_A : ∑ p ∈ offdiag.filter (fun p => ¬(p.1 < p.2)),
                              a p.1 * a p.2 / Real.log (((p.1 : ℝ) + 1) / ((p.2 : ℝ) + 1)) =
                            ∑ p ∈ offdiag.filter (fun p => p.1 < p.2),
                              a p.1 * a p.2 / Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1)) := by
                            apply Finset.sum_nbij (fun p => (p.2, p.1))
                            · intro p hp
                              rw [Finset.mem_filter] at hp ⊢
                              have hp_offdiag := hp.1
                              have hp_ne := (Finset.mem_filter.mp hp_offdiag).2
                              have hp_gt : p.2 < p.1 := Nat.lt_of_le_of_ne (Nat.not_lt.mp hp.2) (Ne.symm hp_ne)
                              have hp_large := (Finset.mem_filter.mp hp_offdiag).1
                              have hp_S := (Finset.mem_filter.mp hp_large).1
                              have ⟨h1, h2⟩ := Finset.mem_product.mp hp_S
                              have h_max_sw : ¬max p.2 p.1 < K₀ := by
                                have := (Finset.mem_filter.mp hp_large).2; rwa [max_comm]
                              refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
                                ⟨Finset.mem_product.mpr ⟨h2, h1⟩, h_max_sw⟩,
                                Ne.symm hp_ne⟩, hp_gt⟩
                            · intro p₁ _ p₂ _ h
                              exact Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h)
                            · intro p hp
                              simp only [Finset.mem_coe, Finset.mem_filter] at hp
                              have hp_offdiag := hp.1
                              have hp_large := (Finset.mem_filter.mp hp_offdiag).1
                              have hp_S := (Finset.mem_filter.mp hp_large).1
                              have ⟨h1, h2⟩ := Finset.mem_product.mp hp_S
                              have h_max_sw : ¬max p.2 p.1 < K₀ := by
                                have := (Finset.mem_filter.mp hp_large).2; rwa [max_comm]
                              have hp_ne := (Finset.mem_filter.mp hp_offdiag).2
                              exact ⟨(p.2, p.1), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
                                ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩,
                                  h_max_sw⟩,
                                  Ne.symm hp_ne⟩, not_lt.mpr (le_of_lt hp.2)⟩, rfl⟩
                            · intro p _; simp [mul_comm (a p.1) (a p.2)]
                          rw [h_B_eq_A]
                          -- Now: 6 * 2A ≤ 2·C_off·T
                          have h_A_le_S : ∑ p ∈ offdiag.filter (fun p => p.1 < p.2),
                              a p.1 * a p.2 / Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1)) ≤
                            ∑ p ∈ S.filter (fun p => p.1 < p.2),
                              a p.1 * a p.2 / Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1)) := by
                            apply Finset.sum_le_sum_of_subset_of_nonneg
                            · intro p hp
                              rw [Finset.mem_filter] at hp ⊢
                              exact ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1).1, hp.2⟩
                            · intro p hp _
                              have hp_lt := (Finset.mem_filter.mp hp).2
                              exact div_nonneg (mul_nonneg (by positivity) (by positivity))
                                (le_of_lt (Real.log_pos (by
                                  rw [one_lt_div (by positivity : (0:ℝ) < (p.1:ℝ)+1)]
                                  exact_mod_cast Nat.succ_lt_succ hp_lt)))
                          have h_S_eq : ∑ p ∈ S.filter (fun p => p.1 < p.2),
                              a p.1 * a p.2 / Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1)) =
                            ∑ p ∈ (Finset.range (K+1) ×ˢ Finset.range (K+1)).filter (fun p => p.1 < p.2),
                              ((p.1+1:ℝ)^(-(1:ℝ)/2)) * ((p.2+1:ℝ)^(-(1:ℝ)/2)) /
                                Real.log (((p.2:ℝ)+1) / ((p.1:ℝ)+1)) := by
                            congr 1; funext p; simp [ha_def]; norm_num
                          calc 6 * (∑ p ∈ offdiag.filter (fun p => p.1 < p.2),
                                  a p.1 * a p.2 / Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1)) +
                                ∑ p ∈ offdiag.filter (fun p => p.1 < p.2),
                                  a p.1 * a p.2 / Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1)))
                              = 12 * ∑ p ∈ offdiag.filter (fun p => p.1 < p.2),
                                  a p.1 * a p.2 / Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1)) := by ring
                            _ ≤ 12 * ∑ p ∈ S.filter (fun p => p.1 < p.2),
                                  a p.1 * a p.2 / Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1)) := by
                                gcongr
                            _ = 12 * ∑ p ∈ (Finset.range (K+1) ×ˢ Finset.range (K+1)).filter
                                    (fun p => p.1 < p.2),
                                  ((p.1+1:ℝ)^(-(1:ℝ)/2)) * ((p.2+1:ℝ)^(-(1:ℝ)/2)) /
                                    Real.log (((p.2:ℝ)+1) / ((p.1:ℝ)+1)) := by rw [h_S_eq]
                            _ ≤ 12 * (C_off * ↑(K+1) * Real.log (↑(K+1) + 1)) := by
                                gcongr; exact hC_off (K + 1) (by omega)
                            _ ≤ 12 * (C_off * (↑K + 1) * (↑K + 1)) := by
                                have hlog_le : Real.log ((↑(K + 1) : ℝ) + 1) ≤ ↑K + 1 := by
                                  rw [show (↑(K + 1) : ℝ) + 1 = (↑K : ℝ) + 2 from by push_cast; ring]
                                  exact log_le_nat K
                                have h_nn : 0 ≤ C_off * (↑K + 1) := mul_nonneg
                                  (le_of_lt hC_off_pos) (by positivity)
                                have h_step := mul_le_mul_of_nonneg_left hlog_le h_nn
                                push_cast at h_step ⊢
                                nlinarith
                            _ = 12 * C_off * (↑K + 1) ^ 2 := by ring
                            _ ≤ 12 * C_off * (T / (2 * Real.pi)) :=
                                mul_le_mul_of_nonneg_left hKsq (by positivity)
                            _ ≤ 2 * C_off * T := by
                                rw [show 12 * C_off * (T / (2 * Real.pi)) =
                                  12 * (C_off * T) / (2 * Real.pi) from by ring]
                                rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
                                nlinarith [Real.pi_gt_three, mul_nonneg (le_of_lt hC_off_pos) (le_of_lt hT_pos)]
                    _ = (2 * C_off + 12) * T := by ring
            _ = (2 * C_off + 17) * T := by ring
    _ = (4 * ↑K₀ + 2 * C_off + 17) * T := by nlinarith

/-- **Key norm bound**: ‖∫₁ᵀ oscSum²‖ ≤ C·T for T in block K.

    Uses block decomposition + per-pair bound ≤ T−hS(max j l), then groups
    by m = max(j,l) with weight collapse S(m) ≤ 5. The bound
    ∑_m 5·(T−hS(m)) ≤ 5·(K+1)·T − 5·∑ hS(m) yields O(T) since
    (K+1)² ≤ T/(2π) and ∑ hS(m) ≥ 2π·∑(m+1)² = 2π(K+1)(K+2)(2K+3)/6. -/
lemma norm_integral_oscSum_sq_le_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, ∀ T : ℝ,
      hardyStart K ≤ T → T ≤ hardyStart (K + 1) →
      ‖∫ t in (1:ℝ)..T, (oscSum t) ^ 2‖ ≤ C * T := by
  -- Strategy: block decomposition + triangle inequality + VdC splitting
  -- For each pair (j,l) with m = max(j,l) and K₀ ≤ m < K:
  --   split ∫_{hS m}^T = first_block + beyond, bound by BL(m) + VdC
  -- Off-diagonal VdC sum ≤ 12·C_off·(K+1)·log(K+2) ≤ 12·C_off·T/(2π)
  -- Diagonal and boundary terms are O(T).
  -- Total ≤ C·T where C is universal.
  obtain ⟨K₁, hK₁⟩ := global_off_diagonal_vdc_bound
  obtain ⟨K₂, hK₂⟩ := Aristotle.Standalone.OscPieceBigOAssembly.global_diagonal_vdc_bound
  obtain ⟨C_off, hC_off_pos, hC_off⟩ := off_diagonal_double_sum_bound
  set K₀ := max K₁ K₂
  -- Constant: 4K₀ (small pairs) + 4 (BL off-diag) + 60·C_off/(2π) (VdC off-diag)
  --         + 25 (diagonal) + 20 (boundary)
  -- Simplified: use 4·K₀ + 60·C_off + 50
  refine ⟨4 * (↑K₀ : ℝ) + 60 * C_off + 50, by positivity, fun K T hT hT' => ?_⟩
  have hT_pos : (0 : ℝ) < T := lt_of_lt_of_le (by rw [hardyStart_formula]; positivity) hT
  have hK_nn : (0:ℝ) ≤ ↑K := Nat.cast_nonneg K
  have hK1_ge_one : (1 : ℝ) ≤ (↑K + 1 : ℝ) := by linarith
  have hT_ge_2pi : (2 : ℝ) * Real.pi ≤ T := by
    calc 2 * Real.pi ≤ 2 * Real.pi * (↑K + 1) ^ 2 := by nlinarith [pi_pos, sq_nonneg (↑K : ℝ)]
      _ ≤ T := by rwa [← hardyStart_formula]
  -- (K+1)² ≤ T/(2π), K+1 ≤ T/(2π)
  have hKsq := block_index_sq_le K T hT
  have hK1_le_T : (↑K + 1 : ℝ) ≤ T / (2 * Real.pi) := by nlinarith
  -- hS(K+1) ≤ 4T
  have hS_succ_le : hardyStart (K + 1) ≤ 4 * T := by
    rw [hardyStart_formula]
    have hpi : (0:ℝ) < 2 * Real.pi := by positivity
    -- (K+2)² = (K+1)² + 2(K+1) + 1 ≤ T/(2π) + 2·T/(2π) + 1 = 3T/(2π) + 1
    have hK2sq : (↑K + 2 : ℝ) ^ 2 ≤ 3 * T / (2 * Real.pi) + 1 := by
      have hsq : (↑K + 2 : ℝ) ^ 2 = (↑K + 1) ^ 2 + 2 * (↑K + 1) + 1 := by ring
      have h3 : 3 * T / (2 * Real.pi) = T / (2 * Real.pi) + 2 * (T / (2 * Real.pi)) := by ring
      rw [hsq, h3]; linarith
    have h2 : (↑(K + 1) + 1 : ℝ) = (↑K + 2 : ℝ) := by push_cast; ring
    rw [h2]
    have h1 : 2 * Real.pi * (↑K + 2 : ℝ) ^ 2 ≤ 3 * T + 2 * Real.pi := by
      have := mul_le_mul_of_nonneg_left hK2sq (le_of_lt hpi)
      have h3 : 2 * Real.pi * (3 * T / (2 * Real.pi) + 1) = 3 * T + 2 * Real.pi := by
        field_simp
      linarith
    linarith
  -- Rewrite and decompose
  rw [integral_oscSum_sq_from_one K T hT hT',
      block_decomposition_oscSum_sq K T hT hT']
  -- Triangle inequality
  have h_tri := norm_weighted_double_sum_le (K + 1)
    (fun j => ((j + 1 : ℝ) ^ (-(1/2 : ℝ))))
    (fun j l => ∫ t in (hardyStart (max j l))..T, hardyCosExp j t * hardyCosExp l t)
    (fun j => by positivity)
  calc ‖∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
        (((j + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        (((l + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        ∫ t in (hardyStart (max j l))..T, hardyCosExp j t * hardyCosExp l t‖
      ≤ ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
          ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) * ((l + 1 : ℝ) ^ (-(1/2 : ℝ))) *
          ‖∫ t in (hardyStart (max j l))..T, hardyCosExp j t * hardyCosExp l t‖ :=
        h_tri
    _ ≤ (4 * ↑K₀ + 60 * C_off + 50) * T := by
        -- Split by K < K₀ vs K ≥ K₀
        by_cases hKK₀ : K + 1 ≤ K₀
        · -- Case 1: K < K₀. Trivial bound: ‖∫‖ ≤ T, weight sum ≤ 4(K+1) ≤ 4K₀.
          -- Step 1: bound each term by a_j a_l T
          calc ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
                ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) * ((l + 1 : ℝ) ^ (-(1/2 : ℝ))) *
                ‖∫ t in (hardyStart (max j l))..T, hardyCosExp j t * hardyCosExp l t‖
              ≤ ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
                ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) * ((l + 1 : ℝ) ^ (-(1/2 : ℝ))) * T := by
                apply Finset.sum_le_sum; intro j hj; apply Finset.sum_le_sum; intro l hl
                have hj' := Finset.mem_range.mp hj; have hl' := Finset.mem_range.mp hl
                have h_le : hardyStart (max j l) ≤ T :=
                  (hardyStart_mono (by omega)).trans hT
                gcongr
                exact norm_pair_integral_le_T j l _ T
                  (by rw [hardyStart_formula]; positivity) h_le
            _ ≤ (4 * ↑K₀ + 60 * C_off + 50) * T := by
                -- Factor: ∑∑ a_j a_l T = T·(∑ a_j)² ≤ T·4(K+1) ≤ 4K₀·T ≤ C·T
                have h_eq : ∑ j₀ ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
                    ((j₀ + 1 : ℝ) ^ (-(1/2 : ℝ))) * ((l + 1 : ℝ) ^ (-(1/2 : ℝ))) * T =
                    T * (∑ j₀ ∈ Finset.range (K + 1), ((j₀ + 1 : ℝ) ^ (-(1/2 : ℝ)))) ^ 2 := by
                  rw [sq]; simp_rw [Finset.sum_mul, Finset.mul_sum]
                  congr 1; ext j₀; congr 1; ext l; ring
                rw [h_eq]
                have h_exp_eq : ∀ k : ℕ, ((k + 1 : ℝ) ^ (-(1/2 : ℝ))) =
                    ((k : ℝ) + 1) ^ (-(1:ℝ)/2) := fun k => by norm_num
                have h_sq_le : (∑ j₀ ∈ Finset.range (K + 1),
                    ((j₀ + 1 : ℝ) ^ (-(1/2 : ℝ)))) ^ 2 ≤ 4 * ↑(K + 1) := by
                  simp_rw [h_exp_eq]
                  calc (∑ j₀ ∈ Finset.range (K + 1), ((↑j₀ + 1 : ℝ) ^ (-(1:ℝ)/2))) ^ 2
                      ≤ (2 * Real.sqrt ↑(K + 1)) ^ 2 :=
                        sq_le_sq' (by linarith [Real.sqrt_nonneg (↑(K + 1) : ℝ),
                          Finset.sum_nonneg (fun j₀ (_ : j₀ ∈ Finset.range (K + 1)) =>
                            show (0:ℝ) ≤ ((↑j₀ + 1 : ℝ) ^ (-(1:ℝ)/2)) from by positivity)])
                          (sum_inv_sqrt_le _)
                    _ = 4 * ↑(K + 1) := by
                        rw [mul_pow]; rw [Real.sq_sqrt (Nat.cast_nonneg _)]; ring
                -- 4(K+1) ≤ 4K₀ ≤ 4K₀+60C_off+50
                nlinarith [show (↑(K + 1) : ℝ) ≤ ↑K₀ from by exact_mod_cast hKK₀]
        · -- Case 2: K ≥ K₀. Need VdC cancellation.
          -- Split each pair integral at hS(max+1) for max < K.
          -- First block ≤ BL(max) ≤ BL(K). Tail ≤ global VdC constant.
          -- BL contribution: (∑a)² · BL(K) ≤ 24π(K+1)² ≤ 12T
          -- Off-diag VdC: 12·C_off·(K+1)·log(K+2) ≤ 2C_off·T
          -- Diag VdC: 6(K+1) ≤ T
          -- Small pairs (max < K₀): 4K₀·T
          -- Total: (4K₀ + 2C_off + 14)T ≤ (4K₀ + 60C_off + 50)T
          push_neg at hKK₀
          have hK₀_le_K : K₀ ≤ K := by omega
          calc ∑ j ∈ Finset.range (K + 1), ∑ l ∈ Finset.range (K + 1),
                ((j + 1 : ℝ) ^ (-(1/2 : ℝ))) * ((l + 1 : ℝ) ^ (-(1/2 : ℝ))) *
                ‖∫ t in (hardyStart (max j l))..T, hardyCosExp j t * hardyCosExp l t‖
              ≤ (4 * ↑K₀ + 2 * C_off + 17) * T :=
                vdc_double_sum_bound K₁ K₂ hK₁ hK₂ C_off hC_off_pos hC_off K₀ rfl K T hT hT' hK₀_le_K
            _ ≤ (4 * ↑K₀ + 60 * C_off + 50) * T := by nlinarith

/-! ## Main theorem -/

/-- **Oscillatory piece integral is O(T).**

    Uses the identity MainTerm² - 2·P = 2·Re(oscSum²) and bounds ‖∫ oscSum²‖
    via block decomposition + VdC cancellation. -/
theorem osc_piece_integral_big_O :
    (fun T => ∫ t in (1:ℝ)..T, ((MainTerm t) ^ 2 - 2 * partialMsIntegrand t))
      =O[atTop] (fun T => T) := by
  obtain ⟨C₀, hC₀_pos, h_bound⟩ := norm_integral_oscSum_sq_le_linear
  refine .of_bound (2 * C₀) ?_
  filter_upwards [eventually_ge_atTop (hardyStart 0)] with T hT₀
  obtain ⟨K, hK_le, hK_le'⟩ := exists_block_of_ge_hardyStart0 T hT₀
  have hT_pos : (0 : ℝ) < T := lt_of_lt_of_le (by rw [hardyStart_formula]; positivity) hT₀
  -- Pointwise rewrite + Re/integral commutation
  have h_ii := oscSum_sq_ii_one_T K T hK_le hK_le'
  have h_eq : ∫ t in (1:ℝ)..T, ((MainTerm t) ^ 2 - 2 * partialMsIntegrand t) =
      2 * (∫ t in (1:ℝ)..T, (oscSum t) ^ 2).re := by
    have h_pw : ∀ t, (MainTerm t) ^ 2 - 2 * partialMsIntegrand t =
        2 * ((oscSum t) ^ 2).re := oscPiece_eq_two_re_sq
    rw [show (fun t => (MainTerm t) ^ 2 - 2 * partialMsIntegrand t) =
      (fun t => (2 : ℝ) * ((oscSum t) ^ 2).re) from funext h_pw]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have := Complex.reCLM.intervalIntegral_comp_comm h_ii
    simp only [Complex.reCLM_apply] at this
    exact this
  -- |∫ (M²-2P)| = |2·Re(∫ oscSum²)| ≤ 2·‖∫ oscSum²‖ ≤ 2·C₀·T
  simp only [Real.norm_eq_abs, h_eq]
  have h_main := h_bound K T hK_le hK_le'
  calc |2 * (∫ t in (1:ℝ)..T, (oscSum t) ^ 2).re|
      ≤ 2 * |(∫ t in (1:ℝ)..T, (oscSum t) ^ 2).re| := by rw [abs_mul, abs_of_pos (by positivity)]
    _ ≤ 2 * ‖∫ t in (1:ℝ)..T, (oscSum t) ^ 2‖ := by
        gcongr; exact Complex.abs_re_le_norm _
    _ ≤ 2 * (C₀ * T) := by gcongr
    _ = 2 * C₀ * |T| := by rw [abs_of_pos hT_pos]; ring

end Aristotle.Standalone.OscPieceBigOAssembly
