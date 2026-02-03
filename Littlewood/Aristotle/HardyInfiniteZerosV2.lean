/-
Hardy's theorem: infinitely many zeros on the critical line.

Version 2: Fixed field signatures (endpoints at 1, not arbitrary T₁).

BUG IN V1 (HardyInfiniteZeros.lean):
The mean_square_lower_bound, first_moment_upper_bound, and l1_lower_bound fields
universally quantify over the lower endpoint T₁ ∈ [0,T), requiring the bounds to hold
for ALL such T₁. This is unsatisfiable: for T₁ = T-ε, ∫_{T-ε}^T Z² ≈ ε·Z(T)² → 0,
yet the RHS is c·T·log T. The `grind` proof in V1 works vacuously from sorry = False.

FIX: All integrals are over [1, T] with fixed lower endpoint.

The contradiction argument:
1. Mean square: ∫₁ᵀ Z(t)² dt ≥ c·T·log T
2. First moment: |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2+ε}
3. Z_convexity_bound: |Z(t)| ≤ C'|t|^{1/4+ε}
4. If only finitely many zeros, Z has constant sign on [T₀, ∞)
5. Then |∫_{T₀}^T Z| = ∫_{T₀}^T |Z| (constant sign)
6. So ∫_{T₀}^T |Z| ≤ |∫₁ᵀ Z| + |∫₁^{T₀} Z| ≤ C·T^{1/2+ε₁} + const
7. And ∫₁ᵀ Z² ≤ const + sup_{[T₀,T]}|Z| · ∫_{T₀}^T |Z|
                ≤ const + C'·T^{1/4+ε₂} · (C·T^{1/2+ε₁} + const)
8. So c·T·log T ≤ const + C''·T^{3/4+ε₁+ε₂}
9. For ε₁ + ε₂ < 1/4, exponent 3/4 + ε₁ + ε₂ < 1, so T·log T dominates. Contradiction!

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardyInfiniteZerosV2

open Complex Real Set Filter Topology MeasureTheory

/-- Setup for Hardy's Theorem, Version 2 with correct field signatures.
    All integral bounds use fixed lower endpoint 1, not arbitrary T₁. -/
class HardySetupV2 where
  /-- The real-valued Hardy Z function on the critical line -/
  Z : ℝ → ℝ
  /-- Z is continuous -/
  Z_continuous : Continuous Z
  /-- Z(t) = 0 ↔ ζ(1/2+it) = 0 -/
  Z_zero_iff : ∀ t : ℝ, Z t = 0 ↔ riemannZeta (1/2 + I * t) = 0
  /-- Mean square lower bound: ∫₁ᵀ Z² ≥ c·T·log T (fixed endpoint 1) -/
  mean_square_lower :
    ∃ c : ℝ, c > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
      c * T * Real.log T ≤ ∫ t in Ioc 1 T, (Z t)^2
  /-- First moment upper bound: |∫₁ᵀ Z| ≤ C·T^{1/2+ε} (fixed endpoint 1) -/
  first_moment_upper :
    ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
      |∫ t in Ioc 1 T, Z t| ≤ C * T^(1/2 + ε)
  /-- Convexity bound: |Z(t)| ≤ C|t|^{1/4+ε} -/
  Z_convexity_bound :
    ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∀ t : ℝ, |t| ≥ 2 →
      |Z t| ≤ C * |t|^(1/4 + ε)

variable [inst : HardySetupV2]

/-! ## Step 1: Finitely many zeros implies constant sign -/

/-- If Z has finitely many positive zeros, it has constant sign on [T₀, ∞)
    for some T₀, by continuity and IVT. -/
lemma constant_sign_of_finite (h : Set.Finite {t : ℝ | inst.Z t = 0 ∧ t > 0}) :
    ∃ T₀ : ℝ, T₀ > 0 ∧ ((∀ t : ℝ, t > T₀ → inst.Z t > 0) ∨
                           (∀ t : ℝ, t > T₀ → inst.Z t < 0)) := by
  -- Get an upper bound for the finite set of positive zeros
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t, inst.Z t = 0 ∧ t > 0 → t ≤ M := by
    by_cases he : {t : ℝ | inst.Z t = 0 ∧ t > 0}.Nonempty
    · exact ⟨sSup {t | inst.Z t = 0 ∧ t > 0}, fun t ht => le_csSup h.bddAbove ht⟩
    · exact ⟨0, fun t ht => absurd ⟨t, ht⟩ he⟩
  -- Take T₀ = max(M+1, 1), ensuring T₀ > 0
  set T₀ := max (M + 1) 1 with hT₀_def
  refine ⟨T₀, by positivity, ?_⟩
  -- Z has no zeros on (T₀, ∞)
  have h_nz : ∀ t, t > T₀ → inst.Z t ≠ 0 := by
    intro t ht hzt
    have h1 : t > M + 1 := lt_of_le_of_lt (le_max_left _ _) ht
    have h2 : t > 0 := lt_trans (by positivity : T₀ > 0) ht
    exact absurd (hM t ⟨hzt, h2⟩) (by linarith)
  -- Z(T₀+1) ≠ 0, so it's positive or negative
  have h_nz_ref := h_nz (T₀ + 1) (by linarith)
  rcases lt_trichotomy (inst.Z (T₀ + 1)) 0 with h_neg | h_zero | h_pos
  · right; intro t ht
    by_contra h_not_neg; push_neg at h_not_neg
    rcases eq_or_lt_of_le h_not_neg with h_eq | h_pos_t
    · exact h_nz t ht h_eq.symm
    · -- Z(T₀+1) < 0 and Z(t) > 0, IVT gives a zero between them
      have h_ivt := intermediate_value_uIcc
        (inst.Z_continuous.continuousOn (s := Set.uIcc (T₀ + 1) t))
      have hmin : min (inst.Z (T₀ + 1)) (inst.Z t) ≤ 0 := min_le_of_left_le h_neg.le
      have hmax : 0 ≤ max (inst.Z (T₀ + 1)) (inst.Z t) := le_max_of_le_right h_pos_t.le
      obtain ⟨c, hc_mem, hc_zero⟩ := h_ivt ⟨hmin, hmax⟩
      have hc_gt : c > T₀ := by
        simp only [Set.uIcc_comm, Set.mem_uIcc] at hc_mem
        rcases hc_mem with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
      exact h_nz c hc_gt hc_zero
  · exact absurd h_zero h_nz_ref
  · left; intro t ht
    by_contra h_not_pos; push_neg at h_not_pos
    rcases eq_or_lt_of_le h_not_pos with h_eq | h_neg_t
    · exact h_nz t ht h_eq
    · -- Z(T₀+1) > 0 and Z(t) < 0, IVT gives a zero between them
      have h_ivt := intermediate_value_uIcc
        (inst.Z_continuous.continuousOn (s := Set.uIcc (T₀ + 1) t))
      have hmin : min (inst.Z (T₀ + 1)) (inst.Z t) ≤ 0 := min_le_of_right_le h_neg_t.le
      have hmax : 0 ≤ max (inst.Z (T₀ + 1)) (inst.Z t) := le_max_of_le_left h_pos.le
      obtain ⟨c, hc_mem, hc_zero⟩ := h_ivt ⟨hmin, hmax⟩
      have hc_gt : c > T₀ := by
        simp only [Set.uIcc_comm, Set.mem_uIcc] at hc_mem
        rcases hc_mem with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
      exact h_nz c hc_gt hc_zero

/-! ## Step 2: Constant sign implies |∫Z| = ∫|Z| -/

/-- When Z has constant sign, |∫Z| = ∫|Z|. -/
lemma abs_integral_eq_of_pos (T₀ T : ℝ) (hT : T > T₀)
    (hsign : ∀ t : ℝ, t > T₀ → inst.Z t > 0) :
    |∫ t in Ioc T₀ T, inst.Z t| = ∫ t in Ioc T₀ T, |inst.Z t| := by
  have h_nn : ∀ t ∈ Ioc T₀ T, (0 : ℝ) ≤ inst.Z t :=
    fun t ht => le_of_lt (hsign t ht.1)
  rw [abs_of_nonneg (MeasureTheory.setIntegral_nonneg measurableSet_Ioc h_nn)]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    fun t ht => (abs_of_nonneg (h_nn t ht)).symm

/-! ## Step 3: Decompose mean square integral -/

/-- Decompose ∫₁ᵀ Z² = ∫₁^{T₀} Z² + ∫_{T₀}^T Z². -/
lemma mean_square_decomp (T₀ T : ℝ) (hT₀ : T₀ > 1) (hT : T > T₀) :
    ∫ t in Ioc 1 T, (inst.Z t)^2 ∂volume =
    ∫ t in Ioc 1 T₀, (inst.Z t)^2 ∂volume +
    ∫ t in Ioc T₀ T, (inst.Z t)^2 ∂volume := by
  have h_int : ∀ a b : ℝ, IntegrableOn (fun t => (inst.Z t)^2) (Set.Ioc a b) :=
    fun a b => (inst.Z_continuous.pow 2).continuousOn.integrableOn_compact isCompact_Icc
      |>.mono_set Set.Ioc_subset_Icc_self
  have h_split := MeasureTheory.setIntegral_union
    (Set.Ioc_disjoint_Ioc_of_le (le_refl T₀)) measurableSet_Ioc (h_int 1 T₀) (h_int T₀ T)
  rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith : (1:ℝ) ≤ T₀) (by linarith : T₀ ≤ T)] at h_split
  exact h_split

/-! ## Step 4: Bound ∫_{T₀}^T Z² using sup|Z| and ∫|Z| -/

/-- ∫_{T₀}^T Z² ≤ M · ∫_{T₀}^T |Z| when |Z(t)| ≤ M on [T₀,T].
    Pointwise: Z² = |Z|·|Z| ≤ M·|Z|, then integrate. -/
lemma mean_square_le_sup_times_l1 (T₀ T : ℝ) (hT : T > T₀)
    (M : ℝ) (hM_nn : 0 ≤ M) (hM : ∀ t ∈ Ioc T₀ T, |inst.Z t| ≤ M) :
    ∫ t in Ioc T₀ T, (inst.Z t)^2 ≤ M * ∫ t in Ioc T₀ T, |inst.Z t| := by
  have h_int_sq : IntegrableOn (fun t => (inst.Z t)^2) (Ioc T₀ T) :=
    (inst.Z_continuous.pow 2).continuousOn.integrableOn_compact isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  have h_int_abs : IntegrableOn (fun t => |inst.Z t|) (Ioc T₀ T) :=
    inst.Z_continuous.abs.continuousOn.integrableOn_compact isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  calc ∫ t in Ioc T₀ T, (inst.Z t)^2
      ≤ ∫ t in Ioc T₀ T, M * |inst.Z t| := by
        apply MeasureTheory.setIntegral_mono_on h_int_sq (h_int_abs.const_mul M)
          measurableSet_Ioc
        intro t ht
        rw [← sq_abs, sq]
        exact mul_le_mul_of_nonneg_right (hM t ht) (abs_nonneg _)
    _ = M * ∫ t in Ioc T₀ T, |inst.Z t| :=
        MeasureTheory.integral_const_mul M _

/-! ## Step 5: The contradiction -/

/-- Hardy's theorem: infinitely many zeros of ζ on the critical line.
    The proof derives a contradiction from assuming finitely many zeros:
    constant sign → tight integral bounds → T·log T ≤ C·T^α for α < 1. -/
theorem hardy_infinitely_many_zeros_v2 :
    Set.Infinite {t : ℝ | riemannZeta (1/2 + I * t) = 0} := by
  -- Assume finite
  by_contra h_fin
  rw [Set.not_infinite] at h_fin
  -- Transfer to Z zeros using Z_zero_iff
  have h_Z_fin : Set.Finite {t : ℝ | inst.Z t = 0 ∧ t > 0} := by
    exact h_fin.subset fun t ⟨ht_zero, ht_pos⟩ => (inst.Z_zero_iff t).mp ht_zero
  -- Get constant sign after some T₀
  obtain ⟨T₀, hT₀, hsign⟩ := constant_sign_of_finite h_Z_fin
  -- Get the quantitative bounds
  obtain ⟨c, hc, T₁, hT₁, h_ms⟩ := inst.mean_square_lower
  -- Use ε = 1/10 for both first moment and convexity
  obtain ⟨C_fm, hC_fm, T₂, hT₂, h_fm⟩ := inst.first_moment_upper (1/10) (by norm_num)
  obtain ⟨C_cv, hC_cv, h_cv⟩ := inst.Z_convexity_bound (1/10) (by norm_num)
  -- Set T_min large enough for all bounds
  set T_min := max (max T₀ T₁) (max T₂ 2) with hT_min_def
  have hTm_T0 : T_min ≥ T₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hTm_T1 : T_min ≥ T₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hTm_T2 : T_min ≥ T₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hTm_2 : T_min ≥ 2 := le_trans (le_max_right _ _) (le_max_right _ _)
  have hTm_gt1 : T_min > 1 := by linarith
  -- Integrability helpers
  have h_int_Z : ∀ a b : ℝ, IntegrableOn inst.Z (Ioc a b) :=
    fun a b => inst.Z_continuous.continuousOn.integrableOn_compact isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  -- Fixed constants
  set K := ∫ t in Ioc 1 T_min, (inst.Z t)^2 ∂volume with hK_def
  set K_fm := |∫ t in Ioc 1 T_min, inst.Z t| with hK_fm_def
  have hK_nn : 0 ≤ K := setIntegral_nonneg measurableSet_Ioc (fun _ _ => sq_nonneg _)
  set D := C_cv * (C_fm + K_fm) with hD_def
  -- Main bound: for T > T_min, c * T * log T ≤ K + D * T
  suffices h_bound : ∀ T, T > T_min → c * T * Real.log T ≤ K + D * T by
    -- Contradiction: log T → ∞ but c * log T is bounded
    obtain ⟨T', hT'⟩ := Filter.eventually_atTop.mp
      (Real.tendsto_log_atTop.eventually_gt_atTop ((D + K) / c + 1))
    set T'' := max T' (T_min + 1) with hT''_def
    have hT''_ge : T'' ≥ T' := le_max_left _ _
    have hT''_gt : T'' > T_min := by linarith [le_max_right T' (T_min + 1)]
    have hT''_ge1 : T'' ≥ 1 := by linarith
    have h1 : Real.log T'' > (D + K) / c + 1 := hT' T'' hT''_ge
    -- c * log T'' > D + K + c
    have h2 : c * Real.log T'' - D > K := by
      have : c * ((D + K) / c + 1) = D + K + c := by field_simp
      nlinarith [mul_lt_mul_of_pos_left h1 hc]
    -- From h_bound: c * T'' * log T'' ≤ K + D * T'', i.e., T'' * (c * log T'' - D) ≤ K
    have h3 := h_bound T'' hT''_gt
    -- But T'' ≥ 1 and c * log T'' - D > K ≥ 0
    have h4 : T'' * (c * Real.log T'' - D) ≥ c * Real.log T'' - D := by
      nlinarith
    -- K < c * log T'' - D ≤ T'' * (c * log T'' - D) ≤ K
    linarith
  -- Prove the main bound
  intro T hT
  have hT_pos : T > 0 := by linarith
  have hT_ge1 : 1 ≤ T := by linarith
  -- (a) Mean square lower bound
  have ha : c * T * Real.log T ≤ ∫ t in Ioc 1 T, (inst.Z t)^2 :=
    h_ms T (le_of_lt (lt_of_le_of_lt hTm_T1 hT))
  -- (b) Decompose ∫₁ᵀ Z² = K + ∫_{Tm}^T Z²
  have hb := mean_square_decomp T_min T hTm_gt1 hT
  -- (c) Pointwise |Z(t)| ≤ C_cv * T^(7/20) on [Tm, T]
  have h_cv_bd : ∀ t ∈ Ioc T_min T, |inst.Z t| ≤ C_cv * T ^ ((1:ℝ)/4 + 1/10) := by
    intro t ht
    have ht_pos : t > 0 := by linarith [ht.1]
    calc |inst.Z t| ≤ C_cv * |t| ^ ((1:ℝ)/4 + 1/10) :=
          h_cv t (by rw [abs_of_pos ht_pos]; linarith [ht.1])
      _ ≤ C_cv * T ^ ((1:ℝ)/4 + 1/10) := by
          apply mul_le_mul_of_nonneg_left _ hC_cv.le
          exact rpow_le_rpow (abs_nonneg t)
            (by rw [abs_of_pos ht_pos]; exact ht.2) (by norm_num)
  -- (d) ∫_{Tm}^T Z² ≤ M * ∫_{Tm}^T |Z|
  have hd := mean_square_le_sup_times_l1 T_min T hT
    (C_cv * T ^ ((1:ℝ)/4 + 1/10)) (by positivity) h_cv_bd
  -- (e) Bound ∫_{Tm}^T |Z| via constant sign + triangle + first moment
  -- Integral splitting: ∫₁^T Z = ∫₁^{Tm} Z + ∫_{Tm}^T Z
  have h_split_Z : ∫ t in Ioc 1 T, inst.Z t =
      (∫ t in Ioc 1 T_min, inst.Z t) + (∫ t in Ioc T_min T, inst.Z t) := by
    have h_union := setIntegral_union (Ioc_disjoint_Ioc_of_le (le_refl T_min))
      measurableSet_Ioc (h_int_Z 1 T_min) (h_int_Z T_min T)
    rw [Ioc_union_Ioc_eq_Ioc (by linarith : (1:ℝ) ≤ T_min) (by linarith : T_min ≤ T)] at h_union
    exact h_union
  -- Bound ∫_{Tm}^T |Z| ≤ C_fm * T^(6/10) + K_fm
  have he : ∫ t in Ioc T_min T, |inst.Z t| ≤ C_fm * T ^ ((1:ℝ)/2 + 1/10) + K_fm := by
    have h_fm_T : |∫ t in Ioc 1 T, inst.Z t| ≤ C_fm * T ^ ((1:ℝ)/2 + 1/10) :=
      h_fm T (le_of_lt (lt_of_le_of_lt hTm_T2 hT))
    -- Key: |∫_{Tm}^T Z| ≤ C_fm * T^... + K_fm via triangle inequality
    have h_abs_int : |∫ t in Ioc T_min T, inst.Z t| ≤
        C_fm * T ^ ((1:ℝ)/2 + 1/10) + K_fm := by
      have hI_upper : ∫ t in Ioc 1 T, inst.Z t ≤ C_fm * T ^ ((1:ℝ)/2 + 1/10) :=
        le_trans (le_abs_self _) h_fm_T
      have hI_lower : -(C_fm * T ^ ((1:ℝ)/2 + 1/10)) ≤ ∫ t in Ioc 1 T, inst.Z t :=
        le_trans (neg_le_neg h_fm_T) (neg_abs_le _)
      have hJ_upper : ∫ t in Ioc 1 T_min, inst.Z t ≤ K_fm := le_abs_self _
      have hJ_lower : -(K_fm) ≤ ∫ t in Ioc 1 T_min, inst.Z t := neg_abs_le _
      -- linarith can't decompose ∫₁Tm + ∫_{Tm}T (treats it as one atom).
      -- Use `set` to name each integral, then linarith sees simple ℝ variables.
      set A := ∫ t in Ioc 1 T, inst.Z t with hA_def
      set B := ∫ t in Ioc 1 T_min, inst.Z t with hB_def
      set C_int := ∫ t in Ioc T_min T, inst.Z t with hC_def
      -- h_split_Z now reads: A = B + C_int
      rw [abs_le]
      exact ⟨by linarith [h_split_Z], by linarith [h_split_Z]⟩
    rcases hsign with h_pos | h_neg
    · -- Z > 0: ∫ |Z| = ∫ Z ≤ |∫ Z| ≤ bound
      have h_nn : ∀ t ∈ Ioc T_min T, (0:ℝ) ≤ inst.Z t :=
        fun t ht => le_of_lt (h_pos t (lt_of_le_of_lt hTm_T0 ht.1))
      calc ∫ t in Ioc T_min T, |inst.Z t|
          = ∫ t in Ioc T_min T, inst.Z t :=
            setIntegral_congr_fun measurableSet_Ioc
              (fun t ht => abs_of_nonneg (h_nn t ht))
        _ ≤ |∫ t in Ioc T_min T, inst.Z t| := le_abs_self _
        _ ≤ C_fm * T ^ ((1:ℝ)/2 + 1/10) + K_fm := h_abs_int
    · -- Z < 0: ∫ |Z| = -(∫ Z) = |∫ Z| ≤ bound
      have h_np : ∀ t ∈ Ioc T_min T, inst.Z t ≤ 0 :=
        fun t ht => le_of_lt (h_neg t (lt_of_le_of_lt hTm_T0 ht.1))
      calc ∫ t in Ioc T_min T, |inst.Z t|
          = -(∫ t in Ioc T_min T, inst.Z t) := by
            rw [show -(∫ t in Ioc T_min T, inst.Z t) =
              ∫ t in Ioc T_min T, (fun t => -inst.Z t) t from by simp only [integral_neg]]
            exact setIntegral_congr_fun measurableSet_Ioc
              (fun t ht => abs_of_nonpos (h_np t ht))
        _ ≤ |∫ t in Ioc T_min T, inst.Z t| := neg_le_abs _
        _ ≤ C_fm * T ^ ((1:ℝ)/2 + 1/10) + K_fm := h_abs_int
  -- (f) Chain: c*T*log T ≤ K + C_cv*T^(7/20)*(C_fm*T^(6/10)+K_fm) ≤ K + D*T
  have h_rpow_prod : T ^ ((1:ℝ)/4 + 1/10) * T ^ ((1:ℝ)/2 + 1/10) = T ^ ((19:ℝ)/20) := by
    rw [← rpow_add (by linarith : (0:ℝ) < T)]; norm_num
  have h_rpow_le1 : T ^ ((19:ℝ)/20) ≤ T :=
    (rpow_le_rpow_of_exponent_le hT_ge1 (by norm_num : (19:ℝ)/20 ≤ 1)).trans (rpow_one T).le
  have h_rpow_le2 : T ^ ((1:ℝ)/4 + 1/10) ≤ T :=
    (rpow_le_rpow_of_exponent_le hT_ge1 (by norm_num : (1:ℝ)/4 + 1/10 ≤ 1)).trans (rpow_one T).le
  calc c * T * Real.log T
      ≤ ∫ t in Ioc 1 T, (inst.Z t)^2 := ha
    _ = K + ∫ t in Ioc T_min T, (inst.Z t)^2 := hb
    _ ≤ K + C_cv * T ^ ((1:ℝ)/4 + 1/10) * (∫ t in Ioc T_min T, |inst.Z t|) := by linarith [hd]
    _ ≤ K + C_cv * T ^ ((1:ℝ)/4 + 1/10) * (C_fm * T ^ ((1:ℝ)/2 + 1/10) + K_fm) := by
        nlinarith [he, show 0 ≤ C_cv * T ^ ((1:ℝ)/4 + 1/10) from by positivity]
    _ = K + C_cv * C_fm * (T ^ ((1:ℝ)/4 + 1/10) * T ^ ((1:ℝ)/2 + 1/10)) +
        C_cv * K_fm * T ^ ((1:ℝ)/4 + 1/10) := by ring
    _ = K + C_cv * C_fm * T ^ ((19:ℝ)/20) + C_cv * K_fm * T ^ ((1:ℝ)/4 + 1/10) := by
        rw [h_rpow_prod]
    _ ≤ K + C_cv * C_fm * T + C_cv * K_fm * T := by
        nlinarith [mul_le_mul_of_nonneg_left h_rpow_le1 (by positivity : 0 ≤ C_cv * C_fm),
                   mul_le_mul_of_nonneg_left h_rpow_le2 (by positivity : 0 ≤ C_cv * K_fm)]
    _ = K + D * T := by simp only [hD_def]; ring

end HardyInfiniteZerosV2
