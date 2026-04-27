/-
Analytic deep leaf for B1 (second moment), B3 (block structure), and B2 (first moment).

Three obligations from the Riemann-Siegel approximate functional equation:

1. **Second moment** (Hardy-Littlewood 1918):
   ∫₁ᵀ |ζ(½+it)|² dt = T log T + O(T)

2. **B3 block structure** (Siegel 1932 §3):
   Block integrals of ErrorTerm satisfy sign-definite corrections,
   antitone decay, and partial-block interpolation.

3. **B2 first moment** (Heath-Brown 1978):
   |∫₁ᵀ MainTerm(t) dt| ≤ C · T^{1/2+ε} for all ε > 0.

## Proof structure

### Second moment (obligation 1)
Derived from three sub-obligations:
  (a) RS pointwise bound: |ErrorTerm(t)| ≤ C · t^{-1/4} (from h_expansion)
  (b) ∫(MainTerm² − 2|S_N|²) = O(T) (OscPieceBigOAssembly)
  (c) ∫|S_N|² = ½T log T + O(T) (PROVED: PartialZetaMeanSquareCoeff)
Assembly:
  ∫|ζ|² = ∫(M+E)² = ∫M² + 2∫ME + ∫E²
  ∫M² = ∫(oscPiece + 2·partialMs) = O(T) + TlogT + O(T)   [by (b)+(c)]
  ∫2ME = O(T), ∫E² = O(T)                                  [by (a)]

### B3 block structure (obligation 2)
  Block change of variables + rsPsi positivity + correction decay.
  Delegated to B3BlockStructureFromExpansion.

### B2 first moment (obligation 3)
  Block decomposition + classical Z first moment.
  Delegated to B2FirstMomentFromExpansion.

## Derivation of B1

B1 (∫afeGap = O(T)) is derived in CombinedB1B3DeepLeaf from the
second moment via subtraction:
  ∫ afeGap = ∫|ζ|² − 2∫|S_N|² = (TlogT + O(T)) − (TlogT + O(T)) = O(T)

SORRY COUNT: 1 internal sorry (h_expansion, RS expansion from RSExpansionProof).
  Parts 2 and 3 delegated to B3BlockStructureFromExpansion and
  B2FirstMomentFromExpansion respectively (each with 1 sorry).
WARNING COUNT: 1

Reference: Hardy-Littlewood 1918; Siegel 1932 §3; Titchmarsh §7.2;
Montgomery-Vaughan §9.1; Heath-Brown 1978.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.Standalone.PartialZetaMeanSquareCoeff
import Littlewood.Bridge.HardyZTransfer
import Littlewood.Aristotle.HardyZRealV2
import Littlewood.Aristotle.Standalone.OscPieceBigOAssembly
import Littlewood.Aristotle.Standalone.B3BlockStructureFromExpansion
import Littlewood.Aristotle.Standalone.B2FirstMomentFromExpansion
import Littlewood.Aristotle.Standalone.RSExpansionProof
import Littlewood.Aristotle.Standalone.AnalyticAxioms

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.B1B3AnalyticDeepLeaf

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial Asymptotics
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
open Aristotle.ErrorTermExpansion
open Aristotle.Standalone.AtkinsonFormula
open Aristotle.Standalone.SiegelSaddleExpansionHyp
open Aristotle.Standalone.GabckePhaseCouplingHyp

variable [AtkinsonShiftedInversePhaseCellPrefixBoundHyp]
variable [SiegelSaddleExpansionHyp]
variable [GabckePhaseCouplingHyp]

/-! ## Infrastructure: zetaMsIntegrand = hardyZ² -/

/-- Pointwise: ‖ζ(½+it)‖² = (hardyZ t)².
    Uses hardyZV2 being real-valued and |hardyZV2| = ‖ζ‖. -/
theorem zetaMsIntegrand_eq_hardyZ_sq (t : ℝ) :
    zetaMsIntegrand t = (hardyZ t) ^ 2 := by
  unfold zetaMsIntegrand
  have h_re := HardyZTransfer.hardyZ_eq_hardyZV2_re t
  have h_im := hardyZV2_real t
  have h_norm := hardyZV2_abs_eq_zeta_abs t
  have h_sq : (hardyZ t) ^ 2 = ‖hardyZV2 t‖ ^ 2 := by
    rw [h_re]
    have h_eq : hardyZV2 t = ((hardyZV2 t).re : ℂ) :=
      Complex.ext rfl (by simp [h_im])
    conv_rhs => rw [h_eq, Complex.norm_real]
    exact (sq_abs _).symm
  have h_arg : (↑(1 / 2 : ℝ) : ℂ) + Complex.I * ↑t = 1 / 2 + Complex.I * ↑t := by
    push_cast; ring
  rw [h_sq, h_norm, h_arg]

/-! ## Infrastructure: MainTerm pointwise bound -/

/-- |MainTerm(t)| ≤ 4·t^{1/4} for t ≥ 0. -/
theorem mainTerm_abs_le (t : ℝ) (ht : 0 ≤ t) :
    |MainTerm t| ≤ 4 * t ^ ((1 : ℝ) / 4) := by
  unfold MainTerm
  set N := Nat.floor (Real.sqrt (t / (2 * Real.pi)))
  have h_neg_eq : ∀ n : ℕ, (↑n + 1 : ℝ) ^ (-(1/2 : ℝ)) = (↑n + 1 : ℝ) ^ ((-1 : ℝ)/2) := by
    intro n; congr 1; ring
  simp_rw [h_neg_eq]
  have h_step1 : |2 * ∑ n ∈ Finset.range N,
      ((↑n + 1 : ℝ) ^ ((-1 : ℝ)/2)) * Real.cos (hardyTheta t - t * Real.log (↑n + 1))|
    ≤ 2 * ∑ n ∈ Finset.range N, ((↑n + 1 : ℝ) ^ ((-1 : ℝ)/2)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    gcongr
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum fun n _ => by
      have hnn : (0 : ℝ) ≤ (↑n + 1) ^ ((-1 : ℝ)/2) :=
        Real.rpow_nonneg (by positivity : (0:ℝ) ≤ ↑n + 1) _
      rw [abs_mul]
      calc |(↑n + 1) ^ ((-1 : ℝ)/2)| * |Real.cos _|
          ≤ |(↑n + 1) ^ ((-1 : ℝ)/2)| * 1 := by gcongr; exact abs_cos_le_one _
        _ = (↑n + 1) ^ ((-1 : ℝ)/2) := by rw [mul_one, abs_of_nonneg hnn]
  have h_step2 : 2 * ∑ n ∈ Finset.range N, ((↑n + 1 : ℝ) ^ ((-1 : ℝ)/2))
    ≤ 4 * Real.sqrt (Real.sqrt (t / (2 * Real.pi))) := by
    have h1 := sum_rpow_neg_half_le N
    have h2 : (N : ℝ) ≤ Real.sqrt (t / (2 * Real.pi)) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    linarith [Real.sqrt_le_sqrt h2]
  have h_step3 : Real.sqrt (Real.sqrt (t / (2 * Real.pi))) ≤ t ^ ((1 : ℝ)/4) := by
    have hpi : 1 ≤ 2 * Real.pi := by have := Real.pi_gt_three; linarith
    have h_le : Real.sqrt (Real.sqrt (t / (2 * Real.pi))) ≤ Real.sqrt (Real.sqrt t) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (div_le_self ht hpi))
    have h_eq : Real.sqrt (Real.sqrt t) = t ^ ((1 : ℝ)/4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
      norm_num
    linarith
  linarith

/-! ## RS pointwise bound from expansion -/

open Aristotle.RSBlockParam Aristotle.HardyNProperties
open Aristotle.Standalone.OscPieceBigOAssembly (exists_block_of_ge_hardyStart0)

/-- On [1, hardyStart 0), MainTerm = 0 (empty sum since hardyN = 0). -/
private theorem mainTerm_eq_zero_below_hardyStart0 (t : ℝ)
    (ht : t < hardyStart 0) : MainTerm t = 0 := by
  unfold MainTerm
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_div : t / (2 * Real.pi) < 1 := by
    rw [div_lt_one hpi]
    rw [hardyStart_formula] at ht
    have : ((0 : ℕ) + 1 : ℝ) ^ 2 = 1 := by push_cast; norm_num
    rw [this] at ht; linarith
  have h_sqrt_lt : Real.sqrt (t / (2 * Real.pi)) < 1 := by
    by_cases h_nn : 0 ≤ t / (2 * Real.pi)
    · calc Real.sqrt (t / (2 * Real.pi)) < Real.sqrt 1 := Real.sqrt_lt_sqrt h_nn h_div
        _ = 1 := Real.sqrt_one
    · push_neg at h_nn
      calc Real.sqrt (t / (2 * Real.pi)) = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt h_nn)
        _ < 1 := one_pos
  have h_floor : Nat.floor (Real.sqrt (t / (2 * Real.pi))) = 0 :=
    Nat.floor_eq_zero.mpr h_sqrt_lt
  simp [h_floor]

/-- ErrorTerm = hardyZ on [1, hardyStart 0). -/
private theorem errorTerm_eq_hardyZ_below (t : ℝ)
    (ht : t < hardyStart 0) : ErrorTerm t = hardyZ t := by
  unfold ErrorTerm; rw [mainTerm_eq_zero_below_hardyStart0 t ht]; ring

/-- hardyZ is continuous. -/
private theorem continuous_hardyZ_real : Continuous hardyZ := by
  have h_eq : hardyZ = fun t => (hardyZV2 t).re :=
    funext HardyZTransfer.hardyZ_eq_hardyZV2_re
  rw [h_eq]; exact Complex.continuous_re.comp continuous_hardyZV2

/-- The RS pointwise bound |ErrorTerm(t)| ≤ C·t^{-1/4} follows from the
    block-wise RS expansion via triangle inequality.
    - For t >= hardyStart 0: use the expansion on the containing block
    - For t in [1, hardyStart 0]: ErrorTerm = hardyZ, bounded by compactness -/
theorem rs_pointwise_bound_of_expansion
    (h_exp : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t < hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    ∃ C_rs > (0 : ℝ), ∀ t : ℝ, t ≥ 1 →
      |ErrorTerm t| ≤ C_rs * t ^ (-(1 : ℝ)/4) := by
  obtain ⟨C_R, hCR_pos, h_expansion⟩ := h_exp
  -- Step 1: Compact bound on [1, hardyStart 0]
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := hardyStart 0)).exists_bound_of_continuousOn
    continuous_hardyZ_real.continuousOn
  -- Step 2: Combine into a single constant
  set C_block := (2 * Real.pi) ^ ((1 : ℝ)/4) + C_R
  set C_compact := M₀ * (hardyStart 0) ^ ((1 : ℝ)/4)
  refine ⟨max C_block C_compact + 1, by positivity, fun t ht => ?_⟩
  by_cases h_large : hardyStart 0 ≤ t
  · -- Case: t >= hardyStart 0. Use the block expansion.
    obtain ⟨K, hK_lo, hK_hi⟩ := exists_block_of_ge_hardyStart0 t h_large
    -- Promote ≤ to < via case split (Icc→Ico): at boundary use next block
    obtain ⟨k, hk_lo, hk_hi⟩ : ∃ k, hardyStart k ≤ t ∧ t < hardyStart (k + 1) := by
      rcases lt_or_eq_of_le hK_hi with h_lt | h_eq
      · exact ⟨K, hK_lo, h_lt⟩
      · exact ⟨K + 1, h_eq ▸ le_refl _,
              h_eq ▸ Aristotle.Standalone.RSExpansionProof.hardyStart_lt_succ _⟩
    have ht_pos : (0 : ℝ) < t := by linarith
    have h_exp_k := h_expansion k t hk_lo hk_hi ht_pos
    -- |ErrorTerm(t)| <= |leading| + |remainder|
    have h_tri : |ErrorTerm t| ≤
        |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t)| +
        C_R * t ^ (-(3 : ℝ) / 4) := by
      have h1 : |ErrorTerm t| = |(ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)) + ((-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t))| := by ring_nf
      calc |ErrorTerm t|
          = |(ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t)) + ((-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t))| := h1
        _ ≤ |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t)| +
            |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t)| := abs_add_le _ _
        _ ≤ C_R * t ^ (-(3 : ℝ) / 4) +
            |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t)| := by linarith [h_exp_k]
        _ = |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t)| + C_R * t ^ (-(3 : ℝ) / 4) := by ring
    -- Bound the leading term
    have h_lead : |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
        rsPsi (blockParam k t)| ≤ (2 * Real.pi) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) := by
      have h_neg1 : |(-1 : ℝ) ^ k| = 1 := by simp [abs_pow, abs_neg, abs_one]
      have h_rsPsi : |rsPsi (blockParam k t)| ≤ 1 := by
        unfold rsPsi; exact Real.abs_cos_le_one _
      have h_factor : (2 * Real.pi / t) ^ ((1 : ℝ) / 4) =
          (2 * Real.pi) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) := by
        rw [show 2 * Real.pi / t = 2 * Real.pi * t⁻¹ from div_eq_mul_inv _ _,
            Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (inv_nonneg.mpr ht_pos.le)]
        congr 1
        rw [show (-(1:ℝ)/4) = -((1:ℝ)/4) from by ring, Real.rpow_neg ht_pos.le,
            Real.inv_rpow ht_pos.le]
      calc |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t)|
          = |(-1 : ℝ) ^ k| * |(2 * Real.pi / t) ^ ((1 : ℝ) / 4)| * |rsPsi (blockParam k t)| := by
            rw [abs_mul, abs_mul]
        _ = 1 * |(2 * Real.pi / t) ^ ((1 : ℝ) / 4)| * |rsPsi (blockParam k t)| := by
            rw [h_neg1]
        _ ≤ 1 * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * 1 := by
            have h_rpow_nn : 0 ≤ (2 * Real.pi / t) ^ ((1 : ℝ) / 4) :=
              Real.rpow_nonneg (div_nonneg (by positivity) ht_pos.le) _
            rw [abs_of_nonneg h_rpow_nn]
            exact mul_le_mul_of_nonneg_left h_rsPsi (by linarith)
        _ = (2 * Real.pi) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) := by
            rw [one_mul, mul_one, h_factor]
    -- Combine: t^{-3/4} <= t^{-1/4} for t >= 1
    have h_rpow_mono : t ^ (-(3 : ℝ)/4) ≤ t ^ (-(1 : ℝ)/4) :=
      Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
    calc |ErrorTerm t|
        ≤ (2 * Real.pi) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) + C_R * t ^ (-(3 : ℝ)/4) := by
          linarith [h_tri, h_lead]
      _ ≤ (2 * Real.pi) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) + C_R * t ^ (-(1 : ℝ)/4) := by
          linarith [mul_le_mul_of_nonneg_left h_rpow_mono hCR_pos.le]
      _ = C_block * t ^ (-(1 : ℝ)/4) := by simp only [C_block]; ring
      _ ≤ (max C_block C_compact + 1) * t ^ (-(1 : ℝ)/4) := by
          have : 0 ≤ t ^ (-(1 : ℝ)/4) := Real.rpow_nonneg (by linarith) _
          nlinarith [le_max_left C_block C_compact]
  · -- Case: t < hardyStart 0. ErrorTerm = hardyZ here, bounded by compactness.
    push_neg at h_large
    have ht_in : t ∈ Icc (1 : ℝ) (hardyStart 0) := ⟨ht, le_of_lt h_large⟩
    have h_eq : ErrorTerm t = hardyZ t := errorTerm_eq_hardyZ_below t h_large
    have h_bound_Z : ‖hardyZ t‖ ≤ M₀ := hM₀ t ht_in
    rw [Real.norm_eq_abs] at h_bound_Z
    have h_bound : |ErrorTerm t| ≤ M₀ := by rw [h_eq]; exact h_bound_Z
    have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have h_rpow_inv : t ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) = 1 := by
      rw [show (-(1 : ℝ)/4) = -((1 : ℝ)/4) from by ring,
          ← Real.rpow_add ht_pos, add_neg_cancel, Real.rpow_zero]
    have h_t14_le : t ^ ((1 : ℝ)/4) ≤ (hardyStart 0) ^ ((1 : ℝ)/4) :=
      Real.rpow_le_rpow (by linarith) (le_of_lt h_large) (by norm_num)
    calc |ErrorTerm t|
        ≤ M₀ := h_bound
      _ = M₀ * (t ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4)) := by rw [h_rpow_inv, mul_one]
      _ = M₀ * t ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) := by ring
      _ ≤ M₀ * (hardyStart 0) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) := by
          have h_nn : 0 ≤ t ^ (-(1 : ℝ)/4) := Real.rpow_nonneg (by linarith) _
          have hM₀_nn : 0 ≤ M₀ := le_trans (abs_nonneg _) h_bound
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_t14_le hM₀_nn) h_nn
      _ = C_compact * t ^ (-(1 : ℝ)/4) := by simp only [C_compact]
      _ ≤ (max C_block C_compact + 1) * t ^ (-(1 : ℝ)/4) := by
          have : 0 ≤ t ^ (-(1 : ℝ)/4) := Real.rpow_nonneg (by linarith) _
          nlinarith [le_max_right C_block C_compact]

/-! ## Main theorem -/

/-- **Unified analytic deep leaf**: three obligations from the RS approximate
    functional equation and oscillatory sum analysis.

    Part 1 (Second moment): ∫₁ᵀ |ζ(½+it)|² dt = T log T + O(T).
      Derived from three sub-goals:
      (a) RS bound |ErrorTerm| ≤ C·t^{-1/4} (Siegel 1932) — sorry,
      (b) VdC oscillatory integral O(T) — sorry,
      (c) ∫|S_N|² = ½TlogT + O(T) — PROVED.

    Part 2 (B3): Block integral sign structure (Siegel 1932 §3).
      Block integrals decompose via rsPsi with ≥ 0 correction — sorry.

    Part 3 (B2): First moment bound |∫₁ᵀ MainTerm(t) dt| ≤ C·T^{1/2+ε}.
      Delegated to B2FirstMomentFromExpansion via block decomposition
      + classical Z first moment (Heath-Brown 1978, Titchmarsh §4.15).
      Replaces the previously false B2TailVdcDeepLeaf route (VdC with
      √(n+1) tail width is mathematically incorrect near stationary points).

    B1 (∫ afeGap = O(T)) is derived in CombinedB1B3DeepLeaf from Part 1
    combined with the proved ∫|S_N|² = ½T log T + O(T).

    Reference: Hardy-Littlewood 1918; Siegel 1932; Titchmarsh §7.2;
    Montgomery-Vaughan §9.1; Heath-Brown 1978. -/
theorem b1_b3_analytic_deep_leaf :
    -- Part 1: Second moment ∫|ζ(½+it)|² = T log T + O(T)
    ((fun T => (∫ t in (1:ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
      =O[atTop] (fun T => T)) ∧
    -- Part 2: B3 block structure
    ((let A_val := 4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1, rsPsi p
      let c_fn := fun k : ℕ =>
        (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          - A_val * Real.sqrt ((k : ℝ) + 1)
      (∀ k : ℕ, 0 ≤ c_fn k) ∧
      AntitoneOn c_fn (Ici (1 : ℕ)) ∧
      ∃ C₂ : ℝ, C₂ ≥ 0 ∧
      (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
        ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
          |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
            - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                     ErrorTerm t)| ≤ C₂)) ∧
    -- Part 3: B2 first moment bound (Heath-Brown 1978)
    (∀ ε : ℝ, ε > 0 →
      ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
        |∫ t in Set.Ioc 1 T, MainTerm t| ≤ C * T ^ (1 / 2 + ε))) := by
  -- ═══════════════════════════════════════════════════════
  -- Single analytic sorry: RS expansion (Siegel 1932 §3)
  -- ═══════════════════════════════════════════════════════
  -- Strong form with C_R bound (for B3 block structure)
  have h_expansion_strong : ∃ C_R : ℝ, 0 < C_R ∧ C_R ≤ 1 / 2 ∧ ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t < hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4) :=
    Aristotle.Standalone.RSExpansionProof.rs_expansion_for_b1b3
  -- Weak form without C_R bound (for pointwise bound derivation)
  have h_expansion : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t < hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4) := by
    obtain ⟨C_R, hpos, _, h⟩ := h_expansion_strong; exact ⟨C_R, hpos, h⟩
  refine ⟨?_, ?_, ?_⟩
  · -- ═══════════════════════════════════════════════════════
    -- Part 1: Second moment from three sub-goals
    -- ═══════════════════════════════════════════════════════
    -- (a) RS pointwise bound — DERIVED from expansion
    have h_rs : ∃ (C_rs : ℝ), C_rs > 0 ∧
        ∀ (t : ℝ), t ≥ 1 →
          |ErrorTerm t| ≤ C_rs * t ^ (-(1:ℝ)/4) :=
      rs_pointwise_bound_of_expansion h_expansion
    -- (b) VdC oscillatory cancellation: ∫(M² - 2·partialMs) = O(T)
    have h_osc : (fun T => ∫ t in (1:ℝ)..T,
        ((MainTerm t) ^ 2 - 2 * partialMsIntegrand t))
      =O[atTop] (fun T => T) :=
        Aristotle.Standalone.OscPieceBigOAssembly.osc_piece_integral_big_O
    -- (c) Partial zeta mean square (PROVED)
    have h_partial :=
      Aristotle.Standalone.PartialZetaMeanSquareCoeff.partial_zeta_mean_square_half_coeff
    -- ── Assembly: derive ∫ zetaMsIntegrand - TlogT = O(T) ──
    -- Strategy: rewrite the integral pointwise and split into four O(T) pieces.
    obtain ⟨C_rs, hC_pos, h_rs_bound⟩ := h_rs
    -- Key pointwise identity: zetaMsIntegrand = M² + 2ME + E²
    have h_pw : ∀ t, zetaMsIntegrand t =
        (MainTerm t ^ 2 - 2 * partialMsIntegrand t) +
        2 * partialMsIntegrand t +
        2 * MainTerm t * ErrorTerm t +
        ErrorTerm t ^ 2 := by
      intro t
      rw [zetaMsIntegrand_eq_hardyZ_sq]
      unfold ErrorTerm; ring
    -- Rewrite integral via pointwise identity
    have h_integral_eq : (fun T => (∫ t in (1:ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
        =ᶠ[atTop] (fun T =>
        (∫ t in (1:ℝ)..T, (MainTerm t ^ 2 - 2 * partialMsIntegrand t)) +
        (2 * (∫ t in (1:ℝ)..T, partialMsIntegrand t) - T * Real.log T) +
        (∫ t in (1:ℝ)..T, 2 * MainTerm t * ErrorTerm t) +
        (∫ t in (1:ℝ)..T, ErrorTerm t ^ 2)) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      -- Integral congr via pointwise identity
      have h_congr : ∫ t in (1:ℝ)..T, zetaMsIntegrand t =
          ∫ t in (1:ℝ)..T, ((MainTerm t ^ 2 - 2 * partialMsIntegrand t) +
          2 * partialMsIntegrand t +
          2 * MainTerm t * ErrorTerm t +
          ErrorTerm t ^ 2) :=
        intervalIntegral.integral_congr (fun t _ => h_pw t)
      rw [h_congr]
      -- Split integral by linearity (integrability of pieces)
      have hP_ii := intervalIntegrable_partialMsIntegrand T
      -- Integrability of M², 2ME, E² on [1,T] from bounded·integrable
      -- Helper: MainTerm and ErrorTerm are measurable
      have hM_meas : Measurable MainTerm := MainTerm_eq_hardySum ▸ hardySum_measurable
      have hZ_meas : Measurable hardyZ := by
        have h_eq : hardyZ = fun t => (hardyZV2 t).re :=
          funext HardyZTransfer.hardyZ_eq_hardyZV2_re
        rw [h_eq]
        exact (Complex.continuous_re.comp continuous_hardyZV2).measurable
      have hE_meas : Measurable ErrorTerm := by
        show Measurable (fun t => hardyZ t - MainTerm t)
        exact hZ_meas.sub (MainTerm_eq_hardySum ▸ hardySum_measurable)
      -- Bounds on Ioc 1 T
      have hM_bdd : ∀ t ∈ Ioc 1 T, ‖MainTerm t‖ ≤ 4 * T ^ ((1:ℝ)/4) := fun t ht => by
        rw [Real.norm_eq_abs]
        exact (mainTerm_abs_le t (by linarith [ht.1])).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by linarith [ht.1]) ht.2 (by norm_num))
            (by norm_num))
      have hE_bdd : ∀ t ∈ Ioc 1 T, ‖ErrorTerm t‖ ≤ C_rs := fun t ht => by
        rw [Real.norm_eq_abs]
        exact (h_rs_bound t (by linarith [ht.1])).trans
          (mul_le_of_le_one_right hC_pos.le
            (rpow_le_one_of_one_le_of_nonpos (by linarith [ht.1]) (by norm_num)))
      -- M² integrable: MainTerm is integrable and bounded → M*M integrable
      have hMsq_ii : IntervalIntegrable (fun t => MainTerm t ^ 2) volume 1 T := by
        rw [show (fun t => MainTerm t ^ 2) = (fun t => MainTerm t * MainTerm t)
            from by ext; ring]
        rw [intervalIntegrable_iff, Set.uIoc_of_le hT]
        exact (mainTerm_integrable T).bdd_mul
          (hM_meas.aestronglyMeasurable.restrict)
          (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioc)
             fun t ht => hM_bdd t ht)
      -- 2ME integrable: ErrorTerm integrable, 2*MainTerm bounded
      have hME_ii : IntervalIntegrable (fun t => 2 * MainTerm t * ErrorTerm t) volume 1 T := by
        rw [show (fun t => 2 * MainTerm t * ErrorTerm t) =
            (fun t => (2 * MainTerm t) * ErrorTerm t) from by ext; ring]
        rw [intervalIntegrable_iff, Set.uIoc_of_le hT]
        exact (errorTerm_integrable T).bdd_mul
          ((measurable_const.mul hM_meas).aestronglyMeasurable.restrict)
          (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioc) fun t ht => by
             rw [norm_mul, Real.norm_ofNat]
             exact mul_le_mul_of_nonneg_left (hM_bdd t ht) (by norm_num))
      -- E² integrable: ErrorTerm integrable and bounded → E*E integrable
      have hEsq_ii : IntervalIntegrable (fun t => ErrorTerm t ^ 2) volume 1 T := by
        rw [show (fun t => ErrorTerm t ^ 2) = (fun t => ErrorTerm t * ErrorTerm t)
            from by ext; ring]
        rw [intervalIntegrable_iff, Set.uIoc_of_le hT]
        exact (errorTerm_integrable T).bdd_mul
          (hE_meas.aestronglyMeasurable.restrict)
          (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioc)
             fun t ht => hE_bdd t ht)
      -- oscPiece = M² - 2P is integrable
      have hOsc_ii : IntervalIntegrable
          (fun t => MainTerm t ^ 2 - 2 * partialMsIntegrand t) volume 1 T :=
        hMsq_ii.sub (hP_ii.const_mul 2)
      -- Split: ∫(osc + 2P + 2ME + E²) = ∫osc + 2∫P + ∫2ME + ∫E²
      -- Use integral linearity step by step
      conv_lhs => rw [show (fun t => (MainTerm t ^ 2 - 2 * partialMsIntegrand t) +
          2 * partialMsIntegrand t + 2 * MainTerm t * ErrorTerm t + ErrorTerm t ^ 2) =
          (fun t => (MainTerm t ^ 2 - 2 * partialMsIntegrand t +
          2 * partialMsIntegrand t) + (2 * MainTerm t * ErrorTerm t + ErrorTerm t ^ 2))
          from by ext; ring]
      rw [intervalIntegral.integral_add
            (hOsc_ii.add (hP_ii.const_mul 2))
            (hME_ii.add hEsq_ii)]
      conv_lhs => rw [show (fun t => MainTerm t ^ 2 - 2 * partialMsIntegrand t +
          2 * partialMsIntegrand t) =
          (fun t => (MainTerm t ^ 2 - 2 * partialMsIntegrand t) +
          2 * partialMsIntegrand t)
          from by ext; ring]
      rw [intervalIntegral.integral_add hOsc_ii (hP_ii.const_mul 2)]
      conv_lhs => rw [show (fun t => 2 * MainTerm t * ErrorTerm t + ErrorTerm t ^ 2) =
          (fun t => (2 * MainTerm t * ErrorTerm t) + (ErrorTerm t ^ 2))
          from by ext; ring]
      rw [intervalIntegral.integral_add hME_ii hEsq_ii,
          intervalIntegral.integral_const_mul 2 _]
      ring
    -- ∫ 2ME = O(T) from RS bound + mainTerm_abs_le
    have h_cross : (fun T => ∫ t in (1:ℝ)..T, 2 * MainTerm t * ErrorTerm t)
        =O[atTop] (fun T => T) := by
      refine IsBigO.of_bound (8 * C_rs) ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      -- Pointwise: |2ME(t)| ≤ 8C_rs for t ≥ 1 (via t^{1/4}·t^{-1/4} = 1)
      have h_2me_bdd : ∀ x ∈ Set.uIoc 1 T, ‖2 * MainTerm x * ErrorTerm x‖ ≤ 8 * C_rs := by
        intro t ht
        rw [Set.uIoc_of_le hT] at ht
        have ht1 : t ≥ 1 := by linarith [ht.1]
        have ht_pos : (0:ℝ) < t := by linarith
        rw [Real.norm_eq_abs]
        have hM := mainTerm_abs_le t (by linarith)
        have hE := h_rs_bound t ht1
        calc |2 * MainTerm t * ErrorTerm t|
            = 2 * |MainTerm t| * |ErrorTerm t| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
          _ ≤ 2 * (4 * t ^ ((1:ℝ)/4)) * (C_rs * t ^ (-(1:ℝ)/4)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) hE
                (abs_nonneg _) (by positivity)
          _ = 8 * C_rs * (t ^ ((1:ℝ)/4) * t ^ (-(1:ℝ)/4)) := by ring
          _ = 8 * C_rs := by
              rw [← Real.rpow_add ht_pos]; norm_num
      -- ‖∫ 2ME‖ ≤ 8C_rs · |T-1| ≤ 8C_rs · |T|
      calc |∫ t in (1:ℝ)..T, 2 * MainTerm t * ErrorTerm t|
          ≤ (8 * C_rs) * |T - 1| :=
            intervalIntegral.norm_integral_le_of_norm_le_const h_2me_bdd
        _ ≤ (8 * C_rs) * |T| :=
            mul_le_mul_of_nonneg_left (by
              rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith)
              (by positivity)
    -- ∫ E² = O(T) from RS bound
    have h_errSq : (fun T => ∫ t in (1:ℝ)..T, ErrorTerm t ^ 2)
        =O[atTop] (fun T => T) := by
      refine IsBigO.of_bound (C_rs ^ 2) ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      -- Pointwise: E²(t) ≤ C_rs² for t ∈ uIoc 1 T
      have h_esq_bdd : ∀ x ∈ Set.uIoc 1 T, ‖ErrorTerm x ^ 2‖ ≤ C_rs ^ 2 := by
        intro t ht
        rw [Set.uIoc_of_le hT] at ht
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 : |ErrorTerm t| ≤ C_rs :=
          (h_rs_bound t (by linarith [ht.1])).trans
            (mul_le_of_le_one_right hC_pos.le
              (rpow_le_one_of_one_le_of_nonpos (by linarith [ht.1]) (by norm_num)))
        calc ErrorTerm t ^ 2 = |ErrorTerm t| ^ 2 := (sq_abs _).symm
          _ ≤ C_rs ^ 2 := by
              exact sq_le_sq' (by linarith [abs_nonneg (ErrorTerm t)]) h1
      calc |∫ t in (1:ℝ)..T, ErrorTerm t ^ 2|
          ≤ (C_rs ^ 2) * |T - 1| :=
            intervalIntegral.norm_integral_le_of_norm_le_const h_esq_bdd
        _ ≤ (C_rs ^ 2) * |T| :=
            mul_le_mul_of_nonneg_left (by
              rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith)
              (by positivity)
    -- 2·∫P - TlogT = O(T)
    have h_2partial : (fun T => 2 * (∫ t in (1:ℝ)..T, partialMsIntegrand t)
        - T * Real.log T) =O[atTop] (fun T => T) := by
      have : (fun T => 2 * (∫ t in (1:ℝ)..T, partialMsIntegrand t)
          - T * Real.log T) =
        (fun T => 2 * ((∫ t in (1:ℝ)..T, partialMsIntegrand t)
          - 2⁻¹ * T * Real.log T)) := by ext T; ring
      rw [this]
      exact h_partial.const_mul_left 2
    -- Combine: f = f₁ + f₂ + f₃ + f₄ where each fᵢ = O(T)
    have h_sum := ((h_osc.add h_2partial).add h_cross).add h_errSq
    exact (isBigO_congr h_integral_eq EventuallyEq.rfl).mpr h_sum
  · -- ═══════════════════════════════════════════════════════
    -- Part 2: B3 block structure (Siegel 1932 §3)
    -- Derived from h_expansion via change of variables + rsPsi analysis.
    -- See B3BlockStructureFromExpansion.lean for the proof sketch.
    -- ═══════════════════════════════════════════════════════
    exact Aristotle.Standalone.B3BlockStructureFromExpansion.b3_block_structure_core
      h_expansion_strong
      Aristotle.Standalone.RSExpansionProof.rs_block_antitone
      Aristotle.Standalone.RSExpansionProof.rs_block_interpolation
  · -- ═══════════════════════════════════════════════════════
    -- Part 3: B2 first moment bound (Heath-Brown 1978)
    -- |∫₁ᵀ MainTerm(t) dt| ≤ C·T^{1/2+ε}
    -- Derived from h_expansion via block decomposition + classical Z first moment.
    -- See B2FirstMomentFromExpansion.lean for the proof structure.
    -- ═══════════════════════════════════════════════════════
    exact Aristotle.Standalone.B2FirstMomentFromExpansion.b2_first_moment_core h_expansion

end Aristotle.Standalone.B1B3AnalyticDeepLeaf
