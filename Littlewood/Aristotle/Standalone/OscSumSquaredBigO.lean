/-
Van der Corput bounds for product modes F_j · F_l of Hardy cosine exponentials.

Proves that the product F_j · F_l satisfies the angular velocity ODE required
by ComplexVdC, and derives per-block integral bounds via the first derivative test.

## Key results

### Angular velocity infrastructure
- `product_angular_velocity`: F_j·F_l has angular velocity ω_j+ω_l
- `norm_product_hardyCosExp`: ‖F_j·F_l‖ ≤ 1
- `productOmega_eq`: ω_{j,l} = modeOmega j + modeOmega l
- `differentiable_productOmega`: productOmega is differentiable
- `deriv_productOmega`: ω' = 2·θ''
- `continuous_deriv_productOmega`: ω' is continuous
- `deriv_productOmega_nonneg`: ω' ≥ 0 for t > 0

### Lower bounds and VdC application
- `productOmega_lower_bound_eventually`: for k ≥ K₀, j < k, l < k, on block k:
    ω_{j,l}(t) ≥ log((k+1)²/((j+1)(l+1)))/2
- `product_integral_vdc_bound`: ∃ C > 0, ‖∫_{block k} F_j·F_l‖ ≤ C/log((k+1)²/((j+1)(l+1)))
    for all j < k, l < k, k ≥ 1

## Application path to ∫Re(oscSum²) = O(T)

These per-block bounds can be summed over pairs and blocks to prove
∫₁ᵀ Re(oscSum²) = O(T). The full argument (not yet formalized) uses:
1. Fix pair (j,l) with j ≤ l < N(T), integrate over valid range [hardyStart(l), T]
2. Off-diagonal (j < l): VdC with ω ≥ log((l+1)/(j+1))/2 gives O(1/log ratio)
3. Diagonal (j = l): split at stationary point, trivial + VdC gives O(j)
4. Double sum: off-diagonal O(N·log N) = O(√T·log T), diagonal O(N²) = O(T)

SORRY COUNT: 0

Reference: Plan §Phase 1; Hardy-Littlewood 1918; Montgomery-Vaughan §9.1.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ComplexVdC
import Littlewood.Aristotle.ThetaDerivMonotone
import Littlewood.Aristotle.ThetaDerivAsymptotic
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.HardyCosExpOmega
import Littlewood.Aristotle.OffResonanceSmoothVdC

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.OscSumSquaredBigO

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.HardyNProperties
open Aristotle.HardyCosExpOmega
open Aristotle.OffResonanceSmoothVdC
open ThetaDerivAsymptotic ThetaDerivMonotone
open HardyCosSmooth

-- ============================================================
-- Section 1: Product angular velocity
-- ============================================================

/-- Product of two hardyCosExp modes has unit norm. -/
lemma norm_product_hardyCosExp (j l : ℕ) (t : ℝ) :
    ‖hardyCosExp j t * hardyCosExp l t‖ ≤ 1 := by
  rw [norm_mul, norm_hardyCosExp j t, norm_hardyCosExp l t]
  norm_num

/-- Product F_j · F_l has angular velocity ω_j + ω_l = 2θ'(t) − log((j+1)(l+1)).

    Proof: (F_j·F_l)' = F_j'·F_l + F_j·F_l' = i(ω_j+ω_l)·F_j·F_l
    since F_j' = iω_j·F_j and F_l' = iω_l·F_l. -/
theorem product_angular_velocity (j l : ℕ) (t : ℝ) :
    HasDerivAt (fun x => hardyCosExp j x * hardyCosExp l x)
      (Complex.I * ↑(2 * thetaDeriv t - Real.log (↑(j + 1)) - Real.log (↑(l + 1)))
        * (hardyCosExp j t * hardyCosExp l t)) t := by
  have hj := hardyCosExp_angular_velocity j t
  have hl := hardyCosExp_angular_velocity l t
  have hprod := hj.mul hl
  convert hprod using 1
  simp only [Complex.ofReal_sub]
  push_cast
  ring

/-- The angular velocity of the product mode. -/
def productOmega (j l : ℕ) (t : ℝ) : ℝ :=
  2 * thetaDeriv t - Real.log (↑(j + 1)) - Real.log (↑(l + 1))

lemma productOmega_eq (j l : ℕ) (t : ℝ) :
    productOmega j l t = modeOmega j t + modeOmega l t := by
  unfold productOmega modeOmega
  push_cast
  ring

/-- The product angular velocity is differentiable. -/
lemma differentiable_productOmega (j l : ℕ) :
    Differentiable ℝ (productOmega j l) := by
  intro t
  show DifferentiableAt ℝ (fun t => 2 * thetaDeriv t - Real.log (↑(j + 1)) - Real.log (↑(l + 1))) t
  exact ((thetaDeriv_hasDerivAt t).differentiableAt.const_mul 2).sub
    (differentiableAt_const _) |>.sub (differentiableAt_const _)

/-- The derivative of productOmega is nonneg for t > 0.
    Since ω' ≥ 0, the angular velocity is nondecreasing. -/
lemma deriv_productOmega_nonneg (j l : ℕ) (t : ℝ) (ht : 0 < t) :
    0 ≤ deriv (productOmega j l) t := by
  -- productOmega j l t = 2·θ'(t) - log(j+1) - log(l+1)
  -- deriv = 2·θ''(t) ≥ 0 since θ'' > 0
  have h_deriv : deriv (productOmega j l) t = 2 * deriv thetaDeriv t := by
    unfold productOmega
    simp [deriv_const_mul, deriv_sub, deriv_const,
      (thetaDeriv_hasDerivAt t).differentiableAt]
  rw [h_deriv]
  exact mul_nonneg (by norm_num) (deriv_thetaDeriv_nonneg t ht)

-- ============================================================
-- Section 2: Derivative and continuity of productOmega
-- ============================================================

/-- The derivative of productOmega equals 2·θ''(t). -/
lemma deriv_productOmega (j l : ℕ) (t : ℝ) :
    deriv (productOmega j l) t = 2 * deriv thetaDeriv t := by
  unfold productOmega
  simp [deriv_const_mul, deriv_sub, deriv_const,
    (thetaDeriv_hasDerivAt t).differentiableAt]

/-- The derivative of productOmega is continuous. -/
lemma continuous_deriv_productOmega (j l : ℕ) : Continuous (deriv (productOmega j l)) := by
  have h : deriv (productOmega j l) = fun t => 2 * deriv thetaDeriv t := by
    ext t; exact deriv_productOmega j l t
  rw [h]
  exact continuous_const.mul continuous_deriv_thetaDeriv

-- ============================================================
-- Section 3: Lower bound on productOmega for off-diagonal pairs
-- ============================================================

/-- hardyStart k is positive for all k. -/
private lemma hardyStart_pos' (k : ℕ) : 0 < hardyStart k := by
  rw [hardyStart_formula]; positivity

/-- For sufficiently large k, with j < k and l < k, on block k:
    productOmega j l t ≥ log((k+1)²/((j+1)(l+1)))/2.

    Follows from modeOmega_lower_bound_eventually applied to each factor. -/
lemma productOmega_lower_bound_eventually :
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → ∀ j l : ℕ, j < k → l < k →
      ∀ t : ℝ, hardyStart k ≤ t → t ≤ hardyStart (k + 1) →
        Real.log (((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) / 2
          ≤ productOmega j l t := by
  obtain ⟨K₀, hK₀⟩ := modeOmega_lower_bound_eventually
  refine ⟨K₀, fun k hk j l hjk hlk t ht_lo ht_hi => ?_⟩
  rw [productOmega_eq]
  have hj := hK₀ k hk j hjk t ht_lo ht_hi
  have hl := hK₀ k hk l hlk t ht_lo ht_hi
  have hj1_pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hl1_pos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  -- (k+1)²/((j+1)(l+1)) = ((k+1)/(j+1)) · ((k+1)/(l+1))
  have h_eq : ((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1)) =
      ((k : ℝ) + 1) / ((j : ℝ) + 1) * (((k : ℝ) + 1) / ((l : ℝ) + 1)) := by
    field_simp
  rw [h_eq, Real.log_mul (by positivity) (by positivity)]
  linarith

-- ============================================================
-- Section 4: Per-pair VdC bound for product modes
-- ============================================================

/-- Per-pair VdC bound for the product mode F_j·F_l on blocks.

    For large k (≥ K₀): apply complex_vdc_angular with productOmega lower bound.
    For small k (< K₀): trivially bound ‖∫ F_j·F_l‖ ≤ block_length.

    Result: ‖∫_{block k} F_j·F_l‖ ≤ C / log((k+1)²/((j+1)(l+1))). -/
theorem product_integral_vdc_bound :
    ∃ C_vdc > 0, ∀ k : ℕ, ∀ j l : ℕ, j < k → l < k → 1 ≤ k →
      ‖∫ t in (hardyStart k)..(hardyStart (k + 1)),
        hardyCosExp j t * hardyCosExp l t‖
          ≤ C_vdc / Real.log (((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) := by
  obtain ⟨K₀, hK₀⟩ := productOmega_lower_bound_eventually
  set C_small := 2 * Real.pi * (2 * (K₀ : ℝ) + 3) * (2 * Real.log ((K₀ : ℝ) + 2)) with hC_small_def
  refine ⟨max 6 C_small, by positivity, fun k j l hjk hlk hk => ?_⟩
  have hj1_pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hl1_pos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hjk_r : (j : ℝ) + 1 < (k : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hjk
  have hlk_r : (l : ℝ) + 1 < (k : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hlk
  have hratio_gt : 1 < ((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1)) := by
    rw [one_lt_div (by positivity)]; nlinarith
  have hlog_pos : 0 < Real.log (((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) :=
    Real.log_pos hratio_gt
  have hab : hardyStart k ≤ hardyStart (k + 1) := by
    rw [hardyStart_formula, hardyStart_formula]; gcongr; linarith
  by_cases hk_large : K₀ ≤ k
  · -- Case 1: k ≥ K₀ — apply complex_vdc_angular
    set m := Real.log (((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) / 2 with hm_def
    have hm_pos : 0 < m := by positivity
    have ha_pos : 0 < hardyStart k := hardyStart_pos' k
    -- Provide HasDerivAt in angular velocity form
    have hF_deriv : ∀ t ∈ Set.Icc (hardyStart k) (hardyStart (k + 1)),
        HasDerivAt (fun x => hardyCosExp j x * hardyCosExp l x)
          (Complex.I * ↑(productOmega j l t) * (hardyCosExp j t * hardyCosExp l t)) t := by
      intro t _ht
      exact product_angular_velocity j l t
    have h_bound := Aristotle.ComplexVdC.complex_vdc_angular
      (fun t => hardyCosExp j t * hardyCosExp l t) (productOmega j l)
      (hardyStart k) (hardyStart (k + 1)) m hab hm_pos
      hF_deriv
      (fun t _ht => norm_product_hardyCosExp j l t)
      (differentiable_productOmega j l)
      (continuous_deriv_productOmega j l)
      (fun t ht => hK₀ k hk_large j l hjk hlk t ht.1 ht.2)
      (fun t ht => deriv_productOmega_nonneg j l t (lt_of_lt_of_le ha_pos ht.1))
    calc ‖∫ t in (hardyStart k)..(hardyStart (k + 1)),
            hardyCosExp j t * hardyCosExp l t‖
        ≤ 3 / m := h_bound
      _ = 6 / Real.log (((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) := by
          rw [hm_def]; ring
      _ ≤ max 6 C_small / Real.log (((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) :=
          div_le_div_of_nonneg_right (le_max_left _ _) hlog_pos.le
  · -- Case 2: k < K₀ — trivial bound via ‖F‖ ≤ 1
    push_neg at hk_large
    have hF_int : IntervalIntegrable (fun t => hardyCosExp j t * hardyCosExp l t)
        MeasureTheory.volume (hardyStart k) (hardyStart (k + 1)) := by
      apply ContinuousOn.intervalIntegrable_of_Icc hab
      apply ContinuousOn.mul <;>
        exact (continuous_hardyCosExp_complex _).continuousOn
    -- ‖∫ F_j·F_l‖ ≤ ∫ ‖F_j·F_l‖ ≤ ∫ 1 = block_length
    have h_trivial : ‖∫ t in (hardyStart k)..(hardyStart (k + 1)),
        hardyCosExp j t * hardyCosExp l t‖
        ≤ hardyStart (k + 1) - hardyStart k := by
      have h1 : ‖∫ t in (hardyStart k)..(hardyStart (k + 1)),
          hardyCosExp j t * hardyCosExp l t‖
          ≤ ∫ t in (hardyStart k)..(hardyStart (k + 1)), ‖hardyCosExp j t * hardyCosExp l t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      have h2 : (∫ t in (hardyStart k)..(hardyStart (k + 1)),
          ‖hardyCosExp j t * hardyCosExp l t‖)
          ≤ ∫ t in (hardyStart k)..(hardyStart (k + 1)), (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hab (hF_int.norm) intervalIntegrable_const
        intro t ht; exact norm_product_hardyCosExp j l t
      have h3 : ∫ t in (hardyStart k)..(hardyStart (k + 1)), (1 : ℝ) =
          hardyStart (k + 1) - hardyStart k := by
        simp [intervalIntegral.integral_const, smul_eq_mul, mul_one]
      linarith
    -- Block length ≤ 2π(2K₀+3) since k < K₀
    have hk_le_K₀ : (k : ℝ) + 1 ≤ (K₀ : ℝ) := by exact_mod_cast hk_large
    have h_bl_bound : hardyStart (k + 1) - hardyStart k ≤ 2 * Real.pi * (2 * (K₀ : ℝ) + 3) := by
      rw [block_length]; nlinarith [Real.pi_pos]
    -- log ratio ≤ log((K₀+2)²) = 2·log(K₀+2)
    have h_ratio_upper : ((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))
        ≤ ((K₀ : ℝ) + 2) ^ 2 := by
      have h1 : ((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))
          ≤ ((k : ℝ) + 1) ^ 2 := by
        apply div_le_self (by positivity)
        exact one_le_mul_of_one_le_of_one_le
          (by linarith [Nat.cast_nonneg (α := ℝ) j])
          (by linarith [Nat.cast_nonneg (α := ℝ) l])
      nlinarith
    have hlogK_pos : 0 < 2 * Real.log ((K₀ : ℝ) + 2) := by
      have : 0 < Real.log ((K₀ : ℝ) + 2) :=
        Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) K₀])
      linarith
    have h_log_upper : Real.log (((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1)))
        ≤ 2 * Real.log ((K₀ : ℝ) + 2) := by
      calc Real.log (((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1)))
          ≤ Real.log (((K₀ : ℝ) + 2) ^ 2) := Real.log_le_log (by positivity) h_ratio_upper
        _ = 2 * Real.log ((K₀ : ℝ) + 2) := by rw [Real.log_pow]; ring
    calc ‖∫ t in (hardyStart k)..(hardyStart (k + 1)),
            hardyCosExp j t * hardyCosExp l t‖
        ≤ hardyStart (k + 1) - hardyStart k := h_trivial
      _ ≤ 2 * Real.pi * (2 * (K₀ : ℝ) + 3) := h_bl_bound
      _ = C_small / (2 * Real.log ((K₀ : ℝ) + 2)) := by
          rw [hC_small_def, mul_div_cancel_right₀ _ (ne_of_gt hlogK_pos)]
      _ ≤ C_small / Real.log (((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) :=
          div_le_div_of_nonneg_left (by rw [hC_small_def]; positivity) hlog_pos h_log_upper
      _ ≤ max 6 C_small / Real.log (((k : ℝ) + 1) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) :=
          div_le_div_of_nonneg_right (le_max_right _ _) hlog_pos.le

-- ============================================================
-- Section 5: Monotonicity of productOmega (for global VdC)
-- ============================================================

/-- If 0 < s ≤ t, then ω(s) ≤ ω(t).
    Direct from thetaDeriv being strictly monotone on (0,∞). -/
lemma productOmega_le_of_le (j l : ℕ) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    productOmega j l s ≤ productOmega j l t := by
  simp only [productOmega]
  have h := thetaDeriv_strictMonoOn.monotoneOn
    (Set.mem_Ioi.mpr hs) (Set.mem_Ioi.mpr (lt_of_lt_of_le hs hst)) hst
  linarith

-- ============================================================
-- Section 6: Global off-diagonal VdC bound
-- ============================================================

/-- Global VdC bound for off-diagonal pairs (j < l) on [hardyStart(l+1), T].

    For j < l, both modes are active (hardyN(t) ≥ l+1) when t ≥ hardyStart(l).
    The angular velocity ω ≥ log((l+2)²/((j+1)(l+1)))/2 > 0 on the entire range
    (by monotonicity from the block-k lower bound at k = l+1).

    VdC gives: ‖∫_{hardyStart(l+1)}^T F_j·F_l‖ ≤ 6/log((l+2)²/((j+1)(l+1))). -/
theorem global_off_diagonal_vdc_bound :
    ∃ K₁ : ℕ, ∀ j l : ℕ, j < l → K₁ ≤ l →
      ∀ T : ℝ, hardyStart (l + 1) ≤ T →
        ‖∫ t in (hardyStart (l + 1))..T,
          hardyCosExp j t * hardyCosExp l t‖
            ≤ 6 / Real.log (((l : ℝ) + 2) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) := by
  obtain ⟨K₀, hK₀⟩ := productOmega_lower_bound_eventually
  refine ⟨K₀, fun j l hjl hl T hT => ?_⟩
  -- Positivity setup
  have hj1_pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hl1_pos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  have hl2_pos : (0 : ℝ) < (l : ℝ) + 2 := by positivity
  have hjl_r : (j : ℝ) + 1 < (l : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hjl
  -- j < l+1 and l < l+1
  have hjl1 : j < l + 1 := Nat.lt_succ_of_lt hjl
  have hll1 : l < l + 1 := Nat.lt_succ_self l
  -- Ratio > 1 so log > 0
  have hratio_gt : 1 < ((l : ℝ) + 2) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1)) := by
    rw [one_lt_div (by positivity)]; nlinarith
  have hlog_pos : 0 < Real.log (((l : ℝ) + 2) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) :=
    Real.log_pos hratio_gt
  -- Set lower bound m for angular velocity
  set m := Real.log (((l : ℝ) + 2) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) / 2 with hm_def
  have hm_pos : 0 < m := by positivity
  have ha_pos : 0 < hardyStart (l + 1) := hardyStart_pos' (l + 1)
  -- ω ≥ m on [hardyStart(l+1), T] by monotonicity:
  -- At t₀ = hardyStart(l+1) (left endpoint of block l+1), ω ≥ m by productOmega_lower_bound_eventually
  -- For t ≥ t₀: ω(t) ≥ ω(t₀) ≥ m by monotonicity
  have hω_lower : ∀ t ∈ Set.Icc (hardyStart (l + 1)) T,
      m ≤ productOmega j l t := by
    intro t ⟨ht_lo, _⟩
    -- At hardyStart(l+1): use productOmega_lower_bound_eventually with k = l+1
    have hhs_le : hardyStart (l + 1) ≤ hardyStart (l + 1 + 1) := by
      rw [hardyStart_formula, hardyStart_formula]; gcongr
    have hbase := hK₀ (l + 1) (by omega : K₀ ≤ l + 1) j l hjl1 hll1
      (hardyStart (l + 1)) le_rfl hhs_le
    -- Cast alignment: (l + 1 + 1 : ℕ) = (l + 2 : ℕ), so ↑(l+1)+1 = ↑l+2
    have hcast : ((l + 1 : ℕ) + 1 : ℝ) = (l : ℝ) + 2 := by push_cast; ring
    rw [show (↑(l + 1) + 1 : ℝ) = (↑l + 2 : ℝ) from hcast] at hbase
    -- For t ≥ hardyStart(l+1): use monotonicity
    exact le_trans hbase (productOmega_le_of_le j l _ t ha_pos ht_lo)
  -- Apply complex_vdc_angular
  have h_bound := Aristotle.ComplexVdC.complex_vdc_angular
    (fun t => hardyCosExp j t * hardyCosExp l t) (productOmega j l)
    (hardyStart (l + 1)) T m hT hm_pos
    (fun t _ht => product_angular_velocity j l t)
    (fun t _ht => norm_product_hardyCosExp j l t)
    (differentiable_productOmega j l)
    (continuous_deriv_productOmega j l)
    hω_lower
    (fun t ht => deriv_productOmega_nonneg j l t (lt_of_lt_of_le ha_pos ht.1))
  -- 3/m = 6/log(...)
  calc ‖∫ t in (hardyStart (l + 1))..T,
          hardyCosExp j t * hardyCosExp l t‖
      ≤ 3 / m := h_bound
    _ = 6 / Real.log (((l : ℝ) + 2) ^ 2 / (((j : ℝ) + 1) * ((l : ℝ) + 1))) := by
        rw [hm_def]; ring

-- ============================================================
-- Section 7: Off-diagonal double sum bound — helper lemmas
-- ============================================================

/-- log(x) ≥ 1 - 1/x for x > 0, from `Real.add_one_le_exp` applied to 1/x - 1. -/
private lemma log_ge_one_sub_inv (x : ℝ) (hx : 0 < x) :
    1 - 1 / x ≤ Real.log x := by
  have h := Real.add_one_le_exp (1 / x - 1)
  have h1 : 1 / x ≤ Real.exp (1 / x - 1) := by linarith
  have h2 : Real.log (1 / x) ≤ 1 / x - 1 := by
    rwa [Real.log_le_iff_le_exp (by positivity)]
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (ne_of_gt hx), Real.log_one, zero_sub] at h2
  linarith

/-- Harmonic number bound: H(m) = ∑_{k=0}^{m-1} 1/(k+1) ≤ 1 + log m.
    Proof by induction using 1/(n+1) ≤ log((n+1)/n) from `log_ge_one_sub_inv`. -/
private lemma harmonic_bound (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.range m, (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 + Real.log ↑m := by
  induction m with
  | zero => omega
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hn : n = 0
    · subst hn; simp [Real.log_one]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have ih' := ih hn1
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have h_key : 1 / ((n : ℝ) + 1) ≤ Real.log (↑n + 1) - Real.log ↑n := by
        have h1 := log_ge_one_sub_inv ((↑n + 1) / ↑n) (by positivity)
        rw [Real.log_div (by positivity) hn_pos.ne'] at h1
        rw [one_div, inv_div] at h1
        have h2 : 1 - (↑n : ℝ) / (↑n + 1) = 1 / (↑n + 1) := by field_simp; ring
        linarith
      push_cast at ih' ⊢; linarith

/-- Inverse square root sum bound: ∑_{k=0}^{N-1} (k+1)^{-1/2} ≤ 2√N.
    Proof by telescoping: (k+1)^{-1/2} ≤ 2(√(k+1) - √k). -/
private lemma sum_inv_sqrt_bound (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k : ℝ) + 1) ^ (-(1:ℝ)/2)
    ≤ 2 * Real.sqrt ↑N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1_nn : (0 : ℝ) ≤ (n : ℝ) + 1 := le_of_lt hn1_pos
    have h_rpow : ((n : ℝ) + 1) ^ (-(1:ℝ)/2) = 1 / Real.sqrt ((n : ℝ) + 1) := by
      rw [show -(1:ℝ)/2 = -((1:ℝ)/2) from by ring, Real.rpow_neg hn1_nn,
          ← Real.sqrt_eq_rpow]; simp [one_div]
    rw [h_rpow]
    have h_sqrt_le : Real.sqrt ↑n ≤ Real.sqrt (↑n + 1) :=
      Real.sqrt_le_sqrt (by linarith : (↑n : ℝ) ≤ ↑n + 1)
    have h_sqrt_pos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hn1_pos
    have h_prod : (Real.sqrt (↑n + 1) - Real.sqrt ↑n) *
        (Real.sqrt (↑n + 1) + Real.sqrt ↑n) = 1 := by
      have h1 := Real.sq_sqrt (show (0:ℝ) ≤ ↑n + 1 by positivity)
      have h2 := Real.sq_sqrt (show (0:ℝ) ≤ (↑n : ℝ) by positivity)
      nlinarith [sq_nonneg (Real.sqrt (↑n + 1)), sq_nonneg (Real.sqrt ↑n)]
    have h_sum_pos : 0 < Real.sqrt (↑n + 1) + Real.sqrt ↑n := by positivity
    have h_key : 1 / Real.sqrt ((n : ℝ) + 1) ≤
        2 * (Real.sqrt (↑n + 1) - Real.sqrt ↑n) := by
      rw [div_le_iff₀ h_sqrt_pos]
      have h_diff_nn : 0 ≤ Real.sqrt (↑n + 1) - Real.sqrt ↑n := by linarith
      calc 1 = (Real.sqrt (↑n + 1) - Real.sqrt ↑n) *
                (Real.sqrt (↑n + 1) + Real.sqrt ↑n) := h_prod.symm
        _ ≤ (Real.sqrt (↑n + 1) - Real.sqrt ↑n) *
              (2 * Real.sqrt (↑n + 1)) := by
            exact mul_le_mul_of_nonneg_left (by linarith) h_diff_nn
        _ = 2 * (Real.sqrt (↑n + 1) - Real.sqrt ↑n) * Real.sqrt (↑n + 1) := by ring
    have h_cast : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
    rw [h_cast]; linarith

/-- The filtered sum ∑_{l>j, l<N} 1/(l-j) is bounded by 1 + log N.
    Uses the reindexing l ↦ l-(j+1) to reduce to harmonic_bound. -/
private lemma filter_inv_gap_le (j N : ℕ) (hN : 1 ≤ N) :
    ∑ l ∈ (Finset.range N).filter (fun l => j < l),
      (1 : ℝ) / ((l : ℝ) - (j : ℝ))
    ≤ 1 + Real.log ↑N := by
  have h_filter : (Finset.range N).filter (fun l => j < l) = Finset.Ico (j + 1) N := by
    ext l; simp [Finset.mem_range, Finset.mem_Ico]; omega
  rw [h_filter, Finset.sum_Ico_eq_sum_range]
  conv_lhs =>
    arg 2; ext k
    rw [show (↑(j + 1 + k) : ℝ) - ↑j = (↑k : ℝ) + 1 by push_cast; ring]
  by_cases hm : N - (j + 1) = 0
  · rw [hm]; simp; linarith [Real.log_nonneg (show (1:ℝ) ≤ ↑N by exact_mod_cast hN)]
  · have hm1 : 1 ≤ N - (j + 1) := Nat.one_le_iff_ne_zero.mpr hm
    calc ∑ k ∈ Finset.range (N - (j + 1)), (1 : ℝ) / (↑k + 1)
        ≤ 1 + Real.log ↑(N - (j + 1)) := harmonic_bound _ hm1
      _ ≤ 1 + Real.log ↑N := by
          gcongr; exact_mod_cast (show N - (j + 1) ≤ N from Nat.sub_le _ _)

-- ============================================================
-- Section 7: Off-diagonal double sum bound
-- ============================================================

/-- The off-diagonal double sum ∑_{j<l<N} (j+1)^{-1/2}·(l+1)^{-1/2}/log((l+1)/(j+1))
    is O(N · log(N+1)).

    Proof: bound 1/log((l+1)/(j+1)) ≤ (l+1)/(l-j) via log(x) ≥ (x-1)/x,
    decompose into nested sums, then use harmonic and inv-sqrt bounds.
    Total ≤ 2N(1+log N) ≤ 10N·log(N+1) for N ≥ 1. -/
theorem off_diagonal_double_sum_bound :
    ∃ C_off > 0, ∀ N : ℕ, 1 ≤ N →
      ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 < p.2),
        ((p.1 + 1 : ℝ) ^ (-(1:ℝ)/2)) * ((p.2 + 1 : ℝ) ^ (-(1:ℝ)/2)) /
          Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1))
      ≤ C_off * (N : ℝ) * Real.log ((N : ℝ) + 1) := by
  use 10, by norm_num
  intro N hN
  -- Decompose filter product into nested sums
  rw [Finset.sum_filter, Finset.sum_product]
  simp_rw [← Finset.sum_filter]
  -- Abbreviate the term function
  set f := fun j l => ((j + 1 : ℝ) ^ (-(1:ℝ)/2)) * ((l + 1 : ℝ) ^ (-(1:ℝ)/2)) /
    Real.log (((l : ℝ) + 1) / ((j : ℝ) + 1))
  -- Pointwise bound: f(j,l) ≤ (j+1)^{-1/2} · √N / (l-j)
  -- using log(r) ≥ (r-1)/r and (l+1)^{1/2} ≤ √N
  have h_pw : ∀ j ∈ Finset.range N, ∀ l ∈ (Finset.range N).filter (fun l => j < l),
      f j l ≤ ((j + 1 : ℝ) ^ (-(1:ℝ)/2)) * Real.sqrt ↑N / ((l : ℝ) - (j : ℝ)) := by
    intro j _hj l hl
    have hjl : j < l := (Finset.mem_filter.mp hl).2
    have hlN : l < N := Finset.mem_range.mp (Finset.mem_filter.mp hl).1
    have hj_pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hl_pos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
    have hlj_pos : (0 : ℝ) < (l : ℝ) - (j : ℝ) := by
      exact_mod_cast show 0 < (l : ℤ) - (j : ℤ) by omega
    -- log((l+1)/(j+1)) ≥ (l-j)/(l+1) from log(x) ≥ 1-1/x
    have h_log_lower : ((l : ℝ) - (j : ℝ)) / ((l : ℝ) + 1) ≤
        Real.log (((l : ℝ) + 1) / ((j : ℝ) + 1)) := by
      have h1 := log_ge_one_sub_inv (((l:ℝ)+1)/((j:ℝ)+1)) (by positivity)
      have : 1 - 1 / (((l:ℝ)+1)/((j:ℝ)+1)) = ((l:ℝ)-(j:ℝ))/((l:ℝ)+1) := by
        rw [one_div, inv_div]; field_simp; ring
      linarith
    have h_log_pos : 0 < Real.log (((l:ℝ)+1)/((j:ℝ)+1)) := by
      linarith [div_pos hlj_pos hl_pos]
    -- rpow to sqrt conversion
    have h_rpow_l : ((l:ℝ)+1) ^ (-(1:ℝ)/2) = 1 / Real.sqrt ((l:ℝ)+1) := by
      rw [show -(1:ℝ)/2 = -((1:ℝ)/2) from by ring, Real.rpow_neg (le_of_lt hl_pos),
          ← Real.sqrt_eq_rpow]; simp [one_div]
    -- √(l+1) ≤ √N
    have h_sqrt_le : Real.sqrt ((l:ℝ)+1) ≤ Real.sqrt ↑N :=
      Real.sqrt_le_sqrt (by exact_mod_cast hlN)
    have h_sqrt_l_pos : 0 < Real.sqrt ((l:ℝ)+1) := Real.sqrt_pos.mpr hl_pos
    -- f(j,l) = (j+1)^{-1/2} · (1/√(l+1)) / log(...)
    --        ≤ (j+1)^{-1/2} · (1/√(l+1)) · (l+1)/(l-j)
    --        = (j+1)^{-1/2} · √(l+1) / (l-j)
    --        ≤ (j+1)^{-1/2} · √N / (l-j)
    simp only [f]; rw [h_rpow_l]
    -- Factor (j+1)^{-1/2} out of both sides using mul_div_assoc
    have hj_rpow_nn : 0 ≤ ((j:ℝ)+1) ^ (-(1:ℝ)/2) := by positivity
    rw [show ((j+1:ℝ) ^ (-(1:ℝ)/2)) * (1 / Real.sqrt ((l:ℝ)+1)) /
            Real.log (((l:ℝ)+1)/((j:ℝ)+1)) =
          ((j+1:ℝ) ^ (-(1:ℝ)/2)) * (1 / Real.sqrt ((l:ℝ)+1) /
            Real.log (((l:ℝ)+1)/((j:ℝ)+1))) from mul_div_assoc _ _ _,
        show ((j+1:ℝ) ^ (-(1:ℝ)/2)) * Real.sqrt ↑N / ((l:ℝ) - (j:ℝ)) =
          ((j+1:ℝ) ^ (-(1:ℝ)/2)) * (Real.sqrt ↑N / ((l:ℝ) - (j:ℝ))) from
          mul_div_assoc _ _ _]
    apply mul_le_mul_of_nonneg_left _ hj_rpow_nn
    -- Goal: 1/√(l+1) / log(ratio) ≤ √N / (l-j)
    rw [div_div, div_le_div_iff₀ (mul_pos h_sqrt_l_pos h_log_pos) hlj_pos, one_mul]
    -- Goal: (l-j) ≤ √N * (√(l+1) * log(ratio))
    calc ((l:ℝ) - (j:ℝ))
        ≤ Real.log (((l:ℝ)+1)/((j:ℝ)+1)) * ((l:ℝ)+1) :=
          (div_le_iff₀ hl_pos).mp h_log_lower
      _ = ((l:ℝ)+1) * Real.log (((l:ℝ)+1)/((j:ℝ)+1)) := mul_comm _ _
      _ = (Real.sqrt ((l:ℝ)+1) * Real.sqrt ((l:ℝ)+1)) *
            Real.log (((l:ℝ)+1)/((j:ℝ)+1)) := by
          rw [Real.mul_self_sqrt (le_of_lt hl_pos)]
      _ ≤ (Real.sqrt ↑N * Real.sqrt ((l:ℝ)+1)) *
            Real.log (((l:ℝ)+1)/((j:ℝ)+1)) := by
          gcongr
      _ = Real.sqrt ↑N * (Real.sqrt ((l:ℝ)+1) *
            Real.log (((l:ℝ)+1)/((j:ℝ)+1))) := by ring
  -- Assembly: bound nested sums using helper lemmas
  have h_inner : ∀ j ∈ Finset.range N,
      ∑ l ∈ (Finset.range N).filter (fun l => j < l), f j l ≤
        ((j+1:ℝ) ^ (-(1:ℝ)/2)) * Real.sqrt ↑N * (1 + Real.log ↑N) := by
    intro j hj
    calc ∑ l ∈ (Finset.range N).filter (fun l => j < l), f j l
        ≤ ∑ l ∈ (Finset.range N).filter (fun l => j < l),
            ((j+1:ℝ) ^ (-(1:ℝ)/2)) * Real.sqrt ↑N / ((l:ℝ) - (j:ℝ)) :=
          Finset.sum_le_sum (h_pw j hj)
      _ = ((j+1:ℝ) ^ (-(1:ℝ)/2)) * Real.sqrt ↑N *
            ∑ l ∈ (Finset.range N).filter (fun l => j < l),
              (1:ℝ) / ((l:ℝ) - (j:ℝ)) := by
          conv_lhs => arg 2; ext l; rw [← mul_one_div]
          exact (Finset.mul_sum ..).symm
      _ ≤ ((j+1:ℝ) ^ (-(1:ℝ)/2)) * Real.sqrt ↑N * (1 + Real.log ↑N) :=
          mul_le_mul_of_nonneg_left (filter_inv_gap_le j N hN)
            (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have h_log_N_nonneg : 0 ≤ Real.log (N:ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have h_one_plus_log_nonneg : 0 ≤ 1 + Real.log (N:ℝ) := by linarith
  calc ∑ j ∈ Finset.range N,
        ∑ l ∈ (Finset.range N).filter (fun l => j < l), f j l
      ≤ ∑ j ∈ Finset.range N,
          ((j+1:ℝ) ^ (-(1:ℝ)/2)) * Real.sqrt ↑N * (1 + Real.log ↑N) :=
        Finset.sum_le_sum h_inner
    _ = Real.sqrt ↑N * (1 + Real.log ↑N) *
          ∑ j ∈ Finset.range N, ((j+1:ℝ) ^ (-(1:ℝ)/2)) := by
        conv_lhs =>
          arg 2; ext j
          rw [show ((j+1:ℝ) ^ (-(1:ℝ)/2)) * Real.sqrt ↑N * (1 + Real.log ↑N) =
            Real.sqrt ↑N * (1 + Real.log ↑N) * ((j+1:ℝ) ^ (-(1:ℝ)/2)) from by ring]
        exact (Finset.mul_sum ..).symm
    _ ≤ Real.sqrt ↑N * (1 + Real.log ↑N) * (2 * Real.sqrt ↑N) :=
        mul_le_mul_of_nonneg_left (sum_inv_sqrt_bound N)
          (mul_nonneg (Real.sqrt_nonneg _) h_one_plus_log_nonneg)
    _ = 2 * ↑N * (1 + Real.log ↑N) := by
        rw [show Real.sqrt ↑N * (1 + Real.log ↑N) * (2 * Real.sqrt ↑N) =
          2 * (Real.sqrt ↑N * Real.sqrt ↑N) * (1 + Real.log ↑N) from by ring,
          Real.mul_self_sqrt (Nat.cast_nonneg N)]
    _ ≤ 10 * ↑N * Real.log (↑N + 1) := by
        have h_log2 : (1:ℝ) - 1/2 ≤ Real.log 2 :=
          log_ge_one_sub_inv 2 (by norm_num)
        have h_log_N1_ge : (1:ℝ)/2 ≤ Real.log ((N:ℝ) + 1) := by
          have : (1:ℝ)/2 = 1 - 1/2 := by ring
          rw [this]
          calc (1:ℝ) - 1/2 ≤ Real.log 2 := h_log2
            _ ≤ Real.log ((N:ℝ) + 1) := by
                apply Real.log_le_log (by norm_num : (0:ℝ) < 2)
                exact_mod_cast show 2 ≤ N + 1 from Nat.succ_le_succ hN
        have h_log_mono : Real.log (N:ℝ) ≤ Real.log ((N:ℝ) + 1) :=
          Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (by linarith)
        nlinarith [Nat.cast_nonneg (α := ℝ) N]

end Aristotle.Standalone.OscSumSquaredBigO
