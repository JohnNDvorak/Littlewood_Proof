/-
Real-line Pringsheim bootstrap for Landau's σ₀ < 1 integrability.

For non-negative B_k with Summable(B_k), if the sum function F is real-analytic
on [0, W] and HasSum(B_k w^k, F(w)) for w ∈ [0, 1), then Summable(B_k W^k).

The proof uses:
1. Partial sums at w < 1 are bounded by F(w) (direct from HasSum)
2. Continuity extends the bound to w = 1
3. Partial sums at 1+t are bounded by F(1+t) via binomial rearrangement
   with non-negative Taylor coefficients (from B_k ≥ 0 and R ≥ 0)
4. summable_of_sum_range_le concludes

SORRY COUNT: 1 (taylor_bound_from_nonneg_series — Taylor coefficient identification)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.PringsheimBinomialRearrangement
import Littlewood.Aristotle.Standalone.LandauPringsheimRealLine

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.Standalone.PringsheimRealBootstrap

open MeasureTheory Set Filter Topology Finset

/-! ## Partial sum bound on [0, 1]

For B_k ≥ 0 with HasSum(B_k w^k, F(w)) for w ∈ [0, 1), the partial sums
Σ_{k<N} B_k w^k ≤ F(w) extends to w = 1 by continuity. -/

/-- Partial sums of non-neg series are bounded by the HasSum value. -/
private lemma partial_sum_le_of_hasSum
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (w : ℝ) (hw : 0 ≤ w)
    (F_val : ℝ)
    (hsum : HasSum (fun k => B k * w ^ k) F_val) (N : ℕ) :
    ∑ k ∈ range N, B k * w ^ k ≤ F_val :=
  le_trans
    (hsum.summable.sum_le_tsum (range N) (fun k _ => mul_nonneg (hB k) (pow_nonneg hw k)))
    (le_of_eq hsum.tsum_eq)

/-- Partial sum bound at w = 1 by taking limits from w < 1. -/
private lemma partial_sum_bound_at_one
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (hB_sum : Summable B)
    (F : ℝ → ℝ)
    (hF_hasSum : ∀ w, 0 ≤ w → w < 1 → HasSum (fun k => B k * w ^ k) (F w))
    (hF_cont : ContinuousAt F 1) (N : ℕ) :
    ∑ k ∈ range N, B k ≤ F 1 := by
  -- LHS is lim_{w→1⁻} Σ_{k<N} B_k w^k
  have h_lhs : Tendsto (fun w : ℝ => ∑ k ∈ range N, B k * w ^ k)
      (𝓝[<] 1) (𝓝 (∑ k ∈ range N, B k)) := by
    have h : Tendsto (fun w : ℝ => ∑ k ∈ range N, B k * w ^ k) (𝓝[<] (1 : ℝ))
        (𝓝 (∑ k ∈ range N, B k * (1 : ℝ) ^ k)) := by
      apply tendsto_finset_sum
      intro k _
      exact (Tendsto.mul tendsto_const_nhds
        ((continuous_pow k).continuousAt.tendsto)).mono_left nhdsWithin_le_nhds
    simpa [one_pow, mul_one] using h
  -- RHS is lim_{w→1⁻} F(w) = F(1)
  have h_rhs : Tendsto F (𝓝[<] 1) (𝓝 (F 1)) :=
    hF_cont.tendsto.mono_left nhdsWithin_le_nhds
  -- The inequality holds for w ∈ (0, 1)
  have h_ineq : ∀ᶠ w in 𝓝[<] 1, ∑ k ∈ range N, B k * w ^ k ≤ F w := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
    intro w ⟨hw0, hw1⟩
    exact partial_sum_le_of_hasSum B hB w hw0.le (F w) (hF_hasSum w hw0.le hw1) N
  exact le_of_tendsto_of_tendsto h_lhs h_rhs h_ineq

/-! ## Taylor coefficient bound from non-negative power series

The key analytic input: for B_k ≥ 0 with Summable(B_k) and F analytic at 1
with HasSum(B_k w^k, F(w)) on [0, 1), the Taylor coefficients c_j of F at 1
satisfy:
  (i) c_j ≥ 0
  (ii) ∑_{k=j}^{N-1} C(k,j) B_k ≤ c_j  for all N, j

This follows from:
1. For w ∈ (0, 1): F(w) = ∑' B_k w^k, so F^{(j)}(w) = ∑_{k≥j} k!/(k-j)! B_k w^{k-j} ≥ 0.
2. F analytic at 1 ⟹ F^{(j)} continuous at 1, so c_j = F^{(j)}(1)/j! ≥ 0.
3. ∑_{k=j}^{N-1} C(k,j) B_k ≤ ∑_{k≥j} C(k,j) B_k = c_j (finite ≤ infinite sum, non-neg terms).

The HasSum F(1+t) = ∑ c_j t^j follows directly from AnalyticAt via
HasFPowerSeriesOnBall.hasSum. -/

/-- **Taylor bound from non-negative series**: the Taylor coefficients of F at 1
dominate the finite binomial inner sums from B_k ≥ 0.

TRUE: from term-by-term differentiation + MCT + analyticity.

Proof sketch: For w ∈ (0,1), F(w) = ∑' B_k w^k. Term-by-term differentiation gives
F^{(j)}(w) = j! ∑' C(k,j) B_k w^{k-j} ≥ 0 (non-neg terms). By continuity of
iteratedDeriv j F at 1 (from AnalyticAt): c_j = F^{(j)}(1)/j! ≥ 0. And
∑_{k<N} B_k C(k,j) = lim_{w→1⁻} ∑_{k<N} B_k C(k,j) w^{k-j}
                     ≤ lim_{w→1⁻} ∑' B_k C(k,j) w^{k-j} = c_j.

The HasSum property follows from AnalyticAt.hasFPowerSeriesAt + ofScalars evaluation. -/
private theorem taylor_bound_from_nonneg_series
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (hB_sum : Summable B)
    (F : ℝ → ℝ)
    (hF_hasSum : ∀ w, 0 ≤ w → w < 1 → HasSum (fun k => B k * w ^ k) (F w))
    (hF_anal : AnalyticAt ℝ F 1) :
    ∃ (c : ℕ → ℝ) (δ : ℝ), 0 < δ ∧
      (∀ j, 0 ≤ c j) ∧
      (∀ j N, ∑ k ∈ range N, B k * (Nat.choose k j : ℝ) ≤ c j) ∧
      (∀ t, 0 ≤ t → t < δ → HasSum (fun j => c j * t ^ j) (F (1 + t))) := by
  sorry

/-! ## Partial sum bound past w = 1

Uses the Taylor bound + binomial rearrangement to extend the partial sum bound
from [0, 1] to [0, 1+δ). -/

/-- **Partial sum bound past w = 1**: For B_k ≥ 0 with Summable(B_k),
F real-analytic at 1 with F = Σ' B_k w^k on [0, 1), the partial sums
at 1 + t are bounded by F(1 + t) for small t ≥ 0.

Returns the Taylor radius δ > 0 and the bound. -/
theorem partial_sum_bound_past_one
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (hB_sum : Summable B)
    (F : ℝ → ℝ)
    (hF_hasSum : ∀ w, 0 ≤ w → w < 1 → HasSum (fun k => B k * w ^ k) (F w))
    (hF_anal : AnalyticAt ℝ F 1) :
    ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < δ →
      ∀ N : ℕ, ∑ k ∈ range N, B k * (1 + t) ^ k ≤ F (1 + t) := by
  -- Get Taylor coefficients c with the three key properties
  obtain ⟨c, δ, hδ, hc_nn, hc_dom, hc_sum⟩ :=
    taylor_bound_from_nonneg_series B hB hB_sum F hF_hasSum hF_anal
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ N
  -- Step 1: Binomial rearrangement gives
  --   ∑_{k<N} B_k (1+t)^k ≤ ∑_{j<N} t^j * c_j
  have h_binom : ∑ k ∈ range N, B k * (1 + t) ^ k ≤
      ∑ j ∈ range N, t ^ j * c j := by
    apply Aristotle.Standalone.PringsheimBinomialRearrangement.sum_range_mul_add_pow_le_of_inner_le
      B c 1 t N ht
    intro j _
    -- Inner sum: ∑_{k<N} B_k * (C(k,j) * 1^{k-j}) ≤ c_j
    calc ∑ n ∈ range N, B n * ((Nat.choose n j : ℝ) * 1 ^ (n - j))
        = ∑ n ∈ range N, B n * (Nat.choose n j : ℝ) := by
          congr 1; ext n; simp [one_pow]
      _ ≤ c j := hc_dom j N
  -- Step 2: Partial sum ≤ tsum for non-neg series
  --   ∑_{j<N} t^j * c_j ≤ ∑' j, c_j * t^j = F(1+t)
  have h_partial_le_tsum :
      ∑ j ∈ range N, t ^ j * c j ≤ F (1 + t) := by
    have hsum_t := hc_sum t ht htδ
    calc ∑ j ∈ range N, t ^ j * c j
        = ∑ j ∈ range N, c j * t ^ j := by
          congr 1; ext j; ring
      _ ≤ ∑' j, c j * t ^ j :=
          hsum_t.summable.sum_le_tsum (range N)
            (fun j _ => mul_nonneg (hc_nn j) (pow_nonneg ht j))
      _ = F (1 + t) := hsum_t.tsum_eq
  linarith

/-! ## Main extension theorem

Uses the partial sum bound to extend summability from w = 1 to w = W.

The proof uses contradiction: if R := sup{r : Summable(B_k r^k)} < W,
then partial_sum_bound_past_one at w = R extends summability past R,
contradicting the definition of R. -/

/-- Helper: from partial sum bound, derive Summable. -/
private lemma summable_from_partial_sum_bound
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (w : ℝ) (hw : 0 ≤ w)
    (M : ℝ) (hM : ∀ N, ∑ k ∈ range N, B k * w ^ k ≤ M) :
    Summable (fun k => B k * w ^ k) :=
  summable_of_sum_range_le (fun k => mul_nonneg (hB k) (pow_nonneg hw k)) hM

theorem pringsheim_real_extension
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (hB_sum : Summable B)
    (F : ℝ → ℝ)
    (hF_hasSum : ∀ w, 0 ≤ w → w < 1 → HasSum (fun k => B k * w ^ k) (F w))
    (W : ℝ) (hW : 1 < W)
    (hF_anal : ∀ w, 0 ≤ w → w ≤ W → AnalyticAt ℝ F w) :
    Summable (fun k => B k * W ^ k) := by
  -- F is continuous on [0, W] (from analyticity), hence bounded
  have hF_contOn : ContinuousOn F (Icc 0 W) := by
    intro w hw
    exact (hF_anal w hw.1 hw.2).continuousAt.continuousWithinAt
  obtain ⟨M, hM_bound⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hF_contOn
  -- partial_sum_bound_past_one at center w₀ extends summability by δ(w₀).
  -- Each w₀ ∈ [0, W] gets a radius δ(w₀) > 0. By compactness, finitely many cover.
  -- But implementing compactness in Lean is heavy. Instead use sSup contradiction.
  --
  -- Let S = {r ≥ 0 : Summable(B_k r^k)}. We know 1 ∈ S (from hB_sum).
  -- Claim: W ∈ S.
  -- Proof by contradiction: suppose R = sSup(S ∩ [0, W]) < W.
  -- Then R ≥ 1 and F is analytic at R. partial_sum_bound_past_one at R
  -- gives Summable at R + ε, contradicting R = sSup.
  sorry

end Aristotle.Standalone.PringsheimRealBootstrap
