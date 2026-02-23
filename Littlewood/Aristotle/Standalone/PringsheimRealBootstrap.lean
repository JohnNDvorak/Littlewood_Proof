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

SORRY COUNT: 1
  taylor_coeff_nonneg_and_dominates — Taylor coeff c_j ≥ 0 and ∑ B_k C(k,j) ≤ c_j

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

/-- For ofScalars power series, changeOriginSeriesTerm at (fun _ => w, fun _ => 1)
equals B(k+l) * w^l. -/
private lemma ofScalars_changeOriginSeriesTerm_eval
    (B : ℕ → ℝ) (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l) (w : ℝ) :
    (FormalMultilinearSeries.ofScalars ℝ B).changeOriginSeriesTerm k l s hs
      (fun _ => w) (fun _ => (1 : ℝ)) = B (k + l) * w ^ l := by
  rw [FormalMultilinearSeries.changeOriginSeriesTerm_apply]
  simp only [FormalMultilinearSeries.ofScalars, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]
  congr 1
  rw [show (fun i : Fin (k + l) => s.piecewise (fun _ => w) (fun _ => (1 : ℝ)) i) =
    (fun i => if i ∈ s then w else 1) from by ext i; simp [Finset.piecewise]]
  rw [prod_ite_mem_eq s (fun _ => w), Finset.prod_const, hs]

/-- Taylor coefficients of F at 1 are non-negative and dominate the binomial sums.

Proof: changeOrigin of ofScalars ℝ B at w gives a tsum of non-negative terms.
Via factorial_smul, this equals iteratedDeriv j F w / j!. Taking w→1⁻ gives
c_j ≥ 0. For partial sum domination, reindex and use sum_le_tsum. -/
private lemma taylor_coeff_nonneg_and_dominates
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (hB_sum : Summable B)
    (F : ℝ → ℝ)
    (hF_hasSum : ∀ w, 0 ≤ w → w < 1 → HasSum (fun k => B k * w ^ k) (F w))
    (hF_anal : AnalyticAt ℝ F 1)
    (j : ℕ) :
    0 ≤ iteratedDeriv j F 1 / (j.factorial : ℝ) ∧
    ∀ N, ∑ k ∈ range N, B k * (Nat.choose k j : ℝ) ≤
      iteratedDeriv j F 1 / (j.factorial : ℝ) := by
  -- Setup: power series p = ofScalars ℝ B with radius ≥ 1
  set p := FormalMultilinearSeries.ofScalars ℝ B
  have hpsum_eq : ∀ v : ℝ, p.sum v = ∑' k, B k * v ^ k := by
    intro v; show ∑' n, p n (fun _ => v) = ∑' k, B k * v ^ k
    congr 1; ext n; rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have h_rad : ENNReal.ofReal 1 ≤ p.radius := by
    change (↑(Real.toNNReal 1) : ENNReal) ≤ p.radius
    refine FormalMultilinearSeries.le_radius_of_summable (p := p) ?_
    rw [show (Real.toNNReal 1 : ℝ) = 1 from by norm_num]
    show Summable (fun n => ‖p n‖ * 1 ^ n)
    simp only [one_pow, mul_one]
    exact (show (fun n => ‖p n‖) = B from by
      ext n; rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs,
        abs_of_nonneg (hB n)]) ▸ hB_sum
  have hr_pos : 0 < p.radius :=
    lt_of_lt_of_le (by positivity : (0 : ENNReal) < ENNReal.ofReal 1) h_rad
  have hball : HasFPowerSeriesOnBall p.sum p 0 p.radius := p.hasFPowerSeriesOnBall hr_pos
  -- p.sum = F on (0,1)
  have hGF : ∀ v ∈ Ioo (0 : ℝ) 1, p.sum v = F v := by
    intro v hv; rw [hpsum_eq]; exact (hF_hasSum v hv.1.le hv.2).tsum_eq
  -- w ∈ (0,1) ⟹ w in convergence ball
  have hw_in_ball : ∀ w ∈ Ioo (0 : ℝ) 1, ↑‖w‖₊ < p.radius := by
    intro w hw
    show ‖w‖ₑ < p.radius
    rw [Real.enorm_of_nonneg hw.1.le]
    exact lt_of_lt_of_le
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hw.1.le).mpr hw.2) h_rad
  -- ContinuousAt (iteratedDeriv j F) 1 from AnalyticAt
  have hcont : ContinuousAt (iteratedDeriv j F) 1 := by
    rw [iteratedDeriv_eq_iterate]
    exact (hF_anal.iterated_deriv j).continuousAt
  -- iteratedDeriv j (p.sum) = iteratedDeriv j F on (0,1)
  have hderiv_eq : ∀ w ∈ Ioo (0 : ℝ) 1,
      iteratedDeriv j (p.sum) w = iteratedDeriv j F w := by
    intro w hw
    exact Filter.EventuallyEq.iteratedDeriv_eq j
      (Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Ioo 0 1, Ioo_mem_nhds hw.1 hw.2, fun v hv => hGF v hv⟩)
  -- Helper: w ∈ (0,1) ⟹ changeOriginSeries summable
  have hco_summable : ∀ w ∈ Ioo (0 : ℝ) 1,
      Summable (fun l => (p.changeOriginSeries j l) (fun _ => w)) := by
    intro w hw
    exact (p.changeOriginSeries j).summable (by
      rw [EMetric.mem_ball, edist_eq_enorm_sub, sub_zero]
      exact (hw_in_ball w hw).trans_le (p.le_changeOriginSeries_radius j))
  -- KEY: For w ∈ (0,1), changeOrigin gives iteratedDeriv j (p.sum) w / j! as tsum
  -- of non-negative terms
  have hG_nonneg : ∀ w ∈ Ioo (0 : ℝ) 1, 0 ≤ iteratedDeriv j (p.sum) w := by
    intro w hw
    have hfact := (hball.changeOrigin (hw_in_ball w hw)).factorial_smul (1 : ℝ) j
    rw [zero_add] at hfact
    rw [iteratedDeriv_eq_iteratedFDeriv, ← hfact]
    apply nsmul_nonneg
    show 0 ≤ ((p.changeOriginSeries j).sum w) (fun _ => (1 : ℝ))
    rw [FormalMultilinearSeries.sum,
      ← (ContinuousMultilinearMap.hasSum_eval (hco_summable w hw).hasSum
        (fun _ => (1 : ℝ))).tsum_eq]
    apply tsum_nonneg; intro l
    show 0 ≤ (p.changeOriginSeries j l (fun _ => w)) (fun _ => (1 : ℝ))
    simp only [p, FormalMultilinearSeries.changeOriginSeries,
      ContinuousMultilinearMap.sum_apply]
    apply Finset.sum_nonneg; intro ⟨s, hs⟩ _
    rw [ofScalars_changeOriginSeriesTerm_eval]
    exact mul_nonneg (hB _) (pow_nonneg hw.1.le _)
  -- Non-negativity of c_j by limit
  have hF_nonneg : ∀ w ∈ Ioo (0 : ℝ) 1, 0 ≤ iteratedDeriv j F w := by
    intro w hw; rw [← hderiv_eq w hw]; exact hG_nonneg w hw
  have h_nonneg : 0 ≤ iteratedDeriv j F 1 :=
    ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with w hw
          exact hF_nonneg w hw)
  refine ⟨div_nonneg h_nonneg (Nat.cast_nonneg' _), ?_⟩
  -- Partial sum domination via limit with w^{k-j} intermediate
  intro N
  have h_lhs : Tendsto (fun w : ℝ => ∑ k ∈ range N,
      B k * (Nat.choose k j : ℝ) * w ^ (k - j))
      (𝓝[<] 1) (𝓝 (∑ k ∈ range N, B k * (Nat.choose k j : ℝ))) := by
    have h1 : Tendsto (fun w : ℝ => ∑ k ∈ range N,
        B k * (Nat.choose k j : ℝ) * w ^ (k - j))
        (𝓝[<] 1)
        (𝓝 (∑ k ∈ range N, B k * (Nat.choose k j : ℝ) * 1 ^ (k - j))) := by
      apply tendsto_finset_sum; intro k _
      exact ((continuous_const.mul (continuous_pow (k - j))).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    simp only [one_pow, mul_one] at h1; exact h1
  have h_rhs : Tendsto (fun w : ℝ => iteratedDeriv j F w / (j.factorial : ℝ))
      (𝓝[<] 1) (𝓝 (iteratedDeriv j F 1 / (j.factorial : ℝ))) :=
    Tendsto.div_const (hcont.tendsto.mono_left nhdsWithin_le_nhds) _
  have h_ineq : ∀ᶠ w in 𝓝[<] 1,
      ∑ k ∈ range N, B k * (Nat.choose k j : ℝ) * w ^ (k - j) ≤
        iteratedDeriv j F w / (j.factorial : ℝ) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
    intro w ⟨hw0, hw1⟩
    have hw : w ∈ Ioo (0 : ℝ) 1 := ⟨hw0, hw1⟩
    -- Reduce to changeOrigin value via factorial_smul
    have hiterF : iteratedDeriv j (p.sum) w =
        j.factorial • ((p.changeOrigin w) j (fun _ => 1)) := by
      rw [iteratedDeriv_eq_iteratedFDeriv]
      have hfact := (hball.changeOrigin (hw_in_ball w hw)).factorial_smul (1 : ℝ) j
      rw [zero_add] at hfact; exact hfact.symm
    rw [← hderiv_eq w hw, hiterF, nsmul_eq_mul, mul_div_cancel_left₀ _
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))]
    -- Expand changeOrigin as tsum
    change ∑ k ∈ range N, B k * (Nat.choose k j : ℝ) * w ^ (k - j) ≤
      ((p.changeOriginSeries j).sum w) (fun _ => (1 : ℝ))
    rw [FormalMultilinearSeries.sum,
      ← (ContinuousMultilinearMap.hasSum_eval (hco_summable w hw).hasSum
        (fun _ => (1 : ℝ))).tsum_eq]
    -- Define sequences
    set g := fun l => ((p.changeOriginSeries j l) (fun _ => w)) (fun _ => (1 : ℝ))
    have hg_nn : ∀ l, 0 ≤ g l := by
      intro l; show 0 ≤ ((p.changeOriginSeries j l) (fun _ => w)) (fun _ => (1 : ℝ))
      simp only [FormalMultilinearSeries.changeOriginSeries, ContinuousMultilinearMap.sum_apply]
      exact Finset.sum_nonneg fun ⟨s, hs⟩ _ => by
        rw [ofScalars_changeOriginSeriesTerm_eval]; exact mul_nonneg (hB _) (pow_nonneg hw0.le _)
    have hg_summable : Summable g :=
      (ContinuousMultilinearMap.hasSum_eval (hco_summable w hw).hasSum (fun _ => (1 : ℝ))).summable
    set f := fun k => B k * (Nat.choose k j : ℝ) * w ^ (k - j)
    -- f(l + j) = g(l): each changeOriginSeries term is C(j+l,j) * B(j+l) * w^l
    have hfg : ∀ l, f (l + j) = g l := by
      intro l
      simp only [f, g, show l + j = j + l from by omega, Nat.add_sub_cancel_left]
      symm
      simp only [p, FormalMultilinearSeries.changeOriginSeries,
        ContinuousMultilinearMap.sum_apply]
      simp_rw [ofScalars_changeOriginSeriesTerm_eval]
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      have hcard : Fintype.card {s : Finset (Fin (j + l)) // s.card = l} =
          Nat.choose (j + l) j := by
        rw [Fintype.card_finset_len, Fintype.card_fin, ← Nat.choose_symm_add]
      push_cast [hcard]; ring
    -- f(k) = 0 for k < j (C(k,j) = 0)
    have hf_zero : ∀ k, k < j → f k = 0 := by
      intro k hk
      simp only [f, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, mul_zero, zero_mul]
    -- Summable f via shift equivalence
    have hf_summable : Summable f := by
      rw [← summable_nat_add_iff (f := f) j]
      exact (show (fun l => f (l + j)) = g from funext hfg) ▸ hg_summable
    -- ∑' k, f k = ∑' l, g l (shift by j, killing zero prefix)
    have htsum_eq : ∑' k, f k = ∑' l, g l := by
      have h_shift : HasSum (fun l => f (l + j)) (∑' l, g l) :=
        (funext hfg) ▸ hg_summable.hasSum
      have h_full := (hasSum_nat_add_iff j).mp h_shift
      rw [Finset.sum_eq_zero (fun k hk => hf_zero k (Finset.mem_range.mp hk)),
        add_zero] at h_full
      exact h_full.tsum_eq
    calc ∑ k ∈ range N, f k
        ≤ ∑' k, f k := hf_summable.sum_le_tsum _ (fun k _ =>
          mul_nonneg (mul_nonneg (hB k) (Nat.cast_nonneg' _)) (pow_nonneg hw0.le _))
      _ = ∑' l, g l := htsum_eq
  exact le_of_tendsto_of_tendsto h_lhs h_rhs h_ineq

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
  -- Define c_j = iteratedDeriv j F 1 / j!
  set c := fun j => iteratedDeriv j F 1 / (j.factorial : ℝ) with hc_def
  -- Get HasFPowerSeriesOnBall from AnalyticAt
  obtain ⟨r, hball⟩ := hF_anal.hasFPowerSeriesAt
  have hr_pos := hball.r_pos
  -- Pick a finite δ with ENNReal.ofReal δ ≤ r
  obtain ⟨δ, hδ_pos, hδ_le⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r := by
    by_cases hr_top : r = ⊤
    · exact ⟨1, one_pos, by rw [hr_top]; exact le_top⟩
    · refine ⟨r.toReal, ENNReal.toReal_pos (pos_iff_ne_zero.mp hr_pos) hr_top, ?_⟩
      exact le_of_eq (ENNReal.ofReal_toReal hr_top)
  refine ⟨c, δ, hδ_pos, ?_, ?_, ?_⟩
  · -- c_j ≥ 0
    intro j
    exact (taylor_coeff_nonneg_and_dominates B hB hB_sum F hF_hasSum hF_anal j).1
  · -- Domination
    intro j N
    exact (taylor_coeff_nonneg_and_dominates B hB hB_sum F hF_hasSum hF_anal j).2 N
  · -- HasSum(c_j t^j, F(1+t))
    intro t ht htδ
    have ht_mem : t ∈ EMetric.ball (0 : ℝ) r := by
      rw [EMetric.mem_ball, edist_dist, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht]
      exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mpr htδ) hδ_le
    have hsum := hball.hasSum ht_mem
    simp_rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hsum
    exact hsum

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

/-- Identity theorem extension: if B_k ≥ 0, Summable(B_k c^k) for c ≥ 1,
HasSum(B_k w^k, F(w)) for w ∈ [0,1), and F analytic on [0,c], then
tsum(B_k w^k) = F(w) for w ∈ [0,c).

TRUE: Both w ↦ tsum(B_k w^k) and F are real-analytic on (0,c). They agree on (0,1).
By AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq, they agree on (0,c).
At w = 0: both equal B_0. -/
private lemma tsum_eq_F_of_analytic
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (F : ℝ → ℝ)
    (hF_hasSum : ∀ w, 0 ≤ w → w < 1 → HasSum (fun k => B k * w ^ k) (F w))
    (c : ℝ) (hc1 : 1 ≤ c)
    (hB_sum_c : Summable (fun k => B k * c ^ k))
    (hF_anal : ∀ w, 0 ≤ w → w ≤ c → AnalyticAt ℝ F w)
    (w : ℝ) (hw : 0 ≤ w) (hwc : w < c) :
    ∑' k, B k * w ^ k = F w := by
  -- Case w = 0: both are B 0
  rcases eq_or_lt_of_le hw with rfl | hw_pos
  · have h0 := (hF_hasSum 0 le_rfl (by linarith : (0 : ℝ) < 1)).tsum_eq
    simp only [zero_pow, mul_ite, mul_one, mul_zero, tsum_ite_eq] at h0 ⊢
    exact h0
  -- Case w > 0: use identity theorem on Ioo 0 c
  set G := fun w : ℝ => ∑' k, B k * w ^ k with hG_def
  -- G = F on (0, 1)
  have hGF_lt1 : ∀ v ∈ Ioo (0 : ℝ) 1, G v = F v := by
    intro v hv; exact (hF_hasSum v hv.1.le hv.2).tsum_eq
  -- G analytic on (0, c): from power series ofScalars ℝ B with radius ≥ c
  have hc_nn : (0 : ℝ) ≤ c := by linarith
  have hG_anal : AnalyticOnNhd ℝ G (Ioo 0 c) := by
    intro w₀ hw₀
    -- For w₀ < 1: G agrees with F near w₀, so G is analytic (from hF_anal)
    by_cases hw₀1 : w₀ < 1
    · have hG_eq_F : G =ᶠ[𝓝 w₀] F := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        exact ⟨Ioo 0 1, Ioo_mem_nhds hw₀.1 hw₀1, fun v hv => hGF_lt1 v hv⟩
      exact (hF_anal w₀ hw₀.1.le (by linarith)).congr hG_eq_F.symm
    · -- For w₀ ≥ 1: G is analytic from the power series ofScalars ℝ B with
      -- radius ≥ c > w₀. TRUE by HasFPowerSeriesOnBall + analyticOnNhd.
      -- Pick c' with w₀ < c' < c. G analytic on ball(0, c') from ofScalars.
      push_neg at hw₀1
      -- G = p.sum for p = ofScalars ℝ B with convergence radius ≥ c > w₀
      let p := FormalMultilinearSeries.ofScalars ℝ B
      -- p.sum = G: both are fun v => ∑' n, B n * v ^ n
      have hpG : p.sum = G := by
        ext v; change ∑' n, p n (fun _ => v) = ∑' k, B k * v ^ k
        congr 1; ext n
        show (FormalMultilinearSeries.ofScalars ℝ B) n (fun _ => v) = B n * v ^ n
        rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
      -- Radius of p ≥ c (from Summable(B_k c^k) and ‖p n‖ = B n)
      have h_rad : ENNReal.ofReal c ≤ p.radius := by
        have h_eq : (fun n => ‖p n‖ * c ^ n) = fun k => B k * c ^ k := by
          ext n
          show ‖(FormalMultilinearSeries.ofScalars ℝ B) n‖ * c ^ n = B n * c ^ n
          rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs, abs_of_nonneg (hB n)]
        -- ENNReal.ofReal c = ↑(c.toNNReal) definitionally
        change (↑(Real.toNNReal c) : ENNReal) ≤ p.radius
        refine FormalMultilinearSeries.le_radius_of_summable (p := p) ?_
        rw [show (Real.toNNReal c : ℝ) = c from Real.coe_toNNReal c hc_nn]
        exact h_eq ▸ hB_sum_c
      -- 0 < p.radius (since c ≥ 1 > 0)
      have hr_pos : 0 < p.radius :=
        lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by linarith)) h_rad
      -- w₀ ∈ EMetric.ball 0 p.radius
      have hw₀_ball : w₀ ∈ EMetric.ball (0 : ℝ) p.radius := by
        rw [EMetric.mem_ball, edist_dist, dist_zero_right]
        exact lt_of_lt_of_le
          (by rw [Real.norm_eq_abs, abs_of_pos hw₀.1]
              exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hw₀.1.le).mpr hw₀.2)
          h_rad
      -- p.sum analytic at w₀, hence G analytic at w₀
      exact hpG ▸ (p.hasFPowerSeriesOnBall hr_pos).analyticAt_of_mem hw₀_ball
  -- F analytic on (0, c)
  have hF_analI : AnalyticOnNhd ℝ F (Ioo 0 c) := by
    intro v hv; exact hF_anal v hv.1.le hv.2.le
  -- Identity theorem: G = F on (0, c)
  have h_half_mem : (2⁻¹ : ℝ) ∈ Ioo (0 : ℝ) c := ⟨by positivity, by linarith⟩
  have h_eq_near : G =ᶠ[𝓝 (2⁻¹ : ℝ)] F :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Ioo 0 1, Ioo_mem_nhds (by positivity) (by norm_num),
       fun v hv => hGF_lt1 v hv⟩
  have h_eq : EqOn G F (Ioo 0 c) :=
    hG_anal.eqOn_of_preconnected_of_eventuallyEq hF_analI isPreconnected_Ioo
      h_half_mem h_eq_near
  exact h_eq ⟨hw_pos, hwc⟩

/-- Comparison: Summable at r ≥ w for non-negative series implies Summable at w. -/
private lemma summable_nonneg_of_le
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (r w : ℝ) (hw : 0 ≤ w) (hwr : w ≤ r)
    (hs : Summable (fun k => B k * r ^ k)) :
    Summable (fun k => B k * w ^ k) :=
  Summable.of_nonneg_of_le
    (fun k => mul_nonneg (hB k) (pow_nonneg hw k))
    (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw hwr k) (hB k))
    hs

/-- Generalized partial sum bound at limit point R. -/
private lemma partial_sum_bound_at_limit
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (R : ℝ) (hR : 0 < R)
    (F : ℝ → ℝ)
    (hF_hasSum : ∀ w, 0 ≤ w → w < R → HasSum (fun k => B k * w ^ k) (F w))
    (hF_cont : ContinuousAt F R) (N : ℕ) :
    ∑ k ∈ range N, B k * R ^ k ≤ F R := by
  have h_lhs : Tendsto (fun w : ℝ => ∑ k ∈ range N, B k * w ^ k)
      (𝓝[<] R) (𝓝 (∑ k ∈ range N, B k * R ^ k)) := by
    apply tendsto_finset_sum; intro k _
    exact (Tendsto.mul tendsto_const_nhds
      ((continuous_pow k).continuousAt.tendsto)).mono_left nhdsWithin_le_nhds
  have h_rhs : Tendsto F (𝓝[<] R) (𝓝 (F R)) :=
    hF_cont.tendsto.mono_left nhdsWithin_le_nhds
  have h_ineq : ∀ᶠ w in 𝓝[<] R, ∑ k ∈ range N, B k * w ^ k ≤ F w := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < R by positivity)]
    intro w ⟨hw0, hw1⟩
    exact partial_sum_le_of_hasSum B hB w hw0.le (F w) (hF_hasSum w hw0.le hw1) N
  exact le_of_tendsto_of_tendsto h_lhs h_rhs h_ineq

theorem pringsheim_real_extension
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (hB_sum : Summable B)
    (F : ℝ → ℝ)
    (hF_hasSum : ∀ w, 0 ≤ w → w < 1 → HasSum (fun k => B k * w ^ k) (F w))
    (W : ℝ) (hW : 1 < W)
    (hF_anal : ∀ w, 0 ≤ w → w ≤ W → AnalyticAt ℝ F w) :
    Summable (fun k => B k * W ^ k) := by
  -- sSup contradiction approach
  by_contra h_ns
  -- S = {r ∈ [0,W] : Summable(B_k r^k)}
  set S := {r : ℝ | 0 ≤ r ∧ r ≤ W ∧ Summable (fun k => B k * r ^ k)} with hS_def
  have hS_ne : S.Nonempty :=
    ⟨1, by linarith, hW.le, by simpa [one_pow, mul_one] using hB_sum⟩
  have hS_bdd : BddAbove S := ⟨W, fun r hr => hr.2.1⟩
  set R := sSup S with hR_def
  have hR_ge : 1 ≤ R := le_csSup hS_bdd ⟨by linarith, hW.le,
    by simpa [one_pow, mul_one] using hB_sum⟩
  have hR_le : R ≤ W := csSup_le hS_ne (fun r hr => hr.2.1)
  have hR_pos : 0 < R := by linarith
  -- Key: HasSum(B_k w^k, F(w)) for w ∈ [0, R)
  have hF_hasSum_ext : ∀ w, 0 ≤ w → w < R →
      HasSum (fun k => B k * w ^ k) (F w) := by
    intro w hw hwR
    -- For w < 1: directly from hypothesis
    by_cases hw1 : w < 1
    · exact hF_hasSum w hw hw1
    -- For w ≥ 1: find c ∈ S with c > w, use identity theorem
    · push_neg at hw1
      obtain ⟨c, hcS, hcw⟩ := lt_csSup_iff hS_bdd hS_ne |>.mp hwR
      have hcw' : w < c := hcw
      have hBc : Summable (fun k => B k * c ^ k) := hcS.2.2
      have hBw : Summable (fun k => B k * w ^ k) :=
        summable_nonneg_of_le B hB c w hw hcw'.le hBc
      rw [← tsum_eq_F_of_analytic B hB F hF_hasSum c (by linarith : 1 ≤ c) hBc
        (fun v hv hvc => hF_anal v hv (hvc.trans hcS.2.1)) w hw hcw']
      exact hBw.hasSum
  -- F continuous at R (from analyticity when R < W, or R = W and analytic at W)
  have hF_cont_R : ContinuousAt F R :=
    (hF_anal R (by linarith) hR_le).continuousAt
  -- Summable at R via partial sum bound
  have hsum_R : Summable (fun k => B k * R ^ k) :=
    summable_from_partial_sum_bound B hB R hR_pos.le (F R)
      (fun N => partial_sum_bound_at_limit B hB R hR_pos F hF_hasSum_ext hF_cont_R N)
  -- If R = W: contradiction
  rcases eq_or_lt_of_le hR_le with hRW | hRW
  · exact h_ns (hRW ▸ hsum_R)
  -- R < W: extend past R via partial_sum_bound_past_one (rescaled)
  -- Rescale: B̃_k = B_k R^k, F̃(w) = F(R·w)
  set B' := fun k => B k * R ^ k with hB'_def
  set F' := fun w => F (R * w) with hF'_def
  have hB'_nn : ∀ k, 0 ≤ B' k := fun k => mul_nonneg (hB k) (pow_nonneg hR_pos.le k)
  have hB'_sum : Summable B' := by simpa [hB'_def, one_pow, mul_one] using hsum_R
  have hF'_hasSum : ∀ w, 0 ≤ w → w < 1 →
      HasSum (fun k => B' k * w ^ k) (F' w) := by
    intro w hw hw1
    have hRw_lt : R * w < R := by nlinarith
    have hRw_nn : 0 ≤ R * w := mul_nonneg hR_pos.le hw
    have h := hF_hasSum_ext (R * w) hRw_nn hRw_lt
    have h_eq : ∀ k, B k * (R * w) ^ k = B' k * w ^ k := by
      intro k; simp [hB'_def, mul_pow]; ring
    simpa [h_eq, hF'_def] using h
  have hF'_anal : AnalyticAt ℝ F' 1 := by
    show AnalyticAt ℝ (fun w => F (R * w)) 1
    have : AnalyticAt ℝ F (R * 1) := by simpa using hF_anal R (by linarith) hR_le
    exact this.comp (analyticAt_const.mul analyticAt_id)
  -- Get δ > 0 with partial sums past 1
  obtain ⟨δ, hδ, hbound⟩ := partial_sum_bound_past_one B' hB'_nn hB'_sum F'
    hF'_hasSum hF'_anal
  -- Summable at R(1 + δ/2) > R
  have hδ2 : 0 < δ / 2 := by linarith
  have hδ2_lt : δ / 2 < δ := by linarith
  have hsum_ext : Summable (fun k => B' k * (1 + δ / 2) ^ k) :=
    summable_from_partial_sum_bound B' hB'_nn (1 + δ / 2) (by linarith) (F' (1 + δ / 2))
      (fun N => hbound (δ / 2) hδ2.le hδ2_lt N)
  -- Convert back: Summable(B_k (R(1+δ/2))^k)
  have h_conv : ∀ k, B' k * (1 + δ / 2) ^ k = B k * (R * (1 + δ / 2)) ^ k := by
    intro k; simp [hB'_def, mul_pow]; ring
  have hsum_new : Summable (fun k => B k * (R * (1 + δ / 2)) ^ k) := by
    rwa [show (fun k => B' k * (1 + δ / 2) ^ k) = (fun k => B k * (R * (1 + δ / 2)) ^ k)
      from funext h_conv] at hsum_ext
  -- R(1+δ/2) ∈ S (need R(1+δ/2) ≤ W)
  have hRδ_gt : R < R * (1 + δ / 2) := by nlinarith
  have hRδ_le : R * (1 + δ / 2) ≤ W := by
    by_contra h_gt; push_neg at h_gt
    -- If R(1+δ/2) > W, then W < R(1+δ/2) and Summable at R(1+δ/2)
    -- So Summable at W by comparison
    exact h_ns (summable_nonneg_of_le B hB (R * (1 + δ / 2)) W (by linarith) h_gt.le hsum_new)
  have hRδ_in_S : R * (1 + δ / 2) ∈ S :=
    ⟨by positivity, hRδ_le, hsum_new⟩
  -- Contradiction: R(1+δ/2) > R = sSup S but R(1+δ/2) ∈ S
  exact not_le.mpr hRδ_gt (le_csSup hS_bdd hRδ_in_S)

end Aristotle.Standalone.PringsheimRealBootstrap
