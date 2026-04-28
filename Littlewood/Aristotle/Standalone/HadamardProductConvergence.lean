/-
# Hadamard partial product convergence for xi

Proves that the Hadamard partial products for xi converge locally uniformly,
via `Summable.hasProdUniformlyOn_one_add` (Weierstrass M-test for products)
and a metric argument for the continuous prefactor.

## Status
- E1 norm bounds: PROVED
- M-test per-factor bound: PROVED
- Product convergence + prefactor: PROVED (via hasProdUniformlyOn_one_add)
- Main theorem `hadamard_xi_convergence`: PROVED, 0 sorry

## Integration
When used with AnalyticAxioms, this re-enables the Hadamard chain:
HadamardXiCanonicalProductApprox -> HadamardXiCore -> ZetaLogDerivBound.
-/

import Littlewood.Aristotle.Standalone.HadamardFactorizationXi

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HadamardProductConvergence

open Complex Filter Topology Set HadamardXi

/-! ### E1 norm bounds (PROVED)

The genus-1 Weierstrass elementary factor E1(z) = (1-z)*exp(z).
Key bound: |E1(z)-1| <= 3|z|^2 for |z| <= 1. -/

/-- Genus-1 Weierstrass elementary factor. -/
def E1 (z : ℂ) : ℂ := (1 - z) * exp z

lemma E1_sub_one_eq (z : ℂ) :
    E1 z - 1 = (exp z - 1 - z) - z * (exp z - 1) := by
  unfold E1; ring

/-- |E1(z) - 1| <= 3|z|^2 for |z| <= 1. -/
lemma E1_sub_one_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖E1 z - 1‖ ≤ 3 * ‖z‖ ^ 2 := by
  rw [E1_sub_one_eq]
  have h1 : ‖exp z - 1 - z‖ ≤ ‖z‖ ^ 2 := by
    simpa using norm_exp_sub_one_sub_id_le hz
  have h2 : ‖exp z - 1‖ ≤ 2 * ‖z‖ := by
    simpa using norm_exp_sub_one_le hz
  calc ‖(exp z - 1 - z) - z * (exp z - 1)‖
      ≤ ‖exp z - 1 - z‖ + ‖z * (exp z - 1)‖ := norm_sub_le _ _
    _ ≤ ‖z‖ ^ 2 + ‖z‖ * (2 * ‖z‖) := by
        gcongr
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left h2 (norm_nonneg z)
    _ = 3 * ‖z‖ ^ 2 := by ring

/-- M-test bound: for |s| <= R < |rho|, |E1(s/rho) - 1| <= 3R^2/|rho|^2. -/
lemma E1_factor_norm_le {R : ℝ} (hR : 0 < R) (ρ : ℂ) (hρ : R < ‖ρ‖)
    {s : ℂ} (hs : ‖s‖ ≤ R) :
    ‖E1 (s / ρ) - 1‖ ≤ 3 * R ^ 2 / ‖ρ‖ ^ 2 := by
  have hρ_ne : ρ ≠ 0 := by intro h; rw [h, norm_zero] at hρ; linarith
  have : ‖s / ρ‖ ≤ 1 := by
    rw [norm_div]; exact div_le_one_of_le₀ (by linarith) (by positivity)
  calc ‖E1 (s / ρ) - 1‖ ≤ 3 * ‖s / ρ‖ ^ 2 := E1_sub_one_norm_le this
    _ = 3 * (‖s‖ / ‖ρ‖) ^ 2 := by rw [norm_div]
    _ ≤ 3 * (R / ‖ρ‖) ^ 2 := by gcongr
    _ = 3 * R ^ 2 / ‖ρ‖ ^ 2 := by ring

/-! ### Conversion between E1 and epShifted -/

/-- `E1 (s / ρ) = epShifted 1 ρ s`: the local definition agrees with the
Weierstrass factor library. -/
lemma E1_eq_epShifted (ρ s : ℂ) :
    E1 (s / ρ) = WeierstrassFactors.epShifted 1 ρ s := by
  rw [WeierstrassFactors.ep_one_shifted]; rfl

/-! ### Main convergence theorem

Uses `Summable.hasProdUniformlyOn_one_add` (Weierstrass M-test for products)
available in Mathlib 4.27, plus a metric argument for the continuous prefactor. -/

/-- The Hadamard partial products for xi converge locally uniformly.
Given the Hadamard identity, summability of 1/|rho|^2, and nonzero zeros,
the partial products converge locally uniformly to xi. -/
theorem hadamard_xi_convergence
    (B : ℂ) (zeros : ℕ → ℂ)
    (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hident : ∀ s, RiemannXiAlt s = RiemannXiAlt 0 * exp (B * s) *
        ∏' n, E1 (s / zeros n)) :
    HadamardXiPartialProductsTendstoHyp B zeros := by
  -- The target unfolds to TendstoLocallyUniformlyOn ... RiemannXiAlt atTop Set.univ
  -- Step 1: Reduce to compact sets (ℂ is locally compact)
  rw [HadamardXiPartialProductsTendstoHyp,
      tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _hKuniv hKcompact
  -- Step 2: Use the metric characterization of TendstoUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Step 3: Obtain uniform product convergence on K via M-test
  -- Get a bound R_K on ‖x‖ for x ∈ K (compact ⊂ ℂ is bounded)
  obtain ⟨R_K, hR_K⟩ : ∃ R_K, ∀ x ∈ K, ‖x‖ ≤ R_K :=
    hKcompact.isBounded.exists_norm_le
  -- The summable bound for the M-test: u n = 3 * R_K² / ‖zeros n‖²
  set u : ℕ → ℝ := fun n => 3 * R_K ^ 2 * (1 / ‖zeros n‖ ^ 2)
  have hu : Summable u := hsum.mul_left (3 * R_K ^ 2)
  -- Bound: for large enough n (‖zeros n‖ > 2*R_K), |epShifted(...) - 1| ≤ u n on K
  have hf_bound : ∀ᶠ n in Filter.cofinite,
      ∀ x ∈ K, ‖WeierstrassFactors.epShifted 1 (zeros n) x - 1‖ ≤ u n := by
    -- Since Σ 1/|ρ_n|² converges, eventually |ρ_n| > 2R_K, so |x/ρ_n| ≤ 1/2 on K
    -- Since Σ 1/|ρ_n|² converges, 1/|ρ_n|² → 0 (at cofinite), so |ρ_n| → ∞.
    -- Eventually |x/ρ_n| ≤ 1/2 for all x ∈ K, giving the norm bound.
    set R := max R_K 1 with hR_def
    have hR_pos : (0 : ℝ) < R := by positivity
    -- Eventually ‖zeros n‖ > 2R (since 1/‖zeros n‖² → 0)
    have hlarge : ∀ᶠ n in Filter.cofinite, ‖zeros n‖ > 2 * R := by
      rw [Nat.cofinite_eq_atTop]
      have htend := hsum.tendsto_atTop_zero
      rw [NormedAddCommGroup.tendsto_atTop] at htend
      obtain ⟨N, hN⟩ := htend (1 / (2 * R) ^ 2) (by positivity)
      filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun m hm => hN m hm⟩] with n hn
      have hρ_pos : 0 < ‖zeros n‖ := norm_pos_iff.mpr (hne n)
      simp only [sub_zero] at hn
      rw [Real.norm_of_nonneg (div_nonneg one_pos.le (sq_nonneg _))] at hn
      -- hn : 1 / ‖zeros n‖² < 1 / (2R)²
      rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < ‖zeros n‖ ^ 2) (by positivity)] at hn
      nlinarith [sq_nonneg (‖zeros n‖ - 2 * R)]
    filter_upwards [hlarge] with n hn x hx
    have hρ_pos : 0 < ‖zeros n‖ := norm_pos_iff.mpr (hne n)
    have hR_K_bound := hR_K x hx
    have hquot : ‖x / zeros n‖ ≤ 1 / 2 := by
      rw [norm_div]
      calc ‖x‖ / ‖zeros n‖ ≤ R_K / ‖zeros n‖ := by gcongr
        _ ≤ R / ‖zeros n‖ := by gcongr; exact le_max_left _ _
        _ ≤ R / (2 * R) := by apply div_le_div_of_nonneg_left hR_pos.le (by positivity) (by linarith)
        _ = 1 / 2 := by field_simp
    calc ‖WeierstrassFactors.epShifted 1 (zeros n) x - 1‖
        = ‖1 - WeierstrassFactors.epShifted 1 (zeros n) x‖ := norm_sub_rev _ _
      _ ≤ 3 * ‖x / zeros n‖ ^ 2 :=
          WeierstrassFactors.norm_one_sub_ep_one_shifted_le hquot
      _ = 3 * (‖x‖ / ‖zeros n‖) ^ 2 := by rw [norm_div]
      _ ≤ 3 * (R_K / ‖zeros n‖) ^ 2 := by gcongr
      _ = 3 * R_K ^ 2 * (1 / ‖zeros n‖ ^ 2) := by ring
  have hf_cts : ∀ n, ContinuousOn
      (fun x => WeierstrassFactors.epShifted 1 (zeros n) x - 1) K :=
    fun n => ((WeierstrassFactors.differentiable_epShifted 1 (zeros n)).continuous.sub
      continuous_const).continuousOn
  -- Apply the M-test for products
  have hprod_unif : HasProdUniformlyOn
      (fun n x => WeierstrassFactors.epShifted 1 (zeros n) x)
      (fun x => ∏' n, WeierstrassFactors.epShifted 1 (zeros n) x) K := by
    have hmtest := Summable.hasProdUniformlyOn_one_add hKcompact hu hf_bound hf_cts
    -- hmtest has form (1 + (epShifted - 1)) = epShifted, simplify
    have hsimp : ∀ (i : ℕ) (x : ℂ),
        1 + (WeierstrassFactors.epShifted 1 (zeros i) x - 1) =
        WeierstrassFactors.epShifted 1 (zeros i) x := fun _ _ => by ring
    refine (hmtest.congr (Eventually.of_forall fun s => fun x _ =>
      Finset.prod_congr rfl (fun i _ => hsimp i x))).congr_right
      (fun x _ => tprod_congr (fun n => hsimp n x))
  -- Step 4: Get TendstoUniformlyOn for the product partial sums
  have hprod_range := hprod_unif.tendstoUniformlyOn_finsetRange
  -- hprod_range : TendstoUniformlyOn (fun N x => ∏ i ∈ range N, epShifted ...) (∏' ...) atTop K
  -- Step 5: Bound the prefactor on K
  have hprefactor_cts : ContinuousOn (fun s => RiemannXiAlt 0 * exp (B * s)) K :=
    continuousOn_const.mul ((continuous_const.mul continuous_id).cexp.continuousOn)
  obtain ⟨M, hM_pos, hM_bound⟩ : ∃ M > 0, ∀ s ∈ K, ‖RiemannXiAlt 0 * exp (B * s)‖ ≤ M := by
    -- Continuous ℂ-valued function on compact K has bounded norm
    obtain ⟨M₀, hM₀⟩ := hKcompact.exists_bound_of_continuousOn hprefactor_cts
    exact ⟨max M₀ 1, by positivity, fun s hs => (hM₀ s hs).trans (le_max_left _ _)⟩
  -- Step 6: Combine: prefactor bound + uniform product convergence → full convergence
  -- From hprod_range, get: for large N, dist (∏' n, g n x) (∏ range N, g n x) < ε / M
  have hε' : ε / M > 0 := div_pos hε hM_pos
  rw [Metric.tendstoUniformlyOn_iff] at hprod_range
  filter_upwards [hprod_range (ε / M) hε'] with N hN x hx
  -- Step 7: Use hident to identify RiemannXiAlt with the product expression
  have hE1_eq : ∀ n, E1 (x / zeros n) = WeierstrassFactors.epShifted 1 (zeros n) x :=
    fun n => E1_eq_epShifted (zeros n) x
  -- Rewrite RiemannXiAlt x using hident
  have htprod_eq : ∏' n, E1 (x / zeros n) =
      ∏' n, WeierstrassFactors.epShifted 1 (zeros n) x :=
    tprod_congr (fun n => hE1_eq n)
  set P := ∏' n, WeierstrassFactors.epShifted 1 (zeros n) x with hP_def
  set P_N := ∏ i ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros i) x with hPN_def
  set c := RiemannXiAlt 0 * exp (B * x) with hc_def
  -- Goal: dist (RiemannXiAlt x) (RiemannXiAlt 0 * (exp (B * x) * P_N)) < ε
  -- Rewrite LHS using hident
  have hrw_lhs : RiemannXiAlt x = c * P := by
    rw [hc_def, hident x, htprod_eq, mul_assoc]
  have hrw_rhs : RiemannXiAlt 0 * (exp (B * x) * P_N) = c * P_N := by
    rw [hc_def, mul_assoc]
  rw [hrw_lhs, hrw_rhs, dist_eq_norm, ← mul_sub, norm_mul, ← dist_eq_norm]
  calc ‖c‖ * dist P P_N
      ≤ M * dist P P_N := by
        gcongr
        exact hM_bound x hx
    _ < M * (ε / M) := by
        gcongr
        exact hN x hx
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hM_pos)

end Aristotle.Standalone.HadamardProductConvergence
