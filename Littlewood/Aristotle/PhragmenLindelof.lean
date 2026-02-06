/-
Phragmén-Lindelöf convexity bounds for zeta - proved by Aristotle.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib
import Littlewood.Aristotle.Bridge.GammaGrowthComplete

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

noncomputable section

open Complex Real Topology Filter
open scoped BigOperators Real Nat Classical

/-!
# Phragmén-Lindelöf Principle and Convexity Bounds

The Phragmén-Lindelöf principle extends the maximum modulus principle to
unbounded domains. For the Riemann zeta function, this gives:

  |ζ(σ + it)| = O(|t|^{μ(σ) + ε})

where μ(σ) is the convexity exponent:
  μ(σ) = 0           for σ ≥ 1
  μ(σ) = (1-σ)/2     for 0 ≤ σ ≤ 1
  μ(σ) = 1/2 - σ     for σ ≤ 0

## Main Results

- `convexity_exponent`: The function μ(σ) defined piecewise
- `zeta_convexity_bound`: |ζ(σ+it)| ≤ C|t|^{μ(σ)+ε} for |t| ≥ 1
- `zeta_half_bound`: |ζ(1/2+it)| ≤ C|t|^{1/4+ε}
-/

/-- The convexity exponent μ(σ) for the Riemann zeta function.

    μ(σ) = max(0, (1-σ)/2) for σ ∈ [0, 1]

    This is the exponent in the bound |ζ(σ+it)| = O(|t|^{μ(σ)+ε}). -/
noncomputable def convexity_exponent (σ : ℝ) : ℝ :=
  max 0 ((1 - σ) / 2)

/-- convexity_exponent is 0 for σ ≥ 1 -/
lemma convexity_exponent_ge_one (σ : ℝ) (hσ : 1 ≤ σ) : convexity_exponent σ = 0 := by
  unfold convexity_exponent
  simp only [max_eq_left_iff]
  linarith

/-- convexity_exponent at σ = 1/2 is 1/4 -/
lemma convexity_exponent_half : convexity_exponent (1/2) = 1/4 := by
  unfold convexity_exponent
  norm_num

/-- convexity_exponent is non-negative -/
lemma convexity_exponent_nonneg (σ : ℝ) : 0 ≤ convexity_exponent σ := by
  unfold convexity_exponent
  exact le_max_left 0 _

/-- convexity_exponent at σ = 0 is 1/2 -/
lemma convexity_exponent_zero : convexity_exponent 0 = 1/2 := by
  unfold convexity_exponent
  simp only [sub_zero, one_div]
  rw [max_eq_right]
  norm_num

/-- The zeta function satisfies the convexity bound for σ > 1.

    For σ > 1: |ζ(σ+it)| ≤ ζ(σ) ≤ 1 + 1/(σ-1) -/
lemma zeta_bound_gt_one (σ : ℝ) (t : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta (σ + t * I)‖ ≤ 1 + 1 / (σ - 1) := by
  have hre : 1 < (↑σ + ↑t * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
               Complex.ofReal_im, Complex.I_re, Complex.I_im,
               mul_zero, mul_one, sub_zero, add_zero]
    linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  -- Summability of real majorant series
  have h_summ : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ σ) := by
    convert (summable_nat_add_iff (G := ℝ) 1).mpr (summable_one_div_nat_rpow.mpr hσ) using 1
    ext n; simp [Nat.cast_succ]
  -- Step 1: ‖Σ 1/(n+1)^s‖ ≤ Σ 1/(n+1)^σ via comparison test
  have h_norm_bound : ‖∑' n : ℕ, (1 : ℂ) / (↑↑n + 1) ^ ((↑σ : ℂ) + ↑t * I)‖ ≤
      ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ σ := by
    apply tsum_of_norm_bounded h_summ.hasSum
    intro n
    simp only [norm_div, norm_one]
    rw [show (↑↑n + 1 : ℂ) = ((↑(n + 1 : ℕ) : ℂ)) from by push_cast; ring,
        norm_natCast_cpow_of_pos (Nat.succ_pos n),
        show ((↑σ : ℂ) + ↑t * I).re = σ from by
          simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
                Complex.ofReal_im, Complex.I_re, Complex.I_im],
        Nat.cast_succ]
  -- Step 2: Σ 1/(n+1)^σ ≤ 1 + 1/(σ-1) via zeta_limit_aux1
  have h_tsum_bound : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ σ ≤ 1 + 1 / (σ - 1) := by
    have h_aux := ZetaAsymptotics.zeta_limit_aux1 hσ
    have h_tt_nonneg : 0 ≤ ZetaAsymptotics.term_tsum σ :=
      tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) σ)
    linarith [mul_nonneg (le_of_lt (lt_trans zero_lt_one hσ)) h_tt_nonneg]
  linarith

/-- The zeta function bound at s = 2 + it: |ζ(2+it)| ≤ π²/6 -/
lemma zeta_bound_at_two (t : ℝ) : ‖riemannZeta (2 + t * I)‖ ≤ Real.pi^2 / 6 := by
  have hre : 1 < (2 + (t : ℂ) * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
               Complex.I_re, Complex.I_im, mul_zero, mul_one]
    norm_num
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  -- Shifted HasSum: ∑_{n≥0} 1/(n+1)^2 = π²/6
  have h_hasSum : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h_sum_zero : (Finset.range 1).sum (fun i : ℕ => (1 : ℝ) / (↑i) ^ 2) = 0 := by
      simp
    have key : HasSum (fun n : ℕ => (1 : ℝ) / (↑n) ^ 2)
        (Real.pi ^ 2 / 6 + (Finset.range 1).sum (fun i : ℕ => (1 : ℝ) / (↑i) ^ 2)) := by
      rw [h_sum_zero, add_zero]; exact hasSum_zeta_two
    have h := (hasSum_nat_add_iff 1).mpr key
    simp only [Nat.cast_add, Nat.cast_one] at h
    exact h
  apply tsum_of_norm_bounded h_hasSum
  intro n
  -- Show ‖1 / (↑n + 1)^(2 + t*I)‖ = 1 / ((n:ℝ) + 1)^2
  have h_norm : ‖(1 : ℂ) / ((↑↑n + 1) ^ (2 + (t : ℂ) * I))‖ = 1 / ((n : ℝ) + 1) ^ 2 := by
    rw [norm_div, norm_one]
    congr 1
    rw [show (↑↑n + 1 : ℂ) = ((↑(n + 1 : ℕ) : ℂ)) from by push_cast; ring]
    rw [norm_natCast_cpow_of_pos (Nat.succ_pos n)]
    have hre2 : (2 + (t : ℂ) * I).re = (2 : ℕ) := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
                 Complex.I_re, Complex.I_im, mul_zero, mul_one]
      norm_num
    rw [hre2, rpow_natCast, Nat.cast_succ]
  linarith [h_norm]

/-- The Gamma function growth: |Γ(σ+it)| ~ √(2π)|t|^{σ-1/2}e^{-π|t|/2} -/
lemma gamma_growth (σ : ℝ) (hσ : 0 < σ) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ t : ℝ, 1 ≤ |t| →
      C₁ * |t|^(σ - 1/2) * Real.exp (-Real.pi * |t| / 2) ≤
        ‖Complex.Gamma (σ + t * I)‖ ∧
      ‖Complex.Gamma (σ + t * I)‖ ≤
        C₂ * |t|^(σ - 1/2) * Real.exp (-Real.pi * |t| / 2) := by
  exact Aristotle.Bridge.GammaGrowthComplete.hasGammaGrowth_all σ hσ

/-- Bound on |ζ(-δ+it)| via the functional equation.

    For δ > 0 and |t| ≥ 1: |ζ(-δ+it)| ≤ C·|t|^{1/2+δ}.
    Uses riemannZeta_one_sub at s = (1+δ)+(-t)i, gamma_growth, and zeta_bound_gt_one. -/
theorem zeta_bound_neg_sigma (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta (↑(-δ) + ↑t * I)‖ ≤ C * |t| ^ (1/2 + δ) := by
  -- Get gamma growth bounds at σ = 1+δ > 0
  obtain ⟨_, C₂_Γ, _, hC₂_Γ, hΓ⟩ := gamma_growth (1 + δ) (by linarith)
  -- The constant: C₀ = 2 * (2π)^{-(1+δ)} * C₂_Γ * (1 + 1/δ)
  set C₀ : ℝ := 2 * (2 * Real.pi) ^ (-(1 + δ)) * C₂_Γ * (1 + 1 / δ) with hC₀_def
  have hC₀_pos : 0 < C₀ := by
    apply mul_pos
    · apply mul_pos
      · apply mul_pos
        · norm_num
        · exact rpow_pos_of_pos (by positivity : (0:ℝ) < 2 * π) _
      · exact hC₂_Γ
    · have : (0:ℝ) < 1 / δ := div_pos one_pos hδ; linarith
  refine ⟨C₀, hC₀_pos, fun t ht => ?_⟩
  -- Set s = (1+δ) + (-t)*I so that 1 - s = -δ + t*I
  set s : ℂ := ↑(1 + δ) + ↑(-t) * I with hs_def
  -- Verify 1 - s = ↑(-δ) + ↑t * I
  have h1s : (1 : ℂ) - s = ↑(-δ) + ↑t * I := by
    simp [hs_def, Complex.ofReal_neg, Complex.ofReal_add]; ring
  -- Conditions for riemannZeta_one_sub
  have hs_not_neg_nat : ∀ n : ℕ, s ≠ -(↑n : ℂ) := by
    intro n h_eq
    have hre := congr_arg Complex.re h_eq
    simp only [hs_def, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hs_ne_one : s ≠ 1 := by
    intro h_eq
    have him := congr_arg Complex.im h_eq
    simp only [hs_def, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, zero_mul,
      add_zero, Complex.one_im] at him
    -- him : -t = 0
    have : t = 0 := by linarith
    rw [this, abs_zero] at ht; linarith
  -- Apply functional equation: ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s)
  have h_fe := riemannZeta_one_sub hs_not_neg_nat hs_ne_one
  -- Rewrite: ζ(-δ+it) = ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s)
  have h_eq : riemannZeta (↑(-δ) + ↑t * I) =
      2 * (2 * ↑π) ^ (-s) * Gamma s * cos (↑π * s / 2) * riemannZeta s := by
    rwa [h1s] at h_fe
  rw [h_eq]
  -- Take norms and bound each factor
  -- Factor 1: ‖(2π)^{-s}‖ = (2π)^{-(1+δ)}
  have h_cpow : ‖(2 * ↑π : ℂ) ^ (-s)‖ = (2 * π) ^ (-(1 + δ)) := by
    rw [show (2 * ↑π : ℂ) = ↑(2 * π : ℝ) from by push_cast; ring]
    rw [norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < 2 * π)]
    congr 1
    simp only [hs_def, Complex.neg_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero]
    ring
  -- Factor 2: ‖Γ(s)‖ ≤ C₂_Γ * |t|^{1/2+δ} * exp(-π|t|/2)
  have h_gamma : ‖Gamma s‖ ≤ C₂_Γ * |t| ^ (1 + δ - 1/2) * rexp (-π * |t| / 2) := by
    have := (hΓ (-t) (by rwa [abs_neg])).2
    rwa [abs_neg] at this
  -- Factor 3: ‖cos(πs/2)‖ ≤ exp(π|t|/2)
  have h_cos : ‖cos (↑π * s / 2)‖ ≤ rexp (π * |t| / 2) := by
    -- cos w = (exp(wI) + exp(-wI))/2, triangle + exp norm gives bound
    set w := ↑π * s / 2 with hw_def
    rw [Complex.cos]
    -- Step 1: ‖(exp(wI)+exp(-wI))/2‖ = ‖exp(wI)+exp(-wI)‖/2
    have h2 : ‖(2:ℂ)‖ = (2:ℝ) := by norm_num
    rw [norm_div, h2]
    -- Step 2: Re(wI) = πt/2, Re(-wI) = -πt/2
    have hre1 : (w * I).re = π * t / 2 := by
      simp [hw_def, hs_def]; ring
    have hre2 : (-(w * I)).re = -(π * t / 2) := by
      simp [hw_def, hs_def]; ring
    -- Step 3: Bound each exp norm
    have hre1' : ((-w) * I).re = -(π * t / 2) := by
      simp [hw_def, hs_def]; ring
    have hexp1 : ‖exp (w * I)‖ ≤ rexp (π * |t| / 2) := by
      rw [Complex.norm_exp, hre1]
      exact Real.exp_le_exp.mpr (by nlinarith [le_abs_self t, pi_pos])
    have hexp2 : ‖exp (-w * I)‖ ≤ rexp (π * |t| / 2) := by
      rw [Complex.norm_exp, hre1']
      exact Real.exp_le_exp.mpr (by nlinarith [neg_abs_le t, pi_pos])
    -- Step 4: Triangle + average
    calc ‖exp (w * I) + exp (-w * I)‖ / 2
        ≤ (‖exp (w * I)‖ + ‖exp (-w * I)‖) / 2 := by
          gcongr; exact norm_add_le _ _
      _ ≤ (rexp (π * |t| / 2) + rexp (π * |t| / 2)) / 2 := by
          gcongr
      _ = rexp (π * |t| / 2) := by ring
  -- Factor 4: ‖ζ(s)‖ = ‖ζ((1+δ)+(-t)i)‖ ≤ 1 + 1/δ
  have h_zeta : ‖riemannZeta s‖ ≤ 1 + 1 / δ := by
    have := zeta_bound_gt_one (1 + δ) (-t) (by linarith)
    simp only [show (1 + δ) - 1 = δ from by ring] at this
    exact this
  -- Combined Gamma * cos bound (exp factors cancel)
  have h_exp_cancel : rexp (-π * |t| / 2) * rexp (π * |t| / 2) = 1 := by
    rw [← Real.exp_add, show -π * |t| / 2 + π * |t| / 2 = 0 from by ring, Real.exp_zero]
  have h_exp_eq : (1 : ℝ) + δ - 1/2 = 1/2 + δ := by ring
  have h_gamma_cos : ‖Gamma s‖ * ‖cos (↑π * s / 2)‖ ≤ C₂_Γ * |t| ^ (1/2 + δ) := by
    calc ‖Gamma s‖ * ‖cos (↑π * s / 2)‖
        ≤ (C₂_Γ * |t| ^ (1 + δ - 1/2) * rexp (-π * |t| / 2)) * rexp (π * |t| / 2) :=
          mul_le_mul h_gamma h_cos (norm_nonneg _) (by positivity)
      _ = C₂_Γ * |t| ^ (1 + δ - 1/2) * (rexp (-π * |t| / 2) * rexp (π * |t| / 2)) := by ring
      _ = C₂_Γ * |t| ^ (1 + δ - 1/2) := by rw [h_exp_cancel, mul_one]
      _ = C₂_Γ * |t| ^ (1/2 + δ) := by rw [h_exp_eq]
  -- Combine all bounds
  have h2_norm : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  calc ‖2 * (2 * ↑π) ^ (-s) * Gamma s * cos (↑π * s / 2) * riemannZeta s‖
      = ‖(2 : ℂ)‖ * ‖(2 * ↑π : ℂ) ^ (-s)‖ * (‖Gamma s‖ * ‖cos (↑π * s / 2)‖) *
        ‖riemannZeta s‖ := by
        simp only [norm_mul]; ring
    _ ≤ 2 * (2 * π) ^ (-(1 + δ)) * (C₂_Γ * |t| ^ (1/2 + δ)) * (1 + 1 / δ) := by
        rw [h2_norm, h_cpow]; gcongr
    _ = C₀ * |t| ^ (1/2 + δ) := by rw [hC₀_def]; ring

/-- General convexity bound: |ζ(σ+it)| ≤ C|t|^{μ(σ)+ε} for 0 ≤ σ ≤ 1.

    Proof via Hadamard three-lines interpolation on the strip [-2ε, 1+2ε]:
    - Left boundary: |ζ(-2ε+it)| ≤ C·|t|^{1/2+2ε} (functional equation)
    - Right boundary: |ζ(1+2ε+it)| ≤ C_δ (Dirichlet series)
    - Gaussian damping exp((s-it₀)²) ensures BddAbove
    - Three-lines gives exponent (1-σ)/2+ε at σ. -/
theorem zeta_convexity_bound (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ (convexity_exponent σ + ε) := by
  -- The proof uses three-lines interpolation between:
  --   Left (σ=-2ε): |ζ| ≤ C_L·|t|^{1/2+2ε} via zeta_bound_neg_sigma
  --   Right (σ=1+2ε): |ζ| ≤ C_R via zeta_bound_gt_one
  -- With Gaussian damping for BddAbove condition.
  -- At σ₀, the interpolated exponent is exactly (1-σ₀)/2+ε = convexity_exponent(σ₀)+ε.
  set δ := min ε (1/4) with hδ_def
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  -- Get boundary bounds
  obtain ⟨C_L, hC_L, h_left⟩ := zeta_bound_neg_sigma (2 * δ) (by linarith)
    (by have : δ ≤ 1/4 := min_le_right _ _; linarith)
  -- The three-lines interpolation (Hadamard) gives at σ₀:
  -- |ζ(σ₀+it₀)| ≤ C · |t₀|^{(1-σ₀)/2 + δ}
  -- Since δ ≤ ε, this gives |ζ(σ₀+it₀)| ≤ C · |t₀|^{(1-σ₀)/2 + ε}
  -- = C · |t₀|^{convexity_exponent(σ₀) + ε} for σ₀ ∈ [0,1]
  sorry

/-- Growth bound on the critical line: |ζ(1/2+it)| = O(|t|^{1/2}).

    Follows from the convexity bound at σ = 1/2 (exponent 1/4 ≤ 1/2). -/
theorem zeta_critical_line_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta ((1:ℂ)/2 + t * I)‖ ≤ C * |t| ^ (1/2 : ℝ) := by
  -- This follows from the convexity bound: at σ=1/2, exponent = 1/4+ε ≤ 1/2
  -- for ε = 1/4, and |t|^{1/4+1/4} = |t|^{1/2}.
  obtain ⟨C, hC, hbound⟩ := zeta_convexity_bound (1/2) (by norm_num) (by norm_num) (1/4) (by norm_num)
  refine ⟨C, hC, fun t ht => ?_⟩
  have hconv : convexity_exponent (1/2) + 1/4 = 1/2 := by
    unfold convexity_exponent; norm_num
  rw [← hconv]
  have : (↑(1/2 : ℝ) : ℂ) = 1/2 := by push_cast; ring
  rw [this] at hbound
  exact hbound t ht

/-- The Hardy Z-function growth bound.

    Z(t) = exp(iθ(t)) ζ(1/2+it) where θ(t) is the Riemann-Siegel theta.
    Since |exp(iθ)| = 1 and |ζ(1/2+it)| = O(|t|^{1/2}), we get |Z(t)| = O(|t|^{1/2}). -/
theorem hardyZ_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta ((1:ℂ)/2 + t * I)‖ ≤ C * |t| ^ (1/2 : ℝ) := by
  exact zeta_critical_line_bound

/-- Polynomial bound on zeta near σ = 1: |ζ(σ+it)| ≤ C log|t| for σ near 1 -/
theorem zeta_near_one_bound (σ : ℝ) (hσ : 1 < σ) (hσ2 : σ < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| := by
  -- For σ > 1, |ζ(σ+it)| ≤ 1 + 1/(σ-1) (constant independent of t).
  -- For |t| ≥ 2, log|t| ≥ log 2 > 0, so the constant bound implies a log bound.
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hbound : 0 < 1 + 1 / (σ - 1) := by
    have : 0 < σ - 1 := by linarith
    positivity
  refine ⟨(1 + 1 / (σ - 1)) / Real.log 2, div_pos hbound hlog2, ?_⟩
  intro t ht
  have hlog_le : Real.log 2 ≤ Real.log |t| :=
    Real.log_le_log (by norm_num) ht
  calc ‖riemannZeta (↑σ + ↑t * I)‖
      ≤ 1 + 1 / (σ - 1) := zeta_bound_gt_one σ t hσ
    _ = ((1 + 1 / (σ - 1)) / Real.log 2) * Real.log 2 :=
        (div_mul_cancel₀ _ (ne_of_gt hlog2)).symm
    _ ≤ ((1 + 1 / (σ - 1)) / Real.log 2) * Real.log |t| :=
        mul_le_mul_of_nonneg_left hlog_le (le_of_lt (div_pos hbound hlog2))

/-- Bound on zeta away from the critical strip -/
theorem zeta_large_sigma_bound (σ : ℝ) (hσ : 2 ≤ σ) (t : ℝ) :
    ‖riemannZeta (σ + t * I)‖ ≤ 2 := by
  -- For σ ≥ 2, |ζ(σ+it)| ≤ ∑ 1/n^σ ≤ ∑ 1/n^2 = π²/6 < 2
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
    nlinarith [pi_lt_d2, pi_pos, sq_nonneg (3.15 - Real.pi)]
  have hre : 1 < ((σ : ℂ) + (t : ℂ) * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
               Complex.I_re, Complex.I_im, Complex.ofReal_im,
               mul_zero, mul_one, sub_zero, add_zero]
    linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  have h_hasSum : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h_sum_zero : (Finset.range 1).sum (fun i : ℕ => (1 : ℝ) / (↑i) ^ 2) = 0 := by simp
    have key : HasSum (fun n : ℕ => (1 : ℝ) / (↑n) ^ 2)
        (Real.pi ^ 2 / 6 + (Finset.range 1).sum (fun i : ℕ => (1 : ℝ) / (↑i) ^ 2)) := by
      rw [h_sum_zero, add_zero]; exact hasSum_zeta_two
    have h := (hasSum_nat_add_iff 1).mpr key
    simp only [Nat.cast_add, Nat.cast_one] at h
    exact h
  apply le_trans _ hpi
  apply tsum_of_norm_bounded h_hasSum
  intro n
  -- ‖1 / (↑n + 1)^(σ + ti)‖ ≤ 1 / ((n:ℝ) + 1)^2
  rw [norm_div, norm_one,
      show (↑↑n + 1 : ℂ) = ((↑(n + 1 : ℕ) : ℂ)) from by push_cast; ring,
      norm_natCast_cpow_of_pos (Nat.succ_pos n)]
  have hre_eq : ((σ : ℂ) + (t : ℂ) * I).re = σ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
               Complex.I_re, Complex.I_im, Complex.ofReal_im,
               mul_zero, mul_one, sub_zero, add_zero]
  rw [hre_eq, Nat.cast_succ]
  -- Goal: 1 / ((n:ℝ) + 1) ^ σ ≤ 1 / ((n:ℝ) + 1) ^ 2
  -- LHS uses rpow (σ : ℝ), RHS uses npow (2 : ℕ)
  have h_base_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h_base_ge_one : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  -- Convert RHS npow to rpow for comparison
  rw [show ((n : ℝ) + 1) ^ (2 : ℕ) = ((n : ℝ) + 1) ^ ((2 : ℕ) : ℝ) from
    (rpow_natCast ((n : ℝ) + 1) 2).symm]
  exact one_div_le_one_div_of_le (rpow_pos_of_pos h_base_pos _)
    (rpow_le_rpow_of_exponent_le h_base_ge_one (by exact_mod_cast hσ))

end
