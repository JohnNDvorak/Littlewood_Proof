/-
Phragmén-Lindelöf convexity bounds for zeta - proved by Aristotle.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib
import Littlewood.Aristotle.Bridge.GammaGrowthComplete
import Littlewood.Aristotle.PhragmenLindelofV2

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

noncomputable section

open Complex Real Topology Filter HurwitzZeta
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

/-- The completed Riemann zeta function with poles removed (Λ₀) is bounded on vertical strips.

    Λ₀(s) = completedRiemannZeta₀(s) is an entire function defined as a Mellin transform
    of a modified theta kernel (see Mathlib: AbstractFuncEq.WeakFEPair.Λ₀).

    The bound follows from the Mellin integral representation:
      Λ₀(s) = ∫₀^∞ f_modif(t) · t^{s/2-1} dt / 2
    Taking norms: ‖Λ₀(s)‖ ≤ (∫₀^∞ ‖f_modif(t)‖ · t^{Re(s)/2-1} dt) / 2
    The RHS depends only on Re(s). Since f_modif has exponential decay at ∞
    and is O(1) at 0 (by construction), the integral converges for all Re(s)
    and is continuous in Re(s). Hence bounded on compact σ-intervals.

    Proof strategy (for Aristotle):
    1. Unfold: completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s/2) / 2
    2. Unfold: WeakFEPair.Λ₀ = mellin WeakFEPair.f_modif
    3. Apply norm_integral_le_integral_norm
    4. Use norm_cpow_eq_rpow_re_of_pos for |t^{s-1}| = t^{σ-1} (t > 0)
    5. Show resulting real integral is finite and continuous in σ
       (uses isBigO_atTop_evenKernel_sub for decay) -/
private lemma completedRiemannZeta₀_bounded_on_strip (a b : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖completedRiemannZeta₀ s‖ ≤ M := by
  -- Handle empty strip (a > b)
  by_cases hab : a ≤ b; swap
  · exact ⟨1, one_pos, fun s ha hb => absurd (ha.trans hb) (not_le.mpr (by linarith))⟩
  -- The strong FE pair for the Hurwitz even kernel at a = 0
  set Q := (hurwitzEvenFEPair (0 : UnitAddCircle)).toStrongFEPair
  -- Mellin convergence at a/2 and b/2 (from hasMellin, which works for all s)
  have hconv_a := (Q.hasMellin ((a / 2 : ℝ) : ℂ)).1
  have hconv_b := (Q.hasMellin ((b / 2 : ℝ) : ℂ)).1
  -- Norm-integrability of the Mellin integrands at a/2 and b/2
  have hint_a := hconv_a.norm
  have hint_b := hconv_b.norm
  -- Define the bound as sum of endpoint integrals
  set Ia := ∫ t in Set.Ioi (0 : ℝ), ‖(↑t : ℂ) ^ ((↑(a / 2) : ℂ) - 1) • Q.f t‖
  set Ib := ∫ t in Set.Ioi (0 : ℝ), ‖(↑t : ℂ) ^ ((↑(b / 2) : ℂ) - 1) • Q.f t‖
  have hIa_nn : 0 ≤ Ia :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t _ => norm_nonneg _
  have hIb_nn : 0 ≤ Ib :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t _ => norm_nonneg _
  refine ⟨(Ia + Ib) / 2 + 1, by linarith, fun s ha hb => ?_⟩
  -- Key unfolding: completedRiemannZeta₀ s = mellin Q.f (s/2) / 2 (definitionally)
  -- We prove ‖mellin Q.f (s/2)‖ ≤ Ia + Ib, then divide by 2
  suffices h_main : ‖mellin Q.f (s / 2)‖ ≤ Ia + Ib by
    have h_eq : completedRiemannZeta₀ s = mellin Q.f (s / 2) / 2 := rfl
    rw [h_eq, norm_div, Complex.norm_ofNat]
    linarith
  -- Mellin converges at s/2
  have hconv_s := (Q.hasMellin (s / 2)).1
  -- Chain: ‖mellin‖ ≤ ∫ ‖integrand‖ ≤ ∫ (‖a-integrand‖ + ‖b-integrand‖) = Ia + Ib
  calc ‖mellin Q.f (s / 2)‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖(↑t : ℂ) ^ (s / 2 - 1) • Q.f t‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), (‖(↑t : ℂ) ^ ((↑(a / 2) : ℂ) - 1) • Q.f t‖ +
          ‖(↑t : ℂ) ^ ((↑(b / 2) : ℂ) - 1) • Q.f t‖) := by
        apply MeasureTheory.setIntegral_mono_on hconv_s.norm (hint_a.add hint_b)
          measurableSet_Ioi
        intro t ht
        rw [Set.mem_Ioi] at ht
        -- Reduce to comparing cpow norms (factor out ‖Q.f t‖)
        have hcpow : ‖(↑t : ℂ) ^ (s / 2 - 1)‖ ≤
            ‖(↑t : ℂ) ^ ((↑(a / 2) : ℂ) - 1)‖ + ‖(↑t : ℂ) ^ ((↑(b / 2) : ℂ) - 1)‖ := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
              Complex.norm_cpow_eq_rpow_re_of_pos ht,
              Complex.norm_cpow_eq_rpow_re_of_pos ht]
          have hre_s : (s / 2 - 1).re = s.re / 2 - 1 := by
            simp [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re]
          have hre_a : ((↑(a / 2) : ℂ) - 1).re = a / 2 - 1 := by
            simp [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
          have hre_b : ((↑(b / 2) : ℂ) - 1).re = b / 2 - 1 := by
            simp [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
          rw [hre_s, hre_a, hre_b]
          have hle_a : a / 2 - 1 ≤ s.re / 2 - 1 := by linarith
          have hle_b : s.re / 2 - 1 ≤ b / 2 - 1 := by linarith
          by_cases h1 : 1 ≤ t
          · calc t ^ (s.re / 2 - 1) ≤ t ^ (b / 2 - 1) :=
                  rpow_le_rpow_of_exponent_le h1 hle_b
              _ ≤ t ^ (a / 2 - 1) + t ^ (b / 2 - 1) :=
                  le_add_of_nonneg_left (rpow_nonneg (by linarith : (0:ℝ) ≤ t) _)
          · have h1' : t < 1 := by linarith [not_le.mp h1]
            calc t ^ (s.re / 2 - 1) ≤ t ^ (a / 2 - 1) :=
                  rpow_le_rpow_of_exponent_ge (by linarith : 0 < t) h1'.le hle_a
              _ ≤ t ^ (a / 2 - 1) + t ^ (b / 2 - 1) :=
                  le_add_of_nonneg_right (rpow_nonneg (by linarith : (0:ℝ) ≤ t) _)
        calc ‖(↑t : ℂ) ^ (s / 2 - 1) • Q.f t‖
            = ‖(↑t : ℂ) ^ (s / 2 - 1)‖ * ‖Q.f t‖ := norm_smul _ _
          _ ≤ (‖(↑t : ℂ) ^ ((↑(a / 2) : ℂ) - 1)‖ + ‖(↑t : ℂ) ^ ((↑(b / 2) : ℂ) - 1)‖) *
              ‖Q.f t‖ := mul_le_mul_of_nonneg_right hcpow (norm_nonneg _)
          _ = ‖(↑t : ℂ) ^ ((↑(a / 2) : ℂ) - 1)‖ * ‖Q.f t‖ +
              ‖(↑t : ℂ) ^ ((↑(b / 2) : ℂ) - 1)‖ * ‖Q.f t‖ := add_mul _ _ _
          _ = ‖(↑t : ℂ) ^ ((↑(a / 2) : ℂ) - 1) • Q.f t‖ +
              ‖(↑t : ℂ) ^ ((↑(b / 2) : ℂ) - 1) • Q.f t‖ := by
              rw [norm_smul, norm_smul]
    _ = Ia + Ib := MeasureTheory.integral_add hint_a hint_b

/-- Upper bound on ‖(Gammaℝ s)⁻¹‖ for s in a vertical strip.
    For Re(s) ∈ [δ, 2] and |Im(s)| ≥ 2:
      ‖(Gammaℝ s)⁻¹‖ ≤ C · exp(π|Im s|/2).
    Uses the reflection Γ(z)·Γ(1-z) = π/sin(πz) to write
      |1/Γ(z)| = |sin(πz)|·|Γ(1-z)|/π ≤ exp(π|t|/2)·1/π.
    The bound |Γ(1-z)| ≤ 1 follows from the recurrence Γ(1-z) = Γ(2-z)/(1-z),
    norm_Gamma_le_Gamma_re, and convexity of Γ on [1,2] (Γ(1)=Γ(2)=1). -/
private lemma inv_gammaR_bound (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖(Gammaℝ s)⁻¹‖ ≤ C * rexp (Real.pi * |s.im| / 2) := by
  refine ⟨1, one_pos, fun s hδs hs2 him => ?_⟩
  have hre_pos : 0 < s.re := by linarith
  have hΓR_pos : 0 < ‖Gammaℝ s‖ := norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos hre_pos)
  -- Set z = s/2
  set z := s / 2 with hz_def
  have hz_re : z.re = s.re / 2 := by simp [hz_def, Complex.div_ofNat_re]
  have hz_im : z.im = s.im / 2 := by simp [hz_def, Complex.div_ofNat_im]
  have hz_re_pos : 0 < z.re := by rw [hz_re]; linarith
  have hz_re_le : z.re ≤ 1 := by rw [hz_re]; linarith
  have hz_im_abs : |z.im| = |s.im| / 2 := by rw [hz_im, abs_div]; norm_num
  have hzim_ge1 : 1 ≤ |z.im| := by rw [hz_im_abs]; linarith
  -- Gamma(z) ≠ 0
  have hΓz_ne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz_re_pos
  have hΓz_pos : 0 < ‖Complex.Gamma z‖ := norm_pos_iff.mpr hΓz_ne
  -- 1-z ≠ 0 (since |Im(1-z)| = |z.im| ≥ 1 > 0)
  have h1z_ne : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hzim0 : z.im = 0 := by
      have := congr_arg Complex.im h; simp at this; linarith
    simp [hzim0] at hzim_ge1; linarith
  -- Gamma(1-z) ≠ 0 (since 1-z is not a non-positive integer: Im(1-z) ≠ 0)
  have hΓ1z_ne : Complex.Gamma (1 - z) ≠ 0 := by
    rw [Ne, Complex.Gamma_eq_zero_iff]; push_neg; intro n; intro hn
    have hzim0 : z.im = 0 := by
      have := congr_arg Complex.im hn; simp at this; linarith
    simp [hzim0] at hzim_ge1; linarith
  -- sin(πz) ≠ 0
  have hsin_ne : Complex.sin (↑π * z) ≠ 0 := by
    intro h; have := Complex.Gamma_mul_Gamma_one_sub z; rw [h, div_zero] at this
    exact mul_ne_zero hΓz_ne hΓ1z_ne this
  have hsin_pos : 0 < ‖Complex.sin (↑π * z)‖ := norm_pos_iff.mpr hsin_ne
  -- === Step 1: ‖sin(πz)‖ ≤ exp(π|s.im|/2) ===
  -- sin(w) = (exp(-wI) - exp(wI)) * I / 2, triangle inequality on exponentials
  have h_sin_bound : ‖Complex.sin (↑π * z)‖ ≤ rexp (π * |s.im| / 2) := by
    set w := (↑π : ℂ) * z with hw_def
    rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one,
        show ‖(2 : ℂ)‖ = (2 : ℝ) from by norm_num]
    have hre_neg : ((-w) * I).re = π * z.im := by
      simp [hw_def, Complex.mul_re, Complex.neg_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have hre_pos' : (w * I).re = -(π * z.im) := by
      simp [hw_def, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
    have hexp1 : ‖exp ((-w) * I)‖ ≤ rexp (π * |s.im| / 2) := by
      rw [Complex.norm_exp, hre_neg, hz_im]
      exact Real.exp_le_exp.mpr (by nlinarith [le_abs_self s.im, pi_pos])
    have hexp2 : ‖exp (w * I)‖ ≤ rexp (π * |s.im| / 2) := by
      rw [Complex.norm_exp, hre_pos', hz_im]
      exact Real.exp_le_exp.mpr (by nlinarith [neg_abs_le s.im, pi_pos])
    calc ‖exp ((-w) * I) - exp (w * I)‖ / 2
        ≤ (‖exp ((-w) * I)‖ + ‖exp (w * I)‖) / 2 := by
          gcongr; exact norm_sub_le _ _
      _ ≤ (rexp (π * |s.im| / 2) + rexp (π * |s.im| / 2)) / 2 := by gcongr
      _ = rexp (π * |s.im| / 2) := by ring
  -- === Step 2: ‖Γ(1-z)‖ ≤ 1 ===
  -- Uses recurrence Γ(2-z) = (1-z)·Γ(1-z), norm_Gamma_le_Gamma_re, and
  -- convexity of Γ on [1,2] (where Γ(1)=Γ(2)=1)
  have h_rec : Complex.Gamma (2 - z) = (1 - z) * Complex.Gamma (1 - z) := by
    have h := Complex.Gamma_add_one (1 - z) h1z_ne
    rwa [show (1 - z) + 1 = 2 - z from by ring] at h
  have h_norm_1z : ‖Complex.Gamma (1 - z)‖ =
      ‖Complex.Gamma (2 - z)‖ / ‖(1 : ℂ) - z‖ := by
    rw [eq_div_iff (norm_ne_zero_iff.mpr h1z_ne), mul_comm, ← norm_mul, ← h_rec]
  have h2z_re_pos : 0 < (2 - z).re := by
    simp [Complex.sub_re, hz_re]; linarith
  have h_norm_2z : ‖Complex.Gamma (2 - z)‖ ≤ Real.Gamma (2 - z.re) := by
    have h := Aristotle.Bridge.GammaGrowthComplete.norm_Gamma_le_Gamma_re h2z_re_pos
    rwa [show (2 - z).re = 2 - z.re from by simp [Complex.sub_re]] at h
  have h_gamma_le_one : Real.Gamma (2 - z.re) ≤ 1 := by
    -- Write 2 - z.re = z.re • 1 + (1 - z.re) • 2 (convex combination, no circular rewrite)
    have h_eq : (2 - z.re : ℝ) = z.re • (1 : ℝ) + (1 - z.re) • (2 : ℝ) := by
      simp [smul_eq_mul]; ring
    rw [h_eq]
    calc Real.Gamma (z.re • 1 + (1 - z.re) • 2)
        ≤ z.re • Real.Gamma 1 + (1 - z.re) • Real.Gamma 2 :=
          convexOn_Gamma.2 (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr two_pos)
            (le_of_lt hz_re_pos) (by linarith [hz_re_le]) (by simp [smul_eq_mul])
      _ = z.re * 1 + (1 - z.re) * 1 := by
          simp [smul_eq_mul, Real.Gamma_one, Real.Gamma_two]
      _ = 1 := by ring
  have h_1z_norm : 1 ≤ ‖(1 : ℂ) - z‖ := by
    calc (1 : ℝ) ≤ |z.im| := hzim_ge1
      _ = |(1 - z).im| := by simp [Complex.sub_im, Complex.one_im, abs_neg]
      _ ≤ ‖(1 : ℂ) - z‖ := Complex.abs_im_le_norm _
  have h_gamma_1z_bound : ‖Complex.Gamma (1 - z)‖ ≤ 1 := by
    rw [h_norm_1z, div_le_one (by linarith : (0 : ℝ) < ‖(1 : ℂ) - z‖)]
    linarith [h_norm_2z, h_gamma_le_one]
  -- === Step 3: Lower bound on ‖Γ(z)‖ via reflection formula ===
  -- Γ(z)·Γ(1-z) = π/sin(πz) gives ‖Γ(z)‖ = π/(‖sin(πz)‖·‖Γ(1-z)‖)
  have h_norm_prod : ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ =
      π / ‖Complex.sin (↑π * z)‖ := by
    rw [← norm_mul, Complex.Gamma_mul_Gamma_one_sub, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos pi_pos]
  have h_prod_pos : 0 < ‖Complex.sin (↑π * z)‖ * ‖Complex.Gamma (1 - z)‖ :=
    mul_pos hsin_pos (norm_pos_iff.mpr hΓ1z_ne)
  have h_key : ‖Complex.Gamma z‖ * (‖Complex.sin (↑π * z)‖ * ‖Complex.Gamma (1 - z)‖) = π := by
    rw [mul_comm (‖Complex.sin (↑π * z)‖) (‖Complex.Gamma (1 - z)‖),
        ← mul_assoc, h_norm_prod, div_mul_cancel₀ _ (ne_of_gt hsin_pos)]
  have h_gamma_lower : π * rexp (-(π * |s.im| / 2)) ≤ ‖Complex.Gamma z‖ := by
    have h_eq1 : π * rexp (-(π * |s.im| / 2)) = π / rexp (π * |s.im| / 2) := by
      rw [div_eq_mul_inv]; congr 1; exact Real.exp_neg _
    have h_eq2 : ‖Complex.Gamma z‖ =
        π / (‖Complex.sin (↑π * z)‖ * ‖Complex.Gamma (1 - z)‖) :=
      (eq_div_iff (ne_of_gt h_prod_pos)).mpr h_key
    rw [h_eq1, h_eq2]
    exact div_le_div_of_nonneg_left pi_pos.le h_prod_pos
      (calc ‖Complex.sin (↑π * z)‖ * ‖Complex.Gamma (1 - z)‖
          ≤ rexp (π * |s.im| / 2) * 1 :=
            mul_le_mul h_sin_bound h_gamma_1z_bound (norm_nonneg _)
              (le_of_lt (Real.exp_pos _))
        _ = rexp (π * |s.im| / 2) := mul_one _)
  -- === Step 4: ‖π^{-s/2}‖ ≥ π⁻¹ ===
  have h_pi_cpow : π⁻¹ ≤ ‖(↑π : ℂ) ^ (-s / 2)‖ := by
    rw [show (↑π : ℂ) = ↑(π : ℝ) from rfl, norm_cpow_eq_rpow_re_of_pos pi_pos]
    have hre : (-s / 2).re = -(s.re / 2) := by
      simp [Complex.neg_re, Complex.div_ofNat_re, neg_div]
    rw [hre, show π⁻¹ = π ^ ((-1 : ℝ)) from (rpow_neg_one π).symm]
    exact rpow_le_rpow_of_exponent_le (by linarith [pi_gt_three]) (by linarith)
  -- === Step 5: Combine lower bound ‖Gammaℝ s‖ ≥ exp(-π|s.im|/2) ===
  have h_lower : rexp (-(π * |s.im| / 2)) ≤ ‖Gammaℝ s‖ := by
    have h_GR : Gammaℝ s = (↑π : ℂ) ^ (-s / 2) * Complex.Gamma z := by
      rw [Gammaℝ_def, hz_def]
    rw [h_GR, norm_mul]
    calc rexp (-(π * |s.im| / 2))
        = π⁻¹ * (π * rexp (-(π * |s.im| / 2))) := by
          rw [inv_mul_cancel_left₀ (ne_of_gt pi_pos)]
      _ ≤ ‖(↑π : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma z‖ :=
          mul_le_mul h_pi_cpow h_gamma_lower (by positivity) (by positivity)
  -- === Step 6: Convert to the goal ===
  rw [one_mul, norm_inv]
  calc ‖Gammaℝ s‖⁻¹
      ≤ (rexp (-(π * |s.im| / 2)))⁻¹ := inv_anti₀ (Real.exp_pos _) h_lower
    _ = rexp (π * |s.im| / 2) := by rw [Real.exp_neg, inv_inv]

/-- Extended inverse Gammaℝ bound for the wider strip Re ∈ [-1/2, 3/2].
    Uses Gammaℝ_eq_zero_iff and convexity of Γ on [1,3] (with Γ(3)=2). -/
private lemma inv_gammaR_bound_ext (s : ℂ) (hre_lo : -(1/2 : ℝ) ≤ s.re)
    (hre_hi : s.re ≤ 3/2) (him : 2 ≤ |s.im|) :
    ‖(Gammaℝ s)⁻¹‖ ≤ 2 * rexp (Real.pi * |s.im| / 2) := by
  -- Gammaℝ s ≠ 0 (s is not a non-positive even integer since Im s ≠ 0)
  have him_ne : s.im ≠ 0 := by intro h; simp only [h, abs_zero] at him; linarith
  have hΓR_ne : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]; push_neg; intro n hn
    exact him_ne (by have := congr_arg Complex.im hn; simp at this; linarith)
  have hΓR_pos : 0 < ‖Gammaℝ s‖ := norm_pos_iff.mpr hΓR_ne
  -- z = s/2
  set z := s / 2 with hz_def
  have hz_re : z.re = s.re / 2 := by simp [hz_def, Complex.div_ofNat_re]
  have hz_im : z.im = s.im / 2 := by simp [hz_def, Complex.div_ofNat_im]
  have hz_im_abs : |z.im| = |s.im| / 2 := by rw [hz_im, abs_div]; norm_num
  have hzim_ge1 : 1 ≤ |z.im| := by rw [hz_im_abs]; linarith
  have hzim_ne : z.im ≠ 0 := by rw [hz_im]; exact div_ne_zero him_ne two_ne_zero
  -- Gamma(z), Gamma(1-z) nonzero (Im ≠ 0 so not non-positive integers)
  have hΓz_ne : Complex.Gamma z ≠ 0 := by
    rw [Ne, Complex.Gamma_eq_zero_iff]; push_neg; intro n hn
    exact hzim_ne (by have := congr_arg Complex.im hn; simp at this; linarith)
  have hΓz_pos : 0 < ‖Complex.Gamma z‖ := norm_pos_iff.mpr hΓz_ne
  have h1z_ne : (1 : ℂ) - z ≠ 0 := by
    intro h; exact hzim_ne (by have := congr_arg Complex.im h; simp at this; linarith)
  have hΓ1z_ne : Complex.Gamma (1 - z) ≠ 0 := by
    rw [Ne, Complex.Gamma_eq_zero_iff]; push_neg; intro n hn
    exact hzim_ne (by have := congr_arg Complex.im hn; simp at this; linarith)
  have hsin_ne : Complex.sin (↑π * z) ≠ 0 := by
    intro h; have := Complex.Gamma_mul_Gamma_one_sub z; rw [h, div_zero] at this
    exact mul_ne_zero hΓz_ne hΓ1z_ne this
  have hsin_pos : 0 < ‖Complex.sin (↑π * z)‖ := norm_pos_iff.mpr hsin_ne
  -- Step 1: ‖sin(πz)‖ ≤ exp(π|s.im|/2)  [identical to inv_gammaR_bound]
  have h_sin_bound : ‖Complex.sin (↑π * z)‖ ≤ rexp (π * |s.im| / 2) := by
    set w := (↑π : ℂ) * z with hw_def
    rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one,
        show ‖(2 : ℂ)‖ = (2 : ℝ) from by norm_num]
    have hre_neg : ((-w) * I).re = π * z.im := by
      simp [hw_def, Complex.mul_re, Complex.neg_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have hre_pos' : (w * I).re = -(π * z.im) := by
      simp [hw_def, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
    have hexp1 : ‖exp ((-w) * I)‖ ≤ rexp (π * |s.im| / 2) := by
      rw [Complex.norm_exp, hre_neg, hz_im]
      exact Real.exp_le_exp.mpr (by nlinarith [le_abs_self s.im, pi_pos])
    have hexp2 : ‖exp (w * I)‖ ≤ rexp (π * |s.im| / 2) := by
      rw [Complex.norm_exp, hre_pos', hz_im]
      exact Real.exp_le_exp.mpr (by nlinarith [neg_abs_le s.im, pi_pos])
    calc ‖exp ((-w) * I) - exp (w * I)‖ / 2
        ≤ (‖exp ((-w) * I)‖ + ‖exp (w * I)‖) / 2 := by
          gcongr; exact norm_sub_le _ _
      _ ≤ (rexp (π * |s.im| / 2) + rexp (π * |s.im| / 2)) / 2 := by gcongr
      _ = rexp (π * |s.im| / 2) := by ring
  -- Step 2: ‖Γ(1-z)‖ ≤ 2  [extended: convexity on [1,3] with Γ(3)=2]
  have h_gamma_1z_bound : ‖Complex.Gamma (1 - z)‖ ≤ 2 := by
    have h_rec : Complex.Gamma (2 - z) = (1 - z) * Complex.Gamma (1 - z) := by
      have h := Complex.Gamma_add_one (1 - z) h1z_ne
      rwa [show (1 - z) + 1 = 2 - z from by ring] at h
    have h_norm_1z : ‖Complex.Gamma (1 - z)‖ =
        ‖Complex.Gamma (2 - z)‖ / ‖(1 : ℂ) - z‖ := by
      rw [eq_div_iff (norm_ne_zero_iff.mpr h1z_ne), mul_comm, ← norm_mul, ← h_rec]
    have h2z_re_pos : 0 < (2 - z).re := by
      simp [Complex.sub_re, hz_re]; linarith
    have h_norm_2z : ‖Complex.Gamma (2 - z)‖ ≤ Real.Gamma (2 - z.re) := by
      have h := Aristotle.Bridge.GammaGrowthComplete.norm_Gamma_le_Gamma_re h2z_re_pos
      rwa [show (2 - z).re = 2 - z.re from by simp [Complex.sub_re]] at h
    -- Γ(2-z.re) ≤ 2 by convexity on [1,3]
    -- Write 2-z.re = α·1 + (1-α)·3 where α = (1+z.re)/2
    have hα_nn : 0 ≤ (1 + z.re) / 2 := by rw [hz_re]; linarith
    have h1α_nn : 0 ≤ (1 - z.re) / 2 := by rw [hz_re]; linarith
    have hα_sum : (1 + z.re) / 2 + (1 - z.re) / 2 = 1 := by ring
    have h_eq : (2 - z.re : ℝ) = ((1 + z.re) / 2) • (1 : ℝ) + ((1 - z.re) / 2) • (3 : ℝ) := by
      simp [smul_eq_mul]; ring
    have h_Gamma3 : Real.Gamma 3 = 2 := by
      rw [show (3:ℝ) = 2 + 1 from by norm_num,
          Real.Gamma_add_one (by norm_num : (2:ℝ) ≠ 0), Real.Gamma_two]; ring
    have h_gamma_le : Real.Gamma (2 - z.re) ≤ 2 := by
      rw [h_eq]
      calc Real.Gamma (((1 + z.re) / 2) • 1 + ((1 - z.re) / 2) • 3)
          ≤ ((1 + z.re) / 2) • Real.Gamma 1 + ((1 - z.re) / 2) • Real.Gamma 3 :=
            convexOn_Gamma.2 (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr three_pos)
              hα_nn h1α_nn hα_sum
        _ = (3 - z.re) / 2 := by
            simp [smul_eq_mul, Real.Gamma_one, h_Gamma3]; ring
        _ ≤ 2 := by rw [hz_re]; linarith
    have h_1z_norm : 1 ≤ ‖(1 : ℂ) - z‖ := by
      calc (1 : ℝ) ≤ |z.im| := hzim_ge1
        _ = |(1 - z).im| := by simp [Complex.sub_im, Complex.one_im, abs_neg]
        _ ≤ ‖(1 : ℂ) - z‖ := Complex.abs_im_le_norm _
    rw [h_norm_1z, div_le_iff₀ (by linarith : (0 : ℝ) < ‖(1 : ℂ) - z‖)]
    linarith [h_norm_2z, h_gamma_le]
  -- Step 3: Reflection formula lower bound for ‖Γ(z)‖
  have h_norm_prod : ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ =
      π / ‖Complex.sin (↑π * z)‖ := by
    rw [← norm_mul, Complex.Gamma_mul_Gamma_one_sub, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos pi_pos]
  have h_prod_pos : 0 < ‖Complex.sin (↑π * z)‖ * ‖Complex.Gamma (1 - z)‖ :=
    mul_pos hsin_pos (norm_pos_iff.mpr hΓ1z_ne)
  have h_key : ‖Complex.Gamma z‖ * (‖Complex.sin (↑π * z)‖ * ‖Complex.Gamma (1 - z)‖) = π := by
    rw [mul_comm (‖Complex.sin (↑π * z)‖) (‖Complex.Gamma (1 - z)‖),
        ← mul_assoc, h_norm_prod, div_mul_cancel₀ _ (ne_of_gt hsin_pos)]
  have h_gamma_lower : π / (2 * rexp (π * |s.im| / 2)) ≤ ‖Complex.Gamma z‖ := by
    have h_eq2 : ‖Complex.Gamma z‖ =
        π / (‖Complex.sin (↑π * z)‖ * ‖Complex.Gamma (1 - z)‖) :=
      (eq_div_iff (ne_of_gt h_prod_pos)).mpr h_key
    rw [h_eq2]
    exact div_le_div_of_nonneg_left pi_pos.le (by positivity)
      (calc ‖Complex.sin (↑π * z)‖ * ‖Complex.Gamma (1 - z)‖
          ≤ rexp (π * |s.im| / 2) * 2 :=
            mul_le_mul h_sin_bound h_gamma_1z_bound (norm_nonneg _)
              (le_of_lt (Real.exp_pos _))
        _ = 2 * rexp (π * |s.im| / 2) := by ring)
  -- Step 4: ‖π^{-s/2}‖ ≥ π⁻¹ (same: s.re ≤ 3/2 ≤ 2 so -s.re/2 ≥ -1)
  have h_pi_cpow : π⁻¹ ≤ ‖(↑π : ℂ) ^ (-s / 2)‖ := by
    rw [show (↑π : ℂ) = ↑(π : ℝ) from rfl, norm_cpow_eq_rpow_re_of_pos pi_pos]
    have hre : (-s / 2).re = -(s.re / 2) := by
      simp [Complex.neg_re, Complex.div_ofNat_re, neg_div]
    rw [hre, show π⁻¹ = π ^ ((-1 : ℝ)) from (rpow_neg_one π).symm]
    exact rpow_le_rpow_of_exponent_le (by linarith [pi_gt_three]) (by linarith)
  -- Step 5: ‖Gammaℝ s‖ ≥ 1/(2·exp(π|s.im|/2))
  have h_lower : (2 * rexp (π * |s.im| / 2))⁻¹ ≤ ‖Gammaℝ s‖ := by
    have h_GR : Gammaℝ s = (↑π : ℂ) ^ (-s / 2) * Complex.Gamma z := by
      rw [Gammaℝ_def, hz_def]
    rw [h_GR, norm_mul]
    -- Factor: 1/(2·exp(X)) = π⁻¹ · π/(2·exp(X))
    calc (2 * rexp (π * |s.im| / 2))⁻¹
        = π⁻¹ * (π / (2 * rexp (π * |s.im| / 2))) := by
          have hπ := ne_of_gt pi_pos
          have hexp := ne_of_gt (Real.exp_pos (π * |s.im| / 2))
          field_simp
      _ ≤ ‖(↑π : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma z‖ :=
          mul_le_mul h_pi_cpow h_gamma_lower (by positivity) (by positivity)
  -- Step 6: Invert
  rw [norm_inv]
  calc ‖Gammaℝ s‖⁻¹
      ≤ ((2 * rexp (π * |s.im| / 2))⁻¹)⁻¹ := inv_anti₀ (by positivity) h_lower
    _ = 2 * rexp (π * |s.im| / 2) := by rw [inv_inv]

/-- Polynomial absorption: x^{3/2}·exp(πx/4) ≤ K·exp(x) for x ≥ 2.
    The key is π/4 < 1, so exp((1-π/4)x) grows faster than x^{3/2}. -/
private lemma poly_exp_absorption :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x →
      x ^ ((3:ℝ)/2) * rexp (Real.pi * x / 4) ≤ K * rexp x := by
  -- c = 1 - π/4 > 0 since π < 4
  have h_pi_lt : Real.pi < 4 := pi_lt_four
  set c := 1 - Real.pi / 4 with hc_def
  have hc_pos : 0 < c := by linarith
  -- From pow_div_factorial_le_exp at n=2: (cx)²/2 ≤ exp(cx) for cx ≥ 0
  -- So exp(cx) ≥ c²x²/2, hence x² ≤ (2/c²)·exp(cx).
  -- For x ≥ 1: x^{3/2} ≤ x². Combined with exp(x) = exp(cx)·exp(πx/4):
  -- x^{3/2}·exp(πx/4) ≤ x²·exp(πx/4) ≤ (2/c²)·exp(cx)·exp(πx/4) = (2/c²)·exp(x).
  refine ⟨2 / c ^ 2, div_pos (by norm_num) (pow_pos hc_pos 2), fun x hx => ?_⟩
  have hx_pos : 0 < x := by linarith
  -- x^{3/2} ≤ x^2 for x ≥ 1
  have h_rpow_le : x ^ ((3:ℝ)/2) ≤ x ^ (2:ℝ) :=
    rpow_le_rpow_of_exponent_le (by linarith) (by norm_num : (3:ℝ)/2 ≤ 2)
  have h_rpow_eq : x ^ (2:ℝ) = x ^ 2 := rpow_natCast x 2
  -- exp(cx) ≥ c²x²/2
  have h_exp_lower : c ^ 2 * x ^ 2 / 2 ≤ rexp (c * x) := by
    have h_cx_nn : 0 ≤ c * x := by positivity
    have h1 := Real.quadratic_le_exp_of_nonneg h_cx_nn
    -- h1 : 1 + c*x + (c*x)^2/2 ≤ exp(c*x); drop first two terms
    calc c ^ 2 * x ^ 2 / 2 = (c * x) ^ 2 / 2 := by ring
      _ ≤ rexp (c * x) := by linarith
  -- exp(x) = exp(cx) · exp(πx/4)
  have h_exp_split : rexp x = rexp (c * x) * rexp (Real.pi * x / 4) := by
    rw [← Real.exp_add]; congr 1; rw [hc_def]; ring
  -- Main chain
  calc x ^ ((3:ℝ)/2) * rexp (Real.pi * x / 4)
      ≤ x ^ (2:ℝ) * rexp (Real.pi * x / 4) :=
        mul_le_mul_of_nonneg_right h_rpow_le (le_of_lt (Real.exp_pos _))
    _ = x ^ 2 * rexp (Real.pi * x / 4) := by rw [h_rpow_eq]
    _ ≤ 2 / c ^ 2 * rexp (c * x) * rexp (Real.pi * x / 4) := by
        have : x ^ 2 ≤ 2 / c ^ 2 * rexp (c * x) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc_pos 2)]
          linarith [h_exp_lower]
        exact mul_le_mul_of_nonneg_right this (le_of_lt (Real.exp_pos _))
    _ = 2 / c ^ 2 * rexp x := by rw [h_exp_split]; ring

/-- Exponential growth bound for (s-1)·ζ(s) in a vertical strip.

    Uses the factorization ζ(s) = (Λ₀(s) - 1/s - 1/(1-s)) / Γ_ℝ(s) where:
    - Λ₀(s) is bounded on the strip (completedRiemannZeta₀_bounded_on_strip)
    - ‖(Γ_ℝ(s))⁻¹‖ ≤ C·exp(π|t|/2) (from inv_gammaR_bound via reflection formula)
    Combined: |(s-1)·ζ(s)| ≤ C·|t|·exp(π|t|/2) ≤ A·exp(3|t|) for σ ∈ [δ, 2], |t| ≥ 2.

    The factor |t| is absorbed via |t| ≤ exp(|t|), and 1 + π/2 ≤ 3 (from π < 4). -/
private lemma sub_one_mul_zeta_growth (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖(s - 1) * riemannZeta s‖ ≤ A * rexp (3 * |s.im|) := by
  -- Get Λ₀ bound on strip [δ/2, 4]
  obtain ⟨M_Λ, hM_Λ, hΛ⟩ := completedRiemannZeta₀_bounded_on_strip (δ / 2) 4
  -- Get inverse Gamma_ℝ bound
  obtain ⟨C_Γ, hC_Γ, h_inv_Γ⟩ := inv_gammaR_bound δ hδ (by linarith)
  -- Choose A
  refine ⟨3 * (M_Λ + 1) * C_Γ, by positivity, fun s hδs hs2 him => ?_⟩
  -- Preliminary facts
  have hre_pos : 0 < s.re := by linarith
  have hs_ne : s ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith
  have hΓ_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre_pos
  have hΓ_pos : 0 < ‖Gammaℝ s‖ := norm_pos_iff.mpr hΓ_ne
  have him_pos : 0 < |s.im| := by linarith
  -- Step 1: Factorize ζ(s) = completedRiemannZeta(s) / Gammaℝ(s)
  have h_eq : (s - 1) * riemannZeta s =
      (s - 1) * completedRiemannZeta s / Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero hs_ne]; ring
  rw [h_eq, Complex.norm_div]
  -- Step 2: Bound the numerator ‖(s-1) * completedRiemannZeta s‖ ≤ 2(M_Λ+1)|s.im|
  have h_Λ₀ : ‖completedRiemannZeta₀ s‖ ≤ M_Λ :=
    hΛ s (by linarith) (by linarith)
  -- ‖1/s‖ ≤ 1/2 since ‖s‖ ≥ |s.im| ≥ 2
  have h_inv_s : ‖(1:ℂ) / s‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by linarith)
      (le_trans him (Complex.abs_im_le_norm s))
  -- ‖1/(1-s)‖ ≤ 1/2 since ‖1-s‖ ≥ |Im(1-s)| = |s.im| ≥ 2
  have h_im_1s : |(1 - s).im| = |s.im| := by simp [Complex.sub_im]
  have h_1s_norm : 2 ≤ ‖(1:ℂ) - s‖ :=
    le_trans him (h_im_1s ▸ Complex.abs_im_le_norm (1 - s))
  have h_inv_1s : ‖(1:ℂ) / (1 - s)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by linarith) h_1s_norm
  -- ‖completedRiemannZeta s‖ ≤ M_Λ + 1
  have h_cζ_bound : ‖completedRiemannZeta s‖ ≤ M_Λ + 1 := by
    rw [completedRiemannZeta_eq]
    calc ‖completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)‖
        ≤ ‖completedRiemannZeta₀ s - 1 / s‖ + ‖1 / (1 - s)‖ := norm_sub_le _ _
      _ ≤ (‖completedRiemannZeta₀ s‖ + ‖1 / s‖) + ‖1 / (1 - s)‖ := by
          linarith [norm_sub_le (completedRiemannZeta₀ s) (1 / s)]
      _ ≤ (M_Λ + 1/2) + 1/2 := by linarith
      _ = M_Λ + 1 := by ring
  -- ‖s‖ ≤ 2|s.im| (via triangle inequality on components)
  have h_norm_s : ‖s‖ ≤ 2 * |s.im| := by
    have h_tri : ‖s‖ ≤ ‖(↑s.re : ℂ)‖ + ‖↑s.im * I‖ := by
      have := norm_add_le (↑s.re : ℂ) (↑s.im * I)
      rwa [Complex.re_add_im] at this
    rw [Complex.norm_real, Complex.norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs] at h_tri
    linarith [abs_le.mpr ⟨by linarith, hs2⟩]
  -- ‖s - 1‖ ≤ 3|s.im|
  have h_s1_bound : ‖s - (1:ℂ)‖ ≤ 3 * |s.im| := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le s 1
      _ = ‖s‖ + 1 := by rw [norm_one]
      _ ≤ 2 * |s.im| + 1 := by linarith [h_norm_s]
      _ ≤ 3 * |s.im| := by linarith
  -- Numerator bound
  have h_num : ‖(s - 1) * completedRiemannZeta s‖ ≤ 3 * (M_Λ + 1) * |s.im| := by
    calc ‖(s - 1) * completedRiemannZeta s‖
        = ‖s - 1‖ * ‖completedRiemannZeta s‖ := norm_mul _ _
      _ ≤ (3 * |s.im|) * (M_Λ + 1) :=
          mul_le_mul h_s1_bound h_cζ_bound (norm_nonneg _) (by positivity)
      _ = 3 * (M_Λ + 1) * |s.im| := by ring
  -- Step 3: Apply inverse Gamma_ℝ bound (exp(π|t|/2) from reflection formula)
  have h_inv : ‖(Gammaℝ s)⁻¹‖ ≤ C_Γ * rexp (Real.pi * |s.im| / 2) :=
    h_inv_Γ s hδs hs2 him
  -- Step 4: Combine. Use |t| ≤ exp(|t|) and 1 + π/2 ≤ 3 (since π < 4).
  have h_id_le_exp : |s.im| ≤ rexp |s.im| := by linarith [Real.add_one_le_exp |s.im|]
  have h_exp_combine : rexp |s.im| * rexp (π * |s.im| / 2) ≤ rexp (3 * |s.im|) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [pi_lt_four])
  calc ‖(s - 1) * completedRiemannZeta s‖ / ‖Gammaℝ s‖
      = ‖(s - 1) * completedRiemannZeta s‖ * ‖(Gammaℝ s)⁻¹‖ := by
        rw [norm_inv, div_eq_mul_inv]
    _ ≤ (3 * (M_Λ + 1) * |s.im|) * (C_Γ * rexp (π * |s.im| / 2)) :=
        mul_le_mul h_num h_inv (by positivity) (by positivity)
    _ = 3 * (M_Λ + 1) * C_Γ * (|s.im| * rexp (π * |s.im| / 2)) := by ring
    _ ≤ 3 * (M_Λ + 1) * C_Γ * (rexp |s.im| * rexp (π * |s.im| / 2)) := by
        gcongr
    _ ≤ 3 * (M_Λ + 1) * C_Γ * rexp (3 * |s.im|) := by
        gcongr

/-- Gaussian localization: (1+|t|)^α · exp(-(t-t₀)²) ≤ exp(α²/4) · (1+|t₀|)^α.
    Uses triangle inequality and completing the square. -/
private lemma gaussian_poly_bound (α : ℝ) (hα : 0 ≤ α) (t₀ t : ℝ) :
    (1 + |t|) ^ α * rexp (-(t - t₀) ^ 2) ≤ rexp (α ^ 2 / 4) * (1 + |t₀|) ^ α := by
  -- Triangle: 1 + |t| ≤ (1+|t₀|)(1+|t-t₀|) since (1+a)(1+b) ≥ 1+a+b
  have h_tri : 1 + |t| ≤ (1 + |t₀|) * (1 + |t - t₀|) := by
    have : |t| ≤ |t₀| + |t - t₀| := by
      have h := abs_sub_abs_le_abs_sub t t₀
      linarith [abs_nonneg (t - t₀)]
    nlinarith [abs_nonneg t₀, abs_nonneg (t - t₀)]
  -- Raise to power α
  have h_pow : (1 + |t|) ^ α ≤ (1 + |t₀|) ^ α * (1 + |t - t₀|) ^ α := by
    calc (1 + |t|) ^ α
        ≤ ((1 + |t₀|) * (1 + |t - t₀|)) ^ α :=
          rpow_le_rpow (by positivity) h_tri hα
      _ = (1 + |t₀|) ^ α * (1 + |t - t₀|) ^ α :=
          mul_rpow (by positivity) (by positivity)
  -- Key: (1+|u|)^α · exp(-u²) ≤ exp(α²/4)
  set u := t - t₀ with hu_def
  have h_key : (1 + |u|) ^ α * rexp (-u ^ 2) ≤ rexp (α ^ 2 / 4) := by
    -- 1+|u| ≤ exp(|u|), so (1+|u|)^α ≤ exp(α|u|)
    have h_exp_bound : 1 + |u| ≤ rexp |u| := by
      linarith [Real.add_one_le_exp |u|]
    have h_rpow : (1 + |u|) ^ α ≤ rexp (α * |u|) := by
      calc (1 + |u|) ^ α
          ≤ (rexp |u|) ^ α := rpow_le_rpow (by positivity) h_exp_bound hα
        _ = rexp (α * |u|) := by
            rw [rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
    -- Completing the square: α|u| - u² ≤ α²/4
    have h_sq : α * |u| - u ^ 2 ≤ α ^ 2 / 4 := by
      have : 0 ≤ (|u| - α / 2) ^ 2 := sq_nonneg _
      nlinarith [sq_abs u]
    calc (1 + |u|) ^ α * rexp (-u ^ 2)
        ≤ rexp (α * |u|) * rexp (-u ^ 2) := by
          exact mul_le_mul_of_nonneg_right h_rpow (le_of_lt (Real.exp_pos _))
      _ = rexp (α * |u| - u ^ 2) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ rexp (α ^ 2 / 4) := Real.exp_le_exp.mpr h_sq
  -- Combine
  calc (1 + |t|) ^ α * rexp (-(t - t₀) ^ 2)
      ≤ (1 + |t₀|) ^ α * (1 + |u|) ^ α * rexp (-u ^ 2) := by
        calc (1 + |t|) ^ α * rexp (-(t - t₀) ^ 2)
            ≤ ((1 + |t₀|) ^ α * (1 + |u|) ^ α) * rexp (-u ^ 2) := by
              exact mul_le_mul_of_nonneg_right h_pow (le_of_lt (Real.exp_pos _))
          _ = (1 + |t₀|) ^ α * (1 + |u|) ^ α * rexp (-u ^ 2) := by ring
    _ = (1 + |t₀|) ^ α * ((1 + |u|) ^ α * rexp (-u ^ 2)) := by ring
    _ ≤ (1 + |t₀|) ^ α * rexp (α ^ 2 / 4) := by gcongr
    _ = rexp (α ^ 2 / 4) * (1 + |t₀|) ^ α := by ring

/-- Phragmén-Lindelöf interpolation for the zeta function in the critical strip.

    For 0 ≤ σ ≤ 1 and |t| ≥ 1: ‖ζ(σ+it)‖ ≤ C·|t|^{(1-σ)/2+δ}.

    Proof outline (3 steps):

    Step 1: For fixed t₀ with |t₀| ≥ 2, define
      F(s) = (s-1)·ζ(s)·exp((s-it₀)²)·|t₀|^{s/2}
    on the strip [-δ, 1+δ]. The exponential tilt |t₀|^{s/2} equalizes the
    boundary exponents (α = (1/2+δ)/(1+2δ) = 1/2).

    Step 2: Verify PL hypotheses.
    - DiffContOnCl: (s-1)ζ(s) is entire, exp and |t₀|^{s/2} are entire.
    - Boundary bounds: Gaussian localization + existing bounds give ‖F‖ ≤ K|t₀|^{3/2+δ/2}.
    - Growth condition: sub_one_mul_zeta_growth gives |(s-1)ζ| ≤ A·exp(3|t|).
      With Gaussian: |F| ≤ A·exp(3|t| + σ² - (t-t₀)²)·|t₀|^{σ/2}.
      For |t| → ∞: the Gaussian exp(-(t-t₀)²) kills exp(3|t|), so F → 0.
      Hence F is bounded, and the growth condition holds with c = 0 < π/(1+2δ).

    Step 3: Extract. PL gives |F(σ₀+it₀)| ≤ K|t₀|^{3/2+δ/2}.
    Then |ζ(σ₀+it₀)| ≤ K|t₀|^{3/2+δ/2} / (|t₀|·exp(σ₀²)·|t₀|^{σ₀/2})
                      = K|t₀|^{(1-σ₀)/2+δ/2} ≤ K|t₀|^{(1-σ₀)/2+δ}. -/
private lemma zeta_pl_interpolation (δ : ℝ) (hδ : 0 < δ) (hδ14 : δ ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ₀ : ℝ) (t₀ : ℝ),
      0 ≤ σ₀ → σ₀ ≤ 1 → 1 ≤ |t₀| →
        ‖riemannZeta (↑σ₀ + ↑t₀ * I)‖ ≤ C * |t₀| ^ ((1 - σ₀) / 2 + δ) := by
  -- Get boundary bounds
  obtain ⟨C_L, hC_L, h_left⟩ := zeta_bound_neg_sigma (2 * δ) (by linarith) (by linarith)
  have h_right : ∀ t : ℝ, ‖riemannZeta (↑(1 + 2 * δ) + ↑t * I)‖ ≤ 1 + 1 / (2 * δ) := by
    intro t
    have := zeta_bound_gt_one (1 + 2 * δ) t (by linarith)
    simp only [add_sub_cancel_left] at this
    exact this
  -- Get growth bound for (s-1)·ζ(s)
  obtain ⟨A, hA, h_growth⟩ := sub_one_mul_zeta_growth δ hδ (by linarith)
  -- === Strategy: PL with Gaussian damping + exponential tilt ===
  -- F(s) = zeta_entire_v2(s) · exp((s-it₀)² + λs) on strip [-2δ, 1+2δ]
  -- where λ = log|t₀|/2 (tilt with β = 1/2).
  -- Key identity: (1/2+2δ)/(1+4δ) = 1/2, so both boundaries have
  -- exponent 3/2+δ of |t₀|, and extraction gives (1-σ₀)/2+δ.
  --
  -- Strip parameters
  set a : ℝ := -(2 * δ) with ha_def
  set b : ℝ := 1 + 2 * δ with hb_def
  have hab : a < b := by linarith
  --
  -- Step 1: Compact bound for zeta_entire_v2 on strip with |Im| ≤ 2
  have h_ent_cont : Continuous zeta_entire_v2 := zeta_entire_analytic_v2.continuous
  have h_cont_a : Continuous (fun t : ℝ => ‖zeta_entire_v2 (↑a + ↑t * I)‖) :=
    (h_ent_cont.comp (continuous_const.add (continuous_ofReal.mul continuous_const))).norm
  obtain ⟨t_max_a, _, hmax_a⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := (1 : ℝ))).exists_isMaxOn
    ⟨(0 : ℝ), Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ h_cont_a.continuousOn
  set B_a := ‖zeta_entire_v2 (↑a + ↑t_max_a * I)‖ with hB_a_def
  -- hmax_a : IsMaxOn (norm ∘ zeta_entire_v2 ∘ ...) (Icc (-1) 1) t_max_a
  -- i.e., ∀ t ∈ Icc (-1) 1, ‖zeta_entire_v2(a+it)‖ ≤ B_a
  --
  -- Step 2: Left boundary (1+|t|)^{3/2+2δ} bound for zeta_entire_v2
  set α_L : ℝ := 3 / 2 + 2 * δ with hα_L_def
  have hα_L_nn : (0 : ℝ) ≤ α_L := by linarith
  have h_zev_L : ∀ t : ℝ, ‖zeta_entire_v2 (↑a + ↑t * I)‖ ≤
      (B_a + 2 * C_L + 1) * (1 + |t|) ^ α_L := by
    intro t
    by_cases ht : 1 ≤ |t|
    · -- |t| ≥ 1: use zeta_bound_neg_sigma
      have hs_ne : (↑a + ↑t * I : ℂ) ≠ 1 := by
        intro heq; have : t = 0 := by have := congr_arg Complex.im heq; simpa using this
        rw [this, abs_zero] at ht; linarith
      simp only [zeta_entire_v2, if_neg hs_ne]
      rw [norm_mul]
      -- ‖s-1‖ ≤ (1+2δ) + |t| ≤ 2(1+|t|)
      have h_s1_norm : ‖(↑a + ↑t * I - 1 : ℂ)‖ ≤ 2 * (1 + |t|) := by
        have h1 : ‖(↑a + ↑t * I - 1 : ℂ)‖ ≤ |a - 1| + |t| := by
          calc ‖(↑a + ↑t * I - 1 : ℂ)‖
              = ‖(↑(a - 1) + ↑t * I : ℂ)‖ := by push_cast; ring_nf
            _ ≤ |(↑(a - 1) + ↑t * I : ℂ).re| + |(↑(a - 1) + ↑t * I : ℂ).im| :=
                Complex.norm_le_abs_re_add_abs_im _
            _ = |a - 1| + |t| := by simp
        have h2 : |a - 1| = 1 + 2 * δ := by
          rw [ha_def, show -(2 * δ) - 1 = -(1 + 2 * δ) from by ring, abs_neg,
            abs_of_pos (by linarith)]
        linarith
      -- ‖ζ(-2δ+it)‖ ≤ C_L·|t|^{1/2+2δ}
      have h_zeta_t : ‖riemannZeta (↑a + ↑t * I)‖ ≤ C_L * |t| ^ (1 / 2 + 2 * δ) :=
        h_left t ht
      -- Product bound
      have h_t_le : |t| ≤ 1 + |t| := le_add_of_nonneg_left (by norm_num)
      have h_rpow_le : |t| ^ (1 / 2 + 2 * δ) ≤ (1 + |t|) ^ (1 / 2 + 2 * δ) :=
        rpow_le_rpow (abs_nonneg t) h_t_le (by linarith)
      calc ‖(↑a + ↑t * I - 1 : ℂ)‖ * ‖riemannZeta (↑a + ↑t * I)‖
          ≤ (2 * (1 + |t|)) * (C_L * |t| ^ (1 / 2 + 2 * δ)) :=
            mul_le_mul h_s1_norm h_zeta_t (by positivity) (by positivity)
        _ ≤ (2 * (1 + |t|)) * (C_L * (1 + |t|) ^ (1 / 2 + 2 * δ)) := by
            gcongr
        _ = 2 * C_L * ((1 + |t|) ^ (1 : ℝ) * (1 + |t|) ^ (1 / 2 + 2 * δ)) := by
            rw [rpow_one]; ring
        _ = 2 * C_L * (1 + |t|) ^ α_L := by
            rw [← rpow_add (by positivity : (0:ℝ) < 1 + |t|)]
            congr 1; rw [hα_L_def]; ring
        _ ≤ (B_a + 2 * C_L + 1) * (1 + |t|) ^ α_L := by
            have : 0 ≤ B_a := norm_nonneg _
            gcongr; linarith
    · -- |t| < 1: use compact bound
      push_neg at ht
      have ht_mem : t ∈ Set.Icc (-1 : ℝ) 1 :=
        Set.mem_Icc.mpr ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
      have h_le_Ba : ‖zeta_entire_v2 (↑a + ↑t * I)‖ ≤ B_a := hmax_a ht_mem
      have h_one_le : (1 : ℝ) ≤ (1 + |t|) ^ α_L := by
        calc (1 : ℝ) = 1 ^ α_L := (one_rpow α_L).symm
          _ ≤ (1 + |t|) ^ α_L :=
            rpow_le_rpow zero_le_one (by linarith [abs_nonneg t]) hα_L_nn
      calc ‖zeta_entire_v2 (↑a + ↑t * I)‖ ≤ B_a := h_le_Ba
        _ ≤ B_a * 1 := (mul_one _).symm.le
        _ ≤ (B_a + 2 * C_L + 1) * (1 + |t|) ^ α_L := by
            have : 0 ≤ B_a := norm_nonneg _
            gcongr; linarith
  --
  -- Step 3: Right boundary (1+|t|) bound for zeta_entire_v2
  set K_R : ℝ := (1 + 1 / (2 * δ)) * (1 + 2 * δ) + (1 + 1 / (2 * δ)) with hK_R_def
  have hK_R_pos : 0 < K_R := by positivity
  have h_zev_R : ∀ t : ℝ, ‖zeta_entire_v2 (↑b + ↑t * I)‖ ≤ K_R * (1 + |t|) := by
    intro t
    have hs_ne : (↑b + ↑t * I : ℂ) ≠ 1 := by
      intro heq; have : b = 1 := by
        have := congr_arg Complex.re heq; simpa using this
      linarith
    simp only [zeta_entire_v2, if_neg hs_ne, norm_mul]
    -- ‖s-1‖ = ‖2δ+it‖ ≤ 2δ + |t|
    have h_s1 : ‖(↑b + ↑t * I - 1 : ℂ)‖ ≤ (2 * δ) + |t| := by
      calc ‖(↑b + ↑t * I - 1 : ℂ)‖
          = ‖(↑(2 * δ) + ↑t * I : ℂ)‖ := by congr 1; rw [hb_def]; push_cast; ring
        _ ≤ |(↑(2 * δ) + ↑t * I : ℂ).re| + |(↑(2 * δ) + ↑t * I : ℂ).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = |2 * δ| + |t| := by simp
        _ = 2 * δ + |t| := by rw [abs_of_pos (by linarith)]
    have h_zeta := h_right t
    -- Product: ‖s-1‖·‖ζ‖ ≤ (2δ+|t|)·(1+1/(2δ))
    calc ‖(↑b + ↑t * I - 1 : ℂ)‖ * ‖riemannZeta (↑b + ↑t * I)‖
        ≤ (2 * δ + |t|) * (1 + 1 / (2 * δ)) :=
          mul_le_mul h_s1 h_zeta (by positivity) (by positivity)
      _ ≤ (1 + |t|) * (1 + 1 / (2 * δ)) := by gcongr; linarith
      _ ≤ (1 + |t|) * K_R := by
          gcongr; rw [hK_R_def]
          nlinarith [show 0 < (1 + 1 / (2 * δ)) * (1 + 2 * δ) from by positivity]
      _ = K_R * (1 + |t|) := by ring
  --
  -- Step 4: Build the constant C
  set K_L := B_a + 2 * C_L + 1 with hK_L_def
  have hK_L_pos : 0 < K_L := by
    have : 0 ≤ B_a := norm_nonneg _; linarith
  -- Constants from Gaussian localization
  set C_gL := rexp (α_L ^ 2 / 4 + (2 * δ) ^ 2) with hC_gL_def
  set C_gR := rexp (1 ^ 2 / 4 + (1 + 2 * δ) ^ 2) with hC_gR_def
  -- The constant: absorb (1+|t₀|)^{...} ≤ 2^{...}·|t₀|^{...} for |t₀| ≥ 1
  set C_final := 4 * (max (K_L * C_gL) (K_R * C_gR) + 1) with hC_final_def
  have hC_pos : 0 < C_final := by positivity
  refine ⟨C_final, hC_pos, fun σ₀ t₀ hσ₀_nn hσ₀_le ht₀ => ?_⟩
  --
  -- Step 5: Define the tilted Gaussian function
  have ht₀_pos : 0 < |t₀| := by linarith
  set tilt := Real.log |t₀| / 2 with htilt_def
  have htilt_nn : 0 ≤ tilt := div_nonneg (Real.log_nonneg (by linarith)) (by norm_num)
  -- F(s) = zeta_entire_v2(s) · exp((s - it₀)² + λ·s)
  -- ‖F(σ+it)‖ = ‖zeta_entire_v2‖ · exp(σ² + λσ - (t-t₀)²)
  --            = ‖zeta_entire_v2‖ · exp(σ²+λσ) · exp(-(t-t₀)²)
  -- and exp(λσ) = |t₀|^{σ/2}
  --
  -- Step 6: DiffContOnCl for F — product of entire functions
  -- (We don't need to define F explicitly; we apply PL to the Gaussian-damped
  -- boundary bounds and track the tilt factor algebraically.)
  --
  -- Instead of applying PL formally, we use the PL STRUCTURE:
  -- for each (σ₀, t₀), the bound on ‖ζ(σ₀+it₀)‖ follows from
  -- the boundary bounds + gaussian_poly_bound + algebraic extraction.
  --
  -- === Direct proof via boundary bounds ===
  -- We'll show the result without formally constructing F and applying PL.
  -- The mathematical content is equivalent, but the formalization is shorter.
  --
  -- Key idea: use polynomial_growth_implies_bounded_of_boundary_bounded_v2
  -- on F(s) = zeta_entire_v2(s) · exp((s - ↑t₀ * I)² + ↑tilt * s)
  --
  -- Define F
  set F : ℂ → ℂ := fun s =>
    zeta_entire_v2 s * Complex.exp ((s - ↑t₀ * I) ^ 2 + ↑tilt * s) with hF_def
  --
  -- DiffContOnCl: F is a product of entire functions
  have hF_diff : DiffContOnCl ℂ F (re ⁻¹' Set.Ioo a b) := by
    apply Differentiable.diffContOnCl
    exact zeta_entire_analytic_v2.mul
      (Complex.differentiable_exp.comp
        (((differentiable_id.sub (differentiable_const _)).pow 2).add
          ((differentiable_const _).mul differentiable_id)))
  --
  -- Polynomial growth: F is bounded on strip (k=0)
  -- We need: ∃ k C_g, ∀ z on strip, ‖F z‖ ≤ C_g * (1 + ‖z‖) ^ k
  -- Since the Gaussian exp(-(t-t₀)²) kills exp growth, F is bounded.
  have hF_growth : ∃ k C_g, ∀ z, a ≤ z.re → z.re ≤ b →
      ‖F z‖ ≤ C_g * (1 + ‖z‖) ^ k := by
    -- F is bounded on strip (k=0): Gaussian kills exponential growth of zev.
    -- Step A: Bound Λ₀ on wider strip for the factorization
    obtain ⟨M_Λ', hM_Λ'_pos, hΛ'⟩ := completedRiemannZeta₀_bounded_on_strip (a - 1) (b + 1)
    -- Step B: Compact bound for F when |Im z| ≤ 4
    have hF_cont : Continuous F := (zeta_entire_analytic_v2.mul
      (Complex.differentiable_exp.comp (((differentiable_id.sub
        (differentiable_const _)).pow 2).add
          ((differentiable_const _).mul differentiable_id)))).continuous
    obtain ⟨z_max, _, hz_max⟩ := (isCompact_closedBall (0:ℂ) (b + 4)).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self (by linarith)⟩ hF_cont.norm.continuousOn
    -- Step C: Set constants and prove with k=0
    set A_ext := 4 * (M_Λ' + 1) with hA_ext_def
    set C_exp := A_ext * rexp (9 / 4 + 3 * |t₀| + b ^ 2 + tilt * b)
    refine ⟨0, ‖F z_max‖ + C_exp + 1, fun z hz_l hz_r => ?_⟩
    simp only [pow_zero, mul_one]
    by_cases him : |z.im| ≤ 4
    · -- Compact case: z ∈ closedBall(0, b+4)
      have h_in_ball : z ∈ Metric.closedBall (0 : ℂ) (b + 4) := by
        rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
        calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
          _ ≤ b + 4 := by
            have : |z.re| ≤ b := abs_le.mpr ⟨by linarith [ha_def], hz_r⟩
            linarith
      have hC_pos : 0 ≤ C_exp := by positivity
      have h_le : ‖F z‖ ≤ ‖F z_max‖ := hz_max h_in_ball
      linarith
    · -- Exponential case: |Im z| > 4, use Gammaℝ factorization
      push_neg at him
      have him2 : 2 ≤ |z.im| := by linarith
      have hz_ne : z ≠ 0 := by
        intro h; simp [h] at him; linarith
      have hz_ne_one : z ≠ 1 := by
        intro h; simp [h] at him; linarith
      -- Unfold zev(z) = (z-1)·ζ(z)
      have hzev_eq : zeta_entire_v2 z = (z - 1) * riemannZeta z := by
        simp only [zeta_entire_v2, if_neg hz_ne_one]
      -- ζ(z) = completedRiemannZeta(z) / Gammaℝ(z)
      have hζ_eq : (z - 1) * riemannZeta z =
          (z - 1) * completedRiemannZeta z / Gammaℝ z := by
        rw [riemannZeta_def_of_ne_zero hz_ne]; ring
      -- Bound completedRiemannZeta
      have h_Λ₀ : ‖completedRiemannZeta₀ z‖ ≤ M_Λ' :=
        hΛ' z (by linarith) (by linarith)
      have h_inv_z : ‖(1:ℂ) / z‖ ≤ 1 / 2 := by
        rw [norm_div, norm_one]
        exact div_le_div_of_nonneg_left one_pos.le (by linarith)
          (le_trans him2 (Complex.abs_im_le_norm z))
      have h_inv_1z : ‖(1:ℂ) / (1 - z)‖ ≤ 1 / 2 := by
        rw [norm_div, norm_one]
        apply div_le_div_of_nonneg_left one_pos.le (by linarith)
        calc (2 : ℝ) ≤ |z.im| := him2
          _ = |(1 - z).im| := by simp
          _ ≤ ‖1 - z‖ := Complex.abs_im_le_norm (1 - z)
      have h_cζ : ‖completedRiemannZeta z‖ ≤ M_Λ' + 1 := by
        rw [completedRiemannZeta_eq]
        calc ‖completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)‖
            ≤ ‖completedRiemannZeta₀ z - 1 / z‖ + ‖1 / (1 - z)‖ := norm_sub_le _ _
          _ ≤ (‖completedRiemannZeta₀ z‖ + ‖1 / z‖) + ‖1 / (1 - z)‖ := by
              linarith [norm_sub_le (completedRiemannZeta₀ z) (1 / z)]
          _ ≤ (M_Λ' + 1/2) + 1/2 := by linarith
          _ = M_Λ' + 1 := by ring
      -- ‖z-1‖ ≤ 2|z.im|
      have h_z1 : ‖z - (1:ℂ)‖ ≤ 2 * |z.im| := by
        calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| :=
              Complex.norm_le_abs_re_add_abs_im (z - 1)
          _ = |z.re - 1| + |z.im| := by simp
          _ ≤ (3/2) + |z.im| := by
              have : |z.re - 1| ≤ 3/2 := abs_le.mpr ⟨by linarith [ha_def], by linarith [hb_def]⟩
              linarith
          _ ≤ 2 * |z.im| := by linarith
      -- Gammaℝ inverse bound
      have h_inv_Γ : ‖(Gammaℝ z)⁻¹‖ ≤ 2 * rexp (π * |z.im| / 2) :=
        inv_gammaR_bound_ext z (by linarith [ha_def]) (by linarith [hb_def]) him2
      -- Combine: ‖zev(z)‖ ≤ A_ext · exp(3|z.im|)
      have h_zev : ‖zeta_entire_v2 z‖ ≤ A_ext * rexp (3 * |z.im|) := by
        rw [hzev_eq, hζ_eq, norm_div, norm_mul]
        have h_num : ‖z - 1‖ * ‖completedRiemannZeta z‖ ≤ 2 * (M_Λ' + 1) * |z.im| :=
          calc ‖z - 1‖ * ‖completedRiemannZeta z‖
              ≤ (2 * |z.im|) * (M_Λ' + 1) := mul_le_mul h_z1 h_cζ (norm_nonneg _) (by positivity)
            _ = 2 * (M_Λ' + 1) * |z.im| := by ring
        have h_id_le : |z.im| ≤ rexp |z.im| := by
          linarith [Real.add_one_le_exp |z.im|]
        have h_exp_comb : rexp |z.im| * rexp (π * |z.im| / 2) ≤ rexp (3 * |z.im|) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [pi_lt_four])
        have hΓ_pos : 0 < ‖Gammaℝ z‖ := by
          rw [norm_pos_iff, Ne, Gammaℝ_eq_zero_iff]; push_neg; intro n hn
          have h0 : z.im = 0 := by have := congr_arg Complex.im hn; simp at this; linarith
          rw [h0, abs_zero] at him2; linarith
        calc ‖z - 1‖ * ‖completedRiemannZeta z‖ / ‖Gammaℝ z‖
            = ‖z - 1‖ * ‖completedRiemannZeta z‖ * ‖(Gammaℝ z)⁻¹‖ := by
              rw [norm_inv, div_eq_mul_inv]
          _ ≤ (2 * (M_Λ' + 1) * |z.im|) * (2 * rexp (π * |z.im| / 2)) :=
              mul_le_mul h_num h_inv_Γ (by positivity) (by positivity)
          _ = A_ext * (|z.im| * rexp (π * |z.im| / 2)) := by rw [hA_ext_def]; ring
          _ ≤ A_ext * (rexp |z.im| * rexp (π * |z.im| / 2)) := by gcongr
          _ ≤ A_ext * rexp (3 * |z.im|) := by gcongr
      -- Compute Re of exponential
      have h_re_gen : ((z - ↑t₀ * I) ^ 2 + ↑tilt * z : ℂ).re =
          z.re ^ 2 + tilt * z.re - (z.im - t₀) ^ 2 := by
        simp only [sq, Complex.add_re, Complex.sub_re, Complex.mul_re,
          Complex.add_im, Complex.sub_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, one_mul]
        ring
      -- σ² + tilt·σ ≤ b² + tilt·b
      have h_sigma : z.re ^ 2 + tilt * z.re ≤ b ^ 2 + tilt * b := by
        nlinarith [mul_nonneg (show 0 ≤ b - z.re from by linarith)
          (show 0 ≤ b + z.re + tilt from by linarith [ha_def, hb_def])]
      -- 3|t| - (t-t₀)² ≤ 9/4 + 3|t₀|
      have h_gauss : 3 * |z.im| - (z.im - t₀) ^ 2 ≤ 9 / 4 + 3 * |t₀| := by
        have h_tri : |z.im| ≤ |z.im - t₀| + |t₀| := by
          linarith [abs_sub_abs_le_abs_sub z.im t₀]
        nlinarith [sq_abs (z.im - t₀), sq_nonneg (|z.im - t₀| - 3 / 2)]
      -- Final bound
      have h_norm_F : ‖F z‖ = ‖zeta_entire_v2 z‖ *
          rexp (z.re ^ 2 + tilt * z.re - (z.im - t₀) ^ 2) := by
        simp only [hF_def, norm_mul, Complex.norm_exp, h_re_gen]
      calc ‖F z‖ = ‖zeta_entire_v2 z‖ *
            rexp (z.re ^ 2 + tilt * z.re - (z.im - t₀) ^ 2) := h_norm_F
        _ ≤ (A_ext * rexp (3 * |z.im|)) *
            rexp (b ^ 2 + tilt * b - (z.im - t₀) ^ 2) :=
              mul_le_mul h_zev (Real.exp_le_exp.mpr (sub_le_sub_right h_sigma _))
                (Real.exp_nonneg _) (by positivity)
        _ = A_ext * rexp (3 * |z.im| + (b ^ 2 + tilt * b - (z.im - t₀) ^ 2)) := by
              rw [mul_assoc, ← Real.exp_add]
        _ ≤ A_ext * rexp (9 / 4 + 3 * |t₀| + b ^ 2 + tilt * b) := by
              have hA_nn : 0 ≤ A_ext := by positivity
              exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [h_gauss])) hA_nn
        _ ≤ ‖F z_max‖ + C_exp + 1 := by linarith [norm_nonneg (F z_max)]
  --
  -- Left boundary bound: ∀ y, ‖F(a + I*y)‖ ≤ M
  -- M is chosen so both boundaries satisfy it
  set M_bound := C_final * |t₀| ^ (3 / 2 + δ) with hM_def
  have hM_pos : 0 < M_bound := by positivity
  --
  have hF_left : ∀ y : ℝ, ‖F (↑a + I * ↑y)‖ ≤ M_bound := by
    intro y
    simp only [hF_def, norm_mul, Complex.norm_exp]
    -- Re((a+iy - it₀)² + λ(a+iy)) = a²+λa - (y-t₀)²
    have h_re : ((↑a + I * ↑y - ↑t₀ * I) ^ 2 + ↑tilt * (↑a + I * ↑y) : ℂ).re =
        a ^ 2 + tilt * a - (y - t₀) ^ 2 := by
      simp only [sq, Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.add_im, Complex.sub_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, one_mul]
      ring
    rw [h_re]
    -- exp(a²+λa-(y-t₀)²) = exp(a²+λa)·exp(-(y-t₀)²)
    rw [show a ^ 2 + tilt * a - (y - t₀) ^ 2 =
        (a ^ 2 + tilt * a) + (-(y - t₀) ^ 2) from by ring, Real.exp_add]
    -- ‖zeta_entire_v2(a+iy)‖ ≤ K_L·(1+|y|)^α_L
    have h_zev := h_zev_L y
    -- Gaussian: (1+|y|)^α_L · exp(-(y-t₀)²) ≤ exp(α_L²/4)·(1+|t₀|)^α_L
    have h_gauss := gaussian_poly_bound α_L hα_L_nn t₀ y
    -- exp(a²+λa) = exp(4δ²)·|t₀|^{-δ}  (since λa = (log|t₀|/2)·(-2δ) = -δ·log|t₀|)
    have h_tilt_a : rexp (a ^ 2 + tilt * a) = rexp (a ^ 2) * |t₀| ^ (-δ) := by
      rw [Real.exp_add]
      congr 1
      rw [htilt_def, ha_def]
      rw [rpow_def_of_pos ht₀_pos]
      congr 1; ring
    -- (1+|t₀|)^α_L ≤ 2^α_L · |t₀|^α_L for |t₀| ≥ 1
    have h_one_plus : (1 + |t₀|) ^ α_L ≤ (2 * |t₀|) ^ α_L :=
      rpow_le_rpow (by positivity) (by linarith) hα_L_nn
    have h_two_pow : (2 * |t₀|) ^ α_L = 2 ^ α_L * |t₀| ^ α_L :=
      mul_rpow (by norm_num : (0:ℝ) ≤ 2) (le_of_lt ht₀_pos)
    -- |t₀|^α_L · |t₀|^{-δ} = |t₀|^{α_L-δ} = |t₀|^{3/2+δ}
    have h_rpow_combine : |t₀| ^ α_L * |t₀| ^ (-δ) = |t₀| ^ (3 / 2 + δ) := by
      rw [← rpow_add ht₀_pos]; congr 1; rw [hα_L_def]; ring
    -- Combine: ‖zev‖*(exp(a²+tilt*a)*exp(-(y-t₀)²)) ≤ M_bound
    rw [h_tilt_a, hM_def]
    calc ‖zeta_entire_v2 (↑a + I * ↑y)‖ * (rexp (a ^ 2) * |t₀| ^ (-δ) * rexp (-(y - t₀) ^ 2))
        ≤ (K_L * (1 + |y|) ^ α_L) * (rexp (a ^ 2) * |t₀| ^ (-δ) * rexp (-(y - t₀) ^ 2)) := by
          gcongr; rw [show (I : ℂ) * (↑y : ℂ) = ↑y * I from mul_comm _ _]; exact h_zev
      _ = K_L * rexp (a ^ 2) * |t₀| ^ (-δ) * ((1 + |y|) ^ α_L * rexp (-(y - t₀) ^ 2)) := by
          ring
      _ ≤ K_L * rexp (a ^ 2) * |t₀| ^ (-δ) * (rexp (α_L ^ 2 / 4) * (1 + |t₀|) ^ α_L) := by
          have h_prefix : 0 ≤ K_L * rexp (a ^ 2) * |t₀| ^ (-δ) := by positivity
          exact mul_le_mul_of_nonneg_left h_gauss h_prefix
      _ ≤ K_L * rexp (a ^ 2) * |t₀| ^ (-δ) * (rexp (α_L ^ 2 / 4) * (2 ^ α_L * |t₀| ^ α_L)) := by
          gcongr; calc (1 + |t₀|) ^ α_L ≤ (2 * |t₀|) ^ α_L := h_one_plus
            _ = 2 ^ α_L * |t₀| ^ α_L := h_two_pow
      _ = K_L * (rexp (a ^ 2) * rexp (α_L ^ 2 / 4)) * 2 ^ α_L *
          (|t₀| ^ α_L * |t₀| ^ (-δ)) := by ring
      _ = K_L * rexp (a ^ 2 + α_L ^ 2 / 4) * 2 ^ α_L * |t₀| ^ (3 / 2 + δ) := by
          rw [← Real.exp_add, h_rpow_combine]
      _ = K_L * C_gL * 2 ^ α_L * |t₀| ^ (3 / 2 + δ) := by
          congr 2; rw [hC_gL_def]; congr 1; rw [ha_def]; ring_nf
      _ ≤ C_final * |t₀| ^ (3 / 2 + δ) := by
          gcongr
          have h_αL_le : α_L ≤ 2 := by rw [hα_L_def]; linarith
          have h_2le : (2 : ℝ) ^ α_L ≤ 4 := by
            calc (2 : ℝ) ^ α_L ≤ 2 ^ (2 : ℝ) :=
                rpow_le_rpow_of_exponent_le (by norm_num) h_αL_le
              _ = 4 := by norm_num
          calc K_L * C_gL * 2 ^ α_L ≤ K_L * C_gL * 4 := by gcongr
            _ ≤ max (K_L * C_gL) (K_R * C_gR) * 4 := by gcongr; exact le_max_left _ _
            _ ≤ (max (K_L * C_gL) (K_R * C_gR) + 1) * 4 := by nlinarith
            _ = C_final := by rw [hC_final_def]; ring
  --
  have hF_right : ∀ y : ℝ, ‖F (↑b + I * ↑y)‖ ≤ M_bound := by
    intro y
    simp only [hF_def, norm_mul, Complex.norm_exp]
    have h_re : ((↑b + I * ↑y - ↑t₀ * I) ^ 2 + ↑tilt * (↑b + I * ↑y) : ℂ).re =
        b ^ 2 + tilt * b - (y - t₀) ^ 2 := by
      simp only [sq, Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.add_im, Complex.sub_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, one_mul]
      ring
    rw [h_re]
    rw [show b ^ 2 + tilt * b - (y - t₀) ^ 2 =
        (b ^ 2 + tilt * b) + (-(y - t₀) ^ 2) from by ring, Real.exp_add]
    have h_zev := h_zev_R y
    have h_gauss := gaussian_poly_bound 1 (by norm_num) t₀ y
    -- exp(b²+λb) = exp(b²)·|t₀|^{(1+2δ)/2}
    have h_tilt_b : rexp (b ^ 2 + tilt * b) = rexp (b ^ 2) * |t₀| ^ ((1 + 2 * δ) / 2) := by
      rw [Real.exp_add]; congr 1
      rw [htilt_def, hb_def, rpow_def_of_pos ht₀_pos]; congr 1; ring
    -- (1+|t₀|)^1 ≤ 2|t₀| for |t₀| ≥ 1
    -- |t₀|·|t₀|^{(1+2δ)/2} = |t₀|^{1+(1+2δ)/2} = |t₀|^{3/2+δ}
    have h_rpow_combine_R : |t₀| ^ (1 : ℝ) * |t₀| ^ ((1 + 2 * δ) / 2) =
        |t₀| ^ (3 / 2 + δ) := by
      rw [← rpow_add ht₀_pos]; congr 1; ring
    -- Combine: ‖zev‖*(exp(b²+tilt*b)*exp(-(y-t₀)²)) ≤ M_bound
    rw [h_tilt_b, hM_def]
    calc ‖zeta_entire_v2 (↑b + I * ↑y)‖ * (rexp (b ^ 2) * |t₀| ^ ((1 + 2 * δ) / 2) *
          rexp (-(y - t₀) ^ 2))
        ≤ (K_R * (1 + |y|)) * (rexp (b ^ 2) * |t₀| ^ ((1 + 2 * δ) / 2) *
          rexp (-(y - t₀) ^ 2)) := by
          gcongr; rw [show (I : ℂ) * (↑y : ℂ) = ↑y * I from mul_comm _ _]; exact h_zev
      _ = K_R * rexp (b ^ 2) * |t₀| ^ ((1 + 2 * δ) / 2) *
          ((1 + |y|) * rexp (-(y - t₀) ^ 2)) := by ring
      _ ≤ K_R * rexp (b ^ 2) * |t₀| ^ ((1 + 2 * δ) / 2) *
          (rexp (1 ^ 2 / 4) * (2 * |t₀|)) := by
          have h_gauss' : (1 + |y|) * rexp (-(y - t₀) ^ 2) ≤
              rexp (1 ^ 2 / 4) * (1 + |t₀|) := by
            have := h_gauss; simp only [rpow_one] at this; exact this
          have h_2t : rexp (1 ^ 2 / 4) * (1 + |t₀|) ≤ rexp (1 ^ 2 / 4) * (2 * |t₀|) := by
            gcongr; linarith
          have h_combo := le_trans h_gauss' h_2t
          have h_prefix : 0 ≤ K_R * rexp (b ^ 2) * |t₀| ^ ((1 + 2 * δ) / 2) := by positivity
          exact mul_le_mul_of_nonneg_left h_combo h_prefix
      _ = K_R * (rexp (b ^ 2) * rexp (1 ^ 2 / 4)) * 2 *
          (|t₀| ^ (1 : ℝ) * |t₀| ^ ((1 + 2 * δ) / 2)) := by
          rw [rpow_one]; ring
      _ = K_R * rexp (b ^ 2 + 1 ^ 2 / 4) * 2 * |t₀| ^ (3 / 2 + δ) := by
          rw [← Real.exp_add, h_rpow_combine_R]
      _ = K_R * C_gR * 2 * |t₀| ^ (3 / 2 + δ) := by
          congr 2; rw [hC_gR_def]; congr 1; rw [hb_def]; ring_nf
      _ ≤ C_final * |t₀| ^ (3 / 2 + δ) := by
          gcongr
          have hKR_nn : 0 ≤ K_R * C_gR := by positivity
          calc K_R * C_gR * 2 ≤ K_R * C_gR * 4 := by nlinarith
            _ ≤ max (K_L * C_gL) (K_R * C_gR) * 4 := by
                gcongr; exact le_max_right _ _
            _ ≤ (max (K_L * C_gL) (K_R * C_gR) + 1) * 4 := by nlinarith
            _ = C_final := by rw [hC_final_def]; ring
  --
  -- Step 10: Apply PL
  have hF_bound := polynomial_growth_implies_bounded_of_boundary_bounded_v2 hab
    hF_diff hF_growth hF_left hF_right
  --
  -- Step 11: Evaluate at σ₀+it₀ and extract
  have hz_left : a ≤ (↑σ₀ + ↑t₀ * I : ℂ).re := by simp [ha_def]; linarith
  have hz_right : (↑σ₀ + ↑t₀ * I : ℂ).re ≤ b := by simp [hb_def]; linarith
  have h_eval := hF_bound (↑σ₀ + ↑t₀ * I) hz_left hz_right
  -- h_eval : ‖F(σ₀+it₀)‖ ≤ M_bound = C_final · |t₀|^{3/2+δ}
  --
  -- F(σ₀+it₀) = zeta_entire_v2(σ₀+it₀) · exp(σ₀² + λσ₀)
  -- since (σ₀+it₀ - it₀)² = σ₀², so Re = σ₀² + λσ₀
  -- ‖zeta_entire_v2(σ₀+it₀)‖ ≤ M_bound / exp(σ₀² + λσ₀)
  -- ‖(σ₀+it₀-1)‖ ≥ |t₀| (since ‖(σ₀-1)+it₀‖ ≥ |Im| = |t₀|)
  -- zeta_entire_v2(σ₀+it₀) = (σ₀+it₀-1)·ζ(σ₀+it₀) (since σ₀+it₀ ≠ 1)
  -- ‖ζ(σ₀+it₀)‖ ≤ M_bound / (exp(σ₀² + λσ₀) · |t₀|)
  --             ≤ C_final · |t₀|^{3/2+δ} / (1 · |t₀|^{σ₀/2} · |t₀|)
  --             = C_final · |t₀|^{3/2+δ - σ₀/2 - 1}
  --             = C_final · |t₀|^{(1-σ₀)/2+δ}
  --
  -- Show σ₀+it₀ ≠ 1
  have hs_ne_one : (↑σ₀ + ↑t₀ * I : ℂ) ≠ 1 := by
    intro heq; have : t₀ = 0 := by have := congr_arg Complex.im heq; simpa using this
    rw [this, abs_zero] at ht₀; linarith
  -- ‖(σ₀+it₀-1)‖ ≥ |t₀|
  have h_s1_lower : |t₀| ≤ ‖(↑σ₀ + ↑t₀ * I - 1 : ℂ)‖ := by
    calc |t₀| = |(↑σ₀ + ↑t₀ * I - 1 : ℂ).im| := by simp
      _ ≤ ‖(↑σ₀ + ↑t₀ * I - 1 : ℂ)‖ := Complex.abs_im_le_norm _
  -- F norm computation at σ₀+it₀
  have h_F_at : ‖F (↑σ₀ + ↑t₀ * I)‖ = ‖zeta_entire_v2 (↑σ₀ + ↑t₀ * I)‖ *
      rexp (σ₀ ^ 2 + tilt * σ₀) := by
    simp only [hF_def, norm_mul, Complex.norm_exp]
    congr 1
    simp only [sq, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add]
    ring_nf
  -- zeta_entire_v2 = (s-1)·ζ(s)
  have h_zev_eq : zeta_entire_v2 (↑σ₀ + ↑t₀ * I) =
      (↑σ₀ + ↑t₀ * I - 1) * riemannZeta (↑σ₀ + ↑t₀ * I) := by
    simp only [zeta_entire_v2, if_neg hs_ne_one]
  --
  -- Chain: ‖ζ‖ ≤ ‖zeta_entire_v2‖ / |t₀| ≤ M / (exp(σ₀²+λσ₀)·|t₀|)
  --       ≤ C_final·|t₀|^{3/2+δ} / |t₀|^{σ₀/2+1}
  --       = C_final·|t₀|^{(1-σ₀)/2+δ}
  have h_exp_pos : 0 < rexp (σ₀ ^ 2 + tilt * σ₀) := Real.exp_pos _
  have h_s1_pos : 0 < ‖(↑σ₀ + ↑t₀ * I - 1 : ℂ)‖ := by
    rw [norm_pos_iff]; intro h; exact hs_ne_one (sub_eq_zero.mp h)
  -- ‖ζ‖ = ‖zeta_entire_v2‖ / ‖s-1‖
  have h_norm_rel : ‖riemannZeta (↑σ₀ + ↑t₀ * I)‖ =
      ‖zeta_entire_v2 (↑σ₀ + ↑t₀ * I)‖ / ‖(↑σ₀ + ↑t₀ * I - 1 : ℂ)‖ := by
    rw [h_zev_eq, norm_mul, mul_div_cancel_left₀ _ (ne_of_gt h_s1_pos)]
  rw [h_norm_rel]
  -- ‖zeta_entire_v2‖ ≤ M_bound / exp(σ₀² + tilt*σ₀)
  have h_zev_bound : ‖zeta_entire_v2 (↑σ₀ + ↑t₀ * I)‖ ≤
      M_bound / rexp (σ₀ ^ 2 + tilt * σ₀) := by
    rw [le_div_iff₀ h_exp_pos, ← h_F_at]; exact h_eval
  -- exp(σ₀²+λσ₀) ≥ exp(λσ₀) = |t₀|^{σ₀/2}
  have h_exp_lower : |t₀| ^ (σ₀ / 2) ≤ rexp (σ₀ ^ 2 + tilt * σ₀) := by
    calc |t₀| ^ (σ₀ / 2) = rexp (σ₀ / 2 * Real.log |t₀|) := by
          rw [rpow_def_of_pos ht₀_pos]; congr 1; ring
      _ = rexp (tilt * σ₀) := by congr 1; rw [htilt_def]; ring
      _ ≤ rexp (σ₀ ^ 2 + tilt * σ₀) :=
          Real.exp_le_exp.mpr (le_add_of_nonneg_left (sq_nonneg σ₀))
  -- |t₀|^{σ₀/2} · |t₀| = |t₀|^{σ₀/2+1}
  have h_rpow_s1 : |t₀| ^ (σ₀ / 2) * |t₀| = |t₀| ^ (σ₀ / 2 + 1) := by
    nth_rw 2 [show (|t₀| : ℝ) = |t₀| ^ (1 : ℝ) from (rpow_one _).symm]
    rw [← rpow_add ht₀_pos]
  -- 3/2+δ - (σ₀/2+1) = (1-σ₀)/2+δ
  have h_exp_eq : 3 / 2 + δ - (σ₀ / 2 + 1) = (1 - σ₀) / 2 + δ := by ring
  --
  calc ‖zeta_entire_v2 (↑σ₀ + ↑t₀ * I)‖ / ‖(↑σ₀ + ↑t₀ * I - 1 : ℂ)‖
      ≤ ‖zeta_entire_v2 (↑σ₀ + ↑t₀ * I)‖ / |t₀| :=
        div_le_div_of_nonneg_left (norm_nonneg _) ht₀_pos h_s1_lower
    _ ≤ (M_bound / rexp (σ₀ ^ 2 + tilt * σ₀)) / |t₀| :=
        div_le_div_of_nonneg_right h_zev_bound (le_of_lt ht₀_pos)
    _ = M_bound / (rexp (σ₀ ^ 2 + tilt * σ₀) * |t₀|) := by rw [div_div]
    _ ≤ M_bound / (|t₀| ^ (σ₀ / 2) * |t₀|) :=
        div_le_div_of_nonneg_left (le_of_lt hM_pos)
          (mul_pos (rpow_pos_of_pos ht₀_pos _) ht₀_pos)
          (mul_le_mul_of_nonneg_right h_exp_lower (le_of_lt ht₀_pos))
    _ = M_bound / |t₀| ^ (σ₀ / 2 + 1) := by rw [h_rpow_s1]
    _ = C_final * (|t₀| ^ (3 / 2 + δ) / |t₀| ^ (σ₀ / 2 + 1)) := by
        rw [hM_def]; ring
    _ = C_final * |t₀| ^ (3 / 2 + δ - (σ₀ / 2 + 1)) := by
        rw [← rpow_sub ht₀_pos]
    _ = C_final * |t₀| ^ ((1 - σ₀) / 2 + δ) := by rw [h_exp_eq]

/-- General convexity bound: |ζ(σ+it)| ≤ C|t|^{μ(σ)+ε} for 0 ≤ σ ≤ 1.

    Follows from zeta_pl_interpolation (PL three-lines) with exponent upgrade δ → ε.
    For σ ∈ [0,1]: convexity_exponent(σ) = (1-σ)/2, and (1-σ)/2+δ ≤ (1-σ)/2+ε. -/
theorem zeta_convexity_bound (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ (convexity_exponent σ + ε) := by
  set δ := min ε (1/4) with hδ_def
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ14 : δ ≤ 1/4 := min_le_right _ _
  obtain ⟨C₀, hC₀, h_pl⟩ := zeta_pl_interpolation δ hδ hδ14
  refine ⟨C₀, hC₀, fun t ht => ?_⟩
  have h_exp_le : (1 - σ) / 2 + δ ≤ convexity_exponent σ + ε := by
    have hconv : convexity_exponent σ = (1 - σ) / 2 := by
      unfold convexity_exponent; exact max_eq_right (by linarith)
    linarith
  calc ‖riemannZeta (↑σ + ↑t * I)‖
      ≤ C₀ * |t| ^ ((1 - σ) / 2 + δ) := h_pl σ t hσ0 hσ1 ht
    _ ≤ C₀ * |t| ^ (convexity_exponent σ + ε) := by
        exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le ht h_exp_le)
          (le_of_lt hC₀)

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
