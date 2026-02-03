/-
Mean square infrastructure for zeta on critical line - proved by Aristotle.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib
import Littlewood.Aristotle.HarmonicSumIntegral
import Littlewood.Aristotle.OffDiagonalBound
import Littlewood.Aristotle.IntegralLogAsymp

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

noncomputable section

open Complex Real Filter Asymptotics MeasureTheory Topology
open scoped BigOperators Real Nat Classical Pointwise

/-- The χ factor from the functional equation -/
noncomputable def chi (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (s - 1/2) * Gamma ((1 - s) / 2) / Gamma (s / 2)

/-- |χ(1/2 + it)| = 1 on the critical line.
    This follows from the reflection formula and Γ conjugation:
    - π^{it} has norm 1 (pure imaginary exponent of positive base)
    - Γ((1/2-it)/2) = conj(Γ((1/2+it)/2)), so the ratio has norm 1 -/
lemma norm_chi_critical_line (t : ℝ) : ‖chi (1/2 + I * t)‖ = 1 := by
  unfold chi
  -- Simplify at s = 1/2 + it
  have h1 : (1/2 + I * (t : ℂ) : ℂ) - 1/2 = I * ↑t := by ring
  have h2 : ((1/2 + I * (t : ℂ)) : ℂ) / 2 = 1/4 + I * ↑t / 2 := by ring
  have h3 : (1 - (1/2 + I * (t : ℂ) : ℂ)) / 2 = 1/4 - I * ↑t / 2 := by ring
  rw [h1, h2, h3]
  -- Γ(1/4 - it/2) = star(Γ(1/4 + it/2)) via Schwarz reflection
  have h_conj : (1:ℂ)/4 - I * ↑t / 2 = star ((1:ℂ)/4 + I * ↑t / 2) := by
    apply Complex.ext
    · simp [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, div_ofNat_re]
    · simp [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, div_ofNat_im]; ring
  have h_gc : Gamma ((1:ℂ)/4 - I * ↑t / 2) = star (Gamma ((1:ℂ)/4 + I * ↑t / 2)) := by
    rw [h_conj]; exact Gamma_conj _
  -- Γ(1/4 + it/2) ≠ 0 since Re(1/4 + it/2) = 1/4 > 0
  have h_gne : Gamma ((1:ℂ)/4 + I * ↑t / 2) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, div_ofNat_re,
               mul_zero, zero_mul, sub_zero]
    norm_num
  -- |conj(Γ)/Γ| = 1 and |π^(it)| = 1
  rw [norm_div, norm_mul, h_gc, norm_star, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr h_gne)]
  -- ‖π^(I*t)‖ = 1: positive real to purely imaginary power
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [cpow_def_of_ne_zero hpi_ne, norm_exp]
  have : (Complex.log ↑Real.pi * (I * ↑t)).re = 0 := by
    rw [(Complex.ofReal_log (le_of_lt Real.pi_pos)).symm]
    simp only [mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  rw [this, Real.exp_zero]

/-- Partial sums of the zeta Dirichlet series -/
noncomputable def partialZeta (x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), (n : ℂ) ^ (-s)

/-- N(t) = floor(√(t/2π)) - the truncation point for the approximate functional equation -/
noncomputable def N_t (t : ℝ) : ℕ := Nat.floor (Real.sqrt (t / (2 * Real.pi)))

/-- N_t equals N_truncation from HarmonicSumIntegral -/
lemma N_t_eq_N_truncation (t : ℝ) : N_t t = N_truncation t := rfl

/-- The Icc sum equals harmonicSum -/
lemma sum_Icc_eq_harmonicSum (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1:ℝ)/k = harmonicSum n := by
  -- Use transitivity: Icc sum = harmonic n = harmonicSum n
  rw [harmonicSum_eq_harmonic, harmonic_eq_sum_Icc]
  push_cast
  simp only [one_div]

/-- The harmonic sum differs from log by O(1).
    This is the Euler-Mascheroni constant relationship:
    H_n = Σ_{k=1}^n 1/k = ln(n) + γ + O(1/n) where γ ≈ 0.5772... -/
lemma harmonic_sum_bound :
    (fun x => (∑ n ∈ Finset.Icc 1 (Nat.floor x), (1:ℝ)/n) - Real.log x) =O[atTop] (fun _ => (1:ℝ)) := by
  -- Standard result: H_n - ln(n) converges to γ
  -- Upper bound: H_n ≤ 1 + ln(n) via integral test (∫_1^n 1/x dx = ln n ≤ Σ 1/k)
  -- Lower bound: H_n ≥ ln(n+1) via integral test (Σ 1/k ≥ ∫_1^{n+1} 1/x dx = ln(n+1))
  -- Combined: |H_n - ln n| ≤ max(1, ln((n+1)/n)) ≤ 2
  rw [Asymptotics.isBigO_iff]
  use 2
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [Real.norm_eq_abs, norm_one, mul_one, one_div]
  -- Convert sum to harmonic number
  have h_eq : ∑ i ∈ Finset.Icc 1 ⌊x⌋₊, (↑i : ℝ)⁻¹ = ↑(harmonic ⌊x⌋₊) := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  rw [h_eq]
  -- Use Mathlib's harmonic number bounds
  have h_lo := log_le_harmonic_floor x (by linarith)
  have h_hi := harmonic_floor_le_one_add_log x hx
  rw [abs_le]; constructor <;> linarith

/-- The integral of log(√(t/2π)) is Θ(T log T).
    Explicit: ∫₁ᵀ log(√(t/2π)) dt = (1/2) ∫₁ᵀ (log t - log 2π) dt
            = (1/2)(T log T - T - T log 2π + 1 + log 2π)
            = (1/2) T log T + O(T) = Θ(T log T) -/
lemma integral_log_sqrt_asymp :
    (fun T => ∫ t in (1:ℝ)..T, Real.log (Real.sqrt (t / (2 * Real.pi)))) =Θ[atTop] (fun T => T * Real.log T) := by
  -- Proof outline:
  -- 1. Simplify: log(√(t/2π)) = (1/2)(log t - log(2π))
  -- 2. Compute: ∫₁ᵀ log t dt = T log T - T + 1 (via FTC with antiderivative t log t - t)
  -- 3. Therefore: ∫₁ᵀ log(√(t/2π)) dt = (1/2)(T log T - T + 1) - (1/2)(T-1)log(2π)
  --                                    = (1/2) T log T + O(T)
  -- 4. This is Θ(T log T) since the leading coefficient 1/2 > 0
  -- The bounds needed:
  --   Upper: (1/2) T log T + O(T) ≤ C * T log T for C > 1/2
  --   Lower: c * T log T ≤ (1/2) T log T + O(T) for c < 1/2 and large T
  exact IntegralLogAsymp.integral_log_sqrt_asymp

/-- The integral of harmonic sums is Θ(T log T).
    Since H_{N(t)} = log(N(t)) + O(1) and N(t) = √(t/2π),
    we have H_{N(t)} = (1/2) log(t/2π) + O(1).
    Integrating: ∫₁ᵀ H_{N(t)} dt = (1/2) ∫₁ᵀ log(t/2π) dt + O(T) = Θ(T log T) -/
lemma integral_harmonic_sum_asymp :
    (fun T => ∫ t in (1:ℝ)..T, ∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) =Θ[atTop] (fun T => T * Real.log T) := by
  -- Convert to harmonicSum and use the proved result from HarmonicSumIntegral
  have h_eq : (fun T => ∫ t in (1:ℝ)..T, ∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) =
              (fun T => ∫ t in (1:ℝ)..T, harmonicSum (N_truncation t)) := by
    ext T
    congr 1
    ext t
    rw [sum_Icc_eq_harmonicSum, N_t_eq_N_truncation]
  rw [h_eq]
  exact integral_harmonicSum_asymp

/-- Off-diagonal part of |partial zeta|².
    When expanding |Σ n^{-1/2-it}|² = Σ_n Σ_m n^{-1/2-it} m^{-1/2+it},
    the off-diagonal terms (n ≠ m) form this sum. -/
noncomputable def offDiagSsq (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (N_t t), ∑ m ∈ Finset.Icc 1 (N_t t),
    if n ≠ m then (n * m : ℂ) ^ (-(1/2 : ℂ)) * ((n : ℂ) / m) ^ (-(I * t)) else 0

/-- Bound on oscillatory integral.
    ∫_A^B (n/m)^{-it} dt = ∫_A^B exp(-it log(n/m)) dt
                        = [exp(-it log(n/m)) / (-i log(n/m))]_A^B
    The norm of the antiderivative difference is ≤ 2/|log(n/m)|. -/
lemma integral_cpow_neg_mul_bound (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) (hnm : n ≠ m) (A B : ℝ) :
    ‖∫ t in A..B, ((n : ℂ) / m) ^ (-(I * t))‖ ≤ 2 / |Real.log ((n : ℝ) / m)| := by
  -- Setup: α = log(n/m) ≠ 0, c = -Iα ≠ 0
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_ratio_pos : (0 : ℝ) < (n : ℝ) / m := div_pos hn_pos hm_pos
  have h_ratio_ne_one : (n : ℝ) / m ≠ 1 := by
    intro h
    exact hnm (Nat.cast_injective ((div_eq_one_iff_eq (ne_of_gt hm_pos)).mp h))
  set α := Real.log ((n : ℝ) / m) with hα_def
  have hα_ne : α ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one h_ratio_pos h_ratio_ne_one
  set c := -(I * (α : ℂ)) with hc_def
  have hc_ne : c ≠ 0 := by
    rw [hc_def, neg_ne_zero]
    exact mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hα_ne)
  -- Step 1: Rewrite integrand (n/m)^(-It) = exp(c * t)
  have h_base_ne : (↑((n : ℝ) / m) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt h_ratio_pos)
  have h_rewrite : ∀ t : ℝ, ((n : ℂ) / m) ^ (-(I * ↑t)) = exp (c * ↑t) := by
    intro t
    rw [show (n : ℂ) / m = ↑((n : ℝ) / m) from by push_cast; ring]
    rw [cpow_def_of_ne_zero h_base_ne]
    congr 1
    rw [← Complex.ofReal_log (le_of_lt h_ratio_pos)]
    rw [hc_def]; ring
  -- Rewrite the integral
  have h_int_eq : ∫ t in A..B, ((n : ℂ) / m) ^ (-(I * ↑t)) =
      ∫ t in A..B, exp (c * ↑t) :=
    intervalIntegral.integral_congr (fun t _ => h_rewrite t)
  rw [h_int_eq]
  -- Step 2: FTC with antiderivative F(t) = exp(c*t)/c
  have h_deriv : ∀ t ∈ Set.uIcc A B,
      HasDerivAt (fun u : ℝ => exp (c * ↑u) / c) (exp (c * ↑t)) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => c * (↑u : ℂ)) c t := by
      have h := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
      simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at h
      exact h
    have h2 := h1.cexp
    have h3 := h2.div_const c
    rwa [mul_div_cancel_right₀ _ hc_ne] at h3
  have h_integrable : IntervalIntegrable (fun t => exp (c * ↑t)) MeasureTheory.volume A B :=
    (continuous_exp.comp (continuous_const.mul continuous_ofReal)).continuousOn.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_integrable]
  -- Step 3: Bound ‖exp(c*B)/c - exp(c*A)/c‖ ≤ 2/|α|
  rw [← sub_div, norm_div]
  -- ‖c‖ = |α| since c = -Iα
  have hc_norm : ‖c‖ = |α| := by
    rw [hc_def, norm_neg, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hc_norm]
  -- Numerator bound: ‖exp(c*B) - exp(c*A)‖ ≤ 2
  -- Each exp has norm 1 since c*t is purely imaginary
  have h_exp_norm : ∀ u : ℝ, ‖exp (c * ↑u)‖ = 1 := by
    intro u
    rw [Complex.norm_exp]
    have : (c * ↑u).re = 0 := by
      rw [hc_def]
      simp only [neg_mul, mul_re, I_re, I_im, ofReal_re, ofReal_im,
                  neg_re, mul_re, mul_im]
      ring
    rw [this, Real.exp_zero]
  have h_numer_le : ‖exp (c * ↑B) - exp (c * ↑A)‖ ≤ 2 :=
    calc ‖exp (c * ↑B) - exp (c * ↑A)‖
        ≤ ‖exp (c * ↑B)‖ + ‖exp (c * ↑A)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [h_exp_norm B, h_exp_norm A]
      _ = 2 := by norm_num
  exact (div_le_div_iff_of_pos_right (abs_pos.mpr hα_ne)).mpr h_numer_le

/-- Threshold characterization: n ≤ N_t(t) iff t ≥ 2πn² (for n ≥ 1, t ≥ 0). -/
lemma N_t_ge_iff {n : ℕ} (hn : n ≥ 1) {t : ℝ} (ht : t ≥ 0) :
    n ≤ N_t t ↔ 2 * Real.pi * (n : ℝ) ^ 2 ≤ t := by
  simp only [N_t]
  rw [Nat.le_floor_iff (Real.sqrt_nonneg _)]
  have hpi2 : (0 : ℝ) < 2 * Real.pi := by positivity
  constructor
  · intro h
    have hsq := Real.sq_sqrt (div_nonneg ht (le_of_lt hpi2))
    have h1 := pow_le_pow_left₀ (by positivity : (n : ℝ) ≥ 0) h 2
    rw [hsq] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hpi2)
    rwa [mul_div_cancel₀ _ (ne_of_gt hpi2)] at h2
  · intro h
    have h1 : (n : ℝ) ^ 2 ≤ t / (2 * Real.pi) := by
      rw [le_div_iff₀ hpi2]; linarith
    calc (n : ℝ) = Real.sqrt ((n : ℝ) ^ 2) := by
            rw [Real.sqrt_sq (by positivity : (n : ℝ) ≥ 0)]
      _ ≤ Real.sqrt (t / (2 * Real.pi)) := Real.sqrt_le_sqrt h1

/-- Per-pair oscillatory bound with indicator guard.
    The indicator set {t | n ≤ N_t(t) ∧ m ≤ N_t(t)} = [A, ∞) for A = 2π(max n m)²
    by N_t_ge_iff. The indicator integral is therefore ∫_A^T (...), and
    integral_cpow_neg_mul_bound gives the 2/|log(n/m)| bound. -/
lemma norm_integral_indicator_offDiag_le (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) (hnm : n ≠ m)
    (T : ℝ) (hT : T ≥ 1) (hN : max n m ≤ N_t T) :
    ‖∫ t in (1:ℝ)..T, if (n ≤ N_t t ∧ m ≤ N_t t)
        then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) * ((↑n : ℂ) / ↑m) ^ (-(I * ↑t))
        else 0‖ ≤
      (1 / Real.sqrt (↑n * ↑m)) * (2 / |Real.log ((n : ℝ) / m)|) := by
  set K := max n m
  set A := 2 * Real.pi * (K : ℝ) ^ 2
  have hK1 : K ≥ 1 := hn.trans (le_max_left n m)
  have hpi2 : (0 : ℝ) < 2 * Real.pi := by positivity
  -- A ≤ T
  have hA_le_T : A ≤ T := by
    have h1 : (K : ℝ) ≤ (N_t T : ℝ) := by exact_mod_cast hN
    have h2 : (N_t T : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    have h3 : (K : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) := h1.trans h2
    have h4 := pow_le_pow_left₀ (by positivity : (K : ℝ) ≥ 0) h3 2
    rw [Real.sq_sqrt (div_nonneg (by linarith) (le_of_lt hpi2))] at h4
    have := mul_le_mul_of_nonneg_left h4 (le_of_lt hpi2)
    rwa [mul_div_cancel₀ _ (ne_of_gt hpi2)] at this
  -- 1 ≤ A
  have h1A : 1 ≤ A := by
    have : (K : ℝ) ≥ 1 := by exact_mod_cast hK1
    have : (K : ℝ) ^ 2 ≥ 1 := by nlinarith
    nlinarith [Real.pi_gt_three]
  -- Threshold: for t ≥ 0, cond(t) ↔ A ≤ t
  have h_cond : ∀ t : ℝ, t ≥ 0 → ((n ≤ N_t t ∧ m ≤ N_t t) ↔ (A ≤ t)) := by
    intro t ht
    constructor
    · intro ⟨hn_le, hm_le⟩
      -- K = max n m is either n or m
      have h_n := (N_t_ge_iff hn ht).mp hn_le  -- 2πn² ≤ t
      have h_m := (N_t_ge_iff hm ht).mp hm_le  -- 2πm² ≤ t
      show 2 * Real.pi * (K : ℝ) ^ 2 ≤ t
      rcases le_total n m with h | h
      · rw [show (K : ℝ) = (m : ℝ) from by exact_mod_cast max_eq_right h]; exact h_m
      · rw [show (K : ℝ) = (n : ℝ) from by exact_mod_cast max_eq_left h]; exact h_n
    · intro hAt
      constructor
      · apply (N_t_ge_iff hn ht).mpr
        calc 2 * Real.pi * (n : ℝ) ^ 2
            ≤ 2 * Real.pi * (K : ℝ) ^ 2 := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hpi2)
              exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast le_max_left n m) 2
          _ ≤ t := hAt
      · apply (N_t_ge_iff hm ht).mpr
        calc 2 * Real.pi * (m : ℝ) ^ 2
            ≤ 2 * Real.pi * (K : ℝ) ^ 2 := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hpi2)
              exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast le_max_right n m) 2
          _ ≤ t := hAt
  -- Measurability of N_t (for integrability)
  have hN_meas : Measurable N_t :=
    Nat.measurable_floor.comp
      (Real.continuous_sqrt.measurable.comp ((continuous_id.div_const _).measurable))
  -- Integrability on any subinterval (bounded measurable, norm ≤ 1)
  have h_int_sub : ∀ a b : ℝ, IntervalIntegrable (fun t => if (n ≤ N_t t ∧ m ≤ N_t t)
      then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) * ((↑n : ℂ) / ↑m) ^ (-(I * ↑t))
      else 0) volume a b := by
    intro a b
    apply MeasureTheory.IntegrableOn.intervalIntegrable
    refine Measure.integrableOn_of_bounded (M := 1) isCompact_uIcc.measure_lt_top.ne ?_ ?_
    · apply Measurable.aestronglyMeasurable
      exact Measurable.ite
        ((hN_meas measurableSet_Ici).inter (hN_meas measurableSet_Ici))
        (measurable_const.mul
          (((continuous_const.mul continuous_ofReal).neg).const_cpow
            (Or.inl (div_ne_zero
              (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))
              (Nat.cast_ne_zero.mpr (by omega : m ≠ 0))))).measurable)
        measurable_const
    · rw [ae_restrict_iff' measurableSet_uIcc]
      exact ae_of_all _ fun t _ => by
        split_ifs with h
        · rw [norm_mul]
          have hf2 : ‖((↑n : ℂ) / ↑m) ^ (-(I * ↑t))‖ = 1 := by
            conv_lhs => rw [show ((↑n : ℂ) / ↑m) = (((↑n : ℝ) / ↑m : ℝ) : ℂ)
              from by push_cast; ring]
            rw [Complex.norm_cpow_eq_rpow_re_of_pos
              (show (0:ℝ) < (↑n : ℝ) / ↑m by positivity)]
            have : (-(I * (↑t : ℂ))).re = 0 := by
              simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
            rw [this, rpow_zero]
          have hf1 : ‖(↑n * ↑m : ℂ) ^ (-(1 / 2 : ℂ))‖ ≤ 1 := by
            conv_lhs =>
              rw [show (↑n * ↑m : ℂ) = ((↑n * ↑m : ℝ) : ℂ) from by push_cast; ring,
                show (-(1 / 2 : ℂ)) = ((-(1/2) : ℝ) : ℂ) from by push_cast; ring]
            rw [Complex.norm_cpow_eq_rpow_re_of_pos
                (show (0:ℝ) < (↑n : ℝ) * ↑m by positivity),
              Complex.ofReal_re]
            exact rpow_le_one_of_one_le_of_nonpos
              (by exact_mod_cast show 1 ≤ n * m by nlinarith) (by norm_num)
          rw [hf2, mul_one]; exact hf1
        · simp
  -- Step 1: Rewrite condition using h_cond (valid on [1,T] since t ≥ 1 > 0)
  have h_rewrite_cond : ∀ t ∈ Set.uIcc 1 T,
      (if (n ≤ N_t t ∧ m ≤ N_t t)
        then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) * ((↑n : ℂ) / ↑m) ^ (-(I * ↑t))
        else 0) =
      (if (A ≤ t)
        then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) * ((↑n : ℂ) / ↑m) ^ (-(I * ↑t))
        else 0) := by
    intro t ht
    congr 1; ext
    exact h_cond t (by rcases Set.mem_uIcc.mp ht with ⟨h, _⟩ | ⟨_, h⟩ <;> linarith)
  -- Step 2: Split integral at A
  set c := (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) with hc_def
  set g := fun t : ℝ => ((↑n : ℂ) / ↑m) ^ (-(I * ↑t)) with hg_def
  -- Integrability of the A ≤ t version
  have h_int_A : ∀ a b : ℝ, IntervalIntegrable (fun t =>
      if (A ≤ t) then c * g t else 0) volume a b := by
    intro a b
    apply MeasureTheory.IntegrableOn.intervalIntegrable
    refine Measure.integrableOn_of_bounded (M := 1) isCompact_uIcc.measure_lt_top.ne ?_ ?_
    · apply Measurable.aestronglyMeasurable
      exact Measurable.ite measurableSet_Ici
        (measurable_const.mul
          (((continuous_const.mul continuous_ofReal).neg).const_cpow
            (Or.inl (div_ne_zero
              (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))
              (Nat.cast_ne_zero.mpr (by omega : m ≠ 0))))).measurable)
        measurable_const
    · rw [ae_restrict_iff' measurableSet_uIcc]
      exact ae_of_all _ fun t _ => by
        split_ifs with h
        · rw [norm_mul]
          have hf2 : ‖g t‖ = 1 := by
            simp only [hg_def]
            conv_lhs => rw [show ((↑n : ℂ) / ↑m) = (((↑n : ℝ) / ↑m : ℝ) : ℂ)
              from by push_cast; ring]
            rw [Complex.norm_cpow_eq_rpow_re_of_pos
              (show (0:ℝ) < (↑n : ℝ) / ↑m by positivity)]
            have : (-(I * (↑t : ℂ))).re = 0 := by
              simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
            rw [this, rpow_zero]
          have hf1 : ‖c‖ ≤ 1 := by
            simp only [hc_def]
            conv_lhs =>
              rw [show (↑n * ↑m : ℂ) = ((↑n * ↑m : ℝ) : ℂ) from by push_cast; ring,
                show (-(1 / 2 : ℂ)) = ((-(1/2) : ℝ) : ℂ) from by push_cast; ring]
            rw [Complex.norm_cpow_eq_rpow_re_of_pos
                (show (0:ℝ) < (↑n : ℝ) * ↑m by positivity),
              Complex.ofReal_re]
            exact rpow_le_one_of_one_le_of_nonpos
              (by exact_mod_cast show 1 ≤ n * m by nlinarith) (by norm_num)
          rw [hf2, mul_one]; exact hf1
        · simp
  -- Rewrite using h_cond
  calc ‖∫ t in (1:ℝ)..T, if (n ≤ N_t t ∧ m ≤ N_t t) then c * g t else 0‖
      = ‖∫ t in (1:ℝ)..T, if (A ≤ t) then c * g t else 0‖ := by
        congr 1; exact intervalIntegral.integral_congr h_rewrite_cond
    _ = ‖(∫ t in (1:ℝ)..A, if (A ≤ t) then c * g t else 0) +
          (∫ t in A..T, if (A ≤ t) then c * g t else 0)‖ := by
        congr 1
        exact (intervalIntegral.integral_add_adjacent_intervals
          (h_int_A 1 A) (h_int_A A T)).symm
    _ = ‖(∫ t in (1:ℝ)..A, if (A ≤ t) then c * g t else 0) +
          (∫ t in A..T, c * g t)‖ := by
        -- On [A,T], A ≤ t for all t, so the condition is true
        congr 2
        apply intervalIntegral.integral_congr
        intro t ht
        have : A ≤ t := by
          rcases Set.mem_uIcc.mp ht with ⟨h, _⟩ | ⟨_, h⟩ <;> linarith
        simp [this]
    _ = ‖(∫ t in (1:ℝ)..A, if (A ≤ t) then c * g t else 0) +
          c * (∫ t in A..T, g t)‖ := by
        congr 2
        exact intervalIntegral.integral_const_mul c (fun t => g t)
    _ = ‖c * (∫ t in A..T, g t)‖ := by
        -- ∫₁ᴬ = 0: condition false a.e. on (1,A), only true at boundary {A} (measure 0)
        have h_first : ∫ t in (1:ℝ)..A, (if A ≤ t then c * g t else 0) = 0 := by
          -- ae: on uIoc 1 A, integrand is 0 (fails only at {A}, measure 0)
          have h_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc 1 A →
              (if A ≤ t then c * g t else 0) = (0 : ℂ) := by
            apply ae_iff.mpr
            refine measure_mono_null (fun t (ht : ¬_) => ?_) (measure_singleton A)
            push_neg at ht
            obtain ⟨ht_mem, ht_ne⟩ := ht
            simp only [Set.mem_singleton_iff]
            have ht_ioc : t ∈ Set.Ioc 1 A := by rwa [Set.uIoc_of_le h1A] at ht_mem
            have hle : A ≤ t := by
              by_contra h_nle; push_neg at h_nle
              exact ht_ne (by simp [not_le.mpr h_nle])
            exact le_antisymm (Set.mem_Ioc.mp ht_ioc).2 hle
          rw [intervalIntegral.integral_congr_ae h_ae]; simp
        congr 1; rw [h_first, zero_add]
    _ ≤ ‖c‖ * ‖∫ t in A..T, g t‖ := norm_mul_le c _
    _ ≤ (1 / Real.sqrt (↑n * ↑m)) * (2 / |Real.log ((n : ℝ) / m)|) := by
        -- ‖c‖ = 1/√(nm)
        have h_norm_c : ‖c‖ = 1 / Real.sqrt (↑n * ↑m) := by
          simp only [hc_def]
          conv_lhs =>
            rw [show (↑n * ↑m : ℂ) = ((↑n * ↑m : ℝ) : ℂ) from by push_cast; ring,
              show (-(1 / 2 : ℂ)) = ((-(1/2) : ℝ) : ℂ) from by push_cast; ring]
          rw [Complex.norm_cpow_eq_rpow_re_of_pos
              (show (0:ℝ) < (↑n : ℝ) * ↑m by positivity),
            Complex.ofReal_re,
            Real.rpow_neg (by positivity : (↑n * ↑m : ℝ) ≥ 0),
            ← Real.sqrt_eq_rpow, inv_eq_one_div]
        rw [h_norm_c]
        exact mul_le_mul_of_nonneg_left
          (integral_cpow_neg_mul_bound n m hn hm hnm A T) (by positivity)

/-- The off-diagonal integral is bounded by O(N²).
    Each of the O(N²) off-diagonal terms contributes O(1) due to oscillation cancellation,
    giving a total of O(N²) which is o(T log T) since N = √(T/2π). -/
lemma norm_integral_offDiagSsq_le (T : ℝ) (hT : T ≥ 1) :
    ‖∫ t in (1:ℝ)..T, offDiagSsq t‖ ≤ 8 * (N_t T : ℝ)^2 := by
  set N := N_t T with hN_def
  -- N = 0 case: offDiagSsq sums over empty Icc 1 0 = ∅
  by_cases hN0 : N = 0
  · have h0 : ∀ t ∈ Set.uIcc 1 T, offDiagSsq t = 0 := by
      intro t ht
      simp only [offDiagSsq]
      have h_le_T : t ≤ T := by
        rcases Set.mem_uIcc.mp ht with ⟨_, h⟩ | ⟨h1, h2⟩ <;> linarith
      have hNt_le : N_t t ≤ N := by
        exact Nat.floor_mono (Real.sqrt_le_sqrt
          (div_le_div_of_nonneg_right h_le_T (by positivity : (0:ℝ) ≤ 2 * Real.pi)))
      have : N_t t = 0 := by omega
      rw [this]; simp
    rw [intervalIntegral.integral_congr h0]
    simp [Nat.cast_eq_zero.mpr hN0]
  -- N ≥ 1
  push_neg at hN0
  have hN_pos : 0 < N := Nat.pos_of_ne_zero hN0
  have hN_real_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
  -- N_t is monotone: for t ≤ T, N_t t ≤ N
  have hN_mono : ∀ t, t ≤ T → N_t t ≤ N :=
    fun t ht => Nat.floor_mono (Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_right ht (by positivity)))
  -- Step 1: Exchange ∫ and Σ, triangle inequality, per-pair oscillatory bound.
  -- For each pair (n,m) with n≠m, the contribution to ∫₁ᵀ offDiagSsq(t) dt
  -- is an integral over the subinterval where n,m ≤ N_t(t).
  -- By integral_cpow_neg_mul_bound (valid for ANY interval),
  -- each pair contributes at most (nm)^{-1/2} * 2/|log(n/m)| to the norm.
  have h_step1 : ‖∫ t in (1:ℝ)..T, offDiagSsq t‖ ≤
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        if n ≠ m then (1 / Real.sqrt (↑n * ↑m)) *
          (2 / |Real.log ((n : ℝ) / m)|) else 0 := by
    -- Extension: rewrite offDiagSsq as sum over Icc 1 N with indicator guards
    have h_ext : ∀ t ∈ Set.uIcc 1 T, offDiagSsq t =
        ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          if (n ≤ N_t t ∧ m ≤ N_t t ∧ n ≠ m)
          then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) * ((↑n : ℂ) / ↑m) ^ (-(I * ↑t))
          else 0 := by
      intro t ht
      have hle : t ≤ T := by
        rcases Set.mem_uIcc.mp ht with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> linarith
      have hNt_le : N_t t ≤ N := hN_mono t hle
      simp only [offDiagSsq]
      symm
      -- Reduce big sums to small: extra outer terms vanish (n > N_t t)
      rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hNt_le) (fun n hn hn' => by
        have : ¬(n ≤ N_t t) := by simp only [Finset.mem_Icc] at hn hn' ⊢; omega
        exact Finset.sum_eq_zero (fun m _ => by simp [this]))]
      -- For each n ∈ Icc 1 (N_t t), reduce inner sum and simplify conditions
      apply Finset.sum_congr rfl; intro n hn
      have hn_le : n ≤ N_t t := (Finset.mem_Icc.mp hn).2
      rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hNt_le) (fun m hm hm' => by
        have : ¬(m ≤ N_t t) := by simp only [Finset.mem_Icc] at hm hm' ⊢; omega
        simp [this])]
      apply Finset.sum_congr rfl; intro m hm
      have hm_le : m ≤ N_t t := (Finset.mem_Icc.mp hm).2
      simp [hn_le, hm_le]
    -- Integrability of each indicator-guarded summand (bounded measurable on bounded interval)
    have h_int : ∀ n ∈ Finset.Icc 1 N, ∀ m ∈ Finset.Icc 1 N,
        IntervalIntegrable (fun t : ℝ => if (n ≤ N_t t ∧ m ≤ N_t t ∧ n ≠ m)
          then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) * ((↑n : ℂ) / ↑m) ^ (-(I * ↑t))
          else 0) volume 1 T := by
      intro n hn m hm
      have hn1 := (Finset.mem_Icc.mp hn).1
      have hm1 := (Finset.mem_Icc.mp hm).1
      have hN_meas : Measurable N_t :=
        Nat.measurable_floor.comp
          (Real.continuous_sqrt.measurable.comp ((continuous_id.div_const _).measurable))
      -- Bounded measurable on finite-measure interval → integrable
      apply MeasureTheory.IntegrableOn.intervalIntegrable
      refine Measure.integrableOn_of_bounded (M := 1) isCompact_uIcc.measure_lt_top.ne ?_ ?_
      · -- AEStronglyMeasurable: case split on n = m
        apply Measurable.aestronglyMeasurable
        by_cases hnm : n = m
        · -- n = m: function is constantly 0
          have h_eq : (fun t : ℝ => if (n ≤ N_t t ∧ m ≤ N_t t ∧ n ≠ m)
            then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) * ((↑n : ℂ) / ↑m) ^ (-(I * ↑t))
            else 0) = fun _ => (0 : ℂ) := by ext t; simp [hnm]
          rw [h_eq]; exact measurable_const
        · -- n ≠ m: simplify condition, then Measurable.ite
          have h_eq : (fun t : ℝ => if (n ≤ N_t t ∧ m ≤ N_t t ∧ n ≠ m)
            then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) * ((↑n : ℂ) / ↑m) ^ (-(I * ↑t))
            else 0) = fun t => if (n ≤ N_t t ∧ m ≤ N_t t)
            then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) * ((↑n : ℂ) / ↑m) ^ (-(I * ↑t))
            else 0 := by ext t; simp [hnm]
          rw [h_eq]
          exact Measurable.ite
            ((hN_meas measurableSet_Ici).inter (hN_meas measurableSet_Ici))
            (measurable_const.mul
              (((continuous_const.mul continuous_ofReal).neg).const_cpow
                (Or.inl (div_ne_zero
                  (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))
                  (Nat.cast_ne_zero.mpr (by omega : m ≠ 0))))).measurable)
            measurable_const
      · -- Norm bound ≤ 1
        rw [ae_restrict_iff' measurableSet_uIcc]
        exact ae_of_all _ fun t _ => by
          split_ifs with h
          · rw [norm_mul]
            have hf2 : ‖((↑n : ℂ) / ↑m) ^ (-(I * ↑t))‖ = 1 := by
              conv_lhs => rw [show ((↑n : ℂ) / ↑m) = (((↑n : ℝ) / ↑m : ℝ) : ℂ)
                from by push_cast; ring]
              rw [Complex.norm_cpow_eq_rpow_re_of_pos
                (show (0:ℝ) < (↑n : ℝ) / ↑m by positivity)]
              have : (-(I * (↑t : ℂ))).re = 0 := by
                simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                  Complex.ofReal_re, Complex.ofReal_im]
              rw [this, rpow_zero]
            have hf1 : ‖(↑n * ↑m : ℂ) ^ (-(1 / 2 : ℂ))‖ ≤ 1 := by
              conv_lhs =>
                rw [show (↑n * ↑m : ℂ) = ((↑n * ↑m : ℝ) : ℂ) from by push_cast; ring,
                  show (-(1 / 2 : ℂ)) = ((-(1/2) : ℝ) : ℂ) from by push_cast; ring]
              rw [Complex.norm_cpow_eq_rpow_re_of_pos
                  (show (0:ℝ) < (↑n : ℝ) * ↑m by positivity),
                Complex.ofReal_re]
              exact rpow_le_one_of_one_le_of_nonpos
                (by exact_mod_cast show 1 ≤ n * m by nlinarith) (by norm_num)
            rw [hf2, mul_one]; exact hf1
          · simp
    -- Row-sum integrability (converting Pi-sum to pointwise sum via sum_fn)
    have h_int_row : ∀ n ∈ Finset.Icc 1 N,
        IntervalIntegrable (fun t => ∑ m ∈ Finset.Icc 1 N,
          if (n ≤ N_t t ∧ m ≤ N_t t ∧ n ≠ m)
          then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) * ((↑n : ℂ) / ↑m) ^ (-(I * ↑t))
          else 0) volume 1 T := by
      intro n hn
      have := IntervalIntegrable.sum (Finset.Icc 1 N) (fun m hm => h_int n hn m hm)
      rwa [Finset.sum_fn] at this
    -- Exchange integral and double sum
    have h_exchange : ∫ t in (1:ℝ)..T, offDiagSsq t =
        ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          ∫ t in (1:ℝ)..T, (if (n ≤ N_t t ∧ m ≤ N_t t ∧ n ≠ m)
            then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) * ((↑n : ℂ) / ↑m) ^ (-(I * ↑t))
            else 0) := by
      trans ∑ n ∈ Finset.Icc 1 N, ∫ t in (1:ℝ)..T,
          ∑ m ∈ Finset.Icc 1 N,
            if (n ≤ N_t t ∧ m ≤ N_t t ∧ n ≠ m)
            then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) * ((↑n : ℂ) / ↑m) ^ (-(I * ↑t))
            else 0
      · rw [intervalIntegral.integral_congr h_ext]
        exact intervalIntegral.integral_finset_sum h_int_row
      · refine Finset.sum_congr rfl (fun n hn => ?_)
        exact intervalIntegral.integral_finset_sum (fun m hm => h_int n hn m hm)
    -- Triangle inequality + per-pair bound
    rw [h_exchange]
    refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum fun n _ => norm_sum_le _ _) ?_)
    apply Finset.sum_le_sum; intro n hn; apply Finset.sum_le_sum; intro m hm
    by_cases hnm : n = m
    · -- Diagonal: integrand is always 0
      subst hnm; simp
    · -- Off-diagonal: per-pair oscillatory bound
      simp only [Ne, hnm, not_false_eq_true, ite_true, and_true]
      exact norm_integral_indicator_offDiag_le n m
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).1 hnm T hT
        (max_le (Finset.mem_Icc.mp hn).2 (Finset.mem_Icc.mp hm).2)
  -- Step 2: Bound 2/|log(n/m)| ≤ 2N for n,m ∈ Icc 1 N, n ≠ m.
  -- This uses |log(n/m)| ≥ 1/N (from OffDiagonalBound technique).
  have h_step2 : ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      (if n ≠ m then (1 / Real.sqrt (↑n * ↑m)) *
        (2 / |Real.log ((n : ℝ) / m)|) else 0) ≤
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        if n ≠ m then (1 / Real.sqrt (↑n * ↑m)) * (2 * ↑N) else 0 := by
    apply Finset.sum_le_sum; intro n hn
    apply Finset.sum_le_sum; intro m hm
    split_ifs with h
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hn1 : (1 : ℕ) ≤ n := (Finset.mem_Icc.mp hn).1
      have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
      have hm1 : (1 : ℕ) ≤ m := (Finset.mem_Icc.mp hm).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
      have h_ratio_pos : (0 : ℝ) < (n : ℝ) / m := div_pos hn_pos hm_pos
      have h_ratio_ne_one : (n : ℝ) / m ≠ 1 := by
        intro heq; exact h (Nat.cast_injective ((div_eq_one_iff_eq (ne_of_gt hm_pos)).mp heq))
      have hlog_ne : Real.log ((n : ℝ) / m) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one h_ratio_pos h_ratio_ne_one
      rw [div_le_iff₀ (abs_pos.mpr hlog_ne)]
      -- Need: 2 ≤ |log(n/m)| * (2 * N), i.e., |log(n/m)| ≥ 1/N
      -- This follows from |log(n/m)| ≥ 1/max(n,m) ≥ 1/N
      -- |log(n/m)| ≥ 1/N, using log(x) ≥ 1 - 1/x for x > 0
      -- Key: exp(y) ≥ 1 + y for all y, applied to y = -log(x), gives 1/x ≥ 1 - log(x)
      -- Hence log(x) ≥ 1 - 1/x for x > 0.
      -- For n > m: log(n/m) ≥ 1 - m/n ≥ 1/n ≥ 1/N.
      -- For n < m: |log(n/m)| = log(m/n) ≥ 1 - n/m ≥ 1/m ≥ 1/N.
      have log_ge_one_sub_inv : ∀ x : ℝ, x > 0 → Real.log x ≥ 1 - 1/x := by
        intro x hx
        have := Real.add_one_le_exp (-Real.log x)
        rw [Real.exp_neg, Real.exp_log hx] at this
        simp only [inv_eq_one_div] at this
        linarith
      suffices hsuff : 1 / (N : ℝ) ≤ |Real.log ((n : ℝ) / m)| by
        have h4 : 1 ≤ |Real.log ((n : ℝ) / m)| * N := by
          have := mul_le_mul_of_nonneg_right hsuff (Nat.cast_nonneg N)
          rwa [div_mul_cancel₀ _ (ne_of_gt hN_real_pos)] at this
        nlinarith
      rcases lt_or_gt_of_ne h with h_lt | h_gt
      · -- Case n < m
        have hlt : (n : ℝ) < m := by exact_mod_cast h_lt
        rw [abs_of_neg (Real.log_neg (by positivity) ((div_lt_one hm_pos).mpr hlt))]
        rw [← Real.log_inv, inv_div]
        have h1 : Real.log ((m : ℝ) / n) ≥ 1 - (n : ℝ) / m := by
          have := log_ge_one_sub_inv ((m : ℝ) / n) (div_pos hm_pos hn_pos)
          rwa [one_div, inv_div] at this
        have h2 : 1 - (n : ℝ) / m ≥ 1 / (m : ℝ) := by
          rw [ge_iff_le, ← sub_nonneg]
          have hnat : (n : ℝ) + 1 ≤ m := by exact_mod_cast h_lt
          have : 1 - (n : ℝ) / m - 1 / m = (m - n - 1) / m := by field_simp
          rw [this]; exact div_nonneg (by linarith) (le_of_lt hm_pos)
        have h3 : (1 : ℝ) / N ≤ 1 / m :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hmN)
        linarith
      · -- Case n > m
        have hgt : (m : ℝ) < n := by exact_mod_cast h_gt
        rw [abs_of_pos (Real.log_pos ((one_lt_div hm_pos).mpr hgt))]
        have h1 : Real.log ((n : ℝ) / m) ≥ 1 - (m : ℝ) / n := by
          have := log_ge_one_sub_inv ((n : ℝ) / m) (div_pos hn_pos hm_pos)
          rwa [one_div, inv_div] at this
        have h2 : 1 - (m : ℝ) / n ≥ 1 / (n : ℝ) := by
          rw [ge_iff_le, ← sub_nonneg]
          have hnat : (m : ℝ) + 1 ≤ n := by exact_mod_cast h_gt
          have : 1 - (m : ℝ) / n - 1 / n = (n - m - 1) / n := by field_simp
          rw [this]; exact div_nonneg (by linarith) (le_of_lt hn_pos)
        have h3 : (1 : ℝ) / N ≤ 1 / n :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hnN)
        linarith
    · exact le_refl _
  -- Step 3: Sum bound. Factor out 2N, use Σ 1/√(nm) ≤ (Σ 1/√n)² ≤ (2√N)² = 4N.
  -- Total: 4N * 2N = 8N².
  have h_step3 : ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      (if n ≠ m then (1 / Real.sqrt (↑n * ↑m)) * (2 * ↑N) else 0) ≤
      8 * (N : ℝ) ^ 2 := by
    -- Σ_{n≠m} 1/√(nm) * 2N ≤ (2√N)² * 2N = 8N²
    -- Proof: drop n≠m, factor 1/√(nm) = (1/√n)(1/√m), use Σ 1/√n ≤ 2√N.
    -- Adapted from OffDiagonalBound.norm_integral_offDiagSsqReal_le.
    -- Σ 1/√n ≤ 2√N (by induction, same technique as OffDiagonalBound)
    have h_sqrt_sum : ∑ n ∈ Finset.Icc 1 N, (1 / Real.sqrt (↑n : ℝ)) ≤ 2 * Real.sqrt ↑N := by
      induction' N with N ih <;>
        norm_num [Finset.sum_Ioc_succ_top,
          (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)] at *
      nlinarith [sq_nonneg (Real.sqrt (N : ℝ) - Real.sqrt (↑N + 1)),
        Real.mul_self_sqrt (show (N : ℝ) ≥ 0 by positivity),
        Real.mul_self_sqrt (show (↑N + 1 : ℝ) ≥ 0 by positivity),
        inv_pos.2 (Real.sqrt_pos.2 (show (↑N + 1 : ℝ) > 0 by positivity)),
        mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (show (↑N + 1 : ℝ) > 0 by positivity)))]
    -- Bound each inner sum, then outer sum
    have h_inner_bound : ∀ n ∈ Finset.Icc 1 N,
        ∑ m ∈ Finset.Icc 1 N,
          (if n ≠ m then (1 / Real.sqrt (↑n * ↑m)) * (2 * ↑N) else 0) ≤
        (1 / Real.sqrt ↑n) * (2 * ↑N) * (2 * Real.sqrt ↑N) := by
      intro n hn
      calc ∑ m ∈ Finset.Icc 1 N,
              (if n ≠ m then (1 / Real.sqrt (↑n * ↑m)) * (2 * ↑N) else 0)
          ≤ ∑ m ∈ Finset.Icc 1 N, (1 / Real.sqrt (↑n * ↑m)) * (2 * ↑N) := by
            apply Finset.sum_le_sum; intro m _; split_ifs <;> [exact le_refl _; positivity]
        _ = (1 / Real.sqrt ↑n) * (2 * ↑N) * ∑ m ∈ Finset.Icc 1 N, 1 / Real.sqrt ↑m := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun m _ => ?_)
            rw [show (1 : ℝ) / Real.sqrt (↑n * ↑m) =
                (1 / Real.sqrt ↑n) * (1 / Real.sqrt ↑m) from by
              rw [Real.sqrt_mul (Nat.cast_nonneg n)]; ring]
            ring
        _ ≤ (1 / Real.sqrt ↑n) * (2 * ↑N) * (2 * Real.sqrt ↑N) := by
            apply mul_le_mul_of_nonneg_left h_sqrt_sum (by positivity)
    calc _ ≤ ∑ n ∈ Finset.Icc 1 N,
              (1 / Real.sqrt ↑n) * (2 * ↑N) * (2 * Real.sqrt ↑N) :=
            Finset.sum_le_sum h_inner_bound
      _ = (2 * ↑N) * (2 * Real.sqrt ↑N) *
            ∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt ↑n := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun n _ => ?_); ring
      _ ≤ (2 * ↑N) * (2 * Real.sqrt ↑N) * (2 * Real.sqrt ↑N) := by
          apply mul_le_mul_of_nonneg_left h_sqrt_sum (by positivity)
      _ = 8 * (↑N) ^ 2 := by
          nlinarith [Real.mul_self_sqrt (show (↑N : ℝ) ≥ 0 from Nat.cast_nonneg N)]
  linarith

/-- offDiagSsq is IntervalIntegrable on any bounded interval.
    On [a,b], N_t takes finitely many values, so offDiagSsq is piecewise
    continuous (continuous on each subinterval where N_t is constant).
    Combined with a pointwise norm bound, this gives integrability. -/
lemma offDiagSsq_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable offDiagSsq volume a b := by
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  -- N_t is measurable (Nat.floor ∘ sqrt ∘ linear)
  have hN_meas : Measurable N_t :=
    Nat.measurable_floor.comp
      (Real.continuous_sqrt.measurable.comp ((continuous_id.div_const _).measurable))
  -- offDiagSsq is measurable: pointwise limit of measurable approximations.
  -- F N t sums over k ∈ range(N+1), using indicator on {N_t = k}.
  -- For N ≥ N_t t, F N t = offDiagSsq t, so convergence is eventual equality.
  have h_meas : Measurable offDiagSsq := by
    apply measurable_of_tendsto_metrizable
      (f := fun N t => ∑ k ∈ Finset.range (N + 1),
        if N_t t = k then
          ∑ n ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc 1 k,
            if n ≠ m then (n * m : ℂ) ^ (-(1/2 : ℂ)) * ((n : ℂ) / m) ^ (-(I * ↑t))
            else 0
        else 0)
    · -- Each F N is measurable (finite sum of indicator * continuous)
      intro N
      apply Finset.measurable_sum; intro k _
      apply Measurable.ite (hN_meas (measurableSet_singleton k))
      · apply Finset.measurable_sum; intro n hn
        apply Finset.measurable_sum; intro m hm
        by_cases hnm : n = m
        · simp only [hnm, ne_eq, not_true, ite_false]; exact measurable_const
        · simp only [ne_eq, hnm, not_false_eq_true, ite_true]
          have hn1 : (n : ℕ) ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
          have hm1 : (m : ℕ) ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
          exact measurable_const.mul
            (((continuous_const.mul continuous_ofReal).neg).const_cpow
              (Or.inl (div_ne_zero
                (Nat.cast_ne_zero.mpr hn1)
                (Nat.cast_ne_zero.mpr hm1)))).measurable
      · exact measurable_const
    · -- Pointwise convergence: for each t, F N t = offDiagSsq t for large N
      rw [tendsto_pi_nhds]; intro t
      apply Filter.Tendsto.congr
      · intro N; rfl
      · apply tendsto_const_nhds.congr'
        filter_upwards [Filter.eventually_ge_atTop (N_t t)] with N hN
        show offDiagSsq t = _
        simp only [offDiagSsq]
        -- RHS: ∑ k ∈ range(N+1), if N_t t = k then (sum for k) else 0
        -- Since N_t t ≤ N, N_t t ∈ range(N+1), so sum picks out k = N_t t.
        symm
        rw [Finset.sum_ite_eq]
        simp [Finset.mem_range.mpr (Nat.lt_succ_of_le hN)]
  -- Norm bound on [[a,b]]: each term ≤ 1, at most N_t(t)² terms, N_t bounded on interval
  refine Measure.integrableOn_of_bounded (M := (max |a| |b| + 1) ^ 2)
    isCompact_uIcc.measure_lt_top.ne h_meas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_uIcc]
  exact ae_of_all _ fun t ht => by
    -- Split: ‖offDiagSsq t‖ ≤ N_t(t)² ≤ (max|a||b|+1)²
    -- Part A: N_t(t) ≤ max|a||b| + 1 for t ∈ [[a,b]]
    have hNt : (N_t t : ℝ) ≤ max |a| |b| + 1 := by
      unfold N_t
      -- Get t ≤ max |a| |b| from membership in [[a,b]]
      have h_t_le : t ≤ max |a| |b| := by
        rcases Set.mem_uIcc.mp ht with ⟨_, h⟩ | ⟨_, h⟩
        · linarith [le_abs_self b, le_max_right |a| |b|]
        · linarith [le_abs_self a, le_max_left |a| |b|]
      have hpi : (0:ℝ) < 2 * Real.pi := by linarith [Real.two_pi_pos]
      have hM_nn : (0:ℝ) ≤ max |a| |b| := le_max_of_le_left (abs_nonneg a)
      -- ⌊√(t/2π)⌋ ≤ √(t/2π) ≤ √(max|a||b|) ≤ max|a||b| + 1
      calc (↑⌊Real.sqrt (t / (2 * Real.pi))⌋₊ : ℝ)
          ≤ Real.sqrt (t / (2 * Real.pi)) := Nat.floor_le (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt (max |a| |b|) := by
            apply Real.sqrt_le_sqrt
            -- t / (2π) ≤ max|a||b|: when t ≤ 0, LHS ≤ 0; when t > 0, LHS ≤ t ≤ max|a||b|
            by_cases ht0 : t ≤ 0
            · linarith [div_nonpos_of_nonpos_of_nonneg ht0 hpi.le]
            · push_neg at ht0
              have h1 : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
              exact le_trans (div_le_self ht0.le h1) h_t_le
        _ ≤ max |a| |b| + 1 := by
            nlinarith [Real.sq_sqrt hM_nn, Real.sqrt_nonneg (max |a| |b|)]
    -- Part B: ‖offDiagSsq t‖ ≤ N_t(t)² (each term has norm ≤ 1, at most N_t² terms)
    have hbound : ‖offDiagSsq t‖ ≤ (N_t t : ℝ) ^ 2 := by
      simp only [offDiagSsq]; set N := N_t t
      -- Each off-diagonal term has norm ≤ 1
      have h_term_le : ∀ n ∈ Finset.Icc 1 N, ∀ m ∈ Finset.Icc 1 N,
          ‖if n ≠ m then (↑n * ↑m : ℂ) ^ (-(1 / 2 : ℂ)) *
            ((↑n : ℂ) / ↑m) ^ (-(I * ↑t)) else 0‖ ≤ 1 := by
        intro n hn m hm
        split_ifs with h
        · have hn1 := (Finset.mem_Icc.mp hn).1
          have hm1 := (Finset.mem_Icc.mp hm).1
          rw [norm_mul]
          -- ‖(n/m)^{-it}‖ = 1 (purely imaginary exponent, positive real base)
          have hf2 : ‖((↑n : ℂ) / ↑m) ^ (-(I * ↑t))‖ = 1 := by
            conv_lhs => rw [show ((↑n : ℂ) / ↑m) = (((↑n : ℝ) / ↑m : ℝ) : ℂ)
              from by push_cast; ring]
            rw [Complex.norm_cpow_eq_rpow_re_of_pos
              (show (0:ℝ) < (↑n : ℝ) / ↑m by positivity)]
            have : (-(I * (↑t : ℂ))).re = 0 := by
              simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
            rw [this, rpow_zero]
          -- ‖(nm)^{-1/2}‖ ≤ 1 (base ≥ 1, negative real exponent)
          have hf1 : ‖(↑n * ↑m : ℂ) ^ (-(1 / 2 : ℂ))‖ ≤ 1 := by
            conv_lhs =>
              rw [show (↑n * ↑m : ℂ) = ((↑n * ↑m : ℝ) : ℂ) from by push_cast; ring,
                show (-(1 / 2 : ℂ)) = ((-(1/2) : ℝ) : ℂ) from by push_cast; ring]
            rw [Complex.norm_cpow_eq_rpow_re_of_pos
                (show (0:ℝ) < (↑n : ℝ) * ↑m by positivity),
              Complex.ofReal_re]
            exact rpow_le_one_of_one_le_of_nonpos
              (by exact_mod_cast show 1 ≤ n * m by nlinarith) (by norm_num)
          rw [hf2, mul_one]; exact hf1
        · simp
      -- Triangle inequality twice, then bound each term by 1
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum fun n hn => norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum fun n hn =>
        Finset.sum_le_sum fun m hm => h_term_le n hn m hm) ?_
      -- ∑∑ 1 = N²
      have : ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) = (N : ℝ) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
          Nat.card_Icc, Nat.add_sub_cancel]
        push_cast; ring
      linarith
    -- Combine
    calc ‖offDiagSsq t‖ ≤ (N_t t : ℝ) ^ 2 := hbound
      _ ≤ (max |a| |b| + 1) ^ 2 := by nlinarith

/-- Decomposition: |S|² = diagonal + off-diagonal.
    |Σ_{n≤N} n^{-1/2-it}|² = Σ_n |n^{-1/2-it}|² + Σ_{n≠m} (nm)^{-1/2} (n/m)^{-it}
                          = Σ_n 1/n + (off-diagonal terms) -/
lemma normSq_partialZeta_eq (t : ℝ) :
    Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + I * t)) =
    (∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) + (offDiagSsq t).re := by
  unfold partialZeta offDiagSsq N_t
  set N := Nat.floor (Real.sqrt (t / (2 * Real.pi))) with hN_def
  set S := Finset.Icc 1 N with hS_def
  set s : ℂ := 1/2 + I * ↑t with hs_def
  -- Key helper: each (n,m) term decomposes into diagonal + off-diagonal
  have h_term : ∀ n ∈ S, ∀ m ∈ S,
      (n : ℂ) ^ (-s) * starRingEnd ℂ ((m : ℂ) ^ (-s)) =
      (if n = m then (↑((1:ℝ)/↑n) : ℂ) else 0) +
      (if n ≠ m then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) *
        ((↑n : ℂ) / ↑m) ^ (-(I * ↑t)) else 0) := by
    intro n hn m hm
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    by_cases h : n = m
    · subst h; simp
      -- Goal: (n : ℂ) ^ (-s) * starRingEnd ℂ ((n : ℂ) ^ (-s)) = (n : ℂ)⁻¹
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      -- mul_conj + normSq = ‖·‖² + norm of cpow for positive real base
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
        show (n : ℂ) = ((n : ℝ) : ℂ) from by norm_cast,
        Complex.norm_cpow_eq_rpow_re_of_pos hn_pos, ← Complex.ofReal_inv]
      congr 1
      -- ℝ goal: ((n:ℝ) ^ (-s).re) ^ 2 = (n:ℝ)⁻¹
      have h_re : (-s).re = -(1 / 2 : ℝ) := by
        simp only [hs_def, Complex.neg_re, Complex.add_re, Complex.div_ofNat_re,
          Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [h_re, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (le_of_lt hn_pos),
        show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -(1 : ℝ) from by push_cast; ring,
        Real.rpow_neg (le_of_lt hn_pos), Real.rpow_one]
    · simp [h]
      -- Off-diagonal: n^(-s) * conj(m^(-s)) = (nm)^(-1/2) * (n/m)^(-it)
      -- Strategy: expand all via exp/log, reduce to ring identity on exponents
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) from by norm_cast,
          show (m : ℂ) = ((m : ℝ) : ℂ) from by norm_cast]
      have hn' : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hn_pos)
      have hm' : ((m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hm_pos)
      -- Expand all cpow to exp(log * exponent)
      rw [Complex.cpow_def_of_ne_zero hn',
          Complex.cpow_def_of_ne_zero (mul_ne_zero hn' hm'),
          Complex.cpow_def_of_ne_zero (div_ne_zero hn' hm')]
      conv_lhs =>
        rw [Complex.cpow_def_of_ne_zero hm']
        rw [← Complex.exp_conj]
      -- Combine exp products: exp(a)*exp(b) = exp(a+b)
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      -- Exponent identity: log(n)*(-s) + conj(log(m)*(-s)) = log(nm)*(-1/2) + log(n/m)*(-(I*t))
      -- Express all logs as ofReal of Real.log
      rw [show Complex.log ((n : ℝ) : ℂ) = ↑(Real.log (n : ℝ)) from
            (Complex.ofReal_log (le_of_lt hn_pos)).symm,
          show Complex.log ((m : ℝ) : ℂ) = ↑(Real.log (m : ℝ)) from
            (Complex.ofReal_log (le_of_lt hm_pos)).symm,
          show Complex.log (((n : ℝ) : ℂ) * ((m : ℝ) : ℂ)) = ↑(Real.log (n : ℝ) + Real.log (m : ℝ)) from by
            rw [← Complex.ofReal_mul, ← Complex.ofReal_log (mul_nonneg (le_of_lt hn_pos) (le_of_lt hm_pos)),
                Real.log_mul (ne_of_gt hn_pos) (ne_of_gt hm_pos)],
          show Complex.log (((n : ℝ) : ℂ) / ((m : ℝ) : ℂ)) = ↑(Real.log (n : ℝ) - Real.log (m : ℝ)) from by
            rw [← Complex.ofReal_div, ← Complex.ofReal_log (le_of_lt (div_pos hn_pos hm_pos)),
                Real.log_div (ne_of_gt hn_pos) (ne_of_gt hm_pos)]]
      -- Distribute conj over multiplication and negation
      rw [map_mul (starRingEnd ℂ), map_neg (starRingEnd ℂ)]
      -- conj(↑(Real.log m)) = ↑(Real.log m) since it's real
      rw [show starRingEnd ℂ (↑(Real.log (m : ℝ)) : ℂ) = ↑(Real.log (m : ℝ)) from
            Complex.conj_ofReal _]
      -- conj(s) = 1/2 - I*t
      rw [show starRingEnd ℂ s = 1/2 - I * ↑t from by
            simp only [hs_def, map_add, map_mul, map_div₀, map_one, map_ofNat,
              Complex.conj_I, Complex.conj_ofReal]
            ring]
      -- Now all terms are in ℂ-algebra form. Set variables for ring.
      set a := (↑(Real.log (n : ℝ)) : ℂ)
      set b := (↑(Real.log (m : ℝ)) : ℂ)
      -- Push ↑(x+y) to ↑x + ↑y and ↑(x-y) to ↑x - ↑y
      rw [Complex.ofReal_add, Complex.ofReal_sub]
      ring
  -- Step 1: normSq = Re of double sum
  have h_normSq : Complex.normSq (∑ n ∈ S, (n : ℂ) ^ (-s)) =
      (∑ n ∈ S, ∑ m ∈ S, (n : ℂ) ^ (-s) * starRingEnd ℂ ((m : ℂ) ^ (-s))).re := by
    have : Complex.normSq (∑ n ∈ S, (n : ℂ) ^ (-s)) =
        ((∑ n ∈ S, (n : ℂ) ^ (-s)) * starRingEnd ℂ (∑ n ∈ S, (n : ℂ) ^ (-s))).re := by
      rw [Complex.mul_conj, Complex.ofReal_re]
    rw [this, map_sum (starRingEnd ℂ), Finset.sum_mul]; simp_rw [Finset.mul_sum]
  rw [h_normSq]
  -- Step 2: Rewrite each term, then split into diagonal + off-diagonal sums
  have h_rewrite : (∑ n ∈ S, ∑ m ∈ S,
      (n : ℂ) ^ (-s) * starRingEnd ℂ ((m : ℂ) ^ (-s))) =
      (∑ n ∈ S, ∑ m ∈ S, (if n = m then (↑((1:ℝ)/↑n) : ℂ) else 0)) +
      (∑ n ∈ S, ∑ m ∈ S,
        (if n ≠ m then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) *
          ((↑n : ℂ) / ↑m) ^ (-(I * ↑t)) else 0)) := by
    have h_eq : (∑ n ∈ S, ∑ m ∈ S,
        (n : ℂ) ^ (-s) * starRingEnd ℂ ((m : ℂ) ^ (-s))) =
        ∑ n ∈ S, ∑ m ∈ S, ((if n = m then (↑((1:ℝ)/↑n) : ℂ) else 0) +
          (if n ≠ m then (↑n * ↑m : ℂ) ^ (-(1/2 : ℂ)) *
            ((↑n : ℂ) / ↑m) ^ (-(I * ↑t)) else 0)) := by
      apply Finset.sum_congr rfl; intro n hn
      apply Finset.sum_congr rfl; intro m hm
      exact h_term n hn m hm
    rw [h_eq]; simp_rw [Finset.sum_add_distrib]
  rw [h_rewrite, Complex.add_re]
  congr 1
  · -- Diagonal: Re(∑∑ if n=m then ↑(1/n) else 0) = ∑ 1/n
    have h_diag : (∑ n ∈ S, ∑ m ∈ S, (if n = m then (↑((1:ℝ)/↑n) : ℂ) else 0)) =
        ∑ n ∈ S, (↑((1:ℝ)/↑n) : ℂ) := by
      apply Finset.sum_congr rfl; intro n hn
      simp [Finset.sum_ite_eq', hn]
    rw [h_diag, Complex.re_sum]
    apply Finset.sum_congr rfl; intro n hn
    exact Complex.ofReal_re _

/-- MAIN RESULT: Mean square of partial zeta on critical line.
    ∫₁ᵀ |S(1/2+it)|² dt = ∫₁ᵀ (Σ 1/n + off-diagonal) dt
                        = ∫₁ᵀ H_{N(t)} dt + o(T log T)
                        = Θ(T log T)
    This is the foundation for proving Z(t) changes sign. -/
theorem mean_square_partial_zeta_asymp :
    (fun T => ∫ t in (1:ℝ)..T, Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + I * t)))
    =Θ[atTop] (fun T => T * Real.log T) := by
  -- Step 1: Rewrite integrand using normSq decomposition
  have h_eq : ∀ t, Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + I * t)) =
    (∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) + (offDiagSsq t).re := normSq_partialZeta_eq
  simp_rw [h_eq]
  -- Step 2: Harmonic sum is IntervalIntegrable via monotonicity
  -- (same technique as HarmonicSumIntegral.lean line 175)
  have h_diag_int : ∀ T : ℝ, IntervalIntegrable
      (fun t => ∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) volume 1 T := by
    intro T; apply MonotoneOn.intervalIntegrable
    intro t _ u _ htu
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (Nat.floor_mono (Real.sqrt_le_sqrt
        (div_le_div_of_nonneg_right htu (by positivity)))))
      (fun _ _ _ => by positivity)
  -- Step 3: Off-diagonal Re part is IntervalIntegrable
  -- (bounded piecewise continuous on finite interval; each piece has fixed N_t hence continuous)
  have h_offdiag_int : ∀ T : ℝ, IntervalIntegrable
      (fun t => (offDiagSsq t).re) volume 1 T := by
    intro T
    exact ⟨Complex.reCLM.integrable_comp (offDiagSsq_intervalIntegrable 1 T).1,
           Complex.reCLM.integrable_comp (offDiagSsq_intervalIntegrable 1 T).2⟩
  -- Step 4: Split the integral of sum into sum of integrals
  have h_split : (fun T => ∫ t in (1:ℝ)..T, ((∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) + (offDiagSsq t).re)) =
      (fun T => ∫ t in (1:ℝ)..T, ∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) +
      (fun T => ∫ t in (1:ℝ)..T, (offDiagSsq t).re) := by
    ext T; simp only [Pi.add_apply]
    exact intervalIntegral.integral_add (h_diag_int T) (h_offdiag_int T)
  rw [h_split]
  -- Step 5: Diagonal integral =Θ(T log T), off-diagonal =o(T log T)
  exact integral_harmonic_sum_asymp.add_isLittleO (
    -- Off-diagonal integral is O(T) hence o(T log T)
    -- Key chain: |∫ Re(offDiag)| ≤ ‖∫ offDiag‖ ≤ 8·N_t(T)² ≤ 8T
    (Asymptotics.IsBigO.of_bound 8 (by
      filter_upwards [Filter.eventually_ge_atTop 1] with T hT
      -- Goal: ‖∫₁ᵀ Re(offDiagSsq)‖ ≤ 8 * ‖T‖
      -- Chain: |∫ Re(f)| = |Re(∫ f)| ≤ ‖∫ f‖ ≤ 8·N² ≤ 8T
      have h_int := offDiagSsq_intervalIntegrable 1 T
      -- Re-integral interchange: ∫ Re(f) = Re(∫ f)
      have h_re_eq : ∫ t in (1:ℝ)..T, (offDiagSsq t).re =
          (∫ t in (1:ℝ)..T, offDiagSsq t).re :=
        Complex.reCLM.intervalIntegral_comp_comm h_int
      -- N_t(T)² ≤ T
      have h_N_sq : (N_t T : ℝ)^2 ≤ T := by
        have h1 : (N_t T : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) :=
          Nat.floor_le (Real.sqrt_nonneg _)
        have h2 := Real.sq_sqrt (show (0:ℝ) ≤ T / (2 * Real.pi) by positivity)
        have h4 : (N_t T : ℝ)^2 ≤ Real.sqrt (T / (2 * Real.pi)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
        linarith [show T / (2 * Real.pi) ≤ T from
          div_le_self (by linarith) (by nlinarith [Real.pi_gt_three])]
      simp only [Real.norm_eq_abs]
      rw [h_re_eq]
      calc |(∫ t in (1:ℝ)..T, offDiagSsq t).re|
          ≤ ‖∫ t in (1:ℝ)..T, offDiagSsq t‖ := abs_re_le_norm _
        _ ≤ 8 * (N_t T : ℝ)^2 := norm_integral_offDiagSsq_le T hT
        _ ≤ 8 * |T| := by nlinarith [abs_of_nonneg (show (0:ℝ) ≤ T by linarith)]
    )).trans_isLittleO T_isLittleO_T_log_T)

end
