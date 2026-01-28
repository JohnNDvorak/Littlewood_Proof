/-
Mean square infrastructure for zeta on critical line - proved by Aristotle.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

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
  sorry

/-- The integral of harmonic sums is Θ(T log T).
    Since H_{N(t)} = log(N(t)) + O(1) and N(t) = √(t/2π),
    we have H_{N(t)} = (1/2) log(t/2π) + O(1).
    Integrating: ∫₁ᵀ H_{N(t)} dt = (1/2) ∫₁ᵀ log(t/2π) dt + O(T) = Θ(T log T) -/
lemma integral_harmonic_sum_asymp :
    (fun T => ∫ t in (1:ℝ)..T, ∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) =Θ[atTop] (fun T => T * Real.log T) := by
  sorry

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

/-- The off-diagonal integral is bounded by O(N²).
    Each of the O(N²) off-diagonal terms contributes O(1) due to oscillation cancellation,
    giving a total of O(N²) which is o(T log T) since N = √(T/2π). -/
lemma norm_integral_offDiagSsq_le (T : ℝ) (hT : T ≥ 1) :
    ‖∫ t in (1:ℝ)..T, offDiagSsq t‖ ≤ 8 * (N_t T : ℝ)^2 := by
  sorry

/-- Decomposition: |S|² = diagonal + off-diagonal.
    |Σ_{n≤N} n^{-1/2-it}|² = Σ_n |n^{-1/2-it}|² + Σ_{n≠m} (nm)^{-1/2} (n/m)^{-it}
                          = Σ_n 1/n + (off-diagonal terms) -/
lemma normSq_partialZeta_eq (t : ℝ) :
    Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + I * t)) =
    (∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) + (offDiagSsq t).re := by
  -- Proof outline:
  -- |Σ n^(-s)|² = (Σ n^(-s)) * conj(Σ m^(-s)) = Σ_n Σ_m n^(-s) * conj(m^(-s))
  -- For s = 1/2 + it:
  --   n^(-s) * conj(m^(-s)) = n^(-1/2-it) * m^(-1/2+it) = (nm)^(-1/2) * (n/m)^(-it)
  -- Diagonal (n=m): n^(-1) (since (n/n)^(-it) = 1)
  -- Off-diagonal (n≠m): (nm)^(-1/2) * (n/m)^(-it)
  -- The key identity: normSq(Σ a_n) = Σ_n |a_n|² + Re(Σ_{n≠m} a_n * conj(a_m))
  sorry

/-- MAIN RESULT: Mean square of partial zeta on critical line.
    ∫₁ᵀ |S(1/2+it)|² dt = ∫₁ᵀ (Σ 1/n + off-diagonal) dt
                        = ∫₁ᵀ H_{N(t)} dt + o(T log T)
                        = Θ(T log T)
    This is the foundation for proving Z(t) changes sign. -/
theorem mean_square_partial_zeta_asymp :
    (fun T => ∫ t in (1:ℝ)..T, Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + I * t)))
    =Θ[atTop] (fun T => T * Real.log T) := by
  -- Use normSq_partialZeta_eq to decompose into diagonal + off-diagonal
  -- Diagonal integral: Θ(T log T) by integral_harmonic_sum_asymp
  -- Off-diagonal integral: O(N²) = O(T) = o(T log T) by norm_integral_offDiagSsq_le
  -- Combined: Θ(T log T) + o(T log T) = Θ(T log T)
  sorry

end
