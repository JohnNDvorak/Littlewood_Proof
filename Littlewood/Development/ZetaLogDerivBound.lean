/-
Background Subtraction for ζ'/ζ via the ξ-Hadamard Reduction

## Strategy

The Hadamard product for ξ(s) gives a partial fraction for ζ'/ζ(s).
This file proves the constructive part of that reduction:
  (A) Pole: |1/(s-1)| ≤ 1/|t| ≤ 1/2 — absorbed into C·(log|t|)²
  (B) Background: B₀ + Γ terms — O(log|t|) — absorbed into C·(log|t|)²
  (C) Zero sum / Hadamard remainder: isolated as an explicit zero-avoiding
      analytic hypothesis boundary

The global pointwise theorem for `-ζ'/ζ` is not exported here because it is
singular at zeros. What remains after the constructive background subtraction is
an honest zero-avoiding strip bound on the ξ-Hadamard remainder.

## References

- Titchmarsh, "Theory of the Riemann Zeta Function", §§2.12, 9.6.1
- Davenport, "Multiplicative Number Theory", Chapter 12

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Littlewood.Aristotle.DigammaAsymptotic
import Littlewood.Aristotle.RiemannXiEntire
import Littlewood.Aristotle.Standalone.HadamardFactorizationXi
import Littlewood.Aristotle.Standalone.RvMSubLemmas
import Littlewood.Development.PerronContourShift
import Littlewood.ZetaZeros.RvMRightEdge

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Littlewood.Development.ZetaLogDerivBound

open Complex Real Set MeasureTheory Topology Filter

/-! ## Section 1: Pole Contribution Bounds -/

/-- For σ ∈ [1/2, 2] and |t| ≥ 2: ‖s - 1‖ ≥ |t|. -/
theorem norm_s_sub_one_ge_abs_t (σ t : ℝ) (_ht : 2 ≤ |t|) :
    |t| ≤ ‖(↑σ + ↑t * I : ℂ) - 1‖ := by
  have h1 : (↑σ + ↑t * I : ℂ) - 1 = ↑(σ - 1) + ↑t * I := by push_cast; ring
  rw [h1, Complex.norm_add_mul_I]
  calc |t| = Real.sqrt (t ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt ((σ - 1) ^ 2 + t ^ 2) :=
        Real.sqrt_le_sqrt (by linarith [sq_nonneg (σ - 1)])

/-- Pole bound: |1/(s-1)| ≤ 1/2 for |t| ≥ 2. -/
theorem pole_bound (σ t : ℝ) (ht : 2 ≤ |t|) :
    ‖((↑σ + ↑t * I : ℂ) - 1)⁻¹‖ ≤ 1 / 2 := by
  rw [norm_inv]
  have h_ge := norm_s_sub_one_ge_abs_t σ t ht
  have h_pos : 0 < ‖(↑σ + ↑t * I : ℂ) - 1‖ := by linarith
  rw [inv_le_comm₀ h_pos (by positivity)]
  linarith

/-! ## Section 2: Logarithmic Bounds -/

/-- For |t| ≥ 2: 0 < log|t|. -/
theorem log_abs_t_pos (t : ℝ) (ht : 2 ≤ |t|) : 0 < Real.log |t| :=
  Real.log_pos (by linarith)

/-- For |t| ≥ 2: log 2 ≤ log|t|. -/
theorem log_two_le_log_abs_t (t : ℝ) (ht : 2 ≤ |t|) :
    Real.log 2 ≤ Real.log |t| :=
  Real.log_le_log (by norm_num) (by linarith)

/-- For |t| ≥ 2: the constant 1 is absorbed by C/(log2)² · (log|t|)². -/
theorem one_le_const_times_log_sq (t : ℝ) (ht : 2 ≤ |t|) :
    (1 : ℝ) ≤ 1 / (Real.log 2) ^ 2 * (Real.log |t|) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_t : Real.log 2 ≤ Real.log |t| := log_two_le_log_abs_t t ht
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (sq_pos_of_pos hlog2)]
  nlinarith [sq_nonneg (Real.log |t| - Real.log 2)]

/-- For |t| ≥ 2: log|t| ≤ (1/(log2)) · (log|t|)². -/
theorem log_le_const_times_log_sq (t : ℝ) (ht : 2 ≤ |t|) :
    Real.log |t| ≤ 1 / Real.log 2 * (Real.log |t|) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_t : Real.log 2 ≤ Real.log |t| := log_two_le_log_abs_t t ht
  have hlog_pos : 0 < Real.log |t| := log_abs_t_pos t ht
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hlog2]
  calc Real.log |t| * Real.log 2
      ≤ Real.log |t| * Real.log |t| :=
        mul_le_mul_of_nonneg_left hlog_t hlog_pos.le
    _ = (Real.log |t|) ^ 2 := (sq _).symm

/-! ## Section 2A: Easy Background Bounds -/

/-- For any `σ,t`, the norm of `σ+it` dominates `|t|`. -/
theorem norm_s_ge_abs_t (σ t : ℝ) :
    |t| ≤ ‖(↑σ + ↑t * I : ℂ)‖ := by
  rw [Complex.norm_add_mul_I]
  calc |t| = Real.sqrt (t ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (σ ^ 2 + t ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg σ])

/-- For `|t| ≥ 2`, the reciprocal `1/(σ+it)` is bounded by `1/2`. -/
theorem inv_s_bound (σ t : ℝ) (ht : 2 ≤ |t|) :
    ‖((↑σ + ↑t * I : ℂ))⁻¹‖ ≤ 1 / 2 := by
  rw [norm_inv]
  have h_ge := norm_s_ge_abs_t σ t
  have h_pos : 0 < ‖(↑σ + ↑t * I : ℂ)‖ := by
    have ht_pos : 0 < |t| := by linarith
    linarith
  rw [inv_le_comm₀ h_pos (by positivity)]
  linarith

private theorem half_s_eq (σ t : ℝ) :
    ((↑σ + ↑t * I : ℂ) / 2) = ↑(σ / 2) + ↑(t / 2) * I := by
  apply Complex.ext <;> simp [div_eq_mul_inv]

/-- On `1/2 ≤ σ ≤ 2`, the half-shifted point has norm at most `|t|`. -/
private theorem norm_half_s_le_abs_t (σ t : ℝ)
    (hσlo : 1 / 2 ≤ σ) (hσhi : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖((↑σ + ↑t * I : ℂ) / 2)‖ ≤ |t| := by
  rw [half_s_eq, Complex.norm_add_mul_I]
  rw [show |t| = Real.sqrt (t ^ 2) by rw [Real.sqrt_sq_eq_abs]]
  apply Real.sqrt_le_sqrt
  have hσsq : σ ^ 2 ≤ 4 := by nlinarith [sq_nonneg (σ - 2), hσlo, hσhi]
  have ht_sq : 4 ≤ t ^ 2 := by
    nlinarith [sq_abs t, ht]
  have hσ_part : (σ / 2) ^ 2 ≤ t ^ 2 / 4 := by
    have hσ_one : (σ / 2) ^ 2 ≤ 1 := by nlinarith [hσsq]
    nlinarith
  nlinarith

/-- The half-shifted point lies outside the unit disk when `|t| ≥ 2`. -/
private theorem one_le_norm_half_s (σ t : ℝ) (ht : 2 ≤ |t|) :
    (1 : ℝ) ≤ ‖((↑σ + ↑t * I : ℂ) / 2)‖ := by
  rw [half_s_eq, Complex.norm_add_mul_I]
  have h_abs_half :
      |t| / 2 ≤ Real.sqrt ((σ / 2) ^ 2 + (t / 2) ^ 2) := by
    calc |t| / 2 = Real.sqrt ((t / 2) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.sqrt ((σ / 2) ^ 2 + (t / 2) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [sq_nonneg (σ / 2)]
  have h_abs_ge_one : (1 : ℝ) ≤ |t| / 2 := by nlinarith
  linarith

/-- Hence `log ‖(σ+it)/2‖ ≤ log |t|` on the strip. -/
private theorem log_norm_half_s_le_log_abs_t (σ t : ℝ)
    (hσlo : 1 / 2 ≤ σ) (hσhi : σ ≤ 2) (ht : 2 ≤ |t|) :
    Real.log ‖((↑σ + ↑t * I : ℂ) / 2)‖ ≤ Real.log |t| := by
  have hnorm_pos : 0 < ‖((↑σ + ↑t * I : ℂ) / 2)‖ := by
    have : (1 : ℝ) ≤ ‖((↑σ + ↑t * I : ℂ) / 2)‖ := one_le_norm_half_s σ t ht
    linarith
  exact Real.log_le_log hnorm_pos (norm_half_s_le_abs_t σ t hσlo hσhi ht)

/-- The principal logarithm on the half-strip is bounded by `log |t| + π`. -/
private theorem norm_log_half_s_le_log_abs_t_add_pi (σ t : ℝ)
    (hσlo : 1 / 2 ≤ σ) (hσhi : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖Complex.log (((↑σ + ↑t * I : ℂ) / 2))‖ ≤ Real.log |t| + Real.pi := by
  let w : ℂ := ((↑σ + ↑t * I : ℂ) / 2)
  have hre_nonneg : 0 ≤ (Complex.log w).re := by
    rw [Complex.log_re]
    exact Real.log_nonneg (one_le_norm_half_s σ t ht)
  have hre_le : (Complex.log w).re ≤ Real.log |t| := by
    rw [Complex.log_re]
    exact log_norm_half_s_le_log_abs_t σ t hσlo hσhi ht
  have him_abs : |(Complex.log w).im| ≤ Real.pi := by
    exact abs_le.mpr ⟨by linarith [Complex.neg_pi_lt_log_im w], Complex.log_im_le_pi w⟩
  calc ‖Complex.log w‖ = ‖((Complex.log w).re : ℂ) + ((Complex.log w).im : ℂ) * I‖ := by
        rw [Complex.re_add_im (Complex.log w)]
    _ ≤ ‖((Complex.log w).re : ℂ)‖ + ‖((Complex.log w).im : ℂ) * I‖ := norm_add_le _ _
    _ = |(Complex.log w).re| + |(Complex.log w).im| := by simp
    _ ≤ Real.log |t| + Real.pi := by
        rw [abs_of_nonneg hre_nonneg]
        linarith

/-- The digamma term contributes only linearly in `log |t|` on the strip. -/
private theorem half_logDeriv_Gamma_strip_bound :
    ∃ B0 B1 : ℝ,
      0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (σ t : ℝ), 1 / 2 ≤ σ → σ ≤ 2 → 2 ≤ |t| →
        ‖((1 / 2 : ℂ) * logDeriv Complex.Gamma (((↑σ + ↑t * I : ℂ) / 2)))‖ ≤
          B0 + B1 * Real.log |t| := by
  obtain ⟨C, hCpos, hC⟩ := DigammaAsymptotic.digamma_log_bound
  refine ⟨C + Real.pi, 1, by positivity, by positivity, ?_⟩
  intro σ t hσlo hσhi ht
  let w : ℂ := ((↑σ + ↑t * I : ℂ) / 2)
  have hw_re : w.re ≥ 1 / 4 := by
    rw [show w = ↑(σ / 2) + ↑(t / 2) * I by simpa [w] using half_s_eq σ t]
    simp
    linarith
  have hw_im : |w.im| ≥ 1 := by
    have hw_im_eq : w.im = t / 2 := by
      rw [show w = ↑(σ / 2) + ↑(t / 2) * I by simpa [w] using half_s_eq σ t]
      simp
    rw [hw_im_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hw_gamma : Complex.Gamma w ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    linarith
  have hmain : ‖logDeriv Complex.Gamma w - Complex.log w‖ ≤ C / ‖w‖ := by
    simpa [logDeriv_apply] using hC w hw_re hw_im hw_gamma
  have hlog : ‖Complex.log w‖ ≤ Real.log |t| + Real.pi :=
    norm_log_half_s_le_log_abs_t_add_pi σ t hσlo hσhi ht
  calc ‖((1 / 2 : ℂ) * logDeriv Complex.Gamma w)‖
      = ‖((1 / 2 : ℂ) * ((logDeriv Complex.Gamma w - Complex.log w) + Complex.log w))‖ := by
          congr 1
          ring
    _ ≤ ‖(1 / 2 : ℂ)‖ *
          ‖(logDeriv Complex.Gamma w - Complex.log w) + Complex.log w‖ := norm_mul_le _ _
    _ ≤ (1 / 2 : ℝ) *
          (‖logDeriv Complex.Gamma w - Complex.log w‖ + ‖Complex.log w‖) := by
          have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
          rw [hhalf]
          gcongr
          exact norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) * (C / ‖w‖ + (Real.log |t| + Real.pi)) := by
          gcongr
    _ ≤ C + (Real.log |t| + Real.pi) := by
          have hw_pos : 0 < ‖w‖ := by
            have : (1 : ℝ) ≤ ‖w‖ := by simpa [w] using one_le_norm_half_s σ t ht
            linarith
          have hC_part : (1 / 2 : ℝ) * (C / ‖w‖) ≤ C := by
            have h_inv_le : (1 : ℝ) / ‖w‖ ≤ 1 := by
              rw [div_le_iff₀ hw_pos]
              nlinarith [one_le_norm_half_s σ t ht]
            have : C / ‖w‖ ≤ C := by
              rw [div_le_iff₀ hw_pos]
              nlinarith [one_le_norm_half_s σ t ht, hCpos.le]
            have hnonneg : 0 ≤ C / ‖w‖ := by positivity
            nlinarith
          have hlog_part : (1 / 2 : ℝ) * (Real.log |t| + Real.pi) ≤ Real.log |t| + Real.pi := by
            nlinarith [log_abs_t_pos t ht, Real.pi_pos]
          nlinarith
    _ = (C + Real.pi) + 1 * Real.log |t| := by ring

/-- The pole, constant, and digamma background already satisfy a linear-log bound. -/
private theorem zeta_logderiv_easy_background_bound :
    ∃ B0 B1 : ℝ,
      0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (σ t : ℝ), 1 / 2 ≤ σ → σ ≤ 2 → 2 ≤ |t| →
        let s : ℂ := (↑σ + ↑t * I)
        ‖s⁻¹ + (s - 1)⁻¹ - (1 / 2 : ℂ) * Complex.log (↑Real.pi) +
            (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2)‖ ≤
          B0 + B1 * Real.log |t| := by
  obtain ⟨D0, D1, hD0, hD1, hdigamma⟩ := half_logDeriv_Gamma_strip_bound
  have hlogpi_nonneg : 0 ≤ Real.log Real.pi := by
    have hpi_gt_one : (1 : ℝ) < Real.pi := by
      nlinarith [Real.pi_gt_three]
    exact le_of_lt (Real.log_pos hpi_gt_one)
  refine ⟨1 + Real.log Real.pi + D0, D1, by linarith, hD1, ?_⟩
  intro σ t hσlo hσhi ht
  let s : ℂ := (↑σ + ↑t * I)
  let a : ℂ := s⁻¹
  let b : ℂ := (s - 1)⁻¹
  let c : ℂ := -((1 / 2 : ℂ) * Complex.log (↑Real.pi))
  let d : ℂ := (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2)
  have ha : ‖a‖ ≤ 1 / 2 := by
    simpa [a, s] using inv_s_bound σ t ht
  have hb : ‖b‖ ≤ 1 / 2 := by
    simpa [b, s] using pole_bound σ t ht
  have hc : ‖c‖ ≤ Real.log Real.pi := by
    have hlogpi : Complex.log (↑Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
      simpa using (Complex.ofReal_log (show 0 ≤ Real.pi by positivity)).symm
    have hpi_gt_one : (1 : ℝ) < Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hlogpi_pos : 0 < Real.log Real.pi := Real.log_pos hpi_gt_one
    have hlogpi_norm : ‖Complex.log (↑Real.pi : ℂ)‖ = Real.log Real.pi := by
      rw [hlogpi]
      simp [hlogpi_pos.le]
    calc ‖c‖ = ‖((1 / 2 : ℂ) * Complex.log (↑Real.pi))‖ := by
            dsimp [c]
            rw [norm_neg]
      _ ≤ ‖(Real.log Real.pi : ℂ)‖ := by
          calc ‖((1 / 2 : ℂ) * Complex.log (↑Real.pi))‖
              ≤ ‖(1 / 2 : ℂ)‖ * ‖Complex.log (↑Real.pi)‖ := norm_mul_le _ _
            _ ≤ 1 * ‖Complex.log (↑Real.pi)‖ := by
                have : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by norm_num
                gcongr
            _ = ‖Complex.log (↑Real.pi)‖ := by ring
            _ = ‖(Real.log Real.pi : ℂ)‖ := by rw [hlogpi]
      _ = Real.log Real.pi := by
          simp [hlogpi_pos.le]
  have hd : ‖d‖ ≤ D0 + D1 * Real.log |t| := by
    simpa [d, s] using hdigamma σ t hσlo hσhi ht
  calc ‖a + b + c + d‖
      ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
    _ ≤ (‖a + b‖ + ‖c‖) + ‖d‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ((1 / 2 + 1 / 2) + Real.log Real.pi) + (D0 + D1 * Real.log |t|) := by
        gcongr
    _ = (1 + Real.log Real.pi + D0) + D1 * Real.log |t| := by ring

/-! ## Section 3: Zero Sum — Algebraic Lemmas -/

/-- If n ≤ C · log|t| then n · M ≤ C · M · log|t| (for M ≥ 0). -/
theorem count_times_bound_le (C_d M : ℝ) (n : ℕ) (t : ℝ)
    (hM : 0 ≤ M)
    (h_count : (n : ℝ) ≤ C_d * Real.log |t|) :
    (n : ℝ) * M ≤ C_d * M * Real.log |t| := by
  calc (n : ℝ) * M ≤ C_d * Real.log |t| * M := by
        exact mul_le_mul_of_nonneg_right h_count hM
    _ = C_d * M * Real.log |t| := by ring

/-- Combined pointwise bound: pole + nearby + background ≤ C · (log|t|)². -/
theorem combined_bound_absorb (C_pole C_near C_bg : ℝ)
    (hCp : 0 ≤ C_pole) (_hCn : 0 ≤ C_near) (hCbg : 0 ≤ C_bg)
    (t : ℝ) (ht : 2 ≤ |t|) :
    C_pole + C_near * (Real.log |t|) ^ 2 + C_bg * Real.log |t| ≤
      (C_pole / (Real.log 2) ^ 2 + C_near + C_bg / Real.log 2) *
        (Real.log |t|) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_t : Real.log 2 ≤ Real.log |t| := log_two_le_log_abs_t t ht
  have hlog_pos : 0 < Real.log |t| := log_abs_t_pos t ht
  -- C_pole ≤ (C_pole/(log2)²) · (log|t|)²
  have hsq_mono : (Real.log 2) ^ 2 ≤ (Real.log |t|) ^ 2 :=
    pow_le_pow_left₀ hlog2.le hlog_t 2
  have h1 : C_pole ≤ C_pole / (Real.log 2) ^ 2 * (Real.log |t|) ^ 2 := by
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ (sq_pos_of_pos hlog2)]
    exact mul_le_mul_of_nonneg_left hsq_mono hCp
  -- C_bg · log|t| ≤ (C_bg/log2) · (log|t|)²
  have h2 : C_bg * Real.log |t| ≤ C_bg / Real.log 2 * (Real.log |t|) ^ 2 := by
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ hlog2]
    have : Real.log |t| * Real.log 2 ≤ Real.log |t| * Real.log |t| :=
      mul_le_mul_of_nonneg_left hlog_t hlog_pos.le
    nlinarith [sq_abs (Real.log |t|)]
  nlinarith

/-! ## Section 4: The Hadamard Product (Remaining Analytic Leaf)

This section contains the sole remaining analytic leaf: the Hadamard core
after removing the explicit pole and digamma background.

**Mathematical content (Titchmarsh §2.12):**
The completed zeta function ξ(s) = (1/2)s(s-1)π^{-s/2}Γ(s/2)ζ(s) is entire
of order 1 (Mathlib: `differentiable_completedZeta₀` proves Λ₀ is entire).

By the Hadamard factorization theorem (entire order 1):
  ξ(s) = ξ(0) · e^{As+B} · ∏_ρ (1 - s/ρ) · e^{s/ρ}

Taking the logarithmic derivative:
  ξ'/ξ(s) = A + Σ_ρ [1/(s-ρ) + 1/ρ]

Since ξ(s) = (1/2)s(s-1)π^{-s/2}Γ(s/2)ζ(s):
  ζ'/ζ(s) = ξ'/ξ(s) - 1/s - 1/(s-1) + (1/2)log(π) - (1/2)ψ(s/2)

where ψ = Γ'/Γ is the digamma function.

Rearranging:
  -ζ'/ζ(s) = -B₀ - 1/(s-1) + Σ_ρ [1/(s-ρ) + 1/ρ] + background(s)

The distant zero sum + background satisfies:
  |Σ_{|γ-t|>1} [1/(s-ρ) + 1/ρ] + background(s)| ≤ C · (log|t|)²

by partial summation with N(T) = O(T log T) and Stirling.

**Requirement:** Weierstrass factorization for entire functions of finite order,
together with the standard partial-summation and gamma-term estimates that
produce a coarse `A0 + A1 log|t| + A2 (log|t|)^2` bound. This is NOT in
Mathlib as of v4.27.0-rc1.

When Mathlib adds this, the remaining leaf closes by:
1. `differentiable_completedZeta₀` → ξ is entire
2. Growth bound on ξ → order 1 (from functional equation + Stirling)
3. Hadamard theorem → product representation
4. Log derivative → partial fraction
5. Partial summation → distant zero tail bound
-/

private theorem logDeriv_completedZeta_full_of_re_pos (s : ℂ)
    (hs_re : 0 < s.re) (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    logDeriv completedRiemannZeta s =
      -(1 / 2 : ℂ) * Complex.log (↑Real.pi) +
        (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2) +
          logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro hs0
    have : s.re = 0 := by simpa [hs0] using (rfl : ((0 : ℂ).re = (0 : ℝ)))
    exact (ne_of_gt hs_re) this
  have hG_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs_re
  have heq : completedRiemannZeta =ᶠ[𝓝 s] (Gammaℝ * riemannZeta) := by
    apply Filter.eventuallyEq_iff_exists_mem.mpr
    refine ⟨{z : ℂ | 0 < z.re}, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs_re,
      ?_⟩
    intro z hz_re
    have hz0 : z ≠ 0 := by
      intro hz0
      have : z.re = 0 := by simpa [hz0] using (rfl : ((0 : ℂ).re = (0 : ℝ)))
      exact (ne_of_gt hz_re) this
    have hGz : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos hz_re
    simpa [Pi.mul_apply] using RvMRightEdge.completedZeta_eq_GammaR_mul_zeta z hz0 hGz
  rw [show logDeriv completedRiemannZeta s = logDeriv (Gammaℝ * riemannZeta) s from by
    simp only [logDeriv_apply]
    rw [heq.deriv_eq, heq.eq_of_nhds]]
  have hG_diff : DifferentiableAt ℂ Gammaℝ s := RvMRightEdge.differentiableAt_GammaR s hs_re
  have hzeta_diff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hsplit :
      logDeriv (Gammaℝ * riemannZeta) s = logDeriv Gammaℝ s + logDeriv riemannZeta s := by
    simpa [Pi.mul_apply] using
      (logDeriv_mul (x := s) (f := Gammaℝ) (g := riemannZeta) hG_ne hzeta hG_diff hzeta_diff)
  rw [hsplit]
  rw [RvMRightEdge.logDeriv_GammaR_eq s hs_re]

private theorem background_subtracted_zeta_eq_neg_logDeriv_xi
    (σ t : ℝ) (hσlo : 1 / 2 ≤ σ) (ht : 2 ≤ |t|)
    (hzeta : riemannZeta (↑σ + ↑t * I) ≠ 0) :
    let s : ℂ := (↑σ + ↑t * I)
    ((-deriv riemannZeta s / riemannZeta s) -
      (s⁻¹ + (s - 1)⁻¹ - (1 / 2 : ℂ) * Complex.log (↑Real.pi) +
        (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2))) =
      -logDeriv RiemannXiAlt s := by
  let s : ℂ := (↑σ + ↑t * I)
  have hs_re : 0 < s.re := by
    simp [s]
    linarith
  have hs0 : s ≠ 0 := by
    intro hs0
    have hnorm : |t| ≤ ‖s‖ := by simpa [s] using norm_s_ge_abs_t σ t
    have : ‖s‖ = 0 := by simpa [s, hs0]
    linarith
  have hs1 : s ≠ 1 := by
    intro hs1
    have hnorm : |t| ≤ ‖s - 1‖ := by simpa [s] using norm_s_sub_one_ge_abs_t σ t ht
    have : ‖s - 1‖ = 0 := by simpa [s, hs1]
    linarith
  have hG_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs_re
  have hcomp : completedRiemannZeta s ≠ 0 := by
    rw [RvMRightEdge.completedZeta_eq_GammaR_mul_zeta s hs0 hG_ne]
    exact mul_ne_zero hG_ne hzeta
  have hfun : RiemannXiAlt = RvMSubLemmas.RiemannXiAlt := by
    funext z
    simp [RiemannXiAlt, RvMSubLemmas.RiemannXiAlt]
  have hxi :
      logDeriv RiemannXiAlt s =
        1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
    rw [hfun]
    exact RvMSubLemmas.logDeriv_RiemannXiAlt_decomposition s hs0 hs1 hcomp
  have hcompleted :=
    logDeriv_completedZeta_full_of_re_pos s hs_re hs1 hzeta
  have hlogderiv_zeta :
      logDeriv riemannZeta s = deriv riemannZeta s / riemannZeta s := by
    simpa [logDeriv_apply, hzeta]
  have hcombined :
      logDeriv RiemannXiAlt s =
        s⁻¹ + (s - 1)⁻¹ - (1 / 2 : ℂ) * Complex.log (↑Real.pi) +
          (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2) +
            deriv riemannZeta s / riemannZeta s := by
    rw [hxi, hcompleted, hlogderiv_zeta]
    ring
  change ((-deriv riemannZeta s / riemannZeta s) -
      (s⁻¹ + (s - 1)⁻¹ - (1 / 2 : ℂ) * Complex.log (↑Real.pi) +
        (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2))) = -logDeriv RiemannXiAlt s
  rw [hcombined]
  ring

/-- Conditional canonical-product reduction: once a `HadamardXiCore` instance
is supplied and the point avoids the chosen xi zero set, the background-
subtracted zeta expression is exactly the negative Hadamard constant plus xi
zero sum. This is the constructive upstream reduction provided by
`HadamardFactorizationXi`. -/
private theorem background_subtracted_zeta_eq_neg_hadamard_const_add_zeroSum
    [h : HadamardXi.HadamardXiCore]
    (σ t : ℝ) (hσlo : 1 / 2 ≤ σ) (ht : 2 ≤ |t|)
    (hzeta : riemannZeta (↑σ + ↑t * I) ≠ 0)
    (hs_ne : ∀ n : ℕ, (↑σ + ↑t * I : ℂ) ≠ h.zeros n) :
    let s : ℂ := (↑σ + ↑t * I)
    ((-deriv riemannZeta s / riemannZeta s) -
      (s⁻¹ + (s - 1)⁻¹ - (1 / 2 : ℂ) * Complex.log (↑Real.pi) +
        (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2))) =
      -(h.B + HadamardXi.zeroSum s) := by
  let s : ℂ := (↑σ + ↑t * I)
  have hmain := background_subtracted_zeta_eq_neg_logDeriv_xi σ t hσlo ht hzeta
  have hxi :
      logDeriv RiemannXiAlt s = h.B + HadamardXi.zeroSum s := by
    exact HadamardXi.logDeriv_xi_partial_fraction (h := h) s (by simpa [s] using hs_ne)
  calc
    ((-deriv riemannZeta s / riemannZeta s) -
        (s⁻¹ + (s - 1)⁻¹ - (1 / 2 : ℂ) * Complex.log (↑Real.pi) +
          (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2)))
        = -logDeriv RiemannXiAlt s := hmain
    _ = -(h.B + HadamardXi.zeroSum s) := by rw [hxi]

/-- Honest large-`T` Hadamard boundary: after subtracting the explicit pole and
gamma-background terms, the remaining analytic input is a strip bound for the
canonical-product remainder `B + zeroSum s`, stated only away from the chosen
xi zero set. -/
class HadamardXiResidualStripBoundHyp
    [h : HadamardXi.HadamardXiCore] : Prop where
  bound :
    ∃ A0 A1 A2 : ℝ,
      0 ≤ A0 ∧ 0 ≤ A1 ∧ 0 ≤ A2 ∧
      ∀ (σ t : ℝ), 1 / 2 ≤ σ → σ ≤ 2 → 2 ≤ |t| →
        (∀ n : ℕ, (↑σ + ↑t * I : ℂ) ≠ h.zeros n) →
          ‖h.B + HadamardXi.zeroSum (↑σ + ↑t * I)‖ ≤
            A0 + A1 * Real.log |t| + A2 * (Real.log |t|) ^ 2

/-- Constructive wrapper around the xi canonical-product boundary: away from
the xi zero set and away from zeta zeros, the background-subtracted `-ζ'/ζ`
expression is exactly the negative Hadamard remainder, so any strip bound on
that remainder transfers directly. -/
theorem zeta_logderiv_hadamard_core_bound
    [h : HadamardXi.HadamardXiCore]
    [HadamardXiResidualStripBoundHyp] :
    ∃ A0 A1 A2 : ℝ,
      0 ≤ A0 ∧ 0 ≤ A1 ∧ 0 ≤ A2 ∧
      ∀ (σ t : ℝ), 1 / 2 ≤ σ → σ ≤ 2 → 2 ≤ |t| →
        riemannZeta (↑σ + ↑t * I) ≠ 0 →
        (∀ n : ℕ, (↑σ + ↑t * I : ℂ) ≠ h.zeros n) →
          ‖(-deriv riemannZeta (↑σ + ↑t * I) / riemannZeta (↑σ + ↑t * I)) -
            (((↑σ + ↑t * I : ℂ))⁻¹ + ((↑σ + ↑t * I : ℂ) - 1)⁻¹ -
              (1 / 2 : ℂ) * Complex.log (↑Real.pi) +
              (1 / 2 : ℂ) * logDeriv Complex.Gamma ((↑σ + ↑t * I : ℂ) / 2))‖ ≤
            A0 + A1 * Real.log |t| + A2 * (Real.log |t|) ^ 2 := by
  obtain ⟨A0, A1, A2, hA0, hA1, hA2, hbound⟩ := HadamardXiResidualStripBoundHyp.bound
  refine ⟨A0, A1, A2, hA0, hA1, hA2, ?_⟩
  intro σ t hσlo hσhi ht
  let s : ℂ := (↑σ + ↑t * I)
  intro hzeta hs_ne
  have hrewrite :=
    background_subtracted_zeta_eq_neg_hadamard_const_add_zeroSum
      (h := h) σ t hσlo ht hzeta hs_ne
  have hnorm :
      ‖(-deriv riemannZeta s / riemannZeta s) -
          (s⁻¹ + (s - 1)⁻¹ - (1 / 2 : ℂ) * Complex.log (↑Real.pi) +
            (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2))‖ =
        ‖-(h.B + HadamardXi.zeroSum s)‖ := by
    simpa [s, add_comm, add_left_comm, add_assoc] using congrArg norm hrewrite
  rw [hnorm, norm_neg]
  exact hbound σ t hσlo hσhi ht hs_ne

/-- Honest zero-avoiding large-`T` bound on `-ζ'/ζ`: once the canonical-product
remainder is bounded away from the xi zeros, the explicit pole and digamma
terms are absorbed constructively into the same quadratic-log shape. -/
theorem zeta_logderiv_zero_avoiding_bound
    [h : HadamardXi.HadamardXiCore]
    [HadamardXiResidualStripBoundHyp] :
    ∃ A0 A1 A2 : ℝ,
      0 ≤ A0 ∧ 0 ≤ A1 ∧ 0 ≤ A2 ∧
      ∀ (σ t : ℝ), 1 / 2 ≤ σ → σ ≤ 2 → 2 ≤ |t| →
        riemannZeta (↑σ + ↑t * I) ≠ 0 →
        (∀ n : ℕ, (↑σ + ↑t * I : ℂ) ≠ h.zeros n) →
          ‖(-deriv riemannZeta (↑σ + ↑t * I) / riemannZeta (↑σ + ↑t * I))‖ ≤
            A0 + A1 * Real.log |t| + A2 * (Real.log |t|) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hbg⟩ := zeta_logderiv_easy_background_bound
  obtain ⟨A0, A1, A2, hA0, hA1, hA2, hcore⟩ := zeta_logderiv_hadamard_core_bound
  refine ⟨A0 + B0, A1 + B1, A2, add_nonneg hA0 hB0, add_nonneg hA1 hB1, hA2, ?_⟩
  intro σ t hσlo hσhi ht
  let s : ℂ := (↑σ + ↑t * I)
  intro hzeta hs_ne
  let bg : ℂ :=
    s⁻¹ + (s - 1)⁻¹ - (1 / 2 : ℂ) * Complex.log (↑Real.pi) +
      (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2)
  have hcore' := hcore σ t hσlo hσhi ht hzeta hs_ne
  have hbg' := hbg σ t hσlo hσhi ht
  calc
    ‖(-deriv riemannZeta s / riemannZeta s)‖
        = ‖((-deriv riemannZeta s / riemannZeta s) - bg) + bg‖ := by
            congr 1
            ring
    _ ≤ ‖(-deriv riemannZeta s / riemannZeta s) - bg‖ + ‖bg‖ := norm_add_le _ _
    _ ≤ (A0 + A1 * Real.log |t| + A2 * (Real.log |t|) ^ 2) + (B0 + B1 * Real.log |t|) := by
          gcongr
    _ = (A0 + B0) + (A1 + B1) * Real.log |t| + A2 * (Real.log |t|) ^ 2 := by ring

/-! ## Section 5: From Pointwise to Contour Bounds

The connection from the pointwise bound to the shifted remainder bound
(needed by HadamardProductZeta.hadamard_contour_bound) goes through:

1. Perron formula: ψ(x) = (1/2πi) ∫_{c-iT}^{c+iT} (-ζ'/ζ)(s) x^s/s ds + error
   (sum-integral interchange proved in PerronFormulaProof.lean)

2. Contour shift: move from Re=c to Re=1/2, extracting residues
   (CIF proved in CauchyRectangleFormula.lean; shift in PerronContourShift.lean)

3. Segment bounds: use pointwise bound to bound the shifted contour integrals
   (proved in PerronContourShift.lean and HadamardProductZeta.lean Sections 3-5)

The old unconditional pointwise theorem for `-ζ'/ζ` is not exported from this
module. The honest remaining boundary is the zero-avoiding Hadamard remainder
class `HadamardXiResidualStripBoundHyp`; contour-side files now carry their own
explicit support hypotheses instead of pretending this global bound is already
proved.

Note: The Perron formula itself (connecting ψ to the contour integral)
is a separate mathematical input. The sum-integral interchange is proved
in PerronFormulaProof.lean, but the full Perron formula with error term
requires additional contour analysis.
-/

end Littlewood.Development.ZetaLogDerivBound
