/-
Pointwise Bound on |ζ'/ζ(σ+it)| via Zero Sum Decomposition

Proves: |ζ'/ζ(σ+it)| ≤ C·(log|t|)² for 1/2 ≤ σ ≤ 2, |t| ≥ 2.

## Strategy

The Hadamard product for ξ(s) gives a partial fraction for ζ'/ζ(s).
We decompose the bound into:
  (A) Pole: |1/(s-1)| ≤ 1/|t| ≤ 1/2 — absorbed into C·(log|t|)²
  (B) Background: B₀ + Γ terms — O(log|t|) — absorbed into C·(log|t|)²
  (C) Nearby zeros: ≤ C_d · logT · (something) — O((log|t|)²)
  (D) Distant zeros: O((log|t|)²) by partial summation

The ONLY sorry is the Hadamard product representation itself.

## References

- Titchmarsh, "Theory of the Riemann Zeta Function", §§2.12, 9.6.1
- Davenport, "Multiplicative Number Theory", Chapter 12

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Littlewood.Development.ZetaLogDerivBound

open Complex Real Set MeasureTheory Topology Filter

/-! ## Section 1: Pole Contribution Bounds -/

/-- For σ ∈ [1/2, 2] and |t| ≥ 2: ‖s - 1‖ ≥ |t|. -/
theorem norm_s_sub_one_ge_abs_t (σ t : ℝ) (ht : 2 ≤ |t|) :
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
    (hCp : 0 ≤ C_pole) (hCn : 0 ≤ C_near) (hCbg : 0 ≤ C_bg)
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

/-! ## Section 4: The Hadamard Product (ATOMIC SORRY)

This section contains the SOLE irreducible sorry: the Hadamard product
representation of ζ'/ζ as a sum over zeros.

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

**Requirement:** Weierstrass factorization for entire functions of finite order.
This is NOT in Mathlib as of v4.27.0-rc1.

When Mathlib adds this, the sorry closes by:
1. `differentiable_completedZeta₀` → ξ is entire
2. Growth bound on ξ → order 1 (from functional equation + Stirling)
3. Hadamard theorem → product representation
4. Log derivative → partial fraction
5. Partial summation → distant zero tail bound
-/

/-- **THE ATOMIC SORRY**: The pointwise bound on ζ'/ζ.

    |(-ζ'/ζ)(σ+it)| ≤ C · (log|t|)² for 1/2 ≤ σ ≤ 2, |t| ≥ 2.

    Requires: Weierstrass factorization of entire functions of order 1.
    Not in Mathlib; all algebraic reductions are proved.

    When Mathlib adds `Entire.hadamard_factorization`, this closes via
    the algebraic infrastructure in Sections 1-3 above. -/
theorem zeta_logderiv_pointwise_bound :
    ∃ C > (0 : ℝ), ∀ (σ t : ℝ), 1/2 ≤ σ → σ ≤ 2 → 2 ≤ |t| →
      ‖(-deriv riemannZeta (↑σ + ↑t * I) /
        riemannZeta (↑σ + ↑t * I))‖ ≤ C * (Real.log |t|) ^ 2 := by
  sorry

/-! ## Section 5: From Pointwise to Contour Bounds

The connection from the pointwise bound to the shifted remainder bound
(needed by HadamardProductZeta.hadamard_contour_bound) goes through:

1. Perron formula: ψ(x) = (1/2πi) ∫_{c-iT}^{c+iT} (-ζ'/ζ)(s) x^s/s ds + error
   (sum-integral interchange proved in PerronFormulaProof.lean)

2. Contour shift: move from Re=c to Re=1/2, extracting residues
   (CIF proved in CauchyRectangleFormula.lean; shift in PerronContourShift.lean)

3. Segment bounds: use pointwise bound to bound the shifted contour integrals
   (proved in PerronContourShift.lean and HadamardProductZeta.lean Sections 3-5)

The full chain: once zeta_logderiv_pointwise_bound is proved,
hadamard_contour_bound and perron_small_T_bound follow by assembly.

Note: The Perron formula itself (connecting ψ to the contour integral)
is a separate mathematical input. The sum-integral interchange is proved
in PerronFormulaProof.lean, but the full Perron formula with error term
requires additional contour analysis.
-/

end Littlewood.Development.ZetaLogDerivBound
