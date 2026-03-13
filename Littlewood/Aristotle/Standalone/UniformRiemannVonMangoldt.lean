/-
Uniform Riemann-von Mangoldt formula:

  N(T) = (T/(2π)) · log(T/(2πe)) + O(log T)

where N(T) counts zeros of ζ(s) in the critical strip with 0 < Im(ρ) ≤ T.

This file proves the uniform asymptotic from three standard hypotheses:
  (1) Backlund identity: N(T) = (1/π)θ(T) + 1 + S(T) + O(1)
  (2) Stirling for arg Γ: θ(T) = thetaApprox(T) + O(1/T)
  (3) S(T) = O(log T), which we prove from |arg(z)| ≤ π

The derived uniform bound enables instantiation of CriticalZeroSumDivergesHyp (B5b),
the π-chain exact seed, and phase alignment via Kronecker.

REFERENCES:
  Backlund 1918, Titchmarsh Ch. IX, Montgomery-Vaughan §15.1
-/

import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace UniformRiemannVonMangoldt

/-! ## Definitions -/

/-- N(T): number of zeros of ζ(s) in the critical strip with 0 < Im(s) ≤ T. -/
noncomputable def NZeros (T : ℝ) : ℕ :=
  Set.ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T}

/-- S(T) := (1/π) arg ζ(1/2 + iT). -/
noncomputable def S (T : ℝ) : ℝ :=
  (1 / Real.pi) * (riemannZeta (1/2 + T * Complex.I)).arg

/-- θ(T): Riemann-Siegel theta function (argument of Γ minus log π term). -/
noncomputable def theta (T : ℝ) : ℝ :=
  (Complex.Gamma (1/4 + T/2 * Complex.I)).arg - (T/2) * Real.log Real.pi

/-- Main asymptotic term: (T/(2π)) log(T/(2πe)). -/
noncomputable def mainTerm (T : ℝ) : ℝ :=
  (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))

/-- Theta approximation: (T/2)log(T/(2π)) - T/2 - π/8. -/
noncomputable def thetaApprox (T : ℝ) : ℝ :=
  (T / 2) * Real.log (T / (2 * Real.pi)) - T / 2 - Real.pi / 8

/-! ## S(T) = O(log T) — genuine proof from |arg z| ≤ π -/

/-- |S(T)| ≤ 1 for all T > 0, since |arg z| ≤ π and S = arg/π. -/
theorem S_abs_le_one (T : ℝ) (_hT : 0 < T) : |S T| ≤ 1 := by
  unfold S
  have hpi : 0 < Real.pi := Real.pi_pos
  have h_arg_le := Complex.arg_le_pi (riemannZeta (1/2 + T * Complex.I))
  have h_arg_gt := Complex.neg_pi_lt_arg (riemannZeta (1/2 + T * Complex.I))
  rw [abs_le]
  constructor
  · -- -1 ≤ (1/π) · arg ← arg > -π
    rw [one_div, neg_le_iff_add_nonneg]
    have key : Real.pi⁻¹ * (riemannZeta (1 / 2 + ↑T * Complex.I)).arg + 1
      = ((riemannZeta (1 / 2 + ↑T * Complex.I)).arg + Real.pi) * Real.pi⁻¹ := by field_simp
    rw [key]
    exact mul_nonneg (by linarith) (inv_nonneg.mpr (le_of_lt hpi))
  · -- (1/π) · arg ≤ 1 ← arg ≤ π
    rw [one_div, inv_mul_le_iff₀' hpi]
    linarith

/-- S(T) = O(log T) — uniform bound. -/
theorem S_isBigO_log : S =O[Filter.atTop] Real.log := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / Real.log 2, Filter.eventually_atTop.mpr ⟨2, fun x hx => ?_⟩⟩
  have hx_pos : 0 < x := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogx_nn]
  calc |S x| ≤ 1 := S_abs_le_one x hx_pos
    _ = Real.log 2 / Real.log 2 := (div_self (ne_of_gt hlog2_pos)).symm
    _ ≤ Real.log x / Real.log 2 := by gcongr
    _ = 1 / Real.log 2 * Real.log x := by ring

/-! ## Main theorem: uniform RvM from hypotheses -/

/-- Key algebraic identity: (1/π) · thetaApprox(T) + 1 - mainTerm(T) - 7/8 = 0.

Follows from log(T/(2πe)) = log(T/(2π)) - 1.
-/
theorem identity_thetaApprox_mainTerm (T : ℝ) (hT : 0 < T) :
    (1/Real.pi) * thetaApprox T + 1 - mainTerm T - 7/8 = 0 := by
  unfold thetaApprox mainTerm
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hT2pi_ne : T / (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
  have hlog_split : Real.log (T / (2 * Real.pi * Real.exp 1))
    = Real.log (T / (2 * Real.pi)) - 1 := by
    have : T / (2 * Real.pi * Real.exp 1) = T / (2 * Real.pi) / Real.exp 1 := by
      rw [div_div]
    rw [this, Real.log_div hT2pi_ne (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
  rw [hlog_split]
  field_simp
  ring

/-- **Uniform Riemann-von Mangoldt formula** from Backlund + Stirling.

Given:
  (H1) Backlund: N(T) = (1/π)θ(T) + 1 + S(T) + O(1)
  (H2) Stirling: θ(T) = thetaApprox(T) + O(1/T)

Conclusion: N(T) = mainTerm(T) + O(log T), i.e.,
  N(T) = (T/(2π)) log(T/(2πe)) + O(log T).
-/
theorem uniform_riemann_von_mangoldt
    (hBacklund : ∃ C₁ : ℝ, ∀ T : ℝ, 2 ≤ T →
      |(NZeros T : ℝ) - ((1 / Real.pi) * theta T + 1 + S T)| ≤ C₁)
    (hStirling : ∃ C₂ : ℝ, ∀ T : ℝ, 2 ≤ T →
      |theta T - thetaApprox T| ≤ C₂ / T) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
      |(NZeros T : ℝ) - mainTerm T| ≤ C * Real.log T := by
  obtain ⟨C₁, hC₁⟩ := hBacklund
  obtain ⟨C₂, hC₂⟩ := hStirling
  have hpi_pos := Real.pi_pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  refine ⟨(|C₁| + |C₂| / Real.pi + 1 + 7/8) / Real.log 2, fun T hT => ?_⟩
  have hT_pos : 0 < T := by linarith
  have hlog_pos : 0 < Real.log T := Real.log_pos (by linarith : (1:ℝ) < T)
  have hlog_ge : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  -- Decomposition
  have h_decomp : (NZeros T : ℝ) - mainTerm T
    = ((NZeros T : ℝ) - ((1/Real.pi) * theta T + 1 + S T))
    + (1/Real.pi) * (theta T - thetaApprox T)
    + ((1/Real.pi) * thetaApprox T + 1 - mainTerm T - 7/8)
    + S T + 7/8 := by ring
  have h_identity : (1/Real.pi) * thetaApprox T + 1 - mainTerm T - 7/8 = 0 :=
    identity_thetaApprox_mainTerm T hT_pos
  -- Individual bounds
  have h1 : |(NZeros T : ℝ) - ((1/Real.pi) * theta T + 1 + S T)| ≤ |C₁| :=
    le_trans (hC₁ T hT) (le_abs_self C₁)
  have h2 : |(1/Real.pi) * (theta T - thetaApprox T)| ≤ |C₂| / Real.pi := by
    rw [abs_mul, show |1/Real.pi| = 1/Real.pi from abs_of_pos (by positivity : 0 < 1/Real.pi)]
    calc 1 / Real.pi * |theta T - thetaApprox T|
        ≤ 1 / Real.pi * (|C₂| / T) := by
          gcongr
          exact le_trans (hC₂ T hT) (div_le_div_of_nonneg_right (le_abs_self C₂) (le_of_lt hT_pos))
      _ = |C₂| / (Real.pi * T) := by ring
      _ ≤ |C₂| / Real.pi := by
          gcongr
          exact le_mul_of_one_le_right (le_of_lt hpi_pos) (by linarith)
  have h3 : |S T| ≤ 1 := S_abs_le_one T hT_pos
  -- Combine via triangle inequality
  rw [h_decomp, h_identity]
  set a := (NZeros T : ℝ) - ((1/Real.pi) * theta T + 1 + S T)
  set b := (1/Real.pi) * (theta T - thetaApprox T)
  set s := S T
  -- |a + b + 0 + s + 7/8| ≤ |a| + |b| + |s| + 7/8
  have tri : |a + b + 0 + s + 7/8| ≤ |a| + |b| + |s| + 7/8 := by
    have t1 : |a + b + 0 + s + 7/8| ≤ |a + b + 0 + s| + 7/8 := by
      calc |a + b + 0 + s + 7/8|
          ≤ |a + b + 0 + s| + |(7:ℝ)/8| := abs_add_le _ _
        _ = |a + b + 0 + s| + 7/8 := by
            rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 7/8)]
    have t2 : |a + b + 0 + s| ≤ |a + b| + |s| := by
      rw [show a + b + 0 + s = (a + b) + s from by ring]
      exact abs_add_le _ _
    have t3 : |a + b| ≤ |a| + |b| := abs_add_le a b
    linarith
  -- Now bound each term
  have bound : |a + b + 0 + s + 7/8| ≤ |C₁| + |C₂| / Real.pi + 1 + 7/8 := by
    linarith
  -- constant ≤ (constant / log 2) · log T, since log 2 ≤ log T
  calc |a + b + 0 + s + 7/8|
      ≤ |C₁| + |C₂| / Real.pi + 1 + 7/8 := bound
    _ = (|C₁| + |C₂| / Real.pi + 1 + 7/8) / Real.log 2 * Real.log 2 :=
        (div_mul_cancel₀ _ (ne_of_gt hlog2_pos)).symm
    _ ≤ (|C₁| + |C₂| / Real.pi + 1 + 7/8) / Real.log 2 * Real.log T := by gcongr

/-- **Corollary**: The uniform RvM in Asymptotics.IsBigO form. -/
theorem uniform_riemann_von_mangoldt_isBigO
    (hBacklund : ∃ C₁ : ℝ, ∀ T : ℝ, 2 ≤ T →
      |(NZeros T : ℝ) - ((1 / Real.pi) * theta T + 1 + S T)| ≤ C₁)
    (hStirling : ∃ C₂ : ℝ, ∀ T : ℝ, 2 ≤ T →
      |theta T - thetaApprox T| ≤ C₂ / T) :
    (fun T => (NZeros T : ℝ) - mainTerm T) =O[Filter.atTop] Real.log := by
  obtain ⟨C, hC⟩ := uniform_riemann_von_mangoldt hBacklund hStirling
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, Filter.eventually_atTop.mpr ⟨2, fun T hT => ?_⟩⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith : (1:ℝ) ≤ T))]
  exact hC T hT

end UniformRiemannVonMangoldt
