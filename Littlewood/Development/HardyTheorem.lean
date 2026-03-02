/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected
import Littlewood.Aristotle.HardyZReal
import Littlewood.Aristotle.MeanSquare
import Littlewood.Aristotle.PhragmenLindelof
import Littlewood.Aristotle.SchmidtOscillation

/-!
# Hardy's Theorem Development

Working toward: There are infinitely many zeros of ζ(s) on Re(s) = 1/2.

## Hardy's 1914 Proof Outline

Hardy's proof uses:
1. The Hardy Z-function: Z(t) = exp(iθ(t)) ζ(1/2 + it)
   where θ(t) is the Riemann-Siegel theta function
2. Key property: Z(t) is real for real t
3. Sign changes of Z(t) correspond to zeros on the critical line
4. Showing Z(t) changes sign infinitely often

## Historical Note

Hardy's 1914 paper "Sur les zéros de la fonction ζ(s) de Riemann" established
that there are infinitely many zeros on the critical line Re(s) = 1/2.
This was a major breakthrough in understanding the Riemann zeta function.

## References
- Hardy, "Sur les zéros de la fonction ζ(s) de Riemann" (1914)
- Titchmarsh, "Theory of the Riemann Zeta Function", Chapter 10
- Edwards, "Riemann's Zeta Function", Chapter 8
-/

namespace Littlewood.Development.HardyTheorem

open Complex Real Topology

-- ============================================================
-- SECTION 1: What Mathlib provides
-- ============================================================

#check Complex.Gamma
-- Complex.Gamma : ℂ → ℂ

#check riemannZeta
-- riemannZeta : ℂ → ℂ

#check Complex.arg
-- Complex.arg : ℂ → ℝ (argument of a complex number)

/-
## What Mathlib Provides:

1. **Gamma function:** `Complex.Gamma : ℂ → ℂ`
2. **Riemann zeta:** `riemannZeta : ℂ → ℂ`
3. **Complex argument:** `Complex.arg : ℂ → ℝ`
4. **Functional equation:** `riemannZeta_one_sub`

## What's Missing:

1. **Riemann-Siegel theta function:** θ(t) = arg(Γ(1/4 + it/2)) - (t/2)log(π)
2. **Hardy Z-function:** Z(t) = exp(iθ(t)) · ζ(1/2 + it)
3. **Z(t) is real:** Proof that Z takes real values on ℝ
4. **Sign change analysis:** Tools to detect sign changes
-/

-- ============================================================
-- SECTION 2: The Riemann-Siegel theta function
-- ============================================================

/-- The Riemann-Siegel theta function.

θ(t) = arg(Γ(1/4 + it/2)) - (t/2) · log(π)

This is the phase function that makes Z(t) real.
-/
noncomputable def riemannSiegelTheta (t : ℝ) : ℝ :=
  Complex.arg (Complex.Gamma (1/4 + t/2 * I)) - t/2 * Real.log Real.pi

-- ============================================================
-- SECTION 3: The Hardy Z-function
-- ============================================================

/-- The Hardy Z-function.

Z(t) = exp(i·θ(t)) · ζ(1/2 + it)

Key property: Z(t) is real for all real t.
Zeros of Z(t) correspond to zeros of ζ(s) on the critical line.
-/
noncomputable def hardyZ (t : ℝ) : ℂ :=
  Complex.exp (I * riemannSiegelTheta t) * riemannZeta (1/2 + t * I)

/-- Z(t) is real for all real t.

This follows from the functional equation of ζ(s):
ξ(s) = ξ(1-s) where ξ(s) = π^(-s/2) Γ(s/2) ζ(s)

**BLOCKED:** Requires careful phase tracking through:
1. The reflection formula: ξ(s) = ξ(1-s)
2. The conjugate symmetry: ζ(conj(s)) = conj(ζ(s))
3. On critical line s = 1/2 + it: conj(s) = 1/2 - it = 1 - s
4. Therefore ξ(s) = conj(ξ(s)), so ξ(s) is real
5. The phase factor θ(t) is precisely chosen so that Z(t) = exp(iθ(t))ζ(s) is real

Mathlib has `riemannZeta_one_sub` and `riemannZeta_conj` but extracting
the exact phase requires completing `riemannCompletedZeta` infrastructure.
-/
theorem hardyZ_real (t : ℝ) : (hardyZ t).im = 0 := by
  -- The definitions of hardyZ and hardyZ' are identical
  -- (both are exp(I * θ(t)) * ζ(1/2 + t*I) with same θ definition)
  -- Use hardyZ'_real from HardyZReal
  have h_eq : hardyZ t = hardyZ' t := rfl
  rw [h_eq]
  exact hardyZ'_real t

/-- Extract the real value of Z(t) -/
noncomputable def hardyZ_real_val (t : ℝ) : ℝ :=
  (hardyZ t).re

-- ============================================================
-- SECTION 4: Connection to zeros
-- ============================================================

/-- Z(t) = 0 if and only if ζ(1/2 + it) = 0 -/
theorem hardyZ_zero_iff (t : ℝ) :
    hardyZ t = 0 ↔ riemannZeta (1/2 + t * I) = 0 := by
  constructor
  · intro hz
    simp only [hardyZ] at hz
    have hexp : Complex.exp (I * riemannSiegelTheta t) ≠ 0 := Complex.exp_ne_zero _
    exact (mul_eq_zero.mp hz).resolve_left hexp
  · intro hζ
    simp only [hardyZ, hζ, mul_zero]

-- ============================================================
-- SECTION 4.5: Building toward sign changes (Task 17)
-- ============================================================

/-
## Strategy: From hardyZ_zero_iff to Hardy's Theorem

We have: hardyZ_zero_iff: Z(t) = 0 ↔ ζ(1/2 + it) = 0

The key steps are:
1. Z(t) is real for real t (requires functional equation)
2. Z(t) is continuous (follows from continuity of ζ and exp)
3. Z(t) changes sign infinitely often (the hard part)
4. By IVT, sign changes give zeros
-/

/-- Z(t) is real for all real t.

This follows from the functional equation ξ(s) = ξ(1-s) where
ξ(s) = π^(-s/2) Γ(s/2) ζ(s) is the completed zeta function.
The phase θ(t) is chosen precisely to make this true.

This is an alias for `hardyZ_real`.
-/
theorem hardyZ_is_real (t : ℝ) : (hardyZ t).im = 0 :=
  hardyZ_real t

/-- Consequence: Z(t) equals its real part -/
lemma hardyZ_eq_re (t : ℝ) : hardyZ t = (hardyZ t).re := by
  rw [Complex.ext_iff]
  simp [hardyZ_is_real t]

/-- The INPUT 1/4 + it/2 is in the slit plane (has positive real part). -/
lemma input_quarter_in_slitPlane (t : ℝ) : (1/4 : ℂ) + t/2 * I ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, sub_zero]
  norm_num

-- NOTE: The former lemma `gamma_quarter_in_slitPlane` was FALSE.
-- Numerical verification (scipy) shows Γ(1/4 + it/2) crosses the negative real axis
-- at t ≈ 10.592, 17.12, 22.60, ... (infinitely many crossings).
-- At those points, Γ is a negative real number NOT in Complex.slitPlane.
-- Consequently, Complex.arg(Γ(1/4 + it/2)) has jump discontinuities,
-- and riemannSiegelTheta is NOT continuous as a function ℝ → ℝ.
--
-- However, exp(I * θ(t)) IS continuous, because it factors as
-- Γ(s/2)/‖Γ(s/2)‖ · exp(-I·t/2·log(π)) via exp(I·arg(z)) = z/‖z‖ for z ≠ 0.
-- The proof of hardyZ_continuous below uses the completed zeta representation
-- Z(t) = ξ(1/2+it) / ‖Γℝ(1/2+it)‖ from HardyZReal to bypass theta entirely.

set_option maxHeartbeats 400000 in
/-- exp(I * θ(t)) is continuous, even though θ itself is not (Complex.arg has a branch
cut on the negative real axis, and Γ(1/4 + it/2) crosses that ray at t ≈ 10.592, ...).

The continuity follows from the factorization:
  exp(I·θ(t)) = exp(I·arg(Γ(w))) · exp(-I·t/2·log(π))
             = (Γ(w)/‖Γ(w)‖) · exp(-I·t/2·log(π))
using exp(I·arg(z)) = z/‖z‖ for z ≠ 0 (Mathlib: `norm_mul_exp_arg_mul_I`).
Both factors are continuous: Γ is nonzero for Re(w) > 0, and exp of a linear function
is continuous. -/
lemma exp_I_theta_continuous :
    Continuous (fun t : ℝ => Complex.exp (I * ↑(riemannSiegelTheta t))) := by
  -- Step 1: Factor via exp(I·arg(z)) = z/‖z‖ (norm_mul_exp_arg_mul_I)
  have h_factor : (fun t : ℝ => Complex.exp (I * ↑(riemannSiegelTheta t))) =
      (fun t : ℝ => Complex.Gamma ((1:ℂ)/4 + ↑t/2 * I) /
                     ↑‖Complex.Gamma ((1:ℂ)/4 + ↑t/2 * I)‖ *
                     Complex.exp (-(I * ↑(t/2 * Real.log Real.pi)))) := by
    funext t
    unfold riemannSiegelTheta
    -- Split exponent: exp(I*(a - b)) = exp(I*a) * exp(-I*b)
    rw [show I * ↑(Complex.arg (Complex.Gamma ((1:ℂ)/4 + ↑t/2 * I)) -
        t / 2 * Real.log Real.pi) =
      I * ↑(Complex.arg (Complex.Gamma ((1:ℂ)/4 + ↑t/2 * I))) +
      (-(I * ↑(t / 2 * Real.log Real.pi))) from by push_cast; ring]
    rw [Complex.exp_add]
    congr 1
    -- Show: exp(I * arg(Γ(w))) = Γ(w) / ‖Γ(w)‖
    have hw_ne : Complex.Gamma ((1:ℂ)/4 + ↑t/2 * I) ≠ 0 := gamma_quarter_ne_zero t
    have h_norm_ne : (↑‖Complex.Gamma ((1:ℂ)/4 + ↑t/2 * I)‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw_ne)
    rw [eq_div_iff h_norm_ne, mul_comm]
    -- Goal: ↑‖Γ(w)‖ * exp(I * ↑(arg(Γ(w)))) = Γ(w)
    -- From norm_mul_exp_arg_mul_I: ↑‖z‖ * exp(↑(arg z) * I) = z
    have h := Complex.norm_mul_exp_arg_mul_I (Complex.Gamma ((1:ℂ)/4 + ↑t/2 * I))
    rwa [show ↑(Complex.arg (Complex.Gamma ((1:ℂ)/4 + ↑t/2 * I))) * I =
      I * ↑(Complex.arg (Complex.Gamma ((1:ℂ)/4 + ↑t/2 * I))) from mul_comm _ _] at h
  rw [h_factor]
  -- Step 2: Prove the factored form is continuous
  -- Gamma(1/4 + t/2*I) is continuous (differentiable for Re > 0)
  have h_gamma_cont : Continuous (fun t : ℝ => Complex.Gamma ((1:ℂ)/4 + ↑t/2 * I)) := by
    have h_input : Continuous (fun t : ℝ => (1/4 : ℂ) + ↑t/2 * I) :=
      continuous_const.add ((continuous_ofReal.div_const 2).mul continuous_const)
    refine continuous_iff_continuousAt.mpr (fun t => ?_)
    have h_not_neg_int : ∀ m : ℕ, (1/4 : ℂ) + ↑t/2 * I ≠ -m := fun m => by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.mul_re,
                 Complex.I_re, Complex.I_im, mul_zero] at hre
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      norm_num at hre; linarith
    refine ContinuousAt.comp ?_ h_input.continuousAt
    exact (Complex.differentiableAt_Gamma _ h_not_neg_int).continuousAt
  apply Continuous.mul
  · -- Γ(w)/‖Γ(w)‖ is continuous (nonzero denominator)
    exact h_gamma_cont.div₀
      (continuous_ofReal.comp (continuous_norm.comp h_gamma_cont))
      (fun t => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (gamma_quarter_ne_zero t)))
  · -- exp(-I · t/2 · log(π)) is continuous
    exact Complex.continuous_exp.comp
      (Continuous.neg (continuous_const.mul
        (continuous_ofReal.comp ((continuous_id.div_const 2).mul continuous_const))))

/-- Z is continuous.

We factor Z(t) = exp(I·θ(t)) · ζ(1/2+it). The second factor is continuous because ζ
is differentiable away from s = 1 (and 1/2+it ≠ 1). The first factor is continuous
by `exp_I_theta_continuous` (which bypasses the discontinuous θ via exp(I·arg(z)) = z/‖z‖). -/
theorem hardyZ_continuous : Continuous hardyZ := by
  unfold hardyZ
  apply Continuous.mul
  · -- exp(I * θ(t)) is continuous (bypasses theta's branch cut discontinuity)
    exact exp_I_theta_continuous
  · -- ζ(1/2 + it) is continuous (ζ is differentiable on ℂ \ {1}, and Re(1/2+it)=1/2 ≠ 1)
    have h_input_cont : Continuous (fun t : ℝ => (1/2 : ℂ) + t * I) := by
      apply Continuous.add continuous_const
      exact Continuous.mul continuous_ofReal continuous_const
    have h_ne_one : ∀ t : ℝ, (1/2 : ℂ) + t * I ≠ 1 := by
      intro t h
      have : ((1/2 : ℂ) + t * I).re = (1 : ℂ).re := by rw [h]
      simp at this
    refine continuous_iff_continuousAt.mpr (fun t => ?_)
    show ContinuousAt (riemannZeta ∘ (fun t : ℝ => (1/2 : ℂ) + t * I)) t
    exact ContinuousAt.comp (differentiableAt_riemannZeta (h_ne_one t)).continuousAt
      h_input_cont.continuousAt

/-- Z is continuous as a real-valued function on ℝ -/
theorem hardyZ_real_val_continuous : Continuous hardyZ_real_val := by
  unfold hardyZ_real_val
  exact continuous_re.comp hardyZ_continuous

/-- Z(t) is not identically zero

**BLOCKED:** Requires showing ζ(1/2 + it) ≠ 0 for some specific t.
The numerical fact is that the first zero on the critical line has
imaginary part ≈ 14.134725..., so ζ(1/2 + i) ≠ 0.

This is a NUMERICAL fact not directly provable from Mathlib's current
infrastructure. Options:
1. Axiomatize as a numerical assumption
2. Use analytic continuation from ζ(2) ≠ 0 (requires careful path tracking)
3. Wait for Mathlib to add explicit zero locations
-/
theorem hardyZ_not_zero : ∃ t : ℝ, hardyZ t ≠ 0 := by
  -- Proof by contradiction using the identity theorem
  -- If Z(t) = 0 for all t, then ζ = 0 on critical line, contradicting ζ(2) ≠ 0
  by_contra h
  push_neg at h
  -- h : ∀ t, hardyZ t = 0
  -- This means ζ(1/2 + it) = 0 for all t (since exp ≠ 0)
  have hζ_zero : ∀ t : ℝ, riemannZeta (1/2 + t * I) = 0 := fun t => by
    have := h t
    rwa [hardyZ_zero_iff] at this
  -- ζ(2) = π²/6 ≠ 0
  have hζ_two_ne : riemannZeta 2 ≠ 0 := by
    rw [riemannZeta_two]
    apply div_ne_zero
    · exact pow_ne_zero 2 (ofReal_ne_zero.mpr Real.pi_ne_zero)
    · norm_num
  -- ζ is differentiable (hence analytic) on ℂ \ {1}
  have hζ_diff : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ := fun s hs =>
    (differentiableAt_riemannZeta (Set.mem_compl_singleton_iff.mp hs)).differentiableWithinAt
  have hζ_analytic : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    hζ_diff.analyticOnNhd isOpen_compl_singleton
  -- ℂ \ {1} is connected (since dim_ℝ(ℂ) = 2 > 1)
  have hU_connected : IsConnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.finrank_real_complex]) 1
  -- 1/2 ∈ ℂ \ {1}
  have h_half_mem : (1/2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    norm_num
  -- 2 ∈ ℂ \ {1}
  have h_two_mem : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    norm_num
  -- If ζ = 0 on critical line, 1/2 is in the closure of zeros (excluding 1/2)
  -- The points 1/2 + t*I for t ≠ 0 all have ζ = 0, and they approach 1/2
  have h_in_closure : (1/2 : ℂ) ∈ closure ({z | riemannZeta z = 0} \ {1/2}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    -- Take t = min(ε/2, 1) as a REAL number
    set t : ℝ := min (ε/2) 1 with ht_def
    have ht_pos : 0 < t := lt_min (by linarith) (by norm_num)
    use 1/2 + t * I
    constructor
    · -- In the set of zeros minus {1/2}
      constructor
      · -- ζ(1/2 + t*I) = 0
        simp only [Set.mem_setOf_eq]
        exact hζ_zero t
      · -- Not equal to 1/2
        simp only [Set.mem_singleton_iff]
        intro heq
        -- From heq: 1/2 + t*I = 1/2, so t*I = 0
        have h1 : (t : ℂ) * I = 0 := by
          have : (1/2 : ℂ) + (t : ℂ) * I - 1/2 = 0 := by rw [heq]; ring
          simpa using this
        -- t*I = 0 implies t = 0 (since I ≠ 0)
        rw [mul_eq_zero] at h1
        cases h1 with
        | inl h => exact absurd (Complex.ofReal_eq_zero.mp h) (ne_of_gt ht_pos)
        | inr h => exact Complex.I_ne_zero h
    · -- dist < ε
      rw [dist_eq_norm]
      -- Goal: ‖1/2 - (1/2 + t*I)‖ < ε, which simplifies to ‖-t*I‖
      have hsub : (1/2 : ℂ) - (1/2 + (t : ℂ) * I) = -((t : ℂ) * I) := by ring
      rw [hsub, norm_neg]
      calc ‖(t : ℂ) * I‖ = ‖(t : ℂ)‖ * ‖I‖ := norm_mul _ _
        _ = |t| * 1 := by simp only [Complex.norm_real, Complex.norm_I, Real.norm_eq_abs]
        _ = t := by rw [abs_of_pos ht_pos, mul_one]
        _ ≤ ε/2 := min_le_left _ _
        _ < ε := by linarith
  -- By identity theorem: ζ = 0 on all of ℂ \ {1}
  have hζ_eq_zero : Set.EqOn riemannZeta 0 {(1 : ℂ)}ᶜ :=
    hζ_analytic.eqOn_zero_of_preconnected_of_mem_closure
      hU_connected.isPreconnected h_half_mem h_in_closure
  -- But ζ(2) ≠ 0 and 2 ∈ ℂ \ {1}
  have hζ_two_zero : riemannZeta 2 = 0 := hζ_eq_zero h_two_mem
  exact hζ_two_ne hζ_two_zero

/-- Growth bound: |Z(t)| = O(t^{1/2}) (crude Lindelöf-type bound)

The Phragmén-Lindelöf convexity principle gives |ζ(1/2 + it)| = O(|t|^{1/4+ε}).
Since Z(t) = exp(iθ(t)) ζ(1/2+it) and |exp(iθ)| = 1, we get |Z(t)| = O(|t|^{1/4+ε}).

We prove the slightly weaker bound |Z(t)| = O(|t|^{1/2}) which suffices for applications.
-/
theorem hardyZ_growth_bound :
    ∃ A C : ℝ, 0 < C ∧ ∀ t : ℝ, |t| ≥ 1 → ‖hardyZ t‖ ≤ C * |t| ^ A := by
  -- Use the Phragmén-Lindelöf bound from PhragmenLindelof.lean
  -- hardyZ t = exp(I * θ(t)) * ζ(1/2 + t*I)
  -- |hardyZ t| = |exp(I*θ)| * |ζ(1/2 + t*I)| = 1 * |ζ(1/2 + t*I)|
  -- By zeta_critical_line_bound: |ζ(1/2 + t*I)| ≤ C * |t|^{1/2}
  obtain ⟨C, hC_pos, hC_bound⟩ := zeta_critical_line_bound
  use 1/2, C, hC_pos
  intro t ht
  -- hardyZ t = exp(iθ) * ζ(s) where s = 1/2 + t*I
  unfold hardyZ
  -- |exp(iθ) * ζ(s)| = |exp(iθ)| * |ζ(s)| = 1 * |ζ(s)|
  rw [norm_mul]
  have h_exp_norm : ‖Complex.exp (I * riemannSiegelTheta t)‖ = 1 := by
    rw [show I * (riemannSiegelTheta t : ℂ) = (riemannSiegelTheta t : ℂ) * I from mul_comm _ _]
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [h_exp_norm, one_mul]
  -- Apply the Phragmén-Lindelöf bound
  have h_eq : riemannZeta (1/2 + ↑t * I) = riemannZeta ((1:ℂ)/2 + t * I) := by
    congr 1
  rw [h_eq]
  exact hC_bound t ht

/-- **Connection to Schmidt's Oscillation Lemma**

The explicit formula for ψ(x) gives:
  ψ(x) = x - Σ_{ρ} x^ρ/ρ - log(2π) - ½ log(1 - x⁻²)

where the sum is over non-trivial zeros ρ = β + iγ of ζ(s).
Under RH (all β = 1/2), this becomes:

  ψ(x) - x = - Σ_γ x^{1/2+iγ}/(1/2+iγ) + lower order
            = - x^{1/2} Σ_γ (x^{iγ})/(1/2+iγ) + lower order

Writing x^{iγ} = e^{iγ log x} = cos(γ log x) + i sin(γ log x), this is:

  ψ(x) - x = x^{1/2} Σ_γ c_γ cos(γ log x + φ_γ) + o(x^{1/2})

where c_γ = 2/|1/2+iγ| and φ_γ are phase shifts from the complex coefficients.

**This is exactly the form required by `schmidt_oscillation_lemma_finite`.**

By truncating to a finite set S of zeros with non-zero coefficients,
and bounding the tail by o(x^{1/2}), Schmidt's lemma gives:
  ψ(x) - x > 0 for arbitrarily large x, AND
  ψ(x) - x < 0 for arbitrarily large x.

The analogous argument for Z(t) uses the approximate functional equation:
  Z(t) = 2 Σ_{n≤N} n^{-1/2} cos(θ(t) - t log n) + O(t^{-1/4})
which is a trigonometric sum whose non-vanishing forces sign changes.
-/
theorem schmidt_implies_sign_changes
    (S : Finset ℝ) (hS : S.Nonempty) (hS_pos : ∀ γ ∈ S, 0 < γ)
    (c : ℝ → ℝ) (ph : ℝ → ℝ) (hc : ∀ γ ∈ S, c γ ≠ 0)
    (h_distinct : (S : Set ℝ).Pairwise (· ≠ ·))
    (h_rep : Asymptotics.IsLittleO Filter.atTop
      (fun x => hardyZ_real_val x - (x + ∑ γ ∈ S, c γ * x^(1/2:ℝ) * Real.cos (γ * Real.log x + ph γ)))
      (fun x => x^(1/2:ℝ))) :
    (∀ M, ∃ x > M, hardyZ_real_val x - x > 0) ∧
    (∀ M, ∃ x > M, hardyZ_real_val x - x < 0) :=
  schmidt_oscillation_lemma_finite hS hS_pos c ph hc h_distinct h_rep

/-- The key oscillation lemma: Z changes sign in [T, 2T] for large T.

**THIS IS THE CORE OF HARDY'S 1914 THEOREM**

Hardy's proof uses an integral representation of Z(t) and shows that
the integral of Z(t)² over [T, 2T] is O(T), while if Z didn't change
sign it would be Ω(T log T), giving a contradiction.

The connection to Schmidt's oscillation lemma (`schmidt_implies_sign_changes`)
provides the structural argument: once we establish the explicit formula
representation of Z(t) as a trigonometric sum, Schmidt's lemma guarantees
the sign changes. The remaining work is:
1. Establishing the explicit formula representation for Z(t)
2. Bounding the tail of the series (o(x^{1/2}) error term)
3. Verifying the non-vanishing of coefficients c_γ

See `schmidt_oscillation_lemma_finite` in SchmidtOscillation.lean.
-/
theorem hardyZ_sign_change_in_interval :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, ∃ t₁ t₂ : ℝ,
      t₁ ∈ Set.Icc T (2*T) ∧ t₂ ∈ Set.Icc T (2*T) ∧
      hardyZ_real_val t₁ > 0 ∧ hardyZ_real_val t₂ < 0 := by
  -- PROOF STRATEGY (via Schmidt's Oscillation Lemma):
  --
  -- By the approximate functional equation (Riemann-Siegel formula):
  --   Z(t) = 2 Σ_{n≤N(t)} n^{-1/2} cos(θ(t) - t log n) + O(t^{-1/4})
  --
  -- This is a finite trigonometric sum with non-vanishing coefficients.
  -- By `schmidt_oscillation_lemma_finite`, any function with such a
  -- representation must oscillate: it takes both positive and negative
  -- values for arbitrarily large arguments.
  --
  -- To get the stronger interval form [T, 2T], we use:
  -- - The Ω_± result from `schmidt_implies_sign_changes` gives sign changes
  --   beyond any bound
  -- - The continuity of Z(t) (`hardyZ_continuous`) and the growth bound
  --   (`hardyZ_growth_bound`) ensure the sign changes can be localized
  --   to intervals [T, 2T]
  --
  -- The formal proof requires:
  -- 1. Riemann-Siegel approximate functional equation (explicit formula)
  -- 2. Non-vanishing of leading coefficients (from critical zeros)
  -- 3. Tail bounds matching the o(x^{1/2}) requirement
  -- See `CriticalZeros.lean` for the zero infrastructure.
  sorry

/-- Using IVT: sign change implies zero -/
theorem sign_change_gives_zero (t₁ t₂ : ℝ) (ht : t₁ < t₂)
    (h_pos : hardyZ_real_val t₁ > 0) (h_neg : hardyZ_real_val t₂ < 0) :
    ∃ t ∈ Set.Ioo t₁ t₂, hardyZ t = 0 := by
  -- By intermediate value theorem for continuous real functions
  have hcont : ContinuousOn hardyZ_real_val (Set.Icc t₁ t₂) :=
    hardyZ_real_val_continuous.continuousOn
  -- 0 ∈ (hardyZ_real_val t₂, hardyZ_real_val t₁) since f(t₂) < 0 < f(t₁)
  have h0_mem : (0 : ℝ) ∈ Set.Ioo (hardyZ_real_val t₂) (hardyZ_real_val t₁) := ⟨h_neg, h_pos⟩
  -- Apply IVT (the ' version handles f(b) < y < f(a) case)
  have hivt := intermediate_value_Ioo' (le_of_lt ht) hcont h0_mem
  -- hivt : 0 ∈ hardyZ_real_val '' Ioo t₁ t₂
  obtain ⟨t, ht_mem, ht_zero⟩ := hivt
  refine ⟨t, ht_mem, ?_⟩
  -- hardyZ_real_val t = 0, and hardyZ t = (hardyZ t).re since hardyZ is real-valued
  rw [hardyZ_eq_re t]
  -- ht_zero : hardyZ_real_val t = 0, i.e., (hardyZ t).re = 0
  simp only [hardyZ_real_val] at ht_zero
  simp only [ht_zero, Complex.ofReal_zero]

/-- Sign changes of Z(t) correspond to zeros on the critical line.

If Z(t₁) > 0 and Z(t₂) < 0 (or vice versa), then there exists
t ∈ (t₁, t₂) such that ζ(1/2 + it) = 0.
-/
theorem sign_change_implies_zero (t₁ t₂ : ℝ) (ht : t₁ < t₂)
    (h1 : hardyZ_real_val t₁ * hardyZ_real_val t₂ < 0) :
    ∃ t ∈ Set.Ioo t₁ t₂, riemannZeta (1/2 + t * I) = 0 := by
  -- From h1: a * b < 0 means one positive, one negative
  have hne1 : hardyZ_real_val t₁ ≠ 0 := fun h => by simp [h] at h1
  -- Case split on sign of hardyZ_real_val t₁
  rcases lt_trichotomy (hardyZ_real_val t₁) 0 with h1_neg | h1_eq | h1_pos
  · -- Case 1: hardyZ_real_val t₁ < 0
    -- Then hardyZ_real_val t₂ > 0 (since product < 0)
    have h2_pos : hardyZ_real_val t₂ > 0 := by
      by_contra h
      push_neg at h
      have ha' : 0 ≤ -(hardyZ_real_val t₁) := neg_nonneg.mpr (le_of_lt h1_neg)
      have hb' : 0 ≤ -(hardyZ_real_val t₂) := neg_nonneg.mpr h
      have hprod : 0 ≤ (-(hardyZ_real_val t₁)) * (-(hardyZ_real_val t₂)) := mul_nonneg ha' hb'
      have : hardyZ_real_val t₁ * hardyZ_real_val t₂ ≥ 0 := by linarith [hprod]
      linarith
    -- Use IVT: 0 ∈ (f(t₁), f(t₂)) since f(t₁) < 0 < f(t₂)
    have hcont : ContinuousOn hardyZ_real_val (Set.Icc t₁ t₂) :=
      hardyZ_real_val_continuous.continuousOn
    have h0_mem : (0 : ℝ) ∈ Set.Ioo (hardyZ_real_val t₁) (hardyZ_real_val t₂) := ⟨h1_neg, h2_pos⟩
    have hivt := intermediate_value_Ioo (le_of_lt ht) hcont h0_mem
    obtain ⟨t, ht_mem, ht_zero⟩ := hivt
    refine ⟨t, ht_mem, ?_⟩
    rw [← hardyZ_zero_iff, hardyZ_eq_re t]
    simp only [hardyZ_real_val] at ht_zero
    simp only [ht_zero, Complex.ofReal_zero]
  · -- Case 2: hardyZ_real_val t₁ = 0 (contradiction)
    exact (hne1 h1_eq).elim
  · -- Case 3: hardyZ_real_val t₁ > 0
    -- Then hardyZ_real_val t₂ < 0 (since product < 0)
    have h2_neg : hardyZ_real_val t₂ < 0 := by
      by_contra h
      push_neg at h
      have : hardyZ_real_val t₁ * hardyZ_real_val t₂ ≥ 0 :=
        mul_nonneg (le_of_lt h1_pos) h
      linarith
    -- Use sign_change_gives_zero directly
    have hsz := sign_change_gives_zero t₁ t₂ ht h1_pos h2_neg
    obtain ⟨t, ht_mem, ht_zero⟩ := hsz
    exact ⟨t, ht_mem, (hardyZ_zero_iff t).mp ht_zero⟩

/-- Combining sign change detection with hardyZ_zero_iff gives Hardy's theorem -/
theorem hardy_from_sign_changes :
    (∃ T₀ : ℝ, ∀ T ≥ T₀, ∃ t ∈ Set.Icc T (2*T), hardyZ t = 0) →
    ∀ T : ℝ, ∃ t : ℝ, t > T ∧ riemannZeta (1/2 + t * I) = 0 := by
  intro hsc T
  -- For large enough T' ≥ max(T, T₀), get a zero in [T', 2T']
  -- That zero is > T
  obtain ⟨T₀, hT₀⟩ := hsc
  specialize hT₀ (max (T + 1) T₀) (le_max_right _ _)
  obtain ⟨t, ht_mem, ht_zero⟩ := hT₀
  refine ⟨t, ?_, ?_⟩
  · have : t ≥ max (T + 1) T₀ := ht_mem.1
    linarith [le_max_left (T + 1) T₀]
  · rwa [← hardyZ_zero_iff]

-- ============================================================
-- SECTION 5: Hardy's theorem (stub)
-- ============================================================

/-- Hardy's Theorem: There are infinitely many zeros on the critical line.

More precisely: For all T > 0, there exists t > T such that ζ(1/2 + it) = 0.
-/
theorem hardy_infinitely_many_zeros_stub :
    ∀ T : ℝ, ∃ t : ℝ, t > T ∧ riemannZeta (1/2 + t * I) = 0 := by
  -- This follows from hardyZ_sign_change_in_interval via the already-proved machinery
  -- Step 1: hardyZ_sign_change_in_interval → sign changes in each [T, 2T]
  -- Step 2: sign changes → zeros via sign_change_implies_zero (PROVED)
  -- Step 3: Combine using hardy_from_sign_changes (PROVED)
  apply hardy_from_sign_changes
  -- Need: ∃ T₀, ∀ T ≥ T₀, ∃ t ∈ [T, 2T], hardyZ t = 0
  -- This follows from hardyZ_sign_change_in_interval via IVT
  obtain ⟨T₀, hT₀⟩ := hardyZ_sign_change_in_interval
  use T₀
  intro T hT
  obtain ⟨t₁, t₂, ht₁_mem, ht₂_mem, h_pos, h_neg⟩ := hT₀ T hT
  -- Have sign change: t₁, t₂ ∈ [T, 2T] with opposite signs
  -- By sign_change_implies_zero, there's a zero between them
  have hprod : hardyZ_real_val t₁ * hardyZ_real_val t₂ < 0 := by
    have hp : 0 < hardyZ_real_val t₁ := h_pos
    have hn : hardyZ_real_val t₂ < 0 := h_neg
    nlinarith
  -- Need t₁ < t₂ or t₂ < t₁
  rcases lt_trichotomy t₁ t₂ with h_lt | h_eq | h_gt
  · -- t₁ < t₂
    obtain ⟨t, ht_in, ht_zero⟩ := sign_change_implies_zero t₁ t₂ h_lt hprod
    use t
    constructor
    · -- t ∈ [T, 2T]: since t ∈ (t₁, t₂) ⊆ [T, 2T]
      constructor
      · have h1 : T ≤ t₁ := ht₁_mem.1
        linarith [ht_in.1]
      · have h2 : t₂ ≤ 2*T := ht₂_mem.2
        linarith [ht_in.2]
    · exact (hardyZ_zero_iff t).mpr ht_zero
  · -- t₁ = t₂: contradiction since they have opposite signs
    subst h_eq
    -- hprod : hardyZ_real_val t₁ * hardyZ_real_val t₁ < 0, but x * x ≥ 0
    have hsq : 0 ≤ hardyZ_real_val t₁ * hardyZ_real_val t₁ := mul_self_nonneg _
    linarith
  · -- t₁ > t₂
    have hprod' : hardyZ_real_val t₂ * hardyZ_real_val t₁ < 0 := by linarith
    obtain ⟨t, ht_in, ht_zero⟩ := sign_change_implies_zero t₂ t₁ h_gt hprod'
    use t
    constructor
    · constructor
      · have h1 : T ≤ t₂ := ht₂_mem.1
        linarith [ht_in.1]
      · have h2 : t₁ ≤ 2*T := ht₁_mem.2
        linarith [ht_in.2]
    · exact (hardyZ_zero_iff t).mpr ht_zero

-- ============================================================
-- SECTION 6: Gap Analysis
-- ============================================================

/-
## Gap Analysis for Hardy's Theorem

### What We Can Define/State Now:
1. ✓ Riemann-Siegel theta function (defined above)
2. ✓ Hardy Z-function (defined above)
3. ✓ Connection between Z(t) zeros and ζ zeros (stated, needs proof)
4. ✓ Statement of Hardy's theorem

### What Needs Substantial Work:

1. **Z(t) is Real:**
   - Requires detailed analysis of functional equation
   - Need to track phases carefully
   - Proof difficulty: HARD

2. **Sign Change Detection:**
   - Need to show Z(t) changes sign infinitely often
   - Hardy's approach: integral representations
   - Proof difficulty: VERY HARD

3. **Asymptotic Analysis:**
   - θ(t) asymptotics from Stirling
   - Z(t) behavior for large t
   - Proof difficulty: HARD

4. **Density Lower Bound:**
   - Showing proportion of zeros on critical line
   - More refined than just "infinitely many"
   - Proof difficulty: VERY HARD

### Why Hardy's Theorem is Hard to Formalize:

1. The original proof uses detailed asymptotic analysis
2. Requires careful handling of oscillatory integrals
3. The Riemann-Siegel formula is complex
4. Sign change arguments need continuity + explicit bounds

### Potential Approaches:

1. **Direct:** Formalize Hardy's original argument
   - Most faithful to the mathematics
   - Requires significant Mathlib extensions

2. **Indirect:** Use known results about zero density
   - Requires even more machinery (density theorems)
   - May be harder overall

3. **Axiomatic:** Assume key properties and derive structure
   - Current approach: define concepts, leave proofs as sorry
   - Allows exploring the logical structure
-/

end Littlewood.Development.HardyTheorem
