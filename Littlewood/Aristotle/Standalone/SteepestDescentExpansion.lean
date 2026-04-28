/-
Constructive steepest-descent expansion infrastructure for the Riemann-Siegel
remainder.

This file isolates the hypothesis-free functional-equation side of the
Riemann-Siegel expansion that had previously lived inside
`RSExpansionProof.lean` under ambient analytic typeclass assumptions.

What is constructed here:

1. The forward and reflected zeta remainders on the critical line.
2. The exact functional-equation decomposition of the forward remainder into
   a polynomial-mismatch term and a reflected-tail term.
3. The FE leading term `rsLeadingFromFE` on each RS block.
4. A direct constructor that packages the three analytic leaves into an
   instance of `SiegelSaddleExpansionHyp`.

This is constructive and hypothesis-free, but it does **not** yet prove the
final contour-to-saddle estimate on `saddlePointRemainder`. That remaining
analytic leaf is still the bridge from the FE decomposition to the Gabcke
coefficient bounds.
-/

import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.FunctionalEquationV2
import Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.SteepestDescentExpansion

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.HardyNProperties Aristotle.RSBlockParam
open Aristotle.ErrorTermExpansion

/-! ## Block-local Dirichlet data -/

/-- On block `k`, the Dirichlet cutoff is constant on the open block. -/
theorem hardyN_on_open_block (k : ℕ) (t : ℝ)
    (ht_lo : hardyStart k ≤ t) (ht_hi : t < hardyStart (k + 1)) :
    hardyN t = k + 1 :=
  hardyN_constant_on_block k t ht_lo ht_hi

/-- The complex partial Dirichlet sum `∑_{n≤N(t)} n^{-s}` at `s = 1/2 + it`. -/
def complexPartialSum (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (hardyN t),
    ((n + 1 : ℂ)) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))

/-- The forward zeta remainder `ζ(1/2+it) - ∑_{n≤N(t)} n^{-s}`. -/
def complexZetaRemainder (t : ℝ) : ℂ :=
  riemannZeta (1 / 2 + Complex.I * (t : ℂ)) - complexPartialSum t

/-- Rewriting one summand of the rotated partial sum in cosine form. -/
theorem cpow_re_cos (n : ℕ) (t : ℝ) :
    (Complex.exp (Complex.I * hardyTheta t) *
      ((n + 1 : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)))).re =
    ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
      Real.cos (hardyTheta t - t * Real.log (n + 1)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn_ne : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  have h_cpow :
      (n + 1 : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) =
        Complex.exp (Complex.log (n + 1 : ℂ) * (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))) :=
    Complex.cpow_def_of_ne_zero hn_ne _
  rw [h_cpow]
  have h_log : Complex.log (n + 1 : ℂ) = ((Real.log (n + 1 : ℝ)) : ℂ) := by
    rw [show (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) from by push_cast; ring]
    exact (Complex.ofReal_log (le_of_lt hn_pos)).symm
  rw [h_log, ← Complex.exp_add]
  set L := Real.log ((n : ℝ) + 1)
  have h_exp :
      Complex.I * ↑(hardyTheta t) + ↑L * (-(1 / 2) - Complex.I * ↑t) =
        ↑(-(L / 2)) + ↑(hardyTheta t - t * L) * Complex.I := by
    push_cast
    ring
  rw [h_exp, Complex.exp_add_mul_I]
  simp only [Complex.mul_re, Complex.exp_ofReal_re, Complex.exp_ofReal_im,
    Complex.add_re, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  ring_nf
  have h_rpow : Real.exp (L * (-1 / 2 : ℝ)) = (1 + ↑n) ^ ((-1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 1 + ↑n)]
    congr 1
    simp only [L]
    ring
  rw [h_rpow]
  ring

/-- `MainTerm` is twice the real part of the rotated partial sum. -/
theorem mainTerm_eq_two_re_rotated_sum (t : ℝ) :
    MainTerm t =
      2 * (Complex.exp (Complex.I * hardyTheta t) * complexPartialSum t).re := by
  unfold MainTerm complexPartialSum
  congr 1
  rw [Finset.mul_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun n _ => (cpow_re_cos n t).symm

/-- ErrorTerm as the rotated zeta value minus twice the rotated partial sum. -/
theorem errorTerm_structure (t : ℝ) :
    ErrorTerm t =
      (Complex.exp (Complex.I * hardyTheta t) *
          riemannZeta (1 / 2 + Complex.I * (t : ℂ))).re -
        2 * (Complex.exp (Complex.I * hardyTheta t) * complexPartialSum t).re := by
  rw [show ErrorTerm t = hardyZ t - MainTerm t from rfl]
  rw [mainTerm_eq_two_re_rotated_sum]
  rfl

/-- The standard remainder form of `ErrorTerm`. -/
theorem errorTerm_eq_re_remainder (t : ℝ) :
    ErrorTerm t =
      (Complex.exp (Complex.I * hardyTheta t) * complexZetaRemainder t).re -
        (Complex.exp (Complex.I * hardyTheta t) * complexPartialSum t).re := by
  unfold complexZetaRemainder
  rw [mul_sub, Complex.sub_re, errorTerm_structure]
  ring

/-! ## Functional equation on the critical line -/

/-- The critical-line chi-factor in the Riemann-Siegel normalization. -/
def chiFactor (t : ℝ) : ℂ :=
  2 * (2 * ↑Real.pi) ^ (-(1 / 2 + Complex.I * (t : ℂ))) *
    Complex.Gamma (1 / 2 + Complex.I * (t : ℂ)) *
    Complex.cos (↑Real.pi * (1 / 2 + Complex.I * (t : ℂ)) / 2)

/-- The reflected Dirichlet sum at `1 - s = 1/2 - it`. -/
def reflectedPartialSum (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (hardyN t),
    ((n + 1 : ℂ)) ^ (-(1 / 2 : ℂ) + Complex.I * (t : ℂ))

/-- The reflected zeta remainder at `1/2 - it`. -/
def reflectedZetaRemainder (t : ℝ) : ℂ :=
  riemannZeta (1 / 2 - Complex.I * (t : ℂ)) - reflectedPartialSum t

/-- Functional equation specialized to `s = 1/2 + it`. -/
theorem zeta_fe_critical_line (t : ℝ) (ht : t ≠ 0) :
    riemannZeta (1 / 2 - Complex.I * (t : ℂ)) =
      2 * (2 * ↑Real.pi) ^ (-(1 / 2 + Complex.I * (t : ℂ))) *
        Complex.Gamma (1 / 2 + Complex.I * (t : ℂ)) *
        Complex.cos (↑Real.pi * (1 / 2 + Complex.I * (t : ℂ)) / 2) *
        riemannZeta (1 / 2 + Complex.I * (t : ℂ)) := by
  have h_ne_nat : ∀ n : ℕ, (1 / 2 + Complex.I * (t : ℂ) : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hre := congr_arg Complex.re h
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im] at hre
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h_ne_one : (1 / 2 + Complex.I * (t : ℂ) : ℂ) ≠ 1 := by
    intro h
    have him := congr_arg Complex.im h
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.one_im] at him
    exact ht him
  have h_fe := riemannZeta_one_sub h_ne_nat h_ne_one
  convert h_fe using 2
  ring

/-- The critical-line FE rewritten using `chiFactor`. -/
theorem zeta_reflected_via_fe (t : ℝ) (ht : t ≠ 0) :
    riemannZeta (1 / 2 - Complex.I * (t : ℂ)) =
      chiFactor t * riemannZeta (1 / 2 + Complex.I * (t : ℂ)) := by
  unfold chiFactor
  simpa [mul_assoc] using zeta_fe_critical_line t ht

/-- The chi-factor is nonzero on the critical line. -/
theorem chiFactor_ne_zero (t : ℝ) (ht : t ≠ 0) : chiFactor t ≠ 0 := by
  have hpow : (2 * (2 * ↑Real.pi) ^ (-(1 / 2 + Complex.I * (t : ℂ))) : ℂ) ≠ 0 := by
    refine mul_ne_zero (by norm_num) ?_
    have hbase : ((2 : ℂ) * ↑Real.pi) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [Complex.cpow_def_of_ne_zero hbase]
    exact Complex.exp_ne_zero _
  have hgamma : Complex.Gamma (1 / 2 + Complex.I * (t : ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    have hre := congr_arg Complex.re h
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im] at hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hcos : Complex.cos (↑Real.pi * (1 / 2 + Complex.I * (t : ℂ)) / 2) ≠ 0 := by
    intro hcos
    rcases (Complex.cos_eq_zero_iff).mp hcos with ⟨k, hk⟩
    have him := congr_arg Complex.im hk
    simp [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] at him
    exact ht him
  simpa [chiFactor, mul_assoc] using mul_ne_zero (mul_ne_zero hpow hgamma) hcos

/-- Definitional decomposition of the reflected zeta value. -/
theorem reflected_zeta_decomp (t : ℝ) :
    riemannZeta (1 / 2 - Complex.I * (t : ℂ)) =
      reflectedPartialSum t + reflectedZetaRemainder t := by
  unfold reflectedZetaRemainder
  ring

/-- Definitional decomposition of the forward zeta value. -/
theorem forward_zeta_decomp (t : ℝ) :
    riemannZeta (1 / 2 + Complex.I * (t : ℂ)) =
      complexPartialSum t + complexZetaRemainder t := by
  unfold complexZetaRemainder
  ring

/-- The reflected remainder rewritten through the functional equation. -/
theorem reflected_remainder_via_fe (t : ℝ) (ht : t ≠ 0) :
    reflectedZetaRemainder t =
      chiFactor t * (complexPartialSum t + complexZetaRemainder t) -
        reflectedPartialSum t := by
  rw [show complexPartialSum t + complexZetaRemainder t =
      riemannZeta (1 / 2 + Complex.I * (t : ℂ)) from (forward_zeta_decomp t).symm]
  unfold reflectedZetaRemainder
  rw [zeta_reflected_via_fe t ht]

/-- The polynomial-mismatch piece of the FE remainder decomposition. -/
def forwardPolynomialMismatch (t : ℝ) : ℂ :=
  (chiFactor t)⁻¹ * reflectedPartialSum t - complexPartialSum t

/-- The reflected-tail piece of the FE remainder decomposition. -/
def reflectedTailTerm (t : ℝ) : ℂ :=
  (chiFactor t)⁻¹ * reflectedZetaRemainder t

/-- The forward remainder expressed through reflected data. -/
theorem forward_remainder_via_fe (t : ℝ) (ht : t ≠ 0) :
    complexZetaRemainder t =
      (chiFactor t)⁻¹ * (reflectedPartialSum t + reflectedZetaRemainder t) -
        complexPartialSum t := by
  have hchi := chiFactor_ne_zero t ht
  have hzeta :
      riemannZeta (1 / 2 + Complex.I * (t : ℂ)) =
        (chiFactor t)⁻¹ * riemannZeta (1 / 2 - Complex.I * (t : ℂ)) := by
    calc
      riemannZeta (1 / 2 + Complex.I * (t : ℂ)) =
          (chiFactor t)⁻¹ *
            (chiFactor t * riemannZeta (1 / 2 + Complex.I * (t : ℂ))) := by
              rw [inv_mul_cancel_left₀ hchi]
      _ = (chiFactor t)⁻¹ * riemannZeta (1 / 2 - Complex.I * (t : ℂ)) := by
            rw [← zeta_reflected_via_fe t ht]
  rw [← reflected_zeta_decomp]
  unfold complexZetaRemainder
  rw [hzeta]

/-- Exact FE split of the forward remainder into mismatch plus reflected tail. -/
theorem forward_remainder_split (t : ℝ) (ht : t ≠ 0) :
    complexZetaRemainder t =
      forwardPolynomialMismatch t + reflectedTailTerm t := by
  unfold forwardPolynomialMismatch reflectedTailTerm
  rw [forward_remainder_via_fe t ht]
  ring

/-- ErrorTerm decomposed into FE mismatch and reflected tail pieces. -/
theorem errorTerm_fe_decomposition (t : ℝ) (ht : t ≠ 0) :
    ErrorTerm t =
      (Complex.exp (Complex.I * hardyTheta t) * forwardPolynomialMismatch t).re +
        (Complex.exp (Complex.I * hardyTheta t) * reflectedTailTerm t).re -
        (Complex.exp (Complex.I * hardyTheta t) * complexPartialSum t).re := by
  rw [errorTerm_eq_re_remainder t, forward_remainder_split t ht]
  unfold forwardPolynomialMismatch reflectedTailTerm
  rw [mul_add, Complex.add_re]

/-! ## FE leading term -/

/-- The FE-side leading correction: the first term just beyond the forward sum. -/
def rsLeadingFromFE (t : ℝ) : ℂ :=
  (chiFactor t)⁻¹ * ((hardyN t + 1 : ℂ)) ^ (-(1 / 2 : ℂ) + Complex.I * (t : ℂ))

/-- On block `k`, the FE leading term has index `k + 2`. -/
theorem rsLeadingFromFE_on_block_structure (k : ℕ) (t : ℝ)
    (ht_lo : hardyStart k ≤ t) (ht_hi : t < hardyStart (k + 1)) :
    rsLeadingFromFE t =
      (chiFactor t)⁻¹ * ((k + 2 : ℂ)) ^ (-(1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
  unfold rsLeadingFromFE
  have hN := hardyN_on_open_block k t ht_lo ht_hi
  congr 1
  rw [hN]
  push_cast
  ring_nf

/-! ## Packaging the analytic leaf -/

open Aristotle.Standalone.SiegelSaddleExpansionHyp in
/-- Direct constructor for the analytic saddle-expansion interface from its
three theorem fields. This is the exact constructive packaging needed once the
remaining contour-to-saddle estimate is formalized. -/
def mkSiegelSaddleExpansionHyp
    (h_weighted :
      ∀ k : ℕ, ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
        |(((k : ℝ) + 1 + p) *
            saddlePointRemainder k (blockCoord k p))| ≤
          fresnelC1Bound / Real.sqrt (2 * Real.pi))
    (h_signed :
      ∀ k : ℕ, 1 ≤ k → ∀ p : ℝ, p ∈ Ioc (0 : ℝ) 1 →
        0 ≤ (-1 : ℝ) ^ k * saddlePointRemainder k (blockCoord k p))
    (h_antitone :
      ∀ k : ℕ, 1 ≤ k → ∀ p : ℝ, p ∈ Ioc (0 : ℝ) 1 →
        ((k : ℝ) + 2 + p) *
            ((-1 : ℝ) ^ (k + 1) *
              saddlePointRemainder (k + 1) (blockCoord (k + 1) p)) ≤
          ((k : ℝ) + 1 + p) *
            ((-1 : ℝ) ^ k * saddlePointRemainder k (blockCoord k p))) :
    SiegelSaddleExpansionHyp := by
  refine
    { weighted_profile_bound := h_weighted
      signed_nonneg := h_signed
      normalized_antitone := h_antitone }

end Aristotle.Standalone.SteepestDescentExpansion
