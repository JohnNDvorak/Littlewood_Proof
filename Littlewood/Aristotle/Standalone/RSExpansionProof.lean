/-
Constructive proof infrastructure for the Riemann-Siegel expansion on blocks.

## Target
Prove (or reduce to atomic sub-lemmas) the RS expansion:
  ∀ k t, t ∈ [hardyStart k, hardyStart(k+1)] →
    |ErrorTerm t - (-1)^k · (2π/t)^{1/4} · Ψ(blockParam k t)| ≤ C_R · t^{-3/4}

## Architecture

The proof decomposes into:

### Proved constructively
- `blockParam_mem_Icc`: blockParam ∈ [0,1] on closed blocks
- `cpow_re_cos`: Re(e^{iθ}·(n+1)^{-1/2-it}) = (n+1)^{-1/2}·cos(θ-t·log(n+1))
- `mainTerm_eq_two_re_rotated_sum`: MainTerm = 2·Re(e^{iθ}·∑ n^{-s})
- `errorTerm_structure`: ErrorTerm = Re(e^{iθ}·ζ) - 2·Re(e^{iθ}·partial_sum)
- `rsLeadingTerm_abs_le`: |RS leading term| ≤ (2π/t)^{1/4}
- `two_pi_div_t_rpow_quarter`: (2π/t)^{1/4} = (2π)^{1/4}·t^{-1/4}
- `hardyStart_pos'`, `pos_of_in_block`, `hardyN_on_open_block`
- `neg_one_pow_block_eq`, `neg_one_pow_block_alt`
- `zeta_fe_critical_line`: ζ(1/2-it) = χ(1/2+it)·ζ(1/2+it) (functional equation)
- `sqrt_increment_antitone`: √(k+2+p)-√(k+2) ≤ √(k+1+p)-√(k+1) (concavity)
- `signed_errorTerm_nonneg_on_block`: (-1)^k·ErrorTerm ≥ 0 on block k
- `rs_block_interpolation`: wired through rs_saddle_point_bound (0 sorrys)
- `weighted_increment_antitone`: ∫(√(k+2+p)-√(k+2))Ψ ≤ ∫(√(k+1+p)-√(k+1))Ψ (concavity)

### Atomic sorrys (genuine mathematical content)
- `chi_modulus_critical_line`: |χ(1/2+it)| = 1 on the critical line (1 sorry)
- `saddle_point_remainder` / `rs_saddle_point_bound`: Siegel 1932 saddle-point (1 sorry)
- `leading_term_cov`: CoV identity for RS leading term on blocks (1 sorry)
- `rs_block_antitone`: Block monotonicity from c_fn_expansion (1 sorry)

### Proved (was sorry)
- `signed_block_integral_expansion`: CLOSED via leading_term_cov + pointwise RS bound
- `c_fn_expansion`: algebraic from signed_block_integral_expansion (CLOSED)
- `weighted_sqrt_monotone`: ∫√(k+1+p)·Ψ increasing in k (NEW)

SORRY COUNT: 4 (chi_modulus, saddle_point, leading_term_cov, rs_block_antitone)
WARNING COUNT: 4

Reference: Siegel 1932 §3; Edwards Ch. 7 (pp. 136-145);
Titchmarsh §4.16-4.17; Gabcke 1979.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.FunctionalEquationV2
import Littlewood.Bridge.HardyZTransfer
import Littlewood.Aristotle.HardyThetaSmooth

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.RSExpansionProof

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.HardyNProperties Aristotle.RSBlockParam
open Aristotle.ErrorTermExpansion

-- ============================================================
-- Section 1: blockParam ∈ [0,1] on closed blocks (constructive)
-- ============================================================

/-- blockParam is in [0,1] on a closed block. -/
theorem blockParam_mem_Icc (k : ℕ) (t : ℝ)
    (ht_lo : hardyStart k ≤ t) (ht_hi : t ≤ hardyStart (k + 1)) :
    blockParam k t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨blockParam_nonneg k t ht_lo, ?_⟩
  simp only [blockParam]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  suffices h : Real.sqrt (t / (2 * Real.pi)) ≤ (k : ℝ) + 2 by linarith
  have h_sq : t / (2 * Real.pi) ≤ ((k : ℝ) + 2) ^ 2 := by
    rw [div_le_iff₀ hpi]
    have : hardyStart (k + 1) = 2 * Real.pi * ((k : ℝ) + 2) ^ 2 := by
      unfold hardyStart; push_cast; ring
    linarith
  calc Real.sqrt (t / (2 * Real.pi))
      ≤ Real.sqrt (((k : ℝ) + 2) ^ 2) := Real.sqrt_le_sqrt h_sq
    _ = (k : ℝ) + 2 := Real.sqrt_sq (by positivity)

-- ============================================================
-- Section 2: Complex partial sum and structural identities
-- ============================================================

/-- The complex partial Dirichlet sum Σ_{n≤N} n^{-s} at s = 1/2 + it. -/
def complexPartialSum (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (hardyN t),
    ((n + 1 : ℂ)) ^ (-(1/2 : ℂ) - Complex.I * (t : ℂ))

/-- The complex zeta remainder: ζ(1/2+it) - Σ_{n≤N} n^{-s}. -/
def complexZetaRemainder (t : ℝ) : ℂ :=
  riemannZeta (1/2 + Complex.I * (t : ℂ)) - complexPartialSum t

/-- Each term of the complex partial sum satisfies:
    Re(e^{iθ} · (n+1)^{-1/2-it}) = (n+1)^{-1/2} · cos(θ - t·log(n+1))

    This follows from (n+1)^{-1/2-it} = (n+1)^{-1/2} · exp(-it·log(n+1))
    for n+1 > 0 (using `Complex.cpow_def_of_ne_zero`), combined with
    Re(e^{iα} · e^{-iβ}) = cos(α - β). -/
theorem cpow_re_cos (n : ℕ) (t : ℝ) :
    (Complex.exp (Complex.I * hardyTheta t) *
      ((n + 1 : ℂ) ^ (-(1/2 : ℂ) - Complex.I * (t : ℂ)))).re =
    ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) * Real.cos (hardyTheta t - t * Real.log (n + 1)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn_ne : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  -- Rewrite cpow using cpow_def_of_ne_zero: z^w = exp(log(z)*w)
  have h_cpow : (n + 1 : ℂ) ^ (-(1/2 : ℂ) - Complex.I * (t : ℂ)) =
      Complex.exp (Complex.log (n + 1 : ℂ) * (-(1/2 : ℂ) - Complex.I * (t : ℂ))) :=
    Complex.cpow_def_of_ne_zero hn_ne _
  rw [h_cpow]
  -- Complex.log(n+1) = Real.log(n+1) for positive reals
  have h_log : Complex.log (n + 1 : ℂ) = ((Real.log (n + 1 : ℝ)) : ℂ) := by
    rw [show (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) from by push_cast; ring]
    exact (Complex.ofReal_log (le_of_lt hn_pos)).symm
  rw [h_log]
  -- Combine exponents
  rw [← Complex.exp_add]
  set L := Real.log ((n : ℝ) + 1)
  -- Rewrite exponent as -(L/2) + I*(θ - t*L)
  have h_exp : Complex.I * ↑(hardyTheta t) + ↑L * (-(1/2) - Complex.I * ↑t) =
      ↑(-(L/2)) + ↑(hardyTheta t - t * L) * Complex.I := by
    push_cast; ring
  rw [h_exp, Complex.exp_add_mul_I]
  -- Now: (exp(-(L/2)) * (cos(θ-tL) + sin(θ-tL)*I)).re = exp(-(L/2)) * cos(θ-tL)
  simp only [Complex.mul_re, Complex.exp_ofReal_re, Complex.exp_ofReal_im,
    Complex.add_re, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  ring_nf
  -- Goal: rexp (L * (-1/2)) * cos(...) = cos(...) * (1+n)^(-1/2)
  have h_rpow : Real.exp (L * (-1/2)) = (1 + ↑n) ^ ((-1 : ℝ)/2) := by
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 1 + ↑n)]
    congr 1
    simp only [L]
    ring
  rw [h_rpow]; ring

/-- MainTerm equals 2·Re(e^{iθ} · partial_sum).

    This follows from `cpow_re_cos` applied to each term of the sum,
    using Re(e^{iθ} · Σ_n f(n)) = Σ_n Re(e^{iθ} · f(n)) (linearity of Re). -/
theorem mainTerm_eq_two_re_rotated_sum (t : ℝ) :
    MainTerm t = 2 * (Complex.exp (Complex.I * hardyTheta t) * complexPartialSum t).re := by
  unfold MainTerm complexPartialSum
  -- Cancel the factor of 2
  congr 1
  -- Distribute e^{iθ}· into the sum, then take Re of each term
  rw [Finset.mul_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun n _ => (cpow_re_cos n t).symm

/-- ErrorTerm equals hardyZ minus MainTerm (definitional). -/
theorem errorTerm_eq_hardyZ_minus_mainTerm (t : ℝ) :
    ErrorTerm t = hardyZ t - MainTerm t := rfl

/-- ErrorTerm structural decomposition:
    ErrorTerm(t) = Re(e^{iθ}·ζ(1/2+it)) - 2·Re(e^{iθ}·partial_sum(t))

    This connects the real-valued ErrorTerm to the complex zeta function
    and complex partial Dirichlet sum via the phase factor e^{iθ}. -/
theorem errorTerm_structure (t : ℝ) :
    ErrorTerm t = (Complex.exp (Complex.I * hardyTheta t) *
      riemannZeta (1/2 + Complex.I * (t : ℂ))).re -
      2 * (Complex.exp (Complex.I * hardyTheta t) * complexPartialSum t).re := by
  show hardyZ t - MainTerm t = _
  rw [mainTerm_eq_two_re_rotated_sum]
  -- Goal: Re(e^{iθ}·ζ(1/2+It)) - 2*Re(e^{iθ}·∑) = Re(e^{iθ}·ζ(1/2+It)) - 2*Re(e^{iθ}·∑)
  -- These should be definitionally equal after unfolding hardyZ
  -- hardyZ = (e^{iθ}·ζ(1/2+It)).re where hardyTheta uses Complex.I * (t/2)
  -- vs the goal which uses Complex.I * ↑t
  -- The difference may be in the argument convention
  rfl

-- ============================================================
-- Section 3: Block positivity and geometry
-- ============================================================

/-- hardyStart is positive for all k. -/
theorem hardyStart_pos' (k : ℕ) : 0 < hardyStart k := by
  unfold hardyStart; positivity

/-- t is positive when in any block. -/
theorem pos_of_in_block (k : ℕ) (t : ℝ) (ht : hardyStart k ≤ t) : 0 < t :=
  lt_of_lt_of_le (hardyStart_pos' k) ht

/-- On block k, hardyN t = k+1 (open block). -/
theorem hardyN_on_open_block (k : ℕ) (t : ℝ)
    (ht_lo : hardyStart k ≤ t) (ht_hi : t < hardyStart (k + 1)) :
    hardyN t = k + 1 :=
  hardyN_constant_on_block k t ht_lo ht_hi

-- ============================================================
-- Section 4: RS leading term structure
-- ============================================================

/-- The RS leading term on block k: (-1)^k · (2π/t)^{1/4} · Ψ(p). -/
def rsLeadingTerm (k : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
    rsPsi (blockParam k t)

/-- The RS leading term is bounded by (2π/t)^{1/4} on any block. -/
theorem rsLeadingTerm_abs_le (k : ℕ) (t : ℝ) (ht : 0 < t)
    (_ht_lo : hardyStart k ≤ t) (_ht_hi : t ≤ hardyStart (k + 1)) :
    |rsLeadingTerm k t| ≤ (2 * Real.pi / t) ^ ((1 : ℝ) / 4) := by
  unfold rsLeadingTerm
  rw [abs_mul, abs_mul]
  have h1 : |(-1 : ℝ) ^ k| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [h1, one_mul]
  have h_coeff_nn : 0 ≤ (2 * Real.pi / t) ^ ((1 : ℝ) / 4) := by positivity
  rw [abs_of_nonneg h_coeff_nn]
  have h_psi_le : |rsPsi (blockParam k t)| ≤ 1 := by
    unfold rsPsi; exact abs_cos_le_one _
  linarith [mul_le_of_le_one_right h_coeff_nn h_psi_le]

-- ============================================================
-- Section 5: Sign structure
-- ============================================================

/-- (-1)^k = (-1)^{N-1} where N = k+1. -/
theorem neg_one_pow_block_eq (k : ℕ) :
    (-1 : ℝ) ^ k = (-1 : ℝ) ^ (k + 1 - 1) := by
  have h : k + 1 - 1 = k := Nat.succ_sub_one k
  rw [h]

/-- (-1)^k = (-1)^{(k+1)+1}. -/
theorem neg_one_pow_block_alt (k : ℕ) :
    (-1 : ℝ) ^ k = (-1 : ℝ) ^ ((k + 1) + 1) := by
  have : (k + 1) + 1 = k + 2 := by omega
  rw [this, pow_succ, pow_succ]
  ring

-- ============================================================
-- Section 6: (2π/t)^{1/4} factorization
-- ============================================================

/-- (2π/t)^{1/4} = (2π)^{1/4} · t^{-1/4}. -/
theorem two_pi_div_t_rpow_quarter (t : ℝ) (ht : 0 < t) :
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) =
    (2 * Real.pi) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) := by
  have ht_nn : (0 : ℝ) ≤ t := le_of_lt ht
  rw [div_eq_mul_inv, Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (inv_nonneg.mpr ht_nn)]
  congr 1
  rw [show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) from by ring, Real.rpow_neg ht_nn]
  exact Real.inv_rpow ht_nn _

-- ============================================================
-- Section 6a: Functional equation at the critical line
-- ============================================================

/-- Functional equation: ζ(1/2-it) = chi(1/2+it) · ζ(1/2+it) for t ≠ 0,
    where chi(s) = 2·(2π)^{-s}·Γ(s)·cos(πs/2).

    This is the foundation of the Riemann-Siegel formula: the RS correction
    arises from applying this to express the zeta remainder in terms of
    a second Dirichlet sum rotated by the chi factor. -/
theorem zeta_fe_critical_line (t : ℝ) (ht : t ≠ 0) :
    riemannZeta (1/2 - Complex.I * (t : ℂ)) =
    2 * (2 * ↑Real.pi) ^ (-(1/2 + Complex.I * (t : ℂ))) *
    Complex.Gamma (1/2 + Complex.I * (t : ℂ)) *
    Complex.cos (↑Real.pi * (1/2 + Complex.I * (t : ℂ)) / 2) *
    riemannZeta (1/2 + Complex.I * (t : ℂ)) := by
  have h_ne_nat : ∀ n : ℕ, (1/2 + Complex.I * (t : ℂ) : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hre := congr_arg Complex.re h
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im] at hre
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h_ne_one : (1/2 + Complex.I * (t : ℂ) : ℂ) ≠ 1 := by
    intro h
    have him := congr_arg Complex.im h
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.one_im] at him
    exact ht him
  have h_fe := riemannZeta_one_sub h_ne_nat h_ne_one
  convert h_fe using 2
  ring

-- ============================================================
-- Section 6b: Concavity infrastructure for block analysis
-- ============================================================

/-- The increment √(a+p) - √(a) is decreasing in a (concavity of √).
    Specifically, √(k+2+p) - √(k+2) ≤ √(k+1+p) - √(k+1) for p ≥ 0.

    This is the key analytic ingredient for the antitone property of c(k):
    the correction ∫₀¹ (√(k+1+p) - √(k+1))·Ψ(p) dp is decreasing in k. -/
theorem sqrt_increment_antitone (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    Real.sqrt ((k : ℝ) + 2 + p) - Real.sqrt ((k : ℝ) + 2) ≤
    Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hk1p : (0 : ℝ) < (k : ℝ) + 1 + p := by positivity
    have hk2p : (0 : ℝ) < (k : ℝ) + 2 + p := by positivity
    have h_denom1_pos : 0 < Real.sqrt ((k : ℝ) + 1 + p) + Real.sqrt ((k : ℝ) + 1) := by positivity
    have h_denom2_pos : 0 < Real.sqrt ((k : ℝ) + 2 + p) + Real.sqrt ((k : ℝ) + 2) := by positivity
    -- Rationalize: √(a+p) - √(a) = p/(√(a+p) + √(a))
    have h_rat1 : Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1) =
        p / (Real.sqrt ((k : ℝ) + 1 + p) + Real.sqrt ((k : ℝ) + 1)) := by
      rw [eq_div_iff h_denom1_pos.ne']
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (k:ℝ)+1 by positivity),
                 Real.sq_sqrt hk1p.le]
    have h_rat2 : Real.sqrt ((k : ℝ) + 2 + p) - Real.sqrt ((k : ℝ) + 2) =
        p / (Real.sqrt ((k : ℝ) + 2 + p) + Real.sqrt ((k : ℝ) + 2)) := by
      rw [eq_div_iff h_denom2_pos.ne']
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (k:ℝ)+2 by positivity),
                 Real.sq_sqrt hk2p.le]
    rw [h_rat2, h_rat1]
    -- p/(big sum) ≤ p/(small sum) since big sum ≥ small sum
    apply div_le_div_of_nonneg_left (le_of_lt hp_pos) h_denom1_pos
    have : Real.sqrt ((k : ℝ) + 2 + p) ≥ Real.sqrt ((k : ℝ) + 1 + p) :=
      Real.sqrt_le_sqrt (by linarith)
    have : Real.sqrt ((k : ℝ) + 2) ≥ Real.sqrt ((k : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith

-- ============================================================
-- Section 7: The atomic RS saddle-point bound — decomposed
-- ============================================================

-- ============================================================
-- Section 7a: Sub-lemma 1 — Chi modulus on the critical line
-- ============================================================

/-- Modulus of χ(1/2+it) on the critical line.

    From the functional equation χ(s) = 2^s π^{s-1} sin(πs/2) Γ(1-s),
    on s = 1/2+it, the Stirling approximation of Γ gives
    |χ(1/2+it)| = √(t/(2π)) · (1 + O(1/t)).

    For the RS formula we need the exact identity |χ(1/2+it)| = 1
    which follows from the completed zeta Λ(s) = Λ(1-s) symmetry
    and the fact that Λ is real on the critical line.

    In fact: ζ(s) = χ(s)·ζ(1-s) and on s = 1/2+it, |χ(s)| = 1.
    This is because completedRiemannZeta satisfies Λ(s) = Λ(1-s)
    and |Γℝ(s)/Γℝ(1-s)| = 1 on Re(s) = 1/2.

    Reference: Titchmarsh §4.14, Eq. (4.14.1). -/
theorem chi_modulus_critical_line (t : ℝ) (ht : t ≠ 0) :
    ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-(1/2 + Complex.I * (t : ℂ))) *
      Complex.Gamma (1/2 + Complex.I * (t : ℂ)) *
      Complex.cos (↑Real.pi * (1/2 + Complex.I * (t : ℂ)) / 2)‖ = 1 := by
  sorry

-- ============================================================
-- Section 7b: Sub-lemma 2 — ErrorTerm via zeta remainder
-- ============================================================

/-- **ErrorTerm as a real part of the zeta remainder**.

    ErrorTerm(t) = Re(e^{iθ} · ζ(1/2+it)) - 2·Re(e^{iθ} · ∑_{n≤N} n^{-s})
                 = Re(e^{iθ} · (ζ - ∑)) - Re(e^{iθ} · ∑)

    The first piece Re(e^{iθ}·remainder) connects to the functional equation;
    the second piece Re(e^{iθ}·partial_sum) is the MainTerm/2. -/
theorem errorTerm_eq_re_remainder (t : ℝ) :
    ErrorTerm t = (Complex.exp (Complex.I * hardyTheta t) *
      complexZetaRemainder t).re -
      (Complex.exp (Complex.I * hardyTheta t) * complexPartialSum t).re := by
  -- ErrorTerm = Re(e^{iθ}·ζ) - 2·Re(e^{iθ}·∑)
  -- remainder = ζ - ∑, so Re(e^{iθ}·remainder) = Re(e^{iθ}·ζ) - Re(e^{iθ}·∑)
  -- Hence ErrorTerm = Re(e^{iθ}·remainder) - Re(e^{iθ}·∑)
  unfold complexZetaRemainder
  rw [mul_sub, Complex.sub_re]
  -- Goal: ErrorTerm t = Re(e^{iθ}·ζ) - Re(e^{iθ}·∑) - Re(e^{iθ}·∑)
  -- = Re(e^{iθ}·ζ) - 2·Re(e^{iθ}·∑)
  rw [errorTerm_structure]
  ring

-- ============================================================
-- Section 7c: Sub-lemma 3 — RS leading correction phase
-- ============================================================

/-- The RS phase function: on block k at parameter p = blockParam(k,t),
    the leading correction from the saddle-point analysis gives
    (-1)^{N-1} · cos(π(2p²-2p+1/4)) where N = k+1, i.e., (-1)^k · Ψ(p).

    This is the phase-matching identity that connects the steepest-descent
    evaluation of the contour integral to the Ψ function.

    Reference: Edwards Ch. 7, pp. 136-145; Gabcke 1979 §3. -/
theorem rs_phase_match (k : ℕ) (t : ℝ)
    (_ht_lo : hardyStart k ≤ t) (_ht_hi : t ≤ hardyStart (k + 1)) (_ht : 0 < t) :
    (-1 : ℝ) ^ k * rsPsi (blockParam k t) =
    (-1 : ℝ) ^ k * Real.cos (Real.pi * (2 * (blockParam k t) ^ 2 -
      2 * blockParam k t + 1/4)) := by
  -- This is definitional: rsPsi p = cos(π(2p²-2p+1/4))
  rfl

-- ============================================================
-- Section 7d: Sub-lemma 4 — Saddle-point remainder bound
-- ============================================================

/-- **Saddle-point remainder bound** (Siegel 1932 §3).

    After extracting the leading RS correction (-1)^k·(2π/t)^{1/4}·Ψ(p),
    the next-order terms in the steepest-descent expansion contribute
    O(t^{-3/4}) with an explicit constant.

    This is the genuine analytic content: the saddle-point at w = √(t/2π)
    contributes the leading term, and the remainder from higher-order
    terms in the Taylor expansion of the phase around the saddle is bounded.

    Sub-decomposition:
    1. Contour deformation: ζ(s) = partial sum + contour integral
    2. Saddle at w₀ = √(t/2π): phase = -πw² + t·log(w) + ...
    3. Gaussian integral gives (2π/t)^{1/4} · Ψ(p) at leading order
    4. Next-order correction is bounded by C · t^{-3/4}

    Reference: Siegel 1932 §3; Gabcke 1979 Satz 1 (C_R ≈ 0.127). -/
theorem saddle_point_remainder :
    ∃ C_R : ℝ, 0 < C_R ∧ C_R ≤ 1 / 2 ∧ ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4) := by
  sorry

-- ============================================================
-- Section 7e: Assembly — rs_saddle_point_bound from sub-lemmas
-- ============================================================

/-- **Atomic Riemann-Siegel saddle-point bound** (Siegel 1932 §3).

    This is the irreducible mathematical content of the Riemann-Siegel formula.
    On each block, ErrorTerm is approximated by the RS leading term with
    O(t^{-3/4}) error.

    Now wired through `saddle_point_remainder`.

    Reference: Siegel 1932 §3; Edwards Ch. 7; Titchmarsh §4.16-4.17;
    Gabcke 1979 (optimal constant C_R ≈ 0.127). -/
theorem rs_saddle_point_bound :
    ∃ C_R : ℝ, 0 < C_R ∧ C_R ≤ 1 / 2 ∧ ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4) :=
  saddle_point_remainder

-- ============================================================
-- Section 8: Main theorem + re-exports
-- ============================================================

/-- **RS expansion pointwise** — the main theorem.
    Wired through `rs_saddle_point_bound`. -/
theorem rs_expansion_pointwise :
    ∃ C_R : ℝ, 0 < C_R ∧ C_R ≤ 1 / 2 ∧ ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4) :=
  rs_saddle_point_bound

/-- The RS expansion for B1B3AnalyticDeepLeaf (with C_R ≤ 1/2). -/
theorem rs_expansion_for_b1b3 :
    ∃ C_R : ℝ, 0 < C_R ∧ C_R ≤ 1 / 2 ∧ ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4) :=
  rs_expansion_pointwise

/-- Weaker form without C_R bound. -/
theorem rs_expansion_for_b1b3_weak :
    ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4) := by
  obtain ⟨C_R, hpos, _, h⟩ := rs_expansion_pointwise
  exact ⟨C_R, hpos, h⟩

-- ============================================================
-- Section 9: Block structure from signed RS expansion
-- ============================================================

/-- Helper: the weighted integral ∫₀¹ (√(k+1+p) - √(k+1))·Ψ(p) dp is antitone in k.
    This follows from `sqrt_increment_antitone` plus Ψ(p) ≥ 0 on [0,1]. -/
theorem weighted_increment_antitone (k : ℕ) :
    ∫ p in Ioc (0 : ℝ) 1,
      (Real.sqrt ((k : ℝ) + 2 + p) - Real.sqrt ((k : ℝ) + 2)) * rsPsi p
    ≤ ∫ p in Ioc (0 : ℝ) 1,
      (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p := by
  apply setIntegral_mono_on
  · have : ContinuousOn (fun p =>
        (Real.sqrt ((k : ℝ) + 2 + p) - Real.sqrt ((k : ℝ) + 2)) * rsPsi p) (Icc 0 1) :=
      ContinuousOn.mul
        (ContinuousOn.sub (ContinuousOn.sqrt (continuousOn_const.add continuousOn_id))
          continuousOn_const)
        rsPsi_continuousOn
    exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · have : ContinuousOn (fun p =>
        (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p) (Icc 0 1) :=
      ContinuousOn.mul
        (ContinuousOn.sub (ContinuousOn.sqrt (continuousOn_const.add continuousOn_id))
          continuousOn_const)
        rsPsi_continuousOn
    exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact measurableSet_Ioc
  · intro p hp
    apply mul_le_mul_of_nonneg_right _ (rsPsi_nonneg_on p (Ioc_subset_Icc_self hp))
    exact sqrt_increment_antitone k p (le_of_lt hp.1)

/-- The weighted integral ∫₀¹ √(k+1+p)·Ψ(p) dp is monotone increasing in k.
    This follows from √ being increasing: √(k+2+p) ≥ √(k+1+p) for all p. -/
theorem weighted_sqrt_monotone (k : ℕ) :
    ∫ p in Ioc (0 : ℝ) 1,
      Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p
    ≤ ∫ p in Ioc (0 : ℝ) 1,
      Real.sqrt ((k : ℝ) + 2 + p) * rsPsi p := by
  apply setIntegral_mono_on
  · apply (ContinuousOn.mul _ rsPsi_continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    exact ContinuousOn.sqrt (continuousOn_const.add continuousOn_id)
  · apply (ContinuousOn.mul _ rsPsi_continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    exact ContinuousOn.sqrt (continuousOn_const.add continuousOn_id)
  · exact measurableSet_Ioc
  · intro p hp
    apply mul_le_mul_of_nonneg_right _ (rsPsi_nonneg_on p (Ioc_subset_Icc_self hp))
    exact Real.sqrt_le_sqrt (by linarith)

/-- cos(hardyTheta t - t*log(n+1)) = cos(hardyPhaseSmooth n t), hence continuous.
    From exp_hardyPhaseSmooth_eq: exp(I*smooth) = exp(I*(theta-t*log(n+1))),
    so Re gives cos equality. -/
private lemma re_exp_I_mul_ofReal (x : ℝ) :
    (Complex.exp (Complex.I * (x : ℂ))).re = Real.cos x := by
  rw [mul_comm, Complex.exp_mul_I]
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_im]

private theorem cos_hardyPhase_eq_cos_smooth (n : ℕ) (t : ℝ) :
    Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1)) =
    Real.cos (HardyThetaSmooth.hardyPhaseSmooth n t) := by
  -- exp(I*smooth) = exp(I*(theta-t*log(n+1))) from the bridge.
  -- Re(exp(I*↑x)) = cos(x), so Re parts give cos equality.
  have h := HardyThetaSmooth.exp_hardyPhaseSmooth_eq n t
  rw [← re_exp_I_mul_ofReal, ← re_exp_I_mul_ofReal, h]

/-- Helper: the cos sum in errorTermOnBlock is continuous (using smooth phase bridge). -/
private theorem continuous_cosSum (k : ℕ) :
    Continuous (fun t => (2 : ℝ) * ∑ n ∈ Finset.range (k + 1),
      ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) * Real.cos (hardyTheta t - t * Real.log (n + 1))) := by
  apply continuous_const.mul
  apply continuous_finset_sum
  intro n _
  apply continuous_const.mul
  -- cos(hardyTheta t - t*log(n+1)) = cos(hardyPhaseSmooth n t), which is continuous
  have h_eq : (fun t => Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))) =
      (fun t => Real.cos (HardyThetaSmooth.hardyPhaseSmooth n t)) :=
    funext (cos_hardyPhase_eq_cos_smooth n)
  rw [h_eq]
  exact Real.continuous_cos.comp (HardyThetaSmooth.differentiable_hardyPhaseSmooth n).continuous

/-- errorTermOnBlock is continuous on the block (and in fact everywhere).
    Proved by decomposing into hardyZ (continuous via HardyZTransfer) minus
    a finite sum of continuous cos terms (via hardyPhaseSmooth bridge). -/
private theorem errorTermOnBlock_continuousOn (k : ℕ) :
    ContinuousOn (errorTermOnBlock k) (Icc (hardyStart k) (hardyStart (k + 1))) := by
  -- errorTermOnBlock k t = hardyZ t - 2 * ∑ n, (n+1)^{-1/2} * cos(θ(t) - t·log(n+1))
  unfold errorTermOnBlock
  apply Continuous.continuousOn
  apply Continuous.sub
  · -- hardyZ is continuous
    have h_eq : hardyZ = fun t => (hardyZV2 t).re :=
      funext HardyZTransfer.hardyZ_eq_hardyZV2_re
    rw [h_eq]
    exact Complex.continuous_re.comp continuous_hardyZV2
  · exact continuous_cosSum k

/-- Helper: the signed ErrorTerm integral via signed block integral.
    Factor: (-1)^k * ∫ ET = ∫ (-1)^k * ET. -/
private theorem signed_integral_factor (k : ℕ) :
    (-1 : ℝ) ^ k * ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t =
    ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), (-1 : ℝ) ^ k * ErrorTerm t := by
  simp_rw [← smul_eq_mul]
  exact (integral_smul _ _).symm

/-- Helper: the RS leading term integrated over the block via CoV equals
    4π · ∫₀¹ √(k+1+p) · Ψ(p) dp.

    Proof: CoV t = blockCoord k p = 2π(k+1+p)², dt = blockJacobian k p = 4π(k+1+p).
    (2π/t)^{1/4} = (2π/(2π(k+1+p)²))^{1/4} = ((k+1+p)²)^{-1/4} = (k+1+p)^{-1/2}.
    So (2π/t)^{1/4} · Ψ(blockParam k t) · blockJacobian = (k+1+p)^{-1/2} · Ψ(p) · 4π(k+1+p)
    = 4π · √(k+1+p) · Ψ(p). -/
private theorem leading_term_cov (k : ℕ) :
    ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
      (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) =
    4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1,
      Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p := by
  sorry

/-- Helper: on the block, t^{-3/4} ≤ (hardyStart k)^{-3/4} since t ≥ hardyStart k and
    x ↦ x^{-3/4} is decreasing for positive reals. -/
private theorem rpow_neg_three_quarter_antitone (k : ℕ) (t : ℝ)
    (ht : hardyStart k ≤ t) :
    t ^ (-(3 : ℝ) / 4) ≤ (hardyStart k) ^ (-(3 : ℝ) / 4) := by
  have hk_pos : (0 : ℝ) < hardyStart k := hardyStart_pos' k
  have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le hk_pos ht
  -- x^{-3/4} = (x^{3/4})^{-1} is decreasing for positive x
  -- Use: for 0 < a ≤ b and r ≤ 0, b^r ≤ a^r
  rw [show -(3 : ℝ) / 4 = -((3 : ℝ) / 4) from by ring]
  exact Real.rpow_le_rpow_of_nonpos hk_pos
    ht (by norm_num : -((3 : ℝ) / 4) ≤ 0)

/-- Helper: ErrorTerm is integrable on the block (from continuity of errorTermOnBlock). -/
private theorem errorTerm_integrableOn_block (k : ℕ) :
    IntegrableOn ErrorTerm (Ioc (hardyStart k) (hardyStart (k + 1))) := by
  -- errorTermOnBlock is continuous on Icc hence integrable on Ioo
  have h_int_Ioo : IntegrableOn (errorTermOnBlock k) (Ioo (hardyStart k) (hardyStart (k + 1))) :=
    (errorTermOnBlock_continuousOn k).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  -- On Ioo, errorTermOnBlock = ErrorTerm pointwise (use ae_restrict to Ioo)
  have h_ae : ∀ᵐ t ∂(volume.restrict (Ioo (hardyStart k) (hardyStart (k + 1)))),
      errorTermOnBlock k t = ErrorTerm t := by
    exact (ae_restrict_mem measurableSet_Ioo).mono fun t ht =>
      Aristotle.ErrorTermExpansion.errorTermOnBlock_eq_errorTerm k t (le_of_lt ht.1) ht.2
  have h_eq_Ioo : IntegrableOn ErrorTerm (Ioo (hardyStart k) (hardyStart (k + 1))) :=
    h_int_Ioo.congr h_ae
  -- Transfer from Ioo to Ioc (Ioo =ᵃᵉ Ioc)
  exact h_eq_Ioo.congr_set_ae Ioo_ae_eq_Ioc.symm

/-- Helper: (-1)^k has absolute value 1. -/
private theorem abs_neg_one_pow (k : ℕ) : |(-1 : ℝ) ^ k| = 1 := by
  simp [abs_pow, abs_neg, abs_one]

theorem signed_block_integral_expansion (k : ℕ) (_hk : 1 ≤ k) :
    ∃ R_k : ℝ,
    (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t) =
      4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1,
        Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p)
      + R_k ∧
    ∃ C_R : ℝ, 0 < C_R ∧ C_R ≤ 1 / 2 ∧
      |R_k| ≤ C_R * (hardyStart (k + 1) - hardyStart k) *
        (hardyStart k) ^ (-(3 : ℝ) / 4) := by
  -- Step 1: Get the saddle-point remainder from the RS expansion
  obtain ⟨C_R, hCR_pos, hCR_le, h_rs⟩ := saddle_point_remainder
  -- Step 2: Define the leading term and R_k as the difference
  refine ⟨(-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t) -
    4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1,
      Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p), by ring, C_R, hCR_pos, hCR_le, ?_⟩
  -- Step 3: Bound |R_k| = |signed - leading|
  have hk_pos : (0 : ℝ) < hardyStart k := hardyStart_pos' k
  have h_block_le : hardyStart k ≤ hardyStart (k + 1) := hardyStart_le_succ' k
  -- Use leading_term_cov: ∫_block (2π/t)^{1/4}Ψ(blockParam) = 4π ∫₀¹ √(k+1+p)Ψ(p)
  have h_lcov := leading_term_cov k

  -- (-1)^{2k} = 1
  have h_neg_one_sq : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add, show k + k = 2 * k from by ring,
        pow_mul, neg_one_sq, one_pow]

  -- Strategy: bound the difference using the pointwise RS bound.
  -- The bound ≤ C_R · BL · hs(k)^{-3/4} follows from:
  -- |signed - leading| ≤ ∫_block |ET - (-1)^k(2π/t)^{1/4}Ψ| ≤ C_R · BL · hs(k)^{-3/4}
  -- after showing signed - leading = (-1)^k · ∫_block remainder

  -- Bound using intervalIntegral.norm_integral_le_of_norm_le_const
  -- First convert to interval integral form
  set a := hardyStart k
  set b := hardyStart (k + 1)
  -- Convert Ioc to interval integral (they are equal for a ≤ b)
  have h_Ioc_eq_interval : ∀ f : ℝ → ℝ,
      (∫ t in Ioc a b, f t) = ∫ t in a..b, f t :=
    fun f => (intervalIntegral.integral_of_le h_block_le).symm
  rw [h_Ioc_eq_interval] at h_lcov
  rw [h_Ioc_eq_interval]
  -- Goal: |(-1)^k · ∫_{a..b} ET - 4π · ∫ √·Ψ| ≤ C_R · BL · hs(k)^{-3/4}
  -- Rewrite 4π·∫√·Ψ = ∫_{a..b} (2π/t)^{1/4}·Ψ via h_lcov
  rw [h_lcov.symm]
  -- Goal: |(-1)^k · ∫_{a..b} ET - ∫_{a..b} f| ≤ C_R · BL · hs(k)^{-3/4}
  -- Combine into single integral: (-1)^k · ∫ET - ∫f = ∫[(-1)^k · ET - f]
  have h_ET_ii : IntervalIntegrable ErrorTerm volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h_block_le]
    exact errorTerm_integrableOn_block k
  have h_f_ii : IntervalIntegrable
      (fun t => (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h_block_le]
    apply IntegrableOn.mono_set _ Ioc_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.mul
    · -- (2π/t)^{1/4} is continuous on Icc since t > 0 on block
      apply ContinuousOn.rpow_const
      · exact ContinuousOn.div continuousOn_const continuousOn_id
            (fun t ht => ne_of_gt (pos_of_in_block k t ht.1))
      · intro t ht; left
        exact ne_of_gt (div_pos (by positivity : 0 < 2 * Real.pi)
          (pos_of_in_block k t ht.1))
    · -- Ψ(blockParam k t) is continuous on Icc
      exact rsPsi_continuousOn.comp
        (ContinuousOn.sub
          (ContinuousOn.sqrt (ContinuousOn.div continuousOn_id continuousOn_const
            (fun _ _ => ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))))
          continuousOn_const)
        (fun t ht => blockParam_mem_Icc k t ht.1 ht.2)
  -- Pull (-1)^k inside the integral: (-1)^k * ∫ ET = ∫ (-1)^k * ET
  rw [show (-1 : ℝ) ^ k * (∫ t in a..b, ErrorTerm t) =
    ∫ t in a..b, (-1 : ℝ) ^ k * ErrorTerm t from by
    simp_rw [← smul_eq_mul]; exact (intervalIntegral.integral_smul _ _).symm]
  -- Now combine: ∫ (-1)^k*ET - ∫ f = ∫ ((-1)^k*ET - f)
  rw [← intervalIntegral.integral_sub (h_ET_ii.const_mul _) h_f_ii]
  -- Goal: |∫_{a..b} g| ≤ C_R · BL · a^{-3/4}
  -- Pointwise bound: for t ∈ [[a,b]], ‖g(t)‖ ≤ C_R · a^{-3/4}
  have h_pw : ∀ t, t ∈ Set.uIcc a b →
      ‖(-1 : ℝ) ^ k * ErrorTerm t -
        (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t)‖ ≤
      C_R * a ^ (-(3 : ℝ) / 4) := by
    intro t ht
    rw [Real.norm_eq_abs]
    -- Extract t ∈ [a, b] from uIcc (since a ≤ b)
    have ht_Icc : t ∈ Icc a b := by rwa [uIcc_of_le h_block_le] at ht
    -- Factor: (-1)^k · ET - f = (-1)^k · (ET - (-1)^k · f)
    have h_factor : (-1 : ℝ) ^ k * ErrorTerm t -
        (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) =
      (-1 : ℝ) ^ k * (ErrorTerm t - (-1 : ℝ) ^ k *
        (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t)) := by
      rw [mul_sub]; congr 1
      rw [show (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k *
          (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t)) =
        ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
          ((2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t)) from by ring,
        h_neg_one_sq, one_mul]
    rw [h_factor, abs_mul, abs_neg_one_pow, one_mul]
    calc |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
            rsPsi (blockParam k t)|
        ≤ C_R * t ^ (-(3 : ℝ) / 4) :=
          h_rs k t ht_Icc.1 ht_Icc.2 (lt_of_lt_of_le hk_pos ht_Icc.1)
      _ ≤ C_R * a ^ (-(3 : ℝ) / 4) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hCR_pos)
          exact rpow_neg_three_quarter_antitone k t ht_Icc.1
  -- Apply norm_integral_le_of_norm_le_const and convert to abs
  calc |∫ t in a..b, ((-1 : ℝ) ^ k * ErrorTerm t -
          (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t))|
      = ‖∫ t in a..b, ((-1 : ℝ) ^ k * ErrorTerm t -
          (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ C_R * a ^ (-(3 : ℝ) / 4) * |b - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun t ht => h_pw t (Set.uIoc_subset_uIcc ht))
    _ = C_R * (b - a) * a ^ (-(3 : ℝ) / 4) := by
        rw [abs_of_nonneg (by linarith : 0 ≤ b - a)]; ring

/-- **Sub-lemma: c_fn expansion in terms of weighted √-increments**.

    c(k) = 4π · ∫₀¹ (√(k+1+p) - √(k+1)) · Ψ(p) dp + R_k

    Proved from `signed_block_integral_expansion` by subtracting
    A·√(k+1) = 4π·√(k+1)·∫Ψ from both sides. -/
theorem c_fn_expansion (k : ℕ) (hk : 1 ≤ k) :
    let A_val := 4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)
    let c_fn := fun k : ℕ =>
      (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - A_val * Real.sqrt ((k : ℝ) + 1)
    ∃ R_k : ℝ,
    c_fn k = 4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1,
        (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p)
      + R_k ∧
    ∃ C_R : ℝ, 0 < C_R ∧ C_R ≤ 1 / 2 ∧
      |R_k| ≤ C_R * (hardyStart (k + 1) - hardyStart k) *
        (hardyStart k) ^ (-(3 : ℝ) / 4) := by
  -- From signed_block_integral_expansion, extract the R_k and the identity.
  obtain ⟨R_k, h_signed, hR_bound⟩ := signed_block_integral_expansion k hk
  refine ⟨R_k, ?_, hR_bound⟩
  -- Goal: c_fn k = 4π∫(√(k+1+p)-√(k+1))·Ψ(p)dp + R_k
  -- where c_fn k = (-1)^k·∫_block E - A_val·√(k+1)
  -- and h_signed: (-1)^k·∫_block E = 4π∫√(k+1+p)·Ψ(p)dp + R_k
  -- So c_fn k = 4π∫√(k+1+p)·Ψ(p)dp + R_k - A_val·√(k+1)
  --           = 4π∫√(k+1+p)·Ψ(p)dp + R_k - 4π·(∫Ψ)·√(k+1)
  --           = 4π·(∫√(k+1+p)·Ψ(p)dp - √(k+1)·∫Ψ) + R_k
  --           = 4π·∫(√(k+1+p)-√(k+1))·Ψ(p)dp + R_k
  show (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
    - (4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)) * Real.sqrt ((k : ℝ) + 1)
    = 4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1,
        (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p)
      + R_k
  -- Substitute h_signed into the LHS
  rw [h_signed]
  -- LHS becomes: (4π∫√(k+1+p)·Ψ + R_k) - 4π·(∫Ψ)·√(k+1)
  -- We need: ∫√(k+1+p)·Ψ - (∫Ψ)·√(k+1) = ∫(√(k+1+p)-√(k+1))·Ψ
  -- Rewrite the constant term: (∫Ψ)·√(k+1) = ∫(√(k+1)·Ψ)
  set c_val := Real.sqrt ((k : ℝ) + 1) with hc_def
  -- Integrability of the pieces
  have h_sqrt_psi_int : IntegrableOn (fun p => Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p)
      (Ioc (0 : ℝ) 1) := by
    apply (ContinuousOn.mul _ rsPsi_continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    exact ContinuousOn.sqrt (continuousOn_const.add continuousOn_id)
  have h_const_psi_int : IntegrableOn (fun p => c_val * rsPsi p)
      (Ioc (0 : ℝ) 1) := by
    exact (ContinuousOn.mul continuousOn_const rsPsi_continuousOn).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  -- Key step: show the integral decomposition
  -- ∫√(k+1+p)·Ψ = ∫(√(k+1+p)-c_val)·Ψ + ∫c_val·Ψ = ∫(√(k+1+p)-c_val)·Ψ + c_val·∫Ψ
  -- Step 1: ∫(f·g) = ∫((f-c)·g) + ∫(c·g) via integral_add
  have h_decomp : ∀ (p : ℝ),
      Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p =
      (Real.sqrt ((k : ℝ) + 1 + p) - c_val) * rsPsi p + c_val * rsPsi p := by
    intro p; ring
  have h_int_decomp :
      (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) =
      (∫ p in Ioc (0 : ℝ) 1, (Real.sqrt ((k : ℝ) + 1 + p) - c_val) * rsPsi p) +
      (∫ p in Ioc (0 : ℝ) 1, c_val * rsPsi p) := by
    rw [show (fun p => Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) =
        (fun p => (Real.sqrt ((k : ℝ) + 1 + p) - c_val) * rsPsi p + c_val * rsPsi p) from
      funext h_decomp]
    have h_diff_int : IntegrableOn (fun p => (Real.sqrt ((k : ℝ) + 1 + p) - c_val) * rsPsi p)
        (Ioc (0 : ℝ) 1) := by
      apply (ContinuousOn.mul _ rsPsi_continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
      exact ContinuousOn.sub (ContinuousOn.sqrt (continuousOn_const.add continuousOn_id))
        continuousOn_const
    exact integral_add h_diff_int h_const_psi_int
  -- Step 2: Pull constant out: ∫ c_val * Ψ = c_val * ∫ Ψ
  have h_const_pull : (∫ p in Ioc (0 : ℝ) 1, c_val * rsPsi p) =
      c_val * ∫ p in Ioc (0 : ℝ) 1, rsPsi p := by
    simp_rw [show (fun p => c_val * rsPsi p) = (fun p => c_val • rsPsi p) from
      funext (fun p => (smul_eq_mul c_val (rsPsi p)).symm)]
    exact integral_smul c_val (fun p => rsPsi p)
  -- Combine: substitute h_int_decomp and h_const_pull to get the equality
  -- LHS = 4π·∫√·Ψ + R_k - 4π·(∫Ψ)·c_val
  -- RHS = 4π·∫(√-c)·Ψ + R_k
  -- By h_int_decomp: ∫√·Ψ = ∫(√-c)·Ψ + ∫c·Ψ
  -- By h_const_pull: ∫c·Ψ = c_val·∫Ψ
  -- So LHS = 4π·(∫(√-c)·Ψ + c_val·∫Ψ) + R_k - 4π·(∫Ψ)·c_val = RHS
  have key : (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) =
      (∫ p in Ioc (0 : ℝ) 1, (Real.sqrt ((k : ℝ) + 1 + p) - c_val) * rsPsi p) +
      c_val * ∫ p in Ioc (0 : ℝ) 1, rsPsi p := by
    rw [← h_const_pull]; exact h_int_decomp
  -- Direct rewriting approach to avoid binder name issues
  -- From key: ∫√·Ψ = ∫(√-c)·Ψ + c·∫Ψ
  -- Goal: 4π·∫√·Ψ + R_k - (4π·∫Ψ)·c = 4π·∫(√-c)·Ψ + R_k
  -- Rewrite the LHS using key
  rw [key]; ring

/-- **Block antitone property** (Siegel 1932 §3, Gabcke 1979 Satz 4).
    The correction c(k) is antitone on k ≥ 1.

    The leading term is antitone by `weighted_increment_antitone` (concavity of √).
    The remainder is bounded and inherited from `saddle_point_remainder`.

    **BLOCKER ANALYSIS (Cycle 14)**:
    From `c_fn_expansion`: c(k) = 4π · g(k) + R(k) where
      g(k) = ∫₀¹ (√(k+1+p) - √(k+1)) · Ψ(p) dp is antitone (PROVED).
    But R(k) is the actual remainder from the RS expansion, not its absolute bound.
    We only know |R(k)| ≤ R_bound(k) where R_bound is antitone.
    For antitone c: c(k₁) - c(k₂) = 4π(g(k₁)-g(k₂)) + (R(k₁)-R(k₂)) ≥ 0.
    The worst case |R(k₁)-R(k₂)| ≤ 2·R_bound(k₁), and we need
      4π(g(k₁)-g(k₂)) ≥ 2·R_bound(k₁).
    From `correction_dominates_remainder`: R_bound(k) ≤ 4π·g(k).
    But g(k₁)-g(k₂) ~ O(k^{-3/2}) vs 2·R_bound(k₁) ~ O(k^{-1/2}).
    The bound does NOT close from pointwise estimates alone.
    Requires: either a SIGNED remainder identity (R(k) itself antitone),
    or a tighter coupling between consecutive block remainders.

    Reference: Siegel 1932 §3; Gabcke 1979 Satz 4. -/
theorem rs_block_antitone :
    let A_val := 4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)
    let c_fn := fun k : ℕ =>
      (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - A_val * Real.sqrt ((k : ℝ) + 1)
    AntitoneOn c_fn (Ici (1 : ℕ)) := by
  sorry

/-- Signed ErrorTerm is nonneg on each block: (-1)^k · ErrorTerm(t) ≥ 0.

    From the RS expansion, the signed error ≥ (2π/t)^{1/4}·Ψ(p) - C_R·t^{-3/4}.
    Since Ψ(p) ≥ cos(π/4) on [0,1] and t ≥ hardyStart(0) = 2π, the leading term
    dominates the remainder for C_R ≤ 1/2.

    Key inequality: (2π)^{1/4}·t^{1/2}·cos(π/4) ≥ C_R for t ≥ 2π, C_R ≤ 1/2.
    Proof: (2π)^{1/4} ≥ 1, t^{1/2} ≥ 1, cos(π/4) = √2/2 ≥ 1/2 ≥ C_R. -/
theorem signed_errorTerm_nonneg_on_block
    (C_R : ℝ) (hCR_pos : 0 < C_R) (hCR_le : C_R ≤ 1 / 2)
    (h_rs : ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4))
    (k : ℕ) (t : ℝ)
    (ht_lo : hardyStart k ≤ t) (ht_hi : t ≤ hardyStart (k + 1)) (ht_pos : 0 < t) :
    0 ≤ (-1 : ℝ) ^ k * ErrorTerm t := by
  -- Step 1: Get the pointwise RS bound
  have h_abs := h_rs k t ht_lo ht_hi ht_pos
  -- Step 2: Extract lower bound on ErrorTerm
  have h_lb : ErrorTerm t ≥
      (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) -
      C_R * t ^ (-(3 : ℝ) / 4) := by
    have := neg_abs_le (ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
        rsPsi (blockParam k t))
    linarith
  -- Step 3: Show the leading term dominates the remainder
  -- We need: (2π/t)^{1/4} · Ψ(p) - C_R · t^{-3/4} ≥ 0
  have hp_mem : blockParam k t ∈ Icc (0 : ℝ) 1 := blockParam_mem_Icc k t ht_lo ht_hi
  have hpsi_lb : Real.cos (Real.pi / 4) ≤ rsPsi (blockParam k t) := by
    -- From rsPsi_pos_on proof: cos(π/4) ≤ rsPsi(p) for p ∈ [0,1]
    simp only [rsPsi]
    rw [← Real.cos_abs (Real.pi * (2 * (blockParam k t) ^ 2 - 2 * blockParam k t + 1/4))]
    have ⟨hp0, hp1⟩ := hp_mem
    have harg_abs : |Real.pi * (2 * (blockParam k t) ^ 2 - 2 * blockParam k t + 1/4)| ≤
        Real.pi / 4 := by
      rw [abs_le]; constructor
      · have : 0 ≤ 2 * (blockParam k t - 1/2) ^ 2 := by positivity
        nlinarith [Real.pi_pos]
      · have : 2 * blockParam k t * (blockParam k t - 1) ≤ 0 := by nlinarith
        nlinarith [Real.pi_pos]
    exact Real.strictAntiOn_cos.antitoneOn
      (Set.mem_Icc.mpr ⟨abs_nonneg _, le_trans harg_abs
        (div_le_self (le_of_lt Real.pi_pos) (by norm_num : (1:ℝ) ≤ 4))⟩)
      (Set.mem_Icc.mpr ⟨le_of_lt (div_pos Real.pi_pos (by norm_num : (0:ℝ) < 4)),
        div_le_self (le_of_lt Real.pi_pos) (by norm_num : (1:ℝ) ≤ 4)⟩)
      harg_abs
  -- Leading term: (2π/t)^{1/4} · Ψ(p) ≥ (2π/t)^{1/4} · cos(π/4)
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_leading : (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t)
      ≥ (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * Real.cos (Real.pi / 4) :=
    mul_le_mul_of_nonneg_left hpsi_lb
      (rpow_nonneg (div_nonneg h2pi_pos.le ht_pos.le) _)
  -- Now: (2π/t)^{1/4} · cos(π/4) ≥ C_R · t^{-3/4}
  -- Rewrite: (2π/t)^{1/4} = (2π)^{1/4} · t^{-1/4}
  -- So: (2π)^{1/4} · t^{-1/4} · cos(π/4) ≥ C_R · t^{-3/4}
  -- ⟺ (2π)^{1/4} · t^{1/2} · cos(π/4) ≥ C_R  (multiply by t^{3/4})
  -- Since (2π)^{1/4} ≥ 1, t^{1/2} ≥ 1 (t ≥ 2π > 1), cos(π/4) = √2/2 ≥ 1/2 ≥ C_R
  have h_coeff_pos : 0 < (2 * Real.pi / t) ^ ((1 : ℝ) / 4) :=
    rpow_pos_of_pos (div_pos h2pi_pos ht_pos) _
  have h_dominates : C_R * t ^ (-(3 : ℝ) / 4) ≤
      (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * Real.cos (Real.pi / 4) := by
    -- Factor out t^{-1/4}: coeff = (2π)^{1/4} · t^{-1/4}
    rw [show (2 * Real.pi / t) ^ ((1 : ℝ) / 4) =
        (2 * Real.pi) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) from
      two_pi_div_t_rpow_quarter t ht_pos]
    -- RHS = (2π)^{1/4} · t^{-1/4} · cos(π/4)
    -- LHS = C_R · t^{-3/4} = C_R · t^{-1/4} · t^{-1/2}
    have h_t_inv_pos : 0 < t ^ (-(1 : ℝ) / 4) := rpow_pos_of_pos ht_pos _
    rw [show C_R * t ^ (-(3 : ℝ) / 4) =
        t ^ (-(1 : ℝ) / 4) * (C_R * t ^ (-(1 : ℝ) / 2)) from by
      rw [show (-(3 : ℝ) / 4 : ℝ) = -(1 : ℝ) / 4 + -(1 : ℝ) / 2 from by ring,
          rpow_add ht_pos]; ring]
    rw [show (2 * Real.pi) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) * Real.cos (Real.pi / 4) =
        t ^ (-(1 : ℝ) / 4) * ((2 * Real.pi) ^ ((1 : ℝ) / 4) * Real.cos (Real.pi / 4)) from
      by ring]
    -- Goal after rewrite: t^{-1/4} * (C_R * t^{-1/2}) ≤ t^{-1/4} * ((2π)^{1/4} * cos(π/4))
    -- gcongr produces subgoal: C_R * t^{-1/2} ≤ ... or C_R ≤ ...
    -- Let's use mul_le_mul_of_nonneg_left directly
    apply mul_le_mul_of_nonneg_left _ (le_of_lt h_t_inv_pos)
    -- Need: C_R * t^{-1/2} ≤ (2π)^{1/4} · cos(π/4)
    have ht_ge_one : 1 ≤ t := by
      have h_hs_ge : (1 : ℝ) < hardyStart k := by
        rw [hardyStart_formula]
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith [Real.pi_gt_three]
      linarith
    have h_tinv : t ^ (-(1 : ℝ) / 2) ≤ 1 := by
      rw [show (-(1 : ℝ) / 2 : ℝ) = -((1 : ℝ) / 2) from by ring, rpow_neg ht_pos.le]
      have : 1 ≤ t ^ ((1 : ℝ) / 2) := by
        calc (1 : ℝ) = 1 ^ ((1 : ℝ) / 2) := (one_rpow _).symm
          _ ≤ t ^ ((1 : ℝ) / 2) := rpow_le_rpow (by linarith) ht_ge_one (by norm_num)
      exact inv_le_one_of_one_le₀ this
    have h_cos_pos : 0 ≤ Real.cos (Real.pi / 4) := by
      rw [Real.cos_pi_div_four]; positivity
    have h_cos_ge_half : (1 : ℝ) / 2 ≤ Real.cos (Real.pi / 4) := by
      rw [Real.cos_pi_div_four]
      have h_sq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    have h_2pi_rpow_ge_one : (1 : ℝ) ≤ (2 * Real.pi) ^ ((1 : ℝ) / 4) := by
      calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 4) := (one_rpow _).symm
        _ ≤ (2 * Real.pi) ^ ((1 : ℝ) / 4) :=
          rpow_le_rpow (by linarith) (by linarith [Real.pi_gt_three]) (by norm_num)
    have h1 : C_R * t ^ (-(1 : ℝ) / 2) ≤ C_R := by
      nlinarith [mul_le_mul_of_nonneg_left h_tinv (le_of_lt hCR_pos)]
    have h2 : C_R ≤ Real.cos (Real.pi / 4) := le_trans hCR_le h_cos_ge_half
    have h3 : Real.cos (Real.pi / 4) ≤ (2 * Real.pi) ^ ((1 : ℝ) / 4) * Real.cos (Real.pi / 4) :=
      le_mul_of_one_le_left h_cos_pos h_2pi_rpow_ge_one
    linarith
  -- Combine: signed error ≥ leading - remainder ≥ 0
  have h_nonneg_signed_error :
      (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) -
        C_R * t ^ (-(3 : ℝ) / 4) ≥ 0 := by linarith
  -- Step 4: Transfer to (-1)^k · ErrorTerm via parity case split
  rcases Int.even_or_odd (k : ℤ) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hpow : (-1 : ℝ) ^ k = 1 := Even.neg_one_pow ⟨m.toNat, by omega⟩
    rw [hpow] at h_lb ⊢; linarith
  · have hpow : (-1 : ℝ) ^ k = -1 := Odd.neg_one_pow ⟨m.toNat, by omega⟩
    rw [hpow] at h_lb ⊢
    -- For odd k: ErrorTerm ≤ leading + remainder (from |ET - (-1)^k·L| ≤ R)
    -- -1 * ET ≥ 0 iff ET ≤ 0
    -- We need: ET ≤ -(leading - remainder) · (-1) = remainder - leading ≤ 0
    have h_ub : ErrorTerm t ≤
        (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) +
        C_R * t ^ (-(3 : ℝ) / 4) := by
      have := le_abs_self (ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t))
      linarith
    rw [hpow] at h_ub
    nlinarith

/-- If a nonneg function is integrable on [a,b], then for any T ∈ [a,b],
    the partial integral ∫_a^T f = β · ∫_a^b f for some β ∈ [0,1].
    (Inlined from B3SiegelExpansionProof to avoid importing that file.) -/
private theorem interpolation_of_nonneg_integrand {f : ℝ → ℝ} {a b : ℝ}
    (_hab : a ≤ b)
    (hf_nn : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hf_int : IntegrableOn f (Icc a b))
    (T : ℝ) (_haT : a ≤ T) (hTb : T ≤ b) :
    ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
      ∫ x in Ioc a T, f x = β * ∫ x in Ioc a b, f x := by
  by_cases h_zero : ∫ x in Ioc a b, f x = 0
  · exact ⟨0, le_refl _, zero_le_one, by
      rw [zero_mul]
      have h_mono : ∫ x in Ioc a T, f x ≤ ∫ x in Ioc a b, f x := by
        apply setIntegral_mono_set
        · exact hf_int.mono_set Ioc_subset_Icc_self
        · exact (ae_restrict_mem measurableSet_Ioc).mono fun x hx =>
            hf_nn x (Ioc_subset_Icc_self hx)
        · exact (Ioc_subset_Ioc_right hTb).eventuallyLE
      have h_nn : 0 ≤ ∫ x in Ioc a T, f x := by
        apply setIntegral_nonneg measurableSet_Ioc
        intro x hx
        exact hf_nn x ⟨hx.1.le, le_trans hx.2 hTb⟩
      linarith⟩
  · have h_full_pos : 0 < ∫ x in Ioc a b, f x := by
      apply lt_of_le_of_ne
      · apply setIntegral_nonneg measurableSet_Ioc
        intro x hx; exact hf_nn x (Ioc_subset_Icc_self hx)
      · exact Ne.symm h_zero
    have h_partial_nn : 0 ≤ ∫ x in Ioc a T, f x := by
      apply setIntegral_nonneg measurableSet_Ioc
      intro x hx; exact hf_nn x ⟨hx.1.le, le_trans hx.2 hTb⟩
    have h_partial_le : ∫ x in Ioc a T, f x ≤ ∫ x in Ioc a b, f x := by
      apply setIntegral_mono_set
      · exact hf_int.mono_set Ioc_subset_Icc_self
      · exact (ae_restrict_mem measurableSet_Ioc).mono fun x hx =>
          hf_nn x (Ioc_subset_Icc_self hx)
      · exact (Ioc_subset_Ioc_right hTb).eventuallyLE
    refine ⟨(∫ x in Ioc a T, f x) / (∫ x in Ioc a b, f x),
      div_nonneg h_partial_nn h_full_pos.le,
      div_le_one h_full_pos |>.mpr h_partial_le, ?_⟩
    rw [div_mul_cancel₀ _ h_zero]

/-- **Block interpolation property** (Siegel 1932 §3).
    Partial block integrals interpolate full block integrals with bounded error.

    From `signed_errorTerm_nonneg_on_block`, (-1)^k · ErrorTerm has definite
    sign on each block. This means ErrorTerm itself has definite sign, so
    its antiderivative is monotone on each block, and the partial integral
    is an exact fraction β ∈ [0,1] of the full integral. C₂ = 0. -/
theorem rs_block_interpolation :
    ∃ C₂ : ℝ, C₂ ≥ 0 ∧
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                   ErrorTerm t)| ≤ C₂) := by
  -- Get C_R with 0 < C_R ≤ 1/2 and the pointwise RS bound
  obtain ⟨C_R, hCR_pos, hCR_le, h_rs⟩ := rs_saddle_point_bound
  -- Take C₂ = 0 — the interpolation is exact
  refine ⟨0, le_refl _, ?_⟩
  intro k T hT_lo hT_hi
  have hhs_pos : 0 < hardyStart k := by rw [hardyStart_formula]; positivity
  -- The signed ErrorTerm (-1)^k · ErrorTerm is nonneg on block k
  have h_signed_nn : ∀ t ∈ Icc (hardyStart k) (hardyStart (k + 1)),
      0 ≤ (-1 : ℝ) ^ k * ErrorTerm t := by
    intro t ht
    exact signed_errorTerm_nonneg_on_block C_R hCR_pos hCR_le h_rs k t ht.1 ht.2
      (lt_of_lt_of_le hhs_pos ht.1)
  -- The function (-1)^k · ErrorTerm is integrable on the block
  have h1_lt_hs : (1 : ℝ) < hardyStart k := by
    rw [hardyStart_formula]
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have hET_block_int : IntegrableOn ErrorTerm
      (Icc (hardyStart k) (hardyStart (k + 1))) := by
    have h_big := errorTerm_integrable (hardyStart (k + 1))
    exact h_big.mono_set (fun t ht => ⟨lt_of_lt_of_le h1_lt_hs ht.1, ht.2⟩)
  have hSigned_int : IntegrableOn (fun t => (-1 : ℝ) ^ k * ErrorTerm t)
      (Icc (hardyStart k) (hardyStart (k + 1))) :=
    hET_block_int.const_mul _
  -- Apply interpolation_of_nonneg_integrand to (-1)^k · ErrorTerm
  have h_block_le : hardyStart k ≤ hardyStart (k + 1) := by
    rw [hardyStart_formula, hardyStart_formula]; push_cast
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1 + 1) ^ 2 := by nlinarith
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    nlinarith
  have h_interp := interpolation_of_nonneg_integrand
    h_block_le h_signed_nn hSigned_int T hT_lo hT_hi
  -- h_interp: ∃ β, 0 ≤ β ∧ β ≤ 1 ∧
  --   ∫ (-1)^k·ET on [hs k, T] = β · ∫ (-1)^k·ET on [hs k, hs(k+1)]
  obtain ⟨β, hβ_lo, hβ_hi, h_eq⟩ := h_interp
  refine ⟨β, hβ_lo, hβ_hi, ?_⟩
  -- Convert from (-1)^k · ErrorTerm integrals to ErrorTerm integrals
  have h_factor_partial : ∫ t in Ioc (hardyStart k) T, (-1 : ℝ) ^ k * ErrorTerm t =
      (-1 : ℝ) ^ k * ∫ t in Ioc (hardyStart k) T, ErrorTerm t := by
    simp_rw [← smul_eq_mul]; exact integral_smul _ _
  have h_factor_full : ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
      (-1 : ℝ) ^ k * ErrorTerm t =
      (-1 : ℝ) ^ k * ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t := by
    simp_rw [← smul_eq_mul]; exact integral_smul _ _
  rw [h_factor_partial, h_factor_full] at h_eq
  -- (-1)^k · partial = β · (-1)^k · full
  -- ⟹ (-1)^k · (partial - β · full) = 0
  -- ⟹ partial - β · full = 0
  have h_cancel : ∫ t in Ioc (hardyStart k) T, ErrorTerm t =
      β * ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t := by
    rcases Int.even_or_odd (k : ℤ) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hpow : (-1 : ℝ) ^ k = 1 := Even.neg_one_pow ⟨m.toNat, by omega⟩
      rw [hpow, one_mul, one_mul] at h_eq; exact h_eq
    · have hpow : (-1 : ℝ) ^ k = -1 := Odd.neg_one_pow ⟨m.toNat, by omega⟩
      rw [hpow] at h_eq; linarith
  rw [h_cancel, sub_self, abs_zero]

/-- Signed block integral nonnegativity: from the RS expansion,
    (-1)^k · ∫_{block k} ErrorTerm(t) dt ≥ 0 for each block.
    This means ErrorTerm has definite sign on each block. -/
theorem signed_block_integral_nonneg (k : ℕ) :
    0 ≤ (-1 : ℝ) ^ k *
      ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t := by
  obtain ⟨C_R, hCR_pos, hCR_le, h_rs⟩ := rs_saddle_point_bound
  have hhs_pos : 0 < hardyStart k := by rw [hardyStart_formula]; positivity
  -- The signed ErrorTerm (-1)^k · ErrorTerm is nonneg on block k
  have h_signed_nn : ∀ t ∈ Icc (hardyStart k) (hardyStart (k + 1)),
      0 ≤ (-1 : ℝ) ^ k * ErrorTerm t := by
    intro t ht
    exact signed_errorTerm_nonneg_on_block C_R hCR_pos hCR_le h_rs k t ht.1 ht.2
      (lt_of_lt_of_le hhs_pos ht.1)
  -- Integrability
  have h1_lt_hs : (1 : ℝ) < hardyStart k := by
    rw [hardyStart_formula]
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have hET_block_int : IntegrableOn ErrorTerm
      (Icc (hardyStart k) (hardyStart (k + 1))) := by
    have h_big := errorTerm_integrable (hardyStart (k + 1))
    exact h_big.mono_set (fun t ht => ⟨lt_of_lt_of_le h1_lt_hs ht.1, ht.2⟩)
  have hSigned_int : IntegrableOn (fun t => (-1 : ℝ) ^ k * ErrorTerm t)
      (Icc (hardyStart k) (hardyStart (k + 1))) :=
    hET_block_int.const_mul _
  -- Factor out (-1)^k
  have h_factor : ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
      (-1 : ℝ) ^ k * ErrorTerm t =
      (-1 : ℝ) ^ k * ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t := by
    simp_rw [← smul_eq_mul]
    exact integral_smul _ _
  -- The integral of a nonneg function on Ioc is nonneg
  have h_nn : 0 ≤ ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
      (-1 : ℝ) ^ k * ErrorTerm t := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    exact h_signed_nn t (Ioc_subset_Icc_self ht)
  linarith

end Aristotle.Standalone.RSExpansionProof
