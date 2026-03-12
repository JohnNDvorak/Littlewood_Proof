/-
Algebraic identities for the oscillatory piece of the AFE gap.

Extracted from CombinedB1B3DeepLeaf to avoid import cycles.
These are pure algebraic identities with NO sorry dependencies.

## Key results

- `oscSum`: complex exponential sum ∑ (n+1)^{-1/2} · hardyCosExp(n,t)
- `mainTerm_eq_two_re_oscSum`: MainTerm = 2·Re(oscSum)
- `oscSum_eq_expTheta_partialZeta`: oscSum = e^{iθ}·S_N(½+it)
- `normSq_oscSum_eq_partialMsIntegrand`: |oscSum|² = partialMsIntegrand
- `oscPiece_eq_two_re_sq`: MainTerm² - 2·partialMsIntegrand = 2·Re(oscSum²)

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
import Littlewood.Aristotle.HardyCosSmooth
import Littlewood.Aristotle.HardyZFirstMoment

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.OscPieceIdentities

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
open HardyCosSmooth

/-- Pure complex identity: 4(Re z)² - 2‖z‖² = 2·Re(z²).

    Proof: Re(z²) = Re(z)² - Im(z)², ‖z‖² = Re(z)² + Im(z)².
    So 4x² - 2(x²+y²) = 2x² - 2y² = 2(x²-y²) = 2·Re(z²). -/
theorem four_re_sq_sub_two_normSq (z : ℂ) :
    4 * z.re ^ 2 - 2 * Complex.normSq z = 2 * (z ^ 2).re := by
  have hsq : z ^ 2 = z * z := sq z
  rw [hsq]
  simp only [Complex.normSq_apply, Complex.mul_re]
  ring

/-- The oscillatory complex sum: ∑ (n+1)^{-1/2} · hardyCosExp(n,t).

    This equals e^{iθ}·S_N(½+it), connecting the trig sum (MainTerm)
    to the complex Dirichlet sum (partialZeta). -/
def oscSum (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (hardyN t),
    ((n + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) * hardyCosExp n t

/-- MainTerm = 2·Re(oscSum): the real cosine sum is twice the
    real part of the complex exponential sum. -/
private lemma re_ofReal_mul (a : ℝ) (z : ℂ) : ((↑a : ℂ) * z).re = a * z.re := by
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

theorem mainTerm_eq_two_re_oscSum (t : ℝ) :
    MainTerm t = 2 * (oscSum t).re := by
  unfold MainTerm oscSum
  rw [Complex.re_sum]
  simp_rw [re_ofReal_mul]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  exact hardyCos_eq_re_hardyCosExp n t

/-- Each term of oscSum relates to e^{iθ} times the Dirichlet term:
    ↑((n+1)^{-1/2}) * hardyCosExp(n,t) = e^{iθ} * (n+1:ℂ)^{-(1/2+it)}. -/
private theorem oscSum_term_eq_exp_theta_dirichlet (n : ℕ) (t : ℝ) :
    ((↑((n + 1 : ℝ) ^ (-(1/2 : ℝ))) : ℂ) * hardyCosExp n t) =
    Complex.exp (Complex.I * ↑(hardyTheta t)) *
      ((↑(n + 1) : ℂ) ^ (-(1/2 + Complex.I * ↑t) : ℂ)) := by
  have hn_pos : (0 : ℝ) < (↑n + 1 : ℝ) := by positivity
  have hn_ne : (↑(n + 1) : ℂ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  -- hardyCosExp = exp(I·(θ - t·log(n+1)))
  rw [hardyCosExp_eq_cexp_phaseArg, hardyPhaseArg_eq_hardyTheta_sub_log]
  -- (n+1:ℂ)^{-(1/2+it)} = exp(-(1/2+it)·log(n+1))
  rw [Complex.cpow_def_of_ne_zero hn_ne]
  -- log(↑(n+1)) = ↑(log(n+1)) for positive reals
  have h_log : Complex.log (↑(n + 1) : ℂ) = ↑(Real.log (↑n + 1)) := by
    rw [Complex.ofReal_log (le_of_lt hn_pos)]
    push_cast; ring_nf
  rw [h_log]
  -- (n+1)^{-1/2} = exp(-1/2 · log(n+1))
  have h_rpow : ((n + 1 : ℝ) ^ (-(1/2 : ℝ)) : ℝ) =
      Real.exp (-(1/2) * Real.log (↑n + 1)) := by
    rw [Real.rpow_def_of_pos hn_pos]; ring_nf
  rw [h_rpow, Complex.ofReal_exp]
  -- Now both sides are products of complex exponentials; combine and match
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- oscSum = e^{iθ} · partialZeta(√(t/2π), 1/2+it). -/
private lemma sum_Icc_one_eq_sum_range {β : Type*} [AddCommMonoid β]
    (N : ℕ) (f : ℕ → β) :
    ∑ i ∈ Finset.Icc 1 N, f i = ∑ n ∈ Finset.range N, f (n + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ]

theorem oscSum_eq_expTheta_partialZeta (t : ℝ) :
    oscSum t = Complex.exp (Complex.I * ↑(hardyTheta t)) *
      partialZeta (Real.sqrt (t / (2 * Real.pi))) (1 / 2 + Complex.I * ↑t) := by
  unfold oscSum partialZeta
  rw [Finset.mul_sum, sum_Icc_one_eq_sum_range]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← oscSum_term_eq_exp_theta_dirichlet]

theorem normSq_oscSum_eq_partialMsIntegrand (t : ℝ) :
    Complex.normSq (oscSum t) = partialMsIntegrand t := by
  unfold partialMsIntegrand
  rw [oscSum_eq_expTheta_partialZeta, map_mul]
  -- normSq(e^{iθ}) = 1
  have h_unit : Complex.normSq (Complex.exp (Complex.I * ↑(hardyTheta t))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, exp_iTheta_norm, one_pow]
  rw [h_unit, one_mul]

/-- **Oscillatory piece algebraic identity**:

    MainTerm(t)² - 2·partialMsIntegrand(t) = 2·Re((oscSum t)²)

    This identifies the oscillatory piece of the AFE gap as twice the
    real part of the squared complex sum. Since oscSum = e^{iθ}·S_N,
    this equals 2·Re(e^{2iθ}·S_N²), which oscillates rapidly. -/
theorem oscPiece_eq_two_re_sq (t : ℝ) :
    (MainTerm t) ^ 2 - 2 * partialMsIntegrand t = 2 * ((oscSum t) ^ 2).re := by
  rw [mainTerm_eq_two_re_oscSum, ← normSq_oscSum_eq_partialMsIntegrand]
  have h := four_re_sq_sub_two_normSq (oscSum t)
  linarith

end Aristotle.Standalone.OscPieceIdentities
