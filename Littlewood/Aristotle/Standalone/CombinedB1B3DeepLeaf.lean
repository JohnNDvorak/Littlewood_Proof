/-
Combined deep leaf for B1 (AFE signed gap) and B3 (RS block analysis).

Both obligations arise from the Riemann-Siegel approximate functional equation:
- B1: the signed AFE gap ∫(|ζ|² - 2|S_N|²) = O(T) (Ingham 1926)
- B3: block integral sign structure with interpolation (Siegel 1932)

## Sorry-free infrastructure (algebraic identity chain)
- `zetaMsIntegrand_eq_hardyZ_sq`: ‖ζ(½+it)‖² = Z(t)²
- `hardyZ_eq_mainTerm_add_errorTerm`: Z = MainTerm + ErrorTerm
- `afeGapIntegrand_decomp`: gap = oscPiece + 2ME + E²
- `mainTerm_abs_le`: |MainTerm t| ≤ 4·t^{1/4}
- `cross_plus_errSq_bound`: |2ME + E²| ≤ 8C + C² (given |E| ≤ C·t^{-1/4})
- `oscSum`: complex exponential sum = e^{iθ}·S_N(½+it)
- `mainTerm_eq_two_re_oscSum`: MainTerm = 2·Re(oscSum)
- `oscSum_eq_expTheta_partialZeta`: oscSum = e^{iθ}·partialZeta
- `normSq_oscSum_eq_partialMsIntegrand`: |oscSum|² = partialMsIntegrand
- `oscPiece_eq_two_re_sq`: MainTerm² - 2|S_N|² = 2·Re(oscSum²)

## B1 derivation (from second moment + partial zeta mean square)
B1 follows from:
  ∫ afeGap = ∫|ζ|² − 2∫|S_N|²  (integral linearity)
  ∫|ζ|² = T log T + O(T)         (Hardy-Littlewood 1918, sorry)
  ∫|S_N|² = ½T log T + O(T)     (PROVED: PartialZetaMeanSquareCoeff)
  Total: T log T + O(T) − (T log T + O(T)) = O(T)

## Internal sorry's (0)
All obligations reference B1B3AnalyticDeepLeaf via cross-module opaque projections:
1. h_second_moment := b1_b3_analytic_deep_leaf.1
2. h_b3 := b1_b3_analytic_deep_leaf.2.1
3. h_b2 := b1_b3_analytic_deep_leaf.2.2 (first moment bound, Heath-Brown 1978)

WARNING COUNT: 0 (cross-module opaque references)

Reference: Ingham 1926; Siegel 1932 §3; Titchmarsh §4.16-4.17, §7.2.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Bridge.HardyFirstMomentWiring
import Littlewood.Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
import Littlewood.Aristotle.Standalone.PartialZetaMeanSquareCoeff
import Littlewood.Aristotle.Standalone.B1B3AnalyticDeepLeaf
import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Bridge.HardyZTransfer
import Littlewood.Aristotle.HardyCosSmooth

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.CombinedB1B3DeepLeaf

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
open Aristotle.ErrorTermExpansion
open Aristotle.Standalone.B1B3AnalyticDeepLeaf
open HardyCosSmooth

-- ============================================================
-- B1 Infrastructure: Pointwise decomposition of afeGapIntegrand
-- ============================================================

/-- Pointwise: ‖ζ(½+it)‖² = (hardyZ t)².

    The Hardy Z-function satisfies Z(t) = Re(e^{iθ}·ζ(½+it)),
    and e^{iθ}·ζ is real on the critical line (functional equation),
    so |Z(t)| = ‖ζ(½+it)‖ and hence Z(t)² = ‖ζ(½+it)‖². -/
theorem zetaMsIntegrand_eq_hardyZ_sq (t : ℝ) :
    zetaMsIntegrand t = (hardyZ t) ^ 2 := by
  unfold zetaMsIntegrand
  -- hardyZ t = (hardyZV2 t).re
  have h_re := HardyZTransfer.hardyZ_eq_hardyZV2_re t
  -- hardyZV2 is real-valued (imaginary part = 0)
  have h_im := hardyZV2_real t
  -- ‖hardyZV2 t‖ = ‖ζ(1/2 + I*t)‖
  have h_norm := hardyZV2_abs_eq_zeta_abs t
  -- (hardyZ t)² = ‖hardyZV2 t‖²
  have h_sq : (hardyZ t) ^ 2 = ‖hardyZV2 t‖ ^ 2 := by
    rw [h_re]
    have h_eq : hardyZV2 t = ((hardyZV2 t).re : ℂ) :=
      Complex.ext rfl (by simp [h_im])
    conv_rhs => rw [h_eq, Complex.norm_real]
    exact (sq_abs _).symm
  -- ‖ζ(↑(1/2) + I*↑t)‖² = ‖ζ(1/2 + I*t)‖² (coercion match)
  have h_arg : (↑(1 / 2 : ℝ) : ℂ) + Complex.I * ↑t = 1 / 2 + Complex.I * ↑t := by
    push_cast; ring
  rw [h_sq, h_norm, h_arg]

/-- hardyZ decomposes as MainTerm + ErrorTerm by definition. -/
theorem hardyZ_eq_mainTerm_add_errorTerm (t : ℝ) :
    hardyZ t = MainTerm t + ErrorTerm t := by
  unfold ErrorTerm; ring

/-- **B1 algebraic decomposition**: the AFE gap integrand splits into
    an oscillatory piece, a cross term, and an error-squared term.

    afeGapIntegrand t = (MainTerm² - 2|S_N|²) + 2·MainTerm·ErrorTerm + ErrorTerm²

    The three pieces have different asymptotic behavior:
    - MainTerm² - 2|S_N|² = 2Re(e^{2iθ}S_N²): oscillatory → integral O(T) by VdC
    - 2·MainTerm·ErrorTerm: if |ErrorTerm| = O(t^{-1/4}), integral O(T^{3/4}√(log T))
    - ErrorTerm²: if |ErrorTerm| = O(t^{-1/4}), integral O(√T) -/
theorem afeGapIntegrand_decomp (t : ℝ) :
    afeGapIntegrand t = ((MainTerm t) ^ 2 - 2 * partialMsIntegrand t)
        + 2 * MainTerm t * ErrorTerm t + (ErrorTerm t) ^ 2 := by
  unfold afeGapIntegrand
  rw [zetaMsIntegrand_eq_hardyZ_sq, hardyZ_eq_mainTerm_add_errorTerm]
  ring

-- ============================================================
-- B1 Infrastructure: MainTerm pointwise bound
-- ============================================================

/-- MainTerm is bounded by C·t^{1/4} for t ≥ 0.

    |MainTerm(t)| ≤ 2·∑(n+1)^{-1/2} ≤ 2·2√N(t) ≤ 4·(t/(2π))^{1/4} ≤ 4·t^{1/4}.
    Uses sum_rpow_neg_half_le from ErrorTermExpansion. -/
theorem mainTerm_abs_le (t : ℝ) (ht : 0 ≤ t) :
    |MainTerm t| ≤ 4 * t ^ ((1 : ℝ) / 4) := by
  unfold MainTerm
  set N := Nat.floor (Real.sqrt (t / (2 * Real.pi)))
  -- Normalize -(1/2) to -1/2 throughout for sum_rpow_neg_half_le compatibility
  have h_neg_eq : ∀ n : ℕ, (↑n + 1 : ℝ) ^ (-(1/2 : ℝ)) = (↑n + 1 : ℝ) ^ ((-1 : ℝ)/2) := by
    intro n; congr 1; ring
  simp_rw [h_neg_eq]
  -- Step 1: |2∑ a_n cos φ_n| ≤ 2∑ (n+1)^{-1/2}
  have h_step1 : |2 * ∑ n ∈ Finset.range N,
      ((↑n + 1 : ℝ) ^ ((-1 : ℝ)/2)) * Real.cos (hardyTheta t - t * Real.log (↑n + 1))|
    ≤ 2 * ∑ n ∈ Finset.range N, ((↑n + 1 : ℝ) ^ ((-1 : ℝ)/2)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    gcongr
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum fun n _ => by
      have hnn : (0 : ℝ) ≤ (↑n + 1) ^ ((-1 : ℝ)/2) :=
        Real.rpow_nonneg (by positivity : (0:ℝ) ≤ ↑n + 1) _
      rw [abs_mul]
      calc |(↑n + 1) ^ ((-1 : ℝ)/2)| * |Real.cos _|
          ≤ |(↑n + 1) ^ ((-1 : ℝ)/2)| * 1 := by gcongr; exact abs_cos_le_one _
        _ = (↑n + 1) ^ ((-1 : ℝ)/2) := by rw [mul_one, abs_of_nonneg hnn]
  -- Step 2: 2∑ (n+1)^{-1/2} ≤ 4√(√(t/2π))
  have h_step2 : 2 * ∑ n ∈ Finset.range N, ((↑n + 1 : ℝ) ^ ((-1 : ℝ)/2))
    ≤ 4 * Real.sqrt (Real.sqrt (t / (2 * Real.pi))) := by
    have h1 := sum_rpow_neg_half_le N
    have h2 : (N : ℝ) ≤ Real.sqrt (t / (2 * Real.pi)) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    have h3 : Real.sqrt ↑N ≤ Real.sqrt (Real.sqrt (t / (2 * Real.pi))) :=
      Real.sqrt_le_sqrt h2
    linarith
  -- Step 3: √(√(t/2π)) ≤ t^{1/4}
  have h_step3 : Real.sqrt (Real.sqrt (t / (2 * Real.pi))) ≤ t ^ ((1 : ℝ)/4) := by
    have hpi : 1 ≤ 2 * Real.pi := by have := Real.pi_gt_three; linarith
    have h_le : Real.sqrt (Real.sqrt (t / (2 * Real.pi))) ≤ Real.sqrt (Real.sqrt t) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (div_le_self ht hpi))
    have h_eq : Real.sqrt (Real.sqrt t) = t ^ ((1 : ℝ)/4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
      norm_num
    linarith
  linarith

-- ============================================================
-- B1 Infrastructure: Conditional B1 closure
-- ============================================================

/-- Pointwise bound on the cross+error² piece of the AFE gap.

    If |ErrorTerm(t)| ≤ E·t^{-1/4} for t ≥ 1, then:
    |2·MainTerm·ErrorTerm + ErrorTerm²| ≤ 8E + E²
    (using |MainTerm| ≤ 4·t^{1/4} from mainTerm_abs_le). -/
theorem cross_plus_errSq_bound (E : ℝ) (hE : 0 ≤ E) (t : ℝ) (ht : 1 ≤ t)
    (h_err : |ErrorTerm t| ≤ E * t ^ (-(1 : ℝ)/4)) :
    |2 * MainTerm t * ErrorTerm t + (ErrorTerm t) ^ 2| ≤ 8 * E + E ^ 2 := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos ht
  -- t^{1/4} ≥ 1 for t ≥ 1
  have h_one_le_rpow : 1 ≤ t ^ ((1 : ℝ)/4) := by
    calc (1 : ℝ) = 1 ^ ((1 : ℝ)/4) := (one_rpow _).symm
      _ ≤ t ^ ((1 : ℝ)/4) := Real.rpow_le_rpow zero_le_one ht (by norm_num)
  -- t^{-1/4} ≤ 1 for t ≥ 1
  have h_tpow_le : t ^ (-(1 : ℝ)/4) ≤ 1 := by
    rw [show -(1 : ℝ)/4 = -((1 : ℝ)/4) from by ring, Real.rpow_neg ht0]
    exact inv_le_one_of_one_le₀ h_one_le_rpow
  -- |ErrorTerm| ≤ E
  have h_err_abs : |ErrorTerm t| ≤ E :=
    h_err.trans (by linarith [mul_le_of_le_one_right hE h_tpow_le])
  -- |MainTerm| ≤ 4·t^{1/4}
  have h_main := mainTerm_abs_le t ht0
  -- |MainTerm·ErrorTerm| ≤ 4E (via t^{1/4}·t^{-1/4} = 1)
  have h_rpow_cancel : t ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) = 1 := by
    rw [show -(1 : ℝ)/4 = -((1 : ℝ)/4) from by ring,
        ← Real.rpow_add ht_pos, add_neg_cancel, Real.rpow_zero]
  have h_cross : |MainTerm t| * |ErrorTerm t| ≤ 4 * E := by
    calc |MainTerm t| * |ErrorTerm t|
        ≤ (4 * t ^ ((1 : ℝ)/4)) * (E * t ^ (-(1 : ℝ)/4)) := by gcongr
      _ = 4 * E * (t ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4)) := by ring
      _ = 4 * E := by rw [h_rpow_cancel]; ring
  -- |2·M·E + E²| ≤ 2·|M|·|E| + |E|² ≤ 8E + E²
  have h1 : |2 * MainTerm t * ErrorTerm t| ≤ 2 * (4 * E) := by
    have : |2 * MainTerm t * ErrorTerm t| = 2 * (|MainTerm t| * |ErrorTerm t|) := by
      rw [show 2 * MainTerm t * ErrorTerm t = 2 * (MainTerm t * ErrorTerm t) from by ring,
          abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith [h_cross]
  have h2 : |(ErrorTerm t) ^ 2| ≤ E ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    calc (ErrorTerm t) ^ 2 ≤ |ErrorTerm t| ^ 2 := by
            rw [sq_abs]
      _ ≤ E ^ 2 := by
            exact pow_le_pow_left₀ (abs_nonneg _) h_err_abs 2
  linarith [abs_add_le (2 * MainTerm t * ErrorTerm t) ((ErrorTerm t) ^ 2)]

-- ============================================================
-- B1 Infrastructure: Oscillatory piece = 2Re(z²)
-- ============================================================

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

/-- **Combined B1+B3 deep leaf**: Riemann-Siegel expansion consequences.

    Packages both the B1 signed AFE gap bound and the B3 block analysis
    obligations into a single existential, reflecting their shared origin
    in the Riemann-Siegel approximate functional equation.

    B1 (Ingham 1926): ∫₁ᵀ (|ζ(½+it)|² - 2|S_N(½+it)|²) dt = O(T)
    B3 (Siegel 1932): Block integrals satisfy
      - c(k) ≥ 0 (sign-definite corrections)
      - AntitoneOn c (Ici 1) (corrections decay)
      - Partial-block interpolation with uniform error C₂

    Proof path:
    - B1: Decompose |ζ|² = |MainTerm + ErrorTerm|² = MainTerm² + cross + error².
      MainTerm² - 2|S_N|² = 2Re(e^{2iθ}S_N²) is oscillatory → O(T) by VdC.
      Cross terms: O(∫ t^{-1/4}|S_N|) = O(T^{3/4}√(log T)) by Cauchy-Schwarz.
      Error²: O(∫ t^{-1/2}) = O(√T). Total: O(T).
    - B3: Change of variables via blockCoord/blockJacobian gives
      ∫_block ErrorTerm ≈ (-1)^k · 4π ∫₀¹ (k+1+p)^{1/2} Ψ(p) dp.
      Leading term: A·√(k+1) where A = 4π∫Ψ > 0. Correction:
      4π ∫₀¹ ((k+1+p)^{1/2} - √(k+1))Ψ(p) dp ≥ 0 since Ψ > 0.

    Reference: Ingham 1926; Siegel 1932 §3; Titchmarsh §4.16-4.17, §7.2;
    Montgomery-Vaughan §12.5-§15.2. -/
theorem combined_b1_b3_leaf :
    -- B1: AFE signed gap is O(T)
    ((fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T => T)) ∧
    -- B3: RS block analysis (definitions inlined for cross-module access)
    (let A_val := 4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1, rsPsi p
     let c_fn := fun k : ℕ =>
       (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
         - A_val * Real.sqrt ((k : ℝ) + 1)
     (∀ k : ℕ, 0 ≤ c_fn k) ∧
     AntitoneOn c_fn (Ici (1 : ℕ)) ∧
     ∃ C₂ : ℝ, C₂ ≥ 0 ∧
     (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
       ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
         |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
           - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                    ErrorTerm t)| ≤ C₂)) := by
  -- ═══════════════════════════════════════════════════════════════════
  -- B1: Direct derivation from second moment + partial zeta mean square
  -- ═══════════════════════════════════════════════════════════════════
  -- (A) The classical second moment: ∫₁ᵀ |ζ(½+it)|² = T·log T + O(T)
  --     (Hardy-Littlewood 1918; Titchmarsh §7.2, Theorem 7.2)
  have h_second_moment : (fun T => (∫ t in (1:ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
      =O[atTop] (fun T => T) := b1_b3_analytic_deep_leaf.1
  -- (B) Partial zeta mean square: ∫₁ᵀ |S_N|² = ½·T·log T + O(T)
  --     (PROVED: cycle-free extraction in PartialZetaMeanSquareCoeff.lean)
  have h_partial_ms : (fun T => (∫ t in (1:ℝ)..T, partialMsIntegrand t)
      - 2⁻¹ * T * Real.log T)
      =O[atTop] (fun T => T) :=
    Aristotle.Standalone.PartialZetaMeanSquareCoeff.partial_zeta_mean_square_half_coeff
  -- (C) B3 block structure from Siegel expansion
  have h_b3 :
    let A_val := 4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1, rsPsi p
    let c_fn := fun k : ℕ =>
      (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - A_val * Real.sqrt ((k : ℝ) + 1)
    (∀ k : ℕ, 0 ≤ c_fn k) ∧
    AntitoneOn c_fn (Ici (1 : ℕ)) ∧
    ∃ C₂ : ℝ, C₂ ≥ 0 ∧
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                   ErrorTerm t)| ≤ C₂) := b1_b3_analytic_deep_leaf.2.1
  -- ═══════════════════════════════════════════════════════════════════
  -- Assembly: B1 from ∫|ζ|² = TlogT + O(T) minus 2·∫|S_N|² = TlogT + O(T)
  -- ═══════════════════════════════════════════════════════════════════
  refine ⟨?_, h_b3⟩
  -- ∫ afeGap is eventually equal to f₁ - 2·f₂ where both f₁, f₂ are O(T)
  have h_afe_eq : (fun T => ∫ t in (1:ℝ)..T, afeGapIntegrand t) =ᶠ[atTop]
      (fun T => ((∫ t in (1:ℝ)..T, zetaMsIntegrand t) - T * Real.log T) -
       2 * ((∫ t in (1:ℝ)..T, partialMsIntegrand t) - 2⁻¹ * T * Real.log T)) := by
    filter_upwards with T
    have h_lin : ∫ t in (1:ℝ)..T, afeGapIntegrand t =
        (∫ t in (1:ℝ)..T, zetaMsIntegrand t) -
        2 * (∫ t in (1:ℝ)..T, partialMsIntegrand t) := by
      unfold afeGapIntegrand
      rw [← intervalIntegral.integral_const_mul 2,
          ← intervalIntegral.integral_sub (intervalIntegrable_zetaMsIntegrand T)
            ((intervalIntegrable_partialMsIntegrand T).const_mul 2)]
    linarith [h_lin]
  -- 2 * h_partial_ms is O(T)
  have h_2pm : (fun T => 2 * ((∫ t in (1:ℝ)..T, partialMsIntegrand t) -
      2⁻¹ * T * Real.log T)) =O[atTop] (fun T => T) := by
    obtain ⟨C, hC⟩ := h_partial_ms.isBigOWith
    exact (hC.const_mul_left 2).isBigO
  -- f₁ - 2·f₂ = O(T)
  have h_diff := h_second_moment.sub h_2pm
  exact (Asymptotics.isBigO_congr h_afe_eq.symm EventuallyEq.rfl).mp h_diff

-- ============================================================
-- B2 extraction: MainTermFirstMomentBoundHyp from the unified leaf
-- ============================================================

/-- **B2 extraction**: the first moment bound from the unified analytic deep leaf.

    The B2 obligation (Heath-Brown 1978) is packaged as Part 3 of
    `b1_b3_analytic_deep_leaf`. This theorem extracts it as an instance
    of `MainTermFirstMomentBoundHyp`, replacing the previously false
    B2TailVdcDeepLeaf route. -/
theorem mainTermFirstMomentBoundHyp_from_analytic_leaf :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp :=
  ⟨b1_b3_analytic_deep_leaf.2.2⟩

end Aristotle.Standalone.CombinedB1B3DeepLeaf
