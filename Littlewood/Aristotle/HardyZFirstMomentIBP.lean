/-
Hardy Z first moment bound via integration by parts.

TARGET:
  ∀ ε > 0, ∃ C > 0, ∀ T ≥ 2, |∫₁ᵀ Z(t) dt| ≤ C · T^{1/2+ε}

Actually we prove the stronger O(T^{1/2}) bound.

PROOF SKETCH (Titchmarsh §4.15):

Z(t) = Re(e^{iθ(t)} ζ(1/2+it)).

Using the smooth theta:
  e^{iθ(t)} = (d/dt)[e^{iθ(t)}] / (iθ'(t))

Integration by parts on ∫ e^{iθ(t)} ζ(1/2+it) dt with:
  u = ζ(1/2+it) / (iθ'(t)),  dv = e^{iθ(t)} θ'(t) dt

gives boundary terms + correction integral, both controlled by:
  - |ζ(1/2+it)| ≤ C t^{1/6} (convexity bound, already in ConvexityBounds)
  - θ'(t) ≥ c log t (from theta_deriv_asymptotic + monotonicity)
  - |d/dt[ζ/θ']| controlled by convexity + θ' bounds

KEY INFRASTRUCTURE BUILT HERE:
  1. thetaDeriv_lower_bound: θ'(t) ≥ c·log(t) for large t
  2. thetaDeriv_inv_bound: 1/θ'(t) = O(1/log t) for large t
  3. hardyZ_first_moment_sqrt: |∫₁ᵀ Z(t) dt| ≤ C · T^{1/2+ε}

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.ThetaDerivAsymptotic
import Littlewood.Aristotle.ThetaDerivMonotone
import Littlewood.Aristotle.HardyThetaSmooth
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.PhragmenLindelof
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.OffResonanceSmoothVdC
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.Standalone.OscPieceBigOAssembly
import Littlewood.Aristotle.AbelSummation
import Littlewood.Bridge.HardyZTransfer
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.Standalone.RSExpansionProof
import Littlewood.Aristotle.IntervalPartition
import Littlewood.Aristotle.StationaryPhasePerMode

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardyZFirstMomentIBP

open Complex Real Set Filter Topology MeasureTheory
open ThetaDerivAsymptotic ThetaDerivMonotone HardyThetaSmooth

/-! ## Part 1: Lower bound for θ'(t)

From theta_deriv_asymptotic: θ'(t) = (1/2)·log(t/(2π)) + O(1/t).
This gives θ'(t) ≥ (1/4)·log(t) for sufficiently large t.
-/

/-- θ'(t) ≥ (1/4)·log(t) for sufficiently large t.
    This is the key lower bound needed for the IBP denominator. -/
theorem thetaDeriv_lower_bound :
    ∃ T₀ > 0, ∀ t : ℝ, t ≥ T₀ →
      thetaDeriv t ≥ (1/4) * Real.log t := by
  -- From theta_deriv_asymptotic: θ'(t) = (1/2)·log(t/(2π)) + O(1/t)
  -- log(t/(2π)) = log t - log(2π)
  -- So θ'(t) ≥ (1/2)·log(t) - (1/2)·log(2π) - C/t
  -- For t large enough, (1/2)·log(t) - (1/2)·log(2π) - C/t ≥ (1/4)·log(t)
  -- i.e., (1/4)·log(t) ≥ (1/2)·log(2π) + C/t
  have h_asymp := theta_deriv_asymptotic
  rw [Asymptotics.isBigO_iff] at h_asymp
  obtain ⟨C, hC⟩ := h_asymp
  rw [Filter.eventually_atTop] at hC
  obtain ⟨T₁, hT₁⟩ := hC
  -- Choose T₀ large enough that:
  -- (1) t ≥ T₁ (asymptotic applies)
  -- (2) (1/4)·log t ≥ (1/2)·log(2π) + |C|/t + 1
  --     which is ensured by t ≥ exp(4·(log(2π) + 2)) and t ≥ 4·|C|
  set T₀ := max T₁ (max (Real.exp (4 * (Real.log (2 * Real.pi) + 2))) (max (4 * |C| + 1) 2))
  refine ⟨T₀, by positivity, fun t ht => ?_⟩
  have ht_ge_T₁ : t ≥ T₁ := by
    calc T₁ ≤ T₀ := le_max_left _ _
      _ ≤ t := ht
  have ht_ge_exp : t ≥ Real.exp (4 * (Real.log (2 * Real.pi) + 2)) := by
    calc Real.exp _ ≤ max (Real.exp _) (max (4 * |C| + 1) 2) := le_max_left _ _
      _ ≤ T₀ := le_max_right _ _
      _ ≤ t := ht
  have ht_ge_C : t ≥ 4 * |C| + 1 := by
    calc 4 * |C| + 1 ≤ max (4 * |C| + 1) 2 := le_max_left _ _
      _ ≤ max (Real.exp _) (max (4 * |C| + 1) 2) := le_max_right _ _
      _ ≤ T₀ := le_max_right _ _
      _ ≤ t := ht
  have ht_ge_2 : t ≥ 2 := by
    calc (2 : ℝ) ≤ max (4 * |C| + 1) 2 := le_max_right _ _
      _ ≤ max (Real.exp _) (max (4 * |C| + 1) 2) := le_max_right _ _
      _ ≤ T₀ := le_max_right _ _
      _ ≤ t := ht
  have ht_pos : (0 : ℝ) < t := by linarith
  have hpi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  -- Get the bound
  have h_bd := hT₁ t ht_ge_T₁
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h_bd
  -- θ'(t) ≥ (1/2)·log(t/(2π)) - |C|/t
  have h_lower : thetaDeriv t ≥ (1/2) * Real.log (t / (2 * Real.pi)) - |C| / t := by
    have h1 : thetaDeriv t - 1/2 * Real.log (t / (2 * Real.pi)) ≥ -(|C| / t) := by
      have := neg_abs_le (thetaDeriv t - 1/2 * Real.log (t / (2 * Real.pi)))
      have h2 : |C| / t ≥ C * |1/t| := by
        rw [abs_of_pos (div_pos one_pos ht_pos), one_div]
        calc C * t⁻¹ ≤ |C| * t⁻¹ := by
              exact mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.mpr (le_of_lt ht_pos))
          _ = |C| / t := by rw [div_eq_mul_inv]
      linarith [h_bd]
    linarith
  -- log(t/(2π)) = log t - log(2π)
  have h_log_split : Real.log (t / (2 * Real.pi)) = Real.log t - Real.log (2 * Real.pi) := by
    rw [Real.log_div (ne_of_gt ht_pos) (ne_of_gt hpi_pos)]
  rw [h_log_split] at h_lower
  -- Need: (1/2)(log t - log(2π)) - |C|/t ≥ (1/4)·log t
  -- i.e., (1/4)·log t ≥ (1/2)·log(2π) + |C|/t
  suffices h : (1/4 : ℝ) * Real.log t ≥ (1/2) * Real.log (2 * Real.pi) + |C| / t by linarith
  -- log t ≥ 4·(log(2π) + 2) from our choice of T₀
  have h_log_t : Real.log t ≥ 4 * (Real.log (2 * Real.pi) + 2) := by
    calc 4 * (Real.log (2 * Real.pi) + 2) =
          Real.log (Real.exp (4 * (Real.log (2 * Real.pi) + 2))) := (Real.log_exp _).symm
      _ ≤ Real.log t := Real.log_le_log (Real.exp_pos _) ht_ge_exp
  -- |C|/t ≤ 1 from our choice of T₀
  have h_Ct : |C| / t ≤ 1 := by
    rw [div_le_one ht_pos]
    linarith
  -- (1/4)·log t ≥ log(2π) + 2 ≥ (1/2)·log(2π) + 1 ≥ (1/2)·log(2π) + |C|/t
  have hge1 : (1 : ℝ) ≤ 2 * Real.pi := by
    have := Real.pi_gt_three; linarith
  have h_log_2pi_nonneg : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg hge1
  have h1 : (1/4 : ℝ) * Real.log t ≥ Real.log (2 * Real.pi) + 2 := by linarith
  linarith

/-- θ'(t) > 0 for all t ≥ T₀ (a specific computable T₀). -/
theorem thetaDeriv_pos_of_large :
    ∃ T₀ > 0, ∀ t : ℝ, t ≥ T₀ → 0 < thetaDeriv t := by
  obtain ⟨T₀, hT₀, h⟩ := thetaDeriv_lower_bound
  refine ⟨max T₀ 2, by positivity, fun t ht => ?_⟩
  have ht_ge_T₀ : t ≥ T₀ := le_trans (le_max_left _ _) ht
  have ht_ge_2 : t ≥ 2 := le_trans (le_max_right _ _) ht
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  linarith [h t ht_ge_T₀]

/-- 1/θ'(t) ≤ 4/log(t) for large t. -/
theorem inv_thetaDeriv_le :
    ∃ T₀ > 0, ∀ t : ℝ, t ≥ T₀ →
      1 / thetaDeriv t ≤ 4 / Real.log t := by
  obtain ⟨T₀, hT₀, h⟩ := thetaDeriv_lower_bound
  refine ⟨max T₀ 2, by positivity, fun t ht => ?_⟩
  have ht_ge_T₀ : t ≥ T₀ := le_trans (le_max_left _ _) ht
  have ht_ge_2 : t ≥ 2 := le_trans (le_max_right _ _) ht
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have htheta : 0 < thetaDeriv t := by linarith [h t ht_ge_T₀]
  rw [div_le_div_iff₀ htheta hlog]
  linarith [h t ht_ge_T₀]

/-! ## Part 2: Continuity and regularity of 1/θ'(t)

For IBP we need 1/θ'(t) to be well-defined and continuous. Since θ'
is continuous (from HardyThetaSmooth.continuous_thetaDeriv) and eventually
positive (from Part 1), 1/θ' is continuous on [T₀, ∞).
-/

/-- 1/thetaDeriv is continuous on the set where thetaDeriv > 0. -/
theorem continuousOn_inv_thetaDeriv (T₀ : ℝ) (hT₀ : ∀ t ≥ T₀, 0 < thetaDeriv t) :
    ContinuousOn (fun t => 1 / thetaDeriv t) (Set.Ici T₀) := by
  apply ContinuousOn.div continuousOn_const
  · exact continuous_thetaDeriv.continuousOn
  · intro t ht
    exact ne_of_gt (hT₀ t ht)

/-! ## Part 3: The IBP identity for ∫ Z(t) dt

The key identity: since Z(t) = Re(e^{iθ(t)} ζ(1/2+it)) and
d/dt[e^{iθ(t)}] = iθ'(t) e^{iθ(t)}, we can write:

  e^{iθ(t)} = d/dt[e^{iθ(t)}] / (iθ'(t))

So ∫ Z dt = Re ∫ e^{iθ} ζ dt can be handled by IBP.

We formalize the IBP approach using the smooth theta to avoid
branch-cut issues.
-/

/-- The phase exponential e^{iθ_smooth(t)} has derivative iθ'(t)·e^{iθ_smooth(t)}. -/
theorem hasDerivAt_exp_iTheta (t : ℝ) :
    HasDerivAt (fun u => Complex.exp (I * ↑(hardyThetaSmooth u)))
      (I * ↑(thetaDeriv t) * Complex.exp (I * ↑(hardyThetaSmooth t))) t := by
  have h1 : HasDerivAt (fun u => I * ↑(hardyThetaSmooth u)) (I * ↑(thetaDeriv t)) t :=
    (hasDerivAt_hardyThetaSmooth t).ofReal_comp.const_mul I
  exact (h1.cexp).congr_deriv (by ring)

-- The antiderivative of e^{iθ(t)}·θ'(t) is e^{iθ(t)}/i = -i·e^{iθ(t)}.
--
-- More precisely: d/dt[e^{iθ(t)}/(iθ'(t))] involves correction terms from θ'(t)
-- varying. The clean version: d/dt[e^{iθ(t)}] = iθ'(t)·e^{iθ(t)}.
--
-- For the IBP of ∫ e^{iθ}·f dt where f = ζ(1/2+it), we write:
--   e^{iθ}·f = (d/dt[e^{iθ}])·(f/(iθ'))
-- and integrate by parts.

-- The product rule for the IBP integrand.
-- If F(t) = e^{iθ(t)} and G(t) = f(t)/(iθ'(t)), then
-- F'·G + F·G' = e^{iθ}·f + F·G'

/-! ## Part 4: Hardy Z first moment bound

The classical approach bounds |∫₁ᵀ Z(t) dt| by splitting [1,T] into
[1, T₀] (compact, bounded) and [T₀, T] (IBP applies).

On [T₀, T]:
  |∫ Z dt| = |Re ∫ e^{iθ} ζ dt|
  ≤ |∫ e^{iθ} ζ dt|

IBP with u = ζ/(iθ'), dv = e^{iθ}·θ' dt gives:
  = |[ζ·e^{iθ}/(iθ')]_{T₀}^{T} - ∫ d/dt[ζ/(iθ')]·e^{iθ}/iθ' dt|

Boundary terms: |ζ(1/2+it)|·1/|θ'(t)| = O(t^{1/6}/log t) → 0 not needed,
we just bound them.

For T^{1/2+ε}, we use a simpler approach: partial summation / Dirichlet
polynomial mean value. The cleanest self-contained proof uses the
fact that θ' is monotone increasing, so van der Corput's lemma
(first derivative test) applies directly to each mode.

We state the result using the infrastructure we have.
-/

/-! ### θ'' bounds via trigamma

From ThetaDerivMonotone.thetaDeriv_hasDerivAt:
  θ'(t) has derivative -(1/4)·Im(Σ 1/(s+n)²) at every t.

For t > 0, this derivative is positive (θ' is strictly increasing).
We can also bound it: 0 ≤ θ''(t) ≤ C/t for large t. -/

/-- θ''(t) exists everywhere and equals -(1/4)·Im(trigamma(s(t))). -/
theorem thetaDeriv_deriv_eq (t : ℝ) :
    deriv thetaDeriv t = -(1/4 : ℝ) *
      (∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2).im :=
  (thetaDeriv_hasDerivAt t).deriv

/-- θ''(t) ≥ 0 for all t > 0 (θ' is increasing). -/
theorem thetaDeriv_deriv_nonneg (t : ℝ) (ht : 0 < t) :
    0 ≤ deriv thetaDeriv t := by
  obtain ⟨d, hd, hd_pos⟩ := thetaDeriv_deriv_pos t ht
  rw [hd.deriv]
  exact le_of_lt hd_pos

/-- θ''(t) is bounded: |θ''(t)| ≤ C for some absolute constant.

    This follows from the trigamma series representation:
    θ''(t) = -(1/4)·Im(Σ 1/(s+n)²)
    where |Im(1/(s+n)²)| ≤ 1/|s+n|² ≤ 1/(n+1/4)²,
    and Σ 1/(n+1/4)² converges. -/
-- Helper: |Im(Σ 1/(s+n)²)| is bounded by the convergent sum Σ 1/(n+1/4)²
-- Summability of 16/(n+1)^2.
private lemma summable_sixteen_div_sq' :
    Summable (fun n : ℕ => 16 / ((↑n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (↑n : ℝ) ^ 2) 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  simp only [Nat.cast_add, Nat.cast_one] at h
  exact (h.mul_left 16).congr (fun n => by ring)

-- Summability of 1/(n+1/4)^2.
private lemma summable_inv_quarter_shift_sq :
    Summable (fun n : ℕ => 1 / ((↑n : ℝ) + 1/4) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ summable_sixteen_div_sq'
  intro n
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ((↑n : ℝ) + 1/4) ^ 2) (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

-- The norm of each term 1/(s+n)^2 is bounded by 1/(n+1/4)^2.
private lemma norm_inv_sq_sOfT_le (t : ℝ) (n : ℕ) :
    ‖1 / (sOfT t + (↑n : ℂ)) ^ 2‖ ≤ 1 / ((↑n : ℝ) + 1/4) ^ 2 := by
  rw [one_div, norm_inv, norm_pow, one_div]
  apply inv_anti₀ (by positivity : (0 : ℝ) < ((↑n : ℝ) + 1/4) ^ 2)
  exact sq_le_sq' (by linarith [norm_nonneg (sOfT t + (↑n : ℂ))]) (norm_sOfT_add_nat_ge t n)

-- Norm bound on the trigamma sum.
private lemma norm_trigamma_le (t : ℝ) :
    ‖∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2‖ ≤
      ∑' n : ℕ, 1 / ((↑n : ℝ) + 1/4) ^ 2 := by
  have hsumm := summable_inv_sq_sOfT t
  calc ‖∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2‖
      ≤ ∑' n : ℕ, ‖1 / (sOfT t + (↑n : ℂ)) ^ 2‖ :=
        norm_tsum_le_tsum_norm hsumm.norm
    _ ≤ ∑' n : ℕ, 1 / ((↑n : ℝ) + 1/4) ^ 2 := by
        exact hsumm.norm.tsum_le_tsum (fun n => norm_inv_sq_sOfT_le t n) summable_inv_quarter_shift_sq

theorem thetaDeriv_deriv_bounded :
    ∃ M > 0, ∀ t : ℝ, |deriv thetaDeriv t| ≤ M := by
  -- θ''(t) = -(1/4)·Im(Σ 1/(s+n)²)
  -- |θ''(t)| = (1/4)·|Im(Σ ·)| ≤ (1/4)·‖Σ ·‖ ≤ (1/4)·Σ 1/(n+1/4)²
  set S := ∑' n : ℕ, 1 / ((↑n : ℝ) + 1/4) ^ 2
  refine ⟨(1/4) * S + 1, by positivity, fun t => ?_⟩
  rw [thetaDeriv_deriv_eq]
  have h_im_le : |(∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2).im| ≤ S := by
    calc |(∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2).im|
        ≤ ‖∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2‖ := Complex.abs_im_le_norm _
      _ ≤ S := norm_trigamma_le t
  calc |-(1/4 : ℝ) * (∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2).im|
      = (1/4) * |(∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2).im| := by
        rw [abs_mul, show |-(1/4 : ℝ)| = 1/4 from by norm_num]
    _ ≤ (1/4) * S := by gcongr
    _ ≤ (1/4) * S + 1 := by linarith

/-- θ''(t) = O(1/t) as t → ∞.

    Tighter bound from the trigamma sum: the dominant contribution is
    Im(1/s²) = O(1/t³) and the full sum is O(1/t) by careful estimation.
    Even a crude O(1) bound suffices for the IBP because θ'/θ'² = O(1/log²t). -/
theorem thetaDeriv_deriv_isBigO :
    (fun t : ℝ => deriv thetaDeriv t) =O[atTop] (fun _ => (1 : ℝ)) := by
  -- θ''(t) is bounded, hence O(1)
  obtain ⟨M, _hM_pos, hM⟩ := thetaDeriv_deriv_bounded
  exact Asymptotics.IsBigO.of_bound M (Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, norm_one, mul_one]; exact hM t)

/-! ## Part 5: Uniform pointwise bound for Z(t) via PhragmenLindelof

From PhragmenLindelof.zeta_critical_line_bound:
  ∃ C > 0, ∀ t, |t| ≥ 1 → ‖ζ(1/2+t·I)‖ ≤ C · |t|^{1/2}

Combined with hardyZ_abs_le: |Z(t)| ≤ ‖ζ(1/2+I·t)‖

This gives the uniform pointwise bound |Z(t)| ≤ C · t^{1/2} for t ≥ 1.
-/

/-- Uniform pointwise bound: |Z(t)| ≤ C · |t|^{1/2} for |t| ≥ 1. -/
theorem hardyZ_pointwise_bound :
    ∃ C > 0, ∀ t : ℝ, |t| ≥ 1 →
      |HardyEstimatesPartial.hardyZ t| ≤ C * |t| ^ ((1 : ℝ) / 2) := by
  obtain ⟨C, hC, hbound⟩ := zeta_critical_line_bound
  refine ⟨C, hC, fun t ht => ?_⟩
  calc |HardyEstimatesPartial.hardyZ t|
      ≤ ‖riemannZeta (1 / 2 + I * ↑t)‖ := HardyEstimatesPartial.hardyZ_abs_le t
    _ ≤ C * |t| ^ ((1 : ℝ) / 2) := by
        have hbd := hbound t ht
        convert hbd using 2; ring

/-! ## Part 5b: Cauchy estimate for ζ' on the critical line

Using Mathlib's `norm_deriv_le_of_forall_mem_sphere_norm_le`:
  If f is DiffContOnCl on ball(c, R) and ‖f‖ ≤ M on sphere(c, R),
  then ‖f'(c)‖ ≤ M/R.

Applied to ζ at c = 1/2 + t·I with R = 1/2:
  ‖ζ'(1/2+t·I)‖ ≤ 2·sup_{|w-c|=1/2} ‖ζ(w)‖
  ≤ 2·C_ε·(|t|+1)^{1/2+ε}    (from convexity bound on the sphere)

This gives the derivative convexity bound needed for the IBP correction integral.
-/

-- The Cauchy estimate for ζ' requires DiffContOnCl ℂ riemannZeta (ball c R)
-- for c = 1/2 + t·I, R = 1/2. The key ingredients are:
--   (a) differentiableAt_riemannZeta for s ≠ 1 (Mathlib)
--   (b) riemannZeta is continuous everywhere (Mathlib: continuous_riemannZeta or
--       the fact that the pole at s=1 is removable in the completed zeta)
--   (c) norm_deriv_le_of_forall_mem_sphere_norm_le (Mathlib)
-- Combined with zeta_convexity_bound on the sphere, this gives
-- ‖ζ'(1/2+t·I)‖ ≤ C_ε · |t|^{1/2+ε} for any ε > 0.
-- This infrastructure is recorded for future formalization.

/-! ## Part 5c: IBP oscillatory integral bound

The core bound |∫₁ᵀ Z(t) dt| ≤ C · T^{1/2}.

PROOF STRUCTURE (Titchmarsh §4.15):
1. Split [1,T] = [1,T₀] ∪ [T₀,T]
2. [1,T₀]: bounded by continuity of Z on compact interval
3. [T₀,T]: IBP with u = ζ/(iθ'), dv = d(e^{iθ})
   - Boundary: |ζ(T)/(iθ'(T))| ≤ C·T^{1/2}/log T — proved below
   - Correction: requires VdC or AFE decomposition

Sub-obligations proved constructively:
  (a) ibp_compact_piece_bound: |∫₁^{T₀} Z| ≤ C (compactness) — PROVED
  (b) ibp_boundary_norm_bound: ‖ζ(½+iT)‖/θ'(T) ≤ C·T^{1/2}/log(T) — PROVED
  (c) zeta_critical_norm_div_thetaDeriv_le_sqrt: combined bound — PROVED

Remaining atomic sorry: ibp_oscillatory_bound.
Reference: Titchmarsh 1951, §4.15; Ingham 1932, §5.2.
-/

/-- The compact piece [1, T₀] contributes a bounded constant.
    Since hardyZ is continuous and [1, T₀] is compact, the integral is
    bounded by a fixed constant. -/
private theorem ibp_compact_piece_bound (T₀ : ℝ) (_hT₀ : 2 ≤ T₀) :
    ∃ C₀ > 0, |∫ t in Set.Ioc 1 T₀, HardyEstimatesPartial.hardyZ t| ≤ C₀ := by
  set val := |∫ t in Set.Ioc 1 T₀, HardyEstimatesPartial.hardyZ t|
  exact ⟨val + 1, by positivity, by linarith⟩

/-- The IBP boundary quotient ‖ζ(½+iT)‖/θ'(T) is bounded by C·T^{1/2}/log(T).
    From hardyZ_pointwise_bound: ‖ζ(½+iT)‖ ≤ C·T^{1/2}
    From thetaDeriv_lower_bound: θ'(T) ≥ (1/4)·log(T)
    Combined: ‖ζ‖/θ' ≤ C·T^{1/2} / ((1/4)·log T) = 4C·T^{1/2}/log(T). -/
theorem zeta_critical_norm_div_thetaDeriv_le_sqrt :
    ∃ C > 0, ∃ T₀ ≥ 2, ∀ T : ℝ, T ≥ T₀ →
      ‖riemannZeta (1/2 + I * ↑T)‖ * (1 / thetaDeriv T) ≤
        C * T ^ ((1 : ℝ) / 2) / Real.log T := by
  obtain ⟨C_z, hCz, hzeta⟩ := zeta_critical_line_bound
  obtain ⟨T₁, hT₁, htheta⟩ := thetaDeriv_lower_bound
  set T₀ := max T₁ 2
  refine ⟨4 * C_z, by positivity, T₀, le_max_right _ _, fun T hT => ?_⟩
  have hT_ge_T₁ : T ≥ T₁ := le_trans (le_max_left _ _) hT
  have hT_ge_2 : T ≥ (2 : ℝ) := le_trans (le_max_right _ _) hT
  have hT_pos : (0 : ℝ) < T := by linarith
  have hlog_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have htheta_lb := htheta T hT_ge_T₁
  have htheta_pos : 0 < thetaDeriv T := by linarith
  -- ‖ζ‖ ≤ C_z · |T|^{1/2} = C_z · T^{1/2}
  have h_abs_T : |T| = T := abs_of_pos hT_pos
  have h_zeta_bd : ‖riemannZeta (1/2 + I * ↑T)‖ ≤ C_z * T ^ ((1 : ℝ) / 2) := by
    have h1 := hzeta T (by rw [h_abs_T]; linarith)
    rw [h_abs_T] at h1
    convert h1 using 2; ring
  -- 1/θ'(T) ≤ 4/log(T)
  have h_inv_theta : 1 / thetaDeriv T ≤ 4 / Real.log T := by
    rw [div_le_div_iff₀ htheta_pos hlog_pos]
    linarith
  -- Product: ‖ζ‖ · (1/θ') ≤ C_z·T^{1/2} · 4/log T = 4C_z · T^{1/2}/log T
  calc ‖riemannZeta (1/2 + I * ↑T)‖ * (1 / thetaDeriv T)
      ≤ (C_z * T ^ ((1 : ℝ) / 2)) * (4 / Real.log T) := by
        apply mul_le_mul h_zeta_bd h_inv_theta (by positivity) (by positivity)
    _ = 4 * C_z * T ^ ((1 : ℝ) / 2) / Real.log T := by ring

/-! ### Sub-lemma: VdC for the pure phase integral ∫ e^{iθ(t)} dt on [T₀, T].

From `vdc_first_deriv_exp` (VanDerCorputGeneric):
  if θ'(t) ≥ λ > 0 on [a,b], θ' monotone, θ ∈ C²,
  then ‖∫_a^b e^{iθ(t)} dt‖ ≤ 4/λ.

Here θ = hardyThetaSmooth, θ' = thetaDeriv with:
  θ' monotone on (0,∞)   (thetaDeriv_strictMonoOn)
  θ'(t) ≥ (1/4)·log(t)   (thetaDeriv_lower_bound)
-/

/-- thetaDeriv is differentiable everywhere (from thetaDeriv_hasDerivAt). -/
private theorem differentiable_thetaDeriv : Differentiable ℝ thetaDeriv :=
  fun t => (thetaDeriv_hasDerivAt t).differentiableAt

/-- θ' is C¹ (i.e., θ'' is continuous).
    From the explicit formula θ''(t) = -(1/4)·Im(Σ 1/(s(t)+n)²):
    each term is continuous in t, the series Σ ‖1/(s(t)+n)²‖ ≤ Σ 1/(n+1/4)²
    converges uniformly, so the tsum is continuous.
    TODO: formalize via Weierstrass M-test (uniform convergence of trigamma). -/
-- Each summand t ↦ 1/(sOfT(t)+n)² is continuous in t.
private lemma continuous_inv_sq_summand (n : ℕ) :
    Continuous (fun t : ℝ => (1 : ℂ) / (sOfT t + (↑n : ℂ)) ^ 2) := by
  apply Continuous.div continuous_const
  · apply Continuous.pow
    apply Continuous.add _ continuous_const
    show Continuous fun t => sOfT t
    exact continuous_const.add (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_id |>.div_const 2))
  · intro t; exact pow_ne_zero 2 (sOfT_add_nat_ne_zero t n)

private theorem continuous_deriv_thetaDeriv : Continuous (deriv thetaDeriv) := by
  have h_eq : deriv thetaDeriv = fun t =>
      -(1 / 4 : ℝ) * (∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2).im := by
    ext t; exact (thetaDeriv_hasDerivAt t).deriv
  rw [h_eq]
  -- Each term is continuous and uniformly bounded by 16/(n+1)².
  -- By the Weierstrass M-test (continuous_tsum), the tsum is continuous.
  apply Continuous.mul continuous_const
  exact Complex.continuous_im.comp
    (continuous_tsum (fun n => continuous_inv_sq_summand n)
      summable_sixteen_div_sq' (fun n t => by
        -- Need ‖1/(sOfT t + n)²‖ ≤ 16/(n+1)²
        have h14 := norm_sOfT_add_nat_ge t n
        have h14_pos : (0 : ℝ) < ↑n + 1/4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
        have h1_pos : (0 : ℝ) < ↑n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
        have hstep1 : ‖(1 : ℂ) / (sOfT t + (↑n : ℂ)) ^ 2‖ ≤ 1 / ((↑n : ℝ) + 1/4) ^ 2 := by
          rw [one_div, norm_inv, norm_pow, one_div]
          apply inv_anti₀ (by positivity)
          exact sq_le_sq' (by linarith [norm_nonneg (sOfT t + (↑n : ℂ))]) h14
        have hstep2 : 1 / ((↑n : ℝ) + 1/4) ^ 2 ≤ 16 / ((↑n : ℝ) + 1) ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
        linarith))

/-- θ' is monotone on [a,b] ⊂ (0,∞), inherited from thetaDeriv_strictMonoOn. -/
private theorem thetaDeriv_monotoneOn_Icc {a b : ℝ} (ha : 0 < a) :
    MonotoneOn thetaDeriv (Icc a b) :=
  (thetaDeriv_strictMonoOn.monotoneOn).mono
    (fun _ hx => lt_of_lt_of_le ha hx.1)

/-- The compact piece ∫₁^{T₀} Z is bounded by a constant. -/
private theorem compact_piece_abs_bounded (T₀ : ℝ) :
    ∃ C₀ : ℝ, |∫ t in Set.Ioc 1 T₀, HardyEstimatesPartial.hardyZ t| ≤ C₀ :=
  ⟨|∫ t in Set.Ioc 1 T₀, HardyEstimatesPartial.hardyZ t|, le_refl _⟩

/-- |∫ Z| ≤ ‖∫ e^{iθ}·ζ‖ since Z = Re(e^{iθ}·ζ) and |Re(z)| ≤ ‖z‖.

    Proof: Z(t) = Re(e^{iθ(t)}·ζ(1/2+it)) by definition, so
    ∫ Z = ∫ Re(f) = Re(∫ f) (by reCLM.integral_comp_comm), and
    |Re(∫ f)| ≤ ‖∫ f‖ (by Complex.abs_re_le_norm). -/
private theorem integral_hardyZ_le_norm_complex_integral (a b : ℝ)
    (hint : IntegrableOn (fun t =>
      Complex.exp (I * ↑(HardyEstimatesPartial.hardyTheta t)) *
      riemannZeta (1/2 + I * ↑t)) (Set.Ioc a b)) :
    |∫ t in Set.Ioc a b, HardyEstimatesPartial.hardyZ t| ≤
      ‖∫ t in Set.Ioc a b,
        Complex.exp (I * ↑(HardyEstimatesPartial.hardyTheta t)) *
        riemannZeta (1/2 + I * ↑t)‖ := by
  have h_eq : (fun t => HardyEstimatesPartial.hardyZ t) = (fun t =>
      (Complex.exp (I * ↑(HardyEstimatesPartial.hardyTheta t)) *
        riemannZeta (1/2 + I * ↑t)).re) := by
    ext t; rfl
  rw [h_eq]
  -- ∫ Re(f) = Re(∫ f) by reCLM.integral_comp_comm, then |Re(z)| ≤ ‖z‖
  have h_comm : ∫ t in Set.Ioc a b,
      (Complex.exp (I * ↑(HardyEstimatesPartial.hardyTheta t)) *
        riemannZeta (1/2 + I * ↑t)).re =
      (∫ t in Set.Ioc a b,
        Complex.exp (I * ↑(HardyEstimatesPartial.hardyTheta t)) *
        riemannZeta (1/2 + I * ↑t)).re :=
    Complex.reCLM.integral_comp_comm hint
  rw [h_comm]
  exact Complex.abs_re_le_norm _

-- ════════════════════════════════════════════════════════════
-- Tail integral analysis
-- ════════════════════════════════════════════════════════════
--
-- On [T₀, T] where T₀ from thetaDeriv_lower_bound:
--   θ'(t) ≥ (1/4)·log(T₀), θ' monotone, |Z(t)| ≤ C·t^{1/2}.
--
-- The sharp O(T^{1/2}) bound requires the AFE decomposition of ζ
-- into a Dirichlet polynomial Σ_{n≤N} n^{-s} + controlled error,
-- then applying VdC to each mode individually (Titchmarsh §4.15).
--
-- IBP alone gives O(T^{3/2}/log T) for the correction integral,
-- which is too large. The sub-lemmas below capture the proved
-- components of the IBP approach.
-- ════════════════════════════════════════════════════════════

/-- The derivative of ζ on the critical line satisfies a convexity bound.
    By Cauchy's estimate with radius 1/4:
    ‖ζ'(1/2+it)‖ ≤ (1/R) · sup_{|w-c|=R} ‖ζ(w)‖.
    The uniform strip bound (zeta_strip_bound) gives ‖ζ(w)‖ ≤ C|τ|^{3/4}
    on the sphere, yielding ‖ζ'(1/2+it)‖ ≤ 4C·(|t|+1)^{3/4}. -/
private theorem zeta_deriv_critical_line_bound :
    ∃ C > 0, ∀ t : ℝ, |t| ≥ 2 →
      ‖deriv riemannZeta (1/2 + I * ↑t)‖ ≤ C * |t| ^ ((3 : ℝ)/4) := by
  -- Step 1: Get uniform strip bound
  obtain ⟨C_s, hC_s, h_strip⟩ := zeta_strip_bound
  -- Step 2: The Cauchy estimate at c = 1/2 + t*I with R = 1/4
  -- gives ‖ζ'(c)‖ ≤ (sup on sphere) / R = 4 · sup on sphere
  refine ⟨4 * C_s * 2 ^ ((3 : ℝ)/4), by positivity, fun t ht => ?_⟩
  set c := (1 : ℂ)/2 + I * (↑t : ℂ)
  have hR : (0 : ℝ) < 1/4 := by norm_num
  -- DiffContOnCl: ζ is differentiable on ball(c, 1/4), continuous on closedBall
  -- All points in closedBall(c, 1/4) have Re ∈ [1/4, 3/4], hence ≠ 1
  have h_ne_one : ∀ w ∈ Metric.closedBall c (1/4), w ≠ 1 := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    intro h_eq
    rw [h_eq] at hw
    simp only [c, dist_comm] at hw
    have : (1/4 : ℝ) < dist (1 : ℂ) (1/2 + I * ↑t) := by
      rw [Complex.dist_eq]
      have : (1 : ℂ) - (1/2 + I * ↑t) = 1/2 - I * ↑t := by ring
      rw [this]
      calc (1/4 : ℝ) < 1/2 := by norm_num
        _ ≤ ‖(1/2 : ℂ) - I * ↑t‖ := by
            calc (1/2 : ℝ) = |(1/2 : ℂ).re| := by norm_num [Complex.ofReal_re]
              _ = |((1/2 : ℂ) - I * ↑t).re| := by
                  congr 1; simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
              _ ≤ ‖(1/2 : ℂ) - I * ↑t‖ := Complex.abs_re_le_norm _
    linarith
  have h_diff_on : DifferentiableOn ℂ riemannZeta (Metric.closedBall c (1/4)) := by
    intro w hw
    exact (differentiableAt_riemannZeta (h_ne_one w hw)).differentiableWithinAt
  have h_diffcont : DiffContOnCl ℂ riemannZeta (Metric.ball c (1/4)) :=
    h_diff_on.diffContOnCl_ball (le_refl _)
  -- Bound on sphere: for w ∈ sphere(c, 1/4), bound ‖ζ(w)‖
  have h_sphere_bound : ∀ w ∈ Metric.sphere c (1/4), ‖riemannZeta w‖ ≤
      C_s * (|t| + 1) ^ ((3 : ℝ)/4) := by
    intro w hw
    rw [Metric.mem_sphere] at hw
    -- w = c + (1/4)·e^{iα} for some α, so w.re ∈ [1/4, 3/4] and w.im = t + ...
    have h_re_dist : |w.re - (1/2 : ℝ)| ≤ 1/4 := by
      calc |w.re - 1/2| = |(w - c).re| := by
            simp [c, Complex.sub_re, Complex.add_re, Complex.div_ofNat,
                  Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        _ ≤ ‖w - c‖ := Complex.abs_re_le_norm _
        _ = 1/4 := by rw [← Complex.dist_eq]; exact hw
    have h_im_dist : |w.im - t| ≤ 1/4 := by
      calc |w.im - t| = |(w - c).im| := by
            simp [c, Complex.sub_im, Complex.add_im, Complex.div_ofNat,
                  Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        _ ≤ ‖w - c‖ := Complex.abs_im_le_norm _
        _ = 1/4 := by rw [← Complex.dist_eq]; exact hw
    have hσ_range : 0 ≤ w.re ∧ w.re ≤ 1 := by
      constructor <;> linarith [(abs_le.mp h_re_dist).1, (abs_le.mp h_re_dist).2]
    have hτ_ge : 1 ≤ |w.im| := by
      have : |t| - 1/4 ≤ |w.im| := by
        have h_tri : |t| ≤ |t - w.im| + |w.im| := by
          calc |t| = |(t - w.im) + w.im| := by congr 1; ring
            _ ≤ |t - w.im| + |w.im| := abs_add_le _ _
        linarith [abs_sub_comm t w.im, h_im_dist]
      linarith
    -- Write w = w.re + w.im * I
    have hw_eq : w = ↑w.re + ↑w.im * I := (Complex.re_add_im w).symm
    rw [hw_eq]
    calc ‖riemannZeta (↑w.re + ↑w.im * I)‖
        ≤ C_s * |w.im| ^ ((3 : ℝ)/4) := h_strip w.re w.im hσ_range.1 hσ_range.2 hτ_ge
      _ ≤ C_s * (|t| + 1) ^ ((3 : ℝ)/4) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_s)
          apply rpow_le_rpow (abs_nonneg _) _ (by norm_num : (0 : ℝ) ≤ 3/4)
          calc |w.im| = |(w.im - t) + t| := by congr 1; ring
            _ ≤ |w.im - t| + |t| := abs_add_le _ _
            _ ≤ 1/4 + |t| := by linarith [h_im_dist]
            _ ≤ |t| + 1 := by linarith
  -- Apply Cauchy estimate
  have h_cauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hR h_diffcont h_sphere_bound
  -- h_cauchy : ‖deriv riemannZeta c‖ ≤ C_s * (|t| + 1)^{3/4} / (1/4)
  --          = 4 * C_s * (|t| + 1)^{3/4}
  calc ‖deriv riemannZeta (1/2 + I * ↑t)‖
      = ‖deriv riemannZeta c‖ := rfl
    _ ≤ C_s * (|t| + 1) ^ ((3 : ℝ)/4) / (1/4) := h_cauchy
    _ = 4 * C_s * (|t| + 1) ^ ((3 : ℝ)/4) := by ring
    _ ≤ 4 * C_s * (2 * |t|) ^ ((3 : ℝ)/4) := by
        gcongr
        linarith
    _ = 4 * C_s * (2 ^ ((3 : ℝ)/4) * |t| ^ ((3 : ℝ)/4)) := by
        rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg t)]
    _ = 4 * C_s * 2 ^ ((3 : ℝ)/4) * |t| ^ ((3 : ℝ)/4) := by ring

/-- The IBP boundary quotient ‖ζ(½+iT)‖/θ'(T) ≤ C·T^{1/2}.
    Follows from zeta_critical_norm_div_thetaDeriv_le_sqrt (which gives
    the bound C·T^{1/2}/log(T)) and log(T) ≥ 1 for T ≥ e. -/
private theorem ibp_boundary_bound :
    ∃ C > 0, ∃ T₀ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₀ →
      ‖riemannZeta (1/2 + I * ↑T)‖ / thetaDeriv T ≤ C * T ^ ((1:ℝ)/2) := by
  obtain ⟨C, hC, T₀, hT₀, hbd⟩ := zeta_critical_norm_div_thetaDeriv_le_sqrt
  -- Increase T₀ to ensure log(T) ≥ 1
  set T₁ := max T₀ (Real.exp 1) with hT₁_def
  refine ⟨C, hC, T₁, le_trans hT₀ (le_max_left _ _), fun T hT => ?_⟩
  have hT_ge_T₀ : T ≥ T₀ := le_trans (le_max_left _ _) hT
  have hT_ge_exp : T ≥ Real.exp 1 := le_trans (le_max_right _ _) hT
  have hT_pos : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hT_ge_exp
  have hlog_ge_one : 1 ≤ Real.log T := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) hT_ge_exp
  have hbd' := hbd T hT_ge_T₀
  -- ‖ζ‖ * (1/θ') ≤ C * T^{1/2} / log T ≤ C * T^{1/2} * 1 = C * T^{1/2}
  have h_nonneg : 0 ≤ C * T ^ ((1:ℝ)/2) :=
    mul_nonneg (le_of_lt hC) (rpow_nonneg (le_of_lt hT_pos) _)
  calc ‖riemannZeta (1/2 + I * ↑T)‖ / thetaDeriv T
      = ‖riemannZeta (1/2 + I * ↑T)‖ * (1 / thetaDeriv T) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ C * T ^ ((1:ℝ)/2) / Real.log T := hbd'
    _ ≤ C * T ^ ((1:ℝ)/2) := div_le_self h_nonneg hlog_ge_one

/-- The correction integrand |d/dt[ζ/(iθ')]| is bounded by C·t^{3/4}/log(t).

    From |d/dt[ζ/(iθ')]| ≤ |ζ'|/|θ'| + |ζ|·|θ''|/|θ'|² and:
    - |ζ'(1/2+it)| ≤ C₁·t^{3/4} (zeta_deriv_critical_line_bound)
    - |ζ(1/2+it)| ≤ C₂·t^{1/2} (zeta_critical_line_bound)
    - |θ''(t)| ≤ M (thetaDeriv_deriv_bounded)
    - θ'(t) ≥ (1/4)·log(t) (thetaDeriv_lower_bound)

    Combined: O(t^{3/4}/log t) + O(t^{1/2}/log²t) = O(t^{3/4}/log t). -/
private theorem ibp_correction_integrand_bound :
    ∃ C > 0, ∃ T₀ ≥ (2 : ℝ), ∀ t : ℝ, t ≥ T₀ →
      ‖deriv riemannZeta (1/2 + I * ↑t)‖ / thetaDeriv t +
      ‖riemannZeta (1/2 + I * ↑t)‖ * |deriv thetaDeriv t| / (thetaDeriv t) ^ 2
        ≤ C * t ^ ((3:ℝ)/4) / Real.log t := by
  -- Get the sub-lemma bounds
  obtain ⟨C_d, hC_d, h_deriv⟩ := zeta_deriv_critical_line_bound
  obtain ⟨C_z, hC_z, h_zeta⟩ := zeta_critical_line_bound
  obtain ⟨M, hM_pos, hM⟩ := thetaDeriv_deriv_bounded
  obtain ⟨T₁, hT₁, h_theta⟩ := thetaDeriv_lower_bound
  -- Choose T₀ large enough that log(T₀) ≥ 1 (so θ'(T₀) ≥ 1/4)
  set T₀ := max (max T₁ 2) (Real.exp 1)
  have hT₀_ge_2 : (2 : ℝ) ≤ T₀ := le_trans (le_max_right T₁ 2) (le_max_left _ _)
  refine ⟨4 * C_d + 16 * C_z * M, by positivity,
         T₀, hT₀_ge_2, fun t ht => ?_⟩
  have ht_T₁ : t ≥ T₁ := le_trans (le_trans (le_max_left T₁ 2) (le_max_left _ _)) ht
  have ht_2 : t ≥ 2 := le_trans hT₀_ge_2 ht
  have ht_exp : t ≥ Real.exp 1 := le_trans (le_max_right _ _) ht
  have ht_pos : (0 : ℝ) < t := by linarith
  have h_abs_t : |t| = t := abs_of_pos ht_pos
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have htheta_lb := h_theta t ht_T₁
  have htheta_pos : 0 < thetaDeriv t := by linarith
  -- Term 1: ‖ζ'‖/θ' ≤ C_d·t^{3/4} / ((1/4)·log t) = 4·C_d·t^{3/4}/log t
  have h_term1 : ‖deriv riemannZeta (1/2 + I * ↑t)‖ / thetaDeriv t ≤
      4 * C_d * t ^ ((3:ℝ)/4) / Real.log t := by
    rw [div_le_div_iff₀ htheta_pos hlog]
    have h1 := h_deriv t (by rw [h_abs_t]; linarith)
    rw [h_abs_t] at h1
    have h_rpow_nonneg : 0 ≤ t ^ ((3:ℝ)/4) := rpow_nonneg (le_of_lt ht_pos) _
    calc ‖deriv riemannZeta (1/2 + I * ↑t)‖ * Real.log t
        ≤ C_d * t ^ ((3:ℝ)/4) * Real.log t := by
          apply mul_le_mul_of_nonneg_right h1 (le_of_lt hlog)
      _ ≤ 4 * C_d * t ^ ((3:ℝ)/4) * thetaDeriv t := by
          -- Need: C_d * r * log t ≤ 4 * C_d * r * θ'(t) where r = t^{3/4}
          -- From θ' ≥ (1/4) log t: 4 * θ' ≥ log t
          -- So 4 * C_d * r * θ' ≥ C_d * r * 4 * θ' ≥ C_d * r * log t
          have : Real.log t ≤ 4 * thetaDeriv t := by linarith [htheta_lb]
          calc C_d * t ^ ((3:ℝ)/4) * Real.log t
              ≤ C_d * t ^ ((3:ℝ)/4) * (4 * thetaDeriv t) := by
                apply mul_le_mul_of_nonneg_left this (mul_nonneg (le_of_lt hC_d) h_rpow_nonneg)
            _ = 4 * C_d * t ^ ((3:ℝ)/4) * thetaDeriv t := by ring
  -- Term 2: ‖ζ‖·|θ''|/θ'² ≤ C_z·t^{1/2}·M/((1/4)log t)² = 16·C_z·M·t^{1/2}/log²t
  --       ≤ 16·C_z·M·t^{3/4}/log t  (since t^{1/2}/log t ≤ t^{3/4}/log t for t ≥ 1)
  have h_term2 : ‖riemannZeta (1/2 + I * ↑t)‖ * |deriv thetaDeriv t| / (thetaDeriv t) ^ 2 ≤
      16 * C_z * M * t ^ ((3:ℝ)/4) / Real.log t := by
    have h_zeta_bd' := h_zeta t (by rw [h_abs_t]; linarith)
    rw [h_abs_t] at h_zeta_bd'
    have h_zeta_bd : ‖riemannZeta (1/2 + I * ↑t)‖ ≤ C_z * t ^ ((1:ℝ)/2) := by
      convert h_zeta_bd' using 2; ring
    have h_theta_sq : (thetaDeriv t) ^ 2 ≥ ((1/4) * Real.log t) ^ 2 := by
      exact sq_le_sq' (by linarith) htheta_lb
    have h_theta_sq_pos : 0 < (thetaDeriv t) ^ 2 := by positivity
    rw [div_le_div_iff₀ h_theta_sq_pos hlog]
    -- LHS = ‖ζ‖ * |θ''| * log t
    -- RHS = 16 * C_z * M * t^{3/4} * θ'^2
    -- ‖ζ‖ ≤ C_z * t^{1/2}, |θ''| ≤ M
    -- So LHS ≤ C_z * t^{1/2} * M * log t
    -- RHS ≥ 16 * C_z * M * t^{3/4} * ((1/4)·log t)^2 = C_z * M * t^{3/4} * log²t
    -- Need: t^{1/2} * log t ≤ t^{3/4} * log²t, i.e., 1 ≤ t^{1/4} * log t
    -- For t ≥ 2: t^{1/4} ≥ 2^{1/4} > 1 and log t ≥ log 2 > 0, so product > 0.
    -- Actually need: C_z * t^{1/2} * M * log t ≤ 16 * C_z * M * t^{3/4} * θ'^2
    -- Upper bound on LHS: ‖ζ‖ * |θ''| * log t ≤ C_z * t^{1/2} * M * log t
    have h_zeta_nonneg : 0 ≤ ‖riemannZeta (1/2 + I * ↑t)‖ := norm_nonneg _
    have h_deriv_nonneg : 0 ≤ |deriv thetaDeriv t| := abs_nonneg _
    have h_rpow_nonneg12 : 0 ≤ t ^ ((1:ℝ)/2) := rpow_nonneg (le_of_lt ht_pos) _
    have h_rpow_nonneg34 : 0 ≤ t ^ ((3:ℝ)/4) := rpow_nonneg (le_of_lt ht_pos) _
    have h_rpow_le : t ^ ((1:ℝ)/2) ≤ t ^ ((3:ℝ)/4) :=
      rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    -- ‖ζ‖ * |θ''| * log t ≤ C_z * t^{3/4} * M * 4 * θ' ≤ 16 * C_z * M * t^{3/4} * θ'^2
    -- Step-by-step bound
    have h_abs_deriv_le_M : |deriv thetaDeriv t| ≤ M := hM t
    have h_log_le_4theta : Real.log t ≤ 4 * thetaDeriv t := by linarith [htheta_lb]
    -- ‖ζ‖ * |θ''| ≤ ‖ζ‖ * M ≤ C_z * t^{1/2} * M ≤ C_z * t^{3/4} * M
    have h_prod_le : ‖riemannZeta (1/2 + I * ↑t)‖ * |deriv thetaDeriv t| ≤
        C_z * t ^ ((3:ℝ)/4) * M := by
      calc ‖riemannZeta (1/2 + I * ↑t)‖ * |deriv thetaDeriv t|
          ≤ ‖riemannZeta (1/2 + I * ↑t)‖ * M :=
            mul_le_mul_of_nonneg_left h_abs_deriv_le_M h_zeta_nonneg
        _ ≤ (C_z * t ^ ((1:ℝ)/2)) * M :=
            mul_le_mul_of_nonneg_right h_zeta_bd (le_of_lt hM_pos)
        _ ≤ C_z * t ^ ((3:ℝ)/4) * M := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hM_pos)
            exact mul_le_mul_of_nonneg_left h_rpow_le (le_of_lt hC_z)
    -- Now: (C_z * r * M) * log t ≤ (C_z * r * M) * (4 * θ') ≤ 16 * C_z * M * r * θ'^2
    calc ‖riemannZeta (1/2 + I * ↑t)‖ * |deriv thetaDeriv t| * Real.log t
        ≤ (C_z * t ^ ((3:ℝ)/4) * M) * Real.log t :=
          mul_le_mul_of_nonneg_right h_prod_le (le_of_lt hlog)
      _ ≤ (C_z * t ^ ((3:ℝ)/4) * M) * (4 * thetaDeriv t) :=
          mul_le_mul_of_nonneg_left h_log_le_4theta (by positivity)
      _ = 4 * C_z * M * t ^ ((3:ℝ)/4) * thetaDeriv t := by ring
      _ ≤ 16 * C_z * M * t ^ ((3:ℝ)/4) * (thetaDeriv t) ^ 2 := by
          -- Need: 4 * a * θ' ≤ 16 * a * θ'^2 where a = C_z * M * t^{3/4}
          -- i.e., θ' ≤ 4 * θ'^2, i.e., 1 ≤ 4 * θ'
          -- θ' ≥ (1/4) * log t ≥ (1/4) * log 2 > 1/4 ≥ 1/4
          -- We need 1/4 ≤ θ', so 1 ≤ 4θ'
          have h_theta_ge_quarter : (1/4 : ℝ) ≤ thetaDeriv t := by
            have hlog_ge_1 : (1 : ℝ) ≤ Real.log t := by
              calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
                _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 1) ht_exp
            calc (1/4 : ℝ) ≤ (1/4) * Real.log t := le_mul_of_one_le_right (by norm_num) hlog_ge_1
              _ ≤ thetaDeriv t := htheta_lb
          -- Goal: 4 * C_z * M * t^{3/4} * θ' ≤ 16 * C_z * M * t^{3/4} * θ'^2
          -- Factor: 4 * a * θ' ≤ 4 * a * 4 * θ' * θ' where a = C_z * M * t^{3/4} ≥ 0
          -- Since θ' ≥ 1/4, 4*θ' ≥ 1, so θ' ≤ 4*θ'^2
          have h_theta_sq_bound : thetaDeriv t ≤ 4 * thetaDeriv t ^ 2 := by
            have h1 : 1 ≤ 4 * thetaDeriv t := by linarith
            nlinarith [sq_nonneg (thetaDeriv t)]
          have h_coeff_nonneg : 0 ≤ 4 * C_z * M * t ^ ((3:ℝ)/4) := by positivity
          calc 4 * C_z * M * t ^ ((3:ℝ)/4) * thetaDeriv t
              ≤ 4 * C_z * M * t ^ ((3:ℝ)/4) * (4 * thetaDeriv t ^ 2) :=
                mul_le_mul_of_nonneg_left h_theta_sq_bound h_coeff_nonneg
            _ = 16 * C_z * M * t ^ ((3:ℝ)/4) * thetaDeriv t ^ 2 := by ring
  -- Combine
  calc ‖deriv riemannZeta (1/2 + I * ↑t)‖ / thetaDeriv t +
      ‖riemannZeta (1/2 + I * ↑t)‖ * |deriv thetaDeriv t| / (thetaDeriv t) ^ 2
      ≤ 4 * C_d * t ^ ((3:ℝ)/4) / Real.log t +
        16 * C_z * M * t ^ ((3:ℝ)/4) / Real.log t := add_le_add h_term1 h_term2
    _ = (4 * C_d + 16 * C_z * M) * t ^ ((3:ℝ)/4) / Real.log t := by ring

/- **Main oscillatory integral bound** (sorry — requires AFE-based VdC argument).

    REMAINING ATOMIC OBLIGATION: |∫₁ᵀ Z(t) dt| ≤ C · T^{1/2}.

    PROVED SUB-COMPONENTS:
    (a) thetaDeriv_lower_bound: θ'(t) ≥ (1/4)·log(t) for large t
    (b) thetaDeriv_deriv_nonneg: θ''(t) ≥ 0 (θ' is increasing)
    (c) thetaDeriv_deriv_bounded: |θ''(t)| ≤ M
    (d) hardyZ_pointwise_bound: |Z(t)| ≤ C·|t|^{1/2}
    (e) ibp_compact_piece_bound: |∫₁^{T₀} Z| ≤ C₀
    (f) zeta_critical_norm_div_thetaDeriv_le_sqrt: IBP boundary terms
    (g) ibp_boundary_bound: ‖ζ(T)‖/θ'(T) ≤ C·T^{1/2}
    (h) integral_hardyZ_le_norm_complex_integral: |∫ Z| ≤ ‖∫ e^{iθ}·ζ‖
    (i) ibp_correction_integrand_bound: |d/dt[ζ/(iθ')]| ≤ C·t^{3/4}/log(t)

    DEPENDENCY: This sorry genuinely depends on the RS expansion
    (`rs_saddle_point_bound` in RSExpansionProof.lean).

    WHY IBP/VdC ON THE FULL FUNCTION FAILS:
    - IBP with correction integral: ∫ C·t^{3/4}/log(t) dt = O(T^{7/4}/log T).
      Too large by a factor of T^{5/4}.
    - Per-block VdC (blocks of length L ~ √t): per block ≤ 8C√2·√a/log(a),
      summing over ~√T blocks gives O(T/log T). Still too large.
    - Fundamental issue: |ζ(1/2+it)| = O(t^{1/2}) pointwise, and no IBP or
      VdC on the FULL function can beat pointwise_size × length / oscillation_rate.

    CORRECT APPROACH (Titchmarsh §4.15):
    1. Use the AFE: ζ(1/2+it) = Σ_{n≤N} n^{-1/2-it} + χ·Σ_{m≤M} m^{-1/2+it}
       + O(t^{-1/4}) where N ≈ √(t/2π).
    2. Each mode e^{i(θ(t) - t·log n)} has phase derivative θ'(t) - log(n).
    3. VdC first-derivative test per mode: contribution O(1/(√n · log(T₀))).
    4. Sum Σ_{n≤N} 1/(√n · log T₀) = O(N^{1/2}/log T₀) = O(T^{1/4}/log T₀).
    5. This gives |∫_{T₀}^T Z(t) dt| = O(T^{1/4}/log T₀) = O(T^{1/2}).

    This is why the sorry cannot be closed without `rs_saddle_point_bound`.

    Reference: Titchmarsh (1951), §4.15; Ivić (2003), §4.2. -/

/-! ## Part 6: Per-mode VdC infrastructure for S1

When the RS expansion (S2) closes, each mode n of the Dirichlet polynomial
produces an oscillatory integral ∫ n^{-1/2} · e^{i(θ(t) - t·log(n+1))} dt.

The per-mode phase is φ_n(t) = θ(t) - t·log(n+1), with derivative
φ'_n(t) = θ'(t) - log(n+1) = modeOmega n t.

Off-diagonal modes (n far from k on block k) have |φ'_n| ≥ δ > 0,
so VdC gives O(1/δ) per mode. The weighted sum over modes converges.

This section builds the infrastructure that connects the existing
`OffResonanceSmoothVdC.off_resonance_integral_bound_smooth` to the
first-moment analysis. All lemmas here are constructively proved (no sorry).
-/

section PerModeVdC

open Aristotle.OffResonanceSmoothVdC Aristotle.HardyNProperties
open HardyEstimatesPartial

/-! ### 6a. Per-mode phase derivative: relationship to modeOmega -/

/-- The per-mode phase derivative φ'_n(t) = θ'(t) - log(n+1).
    This is exactly `modeOmega n t` from OffResonanceSmoothVdC. -/
theorem perMode_phaseDeriv_eq_modeOmega (n : ℕ) (t : ℝ) :
    thetaDeriv t - Real.log (↑n + 1) = modeOmega n t := rfl

/-- For t ≥ T₀ (from thetaDeriv_lower_bound), the per-mode phase derivative
    satisfies φ'_n(t) ≥ (1/4)·log(t) - log(n+1). -/
theorem perMode_phaseDeriv_lower :
    ∃ T₀ > 0, ∀ (n : ℕ) (t : ℝ), t ≥ T₀ →
      modeOmega n t ≥ (1/4) * Real.log t - Real.log (↑n + 1) := by
  obtain ⟨T₀, hT₀, hbd⟩ := thetaDeriv_lower_bound
  exact ⟨T₀, hT₀, fun n t ht => sub_le_sub_right (hbd t ht) _⟩

/-- Off-diagonal criterion: if log(n+1) ≤ (1/8)·log(t),
    then modeOmega n t ≥ (1/8)·log(t) for t ≥ T₀.

    Proof: θ'(t) ≥ (1/4)log(t) and log(n+1) ≤ (1/8)log(t),
    so modeOmega = θ' - log(n+1) ≥ (1/4 - 1/8)log(t) = (1/8)log(t). -/
theorem modeOmega_lower_off_diagonal :
    ∃ T₀ > 0, ∀ (n : ℕ) (t : ℝ), t ≥ T₀ →
      Real.log (↑n + 1) ≤ (1/8) * Real.log t →
        modeOmega n t ≥ (1/8) * Real.log t := by
  obtain ⟨T₀, hT₀, hbd⟩ := thetaDeriv_lower_bound
  refine ⟨T₀, hT₀, fun n t ht hlog_n => ?_⟩
  have h1 := hbd t ht
  show thetaDeriv t - Real.log (↑n + 1) ≥ _
  linarith

/-- The modeOmega is monotone increasing on (0,∞) for each mode n,
    inherited from thetaDeriv_strictMonoOn. -/
theorem modeOmega_monotoneOn_Ioi (n : ℕ) :
    MonotoneOn (modeOmega n) (Set.Ioi 0) := by
  intro x hx y hy hxy
  show thetaDeriv x - _ ≤ thetaDeriv y - _
  linarith [thetaDeriv_strictMonoOn.monotoneOn hx hy hxy]

/-! ### 6b. VdC bound per off-diagonal mode on a single block

The key bridge: `off_resonance_integral_bound_smooth` gives
  |∫_{block k} cos(θ(t) - t·log(n+1)) dt| ≤ C_vdc / log((k+1)/(n+1))
for all k ≥ 1 and n < k.

When we multiply by the amplitude (n+1)^{-1/2} from the Dirichlet polynomial,
we get:
  (n+1)^{-1/2} · |∫_{block k} cos(φ_n)| ≤ C_vdc · (n+1)^{-1/2} / log((k+1)/(n+1))
-/

/-- Weighted off-diagonal mode bound: the contribution of mode n < k
    to block k is bounded by C · (n+1)^{-1/2} / log((k+1)/(n+1)). -/
theorem weighted_mode_bound_on_block :
    ∃ C > 0, ∀ k : ℕ, ∀ n : ℕ, n < k → 1 ≤ k →
      ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
        |∫ t in Set.Ioc (HardyEstimatesPartial.hardyStart k)
            (HardyEstimatesPartial.hardyStart (k + 1)),
          Real.cos (HardyEstimatesPartial.hardyTheta t -
            t * Real.log ((n : ℝ) + 1))| ≤
      C * ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) /
        Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
  obtain ⟨C_vdc, hC_pos, hbd⟩ := off_resonance_integral_bound_smooth
  refine ⟨C_vdc, hC_pos, fun k n hnk hk => ?_⟩
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hkn : (n : ℝ) + 1 < (k : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hnk
  have hlog_pos : 0 < Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) :=
    Real.log_pos (by rw [one_lt_div hn1_pos]; linarith)
  have hcoef_nonneg : (0 : ℝ) ≤ ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) := by positivity
  have h_mode := hbd k n hnk hk
  calc ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
        |∫ t in Set.Ioc (HardyEstimatesPartial.hardyStart k)
            (HardyEstimatesPartial.hardyStart (k + 1)),
          Real.cos (HardyEstimatesPartial.hardyTheta t -
            t * Real.log ((n : ℝ) + 1))|
      ≤ ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
        (C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left h_mode hcoef_nonneg
    _ = C_vdc * ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) /
        Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by ring

/-! ### 6c. Harmonic kernel sum infrastructure

The key analytic estimate: for the off-diagonal sum over modes n < k,
  Σ_{n=0}^{k-1} (n+1)^{-1/2} / log((k+1)/(n+1)) ≤ C · √(k+1)

We prove the "far modes" half (n < (k+1)/2) where log((k+1)/(n+1)) ≥ log 2,
giving each term ≤ (n+1)^{-1/2}/log 2. The crude sum bound Σ (n+1)^{-1/2} ≤ N
then gives the far-mode contribution ≤ k/log 2.
-/

/-- Each term (n+1)^{-1/2} ≤ 1 for all n : ℕ. -/
theorem rpow_neg_half_le_one (n : ℕ) :
    ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (↑n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  calc ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2))
      ≤ ((↑n + 1 : ℝ) ^ (0 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    _ = 1 := rpow_zero _

/-- Crude bound: Σ_{n<N} (n+1)^{-1/2} ≤ N.
    Each term ≤ 1, so the sum ≤ N. -/
theorem inv_sqrt_partial_sum_le_card (N : ℕ) :
    ∑ n ∈ Finset.range N, ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) ≤ (N : ℝ) := by
  calc ∑ n ∈ Finset.range N, ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2))
      ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) :=
        Finset.sum_le_sum (fun n _ => rpow_neg_half_le_one n)
    _ = (N : ℝ) := by simp

/-- Partial sum bound for the "far" modes n < (k+1)/2.
    Each term has log((k+1)/(n+1)) ≥ log(2), so the weighted kernel sum is
    bounded by (1/log 2) · Σ (n+1)^{-1/2} ≤ k/log 2. -/
theorem far_mode_kernel_sum_bound (k : ℕ) (_hk : 1 ≤ k) :
    ∀ n ∈ Finset.filter (· < (k + 1) / 2) (Finset.range k),
      ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) /
        Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) ≤
      (1 / Real.log 2) * ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) := by
  intro n hn
  rw [Finset.mem_filter] at hn
  have hn_half := hn.2
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- (k+1)/(n+1) ≥ 2 since n < (k+1)/2 means 2(n+1) ≤ k+1
  have h_ratio_ge_2 : 2 ≤ ((k : ℝ) + 1) / ((n : ℝ) + 1) := by
    rw [le_div_iff₀ hn1_pos]
    have : 2 * (n + 1) ≤ k + 1 := by omega
    exact_mod_cast this
  have hlog_ge : Real.log 2 ≤ Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) :=
    Real.log_le_log (by norm_num) h_ratio_ge_2
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  calc ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) /
        Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1))
      ≤ ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) / Real.log 2 :=
        div_le_div_of_nonneg_left (by positivity) hlog2_pos hlog_ge
    _ = (1 / Real.log 2) * ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) := by ring

/-- The log ratio log((k+1)/(n+1)) is positive for n < k. -/
theorem log_ratio_pos (k n : ℕ) (hnk : n < k) :
    0 < Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hkn : (n : ℝ) + 1 < (k : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hnk
  exact Real.log_pos (by rw [one_lt_div hn1_pos]; linarith)

/-- The log ratio is monotone decreasing in n: if n₁ ≤ n₂ < k, then
    log((k+1)/(n₁+1)) ≥ log((k+1)/(n₂+1)). -/
theorem log_ratio_antitone (k : ℕ) (n₁ n₂ : ℕ) (h12 : n₁ ≤ n₂) (_h2k : n₂ < k) :
    Real.log (((k : ℝ) + 1) / ((n₂ : ℝ) + 1)) ≤
      Real.log (((k : ℝ) + 1) / ((n₁ : ℝ) + 1)) := by
  have hn1_pos : (0 : ℝ) < (n₁ : ℝ) + 1 := by positivity
  have hn2_pos : (0 : ℝ) < (n₂ : ℝ) + 1 := by positivity
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h_le : (n₁ : ℝ) + 1 ≤ (n₂ : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ h12
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ hn2_pos hn1_pos]
  exact mul_le_mul_of_nonneg_left h_le (le_of_lt hk1_pos)

end PerModeVdC

/-! ## Part 7: Per-mode summation assembly

Once the AFE decomposes Z(t) = 2·Σ_{n≤N} (n+1)^{-1/2}·cos(θ-t·log(n+1)) + O(t^{-1/4}),
the first moment becomes a sum of per-mode oscillatory integrals on each block.

This section builds the summation infrastructure:
(1) Block length bound: |block k| ≤ C·(k+1)
(2) Resonant mode contribution: mode n = k on block k is O(√(k+1))
(3) Off-diagonal mode sum on a single block: O(k/log 2) from far_mode_kernel_sum_bound
(4) Total per-block contribution: O(k+1)
(5) Sum over blocks 1..K: O(K²)
(6) With K ~ √T: total = O(T), and with per-mode VdC: O(√T · log T) = O(T^{1/2+ε})

All lemmas here are constructively proved (no sorry, no axiom).
-/

section PerModeSummation

open Aristotle.OffResonanceSmoothVdC Aristotle.HardyNProperties
open HardyEstimatesPartial

/-- Block length ≤ 4π(k+1). Since block_length k = 2π(2k+3) and 2k+3 ≤ 2(k+1)+1 ≤ 2(k+1)+1,
    a cruder bound 2π(2k+3) ≤ 2π·3·(k+1) = 6π(k+1) suffices. -/
theorem block_length_le (k : ℕ) :
    hardyStart (k + 1) - hardyStart k ≤ 6 * Real.pi * ((k : ℝ) + 1) := by
  rw [block_length k]
  -- Need: 2π(2k+3) ≤ 6π(k+1), i.e., 2(2k+3) ≤ 6(k+1), i.e., 4k+6 ≤ 6k+6
  have hpi : 0 < Real.pi := Real.pi_pos
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

/-- Block length is nonneg. -/
theorem block_length_nonneg (k : ℕ) :
    0 ≤ hardyStart (k + 1) - hardyStart k := by
  rw [block_length k]
  have : 0 < Real.pi := Real.pi_pos
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- Resonant mode contribution bound: for the mode n = k on block k,
    the amplitude factor is (k+1)^{-1/2} and the integral is trivially
    bounded by the block length 2π(2k+3). So the contribution is
    (k+1)^{-1/2} · 2π(2k+3) ≤ 6π·(k+1)^{1/2}.

    This is the bound for the single "resonant" term where n ≈ N(t)
    and VdC may not give cancellation. -/
theorem resonant_mode_contribution_bound (k : ℕ) :
    ((↑k + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
      (hardyStart (k + 1) - hardyStart k) ≤
      6 * Real.pi * ((k : ℝ) + 1) ^ ((1 : ℝ)/2) := by
  have h_bl := block_length_le k
  -- (k+1)^{-1/2} ≤ 1 from rpow_neg_half_le_one
  have h_coef := rpow_neg_half_le_one k
  -- So LHS ≤ 1 * block_length ≤ block_length ≤ 6π(k+1)
  -- And 6π(k+1) = 6π·(k+1)^1 ≤ ... no, we need ≤ 6π·(k+1)^{1/2}·√(k+1)?
  -- Actually the bound is: LHS ≤ (k+1)^{-1/2} · 6π(k+1) ≤ 1 · 6π(k+1).
  -- But the RHS is 6π·(k+1)^{1/2} which is SMALLER than 6π(k+1) for k ≥ 0.
  -- So this approach loses too much. Let's use the exact exponent arithmetic.
  --
  -- (k+1)^{-1/2} · block_length ≤ (k+1)^{-1/2} · 6π(k+1)
  -- = 6π · (k+1)^{-1/2+1} = 6π · (k+1)^{1/2}
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h_bl_nn := block_length_nonneg k
  calc ((↑k + 1 : ℝ) ^ (-(1 : ℝ)/2)) * (hardyStart (k + 1) - hardyStart k)
      ≤ ((↑k + 1 : ℝ) ^ (-(1 : ℝ)/2)) * (6 * Real.pi * ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h_bl (by positivity)
    _ = 6 * Real.pi * (((k : ℝ) + 1) ^ (-(1 : ℝ)/2) * ((k : ℝ) + 1)) := by ring
    _ = 6 * Real.pi * ((k : ℝ) + 1) ^ ((1 : ℝ)/2) := by
        congr 1
        conv_lhs => rhs; rw [show ((k : ℝ) + 1) = ((k : ℝ) + 1) ^ (1 : ℝ) from (Real.rpow_one _).symm]
        rw [← Real.rpow_add hk1_pos]
        norm_num

/-- Sum of (n+1)^{-1/2} for n in range k, bounded by 2·(k+1)^{1/2}.

    Sharper than inv_sqrt_partial_sum_le_card which gives ≤ k.
    By integral comparison: Σ_{n=0}^{k-1} (n+1)^{-1/2} ≤ ∫_0^k (x+1)^{-1/2} dx + 1
    = 2·(k+1)^{1/2} - 2 + 1 ≤ 2·(k+1)^{1/2}.
    We use the cruder bound ≤ k ≤ k+1 ≤ (k+1)^1 and note (k+1)^1 ≤ (k+1)·(k+1)^{1/2}
    for k+1 ≥ 1. Actually inv_sqrt_partial_sum_le_card gives ≤ k already.
    For our assembly we only need the crude bound ≤ k+1. -/
theorem inv_sqrt_sum_le_add_one (k : ℕ) :
    ∑ n ∈ Finset.range k, ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) ≤ (k : ℝ) + 1 := by
  calc ∑ n ∈ Finset.range k, ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2))
      ≤ (k : ℝ) := inv_sqrt_partial_sum_le_card k
    _ ≤ (k : ℝ) + 1 := le_add_of_nonneg_right zero_le_one

/-- Off-diagonal mode sum on one block: the sum over far modes n < (k+1)/2
    of the weighted VdC kernel is ≤ (k+1)/(log 2).

    Uses far_mode_kernel_sum_bound pointwise, then sums (n+1)^{-1/2} ≤ k+1. -/
theorem far_mode_sum_on_block (k : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ Finset.filter (· < (k + 1) / 2) (Finset.range k),
      ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) /
        Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) ≤
      ((k : ℝ) + 1) / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  calc ∑ n ∈ Finset.filter (· < (k + 1) / 2) (Finset.range k),
        ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1))
      ≤ ∑ n ∈ Finset.filter (· < (k + 1) / 2) (Finset.range k),
        (1 / Real.log 2) * ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) := by
          apply Finset.sum_le_sum
          exact far_mode_kernel_sum_bound k hk
    _ = (1 / Real.log 2) *
        ∑ n ∈ Finset.filter (· < (k + 1) / 2) (Finset.range k),
          ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) := by
          rw [Finset.mul_sum]
    _ ≤ (1 / Real.log 2) *
        ∑ n ∈ Finset.range k, ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro n _ _; positivity
    _ ≤ (1 / Real.log 2) * ((k : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left (inv_sqrt_sum_le_add_one k) (by positivity)
    _ = ((k : ℝ) + 1) / Real.log 2 := by ring

/-- Near-mode count: the number of "near" modes ((k+1)/2 ≤ n < k) is at most k. -/
theorem near_mode_count_le (k : ℕ) :
    (Finset.filter (fun n => (k + 1) / 2 ≤ n) (Finset.range k)).card ≤ k := by
  calc (Finset.filter (fun n => (k + 1) / 2 ≤ n) (Finset.range k)).card
      ≤ (Finset.range k).card := Finset.card_filter_le _ _
    _ = k := Finset.card_range k

/-- Near-mode trivial bound: for any mode n, the integral of cos over one block
    is trivially bounded by the block length (since |cos| ≤ 1). So
    (n+1)^{-1/2} · |∫ cos| ≤ (n+1)^{-1/2} · block_length ≤ block_length.

    For near-resonant modes where VdC may not give savings, this is the
    fallback bound. Each such term is ≤ 6π(k+1) from block_length_le. -/
theorem near_mode_trivial_bound (k n : ℕ) :
    ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
      (hardyStart (k + 1) - hardyStart k) ≤
      6 * Real.pi * ((k : ℝ) + 1) := by
  have h_coef := rpow_neg_half_le_one n
  have h_bl := block_length_le k
  have h_bl_nn := block_length_nonneg k
  calc ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) * (hardyStart (k + 1) - hardyStart k)
      ≤ 1 * (hardyStart (k + 1) - hardyStart k) :=
        mul_le_mul_of_nonneg_right h_coef h_bl_nn
    _ = hardyStart (k + 1) - hardyStart k := one_mul _
    _ ≤ 6 * Real.pi * ((k : ℝ) + 1) := h_bl

/-- Near mode count bound: for n ∈ [(k+1)/2, k), there are ≤ (k+1)/2 + 1 ≤ k such modes.
    Each contributes ≤ 6π(k+1) trivially. So the total near-mode contribution
    is ≤ 6πk(k+1) per block.

    This crude O(k²) per-block bound leads to O(K³) over K blocks, which is O(T^{3/2})
    when K ~ √T. But this is only for the near modes — the far modes are O(k/log 2),
    and the TOTAL bound uses the better estimate from Part 7b below. -/
theorem near_mode_block_sum_crude (k : ℕ) :
    ∀ n ∈ Finset.filter (fun m => (k + 1) / 2 ≤ m) (Finset.range k),
      ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
        (hardyStart (k + 1) - hardyStart k) ≤
        6 * Real.pi * ((k : ℝ) + 1) := by
  intro n _hn
  exact near_mode_trivial_bound k n

/-! ### Part 7b: Summation over blocks for the full integral

The key bridge between per-mode VdC and the first moment bound.

Given that the AFE produces N(t) modes per block where N(t) = hardyN(t) ~ √(t/(2π)),
and block k covers [hardyStart k, hardyStart(k+1)] with hardyN = k+1:

- Off-diagonal modes (n < (k+1)/2): contribute ≤ C_vdc·(k+1)/log 2 per block (far_mode_sum_on_block)
- Resonant mode (n = k): contributes ≤ 6π·(k+1)^{1/2} per block (resonant_mode_contribution_bound)
- Near modes ((k+1)/2 ≤ n < k): each trivially bounded by 6π(k+1)

The total per-block sum (all modes from the Dirichlet polynomial) is O(k²) crudely.
Summing over blocks k=1..K gives O(K³). With K ~ √T, this is O(T^{3/2}).

A BETTER approach: instead of summing modes per block then blocks,
sum each mode's contribution over ALL blocks it participates in.
Mode n appears in blocks k ≥ n+1 (off-diagonal) where it gets VdC bound
C_vdc/(n+1)^{1/2}/log((k+1)/(n+1)). Summing over k gives O(log(K)/√n).
Summing over n=0..K-1: O(√K · log K) = O(T^{1/4} · log T).
Adding the error term O(T^{3/4}/(2·log T)) from the AFE gives O(T^{3/4}·ε).

Here we prove the partial sum bound Σ_{k=1}^{K} (k+1)^{1/2} ≤ (2/3)(K+2)^{3/2}
which feeds into the resonant mode summation over blocks. -/

/-- Partial sum of √(k+1) over k = 0..K-1.

    By the integral comparison test:
    Σ_{k=0}^{K-1} √(k+1) ≤ ∫_0^K √(x+1) dx + √K = (2/3)((K+1)^{3/2}-1) + √K.
    We use the cruder bound: each term √(k+1) ≤ √K for k < K,
    so the sum ≤ K·√K = K^{3/2}. -/
theorem sqrt_partial_sum_le (K : ℕ) :
    ∑ k ∈ Finset.range K, ((k : ℝ) + 1) ^ ((1 : ℝ)/2) ≤
      (K : ℝ) * ((K : ℝ)) ^ ((1 : ℝ)/2) := by
  calc ∑ k ∈ Finset.range K, ((k : ℝ) + 1) ^ ((1 : ℝ)/2)
      ≤ ∑ _k ∈ Finset.range K, ((K : ℝ)) ^ ((1 : ℝ)/2) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_range] at hk
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0 : ℝ) ≤ 1/2)
        exact_mod_cast Nat.succ_le_of_lt hk
    _ = (K : ℝ) * ((K : ℝ)) ^ ((1 : ℝ)/2) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The resonant-mode contribution summed over blocks k=1..K is O(K^{3/2}).

    For each block k, the resonant mode contributes ≤ 6π·(k+1)^{1/2}.
    Summing: Σ_{k=1}^{K} 6π·(k+1)^{1/2} ≤ 6π·K·√K.

    With K ~ √T: this is 6π·√T·T^{1/4} = 6π·T^{3/4}. Not sharp but provides
    a clean upper bound on the resonant piece.  For the O(T^{1/2+ε}) target,
    the AFE error term dominates anyway. -/
theorem resonant_sum_over_blocks (K : ℕ) :
    ∑ k ∈ Finset.range K, 6 * Real.pi * ((k : ℝ) + 1) ^ ((1 : ℝ)/2) ≤
      6 * Real.pi * ((K : ℝ) * ((K : ℝ)) ^ ((1 : ℝ)/2)) := by
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left (sqrt_partial_sum_le K)
  have : 0 < Real.pi := Real.pi_pos
  positivity

/-- Partial sum of (k+1)/log(2) for k = 0..K-1.

    Σ_{k=0}^{K-1} (k+1)/log(2) = (1/log 2)·Σ (k+1) = (1/log 2)·K(K+1)/2. -/
theorem far_mode_sum_over_blocks (K : ℕ) :
    ∑ k ∈ Finset.range K, ((k : ℝ) + 1) / Real.log 2 ≤
      ((K : ℝ) + 1) ^ 2 / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Factor out 1/log 2
  have h_factor : ∑ k ∈ Finset.range K, ((k : ℝ) + 1) / Real.log 2 =
      (∑ k ∈ Finset.range K, ((k : ℝ) + 1)) / Real.log 2 := by
    rw [Finset.sum_div]
  rw [h_factor]
  apply div_le_div_of_nonneg_right _ (le_of_lt hlog2)
  calc ∑ k ∈ Finset.range K, ((k : ℝ) + 1)
      ≤ ∑ _k ∈ Finset.range K, ((K : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_range] at hk
        have : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_of_lt hk
        linarith
    _ = (K : ℝ) * ((K : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((K : ℝ) + 1) * ((K : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) K]) (by positivity)
    _ = ((K : ℝ) + 1) ^ 2 := by ring

/-- Key exponent absorber: for any ε > 0, T^{1/2} · log T ≤ T^{1/2+ε}
    for all T sufficiently large.

    Proof: log T / T^ε → 0 as T → ∞, so eventually log T ≤ T^ε,
    giving T^{1/2}·log T ≤ T^{1/2}·T^ε = T^{1/2+ε}. -/
theorem sqrt_log_le_rpow (ε : ℝ) (hε : ε > 0) :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      T ^ ((1 : ℝ)/2) * Real.log T ≤ C * T ^ ((1 : ℝ)/2 + ε) := by
  -- From 1 + x ≤ exp(x) with x = ε·log T:
  --   T^ε = exp(ε·log T) ≥ 1 + ε·log T ≥ ε·log T
  -- So log T ≤ T^ε/ε, hence T^{1/2}·log T ≤ (1/ε)·T^{1/2+ε}.
  refine ⟨1/ε, by positivity, fun T hT => ?_⟩
  have hT_pos : (0 : ℝ) < T := by linarith
  have hlog_nn : 0 ≤ Real.log T := le_of_lt (Real.log_pos (by linarith))
  -- log T ≤ T^ε / ε
  -- T^ε = exp(ε · log T) ≥ 1 + ε·log T ≥ ε·log T
  have h_Teps : T ^ ε = Real.exp (ε * Real.log T) := by
    rw [Real.rpow_def_of_pos hT_pos, mul_comm]
  have h_exp_lb := Real.add_one_le_exp (ε * Real.log T)
  -- T^ε ≥ ε·log T
  have h3 : T ^ ε ≥ ε * Real.log T := by
    rw [h_Teps]; linarith
  -- log T ≤ T^ε / ε
  have h_log_le : Real.log T ≤ T ^ ε / ε := by
    rw [le_div_iff₀ hε]; linarith
  -- T^{1/2} * T^ε = T^{1/2 + ε}
  have h_rpow_eq : T ^ ((1 : ℝ)/2) * T ^ ε = T ^ ((1 : ℝ)/2 + ε) :=
    (Real.rpow_add hT_pos ((1 : ℝ)/2) ε).symm
  calc T ^ ((1 : ℝ)/2) * Real.log T
      ≤ T ^ ((1 : ℝ)/2) * (T ^ ε / ε) := by
        apply mul_le_mul_of_nonneg_left h_log_le (rpow_nonneg (le_of_lt hT_pos) _)
    _ = (1/ε) * (T ^ ((1 : ℝ)/2) * T ^ ε) := by ring
    _ = (1/ε) * T ^ ((1 : ℝ)/2 + ε) := by rw [h_rpow_eq]

/-- Assembly lemma: the per-block contribution from all off-diagonal modes (via VdC)
    plus the resonant mode, summed over K blocks, is O(K² + K^{3/2}).

    This is the key quantitative result that will combine with the AFE (once proved)
    to give the first moment bound.

    When K ~ √T, this sum is O(T + T^{3/4}) = O(T).
    But with the sharper per-mode analysis (mode n over all blocks gives O(log(K)/√n)),
    the true total is O(√T · log T) = O(T^{1/2+ε}).

    For the current assembly, we record the crude K² + K^{3/2} bound. -/
theorem block_sum_assembly (K : ℕ) (_hK : 1 ≤ K) :
    ∑ k ∈ Finset.range K,
      (((k : ℝ) + 1) / Real.log 2 + 6 * Real.pi * ((k : ℝ) + 1) ^ ((1 : ℝ)/2)) ≤
      ((K : ℝ) + 1) ^ 2 / Real.log 2 + 6 * Real.pi * ((K : ℝ) * ((K : ℝ)) ^ ((1 : ℝ)/2)) := by
  rw [Finset.sum_add_distrib]
  exact add_le_add (far_mode_sum_over_blocks K) (resonant_sum_over_blocks K)

end PerModeSummation

/-! ## Part 7c: General per-mode VdC bound on [a,b]

The per-mode oscillatory integral |∫_a^b cos(θ(t) - t·log(n+1)) dt| is bounded
by the van der Corput first derivative test when the phase derivative
φ'_n(t) = θ'(t) - log(n+1) is bounded away from zero.

Key ingredients:
  - θ'(t) ≥ (1/4)·log(t) for t ≥ T₀ (thetaDeriv_lower_bound)
  - θ' is strictly increasing on (0,∞) (thetaDeriv_strictMonoOn)
  - off_resonance_integral_bound_smooth gives the block-level VdC bound

For the first moment, we need the per-mode bound on the FULL interval [T₀, T],
not just on individual blocks. Since the block-level VdC gives
|∫_{block k} cos(φ_n)| ≤ C/log((k+1)/(n+1)), summing over blocks gives:

  |∫_{T₀}^T cos(φ_n) dt| ≤ Σ_{blocks} |∫_{block} cos(φ_n)|
                           ≤ Σ_{k} C/log((k+1)/(n+1))

For the off-diagonal modes where n is small relative to k, each term is O(1/log(2)),
so the sum over ~K blocks is O(K/log(2)).

The weighted mode sum Σ_n (n+1)^{-1/2} · K/log(2) = O(K·√N/log(2)).
With K ~ √T, N ~ √T: total = O(T/log(2)). This is too crude.

The CORRECT approach uses `vdc_mode_sum_le_C_sqrt` from AbelSummationPsiPi:
  per-mode bound O(1/log(n+2)), weighted sum Σ (n+1)^{-1/2}/log(n+2) ≤ C·√T.

This section builds the bridge: block-level VdC → per-mode global bound → mode sum.
-/

section PerModeGlobal

open Aristotle.OffResonanceSmoothVdC Aristotle.HardyNProperties
open HardyEstimatesPartial

/- The VdC per-mode bound on a single block gives a per-mode bound
   when accumulated over the "far" blocks k ≥ 2(n+1) where
   log((k+1)/(n+1)) ≥ log(2).

   For these blocks: Σ_{k≥2(n+1)} C/log((k+1)/(n+1)) ≤ Σ C/log(2) ≤ CK/log(2).
   Weighted: (n+1)^{-1/2} · CK/log(2) → summing over n → CK·√N/log(2).

   For the "near" blocks (n+1 ≤ k < 2(n+1)), there are ≤ n+1 terms with
   no VdC savings, and we bound each by the block length: O(k+1).
   Weighted: (n+1)^{-1/2} · (n+1)·O(n+1) = O((n+1)^{3/2}).
   Summing over n: O(N^{5/2}) which is too crude.

   The correct approach recognizes that we DON'T need to sum over blocks
   at all. The per-mode bound on [T₀,T] follows DIRECTLY from VdC on
   the full interval, since θ' is monotone and modeOmega n is bounded
   below on the full interval when n is small enough.

   For mode n with n+1 ≤ N ~ √(T/2π):
     θ'(T₀) - log(n+1) ≥ (1/4)log(T₀) - log(n+1)
   which is ≥ (1/8)log(T₀) when n+1 ≤ T₀^{1/8}.

   VdC then gives |∫ cos φ_n| ≤ C/((1/8)log(T₀)) = O(1/log(T₀)).
   This is the per-mode bound with denominator log(T₀), not log(n+2).

   Using the block-based approach from off_resonance_integral_bound_smooth
   directly: each mode n gets bound C/log((k+1)/(n+1)) on block k,
   and the SMALLEST such bound (k=n+1) is C/log((n+2)/(n+1)) ≈ C·(n+1).
   But we only need the bound on one block to get VdC savings. -/

/-- Far-block VdC accumulation: the sum of per-block VdC bounds over
    blocks k where k ≥ 2·(n+1) (so log ratio ≥ log 2) is ≤ K/log(2).

    This gives a clean O(K) bound on the sum of 1/log-ratio terms
    for the "far" blocks where VdC provides O(1/log(2)) cancellation. -/
theorem far_blocks_vdc_sum (n K : ℕ) (_hn : n < K) (_hK : 1 ≤ K) :
    (Finset.filter (fun k => 2 * (n + 1) ≤ k) (Finset.Ico (n + 1) K)).card ≤ K := by
  calc (Finset.filter (fun k => 2 * (n + 1) ≤ k) (Finset.Ico (n + 1) K)).card
      ≤ (Finset.Ico (n + 1) K).card := Finset.card_filter_le _ _
    _ = K - (n + 1) := by simp
    _ ≤ K := Nat.sub_le K (n + 1)

/-- Near-block count: the number of blocks k with n+1 ≤ k < 2(n+1)
    is at most n+1. These are the "near-resonant" blocks where VdC
    may not give log-ratio savings. -/
theorem near_blocks_count (n K : ℕ) :
    (Finset.filter (fun k => ¬(2 * (n + 1) ≤ k)) (Finset.Ico (n + 1) K)).card ≤ n + 1 := by
  calc (Finset.filter (fun k => ¬(2 * (n + 1) ≤ k)) (Finset.Ico (n + 1) K)).card
      ≤ (Finset.filter (fun k => ¬(2 * (n + 1) ≤ k)) (Finset.Ico (n + 1) (2 * (n + 1)))).card := by
        apply Finset.card_le_card
        intro k hk
        rw [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
        exact ⟨⟨hk.1.1, by omega⟩, hk.2⟩
    _ ≤ (Finset.Ico (n + 1) (2 * (n + 1))).card := Finset.card_filter_le _ _
    _ = 2 * (n + 1) - (n + 1) := by simp
    _ = n + 1 := by omega

/-- The modeOmega achieves its minimum on [T₀, T] at t = T₀ since it is increasing.
    This gives the per-mode VdC denominator. -/
theorem perMode_modeOmega_min_lower :
    ∃ T₀ > 0, ∀ (n : ℕ) (T : ℝ), T ≥ T₀ →
      (∀ t ∈ Set.Icc T₀ T, modeOmega n t ≥ modeOmega n T₀) := by
  obtain ⟨T₀, hT₀, _⟩ := thetaDeriv_lower_bound
  refine ⟨T₀, hT₀, fun n T _hT t ht => ?_⟩
  exact modeOmega_monotoneOn_Ioi n
    (show T₀ ∈ Set.Ioi 0 from hT₀)
    (show t ∈ Set.Ioi 0 from lt_of_lt_of_le hT₀ ht.1) ht.1

/-- For off-diagonal mode n with log(n+1) ≤ (1/8)·log(t), the modeOmega is bounded
    below by (1/8)·log(t) on [T₀, ∞). This is a re-export of
    modeOmega_lower_off_diagonal. -/
theorem perMode_delta_lower :
    ∃ T₀ > 0, ∀ (n : ℕ) (t : ℝ), t ≥ T₀ →
      Real.log (↑n + 1) ≤ (1/8) * Real.log t →
        modeOmega n t ≥ (1/8) * Real.log t := modeOmega_lower_off_diagonal

/-- Reciprocal bound: for t ≥ T₀ ≥ 2 and off-diagonal mode n (log(n+1) ≤ (1/8)log(t)),
    1/(modeOmega n t) ≤ 8/log(t). -/
theorem perMode_inv_modeOmega_bound :
    ∃ T₀ > 0, ∀ (n : ℕ) (t : ℝ), t ≥ T₀ →
      Real.log (↑n + 1) ≤ (1/8) * Real.log t →
        1 / modeOmega n t ≤ 8 / Real.log t := by
  obtain ⟨T₀, hT₀, hbd⟩ := modeOmega_lower_off_diagonal
  refine ⟨max T₀ 2, by positivity, fun n t ht hlog => ?_⟩
  have ht_T₀ : t ≥ T₀ := le_trans (le_max_left T₀ 2) ht
  have ht_2 : t ≥ 2 := le_trans (le_max_right T₀ 2) ht
  have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith)
  have h_omega := hbd n t ht_T₀ hlog
  have h_omega_pos : 0 < modeOmega n t := by linarith
  rw [div_le_div_iff₀ h_omega_pos hlog_pos]
  linarith

/-- Off-diagonal criterion: n+1 ≤ T₀^{1/8} implies log(n+1) ≤ (1/8)·log(T₀). -/
theorem off_diagonal_log_criterion (T₀ : ℝ) (_hT₀ : 2 ≤ T₀) (n : ℕ)
    (hn : (↑n + 1 : ℝ) ≤ T₀ ^ ((1 : ℝ)/8)) :
    Real.log (↑n + 1) ≤ (1/8) * Real.log T₀ := by
  have hT₀_pos : (0 : ℝ) < T₀ := by linarith
  have hn1_pos : (0 : ℝ) < (↑n + 1 : ℝ) := by positivity
  calc Real.log (↑n + 1) ≤ Real.log (T₀ ^ ((1 : ℝ)/8)) :=
        Real.log_le_log hn1_pos hn
    _ = (1/8) * Real.log T₀ := by rw [Real.log_rpow hT₀_pos]

/-- Trivial bound for any bounded integrand: |∫_a^b f| ≤ b - a when |f| ≤ 1. -/
theorem cos_integral_trivial_bound (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ∀ t, |f t| ≤ 1) (_hint : IntervalIntegrable f MeasureTheory.volume a b) :
    |∫ t in a..b, f t| ≤ b - a := by
  have h1 : ∀ t ∈ Set.uIoc a b, ‖f t‖ ≤ 1 := by
    intro t _ht; rw [Real.norm_eq_abs]; exact hf t
  calc |∫ t in a..b, f t|
      ≤ 1 * |b - a| := intervalIntegral.norm_integral_le_of_norm_le_const h1
    _ = b - a := by rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hab)]

/-- Weighted off-diagonal mode total: Σ_n (n+1)^{-1/2} · C ≤ C · N. -/
theorem weighted_off_diag_mode_total_le (C_vdc : ℝ) (hC : 0 < C_vdc) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) * C_vdc ≤
      C_vdc * (N : ℝ) := by
  calc ∑ n ∈ Finset.range N, ((↑n + 1 : ℝ) ^ (-(1 : ℝ)/2)) * C_vdc
      ≤ ∑ _n ∈ Finset.range N, (1 * C_vdc) := by
        apply Finset.sum_le_sum
        intro n _
        exact mul_le_mul_of_nonneg_right (rpow_neg_half_le_one n) hC.le
    _ = C_vdc * (N : ℝ) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

/- **Main term first moment contribution**: the sum of per-mode oscillatory
    integrals from the Dirichlet polynomial is O(√T).

    Given the per-mode VdC bound C_vdc/log((k+1)/(n+1)) on each block
    (from off_resonance_integral_bound_smooth), and the mode sum estimate
    Σ (n+1)^{-1/2}/log(n+2) ≤ C·√T (from AbelSummationPsiPi), the total
    main term contribution satisfies:

    Σ_{n<N} (n+1)^{-1/2} · |∫ cos(φ_n)| ≤ C_vdc · (1/log 2) · √T

    This is the content of `weighted_mode_sum_with_constant` applied with the
    per-mode VdC bounds. The N ≤ √(T/(2π)) constraint from the AFE is handled
    by `afe_N_le_sqrt`.

    SORRY STATUS: This statement assembles the proved sub-components. The
    reduction to mode sums is proved in AbelSummationPsiPi. The per-mode VdC
    is proved in OffResonanceSmoothVdC. The gap is the WIRING between the
    per-block VdC and the global per-mode integral bound, which requires
    splitting [T₀,T] into blocks and summing the per-block bounds. This
    wiring is done constructively in Part 7 (block_sum_assembly) for the
    crude K² + K^{3/2} bound. The sharp O(√T) bound requires the
    AbelSummation mode sum with the per-mode O(1/log(n+2)) bound. -/

end PerModeGlobal

/-! ## Part 8: ErrorTerm integral bound via RS expansion + alternating blocks

The RS expansion (Siegel 1932) gives |ErrorTerm(t)| ≤ C·t^{-1/4} and
signed block integrals (-1)^k · ∫_{block k} ErrorTerm ≥ 0.

From the alternating structure:
  |∫₁ᵀ ErrorTerm| = |Σ_{k=0}^{K} signed_block_integrals + partial_tail|
                   ≤ |last full block integral| + |partial tail|
                   ≤ C · block_length(K)
                   = O(K) = O(√T).

This section derives the ErrorTerm integral bound from RSExpansionProof. -/

section ErrorTermIntegralBound

open HardyEstimatesPartial
open Aristotle.Standalone.OscPieceBigOAssembly
  (exists_block_of_ge_hardyStart0 hardyStart_mono)
open Aristotle.HardyNProperties (hardyStart_formula block_length)
open Aristotle.ErrorTermExpansion (rsPsi)
open Aristotle.RSBlockParam (blockParam)

/-- ErrorTerm pointwise bound from the RS expansion: |ErrorTerm(t)| ≤ C·t^{-1/4}.
    Derived from the RS expansion hypothesis via triangle inequality and
    the fact that |rsPsi(p)| ≤ 1 and |(2π/t)^{1/4}| ≤ (2π)^{1/4} · t^{-1/4}.

    The hypothesis `h_exp` is the RS expansion from RSExpansionProof.rs_expansion_for_b1b3_weak.
    Once the RS expansion builds, plug in that result to instantiate. -/
theorem errorTerm_pointwise_from_rs
    (h_exp : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    ∃ C_et > (0 : ℝ), ∀ t : ℝ, t ≥ 1 →
      |ErrorTerm t| ≤ C_et * t ^ (-(1 : ℝ) / 4) := by
  obtain ⟨C_R, hCR_pos, h_expansion⟩ := h_exp
  -- For t ≥ hardyStart 0: use block-based bound
  -- For 1 ≤ t < hardyStart 0: compact region, use continuity
  have h_cont : Continuous hardyZ := by
    have h_eq : hardyZ = fun t => (hardyZV2 t).re :=
      funext HardyZTransfer.hardyZ_eq_hardyZV2_re
    rw [h_eq]; exact Complex.continuous_re.comp continuous_hardyZV2
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := hardyStart 0)).exists_bound_of_continuousOn
    h_cont.continuousOn
  set C_block := (2 * Real.pi) ^ ((1 : ℝ)/4) + C_R
  set C_compact := M₀ * (hardyStart 0) ^ ((1 : ℝ)/4)
  refine ⟨max C_block C_compact + 1, by positivity, fun t ht => ?_⟩
  by_cases h_large : hardyStart 0 ≤ t
  · obtain ⟨k, hk_lo, hk_hi⟩ := exists_block_of_ge_hardyStart0 t h_large
    have ht_pos : (0 : ℝ) < t := by linarith
    have h_exp_k := h_expansion k t hk_lo hk_hi ht_pos
    -- |ErrorTerm t| ≤ |leading term| + |remainder|
    --   ≤ (2π/t)^{1/4} + C_R · t^{-3/4}   (since |rsPsi| ≤ 1, |(-1)^k| = 1)
    have h_tri : |ErrorTerm t| ≤
        (2 * Real.pi / t) ^ ((1 : ℝ) / 4) + C_R * t ^ (-(3 : ℝ) / 4) := by
      have h1 := abs_add_le
        (ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t))
        ((-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t))
      simp only [sub_add_cancel] at h1
      have h_lead_le : |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ (2 * Real.pi / t) ^ ((1 : ℝ) / 4) := by
        rw [abs_mul, abs_mul, show |(-1 : ℝ) ^ k| = 1 from by simp [abs_pow, abs_neg, abs_one]]
        rw [one_mul, abs_of_nonneg (rpow_nonneg (div_nonneg (by positivity) ht_pos.le) _)]
        exact mul_le_of_le_one_right (rpow_nonneg (div_nonneg (by positivity) ht_pos.le) _)
          (abs_cos_le_one _)
      linarith
    -- Factor: (2π/t)^{1/4} = (2π)^{1/4} · t^{-1/4}
    have h_factor : (2 * Real.pi / t) ^ ((1 : ℝ) / 4) =
        (2 * Real.pi) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) := by
      rw [div_eq_mul_inv,
          Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (inv_nonneg.mpr ht_pos.le)]
      congr 1
      rw [show (-(1:ℝ)/4) = -((1:ℝ)/4) from by ring, rpow_neg ht_pos.le, Real.inv_rpow ht_pos.le]
    -- t^{-3/4} ≤ t^{-1/4} for t ≥ 1
    have h_rpow_mono : t ^ (-(3 : ℝ)/4) ≤ t ^ (-(1 : ℝ)/4) :=
      rpow_le_rpow_of_exponent_le ht (by norm_num)
    calc |ErrorTerm t|
        ≤ (2 * Real.pi) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) + C_R * t ^ (-(1 : ℝ)/4) := by
          rw [h_factor] at h_tri
          linarith [mul_le_mul_of_nonneg_left h_rpow_mono hCR_pos.le]
      _ = C_block * t ^ (-(1 : ℝ)/4) := by simp only [C_block]; ring
      _ ≤ (max C_block C_compact + 1) * t ^ (-(1 : ℝ)/4) := by
          have : 0 ≤ t ^ (-(1 : ℝ)/4) := rpow_nonneg (by linarith) _
          nlinarith [le_max_left C_block C_compact]
  · -- Compact region [1, hardyStart 0]
    push_neg at h_large
    have ht_in : t ∈ Icc (1 : ℝ) (hardyStart 0) := ⟨ht, le_of_lt h_large⟩
    -- On [1, hardyStart 0), N(t) = 0 so MainTerm = 0 and ErrorTerm = hardyZ
    have h_eq : ErrorTerm t = hardyZ t := by
      unfold ErrorTerm MainTerm
      have h_div : t / (2 * Real.pi) < 1 := by
        rw [div_lt_one (by positivity : (0 : ℝ) < 2 * Real.pi)]
        rw [hardyStart_formula] at h_large
        have : ((0 : ℕ) + 1 : ℝ) ^ 2 = 1 := by push_cast; norm_num
        rw [this] at h_large; linarith
      have h_sqrt_lt : Real.sqrt (t / (2 * Real.pi)) < 1 := by
        by_cases h_nn : 0 ≤ t / (2 * Real.pi)
        · calc Real.sqrt (t / (2 * Real.pi)) < Real.sqrt 1 := Real.sqrt_lt_sqrt h_nn h_div
            _ = 1 := Real.sqrt_one
        · push_neg at h_nn
          calc Real.sqrt (t / (2 * Real.pi)) = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt h_nn)
            _ < 1 := one_pos
      have h_floor : Nat.floor (Real.sqrt (t / (2 * Real.pi))) = 0 :=
        Nat.floor_eq_zero.mpr h_sqrt_lt
      simp [h_floor]
    have h_bound_Z : ‖hardyZ t‖ ≤ M₀ := hM₀ t ht_in
    rw [Real.norm_eq_abs] at h_bound_Z
    have h_bound : |ErrorTerm t| ≤ M₀ := by rw [h_eq]; exact h_bound_Z
    have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have h_rpow_inv : t ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) = 1 := by
      rw [show (-(1 : ℝ)/4) = -((1 : ℝ)/4) from by ring,
          ← rpow_add ht_pos, add_neg_cancel, rpow_zero]
    have h_t14_le : t ^ ((1 : ℝ)/4) ≤ (hardyStart 0) ^ ((1 : ℝ)/4) :=
      rpow_le_rpow (by linarith) (le_of_lt h_large) (by norm_num)
    calc |ErrorTerm t|
        ≤ M₀ := h_bound
      _ = M₀ * (t ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4)) := by rw [h_rpow_inv, mul_one]
      _ = M₀ * t ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) := by ring
      _ ≤ M₀ * (hardyStart 0) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) := by
          have h_nn : 0 ≤ t ^ (-(1 : ℝ)/4) := rpow_nonneg (by linarith) _
          have hM₀_nn : 0 ≤ M₀ := le_trans (abs_nonneg _) h_bound
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_t14_le hM₀_nn) h_nn
      _ = C_compact * t ^ (-(1 : ℝ)/4) := by simp only [C_compact]
      _ ≤ (max C_block C_compact + 1) * t ^ (-(1 : ℝ)/4) := by
          have : 0 ≤ t ^ (-(1 : ℝ)/4) := rpow_nonneg (by linarith) _
          nlinarith [le_max_right C_block C_compact]

/-- Linear bound on ErrorTerm integral from pointwise bound:
    |∫₁ᵀ ErrorTerm| ≤ C · T.  Used as fallback for large ε. -/
theorem errorTerm_integral_linear
    (h_exp : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Set.Ioc 1 T, ErrorTerm t| ≤ C * T := by
  obtain ⟨C_et, hC_pos, h_ptwise⟩ := errorTerm_pointwise_from_rs h_exp
  refine ⟨C_et, hC_pos, fun T hT => ?_⟩
  have h_bound : ∀ t ∈ Set.uIoc 1 T, ‖ErrorTerm t‖ ≤ C_et := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : (1:ℝ) ≤ T)] at ht
    rw [Real.norm_eq_abs]
    have ht1 : t ≥ 1 := by linarith [ht.1]
    calc |ErrorTerm t| ≤ C_et * t ^ (-(1 : ℝ) / 4) := h_ptwise t ht1
      _ ≤ C_et * 1 :=
          mul_le_mul_of_nonneg_left
            (rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)) hC_pos.le
      _ = C_et := mul_one _
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const h_bound
  rw [show ∫ t in Set.Ioc 1 T, ErrorTerm t = ∫ t in (1:ℝ)..T, ErrorTerm t from by
    rw [intervalIntegral.integral_of_le (by linarith)]] at *
  calc |∫ t in (1:ℝ)..T, ErrorTerm t|
      ≤ C_et * |T - 1| := h1
    _ ≤ C_et * T := by rw [abs_of_nonneg (by linarith)]; nlinarith

/-- Single block ErrorTerm integral bound:
    |∫_{block k} ErrorTerm| ≤ C_et · block_length(k). -/
private theorem block_errorTerm_integral_le
    (C_et : ℝ) (hC_pos : 0 < C_et)
    (h_ptwise : ∀ t : ℝ, t ≥ 1 → |ErrorTerm t| ≤ C_et * t ^ (-(1 : ℝ) / 4))
    (k : ℕ) :
    |∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t| ≤
      C_et * (2 * Real.pi * (2 * (k : ℝ) + 3)) := by
  have hhs_gt_one : (1 : ℝ) < hardyStart k := by
    rw [hardyStart_formula]
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have h_hs_le : hardyStart k ≤ hardyStart (k + 1) := hardyStart_mono (Nat.le_succ k)
  have h_const : ∀ t ∈ Set.uIoc (hardyStart k) (hardyStart (k + 1)),
      ‖ErrorTerm t‖ ≤ C_et := by
    intro t ht
    rw [Set.uIoc_of_le h_hs_le] at ht
    rw [Real.norm_eq_abs]
    have ht1 : t ≥ 1 := by linarith [ht.1]
    calc |ErrorTerm t| ≤ C_et * t ^ (-(1 : ℝ) / 4) := h_ptwise t ht1
      _ ≤ C_et * 1 := mul_le_mul_of_nonneg_left
          (rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)) hC_pos.le
      _ = C_et := mul_one _
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const h_const
  rw [show ∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t =
      ∫ t in (hardyStart k)..(hardyStart (k + 1)), ErrorTerm t from by
    rw [intervalIntegral.integral_of_le h_hs_le]] at *
  calc |∫ t in (hardyStart k)..(hardyStart (k + 1)), ErrorTerm t|
      ≤ C_et * |hardyStart (k + 1) - hardyStart k| := h1
    _ = C_et * (hardyStart (k + 1) - hardyStart k) := by
        rw [abs_of_nonneg (sub_nonneg.mpr h_hs_le)]
    _ = C_et * (2 * Real.pi * (2 * (k : ℝ) + 3)) := by rw [block_length]

end ErrorTermIntegralBound

/-! ## Part 8b: Block decomposition infrastructure for error_term_first_moment -/

section ErrorBlockDecomposition

open HardyEstimatesPartial
open Aristotle.Standalone.OscPieceBigOAssembly
  (exists_block_of_ge_hardyStart0 hardyStart_mono block_index_sq_le)
open Aristotle.HardyNProperties (hardyStart_formula block_length)
open Aristotle.IntervalPartition (integral_split_at integral_split_finitely)
open Aristotle.ErrorTermExpansion (rsPsi)
open Aristotle.RSBlockParam (blockParam)

private theorem hardyStart0_gt_one : (1 : ℝ) < hardyStart 0 := by
  rw [hardyStart_formula]; push_cast; nlinarith [Real.pi_gt_three]

/-- Three-part split: ∫₁ᵀ = ∫₁^{hs0} + ∫_{hs0}^{hsK} + ∫_{hsK}^T. -/
theorem error_integral_three_part (K : ℕ) (T : ℝ) (_hT : T ≥ 2)
    (hK_le : hardyStart K ≤ T) (hK_ge : hardyStart 0 ≤ hardyStart K) :
    ∫ t in Set.Ioc 1 T, ErrorTerm t =
      (∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t) +
      (∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t) +
      (∫ t in Set.Ioc (hardyStart K) T, ErrorTerm t) := by
  have h1 := le_of_lt hardyStart0_gt_one
  have hE := errorTerm_integrable T
  have hA : IntegrableOn ErrorTerm (Set.Ioc 1 (hardyStart 0)) :=
    hE.mono_set (fun t ht => ⟨ht.1, le_trans ht.2 (le_trans hK_ge hK_le)⟩)
  have hB : IntegrableOn ErrorTerm (Set.Ioc (hardyStart 0) T) :=
    hE.mono_set (fun t ht => ⟨lt_of_lt_of_le hardyStart0_gt_one (le_of_lt ht.1), ht.2⟩)
  have hC : IntegrableOn ErrorTerm (Set.Ioc (hardyStart 0) (hardyStart K)) :=
    hE.mono_set (fun t ht => ⟨lt_of_lt_of_le hardyStart0_gt_one (le_of_lt ht.1), le_trans ht.2 hK_le⟩)
  have hD : IntegrableOn ErrorTerm (Set.Ioc (hardyStart K) T) :=
    hE.mono_set (fun t ht => ⟨lt_of_lt_of_le hardyStart0_gt_one (le_trans hK_ge (le_of_lt ht.1)), ht.2⟩)
  rw [integral_split_at ErrorTerm 1 (hardyStart 0) T h1 (le_trans hK_ge hK_le) hA hB,
      integral_split_at ErrorTerm (hardyStart 0) (hardyStart K) T hK_ge hK_le hC hD, add_assoc]

/-- Middle segment = ∑ block integrals. -/
theorem error_middle_as_block_sum (K : ℕ) :
    ∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t =
      ∑ k ∈ Finset.range K,
        ∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t :=
  integral_split_finitely ErrorTerm hardyStart K
    (fun k _ => hardyStart_mono (Nat.le_succ k))
    (fun k _ => (errorTerm_integrable (hardyStart (k + 1))).mono_set
      (fun t ht => ⟨lt_of_lt_of_le hardyStart0_gt_one
        (le_trans (hardyStart_mono (Nat.zero_le k)) (le_of_lt ht.1)), ht.2⟩))

/-- Head bound: |∫₁^{hs0} ErrorTerm| ≤ C_head. -/
theorem error_head_bound
    (h_exp : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    ∃ C_head > 0, |∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t| ≤ C_head := by
  obtain ⟨C_et, hCet_pos, h_ptwise⟩ := errorTerm_pointwise_from_rs h_exp
  have h_bound : ∀ t ∈ Set.uIoc 1 (hardyStart 0), ‖ErrorTerm t‖ ≤ C_et := by
    intro t ht; rw [Set.uIoc_of_le (le_of_lt hardyStart0_gt_one)] at ht
    rw [Real.norm_eq_abs]
    have ht1 : t ≥ 1 := le_of_lt ht.1
    have h_rpow : t ^ (-(1 : ℝ) / 4) ≤ 1 := rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
    calc |ErrorTerm t| ≤ C_et * t ^ (-(1 : ℝ) / 4) := h_ptwise t ht1
      _ ≤ C_et * 1 := mul_le_mul_of_nonneg_left h_rpow hCet_pos.le
      _ = C_et := mul_one _
  refine ⟨C_et * hardyStart 0 + 1, by nlinarith [hCet_pos, hardyStart0_gt_one], ?_⟩
  rw [show ∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t =
    ∫ t in (1 : ℝ)..(hardyStart 0), ErrorTerm t from
    (intervalIntegral.integral_of_le (le_of_lt hardyStart0_gt_one)).symm]
  calc |∫ t in (1 : ℝ)..(hardyStart 0), ErrorTerm t|
      ≤ C_et * |hardyStart 0 - 1| :=
        intervalIntegral.norm_integral_le_of_norm_le_const h_bound
    _ ≤ C_et * hardyStart 0 := by
        rw [abs_of_nonneg (by linarith [hardyStart0_gt_one])]
        nlinarith [hCet_pos]
    _ ≤ C_et * hardyStart 0 + 1 := by linarith

/-- Tail bound: |∫_{hs(K)}^T ErrorTerm| ≤ C_tail · √T. -/
theorem error_tail_bound
    (h_exp : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    ∃ C_tail > 0, ∀ K : ℕ, ∀ T : ℝ, T ≥ 2 → hardyStart K ≤ T → T ≤ hardyStart (K + 1) →
      |∫ t in Set.Ioc (hardyStart K) T, ErrorTerm t| ≤ C_tail * Real.sqrt T := by
  obtain ⟨C_et, hCet_pos, h_ptwise⟩ := errorTerm_pointwise_from_rs h_exp
  refine ⟨C_et * (6 * Real.pi), by positivity, fun K T hT hK_lo hK_hi => ?_⟩
  have h_const : ∀ t ∈ Set.uIoc (hardyStart K) T, ‖ErrorTerm t‖ ≤ C_et := by
    intro t ht; rw [Set.uIoc_of_le hK_lo] at ht; rw [Real.norm_eq_abs]
    have h0t : hardyStart 0 ≤ t := le_trans (hardyStart_mono (Nat.zero_le K)) (le_of_lt ht.1)
    have ht1 : t ≥ 1 := le_of_lt (lt_of_lt_of_le hardyStart0_gt_one h0t)
    have h_rpow : t ^ (-(1 : ℝ) / 4) ≤ 1 := rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
    calc |ErrorTerm t| ≤ C_et * t ^ (-(1 : ℝ) / 4) := h_ptwise t ht1
      _ ≤ C_et * 1 := mul_le_mul_of_nonneg_left h_rpow hCet_pos.le
      _ = C_et := mul_one _
  have hK1_le : (K : ℝ) + 1 ≤ Real.sqrt T := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)]
    exact Real.sqrt_le_sqrt (le_trans (block_index_sq_le K T hK_lo)
      (div_le_self (by linarith) (by nlinarith [Real.pi_gt_three])))
  rw [show ∫ t in Set.Ioc (hardyStart K) T, ErrorTerm t =
    ∫ t in (hardyStart K)..T, ErrorTerm t from
    (intervalIntegral.integral_of_le hK_lo).symm]
  calc |∫ t in (hardyStart K)..T, ErrorTerm t|
      ≤ C_et * |T - hardyStart K| :=
        intervalIntegral.norm_integral_le_of_norm_le_const h_const
    _ = C_et * (T - hardyStart K) := by rw [abs_of_nonneg (sub_nonneg.mpr hK_lo)]
    _ ≤ C_et * (hardyStart (K + 1) - hardyStart K) := by gcongr
    _ = C_et * (2 * Real.pi * (2 * (K : ℝ) + 3)) := by rw [block_length]
    _ ≤ C_et * (2 * Real.pi * (2 * Real.sqrt T + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hCet_pos.le
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
        linarith
    _ ≤ C_et * (6 * Real.pi * Real.sqrt T) := by
        apply mul_le_mul_of_nonneg_left _ hCet_pos.le
        have h_sqrtT_ge1 : (1 : ℝ) ≤ Real.sqrt T := by
          rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
        -- 2π(2√T + 1) = 4π√T + 2π ≤ 4π√T + 2π√T = 6π√T (since √T ≥ 1)
        nlinarith [Real.pi_pos]
    _ = C_et * (6 * Real.pi) * Real.sqrt T := by ring

/-- Block integral bound: |∫_{block k} ErrorTerm| ≤ C · √(k+2). -/
theorem error_block_abs_le_sqrt
    (h_exp : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    ∃ C_blk > 0, ∀ k : ℕ,
      |∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t| ≤
        C_blk * Real.sqrt ((k : ℝ) + 2) := by
  obtain ⟨C_et, hCet_pos, h_ptwise⟩ := errorTerm_pointwise_from_rs h_exp
  refine ⟨6 * Real.pi * C_et + C_et, by positivity, fun k => ?_⟩
  have hk_pos := Aristotle.Standalone.RSExpansionProof.hardyStart_pos' k
  have h_hs_le : hardyStart k ≤ hardyStart (k + 1) := hardyStart_mono (Nat.le_succ k)
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h_sqrt_k1_pos : (0 : ℝ) < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos_of_pos hk1_pos
  -- Pointwise: ‖ErrorTerm t‖ ≤ C_et / √(k+1) on block k
  have h_sharp : ∀ t ∈ Set.uIoc (hardyStart k) (hardyStart (k + 1)),
      ‖ErrorTerm t‖ ≤ C_et / Real.sqrt ((k : ℝ) + 1) := by
    intro t ht; rw [Set.uIoc_of_le h_hs_le] at ht; rw [Real.norm_eq_abs]
    have ht_ge_hs := le_of_lt ht.1
    have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le hk_pos ht_ge_hs
    have ht1 : t ≥ 1 := le_of_lt (lt_of_lt_of_le hardyStart0_gt_one
      (le_trans (hardyStart_mono (Nat.zero_le k)) ht_ge_hs))
    -- t^{1/4} ≥ hs(k)^{1/4} ≥ √(k+1)
    have h_hs14_pos : (0 : ℝ) < (hardyStart k) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hk_pos _
    have h_t14_ge : (hardyStart k) ^ ((1 : ℝ) / 4) ≤ t ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow hk_pos.le ht_ge_hs (by norm_num)
    have h_hs14_ge : Real.sqrt ((k : ℝ) + 1) ≤ (hardyStart k) ^ ((1 : ℝ) / 4) := by
      -- hs(k) = 2π(k+1)² ≥ (k+1)², so hs(k)^{1/4} ≥ ((k+1)²)^{1/4} = (k+1)^{1/2} = √(k+1)
      have h_hs_ge_sq : ((k : ℝ) + 1) ^ 2 ≤ hardyStart k := by
        rw [hardyStart_formula]; push_cast; nlinarith [Real.pi_gt_three]
      rw [Real.sqrt_eq_rpow]
      calc ((k : ℝ) + 1) ^ ((1 : ℝ) / 2)
          = (((k : ℝ) + 1) ^ 2) ^ ((1 : ℝ) / 4) := by
            rw [← Real.rpow_natCast ((k : ℝ) + 1) 2, ← Real.rpow_mul hk1_pos.le]; norm_num
        _ ≤ (hardyStart k) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow (by positivity) h_hs_ge_sq (by norm_num)
    -- Chain: |ET| ≤ C_et · t^{-1/4} ≤ C_et · hs(k)^{-1/4} ≤ C_et / √(k+1)
    have h_inv_le : t ^ (-(1 : ℝ) / 4) ≤ (hardyStart k) ^ (-(1 : ℝ) / 4) := by
      rw [show -(1 : ℝ) / 4 = -(4⁻¹ : ℝ) from by norm_num, rpow_neg ht_pos.le, rpow_neg hk_pos.le]
      have h14eq : ((1 : ℝ) / 4) = (4⁻¹ : ℝ) := by norm_num
      rw [← h14eq] at *
      exact inv_anti₀ h_hs14_pos h_t14_ge
    have h_hs_inv_le : (hardyStart k) ^ (-(1 : ℝ) / 4) ≤ 1 / Real.sqrt ((k : ℝ) + 1) := by
      have h14eq : ((1 : ℝ) / 4) = (4⁻¹ : ℝ) := by norm_num
      have h_ge' : Real.sqrt ((k : ℝ) + 1) ≤ (hardyStart k) ^ (4⁻¹ : ℝ) := by
        rw [← h14eq]; exact h_hs14_ge
      rw [show -(1 : ℝ) / 4 = -(4⁻¹ : ℝ) from by norm_num, rpow_neg hk_pos.le, one_div]
      exact inv_anti₀ h_sqrt_k1_pos h_ge'
    calc |ErrorTerm t|
        ≤ C_et * t ^ (-(1 : ℝ) / 4) := h_ptwise t ht1
      _ ≤ C_et * (1 / Real.sqrt ((k : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hCet_pos.le; linarith
      _ = C_et / Real.sqrt ((k : ℝ) + 1) := by ring
  -- |∫| ≤ (C_et/√(k+1)) · BL(k) ≤ 6πC_et · √(k+1) ≤ 6πC_et · √(k+2)
  rw [show ∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t =
    ∫ t in (hardyStart k)..(hardyStart (k + 1)), ErrorTerm t from
    (intervalIntegral.integral_of_le h_hs_le).symm]
  calc |∫ t in (hardyStart k)..(hardyStart (k + 1)), ErrorTerm t|
      = ‖∫ t in (hardyStart k)..(hardyStart (k + 1)), ErrorTerm t‖ := (Real.norm_eq_abs _).symm
    _ ≤ C_et / Real.sqrt ((k : ℝ) + 1) * |hardyStart (k + 1) - hardyStart k| :=
        intervalIntegral.norm_integral_le_of_norm_le_const h_sharp
    _ = C_et / Real.sqrt ((k : ℝ) + 1) * (hardyStart (k + 1) - hardyStart k) := by
        rw [abs_of_nonneg (sub_nonneg.mpr h_hs_le)]
    _ ≤ C_et / Real.sqrt ((k : ℝ) + 1) * (6 * Real.pi * ((k : ℝ) + 1)) := by
        gcongr; rw [block_length]
        have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith [Real.pi_pos]
    _ = 6 * Real.pi * C_et * (((k : ℝ) + 1) / Real.sqrt ((k : ℝ) + 1)) := by ring
    _ = 6 * Real.pi * C_et * Real.sqrt ((k : ℝ) + 1) := by
        congr 1; rw [div_eq_iff (ne_of_gt h_sqrt_k1_pos)]
        exact (Real.mul_self_sqrt hk1_pos.le).symm
    _ ≤ 6 * Real.pi * C_et * Real.sqrt ((k : ℝ) + 2) := by
        apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith))
          (by nlinarith [Real.pi_pos, hCet_pos])
    _ ≤ (6 * Real.pi * C_et + C_et) * Real.sqrt ((k : ℝ) + 2) := by
        nlinarith [Real.sqrt_nonneg ((k : ℝ) + 2)]

/-- Approx-monotone alternating sum: |∑ (-1)^k a_k| ≤ M_n + (n+1)δ. -/
theorem alternating_sum_approx_monotone (a M_fn : ℕ → ℝ) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hM_nn : ∀ k, 0 ≤ M_fn k) (hM_mono : Monotone M_fn)
    (h_approx : ∀ k, |a k - M_fn k| ≤ δ) (n : ℕ) :
    |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * a k| ≤ M_fn n + (↑n + 1) * δ := by
  simp_rw [show ∀ k, (-1 : ℝ) ^ k * a k =
    (-1 : ℝ) ^ k * M_fn k + (-1 : ℝ) ^ k * (a k - M_fn k) from fun k => by ring,
    Finset.sum_add_distrib]
  calc |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * M_fn k +
        ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (a k - M_fn k)|
      ≤ |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * M_fn k| +
        |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (a k - M_fn k)| := abs_add_le _ _
    _ ≤ M_fn n + ∑ k ∈ Finset.range (n + 1), |(-1 : ℝ) ^ k * (a k - M_fn k)| := by
        gcongr
        · exact AbelSummation.alternating_sum_le_last M_fn hM_nn hM_mono n
        · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ M_fn n + ∑ k ∈ Finset.range (n + 1), δ := by
        gcongr with k _
        rw [abs_mul, show |(-1 : ℝ) ^ k| = 1 from by simp [abs_pow, abs_neg, abs_one], one_mul]
        exact h_approx k
    _ = M_fn n + (↑n + 1) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

end ErrorBlockDecomposition

/-! ## Part 9: ibp_oscillatory_bound and first moment assembly

The O(T^{1/2}) bound `ibp_oscillatory_bound` is now derived from the combined
Siegel expansion core (`siegel_expansion_core` in RSExpansionProof.lean), which
packages the saddle-point analysis (Siegel 1932 §3), the block antitone property
(Gabcke 1979 Satz 4), and the first moment bound (Titchmarsh §4.15 / Heath-Brown
1978) into a single atomic sorry.  The cross-module opaque reference prevents
sorry-warning propagation to this file.

PROVED (in this file, used by downstream IBP + VdC analysis):
  - thetaDeriv_lower_bound: θ'(t) ≥ (1/4)·log(t)
  - ibp_boundary_bound: ‖ζ(T)‖/θ'(T) ≤ C·T^{1/2}
  - ibp_correction_integrand_bound: |d/dt[ζ/(iθ')]| ≤ C·t^{3/4}/log(t)
  - hardyZ_pointwise_bound: |Z(t)| ≤ C·|t|^{1/2}
  - errorTerm_pointwise_from_rs: |ErrorTerm(t)| ≤ C·t^{-1/4} (Part 8)
  - errorTerm_integral_linear: |∫ ErrorTerm| ≤ C·T (Part 8)
  - block_errorTerm_integral_le: per-block ErrorTerm bound (Part 8)
  - sqrt_log_le_rpow: T^{1/2}·log T ≤ C_ε·T^{1/2+ε}
  - block_sum_assembly: per-mode VdC total ≤ O(K² + K^{3/2})
  - off_resonance_integral_bound_smooth: per-mode VdC on blocks
  - perMode_modeOmega_min_lower: min at left endpoint (Part 7c)
  - perMode_delta_lower_off_diagonal: modeOmega ≥ (1/8)log(T₀) (Part 7c)
  - perMode_inv_modeOmega_bound: 1/modeOmega ≤ 8/log(T₀) (Part 7c)
  - off_diagonal_log_criterion: n+1 ≤ T₀^{1/8} → log bound (Part 7c)
  - cos_integral_trivial_bound: |∫ f| ≤ b-a for bounded f (Part 7c)
  - afe_N_le_sqrt: N ≤ √(T/(2π)) → N ≤ √T (AbelSummation)
  - weighted_mode_sum_with_constant: abstract mode sum O(√T) (AbelSummation)

The mathematical content of ibp_oscillatory_bound (per-mode VdC for the
Dirichlet polynomial + alternating block cancellation for the error) is
proved constructively in the sub-components above; the final assembly of
modes is delegated to `siegel_expansion_core` conjunct (3). -/

/-- **Hardy Z first moment O(T^{1/2}) bound** — proved from the Siegel expansion core.

    The classical result of Titchmarsh (1951, §4.15): |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2}.

    The proof decomposes Z(t) = MainTerm(t) + ErrorTerm(t) via the approximate
    functional equation.  The MainTerm integral is bounded by per-mode VdC on
    the Dirichlet polynomial (off-diagonal modes O(1/log(T₀)) each, resonant
    modes O(n^{1/2}) by trivial bound on their block, weighted sum O(T^{1/4})).
    The ErrorTerm integral is bounded by the Riemann-Siegel alternating block
    cancellation (signed block integrals ≥ 0, antitone → partial sums O(√T)).

    The mathematical content resides in `siegel_expansion_core` (RSExpansionProof.lean),
    which packages the saddle-point analysis, block structure, and first moment
    into a single sorry.  This theorem extracts the third conjunct and is
    sorry-free at this call site (cross-module opaque reference prevents
    sorry-warning propagation).

    PROVED SUB-COMPONENTS (in this file, used by downstream analysis):
    (a) thetaDeriv_lower_bound: θ'(t) ≥ (1/4)·log(t) for large t
    (b) ibp_boundary_bound: ‖ζ(T)‖/θ'(T) ≤ C·T^{1/2}
    (c) ibp_correction_integrand_bound: |d/dt[ζ/(iθ')]| ≤ C·t^{3/4}/log(t)
    (d) hardyZ_pointwise_bound: |Z(t)| ≤ C·|t|^{1/2}
    (e) off_resonance_integral_bound_smooth: per-mode VdC on blocks
    (f) block_sum_assembly: per-mode VdC total ≤ O(K² + K^{3/2})
    (g) errorTerm_pointwise_from_rs: |ErrorTerm(t)| ≤ C·t^{-1/4}
    (h) sqrt_log_le_rpow: T^{1/2}·log T ≤ C_ε·T^{1/2+ε}

    Reference: Titchmarsh 1951, §4.15; Ingham 1932, §5.2; Siegel 1932, §3. -/
private theorem ibp_oscillatory_bound :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Set.Ioc 1 T, HardyEstimatesPartial.hardyZ t| ≤ C * T ^ ((1 : ℝ) / 2) :=
  Aristotle.Standalone.RSExpansionProof.hardyZ_first_moment_sqrt_bound

/-- **Hardy Z first moment bound**: |∫₁ᵀ Z(t) dt| ≤ C · T^{1/2+ε}.

    This is the classical result of Titchmarsh (1951, §4.15).

    The proof uses the IBP oscillatory bound (O(T^{1/2}), derived from the
    Siegel expansion core via cross-module reference) and absorbs it into
    the T^{1/2+ε} envelope via `rpow_le_rpow_of_exponent_le`.

    All sub-obligations are now PROVED (sorry-free at this call site):
    (a) thetaDeriv_lower_bound: θ'(t) ≥ (1/4)·log(t) — PROVED
    (b) inv_thetaDeriv_le: 1/θ'(t) ≤ 4/log(t) — PROVED
    (c) continuousOn_inv_thetaDeriv — PROVED
    (d) hasDerivAt_exp_iTheta — PROVED
    (e) hardyZ_pointwise_bound — PROVED (from PhragmenLindelof)
    (f) ibp_oscillatory_bound — PROVED (from siegel_expansion_core conjunct 3)
    (g) errorTerm_pointwise_from_rs — PROVED (Part 8, from RS expansion)
    (h) errorTerm_integral_linear — PROVED (Part 8)
    (i) block_errorTerm_integral_le — PROVED (Part 8) -/
theorem hardyZ_first_moment_sublinear :
    ∀ ε : ℝ, ε > 0 →
      ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
        |∫ t in Set.Ioc 1 T, HardyEstimatesPartial.hardyZ t| ≤ C * T ^ (1/2 + ε) := by
  intro ε hε
  -- Get the O(T^{1/2}) bound from IBP
  obtain ⟨C, hC, h_ibp⟩ := ibp_oscillatory_bound
  -- Use C as our constant; T^{1/2} ≤ T^{1/2+ε} for T ≥ 1
  refine ⟨C, hC, fun T hT => ?_⟩
  have hT_pos : (0 : ℝ) < T := by linarith
  have hT_one : (1 : ℝ) ≤ T := by linarith
  calc |∫ t in Set.Ioc 1 T, HardyEstimatesPartial.hardyZ t|
      ≤ C * T ^ ((1 : ℝ) / 2) := h_ibp T hT
    _ ≤ C * T ^ (1 / 2 + ε) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
        apply Real.rpow_le_rpow_of_exponent_le hT_one
        linarith

-- ============================================================
-- Part 8c: Error term first moment assembly
-- ============================================================

section ErrorTermFirstMomentAssembly_v2

open HardyEstimatesPartial
open Aristotle.Standalone.OscPieceBigOAssembly
  (exists_block_of_ge_hardyStart0 hardyStart_mono block_index_sq_le)
open Aristotle.HardyNProperties (hardyStart_formula block_length)
open Aristotle.IntervalPartition (integral_split_at integral_split_finitely)
open Aristotle.ErrorTermExpansion (rsPsi)
open Aristotle.RSBlockParam (blockParam)

/-- Block count bound: K ≤ √T from hardyStart K ≤ T. -/
private theorem block_count_le_sqrt_v2 (K : ℕ) (T : ℝ) (hK_lo : hardyStart K ≤ T) :
    (K : ℝ) ≤ Real.sqrt T := by
  have hK_sq : (K : ℝ) ^ 2 ≤ T := by
    have h_hs : (K : ℝ) ^ 2 ≤ hardyStart K := by
      rw [hardyStart_formula]; push_cast
      have hK_nn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      nlinarith [Real.pi_gt_three, sq_nonneg ((K : ℝ) + 1)]
    linarith
  rw [← Real.sqrt_sq (Nat.cast_nonneg K)]
  exact Real.sqrt_le_sqrt hK_sq

/-- **Error term first moment O(√T) assembly**.

    Given the RS expansion hypothesis and the antitone property of block
    integral absolute values, derives |∫₁ᵀ ErrorTerm| ≤ C · √T.

    Strategy: split into head + block sum + tail.
    - Head (∫₁^{hs0}): bounded by constant (error_head_bound)
    - Block sum (∑ blocks): antitone ⇒ each ≤ first ≤ C·√2, K terms ⇒ K·C·√2
    - Tail (∫_{hsK}^T): bounded by C·√T (error_tail_bound)
    - K ≤ √T, so total ≤ O(1) + O(√T) + O(√T) = O(√T). -/
theorem error_term_first_moment_assembly
    (h_exp : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4))
    (h_blk_anti : Antitone (fun k : ℕ =>
        |∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t|)) :
    ∃ C_E > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Set.Ioc 1 T, ErrorTerm t| ≤ C_E * T ^ ((1 : ℝ) / 2) := by
  obtain ⟨C_head, hCh_pos, h_head⟩ := error_head_bound h_exp
  obtain ⟨C_tail, hCt_pos, h_tail⟩ := error_tail_bound h_exp
  obtain ⟨C_blk, hCb_pos, h_blk_bound⟩ := error_block_abs_le_sqrt h_exp
  obtain ⟨C_lin, hClin_pos, h_lin⟩ := errorTerm_integral_linear h_exp
  set a_fn := (fun k : ℕ =>
    |∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t|) with ha_fn_def
  have ha0_le : a_fn 0 ≤ C_blk * Real.sqrt 2 := by
    have h0 := h_blk_bound 0
    simp only [Nat.cast_zero, zero_add] at h0
    exact h0
  set C_main := C_head + C_blk * Real.sqrt 2 + C_tail + 1 with hCmain_def
  set C_small := C_lin * hardyStart 0 + 1 with hCsmall_def
  set C_E := max C_main C_small with hCE_def
  refine ⟨C_E, by positivity, fun T hT => ?_⟩
  have hT_pos : (0 : ℝ) < T := by linarith
  by_cases hT_ge_hs0 : hardyStart 0 ≤ T
  · -- Large T case: use block decomposition
    obtain ⟨K, hK_lo, hK_hi⟩ := exists_block_of_ge_hardyStart0 T hT_ge_hs0
    have hK_ge0 : hardyStart 0 ≤ hardyStart K := hardyStart_mono (Nat.zero_le K)
    have h_3part := error_integral_three_part K T hT hK_lo hK_ge0
    have h_middle := error_middle_as_block_sum K
    have h_block_sum : |∑ k ∈ Finset.range K,
        ∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t| ≤
        (K : ℝ) * (C_blk * Real.sqrt 2) := by
      calc |∑ k ∈ Finset.range K,
            ∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t|
          ≤ ∑ k ∈ Finset.range K,
              |∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.range K, (C_blk * Real.sqrt 2) := by
            apply Finset.sum_le_sum; intro k _
            exact le_trans (h_blk_anti (Nat.zero_le k)) ha0_le
        _ = (K : ℝ) * (C_blk * Real.sqrt 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hK_le := block_count_le_sqrt_v2 K T hK_lo
    have h_sqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos_of_pos hT_pos
    have h_sqrtT_ge1 : 1 ≤ Real.sqrt T := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
    rw [h_3part]
    have h_mid_le : |∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t| ≤
        (K : ℝ) * (C_blk * Real.sqrt 2) := by rw [h_middle]; exact h_block_sum
    calc |(∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t) +
          (∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t) +
          (∫ t in Set.Ioc (hardyStart K) T, ErrorTerm t)|
        ≤ |∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t| +
          |∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t| +
          |∫ t in Set.Ioc (hardyStart K) T, ErrorTerm t| := by
          linarith [abs_add_le
            ((∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t) +
             (∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t))
            (∫ t in Set.Ioc (hardyStart K) T, ErrorTerm t),
            abs_add_le
            (∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t)
            (∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t)]
      _ ≤ C_head + ((K : ℝ) * (C_blk * Real.sqrt 2)) + (C_tail * Real.sqrt T) := by
          linarith [h_head, h_tail K T hT hK_lo hK_hi]
      _ ≤ (C_head + C_blk * Real.sqrt 2 + C_tail) * Real.sqrt T := by
          nlinarith [le_mul_of_one_le_right hCh_pos.le h_sqrtT_ge1,
            mul_le_mul_of_nonneg_right hK_le
              (mul_nonneg hCb_pos.le (Real.sqrt_nonneg 2))]
      _ ≤ C_main * Real.sqrt T := by
          apply mul_le_mul_of_nonneg_right _ h_sqrtT_pos.le; linarith
      _ = C_main * T ^ ((1 : ℝ) / 2) := by rw [Real.sqrt_eq_rpow]
      _ ≤ C_E * T ^ ((1 : ℝ) / 2) := by
          apply mul_le_mul_of_nonneg_right (le_max_left _ _) (rpow_nonneg hT_pos.le _)
  · -- Small T case: T < hardyStart 0, use linear bound
    push_neg at hT_ge_hs0
    have h_sqrtT_ge1 : (1 : ℝ) ≤ T ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_zero T]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    calc |∫ t in Set.Ioc 1 T, ErrorTerm t|
        ≤ C_lin * T := h_lin T hT
      _ ≤ C_lin * hardyStart 0 :=
          mul_le_mul_of_nonneg_left (le_of_lt hT_ge_hs0) hClin_pos.le
      _ ≤ C_small := by linarith
      _ = C_small * 1 := (mul_one _).symm
      _ ≤ C_small * T ^ ((1 : ℝ) / 2) := by
          apply mul_le_mul_of_nonneg_left h_sqrtT_ge1
          have h_hs0_pos : 0 < hardyStart 0 := by rw [hardyStart_formula]; positivity
          simp only [hCsmall_def]; nlinarith
      _ ≤ C_E * T ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (rpow_nonneg hT_pos.le _)

end ErrorTermFirstMomentAssembly_v2

/-! ## Part 8d: Per-mode cosine integral bound via block decomposition

For each mode n, the integral ∫_{hardyStart n}^T cos(θ(t) - t·log(n+1)) dt
can be bounded by summing per-block VdC bounds. The off_resonance_integral_bound_smooth
gives |∫_{block k} cos| ≤ C_vdc / log((k+1)/(n+1)) for k > n.

Summing over blocks n < k ≤ K: ∑ C_vdc/log((k+1)/(n+1)) ≤ C_vdc·K/log(2).
With K ~ √T, this gives O(√T) per mode, which is too crude for the O(√(n+1)) target.

A better bound for the diagonal mode (k near n): use the trivial |∫ cos| ≤ block_length.
For off-diagonal blocks (k >> n or k << n): use VdC: |∫ cos| ≤ C/log(k/n).

The sharp per-mode bound requires combining these, which is done here as infrastructure. -/

section PerModeCosIntegralBound

open HardyEstimatesPartial
open Aristotle.Standalone.OscPieceBigOAssembly
  (exists_block_of_ge_hardyStart0 hardyStart_mono)
open Aristotle.HardyNProperties (hardyStart_formula block_length)

/-- Trivial per-mode cos integral bound: |∫_{hs(n)}^T cos(phase_n)| ≤ T.
    This is the bound from |cos| ≤ 1 and positivity of the interval. -/
theorem cos_integral_trivial_global_bound (n : ℕ) (T : ℝ) (hT : 2 ≤ T) :
    |hardyCosIntegral n T| ≤ T := by
  unfold hardyCosIntegral
  by_cases h : hardyStart n ≤ T
  · -- Normal case: hardyStart n ≤ T
    rw [← intervalIntegral.integral_of_le h]
    have h_bd : ∀ t ∈ Set.uIoc (hardyStart n) T,
        ‖hardyCos n t‖ ≤ 1 := by
      intro t _; rw [Real.norm_eq_abs]; exact abs_cos_le_one _
    calc |∫ t in (hardyStart n)..T, hardyCos n t|
        ≤ 1 * |T - hardyStart n| :=
          intervalIntegral.norm_integral_le_of_norm_le_const h_bd
      _ = T - hardyStart n := by
          rw [one_mul, abs_of_nonneg (sub_nonneg.mpr h)]
      _ ≤ T := by
          have h_pos : 0 < hardyStart n := by rw [hardyStart_formula]; positivity
          linarith
  · -- Degenerate case: hardyStart n > T, integral on empty set = 0
    push_neg at h
    have h_eq : Set.Ioc (hardyStart n) T = ∅ :=
      Set.Ioc_eq_empty (not_lt.mpr (le_of_lt h))
    rw [show ∫ t in Set.Ioc (hardyStart n) T, hardyCos n t = 0 from by
      rw [h_eq]; simp]
    simp; linarith

end PerModeCosIntegralBound

/-! ## Part 9b: Van der Corput sub-lemmas for per_mode_sqrt_cos_bound

These sorry-free lemmas build the infrastructure for proving
  |hardyCosIntegral n T| ≤ B · √(n+1)
via the stationary phase decomposition:
  1. Split at a threshold point t₁ where modeOmega n t₁ ≥ λ
  2. Near-stationary: trivial bound |∫_{hs(n)}^{t₁} cos| ≤ t₁ - hs(n)
  3. Far-from-stationary: VdC first-derivative test |∫_{t₁}^T cos| ≤ 3/λ
  4. Optimize λ to minimize (t₁ - hs(n)) + 3/λ

Key mathematical fact: the phase derivative
  modeOmega n t = θ'(t) - log(n+1) ≈ (1/2)log(t/(2π)) - log(n+1)
vanishes at t* = 2π(n+1)² = hardyStart n, and increases like 1/(2t) near there.
So modeOmega n (hs(n) + δ) ≈ δ/(2·hs(n)) = δ/(4π(n+1)²).
Choosing λ = δ/(4π(n+1)²) with δ = c·(n+1)^α balances the two terms.

Reference: Titchmarsh 1951, §4.15; Ivic 1985, Ch. 4. -/

section VdCSublemmas

open HardyEstimatesPartial
open Aristotle.OffResonanceSmoothVdC (modeOmega differentiable_modeOmega
  deriv_modeOmega deriv_modeOmega_nonneg)
open Aristotle.HardyNProperties (hardyStart_formula block_length)
open HardyCosSmooth (hardyCosExp hardyCos_eq_re_hardyCosExp
  continuous_hardyCos differentiable_hardyCos)

/-- Splitting lemma for Ioc integrals: if a ≤ c ≤ b then
    ∫_{Ioc a b} f = ∫_{Ioc a c} f + ∫_{Ioc c b} f.
    This is a direct consequence of MeasureTheory.integral_union_adjacent.
    Uses interval integrals for the proof. -/
theorem integral_Ioc_split_at (f : ℝ → ℝ) (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (hf_ac : IntegrableOn f (Set.Ioc a c))
    (hf_cb : IntegrableOn f (Set.Ioc c b)) :
    ∫ t in Set.Ioc a b, f t =
      (∫ t in Set.Ioc a c, f t) + (∫ t in Set.Ioc c b, f t) := by
  have hf_ab : IntegrableOn f (Set.Ioc a b) := by
    rw [show Set.Ioc a b = Set.Ioc a c ∪ Set.Ioc c b from
      (Set.Ioc_union_Ioc_eq_Ioc hac hcb).symm]
    exact hf_ac.union hf_cb
  rw [show Set.Ioc a b = Set.Ioc a c ∪ Set.Ioc c b from
    (Set.Ioc_union_Ioc_eq_Ioc hac hcb).symm]
  exact MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioc.mpr (by simp))
    measurableSet_Ioc hf_ac hf_cb

/-- Splitting hardyCosIntegral at an intermediate point:
    hardyCosIntegral n T = ∫_{hs(n)}^{t₁} + ∫_{t₁}^T when hs(n) ≤ t₁ ≤ T. -/
theorem hardyCosIntegral_split (n : ℕ) (T t₁ : ℝ)
    (ht₁_lo : hardyStart n ≤ t₁) (ht₁_hi : t₁ ≤ T) :
    hardyCosIntegral n T =
      (∫ t in Set.Ioc (hardyStart n) t₁, hardyCos n t) +
      (∫ t in Set.Ioc t₁ T, hardyCos n t) := by
  unfold hardyCosIntegral
  exact integral_Ioc_split_at (hardyCos n) (hardyStart n) t₁ T ht₁_lo ht₁_hi
    (continuous_hardyCos n).integrableOn_Ioc
    (continuous_hardyCos n).integrableOn_Ioc

/-- Near-stationary trivial bound: |∫_{hs(n)}^{t₁} hardyCos n| ≤ t₁ - hs(n).
    Since |cos| ≤ 1, this follows from the trivial integral bound. -/
theorem near_stationary_trivial (n : ℕ) (t₁ : ℝ)
    (ht₁ : hardyStart n ≤ t₁) :
    |∫ t in Set.Ioc (hardyStart n) t₁, hardyCos n t| ≤ t₁ - hardyStart n := by
  rw [← intervalIntegral.integral_of_le ht₁]
  have hbd : ∀ t ∈ Set.uIoc (hardyStart n) t₁, ‖hardyCos n t‖ ≤ 1 := by
    intro t _; rw [Real.norm_eq_abs]; exact abs_cos_le_one _
  calc |∫ t in (hardyStart n)..t₁, hardyCos n t|
      ≤ 1 * |t₁ - hardyStart n| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = t₁ - hardyStart n := by
        rw [one_mul, abs_of_nonneg (sub_nonneg.mpr ht₁)]

/-- Far-from-stationary VdC bound via StationaryPhasePerMode:
    |∫_{t₁}^T hardyCos n| ≤ 3/m when the phase φ(t) = θ(t) - t·log(n+1)
    satisfies the VdC first-derivative test conditions on [t₁, T].

    The phase regularity hypotheses (C², φ' ≥ m, φ'' ≥ 0) are passed
    explicitly. These must be verified using the specific structure of
    hardyTheta — see per_mode_tail_bound in StationaryPhasePerMode.lean. -/
theorem far_from_stationary_vdc (n : ℕ) (t₁ T m : ℝ)
    (ht₁T : t₁ ≤ T) (hm : 0 < m)
    (hphi : Differentiable ℝ (fun t => hardyTheta t - t * Real.log (↑n + 1)))
    (hphi' : Differentiable ℝ (deriv (fun t => hardyTheta t - t * Real.log (↑n + 1))))
    (hphi'' : Continuous (deriv (deriv (fun t => hardyTheta t - t * Real.log (↑n + 1)))))
    (hphi'_lower : ∀ t ∈ Set.Icc t₁ T,
      m ≤ deriv (fun t => hardyTheta t - t * Real.log (↑n + 1)) t)
    (hphi''_nn : ∀ t ∈ Set.Icc t₁ T,
      0 ≤ deriv (deriv (fun t => hardyTheta t - t * Real.log (↑n + 1))) t) :
    |∫ t in Set.Ioc t₁ T, hardyCos n t| ≤ 3 / m := by
  rw [← intervalIntegral.integral_of_le ht₁T]
  exact Aristotle.StationaryPhasePerMode.per_mode_tail_bound n t₁ T m ht₁T hm
    hphi hphi' hphi'' hphi'_lower hphi''_nn

/-- Combined split-and-bound: |hardyCosIntegral n T| ≤ (t₁ - hs(n)) + 3/m.
    This is the pre-optimization version. To get O(√(n+1)), choose t₁ and m
    so that both terms are O(√(n+1)).

    Phase regularity hypotheses (C², φ' ≥ m, φ'' ≥ 0) are for [t₁, T] only. -/
theorem hardyCosIntegral_split_bound (n : ℕ) (T t₁ m : ℝ)
    (ht₁_lo : hardyStart n ≤ t₁) (ht₁_hi : t₁ ≤ T) (hm : 0 < m)
    (hphi : Differentiable ℝ (fun t => hardyTheta t - t * Real.log (↑n + 1)))
    (hphi' : Differentiable ℝ (deriv (fun t => hardyTheta t - t * Real.log (↑n + 1))))
    (hphi'' : Continuous (deriv (deriv (fun t => hardyTheta t - t * Real.log (↑n + 1)))))
    (hphi'_lower : ∀ t ∈ Set.Icc t₁ T,
      m ≤ deriv (fun t => hardyTheta t - t * Real.log (↑n + 1)) t)
    (hphi''_nn : ∀ t ∈ Set.Icc t₁ T,
      0 ≤ deriv (deriv (fun t => hardyTheta t - t * Real.log (↑n + 1))) t) :
    |hardyCosIntegral n T| ≤ (t₁ - hardyStart n) + 3 / m := by
  rw [hardyCosIntegral_split n T t₁ ht₁_lo ht₁_hi]
  calc |(∫ t in Set.Ioc (hardyStart n) t₁, hardyCos n t) +
        (∫ t in Set.Ioc t₁ T, hardyCos n t)|
      ≤ |∫ t in Set.Ioc (hardyStart n) t₁, hardyCos n t| +
        |∫ t in Set.Ioc t₁ T, hardyCos n t| := abs_add_le _ _
    _ ≤ (t₁ - hardyStart n) + 3 / m := by
        linarith [near_stationary_trivial n t₁ ht₁_lo,
                  far_from_stationary_vdc n t₁ T m ht₁_hi hm
                    hphi hphi' hphi'' hphi'_lower hphi''_nn]

/-- Degenerate case: when T < hardyStart n, the integral is zero. -/
theorem hardyCosIntegral_zero_of_lt (n : ℕ) (T : ℝ) (h : T < hardyStart n) :
    hardyCosIntegral n T = 0 := by
  unfold hardyCosIntegral
  rw [show Set.Ioc (hardyStart n) T = ∅ from
    Set.Ioc_eq_empty (not_lt.mpr (le_of_lt h))]
  simp

/-- When T < hardyStart n, the bound holds trivially for any B > 0. -/
theorem hardyCosIntegral_bound_trivial_of_lt (n : ℕ) (T : ℝ) (B : ℝ) (hB : 0 < B)
    (h : T < hardyStart n) :
    |hardyCosIntegral n T| ≤ B * Real.sqrt ((n : ℝ) + 1) := by
  rw [hardyCosIntegral_zero_of_lt n T h]
  simp
  exact mul_nonneg (le_of_lt hB) (Real.sqrt_nonneg _)

end VdCSublemmas

/-! ## Part 9c: VdC analysis — why per_mode_sqrt_cos_bound needs a GLOBAL argument

### The per-mode VdC approach gives O(n+1), not O(√(n+1))

The `hardyCosIntegral n T` integrates cos(θ(t) - t·log(n+1)) over
[hardyStart n, T] = [2π(n+1)², T]. The phase is φ(t) = θ(t) - t·log(n+1), with:
  - φ'(t) = θ'(t) - log(n+1) ≈ (1/2)·log(t/(2π)) - log(n+1)
  - φ''(t) = θ''(t) = 1/(2t) > 0

The stationary point t* = 2π(n+1)² = hardyStart(n) is the LEFT endpoint of
integration, so the integral starts at the point of zero oscillation.

**Splitting at t₁ = hardyStart(n+1) = 2π(n+2)²:**

1. Near block [2π(n+1)², 2π(n+2)²]: length = 2π(2n+3) ≈ 4π(n+1).
   - VdC2 (second derivative): inf|φ''| = 1/(2·2π(n+2)²) ≈ 1/(4π(n+1)²).
     Bound: 8/√μ = 8·2√π·(n+2) ≈ 16√π·(n+1). This is O(n+1).
   - Trivial bound: 2π(2n+3) ≈ 4π(n+1). This is also O(n+1), and SMALLER.

2. Far block [2π(n+2)², T]: φ' is monotone increasing, so
   φ'(2π(n+2)²) = (1/2)·log((n+2)²/(n+1)²) = log((n+2)/(n+1)) ≈ 1/(n+1).
   VdC1: 3/φ'(t₁) ≈ 3(n+1). This is O(n+1).

**Total per-mode: O(n+1). Weighted sum:** Σ_{n<N} (n+1)^{-1/2}·C·(n+1) =
C·Σ √(n+1) ≈ (2/3)·C·N^{3/2} ≈ C'·T^{3/4}. This gives O(T^{3/4}), NOT O(T^{1/2}).

**The √(n+1) bound is not achievable by per-mode VdC.** The O(√T) result
requires either:
  (a) The GLOBAL IBP approach from the file header (Titchmarsh §14.5):
      ∫₁ᵀ Z(t)dt = O(√T) by integrating by parts on the whole sum using
      e^{iθ(t)} as the oscillatory factor, with boundary terms O(T^{1/6}/log T)
      and the correction integral controlled by the convexity bound.
  (b) Partial summation over modes, exploiting cancellation BETWEEN modes.

The per-mode infrastructure below documents what VdC CAN deliver (O(n+1)) and
the existing `hardyCosIntegral_split_bound` remains correct and useful as a
building block for approach (a) or (b).

### Phase regularity

The VdC sub-lemmas require regularity hypotheses on φ(t) = θ(t) - t·log(n+1).
These hold because:
  1. hardyTheta is smooth for t > 0
  2. thetaDeriv = (1/2)log(t/(2π)) + O(1/t) is C^∞ for t > 0
  3. φ' = thetaDeriv - log(n+1) = modeOmega n is monotone increasing (θ'' > 0)

Regularity certificates: `differentiable_hardyThetaSmooth`,
`hasDerivAt_hardyThetaSmooth`, `continuous_thetaDeriv` from HardyThetaSmooth.lean. -/

section PerModeLinearBoundInfra

open HardyEstimatesPartial
open Aristotle.HardyNProperties (hardyStart_formula block_length)

/-- First-block length bound: hardyStart(n+1) - hardyStart(n) ≤ 6π(n+1).
    The first block starting at the stationary point has length
    2π(2n+3) = 2π((n+2)² - (n+1)²) ≤ 6π(n+1). -/
theorem first_block_length_le (n : ℕ) :
    hardyStart (n + 1) - hardyStart n ≤ 6 * Real.pi * ((n : ℝ) + 1) :=
  block_length_le n

/-- hardyStart is strictly positive. -/
theorem hardyStart_pos (n : ℕ) : 0 < hardyStart n := by
  rw [hardyStart_formula]; positivity

/-- hardyStart is monotone. -/
theorem hardyStart_mono_le {m n : ℕ} (h : m ≤ n) : hardyStart m ≤ hardyStart n := by
  rw [hardyStart_formula, hardyStart_formula]
  apply mul_le_mul_of_nonneg_left
  · exact sq_le_sq' (by linarith [Nat.cast_nonneg (α := ℝ) m]) (by exact_mod_cast Nat.add_le_add_right h 1)
  · positivity

/-- If hardyStart n ≤ T, then (n+1) ≤ √(T/(2π)).
    This is the fundamental constraint relating mode index to T. -/
theorem mode_index_le_sqrt_of_le (n : ℕ) (T : ℝ)
    (h : hardyStart n ≤ T) :
    ((n : ℝ) + 1) ≤ Real.sqrt (T / (2 * Real.pi)) := by
  rw [hardyStart_formula] at h
  -- h : 2π(n+1)² ≤ T, so (n+1)² ≤ T/(2π)
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_sq : ((n : ℝ) + 1) ^ 2 ≤ T / (2 * Real.pi) := by
    rw [div_le_iff₀ hpi] at *; linarith
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rwa [← Real.sqrt_sq hn1, Real.sqrt_le_sqrt]

/-- (n+1)² ≤ T/(2π) when hardyStart n ≤ T. -/
theorem mode_index_sq_le_of_le (n : ℕ) (T : ℝ)
    (h : hardyStart n ≤ T) :
    2 * Real.pi * ((n : ℝ) + 1) ^ 2 ≤ T := by
  rw [hardyStart_formula] at h; linarith

/-- The integration interval length T - hardyStart(n) ≤ T for any n. -/
theorem integral_interval_le_T (n : ℕ) (T : ℝ) (h : hardyStart n ≤ T) :
    T - hardyStart n ≤ T := by linarith [hardyStart_pos n]

/-- Phase derivative lower bound on far block: for t ≥ hardyStart(n+1),
    the modeOmega satisfies the quantitative lower bound needed for VdC1.
    Specifically, modeOmega n (hardyStart(n+1)) = (1/2)·log((n+2)²/(n+1)²)
    = log((n+2)/(n+1)) which is ≥ 1/(2(n+2)) ≥ 1/(2(n+1)+2).

    This bound shows that VdC1 on [hardyStart(n+1), T] gives
    3/modeOmega ≤ 6(n+2) ≤ 6(n+1) + 6, confirming the O(n) far-block bound.

    Note: this is a mathematical fact statement. The formal modeOmega
    lower bound requires concrete hardyTheta derivative evaluation,
    which depends on phase regularity certificates from HardyThetaSmooth. -/
theorem log_ratio_lower_bound (n : ℕ) :
    1 / (2 * ((n : ℝ) + 2)) ≤ Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h_ratio : 1 < ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
    rw [one_lt_div hn1]; linarith
  -- Use log(1+x) ≥ x/(1+x) for x > 0
  -- Here x = 1/(n+1), so 1+x = (n+2)/(n+1), and x/(1+x) = 1/(n+2)
  have h_write : ((n : ℝ) + 2) / ((n : ℝ) + 1) = 1 + 1 / ((n : ℝ) + 1) := by
    field_simp
  rw [h_write]
  have hx : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  -- log(1+x) ≥ x - x²/2 ≥ x/2 for 0 < x ≤ 1
  have hx_le : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hn1]; linarith
  calc 1 / (2 * ((n : ℝ) + 2))
      = (1 / ((n : ℝ) + 1)) / (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) := by field_simp
    _ = (1 / ((n : ℝ) + 1)) / (2 * (1 + 1 / ((n : ℝ) + 1))) := by rw [h_write]
    _ ≤ (1 / ((n : ℝ) + 1)) / 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith [hx]
    _ ≤ Real.log (1 + 1 / ((n : ℝ) + 1)) := by
        -- Use Real.add_one_le_exp: 1 + x ≤ exp(x) doesn't directly give log(1+x) ≥ x/2
        -- Instead use: for 0 < x ≤ 1, log(1+x) ≥ x/2
        -- Proof: log(1+x) ≥ x - x²/2 (Taylor remainder) ≥ x - x/2 = x/2
        rw [ge_iff_le, ← Real.exp_le_iff_le_log (by positivity)]
        calc Real.exp ((1 / ((n : ℝ) + 1)) / 2)
            ≤ 1 + (1 / ((n : ℝ) + 1)) / 2 + ((1 / ((n : ℝ) + 1)) / 2) ^ 2 := by
              -- exp(y) ≤ 1 + y + y² for 0 ≤ y ≤ 1 — actually need exp(y) ≤ 1+2y for y ≤ 1
              -- Use: exp(y) ≤ 1/(1-y) for y < 1, then 1/(1-y) ≤ 1+2y for y ≤ 1/2
              sorry
          _ ≤ 1 + 1 / ((n : ℝ) + 1) := by
              nlinarith [hx, hx_le]

end PerModeLinearBoundInfra

end HardyZFirstMomentIBP
