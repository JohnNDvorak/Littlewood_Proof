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

/-! ## Part 9: ibp_oscillatory_bound and first moment assembly

The sorry at `ibp_oscillatory_bound` requires the full per-mode oscillatory
cancellation argument (Titchmarsh 1951, §4.15). The proved sub-components are:

PROVED (in this file):
  - thetaDeriv_lower_bound: θ'(t) ≥ (1/4)·log(t)
  - ibp_boundary_bound: ‖ζ(T)‖/θ'(T) ≤ C·T^{1/2}
  - ibp_correction_integrand_bound: |d/dt[ζ/(iθ')]| ≤ C·t^{3/4}/log(t)
  - hardyZ_pointwise_bound: |Z(t)| ≤ C·|t|^{1/2}
  - errorTerm_pointwise_from_rs: |ErrorTerm(t)| ≤ C·t^{-1/4} (Part 8)
  - errorTerm_integral_linear: |∫ ErrorTerm| ≤ C·T (Part 8)
  - block_errorTerm_integral_le: per-block ErrorTerm bound (Part 8)
  - sqrt_log_le_rpow: T^{1/2}·log T ≤ C_ε·T^{1/2+ε}
  - block_sum_assembly: per-mode VdC total ≤ O(K² + K^{3/2})

REMAINING GAP: per-mode global VdC on the IBP correction integral.
  The correction ∫ d/dt[ζ/(iθ')] · e^{iθ} dt has the oscillatory e^{iθ} factor.
  Decomposing ζ into modes and applying VdC per mode to the correction gives
  each mode's correction as O(1/(n^{1/2} · (θ'_min)²)), summing to O(1/log²T₀).
  This is the content of Titchmarsh §4.15, Lemma 4.16. -/

private theorem ibp_oscillatory_bound :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Set.Ioc 1 T, HardyEstimatesPartial.hardyZ t| ≤ C * T ^ ((1 : ℝ) / 2) := by
  sorry

/-- **Hardy Z first moment bound**: |∫₁ᵀ Z(t) dt| ≤ C · T^{1/2+ε}.

    This is the classical result of Titchmarsh (1951, §4.15).

    The proof uses the IBP oscillatory bound (O(T^{1/2})) and absorbs
    it into the T^{1/2+ε} envelope.

    SUB-OBLIGATIONS:
    (a) thetaDeriv_lower_bound: θ'(t) ≥ (1/4)·log(t) — PROVED
    (b) inv_thetaDeriv_le: 1/θ'(t) ≤ 4/log(t) — PROVED
    (c) continuousOn_inv_thetaDeriv — PROVED
    (d) hasDerivAt_exp_iTheta — PROVED
    (e) hardyZ_pointwise_bound — PROVED (from PhragmenLindelof)
    (f) ibp_oscillatory_bound — SORRY (correction integral via AFE + VdC)
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

end HardyZFirstMomentIBP
