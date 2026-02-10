import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.VanDerCorputInfra
import Littlewood.Aristotle.CosPiSqSign
import Littlewood.Aristotle.VdcFirstDerivTest
import Littlewood.Aristotle.HardyCosSmooth
import Littlewood.Bridge.HardyChainHyp

/-!
Bridge plumbing for Hardy's first-moment hypothesis.

This module is sorry-free and does not add new axioms. It isolates the exact
remaining analytic obligations:

1. a `MainTerm` integral bound at scale `T^(1/2+ε)`
2. an `ErrorTerm` integral bound at scale `T^(1/2+ε)`

Once those are available, the final `HardyFirstMomentUpperHyp` statement follows
immediately from `HardyZFirstMoment.hardyZ_first_moment_bound_conditional_two_bounds`.
-/

noncomputable section

open Complex Real Set Filter MeasureTheory

namespace HardyFirstMomentWiring

/-- Missing main-term estimate in the Hardy first-moment chain. -/
class MainTermFirstMomentBoundHyp : Prop where
  bound : ∀ ε : ℝ, ε > 0 →
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, HardyEstimatesPartial.MainTerm t| ≤ C * T ^ (1 / 2 + ε)

/-- Missing error-term estimate in the Hardy first-moment chain. -/
class ErrorTermFirstMomentBoundHyp : Prop where
  bound : ∀ ε : ℝ, ε > 0 →
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, HardyEstimatesPartial.ErrorTerm t| ≤ C * T ^ (1 / 2 + ε)

/-- Stronger optional input for the Hardy remainder:
pointwise `t^(-1/2)` decay on `[1, ∞)`. -/
class ErrorTermPointwiseInvSqrtBoundHyp : Prop where
  bound :
    ∃ C > 0, ∀ t : ℝ, t ≥ 1 →
      |HardyEstimatesPartial.ErrorTerm t| ≤ C / Real.sqrt t

/-- A pointwise `t^(-1/2)` bound for `ErrorTerm` implies the full
`ErrorTermFirstMomentBoundHyp` scale `T^(1/2+ε)` for every `ε > 0`. -/
theorem errorTermFirstMomentBound_of_pointwise_invSqrt
    (hpoint :
      ∃ C > 0, ∀ t : ℝ, t ≥ 1 →
        |HardyEstimatesPartial.ErrorTerm t| ≤ C / Real.sqrt t) :
    ErrorTermFirstMomentBoundHyp := by
  rcases hpoint with ⟨C₀, hC₀, hpointC₀⟩
  refine ⟨?_⟩
  intro ε hε
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hErrInt :
      IntervalIntegrable HardyEstimatesPartial.ErrorTerm volume 1 T := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT1).2
      (HardyEstimatesPartial.errorTerm_integrable T)
  have hInvSqrtInt :
      IntervalIntegrable (fun t : ℝ => C₀ / Real.sqrt t) volume 1 T := by
    refine (continuousOn_of_forall_continuousAt ?_).intervalIntegrable
    intro t ht
    have htIcc : t ∈ Set.Icc (1 : ℝ) T := by
      simpa [Set.uIcc_of_le hT1] using ht
    have ht_pos : 0 < t := lt_of_lt_of_le (by norm_num) htIcc.1
    refine ContinuousAt.div continuousAt_const
      Real.continuous_sqrt.continuousAt ?_
    exact (Real.sqrt_ne_zero (le_of_lt ht_pos)).2 (ne_of_gt ht_pos)
  have hMono :
      ∫ t in 1..T, |HardyEstimatesPartial.ErrorTerm t|
        ≤ ∫ t in 1..T, C₀ / Real.sqrt t := by
    refine intervalIntegral.integral_mono_on hT1 hErrInt.norm hInvSqrtInt ?_
    intro t ht
    have htIcc : t ∈ Set.Icc (1 : ℝ) T := by
      simpa [Set.uIcc_of_le hT1] using ht
    exact hpointC₀ t htIcc.1
  have hAbsInt :
      |∫ t in 1..T, HardyEstimatesPartial.ErrorTerm t|
        ≤ ∫ t in 1..T, |HardyEstimatesPartial.ErrorTerm t| := by
    simpa [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_integral_norm
        (f := HardyEstimatesPartial.ErrorTerm) hT1)
  have hConstMul :
      ∫ t in 1..T, C₀ / Real.sqrt t
        = C₀ * ∫ t in 1..T, t ^ (-(1 / 2 : ℝ)) := by
    calc
      ∫ t in 1..T, C₀ / Real.sqrt t
          = ∫ t in 1..T, C₀ * t ^ (-(1 / 2 : ℝ)) := by
              refine intervalIntegral.integral_congr ?_
              intro t ht
              have htIcc : t ∈ Set.Icc (1 : ℝ) T := by
                simpa [Set.uIcc_of_le hT1] using ht
              have ht_pos : 0 < t := lt_of_lt_of_le (by norm_num) htIcc.1
              simpa [div_eq_mul_inv, Real.sqrt_eq_rpow, Real.rpow_neg (le_of_lt ht_pos)]
      _ = C₀ * ∫ t in 1..T, t ^ (-(1 / 2 : ℝ)) := by
            simpa [mul_assoc, mul_comm, mul_left_comm] using
              (intervalIntegral.integral_const_mul C₀
                (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (a := 1) (b := T))
  have hNoZero : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) T := by
    intro h0
    have h0' : (0 : ℝ) ∈ Set.Icc (1 : ℝ) T := by
      simpa [Set.uIcc_of_le hT1] using h0
    exact (not_le_of_gt (by norm_num : (0 : ℝ) < 1)) h0'.1
  have hRpowRaw :
      ∫ t in 1..T, t ^ (-(1 / 2 : ℝ))
        = (T ^ ((-(1 / 2 : ℝ)) + 1) - (1 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1))
            / ((-(1 / 2 : ℝ)) + 1) := by
    simpa using
      (integral_rpow (a := 1) (b := T) (r := (-(1 / 2 : ℝ)))
        (Or.inr ⟨by norm_num, hNoZero⟩))
  have hRpowLe :
      ∫ t in 1..T, t ^ (-(1 / 2 : ℝ)) ≤ 2 * Real.sqrt T := by
    calc
      ∫ t in 1..T, t ^ (-(1 / 2 : ℝ))
          = (T ^ ((-(1 / 2 : ℝ)) + 1) - (1 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1))
              / ((-(1 / 2 : ℝ)) + 1) := hRpowRaw
      _ = (T ^ (1 / 2 : ℝ) - 1) / (1 / 2 : ℝ) := by
            ring_nf
      _ = (T ^ (1 / 2 : ℝ) - (1 : ℝ) ^ (1 / 2 : ℝ)) * 2 := by ring
      _ = 2 * (Real.sqrt T - 1) := by
            rw [Real.sqrt_eq_rpow]
            ring
      _ ≤ 2 * Real.sqrt T := by
            nlinarith [Real.sqrt_nonneg T]
  have hInvSqrtLe :
      ∫ t in 1..T, C₀ / Real.sqrt t ≤ 2 * C₀ * Real.sqrt T := by
    calc
      ∫ t in 1..T, C₀ / Real.sqrt t
          = C₀ * ∫ t in 1..T, t ^ (-(1 / 2 : ℝ)) := hConstMul
      _ ≤ C₀ * (2 * Real.sqrt T) := by
            exact mul_le_mul_of_nonneg_left hRpowLe (le_of_lt hC₀)
      _ = 2 * C₀ * Real.sqrt T := by ring
  have hPowMono : T ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 + ε) := by
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  calc
    |∫ t in Ioc 1 T, HardyEstimatesPartial.ErrorTerm t|
        = |∫ t in 1..T, HardyEstimatesPartial.ErrorTerm t| := by
            rw [← intervalIntegral.integral_of_le hT1]
    _ ≤ ∫ t in 1..T, |HardyEstimatesPartial.ErrorTerm t| := hAbsInt
    _ ≤ ∫ t in 1..T, C₀ / Real.sqrt t := hMono
    _ ≤ 2 * C₀ * Real.sqrt T := hInvSqrtLe
    _ = (2 * C₀) * T ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
    _ ≤ (2 * C₀) * T ^ (1 / 2 + ε) := by
          exact mul_le_mul_of_nonneg_left hPowMono (by positivity)

instance [ErrorTermPointwiseInvSqrtBoundHyp] : ErrorTermFirstMomentBoundHyp := by
  exact errorTermFirstMomentBound_of_pointwise_invSqrt
    ErrorTermPointwiseInvSqrtBoundHyp.bound

/-- Complex oscillatory phase attached to `hardyCos`. -/
noncomputable def hardyExpPhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (HardyEstimatesPartial.hardyTheta t - t * Real.log (n + 1)))

/-- Rewrite `exp(i*hardyTheta)` in terms of the branch-independent
`hardyPhase` used in measurability infrastructure. -/
lemma exp_I_hardyTheta_eq_hardyPhase (t : ℝ) :
    Complex.exp (Complex.I * HardyEstimatesPartial.hardyTheta t)
      = HardyEstimatesPartial.hardyPhase t := by
  let s : ℂ := (1 / 4 : ℂ) + Complex.I * (t / 2)
  have hs : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    norm_num [s]
  have hlog :
      Complex.exp (Complex.I * (Complex.log (Complex.Gamma s)).im)
        = Complex.Gamma s / ↑‖Complex.Gamma s‖ := by
    simpa [s] using HardyEstimatesPartial.exp_im_log_eq_div_norm (Complex.Gamma s) hs
  let A : ℂ := Complex.I * (Complex.log (Complex.Gamma s)).im
  let B : ℂ := Complex.I * ((t / 2) * Real.log Real.pi)
  let A0 : ℂ := Complex.I * ((Complex.log (Complex.Gamma s)).im - (t / 2) * Real.log Real.pi)
  have hA0 : A0 = A - B := by
    simp [A0, A, B, mul_sub]
  have hsplit : Complex.exp (A - B) = Complex.exp A * Complex.exp (-B) := by
    rw [sub_eq_add_neg, Complex.exp_add]
  have hlogA : Complex.exp A = Complex.Gamma s / ↑‖Complex.Gamma s‖ := by
    simpa [A] using hlog
  calc
    Complex.exp (Complex.I * HardyEstimatesPartial.hardyTheta t)
        = Complex.exp A0 := by
            simp [HardyEstimatesPartial.hardyTheta, s, A0]
    _ = Complex.exp (A - B) := by rw [hA0]
    _ = Complex.exp A * Complex.exp (-B) := hsplit
    _ = (Complex.Gamma s / ↑‖Complex.Gamma s‖) * Complex.exp (-B) := by rw [hlogA]
    _ = HardyEstimatesPartial.hardyPhase t := by
      unfold HardyEstimatesPartial.hardyPhase
      subst s
      refine congrArg
        (fun z : ℂ =>
          (Complex.Gamma (1 / 4 + Complex.I * (t / 2)) /
            ↑‖Complex.Gamma (1 / 4 + Complex.I * (t / 2))‖) * z) ?_
      unfold B
      congr 1
      ring

lemma hardyExpPhase_eq_hardyPhase_mul_exp (n : ℕ) (t : ℝ) :
    hardyExpPhase n t
      = HardyEstimatesPartial.hardyPhase t
          * Complex.exp (-Complex.I * t * Real.log (n + 1)) := by
  unfold hardyExpPhase
  calc
    Complex.exp (Complex.I * (HardyEstimatesPartial.hardyTheta t - t * Real.log (n + 1)))
        = Complex.exp (Complex.I * HardyEstimatesPartial.hardyTheta t)
            * Complex.exp (-Complex.I * t * Real.log (n + 1)) := by
              have hmul :
                  Complex.I * (HardyEstimatesPartial.hardyTheta t - t * Real.log (n + 1))
                    = Complex.I * HardyEstimatesPartial.hardyTheta t
                      + (-Complex.I * t * Real.log (n + 1)) := by
                    ring
              rw [hmul, Complex.exp_add]
    _ = HardyEstimatesPartial.hardyPhase t * Complex.exp (-Complex.I * t * Real.log (n + 1)) := by
      rw [exp_I_hardyTheta_eq_hardyPhase]

lemma hardyExpPhase_eq_hardyCosExp (n : ℕ) (t : ℝ) :
    hardyExpPhase n t = HardyCosSmooth.hardyCosExp n t := by
  have hcexp := HardyCosSmooth.hardyCosExp_eq_cexp_phaseArg n t
  have harg := HardyCosSmooth.hardyPhaseArg_eq_hardyTheta_sub_log n t
  rw [harg] at hcexp
  simpa [hardyExpPhase] using hcexp.symm

lemma hardyExpPhase_differentiableAt (n : ℕ) (t : ℝ) :
    DifferentiableAt ℝ (hardyExpPhase n) t := by
  have hEq : hardyExpPhase n = fun x : ℝ => HardyCosSmooth.hardyCosExp n x := by
    funext x
    exact hardyExpPhase_eq_hardyCosExp n x
  simpa [hEq] using HardyCosSmooth.differentiableAt_hardyCosExp_complex n t

lemma hardyExpPhase_differentiable (n : ℕ) :
    Differentiable ℝ (hardyExpPhase n) := by
  intro t
  exact hardyExpPhase_differentiableAt n t

lemma hardyExpPhase_continuous (n : ℕ) : Continuous (hardyExpPhase n) := by
  exact (hardyExpPhase_differentiable n).continuous

lemma hardyCos_eq_re_hardyExpPhase (n : ℕ) (t : ℝ) :
    HardyEstimatesPartial.hardyCos n t = (hardyExpPhase n t).re := by
  let x : ℝ := HardyEstimatesPartial.hardyTheta t - t * Real.log (n + 1)
  have hx : (hardyExpPhase n t).re = Real.cos x := by
    simpa [hardyExpPhase, x, mul_comm] using (Complex.exp_ofReal_mul_I_re x)
  have hcos : HardyEstimatesPartial.hardyCos n t = Real.cos x := by
    simp [HardyEstimatesPartial.hardyCos, x]
  rw [hcos, hx]

lemma hardyExpPhase_norm (n : ℕ) (t : ℝ) : ‖hardyExpPhase n t‖ = 1 := by
  simpa [hardyExpPhase, mul_comm] using
    Complex.norm_exp_I_mul_ofReal
      (HardyEstimatesPartial.hardyTheta t - t * Real.log (n + 1))

lemma hardyExpPhase_intervalIntegrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (hardyExpPhase n) volume a b := by
  exact (hardyExpPhase_continuous n).intervalIntegrable a b

lemma hardyStart_ge_two (n : ℕ) :
    (2 : ℝ) ≤ HardyEstimatesPartial.hardyStart n := by
  have hsq : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 : ℕ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith
  unfold HardyEstimatesPartial.hardyStart
  nlinarith [Real.pi_gt_three, hsq]

lemma hardyExpPhase_integrableOn_Ioc (n : ℕ) (a b : ℝ) :
    IntegrableOn (hardyExpPhase n) (Ioc a b) := by
  exact (hardyExpPhase_continuous n).integrableOn_Ioc

lemma hardyCosIntegral_eq_re_hardyExpPhaseIntegral (n : ℕ) (a b : ℝ) :
    ∫ t in Ioc a b, HardyEstimatesPartial.hardyCos n t
      = (∫ t in Ioc a b, hardyExpPhase n t).re := by
  have hcos :
      ∫ t, HardyEstimatesPartial.hardyCos n t ∂ (volume.restrict (Ioc a b))
        = ∫ t, (hardyExpPhase n t).re ∂ (volume.restrict (Ioc a b)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    simpa [hardyCos_eq_re_hardyExpPhase]
  have hre :
      ∫ t, (hardyExpPhase n t).re ∂ (volume.restrict (Ioc a b))
        = (∫ t, hardyExpPhase n t ∂ (volume.restrict (Ioc a b))).re := by
    simpa using
      (integral_re (μ := volume.restrict (Ioc a b)) (f := hardyExpPhase n)
        (hardyExpPhase_integrableOn_Ioc n a b))
  exact hcos.trans hre

/-- Optional stronger analytic input: uniform boundedness of the complex
oscillatory integral associated to `hardyCos`. -/
class HardyExpPhaseIntegralUniformBoundHyp : Prop where
  bound :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      ‖∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t‖ ≤ B

/-- Variant of the complex oscillatory bound that only needs to hold on the
nonempty support range `hardyStart n ≤ T`, stated with interval integrals. -/
class HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp : Prop where
  bound :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖ ≤ B

/-- Mode-sensitive support-interval bound for the complex oscillatory phase:
the `n`-mode integral is allowed to grow like `√(n+1)`. -/
class HardyExpPhaseIntervalIntegralSqrtModeBoundOnSupportHyp : Prop where
  bound :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖
        ≤ B * Real.sqrt (n + 1)

/-- Stationary-window tail input for the Hardy oscillatory phase.
This is the second-derivative/stationary-phase route: after removing a short
initial window of length `√(n+1)` from the support start `hardyStart n`,
the remaining tail integral admits a `√(n+1)` bound. -/
class HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp : Prop where
  bound :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ‖∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
          hardyExpPhase n t‖ ≤ B * Real.sqrt (n + 1)

/-- Recover the full support `√(n+1)` bound by splitting into:
1) a short near-stationary window `[hardyStart n, hardyStart n + √(n+1)]`
   controlled by `‖hardyExpPhase‖ = 1`, and
2) the tail controlled by
   `HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp`. -/
theorem hardyExpPhaseIntervalIntegralSqrtModeBoundOnSupport_of_stationaryTail
    (htail :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
        ‖∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
            hardyExpPhase n t‖ ≤ B * Real.sqrt (n + 1)) :
    HardyExpPhaseIntervalIntegralSqrtModeBoundOnSupportHyp := by
  rcases htail with ⟨B, hB, htailB⟩
  refine ⟨B + 1, add_pos hB zero_lt_one, ?_⟩
  intro n T hT hstart
  let a : ℝ := HardyEstimatesPartial.hardyStart n
  let c : ℝ := a + Real.sqrt (n + 1)
  by_cases hcut : c ≤ T
  · have hsplit :
        ∫ t in a..T, hardyExpPhase n t
          = (∫ t in a..c, hardyExpPhase n t)
              + (∫ t in c..T, hardyExpPhase n t) := by
      simpa using
        (intervalIntegral.integral_add_adjacent_intervals
          (hardyExpPhase_intervalIntegrable n a c)
          (hardyExpPhase_intervalIntegrable n c T)).symm
    have hNear :
        ‖∫ t in a..c, hardyExpPhase n t‖ ≤ Real.sqrt (n + 1) := by
      calc
        ‖∫ t in a..c, hardyExpPhase n t‖
            ≤ ∫ t in a..c, ‖hardyExpPhase n t‖ := by
                simpa using intervalIntegral.norm_integral_le_integral_norm
                  (f := fun t => hardyExpPhase n t)
                  (le_add_of_nonneg_right (Real.sqrt_nonneg _))
        _ = ∫ t in a..c, (1 : ℝ) := by
              refine intervalIntegral.integral_congr ?_
              intro t ht
              simpa using hardyExpPhase_norm n t
        _ = c - a := by simp
        _ = Real.sqrt (n + 1) := by
              simp [c]
    have hTail :
        ‖∫ t in c..T, hardyExpPhase n t‖ ≤ B * Real.sqrt (n + 1) := by
      have hcut' : HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T := by
        simpa [a, c] using hcut
      simpa [a, c] using htailB n T hT hcut'
    calc
      ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖
          = ‖(∫ t in a..c, hardyExpPhase n t) + (∫ t in c..T, hardyExpPhase n t)‖ := by
              simpa [a, hsplit]
      _ ≤ ‖∫ t in a..c, hardyExpPhase n t‖ + ‖∫ t in c..T, hardyExpPhase n t‖ := by
            exact norm_add_le _ _
      _ ≤ Real.sqrt (n + 1) + B * Real.sqrt (n + 1) := add_le_add hNear hTail
      _ = (B + 1) * Real.sqrt (n + 1) := by ring
  · have hcut' : T ≤ c := le_of_not_ge hcut
    have hShort :
        ‖∫ t in a..T, hardyExpPhase n t‖ ≤ Real.sqrt (n + 1) := by
      calc
        ‖∫ t in a..T, hardyExpPhase n t‖
            ≤ ∫ t in a..T, ‖hardyExpPhase n t‖ := by
                simpa using intervalIntegral.norm_integral_le_integral_norm
                  (f := fun t => hardyExpPhase n t) hstart
        _ = ∫ t in a..T, (1 : ℝ) := by
              refine intervalIntegral.integral_congr ?_
              intro t ht
              simpa using hardyExpPhase_norm n t
        _ = T - a := by simp
        _ ≤ c - a := by exact sub_le_sub_right hcut' a
        _ = Real.sqrt (n + 1) := by
              simp [c]
    have hOneLe : (1 : ℝ) ≤ B + 1 := by linarith
    calc
      ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖
          = ‖∫ t in a..T, hardyExpPhase n t‖ := by simp [a]
      _ ≤ Real.sqrt (n + 1) := hShort
      _ = (1 : ℝ) * Real.sqrt (n + 1) := by ring
      _ ≤ (B + 1) * Real.sqrt (n + 1) := by
            exact mul_le_mul_of_nonneg_right hOneLe (Real.sqrt_nonneg _)

instance [HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp] :
    HardyExpPhaseIntervalIntegralSqrtModeBoundOnSupportHyp := by
  exact hardyExpPhaseIntervalIntegralSqrtModeBoundOnSupport_of_stationaryTail
    HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp.bound

/-- Any support-level `√(n+1)` bound yields the stationary-window tail bound
by subtracting two support integrals:
`∫_{start+√}^{T} = ∫_{start}^{T} - ∫_{start}^{start+√}`. -/
theorem hardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupport_of_intervalSqrtMode
    (hinterval :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖
          ≤ B * Real.sqrt (n + 1)) :
    HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp := by
  rcases hinterval with ⟨B, hB, hbound⟩
  refine ⟨2 * B, by positivity, ?_⟩
  intro n T hT htail
  let a : ℝ := HardyEstimatesPartial.hardyStart n
  let c : ℝ := a + Real.sqrt (n + 1)
  have hstartC : a ≤ c := by
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hstartT : a ≤ T := by
    exact le_trans hstartC (by simpa [a, c] using htail)
  have hStart_ge_two : (2 : ℝ) ≤ a := by
    unfold a HardyEstimatesPartial.hardyStart
    have hsq : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 : ℕ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith
    nlinarith [Real.pi_gt_three, hsq]
  have hC_ge_two : (2 : ℝ) ≤ c := by
    exact le_trans hStart_ge_two hstartC
  have hsplit :
      ∫ t in a..T, hardyExpPhase n t
        = (∫ t in a..c, hardyExpPhase n t)
            + (∫ t in c..T, hardyExpPhase n t) := by
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (hardyExpPhase_intervalIntegrable n a c)
        (hardyExpPhase_intervalIntegrable n c T)).symm
  have htailEq :
      ∫ t in c..T, hardyExpPhase n t
        = (∫ t in a..T, hardyExpPhase n t)
            - (∫ t in a..c, hardyExpPhase n t) := by
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hsplit.symm)
  calc
    ‖∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T, hardyExpPhase n t‖
        = ‖∫ t in c..T, hardyExpPhase n t‖ := by
            simp [a, c]
    _ = ‖(∫ t in a..T, hardyExpPhase n t)
            - (∫ t in a..c, hardyExpPhase n t)‖ := by
            rw [htailEq]
    _ ≤ ‖∫ t in a..T, hardyExpPhase n t‖ + ‖∫ t in a..c, hardyExpPhase n t‖ := by
          exact norm_sub_le _ _
    _ ≤ B * Real.sqrt (n + 1) + B * Real.sqrt (n + 1) := by
          exact add_le_add (hbound n T hT hstartT) (hbound n c hC_ge_two hstartC)
    _ = (2 * B) * Real.sqrt (n + 1) := by ring

theorem hardyExpPhaseIntervalIntegralSqrtModeBoundOnSupport_of_uniform
    (hinterval :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖ ≤ B) :
    HardyExpPhaseIntervalIntegralSqrtModeBoundOnSupportHyp := by
  obtain ⟨B, hB, hintervalB⟩ := hinterval
  refine ⟨B, hB, ?_⟩
  intro n T hT hstart
  calc
    ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖
        ≤ B := hintervalB n T hT hstart
    _ = B * 1 := by ring
    _ ≤ B * Real.sqrt (n + 1) := by
        have hBnn : 0 ≤ B := le_of_lt hB
        have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (n + 1) := by
          have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          simpa using (Real.sqrt_le_sqrt hbase)
        exact mul_le_mul_of_nonneg_left hsqrt_ge_one hBnn

instance [HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp] :
    HardyExpPhaseIntervalIntegralSqrtModeBoundOnSupportHyp := by
  exact hardyExpPhaseIntervalIntegralSqrtModeBoundOnSupport_of_uniform
    HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp.bound

/-- Real phase underlying `hardyExpPhase`. -/
noncomputable def hardyPhaseReal (n : ℕ) (t : ℝ) : ℝ :=
  HardyEstimatesPartial.hardyTheta t - t * Real.log (n + 1)

lemma hardyExpPhase_eq_exp_phase (n : ℕ) (t : ℝ) :
    hardyExpPhase n t = Complex.exp (Complex.I * hardyPhaseReal n t) := by
  simp [hardyExpPhase, hardyPhaseReal]

/-- Candidate integration-by-parts primitive for van der Corput. -/
noncomputable def hardyVdcPrimitive (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * hardyPhaseReal n t) /
    (Complex.I * deriv (hardyPhaseReal n) t)

/-- Correction integrand produced by differentiating the primitive. -/
noncomputable def hardyVdcCorrection (n : ℕ) (t : ℝ) : ℂ :=
  hardyExpPhase n t *
    deriv (fun x => 1 / (Complex.I * deriv (hardyPhaseReal n) x)) t

/-- The correction term has the same norm as its derivative-inverse factor,
because `‖hardyExpPhase n t‖ = 1`. -/
lemma hardyVdcCorrection_norm_eq_derivInv_norm (n : ℕ) (t : ℝ) :
    ‖hardyVdcCorrection n t‖ =
      ‖deriv (fun x => 1 / (Complex.I * deriv (hardyPhaseReal n) x)) t‖ := by
  unfold hardyVdcCorrection
  rw [norm_mul, hardyExpPhase_norm, one_mul]

/-- Endpoint-control input for van der Corput integration by parts on the Hardy phase. -/
class HardyExpPhaseVdcEndpointBoundOnSupportHyp : Prop where
  bound :
    ∃ B₀ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ‖hardyVdcPrimitive n T
        - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖ ≤ B₀

/-- Mode-sensitive endpoint control input for van der Corput integration by
parts on the Hardy phase: the endpoint term may grow like `√(n+1)`. -/
class HardyExpPhaseVdcEndpointSqrtModeBoundOnSupportHyp : Prop where
  bound :
    ∃ B₀ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ‖hardyVdcPrimitive n T
        - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖
          ≤ B₀ * Real.sqrt (n + 1)

/-- Correction-integral control input for van der Corput integration by parts
on the Hardy phase. -/
class HardyExpPhaseVdcCorrectionBoundOnSupportHyp : Prop where
  bound :
    ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖ ≤ B₁

/-- Mode-sensitive correction-integral control input for van der Corput
integration by parts on the Hardy phase: the correction term may grow like
`√(n+1)`. -/
class HardyExpPhaseVdcCorrectionSqrtModeBoundOnSupportHyp : Prop where
  bound :
    ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖
        ≤ B₁ * Real.sqrt (n + 1)

/-- Quantitative lower bound input for the Hardy phase derivative on the
support range. This gives endpoint control for the VdC primitive. -/
class HardyExpPhaseDerivAbsLowerBoundOnSupportHyp : Prop where
  bound :
    ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        m ≤ |deriv (hardyPhaseReal n) t|

/-- Mode-sensitive lower bound input for the Hardy phase derivative on support.
The derivative is allowed to decay like `1 / √(n+1)`. This is designed to feed
mode-sensitive endpoint bounds for VdC. -/
class HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp : Prop where
  bound :
    ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        m / Real.sqrt (n + 1) ≤ |deriv (hardyPhaseReal n) t|

/-- Support-wise differentiability input for the phase derivative
`deriv (hardyPhaseReal n)`. -/
class HardyPhaseDerivDifferentiableOnSupportHyp : Prop where
  differentiable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t

/-- Quantitative pointwise decay for the second derivative of the Hardy phase
on support. Combined with a uniform lower bound on `|phase'|`, this yields a
pointwise decay bound for the derivative-inverse correction factor
`deriv (1 / (I * phase'))`. -/
class HardyExpPhaseSecondDerivAbsBoundOnSupportHyp : Prop where
  bound :
    ∃ M > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        |deriv (deriv (hardyPhaseReal n)) t| ≤ M / t ^ (3 / 2 : ℝ)

/-- L¹-control input for the VdC correction integrand on the support range.
This bundles both interval-integrability and a uniform L¹ bound on the support
range.  The integrability field keeps downstream interval-integral identities
honest (instead of relying on default `integral = 0` behavior outside the
integrable regime). -/
class HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp : Prop where
  intervalIntegrable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      IntervalIntegrable (hardyVdcCorrection n) volume
        (HardyEstimatesPartial.hardyStart n) T
  bound :
    ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∫ t in HardyEstimatesPartial.hardyStart n..T, ‖hardyVdcCorrection n t‖ ≤ B₁

/-- Pointwise decay input for the Hardy VdC correction term.  This is a
quantitative substitute for direct `L¹` control: if
`‖hardyVdcCorrection n t‖ ≲ t^(-3/2)` on the support interval, then the
correction is uniformly `L¹`-bounded because `∫_{a}^{∞} t^(-3/2) dt < ∞`. -/
class HardyExpPhaseVdcCorrectionPointwiseDecayOnSupportHyp : Prop where
  bound :
    ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        ‖hardyVdcCorrection n t‖ ≤ B₁ / t ^ (3 / 2 : ℝ)

/-- Equivalent pointwise-decay input on the derivative-inverse factor inside the
VdC correction term. This removes the unit-modulus oscillatory factor. -/
class HardyExpPhaseVdcCorrectionDerivInvPointwiseDecayOnSupportHyp : Prop where
  bound :
    ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        ‖deriv (fun x => 1 / (Complex.I * deriv (hardyPhaseReal n) x)) t‖
          ≤ B₁ / t ^ (3 / 2 : ℝ)

theorem hardyExpPhaseVdcCorrectionPointwiseDecayOnSupport_of_derivInv
    [HardyExpPhaseVdcCorrectionDerivInvPointwiseDecayOnSupportHyp] :
    HardyExpPhaseVdcCorrectionPointwiseDecayOnSupportHyp := by
  obtain ⟨B₁, hB₁, hbound⟩ := HardyExpPhaseVdcCorrectionDerivInvPointwiseDecayOnSupportHyp.bound
  refine ⟨B₁, hB₁, ?_⟩
  intro n T hT hstart t ht
  simpa [hardyVdcCorrection_norm_eq_derivInv_norm] using hbound n T hT hstart t ht

instance [HardyExpPhaseVdcCorrectionDerivInvPointwiseDecayOnSupportHyp] :
    HardyExpPhaseVdcCorrectionPointwiseDecayOnSupportHyp := by
  exact hardyExpPhaseVdcCorrectionPointwiseDecayOnSupport_of_derivInv

theorem hardyExpPhaseVdcCorrectionDerivInvPointwiseDecayOnSupport_of_derivLower_secondDeriv
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    HardyExpPhaseVdcCorrectionDerivInvPointwiseDecayOnSupportHyp := by
  obtain ⟨m, hm, hDerivLower⟩ := HardyExpPhaseDerivAbsLowerBoundOnSupportHyp.bound
  obtain ⟨M, hM, hSecond⟩ := HardyExpPhaseSecondDerivAbsBoundOnSupportHyp.bound
  refine ⟨M / m ^ 2, div_pos hM (sq_pos_of_pos hm), ?_⟩
  intro n T hT hstart t ht
  let den : ℝ → ℂ :=
    fun x : ℝ => Complex.I * ((deriv (hardyPhaseReal n) x : ℝ) : ℂ)
  let g : ℝ → ℂ := (fun _ : ℝ => (1 : ℂ)) / den
  change ‖deriv g t‖ ≤ (M / m ^ 2) / t ^ (3 / 2 : ℝ)
  have hStart_pos : 0 < HardyEstimatesPartial.hardyStart n := by
    unfold HardyEstimatesPartial.hardyStart
    positivity
  have ht' : t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n) T := by
    simpa [Set.uIcc_of_le hstart] using ht
  have ht_pos : 0 < t := lt_of_lt_of_le hStart_pos ht'.1
  have hDerivLower_t : m ≤ |deriv (hardyPhaseReal n) t| := hDerivLower n T hT hstart t ht
  have hDerivNe : deriv (hardyPhaseReal n) t ≠ 0 := by
    have hAbsPos : 0 < |deriv (hardyPhaseReal n) t| := lt_of_lt_of_le hm hDerivLower_t
    exact abs_ne_zero.mp (ne_of_gt hAbsPos)
  have hPhaseDerivDiff :
      DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t :=
    HardyPhaseDerivDifferentiableOnSupportHyp.differentiable n T hT hstart t ht
  have hSecond_t :
      |deriv (deriv (hardyPhaseReal n)) t| ≤ M / t ^ (3 / 2 : ℝ) :=
    hSecond n T hT hstart t ht
  have hDerivHas :
      HasDerivAt (fun x : ℝ => deriv (hardyPhaseReal n) x)
        (deriv (deriv (hardyPhaseReal n)) t) t :=
    hPhaseDerivDiff.hasDerivAt
  have hDerivHasC :
      HasDerivAt
        (fun x : ℝ => ((deriv (hardyPhaseReal n) x : ℝ) : ℂ))
        (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ)) t :=
    HasDerivAt.ofReal_comp hDerivHas
  have hDenHas :
      HasDerivAt
        den
        (Complex.I * (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ))) t := by
    simpa [den, mul_assoc, mul_comm, mul_left_comm] using
      (HasDerivAt.mul (hasDerivAt_const t Complex.I) hDerivHasC)
  have hDenNe : den t ≠ 0 := by
    refine mul_ne_zero Complex.I_ne_zero ?_
    exact_mod_cast hDerivNe
  have hInvHas :
      HasDerivAt
        g
        (-(Complex.I * (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ))) /
          (Complex.I * ((deriv (hardyPhaseReal n) t : ℝ) : ℂ)) ^ 2) t := by
    simpa [g, den] using (HasDerivAt.div (hasDerivAt_const t (1 : ℂ)) hDenHas hDenNe)
  have hDerivEq :
      deriv g t =
        (-(Complex.I * (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ))) /
          (Complex.I * ((deriv (hardyPhaseReal n) t : ℝ) : ℂ)) ^ 2) := by
    simpa using hInvHas.deriv
  have hDenLower :
      m ≤ ‖Complex.I * ((deriv (hardyPhaseReal n) t : ℝ) : ℂ)‖ := by
    simpa using hDerivLower_t
  have hDenSqLower :
      m ^ 2 ≤ ‖Complex.I * ((deriv (hardyPhaseReal n) t : ℝ) : ℂ)‖ ^ 2 := by
    nlinarith [hDenLower]
  have hNumBound' :
      ‖((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ)‖ ≤ M / t ^ (3 / 2 : ℝ) := by
    simpa using hSecond_t
  have hNumBound :
      ‖Complex.I * (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ))‖
        ≤ M / t ^ (3 / 2 : ℝ) := by
    simpa [norm_mul] using hNumBound'
  calc
    ‖deriv g t‖
        = ‖Complex.I * (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ))‖
            / ‖Complex.I * ((deriv (hardyPhaseReal n) t : ℝ) : ℂ)‖ ^ 2 := by
              rw [hDerivEq, norm_div, norm_neg, norm_pow]
    _ ≤ ‖Complex.I * (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ))‖ / m ^ 2 := by
          refine div_le_div_of_nonneg_left ?_ ?_ hDenSqLower
          · exact norm_nonneg _
          · exact sq_pos_of_pos hm
    _ ≤ (M / t ^ (3 / 2 : ℝ)) / m ^ 2 := by
          exact div_le_div_of_nonneg_right hNumBound (sq_nonneg m)
    _ = (M / m ^ 2) / t ^ (3 / 2 : ℝ) := by
          ring

instance [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    HardyExpPhaseVdcCorrectionDerivInvPointwiseDecayOnSupportHyp := by
  exact
    hardyExpPhaseVdcCorrectionDerivInvPointwiseDecayOnSupport_of_derivLower_secondDeriv

/-- Calculus hypotheses needed to turn van der Corput's derivative identity
into an interval-integral decomposition for `hardyExpPhase`. -/
class HardyExpPhaseVdcCalculusOnSupportHyp : Prop where
  phaseDifferentiable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        DifferentiableAt ℝ (hardyPhaseReal n) t
  phaseDerivDifferentiable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t
  phaseDerivNonzero :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        deriv (hardyPhaseReal n) t ≠ 0
  primitiveDifferentiable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        DifferentiableAt ℝ (hardyVdcPrimitive n) t
  primitiveDerivIntervalIntegrable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      IntervalIntegrable (deriv (hardyVdcPrimitive n)) volume
        (HardyEstimatesPartial.hardyStart n) T
  expPhaseIntervalIntegrable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      IntervalIntegrable (hardyExpPhase n) volume
        (HardyEstimatesPartial.hardyStart n) T
  correctionIntervalIntegrable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      IntervalIntegrable (hardyVdcCorrection n) volume
        (HardyEstimatesPartial.hardyStart n) T

/-- Core phase-side calculus input for the Hardy van der Corput decomposition.
This isolates the derivative-side assumptions on `hardyPhaseReal`. -/
class HardyExpPhaseVdcPhaseCalculusOnSupportHyp : Prop where
  phaseDifferentiable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        DifferentiableAt ℝ (hardyPhaseReal n) t
  phaseDerivDifferentiable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t
  phaseDerivNonzero :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        deriv (hardyPhaseReal n) t ≠ 0

/-- Core primitive/correction-side input for the Hardy van der Corput decomposition.
This avoids repeating assumptions derivable from interval-integrability closure. -/
class HardyExpPhaseVdcPrimitiveCorrectionOnSupportHyp : Prop where
  primitiveDifferentiable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        DifferentiableAt ℝ (hardyVdcPrimitive n) t
  correctionIntervalIntegrable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      IntervalIntegrable (hardyVdcCorrection n) volume
        (HardyEstimatesPartial.hardyStart n) T

/-- Support-wise differentiability input for `hardyTheta`.
This is the phase-side analytic regularity needed to differentiate
`hardyPhaseReal`. -/
class HardyThetaDifferentiableOnSupportHyp : Prop where
  differentiable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        DifferentiableAt ℝ HardyEstimatesPartial.hardyTheta t

/-- Quantitative lower-bound input on the Hardy phase gap
`deriv hardyTheta - log(n+1)` along the support range.
This directly controls `|deriv (hardyPhaseReal n)|`. -/
class HardyThetaPhaseGapLowerBoundOnSupportHyp : Prop where
  bound :
    ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        m ≤ |deriv HardyEstimatesPartial.hardyTheta t - Real.log (n + 1)|

/-- Mode-sensitive lower-bound input on the Hardy phase gap
`deriv hardyTheta - log(n+1)` along support. The gap is allowed to decay like
`1 / √(n+1)`. -/
class HardyThetaPhaseGapLowerSqrtModeOnSupportHyp : Prop where
  bound :
    ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        m / Real.sqrt (n + 1)
          ≤ |deriv HardyEstimatesPartial.hardyTheta t - Real.log (n + 1)|

/-- Support-wise branch-cut control input for `hardyTheta`: the Gamma value
stays in `Complex.slitPlane`, so `Complex.log` is differentiable along support. -/
class HardyGammaInSlitPlaneOnSupportHyp : Prop where
  inSlit :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        Complex.Gamma (1 / 4 + Complex.I * (t / 2)) ∈ Complex.slitPlane

/-- Support-wise interval-integrability input for the VdC correction integrand. -/
class HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp : Prop where
  intervalIntegrable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      IntervalIntegrable (hardyVdcCorrection n) volume
        (HardyEstimatesPartial.hardyStart n) T

lemma hardyTheta_differentiableAt_of_gamma_mem_slitPlane
    (t : ℝ)
    (hslit : Complex.Gamma (1 / 4 + Complex.I * (t / 2)) ∈ Complex.slitPlane) :
    DifferentiableAt ℝ HardyEstimatesPartial.hardyTheta t := by
  let g : ℝ → ℂ := fun x => (1 / 4 : ℂ) + Complex.I * (x / 2)
  have hg_has : HasDerivAt g (Complex.I / 2) t := by
    have hdiv : HasDerivAt (fun x : ℝ => (x / 2 : ℝ)) (1 / 2 : ℝ) t := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (hasDerivAt_id t).const_mul (1 / 2 : ℝ)
    have hdivC : HasDerivAt (fun x : ℝ => ((x / 2 : ℝ) : ℂ)) (1 / 2 : ℂ) t := by
      simpa using (HasDerivAt.ofReal_comp hdiv)
    have hmul : HasDerivAt (fun x : ℝ => Complex.I * ((x / 2 : ℝ) : ℂ))
        (Complex.I * (1 / 2 : ℂ)) t :=
      HasDerivAt.const_mul Complex.I hdivC
    simpa [g, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul

  have hGamma_diffC : DifferentiableAt ℂ Complex.Gamma (g t) := by
    refine Complex.differentiableAt_Gamma (g t) ?_
    intro m hm
    have hpos : 0 < (g t).re := by
      simp [g]
    have hneg : (-((m : ℂ))).re ≤ 0 := by
      simp
    have hEqRe : (g t).re = (-((m : ℂ))).re := by
      simpa [hm]
    linarith
  have hGamma_has : HasDerivAt (fun x : ℝ => Complex.Gamma (g x))
      ((deriv Complex.Gamma (g t)) * (Complex.I / 2)) t := by
    simpa [g] using
      (HasDerivAt.comp (x := t) (h₂ := Complex.Gamma) (h := g)
        hGamma_diffC.hasDerivAt hg_has)
  have hGammaLog_has : HasDerivAt
      (fun x : ℝ => Complex.log (Complex.Gamma (g x)))
      ((Complex.Gamma (g t))⁻¹ * ((deriv Complex.Gamma (g t)) * (Complex.I / 2))) t := by
    simpa [g] using
      (HasDerivAt.comp (x := t) (h₂ := Complex.log)
        (h := fun x : ℝ => Complex.Gamma (g x))
        (Complex.hasDerivAt_log hslit) hGamma_has)
  have hGammaLog_diff : DifferentiableAt ℝ
      (fun x : ℝ => Complex.log (Complex.Gamma (g x))) t :=
    hGammaLog_has.differentiableAt

  have hIm_diff : DifferentiableAt ℝ
      (fun x : ℝ => (Complex.log (Complex.Gamma (g x))).im) t := by
    exact (Complex.imCLM.differentiableAt).comp t hGammaLog_diff

  have hlin_diff : DifferentiableAt ℝ
      (fun x : ℝ => (x / 2) * Real.log Real.pi) t := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      ((hasDerivAt_id t).mul_const ((1 / 2 : ℝ) * Real.log Real.pi)).differentiableAt

  change DifferentiableAt ℝ
    (fun x : ℝ => (Complex.log (Complex.Gamma (1 / 4 + Complex.I * (x / 2)))).im
      - (x / 2) * Real.log Real.pi) t
  exact hIm_diff.sub hlin_diff

theorem hardyThetaDifferentiableOnSupport_of_gammaInSlitPlane
    (hslit :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          Complex.Gamma (1 / 4 + Complex.I * (t / 2)) ∈ Complex.slitPlane) :
    HardyThetaDifferentiableOnSupportHyp := by
  refine ⟨?_⟩
  intro n T hT hstart t ht
  exact hardyTheta_differentiableAt_of_gamma_mem_slitPlane t (hslit n T hT hstart t ht)

instance [HardyGammaInSlitPlaneOnSupportHyp] :
    HardyThetaDifferentiableOnSupportHyp := by
  exact hardyThetaDifferentiableOnSupport_of_gammaInSlitPlane
    HardyGammaInSlitPlaneOnSupportHyp.inSlit

lemma hardyPhaseReal_differentiableAt_of_hardyTheta
    {n : ℕ} {t : ℝ}
    (hThetaDiff : DifferentiableAt ℝ HardyEstimatesPartial.hardyTheta t) :
    DifferentiableAt ℝ (hardyPhaseReal n) t := by
  have hlin : DifferentiableAt ℝ (fun x : ℝ => x * Real.log (n + 1)) t :=
    (hasDerivAt_id t).mul_const (Real.log (n + 1)) |>.differentiableAt
  change DifferentiableAt ℝ
    (fun x : ℝ => HardyEstimatesPartial.hardyTheta x - x * Real.log (n + 1)) t
  exact hThetaDiff.sub hlin

lemma hardyPhaseReal_deriv_eq_hardyTheta_deriv_sub_log
    {n : ℕ} {t : ℝ}
    (hThetaDiff : DifferentiableAt ℝ HardyEstimatesPartial.hardyTheta t) :
    deriv (hardyPhaseReal n) t =
      deriv HardyEstimatesPartial.hardyTheta t - Real.log (n + 1) := by
  have hlinHas :
      HasDerivAt (fun x : ℝ => x * Real.log (n + 1))
        (Real.log (n + 1)) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_id t).const_mul (Real.log (n + 1))
  have hphaseHas :
      HasDerivAt (hardyPhaseReal n)
        (deriv HardyEstimatesPartial.hardyTheta t - Real.log (n + 1)) t := by
    change HasDerivAt
      (fun x : ℝ => HardyEstimatesPartial.hardyTheta x - x * Real.log (n + 1))
      (deriv HardyEstimatesPartial.hardyTheta t - Real.log (n + 1)) t
    simpa using hThetaDiff.hasDerivAt.sub hlinHas
  exact hphaseHas.deriv

theorem hardyExpPhaseDerivAbsLowerBoundOnSupport_of_hardyThetaPhaseGap
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyThetaPhaseGapLowerBoundOnSupportHyp] :
    HardyExpPhaseDerivAbsLowerBoundOnSupportHyp := by
  obtain ⟨m, hm, hgap⟩ := HardyThetaPhaseGapLowerBoundOnSupportHyp.bound
  refine ⟨m, hm, ?_⟩
  intro n T hT hstart t ht
  have hThetaDiff :
      DifferentiableAt ℝ HardyEstimatesPartial.hardyTheta t :=
    HardyThetaDifferentiableOnSupportHyp.differentiable n T hT hstart t ht
  have hderiv :
      deriv (hardyPhaseReal n) t
        = deriv HardyEstimatesPartial.hardyTheta t - Real.log (n + 1) :=
    hardyPhaseReal_deriv_eq_hardyTheta_deriv_sub_log (n := n) hThetaDiff
  simpa [hderiv] using hgap n T hT hstart t ht

instance [HardyThetaDifferentiableOnSupportHyp]
    [HardyThetaPhaseGapLowerBoundOnSupportHyp] :
    HardyExpPhaseDerivAbsLowerBoundOnSupportHyp := by
  exact hardyExpPhaseDerivAbsLowerBoundOnSupport_of_hardyThetaPhaseGap

/-- Uniform phase-gap lower bounds imply the mode-sensitive phase-gap class by
the trivial inequality `1 ≤ √(n+1)`. -/
theorem hardyThetaPhaseGapLowerSqrtModeOnSupport_of_uniform
    (hgap :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          m ≤ |deriv HardyEstimatesPartial.hardyTheta t - Real.log (n + 1)|) :
    HardyThetaPhaseGapLowerSqrtModeOnSupportHyp := by
  rcases hgap with ⟨m, hm, hbound⟩
  refine ⟨m, hm, ?_⟩
  intro n T hT hstart t ht
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (n + 1) := by
    have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simpa using (Real.sqrt_le_sqrt hbase)
  calc
    m / Real.sqrt (n + 1) ≤ m / 1 := by
      exact div_le_div_of_nonneg_left (le_of_lt hm) (by positivity) hsqrt_ge_one
    _ = m := by ring
    _ ≤ |deriv HardyEstimatesPartial.hardyTheta t - Real.log (n + 1)| :=
      hbound n T hT hstart t ht

instance [HardyThetaPhaseGapLowerBoundOnSupportHyp] :
    HardyThetaPhaseGapLowerSqrtModeOnSupportHyp := by
  exact hardyThetaPhaseGapLowerSqrtModeOnSupport_of_uniform
    HardyThetaPhaseGapLowerBoundOnSupportHyp.bound

/-- Mode-sensitive phase-gap bounds transfer to mode-sensitive lower bounds on
`|deriv (hardyPhaseReal n)|`. -/
theorem hardyExpPhaseDerivAbsLowerSqrtModeOnSupport_of_hardyThetaPhaseGapSqrtMode
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyThetaPhaseGapLowerSqrtModeOnSupportHyp] :
    HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp := by
  obtain ⟨m, hm, hgap⟩ := HardyThetaPhaseGapLowerSqrtModeOnSupportHyp.bound
  refine ⟨m, hm, ?_⟩
  intro n T hT hstart t ht
  have hThetaDiff :
      DifferentiableAt ℝ HardyEstimatesPartial.hardyTheta t :=
    HardyThetaDifferentiableOnSupportHyp.differentiable n T hT hstart t ht
  have hderiv :
      deriv (hardyPhaseReal n) t
        = deriv HardyEstimatesPartial.hardyTheta t - Real.log (n + 1) :=
    hardyPhaseReal_deriv_eq_hardyTheta_deriv_sub_log (n := n) hThetaDiff
  simpa [hderiv] using hgap n T hT hstart t ht

instance [HardyThetaDifferentiableOnSupportHyp]
    [HardyThetaPhaseGapLowerSqrtModeOnSupportHyp] :
    HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp := by
  exact
    hardyExpPhaseDerivAbsLowerSqrtModeOnSupport_of_hardyThetaPhaseGapSqrtMode

lemma hardyVdcPrimitive_differentiableAt_of_phase
    {n : ℕ} {t : ℝ}
    (hPhaseDiff : DifferentiableAt ℝ (hardyPhaseReal n) t)
    (hPhaseDerivDiff : DifferentiableAt ℝ (deriv (fun x : ℝ => hardyPhaseReal n x)) t)
    (hPhaseDerivNe : deriv (fun x : ℝ => hardyPhaseReal n x) t ≠ 0) :
    DifferentiableAt ℝ (hardyVdcPrimitive n) t := by
  have hPhaseHas : HasDerivAt (fun x : ℝ => hardyPhaseReal n x)
      (deriv (fun x : ℝ => hardyPhaseReal n x) t) t :=
    hPhaseDiff.hasDerivAt
  have hPhaseHasC : HasDerivAt (fun x : ℝ => (hardyPhaseReal n x : ℂ))
      (((deriv (fun x : ℝ => hardyPhaseReal n x) t : ℝ) : ℂ)) t :=
    HasDerivAt.ofReal_comp hPhaseHas
  have hArgHas : HasDerivAt (fun x : ℝ => Complex.I * (hardyPhaseReal n x : ℂ))
      (Complex.I * (((deriv (fun x : ℝ => hardyPhaseReal n x) t : ℝ) : ℂ))) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (HasDerivAt.mul (hasDerivAt_const t Complex.I) hPhaseHasC)
  have hNumHas : HasDerivAt
      (fun x : ℝ => Complex.exp (Complex.I * (hardyPhaseReal n x : ℂ)))
      (Complex.exp (Complex.I * (hardyPhaseReal n t : ℂ)) *
        (Complex.I * (((deriv (fun x : ℝ => hardyPhaseReal n x) t : ℝ) : ℂ)))) t :=
    HasDerivAt.comp t (Complex.hasDerivAt_exp _) hArgHas

  have hDerivHas : HasDerivAt (fun x : ℝ => deriv (fun y : ℝ => hardyPhaseReal n y) x)
      (deriv (fun x : ℝ => deriv (fun y : ℝ => hardyPhaseReal n y) x) t) t :=
    hPhaseDerivDiff.hasDerivAt
  have hDerivHasC : HasDerivAt
      (fun x : ℝ => ((deriv (fun y : ℝ => hardyPhaseReal n y) x : ℝ) : ℂ))
      (((deriv (fun x : ℝ => deriv (fun y : ℝ => hardyPhaseReal n y) x) t : ℝ) : ℂ)) t :=
    HasDerivAt.ofReal_comp hDerivHas
  have hDenHas : HasDerivAt
      (fun x : ℝ => Complex.I * ((deriv (fun y : ℝ => hardyPhaseReal n y) x : ℝ) : ℂ))
      (Complex.I * (((deriv (fun x : ℝ => deriv (fun y : ℝ => hardyPhaseReal n y) x) t : ℝ) : ℂ)))
      t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (HasDerivAt.mul (hasDerivAt_const t Complex.I) hDerivHasC)

  have hDenNe : Complex.I * ((deriv (fun x : ℝ => hardyPhaseReal n x) t : ℝ) : ℂ) ≠ 0 := by
    refine mul_ne_zero Complex.I_ne_zero ?_
    exact_mod_cast hPhaseDerivNe

  have hDiff : DifferentiableAt ℝ
      (fun x : ℝ => Complex.exp (Complex.I * (hardyPhaseReal n x : ℂ)) /
        (Complex.I * ((deriv (fun y : ℝ => hardyPhaseReal n y) x : ℝ) : ℂ))) t :=
    hNumHas.differentiableAt.div hDenHas.differentiableAt hDenNe
  change DifferentiableAt ℝ
    (fun x : ℝ => Complex.exp (Complex.I * hardyPhaseReal n x) /
      (Complex.I * deriv (hardyPhaseReal n) x)) t
  simpa using hDiff

theorem hardyExpPhaseVdcPhaseCalculusOnSupport_of_hardyTheta
    (hThetaDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ HardyEstimatesPartial.hardyTheta t)
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t)
    (hPhaseDerivNe :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          deriv (hardyPhaseReal n) t ≠ 0) :
    HardyExpPhaseVdcPhaseCalculusOnSupportHyp := by
  refine ⟨?_, hPhaseDerivDiff, hPhaseDerivNe⟩
  intro n T hT hstart t ht
  exact hardyPhaseReal_differentiableAt_of_hardyTheta
    (hThetaDiff n T hT hstart t ht)

theorem hardyExpPhaseVdcPhaseCalculusOnSupport_of_hardyTheta_and_derivLower
    (hThetaDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ HardyEstimatesPartial.hardyTheta t)
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t)
    (hDerivLower :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          m ≤ |deriv (hardyPhaseReal n) t|) :
    HardyExpPhaseVdcPhaseCalculusOnSupportHyp := by
  rcases hDerivLower with ⟨m, hm, hbound⟩
  refine hardyExpPhaseVdcPhaseCalculusOnSupport_of_hardyTheta
    hThetaDiff hPhaseDerivDiff ?_
  intro n T hT hstart t ht
  have habs_pos : 0 < |deriv (hardyPhaseReal n) t| := lt_of_lt_of_le hm (hbound n T hT hstart t ht)
  exact (abs_pos.mp habs_pos)

instance [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp] :
    HardyExpPhaseVdcPhaseCalculusOnSupportHyp := by
  exact hardyExpPhaseVdcPhaseCalculusOnSupport_of_hardyTheta_and_derivLower
    HardyThetaDifferentiableOnSupportHyp.differentiable
    HardyPhaseDerivDifferentiableOnSupportHyp.differentiable
    HardyExpPhaseDerivAbsLowerBoundOnSupportHyp.bound

/-- Mode-sensitive lower bounds on `|phase'|` are also enough to produce the
nonvanishing side-condition in the VdC phase-calculus package. -/
theorem hardyExpPhaseVdcPhaseCalculusOnSupport_of_hardyTheta_and_derivLowerSqrtMode
    (hThetaDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ HardyEstimatesPartial.hardyTheta t)
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t)
    (hDerivLower :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          m / Real.sqrt (n + 1) ≤ |deriv (hardyPhaseReal n) t|) :
    HardyExpPhaseVdcPhaseCalculusOnSupportHyp := by
  rcases hDerivLower with ⟨m, hm, hbound⟩
  refine hardyExpPhaseVdcPhaseCalculusOnSupport_of_hardyTheta
    hThetaDiff hPhaseDerivDiff ?_
  intro n T hT hstart t ht
  have hsqrt_pos : 0 < Real.sqrt (n + 1) := by positivity
  have hdiv_pos : 0 < m / Real.sqrt (n + 1) := div_pos hm hsqrt_pos
  have habs_pos : 0 < |deriv (hardyPhaseReal n) t| :=
    lt_of_lt_of_le hdiv_pos (hbound n T hT hstart t ht)
  exact (abs_pos.mp habs_pos)

instance (priority := 900) [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp] :
    HardyExpPhaseVdcPhaseCalculusOnSupportHyp := by
  exact
    hardyExpPhaseVdcPhaseCalculusOnSupport_of_hardyTheta_and_derivLowerSqrtMode
      HardyThetaDifferentiableOnSupportHyp.differentiable
      HardyPhaseDerivDifferentiableOnSupportHyp.differentiable
      HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp.bound

theorem hardyExpPhaseVdcPrimitiveCorrectionOnSupport_of_phase_and_correction
    (hPhaseDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (hardyPhaseReal n) t)
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t)
    (hPhaseDerivNe :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          deriv (hardyPhaseReal n) t ≠ 0)
    (hCorrectionInt :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        IntervalIntegrable (hardyVdcCorrection n) volume
          (HardyEstimatesPartial.hardyStart n) T) :
    HardyExpPhaseVdcPrimitiveCorrectionOnSupportHyp := by
  refine ⟨?_, hCorrectionInt⟩
  intro n T hT hstart t ht
  exact hardyVdcPrimitive_differentiableAt_of_phase
    (hPhaseDiff n T hT hstart t ht)
    (hPhaseDerivDiff n T hT hstart t ht)
    (hPhaseDerivNe n T hT hstart t ht)

instance [HardyExpPhaseVdcPhaseCalculusOnSupportHyp]
    [HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp] :
    HardyExpPhaseVdcPrimitiveCorrectionOnSupportHyp := by
  exact hardyExpPhaseVdcPrimitiveCorrectionOnSupport_of_phase_and_correction
    HardyExpPhaseVdcPhaseCalculusOnSupportHyp.phaseDifferentiable
    HardyExpPhaseVdcPhaseCalculusOnSupportHyp.phaseDerivDifferentiable
    HardyExpPhaseVdcPhaseCalculusOnSupportHyp.phaseDerivNonzero
    HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp.intervalIntegrable

lemma hardyVdcPrimitive_norm_le_inv_of_phaseDerivAbsLower_onInterval
    {n : ℕ} {a b : ℝ} {m : ℝ} (hm : 0 < m)
    (hderivLower :
      ∀ t ∈ Set.uIcc a b,
        m ≤ |deriv (hardyPhaseReal n) t|)
    {t : ℝ} (ht : t ∈ Set.uIcc a b) :
    ‖hardyVdcPrimitive n t‖ ≤ 1 / m := by
  have hderivBound : m ≤ ‖Complex.I * deriv (hardyPhaseReal n) t‖ := by
    calc
      m ≤ |deriv (hardyPhaseReal n) t| := hderivLower t ht
      _ = ‖Complex.I * deriv (hardyPhaseReal n) t‖ := by
            simp
  calc
    ‖hardyVdcPrimitive n t‖
        = ‖Complex.exp (Complex.I * hardyPhaseReal n t)‖
            / ‖Complex.I * deriv (hardyPhaseReal n) t‖ := by
              simp [hardyVdcPrimitive]
    _ = 1 / ‖Complex.I * deriv (hardyPhaseReal n) t‖ := by simp
    _ ≤ 1 / m := by
          exact one_div_le_one_div_of_le hm hderivBound

lemma hardyVdcPrimitive_norm_le_inv_of_phaseDerivAbsLower
    {n : ℕ} {T : ℝ}
    {m : ℝ} (hm : 0 < m)
    (hderivLower :
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        m ≤ |deriv (hardyPhaseReal n) t|)
    {t : ℝ} (ht : t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T) :
    ‖hardyVdcPrimitive n t‖ ≤ 1 / m := by
  exact hardyVdcPrimitive_norm_le_inv_of_phaseDerivAbsLower_onInterval
    (n := n) (a := HardyEstimatesPartial.hardyStart n) (b := T)
    hm hderivLower ht

theorem hardyExpPhaseVdcEndpointBoundOnSupport_of_phaseDerivAbsLower
    (hderivLower :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          m ≤ |deriv (hardyPhaseReal n) t|) :
    HardyExpPhaseVdcEndpointBoundOnSupportHyp := by
  rcases hderivLower with ⟨m, hm, hbound⟩
  refine ⟨2 / m, by positivity, ?_⟩
  intro n T hT hstart
  have hTmem : T ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T := by
    simpa [Set.uIcc_of_le hstart]
  have hStartMem :
      HardyEstimatesPartial.hardyStart n ∈
        Set.uIcc (HardyEstimatesPartial.hardyStart n) T := by
    simpa [Set.uIcc_of_le hstart]
  have hprimT :
      ‖hardyVdcPrimitive n T‖ ≤ 1 / m :=
    hardyVdcPrimitive_norm_le_inv_of_phaseDerivAbsLower
      (n := n) (T := T) hm (hbound n T hT hstart) hTmem
  have hprimStart :
      ‖hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖ ≤ 1 / m :=
    hardyVdcPrimitive_norm_le_inv_of_phaseDerivAbsLower
      (n := n) (T := T) hm (hbound n T hT hstart) hStartMem
  calc
    ‖hardyVdcPrimitive n T
      - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖
        ≤ ‖hardyVdcPrimitive n T‖
            + ‖hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖ := by
              exact norm_sub_le _ _
    _ ≤ 1 / m + 1 / m := add_le_add hprimT hprimStart
    _ = 2 / m := by ring

instance [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp] :
    HardyExpPhaseVdcEndpointBoundOnSupportHyp := by
  exact hardyExpPhaseVdcEndpointBoundOnSupport_of_phaseDerivAbsLower
    HardyExpPhaseDerivAbsLowerBoundOnSupportHyp.bound

/-- Uniform phase-derivative lower bounds imply the mode-sensitive lower-bound
class by the trivial inequality `1 ≤ √(n+1)`. -/
theorem hardyExpPhaseDerivAbsLowerSqrtModeOnSupport_of_uniform
    (hderivLower :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          m ≤ |deriv (hardyPhaseReal n) t|) :
    HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp := by
  rcases hderivLower with ⟨m, hm, hbound⟩
  refine ⟨m, hm, ?_⟩
  intro n T hT hstart t ht
  have hsqrt_pos : 0 < Real.sqrt (n + 1) := by
    positivity
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (n + 1) := by
    have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simpa using (Real.sqrt_le_sqrt hbase)
  calc
    m / Real.sqrt (n + 1) ≤ m / 1 := by
        exact div_le_div_of_nonneg_left (le_of_lt hm) (by positivity) hsqrt_ge_one
    _ = m := by ring
    _ ≤ |deriv (hardyPhaseReal n) t| := hbound n T hT hstart t ht

instance [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp] :
    HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp := by
  exact hardyExpPhaseDerivAbsLowerSqrtModeOnSupport_of_uniform
    HardyExpPhaseDerivAbsLowerBoundOnSupportHyp.bound

/-- Mode-sensitive derivative lower bounds imply a mode-sensitive endpoint bound
for the VdC primitive on support. -/
theorem hardyExpPhaseVdcEndpointSqrtModeBoundOnSupport_of_phaseDerivAbsLowerSqrtMode
    (hderivLower :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          m / Real.sqrt (n + 1) ≤ |deriv (hardyPhaseReal n) t|) :
    HardyExpPhaseVdcEndpointSqrtModeBoundOnSupportHyp := by
  rcases hderivLower with ⟨m, hm, hbound⟩
  refine ⟨2 / m, by positivity, ?_⟩
  intro n T hT hstart
  have hsqrt_pos : 0 < Real.sqrt (n + 1) := by
    positivity
  have hTmem : T ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T := by
    simpa [Set.uIcc_of_le hstart]
  have hStartMem :
      HardyEstimatesPartial.hardyStart n ∈
        Set.uIcc (HardyEstimatesPartial.hardyStart n) T := by
    simpa [Set.uIcc_of_le hstart]
  have hprimT :
      ‖hardyVdcPrimitive n T‖ ≤ 1 / (m / Real.sqrt (n + 1)) :=
    hardyVdcPrimitive_norm_le_inv_of_phaseDerivAbsLower
      (n := n) (T := T) (div_pos hm hsqrt_pos) (hbound n T hT hstart) hTmem
  have hprimStart :
      ‖hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖
        ≤ 1 / (m / Real.sqrt (n + 1)) :=
    hardyVdcPrimitive_norm_le_inv_of_phaseDerivAbsLower
      (n := n) (T := T) (div_pos hm hsqrt_pos) (hbound n T hT hstart) hStartMem
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have hsqrt_ne : Real.sqrt (n + 1) ≠ 0 := ne_of_gt hsqrt_pos
  calc
    ‖hardyVdcPrimitive n T
      - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖
        ≤ ‖hardyVdcPrimitive n T‖
            + ‖hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖ := by
              exact norm_sub_le _ _
    _ ≤ 1 / (m / Real.sqrt (n + 1)) + 1 / (m / Real.sqrt (n + 1)) := add_le_add hprimT hprimStart
    _ = 2 / (m / Real.sqrt (n + 1)) := by ring
    _ = (2 / m) * Real.sqrt (n + 1) := by
          field_simp [hm_ne, hsqrt_ne]

instance [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp] :
    HardyExpPhaseVdcEndpointSqrtModeBoundOnSupportHyp := by
  exact hardyExpPhaseVdcEndpointSqrtModeBoundOnSupport_of_phaseDerivAbsLowerSqrtMode
    HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp.bound

/-- Uniform VdC correction bounds imply the mode-sensitive correction class by
the trivial inequality `1 ≤ √(n+1)`. -/
theorem hardyExpPhaseVdcCorrectionSqrtModeBoundOnSupport_of_uniform
    (hcor :
      ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖ ≤ B₁) :
    HardyExpPhaseVdcCorrectionSqrtModeBoundOnSupportHyp := by
  rcases hcor with ⟨B₁, hB₁, hbound⟩
  refine ⟨B₁, hB₁, ?_⟩
  intro n T hT hstart
  calc
    ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖
        ≤ B₁ := hbound n T hT hstart
    _ = B₁ * 1 := by ring
    _ ≤ B₁ * Real.sqrt (n + 1) := by
        have hB₁nn : 0 ≤ B₁ := le_of_lt hB₁
        have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (n + 1) := by
          have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          simpa using (Real.sqrt_le_sqrt hbase)
        exact mul_le_mul_of_nonneg_left hsqrt_ge_one hB₁nn

instance [HardyExpPhaseVdcCorrectionBoundOnSupportHyp] :
    HardyExpPhaseVdcCorrectionSqrtModeBoundOnSupportHyp := by
  exact hardyExpPhaseVdcCorrectionSqrtModeBoundOnSupport_of_uniform
    HardyExpPhaseVdcCorrectionBoundOnSupportHyp.bound

/-- Pointwise `t^(-3/2)` decay of the VdC correction term implies support-wise
interval-integrability on every finite support interval. -/
theorem hardyExpPhaseVdcCorrectionIntervalIntegrableOnSupport_of_pointwiseDecay
    [HardyExpPhaseVdcCorrectionPointwiseDecayOnSupportHyp] :
    HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp := by
  obtain ⟨B₁, hB₁, hDecay⟩ := HardyExpPhaseVdcCorrectionPointwiseDecayOnSupportHyp.bound
  refine ⟨?_⟩
  intro n T hT hstart
  have hStart_pos : 0 < HardyEstimatesPartial.hardyStart n := by
    unfold HardyEstimatesPartial.hardyStart
    positivity
  have hPowInt :
      IntervalIntegrable
        (fun t : ℝ => B₁ / t ^ (3 / 2 : ℝ))
        volume (HardyEstimatesPartial.hardyStart n) T := by
    refine (continuousOn_of_forall_continuousAt ?_).intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n) T := by
      simpa [Set.uIcc_of_le hstart] using ht
    have ht_pos : 0 < t := lt_of_lt_of_le hStart_pos ht'.1
    have ht_ne : t ^ (3 / 2 : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.rpow_pos_of_pos ht_pos _)
    exact ContinuousAt.div continuousAt_const
      (ContinuousAt.rpow continuousAt_id continuousAt_const (Or.inr (by norm_num)))
      ht_ne
  have hPowOn :
      IntegrableOn (fun t : ℝ => B₁ / t ^ (3 / 2 : ℝ))
        (Set.Icc (HardyEstimatesPartial.hardyStart n) T) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hstart).1 hPowInt
  have hMeasDerivInv :
      Measurable (fun t : ℝ =>
        deriv (fun x => 1 / (Complex.I * deriv (hardyPhaseReal n) x)) t) := by
    simpa using
      (measurable_deriv
        (fun x : ℝ => 1 / (Complex.I * deriv (hardyPhaseReal n) x)))
  have hMeasCorr : Measurable (hardyVdcCorrection n) := by
    unfold hardyVdcCorrection
    exact (hardyExpPhase_continuous n).measurable.mul hMeasDerivInv
  have hCorrOn :
      IntegrableOn (hardyVdcCorrection n)
        (Set.Icc (HardyEstimatesPartial.hardyStart n) T) volume := by
    refine MeasureTheory.Integrable.mono' hPowOn hMeasCorr.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    exact hDecay n T hT hstart t (by simpa [Set.uIcc_of_le hstart] using ht)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hstart).2 hCorrOn

theorem hardyExpPhaseVdcCorrectionNormIntegralBoundOnSupport_of_pointwiseDecay
    [HardyExpPhaseVdcCorrectionPointwiseDecayOnSupportHyp]
    [HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp] :
    HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp := by
  refine ⟨?_, ?_⟩
  · intro n T hT hstart
    exact HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp.intervalIntegrable n T hT hstart
  obtain ⟨B₁, hB₁, hDecay⟩ := HardyExpPhaseVdcCorrectionPointwiseDecayOnSupportHyp.bound
  refine ⟨B₁ * Real.sqrt 2, mul_pos hB₁ (Real.sqrt_pos.2 (by norm_num)), ?_⟩
  intro n T hT hstart
  have hCorrInt :
      IntervalIntegrable (hardyVdcCorrection n) volume
        (HardyEstimatesPartial.hardyStart n) T :=
    HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp.intervalIntegrable n T hT hstart
  have hNormInt :
      IntervalIntegrable (fun t => ‖hardyVdcCorrection n t‖) volume
        (HardyEstimatesPartial.hardyStart n) T :=
    hCorrInt.norm
  have hStart_pos : 0 < HardyEstimatesPartial.hardyStart n := by
    unfold HardyEstimatesPartial.hardyStart
    positivity
  have hPowInt :
      IntervalIntegrable
        (fun t : ℝ => B₁ / t ^ (3 / 2 : ℝ))
        volume (HardyEstimatesPartial.hardyStart n) T := by
    refine (continuousOn_of_forall_continuousAt ?_).intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n) T := by
      simpa [Set.uIcc_of_le hstart] using ht
    have ht_pos : 0 < t := lt_of_lt_of_le hStart_pos ht'.1
    have ht_ne : t ^ (3 / 2 : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.rpow_pos_of_pos ht_pos _)
    exact ContinuousAt.div continuousAt_const
      (ContinuousAt.rpow continuousAt_id continuousAt_const (Or.inr (by norm_num)))
      ht_ne
  have hMono :
      ∫ t in HardyEstimatesPartial.hardyStart n..T, ‖hardyVdcCorrection n t‖
        ≤ ∫ t in HardyEstimatesPartial.hardyStart n..T, B₁ / t ^ (3 / 2 : ℝ) := by
    refine intervalIntegral.integral_mono_on hstart hNormInt hPowInt ?_
    intro t ht
    exact hDecay n T hT hstart t (by simpa [Set.uIcc_of_le hstart] using ht)
  have hConstMul :
      ∫ t in HardyEstimatesPartial.hardyStart n..T, B₁ / t ^ (3 / 2 : ℝ)
        = B₁ * ∫ t in HardyEstimatesPartial.hardyStart n..T, t ^ (-(3 / 2 : ℝ)) := by
    calc
      ∫ t in HardyEstimatesPartial.hardyStart n..T, B₁ / t ^ (3 / 2 : ℝ)
          = ∫ t in HardyEstimatesPartial.hardyStart n..T, B₁ * t ^ (-(3 / 2 : ℝ)) := by
              refine intervalIntegral.integral_congr ?_
              intro t ht
              have ht' : t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n) T := by
                simpa [Set.uIcc_of_le hstart] using ht
              have ht_pos : 0 < t := lt_of_lt_of_le hStart_pos ht'.1
              have hrpow :
                  t ^ (-(3 / 2 : ℝ)) = (t ^ (3 / 2 : ℝ))⁻¹ :=
                Real.rpow_neg (le_of_lt ht_pos) (3 / 2 : ℝ)
              calc
                B₁ / t ^ (3 / 2 : ℝ) = B₁ * (t ^ (3 / 2 : ℝ))⁻¹ := by
                  rw [div_eq_mul_inv]
                _ = B₁ * t ^ (-(3 / 2 : ℝ)) := by
                  rw [← hrpow]
      _ = B₁ * ∫ t in HardyEstimatesPartial.hardyStart n..T, t ^ (-(3 / 2 : ℝ)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (intervalIntegral.integral_const_mul B₁
                (fun t : ℝ => t ^ (-(3 / 2 : ℝ)))
                (a := HardyEstimatesPartial.hardyStart n) (b := T))
  have hNoZero :
      (0 : ℝ) ∉ Set.uIcc (HardyEstimatesPartial.hardyStart n) T := by
    intro hz
    have hz' : (0 : ℝ) ∈ Set.Icc (HardyEstimatesPartial.hardyStart n) T := by
      simpa [Set.uIcc_of_le hstart] using hz
    exact (not_le_of_gt hStart_pos) hz'.1
  have hRpowRaw :
      ∫ t in HardyEstimatesPartial.hardyStart n..T, t ^ (-(3 / 2 : ℝ))
        = (T ^ ((-(3 / 2 : ℝ)) + 1)
            - (HardyEstimatesPartial.hardyStart n) ^ ((-(3 / 2 : ℝ)) + 1))
            / ((-(3 / 2 : ℝ)) + 1) := by
    simpa using
      (integral_rpow
        (a := HardyEstimatesPartial.hardyStart n)
        (b := T)
        (r := (-(3 / 2 : ℝ)))
        (Or.inr ⟨by norm_num, hNoZero⟩))
  have hExp : ((-(3 / 2 : ℝ)) + 1) = (-(1 / 2 : ℝ)) := by ring
  have hRpow :
      ∫ t in HardyEstimatesPartial.hardyStart n..T, t ^ (-(3 / 2 : ℝ))
        = (T ^ (-(1 / 2 : ℝ))
            - (HardyEstimatesPartial.hardyStart n) ^ (-(1 / 2 : ℝ)))
            / (-(1 / 2 : ℝ)) := by
    simpa [hExp] using hRpowRaw
  have hRpow_le :
      ∫ t in HardyEstimatesPartial.hardyStart n..T, t ^ (-(3 / 2 : ℝ))
        ≤ Real.sqrt 2 := by
    have hT_nonneg : 0 ≤ T := le_trans (by norm_num : (0 : ℝ) ≤ 2) hT
    have h_nonneg_tail : 0 ≤ T ^ (-(1 / 2 : ℝ)) := by
      exact Real.rpow_nonneg hT_nonneg (-(1 / 2 : ℝ))
    have h_calc :
        (T ^ (-(1 / 2 : ℝ))
            - (HardyEstimatesPartial.hardyStart n) ^ (-(1 / 2 : ℝ)))
            / (-(1 / 2 : ℝ))
          = 2 * ((HardyEstimatesPartial.hardyStart n) ^ (-(1 / 2 : ℝ))
              - T ^ (-(1 / 2 : ℝ))) := by
      ring
    have h_step :
        2 * ((HardyEstimatesPartial.hardyStart n) ^ (-(1 / 2 : ℝ))
              - T ^ (-(1 / 2 : ℝ)))
          ≤ 2 * (HardyEstimatesPartial.hardyStart n) ^ (-(1 / 2 : ℝ)) := by
      nlinarith [h_nonneg_tail]
    have hStart_ge_two : (2 : ℝ) ≤ HardyEstimatesPartial.hardyStart n := by
      have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
      have hsq : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      unfold HardyEstimatesPartial.hardyStart
      nlinarith [Real.pi_gt_three, hsq]
    have hSqrtMono :
        Real.sqrt (2 : ℝ) ≤ Real.sqrt (HardyEstimatesPartial.hardyStart n) :=
      Real.sqrt_le_sqrt hStart_ge_two
    have hInvMono :
        (Real.sqrt (HardyEstimatesPartial.hardyStart n))⁻¹ ≤ (Real.sqrt (2 : ℝ))⁻¹ := by
      simpa [one_div] using
        (one_div_le_one_div_of_le (Real.sqrt_pos.2 (by norm_num)) hSqrtMono)
    have hStartInv :
        (HardyEstimatesPartial.hardyStart n) ^ (-(1 / 2 : ℝ))
          = (Real.sqrt (HardyEstimatesPartial.hardyStart n))⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hStart_pos)]
      rw [Real.sqrt_eq_rpow]
    have hTwoInv :
        (2 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (2 : ℝ))⁻¹ := by
      rw [Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [Real.sqrt_eq_rpow]
    have hStartPow :
        (HardyEstimatesPartial.hardyStart n) ^ (-(1 / 2 : ℝ))
          ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc
        (HardyEstimatesPartial.hardyStart n) ^ (-(1 / 2 : ℝ))
            = (Real.sqrt (HardyEstimatesPartial.hardyStart n))⁻¹ := hStartInv
        _ ≤ (Real.sqrt (2 : ℝ))⁻¹ := hInvMono
        _ = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by simpa using hTwoInv.symm
    have hTwoOver :
        2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt 2 := by
      have h2pos : 0 < (2 : ℝ) := by norm_num
      calc
        2 * (2 : ℝ) ^ (-(1 / 2 : ℝ))
            = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by norm_num
        _ = (2 : ℝ) ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := by
              rw [← Real.rpow_add h2pos (1 : ℝ) (-(1 / 2 : ℝ))]
        _ = (2 : ℝ) ^ (1 / 2 : ℝ) := by ring_nf
        _ = Real.sqrt 2 := by rw [Real.sqrt_eq_rpow]
    calc
      ∫ t in HardyEstimatesPartial.hardyStart n..T, t ^ (-(3 / 2 : ℝ))
          = (T ^ (-(1 / 2 : ℝ))
              - (HardyEstimatesPartial.hardyStart n) ^ (-(1 / 2 : ℝ)))
              / (-(1 / 2 : ℝ)) := hRpow
      _ = 2 * ((HardyEstimatesPartial.hardyStart n) ^ (-(1 / 2 : ℝ))
            - T ^ (-(1 / 2 : ℝ))) := h_calc
      _ ≤ 2 * (HardyEstimatesPartial.hardyStart n) ^ (-(1 / 2 : ℝ)) := h_step
      _ ≤ 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
            gcongr
      _ = Real.sqrt 2 := hTwoOver
  calc
    ∫ t in HardyEstimatesPartial.hardyStart n..T, ‖hardyVdcCorrection n t‖
        ≤ ∫ t in HardyEstimatesPartial.hardyStart n..T, B₁ / t ^ (3 / 2 : ℝ) := hMono
    _ = B₁ * ∫ t in HardyEstimatesPartial.hardyStart n..T, t ^ (-(3 / 2 : ℝ)) := hConstMul
    _ ≤ B₁ * Real.sqrt 2 := by
          exact mul_le_mul_of_nonneg_left hRpow_le (le_of_lt hB₁)

instance [HardyExpPhaseVdcCorrectionPointwiseDecayOnSupportHyp]
    [HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp] :
    HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp := by
  exact hardyExpPhaseVdcCorrectionNormIntegralBoundOnSupport_of_pointwiseDecay

/-- Three analytic inputs (phase-derivative lower bound, differentiability of
`phase'`, and second-derivative decay) are enough to recover the correction
`L¹` package. Interval-integrability is discharged via the pointwise decay
bound. -/
theorem hardyExpPhaseVdcCorrectionNormIntegralBoundOnSupport_of_derivLower_secondDeriv
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp := by
  let _ : HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp :=
    hardyExpPhaseVdcCorrectionIntervalIntegrableOnSupport_of_pointwiseDecay
  infer_instance

instance (priority := 900) [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp := by
  exact hardyExpPhaseVdcCorrectionNormIntegralBoundOnSupport_of_derivLower_secondDeriv

/-- Convenience assembly: second-derivative decay + derivative lower bound
yield pointwise decay of the inverse-derivative factor, and with interval
integrability this upgrades to the full correction `L¹` bound class. -/
instance [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp] :
    HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp := by
  infer_instance

instance [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp] :
    HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp := by
  exact ⟨HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp.intervalIntegrable⟩

theorem hardyExpPhaseVdcCorrectionBoundOnSupport_of_normIntegral
    (hcor :
      ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∫ t in HardyEstimatesPartial.hardyStart n..T, ‖hardyVdcCorrection n t‖ ≤ B₁) :
    HardyExpPhaseVdcCorrectionBoundOnSupportHyp := by
  rcases hcor with ⟨B₁, hB₁, hbound⟩
  refine ⟨B₁, hB₁, ?_⟩
  intro n T hT hstart
  calc
    ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖
        ≤ ∫ t in HardyEstimatesPartial.hardyStart n..T, ‖hardyVdcCorrection n t‖ := by
              simpa using intervalIntegral.norm_integral_le_integral_norm
                (f := fun t => hardyVdcCorrection n t) hstart
    _ ≤ B₁ := hbound n T hT hstart

instance [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp] :
    HardyExpPhaseVdcCorrectionBoundOnSupportHyp := by
  exact hardyExpPhaseVdcCorrectionBoundOnSupport_of_normIntegral
    HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp.bound

lemma hardyVdcPrimitive_deriv_eq_phase_plus_correction_onInterval
    {n : ℕ} {a b : ℝ}
    (hPhaseDiff :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ (hardyPhaseReal n) t)
    (hPhaseDerivDiff :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t)
    (hPhaseDerivNe :
      ∀ t ∈ Set.uIcc a b,
        deriv (hardyPhaseReal n) t ≠ 0) :
    ∀ t ∈ Set.uIcc a b,
      deriv (hardyVdcPrimitive n) t = hardyExpPhase n t + hardyVdcCorrection n t := by
  intro t ht
  have haux :=
    Aristotle.VanDerCorput.van_der_corput_deriv_aux
      (f := hardyPhaseReal n) (t := t)
      (hPhaseDiff t ht)
      (hPhaseDerivDiff t ht)
      (hPhaseDerivNe t ht)
  simpa [hardyVdcPrimitive, hardyVdcCorrection, hardyExpPhase_eq_exp_phase,
    mul_assoc, mul_comm, mul_left_comm] using haux

lemma hardyVdcPrimitive_derivIntervalIntegrable_onInterval_of_phase_and_correction
    {n : ℕ} {a b : ℝ}
    (hPhaseDiff :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ (hardyPhaseReal n) t)
    (hPhaseDerivDiff :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t)
    (hPhaseDerivNe :
      ∀ t ∈ Set.uIcc a b,
        deriv (hardyPhaseReal n) t ≠ 0)
    (hCorrectionInt :
      IntervalIntegrable (hardyVdcCorrection n) volume a b) :
    IntervalIntegrable (deriv (hardyVdcPrimitive n)) volume a b := by
  have hDerivEq := hardyVdcPrimitive_deriv_eq_phase_plus_correction_onInterval
    (n := n) (a := a) (b := b) hPhaseDiff hPhaseDerivDiff hPhaseDerivNe
  have hExpInt : IntervalIntegrable (hardyExpPhase n) volume a b :=
    hardyExpPhase_intervalIntegrable n a b
  have hSumInt :
      IntervalIntegrable (fun t => hardyExpPhase n t + hardyVdcCorrection n t) volume a b :=
    hExpInt.add hCorrectionInt
  exact hSumInt.congr (fun t ht => by
    have htIcc : t ∈ Set.uIcc a b := ⟨le_of_lt ht.1, ht.2⟩
    simpa using (hDerivEq t htIcc).symm)

lemma hardyVdcPrimitive_deriv_eq_phase_plus_correction
    (hPhaseDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (hardyPhaseReal n) t)
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t)
    (hPhaseDerivNe :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          deriv (hardyPhaseReal n) t ≠ 0) :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
        deriv (hardyVdcPrimitive n) t = hardyExpPhase n t + hardyVdcCorrection n t := by
  intro n T hT hstart t ht
  exact hardyVdcPrimitive_deriv_eq_phase_plus_correction_onInterval
    (n := n) (a := HardyEstimatesPartial.hardyStart n) (b := T)
    (hPhaseDiff n T hT hstart)
    (hPhaseDerivDiff n T hT hstart)
    (hPhaseDerivNe n T hT hstart) t ht

theorem hardyVdcPrimitive_derivIntervalIntegrable_onSupport_of_phase_and_correction
    (hPhaseDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (hardyPhaseReal n) t)
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t)
    (hPhaseDerivNe :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          deriv (hardyPhaseReal n) t ≠ 0)
    (hCorrectionInt :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        IntervalIntegrable (hardyVdcCorrection n) volume
          (HardyEstimatesPartial.hardyStart n) T) :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      IntervalIntegrable (deriv (hardyVdcPrimitive n)) volume
        (HardyEstimatesPartial.hardyStart n) T := by
  intro n T hT hstart
  have hDerivEq := hardyVdcPrimitive_deriv_eq_phase_plus_correction
    hPhaseDiff hPhaseDerivDiff hPhaseDerivNe
  have hExpInt :
      IntervalIntegrable (hardyExpPhase n) volume
        (HardyEstimatesPartial.hardyStart n) T :=
    hardyExpPhase_intervalIntegrable n _ _
  have hSumInt :
      IntervalIntegrable (fun t => hardyExpPhase n t + hardyVdcCorrection n t) volume
        (HardyEstimatesPartial.hardyStart n) T :=
    hExpInt.add (hCorrectionInt n T hT hstart)
  exact hardyVdcPrimitive_derivIntervalIntegrable_onInterval_of_phase_and_correction
    (n := n) (a := HardyEstimatesPartial.hardyStart n) (b := T)
    (hPhaseDiff n T hT hstart)
    (hPhaseDerivDiff n T hT hstart)
    (hPhaseDerivNe n T hT hstart)
    (hCorrectionInt n T hT hstart)

theorem hardyExpPhaseVdcCalculusOnSupport_of_phase_primitive_correction
    (hPhaseDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (hardyPhaseReal n) t)
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t)
    (hPhaseDerivNe :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          deriv (hardyPhaseReal n) t ≠ 0)
    (hPrimitiveDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (hardyVdcPrimitive n) t)
    (hCorrectionInt :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        IntervalIntegrable (hardyVdcCorrection n) volume
          (HardyEstimatesPartial.hardyStart n) T) :
    HardyExpPhaseVdcCalculusOnSupportHyp := by
  refine ⟨hPhaseDiff, hPhaseDerivDiff, hPhaseDerivNe, hPrimitiveDiff, ?_, ?_, hCorrectionInt⟩
  · exact hardyVdcPrimitive_derivIntervalIntegrable_onSupport_of_phase_and_correction
      hPhaseDiff hPhaseDerivDiff hPhaseDerivNe hCorrectionInt
  · intro n T hT hstart
    exact hardyExpPhase_intervalIntegrable n _ _

instance [HardyExpPhaseVdcPhaseCalculusOnSupportHyp]
    [HardyExpPhaseVdcPrimitiveCorrectionOnSupportHyp] :
    HardyExpPhaseVdcCalculusOnSupportHyp := by
  exact hardyExpPhaseVdcCalculusOnSupport_of_phase_primitive_correction
    HardyExpPhaseVdcPhaseCalculusOnSupportHyp.phaseDifferentiable
    HardyExpPhaseVdcPhaseCalculusOnSupportHyp.phaseDerivDifferentiable
    HardyExpPhaseVdcPhaseCalculusOnSupportHyp.phaseDerivNonzero
    HardyExpPhaseVdcPrimitiveCorrectionOnSupportHyp.primitiveDifferentiable
    HardyExpPhaseVdcPrimitiveCorrectionOnSupportHyp.correctionIntervalIntegrable

/-- VdC decomposition identity on an arbitrary compact interval `[a,b]`.
This is the interval-local form used by the stationary-tail route. -/
theorem hardyExpPhase_vdc_decomposition_onInterval_of_calculus
    {n : ℕ} {a b : ℝ}
    (hDerivEq :
      ∀ t ∈ Set.uIcc a b,
        deriv (hardyVdcPrimitive n) t = hardyExpPhase n t + hardyVdcCorrection n t)
    (hPrimitiveDiff :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ (hardyVdcPrimitive n) t)
    (hPrimitiveDerivInt :
      IntervalIntegrable (deriv (hardyVdcPrimitive n)) volume a b)
    (hExpInt :
      IntervalIntegrable (hardyExpPhase n) volume a b)
    (hCorrectionInt :
      IntervalIntegrable (hardyVdcCorrection n) volume a b) :
    ∫ t in a..b, hardyExpPhase n t =
      (hardyVdcPrimitive n b - hardyVdcPrimitive n a)
        - ∫ t in a..b, hardyVdcCorrection n t := by
  have hIntDeriv :
      ∫ t in a..b, deriv (hardyVdcPrimitive n) t
        = hardyVdcPrimitive n b - hardyVdcPrimitive n a := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun t ht => hPrimitiveDiff t ht)
      hPrimitiveDerivInt
  have hAdd :
      (∫ t in a..b, hardyExpPhase n t)
        + (∫ t in a..b, hardyVdcCorrection n t)
        = hardyVdcPrimitive n b - hardyVdcPrimitive n a := by
    calc
      (∫ t in a..b, hardyExpPhase n t)
          + (∫ t in a..b, hardyVdcCorrection n t)
          = ∫ t in a..b, (hardyExpPhase n t + hardyVdcCorrection n t) := by
              symm
              exact intervalIntegral.integral_add hExpInt hCorrectionInt
      _ = ∫ t in a..b, deriv (hardyVdcPrimitive n) t := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            symm
            exact hDerivEq t ht
      _ = hardyVdcPrimitive n b - hardyVdcPrimitive n a := hIntDeriv
  exact (eq_sub_iff_add_eq).2 hAdd

theorem hardyExpPhase_vdc_decomposition_onSupport_of_calculus
    (hDerivEq :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          deriv (hardyVdcPrimitive n) t = hardyExpPhase n t + hardyVdcCorrection n t)
    (hPrimitiveDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (hardyVdcPrimitive n) t)
    (hPrimitiveDerivInt :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        IntervalIntegrable (deriv (hardyVdcPrimitive n)) volume
          (HardyEstimatesPartial.hardyStart n) T)
    (hExpInt :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        IntervalIntegrable (hardyExpPhase n) volume (HardyEstimatesPartial.hardyStart n) T)
    (hCorrectionInt :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        IntervalIntegrable (hardyVdcCorrection n) volume
          (HardyEstimatesPartial.hardyStart n) T) :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t =
        (hardyVdcPrimitive n T
          - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n))
          - ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t := by
  intro n T hT hstart
  have hIntDeriv :
      ∫ t in HardyEstimatesPartial.hardyStart n..T, deriv (hardyVdcPrimitive n) t
        = hardyVdcPrimitive n T
          - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n) := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun t ht => hPrimitiveDiff n T hT hstart t ht)
      (hPrimitiveDerivInt n T hT hstart)
  have hAdd :
      (∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t)
        + (∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t)
        = hardyVdcPrimitive n T
          - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n) := by
    calc
      (∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t)
          + (∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t)
          = ∫ t in HardyEstimatesPartial.hardyStart n..T,
              (hardyExpPhase n t + hardyVdcCorrection n t) := by
                symm
                exact intervalIntegral.integral_add
                  (hExpInt n T hT hstart) (hCorrectionInt n T hT hstart)
      _ = ∫ t in HardyEstimatesPartial.hardyStart n..T, deriv (hardyVdcPrimitive n) t := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            symm
            exact hDerivEq n T hT hstart t ht
      _ = hardyVdcPrimitive n T
            - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n) := hIntDeriv
  exact (eq_sub_iff_add_eq).2 hAdd

/-- Van der Corput-style decomposition data on the nonempty support range.
This isolates the remaining analytic obligations needed to bound
`∫ hardyExpPhase`. -/
class HardyExpPhaseVdcOnSupportHyp : Prop where
  endpointBound :
    ∃ B₀ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ‖hardyVdcPrimitive n T
        - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖ ≤ B₀
  correctionBound :
    ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖ ≤ B₁
  decomposition :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t =
        (hardyVdcPrimitive n T
          - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n))
          - ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t

/-- Mode-sensitive VdC package on support:
endpoint and correction controls are allowed to grow like `√(n+1)`. -/
class HardyExpPhaseVdcSqrtModeOnSupportHyp : Prop where
  endpointBound :
    ∃ B₀ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ‖hardyVdcPrimitive n T
        - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖
          ≤ B₀ * Real.sqrt (n + 1)
  correctionBound :
    ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖
        ≤ B₁ * Real.sqrt (n + 1)
  decomposition :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t =
        (hardyVdcPrimitive n T
          - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n))
          - ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t

/-- Tail-localized mode-sensitive VdC package on the support complement of the
stationary window. This avoids requiring phase-derivative lower bounds all the
way down to `hardyStart n`. -/
class HardyExpPhaseVdcSqrtModeOnTailSupportHyp : Prop where
  endpointBound :
    ∃ B₀ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ‖hardyVdcPrimitive n T
        - hardyVdcPrimitive n
            (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))‖
          ≤ B₀ * Real.sqrt (n + 1)
  correctionBound :
    ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ‖∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
          hardyVdcCorrection n t‖ ≤ B₁ * Real.sqrt (n + 1)
  decomposition :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
          hardyExpPhase n t =
        (hardyVdcPrimitive n T
          - hardyVdcPrimitive n
              (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)))
          - ∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
              hardyVdcCorrection n t

/-- Tail-localized phase-side calculus assumptions for VdC, restricted to
`[hardyStart n + √(n+1), T]`. -/
class HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp : Prop where
  phaseDifferentiable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ∀ t ∈ Set.uIcc
        (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T,
        DifferentiableAt ℝ (hardyPhaseReal n) t
  phaseDerivDifferentiable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ∀ t ∈ Set.uIcc
        (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T,
        DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t

/-- Tail-localized mode-sensitive lower bound for `|phase'|`. -/
class HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp : Prop where
  bound :
    ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ∀ t ∈ Set.uIcc
        (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T,
        m / Real.sqrt (n + 1) ≤ |deriv (hardyPhaseReal n) t|

/-- Tail-localized second-derivative decay input for the Hardy phase.
This is the stationary-phase side used to control the VdC correction term on
`[hardyStart n + √(n+1), T]`. -/
class HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp : Prop where
  bound :
    ∃ M > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ∀ t ∈ Set.uIcc
        (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T,
        |deriv (deriv (hardyPhaseReal n)) t| ≤ M / t ^ (3 / 2 : ℝ)

/-- Tail-localized branch-cut control input for `hardyTheta`: the Gamma value
stays in `Complex.slitPlane` on the stationary-window complement. -/
class HardyGammaInSlitPlaneOnTailSupportHyp : Prop where
  inSlit :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ∀ t ∈ Set.uIcc
        (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T,
        Complex.Gamma (1 / 4 + Complex.I * (t / 2)) ∈ Complex.slitPlane

/-- Tail-localized differentiability input for `hardyTheta`. -/
class HardyThetaDifferentiableOnTailSupportHyp : Prop where
  differentiable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ∀ t ∈ Set.uIcc
        (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T,
        DifferentiableAt ℝ HardyEstimatesPartial.hardyTheta t

/-- Tail-localized differentiability input for `deriv (hardyPhaseReal n)`. -/
class HardyPhaseDerivDifferentiableOnTailSupportHyp : Prop where
  differentiable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ∀ t ∈ Set.uIcc
        (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T,
        DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t

/-- Restrict support-level branch-cut control on `hardyTheta` to the
stationary tail. -/
theorem hardyGammaInSlitPlaneOnTailSupport_of_support
    [HardyGammaInSlitPlaneOnSupportHyp] :
    HardyGammaInSlitPlaneOnTailSupportHyp := by
  refine ⟨?_⟩
  intro n T hT htail t ht
  let c : ℝ := HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)
  have hstart : HardyEstimatesPartial.hardyStart n ≤ T := by
    exact le_trans
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      htail
  have hstartC : HardyEstimatesPartial.hardyStart n ≤ c := by
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have htTailIcc : t ∈ Set.Icc c T := by
    simpa [Set.uIcc_of_le htail, c] using ht
  have htSupport :
      t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T := by
    have htSupportIcc : t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n) T := by
      exact ⟨le_trans hstartC htTailIcc.1, htTailIcc.2⟩
    simpa [Set.uIcc_of_le hstart] using htSupportIcc
  exact
    HardyGammaInSlitPlaneOnSupportHyp.inSlit
      n T hT hstart t htSupport

instance [HardyGammaInSlitPlaneOnSupportHyp] :
    HardyGammaInSlitPlaneOnTailSupportHyp := by
  exact hardyGammaInSlitPlaneOnTailSupport_of_support

/-- Tail-localized `hardyTheta` differentiability from tail-localized slit-plane
control of the Gamma input. -/
theorem hardyThetaDifferentiableOnTailSupport_of_gammaInSlitPlane
    (hslit :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.uIcc
          (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T,
          Complex.Gamma (1 / 4 + Complex.I * (t / 2)) ∈ Complex.slitPlane) :
    HardyThetaDifferentiableOnTailSupportHyp := by
  refine ⟨?_⟩
  intro n T hT htail t ht
  exact hardyTheta_differentiableAt_of_gamma_mem_slitPlane t (hslit n T hT htail t ht)

instance [HardyGammaInSlitPlaneOnTailSupportHyp] :
    HardyThetaDifferentiableOnTailSupportHyp := by
  exact hardyThetaDifferentiableOnTailSupport_of_gammaInSlitPlane
    HardyGammaInSlitPlaneOnTailSupportHyp.inSlit

/-- Restrict support-level `hardyTheta` differentiability to the stationary
tail. -/
theorem hardyThetaDifferentiableOnTailSupport_of_support
    [HardyThetaDifferentiableOnSupportHyp] :
    HardyThetaDifferentiableOnTailSupportHyp := by
  refine ⟨?_⟩
  intro n T hT htail t ht
  let c : ℝ := HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)
  have hstart : HardyEstimatesPartial.hardyStart n ≤ T := by
    exact le_trans
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      htail
  have hstartC : HardyEstimatesPartial.hardyStart n ≤ c := by
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have htTailIcc : t ∈ Set.Icc c T := by
    simpa [Set.uIcc_of_le htail, c] using ht
  have htSupport :
      t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T := by
    have htSupportIcc : t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n) T := by
      exact ⟨le_trans hstartC htTailIcc.1, htTailIcc.2⟩
    simpa [Set.uIcc_of_le hstart] using htSupportIcc
  exact
    HardyThetaDifferentiableOnSupportHyp.differentiable
      n T hT hstart t htSupport

instance [HardyThetaDifferentiableOnSupportHyp] :
    HardyThetaDifferentiableOnTailSupportHyp := by
  exact hardyThetaDifferentiableOnTailSupport_of_support

/-- Restrict support-level differentiability of `deriv (hardyPhaseReal n)` to
the stationary tail. -/
theorem hardyPhaseDerivDifferentiableOnTailSupport_of_support
    [HardyPhaseDerivDifferentiableOnSupportHyp] :
    HardyPhaseDerivDifferentiableOnTailSupportHyp := by
  refine ⟨?_⟩
  intro n T hT htail t ht
  let c : ℝ := HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)
  have hstart : HardyEstimatesPartial.hardyStart n ≤ T := by
    exact le_trans
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      htail
  have hstartC : HardyEstimatesPartial.hardyStart n ≤ c := by
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have htTailIcc : t ∈ Set.Icc c T := by
    simpa [Set.uIcc_of_le htail, c] using ht
  have htSupport :
      t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T := by
    have htSupportIcc : t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n) T := by
      exact ⟨le_trans hstartC htTailIcc.1, htTailIcc.2⟩
    simpa [Set.uIcc_of_le hstart] using htSupportIcc
  exact
    HardyPhaseDerivDifferentiableOnSupportHyp.differentiable
      n T hT hstart t htSupport

instance [HardyPhaseDerivDifferentiableOnSupportHyp] :
    HardyPhaseDerivDifferentiableOnTailSupportHyp := by
  exact hardyPhaseDerivDifferentiableOnTailSupport_of_support

/-- Build the tail-localized phase-calculus package directly from tail-localized
`hardyTheta` and `phase'` differentiability hypotheses. -/
theorem hardyExpPhaseVdcPhaseCalculusOnTailSupport_of_hardyThetaTail_classes
    [HardyThetaDifferentiableOnTailSupportHyp]
    [HardyPhaseDerivDifferentiableOnTailSupportHyp] :
    HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp := by
  refine ⟨?_, ?_⟩
  · intro n T hT htail t ht
    exact hardyPhaseReal_differentiableAt_of_hardyTheta
      (n := n)
      (HardyThetaDifferentiableOnTailSupportHyp.differentiable
        n T hT htail t ht)
  · intro n T hT htail t ht
    exact
      HardyPhaseDerivDifferentiableOnTailSupportHyp.differentiable
        n T hT htail t ht

instance (priority := 850) [HardyThetaDifferentiableOnTailSupportHyp]
    [HardyPhaseDerivDifferentiableOnTailSupportHyp] :
    HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp := by
  exact hardyExpPhaseVdcPhaseCalculusOnTailSupport_of_hardyThetaTail_classes

/-- Restrict support-level phase calculus hypotheses to the stationary tail. -/
theorem hardyExpPhaseVdcPhaseCalculusOnTailSupport_of_support
    [HardyExpPhaseVdcPhaseCalculusOnSupportHyp] :
    HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp := by
  refine ⟨?_, ?_⟩
  · intro n T hT htail t ht
    let c : ℝ := HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)
    have hstart : HardyEstimatesPartial.hardyStart n ≤ T := by
      exact le_trans
        (le_add_of_nonneg_right (Real.sqrt_nonneg _))
        htail
    have hstartC : HardyEstimatesPartial.hardyStart n ≤ c := by
      exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    have htTailIcc : t ∈ Set.Icc c T := by
      simpa [Set.uIcc_of_le htail, c] using ht
    have htSupport :
        t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T := by
      have htSupportIcc : t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n) T := by
        exact ⟨le_trans hstartC htTailIcc.1, htTailIcc.2⟩
      simpa [Set.uIcc_of_le hstart] using htSupportIcc
    exact
      HardyExpPhaseVdcPhaseCalculusOnSupportHyp.phaseDifferentiable
        n T hT hstart t htSupport
  · intro n T hT htail t ht
    let c : ℝ := HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)
    have hstart : HardyEstimatesPartial.hardyStart n ≤ T := by
      exact le_trans
        (le_add_of_nonneg_right (Real.sqrt_nonneg _))
        htail
    have hstartC : HardyEstimatesPartial.hardyStart n ≤ c := by
      exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    have htTailIcc : t ∈ Set.Icc c T := by
      simpa [Set.uIcc_of_le htail, c] using ht
    have htSupport :
        t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T := by
      have htSupportIcc : t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n) T := by
        exact ⟨le_trans hstartC htTailIcc.1, htTailIcc.2⟩
      simpa [Set.uIcc_of_le hstart] using htSupportIcc
    exact
      HardyExpPhaseVdcPhaseCalculusOnSupportHyp.phaseDerivDifferentiable
        n T hT hstart t htSupport

instance [HardyExpPhaseVdcPhaseCalculusOnSupportHyp] :
    HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp := by
  exact hardyExpPhaseVdcPhaseCalculusOnTailSupport_of_support

/-- Restrict support-level mode-sensitive derivative lower bounds to the
stationary tail. -/
theorem hardyExpPhaseDerivAbsLowerSqrtModeOnTailSupport_of_support
    [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp] :
    HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp := by
  obtain ⟨m, hm, hbound⟩ := HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp.bound
  refine ⟨m, hm, ?_⟩
  intro n T hT htail t ht
  let c : ℝ := HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)
  have hstart : HardyEstimatesPartial.hardyStart n ≤ T := by
    exact le_trans
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      htail
  have hstartC : HardyEstimatesPartial.hardyStart n ≤ c := by
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have htTailIcc : t ∈ Set.Icc c T := by
    simpa [Set.uIcc_of_le htail, c] using ht
  have htSupport :
      t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T := by
    have htSupportIcc : t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n) T := by
      exact ⟨le_trans hstartC htTailIcc.1, htTailIcc.2⟩
    simpa [Set.uIcc_of_le hstart] using htSupportIcc
  exact hbound n T hT hstart t htSupport

instance [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp] :
    HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp := by
  exact hardyExpPhaseDerivAbsLowerSqrtModeOnTailSupport_of_support

/-- Restrict support-level second-derivative decay to the stationary tail. -/
theorem hardyExpPhaseSecondDerivAbsBoundOnTailSupport_of_support
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp := by
  obtain ⟨M, hM, hbound⟩ := HardyExpPhaseSecondDerivAbsBoundOnSupportHyp.bound
  refine ⟨M, hM, ?_⟩
  intro n T hT htail t ht
  let c : ℝ := HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)
  have hstart : HardyEstimatesPartial.hardyStart n ≤ T := by
    exact le_trans
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      htail
  have hstartC : HardyEstimatesPartial.hardyStart n ≤ c := by
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have htTailIcc : t ∈ Set.Icc c T := by
    simpa [Set.uIcc_of_le htail, c] using ht
  have htSupport :
      t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T := by
    have htSupportIcc : t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n) T := by
      exact ⟨le_trans hstartC htTailIcc.1, htTailIcc.2⟩
    simpa [Set.uIcc_of_le hstart] using htSupportIcc
  exact hbound n T hT hstart t htSupport

instance [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp := by
  exact hardyExpPhaseSecondDerivAbsBoundOnTailSupport_of_support

/-- Tail-localized correction `L¹` package at `√(n+1)` scale. -/
class HardyExpPhaseVdcCorrectionNormIntegralSqrtModeOnTailSupportHyp : Prop where
  intervalIntegrable :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      IntervalIntegrable (hardyVdcCorrection n) volume
        (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T
  bound :
    ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
        ‖hardyVdcCorrection n t‖ ≤ B₁ * Real.sqrt (n + 1)

/-- Tail endpoint `√(n+1)` bound from tail derivative lower bounds. -/
theorem hardyExpPhaseVdcEndpointSqrtModeOnTailSupport_of_phaseDerivAbsLowerSqrtMode
    (hderivLower :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.uIcc
          (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T,
          m / Real.sqrt (n + 1) ≤ |deriv (hardyPhaseReal n) t|) :
    ∃ B₀ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
      ‖hardyVdcPrimitive n T
        - hardyVdcPrimitive n
            (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))‖
        ≤ B₀ * Real.sqrt (n + 1) := by
  rcases hderivLower with ⟨m, hm, hbound⟩
  refine ⟨2 / m, by positivity, ?_⟩
  intro n T hT htail
  let c : ℝ := HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)
  have hsqrt_pos : 0 < Real.sqrt (n + 1) := by positivity
  have hTmem : T ∈ Set.uIcc c T := by
    simpa [Set.uIcc_of_le htail, c]
  have hcmem : c ∈ Set.uIcc c T := by
    simpa [Set.uIcc_of_le htail]
  have hprimT :
      ‖hardyVdcPrimitive n T‖ ≤ 1 / (m / Real.sqrt (n + 1)) :=
    hardyVdcPrimitive_norm_le_inv_of_phaseDerivAbsLower_onInterval
      (n := n) (a := c) (b := T) (m := m / Real.sqrt (n + 1))
      (div_pos hm hsqrt_pos) (hbound n T hT htail) hTmem
  have hprimC :
      ‖hardyVdcPrimitive n c‖ ≤ 1 / (m / Real.sqrt (n + 1)) :=
    hardyVdcPrimitive_norm_le_inv_of_phaseDerivAbsLower_onInterval
      (n := n) (a := c) (b := T) (m := m / Real.sqrt (n + 1))
      (div_pos hm hsqrt_pos) (hbound n T hT htail) hcmem
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have hsqrt_ne : Real.sqrt (n + 1) ≠ 0 := ne_of_gt hsqrt_pos
  calc
    ‖hardyVdcPrimitive n T
      - hardyVdcPrimitive n
          (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))‖
        = ‖hardyVdcPrimitive n T - hardyVdcPrimitive n c‖ := by
            simp [c]
    _ ≤ ‖hardyVdcPrimitive n T‖ + ‖hardyVdcPrimitive n c‖ := by
          exact norm_sub_le _ _
    _ ≤ 1 / (m / Real.sqrt (n + 1)) + 1 / (m / Real.sqrt (n + 1)) := by
          exact add_le_add hprimT hprimC
    _ = 2 / (m / Real.sqrt (n + 1)) := by ring
    _ = (2 / m) * Real.sqrt (n + 1) := by
          field_simp [hm_ne, hsqrt_ne]

/-- Pointwise derivative-inverse bound used in the tail correction estimate. -/
lemma hardyVdcCorrectionDerivInv_norm_le_of_derivLower_secondDeriv_at
    {n : ℕ} {t m M : ℝ}
    (hm : 0 < m)
    (hDerivLower_t : m ≤ |deriv (hardyPhaseReal n) t|)
    (hPhaseDerivDiff_t : DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t)
    (hSecond_t : |deriv (deriv (hardyPhaseReal n)) t| ≤ M / t ^ (3 / 2 : ℝ)) :
    ‖deriv (fun x => 1 / (Complex.I * deriv (hardyPhaseReal n) x)) t‖
      ≤ (M / m ^ 2) / t ^ (3 / 2 : ℝ) := by
  let den : ℝ → ℂ := fun x : ℝ => Complex.I * ((deriv (hardyPhaseReal n) x : ℝ) : ℂ)
  let g : ℝ → ℂ := (fun _ : ℝ => (1 : ℂ)) / den
  change ‖deriv g t‖ ≤ (M / m ^ 2) / t ^ (3 / 2 : ℝ)
  have hDerivNe : deriv (hardyPhaseReal n) t ≠ 0 := by
    have hAbsPos : 0 < |deriv (hardyPhaseReal n) t| := lt_of_lt_of_le hm hDerivLower_t
    exact abs_ne_zero.mp (ne_of_gt hAbsPos)
  have hDerivHas :
      HasDerivAt (fun x : ℝ => deriv (hardyPhaseReal n) x)
        (deriv (deriv (hardyPhaseReal n)) t) t :=
    hPhaseDerivDiff_t.hasDerivAt
  have hDerivHasC :
      HasDerivAt
        (fun x : ℝ => ((deriv (hardyPhaseReal n) x : ℝ) : ℂ))
        (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ)) t :=
    HasDerivAt.ofReal_comp hDerivHas
  have hDenHas :
      HasDerivAt den
        (Complex.I * (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ))) t := by
    simpa [den, mul_assoc, mul_comm, mul_left_comm] using
      (HasDerivAt.mul (hasDerivAt_const t Complex.I) hDerivHasC)
  have hDenNe : den t ≠ 0 := by
    refine mul_ne_zero Complex.I_ne_zero ?_
    exact_mod_cast hDerivNe
  have hInvHas :
      HasDerivAt g
        (-(Complex.I * (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ))) /
          (Complex.I * ((deriv (hardyPhaseReal n) t : ℝ) : ℂ)) ^ 2) t := by
    simpa [g, den] using (HasDerivAt.div (hasDerivAt_const t (1 : ℂ)) hDenHas hDenNe)
  have hDerivEq :
      deriv g t =
        (-(Complex.I * (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ))) /
          (Complex.I * ((deriv (hardyPhaseReal n) t : ℝ) : ℂ)) ^ 2) := by
    simpa using hInvHas.deriv
  have hDenLower :
      m ≤ ‖Complex.I * ((deriv (hardyPhaseReal n) t : ℝ) : ℂ)‖ := by
    simpa using hDerivLower_t
  have hDenSqLower :
      m ^ 2 ≤ ‖Complex.I * ((deriv (hardyPhaseReal n) t : ℝ) : ℂ)‖ ^ 2 := by
    nlinarith [hDenLower]
  have hNumBound' :
      ‖((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ)‖ ≤ M / t ^ (3 / 2 : ℝ) := by
    simpa using hSecond_t
  have hNumBound :
      ‖Complex.I * (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ))‖
        ≤ M / t ^ (3 / 2 : ℝ) := by
    simpa [norm_mul] using hNumBound'
  calc
    ‖deriv g t‖
        = ‖Complex.I * (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ))‖
            / ‖Complex.I * ((deriv (hardyPhaseReal n) t : ℝ) : ℂ)‖ ^ 2 := by
              rw [hDerivEq, norm_div, norm_neg, norm_pow]
    _ ≤ ‖Complex.I * (((deriv (deriv (hardyPhaseReal n)) t : ℝ) : ℂ))‖ / m ^ 2 := by
          refine div_le_div_of_nonneg_left ?_ ?_ hDenSqLower
          · exact norm_nonneg _
          · exact sq_pos_of_pos hm
    _ ≤ (M / t ^ (3 / 2 : ℝ)) / m ^ 2 := by
          exact div_le_div_of_nonneg_right hNumBound (sq_nonneg m)
    _ = (M / m ^ 2) / t ^ (3 / 2 : ℝ) := by
          ring

/-- Quantitative tail integral bound for `t^(-3/2)`:
when `c` is at least `4 (n+1)^2`, the integral over `[c, T]` is at most
`1/(n+1)`. -/
lemma hardyIntegral_rpow_negThreeHalves_tail_le_inv_mode
    {n : ℕ} {c T : ℝ}
    (hct : c ≤ T)
    (hc_pos : 0 < c)
    (hmode : (4 : ℝ) * ((n + 1 : ℝ) ^ (2 : ℕ)) ≤ c) :
    ∫ t in c..T, t ^ (-(3 / 2 : ℝ)) ≤ 1 / (n + 1 : ℝ) := by
  have hNoZero : (0 : ℝ) ∉ Set.uIcc c T := by
    intro hz
    have hz' : (0 : ℝ) ∈ Set.Icc c T := by
      simpa [Set.uIcc_of_le hct] using hz
    exact (not_le_of_gt hc_pos) hz'.1
  have hRpow :
      ∫ t in c..T, t ^ (-(3 / 2 : ℝ))
        = (T ^ (-(1 / 2 : ℝ)) - c ^ (-(1 / 2 : ℝ))) / (-(1 / 2 : ℝ)) := by
    have hRpowRaw :
        ∫ t in c..T, t ^ (-(3 / 2 : ℝ))
          = (T ^ ((-(3 / 2 : ℝ)) + 1) - c ^ ((-(3 / 2 : ℝ)) + 1))
              / ((-(3 / 2 : ℝ)) + 1) := by
      simpa using
        (integral_rpow (a := c) (b := T) (r := (-(3 / 2 : ℝ)))
          (Or.inr ⟨by norm_num, hNoZero⟩))
    have hExp : ((-(3 / 2 : ℝ)) + 1) = (-(1 / 2 : ℝ)) := by ring
    simpa [hExp] using hRpowRaw
  have hT_nonneg : 0 ≤ T := le_trans (le_of_lt hc_pos) hct
  have hTpow_nonneg : 0 ≤ T ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hT_nonneg _
  have hCalc :
      (T ^ (-(1 / 2 : ℝ)) - c ^ (-(1 / 2 : ℝ))) / (-(1 / 2 : ℝ))
        = 2 * (c ^ (-(1 / 2 : ℝ)) - T ^ (-(1 / 2 : ℝ))) := by
    ring
  have hStep :
      2 * (c ^ (-(1 / 2 : ℝ)) - T ^ (-(1 / 2 : ℝ)))
        ≤ 2 * c ^ (-(1 / 2 : ℝ)) := by
    nlinarith [hTpow_nonneg]
  have hcInv :
      c ^ (-(1 / 2 : ℝ)) = (Real.sqrt c)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hc_pos)]
    rw [Real.sqrt_eq_rpow]
  have hModeSqrt :
      2 * (n + 1 : ℝ) ≤ Real.sqrt c := by
    have hModeSqrt' :
        Real.sqrt ((4 : ℝ) * ((n + 1 : ℝ) ^ (2 : ℕ))) ≤ Real.sqrt c :=
      Real.sqrt_le_sqrt hmode
    have hSqrtFour :
        Real.sqrt ((4 : ℝ) * ((n + 1 : ℝ) ^ (2 : ℕ)))
          = 2 * (n + 1 : ℝ) := by
      calc
        Real.sqrt ((4 : ℝ) * ((n + 1 : ℝ) ^ (2 : ℕ)))
            = Real.sqrt ((2 * (n + 1 : ℝ)) ^ (2 : ℕ)) := by ring_nf
        _ = |2 * (n + 1 : ℝ)| := by rw [Real.sqrt_sq_eq_abs]
        _ = 2 * (n + 1 : ℝ) := by
              exact abs_of_nonneg (by positivity)
    simpa [hSqrtFour] using hModeSqrt'
  have hInvLe : 1 / Real.sqrt c ≤ 1 / (2 * (n + 1 : ℝ)) := by
    exact one_div_le_one_div_of_le (by positivity) hModeSqrt
  have hTwoInv :
      2 * (Real.sqrt c)⁻¹ ≤ 2 * (2 * (n + 1 : ℝ))⁻¹ := by
    have hMul :
        2 * (1 / Real.sqrt c) ≤ 2 * (1 / (2 * (n + 1 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hInvLe (by norm_num : (0 : ℝ) ≤ 2)
    simpa [one_div] using hMul
  have hTwoInvEq :
      2 * (2 * (n + 1 : ℝ))⁻¹ = 1 / (n + 1 : ℝ) := by
    field_simp [show (n + 1 : ℝ) ≠ 0 by positivity]
  calc
    ∫ t in c..T, t ^ (-(3 / 2 : ℝ))
        = (T ^ (-(1 / 2 : ℝ)) - c ^ (-(1 / 2 : ℝ))) / (-(1 / 2 : ℝ)) := hRpow
    _ = 2 * (c ^ (-(1 / 2 : ℝ)) - T ^ (-(1 / 2 : ℝ))) := hCalc
    _ ≤ 2 * c ^ (-(1 / 2 : ℝ)) := hStep
    _ = 2 * (Real.sqrt c)⁻¹ := by rw [hcInv]
    _ ≤ 2 * (2 * (n + 1 : ℝ))⁻¹ := hTwoInv
    _ = 1 / (n + 1 : ℝ) := hTwoInvEq

/-- Tail correction `L¹` control from tail second-derivative decay and
mode-sensitive lower bounds on `|phase'|`. -/
theorem hardyExpPhaseVdcCorrectionNormIntegralSqrtModeOnTailSupport_of_derivLowerSqrt_secondDeriv
    [HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    HardyExpPhaseVdcCorrectionNormIntegralSqrtModeOnTailSupportHyp := by
  obtain ⟨m, hm, hDerivLower⟩ := HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp.bound
  obtain ⟨M, hM, hSecond⟩ := HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp.bound
  have hCorrIntTail :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
        IntervalIntegrable (hardyVdcCorrection n) volume
          (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T := by
    intro n T hT htail
    let c : ℝ := HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)
    let Cn : ℝ := (M / m ^ 2) * (n + 1)
    have hstart_pos : 0 < HardyEstimatesPartial.hardyStart n := by
      unfold HardyEstimatesPartial.hardyStart
      positivity
    have hc_pos : 0 < c := by
      exact lt_of_lt_of_le hstart_pos (le_add_of_nonneg_right (Real.sqrt_nonneg _))
    have hPowInt :
        IntervalIntegrable (fun t : ℝ => Cn / t ^ (3 / 2 : ℝ)) volume c T := by
      refine (continuousOn_of_forall_continuousAt ?_).intervalIntegrable
      intro t ht
      have ht' : t ∈ Set.Icc c T := by
        simpa [Set.uIcc_of_le htail, c] using ht
      have ht_pos : 0 < t := lt_of_lt_of_le hc_pos ht'.1
      have ht_ne : t ^ (3 / 2 : ℝ) ≠ 0 := by
        exact ne_of_gt (Real.rpow_pos_of_pos ht_pos _)
      exact ContinuousAt.div continuousAt_const
        (ContinuousAt.rpow continuousAt_id continuousAt_const (Or.inr (by norm_num)))
        ht_ne
    have hPowOn :
        IntegrableOn (fun t : ℝ => Cn / t ^ (3 / 2 : ℝ)) (Set.Icc c T) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le htail).1 hPowInt
    have hMeasDerivInv :
        Measurable (fun t : ℝ =>
          deriv (fun x => 1 / (Complex.I * deriv (hardyPhaseReal n) x)) t) := by
      simpa using
        (measurable_deriv
          (fun x : ℝ => 1 / (Complex.I * deriv (hardyPhaseReal n) x)))
    have hMeasCorr : Measurable (hardyVdcCorrection n) := by
      unfold hardyVdcCorrection
      exact (hardyExpPhase_continuous n).measurable.mul hMeasDerivInv
    have hCorrOn :
        IntegrableOn (hardyVdcCorrection n) (Set.Icc c T) volume := by
      refine MeasureTheory.Integrable.mono' hPowOn hMeasCorr.aestronglyMeasurable ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
      have hDerivLower_t :
          m / Real.sqrt (n + 1) ≤ |deriv (hardyPhaseReal n) t| :=
        hDerivLower n T hT htail t (by simpa [Set.uIcc_of_le htail, c] using ht)
      have hPhaseDerivDiff_t :
          DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t :=
        HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp.phaseDerivDifferentiable
          n T hT htail t (by simpa [Set.uIcc_of_le htail, c] using ht)
      have hSecond_t :
          |deriv (deriv (hardyPhaseReal n)) t| ≤ M / t ^ (3 / 2 : ℝ) :=
        hSecond n T hT htail t (by simpa [Set.uIcc_of_le htail, c] using ht)
      have hsqrt_pos : 0 < Real.sqrt (n + 1) := by positivity
      have hDerivInv_t :
          ‖deriv (fun x => 1 / (Complex.I * deriv (hardyPhaseReal n) x)) t‖
            ≤ ((M / m ^ 2) * (n + 1)) / t ^ (3 / 2 : ℝ) := by
        have hRaw :=
          hardyVdcCorrectionDerivInv_norm_le_of_derivLower_secondDeriv_at
            (n := n) (t := t) (m := m / Real.sqrt (n + 1)) (M := M)
            (div_pos hm hsqrt_pos) hDerivLower_t hPhaseDerivDiff_t hSecond_t
        have hm_ne : m ≠ 0 := ne_of_gt hm
        have hsqrt_ne : Real.sqrt (n + 1) ≠ 0 := ne_of_gt hsqrt_pos
        have hsqrt_sq : Real.sqrt (n + 1) ^ (2 : ℕ) = (n + 1 : ℝ) := by
          have hn1_nonneg : 0 ≤ (n + 1 : ℝ) := by positivity
          nlinarith [Real.sq_sqrt hn1_nonneg]
        calc
          ‖deriv (fun x => 1 / (Complex.I * deriv (hardyPhaseReal n) x)) t‖
              ≤ (M / (m / Real.sqrt (n + 1)) ^ 2) / t ^ (3 / 2 : ℝ) := hRaw
          _ = ((M / m ^ 2) * (Real.sqrt (n + 1) ^ (2 : ℕ))) / t ^ (3 / 2 : ℝ) := by
                field_simp [hm_ne, hsqrt_ne]
          _ = ((M / m ^ 2) * (n + 1)) / t ^ (3 / 2 : ℝ) := by rw [hsqrt_sq]
      simpa [c, Cn, hardyVdcCorrection_norm_eq_derivInv_norm] using hDerivInv_t
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le htail).2 hCorrOn
  refine ⟨hCorrIntTail, ?_⟩
  refine ⟨M / m ^ 2, div_pos hM (sq_pos_of_pos hm), ?_⟩
  intro n T hT htail
  let c : ℝ := HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)
  let Cn : ℝ := (M / m ^ 2) * (n + 1)
  have hCorrInt :
      IntervalIntegrable (hardyVdcCorrection n) volume c T := by
    simpa [c] using hCorrIntTail n T hT htail
  have hNormInt :
      IntervalIntegrable (fun t => ‖hardyVdcCorrection n t‖) volume c T := hCorrInt.norm
  have hstart_pos : 0 < HardyEstimatesPartial.hardyStart n := by
    unfold HardyEstimatesPartial.hardyStart
    positivity
  have hc_pos : 0 < c := by
    exact lt_of_lt_of_le hstart_pos (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hPowInt :
      IntervalIntegrable (fun t : ℝ => Cn / t ^ (3 / 2 : ℝ)) volume c T := by
    refine (continuousOn_of_forall_continuousAt ?_).intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.Icc c T := by
      simpa [Set.uIcc_of_le htail, c] using ht
    have ht_pos : 0 < t := lt_of_lt_of_le hc_pos ht'.1
    have ht_ne : t ^ (3 / 2 : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.rpow_pos_of_pos ht_pos _)
    exact ContinuousAt.div continuousAt_const
      (ContinuousAt.rpow continuousAt_id continuousAt_const (Or.inr (by norm_num)))
      ht_ne
  have hMono :
      ∫ t in c..T, ‖hardyVdcCorrection n t‖
        ≤ ∫ t in c..T, Cn / t ^ (3 / 2 : ℝ) := by
    refine intervalIntegral.integral_mono_on htail hNormInt hPowInt ?_
    intro t ht
    have hDerivLower_t :
        m / Real.sqrt (n + 1) ≤ |deriv (hardyPhaseReal n) t| :=
      hDerivLower n T hT htail t (by simpa [Set.uIcc_of_le htail, c] using ht)
    have hPhaseDerivDiff_t :
        DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t :=
      HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp.phaseDerivDifferentiable
        n T hT htail t (by simpa [Set.uIcc_of_le htail, c] using ht)
    have hSecond_t :
        |deriv (deriv (hardyPhaseReal n)) t| ≤ M / t ^ (3 / 2 : ℝ) :=
      hSecond n T hT htail t (by simpa [Set.uIcc_of_le htail, c] using ht)
    have hsqrt_pos : 0 < Real.sqrt (n + 1) := by positivity
    have hDerivInv_t :
        ‖deriv (fun x => 1 / (Complex.I * deriv (hardyPhaseReal n) x)) t‖
          ≤ ((M / m ^ 2) * (n + 1)) / t ^ (3 / 2 : ℝ) := by
      have hRaw :=
        hardyVdcCorrectionDerivInv_norm_le_of_derivLower_secondDeriv_at
          (n := n) (t := t) (m := m / Real.sqrt (n + 1)) (M := M)
          (div_pos hm hsqrt_pos) hDerivLower_t hPhaseDerivDiff_t hSecond_t
      have hm_ne : m ≠ 0 := ne_of_gt hm
      have hsqrt_ne : Real.sqrt (n + 1) ≠ 0 := ne_of_gt hsqrt_pos
      have hsqrt_sq : Real.sqrt (n + 1) ^ (2 : ℕ) = (n + 1 : ℝ) := by
        have hn1_nonneg : 0 ≤ (n + 1 : ℝ) := by positivity
        nlinarith [Real.sq_sqrt hn1_nonneg]
      calc
        ‖deriv (fun x => 1 / (Complex.I * deriv (hardyPhaseReal n) x)) t‖
            ≤ (M / (m / Real.sqrt (n + 1)) ^ 2) / t ^ (3 / 2 : ℝ) := hRaw
        _ = ((M / m ^ 2) * (Real.sqrt (n + 1) ^ (2 : ℕ))) / t ^ (3 / 2 : ℝ) := by
              field_simp [hm_ne, hsqrt_ne]
        _ = ((M / m ^ 2) * (n + 1)) / t ^ (3 / 2 : ℝ) := by rw [hsqrt_sq]
    simpa [hardyVdcCorrection_norm_eq_derivInv_norm, c, Cn] using hDerivInv_t
  have hConstMul :
      ∫ t in c..T, Cn / t ^ (3 / 2 : ℝ)
        = Cn * ∫ t in c..T, t ^ (-(3 / 2 : ℝ)) := by
    calc
      ∫ t in c..T, Cn / t ^ (3 / 2 : ℝ)
          = ∫ t in c..T, Cn * t ^ (-(3 / 2 : ℝ)) := by
              refine intervalIntegral.integral_congr ?_
              intro t ht
              have ht' : t ∈ Set.Icc c T := by
                simpa [Set.uIcc_of_le htail, c] using ht
              have ht_pos : 0 < t := lt_of_lt_of_le hc_pos ht'.1
              have hpow :
                  t ^ (-(3 / 2 : ℝ)) = (t ^ (3 / 2 : ℝ))⁻¹ :=
                Real.rpow_neg (le_of_lt ht_pos) (3 / 2 : ℝ)
              calc
                Cn / t ^ (3 / 2 : ℝ) = Cn * (t ^ (3 / 2 : ℝ))⁻¹ := by
                  rw [div_eq_mul_inv]
                _ = Cn * t ^ (-(3 / 2 : ℝ)) := by
                  rw [← hpow]
      _ = Cn * ∫ t in c..T, t ^ (-(3 / 2 : ℝ)) := by
            simpa [mul_assoc, mul_comm, mul_left_comm] using
              (intervalIntegral.integral_const_mul Cn
                (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (a := c) (b := T))
  have hModeStart :
      (4 : ℝ) * ((n + 1 : ℝ) ^ (2 : ℕ)) ≤ HardyEstimatesPartial.hardyStart n := by
    unfold HardyEstimatesPartial.hardyStart
    have hsq_nonneg : 0 ≤ ((n + 1 : ℝ) ^ (2 : ℕ)) := by positivity
    nlinarith [Real.pi_gt_three, hsq_nonneg]
  have hModeC :
      (4 : ℝ) * ((n + 1 : ℝ) ^ (2 : ℕ)) ≤ c := by
    exact le_trans hModeStart (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hRpowLe :
      ∫ t in c..T, t ^ (-(3 / 2 : ℝ)) ≤ 1 / (n + 1 : ℝ) :=
    hardyIntegral_rpow_negThreeHalves_tail_le_inv_mode
      (n := n) (c := c) (T := T) htail hc_pos hModeC
  have hCn_nonneg : 0 ≤ Cn := by
    unfold Cn
    positivity
  have hMajorant :
      ∫ t in c..T, Cn / t ^ (3 / 2 : ℝ) ≤ M / m ^ 2 := by
    calc
      ∫ t in c..T, Cn / t ^ (3 / 2 : ℝ)
          = Cn * ∫ t in c..T, t ^ (-(3 / 2 : ℝ)) := hConstMul
      _ ≤ Cn * (1 / (n + 1 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hRpowLe hCn_nonneg
      _ = M / m ^ 2 := by
            unfold Cn
            field_simp [show (n + 1 : ℝ) ≠ 0 by positivity]
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (n + 1) := by
    have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simpa using (Real.sqrt_le_sqrt hbase)
  calc
    ∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
        ‖hardyVdcCorrection n t‖
        = ∫ t in c..T, ‖hardyVdcCorrection n t‖ := by
            simp [c]
    _ ≤ ∫ t in c..T, Cn / t ^ (3 / 2 : ℝ) := hMono
    _ ≤ M / m ^ 2 := hMajorant
    _ = (M / m ^ 2) * 1 := by ring
    _ ≤ (M / m ^ 2) * Real.sqrt (n + 1) := by
          exact mul_le_mul_of_nonneg_left hsqrt_ge_one (by positivity)

instance (priority := 900) [HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    HardyExpPhaseVdcCorrectionNormIntegralSqrtModeOnTailSupportHyp := by
  exact
    hardyExpPhaseVdcCorrectionNormIntegralSqrtModeOnTailSupport_of_derivLowerSqrt_secondDeriv

/-- Tail-localized VdC package from tail phase calculus, tail lower bounds on
`|phase'|`, and tail correction `L¹` control. -/
theorem hardyExpPhaseVdcSqrtModeOnTailSupport_of_derivLowerSqrt_correctionNorm_tailClasses
    [HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralSqrtModeOnTailSupportHyp] :
    HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  obtain ⟨m, hm, hderivLower⟩ :=
    HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp.bound
  have hEndpoint :
      ∃ B₀ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
        ‖hardyVdcPrimitive n T
          - hardyVdcPrimitive n
              (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))‖
          ≤ B₀ * Real.sqrt (n + 1) :=
    hardyExpPhaseVdcEndpointSqrtModeOnTailSupport_of_phaseDerivAbsLowerSqrtMode
      ⟨m, hm, hderivLower⟩
  obtain ⟨B₁, hB₁, hcorrNorm⟩ :=
    HardyExpPhaseVdcCorrectionNormIntegralSqrtModeOnTailSupportHyp.bound
  refine ⟨hEndpoint, ?_, ?_⟩
  · refine ⟨B₁, hB₁, ?_⟩
    intro n T hT htail
    have hcorrInt :
        IntervalIntegrable (hardyVdcCorrection n) volume
          (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T :=
      HardyExpPhaseVdcCorrectionNormIntegralSqrtModeOnTailSupportHyp.intervalIntegrable
        n T hT htail
    calc
      ‖∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
          hardyVdcCorrection n t‖
          ≤ ∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
              ‖hardyVdcCorrection n t‖ := by
                simpa using intervalIntegral.norm_integral_le_integral_norm
                  (f := fun t => hardyVdcCorrection n t) htail
      _ ≤ B₁ * Real.sqrt (n + 1) := hcorrNorm n T hT htail
  · intro n T hT htail
    let c : ℝ := HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)
    have hPhaseDiffTail :
        ∀ t ∈ Set.uIcc c T, DifferentiableAt ℝ (hardyPhaseReal n) t := by
      intro t ht
      simpa [c] using
        (HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp.phaseDifferentiable
          n T hT htail t ht)
    have hPhaseDerivDiffTail :
        ∀ t ∈ Set.uIcc c T, DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t := by
      intro t ht
      simpa [c] using
        (HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp.phaseDerivDifferentiable
          n T hT htail t ht)
    have hPhaseDerivNeTail :
        ∀ t ∈ Set.uIcc c T, deriv (hardyPhaseReal n) t ≠ 0 := by
      intro t ht
      have hsqrt_pos : 0 < Real.sqrt (n + 1) := by positivity
      have hdiv_pos : 0 < m / Real.sqrt (n + 1) := div_pos hm hsqrt_pos
      have habs_pos : 0 < |deriv (hardyPhaseReal n) t| :=
        lt_of_lt_of_le hdiv_pos (hderivLower n T hT htail t (by simpa [c] using ht))
      exact (abs_pos.mp habs_pos)
    have hPrimDiffTail :
        ∀ t ∈ Set.uIcc c T, DifferentiableAt ℝ (hardyVdcPrimitive n) t := by
      intro t ht
      exact hardyVdcPrimitive_differentiableAt_of_phase
        (hPhaseDiffTail t ht)
        (hPhaseDerivDiffTail t ht)
        (hPhaseDerivNeTail t ht)
    have hCorrIntTail :
        IntervalIntegrable (hardyVdcCorrection n) volume c T := by
      simpa [c] using
        (HardyExpPhaseVdcCorrectionNormIntegralSqrtModeOnTailSupportHyp.intervalIntegrable
          n T hT htail)
    have hDerivEqTail :
        ∀ t ∈ Set.uIcc c T,
          deriv (hardyVdcPrimitive n) t = hardyExpPhase n t + hardyVdcCorrection n t :=
      hardyVdcPrimitive_deriv_eq_phase_plus_correction_onInterval
        (n := n) (a := c) (b := T)
        hPhaseDiffTail hPhaseDerivDiffTail hPhaseDerivNeTail
    have hPrimDerivIntTail :
        IntervalIntegrable (deriv (hardyVdcPrimitive n)) volume c T :=
      hardyVdcPrimitive_derivIntervalIntegrable_onInterval_of_phase_and_correction
        (n := n) (a := c) (b := T)
        hPhaseDiffTail hPhaseDerivDiffTail hPhaseDerivNeTail hCorrIntTail
    have hExpIntTail :
        IntervalIntegrable (hardyExpPhase n) volume c T :=
      hardyExpPhase_intervalIntegrable n c T
    simpa [c] using
      (hardyExpPhase_vdc_decomposition_onInterval_of_calculus
        (n := n) (a := c) (b := T)
        hDerivEqTail hPrimDiffTail hPrimDerivIntTail hExpIntTail hCorrIntTail)

instance (priority := 900) [HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralSqrtModeOnTailSupportHyp] :
    HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  exact
    hardyExpPhaseVdcSqrtModeOnTailSupport_of_derivLowerSqrt_correctionNorm_tailClasses

/-- Tail-only assembly route: tail-localized differentiability of `hardyTheta`
and `phase'`, together with tail lower/upper derivative controls, imply the
full tail `√(n+1)` VdC package. This bypasses support-level hypotheses. -/
theorem hardyExpPhaseVdcSqrtModeOnTailSupport_of_hardyThetaTail_secondDeriv_classes
    [HardyThetaDifferentiableOnTailSupportHyp]
    [HardyPhaseDerivDifferentiableOnTailSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  let _ : HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp := inferInstance
  let _ : HardyExpPhaseVdcCorrectionNormIntegralSqrtModeOnTailSupportHyp := inferInstance
  infer_instance

instance (priority := 850) [HardyThetaDifferentiableOnTailSupportHyp]
    [HardyPhaseDerivDifferentiableOnTailSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  exact hardyExpPhaseVdcSqrtModeOnTailSupport_of_hardyThetaTail_secondDeriv_classes

theorem hardyExpPhaseVdcSqrtModeOnSupport_of_vdc
    (hvdc :
      (∃ B₀ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ‖hardyVdcPrimitive n T
          - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖ ≤ B₀) ∧
      (∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖ ≤ B₁) ∧
      (∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t =
          (hardyVdcPrimitive n T
            - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n))
            - ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t)) :
    HardyExpPhaseVdcSqrtModeOnSupportHyp := by
  rcases hvdc with ⟨⟨B₀, hB₀, hEndpoint⟩, ⟨B₁, hB₁, hCorrection⟩, hDecomp⟩
  refine ⟨?_, ?_, hDecomp⟩
  · refine ⟨B₀, hB₀, ?_⟩
    intro n T hT hstart
    calc
      ‖hardyVdcPrimitive n T
          - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖
          ≤ B₀ := hEndpoint n T hT hstart
      _ = B₀ * 1 := by ring
      _ ≤ B₀ * Real.sqrt (n + 1) := by
          have hB₀nn : 0 ≤ B₀ := le_of_lt hB₀
          have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (n + 1) := by
            have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
            simpa using (Real.sqrt_le_sqrt hbase)
          exact mul_le_mul_of_nonneg_left hsqrt_ge_one hB₀nn
  · refine ⟨B₁, hB₁, ?_⟩
    intro n T hT hstart
    calc
      ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖
          ≤ B₁ := hCorrection n T hT hstart
      _ = B₁ * 1 := by ring
      _ ≤ B₁ * Real.sqrt (n + 1) := by
          have hB₁nn : 0 ≤ B₁ := le_of_lt hB₁
          have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (n + 1) := by
            have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
            simpa using (Real.sqrt_le_sqrt hbase)
          exact mul_le_mul_of_nonneg_left hsqrt_ge_one hB₁nn

/-- Assemble a mode-sensitive VdC package from mode-sensitive endpoint and
correction bounds plus the VdC calculus decomposition. -/
theorem hardyExpPhaseVdcSqrtModeOnSupport_of_endpointSqrt_correctionSqrt_calculus
    [HardyExpPhaseVdcEndpointSqrtModeBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionSqrtModeBoundOnSupportHyp]
    [HardyExpPhaseVdcCalculusOnSupportHyp] :
    HardyExpPhaseVdcSqrtModeOnSupportHyp := by
  refine ⟨HardyExpPhaseVdcEndpointSqrtModeBoundOnSupportHyp.bound,
    HardyExpPhaseVdcCorrectionSqrtModeBoundOnSupportHyp.bound, ?_⟩
  exact hardyExpPhase_vdc_decomposition_onSupport_of_calculus
    (hardyVdcPrimitive_deriv_eq_phase_plus_correction
      HardyExpPhaseVdcCalculusOnSupportHyp.phaseDifferentiable
      HardyExpPhaseVdcCalculusOnSupportHyp.phaseDerivDifferentiable
      HardyExpPhaseVdcCalculusOnSupportHyp.phaseDerivNonzero)
    HardyExpPhaseVdcCalculusOnSupportHyp.primitiveDifferentiable
    HardyExpPhaseVdcCalculusOnSupportHyp.primitiveDerivIntervalIntegrable
    HardyExpPhaseVdcCalculusOnSupportHyp.expPhaseIntervalIntegrable
    HardyExpPhaseVdcCalculusOnSupportHyp.correctionIntervalIntegrable

instance [HardyExpPhaseVdcEndpointSqrtModeBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionSqrtModeBoundOnSupportHyp]
    [HardyExpPhaseVdcCalculusOnSupportHyp] :
    HardyExpPhaseVdcSqrtModeOnSupportHyp := by
  exact
    hardyExpPhaseVdcSqrtModeOnSupport_of_endpointSqrt_correctionSqrt_calculus

/-- Convenience assembly: mode-sensitive derivative lower bounds, mode-sensitive
correction bounds, and VdC calculus imply the full mode-sensitive VdC package. -/
theorem hardyExpPhaseVdcSqrtModeOnSupport_of_derivLowerSqrt_correctionSqrt_calculus
    [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp]
    [HardyExpPhaseVdcCorrectionSqrtModeBoundOnSupportHyp]
    [HardyExpPhaseVdcCalculusOnSupportHyp] :
    HardyExpPhaseVdcSqrtModeOnSupportHyp := by
  let _ : HardyExpPhaseVdcEndpointSqrtModeBoundOnSupportHyp := inferInstance
  infer_instance

/-- Convenience assembly for the mode-sensitive route:
`|phase'| ≳ 1/√(n+1)` and correction `L¹` control imply the full
mode-sensitive VdC-on-support package. The correction `L¹` hypothesis is
upgraded to a mode-sensitive correction bound automatically. -/
theorem hardyExpPhaseVdcSqrtModeOnSupport_of_derivLowerSqrt_correctionNorm
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp] :
    HardyExpPhaseVdcSqrtModeOnSupportHyp := by
  let _ : HardyExpPhaseVdcCorrectionSqrtModeBoundOnSupportHyp := inferInstance
  let _ : HardyExpPhaseVdcCalculusOnSupportHyp := inferInstance
  exact hardyExpPhaseVdcSqrtModeOnSupport_of_derivLowerSqrt_correctionSqrt_calculus

instance [HardyExpPhaseVdcOnSupportHyp] :
    HardyExpPhaseVdcSqrtModeOnSupportHyp := by
  exact hardyExpPhaseVdcSqrtModeOnSupport_of_vdc
    ⟨HardyExpPhaseVdcOnSupportHyp.endpointBound,
      HardyExpPhaseVdcOnSupportHyp.correctionBound,
      HardyExpPhaseVdcOnSupportHyp.decomposition⟩

instance [HardyExpPhaseVdcEndpointBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionBoundOnSupportHyp]
    [HardyExpPhaseVdcCalculusOnSupportHyp] :
    HardyExpPhaseVdcOnSupportHyp := by
  refine ⟨HardyExpPhaseVdcEndpointBoundOnSupportHyp.bound,
    HardyExpPhaseVdcCorrectionBoundOnSupportHyp.bound, ?_⟩
  exact hardyExpPhase_vdc_decomposition_onSupport_of_calculus
    (hardyVdcPrimitive_deriv_eq_phase_plus_correction
      HardyExpPhaseVdcCalculusOnSupportHyp.phaseDifferentiable
      HardyExpPhaseVdcCalculusOnSupportHyp.phaseDerivDifferentiable
      HardyExpPhaseVdcCalculusOnSupportHyp.phaseDerivNonzero)
    HardyExpPhaseVdcCalculusOnSupportHyp.primitiveDifferentiable
    HardyExpPhaseVdcCalculusOnSupportHyp.primitiveDerivIntervalIntegrable
    HardyExpPhaseVdcCalculusOnSupportHyp.expPhaseIntervalIntegrable
    HardyExpPhaseVdcCalculusOnSupportHyp.correctionIntervalIntegrable

theorem hardyExpPhaseIntervalIntegralUniformBoundOnSupport_of_vdc
    (hvdc :
      (∃ B₀ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ‖hardyVdcPrimitive n T
          - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖ ≤ B₀) ∧
      (∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖ ≤ B₁) ∧
      (∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t =
          (hardyVdcPrimitive n T
            - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n))
            - ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t)) :
    HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp := by
  rcases hvdc with ⟨⟨B₀, hB₀, hEndpoint⟩, ⟨B₁, hB₁, hCorrection⟩, hDecomp⟩
  refine ⟨B₀ + B₁, add_pos hB₀ hB₁, ?_⟩
  intro n T hT hstart
  calc
    ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖
        = ‖(hardyVdcPrimitive n T
            - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n))
            - ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖ := by
            rw [hDecomp n T hT hstart]
    _ ≤ ‖hardyVdcPrimitive n T
            - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖
          + ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖ := by
            exact norm_sub_le _ _
    _ ≤ B₀ + B₁ := by
      exact add_le_add (hEndpoint n T hT hstart) (hCorrection n T hT hstart)

theorem hardyExpPhaseIntervalIntegralSqrtModeBoundOnSupport_of_vdcSqrtMode
    (hvdc :
      (∃ B₀ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ‖hardyVdcPrimitive n T
          - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖
            ≤ B₀ * Real.sqrt (n + 1)) ∧
      (∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖
          ≤ B₁ * Real.sqrt (n + 1)) ∧
      (∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t =
          (hardyVdcPrimitive n T
            - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n))
            - ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t)) :
    HardyExpPhaseIntervalIntegralSqrtModeBoundOnSupportHyp := by
  rcases hvdc with ⟨⟨B₀, hB₀, hEndpoint⟩, ⟨B₁, hB₁, hCorrection⟩, hDecomp⟩
  refine ⟨B₀ + B₁, add_pos hB₀ hB₁, ?_⟩
  intro n T hT hstart
  calc
    ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖
        = ‖(hardyVdcPrimitive n T
            - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n))
            - ∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖ := by
            rw [hDecomp n T hT hstart]
    _ ≤ ‖hardyVdcPrimitive n T
            - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖
          + ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖ := by
            exact norm_sub_le _ _
    _ ≤ B₀ * Real.sqrt (n + 1) + B₁ * Real.sqrt (n + 1) := by
          exact add_le_add (hEndpoint n T hT hstart) (hCorrection n T hT hstart)
    _ = (B₀ + B₁) * Real.sqrt (n + 1) := by ring

instance [HardyExpPhaseVdcOnSupportHyp] :
    HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp := by
  refine hardyExpPhaseIntervalIntegralUniformBoundOnSupport_of_vdc ?_
  exact ⟨HardyExpPhaseVdcOnSupportHyp.endpointBound,
    HardyExpPhaseVdcOnSupportHyp.correctionBound,
    HardyExpPhaseVdcOnSupportHyp.decomposition⟩

instance [HardyExpPhaseVdcSqrtModeOnSupportHyp] :
    HardyExpPhaseIntervalIntegralSqrtModeBoundOnSupportHyp := by
  refine hardyExpPhaseIntervalIntegralSqrtModeBoundOnSupport_of_vdcSqrtMode ?_
  exact ⟨HardyExpPhaseVdcSqrtModeOnSupportHyp.endpointBound,
    HardyExpPhaseVdcSqrtModeOnSupportHyp.correctionBound,
    HardyExpPhaseVdcSqrtModeOnSupportHyp.decomposition⟩

/-- Concrete VdC route for the stationary-window tail class. -/
theorem hardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupport_of_vdcSqrtMode
    [HardyExpPhaseVdcSqrtModeOnSupportHyp] :
    HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp := by
  let hinterval : HardyExpPhaseIntervalIntegralSqrtModeBoundOnSupportHyp := by
    refine hardyExpPhaseIntervalIntegralSqrtModeBoundOnSupport_of_vdcSqrtMode ?_
    exact ⟨HardyExpPhaseVdcSqrtModeOnSupportHyp.endpointBound,
      HardyExpPhaseVdcSqrtModeOnSupportHyp.correctionBound,
      HardyExpPhaseVdcSqrtModeOnSupportHyp.decomposition⟩
  exact
    hardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupport_of_intervalSqrtMode
      hinterval.bound

instance (priority := 900) [HardyExpPhaseVdcSqrtModeOnSupportHyp] :
    HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp := by
  exact hardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupport_of_vdcSqrtMode

/-- Tail-localized VdC package implies the stationary-window tail bound
directly. -/
theorem hardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupport_of_vdcSqrtTailMode
    (hvdcTail :
      (∃ B₀ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
        ‖hardyVdcPrimitive n T
          - hardyVdcPrimitive n
              (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))‖
            ≤ B₀ * Real.sqrt (n + 1)) ∧
      (∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
        ‖∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
            hardyVdcCorrection n t‖ ≤ B₁ * Real.sqrt (n + 1)) ∧
      (∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
            hardyExpPhase n t =
          (hardyVdcPrimitive n T
            - hardyVdcPrimitive n
                (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)))
            - ∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
                hardyVdcCorrection n t)) :
    HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp := by
  rcases hvdcTail with ⟨⟨B₀, hB₀, hEndpoint⟩, ⟨B₁, hB₁, hCorrection⟩, hDecomp⟩
  refine ⟨B₀ + B₁, add_pos hB₀ hB₁, ?_⟩
  intro n T hT htail
  calc
    ‖∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T, hardyExpPhase n t‖
        = ‖(hardyVdcPrimitive n T
            - hardyVdcPrimitive n
                (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)))
            - ∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
                hardyVdcCorrection n t‖ := by
              rw [hDecomp n T hT htail]
    _ ≤ ‖hardyVdcPrimitive n T
            - hardyVdcPrimitive n
                (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))‖
          + ‖∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
                hardyVdcCorrection n t‖ := by
            exact norm_sub_le _ _
    _ ≤ B₀ * Real.sqrt (n + 1) + B₁ * Real.sqrt (n + 1) := by
          exact add_le_add (hEndpoint n T hT htail) (hCorrection n T hT htail)
    _ = (B₀ + B₁) * Real.sqrt (n + 1) := by ring

instance [HardyExpPhaseVdcSqrtModeOnTailSupportHyp] :
    HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp := by
  refine hardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupport_of_vdcSqrtTailMode ?_
  exact ⟨HardyExpPhaseVdcSqrtModeOnTailSupportHyp.endpointBound,
    HardyExpPhaseVdcSqrtModeOnTailSupportHyp.correctionBound,
    HardyExpPhaseVdcSqrtModeOnTailSupportHyp.decomposition⟩

/-- Build the tail-localized VdC package from the support-level package by
restricting from `[hardyStart n, T]` to the tail interval
`[hardyStart n + √(n+1), T]`. -/
theorem hardyExpPhaseVdcSqrtModeOnTailSupport_of_vdcSqrtMode_onSupport
    [HardyExpPhaseVdcSqrtModeOnSupportHyp]
    [HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp] :
    HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  obtain ⟨B₀, hB₀, hEndpoint⟩ := HardyExpPhaseVdcSqrtModeOnSupportHyp.endpointBound
  obtain ⟨B₁, hB₁, hCorrection⟩ := HardyExpPhaseVdcSqrtModeOnSupportHyp.correctionBound
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨2 * B₀, by positivity, ?_⟩
    intro n T hT htail
    let a : ℝ := HardyEstimatesPartial.hardyStart n
    let c : ℝ := a + Real.sqrt (n + 1)
    have hstartC : a ≤ c := by
      exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    have hcut : c ≤ T := by
      simpa [a, c] using htail
    have hstartT : a ≤ T := le_trans hstartC hcut
    have hC_ge_two : (2 : ℝ) ≤ c := by
      exact le_trans (by simpa [a] using hardyStart_ge_two n) hstartC
    have hEndpointT :
        ‖hardyVdcPrimitive n T - hardyVdcPrimitive n a‖ ≤ B₀ * Real.sqrt (n + 1) :=
      hEndpoint n T hT hstartT
    have hEndpointC :
        ‖hardyVdcPrimitive n c - hardyVdcPrimitive n a‖ ≤ B₀ * Real.sqrt (n + 1) :=
      hEndpoint n c hC_ge_two hstartC
    have hSplit :
        hardyVdcPrimitive n T - hardyVdcPrimitive n c
          = (hardyVdcPrimitive n T - hardyVdcPrimitive n a)
              - (hardyVdcPrimitive n c - hardyVdcPrimitive n a) := by
      ring
    calc
      ‖hardyVdcPrimitive n T
          - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))‖
          = ‖hardyVdcPrimitive n T - hardyVdcPrimitive n c‖ := by
              simp [a, c]
      _ = ‖(hardyVdcPrimitive n T - hardyVdcPrimitive n a)
            - (hardyVdcPrimitive n c - hardyVdcPrimitive n a)‖ := by
              rw [hSplit]
      _ ≤ ‖hardyVdcPrimitive n T - hardyVdcPrimitive n a‖
            + ‖hardyVdcPrimitive n c - hardyVdcPrimitive n a‖ := by
              exact norm_sub_le _ _
      _ ≤ B₀ * Real.sqrt (n + 1) + B₀ * Real.sqrt (n + 1) := by
            exact add_le_add hEndpointT hEndpointC
      _ = (2 * B₀) * Real.sqrt (n + 1) := by ring
  · refine ⟨2 * B₁, by positivity, ?_⟩
    intro n T hT htail
    let a : ℝ := HardyEstimatesPartial.hardyStart n
    let c : ℝ := a + Real.sqrt (n + 1)
    have hstartC : a ≤ c := by
      exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    have hcut : c ≤ T := by
      simpa [a, c] using htail
    have hstartT : a ≤ T := le_trans hstartC hcut
    have hC_ge_two : (2 : ℝ) ≤ c := by
      exact le_trans (by simpa [a] using hardyStart_ge_two n) hstartC
    have hCorrStartT :
        IntervalIntegrable (hardyVdcCorrection n) volume a T :=
      HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp.intervalIntegrable n T hT hstartT
    have hCorrOnStartT :
        IntegrableOn (hardyVdcCorrection n) (Ioc a T) := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hstartT).1 hCorrStartT
    have hSubsetAC : Set.Ioc a c ⊆ Set.Ioc a T := by
      intro t ht
      exact ⟨ht.1, le_trans ht.2 hcut⟩
    have hSubsetCT : Set.Ioc c T ⊆ Set.Ioc a T := by
      intro t ht
      exact ⟨lt_of_le_of_lt hstartC ht.1, ht.2⟩
    have hCorrAC :
        IntervalIntegrable (hardyVdcCorrection n) volume a c := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hstartC).2
        (hCorrOnStartT.mono_set hSubsetAC)
    have hCorrCT :
        IntervalIntegrable (hardyVdcCorrection n) volume c T := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hcut).2
        (hCorrOnStartT.mono_set hSubsetCT)
    have hCorrSplit :
        ∫ t in a..T, hardyVdcCorrection n t
          = (∫ t in a..c, hardyVdcCorrection n t)
              + (∫ t in c..T, hardyVdcCorrection n t) := by
      simpa using
        (intervalIntegral.integral_add_adjacent_intervals hCorrAC hCorrCT).symm
    have hCorrTailEq :
        ∫ t in c..T, hardyVdcCorrection n t
          = (∫ t in a..T, hardyVdcCorrection n t)
              - (∫ t in a..c, hardyVdcCorrection n t) := by
      exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hCorrSplit.symm)
    have hCorrectionT :
        ‖∫ t in a..T, hardyVdcCorrection n t‖ ≤ B₁ * Real.sqrt (n + 1) :=
      hCorrection n T hT hstartT
    have hCorrectionC :
        ‖∫ t in a..c, hardyVdcCorrection n t‖ ≤ B₁ * Real.sqrt (n + 1) :=
      hCorrection n c hC_ge_two hstartC
    calc
      ‖∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
            hardyVdcCorrection n t‖
          = ‖∫ t in c..T, hardyVdcCorrection n t‖ := by
              simp [a, c]
      _ = ‖(∫ t in a..T, hardyVdcCorrection n t)
            - (∫ t in a..c, hardyVdcCorrection n t)‖ := by
              rw [hCorrTailEq]
      _ ≤ ‖∫ t in a..T, hardyVdcCorrection n t‖
            + ‖∫ t in a..c, hardyVdcCorrection n t‖ := by
              exact norm_sub_le _ _
      _ ≤ B₁ * Real.sqrt (n + 1) + B₁ * Real.sqrt (n + 1) := by
            exact add_le_add hCorrectionT hCorrectionC
      _ = (2 * B₁) * Real.sqrt (n + 1) := by ring
  · intro n T hT htail
    let a : ℝ := HardyEstimatesPartial.hardyStart n
    let c : ℝ := a + Real.sqrt (n + 1)
    have hstartC : a ≤ c := by
      exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    have hcut : c ≤ T := by
      simpa [a, c] using htail
    have hstartT : a ≤ T := le_trans hstartC hcut
    have hC_ge_two : (2 : ℝ) ≤ c := by
      exact le_trans (by simpa [a] using hardyStart_ge_two n) hstartC
    have hExpSplit :
        ∫ t in a..T, hardyExpPhase n t
          = (∫ t in a..c, hardyExpPhase n t)
              + (∫ t in c..T, hardyExpPhase n t) := by
      simpa using
        (intervalIntegral.integral_add_adjacent_intervals
          (hardyExpPhase_intervalIntegrable n a c)
          (hardyExpPhase_intervalIntegrable n c T)).symm
    have hExpTailEq :
        ∫ t in c..T, hardyExpPhase n t
          = (∫ t in a..T, hardyExpPhase n t)
              - (∫ t in a..c, hardyExpPhase n t) := by
      exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hExpSplit.symm)
    have hCorrStartT :
        IntervalIntegrable (hardyVdcCorrection n) volume a T :=
      HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp.intervalIntegrable n T hT hstartT
    have hCorrOnStartT :
        IntegrableOn (hardyVdcCorrection n) (Ioc a T) := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hstartT).1 hCorrStartT
    have hSubsetAC : Set.Ioc a c ⊆ Set.Ioc a T := by
      intro t ht
      exact ⟨ht.1, le_trans ht.2 hcut⟩
    have hSubsetCT : Set.Ioc c T ⊆ Set.Ioc a T := by
      intro t ht
      exact ⟨lt_of_le_of_lt hstartC ht.1, ht.2⟩
    have hCorrAC :
        IntervalIntegrable (hardyVdcCorrection n) volume a c := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hstartC).2
        (hCorrOnStartT.mono_set hSubsetAC)
    have hCorrCT :
        IntervalIntegrable (hardyVdcCorrection n) volume c T := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hcut).2
        (hCorrOnStartT.mono_set hSubsetCT)
    have hCorrSplit :
        ∫ t in a..T, hardyVdcCorrection n t
          = (∫ t in a..c, hardyVdcCorrection n t)
              + (∫ t in c..T, hardyVdcCorrection n t) := by
      simpa using
        (intervalIntegral.integral_add_adjacent_intervals hCorrAC hCorrCT).symm
    have hCorrTailEq :
        ∫ t in c..T, hardyVdcCorrection n t
          = (∫ t in a..T, hardyVdcCorrection n t)
              - (∫ t in a..c, hardyVdcCorrection n t) := by
      exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hCorrSplit.symm)
    have hDecompT :
        ∫ t in a..T, hardyExpPhase n t
          = (hardyVdcPrimitive n T - hardyVdcPrimitive n a)
              - ∫ t in a..T, hardyVdcCorrection n t :=
      HardyExpPhaseVdcSqrtModeOnSupportHyp.decomposition n T hT hstartT
    have hDecompC :
        ∫ t in a..c, hardyExpPhase n t
          = (hardyVdcPrimitive n c - hardyVdcPrimitive n a)
              - ∫ t in a..c, hardyVdcCorrection n t :=
      HardyExpPhaseVdcSqrtModeOnSupportHyp.decomposition n c hC_ge_two hstartC
    calc
      ∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T, hardyExpPhase n t
          = ∫ t in c..T, hardyExpPhase n t := by
              simp [a, c]
      _ = (∫ t in a..T, hardyExpPhase n t) - (∫ t in a..c, hardyExpPhase n t) := by
            rw [hExpTailEq]
      _ = ((hardyVdcPrimitive n T - hardyVdcPrimitive n a)
              - ∫ t in a..T, hardyVdcCorrection n t)
            - ((hardyVdcPrimitive n c - hardyVdcPrimitive n a)
              - ∫ t in a..c, hardyVdcCorrection n t) := by
            rw [hDecompT, hDecompC]
      _ = (hardyVdcPrimitive n T - hardyVdcPrimitive n c)
            - ((∫ t in a..T, hardyVdcCorrection n t)
              - (∫ t in a..c, hardyVdcCorrection n t)) := by
            ring
      _ = (hardyVdcPrimitive n T - hardyVdcPrimitive n c)
            - ∫ t in c..T, hardyVdcCorrection n t := by
            rw [hCorrTailEq]
      _ = (hardyVdcPrimitive n T
            - hardyVdcPrimitive n
                (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)))
            - ∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
                hardyVdcCorrection n t := by
            simp [a, c]

instance (priority := 900) [HardyExpPhaseVdcSqrtModeOnSupportHyp]
    [HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp] :
    HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  exact hardyExpPhaseVdcSqrtModeOnTailSupport_of_vdcSqrtMode_onSupport

/-- Concrete stationary-phase route to the tail-localized VdC package:
mode-sensitive derivative lower bounds plus correction `L¹` control on support
yield support VdC, which then restricts to the tail interval. -/
theorem hardyExpPhaseVdcSqrtModeOnTailSupport_of_derivLowerSqrt_correctionNorm
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp] :
    HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  let _ : HardyExpPhaseVdcSqrtModeOnSupportHyp := inferInstance
  let _ : HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp := inferInstance
  infer_instance

/-- Convenience assembly: quantitative phase-derivative lower bounds and
L¹-correction bounds, together with VdC calculus hypotheses, imply the full
VdC-on-support package. -/
theorem hardyExpPhaseVdcOnSupport_of_derivLower_correctionNorm_calculus
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp]
    [HardyExpPhaseVdcCalculusOnSupportHyp] :
    HardyExpPhaseVdcOnSupportHyp := by
  infer_instance

/-- Full VdC-on-support package from explicit phase calculus assumptions:
`hardyTheta` differentiability on support, differentiability of the phase
derivative, a quantitative lower bound on `|phase'|`, quantitative L¹-control
of the correction term, and interval-integrability of the correction term. -/
theorem hardyExpPhaseVdcOnSupport_of_hardyTheta_derivLower_correctionNorm_correctionInt
    (hThetaDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ HardyEstimatesPartial.hardyTheta t)
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          DifferentiableAt ℝ (deriv (hardyPhaseReal n)) t)
    (hDerivLower :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (HardyEstimatesPartial.hardyStart n) T,
          m ≤ |deriv (hardyPhaseReal n) t|)
    (hCorrectionNorm :
      ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ∫ t in HardyEstimatesPartial.hardyStart n..T, ‖hardyVdcCorrection n t‖ ≤ B₁)
    (hCorrectionInt :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        IntervalIntegrable (hardyVdcCorrection n) volume
          (HardyEstimatesPartial.hardyStart n) T) :
    HardyExpPhaseVdcOnSupportHyp := by
  let hPhaseCalc : HardyExpPhaseVdcPhaseCalculusOnSupportHyp :=
    hardyExpPhaseVdcPhaseCalculusOnSupport_of_hardyTheta_and_derivLower
      hThetaDiff hPhaseDerivDiff hDerivLower
  let hPrimCorr : HardyExpPhaseVdcPrimitiveCorrectionOnSupportHyp :=
    hardyExpPhaseVdcPrimitiveCorrectionOnSupport_of_phase_and_correction
      hPhaseCalc.phaseDifferentiable
      hPhaseCalc.phaseDerivDifferentiable
      hPhaseCalc.phaseDerivNonzero
      hCorrectionInt
  let hCalc : HardyExpPhaseVdcCalculusOnSupportHyp :=
    hardyExpPhaseVdcCalculusOnSupport_of_phase_primitive_correction
      hPhaseCalc.phaseDifferentiable
      hPhaseCalc.phaseDerivDifferentiable
      hPhaseCalc.phaseDerivNonzero
      hPrimCorr.primitiveDifferentiable
      hPrimCorr.correctionIntervalIntegrable
  let hEndpoint : HardyExpPhaseVdcEndpointBoundOnSupportHyp :=
    hardyExpPhaseVdcEndpointBoundOnSupport_of_phaseDerivAbsLower hDerivLower
  let hCorrection : HardyExpPhaseVdcCorrectionBoundOnSupportHyp :=
    hardyExpPhaseVdcCorrectionBoundOnSupport_of_normIntegral hCorrectionNorm
  exact (inferInstance :
    HardyExpPhaseVdcOnSupportHyp)

/-- Class-level assembly version of
`hardyExpPhaseVdcOnSupport_of_hardyTheta_derivLower_correctionNorm_correctionInt`. -/
theorem hardyExpPhaseVdcOnSupport_of_hardyTheta_classes
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp] :
    HardyExpPhaseVdcOnSupportHyp := by
  exact hardyExpPhaseVdcOnSupport_of_hardyTheta_derivLower_correctionNorm_correctionInt
    HardyThetaDifferentiableOnSupportHyp.differentiable
    HardyPhaseDerivDifferentiableOnSupportHyp.differentiable
    HardyExpPhaseDerivAbsLowerBoundOnSupportHyp.bound
    HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp.bound
    HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp.intervalIntegrable

instance [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp] :
    HardyExpPhaseVdcOnSupportHyp := by
  exact hardyExpPhaseVdcOnSupport_of_hardyTheta_classes

/-- VdC-on-support package from phase-side Hardy classes and second-derivative
decay alone: correction `L¹` control is recovered automatically. -/
theorem hardyExpPhaseVdcOnSupport_of_hardyTheta_secondDeriv_classes
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    HardyExpPhaseVdcOnSupportHyp := by
  infer_instance

instance (priority := 900) [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    HardyExpPhaseVdcOnSupportHyp := by
  exact hardyExpPhaseVdcOnSupport_of_hardyTheta_secondDeriv_classes

/-- Mode-sensitive global bound for the `Ioc` oscillatory integral:
the `n`-mode integral may grow like `√(n+1)`. -/
class HardyExpPhaseIntegralSqrtModeBoundHyp : Prop where
  bound :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      ‖∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t‖
        ≤ B * Real.sqrt (n + 1)

theorem hardyExpPhaseIntegralUniformBound_of_interval_onSupport
    (hinterval :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖ ≤ B) :
    HardyExpPhaseIntegralUniformBoundHyp := by
  obtain ⟨B, hB, hintervalB⟩ := hinterval
  refine ⟨B, hB, ?_⟩
  intro n T hT
  by_cases hstart : HardyEstimatesPartial.hardyStart n ≤ T
  · calc
      ‖∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t‖
          = ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖ := by
              rw [← intervalIntegral.integral_of_le hstart]
      _ ≤ B := hintervalB n T hT hstart
  · have hEmpty : Ioc (HardyEstimatesPartial.hardyStart n) T = ∅ := by
      ext t
      constructor
      · intro ht
        exact hstart (le_trans (le_of_lt ht.1) ht.2)
      · intro ht
        exact False.elim ht
    have hZero :
        ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t = 0 := by
      simp [hEmpty]
    rw [hZero, norm_zero]
    exact le_of_lt hB

instance [HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp] :
    HardyExpPhaseIntegralUniformBoundHyp := by
  exact hardyExpPhaseIntegralUniformBound_of_interval_onSupport
    HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp.bound

theorem hardyExpPhaseIntegralSqrtModeBound_of_interval_onSupport
    (hinterval :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n ≤ T →
        ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖
          ≤ B * Real.sqrt (n + 1)) :
    HardyExpPhaseIntegralSqrtModeBoundHyp := by
  obtain ⟨B, hB, hintervalB⟩ := hinterval
  refine ⟨B, hB, ?_⟩
  intro n T hT
  by_cases hstart : HardyEstimatesPartial.hardyStart n ≤ T
  · calc
      ‖∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t‖
          = ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyExpPhase n t‖ := by
              rw [← intervalIntegral.integral_of_le hstart]
      _ ≤ B * Real.sqrt (n + 1) := hintervalB n T hT hstart
  · have hEmpty : Ioc (HardyEstimatesPartial.hardyStart n) T = ∅ := by
      ext t
      constructor
      · intro ht
        exact hstart (le_trans (le_of_lt ht.1) ht.2)
      · intro ht
        exact False.elim ht
    have hZero :
        ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t = 0 := by
      simp [hEmpty]
    rw [hZero, norm_zero]
    exact mul_nonneg (le_of_lt hB) (Real.sqrt_nonneg _)

instance [HardyExpPhaseIntervalIntegralSqrtModeBoundOnSupportHyp] :
    HardyExpPhaseIntegralSqrtModeBoundHyp := by
  exact hardyExpPhaseIntegralSqrtModeBound_of_interval_onSupport
    HardyExpPhaseIntervalIntegralSqrtModeBoundOnSupportHyp.bound

instance [HardyExpPhaseIntegralUniformBoundHyp] :
    HardyExpPhaseIntegralSqrtModeBoundHyp := by
  obtain ⟨B, hB, hbound⟩ := HardyExpPhaseIntegralUniformBoundHyp.bound
  exact ⟨B, hB, fun n T hT => by
    calc
      ‖∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t‖
          ≤ B := hbound n T hT
      _ = B * 1 := by ring
      _ ≤ B * Real.sqrt (n + 1) := by
          have hBnn : 0 ≤ B := le_of_lt hB
          have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (n + 1) := by
            have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
            simpa using (Real.sqrt_le_sqrt hbase)
          exact mul_le_mul_of_nonneg_left hsqrt_ge_one hBnn⟩

/-- Optional stronger analytic input for the main term:
uniform boundedness of each oscillatory cosine integral. -/
class HardyCosIntegralUniformBoundHyp : Prop where
  bound :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
    |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
        HardyEstimatesPartial.hardyCos n t| ≤ B

/-- A weaker, mode-sensitive cosine integral input:
each `n`-mode may grow like `√(n+1)`, which still suffices after weighting by
`(n+1)^(-1/2)` in `hardySumInt`. -/
class HardyCosIntegralSqrtModeBoundHyp : Prop where
  bound :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
          HardyEstimatesPartial.hardyCos n t| ≤ B * Real.sqrt (n + 1)

theorem hardyCosIntegralUniformBound_of_hardyExpPhaseIntegralUniformBound
    (hphase :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        ‖∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t‖ ≤ B) :
    HardyCosIntegralUniformBoundHyp := by
  obtain ⟨B, hB, hphaseB⟩ := hphase
  refine ⟨B, hB, ?_⟩
  intro n T hT
  calc
    |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
        HardyEstimatesPartial.hardyCos n t|
        = |(∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t).re| := by
            rw [hardyCosIntegral_eq_re_hardyExpPhaseIntegral]
    _ ≤ ‖∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t‖ := by
          exact Complex.abs_re_le_norm _
    _ ≤ B := hphaseB n T hT

instance [HardyExpPhaseIntegralUniformBoundHyp] : HardyCosIntegralUniformBoundHyp := by
  exact hardyCosIntegralUniformBound_of_hardyExpPhaseIntegralUniformBound
    HardyExpPhaseIntegralUniformBoundHyp.bound

theorem hardyCosIntegralSqrtModeBound_of_hardyExpPhaseIntegralSqrtModeBound
    (hphase :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        ‖∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t‖
          ≤ B * Real.sqrt (n + 1)) :
    HardyCosIntegralSqrtModeBoundHyp := by
  obtain ⟨B, hB, hphaseB⟩ := hphase
  refine ⟨B, hB, ?_⟩
  intro n T hT
  calc
    |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
        HardyEstimatesPartial.hardyCos n t|
        = |(∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t).re| := by
            rw [hardyCosIntegral_eq_re_hardyExpPhaseIntegral]
    _ ≤ ‖∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T, hardyExpPhase n t‖ := by
          exact Complex.abs_re_le_norm _
    _ ≤ B * Real.sqrt (n + 1) := hphaseB n T hT

instance [HardyExpPhaseIntegralSqrtModeBoundHyp] :
    HardyCosIntegralSqrtModeBoundHyp := by
  exact hardyCosIntegralSqrtModeBound_of_hardyExpPhaseIntegralSqrtModeBound
    HardyExpPhaseIntegralSqrtModeBoundHyp.bound

theorem hardyCosIntegralSqrtModeBound_of_uniform
    (hcos :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
            HardyEstimatesPartial.hardyCos n t| ≤ B) :
    HardyCosIntegralSqrtModeBoundHyp := by
  obtain ⟨B, hB, hcosB⟩ := hcos
  refine ⟨B, hB, ?_⟩
  intro n T hT
  calc
    |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
        HardyEstimatesPartial.hardyCos n t|
        ≤ B := hcosB n T hT
    _ = B * 1 := by ring
    _ ≤ B * Real.sqrt (n + 1) := by
        have hBnn : 0 ≤ B := le_of_lt hB
        have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (n + 1) := by
          have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          simpa using (Real.sqrt_le_sqrt hbase)
        exact mul_le_mul_of_nonneg_left hsqrt_ge_one hBnn

instance [HardyCosIntegralUniformBoundHyp] : HardyCosIntegralSqrtModeBoundHyp := by
  exact hardyCosIntegralSqrtModeBound_of_uniform
    HardyCosIntegralUniformBoundHyp.bound

/-- Direct first-derivative van der Corput route for the cosine modes:
if `hardyPhaseReal n` is globally `C²`, has monotone derivative on each tail
`[hardyStart n + √(n+1), T]`, and that derivative is bounded below by
`m / √(n+1)`, then each cosine-mode integral is `O(√(n+1))`. -/
theorem hardyCosIntegralSqrtModeBound_of_vdcFirstDeriv_tail
    (hPhaseDiff : ∀ n : ℕ, Differentiable ℝ (hardyPhaseReal n))
    (hPhaseDerivDiff : ∀ n : ℕ, Differentiable ℝ (deriv (hardyPhaseReal n)))
    (hPhaseSecondCont : ∀ n : ℕ, Continuous (deriv (deriv (hardyPhaseReal n))))
    (hDerivLowerTail :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T,
          m / Real.sqrt (n + 1) ≤ deriv (hardyPhaseReal n) t)
    (hSecondNonnegTail :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.Icc (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1)) T,
          0 ≤ deriv (deriv (hardyPhaseReal n)) t) :
    HardyCosIntegralSqrtModeBoundHyp := by
  obtain ⟨m, hm, hDerivLower⟩ := hDerivLowerTail
  refine ⟨1 + 3 / m, by positivity, ?_⟩
  intro n T hT
  let a : ℝ := HardyEstimatesPartial.hardyStart n
  let c : ℝ := a + Real.sqrt (n + 1)
  by_cases hstart : a ≤ T
  · by_cases hcut : c ≤ T
    · have hNearInt :
        IntervalIntegrable (fun t : ℝ => Real.cos (hardyPhaseReal n t)) volume a c :=
        (Real.continuous_cos.comp (hPhaseDiff n).continuous).intervalIntegrable _ _
      have hTailInt :
          IntervalIntegrable (fun t : ℝ => Real.cos (hardyPhaseReal n t)) volume c T :=
        (Real.continuous_cos.comp (hPhaseDiff n).continuous).intervalIntegrable _ _
      have hsplit :
          ∫ t in a..T, Real.cos (hardyPhaseReal n t)
            = (∫ t in a..c, Real.cos (hardyPhaseReal n t))
                + (∫ t in c..T, Real.cos (hardyPhaseReal n t)) := by
        simpa using
          (intervalIntegral.integral_add_adjacent_intervals hNearInt hTailInt).symm
      have hNear :
          |∫ t in a..c, Real.cos (hardyPhaseReal n t)| ≤ Real.sqrt (n + 1) := by
        have hNearAbs :
            |∫ t in a..c, Real.cos (hardyPhaseReal n t)|
              ≤ ∫ t in a..c, |Real.cos (hardyPhaseReal n t)| := by
          simpa [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_integral_norm
              (f := fun t : ℝ => Real.cos (hardyPhaseReal n t))
              (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
        calc
          |∫ t in a..c, Real.cos (hardyPhaseReal n t)|
              ≤ ∫ t in a..c, |Real.cos (hardyPhaseReal n t)| := hNearAbs
          _ ≤ ∫ t in a..c, (1 : ℝ) := by
                refine intervalIntegral.integral_mono_on
                  (le_add_of_nonneg_right (Real.sqrt_nonneg _))
                  ?_ ?_ ?_
                · exact (continuous_abs.comp
                    (Real.continuous_cos.comp (hPhaseDiff n).continuous)).intervalIntegrable _ _
                · exact (continuous_const).intervalIntegrable _ _
                · intro t ht
                  exact Real.abs_cos_le_one _
          _ = c - a := by simp
          _ = Real.sqrt (n + 1) := by simp [c]
      have hm_div_pos : 0 < m / Real.sqrt (n + 1) := by
        exact div_pos hm (Real.sqrt_pos.2 (by positivity))
      have hTail :
          |∫ t in c..T, Real.cos (hardyPhaseReal n t)| ≤ (3 / m) * Real.sqrt (n + 1) := by
        have hbase :
            |∫ t in c..T, Real.cos (hardyPhaseReal n t)|
              ≤ 3 / (m / Real.sqrt (n + 1)) := by
          exact VdcFirstDerivTest.vdc_cos_bound
            (phi := hardyPhaseReal n) (a := c) (b := T)
            (m := m / Real.sqrt (n + 1)) hcut hm_div_pos
            (hPhaseDiff n) (hPhaseDerivDiff n) (hPhaseSecondCont n)
            (hDerivLower n T hT (by simpa [a, c] using hcut))
            (hSecondNonnegTail n T hT (by simpa [a, c] using hcut))
        calc
          |∫ t in c..T, Real.cos (hardyPhaseReal n t)| ≤ 3 / (m / Real.sqrt (n + 1)) := hbase
          _ = (3 / m) * Real.sqrt (n + 1) := by
                field_simp [hm.ne', (Real.sqrt_pos.2 (by positivity)).ne']
      have hcosEq :
          ∫ t in Ioc a T, HardyEstimatesPartial.hardyCos n t
            = ∫ t in a..T, Real.cos (hardyPhaseReal n t) := by
        rw [← intervalIntegral.integral_of_le hstart]
        refine intervalIntegral.integral_congr ?_
        intro t ht
        simp [HardyEstimatesPartial.hardyCos, hardyPhaseReal]
      calc
        |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
            HardyEstimatesPartial.hardyCos n t|
            = |∫ t in a..T, Real.cos (hardyPhaseReal n t)| := by
                simpa [a] using congrArg abs hcosEq
        _ = |(∫ t in a..c, Real.cos (hardyPhaseReal n t))
              + (∫ t in c..T, Real.cos (hardyPhaseReal n t))| := by
                rw [hsplit]
        _ ≤ |∫ t in a..c, Real.cos (hardyPhaseReal n t)|
              + |∫ t in c..T, Real.cos (hardyPhaseReal n t)| := by
                exact abs_add_le _ _
        _ ≤ Real.sqrt (n + 1) + (3 / m) * Real.sqrt (n + 1) := by
              exact add_le_add hNear hTail
        _ = (1 + 3 / m) * Real.sqrt (n + 1) := by ring
    · have hcut' : T ≤ c := le_of_not_ge hcut
      have hShort :
          |∫ t in a..T, Real.cos (hardyPhaseReal n t)| ≤ Real.sqrt (n + 1) := by
        have hShortAbs :
            |∫ t in a..T, Real.cos (hardyPhaseReal n t)|
              ≤ ∫ t in a..T, |Real.cos (hardyPhaseReal n t)| := by
          simpa [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_integral_norm
              (f := fun t : ℝ => Real.cos (hardyPhaseReal n t)) hstart)
        calc
          |∫ t in a..T, Real.cos (hardyPhaseReal n t)|
              ≤ ∫ t in a..T, |Real.cos (hardyPhaseReal n t)| := hShortAbs
          _ ≤ ∫ t in a..T, (1 : ℝ) := by
                refine intervalIntegral.integral_mono_on hstart
                  ?_ ?_ ?_
                · exact (continuous_abs.comp
                    (Real.continuous_cos.comp (hPhaseDiff n).continuous)).intervalIntegrable _ _
                · exact (continuous_const).intervalIntegrable _ _
                · intro t ht
                  exact Real.abs_cos_le_one _
          _ = T - a := by simp
          _ ≤ c - a := by exact sub_le_sub_right hcut' a
          _ = Real.sqrt (n + 1) := by simp [c]
      have hDivNonneg : 0 ≤ 3 / m := by
        exact div_nonneg (by positivity) (le_of_lt hm)
      have hOneLe : (1 : ℝ) ≤ 1 + 3 / m := by
        linarith
      have hcosEq :
          ∫ t in Ioc a T, HardyEstimatesPartial.hardyCos n t
            = ∫ t in a..T, Real.cos (hardyPhaseReal n t) := by
        rw [← intervalIntegral.integral_of_le hstart]
        refine intervalIntegral.integral_congr ?_
        intro t ht
        simp [HardyEstimatesPartial.hardyCos, hardyPhaseReal]
      calc
        |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
            HardyEstimatesPartial.hardyCos n t|
            = |∫ t in a..T, Real.cos (hardyPhaseReal n t)| := by
                simpa [a] using congrArg abs hcosEq
        _ ≤ Real.sqrt (n + 1) := hShort
        _ = (1 : ℝ) * Real.sqrt (n + 1) := by ring
        _ ≤ (1 + 3 / m) * Real.sqrt (n + 1) := by
              exact mul_le_mul_of_nonneg_right hOneLe (Real.sqrt_nonneg _)
  · have hEmpty : Ioc a T = ∅ := by
      ext t
      constructor
      · intro ht
        exact hstart (le_trans (le_of_lt ht.1) ht.2)
      · intro ht
        exact False.elim ht
    have hZero :
        ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
          HardyEstimatesPartial.hardyCos n t = 0 := by
      simp [a, hEmpty]
    rw [hZero, abs_zero]
    exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

theorem hardyCosIntegralUniformBound_of_vdc
    [HardyExpPhaseVdcEndpointBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionBoundOnSupportHyp]
    [HardyExpPhaseVdcCalculusOnSupportHyp] :
    HardyCosIntegralUniformBoundHyp := by
  infer_instance

/-- Same as `hardyCosIntegralUniformBound_of_vdc`, but with endpoint/correction
inputs discharged by derivative-lower and correction-L¹ bounds. -/
theorem hardyCosIntegralUniformBound_of_derivLower_correctionNorm_calculus
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp]
    [HardyExpPhaseVdcCalculusOnSupportHyp] :
    HardyCosIntegralUniformBoundHyp := by
  infer_instance

theorem hardyCosIntegralUniformBound_of_hardyTheta_classes
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp] :
    HardyCosIntegralUniformBoundHyp := by
  infer_instance

instance [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionIntervalIntegrableOnSupportHyp] :
    HardyCosIntegralUniformBoundHyp := by
  exact hardyCosIntegralUniformBound_of_hardyTheta_classes

/-- Hardy cosine integral uniform bound from the core phase classes plus
second-derivative decay. -/
theorem hardyCosIntegralUniformBound_of_hardyTheta_secondDeriv_classes
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    HardyCosIntegralUniformBoundHyp := by
  infer_instance

instance (priority := 900) [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerBoundOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    HardyCosIntegralUniformBoundHyp := by
  exact hardyCosIntegralUniformBound_of_hardyTheta_secondDeriv_classes

/-- Mode-sensitive cosine-integral control from the phase-calculus route:
`|phase'| ≳ 1/√(n+1)` together with correction `L¹` control on support implies
`|∫ hardyCos_n| ≲ √(n+1)`. -/
theorem hardyCosIntegralSqrtModeBound_of_derivLowerSqrt_correctionNorm
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp] :
    HardyCosIntegralSqrtModeBoundHyp := by
  let _ : HardyExpPhaseVdcSqrtModeOnSupportHyp := inferInstance
  infer_instance

instance (priority := 900) [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp] :
    HardyCosIntegralSqrtModeBoundHyp := by
  exact hardyCosIntegralSqrtModeBound_of_derivLowerSqrt_correctionNorm

/-- Stationary-phase cancellation input for weighted mode integrals:
after applying the Hardy coefficient `(n+1)^(-1/2)`, each mode decomposes into
an alternating `√(n+1)` principal term (with fixed coefficient `A`) plus a
uniformly bounded error. -/
class HardyCosIntegralAlternatingSqrtDecompositionHyp : Prop where
  bound :
    ∃ A B : ℝ, B > 0 ∧ ∀ T : ℝ, T ≥ 2 →
      ∃ err : ℕ → ℝ,
        (∀ n : ℕ, n < HardyEstimatesPartial.hardyN T →
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
              HardyEstimatesPartial.hardyCos n t
            = A * ((-1 : ℝ) ^ n * Real.sqrt (n + 1)) + err n) ∧
        (∀ n : ℕ, n < HardyEstimatesPartial.hardyN T → |err n| ≤ B)

/-- Any mode-sensitive cosine bound can be packaged as an alternating
decomposition by taking zero main amplitude (`A = 0`) and absorbing each mode
into the bounded error term. -/
theorem hardyCosIntegralAlternatingSqrtDecomposition_of_sqrtMode
    (hcos :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
            HardyEstimatesPartial.hardyCos n t| ≤ B * Real.sqrt (n + 1)) :
    HardyCosIntegralAlternatingSqrtDecompositionHyp := by
  obtain ⟨B, hB, hcosB⟩ := hcos
  refine ⟨0, B, hB, ?_⟩
  intro T hT
  let err : ℕ → ℝ := fun n =>
    ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
      ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
        HardyEstimatesPartial.hardyCos n t
  refine ⟨err, ?_, ?_⟩
  · intro n hn
    simp [err]
  · intro n hn
    have hcoef_nonneg : 0 ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have hI :
        |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
            HardyEstimatesPartial.hardyCos n t| ≤ B * Real.sqrt (n + 1) :=
      hcosB n T hT
    have hcoef_sqrt_eq_one :
        (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (n + 1) = 1 := by
      have hbase_pos : 0 < (n + 1 : ℝ) := by positivity
      calc
        (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (n + 1)
            = (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * (n + 1 : ℝ) ^ (1 / 2 : ℝ) := by
                rw [Real.sqrt_eq_rpow]
        _ = (n + 1 : ℝ) ^ ((-(1 / 2 : ℝ)) + (1 / 2 : ℝ)) := by
              rw [← Real.rpow_add hbase_pos]
        _ = 1 := by norm_num
    calc
      |err n|
          = |((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
              ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
                HardyEstimatesPartial.hardyCos n t| := by
              rfl
      _ = (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
              HardyEstimatesPartial.hardyCos n t| := by
            rw [abs_mul, abs_of_nonneg hcoef_nonneg]
      _ ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * (B * Real.sqrt (n + 1)) := by
            exact mul_le_mul_of_nonneg_left hI hcoef_nonneg
      _ = B * ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (n + 1)) := by ring
      _ = B * 1 := by rw [hcoef_sqrt_eq_one]
      _ = B := by ring

instance [HardyCosIntegralSqrtModeBoundHyp] :
    HardyCosIntegralAlternatingSqrtDecompositionHyp := by
  exact hardyCosIntegralAlternatingSqrtDecomposition_of_sqrtMode
    HardyCosIntegralSqrtModeBoundHyp.bound

lemma alternating_sqrt_sum_bound_range (N : ℕ) :
    |∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt (n + 1)| ≤ Real.sqrt N := by
  cases N with
  | zero =>
      simp
  | succ k =>
      simpa using CosPiSqSign.alternating_sqrt_sum_bound k

/-- Alternating stationary-phase decomposition implies the main-term first
moment bound at scale `T^(1/2+ε)`. -/
theorem mainTermFirstMomentBound_of_alternatingSqrtDecomposition
    (hdec :
      ∃ A B : ℝ, B > 0 ∧ ∀ T : ℝ, T ≥ 2 →
        ∃ err : ℕ → ℝ,
          (∀ n : ℕ, n < HardyEstimatesPartial.hardyN T →
            ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
              ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
                HardyEstimatesPartial.hardyCos n t
              = A * ((-1 : ℝ) ^ n * Real.sqrt (n + 1)) + err n) ∧
          (∀ n : ℕ, n < HardyEstimatesPartial.hardyN T → |err n| ≤ B)) :
    MainTermFirstMomentBoundHyp := by
  obtain ⟨A, B, hB, hdecB⟩ := hdec
  refine ⟨?_⟩
  intro ε hε
  refine ⟨4 * (|A| + B + 1), by positivity, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hMainInt :
      ∫ t in Ioc 1 T, HardyEstimatesPartial.MainTerm t =
        HardyEstimatesPartial.hardySumInt T := by
    calc
      ∫ t in Ioc 1 T, HardyEstimatesPartial.MainTerm t
          = ∫ t in Ioc 1 T, HardyEstimatesPartial.hardySum t := by
              simp [HardyEstimatesPartial.MainTerm_eq_hardySum]
      _ = HardyEstimatesPartial.hardySumInt T := by
            simpa using HardyEstimatesPartial.hardySum_integral_eq T hT1
  obtain ⟨err, hrepr, herr⟩ := hdecB T hT
  let N : ℕ := HardyEstimatesPartial.hardyN T
  set S : ℝ :=
    ∑ n ∈ Finset.range N,
      ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
        ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
          HardyEstimatesPartial.hardyCos n t
  have hSdef : HardyEstimatesPartial.hardySumInt T = 2 * S := by
    simp [S, HardyEstimatesPartial.hardySumInt, N]
  have hS_repr :
      S =
        A * (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt (n + 1))
          + ∑ n ∈ Finset.range N, err n := by
    unfold S
    calc
      ∑ n ∈ Finset.range N,
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
              HardyEstimatesPartial.hardyCos n t
          = ∑ n ∈ Finset.range N,
              (A * ((-1 : ℝ) ^ n * Real.sqrt (n + 1)) + err n) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              have hnlt : n < HardyEstimatesPartial.hardyN T := by
                simpa [N] using Finset.mem_range.mp hn
              exact hrepr n hnlt
      _ = (∑ n ∈ Finset.range N, A * ((-1 : ℝ) ^ n * Real.sqrt (n + 1)))
            + ∑ n ∈ Finset.range N, err n := by
              rw [Finset.sum_add_distrib]
      _ = A * (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt (n + 1))
            + ∑ n ∈ Finset.range N, err n := by
              rw [← Finset.mul_sum]
  have hAltBase :
      |∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt (n + 1)| ≤ Real.sqrt N :=
    alternating_sqrt_sum_bound_range N
  have hAltBound :
      |A * (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt (n + 1))|
        ≤ |A| * Real.sqrt N := by
    calc
      |A * (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt (n + 1))|
          = |A| *
              |∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt (n + 1)| := by
                rw [abs_mul]
      _ ≤ |A| * Real.sqrt N := by
            exact mul_le_mul_of_nonneg_left hAltBase (abs_nonneg A)
  have hErrBound :
      |∑ n ∈ Finset.range N, err n| ≤ (N : ℝ) * B := by
    calc
      |∑ n ∈ Finset.range N, err n|
          ≤ ∑ n ∈ Finset.range N, |err n| := by
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range N, B := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hnlt : n < HardyEstimatesPartial.hardyN T := by
            simpa [N] using Finset.mem_range.mp hn
          exact herr n hnlt
      _ = (N : ℝ) * B := by simp [mul_comm]
  have hSbound : |S| ≤ (|A| + B + 1) * ((N : ℝ) + 1) := by
    rw [hS_repr]
    calc
      |A * (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt (n + 1))
          + ∑ n ∈ Finset.range N, err n|
          ≤ |A * (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt (n + 1))|
              + |∑ n ∈ Finset.range N, err n| := by
                exact abs_add_le _ _
      _ ≤ |A| * Real.sqrt N + ((N : ℝ) * B) := add_le_add hAltBound hErrBound
      _ ≤ |A| * ((N : ℝ) + 1) + ((N : ℝ) * B) := by
          gcongr
          have hNnn : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
          nlinarith [Real.sq_sqrt hNnn]
      _ ≤ (|A| + B + 1) * ((N : ℝ) + 1) := by
          have hNnn : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
          nlinarith [hNnn, abs_nonneg A, hB]
  have hN_le : (N : ℝ) ≤ T ^ (1 / 2 + ε) := by
    have hN_floor :
        (N : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) := by
      simpa [N] using Nat.floor_le (Real.sqrt_nonneg (T / (2 * Real.pi)))
    have hdiv_le : T / (2 * Real.pi) ≤ T := by
      have hTnn : 0 ≤ T := by linarith
      have hden_ge_one : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      have hdiv' : T / (2 * Real.pi) ≤ T / 1 := by
        exact div_le_div_of_nonneg_left hTnn (by positivity : (0 : ℝ) < 1) hden_ge_one
      simpa using hdiv'
    have hsqrt_le : Real.sqrt (T / (2 * Real.pi)) ≤ Real.sqrt T := Real.sqrt_le_sqrt hdiv_le
    have hpow_mono : T ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 + ε) := by
      exact Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ T) (by linarith)
    calc
      (N : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) := hN_floor
      _ ≤ Real.sqrt T := hsqrt_le
      _ = T ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ ≤ T ^ (1 / 2 + ε) := hpow_mono
  have hpow_ge_one : (1 : ℝ) ≤ T ^ (1 / 2 + ε) := by
    exact Real.one_le_rpow (by linarith : (1 : ℝ) ≤ T) (by linarith : 0 ≤ (1 / 2 : ℝ) + ε)
  have hNplusOne_le : (N : ℝ) + 1 ≤ 2 * T ^ (1 / 2 + ε) := by
    nlinarith [hN_le, hpow_ge_one]
  have hSumIntBound :
      |HardyEstimatesPartial.hardySumInt T|
        ≤ (4 * (|A| + B + 1)) * T ^ (1 / 2 + ε) := by
    calc
      |HardyEstimatesPartial.hardySumInt T|
          = 2 * |S| := by
              rw [hSdef, abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ 2 * ((|A| + B + 1) * ((N : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left hSbound (by positivity)
      _ ≤ 2 * ((|A| + B + 1) * (2 * T ^ (1 / 2 + ε))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hNplusOne_le (by positivity))
            (by positivity)
      _ = (4 * (|A| + B + 1)) * T ^ (1 / 2 + ε) := by ring
  simpa [hMainInt] using hSumIntBound

instance [HardyCosIntegralAlternatingSqrtDecompositionHyp] :
    MainTermFirstMomentBoundHyp := by
  exact mainTermFirstMomentBound_of_alternatingSqrtDecomposition
    HardyCosIntegralAlternatingSqrtDecompositionHyp.bound

/-- `√(n+1)` mode-growth for cosine integrals is enough for the main-term
first-moment bound at scale `T^(1/2+ε)`, because the Hardy coefficient
`(n+1)^(-1/2)` cancels the mode growth. -/
theorem mainTermFirstMomentBound_of_sqrtMode_hardyCosIntegral
    (hcos :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
            HardyEstimatesPartial.hardyCos n t| ≤ B * Real.sqrt (n + 1)) :
    MainTermFirstMomentBoundHyp := by
  obtain ⟨B, hB, hcosB⟩ := hcos
  refine ⟨?_⟩
  intro ε hε
  refine ⟨2 * B, by positivity, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hMainInt :
      ∫ t in Ioc 1 T, HardyEstimatesPartial.MainTerm t =
        HardyEstimatesPartial.hardySumInt T := by
    calc
      ∫ t in Ioc 1 T, HardyEstimatesPartial.MainTerm t
          = ∫ t in Ioc 1 T, HardyEstimatesPartial.hardySum t := by
              simp [HardyEstimatesPartial.MainTerm_eq_hardySum]
      _ = HardyEstimatesPartial.hardySumInt T := by
            simpa using HardyEstimatesPartial.hardySum_integral_eq T hT1
  set S : ℝ :=
    ∑ n ∈ Finset.range (HardyEstimatesPartial.hardyN T),
      ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
        ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
          HardyEstimatesPartial.hardyCos n t
  have hSdef : HardyEstimatesPartial.hardySumInt T = 2 * S := by
    simp [S, HardyEstimatesPartial.hardySumInt]
  have hSboundAux :
      |∑ n ∈ Finset.range (HardyEstimatesPartial.hardyN T),
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
              HardyEstimatesPartial.hardyCos n t|
        ≤ (HardyEstimatesPartial.hardyN T : ℝ) * B := by
    calc
      |∑ n ∈ Finset.range (HardyEstimatesPartial.hardyN T),
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
              HardyEstimatesPartial.hardyCos n t|
          ≤ ∑ n ∈ Finset.range (HardyEstimatesPartial.hardyN T),
              |((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
                ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
                  HardyEstimatesPartial.hardyCos n t| := by
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range (HardyEstimatesPartial.hardyN T), B := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hcoef_nonneg : 0 ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
          have hI :
              |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
                  HardyEstimatesPartial.hardyCos n t| ≤ B * Real.sqrt (n + 1) :=
            hcosB n T hT
          have hcoef_sqrt_eq_one :
              (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (n + 1) = 1 := by
            have hbase_pos : 0 < (n + 1 : ℝ) := by positivity
            calc
              (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (n + 1)
                  = (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * (n + 1 : ℝ) ^ (1 / 2 : ℝ) := by
                      rw [Real.sqrt_eq_rpow]
              _ = (n + 1 : ℝ) ^ ((-(1 / 2 : ℝ)) + (1 / 2 : ℝ)) := by
                    rw [← Real.rpow_add hbase_pos]
              _ = 1 := by norm_num
          calc
            |((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
                ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
                  HardyEstimatesPartial.hardyCos n t|
                = (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
                    |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
                      HardyEstimatesPartial.hardyCos n t| := by
                        rw [abs_mul, abs_of_nonneg hcoef_nonneg]
            _ ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * (B * Real.sqrt (n + 1)) := by
                exact mul_le_mul_of_nonneg_left hI hcoef_nonneg
            _ = B * ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (n + 1)) := by ring
            _ = B * 1 := by rw [hcoef_sqrt_eq_one]
            _ = B := by ring
      _ = (HardyEstimatesPartial.hardyN T : ℝ) * B := by
          simp [mul_comm]
  have hSbound : |S| ≤ (HardyEstimatesPartial.hardyN T : ℝ) * B := by
    simpa [S] using hSboundAux
  have hN_le : (HardyEstimatesPartial.hardyN T : ℝ) ≤ T ^ (1 / 2 + ε) := by
    have hN_floor :
        (HardyEstimatesPartial.hardyN T : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) := by
      exact Nat.floor_le (Real.sqrt_nonneg _)
    have hdiv_le : T / (2 * Real.pi) ≤ T := by
      have hTnn : 0 ≤ T := by linarith
      have hden_ge_one : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      have hdiv' : T / (2 * Real.pi) ≤ T / 1 := by
        exact div_le_div_of_nonneg_left hTnn (by positivity : (0 : ℝ) < 1) hden_ge_one
      simpa using hdiv'
    have hsqrt_le : Real.sqrt (T / (2 * Real.pi)) ≤ Real.sqrt T := Real.sqrt_le_sqrt hdiv_le
    have hpow_mono : T ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 + ε) := by
      exact Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ T) (by linarith)
    calc
      (HardyEstimatesPartial.hardyN T : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) := hN_floor
      _ ≤ Real.sqrt T := hsqrt_le
      _ = T ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ ≤ T ^ (1 / 2 + ε) := hpow_mono
  have hSumIntBound :
      |HardyEstimatesPartial.hardySumInt T| ≤ (2 * B) * T ^ (1 / 2 + ε) := by
    calc
      |HardyEstimatesPartial.hardySumInt T|
          = 2 * |S| := by
              rw [hSdef, abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ 2 * ((HardyEstimatesPartial.hardyN T : ℝ) * B) := by
          exact mul_le_mul_of_nonneg_left hSbound (by positivity)
      _ = (2 * B) * (HardyEstimatesPartial.hardyN T : ℝ) := by ring
      _ ≤ (2 * B) * T ^ (1 / 2 + ε) := by
          exact mul_le_mul_of_nonneg_left hN_le (by positivity)
  simpa [hMainInt] using hSumIntBound

/-- Uniformly bounded cosine integrals imply the `MainTerm` first-moment bound
at scale `T^(1/2+ε)`. -/
theorem mainTermFirstMomentBound_of_uniform_hardyCosIntegral
    (hcos :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
            HardyEstimatesPartial.hardyCos n t| ≤ B) :
    MainTermFirstMomentBoundHyp := by
  obtain ⟨B, hB, hcosB⟩ := hcos
  refine ⟨?_⟩
  intro ε hε
  refine ⟨2 * B, by positivity, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hMainInt :
      ∫ t in Ioc 1 T, HardyEstimatesPartial.MainTerm t =
        HardyEstimatesPartial.hardySumInt T := by
    calc
      ∫ t in Ioc 1 T, HardyEstimatesPartial.MainTerm t
          = ∫ t in Ioc 1 T, HardyEstimatesPartial.hardySum t := by
              simp [HardyEstimatesPartial.MainTerm_eq_hardySum]
      _ = HardyEstimatesPartial.hardySumInt T := by
            simpa using HardyEstimatesPartial.hardySum_integral_eq T hT1
  set S : ℝ :=
    ∑ n ∈ Finset.range (HardyEstimatesPartial.hardyN T),
      ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
        ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
          HardyEstimatesPartial.hardyCos n t
  have hSdef : HardyEstimatesPartial.hardySumInt T = 2 * S := by
    simp [S, HardyEstimatesPartial.hardySumInt]
  have hSboundAux :
      |∑ n ∈ Finset.range (HardyEstimatesPartial.hardyN T),
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
              HardyEstimatesPartial.hardyCos n t|
        ≤ (HardyEstimatesPartial.hardyN T : ℝ) * B := by
    calc
      |∑ n ∈ Finset.range (HardyEstimatesPartial.hardyN T),
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
              HardyEstimatesPartial.hardyCos n t|
          ≤ ∑ n ∈ Finset.range (HardyEstimatesPartial.hardyN T),
              |((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
                ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
                  HardyEstimatesPartial.hardyCos n t| := by
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range (HardyEstimatesPartial.hardyN T), B := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hcoef_nonneg : 0 ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
          have hcoef_le_one : (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
            refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by norm_num)
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          have hI :
              |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
                  HardyEstimatesPartial.hardyCos n t| ≤ B :=
            hcosB n T hT
          calc
            |((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
                ∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
                  HardyEstimatesPartial.hardyCos n t|
                = (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
                    |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
                      HardyEstimatesPartial.hardyCos n t| := by
                        rw [abs_mul, abs_of_nonneg hcoef_nonneg]
            _ ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * B := by
                exact mul_le_mul_of_nonneg_left hI hcoef_nonneg
            _ ≤ 1 * B := by
                exact mul_le_mul_of_nonneg_right hcoef_le_one (le_of_lt hB)
            _ = B := by ring
      _ = (HardyEstimatesPartial.hardyN T : ℝ) * B := by
          simp [mul_comm]
  have hSbound : |S| ≤ (HardyEstimatesPartial.hardyN T : ℝ) * B := by
    simpa [S] using hSboundAux
  have hN_le : (HardyEstimatesPartial.hardyN T : ℝ) ≤ T ^ (1 / 2 + ε) := by
    have hN_floor :
        (HardyEstimatesPartial.hardyN T : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) := by
      exact Nat.floor_le (Real.sqrt_nonneg _)
    have hdiv_le : T / (2 * Real.pi) ≤ T := by
      have hTnn : 0 ≤ T := by linarith
      have hden_ge_one : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      have hdiv' : T / (2 * Real.pi) ≤ T / 1 := by
        exact div_le_div_of_nonneg_left hTnn (by positivity : (0 : ℝ) < 1) hden_ge_one
      simpa using hdiv'
    have hsqrt_le : Real.sqrt (T / (2 * Real.pi)) ≤ Real.sqrt T := Real.sqrt_le_sqrt hdiv_le
    have hpow_mono : T ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 + ε) := by
      exact Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ T) (by linarith)
    calc
      (HardyEstimatesPartial.hardyN T : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) := hN_floor
      _ ≤ Real.sqrt T := hsqrt_le
      _ = T ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ ≤ T ^ (1 / 2 + ε) := hpow_mono
  have hSumIntBound :
      |HardyEstimatesPartial.hardySumInt T| ≤ (2 * B) * T ^ (1 / 2 + ε) := by
    calc
      |HardyEstimatesPartial.hardySumInt T|
          = 2 * |S| := by
              rw [hSdef, abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ 2 * ((HardyEstimatesPartial.hardyN T : ℝ) * B) := by
          exact mul_le_mul_of_nonneg_left hSbound (by positivity)
      _ = (2 * B) * (HardyEstimatesPartial.hardyN T : ℝ) := by ring
      _ ≤ (2 * B) * T ^ (1 / 2 + ε) := by
          exact mul_le_mul_of_nonneg_left hN_le (by positivity)
  simpa [hMainInt] using hSumIntBound

instance [HardyCosIntegralUniformBoundHyp] : MainTermFirstMomentBoundHyp := by
  exact mainTermFirstMomentBound_of_uniform_hardyCosIntegral
    HardyCosIntegralUniformBoundHyp.bound

instance [HardyCosIntegralSqrtModeBoundHyp] : MainTermFirstMomentBoundHyp := by
  exact mainTermFirstMomentBound_of_sqrtMode_hardyCosIntegral
    HardyCosIntegralSqrtModeBoundHyp.bound

/-- If the two remaining integral bounds are available, the Hardy first-moment hypothesis follows. -/
theorem hardyFirstMomentUpper_from_two_bounds
    [MainTermFirstMomentBoundHyp] [ErrorTermFirstMomentBoundHyp] :
    HardyFirstMomentUpperHyp := by
  refine ⟨?_⟩
  intro ε hε
  obtain ⟨C₁, hC₁, hMain⟩ := MainTermFirstMomentBoundHyp.bound ε hε
  obtain ⟨C₂, hC₂, hErr⟩ := ErrorTermFirstMomentBoundHyp.bound ε hε
  obtain ⟨C, hC, T₀, hT₀, hHardy⟩ :=
    HardyEstimatesPartial.hardyZ_first_moment_bound_conditional_two_bounds ε hε
      ⟨C₁, hC₁, hMain⟩ ⟨C₂, hC₂, hErr⟩
  refine ⟨C, hC, max 2 T₀, le_max_left _ _, ?_⟩
  intro T hT
  exact hHardy T (le_trans (le_max_right _ _) hT)

/-! Direct closure routes for the Hardy first moment.

These theorems package common instance-search chains so downstream modules can
target the highest-leverage analytic obligations directly (for example, a
support-level oscillatory bound for `hardyExpPhase` plus an error-term bound),
without manually reassembling intermediate typeclasses.
-/

/-- Direct route:
`HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp` + `ErrorTermFirstMomentBoundHyp`
imply `HardyFirstMomentUpperHyp`. -/
theorem hardyFirstMomentUpper_from_expPhaseInterval_onSupport_and_error
    [HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp]
    [ErrorTermFirstMomentBoundHyp] :
    HardyFirstMomentUpperHyp := by
  let _ : HardyExpPhaseIntegralUniformBoundHyp := inferInstance
  let _ : HardyCosIntegralUniformBoundHyp := inferInstance
  let _ : MainTermFirstMomentBoundHyp := inferInstance
  exact hardyFirstMomentUpper_from_two_bounds

/-- Variant of
`hardyFirstMomentUpper_from_expPhaseInterval_onSupport_and_error`
that uses the stronger pointwise remainder input
`ErrorTermPointwiseInvSqrtBoundHyp`. -/
theorem hardyFirstMomentUpper_from_expPhaseInterval_onSupport_and_errorPointwiseInvSqrt
    [HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp]
    [ErrorTermPointwiseInvSqrtBoundHyp] :
    HardyFirstMomentUpperHyp := by
  let _ : ErrorTermFirstMomentBoundHyp := inferInstance
  exact hardyFirstMomentUpper_from_expPhaseInterval_onSupport_and_error

/-- Mode-sensitive direct route:
`HardyTheta` differentiability + `phase'` differentiability + a
`1/√(n+1)` lower bound for the phase gap + correction `L¹` control imply the
main-term bound via VdC and therefore `HardyFirstMomentUpperHyp` once the error
term first-moment bound is available. -/
theorem hardyFirstMomentUpper_from_derivLowerSqrt_correctionNorm_and_error
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp]
    [ErrorTermFirstMomentBoundHyp] :
    HardyFirstMomentUpperHyp := by
  let _ : HardyCosIntegralSqrtModeBoundHyp := inferInstance
  let _ : MainTermFirstMomentBoundHyp := inferInstance
  exact hardyFirstMomentUpper_from_two_bounds

/-- Variant of
`hardyFirstMomentUpper_from_derivLowerSqrt_correctionNorm_and_error`
using the stronger pointwise Hardy remainder hypothesis. -/
theorem hardyFirstMomentUpper_from_derivLowerSqrt_correctionNorm_and_errorPointwiseInvSqrt
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp]
    [ErrorTermPointwiseInvSqrtBoundHyp] :
    HardyFirstMomentUpperHyp := by
  let _ : ErrorTermFirstMomentBoundHyp := inferInstance
  exact hardyFirstMomentUpper_from_derivLowerSqrt_correctionNorm_and_error

instance [MainTermFirstMomentBoundHyp] [ErrorTermFirstMomentBoundHyp] :
    HardyFirstMomentUpperHyp := by
  exact hardyFirstMomentUpper_from_two_bounds

instance (priority := 920)
    [HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp]
    [ErrorTermFirstMomentBoundHyp] :
    HardyFirstMomentUpperHyp := by
  exact hardyFirstMomentUpper_from_expPhaseInterval_onSupport_and_error

instance (priority := 910)
    [HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp]
    [ErrorTermPointwiseInvSqrtBoundHyp] :
    HardyFirstMomentUpperHyp := by
  exact hardyFirstMomentUpper_from_expPhaseInterval_onSupport_and_errorPointwiseInvSqrt

instance (priority := 905)
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp]
    [ErrorTermFirstMomentBoundHyp] :
    HardyFirstMomentUpperHyp := by
  exact hardyFirstMomentUpper_from_derivLowerSqrt_correctionNorm_and_error

instance (priority := 904)
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp]
    [HardyExpPhaseVdcCorrectionNormIntegralBoundOnSupportHyp]
    [ErrorTermPointwiseInvSqrtBoundHyp] :
    HardyFirstMomentUpperHyp := by
  exact hardyFirstMomentUpper_from_derivLowerSqrt_correctionNorm_and_errorPointwiseInvSqrt

end HardyFirstMomentWiring
