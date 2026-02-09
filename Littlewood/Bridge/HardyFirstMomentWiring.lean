import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.VanDerCorputInfra
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

/-- Complex oscillatory phase attached to `hardyCos`. -/
noncomputable def hardyExpPhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (HardyEstimatesPartial.hardyTheta t - t * Real.log (n + 1)))

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

lemma hardyExpPhase_integrableOn_Ioc (n : ℕ) (a b : ℝ) :
    IntegrableOn (hardyExpPhase n) (Ioc a b) := by
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) ?_ ?_ ?_
  · simpa using (Continuous.integrableOn_Ioc (f := fun _ : ℝ => (1 : ℝ)) continuous_const)
  · have hreal :
        Measurable
          (fun t : ℝ => HardyEstimatesPartial.hardyTheta t - t * Real.log (n + 1)) :=
      HardyEstimatesPartial.hardyTheta_measurable.sub (measurable_id.mul_const _)
    let xfun : ℝ → ℝ := fun t => HardyEstimatesPartial.hardyTheta t - t * Real.log (n + 1)
    have hxfun : Measurable xfun := by
      simpa [xfun] using hreal
    have hcomplex :
        Measurable (fun t : ℝ => ((xfun t : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp hxfun
    have harg :
        Measurable
          (fun t : ℝ => Complex.I * ((xfun t : ℝ) : ℂ)) :=
      measurable_const.mul hcomplex
    simpa [hardyExpPhase, xfun] using
      (Complex.continuous_exp.measurable.comp harg).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    simpa [hardyExpPhase_norm] using (le_rfl : (1 : ℝ) ≤ 1)

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

/-- Endpoint-control input for van der Corput integration by parts on the Hardy phase. -/
class HardyExpPhaseVdcEndpointBoundOnSupportHyp : Prop where
  bound :
    ∃ B₀ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ‖hardyVdcPrimitive n T
        - hardyVdcPrimitive n (HardyEstimatesPartial.hardyStart n)‖ ≤ B₀

/-- Correction-integral control input for van der Corput integration by parts
on the Hardy phase. -/
class HardyExpPhaseVdcCorrectionBoundOnSupportHyp : Prop where
  bound :
    ∃ B₁ > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      HardyEstimatesPartial.hardyStart n ≤ T →
      ‖∫ t in HardyEstimatesPartial.hardyStart n..T, hardyVdcCorrection n t‖ ≤ B₁

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
  have haux :=
    Aristotle.VanDerCorput.van_der_corput_deriv_aux
      (f := hardyPhaseReal n) (t := t)
      (hPhaseDiff n T hT hstart t ht)
      (hPhaseDerivDiff n T hT hstart t ht)
      (hPhaseDerivNe n T hT hstart t ht)
  simpa [hardyVdcPrimitive, hardyVdcCorrection, hardyExpPhase_eq_exp_phase,
    mul_assoc, mul_comm, mul_left_comm] using haux

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

instance [HardyExpPhaseVdcOnSupportHyp] :
    HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp := by
  refine hardyExpPhaseIntervalIntegralUniformBoundOnSupport_of_vdc ?_
  exact ⟨HardyExpPhaseVdcOnSupportHyp.endpointBound,
    HardyExpPhaseVdcOnSupportHyp.correctionBound,
    HardyExpPhaseVdcOnSupportHyp.decomposition⟩

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

/-- Optional stronger analytic input for the main term:
uniform boundedness of each oscillatory cosine integral. -/
class HardyCosIntegralUniformBoundHyp : Prop where
  bound :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc (HardyEstimatesPartial.hardyStart n) T,
          HardyEstimatesPartial.hardyCos n t| ≤ B

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

theorem hardyCosIntegralUniformBound_of_vdc
    [HardyExpPhaseVdcEndpointBoundOnSupportHyp]
    [HardyExpPhaseVdcCorrectionBoundOnSupportHyp]
    [HardyExpPhaseVdcCalculusOnSupportHyp] :
    HardyCosIntegralUniformBoundHyp := by
  infer_instance

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

end HardyFirstMomentWiring
