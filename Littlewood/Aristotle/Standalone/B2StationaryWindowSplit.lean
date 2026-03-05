import Mathlib
import Littlewood.Aristotle.HardyCosSmooth
import Littlewood.Aristotle.Standalone.B2MainTermFirstMomentExact

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.B2StationaryWindowSplit

open MeasureTheory Set
open HardyEstimatesPartial

/-- Short-interval (`[hardyStart n, min(T, hardyStart n + sqrt(n+1))]`) mode bound. -/
def B2HardyCosNearWindowPayload : Prop :=
  ∃ Bnear > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
    |∫ t in Ioc (hardyStart n) (min T (hardyStart n + Real.sqrt (n + 1))), hardyCos n t|
      ≤ Bnear * Real.sqrt (n + 1)

/-- Tail-interval (`[min(T, hardyStart n + sqrt(n+1)), T]`) mode bound. -/
def B2HardyCosTailWindowPayload : Prop :=
  ∃ Btail > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
    |∫ t in Ioc (min T (hardyStart n + Real.sqrt (n + 1))) T, hardyCos n t|
      ≤ Btail * Real.sqrt (n + 1)

/-- Build the tail-window cosine payload from a tail-window `hardyExpPhase` norm bound. -/
theorem tailWindowPayload_of_hardyExpPhaseTailBound
    (hTailExp :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ‖∫ t in (hardyStart n + Real.sqrt (n + 1))..T,
            HardyFirstMomentWiring.hardyExpPhase n t‖ ≤ B * Real.sqrt (n + 1)) :
    B2HardyCosTailWindowPayload := by
  rcases hTailExp with ⟨B, hB, hTailB⟩
  refine ⟨B, hB, ?_⟩
  intro n T hT
  let c : ℝ := min T (hardyStart n + Real.sqrt (n + 1))
  by_cases hcut : hardyStart n + Real.sqrt (n + 1) ≤ T
  · have hc_eq : c = hardyStart n + Real.sqrt (n + 1) := by
      unfold c
      exact min_eq_right hcut
    calc
      |∫ t in Ioc (min T (hardyStart n + Real.sqrt (n + 1))) T, hardyCos n t|
          = |(∫ t in Ioc c T, HardyFirstMomentWiring.hardyExpPhase n t).re| := by
              rw [HardyFirstMomentWiring.hardyCosIntegral_eq_re_hardyExpPhaseIntegral]
      _ ≤ ‖∫ t in Ioc c T, HardyFirstMomentWiring.hardyExpPhase n t‖ := Complex.abs_re_le_norm _
      _ = ‖∫ t in c..T, HardyFirstMomentWiring.hardyExpPhase n t‖ := by
            have hc_le_T : c ≤ T := by
              unfold c
              exact min_le_left _ _
            rw [← intervalIntegral.integral_of_le
              (f := HardyFirstMomentWiring.hardyExpPhase n) hc_le_T]
      _ = ‖∫ t in (hardyStart n + Real.sqrt (n + 1))..T,
            HardyFirstMomentWiring.hardyExpPhase n t‖ := by
            simp [c, hc_eq]
      _ ≤ B * Real.sqrt (n + 1) := hTailB n T hT hcut
  · have hc_eq : c = T := by
      unfold c
      exact min_eq_left (le_of_not_ge hcut)
    calc
      |∫ t in Ioc (min T (hardyStart n + Real.sqrt (n + 1))) T, hardyCos n t|
          = |∫ t in Ioc T T, hardyCos n t| := by simp [c, hc_eq]
      _ = 0 := by simp
      _ ≤ B * Real.sqrt (n + 1) := by
            have hBnn : 0 ≤ B := le_of_lt hB
            exact mul_nonneg hBnn (Real.sqrt_nonneg _)

/-- Class-based specialization of `tailWindowPayload_of_hardyExpPhaseTailBound`. -/
theorem tailWindowPayload_of_stationaryTailClass
    [HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp] :
    B2HardyCosTailWindowPayload := by
  exact
    tailWindowPayload_of_hardyExpPhaseTailBound
      HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp.bound

/-- Recombine short-window and tail-window mode bounds into the canonical B2 payload. -/
theorem payload_of_near_and_tail
    (hNear : B2HardyCosNearWindowPayload)
    (hTail : B2HardyCosTailWindowPayload) :
    Aristotle.Standalone.B2MainTermFirstMomentExact.B2HardyCosSqrtPayload := by
  rcases hNear with ⟨Bnear, hBnear, hNearB⟩
  rcases hTail with ⟨Btail, hBtail, hTailB⟩
  refine ⟨Bnear + Btail, by linarith [hBnear, hBtail], ?_⟩
  intro n T hT
  let c : ℝ := min T (hardyStart n + Real.sqrt (n + 1))
  by_cases hstart : hardyStart n ≤ T
  · have hstart_le_c : hardyStart n ≤ c := by
      unfold c
      exact le_min hstart (le_add_of_nonneg_right (Real.sqrt_nonneg _))
    have hc_le_T : c ≤ T := by
      unfold c
      exact min_le_left _ _
    have hInt_near : IntervalIntegrable (hardyCos n) volume (hardyStart n) c :=
      HardyCosSmooth.intervalIntegrable_hardyCos n (hardyStart n) c
    have hInt_tail : IntervalIntegrable (hardyCos n) volume c T :=
      HardyCosSmooth.intervalIntegrable_hardyCos n c T
    have hsplit :
        ∫ t in Ioc (hardyStart n) T, hardyCos n t
          = (∫ t in Ioc (hardyStart n) c, hardyCos n t)
            + (∫ t in Ioc c T, hardyCos n t) := by
      rw [← intervalIntegral.integral_of_le (f := hardyCos n) hstart,
          ← intervalIntegral.integral_of_le (f := hardyCos n) hstart_le_c,
          ← intervalIntegral.integral_of_le (f := hardyCos n) hc_le_T]
      simpa using
        (intervalIntegral.integral_add_adjacent_intervals (f := hardyCos n) hInt_near hInt_tail).symm
    have hNear' : |∫ t in Ioc (hardyStart n) c, hardyCos n t| ≤ Bnear * Real.sqrt (n + 1) := by
      simpa [c] using hNearB n T hT
    have hTail' : |∫ t in Ioc c T, hardyCos n t| ≤ Btail * Real.sqrt (n + 1) := by
      simpa [c] using hTailB n T hT
    calc
      |∫ t in Ioc (hardyStart n) T, hardyCos n t|
          = |(∫ t in Ioc (hardyStart n) c, hardyCos n t) + (∫ t in Ioc c T, hardyCos n t)| := by
              rw [hsplit]
      _ ≤ |∫ t in Ioc (hardyStart n) c, hardyCos n t| + |∫ t in Ioc c T, hardyCos n t| := by
            simpa using
              (norm_add_le
                (∫ t in Ioc (hardyStart n) c, hardyCos n t)
                (∫ t in Ioc c T, hardyCos n t))
      _ ≤ Bnear * Real.sqrt (n + 1) + Btail * Real.sqrt (n + 1) := by gcongr
      _ = (Bnear + Btail) * Real.sqrt (n + 1) := by ring
  · have hmain_zero : ∫ t in Ioc (hardyStart n) T, hardyCos n t = 0 := by
      have hEmpty : Ioc (hardyStart n) T = ∅ := by
        apply Set.Ioc_eq_empty
        intro hlt
        exact hstart (le_of_lt hlt)
      simp [hEmpty]
    rw [hmain_zero, abs_zero]
    have hB_nonneg : 0 ≤ Bnear + Btail := by linarith [hBnear, hBtail]
    exact mul_nonneg hB_nonneg (Real.sqrt_nonneg _)

/-- Convert the split-window B2 payload directly to `MainTermFirstMomentBoundHyp`. -/
theorem mainTermFirstMomentBoundHyp_of_near_and_tail
    (hNear : B2HardyCosNearWindowPayload)
    (hTail : B2HardyCosTailWindowPayload) :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact
    Aristotle.Standalone.B2MainTermFirstMomentExact.mainTermFirstMomentBoundHyp_of_payload
      (payload_of_near_and_tail hNear hTail)

end Aristotle.Standalone.B2StationaryWindowSplit
