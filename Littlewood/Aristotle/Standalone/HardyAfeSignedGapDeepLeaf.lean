/- 
Delegated deep leaf for B1 (signed AFE mean-square gap).

This file carries the analytic payload:
`(fun T => ∫_1^T (|ζ|² - 2|S_N|²)) = O(T)`.

The main-chain atomic theorem in `HardyAfeSignedGapAtomic.lean` is now a
sorry-free wrapper that references this leaf theorem.
-/

import Littlewood.Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
import Littlewood.Aristotle.Standalone.HardyAfeSignedGapScaffold
import Littlewood.Aristotle.Standalone.HardyAfeSignedGapRootInfra
import Littlewood.Aristotle.Standalone.HardyAfeSignedGapProvider

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyAfeSignedGapDeepLeaf

open Filter Asymptotics MeasureTheory Set
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra

/-- Assembly route for the B1 signed-gap leaf:
critical-line zeta mean-square (`ZetaMeanSquareHalfBound`) plus the partial-zeta
`1/2 * T log T + O(T)` channel imply the signed AFE gap `O(T)`. -/
theorem afe_signed_integral_gap_bound_of_halfBound_and_partial
    [ZetaMeanSquareHalfBound]
    (hpartial :
      (fun T => (∫ t in (1 : ℝ)..T, partialMsIntegrand t) -
          (1 / 2 : ℝ) * T * Real.log T)
        =O[atTop] (fun T => T)) :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
    =O[atTop] (fun T => T) := by
  exact
    Aristotle.Standalone.HardyAfeSignedGapScaffold.signed_gap_isBigO_of_halfBound_and_partial_asymptotic
      hpartial

/-- Candidate closure route for this deep leaf once a critical-line zeta
mean-square provider is available. -/
theorem afe_signed_integral_gap_bound_of_halfBound
    [ZetaMeanSquareHalfBound] :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
    =O[atTop] (fun T => T) := by
  exact Aristotle.Standalone.HardyAfeSignedGapRootInfra.signed_gap_isBigO_of_halfBound

/-- Candidate closure route with an explicit (non-typeclass) critical-line
zeta mean-square asymptotic theorem. -/
theorem afe_signed_integral_gap_bound_of_explicit_halfBound
    (hhalf :
      (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
        =O[atTop] (fun T => T)) :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
    =O[atTop] (fun T => T) := by
  exact
    Aristotle.Standalone.HardyAfeSignedGapRootInfra.signed_gap_isBigO_of_explicit_halfBound
      hhalf

/-- Candidate closure route from an unconditional zeta-channel `1..T`
main-term theorem. -/
theorem afe_signed_integral_gap_bound_of_zeta_channel_main_term
    (hzeta :
      (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
        =O[atTop] (fun T : ℝ => T)) :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
    =O[atTop] (fun T : ℝ => T) := by
  exact
    Aristotle.Standalone.HardyAfeSignedGapProvider.signed_gap_isBigO_of_zeta_channel_main_term
      hzeta

/-- Candidate closure route from the exact Hardy-Z `Ioc 1 T` main-term
asymptotic statement. -/
theorem afe_signed_integral_gap_bound_of_hardyZ_ioc_main_term
    (hHardy :
      (fun T : ℝ =>
        (∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2) - T * Real.log T)
        =O[atTop] (fun T : ℝ => T)) :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
    =O[atTop] (fun T : ℝ => T) := by
  exact
    Aristotle.Standalone.HardyAfeSignedGapProvider.signed_gap_isBigO_of_hardyZ_ioc_main_term
      hHardy

/-- Candidate closure route from the packaged Hardy mean-square asymptotic
class (`HardyMeanSquareAsymptoticHyp`). -/
theorem afe_signed_integral_gap_bound_of_hardyMeanSquareAsymptoticHyp
    [Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp] :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T : ℝ => T) := by
  exact
    Aristotle.Standalone.HardyAfeSignedGapProvider.signed_gap_isBigO_of_hardyMeanSquareAsymptoticHyp

/-- Candidate closure route from the bundled B1 root payload class. -/
theorem afe_signed_integral_gap_bound_of_rootPayload
    [Aristotle.Standalone.HardyAfeSignedGapRootInfra.HardyAfeSignedGapRootPayload] :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
    =O[atTop] (fun T => T) := by
  exact Aristotle.Standalone.HardyAfeSignedGapRootInfra.signed_gap_isBigO_of_rootPayload

/-- **Delegated B1 deep leaf**: signed AFE gap has `O(T)` integral growth. -/
theorem afe_signed_integral_gap_bound_leaf :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
    =O[atTop] (fun T => T) := by
  sorry

end Aristotle.Standalone.HardyAfeSignedGapDeepLeaf
