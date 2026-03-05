import Littlewood.Aristotle.Standalone.HardyAfeSignedGapRootInfra
import Littlewood.Aristotle.Standalone.HardyAfeZetaChannelFromAsymptotic

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyAfeSignedGapProvider

open Filter Asymptotics MeasureTheory Set
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
open Aristotle.Standalone.HardyAfeSignedGapScaffold
open Aristotle.Standalone.HardyAfeSignedGapRootInfra

/-- Non-circular B1 provider endpoint:
an unconditional `1..T` zeta-channel main-term theorem plus the proved partial
channel asymptotic imply the signed AFE gap bound. -/
theorem signed_gap_isBigO_of_zeta_channel_main_term
    (hzeta :
      (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
        =O[atTop] (fun T : ℝ => T)) :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T : ℝ => T) := by
  exact signed_gap_isBigO_of_main_term_asymptotics
    hzeta
    partial_channel_main_term_isBigO

/-- Forward bridge: signed AFE gap `O(T)` implies the `1..T` zeta-channel
main-term asymptotic. -/
theorem zeta_channel_main_term_isBigO_of_signed_gap
    (hSigned :
      (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
        =O[atTop] (fun T : ℝ => T)) :
    (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T) := by
  exact Aristotle.Standalone.HardyAfeSignedGapRootInfra.zeta_channel_main_term_isBigO_of_signed_gap
    hSigned

/-- Exact fixed-point equivalence for B1: the signed AFE gap bound and the
`1..T` zeta-channel asymptotic are inter-derivable. -/
theorem signed_gap_iff_zeta_channel_main_term :
    ((fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T : ℝ => T)) ↔
    ((fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T)) := by
  constructor
  · intro hSigned
    exact zeta_channel_main_term_isBigO_of_signed_gap hSigned
  · intro hzeta
    exact signed_gap_isBigO_of_zeta_channel_main_term hzeta

/-- Provider endpoint from an explicit critical-line second-moment asymptotic. -/
theorem signed_gap_isBigO_of_explicit_half_asymptotic
    (hhalf :
      (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
        =O[atTop] (fun T : ℝ => T)) :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T : ℝ => T) := by
  exact signed_gap_isBigO_of_explicit_halfBound hhalf

/-- Exact fixed-point equivalence for B1 against the explicit critical-line
second-moment asymptotic. -/
theorem signed_gap_iff_explicit_half_asymptotic :
    ((fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T : ℝ => T)) ↔
    ((fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
      =O[atTop] (fun T : ℝ => T)) := by
  constructor
  · intro hSigned
    exact mean_square_zeta_half_asymp_of_signed_gap hSigned
  · intro hhalf
    exact signed_gap_isBigO_of_explicit_half_asymptotic hhalf

/-- Provider endpoint from `HardyMeanSquareAsymptoticHyp`. -/
theorem signed_gap_isBigO_of_hardyMeanSquareAsymptoticHyp
    [Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp] :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T : ℝ => T) := by
  exact
    Aristotle.Standalone.HardyAfeZetaChannelFromAsymptotic.signed_gap_isBigO_of_hardyMeanSquareAsymptoticHyp

/-- Non-circular provider route from the Hardy-Z `Ioc 1 T` main-term asymptotic
to the signed AFE gap endpoint. This isolates B1 to a single analytic root
statement on `HardyEstimatesPartial.hardyZ`. -/
theorem signed_gap_isBigO_of_hardyZ_ioc_main_term
    (hHardy :
      (fun T : ℝ =>
        (∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2) - T * Real.log T)
        =O[atTop] (fun T : ℝ => T)) :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T : ℝ => T) := by
  exact
    signed_gap_isBigO_of_zeta_channel_main_term
      (Aristotle.Standalone.HardyAfeZetaChannelFromAsymptotic.zeta_channel_main_term_isBigO_of_hardyZ_ioc_main_term
        hHardy)

/-- Class bridge: package an explicit second-moment theorem as the standard
`ZetaMeanSquareHalfBound` instance. -/
def zetaMeanSquareHalfBound_of_explicit
    (hhalf :
      (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
        =O[atTop] (fun T : ℝ => T)) :
    ZetaMeanSquareHalfBound :=
  ⟨hhalf⟩

end Aristotle.Standalone.HardyAfeSignedGapProvider
