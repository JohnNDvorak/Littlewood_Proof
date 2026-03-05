import Littlewood.Aristotle.Standalone.HardyAfeSignedGapProvider
import Littlewood.Aristotle.Standalone.HardyAfeZetaChannelFromAsymptotic

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyAfeHardyZIocMainTermRoot

open Filter Asymptotics MeasureTheory Set
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
open Aristotle.Standalone.HardyAfeZetaChannelFromAsymptotic
open Aristotle.Standalone.HardyAfeSignedGapProvider

/-- Canonical B1 root statement for the signed AFE mean-square gap channel. -/
abbrev SignedGapRootStatement : Prop :=
  (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
    =O[atTop] (fun T : ℝ => T)

/-- Canonical B1 root statement for the zeta `1..T` mean-square main term. -/
abbrev ZetaChannelRootStatement : Prop :=
  (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
    =O[atTop] (fun T : ℝ => T)

/-- Canonical B1 root statement in exact Hardy-Z `Ioc 1 T` form. -/
abbrev HardyZIocRootStatement : Prop :=
  (fun T : ℝ =>
    (∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2) - T * Real.log T)
    =O[atTop] (fun T : ℝ => T)

/-- Lift a zeta-channel root theorem into the exact Hardy-Z `Ioc 1 T` form. -/
theorem hardyZ_ioc_main_term_of_zeta_channel_root
    (hzeta : ZetaChannelRootStatement) :
    HardyZIocRootStatement := by
  exact hardyZ_ioc_main_term_isBigO_of_zeta_channel_main_term hzeta

/-- Lift a signed-gap root theorem into the exact Hardy-Z `Ioc 1 T` form. -/
theorem hardyZ_ioc_main_term_of_signed_gap_root
    (hSigned : SignedGapRootStatement) :
    HardyZIocRootStatement := by
  exact
    hardyZ_ioc_main_term_of_zeta_channel_root
      (zeta_channel_main_term_isBigO_of_signed_gap hSigned)

/-- Project the exact Hardy-Z `Ioc 1 T` root theorem back to the signed-gap root theorem. -/
theorem signed_gap_root_of_hardyZ_ioc_main_term
    (hHardy : HardyZIocRootStatement) :
    SignedGapRootStatement := by
  exact signed_gap_isBigO_of_hardyZ_ioc_main_term hHardy

/-- Exact root-level equivalence between signed-gap and Hardy-Z `Ioc 1 T` forms. -/
theorem signed_gap_root_iff_hardyZ_ioc_root :
    SignedGapRootStatement ↔ HardyZIocRootStatement := by
  constructor
  · intro hSigned
    exact hardyZ_ioc_main_term_of_signed_gap_root hSigned
  · intro hHardy
    exact signed_gap_root_of_hardyZ_ioc_main_term hHardy

/-- Exact root-level equivalence between zeta-channel and Hardy-Z `Ioc 1 T` forms. -/
theorem zeta_channel_root_iff_hardyZ_ioc_root :
    ZetaChannelRootStatement ↔ HardyZIocRootStatement := by
  exact zeta_channel_main_term_iff_hardyZ_ioc_main_term

end Aristotle.Standalone.HardyAfeHardyZIocMainTermRoot
