import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLegacyLinearLogWitnessCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
open Aristotle.Standalone.ExternalPort.StrongPNTLegacyLinearLogWitnessCompat

/-- Lean-4.27 refactor surface for the core `StrongPNT/PNT5_Strong` contour
theorem family used by the B5a lane.

The field names intentionally mirror the external theorem names so downstream
adapters can target a stable, external-style API without importing the original
toolchain-incompatible package. -/
structure PNT5StrongRefactorBundle : Type where
  perronIntegralRe : ℝ → ℝ → ℝ
  contourRemainderRe : ℝ → ℝ → ℝ
  SmoothedChebyshevPull1 :
    ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
        Cₚ * Real.log x
  SmoothedChebyshevPull2 :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T
  ZetaBoxEval :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |contourRemainderRe x T| ≤
        Cc * (Real.sqrt x * Real.log T / Real.sqrt T)
  SmoothedChebyshevClose :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)

/-- Convert a refactored `PNT5_Strong` bundle into the canonical StrongPNT B5a
component bundle. -/
def toComponentBundle
    (hBundle : PNT5StrongRefactorBundle) :
    StrongPNTB5aComponentBundle where
  perronIntegralRe := hBundle.perronIntegralRe
  contourRemainderRe := hBundle.contourRemainderRe
  smoothedChebyshevPull1 := hBundle.SmoothedChebyshevPull1
  smoothedChebyshevPull2 := hBundle.SmoothedChebyshevPull2
  zetaBoxEval := hBundle.ZetaBoxEval

/-- Convert a refactored `PNT5_Strong` bundle into the StrongPNT legacy
linear-log witness bundle. -/
def toLegacyWitnessBundle
    (hBundle : PNT5StrongRefactorBundle) :
    StrongPNTLegacyLinearLogWitnessBundle where
  explicitFormulaPsiLinearLog := hBundle.SmoothedChebyshevClose

/-- Canonical legacy witness endpoint exposed on the refactored PNT5 bundle. -/
theorem legacy_linear_log_bound_of_refactored_pnt5
    (hBundle : PNT5StrongRefactorBundle) :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) :=
  hBundle.SmoothedChebyshevClose

/-- Canonical shifted-remainder endpoint exposed on the refactored PNT5
bundle. -/
theorem shifted_remainder_bound_of_refactored_pnt5
    (hBundle : PNT5StrongRefactorBundle) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_strongpnt_bundle (toComponentBundle hBundle)

/-- Constructor endpoint: recover the legacy explicit-formula class from the
refactored PNT5 bundle. -/
def explicitFormulaPsiHyp_of_refactored_pnt5
    (hBundle : PNT5StrongRefactorBundle) :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp := by
  exact explicitFormulaPsiHyp_of_strongpnt_bundle (toLegacyWitnessBundle hBundle)

/-- Constructor endpoint: recover the B5a root payload class from the refactored
PNT5 bundle. -/
theorem b5a_rootPayload_of_refactored_pnt5
    (hBundle : PNT5StrongRefactorBundle) :
    ExplicitFormulaPsiB5aRootPayload := by
  exact b5a_rootPayload_of_strongpnt_legacy_witness_bundle
    (toLegacyWitnessBundle hBundle)

end Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
