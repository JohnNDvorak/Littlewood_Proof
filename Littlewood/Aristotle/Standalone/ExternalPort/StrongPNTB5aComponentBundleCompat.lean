import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteComponentsLane

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteComponentsLane

/-- StrongPNT-shaped component bundle for the legacy `psi` explicit-formula lane.
Field names follow the external theorem stack (`SmoothedChebyshevPull*`, `ZetaBoxEval`)
while matching the exact local payload interfaces. -/
structure StrongPNTB5aComponentBundle : Type where
  perronIntegralRe : ℝ → ℝ → ℝ
  contourRemainderRe : ℝ → ℝ → ℝ
  smoothedChebyshevPull1 :
    ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
        Cₚ * Real.log x
  smoothedChebyshevPull2 :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T
  zetaBoxEval :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |contourRemainderRe x T| ≤
        Cc * (Real.sqrt x * Real.log T / Real.sqrt T)

/-- Build the canonical external B5a component payload from a StrongPNT-shaped bundle. -/
def externalLegacyComponentsPayload_of_strongpnt_bundle
    (hBundle : StrongPNTB5aComponentBundle) :
    Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload.ExternalLegacyLinearLogComponentsPayload :=
  externalLegacyComponentsPayload_of_witness
    hBundle.perronIntegralRe
    hBundle.contourRemainderRe
    hBundle.smoothedChebyshevPull1
    hBundle.smoothedChebyshevPull2
    hBundle.zetaBoxEval

/-- Endpoint: recover the legacy linear-log witness directly from a
StrongPNT-shaped component bundle. -/
theorem legacy_linear_log_bound_of_strongpnt_bundle
    (hBundle : StrongPNTB5aComponentBundle) :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
  exact legacy_linear_log_bound_of_concrete_external_components
    hBundle.perronIntegralRe
    hBundle.contourRemainderRe
    hBundle.smoothedChebyshevPull1
    hBundle.smoothedChebyshevPull2
    hBundle.zetaBoxEval

/-- Endpoint: recover the canonical B5a shifted-remainder bound directly from a
StrongPNT-shaped component bundle. -/
theorem shifted_remainder_bound_of_strongpnt_bundle
    (hBundle : StrongPNTB5aComponentBundle) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_concrete_external_components
    hBundle.perronIntegralRe
    hBundle.contourRemainderRe
    hBundle.smoothedChebyshevPull1
    hBundle.smoothedChebyshevPull2
    hBundle.zetaBoxEval

end Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
