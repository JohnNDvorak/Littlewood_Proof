/- 
Delegated deep leaf for B5a (shifted remainder bound).

This file carries the analytic Perron/residue/contour payload:
`|shiftedRemainderRe x T| ≤ C₂ * (sqrt/log + log^2)` uniformly for `x,T ≥ 2`.

The main-chain atomic theorem in `ExplicitFormulaPsiB5aShiftedBoundAtomic.lean`
is now a sorry-free wrapper that references this leaf theorem.

SORRY COUNT: 1 (explicit B5a analytic frontier)
-/

import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteWitnessLane
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteComponentsLane
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLegacyLinearLogWitnessCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf

open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteWitnessLane
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteComponentsLane
open Aristotle.Standalone.ExternalPort.StrongPNTLegacyLinearLogWitnessCompat
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors
open Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider

/-- **Delegated B5a deep leaf**: truncated explicit-formula shifted remainder
bound with variable truncation height `T`.

## Proof strategy (3 independent sub-goals)

Use `shifted_remainder_bound_candidate_of_concrete_external_components` with:

1. **Perron truncation** (Davenport 17.1): Define `perronIntegralRe x T` as the
   real part of `(1/2πi) ∫_{c-iT}^{c+iT} (-ζ'/ζ)(s) x^s/s ds` and show
   `|ψ(x) - perronIntegralRe x T| ≤ Cₚ · (log x)²`.

2. **Residue identity** (Cauchy): After shifting the contour from `Re s = c > 1`
   to `Re s = 1/2`, residues at `s = 1` and `s = ρ` give
   `perronIntegralRe x T = x − Σ Re(x^ρ/ρ) + contourRemainderRe x T`.

3. **Contour shift bound** (Davenport 17.2): The half-line integral satisfies
   `|contourRemainderRe x T| ≤ Cc · √x · (log T)² / √T`.

## Alternative routes (all proved)

- `shifted_remainder_bound_candidate_of_general_hyp` — from ExplicitFormulaPsiGeneralHyp
- `shifted_remainder_bound_candidate_of_legacy_explicit_formula` — from legacy class
- `shifted_remainder_bound_candidate_of_concrete_external_witness` — from weaker linear-log bound
- `shifted_remainder_bound_candidate_of_rootPayload` — from B5a root payload class
-/
theorem shifted_remainder_bound_leaf :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  -- The conditional Perron provider currently requires
  -- `ShiftedRemainderSegmentBoundLargeTHyp`; keep this as the explicit B5a
  -- analytic frontier instead of hiding that dependency behind a failed
  -- cross-module reference.
  sorry

/-- Candidate closure route for this deep leaf from the standalone
general truncated explicit-formula class. -/
theorem shifted_remainder_bound_candidate_of_general_hyp
    [ExplicitFormulaPsiGeneralHyp] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra.shifted_remainder_bound_of_general_hyp

/-- Candidate closure route from the legacy Dirichlet-phase explicit-formula
class used elsewhere in the project. -/
theorem shifted_remainder_bound_candidate_of_legacy_explicit_formula
    [Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra.shifted_remainder_bound_of_legacy_explicit_formula

/-- Candidate closure route from an explicit (non-typeclass) general truncated
explicit-formula theorem. -/
theorem shifted_remainder_bound_candidate_of_general_formula
    (hGeneral :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra.shifted_remainder_bound_of_general_formula
      hGeneral

/-- Candidate closure route from the bundled B5a root payload class. -/
theorem shifted_remainder_bound_candidate_of_rootPayload
    [Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra.ExplicitFormulaPsiB5aRootPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra.shifted_remainder_bound_of_rootPayload

/-- Candidate closure route from any external witness payload instance through
auto-wired B5a constructor classes. -/
theorem shifted_remainder_bound_candidate_of_external_witness_payload
    [Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload.ExternalLegacyLinearLogWitnessPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_external_witness_auto

/-- Candidate closure route from any external legacy-component payload instance
through auto-wired B5a constructor classes. -/
theorem shifted_remainder_bound_candidate_of_external_legacy_components_payload
    [Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload.ExternalLegacyLinearLogComponentsPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_external_legacy_components_auto

/-- Candidate closure route from any external shifted-component payload instance
through auto-wired B5a constructor classes. -/
theorem shifted_remainder_bound_candidate_of_external_shifted_components_payload
    [Aristotle.Standalone.ExternalPort.B5aExternalShiftedComponentsPayload.ExternalShiftedBoundComponentsPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_external_shifted_components_auto

/-- Candidate closure route from one concrete external legacy linear-log witness
theorem term (external-port integration lane). -/
theorem shifted_remainder_bound_candidate_of_concrete_external_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_concrete_external_witness hWitness

/-- Candidate closure route from one StrongPNT-style legacy linear-log witness
bundle (external-port integration lane). -/
theorem shifted_remainder_bound_candidate_of_strongpnt_legacy_witness_bundle
    (hBundle : StrongPNTLegacyLinearLogWitnessBundle) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_strongpnt_legacy_witness_bundle hBundle

/-- Candidate closure route from one global StrongPNT payload instance carrying
the legacy linear-log witness. -/
theorem shifted_remainder_bound_candidate_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_strongpnt_global_payload

/-- Candidate closure route from one concrete global StrongPNT witness payload
class instance through the consolidated concrete-provider lane. -/
theorem shifted_remainder_bound_candidate_of_strongpnt_concrete_witness_payload
    [StrongPNTConcreteGlobalWitnessPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances.b5a_and_rhpi_endpoints_of_strongpnt_concrete_witness_payload.1

/-- Candidate closure route from one concrete external component package
(Perron + residue identity + contour bound). -/
theorem shifted_remainder_bound_candidate_of_concrete_external_components
    (perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ)
    (hPerron :
      ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * Real.log x)
    (hResidue :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T =
          x - Aristotle.Standalone.ExplicitFormulaPsiSkeleton.zeroSumRe x T +
            contourRemainderRe x T)
    (hContour :
      ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * Real.log T / Real.sqrt T)) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    shifted_remainder_bound_of_concrete_external_components
      perronIntegralRe contourRemainderRe hPerron hResidue hContour

/-- Candidate closure route from the consolidated concrete B5a provider payload
class. -/
theorem shifted_remainder_bound_candidate_of_concrete_provider
    [B5aConcreteProviderPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider.shifted_remainder_bound_of_concrete_provider

end Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf
