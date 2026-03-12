import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteWitnessLane
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteComponentsLane
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalConcreteExactSeedLane
import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat
import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfRectangleBoundCompat
import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfReciprocalRectangleBoundCompat
import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingPrincipalPartRectangleBoundCompat
import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfLogDerivByZetaBoundCompat
import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingRefactorBundle
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTAnalyticRefactorBundle
import Littlewood.Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourRefactorBundle
import Littlewood.Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourToStrongPNTRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.ExternalRefactorProviderAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTPNT5AndRHPiProviderAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTPNT5RefactorProviderPayload
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiRefactorProviderPayload
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTSplitRefactorProviderAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTZetaRectangleBoundCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLegacyLinearLogWitnessCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLogDerivSeriesCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadConcreteLane
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalRefactorBundle
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalExternalPayloadAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundleFromExternalPayloads
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteWitnessLane
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteComponentsLane
open Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload
open Aristotle.Standalone.ExternalPort.RHPiExternalConcreteExactSeedLane
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfRectangleBoundCompat
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfReciprocalRectangleBoundCompat
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingPrincipalPartRectangleBoundCompat
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfLogDerivByZetaBoundCompat
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingRefactorBundle
open Aristotle.Standalone.ExternalPort.StrongPNTAnalyticRefactorBundle
open Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourRefactorBundle
open Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourToStrongPNTRefactor
open Aristotle.Standalone.ExternalPort.ExternalRefactorProviderAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTPNT5AndRHPiProviderAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTPNT5RefactorProviderPayload
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiRefactorProviderPayload
open Aristotle.Standalone.ExternalPort.StrongPNTSplitRefactorProviderAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTZetaRectangleBoundCompat
open Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
open Aristotle.Standalone.ExternalPort.StrongPNTLegacyLinearLogWitnessCompat
open Aristotle.Standalone.ExternalPort.StrongPNTLogDerivSeriesCompat
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadConcreteLane
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalRefactorBundle
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalExternalPayloadAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundleFromExternalPayloads
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider
open Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open PiLiDirectOscillationBridge

/-- One concrete external legacy witness theorem is enough to recover the
full B5a constructor bundle. -/
theorem b5a_constructor_bundle_of_concrete_external_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      ExplicitFormulaPsiB5aRootPayload := by
  letI : ExternalLegacyLinearLogWitnessPayload :=
    externalLegacyLinearLogWitnessPayload_of_witness hWitness
  refine ⟨inferInstance, ?_⟩
  exact ⟨inferInstance, inferInstance⟩

/-- One concrete external component package is enough to recover the full B5a
constructor bundle. -/
theorem b5a_constructor_bundle_of_concrete_external_components
    (perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ)
    (hPerron :
      ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * Real.log x)
    (hResidue :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
    (hContour :
      ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * Real.log T / Real.sqrt T)) :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      ExplicitFormulaPsiB5aRootPayload := by
  letI : ExternalLegacyLinearLogComponentsPayload :=
    externalLegacyComponentsPayload_of_witness
      perronIntegralRe contourRemainderRe hPerron hResidue hContour
  refine ⟨inferInstance, ?_⟩
  exact ⟨inferInstance, inferInstance⟩

/-- One StrongPNT-shaped component bundle is enough to recover the full B5a
constructor bundle through the external-port component lane. -/
theorem b5a_constructor_bundle_of_strongpnt_component_bundle
    (hBundle : StrongPNTB5aComponentBundle) :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      ExplicitFormulaPsiB5aRootPayload := by
  exact b5a_constructor_bundle_of_concrete_external_components
    hBundle.perronIntegralRe
    hBundle.contourRemainderRe
    hBundle.smoothedChebyshevPull1
    hBundle.smoothedChebyshevPull2
    hBundle.zetaBoxEval

/-- One StrongPNT-shaped legacy linear-log witness bundle is enough to recover
the full B5a constructor bundle through the external witness lane. -/
theorem b5a_constructor_bundle_of_strongpnt_legacy_witness_bundle
    (hBundle : StrongPNTLegacyLinearLogWitnessBundle) :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      ExplicitFormulaPsiB5aRootPayload := by
  letI : ExternalLegacyLinearLogWitnessPayload :=
    externalLegacyLinearLogWitnessPayload_of_strongpnt_bundle hBundle
  refine ⟨inferInstance, ?_⟩
  exact ⟨inferInstance, inferInstance⟩

/-- One global StrongPNT payload class instance is enough to recover the full
B5a constructor bundle. -/
theorem b5a_constructor_bundle_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      ExplicitFormulaPsiB5aRootPayload := by
  refine ⟨inferInstance, ?_⟩
  exact ⟨inferInstance, inferInstance⟩

/-- Refactored `PrimeNumberTheoremAndContour` payload endpoint:
canonical shifted-contours B5a bound from one bundled payload term. -/
theorem shifted_contours_bound_of_refactored_pnt_contour_payload
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourRefactorBundle.shifted_contours_bound_of_refactored_payload
      hPayload

/-- Refactored `PrimeNumberTheoremAndContour` payload endpoint:
recover the full B5a constructor bundle from one bundled payload term. -/
theorem b5a_constructor_bundle_of_refactored_pnt_contour_payload
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload) :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      ExplicitFormulaPsiB5aRootPayload := by
  exact
    Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourRefactorBundle.b5a_constructor_bundle_of_refactored_payload
      hPayload

/-- Refactored `PrimeNumberTheoremAndContour` + refactored RH-`pi` exact-seed
bundle endpoint:
recover canonical B5a and RH-`pi` endpoint obligations directly. -/
theorem b5a_and_rhpi_endpoints_of_refactored_pnt_contour_and_rhpi
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload)
    (hRhPi : RHPiExactSeedRefactorBundle) :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hRhPi.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact
    Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourToStrongPNTRefactor.b5a_and_rhpi_endpoints_of_refactored_pnt_contour_and_rhpi
      hPayload hRhPi

/-- Refactored `PrimeNumberTheoremAndContour` + refactored RH-`pi` exact-seed
bundle endpoint:
recover all constructor roots needed by the active B5a/B7 closure files. -/
theorem root_constructor_bundle_of_refactored_pnt_contour_and_rhpi
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload)
    (hRhPi : RHPiExactSeedRefactorBundle) :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact
    Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourToStrongPNTRefactor.root_constructor_bundle_of_refactored_pnt_contour_and_rhpi
      hPayload hRhPi

/-- Consolidated refactor-provider class endpoint:
recover all constructor roots needed by the active B5a/B7 closure files. -/
theorem root_constructor_bundle_of_refactored_provider_payload_class
    [RefactoredPNTContourAndRHPiProviderPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact
    Aristotle.Standalone.ExternalPort.ExternalRefactorProviderAutoInstances.root_constructor_bundle_of_refactored_provider_payload

/-- Consolidated refactor-provider class endpoint:
recover canonical B5a and RH-`pi` endpoint obligations. -/
theorem b5a_and_rhpi_endpoints_of_refactored_provider_payload_class
    [RefactoredPNTContourAndRHPiProviderPayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    Aristotle.Standalone.ExternalPort.ExternalRefactorProviderAutoInstances.b5a_and_rhpi_endpoints_of_refactored_provider_payload

/-- Consolidated `PNT5`+RH-`pi` refactor-provider class endpoint:
recover all constructor roots needed by the active B5a/B7 closure files. -/
theorem root_constructor_bundle_of_pnt5_and_rhpi_provider_payload_class
    [PNT5AndRHPiRefactorProviderPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTPNT5AndRHPiProviderAutoInstances.root_constructor_bundle_of_pnt5_and_rhpi_provider_payload

/-- Consolidated `PNT5`+RH-`pi` refactor-provider class endpoint:
recover canonical B5a and RH-`pi` endpoint obligations. -/
theorem b5a_and_rhpi_endpoints_of_pnt5_and_rhpi_provider_payload_class
    [PNT5AndRHPiRefactorProviderPayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTPNT5AndRHPiProviderAutoInstances.b5a_and_rhpi_endpoints_of_pnt5_and_rhpi_provider_payload

/-- Split B5a-only refactored provider class endpoint:
recover the full B5a constructor bundle from one refactored `PNT5_Strong`
bundle provider class instance. -/
theorem b5a_constructor_bundle_of_pnt5_refactor_provider_payload_class
    [PNT5StrongRefactorProviderPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      ExplicitFormulaPsiB5aRootPayload := by
  exact b5a_constructor_bundle_of_pnt5_refactor_provider_payload

/-- Split RH-`pi`-only refactored provider class endpoint:
recover the bundled RH-`pi` exact-seed root payload class from one refactored
exact-seed provider class instance. -/
theorem rhpi_rootPayload_of_refactor_provider_payload_class
    [RHPiExactSeedRefactorProviderPayload] :
    RHPiUnconditionalExactSeedRootPayload := by
  exact rhpi_rootPayload_of_refactor_provider_payload

/-- Split RH-`pi`-only refactored provider class endpoint:
recover all three RH-`pi` exact-seed obligations from one refactored exact-seed
provider class instance. -/
theorem rhpi_exactSeedTriple_of_refactor_provider_payload_class
    [RHPiExactSeedRefactorProviderPayload] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact rhpi_exactSeedTriple_of_refactor_provider_payload

/-- Split refactored provider class endpoint:
recover all constructor roots needed by the active B5a/B7 closure files. -/
theorem root_constructor_bundle_of_split_refactor_provider_payload_class
    [PNT5StrongRefactorProviderPayload]
    [RHPiExactSeedRefactorProviderPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact root_constructor_bundle_of_split_refactor_provider_payload

/-- Split refactored provider class endpoint:
recover canonical B5a and RH-`pi` endpoint obligations. -/
theorem b5a_and_rhpi_endpoints_of_split_refactor_provider_payload_class
    [PNT5StrongRefactorProviderPayload]
    [RHPiExactSeedRefactorProviderPayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact b5a_and_rhpi_endpoints_of_split_refactor_provider_payload

/-- One bundled concrete RH-pi witness term is enough to recover the bundled
root payload class required by unconditional endpoint closures. -/
theorem rhpi_rootPayload_of_concrete_external_triple
    (hTriple : ConcreteExactSeedTriple) :
    RHPiUnconditionalExactSeedRootPayload := by
  letI : ExternalExactSeedPayload := externalExactSeedPayload_of_triple hTriple
  infer_instance

/-- One bundled concrete RH-pi witness term is enough to recover all three
exact-seed endpoint payload obligations. -/
theorem rhpi_exactSeedTriple_of_concrete_external_triple
    (hTriple : ConcreteExactSeedTriple) :
    TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hTriple.truncated
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact exactSeedTriple_of_concrete_external_triple hTriple

/-- One StrongPNT-shaped bundled RH-pi exact-seed payload is enough to recover
the bundled root payload class required by unconditional endpoint closures. -/
theorem rhpi_rootPayload_of_strongpnt_exactSeed_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    RHPiUnconditionalExactSeedRootPayload := by
  exact rhpi_rootPayload_of_strongpnt_bundle hBundle

/-- One StrongPNT-shaped bundled RH-pi exact-seed payload is enough to recover
all three exact-seed endpoint obligations. -/
theorem rhpi_exactSeedTriple_of_strongpnt_exactSeed_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact rhpi_exactSeedTriple_of_strongpnt_bundle hBundle

/-- One refactored RH-pi exact-seed bundle is enough to recover all three
exact-seed endpoint obligations. -/
theorem rhpi_exactSeedTriple_of_refactored_rhpi_bundle
    (hBundle : RHPiExactSeedRefactorBundle) :
    TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact exactSeedTriple_of_refactored_bundle hBundle

/-- One global StrongPNT payload class instance is enough to recover all three
RH-pi exact-seed endpoint obligations. -/
theorem rhpi_exactSeedTriple_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact exactSeedUnconditionalTriple_of_strongpnt_global_payload

/-- One concrete external B5a linear-log witness together with one concrete
RH-pi exact-seed witness triple is enough to recover both constructor bundles:
B5a global constructors and all three RH-pi exact-seed endpoints. -/
theorem b5a_and_rhpi_constructor_bundle_of_concrete_global_witnesses
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x))
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    (∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      ExplicitFormulaPsiB5aRootPayload) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  letI : StrongPNTGlobalPayload :=
    strongpnt_global_payload_of_witnesses hWitness hTruncated hTarget hAntiTarget
  refine ⟨b5a_constructor_bundle_of_strongpnt_global_payload, ?_⟩
  exact
    ⟨truncatedExplicitFormulaPi_of_strongpnt_global_payload,
      targetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload,
      antiTargetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload⟩

/-- One StrongPNT-style B5a component bundle together with one StrongPNT-style
RH-pi exact-seed bundle is enough to recover both constructor bundles. -/
theorem b5a_and_rhpi_constructor_bundle_of_strongpnt_bundles
    (hB5a : StrongPNTB5aComponentBundle)
    (hRhPi : StrongPNTRHPiExactSeedBundle) :
    (∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      ExplicitFormulaPsiB5aRootPayload) ∧
      TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hRhPi.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  letI : StrongPNTGlobalPayload := strongpnt_global_payload_of_bundles hB5a hRhPi
  refine ⟨b5a_constructor_bundle_of_strongpnt_global_payload, ?_⟩
  refine ⟨truncatedExplicitFormulaPi_of_strongpnt_global_payload, ?_⟩
  letI : TruncatedExplicitFormulaPiHyp := hRhPi.truncatedPiFormula
  exact
    ⟨targetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload,
      antiTargetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload⟩

/-- One bundled refactored global StrongPNT payload is enough to recover all
three constructor roots needed by the active B5a and RH-pi closure files. -/
theorem root_constructor_bundle_of_refactored_global_bundle_payload
    (hBundle : StrongPNTGlobalRefactorPayload) :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTGlobalRefactorBundle.root_constructor_bundle_of_refactored_global_bundle
      hBundle

/-- One bundled refactored global StrongPNT payload is enough to recover the
canonical B5a shifted bound and RH-pi exact-seed endpoint obligations. -/
theorem b5a_and_rhpi_endpoints_of_refactored_global_bundle_payload
    (hBundle : StrongPNTGlobalRefactorPayload) :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hBundle.rhpi.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTGlobalRefactorBundle.b5a_and_rhpi_endpoints_of_refactored_global_bundle
      hBundle

/-- One global StrongPNT payload class instance is enough to recover all three
constructor roots needed by the active B5a and RH-pi closure files. -/
theorem root_constructor_bundle_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  refine ⟨explicitFormulaPsiHyp_of_strongpnt_global_payload, ?_⟩
  exact
    ⟨explicitFormulaPsiGeneralHyp_of_strongpnt_global_payload,
      rhpi_rootPayload_of_strongpnt_global_payload⟩

/-- A fused pair of external payload lanes (B5a components + RH-pi exact-seed)
is enough to recover all three constructor roots needed by the active B5a and
RH-pi closure files. -/
theorem root_constructor_bundle_of_external_payload_lanes
    [ExternalLegacyLinearLogComponentsPayload]
    [ExternalExactSeedPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTGlobalExternalPayloadAutoInstances.root_constructor_bundle_of_external_payload_lanes

/-- Same fused external payload lanes recover all three constructor roots through
the bundled StrongPNT global payload route. -/
theorem root_constructor_bundle_of_external_payload_lanes_via_bundle
    [ExternalLegacyLinearLogComponentsPayload]
    [ExternalExactSeedPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundleFromExternalPayloads.root_constructor_bundle_of_external_payload_lanes_via_bundle

/-- One consolidated concrete B5a provider payload and one consolidated concrete
RH-`pi` exact-seed provider payload are enough to recover all constructor roots
needed by the active B5a/B7 closure files. -/
theorem root_constructor_bundle_of_concrete_provider_payloads
    [B5aConcreteProviderPayload]
    [RHPiConcreteProviderPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  rcases b5a_constructor_bundle_of_concrete_provider with ⟨hPsi, hGeneral, _hB5aRoot⟩
  refine ⟨hPsi, ?_⟩
  exact ⟨hGeneral, rhpi_rootPayload_of_concrete_provider⟩

/-- One concrete global witness payload class instance is enough to recover all
three constructor roots needed by the active B5a and RH-pi closure files. -/
theorem root_constructor_bundle_of_concrete_global_witness_payload
    [StrongPNTConcreteGlobalWitnessPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact root_constructor_bundle_of_strongpnt_global_payload

/-- One bundled StrongPNT payload class instance is enough to recover all three
constructor roots needed by the active B5a and RH-pi closure files. -/
  theorem root_constructor_bundle_of_concrete_global_bundle_payload
    [StrongPNTConcreteGlobalBundlePayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances.root_constructor_bundle_of_concrete_global_bundle_payload

/-- One-shot constructor endpoint bundle from concrete StrongPNT-style B5a and
RH-pi bundle terms. -/
  theorem b5a_and_rhpi_endpoints_of_strongpnt_bundles
    (hB5a : StrongPNTB5aComponentBundle)
    (hRhPi : StrongPNTRHPiExactSeedBundle) :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hRhPi.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances.b5a_and_rhpi_endpoints_of_strongpnt_bundles hB5a hRhPi

/-- One concrete global StrongPNT witness payload class instance is enough to
recover all three constructor roots through the consolidated concrete-provider
lane. -/
theorem root_constructor_bundle_of_strongpnt_concrete_witness_payload
    [StrongPNTConcreteGlobalWitnessPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances.root_constructor_bundle_of_strongpnt_concrete_witness_payload

/-- One concrete global StrongPNT witness payload class instance is enough to
recover canonical B5a+RH-`pi` endpoint obligations through the consolidated
concrete-provider lane. -/
theorem b5a_and_rhpi_endpoints_of_strongpnt_concrete_witness_payload
    [StrongPNTConcreteGlobalWitnessPayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances.b5a_and_rhpi_endpoints_of_strongpnt_concrete_witness_payload

/-- Rectangle-ready endpoint for strongpnt-style contour integration:
uniform bounds for `ζ` and `1/ζ` on any closed rectangle inside `Re(s) > 1`. -/
theorem zeta_and_inv_bounds_on_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    (∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖riemannZeta s‖ ≤ B) ∧
      (∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖(riemannZeta s)⁻¹‖ ≤ B) := by
  refine ⟨?_, ?_⟩
  · exact exists_norm_riemannZeta_bound_on_rectangle_of_re_gt_one hRect
  · exact exists_norm_inv_riemannZeta_bound_on_rectangle_of_re_gt_one hRect

/-- Pole-cancelled zeta lane readiness endpoint:
continuity of `-ζ₁'/ζ₁` on `{z | z = 1 ∨ ζ z ≠ 0}`. -/
theorem zrf_neg_logDeriv_continuous_on_one_or_zeta_nonzero :
    ContinuousOn
      (fun z =>
        -deriv Aristotle.ZetaPoleCancellation.zrf z /
          Aristotle.ZetaPoleCancellation.zrf z)
      {z : ℂ | z = 1 ∨ riemannZeta z ≠ 0} := by
  simpa using continuousOn_neg_logDeriv_zrf_port

/-- Rectangle-bound readiness endpoint for `-ζ₁'/ζ₁` on `Re(s) > 1`. -/
theorem zrf_neg_logDeriv_bound_on_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖-deriv Aristotle.ZetaPoleCancellation.zrf s /
        Aristotle.ZetaPoleCancellation.zrf s‖ ≤ B := by
  exact exists_norm_neg_logDeriv_zrf_bound_on_rectangle_of_re_gt_one hRect

/-- Rectangle-bound readiness endpoint for both reciprocal and logarithmic
derivative of the pole-cancelled zeta function on `Re(s) > 1`. -/
theorem zrf_inv_and_neg_logDeriv_bounds_on_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    (∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖(Aristotle.ZetaPoleCancellation.zrf s)⁻¹‖ ≤ B) ∧
    (∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖-deriv Aristotle.ZetaPoleCancellation.zrf s /
        Aristotle.ZetaPoleCancellation.zrf s‖ ≤ B) := by
  refine ⟨?_, ?_⟩
  · exact exists_norm_inv_zrf_bound_on_rectangle_of_re_gt_one hRect
  · exact exists_norm_neg_logDeriv_zrf_bound_on_rectangle_of_re_gt_one hRect

/-- Decomposition-style readiness endpoint for `-ζ₁'/ζ₁`:
derive the rectangle bound from the `-ζ'/ζ` and `1/(s-1)` components. -/
theorem zrf_neg_logDeriv_bound_via_zeta_and_principal_part_on_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖-deriv Aristotle.ZetaPoleCancellation.zrf s /
        Aristotle.ZetaPoleCancellation.zrf s‖ ≤ B := by
  exact exists_norm_neg_logDeriv_zrf_bound_via_zeta_on_rectangle_of_re_gt_one hRect

/-- Refactored nonvanishing payload endpoint:
`1/ζ₁` and `-ζ₁'/ζ₁` rectangle bounds from one bundled external payload term. -/
theorem zrf_inv_and_neg_logDeriv_bounds_on_rectangle_of_re_gt_one_of_refactored_payload
    (hPayload : NonvanishingRectangleRefactorPayload)
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    (∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖(Aristotle.ZetaPoleCancellation.zrf s)⁻¹‖ ≤ B) ∧
    (∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖-deriv Aristotle.ZetaPoleCancellation.zrf s /
        Aristotle.ZetaPoleCancellation.zrf s‖ ≤ B) := by
  exact
    Aristotle.Standalone.ExternalPort.DirichletNonvanishingRefactorBundle.zrf_inv_and_neg_logDeriv_bounds_on_rectangle_of_re_gt_one_of_refactored_payload
      hPayload hRect

/-- Refactored nonvanishing payload endpoint:
decomposition-style rectangle bound for `-ζ₁'/ζ₁`. -/
theorem zrf_neg_logDeriv_bound_via_zeta_on_rectangle_of_re_gt_one_of_refactored_payload
    (hPayload : NonvanishingRectangleRefactorPayload)
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖-deriv Aristotle.ZetaPoleCancellation.zrf s /
        Aristotle.ZetaPoleCancellation.zrf s‖ ≤ B := by
  exact
    Aristotle.Standalone.ExternalPort.DirichletNonvanishingRefactorBundle.zrf_neg_logDeriv_bound_via_zeta_on_rectangle_of_re_gt_one_of_refactored_payload
      hPayload hRect

/-- Refactored StrongPNT analytic payload endpoint:
rectangle bounds for `ζ` and `1/ζ` from one bundled analytic payload term. -/
theorem zeta_and_inv_bounds_on_rectangle_of_re_gt_one_of_refactored_analytic_payload
    (hPayload : StrongPNTAnalyticRefactorPayload)
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    (∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖riemannZeta s‖ ≤ B) ∧
      (∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖(riemannZeta s)⁻¹‖ ≤ B) := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTAnalyticRefactorBundle.zeta_and_inv_bounds_on_rectangle_of_re_gt_one_of_refactored_payload
      hPayload hRect

/-- Refactored StrongPNT analytic payload endpoint:
real-part Dirichlet-series line identity for `-ζ'/ζ`. -/
theorem neg_logDeriv_riemannZeta_re_series_on_line_of_refactored_analytic_payload
    (hPayload : StrongPNTAnalyticRefactorPayload)
    {σ t : ℝ}
    (hσ : 1 < σ) :
    (-deriv riemannZeta (σ + t * Complex.I) /
        riemannZeta (σ + t * Complex.I)).re =
      ∑' n : ℕ,
        (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (σ + t * Complex.I) n).re := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTAnalyticRefactorBundle.neg_logDeriv_riemannZeta_re_series_on_line_of_refactored_payload
      hPayload hσ

/-- Refactored StrongPNT analytic payload endpoint:
`ζ'/ζ` tends to cobounded near a nontrivial zero. -/
theorem zeta_logDeriv_tendsto_cobounded_of_refactored_analytic_payload
    (hPayload : StrongPNTAnalyticRefactorPayload)
    (ρ₀ : ℂ) (hne : ρ₀ ≠ 1) (hz : riemannZeta ρ₀ = 0) :
    Filter.Tendsto (fun s => deriv riemannZeta s / riemannZeta s)
      (nhdsWithin ρ₀ (({ρ₀} : Set ℂ)ᶜ))
      (Bornology.cobounded ℂ) := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTAnalyticRefactorBundle.zeta_logDeriv_tendsto_cobounded_of_refactored_payload
      hPayload ρ₀ hne hz

/-- StrongPNT-style line endpoint: real-part series identity for `-ζ'/ζ` on
`s = σ + it` with `σ > 1`. -/
theorem neg_logDeriv_riemannZeta_re_series_on_line
    {σ t : ℝ}
    (hσ : 1 < σ) :
    (-deriv riemannZeta (σ + t * Complex.I) /
        riemannZeta (σ + t * Complex.I)).re =
      ∑' n : ℕ,
        (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (σ + t * Complex.I) n).re := by
  exact neg_logDeriv_riemannZeta_re_eq_tsum_re_on_line hσ

end Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness
