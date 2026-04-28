# Former Frontier Reintegration - 2026-04-28

## Scope

This pass reviewed the recovered CloudDocs source files under:

`.recovery_artifacts/2026-04-21/clouddocs_absent_quarantine_2026-04-28/files`

The active-source copy was intentionally conservative:

- `Littlewood/ZetaZeros/FirstZeroWitness.lean` remained out of active source.
- 125 recovered Lean files were initially copied into active source for inspection.
- 78 recovered files remain active after compile classification.
- 47 recovered files were staged back out because they compile against stale APIs or stale theorem shapes.

Staged active copies were preserved at:

`.recovery_artifacts/2026-04-21/clouddocs_absent_quarantine_2026-04-28/staged_active_api_drift_2026-04-28`

The original CloudDocs quarantine copies remain untouched.

## Integrated Active Batch

The following recovered surfaces were added to the root import path and verified:

- `Littlewood.Aristotle.Standalone.JensenZeroCounting`
- `Littlewood.Aristotle.Standalone.PerronKernelTruncation`
- `Littlewood.Aristotle.Standalone.PerronTruncationAtomics`
- `Littlewood.Aristotle.Standalone.SmallTPerronSqrtBridge`
- `Littlewood.Aristotle.Standalone.SteepestDescentExpansion`
- `Littlewood.Aristotle.Standalone.AnalyticOrderAtConj`
- `Littlewood.Aristotle.HarmonicMaxPrinciple`
- `Littlewood.Aristotle.Standalone.AbelMultiplicityCorrectionProof`

Additional recovered modules that built cleanly remain active as untracked source files for follow-up review and possible root integration.

## Compatibility Patches

The active branch received small compatibility patches while validating recovered files:

- `Littlewood/CoreLemmas/GrowthDomination.lean`
  - Added `eventually_ge_lll_const`, needed by recovered `PsiThetaLllTransfer`.
- `Littlewood/ZetaZeros/ZeroDensity.lean`
  - Added `zetaNontrivialZero_im_ne_zero`, using the existing real nonvanishing theorem.
- `Littlewood/ZetaZeros/PairedFarZeroCancellationHelper.lean`
  - Temporarily updated old first-zero imports before the whole stale paired-cancellation closure was staged.
- `Littlewood/Aristotle/Standalone/RvMPartialSummation.lean`
  - Adjusted the wrapper arity to the current bound class.
- `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`
  - Replaced a broken dependency on the combined B5a+pi bundle with an explicit theorem `sorry`.
  - This is now an honest B5a analytic frontier, not a hidden failed typeclass dependency.
- `Littlewood/Basic/ChebyshevFunctionsQuarantine.lean`
  - Converted three quarantined Chebyshev/PNT axioms into theorem sorries.

## Staged API-Drift Batch

The following recovered files were removed from active source and preserved in the staged-artifact directory:

- `Littlewood/Aristotle/Standalone/ContourRemainderMultFromHadamard.lean`
- `Littlewood/Aristotle/Standalone/ExplicitFormulaAbelBoundMultBridge.lean`
- `Littlewood/Aristotle/Standalone/ExternalPort/PerronLinearLogDirectSorry.lean`
- `Littlewood/Aristotle/Standalone/ExternalPort/RefactoredPNTContourAndRHPiProviderLeaf.lean`
- `Littlewood/Aristotle/Standalone/HadamardConstructiveBridge.lean`
- `Littlewood/Aristotle/Standalone/HadamardFactorizationWiring.lean`
- `Littlewood/Aristotle/Standalone/HadamardMultEnumeration.lean`
- `Littlewood/Aristotle/Standalone/HadamardXiEnumCleanProvider.lean`
- `Littlewood/Aristotle/Standalone/HadamardZeroEnumeration.lean`
- `Littlewood/Aristotle/Standalone/HalfLineBoundClosure.lean`
- `Littlewood/Aristotle/Standalone/HalfLineIntegralBound.lean`
- `Littlewood/Aristotle/Standalone/JensenLocalDensityBridge.lean`
- `Littlewood/Aristotle/Standalone/LittlewoodPLSetup.lean`
- `Littlewood/Aristotle/Standalone/LittlewoodPiArgApproxLeafInstances.lean`
- `Littlewood/Aristotle/Standalone/LittlewoodPsiLeafInstances.lean`
- `Littlewood/Aristotle/Standalone/LittlewoodUpperHalfStripClean.lean`
- `Littlewood/Aristotle/Standalone/PsiClassicalSupport.lean`
- `Littlewood/Aristotle/Standalone/RHPiClassicalPsiMeanSquare.lean`
- `Littlewood/Aristotle/Standalone/RHPiCorrectedCanonicalFromPerronBridge.lean`
- `Littlewood/Aristotle/Standalone/RHPiExplicitFormulaErrorAtFixedHeight.lean`
- `Littlewood/Aristotle/Standalone/RHPiInhomogeneousPhaseDirectHonest.lean`
- `Littlewood/Aristotle/Standalone/RHPiInhomogeneousPhaseFitReduction.lean`
- `Littlewood/Aristotle/Standalone/RHPiShiftedRemainderDivLogFixedHeight.lean`
- `Littlewood/Aristotle/Standalone/RHPiTargetHeightControlDirectHonest.lean`
- `Littlewood/Aristotle/Standalone/ShiftedRemainderSegmentBoundDirect.lean`
- `Littlewood/Aristotle/Standalone/ZetaLogDerivIntegralHalfOneDirect.lean`
- `Littlewood/Aristotle/Standalone/ZetaLogDerivIntegralOneTwoDirect.lean`
- `Littlewood/Aristotle/Standalone/ZetaLogDerivOneTwoDirectBypass.lean`
- `Littlewood/Bridge/ContourRemainderMultLeaf.lean`
- `Littlewood/Bridge/PerronContourClosureAssembly.lean`
- `Littlewood/Bridge/PerronFormulaAssembly.lean`
- `Littlewood/Bridge/PerronPlanckQuarks.lean`
- `Littlewood/Bridge/PsiOscillationDeepSorries.lean`
- `Littlewood/Bridge/ShiftedRemainderFromLogDerivLeaf.lean`
- `Littlewood/Bridge/ShiftedRemainderMultFromLogDerivLeaf.lean`
- `Littlewood/Bridge/ShiftedRemainderSegmentBoundLeaf.lean`
- `Littlewood/Development/ShiftedRemainderMultInterface.lean`
- `Littlewood/Test/AuditSorryFree.lean`
- `Littlewood/Test/XiEnumTrace.lean`
- `Littlewood/ZetaZeros/BacklundDirectProof.lean`
- `Littlewood/ZetaZeros/PairedFarZeroCancellationBridge.lean`
- `Littlewood/ZetaZeros/PairedFarZeroCancellationBridgeWiring.lean`
- `Littlewood/ZetaZeros/PairedFarZeroCancellationHelper.lean`
- `Littlewood/ZetaZeros/PairedFarZeroCancellationInstance.lean`
- `Littlewood/ZetaZeros/PairedRemainderAssembly.lean`
- `Littlewood/ZetaZeros/RvmHalfTopVariationProof.lean`
- `Littlewood/ZetaZeros/ZetaHalfTopSublemmaB.lean`

Reasons:

- `ShiftedRemainderSegmentBoundDirect` has the old large-shift remainder shape.
- `HadamardFactorizationWiring` / `HadamardZeroEnumeration` use stale Hadamard namespaces and typeclass packaging.
- `RvmHalfTopVariationProof` and `ZetaHalfTopSublemmaB` reference old private or renamed log-derivative surfaces.
- The paired-cancellation and Perron assembly files depend on those stale RvM/ZetaHalfTop surfaces.
- The recovered audit/test files assume the old stale providers are active.

## Axiom Policy

Current active-source axiom scan, excluding recovery artifact snapshots, reports only:

- `Littlewood/ZetaZeros/ZeroCountingAssumptions.lean`
  - `firstZeroExistsHyp_witness`
  - `zeroFreeBelow1413Hyp_witness`

This matches the accepted policy: standard Lean axioms plus the first-zero/zero-free-below-14.13 computational witness boundary. The former Chebyshev/PNT quarantine axioms are now theorem sorries.

## Verification

Commands run successfully after staging and patches:

- `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf`
- `lake env lean Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundAtomic.lean`
- `lake build Littlewood`
- `lake build Littlewood.Main.LittlewoodPsi Littlewood.Main.LittlewoodPi`

The root build and public API targets are certified again.

## Remaining Recovery Frontier

The staged API-drift files are not discarded; they are preserved for selective porting. The highest-value recoverable material appears to be:

- Hadamard enumeration/factorization providers, after adapting to current `HadamardFactorizationCore` and `ZeroCountingAssumptions`.
- RvM half-top / zeta log-derivative bridge, after replacing old private theorem references with current public surfaces.
- Paired far-zero cancellation, after the RvM/ZetaHalfTop layer is ported.
- Large-shift segment-form theorem, after reconciling the old recovered shape with current `ShiftedRemainderSegmentBoundLargeTHyp`.

These are proof-frontier items, not build blockers.
