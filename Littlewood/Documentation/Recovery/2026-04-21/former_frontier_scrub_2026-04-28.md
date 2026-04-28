# Former Frontier Scrub

Date: 2026-04-28 CDT

Branch: `recovery/provider-forensics-2026-04-21`

Current certified head before this scrub:

- `cd61d5e Restore analytic proof debt as explicit sorries`
- Full `lake build` passed with 8282 jobs.

## Purpose

Check whether any former pre-crash files or stale worktree files are ahead of
the current recovered frontier and should be brought back before the proof
campaign continues.

## Sources Checked

1. Active source tree:
   `/Users/john.n.dvorak/Projects/Littlewood_Proof`
2. Stale local worktrees:
   `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/*`
3. Banked recovery artifacts:
   `.recovery_artifacts/2026-04-21`
4. iCloud CloudDocs Git tree metadata:
   `/Users/john.n.dvorak/Library/Mobile Documents/com~apple~CloudDocs/Documents/Git/Littlewood_Proof`
5. iCloud CloudDocs GitHub tree:
   `/Users/john.n.dvorak/Library/Mobile Documents/com~apple~CloudDocs/Documents/GitHub/Littlewood_Proof`

## Result

### Local worktrees

The stale local worktrees are not ahead of the current recovery branch.

- Each stale worktree is still based at `0993b9d Recover public provider baseline`.
- Current source has the merged lane work plus later recovery/de-axiom commits.
- The only apparent "old has fewer sorries" signal is
  `PerronTruncationInfra.lean`: stale worktrees have one direct `sorry`, current
  has two. This is not a recovered proof. The current file added a sharper
  finite weighted cutoff reduction leaf, so the extra `sorry` is a newly
  exposed honest theorem obligation, not a regression to be reverted.
- `AnalyticAxioms.lean` in stale worktrees still contains the removed private
  analytic axiom providers, so it must not be used as recovery source.

Conclusion: no stale worktree patch should be ported wholesale.

### Banked local artifacts

Readable banked artifacts remain correctly classified:

- `.recovery_artifacts/2026-04-21/banked/ZetaMeanSquareHalfFromHardyAsymptotic.lean`
  is a compiled bridge artifact, but still off-path because the active
  non-circular B1 lane lacks upstream provider supply.
- `.recovery_artifacts/2026-04-21/evidence/ContourRemainderMultLeaf.lean`
  is evidence for the mult-contour/Perron route and still contains explicit
  analytic gap boundaries.
- `.recovery_artifacts/2026-04-21/evidence/PairedFarZeroCancellationBridge.lean`
  is evidence for the paired far-zero cancellation route and still contains
  a real paired-remainder bound gap.
- `.recovery_artifacts/2026-04-21/evidence/ZeroAvoidingHeight.lean`
  is a useful combinatorial height-selection proof artifact, but it is not
  mapped to the current public provider frontier.

Conclusion: these are already banked and documented; no source port is justified
until a current class/theorem leaf consumes them.

### CloudDocs Git tree

The CloudDocs Git worktree remains unsafe as direct code truth:

- Git metadata operations hang.
- File metadata is readable.
- File content reads from the CloudDocs `Documents/Git/Littlewood_Proof` tree
  hang, even for small files such as `PerronFormulaCIF.lean`.
- `brctl download` on a representative file returned, but the subsequent file
  read still hung.

Metadata shows 722 old `.lean` source files under the CloudDocs tree. Comparing
file names against current active source excluding `Littlewood/Documentation`
finds 129 old source files absent from the active source tree. These are listed
below so the old frontier is not lost.

Conclusion: do not blindly copy from this CloudDocs tree. Treat it as an
unhydrated/unsafe source until individual files can be read, compiled, and
mapped to an active theorem leaf.

## CloudDocs Absent Source Manifest

These files exist by metadata in the old CloudDocs Git tree and are absent from
the current active source tree, excluding documentation snapshots.

```text
Littlewood/Aristotle/HarmonicMaxPrinciple.lean
Littlewood/Aristotle/Standalone/AbelMultiplicityCorrectionProof.lean
Littlewood/Aristotle/Standalone/AnalyticOrderAtConj.lean
Littlewood/Aristotle/Standalone/AnalyticQuotient.lean
Littlewood/Aristotle/Standalone/ArctanIntegralBound.lean
Littlewood/Aristotle/Standalone/ArithBound.lean
Littlewood/Aristotle/Standalone/ContourRemainderMultFromHadamard.lean
Littlewood/Aristotle/Standalone/ContourShift.lean
Littlewood/Aristotle/Standalone/DiophantineSimultaneousApprox.lean
Littlewood/Aristotle/Standalone/DlVPCoreEstimateAristotle.lean
Littlewood/Aristotle/Standalone/ExplicitFormulaAbelBoundMultBridge.lean
Littlewood/Aristotle/Standalone/ExplicitFormulaAbelBoundPlaceholder.lean
Littlewood/Aristotle/Standalone/ExplicitFormulaAbelMultiplicityCorrectionPlaceholder.lean
Littlewood/Aristotle/Standalone/ExplicitFormulaAssemblyArithmetic.lean
Littlewood/Aristotle/Standalone/ExternalPort/PerronLinearLogDirectSorry.lean
Littlewood/Aristotle/Standalone/ExternalPort/PerronLinearLogWitnessLeaf.lean
Littlewood/Aristotle/Standalone/ExternalPort/RefactoredPNTContourAndRHPiProviderLeaf.lean
Littlewood/Aristotle/Standalone/FarSumHelpers.lean
Littlewood/Aristotle/Standalone/HadamardConstructiveBridge.lean
Littlewood/Aristotle/Standalone/HadamardFactorizationCore.lean
Littlewood/Aristotle/Standalone/HadamardFactorizationWiring.lean
Littlewood/Aristotle/Standalone/HadamardLiouvilleArgument.lean
Littlewood/Aristotle/Standalone/HadamardLiouvilleGeneralized.lean
Littlewood/Aristotle/Standalone/HadamardMultEnumeration.lean
Littlewood/Aristotle/Standalone/HadamardProductConvergence.lean
Littlewood/Aristotle/Standalone/HadamardXiCoreInstance.lean
Littlewood/Aristotle/Standalone/HadamardXiEnumCleanProvider.lean
Littlewood/Aristotle/Standalone/HadamardXiHypDensityProvider.lean
Littlewood/Aristotle/Standalone/HadamardZeroEnumeration.lean
Littlewood/Aristotle/Standalone/HadamardZeroExistence.lean
Littlewood/Aristotle/Standalone/HalfLineBoundClosure.lean
Littlewood/Aristotle/Standalone/HalfLineIntegralBound.lean
Littlewood/Aristotle/Standalone/JensenLocalDensityBridge.lean
Littlewood/Aristotle/Standalone/JensenZeroCountBridge.lean
Littlewood/Aristotle/Standalone/JensenZeroCounting.lean
Littlewood/Aristotle/Standalone/JensenZeroCountingOrderOne.lean
Littlewood/Aristotle/Standalone/LittlewoodClassicalBridge.lean
Littlewood/Aristotle/Standalone/LittlewoodDiagonalEval.lean
Littlewood/Aristotle/Standalone/LittlewoodKeyLemma.lean
Littlewood/Aristotle/Standalone/LittlewoodPLSetup.lean
Littlewood/Aristotle/Standalone/LittlewoodPiArgApproxLeafInstances.lean
Littlewood/Aristotle/Standalone/LittlewoodPiLeafInstances.lean
Littlewood/Aristotle/Standalone/LittlewoodPsiLeafInstances.lean
Littlewood/Aristotle/Standalone/LittlewoodUpperHalfStripClean.lean
Littlewood/Aristotle/Standalone/LowHeightShellSumCorrected.lean
Littlewood/Aristotle/Standalone/MinimumModulusPigeonhole.lean
Littlewood/Aristotle/Standalone/MultBridgeHelpers.lean
Littlewood/Aristotle/Standalone/MultConjugatePairing.lean
Littlewood/Aristotle/Standalone/MultKernelConversion.lean
Littlewood/Aristotle/Standalone/MultWeightedExplicitFormulaProof.lean
Littlewood/Aristotle/Standalone/NearHeightShellSumCorrected.lean
Littlewood/Aristotle/Standalone/NonvanishingEntireLinear.lean
Littlewood/Aristotle/Standalone/PairedRemainderIntegralCorrected.lean
Littlewood/Aristotle/Standalone/PerronAssemblyAtomics.lean
Littlewood/Aristotle/Standalone/PerronContourLiteralBounds.lean
Littlewood/Aristotle/Standalone/PerronFormulaAtomics.lean
Littlewood/Aristotle/Standalone/PerronFormulaCIF.lean
Littlewood/Aristotle/Standalone/PerronFubiniAtomics.lean
Littlewood/Aristotle/Standalone/PerronKernelAtomics.lean
Littlewood/Aristotle/Standalone/PerronKernelBound.lean
Littlewood/Aristotle/Standalone/PerronKernelTruncation.lean
Littlewood/Aristotle/Standalone/PerronResidueAtoms.lean
Littlewood/Aristotle/Standalone/PerronSegmentBound.lean
Littlewood/Aristotle/Standalone/PerronSublemmas.lean
Littlewood/Aristotle/Standalone/PerronTruncationAtomics.lean
Littlewood/Aristotle/Standalone/PsiClassicalSupport.lean
Littlewood/Aristotle/Standalone/PsiThetaLllTransfer.lean
Littlewood/Aristotle/Standalone/RHPiClassicalPsiMeanSquare.lean
Littlewood/Aristotle/Standalone/RHPiCorrectedCanonicalFromPerronBridge.lean
Littlewood/Aristotle/Standalone/RHPiExplicitFormulaErrorAtFixedHeight.lean
Littlewood/Aristotle/Standalone/RHPiInhomogeneousPhaseDirectHonest.lean
Littlewood/Aristotle/Standalone/RHPiInhomogeneousPhaseFitReduction.lean
Littlewood/Aristotle/Standalone/RHPiMeanSquareReduction.lean
Littlewood/Aristotle/Standalone/RHPiPsiThetaPiCorrection.lean
Littlewood/Aristotle/Standalone/RHPiShiftedRemainderDivLogFixedHeight.lean
Littlewood/Aristotle/Standalone/RHPiTargetHeightControlDirectHonest.lean
Littlewood/Aristotle/Standalone/RHPiZeroSumConventionBridge.lean
Littlewood/Aristotle/Standalone/RectCircleEquality.lean
Littlewood/Aristotle/Standalone/ResidueExtraction.lean
Littlewood/Aristotle/Standalone/RvMPartialSummation.lean
Littlewood/Aristotle/Standalone/ShiftedRemainderSegmentBoundDirect.lean
Littlewood/Aristotle/Standalone/SiegelContourIntegral.lean
Littlewood/Aristotle/Standalone/SmallTPerronLeafInstances.lean
Littlewood/Aristotle/Standalone/SmallTPerronSqrtBridge.lean
Littlewood/Aristotle/Standalone/SteepestDescentExpansion.lean
Littlewood/Aristotle/Standalone/SwissCheeseIntegral.lean
Littlewood/Aristotle/Standalone/TruncatedPerronIdentity.lean
Littlewood/Aristotle/Standalone/XiGrowthBound.lean
Littlewood/Aristotle/Standalone/ZetaLogDerivHorizontalBound.lean
Littlewood/Aristotle/Standalone/ZetaLogDerivIntegralHalfOneDirect.lean
Littlewood/Aristotle/Standalone/ZetaLogDerivIntegralOneTwoDirect.lean
Littlewood/Aristotle/Standalone/ZetaLogDerivLocalBound.lean
Littlewood/Aristotle/Standalone/ZetaLogDerivOneTwoDirectBypass.lean
Littlewood/Bridge/ContourRemainderMultLeaf.lean
Littlewood/Bridge/HadamardConcreteBridge.lean
Littlewood/Bridge/PerronContourClosureAssembly.lean
Littlewood/Bridge/PerronFormulaAssembly.lean
Littlewood/Bridge/PerronPlanckQuarks.lean
Littlewood/Bridge/PerronPlanckQuarksPhase2.lean
Littlewood/Bridge/PerronSignedCancellationHelpers.lean
Littlewood/Bridge/PsiOscillationDeepSorries.lean
Littlewood/Bridge/ShiftedRemainderFromLogDerivLeaf.lean
Littlewood/Bridge/ShiftedRemainderMultFromLogDerivLeaf.lean
Littlewood/Bridge/ShiftedRemainderSegmentBoundLeaf.lean
Littlewood/CoreLemmas/DirichletIntegralProofs.lean
Littlewood/CoreLemmas/LandauLemmaProof.lean
Littlewood/CoreLemmas/SumOverPositiveOrdinatesProof.lean
Littlewood/Development/ShiftedRemainderMultInterface.lean
Littlewood/SigmaMultSummability.lean
Littlewood/Test/AuditSorryFree.lean
Littlewood/Test/XiEnumTrace.lean
Littlewood/ZetaZeros/BacklundDirectProof.lean
Littlewood/ZetaZeros/ChebyshevErrorBoundProof.lean
Littlewood/ZetaZeros/ErrorBoundHelpers.lean
Littlewood/ZetaZeros/ErrorBoundOptimization.lean
Littlewood/ZetaZeros/FirstZeroWitness.lean
Littlewood/ZetaZeros/GammaHalfTopVariationBound.lean
Littlewood/ZetaZeros/PairedFarZeroCancellationBridge.lean
Littlewood/ZetaZeros/PairedFarZeroCancellationBridgeWiring.lean
Littlewood/ZetaZeros/PairedFarZeroCancellationHelper.lean
Littlewood/ZetaZeros/PairedFarZeroCancellationInstance.lean
Littlewood/ZetaZeros/PairedRemainderAssembly.lean
Littlewood/ZetaZeros/PairedRemainderIntegral.lean
Littlewood/ZetaZeros/PairedRemainderLogSq.lean
Littlewood/ZetaZeros/RvmHalfTopVariationProof.lean
Littlewood/ZetaZeros/ZeroAvoidingHeight.lean
Littlewood/ZetaZeros/ZeroCountingCrudeBoundFromMult.lean
Littlewood/ZetaZeros/ZetaHalfTopSublemmaB.lean
Littlewood/ZetaZeros/ZetaHalfTopSublemmas.lean
```

## Current Recovery Decision

No active source file was ported in this scrub.

The current recovery branch is build-certified and has the honest no-analytic-
axiom frontier restored. The old CloudDocs tree may contain useful proof
fragments, especially in Perron/Hadamard/zero infrastructure, but file content
is not safely readable yet. The correct next action is to continue proof work
from the current active theorem leaves, and only port one former file at a time
after it is readable, mapped to a current class/theorem, and validated by a
focused build.

