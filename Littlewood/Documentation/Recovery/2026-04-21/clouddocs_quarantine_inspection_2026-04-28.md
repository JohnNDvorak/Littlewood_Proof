# CloudDocs Absent-Source Quarantine Inspection

Date: 2026-04-28

This records the quarantine pass over the 129 old CloudDocs source files that
were visible in Git metadata but absent from active source.

## Quarantine

- Quarantine root:
  `.recovery_artifacts/2026-04-21/clouddocs_absent_quarantine_2026-04-28/`
- Copied source mirror:
  `.recovery_artifacts/2026-04-21/clouddocs_absent_quarantine_2026-04-28/files/`
- Download report:
  `.recovery_artifacts/2026-04-21/clouddocs_absent_quarantine_2026-04-28/reports/download_report.json`
- `.recovery_artifacts/` is gitignored, so no quarantined source is on the
  active build path.

## Download Result

- Total old source paths: 129
- Copied into quarantine: 126
- Copy timeouts after `brctl download` returned successfully: 3
- Other copy failures: 0

The three paths that timed out in the first pass were:

- `Littlewood/Aristotle/HarmonicMaxPrinciple.lean`
- `Littlewood/Aristotle/Standalone/AbelMultiplicityCorrectionProof.lean`
- `Littlewood/Aristotle/Standalone/AnalyticOrderAtConj.lean`

These were recovered in a later exact-path retry pass; see below. They should
still not be blindly ported, because only two check directly and the Abel proof
depends on a staged legacy module chain.

## Retry Recovery Of Initial Timeouts

Retry quarantine root:
`.recovery_artifacts/2026-04-21/clouddocs_absent_quarantine_2026-04-28/retry_3_files_2026-04-28/`

The retry used exact Spotlight-discovered paths under:
`~/Library/Mobile Documents/com~apple~CloudDocs/Documents/Git/Littlewood_Proof/`

Recovered files:

- `Littlewood/Aristotle/HarmonicMaxPrinciple.lean`
  - size: 3610 bytes
  - sha1: `21f107ca3fa395425a2d47d0d6fc03f430a9e602`
- `Littlewood/Aristotle/Standalone/AbelMultiplicityCorrectionProof.lean`
  - size: 22165 bytes
  - sha1: `cbc7c524f26c2c79087e1de72022103638c17b5c`
- `Littlewood/Aristotle/Standalone/AnalyticOrderAtConj.lean`
  - size: 7766 bytes
  - sha1: `abfedd5a4c6dd82904dfe6115af21f4a7d844350`

Code-token scan over these three recovered files:

- Files with code `sorry`: 0
- Total code `sorry`: 0
- Files with `axiom`: 0
- Total `axiom`: 0

Focused Lean checks:

- `HarmonicMaxPrinciple.lean`: checks directly.
- `AnalyticOrderAtConj.lean`: checks directly.
- `AbelMultiplicityCorrectionProof.lean`: recovered and clean, but direct
  quarantine checking stops on missing module object for quarantined
  `ExplicitFormulaAbelMultiplicityCorrectionPlaceholder`.
- `LittlewoodKeyLemma.lean`, a large dependency of that placeholder chain,
  checks directly from quarantine with warnings only.

The Abel correction chain is therefore a real port candidate, but it must be
staged as a small coherent module chain, not pasted in as a single file.

## Active Source Integration

Integrated on 2026-04-28:

- `Littlewood/Aristotle/HarmonicMaxPrinciple.lean`
  - Direct salvage of the recovered rectangle harmonic maximum principle.
  - Focused check: `lake env lean Littlewood/Aristotle/HarmonicMaxPrinciple.lean`
    passes.
- `Littlewood/Aristotle/Standalone/AnalyticOrderAtConj.lean`
  - Direct salvage of conjugation invariance for `analyticOrderAt riemannZeta`.
  - Focused check:
    `lake env lean Littlewood/Aristotle/Standalone/AnalyticOrderAtConj.lean`
    passes.
- `Littlewood/Aristotle/Standalone/AbelMultiplicityCorrectionProof.lean`
  - Adapted salvage. The obsolete placeholder import was removed.
  - The focused `ZeroCountingMultiplicityExcessLogBoundHyp` compatibility class
    is now supplied from the current theorem-first
    `distinct_mult_compatibility_bound_iff_excess_bound` surface.
  - The recovered `AbelMultiplicityCorrectionBoundHyp` instance is preserved
    without new axioms.
  - Focused check:
    `lake env lean Littlewood/Aristotle/Standalone/AbelMultiplicityCorrectionProof.lean`
    passes.

The integrated files contain no code `sorry` and no `axiom`.

## Root Library Integration

Integrated into `Littlewood.lean` on 2026-04-28:

- `Littlewood.Aristotle.Standalone.AnalyticOrderAtConj`
- `Littlewood.Aristotle.HarmonicMaxPrinciple`
- `Littlewood.Aristotle.Standalone.AbelMultiplicityCorrectionProof`

This makes the recovered modules part of the normal root library import surface
without adding them to the strict public theorem files
`Littlewood/Main/LittlewoodPsi.lean` or `Littlewood/Main/LittlewoodPi.lean`.

Verification:

- `lake build Littlewood.Aristotle.Standalone.AnalyticOrderAtConj
  Littlewood.Aristotle.HarmonicMaxPrinciple
  Littlewood.Aristotle.Standalone.AbelMultiplicityCorrectionProof` passed.
- `lake env lean Littlewood.lean` passed.

## Debt Scan

Code-token scan over the 126 copied `.lean` files, stripping comments and
strings:

- Files with code `sorry`: 16
- Total code `sorry`: 28
- Files with `axiom`: 4
- Total `axiom`: 6
- `opaque`/`constant`: 0

Axiom-bearing files:

- `Littlewood/Aristotle/Standalone/HalfLineBoundClosure.lean`
- `Littlewood/Aristotle/Standalone/RHPiInhomogeneousPhaseDirectHonest.lean`
- `Littlewood/Aristotle/Standalone/RHPiTargetHeightControlDirectHonest.lean`
- `Littlewood/ZetaZeros/FirstZeroWitness.lean`

The first-zero witness is the expected first-zero external fact. The other
axiom-bearing files are not acceptable as active providers without replacement.

## Focused Lean Checks

These checks were run serially. No full build was run for this quarantine pass.

Clean from quarantine:

- `Littlewood/Aristotle/Standalone/SteepestDescentExpansion.lean`
- `Littlewood/Aristotle/Standalone/SmallTPerronSqrtBridge.lean`
- `Littlewood/Aristotle/Standalone/JensenZeroCounting.lean`
- `Littlewood/Aristotle/Standalone/PerronKernelTruncation.lean`
- `Littlewood/Aristotle/Standalone/PerronTruncationAtomics.lean`

Needs staged module recovery before a meaningful check:

- `Littlewood/Aristotle/Standalone/SmallTPerronLeafInstances.lean`
  imports quarantined `SmallTPerronSqrtBridge`.
- `Littlewood/Aristotle/Standalone/ShiftedRemainderSegmentBoundDirect.lean`
  imports quarantined Jensen modules.
- `Littlewood/Aristotle/Standalone/JensenZeroCountBridge.lean`
  imports quarantined `JensenZeroCountingOrderOne`.
- `Littlewood/Aristotle/Standalone/JensenZeroCountingOrderOne.lean`
  imports quarantined `JensenZeroCounting`.

Needs local API repair:

- `Littlewood/Bridge/HadamardConcreteBridge.lean`
  fails on missing or renamed
  `ZetaZeros.Density.zetaNontrivialZero_im_ne_zero`.
- `Littlewood/Aristotle/Standalone/RHPiInhomogeneousPhaseFitReduction.lean`
  fails because the old interface uses `piScale x`, while the current target
  expects `Real.sqrt x / Real.log x`.

## High-Signal Recovery Candidates

1. `SteepestDescentExpansion.lean`

   Clean, no `sorry`, no `axiom`, and checks directly. This is a real former
   frontier artifact. It packages the functional-equation side of the
   Riemann-Siegel steepest-descent expansion into a constructor for
   `SiegelSaddleExpansionHyp`, but it still depends on separate analytic leaves;
   it is not a final saddle provider by itself.

2. `PerronKernelTruncation.lean` and `PerronTruncationAtomics.lean`

   Clean and check directly. These are useful Perron kernel/truncation
   infrastructure candidates. They should be staged behind explicit imports,
   not dropped directly into the public path.

3. `SmallTPerronSqrtBridge.lean` plus `SmallTPerronLeafInstances.lean`

   The bridge checks directly after building the active `SmallTContourInfra`
   dependency. The leaf instance needs the bridge staged as a real module. This
   looks recoverable and low-risk, but it is a bounded-height Perron route, not
   the main large-shift closure.

4. Jensen zero-counting chain

   `JensenZeroCounting.lean` checks directly. The higher files need staged
   module recovery. This chain is relevant to direct shifted-remainder segment
   bounds and may help avoid false pointwise `-ζ'/ζ` provider classes.

5. `HadamardConcreteBridge.lean`

   No `sorry`/`axiom`, but current API drift blocks it. It is an optional bridge
   from Hadamard canonical zeros to concrete positive-ordinate zeta zeros. It
   should be repaired only if the active zero infrastructure still needs that
   concrete bridge.

6. RH-`pi` inhomogeneous phase files

   `RHPiInhomogeneousPhaseFitReduction.lean` is a clean reduction with API drift.
   The direct "honest" providers nearby contain private axioms and should be
   treated as subgoal maps only, not as acceptable final providers.

## Porting Rule

Do not copy the quarantine into active source wholesale. Port one coherent
candidate chain at a time, with a focused `lake env lean` or target build after
each staged move. A candidate is eligible only if it has no new nonstandard
axioms and its dependencies are explicit.
