# Lane #3 RS7 Closeout Plan (Phase-Lift Required)

Date: 2026-03-04
Owner lane: RS/ErrorTerm/RSBlockBounds
Goal: close delegated RS7 cluster in a way that can be made unconditional later, without adding axioms.

## Current RS7 frontier
- `Littlewood/Aristotle/ErrorTermExpansion.lean`
  - `theta_stirling_expansion`
  - `off_resonance_integral_bound`
  - `off_resonance_sum_bound`
  - `errorTerm_expansion`
- `Littlewood/Aristotle/RSBlockBounds.lean`
  - `c_block_nonneg`
  - `c_block_antitone`
  - `block_interpolation`

## Confirmed blockers (from in-repo analysis)
1. Principal-branch incompatibility
- `StirlingArgGamma.stirling_arg_gamma_asymp_false`
- `StirlingArgGamma.stirling_arg_gamma_false`

Interpretation: the global-value Stirling asymptotic for current principal-branch `hardyTheta` is false as stated.

2. Off-resonance VdC chain is assumption-only
- Available:
  - `VdcFirstDerivTest.vdc_cos_bound`
  - `StationaryPhasePerMode.per_mode_tail_bound`
- Missing unconditionally instantiated inputs:
  - support differentiability/nonvanishing/second-derivative classes in `HardyFirstMomentWiring`
- No unconditional theorem in current repo identifies the exact phase derivative needed by `off_resonance_integral_bound` with sufficient strength on full block intervals.

3. RSBlockBounds triple depends on unresolved `errorTerm_expansion`
- `c_block_nonneg`, `c_block_antitone`, `block_interpolation` need integrated sign/coherence data not currently proved.

## Execution strategy

### Track A (core): phase-lift infrastructure
Objective: replace branch-sensitive theta-value usage with branch-stable phase infrastructure for stationary-phase estimates.

A1. Introduce a branch-stable phase object for analysis-only lemmas.
- Keep existing `hardyTheta` definition untouched for compatibility.
- Add separate analysis phase path based on existing `hardyExpPhase`/`hardyPhaseReal` machinery in `HardyFirstMomentWiring`.

A2. Prove an off-resonance integral theorem in analysis-phase form.
Target theorem shape:
- bound `|∫_{block k} cos(phase_n)|` by `const / gap(k,n)`
- built from `vdc_cos_bound` + explicit lower bound hypotheses.

A3. Bridge theorem from analysis phase to current cosine integrand form.
- Use definitional identity `hardyPhaseReal n t = hardyTheta t - t*log(n+1)` where valid.
- isolate any slit-plane/differentiability requirements as local hypotheses (no global axiom).

### Track B (RS expansion payload)
Objective: convert local phase/control theorems into block-level RS remainder statement.

B1. Prove a support-level sign-coherence lemma from the expansion payload.
- input: expansion with error control
- output: block partial integral interpolation with uniform constant.

B2. Derive correction-sequence properties.
- prove `c_block_nonneg`
- prove antitonicity (or prove a stronger monotone majorant and derive antitone).

### Track C (integration into existing files)
C1. `ErrorTermExpansion.lean`
- replace `off_resonance_integral_bound` sorry with theorem from Track A.
- replace `off_resonance_sum_bound` sorry with sum-level theorem from A+B.
- leave `theta_stirling_expansion` only if reformulated branch-stably; otherwise derive downstream without it.

C2. `RSBlockBounds.lean`
- consume Track B lemmas to close the 3 RSBlockBounds sorries.

## Acceptance checks
- `lake build Littlewood.Aristotle.ErrorTermExpansion`
- `lake build Littlewood.Aristotle.RSBlockBounds`
- `./scripts/critical_path_expanded_status.sh`
  - delegated sorries reduced from 12 by at least the RS7 subset.

## Non-goals in this lane
- B1 deep leaf (`HardyAfeSignedGapDeepLeaf`)
- B5a deep leaf (`ExplicitFormulaPsiB5aShiftedBoundDeepLeaf`)
- RH-pi exact seed 3

