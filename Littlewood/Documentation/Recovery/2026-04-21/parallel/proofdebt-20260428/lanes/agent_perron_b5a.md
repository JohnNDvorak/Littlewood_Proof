# Agent Perron/B5a Ledger

Branch: `proofdebt/20260428-perron-b5a`

Worktree: `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/perron-b5a`

## Ownership

- Writable code: B5a, Perron truncation, Hadamard, small-`T`, and shifted
  remainder provider files.
- Writable ledger: this file only.
- Coordinator-owned shared files are read-only.

## Live Targets

1. Close `shifted_remainder_bound_leaf`.
2. Produce a non-circular provider route for
   `ShiftedRemainderSegmentBoundLargeTHyp` and `SmallTPerronBoundHyp`.
3. Repair or bypass false/off-path Perron truncation statements instead of
   proving them as stated.

## Guardrails

- Do not prove `perron_tail_bound_core` as stated.
- Do not use a provider theorem that already consumes the provider class being
  supplied.
- Do not edit Atkinson, Pi/Phase, RS/Gabcke, or public main files.
- Do not run a full build.

## Requested Checks

- focused build for touched Perron/B5a module(s)
- strict public import probes for `Littlewood.Main.LittlewoodPsi` and
  `Littlewood.Main.LittlewoodPi`

## Session Log

### 2026-04-28 Launch

- Baseline: `acdc136`.
- Initial target: `shifted_remainder_bound_leaf`.
- Coordinator action: initial agent dispatched; Aristotle sidecar planned.

### 2026-04-28 Round 1 - B5a Large/Small Direct Split

- Classification: `CONDITIONAL_REDUCTION`.
- Theorem/file attacked:
  `Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.shifted_remainder_bound_leaf`
  in `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`.
- Code fact banked:
  `shifted_remainder_bound_candidate_of_large_small_direct`.
  This reduces the B5a full shifted-remainder leaf to two explicit ordinary
  hypotheses, not typeclass search:
  1. the direct large-`T` segment-form payload matching
     `ShiftedRemainderSegmentBoundLargeTHyp.bound`;
  2. the direct small-`T` payload matching
     `HadamardProductZeta.SmallTPerronBoundHyp.bound`.
  The theorem constructs only local instances from those supplied payloads and
  reuses `HadamardProductZeta.full_contour_bound` for the already-proved
  `T <= 16` / `T >= 16` case split.
- Circular/failed routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports, or any
  route that derives `SmallTPerronBoundHyp` from the full shifted-remainder
  provider being supplied.  Did not touch or attempt `perron_tail_bound_core`
  as stated.
- Files changed:
  `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf`
  followed by strict public import probes for `Littlewood.Main.LittlewoodPsi`
  and `Littlewood.Main.LittlewoodPi`.
- Smallest next theorem:
  close one of the two explicit inputs now exposed by
  `shifted_remainder_bound_candidate_of_large_small_direct`, preferably the
  small-`T` payload
  `∃ C₂ > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    |HadamardProductZeta.shiftedRemainderRe x T| <=
      C₂ * (sqrt/log shape + (log x)^2)`
  via the Perron truncation/weighted-kernel cutoff chain.  The alternate large
  atom is the direct segment-form payload of
  `ShiftedRemainderSegmentBoundLargeTHyp.bound`.
- Coordinator action required: run the requested validation; no full build
  requested.

### 2026-04-28 Round 2 - Small-T Weighted Kernel Handoff

- Classification: `STRICTER_SMALL_T_REDUCTION`.
- Theorem/file attacked:
  `HadamardProductZeta.SmallTPerronBoundHyp.bound` direct payload via
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`.
- Code facts banked:
  `small_T_direct_bound_from_weighted_kernel_and_residue` reduces the direct
  small-`T` shifted-remainder payload to:
  1. finite weighted Perron-kernel cutoff:
     `∃ Cw > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
       perronKernelWeightedCutoffError x T <= Cw * (Real.log x)^2`;
  2. bounded-height residue extraction for the concrete
     `perronVerticalIntegral`:
     `∃ Cᵣ > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
       |perronVerticalIntegral x T - (x - HadamardProductZeta.zeroSumRe x T)|
         <= Cᵣ * (sqrt/log small-T shape)`.
  Also banked `small_T_perron_bound_hyp_from_weighted_kernel_and_residue`, a
  non-instance provider constructor for `SmallTPerronBoundHyp` from exactly
  those two atoms.
- Existing facts reused:
  `small_T_perronKernelFiniteSum_cutoff_bound_from_weighted_error`;
  `small_T_perronVerticalIntegral_truncation_bound_from_kernel_sum_bound`;
  `small_T_direct_bound_from_perronVerticalIntegral_components`;
  `HadamardProductZeta.small_T_perron_bound_hyp_of_direct_bound`.
- Circular/failed routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports, or any
  theorem consuming `SmallTPerronBoundHyp`.  Did not attempt
  `perron_tail_bound_core` as stated; the new route only composes the existing
  exchange/kernel reductions and records the true remaining atoms.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`
  followed by the strict public import probes for `Littlewood.Main.LittlewoodPsi`
  and `Littlewood.Main.LittlewoodPi` if the focused build passes.
- Smallest next theorem:
  prove the finite weighted cutoff atom
  `∃ Cw > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelWeightedCutoffError x T <= Cw * (Real.log x)^2`.
  The second remaining small-`T` atom is the bounded-height residue extraction
  for `perronVerticalIntegral`; attack it only after the weighted cutoff path
  stalls or validates as harder.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-28 Round 3 - Weighted Kernel Boundary Split

- Classification: `BOUNDARY_ATOM_ISOLATION`.
- Theorem/file attacked:
  finite weighted cutoff atom below
  `small_T_direct_bound_from_weighted_kernel_and_residue`, in
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`.
- Code facts banked:
  `perronKernelWeightedBoundaryWindowError` and
  `perronKernelWeightedOffBoundaryWindowError`, splitting the finite
  `perronKernelWeightedCutoffError` at the sharp transition window
  `|x - n| <= x / T`.
  Proved
  `perronKernelWeightedCutoffError_eq_boundary_add_offBoundary`, the exact
  finite-sum partition, and
  `small_T_weighted_kernel_cutoff_bound_from_boundary_split`, which reduces
  the global weighted cutoff atom to separate `O((log x)^2)` estimates for the
  boundary window and its complement.
- Local assessment:
  the weighted cutoff target is not safely reachable by applying the existing
  per-term bounds uniformly, because those bounds contain `log (x / n)` and
  degenerate at the sharp cutoff near `n = x`.  The new boundary-window atom is
  the explicit obstruction to any direct per-term route.
- Circular/failed routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports, or any
  theorem consuming `SmallTPerronBoundHyp`.  Did not attempt
  `perron_tail_bound_core` as stated.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`
  followed by strict public import probes for `Littlewood.Main.LittlewoodPsi`
  and `Littlewood.Main.LittlewoodPi` if the focused build passes.
- Smallest next theorem:
  prove or refute the boundary-window atom
  `∃ Cb > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelWeightedBoundaryWindowError x T <= Cb * (Real.log x)^2`.
  If this stalls, the next off-boundary theorem is the complement estimate for
  `perronKernelWeightedOffBoundaryWindowError`, where existing per-term Perron
  bounds should be applicable away from `log (x / n) = 0`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-28 Round 4 - Boundary Window Weight Reduction

- Classification: `BOUNDARY_WEIGHT_REDUCTION`.
- Theorem/file attacked:
  `perronKernelWeightedBoundaryWindowError` bound in
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`.
- Code facts banked:
  added `perronKernelBoundaryWindowVonMangoldtWeight`, the exact pure
  von Mangoldt weight of the boundary set
  `{n ∈ range (floor x + 1) | |x - n| <= x / T}`.
  Proved
  `perronKernelWeightedBoundaryWindowError_le_kernelSup_mul_vonMangoldtWeight`,
  controlling the boundary weighted error by a uniform kernel-error supremum
  times that pure arithmetic weight.  Added
  `small_T_boundary_window_bound_from_kernel_sup_and_vonMangoldt_weight`,
  reducing the boundary-window atom to:
  1. a uniform bounded-height kernel-error supremum on the boundary window;
  2. the exact arithmetic weight estimate
     `perronKernelBoundaryWindowVonMangoldtWeight x T <= Cv * (Real.log x)^2`.
- Local assessment:
  a direct proof of the boundary-window atom remains too broad.  The current
  split exposes the true arithmetic obstruction: for `2 <= T <= 16`, the
  window `|x - n| <= x / T` is macroscopic unless a sharper kernel cancellation
  or a stronger arithmetic interval-weight statement is supplied.
- Circular/failed routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports, or any
  theorem consuming `SmallTPerronBoundHyp`.  Did not use or modify
  `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`
  followed by strict public import probes for `Littlewood.Main.LittlewoodPsi`
  and `Littlewood.Main.LittlewoodPi` if the focused build passes.
- Smallest next theorem:
  first prove the uniform boundary kernel supremum if it is locally reachable:
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈ boundary(x,T),
    |1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T| <= K`.
  The arithmetic theorem then needed is the exact boundary weight estimate
  `∃ Cv > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelBoundaryWindowVonMangoldtWeight x T <= Cv * (Real.log x)^2`;
  this may be false for the current macroscopic window and should be checked
  before attempting a long proof.
- Coordinator action required: run the requested focused validation; no full
  build requested.
