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

### 2026-04-28 Aristotle Harvest Integration

- Job: `43160ae0-78e7-4d7e-b8af-76332fd6c59f`.
- Classification: `NON_CIRCULAR_REDUCTION`.
- Target audited:
  `shifted_remainder_bound_leaf` and its small-T provider route.
- Result:
  the clean public-path shape is a reduction to two independent classes,
  `ShiftedRemainderSegmentBoundLargeTHyp` and
  `HadamardProductZeta.SmallTPerronBoundHyp`.
- Guardrail:
  do not derive small-T Perron from `shifted_remainder_bound_atomic`, because
  that route consumes the shifted-remainder provider class through the
  skeleton namespace and is circular.
- Failed route:
  do not prove or depend on `perron_tail_bound_core` as stated.
- Current lane guidance:
  the lane has already validated the exact-hit split. Continue on the
  punctured-window decaying kernel estimate, then off-boundary and compact
  residue extraction.

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

### 2026-04-28 Coordinator Validation - Exact-Hit Boundary Error

- Classification: `VALIDATED_WITH_COORDINATOR_FIX`.
- Focused command:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Result:
  initial validation failed on two local proof-shape issues in
  `perronKernelWeightedExactHitBoundaryError_le_kernelSup_mul_log`:
  the `Finset.card_le_one_iff` intro order was wrong, and the final
  `mul_le_mul` call supplied `vonMangoldt_nonneg n` where Lean required
  `0 <= Real.log x`.
- Fix:
  corrected the intro order to `intro a b ha hb` and supplied the already
  available `hlogx_nonneg` to `mul_le_mul`.
- Final validation:
  focused build completed successfully.  Public import probes were deferred
  because this did not close a public provider yet.
- Smallest next theorem:
  prove the punctured-window decaying kernel estimate, excluding the exact hit.

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

### 2026-04-28 Round 5 - Boundary Weight Scale Correction

- Classification: `FALSE_SCALE_OBSTRUCTION`.
- Theorem/file attacked:
  scale-check for
  `perronKernelBoundaryWindowVonMangoldtWeight x T <= Cv * (Real.log x)^2`
  in `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`.
- Finding:
  the pure von Mangoldt boundary-window estimate with right side
  `O((log x)^2)` is scale-incorrect for the current window.  For fixed
  `2 <= T <= 16`, the set
  `{n <= floor x | |x - n| <= x / T}` has macroscopic length comparable to
  `x / T`; by the usual Chebyshev/PNT scale its Λ-weight is linear-window
  scale, not logarithmic-square scale.  Therefore a uniform kernel supremum
  times this pure weight cannot close the boundary-window atom unless the
  kernel supremum itself decays like `T * (log x)^2 / x`.
- Code facts banked:
  updated the old
  `small_T_boundary_window_bound_from_kernel_sup_and_vonMangoldt_weight`
  docstring to mark it diagnostic rather than the live scale-correct route.
  Added
  `small_T_boundary_window_bound_from_scaled_kernel_and_linear_weight`, which
  replaces the false pure-weight path with the correct product scale:
  1. boundary-window kernel error
     `<= K * (T * (Real.log x)^2 / x)`;
  2. boundary-window von Mangoldt weight
     `<= Cv * (x / T)`;
  together imply
  `perronKernelWeightedBoundaryWindowError x T <= Cb * (Real.log x)^2`.
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
  prove the scale-correct linear window estimate
  `∃ Cv > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelBoundaryWindowVonMangoldtWeight x T <= Cv * (x / T)`.
  After that, prove the decaying boundary-kernel estimate
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈ boundary(x,T),
    |1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T|
      <= K * (T * (Real.log x)^2 / x)`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-28 Round 6 - Boundary Window Weight Closure

- Classification: `ATOM_CLOSED_PENDING_VALIDATION`.
- Theorem/file attacked:
  scale-correct linear boundary-window von Mangoldt weight estimate in
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`.
- Code facts banked:
  added `dirichletPhase_chebyshevPsi_eq_chebyshev_psi`, identifying the
  local finite-range `DirichletPhaseAlignment.chebyshevPsi` with Mathlib's
  `Chebyshev.psi`.
  Added `dirichletPhase_chebyshevPsi_le_const_mul_self`, importing Mathlib's
  global Chebyshev linear bound onto the local definition.
  Added `perronKernelBoundaryWindowVonMangoldtWeight_le_chebyshevPsi`, bounding
  the boundary-window sum by the full Chebyshev sum at height `x`.
  Proved `small_T_boundary_window_vonMangoldt_weight_linear_bound`:
  `∃ Cv > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelBoundaryWindowVonMangoldtWeight x T <= Cv * (x / T)`.
- Scale check:
  the theorem uses the correct `x / T` window scale.  The constant is enlarged
  by `T <= 16`, so no false logarithmic-square interval-weight assertion is
  used.
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
  prove the decaying boundary-kernel estimate
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈ boundary(x,T),
    |1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T|
      <= K * (T * (Real.log x)^2 / x)`.
  If this estimate is too strong at exact or near-integer `x`, refine the
  boundary decomposition further before attempting the off-boundary estimate.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-28 Round 7 - Boundary Kernel Diagonal Split

- Classification: `TARGET_FALSE_AS_STATED_REDUCED_PENDING_VALIDATION`.
- Theorem/file attacked:
  decaying boundary-kernel estimate for `perronPerTermIntegral` on the full
  boundary window in
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`.
- Scale obstruction:
  the requested full-window per-term estimate
  `|1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T|
    <= K * (T * (Real.log x)^2 / x)`
  is false when `x` is an integer and `n = x`.  Then `x / n = 1`, and the
  truncated Perron kernel has a jump-size error bounded away from zero for
  fixed `2 <= T <= 16`, while `T * (log x)^2 / x -> 0`.
- Code facts banked:
  added `perronKernelWeightedExactHitBoundaryError` for the exact integer
  diagonal `n = x`.
  Added `perronKernelWeightedPuncturedBoundaryWindowError` for the boundary
  window with `n = x` removed.
  Proved
  `perronKernelWeightedBoundaryWindowError_eq_exactHit_add_punctured`, an exact
  finite-sum split of the boundary window into these two pieces.
  Added
  `perronKernelWeightedPuncturedBoundaryWindowError_le_kernelSup_mul_vonMangoldtWeight`,
  bounding the punctured weighted error by a punctured kernel supremum times the
  full boundary-window von Mangoldt weight.
  Added
  `small_T_boundary_window_bound_from_punctured_scaled_kernel_linear_weight_and_exactHit`,
  reducing the boundary-window atom to:
  1. an exact-hit weighted error bound
     `perronKernelWeightedExactHitBoundaryError x T <= Ce * (Real.log x)^2`;
  2. a punctured-window decaying kernel bound at scale
     `K * (T * (Real.log x)^2 / x)`;
  3. the already validated linear boundary-window weight bound
     `perronKernelBoundaryWindowVonMangoldtWeight x T <= Cv * (x / T)`.
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
  first close the exact-hit bound
  `∃ Ce > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelWeightedExactHitBoundaryError x T
      <= Ce * (Real.log x)^2`.
  Then attack the punctured kernel estimate, with `n = x` excluded:
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈ puncturedBoundary(x,T),
    |1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T|
      <= K * (T * (Real.log x)^2 / x)`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-28 Round 8 - Exact-Hit Boundary Error Closure

- Classification: `ATOM_CLOSED_PENDING_VALIDATION`.
- Theorem/file attacked:
  exact-hit weighted boundary error
  `perronKernelWeightedExactHitBoundaryError` in
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`.
- Code facts banked:
  added `log_le_const_mul_log_sq_of_ge_two`, absorbing `Real.log x` into
  `(Real.log x)^2` uniformly for `x >= 2`.
  Added `perronKernelWeightedExactHitBoundaryError_le_kernelSup_mul_log`, which
  uses the fact that the exact-hit filter `(n : ℝ) = x` has cardinal at most
  one and `vonMangoldt_le_log` gives `Λ(n) <= Real.log x`.
  Added `small_T_exactHit_kernel_uniform_bound`, a direct bounded-height
  Perron-kernel estimate at the exact hit.  It uses only
  `perron_per_term_abs_bound_general`, `T <= 16`, and `c_param_gt_one`; no tail
  theorem is used.
  Proved `small_T_exactHit_boundary_error_bound`:
  `∃ Ce > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelWeightedExactHitBoundaryError x T
      <= Ce * (Real.log x)^2`.
- Scale check:
  the exact-hit kernel error is only uniformly bounded, not decaying.  This is
  sufficient because the exact-hit set has at most one term and its
  von Mangoldt weight is `O(log x)`, then absorbed into `O((log x)^2)`.
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
  prove the punctured-window decaying kernel estimate, with `n = x` excluded:
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈ puncturedBoundary(x,T),
    |1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T|
      <= K * (T * (Real.log x)^2 / x)`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-28 Round 9 - Punctured Window Near-Diagonal Split

- Classification: `TARGET_FALSE_AS_STATED_REDUCED_PENDING_VALIDATION`.
- Theorem/file attacked:
  punctured-window decaying kernel estimate below
  `small_T_boundary_window_bound_from_punctured_scaled_kernel_linear_weight_and_exactHit`
  in `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`.
- Scale obstruction:
  excluding only the exact hit `(n : ℝ) = x` is still not enough for the
  pointwise decaying estimate
  `|1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T|
    <= K * (T * (Real.log x)^2 / x)`.
  For large real `x` arbitrarily close to an integer `n`, the truncated Perron
  kernel remains in its transition region while the right side tends to zero.
  The statement therefore needs a near-diagonal punctured atom before a
  separated pointwise decay theorem can be scale-correct.
- Code facts banked:
  added `perronKernelWeightedNearDiagonalPuncturedBoundaryError`, the
  punctured boundary contribution with `|x - n| <= 1`.
  Added `perronKernelWeightedSeparatedPuncturedBoundaryError`, the remaining
  punctured contribution with `¬ |x - n| <= 1`.
  Proved
  `perronKernelWeightedPuncturedBoundaryWindowError_eq_nearDiagonal_add_separated`,
  an exact finite-sum partition of the punctured boundary window.
  Added
  `perronKernelWeightedSeparatedPuncturedBoundaryError_le_kernelSup_mul_vonMangoldtWeight`,
  controlling the separated weighted piece by a separated kernel supremum times
  the full validated boundary-window von Mangoldt weight.
  Added
  `small_T_punctured_boundary_window_bound_from_nearDiagonal_and_separated_kernel`,
  reducing the punctured-window weighted bound to:
  1. a near-diagonal punctured weighted error bound
     `perronKernelWeightedNearDiagonalPuncturedBoundaryError x T
       <= Cn * (Real.log x)^2`;
  2. a separated punctured pointwise kernel estimate at scale
     `K * (T * (Real.log x)^2 / x)`;
  3. the existing linear boundary-window weight estimate.
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
  first prove the near-diagonal punctured weighted error bound
  `∃ Cn > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelWeightedNearDiagonalPuncturedBoundaryError x T
      <= Cn * (Real.log x)^2`.
  The separated pointwise kernel estimate is now the scale-correct version of
  the original target:
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈ separatedPuncturedBoundary(x,T),
    |1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T|
      <= K * (T * (Real.log x)^2 / x)`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 10 - Near-Diagonal Punctured Error Reduction

- Classification: `STRICTER_NEAR_DIAGONAL_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  near-diagonal punctured weighted boundary error below
  `small_T_punctured_boundary_window_bound_from_nearDiagonal_and_separated_kernel`
  in `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`.
- Code facts banked:
  added `perronKernelNearDiagonalPuncturedBoundarySet`, naming the exact finite
  set
  `{n <= floor x | |x - n| <= x / T, (n : ℝ) != x, |x - n| <= 1}`.
  Added `perronKernelNearDiagonalPuncturedVonMangoldtWeight`, the pure
  von Mangoldt weight of this unit punctured boundary set.
  Added
  `perronKernelWeightedNearDiagonalPuncturedBoundaryError_le_kernelSup_mul_weight`,
  reducing the near-diagonal weighted error to a uniform kernel bound times the
  pure near-diagonal weight.
  Added
  `perronKernelWeightedNearDiagonalPuncturedBoundaryError_le_kernelSup_mul_log`,
  showing that if the named near-diagonal set has cardinality at most one, then
  the near-diagonal weighted error is `<= K * Real.log x` under a uniform
  kernel bound.  The proof uses only `vonMangoldt_le_log`, membership in
  `range (floor x + 1)`, `Nat.floor_le`, and the unit-band exclusion of
  `n = 0`.
  Added
  `small_T_nearDiagonal_punctured_boundary_bound_from_cardinality_and_kernel`,
  reducing the target
  `perronKernelWeightedNearDiagonalPuncturedBoundaryError x T
    <= Cn * (Real.log x)^2`
  to:
  1. the exact finite-cardinality atom
     `(perronKernelNearDiagonalPuncturedBoundarySet x T).card <= 1`;
  2. a uniform bounded-height kernel estimate on that same finite set.
- Failed route / scale note:
  did not attempt to prove the decaying kernel estimate on the near-diagonal
  punctured set.  That would still be scale-unsafe near real `x` arbitrarily
  close to an integer.  The near-diagonal path only needs a uniform kernel
  bound because the finite-cardinality/log-weight atom absorbs it into
  `O((Real.log x)^2)`.
- Circular/failed routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the exact finite-cardinality atom
  `∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    (perronKernelNearDiagonalPuncturedBoundarySet x T).card <= 1`.
  Then prove the uniform local kernel atom
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈
    perronKernelNearDiagonalPuncturedBoundarySet x T,
      |1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T| <= K`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 11 - Near-Diagonal Cardinality Closure

- Classification: `FINITE_CARDINALITY_ATOM_CLOSED_PENDING_VALIDATION`.
- Theorem/file attacked:
  exact finite-cardinality atom for
  `perronKernelNearDiagonalPuncturedBoundarySet` in
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`.
- Code facts banked:
  added `perronKernelNearDiagonalPuncturedBoundarySet_card_le_one`:
  `∀ x T, x >= 2 ->
    (perronKernelNearDiagonalPuncturedBoundarySet x T).card <= 1`.
  The proof uses only finite-set membership, `Nat.floor_le`, the unit-band
  constraint `|x - n| <= 1`, and the puncturing condition `(n : ℝ) != x`.
  If two natural numbers in the set are distinct, they must be consecutive;
  the interval constraints then force the larger one to equal `x`, contradicting
  the puncture.
  Added `small_T_nearDiagonal_punctured_boundary_bound_from_kernel`, reducing
  the near-diagonal weighted error to the single remaining source atom: a
  uniform bounded-height kernel estimate on
  `perronKernelNearDiagonalPuncturedBoundarySet`.
- Failed route / scale note:
  did not retry the decaying-kernel route on the near-diagonal punctured set.
  That route remains scale-unsafe when real `x` approaches an integer.  The
  cardinality closure confirms the correct near-diagonal strategy is uniform
  kernel control plus one logarithmic von Mangoldt weight.
- Circular/failed routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the uniform local kernel atom
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈
    perronKernelNearDiagonalPuncturedBoundarySet x T,
      |1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T| <= K`.
  A scale-safe route should use only bounded-height Perron per-term estimates
  and the facts `1 <= n`, `n <= x`, and `x <= n + 1` from near-diagonal
  membership; it should not try to prove decay in `x`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 12 - Near-Diagonal Kernel Closure

- Classification: `PROVED_PENDING_VALIDATION`.
- Exact theorem attacked:
  uniform local Perron-kernel bound feeding
  `small_T_nearDiagonal_punctured_boundary_bound_from_kernel` in
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`.
- Banked inputs:
  `perron_per_term_abs_bound_general`, `per_term_rpow_bound`,
  `c_param_pos`, `c_param_gt_one`, `Real.pi_gt_three`, and the validated
  finite-cardinality theorem
  `perronKernelNearDiagonalPuncturedBoundarySet_card_le_one`.
- Code facts banked:
  added `perronKernelNearDiagonalPuncturedBoundarySet_mem_bounds`, extracting
  from near-diagonal membership the scale-safe facts
  `1 <= n`, `(n : ℝ) <= x`, and `x <= (n : ℝ) + 1`.
  Proved `small_T_nearDiagonal_punctured_kernel_uniform_bound`:
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈
    perronKernelNearDiagonalPuncturedBoundarySet x T,
      |1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T| <= K`.
  The proof uses only the absolute bounded-height per-term estimate, `T <= 16`,
  and the local consequence `x / n <= 2`; it does not assert any decay in `x`.
  Added `small_T_nearDiagonal_punctured_boundary_bound`, closing
  `∃ Cn > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelWeightedNearDiagonalPuncturedBoundaryError x T
      <= Cn * (Real.log x)^2`.
- Failed routes:
  did not use the decaying near-integer kernel route.  It remains forbidden
  because real `x` can approach an integer while the requested decaying right
  side tends to zero.
- Circular/failed routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  return to the separated punctured boundary-window pointwise estimate:
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈
    (((range (floor x + 1)).filter boundary).filter (fun n => (n : ℝ) != x)).filter
      (fun n => ¬ |x - (n : ℝ)| <= 1),
    |1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T|
      <= K * (T * (Real.log x)^2 / x)`.
  This is the first remaining place where decay is scale-safe after removing
  exact hits and the unit near-diagonal band.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 13 - Separated Boundary Weighted Assembly

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  separated punctured boundary route below
  `small_T_punctured_boundary_window_bound_from_nearDiagonal_and_separated_kernel`
  in `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`.
- Banked inputs:
  validated exact-hit bound `small_T_exactHit_boundary_error_bound`, validated
  near-diagonal bound `small_T_nearDiagonal_punctured_boundary_bound`, and the
  exact finite-sum splits
  `perronKernelWeightedBoundaryWindowError_eq_exactHit_add_punctured` and
  `perronKernelWeightedPuncturedBoundaryWindowError_eq_nearDiagonal_add_separated`.
- Failed route:
  the separated pointwise decay estimate at scale
  `K * (T * (Real.log x)^2 / x)` is demoted for the current bounded-height
  window.  Even after removing exact hits and the unit near-diagonal band,
  fixed bounded `T` leaves macroscopic boundary points where the truncated
  Perron kernel need not have pointwise error tending to zero with `x`.  This
  route should not be retried without a stronger distance-from-transition
  hypothesis that really forces decay.
- Code facts banked:
  added
  `small_T_punctured_boundary_window_bound_from_nearDiagonal_and_separated_weighted`,
  reducing the punctured boundary-window estimate to near-diagonal weighted
  control plus a direct separated weighted-error estimate.
  Added
  `small_T_punctured_boundary_window_bound_from_separated_weighted`, using the
  closed near-diagonal atom so the punctured window now depends only on
  `perronKernelWeightedSeparatedPuncturedBoundaryError`.
  Added `small_T_boundary_window_bound_from_separated_weighted`, using the
  closed exact-hit and near-diagonal atoms so the full boundary window depends
  only on the direct separated weighted-error estimate.
  Added
  `small_T_weighted_kernel_cutoff_bound_from_separated_boundary_and_offBoundary`,
  reducing the finite weighted cutoff atom to:
  1. the separated punctured boundary weighted estimate;
  2. the off-boundary weighted estimate.
- Circular/failed routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the direct separated weighted-error atom
  `∃ Cs > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelWeightedSeparatedPuncturedBoundaryError x T
      <= Cs * (Real.log x)^2`.
  If this remains too broad, split the separated boundary window by dyadic
  distance from `x`, proving an exact weighted summation lemma rather than a
  pointwise decay supremum.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 14 - Separated Davenport Envelope Reduction

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the direct separated weighted-error atom
  `∃ Cs > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelWeightedSeparatedPuncturedBoundaryError x T
      <= Cs * (Real.log x)^2`.
- Scale check:
  a uniform separated kernel supremum paired with a pure window weight is still
  scale-unsafe on the macroscopic `|x - n| <= x / T` window.  The replacement
  keeps the Davenport `1 / log (x / n)` distance singularity inside the weighted
  finite sum.  This is the scale where the expected harmonic summation can
  plausibly produce `O((log x)^2)`.
- Banked inputs:
  validated exact-hit and near-diagonal closures from earlier rounds, the
  exact finite-sum split
  `perronKernelWeightedPuncturedBoundaryWindowError_eq_nearDiagonal_add_separated`,
  and the existing per-term Davenport-style Perron bounds
  `perron_per_term_large_bound` / `perron_per_term_small_bound`.
- Code facts banked:
  added `perronKernelSeparatedPuncturedBoundarySet` to name the separated
  finite set directly.
  Added `perronKernelSeparatedDavenportEnvelopeTerm` and
  `perronKernelSeparatedDavenportEnvelope`, preserving the local
  `1 / log (x / n)` kernel singularity in the finite weighted sum.
  Added
  `perronKernelWeightedSeparatedPuncturedBoundaryError_le_davenportEnvelope`,
  an exact finite-sum domination by the Davenport envelope under a pointwise
  local envelope hypothesis.
  Added `small_T_separated_weighted_bound_from_davenport_envelope`, reducing
  the separated weighted atom to:
  1. the pointwise Davenport-envelope kernel normalization on
     `perronKernelSeparatedPuncturedBoundarySet`;
  2. the weighted Davenport-envelope summation bound
     `perronKernelSeparatedDavenportEnvelope x T <= Cd * (Real.log x)^2`.
  Added
  `small_T_weighted_kernel_cutoff_bound_from_davenport_separated_and_offBoundary`,
  wiring this separated route back into the finite cutoff surface together with
  the existing off-boundary weighted atom.
- Failed/demoted routes:
  did not retry the demoted pointwise
  `K * (T * (Real.log x)^2 / x)` route.  Also did not assert a pure
  `O((log x)^2)` von Mangoldt weight for the macroscopic separated window.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the pointwise Davenport-envelope normalization:
  `∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈
    perronKernelSeparatedPuncturedBoundarySet x T,
      |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|
        <= perronKernelSeparatedDavenportEnvelopeTerm x T n`.
  This should first extract membership facts
  `1 <= n`, `(n : ℝ) < x`, and `1 < x / (n : ℝ)` from the separated set, then
  apply `perron_per_term_large_bound`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 15 - Separated Davenport Kernel Normalization

- Classification: `PROVED_PENDING_VALIDATION`.
- Exact theorem attacked:
  the pointwise Davenport-envelope normalization feeding
  `small_T_separated_weighted_bound_from_davenport_envelope`:
  `∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈
    perronKernelSeparatedPuncturedBoundarySet x T,
      |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|
        <= perronKernelSeparatedDavenportEnvelopeTerm x T n`.
- Scale check:
  no two-sided split is needed in the current finite Perron cutoff because
  `perronKernelSeparatedPuncturedBoundarySet` is still a subset of
  `range (Nat.floor x + 1)`, hence every member has `(n : ℝ) <= x`.  The exact
  hit filter plus range bound gives `(n : ℝ) < x`, so the large-side
  Davenport bound applies with `1 < x / (n : ℝ)`.
- Code facts banked:
  added `perronKernelSeparatedPuncturedBoundarySet_mem_large_side`, extracting
  `1 <= n`, `(n : ℝ) < x`, and `1 < x / (n : ℝ)` from separated-set
  membership under `x >= 2`.
  Added `small_T_separated_davenport_kernel_bound`, proving the pointwise
  Davenport-envelope normalization directly from
  `perron_per_term_large_bound`.
  Added `small_T_separated_weighted_bound_from_davenport_envelope_bound`, so
  the separated weighted atom now depends only on the weighted Davenport
  envelope summation bound.
  Added
  `small_T_weighted_kernel_cutoff_bound_from_davenport_envelope_and_offBoundary`,
  so the finite weighted cutoff route now depends only on:
  1. `perronKernelSeparatedDavenportEnvelope x T <= Cd * (Real.log x)^2`;
  2. the off-boundary weighted atom.
- Failed/demoted routes:
  did not retry pointwise decay at
  `K * (T * (Real.log x)^2 / x)` and did not replace the separated window by a
  pure macroscopic `O((log x)^2)` von Mangoldt weight.  The Davenport
  `1 / log (x / n)` singularity remains inside the finite weighted sum.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the weighted Davenport-envelope summation bound
  `∃ Cd > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedDavenportEnvelope x T
      <= Cd * (Real.log x)^2`.
  If this is too broad, split the finite set by dyadic distance from `x` while
  preserving the exact `1 / log (x / n)` weight.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 16 - Davenport Envelope Scale Split

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the weighted Davenport-envelope summation target
  `∃ Cd > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedDavenportEnvelope x T
      <= Cd * (Real.log x)^2`.
- Scale check:
  the pure `O((log x)^2)` target is not scale-correct for the current
  macroscopic separated window.  The smooth Davenport component alone has
  one bounded-height contribution per boundary-window integer, so its natural
  scale retains the linear window factor `x / T`.  The singular component
  keeps the necessary `1 / log (x / n)` distance factor and should be handled
  as a weighted harmonic-distance sum.
- Code facts banked:
  added `perronKernelSeparatedDavenportSingularEnvelope` and
  `perronKernelSeparatedDavenportSmoothEnvelope`.
  Proved the exact split
  `perronKernelSeparatedDavenportEnvelope_eq_singular_add_smooth`.
  Added
  `small_T_separated_davenport_envelope_linear_bound_from_components`, reducing
  the scale-correct linear-window envelope bound to singular and smooth
  component bounds at scale `(x / T) * (Real.log x)^2`.
  Added
  `small_T_separated_weighted_bound_from_linear_davenport_envelope_bound`,
  recording the scale-correct separated weighted-error consequence without
  claiming the false pure `O((log x)^2)` envelope sum.
- Failed/demoted routes:
  demoted the pure `O((log x)^2)` weighted Davenport-envelope target as
  scale-incorrect for bounded `T`.  Did not replace the separated window by a
  pure macroscopic von Mangoldt weight, and did not retry pointwise decay at
  `K * (T * (Real.log x)^2 / x)`.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the singular weighted harmonic-distance component at the scale
  `∃ Cs > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedDavenportSingularEnvelope x T
      <= Cs * (x / T) * (Real.log x)^2`.
  If needed, split `perronKernelSeparatedPuncturedBoundarySet` by integer or
  dyadic distance from `x`, using comparability of `Real.log (x / n)` with
  `(x - n) / x`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 17 - Singular Envelope Log-Distance Reduction

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the singular weighted harmonic-distance component
  `∃ Cs > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedDavenportSingularEnvelope x T
      <= Cs * (x / T) * (Real.log x)^2`.
- Scale check:
  kept the `(x / T)` scale from Round 16.  The singular term is now compared
  to the explicit harmonic-distance weight `x / (T * (x - n))`; no pure
  `O((log x)^2)` window-weight route is used.
- Code facts banked:
  added `perronKernelSeparatedDavenportSingularTerm`, so the singular summand
  can be targeted pointwise.
  Added `perronKernelSeparatedLogDistanceTerm` and
  `perronKernelSeparatedLogDistanceEnvelope`, naming the weighted harmonic
  distance sum over `perronKernelSeparatedPuncturedBoundarySet`.
  Added
  `perronKernelSeparatedDavenportSingularEnvelope_le_logDistanceEnvelope`,
  reducing the singular envelope to a pointwise comparison with
  `K * perronKernelSeparatedLogDistanceTerm`.
  Added
  `small_T_separated_singular_envelope_bound_from_logDistance`, reducing the
  singular component to:
  1. pointwise log-distance comparison of the singular Davenport summand;
  2. the weighted harmonic-distance summation bound for
     `perronKernelSeparatedLogDistanceEnvelope`.
- Failed/demoted routes:
  did not retry the refuted pure `O((log x)^2)` Davenport-envelope target and
  did not collapse the separated window to a macroscopic von Mangoldt weight.
  The `1 / log (x / n)` singularity is preserved through the explicit
  `x / (x - n)` distance envelope.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the pointwise comparison
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈
    perronKernelSeparatedPuncturedBoundarySet x T,
      perronKernelSeparatedDavenportSingularTerm x T n
        <= K * perronKernelSeparatedLogDistanceTerm x T n`.
  This should use the existing large-side membership facts and the elementary
  comparison `Real.log (x / n) >= (x - n) / x`, plus bounded control of
  `(x/n)^(1 + 1/log x) + 1` on the boundary window.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 18 - Singular Pointwise Numerator Closure

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the pointwise comparison
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈
    perronKernelSeparatedPuncturedBoundarySet x T,
      perronKernelSeparatedDavenportSingularTerm x T n
        <= K * perronKernelSeparatedLogDistanceTerm x T n`.
- Code facts banked:
  added `perronKernelSeparatedDavenportSingularNumerator`, isolating the
  numerator `(x/n)^(1 + 1/log x) + 1`.
  Added
  `perronKernelSeparatedDavenportSingularTerm_le_logDistanceTerm_of_num_and_recip`,
  reducing each singular summand to two elementary pointwise facts:
  numerator boundedness and reciprocal-log distance comparison.
  Added `small_T_separated_singular_pointwise_bound_from_num_and_recip`,
  lifting those two local facts to the existential pointwise comparison needed
  by `small_T_separated_singular_envelope_bound_from_logDistance`.
  Proved `small_T_separated_singular_numerator_bound` with constant
  `2 * Real.exp 1 + 1`; the proof uses separated-set large-side membership,
  the boundary-window inequality, `T >= 2` to get `x / n <= 2`, and
  `per_term_rpow_bound`.
- Remaining pointwise atom:
  prove the reciprocal-log distance comparison
  `∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈
    perronKernelSeparatedPuncturedBoundarySet x T,
      (Real.log (x / (n : ℝ)))⁻¹ <= x / (x - (n : ℝ))`.
  This is the formal version of
  `Real.log (x / n) >= (x - n) / x`.
- Failed/demoted routes:
  no use of the pure `O((log x)^2)` bounded-`T` envelope route, no macroscopic
  pure window-weight replacement, and no pointwise
  `K * T * (Real.log x)^2 / x` decay route.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the reciprocal-log comparison above, likely from
  `Real.one_sub_inv_le_log_of_pos` applied to `x / (n : ℝ)`, after rewriting
  `1 - (x / n)⁻¹` as `(x - n) / x` using separated-set large-side membership.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 19 - Singular Reciprocal-Log Closure

- Classification: `PROOF_REDUCTION_CLOSURE`.
- Exact theorem attacked:
  the reciprocal-log distance comparison feeding
  `perronKernelSeparatedDavenportSingularTerm_le_logDistanceTerm_of_num_and_recip`:
  `∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈
    perronKernelSeparatedPuncturedBoundarySet x T,
      (Real.log (x / (n : ℝ)))⁻¹ <= x / (x - (n : ℝ))`.
- Code facts banked:
  proved `small_T_separated_reciprocal_log_distance_bound`.  The proof uses
  `perronKernelSeparatedPuncturedBoundarySet_mem_large_side` to obtain
  `1 <= n`, `(n : ℝ) < x`, and `1 < x / n`, then applies
  `Real.one_sub_inv_le_log_of_pos` to `x / (n : ℝ)` and rewrites
  `1 - (x / n)⁻¹` as `(x - n) / x`.  Positivity of both sides permits
  inversion by `inv_le_inv₀`.
  Added `small_T_separated_singular_pointwise_bound`, combining the new
  reciprocal-log comparison with the previously validated numerator bound
  `small_T_separated_singular_numerator_bound`.
- Scale check:
  preserved the `(x / T)` harmonic-distance route.  The singularity remains in
  `perronKernelSeparatedLogDistanceTerm`; this round does not replace the
  separated window by a pure bounded-height `O((Real.log x)^2)` weight.
- Failed/demoted routes:
  did not use the refuted pointwise `K * T * (Real.log x)^2 / x` decay route
  near integer `x`, and did not revive the false pure macroscopic window-weight
  estimate.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the weighted harmonic-distance summation bound
  `∃ Cℓ > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedLogDistanceEnvelope x T
      <= Cℓ * (x / T) * (Real.log x)^2`.
  This is now the remaining input to
  `small_T_separated_singular_envelope_bound_from_logDistance`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 20 - Weighted Harmonic-Distance Unweighting

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the weighted harmonic-distance summation bound
  `∃ Cℓ > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedLogDistanceEnvelope x T
      <= Cℓ * (x / T) * (Real.log x)^2`.
- Code facts banked:
  added `perronKernelSeparatedUnweightedLogDistanceEnvelope`, the finite
  unweighted sum of `perronKernelSeparatedLogDistanceTerm` over
  `perronKernelSeparatedPuncturedBoundarySet`.
  Proved `perronKernelSeparatedLogDistanceEnvelope_le_log_mul_unweighted`,
  bounding the weighted envelope by `Real.log x` times the unweighted envelope.
  The proof uses large-side separated membership, `vonMangoldt_le_log`, and
  `Real.log_le_log` from `(n : ℝ) <= x`.
  Added `small_T_separated_logDistance_bound_from_unweighted`, reducing the
  weighted harmonic-distance bound to the strictly smaller unweighted finite
  harmonic-distance atom
  `∃ Ch > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedUnweightedLogDistanceEnvelope x T
      <= Ch * (x / T) * Real.log x`.
  Added
  `small_T_separated_singular_envelope_bound_from_unweighted_logDistance`,
  wiring the now-closed pointwise singular route directly to this unweighted
  harmonic-distance atom.
- Scale check:
  preserved the `(x / T)` route.  The extra `Real.log x` comes only from the
  honest pointwise `Λ(n) <= log x`; the remaining summation is the expected
  unweighted harmonic series over distances from the cutoff.
- Failed/demoted routes:
  did not use a pure bounded-height `O((Real.log x)^2)` Davenport-envelope
  route and did not replace the macroscopic separated window by a false pure
  von Mangoldt weight estimate.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the unweighted finite harmonic-distance summation bound
  `∃ Ch > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedUnweightedLogDistanceEnvelope x T
      <= Ch * (x / T) * Real.log x`.
  This should use the separated facts `1 < x - n` and `x - n <= x / T`,
  then compare the finite integer-distance sum to a harmonic sum.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 21 - Unweighted Harmonic Scale Factorization

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the remaining unweighted finite harmonic-distance bound
  `∃ Ch > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedUnweightedLogDistanceEnvelope x T
      <= Ch * (x / T) * Real.log x`.
- Code facts banked:
  added `perronKernelSeparatedReciprocalDistanceEnvelope`, the pure reciprocal
  sum `Σ (x - n)⁻¹` over `perronKernelSeparatedPuncturedBoundarySet`.
  Proved `perronKernelSeparatedPuncturedBoundarySet_mem_distance_bounds`,
  extracting the separated distance facts `1 < x - n` and `x - n <= x / T`
  from existing large-side membership and the boundary-window filters.
  Proved
  `perronKernelSeparatedUnweightedLogDistanceEnvelope_eq_scale_mul_reciprocal`,
  factoring the global `x / T` scale out of the unweighted log-distance
  envelope.
  Added `small_T_separated_unweighted_logDistance_bound_from_reciprocal`,
  reducing the target to the strictly smaller pure finite harmonic atom
  `∃ Ch > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedReciprocalDistanceEnvelope x T <= Ch * Real.log x`.
  Added the downstream wiring lemmas
  `small_T_separated_logDistance_bound_from_reciprocal` and
  `small_T_separated_singular_envelope_bound_from_reciprocal_logDistance`.
- Scale check:
  preserved the `(x / T)` factor exactly.  No bounded-height pure Davenport
  envelope was asserted; the only remaining growth is the expected harmonic
  `Real.log x`.
- Failed/demoted routes:
  did not try to bound the macroscopic separated window by a pure
  `O((Real.log x)^2)` von Mangoldt weight, and did not use the false
  near-integer pointwise decay route.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the pure reciprocal-distance harmonic sum
  `∃ Ch > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedReciprocalDistanceEnvelope x T <= Ch * Real.log x`.
  The proof should reindex by integer distance below the cutoff, using
  `1 < x - n` and `x - n <= x / T`, then compare to a standard finite
  harmonic sum.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 22 - Reciprocal Distance to Harmonic Floor

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the live pure reciprocal-distance atom
  `∃ Ch > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedReciprocalDistanceEnvelope x T <= Ch * Real.log x`.
- Code facts banked:
  added private `harmonic_floor_le_const_mul_log`, proving
  `(harmonic (Nat.floor x) : ℝ) <= (1 + 1 / Real.log 2) * Real.log x`
  for `x >= 2` using Mathlib's `harmonic_floor_le_one_add_log`.
  Added
  `small_T_separated_reciprocalDistance_bound_from_harmonic_floor`, reducing
  the live reciprocal-distance atom to the exact finite harmonic majorant
  `∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedReciprocalDistanceEnvelope x T
      <= (harmonic (Nat.floor x) : ℝ)`.
- Scale check:
  the `(x / T)` scale is already factored out by Round 21.  This round keeps
  only the logarithmic harmonic growth and does not introduce a bounded-height
  pure Davenport envelope.
- Failed/demoted routes:
  did not assert a broad dummy constant.  A direct proof needs the finite
  reindexing/injection from separated indices `n` to integer distances below
  `Nat.floor x`; that combinatorial step was isolated instead of guessed.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the finite reindexing/cardinality majorant
  `∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedReciprocalDistanceEnvelope x T
      <= (harmonic (Nat.floor x) : ℝ)`.
  It should map each separated `n <= floor x` to `Nat.floor x - n`, use
  `1 < x - n` to exclude zero distance, and compare the resulting reciprocal
  terms to the standard harmonic sum.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 23 - Finite Harmonic Floor Reindexing

- Classification: `CANDIDATE_CLOSE`.
- Exact theorem attacked:
  the finite reindexing atom
  `∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelSeparatedReciprocalDistanceEnvelope x T
      <= (harmonic (Nat.floor x) : ℝ)`.
- Code facts banked:
  added `perronKernelSeparatedFloorDistanceEnvelope`, the integer
  floor-distance sum `Σ (floor x - n)⁻¹` over the separated punctured boundary
  set.  Added private membership helpers extracting `n <= floor x` and
  `0 < floor x - n` from the existing separated facts, using `1 < x - n` and
  `x < floor x + 1`.
  Proved
  `perronKernelSeparatedReciprocalDistanceEnvelope_le_floorDistanceEnvelope`
  by termwise reciprocal comparison
  `(x - n)⁻¹ <= (floor x - n)⁻¹`.
  Proved
  `perronKernelSeparatedFloorDistanceEnvelope_le_harmonic_floor` by injecting
  `n` into the positive integer distance `floor x - n`, proving the image is a
  subset of `Finset.Icc 1 (Nat.floor x)`, and comparing to
  `harmonic_eq_sum_Icc`.
  Proved the requested closed majorant
  `perronKernelSeparatedReciprocalDistanceEnvelope_le_harmonic_floor` and
  added the closed consequence `small_T_separated_reciprocalDistance_bound`.
- Scale check:
  preserved the existing `(x / T)` factorization and only closed the pure
  harmonic `O(log x)` reciprocal-distance atom.  Did not introduce a false
  pure bounded-height Davenport-envelope bound.
- Failed/demoted routes:
  did not use the demoted pointwise `K * T * log^2 x / x` route near integer
  `x`, and did not assert a macroscopic pure `O((log x)^2)` von Mangoldt
  window estimate.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  after validation, use `small_T_separated_reciprocalDistance_bound` to close
  the existing separated log-distance / singular Davenport-envelope wiring, or
  continue to the remaining off-boundary weighted cutoff estimate if that
  wiring is already sufficient.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 24 - Linear Davenport Separated Route

- Classification: `CANDIDATE_CLOSE`.
- Exact theorem attacked:
  the next separated Davenport/public-path surface below the validated
  reciprocal-distance bound, keeping the honest linear-window scale
  `x / T`.
- Code facts banked:
  updated the `perronKernelSeparatedDavenportEnvelope` doc comment to record
  that the pure `O((log x)^2)` envelope is false on the macroscopic separated
  window.
  Added `small_T_separated_davenport_smooth_pointwise_bound`, bounding the
  smooth Davenport summand uniformly from the existing numerator bound and
  `T >= 2`, `1 + 1 / log x >= 1`.
  Added `small_T_separated_davenport_smooth_envelope_bound`, bounding the
  smooth envelope by `Cm * (x / T) * (Real.log x)^2` using the already proved
  linear boundary-window von Mangoldt weight and log-square absorption.
  Added closed linear-scale consequences
  `small_T_separated_singular_envelope_bound`,
  `small_T_separated_davenport_envelope_linear_bound`, and
  `small_T_separated_weighted_linear_bound`.
- Scale check:
  preserved the scale-correct `x / T` factor.  This deliberately does not
  claim the false pure bounded-height separated Davenport envelope needed by
  older conditional cutoff lemmas.
- Failed/demoted routes:
  did not use the demoted near-integer pointwise
  `K * T * (log x)^2 / x` route, and did not assert a macroscopic pure
  `O((log x)^2)` von Mangoldt or Davenport-envelope estimate.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  continue outside the separated Davenport route: either prove a compatible
  off-boundary weighted cutoff estimate, or decide whether the public
  small-`T` weighted cutoff theorem must be restated through the existing
  residue/truncation route because the separated boundary contribution is only
  available at linear-window scale.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 25 - Linear Cutoff Assembly

- Classification: `CANDIDATE_REDUCTION`.
- Exact theorem attacked:
  the weighted cutoff/public-path surface after the validated separated
  Davenport route, under the scale-correct target
  `C * (x / T) * (Real.log x)^2`.
- Code facts banked:
  added the private absorption helper
  `small_T_logSq_le_eight_linear_logSq`, using `x >= 2` and `T <= 16` to
  embed pure `log^2` exact-hit and near-diagonal contributions into the
  linear-window scale.
  Added
  `small_T_boundary_window_linear_bound_from_separated_linear` and closed
  `small_T_boundary_window_linear_bound`, assembling the exact-hit,
  near-diagonal, and separated boundary-window errors without using the old
  pure Davenport target.
  Added
  `small_T_weighted_kernel_cutoff_linear_bound_from_boundary_and_offBoundary`
  and `small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary`, reducing
  the scale-correct weighted cutoff to the remaining off-boundary estimate at
  the same linear-window scale.
  Added
  `small_T_perronKernelFiniteSum_cutoff_linear_bound_from_weighted_error`,
  carrying a linear weighted cutoff bound to the finite Perron-kernel cutoff
  error.
- Scale check:
  the separated Davenport boundary contribution remains at
  `C * (x / T) * (Real.log x)^2`.  This round intentionally does not claim the
  false pure `O((Real.log x)^2)` weighted cutoff needed by the older
  `SmallTPerronBoundHyp` handoff.
- Failed/demoted routes:
  did not force the macroscopic separated boundary contribution into a pure
  bounded-height estimate.  The existing public small-`T` provider route still
  requires either a different cancellation/residue route or a modified
  handoff, because the linear-window cutoff alone is too large for the pure
  small-`T` target.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the compatible off-boundary weighted cutoff estimate
  `∃ Co > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelWeightedOffBoundaryWindowError x T
      <= Co * (x / T) * (Real.log x)^2`,
  or introduce a non-circular truncation/residue handoff that explicitly
  bypasses the false pure weighted cutoff target.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 26 - Off-Boundary Davenport Handoff

- Classification: `CANDIDATE_REDUCTION`.
- Exact theorem attacked:
  the compatible off-boundary atom at the honest linear-window scale
  `C * (x / T) * (Real.log x)^2`.
- Code facts banked:
  added `perronKernelOffBoundaryDavenportEnvelopeTerm` and
  `perronKernelOffBoundaryDavenportEnvelope`, retaining Davenport's
  `1 / log (x / n)` structure off the sharp boundary window.
  Proved
  `perronKernelWeightedOffBoundaryWindowError_le_davenportEnvelope`: for
  `x >= 2`, `2 <= T`, every positive off-boundary finite-sum term satisfies
  `1 < x / n`, so `perron_per_term_large_bound` gives the weighted Davenport
  envelope; the `n = 0` term is zero because `vonMangoldt 0 = 0`.
  Added
  `small_T_offBoundary_weighted_linear_bound_from_davenportEnvelope`, reducing
  the requested off-boundary weighted cutoff to the envelope summation bound,
  and
  `small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary_davenportEnvelope`,
  wiring that bound into the closed linear boundary-window assembly.
- Scale check:
  preserved the scale-correct `x / T` factor.  The new off-boundary envelope
  is a summation target at linear-window scale; it does not assert the false
  pure bounded-height cutoff estimate.
- Failed/demoted routes:
  did not use a constant off-boundary kernel supremum.  That route is too
  coarse for small `n`, where Davenport's bound naturally has `x / (T * n)`
  size and must be summed with the von Mangoldt weight.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the off-boundary Davenport-envelope summation bound
  `∃ Cd > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelOffBoundaryDavenportEnvelope x T
      <= Cd * (x / T) * (Real.log x)^2`.
  The likely route is to split the envelope into the smooth
  `1 / T` part and the singular `1 / (T * log (x / n))` part; on the
  off-boundary set, convert `1 / log (x / n)` to a distance term and sum by
  harmonic-distance or dyadic bands below `x - x / T`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 27 - Off-Boundary Envelope Components

- Classification: `CANDIDATE_REDUCTION`.
- Exact theorem attacked:
  the closed off-boundary Davenport-envelope summation bound
  `∃ Cd > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelOffBoundaryDavenportEnvelope x T
      <= Cd * (x / T) * (Real.log x)^2`.
- Code facts banked:
  split `perronKernelOffBoundaryDavenportEnvelope` into exact component
  definitions:
  `perronKernelOffBoundaryDavenportSingularTerm`,
  `perronKernelOffBoundaryDavenportSmoothTerm`,
  `perronKernelOffBoundaryDavenportSingularEnvelope`, and
  `perronKernelOffBoundaryDavenportSmoothEnvelope`.
  Proved the exact finite-sum identity
  `perronKernelOffBoundaryDavenportEnvelope_eq_singular_add_smooth`.
  Added
  `small_T_offBoundary_davenportEnvelope_linear_bound_from_components`,
  reducing the closed envelope target to separate singular and smooth
  summation bounds at the same scale.
  Added
  `small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary_davenport_components`
  to wire those two component bounds through the already validated
  linear-scale cutoff assembly.
- Scale check:
  preserved the linear-window target
  `C * (x / T) * (Real.log x)^2`; no pure
  `O((Real.log x)^2)` off-boundary or boundary-window bound was introduced.
- Failed/demoted routes:
  did not use a constant kernel supremum.  The smooth component still needs
  the weighted reciprocal sum `Σ Λ(n)/n`, and the singular component still
  needs the reciprocal-log/distance summation away from
  `|x - n| <= x / T`.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  close the smooth component first:
  `∃ Cm > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelOffBoundaryDavenportSmoothEnvelope x T
      <= Cm * (x / T) * (Real.log x)^2`.
  A local route should use `per_term_rpow_bound`, `c >= 1`, and the finite
  weighted reciprocal estimate
  `Σ_{1 <= n <= floor x} Λ(n) / n = O((Real.log x)^2)`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 28 - Smooth Off-Boundary Envelope

- Classification: `CANDIDATE_CLOSE`.
- Exact theorem attacked:
  the smooth off-boundary Davenport component
  `∃ Cm > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelOffBoundaryDavenportSmoothEnvelope x T
      <= Cm * (x / T) * (Real.log x)^2`.
- Code facts banked:
  added `perronKernelVonMangoldtReciprocalWeight`, the finite reciprocal
  von Mangoldt weight over `range (floor x + 1)` with an explicit zero branch.
  Proved
  `perronKernelVonMangoldtReciprocalWeight_le_log_mul_harmonic_floor` from
  `vonMangoldt_le_log`, monotonicity of `log`, and the harmonic majorant.
  Proved the closed reciprocal-weight bound
  `small_T_vonMangoldt_reciprocalWeight_bound`.
  Proved
  `perronKernelOffBoundaryDavenportSmoothEnvelope_le_reciprocalWeight` using
  `per_term_rpow_bound`, `c >= 1`, and positivity of `T`.
  Closed the target as
  `small_T_offBoundary_davenportSmoothEnvelope_bound`.
- Scale check:
  preserved the required `x / T` factor.  The proof sums the natural
  `Λ(n) / n` weight and does not use a constant kernel supremum or a pure
  `O((Real.log x)^2)` off-boundary route.
- Failed/demoted routes:
  no attempt to bound the smooth envelope by full Chebyshev weight
  `ψ(x) = O(x)`, which would lose a factor of `x`.  The reciprocal-weight
  route keeps the scale correct.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  attack the singular component
  `∃ Cs > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelOffBoundaryDavenportSingularEnvelope x T
      <= Cs * (x / T) * (Real.log x)^2`.
  The expected route is a reciprocal-log/distance comparison on the
  off-boundary set, followed by a finite weighted distance summation below
  `x - x / T`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 29 - Singular Off-Boundary Distance Reduction

- Classification: `CANDIDATE_REDUCTION`.
- Exact theorem attacked:
  the remaining singular off-boundary Davenport component
  `∃ Cs > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelOffBoundaryDavenportSingularEnvelope x T
      <= Cs * (x / T) * (Real.log x)^2`.
- Code facts banked:
  added `perronKernelOffBoundaryDistanceWeight`, the finite
  `Σ Λ(n) / (x - n)` weight on the off-boundary set.
  Added
  `small_T_offBoundary_davenportSingularEnvelope_bound_from_pointwise_and_distance`,
  reducing the singular envelope to:
  a pointwise reciprocal-log comparison against
  `(x / T) * (Λ(n)/n + Λ(n)/(x-n))`, plus the distance-weight summation bound.
  Added
  `small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary_singularDistance`,
  wiring this singular-distance reduction together with the validated smooth
  component through the linear-scale cutoff route.
- Scale check:
  preserved the `x / T` factor explicitly.  The existing reciprocal-weight
  theorem supplies the `Λ(n)/n` part; the only new summation atom is the
  distance weight at `O((Real.log x)^2)`.
- Failed/demoted routes:
  did not use a constant singular kernel supremum or a pure
  `O((Real.log x)^2)` off-boundary cutoff.  The reciprocal-log singularity is
  kept inside the pointwise/distance split.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the pointwise reciprocal-log comparison
  `∃ K > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 -> ∀ n ∈ offBoundary,
    perronKernelOffBoundaryDavenportSingularTerm x T n
      <= K * (x / T) * (Λ(n)/n + Λ(n)/(x-n))`,
  then prove the distance-weight summation
  `∃ Cd > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelOffBoundaryDistanceWeight x T <= Cd * (Real.log x)^2`.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 30 - Singular Pointwise Log Split

- Classification: `CANDIDATE_CLOSE`.
- Exact theorem attacked:
  the pointwise reciprocal-log comparison feeding the singular off-boundary
  reduction.
- Code facts banked:
  proved `small_T_offBoundary_davenportSingular_pointwise_bound`.  For
  positive off-boundary terms, the finite range gives `n <= floor x <= x`;
  the off-boundary predicate rules out `n = x`, so `n < x` and
  `1 < x / n`.  The proof uses
  `Real.one_sub_inv_le_log_of_pos` to obtain
  `(log (x / n))⁻¹ <= x / (x - n)`, and `per_term_rpow_bound` plus
  `1 <= exp(1) * x / n` to bound the numerator by
  `2 * exp(1) * x / n`.  Algebra then splits
  `x / (n * (x - n))` as `1 / n + 1 / (x - n)`.
  Added
  `small_T_offBoundary_davenportSingularEnvelope_bound_from_distance`, so the
  singular envelope now depends only on the distance-weight summation.
  Added
  `small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary_distance`,
  wiring the complete linear cutoff route from that single remaining atom.
- Scale check:
  the proof keeps the `x / T` factor explicit and does not replace the
  reciprocal-log singularity by a constant supremum.
- Failed/demoted routes:
  did not attempt a pure `O((Real.log x)^2)` cutoff route and did not use the
  false global tail statement.  The only remaining analytic atom is the finite
  weighted distance sum.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  prove the finite off-boundary distance-weight summation
  `∃ Cd > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelOffBoundaryDistanceWeight x T <= Cd * (Real.log x)^2`.
  The likely proof should reindex by the integer distance below `floor x` or
  use dyadic bands below `x - x / T`, with the existing
  `vonMangoldt_le_log` and harmonic-sum infrastructure.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 31 - Distance Weight Cancellation

- Classification: `CANDIDATE_CLOSE`.
- Exact theorem attacked:
  the remaining distance-weight summation
  `∃ Cd > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    perronKernelOffBoundaryDistanceWeight x T <= Cd * (Real.log x)^2`.
- Code facts banked:
  proved `perronKernelOffBoundaryDistanceWeight_le_scaled_chebyshevPsi`.
  For positive terms in the finite range, `n <= floor x <= x`; the
  off-boundary predicate rules out `n = x` and gives
  `x / T < x - n`, hence `(x - n)⁻¹ <= T / x`.  Summing over the finite
  off-boundary subset gives the exact bound
  `perronKernelOffBoundaryDistanceWeight x T <= (T / x) * chebyshevPsi x`.
  Proved the closed summation theorem
  `small_T_offBoundary_distanceWeight_bound` from Chebyshev's linear bound,
  `T <= 16`, and absorption of the resulting constant into `(Real.log x)^2`
  for `x >= 2`.
  Added closed downstream consequences:
  `small_T_offBoundary_davenportSingularEnvelope_bound`,
  `small_T_offBoundary_davenportEnvelope_linear_bound`, and
  `small_T_weighted_kernel_cutoff_linear_bound`.
- Scale check:
  the distance-weight proof keeps the `T / x` factor until it cancels against
  the Chebyshev `O(x)` bound, giving a legitimate bounded contribution before
  log-square absorption.  It does not use a constant kernel supremum.
- Failed/demoted routes:
  did not use a pure bounded-height cutoff target or asymptotic handwave.  The
  resulting closed weighted cutoff is explicitly the linear-window theorem
  `C * (x / T) * (Real.log x)^2`, not the false pure provider target.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  route the closed linear weighted cutoff through the finite Perron-kernel
  linear handoff already present as
  `small_T_perronKernelFiniteSum_cutoff_linear_bound_from_weighted_error`,
  and decide whether any downstream truncation/residue theorem can honestly
  consume the linear-window scale without reintroducing the false pure
  `SmallTPerronBoundHyp` route.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 32 - Linear Cutoff Handoff

- Classification: `CANDIDATE_REDUCTION`.
- Exact theorem attacked:
  route the closed `small_T_weighted_kernel_cutoff_linear_bound` through the
  finite Perron-kernel handoff and test the downstream small-`T` shape.
- Code facts banked:
  added the closed wrapper
  `small_T_perronKernelFiniteSum_cutoff_linear_bound`, which applies
  `small_T_perronKernelFiniteSum_cutoff_linear_bound_from_weighted_error` to
  the validated weighted cutoff theorem.  Added
  `small_T_perronVerticalIntegral_truncation_linear_bound_from_kernel_sum_bound`
  and the closed
  `small_T_perronVerticalIntegral_truncation_linear_bound`; the exchange
  error `O(1)` is absorbed into the linear-window scale using
  `x / T >= 1 / 8` on `x >= 2`, `2 <= T <= 16`.  Added the honest downstream
  handoff `small_T_direct_linear_bound_from_perronVerticalIntegral_components`
  and its closed-cutoff specialization `small_T_direct_linear_bound_from_residue`.
- Scale check:
  the downstream theorem now has final shape
  `sqrt x * (log T)^2 / sqrt T + (x / T) * (log x)^2`.  This is the strongest
  statement supported by the current validated cutoff route.  It cannot be
  passed to `SmallTPerronBoundHyp`, whose public target allows only
  `sqrt x * (log T)^2 / sqrt T + (log x)^2`; for fixed bounded `T`, the
  extra `(x / T)` factor grows linearly in `x` and is not absorbable by a
  uniform constant.
- Failed/demoted routes:
  did not coerce the linear cutoff into the false pure `(Real.log x)^2`
  truncation target and did not create a provider instance from this theorem.
  The pure provider route remains blocked unless a sharper cutoff/truncation
  theorem removes the macroscopic `x / T` factor or a different residue
  cancellation handoff consumes it.
- Circular/forbidden routes avoided:
  no use of `ContourRemainderBoundHyp.bound`, `general_formula_accessible`,
  `PerronAssumptionsBridge.small_T_contour_bound`, public main imports,
  `shifted_remainder_bound_atomic`, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  either prove a sharper finite Perron-kernel cutoff/truncation bound that
  removes the macroscopic `(x / T)` factor before the vertical-integral
  handoff, or introduce a residue/cancellation theorem that consumes the
  linear-window truncation term without routing through the public
  `SmallTPerronBoundHyp` target.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 33 - Linear Absorption Boundary

- Classification: `CANDIDATE_REDUCTION`.
- Exact theorem attacked:
  the blocker between the validated linear-window cutoff shape
  `sqrt x * (log T)^2 / sqrt T + (x / T) * (log x)^2` and the public
  `SmallTPerronBoundHyp` target
  `sqrt x * (log T)^2 / sqrt T + (log x)^2`.
- Code facts banked:
  added `small_T_direct_bound_from_linear_bound_and_absorption`, an ordinary
  theorem adapter from an honest linear direct bound plus the explicit
  absorption atom
  `(x / T) * (Real.log x)^2 <= A *
    (sqrt x * (Real.log T)^2 / sqrt T + (Real.log x)^2)`.
  Added the non-instance provider adapter
  `small_T_perron_bound_hyp_from_linear_residue_and_absorption`, which combines
  the closed linear cutoff/residue handoff with that explicit absorption atom.
- Scale check:
  no unconditional absorption was asserted.  On the current public domain
  `x >= 2`, `2 <= T <= 16`, the linear-window term has growth
  `(x / T) * (log x)^2`; for bounded `T` this is not uniformly controlled by
  `sqrt x * (log T)^2 / sqrt T + (log x)^2`.  The adapter therefore isolates
  the missing statement instead of feeding the linear theorem into
  `SmallTPerronBoundHyp`.
- Failed/demoted routes:
  did not change the public `SmallTPerronBoundHyp` statement, did not create
  an automatic instance, and did not weaken the main theorem.  The current
  linear cutoff route remains a valid handoff only for a strengthened target
  or for a later proof/cancellation theorem that removes or absorbs the
  `x / T` factor under a genuinely narrower parameter regime.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, contour providers,
  `general_formula_accessible`, public main imports, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  either prove a sharper cutoff/truncation theorem with pure
  `O((Real.log x)^2)` error, prove a cancellation/residue handoff that removes
  the linear-window term before the public provider boundary, or intentionally
  introduce a separate strengthened small-`T` surface for consumers that can
  use the linear-window shape.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 34 - Linear Window Surface

- Classification: `CANDIDATE_SURFACE_SPLIT`.
- Exact theorem attacked:
  the public/provider mismatch between the validated linear-window small-`T`
  route and the legacy `SmallTPerronBoundHyp` target.
- Code facts banked:
  added `SmallTPerronLinearWindowBoundHyp`, a separate strengthened small-`T`
  surface whose bound keeps the honest term
  `(x / T) * (Real.log x)^2`.  Added
  `small_T_linear_window_bound_hyp_from_residue`, which constructs this
  surface from the closed linear Perron cutoff route plus the remaining
  bounded-height residue atom.  Added
  `small_T_direct_linear_bound_from_linear_window_hyp`, a direct consumer
  theorem for code that can use the linear-window shape.  Added
  `small_T_perron_bound_hyp_from_linear_window_hyp_and_absorption`, a
  no-instance bridge to the legacy public class only when the explicit
  absorption atom is supplied.
- Scale check:
  did not assert the false full-domain absorption and did not bridge the new
  surface to `SmallTPerronBoundHyp` automatically.  The linear-window class is
  a proof-facing surface for the scale currently supported by the Perron
  cutoff route.
- Failed/demoted routes:
  did not weaken the existing public class, did not add a dummy witness, and
  did not create a hidden instance.  The legacy public target still requires a
  sharper cutoff/cancellation theorem or an explicit absorption theorem under
  a genuinely stronger parameter regime.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, contour providers,
  `general_formula_accessible`, public main imports, or any theorem consuming
  `SmallTPerronBoundHyp`.  Did not use or modify `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Requested coordinator validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Local validation:
  passed under `/tmp/littlewood-lean-singleflight.lock` with
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- Smallest next theorem:
  either prove the bounded-height residue atom for
  `perronVerticalIntegral`, which would close the new linear-window surface,
  or prove a sharper finite cutoff/cancellation theorem that removes the
  `(x / T)` factor and can feed the legacy public `SmallTPerronBoundHyp`
  target.
- Coordinator action required: run the requested focused validation; no full
  build requested.

### 2026-04-29 Round 35 - Residue To Contour Remainder Split

- Classification: `CANDIDATE_REDUCTION_VALIDATED`.
- Exact theorem attacked:
  the bounded-height residue atom feeding `SmallTPerronLinearWindowBoundHyp`.
- Code facts banked:
  added `small_T_perronVerticalIntegral_residue_bound_from_contour_remainder`,
  reducing the direct residue estimate to two strictly smaller atoms: an exact
  identity
  `perronVerticalIntegral x T = x - zeroSumRe x T + contourRemainderRe x T`,
  and a bounded-height estimate for only `contourRemainderRe`.
  Added `small_T_linear_window_bound_hyp_from_contour_remainder`, wiring this
  split into `SmallTPerronLinearWindowBoundHyp`.  Added
  `small_T_perron_bound_hyp_from_contour_remainder_and_absorption`, wiring the
  same split through the explicit absorption bridge to the legacy public
  provider target when, and only when, the absorption atom is supplied.
- Scale check:
  no false full-domain absorption was asserted, no legacy instance was added,
  and the linear-window term remains visible until the explicit absorption
  hypothesis is provided.
- Failed/demoted routes:
  did not route through shifted remainder atoms, contour provider shortcuts,
  or `general_formula_accessible`.  The new split is algebraic/conditional and
  leaves the analytic residue work in the exact contour-identity plus
  contour-remainder bound atoms.
- Circular/forbidden routes avoided:
  no use of `SmallTPerronBoundHyp`, shifted remainder atoms, public main
  imports, or `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  first lock-gated attempt exited `LEAN_BUSY` because another focused Lake
  process was running.  Retried under `/tmp/littlewood-lean-singleflight.lock`;
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra` passed.
- Smallest next theorem:
  prove the concrete bounded-height contour-remainder identity for
  `perronVerticalIntegral`, or the bounded-height estimate for that concrete
  `contourRemainderRe`, whichever is locally reachable first.

### 2026-04-29 Round 36 - Concrete Vertical Contour Remainder

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the concrete contour-remainder identity for `perronVerticalIntegral` feeding
  `SmallTPerronLinearWindowBoundHyp`.
- Code facts banked:
  added the concrete local definition `perronVerticalContourRemainderRe` as
  `perronVerticalIntegral x T - x + zeroSumRe x T`.  Proved
  `perronVerticalIntegral_residue_identity`, so the actual vertical integral
  now has the residue decomposition
  `perronVerticalIntegral x T = x - zeroSumRe x T +
    perronVerticalContourRemainderRe x T` by algebra.  Added
  `small_T_perronVerticalIntegral_residue_bound_from_concrete_contour_remainder`,
  `small_T_linear_window_bound_hyp_from_concrete_contour_remainder`, and
  `small_T_perron_bound_hyp_from_concrete_contour_remainder_and_absorption`,
  wiring the concrete identity into the linear-window surface and the existing
  explicit absorption bridge.
- Scale check:
  no bounded-height estimate was asserted for free.  The remaining analytic
  atom is exactly the small-`T` bound for the concrete defect
  `perronVerticalContourRemainderRe`, with the legacy absorption obligation
  still separate and explicit.
- Failed/demoted routes:
  did not use placeholder shifted-remainder witnesses, did not route through
  contour provider classes, and did not install a `SmallTPerronBoundHyp`
  instance.  The theorem only names the concrete residue defect and closes the
  algebraic identity side.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`, or
  `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  Passed under `/tmp/littlewood-lean-singleflight.lock`.
- Smallest next theorem:
  prove
  `∃ Cc > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    |perronVerticalContourRemainderRe x T| <=
      Cc * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T)`.

### 2026-04-29 Round 37 - Concrete Remainder Normalized Supremum

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the bounded-height concrete defect estimate for
  `perronVerticalContourRemainderRe`.
- Code facts banked:
  added `small_T_residue_error_shape_pos`, proving the denominator
  `Real.sqrt x * (Real.log T)^2 / Real.sqrt T` is strictly positive on
  `x >= 2`, `2 <= T`, `T <= 16`, using the closed small-`T` denominator lower
  bound from `HadamardProductZeta`.  Added
  `small_T_concrete_contour_remainder_bound_from_normalized_sup`, which turns
  a normalized supremum bound for the concrete defect into the exact
  bounded-height estimate.  Added linear-window and legacy-with-absorption
  adapters from this normalized supremum atom.
- Scale check:
  a literal compact box in `(x,T)` is not available for the full target because
  `x >= 2` is unbounded.  The new atom therefore keeps the normalization by
  `sqrt x * (log T)^2 / sqrt T` and uses only the closed bounded `T` interval
  for denominator positivity.
- Failed/demoted routes:
  did not assert an unscaled uniform bound on the concrete defect, did not
  claim compactness in the unbounded `x` direction, and did not introduce a
  legacy `SmallTPerronBoundHyp` instance.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`, or
  `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  Passed under `/tmp/littlewood-lean-singleflight.lock`.
- Smallest next theorem:
  prove the normalized concrete-defect supremum
  `∃ Cc > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
    |perronVerticalContourRemainderRe x T| /
      (Real.sqrt x * (Real.log T)^2 / Real.sqrt T) <= Cc`.

### 2026-04-29 Round 38 - Normalized Supremum Slab/Tail Split

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the global normalized concrete-defect supremum for
  `perronVerticalContourRemainderRe`.
- Code facts banked:
  added
  `small_T_concrete_contour_remainder_normalized_sup_from_slab_and_tail`,
  splitting the unbounded `x >= 2` domain at an explicit cutoff `X0`.
  The theorem combines a bounded-slab estimate on `2 <= x <= X0` with an
  asymptotic-tail estimate on `X0 <= x` by taking the maximum of the two
  constants.  Added
  `small_T_linear_window_bound_hyp_from_concrete_contour_remainder_slab_and_tail`,
  wiring this split into `SmallTPerronLinearWindowBoundHyp`.
- Scale check:
  no compactness in `x` was claimed.  The bounded part is explicitly the slab
  `2 <= x <= X0`; the unbounded tail remains a separate normalized analytic
  theorem.  The legacy absorption obligation remains separate.
- Failed/demoted routes:
  did not assert a global compact supremum, did not use an unscaled bound, and
  did not introduce a legacy `SmallTPerronBoundHyp` instance.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`, or
  `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  First lock-gated attempt exited `LEAN_BUSY` while
  `Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp` was validating.
  Retried under `/tmp/littlewood-lean-singleflight.lock`; the focused Perron
  build passed.
- Smallest next theorem:
  choose an explicit cutoff `X0 >= 2` and prove either the bounded slab
  normalized estimate on `2 <= x <= X0`, or the asymptotic normalized tail
  estimate on `X0 <= x`.

### 2026-04-29 Round 39 - Explicit Cutoff 16 Slab/Tail

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  choose an explicit cutoff for the normalized concrete-defect slab/tail split.
- Code facts banked:
  chose `X0 = 16` and added
  `small_T_concrete_contour_remainder_normalized_sup_from_slab16_and_tail16`.
  This specializes the generic slab/tail theorem to a genuine compact slab
  `2 <= x <= 16`, `2 <= T <= 16`, plus the asymptotic tail `16 <= x`.
  Added
  `small_T_linear_window_bound_hyp_from_concrete_contour_remainder_slab16_and_tail16`,
  wiring the explicit-cutoff split into `SmallTPerronLinearWindowBoundHyp`.
- Scale check:
  no compactness is claimed outside the slab.  The tail still carries the
  normalized denominator and remains an unbounded analytic estimate.
- Failed/demoted routes:
  did not use an unscaled bound, did not claim global compactness in `x`, and
  did not introduce a legacy `SmallTPerronBoundHyp` instance.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`, or
  `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  Passed under `/tmp/littlewood-lean-singleflight.lock` with the corrected
  non-self-matching guard.
- Smallest next theorem:
  prove either the compact slab atom
  `∃ Cslab > 0, ∀ x T, x >= 2 -> x <= 16 -> 2 <= T -> T <= 16 ->
    |perronVerticalContourRemainderRe x T| /
      (Real.sqrt x * (Real.log T)^2 / Real.sqrt T) <= Cslab`,
  or the asymptotic tail atom
  `∃ Ctail > 0, ∀ x T, 16 <= x -> 2 <= T -> T <= 16 ->
    |perronVerticalContourRemainderRe x T| /
      (Real.sqrt x * (Real.log T)^2 / Real.sqrt T) <= Ctail`.

### 2026-04-29 Round 40 - Compact Slab Bounded Image

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the cutoff-`16` compact slab normalized contour-defect estimate.
- Code facts banked:
  named the normalized defect as
  `perronVerticalContourRemainderNormalized`.  Added
  `small_T_concrete_contour_remainder_slab16_from_bddAbove_image`, proving
  that boundedness above of the normalized defect image over the closed
  rectangle `2 <= x <= 16`, `2 <= T <= 16` yields the required slab estimate.
  Added
  `small_T_concrete_contour_remainder_normalized_sup_from_bddAbove_slab16_and_tail16`
  and
  `small_T_linear_window_bound_hyp_from_concrete_contour_remainder_bddAbove_slab16_and_tail16`
  to wire this compact-slab atom into the existing tail split and
  `SmallTPerronLinearWindowBoundHyp`.
- Scale check:
  this is only a bounded-slab statement.  No compactness is claimed for the
  unbounded `x >= 2` domain; the `16 <= x` tail atom remains separate.
- Failed/demoted routes:
  did not assert a full-domain absorption of `(x / T) * (log x)^2`, did not
  use a constant off-boundary supremum, and did not introduce a legacy
  `SmallTPerronBoundHyp` instance.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`, or
  `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra` under
  `/tmp/littlewood-lean-singleflight.lock`.  First attempt failed because the
  local `BddAbove` witness is an `upperBounds` predicate with implicit set
  element argument; corrected `hM _ himage` to `hM himage`.  Second focused
  build passed.
- Smallest next theorem:
  prove the compactness/continuity input
  `BddAbove (((fun p : ℝ × ℝ =>
      perronVerticalContourRemainderNormalized p.1 p.2) '')
    {p : ℝ × ℝ | 2 <= p.1 /\ p.1 <= 16 /\ 2 <= p.2 /\ p.2 <= 16})`,
  or prove the separate asymptotic tail atom on `16 <= x`.

### 2026-04-29 Round 41 - Compact Slab Continuity Handoff

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the compactness/continuity input for the cutoff-`16` slab
  `BddAbove` image atom.
- Code facts banked:
  added
  `small_T_concrete_contour_remainder_slab16_bddAbove_image_from_continuousOn`.
  It proves the closed rectangle
  `{p : ℝ × ℝ | 2 <= p.1 /\ p.1 <= 16 /\ 2 <= p.2 /\ p.2 <= 16}`
  is compact by rewriting it as `Icc 2 16 ×ˢ Icc 2 16`, then applies
  `IsCompact.bddAbove_image`.  Added
  `small_T_concrete_contour_remainder_slab16_from_continuousOn`,
  `small_T_concrete_contour_remainder_normalized_sup_from_continuousOn_slab16_and_tail16`,
  and
  `small_T_linear_window_bound_hyp_from_concrete_contour_remainder_continuousOn_slab16_and_tail16`
  to wire explicit slab continuity into the existing slab/tail and
  linear-window surfaces.
- Scale check:
  the compactness argument is restricted to `2 <= x <= 16`,
  `2 <= T <= 16`.  The unbounded tail on `16 <= x` remains separate and no
  global compactness in `x` is asserted.
- Failed/demoted routes:
  did not assert continuity of the Perron integral or zeta-log-derivative
  expression yet; that analytic regularity remains an explicit hypothesis.
  Did not introduce a legacy `SmallTPerronBoundHyp` instance.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`, or
  `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra` under
  `/tmp/littlewood-lean-singleflight.lock`.  Initial validation was blocked by
  stale queued validation shells using the old `pgrep -fl` guard; stopped the
  queued Perron shell and retried with the corrected `ps -axo comm=` guard.
  First real build attempt exposed the product-box proposition ordering, so
  the compactness proof was changed from `simpa` to an explicit set equality
  conversion.  Final focused build passed.
- Smallest next theorem:
  prove the slab regularity hypothesis
  `ContinuousOn (fun p : ℝ × ℝ =>
      perronVerticalContourRemainderNormalized p.1 p.2)
    {p : ℝ × ℝ | 2 <= p.1 /\ p.1 <= 16 /\ 2 <= p.2 /\ p.2 <= 16}`,
  or prove the separate asymptotic tail atom on `16 <= x`.

### 2026-04-29 Round 42 - Normalize Slab Continuity to Components

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the slab continuity hypothesis for
  `perronVerticalContourRemainderNormalized` on the cutoff box
  `2 <= x <= 16`, `2 <= T <= 16`.
- Code facts banked:
  added
  `small_T_concrete_contour_remainder_continuousOn_slab16_from_components`,
  reducing unnormalized concrete-remainder continuity to continuity of the two
  analytic components
  `(fun p => perronVerticalIntegral p.1 p.2)` and
  `(fun p => zeroSumRe p.1 p.2)` on the same box.  Added
  `small_T_residue_error_shape_continuousOn_slab16` and
  `small_T_residue_error_shape_ne_zero_on_slab16`, proving the normalization
  denominator is continuous and nonzero on the cutoff slab using
  `small_T_residue_error_shape_pos`.  Added
  `small_T_concrete_contour_remainder_normalized_continuousOn_slab16_from_remainder`
  and
  `small_T_concrete_contour_remainder_normalized_continuousOn_slab16_from_components`.
  Wired the component-continuity route into the normalized slab/tail supremum
  and `SmallTPerronLinearWindowBoundHyp` via
  `small_T_concrete_contour_remainder_normalized_sup_from_component_continuity_slab16_and_tail16`
  and
  `small_T_linear_window_bound_hyp_from_concrete_contour_remainder_component_continuity_slab16_and_tail16`.
- Scale check:
  all continuity and denominator facts are restricted to the compact cutoff box.
  The `16 <= x` tail remains a separate unbounded analytic atom.
- Failed/demoted routes:
  did not claim continuity of the variable-limit Perron integral or zero sum.
  Those are now the explicit smaller slab regularity atoms.  Did not introduce
  a legacy `SmallTPerronBoundHyp` instance or any absorption shortcut.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`, or
  `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `git diff --check`; then
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra` under
  `/tmp/littlewood-lean-singleflight.lock` with the corrected `ps -axo comm=`
  guard.  Both passed.
- Smallest next theorem:
  prove either
  `ContinuousOn (fun p : ℝ × ℝ => perronVerticalIntegral p.1 p.2)
    {p : ℝ × ℝ | 2 <= p.1 /\ p.1 <= 16 /\ 2 <= p.2 /\ p.2 <= 16}`
  and
  `ContinuousOn (fun p : ℝ × ℝ => zeroSumRe p.1 p.2)
    {p : ℝ × ℝ | 2 <= p.1 /\ p.1 <= 16 /\ 2 <= p.2 /\ p.2 <= 16}`,
  or prove the separate asymptotic tail atom on `16 <= x`.

### 2026-04-29 Round 43 - Reduce Zero-Sum Slab Continuity to Local Zero-Set Constancy

- Classification: `THEOREM_LEVEL_REDUCTION`.
- Exact theorem attacked:
  `ContinuousOn (fun p : ℝ × ℝ =>
      Littlewood.Development.HadamardProductZeta.zeroSumRe p.1 p.2)
    {p : ℝ × ℝ | 2 <= p.1 /\ p.1 <= 16 /\ 2 <= p.2 /\ p.2 <= 16}`.
- Code facts banked:
  added `small_T_zeroSumRe_fixedZeros_continuousOn_slab16`, proving
  continuity on the slab for a fixed finite set
  `ZerosBelow T0`.  Added
  `small_T_zeroSumRe_continuousOn_slab16_from_fixedZeros_local_agreement`,
  reducing moving zero-sum continuity to local agreement with the fixed finite
  zero sum at each slab point.  Added
  `small_T_zeroSumRe_continuousOn_slab16_from_zerosBelow_eventually_eq`,
  reducing that local agreement to the exact atom
  `∀ᶠ q in 𝓝[slab] p, ZerosBelow q.2 = ZerosBelow p.2`.
- Scale/shape check:
  the proof is restricted to the cutoff slab and does not claim compactness in
  unbounded `x`.  It also does not assert global continuity of the moving
  finite zero set across zero ordinates.
- Failed/demoted routes:
  did not force direct global zero-sum continuity in `T`; the moving
  `Finset` can jump at zero heights, so local zero-set constancy is now the
  precise smaller atom.  Did not touch the separate Perron-integral
  continuity atom or the `16 <= x` tail atom.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`,
  `SmallTPerronBoundHyp`, or `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `git diff --check`; then
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra` under
  `/tmp/littlewood-lean-singleflight.lock` with the corrected `ps -axo comm=`
  guard.  The first two focused attempts exposed Lean notation issues in the
  new theorem statement (`∑ ... in` and a split `=ᶠ[...]` token); after
  changing to the local `∑ ρ ∈ S` syntax and keeping `=ᶠ[...]` contiguous,
  the focused build passed.
- Smallest next theorem:
  prove the local zero-set constancy atom
  `∀ p ∈ slab, ∀ᶠ q in 𝓝[slab] p,
      ZerosBelow q.2 = ZerosBelow p.2`,
  or separately prove
  `ContinuousOn (fun p : ℝ × ℝ => perronVerticalIntegral p.1 p.2) slab`,
  or the normalized asymptotic tail atom on `16 <= x`.

### 2026-04-29 Round 44 - Push Zero-Sum Constancy Below `ZerosBelow`

- Classification: `THEOREM_LEVEL_REDUCTION`.
- Exact theorem attacked:
  local zero-set constancy on the cutoff slab,
  `∀ p ∈ slab, ∀ᶠ q in 𝓝[slab] p,
      ZerosBelow q.2 = ZerosBelow p.2`.
- Code facts banked:
  added
  `small_T_zerosBelow_eventually_eq_from_criticalZeroSet_eventually_eq`,
  reducing local `ZerosBelow` equality to local equality of the underlying
  closed-height critical-zero sets
  `CriticalZeros ∩ {ρ | |ρ.im| <= T}`.  Added
  `small_T_zeroSumRe_continuousOn_slab16_from_criticalZeroSet_eventually_eq`,
  wiring that smaller set-level atom back into the zero-sum slab-continuity
  route from Round 43.
- Shape check:
  `ZerosBelow T` is defined using the closed boundary condition
  `|ρ.im| <= T`; unconditional local constancy at every slab height would fail
  at a height equal to `|ρ.im|` for a critical zero.  This patch does not claim
  such a boundary-zero exclusion.  It only removes the `Finset`/`toFinset`
  wrapper and leaves the exact set-level stability statement.
- Failed/demoted routes:
  did not assert the global slab local constancy theorem.  Did not claim
  zero-sum continuity through a moving finite set without proving boundary
  stability.  Did not address the separate vertical Perron integral continuity
  or `16 <= x` normalized tail atom.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`,
  `SmallTPerronBoundHyp`, or `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `git diff --check`; then
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra` under
  `/tmp/littlewood-lean-singleflight.lock` with the corrected `ps -axo comm=`
  guard.  Both passed.
- Smallest next theorem:
  prove the set-level local stability atom
  `∀ p ∈ slab, ∀ᶠ q in 𝓝[slab] p,
      CriticalZeros ∩ {ρ | |ρ.im| <= q.2} =
        CriticalZeros ∩ {ρ | |ρ.im| <= p.2}`,
  probably from a boundary-zero exclusion/gap condition; otherwise choose the
  independent atom
  `ContinuousOn (fun p : ℝ × ℝ => perronVerticalIntegral p.1 p.2) slab`,
  or the normalized asymptotic tail atom on `16 <= x`.

### 2026-04-29 Round 45 - Reduce Perron Slab Continuity to Raw Interval Integral

- Classification: `THEOREM_LEVEL_REDUCTION`.
- Exact theorem attacked:
  `ContinuousOn (fun p : ℝ × ℝ => perronVerticalIntegral p.1 p.2)
    {p : ℝ × ℝ | 2 <= p.1 /\ p.1 <= 16 /\ 2 <= p.2 /\ p.2 <= 16}`.
- Code facts banked:
  added `perronVerticalIntegrand`, naming the real vertical-line integrand
  with `c = 1 + 1 / Real.log x`.  Added
  `perronVerticalRawIntegral`, naming the unscaled variable-height integral
  `∫ t in (-T)..T, perronVerticalIntegrand x t`.  Proved
  `perronVerticalIntegral_eq_rawIntegral`, showing the existing public
  `perronVerticalIntegral` is exactly `(2 * Real.pi)⁻¹` times the raw
  integral.  Added
  `small_T_perronVerticalIntegral_continuousOn_slab16_from_rawIntegral`,
  reducing vertical Perron slab continuity to parametric continuity of the raw
  variable-limit interval integral.
- Shape check:
  did not retry unconditional `ZerosBelow`/closed critical-zero set local
  constancy; that remains dishonest at zero boundary heights.  This pass pivots
  to the independent Perron-integral continuity atom and only removes the
  constant prefactor/inlined expression.
- Failed/demoted routes:
  did not attempt to prove the variable-limit integral continuity directly in
  one step.  The remaining proof likely needs a dominated-convergence or fixed
  `[-16,16]` indicator formulation for the moving interval endpoints.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`,
  `SmallTPerronBoundHyp`, or `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `git diff --check`; then
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra` under
  `/tmp/littlewood-lean-singleflight.lock` with the corrected `ps -axo comm=`
  guard.  Both passed.
- Smallest next theorem:
  prove
  `ContinuousOn (fun p : ℝ × ℝ => perronVerticalRawIntegral p.1 p.2) slab`,
  probably by rewriting the moving interval as a fixed `[-16,16]` integral with
  an interval indicator and applying a dominated-convergence theorem; the
  separate normalized `16 <= x` tail atom remains an alternate route.

### 2026-04-29 Round 46 - Reduce Raw Perron Continuity to Fixed Window

- Classification: `THEOREM_LEVEL_REDUCTION`.
- Exact theorem attacked:
  `ContinuousOn (fun p : ℝ × ℝ => perronVerticalRawIntegral p.1 p.2)
    {p : ℝ × ℝ | 2 <= p.1 /\ p.1 <= 16 /\ 2 <= p.2 /\ p.2 <= 16}`.
- Code facts banked:
  added `perronVerticalFixedWindowIntegral`, the fixed `[-16,16]`
  indicator formulation
  `∫ t in (-16)..16, (Set.Icc (-T) T).indicator
    (fun u => perronVerticalIntegrand x u) t`.  Added
  `small_T_perronVerticalRawIntegral_continuousOn_slab16_from_fixedWindow`,
  reducing raw variable-height continuity to fixed-window continuity plus the
  slab equality between the raw and fixed-window integrals.  Added
  `small_T_perronVerticalIntegral_continuousOn_slab16_from_fixedWindow`,
  wiring that fixed-window split through the existing raw-integral prefactor
  handoff for the public vertical Perron integral.
- Shape check:
  this pass keeps the cutoff-`16` slab and does not claim compactness in the
  unbounded `x` direction.  It also does not retry unconditional closed-cutoff
  `ZerosBelow` local constancy at zero heights.
- Failed/demoted routes:
  did not attempt the full dominated-convergence proof in one step.  The
  endpoint algebra/equality between `(-T)..T` and the `[-16,16]` indicator
  form is kept as a separate Lean-facing atom.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`,
  `SmallTPerronBoundHyp`, or `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `git diff --check`; then
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra` under
  `/tmp/littlewood-lean-singleflight.lock` with the corrected `ps -axo comm=`
  guard.  Both passed.
- Smallest next theorem:
  prove the fixed-window atom
  `ContinuousOn (fun p : ℝ × ℝ =>
      perronVerticalFixedWindowIntegral p.1 p.2) slab`
  by a fixed-domain dominated-convergence argument, and prove the endpoint
  equality atom
  `∀ p ∈ slab, perronVerticalRawIntegral p.1 p.2 =
      perronVerticalFixedWindowIntegral p.1 p.2`, likely from
  `intervalIntegral.integral_indicator` and the slab inequalities
  `2 <= T <= 16`.

### 2026-04-29 Round 47 - Close Raw/Fixed Perron Window Equality

- Classification: `PROOF_CLOSED_AND_REDUCTION_SHARPENED`.
- Exact theorem attacked:
  `∀ p ∈ slab, perronVerticalRawIntegral p.1 p.2 =
      perronVerticalFixedWindowIntegral p.1 p.2`.
- Code facts banked:
  changed `perronVerticalFixedWindowIntegral` from a closed `Set.Icc (-T) T`
  indicator to the exact `Set.Ioc (-T) T` interval-integral convention used by
  `intervalIntegral.integral_of_le`.  Proved
  `small_T_perronVerticalRawIntegral_eq_fixedWindow_on_slab16` by rewriting
  both interval integrals to set integrals, using
  `MeasureTheory.integral_indicator measurableSet_Ioc`, and restricting along
  `Set.Ioc (-T) T ⊆ Set.Ioc (-16) 16`.
  Added
  `small_T_perronVerticalRawIntegral_continuousOn_slab16_of_fixedWindow` and
  `small_T_perronVerticalIntegral_continuousOn_slab16_of_fixedWindow`, so the
  public vertical Perron slab-continuity route now needs only the fixed-window
  continuity atom.
- Shape check:
  the equality is exact, not an endpoint-a.e. claim, because the fixed-window
  indicator now matches Lean's half-open interval-integral domain.  The cutoff
  `2 <= T <= 16` supplies the subset into the ambient `[-16,16]` window.
- Failed/demoted routes:
  did not try to prove fixed-window dominated convergence in this pass.  The
  prior closed-interval indicator route would have required an endpoint
  null-set argument; using `Ioc` avoids that extra proof debt.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`,
  `SmallTPerronBoundHyp`, or `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `git diff --check`; then
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra` under
  `/tmp/littlewood-lean-singleflight.lock` with the corrected `ps -axo comm=`
  guard.  Both passed.
- Smallest next theorem:
  prove the remaining fixed-window dominated-convergence atom
  `ContinuousOn (fun p : ℝ × ℝ =>
      perronVerticalFixedWindowIntegral p.1 p.2) slab`.

### 2026-04-29 Round 48 - Reduce Fixed-Window Continuity to Dominated Convergence

- Classification: `THEOREM_LEVEL_REDUCTION`.
- Exact theorem attacked:
  `ContinuousOn (fun p : ℝ × ℝ =>
      perronVerticalFixedWindowIntegral p.1 p.2)
    {p : ℝ × ℝ | 2 <= p.1 /\ p.1 <= 16 /\ 2 <= p.2 /\ p.2 <= 16}`.
- Code facts banked:
  added `perronVerticalFixedWindowIntegrandParam`, bundling the fixed-window
  integrand as a function of `(x,T)` and `t`.  Added
  `perronVerticalFixedWindowIntegral_eq_setIntegral`, rewriting the interval
  integral over `(-16)..16` as the set integral over `Set.Ioc (-16) 16`.
  Added
  `small_T_perronVerticalFixedWindowIntegral_continuousOn_slab16_from_dominated_convergence`,
  reducing fixed-window slab continuity to Mathlib's
  `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`.
- Remaining exact inputs to that theorem:
  local eventual `AEStronglyMeasurable` of
  `fun t => perronVerticalFixedWindowIntegrandParam q t` on
  `volume.restrict (Set.Ioc (-16) 16)`; a local integrable majorant for
  `‖perronVerticalFixedWindowIntegrandParam q t‖`; and a.e. pointwise
  convergence in `q` at each slab point away from the moving indicator
  endpoints.
- Shape check:
  did not claim joint continuity of the indicator integrand.  The pointwise
  convergence obligation is explicitly a.e. on the fixed window, which is the
  honest way to avoid the moving endpoint discontinuities.
- Failed/demoted routes:
  did not attempt to force `continuousOn_integral_of_compact_support`, since
  the indicator factor is not continuous in `(q,t)` at `t = ±q.2`.  Did not
  return to the closed-cutoff zero-set constancy route.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`,
  `SmallTPerronBoundHyp`, or `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `git diff --check`; then
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra` under
  `/tmp/littlewood-lean-singleflight.lock` with the corrected `ps -axo comm=`
  guard.  Both passed.
- Smallest next theorem:
  prove the a.e. moving-indicator convergence atom
  `∀ p ∈ slab, ∀ᵐ t ∂volume.restrict (Set.Ioc (-16) 16),
      Tendsto (fun q : ℝ × ℝ =>
        perronVerticalFixedWindowIntegrandParam q t) (𝓝[slab] p)
        (𝓝 (perronVerticalFixedWindowIntegrandParam p t))`;
  then prove the local measurability and local bounded-majorant atoms for the
  same fixed-window integrand.

### 2026-04-29 Round 49 - Split Fixed-Window DCT Inputs

- Classification: `THEOREM_LEVEL_REDUCTION`.
- Exact DCT inputs attacked:
  local eventual `AEStronglyMeasurable` of
  `fun t => perronVerticalFixedWindowIntegrandParam q t`, and the a.e.
  moving-indicator convergence input for the same fixed-window integrand.
- Code facts banked:
  added
  `small_T_perronVerticalFixedWindowIntegrand_aestronglyMeasurable_from_integrand`,
  reducing the DCT measurability input to measurability of the unwindowed
  Perron integrand on `volume.restrict (Set.Ioc (-16) 16)`.  Added
  `small_T_perronVerticalFixedWindowIntegrand_tendsto_ae_from_integrand_and_membership`,
  reducing the DCT a.e. convergence input to two smaller facts: ordinary
  convergence of `perronVerticalIntegrand q.1 t` at fixed `t`, and eventual
  stability of membership in `Set.Ioc (-q.2) q.2`.
- Shape check:
  did not claim joint continuity of the moving indicator.  The indicator jump
  is isolated into the exact eventual-membership atom, which should be proved
  a.e. by excluding the two endpoint heights `t = p.2` and `t = -p.2`.
- Failed/demoted routes:
  did not force a direct proof of the local integrable-majorant atom.  Did not
  use closed-cutoff zero-set constancy or any public/provider shortcut.
- Circular/forbidden routes avoided:
  no use of shifted remainder atoms, public main imports,
  `general_formula_accessible`, `ContourRemainderBoundHyp.bound`,
  `SmallTPerronBoundHyp`, or `perron_tail_bound_core`.
- Files changed:
  `Littlewood/Aristotle/Standalone/PerronTruncationInfra.lean`;
  `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_perron_b5a.md`.
- Validation:
  `git diff --check`; then
  `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra` under
  `/tmp/littlewood-lean-singleflight.lock` with the corrected `ps -axo comm=`
  guard.  Both passed.
- Smallest next theorem:
  prove the endpoint-exclusion/eventual-membership atom
  `∀ p ∈ slab, ∀ᵐ t ∂volume.restrict (Set.Ioc (-16) 16),
      ∀ᶠ q in 𝓝[slab] p,
        (t ∈ Set.Ioc (-q.2) q.2 ↔ t ∈ Set.Ioc (-p.2) p.2)`;
  separately prove unwindowed Perron integrand measurability/convergence on
  the fixed window and the local integrable-majorant atom.
