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
