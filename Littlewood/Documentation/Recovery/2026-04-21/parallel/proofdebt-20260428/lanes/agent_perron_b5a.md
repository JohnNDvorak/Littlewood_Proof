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
