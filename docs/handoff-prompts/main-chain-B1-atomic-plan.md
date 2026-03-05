# B1 Atomic Closure Prompt

## Target
Close exactly:
- `Littlewood/Aristotle/Standalone/HardyAfeSignedGapAtomic.lean`
- theorem: `afe_signed_integral_gap_bound_atomic`

Statement:
```lean
(fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t) =O[atTop] (fun T => T)
```

## Existing no-sorry machinery you should use
- `Littlewood/Aristotle/Standalone/HardyAfeMeanSquareBridgeInfra.lean`
  - `zetaMsIntegrand`, `partialMsIntegrand`, `afeGapIntegrand`
- `Littlewood/Aristotle/Standalone/HardyAfeSignedGapScaffold.lean`
  - `integral_afeGap_eq_zeta_minus_two_partial`
  - `signed_gap_isBigO_of_main_term_asymptotics`
- `Littlewood/Aristotle/Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean`
  - `partial_zeta_mean_square_half_coeff` is already proved in-file (private)

## Preferred proof strategy
1. Prove/obtain critical-line zeta second moment in `Icc/Ioc` normalization:
   `∫_1^T zetaMsIntegrand - T log T = O(T)`.
2. Combine with partial channel asymptotic through
   `signed_gap_isBigO_of_main_term_asymptotics`.
3. Keep theorem unconditional (no new axioms/classes).

## Acceptance checks
```bash
lake build Littlewood.Aristotle.Standalone.HardyAfeSignedGapAtomic
./scripts/critical_path_5_status.sh
```
Expected: B1 sorry disappears, no new axiom/postulate lines.
