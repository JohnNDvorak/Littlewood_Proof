# B5a Atomic Closure Prompt

## Target
Close exactly:
- `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundAtomic.lean`
- theorem: `shifted_remainder_bound_atomic`

Statement:
```lean
∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
  |shiftedRemainderRe x T| ≤
    C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)
```

## Existing no-sorry machinery you should use
- `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aDefs.lean`
  - `zeroSumRe`, `shiftedRemainderRe`
- `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aFromShiftedBound.lean`
  - `shifted_contours_components_of_shifted_bound` (already proved)
- `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aComponents.lean`
  - consumes `shifted_remainder_bound_atomic`
- `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aContourBounds.lean`
  - final algebraic combiner already proved

## Preferred proof strategy
1. Prove the direct shifted-remainder bound above (Perron + residue + contour).
2. Do not touch component combiners unless needed; they are already sorry-free.
3. Keep theorem unconditional (no new axioms/classes).

## Acceptance checks
```bash
lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundAtomic
lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiSkeleton
./scripts/critical_path_5_status.sh
```
Expected: B5a main sorry disappears, no new axiom/postulate lines.
