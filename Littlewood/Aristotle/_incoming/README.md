# Aristotle Incoming Files

*Updated 2026-01-31*

## Intake Process

1. Copy the output file here
2. Run `./intake.sh <filename>` for quick assessment
3. Fix common issues:
   - Add namespace if missing
   - Resolve `exact?` calls (check if Mathlib has the theorem)
   - Remove `#check`/`#print` debug lines
   - Remove duplicate definitions (import from HardyEstimatesPartial etc.)
4. Build: `lake env lean <file>`
5. Move to `../` (main Aristotle directory)
6. Add import to `Littlewood.lean` with sorry annotation
7. Full build: `lake build`
8. Wire to project (update bridges/instances)
9. Commit with clear message and sorry count

## Priority Returns

| Prompt | Purpose | Priority | Impact |
|--------|---------|----------|--------|
| MeanSquareLowerBound | ∫\|Z\|² ≥ c·T·log T | CRITICAL | Fills BuildingBlocks field 4 |
| HardyZIntegralBound | \|∫Z\| ≤ C·T^{1/2+ε} | CRITICAL | Fills BuildingBlocks field 5 |
| HardyInfiniteZerosComplete | Final Hardy assembly | THE PRIZE | Closes HardyCriticalLineZerosHyp |
| ZeroCountingArgument | N(T) arg principle | Medium | Closes ZeroCounting sorry |
| ZetaResidueOne | (s-1)ζ(s) → 1 | DONE ✅ | Used Mathlib's riemannZeta_residue_one |

## When Hardy Arrives

See `Documentation/HardyCompletionChecklist.md` for step-by-step.

Key: Verify it proves infinitely many sign changes of Z(t), then:
1. Wire to BuildingBlocks (HardyBuildingBlocksInstance.lean)
2. Close HardyCriticalLineZerosHyp (HardyCriticalLineWiring.lean)
3. Cascade through dependent assumptions

## Current Active Sorries (12 across 6 Aristotle files)

| File | Sorries | Nature |
|------|---------|--------|
| MeanSquare.lean | 3 | Off-diagonal, normSq, main theorem |
| ZeroCounting.lean | 3 | 1 DEPRECATED, 2 arg principle |
| PhragmenLindelof.lean | 3 | Convexity, Stirling |
| PartialSummation.lean | 1 | ψ → π-li transfer |
| PerronContourIntegralsV2.lean | 1 | Cauchy integral |
| HardyZConjugation.lean | 1 | Mellin identity |

Plus 1 in CoreLemmas/LandauLemma.lean and 58 in Assumptions.lean.
