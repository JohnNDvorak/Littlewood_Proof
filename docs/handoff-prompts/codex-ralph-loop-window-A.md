# Codex Ralph Loop — Window A (Direct Closure Path)

## Objective
Close the two in-repo `sorry` sites that are most likely to fall to deterministic wiring or local construction:

1. `Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean:113` (`deep_blocker_B2`)
2. `Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean:168` (`deep_blocker_B7_coeff_control_leaf`)

## Hard constraints
- No `axiom`, no `postulate`, no `sorry`, no `admit`.
- Do not change theorem statements.
- Prefer proving by existing theorem/instance bridge before writing new heavy code.
- Keep edits minimal and localized.

## Loop protocol
1. Run baseline checks:
```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
rg -n "^[[:space:]]*sorry$" \
  Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean \
  Littlewood/Aristotle/Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean \
  Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean \
  Littlewood/Aristotle/Standalone/ExplicitFormulaPsiSkeleton.lean
```
2. Try the smallest proof-body replacement first:
- `deep_blocker_B2 := by infer_instance`
- `deep_blocker_B7_coeff_control_leaf := by exact ?_` via existing pair theorem
3. If inference fails, search for exact bridge theorem names with `rg`.
4. Add only necessary imports into `DeepBlockersResolved.lean` if a bridge theorem exists but is not in scope.
5. Rebuild targeted module:
```bash
lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved
```
6. If successful, rebuild critical chain:
```bash
lake build Littlewood.Aristotle.DeepSorries
```
7. Report after each loop:
- exact code diff summary
- current count of remaining critical-path sorries
- whether any new sorry/axiom appeared

## Preferred closure candidates for B7
Try these first (in order):
1. `RHPiCoeffControlClassInstances.coeffControlClasses_of_correctedPhaseCouplingHyp`
2. `RHPiDeepCoeffControlWitnesses.coeffControlClasses_of_phaseAboveThresholdHyp`
3. `RHPiDeepCoeffControlWitnesses.coeffControlClasses_of_exactSeedAboveThresholdHyp`

Only use a candidate if all required typeclass inputs are already available in-scope without introducing new sorries.

## Preferred closure candidates for B2
Try these first (in order):
1. `infer_instance : HardyFirstMomentWiring.MainTermFirstMomentBoundHyp`
2. existing wiring theorem in `HardyFirstMomentWiring` that returns this class from already available typeclasses.

Do not introduce new placeholder classes or assumptions.

