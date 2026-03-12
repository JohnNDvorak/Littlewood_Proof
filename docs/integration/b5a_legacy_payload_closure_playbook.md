# B5a Legacy Payload Closure Playbook

This playbook closes:

- `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean:32`

without changing target signatures and without introducing circular imports.

## What Is Already Built

1. Legacy payload class and global instance bridge:
   - `ExplicitFormulaPsiLegacyGlobalInstance.ExplicitFormulaPsiLegacyPayload`
   - `instance [ExplicitFormulaPsiLegacyPayload] : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp`
2. Legacy root payload scaffolding:
   - `ExplicitFormulaPsiLegacyLinearLogRootInfra.ExplicitFormulaPsiLegacyLinearLogRootPayload`
   - `ExplicitFormulaPsiLegacyLinearLogProvider` root-to-legacy bridge instance
3. B5a bridge from legacy class to shifted bound:
   - `ExplicitFormulaPsiB5aRootLifts.rootPayload_of_legacy_explicit_formula`
   - `ExplicitFormulaPsiB5aRootInfra.shifted_remainder_bound_of_legacy_explicit_formula`

## Missing Constructor (single hard requirement)

Provide one concrete instance:

- `instance : ExplicitFormulaPsiLegacyLinearLogRootPayload`

with witness shape:

- `∃ C, ∀ x T ≥ 2, |chebyshevPsi x - x - (-(∑ ...))| ≤ C * (sqrt*log/sqrt + log)`

## Exact Non-Circular Closure Route (after missing instance exists)

1. Global legacy class synthesis:
   - `ExplicitFormulaPsiLegacyLinearLogProvider` gives
     `ExplicitFormulaPsiLegacyPayload`.
   - `ExplicitFormulaPsiLegacyGlobalInstance` gives
     `Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp`.
2. B5a root payload synthesis:
   - `ExplicitFormulaPsiB5aRootLifts.rootPayload_of_legacy_explicit_formula`.
3. Deep leaf closure:
   - Replace deep leaf `sorry` with
     `exact Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra.shifted_remainder_bound_of_legacy_explicit_formula`.

## Validation

1. `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf`
2. `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiSkeleton`
3. `lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved`
4. `./scripts/critical_path_expanded_status.sh`

