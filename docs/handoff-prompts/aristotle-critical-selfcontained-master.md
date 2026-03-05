# Aristotle Prompt Pack (Critical Path, Fully Self-Contained)

This pack targets exactly the 5 active critical-path `sorry` sites in the main build chain.

## Environment
- Lean: `leanprover/lean4:v4.27.0-rc1`
- Mathlib: `fdddb3ea2c8c35de4455e033bc2a5df4d3a391ee`
- Policy: **no `axiom`, no `postulate`, no `sorry`, no `admit`**

## Targets (5)
1. `B1` — `afe_integral_remainder_bound`
   - `Littlewood/Aristotle/Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean:208`
2. `B2` — `deep_blocker_B2`
   - `Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean:113`
3. `B3` — `rs_block_analysis`
   - `Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean:130`
4. `B5a` — `shifted_contours_bound`
   - `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiSkeleton.lean:65`
5. `B7` — `deep_blocker_B7_coeff_control_leaf`
   - `Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean:168`

## Files in this pack
- `aristotle-critical-selfcontained-B1.md`
- `aristotle-critical-selfcontained-B2.md`
- `aristotle-critical-selfcontained-B3.md`
- `aristotle-critical-selfcontained-B5a.md`
- `aristotle-critical-selfcontained-B7.md`

## Required response format (for every prompt)
Return exactly these sections:

1. `STATUS: PROVED` or `STATUS: BLOCKED`
2. `PATCH:` with one Lean fenced block containing only the replacement proof term/body for the target theorem.
3. `IMPORT_DELTA:` either `none` or explicit additional imports.
4. `WHY_IT_COMPILES:` short explanation referencing only names in provided context.

## Acceptance rules
- Do not change theorem statements.
- Do not introduce assumptions/axioms/placeholder classes to bypass proof obligations.
- Do not use any repository-local file not included in the prompt context, unless that dependency is explicitly pasted in the prompt.
- Output must be ready to paste into the target theorem body.

## Suggested run order
1. `B7` (can occasionally close through deterministic witness-class bridges)
2. `B1`
3. `B2`
4. `B3`
5. `B5a`
