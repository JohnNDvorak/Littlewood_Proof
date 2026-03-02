# B7 Real-Progress Policy

Canonical scope for this loop:
- `docs/rh_pi_7a7c_remaining_deep_obligation.md`

This policy applies to `scripts/ralph_loop_b7_deep_leaves.sh`.

## Goal
Prevent wheel spinning by requiring measurable constructive proof progress on the
three explicit B7 leaves in
`Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean`.

## Real Progress (strict)
Mode: `leaf_milestone_closure_v1` (default)

A session counts as real progress under a milestone-gated policy.

Path A: leaf closure progress (always valid)
1. B7 deep-leaf sorry count strictly decreases.
2. Targeted build passes.
3. No new axioms were introduced in B7 chain files.
4. No sorry/admit relocation gate failure.
5. No ex-falso gate failure.
6. Construction command completed (not failed/timed out).

Path B: constructive step progress (grace window only)
1. Active leaf is detected from current sorry state:
   - `target` -> `deep_blocker_B7_target_phase_coupling_family_leaf`
   - `antitarget` -> `deep_blocker_B7_antitarget_phase_coupling_family_leaf`
   - `coeff` -> `deep_blocker_B7_coeff_control_leaf`
2. Active leaf session count is within grace (`<= 2` sessions on that leaf).
3. In `DeepBlockersResolved.lean`, at least one new proved active-leaf step lemma is added with prefix:
   - `deep_blocker_B7_target_phase_coupling_step_`
   - `deep_blocker_B7_antitarget_phase_coupling_step_`
   - `deep_blocker_B7_coeff_control_step_`
4. The active leaf proof body adds at least one new usage of the active step prefix.
5. `DeepBlockersResolved.lean` must be edited in-session (mandatory deep edit gate).
6. Session contract markers appear in construct output:
   - `MICRO_GOAL:`
   - `PROVED_LEMMAS:`
   - `LEAF_USAGE:`
   - `BLOCKER_NEXT:`
   - `CLOSURE_PLAN_STEP:`
7. Targeted build passes.
8. No new axioms/sorry relocation/ex-falso gate failures.
9. Construction command completed (not failed/timed out).

Post-grace behavior (`> 2` sessions on active leaf):
- step-lemma deltas are logged but do not count as real progress;
- closure of the active leaf is required for progress credit.

Non-progress signals that do not count by themselves:
- no-exfalso gate pass
- endpoint/gate checks pass with unchanged leaf count
- wiring-only file edits
- analysis-only sessions with no new active-leaf proved-step lemma

## Regression Handling
The loop snapshots the best known state (lowest leaf sorry count with passing
build) under `best_state/` in the run directory.

If a later session increases leaf sorry count above the best known value, the
session is marked as a regression and does not count as progress.

## Stall Policy
Default hard-stop threshold: 5 consecutive sessions without real progress.

Additional anti-wheel-spin hard-stop:
- stop after 2 consecutive sessions without a mandatory deep edit to
  `DeepBlockersResolved.lean`.

Milestone hard-stop (selected policy):
- grace sessions per active leaf: `2`
- deadline sessions per active leaf: `6`
- if the active leaf is still unresolved at deadline, stop immediately and emit
  a milestone escalation bundle (`leaf_milestone_missed_<leaf>`).

On stall stop, the loop emits:
- `escalation_summary.md`
- `escalation_summary.json`

These include last-session metrics, best-state reference, and remaining
constructive theorem targets.

## Required B7 constructive targets
- `deep_blocker_B7_target_phase_coupling_family_leaf`
- `deep_blocker_B7_antitarget_phase_coupling_family_leaf`
- `deep_blocker_B7_coeff_control_leaf`
