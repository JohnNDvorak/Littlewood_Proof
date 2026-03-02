# RH-π 7a/7c: Remaining Deep Obligation (Executable Spec)

## Current Status

The standalone chain is build-clean and deterministic bridges are complete:

- `RHPiPerronFromTruncatedPiBridge` (Perron error transfer)
- `RHPiTargetTowerFromPerronThreshold` (threshold-to-tower bridge)
- `RHPiTowerWitnessFromPerronAndPhase` (payload assembly)
- `RHPi7a7cFromPerronPhase` (7a/7c endpoint)
- `RHPiPhaseCouplingFromThresholdBridge` (class wiring)

The unresolved part is **not** wiring. It is a missing constructive existence theorem producing the phase-coupled families.

As of the latest refactor, `DeepBlockersResolved.rhPiWitness` now consumes these
two classes directly:

- `TargetTowerPhaseCouplingFamilyHyp`
- `AntiTargetTowerPhaseCouplingFamilyHyp`

So the 7a/7c deep blocker now points at the true remaining obligations with no
intermediate tower-wrapper class in the way.

## Why 7a/7c Is Still Open

To instantiate:

- `TargetTowerPhaseCouplingFamilyHyp`
- `AntiTargetTowerPhaseCouplingFamilyHyp`

you must supply, for each RH branch and each threshold `X`, witnesses `(x, T, ε)` with:

1. Perron/truncated explicit formula error at `(x, T)`
2. simultaneous target (or anti-target) phase control on `(finite_zeros_le T).toFinset`
3. quantitative height control compatible with the `lll` budget

Formally (positive branch shape):

```
∀ hRH : RiemannHypothesis,
∀ X : ℝ,
∃ x : ℝ, X < x ∧ ∃ T : ℝ,
  4 ≤ T ∧
  1 < x ∧
  |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ Real.sqrt x / Real.log x ∧
  ∃ ε : ℝ,
    0 < ε ∧ ε < 1 ∧
    (∀ ρ ∈ (finite_zeros_le T).toFinset,
      ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
    x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)))
```

Negative branch is the same with `-(ρ / ‖ρ‖)`.

## Missing Theorem to Prove (Core)

Prove a constructive finite-zero **phase-coupled Perron witness** theorem (positive and negative versions):

```
theorem finite_zero_target_tower_witness_family
  (hRH : RiemannHypothesis) :
  ∀ X : ℝ, ∃ x T ε, ...   -- exact positive branch shape above
```

and analogously:

```
theorem finite_zero_antitarget_tower_witness_family
  (hRH : RiemannHypothesis) :
  ∀ X : ℝ, ∃ x T ε, ...   -- exact negative branch shape
```

Once these are proved, provide instances:

- `TargetTowerPhaseCouplingFamilyHyp`
- `AntiTargetTowerPhaseCouplingFamilyHyp`

and 7a/7c close via existing endpoints.

## Integration Targets

Populate these classes from the two constructive theorems:

- `Littlewood/Aristotle/Standalone/RHPiTowerWitnessFromPerronAndPhase.lean`
  - `TargetTowerPhaseCouplingFamilyHyp.witness`
  - `AntiTargetTowerPhaseCouplingFamilyHyp.witness`

Then these theorems become available immediately (already proved):

- `Aristotle.Standalone.RHPi7a7cFromPerronPhase.rh_pi_7a_7c_pair_from_perron_phase_hyp`
- `Aristotle.Standalone.RHPiPhaseCouplingFromThresholdBridge.rh_pi_7a_7c_pair_from_threshold_hyp`

## Technical Note

Do not spend effort on new wrapper classes until the two witness families above are proved.
All remaining blockers for 7a/7c are concentrated in those two existence theorems.
