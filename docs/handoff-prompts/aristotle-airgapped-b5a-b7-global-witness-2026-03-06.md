# Aristotle Air-Gapped Prompt: Close B5a + B7(3) via Global Witness

You have **zero repository access**. You cannot open files, search code, or inspect imports.
Treat this prompt as the **entire source of truth**.

Your task is to produce a Lean patch that closes 4 delegated sorries by constructing one missing global payload instance.

## Hard constraints

1. No `axiom`, `postulate`, `sorry`, `admit`.
2. Keep all target theorem signatures unchanged.
3. No weakened assumptions.
4. Output only Lean code blocks for:
   - one new module file content
   - exact replacement theorem bodies for the 4 target sorries
5. No prose in final output besides short code comments.

## Objective

Close these 4 theorems:

- `shifted_remainder_bound_leaf` (B5a deep leaf)
- `truncatedExplicitFormulaPi_unconditional`
- `targetTowerExactSeedAbovePerronThreshold_unconditional`
- `antiTargetTowerExactSeedAbovePerronThreshold_unconditional`

## Key blocker to resolve

Missing global instance:

```lean
Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors.StrongPNTConcreteGlobalWitnessPayload : Prop
```

## Declaration packet (already available in environment)

Use these declarations exactly as given.

```lean
/-- Core class to construct. -/
class StrongPNTConcreteGlobalWitnessPayload : Prop where
  legacyLinearLogWitness :
    ∃ C,
      ∀ (x T : ℝ), x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
            -(∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T, ↑x ^ ρ / ρ).re| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)
  truncatedPi : TruncatedExplicitFormulaPiHyp
  targetSeed :
    letI : TruncatedExplicitFormulaPiHyp := truncatedPi
    TargetTowerExactSeedAbovePerronThreshold
  antiTargetSeed :
    letI : TruncatedExplicitFormulaPiHyp := truncatedPi
    AntiTargetTowerExactSeedAbovePerronThreshold

/-- Constructor helper for the class above. -/
def concrete_global_witness_payload_of_witnesses
  (hWitness :
    ∃ C,
      ∀ (x T : ℝ), x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
            -(∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T, ↑x ^ ρ / ρ).re| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x))
  (hTruncated : TruncatedExplicitFormulaPiHyp)
  (hTarget : TargetTowerExactSeedAbovePerronThreshold)
  (hAntiTarget : AntiTargetTowerExactSeedAbovePerronThreshold) :
  StrongPNTConcreteGlobalWitnessPayload

/-- Endpoint bundle unlocked by the global witness payload. -/
theorem b5a_and_rhpi_endpoints_of_strongpnt_concrete_witness_payload
  [StrongPNTConcreteGlobalWitnessPayload] :
  (∃ C₂ > 0,
      ∀ (x T : ℝ), x ≥ 2 → T ≥ 2 →
        |shiftedRemainderRe x T| ≤
          C₂ * (Real.sqrt x * Real.log T ^ 2 / Real.sqrt T + Real.log x ^ 2)) ∧
    TruncatedExplicitFormulaPiHyp ∧
    TargetTowerExactSeedAbovePerronThreshold ∧
    AntiTargetTowerExactSeedAbovePerronThreshold

/-- Direct closure theorem for B5a sorry once payload exists. -/
theorem shifted_remainder_bound_candidate_of_strongpnt_concrete_witness_payload
  [StrongPNTConcreteGlobalWitnessPayload] :
  ∃ C₂ > 0,
    ∀ (x T : ℝ), x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * Real.log T ^ 2 / Real.sqrt T + Real.log x ^ 2)

/-- Direct closure theorems for RH-pi 3 sorries once payload exists. -/
theorem truncatedExplicitFormulaPi_unconditional_of_strongpnt_concrete_witness_payload
  [StrongPNTConcreteGlobalWitnessPayload] : TruncatedExplicitFormulaPiHyp

theorem targetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_concrete_witness_payload
  [StrongPNTConcreteGlobalWitnessPayload] : TargetTowerExactSeedAbovePerronThreshold

theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_concrete_witness_payload
  [StrongPNTConcreteGlobalWitnessPayload] : AntiTargetTowerExactSeedAbovePerronThreshold
```

## Additional available lanes (if needed)

These are available theorem routes; use only if they help build the global payload instance:

```lean
theorem b5a_and_rhpi_endpoints_of_external_payload_lanes
  [Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload.ExternalLegacyLinearLogComponentsPayload]
  [Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload.ExternalExactSeedPayload] :
  (∃ C₂ > 0, ∀ (x T : ℝ), x ≥ 2 → T ≥ 2 → |shiftedRemainderRe x T| ≤ C₂ * (Real.sqrt x * Real.log T ^ 2 / Real.sqrt T + Real.log x ^ 2)) ∧
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧ AntiTargetTowerExactSeedAbovePerronThreshold

theorem b5a_and_rhpi_endpoints_of_split_refactor_provider_payload
  [Aristotle.Standalone.ExternalPort.StrongPNTPNT5RefactorProviderPayload.PNT5StrongRefactorProviderPayload]
  [Aristotle.Standalone.ExternalPort.StrongPNTRHPiRefactorProviderPayload.RHPiExactSeedRefactorProviderPayload] :
  (∃ C₂ > 0, ∀ (x T : ℝ), x ≥ 2 → T ≥ 2 → |shiftedRemainderRe x T| ≤ C₂ * (Real.sqrt x * Real.log T ^ 2 / Real.sqrt T + Real.log x ^ 2)) ∧
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧ AntiTargetTowerExactSeedAbovePerronThreshold
```

Important observed fact from environment:

```lean
-- This currently fails in the host repo unless you construct missing providers:
-- #synth StrongPNTConcreteGlobalWitnessPayload
```

## Target file snippets to patch

### 1) New file to create

Create:

```lean
Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTConcreteGlobalWitnessUnconditional.lean
```

It must define a global instance:

```lean
instance : Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors.StrongPNTConcreteGlobalWitnessPayload := by
  -- construct with concrete_global_witness_payload_of_witnesses
```

### 2) B5a sorry replacement

Current theorem:

```lean
theorem shifted_remainder_bound_leaf :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  sorry
```

Replace body with:

```lean
by
  exact shifted_remainder_bound_candidate_of_strongpnt_concrete_witness_payload
```

### 3) RH-pi three sorry replacements

Current theorems:

```lean
theorem truncatedExplicitFormulaPi_unconditional : TruncatedExplicitFormulaPiHyp := by
  sorry

theorem targetTowerExactSeedAbovePerronThreshold_unconditional :
    TargetTowerExactSeedAbovePerronThreshold := by
  sorry

theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  sorry
```

Replace with:

```lean
by
  exact truncatedExplicitFormulaPi_unconditional_of_strongpnt_concrete_witness_payload
```

```lean
by
  exact targetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_concrete_witness_payload
```

```lean
by
  exact antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_concrete_witness_payload
```

## Required output format

Return exactly 2 Lean code blocks:

1. **Full content** of new file `StrongPNTConcreteGlobalWitnessUnconditional.lean`.
2. **Patch snippets only** for the 4 theorem body replacements.

Do not include any markdown bullets after code. No explanations.

## Completion criterion

Your generated code must leave no `sorry` in those 4 target theorems and must not introduce new axioms/postulates/sorries.
