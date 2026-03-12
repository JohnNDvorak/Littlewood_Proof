# B5a+B7 Fallback Integration Template

Use this only if Aristotle returns field-level witness terms but not a fully wired module.

## 1) New module skeleton

Create:

`Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTConcreteGlobalWitnessUnconditional.lean`

```lean
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTConcreteGlobalWitnessUnconditional

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors

-- Replace these with concrete unconditional terms from Aristotle output:
axiom hWitness_placeholder :
  ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
    |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
      (-(∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
      C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)

axiom hTruncated_placeholder : TruncatedExplicitFormulaPiHyp

axiom hTarget_placeholder :
  letI : TruncatedExplicitFormulaPiHyp := hTruncated_placeholder
  TargetTowerExactSeedAbovePerronThreshold

axiom hAntiTarget_placeholder :
  letI : TruncatedExplicitFormulaPiHyp := hTruncated_placeholder
  AntiTargetTowerExactSeedAbovePerronThreshold

instance : StrongPNTConcreteGlobalWitnessPayload := by
  exact concrete_global_witness_payload_of_witnesses
    hWitness_placeholder
    hTruncated_placeholder
    hTarget_placeholder
    hAntiTarget_placeholder

end Aristotle.Standalone.ExternalPort.StrongPNTConcreteGlobalWitnessUnconditional
```

## 2) Target theorem replacements

### B5a

```lean
by
  exact shifted_remainder_bound_candidate_of_strongpnt_concrete_witness_payload
```

### RH-pi (truncated)

```lean
by
  exact truncatedExplicitFormulaPi_unconditional_of_strongpnt_concrete_witness_payload
```

### RH-pi (target)

```lean
by
  exact targetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_concrete_witness_payload
```

### RH-pi (anti-target)

```lean
by
  exact antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_concrete_witness_payload
```

## 3) Validation command

```bash
./scripts/validate_b5a_b7_closure.sh
```

## Notes

- Remove all placeholder `axiom` declarations before final merge.
- Final accepted state is no new axioms/postulates/sorries.
