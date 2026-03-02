# DeepSorries Leaf Wiring Map

This map lists the remaining placeholders in
`Littlewood/Aristotle/DeepSorries.lean` and the corresponding standalone leaf
theorems to use for wiring.

All listed leaf theorems are direct-`sorry`-free and `#print axioms` reports
only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## Placeholder 1: Hardy mean-square asymptotic argument

- Location: `Littlewood/Aristotle/DeepSorries.lean:234`
- Current shape:
  - `HardyMeanSquareLeafFromAsymptotic.hardy_mean_square_lower_of_asymptotic sorry`
- Leaf support:
  - `Littlewood/Aristotle/HardyMeanSquareAsymptoticLeaf.lean`
  - class:
    - `Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp`
  - theorem:
    - `Aristotle.HardyMeanSquareAsymptoticLeaf.hardy_mean_square_lower_for_setup_v2`
- Wiring pattern:
  - Either keep current call and replace only the `sorry` with a proof of the
    asymptotic.
  - Or replace entire field with:
    - `Aristotle.HardyMeanSquareAsymptoticLeaf.hardy_mean_square_lower_for_setup_v2`
    after providing an instance of
    `HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp`.

## Placeholder 2: Hardy first-moment upper field

- Location: `Littlewood/Aristotle/DeepSorries.lean:235`
- Leaf support:
  - `Littlewood/Aristotle/HardyFirstMomentUpperLeaf.lean`
  - theorem:
    - `Aristotle.HardyFirstMomentUpperLeaf.hardy_first_moment_upper_for_setup_v2`
- Required instances:
  - `HardyFirstMomentWiring.MainTermFirstMomentBoundHyp`
  - `HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp`

## Placeholders 3-4: RH ψ frequent witnesses

- Location: `Littlewood/Aristotle/DeepSorries.lean:267` (two `sorry`s)
- Leaf support:
  - `Littlewood/Aristotle/RHPsiFrequentWitnessLeaf.lean`
  - class:
    - `Aristotle.RHPsiFrequentWitnessLeaf.RHPsiFrequentWitnessHyp`
  - theorem:
    - `Aristotle.RHPsiFrequentWitnessLeaf.rh_psi_oscillation_from_witnesses`
- Wiring pattern:
  - Replace
    `Aristotle.RHCaseOscillation.rh_psi_oscillation_from_frequent sorry sorry`
    with:
    - `Aristotle.RHPsiFrequentWitnessLeaf.rh_psi_oscillation_from_witnesses`
  - after providing an instance of
    `RHPsiFrequentWitnessLeaf.RHPsiFrequentWitnessHyp`.

## Placeholder 5: LandauAbscissaHyp argument

- Location: `Littlewood/Aristotle/DeepSorries.lean:275`
- Leaf support:
  - `Littlewood/Aristotle/LandauAbscissaHypLeaf.lean`
  - class (optional):
    - `Aristotle.LandauAbscissaHypLeaf.LandauRealIntegrabilityHyp`
  - theorem:
    - `Aristotle.LandauAbscissaHypLeaf.landau_abscissa_hyp_of_real_integrability`
  - theorem (instance-style):
    - `Aristotle.LandauAbscissaHypLeaf.landau_abscissa_hyp_of_instance`
- Required input:
  - `Aristotle.LandauAbscissaConvergence.RealIntegrabilityHyp`

## Placeholders 6-7: RH π-li frequent witnesses

- Location: `Littlewood/Aristotle/DeepSorries.lean:282` (two `sorry`s)
- Leaf support:
  - `Littlewood/Aristotle/RHPiLiFrequentWitnessLeaf.lean`
  - class:
    - `Aristotle.RHPiLiFrequentWitnessLeaf.RHPiLiFrequentWitnessHyp`
  - theorem:
    - `Aristotle.RHPiLiFrequentWitnessLeaf.rh_pi_li_oscillation_from_witnesses`
- Wiring pattern:
  - Replace
    `Aristotle.RHCaseOscillation.rh_pi_li_oscillation_from_frequent sorry sorry`
    with:
    - `Aristotle.RHPiLiFrequentWitnessLeaf.rh_pi_li_oscillation_from_witnesses`
  - after providing an instance of
    `RHPiLiFrequentWitnessLeaf.RHPiLiFrequentWitnessHyp`.

## Placeholder 8: PiAtomHardCase argument

- Location: `Littlewood/Aristotle/DeepSorries.lean:288`
- Leaf support:
  - `Littlewood/Aristotle/PiAtomHardCaseLeaf.lean`
  - class (optional):
    - `Aristotle.PiAtomHardCaseLeaf.PiAtomHardCaseHyp`
  - theorem:
    - `Aristotle.PiAtomHardCaseLeaf.pringsheim_pi_atom_of_hard_case`
  - theorem (instance-style):
    - `Aristotle.PiAtomHardCaseLeaf.pringsheim_pi_atom_of_instance`
- Required input:
  - `Aristotle.PringsheimPiAtom.PiAtomHardCase`

## New Standalone Artifacts (Feb 18, 2026)

- `Littlewood/Aristotle/Standalone/HardyApproxFunctionalEqMeanValueLowerDecomp.lean`
  - `Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.zeta_critical_mean_value_lower_of_asymptotic`
    - Converts
      `(fun T => mean_square_zeta (1/2) T - T * log T) =O(T)`
      into the exact atom shape
      `∃ c>0, ∃ T₁≥2, ∀ T≥T₁, ∫_{Ioc 1 T} hardyZ^2 ≥ c*T*log T`.
  - `Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.zeta_critical_mean_value_lower`
    - Instance-specialized version under `[ZetaMeanSquareHalfBound]`.

- `Littlewood/Aristotle/Standalone/PringsheimBinomialRearrangement.lean`
  - `Aristotle.Standalone.PringsheimBinomialRearrangement.sum_range_mul_add_pow_reindex`
    - Finite binomial double-sum reindexing:
      `Σ aₙ(R+t)^n = Σ t^k Σ aₙ * choose(n,k) * R^(n-k)`.
  - `Aristotle.Standalone.PringsheimBinomialRearrangement.sum_range_mul_add_pow_le_of_inner_le`
    - Ordered comparison form for the same rearrangement.
  - Intended use:
    - Directly targets the combinatorial core needed by the remaining
      Landau/Pringsheim extension blocker (`hF_ext` chain).

- `Littlewood/Aristotle/Standalone/RSPerBlockScaledResidualBridge.lean`
  - `Aristotle.Standalone.RSPerBlockScaledResidualBridge.centeredResidualInput_of_scaledResidual`
    - Nontrivial proved inequality:
      from per-block residual `≤ R / hardyN T`, deduce centered residual sum `≤ R`
      using `abs_sum_le_sum_abs` + finite-sum cancellation.
  - `Aristotle.Standalone.RSPerBlockScaledResidualBridge.perBlockSignedBoundHyp_of_scaledResidual`
    - Constructs `RSBlockDecomposition.PerBlockSignedBoundHyp` from one scaled residual hypothesis.
  - `Aristotle.Standalone.RSPerBlockScaledResidualBridge.errorTerm_alternatingSqrt_decomposition_of_scaledResidual`
    - Ready-to-wire decomposition in the shape consumed by
      `RiemannSiegelSignCancellation`.

## Core Compile Fixes

- `Littlewood/Aristotle/RSSignStructure.lean`
  - Fixed theorem signatures to take
    `Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp` explicitly.
  - File now compiles with:
    - `lake env lean Littlewood/Aristotle/RSSignStructure.lean`

## New Standalone Artifact (Feb 18, 2026, cycle 2)

- `Littlewood/Aristotle/Standalone/RSFirstMomentHalfFromLocalBlocks.lean`
  - `Aristotle.Standalone.RSFirstMomentHalfFromLocalBlocks.errorTermFirstMomentBoundHyp_of_local_blocks`
    - Fully proved construction of `HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp`
      from only:
      - `A > 0`, `B ≥ 0`
      - `LocalPerBlockSignedInput A B`
    - Derivation is non-vacuous:
      - uses `RSBlockDecomposition.errorTerm_block_sum`,
      - proves explicit residual control `|Rsum| ≤ N*B`,
      - uses alternating-`sqrt` cancellation (`CosPiSqSign.alternating_sqrt_sum_bound`),
      - converts to the target `T^(1/2+ε)` scale for every `ε > 0`.
    - Axiom check:
      - `#print axioms ...errorTermFirstMomentBoundHyp_of_local_blocks`
      - only `[propext, Classical.choice, Quot.sound]`.
  - `Aristotle.Standalone.RSFirstMomentHalfFromLocalBlocks.hardyFirstMomentUpperHyp_of_mainTerm_and_local_blocks`
    - Immediate wiring endpoint: with `[MainTermFirstMomentBoundHyp]` and local RS
      block input, derives `HardyFirstMomentUpperHyp`.
