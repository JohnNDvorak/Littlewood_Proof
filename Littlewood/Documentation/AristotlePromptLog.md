# Aristotle Prompt Log

*Updated 2026-01-31*

## Completed Prompts (Sorry-Free Returns)

| # | Prompt Name | File Created | Key Theorems | Date |
|---|-------------|-------------|--------------|------|
| 1 | HardyZReal | HardyZReal.lean | completedRiemannZeta_real_on_critical_line | — |
| 2 | HardyZRealV2 | HardyZRealV2.lean | hardyZV2_real, continuous_hardyZV2, hardyZV2_zero_iff_zeta_zero | — |
| 3 | HardyZRealV4 | HardyZRealV4.lean | hardyZV4_real | — |
| 4 | HardyZComplete | HardyZComplete.lean | hardyZV3_real | — |
| 5 | FunctionalEquationV2 | FunctionalEquationV2.lean | LambdaV2_one_sub | — |
| 6 | SchmidtNew | SchmidtNew.lean | schmidt_oscillation, trigPoly_zero_iff_coeffs_zero | — |
| 7 | ZeroCountingNew | ZeroCountingNew.lean | zero_counting infrastructure | — |
| 8 | ThreeFourOneV2 | ThreeFourOneV2.lean | zeta_ne_zero_re_one_v2, three_four_one_v2 | — |
| 9 | LaurentExpansion | LaurentExpansion.lean | neg_zeta_logDeriv_residue_one | — |
| 10 | ThetaLinearBoundV2 | ThetaLinearBoundV2.lean | theta_linear_bound | — |
| 11 | CompletedZetaCriticalLine | CompletedZetaCriticalLine.lean | completedRiemannZeta_critical_line_real | — |
| 12 | RiemannXi | RiemannXi.lean | RiemannXi_one_sub, differentiable_RiemannXi | — |
| 13 | HardyEstimatesPartial | HardyEstimatesPartial.lean | hardyTheta, hardyZ, exp_iTheta_norm | — |
| 14 | HardyZFirstMoment | HardyZFirstMoment.lean | hardyZ_first_moment_crude | 2026-01-31 |
| 15 | ConvexityBounds | ConvexityBounds.lean | phragmen_lindelof_interpolation, norm_gamma bounds | 2026-01-31 |
| 16 | HardyZCauchySchwarz | HardyZCauchySchwarz.lean | integral_cauchy_schwarz, hardyZ_eq_alt | 2026-01-31 |
| 17 | HardyZMeasurability | HardyZMeasurability.lean | hardyZ_integrable, hardySum_integral_eq | 2026-01-31 |
| 18 | ZetaConvexityStrip | ZetaConvexityStrip.lean | zetaAuxG_cont_diff (DiffContOnCl) | 2026-01-31 |
| 19 | MeanSquarePartialSum | MeanSquarePartialSum.lean | meanSquarePartialSum, meanSquareZeta defs | 2026-01-31 |
| — | *(~60 more sorry-free files)* | Various | Various | — |

## Returns with Sorries (Need Follow-up)

| # | Prompt Name | File | Sorries | Nature |
|---|-------------|------|---------|--------|
| 1 | MeanSquare | MeanSquare.lean | 3 | Off-diagonal, normSq, main theorem |
| 2 | ZeroCounting | ZeroCounting.lean | 3 | 1 deprecated, 2 arg principle |
| 3 | PhragmenLindelof | PhragmenLindelof.lean | 3 | Critical line, convexity, Stirling |
| 4 | PartialSummation | PartialSummation.lean | 1 | ψ→π-li transfer |
| 5 | PerronContourIntegralsV2 | PerronContourIntegralsV2.lean | 1 | Cauchy integral |
| 6 | HardyZConjugation | HardyZConjugation.lean | 1 | Mellin identity |

## Pending Critical Prompts

| Priority | Prompt | Purpose | Impact |
|----------|--------|---------|--------|
| CRITICAL | MeanSquareLowerBound | ∫\|Z\|² ≥ c·T·log T | Fills BuildingBlocks field 4 |
| CRITICAL | HardyZIntegralBound | \|∫Z\| ≤ C·T^{1/2+ε} | Fills BuildingBlocks field 5 |
| THE PRIZE | HardyInfiniteZerosComplete | Final Hardy assembly | Closes HardyCriticalLineZerosHyp |
| Medium | ZeroCountingArgument | N(T) via arg principle | Closes ZeroCounting sorry |
| Medium | StirlingForGamma | Stirling asymptotic for Γ | Closes PhragmenLindelof sorry |
| Low | PerronCauchyRectangle | Cauchy integral for rectangle | Closes PerronContourIntegralsV2 sorry |

## Integration Notes

### Intake Process
1. Copy Aristotle output to `_incoming/`
2. Run `./intake.sh <filename>` for quick assessment
3. Fix common issues (namespace, `exact?`, `#check`, duplicates)
4. Build individually: `lake env lean <file>`
5. Move to main Aristotle directory
6. Add import to `Littlewood.lean`
7. Full build: `lake build`

### Common Issues
- **Duplicate definitions**: Aristotle files redefine `hardyTheta`, `hardyZ`, `chebyshevPsi`, etc.
  Solution: Import from canonical source, delete local definition.
- **`exact?` calls**: Replace with actual tactic/term proof.
- **`#check`/`#print` lines**: Remove before integration.
- **Namespace missing**: Add `namespace <ModuleName>` / `end <ModuleName>`.
- **Type mismatches**: `ℝ → ℝ` vs `ℝ → ℂ` for Hardy Z. Use HardyZTransfer bridge.
