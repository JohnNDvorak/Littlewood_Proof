# Blocker External Integration Map (March 5, 2026)

This map is the execution artifact for manual theorem-port integration against the
current critical blockers (`delegated_sorries=13`, `delegated_axiom_postulate_lines=0`).

## Operating Rules

1. Manual port only (no new lake dependency wiring in this pass).
2. No `axiom`, `postulate`, `sorry`, `admit`.
3. Do not touch active B1/B2-owner files while integrating B5a lane payloads.
4. Preserve theorem signatures in critical endpoints.

## Priority Order

1. B5a root constructor (`DirichletPhaseAlignment.ExplicitFormulaPsiHyp`).
2. RH-pi exact-seed root constructor (`RHPiUnconditionalExactSeedRootPayload`).
3. B1/B2 root constructors.
4. RS7 residual blocks.

## Mapping Table

| Lane | Local target (first closure point) | External theorem candidates | Local adapter target |
|---|---|---|---|
| B5a | `Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp` global instance | `PrimeNumberTheoremAnd/MediumPNT.lean`: `SmoothedChebyshevClose`, `SmoothedChebyshevPull1`, `SmoothedChebyshevPull2`, `ZetaBoxEval`, `I1Bound..I5Bound`; `strongpnt/StrongPNT/PNT5_Strong.lean`: `SmoothedChebyshevPull1`, `SmoothedChebyshevPull2`, `ZetaBoxEval`, `I1Bound..I8Bound` | `ExplicitFormulaPsiLegacyLinearLogRootPayload.witness` then `ExplicitFormulaPsiLegacyPayload` instance |
| B5a | `ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.shifted_remainder_bound_leaf` | same as above, plus contour pull stack from `PrimeNumberTheoremAnd/PerronFormula.lean` (`contourPull`, `residuePull1`, `residuePull2`) | close deep leaf via `ExplicitFormulaPsiB5aRootInfra.shifted_remainder_bound_of_legacy_explicit_formula` |
| RH-pi | `RHPiUnconditionalExactSeedRootPayload` instance | no direct 1:1 exact-seed payload found externally; support lemmas from `DirichletNonvanishing/Project/EulerProducts/PNT.lean` (`riemannZeta_ne_zero_of_one_le_re`, `neg_logDeriv_ζ₁_eq`, `continuousOn_neg_logDeriv_ζ₁`) | new provider module constructing explicit `truncated/target/antiTarget` payload terms |
| B1 | `ZetaMeanSquareHalfBound` | `PrimeNumberTheoremAnd` Mellin/Perron stack; `strongpnt` smoothed PNT chain | B1 root provider module exporting class instance |
| B2 | `B2TailVdcRootPayload`, `B2SupportPhaseRootPayload` | `PrimeNumberTheoremAnd/ZetaAppendix.lean`: oscillatory cancellation lemmas (`lemma_aachIBP`, `lemma_aachcanc`, `proposition_applem`) | B2 support/tail constructor adapters |
| RS7 | `ErrorTermExpansion` + `RSBlockBounds` delegated sorries | `strongpnt/StrongPNT/PNT4_ZeroFreeRegion.lean` log-derivative control blocks + `PrimeNumberTheoremAnd` contour residue tools | RS7-specific adapter lemmas (new modules only) |

## Implemented Safe Integration (initial slice)

1. Added isolated adapter module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/DirichletNonvanishingCompat.lean`
2. Exported wrappers:
   - `riemannZeta_ne_zero_of_one_le_re_port`
   - `riemannZeta_residue_one_port`
   - `neg_logDeriv_riemannZeta_eq_LSeries_vonMangoldt_port`
   - `neg_logDeriv_riemannZeta_eq_tsum_term_vonMangoldt_port`
   - `summable_LSeries_term_vonMangoldt_port`
3. Build-validated target:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingCompat`

## Implemented Safe Integration (next slice)

1. Added B5a contour/Perron external-port adapter module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/PrimeNumberTheoremAndContourCompat.lean`
2. Exported wrappers:
   - `perron_truncation_error_port`
   - `contour_remainder_bound_port`
   - `shifted_contours_bound_of_components_port`
   - `legacy_linear_log_bound_of_components_exact_port`
3. Added strongpnt-style log-derivative adapter module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTLogDerivCompat.lean`
4. Exported wrappers:
   - `zeta_logDeriv_meromorphicAt_port`
   - `zeta_logDeriv_meromorphicOrder_neg_port`
   - `zeta_logDeriv_tendsto_cobounded_port`
5. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourCompat`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLogDerivCompat`

## Implemented Safe Integration (constructor-facing wiring slice)

1. Added constructor-facing adapter module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/B5aLegacyPayloadWiring.lean`
2. Exported endpoints:
   - `legacy_linear_log_rootPayload_of_external_witness`
   - `dirichletPhase_explicitFormulaPsiHyp_of_external_witness`
   - `shifted_remainder_bound_of_external_legacy_witness`
3. Build-validated target:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.B5aLegacyPayloadWiring`

## Implemented Safe Integration (payload-class injection slice)

1. Added external payload class module for B5a:
   - `Littlewood/Aristotle/Standalone/ExternalPort/B5aExternalLegacyWitnessPayload.lean`
2. Added external payload class module for RH-pi exact-seed:
   - `Littlewood/Aristotle/Standalone/ExternalPort/RHPiExternalExactSeedPayload.lean`
3. Exported constructor-injection endpoints:
   - B5a:
     - `ExternalLegacyLinearLogWitnessPayload`
     - `shifted_remainder_bound_of_external_payload`
     - `explicitFormulaPsiHyp_of_external_payload`
   - RH-pi:
     - `ExternalExactSeedPayload`
     - `exactSeedUnconditionalTriple_of_externalPayload`
     - component extraction theorems for truncated/target/anti-target payloads
4. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload`

## Implemented Safe Integration (component-payload injection slice)

1. Added external legacy-component payload module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/B5aExternalLegacyComponentsPayload.lean`
2. Added external shifted-component payload module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/B5aExternalShiftedComponentsPayload.lean`
3. Exported constructor-injection endpoints:
   - legacy component lane:
     - `ExternalLegacyLinearLogComponentsPayload`
     - `legacy_linear_log_bound_of_external_components_payload`
     - `explicitFormulaPsiHyp_of_external_legacy_components_payload`
     - `shifted_remainder_bound_of_external_legacy_components_payload`
   - shifted component lane:
     - `ExternalShiftedBoundComponentsPayload`
     - `shifted_remainder_bound_of_external_shifted_components_payload`
     - `explicitFormulaPsiGeneralHyp_of_external_shifted_components_payload`
4. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalShiftedComponentsPayload`

## Implemented Safe Integration (ported-growth theorem slice)

1. Added concrete theorem-port module from strongpnt:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTGrowthCompat.lean`
2. Ported theorem content:
   - `log_pow_nat_le_const_mul_port` (adapted from strongpnt `IBound_aux1`)
   - `log_pow_nat_eventually_linear_port` (eventual-atTop corollary)
3. Build-validated target:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGrowthCompat`

## Implemented Safe Integration (ported-rectangle holomorphic slice)

1. Added concrete theorem-port module from strongpnt contour helper:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTRectangleHolomorphicCompat.lean`
2. Ported theorem content:
   - `bddAbove_norm_image_rectangle_of_holomorphicOn`
3. Build-validated target:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRectangleHolomorphicCompat`

## Implemented Safe Integration (auto-instance wiring slice)

1. Added auto-instance bridge modules:
   - `Littlewood/Aristotle/Standalone/ExternalPort/B5aExternalAutoInstances.lean`
   - `Littlewood/Aristotle/Standalone/ExternalPort/RHPiExternalExactSeedAutoInstances.lean`
2. Exported auto-wiring instances/endpoints:
   - B5a:
     - `ExternalLegacyLinearLogWitnessPayload -> ExplicitFormulaPsiHyp`
     - `ExternalLegacyLinearLogWitnessPayload -> ExplicitFormulaPsiB5aRootPayload`
     - `ExternalLegacyLinearLogWitnessPayload -> ExplicitFormulaPsiGeneralHyp`
     - `ExternalLegacyLinearLogComponentsPayload -> ExplicitFormulaPsiHyp`
     - `ExternalLegacyLinearLogComponentsPayload -> ExplicitFormulaPsiB5aRootPayload`
     - `ExternalLegacyLinearLogComponentsPayload -> ExplicitFormulaPsiGeneralHyp`
     - `ExternalShiftedBoundComponentsPayload -> ExplicitFormulaPsiGeneralHyp`
     - endpoint theorems for shifted-remainder bound via each payload lane
   - RH-pi:
     - `ExternalExactSeedPayload -> TruncatedExplicitFormulaPiHyp`
     - `ExternalExactSeedPayload -> TargetTowerExactSeedAbovePerronThreshold`
     - `ExternalExactSeedPayload -> AntiTargetTowerExactSeedAbovePerronThreshold`
     - `exactSeedUnconditionalTriple_of_externalPayload_auto`
3. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedAutoInstances`

## Implemented Safe Integration (concrete witness-lane slice)

1. Added concrete witness-lane modules:
   - `Littlewood/Aristotle/Standalone/ExternalPort/B5aExternalConcreteWitnessLane.lean`
   - `Littlewood/Aristotle/Standalone/ExternalPort/RHPiExternalConcreteExactSeedLane.lean`
2. Exported concrete theorem-to-endpoint adapters:
   - B5a:
     - `externalLegacyLinearLogWitnessPayload_of_witness`
     - `shifted_remainder_bound_of_concrete_external_witness`
   - RH-pi:
     - `externalExactSeedPayload_of_witness`
     - `truncatedExplicitFormulaPi_of_concrete_external_witness`
     - `targetTowerExactSeedAbovePerronThreshold_of_concrete_external_witness`
     - `antiTargetTowerExactSeedAbovePerronThreshold_of_concrete_external_witness`
     - `exactSeedTriple_of_concrete_external_witness`
3. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteWitnessLane`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalConcreteExactSeedLane`

## Implemented Safe Integration (endpoint adoption slice)

1. Adopted concrete external witness candidate routes into B5a deep-leaf endpoint:
   - `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`
   - added `shifted_remainder_bound_candidate_of_concrete_external_witness`
2. Adopted concrete external witness candidate routes into RH-pi exact-seed endpoint:
   - `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean`
   - added `exactSeedUnconditionalTriple_of_concrete_external_witness`
   - added component candidate routes for truncated/target/anti-target payloads
3. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf`
   - `lake build Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence`

## Immediate B5a Execution Checklist

1. Port one concrete linear-log witness theorem into a new standalone upstream provider module (no atomic/deep-leaf/skeleton imports).
2. Instantiate `ExplicitFormulaPsiLegacyLinearLogRootPayload` from that theorem.
3. Use existing bridges:
   - `ExplicitFormulaPsiLegacyLinearLogProvider` -> `ExplicitFormulaPsiLegacyPayload`
   - `ExplicitFormulaPsiLegacyGlobalInstance` -> global `DirichletPhaseAlignment.ExplicitFormulaPsiHyp`
   - `ExplicitFormulaPsiB5aRootLifts.rootPayload_of_legacy_explicit_formula`
4. Replace B5a deep-leaf `sorry` with `exact` through root-infra endpoint.

## Validation Commands

1. `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf`
2. `lake build Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence`
3. `lake build Littlewood.Aristotle.Standalone.RHPiDeepCoeffControlWitnesses`
4. `lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved`
5. `lake build Littlewood.Aristotle.DeepSorries`
6. `./scripts/root_constructor_status.sh`
7. `./scripts/critical_path_expanded_status.sh`

## Source Index

- External harvest report:
  - `docs/external_repo_harvest_2026-03-05.md`
- Key hits:
  - `docs/review_graphs/external_repo_harvest_keyhits.txt`
- Summary TSV:
  - `docs/review_graphs/external_repo_harvest_summary.tsv`

## Implemented Safe Integration (strongpnt reciprocal/log helper slice)

1. Added helper-compat module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTReciprocalLogCompat.lean`
2. Ported reusable helper theorem shapes from `StrongPNT/PNT5_Strong.lean`:
   - `norm_reciprocal_inequality_1`
   - `norm_reciprocal_inequality`
   - `one_add_inv_log`
   - `log_pos`
3. Build-validated target:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTReciprocalLogCompat`

## Implemented Safe Integration (strongpnt log-derivative holomorphic slice)

1. Added helper-compat module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTLogDerivativeHolomorphicCompat.lean`
2. Ported reusable theorem shapes from Riemann-project holomorphic log-derivative helpers,
   specialized to `riemannZeta` on `Re(s) > 1`:
   - `differentiableOn_logDeriv`
   - `continuousOn_logDeriv`
   - `differentiableOn_logDeriv_riemannZeta_re_gt_one`
   - `differentiableOn_neg_logDeriv_riemannZeta_re_gt_one`
   - `continuousOn_neg_logDeriv_riemannZeta_re_gt_one`
3. Build-validated target:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeHolomorphicCompat`

## Implemented Safe Integration (strongpnt log-derivative rectangle-bound slice)

1. Added helper-compat module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTLogDerivativeRectangleBoundCompat.lean`
2. Exported reusable rectangle boundedness endpoints for `-ζ'/ζ` on `Re(s) > 1`:
   - `bddAbove_norm_neg_logDeriv_image_rectangle_of_re_gt_one`
   - `exists_norm_neg_logDeriv_bound_on_rectangle_of_re_gt_one`
3. Build-validated target:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeRectangleBoundCompat`

## Implemented Safe Integration (B5a concrete component adapter slice)

1. Added adapter module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/B5aExternalConcreteComponentsLane.lean`
2. Exported concrete component-package endpoints:
   - `externalLegacyComponentsPayload_of_witness`
   - `legacy_linear_log_bound_of_concrete_external_components`
   - `explicitFormulaPsiHyp_of_concrete_external_components`
   - `shifted_remainder_bound_of_concrete_external_components`
3. Build-validated target:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteComponentsLane`

## Implemented Safe Integration (RH-pi bundled witness adapter slice)

1. Extended adapter module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/RHPiExternalConcreteExactSeedLane.lean`
2. Added bundled witness container and endpoints:
   - `ConcreteExactSeedTriple`
   - `externalExactSeedPayload_of_triple`
   - `truncatedExplicitFormulaPi_of_concrete_external_triple`
   - `targetTowerExactSeedAbovePerronThreshold_of_concrete_external_triple`
   - `antiTargetTowerExactSeedAbovePerronThreshold_of_concrete_external_triple`
   - `exactSeedTriple_of_concrete_external_triple`
3. Build-validated target:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalConcreteExactSeedLane`

## Implemented Safe Integration (payload-class endpoint adoption slice)

1. Extended blocker endpoint files with typeclass-driven external payload routes:
   - `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`
   - `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean`
2. Added new endpoint candidate route theorems:
   - B5a:
     - `shifted_remainder_bound_candidate_of_external_witness_payload`
     - `shifted_remainder_bound_candidate_of_external_legacy_components_payload`
     - `shifted_remainder_bound_candidate_of_external_shifted_components_payload`
   - RH-pi:
     - `exactSeedUnconditionalTriple_of_externalPayload`
     - `truncatedExplicitFormulaPi_unconditional_of_externalPayload`
     - `targetTowerExactSeedAbovePerronThreshold_unconditional_of_externalPayload`
     - `antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_externalPayload`
3. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf`
   - `lake build Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence`

## Implemented Safe Integration (constructor-readiness module slice)

1. Added synthesis/readiness module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/ExternalConstructorReadiness.lean`
2. Exported constructor-readiness endpoints:
   - `b5a_constructor_bundle_of_concrete_external_witness`
   - `b5a_constructor_bundle_of_concrete_external_components`
   - `rhpi_rootPayload_of_concrete_external_triple`
   - `rhpi_exactSeedTriple_of_concrete_external_triple`
   - `zeta_and_inv_bounds_on_rectangle_of_re_gt_one`
   - `zrf_neg_logDeriv_continuous_on_one_or_zeta_nonzero`
3. Build-validated target:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness`

## Implemented Safe Integration (DirichletNonvanishing pole-cancellation slice)

1. Added adapter module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/DirichletNonvanishingPoleCancellationCompat.lean`
2. Exported ported compatibility endpoints around `ζ₁(s) = (s-1)ζ(s)` (`zrf` in-repo):
   - `zrf_apply_of_ne_one_port`
   - `zrf_nonzero_of_one_or_zeta_nonzero_port`
   - `neg_logDeriv_zrf_eq_port`
   - `continuousOn_neg_logDeriv_zrf_port`

## Implemented Safe Integration (global bundled payload auto-instance slice)

1. Added bundled payload auto-instance module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTGlobalBundlePayloadAutoInstances.lean`
2. Exported constructor/endpoints:
   - `StrongPNTConcreteGlobalBundlePayload`
   - `root_constructor_bundle_of_concrete_global_bundle_payload`
   - `b5a_and_rhpi_endpoints_of_concrete_global_bundle_payload`
   - `concrete_global_bundle_payload_of_bundles`
   - one-shot endpoints from concrete strongpnt bundle terms
3. Extended readiness synthesis module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/ExternalConstructorReadiness.lean`
   - new endpoints:
     - `root_constructor_bundle_of_concrete_global_bundle_payload`
     - `b5a_and_rhpi_endpoints_of_strongpnt_bundles`
4. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness`
3. Build-validated target:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat`

## Implemented Safe Integration (strongpnt zeta/reciprocal rectangle-bound slice)

1. Added helper-compat module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTZetaRectangleBoundCompat.lean`
2. Exported reusable rectangle boundedness endpoints on `Re(s) > 1`:
   - `differentiableOn_riemannZeta_re_gt_one`
   - `differentiableOn_inv_riemannZeta_re_gt_one`
   - `bddAbove_norm_riemannZeta_image_rectangle_of_re_gt_one`
   - `exists_norm_riemannZeta_bound_on_rectangle_of_re_gt_one`
   - `bddAbove_norm_inv_riemannZeta_image_rectangle_of_re_gt_one`
   - `exists_norm_inv_riemannZeta_bound_on_rectangle_of_re_gt_one`
3. Integrated into readiness surface:
   - `ExternalConstructorReadiness.zeta_and_inv_bounds_on_rectangle_of_re_gt_one`
4. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTZetaRectangleBoundCompat`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness`

## Implemented Safe Integration (DirichletNonvanishing `1/ζ₁` rectangle-bound slice)

1. Added helper-compat module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/DirichletNonvanishingZrfReciprocalRectangleBoundCompat.lean`
2. Exported reusable reciprocal-`ζ₁` endpoints (`ζ₁ = (s-1)ζ`, called `zrf` in-repo):
   - `continuousOn_inv_zrf_on_one_or_zeta_nonzero`
   - `bddAbove_norm_inv_zrf_image_rectangle_of_one_or_zeta_nonzero`
   - `exists_norm_inv_zrf_bound_on_rectangle_of_one_or_zeta_nonzero`
   - `exists_norm_inv_zrf_bound_on_rectangle_of_re_gt_one`
3. Integrated into readiness surface:
   - `ExternalConstructorReadiness.zrf_inv_and_neg_logDeriv_bounds_on_rectangle_of_re_gt_one`
4. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfReciprocalRectangleBoundCompat`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness`

## Implemented Safe Integration (DirichletNonvanishing decomposition-bound slice)

1. Added helper-compat modules:
   - `Littlewood/Aristotle/Standalone/ExternalPort/DirichletNonvanishingPrincipalPartRectangleBoundCompat.lean`
   - `Littlewood/Aristotle/Standalone/ExternalPort/DirichletNonvanishingZrfLogDerivByZetaBoundCompat.lean`
2. Exported decomposition-ready endpoints on `Re(s) > 1`:
   - principal-part (`1/(s-1)`) rectangle bounds:
     - `differentiableOn_inv_sub_one_re_gt_one`
     - `bddAbove_norm_inv_sub_one_image_rectangle_of_re_gt_one`
     - `exists_norm_inv_sub_one_bound_on_rectangle_of_re_gt_one`
   - decomposition bound:
     - `exists_norm_neg_logDeriv_zrf_bound_via_zeta_on_rectangle_of_re_gt_one`
3. Integrated into readiness surface:
   - `ExternalConstructorReadiness.zrf_neg_logDeriv_bound_via_zeta_and_principal_part_on_rectangle_of_re_gt_one`
4. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingPrincipalPartRectangleBoundCompat`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfLogDerivByZetaBoundCompat`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness`

## Implemented Safe Integration (strongpnt bundle-to-B5a constructor slice)

1. Added strongpnt-named bundle adapter module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTB5aComponentBundleCompat.lean`
2. Exported endpoints:
   - `StrongPNTB5aComponentBundle`
   - `externalLegacyComponentsPayload_of_strongpnt_bundle`
   - `legacy_linear_log_bound_of_strongpnt_bundle`
   - `shifted_remainder_bound_of_strongpnt_bundle`
3. Extended readiness surface:
   - `ExternalConstructorReadiness.b5a_constructor_bundle_of_strongpnt_component_bundle`

## Implemented Safe Integration (strongpnt log-derivative series slice)

1. Added series-compat module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTLogDerivSeriesCompat.lean`
2. Exported endpoints:
   - `neg_logDeriv_riemannZeta_eq_vonMangoldt_tsum_of_re_gt_one`
   - `neg_logDeriv_riemannZeta_eq_vonMangoldt_tsum_on_line`
   - `summable_vonMangoldt_tsum_on_line`
   - `neg_logDeriv_riemannZeta_re_eq_tsum_re_on_line`
   - `abs_re_neg_logDeriv_riemannZeta_on_line_le_norm`
3. Extended readiness surface:
   - `ExternalConstructorReadiness.neg_logDeriv_riemannZeta_re_series_on_line`

## Implemented Safe Integration (strongpnt bundle adapters slice)

1. Added StrongPNT-style legacy linear-log witness adapter module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTLegacyLinearLogWitnessCompat.lean`
2. Exported B5a-facing endpoints:
   - `StrongPNTLegacyLinearLogWitnessBundle`
   - `externalLegacyLinearLogWitnessPayload_of_strongpnt_bundle`
   - `explicitFormulaPsiHyp_of_strongpnt_bundle`
   - `shifted_remainder_bound_of_strongpnt_legacy_witness_bundle`
   - `b5a_rootPayload_of_strongpnt_legacy_witness_bundle`
3. Added StrongPNT-style RH-pi exact-seed bundle adapter module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTRHPiExactSeedBundleCompat.lean`
4. Exported RH-pi-facing endpoints:
   - `StrongPNTRHPiExactSeedBundle`
   - `concreteExactSeedTriple_of_strongpnt_bundle`
   - `externalExactSeedPayload_of_strongpnt_bundle`
   - `rhpi_rootPayload_of_strongpnt_bundle`
   - `rhpi_exactSeedTriple_of_strongpnt_bundle`
   - component extraction endpoints for truncated/target/anti-target
5. Extended readiness surface:
   - `ExternalConstructorReadiness.b5a_constructor_bundle_of_strongpnt_legacy_witness_bundle`
   - `ExternalConstructorReadiness.rhpi_rootPayload_of_strongpnt_exactSeed_bundle`
   - `ExternalConstructorReadiness.rhpi_exactSeedTriple_of_strongpnt_exactSeed_bundle`
6. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLegacyLinearLogWitnessCompat`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness`

## Implemented Safe Integration (strongpnt global payload auto-instance slice)

1. Added global StrongPNT payload auto-instance module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTGlobalPayloadAutoInstances.lean`
2. Exported unified constructor payload class and endpoints:
   - `StrongPNTGlobalPayload`
   - auto-instances:
     - `StrongPNTGlobalPayload -> ExternalLegacyLinearLogWitnessPayload`
     - `StrongPNTGlobalPayload -> ExternalExactSeedPayload`
   - endpoint theorems:
     - `shifted_remainder_bound_of_strongpnt_global_payload`
     - `exactSeedUnconditionalTriple_of_strongpnt_global_payload`
     - component endpoints for truncated/target/anti-target
3. Extended endpoint candidate-route files:
   - `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`
     - added `shifted_remainder_bound_candidate_of_strongpnt_global_payload`
   - `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean`
     - added candidate routes for the global StrongPNT payload class:
       - `exactSeedUnconditionalTriple_of_strongpnt_global_payload`
       - `truncatedExplicitFormulaPi_unconditional_of_strongpnt_global_payload`
       - `targetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_global_payload`
       - `antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_global_payload`
4. Extended readiness surface:
   - `Littlewood/Aristotle/Standalone/ExternalPort/ExternalConstructorReadiness.lean`
   - added:
     - `b5a_constructor_bundle_of_strongpnt_global_payload`
     - `rhpi_exactSeedTriple_of_strongpnt_global_payload`

## Implemented Safe Integration (strongpnt global concrete constructor slice)

1. Added concrete global payload constructor module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTGlobalPayloadConcreteLane.lean`
2. Exported concrete and bundled constructor lanes:
   - `strongpnt_legacy_bundle_of_witness`
   - `strongpnt_exactSeed_bundle_of_witness`
   - `strongpnt_global_payload_of_witnesses`
   - `strongpnt_global_payload_of_bundles`
3. Exported one-shot endpoint theorems:
   - `b5a_and_rhpi_endpoints_of_concrete_global_witnesses`
   - `b5a_and_rhpi_endpoints_of_strongpnt_bundles`
4. Build-validated target:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadConcreteLane`

## Implemented Safe Integration (global root-constructor bundle slice)

1. Added unified root-constructor bridge module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTGlobalRootConstructors.lean`
2. Exported constructor-facing payload class and endpoints:
   - `StrongPNTConcreteGlobalWitnessPayload`
   - auto-instance:
     - `StrongPNTConcreteGlobalWitnessPayload -> StrongPNTGlobalPayload`
   - constructor endpoints:
     - `explicitFormulaPsiHyp_of_strongpnt_global_payload`
     - `explicitFormulaPsiGeneralHyp_of_strongpnt_global_payload`
     - `rhpi_rootPayload_of_strongpnt_global_payload`
     - `root_constructor_bundle_of_strongpnt_global_payload`
     - `root_constructor_bundle_of_concrete_global_witness_payload`
   - combined endpoint:
     - `b5a_and_rhpi_endpoints_of_concrete_global_witness_payload`
   - concrete payload constructor:
     - `concrete_global_witness_payload_of_witnesses`
3. Extended readiness surface:
   - `Littlewood/Aristotle/Standalone/ExternalPort/ExternalConstructorReadiness.lean`
   - added:
     - `root_constructor_bundle_of_strongpnt_global_payload`
     - `root_constructor_bundle_of_concrete_global_witness_payload`
4. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness`
   - `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf`
   - `lake build Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence`
   - `lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved`
   - `./scripts/critical_path_expanded_status.sh`

## Implemented Safe Integration (external payload lane fusion slice)

1. Added fused external-lane auto-instance module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTGlobalExternalPayloadAutoInstances.lean`
2. Exported cross-lane auto-instance:
   - `[ExternalLegacyLinearLogComponentsPayload]`
   - `[ExternalExactSeedPayload]`
   - `-> StrongPNTConcreteGlobalWitnessPayload`
3. Exported fused endpoint theorems:
   - `root_constructor_bundle_of_external_payload_lanes`
   - `b5a_and_rhpi_endpoints_of_external_payload_lanes`
4. Extended readiness surface:
   - `Littlewood/Aristotle/Standalone/ExternalPort/ExternalConstructorReadiness.lean`
   - added:
     - `root_constructor_bundle_of_external_payload_lanes`
5. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalExternalPayloadAutoInstances`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness`
   - `./scripts/root_constructor_status.sh`
   - `./scripts/critical_path_expanded_status.sh`

## Implemented Safe Integration (external payload bundle-route fusion slice)

1. Added bundled-route fusion module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTGlobalBundleFromExternalPayloads.lean`
2. Exported external-lane to StrongPNT-bundle adapters:
   - `strongpnt_b5a_bundle_of_external_components`
   - `strongpnt_rhpi_bundle_of_external_payload`
3. Exported cross-lane auto-instance:
   - `[ExternalLegacyLinearLogComponentsPayload]`
   - `[ExternalExactSeedPayload]`
   - `-> StrongPNTConcreteGlobalBundlePayload`
4. Exported bundled-route endpoints:
   - `root_constructor_bundle_of_external_payload_lanes_via_bundle`
   - `b5a_and_rhpi_endpoints_of_external_payload_lanes_via_bundle`
5. Extended readiness surface:
   - `Littlewood/Aristotle/Standalone/ExternalPort/ExternalConstructorReadiness.lean`
   - added:
     - `root_constructor_bundle_of_external_payload_lanes_via_bundle`
6. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundleFromExternalPayloads`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness`

## Implemented Safe Integration (StrongPNT concrete-provider bridge slice)

1. Added concrete-provider bridge module:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTConcreteProviderAutoInstances.lean`
2. Exported cross-lane auto-instances/endpoints:
   - auto-instances:
     - `StrongPNTConcreteGlobalWitnessPayload -> B5aConcreteProviderPayload`
     - `StrongPNTConcreteGlobalWitnessPayload -> RHPiConcreteProviderPayload`
   - endpoint theorems:
     - `root_constructor_bundle_of_strongpnt_concrete_witness_payload`
     - `b5a_and_rhpi_endpoints_of_strongpnt_concrete_witness_payload`
     - bundle-class variants for `StrongPNTConcreteGlobalBundlePayload`
3. Extended readiness surface:
   - `Littlewood/Aristotle/Standalone/ExternalPort/ExternalConstructorReadiness.lean`
   - added:
     - `root_constructor_bundle_of_strongpnt_concrete_witness_payload`
     - `b5a_and_rhpi_endpoints_of_strongpnt_concrete_witness_payload`
4. Extended endpoint candidate-route files:
   - `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`
     - `shifted_remainder_bound_candidate_of_strongpnt_concrete_witness_payload`
   - `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean`
     - `truncatedExplicitFormulaPi_unconditional_of_strongpnt_concrete_witness_payload`
     - `targetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_concrete_witness_payload`
     - `antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_concrete_witness_payload`

## Implemented Safe Integration (split-refactor provider payload slice)

1. Added split refactor-provider modules:
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTPNT5RefactorProviderPayload.lean`
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTRHPiRefactorProviderPayload.lean`
   - `Littlewood/Aristotle/Standalone/ExternalPort/StrongPNTSplitRefactorProviderAutoInstances.lean`
2. Exported split-lane payload classes and auto-wiring:
   - B5a split lane:
     - `PNT5StrongRefactorProviderPayload`
     - `PNT5StrongRefactorProviderPayload -> B5aConcreteProviderPayload`
     - `b5a_constructor_bundle_of_pnt5_refactor_provider_payload`
   - RH-pi split lane:
     - `RHPiExactSeedRefactorProviderPayload`
     - `RHPiExactSeedRefactorProviderPayload -> RHPiConcreteProviderPayload`
     - `rhpi_rootPayload_of_refactor_provider_payload`
     - `rhpi_exactSeedTriple_of_refactor_provider_payload`
   - Split-lane fusion:
     - `[PNT5StrongRefactorProviderPayload] [RHPiExactSeedRefactorProviderPayload]`
       `-> PNT5AndRHPiRefactorProviderPayload`
     - root/endpoint bundle theorems via `StrongPNTSplitRefactorProviderAutoInstances`
3. Extended readiness hub:
   - `Littlewood/Aristotle/Standalone/ExternalPort/ExternalConstructorReadiness.lean`
   - Added split-provider readiness endpoints for B5a-only lane, RH-pi-only lane,
     and fused B5a+RH-pi lane.
4. Build-validated targets:
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTPNT5RefactorProviderPayload`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiRefactorProviderPayload`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTSplitRefactorProviderAutoInstances`
   - `lake build Littlewood.Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness`
