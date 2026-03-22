# Criticality Audit: Sorry-to-Main-Theorem Tracing

**Agent 4 (iteration 4), 2026-03-15**

## Method

Traced each sorry through the import and definition chain to determine if it is
transitively needed by `littlewood_psi` (in `Littlewood/Main/LittlewoodPsi.lean`)
or `littlewood_pi_li` (in `Littlewood/Main/LittlewoodPi.lean`).

Both main theorems delegate to:
```
Aristotle.DeepSorries.psi_full_strength_oscillation  (LittlewoodPsi)
Aristotle.DeepSorries.pi_li_full_strength_oscillation (LittlewoodPi)
```
which come from `combined_atoms` in `DeepSorries.lean`, which delegates to:
```
Aristotle.Standalone.DeepBlockersResolved.combined_atoms_resolved_unconditional
```

The critical path is: `LittlewoodPsi/LittlewoodPi -> DeepSorries -> DeepBlockersResolved -> [deep blockers]`.

---

## Results Summary

| # | File | Sorry | Critical Path? | Used By |
|---|------|-------|---------------|---------|
| 1 | RSExpansionProof.lean:3158 | `gabcke_next_order_bound` | **YES** | Hardy chain (B1/B3) |
| 2 | RSExpansionProof.lean:3183 | `block_correction_antitone_from_saddle` | **YES** | Hardy chain (B3) |
| 3 | RSExpansionProof.lean:3434 | `mainTerm_first_moment_ibp` | **YES** | Hardy chain (B1/B2) |
| 4 | ExplicitFormulaPsiB5aDefs.lean:65 | `ZetaLogDerivPointwiseBoundHyp` | **YES** | Psi chain (B5a) |
| 5 | ExplicitFormulaPsiB5aDefs.lean:391 | `SmallTPerronBoundHyp` | **YES** | Psi chain (B5a) |
| 6 | PiLiDirectOscillation.lean:196 | `AbelCorrectionPsiPiHyp` | **NO (dead code)** | Unused instance |
| 7 | PerronExplicitFormulaProvider.lean:1697 | `pi_approx` (known false) | **YES** | Pi chain (B7) |
| 8 | PerronExplicitFormulaProvider.lean:2099 | `tower_cap_dominates` | **YES** | Pi chain (B7) |
| 9 | DirichletApproximation.lean:656 | K-torus Dirichlet | **YES** | Pi chain (B7) |
| 10 | ZeroCountingAssumptions.lean:58 | `ZeroCountingLowerBound` | **YES** | Pi chain (B7) |
| 11 | ZeroCountingAssumptions.lean:65 | `zero_ord_lower_bound` | **YES** | Pi chain (B7) |

**10 of 11 sorrys are on the critical path. 1 is dead code (#6).**

---

## Detailed Traces

### Sorry #1: `gabcke_next_order_bound` (RSExpansionProof.lean:3158) — ON CRITICAL PATH

**Chain:**
```
DeepBlockersResolved
  -> CombinedB1B3DeepLeaf.combined_b1_b3_leaf
    -> B1B3AnalyticDeepLeaf.b1_b3_analytic_deep_leaf
      -> RSExpansionProof.rs_expansion_for_b1b3
        -> rs_expansion_pointwise
          -> rs_saddle_point_bound
            -> saddle_point_remainder
              -> saddle_pointwise_bound_from_cubic
                -> saddle_from_next_correction gabcke_next_order_bound  <-- SORRY #1
```

Also used transitively by `errorTerm_abs_le_on_block` -> `error_block_integral_bound` -> `errorTerm_first_moment_sqrt` -> `siegel_first_moment` -> `hardyZ_first_moment_sqrt_bound`.

**Impact:** Required for both B1 (second moment) and B3 (block structure) deep blockers, which are needed for Hardy's theorem.

### Sorry #2: `block_correction_antitone_from_saddle` (RSExpansionProof.lean:3183) — ON CRITICAL PATH

**Chain:**
```
DeepBlockersResolved
  -> CombinedB1B3DeepLeaf.combined_b1_b3_leaf
    -> B1B3AnalyticDeepLeaf.b1_b3_analytic_deep_leaf
      -> RSExpansionProof.rs_block_antitone
        = block_correction_antitone_from_saddle  <-- SORRY #2
```

Also packaged in `siegel_saddle_and_antitone.2` and `siegel_expansion_core` conjunct 2.

**Impact:** Required for B3 block structure (Gabcke Satz 4). Needed for Hardy's theorem.

### Sorry #3: `mainTerm_first_moment_ibp` (RSExpansionProof.lean:3434) — ON CRITICAL PATH

**Chain:**
```
DeepBlockersResolved
  -> CombinedB1B3DeepLeaf.combined_b1_b3_leaf
    -> B1B3AnalyticDeepLeaf.b1_b3_analytic_deep_leaf (Part 3)
      -> B2FirstMomentFromExpansion.b2_first_moment_core
        -> HardyZFirstMomentIBP.hardyZ_first_moment_sublinear
          -> ibp_oscillatory_bound
            -> RSExpansionProof.hardyZ_first_moment_sqrt_bound
              -> siegel_first_moment
                -> mainTerm_first_moment_ibp  <-- SORRY #3
```

**Impact:** Required for B2 (first moment bound). Also part of the first moment bound that feeds into Hardy's theorem.

### Sorry #4: `ZetaLogDerivPointwiseBoundHyp` (ExplicitFormulaPsiB5aDefs.lean:65) — ON CRITICAL PATH

**Chain:**
```
DeepBlockersResolved
  -> ExplicitFormulaPsiSkeleton
    -> ExplicitFormulaPsiB5aDefs (imports)
      -> instance : ZetaLogDerivPointwiseBoundHyp where bound := by sorry  <-- SORRY #4
```

This typeclass provides the large-T contour bound for the Perron formula. It feeds into
`ContourRemainderBoundHyp` which is used by the explicit formula for psi (B5a blocker).

**Impact:** Required for B5a (explicit formula for psi). Irreducible: needs Hadamard-style
pointwise bound on zeta'/zeta.

### Sorry #5: `SmallTPerronBoundHyp` (ExplicitFormulaPsiB5aDefs.lean:391) — ON CRITICAL PATH

**Chain:**
```
DeepBlockersResolved
  -> ExplicitFormulaPsiSkeleton
    -> ExplicitFormulaPsiB5aDefs (imports)
      -> instance : SmallTPerronBoundHyp where bound := by sorry  <-- SORRY #5
```

Combined with sorry #4 into `ContourRemainderBoundHyp`. The small-T case (T in [2,16])
requires Perron contour integration with bounded height.

**Impact:** Required for B5a. IRREDUCIBLE and INDEPENDENT of sorry #4.
Note: MEMORY.md flags this as CIRCULAR with `SmallTPerronBoundHyp` — the bridge's
`small_T_contour_bound` transits the sorry back through `ContourRemainderBoundHyp`.

### Sorry #6: `AbelCorrectionPsiPiHyp` (PiLiDirectOscillation.lean:196) — NOT ON CRITICAL PATH (DEAD CODE)

**Evidence:**
- `AbelCorrectionPsiPiHyp` is a typeclass defined at line 80 of PiLiDirectOscillation.lean.
- It is instantiated at line 205 (with sorry at line 206).
- It is used ONLY at line 219, inside the `PiApproxFromExplicitFormulaHyp` instance.
- `PiApproxFromExplicitFormulaHyp` is NEVER consumed as a `[PiApproxFromExplicitFormulaHyp]`
  variable anywhere in the codebase. No file uses it as a typeclass dependency.
- The actual pi-chain uses `TruncatedExplicitFormulaPiHyp` (provided by
  `PerronExplicitFormulaProvider.pi_explicit_formula_from_perron`), not `PiApproxFromExplicitFormulaHyp`.

**Confirmed dead code.** Agent 4v3's finding is correct.

### Sorry #7: `pi_approx` (PerronExplicitFormulaProvider.lean:1697) — ON CRITICAL PATH (but KNOWN FALSE)

**Chain:**
```
DeepBlockersResolved
  -> RHPiUnconditionalExactSeedExistence
    -> RHPiExactSeedDeepLeaf
      -> CombinedB5aRHPiDeepLeaf
        -> RHPiExactSeedConstructive
          -> truncatedPiHypInstance
            = PerronExplicitFormulaProvider.pi_explicit_formula_from_perron
              -> .pi_approx := by sorry  <-- SORRY #7
```

The `TruncatedExplicitFormulaPiHyp` typeclass has two fields: `pi_approx` (sorry'd, known false
for S=emptyset) and `zero_sum_neg_frequently` (proved). The sorry propagates because the
typeclass instance is used as a whole by the B7 chain.

**Impact:** This is noted as "known permanent/false" in the mission brief. The `pi_approx`
field has `forall eps > 0` type which is mathematically false. A refactor to split
the typeclass would eliminate this sorry.

### Sorry #8: `tower_cap_dominates_perronThreshold` (PerronExplicitFormulaProvider.lean:2099) — ON CRITICAL PATH

**Chain:**
```
DeepBlockersResolved
  -> ... -> PerronExplicitFormulaProvider
    -> seed_witness_from_perron_core
      -> tower_cap_dominates_perronThreshold  <-- SORRY #8
```

Used at line 2203 in `seed_witness_from_perron_core`, which feeds into
`TargetTowerExactSeedAbovePerronThreshold` and `AntiTargetTowerExactSeedAbovePerronThreshold`.

**Impact:** Required for B7 (RH-side pi-li witness). IRREDUCIBLE without architectural refactor
or explicit Perron threshold growth bound.

### Sorry #9: K-torus Dirichlet (DirichletApproximation.lean:656) — ON CRITICAL PATH

**Chain:**
```
DeepBlockersResolved
  -> ... -> PerronExplicitFormulaProvider
    -> simultaneous_dirichlet_on_interval (line ~2170)
      -> DirichletApprox.inhomogeneous_dirichlet_on_interval_zsmul
        -> inhomogeneous_dirichlet_on_interval  <-- SORRY #9
```

K-torus covering argument (Cassels 1957). The `K >= 1` case requires pigeonhole
on the K-dimensional torus.

**Impact:** Required for constructing Dirichlet phase alignment witnesses in the B7 chain.

### Sorry #10: `ZeroCountingLowerBound` (ZeroCountingAssumptions.lean:58) — ON CRITICAL PATH

**Chain:**
```
DeepBlockersResolved
  -> ... -> PerronExplicitFormulaProvider (imports ZeroCountingAssumptions)
    -> tower_cap_dominates_perronThreshold [ZeroCountingLowerBoundHyp]
```

N(T) >= T/(3pi) * log T, a consequence of the Riemann-von Mangoldt formula.

**Impact:** Required for the tower cap domination (sorry #8) and the seed witness construction.
IRREDUCIBLE: needs the argument principle (not in Mathlib).

### Sorry #11: `zero_ord_lower_bound` (ZeroCountingAssumptions.lean:65) — ON CRITICAL PATH

**Chain:**
```
DeepBlockersResolved
  -> ... -> PerronExplicitFormulaProvider (imports ZeroCountingAssumptions)
    -> simultaneous_dirichlet_on_interval
      -> needs |gamma_k| >= 1 hypothesis
        -> zero_ord_lower_bound  <-- SORRY #11
```

All nontrivial zeta zeros with positive imaginary part have Im(rho) >= 1. Follows from
classical zero-free region. First zero has Im ~ 14.134.

**Impact:** Required for the Dirichlet approximation step in the B7 chain.
IRREDUCIBLE: same barrier as RvM (no zero-free region in Mathlib).

---

## Summary by Proof Chain

### Hardy Chain (sorrys #1, #2, #3)
All three RSExpansionProof sorrys feed into the Hardy chain:
- #1 (gabcke_next_order_bound) -> B1 second moment + B3 block structure
- #2 (block_correction_antitone) -> B3 block structure
- #3 (mainTerm_first_moment_ibp) -> B2 first moment

These are INDEPENDENT of the psi/pi chains.

### Psi Chain (sorrys #4, #5)
Both B5aDefs sorrys feed the explicit formula for psi:
- #4 (ZetaLogDerivPointwiseBound) -> large-T contour bound
- #5 (SmallTPerronBound) -> small-T contour bound (CIRCULAR per MEMORY.md)

These are INDEPENDENT of Hardy chain and pi chain.

### Pi Chain (sorrys #7, #8, #9, #10, #11)
All five feed the RH-side pi-li witness (B7):
- #7 (pi_approx, known false) -> TruncatedExplicitFormulaPiHyp
- #8 (tower_cap_dominates) -> seed witness construction
- #9 (K-torus Dirichlet) -> phase alignment witnesses
- #10 (ZeroCountingLowerBound) -> tower cap argument
- #11 (zero_ord_lower_bound) -> Dirichlet approximation hypothesis

Note: #10 and #11 are also transitively needed by #8.

### Dead Code (sorry #6)
- #6 (AbelCorrectionPsiPiHyp) -> unused PiApproxFromExplicitFormulaHyp instance

---

## Recommendations

1. **Sorry #6 can be deleted** (or its sorry removed with `exact absurd`). It feeds only
   into `PiApproxFromExplicitFormulaHyp` which is never consumed.

2. **Sorry #7 should be refactored.** The `pi_approx` field of `TruncatedExplicitFormulaPiHyp`
   is mathematically false. Splitting the typeclass so `zero_sum_neg_frequently` can be
   provided without the false field would eliminate one sorry.

3. **Sorrys #10 and #11 are prerequisites for #8.** Closing #8 without closing #10 and #11
   first is impossible since `tower_cap_dominates_perronThreshold` requires
   `[ZeroCountingLowerBoundHyp]`.

4. **The 10 critical sorrys split cleanly into 3 independent groups** (Hardy: 3, Psi: 2,
   Pi: 5) that can be attacked in parallel.
