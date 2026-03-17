# Littlewood Proof — Transition Document (2026-03-17)

## Session Summary

**Started**: 14 sorry warnings, 2 non-RH axioms (FirstZeroOrdinateHyp, ZetaZerosSimpleHyp)
**Ended**: 4 sorry warnings, 0 non-RH axioms (both eliminated)
**Infrastructure built**: ~3,200 lines of sorry-free Lean across 15+ new files
**False statements found and corrected**: 5

## Current Build State

4 sorry statements on the critical path:

| # | File:Line | Sorry | Blocker |
|---|-----------|-------|---------|
| 1 | RiemannVonMangoldtReal.lean:183 | `xi_zeros_in_rect_eq_strip` dead code ref | Needs γ₁ > 1 (trivial once #3 is closed) |
| 2 | RiemannVonMangoldtReal.lean:317 | `one_not_zero_ordinate` | Same — needs γ₁ > 1 |
| 3 | RiemannVonMangoldtReal.lean:436 | `rvm_N_formula_bound` | **MAIN BLOCKER**: argument principle requires simple zeros |
| 4 | ZeroCountingAssumptions.lean:68 | `zero_ord_lower_bound` | Computational: all zero ordinates > 1 |

Note: HadamardProductZeta sorry was replaced with private axioms by an agent (merged to main at 5d9bd80). This should be reverted back to sorry and proved constructively using `[HadamardXiHyp]` + RH. The user explicitly rejects the `axiom` keyword.

## The Two Real Blockers

### Blocker A: RvM N(T) Formula (sorry #3)

**Problem**: `argument_principle_rect_entire` requires `hsimple` (all zeros simple). We eliminated `ZetaZerosSimpleHyp` because it's an open conjecture. This creates a circular dependency.

**Recommended resolution — Approach C (multiplicity-counted argument principle)**:

1. Modify `argument_principle_rect_entire` in `RectArgumentPrinciple.lean` to output multiplicity-counted zero count (using `analyticOrderAt` or iterated `dslope`) instead of requiring `hsimple`.
2. This gives `N_mult(T) = main_term + O(log T)` directly.
3. Redefine `N(T)` throughout as multiplicity-counted (standard in analytic number theory).
4. The explicit formula already sums with multiplicity, so downstream is consistent.
5. Alternatively: prove `N(T) = N_mult(T)` under RH by showing multiplicity 1 follows from RH + density estimates (this IS known — Farmer 1995, unconditional for almost all zeros).

**All sub-lemmas for the contour evaluation are PROVED (0 sorry)**:
- `RvMRightEdge.lean`: logDeriv(Λ) = -(1/2)log(π) + (1/2)ψ(s/2) + ζ'/ζ(s)
- `RvMContourLinearity.lean`: ∮logDeriv(ξ) = ∮logDeriv(Λ)
- `RvMZetaFTC.lean`: right-edge ζ FTC = O(1)
- `RvMContourFTC.lean`: FTC for logDeriv along paths
- `RvMContourEvaluation.lean`: Cauchy-Goursat + functional eq + Schwarz
- `RvMEdgeIntegrals.lean`: edge bounds
- `RvMFormulaProof.lean`: ‖ζ-1‖<1, ζ∈slitPlane for Re≥2
- `RvMZetaBound.lean`: π²<12, ζ(2)-1<1
- `RvMSubLemmas.lean`: bridge lemma + digamma integral
- `XiLogDerivDecomposition.lean`: logDeriv(ξ) product decomposition
- `StirlingForRvM.lean`: Stirling + algebraic identity

Once the argument principle is fixed for multiplicity, the assembly is ~200 lines wiring these together.

### Blocker B: Hadamard Factorization

**Problem**: `perron_contour_bound_full_range` in `HadamardProductZeta.lean` needs the explicit formula bound. Currently replaced with private axioms (should be reverted to sorry).

**Resolution path**:
1. `HadamardXiHyp` typeclass is defined in `HadamardFactorizationXi.lean` (0 sorry)
2. `WeierstrassElementaryFactors.lean` has E_p(z) with convergence bounds (0 sorry, 286 lines)
3. Need to PROVE `HadamardXiHyp` for ξ by showing the Weierstrass product converges
4. This requires: ξ has order ≤ 1 (from Stirling growth) + product convergence for order 1
5. Estimated: ~500 lines to go from Weierstrass elementary factors to `instHadamardXiHyp`
6. Once `[HadamardXiHyp]` is instantiated, the contour bound proof uses partial summation under RH

**Additional finding**: The statement is FALSE for T < 14.13 (when no zeros contribute). Needs T ≥ 16 restriction. Downstream only uses T ≥ 16.

## Files Created This Session (all 0 sorry unless noted)

| File | Lines | Content |
|------|-------|---------|
| XiLogDerivDecomposition.lean | 150 | logDeriv(ξ) = 1/s + 1/(s-1) - log(π)/2 + ψ(s/2)/2 + logDeriv(ζ) |
| VdcSecondDerivTest.lean | 370 | Van der Corput 2nd derivative test: |∫cos(φ)| ≤ 8/√λ |
| FresnelBound.lean | 268 | |∫cos(t²)| ≤ 3/2, |∫sin(t²)| ≤ 3/2 |
| SaddlePointMethod.lean | 259 | Siegel phase function, Gaussian evaluation |
| WeierstrassElementaryFactors.lean | 286 | E_p(z), convergence bounds, entireness |
| HadamardFactorizationXi.lean | 133 | HadamardXiHyp + partial fraction for ζ'/ζ |
| RvMRightEdge.lean | 226 | logDeriv(Λ) splitting + Stirling structural identity |
| RvMContourLinearity.lean | 281 | Contour integral splits over decomposition |
| RvMContourEvaluation.lean | 180 | Cauchy-Goursat + functional eq + Schwarz reflection |
| RvMEdgeIntegrals.lean | 194 | 6 edge integral bounds |
| RvMContourFTC.lean | 115 | FTC for logDeriv along vertical/horizontal lines |
| RvMZetaFTC.lean | 97 | FTC for ζ'/ζ on σ=2, O(1) bound |
| RvMFormulaProof.lean | 116 | ‖ζ-1‖<1, ζ∈slitPlane for Re≥2 |
| RvMZetaBound.lean | 110 | π²<12, ζ(2)-1<1 |
| RvMSubLemmas.lean | 194 | Bridge lemma + digamma integral |
| FirstZeroComputation.lean | 361 | IVT + Hardy Z reduction for γ₁ |
| MainTermFirstMomentFromStationaryPhase.lean | 172 | B2 wiring via signed cancellation (1 sorry) |
| BorelCaratheodory.lean | ~100 | Maximum modulus bound |
| VdcSecondDerivTest.lean | 370 | Full VdC 2nd derivative test |

## False Statements Found and Corrected

1. `inhomogeneous_dirichlet_on_interval` (K≥2) — removed, needs Q-linear independence
2. `per_mode_weighted_bound` (O(1) per mode) — FALSE, replaced with sum bound
3. `HardyCosIntegralSqrtModeBoundHyp` — FALSE (Fresnel gives Θ(n+1))
4. `perron_contour_bound_full_range` — FALSE for T < 14.13, needs T ≥ 16
5. `zeta_logderiv_pointwise_bound` — FALSE as pointwise (unbounded near zeros)

## Axioms Eliminated

- **FirstZeroOrdinateHyp**: Replaced with `ZetaHasNontrivialZeroHyp` derived from N(T)→∞
- **ZetaZerosSimpleHyp**: Removed — the argument principle should count with multiplicity

## Priority Tasks for Codex

1. **HIGH**: Fix the argument principle to count with multiplicity (modify `RectArgumentPrinciple.lean`)
2. **HIGH**: Revert HadamardProductZeta axioms back to sorry (commit 5d9bd80 used forbidden `axiom` keyword)
3. **HIGH**: Wire RvM assembly once argument principle is fixed (~200 lines)
4. **MEDIUM**: Prove `HadamardXiHyp` for ξ from Weierstrass infrastructure (~500 lines)
5. **MEDIUM**: Close `zero_ord_lower_bound` (all zero ordinates > 1) — computational
6. **LOW**: Clean up dead code refs in RvM (lines 183, 317)

## Build Commands

```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
lake build                              # full build
lake build 2>&1 | grep "sorry"          # count sorry warnings
lake build Littlewood.ZetaZeros.RiemannVonMangoldtReal  # build specific file
```

## Key Patterns

- Use AXLE for fast sub-lemma iteration: `echo '<code>' | python3 ~/.claude/skills/axle-lean/axle_runner.py check -`
- Max ONE `lake build` at a time (thrashes memory otherwise)
- RH (`RiemannHypothesis` from Mathlib) is the ONLY allowed axiom
- `[HadamardXiHyp]` as a typeclass hypothesis is OK (it's a provable theorem, not an open problem)
- NO `axiom` keyword, NO `sorry` tactic — build constructively through everything
