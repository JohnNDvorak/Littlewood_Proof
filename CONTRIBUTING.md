# Contributing to Littlewood Formalization

## Sorry Inventory (audited 2026-02-02 from `lake build`)

**66 project sorry declarations** (+ 3 from PrimeNumberTheoremAnd dependency).

### Imported by build (produce warnings)

| File | Declarations | Topic |
|------|-------------|-------|
| `Assumptions.lean` | 58 | Hypothesis class instances (classical results not in Mathlib) |
| `Aristotle/PhragmenLindelof.lean` | 3 | Convexity bounds, Gamma growth (Stirling) |
| `Aristotle/ZeroCounting.lean` | 2 | N(T) argument principle + asymptotic |
| `Aristotle/HardyApproxFunctionalEq.lean` | 1 | Approximate functional equation |
| `Aristotle/MeanSquare.lean` | 0 | **Sorry-free** (off-diagonal integral bound proved) |
| `Aristotle/PartialSummation.lean` | 1 | pi(x) - li(x) via partial summation |
| `CoreLemmas/LandauLemma.lean` | 1 | Analytic continuation identity (FALSE as stated, see docs/) |

### Sorry-free files (recently closed)

These Aristotle and Bridge files previously had sorries and are now fully proved:

| File | Sorries closed | Key results |
|------|---------------|-------------|
| `HardyInfiniteZerosV2.lean` | 5 | All helper lemmas + `hardy_infinitely_many_zeros_v2` |
| `HardySetupV2Instance.lean` | 3 | All 6 `HardySetupV2` fields proved |
| `MeanSquareBridge.lean` | 2 | `norm_hardyZ_mean_square_lower`, `re_hardyZ_mean_square_lower` |
| `ZetaBoundsV2.lean` | 3 | `zeta_bound_re_ge_one`, functional equation, Gamma bound |
| `StirlingBernoulli.lean` | 2 | Bernoulli B1/B2 bounds |
| `DiagonalIntegralBound.lean` | 4 | Diagonal integral lower bound |
| `ContourRectangle.lean` | 1 | Cauchy-Goursat via Mathlib |
| `PerronContourIntegralsV2.lean` | 1 | Perron contour symmetry |
| `HardyZConjugation.lean` | 1 | Mellin transform identity |
| `MeanSquare.lean` | 2 | norm_integral_offDiagSsq_le, off-diagonal integral bound |

### On disk but not imported

| File | Topic |
|------|-------|
| `Aristotle/_deprecated/` | Deprecated files (not imported) |
| `Aristotle/ChebyshevTheta.lean` | Redefines psi/theta (conflicts with Basic/) |
| `Bridge/HardyAssemblyAttempt.lean` | V1 exploration, superseded by V2 chain |
| `Development/` | WIP proofs (not imported by main build) |

## Hardy Chain (Complete)

The Hardy chain from mean square estimates through to `HardyCriticalLineZerosHyp` is
**structurally complete** with 0 sorries in all Bridge files:

```
DiagonalIntegralBound           (0 sorries) ✅
  → HardyApproxFunctionalEq    (1 sorry)   -- approx_functional_eq
  → MeanSquarePartialSumAsymptotic (0 sorries) ✅
  → OscillatorySumBound         (0 sorries) ✅
  → MeanSquareBridge             (0 sorries) ✅
  → HardySetupV2Instance         (0 sorries) ✅
  → HardyInfiniteZerosV2         (0 sorries) ✅
  → HardyCriticalLineWiring      (0 sorries) ✅ → Schmidt
```

The remaining inputs are hypothesis classes (`ZetaCriticalLineBoundHyp`,
`HardyFirstMomentUpperHyp`) whose sorry instances live in `Assumptions.lean`.
The Hardy chain wiring is now fully connected: providing instances for these
two classes automatically discharges `HardyCriticalLineZerosHyp`.

### Recently proved

| Instance | File | Method |
|----------|------|--------|
| `Landau.ZetaLogDerivPoleHyp` | `Assumptions.lean` | analyticOrderAt arithmetic + identity theorem |
| `Schmidt.HardyCriticalLineZerosHyp` | via `HardyCriticalLineWiring` | Wired through bridge (conditional on 2 hyp classes) |

## Tractable Sorries by Difficulty

### Priority 1: HardyApproxFunctionalEq (1 sorry)

Approximate functional equation: `∫ Z² ≥ k ∫ ‖S‖² - CT`. This is the
last sorry on the Hardy critical path. Closing it (plus the two hypothesis
class instances) would make the Hardy chain fully sorry-free.

See [`docs/aristotle_prompts.md`](docs/aristotle_prompts.md) for a detailed prompt.

### Priority 2: PhragmenLindelof (3 sorries)

Three sorries encoding:
- Critical line zeta bound via functional equation + Stirling
- General Phragmen-Lindelof convexity bound
- Gamma function growth (Stirling's approximation)

Closing these would discharge `ZetaCriticalLineBoundHyp` in `Assumptions.lean`.

### Priority 3: ZeroCounting (2 sorries)

N(T) via argument principle and Riemann-von Mangoldt asymptotic.

### Priority 4: PartialSummation (1 sorry)

Transfer: psi oscillation implies pi-li oscillation. Requires bounding
error terms (prime power sums and integral remainder).

### Priority 5: LandauLemma (1 sorry — FALSE as stated)

The `zeta_zero_implies_vonMangoldt_singularity` theorem is FALSE as stated
(see `docs/FALSE_THEOREMS.md`). The `LSeries` function returns 0 for
non-summable series, making it trivially analytic. Not used downstream.
The related `ZetaLogDerivPoleHyp` (−ζ'/ζ has poles at zeta zeros) is now PROVED.

## Workflow

1. Pick a sorry from the inventory above
2. Check [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/)
   for the needed API (especially `Mathlib.NumberTheory.LSeries.*`,
   `Mathlib.NumberTheory.ZetaFunction.*`)
3. If Mathlib has the lemma: replace `sorry` with proof
4. If Mathlib doesn't: document what's missing in an issue
5. Run `lake build` to verify

## Code Style

- Follow Mathlib conventions
- Use `sorry -- BLOCKED: [reason]` for documented blockers
- Add references to Mathlib lemmas in comments
- Keep proofs readable; prefer `exact` over `simp` when clear
- Use `maxHeartbeats 800000` for Aristotle files (not 0)

## Testing

```bash
# Full build
lake build

# Specific file
lake build Littlewood.Aristotle.MeanSquare

# Count sorries
lake build 2>&1 | grep "uses 'sorry'" | wc -l
```

## Questions?

- Open an issue on this repository
- See [`docs/CurrentStatus.md`](docs/CurrentStatus.md) for the latest dashboard
- See [`docs/blocking_analysis.md`](docs/blocking_analysis.md) for gap analysis
