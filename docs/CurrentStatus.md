# Littlewood Proof: Current Status

**Date**: 2026-02-02 (audited)

## Sorry Count Summary (from `lake build`)

| Directory | Files | Sorries | Notes |
|-----------|-------|---------|-------|
| Assumptions.lean | 1 | 58 | Hypothesis class instances (classical results not in Mathlib) |
| Aristotle/ | 4 | 7 | Analytic number theory proofs (active, imported) |
| Bridge/ | 0 | 0 | All bridge files sorry-free (Hardy chain complete) |
| CoreLemmas/ | 1 | 1 | Landau lemma analytic continuation |
| **Total (project)** | **6** | **66** | Main proof chain: 0 sorries |

Additionally: 3 sorries from PrimeNumberTheoremAnd dependency.
Development/ files (not imported): 4 sorries across 3 files.
Deprecated Aristotle files: not counted above.

## Hardy Chain Status (Structurally Complete)

```
DiagonalIntegralBound: integral |S_N|^2 >= c*T*log T      (0 sorries) done
  -> HardyApproxFunctionalEq: integral Z^2 >= k*integral|S|^2 - CT   (1 sorry)
  -> MeanSquarePartialSumAsymptotic                        (0 sorries) done
  -> OscillatorySumBound                                   (0 sorries) done
  -> MeanSquareBridge: integral Z^2 >= c'*T*log T          (0 sorries) done
  -> HardySetupV2Instance: ALL 6 FIELDS PROVED             (0 sorries) done
  -> HardyInfiniteZerosV2: ALL 5 LEMMAS PROVED             (0 sorries) done
  -> HardyCriticalLineWiring -> Schmidt.HardyCriticalLineZerosHyp  done
  -> PsiOscillationWiring -> PsiOscillationSqrtHyp         done (NEW)
```

**The Hardy chain is structurally complete.** All files from MeanSquareBridge
through PsiOscillationWiring are sorry-free. The remaining analytic inputs
are encoded as hypothesis classes:

- `ZetaCriticalLineBoundHyp` -- Phragmen-Lindelof convexity (sorry in Assumptions.lean)
- `HardyFirstMomentUpperHyp` -- first moment upper bound (sorry in Assumptions.lean)
- `approx_functional_eq` (1 sorry in HardyApproxFunctionalEq.lean)

When these are proved, the sorry count drops by 3.

## Bridge Wiring (NEW: PsiOscillationWiring.lean)

A new bridge file `Littlewood/Bridge/PsiOscillationWiring.lean` connects
`PsiOscillationFromCriticalZerosHyp` to `PsiOscillationSqrtHyp`. These
two classes assert the identical proposition (ψ-x = Omega_pm(sqrt(x))),
so the bridge is trivial (0 sorries).

Combined with `HardyCriticalLineWiring`, the chain from Hardy's theorem
to the main `littlewood_psi` theorem is now fully wired:

```
[ZetaCriticalLineBoundHyp] + [HardyFirstMomentUpperHyp]
  -> HardyCriticalLineZerosHyp          (HardyCriticalLineWiring.lean)
  -> PsiOscillationFromCriticalZerosHyp  (still sorry-backed in Assumptions.lean)
  -> PsiOscillationSqrtHyp              (PsiOscillationWiring.lean)
  -> littlewood_psi                     (0 sorries)
```

**Gap**: The step from `HardyCriticalLineZerosHyp` to
`PsiOscillationFromCriticalZerosHyp` is not yet wired. This requires the
explicit formula argument: "infinitely many zeros on Re=1/2 implies ψ-x
oscillates at scale sqrt(x)." This is the content of Schmidt's oscillation
theorem, which the project encodes via several hypothesis classes
(SchmidtPsiOscillationHyp, MellinPsiIdentityHyp, etc.).

## Critical Finding: OmegaPsiToThetaHyp is FALSE

**OmegaPsiToThetaHyp** (in ConversionFormulas.lean) asserts:

> For all f >= sqrt(x), if psi-x = Omega_pm(f), then theta-x = Omega_pm(f).

This is **mathematically false** for f = sqrt(x). The proof fails on the
Omega_plus direction:

- From `theta_psi_simple`: theta(x) = psi(x) + E, where |E| <= 2*sqrt(x)*log(x)
- More precisely, psi(x) - theta(x) = psi(sqrt(x)) + O(x^{1/3}) ~ sqrt(x) by PNT
- So theta(x) - x = (psi(x) - x) - sqrt(x) + o(sqrt(x))
- If psi(x) - x >= c*sqrt(x) i.o. (Omega_plus), then theta(x) - x >= (c-1)*sqrt(x) + o(sqrt(x))
- This is positive only if c > 1, but Omega_plus only guarantees c > 0

The Omega_minus direction works (the -sqrt(x) shift helps), but Omega_plus fails
when the Omega_pm constant c <= 1.

**Impact**: The main theorem `littlewood_pi_li` calls `omega_psi_to_pi_li`
with f = sqrt(x), which chains through OmegaPsiToThetaHyp. Since this
hypothesis is false, it cannot be proved (only sorry-backed).

**Proposed fix**: Replace OmegaPsiToThetaHyp + OmegaThetaToPiLiHyp in the
main chain with a single direct hypothesis:

```lean
class ThetaOscillationSqrtHyp : Prop where
  oscillation : (fun x => chebyshevTheta x - x) =Omega_pm[fun x => Real.sqrt x]

class PiLiOscillationFromThetaHyp : Prop where
  oscillation : (fun x => primeCounting (floor x) - li x) =Omega_pm[fun x => sqrt x / log x]
```

Both are classically true and can be proved from the explicit formula directly
without going through the ψ-to-θ transfer.

## Hypothesis Instance Status

### Fully Proved (no sorries)
- `ZeroConjZeroHyp` -- conjugation symmetry of nontrivial zeros
- `ZeroOneSubZeroHyp` -- functional equation symmetry of nontrivial zeros
- `FunctionalEquationHyp` -- zeta functional equation
- `LambdaSymmetryHyp` -- completed zeta symmetry

### Pre-Wired (fires automatically when dependencies are met)
- `Schmidt.HardyCriticalLineZerosHyp` -- in HardyCriticalLineWiring.lean
  - Instance fires when `ZetaCriticalLineBoundHyp` and `HardyFirstMomentUpperHyp` are available
- `PsiOscillationSqrtHyp` -- in PsiOscillationWiring.lean (NEW)
  - Instance fires when `PsiOscillationFromCriticalZerosHyp` is available

### All Others: Sorry (in Assumptions.lean)
- 58 instances for classical analytic number theory results
- Each corresponds to a well-known theorem not yet available in Mathlib

## Aristotle Module: Active Sorries

| File | Sorries | Topic |
|------|---------|-------|
| PhragmenLindelof.lean | 3 | Convexity bounds, Gamma growth (Stirling) |
| ZeroCounting.lean | 2 | N(T) argument principle + asymptotic |
| HardyApproxFunctionalEq.lean | 1 | Approximate functional equation |
| PartialSummation.lean | 1 | pi(x) - li(x) via partial summation |

**Sorry-free Aristotle files** (previously had sorries): ContourRectangle,
PerronContourIntegralsV2, CauchyGoursatRectangle, StirlingBernoulli,
ZeroFreeRegionV3, HardyZConjugation, HardyInfiniteZerosV2, ZetaBoundsV2,
ContourInfrastructure, DiagonalIntegralBound, MeanSquare, MeanSquareBridge,
HardySetupV2Instance

## Key Gaps for Progress

1. **OmegaPsiToThetaHyp is FALSE** (see above). Architecture change needed.
2. **PhragmenLindelof** (3 sorries): Convexity bounds and Gamma growth.
   Closing these would discharge `ZetaCriticalLineBoundHyp`.
3. **HardyApproxFunctionalEq** (1 sorry): Approximate functional equation.
   Last sorry on the Hardy critical path.
4. **PsiOscillationFromCriticalZerosHyp**: Not wired from HardyCriticalLineZerosHyp.
   Needs explicit formula argument (Schmidt's oscillation theorem proof).
5. **ZeroCounting** (2 sorries): N(T) via argument principle. Not on critical path.
6. **PartialSummation** (1 sorry): Transfer from psi to pi-li oscillation.
7. **LandauLemma** (1 sorry): Identity theorem for Dirichlet series.

**Aristotle prompts**: See `docs/aristotle_prompts.md` for ready-to-use prompts.

## Build Status

- Full `lake build` passes with 69 sorry warnings (66 project + 3 dependency)
- All .lean files compile
- ~33,800 lines of Lean code
- 174 total .lean files, 159 sorry-free (91%)
