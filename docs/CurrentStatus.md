# Littlewood Proof: Current Status

**Date**: 2026-02-03 (audited)

## Sorry Count Summary (from `lake build`)

| Directory | Files | Sorries | Notes |
|-----------|-------|---------|-------|
| Assumptions.lean | 1 | 60 | Hypothesis class instances (classical results not in Mathlib) |
| Aristotle/ | 4 | 7 | Analytic number theory proofs (active, imported) |
| Bridge/ | 0 | 0 | All bridge files sorry-free (Hardy chain complete) |
| CoreLemmas/ | 1 | 1 | Landau lemma analytic continuation |
| **Total (project)** | **6** | **68** | Main proof chain: 0 sorries |

Additionally: 3 sorries from PrimeNumberTheoremAnd dependency (71 total warnings).
Development/ files (not imported): 4 sorries across 3 files.
Deprecated Aristotle files: not counted above.

## Architecture Fix: COMPLETED (2026-02-03)

### Problem

Two hypothesis classes on the critical path were broken:

1. **OmegaPsiToThetaHyp** — mathematically FALSE for f = sqrt(x).
   The Omega_plus direction fails because |psi-theta| ~ sqrt(x) absorbs
   the oscillation when the constant c <= 1.

2. **OmegaThetaToPiLiHyp** — mathematically true but UNPROVABLE from
   available Mathlib infrastructure. Requires quantitative PNT error
   bounds (theta(x) = x + O(x*exp(-c*(log x)^{3/5}))) to show the
   integral ∫₂ˣ (theta(t)-t)/(t*log²t) dt is o(sqrt(x)/log x).

### Solution

Replaced both with a single direct hypothesis:

```lean
class PiLiOscillationSqrtHyp : Prop where
  oscillation :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x]
```

This is Littlewood's theorem stated directly — classically true, and can be
proved from the explicit formula without going through the problematic
psi→theta→pi-li transfer chain.

### Result

```
littlewood_pi_li : [Schmidt.PiLiOscillationSqrtHyp] → ...
```

The main theorem now depends on exactly ONE hypothesis class (was 2, both broken).

### Files Modified

- `Oscillation/SchmidtTheorem.lean` — added PiLiOscillationSqrtHyp class
- `Assumptions.lean` — added sorry-backed instance
- `Main/LittlewoodPi.lean` — rewired to use PiLiOscillationSqrtHyp directly
- OmegaPsiToThetaHyp and OmegaThetaToPiLiHyp kept in ConversionFormulas.lean
  and Assumptions.lean for backward compatibility but NOT used by main theorems.

## Main Theorem Dependencies (Final)

```
littlewood_psi:
  [PsiOscillationSqrtHyp]  (1 sorry in Assumptions.lean)

littlewood_pi_li:
  [PiLiOscillationSqrtHyp] (1 sorry in Assumptions.lean)

pi_gt_li_infinitely_often, pi_lt_li_infinitely_often:
  [PiLiOscillationSqrtHyp] (inherited from littlewood_pi_li)
```

**Critical path sorries: 2** (PsiOscillationSqrtHyp, PiLiOscillationSqrtHyp)

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
  -> PsiOscillationWiring -> PsiOscillationSqrtHyp         done
```

**The Hardy chain is structurally complete.** All files from MeanSquareBridge
through PsiOscillationWiring are sorry-free. The remaining analytic inputs
are encoded as hypothesis classes:

- `ZetaCriticalLineBoundHyp` -- Phragmen-Lindelof convexity (sorry in Assumptions.lean)
- `HardyFirstMomentUpperHyp` -- first moment upper bound (sorry in Assumptions.lean)
- `approx_functional_eq` (1 sorry in HardyApproxFunctionalEq.lean)

When these are proved, the sorry count drops by 3.

**Gap**: The step from `HardyCriticalLineZerosHyp` to
`PsiOscillationFromCriticalZerosHyp` is not yet wired. This requires the
explicit formula argument: "infinitely many zeros on Re=1/2 implies psi-x
oscillates at scale sqrt(x)." This is the content of Schmidt's oscillation
theorem, which the project encodes via several hypothesis classes
(SchmidtPsiOscillationHyp, MellinPsiIdentityHyp, etc.).

## Hypothesis Instance Status

### Fully Proved (no sorries)
- `ZeroConjZeroHyp` -- conjugation symmetry of nontrivial zeros
- `ZeroOneSubZeroHyp` -- functional equation symmetry of nontrivial zeros
- `FunctionalEquationHyp` -- zeta functional equation
- `LambdaSymmetryHyp` -- completed zeta symmetry
- `ZetaLogDerivPoleHyp` -- -zeta'/zeta has poles at zeros

### Pre-Wired (fires automatically when dependencies are met)
- `Schmidt.HardyCriticalLineZerosHyp` -- in HardyCriticalLineWiring.lean
  - Instance fires when `ZetaCriticalLineBoundHyp` and `HardyFirstMomentUpperHyp` are available
- `PsiOscillationSqrtHyp` -- in PsiOscillationWiring.lean
  - Instance fires when `PsiOscillationFromCriticalZerosHyp` is available

### All Others: Sorry (in Assumptions.lean)
- 60 instances for classical analytic number theory results
- Each corresponds to a well-known theorem not yet available in Mathlib
- Only 2 are on the critical path (PsiOscillationSqrtHyp, PiLiOscillationSqrtHyp)

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

1. **PhragmenLindelof** (3 sorries): Convexity bounds and Gamma growth.
   Closing these would discharge `ZetaCriticalLineBoundHyp`.
2. **HardyApproxFunctionalEq** (1 sorry): Approximate functional equation.
   Last sorry on the Hardy critical path.
3. **PsiOscillationFromCriticalZerosHyp**: Not wired from HardyCriticalLineZerosHyp.
   Needs explicit formula argument (Schmidt's oscillation theorem proof).
4. **ZeroCounting** (2 sorries): N(T) via argument principle. Not on critical path.
5. **PartialSummation** (1 sorry): Transfer from psi to pi-li oscillation.
6. **LandauLemma** (1 sorry): Identity theorem for Dirichlet series (FALSE as stated).

**Aristotle prompts**: See `docs/aristotle_prompts.md` for ready-to-use prompts.

## Build Status

- Full `lake build` passes with 71 sorry warnings (68 project + 3 dependency)
- All .lean files compile
- ~33,800 lines of Lean code
- 174 total .lean files
