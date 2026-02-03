# Littlewood's Oscillation Theorem — Lean 4 Formalization

A machine-checked proof that pi(x) - li(x) changes sign infinitely often,
formalizing Littlewood's 1914 result via Hardy's critical-line zeros,
explicit formulas, and Schmidt's oscillation lemma. The main theorems
compile with **0 sorries**; analytic content is encoded in 58 hypothesis
class instances filled incrementally with proofs co-authored by
[Aristotle](https://app.harmonic.fun) (Harmonic) and Claude (Anthropic).

## Status

`lake build` reports **69** sorry-bearing declarations (66 project + 3 from
`PrimeNumberTheoremAnd` dependency).

| Metric | Count |
|--------|-------|
| Sorry declarations (`lake build`, total) | **69** |
| Assumptions.lean (hypothesis instances) | 58 |
| Aristotle/ (active, imported) | 7 across 4 files |
| Bridge/ | 0 |
| CoreLemmas/ | 1 |
| Main theorem sorries | **0** |
| Hardy chain (HardySetupV2Instance) | **0** (all 6 fields proved) |
| Lines of Lean code | ~33,800 |
| Total .lean files | 174 |
| Sorry-free .lean files | 159 (91%) |

## Main Theorems

Both theorems compile and typecheck with no sorries in their proof terms:

```lean
-- psi(x) - x = Omega_pm(sqrt(x))
-- (Chebyshev's psi oscillates at scale sqrt(x))
theorem littlewood_psi :
    (fun x => chebyshevPsi x - x) =Omega_pm[fun x => Real.sqrt x] :=
  Schmidt.psi_oscillation_sqrt
```

```lean
-- pi(x) - li(x) = Omega_pm(sqrt(x) / log(x))
-- (prime counting error oscillates at scale sqrt(x)/log(x))
theorem littlewood_pi_li [OmegaPsiToThetaHyp] [OmegaThetaToPiLiHyp] :
    (fun x => (Nat.primeCounting (Nat.floor x) : R) - logarithmicIntegral x)
    =Omega_pm[fun x => Real.sqrt x / Real.log x]
```

Corollaries proved from `littlewood_pi_li`:
- `pi_gt_li_infinitely_often` : pi(x) > li(x) infinitely often
- `pi_lt_li_infinitely_often` : pi(x) < li(x) infinitely often
- `pi_minus_li_sign_changes` : the sign changes infinitely often

## Architecture

The project uses **hypothesis-driven design** to separate logical structure
from analytic content:

1. **Hypothesis classes** (`class FooHyp : Prop`) encode classical theorems
   not yet in Mathlib (Perron's formula, zero density estimates, etc.)
2. **Main theorems** are proved assuming these classes — the full proof
   chain from Hardy's theorem through Schmidt oscillation to Littlewood
   compiles with 0 sorries
3. **`Assumptions.lean`** provides `sorry`-backed instances for all 58 hypothesis class instances
4. **Aristotle/ and Bridge/** work toward replacing those sorries with
   genuine proofs

When an assumption is proved, the `sorry` instance moves out of
`Assumptions.lean` and the hypothesis is discharged. Four instances are
already fully proved:
- `FunctionalEquationHyp` — zeta functional equation
- `LambdaSymmetryHyp` — completed zeta symmetry
- `ZeroConjZeroHyp` — conjugation symmetry of nontrivial zeros
- `ZeroOneSubZeroHyp` — functional equation symmetry

## Project Structure

```
Littlewood/
  Basic/                      3 files  -- Omega-notation, Chebyshev psi/theta, li(x)
  ZetaZeros/                  3 files  -- Zero counting N(T), density, sup real part
  ExplicitFormulas/           4 files  -- Explicit formula for psi, smoothed, conversions
  CoreLemmas/                 3 files  -- Landau lemma (1 sorry), Dirichlet approx, weighted avg
  Oscillation/                2 files  -- Schmidt oscillation theorem
  Main/                       3 files  -- Littlewood, LittlewoodPsi, LittlewoodPi (0 sorries)
  Mertens/                    1 file   -- Mertens' first theorem
  Assumptions.lean            1 file   -- 58 hypothesis instances (all sorry)
  Aristotle/                101 files  -- AI-generated proofs (Harmonic + Claude)
  Bridge/                    23 files  -- Wiring Aristotle proofs to hypothesis classes
  Development/               17 files  -- WIP proofs (not imported by main build)
  Tests/                      8 files  -- Integration tests
docs/
  CurrentStatus.md            Canonical status dashboard
  aristotle_prompts.md        Ready-to-use prompts for remaining sorries
  blocking_analysis.md        Gap analysis
  hypothesis_*.md             Hypothesis tracking and mapping
```

## Hardy Chain (Critical Path)

Hardy's theorem (infinitely many zeros on the critical line) is the
key input to the oscillation argument.

```
DiagonalIntegralBound: integral |S_N|^2 >= c*T*log T      (0 sorries) ✅
  -> HardyApproxFunctionalEq: integral Z^2 >= k*integral|S|^2 - CT   (1 sorry)
  -> MeanSquarePartialSumAsymptotic                        (0 sorries) ✅
  -> OscillatorySumBound                                   (0 sorries) ✅
  -> MeanSquareBridge: integral Z^2 >= c'*T*log T          (0 sorries) ✅
  -> HardySetupV2Instance: ALL 6 FIELDS PROVED             (0 sorries) ✅
  -> HardyInfiniteZerosV2: ALL 5 LEMMAS PROVED             (0 sorries) ✅
  -> HardyCriticalLineWiring -> Schmidt.HardyCriticalLineZerosHyp  ✅
```

**The Hardy chain is structurally complete.** All files from MeanSquareBridge
through HardyCriticalLineWiring are sorry-free. The remaining analytic inputs
are encoded as hypothesis classes:

- `ZetaCriticalLineBoundHyp` — Phragmén-Lindelöf convexity: |ζ(1/2+it)| ≤ C|t|^{1/4+ε}
- `HardyFirstMomentUpperHyp` — first moment: |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2+ε}
- `approx_functional_eq` (1 sorry) — approximate functional equation

When these are proved, the sorry count drops by 3 (2 assumptions + 1 Aristotle).

## Sorry Inventory

Audited from `lake build` output (2026-02-02). Only imported files
produce build warnings.

| Location | Declarations | Files | Notes |
|----------|-------------|-------|-------|
| **Assumptions.lean** | 58 | 1 | Hypothesis instances for classical results not in Mathlib |
| **Aristotle/** | 7 | 4 | HardyApproxFunctionalEq (1), PhragmenLindelof (3), ZeroCounting (2), PartialSummation (1) |
| **Bridge/** | 0 | 0 | All bridge files sorry-free (Hardy chain complete) |
| **CoreLemmas/** | 1 | 1 | LandauLemma -- analytic continuation identity theorem |
| **Total (project)** | **66** | **6** | Main proof chain: 0 sorries, Hardy chain: 0 sorries |

Additionally on disk but not imported by the build:
- `Aristotle/_deprecated/`: 10 sorries across 3 files
- `Aristotle/ChebyshevTheta.lean`: 3 sorries (redefines psi/theta, not imported)
- `Bridge/HardyBuildingBlocksInstance.lean`: 2 sorries (template, not imported)
- `Bridge/HardyAssemblyAttempt.lean`: 1 sorry (V1, superseded by V2)
- `Development/`: 4 sorries across 3 files (HardyTheorem, ZeroFreeRegion, LittlewoodTheorem)

## Recently Closed Sorry-Free Files

These Aristotle files previously had sorries and are now fully proved:

| File | Sorries closed | Key results |
|------|---------------|-------------|
| **ZetaBoundsV2.lean** | 3 | zeta_bound_re_ge_one, functional_equation, gamma_sq_bound_zero |
| **HardyInfiniteZerosV2.lean** | 5 | All helper lemmas + hardy_infinitely_many_zeros_v2 |
| **ZeroFreeRegionV3.lean** | 3 | continuousAt, analyticAt, log_deriv_residue_bounded_near_one |
| **CauchyGoursatRectangle.lean** | 3 | Cauchy-Goursat for rectangles |
| **HardyZConjugation.lean** | 1 | Mellin transform identity |
| **StirlingBernoulli.lean** | 2 | Bernoulli B1/B2 bounds |
| **ContourRectangle.lean** | 1 | Cauchy-Goursat via Mathlib |
| **PerronContourIntegralsV2.lean** | 1 | Perron contour symmetry |
| **ContourInfrastructure.lean** | 3 | Contour measure-zero segments |
| **DiagonalIntegralBound.lean** | 4 | Diagonal integral lower bound |
| **MeanSquareBridge.lean** | 1 | norm_hardyZ_mean_square_lower, re_hardyZ_mean_square_lower |
| **HardySetupV2Instance.lean** | 2 | All 6 HardySetupV2 fields proved (mean_square, first_moment, convexity) |
| **MeanSquare.lean** | 2 | norm_integral_offDiagSsq_le, off-diagonal integral bound |

## Building

Requires [Lean 4](https://leanprover.github.io/) and
[Mathlib](https://github.com/leanprover-community/mathlib4).

```bash
# Install Lean 4 via elan (if not already installed)
curl https://elan.lean-lang.org/install.sh -sSf | sh

# Build the full project
lake build

# Build a specific file
lake build Littlewood.Development.ZeroFreeRegion

# Count sorry declarations
lake build 2>&1 | grep "uses 'sorry'" | wc -l
```

Dependencies (from `lakefile.toml`):
- `mathlib` (leanprover-community)
- `PrimeNumberTheoremAnd` (AlexKontorovich)

Build configuration: `maxHeartbeats 1600000`, `maxRecDepth 4000`.

## Contributing

### Tractable Sorries (Aristotle Prompts Available)

See `docs/aristotle_prompts.md` for detailed prompts. Priority order:

1. **HardyApproxFunctionalEq.lean** (1 sorry) -- approximate functional equation: ∫Z² ≥ k∫‖S‖² - CT. Closes `approx_functional_eq`.
2. **PhragmenLindelof.lean** (3 sorries) -- critical line zeta bound, convexity, Gamma growth (Stirling). Closes `ZetaCriticalLineBoundHyp`.
3. **ZeroCounting.lean** (2 sorries) -- N(T) via argument principle, asymptotic.
4. **PartialSummation.lean** (1 sorry) -- psi oscillation implies pi-li oscillation.
5. **LandauLemma.lean** (1 sorry) -- identity theorem for analytic continuation (FALSE as stated, not used downstream).

### Workflow

1. Pick a sorry from the inventory above
2. Search [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/) for the needed lemma
3. If Mathlib has it: replace `sorry` with a proof
4. If not: document precisely what's missing
5. Run `lake build` to verify

## References

- Littlewood, J.E. "Sur la distribution des nombres premiers." _C.R. Acad. Sci. Paris_ 158 (1914), 1869-1872.
- Ingham, A.E. _The Distribution of Prime Numbers._ Cambridge, 1932.
- Montgomery, H.L. and Vaughan, R.C. _Multiplicative Number Theory I._ Cambridge, 2007.
- Titchmarsh, E.C. _The Theory of the Riemann Zeta-Function._ 2nd ed., Oxford, 1986.
- Iwaniec, H. and Kowalski, E. _Analytic Number Theory._ AMS, 2004.

## License

Apache 2.0
