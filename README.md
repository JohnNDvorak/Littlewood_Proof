# Littlewood's Oscillation Theorem — Lean 4 Formalization

A machine-checked proof that pi(x) - li(x) changes sign infinitely often,
formalizing Littlewood's 1914 result via Hardy's critical-line zeros,
explicit formulas, and Schmidt's oscillation lemma. The main theorems
compile with **0 sorries**; analytic content is encoded in 58 hypothesis
classes filled incrementally with proofs co-authored by
[Aristotle](https://app.harmonic.fun) (Harmonic) and Claude (Anthropic).

## Status

`lake build` reports **74** sorry-bearing declarations (+ 3 from the
`PrimeNumberTheoremAnd` dependency).

| Metric | Count |
|--------|-------|
| Sorry declarations (`lake build`, project only) | **74** |
| Assumptions.lean (hypothesis instances) | 58 |
| Aristotle/ (active, imported) | 11 across 6 files |
| Bridge/ | 4 across 2 files |
| CoreLemmas/ | 1 |
| Main theorem sorries | **0** |
| Lines of Lean code | ~30,400 |
| Total .lean files | 162 |
| Sorry-free .lean files | 145 (90%) |
| Hardy chain status | 3 Aristotle sorries from completion |

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
3. **`Assumptions.lean`** provides `sorry`-backed instances for all 58 hypothesis classes
4. **Aristotle/ and Bridge/** work toward replacing those sorries with
   genuine proofs

When an assumption is proved, the `sorry` instance moves out of
`Assumptions.lean` and the hypothesis is discharged. Two instances are
already fully proved:
- `ZeroConjZeroHyp` — conjugation symmetry of nontrivial zeros
- `ZeroOneSubZeroHyp` — functional equation symmetry

## Project Structure

```
Littlewood/
  Basic/                      3 files — Omega-notation, Chebyshev psi/theta, li(x)
  ZetaZeros/                  3 files — Zero counting N(T), density, sup real part
  ExplicitFormulas/           4 files — Explicit formula for psi, Perron, smoothed, conversions
  CoreLemmas/                 3 files — Landau lemma (1 sorry), Dirichlet approx, weighted avg
  Oscillation/                2 files — Schmidt oscillation theorem
  Main/                       3 files — Littlewood, LittlewoodPsi, LittlewoodPi (0 sorries)
  Mertens/                    1 file  — Mertens' first theorem
  Assumptions.lean            1 file  — 58 hypothesis instances (all sorry)
  Aristotle/                 93 files — AI-generated proofs (Harmonic), 11 active sorries
  Bridge/                    20 files — Wiring Aristotle proofs to hypothesis classes
  Development/               18 files — WIP proofs (not imported by main build)
  Tests/                      7 files — Integration tests
  Documentation/             40 files — Status tracking, prompt logs
docs/
  CurrentStatus.md            Canonical status dashboard (updated each push)
  blocking_analysis.md        Gap analysis
  hypothesis_*.md             Hypothesis tracking and mapping
  lemma_index.md              Lemma inventory
  sorry_analysis/             Detailed sorry audits
  mathlib_pr_specs/           Specifications for needed Mathlib PRs
  roadmap.md                  Development roadmap
  _archive/                   Historical milestones and old status files
```

## Hardy Chain (Critical Path)

The Hardy chain proves infinitely many zeros on the critical line,
which is the key input to the oscillation argument:

```
HardySetupInstance (3 Aristotle sorries)
  |
  v
HardyInfiniteZeros.hardy_infinitely_many_zeros (0 sorries)
  |
  v
HardyCriticalLineWiring — conversion lemma fully proved
  |
  v
Schmidt.HardyCriticalLineZerosHyp — instance auto-fires when chain closes
```

**3 sorries needed** (all require Aristotle / deep analytic proofs):
1. `mean_square_lower_bound` — integral of Z(t)^2 >= c T log T
2. `first_moment_upper_bound` — |integral of Z(t)| <= C T^(1/2+eps)
3. `l1_lower_bound` — integral of |Z(t)| >= c T

Key files: `HardyZContradiction.lean` (BuildingBlocks structure),
`HardyInfiniteZeros.lean` (main theorem), `HardySetupInstance.lean`
(3 sorry fields), `Bridge/HardyCriticalLineWiring.lean` (conversion),
`HardyApproxFunctionalEq.lean` (connects partial sum mean square to
full Z(t) mean square — 0 sorries, bridges the diagonal bound to
`mean_square_lower_bound`).

## Sorry Inventory

Audited from `lake build` output (2026-01-31). Only imported files
produce build warnings; Development/ files are on disk but not imported.

| Location | Declarations | Files | Notes |
|----------|-------------|-------|-------|
| **Assumptions.lean** | 58 | 1 | Hypothesis instances for classical results not in Mathlib |
| **Aristotle/** | 11 | 6 | MeanSquare (3), PhragmenLindelof (3), ZeroCounting (2), PartialSummation (1), PerronContourIntegralsV2 (1), HardyZConjugation (1) |
| **Bridge/** | 4 | 2 | HardySetupInstance (3), HardyAssemblyAttempt (1) |
| **CoreLemmas/** | 1 | 1 | LandauLemma — analytic continuation identity |
| **Total (project)** | **74** | **10** | Main proof chain: 0 sorries |

Additionally on disk but not imported by the build:
- `Aristotle/_deprecated/`: 10 sorries across 3 files
- `Aristotle/ChebyshevTheta.lean`: 3 sorries (redefines psi/theta)
- `Development/`: 5 sorries across 3 files (HardyTheorem, ZeroFreeRegion, LittlewoodTheorem)

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

### Easy — Close Low-Hanging Sorries

Pick a sorry from `Aristotle/` files and check if current Mathlib can fill it:
- `PerronContourIntegralsV2.lean` (1 sorry) — Mathlib has `integral_boundary_rect_eq_zero_of_differentiableOn`
- `ContourInfrastructure.lean` — measure preimage lemmas
- `DiagonalIntegralBound.lean` — harmonic sum bounds

### Medium — Small Mathlib PRs

See [`docs/mathlib_pr_specs/`](docs/mathlib_pr_specs/) for specifications:
1. **Quantitative zero-free region** — most prerequisites exist in Mathlib
2. **Perron's formula** — high impact, unlocks explicit formula sorries

### Hard — Major Analytic Number Theory

- Zero counting infrastructure (Riemann-von Mangoldt with uniform constants)
- Hardy's theorem (approximate functional equation, mean value estimates)
- Phragmen-Lindelof convexity bounds

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
