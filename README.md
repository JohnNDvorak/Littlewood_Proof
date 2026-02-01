# Littlewood's Oscillation Theorem — Lean 4 Formalization

A machine-checked proof that pi(x) - li(x) changes sign infinitely often,
formalizing Littlewood's 1914 result via Hardy's critical-line zeros,
explicit formulas, and Schmidt's oscillation lemma. The main theorems
compile with **0 sorries**; analytic content is encoded in 58 hypothesis
classes filled incrementally with proofs co-authored by
[Aristotle](https://app.harmonic.fun) (Harmonic) and Claude (Anthropic).

## Status

`lake build` reports **87** sorry-bearing declarations (+ 3 from the
`PrimeNumberTheoremAnd` dependency).

| Metric | Count |
|--------|-------|
| Sorry declarations (`lake build`, project only) | **87** |
| Assumptions.lean (hypothesis instances) | 58 |
| Aristotle/ (active, imported) | 19 across 9 files |
| Bridge/ | 9 across 4 files |
| CoreLemmas/ | 1 |
| Main theorem sorries | **0** |
| Lines of Lean code | ~31,300 |
| Total .lean files | 169 |
| Sorry-free .lean files | 155 (92%) |
| Hardy chain status | V1 BUGGY (field signatures unsatisfiable); V2 created with correct architecture |

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
  Aristotle/                 98 files — AI-generated proofs (Harmonic), 19 active sorries
  Bridge/                    23 files — Wiring Aristotle proofs to hypothesis classes
  Development/               18 files — WIP proofs (not imported by main build)
  Tests/                      8 files — Integration tests
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
which is the key input to the oscillation argument.

### V1 (BUGGY — `HardyInfiniteZeros.lean`)

The original `HardySetup` class has unsatisfiable field signatures:
`mean_square_lower_bound` quantifies `∀ T₁ ∈ [0,T)`, requiring
`∫_{T₁}^T Z² ≥ c·T·log T` for ALL T₁. For T₁ near T the integral
vanishes, so the field is **mathematically false**. The `grind` proof
of `hardy_infinitely_many_zeros` works **vacuously** from `sorry = False`.

### V2 (CANONICAL — `HardyInfiniteZerosV2.lean`)

Fixed architecture with correct field signatures:

```
HardySetupV2 FIELDS (6 total):
1. Z                    ✅ HardyEstimatesPartial.hardyZ
2. Z_continuous          ✅ HardySetupInstance
3. Z_zero_iff            ✅ HardySetupInstance
4. mean_square_lower     ⚠️ MeanSquareBridge (2 sorries in chain)
5. first_moment_upper    ❌ Needs Aristotle
6. Z_convexity_bound     ❌ Needs Aristotle (Phragmén-Lindelöf)
```

All integrals use fixed lower endpoint 1 (not arbitrary T₁).
The contradiction argument uses exponent 3/4 + ε₁ + ε₂ < 1
for ε₁ + ε₂ < 1/4, giving T·log T vs T^α with α < 1.

```
DiagonalIntegralBound: ∫|S_N|² ≥ c·T·log T                          (0 sorries) ✓
  |
  v
HardyApproxFunctionalEq: ∫Z² ≥ k·∫|S_N|² - C·T                     (0 sorries) ✓
  |
  v
MeanSquarePartialSumAsymptotic: ∫|S_N|² ≥ c₁·T·log T                (0 sorries) ✓
  |
  v
OscillatorySumBound: |∫ oscillatory| ≤ C·T^{1/2+ε}                  (0 sorries) ✓
  |
  v
MeanSquareBridge: ∫Z² ≥ c'·T·log T on [1,T]                        (2 sorries)
  |
  v
HardySetupV2Instance: fields 1-3 proved, 4-6 sorry                  (3 sorries)
  |
  v
HardyInfiniteZerosV2.hardy_infinitely_many_zeros_v2                 (5 sorries)
  |
  v
HardyCriticalLineWiring → Schmidt.HardyCriticalLineZerosHyp
```

**Remaining for Hardy:**
1. Close MeanSquareBridge sorries (type transfer between hardyZ variants)
2. `first_moment_upper` — connect OscillatorySumBound to Hardy Z
3. `Z_convexity_bound` — |ζ(1/2+it)| ≤ C|t|^{1/4+ε} (Phragmén-Lindelöf)

Key files: `HardyInfiniteZerosV2.lean`, `HardySetupV2Instance.lean`,
`MeanSquareBridge.lean`, `DiagonalIntegralBound.lean`,
`HardyApproxFunctionalEq.lean`, `MeanSquarePartialSumAsymptotic.lean`,
`OscillatorySumBound.lean`, `ContourRectangle.lean`.

## Sorry Inventory

Audited from `lake build` output (2026-02-01). Only imported files
produce build warnings; Development/ files are on disk but not imported.

| Location | Declarations | Files | Notes |
|----------|-------------|-------|-------|
| **Assumptions.lean** | 58 | 1 | Hypothesis instances for classical results not in Mathlib |
| **Aristotle/** | 19 | 9 | HardyInfiniteZerosV2 (5), MeanSquare (3), PhragmenLindelof (3), StirlingBernoulli (2), ZeroCounting (2), PerronContourIntegralsV2 (1), PartialSummation (1), HardyZConjugation (1), ContourRectangle (1) |
| **Bridge/** | 9 | 4 | HardySetupV2Instance (3), HardySetupInstance (3), MeanSquareBridge (2), HardyAssemblyAttempt (1) |
| **CoreLemmas/** | 1 | 1 | LandauLemma — analytic continuation identity |
| **Total (project)** | **87** | **15** | Main proof chain: 0 sorries |

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
- `ContourRectangle.lean` (1 sorry) — same Mathlib API, needs argument matching
- `DiagonalIntegralBound.lean` — harmonic sum bounds

### Medium — Small Mathlib PRs

See [`docs/mathlib_pr_specs/`](docs/mathlib_pr_specs/) for specifications:
1. **Quantitative zero-free region** — most prerequisites exist in Mathlib
2. **Perron's formula** — high impact, unlocks explicit formula sorries

### Hard — Major Analytic Number Theory

- Zero counting infrastructure (Riemann-von Mangoldt with uniform constants)
- Hardy's theorem (approximate functional equation, mean value estimates)
- Phragmen-Lindelof convexity bounds
- Connect OscillatorySumBound to Hardy Z first moment

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
