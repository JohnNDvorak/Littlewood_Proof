# Littlewood's Oscillation Theorem — Lean 4 Formalization

A machine-checked proof that pi(x) - li(x) changes sign infinitely often,
formalizing Littlewood's 1914 result via Hardy's critical-line zeros,
explicit formulas, and Schmidt's oscillation lemma. The main theorems
compile with **0 sorries**; analytic content is encoded in 58 hypothesis
classes filled incrementally with proofs co-authored by
[Aristotle](https://app.harmonic.fun) (Harmonic) and Claude (Anthropic).

## Status

| Metric | Count |
|--------|-------|
| Total sorry declarations | **~102** |
| Assumptions.lean (hypothesis instances) | 61 |
| Aristotle active sorries | 15 |
| Bridge sorries | 6 |
| Development sorries | 5 |
| CoreLemmas sorries | 1 |
| Sorry-free files | ~85% of codebase |
| Main theorem sorries | **0** |
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
3. **`Assumptions.lean`** provides `sorry`-backed instances for all 58 classes
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
  Basic/                     3 files — Omega-notation, Chebyshev psi/theta, li(x)
  ZetaZeros/                 3 files — Zero counting N(T), density, sup real part
  ExplicitFormulas/          3 files — Explicit formula for psi, smoothed, conversions
  CoreLemmas/                3 files — Landau lemma (1 sorry), Dirichlet approx, weighted avg
  Oscillation/               2 files — Schmidt oscillation theorem
  Main/                      2 files — LittlewoodPsi, LittlewoodPi (0 sorries)
  Mertens/                   1 file  — Mertens' first theorem
  Assumptions.lean           1 file  — 58 hypothesis instances (all sorry)
  Aristotle/                90 files — AI-generated proofs (Harmonic), ~15 active sorries
  Bridge/                   19 files — Wiring Aristotle proofs to hypothesis classes
  Development/               3 files — WIP proofs (5 sorries)
  Tests/                     2 files — Integration tests
  Documentation/            42 files — Status tracking, prompt logs
docs/
  CurrentStatus.md           Canonical status dashboard (updated each push)
  blocking_analysis.md       Gap analysis
  hypothesis_*.md            Hypothesis tracking and mapping
  lemma_index.md             Lemma inventory
  sorry_analysis/            Detailed sorry audits
  mathlib_pr_specs/          Specifications for needed Mathlib PRs
  roadmap.md                 Development roadmap
  _archive/                  Historical milestones and old status files
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
(3 sorry fields), `Bridge/HardyCriticalLineWiring.lean` (conversion).

## Sorry Inventory

| Location | Sorries | Notes |
|----------|---------|-------|
| **Assumptions.lean** | 61 | Hypothesis instances for classical results not in Mathlib |
| **Aristotle/** | 15 | Across 7 files (MeanSquare, PhragmenLindelof, ZeroCounting, PartialSummation, PerronContourIntegralsV2, HardyZConjugation, ChebyshevTheta) |
| **Bridge/** | 6 | Hardy setup (3), building blocks (2), assembly (1) |
| **Development/** | 5 | LittlewoodTheorem (1), HardyTheorem (2), ZeroFreeRegion (2) |
| **CoreLemmas/** | 1 | Landau lemma analytic continuation |
| **Total** | **~102** | Main proof chain: 0 sorries |

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
