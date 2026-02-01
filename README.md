# Littlewood's Oscillation Theorem — Lean 4 Formalization

A machine-checked proof that pi(x) - li(x) changes sign infinitely often,
formalizing Littlewood's 1914 result via Hardy's critical-line zeros,
explicit formulas, and Schmidt's oscillation lemma. The main theorems
compile with **0 sorries**; analytic content is encoded in 58 hypothesis
classes filled incrementally with proofs co-authored by
[Aristotle](https://app.harmonic.fun) (Harmonic) and Claude (Anthropic).

## Status

`lake build` reports **90** sorry-bearing declarations (+ 3 from the
`PrimeNumberTheoremAnd` dependency).

| Metric | Count |
|--------|-------|
| Sorry declarations (`lake build`, project only) | **90** |
| Assumptions.lean (hypothesis instances) | 58 |
| Aristotle/ (active, imported) | 28 across 12 files |
| Bridge/ | 4 across 2 files |
| CoreLemmas/ | 1 |
| Main theorem sorries | **0** |
| Lines of Lean code | ~32,100 |
| Total .lean files | 172 |
| Sorry-free .lean files | 157 (91%) |
| Hardy chain status | V2 canonical (V1 deprecated — unsatisfiable field signatures) |

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
  Aristotle/                101 files — AI-generated proofs (Harmonic), 28 active sorries
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
4. mean_square_lower     ⚠️ MeanSquareBridge (1 sorry in chain)
5. first_moment_upper    ❌ Needs Aristotle
6. Z_convexity_bound     ❌ Needs Aristotle (Phragmén-Lindelöf)
```

All integrals use fixed lower endpoint 1 (not arbitrary T₁).
The contradiction argument uses exponent 3/4 + ε₁ + ε₂ < 1
for ε₁ + ε₂ < 1/4, giving T·log T vs T^α with α < 1.

HardyInfiniteZerosV2 proof steps:
- `constant_sign_of_finite` — ✅ fully proved (IVT-based)
- `abs_integral_eq_of_pos` — ✅ fully proved (constant sign → |∫Z| = ∫|Z|)
- `mean_square_decomp` — sorry (∂volume elaboration mismatch)
- `mean_square_le_sup_times_l1` — sorry (iSup BddAbove on Ioc)
- `hardy_infinitely_many_zeros_v2` — sorry (main contradiction)

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
MeanSquareBridge: ∫Z² ≥ c'·T·log T on [1,T]                        (1 sorry)
  |
  v
HardySetupV2Instance: fields 1-3 proved, 4-6 sorry                  (3 sorries)
  |
  v
HardyInfiniteZerosV2.hardy_infinitely_many_zeros_v2                 (3 sorries)
  |
  v
HardyCriticalLineWiring → Schmidt.HardyCriticalLineZerosHyp
```

**Remaining for Hardy:**
1. Close MeanSquareBridge sorry (type transfer between hardyZ variants)
2. `first_moment_upper` — connect OscillatorySumBound to Hardy Z
3. `Z_convexity_bound` — |ζ(1/2+it)| ≤ C|t|^{1/4+ε} (Phragmén-Lindelöf)

## Sorry Inventory

Audited from `lake build` output (2026-02-01). Only imported files
produce build warnings; Development/ files are on disk but not imported.

| Location | Declarations | Files | Notes |
|----------|-------------|-------|-------|
| **Assumptions.lean** | 58 | 1 | Hypothesis instances for classical results not in Mathlib |
| **Aristotle/** | 28 | 12 | HardyInfiniteZerosV2 (3), ZeroFreeRegionV3 (6), MeanSquare (3), CauchyGoursatRectangle (3), PhragmenLindelof (3), ZetaBoundsV2 (3), ZeroCounting (2), PerronContourIntegralsV2 (1), PartialSummation (1), HardyZConjugation (1), ContourRectangle (1) |
| **Bridge/** | 4 | 2 | HardySetupV2Instance (3), MeanSquareBridge (1) |
| **CoreLemmas/** | 1 | 1 | LandauLemma — analytic continuation identity |
| **Total (project)** | **90** | **15** | Main proof chain: 0 sorries |

Additionally on disk but not imported by the build:
- `Aristotle/_deprecated/`: 10 sorries across 3 files
- `Aristotle/ChebyshevTheta.lean`: 3 sorries (redefines psi/theta)
- `Aristotle/HardyInfiniteZeros.lean`: V1 deprecated (unsatisfiable field signatures)
- `Bridge/HardyAssemblyAttempt.lean`: V1 exploration file (superseded by V2)
- `Development/`: 5 sorries across 3 files (HardyTheorem, ZeroFreeRegion, LittlewoodTheorem)

## New in This Version

### Aristotle Integration (3 new files)

**ZetaBoundsV2.lean** — Zeta function bounds and functional equation:
- `zeta_bound_re_ge_one`: ‖ζ(s)‖ ≤ Re(s)/(Re(s)-1) for Re(s) > 1
- `functional_equation`: ζ(s) = χ(s)·ζ(1-s) via reflection formula
- `sin_bound_aux`: |sin(πs/2)| ≤ exp(π|Im s|/2) in critical strip
- `sinh_lower_bound`: |sinh(πt)| ≥ exp(π|t|)/4 for |t| ≥ 2
- `gamma_abs_imag`: |Γ(it)| = |Γ(1-it)|/|t|
- `gamma_sq_bound_zero`: |Γ(1-it)|² ≤ 4π|t|exp(-π|t|)

**CauchyGoursatRectangle.lean** — Cauchy-Goursat theorem for rectangles:
- `rectBoundary`: parametrized rectangle contour over [0,4]
- `cauchy_goursat_rectangle_segments`: ∮f = 0 (segment form)
- `rectIntegral_eq_sum_segments`: contour integral = sum of segments
- `cauchy_goursat_rectangle`: main theorem, via Mathlib's `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`

**ZeroFreeRegionV3.lean** — Zero-free region infrastructure:
- `three_four_one`: 3+4cosθ+cos2θ ≥ 0 (fully proved)
- `zeta_ne_zero_on_one_line`: ζ(1+it) ≠ 0 for t ≠ 0 (via `riemannZeta_ne_zero_of_one_le_re`)
- `zeta_ne_zero_re_eq_one`: same for |t| ≥ 1
- `re_log_deriv_zeta_eq_sum`: Re(-ζ'/ζ(s)) = Σ Λ(n)n^{-σ}cos(t log n)
- `summable_vonMangoldt_mul_cos`: summability of the Dirichlet series
- `norm_zeta_log_deriv_ineq`: 3·Re(-ζ'/ζ(σ)) + 4·Re(-ζ'/ζ(σ+it)) + Re(-ζ'/ζ(σ+2it)) ≥ 0
- `zetaResidueFunction`: (s-1)ζ(s) removable singularity
- `zeta_log_deriv_bound_near_one`: -Re(ζ'/ζ(σ)) ≤ 1/(σ-1) + C

### HardyInfiniteZerosV2 Proof Progress

Proved 2 of 5 lemmas:
- `constant_sign_of_finite`: Finite zeros → constant sign via IVT
- `abs_integral_eq_of_pos`: Constant positive sign → |∫Z| = ∫|Z|

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
- `CauchyGoursatRectangle.lean` (3 sorries) — continuousOn/deriv matching for segment integrals
- `ZetaBoundsV2.lean` (3 sorries) — zeta bound, functional equation, Gamma bound

### Medium — Small Mathlib PRs

See [`docs/mathlib_pr_specs/`](docs/mathlib_pr_specs/) for specifications:
1. **Quantitative zero-free region** — most prerequisites exist in Mathlib
2. **Perron's formula** — high impact, unlocks explicit formula sorries

### Hard — Major Analytic Number Theory

- Zero counting infrastructure (Riemann-von Mangoldt with uniform constants)
- Hardy's theorem (approximate functional equation, mean value estimates)
- Phragmen-Lindelof convexity bounds
- Connect OscillatorySumBound to Hardy Z first moment
- Zero-free region: close `analyticAt_zetaResidueFunction` and `log_deriv_residue_bounded_near_one`

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
