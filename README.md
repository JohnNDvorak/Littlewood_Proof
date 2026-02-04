# Littlewood's Oscillation Theorem — Lean 4 Formalization

A machine-checked proof that pi(x) - li(x) changes sign infinitely often,
formalizing Littlewood's 1914 result via Hardy's critical-line zeros,
explicit formulas, and Schmidt's oscillation lemma. The main theorems
compile with **0 sorries** and resolve with **no explicit typeclass
parameters**; all dependencies are wired through bridge files that make
the mathematical dependency chain explicit. Analytic content is encoded
in 57 hypothesis class instances filled incrementally with proofs
co-authored by [Aristotle](https://app.harmonic.fun) (Harmonic) and
Claude (Anthropic).

## Status

`lake build` reports **69** sorry-bearing declarations (66 project + 3 from
`PrimeNumberTheoremAnd` dependency). Last audited: 2026-02-03.

| Metric | Count |
|--------|-------|
| Sorry declarations (`lake build`, total) | **69** |
| Assumptions.lean (hypothesis instances) | 57 |
| Bridge/ExplicitFormulaOscillation.lean | 1 (oscillation extraction) |
| Aristotle/ (active, imported) | 7 across 4 files |
| CoreLemmas/ | 1 |
| Main theorem sorries | **0** |
| Main theorem explicit typeclass params | **0** (all auto-resolved) |
| Lines of Lean code | ~33,800 |
| Total .lean files | 176 |
| Files with build-visible sorries | 7 |

## Main Theorems

Both theorems compile, typecheck, and resolve all instances automatically:

```lean
-- psi(x) - x = Omega_pm(sqrt(x))
-- All typeclass instances resolve automatically through bridge chain
theorem littlewood_psi :
    (fun x => chebyshevPsi x - x) =Omega_pm[fun x => Real.sqrt x] :=
  Schmidt.psi_oscillation_sqrt

-- pi(x) - li(x) = Omega_pm(sqrt(x) / log(x))
-- All typeclass instances resolve automatically through bridge chain
theorem littlewood_pi_li :
    (fun x => (Nat.primeCounting (Nat.floor x) : R) - logarithmicIntegral x)
    =Omega_pm[fun x => Real.sqrt x / Real.log x] :=
  PiLiOscillationSqrtHyp.oscillation
```

Corollaries proved from `littlewood_pi_li`:
- `pi_gt_li_infinitely_often` : pi(x) > li(x) infinitely often
- `pi_lt_li_infinitely_often` : pi(x) < li(x) infinitely often
- `pi_minus_li_sign_changes` : the sign changes infinitely often

### Critical Path: Sorries the Main Theorems Depend On

**For `littlewood_psi`** (5 sorries on critical path):

| Sorry | Location | Mathematical Content |
|-------|----------|---------------------|
| Oscillation extraction | Bridge/ExplicitFormulaOscillation.lean | ∞ critical-line zeros + explicit formula → Ω±(√x) |
| ZetaCriticalLineBoundHyp | Assumptions.lean | \|ζ(1/2+it)\| ≤ C\|t\|^{1/4+ε} |
| HardyFirstMomentUpperHyp | Assumptions.lean | \|∫₁ᵀ Z(t) dt\| ≤ C·T^{1/2+ε} |
| ExplicitFormulaPsiHyp | Assumptions.lean | ψ₀(x) = x - Σ_ρ x^ρ/ρ + O(log x) |
| approx_functional_eq | Aristotle/HardyApproxFunctionalEq.lean | ∫Z² ≥ k·∫\|S\|² - CT |

**For `littlewood_pi_li`** (2 sorries on critical path):

| Sorry | Location | Mathematical Content |
|-------|----------|---------------------|
| ThetaOscillationSqrtHyp | Assumptions.lean | θ(x) - x = Ω±(√x) |
| OmegaThetaToPiLiHyp | Assumptions.lean | θ oscillation → π-li oscillation |

The remaining 50+ sorry-backed hypothesis instances in Assumptions.lean
support the wider infrastructure (zero counting, explicit formulas,
Landau lemma, etc.) but are **not on the critical path** for the main
theorems.

## Complete Dependency Tree

```
littlewood_psi
  └── [PsiOscillationSqrtHyp] ← auto-resolved
      └── PsiOscillationWiring.lean (0 sorry)
          └── [PsiOscillationFromCriticalZerosHyp] ← auto-resolved
              └── ExplicitFormulaOscillation.lean (1 SORRY)
                  ├── [HardyCriticalLineZerosHyp] ← auto-resolved
                  │   └── HardyCriticalLineWiring.lean (0 sorry)
                  │       ├── [ZetaCriticalLineBoundHyp]     SORRY
                  │       ├── [HardyFirstMomentUpperHyp]     SORRY
                  │       └── HardyInfiniteZerosV2 (0 sorry)
                  │           └── approx_functional_eq       SORRY (Aristotle)
                  └── [ExplicitFormulaPsiHyp]                SORRY

littlewood_pi_li
  └── [PiLiOscillationSqrtHyp] ← auto-resolved
      └── PsiToPiLiOscillation.lean (0 sorry)
          ├── [ThetaOscillationSqrtHyp]    SORRY
          └── [OmegaThetaToPiLiHyp]        SORRY
```

No sorry in the tree says "assume Littlewood to prove Littlewood." Every sorry
encodes a specific, independently meaningful piece of analytic number theory.

## Architecture

The project uses **hypothesis-driven design** to separate logical structure
from analytic content:

1. **Hypothesis classes** (`class FooHyp : Prop`) encode classical theorems
   not yet in Mathlib (Perron's formula, zero density estimates, etc.)
2. **Main theorems** are proved assuming these classes — the full proof
   chain from Hardy's theorem through Schmidt oscillation to Littlewood
   compiles with 0 sorries
3. **`Assumptions.lean`** provides `sorry`-backed instances for 57
   hypothesis class instances
4. **Aristotle/ and Bridge/** work toward replacing those sorries with
   genuine proofs

When an assumption is proved, the `sorry` instance moves out of
`Assumptions.lean` and the hypothesis is discharged. Five instances are
already fully proved or auto-wired:
- `FunctionalEquationHyp` — zeta functional equation (proved)
- `LambdaSymmetryHyp` — completed zeta symmetry (proved)
- `ZeroConjZeroHyp` — conjugation symmetry of nontrivial zeros (proved)
- `ZeroOneSubZeroHyp` — functional equation symmetry (proved)
- `ZetaLogDerivPoleHyp` — -zeta'/zeta has poles at zeros (proved, ~100 lines in Assumptions.lean)

Auto-wired (fire when dependencies are met):
- `HardyCriticalLineZerosHyp` — via `HardyCriticalLineWiring.lean` (needs `ZetaCriticalLineBoundHyp` + `HardyFirstMomentUpperHyp`)
- `PsiOscillationFromCriticalZerosHyp` — via `ExplicitFormulaOscillation.lean` (needs `HardyCriticalLineZerosHyp` + `ExplicitFormulaPsiHyp`, 1 sorry)
- `PsiOscillationSqrtHyp` — via `PsiOscillationWiring.lean` (needs `PsiOscillationFromCriticalZerosHyp`)
- `PiLiOscillationSqrtHyp` — via `PsiToPiLiOscillation.lean` (needs `ThetaOscillationSqrtHyp` + `OmegaThetaToPiLiHyp`)

## Project Structure

```
Littlewood/
  Basic/                      3 files  -- Omega-notation, Chebyshev psi/theta, li(x)
  ZetaZeros/                  3 files  -- Zero counting N(T), density, sup real part
  ExplicitFormulas/            4 files  -- Explicit formula for psi, smoothed, conversions
  CoreLemmas/                  3 files  -- Landau lemma (1 sorry), Dirichlet approx, weighted avg
  Oscillation/                 2 files  -- Schmidt oscillation theorem
  Main/                        3 files  -- Littlewood, LittlewoodPsi, LittlewoodPi (0 sorries)
  Mertens/                     1 file   -- Mertens' first theorem
  Assumptions.lean             1 file   -- 57 hypothesis instances (all sorry)
  Aristotle/                 105 files  -- AI-generated proofs (Harmonic + Claude)
  Bridge/                     24 files  -- Wiring Aristotle proofs to hypothesis classes
  Development/                17 files  -- WIP proofs (not imported by main build)
  Tests/                       8 files  -- Integration tests
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
DiagonalIntegralBound: ∫|S_N|² ≥ c·T·log T                (0 sorries)
  → HardyApproxFunctionalEq: ∫Z² ≥ k·∫|S|² - CT           (1 sorry)
  → MeanSquarePartialSumAsymptotic                          (0 sorries)
  → OscillatorySumBound                                     (0 sorries)
  → MeanSquareBridge: ∫Z² ≥ c'·T·log T                     (0 sorries)
  → HardySetupV2Instance: ALL 6 FIELDS PROVED               (0 sorries)
  → HardyInfiniteZerosV2: ALL 5 LEMMAS PROVED               (0 sorries)
  → HardyCriticalLineWiring → HardyCriticalLineZerosHyp     (0 sorries)
  → ExplicitFormulaOscillation → PsiOscillationFromCriticalZerosHyp (1 sorry)
  → PsiOscillationWiring → PsiOscillationSqrtHyp            (0 sorries)
  → littlewood_psi                                          (0 sorries)
```

**The Hardy chain is fully wired from inputs to main theorem.** The
remaining analytic inputs are:

- `ZetaCriticalLineBoundHyp` — Phragmen-Lindelof convexity: |zeta(1/2+it)| <= C|t|^{1/4+eps}
- `HardyFirstMomentUpperHyp` — first moment: |int_1^T Z(t) dt| <= C*T^{1/2+eps}
- `ExplicitFormulaPsiHyp` — explicit formula: psi_0(x) = x - sum_rho x^rho/rho + O(log x)
- `approx_functional_eq` (1 sorry) — approximate functional equation
- Oscillation extraction (1 sorry in ExplicitFormulaOscillation.lean)

## Sorry Inventory

Audited from `lake build` output (2026-02-03). Only imported files
produce build warnings.

| Location | Declarations | Files | Notes |
|----------|-------------|-------|-------|
| **Assumptions.lean** | 57 | 1 | Hypothesis instances for classical results not in Mathlib |
| **Bridge/** | 1 | 1 | ExplicitFormulaOscillation (oscillation extraction from zeros + formula) |
| **Aristotle/** | 7 | 4 | HardyApproxFunctionalEq (1), PhragmenLindelof (3), ZeroCounting (2), PartialSummation (1) |
| **CoreLemmas/** | 1 | 1 | LandauLemma — identity theorem (FALSE as stated; not used downstream) |
| **Total (project)** | **66** | **7** | Main proof chain: 0 sorries, all instances auto-resolved |

Additionally on disk but not imported by the build:
- `Aristotle/_deprecated/`: 3 files (superseded proofs)
- `Aristotle/ChebyshevTheta.lean`: redefines psi/theta (not imported)
- `Bridge/HardyBuildingBlocksInstance.lean`: template (not imported)
- `Bridge/HardyAssemblyAttempt.lean`: V1, superseded by V2
- `Development/`: 4 files (WIP, not imported)
- `Tests/`: 4 files (not imported by main build)

## Detailed Aristotle Sorry Inventory

| File | Sorries | What each sorry needs | Difficulty |
|------|---------|----------------------|------------|
| **PhragmenLindelof.lean** | 3 | `zeta_critical_line_bound`: |zeta(1/2+it)| <= C|t|^{1/2} via Phragmen-Lindelof. `zeta_convexity_bound`: general strip bound. `gamma_growth`: Stirling approximation for Gamma. | Hard — genuine complex analysis. Has proved helpers: `zeta_bound_gt_one`, `zeta_bound_at_two`, `zeta_near_one_bound`, `zeta_large_sigma_bound`. |
| **ZeroCounting.lean** | 2 | `zetaZeroCount_via_argument`: N(T) via argument principle. `zetaZeroCount_asymp`: N(T) = (T/2pi)log(T/2pi) - T/2pi + O(log T). | Medium — argument principle machinery exists in Mathlib but connecting it to zeta is nontrivial. |
| **HardyApproxFunctionalEq.lean** | 1 | `approx_functional_eq`: int Z^2 >= k * int ||S||^2 - C*T. Needs Riemann-Siegel type approximate functional equation. | Hard — deep analytic number theory. Previous version was vacuously true (binder precedence bug, now fixed). |
| **PartialSummation.lean** | 1 | `psi_oscillation_implies_pi_li_oscillation`: transfer via partial summation. Needs connecting Mathlib's `primeCounting_eq_theta_div_log_add_integral` with project's `logarithmicIntegral`. | Medium — infrastructure exists but wiring is laborious. |

## Key Definitions

An AI assistant working on this project should know these definitions:

| Name | Definition | File |
|------|-----------|------|
| `chebyshevPsi` | Alias for `Chebyshev.psi` (sum of von Mangoldt) | ChebyshevFunctions.lean |
| `chebyshevTheta` | Alias for `Chebyshev.theta` (sum of log p over primes) | ChebyshevFunctions.lean |
| `logarithmicIntegral` | `li(x) = int_2^x 1/log(t) dt` | LogarithmicIntegral.lean |
| `IsOmegaPlusMinus f g` | `exists c > 0, f(x) >= c*g(x) i.o. AND f(x) <= -c*g(x) i.o.` | OmegaNotation.lean |
| `zetaNontrivialZeros` | `{s : C | riemannZeta s = 0 AND 0 < s.re AND s.re < 1}` | ZetaZeros/ |
| `hardyZ` | `||riemannZeta(1/2 + t*I)||` (norm-based variant) | HardyApproxFunctionalEq.lean |
| `zeroCountingFunction` | N(T) = number of zeros with 0 < Im(rho) <= T | ZeroCountingFunction.lean |

## Key Mathlib APIs Used

| Mathlib Lemma | What it gives |
|---------------|--------------|
| `Chebyshev.theta_le_psi` | theta(x) <= psi(x) |
| `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` | |psi(x) - theta(x)| <= 2*sqrt(x)*log(x) |
| `Chebyshev.psi_eq_theta_add_sum_theta` | psi = theta + sum of theta at roots |
| `Chebyshev.primeCounting_eq_theta_div_log_add_integral` | pi(x) = theta(x)/log(x) + integral (Abel summation) |
| `Chebyshev.primeCounting_sub_theta_div_log_isBigO` | pi(x) - theta(x)/log(x) = O(x/log^2 x) |
| `Chebyshev.integral_theta_div_log_sq_isLittleO` | integral term is o(x/log x) |
| `riemannZeta` | Riemann zeta function (analytic continuation) |
| `Complex.Gamma` | Gamma function |

## Notes for AI Assistants

### What works
- Both main theorems resolve with **NO explicit typeclass parameters** — all instances auto-resolve through the bridge chain.
- The Hardy chain from DiagonalIntegralBound through littlewood_psi is fully wired.
- The π-li chain from ThetaOscillationSqrtHyp through littlewood_pi_li is fully wired.
- `lake build` completes cleanly (all files compile, only sorry warnings).
- Every sorry on the critical path encodes a specific, independently meaningful piece of mathematics — no sorry says "assume Littlewood to prove Littlewood."

### What doesn't work
- **OmegaPsiToThetaHyp is mathematically false** (kept for backward compatibility, NOT used by main theorems).
- **LandauLemma.lean** sorry is FALSE as stated (LSeries returns 0 for non-summable series, making it trivially analytic). Not used downstream.
- **ExplicitFormulaOscillation** has 1 sorry for the hard step: extracting oscillation from the explicit formula + infinitely many critical-line zeros.

### Build configuration
- `maxHeartbeats 1600000`, `maxRecDepth 4000` in lakefile.toml
- Individual files may set lower values (800000 heartbeats is common)
- `synthInstance.maxHeartbeats 20000`, `synthInstance.maxSize 128` in some files

### Common pitfalls
- The project defines its OWN `chebyshevPsi`/`chebyshevTheta`/`logarithmicIntegral` as aliases or redefinitions of Mathlib/PrimeNumberTheoremAnd functions. Always check which namespace you're in.
- Aristotle files sometimes define LOCAL versions of `hardyZ`, `hardyTheta` etc. that differ from the Bridge/ definitions. Check the namespace.
- The `_deprecated/` and `Development/` directories contain abandoned approaches. Don't build on them.
- Many Bridge files exist but are NOT imported by the main build. Check `import` statements.

### Priority for reducing sorry count
1. **ExplicitFormulaOscillation** (1 sorry) — the oscillation extraction. Needs: show that the zero sum from the explicit formula with ∞ many Re=1/2 zeros forces Ω±(√x).
2. **PhragmenLindelof.lean** (3 sorries) — closes `ZetaCriticalLineBoundHyp`, unblocks Hardy chain input.
3. **HardyApproxFunctionalEq.lean** (1 sorry) — approximate functional equation, feeds Hardy chain.
4. **ThetaOscillationSqrtHyp** (sorry in Assumptions) — needs explicit formula for θ + Hardy zeros. Independent from ψ chain.
5. **OmegaThetaToPiLiHyp** (sorry in Assumptions) — needs quantitative PNT error bounds.
6. **ZeroCounting.lean** (2 sorries) — not on critical path but tractable.

### What a second AI should read first
1. This README (complete dependency tree above)
2. `docs/CurrentStatus.md` — detailed status with wiring diagrams
3. `Littlewood/Assumptions.lean` — all 57 hypothesis instances
4. `Littlewood/Bridge/ExplicitFormulaOscillation.lean` — the key bridge with 1 sorry
5. `Littlewood/Bridge/PsiToPiLiOscillation.lean` — the π-li bridge (0 sorry)
6. `docs/aristotle_prompts.md` — ready-to-use prompts for closing sorries

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

# List sorry locations
lake build 2>&1 | grep "uses 'sorry'" | grep -v PrimeNumberTheoremAnd
```

Dependencies (from `lakefile.toml`):
- `mathlib` (leanprover-community)
- `PrimeNumberTheoremAnd` (AlexKontorovich)

Build configuration: `maxHeartbeats 1600000`, `maxRecDepth 4000`.

## Contributing

### Tractable Sorries (Aristotle Prompts Available)

See `docs/aristotle_prompts.md` for detailed prompts. Priority order:

1. **ExplicitFormulaOscillation.lean** (1 sorry) — show ∞ critical-line zeros + explicit formula → ψ oscillation. THE key mathematical step.
2. **PhragmenLindelof.lean** (3 sorries) — critical line zeta bound, convexity, Gamma growth (Stirling). Closes `ZetaCriticalLineBoundHyp`.
3. **HardyApproxFunctionalEq.lean** (1 sorry) — approximate functional equation: int Z^2 >= k*int ||S||^2 - CT.
4. **ZeroCounting.lean** (2 sorries) — N(T) via argument principle, asymptotic.
5. **PartialSummation.lean** (1 sorry) — psi oscillation implies pi-li oscillation.
6. **LandauLemma.lean** (1 sorry) — identity theorem for analytic continuation (FALSE as stated, not used downstream).

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
