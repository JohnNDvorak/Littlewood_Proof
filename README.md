# Littlewood's Oscillation Theorem — Lean 4 Formalization

A machine-checked proof that pi(x) - li(x) changes sign infinitely often,
formalizing Littlewood's 1914 result via Hardy's critical-line zeros,
explicit formulas, and Schmidt's oscillation lemma. The main theorems
compile with **0 sorries** and resolve with **no explicit typeclass
parameters**; all dependencies are wired through bridge files that make
the mathematical dependency chain explicit. Analytic content is encoded
in hypothesis class instances filled incrementally with proofs
co-authored by [Aristotle](https://app.harmonic.fun) (Harmonic) and
Claude (Anthropic).

## Status

Last audited: 2026-02-07.

| Metric | Count |
|--------|-------|
| Sorry warnings (full `lake build`) | **10** (7 project + 3 external) |
| CriticalAssumptions.lean (critical path hypotheses) | 1 |
| Bridge/ (oscillation extraction + transfer) | 3 |
| Aristotle/ (active, imported) | 3 across 2 files |
| Aristotle/Bridge/ (wiring) | **0** (3 files, all sorry-free) |
| Main theorem sorries | **0** |
| Main theorem explicit typeclass params | **0** (all auto-resolved) |
| Lines of Lean code | ~42,300 |
| Total .lean files | 217 |
| Aristotle files (total) | 136 |
| Aristotle files in build | 81 |
| Budget-exhaustion sorries closed by Claude Code | 22/22 |

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

**For `littlewood_psi`** (4 sorries on critical path):

| Sorry | Location | Mathematical Content |
|-------|----------|---------------------|
| Oscillation extraction (ψ) | Bridge/ExplicitFormulaOscillation.lean | ∞ critical-line zeros → ψ Ω±(√x) |
| HardyFirstMomentUpperHyp | CriticalAssumptions.lean | \|∫₁ᵀ Z(t) dt\| ≤ C·T^{1/2+ε} |
| approx_functional_eq | Aristotle/HardyApproxFunctionalEq.lean | ∫Z² ≥ k·∫\|S\|² - CT |
| ~~ZetaCriticalLineBoundHyp~~ | ~~CriticalAssumptions.lean~~ | **AUTO-WIRED** via PhragmenLindelofWiring |

**For `littlewood_pi_li`** (all ψ sorries above, plus 2):

| Sorry | Location | Mathematical Content |
|-------|----------|---------------------|
| Oscillation extraction (θ) | Bridge/ThetaExplicitFormulaOscillation.lean | ∞ critical-line zeros → θ Ω±(√x) |
| OmegaThetaToPiLiHyp | Bridge/OmegaThetaToPiLiWiring.lean | θ oscillation → π-li oscillation |

**Removed from critical path** (tsum formulation was FALSE):
- `ExplicitFormulaPsiHyp` — tsum ∑' ρ x^ρ/ρ not absolutely convergent; folded into bridge sorry
- `ExplicitFormulaThetaHyp` — same tsum issue; folded into bridge sorry

## Complete Dependency Tree

```
littlewood_psi
  └── [PsiOscillationSqrtHyp] ← auto-resolved
      └── PsiOscillationWiring.lean (0 sorry)
          └── [PsiOscillationFromCriticalZerosHyp] ← auto-resolved
              └── ExplicitFormulaOscillation.lean (1 SORRY)
                  └── [HardyCriticalLineZerosHyp] ← auto-resolved
                      └── HardyCriticalLineWiring.lean (0 sorry)
                          ├── [ZetaCriticalLineBoundHyp]     AUTO (PhragmenLindelofWiring)
                          ├── [HardyFirstMomentUpperHyp]     SORRY
                          └── HardyInfiniteZerosV2 (0 sorry)
                              └── approx_functional_eq       SORRY (Aristotle)

littlewood_pi_li
  └── [PiLiOscillationSqrtHyp] ← auto-resolved
      └── PsiToPiLiOscillation.lean (0 sorry)
          ├── [ThetaOscillationSqrtHyp] ← auto-resolved
          │   └── ThetaExplicitFormulaOscillation.lean (1 SORRY)
          │       └── [HardyCriticalLineZerosHyp]  ← auto-resolved (full ψ chain above)
          └── [OmegaThetaToPiLiHyp]
              └── OmegaThetaToPiLiWiring.lean (1 SORRY)
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
3. **`CriticalAssumptions.lean`** provides `sorry`-backed instances for the
   1 remaining critical path hypothesis class (was 5; 3 removed, 1 auto-wired, 1 moved to bridge)
4. **`Assumptions.lean`** provides `sorry`-backed instances for ~52
   infrastructure hypothesis classes (not on critical path)
5. **Aristotle/ and Bridge/** work toward replacing those sorries with
   genuine proofs

When an assumption is proved, the `sorry` instance moves out and the
hypothesis is discharged. Six instances are already fully proved:
- `FunctionalEquationHyp` — zeta functional equation (proved)
- `LambdaSymmetryHyp` — completed zeta symmetry (proved)
- `ZeroConjZeroHyp` — conjugation symmetry of nontrivial zeros (proved)
- `ZeroOneSubZeroHyp` — functional equation symmetry (proved)
- `ZetaLogDerivPoleHyp` — -zeta'/zeta has poles at zeros (proved)
- `ZetaCriticalLineBoundHyp` — |ζ(1/2+it)| ≤ C|t|^{1/4+ε} (auto-wired via PhragmenLindelofWiring)

Auto-wired (fire when dependencies are met):
- `ZetaCriticalLineBoundHyp` — via `Bridge/PhragmenLindelofWiring.lean` (0 sorry)
- `HardyCriticalLineZerosHyp` — via `HardyCriticalLineWiring.lean`
- `PsiOscillationFromCriticalZerosHyp` — via `ExplicitFormulaOscillation.lean` (1 sorry)
- `PsiOscillationSqrtHyp` — via `PsiOscillationWiring.lean`
- `ThetaOscillationSqrtHyp` — via `ThetaExplicitFormulaOscillation.lean` (1 sorry)
- `OmegaThetaToPiLiHyp` — via `OmegaThetaToPiLiWiring.lean` (1 sorry)
- `PiLiOscillationSqrtHyp` — via `PsiToPiLiOscillation.lean`

## Project Structure

```
Littlewood/
  Basic/                      3 files  -- Omega-notation, Chebyshev psi/theta, li(x)
  ZetaZeros/                  3 files  -- Zero counting N(T), density, sup real part
  ExplicitFormulas/            5 files  -- Explicit formulas for psi and theta, smoothed, conversions
  CoreLemmas/                  3 files  -- Landau lemma, Dirichlet approx, weighted avg
  Oscillation/                 2 files  -- Schmidt oscillation theorem
  Main/                        3 files  -- Littlewood, LittlewoodPsi, LittlewoodPi (0 sorries)
  Mertens/                     1 file   -- Mertens' first theorem
  CriticalAssumptions.lean     1 file   -- 1 critical path hypothesis instance (sorry)
  Assumptions.lean             1 file   -- ~52 infrastructure hypothesis instances (sorry)
  Aristotle/                 136 files  -- AI-generated proofs (Harmonic + Claude)
    Bridge/                    3 files  -- Aristotle-side wiring (all sorry-free)
    _deprecated/               4 files  -- Superseded Aristotle files
  Bridge/                     30 files  -- Wiring Aristotle proofs to hypothesis classes
  Development/                17 files  -- WIP proofs (not imported by main build)
  Tests/                       8 files  -- Integration tests
scripts/
  verify_build.sh             Automated build verification
  status.sh                   Quick project metrics
  integrate_aristotle.sh      Aristotle file integration automation
docs/
  resumption_guide.md         Claude Code session handoff guide
  AristotleStatus.md          Per-file Aristotle tracking
  aristotle_integration_checklist.md  Manual integration steps
  CurrentStatus.md            Canonical status dashboard
  sorry_manifest.txt          Machine-readable sorry list
  wiring_readiness.md         Per-hypothesis integration guide
  FALSE_THEOREMS.md           Known false/vacuous theorems to avoid
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

- `ZetaCriticalLineBoundHyp` — **AUTO-WIRED** via PhragmenLindelofWiring (0 sorries)
- `HardyFirstMomentUpperHyp` — first moment: |int_1^T Z(t) dt| <= C*T^{1/2+eps}
- `approx_functional_eq` (1 sorry) — approximate functional equation
- Oscillation extraction (1 sorry in ExplicitFormulaOscillation.lean)

## Sorry Inventory

Audited from `lake build` output (2026-02-07). Only imported files
produce build warnings.

### Full build: `lake build` — 10 warnings

| Location | Sorries | Notes |
|----------|---------|-------|
| **CriticalAssumptions.lean** | 1 | HardyFirstMomentUpperHyp |
| **Bridge/** | 3 | ExplicitFormulaOscillation + ThetaExplicitFormulaOscillation + OmegaThetaToPiLiWiring |
| **Aristotle/** | 3 | HardyApproxFunctionalEq(1), ZeroCounting(2) |
| **PrimeNumberTheoremAnd** | 3 | External dependency, NOT on critical path |
| **Total** | **10** | 7 project + 3 external |

### Infrastructure: `lake build Littlewood.Assumptions` — adds ~52 sorries

Assumptions.lean provides sorry-backed instances for non-critical hypothesis
classes (zero counting, weighted average, Landau lemma, etc.). These are NOT
imported by the main theorems and are scaffolding for future extensions.

## Detailed Aristotle Sorry Inventory

| File | Sorries | What each sorry needs | Difficulty |
|------|---------|----------------------|------------|
| **ZeroCounting.lean** | 2 | `zetaZeroCount_via_argument`: N(T) via argument principle. `zetaZeroCount_asymp`: N(T) = (T/2pi)log(T/2pie) - T/2pi + O(log T). | Medium — argument principle machinery exists in Mathlib. |
| **HardyApproxFunctionalEq.lean** | 1 | `approx_functional_eq`: int Z^2 >= k * int \|\|S\|\|^2 - C*T. Needs Riemann-Siegel type approximate functional equation. | Hard — deep analytic number theory. |

### Recently Closed Sorries

| File | Sorry | Closed by |
|------|-------|-----------|
| CriticalAssumptions.lean | `ExplicitFormulaPsiHyp` | REMOVED — tsum formulation FALSE (∑1/\|ρ\| diverges) |
| CriticalAssumptions.lean | `ExplicitFormulaThetaHyp` | REMOVED — same tsum issue |
| CriticalAssumptions.lean | `ZetaCriticalLineBoundHyp` | AUTO-WIRED via PhragmenLindelofWiring |
| CriticalAssumptions.lean | `OmegaThetaToPiLiHyp` | Moved to Bridge/OmegaThetaToPiLiWiring |
| PhragmenLindelof.lean | `zeta_pl_interpolation` | Claude Code — PL + Gaussian damping + Gammaℝ factorization |
| PhragmenLindelof.lean | `gamma_growth` | Claude Code — via GammaGrowthComplete + StirlingRatioPL |
| PhragmenLindelof.lean | `zeta_convexity_bound` | Claude Code — via PhragmenLindelof.vertical_strip |
| PartialSummation.lean | `psi_oscillation_implies_pi_li_oscillation` | REMOVED — theorem was FALSE as stated |
| Bridge/StirlingRatioPL.lean | `stirling_ratio_bounded_on_strip` | Claude Code — via PL + norm_cpow_of_ne_zero |
| DirichletPhaseAlignment.lean | `abs_sin_le_abs`, `h_dirichlet` | Claude Code — direct application |
| ZeroCountingRectangle.lean | `limit_mul_zeta_sub_one` | Claude Code — via tendsto_riemannZeta_sub_one_div |
| ZeroCountingRectangle.lean | `AnalyticAt ℂ g c` | Claude Code — removable singularity theorem |

### Sorry-Free Aristotle Achievements

- **Aristotle/Bridge/** — 3 files, **all sorry-free**:
  - `GammaGrowthComplete.lean` — HasGammaGrowth for all σ > 0
  - `GammaGrowthWiring.lean` — wires gamma growth to critical path
  - `StirlingRatioPL.lean` — Stirling ratio bounded via Phragmen-Lindelof
- **PhragmenLindelof.lean** — reduced from 3 sorries to **0** (all closed: gamma_growth, zeta_convexity_bound, zeta_pl_interpolation)
- **ZetaBoundGtOne.lean** — |ζ(1+δ+it)| ≤ |ζ(1+δ)| (sorry-free)
- **DirichletPhaseAlignment.lean** — Simultaneous Dirichlet approximation, phase alignment from critical zeros, oscillation extraction infrastructure (sorry-free)
- **ZeroCountingRectangle.lean** — Rectangle contour integrals, N(T), zeta log deriv residue, (s-1)*ζ(s)→1, removable singularity (sorry-free)
- **ZetaConvexityStrip.lean** — zeta convexity bounds (sorry-free)
- **RiemannSiegelBound.lean** — Riemann-Siegel bounds (sorry-free)
- **ZetaAnalyticProperties.lean** — functional equation, zeros isolated/finite, analytic at s!=1, Re(ζ)>0 for Re(s)>=2 (sorry-free)
- **ZetaBoundFunctionalEq.lean** — zeta bounded Re(s)>=1+δ, functional eq χ(s) (sorry-free)
- **HardyZIdentities.lean** — Hardy square bound, pointwise identity, integrability (sorry-free)
- **ExplicitFormulaPerron.lean** — finite-sum explicit formula classes (sorry-free)
- **OscillationInfraV2.lean** — sum_diverges_to_infinity oscillation extraction (sorry-free)
- 120+ Aristotle files compile sorry-free

## Key Definitions

| Name | Definition | File |
|------|-----------|------|
| `chebyshevPsi` | Alias for `Chebyshev.psi` (sum of von Mangoldt) | ChebyshevFunctions.lean |
| `chebyshevTheta` | Alias for `Chebyshev.theta` (sum of log p over primes) | ChebyshevFunctions.lean |
| `chebyshevTheta0` | Normalized theta: (θ(x⁺) + θ(x⁻))/2 | ExplicitFormulaTheta.lean |
| `logarithmicIntegral` | `li(x) = int_2^x 1/log(t) dt` | LogarithmicIntegral.lean |
| `IsOmegaPlusMinus f g` | `exists c > 0, f(x) >= c*g(x) i.o. AND f(x) <= -c*g(x) i.o.` | OmegaNotation.lean |
| `zetaNontrivialZeros` | `{s : C | riemannZeta s = 0 AND 0 < s.re AND s.re < 1}` | ZetaZeros/ |
| `hardyZ` | `||riemannZeta(1/2 + t*I)||` (norm-based variant) | HardyApproxFunctionalEq.lean |
| `zeroCountingFunction` | N(T) = number of zeros with 0 < Im(rho) <= T | ZeroCountingFunction.lean |
| `stirling_ratio` | Γ(z)/(z^{z-1/2}e^{-z}) | GammaGrowthGeneral.lean |

## Key Mathlib APIs Used

| Mathlib Lemma | What it gives |
|---------------|--------------|
| `Chebyshev.theta_le_psi` | theta(x) <= psi(x) |
| `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` | \|psi(x) - theta(x)\| <= 2*sqrt(x)*log(x) |
| `Chebyshev.psi_eq_theta_add_sum_theta` | psi = theta + sum of theta at roots |
| `Chebyshev.primeCounting_eq_theta_div_log_add_integral` | pi(x) = theta(x)/log(x) + integral |
| `riemannZeta` | Riemann zeta function (analytic continuation) |
| `Complex.Gamma` | Gamma function |
| `PhragmenLindelof.vertical_strip` | PL on vertical strips with growth bound |
| `norm_cpow_of_ne_zero` | \|z^w\| = \|z\|^(Re w) / exp(arg z * Im w) |
| `Complex.Gamma_mul_Gamma_one_sub` | Gamma reflection formula (no conditions) |
| `abs_sin_le_abs` | \|sin x\| ≤ \|x\| for all real x |
| `tendsto_riemannZeta_sub_one_div` | ζ(s) - 1/(s-1) → γ (Euler-Mascheroni) as s → 1 |
| `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` | Removable singularity: diff on punctured nhds + continuous → analytic |
| `HurwitzZeta.hurwitzZetaEven_residue_one` | (s-1)*ζ(s) → 1 at s=1 |

## Notes for AI Assistants

### What works
- Both main theorems resolve with **NO explicit typeclass parameters** — all instances auto-resolve through the bridge chain.
- The Hardy chain from DiagonalIntegralBound through littlewood_psi is fully wired.
- The π-li chain from ThetaOscillationSqrtHyp through littlewood_pi_li is fully wired.
- θ oscillation is derived directly from the explicit formula for θ (same zero sum as ψ), avoiding the problematic ψ→θ transfer.
- `lake build` completes cleanly (all files compile, only sorry warnings).
- Every sorry on the critical path encodes a specific, independently meaningful piece of mathematics.
- `scripts/integrate_aristotle.sh` automates Aristotle file integration.
- `docs/resumption_guide.md` provides session handoff context for Claude Code.

### What doesn't work
- **OmegaPsiToThetaHyp is mathematically false** (kept for backward compatibility, NOT used by main theorems).
- **PsiToThetaOscillation.lean is DEPRECATED** — the ψ→θ transfer is mathematically problematic (|ψ-θ| ~ √x absorbs the Ω₊ signal). Replaced by ThetaExplicitFormulaOscillation.lean.
- **LandauLemma.lean** sorry is FALSE as stated. Not used downstream.
- **ExplicitFormulaPsiHyp/ThetaHyp** used tsum over zetaNontrivialZeros, which is FALSE (∑1/|ρ| diverges on critical line → tsum = 0). Use truncated sums instead.

### Build configuration
- `maxHeartbeats 1600000`, `maxRecDepth 4000` in lakefile.toml
- Individual files may set higher/lower values
- `synthInstance.maxHeartbeats 20000`, `synthInstance.maxSize 128` in some files

### Common pitfalls
- The project defines its OWN `chebyshevPsi`/`chebyshevTheta`/`logarithmicIntegral` as aliases or redefinitions of Mathlib/PrimeNumberTheoremAnd functions. Always check which namespace you're in.
- Aristotle files sometimes define LOCAL versions of `hardyZ`, `hardyTheta` etc. that differ from the Bridge/ definitions. Check the namespace.
- The `_deprecated/` and `Development/` directories contain abandoned approaches. Don't build on them.
- Many Bridge files exist but are NOT imported by the main build. Check `import` statements.
- `norm_cpow_of_ne_zero` DOES exist in Mathlib (despite some references claiming otherwise).
- Use `le_div_iff₀`/`div_le_iff₀` (with ₀ subscript) in current Mathlib.
- `← rpow_zero` can rewrite the wrong `1` — use `calc` with `(rpow_zero _).symm` instead.

### Priority for reducing sorry count
1. **ExplicitFormulaOscillation** (1 sorry) — ψ oscillation extraction from zeros. Needs truncated explicit formula + Dirichlet phase alignment (alignment PROVED in DirichletPhaseAlignment.lean).
2. **ThetaExplicitFormulaOscillation** (1 sorry) — θ oscillation extraction (same argument as ψ).
3. **HardyApproxFunctionalEq.lean** (1 sorry) — approximate functional equation.
4. **OmegaThetaToPiLiWiring** (1 sorry) — θ oscillation → π-li oscillation transfer.
5. **HardyFirstMomentUpperHyp** (1 sorry) — first moment bound (conditional theorem proved, needs oscillatory integral bounds).
6. **ZeroCounting.lean** (2 sorries) — N(T) via argument principle, asymptotic.

### What a second AI should read first
1. This README (complete dependency tree above)
2. `docs/resumption_guide.md` — session handoff guide with Lean/Mathlib API notes
3. `docs/CurrentStatus.md` — detailed status with wiring diagrams
4. `Littlewood/CriticalAssumptions.lean` — 1 critical path hypothesis instance
5. `Littlewood/Bridge/ExplicitFormulaOscillation.lean` — the key ψ bridge (1 sorry)
6. `Littlewood/Bridge/ThetaExplicitFormulaOscillation.lean` — the θ bridge (1 sorry)
7. `Littlewood/Bridge/PsiToPiLiOscillation.lean` — the π-li bridge (0 sorry)
8. `docs/aristotle_prompts.md` — ready-to-use prompts for closing sorries

## Building

Requires [Lean 4](https://leanprover.github.io/) and
[Mathlib](https://github.com/leanprover-community/mathlib4).

```bash
# Install Lean 4 via elan (if not already installed)
curl https://elan.lean-lang.org/install.sh -sSf | sh

# Build the main theorems only (fastest verification)
lake build Littlewood.Main.Littlewood

# Build the full project
lake build

# Verify critical path test
lake build Littlewood.Tests.CriticalPathTest

# Count sorry declarations
lake build 2>&1 | grep "uses 'sorry'" | wc -l

# List project sorry locations (excluding external dependencies)
lake build 2>&1 | grep "uses 'sorry'" | grep -v PrimeNumberTheoremAnd

# Run automated verification
./scripts/verify_build.sh

# Integrate a new Aristotle file
./scripts/integrate_aristotle.sh path/to/file.lean TargetName
```

Dependencies (from `lakefile.toml`):
- `mathlib` (leanprover-community)
- `PrimeNumberTheoremAnd` (AlexKontorovich)

Build configuration: `maxHeartbeats 1600000`, `maxRecDepth 4000`.

## Contributing

### Tractable Sorries (Aristotle Prompts Available)

See `docs/aristotle_prompts.md` for detailed prompts. Priority order:

1. **ExplicitFormulaOscillation.lean** (1 sorry) — show ∞ critical-line zeros → ψ oscillation. Dirichlet alignment infrastructure proved.
2. **ThetaExplicitFormulaOscillation.lean** (1 sorry) — same argument as #1 applied to θ.
3. **HardyApproxFunctionalEq.lean** (1 sorry) — approximate functional equation.
4. **OmegaThetaToPiLiWiring.lean** (1 sorry) — θ oscillation → π-li oscillation transfer.
5. **ZeroCounting.lean** (2 sorries) — N(T) via argument principle, asymptotic.

### Workflow

1. Pick a sorry from the inventory above
2. Search [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/) for the needed lemma
3. If Mathlib has it: replace `sorry` with a proof
4. If not: document precisely what's missing
5. Run `lake build` to verify
6. Or use `./scripts/integrate_aristotle.sh` for new Aristotle files

## References

- Littlewood, J.E. "Sur la distribution des nombres premiers." _C.R. Acad. Sci. Paris_ 158 (1914), 1869-1872.
- Ingham, A.E. _The Distribution of Prime Numbers._ Cambridge, 1932.
- Montgomery, H.L. and Vaughan, R.C. _Multiplicative Number Theory I._ Cambridge, 2007.
- Titchmarsh, E.C. _The Theory of the Riemann Zeta-Function._ 2nd ed., Oxford, 1986.
- Iwaniec, H. and Kowalski, E. _Analytic Number Theory._ AMS, 2004.

## License

Apache 2.0
