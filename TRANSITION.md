# Transition Document: Littlewood's 1914 Oscillation Theorem (Lean 4)

## What This Project Is

A Lean 4 + Mathlib formalization of Littlewood's 1914 proof that π(x) - li(x) changes sign infinitely often. The main results are:

```
Littlewood.littlewood_psi       : ψ(x) - x = Ω±(x^{1/2})
LittlewoodPi.littlewood_pi_li   : π(x) - li(x) = Ω±(x^{1/2}/log x)
LittlewoodPi.pi_gt_li_infinitely_often  : π(x) > li(x) infinitely often
LittlewoodPi.pi_lt_li_infinitely_often  : π(x) < li(x) infinitely often
```

These compile and typecheck. They depend on 58 hypothesis classes in `Assumptions.lean`, each representing a classical theorem not yet in Mathlib (Perron's formula, zero density estimates, explicit formulas, etc.). The project's goal is to close these assumptions by proving them, primarily using AI-generated proofs from Harmonic's "Aristotle" system.

## Repository Location & Build

```
/Users/john.n.dvorak/Documents/Git/Littlewood_Proof/
```

- **Lean version**: leanprover/lean4:v4.24.0
- **Mathlib version**: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
- **Build command**: `lake build` (takes ~5 min, all cached after first build)
- **Sorry count command**: `lake build 2>&1 | grep "uses 'sorry'" | wc -l`
- **Individual file build**: `lake env lean Littlewood/Aristotle/SomeFile.lean 2>&1`

## Current State (2026-01-31)

### Build: CLEAN (no errors)

| Metric | Value |
|--------|-------|
| Total sorry declarations | **77** (74 Littlewood + 3 PrimeNumberTheoremAnd dependency) |
| Assumption sorries (Assumptions.lean) | 58 |
| Non-assumption sorries | 16 (across 10 files + 1 dependency) |
| Active imports in Littlewood.lean | 110 |
| Aristotle files on disk | 90 |
| Aristotle files actively imported | 79 |
| Aristotle files commented out (conflicts) | 11 |
| Bridge files on disk | 19 |
| Bridge files imported | 14 |
| Bridge files not imported (conflicts) | 5 |

### Sorry Declarations by File (non-Assumptions)

| File | Count | Nature | Fixability |
|------|-------|--------|------------|
| `Aristotle/MeanSquare.lean` | 3 | off-diagonal bound, normSq decomp, main thm | MAYBE: existing `integral_cpow_neg_mul_bound` might help |
| `Aristotle/ZeroCounting.lean` | 3 | xi diff (1 deprecated), arg principle, RvM | NEEDS_ARISTOTLE: deep contour integration |
| `Aristotle/PhragmenLindelof.lean` | 3 | critical line bound, convexity, Stirling | NEEDS_ARISTOTLE: Phragmén-Lindelöf theorem |
| `Aristotle/PartialSummation.lean` | 1 | π(x)-li(x) sign changes from ψ(x)-x | NEEDS_ARISTOTLE: partial summation argument |
| `Aristotle/PerronContourIntegralsV2.lean` | 1 | Perron contour integral | FIXABLE: Mathlib has `integral_boundary_rect_eq_zero_of_differentiableOn` |
| `Aristotle/HardyZConjugation.lean` | 1 | conjugation symmetry | NEEDS_ARISTOTLE: completedZeta conjugation |
| `Aristotle/DiagonalIntegralBound.lean` | 1 | harmonic sum bounds + measurability | FIXABLE: broken by missing `Nat.Icc_succ_left` in current Mathlib |
| `Aristotle/ContourInfrastructure.lean` | 1 | measure preimage lemmas | FIXABLE: `exact?` should resolve these |
| `CoreLemmas/LandauLemma.lean` | 1 | Landau's lemma | NEEDS_ARISTOTLE |
| `Bridge/HardyAssemblyAttempt.lean` | 1 | Hardy assembly exploration | Exploratory, not critical |

## Directory Structure

```
Littlewood/
├── Basic/                   -- Ω-notation, Chebyshev ψ/θ, logarithmic integral li
│   ├── OmegaNotation.lean   -- Ω±(f) definition
│   ├── ChebyshevFunctions.lean  -- chebyshevPsi, chebyshevTheta (canonical defs)
│   └── LogarithmicIntegral.lean -- li(x)
├── ZetaZeros/               -- Zero counting N(T), zero density, sup real part
├── ExplicitFormulas/         -- Explicit formula for ψ, smoothed versions, conversions
├── CoreLemmas/               -- Landau lemma (1 sorry), Dirichlet approx, weighted average
├── Oscillation/              -- Schmidt oscillation theorem
├── Main/                     -- LittlewoodPsi.lean, LittlewoodPi.lean (final theorems)
├── Mertens/                  -- Mertens' first theorem
├── Assumptions.lean          -- 58 hypothesis class instances (all sorry)
├── Aristotle/                -- 90 files from Harmonic's Aristotle AI
├── Bridge/                   -- 19 files connecting Aristotle → hypothesis classes
└── Documentation/            -- 42 .md files (status tracking, prompt logs, etc.)
```

## Aristotle Files: How They Work

Aristotle (by Harmonic, https://app.harmonic.fun) generates standalone Lean 4 proofs. Each file:
- Imports only `Mathlib` (no project dependencies)
- Has its own definitions (often redefinitions of things in Basic/)
- Uses `set_option maxHeartbeats 0` (we change to 800000 during integration)
- May have `#check` lines (remove during integration)
- May have `exact?` calls (replace with `sorry` if budget expired)

### Integration Protocol (for new Aristotle files)

1. Read the raw file from `/Users/john.n.dvorak/Documents/Aristotle_Unedited/`
2. Check for definition conflicts with existing files (especially `chebyshevPsi`, `zetaPartialSum`, `N_t`, `hardyZ`, `hardyTheta`)
3. Create in `Littlewood/Aristotle/` with a namespace to avoid conflicts
4. Remove `#check`/`#print` lines
5. Replace `exact?` with `sorry` (with comment noting what it was)
6. Change `maxHeartbeats 0` → `maxHeartbeats 800000`
7. Build: `lake env lean Littlewood/Aristotle/NewFile.lean 2>&1`
8. Add import to `Littlewood.lean`
9. Full build: `lake build 2>&1 | grep "uses 'sorry'" | wc -l`

### Files That CANNOT Be Imported (definition conflicts with Basic/)

These 11 Aristotle files redefine `chebyshevPsi`, `primeCountingReal`, or `li`:
- ChebyshevTheta, PiLiOscillation, PsiDominance, PerronNew, PerronFormulaV2
- ExplicitFormulaV3, SchmidtOscillationInfinite, PartialSummationPiLi
- FunctionalEquation (deprecated), PerronFormula, PrimePowerSums

Their theorems ARE valid — they just can't be imported alongside Basic/. To use them, either create Bridge files that reference their theorems without importing conflicting defs, or refactor them to use Basic/ definitions.

### Unedited Files Not Yet Integrated

There are **63 files** in `/Users/john.n.dvorak/Documents/Aristotle_Unedited/` (UUID-named). Many of these are earlier versions of already-integrated files. When the user provides new Aristotle output files, they appear here first.

## The Hardy Critical Path

The most important open problem is closing the Hardy Z function chain, which would prove infinitely many zeros on the critical line and help close several assumptions.

### What's Done (compiles, 0 sorries)

```
Hardy Z function defined (4 equivalent variants):
  hardyZ      : ℝ → ℝ  (HardyEstimatesPartial)     -- uses (Complex.log ...).im
  hardyZV2    : ℝ → ℂ  (HardyZRealV2)               -- uses Complex.arg
  hardyZV4    : ℝ → ℂ  (HardyZRealV4)               -- Mathlib completedRiemannZeta₀
  Z theta     : ℝ → ℝ  (HardyZContradiction)         -- parameterized by theta

Equivalences proved:
  hardyTheta_eq_thetaV2    (Bridge/HardyZTransfer)
  hardyZ_eq_hardyZV2_re    (Bridge/HardyZTransfer)

Infrastructure proved (0 sorries each):
  - Continuity of Z(t)
  - |Z(t)| = ‖ζ(1/2+it)‖
  - Z(t) = 0 ↔ ζ(1/2+it) = 0
  - Cauchy-Schwarz for ∫|Z|
  - Measurability/integrability
  - Mean square lower bound for PARTIAL SUM: ∫|S_N|² ≥ c·T·log N
  - Diagonal integral ≥ c·T·log T  (4 internal sorries, but structure complete)
  - Constant sign theorem (IVT): no zeros on [T₀,∞) ⟹ constant sign
  - |∫Z| = ∫|Z| when constant sign
  - Asymptotic contradiction: c·T > C·T^{1/2+ε} for large T
  - MAIN THEOREM: HardySetup ⟹ infinitely many zeros (0 sorries!)
```

### What's Missing (the gap)

```
PARTIAL SUM mean square ─── [approximate functional equation] ──→ FULL ZETA mean square
  ∫|S_N(t)|² ≥ c·T·log T                                        ∫|ζ(1/2+it)|² ≥ c·T·log T

The approximate functional equation says:
  ζ(s) = Σ_{n≤√(t/2π)} n^{-s} + χ(s)·Σ_{n≤√(t/2π)} n^{-(1-s)} + error
where the error is O(t^{-1/4}).

This connection would fill the `zeta_mean_square_lower_bound` field in BuildingBlocks
and the `mean_square_lower_bound` field in HardySetup.

Also still needed:
  - First moment upper bound: |∫Z| ≤ C·T^{1/2+ε}  (convexity bound route)
  - Connecting HardySetup class (8 fields) to BuildingBlocks structure (6 fields)
```

### Key Files in the Hardy Chain

| File | Role |
|------|------|
| `HardyZContradiction.lean` | `BuildingBlocks` structure (6 fields), main contradiction proof |
| `HardyInfiniteZeros.lean` | `HardySetup` class (8 fields), `hardy_infinitely_many_zeros` theorem |
| `HardyEstimatesPartial.lean` | `hardyZ`/`hardyTheta` definitions, `exp_iTheta_norm` |
| `HardyZMeasurability.lean` | Integrability/measurability of Z |
| `HardyZCauchySchwarz.lean` | Cauchy-Schwarz for integral estimates |
| `MeanSquareLowerBound.lean` | ∫\|S_N\|² ≥ c·T·log N (partial sum version) |
| `DiagonalIntegralBound.lean` | ∫ diagonal ≥ c·T·log T |
| `Bridge/HardyZTransfer.lean` | Type conversion between Hardy Z variants |
| `Bridge/HardyBuildingBlocksInstance.lean` | Template for filling BuildingBlocks fields |
| `Bridge/HardyCriticalLineWiring.lean` | Pre-wired infrastructure |

## The 58 Assumption Classes

These are in `Assumptions.lean`. Each is a `class` defined in the corresponding module under `Basic/`, `ZetaZeros/`, `ExplicitFormulas/`, etc. They encode theorems like:

- **Explicit formula**: ψ(x) = x - Σ_ρ x^ρ/ρ + O(log²x/T)
- **Perron's formula**: contour integral representation of ψ
- **Zero density**: N(σ,T) ≤ C·T^{a(1-σ)}·log^b(T)
- **Landau's lemma**: Dirichlet series with nonneg coefficients
- **Schmidt oscillation**: trigonometric polynomial independence
- **Weighted average**: integral formulas for ψ(x)-x over zeros
- **Mertens-type**: bounds on prime sums
- **Chebyshev**: ψ(x) ~ x, θ(x) ~ x

To close an assumption: prove the corresponding theorem in Lean 4, then remove the `sorry` from the instance in `Assumptions.lean`.

## Bridge Files: How Wiring Works

Bridge files connect Aristotle proofs (which define their own functions) to the hypothesis classes (which use Basic/ definitions). Pattern:

```lean
-- Bridge/SomeBridge.lean
import Littlewood.Aristotle.SomeProof   -- has Aristotle.someTheorem
import Littlewood.Basic.SomeModule      -- has SomeHyp class

-- Step 1: Show Aristotle's definition equals ours
theorem defs_agree : Aristotle.f = Basic.f := by ...

-- Step 2: Transfer the theorem
instance : SomeHyp := ⟨by rw [← defs_agree]; exact Aristotle.someTheorem⟩
```

## Aristotle Prompts

Prompts for Aristotle go to https://app.harmonic.fun. Key tips:
- Include Lean/Mathlib version in the prompt
- Attach `.lean` context files when building on existing work
- Budget may expire mid-proof (look for "budget reached" in output)
- Use `exact?` output as hints for what Lean would resolve

Existing prompt templates are in `Documentation/Batch2Prompts.md`:
- **Prompt 4**: Riemann-von Mangoldt N(T) = (T/2π)log(T/2πe) + O(log T) (uniform in T)
- **Prompt 5**: Zero-free region: ζ(s) ≠ 0 for σ > 1 - c/log|t|
- **Prompt 6**: Perron's formula: ψ(x) = (1/2πi)∫ -ζ'/ζ · x^s/s ds

## What To Work On Next (Priority Order)

### Priority 1: Close DiagonalIntegralBound sorries
The 4 sorries in `DiagonalIntegralBound.lean` are:
- 2x harmonic sum bounds (∑1/k ≥ log(n+1) and ∑1/k ≤ log(n)+1) — broken by missing `Nat.Icc_succ_left`. Try rewriting the induction to use `Finset.sum_range` instead of `Finset.Icc`.
- 2x measurability of `fun n : ℕ => ∑ k ∈ Finset.range n, (1/(k+1) : ℝ)` — this should follow from `Measurable.of_discrete` or similar since ℕ has the discrete topology.

### Priority 2: Close ContourInfrastructure sorries
The 3 sorries are all measure preimage lemmas. They need to show that the preimage of a line (like {z : ℂ | z.im = 0}) under the `ℂ ≃ ℝ×ℝ` equivalence equals the corresponding product set. Try `simp [Complex.equivRealProd]` or `ext; simp`.

### Priority 3: Close PerronContourIntegralsV2 sorry
Mathlib has `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. The sorry is about a contour integral. Check if the Mathlib API can be applied directly.

### Priority 4: Hardy Chain Completion
Send Aristotle prompts for:
- Approximate functional equation connecting partial sums to ζ
- First moment upper bound via convexity
- Mean square lower bound for ζ on the critical line

Then wire the results through Bridge files to fill BuildingBlocks/HardySetup.

### Priority 5: Close MeanSquare.lean sorries
The off-diagonal bound sorry might be closeable using existing `Aristotle/OffDiagonalBound.lean` (off-diagonal ≤ 8N²) and `OffDiagonalIntegralV2.lean` (off-diagonal integral ≤ CN²).

### Priority 6: New Aristotle Prompts (Batch 2)
Templates ready in `Documentation/Batch2Prompts.md` for Riemann-von Mangoldt, zero-free region, and Perron's formula.

## Important Gotchas

1. **Sorry counting**: Only `lake build 2>&1 | grep "uses 'sorry'" | wc -l` is reliable. Grep for 'sorry' overcounts (comments, strings). The 3 PrimeNumberTheoremAnd sorries are from a dependency, not our code.

2. **maxHeartbeats**: Aristotle uses `set_option maxHeartbeats 0` (unlimited). Change to `800000` during integration. If a proof times out, try increasing to `1600000` before declaring it broken.

3. **Definition conflicts**: The biggest recurring issue. `chebyshevPsi`, `primeCountingReal`, `li`, `zetaPartialSum`, `N_t`, `hardyZ`, `hardyTheta`, `Xi`, `xi` all have multiple definitions across files. Always namespace new files.

4. **Vacuous proofs**: Some Aristotle theorems prove `∃ C, |f(T)| ≤ C·g(T)` by choosing `C := |f(T)|/g(T)`. This makes C depend on T, which is vacuous. These are noted in file headers. `ContourInfrastructure.lean` has two such theorems (renamed with `_vacuous` suffix).

5. **`grind` tactic**: Used in `HardyInfiniteZeros.hardy_infinitely_many_zeros`. It compiled successfully on 2026-01-31 but `grind` behavior may change between Lean versions. If it breaks, the proof needs explicit steps (contradiction via `hardy_inequality_contradiction_large_T`).

6. **Bridge files not imported**: 5 Bridge files exist but aren't imported due to dependency conflicts:
   - `AllBridges` (umbrella, redundant)
   - `NewBridges` (imports TrigPolyIndependence, conflicts with SchmidtNew)
   - `FromGauss` (imports PrimeNumberTheoremAnd, uncertain)
   - `AristotleTransfers` (imports EquivalenceTest, not in main)
   - `VerifyBridges` (verification, not needed for build)

7. **Commented-out Aristotle imports**: 11 files are commented out because they redefine `chebyshevPsi`/`li`/etc. Their theorems are valid but need Bridge files to use.

## Git State

Latest commit: integration of 3 Aristotle files (DiagonalIntegralBound, ContourInfrastructure, HardyInfiniteZeros).

Recent commit history:
```
[pending]  Integrate 3 Aristotle files: diagonal integral, contour infra, Hardy infinite zeros
0c6a3aa   Integrate MeanSquareLowerBound from Aristotle (0 sorries); add Batch2 prompts
f920060   Add missing Bridge imports, wiring analysis docs, sorry closure log
85af9a1   Close ZetaConvexityStrip sorry via riemannZeta_residue_one; add Hardy infrastructure
b9c602c   Merge agent-work: integrate 3 Aristotle files
ecc9a91   Integrate 3 Aristotle files: measurability, PL convexity, partial sum defs
b7ea86a   Overnight session: Hardy assembly, sorry audit, infrastructure
0c75e6a   Integrate 3 Aristotle files: first moment, convexity bounds, Cauchy-Schwarz
```

## Documentation Files

`Littlewood/Documentation/` contains 42 markdown files. The most useful:
- `StatusDashboard.md` — overall project status
- `SorryClosureLog.md` — history of sorry closures
- `AristotlePromptLog.md` — record of Aristotle prompts sent
- `Batch2Prompts.md` — templates for next round of Aristotle prompts
- `HardyDependencyChain.md` — which assumptions the Hardy chain closes
- `HypothesisMapping.md` — maps Aristotle theorems to hypothesis classes
- `DefinitionConflicts.md` — known definition conflict list

## Summary of Numbers

- **77** total sorry declarations (74 ours + 3 dependency)
- **58** assumption classes to close
- **16** non-assumption sorry declarations across 10 files
- **90** Aristotle files integrated
- **19** Bridge files
- **110** active imports
- **0** build errors
- **63** unedited Aristotle files in staging area (many are older versions)
