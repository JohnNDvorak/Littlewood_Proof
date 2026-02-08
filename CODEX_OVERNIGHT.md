# Codex Overnight Session — 2026-02-07

## Project Context

Lean 4 formalization of Littlewood's oscillation theorem. `lake build` passes
with **10 sorry warnings** (7 project + 3 external). Working tree is clean,
all changes pushed to `main`.

## Build Commands

```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
lake build                    # full build, expect 10 sorry warnings
lake build 2>&1 | grep "declaration uses 'sorry'" | wc -l   # should print 10
```

## CRITICAL: Do Not Touch

- `PrimeNumberTheoremAnd/` or `.lake/` — external dependencies
- `Aristotle/_deprecated/` — dead code
- Do NOT try to prove these FALSE theorems (see `docs/FALSE_THEOREMS.md`):
  - `FunctionalEquation.lean: zeta_functional_equation` (missing Gamma_R != 0 hyp)
  - `FunctionalEquation.lean: completed_zeta_zeros_eq_zeta_zeros` (missing 0 < s.re)
  - `ZeroCounting.lean (V1): xi_Mathlib_eq_RiemannXi` (missing 0 < s.re)
  - `CoreLemmas/LandauLemma.lean: zeta_zero_implies_vonMangoldt_singularity` (tsum/LSeries issue)
- Do NOT use tsum over `zetaNontrivialZeros` — it's NOT absolutely convergent (tsum = 0 in Lean)
- Do NOT import files that redefine `chebyshevPsi`/`primeCountingReal`/`li` at root level — they conflict with `Basic/`. These are already listed as commented-out imports in `Littlewood.lean`.

---

## Task 1: Fix stale comments in `Littlewood.lean` (EASY)

Several import comments in `Littlewood.lean` have wrong sorry counts. Update them to match reality:

| Line | Current comment | Correct comment |
|------|----------------|-----------------|
| ~105 | `HardyZConjugation -- ... (1 sorry)` | Verify: does it still have 1 sorry? If 0, update to `(0 sorries) ✓` |
| ~120 | `HardyInfiniteZerosV2 -- ... (1 sorry)` | Verify: does it still have 1 sorry? Check with `grep sorry` |
| ~124 | `ContourRectangle -- ... (1 sorry)` | Verify |
| ~125 | `ZetaBoundsV2 -- ... (3 sorries)` | Verify |
| ~127 | `ZeroFreeRegionV3 -- ... (3 sorries)` | Verify |
| ~141 | `MeanSquare -- 3 sorries` | Verify |
| ~142 | `ZeroCounting -- 2 sorries` | Verify |
| ~143 | `PhragmenLindelof -- 3 sorries` | **WRONG**: should be `(0 sorries) ✓` — all 3 were closed |
| ~144 | `PartialSummation -- 1 sorry` | **WRONG**: the sorry was REMOVED (theorem was FALSE). Update to `(0 sorries) ✓` |

Method: For each file, run `grep -c "sorry" Littlewood/Aristotle/FILE.lean` (excluding comments).
Then update the comment. Do NOT change any code, only comments.

Also update the docstring at the bottom of `Littlewood.lean` (lines ~193-203):
- `Sorry declarations (project): 82` is outdated — don't try to count all of Assumptions.lean, just note it's stale or remove the line.

**Validation**: `lake build` still passes, 10 sorry warnings.

---

## Task 2: Fix `RemainderTermAnalysis.lean` and import it (MEDIUM)

File: `Littlewood/Aristotle/RemainderTermAnalysis.lean` (currently in repo but NOT imported)

This file has 4 `exact?` placeholders. Fix them:

1. **Line ~255**: `fun _ _ _ => by exact?` — replace with `fun _ _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg`
2. **Line ~268**: `exact?` — replace with `exact ArithmeticFunction.vonMangoldt_le_log`
3. **Line ~312**: `exact?` — replace with the theorem proved earlier in the same file (`integral_inv_log_pow_four_bound` or similar — read the file to find the right name)
4. **Line ~325**: `exact?` — try `exact h_final.of_norm_left` or `exact Asymptotics.IsLittleO.of_norm_left h_final`

After fixing, the file should have 0 sorries. BUT it defines `li` inside `namespace Aristotle.RemainderTermAnalysis` — this should NOT conflict with `Basic/LogarithmicIntegral.lean`.

Add to `Littlewood.lean`:
```lean
import Littlewood.Aristotle.RemainderTermAnalysis  -- Remainder term analysis (0 sorries) ✓
```

**Validation**: `lake build` still passes with 10 sorry warnings (not 12+).

---

## Task 3: Wire more orphan Aristotle files into build (MEDIUM)

Check these orphan files for importability (0 sorries, no root-level conflicts):

### Safe to import (have namespaces, no conflicts):
- `VanDerCorputInfra.lean` — namespace `Aristotle.VanDerCorput`, 0 sorries. Van der Corput integration infrastructure.
- `DirichletPhaseAlignment.lean` — check namespace. Simultaneous Dirichlet approximation (PROVED). 0 sorries.
- `ZeroCountingRectangle.lean` — check namespace. Rectangle contour integrals. 0 sorries.
- `ContourIntegrationV2.lean` — check namespace. Cauchy rectangle theorem. 0 sorries.
- `ZetaLogDerivInfra.lean` — check namespace. Pole structure of -ζ'/ζ. 0 sorries.
- `HardySetupRequirements.lean` — check namespace. 0 sorries.
- `GammaGrowthGeneral.lean` — check namespace. 0 sorries.
- `ZetaBoundGtOne.lean` — check namespace. 0 sorries.
- `RiemannSiegelBound.lean` — check namespace. 0 sorries.

### DO NOT import (conflicts):
- Files that redefine `chebyshevPsi` at root level: `PerronNew`, `PsiDominance`, `PiLiOscillation`, `PerronFormulaV2`, `ExplicitFormulaV3`, `PartialSummationPiLi`, `ChebyshevTheta`
- Files that conflict with existing imports: `SchmidtOscillation`/`TrigPolyIndependence` (conflict with `SchmidtNew`), `ZeroCountingV2` (conflicts with `ZeroCountingNew`)
- `HardyInfiniteZeros` (deprecated V1, vacuous proofs)
- `FunctionalEquation` (deprecated, has false theorem)

### Method for each file:
1. `grep -c "sorry" Littlewood/Aristotle/FILE.lean` — must be 0
2. Check for top-level `noncomputable def` outside any namespace — conflict risk
3. If safe, add `import Littlewood.Aristotle.FILE` to `Littlewood.lean`
4. Run `lake build` — if duplicate definition errors, remove the import and add a comment explaining why

**Validation**: `lake build` passes, sorry count stays at 10.

---

## Task 4: Update `docs/AristotleStatus.md` counts (EASY)

After completing Tasks 1-3, update:
- Number of files in build (currently 81)
- Number of orphans (currently 50)
- Add any newly imported files to the "Key Sorry-Free Files" table

---

## Task 5 (STRETCH): Attempt to close `zetaZeroCount_via_argument` (HARD)

File: `Littlewood/Aristotle/ZeroCounting.lean:117`

This sorry needs the argument principle to connect the contour integral
of ζ'/ζ around a rectangle to the number of zeros inside. Infrastructure exists:
- `CauchyGoursatRectangle.lean` — Cauchy-Goursat for rectangles (0 sorries)
- `ContourRectangle.lean` — rectangle contour integrals
- `ZetaLogDerivInfra.lean` — pole structure of -ζ'/ζ
- `ZeroCountingRectangle.lean` — (s-1)ζ(s)→1, residue infrastructure

Read these files to understand what's available, then attempt to fill the sorry.
The argument principle may not be directly in Mathlib — check first with
`grep -r "argument_principle\|winding_number\|argument_count" .lake/packages/mathlib/`.

If blocked, document what's missing and move on.

---

## Task 6 (STRETCH): Attempt `zetaZeroCount_asymp` (HARD)

File: `Littlewood/Aristotle/ZeroCounting.lean:134`

The asymptotic N(T) = (T/2π)log(T/2πe) + O(log T). Infrastructure:
- `NAsymptotic.lean` — N(T) asymptotic framework (0 sorries)
- `NZerosStirling.lean` — N(T) from S(T) and Stirling (0 sorries)
- `RiemannVonMangoldtV2.lean` — R-vM formula v2 (0 sorries, but `NZeros` is a formula not actual count)

The connection between the formula `NZeros` and the actual zero count `zetaZeroCount` IS the argument principle (Task 5). So this likely depends on Task 5.

---

## Commit Instructions

After each completed task:
1. Run `lake build` and verify sorry count = 10
2. `git add` only the files you changed
3. Commit with descriptive message
4. Push to main

Example:
```bash
git add Littlewood.lean
git commit -m "Fix stale sorry count comments in Littlewood.lean"
git push
```

## Priority Order

1. Task 1 (fix comments) — 10 min, guaranteed value
2. Task 2 (RemainderTermAnalysis) — 30 min, likely success
3. Task 3 (wire orphans) — 1 hr, incremental wins
4. Task 4 (update docs) — 10 min
5. Task 5/6 (stretch) — only if time permits, may be blocked
