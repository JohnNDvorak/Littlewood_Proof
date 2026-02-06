# Resumption Guide for Littlewood Formalization

**Last Updated**: 2026-02-05 (post StirlingRatioPL closure)

## Quick Start

```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
lake exe cache get
lake build Littlewood.Main.Littlewood
# Expected: ~11 sorry warnings (project + external)
./scripts/verify_build.sh
```

## Project Goal

Formalize Littlewood's theorem in Lean 4 / Mathlib:
- **`littlewood_psi`**: ψ(x) - x = Ω±(√x)
- **`littlewood_pi_li`**: π(x) - li(x) = Ω±(√x / log x)

Both theorems typecheck today with sorry-backed hypothesis instances.

## Current State (2026-02-05)

- **Main theorems**: `littlewood_psi` and `littlewood_pi_li` typecheck
- **Architecture**: Structurally complete — all bridges wired, all chains connected
- **Wiring**: COMPLETE — all Aristotle/Bridge files have 0 sorries
- **External sorries**: 3 in PrimeNumberTheoremAnd/Wiener.lean (NOT on critical path)
- **Budget-exhaustion sorry track record**: 14/15 closed by Claude Code

## Critical Path: 5 Base Assumptions

| # | Assumption | Status | Blocker |
|---|-----------|--------|---------|
| 1 | `ExplicitFormulaPsiHyp` | Pure axiom | Perron's formula (contour integrals not in Mathlib) |
| 2 | `ZetaCriticalLineBoundHyp` | **Partial** | gamma_growth DONE; zeta convexity interpolation remains |
| 3 | `HardyFirstMomentUpperHyp` | **Partial** | Conditional proof exists; needs 4 prerequisites |
| 4 | `OmegaThetaToPiLiHyp` | Pure axiom | Zero-free region / partial summation transfer |
| 5 | `ExplicitFormulaThetaHyp` | Pure axiom | Same blocker as #1 |

## Wiring Chain (all sorry-free except 2 math sorries)

```
ExplicitFormulaPsiHyp ─┐
                       ├─> PsiOscillationFromCriticalZerosHyp (1 math sorry)
HardyCriticalLineZerosHyp ─┤     ├─> PsiOscillationSqrtHyp ──> littlewood_psi
  ├─ ZetaCriticalLineBoundHyp     │
  └─ HardyFirstMomentUpperHyp    │
                                  │
ExplicitFormulaThetaHyp ──┐       │
                          ├─> ThetaOscillationSqrtHyp (1 math sorry)
HardyCriticalLineZerosHyp ─┘     │
                                  ├─> PiLiOscillationSqrtHyp ──> littlewood_pi_li
OmegaThetaToPiLiHyp ─────────────┘
```

## Aristotle Sorry Scorecard

| Category | Sorries | Notes |
|----------|---------|-------|
| Assumptions.lean | 54 | Infrastructure axioms (by design) |
| CriticalAssumptions.lean | 4 | Critical path axioms |
| **Aristotle (active)** | **7** | 6 deep math + 1 interpolation |
| Aristotle/Bridge | **0** | All 3 files sorry-free |
| Bridge (main) | 2 | Oscillation extraction (phase alignment) |
| Development | 5 | Experimental/blocked |
| Deprecated | 13 | Not on critical path |

### 6 Remaining Deep Aristotle Sorries

| File | Line | Sorry | Depth |
|------|------|-------|-------|
| `HardyApproxFunctionalEq.lean` | 119 | `approx_functional_eq` | Riemann-Siegel formula |
| `ExplicitFormula.lean` | 100 | `explicit_formula_for_psi` | Perron's formula |
| `PartialSummation.lean` | 238 | oscillation transfer | Deep analysis |
| `PartialSummation.lean` | 241 | oscillation transfer | Deep analysis |
| `ZeroCounting.lean` | 120 | argument principle | Complex analysis |
| `ZeroCounting.lean` | 132 | N(T) formula | Complex analysis |

### Recently Closed (by Claude Code)

- **PhragmenLindelof.lean** — `zeta_convexity_bound` CLOSED via PL vertical_strip
- **Bridge/StirlingRatioPL.lean** — `stirling_ratio_bounded_on_strip` CLOSED via PL
- **Bridge/GammaGrowthComplete.lean** — `HasGammaGrowth` for all σ > 0 (sorry-free)
- **StirlingBernoulli.lean** — `hasDerivWithinAt_B2_right` closed
- **ContourIntegrationV2.lean** — `crossing_upper` closed
- **HardyApproxFunctionalEqV2.lean** — both sorries closed

## Key Files

| File | Purpose |
|------|---------|
| `CriticalAssumptions.lean` | The 5 critical sorry instances |
| `Assumptions.lean` | All 56+ hypothesis instances (imports CriticalAssumptions) |
| `Bridge/*.lean` | Wiring between hypotheses |
| `Aristotle/*.lean` | ~132 independent proof files |
| `Aristotle/Bridge/*.lean` | Aristotle-side wiring (3 files, all sorry-free) |
| `Main/Littlewood.lean` | `littlewood_psi` theorem |
| `Main/LittlewoodPi.lean` | `littlewood_pi_li` theorem |
| `Tests/CriticalPathTest.lean` | Instance resolution test |

## When Aristotle Delivers a File

Use the automated integration script:

```bash
./scripts/integrate_aristotle.sh ~/Downloads/aristotle_output.lean TargetName
```

This handles: copy, namespace, exact?→sorry, #check removal, heartbeat normalization, build.

For manual integration, see `docs/aristotle_integration_checklist.md`.

### Common Budget-Exhaustion Fixes

| Pattern | Fix |
|---------|-----|
| `exact?` timeout | Try `exact theorem_name` directly |
| `rpow_zero` rewriting wrong `1` | Use `calc` with `(rpow_zero _).symm` |
| `le_div_iff` not found | Use `le_div_iff₀` (with ₀ subscript) |
| `Int.cast_nonneg.mpr` not found | Use `exact_mod_cast` or `by_contra; push_neg; omega` |
| `Complex.abs_im_le_abs` not found | Use `abs_im_le_norm` |
| `h.not_le` (Lean 4.24) | Use `not_le.2 h` (Lean 4.27) |

## Priority Order for Next Work

| Priority | Target | Impact | Approach |
|----------|--------|--------|----------|
| 1 | `PhragmenLindelof.lean:287` (`zeta_convexity_bound`) | Closes ZetaCriticalLineBoundHyp | Hadamard three-lines interpolation — gamma_growth now available |
| 2 | `HardyApproxFunctionalEq.lean:119` | Feeds Hardy chain | Riemann-Siegel — deep, needs new Aristotle output |
| 3 | `ExplicitFormulaPsiHyp` | Enables ψ oscillation | Perron's formula — needs contour integration not in Mathlib |
| 4 | `ExplicitFormulaThetaHyp` | Enables θ oscillation | Same infrastructure as #3 |
| 5 | `OmegaThetaToPiLiHyp` | Final π-li link | Partial summation + error bounds |
| 6 | Bridge math sorries | Final wiring | Oscillation extraction (phase alignment / Kronecker) |

## OmegaThetaToPiLiHyp: Architectural Issue

The current hypothesis requires ∀ f, but only f = √x is used. Options:
1. **Weaken to specific case**: Create `OmegaThetaToPiLiSqrtHyp` with just f = √x
2. **Use unbounded oscillation**: PsiDominance.lean lemmas require K√x bounds
3. **Direct proof**: Use `pi_sub_li_decomposition` + PNT error bounds

## Documentation Index

| File | Purpose |
|------|---------|
| `docs/AristotleStatus.md` | Per-file Aristotle tracking |
| `docs/aristotle_integration_checklist.md` | Manual integration steps |
| `docs/sorry_manifest.txt` | Machine-readable sorry list |
| `docs/project_snapshot_*.md` | State at specific dates |
| `docs/wiring_readiness.md` | Per-hypothesis integration guide |
| `docs/FALSE_THEOREMS.md` | Known false/vacuous theorems to avoid |
| `scripts/verify_build.sh` | Automated build verification |
| `scripts/status.sh` | Quick project metrics |
| `scripts/integrate_aristotle.sh` | Aristotle file integration |

## What NOT to Touch

- `PrimeNumberTheoremAnd/` — External dependency with 3 dead-code sorries
- `Aristotle/_deprecated/` — Old files, not imported anywhere
- `.lake/packages/mathlib/` — External Mathlib files
- Files with `V1` suffix when a `V2`/`V3` exists — the higher version is canonical

## Lean/Mathlib API Notes

Key lemmas discovered during sorry-closing work:

- `norm_cpow_of_ne_zero`: `‖z ^ w‖ = ‖z‖ ^ w.re / exp(arg z * w.im)` — exists and works
- `norm_cpow_eq_rpow_re_of_pos`: `‖(x:ℂ) ^ z‖ = x ^ z.re` for real x > 0
- `abs_arg_le_pi_div_two_iff`: `|arg z| ≤ π/2 ↔ 0 ≤ Re z`
- `Complex.Gamma_mul_Gamma_one_sub`: reflection formula, NO conditions
- `PhragmenLindelof.vertical_strip`: PL on strips, growth rate c < π/(b-a)
- `add_one_le_exp`: `x + 1 ≤ exp(x)` — useful for exp dominance
- `le_div_iff₀` / `div_le_iff₀`: the ₀ subscript versions in current Mathlib

## Conversation Handoff

If starting a new Claude Code session:

1. Read this file for orientation
2. Read `docs/AristotleStatus.md` for current Aristotle work
3. Read `docs/project_snapshot_YYYYMMDD.md` for recent session notes
4. Run `./scripts/verify_build.sh` to confirm state
5. Check Claude Code's `MEMORY.md` for accumulated Lean/Mathlib lessons

The formalization is **structurally complete**. All that remains is closing
the mathematical sorries — deep results requiring infrastructure not yet in Mathlib
or sophisticated proofs that Aristotle is best positioned to deliver.
