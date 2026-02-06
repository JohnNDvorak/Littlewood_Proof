# Aristotle Output Integration Checklist

**Last updated**: 2026-02-04
**Current Lean version**: leanprover/lean4:v4.27.0-rc1
**Project standard maxHeartbeats**: 1600000

## When Aristotle Delivers a File

### Pre-Integration Analysis
- [ ] Note the uuid from the file header
- [ ] Check Lean version in header (usually v4.24.0 — needs compat fixes for v4.27)
- [ ] Count `exact?` calls (these become `sorry` during integration)
- [ ] Count existing `sorry` calls
- [ ] Check for `#check` statements (remove them)
- [ ] Check for `maxHeartbeats 0` (change to 1600000)
- [ ] Identify what theorems are proved vs sorry-backed
- [ ] Check if definitions conflict with project definitions (chebyshevPsi, li, etc.)

### Integration Steps
1. [ ] Copy file to `Littlewood/Aristotle/<DescriptiveName>.lean`
2. [ ] Update file header comment (add sorry count, list proved theorems)
3. [ ] Set `maxHeartbeats 1600000` (project standard)
4. [ ] Add namespace: `namespace Aristotle.<DescriptiveName>`
5. [ ] Add `end Aristotle.<DescriptiveName>` at end
6. [ ] Replace all `exact?` with `sorry`
7. [ ] Remove all `#check` statements
8. [ ] Run `lake build Littlewood.Aristotle.<DescriptiveName>`
9. [ ] Fix any Lean 4.24 -> 4.27 compatibility issues (see below)
10. [ ] Verify sorry count matches expected

### Post-Integration Audit
11. [ ] For each sorry, determine if it's:
    - Budget exhaustion (`exact?` timeout) — try to close
    - Real math gap — document what's needed
12. [ ] Attempt to close budget-exhaustion sorries (common wins below)
13. [ ] Update `docs/AristotleStatus.md` (file count, reference table, prompt status)
14. [ ] If build-visible, update `docs/sorry_manifest.txt`

### Wiring (if closing a hypothesis)
15. [ ] Identify which Bridge file consumes this theorem
16. [ ] Check if auto-wiring works or manual bridge needed
17. [ ] If PhragmenLindelofWiring pattern: import Bridge file in CriticalAssumptions, remove sorry instance
18. [ ] Run `lake build Littlewood.Main.Littlewood`
19. [ ] Verify sorry count decreased
20. [ ] Update `scripts/verify_build.sh` expected count

## Known Compatibility Fixes (Lean 4.24 -> 4.27)

| Pattern | Old (4.24) | New (4.27) | Example |
|---------|-----------|-----------|---------|
| Dot notation for not_le | `h.not_le` | `not_le.2 h` | ContourIntegrationV2 |
| Int cast lemma rename | `Int.cast_nonneg.mpr` | `exact_mod_cast` | ZetaIntegralRep |
| ContDiffOn parameter | `le_rfl` | `(by norm_num)` | VanDerCorputInfra |
| simp unused args | warning only | warning only | Cosmetic, ignore |

## Common Sorry Closures

| Sorry pattern | Likely fix |
|---------------|-----------|
| `exact?` on `riemannZeta_residue_one` | `exact riemannZeta_residue_one` |
| `exact?` on self-referencing theorem | `exact <theorem_name>` |
| `exact?` on `neg_log_deriv_of_pow_mul_analytic` | `exact neg_log_deriv_of_pow_mul_analytic ...` |
| `analyticOrderAt ≠ 0` from `f(z) = 0` | `rw [ne_eq, h_analytic.analyticOrderAt_eq_zero]; exact not_not.mpr hρ` |
| `1 ≤ x` from `x ≠ 0` in `ℕ∞` | `exact ENat.one_le_iff_ne_zero.mpr h` |
| Interval ordering `a < b` | `exact h_ordering` (check hypotheses) |
| Forward direction of iff | `simp_all +decide [...]` (check analogous proved case) |

## Wiring Quick Reference

| Aristotle Target | Bridge File | Hypothesis Closed | Status |
|-----------------|-------------|-------------------|--------|
| `approx_functional_eq` | MeanSquareBridge (auto) | feeds Hardy chain | 1 sorry remains |
| `gamma_growth` | PhragmenLindelofWiring (READY) | `ZetaCriticalLineBoundHyp` | 1 sorry + needs new math |
| `zeta_convexity_bound` | PhragmenLindelofWiring (READY) | `ZetaCriticalLineBoundHyp` | blocked by gamma_growth |
| Perron formula proofs | needs new Bridge | `ExplicitFormulaPsiHyp` | Prompts 6-9 chain |
| Perron formula (theta) | needs new Bridge | `ExplicitFormulaThetaHyp` | same chain |
| θ→π-li transfer | needs new Bridge | `OmegaThetaToPiLiHyp` | requires error bounds |

## File Naming Convention

- `<Topic>.lean` — primary file for a topic
- `<Topic>V2.lean`, `<Topic>V3.lean` — improved versions
- `<Topic>Infra.lean` — infrastructure/definitions file
- Files use `import Mathlib` only (standalone, no project imports)
- Namespace: `Aristotle.<FileName>` (e.g., `Aristotle.ZetaLogDerivInfra`)
