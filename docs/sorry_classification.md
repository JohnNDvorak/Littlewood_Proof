# Sorry Classification for Littlewood Formalization

**Generated:** 2026-01-21
**Total Sorries:** 121
**Excluding Comment References:** ~115 actual sorry statements

## Classification Categories

### Category A: Potentially Provable with Current Mathlib (~3)

These sorries are pure Lean/Mathlib technical issues, not mathematical blockers:

| File | Line | Lemma | Notes |
|------|------|-------|-------|
| TypeBridge.lean | 155 | `summatory_step` | Finset.Icc manipulation; needs correct tactic strategy |
| ZeroFreeRegion.lean | 338 | `zeta_ne_zero_implies_product_bound` | Logic extraction from 3-4-1 inequality |
| ZeroFreeRegion.lean | 382 | `neg_zeta_logderiv_re_bound` | Bound extraction, may need calculus |

**Estimated effort:** 2-8 hours each if provable

### Category B: Hypothesis Instances (61)

All in `Assumptions.lean` - these are **documented assumptions** representing the hypothesis-based architecture. They require the corresponding Development theorems to be completed.

**Not fillable directly** - require Category C or D work first.

### Category C: Blocked on Quantitative Zero-Free Region (~15)

Need Mathlib's interior zero-free region (beyond Re(s) ≥ 1):

| File | Line | Description |
|------|------|-------------|
| ZeroFreeRegion.lean | 256 | DirichletCharacter specialization |
| ZeroFreeRegion.lean | 280 | Quantitative zero-free region |
| ZeroFreeRegion.lean | 320 | Mertens inequality |
| ZeroFreeRegion.lean | 353 | ζ real-valued on reals |
| ZeroFreeRegion.lean | 373 | Laurent expansion |
| ZeroFreeRegion.lean | 412 | Interior region |
| SupremumRealPart.lean | 335-347 | All 4 sorries |
| + Related instances | - | Depends on these |

**Mathlib PR needed:** `quantitative_zero_free.md` spec (~80-150 hours)

### Category D: Blocked on Perron's Formula (~25)

Explicit formula infrastructure requires Perron:

| File | Lines | Description |
|------|-------|-------------|
| CoreLemmas/LandauLemma.lean | 387-437 | All 11 hypothesis instances |
| CoreLemmas/WeightedAverageFormula.lean | 349-379 | All 7 hypothesis instances |
| ConversionFormulas.lean | 241, 246 | Omega conversions |
| + Assumptions.lean | - | Related explicit formula hyps |

**Mathlib PR needed:** `perron_formula.md` spec (~100-200 hours)

### Category E: Blocked on Hardy's Theorem (~15)

Hardy Z-function and critical line zeros:

| File | Lines | Description |
|------|-------|-------------|
| HardyTheorem.lean | 90 | Riemann-Siegel theta asymptotic |
| HardyTheorem.lean | 112 | hardyZ_real |
| HardyTheorem.lean | 142 | sign_change_implies_zero |
| HardyTheorem.lean | 169 | hardyZ_is_real |
| HardyTheorem.lean | 181 | hardyZ_continuous |
| HardyTheorem.lean | 195-264 | All remaining Hardy lemmas |
| SchmidtTheorem.lean | 195-231 | All 9 oscillation instances |

**Mathlib PR needed:** `hardy_theorem.md` spec (~200-400 hours)

### Category F: Blocked on Zero Counting (~10)

N(T) asymptotic formula:

| File | Description |
|------|-------------|
| Related instances in Assumptions.lean | ZeroCountingAsymptoticHyp, etc. |

**Mathlib PR needed:** `zero_counting.md` spec (~100-200 hours)

## Summary Table

| Category | Count | Estimated Hours | Mathlib PR Required |
|----------|-------|-----------------|---------------------|
| A: Potentially Provable | ~3 | 10-25 | No |
| B: Hypothesis Instances | 61 | N/A | Depends on C-F |
| C: Zero-Free Region | ~15 | 80-150 | Yes |
| D: Perron's Formula | ~25 | 100-200 | Yes |
| E: Hardy's Theorem | ~15 | 200-400 | Yes |
| F: Zero Counting | ~10 | 100-200 | Yes |
| **Total** | **~115** | **490-975** | **4 major PRs** |

## Recommendations

### Immediate Action (Category A)

1. **`summatory_step`**: Try different tactic approach (unfold vs simp, explicit types)
2. **`zeta_ne_zero_implies_product_bound`**: Check if logic can be extracted from existing 3-4-1 proof
3. **`neg_zeta_logderiv_re_bound`**: May require real analysis bounds

### Near-Term (After Mathlib Growth)

Monitor Mathlib for:
- Quantitative zero-free region additions
- Perron's formula or related contour integration
- Hardy Z-function definitions

### Long-Term (Mathlib PRs)

Priority order for community contribution:
1. **Quantitative Zero-Free** - Most prerequisites exist, medium complexity
2. **Perron's Formula** - High impact, unlocks explicit formulas
3. **Zero Counting** - Requires argument principle extensions
4. **Hardy's Theorem** - Highest complexity, requires slitPlane fixes

## Files with No Sorries (Proved Theorems)

These files have complete proofs:
- `Littlewood/Main/*.lean` - Main theorem statements (compile without sorry)
- `Littlewood/ZetaZeros/ZeroCountingFunction.lean` - Basic definitions
- `Littlewood/Development/LandauLemma.lean` - vonMangoldt identity proved
- `Littlewood/Development/Bridge.lean` - Documentation only

## Conclusion

**~3 sorries are potentially attackable** with current Mathlib, requiring creative tactic work.

**~112 sorries are blocked** on Mathlib infrastructure that doesn't exist:
- 61 are hypothesis instances (architectural placeholders)
- ~51 are actual proof blockers requiring 4 major Mathlib PRs

**Estimated time to 100% formalization: 490-975 hours** of Mathlib development.
