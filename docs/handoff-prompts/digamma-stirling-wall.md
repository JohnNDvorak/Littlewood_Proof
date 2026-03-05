# Handoff Prompt: The Digamma/Stirling Wall

## Mission

Prove `digamma_log_bound_atomic` in Lean 4 / Mathlib:

```lean
theorem digamma_log_bound_atomic :
    ∃ C > 0, ∀ s : ℂ, s.re ≥ 1/4 → |s.im| ≥ 1 →
      Gamma s ≠ 0 →
      ‖deriv Gamma s / Gamma s - Complex.log s‖ ≤ C / ‖s‖
```

**File**: `Littlewood/Aristotle/DigammaBinetBound.lean:92`

This is the **single most critical sorry** in the project. Closing it unblocks
**9 of 13 remaining sorry's** across 3 independent proof chains (B3, B5b, and
the Riemann-von Mangoldt infrastructure shared by both).

## Impact Map

```
digamma_log_bound_atomic (THIS SORRY)
├── DigammaAsymptotic.lean → digamma_log_bound (delegates)
│   └── re_digamma_asymptotic: Re(ψ(s) - log(s)) = O(1/t)
│       └── ThetaDerivAsymptotic.lean → theta_deriv_asymptotic
│           └── θ'(t) = (1/2)·log(t/(2π)) + O(1/t) [PROVED]
│               └── Integration gives θ(t) Stirling expansion
│                   └── theta_stirling_expansion [BLOCKS 4 B3 sorry's]
│                   └── RvM Theta hypothesis [BLOCKS 2 B5b sorry's]
│                       └── riemann_von_mangoldt_conditional (also needs AP)
│                           └── critical_zero_sum_diverges
│                           └── exists_large_x_phases_aligned_to_target
└── (7 B3-infra sorry's trace through theta_stirling or share the Stirling gap)
```

## What's Already Proved (Use These)

### In DigammaBinetBound.lean (42 lines proved, 1 sorry)

- **`gauss_term_bound`** (line 44): `‖log(1+1/w) - 1/w‖ ≤ 1/‖w‖²` for `‖w‖ ≥ 2`.
  Uses Mathlib's `norm_log_one_add_sub_self_le`.

- **`norm_sq_add_natCast_ge`** (line 71): `‖s‖² + j² ≤ ‖s+j‖²` for `Re(s) ≥ 0`.
  Proved by expanding norms and using `2j·Re(s) ≥ 0`.

### In BinetStirling.lean (512 lines, 0 sorry)

- **`log_quarter_plus_it_half_asymptotic`** (line 150):
  `log(1/4+it/2) = log(t/2) + iπ/2 - i/(2t) + O(1/t²)`

- **`stirling_approx_im_asymptotic`** (line 184):
  `Im(stirlingApprox(t)) - ((t/2)·log(t/2) - t/2 - π/8) = O(1/t)`

- Binet integrand infrastructure (lines 287-510): `binetIntegrand`, `binetIntegral`,
  continuity, differentiability, boundedness, `binet_integrand_limit_zero` (→ 1/12).

### In StirlingBernoulli.lean (221 lines, 0 sorry)

- `B2_continuous`, `deriv_B2`, `B2_zero`, `B2_bounded`,
  `integral_B1_eq_B2_sub_const`, `hasDerivWithinAt_B2_right`

### In StirlingGammaBounds.lean (528 lines, 0 sorry)

- `stirling_proxy_bounded_strip` (Phragmen-Lindelof), `gamma_reflection_bound`,
  `gamma_step_down`, `gamma_one_bound`, `gamma_two_bound`

### In ThetaDerivAsymptotic.lean (419 lines, 0 sorry conditional on digamma)

- **`theta_deriv_asymptotic`** (line 214): `θ'(t) - (1/2)·log(t/(2π)) = O(1/t)`.
  **PROVED** from `re_digamma_asymptotic` (which delegates to `digamma_log_bound_atomic`).

## What Mathlib Provides

### Gamma function (`.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/`)

| Lemma | File | What it gives |
|-------|------|---------------|
| `Complex.GammaSeq s n` | Beta.lean:233 | `n^s · n! / ∏_{j=0}^n (s+j)` |
| `Complex.GammaSeq_tendsto_Gamma s` | Beta.lean:337 | `GammaSeq s → Γ(s)` pointwise |
| `Complex.Gamma_ne_zero_of_re_pos` | Beta.lean:454 | `Re(s) > 0 → Γ(s) ≠ 0` |
| `Complex.Gamma_mul_Gamma_one_sub` | Beta.lean | Reflection formula |
| `hasDerivAt_GammaIntegral` | Deriv.lean:50 | Derivative of Mellin integral, `Re(s) > 0` |
| `differentiableAt_Gamma` | Deriv.lean:86 | `s ∉ -ℕ → DifferentiableAt ℂ Γ s` |
| `differentiable_one_div_Gamma` | Deriv.lean | `1/Γ` is entire |

### Locally uniform limits (`.lake/packages/mathlib/Mathlib/Analysis/Complex/LocallyUniformLimit.lean`)

| Lemma | Line | What it gives |
|-------|------|---------------|
| `TendstoLocallyUniformlyOn.deriv` | 153 | If `F_n → f` locally uniformly on open `U`, and each `F_n` is differentiable on `U`, then `F_n' → f'` locally uniformly on `U` |

### What Mathlib Does NOT Provide

- No complex `logGamma` or `digamma` function
- No complex Stirling formula with error bounds
- No locally uniform convergence of `GammaSeq` (only pointwise)
- No Binet integral representation connecting to Gamma
- No Gauss digamma series `ψ(s) = lim_{n→∞} [log n - Σ_{j=0}^n 1/(s+j)]`

## Proof Strategy

### Recommended: Gauss Series Route (~200-300 lines)

**Step 1** (~80 lines): Prove `GammaSeq` converges **locally uniformly** on
`U = {s : ℂ | ∀ m : ℕ, s ≠ -m}` (or the simpler `U = {Re > 0}`).

The key: `GammaSeq s n = n^s · n! / ∏_{j=0}^n (s+j)`. Each `GammaSeq(·, n)` is
rational in s (hence analytic on U). Pointwise convergence is
`GammaSeq_tendsto_Gamma`. For locally uniform convergence, use Vitali's theorem
(not in Mathlib) or prove a direct uniform bound on compact subsets of U.

**Alternative to Vitali**: Show `GammaSeq` is locally bounded. On compact K ⊂ U,
each factor `|n^s · n! / ∏(s+j)|` is bounded by `C_K · |Γ(s)| + ε` for large n.
This follows from the product formula. Combined with pointwise convergence,
Montel's theorem (not in Mathlib) gives locally uniform convergence. OR: just
prove the bound directly by estimating the tail of `log(GammaSeq(s,n)/Γ(s))`.

**Simplest approach**: Work on `{Re > 1/4} ∩ {|Im| > 1/2}` where Γ is nonzero and
bounded below. Show `|GammaSeq(s,n)/Γ(s) - 1| → 0` uniformly on compacts, by:
- `GammaSeq(s,n)/Γ(s) = ∏_{j>n} (1 + s/j)·e^{-s/j}` (from Weierstrass product)
- Each partial product is bounded; tail → 1 uniformly.

**Step 2** (~30 lines): Apply `TendstoLocallyUniformlyOn.deriv` to get
`deriv(GammaSeq(·,n)) → Γ'` locally uniformly on U.

**Step 3** (~40 lines): Compute `deriv(GammaSeq(·,n))/GammaSeq(·,n)` explicitly:
```
log(GammaSeq(s,n)) = s·log(n) + log(n!) - Σ_{j=0}^n log(s+j)
d/ds = log(n) - Σ_{j=0}^n 1/(s+j)
```
This is the **Gauss digamma series** truncated at n.

**Step 4** (~50 lines): Show `Γ'/Γ(s) = lim [log(n) - Σ_{j=0}^n 1/(s+j)]`
locally uniformly on U. Then:
```
ψ(s) - log(s) = lim_{n→∞} [log(n) - Σ_{j=0}^n 1/(s+j)] - log(s)
              = lim_{n→∞} [(log(n) - log(s)) - Σ_{j=0}^n 1/(s+j)]
              = -γ/s + Σ_{j≥1} [1/j - 1/(s+j)]     (Euler-Mascheroni absorbed)
```
Actually, the cleaner identity is:
```
ψ(s) - log(s) = Σ_{j≥0} [log(1 + 1/(s+j)) - 1/(s+j)]
```
Each term bounded by `1/‖s+j‖²` (from `gauss_term_bound` at `w = s+j`).

**Step 5** (~50 lines): Sum the bound:
```
Σ_{j≥0} 1/‖s+j‖² ≤ Σ_{j≥0} 1/(‖s‖²+j²)    (from norm_sq_add_natCast_ge)
                   ≤ 1/‖s‖² + ∫_0^∞ dt/(‖s‖²+t²)
                   = 1/‖s‖² + π/(2‖s‖)
                   ≤ C/‖s‖    (for ‖s‖ ≥ 1)
```
For `Re(s) ≥ 1/4`, `|Im(s)| ≥ 1`: `‖s‖ ≥ 1`, so this gives `C/‖s‖`.

### Alternative: Binet Integral Route (~300-400 lines)

Prove `log Γ(s) = (s-1/2)·log(s) - s + (1/2)·log(2π) + binetIntegral(s)` where
`|binetIntegral(s)| ≤ C/|s|`. Differentiate to get the digamma bound.

This is harder because:
- Need to establish the Binet integral representation (integration by parts of
  the Bernoulli series against `e^{-tz}`)
- Need to connect `binetIntegral` to `log(Gamma)` (not just `Gamma`)
- The Binet integrand infrastructure in BinetStirling.lean is ready but the
  connection to Gamma is not proved

### Alternative: Direct Derivative Estimate (~150-200 lines, risky)

Skip the series entirely. Prove `|Γ'(s)/Γ(s) - log(s)| ≤ C/|s|` directly from:
1. The reflection formula `Γ(s)Γ(1-s) = π/sin(πs)` (differentiate both sides)
2. The functional equation `Γ(s+1) = sΓ(s)` (shift to large Re(s))
3. Stirling's formula for real Gamma (Mathlib has this asymptotically)

Risk: connecting real Stirling to complex via Phragmen-Lindelof may be as hard
as the direct Gauss series approach.

## File Map

### Files to modify
| File | Lines | Sorry | Action |
|------|-------|-------|--------|
| `Littlewood/Aristotle/DigammaBinetBound.lean` | 94 | 1 | **PROVE the sorry** |

### Files that will be unblocked (read-only context)
| File | Lines | Sorry | Role |
|------|-------|-------|------|
| `Littlewood/Aristotle/DigammaAsymptotic.lean` | 164 | 0 | Delegates to `digamma_log_bound_atomic` |
| `Littlewood/Aristotle/ThetaDerivAsymptotic.lean` | 419 | 0 | `θ'(t)` asymptotic (conditional) |
| `Littlewood/Aristotle/BinetStirling.lean` | 512 | 0 | Stirling approximation + Binet infra |
| `Littlewood/Aristotle/StirlingBernoulli.lean` | 221 | 0 | Bernoulli periodic functions |
| `Littlewood/Aristotle/StirlingGammaBounds.lean` | 528 | 0 | Gamma bounds via Phragmen-Lindelof |
| `Littlewood/Aristotle/StirlingArgGamma.lean` | 189 | 0 | NEGATIVE result: naive arg(Γ) expansion is FALSE |
| `Littlewood/Aristotle/ErrorTermExpansion.lean` | ~350 | 4 | B3 infra (theta_stirling blocks 4 sorry's) |
| `Littlewood/Aristotle/RSBlockBounds.lean` | ~160 | 3 | B3 infra (3 sorry's, some share Stirling dep) |
| `Littlewood/Aristotle/RiemannVonMangoldt.lean` | 166 | 0 | RvM conditional theorem (needs Stirling) |
| `Littlewood/Aristotle/Standalone/PsiZeroSumOscillationFromIngham.lean` | ~897 | 1 | B5b (needs RvM for sum divergence) |
| `Littlewood/Aristotle/DirichletPhaseAlignment.lean` | ~389 | 1 | B5b (needs RvM for phase alignment) |

### Mathlib files (read-only reference)
| File | Key contents |
|------|-------------|
| `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean` | `GammaSeq`, `GammaSeq_tendsto_Gamma`, `Gamma_ne_zero` |
| `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean` | `hasDerivAt_GammaIntegral`, `differentiableAt_Gamma` |
| `.lake/packages/mathlib/Mathlib/Analysis/Complex/LocallyUniformLimit.lean` | `TendstoLocallyUniformlyOn.deriv` |

## Build & Verify

```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof

# Build just the target file
lake build Littlewood.Aristotle.DigammaBinetBound

# Build downstream to verify unblocking
lake build Littlewood.Aristotle.DigammaAsymptotic
lake build Littlewood.Aristotle.ThetaDerivAsymptotic

# Full project sorry count (target: 12 after closing this sorry)
lake build 2>&1 | grep "declaration uses 'sorry'" | sort -u | wc -l
```

## Constraints

- **Import only `Mathlib`** (no project-internal imports needed for this file).
- The file currently has `set_option maxHeartbeats 400000`. Increase if needed.
- `open Complex` is already in scope.
- All infrastructure lemmas (`gauss_term_bound`, `norm_sq_add_natCast_ge`) are
  in the same file and ready to use.
- The proof should work for `s.re ≥ 1/4 ∧ |s.im| ≥ 1`. The `Gamma s ≠ 0`
  hypothesis is available (and follows from `Gamma_ne_zero_of_re_pos` for
  `Re(s) > 0`, but the bound includes `Re(s) = 1/4` where this doesn't apply
  directly — use `Gamma_ne_zero` with `∀ m, s ≠ -m` from the strip constraint).

## Key Pitfalls

1. **Locally uniform convergence is the hard part.** Mathlib has pointwise
   `GammaSeq_tendsto_Gamma` but not locally uniform. You need to either:
   - Prove a direct uniform bound on compacts (recommended)
   - Use Montel/Vitali (not in Mathlib — would need to build from scratch)
   - Find a workaround that avoids locally uniform convergence entirely

2. **`deriv Gamma s / Gamma s` vs. a defined `digamma`.** Mathlib has no digamma
   function. The expression `deriv Gamma s / Gamma s` is the logDerivative.
   Make sure `deriv Gamma` is well-defined at s (use `differentiableAt_Gamma`).

3. **`gauss_term_bound` requires `‖w‖ ≥ 2`.** For `w = s + j` with `‖s‖ ≥ 1`,
   the first few terms (j = 0, maybe j = 1) may have `‖s+j‖ < 2`. Handle these
   separately with a cruder bound.

4. **The sum `Σ 1/‖s+j‖²` needs `Summable`.** Prove via comparison with `Σ 1/j²`
   (which is summable). For `j ≥ ‖s‖`, `‖s+j‖ ≥ j - ‖s‖ ≥ j/2`, so
   `1/‖s+j‖² ≤ 4/j²`.

5. **Branch cut of `Complex.log`.** The Gauss series uses `log(1 + 1/(s+j))`.
   For `Re(s) ≥ 1/4` and `j ≥ 0`, `Re(1 + 1/(s+j)) > 0`, so the principal
   branch is correct. But verify this doesn't cause issues for small j.

## What Success Looks Like

After closing this sorry:
- `DigammaBinetBound.lean` has **0 sorry**
- `DigammaAsymptotic.lean` remains **0 sorry** (was conditional, now unconditional)
- `ThetaDerivAsymptotic.lean` remains **0 sorry** (was conditional, now unconditional)
- `theta_stirling_expansion` becomes provable (~50 more lines of wiring)
- Project sorry count drops from **13 → 12** immediately, with path to **≤ 8**
  via downstream wiring through `ErrorTermExpansion.lean`

---

*Repo*: `/Users/john.n.dvorak/Documents/Git/Littlewood_Proof/`
*Mathlib pin*: `fdddb3ea2c8c` (v4.27.0-rc1 compatible)
*Build*: `lake build` — 0 errors, 13 sorry warnings currently
