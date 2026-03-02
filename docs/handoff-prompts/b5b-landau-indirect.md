# Handoff Prompt: B5b via Landau Indirect Argument + Interface Refactoring

## Overview

This prompt replaces the original "inhomogeneous Dirichlet approximation" task. That approach required the Linear Independence conjecture for zeta zero ordinates (an open problem). Instead, we use **Landau's indirect argument** to prove ψ(x) - x = Ω±(√x) directly, which is sufficient for Littlewood's theorem and requires no Diophantine hypotheses.

**This task has two parts:**
1. **Interface refactoring**: Weaken `PsiZeroSumOscillationHyp` and its downstream consumers from `Ω±(4√x·lll(x))` to `Ω±(√x)`
2. **Proof**: Fill in the B5b sorry using Landau's indirect argument

## Why The Weakening Is Safe

The downstream chain immediately discards the lll(x) factor:
```
PsiZeroSumOscillationHyp [Ω±(4√x·lll(x))]
  → combined_atoms [Ω±(√x·lll(x))]
    → littlewood_psi [Ω±(√x·lll(x))]
      → littlewood_psi_sqrt [Ω±(√x)]    ← via of_eventually_ge, since √x ≤ √x·lll(x)
        → ALL final corollaries (sign changes, etc.)
```

Every downstream consumer uses `littlewood_psi_sqrt`, not `littlewood_psi`. The lll factor is dead weight. The π-li chain is fully independent (already proved, 0 sorry) and keeps its own lll factor.

## Part 1: Interface Changes (9 files)

### File 1: `Littlewood/Aristotle/Standalone/ExplicitFormulaAndOscillationFromSubSorries.lean`

**Line 105-110** — Change `PsiZeroSumOscillationHyp`:
```lean
-- BEFORE:
class PsiZeroSumOscillationHyp : Prop where
  proof : ZetaZeros.RiemannHypothesis →
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      psiMainTerm x ≥ 4 * (Real.sqrt x * lll x)) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      psiMainTerm x ≤ -(4 * (Real.sqrt x * lll x)))

-- AFTER:
class PsiZeroSumOscillationHyp : Prop where
  proof : ZetaZeros.RiemannHypothesis →
    (∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≥ C * Real.sqrt x) ∧
    (∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≤ -(C * Real.sqrt x))
```

**Key change:** Operates on `chebyshevPsi x - x` directly (not `psiMainTerm`). Quantifies over all constants C (the Landau argument gives unbounded oscillation). This bypasses the psiMainTerm decomposition entirely.

**Line 118-121** — Change `explicitFormulaAndOscillationHyp_proved`:
The assembly theorem pairs B5a and B5b. Part 2 of ExplicitFormulaAndOscillationHyp must match the new PsiZeroSumOscillationHyp format.

### File 2: `Littlewood/Aristotle/Standalone/RHPsiWitnessFromZeroSum.lean`

**Lines 68-78** — Change `ExplicitFormulaAndOscillationHyp`:
Part 2 must match the new PsiZeroSumOscillationHyp (operates on chebyshevPsi, quantifies over C).

**Lines 82-181** — Simplify or remove intermediate lemmas:
- `explicit_formula_and_oscillation` — type changes
- `psiMainTerm_oscillates_large` — **REMOVE** (no longer needed; psiMainTerm not used in the oscillation path)
- `log_pow3_eventually_le_sqrt_mul_lll` — may still be needed for error bound

**Lines 192-224** — Rewrite `rh_psi_minus_x_oscillates_large`:
The current proof subtracts psiMainTerm oscillation from error to get ψ-x oscillation. With the new B5b, ψ-x oscillation is given DIRECTLY. The new proof is trivial: just extract Part 2 from the hypothesis.

**Lines 233-270** — Rewrite `rh_psi_main_term_oscillates`:
Currently derives psiMain oscillation from ψ-x oscillation. Simplify: given ψ-x oscillates ±C√x and |(ψ-x) + psiMain| ≤ (log x)³, conclude psiMain oscillates ±(C-1)√x for large enough x. Use C=2 to get psiMain oscillates ±√x.

**Lines 280-284** — Adjust `rhPsiWitness_proved`:
Output needs to match the (updated) RhPsiWitnessData.

### File 3: `Littlewood/Aristotle/Standalone/CombinedAtomsFromDeepBlockers.lean`

**Lines 30-38** — Change `RhPsiWitnessData`:
```lean
-- BEFORE:
def RhPsiWitnessData : Prop :=
  ∀ (_hRH : ZetaZeros.RiemannHypothesis),
    ∃ psiMain : ℝ → ℝ,
      (∀ᶠ x in atTop,
        |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧
        psiMain x ≤ -(2 * (Real.sqrt x * lll x))) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧
        2 * (Real.sqrt x * lll x) ≤ psiMain x)

-- AFTER:
def RhPsiWitnessData : Prop :=
  ∀ (_hRH : ZetaZeros.RiemannHypothesis),
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x]
```

This is much simpler: the RH branch just needs to provide Ω±(√x) for ψ-x.

### File 4: `Littlewood/Aristotle/Standalone/DeepBlockerAssembly.lean`

**Lines 131-151** — Change `combined_atoms_from_five_blockers` output type:
Replace `(fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x]`
with `(fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x]`.
The proof body at line 150-151 may need adjustment.

### File 5: `Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean`

**Lines 132-146** — Update docstrings for B5b and B5.
**Line 469-471** — `rhPsiWitness` needs to produce the new format.
**Lines 687-697** — `combined_atoms_resolved_unconditional` output type changes (ψ part only).

### File 6: `Littlewood/Aristotle/DeepSorries.lean`

**Lines 235-250** — `combined_atoms`: change ψ output from `√x * lll x` to `√x`.
**Lines 261-317** — `all_deep_results`:
  - Component (4) changes from `√x * lll x` to `√x`
  - Component (2) Landau ψ contradiction: currently uses `of_eventually_ge` to downgrade lll → becomes trivial identity
**Lines 340-343** — `psi_full_strength_oscillation`: changes to `=Ω±[fun x => Real.sqrt x]`

### File 7: `Littlewood/Main/LittlewoodPsi.lean`

**Lines 46-49** — `littlewood_psi`: change to `=Ω±[fun x => Real.sqrt x]`
**Lines 53-58** — `littlewood_psi_sqrt`: becomes trivially `littlewood_psi` (or keep as alias)
Remove the `of_eventually_ge sqrt_eventually_le_sqrt_mul_lll` call.

### File 8: `Littlewood/Main/LittlewoodPi.lean`

**No changes needed.** The π-li chain is independent and keeps its own lll factor.

### File 9: `Littlewood/Aristotle/Standalone/PsiZeroSumOscillationFromIngham.lean`

**Lines 122-141** — Replace sorry proof with Landau indirect argument (Part 2 below).

---

## Part 2: The Proof (Landau Indirect Argument)

### Target

Fill in the sorry in `psiZeroSumOscillation_proved` (PsiZeroSumOscillationFromIngham.lean).

After the interface change, the goal becomes:

```lean
theorem psiZeroSumOscillation_proved
    [ExplicitFormulaPsiGeneralHyp] :
    PsiZeroSumOscillationHyp where
  proof := by
    intro hRH
    constructor
    · -- ∀ C X, ∃ x > X, chebyshevPsi x - x ≥ C * √x
      intro C X
      sorry  -- ← FILL THIS
    · -- ∀ C X, ∃ x > X, chebyshevPsi x - x ≤ -(C * √x)
      intro C X
      sorry  -- ← FILL THIS
```

### Mathematical Proof (Landau 1905 / Ingham 1932)

**Positive direction: ψ(x) - x takes arbitrarily large values relative to √x.**

Proof by contradiction. Fix C > 0. Assume ψ(x) - x ≤ C√x for all x ≥ x₀.

**Step 1:** From the explicit formula (B5a), for x ≥ 2, T ≥ 2:
```
|ψ(x) - x + ∑_{|γ|≤T} Re(x^ρ/ρ)| ≤ K · (√x · (log T)²/√T + (log x)²)
```

**Step 2:** Under the assumption ψ(x) - x ≤ C√x and using the explicit formula at T = x:
```
-∑_{|γ|≤x} Re(x^ρ/ρ) ≤ C√x + K(log x)²
```
So the zero sum is bounded below.

**Step 3:** The key Landau-Ingham observation:

Consider the function:
```
F(s) = ∑_p (log p) · p^{-s} = -ζ'(s)/ζ(s) - analytic terms
```

If ψ(x) - x ≤ C√x for all large x, then ψ(x) = O(x), so the Dirichlet series for ψ converges for Re(s) > 1. The Mellin/Stieltjes transform:
```
∫₁^∞ (C√x - (ψ(x) - x)) x^{-s-1} dx
```
converges absolutely for Re(s) > 1/2 (since the integrand is O(x^{1/2-s})).

This gives C/(s - 1/2) + ζ'(s)/ζ(s) + 1/(s-1) + (analytic) is holomorphic for Re(s) > 1/2.

**Step 4:** But under RH, ζ has zeros at ρ = 1/2 + iγ, so ζ'/ζ has POLES at those points. A function cannot be both holomorphic and have poles in the half-plane Re(s) > 1/2.

Specifically, at ρ₀ = 1/2 + iγ₀ (any zero on the critical line):
- ζ'/ζ has a pole of order equal to the multiplicity of the zero
- C/(s-1/2) has a simple pole at s = 1/2 (real axis only)
- If γ₀ ≠ 0, the pole of ζ'/ζ at 1/2 + iγ₀ is NOT cancelled

This contradicts the convergence of the integral for Re(s) > 1/2. □

The **negative direction** is symmetric: assume ψ(x) - x ≥ -C√x, then ∫₁^∞ ((ψ(x)-x) + C√x) x^{-s-1} dx converges for Re(s) > 1/2, giving the same contradiction.

### Lean Proof Strategy

The full Landau argument via Mellin transforms is difficult to formalize. Here is a more Lean-friendly approach using only the explicit formula:

**Approach: Explicit formula + unbounded zero sum**

1. Under RH, there are infinitely many critical-line zeros (Hardy's theorem, already proved)
2. The explicit formula at T = x gives: ψ(x) - x ≈ -∑_{|γ|≤x} Re(x^ρ/ρ) ± O((log x)²)
3. Under RH with ρ = 1/2+iγ: Re(x^ρ/ρ) = √x · Re(x^{iγ}/(1/2+iγ))
4. **Key claim (sorry-able):** Under RH, for any C > 0 and X > 0, there exists x > X such that |∑_{|γ|≤x} Re(x^ρ/ρ)| ≥ (C+1)√x.
5. At such x: |ψ(x) - x| ≥ (C+1)√x - O((log x)²) ≥ C√x for large x.

For the signed version (both + and -), use conjugate pair symmetry + Hardy's infinitely many zeros.

**Alternative (cleaner for Lean):** Factor the proof as:
1. A local sorry for the Landau-Ingham fact: "under RH with infinitely many critical zeros, ψ(x) - x is unbounded above (and below) relative to √x"
2. All the interface wiring proved

This puts the sorry exactly where the deep analytic number theory lives.

### Available Infrastructure

- `ExplicitFormulaPsiGeneralHyp` (B5a, atomic sorry): general explicit formula with variable T
- `HardyCriticalLineZerosHyp` (proved via Hardy chain): infinitely many critical-line zeros
- `ZetaZeros.RiemannHypothesis`: ∀ ρ ∈ CriticalZeros, ρ.re = 1/2
- `chebyshevPsi`: ψ(x) = ∑_{n≤x} Λ(n)
- `exists_large_x_phases_aligned_finset` (proved): align phases to w=1

### Lean-Specific Gotchas

1. **`relaxedAutoImplicit false` and `autoImplicit false`** — all types explicit
2. **`chebyshevPsi`** has TWO definitions: `Chebyshev.psi` (in Basic/) and `Aristotle.DirichletPhaseAlignment.chebyshevPsi`. They differ by the n=0 term (Λ(0) = 0). The bridge `h_bridge` in RHPsiWitnessFromZeroSum.lean (line 109-115) shows how to convert.
3. **`Ω±` notation**: `f =Ω±[g]` means `IsOmegaPlusMinus atTop f g`. Defined in `Basic/OmegaNotation.lean`.
4. **Filter lemmas**: `filter_upwards`, `eventually_ge_atTop`, `eventually_atTop.1` are heavily used.

## Estimated Size

- Interface changes: ~200 lines of modifications across 8 files
- B5b proof: ~80-150 lines (depending on how much is sorry'd locally)

## Acceptance Criteria

```bash
# Build full project
lake build 2>&1 | grep "declaration uses 'sorry'" | sort -u | wc -l
# Expected: 4 (down from 5 — B5b proof body sorry is eliminated)
# Remaining: B1 (afe_mean_square_bridge), B2 (MainTermFirstMomentBoundHyp),
#            B3 (PerBlockSignedBoundHyp), B5a (ExplicitFormulaPsiGeneralHyp)

# OR if B5b still has a local sorry for the Landau fact:
# Expected: 5 (same as before, but sorry moves from proof-body to cleaner location)

# Verify final theorems still compile
lake build Littlewood.Main.LittlewoodPsi
lake build Littlewood.Main.LittlewoodPi

# Verify the key theorem types
grep -n "littlewood_psi\b" Littlewood/Main/LittlewoodPsi.lean
# Should show: =Ω±[fun x => Real.sqrt x]  (no lll)

grep -n "littlewood_pi_li\b" Littlewood/Main/LittlewoodPi.lean
# Should show: =Ω±[fun x => Real.sqrt x / Real.log x * lll x]  (unchanged)
```

## Execution Order

1. Make ALL interface changes FIRST (files 1-8), replacing lll with √x
2. Build and fix type errors — these should be mechanical
3. Then fill in the B5b proof (file 9)
4. Final build verification

## Note on Prompt #2 (Sum Divergence)

The sum divergence prompt (`sum-divergence.md`) was originally needed for the Ingham phase alignment approach. With the switch to Landau's indirect argument, it is **no longer required** for B5b. However, it remains valid standalone infrastructure and may be useful for future strengthening of the result (if LI is ever proved or assumed).

## References

- Landau, E. (1905). "Über einen Satz von Tschebyschef." *Math. Ann.* 61, 527-550.
- Ingham, A. E. (1932). *The Distribution of Prime Numbers*, Chapter V.
- Montgomery & Vaughan (2007). *Multiplicative Number Theory I*, Theorem 15.11 and §15.2.
- Korevaar, J. (2004). *Tauberian Theory*, §III.4 (Landau-type oscillation theorems).
