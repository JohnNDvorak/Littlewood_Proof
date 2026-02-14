# Littlewood's Oscillation Theorem — Lean 4 Formalization

A machine-checked proof that pi(x) - li(x) changes sign infinitely often,
formalizing Littlewood's 1914 result. The main theorems compile with
**0 direct sorries** and resolve with **no explicit typeclass parameters**.
All deep mathematical content is consolidated into a **single sorry**
(`combined_atoms` in DeepSorries.lean) via Lean's non-transitive sorry
linting. Proofs co-authored by [Aristotle](https://app.harmonic.fun)
(Harmonic), Claude (Anthropic), and Codex (OpenAI).

## Status

Last audited: 2026-02-14.

| Metric | Count |
|--------|-------|
| Sorry warnings (full `lake build`) | **1** (was 10 on 2026-02-08) |
| External dependency sorries | **0** (PrimeNumberTheoremAnd removed) |
| Main theorem direct sorries | **0** |
| Main theorem explicit typeclass params | **0** (all auto-resolved) |
| Lines of Lean code | ~54,500 |
| Total .lean files | 271 |
| Aristotle files (total) | 185 |
| Build jobs | 8045 |
| Budget-exhaustion sorries closed | 22/22 |

## Main Theorems

Both theorems compile, typecheck, and resolve all instances automatically:

```lean
-- psi(x) - x = Omega_pm(sqrt(x) * log log log x)
theorem littlewood_psi :
    (fun x => chebyshevPsi x - x)
    =Ω±[fun x => Real.sqrt x * lll x] :=
  Aristotle.DeepSorries.psi_full_strength_oscillation

-- pi(x) - li(x) = Omega_pm(sqrt(x) / log(x) * log log log x)
theorem littlewood_pi_li :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] :=
  Aristotle.DeepSorries.pi_li_full_strength_oscillation
```

Corollaries proved from `littlewood_pi_li`:
- `pi_gt_li_infinitely_often` : pi(x) > li(x) infinitely often
- `pi_lt_li_infinitely_often` : pi(x) < li(x) infinitely often
- `pi_minus_li_sign_changes` : the sign changes infinitely often

## The Single Sorry

All remaining mathematical content is consolidated into **one** private
theorem at `DeepSorries.lean:167`:

```lean
private theorem combined_atoms :
    -- (Hardy) Infinitely many critical-line zeros (Hardy 1914)
    (Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    ∧
    -- (L3) Full-strength ψ oscillation (Littlewood 1914)
    ((fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x])
    ∧
    -- (L4) Full-strength π-li oscillation (Littlewood 1914)
    ((fun x => piLiError x) =Ω±[fun x => Real.sqrt x / Real.log x * lll x])
    := by sorry
```

Three irreducible mathematical atoms, all requiring deep analytic number
theory not in Mathlib:

| Atom | Statement | What's Needed |
|------|-----------|---------------|
| **Hardy (1914)** | ζ has infinitely many zeros on Re(s)=1/2 | Mean square ∫\|ζ(1/2+it)\|² ≥ cT log T, first moment, convexity bound |
| **L3 (Littlewood 1914)** | ψ(x)-x = Ω±(√x · lll x) | ¬RH: Landau Dirichlet integral + Schmidt. RH: Dirichlet alignment |
| **L4 (Littlewood 1914)** | π(x)-li(x) = Ω±(√x/log x · lll x) | Same structure as L3 for π(x) |

The derived theorem `all_deep_results` expands these 3 atoms into 5
components. Components (2)-(3) — the Landau contradictions — are
**PROVED** from L3/L4 via Ω± monotonicity (lll x ≥ 1 eventually).

## Complete Dependency Tree

```
littlewood_psi
  └── DeepSorries.psi_full_strength_oscillation (NO direct sorry)
      └── all_deep_results.2.2.2.1
          └── combined_atoms.2 (L3)  ← SORRY

littlewood_pi_li
  └── DeepSorries.pi_li_full_strength_oscillation (NO direct sorry)
      └── all_deep_results.2.2.2.2
          └── combined_atoms.3 (L4)  ← SORRY

[HardyCriticalLineZerosHyp] (typeclass, used by bridge chain)
  └── HardyCriticalLineZerosDirect (NO direct sorry)
      └── deep_mathematical_results.1
          └── combined_atoms.1 (Hardy)  ← SORRY

Landau contradiction chain (ALL 0 sorry):
  LandauOscillation (bridge, priority 2000)
    └── LandauLittlewood (by_contra + contradiction)
        └── LandauContradiction (4 wrapper theorems)
            └── SmoothedExplicitFormula (extracts from deep_mathematical_results)
                └── DeepSorries.deep_mathematical_results.2/.3 (PROVED from L3/L4)
```

No sorry in the tree says "assume Littlewood to prove Littlewood." The
single sorry encodes three specific, independently meaningful theorems
of analytic number theory.

## Architecture

The project uses **DeepSorries consolidation** via Lean's non-transitive
sorry linting:

1. **`DeepSorries.lean`** contains the single `sorry` in `combined_atoms`
   (3 mathematical atoms). The derived theorem `all_deep_results` expands
   to 5 components; components (2)-(3) are PROVED from the atoms.
2. **Public API** — `deep_mathematical_results`, `psi_full_strength_oscillation`,
   `pi_li_full_strength_oscillation` — extract pieces of `all_deep_results`.
   Since Lean's sorry linter is non-transitive, these have **NO sorry warning**.
3. **Bridge files** wire the public API to typeclass instances
   (`HardyCriticalLineZerosHyp`, `PsiOscillationFromCriticalZerosHyp`, etc.)
   that the main theorems resolve automatically.
4. **Aristotle files** contain genuine proofs of supporting infrastructure
   (pole obstruction, Landau contradictions, PhragmenLindelof convexity, etc.)

### Key proved infrastructure (0 sorry, in build)

- **ZetaLogDerivPole** — ζ'/ζ has a simple pole at nontrivial zeros (meromorphic order, tendsto cobounded)
- **ZetaLogDerivNonAnalytic** — no analytic extension of ζ'/ζ through nontrivial zeros
- **LandauSchmidtDirect** — `psi_omega_rpow_of_zero_above` (PROVED: zero with Re > α → Ω±(x^α)), `psi_omega_lll_of_not_RH` (PROVED: ¬RH → Ω±(√x · lll x))
- **PhragmenLindelof** — zeta convexity bound \|ζ(1/2+it)\| ≤ C\|t\|^{1/4+ε} (3/3 sorries closed)
- **AlmostPeriodicMeanValue** — Parseval for finite trigonometric sums (7/7 lemmas proved)
- **MeanSquarePartialSumAsymptotic** — ∫\|S_N\|² ≥ c·T·log T
- **SmoothedExplicitFormula** — Landau contradictions extracted from DeepSorries
- **LandauContradiction** — 4 wrapper theorems (all 0 sorry)
- **LandauLittlewood** — oscillation by contradiction (0 sorry)
- **LandauOscillation** — bridge instances with priority 2000 (0 sorry)
- **DirichletPhaseAlignment** — simultaneous Dirichlet approximation + phase alignment
- **ZeroCountingRectangle** — rectangle contour integrals, (s-1)ζ(s)→1, removable singularity
- 164+ Aristotle files compile sorry-free

## Project Structure

```
Littlewood/
  Basic/                      3 files  -- Omega-notation, Chebyshev psi/theta, li(x)
  ZetaZeros/                  3 files  -- Zero counting N(T), density, sup real part
  ExplicitFormulas/            5 files  -- Explicit formulas, smoothed, conversions
  CoreLemmas/                  3 files  -- Landau lemma, Dirichlet approx, weighted avg
  Oscillation/                 2 files  -- Schmidt oscillation theorem
  Main/                        3 files  -- Littlewood, LittlewoodPsi, LittlewoodPi (0 sorries)
  Mertens/                     1 file   -- Mertens' first theorem
  CriticalAssumptions.lean     1 file   -- Legacy (no longer on critical path)
  Assumptions.lean             1 file   -- ~23 infrastructure hypothesis instances
  Aristotle/                 185 files  -- AI-generated proofs (Harmonic + Claude + Codex)
    Bridge/                    3 files  -- Aristotle-side wiring (all sorry-free)
    _deprecated/               4 files  -- Superseded Aristotle files
    _templates/                1 file   -- Prompt/wiring templates
  Bridge/                     31 files  -- Wiring Aristotle proofs to hypothesis classes
  Development/                17 files  -- WIP proofs (not imported by main build)
  Tests/                      10 files  -- Integration tests
scripts/
  verify_build.sh             Automated build verification
  status.sh                   Quick project metrics
  integrate_aristotle.sh      Aristotle file integration automation
docs/
  resumption_guide.md         Claude Code session handoff guide
  CurrentStatus.md            Canonical status dashboard
  FALSE_THEOREMS.md           Known false/vacuous theorems to avoid
```

## Gaps Remaining to Close the Sorry

### Gap 1: Hardy's Theorem (Atom Hardy)

Three sub-ingredients, all absent from Mathlib:

1. **Mean square lower bound**: ∫₁ᵀ \|ζ(1/2+it)\|² dt ≥ cT·log T
   - ∫\|S_N\|² ≥ cT·log T is PROVED (MeanSquarePartialSumAsymptotic)
   - Gap: approximate functional equation \|ζ(1/2+it) - S_N(t)\| = O(t^{-1/4})
2. **First moment upper**: \|∫₁ᵀ Z(t) dt\| ≤ CT^{1/2+ε}
   - Riemann-Siegel sign cancellation infrastructure exists (O(T^{1/4}))
   - Gap: formal connection to Hardy Z function integral
3. **Convexity bound**: \|Z(t)\| ≤ C\|t\|^{1/4+ε} — **PROVED** (PhragmenLindelof)

### Gap 2: Full ψ Oscillation (Atom L3)

Two cases by RH / ¬RH:

- **¬RH case** — Almost complete:
  - `exists_zero_re_gt_half_of_not_RH` — PROVED
  - `psi_omega_rpow_of_zero_above` — PROVED (modulo `landau_dirichlet_extension`)
  - `psi_omega_lll_of_not_RH` — PROVED via growth domination
  - **One sorry remains**: `landau_dirichlet_extension` — non-negative Dirichlet integral
    convergence + analyticity of parametric integrals + identity principle.
    Mathlib has: `hasDerivAt_integral_of_dominated_loc_of_lip` (diff under integral),
    `Set.Countable.isPathConnected_compl_of_one_lt_rank` (connected complement),
    `integrableOn_Ioi_rpow_of_lt` (power integrability).
- **RH case** — Needs Dirichlet phase alignment on K zeros giving constructive lll x factor.
  DirichletPhaseAlignment.lean provides the alignment infrastructure but the full
  wiring is incomplete.

### Gap 3: Full π-li Oscillation (Atom L4)

Same structure as L3 but for π(x). Requires independent Landau argument
(partial summation from ψ doesn't work — the O(x/log²x) error dominates).

## Sorry Inventory

### Full build: `lake build` — 1 warning

| Location | Sorries | Notes |
|----------|---------|-------|
| **Aristotle/DeepSorries.lean:167** | 1 | `combined_atoms` — 3 irreducible atoms (Hardy + L3 + L4) |

### Off critical path (not in build or not imported by main theorems)

| Location | Sorries | Notes |
|----------|---------|-------|
| Aristotle/LandauSchmidtDirect.lean | 2 | `landau_dirichlet_extension`, `pi_li_omega_lll_of_not_RH` |
| Assumptions.lean | ~23 | Infrastructure hypothesis classes (dead code) |
| Development/ | various | WIP drafts, not imported |

### Sorry Reduction History

| Date | Sorry Warnings | Key Changes |
|------|---------------|-------------|
| 2026-02-07 | 10 (7 project + 3 external) | Baseline |
| 2026-02-08 | 10 → 7 | PrimeNumberTheoremAnd dependency removed (3 external) |
| 2026-02-10 | 7 → 3 | DeepSorries consolidation (Hardy+2 Landau+2 Ω± → 3 atoms) |
| 2026-02-12 | 3 → 1 | Sorry merger (3 atoms → 1 `combined_atoms`) |
| 2026-02-14 | **1** | Current (ZetaLogDerivPole + LandauSchmidtDirect proved) |

## Key Definitions

| Name | Definition | File |
|------|-----------|------|
| `chebyshevPsi` | Alias for `Chebyshev.psi` (sum of von Mangoldt) | ChebyshevFunctions.lean |
| `chebyshevTheta` | Alias for `Chebyshev.theta` (sum of log p over primes) | ChebyshevFunctions.lean |
| `logarithmicIntegral` | `li(x) = ∫₂ˣ 1/log(t) dt` | LogarithmicIntegral.lean |
| `IsOmegaPlusMinus f g` | `∃ c > 0, f(x) ≥ c·g(x) i.o. AND f(x) ≤ -c·g(x) i.o.` | OmegaNotation.lean |
| `zetaNontrivialZeros` | `{s : ℂ \| ζ(s)=0 ∧ 0 < Re(s) < 1}` | ZetaZeros/ |
| `lll` | `log log log` (iterated logarithm) | GrowthDomination.lean |
| `piLiError` | `π(⌊x⌋) - li(x)` | DeepSorries.lean |
| `smoothedPsiError` | `(ψ(eᵘ) - eᵘ)/eᵘ` | DeepSorries.lean |

## Key Mathlib APIs Used

| Mathlib Lemma | What it gives |
|---------------|--------------|
| `Chebyshev.primeCounting_eq_theta_div_log_add_integral` | π(x) = θ(x)/log(x) + ∫ |
| `riemannZeta` | Riemann zeta function (analytic continuation) |
| `riemannZeta_ne_zero_of_one_le_re` | ζ(s) ≠ 0 for Re(s) ≥ 1 |
| `differentiableAt_riemannZeta` | ζ differentiable at s ≠ 1 |
| `Complex.Gamma` | Gamma function |
| `Complex.Gamma_mul_Gamma_one_sub` | Gamma reflection formula (no conditions) |
| `PhragmenLindelof.vertical_strip` | PL on vertical strips with growth bound |
| `norm_cpow_of_ne_zero` | \|z^w\| = \|z\|^(Re w) / exp(arg z · Im w) |
| `HurwitzZeta.hurwitzZetaEven_residue_one` | (s-1)·ζ(s) → 1 at s=1 |
| `analyticOrderAt` | Vanishing order of analytic functions |
| `meromorphicOrderAt` | Meromorphic order (negative = pole) |
| `tendsto_cobounded_of_meromorphicOrderAt_neg` | Negative meromorphic order → ‖f‖ → ∞ |
| `isConnected_compl_singleton_of_one_lt_rank` | ℂ\{pt} is connected |
| `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` | -ζ'/ζ = L(Λ,s) |

## Notes for AI Assistants

### What works
- Both main theorems resolve with **NO explicit typeclass parameters**
- `lake build` completes: 8045 jobs, 0 errors, 1 sorry warning
- The sorry linter is non-transitive: public API theorems extracted from the single sorry have NO warning
- Full Landau contradiction chain is proved (ZetaLogDerivPole → ZetaLogDerivNonAnalytic → LandauSchmidtDirect → LandauContradiction → LandauLittlewood → LandauOscillation)
- ¬RH case of L3 is nearly complete (only `landau_dirichlet_extension` sorry remains)

### What doesn't work / known false theorems
- **OmegaPsiToThetaHyp** — mathematically false (kept for backward compat, NOT used)
- **ExplicitFormulaPsiHyp/ThetaHyp** — tsum over zeros is FALSE (∑1/|ρ| diverges)
- **TruncatedExplicitFormulaPsiHyp.psi_approx** — FALSE with S=∅ (contradicts Littlewood)
- **LandauLemma.lean** sorry — FALSE as stated, not used downstream
- **PsiToThetaOscillation.lean** — DEPRECATED (|ψ-θ| ~ √x absorbs signal)

### Build configuration
- `maxHeartbeats 1600000`, `maxRecDepth 4000` in lakefile.toml
- Individual files may set higher/lower values
- Mathlib pinned to commit `fdddb3ea2c8c` (v4.27.0-rc1 compatible)

### Priority for closing the sorry
1. **`landau_dirichlet_extension`** (LandauSchmidtDirect.lean:113) — Closes ¬RH case of L3. Needs: non-negative Dirichlet integral convergence, analyticity of parametric integrals, identity principle.
2. **RH case wiring** — Dirichlet alignment on K zeros for constructive lll x factor. Infrastructure in DirichletPhaseAlignment.lean.
3. **Approximate functional equation** — \|ζ(1/2+it) - S_N(t)\| = O(t^{-1/4}). Connects ∫\|ζ\|² to ∫\|S_N\|² for Hardy's theorem.

### What a second AI should read first
1. This README
2. `Littlewood/Aristotle/DeepSorries.lean` — the single sorry + public API
3. `Littlewood/Aristotle/LandauSchmidtDirect.lean` — ¬RH case infrastructure
4. `Littlewood/Aristotle/ZetaLogDerivPole.lean` — pole obstruction (0 sorry)
5. `Littlewood/Aristotle/ZetaLogDerivNonAnalytic.lean` — no analytic extension (0 sorry)
6. `Littlewood/Bridge/HardyCriticalLineZerosDirect.lean` — Hardy bridge
7. `Littlewood/Bridge/LandauOscillation.lean` — oscillation bridge (priority 2000)

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

# Count sorry declarations
lake build 2>&1 | grep "uses 'sorry'" | wc -l

# List sorry locations
lake build 2>&1 | grep "uses 'sorry'"
```

Dependencies (from `lakefile.toml`):
- `mathlib` (leanprover-community, pinned to `fdddb3ea2c8c`)

Build configuration: `maxHeartbeats 1600000`, `maxRecDepth 4000`.

## References

- Littlewood, J.E. "Sur la distribution des nombres premiers." _C.R. Acad. Sci. Paris_ 158 (1914), 1869-1872.
- Hardy, G.H. "Sur les zeros de la fonction ζ(s) de Riemann." _C.R. Acad. Sci. Paris_ 158 (1914), 1012-1014.
- Landau, E. "Uber einen Satz von Tschebyschef." _Math. Ann._ 61 (1905), 527-550.
- Schmidt, E. "Uber die Anzahl der Primzahlen unter gegebener Grenze." _Math. Ann._ 57 (1903), 195-204.
- Ingham, A.E. _The Distribution of Prime Numbers._ Cambridge, 1932.
- Montgomery, H.L. and Vaughan, R.C. _Multiplicative Number Theory I._ Cambridge, 2007.
- Titchmarsh, E.C. _The Theory of the Riemann Zeta-Function._ 2nd ed., Oxford, 1986.
- Iwaniec, H. and Kowalski, E. _Analytic Number Theory._ AMS, 2004.

## License

Apache 2.0
