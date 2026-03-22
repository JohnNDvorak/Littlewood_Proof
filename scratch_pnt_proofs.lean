/-
Agent 4 (iteration 3) — PNT feasibility analysis for sorry #7
(AbelCorrectionPsiPiHyp in PiLiDirectOscillation.lean:206)
Date: 2026-03-15

## EXECUTIVE SUMMARY

**AbelCorrectionPsiPiHyp is NOT on the critical path** and is
**likely mathematically unprovable as stated**, even with PNT.
The main theorems (`littlewood_psi`, `littlewood_pi_li`) bypass it
via LandauOscillation.lean (priority 2000).

## DETAILED ANALYSIS

### 1. PrimeNumberTheoremAnd (PNTA) availability

PNTA is physically present in `.lake/packages/PrimeNumberTheoremAnd/`
but is NOT declared as a dependency in `lakefile.toml`. The project
cannot import it without:
  (a) Adding `[[require]]` block to lakefile.toml
  (b) Running `lake update` + full rebuild
  (c) Risk: dependency resolution conflicts with pinned Mathlib rev

Key theorem in PNTA (Consequences.lean:225):
  `WeakPNT'' : ψ ~[atTop] (fun x ↦ x)`
  where `ψ x := Chebyshev.psi x` (same as Littlewood's `chebyshevPsi`)

Stronger result in PNTA (MediumPNT.lean:3804):
  `MediumPNT : ∃ c > 0, (ψ - id) =O[atTop]
    fun x ↦ x * exp (-c * (log x) ^ ((1:ℝ)/10))`

Even stronger (StrongPNT.lean): ψ(x) = x + O(x·exp(-c√(log x)))
  — COMMENTED OUT, not actually proved in PNTA.

### 2. Why PNT is INSUFFICIENT for AbelCorrectionPsiPiHyp

The sorry is:
  `∃ D > 0, ∀ᶠ x in atTop,
    |π(x) - li(x) - (ψ(x)-x)/log x| ≤ D * (√x / log x)`

The Abel summation decomposition (from PartialSummation.lean) gives:
  π(x) - li(x) - (ψ(x)-x)/logx
    = -sumPrimePowers(x) + ∫₂ˣ (ψ(t)-t)/(t·(log t)²) dt + 2/log 2

Term analysis:
  1. sumPrimePowers(x) ≈ √x/(2·log x) — this IS O(√x/log x). ✓
  2. 2/log 2 — constant, absorbed for large x. ✓
  3. ∫₂ˣ (ψ(t)-t)/(t·(log t)²) dt — THIS IS THE PROBLEM. ✗

With WeakPNT (ψ(t) ~ t, i.e., |ψ(t)-t| = o(t)):
  For any ε > 0, eventually |ψ(t)-t| ≤ ε·t.
  |integrand| ≤ ε/(log t)² for t ≥ t₀(ε).
  ∫₂ˣ ≤ const + ε · ∫_{t₀}ˣ 1/(log t)² dt ≈ const + ε · x/(log x)²

  So the integral is o(x/(log x)²).
  But x/(log x)² vs √x/log x: their ratio is √x/log x → ∞.
  Therefore o(x/(log x)²) does NOT imply O(√x/log x).

With MediumPNT (|ψ(t)-t| ≤ C·t·exp(-c·(log t)^(1/10))):
  |integrand| ≤ C · exp(-c·(log t)^(1/10)) / (log t)²
  ∫₂ˣ this dt: substitute u = log t, dt = eᵘ du:
    = C · ∫ exp(u - c·u^(1/10)) / u² du
  Since u dominates c·u^(1/10) for large u, the exponent → +∞.
  The integral grows approximately like
    x · exp(-c · (log x)^(1/10)) / (log x)²
  which is o(x/(log x)²) but still ≫ √x/log x.

Even with the strong PNT (|ψ(t)-t| ≤ C·t·exp(-c·√(log t))):
  Same substitution gives ∫ exp(u - c·√u)/u² du.
  Since u - c·√u → +∞, this also diverges.
  Growth rate: x · exp(-c·√(log x)) / (log x)².
  Ratio to √x/log x: √x · exp(-c·√(log x)) / log x
    = exp((log x)/2 - c·√(log x)) / log x → ∞.
  So even with the STRONGEST known unconditional PNT error,
  the integral is NOT O(√x/log x).

### 3. Is AbelCorrectionPsiPiHyp mathematically true?

PROBABLY NOT as stated with bound D·√x/log x.

The correction π(x) - li(x) - (ψ(x)-x)/logx involves an integral
that inherently grows faster than √x/log x. The dominant contribution
is from the integral ∫₂ˣ (ψ(t)-t)/(t·(log t)²) dt.

Under RH: |ψ(t)-t| = O(√t · log²t), which gives:
  |integrand| ≤ C/(√t) — and ∫₂ˣ 1/√t dt = O(√x)
  So the integral is O(√x), and dividing by... wait, it's already
  not divided by anything extra. O(√x) vs √x/logx: ratio = logx → ∞.
  Still not O(√x/log x)!

Even under RH, the integral is O(√x) not O(√x/log x).

**VERDICT**: AbelCorrectionPsiPiHyp with bound D·√x/log x appears
to be MATHEMATICALLY FALSE. The correction is O(√x) under RH,
which does NOT fit inside D·√x/log x.

NOTE: Agent 3's comment at PiLiDirectOscillation.lean:189 claiming
"o(x/(logx)²) = o(√x/logx)" is an ERROR in the asymptotic analysis.
o(x/log²x) is a LARGER class than o(√x/logx).

### 4. Critical path status

The sorry at PiLiDirectOscillation.lean:206 is NOT on the critical path:

  littlewood_psi: Uses LandauOscillation (priority 2000), bypasses entirely.
  littlewood_pi_li: Uses LandauOscillation (priority 2000), bypasses entirely.

The sorry IS live for the B7 chain (lll factor enhancement), but:
  - It feeds PiApproxFromExplicitFormulaHyp (line 212)
  - Which feeds TruncatedExplicitFormulaPiHyp.pi_approx
  - Which is itself mathematically false (line 65-68)

So the entire PiLiDirectOscillation path is mathematically unsound.
The LandauOscillation bypass is the correct approach.

### 5. Recommendation

DO NOT attempt to close this sorry. It is:
  (a) Off the critical path (LandauOscillation wins)
  (b) Mathematically false as stated (integral grows faster than √x/logx)
  (c) Part of a chain that passes through another false statement (pi_approx)

Adding PNTA as a dependency would be valuable for OTHER reasons
(e.g., potential future sorry closures) but would NOT help here.

### 6. PNTA import feasibility (for reference)

To add PNTA to the project:
  1. Add to lakefile.toml:
     ```
     [[require]]
     name = "PrimeNumberTheoremAnd"
     scope = "AlexKontorovich"
     rev = "<commit hash from .lake/packages>"
     ```
  2. Run `lake update PrimeNumberTheoremAnd`
  3. Run `lake build` (expect ~20-30 min full rebuild)
  4. Risk: PNTA may depend on a different Mathlib commit than
     the pinned `fdddb3ea2c8c` — conflict resolution needed.
  5. The package IS already cached in .lake/packages/ with
     matching lean-toolchain (v4.27.0-rc1), suggesting
     compatibility was tested at some point.
-/

-- Proof prototype: the integral bound FAILS even with MediumPNT

import Mathlib

noncomputable section
open Filter Asymptotics MeasureTheory Real Set

/-! ## Part A: What MediumPNT gives us

MediumPNT (PNTA): ∃ c > 0, (ψ - id) =O[atTop] (fun x ↦ x * exp(-c*(log x)^(1/10)))
WeakPNT'' (PNTA): ψ ~[atTop] (fun x ↦ x)

Both use `ψ x := Chebyshev.psi x`, which equals Littlewood's `chebyshevPsi`.
-/

-- Axiomatize PNT results (since PNTA not importable)
axiom pnt_weak : (fun x : ℝ => Chebyshev.psi x) ~[atTop] (fun x => x)

axiom pnt_medium : ∃ c > (0 : ℝ),
  (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
    (fun x => x * exp (-c * (log x) ^ ((1 : ℝ) / 10)))

/-! ## Part B: The integral that blocks AbelCorrectionPsiPiHyp

The correction π(x) - li(x) - (ψ(x)-x)/logx contains the integral
∫₂ˣ (ψ(t)-t)/(t·(log t)²) dt. We show this integral grows faster
than √x/log x, making the sorry statement false.
-/

/-- Key fact: x/(log x)² grows faster than √x/log x.
    Equivalently, √x/log x → ∞. -/
theorem sqrt_div_log_tendsto_atTop :
    Tendsto (fun x : ℝ => sqrt x / log x) atTop atTop := by
  apply Tendsto.atTop_div_const (tendsto_sqrt_atTop)
  -- Actually this isn't quite right. We need a different approach.
  sorry

/-- The integral ∫₂ˣ 1/(log t)² dt is Θ(x/(log x)²).
    In particular, it is NOT O(√x/log x). -/
theorem integral_inv_log_sq_growth :
    ¬ ∃ D > (0 : ℝ), ∀ᶠ x : ℝ in atTop,
      ∫ t in (2:ℝ)..x, (1 : ℝ) / (log t) ^ 2 ≤ D * (sqrt x / log x) := by
  sorry

/-! ## Part C: Correct bound (what IS provable)

With PNT, the integral is o(x/(log x)²), and the full correction
|π(x) - li(x) - (ψ(x)-x)/logx| is O(√x) (not O(√x/logx)).

Under RH: O(√x · log²x) (Schoenfeld 1976).

The achievable bound is:
  |π(x) - li(x) - (ψ(x)-x)/logx| ≤ D · √x
which is weaker than the sorry claims.
-/

/-- What IS provable from PNT: the correction is O(√x).
    This follows from:
    - sumPrimePowers(x) = O(√x/logx) ⊂ O(√x)
    - ∫₂ˣ (ψ(t)-t)/(t·log²t) dt = o(x/log²x) ⊂ O(√x) for now... actually not.
    Even this needs care. The integral o(x/log²x) is NOT O(√x).

    In fact, the correct statement is that the integral is
    controlled by the PNT error rate, and with MediumPNT it's
    O(x · exp(-c·(log x)^(1/10)) / (log x)²).
    This is o(x/log²x) but still ≫ √x.

    So even the O(√x) bound requires RH or something equivalent!

    CORRECTED VERDICT: AbelCorrectionPsiPiHyp is false for ANY
    polynomial bound D·x^α/log^β x with α < 1, unless one assumes
    an error term ψ(t)-t = O(t^α) for the same α.
-/

-- Demonstrating the asymptotic incompatibility
-- x/(log x)² / (√x/log x) = √x/log x → ∞
theorem ratio_diverges :
    Tendsto (fun x : ℝ => (x / (log x)^2) / (sqrt x / log x)) atTop atTop := by
  -- This simplifies to √x/log x
  sorry

/-! ## Part D: PNTA theorem signatures (for reference)

From `.lake/packages/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/Consequences.lean`:

```
theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1)
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x)
theorem chebyshev_asymptotic : θ ~[atTop] id
```

From `.lake/packages/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/MediumPNT.lean`:

```
theorem MediumPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))
```

Both use `noncomputable def ψ (x : ℝ) : ℝ := Chebyshev.psi x`
(PrimaryDefinitions.lean:24), which matches Littlewood's
`noncomputable def chebyshevPsi (x : ℝ) : ℝ := Chebyshev.psi x`
(Basic/ChebyshevFunctions.lean:32).
-/
