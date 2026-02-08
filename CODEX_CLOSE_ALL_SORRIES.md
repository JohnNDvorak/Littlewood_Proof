# Codex Session: Close All 7 Remaining Project Sorries

## Project Context

Lean 4 formalization of Littlewood's oscillation theorem. `lake build` passes
with **10 sorry warnings** (7 project + 3 external). Working tree is clean.

```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
lake build                    # full build, expect 10 sorry warnings
lake build 2>&1 | grep "declaration uses 'sorry'" | wc -l   # should print 10
```

## CRITICAL: Do Not Touch

- `PrimeNumberTheoremAnd/` or `.lake/` — external dependencies
- `Aristotle/_deprecated/` — dead code
- Do NOT use tsum over `zetaNontrivialZeros` — not absolutely convergent (tsum = 0 in Lean)
- Do NOT redefine `chebyshevPsi`/`chebyshevTheta`/`li` at root level — conflicts with `Basic/`
- Do NOT change any theorem statements — only fill in proofs

---

## Sorry Inventory (7 total)

| # | File | Line | Type | Critical Path? | Closability |
|---|------|------|------|----------------|-------------|
| 7 | Bridge/OmegaThetaToPiLiWiring.lean | 26 | OmegaThetaToPiLiHyp | YES | **HIGH** |
| 4 | CriticalAssumptions.lean | 84 | HardyFirstMomentUpperHyp | YES | MEDIUM |
| 1 | Aristotle/HardyApproxFunctionalEq.lean | 113 | approx_functional_eq | No | MEDIUM |
| 5 | Bridge/ExplicitFormulaOscillation.lean | 63 | PsiOscillationFromCriticalZerosHyp | YES | LOW |
| 6 | Bridge/ThetaExplicitFormulaOscillation.lean | 63 | ThetaOscillationSqrtHyp | YES | LOW |
| 2 | Aristotle/ZeroCounting.lean | 117 | zetaZeroCount_via_argument | No | BLOCKED |
| 3 | Aristotle/ZeroCounting.lean | 134 | zetaZeroCount_asymp | No | BLOCKED |

---

## SORRY 7: OmegaThetaToPiLiWiring — HIGHEST PRIORITY

**File:** `Littlewood/Bridge/OmegaThetaToPiLiWiring.lean`
**Line:** 26–29

### Goal Type
```lean
∀ f : ℝ → ℝ, (∀ᶠ x in atTop, Real.sqrt x ≤ f x) →
  (fun x => chebyshevTheta x - x) =Ω±[f] →
  (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
    =Ω±[fun x => f x / Real.log x]
```

where:
- `chebyshevTheta x = Chebyshev.theta x` (defined in `Basic/ChebyshevFunctions.lean:35`)
- `logarithmicIntegral x = ∫ t in Ioc 2 x, 1 / Real.log t` (defined in `Basic/LogarithmicIntegral.lean`)
- `IsOmegaPlusMinus f g = IsOmegaPlus f g ∧ IsOmegaMinus f g` (defined in `Basic/OmegaNotation.lean:54`)
- `IsOmegaPlus f g = ∃ c > 0, ∃ᶠ x in atTop, f x ≥ c * g x` (line 44)
- `IsOmegaMinus f g = ∃ c > 0, ∃ᶠ x in atTop, f x ≤ -c * g x` (line 49)

### Key Available Theorems

1. **MediumPNT** (PrimeNumberTheoremAnd/MediumPNT.lean:3804, **PROVED**):
   ```lean
   theorem MediumPNT : ∃ c > 0,
       (ψ - id) =O[atTop]
         fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))
   ```
   This gives: `ψ(x) - x = O(x · exp(-c · (log x)^{1/10}))`.

2. **Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log** (PrimeNumberTheoremAnd/Consequences.lean:182):
   `|ψ(x) - θ(x)| ≤ 2√x · log x` for `x ≥ 1`.
   Combined with MediumPNT: `θ(x) - x = O(x · exp(-c · (log x)^{1/10}))`.

3. **WeakPNT''** (PrimeNumberTheoremAnd/Consequences.lean:103):
   `ψ ~[atTop] id` (Chebyshev psi is asymptotic to the identity).

4. **Abel summation** (Mathlib, NumberTheory/AbelSummation.lean):
   `sum_mul_eq_sub_integral_mul`, `sum_mul_eq_sub_integral_mul₀` — full partial summation API.

5. **PsiOscillationPiLi.lean** (Aristotle, **PROVED with local defs**):
   `psi_oscillation_implies_pi_li_oscillation` proves the transfer from ψ-oscillation
   to π-li sign changes, assuming `pi_sub_li_error = O(√x/log x)`. Serves as a
   REFERENCE PROOF for the mathematical argument — but uses LOCAL definitions
   (`Aristotle.PsiOscillationPiLi.chebyshevPsi`, `.li`) incompatible with project's types.

### Proof Strategy

The standard argument is by Abel/partial summation:

**Step 1: Establish the identity**
```
π(x) - li(x) = (θ(x) - x)/log x + R(x)
```
where `R(x) = ∫₂ˣ (θ(t) - t)/(t · log²t) dt + constant`.

This comes from:
- Abel summation: `π(x) = θ(x)/log x + ∫₂ˣ θ(t)/(t · log²t) dt + C₁`
  (apply `sum_mul_eq_sub_integral_mul` with `c(n) = 1_{n prime} · log n` and `f(t) = 1/log t`)
- Integration by parts: `li(x) = x/log x + ∫₂ˣ 1/log²t dt + C₂`
  (integrate `∫ 1/log t dt` by parts using `u = 1/log t`, `dv = dt`)

**Step 2: Bound R(x) using MediumPNT**

From MediumPNT + abs_psi_sub_theta:
```
|θ(t) - t| ≤ C · t · exp(-c · (log t)^{1/10}) + 2√t · log t
```
So:
```
|R(x)| ≤ C · ∫₂ˣ exp(-c(log t)^{1/10})/log²t dt + 2 ∫₂ˣ 1/(√t · log t) dt + const
```
The first integral is O(1) (super-polynomial decay). The second integral is O(√x/log x).
BUT: we need `R(x) = o(f(x)/log x)` where `f(x) ≥ √x`.

Key insight: the second integral is O(√x) (not o(√x/log x)). However, the hypothesis
gives `f(x) ≥ √x`, so `f(x)/log x ≥ √x/log x`. And R(x) = O(√x). So R(x) and
f(x)/log x are the SAME ORDER.

**Revised approach — use PsiOscillationPiLi pattern:**

Instead of the identity approach, use the STRONGER formulation from PsiOscillationPiLi.lean:

1. Define `error(x) := π(x) - li(x) - (θ(x) - x)/log x`.
2. Prove `error = O(√x / log x)` using MediumPNT. This is the KEY step.
   - By MediumPNT: `θ(t) - t = O(t · exp(-c(log t)^{1/10}))`.
   - The error is the integral ∫₂ˣ (θ(t)-t)/(t log²t) dt.
   - This integral = O(∫₂ˣ exp(-c(log t)^{1/10})/log²t dt) + O(√x) = O(√x).
   - Actually need O(√x/log x). Use: for any δ > 0, |θ(t) - t| ≤ δt for t ≥ T₀(δ).
     Then ∫_{T₀}ˣ |θ-t|/(t log²t) dt ≤ δ · x/log²x. Choose δ = ε/C.
   - The constant part ∫₂^{T₀} is bounded. So error(x) ≤ C₀ + ε · x/log²x.
   - Since f(x) ≥ √x, f(x)/log x ≥ √x/log x, and √x/log x → ∞, for large x:
     C₀ + ε · x/log²x ≤ (c/2) · f(x)/log x? NO — x/log²x / (√x/log x) = √x/log x → ∞.

**CORRECTED approach — the integral IS bounded:**

The integral ∫₂ˣ (θ(t)-t)/(t log²t) dt with MediumPNT:
```
|θ(t) - t| ≤ C · t · exp(-c · (log t)^{1/10})
```
So the integrand is bounded by `C · exp(-c · (log t)^{1/10}) / log²t`.
Since `exp(-c · u^{1/10})` decays super-polynomially, the integral CONVERGES as x → ∞.
So R(x) → R(∞) = constant. Therefore R(x) = O(1), which IS o(√x/log x).

**This means the proof works!**

**Step 3: Transfer the oscillation**

Given `θ(x) - x ≥ c · f(x)` frequently (Ω₊ direction):
```
π(x) - li(x) = (θ(x) - x)/log x + R(x)
             ≥ c · f(x)/log x + R(x)
             ≥ c · f(x)/log x - |R(∞)| - 1  (for large x, R(x) ≈ R(∞))
             ≥ (c/2) · f(x)/log x           (for x large enough that f(x)/log x > 2(|R(∞)|+1)/c)
```
This works because `f(x)/log x ≥ √x/log x → ∞`.

For the Ω₋ direction: same argument with opposite sign.

### Concrete Implementation Steps

1. **Create a new Aristotle file** `Littlewood/Aristotle/ThetaToPiLiTransfer.lean`:
   - Import `Mathlib`, `Littlewood.Basic.ChebyshevFunctions`, `Littlewood.Basic.LogarithmicIntegral`, `Littlewood.Basic.OmegaNotation`, `PrimeNumberTheoremAnd.MediumPNT`
   - Wrap in `namespace Aristotle.ThetaToPiLiTransfer`
   - Prove the key identity: `π(x) - li(x) = (θ(x) - x)/log x + R(x)` where R(x) converges
   - Prove `R = O(1)` using MediumPNT
   - Prove the transfer: `θ =Ω±[f] → π-li =Ω±[f/log]`

2. **Wire into OmegaThetaToPiLiWiring.lean:**
   - Import the new Aristotle file
   - Replace `sorry` with the proved theorem

3. **Validate:** `lake build` → 9 sorry warnings (down from 10).

### Fallback

If the full Abel summation + MediumPNT approach proves too complex, there's a
simpler structural approach:

- Prove `π(x) ≥ θ(x)/log x` (each prime ≤ x contributes log p ≤ log x to θ,
  so θ(x) ≤ π(x) · log x).
- Prove `li(x) ≤ x/log x + C · x/log²x` (by integration by parts or series expansion).
- Then when θ(x) - x ≥ c√x: π(x) ≥ (x + c√x)/log x, and
  li(x) ≤ x/log x + C · x/log²x. So π - li ≥ c√x/log x - C·x/log²x.
  For large x, c√x/log x dominates C·x/log²x? NO — x/log²x / (√x/log x) = √x/log x → ∞.

So the fallback doesn't work. The Abel summation + MediumPNT approach is necessary.

---

## SORRY 4: HardyFirstMomentUpperHyp — SECOND PRIORITY

**File:** `Littlewood/CriticalAssumptions.lean`
**Line:** 84–86

### Goal Type
```lean
∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
  |∫ t in Ioc 1 T, HardyEstimatesPartial.hardyZ t| ≤ C * T ^ (1/2 + ε)
```

where `HardyEstimatesPartial.hardyZ t = (exp(i·θ(t)) · ζ(1/2+it)).re`.

### Key Available Theorems

1. **hardyZ_first_moment_bound_conditional_two_bounds** (HardyZFirstMoment.lean:107, **PROVED**):
   Reduces the goal to two integral bounds:
   ```lean
   (h_main_bound : ∃ C₁ > 0, ∀ T ≥ 2, |∫ MainTerm| ≤ C₁ * T^(1/2+ε))
   (h_error_bound : ∃ C₂ > 0, ∀ T ≥ 2, |∫ ErrorTerm| ≤ C₂ * T^(1/2+ε))
   ```

2. **oscillatory_sum_integral_bound** (OscillatorySumBound.lean:95, **PROVED**):
   ```lean
   ∃ C > 0, ∃ T₀ ≥ 2, ∀ T ≥ T₀,
     |∫ t in Ioc 1 T, ∑ n ∈ Ico 1 (√⌊T⌋),
       (n+1)^{-1/2} * cos(t * log(n+1))| ≤ C * T^(1/2+ε)
   ```
   Bounds the oscillatory sum WITHOUT the θ(t) phase.

3. **ZetaCriticalLineBoundHyp** (auto-wired, 0 sorries):
   `‖ζ(1/2+it)‖ ≤ C · |t|^{1/4+ε}` — pointwise zeta bound.

### Gap Analysis

**Main Term bound (h_main_bound):**
- `MainTerm t = 2 · ∑ n^{-1/2} · cos(θ(t) - t log(n+1))`
- OscillatorySumBound bounds `∑ n^{-1/2} · cos(t · log(n+1))` (NO θ phase)
- The θ(t) phase modifies each term: `cos(θ(t) - t log n) ≠ cos(t log n)`
- To bridge this gap: use `cos(θ-α) = cos θ cos α + sin θ sin α` to split the sum
  into `cos θ · ∑(...) + sin θ · ∑(...)`. Each sub-sum is oscillatory and can be
  bounded similarly to OscillatorySumBound. The `cos θ`, `sin θ` prefactors are bounded
  by 1 and slowly varying (θ'(t) ~ (1/2)log(t/2π)), so integration by parts gives
  additional cancellation.
- Alternative: Use the second derivative test (van der Corput) on each integral
  `∫ cos(θ(t) - t log n) dt`. The phase has second derivative θ''(t) = -1/(2t),
  giving a bound O(√T) per term, and ∑ n^{-1/2} · √T ≈ √N · √T ≈ T^{3/4} total.
  This is ≤ T^{1/2+ε} only if ε ≥ 1/4, which is NOT sufficient for all ε > 0.

**Error Term bound (h_error_bound):**
- `ErrorTerm t = hardyZ t - MainTerm t = O(t^{-1/4})` by Riemann-Siegel
- `∫₁ᵀ O(t^{-1/4}) dt = O(T^{3/4})` — again only good for ε ≥ 1/4.

### Strategy

**Approach 1 (most direct):** Use the pointwise bound from ZetaCriticalLineBoundHyp:
`|Z(t)| ≤ ‖ζ(1/2+it)‖ ≤ C|t|^{1/4+ε/2}` (from hardyZ_abs_le + ZetaCriticalLineBoundHyp).
Then `|∫ Z| ≤ ∫ |Z| ≤ C ∫₁ᵀ t^{1/4+ε/2} dt = O(T^{5/4+ε/2})`.
This gives T^{5/4+ε/2} ≤ T^{1/2+ε} only when 5/4+ε/2 ≤ 1/2+ε, i.e., 3/4 ≤ ε/2,
i.e., ε ≥ 3/2. **NOT sufficient for all ε > 0.**

**Approach 2 (Cauchy-Schwarz + mean value):**
By Cauchy-Schwarz: `|∫₁ᵀ Z| ≤ √T · (∫₁ᵀ Z²)^{1/2}`.
The mean square ∫₁ᵀ Z² ~ T log T (classical Ingham result). So `|∫ Z| ≤ C · T · √(log T)`.
This is O(T^{1+ε}) for any ε > 0, but NOT O(T^{1/2+ε}). **NOT sufficient.**

**Approach 3 (genuine oscillatory cancellation):**
The actual bound requires proving that `∫₁ᵀ Z(t) dt` has cancellation from the
oscillatory phases. This is Theorem 7.6 in Titchmarsh: the first moment satisfies
`∫₁ᵀ Z(t) dt = O(T^{1/2})`. The proof uses the approximate functional equation +
van der Corput method to bound each oscillatory integral.

The van der Corput second derivative test gives: for f with |f''(t)| ≥ λ on [a,b]:
```
|∫_a^b e^{if(t)} dt| ≤ 8/√λ
```
Applied to `∫ cos(θ(t) - t log n)` with θ''(t) ≈ -1/(2t), giving λ ≈ 1/(2T):
```
|∫₁ᵀ cos(θ(t) - t log n) dt| ≤ 8√(2T) = O(√T)
```
Then `∑ n^{-1/2} · O(√T) = O(√T · 2√N) = O(√T · √(√T)) = O(T^{3/4})`.

To get O(T^{1/2+ε}), need first derivative test (van der Corput) on intervals where
|f'(t)| is bounded away from 0, which works except near the stationary point t = 2πn².
The contribution near the stationary point is O(1/√|f''|) = O(√T). Summing over
the ~1 term near each n gives O(T^{1/4}) total from stationary points. The rest
contributes O(1/|f'|) ≤ O(1/log n) per term, giving ∑ n^{-1/2}/log n ≤ C√N ≈ CT^{1/4}.
Total: O(T^{1/4}) = O(T^{1/2+ε}) for all ε > 0. ✓

### Concrete Implementation Steps

1. **Prove van der Corput second derivative test** in a new Aristotle file
   `Littlewood/Aristotle/VanDerCorput.lean`:
   ```lean
   theorem van_der_corput_second_derivative (f : ℝ → ℝ) (a b : ℝ) (λ : ℝ)
     (hf : ∀ t ∈ Icc a b, |deriv (deriv f) t| ≥ λ) (hλ : λ > 0) :
     |∫ t in Icc a b, Real.cos (f t)| ≤ 8 / Real.sqrt λ
   ```

2. **Apply to each oscillatory integral** in MainTerm:
   - Phase f(t) = θ(t) - t log n has f''(t) = θ''(t) ~ -1/(2t)
   - Bound each integral by O(√T), sum over n to get O(T^{1/4})

3. **Bound ErrorTerm** using Riemann-Siegel: `ErrorTerm = O(t^{-1/4})`, so
   `|∫ ErrorTerm| = O(T^{3/4}) = O(T^{1/2+1/4})`. This is O(T^{1/2+ε}) for ε ≥ 1/4.
   For ε < 1/4, need better Riemann-Siegel bounds (available in RiemannSiegelBound.lean).

4. **Apply hardyZ_first_moment_bound_conditional_two_bounds** to combine.

5. **Wire into CriticalAssumptions.lean** to replace the sorry.

### Risk Assessment

- Van der Corput second derivative test: MEDIUM difficulty. Standard analysis proof
  but involves integration by parts twice + careful bounds. ~200 lines of Lean.
- Application to MainTerm: MEDIUM. Need to handle the varying truncation
  N(t) = ⌊√(t/2π)⌋ in the sum.
- ErrorTerm: LOW for ε ≥ 1/4, HARD for all ε (needs uniform Riemann-Siegel).
- Overall: Could get a WEAKER result (e.g., ε ≥ 1/4) which still helps.

---

## SORRY 1: HardyApproxFunctionalEq — NOT ON CRITICAL PATH

**File:** `Littlewood/Aristotle/HardyApproxFunctionalEq.lean`
**Line:** 113–119

### Goal Type
```lean
∃ k > 0, ∃ C ≥ 0, ∃ T₁ ≥ 2, ∀ T : ℝ, T ≥ T₁ →
  ∫ t in Set.Ioc 1 T, (hardyZ t)^2 ≥
    (k * ∫ t in Set.Ioc 1 T, ‖partial_sum_approx t‖^2) - C * T
```

### Strategy

This is the mean-square approximate functional equation. The key identity is:
`Z(t)² ≈ |S_N(t)|² + cross terms + error²`

where S_N is the partial Dirichlet sum. The cross terms average out to O(T)
while `∫ |S_N|² ≈ T · H_N ≈ T log T`. So for k small enough (k = 1/2) and
C large enough, the bound holds.

Available infrastructure:
- `DiagonalIntegralBound.lean`: ∫ diagonalSum ≥ c · T log T (**PROVED**)
- `MeanSquarePartialSumAsymptotic.lean`: ∫ ‖S‖² partial sum bounds (**PROVED**)
- `HardyZMeasurability.lean`: measurability + integrability (**PROVED**)

The gap is connecting `Z²` to `|S_N|²` via the approximate functional equation
pointwise estimate: `Z(t) = 2 Re(S_N(t)) + O(t^{-1/4})`.

### Difficulty: MEDIUM-HIGH
Not on the critical path for littlewood_psi or littlewood_pi_li. Lower priority.

---

## SORRIES 5 & 6: ExplicitFormulaOscillation / ThetaExplicitFormulaOscillation

**Files:** `Littlewood/Bridge/ExplicitFormulaOscillation.lean:63`,
         `Littlewood/Bridge/ThetaExplicitFormulaOscillation.lean:63`

### Goal Types
```lean
-- Sorry 5:
(fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x]
-- (given [HardyCriticalLineZerosHyp])

-- Sorry 6:
(fun x => chebyshevTheta x - x) =Ω±[fun x => Real.sqrt x]
-- (given [HardyCriticalLineZerosHyp])
```

### Blocker: Perron Formula

Both sorries require the truncated explicit formula:
```
ψ(x) - x = -∑_{|γ|≤T} x^ρ/ρ + O(x log²x / T)   [non-vacuously!]
```

TruncatedExplicitFormula.lean has `psi_as_trig_sum` but its proof is VACUOUS
(the constant C depends on x,T, making the bound trivially true). A genuine
proof requires **Perron's formula**, which is NOT in Mathlib.

### Available Infrastructure

- **DirichletPhaseAlignment.lean** (**PROVED**, 0 sorries):
  - `simultaneous_dirichlet_approximation`: Full Dirichlet approximation theorem
  - `exists_large_x_phases_aligned_finset`: Phase alignment for finite sets of zeros
  - `bound_real_part_of_sum_aligned`: Lower bound on Re(∑ x^ρ/ρ) when phases align
  - BUT: uses LOCAL definitions (its own `chebyshevPsi`, `CriticalZeros`, etc.)

- **TruncatedExplicitFormula.lean** (**PROVED** but VACUOUS):
  - `psi_as_trig_sum`: vacuously true (C depends on x,T)
  - Uses LOCAL `chebyshevPsi` definition

### Intermediate Steps (if Perron unavailable)

1. **Formalize Perron's formula** as a new Aristotle file:
   ```lean
   theorem perron_formula (f : ℕ → ℂ) (s₀ : ℝ) (x T : ℝ) :
     |∑ n ∈ Icc 1 ⌊x⌋₊, f n - (1/(2*π*I)) * ∫ t in Icc (-T) T,
       (∑' n, f n / n^(s₀ + I*t)) * x^(s₀ + I*t) / (s₀ + I*t)| ≤ error(x, T, s₀)
   ```
   This is a ~500-line proof involving contour shifting + residue estimation.
   **Difficulty: VERY HIGH.**

2. **Alternatively, prove a NON-VACUOUS truncated explicit formula** using a simpler
   approach: Ramanujan's identity or direct estimation of ψ via log-derivative of ζ.
   This avoids Perron but is still substantial work.

3. **If Perron is available**, wiring to the oscillation extraction is straightforward:
   - Apply `psi_as_trig_sum` (non-vacuous version)
   - Apply `exists_large_x_phases_aligned_finset` + `bound_real_part_of_sum_aligned`
   - Construct the Ω₊ and Ω₋ witnesses
   - Must adapt from local types to project types (rename + unfold definitions)

### Recommendation

These sorries are the hardest in the project. Focus on Sorry 7 and Sorry 4 first.
If those are closed, document the exact Perron formula statement needed and the
type adaptation required, for future work.

---

## SORRIES 2 & 3: ZeroCounting — NOT ON CRITICAL PATH

**File:** `Littlewood/Aristotle/ZeroCounting.lean`

### Sorry 2 (line 117): zetaZeroCount_via_argument
```lean
∃ S : ℝ, |S| ≤ Real.log T ∧
  (zetaZeroCount T : ℝ) = (1/Real.pi) * (Complex.arg (xi_Mathlib (1/2 + T * I))) + 1 + S
```

### Sorry 3 (line 134): zetaZeroCount_asymp
```lean
(fun T => (zetaZeroCount T : ℝ) - (T / (2 * Real.pi)) *
  Real.log (T / (2 * Real.pi * Real.exp 1))) =O[atTop] (fun T => Real.log T)
```

### Blocker: Argument Principle

Both require the **argument principle** (relating contour integral of f'/f to zero count),
which is NOT in Mathlib. Without it:
- Sorry 2 cannot connect `zetaZeroCount` (ncard of zeros) to `Complex.arg` (winding)
- Sorry 3 depends on Sorry 2 for the connection

### Available Infrastructure (NOT sufficient to close)

- `ZeroCountingRectangle.lean`: Rectangle contour definitions, δ arg zeta (**PROVED**)
- `ZetaLogDerivInfra.lean`: Pole structure of -ζ'/ζ (**PROVED**)
- `CauchyGoursatRectangle.lean`: Cauchy-Goursat for rectangles (**PROVED**)
- `NAsymptotic.lean`: Conditional N(T) asymptotic (3 hypotheses) (**PROVED**)
- `RiemannVonMangoldtV2.lean`: N_eq_main_plus_S (**PROVED** but NZeros is defined
  by formula, NOT as actual zero count — vacuous)
- `NZerosStirling.lean`: S_bound, N_from_S_and_Stirling (**PROVED** but same
  vacuity — NZeros is a formula, not ncard)

### Note on Type Mismatch

The conditional theorems in NAsymptotic/RiemannVonMangoldtV2 define:
```lean
noncomputable def N (T : ℝ) : ℝ :=
  (Set.ncard {s : ℂ | ζ(s)=0 ∧ ...} : ℝ)
```
This IS definitionally equal to `(zetaZeroCount T : ℝ)`. However, connecting
the FORMULA `(1/π)(argΓ + arg ζ) + 1` to this actual count requires the
argument principle. The conditional theorems take this connection as a hypothesis
(`h_RVM`), which is exactly what Sorry 2 needs to provide.

### Recommendation

These are NOT on the critical path. Skip unless Sorries 4/7 are closed early.
If attempting, the argument principle would need to be formalized from scratch
(~1000 lines, involving winding numbers, holomorphic function theory, and
meromorphic residue counting).

---

## Commit Instructions

After each successfully closed sorry:
1. Run `lake build` and verify sorry count decreased by 1
2. `git add` only the files you changed
3. Commit with descriptive message
4. Push to main

Example:
```bash
lake build 2>&1 | grep "declaration uses 'sorry'" | wc -l  # should print 9 after Sorry 7
git add Littlewood/Bridge/OmegaThetaToPiLiWiring.lean Littlewood/Aristotle/ThetaToPiLiTransfer.lean
git commit -m "Close OmegaThetaToPiLiHyp sorry via Abel summation + MediumPNT"
git push
```

## Priority Order

1. **Sorry 7** (OmegaThetaToPiLiWiring) — HIGHEST. Uses MediumPNT + Abel summation.
   Expected: ~300 lines of new Lean in an Aristotle file + wiring.
2. **Sorry 4** (HardyFirstMomentUpperHyp) — MEDIUM. Needs van der Corput.
   Expected: ~500 lines, may only close for ε ≥ 1/4.
3. **Sorry 1** (HardyApproxFunctionalEq) — LOW PRIORITY. Not critical path.
4. **Sorries 5/6** (ExplicitFormulaOscillation) — BLOCKED on Perron. Document gaps.
5. **Sorries 2/3** (ZeroCounting) — BLOCKED on argument principle. Document gaps.
