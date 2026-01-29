# Wiring Guide: Aristotle Prompts for Hypothesis Classes

Updated: 2026-01-29

This document specifies the exact Lean 4 theorem statements that Aristotle
needs to produce in order to wire each hypothesis class. For each hypothesis,
we give:
1. The exact type that needs to be proved
2. What Aristotle already has
3. What's missing
4. A suggested Aristotle prompt

---

## TIER 1: Blocked Only by Statement Strength

### ZeroCountingRvmExplicitHyp

**Exact type needed:**
```lean
theorem riemann_von_mangoldt_uniform :
    ∃ C T0 : ℝ, ∀ T ≥ T0,
      |(RiemannVonMangoldtModule.NZeros T : ℝ) -
       (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) + T / (2 * Real.pi)|
      ≤ C * Real.log T
```

**What exists:** `riemann_von_mangoldt` proves `∀ T ≥ 2, ∃ C, |...| ≤ C * log T`
(C depends on T - quantifiers are wrong way around)

**Aristotle prompt:** "Prove the Riemann-von Mangoldt formula with a UNIFORM constant: there exist C and T0 such that for all T >= T0, |N(T) - (T/2pi)log(T/2pi) + T/2pi| <= C * log T. The key is that C must NOT depend on T. Use the argument principle and Stirling's approximation. The constant C comes from bounding S(T) and the Stirling remainder, both of which have uniform bounds."

### ZeroCountingAsymptoticHyp (derived from RvmExplicit)

Once ZeroCountingRvmExplicitHyp is wired, ZeroCountingAsymptoticHyp follows
automatically via the instance at ZeroCountingFunction.lean:589.

**Alternative Aristotle prompt (IsBigO version):**
```lean
theorem N_asymptotic_direct :
    (fun T => (NZeros T : ℝ) -
      (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)))
    =O[Filter.atTop] Real.log
```
This directly gives the IsBigO form without needing the intermediate step.

### ZeroCountingCrudeBoundHyp (follows from asymptotic)

**Exact type needed:**
```lean
∃ C : ℝ, ∀ {T : ℝ}, 4 ≤ T → (N T : ℝ) ≤ C * T * Real.log T
```

**Derivation:** From asymptotic, N(T) = (T/2pi)log(T/2pi) + O(log T).
The main term is O(T log T), so N(T) ≤ C * T * log T for large T.

### ZeroCountingTendstoHyp (follows from asymptotic)

**Exact type needed:**
```lean
Tendsto (fun T => (N T : ℝ)) atTop atTop
```

**Derivation:** The main term (T/2pi)log(T/2pie) -> infinity.
Error is O(log T) which is negligible. So N(T) -> infinity.

---

## TIER 2: Need IsBigO Lifting

### NAsymptotic Path (alternative to Tier 1)

To use `ZetaZeroCount.N_asymptotic`, need these as IsBigO:

**h_RVM (argument principle):**
```lean
theorem rvm_isBigO :
    (fun T => ZetaZeroCount.N T -
      ((1 / Real.pi) * ZetaZeroCount.argGamma T -
       (T / (2 * Real.pi)) * Real.log Real.pi +
       ZetaZeroCount.S T + 1))
    =O[Filter.atTop] (fun T => 1 / T)
```

**h_Stirling:**
```lean
theorem stirling_isBigO :
    (fun T => ZetaZeroCount.argGamma T -
      ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8))
    =O[Filter.atTop] (fun T => 1 / T)
```

**h_S (ALREADY PROVED):** `S_term_bound` in ZeroCountingNew.lean

---

## TIER 3: Need New Aristotle Proofs

### OmegaPsiToThetaHyp

**Exact type needed:**
```lean
∀ f : ℝ → ℝ, (∀ᶠ x in atTop, Real.sqrt x ≤ f x) →
  (fun x => chebyshevPsi x - x) =Ω±[f] →
  (fun x => chebyshevTheta x - x) =Ω±[f]
```

**Available:** PsiThetaBound.psi_theta_bound proves |psi(x) - theta(x)| <= C * sqrt(x)

**Aristotle prompt:** "Prove: if f(x)/sqrt(x) -> infinity and psi(x) - x = Omega_pm(f), then theta(x) - x = Omega_pm(f). Use the fact that |psi(x) - theta(x)| <= C * sqrt(x) (PsiThetaBound). Since f(x) >> sqrt(x), the difference |psi - theta| is negligible compared to f, so the oscillation of psi transfers to theta."

### HardyCriticalLineZerosHyp

**Exact type needed:**
```lean
Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1/2 }
```

**Status:** Aristotle batch submitted, awaiting result.

### ExplicitFormulaPsiHyp

**Exact type needed:**
```lean
∀ x : ℝ, 1 < x →
  ∃ E : ℂ, ‖E‖ ≤ Real.log x ∧
    (ψ₀ x : ℂ) = x - ∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / ρ.val
      - Real.log (2 * π) - (1/2 : ℂ) * Real.log (1 - x^(-2 : ℤ)) + E
```

**Available:** TruncatedExplicitFormula.psi_as_trig_sum (truncated sum, not tsum)

**Gap:** Truncated sum vs infinite series (tsum). This is a real mathematical gap requiring convergence of the zero sum.

---

## TIER 4: Complex Multi-Step Chains

### SchmidtPsiOscillationHyp

**Exact type needed:**
```lean
∀ ε : ℝ, 0 < ε →
  (fun x => chebyshevPsi x - x) =Ω±[fun x => x ^ (Θ - ε)]
```

**Chain needed:**
1. ExplicitFormulaPsiHyp (full explicit formula)
2. Express zero sum as trig polynomial (via change of variables x = e^u)
3. Apply SchmidtNew.schmidt_oscillation (trig poly oscillation)
4. Convert back to get Ω± oscillation

**Status:** BLOCKED until explicit formula is complete.

---

## Bridge Status Summary

| Bridge | Status |
|--------|--------|
| chebyshevPsiV3 = chebyshevPsi | PROVED |
| zeroCountingFunction = ZetaZeroCount.N | PROVED |
| RVM.NZeros = zeroCountingFunction | PROVED (new) |
| ZCN.NZeros = zeroCountingFunction | PROVED (new) |
| chebyshevPsi = PsiThetaBound.psi | NEEDED |
| chebyshevTheta = PsiThetaBound.theta | NEEDED |
| zetaNontrivialZeros = zetaZerosBelowSet | PARTIAL |
