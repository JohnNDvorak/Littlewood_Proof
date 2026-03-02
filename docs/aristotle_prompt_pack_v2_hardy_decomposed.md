# Aristotle Prompt Pack V2B (Hardy Decomposed, Mathlib-Only)

Date: 2026-02-15
Purpose: Break the Hardy atom into smaller standalone prompts with explicit deliverables.

Global constraints:
- Use only `import Mathlib`.
- No project imports.
- No `axiom`, no `sorry`, no `by admit` in returned code.
- Return one complete Lean file per prompt.

---

BEGIN HARDY PROMPT A (Abstract Sign-Contradiction Core)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Real MeasureTheory Set

/-- Abstract sign-contradiction engine used by Hardy's argument. -/
theorem hardy_sign_contradiction_core
    (Z : ℝ → ℝ)
    (h_sq_lower : ∀ᶠ T in Filter.atTop,
      (1 : ℝ) ≤ T ∧ T * Real.log T ≤ ∫ t in (1 : ℝ)..T, (Z t)^2)
    (h_abs_int_upper : ∃ A > 0, ∀ᶠ T in Filter.atTop,
      (1 : ℝ) ≤ T ∧ |∫ t in (1 : ℝ)..T, Z t| ≤ A * T^(3/4 : ℝ))
    (h_pointwise : ∃ B > 0, ∀ᶠ t in Filter.atTop,
      (1 : ℝ) ≤ t ∧ |Z t| ≤ B * t^(1/4 : ℝ)) :
    ¬ (∃ T0 : ℝ, ∀ t ≥ T0, 0 ≤ Z t) ∧ ¬ (∃ T0 : ℝ, ∀ t ≥ T0, Z t ≤ 0) := by
  /-
  Required proof idea:
  - If `Z` is eventually one-signed, then `∫ Z^2 ≤ sup|Z| * |∫ Z|` on large intervals.
  - Use given growth bounds to derive `∫ Z^2 = O(T)` or `O(T^p)` with `p < 1*log behavior`.
  - Contradict `T log T ≤ ∫ Z^2` eventually.
  -/
  sorry
```

END HARDY PROMPT A

---

BEGIN HARDY PROMPT B (Critical-Line Zero Transfer)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Complex Set

/-- Nontrivial zeta zeros in the critical strip. -/
def zetaNontrivialZeros : Set ℂ :=
  { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 }

/-- If a real-valued critical-line proxy has infinitely many real zeros,
then zeta has infinitely many nontrivial critical-line zeros. -/
 theorem hardy_zero_transfer
    (Z : ℝ → ℝ)
    (hProxy : ∀ t : ℝ, Z t = 0 → riemannZeta ((1 / 2 : ℝ) + t * Complex.I) = 0)
    (hStrip : ∀ t : ℝ, Z t = 0 → 0 < ((1 / 2 : ℝ) : ℂ).re ∧ ((1 / 2 : ℝ) : ℂ).re < 1)
    (hInf : Set.Infinite {t : ℝ | Z t = 0}) :
    Set.Infinite {ρ : ℂ | ρ ∈ zetaNontrivialZeros ∧ ρ.re = (1 : ℝ) / 2} := by
  sorry
```

END HARDY PROMPT B

---

BEGIN HARDY PROMPT C (Hardy Atom Assembly)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

/-- Nontrivial zeta zeros in the critical strip. -/
def zetaNontrivialZeros : Set ℂ :=
  { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 }

/-- Final Hardy atom in the exact DeepSorries-compatible form. -/
theorem hardy_infinitely_many_critical_line_zeros :
    Set.Infinite {ρ : ℂ | ρ ∈ zetaNontrivialZeros ∧ ρ.re = (1 : ℝ) / 2} := by
  /-
  This prompt requires a complete end-to-end Hardy proof in one file.
  You may define any auxiliary Hardy Z / Xi functions locally.
  You must prove all needed analytic bounds inside this file.
  Do not leave assumptions unproved.
  -/
  sorry
```

END HARDY PROMPT C

---

BEGIN HARDY PROMPT D (Intermediate Mean-Square Theorem)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Real MeasureTheory

/-- Standalone mean-square lower bound target used in Hardy proof. -/
theorem hardy_mean_square_lower_bound_template
    (Z : ℝ → ℝ) :
    ∃ c > 0, ∀ᶠ T in Filter.atTop,
      (1 : ℝ) ≤ T ∧ c * T * Real.log T ≤ ∫ t in (1 : ℝ)..T, (Z t)^2 := by
  /-
  Provide a concrete `Z` linked to zeta on Re=1/2 and prove this bound.
  -/
  sorry
```

END HARDY PROMPT D

---

BEGIN HARDY PROMPT E (Intermediate First-Moment Theorem)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Real MeasureTheory

/-- Standalone first-moment cancellation bound target used in Hardy proof. -/
theorem hardy_first_moment_bound_template
    (Z : ℝ → ℝ) :
    ∃ A > 0, ∀ᶠ T in Filter.atTop,
      (1 : ℝ) ≤ T ∧ |∫ t in (1 : ℝ)..T, Z t| ≤ A * T^(3/4 : ℝ) := by
  /-
  Prove with your chosen concrete Hardy proxy `Z`.
  -/
  sorry
```

END HARDY PROMPT E
