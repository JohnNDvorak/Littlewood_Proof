# Aristotle Prompt Pack V2 (Mathlib-Only, Self-Contained)

Date: 2026-02-15
Purpose: Replace ineffective prior prompts with execution-ready prompts that map to the remaining DeepSorries blockers.

Global constraints for every prompt below:
- Use only `import Mathlib`.
- Do not import any project/local files.
- No `axiom`, no `sorry`, no `by admit`.
- Return a complete compilable Lean file.
- Keep theorem names and signatures exactly as specified.

Direct mapping to unresolved placeholders in `Littlewood/Aristotle/DeepSorries.lean`:
- Prompt 1 -> line 205 (`hHardy`)
- Prompts 2 and 3 -> line 212 (`rh_psi_oscillation_from_frequent` arguments)
- Prompt 4 -> line 217 (`psi_dirichlet_integral` section atom)
- Prompts 5 and 6 -> line 224 (`rh_pi_li_oscillation_from_frequent` arguments)
- Prompt 7 -> line 229 (`pi_log_zeta_extension` section atom)

Support prompts (8-10) are high-value prerequisites for Prompts 4 and 7.

---

BEGIN PROMPT 1 (Hardy Atom, Final Form)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

/-- Nontrivial zeta zeros in the critical strip. -/
def zetaNontrivialZeros : Set ℂ :=
  { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 }

/-- Final Hardy atom required by DeepSorries. -/
theorem hardy_infinitely_many_critical_line_zeros :
    Set.Infinite {ρ : ℂ | ρ ∈ zetaNontrivialZeros ∧ ρ.re = (1 : ℝ) / 2} := by
  /-
  Required structure of proof (all formalized in this file):
  1) Define Hardy Z-function `Z : ℝ → ℝ` (or an equivalent real-valued critical-line proxy).
  2) Prove a mean-square lower bound on [1,T]: `∫ t in 1..T, (Z t)^2` is at least `c * T * log T` eventually.
  3) Prove first-moment bound: `|∫ t in 1..T, Z t| ≤ C * T^a` for some `a < 1`.
  4) Prove pointwise upper bound: `|Z t| ≤ C' * t^b` with `b < 1/2` eventually.
  5) Show eventual one-sign behavior contradicts (2)-(4), hence infinitely many sign changes.
  6) Convert sign changes of `Z` to infinitely many zeros of `riemannZeta` on `re = 1/2`.
  -/
  sorry
```

END PROMPT 1

---

BEGIN PROMPT 2 (RH Case, psi Positive Frequency)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

def lll (x : ℝ) : ℝ := Real.log (Real.log (Real.log x))
def chebyshevPsi (x : ℝ) : ℝ := Chebyshev.psi x

def zetaNontrivialZeros : Set ℂ :=
  { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 }

def RiemannHypothesisLocal : Prop :=
  ∀ ρ : ℂ, ρ ∈ zetaNontrivialZeros → ρ.re = (1 : ℝ) / 2

/-- RH-case frequent positive excursions for psi error. -/
theorem rh_psi_frequent_plus
    (hRH : RiemannHypothesisLocal) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ chebyshevPsi x - x ≥ Real.sqrt x * lll x := by
  /-
  Deliver a full proof in this file.
  Suggested route: truncated explicit formula for psi + finite-zero phase alignment +
  quantitative lower bound on aligned zero contribution dominating error terms.
  -/
  sorry
```

END PROMPT 2

---

BEGIN PROMPT 3 (RH Case, psi Negative Frequency)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

def lll (x : ℝ) : ℝ := Real.log (Real.log (Real.log x))
def chebyshevPsi (x : ℝ) : ℝ := Chebyshev.psi x

def zetaNontrivialZeros : Set ℂ :=
  { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 }

def RiemannHypothesisLocal : Prop :=
  ∀ ρ : ℂ, ρ ∈ zetaNontrivialZeros → ρ.re = (1 : ℝ) / 2

/-- RH-case frequent negative excursions for psi error. -/
theorem rh_psi_frequent_minus
    (hRH : RiemannHypothesisLocal) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ chebyshevPsi x - x ≤ -(Real.sqrt x * lll x) := by
  /-
  Deliver a full proof in this file.
  Suggested route mirrors prompt 2 with opposite phase targeting.
  -/
  sorry
```

END PROMPT 3

---

BEGIN PROMPT 4 (Landau/Pringsheim psi Atom, Full Strength)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

def chebyshevPsi (x : ℝ) : ℝ := Chebyshev.psi x

/-- Full psi-side Landau/Pringsheim atom required by DeepSorries. -/
theorem pringsheim_psi
    (α : ℝ) (hα : (1 : ℝ) / 2 < α)
    (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hBound : ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        G s = s * (↑C : ℂ) / (s - (↑α : ℂ))
            + (↑σ : ℂ) * (s / (s - 1))
            + (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s) := by
  /-
  Required structure:
  1) Define nonnegative auxiliary function g(t) = C*t^α + σ*(t - psi(t)) eventually.
  2) Build Mellin-Dirichlet transform candidate G and prove convergence on Re(s) > 1.
  3) Prove formula identity on Re(s) > 1.
  4) Extend to Re(s) > α via nonnegative Dirichlet/Landau-Pringsheim mechanism.
  5) Upgrade to AnalyticOnNhd on {Re > α}.
  -/
  sorry
```

END PROMPT 4

---

BEGIN PROMPT 5 (RH Case, pi-li Positive Frequency)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

def lll (x : ℝ) : ℝ := Real.log (Real.log (Real.log x))

noncomputable def logarithmicIntegral (x : ℝ) : ℝ :=
  ∫ t in Set.Ioc 2 x, (1 / Real.log t)

def piLiError (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x

def zetaNontrivialZeros : Set ℂ :=
  { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 }

def RiemannHypothesisLocal : Prop :=
  ∀ ρ : ℂ, ρ ∈ zetaNontrivialZeros → ρ.re = (1 : ℝ) / 2

/-- RH-case frequent positive excursions for pi-li error. -/
theorem rh_pi_li_frequent_plus
    (hRH : RiemannHypothesisLocal) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piLiError x ≥ Real.sqrt x / Real.log x * lll x := by
  /-
  Full proof required.
  Route may be direct (explicit formula for pi-li) or transfer from psi with
  fully proved remainder control.
  -/
  sorry
```

END PROMPT 5

---

BEGIN PROMPT 6 (RH Case, pi-li Negative Frequency)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

def lll (x : ℝ) : ℝ := Real.log (Real.log (Real.log x))

noncomputable def logarithmicIntegral (x : ℝ) : ℝ :=
  ∫ t in Set.Ioc 2 x, (1 / Real.log t)

def piLiError (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x

def zetaNontrivialZeros : Set ℂ :=
  { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 }

def RiemannHypothesisLocal : Prop :=
  ∀ ρ : ℂ, ρ ∈ zetaNontrivialZeros → ρ.re = (1 : ℝ) / 2

/-- RH-case frequent negative excursions for pi-li error. -/
theorem rh_pi_li_frequent_minus
    (hRH : RiemannHypothesisLocal) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piLiError x ≤ -(Real.sqrt x / Real.log x * lll x) := by
  /-
  Full proof required.
  Route mirrors prompt 5 with opposite phase targeting.
  -/
  sorry
```

END PROMPT 6

---

BEGIN PROMPT 7 (Landau/Pringsheim pi-log-zeta Atom, Full Strength)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

noncomputable def logarithmicIntegral (x : ℝ) : ℝ :=
  ∫ t in Set.Ioc 2 x, (1 / Real.log t)

def piLiError (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x

/-- Full pi-side Landau/Pringsheim atom required by DeepSorries. -/
theorem pringsheim_pi
    (α : ℝ) (hα : (1 : ℝ) / 2 < α)
    (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hBound : ∀ᶠ x in atTop, σ * piLiError x ≤ C * x ^ α) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → Complex.exp (H s) = riemannZeta s := by
  /-
  Required structure:
  1) Construct log-zeta representation on Re(s) > 1.
  2) Connect one-sided pi-li bound to an analytic continuation mechanism to Re(s) > α.
  3) Prove extension analyticity on {Re > α}.
  4) Ensure compatibility equation exp(H s)=zeta(s) on Re(s)>1.
  -/
  sorry
```

END PROMPT 7

---

BEGIN PROMPT 8 (Support: Mellin Formula for x)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open MeasureTheory Complex Real

/-- Mellin integral of x against x^{-s-1} on (1,∞). -/
theorem mellin_x_formula
    (s : ℂ) (hs : 1 < s.re) :
    (∫ x in Set.Ioi (1 : ℝ),
      ((x : ℂ) * ((x : ℂ) ^ (-(s + 1))))) = 1 / (s - 1) := by
  sorry
```

END PROMPT 8

---

BEGIN PROMPT 9 (Support: Mellin Formula for x^alpha)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open MeasureTheory Complex Real

/-- Mellin integral of x^alpha against x^{-s-1} on (1,∞). -/
theorem mellin_rpow_alpha_formula
    (α : ℝ) (s : ℂ) (hs : α < s.re) :
    (∫ x in Set.Ioi (1 : ℝ),
      (((x : ℂ) ^ (α : ℂ)) * ((x : ℂ) ^ (-(s + 1))))) = 1 / (s - (α : ℂ)) := by
  sorry
```

END PROMPT 9

---

BEGIN PROMPT 10 (Support: No Analytic Global Log-zeta Past Pole)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Complex Set

/-- Pole obstruction: no analytic logarithm of zeta on any half-plane crossing 1. -/
theorem zeta_has_no_analytic_log_at_one
    (α : ℝ) (hα : α < (1 : ℝ)) :
    ¬ ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      (∀ s : ℂ, 1 < s.re → Complex.exp (H s) = riemannZeta s) := by
  sorry
```

END PROMPT 10

---

## Execution Notes for Aristotle

- Prompts 1-7 are the direct blockers.
- Prompts 8-10 are support lemmas that should be proved first and then reused in 4/7.
- Return one Lean file per prompt, each standalone and compilable with only `import Mathlib`.
- Avoid introducing project-specific names; keep local defs exactly as provided.
