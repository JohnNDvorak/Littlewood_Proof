# DeepSorries Mathlib-Only Aristotle Prompts

Date: 2026-02-15
Scope: Replace the 7 remaining `sorry` placeholders in `Littlewood/Aristotle/DeepSorries.lean`.
Constraint: Each prompt below is self-contained and relies only on Mathlib primitives.

## Mapping to current placeholders

1. `DeepSorries.lean:205` (Hardy atom)
2. `DeepSorries.lean:212` first argument (`h_plus` for psi RH-case)
3. `DeepSorries.lean:212` second argument (`h_minus` for psi RH-case)
4. `DeepSorries.lean:217` argument to `psi_dirichlet_integral`
5. `DeepSorries.lean:224` first argument (`h_plus` for pi-li RH-case)
6. `DeepSorries.lean:224` second argument (`h_minus` for pi-li RH-case)
7. `DeepSorries.lean:229` argument to `pi_log_zeta_extension`

---

BEGIN PROMPT 1

```lean
set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

/-- Third iterated logarithm. -/
def lll (x : ℝ) : ℝ := Real.log (Real.log (Real.log x))

/-- Chebyshev psi from Mathlib. -/
def chebyshevPsi (x : ℝ) : ℝ := Chebyshev.psi x

/-- Nontrivial zeta zeros in the critical strip. -/
def zetaNontrivialZeros : Set ℂ :=
  { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 }

/-- Target theorem (Hardy 1914): infinitely many critical-line nontrivial zeros. -/
theorem hardy_infinitely_many_critical_line_zeros :
    Set.Infinite {ρ : ℂ | ρ ∈ zetaNontrivialZeros ∧ ρ.re = (1 : ℝ) / 2} := by
  -- Provide a complete proof using only Mathlib.
  sorry
```

END PROMPT 1

---

BEGIN PROMPT 2

```lean
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

/-- RH-case positive frequent lower bound needed for psi oscillation. -/
theorem rh_psi_frequent_plus
    (hRH : RiemannHypothesisLocal) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ chebyshevPsi x - x ≥ Real.sqrt x * lll x := by
  -- Prove from Mathlib-level RH machinery and explicit-formula infrastructure.
  sorry
```

END PROMPT 2

---

BEGIN PROMPT 3

```lean
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

/-- RH-case negative frequent upper bound needed for psi oscillation. -/
theorem rh_psi_frequent_minus
    (hRH : RiemannHypothesisLocal) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ chebyshevPsi x - x ≤ -(Real.sqrt x * lll x) := by
  -- Prove from Mathlib-level RH machinery and explicit-formula infrastructure.
  sorry
```

END PROMPT 3

---

BEGIN PROMPT 4

```lean
set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

def chebyshevPsi (x : ℝ) : ℝ := Chebyshev.psi x

/-- Landau/Pringsheim nonnegative Dirichlet integral theorem for psi-side bounds. -/
theorem pringsheim_psi
    (α : ℝ) (hα : 1 / 2 < α)
    (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hBound : ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        G s = s * (↑C : ℂ) / (s - (↑α : ℂ)) +
              (↑σ : ℂ) * (s / (s - 1)) +
              (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s) := by
  -- Full proof required; no axioms/sorries.
  sorry
```

END PROMPT 4

---

BEGIN PROMPT 5

```lean
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

/-- RH-case positive frequent lower bound needed for pi-li oscillation. -/
theorem rh_pi_li_frequent_plus
    (hRH : RiemannHypothesisLocal) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piLiError x ≥ Real.sqrt x / Real.log x * lll x := by
  -- Prove from Mathlib-level RH machinery and explicit-formula infrastructure.
  sorry
```

END PROMPT 5

---

BEGIN PROMPT 6

```lean
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

/-- RH-case negative frequent upper bound needed for pi-li oscillation. -/
theorem rh_pi_li_frequent_minus
    (hRH : RiemannHypothesisLocal) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piLiError x ≤ -(Real.sqrt x / Real.log x * lll x) := by
  -- Prove from Mathlib-level RH machinery and explicit-formula infrastructure.
  sorry
```

END PROMPT 6

---

BEGIN PROMPT 7

```lean
set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

noncomputable def logarithmicIntegral (x : ℝ) : ℝ :=
  ∫ t in Set.Ioc 2 x, (1 / Real.log t)

def piLiError (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x

/-- Landau/Pringsheim analytic log-zeta extension for one-sided pi-li bounds. -/
theorem pringsheim_pi
    (α : ℝ) (hα : 1 / 2 < α)
    (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hBound : ∀ᶠ x in atTop, σ * piLiError x ≤ C * x ^ α) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → Complex.exp (H s) = riemannZeta s := by
  -- Full proof required; no axioms/sorries.
  sorry
```

END PROMPT 7

---

## Transplant instructions back into `DeepSorries.lean`

- Prompt 1 fills line 205 (`hHardy`).
- Prompts 2 and 3 fill the two arguments at line 212.
- Prompt 4 fills the argument at line 217.
- Prompts 5 and 6 fill the two arguments at line 224.
- Prompt 7 fills the argument at line 229.

When integrating, convert local names if needed:
- `RiemannHypothesisLocal` -> project RH proposition used at call site.
- local `logarithmicIntegral` -> `LogarithmicIntegral.logarithmicIntegral`.
- local `chebyshevPsi` -> project `chebyshevPsi` alias.
