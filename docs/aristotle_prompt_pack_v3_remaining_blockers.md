# Aristotle Prompt Pack V3 (Remaining Blockers Only)

> Legacy note (2026-02-27): For the active RH-pi B7 loop, this file is non-canonical.
> Canonical loop objective/payload source is `docs/rh_pi_7a7c_remaining_deep_obligation.md`
> and policy is `docs/b7_real_progress_policy.md`.
> Use this prompt pack only for DeepSorries-era salvage tasks, not B7 loop control.

Date: 2026-02-15
Use case: Claude already mined useful pieces; this pack targets only what is still missing.

Global rules (apply to every prompt):
- `import Mathlib` only.
- No project imports, no external files.
- No `axiom`, no `sorry`, no `admit`.
- Return a complete, compilable Lean file.

Still-missing targets (from current `DeepSorries` structure):
- Hardy atom: `DeepSorries.lean:205`
- RH frequent bounds for psi: `DeepSorries.lean:212`
- Landau/Pringsheim psi atom: `DeepSorries.lean:217`
- RH frequent bounds for pi-li: `DeepSorries.lean:224`
- Landau/Pringsheim pi atom: `DeepSorries.lean:229`

---

BEGIN PROMPT R1 (Hardy Final Atom, Highest Priority)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

/-- Nontrivial zeta zeros in the critical strip. -/
def zetaNontrivialZeros : Set ℂ :=
  { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 }

/-- Final Hardy atom needed by DeepSorries. -/
theorem hardy_infinitely_many_critical_line_zeros :
    Set.Infinite {ρ : ℂ | ρ ∈ zetaNontrivialZeros ∧ ρ.re = (1 : ℝ) / 2} := by
  /-
  Must be unconditional.
  Required ingredients inside this file:
  1) Define a real-valued critical-line proxy (Hardy Z or equivalent).
  2) Mean-square lower bound of order T*log T.
  3) First-moment cancellation bound of lower growth order.
  4) Pointwise upper bound sufficient for the sign contradiction.
  5) Conclude infinitely many critical-line zeros of zeta.
  -/
  sorry
```

END PROMPT R1

---

BEGIN PROMPT R2 (Hardy Core Contradiction Sublemma)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Real MeasureTheory Set Filter

/-- Abstract sign-contradiction engine for Hardy's method.
This isolates the part Claude still needed: converting analytic bounds into
"not eventually one sign". -/
theorem hardy_sign_contradiction_core
    (Z : ℝ → ℝ)
    (h_sq_lower : ∃ c > 0, ∀ᶠ T in atTop,
      (1 : ℝ) ≤ T ∧ c * T * Real.log T ≤ ∫ t in (1 : ℝ)..T, (Z t)^2)
    (h_int_upper : ∃ A > 0, ∀ᶠ T in atTop,
      (1 : ℝ) ≤ T ∧ |∫ t in (1 : ℝ)..T, Z t| ≤ A * T^(3/4 : ℝ))
    (h_ptwise : ∃ B > 0, ∀ᶠ t in atTop,
      (1 : ℝ) ≤ t ∧ |Z t| ≤ B * t^(1/4 : ℝ)) :
    ¬ (∃ T0 : ℝ, ∀ t ≥ T0, 0 ≤ Z t) ∧ ¬ (∃ T0 : ℝ, ∀ t ≥ T0, Z t ≤ 0) := by
  sorry
```

END PROMPT R2

---

BEGIN PROMPT R3 (RH Case: Frequent Bounds Needed at line 212 and 224)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

def lll (x : ℝ) : ℝ := Real.log (Real.log (Real.log x))
def chebyshevPsi (x : ℝ) : ℝ := Chebyshev.psi x

noncomputable def logarithmicIntegral (x : ℝ) : ℝ :=
  ∫ t in Set.Ioc 2 x, (1 / Real.log t)

def piLiError (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x

def zetaNontrivialZeros : Set ℂ :=
  { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 }

def RiemannHypothesisLocal : Prop :=
  ∀ ρ : ℂ, ρ ∈ zetaNontrivialZeros → ρ.re = (1 : ℝ) / 2

/-- RH-case positive/negative frequent bounds for psi error. -/
theorem rh_psi_frequent_pair
    (hRH : RiemannHypothesisLocal) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧ chebyshevPsi x - x ≥ Real.sqrt x * lll x)
    ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧ chebyshevPsi x - x ≤ -(Real.sqrt x * lll x)) := by
  sorry

/-- RH-case positive/negative frequent bounds for pi-li error. -/
theorem rh_pi_li_frequent_pair
    (hRH : RiemannHypothesisLocal) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piLiError x ≥ Real.sqrt x / Real.log x * lll x)
    ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piLiError x ≤ -(Real.sqrt x / Real.log x * lll x)) := by
  sorry
```

END PROMPT R3

---

BEGIN PROMPT R4 (Landau/Pringsheim psi Atom, Missing Tail Only)

```lean
import Mathlib

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Asymptotics Set
open Complex Real

def chebyshevPsi (x : ℝ) : ℝ := Chebyshev.psi x

/-- Full psi atom needed at DeepSorries line 217.
This is the part still missing after Claude's salvage pass. -/
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
  Focus on the still-missing pieces explicitly:
  1) derive eventual nonnegativity of Landau auxiliary g,
  2) nonnegative-coefficient/Pringsheim mechanism,
  3) extension from Re>1 to Re>α,
  4) final AnalyticOnNhd packaging.
  -/
  sorry
```

END PROMPT R4

---

BEGIN PROMPT R5 (Landau/Pringsheim pi Atom, Hard Range 1/2<α<1)

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

/-- Full pi atom needed at DeepSorries line 229.
Claude covered useful Re>1 pieces; this prompt is for the remaining hard extension. -/
theorem pringsheim_pi
    (α : ℝ) (hα : (1 : ℝ) / 2 < α)
    (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hBound : ∀ᶠ x in atTop, σ * piLiError x ≤ C * x ^ α) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → Complex.exp (H s) = riemannZeta s := by
  /-
  Focus explicitly on the still-missing part: the 1/2<α<1 extension mechanism.
  The final theorem must be unconditional and match this signature exactly.
  -/
  sorry
```

END PROMPT R5

---

## Send Order (Recommended)

1. Prompt R1 (Hardy final atom)
2. Prompt R2 (Hardy contradiction core; can run in parallel if R1 stalls)
3. Prompt R4 (pringsheim_psi)
4. Prompt R5 (pringsheim_pi hard case)
5. Prompt R3 (RH frequent pair, if still open)
