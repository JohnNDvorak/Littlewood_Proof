/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Omega Asymptotic Notation

This file defines the Omega (Ω) family of asymptotic notations, which describe
lower bounds and oscillation behavior of functions. These complement the standard
big-O and little-o notations from Mathlib.

## Definitions

* `IsOmega f g` : f(x) = Ω(g(x)) means limsup |f(x)|/g(x) > 0
* `IsOmegaPlus f g` : f(x) = Ω₊(g(x)) means limsup f(x)/g(x) > 0
* `IsOmegaMinus f g` : f(x) = Ω₋(g(x)) means liminf f(x)/g(x) < 0
* `IsOmegaPlusMinus f g` : f(x) = Ω±(g(x)) means both Ω₊ and Ω₋ hold

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Section 15.1
-/

namespace Asymptotics

open Filter Topology

variable {α : Type*} [TopologicalSpace α] [Preorder α]

section Definitions

/-- `f(x) = Ω(g(x))` means `|f(x)| ≥ c·g(x)` infinitely often for some `c > 0`. -/
def IsOmega (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ c > 0, ∃ᶠ x in atTop, |f x| ≥ c * g x

/-- `f(x) = Ω₊(g(x))` means `f(x) ≥ c·g(x)` infinitely often for some `c > 0`. -/
def IsOmegaPlus (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ c > 0, ∃ᶠ x in atTop, f x ≥ c * g x

/-- `f(x) = Ω₋(g(x))` means `f(x) ≤ -c·g(x)` infinitely often for some `c > 0`. -/
def IsOmegaMinus (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ c > 0, ∃ᶠ x in atTop, f x ≤ -c * g x

/-- `f(x) = Ω±(g(x))` means both `Ω₊` and `Ω₋` hold.
    This is the key notation for Littlewood's theorem, indicating
    that `f` oscillates to magnitude at least `g` in both directions. -/
def IsOmegaPlusMinus (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  IsOmegaPlus f g ∧ IsOmegaMinus f g

/-- Notation for Ω -/
scoped notation:50 f " =Ω[" g "]" => IsOmega f g

/-- Notation for Ω₊ -/
scoped notation:50 f " =Ω₊[" g "]" => IsOmegaPlus f g

/-- Notation for Ω₋ -/
scoped notation:50 f " =Ω₋[" g "]" => IsOmegaMinus f g

/-- Notation for Ω± -/
scoped notation:50 f " =Ω±[" g "]" => IsOmegaPlusMinus f g

end Definitions

section BasicProperties

variable {f f' g g' : ℝ → ℝ}

/-!
Note: We use the "frequently large" formulation of Ω/Ω± to avoid boundedness
side conditions that arise in limsup/liminf comparisons.
-/

/-- Ω± implies Ω -/
theorem IsOmegaPlusMinus.isOmega (h : f =Ω±[g]) : f =Ω[g] := by
  rcases h with ⟨hplus, _hminus⟩
  rcases hplus with ⟨c, hc, hfreq⟩
  refine ⟨c, hc, ?_⟩
  refine hfreq.mono ?_
  intro x hx
  exact hx.trans (le_abs_self _)

/-- Ω₊ implies Ω -/
theorem IsOmegaPlus.isOmega (h : f =Ω₊[g]) (_hg : ∀ᶠ x in atTop, 0 < g x) : f =Ω[g] := by
  rcases h with ⟨c, hc, hfreq⟩
  refine ⟨c, hc, ?_⟩
  refine hfreq.mono ?_
  intro x hx
  exact hx.trans (le_abs_self _)

/-- Ω₋ for f implies Ω₊ for -f -/
theorem IsOmegaMinus.neg_isOmegaPlus (h : f =Ω₋[g]) : (fun x => -f x) =Ω₊[g] := by
  rcases h with ⟨c, hc, hfreq⟩
  refine ⟨c, hc, ?_⟩
  refine hfreq.mono ?_
  intro x hx
  have := neg_le_neg hx
  simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using this

/-- Ω₊ for f implies Ω₋ for -f -/
theorem IsOmegaPlus.neg_isOmegaMinus (h : f =Ω₊[g]) : (fun x => -f x) =Ω₋[g] := by
  rcases h with ⟨c, hc, hfreq⟩
  refine ⟨c, hc, ?_⟩
  refine hfreq.mono ?_
  intro x hx
  have := neg_le_neg hx
  simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using this

/-- Ω± is preserved under negation -/
theorem IsOmegaPlusMinus.neg (h : f =Ω±[g]) : (fun x => -f x) =Ω±[g] :=
  ⟨h.2.neg_isOmegaPlus, h.1.neg_isOmegaMinus⟩

end BasicProperties

section FrequentlyLarge

/-- Ω₊ implies f(x) ≥ c·g(x) frequently -/
theorem IsOmegaPlus.frequently_ge (h : f =Ω₊[g]) :
    ∃ c > 0, ∃ᶠ x in atTop, f x ≥ c * g x := by
  simpa [IsOmegaPlus] using h

/-- Ω₋ implies f(x) ≤ -c·g(x) frequently -/
theorem IsOmegaMinus.frequently_le (h : f =Ω₋[g]) :
    ∃ c > 0, ∃ᶠ x in atTop, f x ≤ -c * g x := by
  simpa [IsOmegaMinus] using h

/-- Ω± implies infinitely many sign changes (when g is eventually positive) -/
theorem IsOmegaPlusMinus.sign_changes (h : f =Ω±[g]) (hg : ∀ᶠ x in atTop, 0 < g x) :
    (∃ᶠ x in atTop, 0 < f x) ∧ (∃ᶠ x in atTop, f x < 0) := by
  rcases h with ⟨hplus, hminus⟩
  rcases hplus with ⟨c, hc, hfreq⟩
  have hpos : ∀ᶠ x in atTop, 0 < c * g x := by
    refine hg.mono ?_
    intro x hxg
    exact mul_pos hc hxg
  have hfreq_pos : ∃ᶠ x in atTop, 0 < f x := by
    refine (hfreq.and_eventually hpos).mono ?_
    intro x hx
    exact lt_of_lt_of_le hx.2 hx.1
  rcases hminus with ⟨c', hc', hfreq'⟩
  have hneg : ∀ᶠ x in atTop, -c' * g x < 0 := by
    refine hg.mono ?_
    intro x hxg
    have hpos' : 0 < c' * g x := mul_pos hc' hxg
    have : -(c' * g x) < 0 := neg_lt_zero.mpr hpos'
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using this
  have hfreq_neg : ∃ᶠ x in atTop, f x < 0 := by
    refine (hfreq'.and_eventually hneg).mono ?_
    intro x hx
    exact lt_of_le_of_lt hx.1 hx.2
  exact ⟨hfreq_pos, hfreq_neg⟩

end FrequentlyLarge

section Construction

/-- Construct Ω± from explicit limsup/liminf bounds -/
theorem isOmegaPlusMinus_of_limsup_liminf
    (h_sup : Filter.limsup (fun x => f x / g x) atTop > 0)
    (h_inf : Filter.liminf (fun x => f x / g x) atTop < 0) :
    f =Ω±[g] :=
  by
    -- TODO: Relate limsup/liminf bounds to the "frequently large" definition.
    -- This should follow from standard filter characterizations.
    sorry

end Construction

section Scaling

/-- Scaling: if f =Ω±[g] and c > 0, then c·f =Ω±[g] -/
theorem IsOmegaPlusMinus.const_mul (h : f =Ω±[g]) (c : ℝ) (hc : 0 < c) :
    (fun x => c * f x) =Ω±[g] := by
  rcases h with ⟨hplus, hminus⟩
  rcases hplus with ⟨c', hc', hfreq⟩
  rcases hminus with ⟨c'', hc'', hfreq'⟩
  refine ⟨?_, ?_⟩
  · refine ⟨c * c', mul_pos hc hc', ?_⟩
    refine hfreq.mono ?_
    intro x hx
    have : c * f x ≥ c * (c' * g x) := by
      exact mul_le_mul_of_nonneg_left hx (le_of_lt hc)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  · refine ⟨c * c'', mul_pos hc hc'', ?_⟩
    refine hfreq'.mono ?_
    intro x hx
    have : c * f x ≤ c * (-c'' * g x) := by
      exact mul_le_mul_of_nonneg_left hx (le_of_lt hc)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-- Scaling the comparison function: if f =Ω±[g] and c > 0, then f =Ω±[c·g] -/
theorem IsOmegaPlusMinus.div_const (h : f =Ω±[g]) (c : ℝ) (hc : 0 < c) :
    f =Ω±[fun x => c * g x] := by
  rcases h with ⟨hplus, hminus⟩
  rcases hplus with ⟨c', hc', hfreq⟩
  rcases hminus with ⟨c'', hc'', hfreq'⟩
  refine ⟨?_, ?_⟩
  · refine ⟨c' / c, div_pos hc' hc, ?_⟩
    refine hfreq.mono ?_
    intro x hx
    have hc0 : c ≠ 0 := ne_of_gt hc
    have : (c' / c) * (c * g x) = c' * g x := by
      field_simp [hc0, mul_comm, mul_left_comm, mul_assoc]
    simpa [this] using hx
  · refine ⟨c'' / c, div_pos hc'' hc, ?_⟩
    refine hfreq'.mono ?_
    intro x hx
    have hc0 : c ≠ 0 := ne_of_gt hc
    have : -(c'' / c) * (c * g x) = -c'' * g x := by
      field_simp [hc0, mul_comm, mul_left_comm, mul_assoc]
    simpa [this] using hx

end Scaling

end Asymptotics
