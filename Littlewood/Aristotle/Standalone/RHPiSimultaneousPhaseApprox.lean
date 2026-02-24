import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.ZetaZeros.SupremumRealPart

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiSimultaneousPhaseApprox

open Filter Complex ZetaZeros

private lemma mem_zero_finset_nontrivial
    {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (finite_zeros_le T).toFinset) :
    ρ ∈ zetaNontrivialZeros := by
  have hz : ρ ∈ zerosUpTo T := by
    simpa using hρ
  have hz' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hz
  exact (mem_zetaNontrivialZerosPos.1 hz'.1).1

/-- Under RH, every zero in `(finite_zeros_le T).toFinset` is on the critical
line. -/
lemma finite_zero_finset_re_half
    (hRH : ZetaZeros.RiemannHypothesis)
    {T : ℝ} :
    ∀ ρ ∈ (finite_zeros_le T).toFinset, ρ.re = 1 / 2 := by
  intro ρ hρ
  exact hRH ρ (mem_zero_finset_nontrivial (T := T) hρ)

/-- Finite-height target-phase alignment on project zero sets:
for any fixed `T`, positive tolerance `ε`, and threshold `X`, there is `x > X`
such that all phases `x^{i·Im(ρ)}` with `ρ ∈ zerosUpTo(T)` are `ε`-close to `1`.
-/
theorem exists_large_x_aligned_at_height
    (hRH : ZetaZeros.RiemannHypothesis)
    (T ε X : ℝ) (hε : 0 < ε) :
    ∃ x : ℝ, X < x ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε) := by
  let S : Finset ℂ := (finite_zeros_le T).toFinset
  have hS : ∀ ρ ∈ S, ρ.re = 1 / 2 := by
    intro ρ hρ
    exact finite_zero_finset_re_half (T := T) hRH ρ (by simpa [S] using hρ)
  simpa [S] using
    Aristotle.DirichletPhaseAlignment.exists_large_x_phases_aligned_finset S hS ε hε X

/-- Filter form of finite-height target-phase alignment. -/
theorem frequently_aligned_at_height
    (hRH : ZetaZeros.RiemannHypothesis)
    (T ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ x : ℝ in atTop,
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε) := by
  rw [Filter.frequently_atTop]
  intro X
  rcases exists_large_x_aligned_at_height hRH T ε X hε with ⟨x, hXx, hphase⟩
  exact ⟨x, le_of_lt hXx, hphase⟩

end Aristotle.Standalone.RHPiSimultaneousPhaseApprox
