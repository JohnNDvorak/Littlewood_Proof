import Littlewood.Aristotle.Standalone.RHPiSimultaneousPhaseApprox
import Littlewood.Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiPhasePerronSynthesis

open Filter Complex ZetaZeros
open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge
open Aristotle.Standalone.RHPiSimultaneousPhaseApprox

/-- At fixed height `T`, intersect:
1) eventual Perron explicit-formula error at `sqrt/log` scale, and
2) cofinal target phase alignment on zeros up to `T`.

This gives a single `x` carrying both payloads simultaneously. -/
theorem exists_large_x_perron_error_and_alignment_at_height
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (T ε X : ℝ) (hε : 0 < ε) :
    ∃ x : ℝ, X < x ∧
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ Real.sqrt x / Real.log x ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε) := by
  obtain ⟨Berr, hBerr⟩ := Filter.eventually_atTop.1
    (perron_sqrt_error_eventually_at_height_of_truncatedPiBridge hRH T)
  rcases exists_large_x_aligned_at_height hRH T ε (max X Berr) hε with
    ⟨x, hx, hphase⟩
  have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hBerrx : Berr ≤ x := le_trans (le_max_right _ _) (le_of_lt hx)
  have herr : 1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ Real.sqrt x / Real.log x := hBerr x hBerrx
  exact ⟨x, hXx, herr.1, herr.2, hphase⟩

/-- Frequently many `x` (at fixed height `T`) satisfy both the Perron
`sqrt/log` error bound and target phase alignment. -/
theorem frequently_perron_error_and_alignment_at_height
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (T ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ x in atTop,
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ Real.sqrt x / Real.log x ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε) := by
  rw [Filter.frequently_atTop]
  intro X
  rcases exists_large_x_perron_error_and_alignment_at_height hRH T ε X hε with
    ⟨x, hXx, hx1, herr, hphase⟩
  exact ⟨x, le_of_lt hXx, hx1, herr, hphase⟩

end Aristotle.Standalone.RHPiPhasePerronSynthesis

