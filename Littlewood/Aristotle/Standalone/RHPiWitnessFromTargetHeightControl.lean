import Littlewood.Aristotle.Standalone.RHPiTargetPhaseWitnessBuilders
import Littlewood.Aristotle.Standalone.RHPiReciprocalNormGrowth

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiWitnessFromTargetHeightControl

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.RHPiTargetPhaseWitnessBuilders
open Aristotle.Standalone.RHPiReciprocalNormGrowth

/-- Positive RH pointwise witness family from:
1) explicit-formula error on zeros-up-to-`T`,
2) target-phase control on the same finite zero set,
3) zero-count-driven coefficient domination. -/
theorem rh_pi_positive_main_witness_family_from_target_height_control
    (hRH : ∀ ρ ∈ zetaNontrivialZeros, ρ.re = 1 / 2)
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      4 * piScale x ≤ piMainFromZeros S x := by
  intro X
  rcases h_witness X with
    ⟨x, hxX, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hNcoeff⟩
  let S : Finset ℂ := (finite_zeros_le T).toFinset
  have hS : ∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2 := by
    intro ρ hρ
    exact mem_zero_finset_critical_line hRH (by simpa [S] using hρ)
  have hSre : ∀ ρ ∈ S, ρ.re = 1 / 2 := fun ρ hρ => (hS ρ hρ).2
  have hcoeff :
      2 * lll x ≤ (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖) := by
    have hcoeff' :
        2 * lll x ≤
          (1 - ε) * Finset.sum (finite_zeros_le T).toFinset (fun ρ => 1 / ‖ρ‖) :=
      coeff_domination_of_zero_count_div (x := x) (T := T) (ε := ε) hεlt hNcoeff hT4
    simpa [S] using hcoeff'
  have hphaseS :
      ∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε := by
    simpa [S] using hphase
  have hmain : 4 * piScale x ≤ piMainFromZeros S x :=
    piMain_from_target_phase_lower_four S hx1 hSre hphaseS hcoeff
  exact ⟨x, hxX, S, hS, by simpa [S] using herr, hmain⟩

/-- Negative RH pointwise witness family from:
1) explicit-formula error on zeros-up-to-`T`,
2) anti-target phase control on the same finite zero set,
3) zero-count-driven coefficient domination. -/
theorem rh_pi_negative_main_witness_family_from_antitarget_height_control
    (hRH : ∀ ρ ∈ zetaNontrivialZeros, ρ.re = 1 / 2)
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      piMainFromZeros S x ≤ -(4 * piScale x) := by
  intro X
  rcases h_witness X with
    ⟨x, hxX, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hNcoeff⟩
  let S : Finset ℂ := (finite_zeros_le T).toFinset
  have hS : ∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2 := by
    intro ρ hρ
    exact mem_zero_finset_critical_line hRH (by simpa [S] using hρ)
  have hSre : ∀ ρ ∈ S, ρ.re = 1 / 2 := fun ρ hρ => (hS ρ hρ).2
  have hcoeff :
      2 * lll x ≤ (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖) := by
    have hcoeff' :
        2 * lll x ≤
          (1 - ε) * Finset.sum (finite_zeros_le T).toFinset (fun ρ => 1 / ‖ρ‖) :=
      coeff_domination_of_zero_count_div (x := x) (T := T) (ε := ε) hεlt hNcoeff hT4
    simpa [S] using hcoeff'
  have hphaseS :
      ∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε := by
    simpa [S] using hphase
  have hmain : piMainFromZeros S x ≤ -(4 * piScale x) :=
    piMain_from_target_phase_upper_four S hx1 hSre hphaseS hcoeff
  exact ⟨x, hxX, S, hS, by simpa [S] using herr, hmain⟩

end Aristotle.Standalone.RHPiWitnessFromTargetHeightControl
