import Littlewood.Aristotle.Standalone.RHPiPerronTruncatedWitness
import Littlewood.Aristotle.Standalone.RHPiTargetHeightFromTowerBound

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiPerronTowerWitness

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.RHPiPerronTruncatedWitness
open Aristotle.Standalone.RHPiTargetHeightFromTowerBound

/--
Target-height tower witness family with Perron/truncated explicit-formula error
at the baseline `sqrt/log` scale.
-/
abbrev TargetHeightTowerSqrtWitness : Prop :=
  ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
    4 ≤ T ∧
    1 < x ∧
    |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤
      Real.sqrt x / Real.log x ∧
    (∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
      x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)))
    )

/--
Anti-target-height tower witness family with Perron/truncated explicit-formula
error at the baseline `sqrt/log` scale.
-/
abbrev AntiTargetHeightTowerSqrtWitness : Prop :=
  ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
    4 ≤ T ∧
    1 < x ∧
    |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤
      Real.sqrt x / Real.log x ∧
    (∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
      x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)))
    )

/-- Target-height tower witness family at the Littlewood `piScale` scale. -/
abbrev TargetHeightTowerPiScaleWitness : Prop :=
  ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
    4 ≤ T ∧
    1 < x ∧
    |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
    (∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
      x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)))
    )

/-- Anti-target-height tower witness family at the Littlewood `piScale` scale. -/
abbrev AntiTargetHeightTowerPiScaleWitness : Prop :=
  ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
    4 ≤ T ∧
    1 < x ∧
    |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
    (∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
      x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)))
    )

/-- Upgrade target-height tower witnesses from `sqrt/log` error to `piScale`. -/
theorem target_tower_sqrt_to_piScale
    (hTarget : TargetHeightTowerSqrtWitness) :
    TargetHeightTowerPiScaleWitness := by
  rcases (Filter.eventually_atTop.1 lll_eventually_ge_one) with ⟨B, hB⟩
  intro X
  rcases hTarget (max X B) with
    ⟨x, hx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hxUpper⟩
  have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx)
  have hlll : 1 ≤ lll x := hB x hBx
  have herr' :
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x :=
    sqrt_error_le_piScale_of_lll_ge_one hx1 hlll herr
  exact ⟨x, hXx, T, hT4, hx1, herr', ε, hεpos, hεlt, hphase, hxUpper⟩

/-- Upgrade anti-target-height tower witnesses from `sqrt/log` error to
`piScale`. -/
theorem antitarget_tower_sqrt_to_piScale
    (hAntiTarget : AntiTargetHeightTowerSqrtWitness) :
    AntiTargetHeightTowerPiScaleWitness := by
  rcases (Filter.eventually_atTop.1 lll_eventually_ge_one) with ⟨B, hB⟩
  intro X
  rcases hAntiTarget (max X B) with
    ⟨x, hx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hxUpper⟩
  have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx)
  have hlll : 1 ≤ lll x := hB x hBx
  have herr' :
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x :=
    sqrt_error_le_piScale_of_lll_ge_one hx1 hlll herr
  exact ⟨x, hXx, T, hT4, hx1, herr', ε, hεpos, hεlt, hphase, hxUpper⟩

/-- Build full RH `π-li` witness data from Perron-style target/anti-target
tower families at baseline `sqrt/log` error scale. -/
theorem rhPiWitness_from_target_tower_sqrt
    (hRH : ZetaZeros.RiemannHypothesis)
    (hTarget : TargetHeightTowerSqrtWitness)
    (hAntiTarget : AntiTargetHeightTowerSqrtWitness) :
    RhPiWitnessData := by
  have hTargetPi : TargetHeightTowerPiScaleWitness :=
    target_tower_sqrt_to_piScale hTarget
  have hAntiTargetPi : AntiTargetHeightTowerPiScaleWitness :=
    antitarget_tower_sqrt_to_piScale hAntiTarget
  exact rhPiWitness_from_target_height_with_tower_bounds hRH hTargetPi hAntiTargetPi

/-- Quantified wrapper for direct use in blocker replacement:
if each RH branch provides the two Perron-style tower families at `sqrt/log`,
then Blocker 7 (`RhPiWitnessData`) follows. -/
theorem rhPiWitness_proved_of_target_tower_sqrt
    (hTarget :
      ∀ _hRH : ZetaZeros.RiemannHypothesis, TargetHeightTowerSqrtWitness)
    (hAntiTarget :
      ∀ _hRH : ZetaZeros.RiemannHypothesis, AntiTargetHeightTowerSqrtWitness) :
    RhPiWitnessData := by
  intro hRH
  exact (rhPiWitness_from_target_tower_sqrt hRH (hTarget hRH) (hAntiTarget hRH)) hRH

end Aristotle.Standalone.RHPiPerronTowerWitness
