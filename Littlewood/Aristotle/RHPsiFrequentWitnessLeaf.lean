import Mathlib
import Littlewood.Aristotle.RHCaseOscillation
import Littlewood.CoreLemmas.GrowthDomination

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.RHPsiFrequentWitnessLeaf

open Filter Topology Asymptotics
open GrowthDomination

/-- Standalone hypothesis class for the RH ψ frequent-witness pair used at
`DeepSorries.combined_atoms` line 267. -/
class RHPsiFrequentWitnessHyp : Prop where
  h_plus :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≥ Real.sqrt x * lll x
  h_minus :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≤ -(Real.sqrt x * lll x)

/-- Importable leaf theorem discharging the RH ψ branch once the frequent
witness hypotheses are supplied. -/
theorem rh_psi_oscillation_from_witnesses
    [RHPsiFrequentWitnessHyp] :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x] :=
  Aristotle.RHCaseOscillation.rh_psi_oscillation_from_frequent
    RHPsiFrequentWitnessHyp.h_plus
    RHPsiFrequentWitnessHyp.h_minus

end Aristotle.RHPsiFrequentWitnessLeaf
