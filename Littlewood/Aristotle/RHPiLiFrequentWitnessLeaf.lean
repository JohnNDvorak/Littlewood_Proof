import Mathlib
import Littlewood.Aristotle.RHCaseOscillation
import Littlewood.CoreLemmas.GrowthDomination

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.RHPiLiFrequentWitnessLeaf

open Filter Topology Asymptotics
open GrowthDomination

/-- Standalone hypothesis class for the RH π-li frequent-witness pair used at
`DeepSorries.combined_atoms` line 282. -/
class RHPiLiFrequentWitnessHyp : Prop where
  h_plus :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      (Nat.primeCounting (Nat.floor x) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≥
        Real.sqrt x / Real.log x * lll x
  h_minus :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      (Nat.primeCounting (Nat.floor x) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≤
        -(Real.sqrt x / Real.log x * lll x)

/-- Importable leaf theorem discharging the RH π-li branch once the frequent
witness hypotheses are supplied. -/
theorem rh_pi_li_oscillation_from_witnesses
    [RHPiLiFrequentWitnessHyp] :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] :=
  Aristotle.RHCaseOscillation.rh_pi_li_oscillation_from_frequent
    RHPiLiFrequentWitnessHyp.h_plus
    RHPiLiFrequentWitnessHyp.h_minus

end Aristotle.RHPiLiFrequentWitnessLeaf
