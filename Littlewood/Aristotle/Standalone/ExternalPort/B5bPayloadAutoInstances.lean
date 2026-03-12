import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.Aristotle.Standalone.PsiZeroSumOscillationFromIngham

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.B5bPayloadAutoInstances

open Aristotle.DirichletPhaseAlignment
open Aristotle.Standalone.PsiZeroSumOscillationFromIngham

/-- Payload witness shape for `PhaseAlignmentToTargetHyp`. -/
def PhaseAlignmentToTargetWitness : Prop :=
  ∀ (S : Finset ℂ), (∀ ρ ∈ S, ρ.re = 1 / 2) →
    (∀ ρ ∈ S, 0 < ρ.im) →
    ∀ (w : ℂ), ‖w‖ = 1 →
    ∀ (ε : ℝ), ε > 0 →
    ∀ (X : ℝ), ZetaZeros.RiemannHypothesis →
      ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - w‖ < ε

/-- Payload witness shape for `CriticalZeroSumDivergesHyp`. -/
def CriticalZeroSumDivergesWitness : Prop :=
  ∀ (_hRH : ZetaZeros.RiemannHypothesis) (M : ℝ), ∃ T : ℝ, T ≥ 2 ∧
    M ≤ ∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1 / 4 + ρ.im ^ 2)

/-- External payload lane for phase-alignment-to-target witnesses. -/
class PhaseAlignmentToTargetPayload : Prop where
  witness : PhaseAlignmentToTargetWitness

/-- External payload lane for weighted critical-zero divergence witnesses. -/
class CriticalZeroSumDivergesPayload : Prop where
  witness : CriticalZeroSumDivergesWitness

/-- Package a concrete phase-alignment witness theorem as payload. -/
def phaseAlignmentToTargetPayload_of_witness
    (h : PhaseAlignmentToTargetWitness) :
    PhaseAlignmentToTargetPayload :=
  ⟨h⟩

/-- Package a concrete critical-zero divergence theorem as payload. -/
def criticalZeroSumDivergesPayload_of_witness
    (h : CriticalZeroSumDivergesWitness) :
    CriticalZeroSumDivergesPayload :=
  ⟨h⟩

/-- Auto-wire `PhaseAlignmentToTargetHyp` from payload. -/
instance (priority := 100)
    [PhaseAlignmentToTargetPayload] :
    Aristotle.DirichletPhaseAlignment.PhaseAlignmentToTargetHyp where
  approx := PhaseAlignmentToTargetPayload.witness

/-- Auto-wire `CriticalZeroSumDivergesHyp` from payload. -/
instance (priority := 100)
    [CriticalZeroSumDivergesPayload] :
    Aristotle.Standalone.PsiZeroSumOscillationFromIngham.CriticalZeroSumDivergesHyp where
  proof := CriticalZeroSumDivergesPayload.witness

end Aristotle.Standalone.ExternalPort.B5bPayloadAutoInstances
