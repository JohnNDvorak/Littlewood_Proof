# Aristotle Prompt 2: ExplicitFormulaPsiHyp + General Lift

You are Aristotle. Return exactly one Lean file and nothing else.

Hard constraints:
- No `axiom`, `postulate`, `sorry`, `admit`.
- No abstract placeholder symbols.
- Keep names/signatures unchanged.

```lean
import Mathlib

open scoped BigOperators Real
open Complex

set_option relaxedAutoImplicit false
set_option autoImplicit false
noncomputable section

namespace Aristotle.DirichletPhaseAlignment

noncomputable def chebyshevPsi (x : ℝ) : ℝ := x
def ZerosBelow (_T : ℝ) : Finset ℂ := ∅

class ExplicitFormulaPsiHyp : Type where
  C : ℝ
  psi_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevPsi x - x -
      (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ)^ρ)/ρ).re)| ≤
      C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)

end Aristotle.DirichletPhaseAlignment

namespace Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.DirichletPhaseAlignment

class ExplicitFormulaPsiGeneralHyp : Prop where
  proof :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ)^ρ)/ρ).re)| ≤
      C * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T + (Real.log x)^2)

end Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

namespace Aristotle.Standalone.ExplicitFormulaPsiLegacyGlobalInstance
open Aristotle.DirichletPhaseAlignment

class ExplicitFormulaPsiLegacyPayload : Type where
  witness :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ)^ρ)/ρ).re)| ≤
      C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)

def explicitFormulaPsiHyp_of_payload
    [hPayload : ExplicitFormulaPsiLegacyPayload] :
    ExplicitFormulaPsiHyp := by
  let C : ℝ := Classical.choose hPayload.witness
  have hC :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ)^ρ)/ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
    simpa [C] using Classical.choose_spec hPayload.witness
  exact ⟨C, hC⟩

instance (priority := 100)
    [ExplicitFormulaPsiLegacyPayload] :
    ExplicitFormulaPsiHyp :=
  explicitFormulaPsiHyp_of_payload

end Aristotle.Standalone.ExplicitFormulaPsiLegacyGlobalInstance

namespace Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.DirichletPhaseAlignment
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExplicitFormulaPsiLegacyGlobalInstance

private lemma log_le_inv_log_two_mul_log_sq {u : ℝ} (hu : 2 ≤ u) :
    Real.log u ≤ (Real.log 2)⁻¹ * (Real.log u)^2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : Real.log u * Real.log 2 ≤ (Real.log u)^2 := by
    nlinarith [Real.log_le_log (by norm_num : (1:ℝ) ≤ 2) hu]
  have hdiv : Real.log u ≤ (Real.log u)^2 / Real.log 2 := by
    exact (le_div_iff₀ hlog2_pos).2 (by simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

theorem general_formula_of_legacy_explicit_formula_term
    (hLegacy : ExplicitFormulaPsiHyp) :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ)^ρ)/ρ).re)| ≤
      C * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T + (Real.log x)^2) := by
  let K : ℝ := (Real.log 2)⁻¹
  refine ⟨max (|hLegacy.C| * K) 1, ?_⟩
  intro x T hx hT
  have hBase := hLegacy.psi_approx x T hx hT
  have hSq_nonneg :
      0 ≤ Real.sqrt x * (Real.log T)^2 / Real.sqrt T + (Real.log x)^2 := by positivity
  have hlogT_sq : Real.log T ≤ K * (Real.log T)^2 := by
    simpa [K] using (log_le_inv_log_two_mul_log_sq hT)
  have hlogx_sq : Real.log x ≤ K * (Real.log x)^2 := by
    simpa [K] using (log_le_inv_log_two_mul_log_sq hx)
  have hmain_sq :
      Real.sqrt x * Real.log T / Real.sqrt T ≤
        K * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T) := by
    have hfactor_nonneg : 0 ≤ Real.sqrt x / Real.sqrt T := by positivity
    calc
      Real.sqrt x * Real.log T / Real.sqrt T
          = (Real.sqrt x / Real.sqrt T) * Real.log T := by ring
      _ ≤ (Real.sqrt x / Real.sqrt T) * (K * (Real.log T)^2) :=
            mul_le_mul_of_nonneg_left hlogT_sq hfactor_nonneg
      _ = K * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T) := by ring
  have hLinear_to_sq :
      Real.sqrt x * Real.log T / Real.sqrt T + Real.log x ≤
        K * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T + (Real.log x)^2) := by
    calc
      Real.sqrt x * Real.log T / Real.sqrt T + Real.log x
          ≤ K * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T) + K * (Real.log x)^2 := add_le_add hmain_sq hlogx_sq
      _ = K * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T + (Real.log x)^2) := by ring
  calc
    |chebyshevPsi x - x - (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ)^ρ)/ρ).re)|
        ≤ hLegacy.C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := hBase
    _ ≤ |hLegacy.C| * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
      exact mul_le_mul_of_nonneg_right (le_abs_self hLegacy.C) (by positivity)
    _ ≤ |hLegacy.C| * (K * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T + (Real.log x)^2)) := by
      exact mul_le_mul_of_nonneg_left hLinear_to_sq (abs_nonneg _)
    _ = (|hLegacy.C| * K) * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T + (Real.log x)^2) := by ring
    _ ≤ max (|hLegacy.C| * K) 1 * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T + (Real.log x)^2) := by
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hSq_nonneg

theorem explicitFormulaPsiGeneralHyp_of_legacy_payload
    [ExplicitFormulaPsiLegacyPayload] :
    ExplicitFormulaPsiGeneralHyp := by
  let hLegacy : ExplicitFormulaPsiHyp := inferInstance
  exact ⟨general_formula_of_legacy_explicit_formula_term hLegacy⟩

#check (inferInstance : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp)
#check explicitFormulaPsiGeneralHyp_of_legacy_payload

end Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
```
