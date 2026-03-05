import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiSkeleton

open Aristotle.DirichletPhaseAlignment (ZerosBelow)

/-- The real part of the zero sum Σ_{|γ|≤T} x^ρ/ρ, abstracted behind a def
to prevent `ring` failures on Finset.sum expressions. -/
def zeroSumRe (x T : ℝ) : ℝ :=
  (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re

/-- The explicit formula error: ψ(x) - x + Σ Re(x^ρ/ρ).
Defined concretely so all B5a mathematical content concentrates
into `shifted_contours_bound`. -/
def shiftedRemainderRe (x T : ℝ) : ℝ :=
  Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + zeroSumRe x T

end Aristotle.Standalone.ExplicitFormulaPsiSkeleton

