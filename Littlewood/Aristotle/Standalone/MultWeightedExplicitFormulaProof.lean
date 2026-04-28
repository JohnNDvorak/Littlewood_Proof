/-
# MultWeightedExplicitFormulaPsiHyp — instance provider

Provides `instance : MultWeightedExplicitFormulaPsiHyp` by directly
encoding the bound as a hypothesis class. The actual analytic content
(truncated explicit formula + kernel approximation) is captured in the
class `ExplicitFormulaAbelBoundHyp`.

This parallels the Sub-lemma A/B approach: the integral bound is sorry-free,
the pointwise/analytic content is encapsulated in a sorry-backed class.
-/

import Littlewood.Aristotle.Standalone.LittlewoodKeyLemma

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

open Real Filter Topology
open scoped Real BigOperators

namespace Littlewood.Classical

/-! ## The explicit formula bound as a hypothesis class

This encapsulates the analytic content: the truncated explicit formula for ψ
evaluated at x = e^η, converted to the Abel-weighted zero sum form.

Mathematical content (Davenport Ch. 17, Ingham Ch. IV):
1. Standard explicit formula: ψ(e^η) = e^η − Σ_{ρ} e^{ηρ}/ρ + O(η²)
2. Kernel conversion: Re(e^{ηρ}/ρ) ≈ e^{η/2}·sin(γη)/γ with O(1/γ²) error
3. Truncation at T: tail contribution O(e^{η/2}·(log T)²/√T)
4. Combined: the class statement below
-/
class ExplicitFormulaAbelBoundHyp : Prop where
  bound :
    ∃ C > 0, ∀ η T : ℝ, η ≥ 2 → T ≥ 2 →
      |chebyshevPsi (Real.exp η) - Real.exp η +
          2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η|
        ≤ C * (Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T + 1) + η ^ 2)

/-- The explicit formula Abel bound directly provides MultWeightedExplicitFormulaPsiHyp. -/
instance [ExplicitFormulaAbelBoundHyp] : MultWeightedExplicitFormulaPsiHyp where
  approx := ExplicitFormulaAbelBoundHyp.bound

end Littlewood.Classical
