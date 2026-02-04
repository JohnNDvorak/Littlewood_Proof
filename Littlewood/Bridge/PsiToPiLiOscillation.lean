/-
Bridge: Wire ThetaOscillationSqrtHyp + OmegaThetaToPiLiHyp
         → PiLiOscillationSqrtHyp.

This bridge encodes the partial summation transfer:
  θ(x) - x = Ω±(√x)  implies  π(x) - li(x) = Ω±(√x / log x).

The key identity is:
  π(x) - li(x) = (θ(x) - x) / log x + O(√x / log²x)

Since the error term O(√x / log²x) is smaller than √x / log x,
the oscillation in θ(x) - x at scale √x transfers to oscillation
in π(x) - li(x) at scale √x / log x.

DEPENDENCIES:
  - ThetaOscillationSqrtHyp   (θ(x) - x = Ω±(√x), from explicit formula for θ)
  - OmegaThetaToPiLiHyp       (generic Ω± transfer from θ to π-li)

OUTPUT:
  - PiLiOscillationSqrtHyp    (π(x) - li(x) = Ω±(√x / log x))

This completes the chain from ψ oscillation to π-li oscillation:
  PsiOscillationSqrtHyp ─(not directly)─> ThetaOscillationSqrtHyp
                                            ─(this bridge)─> PiLiOscillationSqrtHyp

Note: The transfer from ψ to θ (OmegaPsiToThetaHyp) is FALSE for f = √x.
ThetaOscillationSqrtHyp is therefore stated as a separate hypothesis,
provable independently from the explicit formula for θ.

SORRY COUNT: 0  (pure wiring of existing hypothesis classes)
-/

import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.ExplicitFormulas.ConversionFormulas

noncomputable section

open Schmidt Conversion Filter

/-- θ(x) - x = Ω±(√x) transfers to π(x) - li(x) = Ω±(√x / log x)
    via the generic OmegaThetaToPiLiHyp transfer mechanism. -/
instance [ThetaOscillationSqrtHyp] [OmegaThetaToPiLiHyp] :
    PiLiOscillationSqrtHyp where
  oscillation := by
    -- θ(x) - x = Ω±(√x)
    have h_theta := ThetaOscillationSqrtHyp.oscillation
    -- √x ≤ √x (trivial dominance condition for the transfer)
    have h_dom : ∀ᶠ x in atTop, Real.sqrt x ≤ Real.sqrt x :=
      Eventually.of_forall fun _ => le_rfl
    -- Apply the generic transfer: Ω±(√x) for θ → Ω±(√x / log x) for π-li
    exact OmegaThetaToPiLiHyp.property (fun x => Real.sqrt x) h_dom h_theta
