/-
**LandauAbscissaHypProved**: Final assembly proving `PringsheimPsiAtom.LandauAbscissaHyp`
unconditionally (no sorry, no hypotheses).

This eliminates the `PhaseAlignmentToTargetHyp` (GSH) dependency by implementing
Landau's 1905 Satz 15: the abscissa of convergence of a non-negative Dirichlet
integral is a singularity.

## Assembly chain

1. `SigmaLtOneFromPringsheimExtension.sigmaLtOneHyp_proved`
   proves `LandauAbscissaProof.SigmaLtOneHyp` via:
   - Pringsheim singularity theorem on the real line (`PringsheimRealBootstrap`)
   - Anti-coefficient summability from Cauchy domination
   - Tonelli interchange for non-negative Taylor coefficients

2. `LandauAbscissaProof.landau_abscissa_hyp_proved`
   reduces `PringsheimPsiAtom.LandauAbscissaHyp` to `SigmaLtOneHyp`:
   - Compact part [1, T₀]: bounded integrand on finite-measure set
   - σ₀ > 1 case: direct convergence from growth bounds
   - σ₀ = 1 case: MCT push from σ ↘ 1
   - σ₀ < 1 case: dispatched via `SigmaLtOneHyp`

3. `ZetaPoleCancellation` provides pole cancellation at s = 1.

## References

* Landau, "Über einen Satz von Tschebyschef" (1905), Satz 15
* Hardy-Riesz, "The General Theory of Dirichlet's Series", Ch. 1

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.LandauAbscissaProof
import Littlewood.Aristotle.Standalone.SigmaLtOneFromPringsheimExtension

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Aristotle.LandauAbscissaHypProved

open Aristotle.LandauAbscissaProof
open Aristotle.Standalone.SigmaLtOneFromPringsheimExtension

/-- **Landau's abscissa of convergence theorem — fully proved**.

For g(t) = C·t^α + σ·(t - ψ(t)) ≥ 0 eventually, the Dirichlet integral
∫₁^∞ g(t)·t^{-(s+1)} dt converges absolutely for Re(s) > α, and the
witness function G is analytic on {Re(s) > α}.

This is the unconditional proof of `PringsheimPsiAtom.LandauAbscissaHyp`,
assembled from:
- `sigmaLtOneHyp_proved` (Pringsheim extension on the real line)
- `landau_abscissa_hyp_proved` (compact + tail integrability wiring) -/
theorem landauAbscissaHyp : Aristotle.PringsheimPsiAtom.LandauAbscissaHyp :=
  landau_abscissa_hyp_proved sigmaLtOneHyp_proved

end Aristotle.LandauAbscissaHypProved
