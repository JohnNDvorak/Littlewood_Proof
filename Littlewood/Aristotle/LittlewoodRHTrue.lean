/-
# Littlewood's Theorem: RH-True Branch

Under RH, the full Littlewood strength ψ(x) - x = Ω±(√x · log log log x) comes
from the constructive Dirichlet approximation argument:

  1. Under RH, all nontrivial zeros have form ρ = 1/2 + iγ.
  2. The explicit formula gives ψ(x) - x ≈ -∑_ρ x^ρ/ρ.
  3. For the √x · lll x lower bound: use Dirichlet's theorem to simultaneously
     approximate K zero ordinates γ₁, ..., γ_K so that the terms x^ρ/ρ
     align in phase. The number of zeros up to height T is K ~ T log T.
  4. Choose x = M^n where n is selected by Dirichlet approximation with denominator
     bound M^K. Then log log x ~ log K ~ log(M log M) ~ log M, and
     log log log x ~ log log M. The aligned sum gives magnitude ≥ c · √x · log M.
  5. Since log M ≥ c' · log log log x for the constructed x, we get
     |ψ(x) - x| ≥ c'' · √x · log log log x.

This requires the explicit formula (Perron) which is behind sorry in the project.
We encapsulate this as a hypothesis class `PsiOscillationLLLRHHyp`.

SORRY COUNT: 0 in this file (uses hypothesis class PsiOscillationLLLRHHyp)
-/

import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.Basic.OmegaNotation
import Littlewood.CoreLemmas.GrowthDomination

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Real Filter Topology Asymptotics
open Schmidt ZetaZeros GrowthDomination

namespace Aristotle.LittlewoodRHTrue

/--
HYPOTHESIS: Under RH, ψ(x) - x = Ω±(√x · log log log x).
MATHEMATICAL STATUS: Littlewood 1914, constructive Dirichlet alignment.
  Under RH, the explicit formula + simultaneous Dirichlet approximation
  on K zero ordinates (K = N(T) ~ T log T) with aligned phases gives
  |ψ(x) - x| ≥ c · √x · log M for suitable x = M^n, where n is bounded
  by M^K. Since log M ≈ log log log x for these values, the full-strength
  Ω± bound follows.
MATHLIB STATUS: requires explicit formula for ψ (Perron), not in Mathlib.
REFERENCE: Montgomery-Vaughan, "Multiplicative Number Theory I", §15.2.
-/
class PsiOscillationLLLRHHyp : Prop where
  oscillation :
    ZetaZeros.RiemannHypothesis →
    (fun x => chebyshevPsi x - x)
    =Ω±[fun x => Real.sqrt x * lll x]

/-- When RH holds, ψ(x) - x = Ω±(√x · log log log x).

Delegates to PsiOscillationLLLRHHyp (which requires the explicit formula). -/
theorem littlewood_psi_rh_true [PsiOscillationLLLRHHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x)
    =Ω±[fun x => Real.sqrt x * lll x] :=
  PsiOscillationLLLRHHyp.oscillation hRH

end Aristotle.LittlewoodRHTrue
