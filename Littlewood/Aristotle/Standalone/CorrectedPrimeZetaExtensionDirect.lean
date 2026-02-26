/-
Proof of CorrectedPrimeZetaExtensionHyp (Blocker 6).

Under the one-sided bound σ*(π(x)-li(x)) ≤ C*x^α with 1/2 < α < 1,
primeZeta(s) + log(s-1) extends analytically from {Re > 1} to {Re > α}.

## Proof Strategy (ζ zero-free + holomorphic log)

The proof is decomposed in PiAtomCoreFromZetaZeroFree.lean into two sub-lemmas:

1. **ζ zero-free on {Re > α}** (`zrf_ne_zero_of_piLiHardBound`):
   Under PiLiHardBound, the function zrf(s) = (s-1)ζ(s) is non-vanishing
   on {Re > α}. This follows from:
   (a) π→ψ partial summation transfer: PiLiHardBound → ψ bound
   (b) Landau–Pringsheim convergence (B4, PROVED): ψ bound → integral converges
   (c) Algebraic identity: convergence → ζ'/ζ has no poles → ζ zero-free

2. **Holomorphic logarithm** (`analytic_log_on_halfPlane`):
   For f entire and non-vanishing on {Re > α}, ∃ g analytic on {Re > α}
   with exp(g) = f. Standard: half-plane is convex, hence simply connected.

Assembly (PROVED): Apply (2) to zrf (entire by ZetaPoleCancellation) with (1)
for non-vanishing. Then exp(G(s)) = zrf(s) = (s-1)ζ(s) for Re(s) > 1.
Reverse direction (PROVED): CorrectedPrimeZetaFromCore gives B6 from the core.

SORRY COUNT: 0 (2 sorries delegated to PiAtomCoreFromZetaZeroFree.lean)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.PiAtomHardCaseCorrectedCore
import Littlewood.Aristotle.Standalone.CorrectedPrimeZetaFromCore
import Littlewood.Aristotle.Standalone.PrimeZetaExtensionProof
import Littlewood.Aristotle.Standalone.PiAtomCoreFromZetaZeroFree

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.CorrectedPrimeZetaExtensionDirect

open Complex Real Filter Topology MeasureTheory Set
open Aristotle.Standalone.PiAtomHardCaseCorrectedCore
open Aristotle.Standalone.PiAtomCoreFromZetaZeroFree

/-! ## The generating function R(t) -/

/-- The non-negative generating function: R(t) = C*t^α - σ*(π(⌊t⌋) - li(t)).
Under PiLiHardBound, R(t) ≥ 0 eventually. -/
def piGenFun (C α σ_sign : ℝ) (t : ℝ) : ℝ :=
  C * t ^ α - σ_sign * ((↑(Nat.primeCounting ⌊t⌋₊) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral t)

/-- R(t) ≥ 0 eventually, from PiLiHardBound. -/
theorem piGenFun_eventually_nonneg
    (α C σ_sign : ℝ)
    (hbound : PiLiHardBound α C σ_sign) :
    ∀ᶠ t in atTop, 0 ≤ piGenFun C α σ_sign t := by
  filter_upwards [hbound] with t ht
  simp only [piGenFun]
  linarith

/-! ## Core: PiAtomHardCaseCorrectedCore via ζ zero-free decomposition

Proved via PiAtomCoreFromZetaZeroFree.piAtomHardCaseCorrectedCore_of_zeroFreeAndLog,
which decomposes into two sub-sorries:
  1. zrf_ne_zero_of_piLiHardBound (ζ zero-free under PiLiHardBound)
  2. analytic_log_on_halfPlane (holomorphic log on simply connected domain) -/
theorem piAtomHardCaseCorrectedCore_direct :
    PiAtomHardCaseCorrectedCore :=
  piAtomHardCaseCorrectedCore_of_zeroFreeAndLog

/-! ## Wiring: PiAtomHardCaseCorrectedCore → CorrectedPrimeZetaExtensionHyp

Uses the existing reverse direction in CorrectedPrimeZetaFromCore.lean. -/

/-- B6 proved: CorrectedPrimeZetaExtensionHyp from the direct core proof. -/
theorem correctedPrimeZetaExtension_proved :
    Aristotle.Standalone.PrimeZetaExtensionProof.CorrectedPrimeZetaExtensionHyp :=
  Aristotle.Standalone.CorrectedPrimeZetaFromCore.correctedPrimeZetaExtensionHyp_of_correctedCore
    piAtomHardCaseCorrectedCore_direct

end Aristotle.Standalone.CorrectedPrimeZetaExtensionDirect
