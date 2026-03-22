/-
Standalone instances for zeta-zero assumptions WITHOUT importing
Assumptions.lean. This breaks the import cycle:

  Assumptions → CriticalAssumptions → ... → PerronExplicitFormulaProvider

allowing PerronExplicitFormulaProvider to import this file directly.

## RvM lower-bound chain
The Riemann-von Mangoldt route to `ZeroCountingLowerBoundHyp` now also depends
on the explicit half-top boundary `RvmHalfTopZetaVariationBoundHyp` exposed in
`RiemannVonMangoldtReal.lean`, so this file no longer claims to synthesize that
full chain from the local delegated inputs alone:
  `RiemannVonMangoldtReal.rvm_explicit_hyp` provides `ZeroCountingRvmExplicitHyp`
  Instance chain in ZeroCountingFunction.lean:
    `ZeroCountingRvmExplicitHyp` → `ZeroCountingAsymptoticHyp`
      → `ZeroCountingMainTermHyp` → `ZeroCountingLowerBoundHyp`

## Instance 2: ZeroOrdinateLowerBoundHyp
The constructive route now lives in `FirstZeroComputation.lean`:
  `FirstZeroExistsHyp`     → `ZetaHasNontrivialZeroHyp`
  `ZeroFreeBelow1413Hyp`   → `ZeroOrdinateLowerBoundHyp`

This file does NOT claim those computational facts are already proved.
Instead, it exports localized opaque placeholders for the two first-zero
sub-hypotheses, keeping the import graph cycle-free while making the
dependency surface explicit.

Used by: PerronExplicitFormulaProvider.lean, which needs both the large-T zero
counting lower bound and the coarse ordinate bound `1 < Im(ρ)`.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.FirstZeroComputation
import Littlewood.ZetaZeros.RiemannVonMangoldtReal

noncomputable section

namespace ZetaZeros

open FirstZeroComputation

/-- Delegated witness for the existence of a positive nontrivial zero.
    The intended constructive route is the Hardy-Z sign-change framework in
    `FirstZeroComputation.lean`, but that computation is not wired yet. -/
private axiom firstZeroExistsHyp_witness : FirstZeroExistsHyp

/-- Delegated witness for zero-freeness below `14.13`.
    This is the minimal computational input needed to derive
    `ZeroOrdinateLowerBoundHyp` via `FirstZeroComputation.lean`. -/
private axiom zeroFreeBelow1413Hyp_witness : ZeroFreeBelow1413Hyp

/-- Delegated witness for the remaining constructive `ξ'` contour input behind
    the RvM common-zero-mass compatibility lane. This is now stated at the
    boundary/log-integral level rather than the already-composed zero-count
    bound. -/
private axiom xiDerivBoundaryLogIntegralBoundFrom14Hyp_witness :
    XiDerivBoundaryLogIntegralBoundFrom14Hyp

instance instFirstZeroExistsHyp : FirstZeroExistsHyp :=
  firstZeroExistsHyp_witness

instance instZeroFreeBelow1413Hyp : ZeroFreeBelow1413Hyp :=
  zeroFreeBelow1413Hyp_witness

instance instXiDerivBoundaryLogIntegralBoundFrom14Hyp :
    XiDerivBoundaryLogIntegralBoundFrom14Hyp :=
  xiDerivBoundaryLogIntegralBoundFrom14Hyp_witness

-- Verify the active delegated instances still resolve here.
#check (inferInstance : ZetaHasNontrivialZeroHyp)
#check (inferInstance : ZeroOrdinateLowerBoundHyp)
#check (inferInstance : XiDerivBoundaryLogIntegralBoundFrom14Hyp)
#check (inferInstance : XiDerivZeroCountRectMultBoundFrom14Hyp)

end ZetaZeros
