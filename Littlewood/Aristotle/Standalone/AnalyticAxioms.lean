/-
Recovery stub for former analytic axiom providers.

This file intentionally provides no instances and declares no axioms.  The
March 2026 recovery shim installed private analytic axioms here for:

1. `SiegelSaddleExpansionHyp`
2. `HadamardXiCanonicalProductCriticalZeros`
3. `HadamardXiNearZeroSumBound`
4. `HadamardXiFarZeroSumBound`
5. `ShiftedRemainderContourDecompFromLogDerivLargeTHyp`

Those providers are not part of the accepted final axiom policy.  The current
frontier must expose the corresponding analytic content as ordinary theorem
debt or class assumptions, with temporary `sorry` leaves where necessary.

Accepted non-Lean mathematical input remains isolated in
`Littlewood.ZetaZeros.ZeroCountingAssumptions`: the first-zero existence and
zero-free-below-14.13 witnesses.
-/

import Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp
import Littlewood.Aristotle.Standalone.HadamardFactorizationXi
import Littlewood.Development.ShiftedRemainderInterface
import Littlewood.Development.ZetaLogDerivBound

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.AnalyticAxioms

/-! This namespace is kept only so stale references fail locally rather than
reintroducing global analytic providers. -/

end Aristotle.Standalone.AnalyticAxioms
