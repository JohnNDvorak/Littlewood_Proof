/-
# Global HadamardXiCore instance from HadamardFactorizationWiring

Session 12: The chain HadamardXiCanonicalProductApprox → HadamardXiCore
is fully sorry-free in HadamardFactorizationXi.lean (via hadamardXi_core_of_approx,
line 1272). The Wiring provides HadamardXiCanonicalProductApprox at priority 1200.
This file registers the composition as a global instance, making HadamardXiCore
available to all downstream consumers (ZetaLogDerivBound, BacklundDirectProof, etc.)
without any sorry.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.HadamardFactorizationCore
import Littlewood.Aristotle.Standalone.HadamardFactorizationXi

noncomputable section

open HadamardXi
open Aristotle.Standalone.HadamardFactorizationWiring

/-- Global sorry-free `HadamardXiCore` from the constructive Hadamard factorization. -/
instance (priority := 1200) : HadamardXiCore :=
  hadamardXi_core_of_approx hadamardXiApprox_from_factorization

/-- Global `HadamardXiZeroCover`: every xi zero is listed in the enumeration.
    Proved constructively from the canonical product (xi vanishes iff some factor vanishes). -/
instance (priority := 1200) : HadamardXiZeroCover
    (hadamardXiApprox_from_factorization.zeros) where
  xi_complete := hadamardXi_complete_xi_of_approx hadamardXiApprox_from_factorization
