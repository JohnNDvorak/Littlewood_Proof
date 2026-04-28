/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.Basic.ChebyshevFunctions

/-!
# Quarantined PNT Asymptotics

These theorem statements were previously derived from the PrimeNumberTheoremAnd package.
They are mathematically correct consequences of the Prime Number Theorem,
but are currently sorry-backed rather than proved from Mathlib.

**STATUS**: QUARANTINED — not imported by any build file.
These do not affect the main build, and they are not axioms.

**FUTURE**: Once Mathlib has a complete PNT proof with these consequences,
these axioms should be replaced with actual proofs and contributed upstream.

**REFERENCES**:
  - Hadamard (1896), de la Vallée-Poussin (1896): PNT
  - Chebyshev (1852): θ(x) ~ x, ψ(x) ~ x
-/

open Nat ArithmeticFunction Finset BigOperators Real Filter
open scoped Chebyshev

namespace ChebyshevExt.Quarantine

/-- θ(x)/x → 1 as x → ∞ (PNT for θ).
Previously derived from PrimeNumberTheoremAnd.chebyshev_asymptotic. -/
theorem chebyshevTheta_asymptotic : Tendsto (fun x => θ x / x) atTop (nhds 1) := by
  sorry

/-- ψ(x)/x → 1 as x → ∞ (PNT for ψ).
Previously derived from PrimeNumberTheoremAnd.WeakPNT''. -/
theorem chebyshevPsi_asymptotic : Tendsto (fun x => ψ x / x) atTop (nhds 1) := by
  sorry

/-- x/2 ≤ θ(x) eventually, consequence of PNT.
Previously derived from PrimeNumberTheoremAnd.chebyshev_asymptotic. -/
theorem chebyshevTheta_eventually_ge : ∀ᶠ x in atTop, x / 2 ≤ θ x := by
  sorry

end ChebyshevExt.Quarantine
