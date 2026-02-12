/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/

/-!
# Bridge: Instances from Gauss (PrimeNumberTheoremAnd) — RETIRED

This file previously provided bridge theorems from the PrimeNumberTheoremAnd package.
The dependency was removed to eliminate 3 external sorry warnings from Wiener.lean.

The three PNT-derived theorems (chebyshevPsi_asymptotic, chebyshevTheta_asymptotic,
chebyshevTheta_eventually_ge) are now axiomatized in Basic/ChebyshevFunctions.lean.

The `th43_b` usage in ThetaToPiLiTransferInfra.lean was replaced with the Mathlib
equivalent `Chebyshev.primeCounting_eq_theta_div_log_add_integral`.

## References

* PrimeNumberTheoremAnd: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
-/
