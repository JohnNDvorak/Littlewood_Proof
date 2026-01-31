/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Littlewood.Main.LittlewoodPi
import Littlewood.Main.LittlewoodPsi
import Littlewood.Development.ZeroFreeRegion
import Littlewood.Development.TypeBridge
import Littlewood.ZetaZeros.ZeroCountingFunction

/-!
# Test Suite for Main Theorems

This file verifies that all main theorems compile correctly.
It serves as a regression test for the Littlewood formalization.

## Purpose
- Ensure main theorem statements compile
- Catch any breakage in the theorem chain
- Document the key results

## Usage
```
lake build Littlewood.Tests.MainTheorems
```
If this file compiles, all main theorems are well-formed.
-/

namespace Littlewood.Tests

/-! ## Main Oscillation Theorems -/

-- Littlewood's theorem for π(x) - li(x)
#check @LittlewoodPi.littlewood_pi_li

-- Oscillation for ψ(x) - x
#check @Littlewood.littlewood_psi

-- Quantitative versions
#check @LittlewoodPi.pi_gt_li_infinitely_often
#check @LittlewoodPi.pi_lt_li_infinitely_often

/-! ## Zero-Free Region (Development) -/

-- Trigonometric inequality
#check @Littlewood.Development.ZeroFreeRegion.trig_inequality

-- Zeta non-vanishing on Re = 1
#check @Littlewood.Development.ZeroFreeRegion.zeta_ne_zero_on_one_line

-- Euler product
#check @Littlewood.Development.ZeroFreeRegion.zeta_euler_product

-- Log derivative identity
#check @Littlewood.Development.ZeroFreeRegion.neg_zeta_logderiv_eq_vonMangoldt

/-! ## Type Bridge (Development) -/

-- Summatory step
#check @Littlewood.Development.TypeBridge.summatory_step

-- Partial sums monotone
#check @Littlewood.Development.TypeBridge.partial_sums_monotone

/-! ## Zeta Zeros -/

-- Non-trivial zeros set
#check @ZetaZeros.zetaNontrivialZeros

-- Zero counting function
#check @ZetaZeros.zeroCountingFunction

-- Riemann Hypothesis statement
#check @ZetaZeros.RiemannHypothesis'

/-! ## Proved Instances -/

-- These instances have real proofs (no sorry)
-- Located in ZeroCountingFunction.lean
#check ZetaZeros.ZeroConjZeroHyp
#check ZetaZeros.ZeroOneSubZeroHyp

/-! ## Test Complete -/

-- If this compiles, all main theorems are well-formed
example : True := trivial

end Littlewood.Tests
