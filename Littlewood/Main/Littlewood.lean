/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.Main.LittlewoodPi
import Littlewood.Main.LittlewoodPsi

/-!
# Littlewood's Oscillation Theorem - Main Exports

This file re-exports the main results of Littlewood's 1914 theorem on the
oscillation of π(x) - li(x).

## Main Theorems

* `LittlewoodPi.littlewood_pi_li` : π(x) - li(x) = Ω±(x^{1/2}/log x · log log log x)
* `Littlewood.littlewood_psi` : ψ(x) - x = Ω±(x^{1/2} · log log log x)
* `LittlewoodPi.pi_gt_li_infinitely_often` : π(x) > li(x) infinitely often
* `LittlewoodPi.pi_lt_li_infinitely_often` : π(x) < li(x) infinitely often

## Historical Significance

Littlewood's 1914 result resolved a century-old question about the relationship
between π(x) and li(x). Gauss had observed that li(x) > π(x) for all computed
values, and this pattern was expected to continue. Littlewood proved this must
fail infinitely often, though he gave no explicit bound on when.

The first explicit bound was given by Skewes in 1933 (assuming RH):
  x < exp(exp(exp(79)))

Modern bounds are much smaller, around 10^316.

## References

* J.E. Littlewood, "Sur la distribution des nombres premiers" (1914)
* S. Skewes, "On the difference π(x) - li(x)" (1933)
* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 15
-/

-- Re-export all main results
#check LittlewoodPi.littlewood_pi_li
#check Littlewood.littlewood_psi
#check LittlewoodPi.pi_gt_li_infinitely_often
#check LittlewoodPi.pi_lt_li_infinitely_often
#check LittlewoodPi.pi_minus_li_sign_changes
