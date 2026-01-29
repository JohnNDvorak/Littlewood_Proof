/-
# Wiring Tests

This file verifies that key Aristotle theorems are accessible from the main project
and documents their types for wiring to hypothesis classes.

No proofs are attempted here — this is purely a compilation/type check.

Co-authored-by: Claude <noreply@anthropic.com>
-/

import Littlewood.Bridge.AristotleWiring
import Littlewood.Bridge.AristotleBridges
import Littlewood.Bridge.ZeroCountingBridge
import Littlewood.Bridge.ThetaEquivalence
import Littlewood.Aristotle.ZeroCountingNew
import Littlewood.Aristotle.NAsymptotic
import Littlewood.Aristotle.SchmidtNew
import Littlewood.Aristotle.HardyZRealV4
import Littlewood.Aristotle.LandauLemma
import Littlewood.Aristotle.ThetaLinearBoundV2
import Littlewood.Aristotle.ChebyshevThetaV2

noncomputable section

/-! ## Available Aristotle Results -/

section AvailableResults

-- ThetaLinearBoundV2: theta(n) = O(n)
#check @ThetaLinearBoundV2.theta_O_n
-- Type: ∃ C, ∀ n, theta n ≤ C * n

-- ThetaLinearBound: theta(x) ≤ Cx for x ≥ 1 (now sorry-free via V2 bridge)
#check @ThetaLinearBound.theta_le_linear
-- Type: ∃ C > 0, ∀ x ≥ 1, theta x ≤ C * x

-- ChebyshevThetaV2: psi = sum of theta at roots
#check @ChebyshevThetaV2.psi_nat_eq_sum_theta_nat
-- Type: psi n = ∑ k, theta (⌊n^(1/(k+1))⌋)

-- ZeroCountingNew: S(T) = O(log T)
#check @ZeroCountingNew.S_isBigO_log
-- Type: S =O[atTop] log

-- NAsymptotic: N(T) asymptotic (conditional on S, RVM, Stirling)
#check @ZetaZeroCount.N_asymptotic
-- Type: (h_S : ...) → (h_RVM : ...) → (h_Stirling : ...) →
--   (fun T => N T - main_term) =O[atTop] log

-- SchmidtNew: trig polynomial zero iff coefficients zero
#check @SchmidtNew.trigPoly_zero_iff_coeffs_zero
-- Type: trigPoly = 0 ↔ all coefficients = 0

-- HardyZRealV4: infinitely many zeros on critical line
#check @HardyZRealV4.hardyZ_infinitely_many_zeros
-- Type: ∀ T, ∃ t > T, hardyZ t = 0

-- LandauLemma: Dirichlet series singularity
#check @landau_dirichlet_singularity
-- Type: For real a : ℕ → ℝ, Dirichlet series has singularity at abscissa

-- Explicit formula (truncated)
#check @TruncatedExplicitFormula.psi_as_trig_sum
-- Type: ψ(x) - x = -2∑ᵨ x^(Re ρ)/|ρ| cos(...) + error

-- ZeroCountingBridge: NZeros definitions agree
#check @NZeros_RVM_eq_zeroCountingFunction
#check @NZeros_root_eq_zeroCountingFunction

-- ThetaEquivalence: theta definitions agree on ℕ
#check @theta_eq_at_nat
-- Type: ThetaLinearBound.theta n = ThetaLinearBoundV2.theta n

-- StirlingArgGamma results
#check @stirling_arg_gamma
#check @im_stirling_term_approx

-- NZerosStirling results
#check @NZerosStirling.S_bound
#check @NZerosStirling.N_from_S_and_Stirling

end AvailableResults

/-! ## Wiring Gap Analysis

### Feasible Bridges (need ~1-3 lemmas each)

1. **ZeroCountingAsymptoticHyp** ← NAsymptotic
   Gap: Need h_RVM and h_Stirling hypotheses satisfied
   Path: RiemannVonMangoldt + StirlingArgGamma + ZeroCountingNew.S_isBigO_log

2. **ZeroCountingTendstoHyp** ← derives from asymptotic
   Gap: Need N(T) → ∞, follows from N(T) ~ T log T

3. **ZeroCountingCrudeBoundHyp** ← NAsymptotic
   Gap: Extract explicit C from O(T log T)

4. **HardyCriticalLineZerosHyp** ← HardyZRealV4
   Gap: hardyZ zeros → riemannZeta zeros on critical line

### Hard Bridges (need substantial new code)

5. **LandauLemmaHyp** ← LandauLemma
   Gap: Real coefficients (a : ℕ → ℝ) vs complex (a : ℕ → ℂ)

6. **SchmidtPsiOscillationHyp** ← SchmidtNew
   Gap: Abstract trig poly result → applied to chebyshevPsi via explicit formula

7. **ZeroCountingRvmExplicitHyp** ← RiemannVonMangoldt
   Gap: ∃ C (uniform) vs ∃ C (per T)

### Missing (no Aristotle proof available)

All explicit formula hypotheses, weighted average, zero-free region,
RH-conditional results (~40+ classes).
-/

end
