/-
Full Integration Test
Verifies all main theorems and key infrastructure are accessible.
-/
import Littlewood

-- ============================================================
-- Main Theorems
-- ============================================================

-- Littlewood's theorem for ψ
#check @Littlewood.littlewood_psi

-- Littlewood's theorem for π
#check @LittlewoodPi.littlewood_pi_li

-- Infinitely often π(x) > li(x)
#check @LittlewoodPi.pi_gt_li_infinitely_often

-- Infinitely often π(x) < li(x)
#check @LittlewoodPi.pi_lt_li_infinitely_often

-- ============================================================
-- Key Mathlib Infrastructure
-- ============================================================

-- Zeta non-vanishing on Re(s) ≥ 1
#check @riemannZeta_ne_zero_of_one_le_re

-- Zeta residue at s = 1
#check @riemannZeta_residue_one

-- Von Mangoldt L-series equals -ζ'/ζ
#check @ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div

-- L-series derivative formula
#check @LSeries_hasDerivAt

-- ============================================================
-- Omega Notation
-- ============================================================

#check @Asymptotics.IsOmegaPlusMinus
#check @Asymptotics.IsOmegaPlus
#check @Asymptotics.IsOmegaMinus

-- ============================================================
-- Prime Counting Functions
-- ============================================================

#check @chebyshevPsi
#check @chebyshevTheta
#check @LogarithmicIntegral.logarithmicIntegral

-- ============================================================
-- Hypothesis Classes (to be filled)
-- ============================================================

#check @ZetaZeros.ZeroFreeRegionHyp
#check @Schmidt.SchmidtPsiOscillationHyp
#check @Landau.LandauLemmaHyp
