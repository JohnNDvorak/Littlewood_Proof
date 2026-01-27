-- Basic definitions
import Littlewood.Basic.OmegaNotation
import Littlewood.Basic.ChebyshevFunctions
import Littlewood.Basic.LogarithmicIntegral

-- Zeta zero machinery
import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.ZetaZeros.ZeroDensity
import Littlewood.ZetaZeros.SupremumRealPart

-- Explicit formulas
import Littlewood.ExplicitFormulas.ExplicitFormulaPsi
import Littlewood.ExplicitFormulas.SmoothedVersions
import Littlewood.ExplicitFormulas.ConversionFormulas

-- Core lemmas
import Littlewood.CoreLemmas.LandauLemma
import Littlewood.CoreLemmas.DirichletApproximation
import Littlewood.CoreLemmas.WeightedAverageFormula

-- Aristotle proofs (from Harmonic)
import Littlewood.Aristotle.HardyZReal
import Littlewood.Aristotle.MeanSquare
import Littlewood.Aristotle.FunctionalEquation
import Littlewood.Aristotle.ThreeFourOne
import Littlewood.Aristotle.PerronFormula
import Littlewood.Aristotle.ZeroCounting
import Littlewood.Aristotle.DirichletSeries
import Littlewood.Aristotle.LandauLemma
import Littlewood.Aristotle.LaurentExpansion
import Littlewood.Aristotle.PhragmenLindelof
import Littlewood.Aristotle.SchmidtOscillation
import Littlewood.Aristotle.CriticalZeros
import Littlewood.Aristotle.SchmidtOscillationInfinite
import Littlewood.Aristotle.DirichletApprox
import Littlewood.Aristotle.ZetaZeroInfrastructure
import Littlewood.Aristotle.PhaseAlignment
import Littlewood.Aristotle.PartialSummation
import Littlewood.Aristotle.BinetStirling
import Littlewood.Aristotle.ZetaMoments
import Littlewood.Aristotle.PerronFormulaV2
import Littlewood.Aristotle.ZeroCountingV2

-- Mertens' theorems
import Littlewood.Mertens.MertensFirst

-- Oscillation theorems
import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.Oscillation.SchmidtPi

-- Main theorems
import Littlewood.Main.LittlewoodPsi
import Littlewood.Main.LittlewoodPi

/-!
# Littlewood's 1914 Oscillation Theorem

This library formalizes Littlewood's 1914 proof that π(x) - li(x) changes sign
infinitely many times, specifically:

$$\pi(x) - \text{li}(x) = \Omega_{\pm}\left(\frac{x^{1/2}}{\log x} \log\log\log x\right)$$

## Main Results

* `Littlewood.littlewood_psi` : ψ(x) - x = Ω±(x^{1/2} log log log x)
* `Littlewood.littlewood_pi_li` : π(x) - li(x) = Ω±(x^{1/2}/log x · log log log x)

## References

* J.E. Littlewood, "Sur la distribution des nombres premiers" (1914)
* H.L. Montgomery and R.C. Vaughan, "Multiplicative Number Theory I" (2007)
-/
