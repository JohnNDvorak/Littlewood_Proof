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
-- NOTE: Many Aristotle files redefine basic functions (chebyshevPsi, primeCountingReal, li)
-- because they are standalone proofs. Files that conflict with Basic/ are commented out.
-- The theorems in those files are still valid and can be imported individually where needed.

-- Hardy Z function machinery (no conflicts)
import Littlewood.Aristotle.HardyZRealV4           -- Hardy Z (0 sorries) ✓
import Littlewood.Aristotle.HardyZRealV2           -- Hardy Z v2 (0 sorries) ✓
import Littlewood.Aristotle.HardyZReal             -- Hardy Z original (0 sorries) ✓
import Littlewood.Aristotle.HardyZComplete         -- Hardy Z complete (0 sorries) ✓
import Littlewood.Aristotle.HardyAssumptions       -- Hardy assumptions (0 sorries) ✓

-- Functional equation (no conflicts)
import Littlewood.Aristotle.FunctionalEquationV2   -- Functional equation (0 sorries) ✓

-- Schmidt oscillation - SchmidtNew is the main file (has trigPoly_zero_iff_coeffs_zero)
import Littlewood.Aristotle.SchmidtNew             -- Schmidt oscillation (0 sorries) ✓
-- import Littlewood.Aristotle.TrigPolyIndependence -- conflicts with SchmidtNew
-- import Littlewood.Aristotle.SchmidtOscillation  -- conflicts with SchmidtNew

-- Zeta infrastructure (no conflicts with Basic/)
import Littlewood.Aristotle.ZeroCountingNew        -- Zero counting N(T) (0 sorries) ✓
-- import Littlewood.Aristotle.ZeroCountingV2      -- conflicts with ZeroCountingNew (NZeros)
import Littlewood.Aristotle.ZetaZeroInfrastructure -- Zero infrastructure (0 sorries) ✓
import Littlewood.Aristotle.NAsymptotic            -- N(T) asymptotic (0 sorries) ✓
import Littlewood.Aristotle.RiemannXi              -- Riemann Xi entire (1 sorry) ✓ NEW
import Littlewood.Aristotle.ZetaMoments            -- Zeta moments (0 sorries) ✓
import Littlewood.Aristotle.CriticalZeros          -- Critical zeros (0 sorries) ✓

-- Analysis infrastructure (no conflicts)
import Littlewood.Aristotle.PhragmenLindelofV2     -- Phragmén-Lindelöf v2 (0 sorries) ✓
import Littlewood.Aristotle.ThreeFourOneV2         -- 3-4-1 v2 (0 sorries) ✓
import Littlewood.Aristotle.ThreeFourOne           -- 3-4-1 original (0 sorries) ✓
import Littlewood.Aristotle.DirichletApprox        -- Dirichlet approx (0 sorries) ✓
import Littlewood.Aristotle.DirichletSeries        -- Dirichlet series (0 sorries) ✓
import Littlewood.Aristotle.LandauLemma            -- Landau lemma (0 sorries) ✓
import Littlewood.Aristotle.LaurentExpansion       -- Laurent at s=1 (0 sorries) ✓
import Littlewood.Aristotle.PhaseAlignment         -- Phase alignment (0 sorries) ✓
import Littlewood.Aristotle.CosBound               -- Cos bounds (0 sorries) ✓
import Littlewood.Aristotle.BinetStirling          -- Binet/Stirling (0 sorries) ✓
import Littlewood.Aristotle.Definitions            -- Unified definitions (0 sorries) ✓

-- Files that redefine chebyshevPsi/primeCountingReal/li (conflicts with Basic/)
-- These are valid standalone proofs but can't be imported alongside Basic/
-- import Littlewood.Aristotle.PiLiOscillation     -- redefines chebyshevPsi, li
-- import Littlewood.Aristotle.PsiDominance        -- redefines chebyshevPsi
-- import Littlewood.Aristotle.PerronNew           -- redefines chebyshevPsi
-- import Littlewood.Aristotle.PerronFormulaV2     -- redefines chebyshevPsi
-- import Littlewood.Aristotle.ExplicitFormulaV3   -- redefines chebyshevPsi
-- import Littlewood.Aristotle.SchmidtOscillationInfinite -- uses local chebyshevPsi

-- Aristotle files with remaining sorries
import Littlewood.Aristotle.MeanSquare             -- 5 sorries (no conflict)
import Littlewood.Aristotle.ZeroCounting           -- 4 sorries (no conflict)
import Littlewood.Aristotle.PhragmenLindelof       -- 3 sorries (no conflict)
import Littlewood.Aristotle.PartialSummation       -- 2 sorries (has chebyshevPsi but uses Basic import)
import Littlewood.Aristotle.FunctionalEquation     -- 1 sorry (deprecated, use V2)
-- import Littlewood.Aristotle.PerronFormula       -- 6 sorries, redefines chebyshevPsi

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

$$\pi(x) - \text{li}(x) = \Omega_{\pm}\left(\frac{x^{1/2}}{\log x}\right)$$

## Main Results

* `Littlewood.littlewood_psi` : ψ(x) - x = Ω±(x^{1/2})
* `LittlewoodPi.littlewood_pi_li` : π(x) - li(x) = Ω±(x^{1/2}/log x)
* `LittlewoodPi.pi_gt_li_infinitely_often` : π(x) > li(x) infinitely often
* `LittlewoodPi.pi_lt_li_infinitely_often` : π(x) < li(x) infinitely often

## Project Status

The main theorems are proved assuming ~58 hypothesis classes (classical theorems
not yet in Mathlib). See `Assumptions.lean` for the full list.

### Aristotle Files (from Harmonic)
- Total: 37 files
- Sorry-free: 31 files (84%)
- With sorries: 6 files (21 sorries total)

## References

* J.E. Littlewood, "Sur la distribution des nombres premiers" (1914)
* H.L. Montgomery and R.C. Vaughan, "Multiplicative Number Theory I" (2007)
-/
