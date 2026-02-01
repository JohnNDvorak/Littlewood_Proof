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
import Littlewood.Aristotle.HardyInfrastructure    -- Hardy Z + hypotheses structure (0 sorries) ✓
import Littlewood.Aristotle.HardyEstimatesPartial  -- Hardy estimates structure, partial (0 sorries) ✓
import Littlewood.Aristotle.HardyZFirstMoment     -- Hardy Z first moment infrastructure (0 sorries) ✓
import Littlewood.Aristotle.HardyZCauchySchwarz   -- Hardy Z Cauchy-Schwarz + alt formula (0 sorries) ✓
import Littlewood.Aristotle.ConvexityBounds       -- Gamma/sin/cos/PL convexity bounds (0 sorries) ✓

-- Functional equation (no conflicts)
import Littlewood.Aristotle.FunctionalEquationV2   -- Functional equation (0 sorries) ✓

-- Schmidt oscillation - SchmidtNew is the main file (has trigPoly_zero_iff_coeffs_zero)
import Littlewood.Aristotle.SchmidtNew             -- Schmidt oscillation (0 sorries) ✓
-- import Littlewood.Aristotle.TrigPolyIndependence -- conflicts with SchmidtNew
-- import Littlewood.Aristotle.SchmidtOscillation  -- conflicts with SchmidtNew

-- Zeta infrastructure (no conflicts with Basic/)
import Littlewood.Aristotle.ZeroCountingNew        -- Zero counting N(T) (0 sorries) ✓
import Littlewood.Aristotle.ZeroCountingXi         -- xi entire, zero counting (0 sorries) ✓
-- import Littlewood.Aristotle.ZeroCountingV2      -- conflicts with ZeroCountingNew (NZeros)
import Littlewood.Aristotle.ZetaZeroInfrastructure -- Zero infrastructure (0 sorries) ✓
import Littlewood.Aristotle.NAsymptotic            -- N(T) asymptotic (0 sorries) ✓
import Littlewood.Aristotle.RiemannXi              -- Riemann Xi entire (0 sorries) ✓
import Littlewood.Aristotle.RiemannXiEntire        -- RiemannXiAlt entire proof (0 sorries) ✓
import Littlewood.Aristotle.XiDifferentiability    -- Xi differentiability analysis (0 sorries) ✓
import Littlewood.Aristotle.ZetaMoments            -- Zeta moments (0 sorries) ✓
import Littlewood.Aristotle.ZetaMeanSquare         -- Mean square estimates (0 sorries) ✓
import Littlewood.Aristotle.PartialZetaNormSq      -- |partial zeta|² expansion (0 sorries) ✓
import Littlewood.Aristotle.PartialZetaNormSqV2    -- General |partial zeta|² (0 sorries) ✓
import Littlewood.Aristotle.IntegralArctanFormula  -- ∫Re(1/(c+ti)) = 2arctan (0 sorries) ✓
import Littlewood.Aristotle.CriticalZeros          -- Critical zeros (0 sorries) ✓
import Littlewood.Aristotle.ZetaZerosFiniteBelow   -- Finitely many zeros below T (0 sorries) ✓
import Littlewood.Aristotle.ZetaZerosFiniteBelowV2 -- Finite zeros via isolated zeros principle (0 sorries) ✓
import Littlewood.Aristotle.OffDiagonalBound       -- Off-diagonal ≤ 8N² (0 sorries) ✓
import Littlewood.Aristotle.OffDiagonalIntegralV2  -- Off-diagonal integral ≤ CN² (0 sorries) ✓
import Littlewood.Aristotle.ThetaLinearBound       -- θ(x) = O(x) (0 sorries) ✓
import Littlewood.Aristotle.ThetaLinearBoundV2     -- θ(n) ≤ Cn via Chebyshev (0 sorries) ✓
import Littlewood.Aristotle.ChebyshevThetaV2       -- ψ = Σ θ(n^{1/k}), θ diff ≤ log C(2n,n) (0 sorries) ✓
import Littlewood.Aristotle.PsiThetaBound          -- |ψ(x) - θ(x)| ≤ C√x (0 sorries) ✓
import Littlewood.Aristotle.HarmonicSumIntegral    -- ∫H_{N(t)} = Θ(T log T) (0 sorries) ✓
import Littlewood.Aristotle.HorizontalSegmentBounds -- Horizontal segment bounds (0 sorries) ✓
import Littlewood.Aristotle.PerronContourIntegrals -- Perron contour integrals (0 sorries) ✓
import Littlewood.Aristotle.PerronContourIntegralsV2 -- Perron contour integrals v2 (1 sorry)
import Littlewood.Bridge.HardyAssemblyAttempt       -- Hardy assembly exploration (1 sorry)
import Littlewood.Aristotle.StirlingGammaBounds  -- Stirling/Gamma bounds (0 sorries) ✓

-- Analysis infrastructure (no conflicts)
import Littlewood.Aristotle.PhragmenLindelofStrip  -- Phragmén-Lindelöf strip bounds (0 sorries) ✓
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
import Littlewood.Aristotle.FunctionalEquationHyp  -- Functional equation hypothesis (0 sorries) ✓
import Littlewood.Aristotle.IntegralLogSqrtAsymp  -- ∫log(√(1/4+t²)) = Θ(T log T) (0 sorries) ✓
import Littlewood.Aristotle.IntegralLogAsymp     -- ∫log(√(t/2π)) = Θ(T log T) (0 sorries) ✓
import Littlewood.Aristotle.GammaGrowth           -- Gamma growth bounds, harmonic sums (0 sorries) ✓
import Littlewood.Aristotle.RiemannVonMangoldt    -- Riemann-von Mangoldt N(T) framework (0 sorries) ✓
import Littlewood.Aristotle.RiemannVonMangoldtV2  -- R-vM formula v2 with xi, ImLogGamma (0 sorries) ✓
import Littlewood.Aristotle.NZerosStirling        -- N(T) from S(T) and Stirling (0 sorries) ✓
import Littlewood.Aristotle.TruncatedExplicitFormula -- Truncated explicit formula for psi (0 sorries) ✓
import Littlewood.Aristotle.StirlingArgGamma      -- Stirling arg Gamma bounds (0 sorries) ✓
import Littlewood.Aristotle.ZetaBoundsNorm        -- Zeta norm bounds, functional eq (0 sorries) ✓
import Littlewood.Aristotle.HardyZConjugation     -- Hardy Z, completedZeta conjugation (1 sorry)
import Littlewood.Aristotle.CompletedZetaCriticalLine -- Completed zeta real on critical line (0 sorries) ✓
import Littlewood.Aristotle.ExplicitFormulaInfrastructure -- Zeta zeros finite, explicit formula (0 sorries) ✓
import Littlewood.Aristotle.ZetaConjugation         -- Zeta/FE pair conjugation properties (0 sorries) ✓
import Littlewood.Aristotle.DirichletSeriesConvergence -- Dirichlet series summability lemmas (0 sorries) ✓
import Littlewood.Aristotle.HardyZContradiction       -- Hardy Z contradiction infrastructure (0 sorries) ✓
import Littlewood.Aristotle.HardyZMeasurability       -- Hardy Z measurability/integrability (0 sorries) ✓
import Littlewood.Aristotle.ZetaConvexityStrip         -- Zeta PL convexity in critical strip (0 sorries) ✓
import Littlewood.Aristotle.MeanSquarePartialSum       -- Mean square partial sum definitions (0 sorries) ✓
import Littlewood.Aristotle.ZeroFreeRegionV2           -- Zero-free region / 3-4-1 infrastructure (0 sorries) ✓
import Littlewood.Aristotle.ZetaBoundsPartialSum       -- Zeta bounds, partial sums, harmonic bound (0 sorries) ✓
import Littlewood.Aristotle.MeanSquareLowerBound        -- Mean square lower bound for partial sum (0 sorries) ✓
import Littlewood.Aristotle.DiagonalIntegralBound       -- Diagonal integral ≥ c·T·log T (4 sorries)
import Littlewood.Aristotle.ContourInfrastructure       -- Contour defs, measure-zero segments (3 sorries)
import Littlewood.Aristotle.HardyInfiniteZeros          -- Hardy's theorem V1: BUGGY field signatures (grind works vacuously)
import Littlewood.Aristotle.HardyInfiniteZerosV2        -- Hardy's theorem V2: FIXED field signatures (canonical path)
import Littlewood.Aristotle.HardyApproxFunctionalEq     -- Approx functional eq: ∫Z²≥k∫|S_N|²-CT (0 sorries) ✓
import Littlewood.Aristotle.MeanSquarePartialSumAsymptotic -- Mean square ∫|S_N|² ≥ c·T·log T (0 sorries) ✓
import Littlewood.Aristotle.OscillatorySumBound          -- First moment: |∫ oscillatory| ≤ C·T^(1/2+ε) (0 sorries) ✓
import Littlewood.Aristotle.ContourRectangle             -- Rectangle contour integrals, Cauchy (1 sorry)

-- Files that redefine chebyshevPsi/primeCountingReal/li (conflicts with Basic/)
-- These are valid standalone proofs but can't be imported alongside Basic/
-- import Littlewood.Aristotle.ChebyshevTheta     -- redefines psi, theta (3 sorries) - KEY: psi_theta_bound, theta_le_linear
-- import Littlewood.Aristotle.PiLiOscillation     -- redefines chebyshevPsi, li
-- import Littlewood.Aristotle.PsiDominance        -- redefines chebyshevPsi
-- import Littlewood.Aristotle.PerronNew           -- redefines chebyshevPsi
-- import Littlewood.Aristotle.PerronFormulaV2     -- redefines chebyshevPsi
-- import Littlewood.Aristotle.ExplicitFormulaV3   -- redefines chebyshevPsi
-- import Littlewood.Aristotle.SchmidtOscillationInfinite -- uses local chebyshevPsi
-- import Littlewood.Aristotle.PartialSummationPiLi -- redefines chebyshevPsi, primeCountingReal, li

-- Aristotle files with remaining sorries (verified via lake build sorry warnings)
import Littlewood.Aristotle.MeanSquare             -- 3 sorries: off-diag bound, normSq decomp, main thm
import Littlewood.Aristotle.ZeroCounting           -- 3 sorries: xi diff (deprecated), arg principle, RvM
import Littlewood.Aristotle.PhragmenLindelof       -- 3 sorries: critical line bound, convexity, Stirling
import Littlewood.Aristotle.PartialSummation       -- 1 sorry: π(x)-li(x) sign changes from ψ(x)-x
-- import Littlewood.Aristotle.FunctionalEquation  -- DEPRECATED: 1 sorry, use FunctionalEquationV2
-- import Littlewood.Aristotle.PerronFormula       -- 5 sorries, redefines chebyshevPsi
-- import Littlewood.Aristotle.PrimePowerSums      -- 4 sorries, redefines psi

-- Bridge lemmas (connect Aristotle proofs to hypothesis classes)
import Littlewood.Bridge.AristotleBridges          -- Bridge lemmas (0 sorries) ✓
import Littlewood.Bridge.HypothesisInstances       -- All proved instances (0 sorries) ✓
import Littlewood.Bridge.AristotleHypothesisConnections  -- Documentation (0 sorries) ✓
import Littlewood.Bridge.AristotleWiring           -- Master wiring file (0 sorries) ✓
import Littlewood.Bridge.ZeroCountingBridge        -- NZeros definition bridges (0 sorries) ✓
import Littlewood.Bridge.ThetaEquivalence          -- theta ℝ→ℝ ↔ ℕ→ℝ equivalence (0 sorries) ✓
import Littlewood.Bridge.WiringTests               -- Compilation tests for available theorems (0 sorries) ✓
import Littlewood.Bridge.HardyZTransfer            -- Hardy Z type transfer bridge (0 sorries) ✓
import Littlewood.Bridge.HardyBuildingBlocksInstance  -- BuildingBlocks 4/6 fields template (0 sorries) ✓
import Littlewood.Bridge.HardyZDefinitionMap          -- Hardy Z variant equivalences (0 sorries) ✓
import Littlewood.Bridge.HardyCriticalLineWiring      -- Pre-wired for Hardy completion (0 sorries) ✓
import Littlewood.Bridge.HardyZUnified                -- Unified Hardy Z exports (0 sorries) ✓
import Littlewood.Bridge.HardyChainTest               -- Hardy chain integration test (0 sorries) ✓
import Littlewood.Bridge.MeanSquareBridge              -- Mean square bridge: DiagBound + ApproxFuncEq (2 sorries)
import Littlewood.Bridge.HardySetupV2Instance          -- HardySetupV2 instance: 3/6 proved, 3 sorry

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
- Total: 87 files (+ 4 deprecated/templates)
- Sorry-free: 81 active files (93%)
- With sorries: 6 active files (12 sorry declarations)
- Sorry breakdown: MeanSquare(3), ZeroCounting(3, 1 deprecated), PhragmenLindelof(3),
  PartialSummation(1), PerronContourIntegralsV2(1), HardyZConjugation(1),
  CoreLemmas/LandauLemma(1), HardyAssemblyAttempt(1)

## References

* J.E. Littlewood, "Sur la distribution des nombres premiers" (1914)
* H.L. Montgomery and R.C. Vaughan, "Multiplicative Number Theory I" (2007)
-/
