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
import Littlewood.Aristotle.HardyZIdentities      -- Hardy square bound, pointwise identity (0 sorries) ✓
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
import Littlewood.Aristotle.ZetaAnalyticProperties -- Zero isolation, finiteness, analyticity (0 sorries) ✓
import Littlewood.Aristotle.OffDiagonalBound       -- Off-diagonal ≤ 8N² (0 sorries) ✓
import Littlewood.Aristotle.OffDiagonalIntegralV2  -- Off-diagonal integral ≤ CN² (0 sorries) ✓
import Littlewood.Aristotle.ThetaLinearBound       -- θ(x) = O(x) (0 sorries) ✓
import Littlewood.Aristotle.ThetaLinearBoundV2     -- θ(n) ≤ Cn via Chebyshev (0 sorries) ✓
import Littlewood.Aristotle.ChebyshevThetaV2       -- ψ = Σ θ(n^{1/k}), θ diff ≤ log C(2n,n) (0 sorries) ✓
import Littlewood.Aristotle.PsiThetaBound          -- |ψ(x) - θ(x)| ≤ C√x (0 sorries) ✓
import Littlewood.Aristotle.PsiThetaCanonicalBound -- canonical ψ/θ transfer lemmas (0 sorries) ✓
import Littlewood.Aristotle.HarmonicSumIntegral    -- ∫H_{N(t)} = Θ(T log T) (0 sorries) ✓
import Littlewood.Aristotle.HorizontalSegmentBounds -- Horizontal segment bounds (0 sorries) ✓
import Littlewood.Aristotle.PerronContourIntegrals -- Perron contour integrals (0 sorries) ✓
import Littlewood.Aristotle.PerronContourIntegralsV2 -- Perron contour integrals v2 (1 sorry)
-- import Littlewood.Bridge.HardyAssemblyAttempt    -- DEPRECATED: V1 exploration file, superseded by V2 chain
import Littlewood.Aristotle.StirlingGammaBounds  -- Stirling/Gamma bounds (0 sorries) ✓
import Littlewood.Aristotle.StirlingBernoulli    -- Bernoulli B1/B2, continuity, ∫B1=B2/2-1/12 (0 sorries) ✓

-- Analysis infrastructure (no conflicts)
import Littlewood.Aristotle.PhragmenLindelofStrip  -- Phragmén-Lindelöf strip bounds (0 sorries) ✓
import Littlewood.Aristotle.PhragmenLindelofV2     -- Phragmén-Lindelöf v2 (0 sorries) ✓
import Littlewood.Aristotle.ThreeFourOneV2         -- 3-4-1 v2 (0 sorries) ✓
import Littlewood.Aristotle.ThreeFourOne           -- 3-4-1 original (0 sorries) ✓
import Littlewood.Aristotle.DirichletApprox        -- Dirichlet approx (0 sorries) ✓
import Littlewood.Aristotle.DirichletSeries        -- Dirichlet series (0 sorries) ✓
import Littlewood.Aristotle.LandauLemma            -- Landau lemma (0 sorries) ✓
import Littlewood.Aristotle.DeepSorries              -- Combined deep mathematical sorry (1 sorry)
import Littlewood.Aristotle.SmoothedExplicitFormula -- Landau contradictions (0 sorries, extracted from DeepSorries)
import Littlewood.Aristotle.LandauContradiction    -- Landau contradiction atoms (4 sorries)
import Littlewood.Aristotle.LandauLittlewood       -- Landau-Littlewood oscillation consequences (0 local sorries)
import Littlewood.Aristotle.LaurentExpansion       -- Laurent at s=1 (0 sorries) ✓
import Littlewood.Aristotle.PhaseAlignment         -- Phase alignment (0 sorries) ✓
import Littlewood.Aristotle.OscillationInfraV2     -- sum_diverges_to_infinity technique (0 sorries) ✓
import Littlewood.Aristotle.CosBound               -- Cos bounds (0 sorries) ✓
import Littlewood.Aristotle.BinetStirling          -- Binet/Stirling (0 sorries) ✓
import Littlewood.Aristotle.Definitions            -- Unified definitions (0 sorries) ✓
import Littlewood.Aristotle.FunctionalEquationHyp  -- Functional equation hypothesis (0 sorries) ✓
import Littlewood.Aristotle.IntegralLogSqrtAsymp  -- ∫log(√(1/4+t²)) = Θ(T log T) (0 sorries) ✓
import Littlewood.Aristotle.IntegralLogAsymp     -- ∫log(√(t/2π)) = Θ(T log T) (0 sorries) ✓
import Littlewood.Aristotle.GammaGrowth           -- Gamma growth bounds, harmonic sums (0 sorries) ✓
import Littlewood.Aristotle.GammaHalfPlane        -- Γ(1/4+it/2) properties for Hardy θ (0 sorries) ✓
import Littlewood.Aristotle.HardyCosSmooth        -- Branch-cut-free hardyCos representation (0 sorries) ✓
import Littlewood.Aristotle.AngularDerivative     -- Derivative of z/‖z‖ for complex-valued real-parameterized maps (0 sorries) ✓
import Littlewood.Aristotle.HardyCosExpDeriv      -- Explicit derivative formula for HardyCosSmooth.hardyCosExp (0 sorries) ✓
-- import Littlewood.Aristotle.HardyCosExpOmega      -- Angular velocity (DEAD CODE: not on critical path, pulls DigammaBinetBound sorry)
import Littlewood.Aristotle.ComplexOscillatoryBound -- Basic complex interval-integral norm bounds (0 sorries) ✓
import Littlewood.Aristotle.StationaryPhasePerMode -- Per-mode Hardy cosine tail wrapper via VdC (0 sorries) ✓
import Littlewood.Aristotle.RiemannVonMangoldt    -- Riemann-von Mangoldt N(T) framework (0 sorries) ✓
import Littlewood.Aristotle.RiemannVonMangoldtV2  -- R-vM formula v2 with xi, ImLogGamma (0 sorries) ✓
import Littlewood.Aristotle.NZerosStirling        -- N(T) from S(T) and Stirling (0 sorries) ✓
import Littlewood.Aristotle.TruncatedExplicitFormula -- Truncated explicit formula for psi (0 sorries) ✓
import Littlewood.Aristotle.ExplicitFormulaPerron    -- Finite-sum explicit formula classes (0 sorries) ✓
import Littlewood.Aristotle.StirlingArgGamma      -- Stirling arg Gamma bounds (0 sorries) ✓
import Littlewood.Aristotle.ZetaBoundsNorm        -- Zeta norm bounds, functional eq (0 sorries) ✓
import Littlewood.Aristotle.ZetaBoundFunctionalEq -- Zeta bounded Re(s)≥1+δ, functional eq (0 sorries) ✓
import Littlewood.Aristotle.HardyZConjugation     -- Hardy Z, completedZeta conjugation (0 sorries) ✓
import Littlewood.Aristotle.CompletedZetaCriticalLine -- Completed zeta real on critical line (0 sorries) ✓
import Littlewood.Aristotle.ExplicitFormulaInfrastructure -- Zeta zeros finite, explicit formula (0 sorries) ✓
import Littlewood.Aristotle.ZetaConjugation         -- Zeta/FE pair conjugation properties (0 sorries) ✓
import Littlewood.Aristotle.DirichletSeriesConvergence -- Dirichlet series summability lemmas (0 sorries) ✓
import Littlewood.Aristotle.HardyZContradiction       -- Hardy Z contradiction infrastructure (0 sorries) ✓
import Littlewood.Aristotle.HardyZMeasurability       -- Hardy Z measurability/integrability (0 sorries) ✓
import Littlewood.Aristotle.RemainderTermAnalysis     -- Remainder term analysis (0 sorries) ✓
import Littlewood.Aristotle.ThetaToPiLiTransferInfra  -- θ→(π-li) exact decomposition identity (0 sorries) ✓
import Littlewood.Aristotle.ZetaConvexityStrip         -- Zeta PL convexity in critical strip (0 sorries) ✓
import Littlewood.Aristotle.MeanSquarePartialSum       -- Mean square partial sum definitions (0 sorries) ✓
import Littlewood.Aristotle.ZeroFreeRegionV2           -- Zero-free region / 3-4-1 infrastructure (0 sorries) ✓
import Littlewood.Aristotle.ZetaBoundsPartialSum       -- Zeta bounds, partial sums, harmonic bound (0 sorries) ✓
import Littlewood.Aristotle.MeanSquareLowerBound        -- Mean square lower bound for partial sum (0 sorries) ✓
import Littlewood.Aristotle.DirichletPolynomialMVT      -- Dirichlet polynomial mean-square infrastructure (0 sorries) ✓
import Littlewood.Aristotle.DiagonalIntegralBound       -- Diagonal integral ≥ c·T·log T (0 sorries) ✓
import Littlewood.Aristotle.ContourInfrastructure       -- Contour defs, measure-zero segments (0 sorries) ✓
import Littlewood.Aristotle.ContourIntegrationV2        -- Cauchy rectangle contour integration infrastructure (0 sorries) ✓
import Littlewood.Aristotle.ZeroCountingRectangle       -- Zero-counting rectangle residue/limit infrastructure (0 sorries) ✓
import Littlewood.Aristotle.ZetaLogDerivInfra           -- -ζ'/ζ pole/log-derivative infrastructure (0 sorries) ✓
import Littlewood.Aristotle.VanDerCorputInfra           -- Van der Corput oscillatory integral infrastructure (0 sorries) ✓
import Littlewood.Aristotle.VdcFirstDerivTest            -- Van der Corput first derivative test: |∫cos(φ)| ≤ 3/m (0 sorries) ✓
import Littlewood.Aristotle.AbelSummation                -- Abel summation + alternating series bound (0 sorries) ✓
import Littlewood.Aristotle.CosPiSqSign                  -- cos(πn²) = (-1)^n + alternating sqrt sum bound (0 sorries) ✓
import Littlewood.Aristotle.DirichletPhaseAlignment     -- Simultaneous Dirichlet phase-alignment infrastructure (0 sorries) ✓
import Littlewood.Aristotle.GammaGrowthGeneral          -- General Gamma growth bounds (0 sorries) ✓
import Littlewood.Aristotle.ZetaBoundGtOne              -- ζ(s) bounded for Re(s) > 1 infrastructure (0 sorries) ✓
import Littlewood.Aristotle.RiemannSiegelBound          -- Riemann-Siegel style Z-function bounds (0 sorries) ✓
import Littlewood.Aristotle.IntervalPartition          -- Finite Ioc integral partition lemmas (0 sorries) ✓
import Littlewood.Aristotle.HardyNProperties           -- hardyN/hardyStart breakpoint properties (0 sorries) ✓
-- import Littlewood.Aristotle.RSBlockDecomposition       -- MERGED into HardyFirstMomentDirect (was 1 sorry)
import Littlewood.Aristotle.RSBlockAmplitude           -- Crude RS block amplitude / O(T^(3/4)) infrastructure
import Littlewood.Aristotle.RSBlockWiring             -- Wiring RSBoundProp + bridge hypothesis to crude ErrorTerm first moment
-- import Littlewood.Aristotle.RSSignStructure           -- MERGED into HardyFirstMomentDirect
-- import Littlewood.Aristotle.RSRemainderAlternating    -- MERGED into HardyFirstMomentDirect
-- import Littlewood.Aristotle.RiemannSiegelFirstMoment  -- MERGED into HardyFirstMomentDirect (was 1 sorry via chain)
import Littlewood.Aristotle.RiemannSiegelSignCancellation -- RS sign cancellation O(T^{1/4}) (0 sorries) ✓
import Littlewood.Aristotle.FresnelIntegrals             -- Fresnel integral evaluations via Gaussian regularization (0 sorries) ✓
import Littlewood.Aristotle.AlmostPeriodicMeanValue      -- Almost-periodic mean value: Parseval, Cesàro, one-sided bounds (0 sorries) ✓
-- import Littlewood.Aristotle.SecondMVT                    -- Second mean value theorem (DEAD CODE: not on critical path)
-- import Littlewood.Aristotle.SecondMVTAtomic              -- Atomic: du Bois-Reymond second MVT (DEAD CODE: not on critical path)
-- import Littlewood.Aristotle.DigammaAsymptotic             -- Digamma-log bound (DEAD CODE: only feeds HardyCosExpOmega/PhaseDerivBounds)
-- import Littlewood.Aristotle.DigammaBinetBound             -- Binet bound (DEAD CODE: 1 sorry, only feeds DigammaAsymptotic)
-- import Littlewood.Aristotle.ThetaDerivAsymptotic         -- θ' asymptotic (DEAD CODE: only feeds HardyCosExpOmega/PhaseDerivBounds)
-- import Littlewood.Aristotle.PhaseDerivBounds             -- Phase bounds (DEAD CODE: not consumed by any critical path file)
-- import Littlewood.Aristotle.StationaryPhaseDecomposition -- MERGED into HardyFirstMomentDirect (was 1 sorry)
-- import Littlewood.Aristotle.HardyFirstMomentDirect       -- MERGED into HardyCriticalLineZerosDirect
import Littlewood.Aristotle.HardySetupRequirements      -- Hardy setup requirements note (documentation-only module)
-- import Littlewood.Aristotle.HardyInfiniteZeros       -- DEPRECATED: V1 has unsatisfiable field signatures (grind works vacuously)
import Littlewood.Aristotle.HardyInfiniteZerosV2        -- Hardy's theorem V2 (0 sorries) ✓
-- import Littlewood.Aristotle.HardyApproxFunctionalEq     -- MERGED into HardyCriticalLineZerosDirect (was 1 sorry)
-- import Littlewood.Aristotle.MeanValueLowerBound         -- MERGED: dead code (was consumed by HardyApproxFunctionalEq)
-- import Littlewood.Aristotle.ZetaPartialSumComparison    -- MERGED: dead code (was consumed by HardyApproxFunctionalEq)
import Littlewood.Aristotle.MeanSquarePartialSumAsymptotic -- Mean square ∫|S_N|² ≥ c·T·log T (0 sorries) ✓
import Littlewood.Aristotle.OscillatorySumBound          -- First moment: |∫ oscillatory| ≤ C·T^(1/2+ε) (0 sorries) ✓
import Littlewood.Aristotle.ContourRectangle             -- Rectangle contour integrals, Cauchy (0 sorries) ✓
import Littlewood.Aristotle.ZetaBoundsV2                  -- Zeta ‖ζ(s)‖≤Re(s)/(Re(s)-1), χ, FE, sinh/Gamma bounds (0 sorries) ✓
import Littlewood.Aristotle.CauchyGoursatRectangle        -- Cauchy-Goursat rectangle theorem (0 sorries) ✓
import Littlewood.Aristotle.ZeroFreeRegionV3               -- Zero-free region: 3-4-1, ζ(1+it)≠0, log-deriv bounds (0 sorries) ✓

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

-- Aristotle status snapshot (verified via lake build sorry warnings)
import Littlewood.Aristotle.MeanSquare             -- Mean square framework (0 sorries) ✓
import Littlewood.Aristotle.ZeroCounting           -- 2 sorries: arg principle, RvM asymptotic
import Littlewood.Aristotle.PhragmenLindelof       -- Critical line bound/convexity/Stirling (0 sorries) ✓
import Littlewood.Aristotle.PartialSummation       -- Partial summation pipeline (0 sorries) ✓
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
-- import Littlewood.Bridge.HardyCriticalLineWiring      -- MERGED: bypassed by HardyCriticalLineZerosDirect
import Littlewood.Bridge.HardyCriticalLineZerosDirect  -- Direct atomic sorry for Hardy's theorem (1 sorry)
import Littlewood.Bridge.HardyFirstMomentWiring      -- Hardy first-moment plumbing (0 sorries) ✓
import Littlewood.Bridge.HardyZUnified                -- Unified Hardy Z exports (0 sorries) ✓
import Littlewood.Bridge.HardyChainTest               -- Hardy chain integration test (0 sorries) ✓
import Littlewood.Bridge.HardyChainHyp                  -- Hardy chain hypothesis classes (0 sorries) ✓
-- import Littlewood.Bridge.MeanSquareBridge              -- MERGED: dead code (was consumed by HardySetupV2Instance)
-- import Littlewood.Bridge.HardySetupV2Instance          -- MERGED: dead code (was consumed by HardyCriticalLineWiring)
import Littlewood.Bridge.LandauOscillation               -- Landau oscillation bridge (0 sorries; uses Aristotle/LandauLittlewood)

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

### Build Status
- Sorry declarations and file counts change over time; check `docs/sorry_manifest.txt`
  and current `lake build` output for exact totals.
- Main theorem sorries: 0
- Hardy chain: V2 canonical (V1 deprecated)

## References

* J.E. Littlewood, "Sur la distribution des nombres premiers" (1914)
* H.L. Montgomery and R.C. Vaughan, "Multiplicative Number Theory I" (2007)
-/
