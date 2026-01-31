# Detailed Sorry Audit — Aristotle Files

~~19~~ **16 sorries** across ~~9~~ **6 files** remaining. 3 closed manually (RiemannVonMangoldtV2, PsiThetaBound, ZeroFreeRegionV2). Categorized by fixability.

## Category A: Likely Fixable (4 sorries)

These need the right Mathlib lemma or a short proof.

| File | Theorem | Line | What's Needed |
|------|---------|------|---------------|
| ChebyshevTheta | `sum_vonMangoldt_eq_sum_prime_powers_nat` | 65 | Prime power decomposition — **superseded by ChebyshevThetaV2** |
| ChebyshevTheta | `psi_nat_eq_sum_theta_nat` | 73 | Sum over k-th roots — **superseded by ChebyshevThetaV2** |
| ChebyshevTheta | `theta_diff_le_log_choose` | 225 | Binomial bound — **superseded by ChebyshevThetaV2** |
| ~~RiemannVonMangoldtV2~~ | ~~`N_eq_main_plus_S`~~ | ~~75~~ | ~~Stirling + logarithm identities~~ — **CLOSED** (commit d17b9b9) |

**Note:** All 3 ChebyshevTheta sorries are moot — the V2 file proves the same theorems sorry-free.

## Category B: Computational (3 sorries)

These failed due to exact? budget exhaustion or Finset manipulation.

| File | Theorem | Line | What's Needed |
|------|---------|------|---------------|
| MeanSquare | `normSq_partialZeta_eq` | 230 | Expand |partial ζ|² into diagonal + off-diagonal |
| ~~PsiThetaBound~~ | ~~`psi_eq_sum_log_p_mul_count`~~ | ~~108~~ | ~~Finset.biUnion bijection~~ — **CLOSED** (commit d17b9b9) |
| ~~ZeroFreeRegionV2~~ | ~~`zeta_log_deriv_341`~~ | ~~117~~ | ~~Fubini sum interchange~~ — **CLOSED** (commit d17b9b9) |

## Category C: Deep Analytic (8 sorries)

These require genuine mathematical proofs beyond tactic search.

| File | Theorem | Line | What's Needed |
|------|---------|------|---------------|
| HardyZConjugation | `HurwitzZeta_Λ₀_conj` | 116 | Mellin transform conjugation identity |
| MeanSquare | `norm_integral_offDiagSsq_le` | 215 | Off-diagonal oscillatory integral bound |
| MeanSquare | `mean_square_partial_zeta_asymp` | 244 | Mean square = Θ(T log T), depends on prior 2 |
| PartialSummation | `psi_oscillation_implies_pi_li...` (×2) | 238, 241 | Need quantitative Ω±(√x) bounds, not just sign changes |
| PerronContourIntegralsV2 | `integral_boundary_rect_perron_neg` | 442 | Cauchy-Goursat for rectangle contour |
| PhragmenLindelof | `zeta_critical_line_bound` | 153 | |ζ(1/2+it)| = O(|t|^{1/2}) |
| PhragmenLindelof | `zeta_convexity_bound` | 167 | Phragmén-Lindelöf interpolation |
| PhragmenLindelof | `gamma_growth` | 177 | Stirling's approximation for Gamma |

## Category D: FALSE / Deprecated (1 sorry)

| File | Theorem | Line | Issue |
|------|---------|------|-------|
| ZeroCounting | `xi_Mathlib_differentiable` | 123 | **FALSE** — `xi_Mathlib` has poles at s=0,1. File comments explicitly note this. Use `xi_Mathlib_corrected_entire` from ZeroCountingXi instead. |

## Category E: Minor / Cleanup (2 sorries)

| File | Theorem | Line | What's Needed |
|------|---------|------|---------------|
| PartialSummation | `psi_oscillation_implies_pi_li...` (×2) | 238, 241 | **Reclassified to C** — requires quantitative bounds |

**Revised count:** 0 in category E. The PartialSummation sorries were initially rated E but are actually C.

## Summary by Priority

| Priority | Count | Files | Action |
|----------|-------|-------|--------|
| Skip (superseded) | 3 | ChebyshevTheta | Already proved in ChebyshevThetaV2 |
| Skip (false) | 1 | ZeroCounting | Known FALSE, use alternative |
| ~~Medium effort~~ | ~~4~~ → **1** | MeanSquare(1) remaining | 3 closed (d17b9b9) |
| Deep work | 8 | PhragmenLindelof(3), MeanSquare(2), PartialSummation(2), PerronContourIntegrals | New Aristotle prompts |
| Specialized | 1 | HardyZConjugation | Mellin theory |
| **Net actionable** | **1** | MeanSquare `normSq_partialZeta_eq` | Last computational fix |
| **Net blocked** | **11** | | Need new proofs or Aristotle |

## Impact Analysis

### If all 19 sorries were closed:
- PhragmenLindelof: Would give `zeta_critical_line_bound` — **fills Hardy chain requirement #2**
- MeanSquare: Would give `mean_square_partial_zeta_asymp` — **partial Hardy chain requirement #1**
- PerronContourIntegrals: Would advance explicit formula infrastructure

### Highest-value sorry to close:
**PhragmenLindelof.zeta_critical_line_bound** — this is Hardy chain requirement #2.
If Aristotle can't deliver it, this is the most impactful single sorry to close manually.

## Files Without Sorries (complete)

These Aristotle files are entirely sorry-free and ready for use:

- BinetStirling.lean ✓
- ChebyshevThetaV2.lean ✓
- CompletedZetaCriticalLine.lean ✓
- CosBound.lean ✓
- CriticalZeros.lean ✓
- Definitions.lean ✓
- DirichletApprox.lean ✓
- DirichletSeries.lean ✓
- DirichletSeriesConvergence.lean ✓
- ExplicitFormulaInfrastructure.lean ✓
- FunctionalEquationHyp.lean ✓
- FunctionalEquationV2.lean ✓
- GammaGrowth.lean ✓
- HardyAssumptions.lean ✓
- HardyEstimatesPartial.lean ✓
- HardyInfrastructure.lean ✓
- HardyZComplete.lean ✓
- HardyZContradiction.lean ✓
- HardyZReal.lean ✓
- HardyZRealV2.lean ✓
- HardyZRealV4.lean ✓
- HarmonicSumIntegral.lean ✓
- HorizontalSegmentBounds.lean ✓
- IntegralArctanFormula.lean ✓
- IntegralLogAsymp.lean ✓
- IntegralLogSqrtAsymp.lean ✓
- LandauLemma.lean ✓
- LaurentExpansion.lean ✓
- NAsymptotic.lean ✓
- NZerosStirling.lean ✓
- OffDiagonalBound.lean ✓
- OffDiagonalIntegralV2.lean ✓
- PartialSummationPiLi.lean ✓
- PartialZetaNormSq.lean ✓
- PartialZetaNormSqV2.lean ✓
- PerronContourIntegrals.lean ✓
- PerronFormulaV2.lean ✓
- PerronNew.lean ✓
- PhaseAlignment.lean ✓
- PsiThetaBound.lean ✓ *(sorry closed d17b9b9)*
- PhragmenLindelofStrip.lean ✓
- PhragmenLindelofV2.lean ✓
- PiLiOscillation.lean ✓
- PsiDominance.lean ✓
- RiemannVonMangoldt.lean ✓
- RiemannVonMangoldtV2.lean ✓ *(sorry closed d17b9b9)*
- RiemannXi.lean ✓
- RiemannXiEntire.lean ✓
- SchmidtNew.lean ✓
- SchmidtOscillation.lean ✓
- SchmidtOscillationInfinite.lean ✓
- StirlingArgGamma.lean ✓
- StirlingGammaBounds.lean ✓
- ThetaLinearBound.lean ✓
- ThetaLinearBoundV2.lean ✓
- ThreeFourOne.lean ✓
- ThreeFourOneV2.lean ✓
- TrigPolyIndependence.lean ✓
- TruncatedExplicitFormula.lean ✓
- XiDifferentiability.lean ✓
- ZeroCountingNew.lean ✓
- ZeroCountingV2.lean ✓
- ZeroCountingXi.lean ✓
- ZetaBoundsNorm.lean ✓
- ZetaBoundsPartialSum.lean ✓
- ZetaConjugation.lean ✓
- ZetaMeanSquare.lean ✓
- ZetaMoments.lean ✓
- ZetaZeroInfrastructure.lean ✓
- ZeroFreeRegionV2.lean ✓ *(sorry closed d17b9b9)*
- ZetaZerosFiniteBelow.lean ✓
- ZetaZerosFiniteBelowV2.lean ✓
