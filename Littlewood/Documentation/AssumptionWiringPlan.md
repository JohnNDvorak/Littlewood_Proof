# Assumption Wiring Plan

*Updated 2026-01-31*

## Category 1: Already Proved (2)
- ZeroConjZeroHyp ✅ (in ZeroCountingFunction.lean via riemannZeta_conj)
- ZeroOneSubZeroHyp ✅ (in ZeroCountingFunction.lean via functional equation)

## Category 2: Closeable When Hardy Completes (~3-5)

| Assumption | Depends On | Chain |
|------------|------------|-------|
| HardyCriticalLineZerosHyp | Hardy's theorem (mean square + first moment) | Direct |
| PsiOscillationFromCriticalZerosHyp | HardyCriticalLineZerosHyp + explicit formula | Indirect |
| PsiOscillationSqrtHyp | Above + quantitative bounds | Indirect |

## Category 3: Potentially Closeable from Existing Aristotle (investigate)

| Assumption | Potential Source | Status |
|------------|-----------------|--------|
| ZetaLogDerivPoleHyp | LaurentExpansion (complete, 0 sorries) | CHECK signatures |
| ChebyshevErrorBoundThetaHyp | ThetaLinearBound/V2 (0 sorries) | CHECK signatures |
| ZeroCountingAsymptoticHyp | ZeroCountingNew + NAsymptotic (0 sorries) | CHECK signatures |
| ZeroCountingTendstoHyp | ZeroCountingNew (0 sorries) | CHECK signatures |

## Category 4: Need New Aristotle Proofs (~35)

| Family | Count | Key Theorems Needed |
|--------|-------|---------------------|
| Explicit Formula | 11 | Perron's formula, Mellin, contour shifting |
| Weighted Average | 7 | Fejér kernel, phase alignment, sum bounds |
| Schmidt/Oscillation | 5 | Mellin identity, Ω± necessity |
| Zero Counting | 12 | RVM uniform, density estimates, local density |
| Landau | 9 | Pringsheim, Dirichlet analyticity, power series |

## Category 5: Very Deep / Long-term (~5)

| Assumption | Blocker |
|------------|---------|
| ExplicitFormulaPsiHyp | Full Perron + contour integration |
| WeightedAverageFormulaRHHyp | Fejér + RH hypothesis |
| ThetaOscillationRHHyp | Full oscillation theory |
| ZetaZeroSupRealPartDichotomyHyp | Deep zero density theory |
| ZeroFreeRegionHyp | de la Vallée-Poussin type bounds |
