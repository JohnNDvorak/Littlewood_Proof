# Hardy Theorem Chain Status

## Goal
Prove: `∀ T : ℝ, ∃ t : ℝ, t > T ∧ riemannZeta (1/2 + t * I) = 0`

## Available Building Blocks (all sorry-free)

| Component | File | Key Theorem |
|-----------|------|-------------|
| Z is real | HardyZRealV4 | `hardyZV4_real` |
| Z is real (alt) | HardyZReal | `completedRiemannZeta_real_on_critical_line` |
| Z continuous | HardyZRealV2 | `continuous_hardyZV2` |
| Z zeros ↔ ζ zeros | HardyZRealV2 | `hardyZV2_zero_iff_zeta_zero` |
| Cauchy-Schwarz | HardyZContradiction | `Z_integral_cauchy_schwarz` |
| Constant sign → |integral| | HardyZContradiction | `Z_constant_sign_implies_integral_eq_abs` |
| Asymptotic contradiction | HardyZContradiction | `asymptotic_contradiction` |
| Contradiction final step | HardyZContradiction | `contradiction_final_step` |
| Sign change → zero (IVT) | HardyTheorem (Dev) | `sign_change_implies_zero` |
| Sign changes → ∀T ∃t | HardyTheorem (Dev) | `hardy_from_sign_changes` |
| Mean square ∫|ζ|² | ZetaMeanSquare | `zeta_second_moment` |
| ζ conjugation | HardyZConjugation | `completedRiemannZeta_conj` (1 sorry in alt proof) |

## The Gap (1 critical sorry)

`HardyTheorem.lean` line 539: `hardyZ_sign_change_in_interval`

This needs the **Riemann-Siegel approximate functional equation** to show Z(t) has explicit oscillatory form, forcing sign changes. The full chain:

1. "Finitely many zeros" → "Eventually constant sign" (trivial for continuous Z)
2. "Eventually constant sign" → |∫Z| grows like ∫|Z| (have this!)
3. ∫|Z|² ≥ cT log T (have this via ZetaMeanSquare)
4. |∫Z| grows too fast → contradicts first moment bound (have contradiction machinery!)
5. Therefore: infinitely many sign changes → infinitely many zeros

## Submitted to Aristotle
- Hardy Infinite Zeros prompt (self-contained, with definitions)
- Needs: Riemann-Siegel explicit formula for Z(t), or direct sign change proof

## Once Hardy Returns
```
Hardy infinite zeros (Set.Infinite)
  → nonzero coefficients in explicit formula
  → Schmidt oscillation (already proved: trigPoly_zero_iff_coeffs_zero)
  → ψ(x) - x = Ω±(√x) (LittlewoodPsi.lean)
  → π(x) - li(x) = Ω±(√x / log x) (LittlewoodPi.lean)
  → MAIN THEOREM COMPLETE
```
