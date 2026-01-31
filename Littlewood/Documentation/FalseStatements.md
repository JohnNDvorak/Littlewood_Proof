# Known False Statements (Need Fixing)

These statements are mathematically incorrect due to Lean's junk values at poles
or incorrect formulations. **Use the V2/V3/V4 versions instead.**

## 1. FunctionalEquation.lean (OLD - replaced by V2)

### Problem: `zeta_functional_equation`
```lean
theorem zeta_functional_equation :
    riemannZeta s = chi s * riemannZeta (1 - s)
```
- **Why False**: At trivial zeros s = -2, -4, -6, ..., the LHS is 0 but RHS involves
  Γ function poles that produce junk values
- **Fix**: Use `FunctionalEquationV2.lean` with hypothesis `∀ n : ℕ, s ≠ -2*n`

### Status
- File marked as deprecated
- Use `FunctionalEquationV2.lean` for all functional equation needs

## 2. ZeroCounting.lean

### Problem: `RiemannXi_differentiable`
```lean
theorem RiemannXi_differentiable : Differentiable ℂ RiemannXi
```
- **Why False**: RiemannXi = Γ(s/2) * π^(-s/2) * ζ(s), and Γ(s/2) has poles at
  s = 0, -2, -4, ... which produce junk values even though the product should
  cancel nicely
- **Fix**: Use Mathlib's `differentiable_completedRiemannZeta` which handles this correctly

### Problem: `xi_Mathlib_eq_RiemannXi`
```lean
theorem xi_Mathlib_eq_RiemannXi : completedRiemannZeta = RiemannXi
```
- **Why False**: Different handling of poles between the two definitions
- **Fix**: Restrict to `0 < s.re ∧ s.re < 1` (critical strip without poles)

### Problem: `completed_zeta_zeros_eq_zeta_zeros`
```lean
theorem completed_zeta_zeros_eq_zeta_zeros :
    {s | completedRiemannZeta s = 0} = {s | riemannZeta s = 0}
```
- **Why False**: completedRiemannZeta has additional zeros at Γ poles
- **Fix**: Add hypothesis `0 < s.re` to exclude trivial zeros

## 3. PerronFormula.lean

### Problem: `integral_imag_part_arctan`
```lean
theorem integral_imag_part_arctan :
    (∫ ...).im = arctan ...
```
- **Why False**: The integral actually produces a real result, should use `.re`
- **Fix**: Change to `integral_real_part_arctan` with `.re`

## 4. HardyZRealV2.lean (documentation only)

The file documents these as sorries, but they are actually provable:
- `hardyZV2_real` - Z(t) is real-valued
- `hardyZV2_constant_sign_between_zeros` - Sign constancy
- `continuous_hardyZV2` - Z is continuous

**Status**: Use `HardyZRealV4.lean` which has these proved

## Action Items

### Completed Fixes (Session 2026-01-27)
1. ✅ Fixed `zeta_functional_equation` by creating FunctionalEquationV2.lean
2. ✅ Fixed `completed_zeta_zeros_eq_zeta_zeros` by adding `0 < s.re` hypothesis
3. ✅ Fixed `RiemannXi_differentiable` and `xi_Mathlib_eq_RiemannXi`
4. ✅ Fixed `integral_imag_part_arctan` by changing `.im` to `.re`

### Remaining Actions
1. Add deprecation warnings to old file headers
2. Update imports to use V2/V3/V4 versions
3. Consider removing old files entirely after validation

## 5. ZeroCounting.lean: xi_Mathlib_differentiable (FALSE)

```lean
theorem xi_Mathlib_differentiable : Differentiable ℂ xi_Mathlib
-- where xi_Mathlib s = (1/2) * s * (s-1) * completedRiemannZeta s
```

**Why false**: `completedRiemannZeta` returns junk value at s=1, making
`xi_Mathlib(1) = 0` while `lim_{s->1} xi_Mathlib(s) = 1/2` (discontinuous).

**Already documented in file**: Lines 108-117 mark this as deprecated.
`XiDifferentiability.lean` has proof of non-differentiability.

**Correct version**: `ZeroCountingXi.xi_entire` uses `completedRiemannZeta₀`.
Bridge via `xi_Mathlib_eq_corrected` (line 98) for s != 0, 1.

## 6. PartialSummation.lean: psi_oscillation_implies_pi_li_oscillation (UNDERSPECIFIED)

```lean
theorem psi_oscillation_implies_pi_li_oscillation
    (h_psi_pos : ∀ M, ∃ x > M, chebyshevPsi x - x > 0)
    (h_psi_neg : ∀ M, ∃ x > M, chebyshevPsi x - x < 0) :
    (∀ M, ∃ x > M, primeCountingReal x - li x > 0) ∧
    (∀ M, ∃ x > M, primeCountingReal x - li x < 0)
```

**Issue**: Hypotheses only assert sign changes, not quantitative oscillation.
Error terms T(x) and integral may dominate when ψ(x)-x is small.
Needs Ω±(√x) bounds, not just sign change.
Main proof path uses LittlewoodPi.lean's stronger Ω result instead.

## Version Guide

| Definition/Theorem | Old File | New File | Notes |
|-------------------|----------|----------|-------|
| Functional equation | FunctionalEquation.lean | FunctionalEquationV2.lean | Pole restrictions added |
| Hardy Z function | HardyZReal.lean | HardyZRealV4.lean | Full proofs, no sorries |
| Zero counting | ZeroCounting.lean | ZeroCountingNew.lean | Better structure |
| Perron formula | PerronFormula.lean | PerronNew.lean | Infrastructure only |
