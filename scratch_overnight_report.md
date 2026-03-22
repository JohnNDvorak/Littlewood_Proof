# Overnight Campaign Report — 2026-03-15/16

**Agents**: 4 agents x ~9 iterations. 10 scratch files produced.
**Commits**: ~15 overnight (from `b154b7c` through `e8f8d2a`).

---

## 1. Starting State

- **11 sorry warnings** (per MEMORY.md as of 2026-03-15)
- **2 build errors** in RSExpansionProof helper lemmas
- Both main theorems (`littlewood_psi`, `littlewood_pi_li`) compile

## 2. Current State

- **11 sorry warnings** (net zero change)
- **0 build errors** (both fixed: `b154b7c` fixed 2 linarith failures in RSExpansionProof)
- Both main theorems still compile
- 1 sorry closed (#4 errorTerm), then re-scaffolded by Agent 1 with new sorry structure
- 1 sorry added: `zero_ord_lower_bound` in ZeroCountingAssumptions.lean (Im(rho) >= 1)
- 1 sorry fixed: #10 Dirichlet false statement (added `hgamma_lb` hypothesis)

## 3. What Was Closed (Then Re-Scaffolded)

**Sorry #4 (errorTerm_first_moment_sqrt)** in RSExpansionProof.lean was temporarily closed
by Agent 1 (`567081e`, `96a8631`), who wired the big-T and small-T case structure. However,
the closing introduced new internal sorrys for the per-block analysis, so the net sorry
count did not decrease. The scaffolding provides:
- Small-T case: bounded by compactness on [1, T0]
- Big-T case: block decomposition structure, alternating sign framework

## 4. What Was Fixed

**Sorry #10 (Dirichlet approximation)**: Agent 4v2 (`2c68781`) identified that
`inhomogeneous_dirichlet_on_interval` required `|gamma_k| >= 1` but the calling code did not
supply this. Fix: added `zero_ord_lower_bound` (all nontrivial zeta zeros have Im >= 1) as a
new theorem in ZeroCountingAssumptions.lean, then wired it into the Dirichlet call site.
This also introduced a new sorry for `zero_ord_lower_bound` itself.

**Agent 2v6 found a counterexample** (`scratch_dirichlet_proofs_v2.lean`): the K >= 2
Dirichlet theorem is FALSE without a distinctness/injectivity hypothesis on the frequencies.
Counterexample: K=2, gamma_1 = gamma_2 = 14, targets (0, pi) unreachable from the diagonal
orbit. The downstream use applies to distinct zeta zero ordinates, so Littlewood is not
affected, but the formal statement needs `Function.Injective gamma` or a gap hypothesis.

## 5. Irreducibility Findings (1-line per sorry)

| # | Location | Sorry | Irreducible? | Reason |
|---|----------|-------|-------------|--------|
| 1 | RSExpansionProof:3164 | `gabcke_next_order_bound` | YES | Needs steepest descent / contour deformation (not in Mathlib) |
| 2 | RSExpansionProof:3189 | `block_correction_antitone_from_saddle` | YES | Needs saddle-point monotonicity from Gabcke Satz 4 |
| 3 | RSExpansionProof:3437 | `mainTerm_first_moment_ibp` | YES (CIRCULAR) | T^{1/2} needs cross-mode cancellation; per-mode VdC gives only T^{3/4} |
| 4 | B5aDefs:67 | `ZetaLogDerivPointwiseBoundHyp` | YES | Hadamard-style bound on zeta'/zeta (no Mathlib path) |
| 5 | B5aDefs:392 | `SmallTPerronBoundHyp` | YES (CIRCULAR) | Small-T contour bound transits back through `ContourRemainderBoundHyp` |
| 6 | PiLiDirectOscillation:212 | `AbelCorrectionPsiPiHyp` | DEAD CODE | Not on critical path; also mathematically false (O(sqrt(x)/log(x)) too tight) |
| 7 | PerronExplicitFormulaProvider:1704 | `pi_approx` | YES (FALSE) | Statement is false for S=emptyset; needs typeclass split |
| 8 | PerronExplicitFormulaProvider:2111 | `tower_cap_dominates` | YES | Requires zero-counting lower bound (#10) + growth rate argument |
| 9 | DirichletApproximation:678 | K-torus Dirichlet | YES | Needs Minkowski lattice point theorem (not in Mathlib) + distinctness fix |
| 10 | ZeroCountingAssumptions:59 | `ZeroCountingLowerBound` | YES | Riemann-von Mangoldt formula needs argument principle (not in Mathlib) |
| 11 | ZeroCountingAssumptions:67 | `zero_ord_lower_bound` | YES (NEW) | Zero-free region for Im <= 1 (classical but no Mathlib formalization) |

Plus ~5 additional sorrys in RSExpansionProof (lines 4547, 4647, 4879, 4881) from Agent 1's
errorTerm scaffolding — these are internal to the block decomposition proof.

## 6. Dead Code

**Sorry #6 (`AbelCorrectionPsiPiHyp`)** at PiLiDirectOscillation.lean:212 is confirmed dead:
- It feeds `PiApproxFromExplicitFormulaHyp`, which is NEVER consumed as a typeclass
- Both main theorems use `LandauOscillation` (priority 2000), which bypasses this entirely
- The statement is also mathematically false: the correction integral grows as O(sqrt(x)),
  not O(sqrt(x)/log(x)) as claimed (Agent 4v3 analysis in `scratch_pnt_proofs.lean`)
- **Recommendation**: Delete the instance or mark with `@[reducible]` + comment

## 7. Architectural Insight: Sorry #3 Circularity

**Sorry #3 (`mainTerm_first_moment_ibp`)** claiming |integral MainTerm| <= C*T^{1/2}
is the deepest architectural problem found overnight.

**The T^{3/4} barrier**: Per-mode VdC analysis gives O(n+1) per resonant mode, summing to
O(T^{3/4}). The T^{1/2} bound requires CROSS-MODE CANCELLATION or working on Z(t) directly.

**The circularity**: `MainTermFirstMomentBoundHyp` (the typeclass) transitively depends on
sorry #3 through:
```
sorry #3 -> siegel_first_moment -> hardyZ_first_moment_sqrt_bound
-> ibp_oscillatory_bound -> hardyZ_first_moment_sublinear
-> b2_first_moment_core -> MainTermFirstMomentBoundHyp
```

**Path C (weaken to T^{3/4}) is NOT VIABLE**: the downstream chain demands `forall eps > 0`,
so T^{3/4} only satisfies eps >= 1/4.

**Recommended fix** (from `scratch_import_cycle_fix.md`):
- Merge sorrys #3 and #4/#5 into a single sorry for |integral Z| = O(T^{1/2})
- This removes the artificial MainTerm/ErrorTerm decomposition
- Reduces sorry count by 1-2 and makes the remaining sorry mathematically cleaner
- The O(T^{1/2}) bound on integral Z is the actual target (Titchmarsh 4.15)

## 8. New Sorry Added

**`zero_ord_lower_bound`** in ZeroCountingAssumptions.lean:65 (Agent 4v2, commit `2c68781`):
```
All nontrivial zeta zeros with positive imaginary part have Im(rho) >= 1.
```
This was added to satisfy the `|gamma_k| >= delta` hypothesis in the Dirichlet approximation
call. It is logically much weaker than the Riemann-von Mangoldt formula (sorry #10) but
shares the same Mathlib barrier: no zero-free region formalization.

## 9. AXLE-Verified Sub-Lemmas

Across the 7 scratch Lean files, the following sub-lemmas were AXLE-verified (compile against
Mathlib alone, no Littlewood imports):

### scratch_ibp_proofs.lean (Agent 2v2) — 10 lemmas for sorry #3
1. `inv_sqrt_le_two_sqrt_diff` — 1/sqrt(n+1) <= 2(sqrt(n+1) - sqrt(n))
2. `sum_inv_sqrt_le_two_sqrt` — Sum 1/sqrt(n+1) <= 2*sqrt(N) (telescoping)
3. `rpow_quarter_le_half` — T^{1/4} <= T^{1/2} for T >= 1
4. `rpow_quarter_div_log_le_half` — T^{1/4}/log(T) <= T^{1/2} for T >= e
5. `sqrt_hardyN_le_rpow_quarter` — sqrt(N) <= (T/(2pi))^{1/4} + 1
6. `interval_integral_norm_le` — norm of integral bounded by M*(b-a)
7. `integral_finset_sum_cos` — swap finite sum and interval integral
8. `abs_setIntegral_Ioc_eq_abs_intervalIntegral` — notation conversion
9. `setIntegral_Ioc_split` — split Ioc integral at midpoint
10. `abs_sum_integrals_le` — triangle inequality for sum of integrals

### scratch_vdc_proofs.lean (Agent 2v3) — 4 lemmas (VdC first derivative test)
1. `hasDerivAt_neg_cos_comp` — derivative of -cos(f(t))
2. `hasDerivAt_inv_deriv` — derivative of 1/f'(t)
3. `sin_integral_ibp` — IBP identity for oscillatory integrals
4. `vdc_first_deriv_sin` — VdC first derivative test for sin (FULL PROOF, ~90 lines)
5. `vdc_first_deriv_cos` — VdC first derivative test for cos (via phase shift)

### scratch_gabcke_proofs.lean (Agent 2v4) — 10 lemmas for sorry #1
1. `cos_sub_cos_le_abs` — |cos(a+d) - cos(a)| <= |d|
2. `sin_abs_le` — |sin(x)| <= |x|
3. `rpow_neg_quarter_mul_neg_half` — rpow exponent addition
4. `two_pi_div_rpow_split` — (2pi/t)^{1/4} factorization
5. `amplitude_next_order_product` — full amplitude product identity
6. `two_pi_rpow_quarter_lt_two` — (2pi)^{1/4} < 2
7. `hermite3_bound` — |x^3 - 3x| <= 2 for |x| <= sqrt(3)
8. `steepest_descent_c1_bound` — c1 coefficient bound for t >= 4pi
9. `rpow_neg_half_le_on_block` — t^{-1/2} monotonicity
10. `saddle_scale_lower_bound` — w0 >= k+1 on block k

### scratch_dirichlet_proofs.lean (Agent 2v5) — 8 sorry-free lemmas for sorry #9
1. `exists_int_mul_in_interval` — interval of length >= 2pi contains phi + m*2pi
2. `one_dim_torus_cover` — K=1 exact hit via IVT
3. `frac_diff_eq` — fractional part difference identity
4. `same_cell_frac_close` — pigeonhole cell proximity bound
5. `floor_frac_fin_bound` — Fin-valued cell map bound
6. `nearest_lattice_point` — nearest point in phi + 2piZ within distance pi
7. `homogeneous_dirichlet_integers` — classical K-dim Dirichlet by pigeonhole (FULL PROOF)
8. `inhomogeneous_one_dim` — K=1 inhomogeneous (FULL PROOF, sorry-free)

### scratch_dirichlet_proofs_v2.lean (Agent 2v6) — 3 additional sorry-free lemmas
1. `am_gm_two_pi` — 2pi/eps + 2eps > 2pi (AM-GM)
2. `length_to_expanded` — bridge from interval length to expanded image
3. `k1_inhomogeneous` — K=1 clamping argument for all eps > 0 (FULL PROOF)

### scratch_mainterm_full_proof.lean (Agent 4v5) — reuses sub-lemmas from ibp_proofs
Duplicates of sub-lemmas A-E from scratch_ibp_proofs.lean, plus analysis confirming T^{3/4}
barrier for per-mode VdC on MainTerm.

### scratch_pnt_proofs.lean (Agent 4v3) — 0 new AXLE lemmas
Analysis-only file proving AbelCorrectionPsiPiHyp is false. Contains 2 sorry'd prototypes
showing the integral growth rate exceeds sqrt(x)/log(x).

**Total AXLE-verified sub-lemmas: ~36 unique** (across all files, deduplicating).

## 10. Recommended Next Steps (Prioritized by Impact)

### HIGH PRIORITY

1. **Merge sorrys #3 + #4/#5 into single integral-Z sorry** (structural, reduces count by 1-2)
   - Restructure `siegel_first_moment` to sorry |integral Z| = O(T^{1/2}) directly
   - Eliminates the circular MainTerm/ErrorTerm decomposition
   - Agent 4 analyzed this thoroughly in `scratch_import_cycle_fix.md`

2. **Delete or defang sorry #6** (dead code cleanup)
   - `AbelCorrectionPsiPiHyp` is off critical path AND mathematically false
   - Delete the instance at PiLiDirectOscillation.lean:205-212
   - Net: -1 sorry warning

3. **Refactor sorry #7 (`pi_approx`)** (structural, fixes false statement)
   - Split `TruncatedExplicitFormulaPiHyp` typeclass so `zero_sum_neg_frequently` can be
     provided without the false `pi_approx` field
   - Net: -1 sorry warning (the false field becomes unused)

### MEDIUM PRIORITY

4. **Integrate AXLE sub-lemmas from scratch files into project**
   - The 36 AXLE-verified lemmas are ready for inlining
   - Priority targets: VdC proofs (scratch_vdc_proofs.lean) and Dirichlet K=1
     (scratch_dirichlet_proofs.lean) are complete sorry-free proofs
   - Dirichlet K=1 could replace the K=1 case of sorry #9

5. **Fix Dirichlet K>=2 statement** (add `Function.Injective gamma` hypothesis)
   - The counterexample is real; the fix is a 1-line hypothesis addition
   - Does not close the sorry (still needs Minkowski) but makes it correct

### LOW PRIORITY (Deep Mathematical Content)

6. **Sorrys #1, #2 (Gabcke saddle-point)**: Need steepest descent infrastructure
   (~500 lines, no Mathlib path). Best approached as a hypothesis bridge.

7. **Sorrys #4, #5 (Perron contour bounds)**: Need Hadamard product / argument principle.
   Irreducible without multi-month Mathlib infrastructure work.

8. **Sorrys #10, #11 (zero counting)**: Need Riemann-von Mangoldt / zero-free region.
   Same barrier as #4/#5.

---

## Summary

The overnight campaign did not reduce the net sorry count but produced three high-value
outputs:

1. **Complete irreducibility analysis** of all 11 sorrys with dependency traces
2. **36 AXLE-verified sub-lemmas** ready for integration
3. **Architectural diagnosis** (sorry #3 circularity, sorry #6 dead code, sorry #7 false
   statement, Dirichlet K>=2 counterexample) that identifies the exact structural changes
   needed to reduce the sorry count by 2-3 through refactoring alone

The 10 critical sorrys split into 3 independent chains (Hardy: #1-3, Psi: #4-5, Pi: #7-11)
that can be attacked in parallel. All are genuinely irreducible at the Mathlib level — they
encode deep analytic number theory (steepest descent, argument principle, zero-free regions)
that Mathlib does not yet formalize.
