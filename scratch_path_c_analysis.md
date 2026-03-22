# Path C Analysis: Bypassing Sorry #3 via MainTermFirstMomentBoundHyp

Agent 4 (iteration 6), 2026-03-15.

## Question

Can sorry #3 (`mainTerm_first_moment_ibp`, claiming O(T^{1/2})) be BYPASSED
by routing through `MainTermFirstMomentBoundHyp` (which only needs T^{1/2+eps})?

Agent 4v5 noted that per-mode VdC gives T^{3/4}, not T^{1/2}, and hoped the
weaker T^{3/4} might satisfy the downstream consumer. This analysis traces the
full dependency chain to determine feasibility.

## Verdict: PATH C IS NOT VIABLE

Sorry #3 is on the critical path for BOTH the RSExpansionProof chain AND the
bridge/typeclass chain. Weakening it to T^{3/4} breaks the entire flow.

## Detailed Trace

### The Two Chains

**Chain 1 (RSExpansionProof internal)**:
```
mainTerm_first_moment_ibp [sorry #3, claims T^{1/2}]
  -> siegel_first_moment [combines MainTerm + ErrorTerm, claims T^{1/2}]
    -> hardyZ_first_moment_sqrt_bound [public API, claims T^{1/2}]
```

**Chain 2 (Bridge/typeclass)**:
```
MainTermFirstMomentBoundHyp [typeclass, needs T^{1/2+eps}]
  + ErrorTermFirstMomentBoundHyp [typeclass, needs T^{1/2+eps}]
    -> HardyFirstMomentUpperHyp
      -> combined_atoms (via DeepBlockersResolved)
```

### How Chain 2 is Provided

`MainTermFirstMomentBoundHyp` is supplied by:
```
DeepBlockersResolved.deep_blocker_B2
  := CombinedB1B3DeepLeaf.mainTermFirstMomentBoundHyp_from_analytic_leaf
  := <b1_b3_analytic_deep_leaf.2.2>
  := B2FirstMomentFromExpansion.b2_first_moment_core
```

Inside `b2_first_moment_core` (B2FirstMomentFromExpansion.lean:704-743):
```lean
theorem b2_first_moment_core ... :
    forall eps > 0, exists C > 0, ... |int MainTerm| <= C * T^{1/2+eps} := by
  obtain <C1, hC1_pos, h_hardyZ> :=
    HardyZFirstMomentIBP.hardyZ_first_moment_sublinear eps heps  -- !!
  obtain <C2, hC2_pos, h_et_sublinear> :=
    errorTerm_signed_integral_sublinear h_exp eps heps
  -- |int MainTerm| = |int Z - int Error| <= |int Z| + |int Error|
  --                <= C1*T^{1/2+eps} + C2*T^{1/2+eps}
```

And `hardyZ_first_moment_sublinear` (HardyZFirstMomentIBP.lean:2115-2131):
```lean
theorem hardyZ_first_moment_sublinear :
    forall eps > 0, exists C > 0, ... |int Z| <= C * T^{1/2+eps} := by
  obtain <C, hC, h_ibp> := ibp_oscillatory_bound  -- needs T^{1/2} !!
  -- T^{1/2} <= T^{1/2+eps} via rpow_le_rpow_of_exponent_le
```

And `ibp_oscillatory_bound` (HardyZFirstMomentIBP.lean:2092-2095):
```lean
private theorem ibp_oscillatory_bound :=
  Aristotle.Standalone.RSExpansionProof.hardyZ_first_moment_sqrt_bound
```

### The Circularity

The full dependency chain is:

```
sorry #3 (mainTerm_first_moment_ibp, T^{1/2})
  -> siegel_first_moment (T^{1/2})
    -> hardyZ_first_moment_sqrt_bound (T^{1/2})
      -> HardyZFirstMomentIBP.ibp_oscillatory_bound (T^{1/2})
        -> hardyZ_first_moment_sublinear (T^{1/2+eps})
          -> B2FirstMomentFromExpansion.b2_first_moment_core
            -> MainTermFirstMomentBoundHyp (T^{1/2+eps})
              -> DeepBlockersResolved.deep_blocker_B2
```

**MainTermFirstMomentBoundHyp TRANSITIVELY DEPENDS ON sorry #3.**

### Why T^{3/4} Breaks

If we weaken sorry #3 to T^{3/4}:

1. `siegel_first_moment` gets T^{3/4} (max of T^{3/4} main + T^{1/2} error)
2. `hardyZ_first_moment_sqrt_bound` gets T^{3/4}
3. `ibp_oscillatory_bound` gets T^{3/4}
4. `hardyZ_first_moment_sublinear` tries: T^{3/4} <= T^{1/2+eps}?
   - For eps = 1/4: T^{3/4} <= T^{3/4}. OK.
   - For eps = 0.01: T^{3/4} <= T^{0.51}. **FAILS.**
   - The theorem claims "for ALL eps > 0", so this is BROKEN.

5. `b2_first_moment_core` cannot call `hardyZ_first_moment_sublinear`
6. `MainTermFirstMomentBoundHyp` is not provided
7. `DeepBlockersResolved` breaks

### Why This Can't Be Fixed Downstream

`MainTermFirstMomentBoundHyp` requires:
```
forall eps > 0, exists C > 0, forall T >= 2,
  |int MainTerm| <= C * T^{1/2+eps}
```

With T^{3/4} for int Z and T^{1/2} for int ErrorTerm, the best we get is:
```
|int MainTerm| <= |int Z| + |int Error| <= C*T^{3/4} + C*T^{1/2} = O(T^{3/4})
```

This gives T^{1/2+eps} only for eps >= 1/4. The typeclass demands ALL eps > 0.

### The Deeper Issue

The bridge chain's B2 (MainTermFirstMomentBoundHyp) is NOT an independent
sorry. It flows through `hardyZ_first_moment_sublinear`, which itself depends on
sorry #3 via `hardyZ_first_moment_sqrt_bound`. So:

- Sorry #3 in RSExpansionProof is the UNIQUE source of the first-moment bound
- The bridge/typeclass architecture provides a DIFFERENT INTERFACE (T^{1/2+eps}
  instead of T^{1/2}), but the PROOF flows through the same sorry

## Alternative Approaches (from scratch_mainterm_full_proof.lean)

### Path A: Break the import cycle (RECOMMENDED)
Create `HardyZFirstMomentDirect.lean` that proves |int Z| <= C*T^{1/2}
WITHOUT importing RSExpansionProof. This uses Titchmarsh section 4.15 IBP
directly on Z(t). Then RSExpansionProof can import it and close sorry #3
via |int MainTerm| <= |int Z| + |int ErrorTerm|.

The proof infrastructure already exists in HardyZFirstMomentIBP.lean
Parts 1-5, but that file imports RSExpansionProof (creating the cycle).
The fix is to extract the IBP-on-Z proof into a cycle-free file.

### Path D: Direct mean-value theorem
Use Montgomery-Vaughan mean-value theorem on the Dirichlet polynomial.
Per-mode analysis gives T^{3/4} (not enough), but a collective cancellation
argument (Heath-Brown 1978) could give T^{1/2}. This is what the sorry
*intended* but requires substantial new infrastructure.

## Files Examined

- `Littlewood/Aristotle/Standalone/RSExpansionProof.lean:3434` -- sorry #3
- `Littlewood/Aristotle/Standalone/RSExpansionProof.lean:4767` -- siegel_first_moment
- `Littlewood/Aristotle/Standalone/RSExpansionProof.lean:4815` -- hardyZ_first_moment_sqrt_bound
- `Littlewood/Bridge/HardyFirstMomentWiring.lean:29` -- MainTermFirstMomentBoundHyp definition
- `Littlewood/Bridge/HardyFirstMomentWiring.lean:4280` -- hardyFirstMomentUpper_from_two_bounds
- `Littlewood/Aristotle/HardyZFirstMomentIBP.lean:2092` -- ibp_oscillatory_bound
- `Littlewood/Aristotle/HardyZFirstMomentIBP.lean:2115` -- hardyZ_first_moment_sublinear
- `Littlewood/Aristotle/Standalone/B2FirstMomentFromExpansion.lean:704` -- b2_first_moment_core
- `Littlewood/Aristotle/Standalone/B1B3AnalyticDeepLeaf.lean:304` -- b1_b3_analytic_deep_leaf
- `Littlewood/Aristotle/Standalone/CombinedB1B3DeepLeaf.lean:422` -- mainTermFirstMomentBoundHyp_from_analytic_leaf
- `Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean:118` -- deep_blocker_B2
- `Littlewood/Aristotle/HardyFirstMomentDirect.lean:44` -- HardyFirstMomentUpperHyp instance
- `Littlewood/Aristotle/DeepSorries.lean:235` -- combined_atoms

## Summary

Path C (weaken sorry #3 to T^{3/4} and bypass via MainTermFirstMomentBoundHyp)
is **NOT VIABLE** because MainTermFirstMomentBoundHyp transitively depends on
sorry #3 through the chain:

    sorry #3 -> siegel_first_moment -> hardyZ_first_moment_sqrt_bound
    -> ibp_oscillatory_bound -> hardyZ_first_moment_sublinear
    -> b2_first_moment_core -> MainTermFirstMomentBoundHyp

The T^{3/4} bound propagates through the entire chain and breaks
`hardyZ_first_moment_sublinear`, which needs T^{1/2} to absorb into T^{1/2+eps}.

**Sorry #3 is IRREDUCIBLE at the T^{1/2} level.** The fix requires either:
1. Breaking the import cycle (Path A -- extract IBP-on-Z into cycle-free file), or
2. Inlining the full IBP proof (~800 lines of zetaconvexity + theta monotonicity).
