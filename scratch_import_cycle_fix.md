# Import Cycle Fix: RSExpansionProof <-> HardyZFirstMomentIBP

## Agent 4, Iteration 7 — Analysis Report (2026-03-15)

---

## 1. The Import Cycle

```
RSExpansionProof.lean
  |- imports: HardyZFirstMoment, HardyNProperties, ErrorTermExpansion,
  |           RSBlockParam, FunctionalEquationV2, HardyZTransfer,
  |           HardyThetaSmooth, IntervalPartition
  |
  |- sorry #3: mainTerm_first_moment_ibp (line 3434)
  |   Statement: |integral_1^T MainTerm| <= C * T^{1/2}
  |
  |- sorry #4: block_sum_sqrt_bound (line 4547)
  |- sorry #5: errorTerm_first_moment_sqrt interior (line 4594)

HardyZFirstMomentIBP.lean
  |- imports: RSExpansionProof.lean (+ 12 others)
  |- uses from RSExpansionProof:
  |   (a) hardyStart_pos' (line 1939) -- ALSO defined locally at line 2510
  |   (b) hardyZ_first_moment_sqrt_bound (line 2095) -- THE sorry-dependent result
  |
  |- Contains IBP infrastructure (Parts 1-5d, 6-9) that is sorry-free
  |- Parts 1-5d DO NOT depend on RSExpansionProof
  |- Part 8 (errorTerm analysis) depends on RSExpansionProof.hardyStart_pos'
  |   (but also has its own copy)
```

## 2. Why Extracting IBP Infrastructure Does NOT Close Sorry #3

**Critical finding**: Sorry #3 (`mainTerm_first_moment_ibp`) claims:

```
|integral_1^T MainTerm(t) dt| <= C_M * T^{1/2}
```

The HardyZFirstMomentIBP file EXPLICITLY documents (lines 944-962) that this
bound is NOT achievable by the IBP/VdC infrastructure in that file:

- **Per-mode VdC gives O(n+1) per mode** (not O(sqrt(n+1))), confirmed in Part 9c
- **Weighted sum**: sum_{n<N} (n+1)^{-1/2} * O(n+1) = O(N^{3/2}) = O(T^{3/4})
- **The O(T^{3/4}) bound is tight for per-mode analysis of MainTerm**

Therefore, extracting the IBP infrastructure into a standalone file and importing
it into RSExpansionProof WOULD break the import cycle, but WOULD NOT close sorry #3.
The sorry cannot be closed by the existing infrastructure.

## 3. The Real Blocker: Flawed Decomposition Strategy

The current proof architecture for `siegel_first_moment` is:

```
|integral Z| = |integral MainTerm + integral ErrorTerm|
             <= |integral MainTerm| + |integral ErrorTerm|
             <= C_M * sqrt(T) + C_E * sqrt(T)    [by sorry #3 + sorry #4/5]
```

This requires BOTH integrals to be O(sqrt(T)) independently. But:

- **integral MainTerm = O(T^{3/4})** by best available per-mode VdC (NOT O(sqrt(T)))
- **integral ErrorTerm = O(sqrt(T))** by alternating block cancellation (separate sorrys)
- **integral Z = O(sqrt(T))** by Titchmarsh's global argument

The bound |integral MainTerm| = O(sqrt(T)) IS TRUE, but only as a CONSEQUENCE of:
  |integral MainTerm| = |integral Z - integral ErrorTerm| <= O(sqrt(T)) + O(sqrt(T))
This is CIRCULAR: it requires |integral Z| = O(sqrt(T)), which is what we're proving.

## 4. Correct Fix: Two Options

### Option A: Prove integral(Z) = O(sqrt(T)) directly (RECOMMENDED)

Replace `siegel_first_moment` with a direct proof of |integral Z| <= C*sqrt(T)
that does NOT decompose into MainTerm + ErrorTerm. The Titchmarsh 4.15 argument:

1. Write Z(t) = Re(e^{i*theta(t)} * zeta(1/2+it))
2. IBP on integral e^{i*theta} * zeta(1/2+it) dt with:
   - u = zeta(1/2+it) / (i*theta'(t))
   - dv = i*theta'(t) * e^{i*theta(t)} dt = d(e^{i*theta(t)})
3. Boundary terms: |zeta(1/2+iT)|/theta'(T) = O(T^{1/6}/log(T)) = O(sqrt(T))
4. Correction integral: integral |d/dt[zeta/(i*theta')]| dt = O(T^{7/4}/log T)
   **THIS IS TOO LARGE** (the file itself notes this at line 945)

So even the global IBP on Z fails with the convexity bound. The O(sqrt(T))
result actually requires the AFE + per-mode analysis as Titchmarsh does it:

1. Apply AFE: zeta(1/2+it) = sum_{n<=N} n^{-1/2-it} + chi * sum + O(t^{-1/4})
2. Each mode integral_{T0}^{T} n^{-1/2} * e^{i(theta(t) - t*log(n+1))} dt:
   - For n where |theta'(t) - log(n+1)| >= delta (off-resonance): O(1/delta)
   - Resonance at t* = 2*pi*(n+1)^2 contributes O(1) by stationary phase
3. Sum over modes: O(N^{1/2}) = O(T^{1/4}) for off-resonance
4. Resonance sum: O(N) but only O(1) resonant mode per block

**Status of sub-lemmas in HardyZFirstMomentIBP**:
- theta derivative bounds: PROVED (Parts 1-3)
- Per-mode phase derivatives and off-resonance criterion: PROVED (Part 6)
- Per-mode VdC bound (O(n+1), too weak): PROVED (Part 9b-c)
- Assembly into O(sqrt(T)): NOT PROVED, and cannot be from per-mode VdC

The missing ingredient: the per-mode VdC analysis gives O(n+1) per mode
because it starts integrating from the stationary point t* = hardyStart(n).
To get O(1) per resonant mode, you need to use Titchmarsh's trick of
integrating starting from a fixed T0 and using the full phase monotonicity.

### Option B: Weaken mainTerm_first_moment_ibp to O(T^{3/4})

Replace the sorry with the provable bound:
```
mainTerm_first_moment_ibp : exists C > 0, forall T >= 2,
  |integral MainTerm| <= C * T^{3/4}
```

Then `siegel_first_moment` would give |integral Z| <= C_M*T^{3/4} + C_E*T^{1/2}
= O(T^{3/4}). This is weaker than O(sqrt(T)) but might still suffice for downstream
uses if they only need O(T^{1-delta}) for some delta.

**Assessment**: This would break the proof of `hardyZ_first_moment_sqrt_bound`
which promises O(sqrt(T)). All downstream consumers assume O(sqrt(T)). NOT VIABLE.

### Option C: Reprove via Titchmarsh Mode-Summation in a Standalone File

Create `HardyZFirstMomentStandalone.lean` that:
1. Does NOT import RSExpansionProof
2. Imports: HardyZFirstMoment, ThetaDeriv*, HardyThetaSmooth, PhragmenLindelof,
   OffResonanceSmoothVdC, HardyEstimatesPartial, AbelSummation
3. Proves |integral Z| <= C*sqrt(T) using Titchmarsh's mode-summation argument:
   - Decompose Z via AFE (MainTerm + ErrorTerm)
   - For MainTerm: sum of per-mode integrals
   - Key insight: integrate each mode from FIXED T0, not from stationary point
   - Off-resonance modes: O(1/log(T0)) each, sum O(N^{1/2}/log(T0))
   - Near-resonance: partition of unity on stationary blocks, O(1) total contribution
   - ErrorTerm: use pointwise bound |ErrorTerm| <= C*t^{-1/4} from ConvexityBounds
   - Integral: O(T^{3/4}) for ErrorTerm (acceptable when combined)

Actually this also doesn't close the gap. The ErrorTerm integral O(T^{3/4})
and MainTerm integral O(T^{3/4}) give O(T^{3/4}) total, not O(T^{1/2}).

## 5. CONCLUSION

**Sorry #3 (`mainTerm_first_moment_ibp`) is NOT closable by import cycle breaking.**

The import cycle is a RED HERRING. The actual blocker is mathematical:

1. |integral MainTerm| = O(T^{3/4}) by per-mode VdC -- this is the best achievable
   from per-mode analysis. The O(sqrt(T)) bound requires CROSS-MODE CANCELLATION
   or the full Siegel expansion machinery.

2. The decomposition Z = MainTerm + ErrorTerm is the wrong way to prove
   |integral Z| = O(sqrt(T)). The right proof works on Z directly.

3. The IBP infrastructure in HardyZFirstMomentIBP proves sub-lemmas that are
   necessary but NOT sufficient for O(sqrt(T)).

**Recommended next steps:**

1. **Do NOT create HardyZFirstMomentStandalone.lean** -- it would not close any sorry.

2. **Restructure siegel_first_moment** (in RSExpansionProof) to prove |integral Z| = O(sqrt(T))
   directly, without decomposing into MainTerm + ErrorTerm. This eliminates sorry #3 entirely.
   The direct proof should use:
   - The alternating block structure of Z(t) on Siegel blocks
   - The signed integral bound: (-1)^k * integral_{block k} Z >= 0
   - The monotone decay of signed block integrals
   - Telescoping sum gives O(last block integral) = O(block length / sqrt(t)) = O(1)

3. **Alternatively**: merge the two sorrys (#3 and #4/#5) into a single sorry for
   |integral Z| = O(sqrt(T)), which is the actual target. The MainTerm/ErrorTerm
   split was an incorrect intermediate decomposition.

4. **The import cycle CAN be broken** (for cleanliness) by having HardyZFirstMomentIBP
   use its own `hardyStart_pos'` (already defined at line 2510) and removing the
   import of RSExpansionProof. But this also means removing `ibp_oscillatory_bound`
   (line 2092-2095) which is the only consumer of `hardyZ_first_moment_sqrt_bound`.
   The file could make it a hypothesis instead.

## 6. Import Cycle Quick Fix (Does NOT Close Sorrys)

If we want to break the import cycle for structural cleanliness:

**File: HardyZFirstMomentIBP.lean**
- Line 46: REMOVE `import Littlewood.Aristotle.Standalone.RSExpansionProof`
- Line 1939: CHANGE `Aristotle.Standalone.RSExpansionProof.hardyStart_pos' k`
  TO `HardyZFirstMomentIBP.hardyStart_pos' k` (local copy at line 2510)
- Lines 2092-2095: CHANGE `ibp_oscillatory_bound` to take the Z first moment
  bound as a hypothesis parameter instead of importing it

This makes HardyZFirstMomentIBP independent of RSExpansionProof. No sorrys closed.

## 7. Detailed Mode Sum Analysis

The `AbelSummationPsiPi.lean` file (pure Mathlib, no Littlewood imports) has:
- `vdc_mode_sum_with_afe`: If each mode n has bound (n+1)^{-1/2} / log(n+2),
  then total sum <= (1/log 2) * T^{1/2}

This is the right FRAMEWORK. The missing link:

**Needed**: For each mode n, prove |integral_{hs(n)}^T cos(theta(t) - t*log(n+1)) dt| <= C/log(n+2).

**Available**: Per-block VdC gives O(1/log((k+1)/(n+1))) on block k for k > n.

**Blocker**: Summing the per-block bounds over blocks gives O((n+1)*log(n+1)) per mode
(dominated by near-resonance blocks k ~ n+1 where log((k+1)/(n+1)) ~ 1/(n+1)).
This does NOT give O(1/log(n+2)).

The per-mode bound O(1/log(n+2)) requires cancellation WITHIN the near-resonance blocks,
which is the genuine content of the Titchmarsh 4.15 proof. This cancellation uses the
fact that the phase has a stationary inflection at t* = hs(n), so Airy-function-type
estimates apply (not just VdC). This is mathematically equivalent to the saddle-point
analysis in the Siegel expansion.

## 8. File Inventory

| File | Lines | Sorrys | Role |
|------|-------|--------|------|
| RSExpansionProof.lean | ~5700 | 5 active | RS expansion, block structure |
| HardyZFirstMomentIBP.lean | 2579 | 0 | IBP/VdC infrastructure |
| HardyZFirstMoment.lean | ~120 | 0 | MainTerm/ErrorTerm definitions |
| AbelSummationPsiPi.lean | ~1050 | 0 | Mode sum bounds (pure Mathlib) |
| OffResonanceSmoothVdC.lean | ~300 | 0 | Per-block VdC |

## 9. Actionable Recommendation for the User

**Do not create HardyZFirstMomentStandalone.lean.** The import cycle is a symptom, not the disease.

The real fix has two parts:

**Part 1 (Structural, doable now)**: Merge sorry #3 (mainTerm_first_moment_ibp) and sorry #4/5
(errorTerm_first_moment_sqrt) into a SINGLE sorry for |integral Z| = O(sqrt(T)). This removes
the artificial MainTerm/ErrorTerm split. In RSExpansionProof.lean, change `siegel_first_moment`
to directly sorry |integral Z| = O(sqrt(T)), then mark it as a single irreducible sorry.
This REDUCES the sorry count by 1-2 and makes the remaining sorry mathematically cleaner.

**Part 2 (Mathematical, hard)**: Prove |integral Z| = O(sqrt(T)) by one of:
- Titchmarsh 4.15 mode-summation (requires per-mode Airy-type estimates near resonance)
- Direct signed block analysis (requires showing Z has approximate definite sign on blocks)
- Or accept as irreducible (it is genuinely hard number theory)

**Optional cleanup (Part 3)**: Break the import cycle by removing RSExpansionProof import from
HardyZFirstMomentIBP. Replace `ibp_oscillatory_bound` with a hypothesis parameter.
Change `hardyStart_pos'` reference to the local copy. This is purely structural.

## 10. What Agent 4 Did NOT Do (and Why)

- Did NOT create HardyZFirstMomentStandalone.lean: The file would not close any sorry.
  The IBP infrastructure in HardyZFirstMomentIBP is insufficient for O(sqrt(T)) on MainTerm.
  Creating the file would add complexity without reducing the sorry count.

- Did NOT edit RSExpansionProof.lean: Agent 1's file, and the structural changes needed
  (merging sorrys) require coordinated edits.

- Did NOT edit HardyZFirstMomentIBP.lean: The import cycle break is trivial (3 line changes)
  but would break the existing `ibp_oscillatory_bound` which downstream code uses.
  Safer to coordinate with Agent 1.
