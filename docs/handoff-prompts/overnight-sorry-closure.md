# Overnight Sorry Closure — Handoff Document

## Context

You are continuing the AXLE-integrated sorry closure plan for the Littlewood Proof formalization. The repo is at `/Users/john.n.dvorak/Documents/Git/Littlewood_Proof/`. Read `CLAUDE.md` and `~/.claude/projects/-Users-john-n-dvorak/memory/MEMORY.md` for full project context.

**Current state**: 0 build errors, 13 sorry warnings, 8205 jobs. `lake build` passes clean.

**User is away for the night. You have FULL AUTONOMOUS permission** per MEMORY.md. No approval needed for bash commands, file edits, builds, or commits. Execute everything autonomously.

## What Was Just Completed

1. **VanDerCorputGeneric.lean** — `vdc_first_deriv_sin` and `vdc_first_deriv_cos` PROVED (pure Mathlib VdC first-derivative test). One remaining sorry (`vdc_first_deriv_exp`) is not on critical path.

2. **Exploration completed** on all 13 sorry targets. Key findings:
   - B1, B5a, B2 top-level sorry's are all very high difficulty (need independent hard theorems)
   - B3 `theta_stirling_expansion` is BLOCKED by phase-lift issue (`arg` vs unwound `Im log` — see `StirlingArgGamma.lean:135-150` which proves the arg-based formulation is FALSE)
   - `off_resonance_integral_bound` needs `theta_stirling` resolved first
   - THE WALL (`errorTerm_expansion`) is extremely hard
   - π exact seeds need root payload constructor

## Critical Discovery: Two Definitions of hardyTheta

There are TWO different definitions:
- **HardyInfrastructure.lean:42** uses `Complex.arg` (bounded, wraps)
- **HardyEstimatesPartial.lean:45** uses `Complex.log(...).im` (unwound, grows)

`ErrorTermExpansion.lean` opens `HardyEstimatesPartial` so uses the `.im` version. The `.im` version is the correct one for Stirling asymptotics. `StirlingArgGamma.lean:135-150` proves the `arg`-based version is FALSE — but that may not block us since ErrorTermExpansion uses the `.im` version.

**ACTION ITEM**: Verify which `hardyTheta` ErrorTermExpansion.lean actually resolves to. If it's the `.im` version, `theta_stirling_expansion` may be unblocked.

## Available Infrastructure (All Proved, 0 Sorry)

| File | Key Result | Use For |
|------|-----------|---------|
| VanDerCorputGeneric.lean | `vdc_first_deriv_sin/cos` | B2, off_resonance |
| VdcFirstDerivTest.lean | `vdc_cos_bound` | off_resonance_integral_bound |
| BinetStirling.lean | `stirling_approx_im_asymptotic` | theta_stirling |
| ThetaDerivAsymptotic.lean | `theta_deriv_asymptotic` | off_resonance phase bounds |
| ThetaDerivMonotone.lean | `thetaDeriv_strictMonoOn` | monotonicity of phase deriv |
| DigammaBinetBound.lean | `digamma_log_bound_atomic` | Stirling infrastructure |
| GammaSeqLocallyUniform.lean | Gauss identity | Gamma function infrastructure |

## Attack Plan (Priority Order)

### Priority 1: Investigate theta_stirling_expansion unblock

Check which `hardyTheta` definition ErrorTermExpansion.lean uses:
```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
grep -n "hardyTheta" Littlewood/Aristotle/ErrorTermExpansion.lean | head -20
```
Then check what `open HardyEstimatesPartial` brings in scope.

If the `.im` version is used, the path is:
1. `stirling_approx_im_asymptotic` (PROVED in BinetStirling.lean) gives `Im(stirlingApprox) ≈ (t/2)log(t/2) - t/2 - π/8 + O(1/t)`
2. Need: `Im(log Γ(s)) ≈ Im(stirlingApprox(t))` for s = 1/4 + it/2
3. The Binet integral representation bridges this gap
4. Then: `hardyTheta t = Im(log Γ(s)) - (t/2)log π ≈ (t/2)log(t/(2π)) - t/2 - π/8 + O(1/t)`

### Priority 2: off_resonance_integral_bound (if theta_stirling closes)

Uses VdC (`vdc_cos_bound` from VdcFirstDerivTest.lean) + `phase_deriv_off_resonance` (PROVED). Needs:
- `hardyTheta` differentiable on blocks (composition of analytic functions)
- `deriv hardyTheta` close to `(1/2) log(t/(2π))` — from `theta_deriv_asymptotic` (PROVED)
- Phase derivative monotone — from `thetaDeriv_strictMonoOn` (PROVED)
- Lower bound on |phase deriv| — from `phase_deriv_off_resonance` (PROVED)

### Priority 3: off_resonance_sum_bound (if #2 closes)

Weighted sum `∑_{n<k} (n+1)^{-1/2} · (integral bound)` ≤ C·√(k+1). This is:
- Sum of `(n+1)^{-1/2} · 6/log((k+1)/(n+1))` over n < k
- Dyadic splitting: near n ≈ k terms dominate, use `log((k+1)/(n+1)) ≥ (k-n)/(k+1)`
- Standard harmonic-type estimate

### Priority 4: vdc_first_deriv_exp (quick win)

Complete the exp version in VanDerCorputGeneric.lean. Needs both monotone-increasing and monotone-decreasing cases. Use `Complex.norm_exp_ofReal_mul_I_le` or decompose into sin/cos.

### Priority 5: RSBlockBounds triple (if theta_stirling + off_resonance close)

`c_block_nonneg`, `c_block_antitone`, `block_interpolation` at RSBlockBounds.lean:114,119,138. These need `errorTerm_expansion` (THE WALL) which likely won't close tonight, but check the dependency.

### Lower Priority: B1, B5a, B2, π seeds

These each require independent hard mathematical content (second moment of zeta, Perron formula, Heath-Brown VdC, root payload constructor). Unlikely to close in one night but attempt if earlier priorities are exhausted.

## AXLE Workflow (for Mathlib-only sub-lemmas)

```bash
# Quick check (~0.3s)
echo '<lean code with import Mathlib>' | python3 ~/.claude/skills/axle-lean/axle_runner.py check -

# Extract self-contained snippet
# Use /lean-snippet <file> --names <theorem>
```

AXLE has Mathlib but NOT Littlewood imports. Use for sub-lemmas only. Always validate with `lake build` before committing.

## Validation Protocol

After each sorry closure:
```bash
lake build 2>&1 | grep -c "declaration uses 'sorry'"  # Should decrease
lake build  # Must be 0 errors
```

Commit with descriptive message noting which sorry was closed. Include `Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>`.

## Key Lean/Mathlib Patterns

See MEMORY.md `lean-lessons.md` for comprehensive list. Most relevant tonight:
- `abs_add_le` (NOT `abs_add`) for triangle inequality
- `inv_anti₀ (hb : 0 < b) (hba : b ≤ a)` for inverse monotonicity
- `div_le_div_iff₀` has specific argument order
- `integral_Ioc_eq_integral_Ioo' Real.volume_singleton` for Ioc→Ioo
- `norm_integral_le_of_norm_le` argument order: `(hab : a ≤ b) (h_ae) (h_int)`
