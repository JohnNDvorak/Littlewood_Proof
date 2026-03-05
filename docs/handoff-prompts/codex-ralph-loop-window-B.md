# Codex Ralph Loop — Window B (Aristotle Integration + Verification)

## Objective
Integrate Aristotle outputs for the remaining analytic atoms and keep the critical path green at each merge.

Target theorem sites:
1. `Littlewood/Aristotle/Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean:208` (`B1`)
2. `Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean:130` (`B3`)
3. `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiSkeleton.lean:65` (`B5a`)

## Hard constraints
- No new `axiom`, `postulate`, `sorry`, `admit`.
- Paste only theorem-body replacements from Aristotle.
- Preserve theorem signatures and public names exactly.

## Integration loop
1. Wait for one Aristotle result.
2. Apply only the theorem-body patch.
3. Immediately run module build for the touched file.
4. Run critical assembly build.
5. Run active-chain sorry/axiom check.
6. If failure, isolate type mismatch and request a corrected Aristotle patch with exact local error text.

## Commands
```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof

# file-level rebuilds
lake build Littlewood.Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment
lake build Littlewood.Aristotle.Standalone.RSCompleteBlockAsymptotic
lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiSkeleton

# critical-path assembly
lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved
lake build Littlewood.Aristotle.DeepSorries

# active-path sorry scan
rg -n "^[[:space:]]*sorry$" \
  Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean \
  Littlewood/Aristotle/Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean \
  Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean \
  Littlewood/Aristotle/Standalone/ExplicitFormulaPsiSkeleton.lean

# active-path axiom scan
rg -n "\\baxiom\\b|\\bpostulate\\b" \
  Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean \
  Littlewood/Aristotle/Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean \
  Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean \
  Littlewood/Aristotle/Standalone/ExplicitFormulaPsiSkeleton.lean \
  Littlewood/Aristotle/DeepSorries.lean
```

## Reporting format per iteration
1. theorem integrated
2. build status (file + assembly)
3. remaining critical-path sorry count
4. remaining critical-path axiom count
5. next blocker

