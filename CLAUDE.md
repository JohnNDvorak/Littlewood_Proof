# Littlewood Proof — Claude Code Project Instructions

## AXLE Fast Verification

When working on Lean proofs, use AXLE for fast iteration before running `lake build`:

### Quick Check (Mathlib-only snippets)
For self-contained lemmas that only need Mathlib:
```bash
echo '<lean code>' | python3 ~/.claude/skills/axle-lean/axle_runner.py check -
```
This returns in <1s vs minutes for `lake build`. Use this in a tight loop when iterating on tactics.

### Sorry Leaf Workflow
When closing a sorry:
1. **Extract**: Run `/lean-snippet <file> --names <theorem>` to get a self-contained `import Mathlib` version, or manually extract the goal with relevant definitions
2. **Iterate**: Edit the snippet → `axle_runner.py check -` via stdin → read errors → fix → repeat (~0.3s per cycle)
3. **Reintegrate**: Paste the working proof body back into the project file
4. **Validate**: Run `lake build` for final cross-file validation

### Sanity Checks
- Before proving: `/lean-disprove <file>` to check the statement isn't false
- After proving: `/lean-simplify <file>` to clean up redundant tactics
- For delegation: `/lean-sorry <file>` to extract obligation signatures

### When NOT to Use AXLE
- Any theorem referencing `hardyStart`, `hardyTheta`, `hardyZ`, `blockParam`,
  `rsPsi`, `afeGapIntegrand`, or other Littlewood-defined symbols
- Cross-file dependency validation
- Final pre-commit check (always use `lake build`)

### Limitations
- AXLE has Mathlib but NOT Littlewood project imports
- Files with `import Littlewood.*` are auto-checked with `ignore_imports` — cross-file errors won't be caught
- None of the 13 critical sorry's can be directly AXLE-checked; AXLE helps on **sub-lemmas** within sorry proofs
- Always run `lake build` before committing

## Build Commands

- Full build: `lake build` (from repo root)
- Count sorry warnings: `lake build 2>&1 | grep -c "declaration uses 'sorry'"`
- Current baseline: 13 sorry warnings (see MEMORY.md for locations)

## Architecture

Three independent proof chains:
- **Hardy chain**: Hardy's theorem ← B1 (AFE) + B2 (VdC) + B3 (Riemann-Siegel)
- **ψ chain**: Explicit formula ← B5a (shifted bound) + B5b (Landau oscillation)
- **π chain**: Fully sorry-free (PiPringsheimExtension + B7a/B7b)

Main theorems: `littlewood_psi` and `littlewood_pi_li`
