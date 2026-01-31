# Aristotle Incoming Files

When Aristotle returns a proof:

1. Copy the output file here
2. Check it compiles: `lake build` on the file
3. Check for `sorry` count: `grep -c sorry filename.lean`
4. If 0 sorries, move to main Aristotle directory
5. Update Littlewood.lean imports
6. Wire to existing sorries if applicable
7. Update documentation

## Expected Returns

| Prompt | Target | Priority |
|--------|--------|----------|
| HARDY | Hardy's theorem | CRITICAL - Last blocker! |
| M1-M4 | MeanSquare.lean sorries | High |
| PL1-PL3 | PhragmenLindelof.lean sorries | High |
| PS1-PS2 | PartialSummation.lean sorries | High |
| Z1-Z3 | ZeroCounting.lean N(T) sorries | Medium |
| RVM | RiemannVonMangoldtV2.lean | Medium |
| PERRON | PerronContourIntegralsV2.lean | Low |

## Integration Checklist

For each incoming file:

- [ ] File compiles with `lake build Littlewood.Aristotle.NewFile`
- [ ] Sorry count: `grep -c sorry NewFile.lean`
- [ ] No namespace conflicts with existing files
- [ ] No definition conflicts (check DefinitionXRef.md)
- [ ] Added to Littlewood.lean imports
- [ ] Sorries wired where applicable
- [ ] SorryDashboard.md updated
- [ ] BlockerStatus.md updated if relevant

## Hardy Integration (When It Arrives)

Hardy's theorem is the LAST BLOCKER. When it arrives:

1. Verify it proves: `Set.Infinite {t : ℝ | riemannZeta (1/2 + Complex.I * t) = 0}`
2. Check available building blocks:
   - HardyZRealV4.lean: hardyZV4_real
   - ZetaMeanSquare.lean: mean square estimates
   - StirlingGammaBounds.lean: Stirling bounds
3. After integration, the main theorem chain completes!

## Current Sorries Summary

| File | Sorries | Priority |
|------|---------|----------|
| MeanSquare.lean | 4 | High |
| ZeroCounting.lean | 4 (1 FALSE) | Medium |
| PhragmenLindelof.lean | 3 | High |
| PartialSummation.lean | 2 | High |
| RiemannVonMangoldtV2.lean | 1 | Medium |
| PerronContourIntegralsV2.lean | 1 | Low |
| **Total** | **15** | |
