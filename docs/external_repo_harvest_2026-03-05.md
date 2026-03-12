# External Lean Repo Harvest (March 5, 2026)

## Scope

This report records a blocker-focused hunt for reusable Lean theorems outside mathlib, with priority on:

- B5a shifted explicit-formula remainder bounds
- B2/RS7 oscillatory and contour error infrastructure
- RH-pi support lemmas (nonvanishing/log-derivative control)

This is implemented with a reproducible scanner:

- [`scripts/external_repo_harvest_scan.sh`](/Users/john.n.dvorak/Documents/Git/Littlewood_Proof/scripts/external_repo_harvest_scan.sh)
- Output summary TSV: [`docs/review_graphs/external_repo_harvest_summary.tsv`](/Users/john.n.dvorak/Documents/Git/Littlewood_Proof/docs/review_graphs/external_repo_harvest_summary.tsv)
- Output key-hit log: [`docs/review_graphs/external_repo_harvest_keyhits.txt`](/Users/john.n.dvorak/Documents/Git/Littlewood_Proof/docs/review_graphs/external_repo_harvest_keyhits.txt)

## Quick Findings

1. Highest-value reuse targets are `PrimeNumberTheoremAnd`, `strongpnt`, and `DirichletNonvanishing`.
2. `PrimeNumberTheoremAnd` and `strongpnt` contain the closest analogues to B5a contour decomposition and smoothed explicit-formula bounds.
3. `DirichletNonvanishing` gives clean no-sorry/nonvanishing and Wiener-Ikehara infrastructure that can feed RH-pi support lanes.
4. `Riemann-adelic` is not suitable as a witness source (high axiom/sorry/admit volume).

## Candidate Snapshot

| Repo | Lean files | `axiom`/`postulate` lines | `sorry` lines | `admit` lines | Toolchain |
|---|---:|---:|---:|---:|---|
| PrimeNumberTheoremAnd | 69 | 2 | 180 | 0 | `leanprover/lean4:v4.28.0` |
| strongpnt | 8 | 0 | 0 | 0 | `leanprover/lean4:v4.21.0` |
| DirichletNonvanishing | 11 | 0 | 0 | 0 | `leanprover/lean4:v4.13.0-rc3` |
| PNT (jonwashburn) | 6 | 0 | 0 | 0 | `leanprover/lean4:v4.13.0` |
| RiemannHypothesisCurves | 10 | 0 | 0 | 0 | `leanprover/lean4:v4.26.0-rc2` |
| stirling | 1 | 0 | 1 | 0 | `(none)` |
| Lean-RH | 8 | 0 | 0 | 0 | `(none)` |
| lean-riemann-hypothesis | 8 | 0 | 0 | 0 | `(none)` |
| riemann-hypothesis-lean4-formal-proof | 11 | 0 | 0 | 0 | `leanprover/lean4:v4.29.0-rc2` |
| Riemann-adelic | 1094 | 4291 | 5416 | 132 | `(none)` |

## Exact Theorem Paths Worth Adapting

### 1) PrimeNumberTheoremAnd

Primary source repo:

- `https://github.com/AlexKontorovich/PrimeNumberTheoremAnd`

High-signal theorem/module paths:

- `PrimeNumberTheoremAnd/MediumPNT.lean:705` `SmoothedChebyshevClose`
- `PrimeNumberTheoremAnd/MediumPNT.lean:1131` `SmoothedChebyshevPull1`
- `PrimeNumberTheoremAnd/MediumPNT.lean:1379` `SmoothedChebyshevPull2`
- `PrimeNumberTheoremAnd/MediumPNT.lean:1582` `ZetaBoxEval`
- `PrimeNumberTheoremAnd/MediumPNT.lean:1825` `I1Bound`
- `PrimeNumberTheoremAnd/MediumPNT.lean:2207` `I2Bound`
- `PrimeNumberTheoremAnd/MediumPNT.lean:2705` `I3Bound`
- `PrimeNumberTheoremAnd/MediumPNT.lean:3024` `I4Bound`
- `PrimeNumberTheoremAnd/MediumPNT.lean:3440` `I5Bound`
- `PrimeNumberTheoremAnd/MediumPNT.lean:3590` `LogDerivZetaBoundedAndHolo`
- `PrimeNumberTheoremAnd/ZetaBounds.lean:630` `riemannZetaLogDerivResidue`
- `PrimeNumberTheoremAnd/ZetaBounds.lean:669` `riemannZetaLogDerivResidueBigO`
- `PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean` (rectangle/residue contour tooling)
- `PrimeNumberTheoremAnd/MellinCalculus.lean` (Mellin/integration-by-parts stack)
- `PrimeNumberTheoremAnd/ZetaAppendix.lean:399` `lemma_aachIBP`
- `PrimeNumberTheoremAnd/ZetaAppendix.lean:1224` `lemma_aachfour`
- `PrimeNumberTheoremAnd/ZetaAppendix.lean:1604` `lemma_aachcanc`
- `PrimeNumberTheoremAnd/ZetaAppendix.lean:1668` `proposition_applem`
- `PrimeNumberTheoremAnd/Wiener.lean:2394` `WienerIkeharaTheorem'`
- `PrimeNumberTheoremAnd/Wiener.lean:3891` `WienerIkeharaTheorem''`

Blocker fit:

- B5a: strongest analogues via `I1..I9` + contour-pull theorems
- B2/RS7: oscillatory cancellation and contour bounds via `ZetaAppendix`
- RH-pi support: local residue/log-derivative bounds via `ZetaBounds`

### 2) strongpnt

Primary source repo:

- `https://github.com/math-inc/strongpnt`

High-signal theorem/module paths:

- `StrongPNT/PNT5_Strong.lean:808` `SmoothedChebyshevClose`
- `StrongPNT/PNT5_Strong.lean:2048` `SmoothedChebyshevPull1`
- `StrongPNT/PNT5_Strong.lean:2601` `SmoothedChebyshevPull2`
- `StrongPNT/PNT5_Strong.lean:2800` `ZetaBoxEval`
- `StrongPNT/PNT5_Strong.lean:3504` `I1Bound`
- `StrongPNT/PNT5_Strong.lean:3950` `I2Bound`
- `StrongPNT/PNT5_Strong.lean:4503` `I3Bound`
- `StrongPNT/PNT5_Strong.lean:5199` `I4Bound`
- `StrongPNT/PNT5_Strong.lean:5628` `I5Bound`
- `StrongPNT/PNT5_Strong.lean:5588` `I6Bound`
- `StrongPNT/PNT5_Strong.lean:5145` `I7Bound`
- `StrongPNT/PNT5_Strong.lean:4169` `I8Bound`
- `StrongPNT/PNT5_Strong.lean:5810` `LogDerivZetaBoundedAndHolo`
- `StrongPNT/PNT5_Strong.lean:5911` `Strong_PNT`

Blocker fit:

- B5a/RS7: direct analogues of contour error-term infrastructure, all in no-sorry modules

### 3) DirichletNonvanishing

Primary source repo:

- `https://github.com/CBirkbeck/DirichletNonvanishing`

High-signal theorem/module paths:

- `Project/EulerProducts/PNT.lean:18` `WienerIkeharaTheorem`
- `Project/EulerProducts/PNT.lean:275` `riemannZeta_ne_zero_of_one_le_re`
- `Project/EulerProducts/PNT.lean:352` `neg_logDeriv_ζ₁_eq`
- `Project/EulerProducts/PNT.lean:358` `continuousOn_neg_logDeriv_ζ₁`
- `Project/EulerProducts/PNT.lean:377` `PNT_vonMangoldt`
- `Project/EasyCase.lean:118` `LFunction_one_residue_one`

Blocker fit:

- RH-pi support and zero-free/log-derivative continuity lanes

## Blocker-Oriented Adoption Order

1. Mine `PrimeNumberTheoremAnd` for B5a (contour pull + `I`-block bounds + zeta log-derivative residue control).
2. Cross-check same lane in `strongpnt` to extract cleaner no-sorry theorem pathways if equivalent.
3. Feed RH-pi support classes with `DirichletNonvanishing` nonvanishing/log-derivative lemmas.
4. Treat `Riemann-adelic` and RH-narrative repos as idea references only, not payload sources.

## Compatibility Notes

1. Littlewood toolchain is `leanprover/lean4:v4.27.0-rc1`.
2. Top candidates use mixed versions (`v4.13`, `v4.21`, `v4.28`, `v4.29-rc2`), so expect adapter/porting shims.
3. The in-repo import smoke test `Littlewood/Test/PNTAImportTest.lean` currently fails because `PrimeNumberTheoremAnd` is not wired in `lakefile.toml`.

## Reproduction

Run:

```bash
./scripts/external_repo_harvest_scan.sh
```

This refreshes:

- `docs/review_graphs/external_repo_harvest_summary.tsv`
- `docs/review_graphs/external_repo_harvest_keyhits.txt`

