# Aristotle Output Gate Usage

Use this gate before integrating Aristotle-returned Lean files into the repo.

## Script

`./scripts/aristotle_output_gate.sh <lean_file> [required_regex ...]`

Checks:
1. no forbidden constructs (`axiom`, `postulate`, `sorry`, `admit`)
2. `lake env lean` compile pass
3. optional required regex patterns

## Recommended checks for current 4 prompt lanes

### 1) RH-pi root payload

```bash
./scripts/aristotle_output_gate.sh /path/to/aristotle_root1.lean \
  "class RHPiUnconditionalExactSeedRootPayload" \
  "theorem rootPayload_of_concrete_triple" \
  "instance \(priority := 900\)"
```

### 2) ExplicitFormulaPsiHyp + general lift

```bash
./scripts/aristotle_output_gate.sh /path/to/aristotle_root2.lean \
  "class ExplicitFormulaPsiHyp" \
  "theorem general_formula_of_legacy_explicit_formula_term" \
  "theorem explicitFormulaPsiGeneralHyp_of_legacy_payload"
```

### 3) B2 support constructor pack

```bash
./scripts/aristotle_output_gate.sh /path/to/aristotle_root3.lean \
  "class B2SupportPhaseRootPayload" \
  "theorem provide_noncircular_constructor_B2SupportPhaseRootPayload" \
  "#synth B2SupportPhaseRootPayload"
```

### 4) Zeta mean-square half-bound constructor

```bash
./scripts/aristotle_output_gate.sh /path/to/aristotle_root4.lean \
  "class ZetaMeanSquareHalfBound" \
  "theorem zetaMeanSquareHalfBound_of_explicit" \
  "#synth ZetaMeanSquareHalfBound"
```

## Notes

- The gate expects a pure Lean file, not markdown.
- Keep Aristotle output as raw `.lean` and run this first.
