#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

WORKDIR="${WORKDIR:-/tmp/lean-hunt}"
OUT_DIR="$ROOT/docs/integration"
OUT_FILE="${OUT_FILE:-$OUT_DIR/external_dependency_probe_$(date +%F).tsv}"

mkdir -p "$OUT_DIR"

probe_import() {
  local mod="$1"
  local sym="$2"
  local tmp
  tmp="$(mktemp /tmp/external_dep_probe.XXXXXX.lean)"
  {
    echo "import $mod"
    if [ -n "$sym" ]; then
      echo "#check $sym"
    fi
  } > "$tmp"

  if lake env lean "$tmp" >/tmp/external_dep_probe.out 2>/tmp/external_dep_probe.err; then
    rm -f "$tmp"
    echo "pass"
  else
    rm -f "$tmp"
    echo "fail"
  fi
}

clone_meta() {
  local repo="$1"
  local dir="$WORKDIR/$repo"
  local present="no"
  local commit="missing"
  local toolchain="missing"
  if [ -d "$dir" ]; then
    present="yes"
    if [ -d "$dir/.git" ]; then
      commit="$(git -C "$dir" rev-parse --short HEAD 2>/dev/null || echo unknown)"
    fi
    if [ -f "$dir/lean-toolchain" ]; then
      toolchain="$(tr -d '\r' < "$dir/lean-toolchain" | head -n 1)"
    else
      toolchain="(none)"
    fi
  fi
  echo "$present"$'\t'"$commit"$'\t'"$toolchain"
}

# Dependency import probes (expected to fail unless wired in lakefile).
probe_prime="$(probe_import "PrimeNumberTheoremAnd.MediumPNT" "SmoothedChebyshevClose")"
probe_strong="$(probe_import "StrongPNT.PNT5_Strong" "Strong_PNT")"
probe_dirichlet="$(probe_import "Project.EulerProducts.PNT" "WienerIkeharaTheorem")"

# Local adapter readiness probes.
adapter_b5a="fail"
adapter_rhpi="fail"
adapter_readiness="fail"
if lake build Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider >/tmp/external_dep_b5a.out 2>/tmp/external_dep_b5a.err; then
  adapter_b5a="pass"
fi
if lake build Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider >/tmp/external_dep_rhpi.out 2>/tmp/external_dep_rhpi.err; then
  adapter_rhpi="pass"
fi
if lake build Littlewood.Aristotle.Standalone.ExternalPort.ExternalConstructorReadiness >/tmp/external_dep_ready.out 2>/tmp/external_dep_ready.err; then
  adapter_readiness="pass"
fi

{
  printf "repo\tclone_present\tclone_commit\tclone_toolchain\timport_probe\trecommended_mode\tnotes\n"

  IFS=$'\t' read -r p c t < <(clone_meta "PrimeNumberTheoremAnd")
  mode="vendor_adapter"
  [ "$probe_prime" = "pass" ] && mode="direct_dependency"
  printf "PrimeNumberTheoremAnd\t%s\t%s\t%s\t%s\t%s\t%s\n" "$p" "$c" "$t" "$probe_prime" "$mode" "target: MediumPNT.SmoothedChebyshevClose"

  IFS=$'\t' read -r p c t < <(clone_meta "strongpnt")
  mode="vendor_adapter"
  [ "$probe_strong" = "pass" ] && mode="direct_dependency"
  printf "strongpnt\t%s\t%s\t%s\t%s\t%s\t%s\n" "$p" "$c" "$t" "$probe_strong" "$mode" "target: PNT5_Strong.Strong_PNT"

  IFS=$'\t' read -r p c t < <(clone_meta "DirichletNonvanishing")
  mode="vendor_adapter"
  [ "$probe_dirichlet" = "pass" ] && mode="direct_dependency"
  printf "DirichletNonvanishing\t%s\t%s\t%s\t%s\t%s\t%s\n" "$p" "$c" "$t" "$probe_dirichlet" "$mode" "target: Project.EulerProducts.PNT.WienerIkeharaTheorem"

  printf "local_external_adapters\t%s\t%s\t%s\t%s\t%s\t%s\n" "yes" "workspace" "$(tr -d '\r' < lean-toolchain | head -n 1)" "${adapter_b5a},${adapter_rhpi},${adapter_readiness}" "vendor_adapter" "builds: B5a provider, RH-pi provider, readiness"
} > "$OUT_FILE"

echo "wrote $OUT_FILE"
echo "PrimeNumberTheoremAnd import probe: $probe_prime"
echo "strongpnt import probe: $probe_strong"
echo "DirichletNonvanishing import probe: $probe_dirichlet"
echo "Adapter builds: b5a=$adapter_b5a rhpi=$adapter_rhpi readiness=$adapter_readiness"
