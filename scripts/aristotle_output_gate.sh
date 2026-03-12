#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 <lean_file> [required_regex ...]" >&2
  exit 2
fi

LEAN_FILE="$1"
shift || true

if [[ ! -f "$LEAN_FILE" ]]; then
  echo "[gate] missing file: $LEAN_FILE" >&2
  exit 2
fi

# Forbidden constructs for critical-path integration.
forbidden_regex='(^|[^A-Za-z0-9_])(axiom|postulate|sorry|admit)([^A-Za-z0-9_]|$)'

if rg -n --pcre2 "$forbidden_regex" "$LEAN_FILE" >/tmp/aristotle_gate_forbidden.txt; then
  echo "[gate] failed: forbidden constructs found"
  cat /tmp/aristotle_gate_forbidden.txt
  exit 1
fi

echo "[gate] forbidden-token check: pass"

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

echo "[gate] compiling via lake env lean ..."
if ! (cd "$REPO_ROOT" && lake env lean "$LEAN_FILE"); then
  echo "[gate] failed: lean compilation error"
  exit 1
fi

echo "[gate] lean compile check: pass"

if [[ $# -gt 0 ]]; then
  for pattern in "$@"; do
    if ! rg -n --pcre2 "$pattern" "$LEAN_FILE" >/dev/null; then
      echo "[gate] failed: required pattern missing: $pattern"
      exit 1
    fi
    echo "[gate] required pattern present: $pattern"
  done
fi

echo "[gate] PASS: $LEAN_FILE"
