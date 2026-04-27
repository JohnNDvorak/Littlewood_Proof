#!/usr/bin/env bash
set -euo pipefail

ROOT="/Users/john.n.dvorak/Projects/Littlewood_Proof/Littlewood/Documentation/Recovery/2026-04-21/self_drive"

echo "Runner process:"
if pgrep -fl "$ROOT/tools/run_overnight.sh" >/dev/null 2>&1; then
  pgrep -fl "$ROOT/tools/run_overnight.sh"
else
  echo "(no live overnight runner)"
fi

echo

echo "Latest:"
if [[ -f "$ROOT/latest.md" ]]; then
  cat "$ROOT/latest.md"
else
  echo "(missing latest.md)"
fi

echo
echo "Runtime state:"
if [[ -f "$ROOT/runtime_state.json" ]]; then
  cat "$ROOT/runtime_state.json"
else
  echo "(missing runtime_state.json)"
fi

echo
echo "Handoff:"
if [[ -f "$ROOT/handoff_latest.md" ]]; then
  sed -n '1,120p' "$ROOT/handoff_latest.md"
else
  echo "(missing handoff_latest.md)"
fi

echo
echo "Latest metric:"
if [[ -s "$ROOT/metrics/round_metrics.jsonl" ]]; then
  tail -n 1 "$ROOT/metrics/round_metrics.jsonl"
else
  echo "(no round metrics yet)"
fi

echo
echo "Recent routes:"
if [[ -s "$ROOT/metrics/route_ledger.jsonl" ]]; then
  tail -n 5 "$ROOT/metrics/route_ledger.jsonl"
else
  echo "(no routes yet)"
fi

echo
echo "Live lineage:"
if [[ -s "$ROOT/metrics/target_lineage.jsonl" ]]; then
  tail -n 5 "$ROOT/metrics/target_lineage.jsonl"
else
  echo "(no target lineage yet)"
fi

echo
echo "Recent Aristotle jobs:"
if [[ -s "$ROOT/aristotle/jobs.jsonl" ]]; then
  tail -n 10 "$ROOT/aristotle/jobs.jsonl"
else
  echo "(no Aristotle jobs yet)"
fi

echo
echo "Recent logs:"
if compgen -G "$ROOT/logs/*.log" > /dev/null; then
  ls -1t "$ROOT"/logs/*.log | head -n 5
else
  echo "(no logs yet)"
fi
