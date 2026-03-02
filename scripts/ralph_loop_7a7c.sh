#!/usr/bin/env bash
set -euo pipefail

# Ralph Wiggum loop for RH-pi Blocker 7 (B7a/B7b).
# Multi-session orchestration with immediate fresh-session relaunch until:
#   - B7 leaves are closed (no sorry/admit at deep_blocker_B7a/B7b),
#   - class/endpoint gates pass,
#   - targeted builds pass,
# or hard-stop policy triggers.

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# Backward-compat aliases from older script versions.
if [[ -z "${MAX_SESSIONS+x}" && -n "${MAX_ITERS:-}" ]]; then
  MAX_SESSIONS="$MAX_ITERS"
fi
if [[ -z "${MAX_STALE_SESSIONS+x}" && -n "${MAX_STALE_ITERS:-}" ]]; then
  MAX_STALE_SESSIONS="$MAX_STALE_ITERS"
fi

MAX_SESSIONS="${MAX_SESSIONS:-20}"                     # total fresh sessions
MAX_STALE_SESSIONS="${MAX_STALE_SESSIONS:-3}"         # consecutive no-progress sessions
SESSION_TIMEOUT_SECS="${SESSION_TIMEOUT_SECS:-2700}"  # timeout for proof-construction command
MAX_WALLCLOCK_SECS="${MAX_WALLCLOCK_SECS:-43200}"     # absolute run timeout
SLEEP_SECS="${SLEEP_SECS:-1}"
RELAUNCH_ON_NON_CLOSURE="${RELAUNCH_ON_NON_CLOSURE:-1}"
AUTO_CONSTRUCT_CMD="${AUTO_CONSTRUCT_CMD:-}"
CONTINUATION_PROMPT_TEMPLATE="${CONTINUATION_PROMPT_TEMPLATE:-}"

RUN_ID="${RUN_ID:-$(date '+%Y%m%d_%H%M%S')}"
RUN_DIR="${LOG_DIR:-$ROOT/.lake/ralph_7a7c/$RUN_ID}"
mkdir -p "$RUN_DIR"

DEEP_BLOCKERS_FILE="Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean"
B7_CHAIN_FILES=(
  "Littlewood/Aristotle/Standalone/RHPiInhomogeneousApproxObstruction.lean"
  "Littlewood/Aristotle/Standalone/RHPiExactSeedToPerronThresholdArgApprox.lean"
  "Littlewood/Aristotle/Standalone/RHPiExactSeedObstructionBridge.lean"
  "Littlewood/Aristotle/Standalone/RHPiDeepCoeffControlWitnesses.lean"
  "Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean"
)

TARGETED_BUILD_TARGETS=(
  "Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox"
  "Littlewood.Aristotle.Standalone.RHPiInhomogeneousApproxObstruction"
  "Littlewood.Aristotle.Standalone.RHPiExactSeedObstructionBridge"
  "Littlewood.Aristotle.Standalone.DeepBlockersResolved"
)

TARGET_GATE_CHECK="Aristotle.Standalone.RHPiInhomogeneousApproxObstruction.no_uniform_relation_gap_piOverTwo_of_RhPiTargetHeightCoeffControlHyp"
ANTI_GATE_CHECK="Aristotle.Standalone.RHPiInhomogeneousApproxObstruction.no_uniform_relation_gap_piOverTwo_of_RhPiAntiTargetHeightCoeffControlHyp"
ENDPOINT="Aristotle.Standalone.RHPiWitnessFromExplicitFormula.rhPiWitness_proved"

start_epoch="$(date +%s)"
latest_report_path=""

best_b7_sorry_count=9999
best_gate_pass_count=-1
best_targeted_build_pass=0
stale_sessions=0

run_with_timeout() {
  local timeout_secs="$1"
  shift
  if command -v timeout >/dev/null 2>&1; then
    timeout "$timeout_secs" "$@"
  elif command -v gtimeout >/dev/null 2>&1; then
    gtimeout "$timeout_secs" "$@"
  elif command -v python3 >/dev/null 2>&1; then
    python3 -c '
import subprocess
import sys

timeout = float(sys.argv[1])
cmd = sys.argv[2:]

try:
    if timeout > 0:
        proc = subprocess.run(cmd, timeout=timeout)
    else:
        proc = subprocess.run(cmd)
    raise SystemExit(proc.returncode)
except subprocess.TimeoutExpired:
    raise SystemExit(124)
' "$timeout_secs" "$@"
  else
    "$@"
  fi
}

snapshot_b7_chain() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "${B7_CHAIN_FILES[@]}" 2>/dev/null || true
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "${B7_CHAIN_FILES[@]}" 2>/dev/null || true
  else
    git -C "$ROOT" diff --numstat -- "${B7_CHAIN_FILES[@]}" || true
  fi
}

check_b7_leaf_sorry_count() {
  local file="$1"
  awk '
    BEGIN { mode=""; a=0; b=0 }
    /^[[:space:]]*private theorem deep_blocker_B7a[[:space:]]*:/ { mode="a"; next }
    /^[[:space:]]*private theorem deep_blocker_B7b[[:space:]]*:/ { mode="b"; next }
    mode=="a" && /^[[:space:]]*private theorem deep_blocker_B7b[[:space:]]*:/ { mode="b"; next }
    mode=="a" && /^[[:space:]]*(private theorem|theorem|lemma|def|class|instance|abbrev|end)([[:space:]]|$)/ { mode="" }
    mode=="b" && /^[[:space:]]*(private theorem|theorem|lemma|def|class|instance|abbrev|end)([[:space:]]|$)/ { mode="" }
    mode=="a" && /^[[:space:]]*(sorry|admit)([[:space:]]|$)/ { a=1 }
    mode=="b" && /^[[:space:]]*(sorry|admit)([[:space:]]|$)/ { b=1 }
    END { printf "%d %d %d\n", a, b, a+b }
  ' "$file"
}

run_lean_gate() {
  local mode="$1"
  local lean_file="$2"
  local out_file="$3"

  cat > "$lean_file" <<'LEAN'
import Littlewood.Aristotle.Standalone.DeepBlockersResolved
import Littlewood.Aristotle.Standalone.RHPiWitnessFromExplicitFormula
import Littlewood.Aristotle.Standalone.RHPiInhomogeneousApproxObstruction
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
LEAN

  case "$mode" in
    target)
      cat >> "$lean_file" <<LEAN
#check $TARGET_GATE_CHECK
LEAN
      ;;
    anti)
      cat >> "$lean_file" <<LEAN
#check $ANTI_GATE_CHECK
LEAN
      ;;
    endpoint)
      cat >> "$lean_file" <<LEAN
example
    [Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiTargetHeightCoeffControlHyp]
    [Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiAntiTargetHeightCoeffControlHyp] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData := by
  exact $ENDPOINT
LEAN
      ;;
    *)
      echo "unknown gate mode: $mode" >&2
      return 2
      ;;
  esac

  lake env lean "$lean_file" >"$out_file" 2>&1
}

generate_session_prompt() {
  local session_index="$1"
  local prompt_file="$2"
  local prior_blocker="$3"

  : > "$prompt_file"
  if [[ -n "$CONTINUATION_PROMPT_TEMPLATE" && -f "$CONTINUATION_PROMPT_TEMPLATE" ]]; then
    cat "$CONTINUATION_PROMPT_TEMPLATE" >> "$prompt_file"
    printf "\n\n" >> "$prompt_file"
  fi

  cat >> "$prompt_file" <<EOF_PROMPT
Close out the exact explicit deep leaves for B7 in:
- $DEEP_BLOCKERS_FILE
- private theorem deep_blocker_B7a
- private theorem deep_blocker_B7b

Hard requirements:
1. Do not replace leaves with axioms.
2. Preserve existing constructive chain and use proved obstruction/compatibility infrastructure.
3. After edits, run targeted build:
   lake build ${TARGETED_BUILD_TARGETS[*]}

Current loop session: $session_index
Run directory: $RUN_DIR
Previous blocker: $prior_blocker
Previous report: ${latest_report_path:-none}

Deliverables this session:
- measurable proof progress toward removing sorry at deep_blocker_B7a/deep_blocker_B7b,
- build logs confirming status,
- explicit note of remaining blocker if still open.
EOF_PROMPT
}

run_construct_session() {
  local session_prompt="$1"
  local construct_log="$2"

  local rc=0
  if [[ -n "$AUTO_CONSTRUCT_CMD" ]]; then
    if run_with_timeout "$SESSION_TIMEOUT_SECS" bash -lc "$AUTO_CONSTRUCT_CMD" >"$construct_log" 2>&1; then
      rc=0
    else
      rc=$?
    fi
  else
    if run_with_timeout "$SESSION_TIMEOUT_SECS" \
      codex exec --dangerously-bypass-approvals-and-sandbox -C "$ROOT" - < "$session_prompt" >"$construct_log" 2>&1; then
      rc=0
    else
      rc=$?
    fi
  fi
  return "$rc"
}

write_session_json() {
  local report_file="$1"
  python3 - "$report_file" <<'PY'
import json
import os
import sys


def as_int(name, default=0):
    try:
        return int(os.environ.get(name, default))
    except Exception:
        return default


def as_bool(name):
    return os.environ.get(name, "0") in ("1", "true", "True", "yes")

reasons = [r for r in os.environ.get("REPORT_PROGRESS_REASONS", "").split(",") if r]

data = {
    "session_index": as_int("REPORT_SESSION_INDEX"),
    "timestamp": os.environ.get("REPORT_TIMESTAMP", ""),
    "duration_secs": as_int("REPORT_DURATION_SECS"),
    "construct": {
        "status": os.environ.get("REPORT_CONSTRUCT_STATUS", "unknown"),
        "timed_out": as_bool("REPORT_CONSTRUCT_TIMED_OUT"),
        "exit_code": as_int("REPORT_CONSTRUCT_EXIT_CODE", -1),
    },
    "gates": {
        "target": os.environ.get("REPORT_TARGET_STATUS", "fail"),
        "anti": os.environ.get("REPORT_ANTI_STATUS", "fail"),
        "endpoint": os.environ.get("REPORT_ENDPOINT_STATUS", "fail"),
        "targeted_build": os.environ.get("REPORT_BUILD_STATUS", "fail"),
        "b7_leaf_no_sorry": os.environ.get("REPORT_B7_LEAF_STATUS", "fail"),
    },
    "b7_leaf": {
        "deep_blocker_B7a_has_sorry": as_int("REPORT_B7A_HAS_SORRY", 1),
        "deep_blocker_B7b_has_sorry": as_int("REPORT_B7B_HAS_SORRY", 1),
        "sorry_count": as_int("REPORT_B7_SORRY_COUNT", 2),
    },
    "metrics": {
        "gate_pass_count": as_int("REPORT_GATE_PASS_COUNT", 0),
        "targeted_build_pass": as_int("REPORT_TARGETED_BUILD_PASS", 0),
        "b7_obligation_artifacts_updated": as_int("REPORT_B7_ARTIFACTS_UPDATED", 0),
    },
    "progress": {
        "status": os.environ.get("REPORT_PROGRESS_STATUS", "fail"),
        "reasons": reasons,
        "stale_sessions": as_int("REPORT_STALE_SESSIONS", 0),
        "max_stale_sessions": as_int("REPORT_MAX_STALE_SESSIONS", 0),
    },
    "decision": {
        "next_blocker": os.environ.get("REPORT_NEXT_BLOCKER", "unknown"),
        "next_action": os.environ.get("REPORT_NEXT_ACTION", "unknown"),
    },
    "logs": {
        "prompt": os.environ.get("REPORT_PROMPT_LOG", ""),
        "construct": os.environ.get("REPORT_CONSTRUCT_LOG", ""),
        "build": os.environ.get("REPORT_BUILD_LOG", ""),
        "target": os.environ.get("REPORT_TARGET_LOG", ""),
        "anti": os.environ.get("REPORT_ANTI_LOG", ""),
        "endpoint": os.environ.get("REPORT_ENDPOINT_LOG", ""),
        "b7_leaf": os.environ.get("REPORT_B7_LEAF_LOG", ""),
    },
}

with open(sys.argv[1], "w", encoding="utf-8") as f:
    json.dump(data, f, indent=2, sort_keys=True)
PY
}

session_index=1
last_blocker="none"

while :; do
  now_epoch="$(date +%s)"
  elapsed="$((now_epoch - start_epoch))"
  if (( elapsed > MAX_WALLCLOCK_SECS )); then
    echo "Reached MAX_WALLCLOCK_SECS=${MAX_WALLCLOCK_SECS}. Exiting." >&2
    exit 5
  fi

  if (( MAX_SESSIONS > 0 && session_index > MAX_SESSIONS )); then
    echo "Reached MAX_SESSIONS=${MAX_SESSIONS}. Exiting." >&2
    exit 4
  fi

  ts="$(date '+%Y%m%d_%H%M%S')"
  sess_dir="$RUN_DIR/session_${session_index}_${ts}"
  mkdir -p "$sess_dir"

  prompt_log="$sess_dir/session_prompt.txt"
  construct_log="$sess_dir/construct.log"
  build_log="$sess_dir/targeted_build.log"
  target_log="$sess_dir/gate_target.log"
  anti_log="$sess_dir/gate_anti.log"
  endpoint_log="$sess_dir/gate_endpoint.log"
  b7_leaf_log="$sess_dir/gate_b7_leaf.log"
  report_json="$sess_dir/session_report.json"

  session_start="$(date +%s)"

  pre_snapshot="$(snapshot_b7_chain)"
  generate_session_prompt "$session_index" "$prompt_log" "$last_blocker"

  construct_status="pass"
  construct_timed_out=0
  construct_exit_code=0
  if run_construct_session "$prompt_log" "$construct_log"; then
    construct_exit_code=0
  else
    construct_exit_code=$?
    construct_status="fail"
    if [[ "$construct_exit_code" -eq 124 ]]; then
      construct_timed_out=1
    fi
  fi

  build_status="fail"
  targeted_build_pass=0
  if lake build "${TARGETED_BUILD_TARGETS[@]}" >"$build_log" 2>&1; then
    build_status="pass"
    targeted_build_pass=1
  fi

  t1="$(mktemp -t ralph_b7_target_gate)"
  t2="$(mktemp -t ralph_b7_anti_gate)"
  t3="$(mktemp -t ralph_b7_endpoint_gate)"

  target_status="fail"
  anti_status="fail"
  endpoint_status="fail"

  if run_lean_gate target "$t1" "$target_log"; then target_status="pass"; fi
  if run_lean_gate anti "$t2" "$anti_log"; then anti_status="pass"; fi
  if run_lean_gate endpoint "$t3" "$endpoint_log"; then endpoint_status="pass"; fi

  rm -f "$t1" "$t2" "$t3"

  read -r b7a_has_sorry b7b_has_sorry b7_sorry_count < <(check_b7_leaf_sorry_count "$DEEP_BLOCKERS_FILE")
  {
    echo "deep_blocker_B7a_has_sorry=$b7a_has_sorry"
    echo "deep_blocker_B7b_has_sorry=$b7b_has_sorry"
    echo "b7_sorry_count=$b7_sorry_count"
  } >"$b7_leaf_log"

  b7_leaf_status="pass"
  if (( b7a_has_sorry == 1 || b7b_has_sorry == 1 )); then
    b7_leaf_status="fail"
  fi

  gate_pass_count=0
  [[ "$target_status" == "pass" ]] && gate_pass_count=$((gate_pass_count + 1))
  [[ "$anti_status" == "pass" ]] && gate_pass_count=$((gate_pass_count + 1))
  [[ "$endpoint_status" == "pass" ]] && gate_pass_count=$((gate_pass_count + 1))

  post_snapshot="$(snapshot_b7_chain)"
  b7_artifacts_updated=0
  if [[ "$pre_snapshot" != "$post_snapshot" ]]; then
    b7_artifacts_updated=1
  fi

  progress_status="fail"
  progress_reasons=()

  if (( b7_sorry_count < best_b7_sorry_count )); then
    best_b7_sorry_count="$b7_sorry_count"
    progress_status="pass"
    progress_reasons+=("b7_sorry_count_decreased")
  fi
  if (( gate_pass_count > best_gate_pass_count )); then
    best_gate_pass_count="$gate_pass_count"
    progress_status="pass"
    progress_reasons+=("gate_pass_count_increased")
  fi
  if (( targeted_build_pass > best_targeted_build_pass )); then
    best_targeted_build_pass="$targeted_build_pass"
    progress_status="pass"
    progress_reasons+=("targeted_build_passed")
  fi
  if (( b7_artifacts_updated == 1 )); then
    progress_status="pass"
    progress_reasons+=("b7_chain_files_updated")
  fi

  if [[ "$progress_status" == "pass" ]]; then
    stale_sessions=0
  else
    stale_sessions=$((stale_sessions + 1))
  fi

  next_blocker="none"
  if [[ "$construct_status" != "pass" ]]; then
    if (( construct_timed_out == 1 )); then
      next_blocker="construction command timed out"
    else
      next_blocker="construction command failed"
    fi
  elif [[ "$build_status" != "pass" ]]; then
    next_blocker="targeted build failure"
  elif [[ "$b7_leaf_status" != "pass" ]]; then
    next_blocker="B7 leaf sorries remain in DeepBlockersResolved (deep_blocker_B7a/B7b)"
  elif [[ "$target_status" != "pass" ]]; then
    next_blocker="target coeff-control gate unresolved"
  elif [[ "$anti_status" != "pass" ]]; then
    next_blocker="anti coeff-control gate unresolved"
  elif [[ "$endpoint_status" != "pass" ]]; then
    next_blocker="rhPiWitness_proved endpoint gate unresolved"
  elif [[ "$progress_status" != "pass" ]]; then
    next_blocker="no measurable progress"
  fi

  success=0
  if [[ "$build_status" == "pass" &&
        "$b7_leaf_status" == "pass" &&
        "$target_status" == "pass" &&
        "$anti_status" == "pass" &&
        "$endpoint_status" == "pass" ]]; then
    success=1
  fi

  session_end="$(date +%s)"
  session_duration="$((session_end - session_start))"

  next_action="relaunch"
  if (( success == 1 )); then
    next_action="success"
  elif (( stale_sessions >= MAX_STALE_SESSIONS )); then
    next_action="stop_stale"
  elif (( MAX_SESSIONS > 0 && session_index >= MAX_SESSIONS )); then
    next_action="stop_max_sessions"
  elif (( elapsed >= MAX_WALLCLOCK_SECS )); then
    next_action="stop_wallclock"
  elif [[ "$RELAUNCH_ON_NON_CLOSURE" != "1" ]]; then
    next_action="stop_non_closure"
  fi

  progress_reasons_csv=""
  if (( ${#progress_reasons[@]} > 0 )); then
    progress_reasons_csv="$(IFS=, ; echo "${progress_reasons[*]}")"
  fi

  REPORT_SESSION_INDEX="$session_index" \
  REPORT_TIMESTAMP="$ts" \
  REPORT_DURATION_SECS="$session_duration" \
  REPORT_CONSTRUCT_STATUS="$construct_status" \
  REPORT_CONSTRUCT_TIMED_OUT="$construct_timed_out" \
  REPORT_CONSTRUCT_EXIT_CODE="$construct_exit_code" \
  REPORT_TARGET_STATUS="$target_status" \
  REPORT_ANTI_STATUS="$anti_status" \
  REPORT_ENDPOINT_STATUS="$endpoint_status" \
  REPORT_BUILD_STATUS="$build_status" \
  REPORT_B7_LEAF_STATUS="$b7_leaf_status" \
  REPORT_B7A_HAS_SORRY="$b7a_has_sorry" \
  REPORT_B7B_HAS_SORRY="$b7b_has_sorry" \
  REPORT_B7_SORRY_COUNT="$b7_sorry_count" \
  REPORT_GATE_PASS_COUNT="$gate_pass_count" \
  REPORT_TARGETED_BUILD_PASS="$targeted_build_pass" \
  REPORT_B7_ARTIFACTS_UPDATED="$b7_artifacts_updated" \
  REPORT_PROGRESS_STATUS="$progress_status" \
  REPORT_PROGRESS_REASONS="$progress_reasons_csv" \
  REPORT_STALE_SESSIONS="$stale_sessions" \
  REPORT_MAX_STALE_SESSIONS="$MAX_STALE_SESSIONS" \
  REPORT_NEXT_BLOCKER="$next_blocker" \
  REPORT_NEXT_ACTION="$next_action" \
  REPORT_PROMPT_LOG="$prompt_log" \
  REPORT_CONSTRUCT_LOG="$construct_log" \
  REPORT_BUILD_LOG="$build_log" \
  REPORT_TARGET_LOG="$target_log" \
  REPORT_ANTI_LOG="$anti_log" \
  REPORT_ENDPOINT_LOG="$endpoint_log" \
  REPORT_B7_LEAF_LOG="$b7_leaf_log" \
  write_session_json "$report_json"

  latest_report_path="$report_json"
  last_blocker="$next_blocker"

  echo "=== Ralph B7 Session ${session_index} ==="
  echo "timestamp: ${ts}"
  echo "run_dir: ${sess_dir}"
  echo "construct: ${construct_status} (exit=${construct_exit_code}, timed_out=${construct_timed_out})"
  echo "targeted_build: ${build_status}"
  echo "gate_target: ${target_status}"
  echo "gate_anti: ${anti_status}"
  echo "gate_endpoint: ${endpoint_status}"
  echo "gate_b7_leaf_no_sorry: ${b7_leaf_status}"
  echo "b7_sorry_count: ${b7_sorry_count} (a=${b7a_has_sorry}, b=${b7b_has_sorry})"
  echo "gate_pass_count: ${gate_pass_count}/3"
  echo "b7_artifacts_updated: ${b7_artifacts_updated}"
  echo "progress: ${progress_status}"
  echo "progress_reasons: ${progress_reasons[*]:-none}"
  echo "stale_sessions: ${stale_sessions}/${MAX_STALE_SESSIONS}"
  echo "next_blocker: ${next_blocker}"
  echo "next_action: ${next_action}"
  echo "session_report_json: ${report_json}"

  if (( success == 1 )); then
    echo "Ralph B7 loop complete: B7a/B7b closed and all closure gates passed."
    exit 0
  fi

  if [[ "$next_action" == "stop_stale" ]]; then
    echo "Stopping: no measurable progress for ${stale_sessions} consecutive sessions."
    exit 3
  fi
  if [[ "$next_action" == "stop_max_sessions" ]]; then
    echo "Stopping: reached MAX_SESSIONS=${MAX_SESSIONS}."
    exit 4
  fi
  if [[ "$next_action" == "stop_wallclock" ]]; then
    echo "Stopping: reached MAX_WALLCLOCK_SECS=${MAX_WALLCLOCK_SECS}."
    exit 5
  fi
  if [[ "$next_action" == "stop_non_closure" ]]; then
    echo "Stopping: RELAUNCH_ON_NON_CLOSURE=${RELAUNCH_ON_NON_CLOSURE}."
    exit 6
  fi

  session_index=$((session_index + 1))
  sleep "$SLEEP_SECS"
done
