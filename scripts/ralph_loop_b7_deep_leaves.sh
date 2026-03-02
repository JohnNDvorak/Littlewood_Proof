#!/usr/bin/env bash
set -euo pipefail

# Ralph Wiggum loop for RH-pi Blocker 7 deep leaves.
# Multi-session orchestration with immediate fresh-session relaunch until:
#   - deep leaves are closed (no sorry/admit at the three upstream B7 leaves),
#   - no new axioms are introduced in the B7 chain files,
#   - no sorry/admit relocation occurs in the B7 chain files,
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

MAX_SESSIONS="${MAX_SESSIONS:-20}"                      # total fresh sessions
MAX_STALE_SESSIONS="${MAX_STALE_SESSIONS:-5}"          # consecutive no-real-progress sessions
SESSION_TIMEOUT_SECS="${SESSION_TIMEOUT_SECS:-2700}"   # timeout for proof-construction command
MAX_WALLCLOCK_SECS="${MAX_WALLCLOCK_SECS:-43200}"      # absolute run timeout
SLEEP_SECS="${SLEEP_SECS:-1}"
RELAUNCH_ON_NON_CLOSURE="${RELAUNCH_ON_NON_CLOSURE:-1}"
AUTO_CONSTRUCT_CMD="${AUTO_CONSTRUCT_CMD:-}"
CONTINUATION_PROMPT_TEMPLATE="${CONTINUATION_PROMPT_TEMPLATE:-}"
REAL_PROGRESS_MODE="${REAL_PROGRESS_MODE:-leaf_milestone_closure_v1}"
ESCALATION_ON_STALL="${ESCALATION_ON_STALL:-1}"
MAX_MANDATORY_DEEP_EDIT_FAILURES="${MAX_MANDATORY_DEEP_EDIT_FAILURES:-2}"
ACTIVE_LEAF_GRACE_SESSIONS="${ACTIVE_LEAF_GRACE_SESSIONS:-2}"
ACTIVE_LEAF_DEADLINE_SESSIONS="${ACTIVE_LEAF_DEADLINE_SESSIONS:-6}"
STOP_ON_LEAF_MILESTONE_MISS="${STOP_ON_LEAF_MILESTONE_MISS:-1}"

RUN_ID="${RUN_ID:-$(date '+%Y%m%d_%H%M%S')}"
RUN_DIR="${LOG_DIR:-$ROOT/.lake/ralph_b7_deep_leaves/$RUN_ID}"
BEST_STATE_DIR="${BEST_STATE_DIR:-$RUN_DIR/best_state}"
mkdir -p "$RUN_DIR" "$BEST_STATE_DIR"

DEEP_BLOCKERS_FILE="Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean"
DEFAULT_B7_CONTINUATION_TEMPLATE="$ROOT/docs/ralph_b7_forcing_prompt_template.txt"
if [[ -z "$CONTINUATION_PROMPT_TEMPLATE" && -f "$DEFAULT_B7_CONTINUATION_TEMPLATE" ]]; then
  CONTINUATION_PROMPT_TEMPLATE="$DEFAULT_B7_CONTINUATION_TEMPLATE"
fi

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
MIN_SORRY_REDUCTION_REQUIRED="${MIN_SORRY_REDUCTION_REQUIRED:-3}"

start_epoch="$(date +%s)"
latest_report_path=""
last_blocker="none"

best_session_index=0
best_snapshot_dir=""
best_deep_leaf_sorry_count=9999
stale_sessions_real_progress=0
stale_sessions_mandatory_deep_edit=0
active_leaf_current="none"
active_leaf_session_count=0

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

check_b7_deep_leaf_sorry_count() {
  local file="$1"
  awk '
    BEGIN { mode=""; target=0; anti=0; coeff=0 }
    /^[[:space:]]*private theorem deep_blocker_B7_target_phase_coupling_family_leaf([[:space:]]|$)/ { mode="target"; next }
    /^[[:space:]]*private theorem deep_blocker_B7_antitarget_phase_coupling_family_leaf([[:space:]]|$)/ { mode="anti"; next }
    /^[[:space:]]*private theorem deep_blocker_B7_coeff_control_leaf([[:space:]]|$)/ { mode="coeff"; next }
    mode=="target" && /^[[:space:]]*private theorem deep_blocker_B7_antitarget_phase_coupling_family_leaf([[:space:]]|$)/ { mode="anti"; next }
    mode=="anti" && /^[[:space:]]*private theorem deep_blocker_B7_coeff_control_leaf([[:space:]]|$)/ { mode="coeff"; next }
    mode!="" && /^[[:space:]]*(private theorem|theorem|lemma|def|class|instance|abbrev|end)([[:space:]]|$)/ { mode="" }
    mode=="target" && (/^[[:space:]]*(sorry|admit)([[:space:]]|$)/ || /[[:space:]]by[[:space:]]+(sorry|admit)([[:space:]]|$)/) { target=1 }
    mode=="anti" && (/^[[:space:]]*(sorry|admit)([[:space:]]|$)/ || /[[:space:]]by[[:space:]]+(sorry|admit)([[:space:]]|$)/) { anti=1 }
    mode=="coeff" && (/^[[:space:]]*(sorry|admit)([[:space:]]|$)/ || /[[:space:]]by[[:space:]]+(sorry|admit)([[:space:]]|$)/) { coeff=1 }
    END { printf "%d %d %d %d\n", target, anti, coeff, target+anti+coeff }
  ' "$file"
}

check_b7_no_exfalso_count() {
  local file="$1"
  rg -n --pcre2 "False\\.elim|deep_blocker_B7_.*inconsistent|deep_blocker_B7_not_truncated_explicit_formula_pi|deep_blocker_B7_truncated_explicit_formula_pi_false" "$file" 2>/dev/null | wc -l | tr -d ' ' || true
}

count_axiom_lines() {
  local out
  out="$(rg -c --pcre2 '^[[:space:]]*axiom[[:space:]]' "${B7_CHAIN_FILES[@]}" 2>/dev/null || true)"
  if [[ -z "$out" ]]; then
    echo 0
  else
    awk -F: '{ s += $2 } END { print s + 0 }' <<< "$out"
  fi
}

count_code_sorry_like_lines() {
  local out
  out="$(rg -c --pcre2 '(^[[:space:]]*(sorry|admit)[[:space:]]*$)|([[:space:]]by[[:space:]]+(sorry|admit)([[:space:]]|$))' "${B7_CHAIN_FILES[@]}" 2>/dev/null || true)"
  if [[ -z "$out" ]]; then
    echo 0
  else
    awk -F: '{ s += $2 } END { print s + 0 }' <<< "$out"
  fi
}

file_digest() {
  local file="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$file" 2>/dev/null | awk '{print $1}' || true
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$file" 2>/dev/null | awk '{print $1}' || true
  else
    cksum "$file" 2>/dev/null | awk '{print $1 ":" $2}' || true
  fi
}

detect_active_leaf() {
  local target_has_sorry="$1"
  local antitarget_has_sorry="$2"
  local coeff_has_sorry="$3"

  if (( target_has_sorry == 1 )); then
    echo "target deep_blocker_B7_target_phase_coupling_family_leaf deep_blocker_B7_target_phase_coupling_step_"
  elif (( antitarget_has_sorry == 1 )); then
    echo "antitarget deep_blocker_B7_antitarget_phase_coupling_family_leaf deep_blocker_B7_antitarget_phase_coupling_step_"
  elif (( coeff_has_sorry == 1 )); then
    echo "coeff deep_blocker_B7_coeff_control_leaf deep_blocker_B7_coeff_control_step_"
  else
    echo "none none none"
  fi
}

count_active_leaf_step_lemmas() {
  local file="$1"
  local step_prefix="$2"
  local out
  if [[ "$step_prefix" == "none" ]]; then
    echo 0
    return
  fi
  out="$(
    rg -n --pcre2 "^[[:space:]]*(private[[:space:]]+)?(theorem|lemma)[[:space:]]+${step_prefix}[A-Za-z0-9_]*([[:space:]]|:|\\()" "$file" 2>/dev/null || true
  )"
  if [[ -z "$out" ]]; then
    echo 0
  else
    printf '%s\n' "$out" | wc -l | tr -d ' '
  fi
}

count_active_leaf_step_usage() {
  local file="$1"
  local leaf_decl="$2"
  local step_prefix="$3"
  if [[ "$leaf_decl" == "none" || "$step_prefix" == "none" ]]; then
    echo 0
    return
  fi
  awk -v decl="$leaf_decl" -v prefix="$step_prefix" '
    BEGIN { inleaf=0; c=0 }
    $0 ~ ("^[[:space:]]*private theorem " decl "([[:space:]]|:)") { inleaf=1; next }
    inleaf && $0 ~ /^[[:space:]]*(private theorem|theorem|lemma|def|class|instance|abbrev|end)([[:space:]]|$)/ { inleaf=0 }
    inleaf && index($0, prefix) > 0 { c++ }
    END { print c + 0 }
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

snapshot_best_state() {
  local session_index="$1"
  local ts="$2"
  local deep_leaf_sorry_count="$3"
  local build_status="$4"
  local report_path="$5"

  local snap_dir="$BEST_STATE_DIR/session_${session_index}_${ts}"
  rm -rf "$snap_dir"
  mkdir -p "$snap_dir"

  local f
  for f in "${B7_CHAIN_FILES[@]}"; do
    mkdir -p "$snap_dir/$(dirname "$f")"
    cp "$ROOT/$f" "$snap_dir/$f"
  done

  best_snapshot_dir="$snap_dir"
  best_session_index="$session_index"
  best_deep_leaf_sorry_count="$deep_leaf_sorry_count"

  cat > "$BEST_STATE_DIR/manifest.json" <<EOF_MANIFEST
{
  "best_session_index": $best_session_index,
  "timestamp": "$ts",
  "deep_leaf_sorry_count": $best_deep_leaf_sorry_count,
  "targeted_build": "$build_status",
  "snapshot_dir": "$best_snapshot_dir",
  "source_report": "$report_path"
}
EOF_MANIFEST
}

write_escalation_bundle() {
  local reason="$1"
  local md_out="$RUN_DIR/escalation_summary.md"
  local json_out="$RUN_DIR/escalation_summary.json"
  local restart_cmd
  restart_cmd="cd $ROOT && REAL_PROGRESS_MODE=leaf_milestone_closure_v1 ACTIVE_LEAF_GRACE_SESSIONS=0 ACTIVE_LEAF_DEADLINE_SESSIONS=3 MAX_SESSIONS=6 MAX_STALE_SESSIONS=3 RELAUNCH_ON_NON_CLOSURE=1 bash scripts/ralph_loop_b7_deep_leaves.sh"

  REPORT_RUN_DIR="$RUN_DIR" \
  REPORT_REASON="$reason" \
  REPORT_DEEP_FILE="$DEEP_BLOCKERS_FILE" \
  REPORT_BEST_SESSION_INDEX="$best_session_index" \
  REPORT_BEST_DEEP_SORRY="$best_deep_leaf_sorry_count" \
  REPORT_BEST_SNAPSHOT_DIR="$best_snapshot_dir" \
  REPORT_ACTIVE_LEAF_NAME="${active_leaf_name:-none}" \
  REPORT_ACTIVE_LEAF_SESSION_COUNT="${active_leaf_session_count:-0}" \
  REPORT_ACTIVE_LEAF_GRACE_SESSIONS="$ACTIVE_LEAF_GRACE_SESSIONS" \
  REPORT_ACTIVE_LEAF_DEADLINE_SESSIONS="$ACTIVE_LEAF_DEADLINE_SESSIONS" \
  REPORT_REAL_PROGRESS_MODE="$REAL_PROGRESS_MODE" \
  REPORT_RESTART_CMD="$restart_cmd" \
  python3 - "$md_out" "$json_out" <<'PY'
import glob
import json
import os
import re
import sys

md_out = sys.argv[1]
json_out = sys.argv[2]
run_dir = os.environ.get("REPORT_RUN_DIR", "")
reason = os.environ.get("REPORT_REASON", "")
deep_file = os.environ.get("REPORT_DEEP_FILE", "")
best_session_index = int(os.environ.get("REPORT_BEST_SESSION_INDEX", "0") or 0)
best_deep_sorry = int(os.environ.get("REPORT_BEST_DEEP_SORRY", "9999") or 9999)
best_snapshot_dir = os.environ.get("REPORT_BEST_SNAPSHOT_DIR", "")
active_leaf_name = os.environ.get("REPORT_ACTIVE_LEAF_NAME", "none")
active_leaf_session_count = int(os.environ.get("REPORT_ACTIVE_LEAF_SESSION_COUNT", "0") or 0)
active_leaf_grace_sessions = int(os.environ.get("REPORT_ACTIVE_LEAF_GRACE_SESSIONS", "0") or 0)
active_leaf_deadline_sessions = int(os.environ.get("REPORT_ACTIVE_LEAF_DEADLINE_SESSIONS", "0") or 0)
real_progress_mode = os.environ.get("REPORT_REAL_PROGRESS_MODE", "")
restart_cmd = os.environ.get("REPORT_RESTART_CMD", "")

report_paths = sorted(glob.glob(os.path.join(run_dir, "session_*", "session_report.json")))

def parse_report(path):
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)

    session_index = data.get("session_index", os.path.basename(os.path.dirname(path)))
    timestamp = data.get("timestamp", "")

    build = "unknown"
    gates = data.get("gates")
    if isinstance(gates, dict):
        build = gates.get("targeted_build", build)
    targeted = data.get("targeted_build")
    if isinstance(targeted, dict):
        build = targeted.get("status", build)

    deep_leaf = data.get("deep_leaf", {})
    if isinstance(deep_leaf, dict) and "sorry_count" in deep_leaf:
        sorry_count = deep_leaf.get("sorry_count")
    elif isinstance(deep_leaf, dict) and {
        "target_phase_coupling_has_sorry",
        "antitarget_phase_coupling_has_sorry",
        "coeff_control_has_sorry",
    }.issubset(set(deep_leaf.keys())):
        sorry_count = (
            int(deep_leaf.get("target_phase_coupling_has_sorry", 0))
            + int(deep_leaf.get("antitarget_phase_coupling_has_sorry", 0))
            + int(deep_leaf.get("coeff_control_has_sorry", 0))
        )
    else:
        sorry_count = "na"

    real = data.get("real_progress")
    if isinstance(real, dict):
        real_status = real.get("status", "unknown")
        regression = bool(real.get("regression_detected", False))
    else:
        prog = data.get("progress", {}) if isinstance(data.get("progress", {}), dict) else {}
        real_status = prog.get("status", "unknown")
        regression = False

    return {
        "session_index": session_index,
        "timestamp": timestamp,
        "targeted_build": build,
        "deep_leaf_sorry_count": sorry_count,
        "real_progress_status": real_status,
        "regression_detected": regression,
        "report_path": path,
    }

rows = [parse_report(p) for p in report_paths]
last5 = rows[-5:]

def extract_leaf_lines(path):
    lines = {
        "target_phase_coupling_decl_line": None,
        "antitarget_phase_coupling_decl_line": None,
        "coeff_control_decl_line": None,
        "target_phase_coupling_sorry_line": None,
        "antitarget_phase_coupling_sorry_line": None,
        "coeff_control_sorry_line": None,
    }

    if not path or not os.path.exists(path):
        return lines

    mode = None
    with open(path, "r", encoding="utf-8") as f:
        for i, line in enumerate(f, 1):
            stripped = line.strip()
            if stripped.startswith("private theorem deep_blocker_B7_target_phase_coupling_family_leaf"):
                mode = "target_phase_coupling"
                lines["target_phase_coupling_decl_line"] = i
                continue
            if stripped.startswith("private theorem deep_blocker_B7_antitarget_phase_coupling_family_leaf"):
                mode = "antitarget_phase_coupling"
                lines["antitarget_phase_coupling_decl_line"] = i
                continue
            if stripped.startswith("private theorem deep_blocker_B7_coeff_control_leaf"):
                mode = "coeff_control"
                lines["coeff_control_decl_line"] = i
                continue

            if mode and re.match(r"^(private theorem|theorem|lemma|def|class|instance|abbrev|end)\\b", stripped):
                mode = None

            if mode and re.match(r"^sorry$", stripped):
                key = f"{mode}_sorry_line"
                if lines.get(key) is None:
                    lines[key] = i

    return lines

leaf_lines = extract_leaf_lines(deep_file)

payload = {
    "reason": reason,
    "run_dir": run_dir,
    "milestone": {
        "active_leaf_name": active_leaf_name,
        "active_leaf_session_count": active_leaf_session_count,
        "active_leaf_grace_sessions": active_leaf_grace_sessions,
        "active_leaf_deadline_sessions": active_leaf_deadline_sessions,
        "real_progress_mode": real_progress_mode,
    },
    "best_state": {
        "best_session_index": best_session_index,
        "best_deep_leaf_sorry_count": best_deep_sorry,
        "best_snapshot_dir": best_snapshot_dir,
    },
    "last5_sessions": last5,
        "remaining_blockers": {
            "deep_blockers_file": deep_file,
            "leaf_lines": leaf_lines,
            "required_theorems": [
            "deep_blocker_B7_target_phase_coupling_family_leaf",
            "deep_blocker_B7_antitarget_phase_coupling_family_leaf",
            "deep_blocker_B7_coeff_control_leaf",
            ],
        },
    }

with open(json_out, "w", encoding="utf-8") as f:
    json.dump(payload, f, indent=2, sort_keys=True)

md = []
md.append("# B7 Real-Progress Escalation")
md.append("")
md.append(f"- Reason: `{reason}`")
md.append(f"- Run dir: `{run_dir}`")
md.append(f"- Best deep-leaf sorry count: `{best_deep_sorry}` (session `{best_session_index}`)")
md.append(f"- Best snapshot: `{best_snapshot_dir or 'none'}`")
md.append(f"- Active leaf at stop: `{active_leaf_name}` (session_count `{active_leaf_session_count}`, grace `{active_leaf_grace_sessions}`, deadline `{active_leaf_deadline_sessions}`)")
md.append(f"- Real-progress mode: `{real_progress_mode}`")
md.append("")
md.append("## Last 5 Sessions")
md.append("")
md.append("| Session | Timestamp | Build | Deep leaf sorry count | Real progress | Regression |")
md.append("|---|---|---|---:|---|---|")
for row in last5:
    md.append(
        f"| {row['session_index']} | {row['timestamp']} | {row['targeted_build']} | {row['deep_leaf_sorry_count']} | {row['real_progress_status']} | {str(row['regression_detected']).lower()} |"
    )

md.append("")
md.append("## Remaining Constructive Targets")
md.append("")
for name in payload["remaining_blockers"]["required_theorems"]:
    md.append(f"- `{name}`")
md.append("")
md.append("## Active Leaf Lines")
md.append("")
for k, v in leaf_lines.items():
    md.append(f"- `{k}`: `{v}`")

md.append("")
md.append("## Restart Recommendation")
md.append("")
md.append("- Strict leaf-closure restart command:")
md.append(f"  `{restart_cmd}`")

with open(md_out, "w", encoding="utf-8") as f:
    f.write("\n".join(md) + "\n")
PY
}

generate_session_prompt() {
  local session_index="$1"
  local prompt_file="$2"
  local prior_blocker="$3"
  local active_leaf_name="$4"
  local active_leaf_decl="$5"
  local active_leaf_step_prefix="$6"
  local active_leaf_step_lemma_count_start="$7"
  local active_leaf_step_usage_start="$8"
  local active_leaf_session_count="$9"
  local active_leaf_grace_sessions="${10}"
  local active_leaf_deadline_sessions="${11}"
  local active_leaf_post_grace="${12}"

  : > "$prompt_file"
  if [[ -n "$CONTINUATION_PROMPT_TEMPLATE" && -f "$CONTINUATION_PROMPT_TEMPLATE" ]]; then
    cat "$CONTINUATION_PROMPT_TEMPLATE" >> "$prompt_file"
    printf "\n\n" >> "$prompt_file"
  fi

  cat >> "$prompt_file" <<EOF_PROMPT
Close out the exact explicit deep leaves for B7 in:
- $DEEP_BLOCKERS_FILE
- private theorem deep_blocker_B7_target_phase_coupling_family_leaf
- private theorem deep_blocker_B7_antitarget_phase_coupling_family_leaf
- private theorem deep_blocker_B7_coeff_control_leaf

Hard requirements:
1. Do not replace leaves with axioms.
2. Do not relocate sorry/admit into other B7 chain files.
3. Preserve existing constructive chain and use proved obstruction/compatibility infrastructure.
4. Keep B7 closure strict constructive: no ex-falso (False.elim) in B7 path.
5. Do not regress from the best-known deep-leaf sorry count in this run.
6. Do not submit wiring-only edits or sorry shuffling; edits must target constructive theorem proof content.
7. After edits, run targeted build:
   lake build ${TARGETED_BUILD_TARGETS[*]}
8. Active leaf only this session: ${active_leaf_name} (${active_leaf_decl}).
9. Introduce at least one new proved active-leaf step lemma named with prefix:
   ${active_leaf_step_prefix}
10. Use new active-leaf step lemma(s) inside the active leaf proof body.
11. Emit this contract block in the response, exactly once, with non-empty values:
    MICRO_GOAL:
    PROVED_LEMMAS:
    LEAF_USAGE:
    BLOCKER_NEXT:
    CLOSURE_PLAN_STEP:

Current loop session: $session_index
Run directory: $RUN_DIR
Previous blocker: $prior_blocker
Previous report: ${latest_report_path:-none}
Real-progress policy: $REAL_PROGRESS_MODE
Best-known deep-leaf sorry count: $best_deep_leaf_sorry_count (session ${best_session_index})
Best snapshot directory: ${best_snapshot_dir:-none}
Active leaf at session start: ${active_leaf_name}
Active leaf declaration: ${active_leaf_decl}
Active leaf step prefix: ${active_leaf_step_prefix}
Active leaf step lemma count at start: ${active_leaf_step_lemma_count_start}
Active leaf step usage count at start: ${active_leaf_step_usage_start}
Active leaf session count: ${active_leaf_session_count}
Active leaf grace sessions: ${active_leaf_grace_sessions}
Active leaf deadline sessions: ${active_leaf_deadline_sessions}
Active leaf post-grace phase: ${active_leaf_post_grace}

Deliverables this session:
- constructive code changes that prioritize closing the active leaf sorry,
- build logs confirming status,
- explicit note of remaining blocker if still open.

Micro-goal menu (pick one and execute it in code):
- target_phase_coupling_seed_selection_step
- target_phase_coupling_phase_fit_step
- antitarget_phase_coupling_seed_selection_step
- antitarget_phase_coupling_phase_fit_step

Analysis-only sessions do not count. If no proved active-leaf step lemma is added and used, the session is a failure unless deep-leaf sorry count decreases.
If active leaf session count is above grace, step-lemma deltas do not count as progress. In post-grace phase, prioritize direct closure attempt of the active leaf.
Do not increase in-leaf usage count without either:
- new proved step lemma count increase (grace phase), or
- a direct active-leaf closure attempt (post-grace phase).
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


def split_csv(name):
    return [r for r in os.environ.get(name, "").split(",") if r]

real_reasons = split_csv("REPORT_REAL_PROGRESS_REASONS")
legacy_reasons = split_csv("REPORT_PROGRESS_REASONS")

real_progress_status = os.environ.get("REPORT_REAL_PROGRESS_STATUS", "fail")
if not real_reasons and legacy_reasons:
    real_reasons = legacy_reasons

data = {
    "schema_version": as_int("REPORT_SCHEMA_VERSION", 2),
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
        "deep_leaf_no_sorry": os.environ.get("REPORT_DEEP_LEAF_STATUS", "fail"),
        "no_exfalso_in_b7_path": os.environ.get("REPORT_NO_EXFALSO_STATUS", "fail"),
        "no_axiom_introduced": os.environ.get("REPORT_NO_AXIOM_STATUS", "fail"),
        "no_sorry_relocation": os.environ.get("REPORT_NO_SORRY_RELOCATION_STATUS", "fail"),
        "active_leaf_step_delta": os.environ.get("REPORT_ACTIVE_LEAF_STEP_DELTA_STATUS", "fail"),
        "mandatory_deep_edit": os.environ.get("REPORT_MANDATORY_DEEP_EDIT_STATUS", "fail"),
        "session_contract": os.environ.get("REPORT_SESSION_CONTRACT_STATUS", "fail"),
    },
    "deep_leaf": {
        "target_phase_coupling_has_sorry": as_int("REPORT_DEEP_TRUNCATED_HAS_SORRY", 1),
        "antitarget_phase_coupling_has_sorry": as_int("REPORT_DEEP_TARGET_HAS_SORRY", 1),
        "coeff_control_has_sorry": as_int("REPORT_DEEP_ANTITARGET_HAS_SORRY", 1),
        "sorry_count": as_int("REPORT_DEEP_SORRY_COUNT", 3),
    },
    "active_leaf": {
        "name": os.environ.get("REPORT_ACTIVE_LEAF_NAME", "none"),
        "declaration": os.environ.get("REPORT_ACTIVE_LEAF_DECL", "none"),
        "step_prefix": os.environ.get("REPORT_ACTIVE_LEAF_STEP_PREFIX", "none"),
        "session_count": as_int("REPORT_ACTIVE_LEAF_SESSION_COUNT", 0),
        "grace_sessions": as_int("REPORT_ACTIVE_LEAF_GRACE_SESSIONS", 0),
        "deadline_sessions": as_int("REPORT_ACTIVE_LEAF_DEADLINE_SESSIONS", 0),
        "post_grace_phase": as_bool("REPORT_ACTIVE_LEAF_POST_GRACE"),
    },
    "milestone": {
        "status": os.environ.get("REPORT_MILESTONE_STATUS", "unknown"),
        "stop_triggered": as_bool("REPORT_MILESTONE_STOP_TRIGGERED"),
        "stop_on_miss": as_bool("REPORT_STOP_ON_LEAF_MILESTONE_MISS"),
    },
    "metrics": {
        "gate_pass_count": as_int("REPORT_GATE_PASS_COUNT", 0),
        "targeted_build_pass": as_int("REPORT_TARGETED_BUILD_PASS", 0),
        "b7_obligation_artifacts_updated": as_int("REPORT_B7_ARTIFACTS_UPDATED", 0),
        "axiom_count_start": as_int("REPORT_AXIOM_COUNT_START", 0),
        "axiom_count_post": as_int("REPORT_AXIOM_COUNT_POST", 0),
        "sorry_count_start": as_int("REPORT_SORRY_COUNT_START", 0),
        "sorry_count_post": as_int("REPORT_SORRY_COUNT_POST", 0),
        "min_sorry_reduction_required": as_int("REPORT_MIN_SORRY_REDUCTION_REQUIRED", 3),
        "active_leaf_step_lemma_count_start": as_int("REPORT_ACTIVE_LEAF_STEP_LEMMA_COUNT_START", 0),
        "active_leaf_step_lemma_count_post": as_int("REPORT_ACTIVE_LEAF_STEP_LEMMA_COUNT_POST", 0),
        "active_leaf_step_usage_start": as_int("REPORT_ACTIVE_LEAF_STEP_USAGE_START", 0),
        "active_leaf_step_usage_post": as_int("REPORT_ACTIVE_LEAF_STEP_USAGE_POST", 0),
        "session_contract_marker_hits": as_int("REPORT_SESSION_CONTRACT_MARKER_HITS", 0),
        "mandatory_deep_edit_fail_streak": as_int("REPORT_STALE_MANDATORY_DEEP_EDIT", 0),
        "max_mandatory_deep_edit_fail_streak": as_int("REPORT_MAX_MANDATORY_DEEP_EDIT_FAILURES", 0),
        "active_leaf_closed_this_session": as_int("REPORT_ACTIVE_LEAF_CLOSED_THIS_SESSION", 0),
    },
    "real_progress": {
        "mode": os.environ.get("REPORT_REAL_PROGRESS_MODE", "leaf_milestone_closure_v1"),
        "status": real_progress_status,
        "reasons": real_reasons,
        "leaf_delta": as_bool("REPORT_LEAF_DELTA"),
        "active_leaf_step_delta": as_bool("REPORT_ACTIVE_LEAF_STEP_DELTA"),
        "regression_detected": as_bool("REPORT_REGRESSION_DETECTED"),
        "stale_sessions": as_int("REPORT_STALE_REAL_PROGRESS", 0),
        "max_stale_sessions": as_int("REPORT_MAX_STALE_SESSIONS", 0),
    },
    # Backward-compatible alias for older readers.
    "progress": {
        "status": real_progress_status,
        "reasons": real_reasons,
        "stale_sessions": as_int("REPORT_STALE_REAL_PROGRESS", 0),
        "max_stale_sessions": as_int("REPORT_MAX_STALE_SESSIONS", 0),
    },
    "best_state": {
        "session_index": as_int("REPORT_BEST_SESSION_INDEX", 0),
        "deep_leaf_sorry_count": as_int("REPORT_BEST_DEEP_SORRY", 9999),
        "snapshot_dir": os.environ.get("REPORT_BEST_SNAPSHOT_DIR", ""),
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
        "deep_leaf": os.environ.get("REPORT_DEEP_LEAF_LOG", ""),
        "exfalso": os.environ.get("REPORT_EXFALSO_LOG", ""),
        "axiom": os.environ.get("REPORT_AXIOM_LOG", ""),
        "relocation": os.environ.get("REPORT_RELOCATION_LOG", ""),
        "active_leaf_step": os.environ.get("REPORT_ACTIVE_LEAF_STEP_LOG", ""),
        "mandatory_deep_edit": os.environ.get("REPORT_MANDATORY_DEEP_EDIT_LOG", ""),
        "session_contract": os.environ.get("REPORT_SESSION_CONTRACT_LOG", ""),
    },
}

with open(sys.argv[1], "w", encoding="utf-8") as f:
    json.dump(data, f, indent=2, sort_keys=True)
PY
}

session_index=1
axiom_count_start="$(count_axiom_lines)"
sorry_count_start="$(count_code_sorry_like_lines)"
required_sorry_reduction="$MIN_SORRY_REDUCTION_REQUIRED"
target_sorry_ceiling="$sorry_count_start"

read -r _init_trunc _init_target _init_anti initial_deep_leaf_sorry_count \
  < <(check_b7_deep_leaf_sorry_count "$DEEP_BLOCKERS_FILE")
best_deep_leaf_sorry_count="$initial_deep_leaf_sorry_count"

echo "Ralph B7 deep-leaf baseline:"
echo "run_dir: $RUN_DIR"
echo "best_state_dir: $BEST_STATE_DIR"
echo "real_progress_mode: $REAL_PROGRESS_MODE"
echo "axiom_count_start: $axiom_count_start"
echo "sorry_count_start: $sorry_count_start"
echo "initial_deep_leaf_sorry_count: $initial_deep_leaf_sorry_count"
echo "required_sorry_reduction: $required_sorry_reduction"
echo "target_sorry_ceiling: $target_sorry_ceiling"
echo "max_mandatory_deep_edit_failures: $MAX_MANDATORY_DEEP_EDIT_FAILURES"
echo "active_leaf_grace_sessions: $ACTIVE_LEAF_GRACE_SESSIONS"
echo "active_leaf_deadline_sessions: $ACTIVE_LEAF_DEADLINE_SESSIONS"
echo "stop_on_leaf_milestone_miss: $STOP_ON_LEAF_MILESTONE_MISS"

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
  deep_leaf_log="$sess_dir/gate_deep_leaf.log"
  exfalso_log="$sess_dir/gate_no_exfalso.log"
  axiom_log="$sess_dir/gate_no_axiom.log"
  relocation_log="$sess_dir/gate_no_relocation.log"
  active_leaf_step_log="$sess_dir/gate_active_leaf_step.log"
  mandatory_deep_edit_log="$sess_dir/gate_mandatory_deep_edit.log"
  session_contract_log="$sess_dir/gate_session_contract.log"
  report_json="$sess_dir/session_report.json"

  session_start="$(date +%s)"

  pre_snapshot="$(snapshot_b7_chain)"
  pre_deep_digest="$(file_digest "$DEEP_BLOCKERS_FILE")"
  read -r pre_deep_trunc_has_sorry pre_deep_target_has_sorry pre_deep_antitarget_has_sorry pre_deep_leaf_sorry_count \
    < <(check_b7_deep_leaf_sorry_count "$DEEP_BLOCKERS_FILE")
  read -r active_leaf_name active_leaf_decl active_leaf_step_prefix \
    < <(detect_active_leaf "$pre_deep_trunc_has_sorry" "$pre_deep_target_has_sorry" "$pre_deep_antitarget_has_sorry")

  if [[ "$active_leaf_name" == "none" ]]; then
    active_leaf_session_count=0
    active_leaf_current="none"
  elif [[ "$active_leaf_name" == "$active_leaf_current" ]]; then
    active_leaf_session_count=$((active_leaf_session_count + 1))
  else
    active_leaf_current="$active_leaf_name"
    active_leaf_session_count=1
  fi
  active_leaf_post_grace=0
  if [[ "$active_leaf_name" != "none" ]] &&
     (( active_leaf_session_count > ACTIVE_LEAF_GRACE_SESSIONS )); then
    active_leaf_post_grace=1
  fi

  active_leaf_step_lemma_count_start="$(
    count_active_leaf_step_lemmas "$DEEP_BLOCKERS_FILE" "$active_leaf_step_prefix"
  )"
  active_leaf_step_usage_start="$(
    count_active_leaf_step_usage "$DEEP_BLOCKERS_FILE" "$active_leaf_decl" "$active_leaf_step_prefix"
  )"

  generate_session_prompt \
    "$session_index" \
    "$prompt_log" \
    "$last_blocker" \
    "$active_leaf_name" \
    "$active_leaf_decl" \
    "$active_leaf_step_prefix" \
    "$active_leaf_step_lemma_count_start" \
    "$active_leaf_step_usage_start" \
    "$active_leaf_session_count" \
    "$ACTIVE_LEAF_GRACE_SESSIONS" \
    "$ACTIVE_LEAF_DEADLINE_SESSIONS" \
    "$active_leaf_post_grace"

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

  read -r deep_trunc_has_sorry deep_target_has_sorry deep_antitarget_has_sorry deep_leaf_sorry_count \
    < <(check_b7_deep_leaf_sorry_count "$DEEP_BLOCKERS_FILE")
  {
    echo "deep_blocker_B7_target_phase_coupling_family_leaf_has_sorry=$deep_trunc_has_sorry"
    echo "deep_blocker_B7_antitarget_phase_coupling_family_leaf_has_sorry=$deep_target_has_sorry"
    echo "deep_blocker_B7_coeff_control_leaf_has_sorry=$deep_antitarget_has_sorry"
    echo "deep_leaf_sorry_count=$deep_leaf_sorry_count"
  } >"$deep_leaf_log"

  deep_leaf_status="pass"
  if (( deep_leaf_sorry_count > 0 )); then
    deep_leaf_status="fail"
  fi

  session_leaf_delta=0
  if (( deep_leaf_sorry_count < pre_deep_leaf_sorry_count )); then
    session_leaf_delta=1
  fi

  active_leaf_still_open=0
  active_leaf_closed_this_session=0
  case "$active_leaf_name" in
    target)
      active_leaf_still_open="$deep_trunc_has_sorry"
      if (( pre_deep_trunc_has_sorry == 1 && deep_trunc_has_sorry == 0 )); then
        active_leaf_closed_this_session=1
      fi
      ;;
    antitarget)
      active_leaf_still_open="$deep_target_has_sorry"
      if (( pre_deep_target_has_sorry == 1 && deep_target_has_sorry == 0 )); then
        active_leaf_closed_this_session=1
      fi
      ;;
    coeff)
      active_leaf_still_open="$deep_antitarget_has_sorry"
      if (( pre_deep_antitarget_has_sorry == 1 && deep_antitarget_has_sorry == 0 )); then
        active_leaf_closed_this_session=1
      fi
      ;;
    *)
      active_leaf_still_open=0
      active_leaf_closed_this_session=0
      ;;
  esac

  milestone_status="closed"
  if [[ "$active_leaf_name" == "none" ]] || (( active_leaf_still_open == 0 )); then
    milestone_status="closed"
  elif (( active_leaf_session_count <= ACTIVE_LEAF_GRACE_SESSIONS )); then
    milestone_status="within_grace"
  elif (( active_leaf_session_count < ACTIVE_LEAF_DEADLINE_SESSIONS )); then
    milestone_status="post_grace"
  else
    milestone_status="missed"
  fi

  exfalso_count="$(check_b7_no_exfalso_count "$DEEP_BLOCKERS_FILE")"
  no_exfalso_status="pass"
  if (( exfalso_count > 0 )); then
    no_exfalso_status="fail"
  fi
  {
    echo "b7_exfalso_pattern_count=$exfalso_count"
  } >"$exfalso_log"

  axiom_count_post="$(count_axiom_lines)"
  no_axiom_status="pass"
  if (( axiom_count_post != axiom_count_start )); then
    no_axiom_status="fail"
  fi
  {
    echo "axiom_count_start=$axiom_count_start"
    echo "axiom_count_post=$axiom_count_post"
  } >"$axiom_log"

  sorry_count_post="$(count_code_sorry_like_lines)"
  sorry_reduction="$((sorry_count_start - sorry_count_post))"
  no_sorry_relocation_status="pass"
  if (( sorry_count_post > sorry_count_start )); then
    no_sorry_relocation_status="fail"
  fi
  {
    echo "sorry_count_start=$sorry_count_start"
    echo "sorry_count_post=$sorry_count_post"
    echo "required_sorry_reduction=$required_sorry_reduction"
    echo "actual_sorry_reduction=$sorry_reduction"
    echo "target_sorry_ceiling=$target_sorry_ceiling"
    echo "relocation_rule=fail_if_sorry_count_increases"
  } >"$relocation_log"

  post_deep_digest="$(file_digest "$DEEP_BLOCKERS_FILE")"
  mandatory_deep_edit_status="pass"
  if [[ "$pre_deep_digest" == "$post_deep_digest" ]]; then
    mandatory_deep_edit_status="fail"
  fi
  {
    echo "deep_file=$DEEP_BLOCKERS_FILE"
    echo "pre_digest=$pre_deep_digest"
    echo "post_digest=$post_deep_digest"
  } >"$mandatory_deep_edit_log"

  session_contract_marker_hits=0
  if rg -q "MICRO_GOAL:" "$construct_log"; then session_contract_marker_hits=$((session_contract_marker_hits + 1)); fi
  if rg -q "PROVED_LEMMAS:" "$construct_log"; then session_contract_marker_hits=$((session_contract_marker_hits + 1)); fi
  if rg -q "LEAF_USAGE:" "$construct_log"; then session_contract_marker_hits=$((session_contract_marker_hits + 1)); fi
  if rg -q "BLOCKER_NEXT:" "$construct_log"; then session_contract_marker_hits=$((session_contract_marker_hits + 1)); fi
  if rg -q "CLOSURE_PLAN_STEP:" "$construct_log"; then session_contract_marker_hits=$((session_contract_marker_hits + 1)); fi
  session_contract_status="fail"
  if (( session_contract_marker_hits >= 5 )); then
    session_contract_status="pass"
  fi
  {
    echo "required_markers=5"
    echo "marker_hits=$session_contract_marker_hits"
  } >"$session_contract_log"

  active_leaf_step_lemma_count_post="$(
    count_active_leaf_step_lemmas "$DEEP_BLOCKERS_FILE" "$active_leaf_step_prefix"
  )"
  active_leaf_step_usage_post="$(
    count_active_leaf_step_usage "$DEEP_BLOCKERS_FILE" "$active_leaf_decl" "$active_leaf_step_prefix"
  )"
  active_leaf_step_delta=0
  active_leaf_step_delta_status="fail"
  if [[ "$active_leaf_name" != "none" ]] &&
     (( active_leaf_step_lemma_count_post > active_leaf_step_lemma_count_start )) &&
     (( active_leaf_step_usage_post > active_leaf_step_usage_start )); then
    active_leaf_step_delta=1
    active_leaf_step_delta_status="pass"
  fi
  {
    echo "active_leaf_name=$active_leaf_name"
    echo "active_leaf_decl=$active_leaf_decl"
    echo "active_leaf_step_prefix=$active_leaf_step_prefix"
    echo "active_leaf_session_count=$active_leaf_session_count"
    echo "active_leaf_grace_sessions=$ACTIVE_LEAF_GRACE_SESSIONS"
    echo "active_leaf_deadline_sessions=$ACTIVE_LEAF_DEADLINE_SESSIONS"
    echo "active_leaf_post_grace=$active_leaf_post_grace"
    echo "active_leaf_step_lemma_count_start=$active_leaf_step_lemma_count_start"
    echo "active_leaf_step_lemma_count_post=$active_leaf_step_lemma_count_post"
    echo "active_leaf_step_usage_start=$active_leaf_step_usage_start"
    echo "active_leaf_step_usage_post=$active_leaf_step_usage_post"
    echo "active_leaf_closed_this_session=$active_leaf_closed_this_session"
    echo "milestone_status=$milestone_status"
    echo "active_leaf_step_delta=$active_leaf_step_delta"
  } >"$active_leaf_step_log"

  gate_pass_count=0
  [[ "$target_status" == "pass" ]] && gate_pass_count=$((gate_pass_count + 1))
  [[ "$anti_status" == "pass" ]] && gate_pass_count=$((gate_pass_count + 1))
  [[ "$endpoint_status" == "pass" ]] && gate_pass_count=$((gate_pass_count + 1))

  post_snapshot="$(snapshot_b7_chain)"
  b7_artifacts_updated=0
  if [[ "$pre_snapshot" != "$post_snapshot" ]]; then
    b7_artifacts_updated=1
  fi

  best_leaf_delta=0
  if (( deep_leaf_sorry_count < best_deep_leaf_sorry_count )); then
    best_leaf_delta=1
  fi

  regression_detected=0
  if (( best_session_index > 0 )) && (( deep_leaf_sorry_count > best_deep_leaf_sorry_count )); then
    regression_detected=1
  fi

  real_progress_status="fail"
  real_progress_reasons=()

  if [[ "$REAL_PROGRESS_MODE" == "leaf_milestone_closure_v1" ]]; then
    if [[ "$construct_status" == "pass" ]] &&
       [[ "$build_status" == "pass" ]] &&
       [[ "$no_exfalso_status" == "pass" ]] &&
       [[ "$no_axiom_status" == "pass" ]] &&
       [[ "$no_sorry_relocation_status" == "pass" ]]; then
      if (( session_leaf_delta == 1 )); then
        real_progress_status="pass"
        real_progress_reasons+=("leaf_closed_this_session")
        real_progress_reasons+=("targeted_build_passed")
        real_progress_reasons+=("safety_gates_preserved")
      elif [[ "$active_leaf_name" != "none" ]] &&
           (( active_leaf_session_count <= ACTIVE_LEAF_GRACE_SESSIONS )) &&
           (( active_leaf_step_delta == 1 )) &&
           [[ "$mandatory_deep_edit_status" == "pass" ]] &&
           [[ "$session_contract_status" == "pass" ]]; then
        real_progress_status="pass"
        real_progress_reasons+=("active_leaf_step_delta_within_grace")
        real_progress_reasons+=("mandatory_deep_edit")
        real_progress_reasons+=("session_contract_satisfied")
        real_progress_reasons+=("targeted_build_passed")
        real_progress_reasons+=("safety_gates_preserved")
      elif [[ "$active_leaf_name" != "none" ]] &&
           (( active_leaf_session_count > ACTIVE_LEAF_GRACE_SESSIONS )) &&
           (( active_leaf_step_delta == 1 )); then
        real_progress_reasons+=("active_leaf_step_delta_post_grace_ignored")
      fi
    fi
  elif [[ "$REAL_PROGRESS_MODE" == "leaf_delta_build" ]]; then
    if (( session_leaf_delta == 1 )) &&
       [[ "$construct_status" == "pass" ]] &&
       [[ "$build_status" == "pass" ]] &&
       [[ "$no_exfalso_status" == "pass" ]] &&
       [[ "$no_axiom_status" == "pass" ]] &&
       [[ "$no_sorry_relocation_status" == "pass" ]]; then
      real_progress_status="pass"
      real_progress_reasons+=("leaf_sorry_count_decreased")
      real_progress_reasons+=("targeted_build_passed")
      real_progress_reasons+=("safety_gates_preserved")
    fi
  fi

  if (( regression_detected == 1 )); then
    real_progress_reasons+=("regression_detected")
  fi

  if [[ "$real_progress_status" == "pass" ]]; then
    stale_sessions_real_progress=0
  else
    stale_sessions_real_progress=$((stale_sessions_real_progress + 1))
  fi

  if [[ "$mandatory_deep_edit_status" == "pass" ]]; then
    stale_sessions_mandatory_deep_edit=0
  else
    stale_sessions_mandatory_deep_edit=$((stale_sessions_mandatory_deep_edit + 1))
  fi

  next_blocker="none"
  milestone_stop_triggered=0
  if [[ "$construct_status" != "pass" ]]; then
    if (( construct_timed_out == 1 )); then
      next_blocker="construction command timed out"
    else
      next_blocker="construction command failed"
    fi
  elif [[ "$milestone_status" == "missed" ]] && [[ "$STOP_ON_LEAF_MILESTONE_MISS" == "1" ]]; then
    next_blocker="active leaf milestone missed (${active_leaf_name} session=${active_leaf_session_count} deadline=${ACTIVE_LEAF_DEADLINE_SESSIONS})"
    milestone_stop_triggered=1
  elif [[ "$mandatory_deep_edit_status" != "pass" ]]; then
    next_blocker="mandatory deep-leaf edit missing in DeepBlockersResolved"
  elif [[ "$session_contract_status" != "pass" ]]; then
    next_blocker="session contract markers missing in construct output"
  elif [[ "$build_status" != "pass" ]]; then
    next_blocker="targeted build failure"
  elif (( regression_detected == 1 )); then
    next_blocker="deep-leaf regression detected versus best-known state"
  elif [[ "$deep_leaf_status" != "pass" ]]; then
    next_blocker="deep leaf sorries remain in DeepBlockersResolved"
  elif [[ "$no_exfalso_status" != "pass" ]]; then
    next_blocker="ex-falso path still present in B7 closure"
  elif [[ "$no_axiom_status" != "pass" ]]; then
    next_blocker="new axiom introduced in B7 chain files"
  elif [[ "$no_sorry_relocation_status" != "pass" ]]; then
    next_blocker="sorry relocation gate failed in B7 chain files"
  elif [[ "$target_status" != "pass" ]]; then
    next_blocker="target coeff-control gate unresolved"
  elif [[ "$anti_status" != "pass" ]]; then
    next_blocker="anti coeff-control gate unresolved"
  elif [[ "$endpoint_status" != "pass" ]]; then
    next_blocker="rhPiWitness_proved endpoint gate unresolved"
  elif [[ "$real_progress_status" != "pass" ]]; then
    next_blocker="no real measurable progress"
  fi

  success=0
  if [[ "$build_status" == "pass" &&
        "$deep_leaf_status" == "pass" &&
        "$no_exfalso_status" == "pass" &&
        "$no_axiom_status" == "pass" &&
        "$no_sorry_relocation_status" == "pass" &&
        "$target_status" == "pass" &&
        "$anti_status" == "pass" &&
        "$endpoint_status" == "pass" ]]; then
    success=1
  fi

  next_action="relaunch"
  if (( success == 1 )); then
    next_action="success"
  elif (( milestone_stop_triggered == 1 )); then
    next_action="stop_leaf_milestone"
  elif (( stale_sessions_mandatory_deep_edit >= MAX_MANDATORY_DEEP_EDIT_FAILURES )); then
    next_action="stop_deep_edit_stall"
  elif (( stale_sessions_real_progress >= MAX_STALE_SESSIONS )); then
    if [[ "$active_leaf_name" != "none" ]] &&
       (( active_leaf_still_open == 1 )) &&
       [[ "$STOP_ON_LEAF_MILESTONE_MISS" == "1" ]] &&
       (( active_leaf_session_count < ACTIVE_LEAF_DEADLINE_SESSIONS )); then
      next_action="relaunch"
    else
      next_action="stop_stale"
    fi
  elif (( MAX_SESSIONS > 0 && session_index >= MAX_SESSIONS )); then
    next_action="stop_max_sessions"
  elif (( elapsed >= MAX_WALLCLOCK_SECS )); then
    next_action="stop_wallclock"
  elif [[ "$RELAUNCH_ON_NON_CLOSURE" != "1" ]]; then
    next_action="stop_non_closure"
  fi

  progress_reasons_csv=""
  if (( ${#real_progress_reasons[@]} > 0 )); then
    progress_reasons_csv="$(IFS=, ; echo "${real_progress_reasons[*]}")"
  fi

  session_end="$(date +%s)"
  session_duration="$((session_end - session_start))"

  REPORT_SCHEMA_VERSION="2" \
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
  REPORT_DEEP_LEAF_STATUS="$deep_leaf_status" \
  REPORT_DEEP_TRUNCATED_HAS_SORRY="$deep_trunc_has_sorry" \
  REPORT_DEEP_TARGET_HAS_SORRY="$deep_target_has_sorry" \
  REPORT_DEEP_ANTITARGET_HAS_SORRY="$deep_antitarget_has_sorry" \
  REPORT_DEEP_SORRY_COUNT="$deep_leaf_sorry_count" \
  REPORT_NO_EXFALSO_STATUS="$no_exfalso_status" \
  REPORT_NO_AXIOM_STATUS="$no_axiom_status" \
  REPORT_NO_SORRY_RELOCATION_STATUS="$no_sorry_relocation_status" \
  REPORT_ACTIVE_LEAF_STEP_DELTA_STATUS="$active_leaf_step_delta_status" \
  REPORT_MANDATORY_DEEP_EDIT_STATUS="$mandatory_deep_edit_status" \
  REPORT_SESSION_CONTRACT_STATUS="$session_contract_status" \
  REPORT_GATE_PASS_COUNT="$gate_pass_count" \
  REPORT_TARGETED_BUILD_PASS="$targeted_build_pass" \
  REPORT_B7_ARTIFACTS_UPDATED="$b7_artifacts_updated" \
  REPORT_AXIOM_COUNT_START="$axiom_count_start" \
  REPORT_AXIOM_COUNT_POST="$axiom_count_post" \
  REPORT_SORRY_COUNT_START="$sorry_count_start" \
  REPORT_SORRY_COUNT_POST="$sorry_count_post" \
  REPORT_MIN_SORRY_REDUCTION_REQUIRED="$required_sorry_reduction" \
  REPORT_ACTIVE_LEAF_NAME="$active_leaf_name" \
  REPORT_ACTIVE_LEAF_DECL="$active_leaf_decl" \
  REPORT_ACTIVE_LEAF_STEP_PREFIX="$active_leaf_step_prefix" \
  REPORT_ACTIVE_LEAF_SESSION_COUNT="$active_leaf_session_count" \
  REPORT_ACTIVE_LEAF_GRACE_SESSIONS="$ACTIVE_LEAF_GRACE_SESSIONS" \
  REPORT_ACTIVE_LEAF_DEADLINE_SESSIONS="$ACTIVE_LEAF_DEADLINE_SESSIONS" \
  REPORT_ACTIVE_LEAF_POST_GRACE="$active_leaf_post_grace" \
  REPORT_ACTIVE_LEAF_STEP_LEMMA_COUNT_START="$active_leaf_step_lemma_count_start" \
  REPORT_ACTIVE_LEAF_STEP_LEMMA_COUNT_POST="$active_leaf_step_lemma_count_post" \
  REPORT_ACTIVE_LEAF_STEP_USAGE_START="$active_leaf_step_usage_start" \
  REPORT_ACTIVE_LEAF_STEP_USAGE_POST="$active_leaf_step_usage_post" \
  REPORT_ACTIVE_LEAF_CLOSED_THIS_SESSION="$active_leaf_closed_this_session" \
  REPORT_SESSION_CONTRACT_MARKER_HITS="$session_contract_marker_hits" \
  REPORT_STALE_MANDATORY_DEEP_EDIT="$stale_sessions_mandatory_deep_edit" \
  REPORT_MAX_MANDATORY_DEEP_EDIT_FAILURES="$MAX_MANDATORY_DEEP_EDIT_FAILURES" \
  REPORT_MILESTONE_STATUS="$milestone_status" \
  REPORT_MILESTONE_STOP_TRIGGERED="$milestone_stop_triggered" \
  REPORT_STOP_ON_LEAF_MILESTONE_MISS="$STOP_ON_LEAF_MILESTONE_MISS" \
  REPORT_REAL_PROGRESS_MODE="$REAL_PROGRESS_MODE" \
  REPORT_REAL_PROGRESS_STATUS="$real_progress_status" \
  REPORT_REAL_PROGRESS_REASONS="$progress_reasons_csv" \
  REPORT_PROGRESS_STATUS="$real_progress_status" \
  REPORT_PROGRESS_REASONS="$progress_reasons_csv" \
  REPORT_STALE_REAL_PROGRESS="$stale_sessions_real_progress" \
  REPORT_STALE_SESSIONS="$stale_sessions_real_progress" \
  REPORT_MAX_STALE_SESSIONS="$MAX_STALE_SESSIONS" \
  REPORT_LEAF_DELTA="$session_leaf_delta" \
  REPORT_ACTIVE_LEAF_STEP_DELTA="$active_leaf_step_delta" \
  REPORT_REGRESSION_DETECTED="$regression_detected" \
  REPORT_BEST_SESSION_INDEX="$best_session_index" \
  REPORT_BEST_DEEP_SORRY="$best_deep_leaf_sorry_count" \
  REPORT_BEST_SNAPSHOT_DIR="$best_snapshot_dir" \
  REPORT_NEXT_BLOCKER="$next_blocker" \
  REPORT_NEXT_ACTION="$next_action" \
  REPORT_PROMPT_LOG="$prompt_log" \
  REPORT_CONSTRUCT_LOG="$construct_log" \
  REPORT_BUILD_LOG="$build_log" \
  REPORT_TARGET_LOG="$target_log" \
  REPORT_ANTI_LOG="$anti_log" \
  REPORT_ENDPOINT_LOG="$endpoint_log" \
  REPORT_DEEP_LEAF_LOG="$deep_leaf_log" \
  REPORT_EXFALSO_LOG="$exfalso_log" \
  REPORT_AXIOM_LOG="$axiom_log" \
  REPORT_RELOCATION_LOG="$relocation_log" \
  REPORT_ACTIVE_LEAF_STEP_LOG="$active_leaf_step_log" \
  REPORT_MANDATORY_DEEP_EDIT_LOG="$mandatory_deep_edit_log" \
  REPORT_SESSION_CONTRACT_LOG="$session_contract_log" \
  write_session_json "$report_json"

  if [[ "$real_progress_status" == "pass" ]]; then
    snapshot_best_state "$session_index" "$ts" "$deep_leaf_sorry_count" "$build_status" "$report_json"
  fi

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
  echo "gate_deep_leaf_no_sorry: ${deep_leaf_status}"
  echo "active_leaf_session: ${active_leaf_name} (${active_leaf_session_count}/${ACTIVE_LEAF_DEADLINE_SESSIONS}, grace=${ACTIVE_LEAF_GRACE_SESSIONS}, post_grace=${active_leaf_post_grace})"
  echo "milestone_status: ${milestone_status}"
  echo "gate_active_leaf_step_delta: ${active_leaf_step_delta_status} (leaf=${active_leaf_name}, prefix=${active_leaf_step_prefix}, lemma_start=${active_leaf_step_lemma_count_start}, lemma_post=${active_leaf_step_lemma_count_post}, usage_start=${active_leaf_step_usage_start}, usage_post=${active_leaf_step_usage_post})"
  echo "gate_mandatory_deep_edit: ${mandatory_deep_edit_status}"
  echo "gate_session_contract: ${session_contract_status} (marker_hits=${session_contract_marker_hits}/5)"
  echo "gate_no_exfalso_in_b7_path: ${no_exfalso_status} (count=${exfalso_count})"
  echo "gate_no_axiom_introduced: ${no_axiom_status} (start=${axiom_count_start}, post=${axiom_count_post})"
  echo "gate_no_sorry_relocation: ${no_sorry_relocation_status} (start=${sorry_count_start}, post=${sorry_count_post}, required_reduction=${required_sorry_reduction})"
  echo "deep_leaf_sorry_count: ${deep_leaf_sorry_count} (target=${deep_trunc_has_sorry}, antitarget=${deep_target_has_sorry}, coeff=${deep_antitarget_has_sorry})"
  echo "gate_pass_count: ${gate_pass_count}/3"
  echo "b7_artifacts_updated: ${b7_artifacts_updated}"
  echo "real_progress: ${real_progress_status}"
  echo "real_progress_reasons: ${real_progress_reasons[*]:-none}"
  echo "leaf_delta: ${session_leaf_delta}"
  echo "active_leaf_step_delta: ${active_leaf_step_delta}"
  echo "active_leaf_closed_this_session: ${active_leaf_closed_this_session}"
  echo "regression_detected: ${regression_detected}"
  echo "best_deep_leaf_sorry_count: ${best_deep_leaf_sorry_count} (session=${best_session_index})"
  echo "stale_sessions_real_progress: ${stale_sessions_real_progress}/${MAX_STALE_SESSIONS}"
  echo "stale_sessions_mandatory_deep_edit: ${stale_sessions_mandatory_deep_edit}/${MAX_MANDATORY_DEEP_EDIT_FAILURES}"
  echo "next_blocker: ${next_blocker}"
  echo "next_action: ${next_action}"
  echo "session_report_json: ${report_json}"

  if (( success == 1 )); then
    echo "Ralph B7 deep-leaf loop complete: all three upstream deep leaves closed and all closure gates passed."
    exit 0
  fi

  if [[ "$next_action" == "stop_stale" ]]; then
    if [[ "$ESCALATION_ON_STALL" == "1" ]]; then
      write_escalation_bundle "no_real_progress"
      echo "Escalation bundle: $RUN_DIR/escalation_summary.md"
      echo "Escalation bundle JSON: $RUN_DIR/escalation_summary.json"
    fi
    echo "Stopping: no real measurable progress for ${stale_sessions_real_progress} consecutive sessions."
    exit 3
  fi
  if [[ "$next_action" == "stop_leaf_milestone" ]]; then
    if [[ "$ESCALATION_ON_STALL" == "1" ]]; then
      write_escalation_bundle "leaf_milestone_missed_${active_leaf_name}"
      echo "Escalation bundle: $RUN_DIR/escalation_summary.md"
      echo "Escalation bundle JSON: $RUN_DIR/escalation_summary.json"
    fi
    echo "Stopping: active leaf milestone missed (${active_leaf_name}, session_count=${active_leaf_session_count}, deadline=${ACTIVE_LEAF_DEADLINE_SESSIONS})."
    exit 8
  fi
  if [[ "$next_action" == "stop_deep_edit_stall" ]]; then
    if [[ "$ESCALATION_ON_STALL" == "1" ]]; then
      write_escalation_bundle "mandatory_deep_edit_stall"
      echo "Escalation bundle: $RUN_DIR/escalation_summary.md"
      echo "Escalation bundle JSON: $RUN_DIR/escalation_summary.json"
    fi
    echo "Stopping: missing mandatory DeepBlockersResolved edits for ${stale_sessions_mandatory_deep_edit} consecutive sessions."
    exit 7
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
