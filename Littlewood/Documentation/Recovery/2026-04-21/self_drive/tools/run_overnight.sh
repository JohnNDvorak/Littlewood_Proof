#!/usr/bin/env bash
set -euo pipefail

REPO="/Users/john.n.dvorak/Projects/Littlewood_Proof"
RECOVERY="$REPO/Littlewood/Documentation/Recovery/2026-04-21"
SELF="$RECOVERY/self_drive"
LEAN_FILE="$REPO/Littlewood/Aristotle/Standalone/AtkinsonFormula.lean"
PRELUDE_DIR="$SELF/preflight"
RAW_DIR="$SELF/raw"
METRICS_DIR="$SELF/metrics"
PROMPT_DIR="$SELF/aristotle/prompts"
RESULTS_DIR="$SELF/aristotle/results"
SNAPSHOT_DIR="$SELF/aristotle/snapshots"
LOG_DIR="$SELF/logs"
TMP_DIR="${TMPDIR:-/tmp}"
STATE_FILE="$SELF/runtime_state.json"
JOBS_FILE="$SELF/aristotle/jobs.jsonl"
MAX_SECONDS="${MAX_SECONDS:-36000}"
POLL_SECONDS="${POLL_SECONDS:-1200}"
LEAN_TIMEOUT_SECONDS="${LEAN_TIMEOUT_SECONDS:-600}"
LAKE_TIMEOUT_SECONDS="${LAKE_TIMEOUT_SECONDS:-900}"
PUBLIC_PROBE_TIMEOUT_SECONDS="${PUBLIC_PROBE_TIMEOUT_SECONDS:-180}"
FULL_BUILD_TIMEOUT_SECONDS="${FULL_BUILD_TIMEOUT_SECONDS:-3600}"
MAX_ATTEMPTS_PER_PHASE="${MAX_ATTEMPTS_PER_PHASE:-3}"

mkdir -p \
  "$PRELUDE_DIR" \
  "$RAW_DIR" \
  "$METRICS_DIR" \
  "$PROMPT_DIR" \
  "$RESULTS_DIR" \
  "$SNAPSHOT_DIR" \
  "$LOG_DIR"

touch \
  "$SELF/latest.md" \
  "$SELF/handoff_latest.md" \
  "$JOBS_FILE" \
  "$METRICS_DIR/round_metrics.jsonl" \
  "$METRICS_DIR/route_ledger.jsonl" \
  "$METRICS_DIR/target_lineage.jsonl"

RUN_ID="$(date -u +%Y%m%dT%H%M%SZ)"
LOG_FILE="$LOG_DIR/run_${RUN_ID}.log"
exec > >(tee -a "$LOG_FILE") 2>&1

ts_utc() {
  date -u +%Y-%m-%dT%H:%M:%SZ
}

now_local() {
  date '+%Y-%m-%d %H:%M:%S %Z'
}

next_round() {
  find "$RAW_DIR" -maxdepth 1 -type f -name 'ROUND*.md' | wc -l | tr -d ' '
}

round_num() {
  local n
  n="$(next_round)"
  printf "%03d" $((n + 1))
}

theorem_line() {
  local name="$1"
  rg -n -m1 "$name" "$LEAN_FILE" | cut -d: -f1
}

append_jsonl() {
  local file="$1"
  local payload="$2"
  python3 - "$file" "$payload" <<'PY'
import json, sys
path, payload = sys.argv[1], sys.argv[2]
obj = json.loads(payload)
with open(path, "a", encoding="utf-8") as fh:
    fh.write(json.dumps(obj, sort_keys=True) + "\n")
PY
}

write_runtime_state() {
  local phase="$1"
  local target="$2"
  local job_id="$3"
  local job_status="$4"
  local attempts_public="$5"
  local attempts_cleanup="$6"
  local note="$7"
  python3 - "$STATE_FILE" <<PY
import json, pathlib
path = pathlib.Path("$STATE_FILE")
path.write_text(json.dumps({
  "updated_at": "$(ts_utc)",
  "run_id": "$RUN_ID",
  "phase": "$phase",
  "target": "$target",
  "job_id": "$job_id",
  "job_status": "$job_status",
  "attempts": {
    "public_leaf": int("$attempts_public"),
    "cleanup": int("$attempts_cleanup"),
  },
  "note": "$note",
}, indent=2, sort_keys=True) + "\n", encoding="utf-8")
PY
}

write_latest() {
  local status="$1"
  local live_target="$2"
  local action="$3"
  local job_line="$4"
  cat >"$SELF/latest.md" <<EOF
# Self-Drive Latest

- Status: $status
- Live target: $live_target
- Public leaf: \`AtkinsonShiftedInversePhaseCellPrefixBoundHyp\`
- Cleanup lane: \`atkinson_inversePhaseCorePrefix_bound_large_j\` then \`atkinson_largeShiftWeightedBoundarySum_bound\`
- Aristotle: $job_line
- Last action: $action
- Updated: $(now_local)
EOF
}

write_handoff() {
  local body="$1"
  {
    printf '%s\n\n' "# Self-Drive Handoff"
    printf '%b\n\n' "$body"
    printf '%s\n' "Updated: $(now_local)"
  } >"$SELF/handoff_latest.md"
}

record_round() {
  local round="$1"
  local slug="$2"
  local classification="$3"
  local status="$4"
  local target="$5"
  local notes="$6"
  local next_target="$7"
  local raw_file="$RAW_DIR/ROUND${round}_${slug}.md"
  cat >"$raw_file" <<EOF
# Round ${round}: ${slug}

Date: $(date -u +%Y-%m-%d)

## Target
$target

## Setup
Working only in \`Littlewood/Aristotle/Standalone/AtkinsonFormula.lean\` for tracked source changes.

## Banked Inputs
- Existing no-log packager ladder under \`AtkinsonShiftedInversePhaseCellPrefixBoundHyp\`
- Focused health checks: direct \`lean\` and focused \`lake build\`
- Canonical minimal-import invocation probes for ψ and π-li

## Work Performed
$notes

## Results
Classification: \`$classification\`

## Interpretation
$status

## Classification
$classification

## Next Target
$next_target
EOF

  append_jsonl "$METRICS_DIR/round_metrics.jsonl" "$(python3 - <<PY
import json
print(json.dumps({
  "round": int("$round"),
  "created_at": "$(ts_utc)",
  "object": "$target",
  "target_scale": "tracked overnight recovery",
  "classification": "$classification",
  "status": "$status",
  "observed": {},
  "next_target": "$next_target",
  "notes": "$notes".replace("\\n", " ")
}))
PY
)"
}

record_route() {
  local round="$1"
  local route="$2"
  local classification="$3"
  local gap="$4"
  local obstruction="$5"
  local replacement="$6"
  append_jsonl "$METRICS_DIR/route_ledger.jsonl" "$(python3 - <<PY
import json
print(json.dumps({
  "round": int("$round"),
  "route": "$route",
  "classification": "$classification",
  "scale_gap": "$gap",
  "obstruction": "$obstruction",
  "replacement_target": "$replacement",
  "notes": "$obstruction"
}))
PY
)"
}

record_lineage() {
  local round="$1"
  local prev="$2"
  local next="$3"
  local relation="$4"
  local notes="$5"
  append_jsonl "$METRICS_DIR/target_lineage.jsonl" "$(python3 - <<PY
import json
print(json.dumps({
  "round": int("$round"),
  "object": "$next",
  "from": "$prev",
  "relation": "$relation",
  "notes": "$notes"
}))
PY
)"
}

run_with_timeout() {
  local seconds="$1"
  local out="$2"
  shift 2
  python3 - "$seconds" "$out" "$@" <<'PY'
import os, signal, subprocess, sys

timeout = int(sys.argv[1])
out_path = sys.argv[2]
cmd = sys.argv[3:]

try:
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        start_new_session=True,
    )
    output, code = proc.communicate(timeout=timeout), None
    if isinstance(output, tuple):
        output, _ = output
    code = proc.returncode
except subprocess.TimeoutExpired as exc:
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except Exception:
        pass
    output = (exc.stdout or "") + f"\nTIMEOUT: command exceeded {timeout}s\n"
    code = 124

with open(out_path, "w", encoding="utf-8") as fh:
    fh.write(output)

sys.exit(code)
PY
}

lean_formula() {
  local out="$1"
  local lean_bin="$HOME/.elan/toolchains/leanprover--lean4---v4.27.0-rc1/bin/lean"
  local lean_path
  lean_path="$(printf '%s:' "$REPO"/.lake/packages/*/.lake/build/lib/lean "$REPO"/.lake/build/lib/lean)"
  lean_path="${lean_path%:}"
  (
    cd "$REPO"
    run_with_timeout \
      "$LEAN_TIMEOUT_SECONDS" \
      "$out" \
      env "LEAN_PATH=$lean_path" "$lean_bin" "Littlewood/Aristotle/Standalone/AtkinsonFormula.lean"
  )
}

lake_formula() {
  local out="$1"
  (
    cd "$REPO"
    run_with_timeout \
      "$LAKE_TIMEOUT_SECONDS" \
      "$out" \
      lake build Littlewood.Aristotle.Standalone.AtkinsonFormula
  )
}

full_build() {
  local out="$1"
  (
    cd "$REPO"
    run_with_timeout \
      "$FULL_BUILD_TIMEOUT_SECONDS" \
      "$out" \
      lake build
  )
}

probe_file() {
  local code="$1"
  local out="$2"
  local tmp_file
  tmp_file="$(mktemp "$TMP_DIR/littlewood_probe.XXXXXX")"
  mv "$tmp_file" "$tmp_file.lean"
  tmp_file="$tmp_file.lean"
  printf '%s\n' "$code" >"$tmp_file"
  (
    cd "$REPO"
    run_with_timeout "$PUBLIC_PROBE_TIMEOUT_SECONDS" "$out" lake env lean "$tmp_file"
  )
  local code_exit=$?
  rm -f "$tmp_file"
  return "$code_exit"
}

probe_leaf_instance() {
  local out="$1"
  probe_file "import Littlewood.Aristotle.Standalone.AtkinsonFormula
open Aristotle.Standalone.AtkinsonFormula

example : AtkinsonShiftedInversePhaseCellPrefixBoundHyp := by
  infer_instance" "$out"
}

probe_public_psi() {
  local out="$1"
  probe_file "import Littlewood.Main.LittlewoodPsi

example := Littlewood.littlewood_psi" "$out"
}

probe_public_pi() {
  local out="$1"
  probe_file "import Littlewood.Main.LittlewoodPi

example := LittlewoodPi.littlewood_pi_li" "$out"
}

extract_missing_class() {
  local log_file="$1"
  python3 - "$log_file" <<'PY'
import pathlib, re, sys
text = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
m = re.search(r'failed to synthesize instance of type class\s+([A-Za-z0-9_.]+)', text)
print(m.group(1) if m else "")
PY
}

count_sorries() {
  rg -n "sorry" "$LEAN_FILE" | wc -l | tr -d ' '
}

make_snapshot() {
  local dest="$1"
  rm -rf "$dest"
  mkdir -p "$dest"
  rsync -a \
    --exclude='.git/' \
    --exclude='.lake/build/' \
    --exclude='build/' \
    --exclude='.recovery_artifacts/' \
    --exclude='Littlewood/Documentation/Recovery/2026-04-21/self_drive/' \
    --exclude='Littlewood/Bridge/ContourRemainderMultLeaf.lean' \
    --exclude='Littlewood/ZetaZeros/PairedFarZeroCancellationBridge.lean' \
    --exclude='Littlewood/ZetaZeros/ZeroAvoidingHeight.lean' \
    "$REPO/" "$dest/Littlewood_Proof/"
}

phase_target_text() {
  local phase="$1"
  case "$phase" in
    public_leaf)
      printf '%s' "Close \`AtkinsonShiftedInversePhaseCellPrefixBoundHyp\` by resolving the current large-\`j\` common-block remainder route and the raw \`j = 1,2\` correction-prefix patches."
      ;;
    cleanup)
      printf '%s' "Close the cleanup lane in \`AtkinsonFormula.lean\`: \`atkinson_inversePhaseCorePrefix_bound_large_j\` and then \`atkinson_largeShiftWeightedBoundarySum_bound\`."
      ;;
    next_public_blocker)
      printf '%s' "The inverse-phase-cell public leaf is closed; the next public blocker is now live."
      ;;
    done)
      printf '%s' "No remaining AtkinsonFormula public or cleanup blocker detected."
      ;;
    *)
      printf '%s' "Unknown phase"
      ;;
  esac
}

make_aristotle_prompt() {
  local phase="$1"
  local dest="$2"
  local leaf_ln cleanup_ln inst_ln
  leaf_ln="$(theorem_line 'AtkinsonShiftedInversePhaseCellPrefixBoundHyp')"
  inst_ln="$(theorem_line 'atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_j3_and_correction_j1_j2')"
  cleanup_ln="$(theorem_line 'atkinson_inversePhaseCorePrefix_bound_large_j')"
  case "$phase" in
    public_leaf)
      cat >"$dest" <<EOF
Work only in \`Littlewood/Aristotle/Standalone/AtkinsonFormula.lean\`.

Current public leaf:
- \`AtkinsonShiftedInversePhaseCellPrefixBoundHyp\` near line ${leaf_ln}

Current local packager:
- \`atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_j3_and_correction_j1_j2\` near line ${inst_ln}

Required task:
- close the inverse-phase-cell public leaf
- if you cannot close it in one shot, add the smallest exact helper theorem(s) needed and wire them through locally in this file

Current live large-j route:
- the common block-parameter remainder route feeding
  \`atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_commonBlockParamTargetK_remainder\`

Current finite-shift route:
- raw \`j = 1\` correction-prefix bound
- raw \`j = 2\` correction-prefix bound

Forbidden routes:
- no CloudDocs
- no imports from \`ContourRemainderMultLeaf\`, \`PairedFarZeroCancellationBridge\`, or \`ZeroAvoidingHeight\`
- no global correction-prefix bridge restoring the old public boundary
- no circular use of \`AtkinsonLargeShiftPrefixBoundHyp\`
- do not switch to the cleanup lane unless the public leaf is already closed

Acceptance tests after integrating your result:
1. direct \`lean Littlewood/Aristotle/Standalone/AtkinsonFormula.lean\`
2. \`lake build Littlewood.Aristotle.Standalone.AtkinsonFormula\`
3. \`example : Aristotle.Standalone.AtkinsonFormula.AtkinsonShiftedInversePhaseCellPrefixBoundHyp := by infer_instance\`
4. if possible, advance the strict minimal-import invocation path beyond the current Atkinson blocker

Return exact code changes only. Do not return a memo instead of a proof attempt.
EOF
      ;;
    cleanup)
      cat >"$dest" <<EOF
Work only in \`Littlewood/Aristotle/Standalone/AtkinsonFormula.lean\`.

Cleanup target:
- \`atkinson_inversePhaseCorePrefix_bound_large_j\` near line ${cleanup_ln}
- then \`atkinson_largeShiftWeightedBoundarySum_bound\`

Goal:
- eliminate the remaining literal \`sorry\` in the large-shift cleanup lane
- preserve the already-validated public inverse-phase-cell route

Forbidden routes:
- no CloudDocs
- no imports from \`ContourRemainderMultLeaf\`, \`PairedFarZeroCancellationBridge\`, or \`ZeroAvoidingHeight\`
- no circular use of \`AtkinsonLargeShiftPrefixBoundHyp\`
- do not widen the public boundary again

Acceptance tests after integrating your result:
1. direct \`lean Littlewood/Aristotle/Standalone/AtkinsonFormula.lean\`
2. \`lake build Littlewood.Aristotle.Standalone.AtkinsonFormula\`
3. \`rg -n "sorry" Littlewood/Aristotle/Standalone/AtkinsonFormula.lean\` should print nothing

Return exact code changes only.
EOF
      ;;
    *)
      printf 'No Aristotle prompt for phase %s\n' "$phase" >"$dest"
      ;;
  esac
}

submit_aristotle() {
  local prompt_file="$1"
  local snapshot_root="$2"
  local submit_log="$3"
  local prompt
  prompt="$(<"$prompt_file")"
  aristotle submit --project-dir "$snapshot_root/Littlewood_Proof" "$prompt" >"$submit_log" 2>&1
}

poll_status() {
  local project_id="$1"
  local out_file="$2"
  aristotle list --limit 100 >"$out_file" 2>&1 || true
  awk -v id="$project_id" '$1==id {print $2}' "$out_file" | head -n 1
}

download_result() {
  local project_id="$1"
  local dest="$2"
  mkdir -p "$dest"
  local archive="$dest/result_download"
  aristotle result "$project_id" --destination "$archive" >"$dest/result.log" 2>&1 || return 1
  if [[ -f "$archive" ]]; then
    mv "$archive" "$archive.zip" 2>/dev/null || true
    if [[ -f "$archive.zip" ]]; then
      unzip -oq "$archive.zip" -d "$dest/unpacked" >/dev/null 2>&1 || true
    fi
  fi
}

find_candidate_formula() {
  local result_dir="$1"
  find "$result_dir" -type f -path '*Littlewood/Aristotle/Standalone/AtkinsonFormula.lean' | head -n 1
}

validate_repo_phase() {
  local out_dir="$1"
  mkdir -p "$out_dir"
  local phase blocker_psi blocker_pi

  if lean_formula "$out_dir/direct_lean.log"; then
    echo 0 >"$out_dir/direct_lean.exit"
  else
    echo $? >"$out_dir/direct_lean.exit"
    echo "file_health_broken"
    return
  fi

  if lake_formula "$out_dir/lake_formula.log"; then
    echo 0 >"$out_dir/lake_formula.exit"
  else
    echo $? >"$out_dir/lake_formula.exit"
    echo "file_health_broken"
    return
  fi

  if probe_leaf_instance "$out_dir/leaf_instance.log"; then
    echo 0 >"$out_dir/leaf_instance.exit"
  else
    echo $? >"$out_dir/leaf_instance.exit"
    echo "public_leaf"
    return
  fi

  if probe_public_psi "$out_dir/public_psi.log"; then
    echo 0 >"$out_dir/public_psi.exit"
  else
    echo $? >"$out_dir/public_psi.exit"
  fi
  if probe_public_pi "$out_dir/public_pi.log"; then
    echo 0 >"$out_dir/public_pi.exit"
  else
    echo $? >"$out_dir/public_pi.exit"
  fi

  blocker_psi="$(extract_missing_class "$out_dir/public_psi.log")"
  blocker_pi="$(extract_missing_class "$out_dir/public_pi.log")"
  printf '%s\n' "$blocker_psi" >"$out_dir/public_psi.blocker"
  printf '%s\n' "$blocker_pi" >"$out_dir/public_pi.blocker"

  if [[ "$(cat "$out_dir/public_psi.exit")" != "0" || "$(cat "$out_dir/public_pi.exit")" != "0" ]]; then
    echo "next_public_blocker"
    return
  fi

  if rg -n "sorry" "$LEAN_FILE" >"$out_dir/sorries.txt"; then
    echo "cleanup"
  else
    echo "done"
  fi
}

preflight() {
  local out_dir="$PRELUDE_DIR/$RUN_ID"
  mkdir -p "$out_dir"
  git -C "$REPO" branch --show-current >"$out_dir/branch.txt"
  git -C "$REPO" status --short >"$out_dir/status.txt"
  git -C "$REPO" diff -- Littlewood/Aristotle/Standalone/AtkinsonFormula.lean >"$out_dir/AtkinsonFormula.diff" || true
  PREFLIGHT_PHASE="$(validate_repo_phase "$out_dir")"
  PREFLIGHT_OUT_DIR="$out_dir"
}

refresh_frontier_ledger() {
  local phase="$1"
  local action="$2"
  local round
  round="$(round_num)"
  record_round \
    "$round" \
    "frontier_refresh" \
    "CONDITIONAL_REDUCTION" \
    "Refreshed overnight runner frontier against the live repo state." \
    "$(phase_target_text "$phase")" \
    "Recomputed file health, instance synth, canonical public probes, and the cleanup-lane \`sorry\` count. Old self-drive target labels are now superseded by the current phase." \
    "$(phase_target_text "$phase")"
  record_lineage \
    "$round" \
    "stale_self_drive_frontier" \
    "$(phase_target_text "$phase")" \
    "live repo refresh" \
    "The overnight runner now keys off the current repo phase instead of stale target text in latest.md/handoff_latest.md."
  write_latest "running" "$(phase_target_text "$phase")" "$action" "no live Aristotle job"
}

submit_phase_job() {
  local phase="$1"
  local prompt_file="$2"
  local snapshot_dir="$3"
  local submit_log="$4"
  make_aristotle_prompt "$phase" "$prompt_file"
  make_snapshot "$snapshot_dir"
  submit_aristotle "$prompt_file" "$snapshot_dir" "$submit_log"
  grep -Eo '[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' "$submit_log" | head -n 1 || true
}

record_job_event() {
  local project_id="$1"
  local phase="$2"
  local status="$3"
  local prompt_file="$4"
  local snapshot_dir="$5"
  append_jsonl "$JOBS_FILE" "$(python3 - <<PY
import json
print(json.dumps({
  "created_at": "$(ts_utc)",
  "run_id": "$RUN_ID",
  "project_id": "$project_id",
  "phase": "$phase",
  "status": "$status",
  "prompt_file": "$prompt_file",
  "snapshot_dir": "$snapshot_dir"
}))
PY
)"
}

cancel_job() {
  local project_id="$1"
  aristotle cancel "$project_id" >/dev/null 2>&1 || true
}

integrate_candidate_formula() {
  local candidate="$1"
  local stage_dir="$2"
  local backup="$stage_dir/AtkinsonFormula.backup"
  cp "$LEAN_FILE" "$backup"
  cp "$candidate" "$LEAN_FILE"
  if ! lean_formula "$stage_dir/direct_lean.log"; then
    cp "$backup" "$LEAN_FILE"
    return 1
  fi
  if ! lake_formula "$stage_dir/lake_formula.log"; then
    cp "$backup" "$LEAN_FILE"
    return 1
  fi
  return 0
}

harvest_terminal_job() {
  local project_id="$1"
  local phase="$2"
  local status="$3"
  local result_dir="$4"
  local round candidate phase_after stage_dir blocker_psi blocker_pi

  download_result "$project_id" "$result_dir" || true
  candidate="$(find_candidate_formula "$result_dir")"
  stage_dir="$LOG_DIR/harvest_${RUN_ID}_${project_id}"
  mkdir -p "$stage_dir"
  round="$(round_num)"

  if [[ -z "$candidate" ]]; then
    record_round \
      "$round" \
      "aristotle_terminal_no_candidate" \
      "FAILED_ROUTE" \
      "Aristotle returned a terminal result without a harvestable \`AtkinsonFormula.lean\`." \
      "$(phase_target_text "$phase")" \
      "Terminal status: \`$status\`. Result directory: \`$result_dir\`." \
      "$(phase_target_text "$phase")"
    record_route \
      "$round" \
      "aristotle_${phase}_no_candidate" \
      "FAILED_ROUTE" \
      "no candidate file" \
      "No \`AtkinsonFormula.lean\` was found in the extracted Aristotle result tree." \
      "$(phase_target_text "$phase")"
    return
  fi

  if cmp -s "$candidate" "$LEAN_FILE"; then
    record_round \
      "$round" \
      "aristotle_terminal_no_change" \
      "FAILED_ROUTE" \
      "Aristotle returned an \`AtkinsonFormula.lean\` identical to the current repo file." \
      "$(phase_target_text "$phase")" \
      "Terminal status: \`$status\`. Candidate file matched the current repo exactly." \
      "$(phase_target_text "$phase")"
    record_route \
      "$round" \
      "aristotle_${phase}_no_change" \
      "FAILED_ROUTE" \
      "no change" \
      "Aristotle did not move the live file." \
      "$(phase_target_text "$phase")"
    return
  fi

  if ! integrate_candidate_formula "$candidate" "$stage_dir"; then
    record_round \
      "$round" \
      "aristotle_candidate_rejected" \
      "FAILED_ROUTE" \
      "Rejected Aristotle candidate because the local health checks failed after transplanting \`AtkinsonFormula.lean\`." \
      "$(phase_target_text "$phase")" \
      "Terminal status: \`$status\`. Candidate was reverted after failed direct \`lean\` or focused \`lake build\`." \
      "$(phase_target_text "$phase")"
    record_route \
      "$round" \
      "aristotle_${phase}_candidate_rejected" \
      "FAILED_ROUTE" \
      "compile failure" \
      "The transplanted candidate broke direct \`lean\` or focused \`lake build\`; the repo file was restored." \
      "$(phase_target_text "$phase")"
    return
  fi

  phase_after="$(validate_repo_phase "$stage_dir/post_harvest")"
  record_round \
    "$round" \
    "aristotle_candidate_accepted" \
    "CONDITIONAL_REDUCTION" \
    "Accepted Aristotle candidate after local compile validation." \
    "$(phase_target_text "$phase")" \
    "Terminal status: \`$status\`. Candidate transplanted into \`AtkinsonFormula.lean\` and revalidated locally. New repo phase: \`$phase_after\`." \
    "$(phase_target_text "$phase_after")"
  record_lineage \
    "$round" \
    "$(phase_target_text "$phase")" \
    "$(phase_target_text "$phase_after")" \
    "validated Aristotle harvest" \
    "Candidate transplant changed the local repo state and survived direct \`lean\` plus focused \`lake build\`."
}

main() {
  local start_epoch current_job_id current_job_phase current_job_status current_prompt current_snapshot current_submit_log
  local phase out_dir action round public_attempts cleanup_attempts job_status poll_log result_dir final_build_log finished_job_id post_dir
  start_epoch="$(date +%s)"
  current_job_id=""
  current_job_phase=""
  current_job_status=""
  current_prompt=""
  current_snapshot=""
  current_submit_log=""
  public_attempts=0
  cleanup_attempts=0

  write_latest "running" "preflight" "starting overnight harness" "no live Aristotle job"
  write_handoff "Runner starting.\n\nPhase: preflight\nRun id: $RUN_ID\nLog file: $LOG_FILE"
  preflight
  out_dir="$PREFLIGHT_OUT_DIR"
  phase="$PREFLIGHT_PHASE"
  refresh_frontier_ledger "$phase" "preflight complete and frontier refreshed"
  write_handoff "Preflight complete.\n\nRun id: $RUN_ID\nPhase: $phase\nTarget: $(phase_target_text "$phase")\nPreflight dir: $out_dir"
  write_runtime_state "$phase" "$(phase_target_text "$phase")" "" "" "$public_attempts" "$cleanup_attempts" "preflight complete"

  case "$phase" in
    file_health_broken)
      write_latest "blocked" "file health broken" "direct lean or focused lake build failed during preflight" "no live Aristotle job"
      write_handoff "Preflight failed before theorem work.\n\nInspect:\n- $out_dir/direct_lean.log\n- $out_dir/lake_formula.log"
      exit 1
      ;;
    next_public_blocker)
      final_build_log="$LOG_DIR/full_build_${RUN_ID}.log"
      full_build "$final_build_log" || true
      write_latest "stopped" "$(phase_target_text "$phase")" "public leaf already advanced; stopping on the next public blocker" "no live Aristotle job"
      write_handoff "The inverse-phase-cell public leaf is not the current live blocker anymore.\n\nInspect:\n- $out_dir/public_psi.log\n- $out_dir/public_pi.log\n- $final_build_log\n\nRecorded public blockers:\n- ψ: $(cat "$out_dir/public_psi.blocker" 2>/dev/null || true)\n- π: $(cat "$out_dir/public_pi.blocker" 2>/dev/null || true)"
      exit 0
      ;;
    done)
      final_build_log="$LOG_DIR/full_build_${RUN_ID}.log"
      full_build "$final_build_log" || true
      write_latest "stopped" "$(phase_target_text "$phase")" "no public or cleanup blocker detected" "no live Aristotle job"
      write_handoff "No AtkinsonFormula blocker detected in the current repo state.\n\nFull build log: $final_build_log"
      exit 0
      ;;
  esac

  while (( $(date +%s) - start_epoch < MAX_SECONDS )); do
    if [[ -z "$current_job_id" ]]; then
      case "$phase" in
        public_leaf)
          if (( public_attempts >= MAX_ATTEMPTS_PER_PHASE )); then
            write_latest "stopped" "$(phase_target_text "$phase")" "hit maximum Aristotle attempts for the public leaf" "no live Aristotle job"
            write_handoff "Stopped after $public_attempts Aristotle attempts on the public leaf without advancing the repo phase.\n\nNext action: inspect the harvested results and continue locally from the current file state."
            exit 0
          fi
          ;;
        cleanup)
          if (( cleanup_attempts >= MAX_ATTEMPTS_PER_PHASE )); then
            write_latest "stopped" "$(phase_target_text "$phase")" "hit maximum Aristotle attempts for the cleanup lane" "no live Aristotle job"
            write_handoff "Stopped after $cleanup_attempts Aristotle attempts on the cleanup lane without eliminating the remaining \`sorry\`."
            exit 0
          fi
          ;;
      esac

      if [[ -z "${ARISTOTLE_API_KEY:-}" ]]; then
        write_latest "blocked" "$(phase_target_text "$phase")" "ARISTOTLE_API_KEY is not set; runner cannot submit a sidecar job" "no live Aristotle job"
        write_handoff "The overnight harness is ready, but \`ARISTOTLE_API_KEY\` is unset.\n\nCurrent phase: \`$phase\`\nCurrent target: $(phase_target_text "$phase")"
        exit 0
      fi

      current_prompt="$PROMPT_DIR/${RUN_ID}_${phase}.txt"
      current_snapshot="$SNAPSHOT_DIR/${RUN_ID}_${phase}"
      current_submit_log="$LOG_DIR/aristotle_submit_${RUN_ID}_${phase}.log"
      current_job_id="$(submit_phase_job "$phase" "$current_prompt" "$current_snapshot" "$current_submit_log")"

      if [[ -z "$current_job_id" ]]; then
        round="$(round_num)"
        record_round \
          "$round" \
          "aristotle_submit_failed" \
          "FAILED_ROUTE" \
          "Aristotle submit did not return a parseable project id." \
          "$(phase_target_text "$phase")" \
          "Inspect submit log: \`$current_submit_log\`." \
          "$(phase_target_text "$phase")"
        write_latest "blocked" "$(phase_target_text "$phase")" "Aristotle submit failed" "no live Aristotle job"
        write_handoff "Aristotle submit failed to yield a project id.\n\nInspect:\n- $current_submit_log"
        exit 1
      fi

      current_job_phase="$phase"
      current_job_status="SUBMITTED"
      record_job_event "$current_job_id" "$phase" "$current_job_status" "$current_prompt" "$current_snapshot"
      case "$phase" in
        public_leaf) public_attempts=$((public_attempts + 1)) ;;
        cleanup) cleanup_attempts=$((cleanup_attempts + 1)) ;;
      esac
      write_runtime_state "$phase" "$(phase_target_text "$phase")" "$current_job_id" "$current_job_status" "$public_attempts" "$cleanup_attempts" "submitted Aristotle job"
      write_latest "running" "$(phase_target_text "$phase")" "submitted Aristotle job $current_job_id for phase $phase" "project $current_job_id ($phase)"
      write_handoff "Live Aristotle sidecar submitted.\n\nProject id: $current_job_id\nPhase: $phase\nPrompt: $current_prompt\nSnapshot: $current_snapshot\nSubmit log: $current_submit_log"
    fi

    sleep "$POLL_SECONDS"
    poll_log="$LOG_DIR/aristotle_poll_${RUN_ID}_${current_job_id}.log"
    job_status="$(poll_status "$current_job_id" "$poll_log")"
    [[ -z "$job_status" ]] && job_status="UNKNOWN"
    current_job_status="$job_status"
    record_job_event "$current_job_id" "$current_job_phase" "$current_job_status" "$current_prompt" "$current_snapshot"
    write_runtime_state "$phase" "$(phase_target_text "$phase")" "$current_job_id" "$current_job_status" "$public_attempts" "$cleanup_attempts" "polled Aristotle"
    write_latest "running" "$(phase_target_text "$phase")" "Aristotle check-in: $current_job_id is $current_job_status" "project $current_job_id ($current_job_status)"
    write_handoff "Aristotle check-in.\n\nProject id: $current_job_id\nPhase: $current_job_phase\nStatus: $current_job_status\nPrompt: $current_prompt\nSnapshot: $current_snapshot\nPoll log: $poll_log"

    case "$current_job_status" in
      COMPLETE|COMPLETE_WITH_ERRORS|OUT_OF_BUDGET|FAILED|CANCELED)
        result_dir="$RESULTS_DIR/${RUN_ID}_${current_job_id}"
        harvest_terminal_job "$current_job_id" "$current_job_phase" "$current_job_status" "$result_dir"
        finished_job_id="$current_job_id"
        post_dir="$LOG_DIR/post_terminal_${RUN_ID}_${finished_job_id}"
        phase="$(validate_repo_phase "$post_dir")"
        write_runtime_state "$phase" "$(phase_target_text "$phase")" "" "" "$public_attempts" "$cleanup_attempts" "processed terminal Aristotle job"
        current_job_id=""
        current_job_phase=""
        current_job_status=""
        current_prompt=""
        current_snapshot=""
        current_submit_log=""
        case "$phase" in
          file_health_broken)
            write_latest "blocked" "file health broken" "repo health failed after harvesting a terminal Aristotle job" "no live Aristotle job"
            write_handoff "Local file health broke after harvesting an Aristotle result.\n\nInspect:\n- $post_dir"
            exit 1
            ;;
          next_public_blocker)
            final_build_log="$LOG_DIR/full_build_${RUN_ID}.log"
            full_build "$final_build_log" || true
            write_latest "stopped" "$(phase_target_text "$phase")" "public probe advanced past the inverse-phase-cell blocker" "no live Aristotle job"
            write_handoff "The overnight run advanced the strict public path past the inverse-phase-cell blocker.\n\nInspect:\n- $post_dir/public_psi.log\n- $post_dir/public_pi.log\n- $final_build_log"
            exit 0
            ;;
          done)
            final_build_log="$LOG_DIR/full_build_${RUN_ID}.log"
            full_build "$final_build_log" || true
            write_latest "stopped" "$(phase_target_text "$phase")" "all tracked AtkinsonFormula surfaces appear closed" "no live Aristotle job"
            write_handoff "The overnight run closed the current AtkinsonFormula public and cleanup surfaces.\n\nFull build log: $final_build_log"
            exit 0
            ;;
          *)
            round="$(round_num)"
            record_round \
              "$round" \
              "post_terminal_retarget" \
              "CONDITIONAL_REDUCTION" \
              "Processed terminal Aristotle result and recomputed the live repo phase." \
              "$(phase_target_text "$phase")" \
              "Post-harvest phase is now \`$phase\`. The runner will continue with a new exact ticket if attempts remain." \
              "$(phase_target_text "$phase")"
            ;;
        esac
        ;;
      *)
        ;;
    esac
  done

  write_latest "stopped" "$(phase_target_text "$phase")" "hit MAX_SECONDS without finishing the live phase" "project ${current_job_id:-none}"
  write_handoff "The overnight harness hit MAX_SECONDS.\n\nCurrent phase: \`$phase\`\nCurrent target: $(phase_target_text "$phase")\nCurrent job: ${current_job_id:-none}\nCurrent job status: ${current_job_status:-none}"
}

main "$@"
