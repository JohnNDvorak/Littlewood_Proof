#!/usr/bin/env bash
set -euo pipefail

# Ralph Wiggum loop for RH-psi Blocker 5 deep leaves.
# Multi-session orchestration with immediate fresh-session relaunch until:
#   - deep leaves are closed (no sorry/admit at the two B5 sub-sorries),
#   - no new axioms are introduced in the B5 chain files,
#   - no sorry/admit relocation occurs in the B5 chain files,
#   - class/endpoint gates pass,
#   - targeted builds pass,
# or hard-stop policy triggers.
#
# B5 decomposes into two independent sorry leaves:
#   1. ExplicitFormulaPsiAtTEqXHyp   (unconditional explicit formula)
#   2. PsiZeroSumOscillationHyp      (RH-conditional oscillation)

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

REAL_PROGRESS_MODE="${REAL_PROGRESS_MODE:-leaf_delta_build}"
ESCALATION_ON_STALL="${ESCALATION_ON_STALL:-1}"

RUN_ID="${RUN_ID:-$(date '+%Y%m%d_%H%M%S')}"
RUN_DIR="${LOG_DIR:-$ROOT/.lake/ralph_b5/$RUN_ID}"
BEST_STATE_DIR="${BEST_STATE_DIR:-$RUN_DIR/best_state}"
mkdir -p "$RUN_DIR" "$BEST_STATE_DIR"

DEEP_BLOCKERS_FILE="Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean"
B5_CHAIN_FILES=(
  "Littlewood/Aristotle/Standalone/ExplicitFormulaAndOscillationFromSubSorries.lean"
  "Littlewood/Aristotle/Standalone/RHPsiWitnessFromZeroSum.lean"
  "Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean"
  "Littlewood/Aristotle/DirichletPhaseAlignment.lean"
  "Littlewood/CoreLemmas/GrowthDomination.lean"
)

TARGETED_BUILD_TARGETS=(
  "Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries"
  "Littlewood.Aristotle.Standalone.RHPsiWitnessFromZeroSum"
  "Littlewood.Aristotle.Standalone.DeepBlockersResolved"
)

MIN_SORRY_REDUCTION_REQUIRED="${MIN_SORRY_REDUCTION_REQUIRED:-2}"

start_epoch="$(date +%s)"
latest_report_path=""
last_blocker="none"

best_session_index=0
best_snapshot_dir=""
best_deep_leaf_sorry_count=9999
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

snapshot_b5_chain() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "${B5_CHAIN_FILES[@]}" 2>/dev/null || true
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "${B5_CHAIN_FILES[@]}" 2>/dev/null || true
  else
    git -C "$ROOT" diff --numstat -- "${B5_CHAIN_FILES[@]}" || true
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
  for f in "${B5_CHAIN_FILES[@]}"; do
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

  REPORT_RUN_DIR="$RUN_DIR" \
  REPORT_REASON="$reason" \
  REPORT_DEEP_FILE="$DEEP_BLOCKERS_FILE" \
  REPORT_BEST_SESSION_INDEX="$best_session_index" \
  REPORT_BEST_DEEP_SORRY="$best_deep_leaf_sorry_count" \
  REPORT_BEST_SNAPSHOT_DIR="$best_snapshot_dir" \
  python3 - "$md_out" "$json_out" <<'PY'
import glob
import json
import os
import sys

md_out = sys.argv[1]
json_out = sys.argv[2]
run_dir = os.environ.get("REPORT_RUN_DIR", "")
reason = os.environ.get("REPORT_REASON", "")
deep_file = os.environ.get("REPORT_DEEP_FILE", "")
best_session_index = int(os.environ.get("REPORT_BEST_SESSION_INDEX", "0") or 0)
best_deep_sorry = int(os.environ.get("REPORT_BEST_DEEP_SORRY", "9999") or 9999)
best_snapshot_dir = os.environ.get("REPORT_BEST_SNAPSHOT_DIR", "")

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
    deep_leaf = data.get("deep_leaf", {})
    sorry_count = deep_leaf.get("sorry_count", "na") if isinstance(deep_leaf, dict) else "na"
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

payload = {
    "reason": reason,
    "run_dir": run_dir,
    "best_state": {
        "best_session_index": best_session_index,
        "best_deep_leaf_sorry_count": best_deep_sorry,
        "best_snapshot_dir": best_snapshot_dir,
    },
    "last5_sessions": last5,
    "remaining_blockers": {
        "deep_blockers_file": deep_file,
        "required_theorems": [
            "deep_blocker_B5_explicit_formula_psi",
            "deep_blocker_B5_psi_zero_sum_oscillation",
        ],
    },
}

with open(json_out, "w", encoding="utf-8") as f:
    json.dump(payload, f, indent=2, sort_keys=True)

md = []
md.append("# B5 Real-Progress Escalation")
md.append("")
md.append(f"- Reason: `{reason}`")
md.append(f"- Run dir: `{run_dir}`")
md.append(f"- Best deep-leaf sorry count: `{best_deep_sorry}` (session `{best_session_index}`)")
md.append(f"- Best snapshot: `{best_snapshot_dir or 'none'}`")
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

with open(md_out, "w", encoding="utf-8") as f:
    f.write("\n".join(md) + "\n")
PY
}

check_b5_deep_leaf_sorry_count() {
  local file="$1"
  awk '
    BEGIN { mode=""; ef=0; osc=0 }
    /^[[:space:]]*private theorem deep_blocker_B5_explicit_formula_psi[[:space:]]*:/ { mode="ef"; next }
    /^[[:space:]]*private theorem deep_blocker_B5_psi_zero_sum_oscillation[[:space:]]*:/ { mode="osc"; next }
    mode=="ef" && /^[[:space:]]*private theorem deep_blocker_B5_psi_zero_sum_oscillation[[:space:]]*:/ { mode="osc"; next }
    mode!="" && /^[[:space:]]*(private theorem|theorem|lemma|def|class|instance|abbrev|end)([[:space:]]|$)/ { mode="" }
    mode=="ef" && (/^[[:space:]]*(sorry|admit)([[:space:]]|$)/ || /[[:space:]]by[[:space:]]+(sorry|admit)([[:space:]]|$)/) { ef=1 }
    mode=="osc" && (/^[[:space:]]*(sorry|admit)([[:space:]]|$)/ || /[[:space:]]by[[:space:]]+(sorry|admit)([[:space:]]|$)/) { osc=1 }
    END { printf "%d %d %d\n", ef, osc, ef+osc }
  ' "$file"
}

count_axiom_lines() {
  local out
  out="$(rg -c --pcre2 '^[[:space:]]*axiom[[:space:]]' "${B5_CHAIN_FILES[@]}" 2>/dev/null || true)"
  if [[ -z "$out" ]]; then
    echo 0
  else
    awk -F: '{ s += $2 } END { print s + 0 }' <<< "$out"
  fi
}

count_code_sorry_like_lines() {
  local out
  out="$(rg -c --pcre2 '(^[[:space:]]*(sorry|admit)[[:space:]]*$)|([[:space:]]by[[:space:]]+(sorry|admit)([[:space:]]|$))' "${B5_CHAIN_FILES[@]}" 2>/dev/null || true)"
  if [[ -z "$out" ]]; then
    echo 0
  else
    awk -F: '{ s += $2 } END { print s + 0 }' <<< "$out"
  fi
}

run_lean_gate() {
  local mode="$1"
  local lean_file="$2"
  local out_file="$3"

  cat > "$lean_file" <<'LEAN'
import Littlewood.Aristotle.Standalone.DeepBlockersResolved
import Littlewood.Aristotle.Standalone.RHPsiWitnessFromZeroSum
import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
LEAN

  case "$mode" in
    explicit_formula)
      cat >> "$lean_file" <<'LEAN'
#check @Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.ExplicitFormulaPsiAtTEqXHyp.proof
LEAN
      ;;
    oscillation)
      cat >> "$lean_file" <<'LEAN'
#check @Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.PsiZeroSumOscillationHyp.proof
LEAN
      ;;
    endpoint)
      cat >> "$lean_file" <<'LEAN'
example [Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.ExplicitFormulaPsiAtTEqXHyp]
    [Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.PsiZeroSumOscillationHyp] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPsiWitnessData := by
  exact Aristotle.Standalone.RHPsiWitnessFromZeroSum.rhPsiWitness_proved
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
Close out the two explicit deep leaves for B5 in:
- $DEEP_BLOCKERS_FILE
- private theorem deep_blocker_B5_explicit_formula_psi : ExplicitFormulaPsiAtTEqXHyp
- private theorem deep_blocker_B5_psi_zero_sum_oscillation : PsiZeroSumOscillationHyp

Hard requirements:
1. Do not replace leaves with axioms.
2. Do not relocate sorry/admit into other B5 chain files.
3. Preserve existing constructive chain and use proved infrastructure.
4. After edits, run targeted build:
   lake build ${TARGETED_BUILD_TARGETS[*]}

Current loop session: $session_index
Run directory: $RUN_DIR
Previous blocker: $prior_blocker
Previous report: ${latest_report_path:-none}

Mathematical context for ExplicitFormulaPsiAtTEqXHyp (unconditional):
- Need: ∃ C, ∀ x ≥ 2, |chebyshevPsi(x) - x - (-(Σ_{ρ∈ZerosBelow x} x^ρ/ρ).re)| ≤ C·(log x)²
- chebyshevPsi = Σ_{n≤x} Λ(n) (von Mangoldt sum, defined in DirichletPhaseAlignment.lean:26)
- ZerosBelow x = critical zeros with |Im(ρ)| ≤ x (DirichletPhaseAlignment.lean:41)
- This is the T=x case of the truncated explicit formula (Montgomery-Vaughan §12.5)
- Strategy: prove from Perron's formula or use existing zero-counting + tail bounds

Mathematical context for PsiZeroSumOscillationHyp (conditional on RH):
- Need: RH → (cofinal x with psiMainTerm(x) ≥ 4√x·lll(x)) ∧ (cofinal x with psiMainTerm(x) ≤ -4√x·lll(x))
- psiMainTerm(x) = Re(Σ_{ρ∈ZerosBelow x} x^ρ/ρ) (RHPsiWitnessFromZeroSum.lean:48)
- lll(x) = log(log(log(x))) (CoreLemmas/GrowthDomination.lean:32)
- Under RH: all ρ have Re=1/2, so x^ρ = √x·e^{iγ·log x}
- ALREADY PROVED: simultaneous_dirichlet_approximation, exists_large_x_phases_aligned (DirichletPhaseAlignment.lean:116-192)
- ALREADY PROVED: bound_real_part_of_sum_aligned (DirichletPhaseAlignment.lean:270) — lower bound on Re(Σ x^ρ/ρ) when phases aligned to 0
- ALREADY PROVED: exists_large_x_phases_aligned_finset (DirichletPhaseAlignment.lean:256) — for any finite set S and ε, find x with phases near 1
- DETAILED PROOF STRATEGY for oscillation:
  Step 1: Need a new lemma (or adapt bound_real_part_of_sum_aligned) for PHASE π/2 alignment:
    When γ_j·log(x) ≈ π/2 (mod 2π), then x^{iγ_j} ≈ i, and
    Re(i/(1/2+iγ_j)) = γ_j/(1/4+γ_j²) ≈ 1/γ_j for large γ_j.
    So the contribution is √x·Σ 1/γ_j (not the convergent Σ Re(1/ρ) = Σ 1/(2(1/4+γ²))).
  Step 2: The sum Σ_{γ≤T} 1/γ diverges like (1/4π)(log T)² by zero-counting N(T)~(T/2π)log(T/2πe).
    So we can get psiMainTerm(x) ≥ c·√x·(log T)² for aligned x.
    Since lll(x) = log(log(log x)) << (log T)², the bound 4√x·lll(x) is easily exceeded.
  Step 3: Control the tail {γ_N < |γ| ≤ x}: ZerosBelow(x) may include more zeros than aligned.
    Key: the Dirichlet approximant x = exp(2πt) where t ≤ N^N, so ZerosBelow(x) ⊃ S.
    Tail bound: |Σ_{T<|γ|≤x} Re(x^ρ/ρ)| ≤ √x·Σ_{T<|γ|≤x} 1/|ρ|.
    Use Abel summation + zero counting to show tail is smaller than main term.
  Step 4: For negative oscillation, align to -π/2 instead of π/2.
  NOTE: The existing bound_real_part_of_sum_aligned is NOT strong enough (uses Re(1/ρ)=O(1/γ²) not 1/γ).
    Need a new phase-shifted alignment lemma.
- HYPOTHESES NEEDED FROM RH: all zeros have Re=1/2, ZerosBelow(T).Finite, divergent Σ 1/γ
- The ZetaZeros.RiemannHypothesis hypothesis is available as an input to the proof

Key infrastructure files:
- DirichletPhaseAlignment.lean: chebyshevPsi, ZerosBelow, CriticalZeros, phase alignment lemmas
- CoreLemmas/GrowthDomination.lean: lll, growth domination lemmas
- RHPsiWitnessFromZeroSum.lean: psiMainTerm, downstream assembly (all proved given the two sub-sorries)
- ExplicitFormulaAndOscillationFromSubSorries.lean: class definitions + assembly theorem

Deliverables this session:
- measurable proof progress toward removing sorry at the two listed deep leaves,
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

real_reasons = [r for r in os.environ.get("REPORT_REAL_PROGRESS_REASONS", "").split(",") if r]
legacy_reasons = [r for r in os.environ.get("REPORT_PROGRESS_REASONS", "").split(",") if r]

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
        "explicit_formula": os.environ.get("REPORT_EXPLICIT_FORMULA_STATUS", "fail"),
        "oscillation": os.environ.get("REPORT_OSCILLATION_STATUS", "fail"),
        "endpoint": os.environ.get("REPORT_ENDPOINT_STATUS", "fail"),
        "targeted_build": os.environ.get("REPORT_BUILD_STATUS", "fail"),
        "deep_leaf_no_sorry": os.environ.get("REPORT_DEEP_LEAF_STATUS", "fail"),
        "no_axiom_introduced": os.environ.get("REPORT_NO_AXIOM_STATUS", "fail"),
        "no_sorry_relocation": os.environ.get("REPORT_NO_SORRY_RELOCATION_STATUS", "fail"),
    },
    "deep_leaf": {
        "explicit_formula_has_sorry": as_int("REPORT_DEEP_EF_HAS_SORRY", 1),
        "oscillation_has_sorry": as_int("REPORT_DEEP_OSC_HAS_SORRY", 1),
        "sorry_count": as_int("REPORT_DEEP_SORRY_COUNT", 2),
    },
    "metrics": {
        "gate_pass_count": as_int("REPORT_GATE_PASS_COUNT", 0),
        "targeted_build_pass": as_int("REPORT_TARGETED_BUILD_PASS", 0),
        "b5_obligation_artifacts_updated": as_int("REPORT_B5_ARTIFACTS_UPDATED", 0),
        "axiom_count_start": as_int("REPORT_AXIOM_COUNT_START", 0),
        "axiom_count_post": as_int("REPORT_AXIOM_COUNT_POST", 0),
        "sorry_count_start": as_int("REPORT_SORRY_COUNT_START", 0),
        "sorry_count_post": as_int("REPORT_SORRY_COUNT_POST", 0),
        "min_sorry_reduction_required": as_int("REPORT_MIN_SORRY_REDUCTION_REQUIRED", 2),
    },
    "real_progress": {
        "mode": os.environ.get("REPORT_REAL_PROGRESS_MODE", "leaf_delta_build"),
        "status": real_progress_status,
        "reasons": real_reasons,
        "leaf_delta": as_bool("REPORT_LEAF_DELTA"),
        "regression_detected": as_bool("REPORT_REGRESSION_DETECTED"),
        "stale_sessions": as_int("REPORT_STALE_SESSIONS", 0),
        "max_stale_sessions": as_int("REPORT_MAX_STALE_SESSIONS", 0),
    },
    # Backward-compatible alias for older readers.
    "progress": {
        "status": real_progress_status,
        "reasons": real_reasons,
        "stale_sessions": as_int("REPORT_STALE_SESSIONS", 0),
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
        "explicit_formula": os.environ.get("REPORT_EXPLICIT_FORMULA_LOG", ""),
        "oscillation": os.environ.get("REPORT_OSCILLATION_LOG", ""),
        "endpoint": os.environ.get("REPORT_ENDPOINT_LOG", ""),
        "deep_leaf": os.environ.get("REPORT_DEEP_LEAF_LOG", ""),
        "axiom": os.environ.get("REPORT_AXIOM_LOG", ""),
        "relocation": os.environ.get("REPORT_RELOCATION_LOG", ""),
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

read -r _init_ef _init_osc initial_deep_leaf_sorry_count \
  < <(check_b5_deep_leaf_sorry_count "$DEEP_BLOCKERS_FILE")
best_deep_leaf_sorry_count="$initial_deep_leaf_sorry_count"

echo "Ralph B5 deep-leaf baseline:"
echo "run_dir: $RUN_DIR"
echo "best_state_dir: $BEST_STATE_DIR"
echo "real_progress_mode: $REAL_PROGRESS_MODE"
echo "axiom_count_start: $axiom_count_start"
echo "sorry_count_start: $sorry_count_start"
echo "initial_deep_leaf_sorry_count: $initial_deep_leaf_sorry_count"
echo "required_sorry_reduction: $required_sorry_reduction"

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
  ef_log="$sess_dir/gate_explicit_formula.log"
  osc_log="$sess_dir/gate_oscillation.log"
  endpoint_log="$sess_dir/gate_endpoint.log"
  deep_leaf_log="$sess_dir/gate_deep_leaf.log"
  axiom_log="$sess_dir/gate_no_axiom.log"
  relocation_log="$sess_dir/gate_no_relocation.log"
  report_json="$sess_dir/session_report.json"

  session_start="$(date +%s)"

  pre_snapshot="$(snapshot_b5_chain)"
  pre_deep_digest="$(file_digest "$DEEP_BLOCKERS_FILE")"
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

  t1="$(mktemp -t ralph_b5_ef_gate)"
  t2="$(mktemp -t ralph_b5_osc_gate)"
  t3="$(mktemp -t ralph_b5_endpoint_gate)"

  explicit_formula_status="fail"
  oscillation_status="fail"
  endpoint_status="fail"

  if run_lean_gate explicit_formula "$t1" "$ef_log"; then explicit_formula_status="pass"; fi
  if run_lean_gate oscillation "$t2" "$osc_log"; then oscillation_status="pass"; fi
  if run_lean_gate endpoint "$t3" "$endpoint_log"; then endpoint_status="pass"; fi

  rm -f "$t1" "$t2" "$t3"

  read -r deep_ef_has_sorry deep_osc_has_sorry deep_leaf_sorry_count \
    < <(check_b5_deep_leaf_sorry_count "$DEEP_BLOCKERS_FILE")
  {
    echo "deep_blocker_B5_explicit_formula_psi_has_sorry=$deep_ef_has_sorry"
    echo "deep_blocker_B5_psi_zero_sum_oscillation_has_sorry=$deep_osc_has_sorry"
    echo "deep_leaf_sorry_count=$deep_leaf_sorry_count"
  } >"$deep_leaf_log"

  deep_leaf_status="pass"
  if (( deep_leaf_sorry_count > 0 )); then
    deep_leaf_status="fail"
  fi

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
    echo "relocation_rule=fail_if_sorry_count_increases"
  } >"$relocation_log"

  gate_pass_count=0
  [[ "$explicit_formula_status" == "pass" ]] && gate_pass_count=$((gate_pass_count + 1))
  [[ "$oscillation_status" == "pass" ]] && gate_pass_count=$((gate_pass_count + 1))
  [[ "$endpoint_status" == "pass" ]] && gate_pass_count=$((gate_pass_count + 1))

  post_snapshot="$(snapshot_b5_chain)"
  b5_artifacts_updated=0
  if [[ "$pre_snapshot" != "$post_snapshot" ]]; then
    b5_artifacts_updated=1
  fi

  leaf_delta=0
  if (( deep_leaf_sorry_count < best_deep_leaf_sorry_count )); then
    leaf_delta=1
  fi

  regression_detected=0
  if (( best_session_index > 0 )) && (( deep_leaf_sorry_count > best_deep_leaf_sorry_count )); then
    regression_detected=1
  fi

  real_progress_status="fail"
  real_progress_reasons=()

  if (( leaf_delta == 1 )) &&
     [[ "$construct_status" == "pass" ]] &&
     [[ "$build_status" == "pass" ]] &&
     [[ "$no_axiom_status" == "pass" ]] &&
     [[ "$no_sorry_relocation_status" == "pass" ]]; then
    real_progress_status="pass"
    real_progress_reasons+=("leaf_sorry_count_decreased")
    real_progress_reasons+=("targeted_build_passed")
    real_progress_reasons+=("safety_gates_preserved")
  fi

  if (( regression_detected == 1 )); then
    real_progress_reasons+=("regression_detected")
  fi

  if [[ "$real_progress_status" == "pass" ]]; then
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
  elif (( regression_detected == 1 )); then
    next_blocker="deep-leaf regression detected versus best-known state"
  elif [[ "$deep_leaf_status" != "pass" ]]; then
    next_blocker="deep leaf sorries remain in DeepBlockersResolved"
  elif [[ "$no_axiom_status" != "pass" ]]; then
    next_blocker="new axiom introduced in B5 chain files"
  elif [[ "$no_sorry_relocation_status" != "pass" ]]; then
    next_blocker="sorry relocation gate failed in B5 chain files"
  elif [[ "$explicit_formula_status" != "pass" ]]; then
    next_blocker="ExplicitFormulaPsiAtTEqXHyp gate unresolved"
  elif [[ "$oscillation_status" != "pass" ]]; then
    next_blocker="PsiZeroSumOscillationHyp gate unresolved"
  elif [[ "$endpoint_status" != "pass" ]]; then
    next_blocker="rhPsiWitness_proved endpoint gate unresolved"
  elif [[ "$real_progress_status" != "pass" ]]; then
    next_blocker="no real measurable progress"
  fi

  success=0
  if [[ "$build_status" == "pass" &&
        "$deep_leaf_status" == "pass" &&
        "$no_axiom_status" == "pass" &&
        "$no_sorry_relocation_status" == "pass" &&
        "$explicit_formula_status" == "pass" &&
        "$oscillation_status" == "pass" &&
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
  if (( ${#real_progress_reasons[@]} > 0 )); then
    progress_reasons_csv="$(IFS=, ; echo "${real_progress_reasons[*]}")"
  fi

  REPORT_SCHEMA_VERSION="2" \
  REPORT_SESSION_INDEX="$session_index" \
  REPORT_TIMESTAMP="$ts" \
  REPORT_DURATION_SECS="$session_duration" \
  REPORT_CONSTRUCT_STATUS="$construct_status" \
  REPORT_CONSTRUCT_TIMED_OUT="$construct_timed_out" \
  REPORT_CONSTRUCT_EXIT_CODE="$construct_exit_code" \
  REPORT_EXPLICIT_FORMULA_STATUS="$explicit_formula_status" \
  REPORT_OSCILLATION_STATUS="$oscillation_status" \
  REPORT_ENDPOINT_STATUS="$endpoint_status" \
  REPORT_BUILD_STATUS="$build_status" \
  REPORT_DEEP_LEAF_STATUS="$deep_leaf_status" \
  REPORT_DEEP_EF_HAS_SORRY="$deep_ef_has_sorry" \
  REPORT_DEEP_OSC_HAS_SORRY="$deep_osc_has_sorry" \
  REPORT_DEEP_SORRY_COUNT="$deep_leaf_sorry_count" \
  REPORT_NO_AXIOM_STATUS="$no_axiom_status" \
  REPORT_NO_SORRY_RELOCATION_STATUS="$no_sorry_relocation_status" \
  REPORT_GATE_PASS_COUNT="$gate_pass_count" \
  REPORT_TARGETED_BUILD_PASS="$targeted_build_pass" \
  REPORT_B5_ARTIFACTS_UPDATED="$b5_artifacts_updated" \
  REPORT_AXIOM_COUNT_START="$axiom_count_start" \
  REPORT_AXIOM_COUNT_POST="$axiom_count_post" \
  REPORT_SORRY_COUNT_START="$sorry_count_start" \
  REPORT_SORRY_COUNT_POST="$sorry_count_post" \
  REPORT_MIN_SORRY_REDUCTION_REQUIRED="$required_sorry_reduction" \
  REPORT_REAL_PROGRESS_MODE="$REAL_PROGRESS_MODE" \
  REPORT_REAL_PROGRESS_STATUS="$real_progress_status" \
  REPORT_REAL_PROGRESS_REASONS="$progress_reasons_csv" \
  REPORT_PROGRESS_STATUS="$real_progress_status" \
  REPORT_PROGRESS_REASONS="$progress_reasons_csv" \
  REPORT_STALE_SESSIONS="$stale_sessions" \
  REPORT_MAX_STALE_SESSIONS="$MAX_STALE_SESSIONS" \
  REPORT_LEAF_DELTA="$leaf_delta" \
  REPORT_REGRESSION_DETECTED="$regression_detected" \
  REPORT_BEST_SESSION_INDEX="$best_session_index" \
  REPORT_BEST_DEEP_SORRY="$best_deep_leaf_sorry_count" \
  REPORT_BEST_SNAPSHOT_DIR="$best_snapshot_dir" \
  REPORT_NEXT_BLOCKER="$next_blocker" \
  REPORT_NEXT_ACTION="$next_action" \
  REPORT_PROMPT_LOG="$prompt_log" \
  REPORT_CONSTRUCT_LOG="$construct_log" \
  REPORT_BUILD_LOG="$build_log" \
  REPORT_EXPLICIT_FORMULA_LOG="$ef_log" \
  REPORT_OSCILLATION_LOG="$osc_log" \
  REPORT_ENDPOINT_LOG="$endpoint_log" \
  REPORT_DEEP_LEAF_LOG="$deep_leaf_log" \
  REPORT_AXIOM_LOG="$axiom_log" \
  REPORT_RELOCATION_LOG="$relocation_log" \
  write_session_json "$report_json"

  if [[ "$real_progress_status" == "pass" ]]; then
    snapshot_best_state "$session_index" "$ts" "$deep_leaf_sorry_count" "$build_status" "$report_json"
  fi

  latest_report_path="$report_json"
  last_blocker="$next_blocker"

  echo "=== Ralph B5 Session ${session_index} ==="
  echo "timestamp: ${ts}"
  echo "run_dir: ${sess_dir}"
  echo "construct: ${construct_status} (exit=${construct_exit_code}, timed_out=${construct_timed_out})"
  echo "targeted_build: ${build_status}"
  echo "gate_explicit_formula: ${explicit_formula_status}"
  echo "gate_oscillation: ${oscillation_status}"
  echo "gate_endpoint: ${endpoint_status}"
  echo "gate_deep_leaf_no_sorry: ${deep_leaf_status}"
  echo "gate_no_axiom_introduced: ${no_axiom_status} (start=${axiom_count_start}, post=${axiom_count_post})"
  echo "gate_no_sorry_relocation: ${no_sorry_relocation_status} (start=${sorry_count_start}, post=${sorry_count_post})"
  echo "deep_leaf_sorry_count: ${deep_leaf_sorry_count} (ef=${deep_ef_has_sorry}, osc=${deep_osc_has_sorry})"
  echo "gate_pass_count: ${gate_pass_count}/3"
  echo "b5_artifacts_updated: ${b5_artifacts_updated}"
  echo "real_progress: ${real_progress_status}"
  echo "real_progress_reasons: ${real_progress_reasons[*]:-none}"
  echo "leaf_delta: ${leaf_delta}"
  echo "regression_detected: ${regression_detected}"
  echo "best_deep_leaf_sorry_count: ${best_deep_leaf_sorry_count} (session=${best_session_index})"
  echo "stale_sessions: ${stale_sessions}/${MAX_STALE_SESSIONS}"
  echo "next_blocker: ${next_blocker}"
  echo "next_action: ${next_action}"
  echo "session_report_json: ${report_json}"

  if (( success == 1 )); then
    echo "Ralph B5 deep-leaf loop complete: both B5 deep leaves closed and all closure gates passed."
    exit 0
  fi

  if [[ "$next_action" == "stop_stale" ]]; then
    if [[ "$ESCALATION_ON_STALL" == "1" ]]; then
      write_escalation_bundle "no_real_progress"
      echo "Escalation bundle: $RUN_DIR/escalation_summary.md"
      echo "Escalation bundle JSON: $RUN_DIR/escalation_summary.json"
    fi
    echo "Stopping: no real measurable progress for ${stale_sessions} consecutive sessions."
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
