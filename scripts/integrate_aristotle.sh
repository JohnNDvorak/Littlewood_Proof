#!/bin/bash
# Littlewood Formalization: Aristotle File Integration Script
# Run from project root: ./scripts/integrate_aristotle.sh <source_file> [target_name]
#
# Automates the integration checklist (docs/aristotle_integration_checklist.md):
# 1. Copies file to Littlewood/Aristotle/<TargetName>.lean
# 2. Wraps in Aristotle.<TargetName> namespace
# 3. Replaces exact? with sorry
# 4. Removes #check statements
# 5. Normalizes maxHeartbeats to project standard
# 6. Builds and reports sorry count
#
# Does NOT auto-wire Bridge files — that requires manual review.

set -e

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_ROOT"

MAX_HEARTBEATS=3200000

# --- Argument parsing ---
if [ $# -lt 1 ]; then
  echo "Usage: $0 <source_file> [target_name]"
  echo ""
  echo "  source_file  Path to Aristotle-generated .lean file"
  echo "  target_name  Name for the file (without .lean extension)"
  echo "               Defaults to the source filename"
  echo ""
  echo "Example:"
  echo "  $0 ~/Downloads/aristotle_output.lean ZetaConvexityStrip"
  echo "  -> Creates Littlewood/Aristotle/ZetaConvexityStrip.lean"
  exit 1
fi

SOURCE="$1"
if [ ! -f "$SOURCE" ]; then
  echo "ERROR: Source file not found: $SOURCE"
  exit 1
fi

# Determine target name
if [ -n "$2" ]; then
  TARGET_NAME="$2"
else
  TARGET_NAME=$(basename "$SOURCE" .lean)
fi

TARGET="Littlewood/Aristotle/${TARGET_NAME}.lean"
MODULE="Littlewood.Aristotle.${TARGET_NAME}"

echo "=== Aristotle Integration ==="
echo "Source:  $SOURCE"
echo "Target:  $TARGET"
echo "Module:  $MODULE"
echo ""

# --- Pre-flight checks ---
if [ -f "$TARGET" ]; then
  echo "WARNING: Target file already exists: $TARGET"
  read -p "Overwrite? [y/N] " confirm
  if [ "$confirm" != "y" ] && [ "$confirm" != "Y" ]; then
    echo "Aborted."
    exit 0
  fi
fi

# --- Step 1: Copy file ---
echo "--- Step 1: Copying file ---"
cp "$SOURCE" "$TARGET"
echo "  Copied to $TARGET"

# --- Step 2: Analyze source ---
echo ""
echo "--- Step 2: Source analysis ---"

EXACT_Q_COUNT=$(grep -c 'exact?' "$TARGET" 2>/dev/null || true)
EXACT_Q_COUNT=${EXACT_Q_COUNT:-0}
SORRY_COUNT=$(grep -c '^\s*sorry' "$TARGET" 2>/dev/null || true)
SORRY_COUNT=${SORRY_COUNT:-0}
CHECK_COUNT=$(grep -c '^#check' "$TARGET" 2>/dev/null || true)
CHECK_COUNT=${CHECK_COUNT:-0}
HEARTBEAT_LINES=$(grep -n 'maxHeartbeats' "$TARGET" 2>/dev/null || echo "(none)")

echo "  exact? calls:     $EXACT_Q_COUNT"
echo "  sorry calls:      $SORRY_COUNT"
echo "  #check stmts:     $CHECK_COUNT"
echo "  maxHeartbeats:    $HEARTBEAT_LINES"

# Check Lean version in header (macOS-compatible: use grep -oE instead of -oP)
LEAN_VER=$(grep -oE 'v4\.[0-9]+\.[0-9]+' "$TARGET" 2>/dev/null | head -1)
LEAN_VER=${LEAN_VER:-unknown}
if [ "$LEAN_VER" != "unknown" ] && [ "$LEAN_VER" != "v4.27.0" ]; then
  echo "  Lean version:     $LEAN_VER (project uses v4.27.0-rc1 — may need compat fixes)"
else
  echo "  Lean version:     compatible"
fi

# --- Step 3: Add namespace if missing ---
echo ""
echo "--- Step 3: Namespace check ---"

if grep -q "namespace Aristotle\\.${TARGET_NAME}" "$TARGET"; then
  echo "  Namespace already present"
else
  echo "  Adding namespace Aristotle.${TARGET_NAME}"
  # Find the first theorem/lemma/def/structure line and insert namespace before it.
  # This avoids issues with multiline block comments.
  {
    IN_BLOCK_COMMENT=false
    NAMESPACE_INSERTED=false
    while IFS= read -r line; do
      # Track block comments
      if echo "$line" | grep -q '/-'; then
        IN_BLOCK_COMMENT=true
      fi
      if echo "$line" | grep -q '\-/'; then
        IN_BLOCK_COMMENT=false
        echo "$line"
        continue
      fi
      if $IN_BLOCK_COMMENT; then
        echo "$line"
        continue
      fi
      # Insert namespace before first theorem/lemma/def/structure
      if ! $NAMESPACE_INSERTED; then
        if echo "$line" | grep -qE '^(theorem |lemma |def |structure |private |protected |@\[)'; then
          echo ""
          echo "namespace Aristotle.${TARGET_NAME}"
          echo ""
          NAMESPACE_INSERTED=true
        fi
      fi
      echo "$line"
    done < "$TARGET"
    if $NAMESPACE_INSERTED; then
      echo ""
      echo "end Aristotle.${TARGET_NAME}"
    else
      echo ""
      echo "WARNING: Could not find insertion point for namespace" >&2
    fi
  } > "${TARGET}.tmp"
  mv "${TARGET}.tmp" "$TARGET"
fi

# --- Step 4: Replace exact? with sorry ---
echo ""
echo "--- Step 4: Replacing exact? with sorry ---"

if [ "$EXACT_Q_COUNT" -gt 0 ] 2>/dev/null; then
  # Replace exact? (possibly with arguments) with sorry
  sed -i.bak -E 's/exact\?($| .*$)/sorry/g' "$TARGET"
  NEW_EXACT=$(grep -c 'exact?' "$TARGET" 2>/dev/null || true)
  NEW_EXACT=${NEW_EXACT:-0}
  echo "  Replaced $((EXACT_Q_COUNT - NEW_EXACT)) exact? calls with sorry"
  rm -f "${TARGET}.bak"
else
  echo "  No exact? calls to replace"
fi

# --- Step 5: Remove #check statements ---
echo ""
echo "--- Step 5: Removing #check statements ---"

if [ "$CHECK_COUNT" -gt 0 ] 2>/dev/null; then
  sed -i.bak '/^#check/d' "$TARGET"
  echo "  Removed $CHECK_COUNT #check statements"
  rm -f "${TARGET}.bak"
else
  echo "  No #check statements to remove"
fi

# --- Step 6: Normalize maxHeartbeats ---
echo ""
echo "--- Step 6: Normalizing maxHeartbeats ---"

if grep -q 'set_option maxHeartbeats 0' "$TARGET"; then
  sed -i.bak "s/set_option maxHeartbeats 0/set_option maxHeartbeats $MAX_HEARTBEATS/" "$TARGET"
  echo "  Changed maxHeartbeats 0 -> $MAX_HEARTBEATS"
  rm -f "${TARGET}.bak"
elif grep -q 'maxHeartbeats' "$TARGET"; then
  echo "  maxHeartbeats already set (review manually if needed)"
else
  echo "  No maxHeartbeats found (project default applies)"
fi

# --- Step 7: Build ---
echo ""
echo "--- Step 7: Building $MODULE ---"

BUILD_OUTPUT=$(lake build "$MODULE" 2>&1)
BUILD_EXIT=$?

if [ $BUILD_EXIT -ne 0 ]; then
  echo "  BUILD FAILED (exit code $BUILD_EXIT)"
  echo ""
  echo "  Errors:"
  echo "$BUILD_OUTPUT" | grep "^error:" | head -20 | sed 's/^/    /'
  echo ""
  echo "  Common fixes for Lean 4.24 -> 4.27 compat:"
  echo "    - h.not_le -> not_le.2 h"
  echo "    - Int.cast_nonneg.mpr -> exact_mod_cast"
  echo "    - le_div_iff -> le_div_iff₀"
  echo "    - div_le_iff -> div_le_iff₀"
  echo ""
  echo "  File saved at: $TARGET"
  echo "  Fix errors and re-run: lake build $MODULE"
  exit 1
fi

# --- Step 8: Report ---
echo "  BUILD SUCCEEDED"
echo ""

FINAL_SORRY=$(echo "$BUILD_OUTPUT" | grep -c "declaration uses 'sorry'" || echo 0)
FINAL_WARN=$(echo "$BUILD_OUTPUT" | grep -c "^warning:" || echo 0)

echo "=== Integration Summary ==="
echo "  File:          $TARGET"
echo "  Module:        $MODULE"
echo "  Sorry count:   $FINAL_SORRY"
echo "  Warnings:      $FINAL_WARN"
echo ""

if [ "$FINAL_SORRY" -gt 0 ]; then
  echo "  Sorry declarations:"
  echo "$BUILD_OUTPUT" | grep "declaration uses 'sorry'" | sed 's/^/    /'
  echo ""
  echo "  Next steps:"
  echo "    1. Attempt to close budget-exhaustion sorries (see docs/aristotle_integration_checklist.md)"
  echo "    2. Document remaining sorries in docs/AristotleStatus.md"
  echo "    3. Check if any Bridge files can wire this output"
else
  echo "  SORRY-FREE — check if this closes a hypothesis or feeds a Bridge file."
fi

echo ""
echo "  Don't forget to update:"
echo "    - docs/AristotleStatus.md"
echo "    - docs/sorry_manifest.txt (if build-visible)"
echo "    - scripts/verify_build.sh (if sorry count changed)"
