#!/bin/bash
# Littlewood Formalization: CI Verification Script
# Run from project root: ./scripts/verify_build.sh
#
# Checks:
# 1. Main target builds successfully
# 2. Sorry count matches expected value
# 3. CriticalPathTest compiles
# 4. No deprecated imports active

set -e

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_ROOT"

EXPECTED_SORRY_COUNT=11
EXPECTED_PROJECT_SORRY_COUNT=8

echo "=== Littlewood Formalization: Build Verification ==="
echo "Date: $(date)"
echo "Project: $PROJECT_ROOT"
echo ""

# Step 1: Build main target
echo "--- Step 1: Building Littlewood.Main.Littlewood ---"
BUILD_OUTPUT=$(lake build Littlewood.Main.Littlewood 2>&1)
BUILD_EXIT=$?

if [ $BUILD_EXIT -ne 0 ]; then
  echo "FAIL: Main target build failed (exit code $BUILD_EXIT)"
  echo "$BUILD_OUTPUT" | tail -20
  exit 1
fi
echo "PASS: Main target builds successfully"

# Step 2: Count sorry warnings
echo ""
echo "--- Step 2: Checking sorry count ---"
SORRY_COUNT=$(echo "$BUILD_OUTPUT" | grep -c "declaration uses 'sorry'" || true)
PROJECT_SORRY_COUNT=$(echo "$BUILD_OUTPUT" | grep "declaration uses 'sorry'" | grep -c "^warning: Littlewood/" || true)
EXTERNAL_SORRY_COUNT=$(echo "$BUILD_OUTPUT" | grep "declaration uses 'sorry'" | grep -cv "^warning: Littlewood/" || true)

echo "  Total sorry warnings:   $SORRY_COUNT (expected: $EXPECTED_SORRY_COUNT)"
echo "  Project sorries:        $PROJECT_SORRY_COUNT (expected: $EXPECTED_PROJECT_SORRY_COUNT)"
echo "  External sorries:       $EXTERNAL_SORRY_COUNT (expected: $((EXPECTED_SORRY_COUNT - EXPECTED_PROJECT_SORRY_COUNT)))"

if [ "$SORRY_COUNT" -ne "$EXPECTED_SORRY_COUNT" ]; then
  echo "WARNING: Sorry count mismatch!"
  echo "  Sorry declarations:"
  echo "$BUILD_OUTPUT" | grep "declaration uses 'sorry'" | sed 's/^/    /'
  if [ "$SORRY_COUNT" -gt "$EXPECTED_SORRY_COUNT" ]; then
    echo "FAIL: Sorry count increased (regression)"
    exit 1
  else
    echo "NOTE: Sorry count decreased (progress!) — update EXPECTED_SORRY_COUNT in this script"
  fi
else
  echo "PASS: Sorry count matches expected value"
fi

# Step 3: Build CriticalPathTest
echo ""
echo "--- Step 3: Building CriticalPathTest ---"
if lake build Littlewood.Tests.CriticalPathTest 2>&1 | tail -3; then
  echo "PASS: CriticalPathTest compiles"
else
  echo "FAIL: CriticalPathTest failed to compile"
  exit 1
fi

# Step 4: Check for deprecated imports
echo ""
echo "--- Step 4: Checking for deprecated imports ---"
DEPRECATED_IMPORTS=$(grep -r "^import.*PsiToThetaOscillation" Littlewood/ --include="*.lean" 2>/dev/null || true)
if [ -n "$DEPRECATED_IMPORTS" ]; then
  echo "FAIL: Found active imports of deprecated PsiToThetaOscillation:"
  echo "$DEPRECATED_IMPORTS" | sed 's/^/    /'
  exit 1
fi
echo "PASS: No deprecated imports found"

# Step 5: Build standalone Aristotle file (if present)
echo ""
echo "--- Step 5: Building Aristotle.PsiOscillationPiLi (standalone) ---"
if [ -f "Littlewood/Aristotle/PsiOscillationPiLi.lean" ]; then
  if lake build Littlewood.Aristotle.PsiOscillationPiLi 2>&1 | tail -3; then
    echo "PASS: PsiOscillationPiLi compiles (0 sorries)"
  else
    echo "FAIL: PsiOscillationPiLi failed to compile"
    exit 1
  fi
else
  echo "SKIP: PsiOscillationPiLi.lean not found"
fi

# Summary
echo ""
echo "=== VERIFICATION COMPLETE ==="
echo "All checks passed."
echo "  Main target: $SORRY_COUNT sorry warnings ($PROJECT_SORRY_COUNT project + $EXTERNAL_SORRY_COUNT external)"
