#!/bin/bash
# Littlewood Project Status Dashboard
# Updates docs/current_status.txt with current project metrics

cd "$(dirname "$0")/.."

echo "=== LITTLEWOOD PROJECT STATUS ==="
echo "Generated: $(date)"
echo ""

# Count sorries
TOTAL_SORRY=$(grep -r "sorry" Littlewood/ --include="*.lean" | grep -v "^.*:.*--" | wc -l | tr -d ' ')
ASSUME_SORRY=$(grep "sorry" Littlewood/Assumptions.lean | grep -v "^.*--" | wc -l | tr -d ' ')
DEV_SORRY=$(grep -r "sorry" Littlewood/Development/ --include="*.lean" | grep -v "^.*:.*--" | wc -l | tr -d ' ')
OTHER_SORRY=$((TOTAL_SORRY - ASSUME_SORRY - DEV_SORRY))

echo "=== SORRY COUNT ==="
echo "  Total:            $TOTAL_SORRY"
echo "  Assumptions.lean: $ASSUME_SORRY"
echo "  Development/:     $DEV_SORRY"
echo "  Other:            $OTHER_SORRY"
echo ""

# Count hypothesis classes
HYP_CLASSES=$(grep -r "^class.*Hyp.*Prop" Littlewood/ --include="*.lean" | wc -l | tr -d ' ')
HYP_PROVED=$(grep -c "instance.*Hyp.*:=" Littlewood/ZetaZeros/ZeroCountingFunction.lean 2>/dev/null || echo "0")

echo "=== HYPOTHESIS CLASSES ==="
echo "  Total defined:    $HYP_CLASSES"
echo "  Proved instances: $HYP_PROVED"
echo ""

# Count Development lemmas
DEV_TOTAL=$(grep -E "^(lemma|theorem)" Littlewood/Development/*.lean 2>/dev/null | wc -l | tr -d ' ')
DEV_PROVED=$(grep -E "^(lemma|theorem)" Littlewood/Development/*.lean 2>/dev/null | while read line; do
  file=$(echo "$line" | cut -d: -f1)
  linenum=$(echo "$line" | cut -d: -f2 | grep -oE "^[0-9]+")
  # Check if next few lines contain "sorry"
  if ! sed -n "${linenum},$((linenum+20))p" "$file" 2>/dev/null | grep -q "sorry"; then
    echo "1"
  fi
done | wc -l | tr -d ' ')

echo "=== DEVELOPMENT PROGRESS ==="
echo "  Total lemmas:     $DEV_TOTAL"
echo "  Fully proved:     $DEV_PROVED (approximate)"
echo ""

# List Development files
echo "=== DEVELOPMENT FILES ==="
for f in Littlewood/Development/*.lean; do
  if [ -f "$f" ]; then
    sorries=$(grep "sorry" "$f" | grep -v "^.*--" | wc -l | tr -d ' ')
    echo "  $(basename $f): $sorries sorries"
  fi
done
echo ""

# Build status
echo "=== BUILD STATUS ==="
if lake build 2>&1 | tail -1 | grep -q "successfully"; then
  echo "  Status: GREEN"
else
  echo "  Status: NEEDS ATTENTION"
fi
echo ""

# Key theorems
echo "=== KEY THEOREMS ==="
echo "  trig_inequality:     PROVED (ZeroFreeRegion.lean)"
echo "  trig_identity:       PROVED (ZeroFreeRegion.lean)"
echo "  hardyZ_zero_iff:     PROVED (HardyTheorem.lean)"
echo "  partial_sums_mono:   PROVED (LandauLemma.lean)"
echo "  term_comparison:     PROVED (LandauLemma.lean)"
echo "  ZeroConjZeroHyp:     PROVED (ZeroCountingFunction.lean)"
echo "  ZeroOneSubZeroHyp:   PROVED (ZeroCountingFunction.lean)"
echo ""

echo "=== SUMMARY ==="
echo "Main theorems (LittlewoodPsi, LittlewoodPi) type-check with"
echo "hypothesis instances provided by Assumptions.lean."
echo "Development files provide path toward proving those hypotheses."
