#!/bin/bash
# Littlewood Formalization Status Script
# Run from project root: ./scripts/status.sh

echo "=== Littlewood Formalization Status ==="
echo "Generated: $(date)"
echo ""

echo "=== File Counts ==="
echo "  Total .lean files:    $(find Littlewood -name '*.lean' | wc -l | tr -d ' ')"
echo "  Aristotle files:      $(find Littlewood/Aristotle -name '*.lean' 2>/dev/null | wc -l | tr -d ' ')"
echo "  Main/ files:          $(find Littlewood/Main -name '*.lean' 2>/dev/null | wc -l | tr -d ' ')"
echo "  Development/ files:   $(find Littlewood/Development -name '*.lean' 2>/dev/null | wc -l | tr -d ' ')"
echo ""

echo "=== Sorry Counts ==="
echo "  Main/ sorries:        $(grep -r '^[[:space:]]*sorry' Littlewood/Main/*.lean 2>/dev/null | wc -l | tr -d ' ')"
echo "  Aristotle/ sorries:   $(grep -r '^[[:space:]]*sorry' Littlewood/Aristotle/*.lean 2>/dev/null | wc -l | tr -d ' ')"
echo "  Development/ sorries: $(grep -r '^[[:space:]]*sorry' Littlewood/Development/*.lean 2>/dev/null | wc -l | tr -d ' ')"
echo "  Assumptions.lean:     $(grep -c '^[[:space:]]*sorry' Littlewood/Assumptions.lean 2>/dev/null || echo 0)"
echo ""

echo "=== Aristotle File Detail ==="
for f in Littlewood/Aristotle/*.lean; do
  count=$(grep -c '^[[:space:]]*sorry' "$f" 2>/dev/null)
  # Handle empty output from grep -c
  if [ -z "$count" ]; then
    count=0
  fi
  # Convert to integer by removing any whitespace
  count=$(echo "$count" | tr -d '[:space:]')
  if [ "$count" -gt 0 ] 2>/dev/null; then
    echo "  $count sorries: $(basename "$f")"
  fi
done
echo ""

echo "=== Sorry-Free Aristotle Files ==="
sorry_free=0
total=0
for f in Littlewood/Aristotle/*.lean; do
  total=$((total + 1))
  count=$(grep -c '^[[:space:]]*sorry' "$f" 2>/dev/null)
  if [ -z "$count" ]; then
    count=0
  fi
  count=$(echo "$count" | tr -d '[:space:]')
  if [ "$count" -eq 0 ] 2>/dev/null; then
    sorry_free=$((sorry_free + 1))
  fi
done
echo "  $sorry_free / $total files are sorry-free"
echo ""

echo "=== Build Status ==="
if lake build 2>&1 | tail -5; then
  echo "  Build completed"
else
  echo "  Build may have errors - check output above"
fi
