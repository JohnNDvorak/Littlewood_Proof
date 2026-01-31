#!/bin/bash
# Quick intake script for new Aristotle files
# Usage: ./intake.sh <filename.lean>

FILE=$1

if [ -z "$FILE" ]; then
  echo "Usage: ./intake.sh <filename.lean>"
  exit 1
fi

echo "=== INTAKE: $FILE ==="

echo ""
echo "### Sorry count ###"
grep -c "sorry" "$FILE"

echo ""
echo "### exact? count ###"
grep -c "exact?" "$FILE"

echo ""
echo "### Namespace ###"
grep "^namespace" "$FILE"

echo ""
echo "### Imports ###"
grep "^import" "$FILE"

echo ""
echo "### Definitions ###"
grep -E "^def |^noncomputable def " "$FILE"

echo ""
echo "### Theorems/Lemmas ###"
grep -E "^theorem |^lemma " "$FILE"

echo ""
echo "### Potential conflicts (check against existing) ###"
grep -E "^def |^noncomputable def " "$FILE" | sed 's/def \([^ ]*\).*/\1/' | while read name; do
  matches=$(grep -rl "def $name " Littlewood/Aristotle/*.lean 2>/dev/null | wc -l)
  if [ "$matches" -gt 0 ]; then
    echo "  WARNING: '$name' already defined in $matches file(s)"
  fi
done

echo ""
echo "### Build test ###"
cd "$(dirname "$0")/../.." 2>/dev/null || cd .
lake env lean "$FILE" 2>&1 | tail -10
