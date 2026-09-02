#!/usr/bin/env bash
# NOTHING IN THE MODEL LIBRARY MAY IMPORT THE NATIVE TIER (plan v1 §3.3).
# The axiom gate catches the CONSEQUENCE (a native axiom reaching a main-tier
# theorem); this catches the CAUSE, and names it in one line rather than as a
# list of tainted theorems.
#
# It tests for an IMPORT, not for the string `X86Native`.  A first draft grepped
# for the string and failed on this repository's own prose — the sentence in
# X86.lean that TELLS the reader the tier is excluded was read as the violation.
# In Lean a module cannot reference a declaration it has not imported, so the
# import line is the whole of the property, and matching prose is noise that
# trains a reader to ignore the gate.
set -euo pipefail
cd "$(dirname "$0")/.."
if grep -rnE '^[[:space:]]*import[[:space:]]+X86Native' --include='*.lean' X86/ X86.lean 2>/dev/null; then
  echo "⛔ tier isolation VIOLATED: the model library IMPORTS the native tier (above)." >&2
  exit 1
fi
echo "tier isolation: CLEAN — no module under X86/ imports X86Native"
grep -qE '^[[:space:]]*import[[:space:]]+X86$' X86Native.lean \
  || { echo "⛔ X86Native must import X86" >&2; exit 1; }
echo "tier isolation: X86Native imports X86, as the tier's definition requires"
