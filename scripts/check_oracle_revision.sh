#!/usr/bin/env bash
# Refuse to run the differential against a reference model at an unpinned revision.
#
# WHY (D218, docs/TACAS-G5-ARTIFACT.md §1): setup_oracle.sh used to shallow-clone ACL2 at whatever HEAD
# was, and no differential record named the commit it ran against, so every agreement figure was
# agreement with an UNNAMED x86isa. A disagreement against an unpinned oracle cannot be attributed: an
# upstream fix to x86isa (D108) would make declared divergences stop diverging, and the run would go red
# for a reason no record could show.
#
# Prints `reference-model: acl2@<sha>` on success, so a run's output carries the revision.
# Exit 0 = the vendor tree is at the pinned sha. Exit 2 = refused, with what it saw.
# Env for testing only: ORACLE_REV_FILE (default scripts/oracle_revision.txt), ACL2_DIR (default vendor/acl2).
set -uo pipefail
cd "$(dirname "$0")/.."
REV_FILE=${ORACLE_REV_FILE:-scripts/oracle_revision.txt}
DIR=${ACL2_DIR:-vendor/acl2}
want=$(grep -vE '^\s*(#|$)' "$REV_FILE" 2>/dev/null | head -1 | tr -d '[:space:]')
if ! [[ "$want" =~ ^[0-9a-f]{40}$ ]]; then
  echo "⛔ check_oracle_revision: $REV_FILE does not carry one 40-hex sha (read: '${want}') — refusing" >&2
  exit 2
fi
if [ ! -d "$DIR/.git" ]; then
  echo "⛔ check_oracle_revision: no git tree at $DIR — run scripts/setup_oracle.sh; refusing, not skipping" >&2
  exit 2
fi
have=$(git -C "$DIR" rev-parse HEAD 2>/dev/null || echo "<unreadable>")
if [ "$have" != "$want" ]; then
  echo "⛔ check_oracle_revision: $DIR is at $have but $REV_FILE pins $want." >&2
  echo "   A differential run against another revision is agreement with a different model." >&2
  echo "   Check out the pin, or change the pin in a commit that says why." >&2
  exit 2
fi
if [ -n "$(git -C "$DIR" status --porcelain --untracked-files=no 2>/dev/null)" ]; then
  echo "⛔ check_oracle_revision: $DIR is at the pinned sha but has MODIFIED tracked files — refusing" >&2
  exit 2
fi
echo "reference-model: acl2@$want"
