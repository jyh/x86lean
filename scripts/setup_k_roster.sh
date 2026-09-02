#!/usr/bin/env bash
# The SECOND public source, fetched the cheap way.
#
# Plan v1 §2 names the K x86-64 semantics (NCSA, © 2019 UIUC) as the COVERAGE
# TARGET LIST, and `scripts/k_roster.py` derives P1's roster and batch partition
# from it.  A full clone is 2.8 GB — but 2.6 GB of that is `tests/`, and the
# roster reads only `semantics/`, which is 15 MB.  A blobless sparse checkout
# therefore turns "too big for CI" into a fifteen-second job, which is why the
# roster gate can run on every push instead of on one developer's machine.
#
# Idempotent.  The tree is gitignored: this recipe is what the repository
# carries, never the tree (docs/ORACLE-SETUP.md makes the same choice for ACL2).
set -euo pipefail
cd "$(dirname "$0")/.."
DEST=${1:-vendor/k-x86-64}
REPO=https://github.com/kframework/X86-64-semantics.git

if [ -d "$DEST/.git" ]; then
  echo "K tree already at $DEST ($(git -C "$DEST" rev-parse --short HEAD))"
else
  git clone --filter=blob:none --sparse --depth 1 "$REPO" "$DEST"
  git -C "$DEST" sparse-checkout set semantics LICENSE.md
fi
test -d "$DEST/semantics/registerInstructions" || {
  echo "⛔ $DEST/semantics is missing — the sparse checkout did not take" >&2; exit 2; }
echo "K commit $(git -C "$DEST" rev-parse HEAD)"
du -sh "$DEST" 2>/dev/null || true
