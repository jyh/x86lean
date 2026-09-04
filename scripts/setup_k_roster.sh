#!/usr/bin/env bash
# The SECOND public source, fetched the cheap way.
#
# Plan v1 §2 names the K x86-64 semantics (NCSA, © 2019 UIUC) as the COVERAGE
# TARGET LIST, and `scripts/k_roster.py` derives P1's roster and batch partition
# from it.  A full clone is 2.8 GB — but 2.6 GB of that is `tests/`, and the
# roster reads only `semantics/`, which is 15 MB.  A blobless sparse checkout
# therefore turns "too big for CI" into a fifteen-second job, which is why the
# roster gate can run on every push instead of on one developer's machine.
# MEASURED 09/04 at K `592380ae`, the first time this branch had ever run to
# success anywhere: clone 1.3 s, working tree 21 MB = semantics 15 MB + .git
# 5.8 MB.  (The 15 MB above is the semantics tree, and it is right; the number
# a CI runner pays for is the 21 MB.)
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
  # ⛔⛔ NO `LICENSE.md` IN THIS SET, AND THAT IS THE REPAIR (D104). Naming a
  # FILE in a CONE-mode pattern list is fatal — `fatal: 'LICENSE.md' is not a
  # directory` — because cone patterns are directory prefixes. The licence
  # still arrives: cone mode materialises the repository ROOT's files
  # unconditionally, so `clone --sparse` has already written LICENSE.md before
  # any pattern is set. The pattern was REDUNDANT, not merely wrong, which is
  # why neither `--skip-checks` nor no-cone mode is needed here.
  git -C "$DEST" sparse-checkout set semantics
fi
# The two properties this recipe actually promises, each asserted rather than
# assumed — the clone branch above runs only on a machine that has no tree yet,
# so a developer's box (which takes the branch above it) can never witness them.
test -d "$DEST/semantics/registerInstructions" || {
  echo "⛔ $DEST/semantics is missing — the sparse checkout did not take" >&2; exit 2; }
test -s "$DEST/LICENSE.md" || {
  echo "⛔ $DEST/LICENSE.md is missing — this repository READS an NCSA-licensed" >&2
  echo "   source and PROVENANCE.md cites that file; fetching the semantics" >&2
  echo "   without the licence beside them is the one outcome not allowed." >&2; exit 2; }
echo "K commit $(git -C "$DEST" rev-parse HEAD)"
du -sh "$DEST" 2>/dev/null || true
