#!/usr/bin/env bash
# Build the differential oracle from PUBLIC SOURCES.  Idempotent; see
# docs/ORACLE-SETUP.md for the measured lane and what to expect.
set -euo pipefail
cd "$(dirname "$0")/.."
VENDOR="$PWD/vendor"
mkdir -p "$VENDOR"

command -v sbcl >/dev/null || brew install sbcl
sbcl --version

# ⛔ PINNED (D218). This used to clone whatever HEAD was, and no record named the commit, so every
#   differential figure was agreement with an unnamed x86isa. The sha lives in ONE place.
REV=$(grep -vE '^\s*(#|$)' scripts/oracle_revision.txt | head -1 | tr -d '[:space:]')
if [ ! -d "$VENDOR/acl2" ]; then
  git init -q "$VENDOR/acl2"
  git -C "$VENDOR/acl2" remote add origin https://github.com/acl2/acl2.git
  git -C "$VENDOR/acl2" fetch --depth 1 origin "$REV"
  git -C "$VENDOR/acl2" checkout -q FETCH_HEAD
fi
bash scripts/check_oracle_revision.sh    # refuses a tree at any other commit
cd "$VENDOR/acl2"

if [ ! -x saved_acl2 ]; then
  make LISP="$(command -v sbcl)" -j"${J:-2}"
fi
ls -l saved_acl2

cd books
export ACL2="$VENDOR/acl2/saved_acl2"
make -j"${J:-5}" ACL2="$ACL2" projects/x86isa/top.cert
echo "oracle ready: x86isa certified against $(cd .. && git rev-parse --short HEAD)"
