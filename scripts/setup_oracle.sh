#!/usr/bin/env bash
# Build the differential oracle from PUBLIC SOURCES.  Idempotent; see
# docs/ORACLE-SETUP.md for the measured lane and what to expect.
set -euo pipefail
cd "$(dirname "$0")/.."
VENDOR="$PWD/vendor"
mkdir -p "$VENDOR"

command -v sbcl >/dev/null || brew install sbcl
sbcl --version

if [ ! -d "$VENDOR/acl2" ]; then
  git clone --depth 1 https://github.com/acl2/acl2.git "$VENDOR/acl2"
fi
cd "$VENDOR/acl2"
echo "ACL2 HEAD: $(git rev-parse HEAD)"

if [ ! -x saved_acl2 ]; then
  make LISP="$(command -v sbcl)" -j"${J:-2}"
fi
ls -l saved_acl2

cd books
export ACL2="$VENDOR/acl2/saved_acl2"
make -j"${J:-5}" ACL2="$ACL2" projects/x86isa/top.cert
echo "oracle ready: x86isa certified against $(cd .. && git rev-parse --short HEAD)"
