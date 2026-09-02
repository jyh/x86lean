#!/usr/bin/env bash
# The CI axiom ALLOWLIST over the model library (plan v1 §3.6, TRUSTBASE.md).
# Every declaration in `X86` may depend on exactly {propext, Classical.choice,
# Quot.sound}.  Not a denylist: see AxiomGate.lean for why a denylist cannot work.
set -euo pipefail
cd "$(dirname "$0")/.."
MODS="X86 X86.Basic X86.Value X86.Oracle X86.Memory X86.State X86.Syntax X86.Flags \
X86.Semantics X86.Theorems X86.Coverage X86.Serialize"
lake build X86 x86lean-axioms >/dev/null
exec lake env .lake/build/bin/x86lean-axioms $MODS
