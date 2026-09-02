#!/usr/bin/env bash
# ⭐ THE RED-FIRST DRIVE.  A gate that has never been observed to FAIL is not
# known to be a gate.  `X86Native.addByteZf_native` really uses `native_decide`,
# so it really carries an axiom outside the allowlist; the gate must fire on it.
#
# This is not ceremony.  On Lean >= 4.29 a `native_decide` mints a FRESH
# per-computation axiom name (measured on 4.32.0-rc1: the axiom introduced here
# is `X86Native.addByteZf_native._native.native_decide.ax_1_1`, NOT
# `Lean.ofReduceBool`), so the denylist most projects would have written passes
# this file in silence.  The allowlist cannot miss a name it has never heard of,
# and this script is the evidence that it does not.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build X86Native x86lean-axioms >/dev/null
exec lake env .lake/build/bin/x86lean-axioms --expect-violation X86Native
