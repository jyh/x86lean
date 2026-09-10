#!/usr/bin/env bash
# The CI axiom ALLOWLIST over the model library (plan v1 §3.6, TRUSTBASE.md).
# Every declaration in `X86` may depend on exactly {propext, Classical.choice,
# Quot.sound}.  Not a denylist: see AxiomGate.lean for why a denylist cannot work.
#
# ⛔⛔ THE MODULE LIST IS DERIVED FROM `X86.lean`, NOT WRITTEN HERE. Until
# 2026-09-10 it was a hand-maintained literal of twelve module names, and on the
# day `X86.Program` was added to the library the gate ran, did not cover it, and
# printed:
#     axiom-gate: CLEAN — every declaration in [ …the twelve… ]
# ⇒ 🔑 *A GATE NAMED BY A LITERAL STOPS SEEING NEW WORK, AND REPORTS CLEAN ABOUT
# THE HALF IT CAN STILL SEE.* The banner even NAMED its scope, and a reader who
# did not know the library had thirteen modules had nothing to compare it to.
# `X86.lean` is the library root and must import every module for `lake build
# X86` to build it, so its import list is the population — derived, it cannot
# drift from the thing it gates.
set -euo pipefail
cd "$(dirname "$0")/.."

MODS="X86 $(grep -E '^import X86\.' X86.lean | awk '{print $2}' | tr '\n' ' ')"

# ── the control: a derivation that silently yields nothing would pass ────────
# An empty or truncated list makes the gate vacuous, and vacuous reads GREEN.
n=$(printf '%s\n' $MODS | wc -l | tr -d ' ')
if [ "$n" -lt 5 ]; then
  echo "axiom-gate: REFUSED — derived only $n module(s) from X86.lean; expected the" >&2
  echo "  whole library. A short list would make this gate vacuous. Not run." >&2
  exit 2
fi
for required in X86.Semantics X86.Theorems; do
  case " $MODS " in
    *" $required "*) ;;
    *) echo "axiom-gate: REFUSED — derived list is missing $required, so the" >&2
       echo "  derivation is not reading X86.lean's imports correctly." >&2
       exit 2 ;;
  esac
done

lake build X86 x86lean-axioms >/dev/null
exec lake env .lake/build/bin/x86lean-axioms $MODS
