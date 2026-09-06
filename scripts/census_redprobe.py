#!/usr/bin/env python3
"""⭐⭐ THE RED PROBE FOR THE CENSUS SELFTEST.

A selftest that has never been seen to FAIL is a selftest whose arms may be
testing nothing.  This probe breaks each rule the assembly column class rests on
— one at a time, in memory — and REQUIRES the selftest to go red.  A mutation
that leaves it green is a finding about the ARM, not about the mutation
([[feedback-probe-silence-has-two-causes]]).

⛔ IT WRITES NOTHING INTO THE REPOSITORY TREE.  The mutated source is executed
from a string with `__file__` pointed at the real script, so `root` still
resolves to the repo and `docs/COVERAGE.md` is still the model — but no mutated
file ever exists on disk, so an interrupted probe cannot leave one behind
(the P1 seal paid for that lesson with an EXIT trap that SIGKILL does not run).

⚠️ AND IT CARRIES A CONTROL: the unmutated source must go GREEN in the same
harness, or a red proves only that the harness is broken
([[feedback-a-probe-must-create-its-condition]]).
"""
import io, os, sys, contextlib

HERE = os.path.dirname(os.path.abspath(__file__))
TARGET = os.path.join(HERE, "demand_census.py")

# (label, needle, replacement) — each breaks exactly one rule
MUTATIONS = [
    ("MMX is no longer excluded (the over-claim this class found)",
     r'%[xyz]mm|%mm[0-7]\b|%k[0-7]\b|%st', r'%[xyz]mm|%k[0-7]\b|%st'),
    ("a shipped symlink counts as a second binary",
     "if os.path.islink(p) or not is_elf_x86_64(p):",
     "if not is_elf_x86_64(p):"),
    ("scalar floating point counts as packed SIMD",
     'SCALAR_FP = re.compile(r"(ss|sd)$")',
     'SCALAR_FP = re.compile(r"(?!x)x")'),
    ("the body route calls everything hand-written",
     'return "A" if n_packed / n_insns >= BODY_PACKED_FRACTION else "C"',
     'return "A"'),
    ("the body route's instruction floor is removed",
     "if n_insns < BODY_MIN_INSNS:", "if n_insns < 0:"),
    ("the name route claims every symbol",
     "        if ISA_COMPONENT.match(comp):\n            return \"A\"\n    return \"C\"",
     "        if ISA_COMPONENT.match(comp):\n            return \"A\"\n    return \"A\""),
    ("the name route matches a SUBSTRING instead of a component",
     "    for comp in re.split(r\"[._@]\", sym):\n        if ISA_COMPONENT.match(comp):",
     "    for comp in re.split(r\"[._@]\", sym):\n        if ISA_COMPONENT.search(comp) or \"sse\" in sym:"),
    ("an address no symbol covers is attributed to the previous function",
     "        return syms[i] if a <= addr < e else None",
     "        return syms[i]"),
    ("a column with NO symbol map reads as compiler output",
     '        if syms is None:\n            return "-"',
     '        if syms is None:\n            return "CC"'),
    ("a LOCK-prefixed instruction is priced as a vector gap, not as the P2 item",
     'if kind == "lock":\n        return "LOCK prefix (P2 addition 2)"',
     'if kind == "lock" and False:\n        return "LOCK prefix (P2 addition 2)"'),
    ("a segment-prefixed instruction is priced as a vector gap",
     'if kind == "segment":\n        return "segment base %fs:/%gs: (P2 addition 1)"',
     'if kind == "segment" and False:\n        return "segment base %fs:/%gs: (P2 addition 1)"'),
    ("the ISA bucket default is a silent \"other\"",
     'return GPR_EXT.get(base, "GPR/other (unclassified)")',
     'return GPR_EXT.get(base, "other")'),
    ("the %fs:/%gs: narrowing is widened back to all six segments",
     'SEGMENT_RE = re.compile(r"%(?:fs|gs):")',
     'SEGMENT_RE = re.compile(r"%(?:cs|ds|es|ss|fs|gs):")'),
    ("a run of int3 is counted as code again",
     "        if run >= 2:", "        if run >= 999999999:"),

    # ⭐⭐ D98'S OWN DEFECT AND ITS TWO FAILURE DIRECTIONS.  The repair widened
    # what counts as covered, and widening is the direction nobody audits: an
    # over-claim looks like a mistake, an under-claim looks like modesty
    # ([[feedback-under-claims-are-unpoliced]]).  So both directions are planted
    # here, and each must go RED.
    #
    # THE UNDER-CLAIM — this is D98 exactly: the mapping's vector half is a
    # second list that does not grow with the roster, so a batch that adds
    # `movdqa` moves the headline by +0.0%.  It went unseen for twenty-two
    # batches because a stale number is silent.
    ("the identity rule is removed — the mapping stops seeing the model (D98)",
     "    if model is not None and m in model:\n        return m\n    return None",
     "    return None"),
    ("the vector spelling no longer wins — `movq %xmm0,%rax` resolves as `mov`",
     "    if model is not None and ext in XMM_EXT and m in model:\n        return m",
     "    if False:\n        return m"),
    ("`movabsq` stops mapping to the `mov` P2 batch 3 landed",
     '    "movabsq":"mov", "movabs":"mov",', '    "movabsq":None, "movabs":None,'),

    # THE OVER-CLAIM — the direction the repair could newly fail in, one
    # register file at a time.  A model with no MMX, no AVX and no VEX
    # encoding must not be credited with them because the MNEMONIC matches.
    ("MMX is admitted into scope — `paddw %mm0,%mm1` counts as covered",
     '    "MMX (mm)":                               False,',
     '    "MMX (mm)":                               True,'),
    ("AVX2 is admitted into scope — a `%ymm` operand counts as covered",
     '    "AVX2/AVX (ymm)":                         False,',
     '    "AVX2/AVX (ymm)":                         True,'),
    ("the VEX encoding is admitted into scope",
     '    "VEX-128 (v… xmm)":                       False,',
     '    "VEX-128 (v… xmm)":                       True,'),
    ("x87 is admitted into scope",
     '    "x87 (st)":                               False,',
     '    "x87 (st)":                               True,'),
    ("the LOCK refusal is quietly lifted, claiming forms that are #UD",
     '    "LOCK prefix (P2 addition 2)":            False,',
     '    "LOCK prefix (P2 addition 2)":            True,'),
    # ⛔ AND THE PARTITION'S OWN FAILURE MODE: a bucket nobody ruled on must
    # STOP the census.  A default there is invisible by construction, so it gets
    # a mutation in EACH direction rather than a comment — an allow-list would
    # over-claim it and a deny-list would under-claim it, and the arm has to
    # distinguish REFUSING from both.
    #
    # ⚠️ THESE TWO REPLACE A PAIR THAT DID NOT WORK, AND THE PROBE SAID SO.  The
    # first attempt mutated `return EXT_SCOPE[ext]` into `.get(ext, False)` —
    # unreachable, because the refusal above it has already fired, so the
    # mutation was INERT and the probe reported "THE ARM IS BLIND" about an arm
    # that was fine.  ⇒ 🔑 A MUTATION THAT CHANGES NO BEHAVIOUR ACCUSES THE ARM,
    # and the accusation reads exactly like a real finding
    # ([[feedback-probe-silence-has-two-causes]]).  The anchor is the REFUSAL
    # itself, which is the only line that can express either direction.
    ("an unruled ISA bucket falls to COVERED instead of refusing",
     """f"number for a model nobody described. Add it to EXT_SCOPE.")
        sys.exit(2)""",
     """f"number for a model nobody described. Add it to EXT_SCOPE.")
        return True"""),
    ("an unruled ISA bucket falls to NOT COVERED instead of refusing",
     """f"number for a model nobody described. Add it to EXT_SCOPE.")
        sys.exit(2)""",
     """f"number for a model nobody described. Add it to EXT_SCOPE.")
        return False"""),

    # ⭐ AND THE STAMP THAT COULD NOT SEE ANY OF THE ABOVE.  With the rules half
    # welded to the model half, every mutation on this list becomes invisible to
    # the gate that is supposed to notice the document has gone stale.
    ("the stamp hashes only the model again, as it did through D98",
     '    rh = hashlib.sha256("\\n".join(rows).encode()).hexdigest()[:16]',
     "    rh = h"),
    # ⛔ and the DUPLICATE the repair deleted: `ext_table` carried its own copy
    # of the covered test for twenty-two batches and agreed the whole time.
    ("`ext_table` grows a second copy of the covered/not-covered test",
     "        _r, covered, _cls = _decide(m, ext, model)",
     '        _r = to_roster(m, ext, model)\n'
     '        covered = (_r is not None and _kind == "plain" and _r in model)'),
]


def run(src):
    """Execute a source string as the census script with --selftest.
    Returns (exit_code, output)."""
    g = {"__name__": "__main__", "__file__": TARGET}
    buf = io.StringIO()
    argv = sys.argv
    sys.argv = ["demand_census.py", "--selftest"]
    try:
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            try:
                exec(compile(src, TARGET, "exec"), g)
                code = 0
            except SystemExit as e:
                code = e.code if isinstance(e.code, int) else 1
    finally:
        sys.argv = argv
    return code, buf.getvalue()


def main():
    src = open(TARGET).read()
    bad = []
    code, out = run(src)
    ok = code == 0
    print(("  ✔ " if ok else "  ⛔ ") +
          "CONTROL: the UNMUTATED selftest is GREEN in this harness"
          + ("" if ok else f" (exit {code})\n" + out[-1500:]))
    if not ok:
        print("census red probe: FAIL — the harness cannot report green, so no "
              "red below means anything.")
        return 1
    for label, needle, repl in MUTATIONS:
        if src.count(needle) != 1:
            print(f"  ⛔ ANCHOR MISSING ({src.count(needle)} hits): {label}")
            bad.append(label)
            continue
        code, out = run(src.replace(needle, repl))
        red = code != 0
        print(("  ✔ " if red else "  ⛔ ") +
              f"{label} -> selftest {'FAILS (caught)' if red else 'still PASSES — THE ARM IS BLIND'}")
        if not red:
            bad.append(label)
    if bad:
        print(f"census red probe: FAIL ({len(bad)} of {len(MUTATIONS)} mutations "
              f"were not caught)")
        return 1
    print(f"census red probe: PASS (control + {len(MUTATIONS)} mutations, every "
          f"one of them caught)")
    return 0



# ⛔ GUARDED (D151's sweep).  An unguarded `sys.exit(main())` means `import <this
# module>` RUNS the tool and then exits the importer — `kernel_cost.py` cost a
# two-minute profiling pass and a killed probe before this was noticed, and
# `kernel_delta.py` had already been given the same guard by D148.  Two prior
# namings and the siblings were never swept for.
# [[feedback-naming-a-defect-is-not-finding-its-siblings]]
if __name__ == "__main__":
    sys.exit(main())
