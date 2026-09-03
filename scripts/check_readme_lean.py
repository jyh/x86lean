#!/usr/bin/env python3
"""⭐⭐ EVERY ```lean BLOCK IN README.md IS COMPILED.

WHY.  The README is the most-read file in the repository and, since the P1 seal,
the first thing a reader of the GitHub remote sees.  Its Lean block is an
INVITATION: a reader copies it to find out whether this model is usable.  A block
that does not compile is the repository's own recorded defect class arriving in
the one file where it costs the most — a claim that reads as evidence and that no
gate reads ([[feedback-a-citation-is-an-ungated-claim]]).

⛔ AND IT HAPPENED.  The block landed at the seal did not compile: it opened with
`open X86` and no `import X86`, so a reader pasting it got four errors, the first
being `unknown namespace X86`.  The head that wrote it had just corrected THREE
errors of exactly this kind in the description draft it replaced — a wrong CLI
mode, a theorem name that does not exist, a residual list naming a row that is
not in the residue — and then shipped a fourth.
⇒ 🔑 **CORRECTING A CLASS OF ERROR IN SOMEBODY ELSE'S DRAFT DOES NOT INOCULATE
YOUR OWN**, and the only thing that would have caught it is the thing that
catches it now: running it.

⚠️ WHAT THIS DOES NOT CHECK: that the example is INTERESTING, or that it says
what the prose around it claims.  It checks that a reader who copies it gets a
file that compiles.  The limit is stated rather than left to be found.

Usage:  check_readme_lean.py [--selftest]
"""
import os, re, sys, subprocess, tempfile

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)

def blocks(text):
    return re.findall(r"```lean\n(.*?)```", text, re.S)

# ⚠️ NOT EVERY ```lean BLOCK IS A PROGRAM, and pretending otherwise makes this
# gate cry wolf on prose.  The README carries SHAPES on purpose — `def step
# (i : Instr) (s : Cpu) : Cpu` with no body, `step i s = { s with … }` with a
# literal ellipsis — because they say what the semantics LOOKS like, and a
# reader is not meant to paste them.
#
# ⛔ BUT "SKIP WHAT DOES NOT COMPILE" WOULD BE A GATE THAT SKIPS ITS OWN
# SUBJECT.  The rule is by INTENT, not by outcome: a block that declares an
# `example`/`theorem`/`#eval` is offered as runnable, and one of those WITHOUT an
# `import` is a FINDING rather than a fragment — that is exactly the block that
# shipped broken at the seal, and "it did not compile so I skipped it" would have
# passed it.
RUNNABLE_RE = re.compile(r"^\s*(example|theorem|lemma|#eval|#check)\b", re.M)

def classify(b):
    runnable = bool(RUNNABLE_RE.search(b))
    has_import = bool(re.match(r"\s*import\b", b))
    if runnable and has_import:
        return "compile"
    if runnable:
        return "finding"      # looks runnable, cannot be: no import
    return "fragment"

def compile_block(src):
    d = tempfile.mkdtemp(prefix="x86lean-readme-")
    f = os.path.join(d, "Block.lean")
    open(f, "w").write(src)
    r = subprocess.run(["lake", "env", "lean", f],
                       capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip()
    # ⚠️ `lean` exits 0 on a `sorry` warning, so the text is checked too: a
    # block closed by `sorry` compiles and proves nothing.
    #
    # ⛔ AND THE FIRST SPELLING OF THIS TEST WAS WRONG.  It looked for
    # `declaration uses 'sorry'` with straight quotes; Lean emits
    # ``declaration uses `sorry` `` with BACKTICKS, so the check never fired and
    # a `sorry`-closed block would have passed this gate. The arm that plants
    # one is the only reason it is known — a gate's own selftest catching the
    # gate is the arm doing exactly its job.
    # ⇒ 🔑 A PATTERN IS A GUESS ABOUT WORDING UNTIL SOMETHING DRIVES IT.
    bad = (r.returncode != 0 or "error" in out
           or re.search(r"declaration uses .?sorry", out) is not None)
    return (not bad), out

def main():
    text = open("README.md").read()
    bs = blocks(text)
    if not bs:
        print("⛔ README.md has no ```lean block. A gate that cannot find its "
              "subject reports a pass; this one reports a failure.")
        return 2
    if "--selftest" in sys.argv:
        # RED FIRST, both ways: a broken block must fail, and the SHIPPED
        # blocks must pass — a gate that only goes red is stuck, not working.
        ok, _ = compile_block(bs[0] + "\nexample : (1 : Nat) = 2 := rfl\n")
        print(("  ✔ " if not ok else "  ⛔ ") +
              "a block with a false claim is REJECTED")
        ok2, _ = compile_block(bs[0] + "\nexample : (1 : Nat) = 1 := by sorry\n")
        print(("  ✔ " if not ok2 else "  ⛔ ") +
              "a block closed by `sorry` is REJECTED")
        ok3, out3 = compile_block(bs[0])
        print(("  ✔ " if ok3 else "  ⛔ ") + "the SHIPPED block compiles")
        if not ok3:
            print("      " + out3[:400].replace("\n", "\n      "))
        # and a README with no block at all must refuse, not pass
        no = blocks("# nothing here\n")
        print(("  ✔ " if not no else "  ⛔ ") +
              "a README with no lean block yields nothing to check")
        # ⭐ THE CLASSIFIER, DRIVEN ON THE THREE CASES IT EXISTS TO SEPARATE —
        # including the one that actually shipped broken.
        cls = [("a fragment with no declaration is skipped",
                "def step (i : Instr) (s : Cpu) : Cpu", "fragment"),
               ("an ellipsis shape is skipped",
                "step i s = { s with \u2026 }", "fragment"),
               ("an `example` WITHOUT an import is a FINDING, not a skip",
                "open X86\nexample : True := trivial", "finding"),
               ("an `example` WITH an import is compiled",
                "import X86\nexample : True := trivial", "compile")]
        cbad = 0
        for name, src, want in cls:
            got = classify(src)
            good = got == want
            cbad += (not good)
            print(("  ✔ " if good else "  ⛔ ") + name +
                  ("" if good else f"   got {got}, want {want}"))
        bad = ok or ok2 or (not ok3) or bool(no) or cbad
        print("readme-lean selftest: " + ("FAIL" if bad else "PASS (8 arms)"))
        return 1 if bad else 0
    fail, n_c, n_f = 0, 0, 0
    for i, b in enumerate(bs, 1):
        kind = classify(b)
        first = b.strip().splitlines()[0][:56] if b.strip() else ""
        if kind == "fragment":
            n_f += 1
            print(f"  · block {i}: illustrative fragment, not compiled  "
                  f"({first})")
            continue
        if kind == "finding":
            fail += 1
            print(f"  ⛔ block {i} declares an `example`/`theorem` but has NO "
                  f"`import` — it reads as runnable and is not.  ({first})")
            continue
        n_c += 1
        ok, out = compile_block(b)
        print(("  ✔ " if ok else "  ⛔ ") + f"block {i} compiles "
              f"({len(b.splitlines())} lines)")
        if not ok:
            fail += 1
            print("      " + out[:600].replace("\n", "\n      "))
    if n_c == 0:
        print("⛔ no RUNNABLE lean block found in README.md. The example a "
              "reader is invited to copy is the thing this gate exists for; if "
              "there is none, say so deliberately rather than passing.")
        return 2
    if fail:
        print(f"⛔ readme-lean gate FAILED ({fail} block(s)). A reader who "
              f"copies one gets those errors.")
        return 1
    print(f"readme-lean gate: CLEAN — {n_c} runnable block(s) compile, "
          f"{n_f} illustrative fragment(s) skipped by intent (they declare "
          f"nothing).")
    return 0

sys.exit(main())
