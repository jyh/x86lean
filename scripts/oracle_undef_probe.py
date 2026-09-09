#!/usr/bin/env python3
"""MEASURE THE ORACLE — what x86isa EXECUTES, and where it draws UNDEFINED bits.

WHY THIS EXISTS.  Two standing lessons of this repository, made cheap enough to
obey.

  D36: measure the oracle by EXECUTING it, never by reading its catalogue.  The
  catalogue struck `lzcnt` and `blsi` off and both are executed; nine BMI forms
  are in the catalogue and all nine refuse.  Every batch since has priced its
  forms by running them, and nine seconds of probe has repeatedly bought a whole
  batch's design.

  ⛔⛔ AND P1 BATCH 18's OWN PROBE WAS BLIND, WHICH IS THE OTHER HALF.  To find
  which fields x86isa fills from its undefined generator, run the SAME cases
  twice with `create-undef` attached to two different functions and diff the
  post-states: a field that moves is undefined, a field that does not is
  committed.  Batch 18's second attachment was `(+ 1000 (nfix x))`.

  **1000 IS EVEN.**  A flag is one bit, x86isa takes it modulo two, and every
  one-bit undefined field kept its parity and came back IDENTICAL.  The table
  read "zero undefined fields" for every form — which looks exactly like a clean,
  decisive answer.

  ⇒ 🔑 A DIFFERENTIAL PROBE'S PERTURBATION MUST BE ABLE TO MOVE THE NARROWEST
  FIELD IT READS.  The offset here is 1, and the reason is this paragraph.

⭐ THE CONTROLS ARE NOT OPTIONAL AND ARE NOT THE CALLER'S JOB.  This script
appends two forms to whatever it is asked to probe:

  CTRLPOS  `andq %rcx, %rax`   — the SDM leaves AF undefined, and this is the
                                 instruction whose undefined AF first forced the
                                 ACL2 driver's `defattach` to exist at all.  It
                                 MUST come back with `af` undefined in every
                                 case.
  CTRLNEG  `movq %rcx, %rax`   — writes no flag at all.  It MUST come back with
                                 nothing undefined.

If either control fails the script exits 2 and reports NOTHING ELSE, because a
probe that cannot see its own control has not measured the subject — it has
measured its own blindness.  Batch 18's even offset is caught by CTRLPOS in 4.7
seconds.

THE PRE-STATES ARE THE HARNESS'S OWN.  The cases are built by patching the bytes
of the `mov_d` cases inside `run/cases.lsp`, the file `x86lean-diff emit-acl2`
generates, so the states a probe reports on are the states the differential run
will actually use — not a re-implementation of them that can drift.

USAGE
    python3 scripts/oracle_undef_probe.py FORMS.txt [--keep]

    FORMS.txt: one form per line, `id<TAB>AT&T assembly`; `#` comments and blank
    lines ignored.  Example:

        cmpxchg_r_l<TAB>cmpxchgl %edx, %ecx
        shld_r_cl_w<TAB>shldw %cl, %dx, %ax

PUBLIC SOURCE.  clang/LLVM assembles; ACL2 x86isa (BSD-3) executes.  Nothing from
either is copied.
"""
import os, re, subprocess, sys, tempfile, collections
import scratch  # scratch dirs that get removed (591 MB leak, 2026-09-09)

# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS. This script dispatched on
# `"--x" in sys.argv` and otherwise fell through to its main path, so a mistyped
# flag did not fail — it RAN. Measured 2026-09-09: `threads_ab.py` given a bogus
# flag started `lake env lean -D profiler=true`, saturated a core for 300+ s on a
# shared machine, and orphaned past its caller. See portable.strict_flags.
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)

# ⛔ ODD.  See the header.  An even offset cannot flip a one-bit field.
UNDEF_OFFSET = 1

CONTROLS = [("CTRLPOS_and_q", "andq %rcx, %rax", "positive: AF is undefined"),
            ("CTRLNEG_mov_q", "movq %rcx, %rax", "negative: writes no flag")]


def die(msg, code=2):
    print(f"⛔ {msg}", file=sys.stderr)
    sys.exit(code)


def run(cmd):
    return subprocess.run(cmd, shell=True, capture_output=True, text=True)


def read_forms(path):
    forms = []
    for ln in open(path):
        ln = ln.split("#", 1)[0].rstrip("\n")
        if not ln.strip():
            continue
        if "\t" not in ln:
            die(f"form line has no TAB between id and assembly: {ln!r}")
        i, a = ln.split("\t", 1)
        forms.append((i.strip(), a.strip()))
    if not forms:
        die("no forms to probe. A probe with an empty subject is not a pass.")
    return forms


def assemble(forms, tmp):
    src = os.path.join(tmp, "p.s")
    obj = os.path.join(tmp, "p.o")
    with open(src, "w") as f:
        f.write(".text\n")
        for i, a in forms:
            f.write(f"{i}: {a}\n")
    r = run(f"clang -target x86_64-unknown-linux-gnu -c {src} -o {obj}")
    if r.returncode != 0:
        die("the assembler refused a form:\n" + r.stderr)
    r = run(f"objdump -d {obj}")
    if r.returncode != 0:
        die("objdump failed:\n" + r.stderr)
    out, lab = {}, None
    for line in r.stdout.splitlines():
        m = re.match(r"^[0-9a-f]+ <([^>]+)>:", line.strip())
        if m:
            lab = m.group(1)
            continue
        m = re.match(r"^\s*[0-9a-f]+:\s+((?:[0-9a-f]{2} )+)", line)
        if m and lab:
            out[lab] = "".join(m.group(1).split())
            lab = None
    missing = [i for i, _ in forms if i not in out]
    if missing:
        die(f"no instruction assembled at label(s) {missing}")
    return out


def load_pre_states():
    """The 82 `mov_d` cases from the harness's own emitted file."""
    p = "run/cases.lsp"
    if not os.path.exists(p):
        print("── emitting the differential cases (run/cases.lsp is absent) ──")
        if run("lake build x86lean-diff").returncode != 0:
            die("lake build x86lean-diff failed")
        if run(f"lake env .lake/build/bin/x86lean-diff emit-acl2 {p}").returncode != 0:
            die("emit-acl2 failed")
    lines = open(p).read().splitlines()
    cases, i = [], 0
    while i < len(lines):
        if lines[i].startswith('  (:id "mov_d/'):
            cases.append(lines[i:i + 5])
            i += 5
        else:
            i += 1
    if not cases:
        die("no `mov_d` cases found in run/cases.lsp — the emitter's shape changed. "
            "A probe that cannot find its pre-states reports a failure, not a pass.")
    return cases


def build_cases(forms, bytes_by_id, pres, out_path):
    body = ['(in-package "X86ISA")', "", "(defconst *x86lean-cases*", " '("]
    n = 0
    for fid, _ in forms:
        hexb = bytes_by_id[fid]
        bs = [int(hexb[k:k + 2], 16) for k in range(0, len(hexb), 2)]
        codemem = " ".join("(#x%016x . #x%02x)" % (0x400000 + k, bs[k]) for k in range(len(bs)))
        for blk in pres:
            idx = re.match(r'\s*\(:id "mov_d/(\d+)"', blk[0]).group(1)
            l0 = re.sub(r'\(:id "[^"]+"', f'(:id "{fid}/{idx}"', blk[0], count=1)
            l0 = re.sub(r":len \d+", f":len {len(bs)}", l0, count=1)
            l1 = ":bytes (%s)" % " ".join("#x%02x" % x for x in bs)
            l4 = re.sub(r"\(#x0000000000400000 \. #x[0-9a-f]{2}\) "
                        r"\(#x0000000000400001 \. #x[0-9a-f]{2}\)",
                        codemem, blk[4].rstrip(), count=1)
            if l4 == blk[4].rstrip():
                die("could not patch the code bytes of a `mov_d` case — the emitter's "
                    "memory layout changed")
            body += [l0, l1, blk[2], blk[3], l4]
            n += 1
    body.append("))")
    open(out_path, "w").write("\n".join(body) + "\n")
    return n


def oracle_run(cases_path, driver, out_path):
    acl2 = os.environ.get("ACL2", os.path.join(ROOT, "vendor/acl2/saved_acl2"))
    if not os.access(acl2, os.X_OK):
        die(f"no ACL2 image at {acl2} — run scripts/setup_oracle.sh")
    drive = out_path + ".lsp"
    with open(drive, "w") as f:
        f.write(f'''(include-book "projects/x86isa/tools/execution/init-state" :dir :system :ttags :all)
(include-book "projects/x86isa/machine/x86" :dir :system :ttags :all)
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 99000 state)
(ld "{driver}")
(ld "{cases_path}")
(in-package "X86ISA")
(x86l-run-all *x86lean-cases* x86 state)
''')
    with open(out_path, "w") as f:
        subprocess.run([acl2], stdin=open(drive), stdout=f, stderr=subprocess.STDOUT)
    recs, cur = {}, None
    for line in open(out_path):
        m = re.match(r"^CASE id=(\S+) len=", line)
        if m:
            cur = m.group(1)
            continue
        if line.startswith("POST") and cur:
            recs[cur] = line.rstrip()
            cur = None
    return recs


def fields(post):
    return dict(t.split("=", 1) for t in post.split()[1:] if "=" in t)


def main():
    if len(sys.argv) < 2:
        die(__doc__.split("USAGE")[1].strip(), 2)
    forms = read_forms(sys.argv[1])
    subject_ids = [i for i, _ in forms]
    forms = forms + [(i, a) for i, a, _ in CONTROLS]

    tmp = scratch.mkdtemp(prefix="x86lean-probe-")
    bytes_by_id = assemble(forms, tmp)
    pres = load_pre_states()
    cases_path = os.path.join(tmp, "probe.lsp")
    n = build_cases(forms, bytes_by_id, pres, cases_path)
    print(f"── probing {len(subject_ids)} forms + {len(CONTROLS)} controls "
          f"× {len(pres)} real pre-states = {n} cases, twice ──")

    # Two drivers, differing ONLY in the undefined generator's offset.
    drv_a = os.path.join(tmp, "driver_a.lisp")
    drv_b = os.path.join(tmp, "driver_b.lisp")
    base = open("scripts/x86isa_driver.lisp").read()
    old = "(defun x86l-undef (x) (declare (xargs :guard t)) (nfix x))"
    if old not in base:
        die("scripts/x86isa_driver.lisp no longer defines `x86l-undef` as expected; "
            "this probe patches that line and cannot proceed without it")
    open(drv_a, "w").write(base)
    open(drv_b, "w").write(base.replace(
        old, f"(defun x86l-undef (x) (declare (xargs :guard t)) (+ {UNDEF_OFFSET} (nfix x)))"))

    A = oracle_run(cases_path, drv_a, os.path.join(tmp, "a.out"))
    B = oracle_run(cases_path, drv_b, os.path.join(tmp, "b.out"))
    if len(A) != n or len(B) != n:
        die(f"the oracle produced {len(A)}/{len(B)} records for {n} cases. "
            "That is a harness failure, not agreement.")

    agg = collections.OrderedDict()
    for cid in A:
        form = cid.rsplit("/", 1)[0]
        fa, fb = fields(A[cid]), fields(B[cid])
        d = agg.setdefault(form, {"n": 0, "ref": 0, "undef": collections.Counter(),
                                  "cases_undef": 0})
        d["n"] += 1
        if fa.get("refused") == "1":
            d["ref"] += 1
        moved = sorted(k for k in fa if fa[k] != fb.get(k))
        if moved:
            d["cases_undef"] += 1
            for k in moved:
                d["undef"][k] += 1

    # ⛔ THE CONTROLS, BEFORE ANYTHING ELSE IS BELIEVED.
    pos, neg = agg.get("CTRLPOS_and_q", {}), agg.get("CTRLNEG_mov_q", {})
    bad = []
    if pos.get("undef", {}).get("af", 0) != pos.get("n", -1):
        bad.append(f"CTRLPOS `andq %rcx,%rax`: af undefined in "
                   f"{pos.get('undef', {}).get('af', 0)} of {pos.get('n')} cases, expected all")
    if neg.get("cases_undef", -1) != 0:
        bad.append(f"CTRLNEG `movq %rcx,%rax`: {neg.get('cases_undef')} cases report an "
                   f"undefined field, expected none")
    if bad:
        print("⛔⛔ THE PROBE'S OWN CONTROLS FAILED. Nothing below would have meant anything, "
              "so nothing below is printed.")
        for b in bad:
            print("   " + b)
        print("   The classic cause is a perturbation that cannot move the field: the offset "
              "must be ODD to flip a one-bit flag. See this script's header.")
        sys.exit(2)

    w = max(len(f) for f in subject_ids)
    print(f"  ✔ controls: CTRLPOS sees af in all {pos['n']} cases; CTRLNEG sees nothing")
    print()
    print(f"{'form'.ljust(w)}  cases  refused  undef-cases  undefined fields")
    for f in subject_ids:
        d = agg[f]
        fl = ", ".join(f"{k}:{v}" for k, v in sorted(d["undef"].items())) or "—"
        print(f"{f.ljust(w)}  {d['n']:5d}  {d['ref']:7d}  {d['cases_undef']:11d}  {fl}")
    print()
    print("A form with `refused` equal to its case count is NOT SUPPORTED by this oracle at "
          "these pre-states; a form with none is executed in all of them. An `undefined "
          "fields` entry names a field x86isa fills from its undefined generator, with the "
          "number of pre-states in which it does.")
    if "--keep" in sys.argv:
        print(f"\nartefacts kept in {tmp}")


if __name__ == "__main__":
    main()
