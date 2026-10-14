#!/usr/bin/env python3
"""Which published figures have MOVED since the sha they are pinned at?  Read-only.

⛔ WHY THIS EXISTS BESIDE check_claims.py.  `check_claims` re-derives every row of
docs/CLAIMS.tsv AT ITS PINNED SHA, which is exactly right for its question ("is the
figure true of the tree it names?") and silent on the next one ("is it still the
figure a reader of the paper at the SUBMITTED tree should see?").  A stale figure
reads CLEAN there by design.  Measured 2026-10-14 on the TACAS case study: 111 claims
CLEAN, and 10 of the paper's figures had moved (197 -> 199 mnemonics among them).
⇒ This tool runs each row's OWN command at another sha (default HEAD) and lists the
rows whose value differs.  It rewrites nothing: re-pinning is a deliberate edit of the
value, the sha AND the prose, followed by check_claims, never an automatic update
(check_claims' own header explains why it has no --update).

Usage:  claims_drift.py [--at REV] [--paper-only]
        claims_drift.py --selftest
"""
import argparse, os, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TSV = os.path.join(ROOT, "docs", "CLAIMS.tsv")


def rows(path=TSV):
    out = []
    for ln in open(path, encoding="utf-8"):
        if not ln.strip() or ln.startswith("#"):
            continue
        f = ln.rstrip("\n").split("\t")
        if f[0] == "id" or len(f) < 4:
            continue
        out.append({"id": f[0], "value": f[1], "sha": f[2], "cmd": f[3],
                    "appears": f[4] if len(f) > 4 else ""})
    return out


def derive(cmd, sha, cwd=ROOT):
    r = subprocess.run(["bash", "-c", cmd], cwd=cwd, capture_output=True, text=True,
                       env=dict(os.environ, SHA=sha))
    return r.returncode, r.stdout.strip()


def drift(rs, sha, cwd=ROOT):
    """[(row, status, now)] with status in MOVED / SAME / ERROR."""
    res = []
    for r in rs:
        rc, now = derive(r["cmd"], sha, cwd)
        st = "ERROR" if (rc or not now) else ("SAME" if now == r["value"] else "MOVED")
        res.append((r, st, now))
    return res


def selftest():
    bad = []
    def arm(n, c):
        print(("  ✔ " if c else "  ⛔ ") + n)
        if not c:
            bad.append(n)
    with tempfile.TemporaryDirectory() as t:
        def g(*a):
            subprocess.run(["git", *a], cwd=t, check=True, capture_output=True)
        g("init", "-q"); g("config", "user.email", "x@x"); g("config", "user.name", "x")
        open(os.path.join(t, "f.txt"), "w").write("a\nb\n")
        g("add", "-A"); g("commit", "-qm", "1")
        s1 = subprocess.run(["git", "rev-parse", "HEAD"], cwd=t, capture_output=True, text=True).stdout.strip()
        open(os.path.join(t, "f.txt"), "w").write("a\nb\nc\n")
        g("add", "-A"); g("commit", "-qm", "2")
        s2 = subprocess.run(["git", "rev-parse", "HEAD"], cwd=t, capture_output=True, text=True).stdout.strip()
        cmd = 'git show "$SHA":f.txt | wc -l | tr -d " "'
        r = [{"id": "lines", "value": "2", "sha": s1, "cmd": cmd, "appears": "paper"}]
        arm("control: the pinned sha re-derives its own value (SAME)", drift(r, s1, t)[0][1] == "SAME")
        arm("a later sha where the figure grew reads MOVED, with the new value",
            drift(r, s2, t)[0][1:] == ("MOVED", "3"))
        r_bad = [dict(r[0], cmd='git show "$SHA":no-such-file')]
        arm("a command that fails reads ERROR, never SAME", drift(r_bad, s2, t)[0][1] == "ERROR")
        r_empty = [dict(r[0], cmd="true")]
        arm("an EMPTY output reads ERROR (an empty string is not a value)", drift(r_empty, s2, t)[0][1] == "ERROR")
    print("claims_drift selftest: %s (4 arms)" % ("CLEAN" if not bad else "FAIL"))
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--at", default="HEAD")
    ap.add_argument("--paper-only", action="store_true",
                    help="only rows whose appears_in names the paper (paper/...)")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    sha = subprocess.run(["git", "rev-parse", a.at], cwd=ROOT, capture_output=True,
                         text=True, check=True).stdout.strip()
    rs = rows()
    if a.paper_only:
        rs = [r for r in rs if r["appears"].startswith("paper/")]
    res = drift(rs, sha)
    for r, st, now in res:
        if st != "SAME":
            print(f"{st:5s} {r['id']:32s} pinned {r['value']:>10s} @{r['sha'][:7]}  at {sha[:7]}: {now or '-'}")
    n = {k: sum(1 for _r, s, _n in res if s == k) for k in ("SAME", "MOVED", "ERROR")}
    print(f"claims_drift at {sha[:7]}: {len(res)} row(s) — SAME {n['SAME']} · MOVED {n['MOVED']} · "
          f"ERROR {n['ERROR']}. A MOVED row is not a failure: it is a figure the submitted tree "
          f"would print differently, owed a deliberate re-pin (value, sha, prose) and check_claims.")
    return 1 if n["ERROR"] else 0


if __name__ == "__main__":
    sys.exit(main())
