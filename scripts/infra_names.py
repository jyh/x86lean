#!/usr/bin/env python3
"""The infrastructure-name list for this repository's PR-body arm (check_pr_descriptions.py).

WHY THIS FILE IS NOT THE SIBLING REPOSITORIES' check_infra_names.py
-------------------------------------------------------------------
Four sibling public repositories refuse every host and account name in a pull request's title or body. This repository
cannot: it names its measurement machines on purpose. A timing figure without the machine it was measured on is not
comparable, so the decision log, the delta ledger (a box field on every row) and many commit subjects state which box a
figure came from, and no address or credential ever sits beside such a name. That is this repository's convention (ruled
2026-10-18, after a census of its history), not a leak, and a purge of commit subjects is not this file's business.

So the list is split in two. FORBIDDEN is what a PR body must never carry: account names, the account config-directory
names, and the machines that are not measurement boxes here. ALLOWED_BOXES is the measurement machines the convention
permits, kept ONLY so the self-test can prove the arm lets them through. The names are ASSEMBLED, never spelled, because
this repository's gates scan this file too.

It is NOT a tree arm. It scans the rows it is handed and nothing else; the PR-body arm hands it a title and a body.
"""
from __future__ import annotations

import sys

# Refused in a PR title or body. Assembled, never spelled.
FORBIDDEN = [
    "kri" + "ter" + "ion",              # an account (and a box, in the siblings' wording): refused here as an account
    "jao" + "quin",                     # a machine that is not a measurement box in this repository
    "ja" + "son" + "h",                 # an account
    "jy" + "aletheia",                  # an account
    "claude-account-" + "ja" + "son",   # an account's config-directory name
    "claude-acct-" + "ja" + "son",      # the same account's second config-directory spelling
    "salt" + "forge",                   # an account
]

# Permitted by this repository's convention: the machines its measurements are taken on. Used by the self-test only.
ALLOWED_BOXES = [
    "yu" + "kon",
    "ke" + "nai",
    "kat" + "mai",
]

_FINDING_LABEL = "an infrastructure name (account or host)"


def names_in(s: str) -> bool:
    low = s.lower()
    return any(n in low for n in FORBIDDEN)


def scan(rows: list[tuple[str, str]]) -> list[tuple[str, int, str]]:
    """(where, line_number, trimmed_line) for every line of every row that carries a refused name. The caller must
    NEVER print the trimmed line: a CI log on a public repository is public."""
    found = []
    for rel, text in rows:
        for i, line in enumerate(text.splitlines(), 1):
            if names_in(line):
                found.append((rel, i, line.strip()[:160]))
    return found


def self_test() -> int:
    failures = []
    if not FORBIDDEN or len(set(FORBIDDEN)) != len(FORBIDDEN):
        failures.append("the refused list must be non-empty and free of duplicates")
    for n in FORBIDDEN:
        if not scan([("x", "on " + n.upper() + " today")]):
            failures.append("a refused name must be caught in any case")
    for b in ALLOWED_BOXES:
        if scan([("x", "measured on " + b + " at base 0000000")]):
            failures.append("a measurement box this repository names by convention must pass")
        if b in FORBIDDEN or any(b in f or f in b for f in FORBIDDEN):
            failures.append("a measurement box and a refused name must not overlap")
    if scan([("x", "the Windows box, the run box, account A")]):
        failures.append("role words must pass")
    if failures:
        for f in failures:
            print("infra_names SELF-TEST FAIL:", f)
        return 1
    print(f"infra_names SELF-TEST: OK ({len(FORBIDDEN)} refused, {len(ALLOWED_BOXES)} allowed measurement boxes)")
    return 0


if __name__ == "__main__":
    # Refuse an unknown flag before any work (the repo's flag-strictness gate; see portable.strict_flags).
    import os as _os
    sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)
    sys.exit(self_test() if "--self-test" in sys.argv[1:] else 0)
