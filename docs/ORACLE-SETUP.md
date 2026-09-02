# The differential oracle: ACL2 + x86isa, on this machine

Plan v1 §5 (P0) requires the oracle to be installed "from public sources with
the recipe recorded", and — because this Mac is arm64 while x86isa models an
x86-64 machine — requires the seat to **say which lane it actually ran on**
rather than which one it hoped for.

## The lane, measured rather than assumed

**Route 1 (native arm64 SBCL) WORKS. It is the lane this repository uses.**
Neither of the fallbacks was needed:

| route | status |
|---|---|
| 1. native arm64 SBCL + ACL2 | ✅ **used** — image built in ~4 minutes |
| 2. x86-64 container | not needed (and the Docker daemon was down at P0) |
| 3. GitHub x86-64 runner | not needed at P0; it is still the lane the CI job uses, because CI has no ACL2 image |

This matters beyond convenience: ACL2 running natively means a disagreement can
be reproduced and bisected on the developer's own machine in seconds, instead of
through a container or a CI round-trip.

⚠️ **The oracle is an x86-64 SEMANTICS, not an x86-64 MACHINE.** Running it on
arm64 is sound because x86isa is a model — it interprets x86-64, it does not
execute it. What arm64 *does* rule out is plan v1 §4.4's hardware
co-simulation, which needs a real x86-64 processor and therefore a GitHub-hosted
x86-64 runner. That is P1, and it is not a substitute for this and vice versa:
x86isa can be wrong in the same direction as us, and hardware cannot tell us
what Intel left undefined.

## The recipe, exactly as run (2026-09-02, macOS 26.6.2, arm64)

```bash
brew install sbcl                      # SBCL 2.6.8, bottled — no build
git clone --depth 1 https://github.com/acl2/acl2.git vendor/acl2
cd vendor/acl2
make LISP="$(which sbcl)" -j2          # produces ./saved_acl2   (~4 min)

cd books
export ACL2=$PWD/../saved_acl2
make -j5 ACL2=$ACL2 projects/x86isa/top.cert
```

`scripts/setup_oracle.sh` is this recipe, idempotent and logged.

**Sizes and times to expect.** The ACL2 clone is ~1.7 GB (hence `/vendor/` in
`.gitignore` — the recipe is what this repository carries, never the tree). The
ACL2 image builds in about four minutes. Certifying `projects/x86isa/top.cert`
pulls in a large transitive dependency set (`std`, `bitops`, and the `rtl`
books dominate) and is the long pole by a wide margin.

## Licence

ACL2 and the community books are public sources under the licences recorded in
`PROVENANCE.md`; x86isa is BSD-3-Clause, © 2015 Regents of the University of
Texas. Nothing from either tree is copied into this repository. The oracle is
consulted by EXECUTION and its answers are recorded as evidence — never as
theorems, and never as text (TRUSTBASE.md, "What is validated, not proven").
