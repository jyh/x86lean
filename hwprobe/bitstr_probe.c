/* hwprobe/bitstr_probe.c — D333: the x86-64 referee for the BIT-STRING rows (BT/BTS/BTR/BTC, memory base, register
   offset). Runs each row's instruction on THIS processor against a buffer filled from PATTERN with the row's one
   addressed byte overridden, then compares CF, ZF and the WHOLE buffer with the expectations hwprobe/mk_bitstr_rows.py
   derived from the SDM. The SSE (probe.c) and integer (int_probe.c) referees are separate programs, untouched.

   Beside the verdict it prints, per row, whether the processor also matched ACL2 x86isa's rule (column `x86isa`), and
   a total. That column is a reading, NOT part of the verdict.
   Exit 0: every row agrees with the SDM rule. Exit 1: a row disagrees (printed). Exit 2: the harness is unusable — no
   rows, or a declared instruction byte that is not the one assembled. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

struct bio { uint64_t base, off, f, fo; };
typedef void (*bfn)(struct bio *);

struct brow {
  const char *name;
  bfn fn;
  uint64_t reg;       /* the full 64-bit offset register */
  unsigned idx;       /* the addressed byte's index in the buffer */
  unsigned pre;       /* its value before the instruction */
  unsigned f;         /* the six arithmetic flags in */
  unsigned wf;        /* CF and ZF expected out (SDM rule) */
  unsigned wb;        /* the addressed byte expected after (SDM rule) */
  unsigned xf, xb;    /* the same under x86isa's rule */
  int differ;         /* 1: the two rules predict different (CF, byte) on this row */
};

struct bop {
  const char *name;
  const unsigned char *at;
  unsigned len;
  unsigned char bytes[8];
};

#include "bitstr_rows.h"

#define CMP 0x41u     /* CF and ZF: the only defined flags */

static unsigned char buf[BUF] __attribute__((aligned(4096)));

/* Reading code bytes through a pointer to a label is not ISO C; it is what both compilers this probe is built with
   do, and a mismatch refuses the run rather than trusting it. */
static int check_ops(void) {
  int bad = 0;
  for (size_t i = 0; i < sizeof BOPS / sizeof BOPS[0]; i++) {
    if (memcmp(BOPS[i].at, BOPS[i].bytes, BOPS[i].len) != 0) {
      printf("REFUSED %s: the bytes at its _at label are not the declared instruction\n", BOPS[i].name);
      bad = 1;
    }
  }
  return bad;
}

int main(void) {
  size_t n = sizeof BROWS / sizeof BROWS[0], bad = 0, xagree = 0, ndiffer = 0, differ_sdm = 0;
  if (n == 0 || check_ops()) return 2;
  for (size_t i = 0; i < n; i++) {
    const struct brow *r = &BROWS[i];
    memcpy(buf, PATTERN, BUF);
    buf[r->idx] = (unsigned char)r->pre;
    struct bio io = { (uint64_t)(uintptr_t)(buf + BASE), r->reg, r->f, 0 };
    r->fn(&io);
    unsigned got_f = (unsigned)(io.fo & CMP), got_b = buf[r->idx];
    /* every byte but the addressed one must still be PATTERN's */
    long stray = -1;
    for (size_t j = 0; j < BUF; j++) {
      if (j != r->idx && buf[j] != PATTERN[j]) { stray = (long)j; break; }
    }
    int ok = got_f == r->wf && got_b == r->wb && stray < 0;
    int xok = got_f == r->xf && got_b == r->xb && stray < 0;
    if (!ok) bad++;
    if (xok) xagree++;
    if (r->differ) { ndiffer++; if (ok) differ_sdm++; }
    printf("%s %-26s cf/zf %02x want %02x  byte[%+5d] %02x want %02x  x86isa %s%s",
           ok ? "ok  " : "DIFF", r->name, got_f, r->wf, (int)r->idx - BASE, got_b, r->wb,
           xok ? "match" : "differ", r->differ ? " (rules differ)" : "");
    if (stray >= 0) printf("  STRAY WRITE byte[%+ld] %02x pattern %02x", stray - BASE, buf[stray], PATTERN[stray]);
    printf("\n");
  }
  printf("rows %zu disagreements %zu\n", n, bad);
  printf("x86isa-rule agreement %zu of %zu; rows where the rules differ %zu, silicon took the SDM's value on %zu\n",
         xagree, n, ndiffer, differ_sdm);
  return bad ? 1 : 0;
}
