/* hwprobe/probe.c — the x86-64 referee for sub-group B's SDM-pinned rows (D266).
   Runs each row's instruction on THIS processor with MXCSR loaded from the row, and compares the
   result and the sticky flags with the expectations hwprobe/mk_rows.py derived from the SDM.
   Exit 0: every row agrees. Exit 1: a row disagrees (printed). Exit 2: the harness is unusable. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <xmmintrin.h>

typedef uint64_t (*op_fn)(uint64_t, uint64_t);
uint64_t p_cvtsi2sd(uint64_t, uint64_t);
uint64_t p_mulsd(uint64_t, uint64_t);
uint64_t p_mulss(uint64_t, uint64_t);
uint64_t p_addsd(uint64_t, uint64_t);
uint64_t p_addss(uint64_t, uint64_t);
uint64_t p_subsd(uint64_t, uint64_t);
uint64_t p_subss(uint64_t, uint64_t);
uint64_t p_divsd(uint64_t, uint64_t);
uint64_t p_divss(uint64_t, uint64_t);
uint64_t p_minsd(uint64_t, uint64_t);
uint64_t p_minss(uint64_t, uint64_t);
uint64_t p_comisd(uint64_t, uint64_t);
uint64_t p_ucomisd(uint64_t, uint64_t);
uint64_t p_comiss(uint64_t, uint64_t);
uint64_t p_ucomiss(uint64_t, uint64_t);
uint64_t p_cvtss2sd(uint64_t, uint64_t);
uint64_t p_cvttsd2si(uint64_t, uint64_t);
uint64_t p_cvtsd2ss(uint64_t, uint64_t);
uint64_t p_cvtsi2ss(uint64_t, uint64_t);
uint64_t p_cvtsi2ssq(uint64_t, uint64_t);
uint64_t p_cvtsi2sdq(uint64_t, uint64_t);

struct row {
  const char *name;
  op_fn fn;
  unsigned mxcsr;
  uint64_t a, b, want, mask;
  unsigned flags;
};

struct op {
  const char *name;
  op_fn fn;
  unsigned len;
  unsigned char bytes[8];
};

#include "rows.h"

/* The two loads in every p_ function are 5 bytes each (66 48 0f 6e /r), so the instruction under test
   starts at offset 10. Reading code bytes through a function pointer is not ISO C; it is what both
   compilers this probe is built with do, and a mismatch here refuses the run rather than trusting it. */
static int check_ops(void) {
  int bad = 0;
  for (size_t i = 0; i < sizeof OPS / sizeof OPS[0]; i++) {
    const unsigned char *code = (const unsigned char *)(void *)OPS[i].fn;
    if (memcmp(code + 10, OPS[i].bytes, OPS[i].len) != 0) {
      printf("REFUSED %s: the bytes at +10 are not the declared instruction\n", OPS[i].name);
      bad = 1;
    }
  }
  return bad;
}

int main(void) {
  size_t n = sizeof ROWS / sizeof ROWS[0], bad = 0;
  if (n == 0 || check_ops()) return 2;
  for (size_t i = 0; i < n; i++) {
    const struct row *r = &ROWS[i];
    _mm_setcsr(r->mxcsr);
    uint64_t got = r->fn(r->a, r->b);
    unsigned mx = _mm_getcsr();
    _mm_setcsr(0x1f80);
    unsigned want_mx = r->mxcsr | r->flags;
    int vok = ((got & r->mask) == r->want);
    int fok = (mx == want_mx);
    if (!(vok && fok)) bad++;
    printf("%s %-28s result %016llx want %016llx  mxcsr %04x want %04x\n",
           (vok && fok) ? "ok  " : "DIFF", r->name,
           (unsigned long long)(got & r->mask), (unsigned long long)r->want, mx, want_mx);
  }
  printf("rows %zu disagreements %zu\n", n, bad);
  return bad ? 1 : 0;
}
