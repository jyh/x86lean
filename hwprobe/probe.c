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
uint64_t p_sqrtss(uint64_t, uint64_t);
uint64_t p_sqrtsd(uint64_t, uint64_t);
uint64_t p_cvtss2si(uint64_t, uint64_t);
uint64_t p_cvtss2siq(uint64_t, uint64_t);
uint64_t p_cvtsd2si(uint64_t, uint64_t);
uint64_t p_cvtsd2siq(uint64_t, uint64_t);

/* B5: the packed forms take both quadwords of each operand and return all 128 bits (sse_ops.S). */
typedef unsigned __int128 u128;
typedef u128 (*op2_fn)(uint64_t, uint64_t, uint64_t, uint64_t);
u128 p_mulps(uint64_t, uint64_t, uint64_t, uint64_t);
u128 p_mulpd(uint64_t, uint64_t, uint64_t, uint64_t);
u128 p_addps(uint64_t, uint64_t, uint64_t, uint64_t);
u128 p_addpd(uint64_t, uint64_t, uint64_t, uint64_t);
u128 p_subps(uint64_t, uint64_t, uint64_t, uint64_t);
u128 p_subpd(uint64_t, uint64_t, uint64_t, uint64_t);
u128 p_divps(uint64_t, uint64_t, uint64_t, uint64_t);
u128 p_divpd(uint64_t, uint64_t, uint64_t, uint64_t);

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

struct prow {
  const char *name;
  op2_fn fn;
  unsigned mxcsr;
  uint64_t alo, ahi, blo, bhi, wlo, whi;
  unsigned flags;
};

struct pop {
  const char *name;
  op2_fn fn;
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
  /* The packed forms' instruction starts at +28: four 5-byte movq and two 4-byte punpcklqdq (LOAD4). */
  for (size_t i = 0; i < sizeof POPS / sizeof POPS[0]; i++) {
    const unsigned char *code = (const unsigned char *)(void *)POPS[i].fn;
    if (memcmp(code + 28, POPS[i].bytes, POPS[i].len) != 0) {
      printf("REFUSED %s: the bytes at +28 are not the declared instruction\n", POPS[i].name);
      bad = 1;
    }
  }
  return bad;
}

int main(void) {
  size_t n = sizeof ROWS / sizeof ROWS[0], pn = sizeof PROWS / sizeof PROWS[0], bad = 0;
  if (n == 0 || pn == 0 || check_ops()) return 2;
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
  /* B5: all 128 bits of the result are compared, both halves, with no mask: every lane is declared. */
  for (size_t i = 0; i < pn; i++) {
    const struct prow *r = &PROWS[i];
    _mm_setcsr(r->mxcsr);
    u128 got = r->fn(r->alo, r->blo, r->ahi, r->bhi);
    unsigned mx = _mm_getcsr();
    _mm_setcsr(0x1f80);
    uint64_t glo = (uint64_t)got, ghi = (uint64_t)(got >> 64);
    unsigned want_mx = r->mxcsr | r->flags;
    int vok = (glo == r->wlo && ghi == r->whi);
    int fok = (mx == want_mx);
    if (!(vok && fok)) bad++;
    printf("%s %-28s result %016llx%016llx want %016llx%016llx  mxcsr %04x want %04x\n",
           (vok && fok) ? "ok  " : "DIFF", r->name, (unsigned long long)ghi, (unsigned long long)glo,
           (unsigned long long)r->whi, (unsigned long long)r->wlo, mx, want_mx);
  }
  n += pn;
  printf("rows %zu disagreements %zu\n", n, bad);
  return bad ? 1 : 0;
}
