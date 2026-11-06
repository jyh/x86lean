/* hwprobe/shuf_probe.c — D336 (V1b): the x86-64 referee for PSHUFB, PALIGNR, PINSRD, PINSRQ, PEXTRD and PEXTRQ.
   Runs each row's instruction on THIS processor with XMM0, XMM1, the 16-byte memory source, RCX, RAX and RFLAGS loaded
   from the row (shuf_ops.S's header), and compares ALL 128 bits of XMM0, all 64 of RAX, the six arithmetic flags and
   (D362) all 16 bytes at [RBX] after the instruction with the expectations hwprobe/mk_shuf_rows.py derived from the SDM. It shares nothing with probe.c, int_probe.c or
   bitstr_probe.c.
   Exit 0: every row agrees. Exit 1: a row disagrees (printed). Exit 2: the harness is unusable — no rows, a declared
   instruction byte that is not the one assembled, or a processor without SSSE3 or SSE4.1 (a #UD is not a reading). */
#include <cpuid.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

struct sio { uint64_t a[2], b[2], g, f, r[2], ro, fo; } __attribute__((aligned(16)));
typedef void (*sfn)(struct sio *);

struct srow {
  const char *name;
  sfn fn;
  uint64_t a0, a1, b0, b1, g;
  unsigned f;          /* the six arithmetic flags in; NO-FLAGS: they must come out the same */
  uint64_t w0, w1;     /* XMM0 after, low and high quadwords */
  uint64_t wax;        /* RAX after */
  uint64_t wm0, wm1;   /* D362: the 16 bytes at [RBX] (p->b) after — a store's bytes, and b itself for every other form */
};

struct sop {
  const char *name;
  const unsigned char *at;
  unsigned len;
  unsigned char bytes[8];
};

#include "shuf_rows.h"

#define ARITH 0x8d5u

/* CPUID.01H:ECX bit 9 is SSSE3 (PSHUFB, PALIGNR) and bit 19 is SSE4.1 (PINSRD/Q, PEXTRD/Q) — SDM Vol. 2A, CPUID,
   Table 3-10. Printed on every leg; a processor without either REFUSES the run, since a #UD is not a disagreement. */
static int features(void) {
  unsigned a = 0, b = 0, c = 0, d = 0;
  if (!__get_cpuid(1, &a, &b, &c, &d)) {
    printf("REFUSED: CPUID leaf 1 is not available\n");
    return 1;
  }
  int ssse3 = (c >> 9) & 1, sse41 = (c >> 19) & 1;
  printf("cpuid.01.ecx %08x  SSSE3=%d SSE4.1=%d\n", c, ssse3, sse41);
  if (!ssse3 || !sse41) {
    printf("REFUSED: this processor lacks%s%s\n", ssse3 ? "" : " SSSE3", sse41 ? "" : " SSE4.1");
    return 1;
  }
  return 0;
}

/* Reading code bytes through a pointer to a label is not ISO C; it is what both compilers this probe is built with
   do, and a mismatch refuses the run rather than trusting it. */
static int check_ops(void) {
  int bad = 0;
  for (size_t i = 0; i < sizeof SOPS / sizeof SOPS[0]; i++) {
    if (memcmp(SOPS[i].at, SOPS[i].bytes, SOPS[i].len) != 0) {
      printf("REFUSED %s: the bytes at its _at label are not the declared instruction\n", SOPS[i].name);
      bad = 1;
    }
  }
  return bad;
}

int main(void) {
  size_t n = sizeof SROWS / sizeof SROWS[0], bad = 0;
  if (n == 0 || features() || check_ops()) return 2;
  for (size_t i = 0; i < n; i++) {
    const struct srow *r = &SROWS[i];
    struct sio io;
    memset(&io, 0, sizeof io);
    io.a[0] = r->a0; io.a[1] = r->a1; io.b[0] = r->b0; io.b[1] = r->b1; io.g = r->g; io.f = r->f;
    r->fn(&io);
    unsigned got_f = (unsigned)(io.fo & ARITH);
    int ok = io.r[0] == r->w0 && io.r[1] == r->w1 && io.ro == r->wax && got_f == (r->f & ARITH)
             && io.b[0] == r->wm0 && io.b[1] == r->wm1;
    if (!ok) bad++;
    printf("%s %-28s xmm0 %016llx%016llx want %016llx%016llx  rax %016llx want %016llx  flags %03x want %03x"
           "  mem %016llx%016llx want %016llx%016llx\n",
           ok ? "ok  " : "DIFF", r->name, (unsigned long long)io.r[1], (unsigned long long)io.r[0],
           (unsigned long long)r->w1, (unsigned long long)r->w0, (unsigned long long)io.ro,
           (unsigned long long)r->wax, got_f, r->f & ARITH, (unsigned long long)io.b[1], (unsigned long long)io.b[0],
           (unsigned long long)r->wm1, (unsigned long long)r->wm0);
  }
  printf("rows %zu disagreements %zu\n", n, bad);
  return bad ? 1 : 0;
}
