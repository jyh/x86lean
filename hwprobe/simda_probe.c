/* hwprobe/simda_probe.c — D335 (V1a: PMADDWD PMADDUBSW PMULLW PMULHRSW PMULUDQ PADDSW PSUBUSW PSUBUSB PMAXSW PSADBW
   PACKSSDW, each at xmm,xmm and m128,xmm): the x86-64 referee for the SSE-legacy PACKED-INTEGER ARITHMETIC rows.
   Runs each row's instruction on THIS processor with both 128-bit operands and RFLAGS loaded from the row, and compares
   ALL 128 bits of the destination with the expectation hwprobe/mk_simda_rows.py derived from the SDM; and that the
   source register, the m128 source and the six arithmetic flags are unchanged (the SDM: "Flags Affected: None").
   It shares nothing with probe.c, int_probe.c or bitstr_probe.c.
   Exit 0: every row agrees. Exit 1: a row disagrees (printed). Exit 2: the harness is unusable — no rows, a declared
   instruction byte that is not the one assembled, or a processor without SSE2 or SSSE3 (a #UD is not a reading). */
#include <cpuid.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

struct sio { uint64_t a[2], b[2], r[2], s[2], f, fo; } __attribute__((aligned(16)));
typedef void (*sfn)(struct sio *);

struct srow {
  const char *name;
  sfn fn;
  uint64_t a[2], b[2];
  unsigned f;
  uint64_t w[2];
};

struct sop {
  const char *name;
  const unsigned char *at;
  unsigned len;
  int ssse3;
  unsigned char bytes[8];
};

#include "simda_rows.h"

#define ARITH 0x8d5u

/* CPUID.01H:EDX bit 26 is SSE2 (PMADDWD PMULLW PMULUDQ PADDSW PSUBUSW PSUBUSB PMAXSW PSADBW PACKSSDW at xmm) and
   CPUID.01H:ECX bit 9 is SSSE3 (PMADDUBSW, PMULHRSW) — SDM Vol. 2A, CPUID, Tables 3-10 and 3-11. Printed on every leg,
   and a processor without either REFUSES the run: executing the rows would raise #UD, and a crash is not a disagreement. */
static int features(void) {
  unsigned a = 0, b = 0, c = 0, d = 0;
  if (!__get_cpuid(1, &a, &b, &c, &d)) {
    printf("REFUSED: CPUID leaf 1 is not available\n");
    return 1;
  }
  int sse2 = (d >> 26) & 1, ssse3 = (c >> 9) & 1;
  printf("cpuid.01.ecx %08x cpuid.01.edx %08x  SSE2=%d SSSE3=%d\n", c, d, sse2, ssse3);
  if (!sse2 || !ssse3) {
    printf("REFUSED: this processor lacks%s%s\n", sse2 ? "" : " SSE2", ssse3 ? "" : " SSSE3");
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
    static struct sio io;
    memset(&io, 0, sizeof io);
    io.a[0] = r->a[0]; io.a[1] = r->a[1];
    io.b[0] = r->b[0]; io.b[1] = r->b[1];
    io.f = r->f;
    r->fn(&io);
    unsigned got_f = (unsigned)(io.fo & ARITH);
    int dst = io.r[0] == r->w[0] && io.r[1] == r->w[1];
    int src = io.s[0] == r->b[0] && io.s[1] == r->b[1] && io.b[0] == r->b[0] && io.b[1] == r->b[1];
    int flg = got_f == (r->f & ARITH);
    int ok = dst && src && flg;
    if (!ok) bad++;
    printf("%s %-26s r %016llx%016llx want %016llx%016llx  flags %03x want %03x%s%s\n", ok ? "ok  " : "DIFF", r->name,
           (unsigned long long)io.r[1], (unsigned long long)io.r[0], (unsigned long long)r->w[1],
           (unsigned long long)r->w[0], got_f, r->f & ARITH, src ? "" : "  SOURCE WRITTEN", flg ? "" : "  FLAGS WRITTEN");
  }
  printf("rows %zu disagreements %zu\n", n, bad);
  return bad ? 1 : 0;
}
