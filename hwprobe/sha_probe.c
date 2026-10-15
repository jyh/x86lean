/* hwprobe/sha_probe.c — D338 (V2: SHA256MSG1, SHA256MSG2, SHA256RNDS2, each at xmm,xmm and m128,xmm, legacy SSE): the
   x86-64 referee for the SHA-NI rows. Runs each row's instruction on THIS processor with DEST (%xmm1), SRC2 (%xmm2 and
   the m128), the implicit %xmm0 and RFLAGS loaded from the row, and compares ALL 128 bits of the destination with the
   expectation hwprobe/mk_sha_rows.py derived from the SDM (and, for its known-answer rows, from a textbook FIPS 180-4
   SHA-256); and that SRC2 (register and m128), %xmm0 and the six arithmetic flags are unchanged ("Flags Affected: None").
   It shares nothing with probe.c, int_probe.c, bitstr_probe.c, shuf_probe.c or simda_probe.c.
   Exit 0: every row agrees. Exit 1: a row disagrees (printed). Exit 2: the harness is unusable — no rows, a declared
   instruction byte that is not the one assembled, CPUID unavailable or no SSE2.
   ⛔ Exit 3, AND ONLY 3: this processor has no SHA-NI (CPUID.(EAX=07H,ECX=0):EBX bit 29 clear). A #UD is not a reading,
   so no row runs; the code is DISTINCT so a workflow can accept exactly this refusal on a leg KNOWN to lack the extension
   (`macos-15-intel`'s i7-8700B) and fail it everywhere else. `--cpuid` stops after the feature check. */
#include <cpuid.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

struct hio { uint64_t a[2], b[2], k[2], r[2], s[2], t[2], f, fo; } __attribute__((aligned(16)));
typedef void (*hfn)(struct hio *);

struct hrow {
  const char *name;
  hfn fn;
  uint64_t a[2], b[2], k[2];
  unsigned f;
  uint64_t w[2];
};

struct hop {
  const char *name;
  const unsigned char *at;
  unsigned len;
  unsigned char bytes[8];
};

#include "sha_rows.h"

#define ARITH 0x8d5u

/* CPUID.01H:EDX bit 26 is SSE2 and CPUID.(EAX=07H,ECX=0):EBX bit 29 is SHA (SDM Vol. 2A, CPUID, Tables 3-11 and 3-8).
   Both are printed on every leg. Returns 0 (usable), 2 (no CPUID leaf, or no SSE2) or 3 (no SHA-NI). */
static int features(void) {
  unsigned a = 0, b = 0, c = 0, d = 0, b7 = 0;
  if (!__get_cpuid(1, &a, &b, &c, &d)) {
    printf("REFUSED: CPUID leaf 1 is not available\n");
    return 2;
  }
  int sse2 = (d >> 26) & 1;
  unsigned maxleaf = __get_cpuid_max(0, 0);
  if (maxleaf >= 7) {
    unsigned a7 = 0, c7 = 0, d7 = 0;
    __cpuid_count(7, 0, a7, b7, c7, d7);
  }
  int sha = (b7 >> 29) & 1;
  printf("cpuid.01.edx %08x cpuid.07.0.ebx %08x (max leaf %u)  SSE2=%d SHA=%d\n", d, b7, maxleaf, sse2, sha);
  if (!sse2) {
    printf("REFUSED: this processor lacks SSE2\n");
    return 2;
  }
  if (!sha) {
    printf("REFUSED: this processor lacks SHA-NI\n");
    return 3;
  }
  return 0;
}

/* Reading code bytes through a pointer to a label is not ISO C; it is what both compilers this probe is built with
   do, and a mismatch refuses the run rather than trusting it. */
static int check_ops(void) {
  int bad = 0;
  for (size_t i = 0; i < sizeof HOPS / sizeof HOPS[0]; i++) {
    if (memcmp(HOPS[i].at, HOPS[i].bytes, HOPS[i].len) != 0) {
      printf("REFUSED %s: the bytes at its _at label are not the declared instruction\n", HOPS[i].name);
      bad = 1;
    }
  }
  return bad;
}

int main(int argc, char **argv) {
  size_t n = sizeof HROWS / sizeof HROWS[0], bad = 0;
  int fe = features();
  if (fe) return fe;
  if (argc > 1 && strcmp(argv[1], "--cpuid") == 0) return 0;
  if (n == 0 || check_ops()) return 2;
  for (size_t i = 0; i < n; i++) {
    const struct hrow *r = &HROWS[i];
    static struct hio io;
    memset(&io, 0, sizeof io);
    io.a[0] = r->a[0]; io.a[1] = r->a[1];
    io.b[0] = r->b[0]; io.b[1] = r->b[1];
    io.k[0] = r->k[0]; io.k[1] = r->k[1];
    io.f = r->f;
    r->fn(&io);
    unsigned got_f = (unsigned)(io.fo & ARITH);
    int dst = io.r[0] == r->w[0] && io.r[1] == r->w[1];
    int src = io.s[0] == r->b[0] && io.s[1] == r->b[1] && io.b[0] == r->b[0] && io.b[1] == r->b[1];
    int x0 = io.t[0] == r->k[0] && io.t[1] == r->k[1];
    int flg = got_f == (r->f & ARITH);
    int ok = dst && src && x0 && flg;
    if (!ok) bad++;
    printf("%s %-34s r %016llx%016llx want %016llx%016llx  flags %03x want %03x%s%s%s\n", ok ? "ok  " : "DIFF", r->name,
           (unsigned long long)io.r[1], (unsigned long long)io.r[0], (unsigned long long)r->w[1],
           (unsigned long long)r->w[0], got_f, r->f & ARITH, src ? "" : "  SOURCE WRITTEN", x0 ? "" : "  XMM0 WRITTEN",
           flg ? "" : "  FLAGS WRITTEN");
  }
  printf("rows %zu disagreements %zu\n", n, bad);
  return bad ? 1 : 0;
}
