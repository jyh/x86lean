/* hwprobe/aes_probe.c — D342 (V4: AESENC, AESENCLAST legacy; VAESENC, VAESENCLAST, VPCLMULQDQ, VPSHUFB, VPALIGNR,
   VPSLLDQ, VPSRLDQ VEX.128; register forms): the x86-64 referee for the AES-NI/CLMUL/VEX rows. Runs each row's
   instruction on THIS processor with YMM1, YMM2, YMM3 loaded WHOLE from the row (every upper half non-zero) and the
   six arithmetic flags from the row, and compares ALL 256 bits of the destination's YMM register (XMM1 for a legacy
   form, XMM3 for a VEX form) with the expectation hwprobe/mk_aes_rows.py derived from the SDM (and, for its
   known-answer rows, from a textbook FIPS-197 AES-128 and a textbook carry-less product): so a VEX form that did not
   zero bits 255:128, or a legacy form that did, disagrees. The other two YMM registers must be unchanged in all 256
   bits, and the six arithmetic flags unchanged ("Flags Affected: None").
   It shares nothing with the other probes.
   Exit 0: every row agrees. Exit 1: a row disagrees (printed). Exit 2: the harness is unusable — no rows, a declared
   instruction byte that is not the one assembled, CPUID unavailable.
   Exit 3: this processor (or its OS) lacks AES-NI, PCLMULQDQ or AVX — CPUID.01H:ECX bits 25, 1, 28, OSXSAVE (27) and
   XCR0 bits 1-2 (SSE and AVX state enabled). D342 predicts every leg has all of them, so no workflow leg accepts it.
   `--cpuid` stops after the feature check. */
#include <cpuid.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

struct eio { uint64_t y1[4], y2[4], y3[4], o1[4], o2[4], o3[4], f, fo; } __attribute__((aligned(32)));
typedef void (*efn)(struct eio *);

struct erow {
  const char *name;
  efn fn;
  unsigned dst;            /* 1: YMM1 is the destination (legacy SSE); 3: YMM3 (VEX) */
  uint64_t y1[4], y2[4], y3[4];
  unsigned f;
  uint64_t w[4];           /* the destination's expected 256 bits */
};

struct eop {
  const char *name;
  const unsigned char *at;
  unsigned len;
  unsigned char bytes[8];
};

#include "aes_rows.h"

#define ARITH 0x8d5u

static int features(void) {
  unsigned a = 0, b = 0, c = 0, d = 0;
  if (!__get_cpuid(1, &a, &b, &c, &d)) {
    printf("REFUSED: CPUID leaf 1 is not available\n");
    return 2;
  }
  int aes = (c >> 25) & 1, pclmul = (c >> 1) & 1, avx = (c >> 28) & 1, osxsave = (c >> 27) & 1;
  unsigned xlo = 0, xhi = 0;
  if (osxsave) __asm__ volatile("xgetbv" : "=a"(xlo), "=d"(xhi) : "c"(0));
  int ymm_os = (xlo & 6u) == 6u;
  printf("cpuid.01.ecx %08x xcr0 %08x  AES=%d PCLMULQDQ=%d AVX=%d OSXSAVE=%d XCR0.SSE+AVX=%d\n", c, xlo, aes, pclmul,
         avx, osxsave, ymm_os);
  if (!(aes && pclmul && avx && osxsave && ymm_os)) {
    printf("REFUSED: this processor or OS lacks AES-NI, PCLMULQDQ or AVX state\n");
    return 3;
  }
  return 0;
}

static int check_ops(void) {
  int bad = 0;
  for (size_t i = 0; i < sizeof EOPS / sizeof EOPS[0]; i++) {
    if (memcmp(EOPS[i].at, EOPS[i].bytes, EOPS[i].len) != 0) {
      printf("REFUSED %s: the bytes at its _at label are not the declared instruction\n", EOPS[i].name);
      bad = 1;
    }
  }
  return bad;
}

static int eq4(const uint64_t *x, const uint64_t *y) { return memcmp(x, y, 32) == 0; }

int main(int argc, char **argv) {
  size_t n = sizeof EROWS / sizeof EROWS[0], bad = 0;
  int fe = features();
  if (fe) return fe;
  if (argc > 1 && strcmp(argv[1], "--cpuid") == 0) return 0;
  if (n == 0 || check_ops()) return 2;
  for (size_t i = 0; i < n; i++) {
    const struct erow *r = &EROWS[i];
    static struct eio io;
    memset(&io, 0, sizeof io);
    memcpy(io.y1, r->y1, 32); memcpy(io.y2, r->y2, 32); memcpy(io.y3, r->y3, 32);
    io.f = r->f;
    r->fn(&io);
    unsigned got_f = (unsigned)(io.fo & ARITH);
    const uint64_t *got = r->dst == 1 ? io.o1 : io.o3;
    int dst = eq4(got, r->w);
    int others = eq4(io.o2, r->y2) && (r->dst == 1 ? eq4(io.o3, r->y3) : eq4(io.o1, r->y1));
    int flg = got_f == (r->f & ARITH);
    int ok = dst && others && flg;
    if (!ok) bad++;
    printf("%s %-28s ymm%u %016llx%016llx%016llx%016llx want %016llx%016llx%016llx%016llx  flags %03x want %03x%s%s\n",
           ok ? "ok  " : "DIFF", r->name, r->dst, (unsigned long long)got[3], (unsigned long long)got[2],
           (unsigned long long)got[1], (unsigned long long)got[0], (unsigned long long)r->w[3],
           (unsigned long long)r->w[2], (unsigned long long)r->w[1], (unsigned long long)r->w[0], got_f, r->f & ARITH,
           others ? "" : "  SOURCE WRITTEN", flg ? "" : "  FLAGS WRITTEN");
  }
  printf("rows %zu disagreements %zu\n", n, bad);
  return bad ? 1 : 0;
}
