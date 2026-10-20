/* hwprobe/vexsilc_probe.c — D350 (V8c: VPBROADCASTD from xmm and from m32, and the VEX.128 / VEX.256 MEMORY forms of
   VPMADDWD, VPMULHRSW, VPMADDUBSW and VPACKSSDW): the x86-64 referee for the V8c rows, restated from vexsilb_probe.c
   (D348) with a 64-byte memory buffer: RBX = &mem[off], and `off` is unaligned on half the memory rows.
   Runs each row's instruction on THIS processor with YMM1, YMM2, YMM3 loaded WHOLE from the row, MXCSR, RAX and the
   six arithmetic flags from the row, and compares, with the expectation hwprobe/mk_vexsilc_rows.py derived from the
   SDM (every row computed twice there, by a rule and by a textbook):
     - ALL 256 bits of YMM3 (the destination: a VEX.128 form must zero bits 255:128, a VEX.256 one write them with the
       high lane's result);
     - all 64 bits of RAX and all 32 bits of MXCSR, both unchanged (the four forms are integer and write neither);
     - YMM1 and YMM2 unchanged in all 256 bits, and the six arithmetic flags unchanged ("Flags Affected: None");
     - all 64 bytes of the memory buffer unchanged (a memory operand here is a SOURCE, never written).
   It shares nothing with the other probes.
   Exit 0: every row agrees. Exit 1: a row disagrees (printed). Exit 2: the harness is unusable — no rows, a declared
   instruction byte that is not the one assembled, CPUID unavailable.
   Exit 3: this processor (or its OS) lacks AVX or AVX2 — CPUID.01H:ECX bit 28 (AVX), bit 27 (OSXSAVE), XCR0 bits 1-2
   (SSE and AVX state enabled), CPUID.(EAX=07H,ECX=0):EBX bit 5 (AVX2). `--cpuid` stops after the feature check. */
#include <cpuid.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

struct xio {
  uint64_t y1[4], y2[4], y3[4], o1[4], o2[4], o3[4], f, fo, mx, mxo, rax, raxo, off, pad;
  unsigned char mem[64];
} __attribute__((aligned(32)));
typedef void (*xfn)(struct xio *);

struct xrow {
  const char *name;
  xfn fn;
  uint64_t y1[4], y2[4], y3[4];
  unsigned f;
  unsigned mx;             /* MXCSR in: 0x1F80 (all masked) with RC in bits 14:13 */
  uint64_t rax;
  uint64_t mem[8];         /* the 64-byte buffer, little-endian words */
  unsigned off;            /* RBX = &mem[off] */
  uint64_t w[4];           /* YMM3's expected 256 bits */
  uint64_t wrax;           /* RAX's expected 64 bits */
  unsigned wmx;            /* MXCSR's expected 32 bits: mx, unchanged */
};

struct xop {
  const char *name;
  const unsigned char *at;
  unsigned len;
  unsigned char bytes[8];
};

#include "vexsilc_rows.h"

#define ARITH 0x8d5u

static int features(void) {
  unsigned a = 0, b = 0, c = 0, d = 0;
  if (!__get_cpuid(1, &a, &b, &c, &d)) {
    printf("REFUSED: CPUID leaf 1 is not available\n");
    return 2;
  }
  int avx = (c >> 28) & 1, osxsave = (c >> 27) & 1;
  unsigned c1 = c;
  unsigned xlo = 0, xhi = 0;
  if (osxsave) __asm__ volatile("xgetbv" : "=a"(xlo), "=d"(xhi) : "c"(0));
  int ymm_os = (xlo & 6u) == 6u;
  unsigned b7 = 0;
  int avx2 = 0;
  if (__get_cpuid_max(0, 0) >= 7) {
    __cpuid_count(7, 0, a, b, c, d);
    b7 = b;
    avx2 = (b >> 5) & 1;
  }
  printf("cpuid.01.ecx %08x cpuid.07.ebx %08x xcr0 %08x  AVX=%d OSXSAVE=%d XCR0.SSE+AVX=%d AVX2=%d\n", c1, b7, xlo, avx,
         osxsave, ymm_os, avx2);
  if (!(avx && osxsave && ymm_os && avx2)) {
    printf("REFUSED: this processor or OS lacks AVX, AVX2 or the AVX register state\n");
    return 3;
  }
  return 0;
}

static int check_ops(void) {
  int bad = 0;
  for (size_t i = 0; i < sizeof XOPS / sizeof XOPS[0]; i++) {
    if (memcmp(XOPS[i].at, XOPS[i].bytes, XOPS[i].len) != 0) {
      printf("REFUSED %s: the bytes at its _at label are not the declared instruction\n", XOPS[i].name);
      bad = 1;
    }
  }
  return bad;
}

static int eq4(const uint64_t *x, const uint64_t *y) { return memcmp(x, y, 32) == 0; }

int main(int argc, char **argv) {
  size_t n = sizeof XROWS / sizeof XROWS[0], bad = 0;
  int fe = features();
  if (fe) return fe;
  if (argc > 1 && strcmp(argv[1], "--cpuid") == 0) return 0;
  if (n == 0 || check_ops()) return 2;
  for (size_t i = 0; i < n; i++) {
    const struct xrow *r = &XROWS[i];
    static struct xio io;
    memset(&io, 0, sizeof io);
    memcpy(io.y1, r->y1, 32); memcpy(io.y2, r->y2, 32); memcpy(io.y3, r->y3, 32);
    io.f = r->f;
    io.mx = r->mx;
    io.rax = r->rax;
    io.off = r->off;
    memcpy(io.mem, r->mem, 64);
    r->fn(&io);
    unsigned got_f = (unsigned)(io.fo & ARITH);
    unsigned got_mx = (unsigned)(io.mxo & 0xffffffffu);
    int dst = eq4(io.o3, r->w);
    int rax = io.raxo == r->wrax;
    int mx = got_mx == r->wmx;
    int srcs = eq4(io.o1, r->y1) && eq4(io.o2, r->y2);
    int flg = got_f == (r->f & ARITH);
    int memok = memcmp(io.mem, r->mem, 64) == 0;
    int ok = dst && rax && mx && srcs && flg && memok;
    if (!ok) bad++;
    printf("%s %-26s ymm3 %016llx%016llx%016llx%016llx want %016llx%016llx%016llx%016llx  rax %016llx want %016llx  "
           "mxcsr %04x want %04x%s%s\n",
           ok ? "ok  " : "DIFF", r->name, (unsigned long long)io.o3[3], (unsigned long long)io.o3[2],
           (unsigned long long)io.o3[1], (unsigned long long)io.o3[0], (unsigned long long)r->w[3],
           (unsigned long long)r->w[2], (unsigned long long)r->w[1], (unsigned long long)r->w[0],
           (unsigned long long)io.raxo, (unsigned long long)r->wrax, got_mx, r->wmx, srcs ? "" : "  SOURCE WRITTEN",
           flg ? "" : "  FLAGS WRITTEN");
    if (!memok) printf("     MEMORY WRITTEN %s\n", r->name);
  }
  printf("rows %zu disagreements %zu\n", n, bad);
  return bad ? 1 : 0;
}
