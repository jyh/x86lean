/* hwprobe/vexsild_probe.c — D354 (V9b: the VEX.128 / VEX.256 MEMORY forms of VMOVDQA VMOVDQU VMOVAPS VMOVUPS VMOVAPD
   VMOVUPD, loads and stores): the x86-64 referee for the V9b rows, restated from vexsilc_probe.c (D350) with two
   additions — a row may STORE (its expected 64-byte buffer is carried), and a row may be a FAULT row.
   ⭐ FAULT ROWS, NEW TO THIS HARNESS. An aligned kind at a misaligned address raises #GP(0). The OS delivers it as SIGSEGV
   (Linux) or SIGSEGV/SIGBUS (macOS); a handler installed for both siglongjmps back to the caller, which records the
   signal. A row expected to fault agrees only if the call faulted AND the buffer is byte-for-byte unchanged; a row
   expected to run agrees only if it did not fault. x86isa executes every such encoding (D354 P1), so this is the only
   second source the alignment rule has.
   Runs each row's instruction on THIS processor with YMM1, YMM2, YMM3 loaded WHOLE from the row, MXCSR, RAX and the
   six arithmetic flags from the row, and compares, with the expectation hwprobe/mk_vexsild_rows.py derived from the SDM
   (every row computed twice there, by a rule and by a textbook):
     - ALL 256 bits of YMM3 (a load's destination: a VEX.128 load zeroes bits 255:128; a store leaves YMM3 unchanged);
     - all 64 bytes of the buffer (a load leaves it unchanged; a store writes exactly its 16 or 32 bytes);
     - YMM1, YMM2, RAX, MXCSR and the six arithmetic flags unchanged.
   Exit 0: every row agrees. Exit 1: a row disagrees (printed). Exit 2: the harness is unusable — no rows, a declared
   instruction byte that is not the one assembled, a signal handler that cannot be installed, CPUID unavailable.
   Exit 3: this processor (or its OS) lacks AVX or AVX2. `--cpuid` stops after the feature check. */
#include <cpuid.h>
#include <setjmp.h>
#include <signal.h>
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
  uint64_t mem[8];         /* the 64-byte buffer, little-endian words; RBX = &mem[off], and mem is 32-byte aligned */
  unsigned off;
  int fault;               /* 1: the row must raise #GP and write nothing */
  uint64_t w[4];           /* YMM3's expected 256 bits (when it runs) */
  uint64_t wmem[8];        /* the buffer's expected 64 bytes (when it runs) */
};

struct xop {
  const char *name;
  const unsigned char *at;
  unsigned len;
  unsigned char bytes[8];
};

#include "vexsild_rows.h"

#define ARITH 0x8d5u

static sigjmp_buf jb;
static void on_fault(int sig) { siglongjmp(jb, sig); }

static int install(void) {
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_handler = on_fault;
  sigemptyset(&sa.sa_mask);
  if (sigaction(SIGSEGV, &sa, 0) != 0 || sigaction(SIGBUS, &sa, 0) != 0) {
    printf("REFUSED: cannot install the SIGSEGV/SIGBUS handler\n");
    return 2;
  }
  return 0;
}

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

static const char *signame(int s) { return s == SIGSEGV ? "SIGSEGV" : s == SIGBUS ? "SIGBUS" : "signal?"; }

int main(int argc, char **argv) {
  size_t n = sizeof XROWS / sizeof XROWS[0], bad = 0, nfault = 0;
  int fe = features();
  if (fe) return fe;
  if (argc > 1 && strcmp(argv[1], "--cpuid") == 0) return 0;
  if (n == 0 || check_ops() || install()) return 2;
  unsigned mx0 = 0;
  __asm__ volatile("stmxcsr %0" : "=m"(mx0));
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
    volatile int sig = sigsetjmp(jb, 1);
    if (sig == 0) r->fn(&io);
    else __asm__ volatile("ldmxcsr %0" : : "m"(mx0));  /* a fault skipped POST, which restores MXCSR */
    int faulted = sig != 0;
    if (faulted) nfault++;
    int ok;
    if (r->fault) {
      int memok = memcmp(io.mem, r->mem, 64) == 0;
      ok = faulted && memok;
      printf("%s %-24s %s%s%s (want a fault)\n", ok ? "ok  " : "DIFF", r->name,
             faulted ? "faulted " : "RAN", faulted ? signame(sig) : "", memok ? "" : "  MEMORY WRITTEN");
    } else if (faulted) {
      ok = 0;
      printf("DIFF %-24s FAULTED %s (want it to run)\n", r->name, signame(sig));
    } else {
      unsigned got_f = (unsigned)(io.fo & ARITH);
      unsigned got_mx = (unsigned)(io.mxo & 0xffffffffu);
      int dst = eq4(io.o3, r->w);
      int rax = io.raxo == r->rax;
      int mx = got_mx == r->mx;
      int srcs = eq4(io.o1, r->y1) && eq4(io.o2, r->y2);
      int flg = got_f == (r->f & ARITH);
      int memok = memcmp(io.mem, r->wmem, 64) == 0;
      ok = dst && rax && mx && srcs && flg && memok;
      printf("%s %-24s ymm3 %016llx%016llx%016llx%016llx want %016llx%016llx%016llx%016llx%s%s%s%s\n",
             ok ? "ok  " : "DIFF", r->name, (unsigned long long)io.o3[3], (unsigned long long)io.o3[2],
             (unsigned long long)io.o3[1], (unsigned long long)io.o3[0], (unsigned long long)r->w[3],
             (unsigned long long)r->w[2], (unsigned long long)r->w[1], (unsigned long long)r->w[0],
             memok ? "" : "  MEMORY", srcs ? "" : "  SOURCE WRITTEN", flg ? "" : "  FLAGS WRITTEN",
             (rax && mx) ? "" : "  RAX/MXCSR");
    }
    if (!ok) bad++;
  }
  printf("rows %zu faulted %zu disagreements %zu\n", n, nfault, bad);
  return bad ? 1 : 0;
}
