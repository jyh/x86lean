/* hwprobe/int_probe.c — D330 (ADCX, ADOX, MULX) and D334 (ANDN, BEXTR, BLSMSK, BLSR, BZHI, PDEP, PEXT, RORX, MOVNTI):
   the x86-64 referee for the INTEGER rows.
   Runs each row's instruction on THIS processor with the GPRs and RFLAGS loaded from the row, and compares the
   destination registers (or, for MOVNTI, the quadword stored to) and the arithmetic flags the row defines with the expectations hwprobe/mk_int_rows.py derived from the
   SDM. The SSE referee (probe.c) is a separate program and is not touched by this one.
   Exit 0: every row agrees. Exit 1: a row disagrees (printed). Exit 2: the harness is unusable — no rows, a declared
   instruction byte that is not the one assembled, or a processor without BMI1, BMI2, ADX or SSE2 (a #UD is not a
   reading). */
#include <cpuid.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

struct iio { uint64_t a, b, d, f, r0, r1, fo; };
typedef void (*ifn)(struct iio *);

struct irow {
  const char *name;
  ifn fn;
  uint64_t a, b, d;
  unsigned f;
  uint64_t w0, w1;
  int two;          /* 1: r1 is compared too (MULX's low half, or the untouched canary of the same-register form) */
  unsigned wf;      /* the arithmetic flags after the instruction, on the bits fm names */
  unsigned fm;      /* D334: the flags compared — the six (0x8d5) less any the SDM leaves undefined for this form */
};

struct iop {
  const char *name;
  const unsigned char *at;
  unsigned len;
  unsigned char bytes[8];
};

#include "int_rows.h"

#define ARITH 0x8d5u

/* CPUID.(EAX=07H,ECX=0):EBX bit 3 is BMI1 (ANDN, BEXTR, BLSMSK, BLSR), bit 8 is BMI2 (BZHI, MULX, PDEP, PEXT, RORX)
   and bit 19 is ADX (ADCX, ADOX); CPUID.01H:EDX bit 26 is SSE2 (MOVNTI) — SDM Vol. 2A, CPUID, Tables 3-8 and 3-11.
   Printed on every leg, and a processor without any one of them REFUSES the run: executing the rows would raise #UD,
   and a crash is not a disagreement. */
static int features(void) {
  unsigned a = 0, b = 0, c = 0, d = 0, a1 = 0, b1 = 0, c1 = 0, d1 = 0;
  if (!__get_cpuid_count(7, 0, &a, &b, &c, &d) || !__get_cpuid(1, &a1, &b1, &c1, &d1)) {
    printf("REFUSED: CPUID leaf 7 or leaf 1 is not available\n");
    return 1;
  }
  int bmi1 = (b >> 3) & 1, bmi2 = (b >> 8) & 1, adx = (b >> 19) & 1, sse2 = (d1 >> 26) & 1;
  printf("cpuid.07.0.ebx %08x cpuid.01.edx %08x  BMI1=%d BMI2=%d ADX=%d SSE2=%d\n", b, d1, bmi1, bmi2, adx, sse2);
  if (!bmi1 || !bmi2 || !adx || !sse2) {
    printf("REFUSED: this processor lacks%s%s%s%s\n", bmi1 ? "" : " BMI1", bmi2 ? "" : " BMI2", adx ? "" : " ADX",
           sse2 ? "" : " SSE2");
    return 1;
  }
  return 0;
}

/* Reading code bytes through a pointer to a label is not ISO C; it is what both compilers this probe is built with
   do, and a mismatch refuses the run rather than trusting it. */
static int check_ops(void) {
  int bad = 0;
  for (size_t i = 0; i < sizeof IOPS / sizeof IOPS[0]; i++) {
    if (memcmp(IOPS[i].at, IOPS[i].bytes, IOPS[i].len) != 0) {
      printf("REFUSED %s: the bytes at its _at label are not the declared instruction\n", IOPS[i].name);
      bad = 1;
    }
  }
  return bad;
}

int main(void) {
  size_t n = sizeof IROWS / sizeof IROWS[0], bad = 0;
  if (n == 0 || features() || check_ops()) return 2;
  for (size_t i = 0; i < n; i++) {
    const struct irow *r = &IROWS[i];
    struct iio io = { r->a, r->b, r->d, r->f, 0, 0, 0 };
    r->fn(&io);
    unsigned got_f = (unsigned)(io.fo & ARITH);
    /* D334: the comparison is on fm; got_f is printed WHOLE, so a leg's readings of the undefined bits are on record. */
    int ok = io.r0 == r->w0 && (!r->two || io.r1 == r->w1) && (got_f & r->fm) == (r->wf & r->fm) && (r->fm & ~ARITH) == 0
             && r->fm != 0;
    if (!ok) bad++;
    printf("%s %-32s r0 %016llx want %016llx  r1 %016llx want %016llx  flags %03x want %03x mask %03x\n",
           ok ? "ok  " : "DIFF", r->name, (unsigned long long)io.r0, (unsigned long long)r->w0,
           (unsigned long long)io.r1, (unsigned long long)(r->two ? r->w1 : io.r1), got_f, r->wf & r->fm, r->fm);
  }
  printf("rows %zu disagreements %zu\n", n, bad);
  return bad ? 1 : 0;
}
