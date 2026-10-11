/* hwprobe/int_probe.c — D330: the x86-64 referee for the INTEGER rows (ADCX, ADOX, MULX).
   Runs each row's instruction on THIS processor with the GPRs and RFLAGS loaded from the row, and compares the
   destination registers and the six arithmetic flags with the expectations hwprobe/mk_int_rows.py derived from the
   SDM. The SSE referee (probe.c) is a separate program and is not touched by this one.
   Exit 0: every row agrees. Exit 1: a row disagrees (printed). Exit 2: the harness is unusable — no rows, a declared
   instruction byte that is not the one assembled, or a processor without BMI2 or ADX (a #UD is not a reading). */
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
  unsigned wf;      /* the six arithmetic flags after the instruction */
};

struct iop {
  const char *name;
  const unsigned char *at;
  unsigned len;
  unsigned char bytes[8];
};

#include "int_rows.h"

#define ARITH 0x8d5u

/* CPUID.(EAX=07H,ECX=0):EBX bit 8 is BMI2 (MULX) and bit 19 is ADX (ADCX, ADOX) — SDM Vol. 2A, CPUID, Table 3-8.
   Printed on every leg, and a processor without either REFUSES the run: executing the rows would raise #UD, and a
   crash is not a disagreement. */
static int features(void) {
  unsigned a = 0, b = 0, c = 0, d = 0;
  if (!__get_cpuid_count(7, 0, &a, &b, &c, &d)) {
    printf("REFUSED: CPUID leaf 7 is not available\n");
    return 1;
  }
  int bmi2 = (b >> 8) & 1, adx = (b >> 19) & 1;
  printf("cpuid.07.0.ebx %08x  BMI2=%d ADX=%d\n", b, bmi2, adx);
  if (!bmi2 || !adx) {
    printf("REFUSED: this processor lacks %s%s%s\n", bmi2 ? "" : "BMI2", (!bmi2 && !adx) ? " and " : "",
           adx ? "" : "ADX");
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
    int ok = io.r0 == r->w0 && (!r->two || io.r1 == r->w1) && got_f == r->wf;
    if (!ok) bad++;
    printf("%s %-32s r0 %016llx want %016llx  r1 %016llx want %016llx  flags %03x want %03x\n",
           ok ? "ok  " : "DIFF", r->name, (unsigned long long)io.r0, (unsigned long long)r->w0,
           (unsigned long long)io.r1, (unsigned long long)(r->two ? r->w1 : io.r1), got_f, r->wf);
  }
  printf("rows %zu disagreements %zu\n", n, bad);
  return bad ? 1 : 0;
}
