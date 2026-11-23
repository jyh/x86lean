/* hwprobe/pmaddwd_mm_probe.c — D405 §4: MMX PMADDWD on silicon, the third source.
 *
 * The question. The model's MMX pmaddwd (the XMM lane function, low 64 bits; D404 §1) and ACL2 x86isa's
 * `x86-pmaddwd-mmx` disagree in 162 cases. x86isa calls `(simd-muladd-spec (* 8 operand-size) 16 src1 src2)`: chunk size
 * 16, where `simd-muladd-spec`'s own documentation says the MMX form uses chunk size 32 (16-bit halves). The processor
 * decides.
 *
 * Rows come from `pmaddwd_mm_rows.h`, GENERATED from the differential's own record files: the two operands, the model's
 * result and the oracle's. Nothing here is typed. Each pmaddwd reading is MODEL, ORACLE or NEITHER.
 * CONTROLS: paddw rows on which the two models agree; the probe REFUSES (exit 2) if one does not read that value.
 * PLANT (-DPLANT): the pmaddwd rows run paddw instead, so every reading must be NEITHER and the run must not give a
 * verdict (exit 3). That is what shows the classification can fail.
 * Exit: 0 with "VERDICT model" or "VERDICT oracle" when every pmaddwd row agrees with one side; 3 "VERDICT mixed";
 * 2 when a control fails; 4 off x86-64.
 */
#include <stdio.h>
#include <string.h>
#include "pmaddwd_mm_rows.h"

#if !defined(__x86_64__)
int main(void) { puts("REFUSED: not x86-64"); return 4; }
#else

static unsigned long long run_pmaddwd(unsigned long long a, unsigned long long b) {
  unsigned long long r = a;
#ifdef PLANT
  __asm__ volatile("movq %0, %%mm0\n\tmovq %1, %%mm1\n\tpaddw %%mm1, %%mm0\n\tmovq %%mm0, %0\n\temms"
                   : "+m"(r) : "m"(b) : "mm0", "mm1");
#else
  __asm__ volatile("movq %0, %%mm0\n\tmovq %1, %%mm1\n\tpmaddwd %%mm1, %%mm0\n\tmovq %%mm0, %0\n\temms"
                   : "+m"(r) : "m"(b) : "mm0", "mm1");
#endif
  return r;
}

static unsigned long long run_paddw(unsigned long long a, unsigned long long b) {
  unsigned long long r = a;
  __asm__ volatile("movq %0, %%mm0\n\tmovq %1, %%mm1\n\tpaddw %%mm1, %%mm0\n\tmovq %%mm0, %0\n\temms"
                   : "+m"(r) : "m"(b) : "mm0", "mm1");
  return r;
}

int main(int argc, char **argv) {
  (void)argv;
  if (argc > 1) {
    unsigned a, b, c, d;
    __asm__("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d) : "a"(1), "c"(0));
    printf("cpuid.01h edx bit 23 (MMX) = %u\n", (d >> 23) & 1);
    return ((d >> 23) & 1) ? 0 : 2;
  }
  int ok = 1;
  for (size_t i = 0; i < sizeof CT / sizeof CT[0]; i++) {
    unsigned long long g = run_paddw(CT[i].a, CT[i].b);
    int good = g == CT[i].model && g == CT[i].oracle;
    printf("%s control %s/%d got=%016llx want=%016llx\n", good ? "ok  " : "DIFF", CT[i].name, CT[i].pre, g, CT[i].model);
    ok &= good;
  }
  if (!ok) { puts("REFUSED: a control failed, so no pmaddwd reading is evidence"); return 2; }
  int model = 0, oracle = 0, n = (int)(sizeof PM / sizeof PM[0]);
  for (int i = 0; i < n; i++) {
    unsigned long long g = run_pmaddwd(PM[i].a, PM[i].b);
    const char *cls = g == PM[i].model ? "MODEL" : g == PM[i].oracle ? "ORACLE" : "NEITHER";
    model += g == PM[i].model; oracle += g == PM[i].oracle;
    printf("ROW pmaddwd/%d got=%016llx model=%016llx oracle=%016llx %s\n", PM[i].pre, g, PM[i].model, PM[i].oracle, cls);
  }
  if (model == n) { printf("VERDICT model (%d of %d)\n", model, n); return 0; }
  if (oracle == n) { printf("VERDICT oracle (%d of %d)\n", oracle, n); return 0; }
  printf("VERDICT mixed (model %d, oracle %d, of %d)\n", model, oracle, n);
  return 3;
}
#endif
