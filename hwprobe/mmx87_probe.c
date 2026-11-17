/* hwprobe/mmx87_probe.c — D402 §2.2: what an MMX STORE does to the x87 tag word and TOP, on silicon.
 *
 * The question. Vendored ACL2 x86isa (at the pin) applies `mmx-instruction-updates` (tag word := 0,
 * TOP := 0) on its two to-MMX moves and NOT on its two from-MMX moves (0F 7E, 0F 7F), while that
 * function's own documentation says it covers "all MMX instructions except EMMS". The model follows the
 * documented rule. The differential disagrees in exactly 564 places (D402 §4). This probe asks the
 * processor, which is the third source.
 *
 * Each row runs one instruction from a KNOWN x87 state and reads the tag word (FTW, full 16 bits) and
 * TOP (FSW bits 13:11) back with FNSTENV:
 *   P0  after FNINIT           FTW = 0xFFFF, TOP = 0
 *   P7  after FNINIT; FLD1      FTW = 0x3FFF, TOP = 7   (TOP and the tag word both differ from 0)
 * A store reading is RULE when it reads (0x0000, 0) and X86ISA when it reads the pre-state unchanged.
 *
 * CONTROLS, which must hold or the probe REFUSES (exit 2) and says nothing about the stores:
 *   a load (movd r32 -> mm) and movq mm -> mm, where both models agree: (0x0000, 0) from either state;
 *   a non-MMX add, which must leave the state unchanged;
 *   EMMS, whose tag word must read 0xFFFF (its TOP is not judged: nothing here depends on it).
 * PLANT (-DPLANT): the load control's instruction becomes a NOP, so its control must fail and the run
 * must refuse. That is what shows the controls can fail.
 *
 * Exit: 0 with "VERDICT rule" or "VERDICT x86isa" when all eight store readings agree with one
 * hypothesis; 3 ("VERDICT mixed") otherwise; 2 when a control fails; 4 off x86-64.
 */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#if !defined(__x86_64__)
int main(void) { puts("REFUSED: not x86-64"); return 4; }
#else

typedef struct { uint16_t ftw, top; } X87;

static X87 decode(const unsigned char *env) {
  uint16_t fsw, ftw;
  memcpy(&fsw, env + 4, 2);
  memcpy(&ftw, env + 8, 2);
  X87 r = { ftw, (uint16_t)((fsw >> 11) & 7) };
  return r;
}

static uint64_t mem64 = 0x0123456789abcdefULL;

/* One row: set the pre-state, run INSN, read the environment, then EMMS so the next row starts clean. */
#define ROW(NAME, PRE, INSN)                                                       \
  static X87 NAME(void) {                                                          \
    unsigned char env[28];                                                         \
    uint64_t scratch = 0;                                                          \
    __asm__ volatile(PRE "\n\t" INSN "\n\tfnstenv %0\n\temms"                    \
                     : "=m"(env), "+m"(scratch), "+m"(mem64)                       \
                     : "r"((uint64_t)0x1122334455667788ULL)                        \
                     : "rax", "rcx", "mm0", "mm1", "mm3", "memory");               \
    return decode(env);                                                            \
  }

#define P0 "fninit"
#define P7 "fninit\n\tfld1"

/* The four store forms (the question). */
ROW(st_movd_r_p0, P0, "movd %%mm0, %%ecx")
ROW(st_movd_r_p7, P7, "movd %%mm0, %%ecx")
ROW(st_movq_r_p0, P0, "movq %%mm0, %%rax")
ROW(st_movq_r_p7, P7, "movq %%mm0, %%rax")
ROW(st_movd_m_p0, P0, "movd %%mm0, %1")
ROW(st_movd_m_p7, P7, "movd %%mm0, %1")
ROW(st_movq_m_p0, P0, "movq %%mm3, %2")
ROW(st_movq_m_p7, P7, "movq %%mm3, %2")

/* The controls. */
#ifdef PLANT
ROW(ld_movd_p0, P0, "nop")
ROW(ld_movd_p7, P7, "nop")
#else
ROW(ld_movd_p0, P0, "movd %%ecx, %%mm0")
ROW(ld_movd_p7, P7, "movd %%ecx, %%mm0")
#endif
ROW(mm_movq_p0, P0, "movq %%mm1, %%mm0")
ROW(mm_movq_p7, P7, "movq %%mm1, %%mm0")
ROW(nonmmx_p0, P0, "add %%ecx, %%eax")
ROW(nonmmx_p7, P7, "add %%ecx, %%eax")
ROW(emms_p0, P0, "emms")
ROW(emms_p7, P7, "emms")

static const X87 PRE0 = { 0xFFFF, 0 }, PRE7 = { 0x3FFF, 7 }, ZERO = { 0x0000, 0 };

static int eq(X87 a, X87 b) { return a.ftw == b.ftw && a.top == b.top; }

static int control(const char *name, X87 got, X87 want, int judge_top) {
  int ok = got.ftw == want.ftw && (!judge_top || got.top == want.top);
  printf("%s %-12s ftw=%04x top=%u   want ftw=%04x%s\n", ok ? "ok  " : "DIFF", name, got.ftw, got.top,
         want.ftw, judge_top ? (want.top ? " top=7" : " top=0") : " (top not judged)");
  return ok;
}

int main(int argc, char **argv) {
  if (argc > 1 && strcmp(argv[1], "--cpuid") == 0) {
    unsigned a, b, c, d;
    __asm__("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d) : "a"(1), "c"(0));
    printf("cpuid.01h edx bit 23 (MMX) = %u\n", (d >> 23) & 1);
    return ((d >> 23) & 1) ? 0 : 2;
  }
  int ok = 1;
  ok &= control("ld_movd_p0", ld_movd_p0(), ZERO, 1);
  ok &= control("ld_movd_p7", ld_movd_p7(), ZERO, 1);
  ok &= control("mm_movq_p0", mm_movq_p0(), ZERO, 1);
  ok &= control("mm_movq_p7", mm_movq_p7(), ZERO, 1);
  ok &= control("nonmmx_p0", nonmmx_p0(), PRE0, 1);
  ok &= control("nonmmx_p7", nonmmx_p7(), PRE7, 1);
  ok &= control("emms_p0", emms_p0(), PRE0, 0);
  ok &= control("emms_p7", emms_p7(), PRE0, 0);
  if (!ok) { puts("REFUSED: a control failed, so no store reading is evidence"); return 2; }

  struct { const char *name; X87 (*f)(void); X87 pre; } st[] = {
    { "st_movd_r_p0", st_movd_r_p0, PRE0 }, { "st_movd_r_p7", st_movd_r_p7, PRE7 },
    { "st_movq_r_p0", st_movq_r_p0, PRE0 }, { "st_movq_r_p7", st_movq_r_p7, PRE7 },
    { "st_movd_m_p0", st_movd_m_p0, PRE0 }, { "st_movd_m_p7", st_movd_m_p7, PRE7 },
    { "st_movq_m_p0", st_movq_m_p0, PRE0 }, { "st_movq_m_p7", st_movq_m_p7, PRE7 },
  };
  int rule = 0, x86isa = 0, n = (int)(sizeof st / sizeof st[0]);
  for (int i = 0; i < n; i++) {
    X87 g = st[i].f();
    const char *cls = eq(g, ZERO) ? "RULE" : eq(g, st[i].pre) ? "X86ISA" : "NEITHER";
    rule += eq(g, ZERO); x86isa += eq(g, st[i].pre);
    printf("STORE %-12s ftw=%04x top=%u   pre ftw=%04x top=%u   %s\n", st[i].name, g.ftw, g.top,
           st[i].pre.ftw, st[i].pre.top, cls);
  }
  if (rule == n) { printf("VERDICT rule (%d of %d store readings: tag 0, TOP 0)\n", rule, n); return 0; }
  if (x86isa == n) { printf("VERDICT x86isa (%d of %d store readings: x87 state unchanged)\n", x86isa, n); return 0; }
  printf("VERDICT mixed (rule %d, x86isa %d, of %d)\n", rule, x86isa, n);
  return 3;
}
#endif
