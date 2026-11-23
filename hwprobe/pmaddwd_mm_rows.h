/* GENERATED from run/lean.txt and run/oracle.txt (D405 §4): pre mm0, pre mm1, the model's post mm0, the oracle's. */
typedef struct { const char *name; int pre; unsigned long long a, b, model, oracle; } Row;
static const Row PM[] = {
  { "pmaddwd", 0, 0xffffffffffffffffULL, 0x0101010101010100ULL, 0xfffffdfefffffdffULL, 0xfffefffefffeffffULL },
  { "pmaddwd", 1, 0xfffffffffffffffeULL, 0x01010101010100ffULL, 0xfffffdfefffffd01ULL, 0xfffefffefffe0002ULL },
  { "pmaddwd", 2, 0xfffffffffffffffdULL, 0x01010101010100feULL, 0xfffffdfefffffc05ULL, 0xfffefffefffe0006ULL },
  { "pmaddwd", 3, 0xfffffffffffffff0ULL, 0x01010101010100f1ULL, 0xfffffdfeffffefefULL, 0xfffefffefffe00f0ULL },
  { "pmaddwd", 40, 0xffffffffffffff00ULL, 0x0101010101010001ULL, 0xfffffdfefffffdffULL, 0xfffefffefffe0000ULL },
  { "pmaddwd", 80, 0x2255b17a4f291d74ULL, 0x2356b27b502a1e75ULL, 0x1c84412c1c4adabeULL, 0x213452b01f6a386aULL },
};
static const Row CT[] = {
  { "paddw", 0, 0xffffffffffffffffULL, 0x0101010101010100ULL, 0x01000100010000ffULL, 0x01000100010000ffULL },
  { "paddw", 40, 0xffffffffffffff00ULL, 0x0101010101010001ULL, 0x010001000100ff01ULL, 0x010001000100ff01ULL },
};
