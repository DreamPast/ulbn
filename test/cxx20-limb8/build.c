#include <limits.h>
typedef unsigned char ulbn_limb_t;
typedef signed char ulbn_slimb_t;
#define ULBN_LIMB_MAX UCHAR_MAX
#define ULBN_SLIMB_MAX SCHAR_MAX
#define ULBN_SLIMB_MIN SCHAR_MIN
#include "ulbn.c"
