// REQUIRED_ARGS: -w

struct S
{
    extern(C) static int S_clock();
}
static assert(S.S_clock.mangleof == "S_clock");

class C
{
    extern(C) static int C_clock();
}
static assert(C.C_clock.mangleof == "C_clock");
