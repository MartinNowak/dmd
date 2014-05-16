struct S12739
{
    int opApply(int delegate(int) nothrow dg) nothrow
    {
        return 0;
    }
}

void test12739()
{
    S12739 s;
    foreach (e; s)
    {}

    static assert(!__traits(compiles, {foreach (e; s) {throw new Exception("");}}));
}
