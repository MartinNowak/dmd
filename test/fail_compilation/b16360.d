/*
REQUIRED_ARGS: -inline

TEST_OUTPUT:
---
fail_compilation/b16360.d(12): Error: function `b16360.foo` cannot inline function
fail_compilation/b16360.d(25): Error: function `b16360.bar` cannot inline function
---
*/

pragma(inline, true)
auto foo()
{
    static struct U
    {
        int a = 42;
        float b;
        ~this(){} // __dtor: inline not allowed
    }
    U u;
    return u.a;
}

pragma(inline, true)
auto bar()
{
    class U   // class : inline not allowed
    {
        int a = 42;
        float b;
    }
    return (new U).a;
}

void main()
{
    auto f = foo();
    auto b = bar();
}
