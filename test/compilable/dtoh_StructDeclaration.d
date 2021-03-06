/*
REQUIRED_ARGS: -HC -c -o-
PERMUTE_ARGS:
TEST_OUTPUT:
---
#pragma once

// Automatically generated by dmd -HC

#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#define _d_void void
#define _d_bool bool
#define _d_byte signed char
#define _d_ubyte unsigned char
#define _d_short short
#define _d_ushort unsigned short
#define _d_int int
#define _d_uint unsigned
#define _d_long $?:32=long long|64=long$
#define _d_ulong unsigned $?:32=long long|64=long$
#define _d_float float
#define _d_double double
#define _d_real long double
#define _d_char char
#define _d_wchar wchar_t
#define _d_dchar unsigned
typedef _d_long d_int64;

#define _d_null NULL


// Parsing module dtoh_StructDeclaration
struct S;
struct Inner;
struct S
{
    _d_byte a;
    _d_int b;
    _d_long c;
    S() : a(), b(), c() {}
};

struct S2
{
    _d_int a;
    _d_int b;
    _d_long c;
    S2(_d_int a);
    S2() : a(42), b(), c() {}
};

struct S3
{
    _d_int a;
    _d_int b;
    _d_long c;
    extern "C" S3(_d_int a);
    S3() : a(42), b(), c() {}
};

struct
#if defined(__GNUC__) || defined(__clang__)
    __attribute__((packed, aligned(1)))
#elif defined(_MSC_VER)
    __declspec(align(1))
#elif defined(__DMC__)
    #pragma pack(push, 1)
#endif
Aligned
{
    _d_byte a;
    _d_int b;
    _d_long c;
    Aligned(_d_int a);
    Aligned() : a(), b(), c() {}
};
#if defined(__DMC__)
    #pragma pack(pop)
#endif

struct A
{
    _d_int a;
    S s;
    // ignoring extern () block because of linkage
    extern "C" _d_void bar();
    _d_void baz(_d_int x = 42);
    struct
    {
        _d_int x;
        _d_int y;
    };
    union
    {
        _d_int u1;
        _d_char u2[4$?:32=u|64=LLU$];
    };
struct Inner
{
    _d_int x;
    Inner() : x() {}
};

typedef Inner I;
class C;

    A() : a(), s() {}
};
---
*/

/*
StructDeclaration has the following issues:
  * align different than 1 does nothing; we should support align(n), where `n` in [1, 2, 4, 8, 16]
  * align(n): inside struct definition doesn’t add alignment, but breaks generation of default ctors
  * default ctors should be generated only if struct has no ctors
  * if a struct has ctors defined, only default ctor (S() { … }) should be generated to init members to default values, and the defined ctors must be declared
  * if a struct has ctors defined, the declared ctors must have the name of the struct, not __ctor, as `__ctor` might not be portable
  * if a struct has a `member = void`, dtoh code segfaults
  * a struct should only define ctors if it’s extern (C++)
*/

extern (C++) struct S
{
    byte a;
    int b;
    long c;
}

extern (C++) struct S2
{
    int a = 42;
    int b;
    long c;

    this(int a) {}
}

extern (C) struct S3
{
    int a = 42;
    int b;
    long c;

    this(int a) {}
}

extern (C++) align(1) struct Aligned
{
    //align(1):
    byte a;
    int b;
    long c;

    this(int a) {}
}

extern (C++) struct A
{
    int a;
    S s;

    extern (D) void foo();
    extern (C) void bar() {}
    extern (C++) void baz(int x = 42) {}

    struct
    {
        int x;
        int y;
    }

    union
    {
        int u1;
        char[4] u2;
    }

    struct Inner
    {
        int x;
    }

    alias I = Inner;

    extern(C++) class C;

}
