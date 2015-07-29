struct ArrayDT { ~this() pure nothrow @safe @nogc {} }
struct ArrayPB { this(this) pure nothrow @safe @nogc {} }
struct ArrayDTPB
{
    ~this() pure nothrow @safe @nogc {}
    this(this) pure nothrow @safe @nogc {}
}

struct TestDT { ArrayDT[1] array; }
struct TestPB { ArrayPB[1] array; }
struct TestDTPB { ArrayDTPB[1] array; }

class CTestDT { ArrayDT[1] array; }
class CTestPB { ArrayPB[1] array; }
class CTestDTPB { ArrayDTPB[1] array; }
