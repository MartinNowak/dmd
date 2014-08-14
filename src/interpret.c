/* Compiler implementation of the D programming language
 * Copyright (c) 1999-2014 by Digital Mars
 * All Rights Reserved
 * written by Walter Bright
 * http://www.digitalmars.com
 * Distributed under the Boost Software License, Version 1.0.
 * http://www.boost.org/LICENSE_1_0.txt
 * https://github.com/D-Programming-Language/dmd/blob/master/src/interpret.c
 */
#include <typeinfo>

#include "root.h"
#include "aav.h"

#include "aggregate.h"
#include "ctfe.h"
#include "declaration.h"
#include "expression.h"
#include "mtype.h"
#include "statement.h"
#include "target.h"

namespace interpreter
{
enum OP
{
    OPunde,
    OPload,
    OPadd_i, OPadd_r,
    OPand,
    OPcast,

    OPlt_i, OPlt_r, OPlt_s,
    OPle_i, OPle_r, OPle_s,
    OPgt_i, OPgt_r, OPgt_s,
    OPge_i, OPge_r, OPge_s,

    OPdiv_i, OPdiv_r,
    OPeq_i, OPeq_r, OPeq_s,
    OPmin_i, OPmin_r,
    OPneg_i, OPneg_r,
    OPor,
    OPshl,
    OPshr,
    OPvar,
    OPnull,
    OPmul_i, OPmul_r,
    OPcall,
    OPind,
    OPnot,
    OPcom,
    OPcond,
    OPaddass,

    OPstruct,
    OParray,

    OPvoid,
    OPnew,

    OPret,

    OPjmp,
    OPcjmp,
};

struct String
{
    void *data;
    size_t nbytes;
};

union Value
{
    dinteger_t int_;
    uinteger_t uint_;
    real_t real_;
    String str_;
};

struct ByteCode
{
    Array<unsigned char> data;
    Array<Value> constants;
};

class BCCompiler : public Visitor
{
public:
    BCCompiler(ByteCode *bc)
    : vars(NULL)
    , bc(bc)
    , failure(false)
    {}

    // Statements
    void visit(Statement *s)
    {
        s->error("can't compile %s", typeid(*s).name());
        assert(0);
    }

    void visit(CompoundStatement *s)
    {
        for (size_t i = 0; i < s->statements->dim; ++i)
            (*s->statements)[i]->accept(this);
    }

    void visit(ExpStatement *s)
    {
        s->exp->accept(this);
    }

    void visit(ReturnStatement *s)
    {
        s->exp->accept(this);
        write8(OPret);
    }

    void visit(ForStatement *s)
    {
        if (s->init) s->init->accept(this);
        const size_t start = bc->data.dim;
        s->condition->accept(this);
        write8(OPcjmp);
        const size_t fixup = bc->data.dim;
        write32(0);

        s->body->accept(this);
        if (s->increment) s->increment->accept(this);
        write8(OPjmp);
        write32(-(bc->data.dim - start));

        bc->data[fixup] = bc->data.dim - fixup;
    }

    void visit(WhileStatement *s)
    {
        assert(0);
    }

    // Expressions
    void visit(Expression *e)
    {
        e->error("can't compile %s", typeid(*e).name());
        assert(0);
    }

    void visit(IntegerExp *e)
    {
        Value v;
        v.int_ = e->toInteger();
        write8(OPload);
        writeULEB(pushConst(v));
    }

    void visit(RealExp *e)
    {
        Value v;
        v.real_ = e->toReal();
        write8(OPload);
        writeULEB(pushConst(v));
    }

    void visit(StringExp *e)
    {
        Value v;
        v.str_.data = e->string;
        v.str_.nbytes = e->sz * e->len;
        write8(OPload);
        writeULEB(pushConst(v));
    }

    void visit(StructLiteralExp *e)
    {
        // e->error("StructLiteralExp interpret not yet implemented.");
        for (size_t i = 0; i < e->elements->dim; i++)
        {
            if ((*e->elements)[i])
                (*e->elements)[i]->accept(this);
            else
                write8(OPvoid);
        }
        // initialize hidden nested pointer with null
        if (e->sd->fields.dim == e->elements->dim + 1)
        {
            assert(e->sd->isNested());
            write8(OPnull);
        }
        write8(OPstruct);
    }

    void visit(ArrayLiteralExp *e)
    {
        for (size_t i = 0; i < e->elements->dim; ++i)
            (*e->elements)[i]->accept(this);
        write8(OParray);
        writez(e->elements->dim);
    }

    void visit(CastExp *e)
    {
        e->e1->accept(this);

        // TODO: use e->to instead?
        assert(e->type->toBasetype() == e->to->toBasetype());

        if (e->to->toBasetype()->isintegral() &&
            e->e1->type->toBasetype()->isintegral())
        {
            // noop, simply reinterpret dinteger_t value
        }
        else if (e->to->toBasetype()->ty == Tpointer &&
                 e->e1->type->toBasetype()->isintegral())
        {
            // allow unsafe cast, e.g. to initialize Windows HANDLE
        }
        else
        {
            write8(OPcast);
            write8(e->e1->type->toBasetype()->ty);
            write8(e->type->toBasetype()->ty);
        }
    }

    void visit(VarExp *e)
    {
        write8(OPvar);
        if (VarDeclaration *vd = e->var->isVarDeclaration())
            write32((size_t)dmd_aaGetRvalue(vars, vd));
        else if (FuncDeclaration *fd = e->var->isFuncDeclaration())
            write32(0); // write global ctfe function index
        else
            assert(0);
    }

    void visit(NullExp *e)
    {
        write8(OPnull);
    }

    void visit(CallExp *e)
    {
        for (size_t i = 0; i < e->arguments->dim; ++i)
            (*e->arguments)[i]->accept(this);

        e->e1->accept(this);
        if (e->e1->op == TOKvar)
        {
            FuncDeclaration *fd = ((VarExp *)e->e1)->var->isFuncDeclaration();
            if (fd->semanticRun == PASSsemantic3)
            {
                fd->error("circular dependency. Functions cannot be interpreted while being compiled");
                // TODO: use StoppableVisitor
                failure = true;
                return;
            }
            if (!fd->functionSemantic3() || fd->semanticRun < PASSsemantic3done)
            {
                // TODO: use StoppableVisitor
                failure = true;
                return;
            }

            assert(fd && fd->semanticRun >= PASSsemantic3done);
            // TODO: cache compile result, global reference (hash)
            ByteCode *bc = *(ByteCode **)dmd_aaGet(&funcs, fd) = new ByteCode;
            compile(fd->fbody, bc);
            write8(OPcall);
            writez((size_t)fd);
        }
        else
        {
            printf("CallExp no yet implemented %s\n", e->toChars());
        }
    }

    void visit(PtrExp *e)
    {
        write8(OPind);
        write32(0); // TODO: determine variable index
    }

    void visit(NewExp *e)
    {
        write8(OPnew);
    }

    void visit(CondExp *e)
    {
        e->econd->accept(this);
        binOp(e, OPcond);
    }

    void visit(IndexExp *e)
    {
        // TODO:
        binOp(e, OPunde);
    }

    void visit(ArrayLengthExp *e)
    {
        // TODO:
        assert(0);
    }

    void visit(FuncExp *e)
    {
        // TODO:
        assert(0);
    }

    void visit(DeclarationExp *e)
    {
        if (VarDeclaration *vd = e->declaration->isVarDeclaration())
            *(size_t *)dmd_aaGet(&vars, vd) = dmd_aaLen(vars);
        else
            e->error("%s", e->toChars());
    }

    void visit(NegExp *e)
    {
        if (e->e1->type->toBasetype()->isintegral())
            unaOp(e, OPneg_i);
        else if (e->e1->type->toBasetype()->isreal())
            unaOp(e, OPneg_r);
        else
            assert(0);
    }
    void visit(NotExp *e) { unaOp(e, OPnot); }
    void visit(ComExp *e) { unaOp(e, OPcom); }

    void visit(AddExp *e)
    {
        if (e->e1->type->toBasetype()->isintegral())
            binOp(e, OPadd_i);
        else if (e->e1->type->toBasetype()->isreal())
            binOp(e, OPadd_r);
        else
            assert(0);
    }

    void visit(AndAndExp *e)
    {
        e->e1->accept(this);
        write8(OPnot);
        write8(OPcjmp);
        const size_t fixup = bc->data.dim;
        write32(0);

        e->e2->accept(this);
        // TODO: write32
        bc->data[fixup] = bc->data.dim - fixup;
    }

    void visit(AndExp *e) { binOp(e, OPand); }
    void visit(CmpExp *e)
    {
        assert(e->e1->type->toBasetype()->ty == e->e2->type->toBasetype()->ty);
        OP op;
        switch (e->op)
        {
        case TOKlt: op = OPlt_i; break;
        case TOKle: op = OPle_i; break;
        case TOKgt: op = OPgt_i; break;
        case TOKge: op = OPge_i; break;
        default: assert(0);
        }

        if (e->e1->type->toBasetype()->isintegral())
            op = (OP)(op + 0);
        else if (e->e1->type->toBasetype()->isreal())
            op = (OP)(op + 1);
        else if (e->e1->type->toBasetype()->isString())
            op = (OP)(op + 2);
        else
            assert(0);
        binOp(e, op);
    }
    void visit(DivExp *e)
    {
        if (e->e1->type->toBasetype()->isintegral())
            binOp(e, OPdiv_i);
        else if (e->e1->type->toBasetype()->isreal())
            binOp(e, OPdiv_r);
        else
            assert(0);
    }

    void visit(EqualExp *e)
    {
        assert(e->e1->type->toBasetype()->ty == e->e2->type->toBasetype()->ty);
        if (e->e1->type->toBasetype()->isintegral())
            binOp(e, OPeq_i);
        else if (e->e1->type->toBasetype()->isreal())
            binOp(e, OPeq_r);
        else if (e->e1->type->toBasetype()->isString())
            binOp(e, OPeq_s);
        else
            assert(0);
    }
    void visit(MinExp *e)
    {
        assert(e->e1->type->toBasetype()->ty == e->e2->type->toBasetype()->ty);
        if (e->e1->type->toBasetype()->isintegral())
            binOp(e, OPmin_i);
        else if (e->e1->type->toBasetype()->isreal())
            binOp(e, OPmin_r);
        else
            assert(0);
    }
    void visit(OrExp *e) { binOp(e, OPor); }
    void visit(OrOrExp *e)
    {
        e->e1->accept(this);
        write8(OPcjmp);
        const size_t fixup = bc->data.dim;
        write32(0);

        e->e2->accept(this);
        // TODO: write32
        bc->data[fixup] = bc->data.dim - fixup;
    }
    void visit(ShlExp *e) { binOp(e, OPshl); }
    void visit(ShrExp *e) { binOp(e, OPshr); }
    void visit(MulExp *e)
    {
        assert(e->e1->type->toBasetype()->ty == e->e2->type->toBasetype()->ty);
        if (e->e1->type->toBasetype()->isintegral())
            binOp(e, OPmul_i);
        else if (e->e1->type->toBasetype()->isreal())
            binOp(e, OPmul_r);
        else
            assert(0);
    }

    void visit(AddAssignExp *e) { binOp(e, OPaddass); }

    static bool compile(Expression *e, ByteCode *bc)
    {
        BCCompiler compiler(bc);
        e->accept(&compiler);
        return compiler.failure;
    }

    static bool compile(Statement *s, ByteCode *bc)
    {
        BCCompiler compiler(bc);
        s->accept(&compiler);
        return compiler.failure;
    }

private:
    void unaOp(UnaExp *e, OP op)
    {
        e->e1->accept(this);
        write8(op);
    }

    void binOp(BinExp *e, OP op)
    {
        e->e1->accept(this);
        e->e2->accept(this);

        write8(op);
    }

    void write8(uint8_t v)
    {
        bc->data.push(v);
    }

    void write32(int32_t v)
    {
        bc->data.push(v >> 0 & 0xFF);
        bc->data.push(v >> 8 & 0xFF);
        bc->data.push(v >> 16 & 0xFF);
        bc->data.push(v >> 24 & 0xFF);
    }

    void writez(size_t v)
    {
        if (sizeof(v) == 4)
            return write32(v);
        assert(sizeof(v) == 8);
        write32(v);
        write32(v >> 32);
    }

    void writeULEB(size_t v)
    {
        do
        {
            unsigned char b = v & 0x7F;
            write8((v >>= 7) ? b|0x80 : b);
        } while (v);
    }

    size_t pushConst(Value v)
    {
        bc->constants.push(v);
        return bc->constants.dim - 1;
    }

    AA *vars;
    ByteCode *bc;
    bool failure;
    static AA *funcs;
};

AA *BCCompiler::funcs;

size_t readULEB(unsigned char *p, size_t *pidx)
{
    size_t res = 0;
    while (p[*pidx] & 0x80)
    {
        res += p[(*pidx)++] & 0x7F;
        res <<= 7;
    }
    return res + p[(*pidx)++];
}

int32_t read32(unsigned char *p)
{
    return p[0] | p[1] << 8 | p[2] << 16 | p[3] << 24;
}

Value interpret(ByteCode &bc)
{
    size_t sp = 0;
    Value val[32];

    puts("interpret");
    for (size_t idx = 0; idx < bc.data.dim; ++idx)
        printf("0x%x, ", bc.data[idx]);
    puts("");

    for (size_t idx = 0; idx < bc.data.dim; )
    {
        switch (bc.data[idx++])
        {
        case OPload:
            val[sp++] = bc.constants[readULEB(&bc.data[0], &idx)];
            break;

        case OPadd_i:
            val[sp - 2].int_ = val[sp - 2].int_ + val[sp - 1].int_;
            --sp;
            break;

        case OPadd_r:
            val[sp - 2].real_ = val[sp - 2].real_ + val[sp - 1].real_;
            --sp;
            break;

        case OPdiv_i:
            val[sp - 2].int_ = val[sp - 2].int_ / val[sp - 1].int_;
            --sp;
            break;

        case OPdiv_r:
            val[sp - 2].real_ = val[sp - 2].real_ / val[sp - 1].real_;
            --sp;
            break;

        case OPmul_i:
            val[sp - 2].int_ = val[sp - 2].int_ * val[sp - 1].int_;
            --sp;
            break;

        case OPmul_r:
            val[sp - 2].real_ = val[sp - 2].real_ * val[sp - 1].real_;
            --sp;
            break;

        case OPcast:
            assert(0);
            break;

        case OPlt_i:
            val[sp - 2].int_ = val[sp - 2].int_ < val[sp - 1].int_;
            --sp;
            break;

        case OPlt_r:
            val[sp - 2].real_ = val[sp - 2].real_ < val[sp - 1].real_;
            --sp;
            break;

        case OPgt_i:
            val[sp - 2].int_ = val[sp - 2].int_ > val[sp - 1].int_;
            --sp;
            break;

        case OPgt_r:
            val[sp - 2].real_ = val[sp - 2].real_ > val[sp - 1].real_;
            --sp;
            break;

        case OPge_i:
            val[sp - 2].int_ = val[sp - 2].int_ >= val[sp - 1].int_;
            --sp;
            break;

        case OPge_r:
            val[sp - 2].real_ = val[sp - 2].real_ >= val[sp - 1].real_;
            --sp;
            break;

        case OPeq_i:
            val[sp - 2].int_ = val[sp - 2].int_ == val[sp - 1].int_;
            --sp;
            break;

        case OPeq_r:
            val[sp - 2].int_ = val[sp - 2].real_ == val[sp - 1].real_;
            --sp;
            break;

        case OPeq_s:
            val[sp - 2].int_ = val[sp - 2].str_.nbytes == val[sp - 1].str_.nbytes &&
                memcmp(val[sp - 2].str_.data, val[sp - 1].str_.data, val[sp - 1].str_.nbytes) == 0;
            --sp;
            break;

        case OPmin_i:
            val[sp - 2].int_ = val[sp - 2].int_ - val[sp - 1].int_;
            --sp;
            break;

        case OPmin_r:
            val[sp - 2].real_ = val[sp - 2].real_ - val[sp - 1].real_;
            --sp;
            break;

        case OPneg_i:
            val[sp - 1].int_ = -val[sp - 1].int_;
            break;

        case OPneg_r:
            val[sp - 1].real_ = -val[sp - 1].real_;
            break;

        case OPvar:
            assert(0);

        case OPnot:
            val[sp - 1].int_ = !val[sp - 1].int_;
            break;

        case OPcjmp:
            if (val[--sp].int_)
                idx += read32(&bc.data[0]);
            else
                idx += 4;
            break;

        case OPunde:
        default:
            fprintf(stderr, "unhandled op %zu %d\n", idx, bc.data[idx - 1]);
            assert(0);
        }
    }
    assert(sp == 1);
    return val[--sp];
}

bool needsInterpret(Expression *e)
{
    class NeedsInterpret : public Visitor
    {
    public:
        void visit(Expression *e) { result = true; }
        void visit(IntegerExp *e) { result = false; }
        void visit(RealExp *e) { result = false; }
        void visit(StringExp *e) { result = false; }
        bool result;
    };
    NeedsInterpret v;
    e->accept(&v);
    return v.result;
}

// dummy references to workaround link issue
int (ClassReferenceExp::*dummy1)(VarDeclaration *) = &ClassReferenceExp::findFieldIndexByName;
ClassDeclaration *(ClassReferenceExp::*dummy2)() = &ClassReferenceExp::originalClass;

} // End of namespace

using namespace interpreter;

Expression *ctfeInterpret(Expression *e)
{
    if (e->op == TOKerror)
        return e;
    //assert(e->type->ty != Terror);    // FIXME
    if (e->type->ty == Terror)
        return new ErrorExp();

    printf("ctfeInterpret %s\n", e->toChars());
    if (!needsInterpret(e))
        return e;

    unsigned olderrors = global.errors;
    ByteCode bc;
    if (BCCompiler::compile(e, &bc))
    {
        assert(global.errors != olderrors);
        e = EXP_CANT_INTERPRET;
    }
    else
    {
        interpreter::Value v = interpret(bc);
        if (e->type->toBasetype()->isintegral() ||
            e->type->toBasetype()->ty == Tpointer) // integer painted to pointer, TODO: check
            e = new IntegerExp(e->loc, v.int_, e->type);
        else if (e->type->toBasetype()->isreal())
            e = new RealExp(e->loc, v.real_, e->type);
        //    else if (e->type->toBasetype()->isString())
        //        return new StringExp(v.str_);
        else
            assert(0);
    }
    printf("e %s\n", e->toChars());
    return e;
}

Expression *ctfeInterpretForPragmaMsg(Expression *e)
{
    return EXP_CANT_INTERPRET;
}

void printCtfePerformanceStats()
{
}

Expression *getValue(VarDeclaration *vd)
{
    return EXP_CANT_INTERPRET;
}

int CtfeStatus::numArrayAllocs;
