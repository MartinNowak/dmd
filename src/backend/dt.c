// Copyright (C) 1984-1998 by Symantec
// Copyright (C) 2000-2015 by Digital Mars
// All Rights Reserved
// http://www.digitalmars.com
// Written by Walter Bright
/*
 * This source file is made available for personal use
 * only. The license is in backendlicense.txt
 * For any other uses, please contact Digital Mars.
 */

#if !SPP

#include        <stdio.h>
#include        <string.h>
#include        <stdlib.h>
#include        <time.h>
#include        "cc.h"
#include        "oper.h"
#include        "global.h"
#include        "el.h"
#include        "type.h"
#include        "dt.h"

static char __file__[] = __FILE__;      /* for tassert.h                */
#include        "tassert.h"

void dt_ary::reset()
{
    for (size_t i = 0; i < length; ++i)
    {
        if (data[i].dt == DT_abytes || data[i].dt == DT_nbytes)
            mem_free(data[i].DTpbytes);
    }
    if (data)
        mem_free(data);
    length = 0;
    data = NULL;
}

/**********************
 * Construct a DT_azeros record, and return it.
 * Increment dsout.
 */

void dtnzeros(dt_ary& ary, unsigned size)
{
    //printf("dtnzeros(x%x)\n",size);
    assert((long) size >= 0);
    if (!size)
        return;
    dt_t dt;
    dt.dt = DT_azeros;
    dt.DTazeros = size;
#if SCPP
    dsout += size;
#endif
    ary.push(dt);
}

/**********************
 * Construct a DTsymsize record.
 */

void dtsymsize(symbol *s)
{
    assert(!s->Sdt.length);
    symbol_debug(s);
    dt_t dt;
    dt.dt = DT_symsize;
    s->Sdt.push(dt);
}

/**********************
 * Construct a DTnbytes record, and return it.
 */

void dtnbytes(dt_ary& ary, unsigned size, const char *ptr)
{
    if (!size)
        return;

    dt_t dt;
    if (size < DTibytesMax)
    {
        dt->dt = DT_ibytes;
        dt->DTn = size;
        memcpy(dt->DTdata, ptr, size);
    }
    else
    {
        dt->dt = DT_nbytes;
        dt->DTnbytes = size;
        dt->DTpbytes = (char *) MEM_PH_MALLOC(size);
        memcpy(dt->DTpbytes, ptr, size);
    }
    ary.push(dt);
}

/**********************
 * Construct a DTabytes record, and return it.
 */

void dtabytes(dt_ary& ary, unsigned offset, unsigned size, const char *ptr)
{
    return dtabytes(ary, TYnptr, offset, size, ptr);
}

void dtabytes(dt_ary& ary, tym_t ty, unsigned offset, unsigned size, const char *ptr)
{
    dt_t dt;
    dt.dt = DT_abytes;
    dt.DTnbytes = size;
    dt.DTpbytes = (char *) MEM_PH_MALLOC(size);
    dt.Dty = ty;
    dt.DTabytes = offset;
    memcpy(dt.DTpbytes, ptr, size);
    ary.push(dt);
}

/**********************
 * Construct a DTibytes record, and return it.
 */

void dtdword(dt_ary& ary, int value)
{
    dt_t dt;
    dt.dt = DT_ibytes;
    dt.DTn = 4;
    *(int*)dt.DTdata = value;
    ary.push(dt);
}

void dtsize_t(dt_ary& ary, unsigned long long value)
{
    dt_t dt;
    dt.dt = DT_ibytes;
    dt.DTn = NPTRSIZE;
    *(unsigned long long)dt->DTdata = value;
    ary.push(dt);
}

/**********************
 * Construct a DTcoff record, and return it.
 */

void dtcoff(dt_ary& ary, unsigned offset)
{
    dt_t dt;
    dt.dt = DT_coff;
#if TARGET_SEGMENTED
    dt.Dty = TYcptr;
#else
    dt.Dty = TYnptr;
#endif
    dt.DToffset = offset;
    ary.push(dt);
}

/**********************
 * Construct a DTxoff record, and return it.
 */

void dtxoff(dt_ary& ary, symbol *s, unsigned offset)
{
    return dtxoff(ary, s, offset, TYnptr);
}

void dtxoff(dt_ary& ary, symbol *s, unsigned offset, tym_t ty)
{
    symbol_debug(s);
    dt_t dt;
    dt->dt = DT_xoff;
    dt->DTsym = s;
    dt->DToffset = offset;
    dt->Dty = ty;
    ary.push(dt);
}

/*********************************
 */
void dtpatchoffset(dt_t *dt, unsigned offset)
{
    dt->DToffset = offset;
}

/*************************************
 * Create a reference to another dt.
 */
void dtdtoff(dt_ary& ary, dt_ary& data, unsigned offset)
{
    type *t = type_alloc(TYint);
    t->Tcount++;
    Symbol *s = symbol_calloc("internal");
    s->Sclass = SCstatic;
    s->Sfl = FLextern;
    s->Sflags |= SFLnodebug;
    s->Stype = t;
    s->Sdt.swap(data);
    slist_add(s);
    outdata(s);
    return dtxoff(ary, s, offset);
}

/**************************************
 * Repeat a list of dt_t's count times.
 */
void dtrepeat(dt_ary& ary, dt_ary& data, size_t count)
{
    if (!count)
        return;

    if (dtallzeros(dt))
        dtnzeros(pdtend, dt_size(data) * count);
    else if (dtpointers(data))
    {
        const size_t base = ary.length;
        ary.setLength(base + count * data.length);

        for (size_t i = 0; i < count; ++i)
            memcpy(&ary[j + i * data.length], &data[0], data.length);
        for (size_t i = 0; i < data.length; ++i)
        {
            switch (data[i].dt)
            {
            case DT_abytes:
            case DT_nbytes:
                for (size_t j = 0; j < count; ++j)
                {
                    const size_t idx = base + i + j * data.length;
                    ary[idx].DTpbytes = (char *) MEM_PH_MALLOC(data[i].DTnbytes);
                    memcpy(ary[idx].DTpbytes, data[i].DTpbytes, data[i].DTnbytes);
                    break;
                }
            }
        }
    }
    else
    {
        const size_t size = dt_size(data);
        assert(size);
        char *p = (char *)MEM_PH_MALLOC(size * count);
        size_t offset = 0;

        for (size_t i = 0; i < data.length; ++i)
        {
            dt_t *dt = &data[i];
            switch (dt->dt)
            {
                case DT_nbytes:
                    memcpy(p + offset, dt->DTpbytes, dt->DTnbytes);
                    offset += dt->DTnbytes;
                    break;
                case DT_ibytes:
                    memcpy(p + offset, dt->DTdata, dt->DTn);
                    offset += dt->DTn;
                    break;
                case DT_symsize:
                case DT_azeros:
                    memset(p + offset, 0, dt->DTazeros);
                    offset += dt->DTazeros;
                    break;
                default:
#ifdef DEBUG
                    dbg_printf("dt = %p, dt = %d\n",dt,dt->dt);
#endif
                    assert(0);
            }
        }
        assert(offset == size);

        while (count--)
        {
            memcpy(p + offset, p, size);
            offset += size;
        }

        dt_t dt;
        dt.dt = DT_nbytes;
        dt.DTnbytes = size * count;
        dt.DTpbytes = p;
        ary.push(dt);
    }
}

/**************************
 * 'Optimize' a list of dt_t's.
 * (Try to collapse it into one DT_azeros object.)
 */

void dt_optimize(dt_ary& ary)
{
    size_t i = 0;
    for (size_t j = 1; j < ary.length; ++j)
    {
        if (ary[i].dt == DT_azeros && ary[j].dt == DT_azeros)
            ary[i].DTazeros += ary[j].DTazeros;
        else if (++i != j)
            ary[i] = ary[j];
    }
    ary.setLength(i + 1);
}

/**************************
 * Make a common block for s.
 */

void init_common(symbol *s)
{
    //printf("init_common('%s')\n", s->Sident);
    dtnzeros(&s->Sdt,type_size(s->Stype));
    if (s->Sdt)
        s->Sdt->dt = DT_common;
}

/**********************************
 * Compute size of a dt
 */

unsigned dt_size(const dt_ary& ary)
{
    unsigned datasize = 0;
    for (size_t i = 0; i < ary.length; ++i)
    {
        dt_t *dt = &ary[i];
        switch (dt->dt)
        {
            case DT_abytes:
                datasize += size(dt->Dty);
                break;
            case DT_ibytes:
                datasize += dt->DTn;
                break;
            case DT_nbytes:
                datasize += dt->DTnbytes;
                break;
            case DT_symsize:
            case DT_azeros:
                datasize += dt->DTazeros;
                break;
            case DT_common:
                break;
            case DT_xoff:
            case DT_coff:
                datasize += size(dt->Dty);
                break;
            default:
#ifdef DEBUG
                dbg_printf("dt = %p, dt = %d\n",dt,dt->dt);
#endif
                assert(0);
        }
    }
    return datasize;
}

/************************************
 * Return true if dt is all zeros.
 */

bool dtallzeros(const dt_ary& ary)
{
    return ary.length == 1 && ary[0].dt == DT_azeros;
}

/************************************
 * Return true if dt contains pointers (requires relocations).
 */

bool dtpointers(const dt_ary& ary)
{
    for (size_t i = 0; i < ary.length; ++i)
    {
        dt_t *dt = &ary[i];
        switch (dt->dt)
        {
        case DT_abytes:
        case DT_xoff:
        case DT_coff:
            return true;
        }
    }
    return false;
}

/***********************************
 * Turn DT_azeros into DTcommon
 */

void dt2common(dt_ary& ary)
{
    assert(dtallzeros(dt));
    ary[0].dt = DT_common;
}


#endif /* !SPP */
