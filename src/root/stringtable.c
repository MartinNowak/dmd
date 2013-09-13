
// Copyright (c) 1999-2013 by Digital Mars
// All Rights Reserved
// written by Walter Bright
// http://www.digitalmars.com
// License for redistribution is by either the Artistic License
// in artistic.txt, or the GNU General Public License in gnu.txt.
// See the included readme.txt for details.


#include <stdio.h>
#include <stdint.h>                     // uint{8|16|32}_t
#include <string.h>                     // memcpy()
#include <stdlib.h>

#include "root.h"
#include "rmem.h"                       // mem
#include "stringtable.h"

// TODO: Merge with root.String
#if defined __i386__ || defined __x86_64__ || defined  _M_IX86 || defined _M_X64
/*
 * This is the FNV-1a hashing algorithm, described here:
 *   http://www.isthe.com/chongo/tech/comp/fnv/#FNV-1a
 * It has been placed in the public domain.
 */
hash_t calcHash(const char *str, size_t len)
{
    static const hash_t fnv_prime = sizeof(hash_t) == 4 ? 16777619UL : 1099511628211UL;
    static const hash_t offset_basis = sizeof(hash_t) == 4 ? 2166136261UL : 14695981039346656037UL;

    const uint8_t *p = (const uint8_t *)str;
    hash_t hash = offset_basis;
    for (size_t i = 0; i < len; ++i)
    {
        hash ^= p[i];
        hash *= fnv_prime;
    }
    return hash;
}
#else
/*
 * This is the One-at-a-Time hash algorithm, described here:
 *   http://www.burtleburtle.net/bob/hash/doobs.html
 * It has been placed in the public domain.
 *
 * It's faster on architectures where multiplication is
 * expensive.
 */
uint32_t calcHash(const char *str, size_t len)
{
    uint32_t hash = 0;
    const uint8_t *p = (const uint8_t *)str;
    for (size_t i = 0; i < len; ++i)
    {
        hash += p[i];
        hash += (hash << 10);
        hash ^= (hash >> 6);
    }
    hash += (hash << 3);
    hash ^= (hash >> 11);
    hash += (hash << 15);
    return hash;
}
#endif

#define PRINT_STATS 0

#if PRINT_STATS
static void printStringTableStats(StringEntry **buckets, size_t tabledim);
#endif

void StringValue::ctor(const char *p, size_t length)
{
    this->length = length;
    this->lstring[length] = 0;
    memcpy(this->lstring, p, length * sizeof(char));
}

void StringTable::_init(size_t size)
{
    assert(size != 0 && !(size & size - 1)); // power of 2
    table = (void **)mem.calloc(size, sizeof(void *));
    count = 0;
    tabledim = size;
}

StringTable::~StringTable()
{
#if PRINT_STATS
    printf("~StringTable() count: %u\n", (unsigned)count);
    printStringTableStats((StringEntry **)table, tabledim);
#endif
    // Zero out dangling pointers to help garbage collector.
    // Should zero out StringEntry's too.
    ::memset(table, 0, tabledim * sizeof(table[0]));

    mem.free(table);
    table = NULL;
}

struct StringEntry
{
    hash_t hash;
    StringEntry *next;

    StringValue value;

    static StringEntry *alloc(const char *s, size_t len);
};

StringEntry *StringEntry::alloc(const char *s, size_t len)
{
    StringEntry *se;

    se = (StringEntry *) mem.calloc(1,sizeof(StringEntry) + len + 1);
    se->value.ctor(s, len);
    se->hash = calcHash(s,len);
    return se;
}

void **StringTable::search(const char *s, size_t len)
{
    //printf("StringTable::search(%p,%d)\n",s,len);
    const hash_t hash = calcHash(s,len);
    const unsigned idx = hash & tabledim - 1;
    StringEntry **se = (StringEntry **)&table[idx];
    //printf("\thash = %d, u = %d\n",hash,u);
    while (*se)
    {
        if ((*se)->hash == hash && (*se)->value.len() == len &&
                ::memcmp(s, (*se)->value.toDchars(), len) == 0)
            break;
        se = &(*se)->next;
    }
    //printf("\treturn %p, %p\n",se, (*se));
    return (void **)se;
}

StringValue *StringTable::lookup(const char *s, size_t len)
{
    StringEntry *se = *(StringEntry **)search(s,len);
    if (se)
        return &se->value;
    else
        return NULL;
}

StringValue *StringTable::update(const char *s, size_t len)
{
    StringEntry **pse = (StringEntry **)search(s,len);
    StringEntry *se = *pse;
    if (!se)                    // not in table: so create new entry
    {
        se = StringEntry::alloc(s, len);
        *pse = se;
        if (++count > 2 * tabledim) grow();
    }
    return &se->value;
}

StringValue *StringTable::insert(const char *s, size_t len)
{
    StringEntry **pse = (StringEntry **)search(s,len);
    StringEntry *se = *pse;
    if (se)
        return NULL;            // error: already in table
    else
    {
        se = StringEntry::alloc(s, len);
        *pse = se;
        if (++count > 2 * tabledim) grow();
    }
    return &se->value;
}

void StringTable::grow()
{
    const size_t odim = tabledim;
    tabledim *= 4;
    table = (void**)mem.realloc(table, tabledim * sizeof(void*));
    memset(table + odim, 0, 3 * odim * sizeof(void*));

    const size_t mask = tabledim - 1;
    for (size_t idx = 0; idx < odim; ++idx)
    {
        StringEntry **pse = (StringEntry **)&table[idx];
        while (*pse)
        {
            const size_t nidx = (*pse)->hash & mask;
            if (nidx == idx)
            {
                pse = &(*pse)->next;
            }
            else
            {
                StringEntry *se = *pse;
                *pse = se->next;
                se->next = (StringEntry *)table[nidx];
                *(StringEntry **)&table[nidx] = se;
            }
        }
    }
}

#if PRINT_STATS
#include <math.h> // sqrt

static size_t nentries(StringEntry *se)
{
    size_t n = 0;
    for (; se; se = se->next)
        ++n;
    return n;
}

static void printStringTableStats(StringEntry **table, size_t tabledim)
{
    size_t hist[16] = {0};
    size_t sum = 0;
    float sqsum = 0;
    for (size_t i = 0; i < tabledim; ++i)
    {
        const size_t n = nentries((StringEntry *)table[i]);
        ++hist[n < 16 ? n : 15];
        sum += n;
        sqsum += (float)n * (float)n;
    }
    const float mean = (float)sum / tabledim;
    const float var = sqsum / tabledim - mean * mean;
    printf("==== stats StringTable ====\n", (unsigned long long)tabledim);
    printf("tabledim %u nentries %u,  mean %f, dev %f\n", (unsigned)tabledim, (unsigned)sum, mean, sqrt(var));
    const float rel = 100.0f / sum;
    printf("==== histogram ====\n");
    printf("%10s | %10s | %15s | %15s\n", "length", "number", "% of entries", "accum % of entries");
    size_t acc = 0;
    for (size_t i = 0; i < 16; ++i)
    {
        acc += hist[i] * i;
        printf("%10u | %10llu | %15f | %15f\n", (unsigned)i, (unsigned long long)hist[i], hist[i] * i * rel, acc * rel);
    }
    printf("~~~~ hist StringTable<%llu> ~~~~\n", (unsigned long long)tabledim);
}
#endif
