
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
hash_t calcHash(const char *str, size_t len)
{
    hash_t hash = 0;

    while (1)
    {
        switch (len)
        {
            case 0:
                return hash;

            case 1:
                hash *= 37;
                hash += *(const uint8_t *)str;
                return hash;

            case 2:
                hash *= 37;
                hash += *(const uint16_t *)str;
                return hash;

            case 3:
                hash *= 37;
                hash += (*(const uint16_t *)str << 8) +
                        ((const uint8_t *)str)[2];
                return hash;

            default:
                hash *= 37;
                hash += *(const uint32_t *)str;
                str += 4;
                len -= 4;
                break;
        }
    }
}

#define PRINT_STATS 1

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
    table = (void **)mem.calloc(size, sizeof(void *));
    tabledim = size;
    count = 0;
}

StringTable::~StringTable()
{
#if PRINT_STATS
    printStringTableStats((StringEntry **)table, tabledim);
#endif
    // Zero out dangling pointers to help garbage collector.
    // Should zero out StringEntry's too.
    for (size_t i = 0; i < count; i++)
        table[i] = NULL;

    mem.free(table);
    table = NULL;
}

struct StringEntry
{
    StringEntry *left;
    StringEntry *right;
    hash_t hash;

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
    hash_t hash;
    unsigned u;
    int cmp;
    StringEntry **se;

    //printf("StringTable::search(%p,%d)\n",s,len);
    hash = calcHash(s,len);
    u = hash % tabledim;
    se = (StringEntry **)&table[u];
    //printf("\thash = %d, u = %d\n",hash,u);
    while (*se)
    {
        cmp = (*se)->hash - hash;
        if (cmp == 0)
        {
            cmp = (*se)->value.len() - len;
            if (cmp == 0)
            {
                cmp = ::memcmp(s,(*se)->value.toDchars(),len);
                if (cmp == 0)
                    break;
            }
        }
        if (cmp < 0)
            se = &(*se)->left;
        else
            se = &(*se)->right;
    }
    //printf("\treturn %p, %p\n",se, (*se));
    return (void **)se;
}

StringValue *StringTable::lookup(const char *s, size_t len)
{   StringEntry *se;

    se = *(StringEntry **)search(s,len);
    if (se)
        return &se->value;
    else
        return NULL;
}

StringValue *StringTable::update(const char *s, size_t len)
{   StringEntry **pse;
    StringEntry *se;

    pse = (StringEntry **)search(s,len);
    se = *pse;
    if (!se)                    // not in table: so create new entry
    {
        se = StringEntry::alloc(s, len);
        *pse = se;
    }
    return &se->value;
}

StringValue *StringTable::insert(const char *s, size_t len)
{   StringEntry **pse;
    StringEntry *se;

    pse = (StringEntry **)search(s,len);
    se = *pse;
    if (se)
        return NULL;            // error: already in table
    else
    {
        se = StringEntry::alloc(s, len);
        *pse = se;
    }
    return &se->value;
}

#if PRINT_STATS
#include <math.h> // sqrt

static size_t nentries(StringEntry *se)
{
    return se ? 1 + nentries(se->left) + nentries(se->right) : 0;
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
    printf("tabledim %u nentries %u, mean %f, dev %f\n", (unsigned)tabledim, (unsigned)sum, mean, sqrt(var));
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
