#ifndef AAV_H
#define AAV_H

typedef void* Value;
typedef void* Key;

struct AA;
struct Array;

size_t _aaLen(AA* aa);
Value* _aaGet(AA** aa, Key key);
Value _aaGetRvalue(AA* aa, Key key);
void _aaRehash(AA** paa);
Array* _aaKeys(AA* aa);
Array* _aaValues(AA* aa);

#endif
