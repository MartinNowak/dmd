
//#pragma once
#ifndef DT_H
#define DT_H 1

struct dt_t;
struct dt_ary;
typedef struct Symbol symbol;
typedef unsigned tym_t; // data type big enough for type masks

void dt2common(dt_ary &ary);
void init_common(symbol *s);
void dt_optimize(dt_ary &ary);
bool dtpointers(const dt_ary &ary);
unsigned dt_size(const dt_ary &ary);
bool dtallzeros(const dt_ary &ary);
void dtrepeat(dt_ary &ary, dt_ary &data, size_t count);
void dtdtoff(dt_ary &ary, dt_ary &data, unsigned offset);
void dtpatchoffset(dt_t *dt, unsigned offset);
void dtxoff(dt_ary &ary, symbol *s, unsigned offset);
void dtxoff(dt_ary &ary, symbol *s, unsigned offset, tym_t ty);
void dtcoff(dt_ary &ary, unsigned offset);
void dtsize_t(dt_ary &ary, unsigned long long value);
void dtdword(dt_ary &ary, int value);
void dtabytes(dt_ary &ary, unsigned offset, unsigned size, const char *ptr);
void dtabytes(dt_ary &ary, tym_t ty, unsigned offset, unsigned size,
              const char *ptr);
void dtnbytes(dt_ary &ary, unsigned size, const char *ptr);
void dtsymsize(symbol *s);
void dtnzeros(dt_ary &ary, unsigned size);

#endif /* DT_H */
