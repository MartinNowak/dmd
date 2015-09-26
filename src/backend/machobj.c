// Compiler implementation of the D programming language
// Copyright (c) 2009-2011 by Digital Mars
// All Rights Reserved
// written by Walter Bright
// http://www.digitalmars.com
// Distributed under the Boost Software License, Version 1.0.
// http://www.boost.org/LICENSE_1_0.txt
// https://github.com/D-Programming-Language/dmd/blob/master/src/backend/machobj.c


#if SCPP || MARS
#include        <stdio.h>
#include        <string.h>
#include        <stdlib.h>
#include        <sys/types.h>
#include        <sys/stat.h>
#include        <fcntl.h>
#include        <ctype.h>

#if _WIN32 || __linux__
#include        <malloc.h>
#endif

#if __linux__ || __APPLE__ || __FreeBSD__ || __OpenBSD__ || __sun
#include        <signal.h>
#include        <unistd.h>
#endif

#include        "cc.h"
#include        "global.h"
#include        "code.h"
#include        "type.h"
#include        "mach.h"
#include        "outbuf.h"
#include        "filespec.h"
#include        "cv4.h"
#include        "cgcv.h"
#include        "dt.h"

#include        "aa.h"
#include        "tinfo.h"

#if MACHOBJ

#if MARS
#include        "mars.h"
#endif

#include        "mach.h"
#include        "dwarf.h"

// for x86_64
#define X86_64_RELOC_UNSIGNED           0
#define X86_64_RELOC_SIGNED             1
#define X86_64_RELOC_BRANCH             2
#define X86_64_RELOC_GOT_LOAD           3
#define X86_64_RELOC_GOT                4
#define X86_64_RELOC_SUBTRACTOR         5
#define X86_64_RELOC_SIGNED_1           6
#define X86_64_RELOC_SIGNED_2           7
#define X86_64_RELOC_SIGNED_4           8

static Outbuffer *fobjbuf;

static char __file__[] = __FILE__;      // for tassert.h
#include        "tassert.h"

#define DEST_LEN (IDMAX + IDOHD + 1)
char *obj_mangle2(Symbol *s,char *dest);

#if MARS
// C++ name mangling is handled by front end
#define cpp_mangle(s) ((s)->Sident)
#endif


/******************************************
 */

symbol *GOTsym; // global offset table reference

symbol *Obj::getGOTsym()
{
    if (!GOTsym)
    {
        GOTsym = symbol_name("_GLOBAL_OFFSET_TABLE_",SCglobal,tspvoid);
    }
    return GOTsym;
}

static void objfile_write(FILE *fd, void *buffer, unsigned len);

STATIC char * objmodtoseg (const char *modname);
STATIC void objfixupp (struct FIXUP *);
STATIC void ledata_new (int seg,targ_size_t offset);

static long elf_align(targ_size_t size, long offset);
static void writeRelocations(int seg, const IDXSYM *sym_map, Outbuffer *buf);

// The object file is built is several separate pieces


// String Table  - String table for all other names
static Outbuffer *symtab_strings;

// Section Headers
Outbuffer  *SECbuf;             // Buffer to build section table in
#define SecHdrTab   ((struct section *)SECbuf->buf)
#define SecHdrTab64 ((struct section_64 *)SECbuf->buf)

// The relocation for text and data seems to get lost.
// Try matching the order gcc output them
// This means defining the sections and then removing them if they are
// not used.
static int section_cnt;         // Number of sections in table
#define SEC_TAB_INIT 16         // Initial number of sections in buffer
#define SEC_TAB_INC  4          // Number of sections to increment buffer by

#define SYM_TAB_INIT 100        // Initial number of symbol entries in buffer
#define SYM_TAB_INC  50         // Number of symbols to increment buffer by

/* Three symbol tables, because the different types of symbols
 * are grouped into 3 different types (and a 4th for comdef's).
 */

static Outbuffer *symbol_table;

static Outbuffer *indirectsymbuf1;      // indirect symbol table of Symbol*'s
static int jumpTableSeg;                // segment index for __jump_table

static Outbuffer *indirectsymbuf2;      // indirect symbol table of Symbol*'s
static int pointersSeg;                 // segment index for __pointers

/* If an Obj::external_def() happens, set this to the string index,
 * to be added last to the symbol table.
 * Obviously, there can be only one.
 */
static IDXSTR extdef;

#if 0
#define STI_FILE 1              // Where file symbol table entry is
#define STI_TEXT 2
#define STI_DATA 3
#define STI_BSS  4
#define STI_GCC  5              // Where "gcc2_compiled" symbol is */
#define STI_RODAT 6             // Symbol for readonly data
#define STI_COM  8
#endif

// Each compiler segment is a section
// Predefined compiler segments CODE,DATA,CDATA,UDATA map to indexes
//      into SegData[]
//      New compiler segments are added to end.

/******************************
 * Returns !=0 if this segment is a code segment.
 */

int seg_data::isCode()
{
    // The codegen assumes that code->data references are indirect,
    // but when CDATA is treated as code reftoident will emit a direct
    // relocation.
    if (this == SegData[CDATA])
        return false;

    if (I64)
    {
        //printf("SDshtidx = %d, x%x\n", SDshtidx, SecHdrTab64[SDshtidx].flags);
        return strcmp(SecHdrTab64[SDshtidx].segname, "__TEXT") == 0;
    }
    else
    {
        //printf("SDshtidx = %d, x%x\n", SDshtidx, SecHdrTab[SDshtidx].flags);
        return strcmp(SecHdrTab[SDshtidx].segname, "__TEXT") == 0;
    }
}


seg_data **SegData;
int seg_count;
int seg_max;
int seg_tlsseg = UNKNOWN;
int seg_tlsseg_bss = UNKNOWN;

#define MAP_SEG2SECIDX(seg) (SegData[seg]->SDshtidx)

/*******************************************************
 * Because the Mach-O relocations cannot be computed until after
 * all the segments are written out, and we need more information
 * than the Mach-O relocations provide, make our own relocation
 * type. Later, translate to Mach-O relocation structure.
 */

struct Relocation
{   // Relocations are attached to the struct seg_data they refer to
    targ_size_t offset; // location in segment to be fixed up
    symbol *funcsym;    // function in which offset lies, if any
    symbol *targsym;    // if !=NULL, then location is to be fixed up
                        // to address of this symbol
    unsigned targseg;   // if !=0, then location is to be fixed up
                        // to address of start of this segment
    unsigned char rtype;   // RELxxxx
#define RELaddr 0       // straight address
#define RELrel  1       // relative to location to be fixed up
    short val;          // 0, -1, -2, -4
};


/*******************************
 * Output a string into a string table
 * Input:
 *      strtab  =       string table for entry
 *      str     =       string to add
 *
 * Returns index into the specified string table.
 */

IDXSTR Obj::addstr(Outbuffer *strtab, const char *str)
{
    //printf("Obj::addstr(strtab = %p str = '%s')\n",strtab,str);
    IDXSTR idx = strtab->size();        // remember starting offset
    strtab->writeString(str);
    //printf("\tidx %d, new size %d\n",idx,strtab->size());
    return idx;
}

/*******************************
 * Find a string in a string table
 * Input:
 *      strtab  =       string table for entry
 *      str     =       string to find
 *
 * Returns index into the specified string table or 0.
 */

static IDXSTR elf_findstr(Outbuffer *strtab, const char *str, const char *suffix)
{
    const char *ent = (char *)strtab->buf+1;
    const char *pend = ent+strtab->size() - 1;
    const char *s = str;
    const char *sx = suffix;
    int len = strlen(str);

    if (suffix)
        len += strlen(suffix);

    while(ent < pend)
    {
        if(*ent == 0)                   // end of table entry
        {
            if(*s == 0 && !sx)          // end of string - found a match
            {
                return ent - (const char *)strtab->buf - len;
            }
            else                        // table entry too short
            {
                s = str;                // back to beginning of string
                sx = suffix;
                ent++;                  // start of next table entry
            }
        }
        else if (*s == 0 && sx && *sx == *ent)
        {                               // matched first string
            s = sx+1;                   // switch to suffix
            ent++;
            sx = NULL;
        }
        else                            // continue comparing
        {
            if (*ent == *s)
            {                           // Have a match going
                ent++;
                s++;
            }
            else                        // no match
            {
                while(*ent != 0)        // skip to end of entry
                    ent++;
                ent++;                  // start of next table entry
                s = str;                // back to beginning of string
                sx = suffix;
            }
        }
    }
    return 0;                   // never found match
}

/*******************************
 * Output a mangled string into the symbol string table
 * Input:
 *      str     =       string to add
 *
 * Returns index into the table.
 */

static IDXSTR mach_addmangled(Symbol *s)
{
    //printf("mach_addmangled(%s)\n", s->Sident);
    char dest[DEST_LEN];
    char *destr;
    const char *name;
    int len;
    IDXSTR namidx;

    namidx = symtab_strings->size();
    destr = obj_mangle2(s, dest);
    name = destr;
    if (CPP && name[0] == '_' && name[1] == '_')
    {
        if (strncmp(name,"__ct__",6) == 0)
            name += 4;
#if 0
        switch(name[2])
        {
            case 'c':
                if (strncmp(name,"__ct__",6) == 0)
                    name += 4;
                break;
            case 'd':
                if (strcmp(name,"__dl__FvP") == 0)
                    name = "__builtin_delete";
                break;
            case 'v':
                //if (strcmp(name,"__vec_delete__FvPiUIPi") == 0)
                    //name = "__builtin_vec_del";
                //else
                //if (strcmp(name,"__vn__FPUI") == 0)
                    //name = "__builtin_vec_new";
                break;
            case 'n':
                if (strcmp(name,"__nw__FPUI") == 0)
                    name = "__builtin_new";
                break;
        }
#endif
    }
    else if (tyfunc(s->ty()) && s->Sfunc && s->Sfunc->Fredirect)
        name = s->Sfunc->Fredirect;
    len = strlen(name);
    symtab_strings->reserve(len+1);
    strcpy((char *)symtab_strings->p,name);
    symtab_strings->setsize(namidx+len+1);
    if (destr != dest)                  // if we resized result
        mem_free(destr);
    //dbg_printf("\telf_addmagled symtab_strings %s namidx %d len %d size %d\n",name, namidx,len,symtab_strings->size());
    return namidx;
}

/**************************
 * Ouput read only data and generate a symbol for it.
 *
 */

symbol * Obj::sym_cdata(tym_t ty,char *p,int len)
{
    symbol *s;

#if 0
    if (I64)
    {
        alignOffset(DATA, tysize(ty));
        s = symboldata(Doffset, ty);
        SegData[DATA]->SDbuf->write(p,len);
        s->Sseg = DATA;
        s->Soffset = Doffset;   // Remember its offset into DATA section
        Doffset += len;
    }
    else
#endif
    {
        //printf("Obj::sym_cdata(ty = %x, p = %x, len = %d, CDoffset = %x)\n", ty, p, len, CDoffset);
        alignOffset(CDATA, tysize(ty));
        s = symboldata(CDoffset, ty);
        s->Sseg = CDATA;
        //Obj::pubdef(CDATA, s, CDoffset);
        Obj::bytes(CDATA, CDoffset, len, p);
    }

    s->Sfl = /*(config.flags3 & CFG3pic) ? FLgotoff :*/ FLextern;
    return s;
}

/**************************
 * Ouput read only data for data
 *
 */

int Obj::data_readonly(char *p, int len, int *pseg)
{
    int oldoff = CDoffset;
    SegData[CDATA]->SDbuf->reserve(len);
    SegData[CDATA]->SDbuf->writen(p,len);
    CDoffset += len;
    *pseg = CDATA;
    return oldoff;
}

int Obj::data_readonly(char *p, int len)
{
    int pseg;

    return Obj::data_readonly(p, len, &pseg);
}

/******************************
 * Perform initialization that applies to all .o output files.
 *      Called before any other obj_xxx routines
 */
Obj *Obj::init(Outbuffer *objbuf, const char *filename, const char *csegname)
{
    //printf("Obj::init()\n");
    MachObj *obj = new MachObj();

    cseg = CODE;
    fobjbuf = objbuf;

    seg_tlsseg = UNKNOWN;
    seg_tlsseg_bss = UNKNOWN;
    GOTsym = NULL;

    // Initialize buffers

    if (symtab_strings)
        symtab_strings->setsize(1);
    else
    {   symtab_strings = new Outbuffer(1024);
        symtab_strings->reserve(2048);
        symtab_strings->writeByte(0);
    }

    if (!symbol_table)
        symbol_table = new Outbuffer((I64 ? sizeof(nlist_64) : sizeof(nlist)) * SYM_TAB_INIT);
    symbol_table->setsize(0);

    extdef = 0; // TODO: emit external symbols

    if (indirectsymbuf1)
        indirectsymbuf1->setsize(0);
    jumpTableSeg = 0;

    if (indirectsymbuf2)
        indirectsymbuf2->setsize(0);
    pointersSeg = 0;

    // Initialize segments for CODE, DATA, UDATA and CDATA
    size_t struct_section_size = I64 ? sizeof(struct section_64) : sizeof(struct section);
    if (SECbuf)
    {
        SECbuf->setsize(struct_section_size);
    }
    else
    {
        SECbuf = new Outbuffer(SYM_TAB_INC * struct_section_size);
        SECbuf->reserve(SEC_TAB_INIT * struct_section_size);
        // Ignore the first section - section numbers start at 1
        SECbuf->writezeros(struct_section_size);
    }
    section_cnt = 1;

    seg_count = 0;
    int align = I64 ? 4 : 2;            // align to 16 bytes for floating point
    MachObj::getsegment("__text",  "__TEXT", 2, S_REGULAR | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS);
    MachObj::getsegment("__data",  "__DATA", align, S_REGULAR);     // DATA
    MachObj::getsegment("__const", "__TEXT", 2, S_REGULAR);         // CDATA
    MachObj::getsegment("__bss",   "__DATA", 4, S_ZEROFILL);        // UDATA
    MachObj::getsegment("__const", "__DATA", align, S_REGULAR);     // CDATAREL

    if (config.fulltypes)
        dwarf_initfile(filename);

    return obj;
}

/**************************
 * Initialize the start of object output for this particular .o file.
 *
 * Input:
 *      filename:       Name of source file
 *      csegname:       User specified default code segment name
 */

void Obj::initfile(const char *filename, const char *csegname, const char *modname)
{
    //dbg_printf("Obj::initfile(filename = %s, modname = %s)\n",filename,modname);
#if SCPP
    if (csegname && *csegname && strcmp(csegname,".text"))
    {   // Define new section and make it the default for cseg segment
        // NOTE: cseg is initialized to CODE
        IDXSEC newsecidx;
        Elf32_Shdr *newtextsec;
        IDXSYM newsymidx;
        assert(!I64);      // fix later
        SegData[cseg]->SDshtidx = newsecidx =
            elf_newsection(csegname,0,SHT_PROGDEF,SHF_ALLOC|SHF_EXECINSTR);
        newtextsec = &SecHdrTab[newsecidx];
        newtextsec->sh_addralign = 4;
        SegData[cseg]->SDsymidx =
            elf_addsym(0, 0, 0, STT_SECTION, STB_LOCAL, newsecidx);
    }
#endif
    if (config.fulltypes)
        dwarf_initmodule(filename, modname);
}

/************************************
 * Patch pseg/offset by adding in the vmaddr difference from
 * pseg/offset to start of seg.
 */

int32_t *patchAddr(int seg, targ_size_t offset)
{
    return(int32_t *)(fobjbuf->buf + SecHdrTab[SegData[seg]->SDshtidx].offset + offset);
}

int32_t *patchAddr64(int seg, targ_size_t offset)
{
    return(int32_t *)(fobjbuf->buf + SecHdrTab64[SegData[seg]->SDshtidx].offset + offset);
}

void patch(seg_data *pseg, targ_size_t offset, int seg, targ_size_t value)
{
    //printf("patch(offset = x%04x, seg = %d, value = x%llx)\n", (unsigned)offset, seg, value);
    if (I64)
    {
        int32_t *p = (int32_t *)(fobjbuf->buf + SecHdrTab64[pseg->SDshtidx].offset + offset);
#if 0
        printf("\taddr1 = x%llx\n\taddr2 = x%llx\n\t*p = x%llx\n\tdelta = x%llx\n",
            SecHdrTab64[pseg->SDshtidx].addr,
            SecHdrTab64[SegData[seg]->SDshtidx].addr,
            *p,
            SecHdrTab64[SegData[seg]->SDshtidx].addr -
            (SecHdrTab64[pseg->SDshtidx].addr + offset));
#endif
        *p += SecHdrTab64[SegData[seg]->SDshtidx].addr -
              (SecHdrTab64[pseg->SDshtidx].addr - value);
    }
    else
    {
        int32_t *p = (int32_t *)(fobjbuf->buf + SecHdrTab[pseg->SDshtidx].offset + offset);
#if 0
        printf("\taddr1 = x%x\n\taddr2 = x%x\n\t*p = x%x\n\tdelta = x%x\n",
            SecHdrTab[pseg->SDshtidx].addr,
            SecHdrTab[SegData[seg]->SDshtidx].addr,
            *p,
            SecHdrTab[SegData[seg]->SDshtidx].addr -
            (SecHdrTab[pseg->SDshtidx].addr + offset));
#endif
        *p += SecHdrTab[SegData[seg]->SDshtidx].addr -
              (SecHdrTab[pseg->SDshtidx].addr - value);
    }
}

/***************************
 * Renumber symbols so they are ordered as locals, public and then
 * extern/comdef. Returns an array that maps from old to new symbol indices.
 */

static IDXSYM *mach_renumbersyms(IDXSYM *plocal_cnt, IDXSYM *pextdef_cnt, IDXSYM *pundef_cnt)
{
    //printf("mach_renumbersyms()\n");
    const size_t symbol_cnt = symbol_table->size() / (I64 ? sizeof(nlist_64) : sizeof(nlist));
    struct nlist_64 *psyms64 = (struct nlist_64 *)symbol_table;
    struct nlist *psyms = (struct nlist *)symbol_table;

    IDXSYM n = 0;
    IDXSYM *sym_map = (IDXSYM *)util_malloc(sizeof(IDXSYM), symbol_cnt);
    // locals
    for (IDXSYM i = 0; i < symbol_cnt; ++i)
    {
        uint8_t type = I64 ? psyms64[i].n_type : psyms[i].n_type;
        if ((type & (N_EXT | N_UNDF)) == 0)
            sym_map[i] = n++;
    }
    *plocal_cnt = n;
    // extdef
    for (IDXSYM i = 0; i < symbol_cnt; ++i)
    {
        uint8_t type = I64 ? psyms64[i].n_type : psyms[i].n_type;
        if ((type & (N_EXT | N_UNDF)) == N_EXT)
            sym_map[i] = n++;
    }
    *pextdef_cnt = n - *plocal_cnt;
    // undefined/comdef
    for (IDXSYM i = 0; i < symbol_cnt; ++i)
    {
        uint8_t type = I64 ? psyms64[i].n_type : psyms[i].n_type;
        if ((type & (N_EXT | N_UNDF)) == (N_EXT | N_UNDF))
            sym_map[i] = n++;
    }
    *pundef_cnt = n - *pextdef_cnt - *plocal_cnt;
    assert(n == symbol_cnt);
    return sym_map;
}


/***************************
 * Fixup and terminate object file.
 */

void Obj::termfile()
{
    //dbg_printf("Obj::termfile\n");
    if (configv.addlinenumbers)
    {
        dwarf_termmodule();
    }
}

/*********************************
 * Terminate package.
 */

void Obj::term(const char *objfilename)
{
    //printf("Obj::term()\n");
#if SCPP
    if (!errcnt)
#endif
    {
        outfixlist();           // backpatches
    }

    if (configv.addlinenumbers)
    {
        dwarf_termfile();
    }

#if SCPP
    if (errcnt)
        return;
#endif

    /* Write out the object file in the following order:
     *  header
     *  commands
     *          segment_command
     *                  { sections }
     *          symtab_command
     *          dysymtab_command
     *  { segment contents }
     *  { relocations }
     *  symbol table
     *  string table
     *  indirect symbol table
     */

    unsigned foffset;
    unsigned headersize;
    unsigned sizeofcmds;

    // Write out the bytes for the header
    if (I64)
    {
        mach_header_64 header;

        header.magic = MH_MAGIC_64;
        header.cputype = CPU_TYPE_X86_64;
        header.cpusubtype = CPU_SUBTYPE_I386_ALL;
        header.filetype = MH_OBJECT;
        header.ncmds = 3;
        header.sizeofcmds = sizeof(segment_command_64) +
                                (section_cnt - 1) * sizeof(struct section_64) +
                            sizeof(symtab_command) +
                            sizeof(dysymtab_command);
        header.flags = MH_SUBSECTIONS_VIA_SYMBOLS;
        header.reserved = 0;
        fobjbuf->write(&header, sizeof(header));
        foffset = sizeof(header);       // start after header
        headersize = sizeof(header);
        sizeofcmds = header.sizeofcmds;

        // Write the actual data later
        fobjbuf->writezeros(header.sizeofcmds);
        foffset += header.sizeofcmds;
    }
    else
    {
        mach_header header;

        header.magic = MH_MAGIC;
        header.cputype = CPU_TYPE_I386;
        header.cpusubtype = CPU_SUBTYPE_I386_ALL;
        header.filetype = MH_OBJECT;
        header.ncmds = 3;
        header.sizeofcmds = sizeof(segment_command) +
                                (section_cnt - 1) * sizeof(struct section) +
                            sizeof(symtab_command) +
                            sizeof(dysymtab_command);
        header.flags = MH_SUBSECTIONS_VIA_SYMBOLS;
        fobjbuf->write(&header, sizeof(header));
        foffset = sizeof(header);       // start after header
        headersize = sizeof(header);
        sizeofcmds = header.sizeofcmds;

        // Write the actual data later
        fobjbuf->writezeros(header.sizeofcmds);
        foffset += header.sizeofcmds;
    }

    struct segment_command segment_cmd;
    struct segment_command_64 segment_cmd64;
    struct symtab_command symtab_cmd;
    struct dysymtab_command dysymtab_cmd;

    memset(&segment_cmd, 0, sizeof(segment_cmd));
    memset(&segment_cmd64, 0, sizeof(segment_cmd64));
    memset(&symtab_cmd, 0, sizeof(symtab_cmd));
    memset(&dysymtab_cmd, 0, sizeof(dysymtab_cmd));

    if (I64)
    {
        segment_cmd64.cmd = LC_SEGMENT_64;
        segment_cmd64.cmdsize = sizeof(segment_cmd64) +
                                    (section_cnt - 1) * sizeof(struct section_64);
        segment_cmd64.nsects = section_cnt - 1;
        segment_cmd64.maxprot = 7;
        segment_cmd64.initprot = 7;
    }
    else
    {
        segment_cmd.cmd = LC_SEGMENT;
        segment_cmd.cmdsize = sizeof(segment_cmd) +
                                    (section_cnt - 1) * sizeof(struct section);
        segment_cmd.nsects = section_cnt - 1;
        segment_cmd.maxprot = 7;
        segment_cmd.initprot = 7;
    }

    symtab_cmd.cmd = LC_SYMTAB;
    symtab_cmd.cmdsize = sizeof(symtab_cmd);

    dysymtab_cmd.cmd = LC_DYSYMTAB;
    dysymtab_cmd.cmdsize = sizeof(dysymtab_cmd);

    /* If a __pointers section was emitted, need to set the .reserved1
     * field to the symbol index in the indirect symbol table of the
     * start of the __pointers symbols.
     */
    if (pointersSeg)
    {
        seg_data *pseg = SegData[pointersSeg];
        if (I64)
        {
            struct section_64 *psechdr = &SecHdrTab64[pseg->SDshtidx]; // corresponding section
            psechdr->reserved1 = indirectsymbuf1
                ? indirectsymbuf1->size() / sizeof(Symbol *)
                : 0;
        }
        else
        {
            struct section *psechdr = &SecHdrTab[pseg->SDshtidx]; // corresponding section
            psechdr->reserved1 = indirectsymbuf1
                ? indirectsymbuf1->size() / sizeof(Symbol *)
                : 0;
        }
    }

    // Walk through sections determining size and file offsets

    //
    // First output individual section data associate with program
    //  code and data
    //
    foffset = elf_align(I64 ? 8 : 4, foffset);
    if (I64)
        segment_cmd64.fileoff = foffset;
    else
        segment_cmd.fileoff = foffset;
    unsigned vmaddr = 0;

    //printf("Setup offsets and sizes foffset %d\n\tsection_cnt %d, seg_count %d\n",foffset,section_cnt,seg_count);
    // Zero filled segments go at the end, so go through segments twice
    for (int i = 0; i < 2; i++)
    {
        for (int seg = 1; seg <= seg_count; seg++)
        {
            seg_data *pseg = SegData[seg];
            if (I64)
            {
                struct section_64 *psechdr = &SecHdrTab64[pseg->SDshtidx]; // corresponding section

                // Do zero-fill the second time through this loop
                if (i ^ (psechdr->flags == S_ZEROFILL))
                    continue;

                int align = 1 << psechdr->align;
                while (align < pseg->SDalignment)
                {
                    psechdr->align += 1;
                    align <<= 1;
                }
                foffset = elf_align(align, foffset);
                vmaddr = (vmaddr + align - 1) & ~(align - 1);
                if (psechdr->flags == S_ZEROFILL)
                {
                    psechdr->offset = 0;
                    psechdr->size = pseg->SDoffset; // accumulated size
                }
                else
                {
                    psechdr->offset = foffset;
                    psechdr->size = 0;
                    //printf("\tsection name %s,", psechdr->sectname);
                    if (pseg->SDbuf && pseg->SDbuf->size())
                    {
                        //printf("\tsize %d\n", pseg->SDbuf->size());
                        psechdr->size = pseg->SDbuf->size();
                        fobjbuf->write(pseg->SDbuf->buf, psechdr->size);
                        foffset += psechdr->size;
                    }
                }
                psechdr->addr = vmaddr;
                vmaddr += psechdr->size;
                //printf(" assigned offset %d, size %d\n", foffset, psechdr->sh_size);
            }
            else
            {
                struct section *psechdr = &SecHdrTab[pseg->SDshtidx]; // corresponding section

                // Do zero-fill the second time through this loop
                if (i ^ (psechdr->flags == S_ZEROFILL))
                    continue;

                int align = 1 << psechdr->align;
                while (align < pseg->SDalignment)
                {
                    psechdr->align += 1;
                    align <<= 1;
                }
                foffset = elf_align(align, foffset);
                vmaddr = (vmaddr + align - 1) & ~(align - 1);
                if (psechdr->flags == S_ZEROFILL)
                {
                    psechdr->offset = 0;
                    psechdr->size = pseg->SDoffset; // accumulated size
                }
                else
                {
                    psechdr->offset = foffset;
                    psechdr->size = 0;
                    //printf("\tsection name %s,", psechdr->sectname);
                    if (pseg->SDbuf && pseg->SDbuf->size())
                    {
                        //printf("\tsize %d\n", pseg->SDbuf->size());
                        psechdr->size = pseg->SDbuf->size();
                        fobjbuf->write(pseg->SDbuf->buf, psechdr->size);
                        foffset += psechdr->size;
                    }
                }
                psechdr->addr = vmaddr;
                vmaddr += psechdr->size;
                //printf(" assigned offset %d, size %d\n", foffset, psechdr->sh_size);
            }
        }
    }

    if (I64)
    {
        segment_cmd64.vmsize = vmaddr;
        segment_cmd64.filesize = foffset - segment_cmd64.fileoff;
        /* Bugzilla 5331: Apparently having the filesize field greater than the vmsize field is an
         * error, and is happening sometimes.
         */
        if (segment_cmd64.filesize > vmaddr)
            segment_cmd64.vmsize = segment_cmd64.filesize;
    }
    else
    {
        segment_cmd.vmsize = vmaddr;
        segment_cmd.filesize = foffset - segment_cmd.fileoff;
        /* Bugzilla 5331: Apparently having the filesize field greater than the vmsize field is an
         * error, and is happening sometimes.
         */
        if (segment_cmd.filesize > vmaddr)
            segment_cmd.vmsize = segment_cmd.filesize;
    }

    // Sort symbols
    IDXSYM local_cnt, extdef_cnt, undef_cnt;
    IDXSYM *sym_map = mach_renumbersyms(&local_cnt, &extdef_cnt, &undef_cnt);

    // Put out relocation data
    for (int seg = 1; seg <= seg_count; seg++)
    {
        foffset = elf_align(I64 ? 8 : 4, foffset);
        assert(foffset == fobjbuf->size());
        writeRelocations(seg, sym_map, fobjbuf);
        foffset = fobjbuf->size();
    }

    // Put out symbol table
    const size_t symbol_cnt = symbol_table->size() / (I64 ? sizeof(nlist_64) : sizeof(nlist));
    foffset = elf_align(I64 ? 8 : 4, foffset);
    symtab_cmd.symoff = foffset;
    dysymtab_cmd.ilocalsym = 0;
    dysymtab_cmd.nlocalsym  = local_cnt;
    dysymtab_cmd.iextdefsym = local_cnt;
    dysymtab_cmd.nextdefsym = extdef_cnt;
    dysymtab_cmd.iundefsym = local_cnt + extdef_cnt;
    dysymtab_cmd.nundefsym  = undef_cnt;
    assert(local_cnt + extdef_cnt + undef_cnt == symbol_cnt);
    symtab_cmd.nsyms = symbol_cnt;

    if (I64)
    {
        struct nlist_64 *psyms = (struct nlist_64 *)symbol_table;
        fobjbuf->reserve(symbol_cnt * sizeof(psyms[0]));
        for (IDXSYM i = 0; i < local_cnt + extdef_cnt; ++i)
        {
            struct nlist_64 *psym = &psyms[sym_map[i]];
            // relocate all defined symbols by section address
            psym->n_value += SecHdrTab64[psym->n_sect].addr;
            fobjbuf->write(psym, sizeof(*psym));
        }
        // Put out undefined symbols
        for (IDXSYM i = local_cnt + extdef_cnt; i < symbol_cnt; ++i)
            fobjbuf->write(&psyms[sym_map[i]], sizeof(psyms[0]));
        foffset += symbol_cnt * sizeof(psyms[0]);
    }
    else
    {
        struct nlist *psyms = (struct nlist *)symbol_table;
        fobjbuf->reserve(symbol_cnt * sizeof(psyms[0]));
        for (IDXSYM i = 0; i < local_cnt + extdef_cnt; ++i)
        {
            struct nlist *psym = &psyms[sym_map[i]];
            // relocate all defined symbols by section address
            psym->n_value += SecHdrTab[psym->n_sect].addr;
            fobjbuf->write(psym, sizeof(*psym));
        }
        // Put out undefined symbols
        for (IDXSYM i = local_cnt + extdef_cnt; i < symbol_cnt; ++i)
            fobjbuf->write(&psyms[sym_map[i]], sizeof(psyms[0]));
        foffset += symbol_cnt * sizeof(psyms[0]);
    }

    // Put out string table
    foffset = elf_align(I64 ? 8 : 4, foffset);
    symtab_cmd.stroff = foffset;
    symtab_cmd.strsize = symtab_strings->size();
    fobjbuf->write(symtab_strings->buf, symtab_cmd.strsize);
    foffset += symtab_cmd.strsize;

    // Put out indirectsym table, which is in two parts
    foffset = elf_align(I64 ? 8 : 4, foffset);
    dysymtab_cmd.indirectsymoff = foffset;
    if (indirectsymbuf1)
    {
        IDXSYM cnt = indirectsymbuf1->size() / sizeof(IDXSYM);
        IDXSYM *psyms = (IDXSYM *)indirectsymbuf1->buf;
        for (IDXSYM i = 0; i < cnt; ++i)
            fobjbuf->write32(sym_map[psyms[i]]);
        dysymtab_cmd.nindirectsyms += cnt;
    }
    if (indirectsymbuf2)
    {
        IDXSYM cnt = indirectsymbuf2->size() / sizeof(IDXSYM);
        IDXSYM *psyms = (IDXSYM *)indirectsymbuf2->buf;
        for (IDXSYM i = 0; i < cnt; ++i)
            fobjbuf->write32(sym_map[psyms[i]]);
        dysymtab_cmd.nindirectsyms += cnt;
    }
    foffset += dysymtab_cmd.nindirectsyms * 4;

    /* The correct offsets are now determined, so
     * rewind and fix the header.
     */
    fobjbuf->position(headersize, sizeofcmds);
    if (I64)
    {
        fobjbuf->write(&segment_cmd64, sizeof(segment_cmd64));
        fobjbuf->write(SECbuf->buf + sizeof(struct section_64), (section_cnt - 1) * sizeof(struct section_64));
    }
    else
    {
        fobjbuf->write(&segment_cmd, sizeof(segment_cmd));
        fobjbuf->write(SECbuf->buf + sizeof(struct section), (section_cnt - 1) * sizeof(struct section));
    }
    fobjbuf->write(&symtab_cmd, sizeof(symtab_cmd));
    fobjbuf->write(&dysymtab_cmd, sizeof(dysymtab_cmd));
    fobjbuf->position(foffset, 0);
    fobjbuf->flush();
}

/*****************************
 * Line number support.
 */

/***************************
 * Record file and line number at segment and offset.
 * The actual .debug_line segment is put out by dwarf_termfile().
 * Input:
 *      cseg    current code segment
 */

void Obj::linnum(Srcpos srcpos, targ_size_t offset)
{
    if (srcpos.Slinnum == 0)
        return;

#if 0
#if MARS || SCPP
    printf("Obj::linnum(cseg=%d, offset=x%lx) ", cseg, offset);
#endif
    srcpos.print("");
#endif

#if MARS
    if (!srcpos.Sfilename)
        return;
#endif
#if SCPP
    if (!srcpos.Sfilptr)
        return;
    sfile_debug(&srcpos_sfile(srcpos));
    Sfile *sf = *srcpos.Sfilptr;
#endif

    size_t i;
    seg_data *seg = SegData[cseg];

    // Find entry i in SDlinnum_data[] that corresponds to srcpos filename
    for (i = 0; 1; i++)
    {
        if (i == seg->SDlinnum_count)
        {   // Create new entry
            if (seg->SDlinnum_count == seg->SDlinnum_max)
            {   // Enlarge array
                unsigned newmax = seg->SDlinnum_max * 2 + 1;
                //printf("realloc %d\n", newmax * sizeof(linnum_data));
                seg->SDlinnum_data = (linnum_data *)mem_realloc(
                    seg->SDlinnum_data, newmax * sizeof(linnum_data));
                memset(seg->SDlinnum_data + seg->SDlinnum_max, 0,
                    (newmax - seg->SDlinnum_max) * sizeof(linnum_data));
                seg->SDlinnum_max = newmax;
            }
            seg->SDlinnum_count++;
#if MARS
            seg->SDlinnum_data[i].filename = srcpos.Sfilename;
#endif
#if SCPP
            seg->SDlinnum_data[i].filptr = sf;
#endif
            break;
        }
#if MARS
        if (seg->SDlinnum_data[i].filename == srcpos.Sfilename)
#endif
#if SCPP
        if (seg->SDlinnum_data[i].filptr == sf)
#endif
            break;
    }

    linnum_data *ld = &seg->SDlinnum_data[i];
//    printf("i = %d, ld = x%x\n", i, ld);
    if (ld->linoff_count == ld->linoff_max)
    {
        if (!ld->linoff_max)
            ld->linoff_max = 8;
        ld->linoff_max *= 2;
        ld->linoff = (unsigned (*)[2])mem_realloc(ld->linoff, ld->linoff_max * sizeof(unsigned) * 2);
    }
    ld->linoff[ld->linoff_count][0] = srcpos.Slinnum;
    ld->linoff[ld->linoff_count][1] = offset;
    ld->linoff_count++;
}


/*******************************
 * Set start address
 */

void Obj::startaddress(Symbol *s)
{
    //dbg_printf("Obj::startaddress(Symbol *%s)\n",s->Sident);
    //obj.startaddress = s;
}

/*******************************
 * Output library name.
 */

bool Obj::includelib(const char *name)
{
    //dbg_printf("Obj::includelib(name *%s)\n",name);
    return false;
}

/**********************************
 * Do we allow zero sized objects?
 */

bool Obj::allowZeroSize()
{
    return true;
}

/**************************
 * Embed string in executable.
 */

void Obj::exestr(const char *p)
{
    //dbg_printf("Obj::exestr(char *%s)\n",p);
}

/**************************
 * Embed string in obj.
 */

void Obj::user(const char *p)
{
    //dbg_printf("Obj::user(char *%s)\n",p);
}

/*******************************
 * Output a weak extern record.
 */

void Obj::wkext(Symbol *s1,Symbol *s2)
{
    //dbg_printf("Obj::wkext(Symbol *%s,Symbol *s2)\n",s1->Sident,s2->Sident);
}

/*******************************
 * Output file name record.
 *
 * Currently assumes that obj_filename will not be called
 *      twice for the same file.
 */

void obj_filename(const char *modname)
{
    //dbg_printf("obj_filename(char *%s)\n",modname);
    // Not supported by Mach-O
}

/*******************************
 * Embed compiler version in .obj file.
 */

void Obj::compiler()
{
    //dbg_printf("Obj::compiler\n");
}

//#if NEWSTATICDTOR

/**************************************
 * Symbol is the function that calls the static constructors.
 * Put a pointer to it into a special segment that the startup code
 * looks at.
 * Input:
 *      s       static constructor function
 *      dtor    !=0 if leave space for static destructor
 *      seg     1:      user
 *              2:      lib
 *              3:      compiler
 */

void Obj::staticctor(Symbol *s,int dtor,int none)
{
#if 0
    IDXSEC seg;
    Outbuffer *buf;

    //dbg_printf("Obj::staticctor(%s) offset %x\n",s->Sident,s->Soffset);
    //symbol_print(s);
    s->Sseg = seg =
        ElfObj::getsegment(".ctors", NULL, SHT_PROGDEF, SHF_ALLOC|SHF_WRITE, 4);
    buf = SegData[seg]->SDbuf;
    if (I64)
        buf->write64(s->Soffset);
    else
        buf->write32(s->Soffset);
    MachObj::addrel(seg, SegData[seg]->SDoffset, s, RELaddr);
    SegData[seg]->SDoffset = buf->size();
#endif
}

/**************************************
 * Symbol is the function that calls the static destructors.
 * Put a pointer to it into a special segment that the exit code
 * looks at.
 * Input:
 *      s       static destructor function
 */

void Obj::staticdtor(Symbol *s)
{
#if 0
    IDXSEC seg;
    Outbuffer *buf;

    //dbg_printf("Obj::staticdtor(%s) offset %x\n",s->Sident,s->Soffset);
    //symbol_print(s);
    seg = ElfObj::getsegment(".dtors", NULL, SHT_PROGDEF, SHF_ALLOC|SHF_WRITE, 4);
    buf = SegData[seg]->SDbuf;
    if (I64)
        buf->write64(s->Soffset);
    else
        buf->write32(s->Soffset);
    MachObj::addrel(seg, SegData[seg]->SDoffset, s, RELaddr);
    SegData[seg]->SDoffset = buf->size();
#endif
}

//#else

/***************************************
 * Stuff pointer to function in its own segment.
 * Used for static ctor and dtor lists.
 */

void Obj::funcptr(Symbol *s)
{
    //dbg_printf("Obj::funcptr(%s) \n",s->Sident);
}

//#endif

/***************************************
 * Stuff the following data (instance of struct FuncTable) in a separate segment:
 *      pointer to function
 *      pointer to ehsym
 *      length of function
 */

void Obj::ehtables(Symbol *sfunc,targ_size_t size,Symbol *ehsym)
{
    //dbg_printf("Obj::ehtables(%s) \n",sfunc->Sident);

    /* BUG: this should go into a COMDAT if sfunc is in a COMDAT
     * otherwise the duplicates aren't removed.
     */

    int align = I64 ? 3 : 2;            // align to NPTRSIZE
    // The size is sizeof(struct FuncTable) in deh2.d
    int seg = MachObj::getsegment("__deh_eh", "__DATA", align, S_REGULAR);

    Outbuffer *buf = SegData[seg]->SDbuf;
    if (I64)
    {   Obj::reftoident(seg, buf->size(), sfunc, 0, CFoff | CFoffset64);
        Obj::reftoident(seg, buf->size(), ehsym, 0, CFoff | CFoffset64);
        buf->write64(sfunc->Ssize);
    }
    else
    {   Obj::reftoident(seg, buf->size(), sfunc, 0, CFoff);
        Obj::reftoident(seg, buf->size(), ehsym, 0, CFoff);
        buf->write32(sfunc->Ssize);
    }
}

/*********************************************
 * Put out symbols that define the beginning/end of the .deh_eh section.
 * This gets called if this is the module with "main()" in it.
 */

void Obj::ehsections()
{
    //printf("Obj::ehsections()\n");
}

/*********************************
 * Setup for Symbol s to go into a COMDAT segment.
 * Output (if s is a function):
 *      cseg            segment index of new current code segment
 *      Coffset         starting offset in cseg
 * Returns:
 *      "segment index" of COMDAT
 */

int Obj::comdatsize(Symbol *s, targ_size_t symsize)
{
    return Obj::comdat(s);
}

int Obj::comdat(Symbol *s)
{
    const char *sectname;
    const char *segname;
    int align;
    int flags;

    //printf("Obj::comdat(Symbol* %s)\n",s->Sident);
    //symbol_print(s);
    symbol_debug(s);

    if (tyfunc(s->ty()))
    {
        sectname = "__textcoal_nt";
        segname = "__TEXT";
        align = 2;              // 4 byte alignment
        flags = S_COALESCED | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS;
        s->Sseg = MachObj::getsegment(sectname, segname, align, flags);
    }
    else if ((s->ty() & mTYLINK) == mTYthread)
    {
        s->Sfl = FLtlsdata;
        align = 4;
        s->Sseg = MachObj::getsegment("__tlscoal_nt", "__DATA", align, S_COALESCED);
        Obj::data_start(s, 1 << align, s->Sseg);
    }
    else
    {
        s->Sfl = FLdata;
        sectname = "__datacoal_nt";
        segname = "__DATA";
        align = 4;              // 16 byte alignment
        s->Sseg = MachObj::getsegment(sectname, segname, align, S_COALESCED);
    }
                                // find or create new segment
    if (s->Salignment > (1 << align))
        SegData[s->Sseg]->SDalignment = s->Salignment;
    s->Soffset = SegData[s->Sseg]->SDoffset;
    if (s->Sfl == FLdata || s->Sfl == FLtlsdata)
    {   // Code symbols are 'published' by Obj::func_start()

        Obj::pubdef(s->Sseg,s,s->Soffset);
        searchfixlist(s);               // backpatch any refs to this symbol
    }
    return s->Sseg;
}

/**********************************
 * Get segment.
 * Input:
 *      align   segment alignment as power of 2
 * Returns:
 *      segment index of found or newly created segment
 */

int MachObj::getsegment(const char *sectname, const char *segname,
        int align, int flags)
{
    assert(strlen(sectname) <= 16);
    assert(strlen(segname)  <= 16);
    for (int seg = 1; seg <= seg_count; seg++)
    {   seg_data *pseg = SegData[seg];
        if (I64)
        {
            if (strncmp(SecHdrTab64[pseg->SDshtidx].sectname, sectname, 16) == 0 &&
                strncmp(SecHdrTab64[pseg->SDshtidx].segname, segname, 16) == 0)
                return seg;         // return existing segment
        }
        else
        {
            if (strncmp(SecHdrTab[pseg->SDshtidx].sectname, sectname, 16) == 0 &&
                strncmp(SecHdrTab[pseg->SDshtidx].segname, segname, 16) == 0)
                return seg;         // return existing segment
        }
    }

    int seg = ++seg_count;
    if (seg_count >= seg_max)
    {                           // need more room in segment table
        seg_max += 10;
        SegData = (seg_data **)mem_realloc(SegData,seg_max * sizeof(seg_data *));
        memset(&SegData[seg_count], 0, (seg_max - seg_count) * sizeof(seg_data *));
    }
    assert(seg_count < seg_max);
    if (SegData[seg])
    {   seg_data *pseg = SegData[seg];
        Outbuffer *b1 = pseg->SDbuf;
        Outbuffer *b2 = pseg->SDrel;
        memset(pseg, 0, sizeof(seg_data));
        if (b1)
            b1->setsize(0);
        if (b2)
            b2->setsize(0);
        pseg->SDbuf = b1;
        pseg->SDrel = b2;
    }
    else
    {
        seg_data *pseg = (seg_data *)mem_calloc(sizeof(seg_data));
        SegData[seg] = pseg;
        if (flags != S_ZEROFILL)
        {   pseg->SDbuf = new Outbuffer(4096);
            pseg->SDbuf->reserve(4096);
        }
    }

    //dbg_printf("\tNew segment - %d size %d\n", seg,SegData[seg]->SDbuf);
    seg_data *pseg = SegData[seg];

    pseg->SDseg = seg;
    pseg->SDoffset = 0;

    if (I64)
    {
        struct section_64 *sec = (struct section_64 *)
            SECbuf->writezeros(sizeof(struct section_64));
        strncpy(sec->sectname, sectname, 16);
        strncpy(sec->segname, segname, 16);
        sec->align = align;
        sec->flags = flags;
    }
    else
    {
        struct section *sec = (struct section *)
            SECbuf->writezeros(sizeof(struct section));
        strncpy(sec->sectname, sectname, 16);
        strncpy(sec->segname, segname, 16);
        sec->align = align;
        sec->flags = flags;
    }

    pseg->SDshtidx = section_cnt++;
    pseg->SDaranges_offset = 0;
    pseg->SDlinnum_count = 0;

    //printf("seg_count = %d\n", seg_count);
    return seg;
}

/**********************************
 * Reset code seg to existing seg.
 * Used after a COMDAT for a function is done.
 */

void Obj::setcodeseg(int seg)
{
}

/********************************
 * Define a new code segment.
 * Input:
 *      name            name of segment, if NULL then revert to default
 *      suffix  0       use name as is
 *              1       append "_TEXT" to name
 * Output:
 *      cseg            segment index of new current code segment
 *      Coffset         starting offset in cseg
 * Returns:
 *      segment index of newly created code segment
 */

int Obj::codeseg(char *name,int suffix)
{
    //dbg_printf("Obj::codeseg(%s,%x)\n",name,suffix);
#if 0
    const char *sfx = (suffix) ? "_TEXT" : NULL;

    if (!name)                          // returning to default code segment
    {
        if (cseg != CODE)               // not the current default
        {
            SegData[cseg]->SDoffset = Coffset;
            Coffset = SegData[CODE]->SDoffset;
            cseg = CODE;
        }
        return cseg;
    }

    int seg = ElfObj::getsegment(name, sfx, SHT_PROGDEF, SHF_ALLOC|SHF_EXECINSTR, 4);
                                    // find or create code segment

    cseg = seg;                         // new code segment index
    Coffset = 0;
    return seg;
#else
    return 0;
#endif
}

/*********************************
 * Define segments for Thread Local Storage.
 * Output:
 *      seg_tlsseg      set to segment number for TLS segment.
 * Returns:
 *      segment for TLS segment
 */

seg_data *Obj::tlsseg()
{
    //printf("Obj::tlsseg(\n");

    if (seg_tlsseg == UNKNOWN)
    {
        int align = I64 ? 4 : 2;            // align to 16 bytes for floating point
        seg_tlsseg = MachObj::getsegment("__tls_data", "__DATA", align, S_REGULAR);
    }
    return SegData[seg_tlsseg];
}


/*********************************
 * Define segments for Thread Local Storage.
 * Output:
 *      seg_tlsseg_bss  set to segment number for TLS segment.
 * Returns:
 *      segment for TLS segment
 */

seg_data *Obj::tlsseg_bss()
{
    /* Because Mach-O does not support tls, it's easier to support
     * if we have all the tls in one segment.
     */
    return Obj::tlsseg();
}


/*******************************
 * Output an alias definition record.
 */

void Obj::alias(const char *n1,const char *n2)
{
    //printf("Obj::alias(%s,%s)\n",n1,n2);
    assert(0);
#if NOT_DONE
    unsigned len;
    char *buffer;

    buffer = (char *) alloca(strlen(n1) + strlen(n2) + 2 * ONS_OHD);
    len = obj_namestring(buffer,n1);
    len += obj_namestring(buffer + len,n2);
    objrecord(ALIAS,buffer,len);
#endif
}

char *unsstr (unsigned value)
{
    static char buffer [64];

    sprintf (buffer, "%d", value);
    return buffer;
}

/*******************************
 * Mangle a name.
 * Returns:
 *      mangled name
 */

char *obj_mangle2(Symbol *s,char *dest)
{
    size_t len;
    char *name;

    //printf("Obj::mangle(s = %p, '%s'), mangle = x%x\n",s,s->Sident,type_mangle(s->Stype));
    symbol_debug(s);
    assert(dest);
#if SCPP
    name = CPP ? cpp_mangle(s) : s->Sident;
#elif MARS
    name = cpp_mangle(s);
#else
    name = s->Sident;
#endif
    len = strlen(name);                 // # of bytes in name
    //dbg_printf("len %d\n",len);
    switch (type_mangle(s->Stype))
    {
        case mTYman_pas:                // if upper case
        case mTYman_for:
            if (len >= DEST_LEN)
                dest = (char *)mem_malloc(len + 1);
            memcpy(dest,name,len + 1);  // copy in name and ending 0
            for (char *p = dest; *p; p++)
                *p = toupper(*p);
            break;
        case mTYman_std:
#if TARGET_LINUX || TARGET_OSX || TARGET_FREEBSD || TARGET_OPENBSD || TARGET_SOLARIS
            if (tyfunc(s->ty()) && !variadic(s->Stype))
#else
            if (!(config.flags4 & CFG4oldstdmangle) &&
                config.exe == EX_NT && tyfunc(s->ty()) &&
                !variadic(s->Stype))
#endif
            {
                char *pstr = unsstr(type_paramsize(s->Stype));
                size_t pstrlen = strlen(pstr);
                size_t destlen = len + 1 + pstrlen + 1;

                if (destlen > DEST_LEN)
                    dest = (char *)mem_malloc(destlen);
                memcpy(dest,name,len);
                dest[len] = '@';
                memcpy(dest + 1 + len, pstr, pstrlen + 1);
                break;
            }
        case mTYman_cpp:
        case mTYman_d:
        case mTYman_sys:
        case 0:
            if (len >= DEST_LEN)
                dest = (char *)mem_malloc(len + 1);
            memcpy(dest,name,len+1);// copy in name and trailing 0
            break;

        case mTYman_c:
            if (len >= DEST_LEN - 1)
                dest = (char *)mem_malloc(1 + len + 1);
            dest[0] = '_';
            memcpy(dest + 1,name,len+1);// copy in name and trailing 0
            break;


        default:
#ifdef DEBUG
            printf("mangling %x\n",type_mangle(s->Stype));
            symbol_print(s);
#endif
            printf("%d\n", type_mangle(s->Stype));
            assert(0);
    }
    //dbg_printf("\t %s\n",dest);
    return dest;
}

/*******************************
 * Export a function name.
 */

void Obj::export_symbol(Symbol *s,unsigned argsize)
{
    //dbg_printf("Obj::export_symbol(%s,%d)\n",s->Sident,argsize);
}

/*******************************
 * Update data information about symbol
 *      align for output and assign segment
 *      if not already specified.
 *
 * Input:
 *      sdata           data symbol
 *      datasize        output size
 *      seg             default seg if not known
 * Returns:
 *      actual seg
 */

int Obj::data_start(Symbol *sdata, targ_size_t datasize, int seg)
{
    targ_size_t alignbytes;

    //printf("Obj::data_start(%s,size %d,seg %d)\n",sdata->Sident,datasize,seg);
    //symbol_print(sdata);

    assert(sdata->Sseg);
    if (sdata->Sseg == UNKNOWN) // if we don't know then there
        sdata->Sseg = seg;      // wasn't any segment override
    else
        seg = sdata->Sseg;
    targ_size_t offset = Offset(seg);
    if (sdata->Salignment > 0)
    {   if (SegData[seg]->SDalignment < sdata->Salignment)
            SegData[seg]->SDalignment = sdata->Salignment;
        alignbytes = ((offset + sdata->Salignment - 1) & ~(sdata->Salignment - 1)) - offset;
    }
    else
        alignbytes = align(datasize, offset) - offset;
    if (alignbytes)
        Obj::lidata(seg, offset, alignbytes);
    sdata->Soffset = offset + alignbytes;
    return seg;
}

/*******************************
 * Update function info before codgen
 *
 * If code for this function is in a different segment
 * than the current default in cseg, switch cseg to new segment.
 */

void Obj::func_start(Symbol *sfunc)
{
    //printf("Obj::func_start(%s)\n",sfunc->Sident);
    symbol_debug(sfunc);

    assert(sfunc->Sseg);
    if (sfunc->Sseg == UNKNOWN)
        sfunc->Sseg = CODE;
    //printf("sfunc->Sseg %d CODE %d cseg %d Coffset x%x\n",sfunc->Sseg,CODE,cseg,Coffset);
    cseg = sfunc->Sseg;
    assert(cseg == CODE || cseg > UDATA);
    Obj::pubdef(cseg, sfunc, Coffset);
    sfunc->Soffset = Coffset;

    if (config.fulltypes)
        dwarf_func_start(sfunc);
}

/*******************************
 * Update function info after codgen
 */

void Obj::func_term(Symbol *sfunc)
{
    //dbg_printf("Obj::func_term(%s) offset %x, Coffset %x symidx %d\n",
//          sfunc->Sident, sfunc->Soffset,Coffset,sfunc->Sxtrnnum);

#if 0
    // fill in the function size
    if (I64)
        SymbolTable64[sfunc->Sxtrnnum].st_size = Coffset - sfunc->Soffset;
    else
        SymbolTable[sfunc->Sxtrnnum].st_size = Coffset - sfunc->Soffset;
#endif
    if (config.fulltypes)
        dwarf_func_term(sfunc);
}

/** Add a symbol to the symbol table. Arguments match nlist/nlist_64 fields.
 */
static IDXSYM mach_addsym(IDXSTR namidx, uint8_t type, uint8_t sect, uint16_t desc, uint64_t value)
{
    if (I64)
    {
        struct nlist_64 sym;
        sym.n_un.n_strx = namidx;
        sym.n_type = type;
        sym.n_sect = sect;
        sym.n_desc = desc;
        sym.n_value = value;
        symbol_table->write(&sym, sizeof(sym));
        return symbol_table->size() / sizeof(sym) - 1;
    }
    else
    {
        struct nlist sym;
        sym.n_un.n_strx = namidx;
        sym.n_type = type;
        sym.n_sect = sect;
        sym.n_desc = desc;
        sym.n_value = value;
        symbol_table->write(&sym, sizeof(sym));
        return symbol_table->size() / sizeof(sym) - 1;
    }
}

/********************************
 * Output a public definition.
 * Input:
 *      sect =          section index that symbol is defined in
 *      s ->            symbol
 *      offset =        offset of name within section
 */

void Obj::pubdefsize(int seg, Symbol *s, targ_size_t offset, targ_size_t symsize)
{
    return Obj::pubdef(seg, s, offset);
}

void Obj::pubdef(int seg, Symbol *s, targ_size_t offset)
{
    uint8_t type;
    uint16_t desc;
    switch (s->Sclass)
    {
        case SCglobal:
        case SCinline:
            type = N_EXT | N_SECT;
            desc = 0;
            break;
        case SCcomdat:
        case SCcomdef:
            type = N_EXT | N_SECT;
            desc = N_WEAK_DEF;
            break;
        default:
            type = N_SECT;
            desc = 0;
            break;
    }

#if 0
    //printf("\nObj::pubdef(%d,%s,%d)\n",seg,s->Sident,offset);
    //symbol_print(s);
#endif

    symbol_debug(s);
    IDXSTR namidx = mach_addmangled(s);
    // offset will be relocated later to offset + section.addr
    s->Sxtrnnum = mach_addsym(namidx, type, MAP_SEG2SECIDX(seg), desc, offset);
    s->Soffset = offset; // TODO: needed?
    s->Sseg = seg; // TODO: needed?
}

/*******************************
 * Output an external symbol for name.
 * Input:
 *      name    Name to do EXTDEF on
 *              (Not to be mangled)
 * Returns:
 *      Symbol table index of the definition
 *      NOTE: Numbers will not be linear.
 */

int Obj::external_def(const char *name)
{
    //printf("Obj::external_def('%s')\n",name);
    assert(name);
    IDXSTR namidx = Obj::addstr(symtab_strings, name);
    uint8_t type = N_EXT | N_UNDF;
    uint8_t sect = 0;
    uint16_t desc = 0;
    return mach_addsym(namidx, type, sect, desc, 0);
}


/*******************************
 * Output an external for existing symbol.
 * Input:
 *      s       Symbol to do EXTDEF on
 *              (Name is to be mangled)
 * Returns:
 *      Symbol table index of the definition
 *      NOTE: Numbers will not be linear.
 */

int Obj::external(Symbol *s)
{
    //printf("Obj::external('%s') %x\n",s->Sident,s->Svalue);
    symbol_debug(s);
    IDXSTR namidx = mach_addmangled(s);
    uint8_t type = N_EXT | N_UNDF;
    uint8_t sect = 0;
    uint16_t desc = tyfunc(s->ty()) ? REFERENCE_FLAG_UNDEFINED_LAZY
        : REFERENCE_FLAG_UNDEFINED_NON_LAZY;
    return mach_addsym(namidx, type, sect, desc, s->Soffset);
}

/*******************************
 * Output a common block definition.
 * Input:
 *      p ->    external identifier
 *      size    size in bytes of each elem
 *      count   number of elems
 * Returns:
 *      Symbol table index for symbol
 */

int Obj::common_block(Symbol *s, targ_size_t size, targ_size_t count)
{
    // can't have code or thread local comdef's
    assert(!(s->ty() & (
#if TARGET_SEGMENTED
                    mTYcs |
#endif
                    mTYthread)));
    uint8_t align;
    if (size < 2)
        align = 0;          // align is expressed as power of 2
    else if (size < 4)
        align = 1;
    else if (size < 8)
        align = 2;
    else if (size < 16)
        align = 3;
    else
        align = 4;

    //printf("Obj::common_block('%s', size=%d, count=%d)\n",s->Sident,size,count);
    symbol_debug(s);
    IDXSTR namidx = mach_addmangled(s);
    uint8_t type = N_EXT | N_UNDF;
    uint8_t sect = 0;
    uint16_t desc = align << 8;
    if (!s->Sseg)
        s->Sseg = UDATA; // TODO: needed?
    return mach_addsym(namidx, type, sect, desc, size * count);
}

int Obj::common_block(Symbol *s, int flag, targ_size_t size, targ_size_t count)
{
    return common_block(s, size, count);
}

/***************************************
 * Append an iterated data block of 0s.
 * (uninitialized data only)
 */

void Obj::write_zeros(seg_data *pseg, targ_size_t count)
{
    Obj::lidata(pseg->SDseg, pseg->SDoffset, count);
}

/***************************************
 * Output an iterated data block of 0s.
 *
 *      For boundary alignment and initialization
 */

void Obj::lidata(int seg,targ_size_t offset,targ_size_t count)
{
    //printf("Obj::lidata(%d,%x,%d)\n",seg,offset,count);
    size_t idx = SegData[seg]->SDshtidx;
    if ((I64 ? SecHdrTab64[idx].flags : SecHdrTab[idx].flags) == S_ZEROFILL)
    {   // Use SDoffset to record size of bss section
        SegData[seg]->SDoffset += count;
    }
    else
    {
        Obj::bytes(seg, offset, count, NULL);
    }
}

/***********************************
 * Append byte to segment.
 */

void Obj::write_byte(seg_data *pseg, unsigned byte)
{
    Obj::byte(pseg->SDseg, pseg->SDoffset, byte);
}

/************************************
 * Output byte to object file.
 */

void Obj::byte(int seg,targ_size_t offset,unsigned byte)
{
    Outbuffer *buf = SegData[seg]->SDbuf;
    int save = buf->size();
    //dbg_printf("Obj::byte(seg=%d, offset=x%lx, byte=x%x)\n",seg,offset,byte);
    buf->setsize(offset);
    buf->writeByte(byte);
    if (save > offset+1)
        buf->setsize(save);
    else
        SegData[seg]->SDoffset = offset+1;
    //dbg_printf("\tsize now %d\n",buf->size());
}

/***********************************
 * Append bytes to segment.
 */

void Obj::write_bytes(seg_data *pseg, unsigned nbytes, void *p)
{
    Obj::bytes(pseg->SDseg, pseg->SDoffset, nbytes, p);
}

/************************************
 * Output bytes to object file.
 * Returns:
 *      nbytes
 */

unsigned Obj::bytes(int seg, targ_size_t offset, unsigned nbytes, void *p)
{
#if 0
    if (!(seg >= 0 && seg <= seg_count))
    {   printf("Obj::bytes: seg = %d, seg_count = %d\n", seg, seg_count);
        *(char*)0=0;
    }
#endif
    assert(seg >= 0 && seg <= seg_count);
    Outbuffer *buf = SegData[seg]->SDbuf;
    if (buf == NULL)
    {
        //dbg_printf("Obj::bytes(seg=%d, offset=x%lx, nbytes=%d, p=x%x)\n", seg, offset, nbytes, p);
        //raise(SIGSEGV);
if (!buf) halt();
        assert(buf != NULL);
    }
    int save = buf->size();
    //dbg_printf("Obj::bytes(seg=%d, offset=x%lx, nbytes=%d, p=x%x)\n",
            //seg,offset,nbytes,p);
    buf->setsize(offset);
    buf->reserve(nbytes);
    if (p)
    {
        buf->writen(p,nbytes);
    }
    else
    {   // Zero out the bytes
        buf->clearn(nbytes);
    }
    if (save > offset+nbytes)
        buf->setsize(save);
    else
        SegData[seg]->SDoffset = offset+nbytes;
    return nbytes;
}

/*********************************************
 * Add a relocation entry for seg/offset.
 */

void MachObj::addrel(int seg, targ_size_t offset, symbol *targsym,
        unsigned targseg, int rtype, int val)
{
    seg_data *pseg = SegData[seg];
    if (!pseg->SDrel)
        pseg->SDrel = new Outbuffer();

    if (targsym)
    {
        symbol *s = targsym;
        relocation_info rel;
        rel.r_address = offset;
        if (pseg->isCode())
        {
            if (I64)
            {
                rel.r_pcrel = 1;
                rel.r_length = 2; // TODO: shouldn't this be 3 for I64?

                switch (val)
                {
                case -1: rel.r_type = X86_64_RELOC_SIGNED_1; break;
                case -2: rel.r_type = X86_64_RELOC_SIGNED_2; break;
                case -4: rel.r_type = X86_64_RELOC_SIGNED_4; break;
                default: rel.r_type = (rtype == RELrel) ? X86_64_RELOC_BRANCH : X86_64_RELOC_SIGNED; break;
                }

                if (s->Sclass == SCextern ||
                    s->Sclass == SCcomdef ||
                    s->Sclass == SCcomdat ||
                    s->Sclass == SCglobal)
                {
                    if ((s->Sfl == FLfunc || s->Sfl == FLextern || s->Sclass == SCglobal || s->Sclass == SCcomdat || s->Sclass == SCcomdef) && rtype == RELaddr)
                        rel.r_type = X86_64_RELOC_GOT_LOAD;
                    rel.r_symbolnum = s->Sxtrnnum;
                    rel.r_extern = 1;
                }
                else
                {
                    rel.r_symbolnum = s->Sseg; // TODO: why not relocate against Sxtrnnum?
                    rel.r_extern = 0;

                    // relative: targseg.addr + s->Soffset - (seg.addr + offset + 4)
                    // section addresses not yet known => patched later
                    int32_t *p = patchAddr64(seg, offset);
                    *p += s->Soffset;
                    *p -= offset + 4;
                }
            }
            else
            {
                // 32-bit only uses the value written to the target address
            }
        }
        else
        {
            rel.r_pcrel = 0;
            rel.r_length = I64 ? 3 : 2;
            rel.r_type = I64 ? X86_64_RELOC_UNSIGNED : GENERIC_RELOC_VANILLA;

            if (s->Sclass == SCextern ||
                s->Sclass == SCcomdef ||
                s->Sclass == SCcomdat)
            {
                rel.r_symbolnum = s->Sxtrnnum;
                rel.r_extern = 1;
            }
            else
            {
                rel.r_symbolnum = s->Sseg;
                rel.r_extern = 0;
                // absolute: targseg.addr + s->Soffset; section address patched later
                *(I64 ? patchAddr64(seg, offset) : patchAddr(seg, offset)) += s->Soffset;
            }
        }
        pseg->SDrel->write(&rel, sizeof(rel));
    }
    else if (rtype == RELaddr && pseg->isCode())
    {
        assert(0); // TODO: is this actually used
        scattered_relocation_info srel;
        srel.r_address = offset;
        if (I64)
            srel.r_type = X86_64_RELOC_GOT; // TODO: why reloc pair?
        else
            srel.r_type = GENERIC_RELOC_LOCAL_SECTDIFF; // TODO: why sectdiff when we can already compute the relative offset
        srel.r_length = 2;
        srel.r_pcrel = 0;
        srel.r_scattered = 1;
        // absolute: targseg.addr + value; section address patched later
        if (I64)
            srel.r_value = *patchAddr64(seg, offset);
        else
            srel.r_value = *patchAddr(seg, offset);
        pseg->SDrel->write(&srel, sizeof(srel));

        srel.r_address = targseg; // HACK: targseg temporarily stored in unused r_address
        srel.r_type = GENERIC_RELOC_PAIR;
        srel.r_length = 2;
        srel.r_pcrel = 0;
        srel.r_scattered = 1;
        // absolute: seg.addr + func.Slocalgotoffset + NPTRSIZE; section address patched later
        srel.r_value = funcsym_p->Slocalgotoffset + NPTRSIZE; // TODO: check funcsym_p->Slocalgotoffset
        pseg->SDrel->write(&srel, sizeof(srel));
    }
    else
    {
        relocation_info rel;
        rel.r_address = offset;
        rel.r_symbolnum = targseg;
        rel.r_pcrel = (rtype == RELaddr) ? 0 : 1;
        rel.r_length = I64 ? 3 : 2;
        rel.r_extern = 0;
        rel.r_type = I64 ? X86_64_RELOC_UNSIGNED : GENERIC_RELOC_VANILLA;
        // relative: value += targseg.addr - seg.addr; section address patched later
        if (rel.r_pcrel)
        {
        }
        // absolute: value += targseg.addr; section address patched later
        else
        {
        }
        pseg->SDrel->write(&rel, sizeof(rel));
    }
}

/**
 * Write relocations for a segment to object file.
 * Params:
 *   seg = the segment for which to write relocations
 *   sym_map = mapping for renumbered symbol indices
 *   buf = output buffer to write the relocations to
 * Returns:
 *   The number of bytes written
 */
static void writeRelocations(int seg, const IDXSYM *sym_map, Outbuffer *buf)
{
    seg_data *pseg = SegData[seg];
    const unsigned nreloc = pseg->SDrel ? pseg->SDrel->size() / sizeof(relocation_info) : 0;
    if (!nreloc)
        return;

    if (I64)
        SecHdrTab64[MAP_SEG2SECIDX(seg)].reloff = buf->size();
    else
        SecHdrTab[MAP_SEG2SECIDX(seg)].reloff = buf->size();

    relocation_info *r = (relocation_info *)pseg->SDrel->buf;

    for (size_t i = 0; i < nreloc; ++i)
    {
        if (r[i].r_address & R_SCATTERED)
        {
            assert(0);
            scattered_relocation_info *sr = (scattered_relocation_info *)r; // same size as relocation_info
            assert(sr[i].r_type == GENERIC_RELOC_LOCAL_SECTDIFF);
            assert(sr[i + 1].r_type == GENERIC_RELOC_PAIR);
            IDXSYM targseg = sr[i + 1].r_address; // HACK: targseg temporarily stored in unused r_address
            sr[i + 1].r_address = 0;

            // absolute: targseg.addr + value; segment address patched later
            // absolute: seg.addr + func.Slocalgotoffset + NPTRSIZE; section address patched later
            if (I64)
            {
                sr[i].r_value += SecHdrTab64[MAP_SEG2SECIDX(targseg)].addr;
                sr[i + 1].r_value += SecHdrTab64[MAP_SEG2SECIDX(seg)].addr;
            }
            else
            {
                sr[i].r_value += SecHdrTab[MAP_SEG2SECIDX(targseg)].addr;
                sr[i + 1].r_value += SecHdrTab64[MAP_SEG2SECIDX(seg)].addr;
            }
            buf->write(&sr[i], 2 * sizeof(sr[i]));
            ++i; // for the pair
        }
        else if (r[i].r_extern)
        {
            // relative to symbol, doesn't need any section address
            r[i].r_symbolnum = sym_map[r[i].r_symbolnum]; // remap symbol index
            buf->write(&r[i], sizeof(r[i]));
        }
        else
        {
            IDXSYM targseg = r[i].r_symbolnum; // contains target section when r_extern == 0
            if (I64)
            {
                int32_t *p = patchAddr64(seg, r[i].r_address);
                *p += SecHdrTab64[MAP_SEG2SECIDX(targseg)].addr; // += targseg.addr
                if (r[i].r_pcrel)
                    *p -= SecHdrTab64[MAP_SEG2SECIDX(seg)].addr; // -= seg.addr
            }
            else
            {
                int32_t *p = patchAddr(seg, r[i].r_address);
                *p += SecHdrTab[MAP_SEG2SECIDX(targseg)].addr; // += targseg.addr
                if (r[i].r_pcrel)
                    *p -= SecHdrTab[MAP_SEG2SECIDX(seg)].addr; // -= seg.addr
            }
            buf->write(&r[i], sizeof(r[i]));
        }
    }

    if (I64)
        SecHdrTab64[MAP_SEG2SECIDX(seg)].nreloc = nreloc;
    else
        SecHdrTab[MAP_SEG2SECIDX(seg)].nreloc = nreloc;
}

/*******************************
 * Refer to address that is in the data segment.
 * Input:
 *      seg:offset =    the address being fixed up
 *      val =           displacement from start of target segment
 *      targetdatum =   target segment number (DATA, CDATA or UDATA, etc.)
 *      flags =         CFoff, CFseg
 * Example:
 *      int *abc = &def[3];
 *      to allocate storage:
 *              Obj::reftodatseg(DATA,offset,3 * sizeof(int *),UDATA);
 */

void Obj::reftodatseg(int seg,targ_size_t offset,targ_size_t val,
        unsigned targetdatum,int flags)
{
    Outbuffer *buf = SegData[seg]->SDbuf;
    int save = buf->size();
    buf->setsize(offset);
#if 0
    printf("Obj::reftodatseg(seg:offset=%d:x%llx, val=x%llx, targetdatum %x, flags %x )\n",
        seg,offset,val,targetdatum,flags);
#endif
    assert(seg != 0);
    if (SegData[seg]->isCode() && SegData[targetdatum]->isCode())
    {
        assert(0);
    }
    MachObj::addrel(seg, offset, NULL, targetdatum, RELaddr);
    if (I64)
    {
        if (flags & CFoffset64)
        {
            buf->write64(val);
            if (save > offset + 8)
                buf->setsize(save);
            return;
        }
    }
    buf->write32(val);
    if (save > offset + 4)
        buf->setsize(save);
}

/*******************************
 * Refer to address that is in the current function code (funcsym_p).
 * Only offsets are output, regardless of the memory model.
 * Used to put values in switch address tables.
 * Input:
 *      seg =           where the address is going (CODE or DATA)
 *      offset =        offset within seg
 *      val =           displacement from start of this module
 */

void Obj::reftocodeseg(int seg,targ_size_t offset,targ_size_t val)
{
    //printf("Obj::reftocodeseg(seg=%d, offset=x%lx, val=x%lx )\n",seg,(unsigned long)offset,(unsigned long)val);
    assert(seg > 0);
    Outbuffer *buf = SegData[seg]->SDbuf;
    int save = buf->size();
    buf->setsize(offset);
    val -= funcsym_p->Soffset;
    MachObj::addrel(seg, offset, funcsym_p, 0, RELaddr);
//    if (I64)
//        buf->write64(val);
//    else
        buf->write32(val);
    if (save > offset + 4)
        buf->setsize(save);
}

/*******************************
 * Refer to an identifier.
 * Input:
 *      seg =   where the address is going (CODE or DATA)
 *      offset =        offset within seg
 *      s ->            Symbol table entry for identifier
 *      val =           displacement from identifier
 *      flags =         CFselfrel: self-relative
 *                      CFseg: get segment
 *                      CFoff: get offset
 *                      CFpc32: [RIP] addressing, val is 0, -1, -2 or -4
 *                      CFoffset64: 8 byte offset for 64 bit builds
 * Returns:
 *      number of bytes in reference (4 or 8)
 */

int Obj::reftoident(int seg, targ_size_t offset, Symbol *s, targ_size_t val,
        int flags)
{
    int retsize = (flags & CFoffset64) ? 8 : 4;
#if 0
    dbg_printf("\nObj::reftoident('%s' seg %d, offset x%llx, val x%llx, flags x%x)\n",
        s->Sident,seg,(unsigned long long)offset,(unsigned long long)val,flags);
    printf("retsize = %d\n", retsize);
    //dbg_printf("Sseg = %d, Sxtrnnum = %d\n",s->Sseg,s->Sxtrnnum);
    symbol_print(s);
#endif
    assert(seg > 0);
    if (s->Sclass != SClocstat && !s->Sxtrnnum)
    {   // It may get defined later as public or local, so defer
        size_t numbyteswritten = addtofixlist(s, offset, seg, val, flags);
        assert(numbyteswritten == retsize);
    }
    else
    {
        if (I64)
        {
            //if (s->Sclass != SCcomdat)
                //val += s->Soffset;
            int v = 0;
            if (flags & CFpc32)
                v = (int)val;
            if (flags & CFselfrel)
            {
                MachObj::addrel(seg, offset, s, 0, RELrel, v);
            }
            else
            {
                MachObj::addrel(seg, offset, s, 0, RELaddr, v);
            }
        }
        else
        {
            if (SegData[seg]->isCode() && flags & CFselfrel)
            {
                if (!jumpTableSeg)
                {
                    jumpTableSeg =
                        MachObj::getsegment("__jump_table", "__IMPORT",  0, S_SYMBOL_STUBS | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS | S_ATTR_SELF_MODIFYING_CODE);
                }
                seg_data *pseg = SegData[jumpTableSeg];
                if (I64)
                    SecHdrTab64[pseg->SDshtidx].reserved2 = 5;
                else
                    SecHdrTab[pseg->SDshtidx].reserved2 = 5;

                if (!indirectsymbuf1)
                    indirectsymbuf1 = new Outbuffer();
                else
                {
                    // Look through indirectsym to see if it is already there
                    IDXSYM cnt = indirectsymbuf1->size() / sizeof(IDXSYM);
                    IDXSYM *psyms = (IDXSYM *)indirectsymbuf1->buf;
                    for (IDXSYM i = 0; i < cnt; ++i)
                    {
                        if (psyms[i] == s->Sxtrnnum)
                        {
                            val = i * 5;
                            goto L1;
                        }
                    }
                }

                val = pseg->SDbuf->size();
                static char halts[5] = { 0xF4,0xF4,0xF4,0xF4,0xF4 };
                pseg->SDbuf->write(halts, 5);

                // Add symbol index to indirectsymbuf1
                indirectsymbuf1->write32(s->Sxtrnnum);
             L1:
                val -= offset + 4;
                MachObj::addrel(seg, offset, NULL, jumpTableSeg, RELrel);
            }
            else if (SegData[seg]->isCode() &&
                    ((s->Sclass != SCextern && SegData[s->Sseg]->isCode()) || s->Sclass == SClocstat || s->Sclass == SCstatic))
            {
                val += s->Soffset;
                MachObj::addrel(seg, offset, NULL, s->Sseg, RELaddr);
            }
            else if (SegData[seg]->isCode() && !tyfunc(s->ty()))
            {
                if (!pointersSeg)
                {
                    pointersSeg =
                        MachObj::getsegment("__pointers", "__IMPORT",  0, S_NON_LAZY_SYMBOL_POINTERS);
                }
                seg_data *pseg = SegData[pointersSeg];

                if (!indirectsymbuf2)
                    indirectsymbuf2 = new Outbuffer();
                else
                {
                    // Look through indirectsym to see if it is already there
                    IDXSYM cnt = indirectsymbuf2->size() / sizeof(IDXSYM);
                    IDXSYM *psyms = (IDXSYM *)indirectsymbuf2->buf;
                    for (IDXSYM i = 0; i < cnt; ++i)
                    {
                        if (psyms[i] == s->Sxtrnnum)
                        {
                            val = i * 4;
                            goto L2;
                        }
                    }
                }

                val = pseg->SDbuf->size();
                pseg->SDbuf->writezeros(NPTRSIZE);

                // Add symbol index to indirectsymbuf2
                indirectsymbuf2->write32(s->Sxtrnnum);

             L2:
                //printf("Obj::reftoident: seg = %d, offset = x%x, s = %s, val = x%x, pointersSeg = %d\n", seg, offset, s->Sident, val, pointersSeg);
                MachObj::addrel(seg, offset, NULL, pointersSeg, RELaddr);
            }
            else
            {   //val -= s->Soffset;
                MachObj::addrel(seg, offset, s, 0, RELaddr);
            }
        }

        Outbuffer *buf = SegData[seg]->SDbuf;
        int save = buf->size();
        buf->setsize(offset);
        //printf("offset = x%llx, val = x%llx\n", offset, val);
        if (retsize == 8)
            buf->write64(val);
        else
            buf->write32(val);
        if (save > offset + retsize)
            buf->setsize(save);
    }
    return retsize;
}

/*****************************************
 * Generate far16 thunk.
 * Input:
 *      s       Symbol to generate a thunk for
 */

void Obj::far16thunk(Symbol *s)
{
    //dbg_printf("Obj::far16thunk('%s')\n", s->Sident);
    assert(0);
}

/**************************************
 * Mark object file as using floating point.
 */

void Obj::fltused()
{
    //dbg_printf("Obj::fltused()\n");
}

/************************************
 * Close and delete .OBJ file.
 */

void objfile_delete()
{
    //remove(fobjname); // delete corrupt output file
}

/**********************************
 * Terminate.
 */

void objfile_term()
{
#if TERMCODE
    mem_free(fobjname);
    fobjname = NULL;
#endif
}

/**********************************
  * Write to the object file
  */
void objfile_write(FILE *fd, void *buffer, unsigned len)
{
    fobjbuf->write(buffer, len);
}

long elf_align(targ_size_t size, long foffset)
{
    if (size <= 1)
        return foffset;
    long offset = (foffset + size - 1) & ~(size - 1);
    if (offset > foffset)
        fobjbuf->writezeros(offset - foffset);
    return offset;
}

/***************************************
 * Stuff pointer to ModuleInfo in its own segment.
 */

#if MARS

void Obj::moduleinfo(Symbol *scc)
{
    int align = I64 ? 3 : 2; // align to NPTRSIZE

    int seg = MachObj::getsegment("__minfodata", "__DATA", align, S_REGULAR);
    //printf("Obj::moduleinfo(%s) seg = %d:x%x\n", scc->Sident, seg, Offset(seg));

#if 0
    type *t = type_fake(TYint);
    t->Tmangle = mTYman_c;
    char *p = (char *)malloc(5 + strlen(scc->Sident) + 1);
    strcpy(p, "SUPER");
    strcpy(p + 5, scc->Sident);
    symbol *s_minfo_beg = symbol_name(p, SCglobal, t);
    Obj::pubdef(seg, s_minfo_beg, 0);
#endif

    int flags = CFoff;
    if (I64)
        flags |= CFoffset64;
    SegData[seg]->SDoffset += Obj::reftoident(seg, Offset(seg), scc, 0, flags);
}

#endif

/*************************************
 */

void Obj::gotref(symbol *s)
{
    //printf("Obj::gotref(%x '%s', %d)\n",s,s->Sident, s->Sclass);
    switch(s->Sclass)
    {
        case SCstatic:
        case SClocstat:
            s->Sfl = FLgotoff;
            break;

        case SCextern:
        case SCglobal:
        case SCcomdat:
        case SCcomdef:
            s->Sfl = FLgot;
            break;

        default:
            break;
    }
}

#endif
#endif
