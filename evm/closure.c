#include "closure.h"
#include "emalloc.h"

#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>

VAL one;
VAL* zcon;
int v_argc;
VAL* v_argv;
VMState* vm;

extern func _do___U__main();

void epicMemInfo();

ALLOCATOR allocate;
REALLOCATOR reallocate;
pool_t** pools = NULL;
pool_t* pool = NULL;

//void* blob = NULL;
//int blobnext = 0;

/*void* FASTMALLOC(int size) {
    if (blob == NULL) { blob = malloc(10001000); }
    void* newblock = blob+blobnext;
    blobnext+=((size+4) & 0xfffffffc);
    if (blobnext>10000000) blobnext=0;
    return newblock;
    }*/

void dumpClosureA(Closure* c, int rec);

void dumpCon(con* c, int rec) {
    int x,arity;
    if (!rec) { printf("TAG(%d)", c->tag & 65535); }

    arity = c->tag >> 16;
    if (arity>0 && !rec) { printf(": "); }

    for(x=0; x<arity; ++x) {
	dumpClosureA(c->args[x], rec);
	if (x!=(arity-1)) { printf(", "); }
    }
}

void dumpRecord(Closure* r) {
    dumpClosureA(r, 1);
}

void dumpClosureA(Closure* c, int rec) {
    c = DO_EVAL(c,0);
    switch(GETTY(c)) {
    case FUN:
	printf("FUN[");
	break;
    case THUNK:
	printf("THUNK[");
	break;
    case CON:
	if (!rec) { printf("CON["); } else { printf("["); }
	dumpCon((con*)c->info, rec);
	break;
    case INT:
	if (!rec) { printf("INT[%ld", ((eint)c)>>1); } else { printf("[%ld", ((eint)c)>>1); }
	break;
    case BIGINT:
	printf("BIGINT[");
	break;
    case FLOAT:
	printf("FLOAT[");
	break;
    case BIGFLOAT:
	printf("BIGFLOAT[");
	break;
    case STRING:
	printf("STRING[%s", ((char*)c->info));
	break;
    case UNIT:
	printf("UNIT[");
	break;
    case PTR:
	printf("PTR[");
	break;
    case FREEVAR:
	printf("FREEVAR[");
	break;
    default:
	printf("[%d,%ld", GETTY(c), (eint)c->info);
    }
    printf("]");
}

void dumpClosure(Closure* c) {
    dumpClosureA(c,0);
    printf("\n");
}

void assertConR(Closure* c) 
{
    if (c==NULL) { printf("Null constructor\n"); assert(0); }
    if (!ISCON(c)) { dumpClosure(c); assert(0); }
}

void assertIntR(Closure* c) 
{
    if (!ISINT(c)) { dumpClosure(c); assert(0); }
}

void* pool_malloc(size_t size) {
    if ((size & 7)!=0) {
	size = 8 + ((size >> 3) << 3);
    }
    *((size_t*)(pool->block_loc)) = size;
    void* mem = (void*)(((size_t*)(pool->block_loc))+2);
    pool->block_loc = pool->block_loc+size+sizeof(size_t)*2;

    return mem;
}

void* pool_realloc(void* ptr, size_t size) {
    if ((size & 7)!=0) {
	size = 8 + ((size >> 3) << 3);
    }
    *((size_t*)(pool->block_loc)) = size;
    void* mem = (void*)(((size_t*)(pool->block_loc))+2);
    pool->block_loc = pool->block_loc+size+sizeof(size_t)*2;

    size_t orig_size = *(((size_t*)ptr)-2);
    memcpy(mem, ptr, orig_size);

    return mem;
}

void* pool_grow_malloc(size_t size) {
    // TODO: if we're out of space, make a new pool, with a pointer to
    // the old pool so we can free it when we're ready.

    if ((size & 7)!=0) {
	size = 8 + ((size >> 3) << 3);
    }
    *((size_t*)(pool->block_loc)) = size;
    void* mem = (void*)(((size_t*)(pool->block_loc))+2);
    pool->block_loc = pool->block_loc+size+sizeof(size_t)*2;

    return mem;
}

void* pool_grow_realloc(void* ptr, size_t size) {
    if ((size & 7)!=0) {
	size = 8 + ((size >> 3) << 3);
    }
    *((size_t*)(pool->block_loc)) = size;
    void* mem = (void*)(((size_t*)(pool->block_loc))+2);
    pool->block_loc = pool->block_loc+size+sizeof(size_t)*2;

    size_t orig_size = *(((size_t*)ptr)-2);
    memcpy(mem, ptr, orig_size);

    return mem;
}

void freePool(pool_t* pool)
{
    free(pool->block);
    if (pool->grow!=NULL) {
	freePool((pool_t*)(pool->grow));
    }
    free(pool);
}


VAL copyFun(fun* f, pool_t* oldpool) {
    VAL c = EMALLOC(sizeof(Closure)+sizeof(fun));
    fun* fn = (fun*)(c+1);
    fn->fn = f->fn;
    fn->arity = f->arity;
    int args = f->arg_end - f->args;
    fn->args = MKARGS(args);
    fn->arg_end = fn->args + args;
    void** p = fn->args;
    void** a;

    for(a = f->args; a < f->arg_end; ++a, ++p) {
	*p = copy((VAL)(*a), oldpool);
    }
    
    SETTY(c, FUN);
    c->info = (void*)fn;
    EREADY(c);
    return c;
}

VAL copyThunk(thunk* t, pool_t* oldpool) {
    VAL c = EMALLOC(sizeof(Closure)+sizeof(fun));
    thunk* fn = (thunk*)(c+1);
    
    fn->fn = t->fn;
    fn->args = MKARGS(t->numargs);
    fn->numargs = t->numargs;

    void** a = t->args;
    void** p = fn->args;
    int i;

    for(i=0; i < t->numargs; ++i, ++a, ++p) {
	*p = copy((VAL)(*a), oldpool);
    }

    SETTY(c,THUNK);
    c->info = (void*)fn;
    EREADY(c);
    return c;
}

VAL copyCon(con* c, pool_t* oldpool) {
    int arity = c->tag >> 16;
//    printf("COPY CON %d %d\n", c->tag & 65535, arity);

    VAL nc = EMALLOC(sizeof(Closure)+sizeof(con));
    con* cn = (con*)(nc+1);

    cn->tag = c->tag;
    cn->args = MKARGS(arity);
    
    void** a = c->args;
    void** p = cn->args;
    int i;

    for(i=0; i<arity; ++i, ++a, ++p) {
//	printf("COPY ARG %d\n", *a);
	*p = copy((VAL)(*a), oldpool);
    }

    SETTY(nc, CON);
    nc->info = (void*)cn;
    EREADY(nc);
    return nc;
}


// TODO: Preserve sharing. But this function isn't really intended for that
// sort of thing.

VAL copy(VAL x, pool_t* oldpool) {
    // only copy things that were allocated in the given pool.
    // TODO: also need to check whether it was allocated in pool->grow

    if (x>=(VAL)(oldpool->block) && x<(VAL)(oldpool->block_end)) {
	switch(GETTY(x)) {
	case FUN:
	    return copyFun((fun*)x->info, oldpool);
	case THUNK:
	    return copyThunk((thunk*)x->info, oldpool);
	case CON:
	    return copyCon((con*)x->info, oldpool);
	case INT:
	    return x;
	case BIGINT:
	    return MKBIGINT((mpz_t*)(x->info));
	case FLOAT:
	    return MKFLOAT(*((double*)x->info));
	case BIGFLOAT:
	    assert(0); // NOT IMPLEMENTED YET
	case STRING:
	    return MKSTR((char*)x->info);
	case UNIT:
	    return MKUNIT;
	case PTR:
	    return MKPTR(x->info);
	case FREEVAR:
	    assert(0); // NOT IMPLEMENTED
	}
	return x;
    }
    else {
	return x;
    }
}

/// "Promoting" is copying a value on the stack to the heap.
/// Just like copying, except we leave it alone if it's already on the heap.
/// (whether it's on the heap is a flag in the ty field)

VAL promoteFun(fun* f) {
    VAL c = EMALLOC(sizeof(Closure)+sizeof(fun));
    fun* fn = (fun*)(c+1);
    fn->fn = f->fn;
    fn->arity = f->arity;
    int args = f->arg_end - f->args;
    fn->args = MKARGS(args);
    fn->arg_end = fn->args + args;
    void** p = fn->args;
    void** a;

    for(a = f->args; a < f->arg_end; ++a, ++p) {
	*p = promote((VAL)(*a));
    }
    
    SETTY(c, FUN);
    c->info = (void*)fn;
    EREADY(c);
    return c;
}

VAL promoteThunk(thunk* t) {
    VAL c = EMALLOC(sizeof(Closure)+sizeof(fun));
    thunk* fn = (thunk*)(c+1);
    
    fn->fn = t->fn;
    fn->args = MKARGS(t->numargs);
    fn->numargs = t->numargs;

    void** a = t->args;
    void** p = fn->args;
    int i;

    for(i=0; i < t->numargs; ++i, ++a, ++p) {
	*p = promote((VAL)(*a));
    }

    SETTY(c,THUNK);
    c->info = (void*)fn;
    EREADY(c);
    return c;
}

VAL promoteCon(con* c) {
    int arity = c->tag >> 16;
//    printf("COPY CON %d %d\n", c->tag & 65535, arity);

    VAL nc = EMALLOC(sizeof(Closure)+sizeof(con));
    con* cn = (con*)(nc+1);

    cn->tag = c->tag;
    cn->args = MKARGS(arity);
    
    void** a = c->args;
    void** p = cn->args;
    int i;

    for(i=0; i<arity; ++i, ++a, ++p) {
//	printf("COPY ARG %d\n", *a);
	*p = promote((VAL)(*a));
    }

    SETTY(nc, CON);
    nc->info = (void*)cn;
    EREADY(nc);
    return nc;
}

// TODO: Make sure we preserve sharing!

VAL promote(VAL x) {

    if (x && !ISINT(x) && ON_STK(x)) {
	switch(GETTY(x)) {
	case FUN:
	    return promoteFun((fun*)x->info);
	case THUNK:
	    return promoteThunk((thunk*)x->info);
	case CON:
	    return promoteCon((con*)x->info);
	case INT:
	    return x;
	case BIGINT:
	    return MKBIGINT((mpz_t*)(x->info));
	case FLOAT:
	    return MKFLOAT(*((double*)x->info));
	case BIGFLOAT:
	    assert(0); // NOT IMPLEMENTED YET
	case STRING:
	    return MKSTR((char*)x->info);
	case UNIT:
	    return MKUNIT;
	case PTR:
	    return MKPTR(x->info);
	case FREEVAR:
	    assert(0); // NOT IMPLEMENTED
	}
	return x;
    }
    else {
	return x;
    }
}

inline VAL CLOSURE(func x, int arity, int args, void** block)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(fun)); // MKCLOSURE;
    fun* fn = (fun*)(c+1);
    fn->fn = x;
    fn->arity = arity;
    if (args==0) {
	fn->args = 0;
	fn->arg_end = 0;
    } else {
	fn->args = MKARGS(args);
	fn->arg_end=fn->args+args;
	memcpy((void*)(fn->args), (void*)block, args*sizeof(VAL));
    }

    SETTY(c, FUN);
    c->info = (void*)fn;
    EREADY(c);
    return c;
}

inline VAL CONSTRUCTORn(int tag, int arity, void** block)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(con)); // MKCLOSURE;
    con* cn = (con*)(c+1);
    cn->tag = tag + (arity << 16);
    if (arity==0) {
	cn->args = 0;
    } else {
	cn->args = MKARGS(arity);
	memcpy((void*)(cn->args), (void*)block, arity*sizeof(VAL));
    }
    SETTY(c, CON);
    c->info = (void*)cn;
    EREADY(c);
    return c;
}

inline VAL CONSTRUCTOR1(int tag, VAL a1)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(con)+sizeof(VAL)); // MKCLOSURE;
    con* cn = (con*)(c+1);
    cn->tag = tag + (1 << 16);
    cn->args = (void*)c+sizeof(Closure)+sizeof(con); // MKARGS(1);
    cn->args[0] = a1;
    SETTY(c,CON);
    c->info = (void*)cn;
    EREADY(c);
    return c;
}

inline VAL CONSTRUCTOR2(int tag, VAL a1, VAL a2)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(con)+2*sizeof(VAL)); // MKCLOSURE;
    con* cn = (con*)(c+1);
    cn->tag = tag + (2 << 16);
    cn->args = (void*)c+sizeof(Closure)+sizeof(con); //MKARGS(2);
    cn->args[0] = a1;
    cn->args[1] = a2;
    SETTY(c,CON);
    c->info = (void*)cn;
    EREADY(c);

    return c;
}

inline VAL CONSTRUCTOR3(int tag, VAL a1, VAL a2, VAL a3)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(con)+3*sizeof(VAL)); // MKCLOSURE;
    con* cn = (con*)(c+1);
    cn->tag = tag + (3 << 16);
    cn->args = (void*)c+sizeof(Closure)+sizeof(con); //MKARGS(3);
    cn->args[0] = a1;
    cn->args[1] = a2;
    cn->args[2] = a3;
    SETTY(c,CON);
    c->info = (void*)cn;
    EREADY(c);
    return c;
}

inline VAL CONSTRUCTOR4(int tag, VAL a1, VAL a2, VAL a3, VAL a4)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(con)+4*sizeof(VAL)); // MKCLOSURE;
    con* cn = (con*)(c+1);
    cn->tag = tag + (4 << 16);
    cn->args = (void*)c+sizeof(Closure)+sizeof(con); //MKARGS(2);
    cn->args[0] = a1;
    cn->args[1] = a2;
    cn->args[2] = a3;
    cn->args[3] = a4;
    SETTY(c,CON);
    c->info = (void*)cn;
    EREADY(c);
    return c;
}

inline VAL CONSTRUCTOR5(int tag, VAL a1, VAL a2, VAL a3, VAL a4, VAL a5)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(con)+5*sizeof(VAL)); // MKCLOSURE;
    con* cn = (con*)(c+1);
    cn->tag = tag + (5 << 16);
    cn->args = (void*)c+sizeof(Closure)+sizeof(con); //MKARGS(5);
    cn->args[0] = a1;
    cn->args[1] = a2;
    cn->args[2] = a3;
    cn->args[3] = a4;
    cn->args[4] = a5;
    SETTY(c,CON);
    c->info = (void*)cn;
    EREADY(c);
    return c;
}

// This needs to make a copy
inline VAL CLOSURE_ADDN(VAL xin, int args, void** block)
{
    assert(GETTY(xin) == FUN);

    fun* finf = (fun*)xin->info;

    VAL x = CLOSURE(finf->fn, finf->arity, 
		    finf->arg_end-finf->args, finf->args);

    fun* fn = (fun*)(x->info);
    int diff = fn->arg_end - fn->args;

    fn->args = MOREARGS(fn->args, args + diff);
    fn->arg_end = fn->args + diff;

    memcpy((void*)(fn->arg_end), (void*)block, args*sizeof(VAL));
    fn->arg_end += args;
    return x;
}

/*
VAL CLOSURE_ADDN(VAL xin, int args, void** block)
{
    switch(args) {
    case 1: return CLOSURE_ADD1(xin,block[0]);
    case 2: return CLOSURE_ADD2(xin,block[0],block[1]);
    case 3: return CLOSURE_ADD3(xin,block[0],block[1],block[2]);
    case 4: return CLOSURE_ADD4(xin,block[0],block[1],block[2],block[3]);
    case 5: return CLOSURE_ADD5(xin,block[0],block[1],block[2],block[3],block[4]);
    default: return aux_CLOSURE_ADDN(xin,args,block);
    }
}
*/

inline VAL CLOSURE_ADD1(VAL xin, VAL a1)
{
    assert(GETTY(xin)==FUN);

    fun* finf = (fun*)xin->info;

    VAL x = CLOSURE(finf->fn, finf->arity, 
		    finf->arg_end-finf->args, finf->args);

    fun* fn = (fun*)(x->info);
    int diff = fn->arg_end - fn->args;

    fn->args = MOREARGS(fn->args, diff + 1);
    fn->arg_end = fn->args + diff;
    fn->arg_end[0] = a1;
    fn->arg_end+=1;

    return x;
}

inline VAL CLOSURE_ADD2(VAL xin, VAL a1, VAL a2)
{
    assert(GETTY(xin)==FUN);

    fun* finf = (fun*)xin->info;

    VAL x = CLOSURE(finf->fn, finf->arity, 
		    finf->arg_end-finf->args, finf->args);

    fun* fn = (fun*)(x->info);
    int diff = fn->arg_end - fn->args;

    fn->args = MOREARGS(fn->args, diff + 2);
    fn->arg_end = fn->args + diff;
    fn->arg_end[0] = a1;
    fn->arg_end[1] = a2;
    fn->arg_end+=2;

    return x;
}

inline VAL CLOSURE_ADD3(VAL xin, VAL a1, VAL a2, VAL a3)
{
    assert(GETTY(xin)==FUN);

    fun* finf = (fun*)xin->info;

    VAL x = CLOSURE(finf->fn, finf->arity, 
		    finf->arg_end-finf->args, finf->args);

    fun* fn = (fun*)(x->info);
    int diff = fn->arg_end - fn->args;

    fn->args = MOREARGS(fn->args, diff + 3);
    fn->arg_end = fn->args + diff;
    fn->arg_end[0] = a1;
    fn->arg_end[1] = a2;
    fn->arg_end[2] = a3;
    fn->arg_end+=3;

    return x;
}

inline VAL CLOSURE_ADD4(VAL xin, VAL a1, VAL a2, VAL a3, VAL a4)
{
    assert(GETTY(xin)==FUN);

    fun* finf = (fun*)xin->info;

    VAL x = CLOSURE(finf->fn, finf->arity, 
		    finf->arg_end-finf->args, finf->args);

    fun* fn = (fun*)(x->info);
    int diff = fn->arg_end - fn->args;

    fn->args = MOREARGS(fn->args, diff + 4);
    fn->arg_end = fn->args + diff;
    fn->arg_end[0] = a1;
    fn->arg_end[1] = a2;
    fn->arg_end[2] = a3;
    fn->arg_end[3] = a4;
    fn->arg_end+=4;

    return x;
}

inline VAL CLOSURE_ADD5(VAL xin, VAL a1, VAL a2, VAL a3, VAL a4, VAL a5)
{
    assert(GETTY(xin)==FUN);

    fun* finf = (fun*)xin->info;

    VAL x = CLOSURE(finf->fn, finf->arity, 
		    finf->arg_end-finf->args, finf->args);

    fun* fn = (fun*)(x->info);
    int diff = fn->arg_end - fn->args;

    fn->args = MOREARGS(fn->args, diff + 5);
    fn->arg_end = fn->args + diff;
    fn->arg_end[0] = a1;
    fn->arg_end[1] = a2;
    fn->arg_end[2] = a3;
    fn->arg_end[3] = a4;
    fn->arg_end[4] = a5;
    fn->arg_end+=5;

    return x;
}

inline VAL CLOSURE_APPLY(VAL f, int args, void** block)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(thunk)); // MKCLOSURE;
    thunk* fn = (thunk*)(c+1);

    if (ISFUN(f)) {
	return CLOSURE_ADDN(f,args,block);
    }

    fn->fn = (void*)f;
    fn->numargs = args;
    if (args==0) {
	fn->args = 0;
    } else {
	fn->args = MKARGS(args);
	memcpy((void*)(fn->args), (void*)block, args*sizeof(VAL));
    }

    SETTY(c,THUNK);
    c->info = (void*)fn;
    EREADY(c);
    return c;
}

inline VAL aux_CLOSURE_APPLY1(VAL f, VAL a1)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(thunk)); // MKCLOSURE;
    thunk* fn = (thunk*)(c+1);

    if (ISFUN(f)) {
	return CLOSURE_ADD1(f,a1);
    }

    fn->fn = (void*)f;
    fn->numargs = 1;
    fn->args = MKARGS(1);
    fn->args[0] = a1;

    SETTY(c,THUNK);
    c->info = (void*)fn;
    EREADY(c);
    return c;
}

inline VAL aux_CLOSURE_APPLY2(VAL f, VAL a1, VAL a2)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(thunk)); // MKCLOSURE;
    thunk* fn = (thunk*)(c+1);

    if (ISFUN(f)) {
	return NULL; //CLOSURE_ADD2(f,a1,a2);
    }

    fn->fn = (void*)f;
    fn->numargs = 2;
    fn->args = MKARGS(2);
    fn->args[0] = a1;
    fn->args[1] = a2;

    SETTY(c,THUNK);
    c->info = (void*)fn;
    EREADY(c);
    return c;
}

inline VAL aux_CLOSURE_APPLY3(VAL f, VAL a1, VAL a2, VAL a3)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(thunk)); // MKCLOSURE;
    thunk* fn = (thunk*)(c+1);

    if (ISFUN(f)) {
	return CLOSURE_ADD3(f,a1,a2,a3);
    }

    fn->fn = (void*)f;
    fn->numargs = 2;
    fn->args = MKARGS(3);
    fn->args[0] = a1;
    fn->args[1] = a2;
    fn->args[2] = a3;

    SETTY(c,THUNK);
    c->info = (void*)fn;
    EREADY(c);
    return c;
}

inline VAL aux_CLOSURE_APPLY4(VAL f, VAL a1, VAL a2, VAL a3, VAL a4)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(thunk)); // MKCLOSURE;
    thunk* fn = (thunk*)(c+1);

    if (ISFUN(f)) {
	return CLOSURE_ADD4(f,a1,a2,a3,a4);
    }

    fn->fn = (void*)f;
    fn->numargs = 2;
    fn->args = MKARGS(4);
    fn->args[0] = a1;
    fn->args[1] = a2;
    fn->args[2] = a3;
    fn->args[3] = a4;

    SETTY(c,THUNK);
    c->info = (void*)fn;
    EREADY(c);
    return c;
}

inline VAL aux_CLOSURE_APPLY5(VAL f, VAL a1, VAL a2, VAL a3, VAL a4, VAL a5)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(thunk)); // MKCLOSURE;
    thunk* fn = (thunk*)(c+1);

    if (ISFUN(f)) {
	return CLOSURE_ADD5(f,a1,a2,a3,a4,a5);
    }

    fn->fn = (void*)f;
    fn->numargs = 2;
    fn->args = MKARGS(5);
    fn->args[0] = a1;
    fn->args[1] = a2;
    fn->args[2] = a3;
    fn->args[3] = a4;
    fn->args[4] = a5;

    SETTY(c,THUNK);
    c->info = (void*)fn;
    EREADY(c);
    return c;
}

inline VAL CLOSURE_APPLY1(VAL f, VAL a1)
{
    if (ISFUN(f)) {
	fun* finf = (fun*)(f->info);
	int got = finf->arg_end-finf->args;
	if (finf->arity == (got+1)) {
	    void* block[got+1];
	    memcpy(block, finf->args, got*sizeof(VAL));
	    block[got] = a1;
	    return (VAL)(finf->fn(block));
	}
	else if (finf->arity < (got+1)) {
	    return (VAL) DO_EVAL(CLOSURE_ADD1(f,a1), 0);
	}	else return CLOSURE_ADD1(f,a1);
    }
    else return aux_CLOSURE_APPLY1(f,a1);
}

void* block[1024]; // Yes. I know. Better check below that this is big enough.

inline VAL CLOSURE_APPLY2(VAL f, VAL a1, VAL a2)
{
    int i;
    if (ISFUN(f)) {
	fun* finf = (fun*)(f->info);
	int got = finf->arg_end-finf->args;
	if (finf->arity == (got+2)) {
//	    memcpy(block, finf->args, got*sizeof(VAL));
	    for(i=0; i<got; ++i) {
		block[i] = finf->args[i];
	    }
	    block[got] = a1;
	    block[got+1] = a2;
	    return (VAL)(finf->fn(block));
	} else if (finf->arity < (got+2)) {
	    return (VAL) DO_EVAL(CLOSURE_ADD2(f,a1,a2), 0);
	}	else return CLOSURE_ADD2(f,a1,a2);
    }
    else return aux_CLOSURE_APPLY2(f,a1,a2);
}

inline VAL CLOSURE_APPLY3(VAL f, VAL a1, VAL a2, VAL a3)
{
    if (ISFUN(f)) {
	fun* finf = (fun*)(f->info);
	int got = finf->arg_end-finf->args;
	if (finf->arity == (got+3)) {
	    void* block[got+3];
	    memcpy(block, finf->args, got*sizeof(VAL));
	    block[got] = a1;
	    block[got+1] = a2;
	    block[got+2] = a3;
	    return (VAL)(finf->fn(block));
	}
	else if (finf->arity < (got+3)) {
	    return (VAL) DO_EVAL(CLOSURE_ADD3(f,a1,a2,a3), 0);
	}	else return CLOSURE_ADD3(f,a1,a2,a3);
    }
    else return aux_CLOSURE_APPLY3(f,a1,a2,a3);
}

inline VAL CLOSURE_APPLY4(VAL f, VAL a1, VAL a2, VAL a3, VAL a4)
{
    if (ISFUN(f)) {
	fun* finf = (fun*)(f->info);
	int got = finf->arg_end-finf->args;
	if (finf->arity == (got+4)) {
	    void* block[got+4];
	    memcpy(block, finf->args, got*sizeof(VAL));
	    block[got] = a1;
	    block[got+1] = a2;
	    block[got+2] = a3;
	    block[got+3] = a4;
	    return (VAL)(finf->fn(block));
	}
	else if (finf->arity < (got+4)) {
	    return (VAL) DO_EVAL(CLOSURE_ADD4(f,a1,a2,a3,a4), 0);
	}	else return CLOSURE_ADD4(f,a1,a2,a3,a4);
    }
    else return aux_CLOSURE_APPLY4(f,a1,a2,a3,a4);
}

inline VAL CLOSURE_APPLY5(VAL f, VAL a1, VAL a2, VAL a3, VAL a4, VAL a5)
{
    if (ISFUN(f)) {
	fun* finf = (fun*)(f->info);
	int got = finf->arg_end-finf->args;
	if (finf->arity == (got+5)) {
	    void* block[got+5];
	    memcpy(block, finf->args, got*sizeof(VAL));
	    block[got] = a1;
	    block[got+1] = a2;
	    block[got+2] = a3;
	    block[got+3] = a4;
	    block[got+4] = a5;
	    return (VAL)(finf->fn(block));
	}
	else if (finf->arity < (got+5)) {
	    return (VAL) DO_EVAL(CLOSURE_ADD5(f,a1,a2,a3,a4,a5), 0);
	}	else return CLOSURE_ADD5(f,a1,a2,a3,a4,a5);
    }
    else return aux_CLOSURE_APPLY5(f,a1,a2,a3,a4,a5);
}

VAL DO_EVAL(VAL x, int update) {
// dummy value we'll never inspect, leave it alone.
    if (x==NULL) return x; 

    VAL result;
//    VAL x = (VAL)(*xin);
    fun* fn;
    thunk* th;
    int excess;

//    dumpClosure(x);

    switch(GETTY(x)) {
    case CON:
    case INT:
    case BIGINT:
    case FLOAT:
    case STRING:
    case PTR:
    case UNIT:
	return x; // Already evaluated
    case FUN:
	// If the number of arguments is right, run it.
	fn = (fun*)(x->info);
	excess = (fn->arg_end - fn->args) - fn->arity;
	if (excess == 0) {
	    result = fn->fn(fn->args);
	    // If the result is still a function, better eval again to make
	    // more progress.
	    // It could reasonably be null though, so be careful. It's null
	    // if it was a foreign/io call in particular.
	    if (result) {
		if (GETTY(result)==FUN || GETTY(result)==THUNK) {
		    result=DO_EVAL(result, update);
		}
/*		if (ISINT(result)) {
		    printf("Updating with %d\n", x);
		} else {
		    printf("Updating %d %d with %d\n", x, GETTY(x), result);
		    }*/
		if (update) { UPDATE(x,result); } else { return result; }
	    }
	    else {
		if (update) { SETTY(x, INT); x->info=(void*)42; } else { return NULL; }
	    }
	}
	// If there are too many arguments, run it with the right number
	// then apply the remaining arguments to the resulting closure
	else if (excess > 0) {
	    result = fn->fn(fn->args);
	    result = CLOSURE_APPLY(result, excess, fn->args + fn->arity);
	    result = DO_EVAL(result, update);
	    if (update) { UPDATE(x,result); } else { return result; }
	    return x;
	}
	break;
    case THUNK:
	th = (thunk*)(x->info);
	// Evaluate inner thunk, which should give us a function
	VAL nextfn = DO_EVAL((VAL)(th->fn), update);
	// Apply this thunk's arguments to it
	CLOSURE_APPLY((VAL)nextfn, th->numargs, th->args);
	// And off we go again...
	nextfn = DO_EVAL(nextfn, update);
	if (update) { UPDATE(x, nextfn); } else { return nextfn; }
	return x;
	break;
    default:
	assert(0); // Can't happen
    }
    EREADY(x);
    return x;
}

/*
void* DO_PROJECT(VAL x, int arg)
{
    assert(x->ty == CON);
    con* cn = (con*)x->info;
    return cn->args[arg];
}
*/

/*void* MKINT(int x)
{
    return (void*)((x<<1)+1);
//    VAL c = MKCLOSURE;
//    SETTY(c, INT);
//    c->info = (void*)x;
//    return c;
}*/

mpz_t* NEWBIGINTI(int val)
{
    mpz_t* bigint = EMALLOC(sizeof(mpz_t));
    mpz_init(*bigint);
    mpz_set_si(*bigint, val);
    return bigint;
}

void* NEWBIGINTVALI(int val)
{
    mpz_t* bigint;
    VAL c = EMALLOC(sizeof(Closure)+sizeof(mpz_t));
    bigint = (mpz_t*)(c+1);
    mpz_init(*bigint);
    mpz_set_si(*bigint, val);

    SETTY(c, BIGINT);
    c->info = (void*)bigint;
    EREADY(c);
    return c;
}

void* NEWBIGINT(char* intstr)
{
    mpz_t* bigint;
    VAL c = EMALLOC(sizeof(Closure)+sizeof(mpz_t));
    bigint = (mpz_t*)(c+1);
    mpz_init(*bigint);
    mpz_set_str(*bigint, intstr, 10);

    SETTY(c, BIGINT);
    c->info = (void*)bigint;
    EREADY(c);
    return c;
}

void* MKBIGINT(mpz_t* big)
{
    mpz_t* bigint;
    VAL c = EMALLOC(sizeof(Closure)+sizeof(mpz_t));
    bigint = (mpz_t*)(c+1);
    mpz_init(*bigint);
    mpz_set(*bigint, *big);

    SETTY(c, BIGINT);
    c->info = (void*)bigint;
    EREADY(c);
    return c;
}

void* MKFLOAT(double f)
{
    VAL c = EMALLOC(sizeof(Closure)+sizeof(double));
    double* num = (double*)(c+1);
    *num = f;

    SETTY(c, FLOAT);
    c->info = (void*)num;
    EREADY(c);

    return c;
}



/*
int GETINT(void* x)
{
    return ((eint)x)>>1;
}
*/

mpz_t* GETBIGINT(void* x)
{
    if (ISINT(x)) {
	return NEWBIGINTI(GETINT(x));
    } else {
	return (mpz_t*)(((VAL)x)->info);
    }
}

double GETFLOAT(void* x)
{
    return *((double*)(((VAL)x)->info));
}

void* MKSTR(const char* x)
{
//    VAL c = EMALLOC(sizeof(Closure)+strlen(x)+sizeof(char)+1); //MKCLOSURE;
    VAL c = EMALLOC(sizeof(Closure));
    SETTY(c, STRING);
//    c->info = ((void*)c)+sizeof(Closure);// (void*)(EMALLOC(strlen(x)*sizeof(char)+1));
//    strcpy(c->info,x);

// Since MKSTR is used to build strings from foreign calls, the string
// itself will already have been allocated so we just want the closure.
    c->info=(void*)x;
    EREADY(c);
    return c;
}

void* MKPTR(void* x)
{
    VAL c = MKCLOSURE;
    SETTY(c, PTR);
    c->info = x;
    EREADY(c);
    return c;
}

/* void* GETPTR(void* x) */
/* { */
/*     return (void*)(((VAL)x)->info); */
/* } */

void ERROR(char* msg)
{
    printf("*** error : %s ***\n",msg);
    assert(0);
    exit(1);
}

void* MKFREE(int x)
{
    VAL c = MKCLOSURE;
    SETTY(c, FREEVAR);
    c->info = (void*)x;
    EREADY(c);
    return c;
}

void slide(VMState* vm, int lose, int keep) {
    int i;
    for(i = 1; i <= keep; i++) {
	vm->stack_top[-(lose+i)] = *(vm->stack_top-i);
    }
    vm->stack_top-=lose;
}

VAL evm_getArg(int i) {
    if (i>=0 && i<v_argc) 
	return v_argv[i];
    else
	return MKSTR("");
}

int evm_numArgs() {
    return v_argc;
}

VMState* init_evm(int argc, char* argv[])
{
    allocate = GC_malloc;
    reallocate = GC_realloc;

    pools = malloc(sizeof(pool_t*)*1024);
    pool = malloc(sizeof(pool_t));
    *pools = pool;
    pool->block = NULL;
    pool->allocate = GC_malloc;
    pool->reallocate = GC_realloc;

    int i;
    one = MKINT(1);
    zcon = EMALLOC(sizeof(Closure)*255);
    for(i=0;i<255;++i) {
	zcon[i] = CONSTRUCTORn(i,0,0);
    }
    EREADY(zcon);

    v_argc = argc;
    v_argv = EMALLOC(sizeof(Closure)*v_argc);

    for(i=0;i<=argc;++i) {
	v_argv[i] = MKSTR(argv[i]);
    }
    EREADY(v_argv);

    VMState* vm = malloc(sizeof(VMState));
    vm->stack = malloc(sizeof(VAL)*STACK_INIT);
    vm->stack_top = vm->stack+STACK_INIT;
    vm->stack_top = vm->stack;

/*
    vm->roots = malloc(sizeof(VAL)*1024);
    vm->start_roots = vm->roots;

    vm->from_space = malloc(INIT_HEAP_SIZE*2);
    vm->to_space = malloc(INIT_HEAP_SIZE*2);
    vm->nursery = malloc(INIT_HEAP_SIZE);
    vm->heap_size = INIT_HEAP_SIZE;
    vm->next_nursery = 0;
    vm->next = 0;
*/
    return vm;
}

void wrap_GC_free(void * a, size_t b) {
  GC_free(a);
}

void* wrap_GC_realloc(void *ptr, size_t old, size_t new) {
  return GC_realloc(ptr, new);
}
void epic_main(int argc, char* argv[])
{
    GC_init();




    vm = init_evm(argc, argv);
    mp_set_memory_functions(GC_malloc_atomic, wrap_GC_realloc, wrap_GC_free);

//    GC_use_entire_heap = 1;
//    GC_free_space_divisor = 2;
//    GC_enable_incremental();
//    GC_time_limit = GC_TIME_UNLIMITED;

//    GC_full_freq=15;
//    fprintf(stderr, "Heap: %d\n", GC_get_heap_size());


    GC_expand_hp(1000000);
//    fprintf(stderr, "Heap: %d\n", GC_get_heap_size());

//    GC_disable();

    _do___U__main();

//    GC_gcollect();
/*    fprintf(stderr, "%d\n", GC_gc_no);
    fprintf(stderr, "Heap: %d\n", GC_get_heap_size());
    fprintf(stderr, "Free: %d\n", GC_get_free_bytes());
    fprintf(stderr, "Total: %d\n", GC_get_total_bytes());*/

/*
    if (vm->start_roots!=vm->roots) {
	fprintf(stderr, "Warning: roots left %d\n", vm->roots-vm->start_roots);
    }
*/
    epicMemInfo();
    close_evm(vm);
}

void close_evm(VMState* vm)
{
    /*    free(vm->from_space);
    free(vm->to_space);
    free(vm->nursery);
    free(vm->roots);
    free(vm);*/
}
