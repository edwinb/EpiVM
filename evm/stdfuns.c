#include "stdfuns.h"
#include "closure.h"
#include <stdlib.h>
#include <unistd.h>
#include <gmp.h>
#include <string.h>
#include <sys/time.h>

void printInt(int x) { printf("%d\n",x); }
void putStr(char* s) { printf("%s",s); }
void printBigInt(mpz_t x) { printf("%s\n",mpz_get_str(NULL,10,x)); }
void printBig(VAL x) 
{ 
    if (ISINT(x)) {
	printf("%ld INT\n", GETINT(x));
    } else {
	printBigInt(*(GETBIGINT(x)));
    }
}

void epicGC() {
#ifdef USE_BOEHM
    GC_gcollect();
#endif
}

void epicMemInfo() {
#ifdef USE_BOEHM
    GC_gcollect();
    int heap = GC_get_heap_size();
    int free = GC_get_free_bytes();
    int total = GC_get_total_bytes();

    printf("Heap size %d\n", heap);
    printf("Heap used %d\n", heap-free);
    printf("Total allocations %d\n", total);
#endif
}

int readInt() {
    return atoi(readStr());
}

// FIXME: Do this properly!
char* readStr() {
    char *buf = NULL;
    if (buf==NULL) { buf = EMALLOC(sizeof(char)*512); } // yeah, right...
    fgets(buf,512,stdin);
    char *loc = strchr(buf,'\n');
    *loc = '\0';
    return buf;
}

// FIXME: Do this properly!
void* freadStr(void* h) {
    static char bufin[128];
    bufin[0]='\0';

    FILE* f = (FILE*)h;
    fgets(bufin,128,f);
    int len = strlen(bufin);
#ifdef USE_BOEHM
    VAL c = GC_MALLOC_ATOMIC(sizeof(Closure)+len*sizeof(char)+sizeof(char)+1);
#else
    VAL c = EMALLOC(sizeof(Closure)+len*sizeof(char)+sizeof(char)+1);
#endif   
    SETTY(c, STRING);
    c->info = ((void*)(c+1));
    char *buf = (char*)(c->info);
    strcpy(buf,bufin);

    char *loc = strchr(buf,'\n');
    if (loc) *loc = '\0'; else buf[0]='\0';
    return ((void*)c);
}

void fputStr(void* h, char* str) {
    FILE* f = (FILE*)h;
    fputs(str, f);
}

int streq(char* x, char* y) {
    return !(strcmp(x,y));
}

int strlt(char* x, char* y) {
    return strcmp(x,y)<0;
}

int strToInt(char* str)
{
    return strtol(str,NULL,10);
}

char* intToStr(int x)
{
    char* buf = EMALLOC(16);
    sprintf(buf,"%d",x);
    return buf;
}

double intToFloat(int x)
{
    return (double)x;
}

int floatToInt(double x)
{
    return (int)x;
}

double strToFloat(char* str)
{
//    printf("%s, %f\n",str, strtod(str,NULL));
    return strtod(str,NULL);
}

char* floatToStr(double x)
{
//    printf("%f\n",x);
    char* buf = EMALLOC(32);
    sprintf(buf,"%g",x);
    return buf;
}

void* getNative(void * fn) {
    return fn;
}

int strIndex(char* str, int i)
{
    return (int)(str[i]);
}

int strHead(char* str) {
    if (str[0]=='\0') 
	ERROR("Can't take the head of an empty string");
    return (int)(str[0]);
}

char* strTail(char* str) {
    if (str[0]=='\0') 
	ERROR("Can't take the tail of an empty string");
    return str+1; // I'll need to check the GC will understand this...
}

char* strCons(int h, char* str) {
    char* buf = EMALLOC((1+strlen(str))*sizeof(char));
    buf[0]=(char)h;
    strcpy(buf+1, str);
    return buf;
}

char* strrev(char* str) {
    char* buf = EMALLOC((1+strlen(str))*sizeof(char));
    int x = strlen(str);
    buf[x+1]='\0';
    int y = 0; 
    while(x>0) {
	buf[y++] = str[--x];
    }
    return buf;
}

char* substr(char* str, int start, int len) {
    if (len<0) len=0;
    char* buf = EMALLOC((len+1)*sizeof(char));
    strncpy(buf, str+start, len);
    buf[len]='\0';
    return buf;
}

int strFind(char* str, char c) {
    int i = 0;
    while(*str!='\0') {
	if (*str==c) return i;
	++i; ++str;
    }
    return -1;
}

char* append(char* x, char* y) {
    char* buf = EMALLOC((strlen(x)+strlen(y))*sizeof(char));
    strcpy(buf,x);
    strcat(buf,y);
    return buf;
}

mpz_t* addBigInt(mpz_t x, mpz_t y) {
    mpz_t* answer = EMALLOC(sizeof(mpz_t));
    mpz_add(*answer, x, y);
    return answer;
}

VAL addBig(VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
	int vx = GETINT(x);
	int vy = GETINT(y);
	if ((vx <= 0 && vy >=0) || (vx >=0 && vy <=0)) {
	    return INTOP(+,x,y);
	}
	int res = vx + vy;
	if (res >= 1<<30 || res <= -(1 << 30)) {
	    return MKBIGINT(addBigInt(*(NEWBIGINTI(vx)), *(NEWBIGINTI(vy))));
	} else {
	    return MKINT(res);
	}
    } else {
	return MKBIGINT(addBigInt(*(GETBIGINT(x)), *(GETBIGINT(y))));
    }
}

mpz_t* subBigInt(mpz_t x, mpz_t y) {
    mpz_t* answer = EMALLOC(sizeof(mpz_t));
    mpz_sub(*answer, x, y);
    return answer;
}

VAL subBig(VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
	int vx = GETINT(x);
	int vy = GETINT(y);
	if ((vx <= 0 && vy <=0) || (vx >=0 && vy >=0)) {
	    return INTOP(-,x,y);
	}
	int res = vx - vy;
	if (res >= 1<<30 || res <= -(1 << 30)) {
	    return MKBIGINT(subBigInt(*(NEWBIGINTI(vx)), *(NEWBIGINTI(vy))));
	} else {
	    return MKINT(res);
	}
    } else {
	return MKBIGINT(subBigInt(*(GETBIGINT(x)), *(GETBIGINT(y))));
    }
}

mpz_t* mulBigInt(mpz_t x, mpz_t y) {
    mpz_t* answer = EMALLOC(sizeof(mpz_t));
    mpz_mul(*answer, x, y);
    return answer;
}

VAL mulBig(VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
	int vx = abs(GETINT(x));
	int vy = abs(GETINT(y));
	// we could work out likelihood of overflow by checking the number
	// of necessary bits. Here's a quick conservative hack instead.
	if ((vx < (1<<15) && vy < (1<16)) ||
	    (vx < (1<<16) && vy < (1<15)) ||
	    (vx < (1<<20) && vy < (1<11)) ||
	    (vx < (1<<11) && vy < (1<20)) ||
	    (vx < (1<<23) && vy < (1<<8)) ||
	    (vx < (1<<8) && vy < (1<<23))) { // ultra-conservative!
	    return INTOP(*,x,y);
	} else {
	    mpz_t *resb = mulBigInt(*(NEWBIGINTI(vx)), *(NEWBIGINTI(vy)));
	    VAL res = MKBIGINT(resb);
	    return res;
	}
    } else {
	return MKBIGINT(mulBigInt(*(GETBIGINT(x)), *(GETBIGINT(y))));
    }
}

mpz_t* divBigInt(mpz_t x, mpz_t y) {
    mpz_t* answer = EMALLOC(sizeof(mpz_t));
    mpz_tdiv_q(*answer, x, y);
    return answer;
}

VAL divBig(VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
	// always gets smaller, so it's safe
	return INTOP(/, x, y);
    } else {
	return MKBIGINT(divBigInt(*(GETBIGINT(x)), *(GETBIGINT(y))));
    }
}

mpz_t* modBigInt(mpz_t x, mpz_t y) {
    mpz_t* answer = EMALLOC(sizeof(mpz_t));
    mpz_tdiv_r(*answer, x, y);
    return answer;
}

VAL modBig(VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
	// always gets smaller, so it's safe
	return INTOP(%, x, y);
    } else {
	return MKBIGINT(modBigInt(*(GETBIGINT(x)), *(GETBIGINT(y))));
    }
}

int eqBigInt(mpz_t x, mpz_t y) {
    return mpz_cmp(x,y)==0;
}

int eqBig(VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
	return (GETINT(x) == GETINT(y));
    } else {
	return (eqBigInt(*(GETBIGINT(x)), *(GETBIGINT(y))));
    }
}

int ltBigInt(mpz_t x, mpz_t y)
{
    return mpz_cmp(x,y)<0;
}

int ltBig(VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
	return (GETINT(x) < GETINT(y));
    } else {
	return (ltBigInt(*(GETBIGINT(x)), *(GETBIGINT(y))));
    }
}

int gtBigInt(mpz_t x, mpz_t y)
{
    return mpz_cmp(x,y)>0;
}

int gtBig(VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
	return (GETINT(x) > GETINT(y));
    } else {
	return (gtBigInt(*(GETBIGINT(x)), *(GETBIGINT(y))));
    }
}

int leBigInt(mpz_t x, mpz_t y)
{
    return mpz_cmp(x,y)<=0;
}

int leBig(VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
	return (GETINT(x) <= GETINT(y));
    } else {
	return (leBigInt(*(GETBIGINT(x)), *(GETBIGINT(y))));
    }
}

int geBigInt(mpz_t x, mpz_t y)
{
    return mpz_cmp(x,y)>=0;
}

int geBig(VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
	return (GETINT(x) >= GETINT(y));
    } else {
	return (geBigInt(*(GETBIGINT(x)), *(GETBIGINT(y))));
    }
}

mpz_t* strToBigInt(char* str)
{
    mpz_t* answer = EMALLOC(sizeof(mpz_t));
    mpz_init(*answer);
    mpz_set_str(*answer, str, 10);
    return answer;
}

char* bigIntToStr(mpz_t x)
{
    char* str = mpz_get_str(NULL,10,x);
    return str;
}

VAL strToBig(char* str) {
    return MKBIGINT(strToBigInt(str));
}

char* bigToStr(VAL x) {
    if (ISINT(x)) {
	return intToStr(GETINT(x));
    } else {
	return bigIntToStr(*(GETBIGINT(x)));
    }
}


// IORefs
int numrefs = 0;
void** iorefs = NULL;

int newRef() {
    // Increase space for the iorefs
    if (iorefs==NULL) {
	iorefs = (void**)(EMALLOC(sizeof(void*)));
	numrefs=1;
    } else {
	iorefs = (void**)(EREALLOC(iorefs, sizeof(void*)*(numrefs+1)));
	numrefs++;
    }
    return numrefs-1;
}

void* readRef(int r) {
    return iorefs[r];
}

void writeRef(int r, void* val) {
    iorefs[r]=val;
}

// Threads and locks

typedef struct {
    pthread_mutex_t m_id;
} Mutex;

typedef struct {
    pthread_t t_id;
} Thread;

Mutex** ms = NULL;
int mutexes = 0;

int newLock(int sem)
{
    pthread_mutex_t m;

    pthread_mutex_init(&m, NULL);
    Mutex* newm = EMALLOC(sizeof(Mutex));
    newm->m_id = m;

    // Increase space for the mutexes
    if (ms==NULL) {
	ms = (Mutex**)EMALLOC(sizeof(Mutex*));
	mutexes=1;
    } else {
	ms = (Mutex**)(EREALLOC(ms, sizeof(Mutex*)*(mutexes+1)));
	mutexes++;
    }

    ms[mutexes-1] = newm;
    return mutexes-1;
}

void doLock(int lock)
{
    pthread_mutex_lock(&(ms[lock]->m_id));
}

void doUnlock(int lock)
{
    pthread_mutex_unlock(&(ms[lock]->m_id));
}

struct threadinfo {
    void* proc;
    void* result;
};

void* runThread(void* th_in) {
    struct threadinfo* th = (struct threadinfo*)th_in;
    void* v = DO_EVAL(th->proc, 1);
    th->result = v;
    return v;
}

void doFork(void* proc)
{
    pthread_t* t = EMALLOC(sizeof(pthread_t));
    struct threadinfo th;
    th.proc = proc;
    th.result = NULL;
    pthread_create(t, NULL, runThread, &th);
}

void* doWithin(int limit, void* proc, void* doOnFail)
{
    pthread_t* t = EMALLOC(sizeof(pthread_t));
//    printf("CREATING THREAD %d\n", t);
    struct threadinfo th;
    th.proc = proc;
    th.result = NULL;

    struct timeval tv;
    gettimeofday(&tv, NULL);
    int tnow, tthen = do_utime();

    pthread_create(t, NULL, runThread, &th);
//    printf("tthen %d\n", tthen);

    void* ans;

    do 
    {
	// If the answer has been updated, we're done.
	if (th.result!=NULL) {
	    pthread_join(*t, &ans);
	    return ans;
	}
	gettimeofday(&tv, NULL);
	tnow = do_utime();
	usleep(100);
//	printf("tnow %d\n", tnow);
    }
    while(tnow<(tthen+(limit*1000)));
    pthread_cancel(*t);
    return DO_EVAL(doOnFail,1);
}

int do_utime() {
    struct timeval tv;
    gettimeofday(&tv, NULL);

    static int start=0;
    if (start==0) { start = tv.tv_sec; }

    return 1000000*(tv.tv_sec - start)+tv.tv_usec;
}

// Basic file handling

void* fileOpen(char* name, char* mode) {
    FILE* f = fopen(name, mode);
    return (void*)f;
}

void fileClose(void* h) {
    FILE* f = (FILE*)h;
    fclose(f);
}

int isNull(void* ptr) {
    return ptr==NULL;
}

// Command line arguments

int epic_numArgs()
{
    return evm_numArgs();
}

char* epic_getArg(int i)
{
    return GETSTR(evm_getArg(i));
}
