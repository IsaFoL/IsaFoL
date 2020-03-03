#define _POSIX_C_SOURCE 2
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <ctype.h>
#include <stdint.h>
#include <string.h>

#include "isasat_restart.h"



/*the parser is based on the code from lingeling*/

static char * inputname;
static FILE * inputfile;

static int lineno;
static int charno;

static void perr (const char * fmt, ...) {
  va_list ap;
  fprintf (stderr, "%s:%d: ", inputname, lineno);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

static void make_room(CLAUSE *cl) {
  cl->clause = (uint32_t *) realloc(cl->clause, 2*cl->size * sizeof(uint32_t));
  cl->size *= 2;
  if(cl->clause == NULL) {
    perr("failled to allocate memory for clause resizing");
  }
}

static CLAUSE new_clause(void) {
  CLAUSE cl;
  cl.clause = (uint32_t *) malloc(16 * sizeof(uint32_t));
  cl.size = 16;
  cl.used = 0;
  if(cl.clause == NULL) {
    perr("failled to allocate memory for clause");
  }
  return cl;
}

static CLAUSE new_empty_clause(void) {
  CLAUSE cl;
  cl.clause = NULL;
  cl.size = 0;
  cl.used = 0;
  return cl;
}


static CLAUSE copy_clause(CLAUSE *cl0) {
  CLAUSE cl;
  cl.clause = (uint32_t *) malloc(cl0->used * sizeof(uint32_t));
  memcpy(cl.clause, cl0->clause, cl0->used *  sizeof(uint32_t));
  cl.size = cl0->used;
  cl.used = cl0->used;
  if(cl.clause == NULL) {
    perr("failled to allocate memory for clause");
  }
  return cl;
}

static void append_lit(int32_t lit, CLAUSE * cl) {
  uint32_t ulit = (uint32_t)(lit < 0 ? 2 * (-lit - 1) +1 : 2 * (lit - 1) + 0);
  if(cl->used + 1 >= cl->size)
    make_room(cl);
  cl->clause[cl->used] = ulit;
  cl->used++;
}

static void free_clause (CLAUSE *cl) {
  free(cl->clause);
}

CLAUSES new_clauses(int64_t size) {
  CLAUSES clauses;
  clauses.num_clauses = size;
  clauses.clauses = (CLAUSE *) malloc((size+1) * sizeof(CLAUSE));
  for (int64_t n = 0; n < size; ++n) {
    clauses.clauses[n] = new_empty_clause();
  }
  return clauses;
}


void free_clauses (CLAUSES *cl) {
  for (int64_t n = 0; n <= cl->num_clauses; ++n) {
    free_clause(&cl->clauses[n]);
  }
  free(cl->clauses);

}
void print_clause(CLAUSE *cl) {
  for(int i = 0; i < cl->used; ++i) {
    uint32_t lit = cl->clause[i];
    printf("%d ", ((lit % 2 == 0) ? 1 : - 1) * ((lit >>1) + 1));
  }
  printf("0\n");
}

void print_clauses(CLAUSES *cl) {
  for(int i = 0; i < cl->num_clauses; ++i)
    print_clause(&cl->clauses[i]);
}

static int64_t next (void) {
  int64_t res;
  res = getc (inputfile);
  ++charno;
  if (res == '\n') lineno++,charno = 0;
  return res;
}

static CLAUSES parse (void) {
  int ch;
  int32_t lit;
  int32_t sign;
  int64_t num_lits, num_clss;
HEADER:
  ch = next ();
  if (ch == EOF) perr ("unexpected end-of-file in header on line %u", lineno);
  if (ch == 'c') {
    while ((ch = next ()) != '\n')
      if (ch == EOF)
	perr ("unexpected end-of-file in header comment on line %u", lineno);
    goto HEADER;
  }
  if (ch != 'p' ||
      next () != ' ' ||
      next () != 'c' ||
      next () != 'n' ||
      next () != 'f' ||
      next () != ' ') perr ("invalid header (expected 'p cnf '), but found %c on line %u, char %u", ch, lineno, charno-1);

  ch = next ();

  num_lits = ch - '0';
  while (isdigit (ch = next ())) num_lits = 10*num_lits + ch - '0';
 
  ch = next ();
  num_clss = ch - '0';
  while (isdigit (ch = next ())) num_clss = 10*num_clss + ch - '0';

  CLAUSES clauses = new_clauses(num_clss);

  int64_t clause_num = 0;
  CLAUSE cl = new_clause();

CLAUSES:
  if (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n') {
    ch = next ();
    goto CLAUSES;
  }
  if (ch == 'c') {
    while ((ch = next ()) != '\n')
      if (ch == EOF)
	perr ("unexpected end-of-file in body comment on line %u", lineno);
    goto CLAUSES;
  }
  if (ch == EOF) goto DONE;
  if (ch == '0') {
    if(clause_num > num_clss)
      perr("found too many clauses: clause  number %d, only %d expected on line %u", clause_num, num_clss, lineno);
    clauses.clauses[clause_num++] = copy_clause(&cl);
    cl.used = 0;

    ch = next ();
    goto CLAUSES;
  }
  if (ch == '-') {
    sign = -1;
    ch = next ();
    if (!isdigit (ch)) perr ("expected digit after '-' on line %u", lineno);
  } else sign = 1;

  if (!isdigit (ch) || ch == 0) perr ("expected literal on line %u", lineno);

  lit = ch - '0';

  while (isdigit (ch = next ())) lit = 10*lit + ch - '0';
  lit *= sign;

  if(lit < -num_lits || lit > num_lits || lit == 0)
    perr("invalid literal %d, max: %d", lit, num_lits);

  append_lit(lit, &cl);
  goto CLAUSES;

DONE:
  if(clause_num != num_clss)
    perr("found %d clauses, while %d were expected", clause_num, num_clss);

  free(cl.clause);
  return clauses;
}

typedef struct OPTS {
  _Bool s1:1;
  _Bool s2:1;
  _Bool s3:1;
} OPTS;

typedef struct STATS {
  uint64_t s1;
  uint64_t s2;
  uint64_t s3;
  uint64_t s4;
  uint64_t s5;
  uint64_t s6;
  uint64_t s7;
  uint64_t s8;
} STATS;

typedef struct R {
  int64_t finished;
  int64_t  sat;
} R;

int64_t IsaSAT_No_Restart_LLVM_IsaSAT_code_wrapped2(CLAUSES);

void print_propagations(int64_t props) {
  printf("\nc propagations %ld\n", props);
}

void print_conflicts(int64_t props) {
  printf("c conflicts %ld\n", props);
}

void print_decisions(int64_t props) {
  printf("c decisions %ld\n", props);
}

void print_reductions(int64_t props) {
  printf("c reductions %ld\n", props);
}

void print_local_restarts(int64_t props) {
  printf("c local_restarts %ld\n", props);
}

void print_uset(int64_t props) {
  printf("c uset %ld\n", props);
}

void print_GCs(int64_t props) {
  printf("c GCs %ld\n", props);
}

void print_phase(int8_t phase) {
  if(phase == 1)
    printf("c phase: QUIET\n");
  else
    printf("c phase: RESTART\n");
}

/*
declare void @IsaSAT_Show_LLVM_print_c_impl(i64)
declare void @IsaSAT_Show_LLVM_print_char_impl(i64)
declare void @IsaSAT_Show_LLVM_print_uint64_impl(i64)
declare void @IsaSAT_Show_LLVM_print_open_colour_impl(i64)
declare void @IsaSAT_Show_LLVM_print_close_colour_impl(i64)
*/
void IsaSAT_Show_LLVM_print_c_impl() {
  printf("\nc ");
}

void IsaSAT_Show_LLVM_print_uint64_impl(int64_t p) {
  printf(" %12ld ", p);
}
void IsaSAT_Show_LLVM_print_open_colour_impl(int64_t c) {
  printf("\e[%lim", c);
}
void IsaSAT_Show_LLVM_print_close_colour_impl(int64_t c) {
  printf("\e[0m");
}
void IsaSAT_Show_LLVM_print_char_impl(int64_t c) {
  printf("%c", (char)c);
}

_Bool has_suffix (const char * str, const char * suffix) {
  size_t k = strlen (str), l = strlen (suffix);
  return k > l && !strcmp (str + k - l, suffix);
}

static int xzsig[] = { 0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, EOF };
static int bz2sig[] = { 0x42, 0x5A, 0x68, EOF };
static int gzsig[] = { 0x1F, 0x8B, EOF };
static int sig7z[] = { 0x37, 0x7A, 0xBC, 0xAF, 0x27, 0x1C, EOF };
static int lzmasig[] = { 0x5D, 0x00, 0x00, 0x80, 0x00, EOF };


FILE * open_pipe (const char * fmt, const char * path,
                        const char * mode)
{
  size_t prglen = 0;
  while (fmt[prglen] && fmt[prglen] != ' ') prglen++;
  char prg [prglen + 1];
  strncpy (prg, fmt, prglen);
  prg[prglen] = 0;
  char cmd[strlen (fmt) + strlen (path)];
  sprintf (cmd, fmt, path);
  FILE * res = popen (cmd, mode);
  return res;
}

char * find (const char * prg) {
  size_t prglen = strlen (prg);
  const char * c = getenv ("PATH");
  if (!c) return 0;;
  size_t len = strlen (c);
  char e [len + 1];
  strcpy (e, c);
  char * res = 0;
  for (char * p = e, * q; !res && p < e + len; p = q) {
    for (q = p; *q && *q != ':'; q++)
      ;
    *q++ = 0;
    size_t pathlen = (q - p) + prglen;
    char path [pathlen + 1];
    sprintf (path, "%s/%s", p, prg);
    free(path);
  }
  free(e);
  return res;
}

FILE * read_pipe (const char * fmt,
                        const int * sig,
                        const char * path) {
  return open_pipe (fmt, path, "r");
}


void LLVM_DS_NArray_narray_free1(int32_t *);

void print_version() {
  int32_t* version = llvm_version();
  while(*version) {
    printf("%c", (char)*version);
    ++version;
  }
  //LLVM_DS_NArray_narray_free1(*version);
};


int main(int argc, char *argv[]) {
  if(argc != 2) {
    printf("expected one argument, the DIMACS file to solve");
    return 0;
  }
  inputname = argv[1];
  if(has_suffix(inputname, "version")) {
    print_version();
    printf("\n");
    return 0;
  }

  if (has_suffix (inputname, ".xz")) {
    inputfile = read_pipe ("xz -c -d %s", xzsig, inputname);
    printf("c compressed file\n");
    if (!inputfile) goto READ_FILE;
  } else if (has_suffix (inputname, ".lzma")) {
    inputfile = read_pipe ("lzma -c -d %s", lzmasig, inputname);
    if (!inputfile) goto READ_FILE;
  } else if (has_suffix (inputname, ".bz2")) {
    inputfile = read_pipe ("bzip2 -c -d %s", bz2sig, inputname);
    if (!inputfile) goto READ_FILE;
  } else if (has_suffix (inputname, ".gz")) {
    inputfile = read_pipe ("gzip -c -d %s", gzsig, inputname);
    if (!inputfile) goto READ_FILE;
  } else if (has_suffix (inputname, ".7z")) {
    inputfile = read_pipe ("7z x -so %s 2>/dev/null", sig7z, inputname);
    if (!inputfile) goto READ_FILE;
  } else {
READ_FILE:
    printf("c not compressed file\n");
    inputfile = fopen (inputname, "r");
  }

  if(inputfile == NULL) {
    printf("could not open file %s", inputname);
    exit(EXIT_FAILURE);
  }

  CLAUSES clauses = parse();

  fclose(inputfile);
  
  //print_clauses(&clauses);

  printf("c propagations                       redundant                lrestarts                GC        \n"
	 "c                     conflicts                   reductions             level-0            LBDs \n");
  int64_t t = IsaSAT_No_Restart_LLVM_IsaSAT_code_wrapped2(clauses);
  if((t & 2) == 0)
    printf("s UNKNOWN\n");
  if (t & 1)
    printf("s UNSATISFIABLE\n");
  else
    printf("s SATISFIABLE\n");
  free_clauses(&clauses);
  return 0;
}