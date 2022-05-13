#define _POSIX_C_SOURCE 2
#include <assert.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <ctype.h>
#include <assert.h>
#include <stdint.h>
#include <string.h>
#include <sys/time.h>

#include "isasat_restart.h"


/* Put the model in an array to print it*/
typedef struct MODEL {
  int32_t* model;
  int used;
  int size;
} MODEL;

MODEL model;

/*the parser is based on the code from lingeling*/

static char * inputname = NULL;
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

static void append_raw_lit(uint32_t ulit, CLAUSE * cl) {
  if(cl->used + 1 >= cl->size)
    make_room(cl);
  cl->clause[cl->used] = ulit;
  cl->used++;
}

static void append_lit(int32_t lit, CLAUSE * cl) {
  uint32_t ulit = (uint32_t)(lit < 0 ? 2 * (-lit - 1) +1 : 2 * (lit - 1) + 0);
  append_raw_lit(ulit, cl);
}

static void free_clause (CLAUSE *cl) {
  free(cl->clause);
}

int64_t IsaSAT_LLVM_IsaSAT_wrapped(CBOOL, CBOOL, CBOOL, int64_t, int64_t, int64_t, CBOOL, int64_t, int64_t, int64_t, CLAUSES);

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

  model.size = num_lits + 2;
  model.model = malloc((num_lits + 2) * sizeof(int32_t));
  model.used = 0;
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

void IsaSAT_LLVM_print_propa_impl(int64_t props) {
#ifdef PRINTSTATS
  printf("\nc propagations %ld\n", props);
#endif
}

void IsaSAT_LLVM_print_confl_impl(int64_t props) {
#ifdef PRINTSTATS
  printf("c conflicts %ld\n", props);
#endif
}

void IsaSAT_LLVM_print_dec_impl(int64_t props) {
#ifdef PRINTSTATS
  printf("c decisions %ld\n", props);
#endif
}

void IsaSAT_LLVM_print_res_impl(int64_t props) {
#ifdef PRINTSTATS
  printf("c reductions %ld\n", props);
#endif
}

void IsaSAT_LLVM_print_lres_impl(int64_t props) {
#ifdef PRINTSTATS
  printf("c local_restarts %ld\n", props);
#endif
}

void IsaSAT_LLVM_print_uset_impl(int64_t props) {
#ifdef PRINTSTATS
  printf("c uset %ld\n", props);
#endif
}

void IsaSAT_LLVM_print_gc_impl(int64_t props) {
#ifdef PRINTSTATS
  printf("c GCs %ld\n", props);
#endif
}

void IsaSAT_LLVM_print_irred_clss_impl(int64_t props) {
#ifdef PRINTSTATS
  printf("c irred_clss %ld\n", props);
#endif
}

void IsaSAT_LLVM_print_binary_unit_impl(int64_t props) {
#ifdef PRINTSTATS
  printf("c binary unit removed %ld\n", props);
#endif
}
void IsaSAT_LLVM_print_binary_red_removed_impl(int64_t props) {
#ifdef PRINTSTATS
  printf("c binary redundant removed %ld\n", props);
#endif
}
void IsaSAT_LLVM_print_purelit_elim_impl(int64_t props) {
#ifdef PRINTSTATS
  printf("c pure literals unit removed %ld\n", props);
#endif
}
void IsaSAT_LLVM_print_purelit_rounds_impl(int64_t props) {
#ifdef PRINTSTATS
  printf("c elimination rounds %ld\n", props);
#endif
}

void print_phase(int8_t phase) {
#ifdef PRINTSTATS
  if(phase == 1)
    printf("c phase: QUIET\n");
  else
    printf("c phase: RESTART\n");
#endif
}

/*
declare void @IsaSAT_Show_LLVM_print_c_impl(i64)
declare void @IsaSAT_Show_LLVM_print_char_impl(i64)
declare void @IsaSAT_Show_LLVM_print_uint64_impl(i64)
declare void @IsaSAT_Show_LLVM_print_open_colour_impl(i64)
declare void @IsaSAT_Show_LLVM_print_close_colour_impl(i64)
*/
void IsaSAT_Show_LLVM_print_c_impl() {
#ifdef PRINTSTATS
  printf("\nc ");
#endif
}

void IsaSAT_Show_LLVM_print_uint64_impl(int64_t p) {
#ifdef PRINTSTATS
  printf(" %12ld ", p);
#endif
}
void IsaSAT_Show_LLVM_print_open_colour_impl(int64_t c) {
#ifdef PRINTSTATS
  printf("\e[%lim", c);
#endif
}
void IsaSAT_Show_LLVM_print_close_colour_impl(int64_t c) {
#ifdef PRINTSTATS
  printf("\e[0m");
#endif
}
void IsaSAT_Show_LLVM_print_char_impl(int64_t c) {
#ifdef PRINTSTATS
  printf("%c", (char)c);
#endif
}


void IsaSAT_Setup3_LLVM_print_encoded_lit_end_code(uint32_t lit) {
  model.model[model.used++] = lit;
}

void IsaSAT_Setup3_LLVM_print_literal_of_trail_code(uint32_t lit) {
  const int ilit = ((lit %2 == 0) ? 1 : -1) * ((lit >> 1) + 1);
  model.model[model.used++] = ilit;
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
  }
  return res;
}

CBOOL file_match_extension (const char *path, const int *sig)
{
  assert (path);
  FILE * tmp = fopen (path, "r");
  if (!tmp) {
    printf ("failed to open file %s", path);
    abort();
  }

  CBOOL res = 1;
  for (const int *p = sig; res && (*p != EOF); p++)
    res = (getc(tmp) == *p);
  fclose (tmp);
  if (!res) {
#ifdef PRINTSTATS
    printf ("file type signature check for '%s' failed\n", path);
#endif
 }
  return res;
}
FILE * read_pipe (const char * fmt,
                        const int * sig,
                        const char * path) {
  if (sig && !file_match_extension (path, sig))
    return 0;
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

void print_uint32(uint32_t u) {
  //  printf("LBD: %d -", u);
}

FILE *proof = NULL;
int binary_proof = 1;
CLAUSE *proof_clause;

static inline int
isasat_putc (int ch)
{
#ifdef _POSIX_C_SOURCE
  int res = putc_unlocked (ch, proof);
#else
  int res = putc (ch, proof);
#endif
  return res;
}

void IsaSAT_Proofs_LLVM_log_start_new_clause_impl(uint64_t _w) {
  if (!proof)
    return;

  if (binary_proof)
    isasat_putc ('a');
  // tmp
  // isasat_putc (' ');
}

void IsaSAT_Proofs_LLVM_log_end_clause_impl(uint64_t _w) {
  if (!proof)
    return;
  if(!binary_proof) {
    isasat_putc('0');
    isasat_putc('\n');
  }
  else
    isasat_putc(0);
}


static void
isasat_print_binary_lit (uint32_t x)
{
  x = x>0 ? 2*x : -2*x+1;
  unsigned char ch;
  while (x & ~0x7f)
    {
      ch = (x & 0x7f) | 0x80;
      isasat_putc (ch);
      x >>= 7;
    }
  isasat_putc ((unsigned char) x);
}

static void
isasat_print_ascii_lit (uint32_t ilit)
{
  fprintf(proof, "%d ", ilit);
}

static void isasat_print_binary_clause ()
{

  const uint32_t *end = proof_clause->clause + proof_clause->used;
  for (uint32_t *lit = proof_clause->clause; lit != end; ++lit)
    isasat_print_binary_lit(*lit);
  IsaSAT_Proofs_LLVM_log_end_clause_impl(0);
}


static void isasat_print_ascii_clause ()
{

  const uint32_t *end = proof_clause->clause + proof_clause->used;
  for (uint32_t *lit = proof_clause->clause; lit != end; ++lit) {
    isasat_print_ascii_lit(*lit);
  }
  IsaSAT_Proofs_LLVM_log_end_clause_impl(0);
}

static void isasat_print_clause ()
{
  if (binary_proof)
    isasat_print_binary_clause();
  else
    isasat_print_ascii_clause();
}

static void isasat_print_literal (uint32_t lit)
{
  const int ilit = ((lit %2 == 0) ? 1 : -1) * ((lit >> 1) + 1);
  if (binary_proof)
    isasat_print_binary_lit (ilit);
  else
    isasat_print_ascii_lit(ilit);
}

void IsaSAT_Proofs_LLVM_log_literal_impl(uint32_t lit) {
  if (!proof)
    return;
  isasat_print_literal (lit);
}

void IsaSAT_Proofs_LLVM_log_start_del_clause_impl(uint64_t _w) {
  if (!proof)
    return;
  isasat_putc ('d');
  if (!binary_proof)
    isasat_putc (' ');
}

void IsaSAT_Proofs_LLVM_mark_literal_for_unit_deletion_impl(uint32_t lit)
{
  if (!proof)
    return;
  append_raw_lit (lit, proof_clause);
}

void IsaSAT_Proofs_LLVM_mark_clause_for_unit_as_changed_impl(uint64_t i)
{
  if (!proof)
    return;
  IsaSAT_Proofs_LLVM_log_start_del_clause_impl(i);
  const uint32_t *end = proof_clause->clause + proof_clause->used;
  for (uint32_t *lit = proof_clause->clause; lit != end; ++lit)
    IsaSAT_Proofs_LLVM_log_literal_impl(*lit);
  IsaSAT_Proofs_LLVM_log_end_clause_impl(i);
  proof_clause->used = 0;
}

void IsaSAT_Proofs_LLVM_mark_clause_for_unit_as_unchanged_impl(uint64_t i)
{
  if (!proof)
    return;
  proof_clause->used = 0;
}


struct PROFILE {
    long double start;
    int active;
    long double total;
};

struct PROFILE propagate_prof, analyze_prof, gc_prof, reduce_prof, total_prof, parsing_prof,
  init_prof, minimization_prof;

void init_profiles () {
  propagate_prof.total = 0;
  analyze_prof.total = 0;
  gc_prof.total = 0;
  reduce_prof.total = 0;
  total_prof.total = 0;
  parsing_prof.total = 0;
  init_prof.total = 0;
  minimization_prof.total = 0;
}

void start_profile(struct PROFILE *p) {
#ifndef NOPROFILING
  if(p->active) {
#ifdef PRINTSTATS
    printf("c incorrect use of profiling: missing stop... recovering by ignoring last interval\n");
#endif
  }
  p->active = 1;
  struct timeval time;
  gettimeofday(&time, NULL);
  p->start =  time.tv_sec * 1000000 + time.tv_usec;
#endif
}

void IsaSAT_Profile_LLVM_start_profile(uint8_t t) {
#ifndef NOPROFILING
  if(t == IsaSAT_Profile_PROPAGATE ()) {
    start_profile(&propagate_prof);
  }
  else if (t == IsaSAT_Profile_ANALYZE ()) {
    start_profile(&analyze_prof);
  }
  else if (t == IsaSAT_Profile_REDUCE ()) {
    start_profile(&reduce_prof);
  }
  else if (t == IsaSAT_Profile_GC ()) {
    start_profile(&gc_prof);
  }
  else if (t == IsaSAT_Profile_MINIMIZATION ()) {
    start_profile(&minimization_prof);
  }
  else if (t == IsaSAT_Profile_INITIALISATION ()) {
    start_profile(&init_prof);
  } else {
#ifdef PRINTSTATS
    printf("c unrecognised profile, ignoring\n");
#endif
  }
#endif
}

void stop_profile(struct PROFILE *p) {
#ifndef NOPROFILING
  if(!p->active) {
    printf("c incorrect use of profiling: missing start... recovering by ignoring last interval\n");
    return;
  }
  p->active = 0;
  struct timeval time;
  gettimeofday(&time, NULL);
  // printf("profile start at %Lf and stopped at %ld, running for %Lf\n", p->start,  time.tv_sec * 1000000 +time.tv_usec,  time.tv_sec * 1000000 + time.tv_usec - p->start);
  p->total += time.tv_sec * 1000000 + (time.tv_usec - p->start);
#endif
}

void IsaSAT_Profile_LLVM_stop_profile(uint8_t t) {
#ifndef NOPROFILING
  if(t == IsaSAT_Profile_PROPAGATE ()) {
    stop_profile(&propagate_prof);
  }
  else if (t == IsaSAT_Profile_ANALYZE ()) {
    stop_profile(&analyze_prof);
  }
  else if (t == IsaSAT_Profile_REDUCE ()) {
    stop_profile(&reduce_prof);
  }
  else if (t == IsaSAT_Profile_GC ()) {
    stop_profile(&gc_prof);
  }
  else if (t == IsaSAT_Profile_MINIMIZATION ()) {
    stop_profile(&minimization_prof);
  }
  else if (t == IsaSAT_Profile_INITIALISATION ()) {
    stop_profile(&init_prof);
  } else {
    printf("c unrecognised profile, ignoring\n");
  }
#endif
}

int compare_atom(const void* lit1, const void* lit2) {
  const int ilit1 = *((int *)lit1);
  const int ilit2 = *((int *)lit2);
  const int atom1 = ilit1 < 0 ? -ilit1 : ilit1;
  const int atom2 = ilit2 < 0 ? -ilit2 : ilit2;
  if(atom1 == atom2)
    return 0;
  return atom1 > atom2;
}
int main(int argc, char *argv[]) {
  start_profile(&parsing_prof);
  if(argc < 2) {
    printf("expected one argument, the DIMACS file to solve");
    return 0;
  }

#ifdef NOOPTIONS
#define OPTIONu64 const uint64_t
#define OPTIONb const CBOOL
#else
#define OPTIONu64 uint64_t
#define OPTIONb CBOOL
#endif
  OPTIONb target_phases = 1;
  OPTIONb reduce = 1;
  OPTIONb restart = 1;
  OPTIONu64 restartint = 20;
  OPTIONu64 restartmargin = 17;
  OPTIONu64 fema = 128849010;
  OPTIONu64 sema = 429450;
  OPTIONu64 unitinterval = 1000;
  char *proof_path = NULL;
  int versionOnly = 0;

  for(int i = 1; i < argc; ++i) {
    char * opt = argv[i];
    int n;
    //printf("c checking option %s i=%d argc=%d\n", opt, i, argc);
    if(strcmp(opt, "--version\0") == 0)
      versionOnly = 1;
    else
#ifndef NOOPTIONS
       if(strcmp(opt, "--ascii\0") == 0)
      binary_proof = 0;
    else if(strcmp(opt, "--notarget\0") == 0)
      target_phases = 0;
    else if(strcmp(opt, "--noreduce\0") == 0)
      reduce = 0;
    else if(strcmp(opt, "--norestart\0") == 0)
      restart = 0;
    else if (strcmp(opt, "--restartint\0") == 0 && i+1 < argc - 1 && (n = atoi(argv[i+1]))) {
      restartint = (uint64_t)n;
      ++i;
    }
    else if (strcmp(opt, "--restartmargin\0") == 0 && i+1 < argc - 1 && (n = atoi(argv[i+1]))) {
      restartmargin = (uint64_t)n;
      ++i;
    }
    else if (strcmp(opt, "--emafast\0") == 0 && i+1 < argc - 1 && (n = atoi(argv[i+1]))) {
      fema = (uint64_t)n;
      ++i;
    }
    else if (strcmp(opt, "--emaslow\0") == 0 && i+1 < argc - 1 && (n = atoi(argv[i+1]))) {
      sema = (uint64_t)n;
      ++i;
    }
    else if (strcmp(opt, "--unitinterval\0") == 0 && i+1 < argc - 1 && (n = atoi(argv[i+1]))) {
      unitinterval = (uint64_t)n;
      ++i;
    }
    else if (opt[0] == '-') {
      //printf("c ignoring  unrecognised option %s i=%d argc=%d\n", opt, i, argc);
    } else
#endif
      if (inputname) {
      proof_path = opt;
      // printf("c proof file %s i=%d argc=%d\n", opt, i, argc);
      ++i;
    } else if (proof_path) {
      // printf("c ignoring  unrecognised option %s i=%d argc=%d\n", opt, i, argc);
      ++i;
    } else {
      // printf("c input file %s i=%d argc=%d\n", opt, i, argc);
      inputname = opt;
    }
  }
  if(versionOnly || !inputname || has_suffix(inputname, "version\0")) {
    print_version();
    printf("\n");
    return 0;
  }

  if (proof_path) {
    proof = fopen (proof_path, "w");
    if (!proof) {
      printf ("cannot open proof file, aborting");
      return 0;
    }
  }


  if (has_suffix (inputname, ".xz")) {
    inputfile = read_pipe ("xz -c -d %s", xzsig, inputname);
#ifdef PRINTSTATS
    //printf("c compressed file\n");
#endif
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
    inputfile = fopen (inputname, "r");
  }

  if(inputfile == NULL) {
    printf("could not open file %s", inputname);
    exit(EXIT_FAILURE);
  }

  CLAUSES clauses = parse();

  CLAUSE pc = new_clause();
  proof_clause = &pc;

  fclose(inputfile);
  stop_profile(&parsing_prof);

  //print_clauses(&clauses);
  init_profiles();
  start_profile(&total_prof);
#ifdef PRINTSTATS
  printf("c    propagations                       redundant                 reductions                  level-0                       LBDS                    not-mem-reasons\n"
	 "c                     conflicts                      irred                      lrestarts                       GCs                       unit-subsumed               subsumed\n");
  //      c B     47625262        274000         28925          2935            34          7082            11            22            11             0             7             0

#endif
  int64_t t = IsaSAT_LLVM_IsaSAT_wrapped(reduce, restart, 1, restartint, restartmargin, 4, target_phases, fema,
			     sema, unitinterval, clauses);
  stop_profile(&total_prof);

  _Bool interrupted = t & 2;
  _Bool unsatisfiable = t & 1;
  if(interrupted)
    printf("s UNKNOWN\n");
  else if (unsatisfiable)
    printf("s UNSATISFIABLE\n");
  else {
    printf("s SATISFIABLE\n");
    // model.used - 1 to keep 0 at the end
    qsort(model.model, model.used - 1, sizeof(int32_t), compare_atom);
    // taken from CaDiCaL's print_witness
    int c = 0, i = 0, tmp;
    do {
      if (!c)
        printf("v"), c = 1;
      tmp = model.model[i++];
      char str[20];
      sprintf (str, " %d", tmp);
      int l = strlen(str);
      if (c + l > 78) {
        fputs ("\nv", stdout);
	c = 1;
      }
      fputs (str, stdout);
      c += l;
    } while (tmp);
    if (c)
      fputs("\n", stdout);
  }
  free(model.model);


#ifdef PRINTSTATS
  const long double total_measure = propagate_prof.total + analyze_prof.total + minimization_prof.total + reduce_prof.total + gc_prof.total +
    init_prof.total;
  printf("c propagate           : %.2Lf%% (%.2Lf s)\n", 100. * propagate_prof.total / total_prof.total, propagate_prof.total / 1000000.);
  printf("c analyze             : %.2Lf%% (%.2Lf s)\n", 100. * analyze_prof.total / total_prof.total, analyze_prof.total / 1000000.);
  printf("c minimization        : %.2Lf%% (%.2Lf s)\n", 100. * minimization_prof.total / total_prof.total, minimization_prof.total / 1000000.);
  printf("c reduce              : %.2Lf%% (%.2Lf s)\n", 100. * reduce_prof.total / total_prof.total, reduce_prof.total / 1000000.);
  printf("c GC                  : %.2Lf%% (%.2Lf s)\n", 100. * gc_prof.total / total_prof.total, gc_prof.total / 1000000.);
  printf("c initialisation      : %.2Lf%% (%.2Lf s)\n", 100. * init_prof.total / total_prof.total, init_prof.total / 1000000.);
  printf("c ==================================================================\n");
  printf("c total verified      : %Lf s\n", total_prof.total / 1000000);
  printf("c total measured      : %.2Lf%% (%.2Lf s)\n", 100. * total_measure / total_prof.total, total_measure / 1000000.);
  printf("c unverified parsing  : %.2Lf%% (%.2Lf s)\n", 100. * parsing_prof.total / total_prof.total, parsing_prof.total / 1000000.);
#endif

  char res = -1;
  if (interrupted)
    res = 0;
  else if (unsatisfiable) {
    // add missing false clause
    if (proof) {
      proof_clause->used = 0;
      IsaSAT_Proofs_LLVM_log_start_new_clause_impl (0);
      isasat_print_ascii_clause ();
    }
    res = 20;
  }
  else {
    res = 10;
  }
  if (proof)
    fflush(proof), fclose(proof);
  return res;
}
