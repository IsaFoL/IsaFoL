#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <ctype.h>
#include <stdint.h>
#include <string.h>

/*the parser is based on the code from lingeling*/

typedef struct CLAUSE {
  int64_t size;
  struct {
    int64_t used;
    uint32_t* clause;
  };
} CLAUSE;


typedef struct CLAUSES {
  int64_t size;
  CLAUSE* clauses;
} clauses, CLAUSES;


static char * inputname;
static FILE * inputfile;

static int lineno;

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
  clauses.size = size;
  clauses.clauses = (CLAUSE *) malloc((size+1) * sizeof(CLAUSE));
  for (int64_t n = 0; n < size; ++n) {
    clauses.clauses[n] = new_empty_clause();
  }
  return clauses;
}


void free_clauses (CLAUSES *cl) {
  for (int64_t n = 0; n < cl->size; ++n) {
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
  for(int i = 0; i < cl->size; ++i)
    print_clause(&cl->clauses[i]);
}

static int64_t next (void) {
  int64_t res;
  res = getc (inputfile);
  if (res == '\n') lineno++;
  return res;
}

static CLAUSES parse (void) {
  int ch;
  int32_t lit;
  int32_t sign;
  int64_t num_lits, num_clss;
HEADER:
  ch = next ();
  if (ch == EOF) perr ("unexpected end-of-file in header");
  if (ch == 'c') {
    while ((ch = next ()) != '\n')
      if (ch == EOF)
	perr ("unexpected end-of-file in header comment");
    goto HEADER;
  }
  if (ch != 'p' ||
      next () != ' ' ||
      next () != 'c' ||
      next () != 'n' ||
      next () != 'f' ||
      next () != ' ') perr ("invalid header (expected 'p cnf ')");

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
    ch = next (); goto CLAUSES;
  }
  if (ch == 'c') {
    while ((ch = next ()) != '\n')
      if (ch == EOF)
	perr ("unexpected end-of-file in body comment");
    goto CLAUSES;
  }
  if (ch == EOF) goto DONE;
  if (ch == '0') {
    if(clause_num > num_clss)
      perr("found too many clauses: clause  number %d, only %d expected", clause_num, num_clss);
    clauses.clauses[clause_num++] = copy_clause(&cl);
    cl.used = 0;

    ch = next ();
    goto CLAUSES;
  }
  if (ch == '-') {
    sign = -1;
    ch = next ();
    if (!isdigit (ch)) perr ("expected digit after '-'");
  } else sign = 1;

  if (!isdigit (ch) || ch == 0) perr ("expected literal");

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
  printf("c propagations %ld\n", props);
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
declare void @IsaSAT_Show_LLVM_print_uint64_impl(i64)
declare void @print_phase(i64)
*/
void IsaSAT_Show_LLVM_print_c_impl() {
  printf("\nc ");
}

void IsaSAT_Show_LLVM_print_uint64_impl(int64_t p) {
  printf(" %ld ", p);
}

int main(int argc, char *argv[]) {
  if(argc != 2) {
    printf("expected one argument");
    return 0;
  }
  inputname = argv[1];
  inputfile = fopen (inputname, "r");

  if(inputfile == NULL) {
    printf("could not open file %s", inputname);
    exit(EXIT_FAILURE);
  }

  CLAUSES clauses = parse();

  //print_clauses(&clauses);
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