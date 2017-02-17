#include <cstdlib>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <algorithm>
#include <cassert>
#include <functional>
#include <limits>
#include <unordered_map>
#include <cstdint>
#include <thread>

#include <boost/progress.hpp>
#include <gperftools/profiler.h>

#include <atomic>

#include <chrono>

using namespace std;

void fail() {
  clog<<"FAILED"<<endl;
  exit(1);
}


template <typename T> void ensure_idx_valid(vector<T> &v, size_t i, T data) {
  if (i>=v.size()) {
    size_t ns = max(v.size() * 2, i+1);
    v.reserve(ns);
    v.resize(i+1, data);
  }
}

template <typename T> void cnt_increment(vector<T> &v, size_t i, T x = (T)1) {
  ensure_idx_valid(v,i,(T)(0));
  v[i]+=x;
}

template <typename T> void set_resize(vector<T> &v, size_t i, T data) {
  if (i>=v.size()) {
    size_t ns = max(v.size() * 2, i+1);
    v.resize(ns);
  }
  v[i] = data;
}

template<typename T> void del_from_list(vector<T> &v, T x) {
  for (size_t i=0;i<v.size();++i) {
    if (v[i] == x) {
      v[i]=v.back();
      v.pop_back();
      break; 
    }
  }
}


template <typename T> void inc_resize(vector<T> &v, size_t i) {
  if (i>=v.size()) {
    size_t ns = max(v.size() * 2, i+1);
    v.reserve(ns);
    v.resize(i+1);
  }
  ++v[i];
}



typedef int cdb_t;
typedef cdb_t lit_t;

inline size_t var_of(lit_t l) {return static_cast<size_t>(abs(l));}

bool cfg_core_first=true;
bool cfg_ignore_deletion=false;


enum item_type : cdb_t {
  INVALID = 0,
  UNIT_PROP = 1,    // id* 0                                  unit clause ids
  DELETION = 2,     // id                                     id to delete
  RUP_LEMMA = 3,    // id lit* 0 id* 0 id                     new-id clause units conflict-id
  RAT_LEMMA = 4,    // lit id lit* 0 id* 0 (id id* 0 id)* 0   reslit new-id clause units candidate-proofs
  CONFLICT = 5,     // id                                     conflict-id
  RAT_COUNTS = 6    // (lit num)* 0                           literal count
};


struct pos_t {
  size_t pos;
  pos_t(size_t _pos) : pos(_pos) {};
};


struct trail_item_t {
  lit_t l;
  lit_t * reason;
  bool vmarked;
};


template<typename T> class lit_map {
private:
  size_t max_var;
  vector<T> vec;
  T *m;
  
public:
  lit_map(size_t _max_var) : 
      max_var(_max_var)
    , vec(2*max_var + 1)
    , m(vec.data() + max_var)
    {}
  
  lit_map(lit_map const &lm) : max_var(lm.max_var), vec(lm.vec), m(vec.data() + max_var)
  {}
  
  lit_map &operator= (lit_map const &lm) {
    max_var = lm.max_var;
    vec=lm.vec;
    m = vec.data() + max_var;
  }
  
  T &operator [](lit_t l) { assert(static_cast<size_t>(abs(l)) <= max_var); return m[l];}
};


/*
 * 
 * 
 */
class ClauseDB {
private:
  vector<cdb_t> db;   // Stores 0-terminated clauses, in format "Id literals 0"
  
public:
  ClauseDB() = default;
  ClauseDB(ClauseDB const &) = default;
  ClauseDB &operator=(ClauseDB const &) = default;
  
  
  lit_t* p2c(pos_t pos) {
    assert(pos<=db.size());
    return db.data() + pos;
  }
  
  pos_t c2p(lit_t* cl) {
    assert(db.data()<=cl && cl <= db.data() + db.size());
    return cl - db.data();
  }
  
  pos_t current() {return db.size();}
  void append(lit_t l) {db.push_back(l);}
};



/*
 * Global data, which is constant after forward pass
 */
class Global_Data {
private:
  ClauseDB db;
  
  size_t num_clauses=0;
  size_t max_var=0;
  vector<lit_t> pivots;   // Map from clause ids to pivot literals
  vector<pos_t> items;    // List of items in DB
  size_t fst_prf_item=0;  // Index of first proof item
  size_t fst_lemma_id=0;  // Id of first lemma
  
  lit_t *conflict=nullptr;
  
  vector<pair<lit_t *,bool>> fwd_trail; // Forward trail, in format (clause, vmarked)
  vector<bool> on_fwd_trail;            // Whether clause is principal clause on forward trail
  
};

/*
 * Global data, which is synchronized between threads, or joined after thread's execution from thread's local data.
 * 
 */
class Synch_Data {
private:
  lit_map<size_t> rat_counts;  // Literal -> rat-count. Joined over thread results.  

  atomic<bool> *marked = nullptr;  // Whether clause is marked
  atomic_flag *acquired = nullptr; // Whether clause is/was acquired for verification by a worker thread
  
  vector<vector<cdb_t>*> proofs;   // Proof of this item (RUP or RAT proof). Synchronized by acquired.
};

/*
 * Parser that reads cnf and drat files
 * 
 */
class Parser {
private:
  struct Clause_Hash_Eq {
    ClauseDB &db;

    size_t operator() (const pos_t &pos) const; // Hash function
    bool operator() (const pos_t &pos1, const pos_t &pos2) const; // Equality
  };

  Clause_Hash_Eq cheq;  // Hash and equality function for claus-positions
  typedef unordered_multimap<pos_t,pos_t,Clause_Hash_Eq,Clause_Hash_Eq> clause_map_t;
  clause_map_t clause_map; // Map from clauses to their position
  
};



class Verifier {
private:
  ClauseDB db;
  
  lit_map<int> assignment; // Literal -> is-true


  vector<trail_item_t> trail;           // Trail: (literal, reason, marked)
  size_t processed = 0;                 // First unprocessed item on trail

  vector<size_t> vtpos;                 // Position on trail for set variables (var -> size_t)

  lit_map<vector<lit_t*>> watchlists;   // Maps literals to list of clauses watching this literal

  
public:
  Verifier(size_t max_var) : db(), assignment(max_var), trail(), vtpos(), watchlists(max_var) {}
  
  Verifier
  
  
};




/* Id lit1 ... litN 0 */
class ClauseDB {
  
public:  

  
private:
  vector<cdb_t> db;
  


  
  ClauseDB(const ClauseDB&) = delete;
  ClauseDB& operator= (const ClauseDB&) = delete;
  
private:

  
public:  
  ClauseDB();
  ~ClauseDB();
  
  lit_t *begin() {return &(*db.begin()) + 1;};
  lit_t *end() {return &(*db.end()) + 1;};
  
  lit_t *next(lit_t *l) { for (;*l;++l); return (l + 2); }
  
  size_t get_id(lit_t *l) { assert(l); return static_cast<size_t>(l[-1]); }
  pos_t get_del_pos(lit_t *l) { assert(l); return pos_t(static_cast<size_t>(l[0])); }

  lit_t *at_pos(pos_t pos) {assert(pos.pos); return &(db[pos.pos]);}; // Get reference from position. Warning: Invalidated if db is changed.
  pos_t current() {return pos_t(db.size() + 1);}

  
  size_t get_max_var() {return max_var;}
  
  size_t get_num_clauses() {return num_clauses;}
  pos_t parse_clause(istream &in);
  void parse_deletion(istream &in);

  void parse_dimacs(istream &in);
  void parse_proof(istream &in);
  
  

  void add_rat_counts(size_t const *counts);
  void set_conflict_clause(lit_t *cl) {conflict=cl;}
  
  lit_t get_pivot(size_t id) {return pivots[id];}
  lit_t get_pivot(lit_t *cl) {return pivots[get_id(cl)];}
  
  
  // Synchronization: Concurrently accessed
  bool is_marked(size_t id) { return marked[id]; }
  bool is_marked(lit_t *cl) { return is_marked(get_id(cl));}
  void mark_clause(size_t id) { marked[id]=true; }
  void mark_clause(lit_t *cl) { mark_clause(get_id(cl)); }

  bool is_on_fwd_trail(size_t id) { return on_fwd_trail[id]; }
  bool is_on_fwd_trail(lit_t *cl) { return is_on_fwd_trail(get_id(cl));}

  // Principal clause on forward trail
  void set_on_fwd_trail(size_t id) { on_fwd_trail[id] = true; }
  void set_on_fwd_trail(lit_t *cl) { set_on_fwd_trail(get_id(cl)); }
  void init_fwd_trail(vector<trail_item_t> const &tr);
  void vmark_fwd_trail(size_t i) { fwd_trail[i].second=true; }
  vector<pair<lit_t *,bool>> const &get_fwd_trail() {return fwd_trail;}

  // Try to acquire clause. True if successful.
  bool acquire(size_t id) { return !acquired[id].test_and_set(); }

  size_t get_fst_prf_item() {return fst_prf_item;}
  void set_proof_start() { fst_prf_item = items.size(); }
  vector<pos_t> const &get_items() {return items;}
  void erase_item(size_t i) { items[i] = 0;}
  
  // Synchronization: Never called concurrently for same indices, but possible for different indexes. 
  // Clause at this item must have been acquired by thread.
  vector<cdb_t> &init_proof(size_t item_idx) { assert(!proofs[item_idx]); proofs[item_idx] = new vector<cdb_t>(); return *proofs[item_idx]; }
  
  
  void dump_clause(lit_t *cl,ostream &out);
  void dump_proofs(ostream &out);
  void dump_compressed_drat(ostream &out);
};

ClauseDB::ClauseDB() : 
  db(), 
  pivots(), 
  items(), 
  
  on_fwd_trail(),
  
  proofs(), 
  rat_counts_vec(),
  rat_counts(nullptr),
  fwd_trail(),
  cheq{*this}, 
  clause_map(0,cheq,cheq)
{
  
}

ClauseDB::~ClauseDB() {
  if (marked) delete [] marked;
  if (acquired) delete [] acquired;
}



inline size_t ClauseDB::Clause_Hash_Eq::operator() (const pos_t &pos) const {
  size_t sum=0, prod=1, xxor=0; // The hash-function from drat-trim
  for (lit_t *l=db.at_pos(pos);*l;++l) {
    prod*=*l; sum+=*l; xxor^=*l;
  }
  return (1023 * sum + prod) ^ (31 * xxor);
}

inline bool ClauseDB::Clause_Hash_Eq::operator() (const pos_t &pos1, const pos_t &pos2) const {
  lit_t *l1 = db.at_pos(pos1);
  lit_t *l2 = db.at_pos(pos2);

  size_t i=0;
  do {
    if (l1[i]!=l2[i]) return false;
  } while (l1[i++]);
  return true;
}



pos_t ClauseDB::parse_clause(istream &in) {
  pos_t pos = current();
  size_t id = ++num_clauses;                    // Ids start at 1
  
  db.push_back(id);                             // Push id

  size_t len=0;
  
  lit_t l;  
  do {                                          // Push literals and terminating zero
    in>>ws; in>>l; db.push_back(l);
    max_var = max(var_of(l),max_var);
    ++len;
  } while (l);
  --len;

  set_resize<lit_t>(pivots,id,*at_pos(pos));    // Remember pivot
  sort(db.begin()+pos.pos, db.end() - 1);       // Sort
  clause_map.insert({ pos, pos });              // Add to clause_map
  items.push_back(pos);
  proofs.push_back(nullptr);
  
  
  return pos;
}

void ClauseDB::parse_deletion(istream &in) {
  pos_t pos = current();
  size_t csz = db.size();
  db.push_back(0);                              // Push 0-id

  lit_t l;
  do {                                          // Push literals and terminating zero
    in>>ws; in>>l; db.push_back(l);
  } while (l);
  
  
  sort(db.begin()+pos.pos, db.end() - 1);           // Sort
  auto orig_c = clause_map.find(pos.pos);
  
  if (orig_c == clause_map.end()) {
    clog<<"Ignoring deletion of non-existent clause (pos "<<pos.pos<<")"<<endl;
    db.resize(csz);
  } else {
    db.resize(csz+1);
    db.push_back(static_cast<cdb_t>(orig_c->second.pos));
    
    clause_map.erase(orig_c);
    items.push_back(pos);
    proofs.push_back(nullptr);
  }
}

inline void parse_ignore_comments(istream &in) {
  in>>ws;
  while (!in.eof()) {
    if (in.peek()!='c') break;
    in.ignore(numeric_limits<streamsize>::max(), '\n');
    in>>ws;
  }
}


void ClauseDB::parse_dimacs(istream &in) {
  in.exceptions(in.failbit|in.badbit);

  parse_ignore_comments(in);
  if (in.peek()=='p') in.ignore(numeric_limits<streamsize>::max(), '\n');

  while (!in.eof()) {
    parse_ignore_comments(in);
    if (in.eof()) break;

    parse_clause(in);
  }
  
  fst_lemma_id = num_clauses+1;
}


void ClauseDB::parse_proof(istream &in) {
  in.exceptions(in.failbit|in.badbit);

  parse_ignore_comments(in);
  if (in.peek()=='o') in.ignore(numeric_limits<streamsize>::max(), '\n');
  parse_ignore_comments(in);

  set_proof_start();
  
  
  while (!in.eof()) {
    parse_ignore_comments(in);
    if (in.eof()) break;

    if (in.peek()=='d') {
      in.get();
      parse_deletion(in);
    } else {
      parse_clause(in);
    }
  }

  // Initialize (global) rat counts
  rat_counts_vec.resize(2*get_max_var()+1, 0);
  rat_counts = rat_counts_vec.data() + get_max_var();
  
  
  // Initialize flags
  marked = new atomic<bool>[num_clauses + 1];
  for (size_t i=0;i<=num_clauses;++i) marked[i]=false;
  acquired = new atomic_flag[num_clauses + 1];
  for (size_t i=0;i<=num_clauses;++i) acquired[i].clear();
  on_fwd_trail.resize(num_clauses + 1, false);
}


void ClauseDB::add_rat_counts(size_t const *counts) {
  for (lit_t l = -get_max_var();l<=static_cast<lit_t>(get_max_var());++l) rat_counts[l] += counts[l];
}


void ClauseDB::init_fwd_trail(const vector< trail_item_t >& tr) {
  fwd_trail.clear();
  for (auto p : tr) fwd_trail.push_back({p.reason,false});
}


void ClauseDB::dump_clause(lit_t *cl,ostream &out) {
  for (lit_t *l=cl;*l;++l) out<<*l<<" ";
  out<<"0";
}


void ClauseDB::dump_compressed_drat(ostream &out) {
  for (pos_t pi : items) {
    if (pi.pos) {
      lit_t *cl = at_pos(pi);
      
      if (get_id(cl)) {
        if (is_marked(cl)) {
          out<<get_id(cl)<<" ";
          dump_clause(cl,out); out<<endl;
        }
      } else {
        pos_t dpi = get_del_pos(cl);
        lit_t *dcl = at_pos(dpi);
        if (is_marked(dcl)) {
          out<<"d " << get_id(dcl) << " // ";dump_clause(dcl,out); out<<endl;
          
        }
      }
    }
  }
    
}


void ClauseDB::dump_proofs(ostream &out) {
  // GRAT Header
  out<<"GRAT";
  out<<"b";
  out<<"t";
  out<<" "<<sizeof(cdb_t);
  out<<" 0"<<endl;


  // Conflict clause
  assert(conflict);
  out<<item_type::CONFLICT<<" "<<get_id(conflict)<<" 2"<<endl;
  
  // Proof items
  size_t i = items.size();
  size_t tri = fwd_trail.size();
  while (i>fst_prf_item) {
    --i;
    if (get_items()[i].pos) {
      
      lit_t *cl = at_pos(get_items()[i]);
      
      if (get_id(cl)) {
        // Clause
        if (is_on_fwd_trail(cl)) {
          size_t sz=0;
          // Look for clause on forward trail
          size_t ntri=tri;
          do { assert(ntri!=0); --ntri; } while (fwd_trail[ntri].first != cl);
          // Dump v-marked clauses as unit-props
          for (size_t j=ntri;j<tri;++j) {
            if (fwd_trail[j].second) {
              if (!sz) {
                out<<item_type::UNIT_PROP<<" "; ++sz;
              }
              out<<get_id(fwd_trail[j].first)<<" "; ++sz;
            }
          }
          if (sz) {
            out<<"0 "<<sz+1<<endl;
          }
          tri = ntri;
        }
        
        
        if (is_marked(cl)) {
          // Dump proof
          size_t j=0;
          size_t sz=0;
          vector<cdb_t> *prf = proofs[i];
          assert(prf);
          assert(prf->size() > 0);
          
          // TODO/FIXME Store proofs in more structured way, such that this clause-inserting hack becomes unnecessary!
          // Dump item type
          cdb_t itt = (*prf)[j++];
          out<<itt<<" "; ++sz;
          if (itt == item_type::RAT_LEMMA) {
            out<<(*prf)[j++]<<" ";++sz;
          }
          
          // Dump clause
          out<<get_id(cl)<<" ";++sz;
          for (lit_t *l = cl;*l;++l) {out<<*l<<" "; ++sz; }
          out<<"0"; ++sz;
          for (;j<prf->size();++j) {out<<" "<<(*prf)[j]; ++sz; }
          out<<" "<<sz<<endl;
        }
      } else {
        if (!cfg_ignore_deletion) {
          pos_t dpi = get_del_pos(cl);
          lit_t *dcl = at_pos(dpi);
          
          if (is_marked(dcl)) {
            out<<item_type::DELETION<<" "<<get_id(dcl)<<" 2"<<endl;
          }
        }
      }
    }
  }
  
  // Initial unit propagations
  {
    size_t sz=0;
    for (size_t j=0;j<tri;++j) {
      assert(get_id(fwd_trail[j].first) < fst_lemma_id);
      if (fwd_trail[j].second) {
        if (!sz) {
          out<<item_type::UNIT_PROP<<" "; ++sz;
        }
        out<<get_id(fwd_trail[j].first)<<" "; ++sz;
      }
    }
    if (sz) {
      out<<"0 "<<sz+1<<endl;
    }
  }

  // RAT counts
  size_t sz=0;
  out<<item_type::RAT_COUNTS; ++sz;
  for (lit_t l=-get_max_var(); l<=static_cast<lit_t>(get_max_var());++l) {
    if (rat_counts[l]) {
      out<<" "<<l<<" "<<rat_counts[l]; sz+=2;
    }
  }
  out<<" 0 "<< sz+1 <<endl;
}




class Trail {
private:
  ClauseDB &db;
  
  vector<int> assignment;   // Assignment vector
  int *A;                   // Mid-pointer into assignment data

  vector<trail_item_t> trail;    // Trail: (literal, reason, marked)
  size_t processed = 0;                 // First unprocessed item on trail
  size_t main_trail_size = 0;           // Current size of main trail
  vector<bool> mt_marked;               // Marked on main trail

  vector<size_t> vtpos;                // Position on trail for set variables

  vector<pair<lit_t,lit_t>> watched;   // Maps clause ids to watched literals
  vector<vector<lit_t*>> watchlists;   // Maps literals to list of clauses watching this literal
  vector<lit_t*> *WL;                  // Mid-pointer into watchlists
  
  
  inline void set_true(lit_t l) { 
    assert(!A[-l]); 
    A[l]=1;
  }
  inline void reset_true(lit_t l) { 
    assert(A[l]); 
    A[l]=0;
  }

  
public:
  Trail(ClauseDB &);

  Trail(const Trail &tr) : 
    db(tr.db), 
    assignment(tr.assignment), 
    A(assignment.data() + db.get_max_var()),
    trail(tr.trail),
    processed(tr.processed),
    main_trail_size(tr.main_trail_size),
    mt_marked(tr.mt_marked),
    vtpos(tr.vtpos),
    watched(tr.watched),
    watchlists(tr.watchlists),
    WL(watchlists.data() + db.get_max_var())
  {
  }


  Trail& operator=(const Trail &tr) {
    assert(&db == &tr.db);
    assignment = tr.assignment;
    A = assignment.data() + db.get_max_var();
    trail = tr.trail;
    processed=tr.processed;
    main_trail_size=tr.main_trail_size;
    mt_marked=tr.mt_marked;
    vtpos = tr.vtpos;
    watched=tr.watched;
    watchlists=tr.watchlists;
    WL = watchlists.data() + db.get_max_var();
    return *this;
  }
  
  // Keep original mt_marked
  void reinitialize(const Trail &tr) {
    assert(&db == &tr.db);
    assignment = tr.assignment;
    A = assignment.data() + db.get_max_var();
    trail = tr.trail;
    processed=tr.processed;
    main_trail_size=tr.main_trail_size;
    vtpos = tr.vtpos;
    watched=tr.watched;
    watchlists=tr.watchlists;
    WL = watchlists.data() + db.get_max_var();
  }
  
  
  inline bool is_true(lit_t l) {return A[l]!=0;}
  inline bool is_false(lit_t l) {return A[-l]!=0;}

  
  inline void assign_true(lit_t l, lit_t* reason) {
    assert(!is_true(l) && !is_false(l));
    set_true(l); 
    vtpos[var_of(l)] = trail.size();
    trail.push_back({l,reason,false}); 
  }

  
  inline size_t current_pos() {return trail.size();}
  template<typename T> void rollback(size_t pos, T const &ucr);
  template<typename T> void rollback(lit_t *l, T const &ucr);
  
  template<bool core_first> lit_t *propagate_units_aux();
  /*
    Do unit propagation, and return nullptr or conflict clause.
   */
  lit_t *propagate_units() {if (cfg_core_first) return propagate_units_aux<true>(); else return propagate_units_aux<false>(); }

  enum class acres_t { NORMAL, TAUT, CONFLICT };
  
  acres_t add_clause(lit_t *cl);
  void readd_clause(lit_t *cl); // Safe to call for syntactic units or conflict clauses (these have w1==w2==0)
  void rem_clause(lit_t *cl); // Remove clause from watchlist. Do not rollback trail, nor modify assignment. Safe to call for clauses not on watchlists.

  void mark_var(size_t v);     // Mark reason for this variable to be set, recursively
  void mark_clause(lit_t *l);  // Mark literals in clause recursively. 


  void get_rat_candidates(std::vector< lit_t* >& cands, lit_t pivot);
  
  void dbg_check_no_units();
  
  
  inline vector<trail_item_t> const &get_trail() const {return trail;}
  
  // Called after forward pass, to declare current trail as main trail
  void init_main_trail();
  
  void join_vmarked();
  
};


Trail::Trail(ClauseDB &_db) : 
  db(_db), 
  assignment(2*db.get_max_var() + 1), 
  A(assignment.data() + db.get_max_var()), 
  trail(), 
  
  mt_marked(),
  vtpos(db.get_max_var()+1,0),
  
  watched(db.get_num_clauses() + 1),
  watchlists(2*db.get_max_var() + 1),
  WL(watchlists.data() + db.get_max_var())
  
{} 

inline void Trail::mark_var(size_t v) {
  assert(is_true(v) || is_false(v));
  size_t pos = vtpos[v];
  
  if (!trail[pos].vmarked) {
    trail[pos].vmarked=true;
    
    if (pos < main_trail_size) mt_marked[pos]=true; // Store marking on main trail. Only effective after init_main_trail(), as otherwise, main_trail_size==0.
    
    if (trail[pos].reason) mark_clause(trail[pos].reason);
  }
}

void Trail::mark_clause(lit_t *l) {
  db.mark_clause(l);
//   ++cnt_marked;
  
  for (;*l;++l) {    
    mark_var(var_of(*l));
  }
}

void Trail::init_main_trail() {
  mt_marked.resize(trail.size(),false);
  main_trail_size = trail.size();

  // Initialize vmarked from forward pass. TODO: Separate initialization of DB after forward pass, including transfer of marked. Then, vmarked only needs to keep track of (parallel) bwd info
  for (size_t i=0;i<trail.size();++i) if (trail[i].vmarked) mt_marked[i]=true;
}

template<typename T> void Trail::rollback(size_t pos, T const &ucr) {
  for (size_t i=pos;i<trail.size();++i) {
    lit_t l = trail[i].l;
    lit_t *reason = trail[i].reason;
    
    reset_true(l);
    if (trail[i].vmarked && reason) {
      ucr(reason);
    }
  }

  trail.resize(pos);
  if (processed>trail.size()) processed=trail.size();

  if (main_trail_size > trail.size()) main_trail_size = trail.size();
}

template<typename T> void Trail::rollback(lit_t *cl, T const &ucr) {
  size_t i=trail.size();

  // Search clause on trail
  do {
    if (i==0) {
      clog<<"rollback with clause not on trail"<<endl; 
      fail();
    }
    
    --i;
  } while (trail[i].reason != cl);
  
  rollback(i,ucr);
}

template<bool cf_enabled> lit_t *Trail::propagate_units_aux() {
  size_t cf_processed = processed;

  bool cf_mode = cf_enabled;
  
  while (true) {
    size_t &ti = cf_mode?cf_processed:processed;
    
    if (ti == trail.size()) { // Processed all clauses without finding conflict
      if (cf_mode) cf_mode=false; // In cf_mode, switch to non-cf mode
      else { // In non-cf mode, return "no conflict found"
        return nullptr;
      }
    } else {
      lit_t l = trail[ti].l;
      ++ti;
      
      l=-l; // Negated literal has been set to false
      
      vector<lit_t*> &watchlist = WL[l];
      
      
      for (size_t i=0;i<watchlist.size();++i) {
        lit_t *cl = watchlist[i];
        
        // In cf_mode, ignore unmarked clauses
        /* FIXME: We would also like to ignore already processed clauses in non-cf mode.
         * However, we cannot use marked for that, as this may concurrently switch from false->true!
         */
        if (cf_enabled && cf_mode && !db.is_marked(cl)) continue;  
        
        size_t id = db.get_id(cl);
        
        lit_t w1 = watched[id].first; 
        lit_t w2 = watched[id].second;

        //if (w1==l) swap(w1,w2);     // Normalize on w2 being set literal
        if (w1==l) { 
          w1=w2; w2=l; 
        }
        assert(is_false(w2));
        if (is_true(w1)) continue;
        
        
        // Scan through clause and try to find new watched literal
        lit_t *w = nullptr;
        for (lit_t *ll=cl;*ll;++ll) {
          if (*ll!=w1 && !is_false(*ll)) {w=ll; break;}
        }
        
        if (w) { // Found new watchable literal
          // Set new watched
          WL[*w].push_back(cl);
          watched[id]={w1,*w};
          
          // Remove this clause from old watchlist
          watchlist[i] = watchlist.back();
          watchlist.pop_back();
          --i;
          continue;
        } else if (!is_false(w1)) { // Found unit clause
          assign_true(w1,cl);
          
          if (cf_enabled && !cf_mode) {               // If we find a unit in non-cf_mode, switch back to cf-mode
            --ti; // Repeat on this literal, as we have not completed it FIXME: Better complete this literal, or store intermediate state?
            cf_mode=true; break;
          }
          
          continue;
        } else { // Found conflict clause
          return cl;
        }
      }
    }
  }
  
  
}



Trail::acres_t Trail::add_clause(lit_t *cl) {
  // Search for watched literals
  lit_t *w1=nullptr, *w2=nullptr;
  
  for (lit_t *l = cl; *l; ++l) {
    if (is_true(*l)) return acres_t::TAUT; // Ignoring tautology.
    if (!is_false(*l)) {
      if (!w1) w1=l; else if (!w2 && *l!=*w1) w2=l;
    }
  }

  auto id = db.get_id(cl);
  assert(id);

  if (!w1) { // Conflict
    watched[id]={0,0};    // Dummy assignment to watched literals
    return acres_t::CONFLICT;
  } else if (!w2) { // Unit, *w1 is unit literal
    watched[id]={0,0};    // Dummy assignment to watched literals
    assign_true(*w1,cl);
    db.set_on_fwd_trail(cl); // Clause becomes principal clause on forward trail
    return acres_t::NORMAL;
  } else { // >1 undec
    watched[id]={*w1,*w2};
    WL[*w1].push_back(cl);
    WL[*w2].push_back(cl);
    return acres_t::NORMAL;
  }
}

void Trail::readd_clause(lit_t *cl) {
  auto id = db.get_id(cl);
  
  assert(id);
  
  lit_t w1 = watched[id].first;
  lit_t w2 = watched[id].second;

  assert (!w1 == !w2);
  
  if (w1) {
    WL[w1].push_back(cl); 
    WL[w2].push_back(cl);
  }
}



void Trail::rem_clause(lit_t *cl) {
  auto id = db.get_id(cl);
  assert(id);

  lit_t w1 = watched[id].first;
  lit_t w2 = watched[id].second;

  assert (!w1 == !w2);

  if (w1) {
    del_from_list(WL[w1],cl);
    del_from_list(WL[w2],cl);
  }
}


void Trail::get_rat_candidates(vector<lit_t*> &cands, lit_t pivot) {
  pivot=-pivot;
  
  for (lit_t l = -db.get_max_var();l<=static_cast<lit_t>(db.get_max_var());++l) {
    for (auto cl : WL[l]) {
      if (watched[db.get_id(cl)].first == l) {
        for (lit_t *ll=cl; *ll; ++ll) {
          if (*ll == pivot) cands.push_back(cl);
        }
      }
    }
  }
}


void Trail::join_vmarked() {
  assert(mt_marked.size() == db.get_fwd_trail().size());
  
  for (size_t i=0;i<mt_marked.size();++i) {
    if (mt_marked[i]) db.vmark_fwd_trail(i);
  }
}



void Trail::dbg_check_no_units() {
  size_t nc=0;
  for (lit_t l = -db.get_max_var();l<=static_cast<lit_t>(db.get_max_var());++l) {
    for (auto cl : WL[l]) {
      if (watched[db.get_id(cl)].first == l) {
        ++nc;
        size_t n_undec = 0;
        size_t n_true = 0;
        for (lit_t *ll=cl; *ll; ++ll) {
          if (is_true(*ll)) ++n_true;
          else if (!is_false(*ll)) ++n_undec;
        }
        
        if (n_true==0 && n_undec == 1) {
          clog<<"Still unit clauses to propagate"<<endl;
          fail();
        }
        
        if (n_true==0 && n_undec==0) {
          clog<<"Conflict got undetected"<<endl;
          fail();
        }
        
      }
    }
  }
}



class Verifier {
private:
  ClauseDB &db;
  Trail tr;
  vector<size_t> rat_counts_vec;
  size_t *rat_counts;
  size_t num_acquired = 0;
  
  Verifier() = delete;

  lit_t *fwd_pass_aux();
  
public:
  Verifier(ClauseDB &);

  Verifier(Verifier const& vrf) : 
    db(vrf.db), 
    tr(vrf.tr), 
    rat_counts_vec(vrf.rat_counts_vec), 
    rat_counts(rat_counts_vec.data() + db.get_max_var()), 
    num_acquired(vrf.num_acquired)
  {};
  Verifier &operator=(Verifier const&) = delete;
  
  // Keep rat counts and vmarked of trail
  void reinitialize(const Verifier &vrf) {
    assert(&db == &vrf.db);
    tr.reinitialize(vrf.tr);
  }
  
  
  void verify(lit_t *cl, vector<lit_t> &prf);
  
  lit_t *fwd_pass();
  
  void bwd_pass(size_t range_lower, size_t range_upper, bool status_bar = false);
  void bwd_pass() { bwd_pass(db.get_fst_prf_item(), db.get_items().size(), true); }
  
  
  void parallel_bwd(size_t num_threads);
  
//   size_t const* get_rat_counts() {return rat_counts;};
  
  // Join info of this verifier to DB. Not thread-safe!
  void join_info(); 

  size_t get_num_acquired() const {return num_acquired;}
  
  
};


Verifier::Verifier(ClauseDB &_db) : db(_db), tr(db), rat_counts_vec(2*db.get_max_var()+1), rat_counts(rat_counts_vec.data() + db.get_max_var()) {
  
}

struct push_clause_ids {
  ClauseDB &db;
  vector<lit_t> &prf;
  push_clause_ids(ClauseDB &_db, vector<lit_t> &_prf) : db(_db), prf(_prf) {};
  
  void operator () (lit_t *cl) const { prf.push_back(static_cast<lit_t>( db.get_id(cl))); }
};


void Verifier::verify(lit_t *cl, vector<lit_t> &prf) {
  push_clause_ids pci (db,prf);
  
  size_t orig_pos = tr.current_pos();
  lit_t pivot = db.get_pivot(cl);
  bool pivot_false = tr.is_true(pivot); // FIXME: is_false!

  // Falsify literals
  for (lit_t *l = cl; *l; ++l) {
    assert(!tr.is_true(*l)); // Tautologies should have been ignored
    if (!tr.is_false(*l)) tr.assign_true(-(*l),nullptr);
  }
  
  // Unit propagation
  lit_t *conflict = tr.propagate_units();
  
  if (conflict) { // RUP-check succeeded
    tr.mark_clause(conflict);
    prf.push_back(item_type::RUP_LEMMA);
    tr.rollback(orig_pos, pci);
    prf.push_back(0);
    prf.push_back(static_cast<cdb_t>(db.get_id(conflict)));
    
  } else {
    vector<cdb_t> rat_prf;
    push_clause_ids rpci (db,rat_prf);
    // RUP-check failed, do RAT check
    if (pivot_false) {clog<<"RAT check failed due to false pivot"<<endl; fail();}
    rat_counts[pivot]++;
    
    // Gather clauses containing pivot
    vector<lit_t*> cands;
    tr.get_rat_candidates(cands,pivot);

    size_t rat_pos = tr.current_pos();
    // Iterate over candidates
    
    for (auto ccl : cands) {
      // Falsify literals and check blocked
      bool blocked=false;
      for (lit_t *l = ccl;*l;++l) {
        if (*l == -pivot) continue;
        if (tr.is_true(*l)) {
          tr.mark_var(var_of(*l));  // Mark clauses that caused this clause to be blocked
          tr.rollback(rat_pos,[](lit_t *) {return;});
          blocked=true;
          break;
        } else {
          if (!tr.is_false(*l)) tr.assign_true(-(*l),nullptr);
        }
      }
      if (!blocked) {
        lit_t *conflict = tr.propagate_units();
        if (!conflict) {
          clog<<"RAT-check failed"<<endl; 
          fail();
        }
        tr.mark_clause(conflict);
        
        
        rat_prf.push_back(static_cast<cdb_t>(db.get_id(ccl)));
        tr.rollback(rat_pos,rpci); 
        rat_prf.push_back(0);
        rat_prf.push_back(static_cast<cdb_t>(db.get_id(conflict)));
      }
    }
    
    // RAT-check succeeded
    prf.push_back(item_type::RAT_LEMMA);
    prf.push_back(pivot);
    tr.rollback(orig_pos,pci);
    prf.push_back(0);
    for (auto x : rat_prf) prf.push_back(x);
    prf.push_back(0);
  }
}


lit_t *Verifier::fwd_pass_aux() {
  // Add clauses of formula
  for (size_t i=0;i<db.get_fst_prf_item();++i) {
    if (db.get_items()[i].pos) {
      lit_t *cl = db.at_pos(db.get_items()[i]);
      assert(db.get_id(cl));
      
      switch (tr.add_clause(cl)) {
        case Trail::acres_t::TAUT:
          db.erase_item(i);  
          break;
        case Trail::acres_t::CONFLICT: return nullptr; // Trivial conflict in clauses
        default:;  
      }
    }
  }
  
  lit_t *conflict = tr.propagate_units_aux<false>();
  if (conflict) {
    // Conflict after unit-propagation on initial clauses
    return conflict;
  }
  
  // Add lemmas
  for (size_t i=db.get_fst_prf_item();i<db.get_items().size();++i) {
    if (db.get_items()[i].pos) {
      lit_t *cl = db.at_pos(db.get_items()[i]);
      if (db.get_id(cl)) {
        
        switch (tr.add_clause(cl)) {
          case Trail::acres_t::TAUT:
            db.erase_item(i);
            break;
          case Trail::acres_t::CONFLICT:
            tr.mark_clause(cl);
            return cl;
          case Trail::acres_t::NORMAL: {
            conflict = tr.propagate_units();
            if (conflict) {
              tr.mark_clause(conflict);
              return conflict;
            }
          }
        }
      } else {
        if (!cfg_ignore_deletion) {
          pos_t dpi = db.get_del_pos(cl);
          tr.rem_clause(db.at_pos(dpi));
        }
      }
    }
  }
  
  clog << "Forward pass found no conflict" << endl; 
  fail();
  return nullptr; // Unreachable, but not detected by gcc. Adding this to silence warning.
}

lit_t *Verifier::fwd_pass() {
  lit_t *conflict = fwd_pass_aux();

  // Store a copy of the main trail at db
  db.init_fwd_trail(tr.get_trail());
  
  // Declare current trail as main trail
  tr.init_main_trail();

  db.set_conflict_clause(conflict);

  return conflict;
}

void Verifier::bwd_pass(size_t range_lower, size_t range_upper, bool status_bar) {

  assert(range_lower >= db.get_fst_prf_item());
  
  // Iterate over lemmas
  boost::progress_display *pdsp = status_bar?new boost::progress_display(db.get_items().size() - db.get_fst_prf_item()) : nullptr;
  {
    size_t i = db.get_items().size();
    while (i>range_lower) {
      --i;
      
      if (pdsp) ++*pdsp;
      
      
      
      if (db.get_items()[i].pos) {
        
        lit_t *cl = db.at_pos(db.get_items()[i]);
        size_t id = db.get_id(cl);
        
        if (id) { // Lemma
          
          // Remove from 2wl
          tr.rem_clause(cl);

          // Remove from trail
          if (db.is_on_fwd_trail(cl)) {
            tr.rollback(cl,[](lit_t *) {return;});
          }
          
          if (db.is_marked(cl)) {
            if (i<range_upper) { // Only try to prove lemmas in range
              // Try to acquire lemma. If succeeded, verify. Otherwise, someone else is already verifying this.
              if (db.acquire(id)) {
                ++num_acquired;
                verify(cl,db.init_proof(i));
              }
            }
          }
        } else { // Deletion
          if (!cfg_ignore_deletion) {
            pos_t dpi = db.get_del_pos(cl);
            tr.readd_clause(db.at_pos(dpi));
          }
        }
      }
    }
  }
  
  
}

class aux_bwd_pass {
private:
  Verifier vrf;
  const Verifier &master;
  
  const atomic<bool> &completed;
  size_t range_lower;
  size_t range_upper;
  
  size_t num_iterations = 0;
  
  aux_bwd_pass(const aux_bwd_pass &) = delete;
  aux_bwd_pass &operator = (const aux_bwd_pass &) = delete;
  
public:
  aux_bwd_pass(const Verifier &_master, const atomic<bool> &_completed, size_t _range_lower, size_t _range_upper)
    : vrf(_master), master(_master), completed(_completed), range_lower(_range_lower), range_upper(_range_upper)
    {}
  
  void operator() () {
    if (!completed) {
      ++num_iterations;
      vrf.bwd_pass(range_lower, range_upper);
      while (!completed) {
        //clog<<"#"<<num_iterations<<endl;
        ++num_iterations;
        vrf.reinitialize(master);
        vrf.bwd_pass(range_lower, range_upper);
      }
    }
  }

  size_t get_num_iterations() const {return num_iterations;}
  size_t get_num_acquired() const {return vrf.get_num_acquired();}
  
  void join_info() {vrf.join_info();}
  
};



void Verifier::parallel_bwd(size_t num_threads) {
  assert(num_threads);
  
  atomic<bool> completed; completed=false;
  
  Verifier master = *this;
  
  vector<aux_bwd_pass*> aux_vrfs;
  vector<thread> vrf_threads;
  
  
  for (size_t i=0;i<num_threads-1;++i) {
    // ATTENTION Currently, all threads must run to range_lower = fst-prf-item, otherwise, marked lemmas may be left unverified!
    size_t range_lower = db.get_fst_prf_item();
    size_t range_upper = db.get_items().size() + num_threads - i;
    
    
    aux_vrfs.push_back(new aux_bwd_pass(master, completed, range_lower, range_upper));
    
    clog<<"Auxiliary thread #"<<i<<" for range "<<range_lower<<" - "<<range_upper<<endl;
    
    aux_bwd_pass *abp = aux_vrfs[i];
    
    vrf_threads.push_back(thread([abp]() { (*abp)(); }));
  }
  
  clog<<"Main thread for whole range "<<db.get_fst_prf_item()<<" - "<<db.get_items().size()<<endl;
  
  bwd_pass();
  completed=true;
  
  for (auto &t : vrf_threads) t.join();
  
  for (size_t i=0;i<aux_vrfs.size();++i) {
    auto vrf = aux_vrfs[i];
    vrf->join_info();
    clog<<"Aux thread #"<<i<<" verified "<<vrf->get_num_acquired()<<" lemmas in "<<vrf->get_num_iterations()<<" iterations" << endl;
    delete vrf;
  }
  
  join_info();
  clog<<"Main thread verified "<<get_num_acquired()<<" lemmas"<<endl;
}




void Verifier::join_info() {
  tr.join_vmarked();
  db.add_rat_counts(rat_counts);
}


void print_usage() {
  cerr<<"Usage gratgen <dimacs-file> <proof-file> <options>"<<endl;
    cerr<<"Options:"<<endl;
    cerr<<"  -u, --no-core-first    Normal (no core first) unit propagation"<<endl;
    cerr<<"  -o name                Name of GRAT-file. /dev/stdout by default."<<endl;
    cerr<<"  -p, --no-deletion      Ignore deletion of clauses"<<endl;
    cerr<<"  -j, --num-parallel     Number of parallel threads to use"<<endl;
}

void print_info() {
  cerr<<"sizeof(cdb_t) = "<<sizeof(cdb_t)<<endl;
  cerr<<"sizeof(cdb_t*) = "<<sizeof( cdb_t* )<<endl;
}


int main(int argc, char **argv) {

  print_info();

  if (argc<3) {print_usage(); return 2;}

  string dimacs_file = argv[1];
  string proof_file = argv[2];
  string grat_file="/dev/stdout";  // TODO: Make this more portable
  string cdrat_file="";         // TODO: Make this more portable

  size_t num_parallel = thread::hardware_concurrency();
  
  for (int i=3;i<argc;++i) {
    string a = argv[i];
    
    if (a=="-u" || a=="--no-core-first") cfg_core_first = false;
    else if (a=="-p" || a=="--no-deletion") cfg_ignore_deletion = true;
    else if (a=="-j" || a=="--num_parallel") {
      ++i; if (i>=argc) {cerr<<"Expecting argument for "<<a<<endl; fail();}
      num_parallel = stoul(argv[i]);
      if (!num_parallel) {cerr<<"Invalid number of parallel threads "<<num_parallel<<endl; fail();}
    }
    else if (a=="-o") {
      ++i; if (i>=argc) {cerr<<"Expecting argument for -o"<<endl; fail();}
      grat_file=argv[i];
    } else if (a=="-d") {
      ++i; if (i>=argc) {cerr<<"Expecting argument for -d"<<endl; fail();} 
      cdrat_file=argv[i];
    } else {
      cerr<<"Unknown command line argument: "<<a<<endl; fail();
    }
  }
  
  ofstream grat_out(grat_file);
  grat_out.exceptions(grat_out.badbit | grat_out.failbit);
  
  

  ClauseDB db;
  
  {
    clog<<"Parsing formula ..."; clog.flush();
    ifstream fs(dimacs_file,ifstream::in); 
    db.parse_dimacs(fs);
    fs.close();
    clog<<" done."<<endl; clog.flush();
  }
  
  {
    clog<<"Parsing proof ..."; clog.flush();
    ifstream fs(proof_file,ifstream::in); 
    db.parse_proof(fs);
    fs.close();
    clog<<" done."<<endl; clog.flush();
  }

  
  Verifier vrf(db);
  clog<<"Forward pass ..."; clog.flush();
  lit_t *conflict = vrf.fwd_pass();
  clog<<" done."<<endl; clog.flush();
  
  if (conflict) {
    clog<<"Backwards pass:"<<endl; clog.flush();
//     ProfilerStart("/tmp/prof.out");
    auto t = chrono::steady_clock::now();
    vrf.parallel_bwd(num_parallel);
    auto d = chrono::steady_clock::now() - t;
//     ProfilerStop();
    clog<<" done. "<< chrono::duration_cast<chrono::milliseconds>(d).count() <<"ms"<<endl; clog.flush();
    
    clog<<"Writing GRAT ..."; clog.flush();
    db.dump_proofs(grat_out);
    clog<<" done."<<endl; clog.flush();
  } else {
    clog<<"Trivial conflict in clauses."<<endl;
  }

  if (cdrat_file != "") {
    ofstream cdrat_out(cdrat_file);
    db.dump_compressed_drat(cdrat_out);
    cdrat_out.close();
  }
  
  
//   clog<<"cnt_lemmas = "<<cnt_lemmas<<endl;
  
  return 0;
}

