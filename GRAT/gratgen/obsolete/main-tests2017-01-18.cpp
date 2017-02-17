/*
  gratgen -- check DRAT proof files and generate GRAT-certificates
  Author: Peter Lammich
  Some ideas borrowed from the drat-trim tool.

  Features:
    * Backwards checking with core-first unit propagation
    * Generation of trimmed GRAT-certificates
    * Parallel checking

  Lacking features of drat-trim:
    * Forward checking (Could be added, but would probably mess up some code)
    * Binary proof format (Can easily be added)
    * Optimal deletion placement (Probably not important for GRAT-certificate checking)

*/


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
#include <atomic>
#include <chrono>

#include <boost/progress.hpp>
#include <gperftools/profiler.h>


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

/**
 * Delete one x from (unordered) list. Returns true if an x was deleted, false if no x was found.
 */
template<typename T> bool del_from_list(vector<T> &v, T x) {
  for (size_t i=0;i<v.size();++i) {
    if (v[i] == x) {
      v[i]=v.back();
      v.pop_back();
      return true;
    }
  }
  return false;
}


template <typename T> void inc_resize(vector<T> &v, size_t i) {
  if (i>=v.size()) {
    size_t ns = max(v.size() * 2, i+1);
    v.reserve(ns);
    v.resize(i+1);
  }
  ++v[i];
}


template<typename RT, typename T> RT with_timing(string name, T op, chrono::milliseconds *dp = nullptr, ostream &out = clog) {
  RT r;
  out<<name<<" ..."; out.flush();
  auto t = chrono::steady_clock::now();
  r=op();
  auto d = chrono::steady_clock::now() - t;
  chrono::milliseconds dm = chrono::duration_cast<chrono::milliseconds>(d);
  if (dp) *dp=dm;
  out<<" "<< dm.count() <<"ms"<<endl; out.flush();
  return r;
}

template<typename T> void with_timing(string name, T op, chrono::milliseconds *dp = nullptr, ostream &out = clog) {
  out<<name<<" ..."; out.flush();
  auto t = chrono::steady_clock::now();
  op();
  auto d = chrono::steady_clock::now() - t;
  chrono::milliseconds dm = chrono::duration_cast<chrono::milliseconds>(d);
  if (dp) *dp=dm;
  out<<" "<< dm.count() <<"ms"<<endl; out.flush();
}







typedef int cdb_t;
typedef cdb_t lit_t;

inline size_t var_of(lit_t l) {return static_cast<size_t>(abs(l));}

bool cfg_core_first=true;
bool cfg_ignore_deletion=false;
bool cfg_no_proof=false;
bool cfg_assume_nodup=false;
bool cfg_show_progress_bar=true;


chrono::milliseconds stat_parsing_time(0);
chrono::milliseconds stat_checking_time(0);
chrono::milliseconds stat_bwd_checking_time(0);
chrono::milliseconds stat_writing_time(0);
chrono::milliseconds stat_overall_time(0);
chrono::milliseconds stat_overall_vrf_time(0);

size_t stat_itemlist_size(0);
size_t stat_pivots_size(0);
size_t stat_db_size(0);


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
  pos_t() : pos(0) {};
  explicit pos_t(size_t _pos) : pos(_pos) {};
  
  operator bool() const {return pos!=0;}
  bool operator==(pos_t const&p) const {return pos == p.pos;}
  
  static pos_t null;
};

pos_t pos_t::null = pos_t(0);


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
  lit_map(size_t _max_var = 0) : 
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
    return *this;
  }

  void resize(size_t _max_var) {
    max_var = _max_var;
    vec.resize(2*max_var + 1);
    m = vec.data() + max_var;
  }
  
  
  T &operator [](lit_t l) { assert(static_cast<size_t>(abs(l)) <= max_var); return m[l];}

  const T &operator [](lit_t l) const { assert(static_cast<size_t>(abs(l)) <= max_var); return m[l];}
  
  size_t get_max_var() const {return max_var;}
  lit_t lbegin() const {return -static_cast<lit_t>(max_var);}
  lit_t lend() const {return static_cast<lit_t>(max_var) + 1;}

  
  
};


/*
 * 
 * 
 */
class ClauseDB {
private:
  vector<cdb_t> db;   // Stores 0-terminated clauses, in format "Id literals 0". Clause pointers always point to first literal.
  
public:
  ClauseDB() : db() {}
  ClauseDB(ClauseDB const &x) : db(x.db) {
  };
  ClauseDB &operator=(ClauseDB const &x) {
    db = x.db;
    return *this;
  };
  
  
  lit_t *p2c(pos_t pos) {
    assert(pos<=db.size());
    return pos?db.data() + pos.pos:nullptr;
  }

  lit_t const *p2c(pos_t pos) const {
    assert(pos<=db.size());
    return pos?db.data() + pos.pos:nullptr;
  }
  
  vector<cdb_t>::iterator p2i(pos_t pos) {
    assert(pos && pos<=db.size());
    return db.begin() + pos.pos;
  }
  
  vector<cdb_t>::const_iterator p2i(pos_t pos) const {
    assert(pos && pos<=db.size());
    return db.begin() + pos.pos;
  }
  
  
  pos_t c2p(lit_t *cl) const {
    if (cl) {
      assert(db.data()<=cl && cl <= db.data() + db.size());
      return pos_t(cl - db.data());
    } else return pos_t(0);
  }
  
  pos_t current() const {return pos_t(db.size());}
  void append(lit_t l) {
    db.push_back(l);
  }
  
  void shrink_to(pos_t pos) { assert(pos.pos <= current().pos); db.resize(pos.pos); }
  void shrink_to(vector<cdb_t>::iterator end) { assert(end >= db.begin() && end<=db.end()); db.erase(end,db.end()); }

  vector<cdb_t> const &get_db() const {return db;}
  vector<cdb_t> &get_db() {return db;}
};


inline size_t clid(lit_t *cl) {assert(cl); return static_cast<size_t>(cl[-1]);}
inline lit_t &clw1(lit_t *cl) {assert(cl && cl[0]!=0 && cl[1]!=0); return cl[0]; }
inline lit_t &clw2(lit_t *cl) {assert(cl && cl[0]!=0 && cl[1]!=0); return cl[1]; }


class item_t {
private:
//   bool deletion;  // Wether item is deletion
  pos_t pos;      // Position of referenced clause (added or deleted clause), null if erased
  size_t trpos;   // [Position on forward trail + 1, 0 if not unit] | del-flag

public:
  item_t(bool _deletion, pos_t _pos) : pos(_pos), trpos(_deletion?1:0) {}
  // Items can be erased later, e.g., if they are tautologies
  bool is_erased() const {return !pos;}
  void erase() {pos=pos_t::null;}

  bool is_deletion() const {assert(!is_erased()); return trpos&0x1;}
  pos_t get_pos() const {assert(!is_erased()); return pos;}
  
  bool has_tr_pos() const {assert(!is_erased()); return trpos>>1!=0;}
  size_t get_trpos() const {assert(has_tr_pos()); return (trpos>>1) - 1; }
  void set_trpos(size_t _trpos) {assert(!is_erased()); trpos = ((_trpos + 1)<<1) | (trpos&0x1);}
  
  
};


class Parser;
class Synch_Data;

/*
 * Global data, which is constant after forward pass
 */
class Global_Data {
  friend Parser;
  
private:
  ClauseDB db;

  ///// This data is set by friend Parser
  size_t num_clauses=0;
  size_t max_var=0;
  vector<lit_t> pivots;   // Map from clause ids to pivot literals
  vector<item_t> items;   // List of items in DB
  size_t fst_prf_item=0;  // Index of first proof item
  size_t fst_lemma_id=0;  // Id of first lemma
  /////
  
  lit_t *conflict=nullptr;
  
  vector<pair<size_t,bool>> fwd_trail; // Forward trail, in format (clause-id, vmarked)

  Global_Data(Global_Data const &) = delete;
  Global_Data &operator=(Global_Data const &) = delete;

  bool after_parsing = false;
  
  // Do initializations after parsing is completed. Called by friend Parser.
  void init_after_parsing() {
    after_parsing=true;

    items.shrink_to_fit();
    pivots.shrink_to_fit();
    db.get_db().shrink_to_fit();
    
    stat_itemlist_size = items.capacity()*sizeof(item_t);
    stat_pivots_size = pivots.capacity()*sizeof(lit_t);
    stat_db_size = db.get_db().size()*sizeof(cdb_t);
  }
  
  
public:
  Global_Data() : db(), pivots(), items(), fwd_trail() {}
  
  ClauseDB &get_db() {return db;}
  
  size_t get_max_var() const {return max_var;}
  size_t get_num_clauses() const {return num_clauses;}
  
  bool is_after_parsing() const {return after_parsing;}
  
  lit_t get_pivot(lit_t *cl) const {assert(cl); return pivots[clid(cl)];}
  
  size_t get_fst_prf_item() const {return fst_prf_item;}
  size_t get_num_items() const {return items.size();}
  item_t &get_item(size_t i) {return items[i];}
  
  size_t get_fst_lemma_id() const {return fst_lemma_id;}
  
  void init_after_fwd(pos_t cn_pos, vector<trail_item_t> const &tr);
  void join_vmarked(vector<bool> const &marked);

  const vector<pair<size_t,bool>>& get_fwd_trail() const {return fwd_trail;}
  
  lit_t *get_conflict() {return conflict;}
  
  
};


void Global_Data::init_after_fwd(pos_t cn_pos, vector<trail_item_t> const &tr) {
  conflict = db.p2c(cn_pos);
  assert(conflict);
  fwd_trail.clear();
  for (trail_item_t ti : tr) {
    assert(ti.reason);
    fwd_trail.push_back({clid(ti.reason),ti.vmarked});
  }
}

void Global_Data::join_vmarked(const vector<bool> &marked) {
  assert(fwd_trail.size() == marked.size());

  for (size_t i=0;i<marked.size();++i)
    fwd_trail[i].second |= marked[i];

}



Global_Data glb;



/*
 * Global data, which is synchronized between threads, or joined after thread's execution from thread's local data.
 * 
 */
class Synch_Data {
private:
  lit_map<atomic<size_t>> rat_counts;  // Literal -> rat-count.

  vector<atomic<bool>> marked;  // Id -> Whether clause is marked
  vector<atomic_flag> acquired; // Id -> Whether clause is/was acquired for verification by a worker thread
  
  vector<vector<cdb_t>> proofs;   // Id -> Proof of this lemma (RUP or RAT proof). Synchronized by acquired.
  
  
  Synch_Data(Synch_Data const &) = delete;
  Synch_Data &operator= (Synch_Data const &) = delete;

public:
  // Global data must already be after parsing when constructing this
  Synch_Data() : 
    rat_counts(glb.get_max_var())
  , marked(glb.get_num_clauses()+1)
  , acquired(glb.get_num_clauses()+1)
  , proofs(glb.get_num_clauses()+1) 
  {
    assert(glb.is_after_parsing());
    
    for (auto &b : marked) b=false;  // TODO: Is initialization necessary?
    //for (auto &f : acquired) f.test_and_set();  // Set all acquired flags. They are only cleared if clause is marked
  }
  
  void mark_clause(lit_t *cl) { marked[clid(cl)].store(true, memory_order_relaxed); }
  bool is_marked(lit_t *cl) { return marked[clid(cl)].load(memory_order_relaxed); }
  bool acquire(lit_t *cl) { if (marked[clid(cl)]) return !acquired[clid(cl)].test_and_set(memory_order_acquire); else return false; }
  
  vector<cdb_t> &proof_of(lit_t *cl) {return proofs[clid(cl)];}
  
  void inc_rat_counts(lit_t l) { ++rat_counts[l]; }
  const lit_map<atomic<size_t>> &get_rat_counts() { return rat_counts; }
};

/*
 * Parser that reads cnf and drat files
 * 
 */
class Parser {
private:
  struct Clause_Hash_Eq {
    ClauseDB const &db;

    size_t operator() (const pos_t &pos) const; // Hash function
    bool operator() (const pos_t &pos1, const pos_t &pos2) const; // Equality
  };

  Clause_Hash_Eq cheq;  // Hash and equality function for claus-positions
  typedef unordered_multimap<pos_t,pos_t,Clause_Hash_Eq,Clause_Hash_Eq> clause_map_t;
  clause_map_t clause_map; // Map from clauses to their position
  
public:
  Parser() :   
    cheq{glb.db}
  , clause_map(0,cheq,cheq)
  {}
  
  pos_t parse_clause(istream &in);
  pos_t parse_deletion(istream &in);

  void parse_dimacs(istream &in);
  void parse_proof(istream &in);
};


inline size_t Parser::Clause_Hash_Eq::operator() (const pos_t &pos) const {
  size_t sum=0, prod=1, xxor=0; // The hash-function from drat-trim
  for (lit_t const *l=db.p2c(pos);*l;++l) {
    prod*=*l; sum+=*l; xxor^=*l;
  }
  return (1023 * sum + prod) ^ (31 * xxor);
}

inline bool Parser::Clause_Hash_Eq::operator() (const pos_t &pos1, const pos_t &pos2) const {
  lit_t const *l1 = db.p2c(pos1);
  lit_t const *l2 = db.p2c(pos2);

  size_t i=0;
  do {
    if (l1[i]!=l2[i]) return false;
  } while (l1[i++]);
  return true;
}



pos_t Parser::parse_clause(istream &in) {
  size_t id = ++glb.num_clauses;                    // Ids start at 1
  glb.db.append(id);                                // Push id
  pos_t pos = glb.db.current();                     // Positions refer to first literal

  size_t len=0;
  
  lit_t l;  
  do {                                          // Push literals and terminating zero
    in>>ws; in>>l; glb.db.append(l);
    glb.max_var = max(var_of(l),glb.max_var);
    ++len;
  } while (l);
  --len;

  auto cl = glb.db.p2i(pos);                  // pos indicates first literal
  auto cle = glb.db.p2i(glb.db.current())-1;  // set cle one past last literal (Current position is one past terminating zero)

  set_resize<lit_t>(glb.pivots,id,*cl);         // Remember pivot as first literal of clause
  sort(cl,cle);                                 // Sort literals by ascending numerical value

  if (!cfg_assume_nodup) {
    // Remove duplicate literals
    auto ncle = unique(cl,cle);
    if (ncle != cle) {
      ncle[1]=0;
      glb.db.shrink_to(ncle+1);
    }
  }
  
  clause_map.insert({ pos, pos });              // Add to clause_map

  return pos;
}

pos_t Parser::parse_deletion(istream &in) {
  pos_t orig_pos = glb.db.current();
  pos_t result = pos_t::null;
  
  /*
   * In order to hash it, we push the clause to db first. Later, we will delete it again
   */
  
  glb.db.append(0);                             // Push dummy id

  pos_t pos = glb.db.current();
  
  
  lit_t l;
  do {                                          // Push literals and terminating zero
    in>>ws; in>>l; glb.db.append(l);
  } while (l);
  
  lit_t *cl = glb.db.p2c(pos);                  // pos indicates first literal
  lit_t *cle = glb.db.p2c(glb.db.current())-1;  // set cle one past last literal (Current position is one past terminating zero)
  
  sort(cl,cle);                                 // Sort
  auto orig_c = clause_map.find(pos);           // Look up clause
  
  if (orig_c == clause_map.end()) {
    clog<<"Ignoring deletion of non-existent clause (pos "<<pos.pos<<")"<<endl;
  } else {
    result = orig_c->second;
    clause_map.erase(orig_c);
  }

  glb.db.shrink_to(orig_pos);
  return result;
}

inline void parse_ignore_comments(istream &in) {
  in>>ws;
  while (!in.eof()) {
    if (in.peek()!='c') break;
    in.ignore(numeric_limits<streamsize>::max(), '\n');
    in>>ws;
  }
}


void Parser::parse_dimacs(istream &in) {
  in.exceptions(in.failbit|in.badbit);

  parse_ignore_comments(in);
  if (in.peek()=='p') in.ignore(numeric_limits<streamsize>::max(), '\n');

  while (!in.eof()) {
    parse_ignore_comments(in);
    if (in.eof()) break;

    pos_t pos = parse_clause(in);
    
    glb.items.push_back(item_t(false,pos));
  }

  glb.fst_lemma_id = glb.num_clauses+1;
  glb.fst_prf_item = glb.items.size();
}


void Parser::parse_proof(istream &in) {
  in.exceptions(in.failbit|in.badbit);

  parse_ignore_comments(in);
  if (in.peek()=='o') in.ignore(numeric_limits<streamsize>::max(), '\n');
  parse_ignore_comments(in);

  while (!in.eof()) {
    parse_ignore_comments(in);
    if (in.eof()) break;

    if (in.peek()=='d') {
      in.get();
      pos_t pos = parse_deletion(in);
      
      if (pos) glb.items.push_back(item_t(true,pos));
    } else {
      pos_t pos = parse_clause(in);
      glb.items.push_back(item_t(false,pos));
    }
  }
  
  glb.init_after_parsing();
}





class Verifier {
private:
  Synch_Data *sdata = nullptr;
  ClauseDB *db;
  bool my_clause_db = true;
  
  lit_map<int8_t> assignment; // Literal -> is-true


  vector<trail_item_t> trail;           // Trail: (literal, reason, marked)
  size_t processed = 0;                 // First unprocessed item on trail
  vector<bool> fwd_vmarked;             // vmarked on forward trail. Initialized after forward pass.
  size_t fwd_trail_size = 0;            // Current size of forward trail, for setting fwd_vmarked. Initialized after forward pass.
  

  vector<size_t> vtpos;                 // Position on trail for set variables (var -> size_t)

  lit_map<vector<lit_t*>> watchlists;   // Maps literals to list of clauses watching this literal

  // Relocate a clause pointer wrt old clause-db
  void relocate(ClauseDB const *odb, lit_t * &cl) {if (cl) cl=db->p2c(odb->c2p(cl));}
  // Relocate all clause pointers in this data structure
  void relocate(ClauseDB const *odb);


  inline void reset_true(lit_t l) {
    assert(is_true(l));
    assignment[l]=0;
  }
  
public:
  // Initialization of verifier with main database
  Verifier(ClauseDB &_db) : db(&_db), my_clause_db(false), assignment(0), trail(), fwd_vmarked(), vtpos(), watchlists(0) {}
  ~Verifier() {
    if (my_clause_db) delete db;
  }
  
  void init_after_parsing(Synch_Data *_sdata) {
    sdata=_sdata;
    assignment.resize(glb.get_max_var());
    vtpos.resize(glb.get_max_var()+1);
    watchlists.resize(glb.get_max_var());
  }
  
  
  // Initialization of verifier copy with own database
  Verifier(Verifier const &vrf) : 
      sdata(vrf.sdata)
    , db(new ClauseDB(*vrf.db))
    , my_clause_db(true)
    , assignment(vrf.assignment)
    , trail(vrf.trail)
    , processed(vrf.processed)
    , fwd_vmarked(vrf.fwd_vmarked)
    , fwd_trail_size(vrf.fwd_trail_size)
    , vtpos(vrf.vtpos)
    , watchlists(vrf.watchlists) 
  {
    relocate(vrf.db);
  }
  
  Verifier &operator=(Verifier const &vrf) {
    assert(&sdata == &vrf.sdata);
    db = new ClauseDB(*vrf.db);
    my_clause_db = true;
    trail = vrf.trail;
    fwd_vmarked = vrf.fwd_vmarked;
    processed = vrf.processed;
    vtpos = vrf.vtpos;
    watchlists = vrf.watchlists;
    relocate(vrf.db);
    return *this;
  }
  
  Verifier(Verifier const &&vrf) = delete;
  Verifier &operator=(Verifier const &&vrf) = delete;
  
  
  // Assignment
  inline bool is_true(lit_t l) {return assignment[l]!=0;}
  inline bool is_false(lit_t l) {return assignment[-l]!=0;}

  inline void assign_true(lit_t l, lit_t* reason) {
    assert(!is_true(l) && !is_false(l));
    assignment[l] = 1; 
    vtpos[var_of(l)] = trail.size();
    trail.push_back({l,reason,false}); 
  }

  
  // Adding clauses
  enum class acres_t { NORMAL, UNIT, TAUT, CONFLICT };

  acres_t add_clause(lit_t *cl);
  bool rem_clause(lit_t *cl);   // Remove clause from watchlist. Returns true if clause actually was in watchlists.
  void readd_clause(lit_t *cl); // Only clauses that where on watchlists may be readded.
  
  
  // Backtracking and marking
  vector<trail_item_t> const &get_trail() const {return trail;}
  inline size_t trail_pos() {return trail.size();}  // Current trail position
  
  const vector<bool> &get_fwd_vmarked() {return fwd_vmarked;}
  
  void rollback(size_t pos);                        // Rollback to position
  template<typename T> void for_marked_from(size_t pos, T const &ucr); // Dump marked clauses from pos (inclusive), by calling ucr(cl)
  
  void mark_var(size_t v);     // Mark reason for this variable to be set, recursively
  void mark_clause(lit_t *cl); // Mark clause and literals in clause recursively. 
  
  // Unit propagation
  template<bool core_first> lit_t *propagate_units_aux();
  /*
    Do unit propagation, and return nullptr or conflict clause.
   */
  lit_t *propagate_units() {if (cfg_core_first) return propagate_units_aux<true>(); else return propagate_units_aux<false>(); }

  // RUP/RAT verification
  void get_rat_candidates(std::vector< lit_t* >& cands, lit_t pivot);
  void verify(lit_t *cl);
  
  
  pos_t fwd_pass_aux();
  pos_t fwd_pass();
  
  void bwd_pass(size_t start_item, bool show_status_bar = false);
  
  
  void dbg_check_uprop();
  
  
};


void Verifier::dbg_check_uprop() {
  size_t num_undec_clauses = 0;
  
  for (lit_t l = watchlists.lbegin();l<watchlists.lend();++l) {
    for (auto cl : watchlists[l]) {
      
      if (cl[0] != l && cl[1] != l) {
        clog<<"Watched literal not on start pos"<<endl;
        fail();
      }
      
      if (cl[0] == l) {
        // Must not be a unit/conflict clause
        if (is_true(cl[0]) || is_true(cl[1])) continue;

        if (is_false(cl[0]) || is_false(cl[1])) {
          clog<<"Watched literal is false"<<endl; fail();
        }
          
        
        size_t ntrue=0;
        size_t nundec=0;
        
        for (lit_t *l=cl;*l;++l) {
          if (is_true(*l)) ++ntrue;
          else if (!is_false(*l)) ++nundec;
        }
        
        if (ntrue) continue;
        if (nundec==0) {
          clog<<"Conflict clause in WLs"<<endl; 
          fail();
        }
        
        if (nundec==1) {
          clog<<"Unit clause in WLs"<<endl; 
          fail();
        }
        
        ++num_undec_clauses;
      }
    }
  }
  
  clog<<"Watching "<<num_undec_clauses<<" undecided clauses, "<<trail.size()<<" units on trail"<<endl;
}



void Verifier::relocate(ClauseDB const *odb) {
  for (auto &ti : trail) {
    relocate(odb,ti.reason);
  }
  
  for (lit_t l=watchlists.lbegin();l<watchlists.lend();++l) {
    for (auto &cl : watchlists[l]) relocate(odb,cl);
  }
}


Verifier::acres_t Verifier::add_clause(lit_t *cl) {
  // Search for watched literals
  lit_t *w1=nullptr, *w2=nullptr;
  
  for (lit_t *l = cl; *l; ++l) {
    if (is_true(*l)) return acres_t::TAUT; // Ignoring tautology.
    if (!is_false(*l)) {
      if (!w1) w1=l; else if (!w2 && *l!=*w1) w2=l;
    }
  }

  if (!w1) { // Conflict
    return acres_t::CONFLICT;
  } else if (!w2) { // Unit, *w1 is unit literal
    assign_true(*w1,cl);
    return acres_t::UNIT;
  } else { // >1 undec
    assert(w1<w2);    // Implies that double-swapping below is correct
    swap(cl[0],*w1); swap(cl[1],*w2); w1=nullptr; w2=nullptr;
    watchlists[cl[0]].push_back(cl);
    watchlists[cl[1]].push_back(cl);
    return acres_t::NORMAL;
  }
}

bool Verifier::rem_clause(lit_t *cl) {
  if (cl[0]!=0 && cl[1]!=0) {
    bool wl0 = del_from_list(watchlists[cl[0]],cl);
    bool wl1 = del_from_list(watchlists[cl[1]],cl);
    assert(wl0 == wl1);
    (void)wl1; // Silence unused warning
    return wl0;
  } else {
    return false;
  }
}

void Verifier::readd_clause(lit_t *cl) {
  assert(cl[0]!=0 && cl[1]!=0);
  
  watchlists[cl[0]].push_back(cl); 
  watchlists[cl[1]].push_back(cl);
}











void Verifier::rollback(size_t pos) {
  for (size_t i=pos;i<trail.size();++i) reset_true(trail[i].l);
  trail.resize(pos);
  if (processed>trail.size()) processed=trail.size();
}

template<typename T> void Verifier::for_marked_from(size_t pos, T const &ucr) {
  for (size_t i=pos;i<trail.size();++i) {
    if (trail[i].vmarked && trail[i].reason) ucr(trail[i].reason);
  }
}


inline void Verifier::mark_var(size_t v) {
  assert(is_true(v) || is_false(v));
  size_t pos = vtpos[v];
  
  if (!trail[pos].vmarked) {
    trail[pos].vmarked=true;
    
    if (pos < fwd_trail_size) fwd_vmarked[pos]=true; // If this position in on current forward trail, also flag as marked there

    if (trail[pos].reason) mark_clause(trail[pos].reason);
  }
}

void Verifier::mark_clause(lit_t *cl) {
  sdata->mark_clause(cl);
  
  for (auto l=cl;*l;++l) {    
    mark_var(var_of(*l));
  }
}


template<bool cf_enabled> lit_t *Verifier::propagate_units_aux() {
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
      
      vector<lit_t*> &watchlist = watchlists[l];
      
      
      for (size_t i=0;i<watchlist.size();++i) {
        lit_t *cl = watchlist[i];
        
        // In cf_mode, ignore unmarked clauses
        /* FIXME: We would also like to ignore already processed clauses in non-cf mode.
         * However, we cannot use marked for that, as this may concurrently switch from false->true!
         */
        if (cf_enabled && cf_mode && !sdata->is_marked(cl)) continue;  
        
        lit_t w1 = cl[0]; 
        lit_t w2 = cl[1];

        //if (w1==l) swap(w1,w2);     // Normalize on w2 being set literal
        if (w1==l) { 
          w1=w2; w2=l;
          swap(cl[0], cl[1]);
        }
        assert(is_false(w2));
        if (is_true(w1)) continue;
        
        
        // Scan through clause and try to find new watched literal
        // Assuming that clauses do not contain dup literals, we can take first non-false literal from cl+2 onwards
        lit_t *w = nullptr;
        for (lit_t *ll=cl+2;*ll;++ll) {
//           assert(*ll!=w1 && *ll!=w2);     // Removed
          if (!is_false(*ll)) {w=ll; break;}
        }
        
        if (w) { // Found new watchable literal
          // Set new watched
          watchlists[*w].push_back(cl);
          swap(cl[1],*w);
          
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


void Verifier::get_rat_candidates(vector<lit_t*> &cands, lit_t pivot) {
  pivot=-pivot;
  
  for (lit_t l = watchlists.lbegin();l<watchlists.lend();++l) {
    for (auto cl : watchlists[l]) {
      if (cl[0] == l) {
        for (lit_t *ll=cl; *ll; ++ll) {
          if (*ll == pivot) cands.push_back(cl);
        }
      }
    }
  }
}

struct push_clause_ids {
  vector<lit_t> &prf;
  push_clause_ids(vector<lit_t> &_prf) : prf(_prf) {};
  
  void operator () (lit_t *cl) const { prf.push_back(static_cast<lit_t>( clid(cl))); }
};


void Verifier::verify(lit_t *cl) {
  vector<lit_t> &prf = sdata->proof_of(cl);
  push_clause_ids pci (prf);
  
  size_t orig_pos = trail_pos();
  lit_t pivot = glb.get_pivot(cl);
  bool pivot_false = is_false(pivot);

  // Set current size of forward trail. Subsequent clause marking will remember markings set on current forward trail.
  fwd_trail_size = orig_pos;
  
  // Falsify literals
  for (lit_t *l = cl; *l; ++l) {
    assert(!is_true(*l)); // Tautologies should have been ignored
    if (!is_false(*l)) assign_true(-(*l),nullptr);
  }
  
  // Unit propagation
  lit_t *conflict = propagate_units();
  
  if (conflict) { // RUP-check succeeded
    mark_clause(conflict);
    if (!cfg_no_proof) {
      prf.push_back(item_type::RUP_LEMMA);
      for_marked_from(orig_pos, pci);
    }
    rollback(orig_pos);
    if (!cfg_no_proof) {
      prf.push_back(0);
      prf.push_back(static_cast<cdb_t>(clid(conflict)));
    }
  } else {
    vector<cdb_t> rat_prf;
    push_clause_ids rpci (rat_prf);
    // RUP-check failed, do RAT check
    if (pivot_false) {clog<<"RAT check failed due to false pivot"<<endl; fail();}
    sdata->inc_rat_counts(pivot);
    
    // Gather clauses containing pivot
    vector<lit_t*> cands;
    get_rat_candidates(cands,pivot);

    size_t rat_pos = trail_pos();
    // Iterate over candidates
    
    for (auto ccl : cands) {
      // Falsify literals and check blocked
      bool blocked=false;
      for (lit_t *l = ccl;*l;++l) {
        if (*l == -pivot) continue;
        if (is_true(*l)) {
          mark_var(var_of(*l));  // Mark clauses that caused this clause to be blocked
          rollback(rat_pos);
          blocked=true;
          break;
        } else {
          if (!is_false(*l)) assign_true(-(*l),nullptr);
        }
      }
      if (!blocked) {
        lit_t *conflict = propagate_units();
        if (!conflict) {
          clog<<"RAT-check failed"<<endl; 
          fail();
        }
        mark_clause(conflict);
        
        if (!cfg_no_proof) {
          rat_prf.push_back(static_cast<cdb_t>(clid(ccl)));
          for_marked_from(rat_pos,rpci);
        }
        rollback(rat_pos); 
        if (!cfg_no_proof) {
          rat_prf.push_back(0);
          rat_prf.push_back(static_cast<cdb_t>(clid(conflict)));
        }
      }
    }
    
    // RAT-check succeeded
    if (!cfg_no_proof) {
      prf.push_back(item_type::RAT_LEMMA);
      prf.push_back(pivot);
      for_marked_from(orig_pos,pci);
    }
    rollback(orig_pos);
    if (!cfg_no_proof) {
      prf.push_back(0);
      for (auto x : rat_prf) prf.push_back(x);
      prf.push_back(0);
    }
  }
}


pos_t Verifier::fwd_pass_aux() {
  // Add clauses of formula
  for (size_t i=0;i<glb.get_fst_prf_item();++i) {
    item_t &item = glb.get_item(i);
    if (!item.is_erased()) {
      lit_t *cl = db->p2c(item.get_pos());
      
      assert(!item.is_deletion());
      size_t trpos = trail_pos();
      
      switch (add_clause(cl)) {
        case acres_t::TAUT: item.erase(); break;
        case acres_t::UNIT: item.set_trpos(trpos); break;
        case acres_t::CONFLICT: return pos_t::null; // Trivial conflict in clauses
        case acres_t::NORMAL: break;
        default:;  
      }
    }
  }
  
  lit_t *conflict = propagate_units_aux<false>();
  if (conflict) {
    // Conflict after unit-propagation on initial clauses
    return db->c2p(conflict);
  }
  
  // Add lemmas
  for (size_t i=glb.get_fst_prf_item();i<glb.get_num_items();++i) {
    item_t &item = glb.get_item(i);
    if (!item.is_erased()) {
      lit_t *cl = db->p2c(item.get_pos());
      
      if (item.is_deletion()) {
        if (!cfg_ignore_deletion) {
          if (!rem_clause(db->p2c(item.get_pos()))) 
            item.erase(); // Erase deletion of clauses that where not on watchlists, thus that they will no be re-added.
        } else {
          item.erase();
        }
      } else {
        size_t trpos = trail_pos();
        switch (add_clause(cl)) {
          case acres_t::TAUT: item.erase(); break;
          case acres_t::CONFLICT: mark_clause(cl); return db->c2p(cl);

          case acres_t::UNIT: item.set_trpos(trpos);
          case acres_t::NORMAL: {
            conflict = propagate_units();
            if (conflict) {
              mark_clause(conflict);
              return db->c2p(conflict);
            }
          }
        }
      }
    }
  }
  
  clog << "Forward pass found no conflict" << endl; 
  fail();
  return pos_t::null; // Unreachable, but not detected by gcc. Adding this to silence warning.
}

pos_t Verifier::fwd_pass() {
  pos_t res = fwd_pass_aux();
  
  // Initialize fwd_vmarked
  assert(fwd_vmarked.size()==0);
  for (auto &ti : trail) {
    fwd_vmarked.push_back(ti.vmarked);
  }
  
  fwd_trail_size = trail.size();
  
  return res;
}


void Verifier::bwd_pass(size_t start_item, bool show_status_bar) {

  assert(start_item >= glb.get_fst_prf_item());
  
  // Iterate over lemmas
  boost::progress_display *pdsp = show_status_bar?new boost::progress_display(glb.get_num_items() - glb.get_fst_prf_item()) : nullptr;
  
  size_t i = glb.get_num_items();
  while (i>glb.get_fst_prf_item()) {
    --i;
    
    if (pdsp) ++*pdsp;
    
    item_t &item = glb.get_item(i);
    
    if (!item.is_erased()) {
      lit_t *cl = db->p2c(item.get_pos());
      
      if (item.is_deletion()) {
        if (!cfg_ignore_deletion) readd_clause(cl); // We have erased deletions of clauses that were not on watchlist, so readding is safe here.
      } else {
        // Remove from watchlists
        rem_clause(cl);
        
        // Remove from trail
        if (item.has_tr_pos()) rollback(item.get_trpos());
        
        if (i<start_item) { // Only prove lemmas in range
          // Try to acquire lemma. This will only succeed for marked, yet unproved lemmas
          if (sdata->acquire(cl)) {
            verify(cl);
          }
        }
      }
    }
  }
}


class VController {
private:
  Synch_Data *sdata = nullptr;
  Verifier main_vrf;
  
  VController(const VController &) = delete;
  VController &operator=(const VController &) = delete;
  
  void do_parallel_bwd(size_t num_threads);
  
public:
  VController() : main_vrf(glb.get_db()) 
  {}
  
  ~VController() {
    if (sdata) delete sdata;
  }
  
  void do_parsing(istream &cnf_in, istream &drat_in);
  
  void do_verification(size_t num_threads);
 
  void dump_proof(ostream &out);
  
  
};

void VController::do_parsing(istream& cnf_in, istream& drat_in) {
  Parser parser;
  
  with_timing("Parsing formula",[&] () {
    parser.parse_dimacs(cnf_in);
  });

  with_timing("Parsing proof",[&] () {
    parser.parse_proof(drat_in);
  });
}


void VController::do_parallel_bwd(size_t num_threads) {
  if (num_threads>1) clog<<"Checking with "<<num_threads<<" parallel threads"<<endl; else clog<<"Single threaded mode"<<endl;
  assert(num_threads>0);
  // Auxiliary verifiers, initialized to copies of main verifier
  vector<Verifier> aux_vrfs(num_threads - 1,main_vrf);
  vector<thread> aux_threads;

  for (size_t i=0;i<num_threads-1;++i) {
    size_t start_item = glb.get_num_items();

    Verifier *vrf = &aux_vrfs[i];
    aux_threads.push_back(thread([vrf, start_item] () { vrf->bwd_pass(start_item, false); }));
  }
  
  main_vrf.bwd_pass(glb.get_num_items(),cfg_show_progress_bar);
  clog<<"Waiting for aux-threads ..."; clog.flush();
  for (auto &tr : aux_threads) tr.join();
  clog<<"done"<<endl;
  
  for (size_t i=0; i<num_threads-1;++i) glb.join_vmarked(aux_vrfs[i].get_fwd_vmarked());
  glb.join_vmarked(main_vrf.get_fwd_vmarked());
}



void VController::do_verification(size_t num_threads) {
  sdata=new Synch_Data();
  main_vrf.init_after_parsing(sdata);
  
  pos_t cpos = with_timing<pos_t>("Forward pass",[&] {return main_vrf.fwd_pass();});
//   pos_t cpos = main_vrf.fwd_pass();
  
  if (cpos) {
    glb.init_after_fwd(cpos,main_vrf.get_trail());
    with_timing("Backward pass",[&] {do_parallel_bwd(num_threads);},&stat_bwd_checking_time);
  } else {
    clog<<"Trivial conflict in clauses"<<endl;
  }
}

void VController::dump_proof(ostream &out) {
  // GRAT Header
  out<<"GRAT";
  out<<"b";
  out<<"t";
  out<<" "<<sizeof(cdb_t);
  out<<" 0"<<endl;


  // Conflict clause
  assert(glb.get_conflict());
  out<<item_type::CONFLICT<<" "<<clid(glb.get_conflict())<<" 2"<<endl;
  
  // Proof items
  size_t i = glb.get_num_items();
  size_t tri = glb.get_fwd_trail().size();
  while (i>glb.get_fst_prf_item()) {
    --i;
    
    item_t &item = glb.get_item(i);
    
    if (!item.is_erased()) {
      
      lit_t *cl = glb.get_db().p2c(item.get_pos());
      
      
      if (item.is_deletion()) {
        if (!cfg_ignore_deletion) {
          if (sdata->is_marked(cl)) {
            out<<item_type::DELETION<<" "<<clid(cl)<<" 2"<<endl;
          }
        }
      } else {
        if (item.has_tr_pos()) {
          // If clause is principal clause on forward trail, dump v-marked clauses on forward trail and adjust tri
          size_t ntri = item.get_trpos();
          assert(ntri < tri);
          
          size_t sz=0;
          for (size_t j=ntri;j<tri;++j) {
            auto &tritem = glb.get_fwd_trail()[j];
            if (tritem.second) {
              if (!sz) {
                out<<item_type::UNIT_PROP<<" "; ++sz;
              }
              out<<tritem.first<<" "; ++sz;
            }
          }
          
          if (sz) {
            out<<"0 "<<sz+1<<endl;
          }
          
          tri = ntri;
        }
      
        if (sdata->is_marked(cl)) {
          // Dump proof
          size_t j=0;
          size_t sz=0;
          vector<cdb_t> &prf = sdata->proof_of(cl);
          assert(prf.size() > 0);
          
          // TODO/FIXME Store proofs in more structured way, such that this clause-inserting hack becomes unnecessary!
          // Dump item type
          cdb_t itt = prf[j++];
          out<<itt<<" "; ++sz;
          if (itt == item_type::RAT_LEMMA) {
            out<<prf[j++]<<" ";++sz;
          }
          
          // Dump clause
          out<<clid(cl)<<" ";++sz;
          for (lit_t *l = cl;*l;++l) {out<<*l<<" "; ++sz; }
          out<<"0"; ++sz;
          for (;j<prf.size();++j) {out<<" "<<prf[j]; ++sz; }
          out<<" "<<sz<<endl;
        }
      }
    }
  }
  
  // Initial unit propagations. TODO: Redundant, outsource to dump_unit_props(start,end) function.
  {
    size_t sz=0;
    for (size_t j=0;j<tri;++j) {
      size_t id = glb.get_fwd_trail()[j].first;
      bool vmarked = glb.get_fwd_trail()[j].second;
      
      assert(id < glb.get_fst_lemma_id());
      if (vmarked) {
        if (!sz) {
          out<<item_type::UNIT_PROP<<" "; ++sz;
        }
        out<<id<<" "; ++sz;
      }
    }
    if (sz) {
      out<<"0 "<<sz+1<<endl;
    }
  }

  // RAT counts
  size_t sz=0;
  out<<item_type::RAT_COUNTS; ++sz;
  
  auto &rc = sdata->get_rat_counts();
  
  for (lit_t l=rc.lbegin(); l<rc.lend();++l) {
    size_t c = rc[l];
    if (c) {
      out<<" "<<l<<" "<<c; sz+=2;
    }
  }
  out<<" 0 "<< sz+1 <<endl;
}


void print_usage() {
  cerr<<"Usage gratgen <dimacs-file> <proof-file> <options>"<<endl;
    cerr<<"Options:"<<endl;
    cerr<<"  -u, --no-core-first    Normal (no core first) unit propagation"<<endl;
    cerr<<"  -o name                Name of GRAT-file"<<endl;
    cerr<<"  -p, --no-deletion      Ignore deletion of clauses"<<endl;
    cerr<<"  -j, --num-parallel     Number of parallel threads to use"<<endl;
    cerr<<"      --assume-nodup     Assume that clauses contain no duplicate literals"<<endl;
    cerr<<"      --no-progress-bar  Do not show fancy progress bar"<<endl;
}

void print_info() {
  cerr<<"sizeof(cdb_t) = "<<sizeof(cdb_t)<<endl;
  cerr<<"sizeof(cdb_t*) = "<<sizeof( cdb_t* )<<endl;
}


int main(int argc, char **argv) {
  auto main_start_time = chrono::steady_clock::now();

  print_info();

  if (argc<3) {print_usage(); return 2;}

  string dimacs_file = argv[1];
  string proof_file = argv[2];
  string grat_file=""; cfg_no_proof=true;

  size_t num_parallel = thread::hardware_concurrency();
  
  for (int i=3;i<argc;++i) {
    string a = argv[i];
    
    if (a=="-u" || a=="--no-core-first") cfg_core_first = false;
    else if (a=="-p" || a=="--no-deletion") cfg_ignore_deletion = true;
    else if (           a=="--assume-nodup") cfg_assume_nodup = true;
    else if (           a=="--no-progress-bar") cfg_show_progress_bar = false;
    else if (a=="-j" || a=="--num_parallel") {
      ++i; if (i>=argc) {cerr<<"Expecting argument for "<<a<<endl; fail();}
      num_parallel = stoul(argv[i]);
      if (!num_parallel) {cerr<<"Invalid number of parallel threads "<<num_parallel<<endl; fail();}
    }
    else if (a=="-o") {
      ++i; if (i>=argc) {cerr<<"Expecting argument for -o"<<endl; fail();}
      grat_file=argv[i];
      cfg_no_proof=false;
    } else {
      cerr<<"Unknown command line argument: "<<a<<endl; fail();
    }
  }
  
  ofstream grat_out;

  if (!cfg_no_proof) {
    grat_out.open(grat_file);
    grat_out.exceptions(grat_out.badbit | grat_out.failbit);
    grat_out.flush();
  }
  
  
  // Parsing
  {
    Parser parser;
    auto parsing_start_time = chrono::steady_clock::now();
    
    with_timing("Parsing formula",[&] () {
      ifstream fs(dimacs_file,ifstream::in); 
      parser.parse_dimacs(fs);
      fs.close();
    });

    with_timing("Parsing proof",[&] () {
      ifstream fs(proof_file,ifstream::in); 
      parser.parse_proof(fs);
      fs.close();
    });
    
    stat_parsing_time = chrono::duration_cast<chrono::milliseconds>( chrono::steady_clock::now() - parsing_start_time);
  }

  // Verification
  auto checking_start_time = chrono::steady_clock::now();
  VController vctl;
  vctl.do_verification(num_parallel);
  stat_checking_time = chrono::duration_cast<chrono::milliseconds>( chrono::steady_clock::now() - checking_start_time);

  stat_overall_vrf_time = chrono::duration_cast<chrono::milliseconds>( chrono::steady_clock::now() - main_start_time);
  
  if (!cfg_no_proof) {
    // Write proof file
    with_timing("Writing proof",[&] () {vctl.dump_proof(grat_out); grat_out.close();},&stat_writing_time);
  }

  stat_overall_time = chrono::duration_cast<chrono::milliseconds>( chrono::steady_clock::now() - main_start_time);
  
  clog<<"s VERIFIED"<<endl;
  
  clog<<"Timing statistics (ms)"<<endl;
  clog<<"Parsing:  "<<stat_parsing_time.count()<<endl;
  clog<<"Checking: "<<stat_checking_time.count()<<endl;
  clog<<"  * bwd:  "<<stat_bwd_checking_time.count()<<endl;
  clog<<"Writing:  "<<stat_writing_time.count()<<endl;
  clog<<"Overall:  "<<stat_overall_time.count()<<endl;
  clog<<"  * vrf:  "<<stat_overall_vrf_time.count()<<endl;
  clog<<endl;
  clog<<"Size statistics (bytes)"<<endl;
  clog<<"Clause DB size:  "<<stat_db_size<<endl;
  clog<<"Item list:       "<<stat_itemlist_size<<endl;
  clog<<"Pivots store:    "<<stat_pivots_size<<endl;
  
  return 0;
}
