/*
  Efficient checker for GRAT unsat certificates.

  Techniques:
    The supported certificates contain a DRAT-proof together with a trace of all necessary unit propagations.

    A first pass reads the formula and the proof, keeping track of an assignment induced by encountered unit clauses and explicit unit-propagations.
    The RUP and RAT proofs are checked in this pass, however, it is not checked that the RAT candidates given in the proof are exhaustive.

    In a second pass, when all the resolution literals used in RAT proofs are known, a map from resolution literals to clauses in which they occur is collected,
    and used to check whether the RAT candidates are exhaustive. No proof checking is done in this phase.



  Format:
    certificate = unit-props item* conflict
      // The certificate consists of an initial unit propagation for the formula, followed by a list of proof items, and finally a conflict clause

    unit-props = id* 0
      // A sequence of unit clause ids. Each clause in the sequence must be unit if the previous clauses have already been propagated.

    item = lemma | deletion

    lemma = id lit* 0 proof unit-props
      // An unused id for the lemma, followed be the literals and the proof of the lemma, and, finally, some unit-propagations

    proof = unit-props ( id | 0 ratproof )
      // Initial unit propagation for RUP-proof, followed by either a conflict clause id, or a RAT-proof

    ratproof = lit (rat_candidate_proof)* 0
      // Resolution literal, and proofs for each candidate, i.e., each non deleted clause that contains negated resolution literal.

    rat_candidate_proof = id ( unit_props id | 0 0 )
      // Id of candidate clause, followed by unit-propagations and conflict clause id, or by '0 0' if the candidate is blocked.

    deletion = 0 id
      // Id of the clause to delete. The id must have been assigned and not yet deleted.

    conflict = 0 0 id
      // Id of a conflict clause, which finishes the unsat proof.

    id = [1-9][0-9]*
      // Positive clause id. The initial segment of clause ids is used for the clauses in the formula
      // Note/FIXME: Currently limited to machine word size. This limit is not checked!

    lit = -?[1-9][0-9]*
      // Literal.
      // Note/FIXME: Currently limited to machine word size. This limit is not checked!



  TODO:
    * Store RAT-literals in certificate, then do only one pass!
    * Let literal frequency determine whether check is deferred
    * Allow for blocked clauses to be omitted in RAT proof. This requires reconstruction of the assignment in second pass.
    * If resolution literals are known before (e.g. contained in the certificate), one pass would be enough.

    * Optimize on parser, check for overflows (on literals, ids, generated formula-ids, DB-size (how is vector.push_back specified?) )



*/



#include <iostream>
#include <cstdlib>
#include <fstream>
#include <vector>
#include <algorithm>
#include <cassert>
#include <limits>
#include <unordered_map>
#include <cstdint>

//#include <gperftools/profiler.h>

using namespace std;


typedef intptr_t cdb_t;

typedef uintptr_t idx_t;
typedef intptr_t lit_t;




// Hackery to get position info in error case
const cdb_t* dbg_last_item = nullptr;
const cdb_t* dbg_valid_item_end = nullptr;

void fail() {
  if (dbg_last_item) {
    cerr<<"Dumping data base from position of last item onwards"<<endl;
    const cdb_t* end_at = min(dbg_valid_item_end,dbg_last_item+50);

    for (const cdb_t* x=dbg_last_item;x!=end_at;++x) {
      cerr<<*x; if (!*x) cerr<<endl; else cerr<<" ";
    }
    cerr<<endl;
  }
  exit(1);
}
void fail(const char *msg) {
  cerr<<msg<<endl; fail();
}

struct Id {
  private:
    idx_t id;

  public:
    inline Id(idx_t _id) : id(_id) {
      if (id==0) fail("Zero id");
    }

    inline idx_t get() const {return id;}


    inline bool operator==(const Id &i2) const {return id == i2.id;}
    inline bool operator!=(const Id &i2) const {return id != i2.id;}

};

class IdZ {
  private:
    idx_t id;

  public:
    inline IdZ(idx_t _id) : id(_id) {}
    inline bool isZ() const {return id==0;}
    inline Id the_id() const {return Id(id);}
};

class Lit {
  private:
    lit_t l;
    enum class unchecked {};

    inline Lit(lit_t _l, unchecked) : l(_l) {}

  public:
    inline Lit(lit_t _l) : l(_l) {
      if (l==0) fail("Zero literal");
    }

    inline lit_t get() const {return l;}

    inline Lit operator-() const {return Lit(-l,unchecked());}

    inline bool operator==(const Lit &l2) const {return l == l2.l;}
    inline bool operator!=(const Lit &l2) const {return l != l2.l;}

};

class LitZ {
  private:
    lit_t l;

  public:
    inline LitZ(lit_t _l) : l(_l) {}
    inline bool isZ() const {return l==0;}
    inline Lit the_lit() const {return Lit(l);}

    inline lit_t get() const {return l;}

    inline bool operator==(const LitZ &l2) const {return l == l2.l;}
    inline bool operator!=(const LitZ &l2) const {return l != l2.l;}

};


// Holds raw clause and proof data
class Store {
  public:
    Store();

    size_t size();

    void parse_dimacs(istream &in);
    void parse_fvc(istream &in);


    /*
      Generic fetch functions
    */
    IdZ fetch_idz();
    Id fetch_id();
    LitZ fetch_litz();
    Lit fetch_lit();

    /*
      Pointer to clause or lemma at current position.
    */
    const LitZ* current_clause();

    const cdb_t* current_raw();

    /*
      Fetches or synthesizes an id for a clause, depending on store implementation.
    */
    Id fetch_clause_id();

    /*
      True if current position is the start of the proof.
    */
    bool at_proof_start();

    void next_item(); // Move on to next item. PRE: Current position at end of item.

    enum class proof_item_type {LEMMA, DELETION, CONFLICT};

    /*
      Fetches the type of the next proof item, and sets current position to start of information for this item:
        LEMMA: Position is at lemma id
        DELETION: Position is at clause id
        CONFLICT: Position is at conflict clause id
    */
    proof_item_type fetch_proof_item_type();


    /*
      Moves the current position to the beginning, and resets next-id information,
      in order to begin a new pass over the clauses.
    */
    void init_new_pass();


  private:
    vector<cdb_t> data;       // Raw data

    size_t proof_start_pos;   // First item of proof
    cdb_t *proof_start;       // First item of proof, set after DB has stabilized

    cdb_t *current;           // Current position when interpreting data
    idx_t next_id;            // Next id for determining clause ids

    bool at_item_start = false; // Used to check that new items are only loaded if at item start!
    bool in_proof = false;      // Set if inside proof


  private:
    void parse_raw(istream &in);

    idx_t fetch_unsigned();
    lit_t fetch_signed();
    cdb_t fetch_raw();
    cdb_t peek_raw();



  private:
    // Delete
    Store(const Store&);
    void operator=(const Store&);



};



Store::Store() : data(), proof_start_pos(0), proof_start(nullptr), current(nullptr), next_id(1) {}

inline cdb_t Store::fetch_raw() { if (current > &data.back()) fail("Read past end of store"); return *(current++);}
inline cdb_t Store::peek_raw() { if (current > &data.back()) fail("Read past end of store"); return *current;}

inline const cdb_t* Store::current_raw() {return current;}

inline lit_t Store::fetch_signed() {return static_cast<lit_t>(fetch_raw());}
inline idx_t Store::fetch_unsigned() {return static_cast<idx_t>(fetch_raw());}


inline IdZ Store::fetch_idz() {return IdZ(fetch_unsigned());}
inline Id Store::fetch_id() {return fetch_idz().the_id(); }
inline LitZ Store::fetch_litz() {return LitZ(fetch_signed());}
inline Lit Store::fetch_lit() {return fetch_litz().the_lit();}

inline const LitZ* Store::current_clause() {return reinterpret_cast<const LitZ*>(current);}
inline bool Store::at_proof_start() {return current == proof_start;}

inline void Store::next_item() {
  assert(!in_proof || !at_item_start);
  at_item_start=true;

  if (at_proof_start()) {
    assert(!in_proof);
    in_proof=true;
  }
}


inline Store::proof_item_type Store::fetch_proof_item_type() {
  assert(in_proof && at_item_start);
  at_item_start = false;

  if (peek_raw()) return proof_item_type::LEMMA;
  fetch_raw();
  if (peek_raw()) return proof_item_type::DELETION;
  fetch_raw();
  return proof_item_type::CONFLICT;
}

inline Id Store::fetch_clause_id() {return Id(next_id++);}


void Store::init_new_pass() {
  current = data.data();
  next_id=1;
  in_proof=false;
  at_item_start=false;
}

size_t Store::size() {return data.size();}

void Store::parse_dimacs(istream &in) {
  data.clear(); data.shrink_to_fit();

  parse_raw(in);

  proof_start_pos=data.size();

  if (data.size() == 0) fail("Empty proof file");
  if (data.back()!=0) fail("DIMACS file must end with a 0");
}

void Store::parse_fvc(istream &in) {
  parse_raw(in);
  data.shrink_to_fit();
  current = data.data();
  proof_start = data.data() + proof_start_pos;
  at_item_start = true;
  in_proof = false;


  dbg_valid_item_end = &*data.end();
}

void Store::parse_raw(istream &in) {
  in.exceptions(in.failbit|in.badbit);
  do {
    in>>ws;
    if (in.eof()) break;

    char c=in.peek();

    if (c=='c' || c=='p') in.ignore(numeric_limits<streamsize>::max(), '\n');
    else {
      cdb_t x; in>>x; data.push_back(x);
    }
  } while (true);

}



class Assignment {
  public:
    enum class val : signed {
      FALSE = -1, TRUE = 1, UNDEC = 0
    };

    static inline val neg(val v) {return static_cast<val>(static_cast<signed>(v)*-1);}

  private:
    vector<val> A;

    inline size_t index(Lit l) {return abs(l.get()); }


  public:
    inline Assignment() : A() {}

    inline val get_val(Lit l) {
      if (index(l)<A.size()) {
        if (l.get()<0) return neg(A[index(l)]);
        else return A[index(l)];
      } else {return val::UNDEC;}
    }

    inline bool is_false(Lit l) {return get_val(l)==val::FALSE;}
    inline bool is_true(Lit l) {return get_val(l)==val::TRUE;}
    inline bool is_undec(Lit l) {return get_val(l)==val::UNDEC;}

    inline void set_false(Lit l) {
      if (index(l) >= A.size()) A.resize(index(l)+1,val::UNDEC);
      A[index(l)] = l.get()<0?val::TRUE:val::FALSE;
    }

    inline void unset(Lit l) {
      A[index(l)] = val::UNDEC;
    }

};

//struct Clause {
//  public:
//    LitZ *literals
//
//
//  private:
//    Clause();
//    ~Clause();
//    Clause(const Clause&);
//    void operator =(const Clause &);
//
//  private:
//  #pragma GCC diagnostic push
//  #pragma GCC diagnostic ignored "-Wpedantic"
//  lit_t literals[];
//  #pragma GCC diagnostic pop
//};


class Clausemap {
  private:
    vector<const LitZ*> data;

    inline size_t index(Id id) { return id.get(); };

  public:
    Clausemap();

    void clear();

    void ensure_exists(Id id);
    bool contains(Id id);
    const LitZ* lookup(Id id);
    void add(Id id, const LitZ*);
    void del(Id id);


    template<typename F> void foreach_valid_id(const F &f);

};

Clausemap::Clausemap() : data() {}

void Clausemap::clear() {
  data.clear();
}

inline bool Clausemap::contains(Id id) {
  return index(id)<data.size() && data[index(id)] != nullptr;
}

inline void Clausemap::ensure_exists(Id id) {
  if (!contains(id)) { cerr<<"Clause id does not exist "<<id.get()<<endl; fail();}
}

inline const LitZ* Clausemap::lookup(Id id) {
  ensure_exists(id);
  return data[index(id)];
}

inline void Clausemap::add(Id id, const LitZ* c) {
  if (index(id)>=data.size()) data.resize(index(id)+1,nullptr);
  else if (data[index(id)] != nullptr) {cerr<<"Duplicate clause id "<<id.get()<<endl; fail();}
  data[index(id)]=c;
}

inline void Clausemap::del(Id id) {
  ensure_exists(id);
  data[index(id)]=nullptr;
}

template<typename F> inline void Clausemap::foreach_valid_id(const F &f) {
  for (size_t i=1; i<data.size();++i)
    if (data[i]!=nullptr) f(Id(i));

}

template<typename V> class litmap {
  private:
    vector<V> data;

    static inline size_t index(Lit l) {
      lit_t lv = l.get();
      return lv<0 ? 2*static_cast<size_t>(-lv-1) : 2*static_cast<size_t>(lv-1) + 1;
    }

    static inline Lit lit_of(size_t idx) {
      lit_t lv = idx / 2 + 1;
      if (idx % 2 == 0) lv=-lv;
      return Lit(lv);
    }

  public:
    inline litmap() : data() {}
    inline ~litmap() {}

    struct iterator {
      size_t i;
      vector<V> &data;

      iterator &operator++() {++i; return *this;};
      bool operator==(const iterator &i2) const {return i==i2.i;}
      bool operator!=(const iterator &i2) const {return i!=i2.i;}

      struct value_type { Lit first; V &second; };

      value_type operator *() {return value_type{lit_of(i),data[i]};}
    };

    inline iterator begin() {return iterator{0,data};}
    inline iterator end() {return iterator{data.size(),data};}


    inline V &operator [](Lit l) {
      size_t i = index(l);
//      lit_t lv = l.get();
//      size_t i = lv<0 ? 2*static_cast<size_t>(-lv) : 2*static_cast<size_t>(lv) + 1;

      if (i>=data.size()) data.resize(i+1);
      return data[i];
    }
};



class State {
  private:
    Store DB;
    Assignment A;
    Clausemap CM;

    litmap<const cdb_t*> rat_positions;  // rat_positions[l] is position of last lemma that used l as rat resolution literal
    bool have_deferred_rats=false;

//    xxx, ctd here: Implement second pass. Then implement literal frequency optimization, and check its overhead!
//    perhaps also try reverse pass order: First pass collects reslit info only, and second pass does all checks


    vector<Lit> backtrack; // Stored globally

    void set_false_induced(Lit l);

    // Read clause. Return true if this yields UNSAT already.
    bool rd_clause();

    // Check that id refers to unit clause, and return unit literal
    Lit check_unit(Id id);

    // Check that id refers to conflict clause
    void check_conflict(Id id);

    bool rd_proof_item();
    void rd_lemma();
    void rd_del();
    void rd_conflict();
    void rd_induced_units();


    template<typename BT> void rd_follow_units(const BT &backtrack);


    void check_deferred_rats();


  public:
    State();

    ~State();

    inline void parse_dimacs(istream &in) {DB.parse_dimacs(in);}
    inline void parse_fvc(istream &in) {DB.parse_fvc(in);}

    // Read all clauses. Return true if UNSAT.
    bool rd_cnf();

    // Read and check proof
    void rd_proof();



};


State::State() : DB(), A(), CM(), rat_positions(), backtrack() {}
State::~State() {}

inline void State::set_false_induced(Lit l) {
  A.set_false(l);
}


bool State::rd_clause() {
  Id id = DB.fetch_clause_id();

  CM.add(id,DB.current_clause());

  // Scan over clause's literals, and check for conflict or unit clause
  LitZ lu = LitZ(0);
  for (LitZ lz = DB.fetch_litz(); !lz.isZ(); lz=DB.fetch_litz()) {
    Lit l = lz.the_lit();

    if (lz == lu) continue; // Duplicate of stored unit literal

    if (A.is_true(l) || (!A.is_false(l) && !lu.isZ())) { // Tautology or 2 undecided literals
      while (!DB.fetch_litz().isZ());   // Skip over rest, and return
      return false;
    } else if (!A.is_false(l)) {
      lu=lz;
    }
  }

  if (lu.isZ()) { // Conflict clause
    return true;
  } else { // Unit clause
    A.set_false(-lu.the_lit());
    return false;
  }
}


bool State::rd_cnf() {
  while (!DB.at_proof_start()) {
    if (rd_clause()) {
      return true;
    }
    DB.next_item();
  }

  return false;
}

void print_clause(const LitZ* lz, ostream &out) {
  while (true) {
    out<<lz->get();
    if (lz->isZ()) break;
    out<<" ";
    ++lz;
  }
}

inline Lit State::check_unit(Id id) {
  const LitZ *c = CM.lookup(id);

  LitZ ul = 0;

  for (auto lz=c;!lz->isZ();++lz) {
    Lit l = lz->the_lit();
    if (A.is_true(l)) fail("True literal in clause assumed to be unit");
    if (!A.is_false(l)) {
      if (ul.isZ()) ul=*lz;
      else if (ul != *lz) {
        cerr<<"Clause "<<id.get()<<": "; print_clause(c,cerr); cerr<<endl;
        cerr<<"Undec literals are "<<ul.get()<<" and "<<lz->get()<<endl;
        fail("2-undec in clause assumed to be unit");
      }
    }
  }

  if (ul.isZ()) fail("Conflict in clause assumed to be unit");
  return ul.the_lit();
}

inline void State::check_conflict(Id id) {
  for (const LitZ *lz = CM.lookup(id);!lz->isZ();++lz)
    if (!A.is_false(lz->the_lit()))
      fail("Non-false literal in clause assumed to be conflict");

}

template<typename BT> inline void State::rd_follow_units(const BT &add_backtrack) {
  while (true) {
    IdZ uidz = DB.fetch_idz();
    if (uidz.isZ()) break;
    Lit ulit = check_unit(uidz.the_id());
    A.set_false(-ulit);
    add_backtrack(-ulit);
  }
}


inline bool clause_contains(const LitZ *lz, Lit cl) {
  for (;!lz->isZ();++lz) if (lz->the_lit()==cl) return true;
  return false;
}


void State::rd_lemma() {
  Id id = DB.fetch_id();
  const cdb_t* position_for_rat = DB.current_raw();
  const LitZ *c = DB.current_clause();

  //vector<Lit> backtrack;  // TODO: Check if making this global is more efficient!
  backtrack.clear();

  // Start rup checking. On the way of fetching clause, also check for unit clause
  unsigned num_undec = 0; LitZ undec_lit = 0;
  while (true) {
    LitZ lz = DB.fetch_litz();
    if (lz.isZ()) break;
    Lit l = lz.the_lit();
    if (A.is_true(l)) fail("Tautological lemma, should not occur in proof.");
    if (!A.is_false(l)) {
      ++num_undec; undec_lit=lz;
      A.set_false(l);
      backtrack.push_back(l);
    }
  }

  // Literals of clause set to false, now read and check RUP unit clauses
  rd_follow_units([this](Lit l){backtrack.push_back(l);});

  // Read conflict clause id
  IdZ cidz = DB.fetch_idz();

  if (!cidz.isZ()) { // RUP: Proof provides conflict clause id
    check_conflict(cidz.the_id());
    for (Lit l : backtrack) A.unset(l);
    CM.add(id,c);

    if (num_undec == 1) set_false_induced(-undec_lit.the_lit()); // If added unit-lemma, modify assignment
    return;
  }

  // RAT
  Lit reslit = DB.fetch_lit();

  /* Check that reslit is contained in clause, and was not false under original assignment.
    This can be checked by searching for reslot in clause, and -reslit in backtrack:
      If l was false before, -l cannot be added to backtrack.
      Otherwise, -l has been added to backtrack upon falsifying clause literals.
  */
  for (const LitZ *lz = c; ;++lz) {
    if (lz->isZ()) fail("Resolution literal not found in clause");
    if (lz->the_lit()==reslit) break;
  }

  for (auto i=backtrack.begin(); ;++i) {
    if (i==backtrack.end()) fail("Resolution literal was assigned");
    if (*i == reslit) break;
  }


  // Check and record all provided RAT-candidates
  vector<Lit> backtrack2;
  vector<Id> candidates;

  while (true) {
    IdZ idz = DB.fetch_idz();
    if (idz.isZ()) break;
    Id id=idz.the_id();
    candidates.push_back(id);

    const LitZ *candidate = CM.lookup(id);

    // Note: Whether candidates actually contain -reslit is checked later

    // Check if blocked
    bool blocked=false;
    for (const LitZ *lz=candidate; !lz->isZ(); ++lz)
      if (lz->the_lit() != -reslit && A.is_true(lz->the_lit())) { // Blocked clause
        if (!DB.fetch_idz().isZ()) fail("No units allowed on blocked RAT candidate");
        if (!DB.fetch_idz().isZ()) fail("No conflict clause id allowed on blocked RAT candidate");
        blocked=true;
        break;
      }
    if (blocked) continue;

    // Non-blocked clause
    backtrack2.clear();
    // Assign literals (but -reslit) to false
    for (const LitZ *lz=candidate; !lz->isZ(); ++lz) {
      Lit l=lz->the_lit();
      if (l != -reslit && !A.is_false(l)) {
        A.set_false(l);
        backtrack2.push_back(l);
      }
    }


    // Follow units
    rd_follow_units([&backtrack2](Lit l){backtrack2.push_back(l);});

    // Check conflict
    {
      IdZ ccidz = DB.fetch_idz();
      if (ccidz.isZ()) fail("Expected conflict clause id");
      check_conflict(ccidz.the_id());
    }

    // Backtrack over RAT-assignments
    for (Lit l : backtrack2) A.unset(l);
  }

  #define DEFER_RAT_PROOF
  #ifdef DEFER_RAT_PROOF
  // Log resolution literal and position of lemma
  rat_positions[reslit] = position_for_rat;
  have_deferred_rats=true;

  #else
  // Check that RAT-candidates where exhaustive. (We even check for exact match here).
  size_t i = 0;

  CM.foreach_valid_id([&i, &candidates, this, reslit](Id id) {
    // Check for reslit
    if (!clause_contains(CM.lookup(id),-reslit)) return; // Resolution literal not in clause

    if (i>=candidates.size()) fail("RAT exhaustiveness check: Proof contains too few candidates.");
    if (candidates[i] != id) fail("RAT exhaustiveness check: Candidate mismatch.");

    ++i;
  });

  if (i<candidates.size()) fail("RAT exhaustiveness check: Proof contains too much candidates.");
  #endif

//
////  #define SKIP_RAT_PROOF
//  #ifdef SKIP_RAT_PROOF
//  itrail.push_back(ITrail_Entry(position_for_rat));
//  reslits.push_back(reslit);
//  //Defer RAT proof
//  while (!DB.fetch_idz().isZ()) {
//    while (!DB.fetch_idz().isZ()); // Units
//    DB.fetch_idz(); // Conflicts
//  }
//
//  #else
//
//  // Iterate over all candidate clauses, and do rat proofs
//  CM.foreach_valid_id([&backtrack2, this, reslit](Id id) {
//    // Check blocked and contains -reslit
//    const LitZ *candidate = CM.lookup(id);
//
//    // Check for reslit
//    {
//      bool contains_reslit = false;
//      for (const LitZ *lz=candidate; !lz->isZ(); ++lz)
//        if (lz->the_lit() == -reslit) {
//          contains_reslit=true;
//          break;
//        }
//      if (!contains_reslit) return; // Resolution literal not in clause
//    }
//
//    // Compare read id with clause id
//    {
//      IdZ cand_idz = DB.fetch_idz();
//      if (cand_idz.isZ()) fail("Expected more RAT-clauses");
//      if (cand_idz.the_id() != id) fail("Expected different RAT-id");
//    }
//
//    // Check if blocked
//    for (const LitZ *lz=candidate; !lz->isZ(); ++lz)
//      if (lz->the_lit() != -reslit && A.is_true(lz->the_lit())) { // Blocked clause
//        if (!DB.fetch_idz().isZ()) fail("No units allowed on blocked RAT candidate");
//        if (!DB.fetch_idz().isZ()) fail("No conflict clause id allowed on blocked RAT candidate");
//        return;
//      }
//
//    // Non-blocked clause that contains reslit
//    backtrack2.clear();
//    // Assign literals (but -reslit) to false
//    for (const LitZ *lz=candidate; !lz->isZ(); ++lz) {
//      Lit l=lz->the_lit();
//      if (l != -reslit && !A.is_false(l)) {
//        A.set_false(l);
//        backtrack2.push_back(l);
//      }
//    }
//
//
//    // Follow units
//    rd_follow_units([&backtrack2](Lit l){backtrack2.push_back(l);});
//
//    // Check conflict
//    {
//      IdZ ccidz = DB.fetch_idz();
//      if (ccidz.isZ()) fail("Expected conflict clause id");
//      check_conflict(ccidz.the_id());
//    }
//
//    // Backtrack over RAT-assignments
//    for (Lit l : backtrack2) A.unset(l);
//
//  });
//
//  // Read terminator of RAT-clauses
//  if (!DB.fetch_idz().isZ()) fail("Proof contains more RAT-clauses than expected");
//
//  #endif

  // Backtrack over RUP-assignments
  for (Lit l : backtrack) A.unset(l);

  // Add lemma as clause
  CM.add(id,c);

  if (num_undec == 1) set_false_induced(-undec_lit.the_lit()); // If added unit-lemma, modify assignment
}

inline size_t lit_index(Lit l) {
  return l.get()<0?2*static_cast<idx_t>(-l.get()):2*static_cast<idx_t>(l.get())+1;
}


void State::check_deferred_rats() {
  if (have_deferred_rats) {
    clog<<"Checking deferred RAT exhaustiveness"<<endl;
    litmap<vector<Id>*> lcmap;

    // Initialize clause lists for relevant literals
    for (auto lp : rat_positions) {
      if (lp.second) {
        lcmap[-lp.first] = new vector<Id>();
      }
    }


    auto fetch_clause = [this]() {
      const LitZ *c = DB.current_clause();
      while (!DB.fetch_litz().isZ());
      return c;
    };

    auto register_clause = [this,&lcmap](Id id, const LitZ *c) {
      CM.add(id,c);

      for (const LitZ *lz = c; !lz->isZ();++lz) {
        vector<Id>* llist = lcmap[lz->the_lit()];
        if (llist) llist->push_back(id);
      }
    };

    // Start a second pass over DB
    DB.init_new_pass();
    CM.clear();

    // Formula
    while (!DB.at_proof_start()) {
      Id id = DB.fetch_clause_id();
      register_clause(id, fetch_clause());
    }

    // Proof
    // Skip over initial unit propagation
    while (!DB.fetch_idz().isZ());

    bool done=false;
    while (!done) {
      dbg_last_item = DB.current_raw();

      switch (DB.fetch_proof_item_type()) {
        case Store::proof_item_type::LEMMA: {
          Id id = DB.fetch_id();
          const cdb_t* position_for_rat = DB.current_raw();
          const LitZ *c = fetch_clause();

          // Skip over RUP units
          while (!DB.fetch_idz().isZ());

          // Check if RAT
          if (DB.fetch_idz().isZ()) {
            // Get reslit, and check candidates
            Lit reslit = DB.fetch_lit();
            vector<Id> *candidates = lcmap[-reslit];


            if (candidates==nullptr) {
              cerr<<"No list for literal "<<(-reslit).get()<<endl;
              fail();
            }

            assert(candidates);

            size_t cidx=0;

            // Iterate over RAT-proofs
            while (true) {
              // Skip over deleted candidate clauses. Note: we do not remove them, as this would require re-sorting
              while (cidx<candidates->size() && !CM.contains((*candidates)[cidx])) cidx++;

              IdZ cidz = DB.fetch_idz();
              if (cidz.isZ()) break;

              Id cid = cidz.the_id();

              if (cidx >= candidates->size()) fail("RAT exhaustiveness check (deferred): Proof contains too much candidates.");
              if (cid != (*candidates)[cidx++]) fail("RAT exhaustiveness check (deferred): Candidate mismatch");

              // Skip over units and conflict-clause or blocked indicator
              while (!DB.fetch_idz().isZ());
              DB.fetch_idz();
            }

            if (cidx!=candidates->size()) fail("RAT exhaustiveness check (deferred): Proof contains too few candidates.");

            // Stop collecting for this literal if last time used!
            if (rat_positions[reslit] == position_for_rat) {
              delete candidates;
              lcmap[-reslit]=nullptr;
            }
          }

          // Register the lemma
          register_clause(id,c);

          // Skip over induced unit propagations
          while (!DB.fetch_idz().isZ());

          DB.next_item();
        }
        break;
        case Store::proof_item_type::DELETION:
          CM.del(DB.fetch_id()); DB.next_item();
        break;
        case Store::proof_item_type::CONFLICT:
          done=true;
        break;
      }
    }

    // DEBUG: Consistency check: Everything should have been removed from lcmap
    for (auto lp : lcmap) if (lp.second!=nullptr) fail("DEBUG: lcmap not empty");

  }
}


void State::rd_del() {
  CM.del(DB.fetch_id());
}

void State::rd_conflict() {
  check_conflict(DB.fetch_id());
}

void State::rd_induced_units() {
  rd_follow_units([](Lit){}); // No backtracking
}


inline bool State::rd_proof_item() {
  dbg_last_item = DB.current_raw();

  switch (DB.fetch_proof_item_type()) {
    case Store::proof_item_type::LEMMA: rd_lemma(); rd_induced_units(); DB.next_item(); return false;
    case Store::proof_item_type::DELETION: rd_del(); DB.next_item(); return false;
    case Store::proof_item_type::CONFLICT: rd_conflict(); DB.next_item(); return true;
  }
  return false; // Unreachable code, but gcc cannot analyze that. (Probably it cannot assume proof_item_type to be valid.)
}


void State::rd_proof() {
  rd_induced_units(); DB.next_item();
  while (!rd_proof_item());
  check_deferred_rats();
}


void print_usage() {
  cerr<<"Usage fvc_checker <dimacs-file> <proof-file>"<<endl;
}

void print_success_msg() {
  cout<<"s CERTIFIED UNSAT"<<endl;
}


int main(int argc, char **argv) {
  if (sizeof(lit_t) != sizeof(idx_t)) fail("lit_t and idx_t have different sizes");
  if (sizeof(lit_t) != sizeof(LitZ)) fail("lit_t and LitZ have different sizes");

  if (argc!=3) {print_usage(); return 2;}

  State S;

  {
    ifstream cnf;
    ifstream prf;

    clog<<"Parsing cnf"<<endl;
    cnf.open(argv[1],ifstream::in);
    S.parse_dimacs(cnf);
    cnf.close();
    clog<<"Done"<<endl;

    clog<<"Parsing proof"<<endl;
    prf.open(argv[2],ifstream::in);
    S.parse_fvc(prf);
    prf.close();
    clog<<"Done"<<endl;
  }


  clog<<"Reading clauses"<<endl;
  bool trivial_conflict = S.rd_cnf();
  clog<<"Done"<<endl;
  if (trivial_conflict) {
    clog<<"Trivial conflict on clauses"<<endl;
    print_success_msg();
    return 0;
  }

  clog<<"Checking proof"<<endl;
//  ProfilerStart("fvc_check.profile");
  S.rd_proof();
//  ProfilerStop();
  clog<<"Done"<<endl;


  cout<<"s CERTIFIED UNSAT"<<endl;

  return 0;
}

