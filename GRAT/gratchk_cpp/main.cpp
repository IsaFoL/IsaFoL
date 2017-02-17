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


  FIXME
    * Currently, on deletions, we cannot ensure that deleted clause will actually make it into the core. Thus, silently ignore such deletions.
      obvious fix: let gratgen trim the proof, and output only relevant deletions as early as possible.
      
      Similarly, for RAT-candidates, the checker does not know whether the RAT-candidate will actually make it into the core. Ie, we should silently ignore invalid RAT-candidates.
      Here, a fix is more complicated: As the RAT-candidate may generate new core lemmas himself, we cannot just add RAT-candidates lately, when they become core:
      This would require to replay the RAT-proof in the context of the RAT-candidate, inducing a set of new core lemmas, which have to be checked in seaquence ... and may need RAT again.
      


  Change plan, towards simpler checker:
    DONE * Do first pass over proof to collect RAT-literals, then do everything in second pass.
      Use counters instead of positions to decide on discontinuation of a collection for a literal.
    
    DONE * Allow for blocked candidates to be missing in proof
  
    * Support RAT-literals written to proof file.
        0 0 0 lit1 count1 ... litN countN 0
        Must occur as first item. 
      
      
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
    const cdb_t* end_at = min(dbg_valid_item_end,dbg_last_item+100);

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


enum class item_type : cdb_t {
  UNIT_PROP = 1,    // id* 0                                  unit clause ids
  DELETION = 2,     // id                                     id to delete
  RUP_LEMMA = 3,    // id lit* 0 id* 0 id                     new-id clause units conflict-id
  RAT_LEMMA = 4,    // lit id lit* 0 id* 0 (id id* 0 id)* 0   reslit new-id clause units candidate-proofs
  CONFLICT = 5,     // id                                     conflict-id
  RAT_COUNTS = 6    // (lit num)* 0                           literal count
};


// Holds raw clause and proof data
class Store {
  public:
    Store();

    size_t size();

    void parse_dimacs(istream &in);
    void parse_grat(istream &in);


    /*
      Generic fetch functions
    */
    idx_t fetch_unsigned();
    lit_t fetch_signed();

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


    /* Iterations: A pass over the formula or proof has to be initialized. 
     * Once initialized, no new items must be added to the store.
     * The end of the pass can be queried by at_end();
     */
    
    /* Initializes a pass over the formula, and resets the next-id information
     */
    void init_formula_pass();

    /* Initializes a pass over the proof.
     */
    void init_proof_pass();
    
    /* Checks whether current position is one behind last (of formula or proof, depending on current pass)
     */
    bool at_end();

    /* Move on to next item. PRE: Current position at end of item, current item valid.
     * If current position is at last item, the new position will be one behind last.
     */
    void next_item(); 

    /*
      Fetches the type of the next proof item, and sets current position to start of information for this item.
    */
    item_type fetch_proof_item_type();
    item_type peek_proof_item_type();


    void dbg_dump_proof_struct(ostream& out);
    

  private:
    vector<cdb_t> data;       // Raw data

    size_t proof_start_pos=0; // First item of proof

    cdb_t *current = nullptr; // Current position when interpreting data
    idx_t next_id = 1;        // Next id for determining clause ids

    cdb_t* current_item_start = nullptr; // Start of current item
    
    
    bool in_proof = false;         // Set if in proof pass
    bool end_flag = false;         // Set if past-end
    bool backwards_proof = false;  // Set for backwards proof
    


  private:
    void parse_raw(istream &in);

    cdb_t fetch_raw();
    cdb_t peek_raw();

    item_type ensure_valid_item_type(cdb_t);


  private:
    // Delete
    Store(const Store&) = delete;
    void operator=(const Store&) = delete;



};



Store::Store() : data() {}

inline cdb_t Store::fetch_raw() { assert(current); if (current > &data.back()) fail("Read past end of store"); return *(current++);}
inline cdb_t Store::peek_raw() { assert(current); if (current > &data.back()) fail("Read past end of store"); return *current;}

inline const cdb_t* Store::current_raw() {return current;}

inline lit_t Store::fetch_signed() {return static_cast<lit_t>(fetch_raw());}
inline idx_t Store::fetch_unsigned() {return static_cast<idx_t>(fetch_raw());}


inline IdZ Store::fetch_idz() {return IdZ(fetch_unsigned());}
inline Id Store::fetch_id() {return fetch_idz().the_id(); }
inline LitZ Store::fetch_litz() {return LitZ(fetch_signed());}
inline Lit Store::fetch_lit() {return fetch_litz().the_lit();}

inline const LitZ* Store::current_clause() {return reinterpret_cast<const LitZ*>(current);}

inline void Store::next_item() {
  assert(!end_flag);
  if (in_proof) {
    if (backwards_proof) {
      if (current_item_start == data.data() + proof_start_pos) {
        end_flag=true;
        current=nullptr;
      } else  {
        current = current_item_start - 1; // Set current to size-suffix of previous item
        if (current < data.data() + proof_start_pos + *current) fail("Size suffix would lead before proof");
        current = current - *current;
      }
      current_item_start = current;      
    } else {
      if (current_item_start + *current_item_start == data.data() + data.size()) {
        end_flag = true; 
        current = current_item_start = nullptr;
      } else {
        if (current_item_start + *current_item_start + 1 >= data.data() + data.size()) fail("Size of item exceeds proof size");
        current = current_item_start = current_item_start + *current_item_start;
        ++current;
      }
    }
  } else {
    if (current == data.data() + proof_start_pos) {
      end_flag=true;
      current = nullptr;
    }
    current_item_start = current;
  }
}

inline item_type Store::ensure_valid_item_type(cdb_t ty) {
  switch (static_cast<item_type>(ty)) {
    case item_type::CONFLICT:
    case item_type::DELETION:
    case item_type::RUP_LEMMA:
    case item_type::RAT_LEMMA:
    case item_type::UNIT_PROP:
    case item_type::RAT_COUNTS:
      return static_cast<item_type>(ty);
    default:
      cerr<<"Unknown item type "<<ty<<endl;
      fail();
  }
  return item_type::RAT_COUNTS; // Dead code not detected by compiler, but we have to return something here!
}

inline item_type Store::peek_proof_item_type() {
  assert(in_proof);
  return ensure_valid_item_type(peek_raw());
}

inline item_type Store::fetch_proof_item_type() {
  assert(in_proof);
  dbg_last_item = current_raw();
  return ensure_valid_item_type(fetch_raw());
}

inline Id Store::fetch_clause_id() {return Id(next_id++);}


void Store::init_formula_pass() {
  current = current_item_start = data.data();
  next_id=1;
  in_proof=false;
  end_flag=false;
}

void Store::init_proof_pass() {
  if (backwards_proof) {
    if (static_cast<size_t>(data.back())>=data.size()) fail("Last item's size suffix leads before data");
    current = current_item_start = data.data() + (data.size() - 1 - data.back());
  } else {
    current = current_item_start = data.data() + proof_start_pos;
  }
  
  
  in_proof=true;
  end_flag=false;
}

inline bool Store::at_end() {
    return end_flag;
}


size_t Store::size() {return data.size();}

void Store::parse_dimacs(istream &in) {
  data.clear(); data.shrink_to_fit();

  parse_raw(in);

  proof_start_pos=data.size();

  if (data.size() == 0) fail("Empty proof file");
  if (data.back()!=0) fail("DIMACS file must end with a 0");
}


void Store::parse_grat(istream &in) {
  // Header
  if (in.get() != 'G' || in.get() != 'R' || in.get() != 'A' || in.get() != 'T') fail("Expected GRAT header");
  
  { // Direction
    char d = in.get();
    if (d=='f') backwards_proof=false; else if (d=='b') backwards_proof=true; else fail("Invalid direction flag, must be f or b");
  }

  { // Textual/Binary mode
    char m = in.get();
    if (m=='b') fail("Binary mode not yet supported");
    else if (m!='t') fail("Invalid mode indicator");
  }
  
  { // Word size
    size_t sz; in>>ws; in>>sz;
    if (sz==0) fail("Missing word-size field in header");
    if (sz>sizeof(cdb_t)) {
      cerr<<"Proof generated with larger word-size ("<< sz <<") than supported by this checker ("<<sizeof(cdb_t)<<")"<<endl;
      fail();
    }
  }
  
  // Terminator of header
  {
    size_t trm; in>>ws; in>>trm;
    if (trm != 0) fail("Additional header fields, this checker supports GRAT[fb][bt]<word-size>0");
  }
  
  parse_raw(in);
  data.shrink_to_fit();
  current = data.data();

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


void Store::dbg_dump_proof_struct(ostream &out) {
  size_t pos = data.size();
  
  {
    for (size_t p = 308217300; p<308217315;++p)
      if (data.size()>p) {
        clog<<"@"<<p<<": "<<data[p]<<endl;
      }
  }
  
  // Iterate over items
  while (pos > proof_start_pos) {
    // ITEM SZ *
    --pos;
    size_t sz = static_cast<size_t>(data[pos]);
    // ITEM * SZ
    if (pos < sz) fail("Item size leads before proof");
    if (sz == 0) fail("Zero-size item");

    pos-=sz;
    // * ITEM SZ
    cdb_t ty = data[pos];
    
    if (ty<1 || ty>6) fail("Invalid item type");
    
    out<<"@"<<pos<<": "<<ty<<" [...] "<<sz<<endl;
  }
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
    void del_if_valid(Id id);


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

inline void Clausemap::del_if_valid(Id id) {
  if (index(id) < data.size()) data[index(id)]=nullptr;
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


    inline void clear() {data.clear();}
    
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

//     litmap<const cdb_t*> rat_positions;  // rat_positions[l] is position of last lemma that used l as rat resolution literal
//     bool have_deferred_rats=false;

    litmap<size_t> rat_counts;          // Count how often a literal is used as resolution literal in RAT-proof
    litmap<vector<Id>*> lcmap;          // Clause ids containing specified literal, or nullptr if clauses not counted for this literal


    vector<Lit> backtrack; // Stored globally

    void set_false_induced(Lit l);

    // Read clause. Return true if this yields UNSAT already.
    bool rd_clause();

    // Check that id refers to unit clause, and return unit literal. Returns 0 on tautology, if ignoring tautologies is allowed (cfg_ignore_taut_units)
    LitZ check_unit(Id id);

    // Check that id refers to conflict clause
    void check_conflict(Id id);

    bool rd_proof_item();
    void rd_lemma(bool is_rat);
    void rd_del();
    void rd_conflict();
    void rd_induced_units();

    void rd_rat_counts();

    template<typename BT> void rd_follow_units(const BT &backtrack);

    void gather_rat_counts(); // Do a pass over the file and count RAT-literals
    
    /* Register literal l as part of clause id. Updates lcmap if literal is interesting.
     * This must be executed for all literals of all lemmas and clauses added to the database. 
     * For efficiency reasons (loop-merging), we did not encapsulate this functionality with CM.add, which would be the cleaner approach from a design perspective.
     */
    void register_clause_lit(Id id, Lit l); 
    
    /* Skips over (remaining) literals of clause, and registers the clause for the literals.
     */
    void skip_lits_register(Id id);
    
    //void check_deferred_rats();

    // Read all clauses. Return true if UNSAT.
    bool rd_cnf();
    

  public:
    State();

    ~State();

    // TODO: Ultimately, we want a verifier with both, auto-unit and taut_units switched off, as it should be easiest to implement.
    /* If set, on adding a unit clause or lemma, the unit literal is automatically assigned.
     * Otherwise, there must be a unit-clause entry in the certificate until the unit literal is assigned.
     */
    bool cfg_auto_unit = false;
    /* If set, a unit-clause entry is ignored if it is associated to a tautology. This may happen
     * if the certificate generator has a different policy of assigning unit-literals than auto_unit.
     */
    bool cfg_ignore_taut_units = false;
    
    /* If set, deletions of invalid ids are silently ignored. Depending on the implementation, the certificate generator may not 
     * know yet whether a clause will be included in the proof at all, when it emits the deletion, which results in deletions of 
     * invalid ids.
     */
    bool cfg_ignore_invalid_deletions = true;
    
    /* If set, and RAT-counts are not present in certificate, they are gathered by extra pass.
     */
    bool cfg_allow_gather_rat = false;
    
    inline void parse_dimacs(istream &in) {DB.parse_dimacs(in);}
    inline void parse_grat(istream &in) {DB.parse_grat(in);}

    // Read and check clauses and proof
    void check();

    void dbg_dump_proof_struct(ostream &out) {DB.dbg_dump_proof_struct(out);}


};


State::State() : DB(), A(), CM(), rat_counts(), lcmap(), backtrack() {}
State::~State() {}

inline void State::set_false_induced(Lit l) {
  A.set_false(l);
}


inline void State::register_clause_lit(Id id, Lit l) {
  if (lcmap[l]) lcmap[l]->push_back(id);
}

inline void State::skip_lits_register(Id id) {
  while (true) {
    LitZ lz = DB.fetch_litz();
    if (lz.isZ()) break;
    register_clause_lit(id,lz.the_lit());
  }
}


bool State::rd_clause() {
  Id id = DB.fetch_clause_id();

  CM.add(id,DB.current_clause());

  if (cfg_auto_unit) {
    // Scan over clause's literals, and check for conflict or unit clause
    LitZ lu = LitZ(0);
    for (LitZ lz = DB.fetch_litz(); !lz.isZ(); lz=DB.fetch_litz()) {
      Lit l = lz.the_lit();
      register_clause_lit(id,l);

      if (lz == lu) continue; // Duplicate of stored unit literal

      if (A.is_true(l) || (!A.is_false(l) && !lu.isZ())) { // Tautology or 2 undecided literals
        skip_lits_register(id);   // Skip over rest, and return
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
  } else {
    // Skip over clause's literals
    skip_lits_register(id);
    return false;
  }
}


bool State::rd_cnf() {
  DB.init_formula_pass();
  while (!DB.at_end()) {
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

inline LitZ State::check_unit(Id id) {
  const LitZ *c = CM.lookup(id);

  LitZ ul = 0;

  for (auto lz=c;!lz->isZ();++lz) {
    Lit l = lz->the_lit();
    if (A.is_true(l)) {
      if (cfg_ignore_taut_units) {
        return LitZ(0);
      } else {
        cerr<<"True literal in clause assumed to be unit: clause-id "<< id.get() <<" true lit " << l.get() <<endl; 
        cerr<<"You may use the ignore_taut_units configuration to ignore such cases."<<endl;
        fail();
      }
     
    }
    if (!A.is_false(l)) {
      if (ul.isZ()) ul=*lz;
      else if (ul != *lz) {
        cerr<<"Clause "<<id.get()<<": "; print_clause(c,cerr); cerr<<endl;
        cerr<<"Undec literals are "<<ul.get()<<" and "<<lz->get()<<endl;
        fail("2-undec in clause assumed to be unit");
      }
    }
  }

  if (ul.isZ()) {
    cerr<<"Conflict in clause assumed to be unit: "<<id.get()<<endl;
    fail();
  }
  return ul;
}

inline void State::check_conflict(Id id) {
  for (const LitZ *lz = CM.lookup(id);!lz->isZ();++lz)
    if (!A.is_false(lz->the_lit())) {
      cerr<<"Non-false literal "<< lz->get() <<" in clause "<< id.get() <<" assumed to be conflict"<<endl;
      fail();
    }

}

template<typename BT> inline void State::rd_follow_units(const BT &add_backtrack) {
  while (true) {
    IdZ uidz = DB.fetch_idz();
    if (uidz.isZ()) break;
    LitZ ulitz = check_unit(uidz.the_id());
    if (!ulitz.isZ()) {
      Lit ulit = ulitz.the_lit();
      A.set_false(-ulit);
      add_backtrack(-ulit);
    }
  }
}


inline bool clause_contains(const LitZ *lz, Lit cl) {
  for (;!lz->isZ();++lz) if (lz->the_lit()==cl) return true;
  return false;
}


void State::gather_rat_counts() {
  // Clear maps
  for (auto i : lcmap) if (i.second) delete i.second;
  lcmap.clear();
  rat_counts.clear();
  
  // Start pass over proof only
  DB.init_proof_pass();
  
  // Skip over initial unit propagation
  while (!DB.fetch_idz().isZ()); DB.next_item();

  bool done=false;
  while (!done) {
    auto type = DB.fetch_proof_item_type();
    switch (type) {
      case item_type::RAT_LEMMA:
      {
        Lit reslit = DB.fetch_lit();
        ++rat_counts[-reslit];
        
        // Skip over rest of proof
        while (!DB.fetch_idz().isZ()) {
          // Skip over units and conflict-clause or blocked indicator
          while (!DB.fetch_idz().isZ());
          DB.fetch_idz();
        }
        DB.next_item();
      }
      break;
      case item_type::CONFLICT:
        done=true;
      break;
      default:
        DB.next_item();
      
    }
  }
  
  // Initialize lcmap
  for (auto i : rat_counts) if (i.second != 0) lcmap[i.first] = new vector<Id>();
  
  
}


void State::rd_rat_counts() {
  // Clear maps
  for (auto i : lcmap) if (i.second) delete i.second;
  lcmap.clear();
  rat_counts.clear();

  while (true) {
    LitZ lz = DB.fetch_litz();
    if (lz.isZ()) break;
    Lit l = lz.the_lit();

    if (rat_counts[-l] != 0) fail("Duplicate literal for RAT-counts");
    
    size_t n = DB.fetch_unsigned();
    rat_counts[-l] = n;
  }

  // Initialize lcmap
  for (auto i : rat_counts) if (i.second != 0) lcmap[i.first] = new vector<Id>();
}








void State::rd_lemma(bool is_rat) {
  LitZ reslitz(0);
  if (is_rat) reslitz = DB.fetch_lit().get();
  
  Id id = DB.fetch_id();
  const LitZ *c = DB.current_clause();

  backtrack.clear();

  // Start rup checking. On the way of fetching clause, also check for unit clause
  unsigned num_undec = 0; LitZ undec_lit = 0;
  while (true) {
    LitZ lz = DB.fetch_litz();
    if (lz.isZ()) break;
    Lit l = lz.the_lit();

    /* Note: It's ok to register the lemma for its literals already here, although we have not yet proved the lemma:
     *  For a RAT-check, we look for clauses containing -reslit, however, this clause contains reslit, and is checked to not be a tautology.
     */
    register_clause_lit(id,l);
    
    if (A.is_true(l)) fail("Tautological lemma, should not occur in proof.");
    if (!A.is_false(l)) {
      ++num_undec; undec_lit=lz;
      A.set_false(l);
      backtrack.push_back(l);
    }
  }

  // Literals of clause set to false, now read and check RUP unit clauses
  rd_follow_units([this](Lit l){backtrack.push_back(l);});

  if (!is_rat) {
    // Read conflict clause id
    Id cid = DB.fetch_id();

    check_conflict(cid);
    for (Lit l : backtrack) A.unset(l);
    CM.add(id,c);

    if (num_undec == 1 && cfg_auto_unit) set_false_induced(-undec_lit.the_lit()); // If added unit-lemma, modify assignment
    return;
  }

  // RAT
  Lit reslit = reslitz.the_lit();

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

  // Gather RAT-candidates that we actually want to see proofs for
  assert(lcmap[-reslit]);

  for (auto cid : *(lcmap[-reslit])) {
    // Check if blocked, otherwise add to candidate list
    const LitZ *candidate = CM.lookup(cid);
    bool blocked=false;
    for (const LitZ *lz=candidate;!lz->isZ();++lz) {
      if (lz->the_lit() != -reslit && A.is_true(lz->the_lit())) {
        blocked=true;
        break;
      }
    }
    
    if (!blocked) candidates.push_back(cid);
  }

  // Count-down usage-counter, and stop collection for this literal if not needed any more
  assert(rat_counts[-reslit]);
  if (--rat_counts[-reslit] == 0) {
    delete lcmap[-reslit];
    lcmap[-reslit]=nullptr;
  }
  

  // Iterate over candidates present in proof
  auto cand_it = candidates.begin();  // TODO: Allow arbitrary ordering of candidates, if this does not decrease performance too much! (Use unordered_set)

  while (true) {
    IdZ idz = DB.fetch_idz();
    if (idz.isZ()) break;
    Id id=idz.the_id();
    
    if (cand_it == candidates.end() || id != *cand_it) {
      // We do not require a proof for this candidate, skip over it
      while (!DB.fetch_idz().isZ()); // Units
      DB.fetch_idz();                // Conflict clause id, or 0 if blocked 
    } else {
      // Check proof of candidate
      const LitZ *candidate = CM.lookup(id);
      backtrack2.clear();
      
      // Assign literals (but -reslit) to false. Note: We know that candidate is not blocked, as it is in candidates list.
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
      ++cand_it;  // Move to next candidate
    }
  }

  // Check that we have actually seen all required candidates
  if (cand_it != candidates.end()) {
    fail("RAT-proof: Missing proof for candidates (or invalid ordering)");
  }

  // Backtrack over RUP-assignments
  for (Lit l : backtrack) A.unset(l);

  // Add lemma as clause
  CM.add(id,c);

  if (num_undec == 1 && cfg_auto_unit) set_false_induced(-undec_lit.the_lit()); // If added unit-lemma, modify assignment
}

inline size_t lit_index(Lit l) {
  return l.get()<0?2*static_cast<idx_t>(-l.get()):2*static_cast<idx_t>(l.get())+1;
}


// void State::check_deferred_rats() {
//   if (have_deferred_rats) {
//     clog<<"Checking deferred RAT exhaustiveness"<<endl;
//     litmap<vector<Id>*> lcmap;
// 
//     // Initialize clause lists for relevant literals
//     for (auto lp : rat_positions) {
//       if (lp.second) {
//         lcmap[-lp.first] = new vector<Id>();
//       }
//     }
// 
// 
//     auto fetch_clause = [this]() {
//       const LitZ *c = DB.current_clause();
//       while (!DB.fetch_litz().isZ());
//       return c;
//     };
// 
//     auto register_clause = [this,&lcmap](Id id, const LitZ *c) {
//       CM.add(id,c);
// 
//       for (const LitZ *lz = c; !lz->isZ();++lz) {
//         vector<Id>* llist = lcmap[lz->the_lit()];
//         if (llist) llist->push_back(id);
//       }
//     };
// 
//     // Start a second pass over DB
//     DB.init_new_pass();
//     CM.clear();
// 
//     // Formula
//     while (!DB.is_in_proof()) {
//       Id id = DB.fetch_clause_id();
//       register_clause(id, fetch_clause());
//       DB.next_item();
//     }
//     
//     // Proof
//     // Skip over initial unit propagation
//     while (!DB.fetch_idz().isZ()); DB.next_item();
// 
//     bool done=false;
//     while (!done) {
//       dbg_last_item = DB.current_raw();
// 
//       switch (DB.fetch_proof_item_type()) {
//         case Store::proof_item_type::LEMMA: {
//           Id id = DB.fetch_id();
//           const cdb_t* position_for_rat = DB.current_raw();
//           const LitZ *c = fetch_clause();
// 
//           // Skip over RUP units
//           while (!DB.fetch_idz().isZ());
// 
//           // Check if RAT
//           if (DB.fetch_idz().isZ()) {
//             // Get reslit, and check candidates
//             Lit reslit = DB.fetch_lit();
//             vector<Id> *candidates = lcmap[-reslit];
// 
// 
//             if (candidates==nullptr) {
//               cerr<<"No list for literal "<<(-reslit).get()<<endl;
//               fail();
//             }
// 
//             assert(candidates);
// 
//             size_t cidx=0;
// 
//             // Iterate over RAT-proofs
//             while (true) {
//               // Skip over deleted candidate clauses. Note: we do not remove them, as this would require re-sorting
//               while (cidx<candidates->size() && !CM.contains((*candidates)[cidx])) cidx++;
// 
//               IdZ cidz = DB.fetch_idz();
//               if (cidz.isZ()) break;
// 
//               Id cid = cidz.the_id();
// 
//               if (!cfg_ignore_invalid_rat_candidates || CM.contains(cid)) {
//                 if (cidx >= candidates->size()) fail("RAT exhaustiveness check (deferred): Proof contains too much candidates.");
//                 if (cid != (*candidates)[cidx++]) fail("RAT exhaustiveness check (deferred): Candidate mismatch");
//               }
// 
//               // Skip over units and conflict-clause or blocked indicator
//               while (!DB.fetch_idz().isZ());
//               DB.fetch_idz();
//             }
// 
//             if (cidx!=candidates->size()) fail("RAT exhaustiveness check (deferred): Proof contains too few candidates.");
// 
//             // Stop collecting for this literal if last time used!
//             if (rat_positions[reslit] == position_for_rat) {
//               delete candidates;
//               lcmap[-reslit]=nullptr;
//             }
//           }
// 
//           // Register the lemma
//           register_clause(id,c);
// 
//           // Skip over induced unit propagations
//           while (!DB.fetch_idz().isZ());
// 
//           DB.next_item();
//         }
//         break;
//         case Store::proof_item_type::DELETION:
//           if (cfg_ignore_invalid_deletions) CM.del_if_valid(DB.fetch_id()); else CM.del(DB.fetch_id()); 
// 
//           DB.next_item();
//         break;
//         case Store::proof_item_type::CONFLICT:
//           done=true;
//         break;
//       }
//     }
// 
//     // DEBUG: Consistency check: Everything should have been removed from lcmap
//     for (auto lp : lcmap) if (lp.second!=nullptr) fail("DEBUG: lcmap not empty");
// 
//   }
// }


void State::rd_del() {
  if (cfg_ignore_invalid_deletions) CM.del_if_valid(DB.fetch_id()); else CM.del(DB.fetch_id()); 
}

void State::rd_conflict() {
  check_conflict(DB.fetch_id());
}

void State::rd_induced_units() {
  rd_follow_units([](Lit){}); // No backtracking
}


inline bool State::rd_proof_item() {
  dbg_last_item = DB.current_raw();

  auto ty = DB.fetch_proof_item_type();
  switch (ty) {
    case item_type::RUP_LEMMA: case item_type::RAT_LEMMA: rd_lemma(ty==item_type::RAT_LEMMA); DB.next_item(); return false;
    case item_type::UNIT_PROP: rd_induced_units(); DB.next_item(); return false;
    case item_type::DELETION: rd_del(); DB.next_item(); return false;
    case item_type::CONFLICT: rd_conflict(); DB.next_item(); return true;
    case item_type::RAT_COUNTS: fail("RAT_COUNTS item in middle of proof"); return false;
    default: assert(false); // Should be detected on fetching type
  }
  return false; // Unreachable code, but gcc cannot analyze that. (Probably it cannot assume proof_item_type to be valid.)
}


void State::check() {
  
  // Read or gather RAT-counts
  DB.init_proof_pass();
  dbg_last_item = DB.current_raw();
  
  if (DB.peek_proof_item_type() == item_type::RAT_COUNTS) {
    DB.fetch_proof_item_type();
    rd_rat_counts();
    DB.next_item();
  } else {
    if (!cfg_allow_gather_rat) fail("RAT-counts not present, and gathering switched off");
    gather_rat_counts();
  }

  // Read formula
  bool trivial_conflict = rd_cnf();
  if (trivial_conflict) {
    clog<<"Trivial conflict on clauses"<<endl;
    return;
  }
  
  // Read proof
  DB.init_proof_pass();
  // Skip over RAT-counts item, if any
  if (DB.peek_proof_item_type() == item_type::RAT_COUNTS) {
    DB.fetch_proof_item_type();
    while (!DB.fetch_litz().isZ()) DB.fetch_idz();
    DB.next_item();  
  }
  while (!rd_proof_item());
  
  // DEBUG: Consistency check: Everything should have been removed from lcmap, and counts should be down to zero
  for (auto lp : lcmap) if (lp.second!=nullptr) fail("DEBUG: lcmap not empty");
  for (auto c : rat_counts) if (c.second != 0) fail("Positive rat-count remaining");
}


void print_usage() {
  cerr<<"Usage fvc_checker <dimacs-file> <proof-file> <options>"<<endl;
  cerr<<"Options:"<<endl;
  cerr<<"  -g, --gather-rat Allow extra pass for rat-counts"<<endl;
}

void print_success_msg() {
  cout<<"s CERTIFIED UNSAT"<<endl;
}


int main(int argc, char **argv) {
  if (sizeof(lit_t) != sizeof(idx_t)) fail("lit_t and idx_t have different sizes");
  if (sizeof(lit_t) != sizeof(LitZ)) fail("lit_t and LitZ have different sizes");

  State S;

  
  if (argc<3) {print_usage(); return 2;}

  string dimacs_file = argv[1];
  string proof_file = argv[2];
  
  bool cfg_dump_struct = false;
  
  for (int i=3;i<argc;++i) {
    string a = argv[i];
    
    if (a=="-g" || a=="--gather-rat") S.cfg_allow_gather_rat=true;
    if (a=="-d" || a=="--dump-struct") cfg_dump_struct=true;
    else fail(("Unknown command line argument: " + a).c_str());
  }
  

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
    S.parse_grat(prf);
    prf.close();
    clog<<"Done"<<endl;
  }

  if (cfg_dump_struct) {
    clog<<"Dumping proof structure to stdout"<<endl;
    S.dbg_dump_proof_struct(cout);
    clog<<"Done"<<endl;
  } else {
    clog<<"Checking proof"<<endl;
  //  ProfilerStart("fvc_check.profile");
    S.check();
  //  ProfilerStop();
    clog<<"Done"<<endl;


    cout<<"s CERTIFIED UNSAT"<<endl;
  }

  return 0;
}

