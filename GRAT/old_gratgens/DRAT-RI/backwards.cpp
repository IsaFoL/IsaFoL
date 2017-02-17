/*
  Author: Peter Lammich
  Obviously inspired by drat-trim (Marijn Heule and Nathan Wetzler).
*/

/*
  TODO:
    On first pass, we can count literal frequencies, and then decide for which resolution literals to collect occurs-in maps.

*/


#include <cstdlib>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <algorithm>
#include <cassert>
#include <limits>
#include <unordered_map>
#include <cstdint>

using namespace std;

typedef intptr_t cdb_t;
typedef cdb_t lit_t;
typedef cdb_t cid_t;


void fail() {
  clog<<"FAILED"<<endl;
  exit(1);
}




/***************************************************
  Clause Database
***************************************************/

class ClauseDB {
  public:
    ClauseDB();

    // Parsing mode
    void p_begin_proof();     // Begin reading proof
    void p_finish_proof();    // Finish reading proof, and switch to checking mode

    void p_begin_clause();    // Begin reading a clause
    void p_add_lit(lit_t l);  // Add literal to current clause
    void p_finish_clause();   // Finish reading a clause

    void p_begin_deletion();  // Begin reading clause deletion
    void p_del_lit(lit_t l);  // Read literal of deletion clause
    void p_finish_deletion(); // Finish clause deletion

    size_t get_num_vars();    // Return maximum encountered variable +1.

    // Scanning mode
    enum class item_type {CLAUSE, LEMMA, DELETION};
    item_type s_current_item();
    bool s_at_end();            // Returns true if current position is at end of database
    bool s_at_begin();          // Returns true if current position is at begin of database
    bool s_at_proof_start();    // Returns true if current position is first item of proof

    bool s_in_formula();        // True if position is in formula

    cdb_t *s_current_clause(); // Current clause to be added or deleted

    cid_t get_clause_id(cdb_t *c);    // Get id of clause
    lit_t *get_clause_lit1(cdb_t *c); // Get pointer to first literal of clause
    lit_t& pivot(cdb_t* c);           // Get pivot element


    cdb_t *s_move_next(lit_t *hint = nullptr);   // Move to next item, hint hints at position in the literals of a clause.
    cdb_t *s_move_prev();                        // Move to previous item


    // Core clauses
    void mark_core(cdb_t *c);
    bool is_core(cdb_t *c);


    void dump_clause(cdb_t* c, ostream &out);


  private:
    ClauseDB (const ClauseDB &) = delete;
    ClauseDB &operator=(const ClauseDB&) = delete;


    vector<cdb_t> data;

    cdb_t *current = nullptr;
    cdb_t *proof_start = nullptr;

    cid_t next_id = 1;
    cdb_t max_var = 0;


    // Syntactic unit clause detection
    lit_t p_prev_del_lit=0;
    bool p_del_no_unit=false;


    // Position based clause-referencing:
    typedef size_t cpos;
    cdb_t *at_pos(cpos pos); // Get reference from position. Warning: Invalidated if db is changed.



    cpos p_item_start = 0;  // Start of current clause or deletion
    cpos p_proof_start = 0; // Start of proof

    struct Clause_Hash_Eq {
      ClauseDB &db;

      size_t operator() (const size_t &cpos) const; // Hash function
      bool operator() (const size_t &pos1, const size_t &pos2) const; // Equality
    };

    Clause_Hash_Eq cheq;  // Hash and equality function for claus-positions
    typedef unordered_multimap<size_t,size_t,Clause_Hash_Eq,Clause_Hash_Eq> clause_map_t;
    clause_map_t clause_map; // Map from clauses to their position


};


ClauseDB::ClauseDB() : data(), cheq{*this}, clause_map(0,cheq,cheq)  {}


void ClauseDB::p_begin_proof() { p_proof_start = data.size(); }
void ClauseDB::p_finish_proof() {

  // Re-allocate empty clausemap. This is safe way to free occupied memory.
  clause_map.~clause_map_t();
  new (&clause_map) clause_map_t(0,cheq,cheq);

  current = data.data();
  proof_start = data.data() + p_proof_start;
}

inline cdb_t *ClauseDB::at_pos(cpos pos) {
  return data.data() + pos;
}

inline cid_t ClauseDB::get_clause_id(cdb_t *c) {return c[0]>>1;}
inline lit_t *ClauseDB::get_clause_lit1(cdb_t *c) {return c+2;}
inline lit_t& ClauseDB::pivot(cdb_t* c) {return c[1];}

inline void ClauseDB::mark_core(cdb_t *c) { *c |= 1; }
inline bool ClauseDB::is_core(cdb_t *c) { return *c & 1; }


void ClauseDB::dump_clause(cdb_t* c, ostream &out) {
  out<<get_clause_id(c)<<" ["<< pivot(c) <<"]"<<": ";
  for (lit_t *l=get_clause_lit1(c);*l;++l) out<<*l<<" ";
  out<<"0";
}


inline size_t ClauseDB::Clause_Hash_Eq::operator() (const size_t &cpos) const {
  cdb_t *c = db.at_pos(cpos);

  size_t sum=0, prod=1, xxor=0; // The hash-function from drat-trim
  for (lit_t *l=db.get_clause_lit1(c);*l;++l) {
    prod*=*l; sum+=*l; xxor^=*l;
  }
  return (1023 * sum + prod) ^ (31 * xxor);
}

inline bool ClauseDB::Clause_Hash_Eq::operator() (const size_t &pos1, const size_t &pos2) const {
  lit_t *l1 = db.get_clause_lit1(db.at_pos(pos1));
  lit_t *l2 = db.get_clause_lit1(db.at_pos(pos2));

  size_t i=0;
  do {
    if (l1[i]!=l2[i]) return false;
  } while (l1[i++]);
  return true;
}



inline void ClauseDB::p_begin_clause() {
  p_item_start = data.size();
  data.push_back(next_id<<1); ++next_id;
  data.push_back(0); // Reserve space for pivot literal
}

inline void ClauseDB::p_add_lit(lit_t l) {
  data.push_back(l);
  max_var = max(max_var,abs(l));
}

inline void ClauseDB::p_finish_clause() {
  // Memorize pivot literal
  pivot(at_pos(p_item_start)) = *get_clause_lit1(at_pos(p_item_start));

  // Sort clause
  sort(get_clause_lit1(at_pos(p_item_start)), data.data() + data.size());

  // Add terminating zero
  data.push_back(0);

  // Add offset
  data.push_back(-static_cast<cdb_t>(data.size() - p_item_start));

  // Add clause to hashtable
  clause_map.insert({p_item_start, p_item_start});
}


inline void ClauseDB::p_begin_deletion() {
  p_item_start = data.size();
  data.push_back(0);  // Placeholder for id
  data.push_back(0);  // Placeholder for pivot
  p_prev_del_lit=0;
  p_del_no_unit=false;
}

inline void ClauseDB::p_del_lit(lit_t l) {
  data.push_back(l);
  p_del_no_unit = p_del_no_unit || (p_prev_del_lit != l);
  p_prev_del_lit = l;
}

inline void ClauseDB::p_finish_deletion() {
  sort(get_clause_lit1(at_pos(p_item_start)), data.data() + data.size());
  data.push_back(0); // Add terminating zero

  if (p_del_no_unit) {
    auto orig_c = clause_map.find(p_item_start);
    if (orig_c == clause_map.end()) {
      clog<<"Ignoring deletion of non-existent clause "; dump_clause(at_pos(p_item_start),clog);
      clog<<endl;
      data.resize(p_item_start);
    } else {
      // Let data be: 0 clause_pos ofs
      data.resize(p_item_start + 1);
      data.push_back(orig_c->second);
      data.push_back(-static_cast<cdb_t>(data.size() - p_item_start));
      // Remove this clause from clause_map
      clause_map.erase(orig_c);
    }
  } else {
    clog<<"Ignoring deletion of syntactic unit or empty clause "; dump_clause(at_pos(p_item_start),clog);
    clog<<endl;
    data.resize(p_item_start);
  }
}

inline size_t ClauseDB::get_num_vars() {return max_var+1;}


inline ClauseDB::item_type ClauseDB::s_current_item() {
  if (*current == 0) return item_type::DELETION;
  else if (current < proof_start) return item_type::CLAUSE;
  else return item_type::LEMMA;
}

inline bool ClauseDB::s_at_end() {
  return (current == data.data()+data.size());
}

inline bool ClauseDB::s_at_begin() {
  return (current == data.data());
}

inline bool ClauseDB::s_at_proof_start() {
  return (current == proof_start);
}

inline bool ClauseDB::s_in_formula() {
  return current < proof_start;
}


inline cdb_t *ClauseDB::s_current_clause() {
  switch (s_current_item()) {
    case item_type::DELETION:
      return at_pos(current[1]);
    case item_type::CLAUSE: case item_type::LEMMA:
      return current;

  }
  return nullptr; // Dead code
}

inline cdb_t *ClauseDB::s_move_next(lit_t *hint) {
  switch (s_current_item()) {
    case item_type::DELETION: current+=3; return current;
    case item_type::CLAUSE: case item_type::LEMMA:
      if (hint) current=hint; else current+=2; // Use hint or jump over id and pivot to place on first literal of clause
      while (*current) ++current; // Goto terminating 0
      ++current;            // Jump over terminating 0
      ++current;            // Jump over offset
      return current;
  }
  return nullptr; // Dead code
}

inline cdb_t *ClauseDB::s_move_prev() {
  current--;            // Goto offset
  current += *current;  // Add offset to current position (Note: offsets are negative)
  return current;
}

ClauseDB DB; // Global clause DB







/***************************************************
  Certificate_Writer
***************************************************/

class Certificate_Writer {
  private:
    ostream &out;
    vector<cdb_t> buf;
    vector<cdb_t> rat_buf;
    vector<cdb_t> iu_buf;

    vector<cdb_t> *u_buf; // Buffer to put units to (buf or rat_buf)

    bool at_line_begin = true;

    void write_item();  // Write current item, and size tag
    void discard_item(); // Discard current item

    void write_nl();

    static const cdb_t SEP;

    Certificate_Writer(const Certificate_Writer&) = delete;
    Certificate_Writer &operator=(const Certificate_Writer&) = delete;

    void append_iu(); // Append iu_buf to buf (needs reversing)

    /*
      Output encoding: Each top-level entity is followed by its size, which can be used for reverse scanning of the file.

      proof file = (<unit-prop> <size> (<deletion> <size> | <lemma> <unit-prop> <size>)* <conflict_clause> <size>)?
        In backwards mode, the top-level items are in reverse order.


      unit-prop:
        id* 0                                 -- units

      lemma:
        id lit* 0 <proof>                     -- lemma id

      deletion:
        0 id                                  -- clause to delete


      proof = rup_proof | rat_proof

      rup_proof:
        id* 0 id                              -- units, conflict clause

      rat_proof:
        id* 0 0 lit (rat_justification)* 0    -- units, resolution literal

      rat_justification:
        id (id* 0 id | 0 0)                   -- candidate clause, (units, conflict clause | blocked-indication)

    */

  public:
    Certificate_Writer(ostream &_out);

    void begin_lemma(cdb_t *c); // id lit1 ... litn 0
    void put_deletion(cdb_t *c); // 0 id, <write>
    void put_main_conflict(cdb_t *c); // 0 0 id, <write>

    void put_induced_unit(cdb_t *c); // Remember induced unit for next lemma (backwards-mode)

    void put_initial_induced_units(); // <induced-units> 0, <write>


    void begin_rup_proof();       // <nothing>
    void put_unit(cdb_t *c);      // id
    void end_lemma_rup(cdb_t *c); // 0 id, <induced-units> 0, <write>

    void begin_rat_proof(lit_t l); // <Switch output to rat-buffer>, l
    void begin_rat_candidate(cdb_t *c); // id
    void end_rat_candidate_blocked();   // 0 0
    // Using put-unit to output units
    void end_rat_candidate(cdb_t *c); // id
    void end_rat_proof();             // 0, switch output to normal buffer
    // Using put-unit to output rup-units
    void end_lemma_rat();             // 0 0 <rat-buffer>, <induced-units> 0, <write>


};

const cdb_t Certificate_Writer::SEP = 0;


Certificate_Writer::Certificate_Writer(ostream &_out) : out(_out), buf(), rat_buf(),iu_buf(), u_buf(nullptr) {}

void Certificate_Writer::write_nl() {
  out<<endl;
  at_line_begin=true;
}

void Certificate_Writer::write_item() {
  for (auto x : buf) {
    if (!at_line_begin) out<<" ";
    at_line_begin=false;
    out<<x;
  }
  out<<" "<<buf.size();
  write_nl();
  buf.clear();
}

inline void Certificate_Writer::discard_item() {
  buf.clear();
  rat_buf.clear();
  u_buf=nullptr;
}

inline void Certificate_Writer::append_iu() {
  // Append induced units in reversed order
  buf.insert(buf.end(),iu_buf.rbegin(),iu_buf.rend());
}


void Certificate_Writer::begin_lemma(cdb_t *c) {
  buf.push_back(DB.get_clause_id(c));
  for (lit_t *l=DB.get_clause_lit1(c); *l; ++l) buf.push_back(*l);
  buf.push_back(SEP);
}

inline void Certificate_Writer::put_deletion(cdb_t *c) {
  buf.push_back(SEP);
  buf.push_back(DB.get_clause_id(c));
  write_item();
}

void Certificate_Writer::put_main_conflict(cdb_t *c) {
  buf.push_back(SEP);
  buf.push_back(SEP);
  buf.push_back(DB.get_clause_id(c));
  write_item();
}

inline void Certificate_Writer::put_induced_unit(cdb_t *c) {
  iu_buf.push_back(DB.get_clause_id(c));
}

void Certificate_Writer::put_initial_induced_units() {
  append_iu();
  buf.push_back(SEP);
  write_item();
  iu_buf.clear();
}


void Certificate_Writer::begin_rup_proof() {
  u_buf = &buf;
}

inline void Certificate_Writer::put_unit(cdb_t *c) {
  assert(u_buf);
  u_buf->push_back(DB.get_clause_id(c));
}

void Certificate_Writer::end_lemma_rup(cdb_t *c) {
  buf.push_back(SEP);
  buf.push_back(DB.get_clause_id(c));
  append_iu();
  buf.push_back(SEP);
  write_item();
  iu_buf.clear();
  u_buf=nullptr;
}


void Certificate_Writer::begin_rat_proof(lit_t l) {
  u_buf=&rat_buf;
  rat_buf.push_back(l);
}

void Certificate_Writer::begin_rat_candidate(cdb_t *c) {
  rat_buf.push_back(DB.get_clause_id(c));
}

void Certificate_Writer::end_rat_candidate_blocked() {
  rat_buf.push_back(SEP);
  rat_buf.push_back(SEP);
}

void Certificate_Writer::end_rat_candidate(cdb_t *c) {
  rat_buf.push_back(DB.get_clause_id(c));
}
void Certificate_Writer::end_rat_proof() {
  rat_buf.push_back(SEP);
  u_buf = &buf;
}

void Certificate_Writer::end_lemma_rat() {
  buf.push_back(SEP);
  buf.push_back(SEP);
  buf.insert(buf.end(),rat_buf.begin(),rat_buf.end());  // TODO: Could be optimized, copying units twice here
  append_iu();
  buf.push_back(SEP);
  write_item();
  iu_buf.clear();
  rat_buf.clear();
  u_buf=nullptr;
}




/***************************************************
  Watchlist
***************************************************/
// Represents watched literals for clauses
class Watched {
  public:
    Watched(size_t _num_vars);

    ~Watched();

    // Get list of clauses where literal is watched
    vector<cdb_t*>* get_watched_clauses(lit_t l);

    // Get first watched literal of clause
    lit_t get_w1(cdb_t* c);
    // Get second watched literal of clause
    lit_t get_w2(cdb_t* c);

    /* PRECONDITION TO SET WATCHES: Clause must have at least two literals! New literal ptr must point to literal of SAME clause! */
    // Sets initial watched literals. PRE: w1<w2, *w1!=*w2
    void set_initial_watched(cdb_t* c, lit_t *w1, lit_t *w2);
    /*
      Set second watched literal of clause and adds clause to watchlist.
      Does not remove the old watched literal from watchlist!

      PRE: w2 != DB.get_clause_lit1(c)
    */
    void set_new_w2(cdb_t* c, lit_t *w2);

    // Swap watched literals of clause
    void swap_watched(cdb_t* c);

    // Remove clause from watchlists. Note: The watched literals of clause MUST be preserved, as clause may be re-added on backwards pass.
    // Moreover, it must be correct to add any clause non-singleton clause where all literals are set, and later remove it before unsetting
    //   literals of the clause, even if watched literals have not been prepared, i.e., might be the same.
    void remove_watched(cdb_t* c);

    // Add clause, using watched literals from previous time this clause was in watchlist.
    // PRE: Clause must not be syntactic singleton.
    void readd_clause(cdb_t *c);

    // Iterate over all clauses in watchlists
    template<typename F> void foreach_clause(F f);


  private:
    vector<cdb_t*>* WM; // Middle-pointer of array with watch-lists for literals
    //vector<pair<Lit,Lit>> W; // Mapping from Clause Ids to watched literals
    size_t num_vars;

    // Deleted
    Watched(const Watched&) = delete;
    Watched &operator=(const Watched&) = delete;


};



Watched::Watched(size_t _num_vars) : WM(nullptr), num_vars(_num_vars) {
  WM = (new vector<cdb_t*> [2*num_vars+1]) + num_vars;
}

Watched::~Watched() {
  delete [] (WM - num_vars);
}

// Get list of clauses where literal is watched
inline vector<cdb_t*>* Watched::get_watched_clauses(lit_t l) {return WM + l;}

inline lit_t Watched::get_w1(cdb_t* c) {return DB.get_clause_lit1(c)[0];}
inline lit_t Watched::get_w2(cdb_t* c) {return DB.get_clause_lit1(c)[1];}

inline void Watched::set_initial_watched(cdb_t* c, lit_t *w1, lit_t *w2) {
  assert(*w1 != *w2 && w2 > w1);
  get_watched_clauses(*w1)->push_back(c);
  get_watched_clauses(*w2)->push_back(c);
  swap(DB.get_clause_lit1(c)[0], *w1);
  swap(DB.get_clause_lit1(c)[1], *w2);
}


inline void Watched::set_new_w2(cdb_t* c, lit_t *w2) {
  assert(w2 != DB.get_clause_lit1(c));     // TODO: Assertion probably in time-critical code-path ?
  get_watched_clauses(*w2)->push_back(c);
  swap(DB.get_clause_lit1(c)[1], *w2);
}

inline void Watched::swap_watched(cdb_t *c) {
  swap(DB.get_clause_lit1(c)[0], DB.get_clause_lit1(c)[1]);
}


void Watched::remove_watched(cdb_t* c) {
  lit_t w1=get_w1(c); lit_t w2=get_w2(c);

  {
    auto &wl1 = *get_watched_clauses(w1);
    for (size_t i=0;i<wl1.size();++i) {
      if (wl1[i] == c) {
        wl1[i] = wl1.back();
        wl1.pop_back();
        break;
      }
    }
  }

  {
    auto &wl2 = *get_watched_clauses(w2);
    for (size_t i=0;i<wl2.size();++i) {
      if (wl2[i] == c) {
        wl2[i] = wl2.back();
        wl2.pop_back();
        break;
      }
    }
  }

}

void Watched::readd_clause(cdb_t *c) {
  lit_t w1=get_w1(c); lit_t w2=get_w2(c);

  get_watched_clauses(w1)->push_back(c);
  get_watched_clauses(w2)->push_back(c);
}




// Iterate over all clauses
template<typename F> void Watched::foreach_clause(F f) {
  lit_t lbegin = -(num_vars - 1); lit_t lend = num_vars;
  for (lit_t l=lbegin;l<lend;++l) {
    for (cdb_t *c : WM[l]) {
      if (l == get_w1(c)) {
        f(c);
      }
    }
  }
}





/***************************************************
  Trail
***************************************************/
class Trail {
  public:
    Trail(size_t num_vars);

    /*
      PRE for set_false(...): Previously undecided.
    */
    /*
      Set first literal of specified clause to true, and set clause as reason.
    */
    void set_true(cdb_t *reason);
    /*
      Set literal to false, without reason
    */
    void set_false(lit_t l);

    bool is_false(lit_t l);                           // Return true if literal is false.
    bool is_true(lit_t l);                            // Return true if literal is true.

    /*
      Move literal of clause to front.
      PRE: Clause must not be watched!
    */
    void move_front(cdb_t* c, lit_t* l);


    typedef size_t pos_t;

    pos_t get_pos();      // Get current position

    lit_t fetch_pending();  // Get next pending literal, 0 if none
    pos_t get_pending();        // Get current pending position
    void set_pending(pos_t p);  // Reset pending position. Used to restore pending literals if core-first propagation did not find conflict.

    /*
      Conflict analysis marks clauses active that contribute to a conflict clause, or a blocked literal.
    */
    void analyze_main_conflict(cdb_t *c);                                   // Analyze conflict clause in main lemmas
    void analyze_rup_conflict(cdb_t *c, pos_t orig_pos);                    // Analyze conflict clause after RUP-proof
    void analyze_rat_conflict(cdb_t *c, pos_t rup_pos);                     // Analyze conflict clause after RAT candidate proof
    void analyze_rup_after_rat(pos_t orig_pos);                             // Analyze RUP-part of trail after RAT proof

    void rat_mark_blocked(lit_t l);                                         // Mark literal blocking a RAT candidate as relevant


    /* Unwind trail before effect of specified clause. Dump relevant units to cwr. */
    void unwind_including(cdb_t *c, Certificate_Writer *cwr);

    /* Unwind whole trail, dump relevat units to cwr. */
    void unwind_all(Certificate_Writer *cwr);

    void backtrack_ignore(pos_t pos);        // Backtrack to specified position, not dumping anything
    void backtrack_dump(pos_t pos, Certificate_Writer *cwr);  // Backtrack to position over analyzed trail, dumping relevant-old entries to cwr


    void dump(ostream &out);

  private:
    //void analyze_conflict_fixed_part(pos_t fixed_end);
    void analyze_conflict_prf_part(pos_t prf_begin, pos_t prf_end);



  private:
    Trail(const Trail &) = delete;
    Trail &operator=(const Trail &) = delete;


    enum class litval { UNDEC = 0, FALSE, MARKED, MARKED_OLD };

    vector<litval> A_vector;
    litval *A;

    vector<lit_t> TR;
    size_t pending = 0;

    vector<cdb_t*> reasons;


    void unset_false(lit_t l); // Reset false literal to undecided

    /*
      PRECONDITION: Only false literals may be marked/unmarked!

      Marking:
        A literal may be marked as either relevant or old. The idea is, that during a marking
        procedure, literals become marked as relevant first, and, after their dependencies being
        processed, they are marked as old.
        Upon backtracking over the trail and emitting the proof, the marking is finally removed.
        This two-level marking is required because the RUP-part of a trail is used multiple times
        on RAT-proofs, but once marked in the RUP-part, a literal needs not be processed again.
    */
    void mark_relevant(lit_t l);                      // Mark literal as relevant.
    bool is_relevant(lit_t l);                        // Return true if literal is relevant.

    void mark_old(lit_t l);
    bool is_old(lit_t l);

    void unmark(lit_t l);                             // Unmark literal. Remove relevant and old marks.


    cdb_t *get_reason(lit_t l);                       // Get reason for false literal


    void mark_confl_clause(cdb_t *c);                 // Mark all literals of c as relevant
    void mark_unit_clause(cdb_t *c);                  // Mark all but first literals of c as relevant. Assumes that reason of first literal is clause itself!
    void mark_unit_clause_ignoring_old(cdb_t *c);     // Mark all but first literals of c as relevant. Assumes that reason of first literal is clause itself!

};


Trail::Trail(size_t num_vars) : A_vector(2*num_vars + 1), A( A_vector.data() + num_vars), TR(), reasons(num_vars) {}


inline void Trail::set_false(lit_t l) {
  assert(l && !is_false(l) && !is_true(l));
  A[l] = litval::FALSE;
  TR.push_back(l);
  reasons[abs(l)] = nullptr;
}

inline void Trail::set_true(cdb_t *reason) {
  lit_t l = -(*DB.get_clause_lit1(reason));
  assert(l && !is_false(l) && !is_true(l));

  A[l] = litval::FALSE;
  TR.push_back(l);
  reasons[abs(l)] = reason;
}
inline bool Trail::is_false(lit_t l) { return (A[l] != litval::UNDEC); }
inline bool Trail::is_true(lit_t l) { return (A[-l] != litval::UNDEC); }

inline void Trail::unset_false(lit_t l) { A[l] = litval::UNDEC; }


inline void Trail::move_front(cdb_t* c, lit_t* l) { swap( *DB.get_clause_lit1(c), *l); }

inline cdb_t *Trail::get_reason(lit_t l) { return reasons[abs(l)]; }

inline Trail::pos_t Trail::get_pos() { return TR.size(); }


inline lit_t Trail::fetch_pending() {
  if (pending<TR.size()) return TR[pending++]; else return 0;
}

inline Trail::pos_t Trail::get_pending() {return pending;}
inline void Trail::set_pending(pos_t p) { assert(p <= TR.size()); pending = p; }


inline bool Trail::is_relevant(lit_t l) {return A[l] == litval::MARKED; }
inline bool Trail::is_old(lit_t l) { return A[l] == litval::MARKED_OLD; }

inline void Trail::mark_relevant(lit_t l) { assert(is_false(l) && !is_old(l)); A[l] = litval::MARKED; }
inline void Trail::mark_old(lit_t l) { assert(is_false(l)); A[l] = litval::MARKED_OLD; }

inline void Trail::unmark(lit_t l) {assert(is_false(l)); A[l] = litval::FALSE; }

inline void Trail::mark_confl_clause(cdb_t *c) {
  for (lit_t *l=DB.get_clause_lit1(c); *l; ++l) mark_relevant(*l);
}

inline void Trail::mark_unit_clause(cdb_t *c) {
  assert( get_reason(*DB.get_clause_lit1(c)) == c );
  for (lit_t *l=DB.get_clause_lit1(c)+1; *l; ++l) mark_relevant(*l);
}

inline void Trail::mark_unit_clause_ignoring_old(cdb_t *c) {
  assert( get_reason(*DB.get_clause_lit1(c)) == c );
  for (lit_t *l=DB.get_clause_lit1(c)+1; *l; ++l) if (!is_old(*l)) mark_relevant(*l);
}


///*
//  Mark clauses involved in conflict on fixed initial part of trail.
//  This marking procedure stops on already active clauses, and
//  erases all relevance marks the fixed part of the trail.
//*/
//void Trail::analyze_conflict_fixed_part(pos_t fixed_end) {
//  pos_t i = fixed_end;
//
//  while (i>0) {
//    --i;
//    lit_t l = TR[i];
//
//    if (is_relevant(l)) {
//      cdb_t *reason = get_reason(l);
//      if (reason && !DB.is_core(reason)) {
//        mark_unit_clause(reason);
//        DB.mark_core(reason);
//      }
//
//      unmark(l);
//    }
//  }
//}


/*
  Mark clauses involved in conflict on proof-part of trail.
  This marking procedure only considers fresh marks, and converts
  them to old marks.

  This procedure is used to analyze conflicts and blocked literals after both, RUP and RAT proofs.
  After a RAT candidate proof, it is only ran on the RAT-part of the trail,
  after a RUP-proof, and after finishing all RAT candidates, it is run on the RUP-part.
*/
void Trail::analyze_conflict_prf_part(pos_t prf_begin, pos_t prf_end) {
  pos_t i = prf_end;
  while (i > prf_begin) {
    --i;
    lit_t l = TR[i];

    if (is_relevant(l)) {
      cdb_t *reason = get_reason(l);
      if (reason) {
        mark_unit_clause_ignoring_old(reason);
        DB.mark_core(reason);
      }

      mark_old(l);
    }
  }
}




void Trail::rat_mark_blocked(lit_t l) {
  l=-l;
  assert(is_false(l));
  if (!is_old(l)) mark_relevant(l);
}


void Trail::analyze_main_conflict(cdb_t *c) {
  mark_confl_clause(c);
  DB.mark_core(c);

//  analyze_conflict_fixed_part(TR.size());
}

void Trail::analyze_rup_conflict(cdb_t *c, pos_t orig_pos) {
  mark_confl_clause(c);
  analyze_conflict_prf_part(orig_pos,TR.size());
//  analyze_conflict_fixed_part(orig_pos);
}


void Trail::analyze_rat_conflict(cdb_t *c, pos_t rup_pos) {
  mark_confl_clause(c);
  analyze_conflict_prf_part(rup_pos,TR.size());
}

void Trail::analyze_rup_after_rat(pos_t orig_pos) {
  analyze_conflict_prf_part(orig_pos,TR.size());
//  analyze_conflict_fixed_part(orig_pos);
}



void Trail::unwind_including(cdb_t *c, Certificate_Writer *cwr) {
  /*
    Note: As drat-trim does, we detect wether a clause is a reason on the trail, by assuming that
      the corresponding literal is the first watched literal, including unit-clauses!

  */

  lit_t l = -(*DB.get_clause_lit1(c));
  if (is_false(l) && get_reason(l)==c) { // Clause is on trail
    lit_t tbl;
    do {
      tbl = TR.back(); TR.pop_back();

      if (is_relevant(tbl) && get_reason(tbl)) {
        DB.mark_core(get_reason(tbl));
        mark_unit_clause(get_reason(tbl)); // Propagate core marking
        if (cwr) cwr->put_induced_unit(get_reason(tbl)); // Dump unit as induced unit
      }

      unset_false(tbl);
    } while (l != tbl);
  }

  pending = TR.size();
}

void Trail::unwind_all(Certificate_Writer *cwr) {
  while (TR.size()) {
    lit_t tbl = TR.back(); TR.pop_back();

    if (is_relevant(tbl) && get_reason(tbl)) {
      DB.mark_core(get_reason(tbl));
      mark_unit_clause(get_reason(tbl)); // Propagate core marking
      if (cwr) cwr->put_induced_unit(get_reason(tbl)); // Dump unit as induced unit
    }

    unset_false(tbl);
  }
}


void Trail::backtrack_ignore(pos_t pos) {
  while (TR.size()!=pos) {
    unset_false(TR.back());
    TR.pop_back();
  }
  pending = TR.size();
}

void Trail::backtrack_dump(pos_t pos, Certificate_Writer *cwr) {
  for (size_t i = pos; i<TR.size();++i) {
    assert(!is_relevant(TR[i]));  // Analysis shpuld have converted relevant -> old
    if (is_old(TR[i]) && get_reason(TR[i])) if (cwr) cwr->put_unit(get_reason(TR[i]));
    unset_false(TR[i]);
  }

  TR.resize(pos);
  pending = TR.size();
}


void Trail::dump(ostream &out) {
  for (auto i = TR.begin();i!=TR.end();++i) {
    if (TR.data() + pending == &*i) out<<"| ";
    lit_t l=*i;
    out<<l;
    if (is_relevant(l)) out<<"r";
    if (is_old(l)) out<<"o";
    if (get_reason(l)) out<<"("<<DB.get_clause_id(get_reason(l))<<")"; else out<<"***"<<endl;
    out<<" ";
  }
  out<<endl;
}




/***************************************************
  State
***************************************************/
class State {
  public:
    State (size_t num_vars, ostream &out);

    /*
      Do forward pass over clauses.
    */
    void do_pass1();

    /*
      Do backwards pass
    */
    void do_pass2();


    void dbg_assert_all_units();

  private:

    /*
      Add clause.
      Return hint and true iff clause is conflict clause.

      gint can be used to accelerate DB.s_move_next.
    */
    pair<lit_t*,bool> add_clause(cdb_t *c);


    /*
      Unit propagation. Return conflict clause if one was reached
    */
    template<bool> cdb_t* propagate_units_aux();
    cdb_t* propagate_units_nocf();  // No core-first
    cdb_t* propagate_units_cf();    // With core-first optimization


    void verify(cdb_t *c);


  private:
    Watched W;
    Trail TR;

    cdb_t *cclause=nullptr; // Conflict clause at end of first phase

    Certificate_Writer cwr;

    State(const State &) = delete;
    State &operator=(const State &) = delete;


  private:
    size_t stat_total_lemmas = 0;
    size_t stat_core_lemmas = 0;
    size_t stat_core_first_conflicts = 0;
    size_t stat_snd_round_conflicts = 0;

  public:
    void print_stats(ostream &out);

};


State::State(size_t num_vars, ostream &cert_out) : W(num_vars), TR(num_vars), cwr(cert_out) {}


inline pair<lit_t*,bool> State::add_clause(cdb_t *c) {
  // Analyze clause
  lit_t *w1 = nullptr, *w2 = nullptr;

  lit_t *l;
  for (l = DB.get_clause_lit1(c); *l; ++l) {
    if (TR.is_true(*l)) return {l, false}; // Ignoring tautology.
    if (!TR.is_false(*l)) {
      if (!w1) w1=l; else if (!w2 && *l!=*w1) w2=l;
    }
  }

  if (!w1) { // Conflict
    return {l, true};
  } else if (!w2) { // Unit, *w1 is unit literal
    TR.move_front(c,w1); // Warning, *w1 no longer unit literal!
    TR.set_true(c);
    return {l, false};
  } else { // >1 undec
    W.set_initial_watched(c,w1,w2);
    return {l, false};
  }
}

template<bool only_core> inline cdb_t* State::propagate_units_aux() {
  lit_t l;

  Trail::pos_t stored_pending = TR.get_pending();

  while ((l=TR.fetch_pending())) {                     // As long as there are unprocessed literals
    vector<cdb_t*>* l_watched = W.get_watched_clauses(l);    // Get list of clauses watching this literal
    for (size_t i = 0; i<l_watched->size();) {  // Process clauses
      cdb_t *c = (*l_watched)[i];
      if (only_core && !DB.is_core(c)) {++i; continue;}   // In core mode, ignore non-core clauses

      lit_t w1 = W.get_w1(c);                         // Get watched literals
      lit_t w2 = W.get_w2(c);

      if (TR.is_true(w1) || TR.is_true(w2)) // If one literal is true, proceed with next Clause
        {++i; continue;}

      /*
        Note: Subtle dependency:
          On unwinding the trail, we assume that the reason is the first literal of the clause, negated.
          Thus, we implicitly rely on the fact here that w1 is the first literal of the clause!
      */
      if (w1==l) {w1=w2; w2=l; W.swap_watched(c);}       // Normalize on w2 being set literal

      // Now scan through Clause and find new watched literal
      lit_t *w=nullptr;
      for (lit_t *l = DB.get_clause_lit1(c) + 2; *l; ++l ) {
        if (*l != w1 && !TR.is_false(*l)) {
          // Found watchable literal
          w=l;
          break;
        }
      }

      if (w) {                                      // Found new watched literal
        W.set_new_w2(c,w);

        (*l_watched)[i] = l_watched->back();        // Remove this Clause from watchlist
        l_watched->pop_back();
        // Note: We must not increment i, as it points to next clause now

      } else if (!TR.is_false(w1)) {                // Found unit
        TR.set_true(c);                             // Assign to true (Note: unit is first literal in clause!)
        ++i;                                        // Proceed with next Clause
      } else {                                      // Found conflict
        return c;                                   // Return with conflict clause
      }
    }
  }

  if (only_core) TR.set_pending(stored_pending); // After core-first round without conflict, pending literals have not been completely processed, so they are still pending.

  return nullptr;    // No conflict found
}


cdb_t* State::propagate_units_nocf() {
  return propagate_units_aux<false>();
}

cdb_t* State::propagate_units_cf() {
  cdb_t *cc = propagate_units_aux<true>();
  if (!cc) cc=propagate_units_aux<false>(); else ++stat_core_first_conflicts;
  if (cc) ++stat_snd_round_conflicts;
  return cc;
}



void State::verify(cdb_t *c) {
  Trail::pos_t orig_pos = TR.get_pos();

  bool pivot_false = TR.is_false(DB.pivot(c));

  // Falsify literals
  for (lit_t *l=DB.get_clause_lit1(c);*l;++l) {
    //assert(!TR.is_true(*l)); // Note: Tautologies cannot become active, so they should never be verified in backwards pass.
    if (TR.is_true(*l)) {
      // Tautology, verified, no dumping to certificate
      TR.backtrack_ignore(orig_pos);
      return;
    }

    if (!TR.is_false(*l)) TR.set_false(*l);
  }

  cwr.begin_lemma(c);

  // Do unit propagation (core-first)
  cdb_t* cc = propagate_units_cf();

  if (cc) {
    // RUP-check succeeded
    TR.analyze_rup_conflict(cc,orig_pos); // TODO: For proof output, we will have to remember/output relevant units!
    cwr.begin_rup_proof();
    TR.backtrack_dump(orig_pos,&cwr);
    cwr.end_lemma_rup(cc);
  } else {
    //dbg_assert_all_units();

    // RUP-check failed. Do RAT-check
    if (pivot_false) { clog<<"RUP check failed, cannot do RAT b/c pivot_false, for clause: "; DB.dump_clause(c,clog); clog<<endl; fail();}


    lit_t pivot = DB.pivot(c);

    cwr.begin_rat_proof(pivot);

    // Collect resolution candidates
    size_t rup_pos = TR.get_pos();

    // Collect clauses containing -pivot
    vector<cdb_t*> rat_candidates;

    W.foreach_clause([&rat_candidates, pivot](cdb_t *c) {
      for (lit_t *l=DB.get_clause_lit1(c);*l;++l) {
        if (*l == -pivot) {
          rat_candidates.push_back(c);
          return;
        }
      }
    });

    // TODO: How many candidates remain here, compared to the blocked ones?
    // Sort candidates by id
    std::sort(rat_candidates.begin(),rat_candidates.end(),[](cdb_t* c1, cdb_t* c2) {return DB.get_clause_id(c1) < DB.get_clause_id(c2);});


    // Perform rat-checks
    for (cdb_t *ratc : rat_candidates) {
      cwr.begin_rat_candidate(ratc);
      for (lit_t *l=DB.get_clause_lit1(ratc);*l;++l) {
        if (*l == -pivot) continue;
        if (TR.is_true(*l)) { // Blocked
          TR.backtrack_ignore(rup_pos);

          // Flag literals that caused l to be true
          TR.rat_mark_blocked(*l);

          cwr.end_rat_candidate_blocked();

          goto next_candidate;
        }

        if (!TR.is_false(*l)) TR.set_false(*l);
      }

      {
        cdb_t *cc = propagate_units_cf(); // Core-first unit propagation

        if (cc) {
          TR.analyze_rat_conflict(cc,rup_pos);
          TR.backtrack_dump(rup_pos,&cwr);
          cwr.end_rat_candidate(cc);
        } else {
          clog<<"RAT-check failed"<<endl;
          clog<<"Lemma: "; DB.dump_clause(c,clog); clog<<endl;
          clog<<"Candidate: "; DB.dump_clause(ratc,clog); clog<<endl;
          clog<<"Trail dump: "; TR.dump(clog);
          fail();
        }
      }

      next_candidate:;
    }

    // RAT-proof succeeded, analyze RUP-part of trail
    TR.analyze_rup_after_rat(orig_pos);

    cwr.end_rat_proof();
    TR.backtrack_dump(orig_pos,&cwr);
    cwr.end_lemma_rat();
  }
}


void State::dbg_assert_all_units() {
  W.foreach_clause([this](cdb_t *c) {
    // Analyze clause
    lit_t *w1 = nullptr, *w2 = nullptr;

    for (lit_t *l=DB.get_clause_lit1(c); *l; ++l) {
      if (TR.is_true(*l)) {
        assert(!TR.is_false(*l));
        return;
      } else if (!TR.is_false(*l)) {
        if (!w1) w1=l;
        else if (!w2 && *w1!=*l) w2=l;
      }
    }


    if (!w1) {
      clog<<"DBG: Undetected conflict clause "; DB.dump_clause(c,clog); clog<<endl;
      fail();
    } else if (!w2) {
      clog<<"DBG: Undetected unit clause, unit_lit = "<< *w1 <<" "; DB.dump_clause(c,clog); clog<<endl;
      fail();
    } else {
      // Check if watched properly set
      if (w1 != DB.get_clause_lit1(c) || w2 != DB.get_clause_lit1(c) + 1) {
        clog<<"DBG: Watched literals error: "; DB.dump_clause(c,clog); clog<<endl;
        clog<<"ofs(w1) = " << w1 - DB.get_clause_lit1(c) << " ofs(w2) = "<< w2 - DB.get_clause_lit1(c) << endl;
        TR.dump(clog);
        fail();
      }

    }
  });
}



// Sets cclause to found conflict clause
void State::do_pass1() {
  while (!DB.s_at_proof_start()) {
    assert(DB.s_current_item() == ClauseDB::item_type::CLAUSE);

    auto r = add_clause(DB.s_current_clause());
    if (r.second) {
      cclause = DB.s_current_clause();
      // Note: No trail yet to be analyzed
      return; // Trivial conflict in clauses
    }

    DB.s_move_next(r.first);
  }

  cclause = propagate_units_nocf();
  if (cclause) {
    clog<<"Found conflict in formula after unit propagation"<<endl;
    return;
  }

  while (!DB.s_at_end()) {
    switch (DB.s_current_item()) {
      case ClauseDB::item_type::CLAUSE: assert(false);
      case ClauseDB::item_type::LEMMA: {
        // verify(DB.s_current_clause());

        auto r = add_clause(DB.s_current_clause());
        if (r.second) {
          cclause = DB.s_current_clause();
          TR.analyze_main_conflict(cclause); // Mark core
          return;
        }

        cclause = propagate_units_nocf();
        if (cclause) {
          TR.analyze_main_conflict(cclause); // Mark core
          return;
        }
        //dbg_assert_all_units();

        DB.s_move_next(r.first);
      }
      break;
      case ClauseDB::item_type::DELETION:
        W.remove_watched(DB.s_current_clause());
        DB.s_move_next();
        break;


    }
  }

  clog<<"Reached end of proof, but no conflict"<<endl;
  fail();
  return;
}


void State::do_pass2() {
  if (DB.s_in_formula()) return; // Not reached proof in forward pass.

  assert(cclause); // We assume that we have reached a conflict
  cwr.put_main_conflict(cclause);

  DB.s_move_next();  // Move to next clause, such that current is one past last used clause

  while (!DB.s_at_proof_start()) {
    DB.s_move_prev();
    assert(!DB.s_in_formula());

    switch (DB.s_current_item()) {
      case ClauseDB::item_type::DELETION:
        // Re-add clause to watchlist.
        W.readd_clause(DB.s_current_clause());
        /*
          Note: Here are some subtle points:
            * Deletions of syntactic unit clauses have been filtered out. So we can assume every clause has at least two (different) literals here.
            * If this clause has been unit on addition, the watched literals have not been properly set. However, in this case, any literals of the clause
              are safe as watched literals, as they will be only unset when/after the clause is removed anyway.
              However, we may still run into the case that both watched literals are the same. This case must be correctly handled by readd and remove functions of watchlist.
        */
      break;

      case ClauseDB::item_type::CLAUSE: assert(false);
      case ClauseDB::item_type::LEMMA: {
        cdb_t *c = DB.s_current_clause();
        // Remove lemma from watchlist
        W.remove_watched(c);

        // Unwind unit propagations
        TR.unwind_including(c,&cwr);

        ++stat_total_lemmas;
        // Only verify if core clause
        if (DB.is_core(c)) {
          ++stat_core_lemmas;
          verify(c);
        }
      }
      break;

    }
  }

  // Unwind remaining unit propagations on trail, and dump them as initial unit propagations
  TR.unwind_all(&cwr);
  cwr.put_initial_induced_units();
}


void State::print_stats(ostream &out) {
  out<<"total_lemmas = "<<stat_total_lemmas<<endl;
  out<<"core_lemmas = "<<stat_core_lemmas<<endl;
  out<<"core_first_conflicts = "<<stat_core_first_conflicts<<endl;
  out<<"stat_snd_round_conflicts = "<<stat_snd_round_conflicts<<endl;
}



/***************************************************
  Parser
***************************************************/


inline void parse_ignore_comments(istream &in) {
  in>>ws;
  while (!in.eof()) {
    if (in.peek()!='c') break;
    in.ignore(numeric_limits<streamsize>::max(), '\n');
    in>>ws;
  }
}

inline lit_t parse_lit(istream &in) {
  in>>ws;
  lit_t r; in>>r;
  return r;
}

void parse_dimacs(istream &in) {
  in.exceptions(in.failbit|in.badbit);

  parse_ignore_comments(in);
  if (in.peek()=='p') in.ignore(numeric_limits<streamsize>::max(), '\n');

  while (!in.eof()) {
    parse_ignore_comments(in);
    if (in.eof()) break;

    // Parse a Clause
    DB.p_begin_clause();
    while (true) {
      lit_t l = parse_lit(in);
      if (!l) break;
      DB.p_add_lit(l);
    }
    DB.p_finish_clause();
  }
}


void parse_proof(istream &in) {
  in.exceptions(in.failbit|in.badbit);

  parse_ignore_comments(in);
  if (in.peek()=='o') in.ignore(numeric_limits<streamsize>::max(), '\n');
  parse_ignore_comments(in);

  DB.p_begin_proof();

  while (!in.eof()) {
    parse_ignore_comments(in);
    if (in.eof()) break;

    if (in.peek()=='d') {
      in.get();

      DB.p_begin_deletion();
      for (lit_t l=parse_lit(in);l;l=parse_lit(in)) DB.p_del_lit(l);
      DB.p_finish_deletion();
    } else {
      DB.p_begin_clause();
      for (lit_t l=parse_lit(in);l;l=parse_lit(in)) DB.p_add_lit(l);
      DB.p_finish_clause();
    }
  }
}


void print_usage() {
  cerr<<"Usage drat-ri <dimacs-file> <proof-file>"<<endl;
}

void print_info() {
  cerr<<"sizeof(cdb_t) = "<<sizeof(cdb_t)<<endl;
  cerr<<"sizeof(cdb_t*) = "<<sizeof( cdb_t* )<<endl;
}




int main(int argc, char **argv)
{
  print_info();

  if (argc!=3) {print_usage(); return 2;}

  // Parsing
  {
    clog<<"Parsing cnf"<<endl;
    ifstream cnf;
    cnf.open(argv[1],ifstream::in);
    parse_dimacs(cnf);
    cnf.close();

    clog<<"Parsing proof"<<endl;
    ifstream prf;
    prf.open(argv[2],ifstream::in);
    parse_proof(prf);
    prf.close();
    clog<<"Done"<<endl;

    DB.p_finish_proof();
  }

  State ST(DB.get_num_vars(), cout);


  clog<<"Forward pass"<<endl;
  ST.do_pass1();
  clog<<"Done"<<endl;

  clog<<"Backward pass"<<endl;
  ST.do_pass2();
  clog<<"Done"<<endl;

  ST.print_stats(clog);


  cout.flush();

}

