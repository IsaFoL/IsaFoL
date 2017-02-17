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
typedef cdb_t Lit;
typedef cdb_t Cid;


#define STATS
#ifdef STATS
  size_t stat_found_new_watched = 0;
  size_t stat_watch_search_steps = 0;
  size_t stat_unit_clauses = 0;
  size_t stat_relevant_unit_clauses = 0;

  size_t stat_conflicts_out_core = 0;
  size_t stat_conflicts_in_core = 0;

  void print_stats(ostream &out) {
    out<<"found_new_watched = "<<stat_found_new_watched<<endl;
    out<<"watch_search_steps = "<<stat_watch_search_steps<<endl;
    out<<"unit_clauses = "<<stat_unit_clauses<<endl;
    out<<"relevant_unit_clauses = "<<stat_relevant_unit_clauses<<endl;
    out<<"conflicts_out_core = "<<stat_conflicts_out_core<<endl;
    out<<"conflicts_in_core = "<<stat_conflicts_in_core<<endl;
  }


  #define INCR_STAT(var) (++var)
  #define PRINT_STATS(out) print_stats(out)
#else
  #define INCR_STAT(var)
  #define PRINT_STATS(out)
#endif



class Clause;

class Parsing;


class Clausedb {
  private:
    vector<cdb_t> clausedb; // Flat Clause database
    size_t next_id = 1;     // Next Clause id
    size_t max_var = 0;     // Maximum variable value
    size_t proof_start=0;   // Start index of proof in db

    friend Parsing;         // FIXME!

  public:
    Clausedb();

    size_t get_num_vars();
    size_t get_num_cids();

    Clause* clause_at(size_t cpos);
    Clause* first_clause();
    Clause* first_proof_clause();
    Clause* end_clause();

};

Clausedb::Clausedb() : clausedb() {}

inline size_t Clausedb::get_num_vars() {return max_var;}
inline size_t Clausedb::get_num_cids() {return next_id;}

inline Clause* Clausedb::clause_at(size_t cpos) {return (Clause*)(clausedb.data() + cpos); }
inline Clause* Clausedb::first_clause() {return clausedb.empty()?nullptr:(Clause*)(clausedb.data()+1);}
inline Clause* Clausedb::first_proof_clause() {return clausedb.empty()?nullptr:(Clause*)(clausedb.data() + proof_start);}
inline Clause* Clausedb::end_clause() { return clausedb.empty()?nullptr:(Clause*)(clausedb.data() + clausedb.size()); }




// Represent a Clause
class Clause {
  private:
    // Deleted
    Clause();
    Clause(const Clause&);
    Clause &operator=(const Clause&);

    inline cdb_t* data();

  public:


    Cid id();

    Lit* first();

    Lit reslit();

    bool is_del();
    size_t del_pos();

    void write(Clausedb &cdb, ostream &out, bool no_id=false);

    static Clause* next(Lit *l);

    Clause* next();


    void mark();
    bool marked();


    void mark_skipped();
    bool is_marked_skipped();

    /*inline static Clause* prev(Clause *c) {
      int *l=(cdb_t*)c;

      l = l - 2; // Skip over terminating zero of last clause

      while (*l) l--; // Skip until terminating zero before previous clause
      l++;  // Go back to start of previous clause

      return (Clause*)l;
    }*/


};


inline cdb_t* Clause::data() { return reinterpret_cast<cdb_t*>(this); }


inline Cid Clause::id() {return data()[0]>>1;}

inline Lit* Clause::first() {return data()+2;}

inline Lit Clause::reslit() {return data()[1];}

inline bool Clause::is_del() {return id()==-1;}
inline size_t Clause::del_pos() { return data()[1]; }

void Clause::write(Clausedb &cdb, ostream &out, bool no_id) {
  if (is_del()) {
    out<<"d "<<cdb.clause_at(del_pos())->id()<<endl;
  } else {
    if (!no_id) out<<id()<<" ";
    for (Lit* l=first();*l;++l)
      out<<*l<<" ";
    out<<"0"<<endl;
  }
}

inline Clause* Clause::next(Lit *l) {
  for (;*l;++l);
  ++l;
  return reinterpret_cast<Clause*>(l);
}

inline Clause* Clause::next() {
  if (is_del()) {
    return reinterpret_cast<Clause*>(data()+2);
  } else {
    return next(first());
  }
}


inline void Clause::mark() {data()[0]|=1;}
inline bool Clause::marked() {return data()[0] & 1;}


inline void Clause::mark_skipped() {
  data()[0] &= 1; // Set id to 0, preserve mark flag
}

inline bool Clause::is_marked_skipped() {
  return (data()[0]>>1) == 0;
}








class FVC_Out {
  private:
    ostream &out;
    vector<cdb_t> buf;
    vector<cdb_t> rat_buf;

    bool at_line_begin;


    void write_out(vector<cdb_t> &buf);

    void write_nl();

    static const cdb_t SEP;


    /*
      Output encoding:

      proof file = (<unit-prop> (<deletion> | <lemma> <unit-prop>)* <conflict_clause>)?

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
        id id* 0 id                           -- candidate clause, units, conflict clause

    */

  public:
    FVC_Out(ostream &_out);


    void unit_id(Cid id);

    void cmd_lemma_start(Cid id);

    void lemma_lit(Lit l);
    void lemma_start_rup();
    void lemma_end_rup(Cid id);

    void lemma_start_rat(Lit l);

    void lemma_rat_start_justification(Cid id);
    void lemma_rat_end_justification(Cid id);

    void lemma_rat_justify_blocked(Cid id);



    void lemma_rat_start_units();
    void lemma_rat_end_units();

    void lemma_end_rat();

    void lemma_end();

    void cmd_del(Cid id);

    void cmd_unit_prop_start();
    void cmd_unit_prop_end();

    void cmd_conflict_clause(Cid id);

    // Discard current lemma. E.g. issued when it is detected as TAUT while emitting literals.
    void lemma_discard();

};


const cdb_t FVC_Out::SEP = 0;

inline void FVC_Out::write_out(vector<cdb_t> &buf) {
  for (auto x : buf) {
    if (!at_line_begin) out<<" ";
    at_line_begin=false;
    out<<x;
  }
}

inline void FVC_Out::write_nl() {
  out<<endl;
  at_line_begin=true;
}


FVC_Out::FVC_Out(ostream &_out) : out(_out), buf(), rat_buf(), at_line_begin(true) {}


inline void FVC_Out::unit_id(Cid id) {
  buf.push_back(id);
}

inline void FVC_Out::cmd_lemma_start(Cid id) {
  buf.push_back(id);
}

inline void FVC_Out::lemma_lit(Lit l) {buf.push_back(l);}
inline void FVC_Out::lemma_start_rup() {buf.push_back(SEP);}
void FVC_Out::lemma_end_rup(Cid id) {buf.push_back(SEP); buf.push_back(id); }

void FVC_Out::lemma_start_rat(Lit l) {rat_buf.push_back(SEP); rat_buf.push_back(l); }

inline void FVC_Out::lemma_rat_start_justification(Cid id) {rat_buf.push_back(id); }

inline void FVC_Out::lemma_rat_end_justification(Cid id) {rat_buf.push_back(SEP); rat_buf.push_back(id);}

inline void FVC_Out::lemma_rat_justify_blocked(Cid id) { rat_buf.push_back(id); rat_buf.push_back(SEP); rat_buf.push_back(SEP); }

inline void FVC_Out::lemma_rat_start_units() {buf.push_back(SEP);}
inline void FVC_Out::lemma_rat_end_units() {buf.push_back(SEP);}

void FVC_Out::lemma_end_rat() {
  buf.insert(buf.end(),rat_buf.begin(),rat_buf.end());
  buf.push_back(SEP);
  rat_buf.clear();
}


void FVC_Out::cmd_del(Cid id) {
  buf.push_back(SEP); buf.push_back(id);
  write_out(buf); write_nl();
  buf.clear();
}

void FVC_Out::cmd_unit_prop_start() { }
void FVC_Out::cmd_unit_prop_end() {
  buf.push_back(SEP);
  write_out(buf); write_nl();
  buf.clear();
}

void FVC_Out::cmd_conflict_clause(Cid id) {
  buf.push_back(SEP); buf.push_back(SEP);buf.push_back(id);
  write_out(buf); write_nl();
  buf.clear();
}

void FVC_Out::lemma_end() {
  write_out(buf); write_nl();
  buf.clear();
}

// Discard current lemma. E.g. issued when it is detected as TAUT while emitting literals.
void FVC_Out::lemma_discard() { buf.clear(); rat_buf.clear(); }






/*
class FVC_Writer {
  private:
    ostream &out;

  public:
    inline FVC_Writer(ostream &_out) : out(_out) {}

    inline void write_literals(Clause *c) {
      for (Lit *l=c->first();*l;++l) out<<*l<<" ";
      out<<"0";
    }

    inline void write_comment(char *msg) {
      out<<"c "<<msg<<endl;
    }

    inline void write_unit_U() {out<<"U ";}
    inline void write_unit_clause(Clause *c) {out<<c->id()<<" ";}
    inline void writeln_unit_C(Clause *c) {out<<"C "<<c->id()<<endl;}
    inline void writeln_unit_0() {out<<"0"<<endl;}

    inline void writeln_rat_reslit(Lit l) {out<<"R "<<l<<endl;}
    inline void write_rat_clause(Clause *c) {out<<"r "<<c->id()<<" ";}

    // id l1 ... ln 0
    inline void writeln_add_clause(Clause *c) {
      out<<c->id()<<" "; write_literals(c); out<<endl;
    }

    // d id  // TODO: d id1 ... idn 0, i.e., summarize adjacent deletes!
    inline void writeln_del_clause(Clause *c) {
      out<<"d "<<c->id()<<endl;
    }




};
*/




//// WARNING: pointer-tagging, not portable!
//// TODO: Wrap in tagged-ptr class!
//inline Clause* unflag(Clause *c) {
//  return reinterpret_cast<Clause*>(reinterpret_cast<uintptr_t>(c)&~static_cast<uintptr_t>(1));
//}
//
//inline Clause* flag(Clause *c) {
//  return reinterpret_cast<Clause*>(reinterpret_cast<uintptr_t>(c)|static_cast<uintptr_t>(1));
//}
//
//inline bool flagged(Clause *c) {
//  return (reinterpret_cast<uintptr_t>(c)&static_cast<uintptr_t>(1));
//}


// Represent trail and assignment
class Trail {

//  inline void set_false_raw(Lit l, Clause *c) {A[num_vars+l] = true; reason[num_vars+l] = c;}

public:
  Trail(size_t _num_vars);

  bool is_false(Lit l);
  bool is_true(Lit l);
  void unset(Lit l);

  Clause* get_reason(Lit l);

  bool is_flagged(Lit l);

  // Set flag of literal. pre: is_false(l)
  void set_flag(Lit l);

  size_t current_pos();

  void set_false(Lit l, Clause *c);

  // Reset pending literals to state at position. Required for second pass after core-first unit propagation.
  void reset_pending(size_t pos);

  Lit fetch_pending();

  // Backtrack over assumed literals, before unit propagation started
  void backtrack(size_t pos);

  void dump(size_t pos, ostream &out);



  // Backtrack over trail, mark and emit relevant clauses
  void backtrack_and_mark(size_t pos, FVC_Out &out);

  // Emit all unit clauses from specified position onwards
  void emit_units(size_t pos, FVC_Out &out);


  // Flag clauses on trail which are relevant for conflict due to clause c
  void analyze_conflict(size_t pos, Clause *c);

  // Flag clauses which are relevant for literal l becoming false
  void analyze_conflict(size_t pos, Lit l);


private:
  void analyze_conflict_aux(size_t pos);


private:
  enum class Lit_Value {
    NOT_FALSE,
    FALSE,
    FALSE_FLAGGED
  };

  size_t num_vars;
  vector<Lit_Value> A;      // Assignment for literals
  vector<Clause*> reason;   // Maps literals to unit-clause that falsified literal, or nullptr

  vector<Lit> TR;           // Trail, containing dummy value on position 0 to have 0-index invalid (see A)
  size_t processed;         // Position in trail where first pending literal starts


};




Trail::Trail(size_t _num_vars) : num_vars(_num_vars), A(2*_num_vars+1,Lit_Value::NOT_FALSE), reason(2*_num_vars+1,nullptr), TR(), processed(1) {
  TR.push_back(0); // Guard to prevent trail indexes being zero.
  processed=1;
}

inline bool Trail::is_false(Lit l) {return A[num_vars+l] != Lit_Value::NOT_FALSE;}
inline bool Trail::is_true(Lit l) {return is_false(-l);}
inline void Trail::unset(Lit l) {A[num_vars+l] = Lit_Value::NOT_FALSE;}

inline Clause* Trail::get_reason(Lit l) {return reason[num_vars+l];}

inline bool Trail::is_flagged(Lit l) {return A[num_vars+l] == Lit_Value::FALSE_FLAGGED;}


inline void Trail::set_flag(Lit l) {A[num_vars+l] = Lit_Value::FALSE_FLAGGED;}

inline size_t Trail::current_pos() {return processed;}

inline void Trail::set_false(Lit l, Clause *c) {
  A[num_vars+l] = Lit_Value::FALSE;
  reason[num_vars+l] = c;
  TR.push_back(l);
}


inline void Trail::reset_pending(size_t pos) {processed=pos;}

inline Lit Trail::fetch_pending() {
  if (processed < TR.size())
    return TR[processed++];
  else return 0;
}


inline void Trail::backtrack(size_t pos) {
  for (size_t i=pos;i<TR.size();++i) {
    unset(TR[i]);
  }
  TR.resize(pos);
  processed=pos;
}


void Trail::dump(size_t pos, ostream &out) {
  out<<"TRAIL SUFFIX:";
  for (size_t i=pos;i<TR.size();++i) {
    if (i==processed) out<<" |";
    out<<" "<<TR[i];
    if (is_flagged(TR[i])) out<<"*";
    Clause *c = get_reason(TR[i]);
    if (c) out<<"("<<c->id()<<")";
    else out<<"(A)";
  }
  out<<endl;
}



void Trail::backtrack_and_mark(size_t pos, FVC_Out &out) {
  for (size_t i=pos;i<TR.size();++i) {
    if (is_flagged(TR[i])) {
      Clause *rc = get_reason(TR[i]);
      if (rc) {
        INCR_STAT(stat_relevant_unit_clauses);
        rc->mark();
        out.unit_id(rc->id());
      }
    }
    unset(TR[i]);
  }
  TR.resize(pos);
  processed=pos;
}


void Trail::emit_units(size_t pos, FVC_Out &out) {
  out.cmd_unit_prop_start();

  for (size_t i=pos;i<TR.size();++i) {
    Clause *rc = get_reason(TR[i]);
    if (rc) out.unit_id(rc->id());
  }

  out.cmd_unit_prop_end();
}


/*
  Flag all literals on trail which where required to set the already flagged literals >= pos.

  This function is to be used after an initial flagging of relevant literals, and computes the transitive closure of them.

  Implementation:
    This function exploits the fact that literals earlier in the trail cannot be set due to literals that occur later
    in the trail. Thus, a single backwards pass over the trail is sufficient.
*/
inline void Trail::analyze_conflict_aux(size_t pos) {
  size_t i = TR.size();
  while (i>pos) {
    --i;

    Lit l = TR[i];

    if (is_flagged(l)) {
      Clause *c=get_reason(l);
      if (!c) continue;
      for (Lit *k=c->first();*k;++k) if (*k!=-l) set_flag(*k);
    }
  }
}



void Trail::analyze_conflict(size_t pos, Clause *c) {
  for (Lit *l=c->first();*l;++l) set_flag(*l);

  analyze_conflict_aux(pos);
}


void Trail::analyze_conflict(size_t pos, Lit l) {
  set_flag(l);
  analyze_conflict_aux(pos);
}






// Represents watched literals for clauses
class Watched {
  public:
    Watched(size_t _num_vars, size_t num_cids);

    ~Watched();

    // Get list of clauses where literal is watched
    inline vector<Clause*>* get_watched_clauses(Lit l);

    // Get first watched literal of clause
    inline Lit get_w1(Clause* c);
    // Get second watched literal of clause
    inline Lit get_w2(Clause* c);

    // Set first watched literal of clause. Warning: Does not remove the old watched literal from watchlist!
    inline void set_add_w1(Clause* c, Lit l);
    // Set second watched literal of clause. Warning: Does not remove the old watched literal from watchlist!
    inline void set_add_w2(Clause* c, Lit l);

    // Swap watched literals of clause
    inline void swap_watched(Clause *c);

    // Remove clause from watchlists
    void remove_watched(Clause* c);
    // Iterate over all clauses in watchlists
    template<typename F> void foreach_clause(F f);


  private:
    vector<Clause*>* WM; // Middle-pointer of array with watch-lists for literals
    vector<pair<Lit,Lit>> W; // Mapping from Clause Ids to watched literals
    size_t num_vars;

    // Deleted
    Watched(const Watched&);
    Watched &operator=(const Watched&);


};



Watched::Watched(size_t _num_vars, size_t num_cids) : WM(nullptr), W(), num_vars(_num_vars) {
  WM = (new vector<Clause*> [2*num_vars+1]) + num_vars;
  W.resize(num_cids,{0,0});
}

Watched::~Watched() {
  delete [] (WM - num_vars);

}

// Get list of clauses where literal is watched
inline vector<Clause*>* Watched::get_watched_clauses(Lit l) {return WM + l;}

inline Lit Watched::get_w1(Clause* c) {return W[c->id()].first;}
inline Lit Watched::get_w2(Clause* c) {return W[c->id()].second;}

inline void Watched::set_add_w1(Clause* c, Lit l) {
  W[c->id()].first = l;
  get_watched_clauses(l)->push_back(c);
}
inline void Watched::set_add_w2(Clause* c, Lit l) {
  W[c->id()].second = l;
  get_watched_clauses(l)->push_back(c);
}

inline void Watched::swap_watched(Clause *c) {
  auto ww=W[c->id()];
  W[c->id()].first=ww.second;
  W[c->id()].second=ww.first;
}


void Watched::remove_watched(Clause* c) {
  Lit w1=get_w1(c); Lit w2=get_w2(c);

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

// Iterate over all clauses
template<typename F> void Watched::foreach_clause(F f) {
  for (Lit l=-(Lit)num_vars;l<=(Lit)num_vars;++l) {
    for (Clause *c : WM[l]) {
      if (l == get_w1(c)) {
        f(c);
      }
    }
  }


}
























//enum uprop_result {
//  NO_CONFLICT,
//  CONFLICT
//};

class State {

  public:
    State(size_t num_vars, size_t num_cids);

    /*
      Add a clause to the state, and return next clause in clause database.
    */
    Clause *add_clause(Clause *c);

    /*
      Delete clause form state
    */
    void del_clause(Clause *c);

    // Result of check_rat
    enum class check_rat_result {
      ERROR,          // Error on rat-check
      DISCARDED_TAUT, // Lemma was a tautology
      PROVED          // Lemma proved
    };

    /*
      Check RAT-property for lemma. On success, emit lemma and proof.
      Tautologies are not emitted.
    */
    check_rat_result check_rat(Clause *c, FVC_Out &out);


    /*
      Do unit propagation on current clauses and lemmas.
      Emit unit clauses. Emit conflict clause if conflict is reached.
      Returns true if conflict was found
    */
    bool do_unit_propagation(FVC_Out &out);


  private:
    template<bool only_core> Clause *propagate_units_aux();

    Clause *propagate_units(size_t analyze_start_pos);

    Clause *propagate_units();


  private:
    Trail trail;
    Watched watched;



};



State::State(size_t num_vars, size_t num_cids) : trail(num_vars), watched(num_vars, num_cids) {
}


Clause *State::add_clause(Clause *c) {
  Lit w1 = 0;

  // Find watched literals
  Lit *l;
  for (l=c->first();*l;++l) {
    if (trail.is_true(*l)) {
      return Clause::next(l);     // Clause contains true literal, ignore
    } else if (!trail.is_false(*l)) {
      w1=*l++; break;           // Found watched literal
    }
  }

  if (w1==0) {   // All literals in Clause are false
    return nullptr;
  }

  Lit w2 = 0;
  for (;*l;++l) {
    if (*l!=w1) {
      if (trail.is_true(*l)) {
        return Clause::next(l);   // Clause contains true literal, ignore
      } else if (!trail.is_false(*l)) {
        w2=*l++; break;           // Found watched literal
      }
    }
  }

  if (w2==0) { // Unit Clause, modify assignment
    trail.set_false(-w1,nullptr);
    return Clause::next(l);
  } else {            // Non-unit, non-conflict Clause
    // Scan rest of Clause for true literal (TODO: Not required, check if it speeds up things!)
    for (;*l;++l)
      if (trail.is_true(*l)) return Clause::next(l);

    // Add Clause to watchlist
    watched.set_add_w1(c,w1);
    watched.set_add_w2(c,w2);

    return Clause::next(l);
  }
}


void State::del_clause(Clause *c) {
  watched.remove_watched(c);
}


template<bool only_core> Clause *State::propagate_units_aux() {
  Lit l = 0;
  while ((l=trail.fetch_pending())) {                     // As long as there are unprocessed literals
    vector<Clause*>* l_watched = watched.get_watched_clauses(l);    // Get list of clauses watching this literal
    for (size_t i = 0; i<l_watched->size();) {  // Process clauses
      Clause *c = (*l_watched)[i];
      if (only_core && !c->marked()) {++i; continue;}     // In core mode, ignore unmarked clauses

      Lit w1 = watched.get_w1(c);                         // Get watched literals
      Lit w2 = watched.get_w2(c);

      if (trail.is_true(w1) || trail.is_true(w2)) // If one literal is true, proceed with next Clause
        {++i; continue;}

      if (w1==l) {w1=w2; w2=l; watched.swap_watched(c);}       // Normalize on w2 being set literal

      // Now scan through Clause and find new watched literal
      Lit w=0;
      for ( auto l = c->first(); *l; ++l ) {
        INCR_STAT(stat_watch_search_steps);
        if (*l != w1 && !trail.is_false(*l)) {
          // Found watchable literal
          INCR_STAT(stat_found_new_watched);
          w=*l;
          break;
        }
      }

      if (w) {                                      // Found new watched literal
        watched.set_add_w2(c,w);

        (*l_watched)[i] = l_watched->back();        // Remove this Clause from watchlist
        l_watched->pop_back();
        // Note: We must not increment i, as it points to next clause now

      } else if (!trail.is_false(w1)) {             // Found unit
        //if (!wrote_U) {out<<"U "; wrote_U=true;}
        //out<<c->id()<<" ";
        INCR_STAT(stat_unit_clauses);
        trail.set_false(-w1,c);                     // Assign to true (negated to false)
        ++i;                                        // Proceed with next Clause
      } else {                                      // Found conflict
        //out<<"C "<<c->id()<<endl;
        return c;                            // return from unit propagation with false, indicating found conflict
      }

//          next_clause:;
    }
  }
  //if (wrote_U) out<<"0"<<endl;
  return nullptr;    // No conflict found
}

inline Clause *State::propagate_units(size_t analyze_start_pos) {
//      size_t pos = trail.current_pos();                               // Store current position

//      #ifdef CORE_FIRST
//      if (propagate_units_aux<true>() == CONFLICT) {                  // Try core first
//        INCR_STAT(stat_conflicts_in_core);
//        trail.backtrack(pos);
//        return CONFLICT;
//      }
//
//      trail.reset_pending(pos);                                       // Reset pending position, and try again
//      #endif

  Clause *c = propagate_units_aux<false>();

  if (c) {
    INCR_STAT(stat_conflicts_out_core);
    trail.analyze_conflict(analyze_start_pos,c);                    // TODO: Mark core lemmas here, not during backtrack!
  }

  return c;
}

inline Clause *State::propagate_units() {return propagate_units(trail.current_pos());}


State::check_rat_result State::check_rat(Clause *c, FVC_Out &out) {
  Lit *l = c->first();
  if (!*l) return check_rat_result::ERROR;  // Do not handle empty clause, conflict would have been detected earlier!

  Lit reslit = c->reslit();
  bool false_reslit = trail.is_false(reslit);

  size_t orig_pos = trail.current_pos();

  out.cmd_lemma_start(c->id());

  // Iterate over clause, emit and set literals to false. On the way, detect true literals
  for (;*l;++l) {
    if (trail.is_true(*l)) {
      trail.backtrack(orig_pos);
      out.lemma_discard();        // Discard lemma, its a tautology
      return check_rat_result::DISCARDED_TAUT;
    }
    if (!trail.is_false(*l)) trail.set_false(*l,nullptr);
    out.lemma_lit(*l);
  }

  { // Do unit propagation, for RUP-check
    Clause *cc=propagate_units();

    if (cc) { // Found RUP proof
      out.lemma_start_rup();
      trail.backtrack_and_mark(orig_pos,out); // Backtrack, and emit unit clauses on the way
      out.lemma_end_rup(cc->id());
      out.lemma_end();
      return check_rat_result::PROVED;
    }
  }

  // RUP-check failed, do RAT

  if (false_reslit) {
    //out<<"c RUP failed, RAT not possible due to reslit being false"<<endl;
    return check_rat_result::ERROR;
  }

  //out<<"c "; trail.dump(orig_pos,out);


  out.lemma_start_rat(reslit);
  //out<<"R "<<reslit<<endl;
  size_t rup_pos = trail.current_pos();

  // Collect clauses containing -reslit
  vector<Clause*> rat_candidates;

  watched.foreach_clause([&rat_candidates, reslit](Clause *c) {
    for (Lit *l=c->first();*l;++l) {
      if (*l == -reslit) {
        rat_candidates.push_back(c);
        return;
      }
    }
  });

  // TODO: How many candidates remain here, compared to the blocked ones?
  // Sort candidates by id
  std::sort(rat_candidates.begin(),rat_candidates.end(),[](Clause* c1, Clause* c2) {return (c1->id() < c2->id());});

  // Perform rat-checks
  for (Clause *c : rat_candidates) {
    for (Lit *l=c->first();*l;++l) {
      if (*l == -reslit) continue;
      if (trail.is_true(*l)) {
        trail.backtrack(rup_pos);

        // Flag literals that causes -l to be set
        trail.analyze_conflict(orig_pos,-*l);

        out.lemma_rat_justify_blocked(c->id());

        goto next_candidate;
      }

      if (!trail.is_false(*l)) trail.set_false(*l,nullptr);
    }

    //out<<"r "<<c->id()<<" ";

    {
      Clause *cc = propagate_units(orig_pos); // Propagate units, do conflict analysis wrt to original trail position

      if (cc) {
        out.lemma_rat_start_justification(c->id());
        trail.backtrack_and_mark(rup_pos, out);
        out.lemma_rat_end_justification(cc->id());
      } else {
        // Dump additional info
        cerr<<"RAT CHECK FAILED"<<endl;
        cerr<<"  for candidate "<<c->id()<<endl;
        trail.dump(orig_pos,cerr);

        return check_rat_result::ERROR;
      }
    }

    next_candidate:;
  }


  // RAT check succeeded. Backtrack over initial unit propagation, and assemble output

  out.lemma_rat_start_units();
  trail.backtrack_and_mark(orig_pos, out);
  out.lemma_rat_end_units();
  out.lemma_end_rat();
  out.lemma_end();

  return check_rat_result::PROVED;
}


bool State::do_unit_propagation(FVC_Out &out) {
  size_t pos = trail.current_pos();

  out.cmd_unit_prop_start();
  Clause *cc = propagate_units();
  if (cc) {
    trail.backtrack_and_mark(pos,out);
    out.cmd_unit_prop_end();
    out.cmd_conflict_clause(cc->id());
  } else {
    trail.emit_units(pos,out);
  }

  return cc;
}





























/*
  Hash-values and equality for sorted clauses.
*/
class Clause_Hash_Eq {
  private:
    Clausedb &cdb;

  public:
    Clause_Hash_Eq(Clausedb &_cdb /*= *(Clausedb*)nullptr*/) : cdb(_cdb) {}

    inline size_t operator() (const size_t &cpos) const {
      Clause *c = cdb.clause_at(cpos);

      size_t sum=0, prod=1, xxor=0; // The hash-function from drat-trim
      for (Lit *l=c->first();*l;++l) {
        prod*=*l; sum+=*l; xxor^=*l;
      }
      return (1023 * sum + prod) ^ (31 * xxor);
    }

    inline bool operator() (const size_t &pos1, const size_t &pos2) const {
      Lit *l1 = cdb.clause_at(pos1)->first();
      Lit *l2 = cdb.clause_at(pos2)->first();

      size_t i=0;
      do {
        if (l1[i]!=l2[i]) return false;
      } while (l1[i++]);
      return true;
    }

};


class Parsing {
  public:
    Clausedb &cdb;
    Clause_Hash_Eq cheq;

    unordered_multimap<size_t,size_t,Clause_Hash_Eq,Clause_Hash_Eq> clause_map;

  public:
    Parsing(Clausedb &_cdb);

    size_t parse_clause_raw(istream &);
    void commit_clause(size_t pos);
    void retract_clause(size_t pos);

    size_t parse_clause(istream &);

    void ignore_comments(istream &);

    void parse_dimacs(istream &);
    void parse_proof(istream &);

};

Parsing::Parsing(Clausedb &_cdb) :
  cdb(_cdb),
  cheq(cdb),
  clause_map(0,cheq,cheq)
{}



/*
  Parse a clause.
  Return position of that clause.
*/
size_t Parsing::parse_clause_raw(istream &s) {
  cdb_t l;

  // FIXME: Depends on internal clause repr!

  size_t pos=cdb.clausedb.size();
  cdb.clausedb.push_back(cdb.next_id<<1);

  s>>l;                        // First literal gets resolution literal
  cdb.clausedb.push_back(l);

  while (true) {
    cdb.clausedb.push_back(l);
    cdb.max_var = max(static_cast<size_t>(abs(l)),cdb.max_var);
    if (l==0) break;
    s>>l;
  }

  // Sort literals of clause
  sort(cdb.clausedb.begin() + pos + 2, cdb.clausedb.end() - 1);

  return pos;
}

inline void Parsing::commit_clause(size_t) {
  cdb.next_id++;
}

inline void Parsing::retract_clause(size_t pos) {
  cdb.clausedb.resize(pos);
}

/*
  Parse a clause.
  Return position of that clause.
*/
inline size_t Parsing::parse_clause(istream &s) {
  size_t pos=parse_clause_raw(s);
  commit_clause(pos);
  return pos;
}

inline void Parsing::ignore_comments(istream &s) {
  s>>ws;
  while (!s.eof()) {
    if (s.peek()!='c') break;
    s.ignore(numeric_limits<streamsize>::max(), '\n');
    s>>ws;
  }
}

void Parsing::parse_dimacs(istream &s) {
  cdb.clausedb.clear();

  cdb.clausedb.push_back(0); // Guard for Clause::prev() operation
  cdb.next_id=1;
  cdb.max_var = 0;

  clause_map.clear();

  s.exceptions(s.failbit|s.badbit);

  ignore_comments(s);
  if (s.peek()=='p') s.ignore(numeric_limits<streamsize>::max(), '\n');

  while (!s.eof()) {
    ignore_comments(s);
    if (s.eof()) break;

    // Parse a Clause
    size_t cpos = parse_clause(s);

    clause_map.insert({cpos,cpos});
  }

  // Mark start of proof
  cdb.proof_start = cdb.clausedb.size();


/*  for (size_t i=0;i<clausedb.size();++i) {
    int x = clausedb[i];
    cout<<x;
    if (x) cout<<" "; else cout<<endl;
  }
*/

}


void Parsing::parse_proof(istream &s) {
  s.exceptions(s.failbit|s.badbit);

  ignore_comments(s);
  if (s.peek()=='o') s.ignore(numeric_limits<streamsize>::max(), '\n');
  ignore_comments(s);

  while (!s.eof()) {
    ignore_comments(s);
    if (s.eof()) break;

    bool del=false;
    if (s.peek()=='d') {
      s.get();
      del=true;
    }
    size_t cpos = parse_clause_raw(s);

    if (del) {
      auto orig_c = clause_map.find(cpos);

      if (orig_c != clause_map.end()) {
        retract_clause(cpos);
        cdb.clausedb.push_back(-1); cdb.clausedb.push_back(orig_c->second);
        clause_map.erase(orig_c);
      } else {
        cerr<<"c Ignoring deletion of non-existing clause ";
        cdb.clause_at(cpos)->write(cdb,cerr,true);
        retract_clause(cpos);
      }
    } else {
      commit_clause(cpos);
      clause_map.insert({cpos,cpos});
    }
  }
}


class Checker {
  private:
    Clausedb &cdb;
    State s;

  public:
    Checker(Clausedb &_cdb);

    /*
      Process original clauses.
      Returns true if this already proves UNSAT.
    */
    bool process_cnf(FVC_Out &out);

    /*
      Check proof.
      Returns true if UNSAT proved, false otherwise.
    */
    bool process_proof(FVC_Out &out);


};



Checker::Checker(Clausedb &_cdb) : cdb(_cdb), s(cdb.get_num_vars(),cdb.get_num_cids()) {}

/*
  Process original clauses.
  Returns true if this already proves UNSAT.
*/
bool Checker::process_cnf(FVC_Out &out) {
  Clause *c = cdb.first_clause();

  while (c && c!=cdb.first_proof_clause()) {
    c = s.add_clause(c);
  }

  if (c == nullptr) {
    cerr<<"c TRIVIAL CONFLICT IN ORIGINAL CLAUSES"<<endl;
    return true;
  }

  if (s.do_unit_propagation(out)) {
    cerr<<"c CONFLICT IN ORIGINAL CLAUSES AFTER UNIT PROPAGATION"<<endl;
    return true;
  }

  return false;
}

/*
  Check proof.
  Returns true if UNSAT proved, false otherwise.
*/
bool Checker::process_proof(FVC_Out &out) {
  Clause *c = cdb.first_proof_clause();

  size_t intv_start = cdb.get_num_cids() / 100;
  size_t intv = intv_start;
  size_t db_size = reinterpret_cast<cdb_t>(cdb.end_clause()) - reinterpret_cast<cdb_t>(cdb.first_clause());

  while (c && c!=cdb.end_clause()) {
    if (!--intv) {
      intv=intv_start;
      float p = (reinterpret_cast<cdb_t>(c) - reinterpret_cast<cdb_t>(cdb.first_clause())) / static_cast<float>(db_size);

      cerr<<(p*100)<<"% "; cerr.flush();
      //PRINT_STATS(cerr);

    }


    //c->write(cdb,out);

    if (c->is_del()) {
      // TODO: If clause was skipped for output b/c it is a tautology, it's id is still written here!

      Clause *dc = cdb.clause_at(c->del_pos());
      if (!dc->is_marked_skipped()) {
        s.del_clause(dc);
        out.cmd_del(dc->id());
      }
      c = c->next();
    } else {
      switch (s.check_rat(c,out)) {
        case State::check_rat_result::ERROR:
          cerr<<"c RAT CHECK ERROR"<<endl;
          return false;

        case State::check_rat_result::DISCARDED_TAUT:
          c->mark_skipped();
          c = c->next();
          break;

        case State::check_rat_result::PROVED:
          c = s.add_clause(c);

          if (s.do_unit_propagation(out)) {
            cerr<<"c PROVED CONFLICT BY UNIT PROPAGATION"<<endl;
            return true;
          }
      }


    }
  }

  cerr<<"c PROOF CLAUSES CHECKED BUT NO CONFLICT"<<endl;
  return false;
}
























void print_usage() {
  cerr<<"Usage drat-ri <dimacs-file> <proof-file>"<<endl;
}

void print_info() {
  cerr<<"sizeof(cdb_t) = "<<sizeof(cdb_t)<<endl;
  cerr<<"sizeof(Lit) = "<<sizeof(Lit)<<endl;
  cerr<<"sizeof(Clause*) = "<<sizeof( Clause* )<<endl;
}




int main(int argc, char **argv)
{
  ifstream cnf;
  ifstream prf;

  {
    if (argc!=3) {print_usage(); return 2;}

    cnf.open(argv[1],ifstream::in);
    prf.open(argv[2],ifstream::in);
  }

  print_info();

  cerr<<"Parsing"<<endl;

  Clausedb cdb;
  {
    Parsing p(cdb);
    p.parse_dimacs(cnf);
    p.parse_proof(prf);
    cnf.close();
    prf.close();
  }

//  for (Clause *c=cdb.first_clause();c!=cdb.first_proof_clause();c=c->next()) {
//    c->write(cdb,cerr);
//  }

  //p.dbg_init();

  Checker chk(cdb);

  FVC_Out out = FVC_Out(cout);

  cerr<<"Processing CNF"<<endl;

  if (chk.process_cnf(out)) {
    cerr<<"UNSAT"<<endl;
    return 0;
  }

  cerr<<"Processing proof"<<endl;

  if (chk.process_proof(out)) {
    cerr<<"UNSAT"<<endl;
    PRINT_STATS(cerr);
    return 0;
  }

  // Error
  cerr<<"ERROR"<<endl;
  PRINT_STATS(cerr);
  return 1;
}

