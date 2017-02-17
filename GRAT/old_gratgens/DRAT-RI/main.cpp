#include <cstdlib>
#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <cassert>
#include <limits>

using namespace std;

class Lit {
public:
  int l;
  inline Lit(int _l) : l(_l) {}
  inline Lit operator -() {return Lit(-l);}
  inline bool operator ==(Lit x) {return l==x.l;}
  inline bool operator !=(Lit x) {return l!=x.l;}
  inline bool is_null() {return l==0;}
};

Lit null_lit = Lit(0);


class Var {
public:
  int v;
  inline Var(int _v) : v(_v) {}
  inline bool operator ==(Var x) {return v==x.v;}
  inline bool operator !=(Var x) {return v!=x.v;}
};

inline Var var_of_lit(Lit l) {
  return Var(abs(l.l));
}


// Represent a Clause
class Clause {
  private:
    Clause();
  public:
    inline int id() {return *(int*)this;};

    inline Lit* first() {return (Lit*)(((int*)this)+1);}

    void dump() {
      cout<<id()<<": ";
      for (Lit* l=first(); !l->is_null();++l)
        cout<<(l->l)<<" ";

    }

    inline static Clause* next(Lit *l) {
      for (;!l->is_null();++l);
      ++l;
      return (Clause*) l;
    }

    inline Clause* next() {
      return next(first());
    }


    inline static Clause* prev(Clause *c) {
      int *l=(int*)c;

      l = l - 2; // Skip over terminating zero of last clause

      while (*l) l--; // Skip until terminating zero before previous clause
      l++;  // Go back to start of previous clause

      return (Clause*)l;
    }


};

// Assignment


class Assignment {
  private:
    int *A;

    static const int UNDEC = 0;
    static const int TRUE = 1;
    static const int FALSE = 2;



  public:
      Assignment (size_t);

      bool is_false (Lit);
      bool is_true (Lit);
      void set_false (Lit);
      void unset (Lit);

};


Assignment::Assignment(size_t num_var) {
  A = new int [num_var] ();
}

inline bool Assignment::is_false (Lit l) {
  if (l.l<0) return A[-l.l] == TRUE;
  else return A[l.l] == FALSE;
}

inline bool Assignment::is_true (Lit l) {
  if (l.l<0) return A[-l.l] == FALSE;
  else return A[l.l] == TRUE;
}


inline void Assignment::set_false (Lit l) {
  if (l.l<0) A[-l.l] = TRUE;
  else A[l.l] = FALSE;
}

inline void Assignment::unset (Lit l) {
  A[abs(l.l)]=UNDEC;
}


typedef vector<Lit>::size_type trailpos;
class Trail {
  private:
    Assignment A;     // Assignment
    vector<Lit> TR;   // Trail, as list of literals which are set to false
    Clause**reasons;  // Reason as map from variables to Clause*, or 0 if literal was set otherwise

    trailpos pending; // Position of first unprocessed literal in trail
    size_t num_vars;  // Number of variables
    size_t num_cids;
    Clause *conflict=nullptr; // Conflict clause

  public:
    Trail (size_t, size_t);

    // Assigns undecided literal to false
    void assign_false(Lit);
    void assign_false(Lit,Clause *reason);

    inline Clause* get_reason(Var v) {return reasons[v.v];}
    inline Clause* get_reason(Lit l) {return get_reason(var_of_lit(l));}

    // Indicate conflict due to clause
    inline void set_conflict(Clause *reason) {conflict=reason;};
    inline Clause* get_conflict() {return conflict;}

    inline bool is_false(Lit l) {return A.is_false(l);};
    inline bool is_true(Lit l) {return A.is_true(l);};

    trailpos current_pos();
    void backtrack (trailpos);
    inline Lit get(trailpos p) {return TR[p];}

    inline Lit fetch_pending() {if (pending<TR.size()) return TR[pending++]; else return null_lit;}

    void dump();



};


Trail::Trail(size_t _num_vars, size_t _num_cids) : A(_num_vars), TR() {
  num_vars=_num_vars;
  num_cids = _num_cids;
  reasons = new Clause* [num_vars];
  pending = 0;
}

inline void Trail::assign_false(Lit l, Clause* reason) {
  A.set_false(l);
  reasons[var_of_lit(l).v] = reason;
  TR.push_back(l);
}

inline void Trail::assign_false(Lit l) {
  assign_false(l,nullptr);
}

trailpos Trail::current_pos() {
  return TR.size();
}

void Trail::backtrack(trailpos p) {
  for (auto i=p;i<TR.size();++i) {
    A.unset(TR[i]);
  }
  TR.resize(p,null_lit);
  if (pending>TR.size()) pending=TR.size();
  conflict=nullptr;
}


void Trail::dump() {
  for (auto l : TR) {
    cout << l.l;

    Clause *r = reasons[var_of_lit(l).v];
    if (r) cout << " b/c " << r->id();
    else cout << " assm";
    cout<<endl;

  }
}



// Represents watched literals for clauses
class Watched {
  private:
    vector<Clause*>* WM; // Middle-index of array with watch-lists for literals
    vector<pair<Lit,Lit>> W; // Mapping from Clause Ids to watched literals

  public:
    inline Watched(int num_vars, int next_cid) {
      WM = (new vector<Clause*> [2*num_vars+1]) + num_vars;

      W.resize(next_cid,{null_lit,null_lit});

    }

    // Get list of clauses where literal is watched
    inline vector<Clause*>* get_watched_clauses(Lit l) {return WM + l.l;}

    inline Lit get_w1(Clause* c) {return W[c->id()].first;}
    inline Lit get_w2(Clause* c) {return W[c->id()].second;}

    inline void set_add_w1(Clause* c, Lit l) {
      W[c->id()].first = l;
      get_watched_clauses(l)->push_back(c);
    }
    inline void set_add_w2(Clause* c, Lit l) {
      W[c->id()].second = l;
      get_watched_clauses(l)->push_back(c);
    }


    void remove_watched(Clause* c) {
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

};


enum uprop_result {
  NO_CONFLICT,
  CONFLICT
};

/*
  Information if clause induced unit propagation
*/
class IUP_info {
  public:
    int id;         // Id of clause
    trailpos pos;   // Position in trail before induced unit propagation

    IUP_info(int _id, trailpos _pos) {
      id=_id;
      pos=_pos;
    }
};


class State {
  private:
    Trail trail;
    Watched watched;
    size_t num_vars;
    size_t num_cids;

    vector<IUP_info> iups;
    vector<bool> active;


  public:
    State(size_t _num_vars, size_t _num_cids) :
      trail(_num_vars,_num_cids),
      watched(_num_vars,_num_cids),
      active(_num_cids,false)
    {
      num_vars = _num_vars;
      num_cids = _num_cids;
    };


    inline bool has_conflict() {return trail.get_conflict()!=nullptr;}

    /*
      Do unit propagation, until all units are processed or a conflict is found.
      In case of conflict, the trail ends with the literal that ultimately caused the conflict.
    */
    uprop_result propagate_units() {
      Lit l = null_lit;
      while ((l=trail.fetch_pending())!=null_lit) {                     // As long as there are unprocessed literals
        vector<Clause*>* l_watched = watched.get_watched_clauses(l);    // Get list of clauses watching this literal
        for (vector<Clause*>::size_type i = 0; i<l_watched->size();) {  // Process clauses
          Clause *c = (*l_watched)[i];

          Lit w1 = watched.get_w1(c);                         // Get watched literals
          Lit w2 = watched.get_w2(c);

          if (trail.is_true(w1) || trail.is_true(w2)) // If one literal is true, proceed with next Clause
            {++i; continue;}

          bool xchg1 = false;                         // Set if w1 receives new literal
          if (w1==l) {w1=w2; w2=l; xchg1=true;}       // Normalize on w2 being set literal

          // Now scan through Clause and find new watched literal
          for ( auto w = c->first(); !w->is_null(); ++w ) {
            if (*w != w1 && !trail.is_false(*w)) {        // Found one!
              if (xchg1) watched.set_add_w1(c,*w);        // Set it
              else watched.set_add_w2(c,*w);

              (*l_watched)[i] = l_watched->back();        // Remove this Clause from watchlist
              l_watched->pop_back();

              goto next_clause;                           // Continue with next Clause
            }
          }

          // We have found conflict or unit
          if (!trail.is_false(w1)) {                    // Unit
            trail.assign_false(-w1,c);                  // Assign to true (negated to false), due to Clause c
            ++i; goto next_clause;                      // Proceed with next Clause
          } else {                                      // Conflict
            trail.set_conflict(c);
            return CONFLICT;                            // return from unit propagation with false, indicating found conflict
          }

          next_clause:;
        }
      }
      return NO_CONFLICT;    // No conflict found
    }


    Clause *add_clause_iup(Clause *c) {
      Lit w1 = null_lit;

      // Find watched literals
      Lit *l;
      for (l=c->first();!l->is_null();++l) {
        if (trail.is_true(*l)) {
          return Clause::next(l);     // Clause contains true literal, ignore
        } else if (!trail.is_false(*l)) {
          w1=*l++; break;           // Found watched literal
        }
      }

      if (w1==null_lit) {   // All literals in Clause are false
        trail.set_conflict(c);
        return nullptr;
      }

      Lit w2 = null_lit;
      for (;!l->is_null();++l) {
        if (*l!=w1) {
          if (trail.is_true(*l)) {
            return Clause::next(l);   // Clause contains true literal, ignore
          } else if (!trail.is_false(*l)) {
            w2=*l++; break;           // Found watched literal
          }
        }
      }

      if (w2==null_lit) { // Unit Clause, modify assignment and start unit propagation
        iups.push_back(IUP_info(c->id(), trail.current_pos()));
        trail.assign_false(-w1,c);

        if (propagate_units() == CONFLICT) return nullptr;
        else return Clause::next(l);
      } else {            // Non-unit, non-conflict Clause
        // Scan rest of Clause for true literal (TODO: Not required, check if it speeds up things!)
        for (;!l->is_null();++l)
          if (trail.is_true(*l)) return Clause::next(l);

        // Add Clause to watchlist
        watched.set_add_w1(c,w1);
        watched.set_add_w2(c,w2);

        return Clause::next(l);
      }
    }



    void analyze_conflict();

    void write_cert_1(Clause *,ostream &);
    void write_cert_conf(ostream &);


    bool justify_bwd(Clause *c, ostream &);

    void write_iups(int, ostream&);
    void remove_clause(Clause *c);

    bool check_rat(Clause *, ostream &);


    void inline dump_trail() {trail.dump();}

};


void State::analyze_conflict() {
  assert(has_conflict());
  vector<Clause *> stk;

  stk.push_back(trail.get_conflict());

  while (!stk.empty()) {
    Clause *c = stk.back(); stk.pop_back();

    if (!active[c->id()]) {
      active[c->id()]=true;
      cerr<<"activate "<<c->id()<<endl;
      for (Lit *l = c->first(); !l->is_null(); ++l) {
        Clause *r=trail.get_reason(*l);
        if (r) stk.push_back(r);
      }
    }
  }
}

void State::write_iups(int id, ostream &out) {
  if (!iups.empty() && iups.back().id == id) {
    out<<" U";
    for (trailpos p=iups.back().pos;p<trail.current_pos();++p) {
      Clause *cc = trail.get_reason(trail.get(p));

      if (active[cc->id()]) {
        out<<" "<<cc->id();
      }
    }
  }
}

inline void State::remove_clause(Clause *c) {
  auto id = c->id();
  if (!iups.empty() && iups.back().id == id) {
    trail.backtrack(iups.back().pos);
    iups.pop_back();
  }
  watched.remove_watched(c);
}

void State::write_cert_1(Clause *c, ostream &out) {
  auto id = c->id();
  if (active[id]) {
    out<<"A ";
    out<<id;
    write_iups(id,out);
    out<<endl;
  }
  remove_clause(c);
}

void State::write_cert_conf(ostream &out) {
  out<<"C "<<trail.get_conflict()->id()<<endl;
}

bool State::check_rat(Clause *c, ostream &out) {
  auto orig_pos = trail.current_pos();

  if (c->first()->is_null()) return true;

  Lit reslit = *c->first();

  // Check RAT

  // Assign literals of clause to false
  for (Lit *l = c->first(); !l->is_null(); ++l) trail.assign_false(*l);

  if (propagate_units() == CONFLICT) {
    analyze_conflict();




  }



}


bool State::justify_bwd(Clause *c, ostream &out) {
  auto id = c->id();
  bool act = active[id];
  if (act) {
    write_iups(id,out);
  }
  remove_clause(c);

  if (act) {
    if (!check_rat(c,out)) return false;
    //write_clause(c,out);
  }

}


//  if clause is active
//    dump active induced unit-props
//
//  backtrack over clause effect, remove clause from watched list!
//
//  if clause is active
//    justify clause with RAT, dump proofs
//    dump clause


/*void State::analyze_initial_conflict() {
  vector<bool> active(num_cids,false);

  vector<Clause *> stk;

  vector<int> uids;

  {
    Clause *c = trail.get_conflict();
    if (c) {
      stk.push_back(c);
    }
  }

  while (!stk.empty()) {
    Clause *c = stk.back(); stk.pop_back();

    if (!active[c->id()]) {
      active[c->id()]=true;

      uids.push_back(c->id());

      for (Lit *l = c->first(); !l->is_null(); ++l) {
        Clause *r=trail.get_reason(*l);
        if (r) stk.push_back(r);
      }
    }
  }

  reverse(uids.begin(),uids.end());

  // Dump active clauses
  cout<<"A ";
  for (size_t i=0;i<num_cids;++i)
    if (active[i]) cout<<i<<" ";
  cout<<endl;

  cout<<"U ";
  for (auto i : uids) cout<<i<<" ";
  cout<<endl;


}
*/





class Parsing {
  private:
    vector<int> clausedb;   // Flat Clause database
    int next_id = 1;        // Next Clause id
    int max_var = 0;        // Maximum variable value
    vector<int>::size_type proof_start=0; // Start index of proof in db

    Clause* first_clause() {return clausedb.empty()?nullptr:(Clause*)(clausedb.data()+1);}
    Clause* first_proof_clause() {return clausedb.empty()?nullptr:(Clause*)(clausedb.data() + proof_start);}
    Clause* end_clause() { return clausedb.empty()?nullptr:(Clause*)(clausedb.data() + clausedb.size()); }

  public:
    void parse_dimacs(istream &);
    void parse_clause(istream &);
    void parse_proof(istream &);

    void dbg_init() {
      clausedb = {
        0,
        1, 1,2,0,
        2, -1,2,0,
        3, -2, 0};
      next_id=4;
      max_var=2;
      proof_start=clausedb.size();
    };

    State *init_state();

    bool init_proof(State *);

    void write_cert_1(State *, ostream &);

    bool check_proof(State *, ostream &);


};

void Parsing::parse_clause(istream &s) {
  int l;

  clausedb.push_back(next_id++);
  do {
    s>>l;
    clausedb.push_back(l);
    max_var = max(abs(l),max_var);
  } while (l!=0);
}

void Parsing::parse_dimacs(istream &s) {
  clausedb.clear();

  clausedb.push_back(0); // Guard for Clause::prev() operation
  next_id=1;
  max_var = 0;

  s.exceptions(s.failbit|s.badbit);

  if (s.peek()=='p') s.ignore(numeric_limits<streamsize>::max(), '\n');

  while (!s.eof()) {
    s>>ws;
    if (s.eof()) break;

    if (s.peek()=='c') { // Skip over comments
      s.ignore(numeric_limits<streamsize>::max(), '\n');
      continue;
    }

    // Parse a Clause
    parse_clause(s);
  }

  // Mark start of proof
  proof_start = clausedb.size();


/*  for (size_t i=0;i<clausedb.size();++i) {
    int x = clausedb[i];
    cout<<x;
    if (x) cout<<" "; else cout<<endl;
  }
*/

}

void Parsing::parse_proof(istream &s) {
  s.exceptions(s.failbit|s.badbit);

  while (!s.eof()) {
    s>>ws;
    if (s.eof()) break;
    if (s.peek()=='d') {
      s.ignore(numeric_limits<streamsize>::max(), '\n');
      cout<<"Ignoring deletion"<<endl;
    } else {
      parse_clause(s);
    }
  }
}


State *Parsing::init_state() {
  State *s = new State(max_var+1,next_id);

  Clause* c = first_clause();

  Clause* c_end = first_proof_clause();

  while (c && c != c_end) {

    c->dump();
    cout<<endl;

    c = s->add_clause_iup(c);
  }

  return s;
}

bool Parsing::init_proof(State *s) {
  Clause *c = first_proof_clause();

  Clause* c_end = end_clause();

  while (c && c != c_end) {
    c = s->add_clause_iup(c);
  }

  return s->has_conflict();
}


void Parsing::write_cert_1(State *s, ostream &out) {
  // Iterate backwards over original clauses
  Clause *c = first_proof_clause();
  Clause *c_begin=first_clause();

  if (c == c_begin) return;


  do {
    c=Clause::prev(c);
    s->write_cert_1(c,out);
  } while (c != c_begin);

}


//xxx, ctd here: implement proof checking/dumping phase:
//  iterate backwards over proof
//  if clause is active
//    dump active induced unit-props
//
//  backtrack over clause effect, remove clause from watched list!
//
//  if clause is active
//    justify clause with RAT, dump proofs
//    dump clause

bool Parsing::check_proof(State *s, ostream &out) {
  Clause *c = end_clause();
  Clause *c_begin=first_proof_clause();

  if (c == c_begin) return true;

  do {
    c = Clause::prev(c);
    if (!s->justify_bwd(c,out)) return false;
  } while (c != c_begin);


  return true;
}


void print_usage() {
  cout<<"Usage drat-ri <dimacs-file> <proof-file>"<<endl;
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


  assert(sizeof(Lit) == sizeof(int));
  assert(sizeof(Var) == sizeof(int));

  Parsing p;
  p.parse_dimacs(cnf);
  p.parse_proof(prf);
  cnf.close();
  prf.close();

  //p.dbg_init();

  State *s = p.init_state();

  if (s->has_conflict()) {
    cout<<"Initial conflict"<<endl;

    s->analyze_conflict();

    s->write_cert_conf(cout);
    p.write_cert_1(s,cout);

    cout<<"UNSAT"<<endl;
    return 0;
  }

  if (!p.init_proof(s)) {
    cout<<"Proof does not lead to conflict"<<endl;
    cout<<"ERROR"<<endl;
    return 1;
  }


  return 1;
}
