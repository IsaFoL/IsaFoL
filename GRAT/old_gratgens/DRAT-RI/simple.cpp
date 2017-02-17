#include <cstdlib>
#include <iostream>
#include <fstream>
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

  void print_stats(ostream &out) {
    out<<"found_new_watched = "<<stat_found_new_watched<<endl;
    out<<"watch_search_steps = "<<stat_watch_search_steps<<endl;
  }


  #define INCR_STAT(var) (++var)
  #define PRINT_STATS(out) print_stats(out)
#else
  #define INCR_STAT(var)
  #define PRINT_STATS(out)
#endif



// Represent trail and assignment
class Trail {
public:
  typedef unsigned freq_t;
private:
  size_t num_vars;
  vector<bool> A;

  vector<Lit> TR;
  size_t processed;

  inline void set_false_raw(Lit l) {A[num_vars+l] = true; }

public:
  inline Trail(size_t _num_vars) : A(2*_num_vars+1,false) {
    num_vars=_num_vars;
    processed=0;
  }

  inline bool is_false(Lit l) {return A[num_vars+l];}
  inline bool is_true(Lit l) {return A[num_vars-l];}
  inline void unset(Lit l) {A[num_vars+l] = false;}

  inline size_t current_pos() {return processed;}
  inline void set_false(Lit l) {set_false_raw(l); TR.push_back(l); }

  inline Lit fetch_pending() {
    if (processed < TR.size())
      return TR[processed++];
    else return 0;
  }

  inline void backtrack(size_t pos) {
    while (TR.size()>pos) {
      unset(TR.back());
      TR.pop_back();
    }
    processed=pos;
  }

  inline void delete_trail() {TR.clear();}


};


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
    inline size_t get_num_vars() {return max_var;}
    inline size_t get_num_cids() {return next_id;}

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

    Clause* clause_at(size_t cpos) {return (Clause*)(clausedb.data() + cpos); }
    Clause* first_clause() {return clausedb.empty()?nullptr:(Clause*)(clausedb.data()+1);}
    Clause* first_proof_clause() {return clausedb.empty()?nullptr:(Clause*)(clausedb.data() + proof_start);}
    Clause* end_clause() { return clausedb.empty()?nullptr:(Clause*)(clausedb.data() + clausedb.size()); }

};


// Represent a Clause
class Clause {
  private:
    Clause();

    inline cdb_t* data() { return reinterpret_cast<cdb_t*>(this); }

  public:


    inline Cid id() {return data()[0];};

    inline Lit* first() {return data()+1;}

    inline bool is_del() {return id()==-1;}
    inline size_t del_pos() { return data()[1]; }

    void write(Clausedb &cdb, ostream &out, bool no_id=false) {
      if (is_del()) {
        out<<"d "<<cdb.clause_at(del_pos())->id()<<endl;
      } else {
        if (!no_id) out<<id()<<" ";
        for (Lit* l=first();*l;++l)
          out<<*l<<" ";
        out<<"0"<<endl;
      }
    }

    inline static Clause* next(Lit *l) {
      for (;*l;++l);
      ++l;
      return reinterpret_cast<Clause*>(l);
    }

    inline Clause* next() {
      if (is_del()) {
        return reinterpret_cast<Clause*>(data()+2);
      } else {
        return next(first());
      }
    }


    /*inline static Clause* prev(Clause *c) {
      int *l=(cdb_t*)c;

      l = l - 2; // Skip over terminating zero of last clause

      while (*l) l--; // Skip until terminating zero before previous clause
      l++;  // Go back to start of previous clause

      return (Clause*)l;
    }*/


};


// Represents watched literals for clauses
class Watched {
  private:
    vector<Clause*>* WM; // Middle-pointer of array with watch-lists for literals
    vector<pair<Lit,Lit>> W; // Mapping from Clause Ids to watched literals
    size_t num_vars;

  public:
    inline Watched(size_t _num_vars, size_t num_cids) {
      num_vars=_num_vars;
      WM = (new vector<Clause*> [2*num_vars+1]) + num_vars;
      W.resize(num_cids,{0,0});
    }

    ~Watched() {
      delete [] (WM - num_vars);

    }

    // Get list of clauses where literal is watched
    inline vector<Clause*>* get_watched_clauses(Lit l) {return WM + l;}

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

    inline void swap_watched(Clause *c) {
      auto ww=W[c->id()];
      W[c->id()].first=ww.second;
      W[c->id()].second=ww.first;
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

    // Iterate over all clauses
    template<typename F> void foreach_clause(F f) {
      for (Lit l=-(Lit)num_vars;l<=(Lit)num_vars;++l) {
        for (Clause *c : WM[l]) {
          if (l == get_w1(c)) {
            f(c);
          }
        }
      }


    }


};


enum uprop_result {
  NO_CONFLICT,
  CONFLICT
};

class State {
  private:
    Trail trail;
    Watched watched;


  public:
    State(size_t num_vars, size_t num_cids) : trail(num_vars), watched(num_vars, num_cids) {
    }


    Clause *add_clause(Clause *c) {
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
        trail.set_false(-w1);
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


    void del_clause(Clause *c) {
      watched.remove_watched(c);
    }


    uprop_result propagate_units(ostream &out) {
      bool wrote_U=false;

      Lit l = 0;
      while ((l=trail.fetch_pending())) {                     // As long as there are unprocessed literals
        vector<Clause*>* l_watched = watched.get_watched_clauses(l);    // Get list of clauses watching this literal
        for (size_t i = 0; i<l_watched->size();) {  // Process clauses
          Clause *c = (*l_watched)[i];

          Lit w1 = watched.get_w1(c);                         // Get watched literals
          Lit w2 = watched.get_w2(c);

          if (trail.is_true(w1) || trail.is_true(w2)) // If one literal is true, proceed with next Clause
            {++i; continue;}

          if (w1==l) {w1=w2; w2=l; watched.swap_watched(c);}       // Normalize on w2 being set literal

//          // Now scan through Clause and find new watched literal
//          for ( auto w = c->first(); *w; ++w ) {
//            INCR_STAT(stat_watch_search_steps);
//            if (*w != w1 && !trail.is_false(*w)) {        // Found one!
//              INCR_STAT(stat_found_new_watched);
//              watched.set_add_w2(c,*w);
//
//              (*l_watched)[i] = l_watched->back();        // Remove this Clause from watchlist
//              l_watched->pop_back();
//
//              goto next_clause;                           // Continue with next Clause
//            }
//          }

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
            if (!wrote_U) {out<<"U "; wrote_U=true;}
            out<<c->id()<<" ";
            trail.set_false(-w1);                       // Assign to true (negated to false)
            ++i;                                        // Proceed with next Clause
          } else {                                      // Found conflict
            out<<"C "<<c->id()<<endl;
            return CONFLICT;                            // return from unit propagation with false, indicating found conflict
          }

//          next_clause:;
        }
      }
      if (wrote_U) out<<"0"<<endl;
      return NO_CONFLICT;    // No conflict found
    }



    bool check_rat(Clause *c, ostream &out) {
      Lit *l = c->first();
      if (!*l) return false;  // Do not handle empty clause, conflict would have been detected earlier!

      Lit reslit = *l;
      bool false_reslit = trail.is_false(reslit);

      size_t orig_pos = trail.current_pos();

      // Iterate over clause, set literals to false. On the way, detect true literals
      for (;*l;++l) {
        if (trail.is_true(*l)) {
          out<<"c TAUT"<<endl;
          trail.backtrack(orig_pos);
          return true;
        }
        if (!trail.is_false(*l)) trail.set_false(*l);
      }

      // Do unit propagation, for RUP-check
      if (propagate_units(out) == CONFLICT) {
        trail.backtrack(orig_pos);
        return true;
      }

      // RUP-check failed, do RAT

      if (false_reslit) {
        out<<"c RUP failed, RAT not possible due to reslit being false"<<endl;
        return false;
      }

      out<<"R "<<reslit<<endl;
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

      // Sort candidates by id
      std::sort(rat_candidates.begin(),rat_candidates.end(),[](Clause* c1, Clause* c2) {return (c1->id() < c2->id());});

      // Perform rat-checks
      for (Clause *c : rat_candidates) {
        trail.backtrack(rup_pos);
        for (Lit *l=c->first();*l;++l) {
          if (*l == -reslit) continue;
          if (trail.is_true(*l)) goto next_candidate;

          if (!trail.is_false(*l)) trail.set_false(*l);
        }

        out<<"r "<<c->id()<<" ";
        if (propagate_units(out) != CONFLICT) {
          out<<"c RAT CHECK FAILED"<<endl;
          return false;
        }

        next_candidate:;
      }


      // RAT check succeeded
      trail.backtrack(orig_pos);
      return true;
    }


};


class Clause_Hash_Eq {
  private:
    Clausedb &cdb;

  public:
    Clause_Hash_Eq(Clausedb &_cdb /*= *(Clausedb*)nullptr*/) : cdb(_cdb) {}

    inline size_t operator() (const size_t &cpos) const {
      Clause *c = cdb.clause_at(cpos);

      size_t sum=0, prod=1, xxor=0; // The has-function from drat-trim
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

    unordered_map<size_t,size_t,Clause_Hash_Eq,Clause_Hash_Eq> clause_map;

  public:
    Parsing(Clausedb &_cdb) :
      cdb(_cdb),
      cheq(cdb),
      clause_map(0,cheq,cheq)
    {}

    size_t parse_clause_raw(istream &);
    void commit_clause(size_t pos);
    void retract_clause(size_t pos);

    size_t parse_clause(istream &);

    void ignore_comments(istream &);

    void parse_dimacs(istream &);
    void parse_proof(istream &);

};

/*
  Parse a clause.
  Return position of that clause.
*/

size_t Parsing::parse_clause_raw(istream &s) {
  cdb_t l;

  size_t pos=cdb.clausedb.size();
  cdb.clausedb.push_back(cdb.next_id);
  do {
    s>>l;
    cdb.clausedb.push_back(l);
    cdb.max_var = max(static_cast<size_t>(abs(l)),cdb.max_var);
  } while (l!=0);

  // Sort literals of clause
  sort(cdb.clausedb.begin() + pos + 1, cdb.clausedb.end() - 1); // FIXME: Depends on internal clause repr!

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
    Checker(Clausedb &_cdb) : cdb(_cdb), s(cdb.get_num_vars(),cdb.get_num_cids()) {}

    /*
      Process original clauses.
      Returns true if this already proves UNSAT.
    */
    bool process_cnf(ostream &out) {
      Clause *c = cdb.first_clause();

      while (c && c!=cdb.first_proof_clause()) {
        c = s.add_clause(c);
      }

      if (c == 0) {
        out<<"c TRIVIAL CONFLICT IN ORIGINAL CLAUSES"<<endl;
        return true;
      }

      if (s.propagate_units(out) == CONFLICT) {
        out<<"c CONFLICT IN ORIGINAL CLAUSES AFTER UNIT PROPAGATION"<<endl;
        return true;
      }

      return false;
    }

    /*
      Check proof.
      Returns true if UNSAT proved, false otherwise.
    */
    bool process_proof(ostream &out) {
      Clause *c = cdb.first_proof_clause();

      size_t intv_start = cdb.get_num_cids() / 1000;
      size_t intv = intv_start;
      size_t db_size = reinterpret_cast<cdb_t>(cdb.end_clause()) - reinterpret_cast<cdb_t>(cdb.first_clause());

      while (c && c!=cdb.end_clause()) {
        if (!--intv) {
          intv=intv_start;
          float p = (reinterpret_cast<cdb_t>(c) - reinterpret_cast<cdb_t>(cdb.first_clause())) / static_cast<float>(db_size);
          cerr<<(p*100)<<"%"<<endl;
          PRINT_STATS(cerr);
        }


        c->write(cdb,out);

        if (c->is_del()) {
          s.del_clause(cdb.clause_at(c->del_pos()));
          c = c->next();
        } else {
          if (!s.check_rat(c,out)) {
            out<<"c RAT CHECK ERROR"<<endl;
            return false;
          };

          c = s.add_clause(c);

          if (s.propagate_units(out) == CONFLICT) {
            out<<"c PROVED CONFLICT BY UNIT PROPAGATION"<<endl;
            return true;
          }
        }
      }

      out<<"c PROOF CLAUSES CHECKED BUT NO CONFLICT"<<endl;
      return false;
    }





};









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

  ostream &out = cout;

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

