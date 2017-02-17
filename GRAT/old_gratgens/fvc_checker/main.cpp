#include <iostream>
#include <cstdlib>
#include <fstream>
#include <vector>
#include <algorithm>
#include <cassert>
#include <limits>
#include <unordered_map>
#include <cstdint>

using namespace std;

typedef intptr_t Lit;


int64_t stat_cm_looked_at=0;
int64_t stat_cm_deleted=0;


int64_t stat_taut_lemmas=0;
int64_t stat_rup_lemmas=0;
int64_t stat_rat_lemmas=0;



template <typename MW> void error(const MW &mw) {
  mw(cerr);
  exit(1);
}

void error(const char *msg) {
  error([msg](ostream &out) {out<<msg<<endl;});
}


void error() {error("UNSPECIFIED ERROR");}

template<typename MW> void parser_error(const MW &mw, istream &in) {
  error([&in,&mw](ostream &out) {
    in.clear();
    out<<"Parser error ("<<in.tellg()<<"): ";
    mw(out);

    char s[30];
    in.getline((char*)&s,29);
    out<<(char*)&s<<endl;
    in.getline((char*)&s,29);
    out<<(char*)&s<<endl;
    in.getline((char*)&s,29);
    out<<(char*)&s<<endl;
  });



}

void parser_error(const char *msg, istream &in) {
  parser_error([msg](ostream &out) {out<<msg<<endl;},in);
}


class Clause {
  public:
    inline Lit *first() {return reinterpret_cast<Lit*>(this);}

};

struct CPos {
  size_t pos;

  inline bool operator==(const CPos &p) {return p.pos==pos;}
  inline bool operator!=(const CPos &p) {return p.pos!=pos;}

  static const CPos NO_POS;
};

const CPos CPos::NO_POS = CPos{numeric_limits<size_t>::max()};

class Clausedb {
  private:
    vector<Lit> db;

  public:
    Clausedb() :db() {};

    inline void append(Lit l) {db.push_back(l);}
    inline CPos current_pos() {return CPos{db.size()};}

    inline Clause* clause_at(CPos pos) {return reinterpret_cast<Clause*>(db.data() + pos.pos); }



};

class Assignment {
  private:
    vector<int8_t> A;

    inline size_t index(Lit l) {return static_cast<size_t>(l>0?2*l:2*-l+1);}

  public:
    Assignment() : A() {}


    inline bool is_false(Lit l) {
      size_t i=index(l);
      return i<A.size()?A[i]:false;
    }

    inline bool is_true(Lit l) {return is_false(-l);}

    inline void set_false(Lit l) {
      size_t i=index(l);
      if (i>=A.size()) {A.resize(i+1);}
      A[i]=true;
    }

    inline void unset_false(Lit l) {
      A[index(l)] = false;
    };

};

struct CId {
  size_t id;

  static const CId NO_ID;

  inline bool operator==(const CId &p) {return p.id==id;}
  inline bool operator!=(const CId &p) {return p.id!=id;}
};

const CId CId::NO_ID = CId{numeric_limits<size_t>::max()};

class Clausemap {
  private:
    vector<CPos> cmap;

  public:
    Clausemap() : cmap() {
      cmap.reserve(3000000);
    }

    inline CId add_clause(CPos pos) {
      cmap.push_back(pos);
      return CId{cmap.size()-1};
    }

    inline void add_clause(CId id, CPos pos) {
      if (cmap.size()<=id.id) cmap.resize(id.id+1,CPos::NO_POS);
      if (cmap[id.id] != CPos::NO_POS) error("Duplicate id");
      cmap[id.id] = pos;
    }

    inline CPos lookup(CId id) {
      if (id.id>=cmap.size()) error("Invalid clause");
      CPos r = cmap[id.id];
      if (r==CPos::NO_POS) error("Deleted clause");
      return r;
    }

    void del_clause(CId id) {
      if (id.id>=cmap.size()) error("Invalid clause");
      cmap[id.id] = CPos::NO_POS;
    }

    inline CId next(CId id) {
      size_t i=id.id + 1;

      while (i<cmap.size() && cmap[i]==CPos::NO_POS) {++i; ++stat_cm_deleted;}
      ++stat_cm_looked_at;

      return CId{i};
    }

    inline CId first() {
      size_t i=0;
      while (i<cmap.size() && cmap[i]==CPos::NO_POS) ++i;
      return CId{i};
    }

    inline CId cid_end() {return CId{cmap.size()};}



};


inline ostream& operator<< (ostream &out, const CId &id) {
  out<<id.id+1;
  return out;
}

void error_cid(const char *msg, CId cid) {
  error([msg,&cid](ostream &out) {out<<msg<<" (Clause "<<cid<<")"<<endl;});
}



class Checker {
  private:
    Clausedb &db;
    Assignment A;
    Clausemap CM;

    vector<Lit> rup_trail;
    vector<Lit> rat_trail;
    Lit reslit=0;
    CId next_rat_id = CId();
    CPos pending_clause = CPos::NO_POS;
    CId pending_id = CId::NO_ID;

    enum {
      CNF,
      PROOF,
      RUP,
      RAT1,
      RAT2,
      QED
    } state = CNF;



    void analyze_added_clause(CPos pos) {
      // Analyze for conflict or unit
      Clause *c=db.clause_at(pos);
      Lit ul=0;
      for (Lit *l=c->first();*l;++l) {
        if (A.is_true(*l)) {
          // Tautology
          return;
        } else if (!A.is_false(*l)) {
          if (ul) return; // Normal clause
          ul=*l;
        }
      }

      if (ul) A.set_false(-ul); // Unit clause
      else { // Added conflict clause
        state=QED;
      }
    }

    Lit get_unit_lit(CId cid) {
      Clause *c=db.clause_at(CM.lookup(cid));

      Lit ul=0;

      for (Lit *l=c->first();*l;++l) {
        if (A.is_true(*l)) error_cid("No unit (TAUT)",cid);
        if (!A.is_false(*l)) {
          if (ul) error_cid("No unit (2-UNDEC)",cid);
          ul=*l;
        }
      }

      if (!ul) error_cid("No unit (CONFLICT)",cid);
      return ul;
    }

    void assert_conflict(CId id) {
      Clause *cc = db.clause_at(CM.lookup(id));

      for (Lit *l=cc->first();*l;++l)
        if (!A.is_false(*l)) error_cid("No conflict clause",id);
    }

    inline void replay_units_tr(const vector<CId> &units, vector<Lit> &trail) {
      for (CId id : units) {
        Lit l = -get_unit_lit(id);
        A.set_false(l);
        trail.push_back(l);
      }
    }

    inline void find_rat_id() {
      while (next_rat_id!=CM.cid_end()) {
        Clause *c=db.clause_at(CM.lookup(next_rat_id));
        // Check that clause contains literal and is no taut
        bool contains_lit=false;
        Lit blocked=0;
        for (Lit *l=c->first();*l;++l) {
          contains_lit = contains_lit || (*l==reslit);
          if (*l != reslit && A.is_true(*l) && !blocked) {
            //cerr<<"Clause "<<next_rat_id<<" blocked b/c literal "<<*l<<endl;
            blocked=*l;
            //goto next_id;
            // TODO: Go back to code that breaks early here!
          }
        }

        if (contains_lit) {
          if (blocked) {
            //cerr<<"Clause "<<next_rat_id<<" blocked b/c literal "<<blocked<<endl;
          } else break;
        }

        //next_id:
          next_rat_id = CM.next(next_rat_id);

      }
    }


    inline void accept_pending_clause() {
      CM.add_clause(pending_id,pending_clause);
      analyze_added_clause(pending_clause);
    }

  public:
    Checker(Clausedb &_db) :
      db(_db),
      A(),
      CM(),
      rup_trail(),
      rat_trail()
    {}


    inline bool is_QED() {return state==QED;}

    void start_proof() {
      if (state!=CNF) error("Proof must be started from CNF");
      state=PROOF;
    }

    void add_cnf_clause(CPos pos) {
      if (state==CNF) {
        pending_clause=pos;
        CM.add_clause(pending_clause);
        analyze_added_clause(pending_clause);
      } else error("Unexpected add-cnf-clause");
    }

    void add_prf_clause(CId id, CPos pos) {
      if (state==PROOF) {
        pending_clause=pos;
        pending_id=id;

        // Initialize RUP and check for tautology
        rup_trail.clear();
        Clause *c=db.clause_at(pos);
        for (Lit *l=c->first();*l;++l) {
          if (A.is_true(*l)) { // Accept tautology
            for (auto l : rup_trail) A.unset_false(l);
            accept_pending_clause();
            ++stat_taut_lemmas;
            return;
          }
          if (!A.is_false(*l)) {
            A.set_false(*l);
            rup_trail.push_back(*l);
          }
        }
        state=RUP;
        return;
      } else error_cid("Unexpected add-prf-clause",id);
    }

    void delete_clause(CId id) {
      if (state==CNF || state==PROOF) {
        CM.del_clause(id);
      } else error("Unexpected delete-clause");
    }

    void unit_prop_conf(const vector<CId> &units, CId cclause) {
      if (state==CNF || state==PROOF) {
        // Follow units
        for (CId id : units) A.set_false(-get_unit_lit(id));
        assert_conflict(cclause);
        state=QED;
      } else if (state==RUP) {
        // Follow units
        replay_units_tr(units,rup_trail);
        assert_conflict(cclause);
        for (auto l : rup_trail) A.unset_false(l);
        state=PROOF;
        accept_pending_clause();
        ++stat_rup_lemmas;

      } else error("Unexpected uprop-conf");
    }


    void unit_prop_noconf(const vector<CId> &units) {
      if (state==CNF || state==PROOF) {
        for (CId id : units) A.set_false(-get_unit_lit(id));
      } else if (state==RUP) {
        replay_units_tr(units,rup_trail);
        // Initialize rat proof
        state=RAT1;
      } else error("Unexpected uprop-noconf");
    }


    void set_rat_lit(Lit l) {
      if (state==RAT1) {
        reslit=-l;

        //cerr<<"Starting RAT check on literal "<<l<<endl;

        next_rat_id=CM.first(); find_rat_id();

        if (next_rat_id == CM.cid_end()) {
          for (auto l : rup_trail) A.unset_false(l);
          //cerr<<"c RAT: No clauses contain literal "<<reslit<<endl;

          state=PROOF;
          accept_pending_clause();

          ++stat_rat_lemmas;
        } else {
          //cerr<<"Expecting RAT-proof for clause "<<next_rat_id<<endl;
          state=RAT2;
        }
      } else error("Unexpected set-rat-lit");
    }

    void rat_clause(CId id, const vector<CId> &units, CId cclause) {
      if (state==RAT2) {
        if (id!=next_rat_id) {error([id, this](ostream &out){out<<"Wrong rat id "<<id<<" expected "<<next_rat_id;});}

        rat_trail.clear();

        Clause *c=db.clause_at(CM.lookup(id));
        for (Lit *l=c->first();*l;++l) {
          if (!A.is_false(*l)) {
            A.set_false(*l);
            rat_trail.push_back(*l);
          }
        }


        replay_units_tr(units,rat_trail);
        assert_conflict(cclause);
        for (auto l : rat_trail) A.unset_false(l);

        next_rat_id = CM.next(next_rat_id); find_rat_id();

        if (next_rat_id == CM.cid_end()) {
          //cerr<<"RAT proof finished"<<endl;
          for (auto l : rup_trail) A.unset_false(l);
          state=PROOF;
          accept_pending_clause();
          ++stat_rat_lemmas;
        } else {
          //cerr<<"Next RAT-proof for clause "<<next_rat_id<<endl;
        }


      } else error_cid("Unexpected rat-clause",id);
    }


};




class Main {
  public:
    Clausedb db;
    Checker checker;

    vector<CId> units;

  public:
    Main() : db(), checker(db), units() {}


    void skip_ws(istream &in) {
      while (!in.eof()) {
        in>>ws;
        if (in.peek() == 'c') in.ignore(numeric_limits<streamsize>::max(), '\n');
        else break;
      }
    }

    inline bool is_eof(istream &in) {skip_ws(in); return in.eof();}

    inline char peek(istream &in) {skip_ws(in); return in.peek();} // FIXME: Casting -1 to char on EOF

    void expect(istream &in, char c) {
      if (peek(in)!=c) parser_error([this,&in,c](ostream &out) {out<<"Expected "<<c<<"  but got "<<peek(in)<<endl;},in);
      in.ignore(1);
    }

    Lit parse_lit(istream &in) {
      skip_ws(in);
      Lit l;
      in>>l;
      if (!l) error("Expected literal");
      return l;
    }

    CPos parse_clause(istream &in) {
      skip_ws(in);
      Lit l;
      auto cpos = db.current_pos();
      do {
        in>>l;
        db.append(l);
      } while (l);
      return cpos;
    }

    CId parse_cid(istream &in) {
      size_t id;
      in>>id;
      if (id==0)
        parser_error("Expected id",in);
      id--;
      return CId{id};
    }

    void parse_units(istream &in) {
      units.clear();
      while (true) {
        if (peek(in)=='0' || peek(in)=='C') break;
        units.push_back(parse_cid(in));
      }
    }

    void skip_headers(istream &in) {
      while (true) {
        char c = peek(in);
        if (c=='p' || c=='o') in.ignore(1);
        else break;
      }
    }


    void parse_cnf(istream &in) {
      skip_headers(in);
      while (!is_eof(in)) {
        checker.add_cnf_clause(parse_clause(in));
      }
    }

    void parse_proof(istream &in) {
      checker.start_proof();
      skip_headers(in);

      size_t items=0;
      size_t intv_last=0;

      while (!is_eof(in)) {
        items++;
        if (items-intv_last > 1000000) {
          intv_last=items;
          cerr<<".";
          cerr.flush();
        }

        char c = peek(in);

        if (c=='d') {
          in.ignore(1);
          checker.delete_clause(parse_cid(in));
        } else if (c=='U') {
          in.ignore(1);
          parse_units(in);
          items+=units.size();
          if (peek(in)=='C') {
            in.ignore(1);
            checker.unit_prop_conf(units,parse_cid(in));
          } else if (peek(in)=='0') {
            in.ignore(1);
            checker.unit_prop_noconf(units);
          } else error("expected C or 0");
        } else if (c=='C') {
          in.ignore(1);
          units.clear();
          checker.unit_prop_conf(units,parse_cid(in));
        } else if (c=='R') {
          in.ignore(1);
          checker.set_rat_lit(parse_lit(in));
        } else if (c=='r') {
          in.ignore(1);
          CId id = parse_cid(in);
          units.clear();

          if (peek(in)=='U') {
            in.ignore(1);
            parse_units(in);
            items+=units.size();
          }
          expect(in,'C');
          CId cclause = parse_cid(in);
          checker.rat_clause(id,units,cclause);
        } else {
          CId id = parse_cid(in);
          checker.add_prf_clause(id,parse_clause(in));
        }
      }
    }

};



void print_usage() {
  cout<<"Usage fvc_checker <dimacs-file> <proof-file>"<<endl;
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

  Main p;


  cout<<"Parsing cnf"<<endl;
  p.parse_cnf(cnf);
  cout<<"Parsing+checking proof"<<endl;
  p.parse_proof(prf);
  cout<<"Done"<<endl;

  cout<<"stat_cm_looked_at = "<<stat_cm_looked_at<<endl;
  cout<<"stat_cm_deleted = "<<stat_cm_deleted<<endl;

  cout<<"stat_taut_lemmas = "<<stat_taut_lemmas<<endl;
  cout<<"stat_rup_lemmas = "<<stat_rup_lemmas<<endl;
  cout<<"stat_rat_lemmas = "<<stat_rat_lemmas<<endl;


  if (p.checker.is_QED()) {
    cout<<"s CERTIFIED UNSAT"<<endl;
  } else {
    cout<<"ERROR"<<endl;
  }
}

