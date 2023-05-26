#include <cstdlib>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <deque>
#include <algorithm>
#include <cassert>
#include <functional>
#include <limits>
#include <unordered_map>
#include <cstdint>
#include <thread>
#include <atomic>
#include <chrono>
#include <limits>
#include <cmath>


using namespace std;

size_t cfg_out_buf_size_threshold = 16*1024;
bool cfg_display_warnings = true;


void fail(string msg = "") {
  clog<<"c FAILED";
  if (msg!="") clog<<": "<<msg;
  clog<<endl;
  clog<<"s ERROR"<<endl;
  exit(1);
}

void warn(string msg) {
  if (cfg_display_warnings) clog<<"c WARNING: "<<msg<<endl;
}


struct lit_t {
  int32_t val;

  explicit operator bool() {return val!=0;}
};
struct cid_t {
  int32_t val;
  explicit operator bool() {return val!=0;}
};

class Bin_Parser {
  ifstream in;

  char buffer[64*1024];

public:
  Bin_Parser (string name) : in(name,ios::in | ios::binary) {
    in.imbue(locale::classic());
    in.exceptions(in.badbit | in.failbit);
    in.rdbuf()->pubsetbuf(buffer,sizeof buffer);
  }

  ~Bin_Parser() {
    in.close();
  }

  template<typename R> R parse();

  // Parse unsigned encoding of id (apparently used in binary lrat at certain positions)
  cid_t parse_unsigned_id();

//   char parse_char();
//   unsigned parse_uint();
//   int parse_int();
//

  bool is_eof() { return in.peek()<0; }

};

template<> inline char Bin_Parser::parse<char>() {
  int c = in.get();
  assert(c>=0); // Assuming exception on fail!
  return (char)c;
}


template<> inline uint32_t Bin_Parser::parse<uint32_t>() {
  uint32_t res=0;
  uint32_t shift=0;

  int c;
  do {
    c = in.get();
    assert(c>=0); // Assuming exception on fail!
    res |= (c & 0x7F) << shift;  // TODO: Overflow check!
    shift += 7;
  } while ((c&0x80) != 0);

  return res;
}


template <> inline int32_t Bin_Parser::parse<int32_t>() {
  uint32_t ul = parse<uint32_t>();

  int32_t res;

  if ((ul&0x01) != 0) res=-(static_cast<int32_t>(ul>>1));
  else res=static_cast<int32_t>(ul>>1);

  return res;
}

template <> inline lit_t Bin_Parser::parse<lit_t>() { return {parse<int32_t>()}; }

// There are two kind of ids in the proofs:
//   - the ids to label clauses are written as unsigned because they cannot be
//   negative
//   - the ids in justification chains are written as signed integers, because that can be used to
//   express RAT additions
template <> inline cid_t Bin_Parser::parse<cid_t>() { return {parse<int32_t>()}; }

cid_t Bin_Parser::parse_unsigned_id() {
  uint32_t ul = parse<uint32_t>();

  if (ul > INT32_MAX) fail("unsigned id parser: overflow");

  return { (int32_t)ul };
}



class Lrat_Parser {
  Bin_Parser bp;



  vector<lit_t> literals; // Current literals
  vector<cid_t> ids; // Current ids
  cid_t this_id; // This item id, if applicable
  bool addition;

  template<typename R> void rd_until_zero(vector<R> &v) {
    v.clear();

    while (true) {
      R d = bp.parse<R>();

      if (!d) break;
      v.push_back(d);

    }
  }

public:
  cid_t get_this_id() {return this_id;}
  int is_addition() {return addition;}

  vector<lit_t> &get_literals() {return literals;}
  vector<cid_t> &get_ids() {return ids;}

public:
  void rd_line() {
    char opr = bp.parse<char>();
    literals.clear();
    ids.clear();
    this_id={-1};

    if (opr=='a') {
      addition=true;
      this_id = {bp.parse_unsigned_id()}; // ids at this position are encoded as unsigned values
      rd_until_zero(literals);
      rd_until_zero(ids);
    } else if (opr=='d') {
      addition=false;
      rd_until_zero(ids);
    } else {
      fail(string("Unknown op-id: ") + to_string((int)opr));
    }

  }

  bool is_eof() {
    return bp.is_eof();
  }


public:
  Lrat_Parser(string name) : bp(name), literals(), ids(), this_id({-1}), addition(false) {}

};


class Binary_Writer {
private:
  vector<int32_t> data;
  vector<ostream::char_type> buf;
  ofstream out;

  inline void put32(int32_t x) {
    buf.push_back(x);
    buf.push_back(x >> 8);
    buf.push_back(x >> 16);
    buf.push_back(x >> 24);
  }

  inline void flush_buf() {
    if (buf.size()) {
      out.write(buf.data(),buf.size());
      buf.clear();
    }
  }

public:
  Binary_Writer(string name) :data(), buf(), out() {
    out.open(name, ios_base::out | ios_base::binary  | ios_base::trunc);
    out.imbue(locale::classic());
    out.exceptions(out.badbit | out.failbit);
    out.flush();
  }

  ~Binary_Writer() {
    write_out();
    flush_buf();
    out.close();
  }

  template<typename T> void wr(T d);

  template<typename I> void wr_range(I begin, I end);
  template<typename I> void wr_range0(I begin, I end);
  template<typename R> void wr_all_0(R &rng);

  inline void wr0();


  inline void write_out() {
    // Write in reverse
    size_t i=data.size();

    while (i) {
      --i;
      put32(data[i]);
      if (buf.size()>=cfg_out_buf_size_threshold) flush_buf();
    }

    flush_buf();
    out.flush();
  }





};

template<> void Binary_Writer::wr<int32_t>(int32_t d) {data.push_back(d);}
template<> void Binary_Writer::wr<lit_t>(lit_t d) {data.push_back(d.val);}
template<> void Binary_Writer::wr<cid_t>(cid_t d) {data.push_back(d.val);}

inline void Binary_Writer::wr0() {wr<int32_t>(0);}

template<typename I> void Binary_Writer::wr_range(I begin, I end) {
  for (I i=begin; i!=end;++i) wr(*i);
}

template<typename I> void Binary_Writer::wr_range0(I begin, I end) {
  wr_range(begin,end);
  wr0();
}

template<typename R> void Binary_Writer::wr_all_0(R &r) {
  for (auto i : r) wr(i);
  wr0();
}



class Ascii_Writer {
private:
  ofstream out;

  bool has_space = true;

  // Benchmarks showed that this is IO-bound, even when adjusting size of out.rdbuf(). Thus, implementing custom buffering :(
  ostringstream buffer;

  size_t flush_count = 0; // Implementing proper byte-based heuristics with buffer.tellp() costs 10% speed :(

  void flush_buffer() {
    out<<buffer.str();
    buffer.str("");
    flush_count=0;
  }

  inline void check_flush_buffer() {
    if (flush_count++ > cfg_out_buf_size_threshold) flush_buffer();
  }

  inline void write_str(string s) {
    buffer<<s;
    check_flush_buffer();
  }

  inline void write_char(char c) {
    buffer<<c;
    check_flush_buffer();
  }

  inline void prep_token() {
    if (!has_space) write_char(' ');
    has_space=false;
  }


  inline void write_int(int32_t i) {
    prep_token();
    buffer<<i;
    check_flush_buffer();
  }


public:
  inline void write_endl() {write_char('\n'); has_space=true; }



public:
  Ascii_Writer(string name) : out(), buffer() {
    out.open(name, ios_base::out | ios_base::trunc);
    out.imbue(locale::classic());
    out.exceptions(out.badbit | out.failbit);
    out.flush();
  }

  ~Ascii_Writer() {
    flush_buffer();
    out.close();
  }


  inline void write_id(cid_t id) {write_int(id.val);}

  inline void write_lit(lit_t l) {write_int(l.val);}

  inline void write_token(string s) {
    prep_token();
    write_str(s);
  }

  inline void write_clause(vector<lit_t> &clause) {
    for (auto i : clause) write_lit(i);
    write_int(0);
  }

  inline void write_ids(vector<cid_t> &ids) {
    for (auto i : ids) write_id(i);
    write_int(0);
  }



};


/*
 Questions:
   gaps in ids!?
    no problem!

   binary or ASCII lrat?

   does it make sense to natively support lrat?

   how big do lrat-files get? how important is deletion info?

*/

enum item_type : int32_t {
  INVALID = 0,      ///< Unused
  UNIT_PROP = 1,    ///< Unit propagation item. Contains a zero-terminated list of unit-clause IDs: <code>id* 0</code>
  DELETION = 2,     ///< Deletion item. Contains a zero-terminated list of clause IDs to be deleted: <code>id* 0</code>
  RUP_LEMMA = 3,    ///< Lemma with RUP-certificate. Contains the new ID for the lemma, the clause, a list of unit clause IDs, and a conflict clause: <code>id lit* 0 id* 0 id</code>
  RAT_LEMMA = 4,    /**< Lemma with RAT-certificate.
    Contains the pivot-literal, the new ID for the lemma, a list of unit-clauses IDs,
    and a list of candidate proofs: <code> lit id lit* 0 id* 0 (id id* 0 id)* 0</code>

    Each candidate proof contains the ID of the candidate lemma, a list of unit clause IDs, and a conflict clause ID.
  */
  CONFLICT = 5,     ///< Indicates a root conflict. Contains the ID of the conflict clause: <code>id</code>
  RAT_COUNTS = 6    ///< Item to store RAT literal counts. Contains a list of pairs of literals and positive numbers: <code>(lit num)* 0</code>
};


template<> void Binary_Writer::wr<item_type>(item_type d) {data.push_back(d);}



class Grat_Writer {

  Ascii_Writer lem;
  Binary_Writer prf;

public:
  Grat_Writer(string lname, string pname) : lem(lname), prf(pname) {};

  void write_dummy_rat_counts() {
    prf.wr(RAT_COUNTS);
    prf.wr0();
  }

  void write_deletions(vector<cid_t> &dels) {
    prf.wr(DELETION);
    prf.wr_all_0(dels);
  }

  // Note: last element of units-vector is conflict clause!
  void write_rup(cid_t id, vector<lit_t> &clause, vector<cid_t> &units) {
    prf.wr(RUP_LEMMA);
    prf.wr(id);
    if (units.size() == 0) fail("empty unit-propagation sequence, for id: " + to_string(id.val));

    prf.wr_range0(units.begin(), units.end()-1);
    prf.wr(units.back());

    lem.write_clause(clause); lem.write_endl();
  }

  void write_unit_prop(vector<cid_t> &units) {
    prf.wr(UNIT_PROP);
    prf.wr_all_0(units);
  }

  template<typename I> void write_unit_prop(I begin, I end) {
    prf.wr(UNIT_PROP);
    prf.wr_range0(begin,end);
  }

  void write_conflict(cid_t id) {
    prf.wr(CONFLICT);
    prf.wr(id);
  }

};

class Lrat_Grat_Xlator {

  Lrat_Parser lrat;
  Grat_Writer wr;

  bool had_conflict = false;

  void xlate_lrat_line() {
    if (lrat.is_addition()) {
      // Check for RAT-clause
      for (auto i : lrat.get_ids()) {
        if (i.val<0) fail("RAT clauses not yet supported. id " + to_string(lrat.get_this_id().val));
      }

      // Check if conflict clause
      if (lrat.get_literals().size()) { // Normal addition
        wr.write_rup(lrat.get_this_id(),lrat.get_literals(),lrat.get_ids());
      } else { // Conflict
        if (lrat.get_ids().size() == 0) fail("empty unit-propagation sequence at conflict clause, for id: " + to_string(lrat.get_this_id().val));

        wr.write_unit_prop(lrat.get_ids().begin(), lrat.get_ids().end()-1);
        wr.write_conflict(lrat.get_ids().back());

        had_conflict=true;
      }

    } else {
      wr.write_deletions(lrat.get_ids());
    }
  }


public:
  Lrat_Grat_Xlator(string lratf, string lemf, string prff) : lrat(lratf), wr(lemf,prff) {

    size_t lines=0;
    wr.write_dummy_rat_counts();

    while (!lrat.is_eof()) {
      if (had_conflict) {
        warn("Ignoring content after conflict clause");
        break;
      }

      lrat.rd_line();
      xlate_lrat_line();

      ++lines;
    }

    if (!had_conflict) {
      warn("No root conflict in lrat proof. (Generated GRAT proof is invalid)");
    }

    clog<<"c Translated "<<lines<<" lrat lines"<<endl;

  }


};


class Lrat_Lrat_Xlator {

  Lrat_Parser lrat;
  Ascii_Writer wr;

  cid_t last_id = {1}; // Just putting something here initially

  void xlate_lrat_line() {
    if (lrat.is_addition()) {
      wr.write_id(lrat.get_this_id());
      wr.write_clause(lrat.get_literals());
      wr.write_ids(lrat.get_ids());

      wr.write_endl();

      last_id = lrat.get_this_id();
    } else {
      wr.write_id(last_id);
      wr.write_token("d");
      wr.write_ids(lrat.get_ids());
      wr.write_endl();
    }
  }


public:
  Lrat_Lrat_Xlator(string inf, string outf) : lrat(inf), wr(outf) {

    size_t lines=0;

    while (!lrat.is_eof()) {
      lrat.rd_line();
      xlate_lrat_line();

      ++lines;
    }

    clog<<"c Translated "<<lines<<" lrat lines"<<endl;
  }


};


void cnv_to_grat(string lratf, string lemf, string prff) {
  Lrat_Grat_Xlator(lratf,lemf,prff);
}

void cnv_to_lrat(string lratf, string outf) {
  Lrat_Lrat_Xlator(lratf,outf);
}

void read_lrat_dummy(string lratf) {
  Lrat_Parser lrat(lratf);

  size_t lines=0;

  while (!lrat.is_eof()) {
    lrat.rd_line();
    ++lines;
  }

  clog<<"c Read "<<lines<<" lrat lines"<<endl;
}

int main(int argc, char **argv) {

  if (argc==2) {
    clog<<"c Only reading binary lrat (for benchmarking)"<<endl;
    read_lrat_dummy(argv[1]);
  } else if (argc==3) {
    clog<<"c Converting binary lrat to ASCII lrat"<<endl;
    cnv_to_lrat(argv[1],argv[2]);
  } else if (argc == 4) {
    clog<<"c Converting binary lrat to split grat"<<endl;
    cnv_to_grat(argv[1],argv[2],argv[3]);
  } else {
    cerr<<"c Usage: "<<endl;
    cerr<<"c   lrat_grat_cnv <lrat-in-file> <lemma-out-file> <proof-out-file>  -- convert to grat "<<endl;
    cerr<<"c   lrat_grat_cnv <lrat-in-file> <lrat-out-file>  -- convert to ASCII lrat"<<endl;
    cerr<<"c   lrat_grat_cnv <lrat-in-file>   -- just read ASCII lrat"<<endl;
    fail("c Invalid command line arguments");
  }

  return 0;
}


