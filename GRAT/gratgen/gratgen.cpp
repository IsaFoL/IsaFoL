/** @file 
 *  GRATgen main source file.
 *
 *  @author Peter Lammich
 */

/** \mainpage

  <p>
  GRATgen is a tool to check DRAT unsatisfiability certificates and convert them into GRAT certificates.
  
  <p>
  Although GRATgen checks the DRAT certificate during conversion (and also has a check-only mode), 
  its main usage is to generate GRAT certificates which are then checked against the original formula 
  by a _formally verified_ checker.
  
 
  <p>
  
  @author Peter Lammich
  
    all rights reserved. Some ideas borrowed from Marijn Heule's [DRAT-trim](https://www.cs.utexas.edu/~marijn/drat-trim/) tool.

  ## Usage
  
      gratgen cnf-file drat-file [options]
  
    invoke gratgen without arguments to see a list of available options.
    
    
  
  
  ## Features

    * Backwards checking with core-first unit propagation
    * Generation of trimmed GRAT certificates
    * Parallel checking

  ## Lacking features:

    Initially, GRATgen started as a reimplementation of [DRAT-trim](https://www.cs.utexas.edu/~marijn/drat-trim/). 
    Find below a list of features that DRAT-trim has, but GRATgen does not support:

    
    * Forward checking (Could be added, but would probably mess up some code)
    * Binary proof format (Can easily be added)
    * Optimal deletion placement (Probably not important for GRAT-certificate checking)

*/

/** ****************************************
 * @name Program configuration
 * Macros for static program configuration
 * @{
 ******************************************/

/** 
 * Define this to include statistic counters. 
 * 
 * @attention Use for debugging only: This will add properly synchronized statistic counters to some inner loops, and thus significantly slow down the checker!
 */
#ifdef WITH_DBG_STAT
#define WITH_DBG_STAT
#else
#define WITH_DBG_STAT
#undef WITH_DBG_STAT
#endif

/** 
 * Define this to get gperftools profiling. gperftools/profiler.h must be on include path!
 */
#ifdef WITH_PROFILING
#define WITH_PROFILING
#else
#define WITH_PROFILING
#undef WITH_PROFILING
#endif

///@}

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

#ifdef WITH_PROFILING
#include <gperftools/profiler.h>
#endif

#ifdef WITH_DBG_STAT
/// Only execute argument if statistics (::WITH_DBG_STAT) are enabled
#define DBG_STAT(X) X
#else
/// Only execute argument if statistics (::WITH_DBG_STAT) are enabled
#define DBG_STAT(X)
#endif



using namespace std;

/** **************************************************
 * @name Auxiliary global functions
 * Assorted collection of global helper functions.
 * @{
 *****************************************************/

/**
 * Abort checking with optional error message.
 */
void fail(string msg = "") {
  clog<<"FAILED";
  if (msg!="") clog<<": "<<msg;
  clog<<endl;
  exit(1);
}

/**
 * Set v[i]=data, resizing v as necessary. 
 */
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


/**
 * Measure timing of operation, and print timing message to log.
 * @param name name that is printed as operation name
 * @param op operation, invoked as op()
 * @param dp Pointer to store required time to, nullptr if no time to be stored
 * @param out Stream to print message to, clog by default
 * @returns return value of op()
 */
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

/**
 * Measure timing of operation, and print timing message to log. Specialized for op() returning void.
 * @param name name that is printed as operation name
 * @param op operation, invoked as op()
 * @param dp Pointer to store required time to, nullptr if no time to be stored
 * @param out Stream to print message to, clog by default
 */
template<typename T> void with_timing(string name, T op, chrono::milliseconds *dp = nullptr, ostream &out = clog) {
  out<<name<<" ..."; out.flush();
  auto t = chrono::steady_clock::now();
  op();
  auto d = chrono::steady_clock::now() - t;
  chrono::milliseconds dm = chrono::duration_cast<chrono::milliseconds>(d);
  if (dp) *dp=dm;
  out<<" "<< dm.count() <<"ms"<<endl; out.flush();
}

///@}


/** ****************************************
 * @name Variables and Literals
 * Types and functions for variables and literals.
 * 
 * As in the DIMACS format, variables are represented by positive integer numbers. 
 * Literals are represented by non-zero integers, negative numbers representing negated variables.
 * 
 * @{
 ******************************************/

/** Type of clause database entry */
typedef int cdb_t;
/** Type of literals */
typedef cdb_t lit_t;

/** Return variable of literal */
// TODO: size_t and int not necessarily as compatible as desired!
inline size_t var_of(lit_t l) {return static_cast<size_t>(abs(l));}

///@}

/** ****************************************
 * @name Run-time configuration
 * @{
 ******************************************/


bool cfg_core_first = true; ///< Do core-first unit propagation
bool cfg_ignore_deletion = false; ///< Ignore clause deletion items
bool cfg_no_grat = false; ///< Do not produce a GRAT certificate
bool cfg_assume_nodup = false; /**< Assume that clauses contain no duplicate literals. 
  @attention You're on your own if they do nevertheless! 
*/
bool cfg_show_progress_bar = true; ///< Display progress bar

///@}


/** ****************************************
 * @name Statistics
 * 
 * These statistics are collected during every run of the program.
 * @{
 ******************************************/

chrono::milliseconds stat_parsing_time(0);      /**< Time required for parsing formula and DRAT certificate */
chrono::milliseconds stat_checking_time(0);     /**< Time required for checking */
chrono::milliseconds stat_bwd_checking_time(0); /**< Part of checking time spent in backward pass */
chrono::milliseconds stat_writing_time(0);      /**< Time required to write out the certificate */
chrono::milliseconds stat_overall_time(0);      /**< Overall reqired (wall-clock) time */
chrono::milliseconds stat_overall_vrf_time(0);  /**< Part of overall time, excluding time for certificate writing */


size_t stat_itemlist_size(0); /**< Size of item-list in bytes */
size_t stat_pivots_size(0);   /**< Size of pivot map in bytes */
size_t stat_db_size(0);       /**< Size of clause database in bytes */

/// @}

/******************************************
 * Main Program
 ******************************************/

/** GRAT item types */
enum item_type : cdb_t {
  INVALID = 0,      ///< Unused
  UNIT_PROP = 1,    ///< Unit propagation item. Contains a zero-terminated list of unit-clause IDs: <code>ID* 0</code>
  DELETION = 2,     ///< Deletion item. Contains a single clause ID to be deleted: <code>id</code> TODO: Change to zero-terminated list of IDs!
  RUP_LEMMA = 3,    ///< Lemma with RUP-certificate. Contains the new ID for the lemma, the clause, a list of unit clause IDs, and a conflict clause: <code>id lit* 0 id* 0 id</code>
  RAT_LEMMA = 4,    /**< Lemma with RAT-certificate. 
    Contains the pivot-literal, the new ID for the lemma, a list of unit-clauses IDs, 
    and a list of candidate proofs: <code> lit id lit* 0 id* 0 (id id* 0 id)* 0</code> 
    
    Each candidate proof contains the ID of the candidate lemma, a list of unit clause IDs, and a conflict clause ID.
  */
  CONFLICT = 5,     ///< Indicates a root conflict. Contains the ID of the conflict clause: <code>id</code>
  RAT_COUNTS = 6    ///< Item to store RAT literal counts. Contains a list of pairs of literals and positive numbers: <code>(lit num)* 0</code>
};

/**
 * A relative position in the clause database. Used to point into the clause database during parsing phase, when the addresses of the stored data may still change.
 */
struct pos_t {
  size_t pos;           ///< Position wrt the start of the clause database
  pos_t() : pos(0) {};  ///< Initialize position to null
  explicit pos_t(size_t _pos) : pos(_pos) {}; ///< Initialize with a size_t, specifying the position
  
  operator bool() const {return pos!=0;}  ///< True if position is not null
  bool operator==(pos_t const&p) const {return pos == p.pos;} ///< Compare two positions
  
  /** The null position, used as a guard */
  static pos_t null;
};

pos_t pos_t::null = pos_t(0);

/**
 * An item on the trail.
 */
struct trail_item_t {
  /// The literal.
  lit_t l;
  /// Clause due to which this literal was set. nullptr for assumed literals.
  lit_t * reason;
  /// Marker flag used for collecting relevant clauses during conflict analysis.
  bool vmarked;
};

/**
 * Container class to store a mapping from literals to type T.
 */
template<typename T> class lit_map {
private:
  size_t max_var;
  vector<T> vec;
  T *m;
  
public:
  /**
   * Initialize with fixed variable size.
   * @param _max_var Maximum variable number.
   */
  lit_map(size_t _max_var = 0) : 
      max_var(_max_var)
    , vec(2*max_var + 1)
    , m(vec.data() + max_var)
    {}
  
  /**
   * Copy the mapping, and all values
   */
  lit_map(lit_map const &lm) : max_var(lm.max_var), vec(lm.vec), m(vec.data() + max_var)
  {}
  
  /**
   * Assignment, copying the mapping, and all values
   */
  lit_map &operator= (lit_map const &lm) {
    max_var = lm.max_var;
    vec=lm.vec;
    m = vec.data() + max_var;
    return *this;
  }

  /**
   * Resize to new maximal variable number, resetting existing mappings!
   * @param _max_var Maximum variable number
   */
  void resize_reset(size_t _max_var) {
    max_var = _max_var;
    vec.clear();
    vec.resize(2*max_var + 1);
    m = vec.data() + max_var;
  }
  
  /// Get reference to mapping for specified literal
  T &operator [](lit_t l) { assert(static_cast<size_t>(abs(l)) <= max_var); return m[l];}

  /// Get const reference to mapping for specified literal
  const T &operator [](lit_t l) const { assert(static_cast<size_t>(abs(l)) <= max_var); return m[l];}
  
  /// Get maximum variable number
  size_t get_max_var() const {return max_var;}
  
  /** Get smallest mapped literal. 
   * 
   * Used to iterate over all mapped literals:
   *    @code for (lit_t i=X.lbegin();i<X.lend();++i) ...} @endcode
   */
  lit_t lbegin() const {return -static_cast<lit_t>(max_var);}
  /** Get largest mapped literal plus one. 
   * 
   * Used to iterate over all mapped literals:
   *    @code for (lit_t i=X.lbegin();i<X.lend();++i) ...} @endcode
   */
  lit_t lend() const {return static_cast<lit_t>(max_var) + 1;}
  
};


/**
 * Stores the clauses and the certificate as an array of cdb_t items. 
 * 
 */
class ClauseDB {
private:
  vector<cdb_t> db;   // Stores 0-terminated clauses, in format "Id literals 0". Clause pointers always point to first literal.
  
public:
  ClauseDB() : db() {}
  /// Copies the clause database.
  ClauseDB(ClauseDB const &x) : db(x.db) {} 
  /// Assignment operator, copies the clause database.
  ClauseDB &operator=(ClauseDB const &x) {  
    db = x.db;
    return *this;
  };
  
  /**
   * Converts a relative position to a pointer into the current data.
   */
  lit_t *p2c(pos_t pos) {
    assert(pos<=db.size());
    return pos?db.data() + pos.pos:nullptr;
  }

  /**
   * @copydoc p2c()
   */
  lit_t const *p2c(pos_t pos) const {
    assert(pos<=db.size());
    return pos?db.data() + pos.pos:nullptr;
  }

  /**
   * Converts a relative position into an iterator
   */
  vector<cdb_t>::iterator p2i(pos_t pos) {
    assert(pos && pos<=db.size());
    return db.begin() + pos.pos;
  }
  
  /**
   * @copydoc p2i()
   */
  vector<cdb_t>::const_iterator p2i(pos_t pos) const {
    assert(pos && pos<=db.size());
    return db.begin() + pos.pos;
  }
  
  /**
   * Converts a pointer into a relative position.
   */
  pos_t c2p(lit_t *cl) const {
    if (cl) {
      assert(db.data()<=cl && cl <= db.data() + db.size());
      return pos_t(cl - db.data());
    } else return pos_t(0);
  }
  
  /**
   * Get the relative position of the next item to be added to the database.
   */
  pos_t current() const {return pos_t(db.size());}
  
  /**
   * Appends a literal to the clause database. 
   * 
   * This invalidates all pointers and iterators, but preserves relative positions.
   */
  void append(lit_t l) {
    db.push_back(l);
  }
  
  /**
   * Remove everything from (including) the specified positon onwards
   */
  void shrink_to(pos_t pos) { assert(pos.pos <= current().pos); db.resize(pos.pos); }
  /**
   * @copydoc shrink_to()
   */
  void shrink_to(vector<cdb_t>::iterator end) { assert(end >= db.begin() && end<=db.end()); db.erase(end,db.end()); }

  /**
   * Get a const reference to the internal vector storing the data.
   */
  vector<cdb_t> const &get_db() const {return db;}
  
  ///@copydoc get_db() const
  vector<cdb_t> &get_db() {return db;}
};

/** @page pg_clause_format Internal storage of clauses
 * 
 *  Clauses are stored as a zero terminated string of lit_t, and referenced to by a lit_t* to the first literal.
 * 
 *  Moreover, the cdb_t before directly before the first literal of the clause contains the clause id, which is to be interpreted as an unsigned integer.
 *  The function clid() is used to access the id of a clause.
 * 
 *  If a clause is stored in the two-watched literals data structure, the first two literals of the clause are the watched literals, and 
 *  can be accessed with clw1() and clw2().
 */

/**
 * Get the id of a clause. 
 * 
 * @see @ref pg_clause_format
 * @relates ClauseDB
 */
inline size_t clid(lit_t *cl) {assert(cl); return static_cast<size_t>(cl[-1]);}
/**
 * Get the first watched literal of a clause.
 * 
 * @see @ref pg_clause_format
 * @relates ClauseDB
 */
inline lit_t &clw1(lit_t *cl) {assert(cl && cl[0]!=0 && cl[1]!=0); return cl[0]; }
/**
 * Get the second watched literal of a clause.
 * 
 * @see @ref pg_clause_format
 * @relates ClauseDB
 */
inline lit_t &clw2(lit_t *cl) {assert(cl && cl[0]!=0 && cl[1]!=0); return cl[1]; }

/**
 * A certificate item.
 * 
 * Certificate items point to positions in the clause database. 
 * The parser will initially build a list of all items encountered in the DRAT file (i.e. lemmas and deletions).
 * 
 * Later, items may be erased, which means that they will be ignored for a proof. For example, the forward pass will erase tautologies.
 * 
 * Finally, during the forward pass, items are associated to a position in the trail. During the backwards pass, this is then used for rolling back the trail.
 */
class item_t {
private:
  pos_t pos;      // Position of referenced clause (added or deleted clause), null if erased
  size_t trpos;   // [Position on forward trail + 1, 0 if not unit] | del-flag

public:
  /// Construct item at specified position in clause database.
  item_t(bool _deletion, pos_t _pos) : pos(_pos), trpos(_deletion?1:0) {}
  
  /// Check if item is erased.
  bool is_erased() const {return !pos;}
  /// Erase item
  void erase() {pos=pos_t::null;}

  /** 
   * Check if this is a deletion item. 
   * 
   * @pre Item is not erased.
   */
  bool is_deletion() const {assert(!is_erased()); return trpos&0x1;}
  
  /**
   * Get position of item.
   * 
   * @pre Item is not erased.
   */
  pos_t get_pos() const {assert(!is_erased()); return pos;}

  /**
   * Check if item is associated to a trail position
   */
  bool has_tr_pos() const {assert(!is_erased()); return trpos>>1!=0;}
  
  /**
   * Get associated trail position
   *
   * @pre Item is not erased.
   */
  size_t get_trpos() const {assert(has_tr_pos()); return (trpos>>1) - 1; }
  /**
   * Set associated trail position
   * 
   * @pre Item is not erased.
   */
  void set_trpos(size_t _trpos) {assert(!is_erased()); trpos = ((_trpos + 1)<<1) | (trpos&0x1);}
  
  
};


class Parser;
class Synch_Data;

/**
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
  
  /** Do initializations after parsing is completed. Called by friend Parser.
   * 
   * @see @ref Object_Lifetimes
   */
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
  /// Standard constructor
  Global_Data() : db(), pivots(), items(), fwd_trail() {}

  /// Get associated clause database
  ClauseDB &get_db() {return db;}

  /// Get maximum number of variables
  size_t get_max_var() const {return max_var;}
  /// Get number of clauses
  size_t get_num_clauses() const {return num_clauses;}
  
  /// Check whether we are in after-parsing phase
  bool is_after_parsing() const {return after_parsing;}
  
  /// Get the pivot element associated to a clause
  lit_t get_pivot(lit_t *cl) const {assert(cl); return pivots[clid(cl)];}
  
  /// Get the first item of the DRAT certificate
  size_t get_fst_prf_item() const {return fst_prf_item;}
  /// Get the total number of items
  size_t get_num_items() const {return items.size();}
  /// Get item by index
  item_t &get_item(size_t i) {return items[i];}
  
  /// Get the id for the first lemma, i.e., the id of the last clause + 1
  size_t get_fst_lemma_id() const {return fst_lemma_id;}
  
  /**
   * Initialization after forward pass:
   * 
   * @param cn_pos Position of conflict clause
   * @param tr Trail after forward pass
   * 
   * @see @ref Object_Lifetimes
   */
  void init_after_fwd(pos_t cn_pos, vector<trail_item_t> const &tr);
  
  /**
   * Join marking information for forward trail with provided information.
   * This is used after the concurrent backwards phase to join the information computed by the different threads.
   */
  void join_vmarked(vector<bool> const &marked);

  /**
   * Return the forward trail, with marking information joined in.
   */
  const vector<pair<size_t,bool>>& get_fwd_trail() const {return fwd_trail;}
  
  /**
   * Return the conflict clause.
   */
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



Global_Data glb; ///< Only instance of Global_Data @relates Global_Data

/**
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
  /**
   * Constructor.
   *
   * @pre Global data ::glb must already be after parsing when constructing this
   * 
   * @see @ref Object_Lifetimes
   */
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
  
  /// Mark a clause. 
  void mark_clause(lit_t *cl) { marked[clid(cl)].store(true, memory_order_relaxed); }
  /// Check if clause is marked.
  bool is_marked(lit_t *cl) { return marked[clid(cl)].load(memory_order_relaxed); }
  /// Try to acquire a clause
  bool acquire(lit_t *cl) { if (marked[clid(cl)]) return !acquired[clid(cl)].test_and_set(memory_order_acquire); else return false; }
  
  /// Return proof of clause. ALso for modification.
  vector<cdb_t> &proof_of(lit_t *cl) {return proofs[clid(cl)];}
  
  /// Increment RAT-count for specified literal.
  void inc_rat_counts(lit_t l) { ++rat_counts[l]; }
  
  /// Get the RAT-count map.
  const lit_map<atomic<size_t>> &get_rat_counts() { return rat_counts; }
};

/**
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
  /// Constructor
  Parser() :   
    cheq{glb.db}
  , clause_map(0,cheq,cheq)
  {}
  
  /// Skip over whitespace and comments
  void parse_ignore_comments(istream &in);
  
  /// Parse a clause to the global clause database.
  pos_t parse_clause(istream &in);
  /// Parse a deletion item to the global clause database.
  pos_t parse_deletion(istream &in);

  /// Parse the cnf file
  void parse_dimacs(istream &in);
  /// Parse the DRAT file
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

inline void Parser::parse_ignore_comments(istream &in) {
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



/**
 * @page Conflict_Analysis
 * @brief Conflict analysis and lemma marking.
 * 
 * # Conflict Analysis and Lemma Marking
 * 
 * The idea of backwards checking is to certify the lemmas backwards, marking those lemmas that have actually been used for a certification.
 * This way, unmarked lemmas can be skipped.
 * 
 * In order to realize backwards checking, one has to analyze the trail in the state after unit propagation found a conflict, 
 * and find out which lemmas have actually been used to derive the conflict.
 * 
 * The first relevant conflict is the root conflict after all lemmas have been added. 
 * Thus, before backward checking, the checker goes forwards over the lemmas, adds them to the formula, and then does 
 * unit propagation to find a conflict. The state of the trail after this conflict has been found is called *forward trail*.
 * 
 * Once a conflict has been found, all involved lemmas needs to be marked. For this reason, each literal on the trail is associated with a *reason*,
 * that is the unit clause due to which the literal has been set. Note that the reason is null, if the literal was set on initiating a RUP or RAT check, i.e., 
 * as one of the negated literals in the lemma to be proved.
 * 
 * A naive approach to conflict analysis would be to mark all reasons on the current trail. However, in practice, not all lemmas on the trail are actually required 
 * to derive the conflict. Thus, a more precise method is used: Only the reasons for setting the literals of the conflict clause are marked, and the reasons for setting their literals, and so on.
 * 
 * This is realized by a depth first search procedure: Each entry on the trail gets an additional visited flag (called *vmarked*), 
 * indicating that the reasons for the trail entry's literal have already been marked. Moreover, to quickly find the trail entries corresponding to the literals of a clause,
 * we store a map from assigned variables to trail positions. 
 * 
 * The DFS search is realized by the mutually recursive functions ::Verifier::mark_var() and ::Verifier::mark_clause(), 
 * which mark all the (recursive) reasons for a variable being set and for the literals of a clause being assigned. ::Verifier::mark_clause() additionally marks the clause, 
 * indicating that it needs to be certified when the backwards check arrives there.
 * 
 * ## Extracting the Certificate
 * 
 * Finally, a certificate has to be extracted. 
 * Again, there are two places where certificates has to be extracted: 
 * 
 * 1. After a successful RUP or RAT candidate check, a sequence of unit clause ids has to be emitted.
 *    These correspond exactly to the vmarked items that have been added to the trail during the RUP or RAT candidate check, and the list can be extracted during backtracking.
 * 
 * 2. When extracting the overall proof, unit propagations that led to the root conflict have to be recorded, and they must be correctly interleaved with the proofs for the lemmas!
 *    To this end, each lemma is associated with the trail size at which it was processed in the forward pass. 
 *    During emitting the lemmas, the corresponding entries on the forward trail that are vmarked are emitted as unit-propagation items.
 * 
 */


/** @page Core_First_Unit_Propagation
 *  @brief Concurrent core-first unit propagation
 * 
 *  @details
 *  # Concurrent Core-First Unit Propagation
 * 
 *  The goal of core-first unit propagation is to keep the number of newly marked clauses small, by preferring already marked clauses when searching for a conflict.
 * 
 *  Unit propagation is implemented by a two-watched literals scheme, that is, when processing a literal only the clauses that watch this literal have to be considered.
 * 
 *  Standard unit propagation iterates over the unprocessed literals on the trail. 
 *  For each literal, it iterates over the clauses on the literal's watchlist, tries to acquire a new watched literal, and sets encountered unit-literals or detects a conflict.
 * 
 *  For core-first unit propagation, two positions in this iteration (over trail, over watchlist) are maintained. 
 *  The first position indicates how far unit propagation has proceeded when ignoring unmarked clauses in the watchlists, and 
 *  the second position indicates how far unit propagation considering all clauses has proceeded. 
 * 
 *  Initially, unit propagation is done in cf-mode, considering only marked clauses. If this does not yield a conflict, one switches to normal-mode, considering all clauses.
 *  If, in normal mode, a new unit clause is found, one immediately switches back to cf-mode: Thus, the new literal is processed preferring marked clauses again.
 *  
 *  In DRAT-trim, normal mode only considers *unmarked* clauses, as the marked clauses have already been processed in cf-mode.
 *  In our setting, however, new clauses may be marked concurrently: When processing in normal mode, there may be marked clauses that have been marked after 
 *  the cf-mode iteration visited this position, and thus have not yet been processed.
 *  Currently, we consider all clauses in normal mode.
 * 
 *  TODO: We could also locally mark the clauses that we have already processed in cf-mode. Check whether this has a positive effect on runtime!
 *  
 * 
 */



/**
 * Main functionality for DRAT certificate verification.
 * 
 * There may be many concurrent verifiers, each working with its own copy of the clause database, 
 * and each having its own state (including assignment, trail, 2wl)
 * 
 */
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
  /**
   * Construct verifier using a specified clause database, instead of creating an own copy.
   * As clause databases tend to get huge, it is important for memory efficiency not to have an unused copy of the clause database lying around.
   * 
   * Warning: After a verifier is started on a clause database, it will modify the watched literals in there, such that concurrently initializing more 
   *  verifiers from this database is undefined behaviour! 
   * 
   */
  Verifier(ClauseDB &_db) : db(&_db), my_clause_db(false), assignment(0), trail(), fwd_vmarked(), vtpos(), watchlists(0) {}
  
  /// Deconstructor
  ~Verifier() {
    if (my_clause_db) delete db;
  }

  /**
   * Initialize after parsing has been completed
   * 
   * @see @ref Object_Lifetimes
   */
  void init_after_parsing(Synch_Data *_sdata) {
    sdata=_sdata;
    assignment.resize_reset(glb.get_max_var());
    vtpos.resize(glb.get_max_var()+1);
    watchlists.resize_reset(glb.get_max_var());
  }
  
  
  /**
   * Initialize a verifier with a copy of the specified clause database.
   */
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
  
  /**
   * Assign the verifier to be a copy of the specified verifier, using its own clause database and state.
   */
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
  
  /** @name Assignment
   * @{
   */
  
  /// Query wether literal is assigned to true
  inline bool is_true(lit_t l) {return assignment[l]!=0;}
  /// Query wether literal is assigned to false
  inline bool is_false(lit_t l) {return assignment[-l]!=0;}

  /// Assign literal to true
  inline void assign_true(lit_t l, lit_t* reason) {
    assert(!is_true(l) && !is_false(l));
    assignment[l] = 1; 
    vtpos[var_of(l)] = trail.size();
    trail.push_back({l,reason,false}); 
  }

  ///@}
  
  /** @name Adding and removing clauses
   * @{
   */
  
  /// Result of adding a clause
  enum class acres_t { 
    NORMAL,   ///< Clause is 2-undec, and has been added to watchlists
    UNIT,     ///< Clause is a unit clause, assignment has been updated
    TAUT,     ///< Clause is a tautology, it has been ignored
    CONFLICT  ///< Clause is a conflict clause. It has not been added.
  };

  /**
   * Add a clause and update the internal data structures.
   */
  acres_t add_clause(lit_t *cl);
  bool rem_clause(lit_t *cl);   ///< Remove clause from watchlist. Returns true if clause actually was in watchlists.
  void readd_clause(lit_t *cl); ///< Only clauses that where on watchlists may be readded.
  
  ///@}
  
  /** 
   * @name Backtracking and marking 
   * @{
   */
  
  /// Get trail
  vector<trail_item_t> const &get_trail() const {return trail;}
  
  /// Get trail position where next item is added.
  inline size_t trail_pos() {return trail.size();}  
  
  /// Get marking information collected for forward trail
  const vector<bool> &get_fwd_vmarked() {return fwd_vmarked;}
  
  void rollback(size_t pos);                        ///< Rollback to specfied trail position
  
  /** Dump vmarked clauses from pos (inclusive), by calling %ucr(cl).
   * 
   *  This function is used to emit the relevant unit propagations for reaching a conflict, before backtracking.
   * 
   *  @param pos Position (inclusive) to dump vmarked trail items
   *  @param ucr Callback invoked with the reason for each of the vmarked trail items.
   * 
   *  TODO: Could be combined with backtracking, to have only one iteration over the trail!
   * 
   * @see @ref Conflict_Analysis 
   */
  template<typename T> void for_marked_from(size_t pos, T const &ucr); 
  
  void mark_var(size_t v);     ///< Mark reason for this variable to be set, recursively. @see @ref Conflict_Analysis
  void mark_clause(lit_t *cl); ///< Mark clause and literals in clause, recursively. @see @ref Conflict_Analysis
  
  ///@}
  
  /**
   * Do unit propagation, explicitly selecting core-first optimization.
   * Note: Unit propagation does not perform conflict analysis, this must be invoked afterwards, with mark_clause().
   * 
   * @return Conflict clause or nullptr
   * 
   * @see @ref Core_First_Unit_Propagation
   */
  template<bool core_first> lit_t *propagate_units_aux();
  /**
   * Do unit propagation. Select core-first heuristics according to ::cfg_core_first.
   * Note: Unit propagation does not perform conflict analysis, this must be invoked afterwards, with mark_clause().
   * 
   * @return Conflict clause or nullptr
   * 
   * @see @ref Core_First_Unit_Propagation
   * 
   */
  lit_t *propagate_units() {if (cfg_core_first) return propagate_units_aux<true>(); else return propagate_units_aux<false>(); }

  /**
   * Collect all RAT candidates for a specified pivot literal.
   * 
   * @see @ref Unmarked_RAT_Candidates
   */
  void get_rat_candidates(std::vector< lit_t* >& cands, lit_t pivot);

  /**
   * Verify a clause, fail() on error.
   */
  void verify(lit_t *cl);
  
private:
  pos_t fwd_pass_aux();
public:
  /**
   * Perform forward pass
   * 
   * @return relative position of conflict clause
   */
  pos_t fwd_pass();
  
  /**
   * Perform backwards pass, starting at the specified item.
   * 
   * @param start_item Index of proof item to start as
   * @param show_status_bar Wether to print a status bar
   */
  void bwd_pass(size_t start_item, bool show_status_bar = false);
  
  /**
   * Used for debugging only.
   */
  void dbg_check_uprop();
  
  
};


void Verifier::dbg_check_uprop() {
  size_t num_undec_clauses = 0;
  
  for (lit_t l = watchlists.lbegin();l<watchlists.lend();++l) {
    for (auto cl : watchlists[l]) {
      
      if (cl[0] != l && cl[1] != l) {
        fail("Watched literal not on start pos");
      }
      
      if (cl[0] == l) {
        // Must not be a unit/conflict clause
        if (is_true(cl[0]) || is_true(cl[1])) continue;

        if (is_false(cl[0]) || is_false(cl[1])) {
          fail("Watched literal is false");
        }
          
        
        size_t ntrue=0;
        size_t nundec=0;
        
        for (lit_t *l=cl;*l;++l) {
          if (is_true(*l)) ++ntrue;
          else if (!is_false(*l)) ++nundec;
        }
        
        if (ntrue) continue;
        if (nundec==0) {
          fail("Conflict clause in WLs");
        }
        
        if (nundec==1) {
          fail("Unit clause in WLs");
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

#ifdef WITH_DBG_STAT
atomic<uintmax_t> dbg_stat_uprop_c1(0);
atomic<uintmax_t> dbg_stat_uprop_c2(0);
atomic<uintmax_t> dbg_stat_uprop_c3(0);
#endif

template<bool cf_enabled> lit_t *Verifier::propagate_units_aux() {
  size_t cf_processed = processed;

  bool cf_mode = cf_enabled;
  size_t ncf_ctd_i = 0;  // Watchlist index to continue when switching to non-cf_mode. Used to precisely store processed position.
  
  while (true) {
    size_t &ti = cf_mode?cf_processed:processed;

    // Watchlist-precise processed positioning
    size_t wl_starti;
    if (cf_mode) wl_starti=0; 
    else {wl_starti=ncf_ctd_i; ncf_ctd_i=0;}

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
      
      for (size_t i=wl_starti; i<watchlist.size(); ++i) {
        lit_t *cl = watchlist[i];
        
        DBG_STAT(++dbg_stat_uprop_c1;)
        
        /* Filter out unmarked clauses in cf-mode */
        // In cf_mode, ignore unmarked clauses
        /* FIXME: We would also like to ignore already processed clauses in non-cf mode.
         * However, we cannot use marked for that, as this may concurrently switch from false->true!
         * TODO: Enable stricter check in single-threaded mode only, and test whether we get speedup!
         */
//        if (cf_enabled && (cf_mode != sdata->is_marked(cl))) continue;  // For dbg only, not thread safe!
        if (cf_enabled && cf_mode && !sdata->is_marked(cl)) continue;  
        
        
        DBG_STAT(++dbg_stat_uprop_c2;)

        /* Filter out clauses where other watched literal is true */
        lit_t w1 = cl[0]; 
        lit_t w2 = cl[1];
        if (is_true(w1) || is_true(w2)) continue;

        DBG_STAT(++dbg_stat_uprop_c3;)
        
        
        if (w1==l) {                    // Normalize on w2 being set literal
          cl[0] = w2;                   // First part of swapping cl[0] and cl[1]. Second part is deferred, to summarize with swap in found-new-watched case
          w1=w2; w2=l;
        }
        assert(is_false(w2));
        assert(w2 == l);
        assert(cl[0] == w1);
        
        
        // Scan through clause and try to find new watched literal
        // Assuming that clauses do not contain dup literals, we can take first non-false literal from cl+2 onwards
        lit_t *w = nullptr;
        for (lit_t *ll=cl+2;*ll;++ll) {
          assert(*ll!=w1 && *ll!=w2);
          if (!is_false(*ll)) {w=ll; break;}
        }

        if (w) { // Found new watchable literal
          // Set new watched
          watchlists[*w].push_back(cl);

          // Swap w2 and *w (update cl[1] and *w)
          cl[1]=*w; *w=w2;

          // Remove this clause from old watchlist
          watchlist[i] = watchlist.back();
          watchlist.pop_back();
          --i;
          continue;
        } 

        // Complete swapping. TODO: If not swapped, this assignment is spurious. Test whether conditionally doing it improves performance.
        cl[1] = w2;

        // We found no watchable literal in clause
        if (!is_false(w1)) { // Found unit clause
          assign_true(w1,cl);
          
          if (cf_enabled && !cf_mode) {               // If we find a unit in non-cf_mode, switch back to cf-mode
            --ti; ncf_ctd_i = i+1;       // Store exact position where non-cf processing stopped
            cf_mode=true; 
            break;
          }
          
          continue;
        } else { // Found conflict clause
          return cl;
        }
      }
    }
  }
}

/** @page Unmarked_RAT_Candidates
 * @brief On ignoring unmarked RAT candidates
 * @details
 * # On Ignoring Unmarked RAT Candidates
 * 
 * When, during backwards checking, the DRAT-trim tool encounters a RAT candidate that is not marked,
 * it prints a warning and ignores the RAT candidate. Here, we briefly discuss the soundness of this in single threaded and multi-threaded mode.
 * 
 * ## Single-Threaded mode
 *   We believe that it is sound to ignore unmarked RAT candidates. We can argue as follows:
 *    Let l be the pivot literal, and D the unmarked candidate clause (we have -l in D).
 * 
 *    As D is unmarked, it is not used for any proof after the current position, and we could delete it right after the current lemma.
 *    Thus, it remains to show that D canot be used in the proof of the current lemma, after it has been ignored. Then, we could 
 *    delete D *before* the current lemma, justifying to ignore it.
 * 
 *    As l is the pivot literal, it is set to false at the beginning of the proof, making D a tautology.
 *    However, tautologies cannot participate in any conflict, thus D will not be used during the proof of the current lemma.
 * 
 * ## Multi-Threaded Mode
 *  **Unsound**! 
 * 
 *   The clause may be marked by another thread, *after* it has been ignored by this thread.
 *
 * ## Wrap-Up
 *  For our tool, we decided to never ignore unmarked candidate clauses. This may yield slightly more marked clauses, but is thread safe.
 *  Currently, we allow the GRAT format to contain invalid RAT candidate IDs. These correspond to unmarked RAT candidates, and are ignored by the checker.
 *  TODO: Filter out those during certificate write out (::VController::dump_proof()).
 * 
 */


void Verifier::get_rat_candidates(vector<lit_t*> &cands, lit_t pivot) {
  pivot=-pivot;
  
  for (lit_t l = watchlists.lbegin();l<watchlists.lend();++l) {
    for (auto cl : watchlists[l]) {
      if (cl[0] == l) {
        for (lit_t *ll=cl; *ll; ++ll) {
          if (*ll == pivot) {
//             if (!sdata->is_marked(cl)) break; // Attention! Unsound in multithreaded-mode, thus removed completely

            cands.push_back(cl);
            break;
          }
        }
      }
    }
  }
}

/**
 * The functionality of appending clause IDs to a vector.
 */
struct push_clause_ids {
  vector<lit_t> &prf; ///< vector to append IDs to
  
  /// Constructor
  push_clause_ids(vector<lit_t> &_prf) : prf(_prf) {};
  
  /// Append an ID
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
    if (!cfg_no_grat) {
      prf.push_back(item_type::RUP_LEMMA);
      for_marked_from(orig_pos, pci);
    }
    rollback(orig_pos);
    if (!cfg_no_grat) {
      prf.push_back(0);
      prf.push_back(static_cast<cdb_t>(clid(conflict)));
    }
  } else {
    vector<cdb_t> rat_prf;
    push_clause_ids rpci (rat_prf);
    // RUP-check failed, do RAT check
    if (pivot_false) {fail("RAT check failed due to false pivot");}
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
          fail("RAT-check failed");
        }
        mark_clause(conflict);
        
        if (!cfg_no_grat) {
          rat_prf.push_back(static_cast<cdb_t>(clid(ccl)));
          for_marked_from(rat_pos,rpci);
        }
        rollback(rat_pos); 
        if (!cfg_no_grat) {
          rat_prf.push_back(0);
          rat_prf.push_back(static_cast<cdb_t>(clid(conflict)));
        }
      }
    }
    
    // RAT-check succeeded
    if (!cfg_no_grat) {
      prf.push_back(item_type::RAT_LEMMA);
      prf.push_back(pivot);
      for_marked_from(orig_pos,pci);
    }
    rollback(orig_pos);
    if (!cfg_no_grat) {
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
  
  fail("Forward pass found no conflict");
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

/** @page Object_Lifetimes 
 *   @brief Object Initialization and Lifetime 
 * 
 *  @details
 *   # Object Initialization and Lifetime 
 * 
 *    We describe the object initializations during checking.
 *    TODO: The initialization seems to complicated, and could definitely be improved.
 * 
 *    1. Initialized first is a single instance of the Global_Data class (::glb).
 *       The lifetime of this data is split into two phases: During parsing and after parsing.
 * 
 *    2. During parsing, the clause database grows, such that pointers into the clause database may be invalidated. 
 *       In this phase, relative positions (::pos_t) are used to reference to items in the clause database.
 * 
 *    3. Once parsing has completed, the size of the clause database is fixed, and pointers to the first literal of a clause can be used. 
 *       (see @ref pg_clause_format for a description how clauses are stored).
 *       The phase transition is currently done by Parser calling the private Global_Data::init_after_parsing(). The current phase can be queried by Global_Data::is_after_parsing().
 * 
 *    4. Next, an object of type Synch_Data is initialized. It must only be initialized when ::glb is after parsing. 
 * 
 *    5. Next, a main Verifier is constructed, and the Synch_Data object is declared to it via Verifier::init_after_parsing(). 
 * 
 *    6. Using the main verifier, the forward pass of the checker is run. 
 * 
 *    7. After the forward pass has completed with a non-trivial conflict, the conflict clause and the forward trail are declared to the ::glb object (Global_Data::init_after_fwd()).
 * 
 *    8. Then, the main verifier is copied for each additional checker thread, and the backward passes are run in parallel.
 *        Copying a Verifier also creates a new instance of the clause database (::Verifier::Verifier(Verifier const &)).
 *       
 *    9. After all backward checkers have completed, the trail marking information for the main trail, which was collected by each backwards pass privately, is joined. (Global_Data.join_vmarked()) 
 * 
 *    10. Finally, the GRAT certificate is written out (VController::dump_proof())
 */


/**
 * Encapsulates the functionality to control the multi-threaded checker.
 * 
 * @see @ref Object_Lifetimes
 */
class VController {
private:
  Synch_Data *sdata = nullptr;
  Verifier main_vrf;
  
  VController(const VController &) = delete;
  VController &operator=(const VController &) = delete;
  
  void do_parallel_bwd(size_t num_threads);
  
public:
  /// Constructor. There should only be one VController at a time!
  VController() : main_vrf(glb.get_db()) 
  {}
  
  /// Destructor
  ~VController() {
    if (sdata) delete sdata;
  }
  
  /// Parse formula and certificate
  void do_parsing(istream &cnf_in, istream &drat_in);
  
  /// Perform verification, using the specified number of threads.
  void do_verification(size_t num_threads);
 
  /**
   * Write out the proof.
   *
   * @pre Proofs must have been recorded, i.e., ::cfg_no_grat == false
   */
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
#ifdef WITH_PROFILING
    ProfilerStart("/tmp/gratgen3.prof");
#endif
    with_timing("Backward pass",[&] {do_parallel_bwd(num_threads);},&stat_bwd_checking_time);
#ifdef WITH_PROFILING
    ProfilerStop();
#endif
  } else {
    clog<<"Trivial conflict in clauses"<<endl;
  }
}

void VController::dump_proof(ostream &out) {
  assert(!cfg_no_grat);
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

/// Print usage information
void print_usage() {
  cerr<<"Usage gratgen <dimacs-file> <proof-file> <options>"<<endl;
    cerr<<"Options:"<<endl;
    cerr<<"  -u, --no-core-first    Normal (no core first) unit propagation"<<endl;
    cerr<<"  -o name                Name of GRAT-file"<<endl;
    cerr<<"  -p, --no-deletion      Ignore deletion of clauses"<<endl;
    cerr<<"  -j, --num-parallel     Number of parallel threads to use. Default 1."<<endl;
    cerr<<"      --assume-nodup     Assume that clauses contain no duplicate literals"<<endl;
    cerr<<"      --no-progress-bar  Do not show fancy progress bar"<<endl;
}

/// Print sizes of data types used internally
void print_info() {
  cerr<<"sizeof(cdb_t) = "<<sizeof(cdb_t)<<endl;
  cerr<<"sizeof(cdb_t*) = "<<sizeof( cdb_t* )<<endl;
}

/// Main function
int main(int argc, char **argv) {
  auto main_start_time = chrono::steady_clock::now();

  print_info();

  if (argc<3) {print_usage(); return 2;}

  string dimacs_file = argv[1];
  string proof_file = argv[2];
  string grat_file=""; cfg_no_grat=true;

  size_t num_parallel = 1; //thread::hardware_concurrency();
  
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
      cfg_no_grat=false;
    } else {
      cerr<<"Unknown command line argument: "<<a<<endl; fail();
    }
  }
  
  ofstream grat_out;

  if (!cfg_no_grat) {
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
  
  if (!cfg_no_grat) {
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

#ifdef WITH_DBG_STAT
  clog<<"Debugging statistics"<<endl;
  clog<<"stat_uprop_c1 = "<<dbg_stat_uprop_c1<<endl;
  clog<<"stat_uprop_c2 = "<<dbg_stat_uprop_c2<<endl;
  clog<<"stat_uprop_c3 = "<<dbg_stat_uprop_c3<<endl;
#endif


  
  return 0;
}
