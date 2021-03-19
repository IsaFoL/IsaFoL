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


/** @page Heuristics
  @brief This page lists some of the heuristics used by gratgen

  @details

  gratgen uses some heuristics to speed up checking.
  Some of them originate from drat-trim and have been refined, improved, and adopted to teh multi-threaded setting,
  others have been newly developed. Here, we describe the most important ones:

  ## Backwards checking
  Backwards checking has already been used in drat-trim. Our version of backwards checking is almost
  the same, except that we run multiple threads in parallel, each of which is performing a backwards pass.

  The main idea of backwards checking is to first run a forward pass, which adds all lemmas without verifying, and then does unit
  propagation to derive the final conflict. All lemmas required to derive the final conflict are marked.
  Then, one (or multiple) threads run over the proof in backwards order. A lemma is removed, and if it is marked, it is verified.
  After sucecssful verification, all lemmas required for verification are marked.
  For multiple threads, a thread only verifies a lemma if it can acquire it. This ensures that no lemma is verified multiple times.

  ### Synchronization of marked clauses between threads
  Each thread keeps track of a local set of marked clauses, which is periodically synchronized with a global set of marked clauses.
  This ensures that marked clauses are communicated between threads, but a query for a clause to be marked causes no congestion.

  ## Core-first unit propagation

  Core first unit propagation was already included in drat-trim. The main idea is to prefer marked lemmas over
  unmarked ones during unit propagation, trying to reduce the number of newly marked lemmas.

  ### Separate watchlists
  While drat-trim iterates over the watchlist and filters the lemmas by core/noncore (i.e., marked/unmarked), gratgen uses two separate watchlists, one
  for the core and one for the non-core lemmas. Whenever a lemma is marked, it is moved from the non-core to the core watchlists.
  Our benchmarks show that this yields a significant speedup compared to a single watchlist, as iteration over watchlists is in the
  inner loop, and thus executed very often.

  ## RAT-run heuristics
  There are some proofs that contain many RAT lemmas. Searching for RAT-candidates is implemented by brute-force search, iterating over the watchlists.
  This implementation  has been adopted from drat-trim.
  However, experiments show that proofs often contain sequences of adjacent RAT lemmas over the same pivot literal.
  Thus, we store the result of a RAT-candidate search until the pivot literal changes, and re-use the stored result
  if another RAT-proof on the same pivot literal occurs.

  For some examples, this heuristics leads to three to four times faster checking times.
  The overhead of this heuristics is negligible, as RAT candidate lists tend to be short.

  ### Run-wise lemma acquisition in multi-threading
  To make this heuristics effective in multi-threaded mode, a thread will try to acquire all marked lemmas
  of a same-pivot run, before verifying the first lemma. This decreases the probability that a RAT-run is
  distributed over multiple threads, each thread searching the candidate list.

 */

/*
  TODO: Marijn proposed RAT search heuristics based on observation that pivot-literals actually occur in
        small intervals in the proof. Keep track of these intervals, and limit search to them.
        This can be done with modest overhead per literal.
        TUNING: Do pivot literals only occur in single interval? ==> Simpler DS.


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
#undef WITH_DBG_STAT
#define WITH_DBG_STAT
#else
#define WITH_DBG_STAT
#undef WITH_DBG_STAT
#endif

/**
 * Define this to get gperftools profiling. gperftools/profiler.h must be on include path!
 */
#ifdef WITH_PROFILING
#undef WITH_PROFILING
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
  clog<<"c FAILED";
  if (msg!="") clog<<": "<<msg;
  clog<<endl;
  clog<<"s ERROR"<<endl;
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
// template <typename S,typename T> struct dflt_eq {
//   bool operator() (S s, T t) {return s==t;}
// };

template<typename S, typename T/*, typename EQ = dflt_eq<S,T>*/> bool del_from_list(vector<S> &v, T x) {
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
 * @param dp Pointer to time to be incremented. nullptr if no time to be stored
 * @param out Stream to print message to, clog by default
 * @returns return value of op()
 */
template<typename RT, typename T> RT with_timing(string name, T op, chrono::milliseconds *dp = nullptr, ostream &out = clog) {
  RT r;
  out<<"c "<<name<<" ..."; out.flush();
  auto t = chrono::steady_clock::now();
  r=op();
  auto d = chrono::steady_clock::now() - t;
  chrono::milliseconds dm = chrono::duration_cast<chrono::milliseconds>(d);
  if (dp) *dp+=dm;
  out<<" "<< dm.count() <<"ms"<<endl; out.flush();
  return r;
}

/**
 * Measure timing of operation, and print timing message to log. Specialized for op() returning void.
 * @param name name that is printed as operation name
 * @param op operation, invoked as op()
 * @param dp Pointer to time to be incremented. nullptr if no time to be stored
 * @param out Stream to print message to, clog by default
 */
template<typename T> void with_timing(string name, T op, chrono::milliseconds *dp = nullptr, ostream &out = clog) {
  out<<"c "<<name<<" ..."; out.flush();
  auto t = chrono::steady_clock::now();
  op();
  auto d = chrono::steady_clock::now() - t;
  chrono::milliseconds dm = chrono::duration_cast<chrono::milliseconds>(d);
  if (dp) *dp+=dm;
  out<<" "<< dm.count() <<"ms"<<endl; out.flush();
}

/**
 * Measure timing of operation, and print timing message to log, allowing measured operation to print to log.
 * @param name name that is printed as operation name
 * @param op operation, invoked as op()
 * @param dp Pointer to time to be incremented. nullptr if no time to be stored
 * @param out Stream to print message to, clog by default
 * @returns return value of op()
 */
template<typename RT, typename T> RT with_timing_ml(string name, T op, chrono::milliseconds *dp = nullptr, ostream &out = clog) {
  RT r;
  out<<"c Starting "<<name<<endl; out.flush();
  auto t = chrono::steady_clock::now();
  r=op();
  auto d = chrono::steady_clock::now() - t;
  chrono::milliseconds dm = chrono::duration_cast<chrono::milliseconds>(d);
  if (dp) *dp+=dm;
  out<<"c Finished "<<name<<": "<< dm.count() <<"ms"<<endl; out.flush();
  return r;
}

/**
 * Measure timing of operation, and print timing message to log, allowing measured operation to print to log. Specialized for op() returning void.
 * @param name name that is printed as operation name
 * @param op operation, invoked as op()
 * @param dp Pointer to time to be incremented. nullptr if no time to be stored
 * @param out Stream to print message to, clog by default
 */
template<typename T> void with_timing_ml(string name, T op, chrono::milliseconds *dp = nullptr, ostream &out = clog) {
  out<<"c Starting "<<name<<endl; out.flush();
  auto t = chrono::steady_clock::now();
  op();
  auto d = chrono::steady_clock::now() - t;
  chrono::milliseconds dm = chrono::duration_cast<chrono::milliseconds>(d);
  if (dp) *dp+=dm;
  out<<"c Finished "<<name<<": "<< dm.count() <<"ms"<<endl; out.flush();
}


/**
 * Simple spinlock
 */
class spinlock {
private:
  atomic_flag flag = ATOMIC_FLAG_INIT;

  spinlock(spinlock const &) = delete;
  spinlock & operator= (spinlock const &) = delete;

public:
  /**
   * Constructor
   */
  spinlock() {}

  /**
   * Try to acquire the lock.
   * @param max_retries Maximum number of retries if first acquisition fails
   * @return True if acquisition successful.
   */
  inline bool acquire(size_t max_retries) {
    while (flag.test_and_set(std::memory_order_acquire)) {
      if (max_retries-- == 0) return false;
    }
    return true;
  }

  /** Acquire the lock. Busy-wait as long as the lock is acquired.
   */
  inline void acquire() {
    while (flag.test_and_set(std::memory_order_acquire));
  }

  /** Release the lock.
   * @pre Lock must be acquired by the calling thread.
   */
  inline void release() {
    flag.clear(std::memory_order_release);
  }


};



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
bool cfg_summarize_deletions = true; ///< Summarize deletions

size_t cfg_out_buf_size_threshold = 16*1024; ///<Threshold for output buffer size
bool cfg_premark_formula = false;  ///< Mark all clauses of initial formula, to prefer them in unit propagation

bool cfg_single_threaded = false; ///< Operate in single-threaded mode. Implicitly set by -j option.

bool cfg_rat_run_heuristics = true; ///< Enable RAT run heuristics
size_t cfg_rat_run_readd_upper_limit = 1<<8;  ///< Upper limit for re-added clauses to be collected until RAT-run heuristics is reset. TODO: Compute dynamically as fraction of total number of clauses?!

bool cfg_binary_drat = false; ///< Use binary format for drat file

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
size_t stat_num_clauses(0); /**< Number of ids */

size_t stat_rup_lemmas(0);    /**< Number of RUP lemmas */
size_t stat_rat_lemmas(0);    /**< Number of RAT lemmas */


atomic<size_t> stat_rat_run_h(0);     ///< How often RAT-run heuristics was successful
// atomic<size_t> stat_rat_run_h_search_readded(0); ///< How many re-added lemmas were searched by rat-run heuristics
// atomic<size_t> stat_rat_run_h_readd_limit_cancel(0); ///< How often RAT run collection has been cancelled due to re-add limit reached

/// @}

/******************************************
 * Main Program
 ******************************************/

/**
 * A relative position in the clause database. Used to point into the clause database during parsing phase, when the addresses of the stored data may still change.
 * Also used to exchange clauses between threads.
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


/** GRAT item types */
enum item_type : cdb_t {
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
  vector<lit_t> pivots;   // Map from clause ids to pivot literals. Empty clauses have pivot 0.
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
    stat_num_clauses = num_clauses;
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

  /// Get the pivot literal associated to a clause. Empty clauses have pivot 0.
  lit_t get_pivot(lit_t *cl) const {assert(cl); return pivots[clid(cl)];}

  /// Get the first item of the DRAT certificate
  size_t get_fst_prf_item() const {return fst_prf_item;}
  /// Get the total number of items
  size_t get_num_items() const {return items.size();}

  /// Truncate items, discarding the tail. @pre New number of items must be less or equal to current number of items.
  void truncate_items(size_t _num_items);

  /// Get item by index
  item_t &get_item(size_t i) {return items[i];}

  /// Get the id for the first lemma, i.e., the id of the last clause + 1
  size_t get_fst_lemma_id() const {return fst_lemma_id;}

  /// Check if this clause belongs to the original formula (true), or the proof (false)
  bool is_formula_clause(lit_t *cl) const {return clid(cl) < get_fst_lemma_id();}
  /// Check if this clause id belongs to the original formula (true), or the proof (false)
  bool is_formula_clause(size_t id) const {return id < get_fst_lemma_id();}

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


void Global_Data::truncate_items(size_t _num_items) {
  assert(_num_items <= items.size());
  items.erase(items.begin() + _num_items,items.end());
}



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

class Verifier;

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


  pos_t *mark_queue;       // Global marked queue. Capacity must be big enough to hold every clause at most once.
  size_t mq_pos=0;
  spinlock mq_lock;


  Synch_Data(Synch_Data const &) = delete;
  Synch_Data &operator= (Synch_Data const &) = delete;

private:
  /// Mark a clause, and return wether it was already marked.
  inline bool mark_clause(size_t id) { return marked[id].exchange(true); }
  /// Mark a clause.
  inline bool mark_clause(lit_t *cl) { return mark_clause(clid(cl)); }


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
  , mark_queue(cfg_single_threaded?nullptr : new pos_t[glb.get_num_clauses()])
  , mq_lock()
  {
    assert(glb.is_after_parsing());

    for (auto &b : marked) b=false;  // TODO: Is initialization necessary?
    //for (auto &f : acquired) f.test_and_set();  // Set all acquired flags. They are only cleared if clause is marked
  }

  ~Synch_Data() {
    if (mark_queue) delete [] mark_queue;
  }



  /// Check if clause is marked.
  inline bool is_marked(lit_t *cl) { return marked[clid(cl)].load(); }
  /// Try to acquire a clause
  inline bool acquire(lit_t *cl) { return !acquired[clid(cl)].test_and_set(memory_order_acquire); }


  /** Directly mark a single clause.
   * @pre Must be in single-threaded mode @see ::cfg_single_threaded.
   */
  bool mark_clause_single_threaded(lit_t *cl) {
    assert(cfg_single_threaded);
    return mark_clause(cl);
  }


  /// Return reference to proof of clause.
  inline vector<cdb_t> &proof_of(lit_t *cl) {return proofs[clid(cl)];}

  /// Increment RAT-count for specified literal.
  inline void inc_rat_counts(lit_t l) { ++rat_counts[l]; }

  /// Get the RAT-count map.
  inline const lit_map<atomic<size_t>> &get_rat_counts() { return rat_counts; }



  /**
   * Globally mark a vector of clauses, and exchange the data in the vector by incoming clauses.
   * As longer the list of incoming clauses, as harder this function tries to get the lock.
   * @param db Clause database the clauses are stored in. Used to compute positions.
   * @param clauses Vector of clauses to be marked. On success, is filled with incoming clauses to be marked
   * @param idx Marking sync-index for this thread. Updated on success.
   * @param failed_attempts Counter for failed attempts to get the lock. Updated by this function.
   * @returns Whether function succeeded to get the lock and do the update. On success, clauses and index are updated. Otherwise, nothing is updated.
   */
  inline bool bulk_mark_clauses(ClauseDB *db, vector<lit_t*> &clauses, size_t &idx, size_t &failed_attempts) {
    assert(!cfg_single_threaded);
    if (!mq_lock.acquire(clauses.size() + (failed_attempts++))) return false;

    size_t old_pos = mq_pos;
    assert(mq_pos < glb.get_num_clauses());

    for (auto cl : clauses) {
      if (!mark_clause(cl)) {
        assert(mq_pos < glb.get_num_clauses());
        mark_queue[mq_pos++]=db->c2p(cl);
      }
    }

    size_t new_pos = mq_pos;
    mq_lock.release();

    failed_attempts=0;

    clauses.clear();
    for (size_t i=idx;i<old_pos;++i) clauses.push_back(db->p2c(mark_queue[i]));
    idx=new_pos;

    return true;
  }

  /**
   * Get incoming marked clauses from global marking, but do not synchronize outgoing clauses.
   * @param db Clause database the clauses are stored in. Used to compute positions.
   * @param clauses On success, this is filled with incoming clauses to be marked
   * @param idx Marking sync-index for this thread. Updated on success.
   * @param failed_attempts Counter for failed attempts to get the lock. Updated by this function.
   *
   * @warning Not tested, currently not used.
   *
   */
  inline bool get_incoming(ClauseDB *db, vector<lit_t*> &clauses, size_t &idx, size_t &failed_attempts) {
    assert(!cfg_single_threaded);

    if (!mq_lock.acquire(failed_attempts++)) return false;
    size_t end = mq_pos;
    mq_lock.release();
    failed_attempts=0;

    clauses.clear();
    for (size_t i=idx;i<end;++i) clauses.push_back(db->p2c(mark_queue[i]));
    idx=end;
    return true;
  }


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

  /** Parse a clause to the global clause database.
   * @param in Input stream to read from
   * @param parse_append_raw Called with (in) to read and append a clause to clause db. @see parse_append_clause
   *
   */
  template<typename T> pos_t parse_clause(istream &in, T parse_append_raw);
  /// Parse a deletion item to the global clause database.
  template<typename T> pos_t parse_deletion(istream &in, T parse_append_raw);

  /// Parse the cnf file
  void parse_dimacs(istream &in);
  /// Parse the DRAT file
  void parse_proof(istream &in);

private:
  /// Parses a clause and appends to clause db. No postprocessing of clause is done.
  void parse_append_clause_raw(istream &in) {
    lit_t l;
    do {                                          // Push literals and terminating zero
      in>>ws; in>>l; glb.db.append(l);
    } while (l);
  }

  unsigned bin_parse_unsigned(istream &in);
  lit_t bin_parse_lit(istream &in);
  void bin_parse_append_clause_raw(istream &in);

public:
  /// Parse DRAT file in binary format
  void bin_parse_proof(istream &in);


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



template<typename T> pos_t Parser::parse_clause(istream& in, T parse_append_raw) {
  size_t id = ++glb.num_clauses;                    // Ids start at 1
  glb.db.append(id);                                // Push id
  pos_t pos = glb.db.current();                     // Positions refer to first literal

  parse_append_raw(in);  // Read clause to clause-db
  assert(glb.db.current().pos > pos.pos); // At least a terminating 0 must have been read

//   lit_t l;
//   do {                                          // Push literals and terminating zero
//     in>>ws; in>>l; glb.db.append(l);
// //     glb.max_var = max(var_of(l),glb.max_var);
//   } while (l);

  auto cl = glb.db.p2i(pos);                  // pos indicates first literal
  auto cle = glb.db.p2i(glb.db.current())-1;  // set cle one past last literal (Current position is one past terminating zero)

  set_resize<lit_t>(glb.pivots,id,*cl);         // Remember pivot as first literal of clause. Note: If clause is empty, we store 0 as pivot.
  sort(cl,cle);                                 // Sort literals by ascending numerical value

  if (!cfg_assume_nodup) {
    // Remove duplicate literals
    auto ncle = unique(cl,cle);
    if (ncle != cle) {
      ncle[0]=0;
      glb.db.shrink_to(ncle+1);
      cle=ncle;
    }
  }

  // Adjust max-var
  for (auto i = cl;i!=cle;++i) glb.max_var = max(var_of(*i),glb.max_var);


  clause_map.insert({ pos, pos });              // Add to clause_map

  return pos;
}

template<typename T> pos_t Parser::parse_deletion(istream &in, T parse_append_raw) {
  pos_t orig_pos = glb.db.current();
  pos_t result = pos_t::null;

  /*
   * In order to hash it, we push the clause to db first. Later, we will delete it again
   */

  glb.db.append(0);                             // Push dummy id

  pos_t pos = glb.db.current();

  parse_append_raw(in);  // Read clause to clause-db
  assert(glb.db.current().pos > pos.pos); // At least a terminating 0 must have been read

//   lit_t l;
//   do {                                          // Push literals and terminating zero
//     in>>ws; in>>l; glb.db.append(l);
//   } while (l);

  lit_t *cl = glb.db.p2c(pos);                  // pos indicates first literal
  lit_t *cle = glb.db.p2c(glb.db.current())-1;  // set cle one past last literal (Current position is one past terminating zero)

  sort(cl,cle);                                 // Sort

  if (!cfg_assume_nodup) {
    // Remove duplicate literals
    cle = unique(cl,cle);
    cle[0] = 0;
  }

  auto orig_c = clause_map.find(pos);           // Look up clause

  if (orig_c == clause_map.end()) {
    clog<<"c Ignoring deletion of non-existent clause (pos "<<pos.pos<<")"<<endl;
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
  if (!in.eof() && in.peek()=='p') in.ignore(numeric_limits<streamsize>::max(), '\n');

  while (!in.eof()) {
    parse_ignore_comments(in);
    if (in.eof()) break;

    pos_t pos = parse_clause(in,[this](istream &in){parse_append_clause_raw(in);});

    glb.items.push_back(item_t(false,pos));
  }

  glb.fst_lemma_id = glb.num_clauses+1;
  glb.fst_prf_item = glb.items.size();
}


void Parser::parse_proof(istream &in) {
  in.exceptions(in.failbit|in.badbit);

  parse_ignore_comments(in);
  if (!in.eof() && in.peek()=='o') in.ignore(numeric_limits<streamsize>::max(), '\n');
  parse_ignore_comments(in);

  while (!in.eof()) {
    parse_ignore_comments(in);
    if (in.eof()) break;

    if (in.peek()=='d') {
      in.get();
      pos_t pos = parse_deletion(in,[this](istream &in){parse_append_clause_raw(in);});

      if (pos) glb.items.push_back(item_t(true,pos));
    } else {
      pos_t pos = parse_clause(in,[this](istream &in){parse_append_clause_raw(in);});
      glb.items.push_back(item_t(false,pos));
    }
  }

  glb.init_after_parsing();
}


inline unsigned Parser::bin_parse_unsigned(istream &in) {
  unsigned res=0;
  unsigned shift=0;

  int c;
  do {
    c = in.get();
    assert(c>=0); // Assuming exception on fail!
    res |= (c & 0x7F) << shift;  // TODO: Overflow check!
    shift += 7;
  } while ((c&0x80) != 0);

  return res;
}


inline lit_t Parser::bin_parse_lit(istream &in) {
  unsigned ul = bin_parse_unsigned(in);
  if ((ul&0x01) != 0) return -(static_cast<int>(ul>>1));
  else return static_cast<int>(ul>>1);
}

inline void Parser::bin_parse_append_clause_raw(istream &in) {
  lit_t l;
  do {                                          // Push literals and terminating zero
    l=bin_parse_lit(in);
    glb.db.append(l);
  } while (l);
}


void Parser::bin_parse_proof(istream &in) {
//   in.exceptions(in.failbit|in.badbit);

  while (true) {
    int ctrl = in.get();
    if (ctrl < 0) break;

    if (ctrl=='d') {
      pos_t pos = parse_deletion(in,[this](istream &in){bin_parse_append_clause_raw(in);});
      if (pos) glb.items.push_back(item_t(true,pos));
    } else if (ctrl=='a') {
      pos_t pos = parse_clause(in,[this](istream &in){bin_parse_append_clause_raw(in);});
      glb.items.push_back(item_t(false,pos));
    } else {
      fail("Binary format: Invalid ctrl byte " + std::to_string(ctrl));
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
 *  Currently, we consider all clauses in normal mode. However, a clause that remains in the watchlist after being processed in cf-mode has one of
 *  its watched literals set to true (either it was already true, or unit-propagation set it to true). Thus, not much work is spent on those additional clauses.
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


  /**
   * Watchlists are split into core and non-core watchlist.
   * Unmarked clauses go to the noncore watchlist, and are lazily propagated to the core watchlist if they are marked.
   */
  lit_map<vector<lit_t *>> core_watchlists;
  lit_map<vector<lit_t *>> noncore_watchlists;


  /**
   * State of a clause in watchlists
   */
  class wl_clause_state_t {
  private:
    static const unsigned NO_FLAGS     = 0x00;
    static const unsigned IN_WL        = 0x01;      // Clause is in watchlists.
    static const unsigned CORE         = 0x02;      // Clause is core

    unsigned flags = NO_FLAGS;

  public:
    inline bool is_clear() {return flags == NO_FLAGS;}

    inline bool is_inwl() {return flags & IN_WL;}
    inline wl_clause_state_t& set_inwl() {flags|=IN_WL; return *this;}
    inline wl_clause_state_t& clear_inwl() {flags&= ~IN_WL; return *this;}

    inline bool is_core() {return flags & CORE;}
    inline wl_clause_state_t& set_core() {flags|=CORE; return *this;}


    // is_core || !in_wl
//     inline bool der_is_orphan() { return (flags & (CORE|IN_WL)) != IN_WL; }

  };

  vector<wl_clause_state_t> wl_clause_state; // id -> Watchlist state of clauses

  vector<lit_t *> new_core; // Clauses that should be marked as core, buffered during uprop. FIXME Will probably be removed

  vector<lit_t *> marked_outgoing;  // Outgoing marked clauses, to be synchronized
  size_t failed_sync_attempts=0;    // Failed attempts to synchronize marked clauses
  size_t glb_marked_sync_idx=0;     // Synchronization index with global marked queue


  size_t cnt_verified = 0; // Number of lemmas verified by this instance


  vector<lit_t *> rat_candidates;       ///< Last RAT candidate list. May be flushed if RAT run heuristics is not enabled.
  lit_t rat_lit = 0;                    ///< Last literal for which RAT candidates have been collected, 0 if no valid collected candidates.


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
  Verifier(ClauseDB &_db) :
      db(&_db)
    , my_clause_db(false)
    , assignment(0)
    , trail()
    , fwd_vmarked()
    , vtpos()
    , core_watchlists(0)
    , noncore_watchlists(0)
    , wl_clause_state(0)
    , new_core()
    , marked_outgoing()
    , rat_candidates()
    {}

  /// Destructor
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
    if (cfg_core_first) core_watchlists.resize_reset(glb.get_max_var());
    noncore_watchlists.resize_reset(glb.get_max_var());
    wl_clause_state.resize(glb.get_num_clauses() + 1);
    trail.reserve(glb.get_max_var() + 1);
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
    , core_watchlists(vrf.core_watchlists)
    , noncore_watchlists(vrf.noncore_watchlists)
    , wl_clause_state(vrf.wl_clause_state)
    , new_core(vrf.new_core)
    , marked_outgoing()
    , glb_marked_sync_idx(vrf.glb_marked_sync_idx)
    , cnt_verified(vrf.cnt_verified)
    , rat_candidates(vrf.rat_candidates)
    , rat_lit(vrf.rat_lit)
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
    core_watchlists = vrf.core_watchlists;
    noncore_watchlists = vrf.noncore_watchlists;
    cnt_verified = vrf.cnt_verified;
    wl_clause_state = vrf.wl_clause_state;
    new_core = vrf.new_core;

    marked_outgoing.clear();
    glb_marked_sync_idx=vrf.glb_marked_sync_idx;

    rat_candidates=vrf.rat_candidates;
    rat_lit = vrf.rat_lit;

    relocate(vrf.db);
    return *this;
  }

  Verifier(Verifier const &&vrf) = delete;
  Verifier &operator=(Verifier const &&vrf) = delete;


  /** @name Assignment
   * @{
   */

  /// Query wether literal is assigned to true
  inline bool is_true(lit_t l) {assert(l != 0); return assignment[l]!=0;}
  /// Query wether literal is assigned to false
  inline bool is_false(lit_t l) {assert(l != 0); return assignment[-l]!=0;}

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
  void readd_clause(lit_t *cl); ///< Only clauses that where on watchlists may be readded. Watched literals must not have changed since deletion.

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


  /**
   * Synchronize marked clauses. May give up to acquire lock if not too many clauses to synchronize.
   * @param force Force synchronization.
   */
  bool sync_marked(bool force);
  /**
   * Synchronize only incoming marked clauses
   */
  void sync_incoming_marked();


  ///@}

private:

  /** @name RAT run heuristics
   * @{
   */

  inline void clear_rat_runs() {
    rat_lit = 0;
    // We intentionally do not reclaim memory for the lists here: We expect RAT candidate lists to be short, and we have limited the added-list size anyway.
  }



  ///@}

private:

  /**
   * Do unit propagation, explicitly selecting core-first optimization.
   * Note: Unit propagation does not perform conflict analysis, this must be invoked afterwards, with mark_clause().
   *
   * @return Conflict clause or nullptr
   *
   * @see @ref Core_First_Unit_Propagation
   */
  template<bool core_first> lit_t *propagate_units_aux();

public:
  /**
   * Do unit propagation. Select core-first heuristics according to ::cfg_core_first.
   * Note: Unit propagation does not perform conflict analysis, this must be invoked afterwards, with mark_clause().
   *
   * @return Conflict clause or nullptr
   *
   * @see @ref Core_First_Unit_Propagation
   *
   */
  lit_t *propagate_units() {
    if (cfg_core_first) {
      lit_t *res = propagate_units_aux<true>();
      handle_new_core();
      return res;
    }
    else return propagate_units_aux<false>();
  }

private:
  /**
   * Collect all RAT candidates for a specified pivot literal.
   * The results are returned in @ref rat_candidates. This list must not be changed afterwards, e.g., by removing blocked clauses!
   *
   * @see @ref Unmarked_RAT_Candidates
   */
  void get_rat_candidates(lit_t pivot);

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
   * @param show_status_bar Wether to print a status bar
   */
  void bwd_pass(bool show_status_bar);

//   /**
//    * Used for debugging only.
//    */
//   void dbg_check_uprop();


public:
  inline size_t get_cnt_verified() {return cnt_verified;}


private:
  /**
   * @name Watchlist management
   * @{
   */

  /**
   * Add to core or non-core watchlist depending on local and global marked state.
   */
  inline void add_to_wl(lit_t *cl) {
    auto id = clid(cl);

    auto &cst = wl_clause_state[id];
    assert(!cst.is_inwl());

    bool marked = sdata->is_marked(cl);

    lit_t w1=cl[0]; assert(w1 != 0);
    lit_t w2=cl[1]; assert(w2 != 0);

    if (marked || cst.is_core()) { // Make sure that local core clauses are added to core wl
      if (cfg_core_first) {
        core_watchlists[w1].push_back(cl);
        core_watchlists[w2].push_back(cl);
      } else {
        noncore_watchlists[w1].push_back(cl);
        noncore_watchlists[w2].push_back(cl);
      }
      cst.set_inwl().set_core();
    } else {
      noncore_watchlists[w1].push_back(cl);
      noncore_watchlists[w2].push_back(cl);
      cst.set_inwl();
    }


    // RAT run heuristics. Clear run heuristics.
    /* Initially, we have stored the added lemmas here, however, we found that
     * RAT-runs did not exceed over deletion items (which cause adding of clauses).
     * Thus, we immediately invalidate the RAT run heuristics if a new lemma is added.
     */
    if (rat_lit!=0 && cfg_rat_run_heuristics) {
      clear_rat_runs();
    }

  }


  /**
   * Move clause to core watchlists, if it is in noncore-watchlists.
   * Also add clause to outgoing marking synchronization list.
   *
   * May also be called for deleted clauses, or clauses never added to any watchlist.
   * In this case, this function only adds the clause to outgoing marking synchronization list.
   *
   * @param cl Clause to move to core
   * @param to_outgoing If set, the clause is also added to outgoing marked queue.
   *      If, however, this clause has been synched from global marked queue, there is no point re-adding it to local queue, and this should be clear.
   */
  inline void move_to_core(lit_t *cl, bool to_outgoing=true) {
    auto id = clid(cl);
    auto &cst = wl_clause_state[id];

    if (cst.is_core()) return; // No effect on clauses that are already known to be in core
    cst.set_core();

    if (to_outgoing) {
      if (cfg_single_threaded)
        sdata->mark_clause_single_threaded(cl);
      else
        marked_outgoing.push_back(cl);
    }

    if (!cst.is_inwl()) return; // If clause is not in wl, we only add it to outgoing marked list.
    if (!cfg_core_first) return; // If core-first mode is not enabled, we do not maintain core-watchlists

    // Only add clause if it is not deleted, in a watchlist, and not already in core watchlists
    lit_t w1=cl[0]; assert(w1 != 0);
    lit_t w2=cl[1]; assert(w2 != 0);

    // Remove from noncore watchlists
    bool d1 = del_from_list(noncore_watchlists[w1],cl);
    bool d2 = del_from_list(noncore_watchlists[w2],cl);
    assert(d1 && d2);
    (void)(d1 && d2); // Silence unused warning

    // Add to core watchlists
    core_watchlists[w1].push_back(cl);
    core_watchlists[w2].push_back(cl);

  }


  inline void register_new_core(lit_t *cl) {
    new_core.push_back(cl);
  }

  inline void handle_new_core() {
    for (auto cl : new_core) {
      move_to_core(cl);
    }
    new_core.clear();
  }


  ///@}


};


void Verifier::relocate(ClauseDB const *odb) {
  for (auto &ti : trail) {
    relocate(odb,ti.reason);
  }

  if (cfg_core_first) {
    for (lit_t l=core_watchlists.lbegin();l<core_watchlists.lend();++l) {
      for (auto &cl : core_watchlists[l]) relocate(odb,cl);
    }
  }

  for (lit_t l=noncore_watchlists.lbegin();l<noncore_watchlists.lend();++l) {
    for (auto &cl : noncore_watchlists[l]) relocate(odb,cl);
  }

  for (auto &cl : rat_candidates) relocate(odb,cl);


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

    add_to_wl(cl);

    return acres_t::NORMAL;
  }
}

bool Verifier::rem_clause(lit_t *cl) {
  auto id = clid(cl);

  auto &cst = wl_clause_state[id];

  if (!cst.is_inwl()) return false;

  lit_t w1=cl[0]; assert(w1 != 0);
  lit_t w2=cl[1]; assert(w2 != 0);


  if (cfg_core_first && cst.is_core()) {
    bool d1 = del_from_list(core_watchlists[w1],cl);
    bool d2 = del_from_list(core_watchlists[w2],cl);
    assert(d1 && d2);
    (void)(d1 && d2); // Silence unused warning
  } else {
    bool d1 = del_from_list(noncore_watchlists[w1],cl);
    bool d2 = del_from_list(noncore_watchlists[w2],cl);
    assert(d1 && d2);
    (void)(d1 && d2); // Silence unused warning
  }

  cst.clear_inwl();

  return true;
}

void Verifier::readd_clause(lit_t *cl) {
  add_to_wl(cl);
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

    if (pos < fwd_trail_size) fwd_vmarked[pos]=true; // If this position is on current forward trail, also flag as marked there

    if (trail[pos].reason) mark_clause(trail[pos].reason);
  }
}

void Verifier::mark_clause(lit_t *cl) {
  move_to_core(cl);

  for (auto l=cl;*l;++l) {
    mark_var(var_of(*l));
  }
}


bool Verifier::sync_marked(bool force) {
  assert(!cfg_single_threaded);

  if (force) {
    if (!marked_outgoing.size()) return false;
    while (!sdata->bulk_mark_clauses(db,marked_outgoing,glb_marked_sync_idx,failed_sync_attempts));
  } else {
    if (!sdata->bulk_mark_clauses(db,marked_outgoing,glb_marked_sync_idx,failed_sync_attempts)) return false;
  }

  // Successfully synchronized, marked_outgoing now contains incoming clauses
  for (auto cl : marked_outgoing) move_to_core(cl, false);
  marked_outgoing.clear();

  return true;
}

void Verifier::sync_incoming_marked() {
  assert(!cfg_single_threaded);

  vector<lit_t*> incoming;
  if (sdata->get_incoming(db,incoming,glb_marked_sync_idx,failed_sync_attempts)) {
    for (auto cl : incoming) move_to_core(cl, false);
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
    if (cf_mode) {
      assert(cfg_core_first);

      if (cf_processed == trail.size()) {
        // If processed whole trail for cf, switch back to non-cf
        cf_mode=false;
        continue;
      }

      lit_t l = trail[cf_processed].l;
      ++cf_processed;

      l=-l; // Negated literal has been set to false

      auto &__restrict__ watchlist = core_watchlists[l];


      for (size_t i=0;i<watchlist.size();++i) {

        lit_t *cl = watchlist[i];

        assert(wl_clause_state[clid(cl)].is_core());  // Core watchlist will only contain core clauses
        assert(wl_clause_state[clid(cl)].is_inwl());  // Core watchlist must not contain deleted clauses

        DBG_STAT(dbg_stat_uprop_c2++;);


        lit_t w1 = cl[0];
        lit_t w2 = cl[1];

        assert (w1 == l || w2 == l);

        /* Filter out clauses where other watched literal is true */
        if (is_true(w1) || is_true(w2)) {
          continue;
        }


        if (w1==l) {                    // Normalize on w2 being set literal
          cl[0] = w2;                   // First part of swapping cl[0] and cl[1]. Second part is deferred, to summarize with swap in found-new-watched case
          w1=w2; w2=l;
        }
        assert(w2 == l);
        assert(is_false(w2));
        assert(cl[0] == w1);

        // Scan through clause and try to find new watched literal
        // Assuming that clauses do not contain dup literals, we can take first non-false literal from cl+2 onwards
        lit_t *w = nullptr;
        for (lit_t *ll=cl+2;*ll;++ll) {
          assert(*ll!=w1 && *ll!=w2);
          if (!is_false(*ll)) {w=ll; break;}
        }

        if (w) { // Found new watchable literal
          // Remove this clause from old watchlist, correct iteration index
          watchlist[i] = watchlist.back();
          watchlist.pop_back();
          --i;

          assert(*w != l);
          core_watchlists[*w].push_back(cl);

          // Swap w2 and *w (update cl[1] and *w)
          cl[1] = *w; *w = w2;

          continue;
        }

        // Complete swapping. TODO: If not swapped, this assignment is spurious. Test whether conditionally doing it improves performance.
        cl[1] = w2;

        // We found no watchable literal in clause
        if (!is_false(w1)) { // Found unit clause
          assign_true(w1,cl);
          continue;
        } else { // Found conflict clause
          return cl;
        }
      }
    } else {

      if (processed == trail.size()) {
        // No conflict found
        return nullptr;
      }

      lit_t l = trail[processed].l;
      ++processed;

      l=-l; // Negated literal has been set to false


      // Noncore propagation.
      auto &__restrict__  watchlist = noncore_watchlists[l];

      // Precise positioning of noncore propagation continuation index
      size_t i = ncf_ctd_i;
      ncf_ctd_i=0;

      for (;i<watchlist.size();++i) {
        lit_t *cl = watchlist[i];

        assert(!cfg_core_first || !wl_clause_state[clid(cl)].is_core());  // Noncore watchlist will only contain non-core clauses (if cf enabled. Otherwise, core-wl contains all clauses)
        assert(wl_clause_state[clid(cl)].is_inwl());  // Noncore watchlist must not contain deleted clauses


        DBG_STAT(dbg_stat_uprop_c1++;);

//           if (sdata->is_marked(cl)) {
//             register_new_core(cl);
//             DBG_STAT(dbg_stat_uprop_c1++;);
//           }

        lit_t w1 = cl[0];
        lit_t w2 = cl[1];
        assert (w1 == l || w2 == l);

        /* Filter out clauses where other watched literal is true */
        if (is_true(w1) || is_true(w2)) {
          continue;
        }


        if (w1==l) {                    // Normalize on w2 being set literal
          cl[0] = w2;                   // First part of swapping cl[0] and cl[1]. Second part is deferred, to summarize with swap in found-new-watched case
          w1=w2; w2=l;
        }
        assert(w2 == l);
        assert(is_false(w2));
        assert(cl[0] == w1);

        // Scan through clause and try to find new watched literal
        // Assuming that clauses do not contain dup literals, we can take first non-false literal from cl+2 onwards
        lit_t *w = nullptr;
        for (lit_t *ll=cl+2;*ll;++ll) {
          assert(*ll!=w1 && *ll!=w2);
          if (!is_false(*ll)) {w=ll; break;}
        }


        if (w) { // Found new watchable literal
          // Remove this clause from old watchlist, correct iteration index
          watchlist[i] = watchlist.back();
          watchlist.pop_back();
          --i;

          // Add to new watchlist
          assert(*w != l);
          noncore_watchlists[*w].push_back(cl);

          // Swap w2 and *w (update cl[1] and *w)
          cl[1] = *w; *w = w2;

          continue;
        }


        // Complete swapping. TODO: If not swapped, this assignment is spurious. Test whether conditionally doing it improves performance.
        cl[1] = w2;


        // We found no watchable literal in clause
        if (!is_false(w1)) { // Found unit clause
          assign_true(w1,cl);

          if (cf_enabled) {              // If we find a unit in non-cf_mode, switch back to cf-mode
            --processed; ncf_ctd_i = i+1;       // Store exact position where non-cf processing stopped
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


void Verifier::get_rat_candidates(lit_t pivot) {
  // Gather RAT candidates

  assert(pivot !=0 );
  pivot=-pivot;


  if (cfg_rat_run_heuristics && pivot == rat_lit) {
    // RAT run heuristics. Filter last candidates, and search in newly added clauses

    ++stat_rat_run_h;

    // Filter out deleted clauses from last candidates
    for (size_t i=0;i<rat_candidates.size();++i) {
      lit_t *cl = rat_candidates[i];
      if (!wl_clause_state[clid(cl)].is_inwl()) {
        rat_candidates[i]=rat_candidates.back();
        rat_candidates.pop_back();
        --i;
      }
    }

  } else {
    // Search for candidates in watchlists

    rat_candidates.clear();
    if (cfg_rat_run_heuristics) rat_lit=pivot; else rat_lit=0;

    auto collect = [pivot, this](vector<lit_t*>& watchlist, lit_t l) {
      auto end = watchlist.end();

      for (auto it = watchlist.begin();it!=end; ++it) {
        lit_t *cl = *it;

        assert(wl_clause_state[clid(cl)].is_inwl()); // Watchlists must not contain deleted clauses

        if (cl[0] == l) {
          for (lit_t *ll=cl; *ll; ++ll) {
            if (*ll == pivot) {
              rat_candidates.push_back(cl);
              break;
            }
          }
        }
      }
    };


    lit_t lmin=-static_cast<lit_t>(glb.get_max_var());
    lit_t lmax=static_cast<lit_t>(glb.get_max_var());

    if (cfg_core_first) {
      for (lit_t l = lmin;l<=lmax;++l) {
        collect(noncore_watchlists[l],l);
        collect(core_watchlists[l],l);
      }
    } else {
      for (lit_t l = lmin;l<=lmax;++l) {
        collect(noncore_watchlists[l],l);
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
  ++cnt_verified;

  vector<lit_t> &prf = sdata->proof_of(cl);
  push_clause_ids pci (prf);

  size_t orig_pos = trail_pos();
  lit_t pivot = glb.get_pivot(cl);
  bool pivot_false = (pivot!=0) && is_false(pivot);

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
    ++stat_rup_lemmas;
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
    if (pivot == 0) {fail("RUP check failed on empty clause");}     // Cannot do RAT check on empty clause.
    if (pivot_false) {fail("RAT check failed due to false pivot");} // Must not do RAT check if pivot literal is false.
    sdata->inc_rat_counts(pivot);

    // Gather clauses containing pivot. Result is in rat_candidates.
    get_rat_candidates(pivot);

    size_t rat_pos = trail_pos();

    // Iterate over candidates
    for (auto ccl : rat_candidates) {
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
    ++stat_rat_lemmas;

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
        case acres_t::CONFLICT: {
          // Trivial conflict in clauses
//           clog<<"c Trivial conflict in initial clauses"<<endl;
          mark_clause(cl);
          glb.truncate_items(glb.get_fst_prf_item());  // Strip proof, not required
          return db->c2p(cl);
          // return pos_t::null;
        }
        case acres_t::NORMAL: break;
        default:;
      }
    }
  }

  lit_t *conflict = propagate_units();
  if (conflict) {
    // Conflict after unit-propagation on initial clauses
//     clog<<"c Conflict after unit propagation on initial clauses"<<endl;
    mark_clause(conflict);
    glb.truncate_items(glb.get_fst_prf_item());  // Strip proof, not required
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
          case acres_t::CONFLICT:
            mark_clause(cl);
            glb.truncate_items(i+1); // Remaining items not required for proof.
            return db->c2p(cl);

          case acres_t::UNIT: item.set_trpos(trpos);
          case acres_t::NORMAL: {
            conflict = propagate_units();
            if (conflict) {
              mark_clause(conflict);
              glb.truncate_items(i+1);  // Remaining items not required for proof.
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

  // Mark initial clauses
  if (cfg_premark_formula) {
    clog<<"c pre-marking formula"<<endl;

    for (size_t i=0;i<glb.get_fst_prf_item();++i) {
      item_t &it=glb.get_item(i);
      if (!it.is_erased()) {
        assert(!it.is_deletion());
        lit_t *cl = db->p2c(it.get_pos());
        assert(clid(cl)<glb.get_fst_lemma_id());
        move_to_core(cl);
      }
    }
  }

  return res;
}


void Verifier::bwd_pass(bool show_status_bar) {

  // Iterate over lemmas
  boost::progress_display *pdsp = show_status_bar?new boost::progress_display(glb.get_num_items() - glb.get_fst_prf_item()) : nullptr;

  size_t cycles_not_synched = 0;

  size_t outgoing_threshold = 0;
//   if (outgoing_threshold<100) outgoing_threshold=100;

  size_t cycles_threshold = 0;
//   if (cycles_threshold<100) cycles_threshold=100;


  size_t range_detect_max = 512; // Maximum equal-pivot range to acquire simultaneously


  size_t i = glb.get_num_items();

  size_t range_end_idx = glb.get_num_items();   // Next item index not in current range
  deque<lit_t*> range_acquired;               // List of clauses pre-acquired for current range

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
        if (cl[0] && cl[1]) {
          bool inwl = rem_clause(cl);
          assert(inwl);
          (void)inwl; // Silence unused warning
        }

        // Remove from trail
        if (item.has_tr_pos()) rollback(item.get_trpos());


        bool do_verify = false;

        if (!range_acquired.empty() && cl == range_acquired.front()) {
          assert(i>range_end_idx);
          assert(wl_clause_state[clid(cl)].is_core());
          range_acquired.pop_front();
          do_verify=true;
        } else if (wl_clause_state[clid(cl)].is_core()) {
          if (sdata->acquire(cl)) {
            do_verify=true;

            // Range heuristics
            if (!cfg_single_threaded && cfg_rat_run_heuristics && i <= range_end_idx) {
              assert(range_acquired.empty());
              range_end_idx=i;

              lit_t pivot = glb.get_pivot(cl);

              while (true) {
                --range_end_idx;
                if (range_end_idx < glb.get_fst_prf_item()) break;
                if (i - range_end_idx > range_detect_max) break;

                item_t &it = glb.get_item(range_end_idx);
                if (it.is_erased()) continue;
                if (it.is_deletion()) break; // TODO: Is it worth to detect ranges across deletions?

                lit_t *cl2 = db->p2c(it.get_pos());
                if (glb.get_pivot(cl2) != pivot) break;

                // Element is in range

                if (wl_clause_state[clid(cl2)].is_core()) {
                  // Element is in core, try to acquire
                  if (sdata->acquire(cl2)) range_acquired.push_back(cl2);
                }
              }
            }
          }
        }


        if (do_verify) {
          // TODO: Synchronize marked info from global

          // Verify
          verify(cl);

          // Commit newly marked info to global
          if (!cfg_single_threaded) {
            if (marked_outgoing.size() > outgoing_threshold || ++cycles_not_synched>cycles_threshold) {
              if (sync_marked(false)) cycles_not_synched=0;
            }
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

//   /// Parse formula and certificate
//   void do_parsing(istream &cnf_in, istream &drat_in);

  /// Perform verification, using the specified number of threads.
  void do_verification(size_t num_threads);

private:
  /**
   * Write out the proof backwards.
   * @param include_lemmas True to also include lemmas into proofs, false to only write proof (used for split lemmas and proofs)
   * @param out Stream to dump proof to
   *
   * @pre Proofs must have been recorded, i.e., ::cfg_no_grat == false
   */
  template<bool include_lemmas, bool binary> void dump_proof_aux(ostream &out);

  /**
   * Write out the (marked) lemmas forwards.
   * Used to generate the lemmas part for split lemmas and proof format.
   * @param out Stream to dump lemmas to
   */
  void dump_lemmas(ostream &out);


public:
  /**
   * Write out the proof including lemmas.
   *
   * @pre Proofs must have been recorded, i.e., ::cfg_no_grat == false
   * @param out Stream to dump proof to
   */
  void dump_proof(ostream &out);


  /**
   * Write out split proof
   *
   * @pre Proofs must have been recorded, i.e., ::cfg_no_grat == false
   * @param lout Stream to dump lemmas
   * @param pout Stream to dump proofs
   */
  void dump_split_proof(ostream &lout, ostream &pout);
};

// void VController::do_parsing(istream& cnf_in, istream& drat_in) {
//   Parser parser;
//
//   with_timing("Parsing formula",[&] () {
//     parser.parse_dimacs(cnf_in);
//   });
//
//   with_timing("Parsing proof",[&] () {
//     parser.parse_proof(drat_in);
//   });
// }


void VController::do_parallel_bwd(size_t num_threads) {
  if (num_threads>1) clog<<"c Checking with "<<num_threads<<" parallel threads"<<endl; else clog<<"c Single threaded mode"<<endl;
  assert(num_threads>0);
  // Auxiliary verifiers, initialized to copies of main verifier
  vector<Verifier> aux_vrfs(num_threads - 1,main_vrf);

  vector<thread> aux_threads;

  for (size_t i=0;i<num_threads-1;++i) {
    Verifier *vrf = &aux_vrfs[i];
    aux_threads.push_back(thread([vrf, num_threads] () { vrf->bwd_pass(false); }));
  }

  main_vrf.bwd_pass(cfg_show_progress_bar);
  clog<<"c Waiting for aux-threads ..."; clog.flush();
  for (auto &tr : aux_threads) tr.join();
  clog<<"done"<<endl;

  // Synchronize vmarked on forward trail, and clause marking information.
  for (size_t i=0; i<num_threads-1;++i) {
    glb.join_vmarked(aux_vrfs[i].get_fwd_vmarked());
    if (!cfg_single_threaded) aux_vrfs[i].sync_marked(true);
  }
  glb.join_vmarked(main_vrf.get_fwd_vmarked());
  if (!cfg_single_threaded) main_vrf.sync_marked(true);




  // Log number of verified lemmas, compute variance
  {
    clog<<"c Lemmas processed by threads: ";
    double mean = main_vrf.get_cnt_verified();

    clog<<main_vrf.get_cnt_verified()<<" ";

    for (size_t i=0; i<num_threads-1;++i) {
      size_t cv = aux_vrfs[i].get_cnt_verified();

      mean+=cv;
      clog<<cv<<" ";
    }

    mean=mean / num_threads;

    double sumsq = abs(main_vrf.get_cnt_verified() - mean) / mean;
    for (size_t i=0; i<num_threads-1;++i) {
      size_t cv = aux_vrfs[i].get_cnt_verified();
      sumsq += abs(cv - mean) / mean;
    }

    clog<<"mdev: "<< sumsq / num_threads << endl;
  }
}



void VController::do_verification(size_t num_threads) {
  sdata=new Synch_Data(); // FIXME: Memory leak?
  main_vrf.init_after_parsing(sdata);

  pos_t cpos = with_timing<pos_t>("Forward pass",[&] {return main_vrf.fwd_pass();});
//   pos_t cpos = main_vrf.fwd_pass();

  if (cpos) {
    glb.init_after_fwd(cpos,main_vrf.get_trail());
#ifdef WITH_PROFILING
    ProfilerStart("/tmp/gratgen.prof");
#endif
    with_timing_ml("Backward pass",[&] {do_parallel_bwd(num_threads);},&stat_bwd_checking_time);
#ifdef WITH_PROFILING
    ProfilerStop();
#endif
  } else {
    clog<<"c Trivial conflict in clauses"<<endl;
  }

}

/**
 * Contains functions to output a GRAT proof.
 *
 * @param binary True if the proof is output in binary (split) format
 *
 */
template<bool binary> class Proof_Writer {
private:
  // Current item data
  vector<int32_t> data;
  // Current item type
  item_type ty = item_type::INVALID;
  // Output stream
  ostream &out;

  // Buffer for binary write-out. Seems to be faster then using put on ostream.
  vector<ostream::char_type> buf;

public:
  /// Constructor
  Proof_Writer(ostream &_out) : data(), out(_out), buf() {}

public:
  /// Write identifier
  void write_id(size_t id) {data.push_back(id);}
  /// Write counter
  void write_cnt(size_t c) {data.push_back(c);}
  /// Write literal
  void write_lit(lit_t l) {data.push_back(l);}
  /// Write zero
  void write_Z() {data.push_back(0);}

private:
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

  inline void write_out() {
    if (binary) {
      // Write in reverse
      size_t i=data.size();

      while (i) {
        --i;
        put32(data[i]);
      }
      put32(ty);
      if (buf.size()>=cfg_out_buf_size_threshold) flush_buf();
    } else {
      // TODO: Also buffer in text mode!
      out<<ty<<" ";
      for (auto x : data) out<<x<<" ";
      out<<(data.size() + 1)<<'\n';
    }
  }

  void close_current() {
    if (ty != item_type::INVALID && data.size()) {
      if (ty == item_type::DELETION || ty == item_type::UNIT_PROP) write_Z();

      write_out();
      ty = item_type::INVALID;
    }
    data.clear();
  }

public:
  /**
   * Write deletion. Summarizes adjacent deletions.
   */
  void write_del(size_t id) {
    if (ty!=item_type::DELETION) {
      close_current();
      ty=item_type::DELETION;
    }
    write_id(id);
  }

  /**
   * Write unit propagation. Summarizes adjacent unit propagations.
   */
  void write_uprop(size_t id) {
    if (ty!=item_type::UNIT_PROP) {
      close_current();
      ty=item_type::UNIT_PROP;
    }
    write_id(id);
  }

  /**
   * Start writing an item of specified type.
   * @param _ty Type of item. Must not be @see item_type::DELETION or @see item_type::UNIT_PROP, these items are inserted automatically, triggered by invocations of @see write_del and @see write_uprop.
   */
  void start_ty(item_type _ty) {
    close_current();
    ty=_ty;
  }

  /**
   * Close current item and flush writer.
   */
  void close() {
    close_current();
    flush_buf();
    out.flush();
  }
};


template<bool include_lemmas, bool binary> void VController::dump_proof_aux(ostream &out) {
  assert(!cfg_no_grat);

  Proof_Writer<binary> prw(out);

  // Conflict clause
  assert(glb.get_conflict());

  prw.start_ty(item_type::CONFLICT);
  prw.write_id(clid(glb.get_conflict()));

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
          if (sdata->is_marked(cl) || glb.is_formula_clause(cl)) {
            prw.write_del(clid(cl));
          }
        }
      } else {
        if (item.has_tr_pos()) {
          // If clause is principal clause on forward trail, dump v-marked clauses on forward trail and adjust tri
          size_t ntri = item.get_trpos();
          assert(ntri < tri);

          for (size_t j=ntri;j<tri;++j) {
            auto &tritem = glb.get_fwd_trail()[j];
            if (tritem.second) {
              prw.write_uprop(tritem.first);
            }
          }
          tri = ntri;
        }

        if (sdata->is_marked(cl)) {
          // Dump proof
          size_t j=0;

          vector<cdb_t> &prf = sdata->proof_of(cl);
          assert(prf.size() > 0);


          // TODO/FIXME Store proofs in more structured way, such that this clause-inserting hack becomes unnecessary!
          // Item type

          item_type itt = static_cast<item_type>(prf[j++]);

          assert(itt == item_type::RAT_LEMMA || itt == item_type::RUP_LEMMA);


          prw.start_ty(itt);

          if (itt == item_type::RAT_LEMMA) {
            prw.write_lit(prf[j++]);
          }

          prw.write_id(clid(cl));

          if (include_lemmas) {
            // Dump clause
            for (lit_t *l = cl;*l;++l) {prw.write_lit(*l);}
            prw.write_Z();
          }

          // Dump remaining proof
          for (;j<prf.size();++j) {prw.write_id(prf[j]); }
        }
      }
    }
  }


  // Initial unit propagations. TODO: Redundant, outsource to dump_unit_props(start,end) function.
  {
    for (size_t j=0;j<tri;++j) {
      size_t id = glb.get_fwd_trail()[j].first;
      bool vmarked = glb.get_fwd_trail()[j].second;

      assert(id < glb.get_fst_lemma_id());
      if (vmarked) {
        prw.write_uprop(id);
      }
    }
  }

  // RAT counts
  prw.start_ty(item_type::RAT_COUNTS);

  auto &rc = sdata->get_rat_counts();

  for (lit_t l=rc.lbegin(); l<rc.lend();++l) {
    size_t c = rc[l];
    if (c) {
      prw.write_lit(l); prw.write_cnt(c);
    }
  }
  prw.write_Z();
  prw.close();
}


void VController::dump_lemmas(ostream &out) {
  for (size_t i=glb.get_fst_prf_item();i<glb.get_num_items();++i) {
    item_t &item = glb.get_item(i);

    if (!item.is_erased()) {
      lit_t *cl = glb.get_db().p2c(item.get_pos());

      if (!item.is_deletion() && sdata->is_marked(cl)) {
        // Dump clause
        //out<<"c id "<<clid(cl)<<endl; // TODO/FIXME: For debugging only

        for (lit_t *l = cl;*l;++l) {out<<*l<<" "; }
        out<<"0"<<endl;
      }
    }
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


  dump_proof_aux<true,false>(out);
}


void VController::dump_split_proof(ostream &lout, ostream &pout) {
  assert(!cfg_no_grat);

  // Lemmas
  dump_lemmas(lout);

  // Proof
  pout<<"GRATproofonlybt "<<sizeof(cdb_t)<<" 0"<<endl;
  dump_proof_aux<false,true>(pout);
}


/// Print usage information
void print_usage() {
  cerr<<"Usage gratgen <dimacs-file> <proof-file> <options>"<<endl;
    cerr<<"Options:"<<endl;
    cerr<<"  -u, --no-core-first         Normal (no core first) unit propagation"<<endl;
    cerr<<"  -o name                     Name of GRAT-file"<<endl;
    cerr<<"  -l name                     Name of lemmas-file, activates split-proof mode"<<endl;
    cerr<<"  -p, --no-deletion           Ignore deletion of clauses"<<endl;
    cerr<<"  -j, --num-parallel          Number of parallel threads to use. Default 1."<<endl;
    cerr<<"      --assume-nodup          Assume that clauses contain no duplicate literals"<<endl;
    cerr<<"      --no-progress-bar       Do not show fancy progress bar"<<endl;
    cerr<<"      --single-del            Do not summarize deletion items"<<endl;
    cerr<<"      --[no-]premark-formula  Mark clauses of initial formula"<<endl;
    cerr<<"      --[no-]rat-run-h        Use RAT run heuristics"<<endl;
    cerr<<"  -b, --[no-]binary-drat      Use binary DRAT format"<<endl;
}

/// Print sizes of data types used internally
void print_info() {
  clog<<"c sizeof(cdb_t) = "<<sizeof(cdb_t)<<endl;
  clog<<"c sizeof(cdb_t*) = "<<sizeof( cdb_t* )<<endl;
}

/// Main function
int main(int argc, char **argv) {
  auto main_start_time = chrono::steady_clock::now();

  print_info();

  if (argc<3) {print_usage(); return 2;}

  string dimacs_file = argv[1];
  string proof_file = argv[2];
  string grat_file=""; cfg_no_grat=true;
  string lemmas_file="";

  size_t num_parallel = 1; //thread::hardware_concurrency();

  for (int i=3;i<argc;++i) {
    string a = argv[i];

    if (a=="-u" || a=="--no-core-first") cfg_core_first = false;
    else if (a=="-p" || a=="--no-deletion") cfg_ignore_deletion = true;
    else if (           a=="--assume-nodup") cfg_assume_nodup = true;
    else if (           a=="--no-progress-bar") cfg_show_progress_bar = false;
    else if (           a=="--single-del") cfg_summarize_deletions = false;
    else if (           a=="--premark-formula") cfg_premark_formula = true;
    else if (           a=="--no-premark-formula") cfg_premark_formula = false;
    else if (           a=="--no-rat-run-h") cfg_rat_run_heuristics = false;
    else if (a=="-b" || a=="--binary-drat") cfg_binary_drat = true;
    else if (           a=="--no-binary-drat") cfg_binary_drat = false;
    else if (a=="-j" || a=="--num_parallel") {
      ++i; if (i>=argc) {cerr<<"Expecting argument for "<<a<<endl; fail();}
      num_parallel = stoul(argv[i]);
      if (!num_parallel) {cerr<<"Invalid number of parallel threads "<<num_parallel<<endl; fail();}
    } else if (a=="-o") {
      ++i; if (i>=argc) {cerr<<"Expecting argument for -o"<<endl; fail();}
      grat_file=argv[i];
      cfg_no_grat=false;
    } else if (a=="-l") {
      ++i; if (i>=argc) {cerr<<"Expecting argument for -l"<<endl; fail();}
      lemmas_file=argv[i];
    } else {
      cerr<<"Unknown command line argument: "<<a<<endl; fail();
    }
  }

  cfg_single_threaded = (num_parallel==1);


  ofstream grat_out;
  ofstream lemmas_out;
  bool split_proof_mode = (lemmas_file!="");

  if (split_proof_mode) {
    if (cfg_no_grat) { cerr<<"Missing -o option (but found -l option)"<<endl; fail(); }
    clog<<"c Operating in split proof mode"<<endl;
    lemmas_out.open(lemmas_file, ios_base::out | ios_base::trunc);
    lemmas_out.imbue(locale::classic());
    lemmas_out.exceptions(lemmas_out.badbit | lemmas_out.failbit);
    lemmas_out.flush();

    grat_out.open(grat_file, ios_base::out | ios_base::binary  | ios_base::trunc);
    grat_out.imbue(locale::classic());
    grat_out.exceptions(grat_out.badbit | grat_out.failbit);
    grat_out.flush();
  } else if (!cfg_no_grat) {
    grat_out.open(grat_file, ios_base::out | ios_base::trunc);
    grat_out.imbue(locale::classic());
    grat_out.exceptions(grat_out.badbit | grat_out.failbit);
    grat_out.flush();
  }


  if (!cfg_core_first) clog<<"c Disabled core-first unit propagation"<<endl;
  if (cfg_rat_run_heuristics) clog<<"c Using RAT run heuristics"<<endl;
  if (cfg_premark_formula) clog<<"c Pre-marking formula"<<endl;
  if (cfg_ignore_deletion) clog<<"c Ignoring deletions"<<endl;

  // Parsing
  {
    Parser parser;
    auto parsing_start_time = chrono::steady_clock::now();

    with_timing("Parsing formula",[&] () {
      ifstream fs(dimacs_file,ifstream::in);
      parser.parse_dimacs(fs);
      fs.close();
    });

    if (cfg_binary_drat) {
      with_timing("Parsing proof (binary format)",[&] () {
        ifstream fs(proof_file,ios::in | ios::binary);
        parser.bin_parse_proof(fs);
        fs.close();
      });
    } else {
      with_timing("Parsing proof (ASCII format)",[&] () {
        ifstream fs(proof_file,ifstream::in);
        parser.parse_proof(fs);
        fs.close();
      });
    }

    stat_parsing_time = chrono::duration_cast<chrono::milliseconds>( chrono::steady_clock::now() - parsing_start_time);
  }

  // Verification
  auto checking_start_time = chrono::steady_clock::now();
  VController vctl;
  vctl.do_verification(num_parallel);
  stat_checking_time = chrono::duration_cast<chrono::milliseconds>( chrono::steady_clock::now() - checking_start_time);

  stat_overall_vrf_time = chrono::duration_cast<chrono::milliseconds>( chrono::steady_clock::now() - main_start_time);

  if (!cfg_no_grat) {
    if (split_proof_mode) {
      // Write lemmas and proof file
      with_timing("Writing split lemmas and proof",[&] () {vctl.dump_split_proof(lemmas_out, grat_out); lemmas_out.close(); grat_out.close(); },&stat_writing_time);
    } else {
      // Write proof file
      with_timing("Writing combined proof",[&] () {vctl.dump_proof(grat_out); grat_out.close();},&stat_writing_time);
    }
  }

  stat_overall_time = chrono::duration_cast<chrono::milliseconds>( chrono::steady_clock::now() - main_start_time);

  clog<<"s VERIFIED"<<endl;

  clog<<"c Timing statistics (ms)"<<endl;
  clog<<"c Parsing:  "<<stat_parsing_time.count()<<endl;
  clog<<"c Checking: "<<stat_checking_time.count()<<endl;
  clog<<"c   * bwd:  "<<stat_bwd_checking_time.count()<<endl;
  clog<<"c Writing:  "<<stat_writing_time.count()<<endl;
  clog<<"c Overall:  "<<stat_overall_time.count()<<endl;
  clog<<"c   * vrf:  "<<stat_overall_vrf_time.count()<<endl;
  clog<<endl;
  clog<<"c Lemma statistics"<<endl;
  clog<<"c RUP lemmas:  "<<stat_rup_lemmas<<endl;
  clog<<"c RAT lemmas:  "<<stat_rat_lemmas<<endl;
  clog<<"c   RAT run heuristics:   "<<stat_rat_run_h<<endl;
  clog<<"c Total lemmas:  "<<(stat_rup_lemmas + stat_rat_lemmas)<<endl;
  clog<<endl;
  clog<<"c Size statistics (bytes)"<<endl;
  clog<<"c Number of clauses: "<<stat_num_clauses<<endl;
  clog<<"c Clause DB size:  "<<stat_db_size<<endl;
  clog<<"c Item list:       "<<stat_itemlist_size<<endl;
  clog<<"c Pivots store:    "<<stat_pivots_size<<endl;

#ifdef WITH_DBG_STAT
  clog<<"c Debugging statistics"<<endl;
  clog<<"c stat_uprop_c1 = "<<dbg_stat_uprop_c1<<endl;
  clog<<"c stat_uprop_c2 = "<<dbg_stat_uprop_c2<<endl;
  clog<<"c stat_uprop_c3 = "<<dbg_stat_uprop_c3<<endl;
#endif



  return 0;
}
