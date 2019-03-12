theory IsaSAT_Arena
imports IsaSAT_Literals
  Watched_Literals.WB_More_Refinement_List
  Watched_Literals.WB_Word_Assn
begin


subsection \<open>The memory representation: Arenas\<close>


text \<open>
We implement an ``arena'' memory representation: This is a flat representation of clauses, where
all clauses and their headers are put one after the other. A lot of the work done here could be done
automatically by a C compiler (see paragraph on Cadical below).

While this has some advantages from a performance point of view compared to an array of arrays, it
allows to emulate pointers to the middle of array with extra information put before the pointer.
This is an optimisation that is considered as important (at least according to Armin Biere).

In Cadical, the representation is done that way although it is implicit by putting an array into a
structure (and rely on UB behaviour to make sure that the array is ``inlined'' into the structure).
Cadical also uses another trick: the array is but inside a union. This union contains either the
clause or a pointer to the new position if it has been moved (during GC-ing). There is no
way for us to do so in a type-safe manner that works both for \<^typ>\<open>uint64\<close> and \<^typ>\<open>nat\<close> (unless we
know some details of the implementation). For \<^typ>\<open>uint64\<close>, we could use the space used by the
headers. However, it is not clear if we want to do do, since the behaviour would change between the
two types, making a comparison impossible. This means that half of the blocking literals will be
lost (if we iterate over the watch lists) or all (if we iterate over the clauses directly).

The order in memory is in the following order:
  \<^enum> the saved position (is optional in cadical too);
  \<^enum> the status;
  \<^enum> the activity;
  \<^enum> the LBD;
  \<^enum> the size;
  \<^enum> the clause.

Remark that the information can be compressed to reduce the size in memory:
  \<^enum> the saved position can be skipped for short clauses;
  \<^enum> the LBD will most of the time be much shorter than a 32-bit integer, so only an
    approximation can be kept and the remaining bits be reused;
  \<^enum> the activity is not kept by cadical (to use instead a MTF-like scheme).

As we are already wasteful with memory, we implement the first optimisation. Point two can be
implemented automatically by a (non-standard-compliant) C compiler.


In our case, the refinement is done in two steps:
  \<^enum> First, we refine our clause-mapping to a big list. This list contains the original elements.
    For type safety, we introduce a datatype that enumerates all possible kind of elements.
  \<^enum> Then, we refine all these elements to uint32 elements.

In our formalisation, we distinguish active clauses (clauses that are not marked to be deleted) from
dead clauses (that have been marked to be deleted but can still be accessed). Any dead clause can be
removed from the addressable clauses (\<^term>\<open>vdom\<close> for virtual domain). Remark that we actually do not
need the full virtual domain, just the list of all active position (TODO?).

Remark that in our formalisation, we don't (at least not yet) plan to reuse freed spaces
(the predicate about dead clauses must be strengthened to do so). Due to the fact that an arena
is very different from an array of clauses, we refine our data structure by hand to the long list
instead of introducing refinement rules. This is mostly done because iteration is very different
(and it does not change what we had before anyway).

Some technical details: due to the fact that we plan to refine the arena to uint32 and that our
clauses can be tautologies, the size does not fit into uint32 (technically, we have the bound
\<^term>\<open>uint32_max +1\<close>). Therefore, we restrict the clauses to have at least length 2 and we keep
\<^term>\<open>length C - 2\<close> instead of \<^term>\<open>length C\<close> (same for position saving). If we ever add a
preprocessing path that removes tautologies, we could get rid of these two limitations.


To our own surprise, using an arena (without position saving) was exactly as fast as the our former
resizable array of arrays. We did not expect this result since:
  \<^enum> First, we cannot use \<^typ>\<open>uint32\<close> to iterate over clauses anymore (at least no without an
  additional trick like considering a slice).
  \<^enum> Second, there is no reason why MLton would not already use the trick for array.

(We assume that there is no gain due the order in which we iterate over clauses, which seems a
reasonnable assumption, even when considering than some clauses will subsume the previous one, and
therefore, have a high chance to be in the same watch lists).

We can mark clause as used. This trick is used to implement a MTF-like scheme to keep clauses.
\<close>


subsubsection \<open>Status of a clause\<close>

datatype clause_status = IRRED | LEARNED | DELETED

instance clause_status :: heap
proof standard
  let ?f = \<open>(\<lambda>x. case x of IRRED \<Rightarrow> (0::nat) | LEARNED \<Rightarrow> 1 | DELETED \<Rightarrow> 2)\<close>
  have \<open>inj ?f\<close>
    by (auto simp: inj_def split: clause_status.splits)
  then show \<open>\<exists>f. inj (f:: clause_status \<Rightarrow> nat)\<close>
    by blast
qed

instantiation clause_status :: default
begin

definition default_clause_status where \<open>default_clause_status = DELETED\<close>
instance by standard

end

abbreviation clause_status_assn where
  \<open>clause_status_assn \<equiv> (id_assn :: clause_status \<Rightarrow> _)\<close>

lemma IRRED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return IRRED), uncurry0 (RETURN IRRED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

lemma LEARNED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return LEARNED), uncurry0 (RETURN LEARNED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

lemma DELETED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return DELETED), uncurry0 (RETURN DELETED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto


subsubsection \<open>Definition\<close>

text \<open>The following definitions are the offset between the beginning of the clause and the
specific headers before the beginning of the clause. Remark that the first offset is not always
valid. Also remark that the fields are \<^emph>\<open>before\<close> the actual content of the clause.
\<close>
definition POS_SHIFT :: nat where
  \<open>POS_SHIFT = 5\<close>

definition STATUS_SHIFT :: nat where
  \<open>STATUS_SHIFT = 4\<close>

definition ACTIVITY_SHIFT :: nat where
  \<open>ACTIVITY_SHIFT = 3\<close>

definition LBD_SHIFT :: nat where
  \<open>LBD_SHIFT = 2\<close>

definition SIZE_SHIFT :: nat where
  \<open>SIZE_SHIFT = 1\<close>

definition MAX_LENGTH_SHORT_CLAUSE :: nat where
  [simp]: \<open>MAX_LENGTH_SHORT_CLAUSE = 4\<close>

definition is_short_clause where
  [simp]: \<open>is_short_clause C \<longleftrightarrow> length C \<le> MAX_LENGTH_SHORT_CLAUSE\<close>

abbreviation is_long_clause where
  \<open>is_long_clause C \<equiv> \<not>is_short_clause C\<close>

definition header_size :: \<open>nat clause_l \<Rightarrow> nat\<close> where
   \<open>header_size C = (if is_short_clause C then 4 else 5)\<close>

lemmas SHIFTS_def = POS_SHIFT_def STATUS_SHIFT_def ACTIVITY_SHIFT_def LBD_SHIFT_def SIZE_SHIFT_def

lemma (in -) ACTIVITY_SHIFT_hnr:
  \<open>(uncurry0 (return 3), uncurry0 (RETURN ACTIVITY_SHIFT) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: ACTIVITY_SHIFT_def uint64_nat_rel_def br_def)
lemma (in -) STATUS_SHIFT_hnr:
  \<open>(uncurry0 (return 4), uncurry0 (RETURN STATUS_SHIFT) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: STATUS_SHIFT_def uint64_nat_rel_def br_def)


(*TODO is that still used?*)
lemma arena_shift_distinct:
  \<open>i >  3 \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - LBD_SHIFT\<close>
  \<open>i >  3 \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - ACTIVITY_SHIFT\<close>
  \<open>i >  3 \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - STATUS_SHIFT\<close>
  \<open>i >  3 \<Longrightarrow> i - LBD_SHIFT \<noteq> i - ACTIVITY_SHIFT\<close>
  \<open>i >  3 \<Longrightarrow> i - LBD_SHIFT \<noteq> i - STATUS_SHIFT\<close>
  \<open>i >  3 \<Longrightarrow> i - ACTIVITY_SHIFT \<noteq> i - STATUS_SHIFT\<close>

  \<open>i >  4 \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - POS_SHIFT\<close>
  \<open>i >  4 \<Longrightarrow> i - LBD_SHIFT \<noteq> i - POS_SHIFT\<close>
  \<open>i >  4 \<Longrightarrow> i - ACTIVITY_SHIFT \<noteq> i - POS_SHIFT\<close>
  \<open>i >  4 \<Longrightarrow> i - STATUS_SHIFT \<noteq> i - POS_SHIFT\<close>

  \<open>i >  3 \<Longrightarrow> j >  3 \<Longrightarrow> i - SIZE_SHIFT = j - SIZE_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i >  3 \<Longrightarrow> j >  3 \<Longrightarrow> i - LBD_SHIFT = j - LBD_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i >  4 \<Longrightarrow> j >  4 \<Longrightarrow> i - ACTIVITY_SHIFT = j - ACTIVITY_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i >  3 \<Longrightarrow> j >  3 \<Longrightarrow> i - STATUS_SHIFT = j - STATUS_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i >  4 \<Longrightarrow> j >  4 \<Longrightarrow> i - POS_SHIFT = j - POS_SHIFT \<longleftrightarrow> i = j\<close>

  \<open>i \<ge> header_size C \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - LBD_SHIFT\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - ACTIVITY_SHIFT\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - STATUS_SHIFT\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> i - LBD_SHIFT \<noteq> i - ACTIVITY_SHIFT\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> i - LBD_SHIFT \<noteq> i - STATUS_SHIFT\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> i - ACTIVITY_SHIFT \<noteq> i - STATUS_SHIFT\<close>

  \<open>i \<ge> header_size C \<Longrightarrow> is_long_clause C \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - POS_SHIFT\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> is_long_clause C \<Longrightarrow> i - LBD_SHIFT \<noteq> i - POS_SHIFT\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> is_long_clause C \<Longrightarrow> i - ACTIVITY_SHIFT \<noteq> i - POS_SHIFT\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> is_long_clause C \<Longrightarrow> i - STATUS_SHIFT \<noteq> i - POS_SHIFT\<close>

  \<open>i \<ge> header_size C \<Longrightarrow> j \<ge> header_size C' \<Longrightarrow> i - SIZE_SHIFT = j - SIZE_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> j \<ge> header_size C' \<Longrightarrow> i - LBD_SHIFT = j - LBD_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> j \<ge> header_size C' \<Longrightarrow> i - ACTIVITY_SHIFT = j - ACTIVITY_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> j \<ge> header_size C' \<Longrightarrow> i - STATUS_SHIFT = j - STATUS_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> j \<ge> header_size C' \<Longrightarrow> is_long_clause C \<Longrightarrow> is_long_clause C' \<Longrightarrow>
     i - POS_SHIFT = j - POS_SHIFT \<longleftrightarrow> i = j\<close>
  unfolding POS_SHIFT_def STATUS_SHIFT_def ACTIVITY_SHIFT_def LBD_SHIFT_def SIZE_SHIFT_def
    header_size_def
  by (auto split: if_splits simp: is_short_clause_def)

lemma header_size_ge0[simp]: \<open>0 < header_size x1\<close>
  by (auto simp: header_size_def)

datatype arena_el =
  is_Lit: ALit (xarena_lit: \<open>nat literal\<close>) |
  is_LBD: ALBD (xarena_lbd: nat) |
  is_Act: AActivity (xarena_act: nat) |
  is_Size: ASize (xarena_length: nat)  |
  is_Pos: APos (xarena_pos: nat)  |
  is_Status: AStatus (xarena_status: clause_status) (xarena_used: bool)

type_synonym arena = \<open>arena_el list\<close>

definition xarena_active_clause :: \<open>arena \<Rightarrow> nat clause_l \<times> bool \<Rightarrow> bool\<close> where
  \<open>xarena_active_clause arena = (\<lambda>(C, red).
     (length C \<ge> 2 \<and>
       header_size C + length C = length arena \<and>
     (is_long_clause C \<longrightarrow>  (is_Pos (arena!(header_size C - POS_SHIFT)) \<and>
       xarena_pos(arena!(header_size C - POS_SHIFT)) \<le> length C - 2))) \<and>
     is_Status(arena!(header_size C - STATUS_SHIFT)) \<and>
        (xarena_status(arena!(header_size C - STATUS_SHIFT)) = IRRED \<longleftrightarrow> red) \<and>
        (xarena_status(arena!(header_size C - STATUS_SHIFT)) = LEARNED \<longleftrightarrow> \<not>red) \<and>
     is_LBD(arena!(header_size C - LBD_SHIFT)) \<and>
     is_Act(arena!(header_size C - ACTIVITY_SHIFT)) \<and>
     is_Size(arena!(header_size C - SIZE_SHIFT)) \<and>
     xarena_length(arena!(header_size C - SIZE_SHIFT)) + 2 = length C \<and>
     drop (header_size C) arena = map ALit C
  )\<close>

text \<open>As \<^term>\<open>(N\<propto>i, irred N i)\<close> is automatically simplified to \<^term>\<open>the (fmlookup N i)\<close>, we provide an
alternative definition that uses the result after the simplification.\<close>
lemma xarena_active_clause_alt_def:
  \<open>xarena_active_clause arena (the (fmlookup N i)) \<longleftrightarrow> (
     (length (N\<propto>i) \<ge> 2 \<and>
       header_size (N\<propto>i) + length (N\<propto>i) = length arena \<and>
     (is_long_clause (N\<propto>i) \<longrightarrow> (is_Pos (arena!(header_size (N\<propto>i) - POS_SHIFT)) \<and>
       xarena_pos(arena!(header_size (N\<propto>i) - POS_SHIFT)) \<le> length (N\<propto>i) - 2)) \<and>
     is_Status(arena!(header_size (N\<propto>i) - STATUS_SHIFT)) \<and>
        (xarena_status(arena!(header_size (N\<propto>i) - STATUS_SHIFT)) = IRRED \<longleftrightarrow> irred N i) \<and>
        (xarena_status(arena!(header_size (N\<propto>i) - STATUS_SHIFT)) = LEARNED \<longleftrightarrow> \<not>irred N i) \<and>
     is_LBD(arena!(header_size (N\<propto>i) - LBD_SHIFT)) \<and>
     is_Act(arena!(header_size (N\<propto>i) - ACTIVITY_SHIFT)) \<and>
     is_Size(arena!(header_size (N\<propto>i) - SIZE_SHIFT)) \<and>
     xarena_length(arena!(header_size (N\<propto>i) - SIZE_SHIFT)) + 2 = length (N\<propto>i) \<and>
     drop (header_size (N\<propto>i)) arena = map ALit (N\<propto>i)
  ))\<close>
proof -
  have C: \<open>the (fmlookup N i) = (N \<propto> i, irred N i)\<close>
    by simp
  show ?thesis
    apply (subst C)
    unfolding xarena_active_clause_def prod.case
    by meson
qed

text \<open>The extra information is required to prove ``separation'' between active and dead clauses. And
it is true anyway and does not require any extra work to prove.
TODO generalise LBD to extract from every clause?\<close>
definition arena_dead_clause :: \<open>arena \<Rightarrow> bool\<close> where
  \<open>arena_dead_clause arena \<longleftrightarrow>
     is_Status(arena!(4 - STATUS_SHIFT)) \<and> xarena_status(arena!(4 - STATUS_SHIFT)) = DELETED \<and>
     is_LBD(arena!(4 - LBD_SHIFT)) \<and>
     is_Act(arena!(4 - ACTIVITY_SHIFT)) \<and>
     is_Size(arena!(4 - SIZE_SHIFT))
\<close>

text \<open>When marking a clause as garbage, we do not care whether it was used or not.\<close>
definition extra_information_mark_to_delete where
  \<open>extra_information_mark_to_delete arena i = arena[i - STATUS_SHIFT := AStatus DELETED False]\<close>

text \<open>This extracts a single clause from the complete arena.\<close>
abbreviation clause_slice where
  \<open>clause_slice arena N i \<equiv> Misc.slice (i - header_size (N\<propto>i)) (i + length(N\<propto>i)) arena\<close>

abbreviation dead_clause_slice where
  \<open>dead_clause_slice arena N i \<equiv> Misc.slice (i - 4) i arena\<close>

text \<open>We now can lift the validity of the active and dead clauses to the whole memory and link it
the mapping to clauses and the addressable space.

In our first try, the predicated \<^term>\<open>xarena_active_clause\<close> took the whole
arena as parameter. This however turned out to make the proof about updates less modular, since the
slicing already takes care to ignore all irrelevant changes.
\<close>
definition valid_arena :: \<open>arena \<Rightarrow> nat clauses_l \<Rightarrow> nat set \<Rightarrow> bool\<close> where
  \<open>valid_arena arena N vdom \<longleftrightarrow>
    (\<forall>i \<in># dom_m N. i < length arena \<and> i \<ge> header_size (N\<propto>i) \<and>
         xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))) \<and>
    (\<forall>i \<in> vdom. i \<notin># dom_m N \<longrightarrow> (i < length arena \<and> i \<ge> 4 \<and>
      arena_dead_clause (dead_clause_slice arena N i)))
\<close>

lemma valid_arena_empty: \<open>valid_arena [] fmempty {}\<close>
  unfolding valid_arena_def
  by auto

definition arena_status where
  \<open>arena_status arena i = xarena_status (arena!(i - STATUS_SHIFT))\<close>

definition arena_used where
  \<open>arena_used arena i = xarena_used (arena!(i - STATUS_SHIFT))\<close>

definition arena_length where
  \<open>arena_length arena i = 2 + xarena_length (arena!(i - SIZE_SHIFT))\<close>

definition arena_lbd where
  \<open>arena_lbd arena i = xarena_lbd (arena!(i - LBD_SHIFT))\<close>

definition arena_act where
  \<open>arena_act arena i = xarena_act (arena!(i - ACTIVITY_SHIFT))\<close>

definition arena_pos where
  \<open>arena_pos arena i = 2 + xarena_pos (arena!(i - POS_SHIFT))\<close>

definition arena_lit where
  \<open>arena_lit arena i = xarena_lit (arena!i)\<close>


subsubsection \<open>Separation properties\<close>

text \<open>The following two lemmas talk about the minimal distance between two clauses in memory. They
are important for the proof of correctness of all update function.
\<close>
lemma minimal_difference_between_valid_index:
  assumes \<open>\<forall>i \<in># dom_m N. i < length arena \<and> i \<ge> header_size (N\<propto>i) \<and>
         xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close> and
    \<open>i \<in># dom_m N\<close> and \<open>j \<in># dom_m N\<close> and \<open>j > i\<close>
  shows \<open>j - i \<ge> length (N\<propto>i) + header_size (N\<propto>j)\<close>
proof (rule ccontr)
  assume False: \<open>\<not> ?thesis\<close>
  let ?Ci = \<open>the (fmlookup N i)\<close>
  let ?Cj = \<open>the (fmlookup N j)\<close>
  have
    1: \<open>xarena_active_clause (clause_slice arena N i) (N \<propto> i, irred N i)\<close> and
    2: \<open>xarena_active_clause (clause_slice arena N j) (N \<propto> j, irred N j)\<close> and
    i_le: \<open>i < length arena\<close> and
    i_ge: \<open>i \<ge> header_size(N\<propto>i)\<close>and
    j_le: \<open>j < length arena\<close> and
    j_ge: \<open>j \<ge> header_size(N\<propto>j)\<close>
    using assms
    by auto

  have Ci: \<open>?Ci = (N \<propto> i, irred N i)\<close> and Cj: \<open>?Cj = (N \<propto> j, irred N j)\<close>
    by auto

  have
    eq: \<open>Misc.slice i (i + length (N \<propto> i)) arena = map ALit (N \<propto> i)\<close> and
    \<open>length (N \<propto> i) - Suc 0 < length (N \<propto> i)\<close> and
    length_Ni: \<open>length (N\<propto>i) \<ge> 2\<close>
    using 1 i_ge
    unfolding xarena_active_clause_def extra_information_mark_to_delete_def prod.case
     apply simp_all
    apply force
    done

  from arg_cong[OF this(1), of \<open>\<lambda>n. n ! (length (N\<propto>i) - 1)\<close>] this(2-)
  have lit: \<open>is_Lit (arena ! (i + length(N\<propto>i) - 1))\<close>
    using i_le i_ge by (auto simp: map_nth slice_nth)
  have
    Cj2: \<open>2 \<le> length (N \<propto> j)\<close>
    using 2 j_le j_ge
    unfolding xarena_active_clause_def extra_information_mark_to_delete_def prod.case
    header_size_def
    by simp
  have headerj: \<open>header_size (N \<propto> j) \<ge> 4\<close>
    unfolding header_size_def by (auto split: if_splits)
  then have [simp]: \<open>header_size (N \<propto> j) - POS_SHIFT < length (N \<propto> j) + header_size (N \<propto> j)\<close>
    using Cj2
    by linarith
  have [simp]:
    \<open>is_long_clause (N \<propto> j) \<longrightarrow> j + (header_size (N \<propto> j) - POS_SHIFT) - header_size (N \<propto> j) = j - POS_SHIFT\<close>
    \<open>j + (header_size (N \<propto> j) - STATUS_SHIFT) - header_size (N \<propto> j) = j - STATUS_SHIFT\<close>
    \<open>j + (header_size (N \<propto> j) - SIZE_SHIFT) - header_size (N \<propto> j) = j - SIZE_SHIFT\<close>
    \<open>j + (header_size (N \<propto> j) - LBD_SHIFT) - header_size (N \<propto> j) = j - LBD_SHIFT\<close>
    \<open>j + (header_size (N \<propto> j) - ACTIVITY_SHIFT) - header_size (N \<propto> j) = j - ACTIVITY_SHIFT\<close>
    using Cj2 headerj unfolding POS_SHIFT_def STATUS_SHIFT_def LBD_SHIFT_def SIZE_SHIFT_def
      ACTIVITY_SHIFT_def
    by (auto simp: header_size_def)

   have
    pos: \<open>is_long_clause (N \<propto> j) \<longrightarrow> is_Pos (arena ! (j - POS_SHIFT))\<close> and
    st: \<open>is_Status (arena ! (j - STATUS_SHIFT))\<close> and
    size: \<open>is_Size (arena ! (j - SIZE_SHIFT))\<close> and
    lbd: \<open>is_LBD (arena ! (j - LBD_SHIFT))\<close> and
    act: \<open>is_Act (arena ! (j - ACTIVITY_SHIFT))\<close>
    using 2 j_le j_ge Cj2 headerj
    unfolding xarena_active_clause_def extra_information_mark_to_delete_def prod.case
    by (simp_all add: slice_nth)
  have False if ji: \<open>j - i \<ge> length (N\<propto>i)\<close>
  proof -
    have Suc3: \<open>3 = Suc (Suc (Suc 0))\<close>
      by auto
    have Suc4: \<open>4 = Suc (Suc (Suc (Suc 0)))\<close>
      by auto
    have Suc5: \<open>5 = Suc (Suc (Suc (Suc (Suc 0))))\<close>
      by auto
    have j_i_1[iff]:
      \<open>j - 1 = i + length (N \<propto> i) - 1 \<longleftrightarrow> j = i + length (N \<propto> i)\<close>
      \<open>j - 2 = i + length (N \<propto> i) - 1 \<longleftrightarrow> j = i + length (N \<propto> i) + 1\<close>
      \<open>j - 3 = i + length (N \<propto> i) - 1 \<longleftrightarrow> j = i + length (N \<propto> i) + 2\<close>
      \<open>j - 4 = i + length (N \<propto> i) - 1 \<longleftrightarrow> j = i + length (N \<propto> i) + 3\<close>
      \<open>j - 5 = i + length (N \<propto> i) - 1 \<longleftrightarrow> j = i + length (N \<propto> i) + 4\<close>
      using False that j_ge i_ge length_Ni unfolding Suc4 Suc5 header_size_def numeral_2_eq_2
      by (auto split: if_splits)
    have H4: \<open>Suc (j - i) \<le> length (N \<propto> i) + 4 \<Longrightarrow> j - i = length (N \<propto> i) \<or>
       j - i = length (N \<propto> i) + 1 \<or> j - i = length (N \<propto> i) + 2 \<or> j - i = length (N \<propto> i) + 3\<close>
      using False ji j_ge i_ge length_Ni unfolding Suc3 Suc4
      by (auto simp: le_Suc_eq header_size_def split: if_splits)
    have H5: \<open>Suc (j - i) \<le> length (N \<propto> i) + 5 \<Longrightarrow> j - i = length (N \<propto> i) \<or>
       j - i = length (N \<propto> i) + 1 \<or> j - i = length (N \<propto> i) + 2 \<or> j - i = length (N \<propto> i) + 3 \<or>
      (is_long_clause (N \<propto> j) \<and> j = i+length (N \<propto> i) + 4)\<close>
      using False ji j_ge i_ge length_Ni unfolding Suc3 Suc4
      by (auto simp: le_Suc_eq header_size_def split: if_splits)
    consider
       \<open>is_long_clause (N \<propto> j)\<close> \<open>j - POS_SHIFT = i + length(N\<propto>i) - 1\<close> |
       \<open>j - STATUS_SHIFT = i + length(N\<propto>i) - 1\<close> |
       \<open>j - LBD_SHIFT = i + length(N\<propto>i) - 1\<close> |
       \<open>j - ACTIVITY_SHIFT = i + length(N\<propto>i) - 1\<close> |
       \<open>j - SIZE_SHIFT = i + length(N\<propto>i) - 1\<close>
      using False ji j_ge i_ge length_Ni
      unfolding header_size_def not_less_eq_eq STATUS_SHIFT_def SIZE_SHIFT_def
       LBD_SHIFT_def ACTIVITY_SHIFT_def le_Suc_eq POS_SHIFT_def j_i_1
      apply (cases \<open>is_short_clause (N \<propto> j)\<close>)
      subgoal
        using H4 by auto
      subgoal
        using H5 by auto
      done
    then show False
      using lit pos st size lbd act
      by cases auto
  qed
  moreover have False if ji: \<open>j - i < length (N\<propto>i)\<close>
  proof -
    from arg_cong[OF eq, of \<open>\<lambda>xs. xs ! (j-i-1)\<close>]
    have \<open>is_Lit (arena ! (j-1))\<close>
      using that j_le i_le \<open>j > i\<close>
      by (auto simp: slice_nth)
    then show False
      using size unfolding SIZE_SHIFT_def by auto
  qed
  ultimately show False
    by linarith
qed

lemma minimal_difference_between_invalid_index:
  assumes \<open>valid_arena arena N vdom\<close> and
    \<open>i \<in># dom_m N\<close> and \<open>j \<notin># dom_m N\<close> and \<open>j \<ge> i\<close> and \<open>j \<in> vdom\<close>
  shows \<open>j - i \<ge> length (N\<propto>i) + 4\<close>
proof (rule ccontr)
  assume False: \<open>\<not> ?thesis\<close>
  let ?Ci = \<open>the (fmlookup N i)\<close>
  let ?Cj = \<open>the (fmlookup N j)\<close>
  have
    1: \<open>xarena_active_clause (clause_slice arena N i) (N \<propto> i, irred N i)\<close> and
    2: \<open>arena_dead_clause (dead_clause_slice arena N j)\<close> and
    i_le: \<open>i < length arena\<close> and
    i_ge: \<open>i \<ge> header_size(N\<propto>i)\<close>and
    j_le: \<open>j < length arena\<close> and
    j_ge: \<open>j \<ge> 4\<close>
    using assms unfolding valid_arena_def
    by auto

  have Ci: \<open>?Ci = (N \<propto> i, irred N i)\<close> and Cj:  \<open>?Cj = (N \<propto> j, irred N j)\<close>
    by auto

  have
    eq: \<open>Misc.slice i (i + length (N \<propto> i)) arena = map ALit (N \<propto> i)\<close> and
    \<open>length (N \<propto> i) - Suc 0 < length (N \<propto> i)\<close> and
    length_Ni: \<open>length (N\<propto>i) \<ge> 2\<close> and
    pos: \<open>is_long_clause (N \<propto> i) \<longrightarrow>
       is_Pos (arena ! (i - POS_SHIFT))\<close> and
    status: \<open>is_Status (arena ! (i - STATUS_SHIFT))\<close> and
    lbd: \<open>is_LBD (arena ! (i - LBD_SHIFT))\<close> and
    act: \<open>is_Act (arena ! (i - ACTIVITY_SHIFT))\<close> and
    size: \<open>is_Size (arena ! (i - SIZE_SHIFT))\<close> and
    st_init: \<open>(xarena_status (arena ! (i - STATUS_SHIFT)) = IRRED) = (irred N i)\<close> and
    st_learned: \<open>(xarena_status (arena ! (i - STATUS_SHIFT)) = LEARNED) = (\<not> irred N i)\<close>
    using 1 i_ge i_le
    unfolding xarena_active_clause_def extra_information_mark_to_delete_def prod.case
      unfolding STATUS_SHIFT_def LBD_SHIFT_def ACTIVITY_SHIFT_def SIZE_SHIFT_def POS_SHIFT_def
     apply (simp_all add: header_size_def slice_nth split: if_splits)
    apply force+
    done

  have
    st: \<open>is_Status (arena ! (j - STATUS_SHIFT))\<close> and
    del: \<open>xarena_status (arena ! (j - STATUS_SHIFT)) = DELETED\<close>
    using 2 j_le j_ge unfolding arena_dead_clause_def STATUS_SHIFT_def
    by (simp_all add: header_size_def slice_nth)
  consider
    \<open>j - STATUS_SHIFT \<ge> i\<close> |
    \<open>j - STATUS_SHIFT < i\<close>
    using False \<open>j \<ge> i\<close> unfolding STATUS_SHIFT_def
    by linarith
  then show False
  proof cases
    case 1
    then have \<open>j - STATUS_SHIFT < i + length (N\<propto>i)\<close>
      using \<open>j \<ge> i\<close> False j_ge
      unfolding not_less_eq_eq STATUS_SHIFT_def
      by simp
    with arg_cong[OF eq, of \<open>\<lambda>n. n ! (j - STATUS_SHIFT - i)\<close>]
    have lit: \<open>is_Lit (arena ! (j - STATUS_SHIFT))\<close>
      using 1  \<open>j \<ge> i\<close> i_le i_ge j_ge by (auto simp: map_nth slice_nth STATUS_SHIFT_def)
    with st
    show False by auto
  next
    case 2
    then consider
      \<open>j - STATUS_SHIFT = i - STATUS_SHIFT\<close> |
      \<open>j - STATUS_SHIFT = i - LBD_SHIFT\<close> |
      \<open>j - STATUS_SHIFT = i - ACTIVITY_SHIFT\<close> |
      \<open>j - STATUS_SHIFT = i - SIZE_SHIFT\<close> |
      \<open>is_long_clause (N \<propto> i)\<close> and \<open>j - STATUS_SHIFT = i - POS_SHIFT\<close>
      using \<open>j \<ge> i\<close>
      unfolding STATUS_SHIFT_def LBD_SHIFT_def ACTIVITY_SHIFT_def SIZE_SHIFT_def POS_SHIFT_def
      by force
    then show False
      apply cases
      subgoal using st status st_init st_learned del by auto
      subgoal using st lbd by auto
      subgoal using st act by auto
      subgoal using st size by auto
      subgoal using st pos by auto
      done
  qed
qed


text \<open>At first we had the weaker \<^term>\<open>i - j \<ge> 1\<close> which we replaced by \<^term>\<open>i - j \<ge> 4\<close>.
The former however was able to solve many more goals due to different handling between \<^term>\<open>1\<close>
(which is simplified to \<^term>\<open>Suc 0\<close>) and \<^term>\<open>4\<close> (which is not). Therefore, we replaced \<^term>\<open>4\<close>
by \<^term>\<open>Suc (Suc (Suc (Suc 0)))\<close>
\<close>
lemma minimal_difference_between_invalid_index2:
  assumes \<open>valid_arena arena N vdom\<close> and
    \<open>i \<in># dom_m N\<close> and \<open>j \<notin># dom_m N\<close> and \<open>j < i\<close> and \<open>j \<in> vdom\<close>
  shows \<open>i - j \<ge> Suc (Suc (Suc (Suc 0)))\<close> and
     \<open>is_long_clause (N \<propto> i) \<Longrightarrow> i - j \<ge> Suc (Suc (Suc (Suc (Suc 0))))\<close>
proof -
  let ?Ci = \<open>the (fmlookup N i)\<close>
  let ?Cj = \<open>the (fmlookup N j)\<close>
  have
    1: \<open>xarena_active_clause (clause_slice arena N i) (N \<propto> i, irred N i)\<close> and
    2: \<open>arena_dead_clause (dead_clause_slice arena N j)\<close> and
    i_le: \<open>i < length arena\<close> and
    i_ge: \<open>i \<ge> header_size(N\<propto>i)\<close>and
    j_le: \<open>j < length arena\<close> and
    j_ge: \<open>j \<ge> 4\<close>
    using assms unfolding valid_arena_def
    by auto

  have Ci: \<open>?Ci = (N \<propto> i, irred N i)\<close> and Cj:  \<open>?Cj = (N \<propto> j, irred N j)\<close>
    by auto

  have
    eq: \<open>Misc.slice i (i + length (N \<propto> i)) arena = map ALit (N \<propto> i)\<close> and
    \<open>length (N \<propto> i) - Suc 0 < length (N \<propto> i)\<close> and
    length_Ni: \<open>length (N\<propto>i) \<ge> 2\<close> and
    pos: \<open>is_long_clause (N \<propto> i) \<longrightarrow>
       is_Pos (arena ! (i - POS_SHIFT))\<close> and
    status: \<open>is_Status (arena ! (i - STATUS_SHIFT))\<close> and
    lbd: \<open>is_LBD (arena ! (i - LBD_SHIFT))\<close> and
    act: \<open>is_Act (arena ! (i - ACTIVITY_SHIFT))\<close> and
    size: \<open>is_Size (arena ! (i - SIZE_SHIFT))\<close> and
    st_init: \<open>(xarena_status (arena ! (i - STATUS_SHIFT)) = IRRED) \<longleftrightarrow> (irred N i)\<close> and
    st_learned: \<open> (xarena_status (arena ! (i - STATUS_SHIFT)) = LEARNED) \<longleftrightarrow> \<not>irred N i\<close>
    using 1 i_ge i_le
    unfolding xarena_active_clause_def extra_information_mark_to_delete_def prod.case
      unfolding STATUS_SHIFT_def LBD_SHIFT_def ACTIVITY_SHIFT_def SIZE_SHIFT_def POS_SHIFT_def
     apply (simp_all add: header_size_def slice_nth split: if_splits)
    apply force+
    done

  have
    st: \<open>is_Status (arena ! (j - STATUS_SHIFT))\<close> and
    del: \<open>xarena_status (arena ! (j - STATUS_SHIFT)) = DELETED\<close> and
    lbd': \<open>is_LBD (arena ! (j - LBD_SHIFT))\<close> and
    act': \<open>is_Act (arena ! (j - ACTIVITY_SHIFT))\<close> and
    size': \<open>is_Size (arena ! (j - SIZE_SHIFT))\<close>
    using 2 j_le j_ge unfolding arena_dead_clause_def SHIFTS_def
    by (simp_all add: header_size_def slice_nth)
  have 4: \<open>4 = Suc (Suc (Suc (Suc 0)))\<close>  and 5: \<open>5 = Suc (Suc (Suc (Suc (Suc 0))))\<close>
    by auto
  have [simp]: \<open>a < 4 \<Longrightarrow> j - Suc a = i - Suc 0 \<longleftrightarrow> i = j - a\<close> for a
    using \<open>i > j\<close> j_ge i_ge
    by (auto split: if_splits simp: not_less_eq_eq le_Suc_eq )
  have [simp]: \<open>Suc i - j = Suc a \<longleftrightarrow> i - j = a\<close> for a
    using \<open>i > j\<close> j_ge i_ge
    by (auto split: if_splits simp: not_less_eq_eq le_Suc_eq)


  show 1: \<open>i - j \<ge> Suc (Suc (Suc (Suc 0)))\<close> (is ?A)
  proof (rule ccontr)
    assume False: \<open>\<not>?A\<close>
    consider
        \<open>i - STATUS_SHIFT = j - STATUS_SHIFT\<close> |
        \<open>i - STATUS_SHIFT = j - LBD_SHIFT\<close> |
        \<open>i - STATUS_SHIFT = j - ACTIVITY_SHIFT\<close> |
        \<open>i - STATUS_SHIFT = j - SIZE_SHIFT\<close>
      using False \<open>i > j\<close> j_ge i_ge unfolding SHIFTS_def header_size_def 4
      by (auto split: if_splits simp: not_less_eq_eq le_Suc_eq )
    then show False
      apply cases
      subgoal using st status st_init st_learned del by auto
      subgoal using status lbd' by auto
      subgoal using status act' by auto
      subgoal using status size' by auto
      done
  qed

  show \<open>i - j \<ge> Suc (Suc (Suc (Suc (Suc 0))))\<close> (is ?A)
    if long: \<open>is_long_clause (N \<propto> i)\<close>
  proof (rule ccontr)
    assume False: \<open>\<not>?A\<close>

    have [simp]: \<open>a < 5 \<Longrightarrow> a' < 4 \<Longrightarrow> i - Suc a = j - Suc a' \<longleftrightarrow> i - a = j - a'\<close> for a a'
      using \<open>i > j\<close> j_ge i_ge long
      by (auto split: if_splits simp: not_less_eq_eq le_Suc_eq )
    have \<open>i - j = Suc (Suc (Suc (Suc 0)))\<close>
      using 1 \<open>i > j\<close> False j_ge i_ge long unfolding SHIFTS_def header_size_def 4
      by (auto split: if_splits simp: not_less_eq_eq le_Suc_eq)
    then have \<open>i - POS_SHIFT = j - SIZE_SHIFT\<close>
      using 1 \<open>i > j\<close> j_ge i_ge long unfolding SHIFTS_def header_size_def 4 5
      by (auto split: if_splits simp: not_less_eq_eq le_Suc_eq)
    then show False
      using pos long size'
      by auto
  qed
qed

lemma valid_arena_in_vdom_le_arena:
  assumes \<open>valid_arena arena N vdom\<close> and \<open>j \<in> vdom\<close>
  shows \<open>j < length arena\<close>
  using assms unfolding valid_arena_def
  by auto


subsubsection \<open>Updates\<close>

paragraph \<open>Mark to delete\<close>

lemma clause_slice_extra_information_mark_to_delete:
  assumes
    i: \<open>i \<in># dom_m N\<close> and
    ia: \<open>ia \<in># dom_m N\<close> and
    dom: \<open>\<forall>i \<in># dom_m N. i < length arena \<and> i \<ge> header_size (N\<propto>i) \<and>
         xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>
  shows
    \<open>clause_slice (extra_information_mark_to_delete arena i) N ia =
      (if ia = i then extra_information_mark_to_delete (clause_slice arena N ia) (header_size (N\<propto>i))
         else clause_slice arena N ia)\<close>
proof -
  have ia_ge: \<open>ia \<ge> header_size(N \<propto> ia)\<close> \<open>ia < length arena\<close> and
   i_ge:  \<open>i \<ge> header_size(N \<propto> i)\<close> \<open>i < length arena\<close>
    using dom ia i unfolding xarena_active_clause_def
    by auto

  show ?thesis
    using minimal_difference_between_valid_index[OF dom i ia] i_ge
    minimal_difference_between_valid_index[OF dom ia i] ia_ge
    by (cases \<open>ia < i\<close>)
     (auto simp: extra_information_mark_to_delete_def STATUS_SHIFT_def drop_update_swap
       Misc.slice_def header_size_def split: if_splits)
qed

lemma clause_slice_extra_information_mark_to_delete_dead:
  assumes
    i: \<open>i \<in># dom_m N\<close> and
    ia: \<open>ia \<notin># dom_m N\<close> \<open>ia \<in> vdom\<close> and
    dom: \<open>valid_arena arena N vdom\<close>
  shows
    \<open>arena_dead_clause (dead_clause_slice (extra_information_mark_to_delete arena i) N ia) =
      arena_dead_clause (dead_clause_slice arena N ia)\<close>
proof -
  have ia_ge: \<open>ia \<ge> 4\<close> \<open>ia < length arena\<close> and
   i_ge:  \<open>i \<ge> header_size(N \<propto> i)\<close> \<open>i < length arena\<close>
    using dom ia i unfolding valid_arena_def
    by auto
  show ?thesis
    using minimal_difference_between_invalid_index[OF dom i ia(1) _ ia(2)] i_ge ia_ge
    using minimal_difference_between_invalid_index2[OF dom i ia(1) _ ia(2)] ia_ge
    by (cases \<open>ia < i\<close>)
     (auto simp: extra_information_mark_to_delete_def STATUS_SHIFT_def drop_update_swap
       arena_dead_clause_def
       Misc.slice_def header_size_def split: if_splits)
qed

lemma length_extra_information_mark_to_delete[simp]:
  \<open>length (extra_information_mark_to_delete arena i) = length arena\<close>
  unfolding extra_information_mark_to_delete_def by auto

lemma valid_arena_mono: \<open>valid_arena ab ar vdom1 \<Longrightarrow> vdom2 \<subseteq> vdom1 \<Longrightarrow> valid_arena ab ar vdom2\<close>
  unfolding valid_arena_def
  by fast

lemma valid_arena_extra_information_mark_to_delete:
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close>
  shows \<open>valid_arena (extra_information_mark_to_delete arena i) (fmdrop i N) (insert i vdom)\<close>
proof -
  let ?arena = \<open>extra_information_mark_to_delete arena i\<close>
  have [simp]: \<open>i \<notin># remove1_mset i (dom_m N)\<close>
     \<open>\<And>ia. ia \<notin># remove1_mset i (dom_m N) \<longleftrightarrow> ia =i \<or> (i \<noteq> ia \<and> ia \<notin># dom_m N)\<close>
    using assms distinct_mset_dom[of N]
    by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
  have
    dom: \<open>\<forall>i\<in>#dom_m N.
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close> and
    dom': \<open>\<And>i. i\<in>#dom_m N \<Longrightarrow>
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>  and
    vdom: \<open>\<And>i. i\<in>vdom \<longrightarrow> i \<notin># dom_m N \<longrightarrow> 4 \<le> i \<and> arena_dead_clause (dead_clause_slice arena N i)\<close>
    using assms unfolding valid_arena_def by auto
  have \<open>ia\<in>#dom_m (fmdrop i N) \<Longrightarrow>
        ia < length ?arena \<and>
        header_size (fmdrop i N \<propto> ia) \<le> ia \<and>
        xarena_active_clause (clause_slice ?arena (fmdrop i N) ia) (the (fmlookup (fmdrop i N) ia))\<close> for ia
    using dom'[of ia] clause_slice_extra_information_mark_to_delete[OF i _ dom, of ia]
    by auto
  moreover have \<open>ia \<noteq> i \<longrightarrow> ia\<in>insert i vdom \<longrightarrow>
        ia \<notin># dom_m (fmdrop i N) \<longrightarrow>
        4 \<le> ia \<and> arena_dead_clause
         (dead_clause_slice (extra_information_mark_to_delete arena i) (fmdrop i N) ia)\<close> for ia
    using vdom[of ia] clause_slice_extra_information_mark_to_delete_dead[OF i _ _ arena, of ia]
    by auto
  moreover have \<open>4 \<le> i \<and> arena_dead_clause
         (dead_clause_slice (extra_information_mark_to_delete arena i) (fmdrop i N) i)\<close>
    using dom'[of i, OF i]
    unfolding arena_dead_clause_def xarena_active_clause_alt_def
      extra_information_mark_to_delete_def apply -
    by (simp_all add: SHIFTS_def header_size_def Misc.slice_def drop_update_swap min_def
         split: if_splits)
       force+
  ultimately show ?thesis
    using assms unfolding valid_arena_def
    by auto
qed

lemma valid_arena_extra_information_mark_to_delete':
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close>
  shows \<open>valid_arena (extra_information_mark_to_delete arena i) (fmdrop i N) vdom\<close>
  using valid_arena_extra_information_mark_to_delete[OF assms]
  by (auto intro: valid_arena_mono)


paragraph \<open>Removable from addressable space\<close>

lemma valid_arena_remove_from_vdom:
  assumes \<open>valid_arena arena N (insert i vdom)\<close>
  shows  \<open>valid_arena arena N vdom\<close>
  using assms valid_arena_def
  by (auto dest!: in_diffD)


paragraph \<open>Update activity\<close>

definition update_act where
  \<open>update_act C act arena = arena[C - ACTIVITY_SHIFT := AActivity act]\<close>

lemma clause_slice_update_act:
  assumes
    i: \<open>i \<in># dom_m N\<close> and
    ia: \<open>ia \<in># dom_m N\<close> and
    dom: \<open>\<forall>i \<in># dom_m N. i < length arena \<and> i \<ge> header_size (N\<propto>i) \<and>
         xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>
  shows
    \<open>clause_slice (update_act i act arena) N ia =
      (if ia = i then update_act (header_size (N\<propto>i)) act (clause_slice arena N ia)
         else clause_slice arena N ia)\<close>
proof -
  have ia_ge: \<open>ia \<ge> header_size(N \<propto> ia)\<close> \<open>ia < length arena\<close> and
   i_ge:  \<open>i \<ge> header_size(N \<propto> i)\<close> \<open>i < length arena\<close>
    using dom ia i unfolding xarena_active_clause_def
    by auto

  show ?thesis
    using minimal_difference_between_valid_index[OF dom i ia] i_ge
    minimal_difference_between_valid_index[OF dom ia i] ia_ge
    by (cases \<open>ia < i\<close>)
     (auto simp: extra_information_mark_to_delete_def STATUS_SHIFT_def drop_update_swap
       ACTIVITY_SHIFT_def update_act_def
       Misc.slice_def header_size_def split: if_splits)
qed

lemma length_update_act[simp]:
  \<open>length (update_act i act arena) = length arena\<close>
  by (auto simp: update_act_def)

lemma clause_slice_update_act_dead:
  assumes
    i: \<open>i \<in># dom_m N\<close> and
    ia: \<open>ia \<notin># dom_m N\<close> \<open>ia \<in> vdom\<close> and
    dom: \<open>valid_arena arena N vdom\<close>
  shows
    \<open>arena_dead_clause (dead_clause_slice (update_act i act arena) N ia) =
      arena_dead_clause (dead_clause_slice arena N ia)\<close>
proof -
  have ia_ge: \<open>ia \<ge> 4\<close> \<open>ia < length arena\<close> and
   i_ge:  \<open>i \<ge> header_size(N \<propto> i)\<close> \<open>i < length arena\<close>
    using dom ia i unfolding valid_arena_def
    by auto
  show ?thesis
    using minimal_difference_between_invalid_index[OF dom i ia(1) _ ia(2)] i_ge ia_ge
    using minimal_difference_between_invalid_index2[OF dom i ia(1) _ ia(2)] ia_ge
    by (cases \<open>ia < i\<close>)
     (auto simp: extra_information_mark_to_delete_def STATUS_SHIFT_def drop_update_swap
      arena_dead_clause_def update_act_def ACTIVITY_SHIFT_def
       Misc.slice_def header_size_def split: if_splits)
qed

lemma xarena_active_clause_update_act_same:
  assumes
    \<open>i \<ge> header_size (N \<propto> i)\<close> and
    \<open>i < length arena\<close> and
    \<open>xarena_active_clause (clause_slice arena N i)
     (the (fmlookup N i))\<close>
  shows \<open>xarena_active_clause (update_act (header_size (N\<propto>i)) act (clause_slice arena N i))
     (the (fmlookup N i))\<close>
  using assms
  by (cases \<open>is_short_clause (N \<propto> i)\<close>)
    (simp_all add: xarena_active_clause_alt_def update_act_def SHIFTS_def Misc.slice_def
    header_size_def)


lemma valid_arena_update_act:
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close>
  shows \<open>valid_arena (update_act i act arena) N vdom\<close>
proof -
  let ?arena = \<open>update_act i act arena\<close>
  have [simp]: \<open>i \<notin># remove1_mset i (dom_m N)\<close>
     \<open>\<And>ia. ia \<notin># remove1_mset i (dom_m N) \<longleftrightarrow> ia =i \<or> (i \<noteq> ia \<and> ia \<notin># dom_m N)\<close>
    using assms distinct_mset_dom[of N]
    by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
  have
    dom: \<open>\<forall>i\<in>#dom_m N.
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close> and
    dom': \<open>\<And>i. i\<in>#dom_m N \<Longrightarrow>
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>  and
    vdom: \<open>\<And>i. i\<in>vdom \<longrightarrow> i \<notin># dom_m N \<longrightarrow> 4 \<le> i \<and> arena_dead_clause (dead_clause_slice arena N i)\<close>
    using assms unfolding valid_arena_def by auto
  have \<open>ia\<in>#dom_m N \<Longrightarrow> ia \<noteq> i \<Longrightarrow>
        ia < length ?arena \<and>
        header_size (N \<propto> ia) \<le> ia \<and>
        xarena_active_clause (clause_slice ?arena N ia) (the (fmlookup N ia))\<close> for ia
    using dom'[of ia] clause_slice_update_act[OF i _ dom, of ia act]
    by auto
  moreover have \<open>ia = i \<Longrightarrow>
        ia < length ?arena \<and>
        header_size (N \<propto> ia) \<le> ia \<and>
        xarena_active_clause (clause_slice ?arena N ia) (the (fmlookup N ia))\<close> for ia
    using dom'[of ia] clause_slice_update_act[OF i _ dom, of ia act] i
    by (simp add: xarena_active_clause_update_act_same)
  moreover have \<open>ia\<in>vdom \<longrightarrow>
        ia \<notin># dom_m N \<longrightarrow>
        4 \<le> ia \<and> arena_dead_clause
         (dead_clause_slice (update_act i act arena) (fmdrop i N) ia)\<close> for ia
    using vdom[of ia] clause_slice_update_act_dead[OF i _ _ arena, of ia] i
    by auto
  ultimately show ?thesis
    using assms unfolding valid_arena_def
    by auto
qed

paragraph \<open>Update LBD\<close>

definition update_lbd where
  \<open>update_lbd C lbd arena = arena[C - LBD_SHIFT := ALBD lbd]\<close>


lemma clause_slice_update_lbd:
  assumes
    i: \<open>i \<in># dom_m N\<close> and
    ia: \<open>ia \<in># dom_m N\<close> and
    dom: \<open>\<forall>i \<in># dom_m N. i < length arena \<and> i \<ge> header_size (N\<propto>i) \<and>
         xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>
  shows
    \<open>clause_slice (update_lbd i lbd arena) N ia =
      (if ia = i then update_lbd (header_size (N\<propto>i)) lbd (clause_slice arena N ia)
         else clause_slice arena N ia)\<close>
proof -
  have ia_ge: \<open>ia \<ge> header_size(N \<propto> ia)\<close> \<open>ia < length arena\<close> and
   i_ge:  \<open>i \<ge> header_size(N \<propto> i)\<close> \<open>i < length arena\<close>
    using dom ia i unfolding xarena_active_clause_def
    by auto

  show ?thesis
    using minimal_difference_between_valid_index[OF dom i ia] i_ge
    minimal_difference_between_valid_index[OF dom ia i] ia_ge
    by (cases \<open>ia < i\<close>)
     (auto simp: extra_information_mark_to_delete_def drop_update_swap
       update_lbd_def SHIFTS_def
       Misc.slice_def header_size_def split: if_splits)
qed

lemma length_update_lbd[simp]:
  \<open>length (update_lbd i lbd arena) = length arena\<close>
  by (auto simp: update_lbd_def)

lemma clause_slice_update_lbd_dead:
  assumes
    i: \<open>i \<in># dom_m N\<close> and
    ia: \<open>ia \<notin># dom_m N\<close> \<open>ia \<in> vdom\<close> and
    dom: \<open>valid_arena arena N vdom\<close>
  shows
    \<open>arena_dead_clause (dead_clause_slice (update_lbd i lbd arena) N ia) =
      arena_dead_clause (dead_clause_slice arena N ia)\<close>
proof -
  have ia_ge: \<open>ia \<ge> 4\<close> \<open>ia < length arena\<close> and
   i_ge:  \<open>i \<ge> header_size(N \<propto> i)\<close> \<open>i < length arena\<close>
    using dom ia i unfolding valid_arena_def
    by auto
  show ?thesis
    using minimal_difference_between_invalid_index[OF dom i ia(1) _ ia(2)] i_ge ia_ge
    using minimal_difference_between_invalid_index2[OF dom i ia(1) _ ia(2)] ia_ge
    by (cases \<open>ia < i\<close>)
     (auto simp: extra_information_mark_to_delete_def drop_update_swap
      arena_dead_clause_def update_lbd_def SHIFTS_def
       Misc.slice_def header_size_def split: if_splits)
qed

lemma xarena_active_clause_update_lbd_same:
  assumes
    \<open>i \<ge> header_size (N \<propto> i)\<close> and
    \<open>i < length arena\<close> and
    \<open>xarena_active_clause (clause_slice arena N i)
     (the (fmlookup N i))\<close>
  shows \<open>xarena_active_clause (update_lbd (header_size (N\<propto>i)) lbd (clause_slice arena N i))
     (the (fmlookup N i))\<close>
  using assms
  by (cases \<open>is_short_clause (N \<propto> i)\<close>)
    (simp_all add: xarena_active_clause_alt_def update_lbd_def SHIFTS_def Misc.slice_def
    header_size_def)


lemma valid_arena_update_lbd:
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close>
  shows \<open>valid_arena (update_lbd i lbd arena) N vdom\<close>
proof -
  let ?arena = \<open>update_lbd i lbd arena\<close>
  have [simp]: \<open>i \<notin># remove1_mset i (dom_m N)\<close>
     \<open>\<And>ia. ia \<notin># remove1_mset i (dom_m N) \<longleftrightarrow> ia = i \<or> (i \<noteq> ia \<and> ia \<notin># dom_m N)\<close>
    using assms distinct_mset_dom[of N]
    by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
  have
    dom: \<open>\<forall>i\<in>#dom_m N.
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close> and
    dom': \<open>\<And>i. i\<in>#dom_m N \<Longrightarrow>
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>  and
    vdom: \<open>\<And>i. i\<in>vdom \<longrightarrow> i \<notin># dom_m N \<longrightarrow> 4 \<le> i \<and> arena_dead_clause (dead_clause_slice arena N i)\<close>
    using assms unfolding valid_arena_def by auto
  have \<open>ia\<in>#dom_m N \<Longrightarrow> ia \<noteq> i \<Longrightarrow>
        ia < length ?arena \<and>
        header_size (N \<propto> ia) \<le> ia \<and>
        xarena_active_clause (clause_slice ?arena N ia) (the (fmlookup N ia))\<close> for ia
    using dom'[of ia] clause_slice_update_lbd[OF i _ dom, of ia lbd]
    by auto
  moreover have \<open>ia = i \<Longrightarrow>
        ia < length ?arena \<and>
        header_size (N \<propto> ia) \<le> ia \<and>
        xarena_active_clause (clause_slice ?arena N ia) (the (fmlookup N ia))\<close> for ia
    using dom'[of ia] clause_slice_update_lbd[OF i _ dom, of ia lbd] i
    by (simp add: xarena_active_clause_update_lbd_same)
  moreover have \<open>ia\<in>vdom \<longrightarrow>
        ia \<notin># dom_m N \<longrightarrow>
        4 \<le> ia \<and> arena_dead_clause
         (dead_clause_slice (update_lbd i lbd arena) (fmdrop i N) ia)\<close> for ia
    using vdom[of ia] clause_slice_update_lbd_dead[OF i _ _ arena, of ia] i
    by auto
  ultimately show ?thesis
    using assms unfolding valid_arena_def
    by auto
qed


paragraph \<open>Update saved position\<close>

definition update_pos_direct where
  \<open>update_pos_direct C pos arena = arena[C - POS_SHIFT := APos pos]\<close>

lemma clause_slice_update_pos:
  assumes
    i: \<open>i \<in># dom_m N\<close> and
    ia: \<open>ia \<in># dom_m N\<close> and
    dom: \<open>\<forall>i \<in># dom_m N. i < length arena \<and> i \<ge> header_size (N\<propto>i) \<and>
         xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close> and
    long: \<open>is_long_clause (N \<propto> i)\<close>
  shows
    \<open>clause_slice (update_pos_direct i pos arena) N ia =
      (if ia = i then update_pos_direct (header_size (N\<propto>i)) pos (clause_slice arena N ia)
         else clause_slice arena N ia)\<close>
proof -
  have ia_ge: \<open>ia \<ge> header_size(N \<propto> ia)\<close> \<open>ia < length arena\<close> and
   i_ge:  \<open>i \<ge> header_size(N \<propto> i)\<close> \<open>i < length arena\<close>
    using dom ia i unfolding xarena_active_clause_def
    by auto
  show ?thesis
    using minimal_difference_between_valid_index[OF dom i ia] i_ge
    minimal_difference_between_valid_index[OF dom ia i] ia_ge long
    by (cases \<open>ia < i\<close>)
     (auto simp: extra_information_mark_to_delete_def drop_update_swap
       update_pos_direct_def SHIFTS_def
       Misc.slice_def header_size_def split: if_splits)
qed


lemma clause_slice_update_pos_dead:
  assumes
    i: \<open>i \<in># dom_m N\<close> and
    ia: \<open>ia \<notin># dom_m N\<close> \<open>ia \<in> vdom\<close> and
    dom: \<open>valid_arena arena N vdom\<close> and
    long: \<open>is_long_clause (N \<propto> i)\<close>
  shows
    \<open>arena_dead_clause (dead_clause_slice (update_pos_direct i pos arena) N ia) =
      arena_dead_clause (dead_clause_slice arena N ia)\<close>
proof -
  have ia_ge: \<open>ia \<ge> 4\<close> \<open>ia < length arena\<close> and
   i_ge:  \<open>i \<ge> header_size(N \<propto> i)\<close> \<open>i < length arena\<close>
    using dom ia i long unfolding valid_arena_def
    by auto
  show ?thesis
    using minimal_difference_between_invalid_index[OF dom i ia(1) _ ia(2)] i_ge ia_ge
    using minimal_difference_between_invalid_index2[OF dom i ia(1) _ ia(2)] ia_ge long
    by (cases \<open>ia < i\<close>)
     (auto simp: extra_information_mark_to_delete_def drop_update_swap
      arena_dead_clause_def update_pos_direct_def SHIFTS_def
       Misc.slice_def header_size_def split: if_splits)
qed

lemma xarena_active_clause_update_pos_same:
  assumes
    \<open>i \<ge> header_size (N \<propto> i)\<close> and
    \<open>i < length arena\<close> and
    \<open>xarena_active_clause (clause_slice arena N i)
     (the (fmlookup N i))\<close> and
    long: \<open>is_long_clause (N \<propto> i)\<close> and
    \<open>pos \<le> length (N \<propto> i) - 2\<close>
  shows \<open>xarena_active_clause (update_pos_direct (header_size (N\<propto>i)) pos (clause_slice arena N i))
     (the (fmlookup N i))\<close>
  using assms
  by (simp_all add:  update_pos_direct_def SHIFTS_def Misc.slice_def
    header_size_def xarena_active_clause_alt_def)

lemma length_update_pos[simp]:
  \<open>length (update_pos_direct i pos arena) = length arena\<close>
  by (auto simp: update_pos_direct_def)

lemma valid_arena_update_pos:
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close> and
    long: \<open>is_long_clause (N \<propto> i)\<close>and
    pos: \<open>pos \<le> length (N \<propto> i) - 2\<close>
  shows \<open>valid_arena (update_pos_direct i pos arena) N vdom\<close>
proof -
  let ?arena = \<open>update_pos_direct i pos arena\<close>
  have [simp]: \<open>i \<notin># remove1_mset i (dom_m N)\<close>
     \<open>\<And>ia. ia \<notin># remove1_mset i (dom_m N) \<longleftrightarrow> ia =i \<or> (i \<noteq> ia \<and> ia \<notin># dom_m N)\<close>
    using assms distinct_mset_dom[of N]
    by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
  have
    dom: \<open>\<forall>i\<in>#dom_m N.
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close> and
    dom': \<open>\<And>i. i\<in>#dom_m N \<Longrightarrow>
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>  and
    vdom: \<open>\<And>i. i\<in>vdom \<longrightarrow> i \<notin># dom_m N \<longrightarrow> 4 \<le> i \<and> arena_dead_clause (dead_clause_slice arena N i)\<close>
    using assms unfolding valid_arena_def by auto
  have \<open>ia\<in>#dom_m N \<Longrightarrow> ia \<noteq> i \<Longrightarrow>
        ia < length ?arena \<and>
        header_size (N \<propto> ia) \<le> ia \<and>
        xarena_active_clause (clause_slice ?arena N ia) (the (fmlookup N ia))\<close> for ia
    using dom'[of ia] clause_slice_update_pos[OF i _ dom, of ia pos] long
    by auto
  moreover have \<open>ia = i \<Longrightarrow>
        ia < length ?arena \<and>
        header_size (N \<propto> ia) \<le> ia \<and>
        xarena_active_clause (clause_slice ?arena N ia) (the (fmlookup N ia))\<close> for ia
    using dom'[of ia] clause_slice_update_pos[OF i _ dom, of ia pos] i long pos
    by (simp add: xarena_active_clause_update_pos_same)
  moreover have \<open>ia\<in>vdom \<longrightarrow>
        ia \<notin># dom_m N \<longrightarrow>
        4 \<le> ia \<and> arena_dead_clause
         (dead_clause_slice (update_pos_direct i pos arena) N ia)\<close> for ia
    using vdom[of ia] clause_slice_update_pos_dead[OF i _ _ arena, of ia] i long
    by auto
  ultimately show ?thesis
    using assms unfolding valid_arena_def
    by auto
qed




paragraph \<open>Swap literals\<close>

definition swap_lits where
  \<open>swap_lits C i j arena = swap arena (C +i) (C + j)\<close>

lemma clause_slice_swap_lits:
  assumes
    i: \<open>i \<in># dom_m N\<close> and
    ia: \<open>ia \<in># dom_m N\<close> and
    dom: \<open>\<forall>i \<in># dom_m N. i < length arena \<and> i \<ge> header_size (N\<propto>i) \<and>
         xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close> and
    k: \<open>k < length (N \<propto> i)\<close> and
    l: \<open>l < length (N \<propto> i)\<close>
  shows
    \<open>clause_slice (swap_lits i k l arena) N ia =
      (if ia = i then swap_lits (header_size (N\<propto>i)) k l (clause_slice arena N ia)
         else clause_slice arena N ia)\<close>
proof -
  have ia_ge: \<open>ia \<ge> header_size(N \<propto> ia)\<close> \<open>ia < length arena\<close> and
   i_ge:  \<open>i \<ge> header_size(N \<propto> i)\<close> \<open>i < length arena\<close>
    using dom ia i unfolding xarena_active_clause_def
    by auto

  show ?thesis
    using minimal_difference_between_valid_index[OF dom i ia] i_ge
    minimal_difference_between_valid_index[OF dom ia i] ia_ge k l
    by (cases \<open>ia < i\<close>)
     (auto simp: extra_information_mark_to_delete_def drop_update_swap
       swap_lits_def SHIFTS_def swap_def ac_simps
       Misc.slice_def header_size_def split: if_splits)
qed

lemma length_swap_lits[simp]:
  \<open>length (swap_lits i k l arena) = length arena\<close>
  by (auto simp: swap_lits_def)

lemma clause_slice_swap_lits_dead:
  assumes
    i: \<open>i \<in># dom_m N\<close> and
    ia: \<open>ia \<notin># dom_m N\<close> \<open>ia \<in> vdom\<close> and
    dom: \<open>valid_arena arena N vdom\<close>and
    k: \<open>k < length (N \<propto> i)\<close> and
    l: \<open>l < length (N \<propto> i)\<close>
  shows
    \<open>arena_dead_clause (dead_clause_slice (swap_lits i k l arena) N ia) =
      arena_dead_clause (dead_clause_slice arena N ia)\<close>
proof -
  have ia_ge: \<open>ia \<ge> 4\<close> \<open>ia < length arena\<close> and
   i_ge:  \<open>i \<ge> header_size(N \<propto> i)\<close> \<open>i < length arena\<close>
    using dom ia i unfolding valid_arena_def
    by auto
  show ?thesis
    using minimal_difference_between_invalid_index[OF dom i ia(1) _ ia(2)] i_ge ia_ge
    using minimal_difference_between_invalid_index2[OF dom i ia(1) _ ia(2)] ia_ge k l
    by (cases \<open>ia < i\<close>)
     (auto simp: extra_information_mark_to_delete_def drop_update_swap
      arena_dead_clause_def swap_lits_def SHIFTS_def swap_def ac_simps
       Misc.slice_def header_size_def split: if_splits)
qed

lemma xarena_active_clause_swap_lits_same:
  assumes
    \<open>i \<ge> header_size (N \<propto> i)\<close> and
    \<open>i < length arena\<close> and
    \<open>xarena_active_clause (clause_slice arena N i)
     (the (fmlookup N i))\<close>and
    k: \<open>k < length (N \<propto> i)\<close> and
    l: \<open>l < length (N \<propto> i)\<close>
  shows \<open>xarena_active_clause (clause_slice (swap_lits i k l arena) N i)
     (the (fmlookup (N(i \<hookrightarrow> swap (N \<propto> i) k l)) i))\<close>
  using assms
  unfolding xarena_active_clause_alt_def
  by (cases \<open>is_short_clause (N \<propto> i)\<close>)
    (simp_all add:  swap_lits_def SHIFTS_def min_def swap_nth_if map_swap swap_swap
    header_size_def ac_simps is_short_clause_def split: if_splits)

lemma is_short_clause_swap[simp]: \<open>is_short_clause (swap (N \<propto> i) k l) = is_short_clause (N \<propto> i)\<close>
  by (auto simp: header_size_def is_short_clause_def split: if_splits)

lemma header_size_swap[simp]: \<open>header_size (swap (N \<propto> i) k l) = header_size (N \<propto> i)\<close>
  by (auto simp: header_size_def split: if_splits)

lemma valid_arena_swap_lits:
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close> and
    k: \<open>k < length (N \<propto> i)\<close> and
    l: \<open>l < length (N \<propto> i)\<close>
  shows \<open>valid_arena (swap_lits i k l arena) (N(i \<hookrightarrow> swap (N \<propto> i) k l)) vdom\<close>
proof -
  let ?arena = \<open>swap_lits i k l arena\<close>
  have [simp]: \<open>i \<notin># remove1_mset i (dom_m N)\<close>
     \<open>\<And>ia. ia \<notin># remove1_mset i (dom_m N) \<longleftrightarrow> ia =i \<or> (i \<noteq> ia \<and> ia \<notin># dom_m N)\<close>
    using assms distinct_mset_dom[of N]
    by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
  have
    dom: \<open>\<forall>i\<in>#dom_m N.
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close> and
    dom': \<open>\<And>i. i\<in>#dom_m N \<Longrightarrow>
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>  and
    vdom: \<open>\<And>i. i\<in>vdom \<longrightarrow> i \<notin># dom_m N \<longrightarrow> 4 \<le> i \<and> arena_dead_clause (dead_clause_slice arena N i)\<close>
    using assms unfolding valid_arena_def by auto
  have \<open>ia\<in>#dom_m N \<Longrightarrow> ia \<noteq> i \<Longrightarrow>
        ia < length ?arena \<and>
        header_size (N \<propto> ia) \<le> ia \<and>
        xarena_active_clause (clause_slice ?arena N ia) (the (fmlookup N ia))\<close> for ia
    using dom'[of ia] clause_slice_swap_lits[OF i _ dom, of ia k l] k l
    by auto
  moreover have \<open>ia = i \<Longrightarrow>
      ia < length ?arena \<and>
      header_size (N \<propto> ia) \<le> ia \<and>
      xarena_active_clause (clause_slice ?arena N ia)
        (the (fmlookup (N(i \<hookrightarrow> swap (N \<propto> i) k l)) ia))\<close>
    for ia
    using dom'[of ia] clause_slice_swap_lits[OF i _ dom, of ia k l] i k l
    xarena_active_clause_swap_lits_same[OF _ _ _ k l, of arena]
    by auto
  moreover have \<open>ia\<in>vdom \<longrightarrow>
        ia \<notin># dom_m N \<longrightarrow>
        4 \<le> ia \<and> arena_dead_clause (dead_clause_slice (swap_lits i k l arena) (fmdrop i N) ia)\<close>
      for ia
    using vdom[of ia] clause_slice_swap_lits_dead[OF i _ _ arena, of ia] i k l
    by auto
  ultimately show ?thesis
    using i k l arena unfolding valid_arena_def
    by auto
qed


paragraph \<open>Learning a clause\<close>

definition append_clause_skeleton where
  \<open>append_clause_skeleton pos st used act lbd C arena =
    (if is_short_clause C then
      arena @ (AStatus st used) # AActivity act # ALBD lbd #
      ASize (length C - 2) # map ALit C
    else arena @ APos pos # (AStatus st used) # AActivity act #
      ALBD lbd # ASize (length C - 2) # map ALit C)\<close>

definition append_clause where
  \<open>append_clause b C arena =
    append_clause_skeleton 0 (if b then IRRED else LEARNED) True 0 (length C - 2) C arena\<close>

lemma arena_active_clause_append_clause:
  assumes
    \<open>i \<ge> header_size (N \<propto> i)\<close> and
    \<open>i < length arena\<close> and
    \<open>xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>
  shows \<open>xarena_active_clause (clause_slice (append_clause_skeleton pos st used act lbd C arena) N i)
     (the (fmlookup N i))\<close>
proof -
  have \<open>drop (header_size (N \<propto> i)) (clause_slice arena N i) = map ALit (N \<propto> i)\<close> and
    \<open>header_size (N \<propto> i) \<le> i\<close> and
    \<open>i < length arena\<close>
    using assms
    unfolding xarena_active_clause_alt_def
    by auto
   from arg_cong[OF this(1), of length] this(2-)
   have \<open>i + length (N \<propto> i) \<le> length arena\<close>
    unfolding xarena_active_clause_alt_def
    by (auto simp add: slice_len_min_If header_size_def is_short_clause_def split: if_splits)
  then have \<open>clause_slice (append_clause_skeleton pos st used act lbd C arena) N i =
    clause_slice arena N i\<close>
    by (auto simp add: append_clause_skeleton_def)
  then show ?thesis
    using assms by simp
qed

lemma length_append_clause[simp]:
  \<open>length (append_clause_skeleton pos st used act lbd C arena) =
    length arena + length C + header_size C\<close>
  \<open>length (append_clause b C arena) = length arena + length C + header_size C\<close>
  by (auto simp: append_clause_skeleton_def header_size_def
    append_clause_def)

lemma arena_active_clause_append_clause_same: \<open>2 \<le> length C \<Longrightarrow> st \<noteq> DELETED \<Longrightarrow>
    pos \<le> length C - 2 \<Longrightarrow>
    b \<longleftrightarrow> (st = IRRED) \<Longrightarrow>
    xarena_active_clause
     (Misc.slice (length arena) (length arena + header_size C + length C)
       (append_clause_skeleton pos st used act lbd C arena))
     (the (fmlookup (fmupd (length arena + header_size C) (C, b) N)
       (length arena + header_size C)))\<close>
  unfolding xarena_active_clause_alt_def append_clause_skeleton_def
  by (cases st)
   (auto simp: header_size_def slice_start0 SHIFTS_def slice_Cons split: if_splits)

lemma clause_slice_append_clause:
  assumes
    ia: \<open>ia \<notin># dom_m N\<close> \<open>ia \<in> vdom\<close> and
    dom: \<open>valid_arena arena N vdom\<close> and
    \<open>arena_dead_clause (dead_clause_slice (arena) N ia)\<close>
  shows
    \<open>arena_dead_clause (dead_clause_slice (append_clause_skeleton pos st used act lbd C arena) N ia)\<close>
proof -
  have ia_ge: \<open>ia \<ge> 4\<close> \<open>ia < length arena\<close>
    using dom ia unfolding valid_arena_def
    by auto
  then have \<open>dead_clause_slice (arena) N ia =
      dead_clause_slice (append_clause_skeleton pos st used act lbd C arena) N ia\<close>
    by (auto simp add: extra_information_mark_to_delete_def drop_update_swap
      append_clause_skeleton_def
      arena_dead_clause_def swap_lits_def SHIFTS_def swap_def ac_simps
       Misc.slice_def header_size_def split: if_splits)
  then show ?thesis
    using assms by simp
qed


lemma valid_arena_append_clause_skeleton:
  assumes arena: \<open>valid_arena arena N vdom\<close> and le_C: \<open>length C \<ge> 2\<close> and
    b: \<open>b \<longleftrightarrow> (st = IRRED)\<close> and st: \<open>st \<noteq> DELETED\<close> and
    pos: \<open>pos \<le> length C - 2\<close>
  shows \<open>valid_arena (append_clause_skeleton pos st used act lbd C arena)
      (fmupd (length arena + header_size C) (C, b) N)
     (insert (length arena + header_size C) vdom)\<close>
proof -
  let ?arena = \<open>append_clause_skeleton pos st used act lbd C arena\<close>
  let ?i= \<open>length arena + header_size C\<close>
  let ?N = \<open>(fmupd (length arena + header_size C) (C, b) N)\<close>
  let ?vdom = \<open>insert (length arena + header_size C) vdom\<close>
  have
    dom: \<open>\<forall>i\<in>#dom_m N.
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close> and
    dom': \<open>\<And>i. i\<in>#dom_m N \<Longrightarrow>
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>  and
    vdom: \<open>\<And>i. i\<in>vdom \<longrightarrow> i \<notin># dom_m N \<longrightarrow> i \<le> length arena \<and> 4 \<le> i \<and>
      arena_dead_clause (dead_clause_slice arena N i)\<close>
    using assms unfolding valid_arena_def by auto
  have [simp]: \<open>?i \<notin># dom_m N\<close>
    using dom'[of ?i]
    by auto
  have \<open>ia\<in>#dom_m N \<Longrightarrow>
        ia < length ?arena \<and>
        header_size (N \<propto> ia) \<le> ia \<and>
        xarena_active_clause (clause_slice ?arena N ia) (the (fmlookup N ia))\<close> for ia
    using dom'[of ia] arena_active_clause_append_clause[of N ia arena]
    by auto
  moreover have \<open>ia = ?i \<Longrightarrow>
        ia < length ?arena \<and>
        header_size (?N \<propto> ia) \<le> ia \<and>
        xarena_active_clause (clause_slice ?arena ?N ia) (the (fmlookup ?N ia))\<close> for ia
    using dom'[of ia] le_C arena_active_clause_append_clause_same[of C st pos b arena used]
      b st pos
    by auto
  moreover have \<open>ia\<in>vdom \<longrightarrow>
        ia \<notin># dom_m N \<longrightarrow> ia < length (?arena) \<and>
        4 \<le> ia \<and> arena_dead_clause (Misc.slice (ia - 4) ia (?arena))\<close> for ia
    using vdom[of ia] clause_slice_append_clause[of ia N vdom arena pos st used act lbd C, OF _ _ arena]
      le_C b st
    by auto
  ultimately show ?thesis
    unfolding valid_arena_def
    by auto
qed

lemma valid_arena_append_clause:
  assumes arena: \<open>valid_arena arena N vdom\<close> and le_C: \<open>length C \<ge> 2\<close>
  shows \<open>valid_arena (append_clause b C arena)
      (fmupd (length arena + header_size C) (C, b) N)
     (insert (length arena + header_size C) vdom)\<close>
  using valid_arena_append_clause_skeleton[OF assms(1,2),
    of b \<open>if b then IRRED else LEARNED\<close>]
  by (auto simp: append_clause_def)


subsubsection \<open>Refinement Relation\<close>

definition status_rel:: "(nat \<times> clause_status) set" where
  \<open>status_rel = {(0, IRRED), (1, LEARNED), (3, DELETED)}\<close>

definition bitfield_rel where
  \<open>bitfield_rel n = {(a, b). b \<longleftrightarrow> a AND (2 ^ n) > 0}\<close>

definition arena_el_relation where
\<open>arena_el_relation x el  = (case el of
     AStatus n b \<Rightarrow> (x AND 0b11, n) \<in> status_rel \<and> (x, b) \<in> bitfield_rel 2
   | APos n \<Rightarrow> (x, n) \<in> nat_rel
   | ASize n \<Rightarrow> (x, n) \<in> nat_rel
   | ALBD n \<Rightarrow> (x, n) \<in> nat_rel
   | AActivity n \<Rightarrow> (x, n) \<in> nat_rel
   | ALit n \<Rightarrow> (x, n) \<in> nat_lit_rel
)\<close>

definition arena_el_rel where
 arena_el_rel_interal_def: \<open>arena_el_rel = {(x, el). arena_el_relation x el}\<close>

lemmas arena_el_rel_def = arena_el_rel_interal_def[unfolded arena_el_relation_def]

abbreviation arena_el_assn :: "arena_el \<Rightarrow> uint32 \<Rightarrow> assn" where
  \<open>arena_el_assn \<equiv> hr_comp uint32_nat_assn arena_el_rel\<close>

abbreviation arena_assn :: "arena_el list \<Rightarrow> uint32 array_list \<Rightarrow> assn" where
  \<open>arena_assn \<equiv> arl_assn arena_el_assn\<close>

abbreviation status_assn where
  \<open>status_assn \<equiv> hr_comp uint32_nat_assn status_rel\<close>

subsubsection \<open>Preconditions and Assertions for the refinement\<close>

text \<open>The following lemma expresses the relation between the arena and the clauses and especially
  shows the preconditions to be able to generate code.

  The conditions on \<^term>\<open>arena_status\<close> are in the direction to simplify proofs: If we would try to go
  in the opposite direction, we could rewrite \<^term>\<open>\<not>irred N i\<close> into \<^term>\<open>arena_status arena i \<noteq> LEARNED\<close>,
  which is a weaker property.

  The inequality on the length are here to enable simp to prove inequalities \<^term>\<open>arena_length arena C > Suc 0\<close>
  automatically. Normally the arithmetic part can prove it from \<^term>\<open>arena_length arena C \<ge> 2\<close>,
  but as this inequality is simplified away, it does not work.
\<close>
lemma arena_lifting:
  assumes valid: \<open>valid_arena arena N vdom\<close> and
   i: \<open>i \<in># dom_m N\<close>
  shows
    \<open>i \<ge> header_size (N \<propto> i)\<close> and
    \<open>i < length arena\<close>
    \<open>is_Size (arena ! (i - SIZE_SHIFT))\<close>
    \<open>length (N \<propto> i) = arena_length arena i\<close>
    \<open>j < length (N \<propto> i) \<Longrightarrow> N \<propto> i ! j = arena_lit arena (i + j)\<close> and
    \<open>j < length (N \<propto> i) \<Longrightarrow> is_Lit (arena ! (i+j))\<close> and
    \<open>j < length (N \<propto> i) \<Longrightarrow> i + j < length arena\<close> and
    \<open>N \<propto> i ! 0 = arena_lit arena i\<close> and
    \<open>is_Lit (arena ! i)\<close> and
    \<open>i + length (N \<propto> i) \<le> length arena\<close> and
    \<open>is_long_clause (N \<propto> i) \<Longrightarrow> is_Pos (arena ! ( i - POS_SHIFT))\<close> and
    \<open>is_long_clause (N \<propto> i) \<Longrightarrow> arena_pos arena i \<le> arena_length arena i\<close> and
    \<open>is_LBD (arena ! (i - LBD_SHIFT))\<close> and
    \<open>is_Act (arena ! (i - ACTIVITY_SHIFT))\<close> and
    \<open>is_Status (arena ! (i - STATUS_SHIFT))\<close> and
    \<open>SIZE_SHIFT \<le> i\<close> and
    \<open>LBD_SHIFT \<le> i\<close>
    \<open>ACTIVITY_SHIFT \<le> i\<close> and
    \<open>arena_length arena i \<ge> 2\<close> and
    \<open>arena_length arena i \<ge> Suc 0\<close> and
    \<open>arena_length arena i \<ge> 0\<close> and
    \<open>arena_length arena i > Suc 0\<close> and
    \<open>arena_length arena i > 0\<close> and
    \<open>arena_status arena i = LEARNED \<longleftrightarrow> \<not>irred N i\<close> and
    \<open>arena_status arena i = IRRED \<longleftrightarrow> irred N i\<close> and
    \<open>arena_status arena i \<noteq> DELETED\<close> and
    \<open>Misc.slice i (i + arena_length arena i) arena = map ALit (N \<propto> i)\<close>
proof -
  have
    dom: \<open>\<And>i. i\<in>#dom_m N \<Longrightarrow>
      i < length arena \<and>
      header_size (N \<propto> i) \<le> i \<and>
      xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>
    using valid unfolding valid_arena_def
    by blast+

  have
    i_le: \<open>i < length arena\<close> and
    i_ge: \<open>header_size (N \<propto> i) \<le> i\<close> and
    xi: \<open>xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>
    using dom[OF i] by fast+

  have
    ge2: \<open>2 \<le> length (N \<propto> i)\<close> and
    \<open>header_size (N \<propto> i) + length (N \<propto> i) = length (clause_slice arena N i)\<close> and
    pos: \<open>is_long_clause (N \<propto> i) \<longrightarrow>
     is_Pos (clause_slice arena N i ! (header_size (N \<propto> i) - POS_SHIFT)) \<and>
     xarena_pos (clause_slice arena N i ! (header_size (N \<propto> i) - POS_SHIFT))
     \<le> length (N \<propto> i) - 2\<close> and
    status: \<open>is_Status
      (clause_slice arena N i ! (header_size (N \<propto> i) - STATUS_SHIFT))\<close> and
    init: \<open>(xarena_status
       (clause_slice arena N i ! (header_size (N \<propto> i) - STATUS_SHIFT)) =
      IRRED) =
     irred N i\<close> and
    learned: \<open>(xarena_status
       (clause_slice arena N i ! (header_size (N \<propto> i) - STATUS_SHIFT)) =
      LEARNED) =
     (\<not> irred N i)\<close> and
    lbd: \<open>is_LBD (clause_slice arena N i ! (header_size (N \<propto> i) - LBD_SHIFT))\<close> and
    act: \<open>is_Act (clause_slice arena N i ! (header_size (N \<propto> i) - ACTIVITY_SHIFT))\<close> and
    size: \<open>is_Size (clause_slice arena N i ! (header_size (N \<propto> i) - SIZE_SHIFT))\<close> and
    size': \<open>Suc (Suc (xarena_length
                (clause_slice arena N i !
                 (header_size (N \<propto> i) - SIZE_SHIFT)))) =
     length (N \<propto> i)\<close> and
    clause: \<open>Misc.slice i (i + length (N \<propto> i)) arena = map ALit (N \<propto> i)\<close>
    using xi i_le i_ge unfolding xarena_active_clause_alt_def arena_length_def
    by simp_all
  have [simp]:
    \<open>clause_slice arena N i ! (header_size (N \<propto> i) - LBD_SHIFT) = ALBD (arena_lbd arena i)\<close>
    \<open>clause_slice arena N i ! (header_size (N \<propto> i) - STATUS_SHIFT) =
       AStatus (arena_status arena i) (arena_used arena i)\<close>
    using size size' i_le i_ge ge2 lbd status size'
    unfolding header_size_def arena_length_def arena_lbd_def arena_status_def arena_used_def
    by (auto simp: SHIFTS_def slice_nth)
  have HH:
    \<open>arena_length arena i = length (N \<propto> i)\<close> and \<open>is_Size (arena ! (i - SIZE_SHIFT))\<close>
    using size size' i_le i_ge ge2 lbd status size' ge2
    unfolding header_size_def arena_length_def arena_lbd_def arena_status_def
    by (cases \<open>arena ! (i - Suc 0)\<close>; auto simp: SHIFTS_def slice_nth; fail)+
  then show  \<open>length (N \<propto> i) = arena_length arena i\<close> and \<open>is_Size (arena ! (i - SIZE_SHIFT))\<close>
    using i_le i_ge size' size ge2 HH unfolding numeral_2_eq_2
    by (simp_all split:)
  show \<open>arena_length arena i \<ge> 2\<close>
    \<open>arena_length arena i \<ge> Suc 0\<close> and
    \<open>arena_length arena i \<ge> 0\<close> and
    \<open>arena_length arena i > Suc 0\<close> and
    \<open>arena_length arena i > 0\<close>
    using ge2 unfolding HH by auto
  show
    \<open>i \<ge> header_size (N \<propto> i)\<close> and
    \<open>i < length arena\<close>
    using i_le i_ge by auto
  show is_lit: \<open>is_Lit (arena ! (i+j))\<close> \<open>N \<propto> i ! j = arena_lit arena (i + j)\<close>
    if \<open>j < length (N \<propto> i)\<close>
    for j
    using arg_cong[OF clause, of \<open>\<lambda>xs. xs ! j\<close>] i_le i_ge that
    by (auto simp: slice_nth arena_lit_def)

  show i_le_arena: \<open>i + length (N \<propto> i) \<le> length arena\<close>
    using arg_cong[OF clause, of length] i_le i_ge
    by (auto simp: arena_lit_def slice_len_min_If)
  show \<open>is_Pos (arena ! (i - POS_SHIFT))\<close> and
    \<open>arena_pos arena i \<le> arena_length arena i\<close>
  if \<open>is_long_clause (N \<propto> i)\<close>
    using pos ge2 i_le i_ge that unfolding arena_pos_def HH
    by (auto simp: SHIFTS_def slice_nth header_size_def)
  show  \<open>is_LBD (arena ! (i - LBD_SHIFT))\<close> and
    \<open>is_Act (arena ! (i - ACTIVITY_SHIFT))\<close> and
     \<open>is_Status (arena ! (i - STATUS_SHIFT))\<close>
    using lbd act ge2 i_le i_ge status unfolding arena_pos_def
    by (auto simp: SHIFTS_def slice_nth header_size_def)
  show \<open>SIZE_SHIFT \<le> i\<close> and  \<open>LBD_SHIFT \<le> i\<close> and
    \<open>ACTIVITY_SHIFT \<le> i\<close>
    using i_ge unfolding header_size_def SHIFTS_def by (auto split: if_splits)
  show \<open>j < length (N \<propto> i) \<Longrightarrow> i + j < length arena\<close>
    using i_le_arena by linarith
  show
    \<open>N \<propto> i ! 0 = arena_lit arena i\<close> and
    \<open>is_Lit (arena ! i)\<close>
    using is_lit[of 0] ge2 by fastforce+
  show
    \<open>arena_status arena i = LEARNED \<longleftrightarrow> \<not>irred N i \<close>and
    \<open>arena_status arena i = IRRED \<longleftrightarrow> irred N i\<close> and
    \<open>arena_status arena i \<noteq> DELETED\<close>
    using learned init unfolding arena_status_def
    by (auto simp: arena_status_def)
  show
    \<open>Misc.slice i (i + arena_length arena i) arena = map ALit (N \<propto> i)\<close>
    apply (subst list_eq_iff_nth_eq, intro conjI allI)
    subgoal
      using HH i_le_arena i_le
      by (auto simp: slice_nth slice_len_min_If)
    subgoal for j
      using HH i_le_arena i_le is_lit[of j]
      by (cases \<open>arena ! (i + j)\<close>)
       (auto simp: slice_nth slice_len_min_If
         arena_lit_def)
    done
qed


lemma arena_dom_status_iff:
  assumes valid: \<open>valid_arena arena N vdom\<close> and
   i: \<open>i \<in> vdom\<close>
  shows
    \<open>i \<in># dom_m N \<longleftrightarrow> arena_status arena i \<noteq> DELETED\<close> (is \<open>?eq\<close> is \<open>?A \<longleftrightarrow> ?B\<close>) and
    \<open>is_LBD (arena ! (i - LBD_SHIFT))\<close> (is ?lbd) and
    \<open>is_Act (arena ! (i - ACTIVITY_SHIFT))\<close> (is ?act) and
    \<open>is_Status (arena ! (i - STATUS_SHIFT))\<close> (is ?stat) and
    \<open>4 \<le> i\<close> (is ?ge)
proof -
  have H1: ?eq ?lbd ?act ?stat ?ge
    if \<open>?A\<close>
  proof -
    have
      \<open>xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close> and
      i_ge: \<open>header_size (N \<propto> i) \<le> i\<close> and
      i_le: \<open>i < length arena\<close>
      using assms that unfolding valid_arena_def by blast+
    then have \<open>is_Status (clause_slice arena N i ! (header_size (N \<propto> i) - STATUS_SHIFT))\<close> and
      \<open>(xarena_status (clause_slice arena N i ! (header_size (N \<propto> i) - STATUS_SHIFT)) = IRRED) =
       irred N i\<close> and
      \<open>(xarena_status (clause_slice arena N i ! (header_size (N \<propto> i) - STATUS_SHIFT)) = LEARNED) =
        (\<not> irred N i)\<close> and
      \<open>is_LBD (clause_slice arena N i ! (header_size (N \<propto> i) - LBD_SHIFT))\<close> and
      \<open>is_Act (clause_slice arena N i ! (header_size (N \<propto> i) - ACTIVITY_SHIFT)) \<close>
      unfolding xarena_active_clause_alt_def arena_status_def
      by blast+
    then show ?eq and ?lbd and ?act and ?stat and ?ge
      using i_ge i_le that
      unfolding xarena_active_clause_alt_def arena_status_def
      by (auto simp: SHIFTS_def header_size_def slice_nth split: if_splits)
  qed
  moreover have H2: ?eq
    if \<open>?B\<close>
  proof -
    have ?A
    proof (rule ccontr)
      assume \<open>i \<notin># dom_m N\<close>
      then have
        \<open>arena_dead_clause (Misc.slice (i - 4) i arena)\<close> and
        i_ge: \<open>4 \<le> i\<close> and
        i_le: \<open>i < length arena\<close>
        using assms unfolding valid_arena_def by blast+
      then show False
        using \<open>?B\<close>
        unfolding arena_dead_clause_def
        by (auto simp: arena_status_def slice_nth SHIFTS_def)
    qed
    then show ?eq
      using arena_lifting[OF valid, of i] that
      by auto
  qed
  moreover have ?lbd ?act ?stat ?ge if \<open>\<not>?A\<close>
  proof -
    have
      \<open>arena_dead_clause (Misc.slice (i - 4) i arena)\<close> and
      i_ge: \<open>4 \<le> i\<close> and
      i_le: \<open>i < length arena\<close>
      using assms that unfolding valid_arena_def by blast+
    then show ?lbd ?act ?stat ?ge
      unfolding arena_dead_clause_def
      by (auto simp: SHIFTS_def slice_nth)
  qed
  ultimately show ?eq and ?lbd and ?act and ?stat and ?ge
    by blast+
qed

lemma valid_arena_one_notin_vdomD:
  \<open>valid_arena M N vdom \<Longrightarrow> Suc 0 \<notin> vdom\<close>
  using arena_dom_status_iff[of M N vdom 1]
  by auto

text \<open>This is supposed to be used as for assertions. There might be a more ``local'' way to define
it, without the need for an existentially quantified clause set. However, I did not find a definition
which was really much more useful and more practical.
\<close>
definition arena_is_valid_clause_idx :: \<open>arena \<Rightarrow> nat \<Rightarrow> bool\<close> where
\<open>arena_is_valid_clause_idx arena i \<longleftrightarrow>
  (\<exists>N vdom. valid_arena arena N vdom \<and> i \<in># dom_m N)\<close>

text \<open>This precondition has weaker preconditions is restricted to extracting the status (the other
headers can be extracted but only garbage is returned).
\<close>
definition arena_is_valid_clause_vdom :: \<open>arena \<Rightarrow> nat \<Rightarrow> bool\<close> where
\<open>arena_is_valid_clause_vdom arena i \<longleftrightarrow>
  (\<exists>N vdom. valid_arena arena N vdom \<and> i \<in> vdom)\<close>


subsubsection \<open>Code Generation\<close>

paragraph \<open>Length\<close>

definition isa_arena_length where
  \<open>isa_arena_length arena i = do {
      ASSERT(i \<ge> SIZE_SHIFT \<and> i < length arena);
      RETURN (two_uint64 + uint64_of_uint32 ((arena ! (fast_minus i SIZE_SHIFT))))
  }\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN SIZE_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: SIZE_SHIFT_def)

lemma [sepref_fr_rules]:
  \<open>(return o id, RETURN o xarena_length) \<in> [is_Size]\<^sub>a arena_el_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: SIZE_SHIFT_def uint32_nat_rel_def
    arena_el_rel_def br_def hr_comp_def split: arena_el.splits)

lemma nat_of_uint64_eq_2_iff[simp]: \<open>nat_of_uint64 c = 2 \<longleftrightarrow> c = 2\<close>
  using word_nat_of_uint64_Rep_inject by fastforce

lemma arena_el_assn_alt_def:
  \<open>arena_el_assn = hr_comp uint32_assn (uint32_nat_rel O arena_el_rel)\<close>
  by (auto simp: hr_comp_assoc[symmetric])

lemma arena_el_comp: \<open>hn_val (uint32_nat_rel O arena_el_rel) = hn_ctxt arena_el_assn\<close>
  by (auto simp: hn_ctxt_def arena_el_assn_alt_def)

sepref_definition isa_arena_length_code
  is \<open>uncurry isa_arena_length\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_length_def
  by sepref

lemma arena_length_uint64_conv:
  assumes
    a: \<open>(a, aa) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> and
    ba: \<open>ba \<in># dom_m N\<close> and
    valid: \<open>valid_arena aa N vdom\<close>
  shows \<open>Suc (Suc (xarena_length (aa ! (ba - SIZE_SHIFT)))) =
         nat_of_uint64 (2 + uint64_of_uint32 (a ! (ba - SIZE_SHIFT)))\<close>
proof -
  have ba_le: \<open>ba < length aa\<close> and
    size: \<open>is_Size (aa ! (ba - SIZE_SHIFT))\<close> and
    length: \<open>length (N \<propto> ba) = arena_length aa ba\<close>
    using ba valid by (auto simp: arena_lifting)
  have \<open>(a ! (ba - SIZE_SHIFT), aa ! (ba - SIZE_SHIFT))
      \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a, of \<open>ba - SIZE_SHIFT\<close> \<open>ba - SIZE_SHIFT\<close>])
      (use ba_le in auto)
  then have \<open>aa ! (ba - SIZE_SHIFT) = ASize (nat_of_uint32 (a ! (ba - SIZE_SHIFT)))\<close>
    using size unfolding arena_el_rel_def
    by (auto split: arena_el.splits simp: uint32_nat_rel_def br_def)
  moreover have \<open>Suc (Suc (nat_of_uint32 (a ! (ba - SIZE_SHIFT)))) \<le> uint64_max\<close>
    using nat_of_uint32_le_uint32_max[of \<open>a ! (ba - SIZE_SHIFT)\<close>]
    by (auto simp: uint64_max_def uint32_max_def)
  ultimately show ?thesis by (simp add: nat_of_uint64_add nat_of_uint64_uint64_of_uint32)
qed

lemma isa_arena_length_arena_length:
  \<open>(uncurry (isa_arena_length), uncurry (RETURN oo arena_length)) \<in>
    [uncurry arena_is_valid_clause_idx]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>uint64_nat_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_length_def arena_length_def
  by (intro frefI nres_relI)
    (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
       list_rel_imp_same_length arena_length_uint64_conv arena_lifting
    intro!: ASSERT_refine_left)

lemma isa_arena_length_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_length_code, uncurry (RETURN \<circ>\<circ> arena_length))
  \<in> [uncurry arena_is_valid_clause_idx]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_arena_length_code.refine[FCOMP isa_arena_length_arena_length]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)

sepref_definition isa_arena_length_fast_code
  is \<open>uncurry isa_arena_length\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    minus_uint64_nat_assn[sepref_fr_rules]
  unfolding isa_arena_length_def SIZE_SHIFT_def fast_minus_def one_uint64_nat_def[symmetric]
  by sepref

lemma isa_arena_length_fast_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_length_fast_code, uncurry (RETURN \<circ>\<circ> arena_length))
  \<in> [uncurry arena_is_valid_clause_idx]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_arena_length_fast_code.refine[FCOMP isa_arena_length_arena_length]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)


paragraph \<open>Literal at given position\<close>

definition isa_arena_lit where
  \<open>isa_arena_lit arena i = do {
      ASSERT(i < length arena);
      RETURN (arena ! i)
  }\<close>

lemma [sepref_fr_rules]:
  \<open>(return o id, RETURN o xarena_lit) \<in> [is_Lit]\<^sub>a arena_el_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: SIZE_SHIFT_def uint32_nat_rel_def unat_lit_rel_def
    arena_el_rel_def br_def hr_comp_def split: arena_el.splits)

sepref_definition isa_arena_lit_code
  is \<open>uncurry isa_arena_lit\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_lit_def
  by sepref


lemma arena_length_literal_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    ba_le: \<open>ba - j < arena_length arena j\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> and
    ba_j: \<open>ba \<ge> j\<close>
  shows
    \<open>ba < length arena\<close> (is ?le) and
    \<open>(a ! ba, xarena_lit (arena ! ba)) \<in> unat_lit_rel\<close> (is ?unat)
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close>
    using arena_lifting[OF valid j] by (auto simp: )
  show le': ?le
     using le ba_le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits)

  have \<open>(a ! ba, arena ! ba)
      \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a, of \<open>ba\<close> \<open>ba\<close>])
      (use ba_le le' in auto)
  then show ?unat
     using k1[of \<open>ba - j\<close>] k2[of \<open>ba - j\<close>] ba_le length ba_j
     by (cases \<open>arena ! ba\<close>)
      (auto simp: arena_el_rel_def unat_lit_rel_def arena_lit_def
       split: arena_el.splits)
qed


definition arena_is_valid_clause_idx_and_access :: \<open>arena \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
\<open>arena_is_valid_clause_idx_and_access arena i j \<longleftrightarrow>
  (\<exists>N vdom. valid_arena arena N vdom \<and> i \<in># dom_m N \<and> j < length (N \<propto> i))\<close>

text \<open>This is the precondition for direct memory access: \<^term>\<open>N ! (i::nat)\<close> where
\<^term>\<open>(i::nat) = j + (j - i)\<close> instead of \<^term>\<open>N \<propto> j ! (i - j)\<close>.\<close>
definition arena_lit_pre where
\<open>arena_lit_pre arena i \<longleftrightarrow>
  (\<exists>j. i \<ge> j \<and> arena_is_valid_clause_idx_and_access arena j (i - j))\<close>

lemma isa_arena_lit_arena_lit:
  \<open>(uncurry isa_arena_lit, uncurry (RETURN oo arena_lit)) \<in>
    [uncurry arena_lit_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>unat_lit_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_lit_def arena_lit_def
  by (intro frefI nres_relI)
    (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
        list_rel_imp_same_length arena_length_uint64_conv arena_lifting
        arena_is_valid_clause_idx_and_access_def arena_length_literal_conv
        arena_lit_pre_def
      intro!: ASSERT_refine_left)

lemma isa_arena_lit_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_lit_code, uncurry (RETURN \<circ>\<circ> arena_lit))
  \<in> [uncurry arena_lit_pre]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  using isa_arena_lit_code.refine[FCOMP isa_arena_lit_arena_lit]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)

sepref_definition (in-) isa_arena_lit_fast_code
  is \<open>uncurry isa_arena_lit\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_lit_def
  by sepref

declare isa_arena_lit_fast_code.refine

lemma isa_arena_lit_fast_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_lit_fast_code, uncurry (RETURN \<circ>\<circ> arena_lit))
  \<in> [uncurry arena_lit_pre]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  using isa_arena_lit_fast_code.refine[FCOMP isa_arena_lit_arena_lit]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)



paragraph \<open>Status of the clause\<close>


lemma status_assn_hnr_eq[sepref_fr_rules]:
  \<open>(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in> status_assn\<^sup>k *\<^sub>a status_assn\<^sup>k \<rightarrow>\<^sub>a
    bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: status_rel_def hr_comp_def uint32_nat_rel_def br_def
    nat_of_uint32_0_iff nat_of_uint32_Suc03_iff nat_of_uint32_013_neq)

lemma IRRED_status_assn[sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN IRRED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: status_rel_def hr_comp_def uint32_nat_rel_def br_def)

lemma LEARNED_status_assn[sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN LEARNED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: status_rel_def hr_comp_def uint32_nat_rel_def br_def)

lemma DELETED_status_assn[sepref_fr_rules]:
  \<open>(uncurry0 (return 3), uncurry0 (RETURN DELETED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: status_rel_def hr_comp_def uint32_nat_rel_def br_def
    nat_of_uint32_Suc03_iff)


definition isa_arena_status where
  \<open>isa_arena_status arena i = do {
      ASSERT(i < length arena);
      ASSERT(i \<ge> STATUS_SHIFT);
      RETURN (arena ! (fast_minus i STATUS_SHIFT) AND 0b11)
  }\<close>


lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 4), uncurry0 (RETURN STATUS_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: STATUS_SHIFT_def)

sepref_definition arena_status_code
  is \<open>uncurry isa_arena_status\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_status_def
  by sepref

lemma arena_status_literal_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in> x\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j < length arena\<close> (is ?le) and
    \<open>4 \<le> j\<close> and
    \<open>j \<ge> STATUS_SHIFT\<close> and
    \<open> (a ! (j - STATUS_SHIFT) AND 0b11, xarena_status (arena ! (j - STATUS_SHIFT)))
       \<in> uint32_nat_rel O status_rel\<close> (is ?rel)
proof -
  show le: ?le and i4: \<open>4 \<le> j\<close> and  \<open>j \<ge> STATUS_SHIFT\<close>
    using valid j unfolding valid_arena_def
    by (cases \<open>j \<in># dom_m N\<close>; auto simp: header_size_def SHIFTS_def split: if_splits; fail)+
  have [intro]: \<open>\<And>a y. (a, y) \<in> uint32_nat_rel \<Longrightarrow>
      (a AND 3, y AND 3) \<in> uint32_nat_rel\<close>
    apply (auto simp: uint32_nat_rel_def br_def nat_of_uint32_ao)
     by (metis nat_of_uint32_3 nat_of_uint32_ao(1))
  have [dest]: \<open>(y, AStatus x61 x62) \<in> arena_el_rel \<Longrightarrow> (y AND 3, x61) \<in> status_rel\<close> for y x61 x62
    by (auto simp: status_rel_def arena_el_rel_def)
  have \<open>(a ! (j - STATUS_SHIFT), arena ! (j - STATUS_SHIFT)) \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use le in \<open>auto simp: list_rel_imp_same_length\<close>)
  then have  \<open>(a ! (j - STATUS_SHIFT) AND 0b11, xarena_status (arena ! (j - STATUS_SHIFT))) \<in> uint32_nat_rel O status_rel\<close>
    using arena_dom_status_iff[OF valid j]
    by (cases \<open>arena ! (j - STATUS_SHIFT)\<close>)
      (auto intro!: relcomp.relcompI)
  then show ?rel
    using arena_dom_status_iff[OF valid j]
    by (cases \<open>arena ! (j - STATUS_SHIFT)\<close>)
      (auto simp: arena_el_rel_def)
qed


lemma isa_arena_status_arena_status:
  \<open>(uncurry isa_arena_status, uncurry (RETURN oo arena_status)) \<in>
    [uncurry arena_is_valid_clause_vdom]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>uint32_nat_rel O status_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_status_def arena_status_def
  by (intro frefI nres_relI)
   (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
        list_rel_imp_same_length arena_length_uint64_conv arena_lifting
        arena_is_valid_clause_idx_and_access_def arena_length_literal_conv
        arena_is_valid_clause_vdom_def arena_status_literal_conv
      intro!: ASSERT_refine_left)

lemma status_assn_alt_def:
  \<open>status_assn = pure (uint32_nat_rel O status_rel)\<close>
  unfolding hr_comp_pure by simp

lemma isa_arena_status_refine[sepref_fr_rules]:
  \<open>(uncurry arena_status_code, uncurry (RETURN \<circ>\<circ> arena_status))
  \<in> [uncurry arena_is_valid_clause_vdom]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> status_assn\<close>
  using arena_status_code.refine[FCOMP isa_arena_status_arena_status]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp status_assn_alt_def
  by (simp add: arl_assn_comp)


paragraph \<open>Swap literals\<close>

definition isa_arena_swap where
  \<open>isa_arena_swap C i j arena = do {
      ASSERT(C + i < length arena \<and> C + j < length arena);
      RETURN (swap arena (C+i) (C+j))
  }\<close>

sepref_definition swap_lits_code
  is \<open>uncurry3 isa_arena_swap\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  unfolding isa_arena_swap_def
  by sepref

definition swap_lits_pre where
  \<open>swap_lits_pre C i j arena \<longleftrightarrow> C + i < length arena \<and> C + j < length arena\<close>

lemma isa_arena_swap:
  \<open>(uncurry3 isa_arena_swap, uncurry3 (RETURN oooo swap_lits)) \<in>
    [uncurry3 swap_lits_pre]\<^sub>f
     nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<rightarrow>
    \<langle>\<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_status_def arena_status_def
  by (intro frefI nres_relI)
   (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
        list_rel_imp_same_length arena_length_uint64_conv arena_lifting
        arena_is_valid_clause_idx_and_access_def arena_length_literal_conv
        arena_is_valid_clause_vdom_def arena_status_literal_conv
        isa_arena_swap_def swap_lits_def swap_lits_pre_def
      intro!: ASSERT_refine_left swap_param)

lemma swap_lits_refine[sepref_fr_rules]:
  \<open>(uncurry3 swap_lits_code, uncurry3 (RETURN oooo swap_lits))
  \<in> [uncurry3 swap_lits_pre]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using swap_lits_code.refine[FCOMP isa_arena_swap]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp)


paragraph \<open>Update LBD\<close>

definition isa_update_lbd :: \<open>nat \<Rightarrow> uint32 \<Rightarrow> uint32 list \<Rightarrow> uint32 list nres\<close> where
  \<open>isa_update_lbd C lbd arena = do {
      ASSERT(C - LBD_SHIFT < length arena \<and> C \<ge> LBD_SHIFT);
      RETURN (arena [C - LBD_SHIFT := lbd])
  }\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN LBD_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: LBD_SHIFT_def)

sepref_definition isa_update_lbd_code
  is \<open>uncurry2 isa_update_lbd\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  unfolding isa_update_lbd_def
  by sepref

lemma arena_lbd_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> and
    b: \<open>(b, bb) \<in> uint32_nat_rel\<close>
  shows
    \<open>j - LBD_SHIFT < length arena\<close> (is ?le) and
    \<open>(a[j - LBD_SHIFT := b], update_lbd j bb arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
       (is ?unat)
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close>
    using arena_lifting[OF valid j] by (auto simp: )
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: LBD_SHIFT_def)

  show ?unat
     using length a b
     by
      (auto simp: arena_el_rel_def unat_lit_rel_def arena_lit_def update_lbd_def
        uint32_nat_rel_def br_def Collect_eq_comp
       split: arena_el.splits
       intro!: list_rel_update')
qed

definition update_lbd_pre where
  \<open>update_lbd_pre = (\<lambda>((C, lbd), arena). arena_is_valid_clause_idx arena C)\<close>

lemma isa_update_lbd:
  \<open>(uncurry2 isa_update_lbd, uncurry2 (RETURN ooo update_lbd)) \<in>
    [update_lbd_pre]\<^sub>f
     nat_rel \<times>\<^sub>f uint32_nat_rel \<times>\<^sub>f \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<rightarrow>
    \<langle>\<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_status_def arena_status_def
  by (intro frefI nres_relI)
   (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
        list_rel_imp_same_length arena_length_uint64_conv arena_lifting
        arena_is_valid_clause_idx_and_access_def arena_lbd_conv
        arena_is_valid_clause_vdom_def arena_status_literal_conv
        update_lbd_pre_def
        isa_arena_swap_def swap_lits_def swap_lits_pre_def isa_update_lbd_def
      intro!: ASSERT_refine_left swap_param)

lemma update_lbd_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_lbd_code, uncurry2 (RETURN ooo update_lbd))
  \<in> [update_lbd_pre]\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using isa_update_lbd_code.refine[FCOMP isa_update_lbd]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

lemma (in -) LBD_SHIFT_hnr:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN LBD_SHIFT) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: LBD_SHIFT_def uint64_nat_rel_def br_def)

sepref_definition (in -)isa_update_lbd_fast_code
  is \<open>uncurry2 isa_update_lbd\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  supply LBD_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_update_lbd_def
  by sepref

lemma update_lbd_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_lbd_fast_code, uncurry2 (RETURN ooo update_lbd))
  \<in> [update_lbd_pre]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using isa_update_lbd_fast_code.refine[FCOMP isa_update_lbd]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)



paragraph \<open>Get LBD\<close>

definition get_clause_LBD :: \<open>arena \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>get_clause_LBD arena C =  xarena_lbd (arena ! (C - LBD_SHIFT))\<close>

definition get_clause_LBD_pre where
  \<open>get_clause_LBD_pre = arena_is_valid_clause_idx\<close>

definition isa_get_clause_LBD :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint32 nres\<close> where
  \<open>isa_get_clause_LBD arena C = do {
      ASSERT(C - LBD_SHIFT < length arena \<and> C \<ge> LBD_SHIFT);
      RETURN (arena ! (C - LBD_SHIFT))
  }\<close>

lemma arena_get_lbd_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - LBD_SHIFT < length arena\<close> (is ?le) and
    \<open>LBD_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a ! (j - LBD_SHIFT),
        xarena_lbd (arena ! (j - LBD_SHIFT)))
       \<in> uint32_nat_rel\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_LBD (arena ! (j - LBD_SHIFT))\<close>
    using arena_lifting[OF valid j] by (auto simp: )
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: LBD_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have
    \<open>(a ! (j - LBD_SHIFT),
         (arena ! (j - LBD_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  then show \<open>(a ! (j - LBD_SHIFT),
        xarena_lbd (arena ! (j - LBD_SHIFT)))
       \<in> uint32_nat_rel\<close>
    using lbd by (cases \<open>arena ! (j - LBD_SHIFT)\<close>) (auto simp: arena_el_rel_def)
qed

lemma isa_get_clause_LBD_get_clause_LBD:
  \<open>(uncurry isa_get_clause_LBD, uncurry (RETURN oo get_clause_LBD)) \<in>
    [uncurry get_clause_LBD_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle>uint32_nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: isa_get_clause_LBD_def get_clause_LBD_def arena_get_lbd_conv
      get_clause_LBD_pre_def arena_is_valid_clause_idx_def
      list_rel_imp_same_length
      intro!: ASSERT_leI)

sepref_definition isa_get_clause_LBD_code
  is \<open>uncurry isa_get_clause_LBD\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  unfolding isa_get_clause_LBD_def fast_minus_def[symmetric]
  by sepref

lemma isa_get_clause_LBD_code[sepref_fr_rules]:
  \<open>(uncurry isa_get_clause_LBD_code, uncurry (RETURN \<circ>\<circ> get_clause_LBD))
     \<in> [uncurry get_clause_LBD_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using isa_get_clause_LBD_code.refine[FCOMP isa_get_clause_LBD_get_clause_LBD]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


paragraph \<open>Saved position\<close>

definition get_saved_pos_pre where
  \<open>get_saved_pos_pre arena C \<longleftrightarrow> arena_is_valid_clause_idx arena C \<and>
      arena_length arena C > MAX_LENGTH_SHORT_CLAUSE\<close>

definition isa_get_saved_pos :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint64 nres\<close> where
  \<open>isa_get_saved_pos arena C = do {
      ASSERT(C - POS_SHIFT < length arena \<and> C \<ge> POS_SHIFT);
      RETURN (uint64_of_uint32 (arena ! (C - POS_SHIFT)) + two_uint64)
  }\<close>

lemma arena_get_pos_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> and
    length: \<open>arena_length arena j > MAX_LENGTH_SHORT_CLAUSE\<close>
  shows
    \<open>j - POS_SHIFT < length arena\<close> (is ?le) and
    \<open>POS_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(uint64_of_uint32 (a ! (j - POS_SHIFT)) + two_uint64,
        arena_pos arena j)
       \<in> uint64_nat_rel\<close> (is ?rel) and
    \<open>nat_of_uint64
        (uint64_of_uint32
          (a ! (j - POS_SHIFT)) +
         two_uint64) =
       Suc (Suc (xarena_pos
                  (arena ! (j - POS_SHIFT))))\<close> (is ?eq')
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Pos (arena ! (j - POS_SHIFT))\<close> and
    ge: \<open>length (N \<propto> j) > MAX_LENGTH_SHORT_CLAUSE\<close>
    using arena_lifting[OF valid j] length by (auto simp: is_short_clause_def)
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: POS_SHIFT_def)
  show ?ge
    using j_ge ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have
    \<open>(a ! (j - POS_SHIFT),
         (arena ! (j - POS_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  moreover have \<open>Suc (Suc (nat_of_uint32 (a ! (j - POS_SHIFT)))) \<le> uint64_max\<close>
    using nat_of_uint32_le_uint32_max[of \<open>a ! (j - POS_SHIFT)\<close>]
    unfolding uint64_max_def uint32_max_def
    by auto
  ultimately show ?rel
    using lbd apply (cases \<open>arena ! (j - POS_SHIFT)\<close>)
    by (auto simp: arena_el_rel_def
      uint64_nat_rel_def br_def two_uint64_def uint32_nat_rel_def nat_of_uint64_add
      uint64_of_uint32_def nat_of_uint64_add arena_pos_def
      nat_of_uint64_uint64_of_nat_id nat_of_uint32_le_uint64_max)
  then show ?eq'
    using lbd \<open>?rel\<close> apply (cases \<open>arena ! (j - POS_SHIFT)\<close>)
    by (auto simp: arena_el_rel_def
      uint64_nat_rel_def br_def two_uint64_def uint32_nat_rel_def nat_of_uint64_add
      uint64_of_uint32_def nat_of_uint64_add arena_pos_def
      nat_of_uint64_uint64_of_nat_id nat_of_uint32_le_uint64_max)
qed

lemma isa_get_saved_pos_get_saved_pos:
  \<open>(uncurry isa_get_saved_pos, uncurry (RETURN oo arena_pos)) \<in>
    [uncurry get_saved_pos_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle>uint64_nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: isa_get_saved_pos_def arena_get_lbd_conv
      arena_is_valid_clause_idx_def arena_get_pos_conv
      list_rel_imp_same_length get_saved_pos_pre_def
      intro!: ASSERT_leI)


lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 5), uncurry0 (RETURN POS_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: SHIFTS_def)

sepref_definition isa_get_saved_pos_fast_code
  is \<open>uncurry isa_get_saved_pos\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules]
  unfolding isa_get_saved_pos_def
  by sepref

lemma get_saved_pos_code:
  \<open>(uncurry isa_get_saved_pos_fast_code, uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_get_saved_pos_fast_code.refine[FCOMP isa_get_saved_pos_get_saved_pos]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

definition isa_get_saved_pos' :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>isa_get_saved_pos' arena C = do {
      pos \<leftarrow> isa_get_saved_pos arena C;
      RETURN (nat_of_uint64 pos)
  }\<close>


sepref_definition isa_get_saved_pos_code
  is \<open>uncurry isa_get_saved_pos'\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules]
  unfolding isa_get_saved_pos_def isa_get_saved_pos'_def
  by sepref

lemma isa_get_saved_pos_get_saved_pos':
  \<open>(uncurry isa_get_saved_pos', uncurry (RETURN oo arena_pos)) \<in>
    [uncurry get_saved_pos_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: isa_get_saved_pos_def arena_pos_def
      arena_is_valid_clause_idx_def arena_get_pos_conv isa_get_saved_pos'_def
      list_rel_imp_same_length get_saved_pos_pre_def
      intro!: ASSERT_leI)

(* TODO check if we use this version anywhere *)
lemma get_saved_pos_code':
  \<open>(uncurry isa_get_saved_pos_code, uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  using isa_get_saved_pos_code.refine[FCOMP isa_get_saved_pos_get_saved_pos']
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

lemma (in -) POS_SHIFT_uint64_hnr:
  \<open>(uncurry0 (return 5), uncurry0 (RETURN POS_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: POS_SHIFT_def uint64_nat_rel_def br_def)


sepref_definition isa_get_saved_pos_fast_code2
  is \<open>uncurry isa_get_saved_pos\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules] POS_SHIFT_uint64_hnr[sepref_fr_rules]
  unfolding isa_get_saved_pos_def
  by sepref

lemma get_saved_pos_code2[sepref_fr_rules]:
  \<open>(uncurry isa_get_saved_pos_fast_code2, uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_get_saved_pos_fast_code2.refine[FCOMP isa_get_saved_pos_get_saved_pos]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


paragraph \<open>Update Saved Position\<close>

(* TODO: converting from nat to uint32 is a little stupid and always useless (uint64 is enough everytime) *)
definition isa_update_pos :: \<open>nat \<Rightarrow> nat \<Rightarrow> uint32 list \<Rightarrow> uint32 list nres\<close> where
  \<open>isa_update_pos C n arena = do {
      ASSERT(C - POS_SHIFT < length arena \<and> C \<ge> POS_SHIFT \<and> n \<ge> 2 \<and> n - 2 \<le> uint32_max);
      RETURN (arena [C - POS_SHIFT := (uint32_of_nat (n - 2))])
  }\<close>

sepref_definition isa_update_pos_code
  is \<open>uncurry2 isa_update_pos\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  supply minus_uint32_assn[sepref_fr_rules]
  unfolding isa_update_pos_def
  by sepref

definition arena_update_pos where
  \<open>arena_update_pos C pos arena = arena[C - POS_SHIFT := APos (pos - 2)]\<close>

lemma arena_update_pos_alt_def:
  \<open>arena_update_pos C i N = update_pos_direct C (i - 2) N\<close>
  by (auto simp: arena_update_pos_def update_pos_direct_def)

lemma arena_update_pos_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> and
    length: \<open>arena_length arena j > MAX_LENGTH_SHORT_CLAUSE\<close> and
    pos_le: \<open>pos \<le> arena_length arena j\<close> and
    b': \<open>pos \<ge> 2\<close>
  shows
    \<open>j - POS_SHIFT < length arena\<close> (is ?le) and
    \<open>j \<ge> POS_SHIFT\<close> (is ?ge)
    \<open>(a[j - POS_SHIFT := uint32_of_nat (pos - 2)], arena_update_pos j pos arena) \<in>
      \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> (is ?unat) and
    \<open>pos - 2 \<le> uint_max\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    long: \<open>is_long_clause (N \<propto> j)\<close> and
    pos: \<open>is_Pos (arena ! (j - POS_SHIFT))\<close> and
    is_size: \<open>is_Size (arena ! (j - SIZE_SHIFT))\<close>
    using arena_lifting[OF valid j] length by (auto simp: is_short_clause_def header_size_def)
  show le': ?le and ?ge
    using le j_ge long unfolding length[symmetric] header_size_def
    by (auto split: if_splits simp: POS_SHIFT_def)
  have
    \<open>(a ! (j - SIZE_SHIFT),
         (arena ! (j - SIZE_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  then show \<open>pos - 2 \<le> uint_max\<close>
    using b' length is_size pos_le nat_of_uint32_le_uint32_max[of \<open>a ! (j - SIZE_SHIFT)\<close>]
    by (cases \<open>arena ! (j - SIZE_SHIFT)\<close>)
      (auto simp: uint32_nat_rel_def br_def arena_el_rel_def arena_length_def)
  then show ?unat
    using length a pos b'
      valid_arena_update_pos[OF valid j \<open>is_long_clause (N \<propto> j)\<close> ]
    by (auto simp: arena_el_rel_def unat_lit_rel_def arena_lit_def arena_update_pos_def
        uint32_nat_rel_def br_def Collect_eq_comp nat_of_uint32_notle_minus
        nat_of_uint32_uint32_of_nat_id
       split: arena_el.splits
       intro!: list_rel_update')
qed

definition isa_update_pos_pre where
  \<open>isa_update_pos_pre = (\<lambda>((C, lbd), arena). arena_is_valid_clause_idx arena C \<and> lbd \<ge> 2 \<and>
      lbd \<le> arena_length arena C \<and> arena_length arena C > MAX_LENGTH_SHORT_CLAUSE \<and>
      lbd \<ge> 2)\<close>

lemma isa_update_pos:
  \<open>(uncurry2 isa_update_pos, uncurry2 (RETURN ooo arena_update_pos)) \<in>
    [isa_update_pos_pre]\<^sub>f
     nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<rightarrow>
    \<langle>\<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_status_def arena_status_def
  by (intro frefI nres_relI)
    (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
        list_rel_imp_same_length arena_length_uint64_conv arena_lifting
        arena_is_valid_clause_idx_and_access_def arena_lbd_conv
        arena_is_valid_clause_vdom_def arena_status_literal_conv
        update_lbd_pre_def isa_update_pos_def update_pos_direct_def isa_update_pos_pre_def
        isa_arena_swap_def swap_lits_def swap_lits_pre_def isa_update_lbd_def
        arena_update_pos_conv
      intro!: ASSERT_refine_left swap_param)

lemma isa_update_pos_code_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_pos_code, uncurry2 (RETURN ooo arena_update_pos))
  \<in> [isa_update_pos_pre]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using isa_update_pos_code.refine[FCOMP isa_update_pos]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp isa_update_pos_pre_def)

lemma MAX_LENGTH_SHORT_CLAUSE_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 4), uncurry0 (RETURN MAX_LENGTH_SHORT_CLAUSE)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)


paragraph \<open>Mark clause as garbage\<close>

definition mark_garbage_pre where
  \<open>mark_garbage_pre = (\<lambda>(arena, C). arena_is_valid_clause_idx arena C)\<close>

definition mark_garbage where
  \<open>mark_garbage arena C = do {
    ASSERT(C \<ge> STATUS_SHIFT \<and> C - STATUS_SHIFT < length arena);
    RETURN (arena[C - STATUS_SHIFT := (3 :: uint32)])
  }\<close>


lemma mark_garbage_pre:
  assumes
    j: \<open>j \<in># dom_m N\<close> and
    valid: \<open>valid_arena arena N x\<close> and
    arena: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>STATUS_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a[j - STATUS_SHIFT := 3], arena[j - STATUS_SHIFT := AStatus DELETED False])
         \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> (is ?rel) and
    \<open>j - STATUS_SHIFT < length arena\<close> (is ?le)
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close>
    using arena_lifting[OF valid j] by (auto simp: )
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: SHIFTS_def)

  show ?rel
     apply (rule list_rel_update'[OF arena])
     using length
     by
      (auto simp: arena_el_rel_def unat_lit_rel_def arena_lit_def update_lbd_def
        uint32_nat_rel_def br_def Collect_eq_comp status_rel_def bitfield_rel_def
       split: arena_el.splits
       intro!: )
  show ?ge
    using le j_ge unfolding length[symmetric] header_size_def
    by (auto split: if_splits simp: SHIFTS_def)
qed

sepref_definition mark_garbage_code
  is \<open>uncurry mark_garbage\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  unfolding mark_garbage_def fast_minus_def[symmetric]
  by sepref

lemma isa_mark_garbage:
  \<open>(uncurry mark_garbage, uncurry (RETURN oo extra_information_mark_to_delete)) \<in>
    [mark_garbage_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel  \<rightarrow>
    \<langle>\<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_status_def arena_status_def
  by (intro frefI nres_relI)
    (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
        list_rel_imp_same_length arena_length_uint64_conv arena_lifting
        arena_is_valid_clause_idx_and_access_def arena_lbd_conv
        arena_is_valid_clause_vdom_def arena_status_literal_conv mark_garbage_pre
        mark_garbage_def mark_garbage_pre_def extra_information_mark_to_delete_def
        isa_arena_swap_def swap_lits_def swap_lits_pre_def isa_update_lbd_def
      intro!: ASSERT_refine_left)

lemma mark_garbage_hnr[sepref_fr_rules]:
  \<open>(uncurry mark_garbage_code, uncurry (RETURN oo extra_information_mark_to_delete))
  \<in> [mark_garbage_pre]\<^sub>a  arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using mark_garbage_code.refine[FCOMP isa_mark_garbage]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


paragraph \<open>Activity\<close>
definition arena_act_pre where
  \<open>arena_act_pre = arena_is_valid_clause_idx\<close>

definition isa_arena_act :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint32 nres\<close> where
  \<open>isa_arena_act arena C = do {
      ASSERT(C - ACTIVITY_SHIFT < length arena \<and> C \<ge> ACTIVITY_SHIFT);
      RETURN (arena ! (C - ACTIVITY_SHIFT))
  }\<close>

lemma arena_act_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - ACTIVITY_SHIFT < length arena\<close> (is ?le) and
    \<open>ACTIVITY_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a ! (j - ACTIVITY_SHIFT),
        xarena_act (arena ! (j - ACTIVITY_SHIFT)))
       \<in> uint32_nat_rel\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Act (arena ! (j - ACTIVITY_SHIFT))\<close>
    using arena_lifting[OF valid j] by auto
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: ACTIVITY_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have
    \<open>(a ! (j - ACTIVITY_SHIFT),
         (arena ! (j - ACTIVITY_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  then show \<open>(a ! (j - ACTIVITY_SHIFT),
        xarena_act (arena ! (j - ACTIVITY_SHIFT)))
       \<in> uint32_nat_rel\<close>
    using lbd by (cases \<open>arena ! (j - ACTIVITY_SHIFT)\<close>) (auto simp: arena_el_rel_def)
qed

lemma isa_arena_act_arena_act:
  \<open>(uncurry isa_arena_act, uncurry (RETURN oo arena_act)) \<in>
    [uncurry arena_act_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle>uint32_nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: isa_arena_act_def arena_act_def arena_get_lbd_conv
      arena_act_pre_def arena_is_valid_clause_idx_def
      list_rel_imp_same_length arena_act_conv
      intro!: ASSERT_leI)

sepref_definition isa_arena_act_code
  is \<open>uncurry isa_arena_act\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  unfolding isa_arena_act_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref

lemma isa_arena_act_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_act_code, uncurry (RETURN \<circ>\<circ> arena_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using isa_arena_act_code.refine[FCOMP isa_arena_act_arena_act]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


paragraph \<open>Increment Activity\<close>

definition isa_arena_incr_act :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint32 list nres\<close> where
  \<open>isa_arena_incr_act arena C = do {
      ASSERT(C - ACTIVITY_SHIFT < length arena \<and> C \<ge> ACTIVITY_SHIFT);
      let act = arena ! (C - ACTIVITY_SHIFT);
      RETURN (arena[C - ACTIVITY_SHIFT := act + 1])
  }\<close>

definition arena_incr_act where
  \<open>arena_incr_act arena i = arena[i - ACTIVITY_SHIFT := AActivity (sum_mod_uint32_max 1 (xarena_act (arena!(i - ACTIVITY_SHIFT))))]\<close>

lemma arena_incr_act_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - ACTIVITY_SHIFT < length arena\<close> (is ?le) and
    \<open>ACTIVITY_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a[j - ACTIVITY_SHIFT := a ! (j - ACTIVITY_SHIFT) + 1], arena_incr_act arena j) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Act (arena ! (j - ACTIVITY_SHIFT))\<close>
    using arena_lifting[OF valid j] by auto
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: ACTIVITY_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have b:
    \<open>(a ! (j - ACTIVITY_SHIFT),
         (arena ! (j - ACTIVITY_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  show \<open>(a[j - ACTIVITY_SHIFT := a ! (j - ACTIVITY_SHIFT) + 1], arena_incr_act arena j) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
    unfolding arena_incr_act_def
    by (rule list_rel_update'[OF a])
      (cases \<open>arena ! (j - ACTIVITY_SHIFT)\<close>;
      use lbd b in \<open>auto simp add: uint32_nat_rel_def br_def arena_el_rel_def
        Collect_eq_comp sum_mod_uint32_max_def nat_of_uint32_plus\<close>)
qed


lemma isa_arena_incr_act_arena_incr_act:
  \<open>(uncurry isa_arena_incr_act, uncurry (RETURN oo arena_incr_act)) \<in>
    [uncurry arena_act_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: isa_arena_incr_act_def arena_act_def arena_get_lbd_conv
      arena_act_pre_def arena_is_valid_clause_idx_def arena_incr_act_conv
      list_rel_imp_same_length arena_act_conv
      intro!: ASSERT_leI)

sepref_definition isa_arena_incr_act_code
  is \<open>uncurry isa_arena_incr_act\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_arena_incr_act_def ACTIVITY_SHIFT_def fast_minus_def
  by sepref

lemma isa_arena_incr_act_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_incr_act_code, uncurry (RETURN \<circ>\<circ> arena_incr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_arena_incr_act_code.refine[FCOMP isa_arena_incr_act_arena_incr_act]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

lemma length_clause_slice_list_update[simp]:
  \<open>length (clause_slice (arena[i := x]) a b) = length (clause_slice arena a b)\<close>
  by (auto simp: Misc.slice_def)

lemma length_arena_incr_act[simp]:
  \<open>length (arena_incr_act arena C) = length arena\<close>
  by (auto simp: arena_incr_act_def)

lemma valid_arena_arena_incr_act:
  assumes C: \<open>C \<in># dom_m N\<close> and valid: \<open>valid_arena arena N vdom\<close>
  shows
   \<open>valid_arena (arena_incr_act arena C) N vdom\<close>
proof -
  let ?arena = \<open>arena_incr_act arena C\<close>
  have act: \<open>\<forall>i\<in>#dom_m N.
     i < length (arena) \<and>
     header_size (N \<propto> i) \<le> i \<and>
     xarena_active_clause (clause_slice arena N i)
      (the (fmlookup N i))\<close> and
    dead: \<open>\<And>i. i \<in> vdom \<Longrightarrow> i \<notin># dom_m N \<Longrightarrow> i < length arena \<and>
           4 \<le> i \<and> arena_dead_clause (Misc.slice (i - 4) i arena)\<close> and
    C_ge: \<open>header_size (N \<propto> C) \<le> C\<close> and
    C_le: \<open>C < length arena\<close> and
    C_act: \<open>xarena_active_clause (clause_slice arena N C)
      (the (fmlookup N C))\<close>
    using assms
    by (auto simp: valid_arena_def)
  have
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - LBD_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - LBD_SHIFT)\<close> and
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - STATUS_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - STATUS_SHIFT)\<close> and
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - SIZE_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - SIZE_SHIFT)\<close> and
   [simp]: \<open>is_long_clause (N \<propto> C) \<Longrightarrow> clause_slice ?arena N C ! (header_size (N \<propto> C) - POS_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - POS_SHIFT)\<close> and
   [simp]: \<open>length (clause_slice  ?arena N C) = length (clause_slice arena N C)\<close> and
   [simp]: \<open>is_Act (clause_slice ?arena N C ! (header_size (N \<propto> C) - ACTIVITY_SHIFT))\<close> and
   [simp]: \<open>Misc.slice C (C + length (N \<propto> C)) ?arena =
     Misc.slice C (C + length (N \<propto> C)) arena\<close>
    using C_le C_ge unfolding SHIFTS_def arena_incr_act_def header_size_def
    by (auto simp: Misc.slice_def drop_update_swap split: if_splits)

  have \<open>xarena_active_clause (clause_slice ?arena N C) (the (fmlookup N C))\<close>
    using C_act C_le C_ge unfolding xarena_active_clause_alt_def
    by simp

  then have 1: \<open>xarena_active_clause (clause_slice arena N i) (the (fmlookup N i)) \<Longrightarrow>
     xarena_active_clause (clause_slice (arena_incr_act arena C) N i) (the (fmlookup N i))\<close>
    if \<open>i \<in># dom_m N\<close>
    for i
    using minimal_difference_between_valid_index[of N arena C i, OF act]
      minimal_difference_between_valid_index[of N arena i C, OF act] assms
      that C_ge
    by (cases \<open>C < i\<close>; cases \<open>C > i\<close>)
      (auto simp: arena_incr_act_def header_size_def ACTIVITY_SHIFT_def
      split: if_splits)

  have 2:
    \<open>arena_dead_clause (Misc.slice (i - 4) i ?arena)\<close>
    if \<open>i \<in> vdom\<close>\<open>i \<notin># dom_m N\<close>\<open>arena_dead_clause (Misc.slice (i - 4) i arena)\<close>
    for i
  proof -
    have i_ge: \<open>i \<ge> 4\<close> \<open>i < length arena\<close>
      using that valid unfolding valid_arena_def
      by auto
    show ?thesis
      using dead[of i] that C_le C_ge
      minimal_difference_between_invalid_index[OF valid, of C i]
      minimal_difference_between_invalid_index2[OF valid, of C i]
      by (cases \<open>C < i\<close>; cases \<open>C > i\<close>)
        (auto simp: arena_incr_act_def header_size_def ACTIVITY_SHIFT_def C
          split: if_splits)
  qed
  show ?thesis
    using 1 2 valid
    by (auto simp: valid_arena_def)
qed


paragraph \<open>Mark used\<close>

definition isa_mark_used :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint32 list nres\<close> where
  \<open>isa_mark_used arena C = do {
      ASSERT(C - STATUS_SHIFT < length arena \<and> C \<ge> STATUS_SHIFT);
      let act = arena ! (C - STATUS_SHIFT);
      RETURN (arena[C - STATUS_SHIFT := act OR 0b100])
  }\<close>

definition mark_used where
  \<open>mark_used arena i =
     arena[i - STATUS_SHIFT := AStatus (xarena_status (arena!(i - STATUS_SHIFT))) True]\<close>

lemma isa_mark_used_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - STATUS_SHIFT < length arena\<close> (is ?le) and
    \<open>STATUS_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a[j - STATUS_SHIFT := a ! (j - STATUS_SHIFT) OR 4], mark_used arena j) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Status (arena ! (j - STATUS_SHIFT))\<close>
    using arena_lifting[OF valid j] by auto
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: STATUS_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have b:
    \<open>(a ! (j - STATUS_SHIFT),
         (arena ! (j - STATUS_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  have [simp]: \<open>(a OR 4) AND 3 = a AND 3\<close> for a :: int
    supply [[show_types]]
    by (smt BIT_special_simps(1) BIT_special_simps(4) One_nat_def bbw_ao_dist expand_BIT(2)
      int_and_comm int_and_numerals(17) int_and_numerals(3) int_or_extra_simps(1)
      numeral_One numeral_plus_one of_nat_numeral semiring_1_class.of_nat_simps(1)
      semiring_1_class.of_nat_simps(2) semiring_norm(2) semiring_norm(8))
  have Pos: \<open>b \<ge>0 \<Longrightarrow> a \<le> a OR b\<close> for a b :: int
    by (rule le_int_or)
      (auto simp: bin_sign_def)
  have [simp]: \<open>(0::int) \<le> int a OR (4::int)\<close> for a :: nat
    by (rule order_trans[OF _ Pos])
      auto
  then have [simp]: \<open>(a OR 4) AND 3 = a AND 3\<close> for a :: nat
    supply [[show_types]]
    unfolding bitAND_nat_def bitOR_nat_def
    by auto

  have [simp]: \<open>(a OR 4) AND 4 = 4\<close> for a :: nat
    supply [[show_types]]
    unfolding bitAND_nat_def bitOR_nat_def
    by auto
  have nat_of_uint32_4: \<open>4 = nat_of_uint32 4\<close>
    by auto
  have [simp]: \<open>nat_of_uint32 (a OR 4) = nat_of_uint32 a OR 4\<close> for a
    by (subst nat_of_uint32_4, subst nat_of_uint32_ao) simp

  show \<open>(a[j - STATUS_SHIFT := a ! (j - STATUS_SHIFT) OR 0b100],
      mark_used arena j) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
    unfolding mark_used_def
    by (rule list_rel_update'[OF a])
      (cases \<open>arena ! (j - STATUS_SHIFT)\<close>;
      use lbd b in \<open>auto simp add: uint32_nat_rel_def br_def arena_el_rel_def
          status_rel_def bitfield_rel_def
          Collect_eq_comp sum_mod_uint32_max_def nat_of_uint32_plus\<close>)
qed


lemma isa_mark_used_mark_used:
  \<open>(uncurry isa_mark_used, uncurry (RETURN oo mark_used)) \<in>
    [uncurry arena_act_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: isa_mark_used_def arena_get_lbd_conv
      arena_act_pre_def arena_is_valid_clause_idx_def arena_incr_act_conv
      list_rel_imp_same_length isa_mark_used_conv
      intro!: ASSERT_leI)

sepref_definition isa_mark_used_code
  is \<open>uncurry isa_mark_used\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_mark_used_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref

lemma isa_mark_used_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_used_code, uncurry (RETURN \<circ>\<circ> mark_used))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_used_code.refine[FCOMP isa_mark_used_mark_used]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

definition four_uint32 where \<open>four_uint32 = (4 :: uint32)\<close>

lemma four_uint32_hnr:
  \<open>(uncurry0 (return 4), uncurry0 (RETURN (four_uint32 :: uint32)) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def four_uint32_def)

sepref_definition isa_mark_used_fast_code
  is \<open>uncurry isa_mark_used\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  supply four_uint32_hnr[sepref_fr_rules] STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_mark_used_def four_uint32_def[symmetric]
  by sepref

lemma isa_mark_used_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_used_fast_code, uncurry (RETURN \<circ>\<circ> mark_used))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_used_fast_code.refine[FCOMP isa_mark_used_mark_used]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

lemma length_mark_used[simp]: \<open>length (mark_used arena C) = length arena\<close>
  by (auto simp: mark_used_def)

lemma valid_arena_mark_used:
  assumes C: \<open>C \<in># dom_m N\<close> and valid: \<open>valid_arena arena N vdom\<close>
  shows
   \<open>valid_arena (mark_used arena C) N vdom\<close>
proof -
  let ?arena = \<open>mark_used arena C\<close>
  have act: \<open>\<forall>i\<in>#dom_m N.
     i < length (arena) \<and>
     header_size (N \<propto> i) \<le> i \<and>
     xarena_active_clause (clause_slice arena N i)
      (the (fmlookup N i))\<close> and
    dead: \<open>\<And>i. i \<in> vdom \<Longrightarrow> i \<notin># dom_m N \<Longrightarrow> i < length arena \<and>
           4 \<le> i \<and> arena_dead_clause (Misc.slice (i - 4) i arena)\<close> and
    C_ge: \<open>header_size (N \<propto> C) \<le> C\<close> and
    C_le: \<open>C < length arena\<close> and
    C_act: \<open>xarena_active_clause (clause_slice arena N C)
      (the (fmlookup N C))\<close>
    using assms
    by (auto simp: valid_arena_def)
  have
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - LBD_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - LBD_SHIFT)\<close> and
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - STATUS_SHIFT) =
           AStatus (xarena_status (clause_slice arena N C ! (header_size (N \<propto> C) - STATUS_SHIFT)))
             True\<close> and
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - SIZE_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - SIZE_SHIFT)\<close> and
   [simp]: \<open>is_long_clause (N \<propto> C) \<Longrightarrow> clause_slice ?arena N C ! (header_size (N \<propto> C) - POS_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - POS_SHIFT)\<close> and
   [simp]: \<open>length (clause_slice  ?arena N C) = length (clause_slice arena N C)\<close> and
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - ACTIVITY_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - ACTIVITY_SHIFT)\<close> and
   [simp]: \<open>Misc.slice C (C + length (N \<propto> C)) ?arena =
     Misc.slice C (C + length (N \<propto> C)) arena\<close>
    using C_le C_ge unfolding SHIFTS_def mark_used_def header_size_def
    by (auto simp: Misc.slice_def drop_update_swap split: if_splits)

  have \<open>xarena_active_clause (clause_slice ?arena N C) (the (fmlookup N C))\<close>
    using C_act C_le C_ge unfolding xarena_active_clause_alt_def
    by simp

  then have 1: \<open>xarena_active_clause (clause_slice arena N i) (the (fmlookup N i)) \<Longrightarrow>
     xarena_active_clause (clause_slice (mark_used arena C) N i) (the (fmlookup N i))\<close>
    if \<open>i \<in># dom_m N\<close>
    for i
    using minimal_difference_between_valid_index[of N arena C i, OF act]
      minimal_difference_between_valid_index[of N arena i C, OF act] assms
      that C_ge
    by (cases \<open>C < i\<close>; cases \<open>C > i\<close>)
      (auto simp: mark_used_def header_size_def STATUS_SHIFT_def
      split: if_splits)

  have 2:
    \<open>arena_dead_clause (Misc.slice (i - 4) i ?arena)\<close>
    if \<open>i \<in> vdom\<close>\<open>i \<notin># dom_m N\<close>\<open>arena_dead_clause (Misc.slice (i - 4) i arena)\<close>
    for i
  proof -
    have i_ge: \<open>i \<ge> 4\<close> \<open>i < length arena\<close>
      using that valid unfolding valid_arena_def
      by auto
    show ?thesis
      using dead[of i] that C_le C_ge
      minimal_difference_between_invalid_index[OF valid, of C i]
      minimal_difference_between_invalid_index2[OF valid, of C i]
      by (cases \<open>C < i\<close>; cases \<open>C > i\<close>)
        (auto simp: mark_used_def header_size_def STATUS_SHIFT_def C
          split: if_splits)
  qed
  show ?thesis
    using 1 2 valid
    by (auto simp: valid_arena_def)
qed


paragraph \<open>Mark unused\<close>

definition isa_mark_unused :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint32 list nres\<close> where
  \<open>isa_mark_unused arena C = do {
      ASSERT(C - STATUS_SHIFT < length arena \<and> C \<ge> STATUS_SHIFT);
      let act = arena ! (C - STATUS_SHIFT);
      RETURN (arena[C - STATUS_SHIFT := act AND 0b11])
  }\<close>

definition mark_unused where
  \<open>mark_unused arena i =
     arena[i - STATUS_SHIFT := AStatus (xarena_status (arena!(i - STATUS_SHIFT))) False]\<close>

lemma isa_mark_unused_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - STATUS_SHIFT < length arena\<close> (is ?le) and
    \<open>STATUS_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a[j - STATUS_SHIFT := a ! (j - STATUS_SHIFT) AND 3], mark_unused arena j) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Status (arena ! (j - STATUS_SHIFT))\<close>
    using arena_lifting[OF valid j] by auto
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: STATUS_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have b:
    \<open>(a ! (j - STATUS_SHIFT),
         (arena ! (j - STATUS_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  have [simp]: \<open>(a OR 4) AND 3 = a AND 3\<close> for a :: int
    supply [[show_types]]
    by (smt BIT_special_simps(1) BIT_special_simps(4) One_nat_def bbw_ao_dist expand_BIT(2)
      int_and_comm int_and_numerals(17) int_and_numerals(3) int_or_extra_simps(1)
      numeral_One numeral_plus_one of_nat_numeral semiring_1_class.of_nat_simps(1)
      semiring_1_class.of_nat_simps(2) semiring_norm(2) semiring_norm(8))
  have Pos: \<open>b \<ge>0 \<Longrightarrow> a \<le> a OR b\<close> for a b :: int
    by (rule le_int_or)
      (auto simp: bin_sign_def)
  have [simp]: \<open>(0::int) \<le> int a OR (4::int)\<close> for a :: nat
    by (rule order_trans[OF _ Pos])
      auto
  then have [simp]: \<open>(a OR 4) AND 3 = a AND 3\<close> for a :: nat
    supply [[show_types]]
    unfolding bitAND_nat_def bitOR_nat_def
    by auto

  have [simp]: \<open>(a OR 4) AND 4 = 4\<close> for a :: nat
    supply [[show_types]]
    unfolding bitAND_nat_def bitOR_nat_def
    by auto
  have nat_of_uint32_4: \<open>3 = nat_of_uint32 3\<close>
    by auto
  have [simp]: \<open>nat_of_uint32 (a AND 3) = nat_of_uint32 a AND 3\<close> for a
    by (subst nat_of_uint32_4, subst nat_of_uint32_ao) simp
  (* TODO mark nat_0_AND as [simp] *)
  show \<open>(a[j - STATUS_SHIFT := a ! (j - STATUS_SHIFT) AND 3],
      mark_unused arena j) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
    unfolding mark_unused_def
    supply [[show_types]]
    by (rule list_rel_update'[OF a])
      (cases \<open>arena ! (j - STATUS_SHIFT)\<close>;
      use lbd b in \<open>auto simp add: uint32_nat_rel_def br_def arena_el_rel_def
          status_rel_def bitfield_rel_def nat_0_AND
          Collect_eq_comp sum_mod_uint32_max_def nat_of_uint32_plus\<close>)
qed


lemma isa_mark_unused_mark_unused:
  \<open>(uncurry isa_mark_unused, uncurry (RETURN oo mark_unused)) \<in>
    [uncurry arena_act_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: isa_mark_unused_def arena_get_lbd_conv
      arena_act_pre_def arena_is_valid_clause_idx_def arena_incr_act_conv
      list_rel_imp_same_length isa_mark_unused_conv
      intro!: ASSERT_leI)

sepref_definition isa_mark_unused_code
  is \<open>uncurry isa_mark_unused\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_mark_unused_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref

lemma isa_mark_unused_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_unused_code, uncurry (RETURN \<circ>\<circ> mark_unused))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_unused_code.refine[FCOMP isa_mark_unused_mark_unused]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_mark_unused_fast_code
  is \<open>uncurry isa_mark_unused\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  supply STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_mark_unused_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref

lemma isa_mark_unused_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_unused_fast_code, uncurry (RETURN \<circ>\<circ> mark_unused))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_unused_fast_code.refine[FCOMP isa_mark_unused_mark_unused]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

lemma length_mark_unused[simp]: \<open>length (mark_unused arena C) = length arena\<close>
  by (auto simp: mark_unused_def)

lemma valid_arena_mark_unused:
  assumes C: \<open>C \<in># dom_m N\<close> and valid: \<open>valid_arena arena N vdom\<close>
  shows
   \<open>valid_arena (mark_unused arena C) N vdom\<close>
proof -
  let ?arena = \<open>mark_unused arena C\<close>
  have act: \<open>\<forall>i\<in>#dom_m N.
     i < length (arena) \<and>
     header_size (N \<propto> i) \<le> i \<and>
     xarena_active_clause (clause_slice arena N i)
      (the (fmlookup N i))\<close> and
    dead: \<open>\<And>i. i \<in> vdom \<Longrightarrow> i \<notin># dom_m N \<Longrightarrow> i < length arena \<and>
           4 \<le> i \<and> arena_dead_clause (Misc.slice (i - 4) i arena)\<close> and
    C_ge: \<open>header_size (N \<propto> C) \<le> C\<close> and
    C_le: \<open>C < length arena\<close> and
    C_act: \<open>xarena_active_clause (clause_slice arena N C)
      (the (fmlookup N C))\<close>
    using assms
    by (auto simp: valid_arena_def)
  have
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - LBD_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - LBD_SHIFT)\<close> and
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - STATUS_SHIFT) =
           AStatus (xarena_status (clause_slice arena N C ! (header_size (N \<propto> C) - STATUS_SHIFT)))
             False\<close> and
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - SIZE_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - SIZE_SHIFT)\<close> and
   [simp]: \<open>is_long_clause (N \<propto> C) \<Longrightarrow> clause_slice ?arena N C ! (header_size (N \<propto> C) - POS_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - POS_SHIFT)\<close> and
   [simp]: \<open>length (clause_slice  ?arena N C) = length (clause_slice arena N C)\<close> and
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - ACTIVITY_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - ACTIVITY_SHIFT)\<close> and
   [simp]: \<open>Misc.slice C (C + length (N \<propto> C)) ?arena =
     Misc.slice C (C + length (N \<propto> C)) arena\<close>
    using C_le C_ge unfolding SHIFTS_def mark_unused_def header_size_def
    by (auto simp: Misc.slice_def drop_update_swap split: if_splits)

  have \<open>xarena_active_clause (clause_slice ?arena N C) (the (fmlookup N C))\<close>
    using C_act C_le C_ge unfolding xarena_active_clause_alt_def
    by simp

  then have 1: \<open>xarena_active_clause (clause_slice arena N i) (the (fmlookup N i)) \<Longrightarrow>
     xarena_active_clause (clause_slice (mark_unused arena C) N i) (the (fmlookup N i))\<close>
    if \<open>i \<in># dom_m N\<close>
    for i
    using minimal_difference_between_valid_index[of N arena C i, OF act]
      minimal_difference_between_valid_index[of N arena i C, OF act] assms
      that C_ge
    by (cases \<open>C < i\<close>; cases \<open>C > i\<close>)
      (auto simp: mark_unused_def header_size_def STATUS_SHIFT_def
      split: if_splits)

  have 2:
    \<open>arena_dead_clause (Misc.slice (i - 4) i ?arena)\<close>
    if \<open>i \<in> vdom\<close>\<open>i \<notin># dom_m N\<close>\<open>arena_dead_clause (Misc.slice (i - 4) i arena)\<close>
    for i
  proof -
    have i_ge: \<open>i \<ge> 4\<close> \<open>i < length arena\<close>
      using that valid unfolding valid_arena_def
      by auto
    show ?thesis
      using dead[of i] that C_le C_ge
      minimal_difference_between_invalid_index[OF valid, of C i]
      minimal_difference_between_invalid_index2[OF valid, of C i]
      by (cases \<open>C < i\<close>; cases \<open>C > i\<close>)
        (auto simp: mark_unused_def header_size_def STATUS_SHIFT_def C
          split: if_splits)
  qed
  show ?thesis
    using 1 2 valid
    by (auto simp: valid_arena_def)
qed


paragraph \<open>Marked as used?\<close>

definition marked_as_used :: \<open>arena \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>marked_as_used arena C =  xarena_used (arena ! (C - STATUS_SHIFT))\<close>

definition marked_as_used_pre where
  \<open>marked_as_used_pre = arena_is_valid_clause_idx\<close>

definition isa_marked_as_used :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> bool nres\<close> where
  \<open>isa_marked_as_used arena C = do {
      ASSERT(C - STATUS_SHIFT < length arena \<and> C \<ge> STATUS_SHIFT);
      RETURN (arena ! (C - STATUS_SHIFT) AND 4 \<noteq> 0)
  }\<close>



lemma arena_marked_as_used_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - STATUS_SHIFT < length arena\<close> (is ?le) and
    \<open>STATUS_SHIFT \<le> j\<close> (is ?ge) and
    \<open>a ! (j - STATUS_SHIFT) AND 4 \<noteq> 0 \<longleftrightarrow>
        marked_as_used arena j\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1: \<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2: \<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Status (arena ! (j - STATUS_SHIFT))\<close>
    using arena_lifting[OF valid j] by (auto simp: )
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: STATUS_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have [simp]: \<open>a \<noteq> 0 \<longleftrightarrow> nat_of_uint32 a \<noteq> 0\<close> for a:: uint32
    by (simp add: nat_of_uint32_0_iff)
  have
    \<open>(a ! (j - STATUS_SHIFT),
         (arena ! (j - STATUS_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  then show \<open>a ! (j - STATUS_SHIFT) AND 4 \<noteq> 0 \<longleftrightarrow>
        marked_as_used arena j\<close>
    using lbd by (cases \<open>arena ! (j - STATUS_SHIFT)\<close>)
      (auto simp: arena_el_rel_def bitfield_rel_def nat_of_uint32_ao[symmetric]
      marked_as_used_def uint32_nat_rel_def br_def)
qed



lemma isa_marked_as_used_marked_as_used:
  \<open>(uncurry isa_marked_as_used, uncurry (RETURN oo marked_as_used)) \<in>
    [uncurry marked_as_used_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: marked_as_used_pre_def arena_marked_as_used_conv
      get_clause_LBD_pre_def arena_is_valid_clause_idx_def
      list_rel_imp_same_length isa_marked_as_used_def
      intro!: ASSERT_leI)

sepref_definition isa_marked_as_used_code
  is \<open>uncurry isa_marked_as_used\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply op_eq_uint32[sepref_fr_rules]
  unfolding isa_marked_as_used_def fast_minus_def[symmetric]
  by sepref



lemma isa_marked_as_used_code[sepref_fr_rules]:
  \<open>(uncurry isa_marked_as_used_code, uncurry (RETURN \<circ>\<circ> marked_as_used))
     \<in> [uncurry marked_as_used_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using isa_marked_as_used_code.refine[FCOMP isa_marked_as_used_marked_as_used]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


sepref_definition (in -) isa_arena_incr_act_fast_code
  is \<open>uncurry isa_arena_incr_act\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  supply ACTIVITY_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_arena_incr_act_def
  by sepref

lemma isa_arena_incr_act_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_incr_act_fast_code, uncurry (RETURN \<circ>\<circ> arena_incr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_arena_incr_act_fast_code.refine[FCOMP isa_arena_incr_act_arena_incr_act]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition arena_status_fast_code
  is \<open>uncurry isa_arena_status\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    three_uint32_hnr[sepref_fr_rules] STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_arena_status_def three_uint32_def[symmetric]
  by sepref

lemma isa_arena_status_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry arena_status_fast_code, uncurry (RETURN \<circ>\<circ> arena_status))
  \<in> [uncurry arena_is_valid_clause_vdom]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> status_assn\<close>
  using arena_status_fast_code.refine[FCOMP isa_arena_status_arena_status]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp status_assn_alt_def
  by (simp add: arl_assn_comp)

sepref_definition isa_update_pos_fast_code
  is \<open>uncurry2 isa_update_pos\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  supply minus_uint32_assn[sepref_fr_rules] POS_SHIFT_uint64_hnr[sepref_fr_rules] minus_uint64_assn[sepref_fr_rules]
  unfolding isa_update_pos_def  uint32_nat_assn_minus[sepref_fr_rules] two_uint64_nat_def[symmetric]
  by sepref

lemma isa_update_pos_code_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_pos_fast_code, uncurry2 (RETURN ooo arena_update_pos))
  \<in> [isa_update_pos_pre]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using isa_update_pos_fast_code.refine[FCOMP isa_update_pos]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp isa_update_pos_pre_def)

declare isa_update_pos_fast_code.refine[sepref_fr_rules]
  arena_status_fast_code.refine[sepref_fr_rules]


end
