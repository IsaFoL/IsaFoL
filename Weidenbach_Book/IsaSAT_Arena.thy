theory IsaSAT_Arena
imports Watched_Literals.Watched_Literals_Watch_List_Code_Common
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
  \<^enum> the saved position (is optional in cadical);
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
removed from the addressable clauses (\<^term>\<open>vdom\<close> for virtual domain).

Remark that in our formalisation, we don't (at least not yet) plan to reuse freed spaces
(the predicate about dead clauses must be strengthened in that case). Due to the fact that an arena
is very different from an array of clauses, we refine our data structure by hand to the long list
instead of introducing refinement rules. This is mostly done because iteration is very different
(and it does not change what we had before anyway).

Some technical details: due to the fact that we plan to refine the arena to uint32 and that our
clauses can be tautologies, the size does not fit into uint32 (technically, we have the bound
\<^term>\<open>uint32_max +1\<close>). Therefore, we restrict the clauses to have at least length 2 and we keep
\<^term>\<open>length C - 2\<close> instead of \<^term>\<open>length C\<close>.
\<close>

subsubsection \<open>To Move\<close>

(* TODO Move *)

lemma swap_nth_irrelevant:
  \<open>k \<noteq> i \<Longrightarrow> k \<noteq> j \<Longrightarrow> swap xs i j ! k = xs ! k\<close>
  by (auto simp: swap_def)

lemma swap_nth_relevant:
  \<open>i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> swap xs i j ! i = xs ! j\<close>
  by (auto simp: swap_def)

lemma swap_nth_relevant2:
  \<open>i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> swap xs j i ! i = xs ! j\<close>
  by (auto simp: swap_def)

lemma swap_nth_if:
  \<open>i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> swap xs i j ! k =
    (if k = i then xs ! j else if k = j then xs ! i else xs ! k)\<close>
  by (auto simp: swap_def)

lemma drop_swap_irrelevant:
  \<open>k > i \<Longrightarrow> k > j \<Longrightarrow> drop k (swap outl' j i) = drop k outl'\<close>
  by (subst list_eq_iff_nth_eq) auto

lemma take_swap_relevant:
  \<open>k > i \<Longrightarrow> k > j \<Longrightarrow>  take k (swap outl' j i) = swap (take k outl') i j\<close>
  by (subst list_eq_iff_nth_eq) (auto simp: swap_def)

lemma tl_swap_relevant:
  \<open>i > 0 \<Longrightarrow> j > 0 \<Longrightarrow> tl (swap outl' j i) = swap (tl outl') (i - 1) (j - 1)\<close>
  by (subst list_eq_iff_nth_eq)
    (cases \<open>outl' = []\<close>; cases i; cases j; auto simp: swap_def tl_update_swap nth_tl)

lemma mset_tl:
  \<open>mset (tl xs) = remove1_mset (hd xs) (mset xs)\<close>
  by (cases xs) auto

lemma hd_list_update_If:
  \<open>outl' \<noteq> [] \<Longrightarrow> hd (outl'[i := w]) = (if i = 0 then w else hd outl')\<close>
  by (cases outl') (auto split: nat.splits)

lemma mset_tl_delete_index_and_swap:
  assumes
    \<open>0 < i\<close> and
    \<open>i < length outl'\<close>
  shows \<open>mset (tl (delete_index_and_swap outl' i)) =
         remove1_mset (outl' ! i) (mset (tl outl'))\<close>
  using assms
  by (subst mset_tl)+
    (auto simp: hd_butlast hd_list_update_If mset_butlast_remove1_mset
      mset_update last_list_update_to_last ac_simps)

text \<open>TODO this should go to a different place from the previous lemmas, since it concerns
\<^term>\<open>Misc.slice\<close>, which is not part of \<^theory>\<open>HOL.List\<close> but only part of the Refinement Framework.
\<close>
lemma slice_nth:
  \<open>\<lbrakk>from \<le> length xs; i < to - from\<rbrakk> \<Longrightarrow> Misc.slice from to xs ! i = xs ! (from + i)\<close>
  unfolding slice_def Misc.slice_def
  apply (subst nth_take, assumption)
  apply (subst nth_drop, assumption)
  ..

lemma slice_irrelevant[simp]:
  \<open>i < from \<Longrightarrow> Misc.slice from to (xs[i := C]) = Misc.slice from to xs\<close>
  \<open>i \<ge> to \<Longrightarrow> Misc.slice from to (xs[i := C]) = Misc.slice from to xs\<close>
  \<open>i \<ge> to \<or> i < from \<Longrightarrow> Misc.slice from to (xs[i := C]) = Misc.slice from to xs\<close>
  unfolding Misc.slice_def apply auto
  by (metis drop_take take_update_cancel)+

lemma slice_update_swap[simp]:
  \<open>i < to \<Longrightarrow> i \<ge> from \<Longrightarrow> i < length xs \<Longrightarrow>
     Misc.slice from to (xs[i := C]) = (Misc.slice from to xs)[(i - from) := C]\<close>
  unfolding Misc.slice_def by (auto simp: drop_update_swap)

lemma drop_slice[simp]:
  \<open>drop n (Misc.slice from to xs) = Misc.slice (from + n) to xs\<close> for "from" n to xs
    by (auto simp: Misc.slice_def drop_take ac_simps)

lemma take_slice[simp]:
  \<open>take n (Misc.slice from to xs) = Misc.slice from (min to (from + n)) xs\<close> for "from" n to xs
  using antisym_conv by (fastforce simp: Misc.slice_def drop_take ac_simps min_def)

(* End Move *)


subsubsection \<open>Status of a clause\<close>

(* TODO INIT \<leadsto> IRRED *)
datatype clause_status = INIT | LEARNED | DELETED

instance clause_status :: heap
proof standard
  let ?f = \<open>(\<lambda>x. case x of INIT \<Rightarrow> (0::nat) | LEARNED  \<Rightarrow> 1 | DELETED \<Rightarrow> 2)\<close>
  have \<open>inj ?f\<close>
    by (auto simp: inj_def split: clause_status.splits)
  then show \<open>\<exists>f. inj (f::clause_status \<Rightarrow> nat)\<close>
    by blast
qed

instantiation clause_status :: default
begin
definition default_clause_status where \<open>default_clause_status = DELETED\<close>
instance by standard
end

abbreviation clause_status_assn where
  \<open>clause_status_assn \<equiv> (id_assn :: clause_status \<Rightarrow> _)\<close>

lemma INIT_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return INIT), uncurry0 (RETURN INIT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

lemma LEARNED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return LEARNED), uncurry0 (RETURN LEARNED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

lemma DELETED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return DELETED), uncurry0 (RETURN DELETED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto


subsubsection \<open>Definition\<close>

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

definition is_short_clause where
  \<open>is_short_clause C \<longleftrightarrow> length C \<le> 5\<close>

abbreviation is_long_clause where
  \<open>is_long_clause C \<equiv> \<not>is_short_clause C\<close>

definition header_size :: \<open>nat clause_l \<Rightarrow> nat\<close> where
   \<open>header_size C = (if is_short_clause C then 4 else 5)\<close>

lemmas SHIFTS_def = POS_SHIFT_def STATUS_SHIFT_def ACTIVITY_SHIFT_def LBD_SHIFT_def SIZE_SHIFT_def

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

  \<open>i \<ge>  header_size C \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - LBD_SHIFT\<close>
  \<open>i  \<ge>  header_size C \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - ACTIVITY_SHIFT\<close>
  \<open>i  \<ge>  header_size C \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - STATUS_SHIFT\<close>
  \<open>i  \<ge>  header_size C \<Longrightarrow> i - LBD_SHIFT \<noteq> i - ACTIVITY_SHIFT\<close>
  \<open>i  \<ge>  header_size C \<Longrightarrow> i - LBD_SHIFT \<noteq> i - STATUS_SHIFT\<close>
  \<open>i  \<ge>  header_size C \<Longrightarrow> i - ACTIVITY_SHIFT \<noteq> i - STATUS_SHIFT\<close>

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


datatype arena_el =
  is_Lit: ALit (xarena_lit: \<open>nat literal\<close>) |
  is_LBD: ALBD (xarena_lbd: nat) |
  is_Act: AActivity (xarena_act: nat) |
  is_Size: ASize (xarena_length: nat)  |
  is_Pos: APos (xarena_pos: nat)  |
  is_Status: AStatus (xarena_status: clause_status)

type_synonym arena = \<open>arena_el list\<close>

definition xarena_active_clause :: \<open>arena \<Rightarrow> nat clause_l \<times> bool \<Rightarrow> bool\<close> where
  \<open>xarena_active_clause arena = (\<lambda>(C, red).
     (length C \<ge> 2 \<and>
       header_size C + length C = length arena \<and>
     (is_long_clause C \<longrightarrow>  (is_Pos (arena!(header_size C - POS_SHIFT)) \<and>
       xarena_pos(arena!(header_size C - POS_SHIFT)) \<le> length C - 2))) \<and>
     is_Status(arena!(header_size C - STATUS_SHIFT)) \<and>
        (xarena_status(arena!(header_size C - STATUS_SHIFT)) = INIT \<longleftrightarrow> red) \<and>
        (xarena_status(arena!(header_size C - STATUS_SHIFT)) = LEARNED \<longleftrightarrow> \<not>red) \<and>
     is_LBD(arena!(header_size C - LBD_SHIFT)) \<and>
     is_Act(arena!(header_size C - ACTIVITY_SHIFT)) \<and>
     is_Size(arena!(header_size C - SIZE_SHIFT)) \<and>
     xarena_length(arena!(header_size C - SIZE_SHIFT)) + 2 = length C \<and>
     drop (header_size C) arena = map ALit C
  )\<close>

lemma xarena_active_clause_alt_def:
  \<open>xarena_active_clause arena (the (fmlookup N i)) \<longleftrightarrow> (
     (length (N\<propto>i) \<ge> 2 \<and>
       header_size (N\<propto>i) + length (N\<propto>i) = length arena \<and>
     (is_long_clause (N\<propto>i) \<longrightarrow> (is_Pos (arena!(header_size (N\<propto>i) - POS_SHIFT)) \<and>
       xarena_pos(arena!(header_size (N\<propto>i) - POS_SHIFT)) \<le> length (N\<propto>i) - 2)) \<and>
     is_Status(arena!(header_size (N\<propto>i) - STATUS_SHIFT)) \<and>
        (xarena_status(arena!(header_size (N\<propto>i) - STATUS_SHIFT)) = INIT \<longleftrightarrow> irred N i) \<and>
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
it is true anyway and does not require any extra work to prove.\<close>
definition arena_dead_clause :: \<open>arena \<Rightarrow> bool\<close> where
  \<open>arena_dead_clause arena \<longleftrightarrow>
     is_Status(arena!(4 - STATUS_SHIFT)) \<and> xarena_status(arena!(4 - STATUS_SHIFT)) = DELETED \<and>
     is_LBD(arena!(4 - LBD_SHIFT)) \<and>
     is_Act(arena!(4 - ACTIVITY_SHIFT)) \<and>
     is_Size(arena!(4 - SIZE_SHIFT))
\<close>

definition extra_information_mark_to_delete where
  \<open>extra_information_mark_to_delete arena i = arena[i - STATUS_SHIFT := AStatus DELETED]\<close>

abbreviation clause_slice where
  \<open>clause_slice arena N i \<equiv> Misc.slice (i - header_size (N\<propto>i)) (i + length(N\<propto>i)) arena\<close>

abbreviation dead_clause_slice where
  \<open>dead_clause_slice arena N i \<equiv> Misc.slice (i - 4) i arena\<close>

text \<open>In our first try, the predicated \<^term>\<open>xarena_active_clause\<close> took the whole
arena as parameter. This however turned out to make the proof about updates less modular, since the
slicing already takes care to ignore not relevant changes.
\<close>
definition valid_arena where
  \<open>valid_arena arena N vdom \<longleftrightarrow>
    (\<forall>i \<in># dom_m N. i < length arena \<and> i \<ge> header_size (N\<propto>i) \<and>
         xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))) \<and>
    (\<forall>i \<in> vdom. i \<notin># dom_m N \<longrightarrow> (i < length arena \<and> i \<ge> 4 \<and>
      arena_dead_clause (dead_clause_slice arena N i)))
\<close>

definition arena_status where
  \<open>arena_status arena i = xarena_status (arena!(i - STATUS_SHIFT))\<close>

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

  have Ci: \<open>?Ci = (N \<propto> i, irred N i)\<close> and Cj:  \<open>?Cj = (N \<propto> j, irred N j)\<close>
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
    have Suc4: \<open>4 = Suc (Suc (Suc (Suc 0)))\<close>
      by auto
    have Suc5: \<open>5 = Suc (Suc (Suc (Suc (Suc 0))))\<close>
      by auto
    have [simp]: \<open>j - Suc 0 = i + length (N \<propto> i) - Suc 0 \<longleftrightarrow> j = i + length (N \<propto> i)\<close>
      using False that j_ge i_ge length_Ni
      by auto
    consider
       \<open>is_long_clause (N \<propto> j)\<close> \<open>j - POS_SHIFT = i + length(N\<propto>i) - 1\<close> |
       \<open>j - STATUS_SHIFT = i + length(N\<propto>i) - 1\<close> |
       \<open>j - LBD_SHIFT = i + length(N\<propto>i) - 1\<close> |
       \<open>j - ACTIVITY_SHIFT = i + length(N\<propto>i) - 1\<close> |
       \<open>j - SIZE_SHIFT = i + length(N\<propto>i) - 1\<close>
      using False ji j_ge i_ge length_Ni
      unfolding header_size_def not_less_eq_eq STATUS_SHIFT_def SIZE_SHIFT_def
       LBD_SHIFT_def ACTIVITY_SHIFT_def Suc4 le_Suc_eq POS_SHIFT_def Suc5
      apply (cases \<open>is_short_clause (N \<propto> j)\<close>; cases \<open>is_short_clause (N \<propto> i)\<close>;
        clarsimp_all simp only: if_True if_False add_Suc_right add_0_right
        le_Suc_eq; elim disjE Misc.slice_def)
      apply linarith
      by (solves simp)+
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
    st_init: \<open>(xarena_status (arena ! (i - STATUS_SHIFT)) = INIT) = (irred N i)\<close> and
    st_learned: \<open>(xarena_status (arena ! (i - STATUS_SHIFT)) = LEARNED) = (\<not> irred N i)\<close>
    using 1 i_ge i_le
    unfolding xarena_active_clause_def extra_information_mark_to_delete_def prod.case
      unfolding STATUS_SHIFT_def LBD_SHIFT_def ACTIVITY_SHIFT_def SIZE_SHIFT_def POS_SHIFT_def
     apply  (simp_all add: header_size_def slice_nth split: if_splits)
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


text \<open>At first we had the weaker \<^term>\<open>i - j \<ge> 1\<close> with was able to solve many more goals due
to different handling between \<^term>\<open>1\<close> (which is \<^term>\<open>Suc 0\<close>) and \<^term>\<open>4\<close> (which is not
reduced)...
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
    st_init: \<open>(xarena_status (arena ! (i - STATUS_SHIFT)) = INIT) \<longleftrightarrow> (irred N i)\<close> and
    st_learned: \<open> (xarena_status (arena ! (i - STATUS_SHIFT)) = LEARNED) \<longleftrightarrow> \<not>irred N i\<close>
    using 1 i_ge i_le
    unfolding xarena_active_clause_def extra_information_mark_to_delete_def prod.case
      unfolding STATUS_SHIFT_def LBD_SHIFT_def ACTIVITY_SHIFT_def SIZE_SHIFT_def POS_SHIFT_def
     apply  (simp_all add: header_size_def slice_nth split: if_splits)
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
      (if ia = i then extra_information_mark_to_delete (clause_slice arena  N ia) (header_size (N\<propto>i))
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

lemma valid_arena_extra_information_mark_to_delete:
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close>
  shows \<open>valid_arena (extra_information_mark_to_delete arena i) (fmdrop i N) (insert i vdom)\<close>
proof -
  let ?arena = \<open>extra_information_mark_to_delete arena i\<close>
  have [simp]: \<open>i \<notin># remove1_mset i (dom_m N)\<close>
     \<open>\<And>ia. ia \<notin># remove1_mset i (dom_m N) \<longleftrightarrow> ia =i \<or> (i \<noteq> ia \<and> ia \<notin># dom_m N)\<close>
    using assms distinct_mset_dom[of N] by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
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
    apply (simp_all add: SHIFTS_def header_size_def Misc.slice_def drop_update_swap min_def
      split: if_splits)
      apply force
     apply force
    apply force
    done
  ultimately show ?thesis
    using assms unfolding valid_arena_def
    by auto
qed


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
    using assms distinct_mset_dom[of N] by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
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
     (auto simp: extra_information_mark_to_delete_def STATUS_SHIFT_def drop_update_swap
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
     \<open>\<And>ia. ia \<notin># remove1_mset i (dom_m N) \<longleftrightarrow> ia =i \<or> (i \<noteq> ia \<and> ia \<notin># dom_m N)\<close>
    using assms distinct_mset_dom[of N] by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
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

definition update_pos where
  \<open>update_pos C pos arena = arena[C - POS_SHIFT := APos pos]\<close>


lemma clause_slice_update_pos:
  assumes
    i: \<open>i \<in># dom_m N\<close> and
    ia: \<open>ia \<in># dom_m N\<close> and
    dom: \<open>\<forall>i \<in># dom_m N. i < length arena \<and> i \<ge> header_size (N\<propto>i) \<and>
         xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close> and
    long: \<open>is_long_clause (N \<propto> i)\<close>
  shows
    \<open>clause_slice (update_pos i pos arena) N ia =
      (if ia = i then update_pos (header_size (N\<propto>i)) pos (clause_slice arena N ia)
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
       update_pos_def SHIFTS_def
       Misc.slice_def header_size_def split: if_splits)
qed


lemma clause_slice_update_pos_dead:
  assumes
    i: \<open>i \<in># dom_m N\<close> and
    ia: \<open>ia \<notin># dom_m N\<close> \<open>ia \<in> vdom\<close> and
    dom: \<open>valid_arena arena N vdom\<close> and
    long: \<open>is_long_clause (N \<propto> i)\<close>
  shows
    \<open>arena_dead_clause (dead_clause_slice (update_pos i pos arena) N ia) =
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
      arena_dead_clause_def update_pos_def SHIFTS_def
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
  shows \<open>xarena_active_clause (update_pos (header_size (N\<propto>i)) pos (clause_slice arena N i))
     (the (fmlookup N i))\<close>
  using assms
  by (simp_all add:  update_pos_def SHIFTS_def Misc.slice_def
    header_size_def xarena_active_clause_alt_def)

lemma length_update_pos[simp]:
  \<open>length (update_pos i pos arena) = length arena\<close>
  by (auto simp: update_pos_def)

lemma valid_arena_update_pos:
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close> and
    long: \<open>is_long_clause (N \<propto> i)\<close>and
    pos: \<open>pos \<le> length (N \<propto> i) - 2\<close>
  shows \<open>valid_arena (update_pos i pos arena) N vdom\<close>
proof -
  let ?arena = \<open>update_pos i pos arena\<close>
  have [simp]: \<open>i \<notin># remove1_mset i (dom_m N)\<close>
     \<open>\<And>ia. ia \<notin># remove1_mset i (dom_m N) \<longleftrightarrow> ia =i \<or> (i \<noteq> ia \<and> ia \<notin># dom_m N)\<close>
    using assms distinct_mset_dom[of N] by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
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
         (dead_clause_slice (update_pos i pos arena) N ia)\<close> for ia
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

lemma slice_swap[simp]:
   \<open>l \<ge> from \<Longrightarrow> l < to \<Longrightarrow> k \<ge> from \<Longrightarrow> k < to \<Longrightarrow> from < length arena \<Longrightarrow>
     Misc.slice from to (swap arena l k) = swap (Misc.slice from to arena) (k - from) (l - from)\<close>
  by (cases \<open>k = l\<close>) (auto simp: Misc.slice_def swap_def drop_update_swap list_update_swap)

lemma drop_swap_relevant[simp]:
  \<open>i \<ge> k \<Longrightarrow> j \<ge> k \<Longrightarrow> j < length outl' \<Longrightarrow>drop k (swap outl' j i) = swap (drop k outl') (j - k) (i - k)\<close>
  by (cases \<open>j = i\<close>)
    (auto simp: Misc.slice_def swap_def drop_update_swap list_update_swap)


lemma swap_swap: \<open>k < length xs \<Longrightarrow> l < length xs \<Longrightarrow> swap xs k l = swap xs l k\<close>
  by (cases \<open>k = l\<close>)
    (auto simp: Misc.slice_def swap_def drop_update_swap list_update_swap)

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
   (* drop_update_swap Misc.slice_def swap_def *)
    header_size_def  ac_simps is_short_clause_def split: if_splits)

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
    using assms distinct_mset_dom[of N] by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
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
        xarena_active_clause (clause_slice ?arena N ia) (the (fmlookup (N(i \<hookrightarrow> swap (N \<propto> i) k l)) ia))\<close> for ia
    using dom'[of ia] clause_slice_swap_lits[OF i _ dom, of ia k l] i k l
    xarena_active_clause_swap_lits_same[OF _ _ _ k l, of arena]
    by auto
  moreover have \<open>ia\<in>vdom \<longrightarrow>
        ia \<notin># dom_m N \<longrightarrow>
        4 \<le> ia \<and> arena_dead_clause
         (dead_clause_slice (swap_lits i k l arena) (fmdrop i N) ia)\<close> for ia
    using vdom[of ia] clause_slice_swap_lits_dead[OF i _ _ arena, of ia] i k l
    by auto
  ultimately show ?thesis
    using i k l arena unfolding valid_arena_def
    by auto
qed


paragraph \<open>Learning a clause\<close>

definition append_clause where
  \<open>append_clause b C arena =
    (if is_short_clause C then
      arena @ (if b then AStatus INIT else AStatus LEARNED) # AActivity (0) # ALBD (length C - 2) #
         ASize (length C - 2) # map ALit C
    else arena @ APos 0 # (if b then AStatus INIT else AStatus LEARNED) # AActivity (0)  # ALBD (length C - 2)#
         ASize (length C - 2) # map ALit C)\<close>

lemma slice_append[simp]:
  \<open>to \<le> length xs \<Longrightarrow> Misc.slice from to (xs @ ys) = Misc.slice from to xs\<close>
  by (auto simp: Misc.slice_def)

lemma slice_prepend[simp]:
  \<open>from \<ge> length xs \<Longrightarrow> Misc.slice from to (xs @ ys) = Misc.slice (from - length xs) (to - length xs) ys\<close>
  by (auto simp: Misc.slice_def)

lemma slice_len_min_If:
  \<open>length (Misc.slice from to xs) = (if from < length xs then min (length xs - from) (to - from) else 0)\<close>
  unfolding min_def by (auto simp: Misc.slice_def)

lemma arena_active_clause_append_clause:
  assumes
    \<open>i \<ge> header_size (N \<propto> i)\<close> and
    \<open>i < length arena\<close> and
    \<open>xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>
  shows \<open>xarena_active_clause (clause_slice (append_clause b C arena) N i)
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
  then have \<open>clause_slice (append_clause b C arena) N i = clause_slice arena N i\<close>
    by (auto simp add: append_clause_def)
  then show ?thesis
    using assms by simp
qed

lemma length_append_clause[simp]:
  \<open>length (append_clause b C arena) = length arena + length C + header_size C\<close>
  by (auto simp: append_clause_def header_size_def)

lemma
  slice_start0: \<open>Misc.slice 0 to xs = take to xs\<close>
  unfolding Misc.slice_def
  by auto

lemma arena_active_clause_append_clause_same: \<open>2 \<le> length C \<Longrightarrow>
    xarena_active_clause
     (Misc.slice (length arena) (length arena + header_size C + length C)
       (append_clause b C arena))
     ((the (fmlookup (fmupd (length arena + header_size C) (C, b) N) (length arena + header_size C))))\<close>
  unfolding xarena_active_clause_alt_def append_clause_def
  by (auto simp: header_size_def slice_start0 SHIFTS_def slice_Cons split: if_splits)

lemma clause_slice_append_clause:
  assumes
    ia: \<open>ia \<notin># dom_m N\<close> \<open>ia \<in> vdom\<close> and
    dom: \<open>valid_arena arena N vdom\<close> and
    \<open>arena_dead_clause (dead_clause_slice (arena) N ia)\<close>
  shows
    \<open>arena_dead_clause (dead_clause_slice (append_clause b C arena) N ia)\<close>
proof -
  have ia_ge: \<open>ia \<ge> 4\<close> \<open>ia < length arena\<close>
    using dom ia unfolding valid_arena_def
    by auto
  then have \<open>dead_clause_slice (arena) N ia = dead_clause_slice (append_clause b C arena) N ia\<close>
    by (auto simp add: extra_information_mark_to_delete_def drop_update_swap append_clause_def
      arena_dead_clause_def swap_lits_def SHIFTS_def swap_def ac_simps
       Misc.slice_def header_size_def split: if_splits)
  then show ?thesis
    using assms by simp
qed


lemma valid_arena_append_clause:
  assumes arena: \<open>valid_arena arena N vdom\<close> and le_C: \<open>length C \<ge> 2\<close>
  shows \<open>valid_arena (append_clause b C arena) (fmupd (length arena + header_size C) (C, b) N) vdom\<close>
proof -
  let ?arena = \<open>append_clause b C arena\<close>
  let ?i= \<open>length arena + header_size C\<close>
  let ?N = \<open>(fmupd (length arena + header_size C) (C, b) N)\<close>
  have
    dom: \<open>\<forall>i\<in>#dom_m N.
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close> and
    dom': \<open>\<And>i. i\<in>#dom_m N \<Longrightarrow>
        i < length arena \<and>
        header_size (N \<propto> i) \<le> i \<and>
        xarena_active_clause (clause_slice arena N i) (the (fmlookup N i))\<close>  and
    vdom: \<open>\<And>i. i\<in>vdom \<longrightarrow> i \<notin># dom_m N \<longrightarrow> i \<le> length arena \<and> 4 \<le> i \<and> arena_dead_clause (dead_clause_slice arena N i)\<close>
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
    using dom'[of ia] le_C arena_active_clause_append_clause_same[of C arena b]
    by auto
  moreover have \<open>ia\<in>vdom \<longrightarrow>
        ia \<notin># dom_m N \<longrightarrow> ia < length (append_clause b C arena) \<and>
        4 \<le> ia \<and> arena_dead_clause (Misc.slice (ia - 4) ia (append_clause b C arena))\<close> for ia
    using vdom[of ia] clause_slice_append_clause[of ia N vdom arena b C, OF _ _ arena] le_C
    by auto
  ultimately show ?thesis
    unfolding valid_arena_def
    by auto
qed


subsubsection \<open>Refinement Relation\<close>

definition status_rel:: "(nat \<times> clause_status) set" where
  \<open>status_rel = {(0, INIT), (1, LEARNED), (3, DELETED)}\<close>

definition arena_el_relation where
\<open>arena_el_relation x el  = (case el of
     AStatus n \<Rightarrow> (x, n) \<in> status_rel
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


subsubsection \<open>Preconditions and Assertions for the refinement\<close>

text \<open>The following lemma expresses the relation between the arena and the clauses and especially
  shows the preconditions to be able to generate code.
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
    \<open>i + length (N \<propto> i) \<le> length arena\<close> and
    \<open>is_long_clause (N \<propto> i) \<Longrightarrow> is_Pos (arena ! ( i - POS_SHIFT))\<close> and
    \<open>is_long_clause (N \<propto> i) \<Longrightarrow> arena_pos arena i \<le> length (N \<propto> i)\<close> and
    \<open>is_LBD (arena ! (i - LBD_SHIFT))\<close> and
    \<open>is_Act (arena ! (i - ACTIVITY_SHIFT))\<close> and
    \<open>SIZE_SHIFT \<le> i\<close> and
    \<open>LBD_SHIFT \<le> i\<close>
    \<open>ACTIVITY_SHIFT \<le> i\<close>
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
      INIT) =
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
    \<open>clause_slice arena N i ! (header_size (N \<propto> i) - STATUS_SHIFT) = AStatus (arena_status arena i)\<close>
    using size size' i_le i_ge ge2 lbd status size'
    unfolding header_size_def arena_length_def arena_lbd_def arena_status_def
    by (auto simp: SHIFTS_def slice_nth)
  have HH:
    \<open>arena_length arena i = length (N \<propto> i)\<close> and \<open>is_Size (arena ! (i - SIZE_SHIFT))\<close>
    using size size' i_le i_ge ge2 lbd status size' ge2
    unfolding header_size_def arena_length_def arena_lbd_def arena_status_def
    by (cases \<open>arena ! (i - Suc 0)\<close>;auto simp: SHIFTS_def slice_nth; fail)+
  then show  \<open>length (N \<propto> i) = arena_length arena i\<close> and \<open>is_Size (arena ! (i - SIZE_SHIFT))\<close>
    using i_le i_ge size' size ge2 HH unfolding numeral_2_eq_2
    by (simp_all split:)

  show
    \<open>i \<ge> header_size (N \<propto> i)\<close> and
    \<open>i < length arena\<close>
    using i_le i_ge by auto
  show \<open>is_Lit (arena ! (i+j))\<close> and \<open>N \<propto> i ! j = arena_lit arena (i + j)\<close>
    if \<open>j < length (N \<propto> i)\<close>
    for j
    using arg_cong[OF clause, of \<open>\<lambda>xs. xs ! j\<close>] i_le i_ge that
    by (auto simp: slice_nth arena_lit_def)

  show i_le_arena: \<open>i + length (N \<propto> i) \<le> length arena\<close>
    using arg_cong[OF clause, of length] i_le i_ge
    by (auto simp: arena_lit_def slice_len_min_If)
  show \<open>is_Pos (arena ! ( i - POS_SHIFT))\<close> and \<open>arena_pos arena i \<le> length (N \<propto> i)\<close>
  if \<open>is_long_clause (N \<propto> i)\<close>
    using pos ge2 i_le i_ge that unfolding arena_pos_def
    by (auto simp: SHIFTS_def slice_nth header_size_def)
  show  \<open>is_LBD (arena ! (i - LBD_SHIFT))\<close> and
    \<open>is_Act (arena ! (i - ACTIVITY_SHIFT))\<close>
    using lbd act ge2 i_le i_ge unfolding arena_pos_def
    by (auto simp: SHIFTS_def slice_nth header_size_def)
  show \<open>SIZE_SHIFT \<le> i\<close> and  \<open>LBD_SHIFT \<le> i\<close> and
    \<open>ACTIVITY_SHIFT \<le> i\<close>
    using i_ge unfolding header_size_def SHIFTS_def by (auto split: if_splits)
  show \<open>j < length (N \<propto> i) \<Longrightarrow> i + j < length arena\<close>
    using i_le_arena by linarith
qed

text \<open>This is supposed to be used as for assertions. There might be a more ``local'' way to define
it, without the need for an existentially quantified clause set. However, I did not find a definition
which was really much more useful and more practical.
\<close>
definition arena_is_valid_clause_idx :: \<open>arena \<Rightarrow> nat \<Rightarrow> bool\<close> where
\<open>arena_is_valid_clause_idx arena i \<longleftrightarrow>
  (\<exists>N vdom. valid_arena arena N vdom \<and> i \<in># dom_m N)\<close>


subsubsection \<open>Code Generation\<close>

definition uint64_of_uint32_conv :: \<open>nat \<Rightarrow> nat\<close> where
  [simp]: \<open>uint64_of_uint32_conv x = x\<close>

lemma nat_of_uint32_le_uint32_max: \<open>nat_of_uint32 n \<le> uint32_max\<close>
  using nat_of_uint32_plus[of n 0]
  pos_mod_bound[of \<open>uint32_max + 1\<close> \<open>nat_of_uint32 n\<close>]
  by auto


lemma nat_of_uint32_le_uint64_max: \<open>nat_of_uint32 n \<le> uint64_max\<close>
  using nat_of_uint32_le_uint32_max[of n] unfolding uint64_max_def uint32_max_def
  by auto

lemma nat_of_uint64_uint64_of_uint32: \<open>nat_of_uint64 (uint64_of_uint32 n) = nat_of_uint32 n\<close>
  unfolding uint64_of_uint32_def
  by (auto simp: nat_of_uint64_uint64_of_nat_id nat_of_uint32_le_uint64_max)

lemma uint64_of_uint32_hnr[sepref_fr_rules]:
  \<open>(return o uint64_of_uint32, RETURN o uint64_of_uint32_conv) \<in>
    uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: br_def uint32_nat_rel_def uint64_nat_rel_def
      nat_of_uint32_code nat_of_uint64_uint64_of_uint32)

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

(* TODO Move *)
lemma sum_uint64_assn:
  \<open>(uncurry (return oo (+)), uncurry (RETURN oo (+))) \<in> uint64_assn\<^sup>k *\<^sub>a uint64_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by (sepref_to_hoare) sep_auto
(* End Move *)

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
       br_def list_rel_imp_same_length arena_length_uint64_conv arena_lifting
    intro!: ASSERT_refine_left)

lemma isa_arena_length_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_length_code, uncurry (RETURN \<circ>\<circ> arena_length))
  \<in> [uncurry arena_is_valid_clause_idx]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_arena_length_code.refine[FCOMP isa_arena_length_arena_length]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)

definition nat_of_uint64_conv where
  [simp]: \<open>nat_of_uint64_conv x = x\<close>

lemma nat_of_uint64_conv[sepref_fr_rules]:
  \<open>(return o nat_of_uint64, RETURN o nat_of_uint64_conv) \<in> uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)


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
     using le ba_le  j_ge unfolding length[symmetric] header_size_def
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


definition (in -) arena_is_valid_clause_idx_and_access :: \<open>arena \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
\<open>arena_is_valid_clause_idx_and_access arena i j \<longleftrightarrow>
  (\<exists>N vdom. valid_arena arena N vdom \<and> i \<in># dom_m N \<and> j < length (N \<propto> i))\<close>

definition (in -) arena_lit_pre where
\<open>arena_lit_pre arena i \<longleftrightarrow>
  (\<exists>j. i \<ge> j \<and> arena_is_valid_clause_idx_and_access arena j (i - j))\<close>

lemma isa_arena_lit_arena_lit:
  \<open>(uncurry (isa_arena_lit), uncurry (RETURN oo arena_lit)) \<in>
    [uncurry arena_lit_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>unat_lit_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_lit_def arena_lit_def
  by (intro frefI nres_relI)
    (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
       br_def list_rel_imp_same_length arena_length_uint64_conv arena_lifting
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

end
