theory IsaSAT_Lookup_Conflict
  imports
    IsaSAT_Literals
    IsaSAT_Trail
    Watched_Literals.CDCL_Conflict_Minimisation
    LBD
    IsaSAT_Clauses
    "../lib/Explorer"
begin

no_notation Ref.update ("_ := _" 62)


subsubsection \<open>Clauses Encoded as Positions\<close>

text \<open>We use represent the conflict in two data structures close to the one used by the most SAT
solvers: We keep an array that represent the clause (for efficient iteration on the clause) and a
``hash-table'' to efficiently test if a literal belongs to the clause.

The first data structure is simply an array to represent the clause. This theory is only about
the second data structure. We refine it from the clause (seen as a multiset) in two steps:
  \<^enum> First, we represent the clause as a ``hash-table'', where the \<^term>\<open>i\<close>-th position indicates
    \<^term>\<open>Some True\<close> (respectively \<^term>\<open>Some False\<close>, \<^term>\<open>None\<close>) if \<^term>\<open>Pos i\<close> is present in the
    clause (respectively \<^term>\<open>Neg i\<close>, not at all). This allows to represent every not-tautological
    clause whose literals fits in the underlying array.
  \<^enum> Then we refine it to an array of booleans indicating if the atom is present or not. This
    information is redundant because we already know that a literal can only appear negated
    compared to the trail.

The first step makes it easier to reason about the clause (since we have the full clause), while the
second step should generate (slightly) more efficient code.

Most solvers also merge the underlying array with the array used to cache information for the
conflict minimisation (see theory \<^theory>\<open>Watched_Literals.CDCL_Conflict_Minimisation\<close>,
where we only test if atoms appear in the clause, not literals).

As far as we know, versat stops at the first refinement (stating that there is no significant
overhead, which is probably true, but the second refinement is not much additional work anyhow and
we don't have to rely on the ability of the compiler to not represent the option type on booleans
as a pointer, which it might be able to or not).
\<close>

text \<open>This is the first level of the refinement. We tried a few different definitions (including a
direct one, i.e., mapping a position to the inclusion in the set) but the inductive version turned out
to the easiest one to use.
\<close>
inductive mset_as_position :: \<open>bool option list \<Rightarrow> nat literal multiset \<Rightarrow> bool\<close> where
empty:
  \<open>mset_as_position (replicate n None) {#}\<close> |
add:
  \<open>mset_as_position xs' (add_mset L P)\<close>
  if \<open>mset_as_position xs P\<close> and \<open>atm_of L < length xs\<close> and \<open>L \<notin># P\<close> and \<open>-L \<notin># P\<close> and
     \<open>xs' = xs[atm_of L := Some (is_pos L)]\<close>

lemma mset_as_position_distinct_mset:
  \<open>mset_as_position xs P \<Longrightarrow> distinct_mset P\<close>
  by (induction rule: mset_as_position.induct) auto

lemma mset_as_position_atm_le_length:
  \<open>mset_as_position xs P \<Longrightarrow> L \<in># P \<Longrightarrow> atm_of L < length xs\<close>
  by (induction rule: mset_as_position.induct) (auto simp: nth_list_update' atm_of_eq_atm_of)

lemma mset_as_position_nth:
  \<open>mset_as_position xs P \<Longrightarrow> L \<in># P \<Longrightarrow> xs ! (atm_of L) = Some (is_pos L)\<close>
  by (induction rule: mset_as_position.induct)
    (auto simp: nth_list_update' atm_of_eq_atm_of dest: mset_as_position_atm_le_length)

lemma mset_as_position_in_iff_nth:
  \<open>mset_as_position xs P \<Longrightarrow> atm_of L < length xs \<Longrightarrow> L \<in># P \<longleftrightarrow> xs ! (atm_of L) = Some (is_pos L)\<close>
  by (induction rule: mset_as_position.induct)
    (auto simp: nth_list_update' atm_of_eq_atm_of is_pos_neg_not_is_pos
      dest: mset_as_position_atm_le_length)

lemma mset_as_position_tautology: \<open>mset_as_position xs C \<Longrightarrow> \<not>tautology C\<close>
  by (induction rule: mset_as_position.induct) (auto simp: tautology_add_mset)

lemma mset_as_position_right_unique:
  assumes
    map: \<open>mset_as_position xs D\<close> and
    map': \<open>mset_as_position xs D'\<close>
  shows \<open>D = D'\<close>
proof (rule distinct_set_mset_eq)
  show \<open>distinct_mset D\<close>
    using mset_as_position_distinct_mset[OF map] .
  show \<open>distinct_mset D'\<close>
    using mset_as_position_distinct_mset[OF map'] .
  show \<open>set_mset D = set_mset D'\<close>
    using mset_as_position_in_iff_nth[OF map] mset_as_position_in_iff_nth[OF map']
      mset_as_position_atm_le_length[OF map] mset_as_position_atm_le_length[OF map']
    by blast
qed

lemma mset_as_position_mset_union:
  fixes P xs
  defines \<open>xs' \<equiv> fold (\<lambda>L xs. xs[atm_of L := Some (is_pos L)]) P xs\<close>
  assumes
    mset: \<open>mset_as_position xs P'\<close> and
    atm_P_xs: \<open>\<forall>L \<in> set P. atm_of L < length xs\<close> and
    uL_P: \<open>\<forall>L \<in> set P. -L \<notin># P'\<close> and
    dist: \<open>distinct P\<close> and
    tauto: \<open>\<not>tautology (mset P)\<close>
  shows \<open>mset_as_position xs' (mset P \<union># P')\<close>
  using atm_P_xs uL_P dist tauto unfolding xs'_def
proof (induction P)
  case Nil
  show ?case using mset by auto
next
  case (Cons L P) note IH = this(1) and atm_P_xs = this(2) and uL_P = this(3) and dist = this(4)
    and tauto = this(5)
  then have mset:
    \<open>mset_as_position (fold (\<lambda>L xs. xs[atm_of L := Some (is_pos L)]) P xs) (mset P \<union># P')\<close>
    by (auto simp: tautology_add_mset)
  show ?case
  proof (cases \<open>L \<in># P'\<close>)
    case True
    then show ?thesis
      using mset dist
      by (metis (no_types, lifting) add_mset_union assms(2) distinct.simps(2) fold_simps(2)
       insert_DiffM list_update_id mset.simps(2) mset_as_position_nth set_mset_mset
       sup_union_right1)
  next
    case False
    have [simp]: \<open>length (fold (\<lambda>L xs. xs[atm_of L := Some (is_pos L)]) P xs) = length xs\<close>
      by (induction P arbitrary: xs) auto
    moreover have \<open>- L \<notin> set P\<close>
      using tauto by (metis list.set_intros(1) list.set_intros(2) set_mset_mset tautology_minus)
    moreover have
      \<open>fold (\<lambda>L xs. xs[atm_of L := Some (is_pos L)]) P (xs[atm_of L := Some (is_pos L)]) =
       fold (\<lambda>L xs. xs[atm_of L := Some (is_pos L)]) P xs [atm_of L := Some (is_pos L)]\<close>
       using uL_P dist tauto
      apply (induction P arbitrary: xs)
      subgoal by auto
      subgoal for L' P
        by (cases \<open>atm_of L = atm_of L'\<close>)
          (auto simp: tautology_add_mset list_update_swap atm_of_eq_atm_of)
      done
    ultimately show ?thesis
      using mset atm_P_xs dist uL_P False by (auto intro!: mset_as_position.add)
  qed
qed

lemma mset_as_position_empty_iff: \<open>mset_as_position xs {#} \<longleftrightarrow> (\<exists>n. xs = replicate n None)\<close>
  apply (rule iffI)
  subgoal
    by (cases rule: mset_as_position.cases, assumption) auto
  subgoal
    by (auto intro: mset_as_position.intros)
  done

type_synonym (in -) lookup_clause_rel = \<open>nat \<times> bool option list\<close>

definition lookup_clause_rel :: \<open>nat multiset \<Rightarrow> (lookup_clause_rel \<times> nat literal multiset) set\<close> where
\<open>lookup_clause_rel \<A> = {((n, xs), C). n = size C \<and> mset_as_position xs C \<and>
   (\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length xs)}\<close>

lemma lookup_clause_rel_empty_iff: \<open>((n, xs), C) \<in> lookup_clause_rel \<A> \<Longrightarrow> n = 0 \<longleftrightarrow> C = {#}\<close>
  by (auto simp: lookup_clause_rel_def)

lemma conflict_atm_le_length: \<open>((n, xs), C) \<in> lookup_clause_rel \<A> \<Longrightarrow> L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<Longrightarrow>
   L < length xs\<close>
  by (auto simp: lookup_clause_rel_def)


lemma conflict_le_length:
  assumes
    c_rel: \<open>((n, xs), C) \<in> lookup_clause_rel \<A>\<close> and
    L_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
  shows \<open>atm_of L < length xs\<close>
proof -
  have
    size: \<open>n = size C\<close> and
    mset_pos: \<open>mset_as_position xs C\<close> and
    atms_le: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length xs\<close>
    using c_rel unfolding lookup_clause_rel_def by blast+
  have \<open>atm_of L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    using L_\<L>\<^sub>a\<^sub>l\<^sub>l by (simp add: atms_of_def)
  then show ?thesis
    using atms_le by blast
qed

lemma lookup_clause_rel_atm_in_iff:
  \<open>((n, xs), C) \<in> lookup_clause_rel \<A> \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> L \<in># C \<longleftrightarrow> xs!(atm_of L) = Some (is_pos L)\<close>
  by (rule mset_as_position_in_iff_nth)
     (auto simp: lookup_clause_rel_def atms_of_def)

lemma
  assumes
    c: \<open>((n,xs), C) \<in> lookup_clause_rel \<A>\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
  shows
    lookup_clause_rel_not_tautolgy: \<open>\<not>tautology C\<close> and
    lookup_clause_rel_distinct_mset: \<open>distinct_mset C\<close> and
    lookup_clause_rel_size: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C \<Longrightarrow> size C \<le> 1 + uint_max div 2\<close>
proof -
  have mset: \<open>mset_as_position xs C\<close> and \<open>n = size C\<close> and \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length xs\<close>
    using c unfolding lookup_clause_rel_def by fast+
  show \<open>\<not>tautology C\<close>
    using mset
    apply (induction rule: mset_as_position.induct)
    subgoal by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def)
    subgoal by (auto simp: tautology_add_mset)
    done
  show \<open>distinct_mset C\<close>
    using mset mset_as_position_distinct_mset by blast
  then show \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C \<Longrightarrow> size C \<le> 1 + uint_max div 2\<close>
    using simple_clss_size_upper_div2[of \<A> \<open>C\<close>] \<open>\<not>tautology C\<close> bounded by auto
qed

type_synonym lookup_clause_assn = \<open>uint32 \<times> bool array\<close>

definition option_bool_rel :: \<open>(bool \<times> 'a option) set\<close> where
  \<open>option_bool_rel = {(b, x). b \<longleftrightarrow> \<not>(is_None x)}\<close>

abbreviation option_bool_assn where
  \<open>option_bool_assn \<equiv>  pure option_bool_rel\<close>


definition NOTIN :: \<open>bool option\<close> where
  [simp]: \<open>NOTIN = None\<close>

definition ISIN :: \<open>bool \<Rightarrow> bool option\<close> where
  [simp]: \<open>ISIN b = Some b\<close>

definition is_NOTIN :: \<open>bool option \<Rightarrow> bool\<close> where
  [simp]: \<open>is_NOTIN x \<longleftrightarrow> x = NOTIN\<close>

lemma NOTIN_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return False), uncurry0 (RETURN NOTIN)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a option_bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: NOTIN_def option_bool_rel_def)

lemma POSIN_hnr[sepref_fr_rules]:
  \<open>(return o (\<lambda>_. True), RETURN o ISIN) \<in> bool_assn\<^sup>k \<rightarrow>\<^sub>a option_bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: ISIN_def option_bool_rel_def)

lemma is_NOTIN_hnr[sepref_fr_rules]:
  \<open>(return o Not, RETURN o is_NOTIN) \<in> option_bool_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: is_NOTIN_def option_bool_rel_def split: option.splits)

definition option_lookup_clause_rel where
\<open>option_lookup_clause_rel \<A> = {((b,(n,xs)), C). b = (C = None) \<and>
   (C = None \<longrightarrow> ((n,xs), {#}) \<in> lookup_clause_rel \<A>) \<and>
   (C \<noteq> None \<longrightarrow> ((n,xs), the C) \<in> lookup_clause_rel \<A>)}
   \<close>

lemma option_lookup_clause_rel_lookup_clause_rel_iff:
   \<open>((False, (n, xs)), Some C) \<in> option_lookup_clause_rel \<A> \<longleftrightarrow>
   ((n, xs), C) \<in> lookup_clause_rel \<A>\<close>
   unfolding option_lookup_clause_rel_def by auto


type_synonym (in -) option_lookup_clause_assn = \<open>bool \<times> uint32 \<times> bool array\<close>

abbreviation (in -) lookup_clause_rel_assn
  :: \<open>lookup_clause_rel \<Rightarrow> lookup_clause_assn \<Rightarrow> assn\<close>
where
 \<open>lookup_clause_rel_assn \<equiv> (uint32_nat_assn *a array_assn option_bool_assn)\<close>

type_synonym (in -) conflict_option_rel = \<open>bool \<times> nat \<times> bool option list\<close>

abbreviation (in -)conflict_option_rel_assn
  :: \<open>conflict_option_rel \<Rightarrow> option_lookup_clause_assn \<Rightarrow> assn\<close>
where
 \<open>conflict_option_rel_assn \<equiv> (bool_assn *a lookup_clause_rel_assn)\<close>

abbreviation isasat_conflict_assn where
  \<open>isasat_conflict_assn \<equiv> bool_assn *a uint32_nat_assn *a array_assn option_bool_assn\<close>

definition (in -) lookup_clause_assn_is_None :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>lookup_clause_assn_is_None = (\<lambda>(b, _, _). b)\<close>

lemma lookup_clause_assn_is_None_is_None:
  \<open>(RETURN o lookup_clause_assn_is_None, RETURN o is_None) \<in>
   option_lookup_clause_rel \<A> \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
   (auto simp: option_lookup_clause_rel_def lookup_clause_assn_is_None_def split: option.splits)

lemma lookup_clause_assn_is_None_lookup_clause_assn_is_None:
 \<open>(return o lookup_clause_assn_is_None, RETURN o lookup_clause_assn_is_None) \<in>
  conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: lookup_clause_assn_is_None_def)

definition (in -) lookup_clause_assn_is_empty :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>lookup_clause_assn_is_empty = (\<lambda>(_, n, _). n = 0)\<close>

lemma lookup_clause_assn_is_empty_is_empty:
  \<open>(RETURN o lookup_clause_assn_is_empty, RETURN o (\<lambda>D. Multiset.is_empty(the D))) \<in>
  [\<lambda>D. D \<noteq> None]\<^sub>f option_lookup_clause_rel \<A> \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
   (auto simp: option_lookup_clause_rel_def lookup_clause_assn_is_empty_def lookup_clause_rel_def
     Multiset.is_empty_def split: option.splits)

lemma lookup_clause_assn_is_empty_lookup_clause_assn_is_empty:
 \<open>(return o lookup_clause_assn_is_empty, RETURN o lookup_clause_assn_is_empty) \<in>
  conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: lookup_clause_assn_is_empty_def uint32_nat_rel_def br_def nat_of_uint32_0_iff)


definition size_lookup_conflict :: \<open>_ \<Rightarrow> nat\<close> where
  \<open>size_lookup_conflict = (\<lambda>(_, n, _). n)\<close>

definition size_conflict_wl_heur :: \<open>_ \<Rightarrow> nat\<close> where
  \<open>size_conflict_wl_heur = (\<lambda>(M, N, U, D, _, _, _, _). size_lookup_conflict D)\<close>

lemma size_lookup_conflict[sepref_fr_rules]:
   \<open>(return o (\<lambda>(_, n, _). n), RETURN o size_lookup_conflict) \<in>
   (bool_assn *a lookup_clause_rel_assn)\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding size_lookup_conflict_def
  apply sep_auto
  apply sepref_to_hoare
  subgoal for x xi
    apply (cases x, cases xi)
    apply sep_auto
    done
  done


lemma (in -) mset_as_position_length_not_None:
   \<open>mset_as_position x2 C \<Longrightarrow> size C = length (filter ((\<noteq>) None) x2)\<close>
proof (induction rule: mset_as_position.induct)
  case (empty n)
  then show ?case by auto
next
  case (add xs P L xs') note m_as_p = this(1) and atm_L = this(2)
  have xs_L: \<open>xs ! (atm_of L) = None\<close>
  proof -
    obtain bb :: \<open>bool option \<Rightarrow> bool\<close> where
      f1: \<open>\<forall>z. z = None \<or> z = Some (bb z)\<close>
      by (metis option.exhaust)
    have f2: \<open>xs ! atm_of L \<noteq> Some (is_pos L)\<close>
      using add.hyps(1) add.hyps(2) add.hyps(3) mset_as_position_in_iff_nth by blast
    have f3: \<open>\<forall>z b. ((Some b = z \<or> z = None) \<or> bb z) \<or> b\<close>
      using f1 by blast
    have f4: \<open>\<forall>zs. (zs ! atm_of L \<noteq> Some (is_pos (- L)) \<or> \<not> atm_of L < length zs)
           \<or> \<not> mset_as_position zs P\<close>
      by (metis add.hyps(4) atm_of_uminus mset_as_position_in_iff_nth)
    have \<open>\<forall>z b. ((Some b = z \<or> z = None) \<or> \<not> bb z) \<or> \<not> b\<close>
      using f1 by blast
    then show ?thesis
      using f4 f3 f2 by (metis add.hyps(1) add.hyps(2) is_pos_neg_not_is_pos)
  qed
  obtain xs1 xs2 where
    xs_xs12: \<open>xs = xs1 @ None # xs2\<close> and
    xs1: \<open>length xs1 = atm_of L\<close>
    using atm_L upd_conv_take_nth_drop[of \<open>atm_of L\<close> xs \<open>None\<close>] apply -
    apply (subst(asm)(2) xs_L[symmetric])
    by (force simp del: append_take_drop_id)+
  then show ?case
    using add by (auto simp: list_update_append)
qed

lemma option_bool_assn_is_None[sepref_fr_rules]:
  \<open>(return o Not, RETURN o is_None) \<in> option_bool_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: option_bool_rel_def hr_comp_def)


definition (in -) is_in_lookup_conflict where
  \<open>is_in_lookup_conflict = (\<lambda>(n, xs) L. \<not>is_None (xs ! atm_of L))\<close>

sepref_definition is_in_conflict_code
  is \<open>uncurry (RETURN oo is_in_lookup_conflict)\<close>
  :: \<open>[\<lambda>((n, xs), L). atm_of L < length xs]\<^sub>a
       lookup_clause_rel_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> bool_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    uint32_nat_assn_one[sepref_fr_rules] image_image[simp]
  unfolding is_in_lookup_conflict_def
  by sepref

declare is_in_conflict_code.refine[sepref_fr_rules]

lemma mset_as_position_remove:
  \<open>mset_as_position xs D \<Longrightarrow> L < length xs \<Longrightarrow>
   mset_as_position (xs[L := None]) (remove1_mset (Pos L) (remove1_mset (Neg L) D))\<close>
proof (induction rule: mset_as_position.induct)
  case (empty n)
  then have [simp]: \<open>replicate n None[L := None] = replicate n None\<close>
    using list_update_id[of \<open>replicate n None\<close> L] by auto
  show ?case by (auto intro: mset_as_position.intros)
next
  case (add xs P K xs')
  show ?case
  proof (cases \<open>L = atm_of K\<close>)
    case True
    then show ?thesis
      using add by (cases K) auto
  next
    case False
    have map: \<open>mset_as_position (xs[L := None]) (remove1_mset (Pos L) (remove1_mset (Neg L) P))\<close>
      using add by auto
    have \<open>K \<notin># P - {#Pos L, Neg L#}\<close> \<open>-K \<notin># P - {#Pos L, Neg L#}\<close>
      by (auto simp: add.hyps dest!: in_diffD)
    then show ?thesis
      using mset_as_position.add[OF map, of \<open>K\<close> \<open>xs[L := None, atm_of K := Some (is_pos K)]\<close>]
        add False list_update_swap[of \<open>atm_of K\<close> L xs] apply simp
      apply (subst diff_add_mset_swap)
      by auto
  qed
qed

definition (in -) delete_from_lookup_conflict
   :: \<open>nat literal \<Rightarrow> lookup_clause_rel \<Rightarrow> lookup_clause_rel nres\<close> where
  \<open>delete_from_lookup_conflict = (\<lambda>L (n, xs). do {
     ASSERT(n\<ge>1);
     ASSERT(atm_of L < length xs);
     RETURN (fast_minus n one_uint32_nat, xs[atm_of L := None])
   })\<close>

sepref_definition (in -) delete_from_lookup_conflict_code
  is \<open>uncurry delete_from_lookup_conflict\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d \<rightarrow>\<^sub>a lookup_clause_rel_assn\<close>
  unfolding delete_from_lookup_conflict_def NOTIN_def[symmetric]
  by sepref


lemma delete_from_lookup_conflict_op_mset_delete:
  \<open>(uncurry delete_from_lookup_conflict, uncurry (RETURN oo op_mset_delete)) \<in>
       [\<lambda>(L, D). -L \<notin># D \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> L \<in># D]\<^sub>f Id \<times>\<^sub>f lookup_clause_rel \<A> \<rightarrow> \<langle>lookup_clause_rel \<A>\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using mset_as_position_remove[of \<open>snd (snd x)\<close> \<open>snd y\<close> \<open>atm_of (fst y)\<close>]
    apply (cases x; cases y; cases \<open>fst y\<close>)
    by (auto simp: delete_from_lookup_conflict_def lookup_clause_rel_def
        dest!: multi_member_split
        intro!: ASSERT_refine_left)
  done

definition delete_from_lookup_conflict_pre where
  \<open>delete_from_lookup_conflict_pre \<A> = (\<lambda>(a, b). - a \<notin># b \<and> a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> a \<in># b)\<close>

definition set_conflict_m
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> nat clause option \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
   out_learned \<Rightarrow> (nat clause option \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
\<open>set_conflict_m M N i _ _ _ _ =
    SPEC (\<lambda>(C, n, lbd, outl). C = Some (mset (N\<propto>i)) \<and> n = card_max_lvl M (mset (N\<propto>i)) \<and>
     out_learned M C outl)\<close>

definition merge_conflict_m
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> nat clause option \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
  out_learned \<Rightarrow> (nat clause option \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
\<open>merge_conflict_m M N i D _ _ _ =
    SPEC (\<lambda>(C, n, lbd, outl). C = Some (mset (tl (N\<propto>i)) \<union># the D) \<and>
       n = card_max_lvl M (mset (tl (N\<propto>i)) \<union># the D) \<and>
       out_learned M C outl)\<close>

definition merge_conflict_m_g
  :: \<open>nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> nat clause_l \<Rightarrow> nat clause option \<Rightarrow>
  (nat clause option \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
\<open>merge_conflict_m_g init M Ni D =
    SPEC (\<lambda>(C, n, lbd, outl). C = Some (mset (drop init (Ni)) \<union># the D) \<and>
       n = card_max_lvl M (mset (drop init (Ni))  \<union># the D) \<and>
       out_learned M C outl)\<close>

definition add_to_lookup_conflict :: \<open>nat literal \<Rightarrow> lookup_clause_rel \<Rightarrow> lookup_clause_rel\<close> where
  \<open>add_to_lookup_conflict = (\<lambda>L (n, xs). (if xs ! atm_of L = NOTIN then n + 1 else n,
      xs[atm_of L := ISIN (is_pos L)]))\<close>


definition lookup_conflict_merge'_step
  :: \<open>nat multiset \<Rightarrow> nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> lookup_clause_rel \<Rightarrow> nat clause_l \<Rightarrow>
      nat clause \<Rightarrow> out_learned \<Rightarrow> bool\<close>
where
  \<open>lookup_conflict_merge'_step \<A> init M i clvls zs D C outl = (
      let D' = mset (take (i - init) (drop init D));
          E = remdups_mset (D' + C) in
      ((False, zs), Some E) \<in> option_lookup_clause_rel \<A> \<and>
      out_learned M (Some E) outl \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n \<A> E \<and> clvls = card_max_lvl M E)\<close>

lemma option_lookup_clause_rel_update_None:
  assumes  \<open>((False, (n, xs)), Some D) \<in> option_lookup_clause_rel \<A>\<close> and L_xs : \<open>L < length xs\<close>
  shows \<open>((False, (if xs!L = None then n else n - 1, xs[L := None])),
      Some (D - {# Pos L, Neg L #})) \<in> option_lookup_clause_rel \<A>\<close>
proof -
  have [simp]: \<open>L \<notin># A \<Longrightarrow> A - add_mset L' (add_mset L B) = A - add_mset L' B\<close>
    for A B :: \<open>'a multiset\<close> and L L'
    by (metis add_mset_commute minus_notin_trivial)
  have \<open>n = size D\<close> and map: \<open>mset_as_position xs D\<close>
    using assms by (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def)
  have xs_None_iff: \<open>xs ! L = None \<longleftrightarrow> Pos L \<notin># D \<and> Neg L \<notin># D\<close>
    using map L_xs mset_as_position_in_iff_nth[of xs D \<open>Pos L\<close>]
      mset_as_position_in_iff_nth[of xs D \<open>Neg L\<close>]
    by (cases \<open>xs ! L\<close>) auto

  have 1: \<open>xs ! L = None \<Longrightarrow> D - {#Pos L, Neg L#} = D\<close>
    using assms by (auto simp: xs_None_iff minus_notin_trivial)
  have 2: \<open>xs ! L = None \<Longrightarrow> xs[L := None] = xs\<close>
   using map list_update_id[of xs L] by (auto simp: 1)
  have 3: \<open>xs ! L = Some y \<longleftrightarrow> (y \<and> Pos L \<in># D \<and> Neg L \<notin># D) \<or> (\<not>y \<and> Pos L \<notin># D \<and> Neg L \<in># D)\<close>
    for y
    using map L_xs mset_as_position_in_iff_nth[of xs D \<open>Pos L\<close>]
      mset_as_position_in_iff_nth[of xs D \<open>Neg L\<close>]
    by (cases \<open>xs ! L\<close>) auto

  show ?thesis
    using assms mset_as_position_remove[of xs D L]
    by (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def 1 2 3 size_remove1_mset_If
        minus_notin_trivial mset_as_position_remove)
qed


lemma add_to_lookup_conflict_lookup_clause_rel:
  assumes
    confl: \<open>((n, xs), C) \<in> lookup_clause_rel \<A>\<close> and
    uL_C: \<open>-L \<notin># C\<close> and
    L_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
  shows \<open>(add_to_lookup_conflict L (n, xs), {#L#} \<union># C) \<in> lookup_clause_rel \<A>\<close>
proof -
  have
    n: \<open>n = size C\<close> and
    mset: \<open>mset_as_position xs C\<close> and
    atm: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length xs\<close>
    using confl unfolding lookup_clause_rel_def by blast+
  have \<open>distinct_mset C\<close>
    using mset by (blast dest: mset_as_position_distinct_mset)
  have atm_L_xs: \<open>atm_of L < length xs\<close>
    using atm L_\<L>\<^sub>a\<^sub>l\<^sub>l by (auto simp: atms_of_def)
  then show ?thesis
  proof (cases \<open>L \<in># C\<close>)
    case True
    with mset have xs: \<open>xs ! atm_of L = Some (is_pos L)\<close> \<open>xs ! atm_of L \<noteq> None\<close>
      by (auto dest: mset_as_position_nth)
    moreover have \<open>{#L#} \<union># C = C\<close>
      using True by (simp add: subset_mset.sup.absorb2)
    ultimately show ?thesis
      using n mset atm True
      by (auto simp: lookup_clause_rel_def add_to_lookup_conflict_def xs[symmetric])
  next
    case False
    with mset have \<open>xs ! atm_of L = None\<close>
      using mset_as_position_in_iff_nth[of xs C L]
       mset_as_position_in_iff_nth[of xs C \<open>-L\<close>]  atm_L_xs uL_C
      by (cases L; cases \<open>xs ! atm_of L\<close>) auto
    then show ?thesis
      using n mset atm False atm_L_xs uL_C
      by (auto simp: lookup_clause_rel_def add_to_lookup_conflict_def
          intro!: mset_as_position.intros)
  qed
qed


definition outlearned_add
  :: \<open>(nat,nat)ann_lits \<Rightarrow> nat literal \<Rightarrow> nat \<times> bool option list \<Rightarrow> out_learned \<Rightarrow> out_learned\<close> where
  \<open>outlearned_add = (\<lambda>M L zs outl.
    (if get_level M L < count_decided M \<and> \<not>is_in_lookup_conflict zs L then outl @ [L]
           else outl))\<close>

definition clvls_add
  :: \<open>(nat,nat)ann_lits \<Rightarrow> nat literal \<Rightarrow> nat \<times> bool option list \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>clvls_add = (\<lambda>M L zs clvls.
    (if get_level M L = count_decided M \<and> \<not>is_in_lookup_conflict zs L then clvls + 1
           else clvls))\<close>

definition lookup_conflict_merge
  :: \<open>nat \<Rightarrow> (nat,nat)ann_lits \<Rightarrow> nat clause_l \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
        out_learned \<Rightarrow> (conflict_option_rel \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
  \<open>lookup_conflict_merge init M D  = (\<lambda>(b, xs) clvls lbd outl. do {
     (_, clvls, zs, lbd, outl) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i::nat, clvls :: nat, zs, lbd, outl).
         length (snd zs) = length (snd xs) \<and>
             Suc i \<le> uint_max \<and> Suc (fst zs) \<le> uint_max \<and> Suc clvls \<le> uint_max\<^esup>
       (\<lambda>(i :: nat, clvls, zs, lbd, outl). i < length_u D)
       (\<lambda>(i :: nat, clvls, zs, lbd, outl). do {
           ASSERT(i < length_u D);
           ASSERT(Suc i \<le> uint_max);
           let lbd = lbd_write lbd (get_level M (D!i)) True;
           let outl = outlearned_add M (D!i) zs outl;
           let clvls = clvls_add M (D!i) zs clvls;
           let zs = add_to_lookup_conflict (D!i) zs;
           RETURN(Suc i, clvls, zs, lbd, outl)
        })
       (init, clvls, xs, lbd, outl);
     RETURN ((False, zs), clvls, lbd, outl)
   })\<close>

definition resolve_lookup_conflict_aa
  :: \<open>(nat,nat)ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
     out_learned \<Rightarrow> (conflict_option_rel \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
  \<open>resolve_lookup_conflict_aa M N i xs clvls lbd outl =
     lookup_conflict_merge 1 M (N \<propto> i) xs clvls lbd outl\<close>


definition set_lookup_conflict_aa
  :: \<open>(nat,nat)ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
  out_learned \<Rightarrow>(conflict_option_rel \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
  \<open>set_lookup_conflict_aa M C i xs clvls lbd outl =
     lookup_conflict_merge zero_uint32_nat M (C\<propto>i) xs clvls lbd outl\<close>

definition isa_outlearned_add
  :: \<open>trail_pol \<Rightarrow> nat literal \<Rightarrow> nat \<times> bool option list \<Rightarrow> out_learned \<Rightarrow> out_learned\<close> where
  \<open>isa_outlearned_add = (\<lambda>M L zs outl.
    (if get_level_pol M L < count_decided_pol M \<and> \<not>is_in_lookup_conflict zs L then outl @ [L]
           else outl))\<close>

lemma isa_outlearned_add_outlearned_add:
    \<open>(M', M) \<in> trail_pol \<A> \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow>
      isa_outlearned_add M' L zs outl = outlearned_add M L zs outl\<close>
  by (auto simp: isa_outlearned_add_def outlearned_add_def get_level_get_level_pol
    count_decided_trail_ref[THEN fref_to_Down_unRET_Id])

definition isa_clvls_add
  :: \<open>trail_pol \<Rightarrow> nat literal \<Rightarrow> nat \<times> bool option list \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>isa_clvls_add = (\<lambda>M L zs clvls.
    (if get_level_pol M L = count_decided_pol M \<and> \<not>is_in_lookup_conflict zs L then clvls + 1
           else clvls))\<close>

lemma isa_clvls_add_clvls_add:
    \<open>(M', M) \<in> trail_pol \<A> \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow>
      isa_clvls_add M' L zs outl = clvls_add M L zs outl\<close>
  by (auto simp: isa_clvls_add_def clvls_add_def get_level_get_level_pol
    count_decided_trail_ref[THEN fref_to_Down_unRET_Id])

definition isa_lookup_conflict_merge
  :: \<open>nat \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow> nat \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
        out_learned \<Rightarrow> (conflict_option_rel \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
  \<open>isa_lookup_conflict_merge init M N i  = (\<lambda>(b, xs) clvls lbd outl. do {
     ASSERT( arena_is_valid_clause_idx N i);
     (_, clvls, zs, lbd, outl) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i::nat, clvls :: nat, zs, lbd, outl).
         length (snd zs) = length (snd xs) \<and>
             Suc (fst zs) \<le> uint_max \<and> Suc clvls \<le> uint_max\<^esup>
       (\<lambda>(j :: nat, clvls, zs, lbd, outl). j < i + arena_length N i)
       (\<lambda>(j :: nat, clvls, zs, lbd, outl). do {
           ASSERT(j < length N);
           ASSERT(arena_lit_pre N j);
           ASSERT(get_level_pol_pre (M, arena_lit N j));
	   ASSERT(get_level_pol M (arena_lit N j) \<le> Suc (uint32_max div 2));
           let lbd = lbd_write lbd (get_level_pol M (arena_lit N j)) True;
           ASSERT(atm_of (arena_lit N j) < length (snd zs));
           let outl = isa_outlearned_add M (arena_lit N j) zs outl;
           let clvls = isa_clvls_add M (arena_lit N j) zs clvls;
           let zs = add_to_lookup_conflict (arena_lit N j) zs;
           RETURN(Suc j, clvls, zs, lbd, outl)
        })
       (i+init, clvls, xs, lbd, outl);
     RETURN ((False, zs), clvls, lbd, outl)
   })\<close>


definition isa_set_lookup_conflict where
  \<open>isa_set_lookup_conflict = isa_lookup_conflict_merge 0\<close>

lemma isa_lookup_conflict_merge_lookup_conflict_merge_ext:
  assumes valid: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
    bxs: \<open>((b, xs), C) \<in> option_lookup_clause_rel \<A>\<close> and
    M'M: \<open>(M', M) \<in> trail_pol \<A>\<close> and
    bound: \<open>isasat_input_bounded \<A>\<close>
  shows
    \<open>isa_lookup_conflict_merge init M' arena i (b, xs) clvls lbd outl \<le> \<Down> Id
      (lookup_conflict_merge init M (N \<propto> i) (b, xs) clvls lbd outl)\<close>
proof -
  have [refine0]: \<open>((i + init, clvls, xs, lbd, outl), init, clvls, xs, lbd, outl) \<in>
     {(k, l). k = l + i} \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id\<close>
    by auto
  have \<open>no_dup M\<close>
    using assms by (auto simp: trail_pol_def)
  have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<close>
    using M'M by (auto simp: trail_pol_def literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def)
  from literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[OF bound this \<open>no_dup M\<close>]
  have lev_le: \<open>get_level M L \<le> Suc (uint32_max div 2)\<close> for L .

  show ?thesis
    unfolding isa_lookup_conflict_merge_def lookup_conflict_merge_def prod.case
    apply refine_vcg
    subgoal using assms unfolding arena_is_valid_clause_idx_def by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using valid i by (auto simp: arena_lifting)
    subgoal using valid i by (auto simp: arena_lifting ac_simps)
    subgoal using valid i
      by (auto simp: arena_lifting arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
        intro!: exI[of _ i])
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g
      using i literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<A> N i x1] lits valid M'M
      by (auto simp: arena_lifting ac_simps image_image intro!: get_level_pol_pre)
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g'
      using valid i literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<A> N i x1] lits
      by (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff arena_lifting ac_simps get_level_get_level_pol[OF M'M, symmetric]
        isa_outlearned_add_outlearned_add[OF M'M] isa_clvls_add_clvls_add[OF M'M] lev_le)
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g
      using i literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<A> N i x1] lits valid M'M
      using bxs by (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff arena_lifting ac_simps)
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g'
      using valid i literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<A> N i x1] lits
      by (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff arena_lifting ac_simps get_level_get_level_pol[OF M'M]
        isa_outlearned_add_outlearned_add[OF M'M] isa_clvls_add_clvls_add[OF M'M])
    subgoal using bxs by (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff get_level_get_level_pol[OF M'M])
    done
qed

type_synonym (in -) out_learned_assn = \<open>uint32 array_list\<close>

abbreviation (in -) out_learned_assn :: \<open>out_learned \<Rightarrow> out_learned_assn \<Rightarrow> assn\<close> where
  \<open>out_learned_assn \<equiv> arl_assn unat_lit_assn\<close>

abbreviation (in -) minimize_status_rel where
  \<open>minimize_status_rel \<equiv> Id :: (minimize_status \<times> minimize_status) set\<close>

abbreviation (in -) minimize_status_assn where
  \<open>minimize_status_assn \<equiv> (id_assn :: minimize_status \<Rightarrow> _)\<close>

lemma (in -) SEEN_REMOVABLE[sepref_fr_rules]:
  \<open>(uncurry0 (return SEEN_REMOVABLE),uncurry0 (RETURN SEEN_REMOVABLE)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_assn\<close>
  by (sepref_to_hoare) sep_auto

lemma (in -) SEEN_FAILED[sepref_fr_rules]:
  \<open>(uncurry0 (return SEEN_FAILED),uncurry0 (RETURN SEEN_FAILED)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_assn\<close>
  by (sepref_to_hoare) sep_auto

lemma (in -) SEEN_UNKNOWN[sepref_fr_rules]:
  \<open>(uncurry0 (return SEEN_UNKNOWN),uncurry0 (RETURN SEEN_UNKNOWN)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_assn\<close>
  by (sepref_to_hoare) sep_auto


sepref_definition resolve_lookup_conflict_merge_code
  is \<open>uncurry6 (PR_CONST isa_set_lookup_conflict)\<close>
  :: \<open>[\<lambda>((((((M, N), i), (_, xs)), _), _), out). i < length N]\<^sub>a
      trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    uint32_nat_assn_one[sepref_fr_rules] image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    Suc_uint32_nat_assn_hnr[sepref_fr_rules] fmap_length_rll_u_def[simp]
  unfolding isa_lookup_conflict_merge_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric]
    isa_outlearned_add_def isa_clvls_add_def isa_set_lookup_conflict_def
    isasat_codegen
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    is_NOTIN_def[symmetric]
  apply (rewrite at \<open>_ + \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare resolve_lookup_conflict_merge_code.refine[sepref_fr_rules]

(* TODO Move *)
lemma (in -) arena_is_valid_clause_idx_le_uint64_max:
  \<open>arena_is_valid_clause_idx be bd \<Longrightarrow>
    length be \<le> uint64_max \<Longrightarrow>
   bd + arena_length be bd \<le> uint64_max\<close>
  \<open>arena_is_valid_clause_idx be bd \<Longrightarrow> length be \<le> uint64_max \<Longrightarrow>
   bd \<le> uint64_max\<close>
  using arena_lifting(10)[of be _ _ bd]
  by (fastforce simp: arena_lifting arena_is_valid_clause_idx_def)+

sepref_definition resolve_lookup_conflict_merge_fast_code
  is \<open>uncurry6 (PR_CONST isa_set_lookup_conflict)\<close>
  :: \<open>[\<lambda>((((((M, N), i), (_, xs)), _), _), out). i < length N \<and>
         length N \<le> uint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    uint32_nat_assn_one[sepref_fr_rules] image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    Suc_uint32_nat_assn_hnr[sepref_fr_rules] fmap_length_rll_u_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding isa_lookup_conflict_merge_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric]
    isa_outlearned_add_def isa_clvls_add_def isa_set_lookup_conflict_def
    isasat_codegen isa_set_lookup_conflict_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    is_NOTIN_def[symmetric]
    zero_uint64_nat_def[symmetric]
  apply (rewrite at \<open>RETURN (\<hole>, _ ,_, _)\<close>  Suc_eq_plus1)
  apply (rewrite at \<open>RETURN (_ + \<hole>, _ ,_, _)\<close> one_uint64_nat_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref


declare resolve_lookup_conflict_merge_fast_code.refine[sepref_fr_rules]


definition isa_set_lookup_conflict_aa where
  \<open>isa_set_lookup_conflict_aa = isa_lookup_conflict_merge 0\<close>

definition isa_set_lookup_conflict_aa_pre where
  \<open>isa_set_lookup_conflict_aa_pre =
    (\<lambda>((((((M, N), i), (_, xs)), _), _), out). i < length N)\<close>

sepref_register set_lookup_conflict_aa
sepref_definition set_lookup_conflict_aa_code
  is \<open>uncurry6 isa_set_lookup_conflict_aa\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>\<^sub>a
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    fmap_length_rll_u_def[simp]
  unfolding set_lookup_conflict_aa_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric] length_rll_def[symmetric]
    length_aa_u_def[symmetric] isa_outlearned_add_def isa_clvls_add_def
    isasat_codegen isa_set_lookup_conflict_aa_def isa_lookup_conflict_merge_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    is_NOTIN_def[symmetric] isa_set_lookup_conflict_aa_pre_def
  supply [[goals_limit = 1]]
  apply (rewrite at \<open>_ + \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  by sepref

declare set_lookup_conflict_aa_code.refine[sepref_fr_rules]

sepref_definition set_lookup_conflict_aa_fast_code
  is \<open>uncurry6 isa_set_lookup_conflict_aa\<close>
  :: \<open>[\<lambda>((((((M, N), i), (_, xs)), _), _), _). length N \<le> uint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d  *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    fmap_length_rll_u_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding set_lookup_conflict_aa_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric] length_rll_def[symmetric]
    length_aa_u_def[symmetric] isa_outlearned_add_def isa_clvls_add_def
    isasat_codegen isa_set_lookup_conflict_aa_def isa_lookup_conflict_merge_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    is_NOTIN_def[symmetric] isa_set_lookup_conflict_aa_pre_def zero_uint64_nat_def[symmetric]
  supply [[goals_limit = 1]]
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  apply (rewrite at \<open>RETURN (\<hole>, _ ,_, _)\<close>  Suc_eq_plus1)
  apply (rewrite at \<open>RETURN (_ + \<hole>, _ ,_, _)\<close> one_uint64_nat_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare set_lookup_conflict_aa_fast_code.refine[sepref_fr_rules]


lemma lookup_conflict_merge'_spec:
  assumes
    o: \<open>((b, n, xs), Some C) \<in> option_lookup_clause_rel \<A>\<close> and
    dist: \<open>distinct D\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset D)\<close> and
    tauto: \<open>\<not>tautology (mset D)\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C\<close> and
    \<open>clvls = card_max_lvl M C\<close> and
    CD: \<open>\<And>L. L \<in> set (drop init D) \<Longrightarrow> -L \<notin># C\<close> and
    \<open>Suc init \<le> uint_max\<close> and
    \<open>out_learned M (Some C) outl\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
  shows
    \<open>lookup_conflict_merge init M D (b, n, xs) clvls lbd outl \<le>
      \<Down>(option_lookup_clause_rel \<A> \<times>\<^sub>r Id \<times>\<^sub>r Id)
          (merge_conflict_m_g init M D (Some C))\<close>
     (is \<open>_ \<le>  \<Down> ?Ref ?Spec\<close>)
proof -
  define lbd_upd where
     \<open>lbd_upd lbd i \<equiv> lbd_write lbd (get_level M (D!i)) True\<close> for lbd i
  let ?D = \<open>drop init D\<close>
  have le_D_le_upper[simp]: \<open>a < length D \<Longrightarrow> Suc (Suc a) \<le> uint_max\<close> for a
    using simple_clss_size_upper_div2[of \<A> \<open>mset D\<close>] assms by (auto simp: uint_max_def)
  have Suc_N_uint_max: \<open>Suc n \<le> uint_max\<close> and
     size_C_uint_max: \<open>size C \<le> 1 + uint_max div 2\<close> and
     clvls: \<open>clvls = card_max_lvl M C\<close> and
     tauto_C: \<open>\<not> tautology C\<close> and
     dist_C: \<open>distinct_mset C\<close> and
     atms_le_xs: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length xs\<close> and
     map: \<open>mset_as_position xs C\<close>
    using assms simple_clss_size_upper_div2[of \<A> C] mset_as_position_distinct_mset[of xs C]
      lookup_clause_rel_not_tautolgy[of n xs C] bounded
    unfolding option_lookup_clause_rel_def lookup_clause_rel_def
    by (auto simp: uint_max_def)
  then have clvls_uint_max: \<open>clvls \<le> 1 + uint_max div 2\<close>
    using size_filter_mset_lesseq[of \<open>\<lambda>L. get_level M L = count_decided M\<close> C]
    unfolding uint_max_def card_max_lvl_def by linarith
  have [intro]: \<open>((b, a, ba), Some C) \<in> option_lookup_clause_rel \<A> \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C \<Longrightarrow>
        Suc (Suc a) \<le> uint_max\<close> for b a ba C
    using lookup_clause_rel_size[of a ba C, OF _ bounded] by (auto simp: option_lookup_clause_rel_def
        lookup_clause_rel_def uint_max_def)
  have [simp]: \<open>remdups_mset C = C\<close>
    using o mset_as_position_distinct_mset[of xs C] by (auto simp: option_lookup_clause_rel_def
        lookup_clause_rel_def distinct_mset_remdups_mset_id)
  have \<open>\<not>tautology C\<close>
    using mset_as_position_tautology o by (auto simp: option_lookup_clause_rel_def
        lookup_clause_rel_def)
  have \<open>distinct_mset C\<close>
    using mset_as_position_distinct_mset[of _ C] o
    unfolding option_lookup_clause_rel_def lookup_clause_rel_def by auto
  let ?C' = \<open>\<lambda>a. (mset (take (a - init) (drop init D)) + C)\<close>
  have tauto_C': \<open>\<not> tautology (?C' a)\<close> if \<open>a \<ge> init\<close> for a
    using that tauto tauto_C dist dist_C CD unfolding tautology_decomp'
    by (force dest: in_set_takeD in_diffD dest: in_set_dropD
        simp: distinct_mset_in_diff in_image_uminus_uminus)

  define I where
     \<open>I xs = (\<lambda>(i, clvls, zs :: lookup_clause_rel, lbd :: lbd, outl :: out_learned).
                     length (snd zs) =
                     length (snd xs) \<and>
                     Suc i \<le> uint_max \<and>
                     Suc (fst zs) \<le> uint_max \<and>
                     Suc clvls \<le> uint_max)\<close>
   for xs :: lookup_clause_rel
  define I' where \<open>I' = (\<lambda>(i, clvls, zs, lbd :: lbd, outl).
      lookup_conflict_merge'_step \<A> init M i clvls zs D C outl \<and> i \<ge> init)\<close>

  have dist_D: \<open>distinct_mset (mset D)\<close>
    using dist by auto
  have dist_CD: \<open>distinct_mset (C - mset D - uminus `# mset D)\<close>
    using \<open>distinct_mset C\<close> by auto
  have [simp]: \<open>remdups_mset (mset (drop init D) + C) = mset (drop init D) \<union># C\<close>
    apply (rule distinct_mset_rempdups_union_mset[symmetric])
    using dist_C dist by auto

  have
    if_True_I: \<open>I x2 (Suc a, clvls_add M (D ! a) baa aa,
           add_to_lookup_conflict (D ! a) baa, lbd_upd lbd' a,
           outlearned_add M (D ! a) baa outl)\<close> (is ?I) and
    if_true_I': \<open>I' (Suc a, clvls_add M (D ! a) baa aa,
           add_to_lookup_conflict (D ! a) baa, lbd_upd lbd' a,
           outlearned_add M (D ! a) baa outl)\<close> (is ?I')
    if
      I: \<open>I x2 s\<close> and
      I': \<open>I' s\<close> and
      cond: \<open>case s of (i, clvls, zs, lbd, outl) \<Rightarrow> i < length D\<close> and
      s: \<open>s = (a, ba)\<close> \<open>ba = (aa, baa2)\<close> \<open>baa2 = (baa, lbdL')\<close> \<open>(b, n, xs) = (x1, x2)\<close>
      \<open>lbdL' = (lbd', outl)\<close> and
      a_le_D: \<open>a < length D\<close> and
      a_uint_max: \<open>Suc a \<le> uint_max\<close>
    for x1 x2 s a ba aa baa baa2 lbd' lbdL' outl
  proof -
    have [simp]:
      \<open>s = (a, aa, baa, lbd', outl)\<close>
      \<open>ba = (aa, baa, lbd', outl)\<close>
      \<open>x2 = (n, xs)\<close>
      using s by auto
    obtain ab b where baa[simp]: \<open>baa = (ab, b)\<close> by (cases baa)

    have aa: \<open>aa = card_max_lvl M (remdups_mset (?C' a))\<close> and
      ocr: \<open>((False, ab, b), Some (remdups_mset (?C' a))) \<in> option_lookup_clause_rel \<A>\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (remdups_mset (?C' a))\<close> and
      outl: \<open>out_learned M (Some (remdups_mset (?C' a))) outl\<close>
      using I'
      unfolding I'_def lookup_conflict_merge'_step_def Let_def
      by auto
    have
      ab: \<open>ab = size (remdups_mset (?C' a))\<close> and
      map: \<open>mset_as_position b (remdups_mset (?C' a))\<close> and
      \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length b\<close> and
      cr: \<open>((ab, b), remdups_mset (?C' a)) \<in> lookup_clause_rel \<A>\<close>
      using ocr unfolding option_lookup_clause_rel_def lookup_clause_rel_def
      by auto
    have a_init: \<open>a \<ge> init\<close>
      using I' unfolding I'_def by auto
    have \<open>size (card_max_lvl M (remdups_mset (?C' a))) \<le> size (remdups_mset (?C' a))\<close>
      unfolding card_max_lvl_def
      by auto
    then have [simp]: \<open>Suc (Suc aa) \<le> uint_max\<close> \<open>Suc aa \<le> uint_max\<close>
      using size_C_uint_max lits a_init
      simple_clss_size_upper_div2[of \<A> \<open>remdups_mset (?C' a)\<close>, OF bounded]
      unfolding uint_max_def aa[symmetric]
      by (auto simp: tauto_C')
    have [simp]: \<open>length b = length xs\<close>
      using I unfolding I_def by simp_all

    have ab_upper: \<open>Suc (Suc ab) \<le> uint_max\<close>
      using simple_clss_size_upper_div2[OF bounded, of \<open>remdups_mset (?C' a)\<close>]
      lookup_clause_rel_not_tautolgy[OF cr bounded] a_le_D lits mset_as_position_distinct_mset[OF map]
      unfolding ab literals_are_in_\<L>\<^sub>i\<^sub>n_remdups uint_max_def by auto
    show ?I
      using le_D_le_upper a_le_D ab_upper a_init
      unfolding I_def add_to_lookup_conflict_def baa clvls_add_def by auto

    have take_Suc_a[simp]: \<open>take (Suc a - init) ?D = take (a - init) ?D @ [D ! a]\<close>
      by (smt Suc_diff_le a_init a_le_D append_take_drop_id diff_less_mono drop_take_drop_drop
          length_drop same_append_eq take_Suc_conv_app_nth take_hd_drop)
    have [simp]: \<open>D ! a \<notin> set (take (a - init) ?D)\<close>
      using dist tauto a_le_D apply (subst (asm) append_take_drop_id[symmetric, of _ \<open>Suc a - init\<close>],
          subst append_take_drop_id[symmetric, of _ \<open>Suc a - init\<close>])
      apply (subst (asm) distinct_append, subst nth_append)
      by (auto simp: in_set_distinct_take_drop_iff)
    have [simp]: \<open>- D ! a \<notin> set (take (a - init) ?D)\<close>
    proof
      assume "- D ! a \<in> set (take (a - init) (drop init D))"
      then have "(if is_pos (D ! a) then Neg else Pos) (atm_of (D ! a)) \<in> set D"
        by (metis (no_types) in_set_dropD in_set_takeD uminus_literal_def)
      then show False
        using a_le_D tauto by force
    qed

    have D_a_notin: \<open>D ! a \<notin># (mset (take (a - init) ?D) + uminus `# mset (take (a - init) ?D))\<close>
      by (auto simp: uminus_lit_swap[symmetric])
    have uD_a_notin: \<open>-D ! a \<notin># (mset (take (a - init) ?D) + uminus `# mset (take (a - init) ?D))\<close>
      by (auto simp: uminus_lit_swap[symmetric])

    show ?I'
    proof (cases \<open>(get_level M (D ! a) = count_decided M \<and> \<not> is_in_lookup_conflict baa (D ! a))\<close>)
      case if_cond: True
      have [simp]: \<open>D ! a \<notin># C\<close> \<open>-D ! a \<notin># C\<close> \<open>b ! atm_of (D ! a) = None\<close>
        using if_cond mset_as_position_nth[OF map, of \<open>D ! a\<close>]
          if_cond mset_as_position_nth[OF map, of \<open>-D ! a\<close>] D_a_notin uD_a_notin
        by (auto simp: is_in_lookup_conflict_def split: option.splits bool.splits
            dest: in_diffD)
      have [simp]: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
        using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset D)\<close> a_le_D] atms_le_xs
        by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

      have ocr: \<open>((False, add_to_lookup_conflict (D ! a) (ab, b)), Some (remdups_mset (?C' (Suc a))))
        \<in> option_lookup_clause_rel \<A>\<close>
        using ocr D_a_notin uD_a_notin
        unfolding option_lookup_clause_rel_def lookup_clause_rel_def add_to_lookup_conflict_def
        by (auto dest: in_diffD simp: minus_notin_trivial
            intro!: mset_as_position.intros)
      have \<open>out_learned M (Some (remdups_mset (?C' (Suc a)))) (outlearned_add M (D ! a) (ab, b) outl)\<close>
        using D_a_notin uD_a_notin ocr lits if_cond a_init outl
        unfolding outlearned_add_def out_learned_def
        by auto
      then show ?I'
        using D_a_notin uD_a_notin ocr lits if_cond a_init
        unfolding I'_def lookup_conflict_merge'_step_def Let_def clvls_add_def
        by (auto simp: minus_notin_trivial literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
            card_max_lvl_add_mset aa)
    next
      case if_cond: False
      have atm_D_a_le_xs: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
        using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset D)\<close> a_le_D] atms_le_xs
        by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
      have [simp]: \<open>D ! a \<notin># C - add_mset (- D ! a)
             (add_mset (D ! a)
               (mset (take a D) + uminus `# mset (take a D)))\<close>
        using dist_C in_diffD[of \<open>D ! a\<close> C \<open>add_mset (- D ! a)
               (mset (take a D) + uminus `# mset (take a D))\<close>,
            THEN multi_member_split]
        by (meson distinct_mem_diff_mset member_add_mset)
      have a_init: \<open>a \<ge> init\<close>
        using I' unfolding I'_def by auto
      have take_Suc_a[simp]: \<open>take (Suc a - init) ?D = take (a - init) ?D @ [D ! a]\<close>
        by (smt Suc_diff_le a_init a_le_D append_take_drop_id diff_less_mono drop_take_drop_drop
            length_drop same_append_eq take_Suc_conv_app_nth take_hd_drop)
      have [iff]: \<open>D ! a \<notin> set (take (a - init) ?D)\<close>
        using dist tauto a_le_D
        apply (subst (asm) append_take_drop_id[symmetric, of _ \<open>Suc a - init\<close>],
            subst append_take_drop_id[symmetric, of _ \<open>Suc a - init\<close>])
        apply (subst (asm) distinct_append, subst nth_append)
        by (auto simp: in_set_distinct_take_drop_iff)
      have [simp]: \<open>- D ! a \<notin> set (take (a - init) ?D)\<close>
      proof
        assume "- D ! a \<in> set (take (a - init) (drop init D))"
        then have "(if is_pos (D ! a) then Neg else Pos) (atm_of (D ! a)) \<in> set D"
          by (metis (no_types) in_set_dropD in_set_takeD uminus_literal_def)
        then show False
          using a_le_D tauto by force
      qed
      have \<open>D ! a \<in> set (drop init D)\<close>
        using a_init a_le_D by (meson in_set_drop_conv_nth)
      from CD[OF this] have [simp]: \<open>-D ! a \<notin># C\<close> .
      consider
        (None) \<open>b ! atm_of (D ! a) = None\<close> |
        (Some_in) i where \<open>b ! atm_of (D ! a) = Some i\<close> and
        \<open>(if i then Pos (atm_of (D ! a)) else Neg (atm_of (D ! a))) \<in># C\<close>
        using if_cond mset_as_position_in_iff_nth[OF map, of \<open>D ! a\<close>]
          if_cond mset_as_position_in_iff_nth[OF map, of \<open>-D ! a\<close>] atm_D_a_le_xs(1)
        by  (cases \<open>b ! atm_of (D ! a)\<close>) (auto simp: is_pos_neg_not_is_pos)
      then have ocr: \<open>((False, add_to_lookup_conflict (D ! a) (ab, b)),
       Some (remdups_mset (?C' (Suc a)))) \<in> option_lookup_clause_rel \<A>\<close>
      proof cases
        case [simp]: None
        have [simp]: \<open>D ! a \<notin># C\<close>
          using if_cond mset_as_position_nth[OF map, of \<open>D ! a\<close>]
            if_cond mset_as_position_nth[OF map, of \<open>-D ! a\<close>]
          by (auto simp: is_in_lookup_conflict_def split: option.splits bool.splits
              dest: in_diffD)
        have [simp]: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
          using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset D)\<close> a_le_D] atms_le_xs
          by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

        show ocr: \<open>((False, add_to_lookup_conflict (D ! a) (ab, b)),
          Some (remdups_mset (?C' (Suc a)))) \<in> option_lookup_clause_rel \<A>\<close>
          using ocr
          unfolding option_lookup_clause_rel_def lookup_clause_rel_def add_to_lookup_conflict_def
          by (auto dest: in_diffD simp: minus_notin_trivial
              intro!: mset_as_position.intros)
      next
        case Some_in
        then have \<open>remdups_mset (?C' a) = remdups_mset (?C' (Suc a))\<close>
          using if_cond mset_as_position_in_iff_nth[OF map, of \<open>D ! a\<close>] a_init
            if_cond mset_as_position_in_iff_nth[OF map, of \<open>-D ! a\<close>] atm_D_a_le_xs(1)
          by (auto simp: is_neg_neg_not_is_neg)
        moreover
        have 1: \<open>Some i = Some (is_pos (D ! a))\<close>
          using if_cond mset_as_position_in_iff_nth[OF map, of \<open>D ! a\<close>] a_init Some_in
            if_cond mset_as_position_in_iff_nth[OF map, of \<open>-D ! a\<close>] atm_D_a_le_xs(1)
            \<open>D ! a \<notin> set (take (a - init) ?D)\<close> \<open>-D ! a \<notin># C\<close>
            \<open>- D ! a \<notin> set (take (a - init) ?D)\<close>
          by (cases \<open>D ! a\<close>) (auto simp: is_neg_neg_not_is_neg)
        moreover have \<open>b[atm_of (D ! a) := Some i] = b\<close>
          unfolding 1[symmetric] Some_in(1)[symmetric] by simp
        ultimately show ?thesis
          using dist_C atms_le_xs Some_in(1) map
          unfolding option_lookup_clause_rel_def lookup_clause_rel_def add_to_lookup_conflict_def ab
          by (auto simp: distinct_mset_in_diff minus_notin_trivial
              intro: mset_as_position.intros
              simp del: remdups_mset_singleton_sum)
      qed
      have notin_lo_in_C: \<open>\<not>is_in_lookup_conflict (ab, b) (D ! a) \<Longrightarrow> D ! a \<notin># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos (atm_of (D!a))\<close>]
          mset_as_position_in_iff_nth[OF map, of \<open>Neg (atm_of (D!a))\<close>] atm_D_a_le_xs(1)
          \<open>- D ! a \<notin> set (take (a - init) (drop init D))\<close>
          \<open>D ! a \<notin> set (take (a - init) (drop init D))\<close>
          \<open>-D ! a \<notin># C\<close> a_init
        by (cases \<open>b ! (atm_of (D ! a))\<close>; cases \<open>D ! a\<close>)
          (auto simp: is_in_lookup_conflict_def dist_C distinct_mset_in_diff
            split: option.splits bool.splits
            dest: in_diffD)
      have in_lo_in_C: \<open>is_in_lookup_conflict (ab, b) (D ! a) \<Longrightarrow> D ! a \<in># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos (atm_of (D!a))\<close>]
          mset_as_position_in_iff_nth[OF map, of \<open>Neg (atm_of (D!a))\<close>] atm_D_a_le_xs(1)
          \<open>- D ! a \<notin> set (take (a - init) (drop init D))\<close>
          \<open>D ! a \<notin> set (take (a - init) (drop init D))\<close>
          \<open>-D ! a \<notin># C\<close> a_init
        by (cases \<open>b ! (atm_of (D ! a))\<close>; cases \<open>D ! a\<close>)
          (auto simp: is_in_lookup_conflict_def dist_C distinct_mset_in_diff
            split: option.splits bool.splits
            dest: in_diffD)
      moreover have \<open>out_learned M (Some (remdups_mset (?C' (Suc a))))
         (outlearned_add M (D ! a) (ab, b) outl)\<close>
        using D_a_notin uD_a_notin ocr lits if_cond a_init outl in_lo_in_C notin_lo_in_C
        unfolding outlearned_add_def out_learned_def
        by auto
      ultimately show ?I'
        using ocr lits if_cond atm_D_a_le_xs a_init
        unfolding I'_def lookup_conflict_merge'_step_def Let_def clvls_add_def
        by (auto simp: minus_notin_trivial literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
            card_max_lvl_add_mset aa)
    qed
  qed
  have uL_C_if_L_C: \<open>-L \<notin># C\<close> if \<open>L \<in># C\<close> for L
    using tauto_C that unfolding tautology_decomp' by blast

  show confl: \<open>lookup_conflict_merge init M D (b, n, xs) clvls lbd outl
    \<le> \<Down> ?Ref (merge_conflict_m_g init M D (Some C))\<close>
    unfolding resolve_lookup_conflict_aa_def lookup_conflict_merge_def PR_CONST_def
    distinct_mset_rempdups_union_mset[OF dist_D dist_CD] I_def[symmetric] conc_fun_SPEC
    lbd_upd_def[symmetric] Let_def length_u_def merge_conflict_m_g_def
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(j, _). length D - j)\<close> and
          I' = I'])
    subgoal by auto
    subgoal
      using clvls_uint_max Suc_N_uint_max \<open>Suc init \<le> uint_max\<close>
      unfolding uint_max_def I_def by auto
    subgoal using assms
      unfolding lookup_conflict_merge'_step_def Let_def option_lookup_clause_rel_def I'_def
      by (auto simp add: uint_max_def lookup_conflict_merge'_step_def option_lookup_clause_rel_def)
    subgoal by auto
    subgoal unfolding I_def by fast
    subgoal by (rule if_True_I)
    subgoal by (rule if_true_I')
    subgoal for b' n' s j zs
      using dist lits tauto
      by (auto simp: option_lookup_clause_rel_def take_Suc_conv_app_nth
          literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l)
    subgoal using assms by (auto simp: option_lookup_clause_rel_def lookup_conflict_merge'_step_def
          Let_def I_def I'_def)
    done
qed

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mm_literals_are_in_\<L>\<^sub>i\<^sub>n:
  assumes lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
    i: \<open>i \<in># dom_m N\<close>
  shows \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (N \<propto> i))\<close>
  unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_def
proof (standard)
  fix L
  assume \<open>L \<in># all_lits_of_m (mset (N \<propto> i))\<close>
  then have \<open>atm_of L \<in> atms_of_mm (mset `# ran_mf N)\<close>
    using i unfolding ran_m_def in_all_lits_of_m_ain_atms_of_iff
    by (auto dest!: multi_member_split)
  then show \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
    using lits atm_of_notin_atms_of_iff in_all_lits_of_mm_ain_atms_of_iff
    unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
    by blast
qed

lemma isa_set_lookup_conflict:
  \<open>(uncurry6 isa_set_lookup_conflict_aa, uncurry6 set_conflict_m) \<in>
    [\<lambda>((((((M, N), i), xs), clvls), lbd), outl). i \<in># dom_m N \<and> xs = None \<and> distinct (N \<propto> i) \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N) \<and>
       \<not>tautology (mset (N \<propto> i)) \<and> clvls = 0 \<and>
       out_learned M None outl \<and>
       isasat_input_bounded \<A>]\<^sub>f
    trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f nat_rel \<times>\<^sub>f option_lookup_clause_rel \<A> \<times>\<^sub>f nat_rel \<times>\<^sub>f Id
         \<times>\<^sub>f Id  \<rightarrow>
      \<langle>option_lookup_clause_rel \<A> \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<rangle>nres_rel\<close>
proof -
  have H: \<open>set_lookup_conflict_aa M N i (b, n, xs) clvls lbd outl
    \<le> \<Down> (option_lookup_clause_rel \<A> \<times>\<^sub>r Id)
       (set_conflict_m M N i None clvls lbd outl)\<close>
    if
      i: \<open>i \<in># dom_m N\<close> and
      ocr: \<open>((b, n, xs), None) \<in> option_lookup_clause_rel \<A>\<close> and
     dist: \<open>distinct (N \<propto> i)\<close> and
     lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
     tauto: \<open>\<not>tautology (mset (N \<propto> i))\<close> and
     \<open>clvls = 0\<close> and
     out: \<open>out_learned M None outl\<close> and
     bounded: \<open>isasat_input_bounded \<A>\<close>
    for b n xs N i M clvls lbd outl
  proof -
    have lookup_conflict_merge_normalise:
        \<open>lookup_conflict_merge 0 M C (b, zs) = lookup_conflict_merge 0 M C (False, zs)\<close>
      for M C zs
      unfolding lookup_conflict_merge_def by auto
    have [simp]: \<open>out_learned M (Some {#}) outl\<close>
      using out by (cases outl) (auto simp: out_learned_def)
    have T: \<open>((False, n, xs), Some {#}) \<in> option_lookup_clause_rel \<A>\<close>
      using ocr unfolding option_lookup_clause_rel_def by auto
    have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (N \<propto> i))\<close>
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits i] .
    then show ?thesis unfolding set_lookup_conflict_aa_def set_conflict_m_def
      using lookup_conflict_merge'_spec[of False n xs \<open>{#}\<close> \<A> \<open>N\<propto>i\<close> 0 _ 0 outl lbd] that dist T
      by (auto simp: lookup_conflict_merge_normalise uint_max_def merge_conflict_m_g_def)
  qed

  have H: \<open>isa_set_lookup_conflict_aa M' arena i (b, n, xs) clvls lbd outl
    \<le> \<Down> (option_lookup_clause_rel \<A> \<times>\<^sub>r Id)
       (set_conflict_m M N i None clvls lbd outl)\<close>
    if
      i: \<open>i \<in># dom_m N\<close> and
     ocr: \<open>((b, n, xs), None) \<in> option_lookup_clause_rel \<A>\<close> and
     dist: \<open>distinct (N \<propto> i)\<close> and
     lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
     tauto: \<open>\<not>tautology (mset (N \<propto> i))\<close> and
     \<open>clvls = 0\<close> and
     out: \<open>out_learned M None outl\<close> and
     valid: \<open>valid_arena arena N vdom\<close> and
     M'M: \<open>(M', M) \<in> trail_pol \<A>\<close> and
     bounded: \<open>isasat_input_bounded \<A>\<close>
    for b n xs N i M clvls lbd outl arena vdom M'
    unfolding isa_set_lookup_conflict_aa_def
    apply (rule order.trans)
    apply (rule isa_lookup_conflict_merge_lookup_conflict_merge_ext[OF valid i lits ocr M'M bounded])
    unfolding lookup_conflict_merge_def[symmetric] set_lookup_conflict_aa_def[symmetric]
      zero_uint32_nat_def[symmetric]
    by (auto intro: H[OF that(1-7,10)])
  show ?thesis
    unfolding lookup_conflict_merge_def uncurry_def
    by (intro nres_relI frefI) (auto intro!: H)
qed

definition isa_resolve_merge_conflict where
  \<open>isa_resolve_merge_conflict = isa_lookup_conflict_merge 1\<close>

sepref_register isa_resolve_merge_conflict
sepref_definition resolve_merge_conflict_code
  is \<open>uncurry6 isa_resolve_merge_conflict\<close>
  :: \<open>[isa_set_lookup_conflict_aa_pre]\<^sub>a
      trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    fmap_length_rll_u_def[simp]
  unfolding set_lookup_conflict_aa_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric] length_rll_def[symmetric]
    length_aa_u_def[symmetric] isa_outlearned_add_def isa_clvls_add_def
    isasat_codegen isa_set_lookup_conflict_aa_def isa_lookup_conflict_merge_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    is_NOTIN_def[symmetric] isa_set_lookup_conflict_aa_pre_def
    isa_resolve_merge_conflict_def
  apply (rewrite at \<open>_ + \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare resolve_merge_conflict_code.refine[sepref_fr_rules]

sepref_definition resolve_merge_conflict_fast_code
  is \<open>uncurry6 isa_resolve_merge_conflict\<close>
  :: \<open>[uncurry6 (\<lambda>M N i (b, xs) clvls lbd outl. length N \<le> uint64_max \<and>
         isa_set_lookup_conflict_aa_pre ((((((M, N), i), (b, xs)), clvls), lbd), outl))]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    fmap_length_rll_u_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding set_lookup_conflict_aa_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric] length_rll_def[symmetric]
    length_aa_u_def[symmetric] isa_outlearned_add_def isa_clvls_add_def
    isasat_codegen isa_set_lookup_conflict_aa_def isa_lookup_conflict_merge_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric] nat_of_uint64_conv_def
    is_NOTIN_def[symmetric] isa_set_lookup_conflict_aa_pre_def
    isa_resolve_merge_conflict_def
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint64_nat_def[symmetric])
  apply (rewrite in \<open>RETURN (Suc _, _)\<close> Suc_eq_plus1)
  apply (rewrite in \<open>_ + 1\<close> one_uint64_nat_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare resolve_merge_conflict_fast_code.refine[sepref_fr_rules]

definition merge_conflict_m_pre where
  \<open>merge_conflict_m_pre \<A> =
  (\<lambda>((((((M, N), i), xs), clvls), lbd), out). i \<in># dom_m N \<and> xs \<noteq> None \<and> distinct (N \<propto> i) \<and>
       \<not>tautology (mset (N \<propto> i)) \<and>
       (\<forall>L \<in> set (tl (N \<propto> i)). - L \<notin># the xs) \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (the xs) \<and> clvls = card_max_lvl M (the xs) \<and>
       out_learned M xs out \<and> no_dup M \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N) \<and>
       isasat_input_bounded \<A>)\<close>

lemma isa_resolve_merge_conflict:
  \<open>(uncurry6 isa_resolve_merge_conflict, uncurry6 merge_conflict_m) \<in>
    [merge_conflict_m_pre \<A>]\<^sub>f
    trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f nat_rel \<times>\<^sub>f option_lookup_clause_rel \<A>
        \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<times>\<^sub>f Id  \<rightarrow>
      \<langle>option_lookup_clause_rel \<A> \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<rangle>nres_rel\<close>
proof -
  have H1: \<open>resolve_lookup_conflict_aa M N i (b, n, xs) clvls lbd outl
    \<le> \<Down> (option_lookup_clause_rel \<A> \<times>\<^sub>r Id)
       (merge_conflict_m M N i C clvls lbd outl)\<close>
    if
      i: \<open>i \<in># dom_m N\<close> and
      ocr: \<open>((b, n, xs), C) \<in> option_lookup_clause_rel \<A>\<close> and
     dist: \<open>distinct (N \<propto> i)\<close> and
     lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
     lits': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (the C)\<close> and
     tauto: \<open>\<not>tautology (mset (N \<propto> i))\<close> and
     out: \<open>out_learned M C outl\<close> and
     not_neg: \<open>\<And>L. L \<in> set (tl (N \<propto> i)) \<Longrightarrow> - L \<notin># the C\<close> and
     \<open>clvls = card_max_lvl M (the C)\<close> and
     C_None: \<open>C \<noteq> None\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
    for b n xs N i M clvls lbd outl C
  proof -
    have lookup_conflict_merge_normalise:
        \<open>lookup_conflict_merge 1 M C (b, zs) = lookup_conflict_merge 1 M C (False, zs)\<close>
      for M C zs
      unfolding lookup_conflict_merge_def by auto
    have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (N \<propto> i))\<close>
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits i] .
    then show ?thesis unfolding resolve_lookup_conflict_aa_def merge_conflict_m_def
      using lookup_conflict_merge'_spec[of b n xs \<open>the C\<close> \<A> \<open>N\<propto>i\<close> clvls M 1 outl lbd] that dist
         not_neg ocr C_None lits'
      by (auto simp: lookup_conflict_merge_normalise uint_max_def merge_conflict_m_g_def
         drop_Suc)
  qed

  have H2: \<open>isa_resolve_merge_conflict M' arena i (b, n, xs) clvls lbd outl
    \<le> \<Down> (Id \<times>\<^sub>r Id)
       (resolve_lookup_conflict_aa M N i (b, n, xs) clvls lbd outl)\<close>
    if
      i: \<open>i \<in># dom_m N\<close> and
      ocr: \<open>((b, n, xs), C) \<in> option_lookup_clause_rel \<A>\<close> and
      dist: \<open>distinct (N \<propto> i)\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
      lits': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (the C)\<close> and
      tauto: \<open>\<not>tautology (mset (N \<propto> i))\<close> and
      out: \<open>out_learned M C outl\<close> and
      not_neg: \<open>\<And>L. L \<in> set (tl (N \<propto> i)) \<Longrightarrow> - L \<notin># the C\<close> and
      \<open>clvls = card_max_lvl M (the C)\<close> and
      C_None: \<open>C \<noteq> None\<close> and
      valid: \<open>valid_arena arena N vdom\<close> and

       i: \<open>i \<in># dom_m N\<close> and
      dist: \<open>distinct (N \<propto> i)\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
      tauto: \<open>\<not>tautology (mset (N \<propto> i))\<close> and
      \<open>clvls = card_max_lvl M (the C)\<close> and
      out: \<open>out_learned M C outl\<close> and
      bounded: \<open>isasat_input_bounded \<A>\<close> and
      M'M: \<open>(M', M) \<in> trail_pol \<A>\<close>
    for b n xs N i M clvls lbd outl arena vdom C M'
    unfolding isa_resolve_merge_conflict_def
    apply (rule order.trans)
    apply (rule isa_lookup_conflict_merge_lookup_conflict_merge_ext[OF valid i lits ocr M'M])
    unfolding resolve_lookup_conflict_aa_def[symmetric] set_lookup_conflict_aa_def[symmetric]
    using bounded by (auto intro: H1[OF that(1-6)])
  show ?thesis
    unfolding lookup_conflict_merge_def uncurry_def
    apply (intro nres_relI frefI)
    apply clarify
    subgoal
      unfolding merge_conflict_m_pre_def
      apply (rule order_trans)
      apply (rule H2; auto; auto; fail)
      by (auto intro!: H1 simp: merge_conflict_m_pre_def)
    done
qed

definition (in -) is_in_conflict :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> bool\<close> where
  [simp]: \<open>is_in_conflict L C \<longleftrightarrow> L \<in># the C\<close>

definition (in -) is_in_lookup_option_conflict
  :: \<open>nat literal \<Rightarrow> (bool \<times> nat \<times> bool option list) \<Rightarrow> bool\<close>
where
  \<open>is_in_lookup_option_conflict = (\<lambda>L (_, _, xs). xs ! atm_of L = Some (is_pos L))\<close>

lemma is_in_lookup_option_conflict_is_in_conflict:
  \<open>(uncurry (RETURN oo is_in_lookup_option_conflict),
     uncurry (RETURN oo is_in_conflict)) \<in>
     [\<lambda>(L, C). C \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f Id \<times>\<^sub>r option_lookup_clause_rel \<A>  \<rightarrow>
     \<langle>Id\<rangle>nres_rel\<close>
  apply (intro nres_relI frefI)
  subgoal for Lxs LC
    using lookup_clause_rel_atm_in_iff[of _ \<open>snd (snd (snd Lxs))\<close>]
    apply (cases Lxs)
    by (auto simp: is_in_lookup_option_conflict_def option_lookup_clause_rel_def)
  done

definition conflict_from_lookup where
  \<open>conflict_from_lookup = (\<lambda>(n, xs). SPEC(\<lambda>D. mset_as_position xs D \<and> n = size D))\<close>

lemma Ex_mset_as_position:
  \<open>Ex (mset_as_position xs)\<close>
proof (induction \<open>size {#x \<in># mset xs. x \<noteq> None#}\<close> arbitrary: xs)
  case 0
  then have xs: \<open>xs = replicate (length xs) None\<close>
    by (auto simp: filter_mset_empty_conv dest: replicate_length_same)
  show ?case
    by (subst xs) (auto simp: mset_as_position.empty intro!: exI[of _ \<open>{#}\<close>])
next
  case (Suc x) note IH = this(1) and xs = this(2)
  obtain i where
     [simp]: \<open>i < length xs\<close> and
    xs_i: \<open>xs ! i \<noteq> None\<close>
    using xs[symmetric]
    by (auto dest!: size_eq_Suc_imp_elem simp: in_set_conv_nth)
  let ?xs = \<open>xs [i := None]\<close>
  have \<open>x = size {#x \<in># mset ?xs. x \<noteq> None#}\<close>
    using xs[symmetric] xs_i by (auto simp: mset_update size_remove1_mset_If)
  from IH[OF this] obtain D where
     map: \<open>mset_as_position ?xs D\<close>
    by blast
  have [simp]: \<open>Pos i \<notin># D\<close> \<open>Neg i \<notin># D\<close>
    using xs_i mset_as_position_nth[OF map, of \<open>Pos i\<close>]
      mset_as_position_nth[OF map, of \<open>Neg i\<close>]
    by auto
  have [simp]: \<open>xs ! i = a \<Longrightarrow> xs[i := a] = xs\<close> for a
    by auto

  have \<open>mset_as_position xs (add_mset (if the (xs ! i) then Pos i else Neg i) D)\<close>
    using mset_as_position.add[OF map, of \<open>if the (xs ! i) then Pos i else Neg i\<close> xs]
      xs_i[symmetric]
    by (cases \<open>xs ! i\<close>) auto
  then show ?case by blast
qed

lemma id_conflict_from_lookup:
  \<open>(RETURN o id, conflict_from_lookup) \<in> [\<lambda>(n, xs). \<exists>D. ((n, xs), D) \<in> lookup_clause_rel \<A>]\<^sub>f Id \<rightarrow>
    \<langle>lookup_clause_rel \<A>\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: lookup_clause_rel_def conflict_from_lookup_def RETURN_RES_refine_iff)


lemma lookup_clause_rel_exists_le_uint_max:
  assumes ocr: \<open>((n, xs), D) \<in> lookup_clause_rel \<A>\<close> and \<open>n > 0\<close> and
    le_i: \<open>\<forall>k<i. xs ! k = None\<close> and lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> D\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
  shows
    \<open>\<exists>j. j \<ge> i \<and> j < length xs \<and> j < uint_max \<and> xs ! j \<noteq> None\<close>
proof -
  have
    n_D: \<open>n = size D\<close> and
    map: \<open>mset_as_position xs D\<close> and
    le_xs: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length xs\<close>
    using ocr unfolding lookup_clause_rel_def by auto
  have map_empty: \<open>mset_as_position xs {#} \<longleftrightarrow> (xs = [] \<or> set xs = {None})\<close>
    by (subst mset_as_position.simps) (auto simp add: list_eq_replicate_iff)
  have ex_not_none: \<open>\<exists>j. j \<ge> i \<and> j < length xs \<and> xs ! j \<noteq> None\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have \<open>xs = [] \<or> set xs = {None}\<close>
      using le_i by (fastforce simp: in_set_conv_nth)
    then have \<open>mset_as_position xs {#}\<close>
      using map_empty by auto
    then show False
      using mset_as_position_right_unique[OF map] \<open>n > 0\<close> n_D by (cases D) auto
  qed
  then obtain j where
     j: \<open>j \<ge> i\<close>\<open>j < length xs\<close>\<open>xs ! j \<noteq> None\<close>
    by blast
  let ?L = \<open>if the (xs ! j) then Pos j else Neg j\<close>
  have \<open>?L \<in># D\<close>
    using j mset_as_position_in_iff_nth[OF map, of ?L] by auto
  then have \<open>nat_of_lit ?L \<le> uint_max\<close>
    using lits bounded
    by (auto 5 5 dest!: multi_member_split[of _ D]
        simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset split: if_splits)
  then have \<open>j < uint_max\<close>
    by (auto simp: uint_max_def split: if_splits)
  then show ?thesis
    using j by blast
qed


text \<open>During the conflict analysis, the literal of highest level is at the beginning. During the
rest of the time the conflict is \<^term>\<open>None\<close>.
\<close>
definition highest_lit where
  \<open>highest_lit M C L \<longleftrightarrow>
     (L = None \<longrightarrow> C = {#}) \<and>
     (L \<noteq> None \<longrightarrow> get_level M (fst (the L)) = snd (the L) \<and>
        snd (the L) = get_maximum_level M C \<and>
        fst (the L) \<in># C
        )\<close>


paragraph \<open>Conflict Minimisation\<close>

definition iterate_over_conflict_inv where
  \<open>iterate_over_conflict_inv M D\<^sub>0' = (\<lambda>(D, D'). D \<subseteq># D\<^sub>0' \<and> D' \<subseteq># D)\<close>

definition is_literal_redundant_spec where
   \<open>is_literal_redundant_spec K NU UNE D L = SPEC(\<lambda>b. b \<longrightarrow>
      NU + UNE \<Turnstile>pm remove1_mset L (add_mset K D))\<close>

definition iterate_over_conflict
  :: \<open>'v literal \<Rightarrow> ('v, 'mark) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow>  'v clause \<Rightarrow>
       'v clause nres\<close>
where
  \<open>iterate_over_conflict K M NU UNE D\<^sub>0' = do {
    (D, _) \<leftarrow>
       WHILE\<^sub>T\<^bsup>iterate_over_conflict_inv M D\<^sub>0'\<^esup>
       (\<lambda>(D, D'). D' \<noteq> {#})
       (\<lambda>(D, D'). do{
          x \<leftarrow> SPEC (\<lambda>x. x \<in># D');
          red \<leftarrow> is_literal_redundant_spec K NU UNE D x;
          if \<not>red
          then RETURN (D, remove1_mset x D')
          else RETURN (remove1_mset x D, remove1_mset x D')
        })
       (D\<^sub>0', D\<^sub>0');
     RETURN D
}\<close>


definition minimize_and_extract_highest_lookup_conflict_inv where
  \<open>minimize_and_extract_highest_lookup_conflict_inv = (\<lambda>(D, i, s, outl).
    length outl \<le> uint_max \<and> mset (tl outl) = D \<and> outl \<noteq> [] \<and> i \<ge> 1)\<close>

type_synonym 'v conflict_highest_conflict = \<open>('v literal \<times> nat) option\<close>

definition (in -) atm_in_conflict where
  \<open>atm_in_conflict L D \<longleftrightarrow> L \<in> atms_of D\<close>

definition atm_in_conflict_lookup :: \<open>nat \<Rightarrow> lookup_clause_rel \<Rightarrow> bool\<close> where
  \<open>atm_in_conflict_lookup = (\<lambda>L (_, xs). xs ! L \<noteq> None)\<close>

definition atm_in_conflict_lookup_pre  :: \<open>nat \<Rightarrow> lookup_clause_rel \<Rightarrow> bool\<close> where
\<open>atm_in_conflict_lookup_pre L xs \<longleftrightarrow> L < length (snd xs)\<close>

sepref_definition (in -) atm_in_conflict_code
  is \<open>uncurry (RETURN oo atm_in_conflict_lookup)\<close>
  :: \<open>[uncurry atm_in_conflict_lookup_pre]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding atm_in_conflict_lookup_def atm_in_conflict_lookup_pre_def
  by sepref

declare atm_in_conflict_code.refine[sepref_fr_rules]

lemma atm_in_conflict_lookup_atm_in_conflict:
  \<open>(uncurry (RETURN oo atm_in_conflict_lookup), uncurry (RETURN oo atm_in_conflict)) \<in>
     [\<lambda>(L, xs). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)]\<^sub>f Id \<times>\<^sub>f lookup_clause_rel \<A> \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using mset_as_position_in_iff_nth[of \<open>snd (snd x)\<close> \<open>snd y\<close> \<open>Pos (fst x)\<close>]
      mset_as_position_in_iff_nth[of \<open>snd (snd x)\<close> \<open>snd y\<close> \<open>Neg (fst x)\<close>]
    by (cases x; cases y)
      (auto simp: atm_in_conflict_lookup_def atm_in_conflict_def
        lookup_clause_rel_def atm_iff_pos_or_neg_lit
        pos_lit_in_atms_of neg_lit_in_atms_of)
  done

lemma atm_in_conflict_lookup_pre:
  fixes x1 :: \<open>nat\<close> and x2 :: \<open>nat\<close>
  assumes
    \<open>x1n \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and
    \<open>(x2f, x2a) \<in> lookup_clause_rel \<A>\<close>
  shows \<open>atm_in_conflict_lookup_pre (atm_of x1n) x2f\<close>
proof -
  show ?thesis
    using assms
    by (auto simp: lookup_clause_rel_def atm_in_conflict_lookup_pre_def atms_of_def)
qed

definition is_literal_redundant_lookup_spec where
   \<open>is_literal_redundant_lookup_spec \<A> M NU NUE D' L s =
    SPEC(\<lambda>(s', b). b \<longrightarrow> (\<forall>D. (D', D) \<in> lookup_clause_rel \<A> \<longrightarrow>
       (mset `# mset (tl NU)) + NUE \<Turnstile>pm remove1_mset L D))\<close>

type_synonym (in -) conflict_min_cach_l = \<open>minimize_status list \<times> nat list\<close>

definition (in -) conflict_min_cach_set_removable_l
  :: \<open>conflict_min_cach_l \<Rightarrow> nat \<Rightarrow> conflict_min_cach_l nres\<close>
where
  \<open>conflict_min_cach_set_removable_l = (\<lambda>(cach, sup) L. do {
     ASSERT(L < length cach);
     RETURN (cach[L := SEEN_REMOVABLE], sup @ [L])
   })\<close>

definition (in -) conflict_min_cach :: \<open>nat conflict_min_cach \<Rightarrow> nat \<Rightarrow> minimize_status\<close> where
  [simp]: \<open>conflict_min_cach cach L = cach L\<close>

definition lit_redundant_rec_wl_lookup
  :: \<open>nat multiset \<Rightarrow> (nat,nat)ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat clause \<Rightarrow>
     _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (_ \<times> _ \<times> bool) nres\<close>
where
  \<open>lit_redundant_rec_wl_lookup \<A> M NU D cach analysis lbd =
      WHILE\<^sub>T\<^bsup>lit_redundant_rec_wl_inv M NU D\<^esup>
        (\<lambda>(cach, analyse, b). analyse \<noteq> [])
        (\<lambda>(cach, (analyse :: (nat \<times> nat \<times> nat \<times> nat) list), b). do {
            ASSERT((analyse :: (nat \<times> nat \<times> nat \<times> nat) list) \<noteq> []);
	    let (C,k, i, len) = last analyse;
            ASSERT(C \<in># dom_m NU);
            ASSERT(length (NU \<propto> C) > 0); \<comment> \<open> >= 2 would work too \<close>
            ASSERT (NU \<propto> C ! k \<in> lits_of_l M);
            ASSERT(NU \<propto> C ! k \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>);
            let C = NU \<propto> C;
            if i \<ge> len
            then
               RETURN(cach (atm_of (C ! k) := SEEN_REMOVABLE), butlast analyse, True)
            else do {
               let (L, analyse) = get_literal_and_remove_of_analyse_wl C analyse;
               ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>);
               let b = \<not>level_in_lbd (get_level M L) lbd;
               if (get_level M L = zero_uint32_nat \<or>
                   conflict_min_cach cach (atm_of L) = SEEN_REMOVABLE \<or>
                   atm_in_conflict (atm_of L) D)
               then RETURN (cach, (analyse :: (nat \<times> nat \<times> nat \<times> nat) list), False)
               else if b \<or> conflict_min_cach cach (atm_of L) = SEEN_FAILED
               then do {
                  ASSERT(mark_failed_lits_stack_inv NU analyse cach);
                  cach \<leftarrow> mark_failed_lits_wl NU analyse cach;
                  RETURN (cach, [], False)
               }
               else do {
	          ASSERT(- L \<in> lits_of_l M);
                  C \<leftarrow> get_propagation_reason M (-L);
                  case C of
                    Some C \<Rightarrow> RETURN (cach, analyse @ [lit_redundant_reason_stack (-L) NU C], False)
                  | None \<Rightarrow> do {
                      ASSERT(mark_failed_lits_stack_inv NU analyse cach);
                      cach \<leftarrow> mark_failed_lits_wl NU analyse cach;
                      RETURN (cach, [], False)
                  }
              }
          }
        })
       (cach, analysis, False)\<close>

lemma lit_redundant_rec_wl_lookup_mark_failed_lits_stack_inv:
  assumes
    \<open>(x, x') \<in> Id\<close> and
    \<open>case x of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
    \<open>lit_redundant_rec_wl_inv M NU D x'\<close> and
    \<open>\<not> snd (snd (snd (last x1a))) \<le> fst (snd (snd (last x1a)))\<close> and
    \<open>get_literal_and_remove_of_analyse_wl (NU \<propto> fst (last x1c)) x1c = (x1e, x2e)\<close> and
    \<open>x2 = (x1a, x2a)\<close> and
    \<open>x' = (x1, x2)\<close> and
    \<open>x2b = (x1c, x2c)\<close> and
    \<open>x = (x1b, x2b)\<close>
  shows \<open>mark_failed_lits_stack_inv NU x2e x1b\<close>
proof -
  show ?thesis
    using assms
    unfolding mark_failed_lits_stack_inv_def lit_redundant_rec_wl_inv_def
      lit_redundant_rec_wl_ref_def get_literal_and_remove_of_analyse_wl_def
    by (cases \<open>x1a\<close> rule: rev_cases)
       (auto simp: elim!: in_set_upd_cases)
qed

lemma lit_redundant_rec_wl_lookup_lit_redundant_rec_wl:
  assumes
    M_D: \<open>M \<Turnstile>as CNot D\<close> and
    n_d: \<open>no_dup M\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<close>
  shows
   \<open>lit_redundant_rec_wl_lookup \<A> M NU D cach analysis lbd \<le>
      \<Down> Id (lit_redundant_rec_wl M NU D cach analysis lbd)\<close>
proof -
  have M: \<open>\<forall>a \<in> lits_of_l M. a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
    using literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l lits by blast
  have [simp]: \<open>- x1e \<in> lits_of_l M \<Longrightarrow> atm_in_conflict (atm_of x1e) D \<longleftrightarrow> x1e \<in># D\<close> for x1e
    using M_D n_d
    by (auto simp: atm_in_conflict_def true_annots_true_cls_def_iff_negation_in_model
        atms_of_def atm_of_eq_atm_of dest!: multi_member_split no_dup_consistentD)
  have [simp, intro]: \<open>- x1e \<in> lits_of_l M \<Longrightarrow> atm_of x1e \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
     \<open>x1e \<in> lits_of_l M \<Longrightarrow> x1e \<in># (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
     \<open>- x1e \<in> lits_of_l M \<Longrightarrow> x1e \<in># (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> for x1e
    using lits atm_of_notin_atms_of_iff literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l apply blast
    using M uminus_\<A>\<^sub>i\<^sub>n_iff by auto
  have [refine_vcg]: \<open>(a, b) \<in> Id \<Longrightarrow> (a, b) \<in> \<langle>Id\<rangle>option_rel\<close> for a b by auto
  have [refine_vcg]: \<open>get_propagation_reason M x
    \<le> \<Down> (\<langle>nat_rel\<rangle>option_rel) (get_propagation_reason M y)\<close> if \<open>x = y\<close> for x y
    by (use that in auto)
  have [refine_vcg]:\<open>RETURN (\<not> level_in_lbd (get_level M L) lbd) \<le> \<Down> Id (RES UNIV)\<close> for L
    by auto
  have [refine_vcg]: \<open>mark_failed_lits_wl NU a b
    \<le> \<Down> Id
        (mark_failed_lits_wl NU a' b')\<close> if \<open>a = a'\<close> and \<open>b = b'\<close> for a a' b b'
    unfolding that by auto

  show ?thesis
    unfolding lit_redundant_rec_wl_lookup_def lit_redundant_rec_wl_def WHILET_def
    apply (refine_vcg)
    subgoal by auto
    subgoal by (auto simp: lit_redundant_rec_wl_inv_def
          lit_redundant_rec_wl_ref_def)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def
          elim!: neq_Nil_revE)
    subgoal by (auto simp: lit_redundant_rec_wl_inv_def elim!: neq_Nil_revE)
    subgoal by auto
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c
      unfolding lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def
      by (auto simp: lit_redundant_rec_wl_inv_def elim!: neq_Nil_revE[of x1a])
    subgoal by auto
    subgoal by auto
    subgoal by (auto intro!:)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule lit_redundant_rec_wl_lookup_mark_failed_lits_stack_inv; assumption?)
        (auto)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule lit_redundant_rec_wl_lookup_mark_failed_lits_stack_inv) auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition literal_redundant_wl_lookup where
  \<open>literal_redundant_wl_lookup \<A> M NU D cach L lbd = do {
     ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>);
     if get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE
     then RETURN (cach, [], True)
     else if cach (atm_of L) = SEEN_FAILED
     then RETURN (cach, [], False)
     else do {
       ASSERT(-L \<in> lits_of_l M);
       C \<leftarrow> get_propagation_reason M (-L);
       case C of
         Some C \<Rightarrow> lit_redundant_rec_wl_lookup \<A> M NU D cach [lit_redundant_reason_stack (-L) NU C] lbd
       | None \<Rightarrow> do {
           RETURN (cach, [], False)
       }
     }
  }\<close>

lemma literal_redundant_wl_lookup_literal_redundant_wl:
  assumes \<open>M \<Turnstile>as CNot D\<close> \<open>no_dup M\<close> \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<close>
  shows
    \<open>literal_redundant_wl_lookup \<A> M NU D cach L lbd \<le> \<Down> Id (literal_redundant_wl M NU D cach L lbd)\<close>
proof -
  have M: \<open>\<forall>a \<in> lits_of_l M. a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
    using literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l assms by blast
  have [simp, intro!]: \<open>- x1e \<in> lits_of_l M \<Longrightarrow> atm_of x1e \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
     \<open>- x1e \<in> lits_of_l M \<Longrightarrow> x1e \<in># (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> for x1e
    using assms atm_of_notin_atms_of_iff literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l apply blast
    using M uminus_\<A>\<^sub>i\<^sub>n_iff by auto
  have [refine]: \<open>(x, x') \<in> Id \<Longrightarrow> (x, x') \<in> \<langle>Id\<rangle>option_rel\<close> for x x'
    by auto
  have [refine_vcg]: \<open>get_propagation_reason M x
    \<le> \<Down> (\<langle>nat_rel\<rangle>option_rel) (get_propagation_reason M y)\<close> if \<open>x = y\<close> and \<open>y \<in> lits_of_l M\<close> for x y
    by (use that in auto)
  show ?thesis
    unfolding literal_redundant_wl_lookup_def literal_redundant_wl_def
    apply (refine_vcg lit_redundant_rec_wl_lookup_lit_redundant_rec_wl)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x x' xa x'a
      apply (subgoal_tac \<open>lit_redundant_rec_wl_lookup \<A> M NU D cach [lit_redundant_reason_stack (-L) NU xa] lbd
    \<le> \<Down> Id (lit_redundant_rec_wl M NU D cach [lit_redundant_reason_stack (-L) NU xa] lbd)\<close>)
      subgoal by simp
      subgoal using assms
        by (rule lit_redundant_rec_wl_lookup_lit_redundant_rec_wl)
      done
    done
qed


definition (in -) lookup_conflict_nth where
  [simp]: \<open>lookup_conflict_nth = (\<lambda>(_, xs) i. xs ! i)\<close>

definition (in -) lookup_conflict_size where
  [simp]: \<open>lookup_conflict_size = (\<lambda>(n, xs). n)\<close>

definition (in -) lookup_conflict_upd_None where
  [simp]: \<open>lookup_conflict_upd_None = (\<lambda>(n, xs) i. (n-1, xs [i :=None]))\<close>

definition minimize_and_extract_highest_lookup_conflict
  :: \<open>nat multiset \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat clause \<Rightarrow> (nat \<Rightarrow> minimize_status) \<Rightarrow> lbd \<Rightarrow>
     out_learned \<Rightarrow> (nat clause \<times> (nat \<Rightarrow> minimize_status) \<times> out_learned) nres\<close>
where
  \<open>minimize_and_extract_highest_lookup_conflict \<A> = (\<lambda>M NU nxs s lbd outl. do {
    (D, _, s, outl) \<leftarrow>
       WHILE\<^sub>T\<^bsup>minimize_and_extract_highest_lookup_conflict_inv\<^esup>
         (\<lambda>(nxs, i, s, outl). i < length outl)
         (\<lambda>(nxs, x, s, outl). do {
            ASSERT(x < length outl);
            let L = outl ! x;
            ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>);
            (s', _, red) \<leftarrow> literal_redundant_wl_lookup \<A> M NU nxs s L lbd;
            if \<not>red
            then RETURN (nxs, x+1, s', outl)
            else do {
               ASSERT (delete_from_lookup_conflict_pre \<A> (L, nxs));
               RETURN (remove1_mset L nxs, x, s', delete_index_and_swap outl x)
            }
         })
         (nxs, one_uint32_nat, s, outl);
     RETURN (D, s, outl)
  })\<close>

lemma entails_uminus_filter_to_poslev_can_remove:
  assumes NU_uL_E: \<open>NU \<Turnstile>p add_mset (- L) (filter_to_poslev M' L E)\<close> and
     NU_E: \<open>NU \<Turnstile>p E\<close> and L_E: \<open>L \<in># E\<close>
   shows \<open>NU \<Turnstile>p remove1_mset L E\<close>
proof -
  have \<open>filter_to_poslev M' L E \<subseteq># remove1_mset L E\<close>
    by (induction E)
       (auto simp add: filter_to_poslev_add_mset remove1_mset_add_mset_If subset_mset_trans_add_mset
        intro: diff_subset_eq_self subset_mset.dual_order.trans)
  then have \<open>NU \<Turnstile>p add_mset (- L) (remove1_mset L E)\<close>
    using NU_uL_E
    by (meson conflict_minimize_intermediate_step mset_subset_eqD)
  moreover have \<open>NU \<Turnstile>p add_mset L (remove1_mset L E)\<close>
    using NU_E L_E by auto
  ultimately show ?thesis
    using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of NU L \<open>remove1_mset L E\<close>
        \<open>remove1_mset L E\<close>]
    by (auto simp: true_clss_cls_add_self)
qed

lemma minimize_and_extract_highest_lookup_conflict_iterate_over_conflict:
  fixes D :: \<open>nat clause\<close> and S' :: \<open>nat twl_st_l\<close> and NU :: \<open>nat clauses_l\<close> and S :: \<open>nat twl_st_wl\<close>
     and S'' :: \<open>nat twl_st\<close>
   defines
    \<open>S''' \<equiv> state\<^sub>W_of S''\<close>
  defines
    \<open>M \<equiv> get_trail_wl S\<close> and
    NU: \<open>NU \<equiv> get_clauses_wl S\<close> and
    NU'_def: \<open>NU' \<equiv> mset `# ran_mf NU\<close> and
    NUE: \<open>NUE \<equiv> get_unit_learned_clss_wl S + get_unit_init_clss_wl S\<close> and
    M': \<open>M' \<equiv> trail S'''\<close>
  assumes
    S_S': \<open>(S, S') \<in> state_wl_l None\<close> and
    S'_S'': \<open>(S', S'') \<in> twl_st_l None\<close> and
    D'_D: \<open>mset (tl outl) = D\<close> and
    M_D: \<open>M \<Turnstile>as CNot D\<close> and
    dist_D: \<open>distinct_mset D\<close> and
    tauto: \<open>\<not>tautology D\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<close> and
    struct_invs: \<open>twl_struct_invs S''\<close> and
    add_inv: \<open>twl_list_invs S'\<close> and
    cach_init: \<open>conflict_min_analysis_inv M' s' (NU' + NUE) D\<close> and
    NU_P_D: \<open>NU' + NUE \<Turnstile>pm add_mset K D\<close> and
    lits_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> D\<close> and
    K: \<open>K = outl ! 0\<close> and
    outl_nempty: \<open>outl \<noteq> []\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
  shows
    \<open>minimize_and_extract_highest_lookup_conflict \<A> M NU D s' lbd outl \<le>
       \<Down> ({((E, s, outl), E'). E = E' \<and> mset (tl outl) = E \<and> outl ! 0 = K \<and>
               E' \<subseteq># D \<and> outl \<noteq> []})
           (iterate_over_conflict K M NU' NUE D)\<close>
    (is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  let ?UE = \<open>get_unit_learned_clss_wl S\<close>
  let ?NE = \<open>get_unit_init_clss_wl S\<close>
  define N U where
    \<open>N \<equiv> mset `# init_clss_lf NU\<close> and
    \<open>U \<equiv> mset `# learned_clss_lf NU\<close>
  obtain E where
     S''': \<open>S''' = (M', N + ?NE, U + ?UE, E)\<close>
    using M' S_S' S'_S'' unfolding S'''_def N_def U_def NU
    by (cases S) (auto simp: state_wl_l_def twl_st_l_def
        mset_take_mset_drop_mset')
  then have NU_N_U: \<open>mset `# ran_mf NU = N + U\<close>
    using NU S_S' S'_S'' unfolding S'''_def N_def U_def
    apply (subst all_clss_l_ran_m[symmetric])
    apply (subst image_mset_union[symmetric])
    apply (subst image_mset_union[symmetric])
    by (auto simp: mset_take_mset_drop_mset')
  let ?NU = \<open>N + ?NE + U + ?UE\<close>
  have NU'_N_U: \<open>NU' = N + U\<close>
    unfolding NU'_def N_def U_def mset_append[symmetric] image_mset_union[symmetric]
    by auto
  have NU'_NUE: \<open>NU' + NUE = N + get_unit_init_clss_wl S + U + get_unit_learned_clss_wl S\<close>
    unfolding NUE NU'_N_U by (auto simp: ac_simps)
  have struct_inv_S''': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M', N + get_unit_init_clss_wl S,
          U + get_unit_learned_clss_wl S, E)\<close>
    using struct_invs unfolding twl_struct_invs_def S'''_def[symmetric] S'''
    by fast
  then have n_d: \<open>no_dup M'\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      trail.simps by fast
  then have n_d: \<open>no_dup M\<close>
    using S_S' S'_S'' unfolding M_def M' S'''_def by (auto simp: twl_st_wl twl_st_l twl_st)

  define R where
    \<open>R = {((D':: nat clause, i, cach :: nat \<Rightarrow> minimize_status, outl' :: out_learned),
            (F :: nat clause, E :: nat clause)).
            i \<le> length outl' \<and>
            F \<subseteq># D \<and>
            E \<subseteq># F \<and>
            mset (drop i outl') = E \<and>
            mset (tl outl') = F \<and>
            conflict_min_analysis_inv M' cach (?NU) F \<and>
            NU' + NUE \<Turnstile>pm add_mset K F \<and>
            mset (tl outl') = D' \<and>
            i > 0 \<and> outl' \<noteq> [] \<and>
            outl' ! 0 = K
        }\<close>
  have [simp]: \<open>add_mset K (mset (tl outl)) = mset outl\<close>
    using D'_D K
    by (cases outl) (auto simp: drop_Suc outl_nempty)
  have \<open>Suc 0 < length outl \<Longrightarrow>
    highest_lit M (mset (take (Suc 0) (tl outl)))
     (Some (outl ! Suc 0, get_level M (outl ! Suc 0)))\<close>
    using outl_nempty
    by (cases outl; cases \<open>tl outl\<close>)  (auto simp: highest_lit_def get_maximum_level_add_mset)
   then have init_args_ref: \<open>((D, one_uint32_nat, s', outl), D, D) \<in> R\<close>
    using D'_D cach_init NU_P_D dist_D tauto K
    unfolding R_def NUE NU'_def NU_N_U
    by (auto simp: ac_simps drop_Suc outl_nempty)

   have init_lo_inv: \<open>minimize_and_extract_highest_lookup_conflict_inv s'\<close>
    if
      \<open>(s', s) \<in> R\<close> and
      \<open>iterate_over_conflict_inv M D s\<close>
    for s' s
   proof -
     have [dest!]: \<open>mset b \<subseteq># D \<Longrightarrow> length b \<le> size D\<close> for b
       using size_mset_mono by fastforce
    show ?thesis
      using that simple_clss_size_upper_div2[OF bounded lits_D dist_D tauto]
      unfolding minimize_and_extract_highest_lookup_conflict_inv_def
      by (auto simp: R_def uint_max_def)
  qed
  have cond: \<open>(m < length outl') = (D' \<noteq> {#})\<close>
    if
      st'_st: \<open>(st', st) \<in> R\<close> and
      \<open>minimize_and_extract_highest_lookup_conflict_inv st'\<close> and
      \<open>iterate_over_conflict_inv M D st\<close> and
      st:
        \<open>x2b = (j, outl')\<close>
        \<open>x2a = (m, x2b)\<close>
        \<open>st' = (nxs, x2a)\<close>
        \<open>st = (E, D')\<close>
    for st' st nxs x2a m x2b j x2c D' E st2 st3 outl'
  proof -
    show ?thesis
      using st'_st unfolding st R_def
      by auto
  qed

  have redundant: \<open>literal_redundant_wl_lookup \<A> M NU nxs cach
          (outl' ! x1d) lbd
      \<le> \<Down> {((s', a', b'), b). b = b' \<and>
            (b \<longrightarrow> NU' + NUE \<Turnstile>pm remove1_mset L (add_mset K E) \<and>
               conflict_min_analysis_inv M' s' ?NU (remove1_mset L E)) \<and>
            (\<not>b \<longrightarrow> NU' + NUE \<Turnstile>pm add_mset K E \<and> conflict_min_analysis_inv M' s' ?NU E)}
          (is_literal_redundant_spec K NU' NUE E L)\<close>
    (is \<open>_ \<le> \<Down> ?red _\<close>)
    if
      R: \<open>(x, x') \<in> R\<close> and
      \<open>case x' of (D, D') \<Rightarrow> D' \<noteq> {#}\<close> and
      \<open>minimize_and_extract_highest_lookup_conflict_inv x\<close> and
      \<open>iterate_over_conflict_inv M D x'\<close> and
      st:
        \<open>x' = (E, x1a)\<close>
        \<open>x2d = (cach, outl')\<close>
        \<open>x2c = (x1d, x2d)\<close>
        \<open>x = (nxs, x2c)\<close> and
      L: \<open>(outl'!x1d, L) \<in> Id\<close>
      \<open>x1d < length outl'\<close>
    for x x' E x2 x1a x2a nxs x2c x1d x2d x1e x2e cach highest L outl' st3
  proof -
    let ?L = \<open>(outl' ! x1d)\<close>
    have
      \<open>x1d < length outl'\<close> and
      \<open>x1d \<le> length outl'\<close> and
      \<open>mset (tl outl') \<subseteq># D\<close> and
      \<open>E = mset (tl outl')\<close> and
      cach: \<open>conflict_min_analysis_inv M' cach ?NU E\<close> and
      NU_P_E: \<open>NU' + NUE \<Turnstile>pm add_mset K (mset (tl outl'))\<close> and
      \<open>nxs = mset (tl outl')\<close> and
      \<open>0 < x1d\<close> and
      [simp]: \<open>L = outl'!x1d\<close> and
      \<open>E \<subseteq># D\<close>
      \<open>E = mset (tl outl')\<close> and
      \<open>E = nxs\<close>
      using R L unfolding R_def st
      by auto

    have M_x1: \<open>M \<Turnstile>as CNot E\<close>
      by (metis CNot_plus M_D \<open>E \<subseteq># D\<close> subset_mset.le_iff_add true_annots_union)
    then have M'_x1: \<open>M' \<Turnstile>as CNot E\<close>
      using S_S' S'_S'' unfolding M' M_def S'''_def by (auto simp: twl_st twl_st_wl twl_st_l)
    have \<open>outl' ! x1d \<in># E\<close>
      using \<open>E = mset (tl outl')\<close> \<open>x1d < length outl'\<close> \<open>0 < x1d\<close>
      by (auto simp: nth_in_set_tl)

  have 1:
    \<open>literal_redundant_wl_lookup \<A> M NU nxs cach ?L lbd \<le> \<Down> Id (literal_redundant_wl M NU nxs cach ?L lbd)\<close>
      by (rule literal_redundant_wl_lookup_literal_redundant_wl)
       (use n_d lits M_x1 struct_invs add_inv \<open>outl' ! x1d \<in># E\<close> \<open>E = nxs\<close> in auto)
    then have 1:
    \<open>literal_redundant_wl_lookup \<A> M NU nxs cach ?L lbd \<le> (literal_redundant_wl M NU nxs cach ?L lbd)\<close>
      by simp

    have 2:
      \<open>literal_redundant_wl M NU nxs cach ?L lbd \<le> \<Down>
       (Id \<times>\<^sub>r {(analyse, analyse'). analyse' = convert_analysis_list NU analyse \<and>
          lit_redundant_rec_wl_ref NU analyse} \<times>\<^sub>r bool_rel)
       (literal_redundant M' NU' nxs cach ?L)\<close>
      by (rule literal_redundant_wl_literal_redundant[of S S' S'',
            unfolded M_def[symmetric] NU[symmetric] M'[symmetric] S'''_def[symmetric]
            NU'_def[symmetric], THEN order_trans])
        (use bounded S_S' S'_S'' M_x1 struct_invs add_inv \<open>outl' ! x1d \<in># E\<close> \<open>E = nxs\<close> in
          \<open>auto simp: NU\<close>)

    have 3:
       \<open>literal_redundant M' (N + U) nxs cach ?L \<le>
         literal_redundant_spec M' (N + U + ?NE +  ?UE) nxs ?L\<close>
      unfolding \<open>E = nxs\<close>[symmetric]
      apply (rule literal_redundant_spec)
         apply (rule struct_inv_S''')
      apply (rule cach)
       apply (rule \<open>outl' ! x1d \<in># E\<close>)
      apply (rule M'_x1)
      done

    then have 3:
       \<open>literal_redundant M' (NU') nxs cach ?L \<le> literal_redundant_spec M' ?NU nxs ?L\<close>
      by (auto simp: ac_simps NU'_N_U)

    have ent: \<open>NU' + NUE \<Turnstile>pm add_mset (- L) (filter_to_poslev M' L (add_mset K E))\<close>
      if \<open>NU' + NUE \<Turnstile>pm add_mset (- L) (filter_to_poslev M' L E)\<close>
      using that by (auto simp: filter_to_poslev_add_mset add_mset_commute)
    show ?thesis
      apply (rule order.trans)
       apply (rule 1)
      apply (rule order.trans)
       apply (rule 2)
      apply (rule order.trans)
       apply (rule ref_two_step'[OF 3])
      unfolding literal_redundant_spec_def is_literal_redundant_spec_def
          conc_fun_SPEC NU'_NUE[symmetric]
      apply (rule SPEC_rule)
      apply clarify
      using NU_P_E ent \<open>E = nxs\<close> \<open>E = mset (tl outl')\<close>[symmetric] \<open>outl' ! x1d \<in># E\<close>
      by (auto simp: intro!: entails_uminus_filter_to_poslev_can_remove[of _ _ M']
          filter_to_poslev_conflict_min_analysis_inv simp del: diff_union_swap2)
  qed

  have
    outl'_F: \<open>outl' ! i \<in># F\<close> (is ?out) and
    outl'_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>outl' ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> (is ?out_L)
    if
      R: \<open>(S, T) \<in> R\<close> and
      \<open>case S of (nxs, i, s, outl) \<Rightarrow> i < length outl\<close> and
      \<open>case T of (D, D') \<Rightarrow> D' \<noteq> {#}\<close> and
      \<open>minimize_and_extract_highest_lookup_conflict_inv S\<close> and
      \<open>iterate_over_conflict_inv M D T\<close> and
      st:
        \<open>T = (F', F)\<close>
        \<open>S2 = (cach, outl')\<close>
        \<open>S1 = (i, S2)\<close>
        \<open>S = (D', S1)\<close>
      \<open>i < length outl'\<close>
    for S T F' T1 F highest' D' S1 i S2 cach S3 highest outl'
  proof -
    have ?out and \<open>F \<subseteq># D\<close>
      using R \<open>i < length outl'\<close> unfolding R_def st
      by (auto simp: set_drop_conv)
    show ?out
      using \<open>?out\<close> .
    then have \<open>outl' ! i \<in># D\<close>
      using \<open>F \<subseteq># D\<close> by auto
    then show ?out_L
      using lits_D by (auto dest!: multi_member_split simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
  qed

  have
    not_red: \<open>\<not> red \<Longrightarrow> ((D', i + 1, cachr, outl'), F',
        remove1_mset L F) \<in> R\<close> (is \<open>_ \<Longrightarrow> ?not_red\<close>) and
    red: \<open>\<not> \<not> red \<Longrightarrow>
       ((remove1_mset (outl' ! i) D', i, cachr, delete_index_and_swap outl' i),
       remove1_mset L F', remove1_mset L F) \<in> R\<close> (is \<open>_ \<Longrightarrow> ?red\<close>) and
     del: \<open>delete_from_lookup_conflict_pre \<A> (outl' ! i, D')\<close> (is ?del)
    if
      R: \<open>(S, T) \<in> R\<close> and
      \<open>case S of (nxs, i, s, outl) \<Rightarrow> i < length outl\<close> and
      \<open>case T of (D, D') \<Rightarrow> D' \<noteq> {#}\<close> and
      \<open>minimize_and_extract_highest_lookup_conflict_inv S\<close> and
      \<open>iterate_over_conflict_inv M D T\<close> and
      st:
         \<open>T = (F', F)\<close>
         \<open>S2 = (cach, outl')\<close>
         \<open>S1 = (i, S2)\<close>
         \<open>S = (D', S1)\<close>
         \<open>cachred1 = (stack, red)\<close>
         \<open>cachred = (cachr, cachred1)\<close> and
      \<open>i < length outl'\<close> and
      L: \<open>(outl' ! i, L) \<in> Id\<close> and
      \<open>outl' ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and
      cach: \<open>(cachred, red') \<in> (?red F' L)\<close>
    for S T F' T1 F D' S1 i S2 cach S3 highest outl' L cachred red' cachr
      cachred1 stack red
  proof -
    have \<open>L = outl' ! i\<close> and
      \<open>i \<le> length outl'\<close> and
      \<open>mset (tl outl') \<subseteq># D\<close> and
      \<open>mset (drop i outl') \<subseteq># mset (tl outl')\<close> and
      F: \<open>F = mset (drop i outl')\<close> and
      F': \<open>F' = mset (tl outl')\<close> and
      \<open>conflict_min_analysis_inv M' cach ?NU (mset (tl outl'))\<close> and
      \<open>NU' + NUE \<Turnstile>pm add_mset K (mset (tl outl'))\<close> and
      \<open>D' = mset (tl outl')\<close> and
      \<open>0 < i\<close> and
      [simp]: \<open>D' = F'\<close> and
      F'_D: \<open>F' \<subseteq># D\<close> and
      F'_F: \<open>F \<subseteq># F'\<close> and
      \<open>outl' \<noteq> []\<close> \<open>outl' ! 0 = K\<close>
      using R L unfolding R_def st
      by clarify+

    have [simp]: \<open>L = outl' ! i\<close>
      using L by fast
    have L_F: \<open>mset (drop (Suc i) outl') = remove1_mset L F\<close>
      unfolding F
      apply (subst (2) Cons_nth_drop_Suc[symmetric])
      using \<open>i < length outl'\<close> F'_D
      by (auto)
    have \<open>remove1_mset (outl' ! i) F \<subseteq># F'\<close>
      using \<open>F \<subseteq># F'\<close>
      by auto
    have \<open>red' = red\<close> and
      red: \<open>red \<longrightarrow> NU' + NUE \<Turnstile>pm remove1_mset L (add_mset K F') \<and>
       conflict_min_analysis_inv M' cachr ?NU (remove1_mset L F')\<close> and
      not_red: \<open>\<not> red \<longrightarrow> NU' + NUE \<Turnstile>pm add_mset K F' \<and> conflict_min_analysis_inv M' cachr ?NU F'\<close>
      using cach
      unfolding st
      by auto
    have [simp]: \<open>mset (drop (Suc i) (swap outl' (Suc 0) i)) = mset (drop (Suc i) outl')\<close>
      by (subst drop_swap_irrelevant) (use \<open>0 < i\<close> in auto)
    have [simp]: \<open>mset (tl (swap outl' (Suc 0) i)) = mset (tl outl')\<close>
      apply (cases outl'; cases i)
      using \<open>i > 0\<close> \<open>outl' \<noteq> []\<close> \<open>i < length outl'\<close>
         apply (auto simp: swap_def)
      unfolding swap_def[symmetric]
      by (auto simp: )
    have [simp]: \<open>mset (take (Suc i) (tl (swap outl' (Suc 0) i))) =  mset (take (Suc i) (tl outl'))\<close>
      using \<open>i > 0\<close> \<open>outl' \<noteq> []\<close> \<open>i < length outl'\<close>
      by (auto simp: take_tl take_swap_relevant tl_swap_relevant)
    have [simp]: \<open>mset (take i (tl (swap outl' (Suc 0) i))) =  mset (take i (tl outl'))\<close>
      using \<open>i > 0\<close> \<open>outl' \<noteq> []\<close> \<open>i < length outl'\<close>
      by (auto simp: take_tl take_swap_relevant tl_swap_relevant)

    have [simp]: \<open>\<not> Suc 0 < a \<longleftrightarrow> a = 0 \<or> a = 1\<close> for a :: nat
      by auto
     show ?not_red if \<open>\<not>red\<close>
      using \<open>i < length outl'\<close> F'_D L_F \<open>remove1_mset (outl' ! i) F \<subseteq># F'\<close> not_red that
         \<open>i > 0\<close> \<open>outl' ! 0 = K\<close>
      by (auto simp: R_def F[symmetric] F'[symmetric]  drop_swap_irrelevant)

    have [simp]: \<open>length (delete_index_and_swap outl' i) = length outl' - 1\<close>
      by auto
    have last: \<open>\<not> length outl' \<le> Suc i \<Longrightarrow>last outl' \<in> set (drop (Suc i) outl')\<close>
      by (metis List.last_in_set drop_eq_Nil last_drop not_le_imp_less)
    then have H: \<open>mset (drop i (delete_index_and_swap outl' i)) = mset (drop (Suc i) outl')\<close>
      using \<open>i < length outl'\<close>
      by (cases \<open>drop (Suc i) outl' = []\<close>)
        (auto simp: butlast_list_update mset_butlast_remove1_mset)
    have H': \<open>mset (tl (delete_index_and_swap outl' i)) = remove1_mset (outl' ! i) (mset (tl outl'))\<close>
      apply (rule mset_tl_delete_index_and_swap)
      using \<open>i < length outl'\<close> \<open>i > 0\<close> by fast+
    have [simp]: \<open>Suc 0 < i \<Longrightarrow> delete_index_and_swap outl' i ! Suc 0 = outl' ! Suc 0\<close>
      using \<open>i < length outl'\<close> \<open>i > 0\<close>
      by (auto simp: nth_butlast)
    have \<open>remove1_mset (outl' ! i) F \<subseteq># remove1_mset (outl' ! i) F'\<close>
      using \<open>F \<subseteq># F'\<close>
      using mset_le_subtract by blast
    have [simp]: \<open>delete_index_and_swap outl' i \<noteq> []\<close>
      using \<open>outl' \<noteq> []\<close> \<open>i > 0\<close> \<open>i < length outl'\<close>
      by (cases outl') (auto simp: butlast_update'[symmetric] split: nat.splits)
    have [simp]: \<open>delete_index_and_swap outl' i ! 0 = outl' ! 0\<close>
      using  \<open>outl' ! 0 = K\<close> \<open>i < length outl'\<close> \<open>i > 0\<close>
      by (auto simp: butlast_update'[symmetric] nth_butlast)
    have \<open>(outl' ! i) \<in># F'\<close>
      using \<open>i < length outl'\<close> \<open>i > 0\<close> unfolding F' by (auto simp: nth_in_set_tl)
    then show ?red if \<open>\<not>\<not>red\<close>
      using \<open>i < length outl'\<close> F'_D L_F \<open>remove1_mset (outl' ! i) F \<subseteq># remove1_mset (outl' ! i) F'\<close>
        red that \<open>i > 0\<close> \<open>outl' ! 0 = K\<close> unfolding R_def
      by (auto simp: R_def F[symmetric] F'[symmetric] H H' drop_swap_irrelevant
          simp del: delete_index_and_swap.simps)

    have \<open>outl' ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> \<open>outl' ! i \<in># D\<close>
      using \<open>(outl' ! i) \<in># F'\<close> F'_D lits_D
      by (force simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
          dest!: multi_member_split[of \<open>outl' ! i\<close> D])+
    then show ?del
      using \<open>(outl' ! i) \<in># F'\<close> lits_D F'_D tauto
      by (auto simp: delete_from_lookup_conflict_pre_def
          literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
  qed
  show ?thesis
    unfolding minimize_and_extract_highest_lookup_conflict_def iterate_over_conflict_def
    apply (refine_vcg WHILEIT_refine[where R = R])
    subgoal by (rule init_args_ref)
    subgoal for s' s by (rule init_lo_inv)
    subgoal by (rule cond)
    subgoal by auto
    subgoal by (rule outl'_F)
    subgoal by (rule outl'_\<L>\<^sub>a\<^sub>l\<^sub>l)
    apply (rule redundant; assumption)
    subgoal by auto
    subgoal by (rule not_red)
    subgoal by (rule del)
    subgoal
      by (rule red)
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c
      unfolding R_def by (cases x1b) auto
    done
qed

definition cach_refinement_list
  :: \<open>nat multiset \<Rightarrow> (minimize_status list \<times> (nat conflict_min_cach)) set\<close>
where
  \<open>cach_refinement_list \<A>\<^sub>i\<^sub>n = \<langle>Id\<rangle>map_fun_rel {(a, a'). a = a' \<and> a \<in># \<A>\<^sub>i\<^sub>n}\<close>

definition cach_refinement_nonull
  :: \<open>((minimize_status list \<times> nat list) \<times> minimize_status list) set\<close>
where
  \<open>cach_refinement_nonull = {((cach, support), cach'). cach = cach' \<and>
       (\<forall>L < length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set support) \<and>
       (\<forall>L \<in> set support. L < length cach)}\<close>


definition cach_refinement
  :: \<open>nat multiset \<Rightarrow> ((minimize_status list \<times> nat list) \<times> (nat conflict_min_cach)) set\<close>
where
  \<open>cach_refinement \<A>\<^sub>i\<^sub>n = cach_refinement_nonull O cach_refinement_list \<A>\<^sub>i\<^sub>n\<close>

lemma cach_refinement_alt_def:
  \<open>cach_refinement \<A>\<^sub>i\<^sub>n = {((cach, support), cach').
       (\<forall>L < length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set support) \<and>
       (\<forall>L \<in> set support. L < length cach) \<and>
       (\<forall>L \<in># \<A>\<^sub>i\<^sub>n. L < length cach \<and> cach ! L = cach' L)}\<close>
  unfolding cach_refinement_def cach_refinement_nonull_def cach_refinement_list_def
  by (auto simp: map_fun_rel_def)

abbreviation (in -) cach_refinement_l_assn where
  \<open>cach_refinement_l_assn \<equiv> array_assn minimize_status_assn *a arl_assn uint32_nat_assn\<close>

lemma in_cach_refinement_alt_def:
  \<open>((cach, support), cach') \<in> cach_refinement \<A>\<^sub>i\<^sub>n \<longleftrightarrow>
     (cach, cach') \<in> cach_refinement_list \<A>\<^sub>i\<^sub>n \<and>
     (\<forall>L<length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set support) \<and>
      (\<forall>L \<in> set support. L < length cach)\<close>
  by (auto simp: cach_refinement_def cach_refinement_nonull_def cach_refinement_list_def)

definition (in -) conflict_min_cach_l :: \<open>conflict_min_cach_l \<Rightarrow> nat \<Rightarrow> minimize_status\<close> where
  \<open>conflict_min_cach_l = (\<lambda>(cach, sup) L.
      (cach ! L)
 )\<close>

definition conflict_min_cach_l_pre where
  \<open>conflict_min_cach_l_pre = (\<lambda>((cach, sup), L). L < length cach)\<close>

lemma conflict_min_cach_l_pre:
  fixes x1 :: \<open>nat\<close> and x2 :: \<open>nat\<close>
  assumes
    \<open>x1n \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and
    \<open>(x1l, x1j) \<in> cach_refinement \<A>\<close>
  shows \<open>conflict_min_cach_l_pre (x1l, atm_of x1n)\<close>
proof -
  show ?thesis
    using assms by (auto simp: cach_refinement_alt_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n conflict_min_cach_l_pre_def)
qed

sepref_register conflict_min_cach_l
sepref_definition (in -) conflict_min_cach_l_code
  is \<open>uncurry (RETURN oo conflict_min_cach_l)\<close>
  :: \<open>[conflict_min_cach_l_pre]\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> minimize_status_assn\<close>
  unfolding conflict_min_cach_l_def conflict_min_cach_l_pre_def
  by sepref

declare conflict_min_cach_l_code.refine[sepref_fr_rules]

lemma nth_conflict_min_cach:
  \<open>(uncurry (RETURN oo conflict_min_cach_l), uncurry (RETURN oo conflict_min_cach)) \<in>
     [\<lambda>(cach, L). L \<in># \<A>\<^sub>i\<^sub>n]\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n \<times>\<^sub>r nat_rel \<rightarrow> \<langle>minimize_status_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: cach_refinement_def map_fun_rel_def
      cach_refinement_nonull_def cach_refinement_list_def conflict_min_cach_l_def)

definition (in -) conflict_min_cach_set_failed
   :: \<open>nat conflict_min_cach \<Rightarrow> nat \<Rightarrow> nat conflict_min_cach\<close>
where
  [simp]: \<open>conflict_min_cach_set_failed cach L = cach(L := SEEN_FAILED)\<close>

definition (in -) conflict_min_cach_set_failed_l
  :: \<open>conflict_min_cach_l \<Rightarrow> nat \<Rightarrow> conflict_min_cach_l nres\<close>
where
  \<open>conflict_min_cach_set_failed_l = (\<lambda>(cach, sup) L. do {
     ASSERT(L < length cach);
     RETURN (cach[L := SEEN_FAILED], sup @ [L])
   })\<close>

lemma conflict_min_cach_set_failed:
  \<open>(uncurry conflict_min_cach_set_failed_l, uncurry (RETURN oo conflict_min_cach_set_failed)) \<in>
     [\<lambda>(cach, L). L \<in># \<A>\<^sub>i\<^sub>n]\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n \<times>\<^sub>r nat_rel \<rightarrow> \<langle>cach_refinement \<A>\<^sub>i\<^sub>n\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: cach_refinement_alt_def map_fun_rel_def cach_refinement_list_def
      conflict_min_cach_set_failed_l_def)


sepref_definition (in -) conflict_min_cach_set_failed_l_code
  is \<open>uncurry conflict_min_cach_set_failed_l\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply arl_append_hnr[sepref_fr_rules]
  unfolding conflict_min_cach_set_failed_l_def
  by sepref

definition (in -) conflict_min_cach_set_removable
  :: \<open>nat conflict_min_cach \<Rightarrow> nat \<Rightarrow> nat conflict_min_cach\<close>
where
  [simp]: \<open>conflict_min_cach_set_removable cach L = cach(L:= SEEN_REMOVABLE)\<close>

sepref_definition (in -) conflict_min_cach_set_removable_l_code
  is \<open>uncurry conflict_min_cach_set_removable_l\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply arl_append_hnr[sepref_fr_rules]
  unfolding conflict_min_cach_set_removable_l_def
  by sepref

declare conflict_min_cach_set_removable_l_code.refine[sepref_fr_rules]

lemma conflict_min_cach_set_removable:
  \<open>(uncurry conflict_min_cach_set_removable_l,
    uncurry (RETURN oo conflict_min_cach_set_removable)) \<in>
     [\<lambda>(cach, L). L \<in># \<A>\<^sub>i\<^sub>n]\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n \<times>\<^sub>r nat_rel \<rightarrow> \<langle>cach_refinement \<A>\<^sub>i\<^sub>n\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: cach_refinement_alt_def map_fun_rel_def cach_refinement_list_def
      conflict_min_cach_set_removable_l_def)

abbreviation (in -)analyse_refinement_assn where
  \<open>analyse_refinement_assn \<equiv> arl_assn (nat_assn *a nat_assn *a nat_assn *a nat_assn)\<close>

abbreviation (in -)analyse_refinement_fast_assn where
  \<open>analyse_refinement_fast_assn \<equiv>
    arl_assn (uint64_nat_assn *a uint64_nat_assn *a uint64_nat_assn *a uint64_nat_assn)\<close>

lemma minimize_status_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in>
    minimize_status_assn\<^sup>k *\<^sub>a minimize_status_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by (sepref_to_hoare) (sep_auto)

(*TODO length analyse < uint32\_max *)
definition isa_mark_failed_lits_stack where
  \<open>isa_mark_failed_lits_stack NU analyse cach = do {
    let l = length analyse;
    (_, cach) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(_, cach). True\<^esup>
      (\<lambda>(i, cach). i < l)
      (\<lambda>(i, cach). do {
        ASSERT(i < length analyse);
        let (cls_idx, _, idx, _) = analyse ! i;
        ASSERT(cls_idx + idx \<ge> 1);
        ASSERT(cls_idx + idx - 1 < length NU);
	ASSERT(arena_lit_pre NU (cls_idx + idx - 1));
	cach \<leftarrow> conflict_min_cach_set_failed_l cach (atm_of (arena_lit NU (cls_idx + idx - 1)));
        RETURN (i+1, cach)
      })
      (0, cach);
    RETURN cach
   }\<close>


context
begin
private lemma mark_failed_lits_stack_inv_helper1: \<open>mark_failed_lits_stack_inv a ba a2' \<Longrightarrow>
       a1' < length ba \<Longrightarrow>
       (a1'a, a2'a) = ba ! a1' \<Longrightarrow>
       a1'a \<in># dom_m a\<close>
  using nth_mem[of a1' ba] unfolding mark_failed_lits_stack_inv_def
  by (auto simp del: nth_mem)

private lemma mark_failed_lits_stack_inv_helper2: \<open>mark_failed_lits_stack_inv a ba a2' \<Longrightarrow>
       a1' < length ba \<Longrightarrow>
       (a1'a, xx, a2'a, yy) = ba ! a1' \<Longrightarrow>
       a2'a - Suc 0 < length (a \<propto> a1'a)\<close>
  using nth_mem[of a1' ba] unfolding mark_failed_lits_stack_inv_def
  by (auto simp del: nth_mem)

lemma isa_mark_failed_lits_stack_isa_mark_failed_lits_stack:
  \<open>(uncurry2 isa_mark_failed_lits_stack, uncurry2 (mark_failed_lits_stack \<A>\<^sub>i\<^sub>n)) \<in>
     [\<lambda>((N, ana), cach). True]\<^sub>f
     {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f Id \<times>\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n \<rightarrow>
     \<langle>cach_refinement \<A>\<^sub>i\<^sub>n\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>((0, x2c), 0, x2a) \<in> nat_rel \<times>\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n\<close>
    if \<open>(x2c, x2a) \<in> cach_refinement \<A>\<^sub>i\<^sub>n\<close> for x2c x2a
    using that by auto
  have le_length_arena: \<open>x1g + x2g - 1 < length x1c\<close> (is ?le) and
    is_lit: \<open>arena_lit_pre x1c (x1g + x2g - 1)\<close> (is ?lit) and
    isA: \<open>atm_of (arena_lit x1c (x1g + x2g - 1)) \<in># \<A>\<^sub>i\<^sub>n\<close> (is ?A) and
    final: \<open>conflict_min_cach_set_failed_l x2e
     (atm_of (arena_lit x1c (x1g + x2g - 1)))
    \<le> SPEC
       (\<lambda>cach.
           RETURN (x1e + 1, cach)
           \<le> SPEC
              (\<lambda>c. (c, x1d + 1, x2d
                    (atm_of (x1a \<propto> x1f ! (x2f - 1)) := SEEN_FAILED))
                   \<in> nat_rel \<times>\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n))\<close> (is ?final) and
      ge1: \<open>x1g + x2g \<ge> 1\<close>
    if
      \<open>case y of (x, xa) \<Rightarrow> (case x of (N, ana) \<Rightarrow> \<lambda>cach. True) xa\<close> and
      xy: \<open>(x, y) \<in> {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f Id \<times>\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n\<close> and
      st:
        \<open>x1 = (x1a, x2)\<close>
        \<open>y = (x1, x2a)\<close>
        \<open>x1b = (x1c, x2b)\<close>
        \<open>x = (x1b, x2c)\<close>
        \<open>x' = (x1d, x2d)\<close>
        \<open>xa = (x1e, x2e)\<close>
	\<open>x2f2 = (x2f, x2f3)\<close>
	\<open>x2f0 = (x2f1, x2f2)\<close>
        \<open>x2 ! x1d = (x1f, x2f0)\<close>
	\<open>x2g2 = (x2g, x2g3)\<close>
	\<open>x2g0 = (x2g1, x2g2)\<close>
        \<open>x2b ! x1e = (x1g, x2g0)\<close> and
      xax': \<open>(xa, x') \<in> nat_rel \<times>\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n\<close> and
      cond: \<open>case xa of (i, cach) \<Rightarrow> i < length x2b\<close> and
      cond': \<open>case x' of (i, cach) \<Rightarrow> i < length x2\<close> and
      inv: \<open>case x' of (_, x) \<Rightarrow> mark_failed_lits_stack_inv x1a x2 x\<close> and
      \<open>x1d < length x2\<close> and
      le: \<open>x1e < length x2b\<close> and
      atm: \<open>atm_of (x1a \<propto> x1f ! (x2f - 1)) \<in># \<A>\<^sub>i\<^sub>n\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c xa x' x1d x2d x1e x2e x1f x2f x1g x2g
      x2f0 x2f1 x2f2 x2f3 x2g0 x2g1 x2g2 x2g3
  proof -
    obtain i cach where x': \<open>x' = (i, cach)\<close> by (cases x')
    have [simp]:
      \<open>x1 = (x1a, x2)\<close>
      \<open>y = ((x1a, x2), x2a)\<close>
      \<open>x1b = (x1c, x2)\<close>
      \<open>x = ((x1c, x2), x2c)\<close>
      \<open>x' = (x1d, x2d)\<close>
      \<open>xa = (x1d, x2e)\<close>
      \<open>x1f = x1g\<close>
      \<open>x2f = x2g\<close>
      \<open>x2f1 = x2g1\<close>
      \<open>x2f0 = x2g0\<close>
      \<open>x1e = x1d\<close>
      \<open>x2g0 = (x2g1, x2g, x2g3)\<close>
      \<open>x2f3 = x2g3\<close>
      \<open>x2f2 = x2g2\<close>
      \<open>x2b = x2\<close> and
      st': \<open>x2 ! x1d = (x1g, x2g0)\<close> and
      cach:\<open>(x2e, x2d) \<in> cach_refinement \<A>\<^sub>i\<^sub>n\<close> and
      \<open>(x2c, x2a) \<in> cach_refinement \<A>\<^sub>i\<^sub>n\<close>
      using xy st xax'
      by auto
    have arena: \<open>valid_arena x1c x1a vdom\<close>
      using xy unfolding st by auto
    have \<open>x2 ! x1e \<in> set x2\<close>
      using le
      by auto
    then have \<open>x2 ! x1d \<in> set x2\<close> and
      x2f: \<open>x2f \<le> length (x1a \<propto> x1f)\<close> and
      x1f: \<open>x1g \<in># dom_m x1a\<close> and
      x2g: \<open>x2g > 0\<close>
      using inv le unfolding mark_failed_lits_stack_inv_def x' prod.case st st'
      by (auto simp del: nth_mem simp: st')
    have \<open>is_Lit (x1c ! (x1g + (x2g - 1)))\<close>
      by (rule arena_lifting[OF arena x1f]) (use x2f x2g in auto)
    then show ?le and ?A
      using arena_lifting[OF arena x1f] le x2f x1f x2g atm by (auto simp: arena_lit_def)
    show ?lit
      unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
      by (rule bex_leI[of _ x1f])
        (use arena x1f x2f x2g in \<open>auto intro!: exI[of _ x1a] exI[of _ vdom]\<close>)
    show \<open>x1g + x2g \<ge> 1\<close>
      using x2g by auto
    have [simp]: \<open>arena_lit x1c (x1g + x2g - Suc 0) = x1a \<propto> x1g ! (x2g - Suc 0)\<close>
       using that x1f x2f x2g by (auto simp: arena_lifting[OF arena])
    have \<open>atm_of (arena_lit x1c (x1g + x2g - Suc 0)) < length (fst x2e)\<close>
      using \<open>?A\<close> cach by (auto simp: cach_refinement_alt_def dest: multi_member_split)

    then show ?final
      using \<open>?le\<close> \<open>?A\<close> cach
      by (cases x2e)
        (auto simp: conflict_min_cach_set_failed_l_def cach_refinement_alt_def
        arena_lifting[OF arena])
  qed

  show ?thesis
    unfolding isa_mark_failed_lits_stack_def mark_failed_lits_stack_def uncurry_def
    apply (rewrite at \<open>let _ = length _ in _\<close> Let_def)
    apply (intro frefI nres_relI)
    apply refine_vcg
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule ge1)
    subgoal by (rule le_length_arena)
    subgoal
      by (rule is_lit)
    subgoal
      by (rule final)
    subgoal by auto
    done
qed

sepref_definition isa_mark_failed_lits_stack_code
  is \<open>uncurry2 (isa_mark_failed_lits_stack)\<close>
  :: \<open>arena_assn\<^sup>k *\<^sub>a analyse_refinement_assn\<^sup>d *\<^sub>a cach_refinement_l_assn\<^sup>d \<rightarrow>\<^sub>a
      cach_refinement_l_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim!] image_image[simp] length_rll_def[simp]
    mark_failed_lits_stack_inv_helper1[dest] mark_failed_lits_stack_inv_helper2[dest]
    fmap_length_rll_u_def[simp]
  unfolding isa_mark_failed_lits_stack_def PR_CONST_def
    conflict_min_cach_set_failed_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric]
    fmap_rll_def[symmetric]
    conflict_min_cach_set_failed_l_def
  by sepref


sepref_definition isa_mark_failed_lits_stack_fast_code
  is \<open>uncurry2 (isa_mark_failed_lits_stack)\<close>
  :: \<open>[\<lambda>((N, _), _). length N \<le> uint64_max]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a analyse_refinement_fast_assn\<^sup>d *\<^sub>a cach_refinement_l_assn\<^sup>d \<rightarrow>
    cach_refinement_l_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim!] image_image[simp] length_rll_def[simp]
    mark_failed_lits_stack_inv_helper1[dest] mark_failed_lits_stack_inv_helper2[dest]
    fmap_length_rll_u_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding isa_mark_failed_lits_stack_def PR_CONST_def
    conflict_min_cach_set_failed_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric]
    fmap_rll_def[symmetric]
    arena_lit_def[symmetric]
    conflict_min_cach_set_failed_l_def
  apply (rewrite in \<open>_ - \<hole>\<close> one_uint64_nat_def[symmetric])
  apply (rewrite in \<open>_ - \<hole>\<close> one_uint64_nat_def[symmetric])
  apply (rewrite in \<open>_ - \<hole>\<close> one_uint64_nat_def[symmetric])
  unfolding 
    fast_minus_def[symmetric]
  by sepref

sepref_register isa_mark_failed_lits_stack
declare isa_mark_failed_lits_stack_code.refine[sepref_fr_rules]
declare isa_mark_failed_lits_stack_fast_code.refine[sepref_fr_rules]

definition isa_get_literal_and_remove_of_analyse_wl
   :: \<open>arena \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> nat literal \<times> (nat \<times> nat \<times> nat \<times> nat) list\<close> where
  \<open>isa_get_literal_and_remove_of_analyse_wl C analyse =
    (let (i, k, j, len) = last analyse in
     (arena_lit C (i + j), analyse[length analyse - 1 := (i, k, j + 1, len)]))\<close>

definition isa_get_literal_and_remove_of_analyse_wl_pre
   :: \<open>arena \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> bool\<close> where
\<open>isa_get_literal_and_remove_of_analyse_wl_pre arena analyse \<longleftrightarrow>
  (let (i, k, j, len) = last analyse in
    (i + j) < length arena \<and> analyse \<noteq> [] \<and> arena_lit_pre arena (i+j))\<close>

sepref_definition isa_get_literal_and_remove_of_analyse_wl_code
  is \<open>uncurry (RETURN oo isa_get_literal_and_remove_of_analyse_wl)\<close>
  :: \<open>[uncurry isa_get_literal_and_remove_of_analyse_wl_pre]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a analyse_refinement_assn\<^sup>d \<rightarrow>
      unat_lit_assn *a analyse_refinement_assn\<close>
  unfolding isa_get_literal_and_remove_of_analyse_wl_pre_def
  isa_get_literal_and_remove_of_analyse_wl_def fast_minus_def[symmetric]
  by sepref

sepref_definition isa_get_literal_and_remove_of_analyse_wl_fast_code
  is \<open>uncurry (RETURN oo isa_get_literal_and_remove_of_analyse_wl)\<close>
  :: \<open>[\<lambda>(arena, analyse). isa_get_literal_and_remove_of_analyse_wl_pre arena analyse \<and>
         length arena \<le> uint64_max]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a analyse_refinement_fast_assn\<^sup>d \<rightarrow>
      unat_lit_assn *a analyse_refinement_fast_assn\<close>
  unfolding isa_get_literal_and_remove_of_analyse_wl_pre_def
  isa_get_literal_and_remove_of_analyse_wl_def fast_minus_def[symmetric]
  apply (rewrite at \<open>_ + \<hole>\<close> one_uint64_nat_def[symmetric])
  by sepref

declare isa_get_literal_and_remove_of_analyse_wl_code.refine[sepref_fr_rules]
declare isa_get_literal_and_remove_of_analyse_wl_fast_code.refine[sepref_fr_rules]

definition lit_redundant_reason_stack_wl_lookup
  :: \<open>nat literal \<Rightarrow> arena_el list \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat \<times> nat\<close>
where
\<open>lit_redundant_reason_stack_wl_lookup L NU C =
  (if arena_length NU C > 2 then (C, 0, 1, arena_length NU C)
  else if arena_lit NU C = L
  then (C, 0, 1, arena_length NU C)
  else (C, 1, 0, arena_length NU C))\<close>

definition isa_lit_redundant_rec_wl_lookup
  :: \<open>trail_pol \<Rightarrow> arena \<Rightarrow> lookup_clause_rel \<Rightarrow>
     _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (_ \<times> _ \<times> bool) nres\<close>
where
  \<open>isa_lit_redundant_rec_wl_lookup M NU D cach analysis lbd =
      WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
        (\<lambda>(cach, analyse, b). analyse \<noteq> [])
        (\<lambda>(cach, analyse, b). do {
            ASSERT(analyse \<noteq> []);
	    let (C, k, i, len) = last analyse;
            ASSERT(C < length NU);
            ASSERT(arena_is_valid_clause_idx NU C);
            ASSERT(arena_lit_pre NU (C + k));
            if i \<ge> nat_of_uint64_conv len
            then do {
	      cach \<leftarrow> conflict_min_cach_set_removable_l cach (atm_of (arena_lit NU (C + k)));
              RETURN(cach, butlast analyse, True)
	    }
            else do {
               ASSERT (isa_get_literal_and_remove_of_analyse_wl_pre NU analyse);
               let (L, analyse) = isa_get_literal_and_remove_of_analyse_wl NU analyse;
               ASSERT(get_level_pol_pre (M, L));
               let b = \<not>level_in_lbd (get_level_pol M L) lbd;
               ASSERT(atm_in_conflict_lookup_pre (atm_of L) D);
	       ASSERT(conflict_min_cach_l_pre (cach, atm_of L));
               if (get_level_pol M L = zero_uint32_nat \<or>
                   conflict_min_cach_l cach (atm_of L) = SEEN_REMOVABLE \<or>
                   atm_in_conflict_lookup (atm_of L) D)
               then RETURN (cach, analyse, False)
               else if b \<or> conflict_min_cach_l cach (atm_of L) = SEEN_FAILED
               then do {
                  cach \<leftarrow> isa_mark_failed_lits_stack NU analyse cach;
                  RETURN (cach, [], False)
               }
               else do {
                  C \<leftarrow> get_propagation_reason_pol M (-L);
                  case C of
                    Some C \<Rightarrow> RETURN (cach, analyse @ [lit_redundant_reason_stack_wl_lookup (-L) NU C], False)
                  | None \<Rightarrow> do {
                      cach \<leftarrow> isa_mark_failed_lits_stack NU analyse cach;
                      RETURN (cach, [], False)
                }
            }
          }
        })
       (cach, analysis, False)\<close>

lemma isa_lit_redundant_rec_wl_lookup_alt_def:
  \<open>isa_lit_redundant_rec_wl_lookup M NU D cach analysis lbd =
    WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
      (\<lambda>(cach, analyse, b). analyse \<noteq> [])
      (\<lambda>(cach, analyse, b). do {
          ASSERT(analyse \<noteq> []);
	  let (C, k, i, len) = last analyse;
          ASSERT(C < length NU);
          let _ = map xarena_lit
              ((Misc.slice
                C
                (C + arena_length NU C))
                NU);
          ASSERT(arena_is_valid_clause_idx NU C);
          ASSERT(arena_lit_pre NU (C + k));
          if i \<ge> nat_of_uint64_conv len
          then do {
	    cach \<leftarrow> conflict_min_cach_set_removable_l cach (atm_of (arena_lit NU (C + k)));
            RETURN(cach, butlast analyse, True)
          }
          else do {
              ASSERT (isa_get_literal_and_remove_of_analyse_wl_pre NU analyse);
              let (L, analyse) = isa_get_literal_and_remove_of_analyse_wl NU analyse;
              ASSERT(get_level_pol_pre (M, L));
              let b = \<not>level_in_lbd (get_level_pol M L) lbd;
              ASSERT(atm_in_conflict_lookup_pre (atm_of L) D);
	      ASSERT(conflict_min_cach_l_pre (cach, atm_of L));
              if (get_level_pol M L = zero_uint32_nat \<or>
                  conflict_min_cach_l cach (atm_of L) = SEEN_REMOVABLE \<or>
                  atm_in_conflict_lookup (atm_of L) D)
              then RETURN (cach, analyse, False)
              else if b \<or> conflict_min_cach_l cach (atm_of L) = SEEN_FAILED
              then do {
                cach \<leftarrow> isa_mark_failed_lits_stack NU analyse cach;
                RETURN (cach, [], False)
              }
              else do {
                C \<leftarrow> get_propagation_reason_pol M (-L);
                case C of
                  Some C \<Rightarrow> RETURN (cach, analyse @ [lit_redundant_reason_stack_wl_lookup (-L) NU C], False)
                | None \<Rightarrow> do {
                    cach \<leftarrow> isa_mark_failed_lits_stack NU analyse cach;
                    RETURN (cach, [], False)
                }
            }
        }
      })
      (cach, analysis, False)\<close>
  unfolding isa_lit_redundant_rec_wl_lookup_def by (auto simp: Let_def)

lemma isa_lit_redundant_rec_wl_lookup_lit_redundant_rec_wl_lookup:
  \<open>(uncurry5 isa_lit_redundant_rec_wl_lookup, uncurry5 (lit_redundant_rec_wl_lookup \<A>)) \<in>
    [\<lambda>(((((_, N), _), _), _), _).  literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> ((mset \<circ> fst) `# ran_m N)]\<^sub>f
    trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f lookup_clause_rel \<A> \<times>\<^sub>f
     cach_refinement \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow>
      \<langle>cach_refinement \<A> \<times>\<^sub>r Id \<times>\<^sub>r bool_rel\<rangle>nres_rel\<close>
proof -
  have isa_mark_failed_lits_stack: \<open>(uncurry2 isa_mark_failed_lits_stack, uncurry2 mark_failed_lits_wl)
    \<in> [\<lambda>((a, b), ba).
          literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> ((mset \<circ> fst) `# ran_m a) \<and>
          mark_failed_lits_stack_inv a b
           ba]\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f Id \<times>\<^sub>f
                 cach_refinement \<A> \<rightarrow> \<langle>cach_refinement \<A>\<rangle>nres_rel\<close>
    using isa_mark_failed_lits_stack_isa_mark_failed_lits_stack[FCOMP
       mark_failed_lits_stack_mark_failed_lits_wl] .
  have [refine0]: \<open>get_propagation_reason_pol M' L'
    \<le> \<Down> (\<langle>Id\<rangle>option_rel)
       (get_propagation_reason M L)\<close>
    if \<open>(M', M) \<in> trail_pol \<A>\<close> and \<open>(L', L) \<in> Id\<close> and \<open>L \<in> lits_of_l M\<close>
    for M M' L L'
    using get_propagation_reason_pol[of \<A>, THEN fref_to_Down_curry, of M L M' L'] that by auto
  note [simp]=get_literal_and_remove_of_analyse_wl_def isa_get_literal_and_remove_of_analyse_wl_def
    arena_lifting and [split] = prod.splits

  show ?thesis
    supply [[goals_limit=3]]
    supply RETURN_as_SPEC_refine[refine2 add]
    unfolding isa_lit_redundant_rec_wl_lookup_alt_def lit_redundant_rec_wl_lookup_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
      isa_mark_failed_lits_stack[THEN fref_to_Down_curry2])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m
        by (auto simp: arena_lifting)
    subgoal by (auto simp: arena_is_valid_clause_idx_def)
    subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m
      by (auto simp: arena_lifting arena_is_valid_clause_idx_def)
    subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q
       x2q x1r x2r x1s x2s
      apply (auto simp: arena_is_valid_clause_idx_def lit_redundant_rec_wl_inv_def
        isa_get_literal_and_remove_of_analyse_wl_pre_def arena_lit_pre_def
        arena_is_valid_clause_idx_and_access_def lit_redundant_rec_wl_ref_def)
      apply (rule_tac x = \<open>x1q\<close> in exI; auto; rule_tac x = \<open>N\<close> in exI; force simp: arena_lifting)+
      done
    subgoal by (auto simp: arena_lifting arena_is_valid_clause_idx_def nat_of_uint64_conv_def
      lit_redundant_rec_wl_inv_def)
    subgoal
      by (auto simp: arena_lifting arena_is_valid_clause_idx_def bind_rule_complete_RES conc_fun_RETURN
           in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def
          intro!:  conflict_min_cach_set_removable[of \<A>,THEN fref_to_Down_curry, THEN order_trans]
	  dest: List.last_in_set)

   subgoal
      apply (auto simp: arena_is_valid_clause_idx_def
        isa_get_literal_and_remove_of_analyse_wl_pre_def arena_lit_pre_def
        arena_is_valid_clause_idx_and_access_def)
      apply (rule_tac x = x1n in exI; solves auto)+
      done
    subgoal by (auto intro!: get_level_pol_pre)
    subgoal
      by (simp add: atm_in_conflict_lookup_pre)
    subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o
      by (simp add: conflict_min_cach_l_pre)
    subgoal
      by (auto simp: atm_in_conflict_lookup_atm_in_conflict[THEN fref_to_Down_unRET_uncurry_Id]
          nth_conflict_min_cach[THEN fref_to_Down_unRET_uncurry_Id] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
	  get_level_get_level_pol atms_of_def
  	split: prod.splits)
       (subst (asm)  atm_in_conflict_lookup_atm_in_conflict[THEN fref_to_Down_unRET_uncurry_Id];
	  auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n atms_of_def)+
    subgoal by (auto simp: split: prod.splits)
    subgoal by (auto simp: atm_in_conflict_lookup_atm_in_conflict[THEN fref_to_Down_unRET_uncurry_Id]
          nth_conflict_min_cach[THEN fref_to_Down_unRET_uncurry_Id] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
	  get_level_get_level_pol atms_of_def
  	split: prod.splits)
    subgoal by (auto simp: split: prod.splits)
    subgoal by (auto simp: split: prod.splits)
    subgoal by (auto simp: split: prod.splits)
    subgoal by (auto simp: split: prod.splits)
    subgoal by auto
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal by (auto simp: split: prod.splits)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


sepref_register lit_redundant_rec_wl_lookup conflict_min_cach_set_removable_l
  get_propagation_reason_pol

declare get_propagation_reason_code.refine[sepref_fr_rules]

(* TODO fst (lst last) \<le> uint_max? *)
sepref_definition lit_redundant_rec_wl_lookup_code
  is \<open>uncurry5 (isa_lit_redundant_rec_wl_lookup)\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), analysis), lbd). True]\<^sub>a
      trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a (uint32_nat_assn *a array_assn option_bool_assn)\<^sup>k *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a analyse_refinement_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn *a analyse_refinement_assn *a bool_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim] image_image[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms[intro] length_rll_def[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro] nth_rll_def[simp]
    fmap_length_rll_u_def[simp]
    fmap_length_rll_def[simp]
  unfolding isa_lit_redundant_rec_wl_lookup_def
    conflict_min_cach_set_removable_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric] PR_CONST_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    butlast_nonresizing_def[symmetric]
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl.fold_custom_empty)+
  apply (rewrite at \<open>op_arl_empty\<close> annotate_assn[where A=analyse_refinement_assn])
  unfolding nth_rll_def[symmetric] length_rll_def[symmetric]
    fmap_rll_def[symmetric]
    fmap_length_rll_def[symmetric]
  by sepref (* slow *)

declare lit_redundant_rec_wl_lookup_code.refine[sepref_fr_rules]

sepref_definition lit_redundant_rec_wl_lookup_fast_code
  is \<open>uncurry5 (isa_lit_redundant_rec_wl_lookup)\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), analysis), lbd). length NU \<le> uint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a (uint32_nat_assn *a array_assn option_bool_assn)\<^sup>k *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a analyse_refinement_fast_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn *a analyse_refinement_fast_assn *a bool_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim] image_image[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms[intro] length_rll_def[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro] nth_rll_def[simp]
    fmap_length_rll_u_def[simp]
    fmap_length_rll_def[simp]
  unfolding isa_lit_redundant_rec_wl_lookup_def
    conflict_min_cach_set_removable_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric] PR_CONST_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    butlast_nonresizing_def[symmetric]
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl.fold_custom_empty)+
  apply (rewrite at \<open>op_arl_empty\<close> annotate_assn[where A=analyse_refinement_fast_assn])
  apply (rewrite at \<open>_ @ [(_, \<hole>)]\<close> one_uint64_nat_def[symmetric])+

  unfolding nth_rll_def[symmetric] length_rll_def[symmetric]
    fmap_rll_def[symmetric]
    fmap_length_rll_def[symmetric]
  unfolding nth_rll_def[symmetric] length_rll_def[symmetric]
    fmap_rll_def[symmetric]
    fmap_length_rll_def[symmetric]
    zero_uint32_nat_def[symmetric]
    fmap_rll_u_def[symmetric]
    nat_of_uint64_conv_def
  by sepref (* slow *)

declare lit_redundant_rec_wl_lookup_fast_code.refine[sepref_fr_rules]


lemma iterate_over_conflict_spec:
  fixes D :: \<open>'v clause\<close>
  assumes \<open>NU + NUE \<Turnstile>pm add_mset K D\<close> and dist: \<open>distinct_mset D\<close>
  shows
    \<open>iterate_over_conflict K M NU NUE D \<le> \<Down> Id (SPEC(\<lambda>D'. D' \<subseteq># D \<and>
       NU + NUE \<Turnstile>pm add_mset K D'))\<close>
proof -
  define I' where
    \<open>I' = (\<lambda>(E:: 'v clause, f :: 'v clause).
            E \<subseteq># D \<and> NU + NUE \<Turnstile>pm add_mset K E \<and> distinct_mset E \<and> distinct_mset f)\<close>

  have init_I': \<open>I' (D, D)\<close>
    using \<open>NU + NUE \<Turnstile>pm add_mset K D\<close> dist unfolding I'_def highest_lit_def by auto

  have red: \<open>is_literal_redundant_spec K NU NUE a x
      \<le> SPEC (\<lambda>red. (if \<not> red then RETURN (a, remove1_mset x aa)
               else RETURN (remove1_mset x a, remove1_mset x aa))
              \<le> SPEC (\<lambda>s'. iterate_over_conflict_inv M D s' \<and> I' s' \<and>
                 (s', s) \<in> measure (\<lambda>(D, D'). size D')))\<close>
    if
      \<open>iterate_over_conflict_inv M D s\<close> and
      \<open>I' s\<close> and
      \<open>case s of (D, D') \<Rightarrow> D' \<noteq> {#}\<close> and
      \<open>s = (a, aa)\<close> and
      \<open>x \<in># aa\<close>
    for s a b aa x
  proof -
    have \<open>x \<in># a\<close> \<open>distinct_mset aa\<close>
      using that
      by (auto simp: I'_def highest_lit_def
          eq_commute[of \<open>get_level _ _\<close>] iterate_over_conflict_inv_def
          get_maximum_level_add_mset add_mset_eq_add_mset
          dest!:  split: option.splits if_splits)
    then show ?thesis
      using that
      by (auto simp: is_literal_redundant_spec_def iterate_over_conflict_inv_def
          I'_def size_mset_remove1_mset_le_iff remove1_mset_add_mset_If
          intro: mset_le_subtract)
  qed

  show ?thesis
    unfolding iterate_over_conflict_def
    apply (refine_vcg WHILEIT_rule_stronger_inv[where
       R = \<open>measure (\<lambda>(D :: 'v clause, D':: 'v clause).
              size D')\<close> and
          I' = I'])
    subgoal by auto
    subgoal by (auto simp: iterate_over_conflict_inv_def highest_lit_def)
    subgoal by (rule init_I')
    subgoal by (rule red)
    subgoal unfolding I'_def iterate_over_conflict_inv_def by auto
    subgoal unfolding I'_def iterate_over_conflict_inv_def by auto
    done
qed

end

lemma
  fixes D :: \<open>nat clause\<close> and s and s' and NU :: \<open>nat clauses_l\<close> and
    S :: \<open>nat twl_st_wl\<close> and S' :: \<open>nat twl_st_l\<close> and S'' :: \<open>nat twl_st\<close>
  defines
    \<open>S''' \<equiv> state\<^sub>W_of S''\<close>
  defines
    \<open>M \<equiv> get_trail_wl S\<close> and
    NU: \<open>NU \<equiv> get_clauses_wl S\<close> and
    NU'_def: \<open>NU' \<equiv> mset `# ran_mf NU\<close> and
    NUE: \<open>NUE \<equiv> get_unit_learned_clss_wl S + get_unit_init_clss_wl S\<close> and
    M': \<open>M' \<equiv> trail S'''\<close>
  assumes
    S_S': \<open>(S, S') \<in> state_wl_l None\<close> and
    S'_S'': \<open>(S', S'') \<in> twl_st_l None\<close> and
    D'_D: \<open>mset (tl outl) = D\<close> and
    M_D: \<open>M \<Turnstile>as CNot D\<close> and
    dist_D: \<open>distinct_mset D\<close> and
    tauto: \<open>\<not>tautology D\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<close> and
    struct_invs: \<open>twl_struct_invs S''\<close> and
    add_inv: \<open>twl_list_invs S'\<close> and
    cach_init: \<open>conflict_min_analysis_inv M' s' (NU' + NUE) D\<close> and
    NU_P_D: \<open>NU' + NUE \<Turnstile>pm add_mset K D\<close> and
    lits_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> D\<close> and
    K: \<open>K = outl ! 0\<close> and
    outl_nempty: \<open>outl \<noteq> []\<close> and
    \<open>isasat_input_bounded \<A>\<close>
  shows
    \<open>minimize_and_extract_highest_lookup_conflict \<A> M NU D s' lbd outl \<le>
       \<Down> ({((E, s, outl), E'). E = E' \<and> mset (tl outl) = E \<and> outl!0 = K \<and>
               E' \<subseteq># D})
         (SPEC (\<lambda>D'. D' \<subseteq># D \<and> NU' + NUE \<Turnstile>pm add_mset K D'))\<close>
proof -
  show ?thesis
    apply (rule order.trans)
     apply (rule minimize_and_extract_highest_lookup_conflict_iterate_over_conflict[OF
          assms(7-21)[unfolded assms(1-8)],
          unfolded assms(1-8)[symmetric]])
    apply (rule order.trans)
     apply (rule ref_two_step'[OF iterate_over_conflict_spec[OF NU_P_D dist_D]])
    by (auto simp: conc_fun_RES)
qed

sepref_definition delete_index_and_swap_code
  is \<open>uncurry (RETURN oo delete_index_and_swap)\<close>
  :: \<open>[\<lambda>(xs, i). i < length xs]\<^sub>a
      (arl_assn unat_lit_assn)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> arl_assn unat_lit_assn\<close>
  unfolding delete_index_and_swap.simps
  by sepref

declare delete_index_and_swap_code.refine[sepref_fr_rules]


lemma lookup_conflict_size_hnr[sepref_fr_rules]:
  \<open>(return o fst, RETURN o lookup_conflict_size) \<in> lookup_clause_rel_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare sep_auto

lemma single_replicate: \<open>[C] = op_list_append [] C\<close>
  by auto

lemma (in -) lookup_conflict_upd_None_RETURN_def:
  \<open>RETURN oo lookup_conflict_upd_None = (\<lambda>(n, xs) i. RETURN (n- one_uint32_nat, xs [i := NOTIN]))\<close>
  by (auto intro!: ext)

sepref_definition (in -)lookup_conflict_upd_None_code
  is \<open>uncurry (RETURN oo lookup_conflict_upd_None)\<close>
  :: \<open>[\<lambda>((n, xs), i). i < length xs \<and> n > 0]\<^sub>a
     lookup_clause_rel_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> lookup_clause_rel_assn\<close>
  unfolding lookup_conflict_upd_None_RETURN_def fast_minus_def[symmetric]
  by sepref

declare lookup_conflict_upd_None_code.refine[sepref_fr_rules]

definition isa_literal_redundant_wl_lookup ::
    "trail_pol \<Rightarrow> arena \<Rightarrow> lookup_clause_rel \<Rightarrow> conflict_min_cach_l
           \<Rightarrow> nat literal \<Rightarrow> lbd \<Rightarrow> (conflict_min_cach_l \<times> (nat \<times> nat) list \<times> bool) nres"
where
  \<open>isa_literal_redundant_wl_lookup M NU D cach L lbd = do {
     ASSERT(get_level_pol_pre (M, L));
     ASSERT(conflict_min_cach_l_pre (cach, atm_of L));
     if get_level_pol M L = 0 \<or> conflict_min_cach_l cach (atm_of L) = SEEN_REMOVABLE
     then RETURN (cach, [], True)
     else if conflict_min_cach_l cach (atm_of L) = SEEN_FAILED
     then RETURN (cach, [], False)
     else do {
       C \<leftarrow> get_propagation_reason_pol M (-L);
       case C of
         Some C \<Rightarrow> isa_lit_redundant_rec_wl_lookup M NU D cach [(C, 1)] lbd
       | None \<Rightarrow> do {
           RETURN (cach, [], False)
       }
     }
  }\<close>

lemma in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>nD[intro]: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> atm_of L \<in># \<A>\<close>
  using in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n by blast

lemma isa_literal_redundant_wl_lookup_literal_redundant_wl_lookup:
  \<open>(uncurry5 isa_literal_redundant_wl_lookup, uncurry5 (literal_redundant_wl_lookup \<A>)) \<in>
    [\<lambda>(((((_, N), _), _), _), _). literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> ((mset \<circ> fst) `# ran_m N)]\<^sub>f
     trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f lookup_clause_rel \<A> \<times>\<^sub>f cach_refinement \<A>
        \<times>\<^sub>f Id  \<times>\<^sub>f Id \<rightarrow>
      \<langle>cach_refinement \<A> \<times>\<^sub>r Id \<times>\<^sub>r bool_rel\<rangle>nres_rel\<close>
proof -
  have [intro!]: \<open>(x2g, x') \<in> cach_refinement \<A> \<Longrightarrow>
    (x2g, x') \<in> cach_refinement (fold_mset (+) \<A> {#})\<close> for x2g x'
    by auto
  have [refine0]: \<open>get_propagation_reason_pol M (- L)
    \<le> \<Down> (\<langle>Id\<rangle>option_rel)
       (get_propagation_reason M' (- L'))\<close>
    if \<open>(M, M') \<in> trail_pol \<A>\<close> and \<open>(L, L') \<in> Id\<close> and \<open>-L \<in> lits_of_l M'\<close>
    for M M' L L'
    using that get_propagation_reason_pol[of \<A>, THEN fref_to_Down_curry, of M' \<open>-L'\<close> M \<open>-L\<close>] by auto

  show ?thesis
    unfolding isa_literal_redundant_wl_lookup_def literal_redundant_wl_lookup_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      isa_lit_redundant_rec_wl_lookup_lit_redundant_rec_wl_lookup[of \<A> vdom, THEN fref_to_Down_curry5])
    subgoal
      by (rule get_level_pol_pre) auto
    subgoal by (rule conflict_min_cach_l_pre) auto
    subgoal
      by (auto simp: get_level_get_level_pol  in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>nD
            nth_conflict_min_cach[THEN fref_to_Down_unRET_uncurry_Id])
	(subst (asm) nth_conflict_min_cach[THEN fref_to_Down_unRET_uncurry_Id]; auto)+
    subgoal by auto
    subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i
      by (subst nth_conflict_min_cach[THEN fref_to_Down_unRET_uncurry_Id];
            auto simp del: conflict_min_cach_def)
        (auto simp: get_level_get_level_pol in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>nD)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

sepref_register isa_lit_redundant_rec_wl_lookup
sepref_definition literal_redundant_wl_lookup_code
  is \<open>uncurry5 isa_literal_redundant_wl_lookup\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), L), lbd). True]\<^sub>a
      trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>k *\<^sub>a
      cach_refinement_l_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn *a analyse_refinement_assn *a bool_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro]
  unfolding isa_literal_redundant_wl_lookup_def zero_uint32_nat_def[symmetric] PR_CONST_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl.fold_custom_empty)+
  unfolding single_replicate
  unfolding arl.fold_custom_empty
  by sepref

declare literal_redundant_wl_lookup_code.refine[sepref_fr_rules]

sepref_definition literal_redundant_wl_lookup_fast_code
  is \<open>uncurry5 isa_literal_redundant_wl_lookup\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), L), lbd). length NU \<le> uint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>k *\<^sub>a
      cach_refinement_l_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn *a analyse_refinement_fast_assn *a bool_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro]
  unfolding isa_literal_redundant_wl_lookup_def zero_uint32_nat_def[symmetric] PR_CONST_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl.fold_custom_empty)+
  unfolding single_replicate one_uint64_nat_def[symmetric]
  unfolding arl.fold_custom_empty
  by sepref

declare literal_redundant_wl_lookup_fast_code.refine[sepref_fr_rules]


abbreviation (in -) highest_lit_assn where
  \<open>highest_lit_assn \<equiv> option_assn (unat_lit_assn *a uint32_nat_assn)\<close>

definition (in -) lookup_conflict_remove1 :: \<open>nat literal \<Rightarrow> lookup_clause_rel \<Rightarrow> lookup_clause_rel\<close> where
  \<open>lookup_conflict_remove1 =
     (\<lambda>L (n,xs). (n-1, xs [atm_of L := NOTIN]))\<close>

lemma lookup_conflict_remove1:
  \<open>(uncurry (RETURN oo lookup_conflict_remove1), uncurry (RETURN oo remove1_mset))
   \<in> [\<lambda>(L,C). L \<in># C \<and> -L \<notin># C \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f
     Id \<times>\<^sub>f lookup_clause_rel \<A> \<rightarrow> \<langle>lookup_clause_rel \<A>\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (case_tac y; case_tac x)
  subgoal for x y a b aa ab c
    using mset_as_position_remove[of c b \<open>atm_of aa\<close>]
    by (cases \<open>aa\<close>)
      (auto simp: lookup_clause_rel_def lookup_conflict_remove1_def lookup_clause_rel_atm_in_iff
        minus_notin_trivial2 size_remove1_mset_If in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff minus_notin_trivial
        mset_as_position_in_iff_nth)
   done

definition (in -) lookup_conflict_remove1_pre :: \<open>nat literal \<times> nat \<times> bool option list \<Rightarrow> bool\<close> where
\<open>lookup_conflict_remove1_pre = (\<lambda>(L,(n,xs)). n > 0 \<and> atm_of L < length xs)\<close>

sepref_register lookup_conflict_remove1

sepref_definition conflict_remove1_code
  is \<open>uncurry (RETURN oo lookup_conflict_remove1)\<close>
  :: \<open>[lookup_conflict_remove1_pre]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d \<rightarrow>
     lookup_clause_rel_assn\<close>
  supply [[goals_limit=2]] one_uint32_nat[sepref_fr_rules]
  unfolding lookup_conflict_remove1_def one_uint32_nat_def[symmetric] fast_minus_def[symmetric]
  lookup_conflict_remove1_pre_def
  by sepref

declare conflict_remove1_code.refine[sepref_fr_rules]

definition isa_minimize_and_extract_highest_lookup_conflict
  :: \<open>trail_pol \<Rightarrow> arena \<Rightarrow> lookup_clause_rel \<Rightarrow> conflict_min_cach_l \<Rightarrow> lbd \<Rightarrow>
     out_learned \<Rightarrow> (lookup_clause_rel \<times> conflict_min_cach_l \<times> out_learned) nres\<close>
where
  \<open>isa_minimize_and_extract_highest_lookup_conflict  = (\<lambda>M NU nxs s lbd outl. do {
    (D, _, s, outl) \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(nxs, i, s, outl). length outl \<le> uint32_max\<^esup>
         (\<lambda>(nxs, i, s, outl). i < length outl)
         (\<lambda>(nxs, x, s, outl). do {
            ASSERT(x < length outl);
            let L = outl ! x;
            (s', _, red) \<leftarrow> isa_literal_redundant_wl_lookup M NU nxs s L lbd;
            if \<not>red
            then RETURN (nxs, x+1, s', outl)
            else do {
               ASSERT(lookup_conflict_remove1_pre (L, nxs));
               RETURN (lookup_conflict_remove1 L nxs, x, s',  delete_index_and_swap outl x)
            }
         })
         (nxs, one_uint32_nat, s, outl);
     RETURN (D, s, outl)
  })\<close>


lemma isa_minimize_and_extract_highest_lookup_conflict_minimize_and_extract_highest_lookup_conflict:
  \<open>(uncurry5 isa_minimize_and_extract_highest_lookup_conflict,
    uncurry5 (minimize_and_extract_highest_lookup_conflict \<A>)) \<in>
    [\<lambda>(((((_, N), D), _), _), _). literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> ((mset \<circ> fst) `# ran_m N) \<and>
       \<not>tautology D]\<^sub>f
     trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f lookup_clause_rel \<A> \<times>\<^sub>f
         cach_refinement \<A> \<times>\<^sub>f Id  \<times>\<^sub>f Id \<rightarrow>
      \<langle>lookup_clause_rel \<A> \<times>\<^sub>r cach_refinement \<A> \<times>\<^sub>r Id\<rangle>nres_rel\<close>
proof -
  have init: \<open>((x2f, one_uint32_nat, x2g, x2i), x2a::nat literal multiset, one_uint32_nat, x2b, x2d)
        \<in> lookup_clause_rel \<A> \<times>\<^sub>r Id \<times>\<^sub>r cach_refinement \<A> \<times>\<^sub>r Id \<close>
    if
      \<open>(x, y)
      \<in> trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f lookup_clause_rel \<A> \<times>\<^sub>f
        cach_refinement \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id\<close> and
      \<open>x1c = (x1d, x2)\<close> and
      \<open>x1b = (x1c, x2a)\<close> and
      \<open>x1a = (x1b, x2b)\<close> and
      \<open>x1 = (x1a, x2c)\<close> and
      \<open>y = (x1, x2d)\<close> and
      \<open>x1h = (x1i, x2e)\<close> and
      \<open>x1g = (x1h, x2f)\<close> and
      \<open>x1f = (x1g, x2g)\<close> and
      \<open>x1e = (x1f, x2h)\<close> and
      \<open>x = (x1e, x2i)\<close>
    for x y x1 x1a x1b x1c x1d x2 x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
        x2h x2i and
        x2a
  proof -
    show ?thesis
      using that by auto
  qed
  thm isa_literal_redundant_wl_lookup_literal_redundant_wl_lookup[of \<A> vdom, THEN fref_to_Down_curry5]
  show ?thesis
    unfolding isa_minimize_and_extract_highest_lookup_conflict_def uncurry_def
      minimize_and_extract_highest_lookup_conflict_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      isa_literal_redundant_wl_lookup_literal_redundant_wl_lookup[of \<A> vdom, THEN fref_to_Down_curry5])
    apply (rule init; assumption)
    subgoal by (auto simp: minimize_and_extract_highest_lookup_conflict_inv_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal
      by (auto simp: lookup_conflict_remove1_pre_def lookup_clause_rel_def atms_of_def
        minimize_and_extract_highest_lookup_conflict_inv_def)
    subgoal
      by (auto simp: minimize_and_extract_highest_lookup_conflict_inv_def
        intro!: lookup_conflict_remove1[THEN fref_to_Down_unRET_uncurry]
        simp: nth_in_set_tl delete_from_lookup_conflict_pre_def
        dest!: in_set_takeD)
    subgoal by auto
    done
qed

(* TODO Check if the size is actually used anywhere *)

sepref_register isa_minimize_and_extract_highest_lookup_conflict isa_literal_redundant_wl_lookup
sepref_definition minimize_and_extract_highest_lookup_conflict_code
  is \<open>uncurry5 (isa_minimize_and_extract_highest_lookup_conflict)\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), lbd), outl). True]\<^sub>a
       trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      lookup_clause_rel_assn *a cach_refinement_l_assn *a out_learned_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    minimize_and_extract_highest_lookup_conflict_inv_def[simp]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max'[intro] length_u_hnr[sepref_fr_rules]
    array_set_hnr_u[sepref_fr_rules]
  unfolding isa_minimize_and_extract_highest_lookup_conflict_def zero_uint32_nat_def[symmetric]
    one_uint32_nat_def[symmetric] PR_CONST_def
    length_u_def[symmetric] minimize_and_extract_highest_lookup_conflict_inv_def
  by sepref

declare minimize_and_extract_highest_lookup_conflict_code.refine[sepref_fr_rules]

sepref_definition minimize_and_extract_highest_lookup_conflict_fast_code
  is \<open>uncurry5 isa_minimize_and_extract_highest_lookup_conflict\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), lbd), outl). length NU \<le> uint64_max]\<^sub>a
       trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      lookup_clause_rel_assn *a cach_refinement_l_assn *a out_learned_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    minimize_and_extract_highest_lookup_conflict_inv_def[simp]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max'[intro] length_u_hnr[sepref_fr_rules]
    array_set_hnr_u[sepref_fr_rules]
  unfolding isa_minimize_and_extract_highest_lookup_conflict_def zero_uint32_nat_def[symmetric]
    one_uint32_nat_def[symmetric] PR_CONST_def
    length_u_def[symmetric] minimize_and_extract_highest_lookup_conflict_inv_def
  by sepref

declare minimize_and_extract_highest_lookup_conflict_fast_code.refine[sepref_fr_rules]

definition set_empty_conflict_to_none where
  \<open>set_empty_conflict_to_none D = None\<close>

definition set_lookup_empty_conflict_to_none where
  \<open>set_lookup_empty_conflict_to_none = (\<lambda>(n, xs). (True, n, xs))\<close>

lemma set_empty_conflict_to_none_hnr:
  \<open>(RETURN o set_lookup_empty_conflict_to_none, RETURN o set_empty_conflict_to_none) \<in>
     [\<lambda>D. D = {#}]\<^sub>f lookup_clause_rel \<A> \<rightarrow> \<langle>option_lookup_clause_rel \<A>\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def
       set_empty_conflict_to_none_def set_lookup_empty_conflict_to_none_def)

lemma set_lookup_empty_conflict_to_none_hnr[sepref_fr_rules]:
  \<open>(return o set_lookup_empty_conflict_to_none, RETURN o set_lookup_empty_conflict_to_none) \<in>
     lookup_clause_rel_assn\<^sup>d \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  by sepref_to_hoare (sep_auto simp: set_lookup_empty_conflict_to_none_def)

end
