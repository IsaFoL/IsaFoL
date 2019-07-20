theory IsaSAT_Lookup_Conflict
  imports
    IsaSAT_Literals
    Watched_Literals.CDCL_Conflict_Minimisation
    LBD
    IsaSAT_Clauses
    IsaSAT_Watch_List
    IsaSAT_Trail
begin

hide_const Autoref_Fix_Rel.CONSTRAINT


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
       (fold (\<lambda>L xs. xs[atm_of L := Some (is_pos L)]) P xs) [atm_of L := Some (is_pos L)]\<close>
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
    lookup_clause_rel_size: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C \<Longrightarrow> size C \<le> 1 + uint32_max div 2\<close>
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
  then show \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C \<Longrightarrow> size C \<le> 1 + uint32_max div 2\<close>
    using simple_clss_size_upper_div2[of \<A> \<open>C\<close>] \<open>\<not>tautology C\<close> bounded by auto
qed


definition option_bool_rel :: \<open>(bool \<times> 'a option) set\<close> where
  \<open>option_bool_rel = {(b, x). b \<longleftrightarrow> \<not>(is_None x)}\<close>


definition NOTIN :: \<open>bool option\<close> where
  [simp]: \<open>NOTIN = None\<close>

definition ISIN :: \<open>bool \<Rightarrow> bool option\<close> where
  [simp]: \<open>ISIN b = Some b\<close>

definition is_NOTIN :: \<open>bool option \<Rightarrow> bool\<close> where
  [simp]: \<open>is_NOTIN x \<longleftrightarrow> x = NOTIN\<close>

lemma is_NOTIN_alt_def:
  \<open>is_NOTIN x \<longleftrightarrow> is_None x\<close>
  by (auto split: option.splits)

definition option_lookup_clause_rel where
\<open>option_lookup_clause_rel \<A> = {((b,(n,xs)), C). b = (C = None) \<and>
   (C = None \<longrightarrow> ((n,xs), {#}) \<in> lookup_clause_rel \<A>) \<and>
   (C \<noteq> None \<longrightarrow> ((n,xs), the C) \<in> lookup_clause_rel \<A>)}
   \<close>

lemma option_lookup_clause_rel_lookup_clause_rel_iff:
   \<open>((False, (n, xs)), Some C) \<in> option_lookup_clause_rel \<A> \<longleftrightarrow>
   ((n, xs), C) \<in> lookup_clause_rel \<A>\<close>
   unfolding option_lookup_clause_rel_def by auto


type_synonym (in -) conflict_option_rel = \<open>bool \<times> nat \<times> bool option list\<close>

definition (in -) lookup_clause_assn_is_None :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>lookup_clause_assn_is_None = (\<lambda>(b, _, _). b)\<close>

lemma lookup_clause_assn_is_None_is_None:
  \<open>(RETURN o lookup_clause_assn_is_None, RETURN o is_None) \<in>
   option_lookup_clause_rel \<A> \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
   (auto simp: option_lookup_clause_rel_def lookup_clause_assn_is_None_def split: option.splits)

definition (in -) lookup_clause_assn_is_empty :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>lookup_clause_assn_is_empty = (\<lambda>(_, n, _). n = 0)\<close>

lemma lookup_clause_assn_is_empty_is_empty:
  \<open>(RETURN o lookup_clause_assn_is_empty, RETURN o (\<lambda>D. Multiset.is_empty(the D))) \<in>
  [\<lambda>D. D \<noteq> None]\<^sub>f option_lookup_clause_rel \<A> \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
   (auto simp: option_lookup_clause_rel_def lookup_clause_assn_is_empty_def lookup_clause_rel_def
     Multiset.is_empty_def split: option.splits)


definition size_lookup_conflict :: \<open>_ \<Rightarrow> nat\<close> where
  \<open>size_lookup_conflict = (\<lambda>(_, n, _). n)\<close>

definition size_conflict_wl_heur :: \<open>_ \<Rightarrow> nat\<close> where
  \<open>size_conflict_wl_heur = (\<lambda>(M, N, U, D, _, _, _, _). size_lookup_conflict D)\<close>

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


definition (in -) is_in_lookup_conflict where
  \<open>is_in_lookup_conflict = (\<lambda>(n, xs) L. \<not>is_None (xs ! atm_of L))\<close>

lemma mset_as_position_remove:
  \<open>mset_as_position xs D \<Longrightarrow> L < length xs \<Longrightarrow>
   mset_as_position (xs[L := None]) (remove1_mset (Pos L) (remove1_mset (Neg L) D))\<close>
proof (induction rule: mset_as_position.induct)
  case (empty n)
  then have [simp]: \<open>(replicate n None)[L := None] = replicate n None\<close>
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
     RETURN (n - 1, xs[atm_of L := None])
   })\<close>

lemma delete_from_lookup_conflict_op_mset_delete:
  \<open>(uncurry delete_from_lookup_conflict, uncurry (RETURN oo remove1_mset)) \<in>
      [\<lambda>(L, D). -L \<notin># D \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> L \<in># D]\<^sub>f Id \<times>\<^sub>f lookup_clause_rel \<A> \<rightarrow>
      \<langle>lookup_clause_rel \<A>\<rangle>nres_rel\<close>
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
       n = card_max_lvl M (mset (drop init (Ni)) \<union># the D) \<and>
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
             Suc i \<le> uint32_max \<and> Suc (fst zs) \<le> uint32_max \<and> Suc clvls \<le> uint32_max\<^esup>
       (\<lambda>(i :: nat, clvls, zs, lbd, outl). i < length_uint32_nat D)
       (\<lambda>(i :: nat, clvls, zs, lbd, outl). do {
           ASSERT(i < length_uint32_nat D);
           ASSERT(Suc i \<le> uint32_max);
           let lbd = lbd_write lbd (get_level M (D!i));
           ASSERT(\<not>is_in_lookup_conflict zs (D!i) \<longrightarrow> length outl < uint32_max);
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
     lookup_conflict_merge 0 M (C\<propto>i) xs clvls lbd outl\<close>

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
             Suc (fst zs) \<le> uint32_max \<and> Suc clvls \<le> uint32_max\<^esup>
       (\<lambda>(j :: nat, clvls, zs, lbd, outl). j < i + arena_length N i)
       (\<lambda>(j :: nat, clvls, zs, lbd, outl). do {
           ASSERT(j < length N);
           ASSERT(arena_lit_pre N j);
           ASSERT(get_level_pol_pre (M, arena_lit N j));
	   ASSERT(get_level_pol M (arena_lit N j) \<le> Suc (uint32_max div 2));
           let lbd = lbd_write lbd (get_level_pol M (arena_lit N j));
           ASSERT(atm_of (arena_lit N j) < length (snd zs));
           ASSERT(\<not>is_in_lookup_conflict zs (arena_lit N j) \<longrightarrow> length outl < uint32_max);
           let outl = isa_outlearned_add M (arena_lit N j) zs outl;
           let clvls = isa_clvls_add M (arena_lit N j) zs clvls;
           let zs = add_to_lookup_conflict (arena_lit N j) zs;
           RETURN(Suc j, clvls, zs, lbd, outl)
        })
       (i+init, clvls, xs, lbd, outl);
     RETURN ((False, zs), clvls, lbd, outl)
   })\<close>


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
  from literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[OF bound this \<open>no_dup M\<close>]
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
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g'
      using valid i literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<A> N i x1] lits
      by (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff arena_lifting ac_simps get_level_get_level_pol[OF M'M]
        isa_outlearned_add_outlearned_add[OF M'M] isa_clvls_add_clvls_add[OF M'M])
    subgoal using bxs by (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff get_level_get_level_pol[OF M'M])
    done
qed

lemma (in -) arena_is_valid_clause_idx_le_uint64_max:
  \<open>arena_is_valid_clause_idx be bd \<Longrightarrow>
    length be \<le> uint64_max \<Longrightarrow>
   bd + arena_length be bd \<le> uint64_max\<close>
  \<open>arena_is_valid_clause_idx be bd \<Longrightarrow> length be \<le> uint64_max \<Longrightarrow>
   bd \<le> uint64_max\<close>
  using arena_lifting(10)[of be _ _ bd]
  by (fastforce simp: arena_lifting arena_is_valid_clause_idx_def)+


definition isa_set_lookup_conflict_aa where
  \<open>isa_set_lookup_conflict_aa = isa_lookup_conflict_merge 0\<close>

definition isa_set_lookup_conflict_aa_pre where
  \<open>isa_set_lookup_conflict_aa_pre =
    (\<lambda>((((((M, N), i), (_, xs)), _), _), out). i < length N)\<close>

lemma lookup_conflict_merge'_spec:
  assumes
    o: \<open>((b, n, xs), Some C) \<in> option_lookup_clause_rel \<A>\<close> and
    dist: \<open>distinct D\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset D)\<close> and
    tauto: \<open>\<not>tautology (mset D)\<close> and
    lits_C: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C\<close> and
    \<open>clvls = card_max_lvl M C\<close> and
    CD: \<open>\<And>L. L \<in> set (drop init D) \<Longrightarrow> -L \<notin># C\<close> and
    \<open>Suc init \<le> uint32_max\<close> and
    \<open>out_learned M (Some C) outl\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
  shows
    \<open>lookup_conflict_merge init M D (b, n, xs) clvls lbd outl \<le>
      \<Down>(option_lookup_clause_rel \<A> \<times>\<^sub>r Id \<times>\<^sub>r Id)
          (merge_conflict_m_g init M D (Some C))\<close>
     (is \<open>_ \<le>  \<Down> ?Ref ?Spec\<close>)
proof -
  define lbd_upd where
     \<open>lbd_upd lbd i \<equiv> lbd_write lbd (get_level M (D!i))\<close> for lbd i
  let ?D = \<open>drop init D\<close>
  have le_D_le_upper[simp]: \<open>a < length D \<Longrightarrow> Suc (Suc a) \<le> uint32_max\<close> for a
    using simple_clss_size_upper_div2[of \<A> \<open>mset D\<close>] assms by (auto simp: uint32_max_def)
  have Suc_N_uint32_max: \<open>Suc n \<le> uint32_max\<close> and
     size_C_uint32_max: \<open>size C \<le> 1 + uint32_max div 2\<close> and
     clvls: \<open>clvls = card_max_lvl M C\<close> and
     tauto_C: \<open>\<not> tautology C\<close> and
     dist_C: \<open>distinct_mset C\<close> and
     atms_le_xs: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length xs\<close> and
     map: \<open>mset_as_position xs C\<close>
    using assms simple_clss_size_upper_div2[of \<A> C] mset_as_position_distinct_mset[of xs C]
      lookup_clause_rel_not_tautolgy[of n xs C] bounded
    unfolding option_lookup_clause_rel_def lookup_clause_rel_def
    by (auto simp: uint32_max_def)
  then have clvls_uint32_max: \<open>clvls \<le> 1 + uint32_max div 2\<close>
    using size_filter_mset_lesseq[of \<open>\<lambda>L. get_level M L = count_decided M\<close> C]
    unfolding uint32_max_def card_max_lvl_def by linarith
  have [intro]: \<open>((b, a, ba), Some C) \<in> option_lookup_clause_rel \<A> \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C \<Longrightarrow>
        Suc (Suc a) \<le> uint32_max\<close> for b a ba C
    using lookup_clause_rel_size[of a ba C, OF _ bounded] by (auto simp: option_lookup_clause_rel_def
        lookup_clause_rel_def uint32_max_def)
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
                     Suc i \<le> uint32_max \<and>
                     Suc (fst zs) \<le> uint32_max \<and>
                     Suc clvls \<le> uint32_max)\<close>
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
  have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (take (a - init) (drop init D)) \<union># C)\<close> for a
   using lits_C lits by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_def
     dest!: in_set_takeD in_set_dropD)
  then have size_outl_le: \<open>size (mset (take (a - init) (drop init D)) \<union># C) \<le> Suc uint32_max div 2\<close> if \<open>a \<ge> init\<close> for a
    using simple_clss_size_upper_div2[OF bounded, of \<open>mset (take (a - init) (drop init D)) \<union># C\<close>]
       tauto_C'[OF that] \<open>distinct_mset C\<close> dist_D
    by (auto simp: uint32_max_def)

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
      a_uint32_max: \<open>Suc a \<le> uint32_max\<close>
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
    then have [simp]: \<open>Suc (Suc aa) \<le> uint32_max\<close> \<open>Suc aa \<le> uint32_max\<close>
      using size_C_uint32_max lits a_init
      simple_clss_size_upper_div2[of \<A> \<open>remdups_mset (?C' a)\<close>, OF bounded]
      unfolding uint32_max_def aa[symmetric]
      by (auto simp: tauto_C')
    have [simp]: \<open>length b = length xs\<close>
      using I unfolding I_def by simp_all

    have ab_upper: \<open>Suc (Suc ab) \<le> uint32_max\<close>
      using simple_clss_size_upper_div2[OF bounded, of \<open>remdups_mset (?C' a)\<close>]
      lookup_clause_rel_not_tautolgy[OF cr bounded] a_le_D lits mset_as_position_distinct_mset[OF map]
      unfolding ab literals_are_in_\<L>\<^sub>i\<^sub>n_remdups uint32_max_def by auto
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
      assume \<open>- D ! a \<in> set (take (a - init) (drop init D))\<close>
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

  have outl_le: \<open>length bc < uint32_max\<close>
    if
      \<open>I x2 s\<close> and
      \<open>I' s\<close> and
      \<open>s = (a, ba)\<close> and
      \<open>ba = (aa, baa)\<close> and
      \<open>baa = (ab, bb)\<close> and
      \<open>bb = (ac, bc)\<close> for x1 x2 s a ba aa baa ab bb ac bc
  proof -
    have \<open>mset (tl bc) \<subseteq># (remdups_mset (mset (take (a -init) (drop init D)) + C))\<close> and \<open>init \<le> a\<close>
      using that by (auto simp: I_def I'_def lookup_conflict_merge'_step_def Let_def out_learned_def)
    from size_mset_mono[OF this(1)] this(2) show ?thesis using size_outl_le[of a] dist_C dist_D
      by (auto simp: uint32_max_def distinct_mset_rempdups_union_mset)
  qed
  show confl: \<open>lookup_conflict_merge init M D (b, n, xs) clvls lbd outl
    \<le> \<Down> ?Ref (merge_conflict_m_g init M D (Some C))\<close>
    supply [[goals_limit=1]]
    unfolding resolve_lookup_conflict_aa_def lookup_conflict_merge_def
    distinct_mset_rempdups_union_mset[OF dist_D dist_CD] I_def[symmetric] conc_fun_SPEC
    lbd_upd_def[symmetric] Let_def length_uint32_nat_def merge_conflict_m_g_def
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(j, _). length D - j)\<close> and
          I' = I'])
    subgoal by auto
    subgoal
      using clvls_uint32_max Suc_N_uint32_max \<open>Suc init \<le> uint32_max\<close>
      unfolding uint32_max_def I_def by auto
    subgoal using assms
      unfolding lookup_conflict_merge'_step_def Let_def option_lookup_clause_rel_def I'_def
      by (auto simp add: uint32_max_def lookup_conflict_merge'_step_def option_lookup_clause_rel_def)
    subgoal by auto
    subgoal unfolding I_def by fast
    subgoal for x1 x2 s a ba aa baa ab bb ac bc by (rule outl_le)
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
      by (auto simp: lookup_conflict_merge_normalise uint32_max_def merge_conflict_m_g_def)
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
    by (auto intro: H[OF that(1-7,10)])
  show ?thesis
    unfolding lookup_conflict_merge_def uncurry_def
    by (intro nres_relI WB_More_Refinement.frefI) (auto intro!: H)
qed

definition merge_conflict_m_pre where
  \<open>merge_conflict_m_pre \<A> =
  (\<lambda>((((((M, N), i), xs), clvls), lbd), out). i \<in># dom_m N \<and> xs \<noteq> None \<and> distinct (N \<propto> i) \<and>
       \<not>tautology (mset (N \<propto> i)) \<and>
       (\<forall>L \<in> set (tl (N \<propto> i)). - L \<notin># the xs) \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (the xs) \<and> clvls = card_max_lvl M (the xs) \<and>
       out_learned M xs out \<and> no_dup M \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N) \<and>
       isasat_input_bounded \<A>)\<close>

definition isa_resolve_merge_conflict_gt2 where
  \<open>isa_resolve_merge_conflict_gt2 = isa_lookup_conflict_merge 1\<close>

lemma isa_resolve_merge_conflict_gt2:
  \<open>(uncurry6 isa_resolve_merge_conflict_gt2, uncurry6 merge_conflict_m) \<in>
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
      by (auto simp: lookup_conflict_merge_normalise uint32_max_def merge_conflict_m_g_def
         drop_Suc)
  qed

  have H2: \<open>isa_resolve_merge_conflict_gt2 M' arena i (b, n, xs) clvls lbd outl
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
    unfolding isa_resolve_merge_conflict_gt2_def
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


lemma lookup_clause_rel_exists_le_uint32_max:
  assumes ocr: \<open>((n, xs), D) \<in> lookup_clause_rel \<A>\<close> and \<open>n > 0\<close> and
    le_i: \<open>\<forall>k<i. xs ! k = None\<close> and lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> D\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
  shows
    \<open>\<exists>j. j \<ge> i \<and> j < length xs \<and> j < uint32_max \<and> xs ! j \<noteq> None\<close>
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
  then have \<open>nat_of_lit ?L \<le> uint32_max\<close>
    using lits bounded
    by (auto 5 5 dest!: multi_member_split[of _ D]
        simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset split: if_splits)
  then have \<open>j < uint32_max\<close>
    by (auto simp: uint32_max_def split: if_splits)
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
    length outl \<le> uint32_max \<and> mset (tl outl) = D \<and> outl \<noteq> [] \<and> i \<ge> 1)\<close>

type_synonym 'v conflict_highest_conflict = \<open>('v literal \<times> nat) option\<close>

definition (in -) atm_in_conflict where
  \<open>atm_in_conflict L D \<longleftrightarrow> L \<in> atms_of D\<close>

definition atm_in_conflict_lookup :: \<open>nat \<Rightarrow> lookup_clause_rel \<Rightarrow> bool\<close> where
  \<open>atm_in_conflict_lookup = (\<lambda>L (_, xs). xs ! L \<noteq> None)\<close>

definition atm_in_conflict_lookup_pre  :: \<open>nat \<Rightarrow> lookup_clause_rel \<Rightarrow> bool\<close> where
\<open>atm_in_conflict_lookup_pre L xs \<longleftrightarrow> L < length (snd xs)\<close>

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
     ASSERT(length sup \<le> 1 + uint32_max div 2);
     RETURN (cach[L := SEEN_REMOVABLE], if cach ! L = SEEN_UNKNOWN then sup @ [L] else sup)
   })\<close>

definition (in -) conflict_min_cach :: \<open>nat conflict_min_cach \<Rightarrow> nat \<Rightarrow> minimize_status\<close> where
  [simp]: \<open>conflict_min_cach cach L = cach L\<close>


definition lit_redundant_reason_stack2
  :: \<open>'v literal \<Rightarrow> 'v clauses_l \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> bool)\<close> where
\<open>lit_redundant_reason_stack2 L NU C' =
  (if length (NU \<propto> C') > 2 then (C', 1, False)
  else if NU \<propto> C' ! 0 = L then (C', 1, False)
  else (C', 0, True))\<close>

definition ana_lookup_rel
  :: \<open>nat clauses_l \<Rightarrow> ((nat \<times> nat \<times> bool) \<times> (nat \<times> nat \<times> nat \<times> nat)) set\<close>
where
\<open>ana_lookup_rel NU = {((C, i, b), (C', k', i', len')).
  C = C' \<and> k' = (if b then 1 else 0) \<and> i = i' \<and>
  len' = (if b then 1 else length (NU \<propto> C))}\<close>

lemma ana_lookup_rel_alt_def:
  \<open>((C, i, b), (C', k', i', len')) \<in> ana_lookup_rel NU \<longleftrightarrow>
  C = C' \<and> k' = (if b then 1 else 0) \<and> i = i' \<and>
  len' = (if b then 1 else length (NU \<propto> C))\<close>
  unfolding ana_lookup_rel_def
  by auto

abbreviation ana_lookups_rel where
  \<open>ana_lookups_rel NU \<equiv> \<langle>ana_lookup_rel NU\<rangle>list_rel\<close>

definition ana_lookup_conv :: \<open>nat clauses_l \<Rightarrow> (nat \<times> nat \<times> bool) \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)\<close> where
\<open>ana_lookup_conv NU = (\<lambda>(C, i, b). (C, (if b then 1 else 0), i, (if b then 1 else length (NU \<propto> C))))\<close>

definition get_literal_and_remove_of_analyse_wl2
   :: \<open>'v clause_l \<Rightarrow> (nat \<times> nat \<times> bool) list \<Rightarrow> 'v literal \<times> (nat \<times> nat \<times> bool) list\<close> where
  \<open>get_literal_and_remove_of_analyse_wl2 C analyse =
    (let (i, j, b) = last analyse in
     (C ! j, analyse[length analyse - 1 := (i, j + 1, b)]))\<close>

definition lit_redundant_rec_wl_inv2 where
  \<open>lit_redundant_rec_wl_inv2 M NU D =
    (\<lambda>(cach, analyse, b). \<exists>analyse'. (analyse, analyse') \<in> ana_lookups_rel NU \<and>
      lit_redundant_rec_wl_inv M NU D (cach, analyse', b))\<close>

definition mark_failed_lits_stack_inv2 where
  \<open>mark_failed_lits_stack_inv2 NU analyse = (\<lambda>cach.
       \<exists>analyse'. (analyse, analyse') \<in> ana_lookups_rel NU \<and>
      mark_failed_lits_stack_inv NU analyse' cach)\<close>

definition lit_redundant_rec_wl_lookup
  :: \<open>nat multiset \<Rightarrow> (nat,nat)ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat clause \<Rightarrow>
     _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (_ \<times> _ \<times> bool) nres\<close>
where
  \<open>lit_redundant_rec_wl_lookup \<A> M NU D cach analysis lbd =
      WHILE\<^sub>T\<^bsup>lit_redundant_rec_wl_inv2 M NU D\<^esup>
        (\<lambda>(cach, analyse, b). analyse \<noteq> [])
        (\<lambda>(cach, analyse, b). do {
            ASSERT(analyse \<noteq> []);
            ASSERT(length analyse \<le> length M);
	    let (C,k, i, len) = ana_lookup_conv NU (last analyse);
            ASSERT(C \<in># dom_m NU);
            ASSERT(length (NU \<propto> C) > k); \<comment> \<open> >= 2 would work too \<close>
            ASSERT (NU \<propto> C ! k \<in> lits_of_l M);
            ASSERT(NU \<propto> C ! k \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>);
	    ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (NU \<propto> C)));
	    ASSERT(length (NU \<propto> C) \<le> Suc (uint32_max div 2));
	    ASSERT(len \<le> length (NU \<propto> C)); \<comment> \<open>makes the refinement easier\<close>
            let C = NU \<propto> C;
            if i \<ge> len
            then
               RETURN(cach (atm_of (C ! k) := SEEN_REMOVABLE), butlast analyse, True)
            else do {
               let (L, analyse) = get_literal_and_remove_of_analyse_wl2 C analyse;
               ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>);
               let b = \<not>level_in_lbd (get_level M L) lbd;
               if (get_level M L = 0 \<or>
                   conflict_min_cach cach (atm_of L) = SEEN_REMOVABLE \<or>
                   atm_in_conflict (atm_of L) D)
               then RETURN (cach, analyse, False)
               else if b \<or> conflict_min_cach cach (atm_of L) = SEEN_FAILED
               then do {
                  ASSERT(mark_failed_lits_stack_inv2 NU analyse cach);
                  cach \<leftarrow> mark_failed_lits_wl NU analyse cach;
                  RETURN (cach, [], False)
               }
               else do {
	          ASSERT(- L \<in> lits_of_l M);
                  C \<leftarrow> get_propagation_reason M (-L);
                  case C of
                    Some C \<Rightarrow> do {
		      ASSERT(C \<in># dom_m NU);
		      ASSERT(length (NU \<propto> C) \<ge> 2);
		      ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (NU \<propto> C)));
                      ASSERT(length (NU \<propto> C) \<le> Suc (uint32_max div 2));
		      RETURN (cach, analyse @ [lit_redundant_reason_stack2 (-L) NU C], False)
		    }
                  | None \<Rightarrow> do {
                      ASSERT(mark_failed_lits_stack_inv2 NU analyse cach);
                      cach \<leftarrow> mark_failed_lits_wl NU analyse cach;
                      RETURN (cach, [], False)
                  }
              }
          }
        })
       (cach, analysis, False)\<close>

lemma lit_redundant_rec_wl_ref_butlast:
  \<open>lit_redundant_rec_wl_ref NU x \<Longrightarrow> lit_redundant_rec_wl_ref NU (butlast x)\<close>
  by (cases x rule: rev_cases)
    (auto simp: lit_redundant_rec_wl_ref_def dest: in_set_butlastD)

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

context
  fixes M D \<A> NU analysis analysis'
  assumes
    M_D: \<open>M \<Turnstile>as CNot D\<close> and
    n_d: \<open>no_dup M\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<close> and
    ana: \<open>(analysis, analysis') \<in> ana_lookups_rel NU\<close> and
    lits_NU: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> ((mset \<circ> fst) `# ran_m NU)\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
begin
lemma ccmin_rel:
  assumes \<open>lit_redundant_rec_wl_inv M NU D (cach, analysis', False)\<close>
  shows \<open>((cach, analysis, False), cach, analysis', False)
         \<in>  {((cach, ana, b), cach', ana', b').
          (ana, ana') \<in> ana_lookups_rel NU \<and>
          b = b' \<and> cach = cach' \<and> lit_redundant_rec_wl_inv M NU D (cach, ana', b)}\<close>
proof -
  show ?thesis using ana assms by auto
qed


context
  fixes x :: \<open>(nat \<Rightarrow> minimize_status) \<times> (nat \<times> nat \<times> bool) list \<times> bool\<close> and
  x' :: \<open>(nat \<Rightarrow> minimize_status) \<times> (nat \<times> nat \<times> nat \<times> nat) list \<times> bool\<close>
  assumes x_x': \<open>(x, x') \<in> {((cach, ana, b), (cach', ana', b')).
     (ana, ana') \<in> ana_lookups_rel NU \<and> b = b' \<and> cach = cach' \<and>
     lit_redundant_rec_wl_inv M NU D (cach, ana', b)}\<close>
begin

lemma ccmin_lit_redundant_rec_wl_inv2:
  assumes \<open>lit_redundant_rec_wl_inv M NU D x'\<close>
  shows \<open>lit_redundant_rec_wl_inv2 M NU D x\<close>
  using x_x' unfolding lit_redundant_rec_wl_inv2_def
  by auto

context
  assumes
    \<open>lit_redundant_rec_wl_inv2 M NU D x\<close> and
    \<open>lit_redundant_rec_wl_inv M NU D x'\<close>
begin

lemma ccmin_cond:
  fixes x1 :: \<open>nat \<Rightarrow> minimize_status\<close> and
    x2 :: \<open>(nat \<times> nat \<times> bool) list \<times> bool\<close> and
    x1a :: \<open>(nat \<times>  nat \<times> bool) list\<close> and
    x2a :: \<open>bool\<close> and x1b :: \<open>nat \<Rightarrow> minimize_status\<close> and
    x2b :: \<open>(nat \<times> nat \<times> nat \<times> nat) list \<times> bool\<close> and
    x1c :: \<open>(nat \<times> nat \<times> nat \<times> nat) list\<close> and x2c :: \<open>bool\<close>
  assumes
    \<open>x2 = (x1a, x2a)\<close>
    \<open>x = (x1, x2)\<close>
    \<open>x2b = (x1c, x2c)\<close>
    \<open>x' = (x1b, x2b)\<close>
  shows \<open>(x1a \<noteq> []) = (x1c \<noteq> [])\<close>
  using assms x_x'
  by auto

end


context
  assumes
    \<open>case x of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
    \<open>case x' of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
    inv2: \<open>lit_redundant_rec_wl_inv2 M NU D x\<close> and
    \<open>lit_redundant_rec_wl_inv M NU D x'\<close>
begin

context
  fixes x1 :: \<open>nat \<Rightarrow> minimize_status\<close> and
  x2 :: \<open>(nat \<times> nat \<times> nat \<times> nat) list \<times> bool\<close> and
  x1a :: \<open>(nat \<times> nat \<times> nat \<times> nat) list\<close> and x2a :: \<open>bool\<close> and
  x1b :: \<open>nat \<Rightarrow> minimize_status\<close> and
  x2b :: \<open>(nat \<times> nat \<times> bool) list \<times> bool\<close> and
  x1c :: \<open>(nat \<times> nat \<times> bool) list\<close> and
  x2c :: \<open>bool\<close>
  assumes st:
    \<open>x2 = (x1a, x2a)\<close>
    \<open>x' = (x1, x2)\<close>
    \<open>x2b = (x1c, x2c)\<close>
    \<open>x = (x1b, x2b)\<close> and
    x1a: \<open>x1a \<noteq> []\<close>
begin

private lemma st:
    \<open>x2 = (x1a, x2a)\<close>
    \<open>x' = (x1, x1a, x2a)\<close>
    \<open>x2b = (x1c, x2a)\<close>
    \<open>x = (x1, x1c, x2a)\<close>
    \<open>x1b = x1\<close>
    \<open>x2c = x2a\<close> and
  x1c: \<open>x1c \<noteq> []\<close>
  using st x_x' x1a by auto

lemma ccmin_nempty:
  shows \<open>x1c \<noteq> []\<close>
  using x_x' x1a
  by (auto simp: st)

context
  notes _[simp] = st
  fixes x1d :: \<open>nat\<close> and x2d :: \<open>nat \<times> nat \<times> nat\<close> and
    x1e :: \<open>nat\<close> and x2e :: \<open>nat \<times> nat\<close> and
    x1f :: \<open>nat\<close> and
    x2f :: \<open>nat\<close> and x1g :: \<open>nat\<close> and
    x2g :: \<open>nat \<times> nat \<times> nat\<close> and
    x1h :: \<open>nat\<close> and
    x2h :: \<open>nat \<times> nat\<close> and
    x1i :: \<open>nat\<close> and
    x2i :: \<open>nat\<close>
  assumes
    ana_lookup_conv: \<open>ana_lookup_conv NU (last x1c) = (x1g, x2g)\<close> and
    last: \<open>last x1a = (x1d, x2d)\<close> and
    dom: \<open>x1d \<in># dom_m NU\<close> and
    le: \<open>x1e < length (NU \<propto> x1d)\<close> and
    in_lits: \<open>NU \<propto> x1d ! x1e \<in> lits_of_l M\<close> and
    st2:
      \<open>x2g = (x1h, x2h)\<close>
      \<open>x2e = (x1f, x2f)\<close>
      \<open>x2d = (x1e, x2e)\<close>
      \<open>x2h = (x1i, x2i)\<close>
begin

private lemma x1g_x1d:
    \<open>x1g = x1d\<close>
    \<open>x1h = x1e\<close>
    \<open>x1i = x1f\<close>
  using st2 last ana_lookup_conv x_x' x1a last
  by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
    auto simp: ana_lookup_conv_def ana_lookup_rel_def
      list_rel_append_single_iff; fail)+

private definition j where
  \<open>j = fst (snd (last x1c))\<close>

private definition b where
  \<open>b = snd (snd (last x1c))\<close>

private lemma last_x1c[simp]:
  \<open>last x1c = (x1d, x1f, b)\<close>
  using inv2 x1a last x_x' unfolding x1g_x1d st j_def b_def st2
  by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
   auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
    lit_redundant_rec_wl_inv_def ana_lookup_rel_def
    lit_redundant_rec_wl_ref_def)

private lemma
  ana: \<open>(x1d, (if b then 1 else 0), x1f, (if b then 1 else length (NU \<propto> x1d))) = (x1d, x1e, x1f, x2i)\<close> and
  st3:
    \<open>x1e = (if b then 1 else 0)\<close>
    \<open>x1f = j\<close>
    \<open>x2f = (if b then 1 else length (NU \<propto> x1d))\<close>
    \<open>x2d = (if b then 1 else 0, j, if b then 1 else length (NU \<propto> x1d))\<close> and
    \<open>j \<le> (if b then 1 else length (NU \<propto> x1d))\<close> and
    \<open>x1d \<in># dom_m NU\<close> and
    \<open>0 < x1d\<close> and
    \<open>(if b then 1 else length (NU \<propto> x1d)) \<le> length (NU \<propto> x1d)\<close> and
    \<open>(if b then 1 else 0) < length (NU \<propto> x1d)\<close> and
    dist: \<open>distinct (NU \<propto> x1d)\<close> and
    tauto: \<open>\<not> tautology (mset (NU \<propto> x1d))\<close>
  subgoal
    using inv2 x1a last x_x' x1c ana_lookup_conv
    unfolding x1g_x1d st j_def b_def st2
    by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
     auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
         lit_redundant_rec_wl_inv_def ana_lookup_rel_def
         lit_redundant_rec_wl_ref_def ana_lookup_conv_def
       simp del: x1c)
  subgoal
    using inv2 x1a last x_x' x1c unfolding x1g_x1d st j_def b_def st2
    by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
     auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
         lit_redundant_rec_wl_inv_def ana_lookup_rel_def
         lit_redundant_rec_wl_ref_def
       simp del: x1c)
  subgoal
    using inv2 x1a last x_x' x1c unfolding x1g_x1d st j_def b_def st2
    by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
     auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
         lit_redundant_rec_wl_inv_def ana_lookup_rel_def
         lit_redundant_rec_wl_ref_def
       simp del: x1c)
  subgoal
    using inv2 x1a last x_x' x1c unfolding x1g_x1d st j_def b_def st2
    by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
     auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
         lit_redundant_rec_wl_inv_def ana_lookup_rel_def
         lit_redundant_rec_wl_ref_def
       simp del: x1c)
  subgoal
    using inv2 x1a last x_x' x1c unfolding x1g_x1d st j_def b_def st2
    by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
     auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
         lit_redundant_rec_wl_inv_def ana_lookup_rel_def
         lit_redundant_rec_wl_ref_def
       simp del: x1c)
  subgoal
    using inv2 x1a last x_x' x1c unfolding x1g_x1d st j_def b_def st2
    by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
     auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
         lit_redundant_rec_wl_inv_def ana_lookup_rel_def
         lit_redundant_rec_wl_ref_def
       simp del: x1c)
  subgoal
    using inv2 x1a last x_x' x1c unfolding x1g_x1d st j_def b_def
    by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
     auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
         lit_redundant_rec_wl_inv_def ana_lookup_rel_def
         lit_redundant_rec_wl_ref_def
       simp del: x1c)
  subgoal
    using inv2 x1a last x_x' x1c unfolding x1g_x1d st j_def b_def
    by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
     auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
         lit_redundant_rec_wl_inv_def ana_lookup_rel_def
         lit_redundant_rec_wl_ref_def
       simp del: x1c)
  subgoal
    using inv2 x1a last x_x' x1c unfolding x1g_x1d st j_def b_def
    by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
     auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
         lit_redundant_rec_wl_inv_def ana_lookup_rel_def
         lit_redundant_rec_wl_ref_def
       simp del: x1c)
  subgoal
    using inv2 x1a last x_x' x1c unfolding x1g_x1d st j_def b_def
    by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
     auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
         lit_redundant_rec_wl_inv_def ana_lookup_rel_def
         lit_redundant_rec_wl_ref_def
       simp del: x1c)
  subgoal
    using inv2 x1a last x_x' x1c unfolding x1g_x1d st j_def b_def
    by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
     auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
         lit_redundant_rec_wl_inv_def ana_lookup_rel_def
         lit_redundant_rec_wl_ref_def
       simp del: x1c)
  subgoal
    using inv2 x1a last x_x' x1c unfolding x1g_x1d st j_def b_def
    by (cases x1a rule: rev_cases; cases x1c rule: rev_cases;
     auto simp: lit_redundant_rec_wl_inv2_def list_rel_append_single_iff
         lit_redundant_rec_wl_inv_def ana_lookup_rel_def
         lit_redundant_rec_wl_ref_def
       simp del: x1c)
  done

lemma ccmin_in_dom:
  shows x1g_dom: \<open>x1g \<in># dom_m NU\<close>
  using dom unfolding x1g_x1d .

lemma ccmin_in_dom_le_length:
  shows \<open>x1h < length (NU \<propto> x1g)\<close>
  using le unfolding x1g_x1d .

lemma ccmin_in_trail:
  shows \<open>NU \<propto> x1g ! x1h \<in> lits_of_l M\<close>
  using in_lits unfolding x1g_x1d .

lemma ccmin_literals_are_in_\<L>\<^sub>i\<^sub>n_NU_x1g:
  shows \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (NU \<propto> x1g))\<close>
  using lits_NU multi_member_split[OF x1g_dom]
  by (auto simp: ran_m_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_add_mset)

lemma ccmin_le_uint32_max:
  \<open>length (NU \<propto> x1g) \<le> Suc (uint32_max div 2)\<close>
  using simple_clss_size_upper_div2[OF bounded ccmin_literals_are_in_\<L>\<^sub>i\<^sub>n_NU_x1g]
    dist tauto unfolding x1g_x1d
  by auto

lemma ccmin_in_all_lits:
  shows \<open>NU \<propto> x1g ! x1h \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF ccmin_literals_are_in_\<L>\<^sub>i\<^sub>n_NU_x1g, of x1h]
  le unfolding x1g_x1d by auto

lemma ccmin_less_length:
  shows \<open>x2i \<le> length (NU \<propto> x1g)\<close>
  using le ana unfolding x1g_x1d st3 by (simp split: if_splits)

lemma ccmin_same_cond:
  shows \<open>(x2i \<le> x1i) = (x2f \<le> x1f)\<close>
  using le ana unfolding x1g_x1d st3 by (simp split: if_splits)
(*TODO Move + remove duplicate *)
lemma list_rel_butlast:
  assumes rel: \<open>(xs, ys) \<in> \<langle>R\<rangle>list_rel\<close>
  shows \<open>(butlast xs, butlast ys) \<in> \<langle>R\<rangle>list_rel\<close>
proof -
  have \<open>length xs = length ys\<close>
    using assms list_rel_imp_same_length by blast
  then show ?thesis
    using rel
    by (induction xs ys rule: list_induct2) (auto split: nat.splits)
qed

lemma ccmin_set_removable:
  assumes
    \<open>x2i \<le> x1i\<close> and
    \<open>x2f \<le> x1f\<close> and \<open>lit_redundant_rec_wl_inv2 M NU D x\<close>
  shows \<open>((x1b(atm_of (NU \<propto> x1g ! x1h) := SEEN_REMOVABLE), butlast x1c, True),
          x1(atm_of (NU \<propto> x1d ! x1e) := SEEN_REMOVABLE), butlast x1a, True)
         \<in> {((cach, ana, b), cach', ana', b').
       (ana, ana') \<in> ana_lookups_rel NU \<and>
       b = b' \<and> cach = cach' \<and> lit_redundant_rec_wl_inv M NU D (cach, ana', b)}\<close>
  using x_x' by (auto simp: x1g_x1d lit_redundant_rec_wl_ref_butlast lit_redundant_rec_wl_inv_def
    dest: list_rel_butlast)

context
  assumes
    le: \<open>\<not> x2i \<le> x1i\<close> \<open>\<not> x2f \<le> x1f\<close>
begin

context
  notes _[simp]= x1g_x1d st2 last
  fixes x1j :: \<open>nat literal\<close> and x2j :: \<open>(nat \<times> nat \<times> nat \<times> nat) list\<close> and
  x1k :: \<open>nat literal\<close> and x2k :: \<open>(nat \<times> nat \<times> bool) list\<close>
  assumes
    rem: \<open>get_literal_and_remove_of_analyse_wl (NU \<propto> x1d) x1a = (x1j, x2j)\<close> and
    rem2:\<open>get_literal_and_remove_of_analyse_wl2 (NU \<propto> x1g) x1c = (x1k, x2k)\<close> and
    \<open>fst (snd (snd (last x2j))) \<noteq> 0\<close> and
    ux1j_M: \<open>- x1j \<in> lits_of_l M\<close>
begin

private lemma confl_min_last: \<open>(last x1c, last x1a) \<in> ana_lookup_rel NU\<close>
  using x1a x1c x_x' rem rem2 last ana_lookup_conv unfolding x1g_x1d st2 b_def st
  by (cases x1c rule: rev_cases; cases x1a rule: rev_cases)
    (auto simp: list_rel_append_single_iff
     get_literal_and_remove_of_analyse_wl_def
    get_literal_and_remove_of_analyse_wl2_def)

private lemma rel: \<open>(x1c[length x1c - Suc 0 := (x1d, Suc x1f, b)], x1a
     [length x1a - Suc 0 := (x1d, x1e, Suc x1f, x2f)])
    \<in> ana_lookups_rel NU\<close>
  using x1a x1c x_x' rem rem2 confl_min_last unfolding x1g_x1d st2 last b_def st
  by (cases x1c rule: rev_cases; cases x1a rule: rev_cases)
    (auto simp: list_rel_append_single_iff
      ana_lookup_rel_alt_def get_literal_and_remove_of_analyse_wl_def
      get_literal_and_remove_of_analyse_wl2_def)

private lemma x1k_x1j: \<open>x1k = x1j\<close> \<open>x1j = NU \<propto> x1d ! x1f\<close> and
  x2k_x2j: \<open>(x2k, x2j) \<in> ana_lookups_rel NU\<close>
  subgoal
    using x1a x1c x_x' rem rem2 confl_min_last unfolding x1g_x1d st2 last b_def st
    by (cases x1c rule: rev_cases; cases x1a rule: rev_cases)
      (auto simp: list_rel_append_single_iff
	ana_lookup_rel_alt_def get_literal_and_remove_of_analyse_wl_def
	get_literal_and_remove_of_analyse_wl2_def)
  subgoal
    using x1a x1c x_x' rem rem2 confl_min_last unfolding x1g_x1d st2 last b_def st
    by (cases x1c rule: rev_cases; cases x1a rule: rev_cases)
      (auto simp: list_rel_append_single_iff
	ana_lookup_rel_alt_def get_literal_and_remove_of_analyse_wl_def
	get_literal_and_remove_of_analyse_wl2_def)
  subgoal
    using x1a x1c x_x' rem rem2 confl_min_last unfolding x1g_x1d st2 last b_def st
    by (cases x1c rule: rev_cases; cases x1a rule: rev_cases)
      (auto simp: list_rel_append_single_iff
	ana_lookup_rel_alt_def get_literal_and_remove_of_analyse_wl_def
	get_literal_and_remove_of_analyse_wl2_def)
  done

lemma ccmin_x1k_all:
  shows \<open>x1k \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
  unfolding x1k_x1j
  using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF ccmin_literals_are_in_\<L>\<^sub>i\<^sub>n_NU_x1g, of x1f]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[OF lits \<open>- x1j \<in> lits_of_l M\<close>]
  le st3 unfolding x1g_x1d by (auto split: if_splits simp: x1k_x1j uminus_\<A>\<^sub>i\<^sub>n_iff)


context
  notes _[simp]= x1k_x1j
  fixes b :: \<open>bool\<close> and lbd
  assumes b: \<open>(\<not> level_in_lbd (get_level M x1k) lbd, b) \<in> bool_rel\<close>
begin

private lemma in_conflict_atm_in:
  \<open>- x1e' \<in> lits_of_l M \<Longrightarrow> atm_in_conflict (atm_of x1e') D \<longleftrightarrow> x1e' \<in># D\<close> for x1e'
  using M_D n_d
  by (auto simp: atm_in_conflict_def true_annots_true_cls_def_iff_negation_in_model
      atms_of_def atm_of_eq_atm_of dest!: multi_member_split no_dup_consistentD)

lemma ccmin_already_seen:
  shows \<open>(get_level M x1k = 0 \<or>
          conflict_min_cach x1b (atm_of x1k) = SEEN_REMOVABLE \<or>
          atm_in_conflict (atm_of x1k) D) =
         (get_level M x1j = 0 \<or> x1 (atm_of x1j) = SEEN_REMOVABLE \<or> x1j \<in># D)\<close>
  using in_lits ana ux1j_M
  by (auto simp add: in_conflict_atm_in)


private lemma ccmin_lit_redundant_rec_wl_inv: \<open>lit_redundant_rec_wl_inv M NU D
     (x1, x2j, False)\<close>
  using x_x' last ana_lookup_conv rem rem2 x1a x1c le
  by (cases x1a rule: rev_cases; cases x1c rule: rev_cases)
    (auto simp add: lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def
    lit_redundant_reason_stack_def get_literal_and_remove_of_analyse_wl_def
    list_rel_append_single_iff get_literal_and_remove_of_analyse_wl2_def)

lemma ccmin_already_seen_rel:
  assumes
    \<open>get_level M x1k = 0 \<or>
     conflict_min_cach x1b (atm_of x1k) = SEEN_REMOVABLE \<or>
     atm_in_conflict (atm_of x1k) D\<close> and
    \<open>get_level M x1j = 0 \<or> x1 (atm_of x1j) = SEEN_REMOVABLE \<or> x1j \<in># D\<close>
  shows \<open>((x1b, x2k, False), x1, x2j, False)
         \<in> {((cach, ana, b), cach', ana', b').
          (ana, ana') \<in> ana_lookups_rel NU \<and>
          b = b' \<and> cach = cach' \<and> lit_redundant_rec_wl_inv M NU D (cach, ana', b)}\<close>
  using x2k_x2j ccmin_lit_redundant_rec_wl_inv by auto

context
  assumes
    \<open>\<not> (get_level M x1k = 0 \<or>
        conflict_min_cach x1b (atm_of x1k) = SEEN_REMOVABLE \<or>
        atm_in_conflict (atm_of x1k) D)\<close> and
    \<open>\<not> (get_level M x1j = 0 \<or> x1 (atm_of x1j) = SEEN_REMOVABLE \<or> x1j \<in># D)\<close>
begin
lemma ccmin_already_failed:
  shows \<open>(\<not> level_in_lbd (get_level M x1k) lbd \<or>
          conflict_min_cach x1b (atm_of x1k) = SEEN_FAILED) =
         (b \<or> x1 (atm_of x1j) = SEEN_FAILED)\<close>
  using b by auto


context
  assumes
    \<open>\<not> level_in_lbd (get_level M x1k) lbd \<or>
     conflict_min_cach x1b (atm_of x1k) = SEEN_FAILED\<close> and
    \<open>b \<or> x1 (atm_of x1j) = SEEN_FAILED\<close>
begin

lemma ccmin_mark_failed_lits_stack_inv2_lbd:
  shows \<open>mark_failed_lits_stack_inv2 NU x2k x1b\<close>
  using x1a x1c x2k_x2j rem rem2 x_x' le last
  unfolding mark_failed_lits_stack_inv_def lit_redundant_rec_wl_inv_def
    lit_redundant_rec_wl_ref_def get_literal_and_remove_of_analyse_wl_def
  unfolding mark_failed_lits_stack_inv2_def
  apply -
  apply (rule exI[of _ x2j])
  apply (cases \<open>x1a\<close> rule: rev_cases; cases \<open>x1c\<close> rule: rev_cases)
  by (auto simp: mark_failed_lits_stack_inv_def elim!: in_set_upd_cases)

lemma ccmin_mark_failed_lits_wl_lbd:
  shows \<open>mark_failed_lits_wl NU x2k x1b
         \<le> \<Down> Id
            (mark_failed_lits_wl NU x2j x1)\<close>
  by (auto simp: mark_failed_lits_wl_def)


lemma ccmin_rel_lbd:
  fixes cach :: \<open>nat \<Rightarrow> minimize_status\<close> and cacha :: \<open>nat \<Rightarrow> minimize_status\<close>
  assumes \<open>(cach, cacha)  \<in> Id\<close>
  shows \<open>((cach, [], False), cacha, [], False) \<in> {((cach, ana, b), cach', ana', b').
       (ana, ana') \<in> ana_lookups_rel NU \<and>
       b = b' \<and> cach = cach' \<and> lit_redundant_rec_wl_inv M NU D (cach, ana', b)}\<close>
  using x_x' assms by (auto simp: lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def)

end


context
  assumes
    \<open>\<not> (\<not> level_in_lbd (get_level M x1k) lbd \<or>
        conflict_min_cach x1b (atm_of x1k) = SEEN_FAILED)\<close> and
    \<open>\<not> (b \<or> x1 (atm_of x1j) = SEEN_FAILED)\<close>
begin

lemma ccmin_lit_in_trail:
  \<open>- x1k \<in> lits_of_l M\<close>
  using \<open>- x1j \<in> lits_of_l M\<close> x1k_x1j(1) by blast

lemma ccmin_lit_eq:
  \<open>- x1k = - x1j\<close>
  by auto


context
  fixes xa :: \<open>nat option\<close> and x'a :: \<open>nat option\<close>
  assumes xa_x'a: \<open>(xa, x'a) \<in> \<langle>nat_rel\<rangle>option_rel\<close>
begin

lemma ccmin_lit_eq2:
  \<open>(xa, x'a) \<in> Id\<close>
  using xa_x'a by auto

context
  assumes
    [simp]: \<open>xa = None\<close> \<open>x'a = None\<close>
begin

lemma ccmin_mark_failed_lits_stack_inv2_dec:
  \<open>mark_failed_lits_stack_inv2 NU x2k x1b\<close>
  using x1a x1c x2k_x2j rem rem2 x_x' le last
  unfolding mark_failed_lits_stack_inv_def lit_redundant_rec_wl_inv_def
    lit_redundant_rec_wl_ref_def get_literal_and_remove_of_analyse_wl_def
  unfolding mark_failed_lits_stack_inv2_def
  apply -
  apply (rule exI[of _ x2j])
  apply (cases \<open>x1a\<close> rule: rev_cases; cases \<open>x1c\<close> rule: rev_cases)
  by (auto simp: mark_failed_lits_stack_inv_def elim!: in_set_upd_cases)

lemma ccmin_mark_failed_lits_stack_wl_dec:
  shows \<open>mark_failed_lits_wl NU x2k x1b
         \<le> \<Down> Id
            (mark_failed_lits_wl NU x2j x1)\<close>
  by (auto simp: mark_failed_lits_wl_def)


lemma ccmin_rel_dec:
  fixes cach :: \<open>nat \<Rightarrow> minimize_status\<close> and cacha :: \<open>nat \<Rightarrow> minimize_status\<close>
  assumes \<open>(cach, cacha)  \<in> Id\<close>
  shows \<open>((cach, [], False), cacha, [], False)
         \<in>  {((cach, ana, b), cach', ana', b').
       (ana, ana') \<in> ana_lookups_rel NU \<and>
       b = b' \<and> cach = cach' \<and> lit_redundant_rec_wl_inv M NU D (cach, ana', b)}\<close>
  using assms by (auto simp: lit_redundant_rec_wl_ref_def lit_redundant_rec_wl_inv_def)

end


context
  fixes xb :: \<open>nat\<close> and x'b :: \<open>nat\<close>
  assumes H:
    \<open>xa = Some xb\<close>
    \<open>x'a = Some x'b\<close>
    \<open>(xb, x'b) \<in> nat_rel\<close>
    \<open>x'b \<in># dom_m NU\<close>
    \<open>2 \<le> length (NU \<propto> x'b)\<close>
    \<open>x'b > 0\<close>
    \<open>distinct (NU \<propto> x'b) \<and> \<not> tautology (mset (NU \<propto> x'b))\<close>
begin

lemma ccmin_stack_pre:
  shows \<open>xb \<in># dom_m NU\<close> \<open>2 \<le> length (NU \<propto> xb)\<close>
  using H by auto


lemma ccmin_literals_are_in_\<L>\<^sub>i\<^sub>n_NU_xb:
  shows \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (NU \<propto> xb))\<close>
  using lits_NU multi_member_split[of xb \<open>dom_m NU\<close>] H
  by (auto simp: ran_m_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_add_mset)

lemma ccmin_le_uint32_max_xb:
  \<open>length (NU \<propto> xb) \<le> Suc (uint32_max div 2)\<close>
  using simple_clss_size_upper_div2[OF bounded ccmin_literals_are_in_\<L>\<^sub>i\<^sub>n_NU_xb]
    H unfolding x1g_x1d
  by auto

private lemma ccmin_lit_redundant_rec_wl_inv3: \<open>lit_redundant_rec_wl_inv M NU D
     (x1, x2j @ [lit_redundant_reason_stack (- NU \<propto> x1d ! x1f) NU x'b], False)\<close>
  using ccmin_stack_pre H x_x' last ana_lookup_conv rem rem2 x1a x1c le
  by (cases x1a rule: rev_cases; cases x1c rule: rev_cases)
    (auto simp add: lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def
    lit_redundant_reason_stack_def get_literal_and_remove_of_analyse_wl_def
    list_rel_append_single_iff get_literal_and_remove_of_analyse_wl2_def)

lemma ccmin_stack_rel:
  shows \<open>((x1b, x2k @ [lit_redundant_reason_stack2 (- x1k) NU xb], False), x1,
          x2j @ [lit_redundant_reason_stack (- x1j) NU x'b], False)
         \<in>  {((cach, ana, b), cach', ana', b').
       (ana, ana') \<in> ana_lookups_rel NU \<and>
       b = b' \<and> cach = cach' \<and> lit_redundant_rec_wl_inv M NU D (cach, ana', b)}\<close>
  using x2k_x2j H ccmin_lit_redundant_rec_wl_inv3
  by (auto simp: list_rel_append_single_iff ana_lookup_rel_alt_def
      lit_redundant_reason_stack2_def lit_redundant_reason_stack_def)

end
end
end
end
end
end
end
end
end
end
end
end

lemma lit_redundant_rec_wl_lookup_lit_redundant_rec_wl:
  assumes
    M_D: \<open>M \<Turnstile>as CNot D\<close> and
    n_d: \<open>no_dup M\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<close> and
    \<open>(analysis, analysis') \<in> ana_lookups_rel NU\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> ((mset \<circ> fst) `# ran_m NU)\<close> and
    \<open>isasat_input_bounded \<A>\<close>
  shows
   \<open>lit_redundant_rec_wl_lookup \<A> M NU D cach analysis lbd \<le>
      \<Down> (Id \<times>\<^sub>r (ana_lookups_rel NU) \<times>\<^sub>r bool_rel) (lit_redundant_rec_wl M NU D cach analysis' lbd)\<close>
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

  have H: \<open>lit_redundant_rec_wl_lookup \<A> M NU D cach analysis lbd \<le>
      \<Down> {((cach, ana, b), cach', ana', b').
          (ana, ana') \<in> ana_lookups_rel NU \<and>
          b = b' \<and> cach = cach' \<and> lit_redundant_rec_wl_inv M NU D (cach, ana', b)}
       (lit_redundant_rec_wl M NU D cach analysis' lbd)\<close>
    using assms apply -
    unfolding lit_redundant_rec_wl_lookup_def lit_redundant_rec_wl_def WHILET_def
    apply (refine_vcg)
    subgoal by (rule ccmin_rel)
    subgoal by (rule ccmin_lit_redundant_rec_wl_inv2)
    subgoal by (rule ccmin_cond)
    subgoal by (rule ccmin_nempty)
    subgoal by (auto simp: list_rel_imp_same_length)
    subgoal by (rule ccmin_in_dom)
    subgoal by (rule ccmin_in_dom_le_length)
    subgoal by (rule ccmin_in_trail)
    subgoal by (rule ccmin_in_all_lits)
    subgoal by (rule ccmin_literals_are_in_\<L>\<^sub>i\<^sub>n_NU_x1g)
    subgoal by (rule ccmin_le_uint32_max)
    subgoal by (rule ccmin_less_length)
    subgoal by (rule ccmin_same_cond)
    subgoal by (rule ccmin_set_removable)
    subgoal by (rule ccmin_x1k_all)
    subgoal by (rule ccmin_already_seen)
    subgoal by (rule ccmin_already_seen_rel)
    subgoal by (rule ccmin_already_failed)
    subgoal by (rule ccmin_mark_failed_lits_stack_inv2_lbd)
    apply (rule ccmin_mark_failed_lits_wl_lbd; assumption)
    subgoal by (rule ccmin_rel_lbd)
    subgoal by (rule ccmin_lit_in_trail)
    subgoal by (rule ccmin_lit_eq)
    subgoal by (rule ccmin_lit_eq2)
    subgoal by (rule ccmin_mark_failed_lits_stack_inv2_dec)
    apply (rule ccmin_mark_failed_lits_stack_wl_dec; assumption)
    subgoal by (rule ccmin_rel_dec)
    subgoal by (rule ccmin_stack_pre)
    subgoal by (rule ccmin_stack_pre)
    subgoal by (rule ccmin_literals_are_in_\<L>\<^sub>i\<^sub>n_NU_xb)
    subgoal by (rule ccmin_le_uint32_max_xb)
    subgoal by (rule ccmin_stack_rel)
    done
  show ?thesis
    by (rule H[THEN order_trans], rule conc_fun_R_mono)
     auto
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
         Some C \<Rightarrow> do {
	   ASSERT(C \<in># dom_m NU);
	   ASSERT(length (NU \<propto> C) \<ge> 2);
	   ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (NU \<propto> C)));
	   ASSERT(distinct (NU \<propto> C) \<and> \<not>tautology (mset (NU \<propto> C)));
	   ASSERT(length (NU \<propto> C) \<le> Suc (uint32_max div 2));
	   lit_redundant_rec_wl_lookup \<A> M NU D cach [lit_redundant_reason_stack2 (-L) NU C] lbd
	 }
       | None \<Rightarrow> do {
           RETURN (cach, [], False)
       }
     }
  }\<close>

lemma literal_redundant_wl_lookup_literal_redundant_wl:
  assumes \<open>M \<Turnstile>as CNot D\<close> \<open>no_dup M\<close> \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<close>
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> ((mset \<circ> fst) `# ran_m NU)\<close> and
    \<open>isasat_input_bounded \<A>\<close>
  shows
    \<open>literal_redundant_wl_lookup \<A> M NU D cach L lbd \<le>
      \<Down> (Id \<times>\<^sub>f (ana_lookups_rel NU \<times>\<^sub>f bool_rel)) (literal_redundant_wl M NU D cach L lbd)\<close>
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
    \<le> \<Down> ({(C, C'). (C, C') \<in> \<langle>nat_rel\<rangle>option_rel})
      (get_propagation_reason M y)\<close> if \<open>x = y\<close> and \<open>y \<in> lits_of_l M\<close> for x y
    by (use that in \<open>auto simp: get_propagation_reason_def intro: RES_refine\<close>)
  show ?thesis
    unfolding literal_redundant_wl_lookup_def literal_redundant_wl_def
    apply (refine_vcg lit_redundant_rec_wl_lookup_lit_redundant_rec_wl)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal
      using assms by (auto dest!: multi_member_split simp: ran_m_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_add_mset)
    subgoal by auto
    subgoal by auto
    subgoal using assms simple_clss_size_upper_div2[of \<A> \<open>mset (NU \<propto> _)\<close>] by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by (auto simp: lit_redundant_reason_stack2_def lit_redundant_reason_stack_def
      ana_lookup_rel_def)
    subgoal using assms by auto
    subgoal using assms by auto
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
         (nxs, 1, s, outl);
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
    lits_NU: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf NU)\<close> and
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
   then have init_args_ref: \<open>((D, 1, s', outl), D, D) \<in> R\<close>
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
      by (auto simp: R_def uint32_max_def)
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
      \<open>literal_redundant_wl_lookup \<A> M NU nxs cach ?L lbd \<le> \<Down> (Id \<times>\<^sub>f (ana_lookups_rel NU \<times>\<^sub>f bool_rel)) (literal_redundant_wl M NU nxs cach ?L lbd)\<close>
      by (rule literal_redundant_wl_lookup_literal_redundant_wl)
       (use lits_NU n_d lits M_x1 struct_invs bounded add_inv \<open>outl' ! x1d \<in># E\<close> \<open>E = nxs\<close> in auto)

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
      apply (rule ref_two_step')
       apply (rule 2)
       apply (subst conc_fun_chain)
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
         apply (auto simp: WB_More_Refinement_List.swap_def)
      unfolding WB_More_Refinement_List.swap_def[symmetric]
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
  :: \<open>nat multiset \<Rightarrow> ((minimize_status list \<times> nat list) \<times> minimize_status list) set\<close>
where
  \<open>cach_refinement_nonull \<A> = {((cach, support), cach'). cach = cach' \<and>
       (\<forall>L < length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longleftrightarrow> L \<in> set support) \<and>
       (\<forall>L \<in> set support. L < length cach) \<and>
       distinct support \<and> set support \<subseteq> set_mset \<A>}\<close>


definition cach_refinement
  :: \<open>nat multiset \<Rightarrow> ((minimize_status list \<times> nat list) \<times> (nat conflict_min_cach)) set\<close>
where
  \<open>cach_refinement \<A>\<^sub>i\<^sub>n = cach_refinement_nonull \<A>\<^sub>i\<^sub>n O cach_refinement_list \<A>\<^sub>i\<^sub>n\<close>

lemma cach_refinement_alt_def:
  \<open>cach_refinement \<A>\<^sub>i\<^sub>n = {((cach, support), cach').
       (\<forall>L < length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longleftrightarrow> L \<in> set support) \<and>
       (\<forall>L \<in> set support. L < length cach) \<and>
       (\<forall>L \<in># \<A>\<^sub>i\<^sub>n. L < length cach \<and> cach ! L = cach' L) \<and>
       distinct support \<and> set support \<subseteq> set_mset \<A>\<^sub>i\<^sub>n}\<close>
  unfolding cach_refinement_def cach_refinement_nonull_def cach_refinement_list_def
  apply (rule; rule)
  apply (simp add: map_fun_rel_def split: prod.splits)
  apply blast
  apply (simp add: map_fun_rel_def split: prod.splits)
  apply (rule_tac b=x1a in relcomp.relcompI)
  apply blast
  apply blast
  done

lemma in_cach_refinement_alt_def:
  \<open>((cach, support), cach') \<in> cach_refinement \<A>\<^sub>i\<^sub>n \<longleftrightarrow>
     (cach, cach') \<in> cach_refinement_list \<A>\<^sub>i\<^sub>n \<and>
     (\<forall>L<length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longleftrightarrow> L \<in> set support) \<and>
     (\<forall>L \<in> set support. L < length cach) \<and>
     distinct support \<and> set support \<subseteq> set_mset  \<A>\<^sub>i\<^sub>n\<close>
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


lemma nth_conflict_min_cach:
  \<open>(uncurry (RETURN oo conflict_min_cach_l), uncurry (RETURN oo conflict_min_cach)) \<in>
     [\<lambda>(cach, L). L \<in># \<A>\<^sub>i\<^sub>n]\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n \<times>\<^sub>r nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: map_fun_rel_def
      in_cach_refinement_alt_def cach_refinement_list_def conflict_min_cach_l_def)

definition (in -) conflict_min_cach_set_failed
   :: \<open>nat conflict_min_cach \<Rightarrow> nat \<Rightarrow> nat conflict_min_cach\<close>
where
  [simp]: \<open>conflict_min_cach_set_failed cach L = cach(L := SEEN_FAILED)\<close>

definition (in -) conflict_min_cach_set_failed_l
  :: \<open>conflict_min_cach_l \<Rightarrow> nat \<Rightarrow> conflict_min_cach_l nres\<close>
where
  \<open>conflict_min_cach_set_failed_l = (\<lambda>(cach, sup) L. do {
     ASSERT(L < length cach);
     ASSERT(length sup \<le> 1 + uint32_max div 2);
     RETURN (cach[L := SEEN_FAILED], if cach ! L = SEEN_UNKNOWN then sup @ [L] else sup)
   })\<close>

lemma bounded_included_le:
   assumes bounded: \<open>isasat_input_bounded \<A>\<close> and \<open>distinct n\<close> and \<open>set n \<subseteq> set_mset \<A>\<close>
   shows \<open>length n \<le> Suc (uint32_max div 2)\<close>
proof -
  have lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (Pos `# mset n)\<close> and
    dist: \<open>distinct n\<close>
    using assms
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def inj_on_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
   have dist: \<open>distinct_mset (Pos `# mset n)\<close>
    by (subst distinct_image_mset_inj)
      (use dist in \<open>auto simp: inj_on_def\<close>)
  have tauto: \<open>\<not> tautology (poss (mset n))\<close>
    by (auto simp: tautology_decomp)

  show ?thesis
    using simple_clss_size_upper_div2[OF bounded lits dist tauto]
    by (auto simp: uint32_max_def)
qed

lemma conflict_min_cach_set_failed:
  \<open>(uncurry conflict_min_cach_set_failed_l, uncurry (RETURN oo conflict_min_cach_set_failed)) \<in>
     [\<lambda>(cach, L). L \<in># \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded \<A>\<^sub>i\<^sub>n]\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n \<times>\<^sub>r nat_rel \<rightarrow> \<langle>cach_refinement \<A>\<^sub>i\<^sub>n\<rangle>nres_rel\<close>
  supply isasat_input_bounded_def[simp del]
  apply (intro frefI nres_relI) (*TODO Proof*)
  apply   (auto simp: in_cach_refinement_alt_def map_fun_rel_def cach_refinement_list_def
        conflict_min_cach_set_failed_l_def cach_refinement_nonull_def
        all_conj_distrib intro!: ASSERT_leI bounded_included_le[of \<A>\<^sub>i\<^sub>n]
      dest!: multi_member_split dest: set_mset_mono
      dest: subset_add_mset_notin_subset_mset)
  by (fastforce dest: subset_add_mset_notin_subset_mset)+

definition (in -) conflict_min_cach_set_removable
  :: \<open>nat conflict_min_cach \<Rightarrow> nat \<Rightarrow> nat conflict_min_cach\<close>
where
  [simp]: \<open>conflict_min_cach_set_removable cach L = cach(L:= SEEN_REMOVABLE)\<close>

lemma conflict_min_cach_set_removable:
  \<open>(uncurry conflict_min_cach_set_removable_l,
    uncurry (RETURN oo conflict_min_cach_set_removable)) \<in>
     [\<lambda>(cach, L). L \<in># \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded \<A>\<^sub>i\<^sub>n]\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n \<times>\<^sub>r nat_rel \<rightarrow> \<langle>cach_refinement \<A>\<^sub>i\<^sub>n\<rangle>nres_rel\<close>
  supply isasat_input_bounded_def[simp del]
  apply (intro frefI nres_relI) (*TODO Proof*)
  apply   (auto simp: in_cach_refinement_alt_def map_fun_rel_def cach_refinement_list_def
        conflict_min_cach_set_removable_l_def cach_refinement_nonull_def
        all_conj_distrib intro!: ASSERT_leI bounded_included_le[of \<A>\<^sub>i\<^sub>n]
      dest!: multi_member_split dest: set_mset_mono
      dest: subset_add_mset_notin_subset_mset)
  by (fastforce dest: subset_add_mset_notin_subset_mset)+



definition isa_mark_failed_lits_stack where
  \<open>isa_mark_failed_lits_stack NU analyse cach = do {
    let l = length analyse;
    ASSERT(length analyse \<le> 1 + uint32_max div 2);
    (_, cach) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(_, cach). True\<^esup>
      (\<lambda>(i, cach). i < l)
      (\<lambda>(i, cach). do {
        ASSERT(i < length analyse);
        let (cls_idx, idx, _) = (analyse ! i);
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
lemma mark_failed_lits_stack_inv_helper1: \<open>mark_failed_lits_stack_inv a ba a2' \<Longrightarrow>
       a1' < length ba \<Longrightarrow>
       (a1'a, a2'a) = ba ! a1' \<Longrightarrow>
       a1'a \<in># dom_m a\<close>
  using nth_mem[of a1' ba] unfolding mark_failed_lits_stack_inv_def
  by (auto simp del: nth_mem)

lemma mark_failed_lits_stack_inv_helper2: \<open>mark_failed_lits_stack_inv a ba a2' \<Longrightarrow>
       a1' < length ba \<Longrightarrow>
       (a1'a, xx, a2'a, yy) = ba ! a1' \<Longrightarrow>
       a2'a - Suc 0 < length (a \<propto> a1'a)\<close>
  using nth_mem[of a1' ba] unfolding mark_failed_lits_stack_inv_def
  by (auto simp del: nth_mem)

lemma isa_mark_failed_lits_stack_isa_mark_failed_lits_stack:
  assumes \<open>isasat_input_bounded \<A>\<^sub>i\<^sub>n\<close>
  shows \<open>(uncurry2 isa_mark_failed_lits_stack, uncurry2 (mark_failed_lits_stack \<A>\<^sub>i\<^sub>n)) \<in>
     [\<lambda>((N, ana), cach). length ana \<le> 1 +  uint32_max div 2]\<^sub>f
     {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f ana_lookups_rel NU \<times>\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n \<rightarrow>
     \<langle>cach_refinement \<A>\<^sub>i\<^sub>n\<rangle>nres_rel\<close>
proof -
  have subset_mset_add_new: \<open>a \<notin># A \<Longrightarrow> a \<in># B \<Longrightarrow> add_mset a A \<subseteq># B \<longleftrightarrow> A \<subseteq># B\<close> for a A B
    by (metis insert_DiffM insert_subset_eq_iff subset_add_mset_notin_subset)
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
      \<open>case y of (x, xa) \<Rightarrow> (case x of (N, ana) \<Rightarrow> \<lambda>cach. length ana \<le> 1 +  uint32_max div 2) xa\<close> and
      xy: \<open>(x, y) \<in> {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f ana_lookups_rel NU
         \<times>\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n\<close> and
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
	\<open>x2g0 = (x2g, x2g2)\<close>
        \<open>x2b ! x1e = (x1g, x2g0)\<close> and
      xax': \<open>(xa, x') \<in> nat_rel \<times>\<^sub>f cach_refinement \<A>\<^sub>i\<^sub>n\<close> and
      cond: \<open>case xa of (i, cach) \<Rightarrow> i < length x2b\<close> and
      cond': \<open>case x' of (i, cach) \<Rightarrow> i < length x2\<close> and
      inv: \<open>case x' of (_, x) \<Rightarrow> mark_failed_lits_stack_inv x1a x2 x\<close> and
      le: \<open>x1d < length x2\<close> \<open>x1e < length x2b\<close> and
      atm: \<open>atm_of (x1a \<propto> x1f ! (x2f - 1)) \<in># \<A>\<^sub>i\<^sub>n\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c xa x' x1d x2d x1e x2e x1f x2f x1g x2g
      x2f0 x2f1 x2f2 x2f3 x2g0 x2g1 x2g2 x2g3
  proof -
    obtain i cach where x': \<open>x' = (i, cach)\<close> by (cases x')
    have [simp]:
      \<open>x1 = (x1a, x2)\<close>
      \<open>y = ((x1a, x2), x2a)\<close>
      \<open>x1b = (x1c, x2b)\<close>
      \<open>x = ((x1c, x2b), x2c)\<close>
      \<open>x' = (x1d, x2d)\<close>
      \<open>xa = (x1d, x2e)\<close>
      \<open>x1f = x1g\<close>
      \<open>x1e = x1d\<close>
      \<open>x2f0 = (x2f1, x2f, x2f3)\<close>
      \<open>x2g = x2f\<close>
      \<open>x2g0 = (x2g, x2g2)\<close> and
      st': \<open>x2 ! x1d = (x1g, x2f0)\<close> and
      cach:\<open>(x2e, x2d) \<in> cach_refinement \<A>\<^sub>i\<^sub>n\<close> and
      \<open>(x2c, x2a) \<in> cach_refinement \<A>\<^sub>i\<^sub>n\<close> and
      x2f0_x2g0: \<open>((x1g, x2g, x2g2), (x1f, x2f1, x2f, x2f3)) \<in> ana_lookup_rel NU\<close>
      using xy st xax' param_nth[of x1e x2 x1d x2b \<open>ana_lookup_rel NU\<close>] le
      by (auto intro: simp: ana_lookup_rel_alt_def)

    have arena: \<open>valid_arena x1c x1a vdom\<close>
      using xy unfolding st by auto
    have \<open>x2 ! x1e \<in> set x2\<close>
      using le
      by auto
    then have \<open>x2 ! x1d \<in> set x2\<close> and
      x2f: \<open>x2f \<le> length (x1a \<propto> x1f)\<close> and
      x1f: \<open>x1g \<in># dom_m x1a\<close> and
      x2g: \<open>x2g > 0\<close> and
      x2g_u1_le: \<open>x2g - 1 < length (x1a \<propto> x1f)\<close>
      using inv le x2f0_x2g0 nth_mem[of x1d x2]
      unfolding mark_failed_lits_stack_inv_def x' prod.case st st'
      by (auto simp del: nth_mem simp: st' ana_lookup_rel_alt_def split: if_splits
        dest!: bspec[of \<open>set x2\<close> _ \<open>(_, _, _, _)\<close>])

    have \<open>is_Lit (x1c ! (x1g + (x2g - 1)))\<close>
      by (rule arena_lifting[OF arena x1f]) (use x2f x2g x2g_u1_le in auto)
    then show ?le and ?A
      using arena_lifting[OF arena x1f] le x2f x1f x2g atm x2g_u1_le
      by (auto simp: arena_lit_def)
    show ?lit
      unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
      by (rule bex_leI[of _ x1f])
        (use arena x1f x2f x2g x2g_u1_le in \<open>auto intro!: exI[of _ x1a] exI[of _ vdom]\<close>)
    show \<open>x1g + x2g \<ge> 1\<close>
      using x2g by auto
    have [simp]: \<open>arena_lit x1c (x1g + x2g - Suc 0) = x1a \<propto> x1g ! (x2g - Suc 0)\<close>
       using that x1f x2f x2g x2g_u1_le by (auto simp: arena_lifting[OF arena])
    have \<open>atm_of (arena_lit x1c (x1g + x2g - Suc 0)) < length (fst x2e)\<close>
      using \<open>?A\<close> cach by (auto simp: cach_refinement_alt_def dest: multi_member_split)

    then show ?final
      using \<open>?le\<close> \<open>?A\<close> cach x1f x2g_u1_le x2g assms
     apply -
     apply (rule conflict_min_cach_set_failed[of \<A>\<^sub>i\<^sub>n, THEN fref_to_Down_curry, THEN order_trans])
      by (cases x2e)
        (auto simp:  cach_refinement_alt_def RETURN_def conc_fun_RES
        arena_lifting[OF arena] subset_mset_add_new)
  qed

  show ?thesis
    unfolding isa_mark_failed_lits_stack_def mark_failed_lits_stack_def uncurry_def
    apply (rewrite at \<open>let _ = length _ in _\<close> Let_def)
    apply (intro frefI nres_relI)
    apply refine_vcg
    subgoal by (auto simp: list_rel_imp_same_length)
    subgoal by auto
    subgoal by auto
    subgoal for x y x1 x1a x2 x2a x1b x1c x2b x2c xa x' x1d x2d x1e x2e
      by (auto simp: list_rel_imp_same_length)
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

definition isa_get_literal_and_remove_of_analyse_wl
   :: \<open>arena \<Rightarrow> (nat \<times> nat \<times> bool) list \<Rightarrow> nat literal \<times> (nat \<times> nat \<times> bool) list\<close> where
  \<open>isa_get_literal_and_remove_of_analyse_wl C analyse =
    (let (i, j, b) = (last analyse) in
     (arena_lit C (i + j), analyse[length analyse - 1 := (i, j + 1, b)]))\<close>

definition isa_get_literal_and_remove_of_analyse_wl_pre
   :: \<open>arena \<Rightarrow> (nat \<times> nat \<times> bool) list \<Rightarrow> bool\<close> where
\<open>isa_get_literal_and_remove_of_analyse_wl_pre arena analyse \<longleftrightarrow>
  (let (i, j, b) = last analyse in
    analyse \<noteq> [] \<and> arena_lit_pre arena (i+j) \<and> j < uint32_max)\<close>


lemma arena_lit_pre_le: \<open>length a \<le> uint64_max \<Longrightarrow>
       arena_lit_pre a i \<Longrightarrow> i \<le> uint64_max\<close>
   using arena_lifting(7)[of a _ _] unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
  by fastforce

lemma arena_lit_pre_le2: \<open>length a \<le> uint64_max \<Longrightarrow>
       arena_lit_pre a i \<Longrightarrow> i < uint64_max\<close>
   using arena_lifting(7)[of a _ _] unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
  by fastforce

definition lit_redundant_reason_stack_wl_lookup_pre :: \<open>nat literal \<Rightarrow> arena_el list \<Rightarrow> nat \<Rightarrow> bool\<close> where
\<open>lit_redundant_reason_stack_wl_lookup_pre L NU C \<longleftrightarrow>
  arena_lit_pre NU C \<and>
  arena_is_valid_clause_idx NU C\<close>

definition lit_redundant_reason_stack_wl_lookup
  :: \<open>nat literal \<Rightarrow> arena_el list \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> bool\<close>
where
\<open>lit_redundant_reason_stack_wl_lookup L NU C =
  (if arena_length NU C > 2 then (C, 1, False)
  else if arena_lit NU C = L
  then (C, 1, False)
  else (C, 0, True))\<close>

definition ana_lookup_conv_lookup :: \<open>arena \<Rightarrow> (nat \<times> nat \<times> bool) \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)\<close> where
\<open>ana_lookup_conv_lookup NU = (\<lambda>(C, i, b).
  (C, (if b then 1 else 0), i, (if b then 1 else arena_length NU C)))\<close>

definition ana_lookup_conv_lookup_pre :: \<open>arena \<Rightarrow> (nat \<times> nat \<times> bool) \<Rightarrow> bool\<close> where
\<open>ana_lookup_conv_lookup_pre NU = (\<lambda>(C, i, b). arena_is_valid_clause_idx NU C)\<close>

definition isa_lit_redundant_rec_wl_lookup
  :: \<open>trail_pol \<Rightarrow> arena \<Rightarrow> lookup_clause_rel \<Rightarrow>
     _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (_ \<times> _ \<times> bool) nres\<close>
where
  \<open>isa_lit_redundant_rec_wl_lookup M NU D cach analysis lbd =
      WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
        (\<lambda>(cach, analyse, b). analyse \<noteq> [])
        (\<lambda>(cach, analyse, b). do {
            ASSERT(analyse \<noteq> []);
            ASSERT(length analyse \<le> 1 +  uint32_max div 2);
            ASSERT(arena_is_valid_clause_idx NU (fst (last analyse)));
	    ASSERT(ana_lookup_conv_lookup_pre NU ((last analyse)));
	    let (C, k, i, len) = ana_lookup_conv_lookup NU ((last analyse));
            ASSERT(C < length NU);
            ASSERT(arena_is_valid_clause_idx NU C);
            ASSERT(arena_lit_pre NU (C + k));
            if i \<ge> len
            then do {
	      cach \<leftarrow> conflict_min_cach_set_removable_l cach (atm_of (arena_lit NU (C + k)));
              RETURN(cach, butlast analyse, True)
	    }
            else do {
	      ASSERT (isa_get_literal_and_remove_of_analyse_wl_pre NU analyse);
	      let (L, analyse) = isa_get_literal_and_remove_of_analyse_wl NU analyse;
              ASSERT(length analyse \<le> 1 +  uint32_max div 2);
	      ASSERT(get_level_pol_pre (M, L));
	      let b = \<not>level_in_lbd (get_level_pol M L) lbd;
	      ASSERT(atm_in_conflict_lookup_pre (atm_of L) D);
	      ASSERT(conflict_min_cach_l_pre (cach, atm_of L));
	      if (get_level_pol M L = 0 \<or>
		  conflict_min_cach_l cach (atm_of L) = SEEN_REMOVABLE \<or>
		  atm_in_conflict_lookup (atm_of L) D)
	      then RETURN (cach, analyse, False)
	      else if b \<or> conflict_min_cach_l cach (atm_of L) = SEEN_FAILED
	      then do {
		 cach \<leftarrow> isa_mark_failed_lits_stack NU analyse cach;
		 RETURN (cach, take 0 analyse, False)
	      }
	      else do {
		 C \<leftarrow> get_propagation_reason_pol M (-L);
		 case C of
		   Some C \<Rightarrow> do {
		     ASSERT(lit_redundant_reason_stack_wl_lookup_pre (-L) NU C);
		     RETURN (cach, analyse @ [lit_redundant_reason_stack_wl_lookup (-L) NU C], False)
		   }
		 | None \<Rightarrow> do {
		     cach \<leftarrow> isa_mark_failed_lits_stack NU analyse cach;
		     RETURN (cach, take 0 analyse, False)
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
          ASSERT(length analyse \<le> 1 +  uint32_max div 2);
	  let (C, i, b) = last analyse;
          ASSERT(arena_is_valid_clause_idx NU (fst (last analyse)));
	  ASSERT(ana_lookup_conv_lookup_pre NU (last analyse));
	  let (C, k, i, len) = ana_lookup_conv_lookup NU ((C, i, b));
          ASSERT(C < length NU);
          let _ = map xarena_lit
              ((Misc.slice
                C
                (C + arena_length NU C))
                NU);
          ASSERT(arena_is_valid_clause_idx NU C);
          ASSERT(arena_lit_pre NU (C + k));
          if i \<ge> len
          then do {
	    cach \<leftarrow> conflict_min_cach_set_removable_l cach (atm_of (arena_lit NU (C + k)));
            RETURN(cach, butlast analyse, True)
          }
          else do {
              ASSERT (isa_get_literal_and_remove_of_analyse_wl_pre NU analyse);
              let (L, analyse) = isa_get_literal_and_remove_of_analyse_wl NU analyse;
              ASSERT(length analyse \<le> 1+ uint32_max div 2);
              ASSERT(get_level_pol_pre (M, L));
              let b = \<not>level_in_lbd (get_level_pol M L) lbd;
              ASSERT(atm_in_conflict_lookup_pre (atm_of L) D);
	      ASSERT(conflict_min_cach_l_pre (cach, atm_of L));
              if (get_level_pol M L = 0 \<or>
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
                  Some C \<Rightarrow> do {
		    ASSERT(lit_redundant_reason_stack_wl_lookup_pre (-L) NU C);
		    RETURN (cach, analyse @ [lit_redundant_reason_stack_wl_lookup (-L) NU C], False)
		  }
                | None \<Rightarrow> do {
                    cach \<leftarrow> isa_mark_failed_lits_stack NU analyse cach;
                    RETURN (cach, [], False)
                }
            }
        }
      })
      (cach, analysis, False)\<close>
  unfolding isa_lit_redundant_rec_wl_lookup_def Let_def take_0
  by (auto simp: Let_def)

lemma lit_redundant_rec_wl_lookup_alt_def:
  \<open>lit_redundant_rec_wl_lookup \<A> M NU D cach analysis lbd =
      WHILE\<^sub>T\<^bsup>lit_redundant_rec_wl_inv2 M NU D\<^esup>
        (\<lambda>(cach, analyse, b). analyse \<noteq> [])
        (\<lambda>(cach, analyse, b). do {
            ASSERT(analyse \<noteq> []);
            ASSERT(length analyse \<le> length M);
	    let (C, k, i, len) = ana_lookup_conv NU (last analyse);
            ASSERT(C \<in># dom_m NU);
            ASSERT(length (NU \<propto> C) > k); \<comment> \<open> >= 2 would work too \<close>
            ASSERT (NU \<propto> C ! k \<in> lits_of_l M);
            ASSERT(NU \<propto> C ! k \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>);
	    ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (NU \<propto> C)));
	    ASSERT(length (NU \<propto> C) \<le> Suc (uint32_max div 2));
	    ASSERT(len \<le> length (NU \<propto> C)); \<comment> \<open>makes the refinement easier\<close>
	    let (C,k, i, len) = (C,k,i,len);
            let C = NU \<propto> C;
            if i \<ge> len
            then
               RETURN(cach (atm_of (C ! k) := SEEN_REMOVABLE), butlast analyse, True)
            else do {
               let (L, analyse) = get_literal_and_remove_of_analyse_wl2 C analyse;
               ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>);
               let b = \<not>level_in_lbd (get_level M L) lbd;
               if (get_level M L = 0 \<or>
                   conflict_min_cach cach (atm_of L) = SEEN_REMOVABLE \<or>
                   atm_in_conflict (atm_of L) D)
               then RETURN (cach, analyse, False)
               else if b \<or> conflict_min_cach cach (atm_of L) = SEEN_FAILED
               then do {
                  ASSERT(mark_failed_lits_stack_inv2 NU analyse cach);
                  cach \<leftarrow> mark_failed_lits_wl NU analyse cach;
                  RETURN (cach, [], False)
               }
               else do {
	          ASSERT(- L \<in> lits_of_l M);
                  C \<leftarrow> get_propagation_reason M (-L);
                  case C of
                    Some C \<Rightarrow> do {
		      ASSERT(C \<in># dom_m NU);
		      ASSERT(length (NU \<propto> C) \<ge> 2);
		      ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (NU \<propto> C)));
                      ASSERT(length (NU \<propto> C) \<le> Suc (uint32_max div 2));
		      RETURN (cach, analyse @ [lit_redundant_reason_stack2 (-L) NU C], False)
		    }
                  | None \<Rightarrow> do {
                      ASSERT(mark_failed_lits_stack_inv2 NU analyse cach);
                      cach \<leftarrow> mark_failed_lits_wl NU analyse cach;
                      RETURN (cach, [], False)
                  }
              }
          }
        })
       (cach, analysis, False)\<close>
  unfolding lit_redundant_rec_wl_lookup_def Let_def by auto

lemma valid_arena_nempty:
  \<open>valid_arena arena N vdom \<Longrightarrow> i \<in># dom_m N \<Longrightarrow> N \<propto> i \<noteq> []\<close>
  using arena_lifting(19)[of arena N vdom i]
  arena_lifting(4)[of arena N vdom i]
  by auto

lemma isa_lit_redundant_rec_wl_lookup_lit_redundant_rec_wl_lookup:
  assumes \<open>isasat_input_bounded \<A>\<close>
  shows \<open>(uncurry5 isa_lit_redundant_rec_wl_lookup, uncurry5 (lit_redundant_rec_wl_lookup \<A>)) \<in>
    [\<lambda>(((((_, N), _), _), _), _).  literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> ((mset \<circ> fst) `# ran_m N)]\<^sub>f
    trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f lookup_clause_rel \<A> \<times>\<^sub>f
     cach_refinement \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow>
      \<langle>cach_refinement \<A> \<times>\<^sub>r Id \<times>\<^sub>r bool_rel\<rangle>nres_rel\<close>
proof -
  have isa_mark_failed_lits_stack: \<open>isa_mark_failed_lits_stack x2e x2z x1l
	\<le> \<Down> (cach_refinement \<A>)
	   (mark_failed_lits_wl x2 x2y x1j)\<close>
    if
      \<open>case y of
       (x, xa) \<Rightarrow>
	 (case x of
	  (x, xa) \<Rightarrow>
	    (case x of
	     (x, xa) \<Rightarrow>
	       (case x of
		(x, xa) \<Rightarrow>
		  (case x of
		   (uu_, N) \<Rightarrow>
		     \<lambda>_ _ _ _.
			literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> ((mset \<circ> fst) `# ran_m N))                 xa)
		xa)
	     xa)
	  xa\<close> and
      \<open>(x, y)
       \<in> trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f
	 lookup_clause_rel \<A> \<times>\<^sub>f  cach_refinement \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id\<close> and
      \<open>x1c = (x1d, x2)\<close> and
      \<open>x1b = (x1c, x2a)\<close> and
      \<open>x1a = (x1b, x2b)\<close> and
      \<open>x1 = (x1a, x2c)\<close> and
      \<open>y = (x1, x2d)\<close> and
      \<open>x1h = (x1i, x2e)\<close> and
      \<open>x1g = (x1h, x2f)\<close> and
      \<open>x1f = (x1g, x2g)\<close> and
      \<open>x1e = (x1f, x2h)\<close> and
      \<open>x = (x1e, x2i)\<close> and
      \<open>(xa, x') \<in> cach_refinement \<A> \<times>\<^sub>f (Id \<times>\<^sub>f bool_rel)\<close> and
      \<open>case xa of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      \<open>case x' of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      \<open>lit_redundant_rec_wl_inv2 x1d x2 x2a x'\<close> and
      \<open>x2j = (x1k, x2k)\<close> and
      \<open>x' = (x1j, x2j)\<close> and
      \<open>x2l = (x1m, x2m)\<close> and
      \<open>xa = (x1l, x2l)\<close> and
      \<open>x1k \<noteq> []\<close> and
      \<open>x1m \<noteq> []\<close> and
      \<open>x2o = (x1p, x2p)\<close> and
      \<open>x2n = (x1o, x2o)\<close> and
      \<open>ana_lookup_conv x2 (last x1k) = (x1n, x2n)\<close> and
      \<open>x2q = (x1r, x2r)\<close> and
      \<open>last x1m = (x1q, x2q)\<close> and
      \<open>x1n \<in># dom_m x2\<close> and
      \<open>x1o < length (x2 \<propto> x1n)\<close> and
      \<open>x2 \<propto> x1n ! x1o \<in> lits_of_l x1d\<close> and
      \<open>x2 \<propto> x1n ! x1o \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and
      \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (x2 \<propto> x1n))\<close> and
      \<open>length (x2 \<propto> x1n) \<le> Suc (uint32_max div 2)\<close> and
      \<open>x2p \<le> length (x2 \<propto> x1n)\<close> and
      \<open>arena_is_valid_clause_idx x2e (fst (last x1m))\<close> and
      \<open>x2t = (x1u, x2u)\<close> and
      \<open>x2s = (x1t, x2t)\<close> and
      \<open>(x1n, x1o, x1p, x2p) = (x1s, x2s)\<close> and
      \<open>x2w = (x1x, x2x)\<close> and
      \<open>x2v = (x1w, x2w)\<close> and
      \<open>ana_lookup_conv_lookup x2e (x1q, x1r, x2r) = (x1v, x2v)\<close> and
      \<open>x1v < length x2e\<close> and
      \<open>arena_is_valid_clause_idx x2e x1v\<close> and
      \<open>arena_lit_pre x2e (x1v + x1w)\<close> and
      \<open>\<not> x2x \<le> x1x\<close> and
      \<open>\<not> x2u \<le> x1u\<close> and
      \<open>isa_get_literal_and_remove_of_analyse_wl_pre x2e x1m\<close> and
      \<open>get_literal_and_remove_of_analyse_wl2 (x2 \<propto> x1s) x1k = (x1y, x2y)\<close> and
      \<open>isa_get_literal_and_remove_of_analyse_wl x2e x1m = (x1z, x2z)\<close> and
      \<open>x1y \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and    \<open>get_level_pol_pre (x1i, x1z)\<close> and
      \<open>atm_in_conflict_lookup_pre (atm_of x1z) x2f\<close> and
      \<open>conflict_min_cach_l_pre (x1l, atm_of x1z)\<close> and
      \<open>\<not> (get_level_pol x1i x1z = 0 \<or>
	  conflict_min_cach_l x1l (atm_of x1z) = SEEN_REMOVABLE \<or>
	  atm_in_conflict_lookup (atm_of x1z) x2f)\<close> and
      \<open>\<not> (get_level x1d x1y = 0 \<or>
	  conflict_min_cach x1j (atm_of x1y) = SEEN_REMOVABLE \<or>
	  atm_in_conflict (atm_of x1y) x2a)\<close> and
      \<open>\<not> level_in_lbd (get_level_pol x1i x1z) x2i \<or>
       conflict_min_cach_l x1l (atm_of x1z) = SEEN_FAILED\<close> and
      \<open>\<not> level_in_lbd (get_level x1d x1y) x2d \<or>
       conflict_min_cach x1j (atm_of x1y) = SEEN_FAILED\<close> and
      inv2: \<open>mark_failed_lits_stack_inv2 x2 x2y x1j\<close> and
      \<open>length x1m \<le> 1+ uint32_max div 2\<close>
     for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
	 x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q
	 x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y x1z
	 x2z
  proof -
    have [simp]: \<open>x2z = x2y\<close>
      using that
      by (auto simp: isa_get_literal_and_remove_of_analyse_wl_def
	get_literal_and_remove_of_analyse_wl2_def)

    obtain x2y0 where
      x2z: \<open>(x2y, x2y0) \<in> ana_lookups_rel x2\<close> and
      inv: \<open>mark_failed_lits_stack_inv x2 x2y0 x1j\<close>
      using inv2 unfolding mark_failed_lits_stack_inv2_def
      by blast
    have 1: \<open>mark_failed_lits_wl x2 x2y x1j  = mark_failed_lits_wl x2 x2y0 x1j\<close>
      unfolding mark_failed_lits_wl_def by auto
    show ?thesis
      unfolding 1
      apply (rule isa_mark_failed_lits_stack_isa_mark_failed_lits_stack[THEN
	   fref_to_Down_curry2, of \<A> x2 x2y0 x1j x2e x2z x1l vdom x2, THEN order_trans])
      subgoal using assms by fast
      subgoal using that x2z by (auto simp: list_rel_imp_same_length[symmetric]
        isa_get_literal_and_remove_of_analyse_wl_def
        get_literal_and_remove_of_analyse_wl2_def) (* slow *)
      subgoal using that x2z inv by auto
      apply (rule order_trans)
      apply (rule ref_two_step')
      apply (rule mark_failed_lits_stack_mark_failed_lits_wl[THEN
	   fref_to_Down_curry2, of \<A> x2 x2y0 x1j])
      subgoal using inv x2z that by auto
      subgoal using that by auto
      subgoal by auto
      done
  qed
  have isa_mark_failed_lits_stack2: \<open>isa_mark_failed_lits_stack x2e x2z x1l
	\<le> \<Down> (cach_refinement \<A>) (mark_failed_lits_wl x2 x2y x1j)\<close>
    if
      \<open>case y of
       (x, xa) \<Rightarrow>
	 (case x of
	  (x, xa) \<Rightarrow>
	    (case x of
	     (x, xa) \<Rightarrow>
	       (case x of
		(x, xa) \<Rightarrow>
		  (case x of
		   (uu_, N) \<Rightarrow>
		     \<lambda>_ _ _ _.
			literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> ((mset \<circ> fst) `# ran_m N))                 xa)
		xa)
	     xa)
	  xa\<close> and
      \<open>(x, y)
       \<in> trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f       lookup_clause_rel \<A> \<times>\<^sub>f       cach_refinement \<A> \<times>\<^sub>f       Id \<times>\<^sub>f
	 Id\<close> and
      \<open>ana_lookup_conv_lookup x2e (x1q, x1r, x2r) = (x1v, x2v)\<close> and
      \<open>x1v < length x2e\<close> and
      \<open>arena_is_valid_clause_idx x2e x1v\<close> and
      \<open>arena_lit_pre x2e (x1v + x1w)\<close> and
      \<open>\<not> x2x \<le> x1x\<close> and
      \<open>\<not> x2u \<le> x1u\<close> and
      \<open>isa_get_literal_and_remove_of_analyse_wl_pre x2e x1m\<close> and
      \<open>get_literal_and_remove_of_analyse_wl2 (x2 \<propto> x1s) x1k = (x1y, x2y)\<close> and
      \<open>isa_get_literal_and_remove_of_analyse_wl x2e x1m = (x1z, x2z)\<close> and
      \<open>x1y \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and    \<open>get_level_pol_pre (x1i, x1z)\<close> and
      \<open>atm_in_conflict_lookup_pre (atm_of x1z) x2f\<close> and
      \<open>conflict_min_cach_l_pre (x1l, atm_of x1z)\<close> and
      \<open>\<not> (get_level_pol x1i x1z = 0 \<or>
	  conflict_min_cach_l x1l (atm_of x1z) = SEEN_REMOVABLE \<or>
	  atm_in_conflict_lookup (atm_of x1z) x2f)\<close> and
      \<open>\<not> (get_level x1d x1y = 0 \<or>
	  conflict_min_cach x1j (atm_of x1y) = SEEN_REMOVABLE \<or>
	  atm_in_conflict (atm_of x1y) x2a)\<close> and
      \<open>\<not> (\<not> level_in_lbd (get_level_pol x1i x1z) x2i \<or>
	  conflict_min_cach_l x1l (atm_of x1z) = SEEN_FAILED)\<close> and
      \<open>\<not> (\<not> level_in_lbd (get_level x1d x1y) x2d \<or>
	  conflict_min_cach x1j (atm_of x1y) = SEEN_FAILED)\<close> and
      \<open>- x1y \<in> lits_of_l x1d\<close> and
      \<open>(xb, x'a) \<in> \<langle>nat_rel\<rangle>option_rel\<close> and
      \<open>xb = None\<close> and
      \<open>x'a = None\<close> and
      inv2: \<open>mark_failed_lits_stack_inv2 x2 x2y x1j\<close> and
      \<open>(xa, x') \<in> cach_refinement \<A> \<times>\<^sub>f (Id \<times>\<^sub>f bool_rel)\<close> and    \<open>case xa of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      \<open>case x' of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      \<open>lit_redundant_rec_wl_inv2 x1d x2 x2a x'\<close> and
      \<open>x2j = (x1k, x2k)\<close> and
      \<open>x' = (x1j, x2j)\<close> and
      \<open>x2l = (x1m, x2m)\<close> and
      \<open>xa = (x1l, x2l)\<close> and
      \<open>x1k \<noteq> []\<close> and
      \<open>x1m \<noteq> []\<close> and
      \<open>x2o = (x1p, x2p)\<close> and
      \<open>x2n = (x1o, x2o)\<close> and
      \<open>ana_lookup_conv x2 (last x1k) = (x1n, x2n)\<close> and
      \<open>x2q = (x1r, x2r)\<close> and
      \<open>last x1m = (x1q, x2q)\<close> and
      \<open>x1n \<in># dom_m x2\<close> and
      \<open>x1o < length (x2 \<propto> x1n)\<close> and
      \<open>x2 \<propto> x1n ! x1o \<in> lits_of_l x1d\<close> and
      \<open>x2 \<propto> x1n ! x1o \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and
      \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (x2 \<propto> x1n))\<close> and
      \<open>length (x2 \<propto> x1n) \<le> Suc (uint32_max div 2)\<close> and
      \<open>x2p \<le> length (x2 \<propto> x1n)\<close> and
      \<open>arena_is_valid_clause_idx x2e (fst (last x1m))\<close> and
      \<open>x2t = (x1u, x2u)\<close> and
      \<open>x2s = (x1t, x2t)\<close> and
      \<open>(x1n, x1o, x1p, x2p) = (x1s, x2s)\<close> and
      \<open>x2w = (x1x, x2x)\<close> and
      \<open>x2v = (x1w, x2w)\<close> and
      \<open>x1c = (x1d, x2)\<close> and
      \<open>x1b = (x1c, x2a)\<close> and
      \<open>x1a = (x1b, x2b)\<close> and
      \<open>x1 = (x1a, x2c)\<close> and
      \<open>y = (x1, x2d)\<close> and
      \<open>x1h = (x1i, x2e)\<close> and
      \<open>x1g = (x1h, x2f)\<close> and
      \<open>x1f = (x1g, x2g)\<close> and
      \<open>x1e = (x1f, x2h)\<close> and
      \<open>x = (x1e, x2i)\<close> and
      \<open>length x1m \<le> 1 + uint32_max div 2\<close>
    for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q
       x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y x1z
       x2z xb x'a
  proof -
    have [simp]: \<open>x2z = x2y\<close>
      using that
      by (auto simp: isa_get_literal_and_remove_of_analyse_wl_def
	get_literal_and_remove_of_analyse_wl2_def)

    obtain x2y0 where
      x2z: \<open>(x2y, x2y0) \<in> ana_lookups_rel x2\<close> and
      inv: \<open>mark_failed_lits_stack_inv x2 x2y0 x1j\<close>
      using inv2 unfolding mark_failed_lits_stack_inv2_def
      by blast
    have 1: \<open>mark_failed_lits_wl x2 x2y x1j  = mark_failed_lits_wl x2 x2y0 x1j\<close>
      unfolding mark_failed_lits_wl_def by auto
    show ?thesis
      unfolding 1
      apply (rule isa_mark_failed_lits_stack_isa_mark_failed_lits_stack[THEN
	   fref_to_Down_curry2, of  \<A> x2 x2y0 x1j x2e x2z x1l vdom x2, THEN order_trans])
      subgoal using assms by fast
      subgoal using that x2z by (auto simp: list_rel_imp_same_length[symmetric]
        isa_get_literal_and_remove_of_analyse_wl_def
        get_literal_and_remove_of_analyse_wl2_def)
      subgoal using that x2z inv by auto
      apply (rule order_trans)
      apply (rule ref_two_step')
      apply (rule mark_failed_lits_stack_mark_failed_lits_wl[THEN
	   fref_to_Down_curry2, of \<A> x2 x2y0 x1j])
      subgoal using inv x2z that by auto
      subgoal using that by auto
      subgoal by auto
      done
  qed
  have [refine0]: \<open>get_propagation_reason_pol M' L'
    \<le> \<Down> (\<langle>Id\<rangle>option_rel)
       (get_propagation_reason M L)\<close>
    if \<open>(M', M) \<in> trail_pol \<A>\<close> and \<open>(L', L) \<in> Id\<close> and \<open>L \<in> lits_of_l M\<close>
    for M M' L L'
    using get_propagation_reason_pol[of \<A>, THEN fref_to_Down_curry, of M L M' L'] that by auto
  note [simp]=get_literal_and_remove_of_analyse_wl_def isa_get_literal_and_remove_of_analyse_wl_def
    arena_lifting and [split] = prod.splits

  show ?thesis
    supply [[goals_limit=1]] ana_lookup_conv_def[simp] ana_lookup_conv_lookup_def[simp]
    supply RETURN_as_SPEC_refine[refine2 add]
    unfolding isa_lit_redundant_rec_wl_lookup_alt_def lit_redundant_rec_wl_lookup_alt_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m
        by (auto simp: arena_lifting)
    subgoal by (auto simp: trail_pol_alt_def)
    subgoal by (auto simp: arena_is_valid_clause_idx_def
      lit_redundant_rec_wl_inv2_def)
    subgoal by (auto simp: ana_lookup_conv_lookup_pre_def)
    subgoal by (auto simp: arena_is_valid_clause_idx_def)
    subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m
      by (auto simp: arena_lifting arena_is_valid_clause_idx_def)
    subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q
       x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x
      apply (auto simp: arena_is_valid_clause_idx_def lit_redundant_rec_wl_inv_def
        isa_get_literal_and_remove_of_analyse_wl_pre_def arena_lit_pre_def
        arena_is_valid_clause_idx_and_access_def lit_redundant_rec_wl_ref_def)
      by (rule_tac x = \<open>x1s\<close> in exI; auto simp: valid_arena_nempty)+
    subgoal by (auto simp: arena_lifting arena_is_valid_clause_idx_def
      lit_redundant_rec_wl_inv_def split: if_splits)
    subgoal using assms
      by (auto simp: arena_lifting arena_is_valid_clause_idx_def bind_rule_complete_RES conc_fun_RETURN
           in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def
          intro!: conflict_min_cach_set_removable[of \<A>,THEN fref_to_Down_curry, THEN order_trans]
	  dest: List.last_in_set)

   subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q
       x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x
      by (auto simp: arena_is_valid_clause_idx_def lit_redundant_rec_wl_inv_def
        isa_get_literal_and_remove_of_analyse_wl_pre_def arena_lit_pre_def
	uint32_max_def
        arena_is_valid_clause_idx_and_access_def lit_redundant_rec_wl_ref_def)
        (rule_tac x = x1s in exI; auto simp: uint32_max_def; fail)+
    subgoal by (auto simp: list_rel_imp_same_length)
    subgoal by (auto intro!: get_level_pol_pre
      simp: get_literal_and_remove_of_analyse_wl2_def)
    subgoal by (auto intro!: atm_in_conflict_lookup_pre
      simp: get_literal_and_remove_of_analyse_wl2_def)
    subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o
      by (auto intro!: conflict_min_cach_l_pre
      simp: get_literal_and_remove_of_analyse_wl2_def)
    subgoal
      by (auto simp: atm_in_conflict_lookup_atm_in_conflict[THEN fref_to_Down_unRET_uncurry_Id]
          nth_conflict_min_cach[THEN fref_to_Down_unRET_uncurry_Id] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
	  get_level_get_level_pol atms_of_def
          get_literal_and_remove_of_analyse_wl2_def
  	split: prod.splits)
        (subst (asm)  atm_in_conflict_lookup_atm_in_conflict[THEN fref_to_Down_unRET_uncurry_Id];
	  auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n atms_of_def; fail)+
    subgoal by (auto simp: get_literal_and_remove_of_analyse_wl2_def
	  split: prod.splits)
    subgoal by (auto simp: atm_in_conflict_lookup_atm_in_conflict[THEN fref_to_Down_unRET_uncurry_Id]
          nth_conflict_min_cach[THEN fref_to_Down_unRET_uncurry_Id] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
	  get_level_get_level_pol atms_of_def
      simp: get_literal_and_remove_of_analyse_wl2_def
  	split: prod.splits)
    apply (rule isa_mark_failed_lits_stack; assumption)
    subgoal by (auto simp: split: prod.splits)
    subgoal by (auto simp: split: prod.splits)
    subgoal by (auto simp: get_literal_and_remove_of_analyse_wl2_def
      split: prod.splits)
    apply assumption
    apply (rule isa_mark_failed_lits_stack2; assumption)
    subgoal by auto
    subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q
       x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y x1z
       x2z xb x'a xc x'b
       unfolding lit_redundant_reason_stack_wl_lookup_pre_def
      by (auto simp: lit_redundant_reason_stack_wl_lookup_pre_def arena_lit_pre_def
	arena_is_valid_clause_idx_and_access_def arena_is_valid_clause_idx_def
	simp: valid_arena_nempty  get_literal_and_remove_of_analyse_wl2_def
	  lit_redundant_reason_stack_wl_lookup_def
	  lit_redundant_reason_stack2_def
	intro!: exI[of _ x'b] bex_leI[of _ x'b])
    subgoal premises p for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q
       x2q x1r x2r x1s x2s x1t x2t x1u x2u xb x'a xc x'b
      using p
      by (auto simp add: lit_redundant_reason_stack_wl_lookup_def
        lit_redundant_reason_stack_def lit_redundant_reason_stack_wl_lookup_pre_def
	lit_redundant_reason_stack2_def get_literal_and_remove_of_analyse_wl2_def
	 arena_lifting[of x2e x2 vdom]) \<comment> \<open>I have no idea why @{thm arena_lifting} requires
	   to be instantiated.\<close>
    done
qed



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
    lits_NU: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf NU)\<close> and
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
          assms(7-22)[unfolded assms(1-8)],
          unfolded assms(1-8)[symmetric]])
    apply (rule order.trans)
     apply (rule ref_two_step'[OF iterate_over_conflict_spec[OF NU_P_D dist_D]])
    by (auto simp: conc_fun_RES)
qed

lemma (in -) lookup_conflict_upd_None_RETURN_def:
  \<open>RETURN oo lookup_conflict_upd_None = (\<lambda>(n, xs) i. RETURN (n- 1, xs [i := NOTIN]))\<close>
  by (auto intro!: ext)

definition isa_literal_redundant_wl_lookup ::
    "trail_pol \<Rightarrow> arena \<Rightarrow> lookup_clause_rel \<Rightarrow> conflict_min_cach_l
           \<Rightarrow> nat literal \<Rightarrow> lbd \<Rightarrow> (conflict_min_cach_l \<times> (nat \<times> nat \<times> bool) list \<times> bool) nres"
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
         Some C \<Rightarrow> do {
           ASSERT(lit_redundant_reason_stack_wl_lookup_pre (-L) NU C);
           isa_lit_redundant_rec_wl_lookup M NU D cach
	     [lit_redundant_reason_stack_wl_lookup (-L) NU C] lbd}
       | None \<Rightarrow> do {
           RETURN (cach, [], False)
       }
     }
  }\<close>

lemma in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>nD[intro]: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> atm_of L \<in># \<A>\<close>
  using in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n by blast

lemma isa_literal_redundant_wl_lookup_literal_redundant_wl_lookup:
  assumes \<open>isasat_input_bounded \<A>\<close>
  shows \<open>(uncurry5 isa_literal_redundant_wl_lookup, uncurry5 (literal_redundant_wl_lookup \<A>)) \<in>
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
    subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' xb x'a
       unfolding lit_redundant_reason_stack_wl_lookup_pre_def
      by (auto simp: lit_redundant_reason_stack_wl_lookup_pre_def arena_lit_pre_def
	arena_is_valid_clause_idx_and_access_def arena_is_valid_clause_idx_def
	simp: valid_arena_nempty
	intro!: exI[of _ xb])
    subgoal using assms by auto
    subgoal by auto
    subgoal for x y x1 x1a x1b x1c x1d x2 x2a x2b x2c x2d x1e x1f x1g x1h x1i x2e x2f x2g
       x2h x2i xa x' xb x'a
      by (simp add: lit_redundant_reason_stack_wl_lookup_def
        lit_redundant_reason_stack_def lit_redundant_reason_stack_wl_lookup_pre_def
	lit_redundant_reason_stack2_def
	 arena_lifting[of x2e x2 vdom]) \<comment> \<open>I have no idea why @{thm arena_lifting} requires
	   to be instantiated.\<close>
    done
qed

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
         (nxs, 1, s, outl);
     RETURN (D, s, outl)
  })\<close>


lemma isa_minimize_and_extract_highest_lookup_conflict_minimize_and_extract_highest_lookup_conflict:
  assumes \<open>isasat_input_bounded \<A>\<close>
  shows \<open>(uncurry5 isa_minimize_and_extract_highest_lookup_conflict,
    uncurry5 (minimize_and_extract_highest_lookup_conflict \<A>)) \<in>
    [\<lambda>(((((_, N), D), _), _), _). literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> ((mset \<circ> fst) `# ran_m N) \<and>
       \<not>tautology D]\<^sub>f
     trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f lookup_clause_rel \<A> \<times>\<^sub>f
         cach_refinement \<A> \<times>\<^sub>f Id  \<times>\<^sub>f Id \<rightarrow>
      \<langle>lookup_clause_rel \<A> \<times>\<^sub>r cach_refinement \<A> \<times>\<^sub>r Id\<rangle>nres_rel\<close>
proof -
  have init: \<open>((x2f, 1, x2g, x2i), x2a::nat literal multiset, 1, x2b, x2d)
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
    subgoal using assms by auto
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

definition lookup_merge_eq2
  :: \<open>nat literal \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> nat clause_l \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
        out_learned \<Rightarrow> (conflict_option_rel \<times> nat \<times> lbd \<times> out_learned) nres\<close> where
\<open>lookup_merge_eq2 L M N = (\<lambda>(_, zs) clvls lbd outl. do {
    ASSERT(length N = 2);
    let L' = (if N ! 0 = L then N ! 1 else N ! 0);
    ASSERT(get_level M L' \<le> Suc (uint32_max div 2));
    let lbd = lbd_write lbd (get_level M L');
    ASSERT(atm_of L' < length (snd zs));
    ASSERT(length outl < uint32_max);
    let outl = outlearned_add M L' zs outl;
    ASSERT(clvls < uint32_max);
    ASSERT(fst zs < uint32_max);
    let clvls = clvls_add M L' zs clvls;
    let zs = add_to_lookup_conflict L' zs;
    RETURN((False, zs), clvls, lbd, outl)
  })\<close>

definition merge_conflict_m_eq2
  :: \<open>nat literal \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> nat clause_l \<Rightarrow> nat clause option \<Rightarrow>
  (nat clause option \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
\<open>merge_conflict_m_eq2 L M Ni D =
    SPEC (\<lambda>(C, n, lbd, outl). C = Some (remove1_mset L (mset Ni) \<union># the D) \<and>
       n = card_max_lvl M (remove1_mset L (mset Ni) \<union># the D) \<and>
       out_learned M C outl)\<close>

lemma lookup_merge_eq2_spec:
  assumes
    o: \<open>((b, n, xs), Some C) \<in> option_lookup_clause_rel \<A>\<close> and
    dist: \<open>distinct D\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset D)\<close> and
    lits_tr: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<close> and
    n_d: \<open>no_dup M\<close> and
    tauto: \<open>\<not>tautology (mset D)\<close> and
    lits_C: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C\<close> and
    no_tauto: \<open>\<And>K. K \<in> set (remove1 L D) \<Longrightarrow> - K \<notin># C\<close>
    \<open>clvls = card_max_lvl M C\<close> and
    out: \<open>out_learned M (Some C) outl\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>  and
    le2: \<open>length D = 2\<close> and
    L_D: \<open>L \<in> set D\<close>
  shows
    \<open>lookup_merge_eq2 L M D (b, n, xs) clvls lbd outl \<le>
      \<Down>(option_lookup_clause_rel \<A> \<times>\<^sub>r Id \<times>\<^sub>r Id)
          (merge_conflict_m_eq2 L M D (Some C))\<close>
     (is \<open>_ \<le>  \<Down> ?Ref ?Spec\<close>)
proof -
  define lbd_upd where
     \<open>lbd_upd lbd i \<equiv> lbd_write lbd (get_level M (D!i))\<close> for lbd i
  let ?D = \<open>remove1 L D\<close>
  have le_D_le_upper[simp]: \<open>a < length D \<Longrightarrow> Suc (Suc a) \<le> uint32_max\<close> for a
    using simple_clss_size_upper_div2[of \<A> \<open>mset D\<close>] assms by (auto simp: uint32_max_def)
  have Suc_N_uint32_max: \<open>Suc n \<le> uint32_max\<close> and
     size_C_uint32_max: \<open>size C \<le> 1 + uint32_max div 2\<close> and
     clvls: \<open>clvls = card_max_lvl M C\<close> and
     tauto_C: \<open>\<not> tautology C\<close> and
     dist_C: \<open>distinct_mset C\<close> and
     atms_le_xs: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length xs\<close> and
     map: \<open>mset_as_position xs C\<close>
    using assms simple_clss_size_upper_div2[of \<A> C] mset_as_position_distinct_mset[of xs C]
      lookup_clause_rel_not_tautolgy[of n xs C] bounded
    unfolding option_lookup_clause_rel_def lookup_clause_rel_def
    by (auto simp: uint32_max_def)
  then have clvls_uint32_max: \<open>clvls \<le> 1 + uint32_max div 2\<close>
    using size_filter_mset_lesseq[of \<open>\<lambda>L. get_level M L = count_decided M\<close> C]
    unfolding uint32_max_def card_max_lvl_def by linarith
  have [intro]: \<open>((b, a, ba), Some C) \<in> option_lookup_clause_rel \<A> \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C \<Longrightarrow>
        Suc (Suc a) \<le> uint32_max\<close> for b a ba C
    using lookup_clause_rel_size[of a ba C, OF _ bounded] by (auto simp: option_lookup_clause_rel_def
        lookup_clause_rel_def uint32_max_def)
  have [simp]: \<open>remdups_mset C = C\<close>
    using o mset_as_position_distinct_mset[of xs C] by (auto simp: option_lookup_clause_rel_def
        lookup_clause_rel_def distinct_mset_remdups_mset_id)
  have \<open>\<not>tautology C\<close>
    using mset_as_position_tautology o by (auto simp: option_lookup_clause_rel_def
        lookup_clause_rel_def)
  have \<open>distinct_mset C\<close>
    using mset_as_position_distinct_mset[of _ C] o
    unfolding option_lookup_clause_rel_def lookup_clause_rel_def by auto
  have \<open>mset (tl outl) \<subseteq># C\<close>
     using out by (auto simp: out_learned_def)
  from size_mset_mono[OF this] have outl_le: \<open>length outl < uint32_max\<close>
    using simple_clss_size_upper_div2[OF bounded lits_C] dist_C tauto_C by (auto simp: uint32_max_def)
  define L' where \<open>L' \<equiv> if D ! 0 = L then D ! 1 else D ! 0\<close>
  have L'_all: \<open>L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
    using lits le2 by (cases D; cases \<open>tl D\<close>)
      (auto simp: L'_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
  then have L': \<open>atm_of L' \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    by (auto simp: atms_of_def)
  have DLL: \<open>mset D = {#L, L'#}\<close> \<open>set D = {L, L'}\<close> \<open>L \<noteq> L'\<close> \<open>remove1 L D = [L']\<close>
    using le2 L_D dist by (cases D; cases \<open>tl D\<close>; auto simp: L'_def; fail)+
  have \<open>- L' \<in># C \<Longrightarrow> False\<close> and [simp]: \<open>- L' \<notin># C\<close>
    using dist no_tauto by (auto simp: DLL)
  then have o': \<open>((False, add_to_lookup_conflict L' (n, xs)), Some ({#L'#} \<union># C))
    \<in> option_lookup_clause_rel \<A>\<close>
    using o L'_all unfolding option_lookup_clause_rel_def
    by (auto intro!: add_to_lookup_conflict_lookup_clause_rel)
  have [iff]: \<open>is_in_lookup_conflict (n, xs) L' \<longleftrightarrow> L' \<in># C\<close>
    using o mset_as_position_in_iff_nth[of xs C L'] L' no_tauto
    apply (auto simp: is_in_lookup_conflict_def option_lookup_clause_rel_def
         lookup_clause_rel_def DLL is_pos_neg_not_is_pos
        split: option.splits)
    by (smt \<open>- L' \<notin># C\<close> atm_of_uminus is_pos_neg_not_is_pos mset_as_position_in_iff_nth option.inject)
  have clvls_add: \<open>clvls_add M L' (n, xs) clvls = card_max_lvl M ({#L'#} \<union># C)\<close>
    by (cases \<open>L' \<in># C\<close>)
      (auto simp: clvls_add_def card_max_lvl_add_mset clvls add_mset_union
      dest!: multi_member_split)
  have out': \<open>out_learned M (Some ({#L'#} \<union># C)) (outlearned_add M L' (n, xs) outl)\<close>
    using out
    by (cases \<open>L' \<in># C\<close>)
      (auto simp: out_learned_def outlearned_add_def add_mset_union
      dest!: multi_member_split)

  show ?thesis
    unfolding lookup_merge_eq2_def prod.simps L'_def[symmetric]
    apply refine_vcg
    subgoal by (rule le2)
    subgoal using literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[OF bounded lits_tr n_d] by blast
    subgoal using atms_le_xs L' by simp
    subgoal using outl_le .
    subgoal using clvls_uint32_max by (auto simp: uint32_max_def)
    subgoal using Suc_N_uint32_max by auto
    subgoal
      using o' clvls_add out'
      by (auto simp: merge_conflict_m_eq2_def DLL
        intro!: RETURN_RES_refine)
    done
qed

definition isasat_lookup_merge_eq2
  :: \<open>nat literal \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow> nat \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
        out_learned \<Rightarrow> (conflict_option_rel \<times> nat \<times> lbd \<times> out_learned) nres\<close> where
\<open>isasat_lookup_merge_eq2 L M N C = (\<lambda>(_, zs) clvls lbd outl. do {
    ASSERT(arena_lit_pre N C);
    ASSERT(arena_lit_pre N (C+1));
    let L' = (if arena_lit N C = L then arena_lit N (C + 1) else arena_lit N C);
    ASSERT(get_level_pol_pre (M, L'));
    ASSERT(get_level_pol M L' \<le> Suc (uint32_max div 2));
    let lbd = lbd_write lbd (get_level_pol M L');
    ASSERT(atm_of L' < length (snd zs));
    ASSERT(length outl < uint32_max);
    let outl = isa_outlearned_add M L' zs outl;
    ASSERT(clvls < uint32_max);
    ASSERT(fst zs < uint32_max);
    let clvls = isa_clvls_add M L' zs clvls;
    let zs = add_to_lookup_conflict L' zs;
    RETURN((False, zs), clvls, lbd, outl)
  })\<close>

lemma isasat_lookup_merge_eq2_lookup_merge_eq2:
  assumes valid: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
    bxs: \<open>((b, xs), C) \<in> option_lookup_clause_rel \<A>\<close> and
    M'M: \<open>(M', M) \<in> trail_pol \<A>\<close> and
    bound: \<open>isasat_input_bounded \<A>\<close>
  shows
    \<open>isasat_lookup_merge_eq2 L M' arena i (b, xs) clvls lbd outl \<le> \<Down> Id
      (lookup_merge_eq2 L M (N \<propto> i) (b, xs) clvls lbd outl)\<close>
proof -
  define L' where \<open>L' \<equiv> (if arena_lit arena i = L then arena_lit arena (i + 1)
         else arena_lit arena i)\<close>
  define L'' where \<open>L'' \<equiv> (if N \<propto> i ! 0 = L then N \<propto> i ! 1 else N \<propto> i ! 0)\<close>

  have [simp]: \<open>L'' = L'\<close>
    if \<open>length (N \<propto> i) = 2\<close>
    using that i valid by (auto simp: L''_def L'_def arena_lifting)
  have L'_all: \<open>L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
    if \<open>length (N \<propto> i) = 2\<close>
    by (use lits i valid that
          literals_are_in_\<L>\<^sub>i\<^sub>n_mm_add_msetD[of \<A>
	    \<open>mset (N \<propto> i)\<close> _ \<open>arena_lit arena (Suc i)\<close>]
	  literals_are_in_\<L>\<^sub>i\<^sub>n_mm_add_msetD[of \<A>
	    \<open>mset (N \<propto> i)\<close> _ \<open>arena_lit arena i\<close>]
	  nth_mem[of 0 \<open>N \<propto> i\<close>] nth_mem[of 1 \<open>N \<propto> i\<close>]
	in \<open>auto simp: arena_lifting ran_m_def L'_def
	  simp del: nth_mem
	   dest:
	  dest!: multi_member_split\<close>)

  show ?thesis
    unfolding isasat_lookup_merge_eq2_def lookup_merge_eq2_def prod.simps
    L'_def[symmetric] L''_def[symmetric]
    apply refine_vcg
    subgoal
      using valid i
      unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
      by (auto intro!: exI[of _ i] exI[of _ N])
    subgoal
      using valid i
      unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
      by (auto intro!: exI[of _ i] exI[of _ N])
    subgoal
      by (rule get_level_pol_pre[OF _ M'M])
        (use L'_all
	in \<open>auto simp: arena_lifting ran_m_def
	  simp del: nth_mem
	   dest:
	  dest!: multi_member_split\<close>)
    subgoal
      by (subst get_level_get_level_pol[OF M'M, symmetric])
        (use L'_all in auto)
    subgoal by auto
    subgoal
      using M'M L'_all
      by (auto simp: isa_clvls_add_clvls_add get_level_get_level_pol
        isa_outlearned_add_outlearned_add)
    done
qed



definition merge_conflict_m_eq2_pre where
  \<open>merge_conflict_m_eq2_pre \<A> =
  (\<lambda>(((((((L, M), N), i), xs), clvls), lbd), out). i \<in># dom_m N \<and> xs \<noteq> None \<and> distinct (N \<propto> i) \<and>
       \<not>tautology (mset (N \<propto> i)) \<and>
       (\<forall>K \<in> set (remove1 L (N \<propto> i)). - K \<notin># the xs) \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (the xs) \<and> clvls = card_max_lvl M (the xs) \<and>
       out_learned M xs out \<and> no_dup M \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N) \<and>
       isasat_input_bounded \<A> \<and>
       length (N \<propto> i) = 2 \<and>
       L \<in> set (N \<propto> i))\<close>

definition merge_conflict_m_g_eq2 :: \<open>_\<close> where
\<open>merge_conflict_m_g_eq2 L M N i D _ _ _ = merge_conflict_m_eq2 L M (N \<propto> i) D\<close>

lemma isasat_lookup_merge_eq2:
  \<open>(uncurry7 isasat_lookup_merge_eq2, uncurry7 merge_conflict_m_g_eq2) \<in>
    [merge_conflict_m_eq2_pre \<A>]\<^sub>f
    Id \<times>\<^sub>f trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f nat_rel \<times>\<^sub>f option_lookup_clause_rel \<A>
        \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<times>\<^sub>f Id  \<rightarrow>
      \<langle>option_lookup_clause_rel \<A> \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<rangle>nres_rel\<close>
proof -
  have H1: \<open>isasat_lookup_merge_eq2 a (aa, ab, ac, ad, ae, b) ba bb (af, ag, bc) bd be
	 bf
	\<le> \<Down> Id (lookup_merge_eq2 a bg (bh \<propto> bb) (af, ag, bc) bd be bf)\<close>
    if
      \<open>merge_conflict_m_eq2_pre \<A> (((((((ah, bg), bh), bi), bj), bk), bl), bm)\<close> and
      \<open>((((((((a, aa, ab, ac, ad, ae, b), ba), bb), af, ag, bc), bd), be), bf),
	((((((ah, bg), bh), bi), bj), bk), bl), bm)
       \<in> Id \<times>\<^sub>f trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f       nat_rel \<times>\<^sub>f
	 option_lookup_clause_rel \<A> \<times>\<^sub>f       nat_rel \<times>\<^sub>f
	 Id \<times>\<^sub>f
	 Id\<close>
     for a aa ab ac ad ae b ba bb af ag bc bd be bf ah bg bh bi bj bk bl bm
  proof -
    have
      bi: \<open>bi \<in># dom_m bh\<close> and
      \<open>(bf, bm) \<in> Id\<close> and
      \<open>bj \<noteq> None\<close> and
      \<open>(be, bl) \<in> Id\<close> and
      \<open>distinct (bh \<propto> bi)\<close> and
      \<open>(bd, bk) \<in> nat_rel\<close> and
      \<open>\<not> tautology (mset (bh \<propto> bi))\<close> and
      o: \<open>((af, ag, bc), bj) \<in> option_lookup_clause_rel \<A>\<close> and
      \<open>\<forall>K\<in>set (remove1 ah (bh \<propto> bi)). - K \<notin># the bj\<close> and
      st: \<open>bb = bi\<close> and
      \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (the bj)\<close> and
      valid: \<open>valid_arena ba bh vdom\<close> and
      \<open>bk = card_max_lvl bg (the bj)\<close> and
      \<open>(a, ah) \<in> Id\<close> and
      tr: \<open>((aa, ab, ac, ad, ae, b), bg) \<in> trail_pol \<A>\<close> and
      \<open>out_learned bg bj bm\<close> and
      \<open>no_dup bg\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf bh)\<close> and
      bounded: \<open>isasat_input_bounded \<A>\<close> and
      ah: \<open>ah \<in> set (bh \<propto> bi)\<close>
      using that unfolding merge_conflict_m_eq2_pre_def prod.simps prod_rel_iff
      by blast+

  show ?thesis
      by (rule isasat_lookup_merge_eq2_lookup_merge_eq2[OF valid bi[unfolded st[symmetric]]
        lits o tr bounded])
  qed
  have H2: \<open>lookup_merge_eq2 a bg (bh \<propto> bb) (af, ag, bc) bd be bf
	\<le> \<Down> (option_lookup_clause_rel \<A> \<times>\<^sub>f (nat_rel \<times>\<^sub>f (Id \<times>\<^sub>f Id)))
	(merge_conflict_m_g_eq2 ah bg bh bi bj bk bl bm)\<close>
    if
      \<open>merge_conflict_m_eq2_pre \<A>      (((((((ah, bg), bh), bi), bj), bk), bl), bm)\<close> and
      \<open>((((((((a, aa, ab, ac, ad, ae, b), ba), bb), af, ag, bc), bd), be), bf),
	((((((ah, bg), bh), bi), bj), bk), bl), bm)
       \<in> Id \<times>\<^sub>f trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f       nat_rel \<times>\<^sub>f
	 option_lookup_clause_rel \<A> \<times>\<^sub>f       nat_rel \<times>\<^sub>f
	 Id \<times>\<^sub>f
	 Id\<close>
    for a aa ab ac ad ae b ba bb af ag bc bd be bf ah bg bh bi bj bk bl bm
  proof -
    have
      bi: \<open>bi \<in># dom_m bh\<close> and
      bj: \<open>bj \<noteq> None\<close> and
      dist: \<open>distinct (bh \<propto> bi)\<close> and
      tauto: \<open>\<not> tautology (mset (bh \<propto> bi))\<close> and
      o: \<open>((af, ag, bc), bj) \<in> option_lookup_clause_rel \<A>\<close> and
      K: \<open>\<forall>K\<in>set (remove1 ah (bh \<propto> bi)). - K \<notin># the bj\<close> and
      st: \<open>bb = bi\<close>
        \<open>bd = bk\<close>
	\<open>bf = bm\<close>
	\<open>be = bl\<close>
        \<open>a = ah\<close> and
      lits_confl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (the bj)\<close> and
      valid: \<open>valid_arena ba bh vdom\<close> and
      bk: \<open>bk = card_max_lvl bg (the bj)\<close> and
      tr: \<open>((aa, ab, ac, ad, ae, b), bg) \<in> trail_pol \<A>\<close> and
      out: \<open>out_learned bg bj bm\<close> and
      \<open>no_dup bg\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf bh)\<close> and
      bounded: \<open>isasat_input_bounded \<A>\<close> and
      le2: \<open>length (bh \<propto> bi) = 2\<close> and
      ah: \<open>ah \<in> set (bh \<propto> bi)\<close>
      using that unfolding merge_conflict_m_eq2_pre_def prod.simps prod_rel_iff
      by blast+
    obtain bj' where bj': \<open>bj = Some bj'\<close>
      using bj by (cases bj) auto
    have n_d: \<open>no_dup bg\<close> and lits_tr: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> bg\<close>
      using tr unfolding trail_pol_alt_def
      by auto
    have lits_bi: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (bh \<propto> bi))\<close>
      using bi lits by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_add_mset ran_m_def
        dest!: multi_member_split)

    show ?thesis
      unfolding st merge_conflict_m_g_eq2_def
      apply (rule lookup_merge_eq2_spec[THEN order_trans, OF o[unfolded bj']
        dist lits_bi lits_tr n_d tauto lits_confl[unfolded bj' option.sel]
        _ bk[unfolded bj' option.sel] _ bounded le2 ah])
      subgoal using K unfolding bj' by auto
      subgoal using out unfolding bj' .
      subgoal unfolding bj' by auto
      done
  qed

  show ?thesis
    unfolding lookup_conflict_merge_def uncurry_def
    apply (intro nres_relI frefI)
    apply clarify
    subgoal for a aa ab ac ad ae b ba bb af ag bc bd be bf ah bg bh bi bj bk bl bm
      apply (rule H1[THEN order_trans]; assumption?)
      apply (subst Down_id_eq)
      apply (rule H2)
      apply assumption+
      done
    done
qed

end
