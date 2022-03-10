theory IsaSAT_Mark
  imports
    IsaSAT_Clauses
    IsaSAT_Watch_List
    IsaSAT_Trail
begin

chapter \<open>Clauses Encoded as Positions\<close>

text \<open>We use represent the conflict in two data structures close to the one used by the most SAT
solvers: We keep an array that represent the clause (for efficient iteration on the clause) and a
``hash-table'' to efficiently test if a literal belongs to the clause.

The first data structure is simply an array to represent the clause. This theory is only about
the second data structure. We refine it from the clause (seen as a multiset) in two steps:
  \<^enum> First, we represent the clause as a ``hash-table'', where the \<^term>\<open>i\<close>-th position indicates
    \<^term>\<open>Some True\<close> (respectively \<^term>\<open>Some False\<close>, \<^term>\<open>None\<close>) if \<^term>\<open>Pos i\<close> is present in the
    clause (respectively \<^term>\<open>Neg i\<close>, not at all). This allows to represent every not-tautological
    clause whose literals fits in the underlying array.

We use the first part in two different ways: once for the conflict, where we specialize it to
include only information on the atoms and once in the marking structure.
\<close>

text \<open>This is the first level of the refinement. We tried a few different definitions (including a
direct one, i.e., mapping a position to the inclusion in the set) but the inductive version turned out
to the easiest one to use.
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
    c: \<open>((n,xs), C) \<in> lookup_clause_rel \<A>\<close>
  shows
    lookup_clause_rel_not_tautolgy: \<open>\<not>tautology C\<close> and
    lookup_clause_rel_distinct_mset: \<open>distinct_mset C\<close> and
    lookup_clause_rel_size: \<open>isasat_input_bounded \<A> \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C \<Longrightarrow> size C \<le> 1 + uint32_max div 2\<close>
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
  then show \<open>isasat_input_bounded \<A> \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C \<Longrightarrow> size C \<le> 1 + uint32_max div 2\<close>
    using simple_clss_size_upper_div2[of \<A> \<open>C\<close>] \<open>\<not>tautology C\<close> by auto
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

lemma mset_as_position_remove2:
  \<open>mset_as_position xs D \<Longrightarrow> atm_of L < length xs \<Longrightarrow>
   mset_as_position (xs[atm_of L := None]) (D - {#L, -L#})\<close>
  using mset_as_position_remove[of xs D \<open>atm_of (-L)\<close>]
  by (smt add_mset_commute add_mset_diff_bothsides atm_of_uminus insert_DiffM
   literal.exhaust_sel minus_notin_trivial2 remove_1_mset_id_iff_notin uminus_not_id')

lemma mset_as_position_remove3:
  \<open>mset_as_position xs (D - {#L#}) \<Longrightarrow> atm_of L < length xs \<Longrightarrow> distinct_mset D \<Longrightarrow>
   mset_as_position (xs[atm_of L := None]) (D - {#L, -L#})\<close>
  using mset_as_position_remove2[of xs \<open>D - {#L#}\<close> \<open>L\<close>] mset_as_position_tautology[of xs \<open>remove1_mset L D\<close>]
    mset_as_position_distinct_mset[of xs \<open>remove1_mset L D\<close>]
  by (cases \<open>L \<in># D\<close>; cases \<open>-L \<in># D\<close>)
    (auto dest!: multi_member_split simp: minus_notin_trivial ac_simps add_mset_eq_add_mset tautology_add_mset)

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


definition add_to_lookup_conflict :: \<open>nat literal \<Rightarrow> lookup_clause_rel \<Rightarrow> lookup_clause_rel\<close> where
  \<open>add_to_lookup_conflict = (\<lambda>L (n, xs). (if xs ! atm_of L = NOTIN then n + 1 else n,
      xs[atm_of L := ISIN (is_pos L)]))\<close>



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
      using True by (metis mset_contains_eq union_mset_def)
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

definition pre_simplify_clause_inv where
  \<open>pre_simplify_clause_inv C = (\<lambda>(i, tauto, D, D').
    i \<le> length C \<and> (\<not>tauto \<longleftrightarrow> \<not>tautology (mset (take i C))) \<and>
    (\<not>tauto \<longrightarrow> D = remdups_mset (mset (take i C))) \<and>
    set D' \<subseteq> set C \<and>
    mset D' = D \<and>
    \<not>tautology D \<and>
    distinct_mset D)\<close>

definition pre_simplify_clause :: \<open>'v clause_l \<Rightarrow> (bool \<times> 'v clause_l) nres\<close> where
  \<open>pre_simplify_clause C = do {
     (_, tauto, D\<^sub>0, D) \<leftarrow>
       WHILE\<^sub>T\<^bsup> pre_simplify_clause_inv C\<^esup>
         (\<lambda>(i, tauto, D, D'). i < length C \<and> \<not>tauto)
         (\<lambda>(i, tauto, D, D'). do {
           ASSERT(i < length C);
           let L = C!i;
           if -L \<in># D
           then RETURN (i+1,True, D, D')
           else if L \<in># D
           then RETURN (i+1, tauto, D, D')
           else RETURN (i+1,tauto, add_mset L D, D' @ [L])
         })
         (0, False, {#}, []);
     ASSERT(D\<^sub>0 = mset D \<and> set D \<subseteq> set C);
     RETURN (tauto, D)
  }\<close>

definition pre_simplify_clause_spec where
  \<open>pre_simplify_clause_spec C = (\<lambda>(tauto, D).
    (tauto \<longleftrightarrow> tautology (mset C)) \<and>
    (\<not>tauto \<longrightarrow> mset D = remdups_mset (mset C)))\<close>

lemma pre_simplify_clause_spec:
  \<open>pre_simplify_clause C \<le>  \<Down> Id (SPEC(pre_simplify_clause_spec C))\<close>
proof -
  have [refine0]: \<open>wf (measure (\<lambda>(i, _). length C - i))\<close>
    by auto
  show ?thesis
    unfolding pre_simplify_clause_def
    apply refine_vcg
    subgoal by (auto simp: pre_simplify_clause_inv_def)
    subgoal by auto
    subgoal for state i b tauto ba D D'
      by (auto simp: pre_simplify_clause_inv_def
        take_Suc_conv_app_nth tautology_add_mset)
    subgoal
      by auto
    subgoal for state i b tauto ba D D'
      by (auto simp: pre_simplify_clause_inv_def
        take_Suc_conv_app_nth tautology_add_mset)
    subgoal
      by auto
    subgoal for state i b tauto ba D D'
      by (auto simp: pre_simplify_clause_inv_def
        take_Suc_conv_app_nth tautology_add_mset)
    subgoal
      by auto
    subgoal by (auto simp: pre_simplify_clause_inv_def)
    subgoal by (auto simp: pre_simplify_clause_inv_def)
    subgoal for state i b tauto ba D D'
      using not_tautology_mono[of \<open>mset (take i C)\<close> \<open>mset C\<close>]
      by (auto simp: pre_simplify_clause_inv_def mset_take_subseteq
        pre_simplify_clause_spec_def)
    done
qed

definition (in -) lit_is_in_lookup where
  \<open>lit_is_in_lookup = (\<lambda>L (n, xs). do {
     ASSERT(atm_of L < length xs);
     RETURN ((xs ! atm_of L) = Some (is_pos L))})\<close>

definition unmark_clause :: \<open>_\<close> where
  \<open>unmark_clause C lup = do {
     (_, lup) \<leftarrow> WHILE\<^sub>T
       (\<lambda>(i,lup). i < length C)
        (\<lambda>(i,lup).  do {
          ASSERT(i < length C);
          lup \<leftarrow> delete_from_lookup_conflict (C!i) lup;
          RETURN (i+1, lup)
       })
       (0, lup);
     RETURN lup
  }\<close>

lemma unmark_clause_spec:
  assumes \<open>(lup, mset C) \<in> lookup_clause_rel \<A>\<close> \<open>atm_of ` set C \<subseteq> set_mset \<A>\<close>
  shows \<open>unmark_clause C lup \<le> (SPEC(\<lambda>lup'. (lup', {#}) \<in> lookup_clause_rel \<A>))\<close>
proof -
  have [refine]: \<open>wf (measure (\<lambda>(i, _). length C - i))\<close>
    by auto
  show ?thesis
    unfolding unmark_clause_def
    apply (refine_vcg WHILET_rule[where R = \<open>measure (\<lambda>(i, _). length C - i)\<close> and
      I = \<open>\<lambda>(i,lup). (lup, mset (drop i C)) \<in> lookup_clause_rel \<A>\<close>])
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal for s a b
      using lookup_clause_rel_not_tautolgy[of \<open>fst b\<close> \<open>snd b\<close> \<open>mset (drop a C)\<close>] assms(2) apply -
      apply (rule 
        delete_from_lookup_conflict_op_mset_delete[of \<A>, THEN fref_to_Down_curry,
          of \<open>C!a\<close> \<open>mset (drop a C)\<close>, THEN order_trans])
      by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n conc_fun_RES RETURN_def tautology_add_mset
        simp flip: Cons_nth_drop_Suc)
    subgoal
      by auto
    done
qed

lemma lit_is_in_lookup_spec:
  assumes \<open>(lup, C) \<in> lookup_clause_rel \<A>\<close> \<open>atm_of L \<in># \<A>\<close>
  shows \<open>lit_is_in_lookup L lup = RES {L \<in># C}\<close>
  using assms unfolding lit_is_in_lookup_def
  apply refine_rcg
  using mset_as_position_in_iff_nth[of \<open>snd lup\<close> C L]
  by (auto simp: lit_is_in_lookup_def lookup_clause_rel_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
    dest: multi_member_split
    dest: mset_as_position_nth)

definition pre_simplify_clause_lookup
  :: \<open>nat clause_l \<Rightarrow>  nat clause_l \<Rightarrow> lookup_clause_rel \<Rightarrow>
    (bool \<times> nat clause_l \<times> lookup_clause_rel) nres\<close>
where
  \<open>pre_simplify_clause_lookup C D lup = do {
  ASSERT(D = []);
  (_, tauto, lup, D) \<leftarrow>
  WHILE\<^sub>T\<^bsup> \<lambda>_. True\<^esup>
    (\<lambda>(i, tauto, D, D'). i < length C \<and> \<not>tauto)
    (\<lambda>(i, tauto, D, D'). do {
      ASSERT(i < length C);
      ASSERT(fst D < uint32_max \<and> atm_of (C!i) < length (snd D));
      ASSERT(length D' = fst D);
      let L = C!i;
      b \<leftarrow> lit_is_in_lookup (-L) D;
      if b
      then RETURN (i+1,True, D, D')
      else do {
        b \<leftarrow> lit_is_in_lookup L D;
        if b
        then RETURN (i+1, tauto, D, D')
        else RETURN (i+1,tauto, add_to_lookup_conflict L D, D' @ [L])
      }
    })
    (0, False, lup, D);
  lup \<leftarrow> unmark_clause D lup;
  RETURN (tauto, D, lup)
}\<close>

lemma pre_simplify_clause_lookup_pre_simplify_clause:
  assumes \<open>(lup, {#}) \<in> lookup_clause_rel \<A>\<close> \<open>atm_of ` set C \<subseteq> set_mset \<A>\<close>
      \<open>isasat_input_bounded \<A>\<close> and
    [simp]: \<open>E = []\<close>
  shows \<open>pre_simplify_clause_lookup C E lup \<le>
    \<Down>{((tauto, D, lup), (tauto', D')). tauto=tauto' \<and> D=D' \<and> (lup, {#}) \<in> lookup_clause_rel \<A>}
      (pre_simplify_clause C)\<close>
proof -
  have [refine0]: \<open>((0, False, lup, E), 0, False, {#}, []) \<in>
     nat_rel \<times>\<^sub>r bool_rel \<times>\<^sub>r lookup_clause_rel \<A> \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<close>
    using assms by auto
  have [simp]: \<open>x < length C \<Longrightarrow> atm_of (- C ! x) \<in># \<A>\<close>
    \<open>x < length C \<Longrightarrow> atm_of (C ! x) \<in># \<A>\<close> for x
    using assms by auto
  show ?thesis
    using assms
    unfolding pre_simplify_clause_lookup_def pre_simplify_clause_def
    apply (refine_vcg lit_is_in_lookup_spec lhs_step_If)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
      using simple_clss_size_upper_div2[of \<A> \<open>mset x2b\<close>] assms
      unfolding  literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def apply -
      by (subgoal_tac \<open>atm_of ` set (take x1 C) \<subseteq> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>)   
        (auto simp: lit_is_in_lookup_spec in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n pre_simplify_clause_inv_def
        lookup_clause_rel_def uint32_max_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n dest!: in_set_takeD)
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
      using simple_clss_size_upper_div2[of \<A> \<open>mset x2b\<close>] assms
      unfolding  literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def apply -
      by (subgoal_tac \<open>atm_of ` set (take x1 C) \<subseteq> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>)   
        (auto simp: lit_is_in_lookup_spec in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n pre_simplify_clause_inv_def
        lookup_clause_rel_def uint32_max_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n dest!: in_set_takeD)
    subgoal by (clarsimp simp add: lookup_clause_rel_def pre_simplify_clause_inv_def
      simp del: size_mset simp flip: size_mset)
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
      using add_to_lookup_conflict_lookup_clause_rel[of \<open>fst x1e\<close> \<open>snd x1e\<close> x1b \<A> \<open>C ! x1\<close>]
      by (auto simp: lit_is_in_lookup_spec in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
      by (rule unmark_clause_spec[of _ _ \<A>, THEN order_trans])
        auto
    done
qed

end
