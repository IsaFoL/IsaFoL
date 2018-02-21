theory IsaSAT_Lookup_Conflict
  imports Watched_Literals_Watch_List_Domain
    Watched_Literals_Watch_List_Code_Common
    IsaSAT_Trail
    CDCL_Conflict_Minimisation
    "../lib/Explorer"
    LBD
    IsaSAT_Clauses
begin

no_notation Ref.update ("_ := _" 62)


subsubsection \<open>Clauses Encoded as Positions\<close>

inductive mset_as_position :: \<open>bool option list \<Rightarrow> nat literal multiset \<Rightarrow> bool\<close>where
empty:
  \<open>mset_as_position (replicate n None) {#}\<close> |
add:
  \<open>mset_as_position xs' (add_mset L P)\<close>
   if \<open>mset_as_position xs P\<close> \<open>atm_of L < length xs\<close> and \<open>L \<notin># P\<close> and \<open>-L \<notin># P\<close> and
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

context isasat_input_ops
begin

type_synonym (in -) lookup_clause_rel = \<open>nat \<times> bool option list\<close>

definition lookup_clause_rel :: \<open>(lookup_clause_rel \<times> nat literal multiset) set\<close> where
\<open>lookup_clause_rel = {((n, xs), C). n = size C \<and> mset_as_position xs C \<and>
   (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs)}\<close>

lemma lookup_clause_rel_empty_iff: \<open>((n, xs), C) \<in> lookup_clause_rel \<Longrightarrow> n = 0 \<longleftrightarrow> C = {#}\<close>
  by (auto simp: lookup_clause_rel_def)

lemma conflict_atm_le_length: \<open>((n, xs), C) \<in> lookup_clause_rel \<Longrightarrow> L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow>
   L < length xs\<close>
  by (auto simp: lookup_clause_rel_def)


lemma conflict_le_length:
  assumes
    c_rel: \<open>((n, xs), C) \<in> lookup_clause_rel\<close> and
    L_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  shows \<open>atm_of L < length xs\<close>
proof -
  have
    size: \<open>n = size C\<close> and
    mset_pos: \<open>mset_as_position xs C\<close> and
    atms_le: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close>
    using c_rel unfolding lookup_clause_rel_def by blast+
  have \<open>atm_of L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using L_\<L>\<^sub>a\<^sub>l\<^sub>l by (simp add: atms_of_def)
  then show ?thesis
    using atms_le by blast
qed

lemma lookup_clause_rel_atm_in_iff:
  \<open>((n, xs), C) \<in> lookup_clause_rel \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> L \<in>#C \<longleftrightarrow> xs!(atm_of L) = Some (is_pos L)\<close>
  by (rule mset_as_position_in_iff_nth)
     (auto simp: lookup_clause_rel_def atms_of_def)

lemma (in isasat_input_bounded)
  assumes c: \<open>((n,xs), C) \<in> lookup_clause_rel\<close>
  shows
    lookup_clause_rel_not_tautolgy: \<open>\<not>tautology C\<close> and
    lookup_clause_rel_distinct_mset: \<open>distinct_mset C\<close> and
    lookup_clause_rel_size: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C \<Longrightarrow> size C \<le> 1 + uint_max div 2\<close>
proof -
  have mset: \<open>mset_as_position xs C\<close> and \<open>n = size C\<close> and \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close>
    using c unfolding lookup_clause_rel_def by fast+
  show \<open>\<not>tautology C\<close>
    using mset
    apply (induction rule: mset_as_position.induct)
    subgoal by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def)
    subgoal by (auto simp: tautology_add_mset)
    done
  show \<open>distinct_mset C\<close>
    using mset mset_as_position_distinct_mset by blast
  then show \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C \<Longrightarrow> size C \<le> 1 + uint_max div 2\<close>
    using simple_clss_size_upper_div2[of \<open>C\<close>] \<open>\<not>tautology C\<close> by auto
qed

type_synonym (in -) lookup_clause_assn = \<open>uint32 \<times> bool option array\<close>

definition lookup_clause_assn :: \<open>nat clause \<Rightarrow> lookup_clause_assn \<Rightarrow> assn\<close> where
\<open>lookup_clause_assn =
   hr_comp (uint32_nat_assn *a array_assn (option_assn bool_assn)) lookup_clause_rel\<close>

definition option_lookup_clause_rel where
\<open>option_lookup_clause_rel = {((b,(n,xs)), C). b = (C = None) \<and>
   (C = None \<longrightarrow> ((n,xs), {#}) \<in> lookup_clause_rel) \<and>
   (C \<noteq> None \<longrightarrow> ((n,xs), the C) \<in> lookup_clause_rel)}
   \<close>

lemma option_lookup_clause_rel_lookup_clause_rel_iff:
   \<open>((False, (n, xs)), Some C) \<in> option_lookup_clause_rel \<longleftrightarrow>
   ((n, xs), C) \<in> lookup_clause_rel\<close>
   unfolding option_lookup_clause_rel_def by auto


type_synonym (in -) option_lookup_clause_assn = \<open>bool \<times> uint32 \<times> bool option array\<close>

abbreviation (in -) lookup_clause_rel_assn
  :: \<open>lookup_clause_rel \<Rightarrow> lookup_clause_assn \<Rightarrow> assn\<close>
where
 \<open>lookup_clause_rel_assn \<equiv> (uint32_nat_assn *a array_assn (option_assn bool_assn))\<close>

type_synonym (in -) conflict_option_rel = \<open>bool \<times> nat \<times> bool option list\<close>

abbreviation (in -)conflict_option_rel_assn
  :: \<open>conflict_option_rel \<Rightarrow> option_lookup_clause_assn \<Rightarrow> assn\<close>
where
 \<open>conflict_option_rel_assn \<equiv> (bool_assn *a lookup_clause_rel_assn)\<close>

definition option_lookup_clause_assn
  :: \<open>nat clause option \<Rightarrow> option_lookup_clause_assn \<Rightarrow> assn\<close>
where
  \<open>option_lookup_clause_assn =
     hr_comp (bool_assn *a uint32_nat_assn *a array_assn (option_assn bool_assn))
       option_lookup_clause_rel\<close>

definition (in -) lookup_clause_assn_is_None :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>lookup_clause_assn_is_None = (\<lambda>(b, _, _). b)\<close>

lemma lookup_clause_assn_is_None_is_None:
  \<open>(RETURN o lookup_clause_assn_is_None, RETURN o is_None) \<in>
   option_lookup_clause_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
   (auto simp: option_lookup_clause_rel_def lookup_clause_assn_is_None_def split: option.splits)

lemma lookup_clause_assn_is_None_lookup_clause_assn_is_None:
 \<open>(return o lookup_clause_assn_is_None, RETURN o lookup_clause_assn_is_None) \<in>
  conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: lookup_clause_assn_is_None_def)

lemma lookup_clause_assn_is_None_is_none_Code[sepref_fr_rules]:
  \<open>(return \<circ> lookup_clause_assn_is_None, RETURN \<circ> is_None) \<in> option_lookup_clause_assn\<^sup>k \<rightarrow>\<^sub>a
    bool_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
  using lookup_clause_assn_is_None_lookup_clause_assn_is_None[FCOMP
      lookup_clause_assn_is_None_is_None,
  unfolded option_lookup_clause_assn_def[symmetric]] .

definition (in -) lookup_clause_assn_is_empty :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>lookup_clause_assn_is_empty = (\<lambda>(_, n, _). n = 0)\<close>

lemma lookup_clause_assn_is_empty_is_empty:
  \<open>(RETURN o lookup_clause_assn_is_empty, RETURN o (\<lambda>D. Multiset.is_empty(the D))) \<in>
  [\<lambda>D. D \<noteq> None]\<^sub>f option_lookup_clause_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
   (auto simp: option_lookup_clause_rel_def lookup_clause_assn_is_empty_def lookup_clause_rel_def
     Multiset.is_empty_def split: option.splits)

lemma lookup_clause_assn_is_empty_lookup_clause_assn_is_empty:
 \<open>(return o lookup_clause_assn_is_empty, RETURN o lookup_clause_assn_is_empty) \<in>
  conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: lookup_clause_assn_is_empty_def uint32_nat_rel_def br_def nat_of_uint32_0_iff)

lemma lookup_clause_assn_is_empty_is_empty_code[sepref_fr_rules]:
  \<open>(return \<circ> lookup_clause_assn_is_empty, RETURN \<circ> the_is_empty) \<in>
      [\<lambda>D. D \<noteq> None]\<^sub>a option_lookup_clause_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using lookup_clause_assn_is_empty_lookup_clause_assn_is_empty[FCOMP
      lookup_clause_assn_is_empty_is_empty,
  unfolded option_lookup_clause_assn_def[symmetric]] unfolding the_is_empty_def
  option_lookup_clause_assn_def[symmetric]
  by simp

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

end


lemma (in -) mset_as_position_length_not_None:
   \<open>mset_as_position x2 C \<Longrightarrow> size C = length (filter (op \<noteq> None) x2)\<close>
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


context isasat_input_bounded
begin

definition (in -) is_in_lookup_conflict where
  \<open>is_in_lookup_conflict = (\<lambda>(n, xs) L. \<not>is_None (xs ! atm_of L))\<close>

sepref_thm is_in_conflict_code
  is \<open>uncurry (RETURN oo is_in_lookup_conflict)\<close>
  :: \<open>[\<lambda>((n, xs), L). atm_of L < length xs]\<^sub>a
       lookup_clause_rel_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> bool_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    uint32_nat_assn_one[sepref_fr_rules] image_image[simp]
  unfolding is_in_lookup_conflict_def
  by sepref

concrete_definition (in -) is_in_conflict_code
   uses isasat_input_bounded.is_in_conflict_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) is_in_conflict_code_def

lemmas is_in_conflict_hnr[sepref_fr_rules] =
   is_in_conflict_code.refine[OF isasat_input_bounded_axioms]

lemma (in -)mset_as_position_remove:
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
  unfolding delete_from_lookup_conflict_def
  by sepref


lemma (in isasat_input_ops) delete_from_lookup_conflict_op_mset_delete:
  \<open>(uncurry delete_from_lookup_conflict, uncurry (RETURN oo op_mset_delete)) \<in>
       [\<lambda>(L, D). -L \<notin># D \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L \<in># D]\<^sub>f Id \<times>\<^sub>f lookup_clause_rel \<rightarrow> \<langle>lookup_clause_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using mset_as_position_remove[of \<open>snd (snd x)\<close> \<open>snd y\<close> \<open>atm_of (fst y)\<close>]
    apply (cases x; cases y; cases \<open>fst y\<close>)
    by (auto simp: delete_from_lookup_conflict_def lookup_clause_rel_def
        dest!: multi_member_split
        intro!: ASSERT_refine_left)
  done

definition (in isasat_input_ops) delete_from_lookup_conflict_pre where
  \<open>delete_from_lookup_conflict_pre \<equiv> \<lambda>(a, b). - a \<notin># b \<and> a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> a \<in># b\<close>

lemma (in isasat_input_ops) op_mset_delete_lookup_conflict_hnr[sepref_fr_rules]:
  \<open>(uncurry delete_from_lookup_conflict_code, uncurry (RETURN \<circ>\<circ> op_mset_delete))
   \<in> [delete_from_lookup_conflict_pre]\<^sub>a
  unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d \<rightarrow> lookup_clause_assn\<close>
  using delete_from_lookup_conflict_code.refine[FCOMP delete_from_lookup_conflict_op_mset_delete]
  unfolding lookup_clause_assn_def[symmetric] delete_from_lookup_conflict_pre_def
  by simp

definition (in isasat_input_ops) set_conflict_m
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> nat clause option \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
   out_learned \<Rightarrow> (nat clause option \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
\<open>set_conflict_m M N i _ _ _ _ =
    SPEC (\<lambda>(C, n, lbd, outl). C = Some (mset (N\<propto>i)) \<and> n = card_max_lvl M (mset (N\<propto>i)) \<and>
     out_learned M C outl)\<close>

definition (in isasat_input_ops) merge_conflict_m
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> nat clause option \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
  out_learned \<Rightarrow> (nat clause option \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
\<open>merge_conflict_m M N i D _ _ _ =
    SPEC (\<lambda>(C, n, lbd, outl). C = Some (mset (tl (N\<propto>i)) \<union># the D) \<and>
       n = card_max_lvl M (mset (tl (N\<propto>i)) \<union># the D) \<and>
       out_learned M C outl)\<close>

definition (in isasat_input_ops) merge_conflict_m_g
  :: \<open>nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> nat clause_l \<Rightarrow> nat clause option \<Rightarrow>
  (nat clause option \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
\<open>merge_conflict_m_g init M Ni D =
    SPEC (\<lambda>(C, n, lbd, outl). C = Some (mset (drop init (Ni)) \<union># the D) \<and>
       n = card_max_lvl M (mset (drop init (Ni))  \<union># the D) \<and>
       out_learned M C outl)\<close>

definition add_to_lookup_conflict :: \<open>nat literal \<Rightarrow> lookup_clause_rel \<Rightarrow> lookup_clause_rel\<close> where
  \<open>add_to_lookup_conflict = (\<lambda>L (n, xs). (if xs ! atm_of L = None then n + 1 else n,
      xs[atm_of L := Some (is_pos L)]))\<close>


definition lookup_conflict_merge'_step
  :: \<open>nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> lookup_clause_rel \<Rightarrow> nat clause_l \<Rightarrow>
      nat clause \<Rightarrow> out_learned \<Rightarrow> bool\<close>
where
  \<open>lookup_conflict_merge'_step init M i clvls zs D C outl = (
      let D' = mset (take (i - init) (drop init D));
          E = remdups_mset (D' + C) in
      ((False, zs), Some E) \<in> option_lookup_clause_rel \<and>
      out_learned M (Some E) outl \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n E \<and> clvls = card_max_lvl M E)\<close>

lemma option_lookup_clause_rel_update_None:
  assumes  \<open>((False, (n, xs)), Some D) \<in> option_lookup_clause_rel\<close> and L_xs : \<open>L < length xs\<close>
  shows \<open>((False, (if xs!L = None then n else n - 1, xs[L := None])),
      Some (D - {# Pos L, Neg L #})) \<in> option_lookup_clause_rel\<close>
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
  assumes confl: \<open>((n, xs), C) \<in> lookup_clause_rel\<close> and uL_C: \<open>-L \<notin># C\<close> and L_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  shows \<open>(add_to_lookup_conflict L (n, xs), {#L#} \<union># C) \<in> lookup_clause_rel\<close>
proof -
  have
    n: \<open>n = size C\<close> and
    mset: \<open>mset_as_position xs C\<close> and
    atm: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close>
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
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat literal \<Rightarrow> nat \<times> bool option list \<Rightarrow> out_learned \<Rightarrow> out_learned\<close> where
  \<open>outlearned_add = (\<lambda>M L zs outl.
    (if get_level M L < count_decided M \<and> \<not>is_in_lookup_conflict zs L then outl @ [L]
           else outl))\<close>

definition clvls_add
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat literal \<Rightarrow> nat \<times> bool option list \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>clvls_add = (\<lambda>M L zs clvls.
    (if get_level M L = count_decided M \<and> \<not>is_in_lookup_conflict zs L then clvls + 1
           else clvls))\<close>

definition lookup_conflict_merge
  :: \<open>nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> nat clause_l \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
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
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
     out_learned \<Rightarrow> (conflict_option_rel \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
  \<open>resolve_lookup_conflict_aa M C i xs clvls lbd outl =
     lookup_conflict_merge one_uint32_nat M (C\<propto>i) xs clvls lbd outl\<close>


definition set_lookup_conflict_aa
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow>
  out_learned \<Rightarrow>(conflict_option_rel \<times> nat \<times> lbd \<times> out_learned) nres\<close>
where
  \<open>set_lookup_conflict_aa M C i xs clvls lbd outl =
     lookup_conflict_merge zero_uint32_nat M (C\<propto>i) xs clvls lbd outl\<close>

(* TODO Move *)
lemma(in isasat_input_ops) in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n:
  \<open>xa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<longleftrightarrow> atm_of xa \<in># \<A>\<^sub>i\<^sub>n\<close>
  by (simp add: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

lemma (in isasat_input_ops) literals_are_in_\<L>\<^sub>i\<^sub>n_trail_atm_of:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<longleftrightarrow> atm_of ` lits_of_l M \<subseteq> set_mset \<A>\<^sub>i\<^sub>n\<close>
  apply (rule iffI)
  subgoal by (auto dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms)
  subgoal by (fastforce simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def lits_of_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
  done

lemma (in isasat_input_bounded) literals_are_in_\<L>\<^sub>i\<^sub>n_trail_count_decided_uint_max:
  assumes
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M\<close> and
    n_d: \<open>no_dup M\<close>
  shows \<open>count_decided M \<le> Suc (uint_max div 2)\<close>
proof -
  have \<open>length M = card (atm_of ` lits_of_l M)\<close>
    using no_dup_length_eq_card_atm_of_lits_of_l[OF n_d] .
  moreover have \<open>atm_of ` lits_of_l M \<subseteq> set_mset \<A>\<^sub>i\<^sub>n\<close>
    using lits unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_trail_atm_of by auto
  ultimately have \<open>length M \<le> card (set_mset \<A>\<^sub>i\<^sub>n)\<close>
    by (simp add: card_mono)
  moreover {
    have \<open>set_mset \<A>\<^sub>i\<^sub>n \<subseteq> {0 ..< (uint_max div 2) + 1}\<close>
      using in_\<A>\<^sub>i\<^sub>n_less_than_uint_max_div_2 by (fastforce simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
          Ball_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n uint_max_def)
    from subset_eq_atLeast0_lessThan_card[OF this] have \<open>card (set_mset \<A>\<^sub>i\<^sub>n) \<le> uint_max div 2 + 1\<close>
      .
  }
  ultimately have \<open>length M \<le> uint_max div 2 + 1\<close>
    by linarith
  moreover have \<open>count_decided M \<le> length M\<close>
    unfolding count_decided_def by auto
  ultimately show ?thesis by simp
qed

lemma (in isasat_input_bounded) literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<Longrightarrow> no_dup M \<Longrightarrow> get_level M L \<le> Suc (uint_max div 2)\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_trail_count_decided_uint_max[of M]
    count_decided_ge_get_level[of M L]
  by simp

lemma (in -) Suc_uint32_nat_assn_hnr:
  \<open>(return o (\<lambda>n. n + 1), RETURN o Suc) \<in> [\<lambda>n. n < uint_max]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: br_def uint32_nat_rel_def nat_of_uint32_add)
(* End Move *)
end


context isasat_input_bounded
begin

sepref_register resolve_lookup_conflict_aa
sepref_thm resolve_lookup_conflict_merge_code
  is \<open>uncurry6 (PR_CONST resolve_lookup_conflict_aa)\<close>
  :: \<open>[\<lambda>((((((M, N), i), (_, xs)), _), _), out). i \<in># dom_m N \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
        (\<forall>j<length (N\<propto>i). atm_of (N\<propto>i!j) < length (snd xs)) \<and> no_dup M \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N\<propto>i)) \<and>
        length (N\<propto>i) \<le> uint_max]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    uint32_nat_assn_one[sepref_fr_rules] image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    Suc_uint32_nat_assn_hnr[sepref_fr_rules] fmap_length_rll_u_def[simp]
  unfolding resolve_lookup_conflict_aa_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric]
    outlearned_add_def clvls_add_def
    isasat_codegen
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
  apply (rewrite at \<open>_ + \<hole>\<close> annotate_assn[where A = \<open>uint32_nat_assn\<close>])
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) resolve_lookup_conflict_merge_code
   uses isasat_input_bounded.resolve_lookup_conflict_merge_code.refine_raw
   is \<open>(uncurry6 ?f, _) \<in> _\<close>

prepare_code_thms (in -) resolve_lookup_conflict_merge_code_def

lemmas resolve_lookup_conflict_aa_hnr[sepref_fr_rules] =
   resolve_lookup_conflict_merge_code.refine[OF isasat_input_bounded_axioms]

sepref_register set_lookup_conflict_aa
sepref_thm set_lookup_conflict_aa_code
  is \<open>uncurry6 (PR_CONST set_lookup_conflict_aa)\<close>
  :: \<open>[\<lambda>((((((M, N), i), (_, xs)), _), _), _). i \<in># dom_m N \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
        (\<forall>j<length (N\<propto>i). atm_of (N\<propto>i!j) < length (snd xs)) \<and> no_dup M \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N\<propto>i)) \<and>
        length (N\<propto>i) \<le> uint_max]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d  *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    uint32_nat_assn_one[sepref_fr_rules] image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    Suc_uint32_nat_assn_hnr[sepref_fr_rules]  fmap_length_rll_u_def[simp]
  unfolding set_lookup_conflict_aa_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric] length_rll_def[symmetric]
    length_aa_u_def[symmetric] outlearned_add_def clvls_add_def
    isasat_codegen
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
  apply (rewrite at \<open>_ + \<hole>\<close> annotate_assn[where A = \<open>uint32_nat_assn\<close>])
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) set_lookup_conflict_aa_code
   uses isasat_input_bounded.set_lookup_conflict_aa_code.refine_raw
   is \<open>(uncurry6 ?f, _) \<in> _\<close>

prepare_code_thms (in -) set_lookup_conflict_aa_code_def

lemmas set_lookup_conflict_aa_code[sepref_fr_rules] =
   set_lookup_conflict_aa_code.refine[OF isasat_input_bounded_axioms]

(* TODO Move *)
lemma (in -)distinct_in_set_take_iff:
  \<open>distinct D \<Longrightarrow>
    b < length D \<Longrightarrow>
    D ! b \<in> set (take a D) \<longleftrightarrow> b < a\<close>
  apply (induction a arbitrary: b)
  subgoal by simp
  subgoal for a
    by (cases \<open>Suc a < length D\<close>)
      (auto simp: take_Suc_conv_app_nth nth_eq_iff_index_eq)
  done

lemma (in -)in_set_conv_iff:
  \<open>x \<in> set (take n xs) \<longleftrightarrow> (\<exists>i < n. i < length xs \<and> xs ! i = x)\<close>
   apply (induction n)
  subgoal by auto
  subgoal for n
    apply (cases \<open>Suc n < length xs\<close>)
    subgoal by (auto simp: take_Suc_conv_app_nth less_Suc_eq dest: in_set_takeD)
    subgoal
    apply (cases \<open>n < length xs\<close>)
      apply (auto simp: take_Suc_conv_app_nth dest: in_set_takeD)
      using less_Suc_eq apply auto[1]
      apply (meson in_set_conv_nth less_trans_Suc not_less_eq)
      by (meson Suc_lessD less_trans_Suc not_less_eq)
    done
  done

lemma (in -) in_set_distinct_take_drop_iff:
  assumes
    \<open>distinct D\<close> and
    \<open>b < length D\<close>
  shows \<open>D ! b \<in> set (take (a - init) (drop init D)) \<longleftrightarrow> (init \<le> b \<and> b < a)\<close>
  using assms apply (auto 5 5 simp: distinct_in_set_take_iff in_set_conv_iff
      in_set_drop_conv_nth  nth_eq_iff_index_eq dest: in_set_takeD)
  by (metis add_diff_cancel_left' diff_less_mono le_iff_add less_imp_le_nat nth_drop)


lemma (in -)is_neg_neg_not_is_neg: "is_neg (- L) \<longleftrightarrow> \<not> is_neg L"
  by (cases L) auto

(* End Move *)

lemma lookup_conflict_merge'_spec:
  assumes
    o: \<open>((b, n, xs), Some C) \<in> option_lookup_clause_rel\<close> and
    dist: \<open>distinct D\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> and
    tauto: \<open>\<not>tautology (mset D)\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C\<close> and
    \<open>clvls = card_max_lvl M C\<close> and
    CD: \<open>\<And>L. L \<in> set (drop init D) \<Longrightarrow> -L \<notin># C\<close> and
    \<open>Suc init \<le> uint_max\<close> and
    \<open>out_learned M (Some C) outl\<close>
  shows \<open>lookup_conflict_merge init M D (b, n, xs) clvls lbd outl \<le> \<Down> (option_lookup_clause_rel \<times>\<^sub>r Id \<times>\<^sub>r Id)
             (merge_conflict_m_g init M D (Some C))\<close>
     (is \<open>_ \<le>  \<Down> ?Ref ?Spec\<close>)
proof -
  define lbd_upd where
     \<open>lbd_upd lbd i \<equiv> lbd_write lbd (get_level M (D!i)) True\<close> for lbd i
  let ?D = \<open>drop init D\<close>
  have le_D_le_upper[simp]: \<open>a < length D \<Longrightarrow> Suc (Suc a) \<le> uint_max\<close> for a
    using simple_clss_size_upper_div2[of \<open>mset D\<close>] assms by (auto simp: uint_max_def)
  have Suc_N_uint_max: \<open>Suc n \<le> uint_max\<close> and
     size_C_uint_max: \<open>size C \<le> 1 + uint_max div 2\<close> and
     clvls: \<open>clvls = card_max_lvl M C\<close> and
     tauto_C: \<open>\<not> tautology C\<close> and
     dist_C: \<open>distinct_mset C\<close> and
     atms_le_xs: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close> and
     map: \<open>mset_as_position xs C\<close>
    using assms simple_clss_size_upper_div2[of C] mset_as_position_distinct_mset[of xs C]
      lookup_clause_rel_not_tautolgy[of n xs C]
    unfolding option_lookup_clause_rel_def lookup_clause_rel_def
    by (auto simp: uint_max_def)
  then have clvls_uint_max: \<open>clvls \<le> 1 + uint_max div 2\<close>
    using size_filter_mset_lesseq[of \<open>\<lambda>L. get_level M L = count_decided M\<close> C]
    unfolding uint_max_def card_max_lvl_def by linarith
  have [intro]: \<open>((b, a, ba), Some C) \<in> option_lookup_clause_rel \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n C \<Longrightarrow>
        Suc (Suc a) \<le> uint_max\<close> for b a ba C
    using lookup_clause_rel_size[of a ba C] by (auto simp: option_lookup_clause_rel_def
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
      lookup_conflict_merge'_step init M i clvls zs D C outl \<and> i \<ge> init)\<close>

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
      ocr: \<open>((False, ab, b), Some (remdups_mset (?C' a))) \<in> option_lookup_clause_rel\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (remdups_mset (?C' a))\<close> and
      outl: \<open>out_learned M (Some (remdups_mset (?C' a))) outl\<close>
      using I'
      unfolding I'_def lookup_conflict_merge'_step_def Let_def
      by auto
    have
      ab: \<open>ab = size (remdups_mset (?C' a))\<close> and
      map: \<open>mset_as_position b (remdups_mset (?C' a))\<close> and
      \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length b\<close> and
      cr: \<open>((ab, b), remdups_mset (?C' a)) \<in> lookup_clause_rel\<close>
      using ocr unfolding option_lookup_clause_rel_def lookup_clause_rel_def
      by auto
    have a_init: \<open>a \<ge> init\<close>
      using I' unfolding I'_def by auto
    have \<open>size (card_max_lvl M (remdups_mset (?C' a))) \<le> size (remdups_mset (?C' a))\<close>
      unfolding card_max_lvl_def
      by auto
    then have [simp]: \<open>Suc (Suc aa) \<le> uint_max\<close> \<open>Suc aa \<le> uint_max\<close>
      using size_C_uint_max lits a_init
      simple_clss_size_upper_div2[of \<open>remdups_mset (?C' a)\<close>]
      unfolding uint_max_def aa[symmetric]
      by (auto simp: tauto_C')
    have [simp]: \<open>length b = length xs\<close>
      using I unfolding I_def by simp_all

    have ab_upper: \<open>Suc (Suc ab) \<le> uint_max\<close>
      using simple_clss_size_upper_div2[of \<open>remdups_mset (?C' a)\<close>]
      lookup_clause_rel_not_tautolgy[OF cr] a_le_D lits mset_as_position_distinct_mset[OF map]
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
        by (auto simp: is_in_lookup_conflict_def  split: option.splits bool.splits
            dest: in_diffD)
      have [simp]: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
        using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> a_le_D] atms_le_xs
        by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

      have ocr: \<open>((False, add_to_lookup_conflict (D ! a) (ab, b)), Some (remdups_mset (?C' (Suc a))))
        \<in> option_lookup_clause_rel\<close>
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
      have atm_D_a_le_xs: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
        using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> a_le_D] atms_le_xs
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
       Some (remdups_mset (?C' (Suc a)))) \<in> option_lookup_clause_rel\<close>
      proof cases
        case [simp]: None
        have [simp]: \<open>D ! a \<notin># C\<close>
          using if_cond mset_as_position_nth[OF map, of \<open>D ! a\<close>]
            if_cond mset_as_position_nth[OF map, of \<open>-D ! a\<close>]
          by (auto simp: is_in_lookup_conflict_def split: option.splits bool.splits
              dest: in_diffD)
        have [simp]: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
          using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> a_le_D] atms_le_xs
          by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

        show ocr: \<open>((False, add_to_lookup_conflict (D ! a) (ab, b)),
          Some (remdups_mset (?C' (Suc a)))) \<in> option_lookup_clause_rel\<close>
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
          using  dist_C  atms_le_xs Some_in(1) map
          unfolding option_lookup_clause_rel_def lookup_clause_rel_def add_to_lookup_conflict_def ab
          by (auto simp: distinct_mset_in_diff minus_notin_trivial
              intro: mset_as_position.intros
              simp del: remdups_mset_singleton_sum)
      qed
      have notin_lo_in_C: \<open>\<not>is_in_lookup_conflict (ab, b) (D ! a) \<Longrightarrow> D ! a \<notin># C\<close>
        using  mset_as_position_in_iff_nth[OF map, of \<open>Pos (atm_of (D!a))\<close>]
          mset_as_position_in_iff_nth[OF map, of \<open>Neg (atm_of (D!a))\<close>] atm_D_a_le_xs(1)
          \<open>- D ! a \<notin> set (take (a - init) (drop init D))\<close>
          \<open>D ! a \<notin> set (take (a - init) (drop init D))\<close>
          \<open>-D ! a \<notin># C\<close> a_init
        by (cases \<open>b ! (atm_of (D ! a))\<close>; cases \<open>D ! a\<close>)
          (auto simp: is_in_lookup_conflict_def dist_C distinct_mset_in_diff
            split: option.splits bool.splits
            dest: in_diffD)
      have in_lo_in_C: \<open>is_in_lookup_conflict (ab, b) (D ! a) \<Longrightarrow> D ! a \<in># C\<close>
        using  mset_as_position_in_iff_nth[OF map, of \<open>Pos (atm_of (D!a))\<close>]
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


lemma resolve_lookup_conflict_aa_set_conflict:
  \<open>(uncurry6 set_lookup_conflict_aa, uncurry6 set_conflict_m) \<in>
    [\<lambda>((((((M, N), i), xs), clvls), lbd), outl). i \<in># dom_m N \<and> xs = None \<and> distinct (N \<propto> i) \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> i)) \<and> \<not>tautology (mset (N \<propto> i)) \<and> clvls = 0 \<and>
       out_learned M None outl]\<^sub>f
    \<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_lookup_clause_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f Id
         \<times>\<^sub>f Id  \<rightarrow>
      \<langle>option_lookup_clause_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<rangle>nres_rel\<close>
proof -
  have H: \<open>set_lookup_conflict_aa M N i (b, n, xs) clvls lbd outl
    \<le> \<Down> (option_lookup_clause_rel \<times>\<^sub>r Id)
       (set_conflict_m M N i None clvls lbd outl)\<close>
    if
      \<open>i \<in># dom_m N\<close> and
      ocr: \<open>((b, n, xs), None) \<in> option_lookup_clause_rel\<close> and
     dist: \<open>distinct (N \<propto> i)\<close> and
     lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> i))\<close> and
     tauto: \<open>\<not>tautology (mset (N \<propto> i))\<close> and
     \<open>clvls = 0\<close> and
     out: \<open>out_learned M None outl\<close>
    for b n xs N i M clvls lbd outl
  proof -
    have lookup_conflict_merge_normalise:
        \<open>lookup_conflict_merge 0 M C (b, zs) = lookup_conflict_merge 0 M C (False, zs)\<close>
      for M C zs
      unfolding lookup_conflict_merge_def by auto
    have [simp]: \<open>out_learned M (Some {#}) outl\<close>
      using out by (cases outl) (auto simp: out_learned_def)
    have T: \<open>((False, n, xs), Some {#}) \<in> option_lookup_clause_rel\<close>
      using ocr unfolding option_lookup_clause_rel_def by auto
    show ?thesis unfolding set_lookup_conflict_aa_def set_conflict_m_def
      using lookup_conflict_merge'_spec[of False n xs \<open>{#}\<close> \<open>N\<propto>i\<close> 0 _ 0 outl lbd] that dist T
      by (auto simp: lookup_conflict_merge_normalise uint_max_def merge_conflict_m_g_def)
  qed
  show ?thesis
    unfolding lookup_conflict_merge_def uncurry_def
    by (intro nres_relI frefI) (auto simp: H)
qed

theorem resolve_lookup_conflict_merge_code_set_conflict[sepref_fr_rules]:
  \<open>(uncurry6 set_lookup_conflict_aa_code, uncurry6 set_conflict_m) \<in>
  [\<lambda>((((((M, N), i), xs), clvls), lbd), outl). clvls = 0 \<and> i \<in># dom_m N \<and> xs = None \<and> distinct (N \<propto> i) \<and>
    literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> i)) \<and> \<not> tautology (mset (N \<propto> i)) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
     no_dup M \<and> out_learned M None outl]\<^sub>a
  trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a
      lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
    option_lookup_clause_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
   (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
   have H: \<open>?c
  \<in> [comp_PRE (\<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_lookup_clause_rel \<times>\<^sub>f
        nat_rel \<times>\<^sub>f Id \<times>\<^sub>f Id)
     (\<lambda>((((((M, N), i), xs), clvls), lbd), outl). i \<in># dom_m N \<and> xs = None \<and>
         distinct (N \<propto> i) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> i)) \<and> \<not> tautology (mset (N \<propto> i)) \<and>
         clvls = 0 \<and> out_learned M None outl)
     (\<lambda>_ ((((((M, N), i), _, xs), _), _), _). i \<in># dom_m N \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
         (\<forall>j<length (N \<propto> i). atm_of (N \<propto> i ! j) < length (snd xs)) \<and> no_dup M \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> i)) \<and> length (N \<propto> i) \<le> uint_max)
     (\<lambda>_. True)]\<^sub>a
   hrp_comp ((hr_comp trail_pol_assn trail_pol)\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
       conflict_option_rel_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d)
     (\<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_lookup_clause_rel \<times>\<^sub>f
         nat_rel \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow>
    hr_comp (conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn)
      (option_lookup_clause_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f (Id \<times>\<^sub>f Id)))\<close> (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
     using hfref_compI_PRE_aux[OF set_lookup_conflict_aa_code.refine[unfolded PR_CONST_def]
        resolve_lookup_conflict_aa_set_conflict[unfolded PR_CONST_def],
        OF isasat_input_bounded_axioms]
     unfolding PR_CONST_def
     .
   have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def in_br_conv list_mset_rel_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff literals_to_update_wl_empty_def option_lookup_clause_rel_def
        lookup_clause_rel_def uint_max_def
        dest: literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l simple_clss_size_upper_div2)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp option_lookup_clause_assn_def
    by (auto simp: prod_hrp_comp hrp_comp_def hr_comp_invalid)

  have f: \<open>?f' = ?f\<close>
    by (auto simp: list_assn_list_mset_rel_eq_list_mset_assn
       option_lookup_clause_assn_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


lemma resolve_lookup_conflict_aa_merge_conflict_m:
  \<open>(uncurry6 resolve_lookup_conflict_aa, uncurry6 merge_conflict_m) \<in>
    [\<lambda>((((((M, N), i), xs), clvls), lbd), out). i \<in># dom_m N \<and> xs \<noteq> None \<and> distinct (N \<propto> i) \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> i)) \<and> \<not>tautology (mset (N \<propto> i)) \<and>
       (\<forall>L \<in> set (tl (N \<propto> i)). - L \<notin># the xs) \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (the xs) \<and> clvls = card_max_lvl M (the xs) \<and>
       out_learned M xs out]\<^sub>f
    \<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_lookup_clause_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f Id
         \<times>\<^sub>f Id \<rightarrow>
    \<langle>option_lookup_clause_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id\<rangle>nres_rel\<close>
proof -
  have H: \<open>resolve_lookup_conflict_aa M N i (b, n, xs) clvls lbd outl
    \<le> \<Down> (option_lookup_clause_rel \<times>\<^sub>r Id)
       (merge_conflict_m M N i (Some D) clvls lbd outl)\<close>
    if
      \<open>i \<in># dom_m N\<close> and
      ocr: \<open>((b, n, xs), Some D) \<in> option_lookup_clause_rel\<close> and
      dist: \<open>distinct (N \<propto> i)\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> i))\<close> and
      tauto: \<open>\<not>tautology (mset (N \<propto> i))\<close> and
      \<open>\<forall>L \<in> set (tl (N \<propto> i)). - L \<notin># D\<close> and
      lits_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D\<close> and
      clvls: \<open>clvls = card_max_lvl M D\<close> and
      out: \<open>out_learned M (Some D) outl\<close>
    for b n xs N i M clvls lbd D outl
    using lookup_conflict_merge'_spec[of b n xs D \<open>N\<propto>i\<close> clvls M 1 outl lbd] that dist lits_D clvls
      out
    unfolding merge_conflict_m_g_def tl_drop_def[symmetric] resolve_lookup_conflict_aa_def
      merge_conflict_m_def
    by (auto simp: uint_max_def)
  show ?thesis
    unfolding lookup_conflict_merge_def uncurry_def
    by (intro nres_relI frefI) (auto simp: H)
qed

theorem resolve_lookup_conflict_merge_code_merge_conflict_m[sepref_fr_rules]:
  \<open>(uncurry6 resolve_lookup_conflict_merge_code, uncurry6 merge_conflict_m) \<in>
  [\<lambda>((((((M, N), i), xs), clvls), lbd), outl). clvls = card_max_lvl M (the xs) \<and> i \<in># dom_m N \<and>
      xs \<noteq> None \<and> distinct (N \<propto> i) \<and> \<not>tautology (the xs) \<and>
     literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> i)) \<and> \<not> tautology (mset (N \<propto> i)) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
     no_dup M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the xs) \<and>
     (\<forall>L \<in> set (tl (N \<propto> i)). - L \<notin># the xs) \<and> out_learned M xs outl]\<^sub>a
  trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a
      lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
    option_lookup_clause_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
   (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
   have H: \<open>?c
  \<in> [comp_PRE (\<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_lookup_clause_rel \<times>\<^sub>f
      nat_rel \<times>\<^sub>f Id \<times>\<^sub>f Id)
     (\<lambda>((((((M, N), i), xs), clvls), lbd), out). i \<in># dom_m N \<and> xs \<noteq> None \<and> distinct (N \<propto> i) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> i)) \<and> \<not> tautology (mset (N \<propto> i)) \<and>
         (\<forall>L\<in>set (tl (N \<propto> i)). - L \<notin># the xs) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the xs) \<and>
         clvls = card_max_lvl M (the xs) \<and> out_learned M xs out)
     (\<lambda>_ ((((((M, N), i), _, xs), _), _), out). i \<in># dom_m N \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
         (\<forall>j<length (N \<propto> i). atm_of (N \<propto> i ! j) < length (snd xs)) \<and> no_dup M \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> i)) \<and> length (N \<propto> i) \<le> uint_max)
     (\<lambda>_. True)]\<^sub>a
   hrp_comp ((hr_comp trail_pol_assn trail_pol)\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
               conflict_option_rel_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d)
      (\<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_lookup_clause_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f
                      Id \<times>\<^sub>f Id) \<rightarrow>
   hr_comp (conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn)
      (option_lookup_clause_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f (Id \<times>\<^sub>f Id)))\<close> (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
     using hfref_compI_PRE_aux[OF resolve_lookup_conflict_merge_code.refine[unfolded PR_CONST_def]
        resolve_lookup_conflict_aa_merge_conflict_m[unfolded PR_CONST_def], OF isasat_input_bounded_axioms]
     unfolding PR_CONST_def
     .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def in_br_conv list_mset_rel_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff literals_to_update_wl_empty_def option_lookup_clause_rel_def
        lookup_clause_rel_def uint_max_def
        dest: literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l simple_clss_size_upper_div2)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp option_lookup_clause_assn_def
    by (auto simp: prod_hrp_comp hrp_comp_def hr_comp_invalid)

  have f: \<open>?f' = ?f\<close>
    by (auto simp: list_assn_list_mset_rel_eq_list_mset_assn
       option_lookup_clause_assn_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


definition (in -) is_in_conflict :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> bool\<close> where
  [simp]: \<open>is_in_conflict L C \<longleftrightarrow> L \<in># the C\<close>

definition (in -) is_in_lookup_option_conflict
  :: \<open>nat literal \<Rightarrow> (bool \<times> nat \<times> bool option list) \<Rightarrow> bool\<close>
where
  \<open>is_in_lookup_option_conflict = (\<lambda>L (_, _, xs). xs ! atm_of L = Some (is_pos L))\<close>

lemma is_in_lookup_option_conflict_is_in_conflict:
  \<open>(uncurry (RETURN oo is_in_lookup_option_conflict), uncurry (RETURN oo is_in_conflict)) \<in>
     [\<lambda>(L, C). C \<noteq> None \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>r option_lookup_clause_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro nres_relI frefI)
  subgoal for Lxs LC
    using lookup_clause_rel_atm_in_iff[of _ \<open>snd (snd (snd Lxs))\<close>]
    apply (cases Lxs)
    by (auto simp: is_in_lookup_option_conflict_def is_in_conflict_def option_lookup_clause_rel_def)
  done

sepref_definition (in -) is_in_lookup_option_conflict_code
  is \<open>uncurry (RETURN oo is_in_lookup_option_conflict)\<close>
  :: \<open>[\<lambda>(L, (b, n, xs)). atm_of L < length xs]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a (bool_assn *a lookup_clause_rel_assn)\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_in_lookup_option_conflict_def
  by sepref


lemma is_in_lookup_option_conflict_code_is_in_conflict[sepref_fr_rules]:
  \<open>(uncurry is_in_lookup_option_conflict_code,
     uncurry (RETURN oo is_in_conflict)) \<in>
    [\<lambda>(L, C). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> C \<noteq> None]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>k  \<rightarrow> bool_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (Id \<times>\<^sub>f option_lookup_clause_rel) (\<lambda>(L, C). C \<noteq> None \<and> L \<in> snd ` D\<^sub>0)
          (\<lambda>_ (L, b, n, xs). atm_of L < length xs)
          (\<lambda>_. True)]\<^sub>a
      hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a (bool_assn *a lookup_clause_rel_assn)\<^sup>k)
           (Id \<times>\<^sub>f option_lookup_clause_rel) \<rightarrow>
      hr_comp bool_assn bool_rel\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF is_in_lookup_option_conflict_code.refine
        is_in_lookup_option_conflict_is_in_conflict] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def option_lookup_clause_rel_def lookup_clause_rel_def
    by (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff lookup_clause_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    lookup_clause_assn_def option_lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

end

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


context isasat_input_ops
begin

lemma id_conflict_from_lookup:
  \<open>(RETURN o id, conflict_from_lookup) \<in> [\<lambda>(n, xs). \<exists>D. ((n, xs), D) \<in> lookup_clause_rel]\<^sub>f Id \<rightarrow>
    \<langle>lookup_clause_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: lookup_clause_rel_def conflict_from_lookup_def RETURN_RES_refine_iff)

end

definition confl_find_next_index_spec where
 \<open>confl_find_next_index_spec = (\<lambda>(n, xs) i.
     SPEC(\<lambda>j. (j \<ge> i \<and> j < length xs \<and> xs ! j \<noteq> None \<and>
        (\<forall>k. k \<ge> i \<longrightarrow> k < j \<longrightarrow> xs ! k = None))))\<close>

definition confl_find_next_index :: \<open>lookup_clause_rel \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
   \<open>confl_find_next_index = (\<lambda>(n, xs) i.
      WHILE\<^sub>T\<^bsup>\<lambda>j. j < length xs \<and> (\<forall>k. k \<ge> i \<longrightarrow> k < j \<longrightarrow> xs ! k = None) \<and> j \<ge> i\<^esup>
           (\<lambda>j. xs ! j = None)
           (\<lambda>j. do{ASSERT(j + 1 \<le> uint_max); RETURN (j + 1)})
           i
    )
\<close>


context isasat_input_ops
begin

fun confl_find_next_index_pre where
  confl_find_next_index_pre_def:
  \<open>confl_find_next_index_pre (n, xs) i \<longleftrightarrow>  i < length xs \<and>
     (\<exists>j. j \<ge> i \<and> j < length xs \<and> j < uint_max \<and> xs ! j \<noteq> None)\<close>

declare confl_find_next_index_pre.simps[simp del]

lemma confl_find_next_index_confl_find_next_index_spec:
  assumes
    ocr: \<open>confl_find_next_index_pre (n, xs) i\<close>
  shows
    \<open>confl_find_next_index (n, xs) i \<le> confl_find_next_index_spec (n,xs) i\<close>
proof -
  have i_xs: \<open>i < length xs\<close>
    using ocr unfolding confl_find_next_index_pre_def by blast
  have H: False if \<open>\<forall>k\<ge>i. k < l \<longrightarrow> xs ! k = None\<close> and \<open>l \<ge> uint_max\<close> for l
    using ocr that unfolding confl_find_next_index_pre_def
    by (auto simp: uint_max_def)

  have Sucj_le_xs: \<open>j + 1 < length xs\<close>
    if
      j_xs: \<open>j < length xs \<and> (\<forall>k\<ge>i. k < j \<longrightarrow> xs ! k = None) \<and> i \<le> j\<close> and
      xs_j: \<open>xs ! j = None\<close>
    for j
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have \<open>\<forall>k\<ge>i. k \<le> length xs - 1 \<longrightarrow> xs ! k = None\<close>
      using j_xs xs_j by (auto simp: linorder_not_less le_Suc_eq)
    then show False
      using ocr unfolding confl_find_next_index_pre_def by fastforce
  qed

  show ?thesis
    unfolding confl_find_next_index_def confl_find_next_index_spec_def prod.case
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>i. length xs - i)\<close>])
    subgoal by auto
    subgoal by (rule i_xs)
    subgoal by auto
    subgoal by auto
    subgoal for k using H[of k] by  (cases \<open>k \<ge> uint_max\<close>)(auto simp: uint_max_def)
    subgoal for k using Sucj_le_xs by blast
    subgoal for j j' using nat_less_le by fastforce
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


lemma confl_find_next_index_confl_find_next_index_spec_fref:
  \<open>(uncurry confl_find_next_index, uncurry confl_find_next_index_spec) \<in>
      [uncurry confl_find_next_index_pre]\<^sub>f
      Id \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto intro!: confl_find_next_index_confl_find_next_index_spec)
end


context isasat_input_bounded
begin

lemma lookup_clause_rel_exists_le_uint_max:
  assumes ocr: \<open>((n, xs), D) \<in> lookup_clause_rel\<close> and \<open>n > 0\<close> and
    le_i: \<open>\<forall>k<i. xs ! k = None\<close> and lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D\<close>
  shows
    \<open>\<exists>j. j \<ge> i \<and> j < length xs \<and> j < uint_max \<and> xs ! j \<noteq> None\<close>
proof -
  have
    n_D: \<open>n = size D\<close> and
    map: \<open>mset_as_position xs D\<close> and
    le_xs: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close>
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
    using lits in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max
    by (auto 5 5 dest!: multi_member_split[of _ D]
        simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset split: if_splits)
  then have \<open>j < uint_max\<close>
    by (auto simp: uint_max_def split: if_splits)
  then show ?thesis
    using j by blast
qed


end

definition highest_lit where
  \<open>highest_lit M C L \<longleftrightarrow>
     (L = None \<longrightarrow> C = {#}) \<and>
     (L \<noteq> None \<longrightarrow> get_level M (fst (the L)) = snd (the L) \<and>
        snd (the L) = get_maximum_level M C \<and>
        fst (the L) \<in># C
        )\<close>

definition iterate_over_conflict_inv where
  \<open>iterate_over_conflict_inv M D\<^sub>0 = (\<lambda>(D, D'). D \<subseteq># D\<^sub>0 \<and> D' \<subseteq># D)\<close>

definition is_literal_redundant_spec where
   \<open>is_literal_redundant_spec K NU UNE D L = SPEC(\<lambda>b. b \<longrightarrow>
      NU + UNE \<Turnstile>pm remove1_mset L (add_mset K D))\<close>

definition iterate_over_conflict
  :: \<open>'v literal \<Rightarrow> ('v, 'mark) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow>  'v clause \<Rightarrow>
       'v clause nres\<close>
where
  \<open>iterate_over_conflict K M NU UNE D\<^sub>0 = do {
    (D, _) \<leftarrow>
       WHILE\<^sub>T\<^bsup>iterate_over_conflict_inv M D\<^sub>0\<^esup>
       (\<lambda>(D, D'). D' \<noteq> {#})
       (\<lambda>(D, D'). do{
          x \<leftarrow> SPEC (\<lambda>x. x \<in># D');
          red \<leftarrow> is_literal_redundant_spec K NU UNE D x;
          if \<not>red
          then RETURN (D, remove1_mset x D')
          else RETURN (remove1_mset x D, remove1_mset x D')
        })
       (D\<^sub>0, D\<^sub>0);
     RETURN D
}\<close>


definition minimize_and_extract_highest_lookup_conflict_inv where
  \<open>minimize_and_extract_highest_lookup_conflict_inv = (\<lambda>(D, i, s, outl).
    length outl \<le> uint_max)\<close>

type_synonym 'v conflict_highest_conflict = \<open>('v literal \<times> nat) option\<close>

definition (in -) atm_in_conflict where
  \<open>atm_in_conflict L D \<longleftrightarrow> L \<in> atms_of D\<close>

definition atm_in_conflict_lookup :: \<open>nat \<Rightarrow> lookup_clause_rel \<Rightarrow> bool\<close> where
  \<open>atm_in_conflict_lookup = (\<lambda>L (_, xs). xs ! L \<noteq> None)\<close>

sepref_definition (in -) atm_in_conflict_code
  is \<open>uncurry (RETURN oo atm_in_conflict_lookup)\<close>
  :: \<open>[\<lambda>(L, xs). L < length (snd xs)]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding atm_in_conflict_lookup_def
  by sepref

declare atm_in_conflict_code.refine[sepref_fr_rules]

context isasat_input_ops
begin


lemma atm_in_conflict_lookup_atm_in_conflict:
  \<open>(uncurry (RETURN oo atm_in_conflict_lookup), uncurry (RETURN oo atm_in_conflict)) \<in>
     [\<lambda>(L, xs). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>f Id \<times>\<^sub>f lookup_clause_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using mset_as_position_in_iff_nth[of \<open>snd (snd x)\<close> \<open>snd y\<close> \<open>Pos (fst x)\<close>]
      mset_as_position_in_iff_nth[of \<open>snd (snd x)\<close> \<open>snd y\<close> \<open>Neg (fst x)\<close>]
    apply (cases x; cases y) (* TODO Proof *)
    apply (auto simp: atm_in_conflict_lookup_def atm_in_conflict_def
        lookup_clause_rel_def atms_of_def)
      apply (smt atm_of_uminus atms_of_def imageE image_eqI is_pos_neg_not_is_pos
        mset_as_position_in_iff_nth)+
    done
  done


theorem atm_in_conflict_hnr[sepref_fr_rules]:
  \<open>(uncurry atm_in_conflict_code, uncurry (RETURN oo atm_in_conflict)) \<in>
   [\<lambda>(L, xs). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>k \<rightarrow> bool_assn\<close>
   (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
   have H: \<open>?c
  \<in> [comp_PRE (nat_rel \<times>\<^sub>f lookup_clause_rel)
     (\<lambda>(L, xs). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l)
     (\<lambda>_ (L, xs). L < length (snd xs))
     (\<lambda>_. True)]\<^sub>a
   hrp_comp (uint32_nat_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>k) (nat_rel \<times>\<^sub>f lookup_clause_rel) \<rightarrow>
   hr_comp bool_assn bool_rel\<close> (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
     using hfref_compI_PRE_aux[OF atm_in_conflict_code.refine atm_in_conflict_lookup_atm_in_conflict]
     .
   have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def lookup_clause_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp option_lookup_clause_assn_def lookup_clause_assn_def
    by (auto simp: prod_hrp_comp hrp_comp_def hr_comp_invalid)

  have f: \<open>?f' = ?f\<close>
    by (auto simp: list_assn_list_mset_rel_eq_list_mset_assn
       option_lookup_clause_assn_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition is_literal_redundant_lookup_spec where
   \<open>is_literal_redundant_lookup_spec M NU NUE D' L s =
    SPEC(\<lambda>(s', b). b \<longrightarrow> (\<forall>D. (D', D) \<in> lookup_clause_rel \<longrightarrow>
       (mset `# mset (tl NU)) + NUE \<Turnstile>pm remove1_mset L D))\<close>


definition lit_redundant_rec_wl_lookup
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat clause \<Rightarrow>
     _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (_ \<times> _ \<times> bool) nres\<close>
where
  \<open>lit_redundant_rec_wl_lookup M NU D cach analysis lbd =
      WHILE\<^sub>T\<^bsup>lit_redundant_rec_wl_inv M NU D\<^esup>
        (\<lambda>(cach, analyse, b). analyse \<noteq> [])
        (\<lambda>(cach, analyse, b). do {
            ASSERT(analyse \<noteq> []);
            ASSERT(fst (last analyse) \<in># dom_m NU);
            let C = NU \<propto> fst (last analyse);
            ASSERT(length C > 0); (* \<ge> 2 ? *)
            let i = snd (last analyse);
            ASSERT(C!0 \<in> lits_of_l M);
            if i \<ge> length C
            then
               RETURN(cach (atm_of (C ! 0) := SEEN_REMOVABLE), butlast analyse, True)
            else do {
               let (L, analyse) = get_literal_and_remove_of_analyse_wl C analyse;
               ASSERT(-L \<in> lits_of_l M \<and> atm_of L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l);
               let b = \<not>level_in_lbd (get_level M L) lbd;
               if (get_level M L = zero_uint32_nat \<or>
                   conflict_min_cach cach (atm_of L) = SEEN_REMOVABLE \<or>
                   atm_in_conflict (atm_of L) D)
               then RETURN (cach, analyse, False)
               else if b \<or> conflict_min_cach cach (atm_of L) = SEEN_FAILED
               then do {
                  ASSERT(mark_failed_lits_stack_inv NU analyse cach);
                  cach \<leftarrow> mark_failed_lits_wl NU analyse cach;
                  RETURN (cach, [], False)
               }
               else do {
                  C \<leftarrow> get_propagation_reason M (-L);
                  case C of
                    Some C \<Rightarrow> RETURN (cach, analyse @ [(C, 1)], False)
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
    \<open>lit_redundant_rec_wl_inv M NU D x\<close> and
    \<open>x2 = (x1a, x2a)\<close> and
    \<open>x' = (x1, x2)\<close> and
    \<open>x2b = (x1c, x2c)\<close> and
    \<open>x = (x1b, x2b)\<close> and
    \<open>NU \<propto> fst (last x1a) ! 0 \<in> lits_of_l M\<close> and
    \<open>\<not> length (NU \<propto> fst (last x1a)) \<le> snd (last x1a)\<close> and
    \<open>get_literal_and_remove_of_analyse_wl (NU \<propto> fst (last x1c)) x1c = (x1e, x2e)\<close>
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
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M\<close>
  shows
   \<open>lit_redundant_rec_wl_lookup M NU D cach analysis lbd \<le>
      \<Down> Id (lit_redundant_rec_wl M NU D cach analysis lbd)\<close>
proof -
  have M: \<open>\<forall>a \<in> lits_of_l M. a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using isasat_input_ops.literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l lits by blast
  have [simp]: \<open>- x1e \<in> lits_of_l M \<Longrightarrow> atm_in_conflict (atm_of x1e) D \<longleftrightarrow> x1e \<in># D\<close> for x1e
    using M_D n_d
    by (auto simp: atm_in_conflict_def true_annots_true_cls_def_iff_negation_in_model
        atms_of_def atm_of_eq_atm_of dest!: multi_member_split no_dup_consistentD)
  have [simp]: \<open>- x1e \<in> lits_of_l M \<Longrightarrow> atm_of x1e \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close> for x1e
    using lits atm_of_notin_atms_of_iff literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l by blast
  have [refine_vcg]: \<open>(a, b) \<in> Id \<Longrightarrow> (a, b) \<in> \<langle>Id\<rangle>option_rel\<close> for a b by auto
  have [refine_vcg]: \<open>get_propagation_reason M x
    \<le> \<Down> Id (get_propagation_reason M y)\<close> if \<open>x = y\<close> for x y
    unfolding that by auto
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
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule lit_redundant_rec_wl_lookup_mark_failed_lits_stack_inv)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule lit_redundant_rec_wl_lookup_mark_failed_lits_stack_inv)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition (in isasat_input_ops) literal_redundant_wl_lookup where
  \<open>literal_redundant_wl_lookup M NU D cach L lbd = do {
     ASSERT(-L \<in> lits_of_l M);
     if get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE
     then RETURN (cach, [], True)
     else if cach (atm_of L) = SEEN_FAILED
     then RETURN (cach, [], False)
     else do {
       C \<leftarrow> get_propagation_reason M (-L);
       case C of
         Some C \<Rightarrow> lit_redundant_rec_wl_lookup M NU D cach [(C, 1)] lbd
       | None \<Rightarrow> do {
           RETURN (cach, [], False)
       }
     }
  }\<close>

lemma literal_redundant_wl_lookup_literal_redundant_wl:
  assumes \<open>M \<Turnstile>as CNot D\<close> \<open>no_dup M\<close> \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M\<close>
  shows
    \<open>literal_redundant_wl_lookup M NU D cach L lbd \<le> \<Down> Id (literal_redundant_wl M NU D cach L lbd)\<close>
proof -
  have [refine]: \<open>(x, x') \<in> Id \<Longrightarrow> (x, x') \<in> \<langle>Id\<rangle>option_rel\<close> for x x'
    by auto
  show ?thesis
    unfolding literal_redundant_wl_lookup_def literal_redundant_wl_def
    apply (refine_vcg lit_redundant_rec_wl_lookup_lit_redundant_rec_wl)
    subgoal by auto
    subgoal by auto
    subgoal for x x' xa x'a
      apply (subgoal_tac \<open>lit_redundant_rec_wl_lookup M NU D cach [(xa, 1)] lbd
    \<le> \<Down> Id (lit_redundant_rec_wl M NU D cach [(xa, 1)] lbd)\<close>)
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

term minimize_and_extract_highest_lookup_conflict_inv
definition minimize_and_extract_highest_lookup_conflict
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat clause \<Rightarrow> (nat \<Rightarrow> minimize_status) \<Rightarrow> lbd \<Rightarrow>
     out_learned \<Rightarrow> (nat clause \<times> (nat \<Rightarrow> minimize_status) \<times> out_learned) nres\<close>
where
  \<open>minimize_and_extract_highest_lookup_conflict  = (\<lambda>M NU nxs s lbd outl. do {
    (D, _, s, outl) \<leftarrow>
       WHILE\<^sub>T\<^bsup>minimize_and_extract_highest_lookup_conflict_inv\<^esup>
         (\<lambda>(nxs, i, s, outl). i < length outl)
         (\<lambda>(nxs, x, s, outl). do {
            ASSERT(x < length outl);
            let L = outl ! x;
            ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
            (s', _, red) \<leftarrow> literal_redundant_wl_lookup M NU nxs s L lbd;
            if \<not>red
            then RETURN (nxs, x+1, s', outl)
            else do {
               ASSERT (delete_from_lookup_conflict_pre (L, nxs));
               RETURN (remove1_mset L nxs, x, s',  delete_index_and_swap outl x)
            }
         })
         (nxs, one_uint32_nat, s, outl);
     RETURN (D, s, outl)
  })\<close>

lemma conc_fun_mono: \<open>A \<le> B \<Longrightarrow> \<Down> R A \<le> \<Down> R B\<close>
  using ref_two_step by auto

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

end
(* TODO Move *)

lemma swap_nth_irrelevant:
  \<open>k \<noteq> i \<Longrightarrow> k \<noteq> j \<Longrightarrow> swap xs i  j ! k = xs ! k\<close>
  by (auto simp: swap_def)

lemma swap_nth_relevant:
  \<open>i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> swap xs i  j ! i = xs ! j\<close>
  by (auto simp: swap_def)

lemma swap_nth_relevant2:
  \<open>i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> swap xs j i ! i = xs ! j\<close>
  by (auto simp: swap_def)

lemma swap_nth_if:
  \<open>i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> swap xs i  j ! k =
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

lemma hd_take:
  \<open>0 < length outl' \<Longrightarrow> i > 0 \<Longrightarrow> hd (take i outl') = hd outl'\<close>
  by (cases outl'; cases i) auto

lemma hd_list_update_If:
  \<open>i < length outl' \<Longrightarrow> hd (outl'[i := w]) = (if i = 0 then w else hd outl')\<close>
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

(* End Move *)

context isasat_input_bounded
begin

lemma minimize_and_extract_highest_lookup_conflict_iterate_over_conflict:
  fixes D :: \<open>nat clause\<close> and S' :: \<open>nat twl_st_l\<close> and NU :: \<open>nat clauses_l\<close> and S :: \<open>nat twl_st_wl\<close>
     and S'' :: \<open>nat twl_st\<close>
   defines
 (*   \<open>S' \<equiv> st_l_of_wl None S\<close> and
    \<open>S'' \<equiv> twl_st_of_wl None S\<close> and *)
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
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M\<close> and
    struct_invs: \<open>twl_struct_invs S''\<close> and
    add_inv: \<open>twl_list_invs S'\<close> and
    cach_init: \<open>conflict_min_analysis_inv M' s' (NU' + NUE) D\<close> and
    NU_P_D: \<open>NU' + NUE \<Turnstile>pm add_mset K D\<close> and
    lits_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D\<close> and
    K: \<open>K = outl ! 0\<close> and
    outl_nempty: \<open>outl \<noteq> []\<close>
  shows
    \<open>minimize_and_extract_highest_lookup_conflict M NU D s' lbd outl \<le>
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
      using that simple_clss_size_upper_div2[OF lits_D dist_D tauto]
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

  have redundant: \<open>literal_redundant_wl_lookup M NU nxs cach
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
      using S_S' S'_S'' unfolding M' M_def S'''_def by (auto simp: twl_st)
    have \<open>outl' ! x1d \<in># E\<close>
      using \<open>E = mset (tl outl')\<close> \<open>x1d < length outl'\<close> \<open>0 < x1d\<close>
      by (auto simp: nth_in_set_tl)

    have 1:
    \<open>literal_redundant_wl_lookup M NU nxs cach ?L lbd \<le> \<Down> Id (literal_redundant_wl M NU nxs cach ?L lbd)\<close>
      by (rule literal_redundant_wl_lookup_literal_redundant_wl)
        (use n_d lits M_x1 struct_invs add_inv \<open>outl' ! x1d \<in># E\<close> \<open>E = nxs\<close> in auto)
    then have 1:
    \<open>literal_redundant_wl_lookup M NU nxs cach ?L lbd \<le> (literal_redundant_wl M NU nxs cach ?L lbd)\<close>
      by simp

    have 2:
    \<open>literal_redundant_wl M NU nxs cach ?L lbd \<le> \<Down>
       (Id \<times>\<^sub>r {(analyse, analyse'). analyse' = convert_analysis_list NU analyse \<and>
          (\<forall>(i, j)\<in> set analyse. j \<le> length (NU\<propto>i) \<and> i \<in># dom_m NU \<and> j \<ge> 1 \<and> i > 0)} \<times>\<^sub>r bool_rel)
       (literal_redundant M' NU' nxs cach ?L)\<close>
      by (rule literal_redundant_wl_literal_redundant[of S S' S'',
            unfolded M_def[symmetric] NU[symmetric] M'[symmetric] S'''_def[symmetric]
            NU'_def[symmetric]])
         (use S_S' S'_S'' M_x1 struct_invs add_inv \<open>outl' ! x1d \<in># E\<close> \<open>E = nxs\<close> in auto)

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
       apply (rule conc_fun_mono[OF 3])
      unfolding  literal_redundant_spec_def is_literal_redundant_spec_def
          conc_fun_SPEC NU'_NUE[symmetric]
      apply (rule SPEC_rule)
      apply clarify
      using NU_P_E ent \<open>E = nxs\<close> \<open>E = mset (tl outl')\<close>[symmetric] \<open>outl' ! x1d \<in># E\<close>
      by (auto simp: intro!: entails_uminus_filter_to_poslev_can_remove[of _ _ M']
          filter_to_poslev_conflict_min_analysis_inv simp del: diff_union_swap2)
  qed

  have
    outl'_F: \<open>outl' ! i \<in># F\<close> (is ?out) and
    outl'_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>outl' ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> (is ?out_L)
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
     del: \<open>delete_from_lookup_conflict_pre (outl' ! i, D')\<close> (is ?del)
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
      \<open>outl' ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
      cach: \<open>(cachred, red') \<in> (?red F' L)\<close>
    for S T F' T1 F D' S1 i S2 cach S3 highest outl' L  cachred red' cachr
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
        (auto simp: butlast_list_update mset_butlast_remove1_mset single_remove1_mset_eq)
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

    have \<open>outl' ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> \<open>outl' ! i \<in># D\<close>
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
    apply (refine_vcg  WHILEIT_refine[where R = R])
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

end


context isasat_input_ops
begin

abbreviation (in -)analyse_refinement_assn where
  \<open>analyse_refinement_assn \<equiv> arl_assn (nat_assn *a nat_assn)\<close>

end


lemma minimize_status_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (op =)), uncurry (RETURN oo (op =))) \<in>
    minimize_status_assn\<^sup>k *\<^sub>a minimize_status_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by (sepref_to_hoare) (sep_auto)

context isasat_input_ops
begin

context
begin
private lemma mark_failed_lits_stack_inv_helper1: \<open>mark_failed_lits_stack_inv a ba a2' \<Longrightarrow>
       a1' < length ba \<Longrightarrow>
       (a1'a, a2'a) = ba ! a1' \<Longrightarrow>
       a1'a \<in># dom_m a\<close>
  using nth_mem[of a1' ba] unfolding  mark_failed_lits_stack_inv_def
  by (auto simp del: nth_mem)

private lemma mark_failed_lits_stack_inv_helper2: \<open>mark_failed_lits_stack_inv a ba a2' \<Longrightarrow>
       a1' < length ba \<Longrightarrow>
       (a1'a, a2'a) = ba ! a1' \<Longrightarrow>
       a2'a - Suc 0 < length (a \<propto> a1'a)\<close>
  using nth_mem[of a1' ba] unfolding  mark_failed_lits_stack_inv_def
  by (auto simp del: nth_mem)

sepref_thm mark_failed_lits_stack_code
  is \<open>uncurry2 mark_failed_lits_stack\<close>
  :: \<open>clauses_ll_assn\<^sup>k *\<^sub>a analyse_refinement_assn\<^sup>d *\<^sub>a cach_refinement_assn\<^sup>d \<rightarrow>\<^sub>a
      cach_refinement_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim!] image_image[simp] length_rll_def[simp]
    mark_failed_lits_stack_inv_helper1[dest] mark_failed_lits_stack_inv_helper2[dest]
    fmap_length_rll_u_def[simp]
  unfolding mark_failed_lits_stack_def
    conflict_min_cach_set_failed_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric]
    fmap_rll_def[symmetric]
  by sepref

end

sepref_register mark_failed_lits_stack
concrete_definition (in -) mark_failed_lits_stack_code
   uses isasat_input_ops.mark_failed_lits_stack_code.refine_raw
   is \<open>(uncurry2 ?f, _)\<in>_\<close>

prepare_code_thms (in -) mark_failed_lits_stack_code_def

lemmas mark_failed_lits_stack_code_hnr =
   mark_failed_lits_stack_code.refine[of \<A>\<^sub>i\<^sub>n]

lemma mark_failed_lits_wl_hnr[sepref_fr_rules]:
  \<open>(uncurry2 mark_failed_lits_stack_code, uncurry2 mark_failed_lits_wl)
     \<in> [\<lambda>((a, b), ba). literals_are_in_\<L>\<^sub>i\<^sub>n_mm ((mset \<circ> fst) `# ran_m a) \<and>
         mark_failed_lits_stack_inv a b ba]\<^sub>a
        clauses_ll_assn\<^sup>k *\<^sub>a analyse_refinement_assn\<^sup>d *\<^sub>a cach_refinement_assn\<^sup>d \<rightarrow>
        cach_refinement_assn\<close>
  using mark_failed_lits_stack_code_hnr[FCOMP mark_failed_lits_stack_mark_failed_lits_wl]
  .
end

context isasat_input_bounded
begin


lemma literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<Longrightarrow> -a \<in> lits_of_l M \<Longrightarrow> a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def lits_of_def uminus_lit_swap uminus_\<A>\<^sub>i\<^sub>n_iff)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<Longrightarrow> -a \<in> lits_of_l M \<Longrightarrow> atm_of a \<in># \<A>\<^sub>i\<^sub>n\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[of M a]
  unfolding in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[symmetric] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n[symmetric]
  .
(* TODO fst (lst last) \<le> uint_max? *)
sepref_register lit_redundant_rec_wl_lookup
sepref_thm lit_redundant_rec_wl_lookup_code
  is \<open>uncurry5 (PR_CONST lit_redundant_rec_wl_lookup)\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), analysis), lbd).
         literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf NU) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n_trail M]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>k *\<^sub>a
        cach_refinement_assn\<^sup>d *\<^sub>a analyse_refinement_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_assn *a analyse_refinement_assn *a bool_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim] image_image[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms[intro] length_rll_def[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro] nth_rll_def[simp]
    fmap_length_rll_u_def[simp]
    fmap_length_rll_def[simp]
  unfolding lit_redundant_rec_wl_lookup_def
    conflict_min_cach_set_removable_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric] PR_CONST_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl.fold_custom_empty)+
  apply (rewrite at \<open>op_arl_empty\<close> annotate_assn[where A=analyse_refinement_assn])
  apply (rewrite at \<open>let _ = _ \<propto> _ in _\<close> Let_def)
  unfolding nth_rll_def[symmetric] length_rll_def[symmetric]
    fmap_rll_def[symmetric]
    fmap_length_rll_def[symmetric]
  by sepref (* slow *)

concrete_definition (in -) lit_redundant_rec_wl_lookup_code
   uses isasat_input_bounded.lit_redundant_rec_wl_lookup_code.refine_raw
   is \<open>(uncurry5 ?f, _)\<in>_\<close>

prepare_code_thms (in -) lit_redundant_rec_wl_lookup_code_def

lemmas lit_redundant_rec_wl_lookup_hnr[sepref_fr_rules] =
   lit_redundant_rec_wl_lookup_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

end

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

context isasat_input_bounded
begin

lemma
  fixes D :: \<open>nat clause\<close> and s and s' and NU :: \<open>nat clauses_l\<close> and
    S :: \<open>nat twl_st_wl\<close> and S' :: \<open>nat twl_st_l\<close> and S'' :: \<open>nat twl_st\<close>
  defines
(*     \<open>S' \<equiv> st_l_of_wl None S\<close> and
    \<open>S'' \<equiv> twl_st_of_wl None S\<close> and *)
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
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M\<close> and
    struct_invs: \<open>twl_struct_invs S''\<close> and
    add_inv: \<open>twl_list_invs S'\<close> and
    cach_init: \<open>conflict_min_analysis_inv M' s' (NU' + NUE) D\<close> and
    NU_P_D: \<open>NU' + NUE \<Turnstile>pm add_mset K D\<close> and
    lits_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D\<close> and
    K: \<open>K = outl ! 0\<close> and
    outl_nempty: \<open>outl \<noteq> []\<close>
  shows
    \<open>minimize_and_extract_highest_lookup_conflict M NU D s' lbd outl \<le>
       \<Down> ({((E, s, outl), E'). E = E' \<and> mset (tl outl) = E \<and> outl!0 = K \<and>
               E' \<subseteq># D})
         (SPEC (\<lambda>D'. D' \<subseteq># D \<and> NU' + NUE \<Turnstile>pm add_mset K D'))\<close>
proof -
  show ?thesis
    apply (rule order.trans)
     apply (rule minimize_and_extract_highest_lookup_conflict_iterate_over_conflict[OF
          assms(7-20)[unfolded assms(1-8)],
          unfolded assms(1-8)[symmetric]])
    apply (rule order.trans)
     apply (rule conc_fun_mono[OF iterate_over_conflict_spec[OF NU_P_D dist_D]])
    by (auto simp: conc_fun_RES)
qed
end

(* TODO Kill *)
sepref_definition (in -) confl_find_next_index_code
  is \<open>uncurry confl_find_next_index\<close>
  :: \<open>lookup_clause_rel_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding confl_find_next_index_def one_uint32_nat_def[symmetric]
  by sepref

declare (in -) confl_find_next_index_code.refine[sepref_fr_rules]


sepref_definition delete_index_and_swap_code
  is \<open>uncurry (RETURN oo delete_index_and_swap)\<close>
  :: \<open>[\<lambda>(xs, i). i < length xs]\<^sub>a
      (arl_assn unat_lit_assn)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> arl_assn unat_lit_assn\<close>
  unfolding delete_index_and_swap.simps
  by sepref

declare delete_index_and_swap_code.refine[sepref_fr_rules]


context isasat_input_bounded
begin

lemma Pos_unat_lit_assn:
  \<open>(return o (\<lambda>n. two_uint32 * n), RETURN o Pos) \<in> [\<lambda>L. Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     unat_lit_assn\<close>
  apply sepref_to_hoare
  using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max
  by (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      lit_of_natP_def nat_of_uint32_distrib_mult2)

lemma Neg_unat_lit_assn:
  \<open>(return o (\<lambda>n. two_uint32 * n +1), RETURN o Neg) \<in> [\<lambda>L. Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
      unat_lit_assn\<close>
  apply sepref_to_hoare
  using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max
  by (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      lit_of_natP_def nat_of_uint32_distrib_mult2_plus1 uint_max_def)


lemma confl_find_next_index_spec_hnr[sepref_fr_rules]:
  \<open>(uncurry confl_find_next_index_code, uncurry confl_find_next_index_spec)
    \<in> [uncurry confl_find_next_index_pre]\<^sub>a
      lookup_clause_rel_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using confl_find_next_index_code.refine[FCOMP
      confl_find_next_index_confl_find_next_index_spec_fref]
  unfolding uncurry_def by simp

lemma lookup_conflict_size_hnr[sepref_fr_rules]:
  \<open>(return o fst, RETURN o lookup_conflict_size) \<in> lookup_clause_rel_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare sep_auto

sepref_definition (in -)lookup_conflict_nth_code
  is \<open>uncurry (RETURN oo lookup_conflict_nth)\<close>
  :: \<open>[\<lambda>((n, xs), i). i < length xs]\<^sub>a
      lookup_clause_rel_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> option_assn bool_assn\<close>
  unfolding lookup_conflict_nth_def
  by sepref

declare lookup_conflict_nth_code.refine[sepref_fr_rules]

lemma single_replicate: \<open>[C] = op_list_append [] C\<close>
  by auto

lemma (in -) lookup_conflict_upd_None_RETURN_def:
  \<open>RETURN oo lookup_conflict_upd_None = (\<lambda>(n, xs) i. RETURN (n- one_uint32_nat, xs [i :=None]))\<close>
  by (auto intro!: ext)

sepref_definition (in -)lookup_conflict_upd_None_code
  is \<open>uncurry (RETURN oo lookup_conflict_upd_None)\<close>
  :: \<open>[\<lambda>((n, xs), i). i < length xs \<and> n > 0]\<^sub>a
     lookup_clause_rel_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> lookup_clause_rel_assn\<close>
  unfolding lookup_conflict_upd_None_RETURN_def fast_minus_def[symmetric]
  by sepref

declare lookup_conflict_upd_None_code.refine[sepref_fr_rules]

declare lit_redundant_rec_wl_lookup_hnr[sepref_fr_rules]


sepref_register literal_redundant_wl_lookup
sepref_thm literal_redundant_wl_lookup_code
  is \<open>uncurry5 (PR_CONST literal_redundant_wl_lookup)\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), L), lbd). literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf NU)]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>k *\<^sub>a
      cach_refinement_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_assn *a analyse_refinement_assn *a bool_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro]
  unfolding literal_redundant_wl_lookup_def zero_uint32_nat_def[symmetric] PR_CONST_def
  apply (subst conflict_min_cach_def[symmetric])
  apply (subst (3) conflict_min_cach_def[symmetric])
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl.fold_custom_empty)+
  unfolding single_replicate
  unfolding arl.fold_custom_empty
  by sepref

concrete_definition (in -) literal_redundant_wl_lookup_code
   uses isasat_input_bounded.literal_redundant_wl_lookup_code.refine_raw
   is \<open>(uncurry5 ?f, _) \<in> _\<close>

prepare_code_thms (in -) literal_redundant_wl_lookup_code_def

lemmas literal_redundant_wl_lookup_code_hnr[sepref_fr_rules] =
   literal_redundant_wl_lookup_code.refine[OF isasat_input_bounded_axioms]


abbreviation (in -) highest_lit_assn where
  \<open>highest_lit_assn \<equiv> option_assn (unat_lit_assn *a uint32_nat_assn)\<close>

sepref_register minimize_and_extract_highest_lookup_conflict
sepref_thm minimize_and_extract_highest_lookup_conflict_code
  is \<open>uncurry5 (PR_CONST minimize_and_extract_highest_lookup_conflict)\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), lbd), outl). literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf NU)]\<^sub>a
       trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d *\<^sub>a
        cach_refinement_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      lookup_clause_assn *a cach_refinement_assn *a out_learned_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    minimize_and_extract_highest_lookup_conflict_inv_def[simp]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_Suc_le_uint_max[intro] length_u_hnr[sepref_fr_rules]
    array_set_hnr_u[sepref_fr_rules]
  unfolding minimize_and_extract_highest_lookup_conflict_def zero_uint32_nat_def[symmetric]
    one_uint32_nat_def[symmetric] PR_CONST_def
    length_u_def[symmetric] minimize_and_extract_highest_lookup_conflict_inv_def
  by sepref

concrete_definition (in -) minimize_and_extract_highest_lookup_conflict_code
   uses isasat_input_bounded.minimize_and_extract_highest_lookup_conflict_code.refine_raw
   is \<open>(uncurry5 ?f, _) \<in> _\<close>

prepare_code_thms (in -) minimize_and_extract_highest_lookup_conflict_code_def

lemmas minimize_and_extract_highest_lookup_conflict_code_hnr[sepref_fr_rules] =
   minimize_and_extract_highest_lookup_conflict_code.refine[OF isasat_input_bounded_axioms]

end

end
