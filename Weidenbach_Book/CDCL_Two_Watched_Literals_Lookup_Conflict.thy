theory CDCL_Two_Watched_Literals_Lookup_Conflict
  imports CDCL_Two_Watched_Literals_Watch_List_Domain
    CDCL_Two_Watched_Literals_Watch_List_Code_Common
    CDCL_Two_Watched_Literals_IsaSAT_Trail
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
  case (Cons L P) note IH = this(1) and atm_P_xs = this(2) and uL_P = this(3) and dist = this(4) and
    tauto = this(5)
  then have mset: \<open>mset_as_position (fold (\<lambda>L xs. xs[atm_of L := Some (is_pos L)]) P xs) (mset P \<union># P')\<close>
    by (auto simp: tautology_add_mset)
  show ?case
  proof (cases \<open>L \<in># P'\<close>)
    case True
    then show ?thesis
      using mset dist
      by (metis (no_types, lifting) add_mset_union assms(2) distinct.simps(2) fold_simps(2)
       insert_DiffM list_update_id mset.simps(2) mset_as_position_nth set_mset_mset sup_union_right1)
  next
    case False
    have [simp]: \<open>length (fold (\<lambda>L xs. xs[atm_of L := Some (is_pos L)]) P xs) = length xs\<close>
      by (induction P arbitrary: xs) auto
    moreover have \<open>- L \<notin> set P\<close>
      using tauto by (metis list.set_intros(1) list.set_intros(2) set_mset_mset tautology_minus)
    moreover have \<open>fold (\<lambda>L xs. xs[atm_of L := Some (is_pos L)]) P (xs[atm_of L := Some (is_pos L)]) =
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

type_synonym (in -) conflict_rel = "nat \<times> bool option list"

definition conflict_rel :: "(conflict_rel \<times> nat literal multiset) set" where
\<open>conflict_rel = {((n, xs), C). n = size C \<and> mset_as_position xs C \<and>
   (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs)}\<close>

lemma conflict_rel_empty_iff: \<open>((n, xs), C) \<in> conflict_rel \<Longrightarrow> n = 0 \<longleftrightarrow> C = {#}\<close>
  by (auto simp: conflict_rel_def)

lemma conflict_atm_le_length: \<open>((n, xs), C) \<in> conflict_rel \<Longrightarrow> L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> L < length xs\<close>
  by (auto simp: conflict_rel_def)


lemma conflict_le_length:
  assumes
    c_rel: \<open>((n, xs), C) \<in> conflict_rel\<close> and
    L_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  shows \<open>atm_of L < length xs\<close>
proof -
  have
    size: \<open>n = size C\<close> and
    mset_pos: \<open>mset_as_position xs C\<close> and
    atms_le: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close>
    using c_rel unfolding conflict_rel_def by blast+
  have \<open>atm_of L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using L_\<L>\<^sub>a\<^sub>l\<^sub>l by (simp add: atms_of_def)
  then show ?thesis
    using atms_le by blast
qed

lemma conflict_rel_atm_in_iff:
  \<open>((n, xs), C) \<in> conflict_rel \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> L \<in>#C \<longleftrightarrow> xs!(atm_of L) = Some (is_pos L)\<close>
  by (rule mset_as_position_in_iff_nth)
     (auto simp: conflict_rel_def atms_of_def)

lemma (in isasat_input_bounded)
  assumes c: \<open>((n,xs), C) \<in> conflict_rel\<close>
  shows
    conflict_rel_not_tautolgy: \<open>\<not>tautology C\<close> and
    conflict_rel_distinct_mset: \<open>distinct_mset C\<close> and
    conflict_rel_size: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C \<Longrightarrow> size C \<le> 1 + uint_max div 2\<close>
proof -
  have mset: \<open>mset_as_position xs C\<close> and \<open>n = size C\<close> and \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close>
    using c unfolding conflict_rel_def by fast+
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

type_synonym (in -) conflict_assn = "uint32 \<times> bool option array"

definition conflict_assn :: "nat clause \<Rightarrow> conflict_assn \<Rightarrow> assn" where
\<open>conflict_assn = hr_comp (uint32_nat_assn *a array_assn (option_assn bool_assn)) conflict_rel\<close>

definition option_conflict_rel where
\<open>option_conflict_rel = {((b,(n,xs)), C). b = (C = None) \<and>
   (C = None \<longrightarrow> ((n,xs), {#}) \<in> conflict_rel) \<and>
   (C \<noteq> None \<longrightarrow> ((n,xs), the C) \<in> conflict_rel)}
   \<close>

lemma option_conflict_rel_conflict_rel_iff: 
   \<open>((False, (n, xs)), Some C) \<in> option_conflict_rel \<longleftrightarrow>
   ((n, xs), C) \<in> conflict_rel\<close>
   unfolding option_conflict_rel_def by auto


type_synonym (in -) conflict_option_assn = "bool \<times> uint32 \<times> bool option array"

abbreviation (in -) conflict_rel_assn :: \<open>conflict_rel \<Rightarrow> conflict_assn \<Rightarrow> assn\<close> where
 \<open>conflict_rel_assn \<equiv> (uint32_nat_assn *a array_assn (option_assn bool_assn))\<close>

type_synonym (in -) conflict_option_rel = \<open>bool \<times> nat \<times> bool option list\<close>

abbreviation (in -)conflict_option_rel_assn :: \<open>conflict_option_rel \<Rightarrow> conflict_option_assn \<Rightarrow> assn\<close> where
 \<open>conflict_option_rel_assn \<equiv> (bool_assn *a conflict_rel_assn)\<close>

definition conflict_option_assn
  :: \<open>nat clause option \<Rightarrow> conflict_option_assn \<Rightarrow> assn\<close>
where
  \<open>conflict_option_assn =
     hr_comp (bool_assn *a uint32_nat_assn *a array_assn (option_assn bool_assn))
       option_conflict_rel\<close>

definition (in -) conflict_assn_is_None :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>conflict_assn_is_None = (\<lambda>(b, _, _). b)\<close>

lemma conflict_assn_is_None_is_None: \<open>(RETURN o conflict_assn_is_None, RETURN o is_None) \<in>
  option_conflict_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
   (auto simp: option_conflict_rel_def conflict_assn_is_None_def split: option.splits)

lemma conflict_assn_is_None_conflict_assn_is_None:
 \<open>(return o conflict_assn_is_None, RETURN o conflict_assn_is_None) \<in>
  conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: conflict_assn_is_None_def)

lemma conflict_assn_is_None_is_none_Code[sepref_fr_rules]:
  \<open>(return \<circ> conflict_assn_is_None, RETURN \<circ> is_None) \<in> conflict_option_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
  using conflict_assn_is_None_conflict_assn_is_None[FCOMP conflict_assn_is_None_is_None,
  unfolded conflict_option_assn_def[symmetric]] .

definition (in -) conflict_assn_is_empty :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>conflict_assn_is_empty = (\<lambda>(_, n, _). n = 0)\<close>

lemma conflict_assn_is_empty_is_empty: 
  \<open>(RETURN o conflict_assn_is_empty, RETURN o (\<lambda>D. Multiset.is_empty(the D))) \<in>
  [\<lambda>D. D \<noteq> None]\<^sub>f option_conflict_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
   (auto simp: option_conflict_rel_def conflict_assn_is_empty_def conflict_rel_def
     Multiset.is_empty_def split: option.splits)

lemma conflict_assn_is_empty_conflict_assn_is_empty:
 \<open>(return o conflict_assn_is_empty, RETURN o conflict_assn_is_empty) \<in>
  conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: conflict_assn_is_empty_def uint32_nat_rel_def br_def nat_of_uint32_0_iff)

lemma conflict_assn_is_empty_is_empty_code[sepref_fr_rules]:
  \<open>(return \<circ> conflict_assn_is_empty, RETURN \<circ> the_is_empty) \<in>
      [\<lambda>D. D \<noteq> None]\<^sub>a conflict_option_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using conflict_assn_is_empty_conflict_assn_is_empty[FCOMP conflict_assn_is_empty_is_empty,
  unfolded conflict_option_assn_def[symmetric]] unfolding the_is_empty_def
  conflict_option_assn_def[symmetric]
  by simp

definition size_lookup_conflict :: \<open>_ \<Rightarrow> nat\<close> where
  \<open>size_lookup_conflict = (\<lambda>((_, n, _), _). n)\<close>

definition size_conflict_wl_heur :: \<open>_ \<Rightarrow> nat\<close> where
  \<open>size_conflict_wl_heur = (\<lambda>(M, N, U, D, _, _, _, _). size_lookup_conflict D)\<close>

lemma size_lookup_conflict[sepref_fr_rules]:
   \<open>(return o (\<lambda>((_, n, _), _). n), RETURN o size_lookup_conflict) \<in>
   (((bool_assn *a conflict_rel_assn) *a
         option_assn (unat_lit_assn *a uint32_nat_assn)))\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
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
    obtain bb :: "bool option \<Rightarrow> bool" where
      f1: "\<forall>z. z = None \<or> z = Some (bb z)"
      by (metis option.exhaust)
    have f2: "xs ! atm_of L \<noteq> Some (is_pos L)"
      using add.hyps(1) add.hyps(2) add.hyps(3) mset_as_position_in_iff_nth by blast
    have f3: "\<forall>z b. ((Some b = z \<or> z = None) \<or> bb z) \<or> b"
      using f1 by blast
    have f4: "\<forall>zs. (zs ! atm_of L \<noteq> Some (is_pos (- L)) \<or> \<not> atm_of L < length zs) \<or> \<not> mset_as_position zs P"
      by (metis add.hyps(4) atm_of_uminus mset_as_position_in_iff_nth)
    have "\<forall>z b. ((Some b = z \<or> z = None) \<or> \<not> bb z) \<or> \<not> b"
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


(* TODO Move *)
lemma (in -) count_list_filter: \<open>count_list xs x = length (filter (op = x) xs)\<close>
  by (induction xs) auto
lemma sum_length_filter_compl': \<open>length [x\<leftarrow>xs . \<not> P x] + length (filter P xs) = length xs\<close>
  using sum_length_filter_compl[of P xs] by auto
(* End Move *)



context isasat_input_bounded
begin

definition is_in_lookup_conflict where
  \<open>is_in_lookup_conflict = (\<lambda>(n, xs) L. \<not>is_None (xs ! atm_of L))\<close>

sepref_thm is_in_conflict_code
  is \<open>uncurry (RETURN oo is_in_lookup_conflict)\<close>
  :: \<open>[\<lambda>((n, xs), L). atm_of L < length xs]\<^sub>a
       conflict_rel_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> bool_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp] uint32_nat_assn_one[sepref_fr_rules]
  image_image[simp]
  unfolding is_in_lookup_conflict_def
  by sepref

concrete_definition (in -) is_in_conflict_code
   uses isasat_input_bounded.is_in_conflict_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) is_in_conflict_code_def

lemmas is_in_conflict_hnr[sepref_fr_rules] =
   is_in_conflict_code.refine[OF isasat_input_bounded_axioms]

definition conflict_merge :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> nat clause option \<Rightarrow> nat \<Rightarrow>
  (nat clause option \<times> nat) nres\<close> where
\<open>conflict_merge M N i _ _ = RES {(Some (mset (N!i)), card_max_lvl M (mset (N!i)))}\<close>

definition add_to_lookup_conflict :: \<open>nat literal \<Rightarrow> conflict_rel \<Rightarrow> conflict_rel\<close> where
  \<open>add_to_lookup_conflict = (\<lambda>L (n, xs). (if xs ! atm_of L = None then n + 1 else n,
      xs[atm_of L := Some (is_pos L)]))\<close>


definition lookup_conflict_merge'_step :: \<open>(nat, nat) ann_lits \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> conflict_rel \<Rightarrow> nat clause_l \<Rightarrow>
      nat clause \<Rightarrow> bool\<close> where
  \<open>lookup_conflict_merge'_step M i clvls zs D C = (
      let D' = mset (take i D);
          E = remdups_mset (D' + (C - D' - image_mset uminus D')) in
      ((False, zs), Some E) \<in> option_conflict_rel \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n E \<and> clvls = card_max_lvl M E)\<close>

lemma mset_as_position_remove:
  \<open>mset_as_position xs D \<Longrightarrow> L < length xs \<Longrightarrow> mset_as_position (xs[L := None]) (remove1_mset (Pos L) (remove1_mset (Neg L) D))\<close>
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

lemma option_conflict_rel_update_None:
  assumes  \<open>((False, (n, xs)), Some D) \<in> option_conflict_rel\<close> and L_xs : \<open>L < length xs\<close>
  shows \<open>((False, (if xs!L = None then n else n - 1, xs[L := None])),
      Some (D - {# Pos L, Neg L #})) \<in> option_conflict_rel\<close>
proof -
  have [simp]: "L \<notin># A \<Longrightarrow> A - add_mset L' (add_mset L B) = A - add_mset L' B"
    for A B :: \<open>'a multiset\<close> and L L'
    by (metis add_mset_commute minus_notin_trivial)
  have "n = size D" and map: "mset_as_position xs D"
    using assms by (auto simp: option_conflict_rel_def conflict_rel_def)
  have xs_None_iff: "xs ! L = None \<longleftrightarrow> Pos L \<notin># D \<and> Neg L \<notin># D"
    using map L_xs mset_as_position_in_iff_nth[of xs D "Pos L"] mset_as_position_in_iff_nth[of xs D "Neg L"]
    by (cases \<open>xs ! L\<close>) auto

  have 1: \<open>xs ! L = None \<Longrightarrow> D - {#Pos L, Neg L#} = D\<close>
    using assms by (auto simp: xs_None_iff minus_notin_trivial)
  have 2: \<open>xs ! L = None \<Longrightarrow> xs[L := None] = xs\<close>
   using map list_update_id[of xs L] by (auto simp: 1)
  have 3: \<open>xs ! L = Some y \<longleftrightarrow> (y \<and> Pos L \<in># D \<and> Neg L \<notin># D) \<or> (\<not>y \<and> Pos L \<notin># D \<and> Neg L \<in># D)\<close> for y
    using map L_xs mset_as_position_in_iff_nth[of xs D "Pos L"] mset_as_position_in_iff_nth[of xs D "Neg L"]
    by (cases \<open>xs ! L\<close>) auto

  show ?thesis
    using assms mset_as_position_remove[of xs D L]
    by (auto simp: option_conflict_rel_def conflict_rel_def 1 2 3 size_remove1_mset_If minus_notin_trivial
        mset_as_position_remove)
qed


lemma add_to_lookup_conflict_conflict_rel:
  assumes confl: \<open>((n, xs), C) \<in> conflict_rel\<close> and uL_C: \<open>-L \<notin># C\<close> and L_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  shows \<open>(add_to_lookup_conflict L (n, xs), {#L#} \<union># C) \<in> conflict_rel\<close>
proof -
  have
    n: \<open>n = size C\<close> and
    mset: \<open>mset_as_position xs C\<close> and
    atm: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close>
    using confl unfolding conflict_rel_def by blast+
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
      by (auto simp: conflict_rel_def add_to_lookup_conflict_def xs[symmetric])
  next
    case False
    with mset have \<open>xs ! atm_of L = None\<close>
      using mset_as_position_in_iff_nth[of xs C L]
       mset_as_position_in_iff_nth[of xs C \<open>-L\<close>]  atm_L_xs uL_C
      by (cases L; cases \<open>xs ! atm_of L\<close>) auto
    then show ?thesis
      using n mset atm False atm_L_xs uL_C
      by (auto simp: conflict_rel_def add_to_lookup_conflict_def
          intro!: mset_as_position.intros)
  qed
qed

definition lookup_conflict_merge
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clause_l \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> (conflict_option_rel \<times> nat) nres\<close>
where
  \<open>lookup_conflict_merge M D  = (\<lambda>(b, xs) clvls. do {
     (_, clvls, zs) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i::nat, clvls :: nat, zs). i \<le> length D \<and>
         length (snd zs) = length (snd xs) \<and>
             Suc i \<le> uint_max \<and> Suc (fst zs) \<le> uint_max \<and> Suc clvls \<le> uint_max\<^esup>
       (\<lambda>(i :: nat, clvls, zs). i < length D)
       (\<lambda>(i :: nat, clvls, zs). do{
           ASSERT(i < length D);
           ASSERT(Suc i \<le> uint_max);
            if get_level M (D!i) = count_decided M \<and> \<not>is_in_lookup_conflict zs (D!i) then
             RETURN(Suc i, clvls + 1, add_to_lookup_conflict (D!i) zs)
           else
             RETURN(Suc i, clvls, add_to_lookup_conflict (D!i) zs)
           })
       (0, clvls, xs);
     RETURN ((False, zs), clvls)
   })\<close>

definition lookup_conflict_merge_aa :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> (conflict_option_rel \<times> nat) nres\<close> where
  \<open>lookup_conflict_merge_aa M C i xs = lookup_conflict_merge M (C ! i) xs\<close>


sepref_register lookup_conflict_merge_aa
sepref_thm lookup_conflict_merge_code
  is \<open>uncurry4 (PR_CONST lookup_conflict_merge_aa)\<close>
  :: \<open>[\<lambda>((((M, N), i), (_, xs)), _). i < length N \<and> (\<forall>j<length (N!i). atm_of (N!i!j) < length (snd xs)) \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N!i))]\<^sub>a
       trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp] uint32_nat_assn_one[sepref_fr_rules]
  image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
  unfolding lookup_conflict_merge_aa_def lookup_conflict_merge_def add_to_lookup_conflict_def PR_CONST_def
  nth_rll_def[symmetric] length_rll_def[symmetric]
  apply (rewrite at \<open>_ + \<hole>\<close> annotate_assn[where A = \<open>uint32_nat_assn\<close>])
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) lookup_conflict_merge_code
   uses isasat_input_bounded.lookup_conflict_merge_code.refine_raw
   is \<open>(uncurry4 ?f, _) \<in> _\<close>

prepare_code_thms (in -) lookup_conflict_merge_code_def

lemmas lookup_conflict_merge_aa_hnr[sepref_fr_rules] =
   lookup_conflict_merge_code.refine[OF isasat_input_bounded_axioms]

lemma lookup_conflict_merge'_spec:
  assumes
      o: \<open>((b, n, xs), Some C) \<in> option_conflict_rel\<close> and
      dist: \<open>distinct D\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> and
      tauto: \<open>\<not>tautology (mset D)\<close> and
      \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C\<close> and
      \<open>clvls = card_max_lvl M C\<close>
  shows \<open>lookup_conflict_merge M D (b, n, xs) clvls \<le> \<Down> (option_conflict_rel \<times>\<^sub>r Id)
             (RES {(Some (mset D \<union># (C - mset D - uminus `# mset D)),
              card_max_lvl M (mset D \<union># (C - mset D - uminus `# mset D)))})\<close>
proof -
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
      conflict_rel_not_tautolgy[of n xs C]
    unfolding option_conflict_rel_def conflict_rel_def
    by (auto simp: uint_max_def)
  then have clvls_uint_max: \<open>clvls \<le> 1 + uint_max div 2\<close>
    using size_filter_mset_lesseq[of \<open>\<lambda>L. get_level M L = count_decided M\<close> C]
    unfolding uint_max_def card_max_lvl_def by linarith
  have [intro]: \<open>((b, a, ba), Some C) \<in> option_conflict_rel \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n C \<Longrightarrow>
        Suc (Suc a) \<le> uint_max\<close> for b a ba C
    using conflict_rel_size[of a ba C] by (auto simp: option_conflict_rel_def
        conflict_rel_def uint_max_def)
  have [simp]: \<open>remdups_mset C = C\<close>
    using o mset_as_position_distinct_mset[of xs C] by (auto simp: option_conflict_rel_def conflict_rel_def
        distinct_mset_remdups_mset_id)
  have \<open>\<not>tautology C\<close>
    using mset_as_position_tautology o by (auto simp: option_conflict_rel_def
        conflict_rel_def)
  have \<open>distinct_mset C\<close>
    using mset_as_position_distinct_mset[of _ C] o
    unfolding option_conflict_rel_def conflict_rel_def by auto
  let ?C' = \<open>\<lambda>a. mset (take a D) + (C - (mset (take a D) + uminus `# mset (take a D)))\<close>
  have tauto_C': \<open>\<not> tautology (?C' a)\<close> for a
    using tauto tauto_C dist dist_C unfolding tautology_decomp'
    by (auto dest: in_set_takeD in_diffD simp: distinct_mset_in_diff in_image_uminus_uminus)

  define I where
     \<open>I xs = (\<lambda>(i, clvls, zs :: conflict_rel).
                     i \<le> length D \<and>
                     length (snd zs) =
                     length (snd xs) \<and>
                     Suc i \<le> uint_max \<and>
                     Suc (fst zs) \<le> uint_max \<and>
                     Suc clvls \<le> uint_max)\<close>
   for xs :: conflict_rel
  define I' where \<open>I' = (\<lambda>(i, clvls, zs). lookup_conflict_merge'_step M i clvls zs D C)\<close>
  have
    if_True_I: \<open>I x2 (Suc a, aa + 1, add_to_lookup_conflict (D ! a) baa)\<close> (is ?I) and
    if_true_I': \<open>I' (Suc a, aa + 1, add_to_lookup_conflict (D ! a) baa)\<close> (is ?I')
    if
      I: \<open>I x2 s\<close> and
      I': \<open>I' s\<close> and
      \<open>case s of (i, clvls, zs) \<Rightarrow> i < length D\<close> and
      s: \<open>s = (a, ba)\<close> \<open>ba = (aa, baa)\<close> \<open>(b, n, xs) = (x1, x2)\<close> and
      a_le_D: \<open>a < length D\<close> and
      a_uint_max: \<open>Suc a \<le> uint_max\<close> and
      if_cond: \<open>get_level M (D ! a) = count_decided M \<and> \<not> is_in_lookup_conflict baa (D ! a)\<close>
    for x1 x2 s a ba aa baa
  proof -
    have [simp]:
      \<open>s = (a, aa, baa)\<close>
      \<open>ba = (aa, baa)\<close>
      \<open>x2 = (n, xs)\<close>
      using s by auto
    obtain ab b where baa[simp]: \<open>baa = (ab, b)\<close> by (cases baa)

    have aa: \<open>aa = card_max_lvl M (remdups_mset (?C' a))\<close> and
      ocr: \<open>((False, ab, b), Some (remdups_mset (?C' a))) \<in> option_conflict_rel\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (remdups_mset (?C' a))\<close>
      using I'
      unfolding I'_def lookup_conflict_merge'_step_def Let_def
      by auto
    have
      ab: \<open>ab = size (remdups_mset (?C' a))\<close> and
      map: \<open>mset_as_position b (remdups_mset (?C' a))\<close> and
      \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length b\<close> and
      cr: \<open>((ab, b), remdups_mset (?C' a)) \<in> conflict_rel\<close>
      using ocr unfolding option_conflict_rel_def conflict_rel_def
      by auto

    have \<open>size (card_max_lvl M (remdups_mset (?C' a))) \<le> size (remdups_mset (?C' a))\<close>
      unfolding card_max_lvl_def
      by auto
    then have [simp]: \<open>Suc (Suc aa) \<le> uint_max\<close>
      using size_C_uint_max lits
      simple_clss_size_upper_div2[of \<open>remdups_mset (?C' a)\<close>]
      unfolding uint_max_def aa[symmetric]
      by (auto simp: tauto_C')
    have [simp]: \<open>length b = length xs\<close> and
      \<open>a \<le> length D\<close>
      using I unfolding I_def by simp_all

    have ab_upper: \<open>Suc (Suc ab) \<le> uint_max\<close>
      using simple_clss_size_upper_div2[of \<open>remdups_mset (?C' a)\<close>]
      conflict_rel_not_tautolgy[OF cr] a_le_D lits mset_as_position_distinct_mset[OF map]
      unfolding ab literals_are_in_\<L>\<^sub>i\<^sub>n_remdups uint_max_def by auto
    show ?I
      using le_D_le_upper a_le_D ab_upper
      unfolding I_def add_to_lookup_conflict_def baa by auto
    have take_Suc_a[simp]: \<open>take (Suc a) D = take a D @ [D ! a]\<close>
      using take_Suc_conv_app_nth[OF a_le_D] .
    have [simp]: \<open>D ! a \<notin> set (take a D)\<close> \<open>- D ! a \<notin> set (take a D)\<close>
      using dist tauto apply (subst (asm) append_take_drop_id[symmetric, of _ \<open>Suc a\<close>]; auto)
      using tauto apply (subst (asm) append_take_drop_id[symmetric, of _ \<open>Suc a\<close>])
      unfolding mset_append take_Suc_a by (auto simp: tautology_add_mset)
    have D_a_notin: \<open>D ! a \<notin># (mset (take a D) + uminus `# mset (take a D))\<close>
      by (auto simp: uminus_lit_swap[symmetric])
    have uD_a_notin: \<open>-D ! a \<notin># (mset (take a D) + uminus `# mset (take a D))\<close>
      by (auto simp: uminus_lit_swap[symmetric])

    have [simp]: \<open>D ! a \<notin># C\<close> \<open>-D ! a \<notin># C\<close> \<open>b ! atm_of (D ! a) = None\<close>
      using if_cond mset_as_position_nth[OF map, of \<open>D ! a\<close>]
        if_cond mset_as_position_nth[OF map, of \<open>-D ! a\<close>] D_a_notin uD_a_notin
      by (auto simp: is_in_lookup_conflict_def  split: option.splits bool.splits
          dest: in_diffD)
    have [simp]: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> a_le_D] atms_le_xs
      by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

    have ocr: \<open>((False, add_to_lookup_conflict (D ! a) (ab, b)), Some (remdups_mset (?C' (Suc a))))
        \<in> option_conflict_rel\<close>
      using ocr D_a_notin uD_a_notin
      unfolding option_conflict_rel_def conflict_rel_def add_to_lookup_conflict_def
      by (auto dest: in_diffD simp: minus_notin_trivial
          intro!: mset_as_position.intros)

    show ?I'
      using D_a_notin uD_a_notin ocr lits if_cond
      unfolding I'_def lookup_conflict_merge'_step_def Let_def
      by (auto simp: minus_notin_trivial literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
          card_max_lvl_add_mset aa)
  qed
  have uL_C_if_L_C: \<open>-L \<notin># C\<close> if \<open>L \<in># C\<close> for L
    using tauto_C that unfolding tautology_decomp' by blast
  have
    if_False_I: \<open>I x2 (Suc a, aa, add_to_lookup_conflict (D ! a) baa)\<close> (is ?I) and
    if_False_I': \<open>I' (Suc a, aa, add_to_lookup_conflict (D ! a) baa)\<close> (is ?I')
    if
      I: \<open>I x2 s\<close> and
      I': \<open>I' s\<close> and
      \<open>case s of (i, clvls, zs) \<Rightarrow> i < length D\<close> and
      s: \<open>s = (a, ba)\<close> \<open>ba = (aa, baa)\<close> \<open>(b, n, xs) = (x1, x2)\<close> and
      a_le_D: \<open>a < length D\<close> and
      a_uint_max: \<open>Suc a \<le> uint_max\<close> and
      if_cond: \<open>\<not>(get_level M (D ! a) = count_decided M \<and> \<not> is_in_lookup_conflict baa (D ! a))\<close>
    for x1 x2 s a ba aa baa
  proof -
    have [simp]:
      \<open>s = (a, aa, baa)\<close>
      \<open>ba = (aa, baa)\<close>
      \<open>x2 = (n, xs)\<close>
      using s by auto
    obtain ab b where baa[simp]: \<open>baa = (ab, b)\<close> by (cases baa)

    have aa: \<open>aa = card_max_lvl M (remdups_mset (?C' a))\<close> and
      ocr: \<open>((False, ab, b), Some (remdups_mset (?C' a))) \<in> option_conflict_rel\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (remdups_mset (?C' a))\<close>
      using I'
      unfolding I'_def lookup_conflict_merge'_step_def Let_def
      by auto
    have
      ab: \<open>ab = size (remdups_mset (?C' a))\<close> and
      map': \<open>mset_as_position b (remdups_mset (?C' a))\<close> and
      \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length b\<close> and
      cr: \<open>((ab, b), remdups_mset (?C' a)) \<in> conflict_rel\<close>
      using ocr unfolding option_conflict_rel_def conflict_rel_def
      by auto

    have \<open>size (card_max_lvl M (remdups_mset (?C' a))) \<le> size (remdups_mset (?C' a))\<close>
      unfolding card_max_lvl_def
      by auto
    then have Suc_Suc_aa: \<open>Suc (Suc aa) \<le> uint_max\<close>
      using size_C_uint_max lits
      simple_clss_size_upper_div2[of \<open>remdups_mset (?C' a)\<close>]
      unfolding uint_max_def aa[symmetric]
      by (auto simp: tauto_C')
    have [simp]: \<open>length b = length xs\<close> and
      \<open>a \<le> length D\<close>
      using I unfolding I_def by simp_all

    have ab_upper: \<open>Suc (Suc ab) \<le> uint_max\<close>
      using simple_clss_size_upper_div2[of \<open>remdups_mset (?C' a)\<close>]
      conflict_rel_not_tautolgy[OF cr] a_le_D lits mset_as_position_distinct_mset[OF map']
      unfolding ab literals_are_in_\<L>\<^sub>i\<^sub>n_remdups uint_max_def by auto
    show ?I
      using a_le_D ab_upper Suc_Suc_aa
      unfolding I_def add_to_lookup_conflict_def baa by auto
    have take_Suc_a[simp]: \<open>take (Suc a) D = take a D @ [D ! a]\<close>
      using take_Suc_conv_app_nth[OF a_le_D] .
    have Da_take[simp]: \<open>D ! a \<notin> set (take a D)\<close> \<open>- D ! a \<notin> set (take a D)\<close>
      using dist tauto apply (subst (asm) append_take_drop_id[symmetric, of _ \<open>Suc a\<close>]; auto)
      using tauto apply (subst (asm) append_take_drop_id[symmetric, of _ \<open>Suc a\<close>])
      unfolding mset_append take_Suc_a by (auto simp: tautology_add_mset)
    have D_a_notin: \<open>D ! a \<notin># (mset (take a D) + uminus `# mset (take a D))\<close>
      by (auto simp: uminus_lit_swap[symmetric])
    have uD_a_notin: \<open>-D ! a \<notin># (mset (take a D) + uminus `# mset (take a D))\<close>
      by (auto simp: uminus_lit_swap[symmetric])

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

    consider
       (None) \<open>b ! atm_of (D ! a) = None\<close> |
       (SomeT) \<open>b ! atm_of (D ! a) = Some True\<close> |
       (SomeF) \<open>b ! atm_of (D ! a) = Some False\<close>
      by (cases \<open>b ! atm_of (D ! a)\<close>) auto
    then have ocr: \<open>((False, add_to_lookup_conflict (D ! a) (ab, b)), Some (remdups_mset (?C' (Suc a))))
      \<in> option_conflict_rel\<close>
    proof cases
      case [simp]: None
      have [simp]: \<open>D ! a \<notin># C\<close> \<open>-D ! a \<notin># C\<close>
        using if_cond mset_as_position_nth[OF map', of \<open>D ! a\<close>]
          if_cond mset_as_position_nth[OF map', of \<open>-D ! a\<close>] D_a_notin uD_a_notin
        by (auto simp: is_in_lookup_conflict_def split: option.splits bool.splits
            dest: in_diffD)
      have [simp]: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
        using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> a_le_D] atms_le_xs
        by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

      show ocr: \<open>((False, add_to_lookup_conflict (D ! a) (ab, b)), Some (remdups_mset (?C' (Suc a)))) \<in> option_conflict_rel\<close>
        using ocr D_a_notin uD_a_notin
        unfolding option_conflict_rel_def conflict_rel_def add_to_lookup_conflict_def
        by (auto dest: in_diffD simp: minus_notin_trivial
            intro!: mset_as_position.intros)
    next
      case SomeT
      have atm_Da_le: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
        using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> a_le_D] atms_le_xs
        by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
      define Da where
        \<open>Da = Pos (atm_of (D ! a))\<close>
      have uDa_C:  \<open>-Da \<notin># C\<close> and DaC: \<open>Da \<in># C\<close>
        using if_cond mset_as_position_in_iff_nth[OF map', of \<open>D ! a\<close>] SomeT
          if_cond mset_as_position_in_iff_nth[OF map', of \<open>-D ! a\<close>] D_a_notin uD_a_notin atm_Da_le
        by (cases \<open>D!a\<close>; auto simp: is_in_lookup_conflict_def is_pos_neg_not_is_pos Da_def
            split: option.splits bool.splits
            dest: in_diffD)+
      have [simp]: \<open>add_mset (- D ! a) (add_mset (D ! a) E) =  add_mset (- Da) (add_mset (Da) E)\<close> for E
        by (cases \<open>D!a\<close>; auto simp: is_in_lookup_conflict_def is_pos_neg_not_is_pos Da_def
            split: option.splits bool.splits
            dest: in_diffD)+
      have \<open>D ! a = Da \<or> D ! a = -Da\<close>
        by (cases \<open>D ! a\<close>) (auto simp: Da_def)
      obtain C' where C': \<open>C = add_mset Da C'\<close>
        using multi_member_split[OF DaC] by blast
      have [simp]: \<open>- Da \<notin># C'\<close> \<open>D ! a \<notin># C'\<close> \<open>Da \<notin># C'\<close> \<open>-D ! a \<notin># C'\<close>
        using uL_C_if_L_C[of \<open>D ! a\<close>] uL_C_if_L_C[of \<open>D ! a\<close>] C' dist_C unfolding Da_def
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+
      have [simp]: \<open>atm_of (D ! a) = atm_of Da\<close>
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+

      have [simp]: \<open>Da \<notin> set (take a D)\<close> \<open>Da \<notin> uminus ` set (take a D)\<close>
        \<open>- Da \<notin> set (take a D) \<close> \<open>-Da \<notin>  uminus ` set (take a D)\<close>
        using D_a_notin uD_a_notin
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+
      have [simp]: \<open>{#Pos (atm_of Da), Neg (atm_of Da)#} = {#Da, - Da#}\<close>
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+

      have map'': \<open>mset_as_position (b[atm_of Da := None])
          (remdups_mset (mset (take a D) + (C' - (mset (take a D) + uminus `# mset (take a D)))))\<close>
        using mset_as_position_remove[of b _ \<open>atm_of Da\<close>, OF map'] atm_Da_le
        by (auto simp: C')

      have map'':\<open>mset_as_position (b[atm_of Da := Some (is_pos (D ! a))])
        (add_mset (D ! a) (remdups_mset (mset (take a D) + (C' - (mset (take a D) + uminus `# mset (take a D))))))\<close>
        apply (rule mset_as_position.add[OF map''])
        subgoal using atm_Da_le by simp
        subgoal using dist_C by (auto simp: C' distinct_mset_in_diff)
        subgoal using dist_C by (auto simp: C' distinct_mset_in_diff)
        subgoal by auto
        done
      show ?thesis
        using uDa_C SomeT dist_C  map'' atms_le_xs
        unfolding option_conflict_rel_def conflict_rel_def add_to_lookup_conflict_def ab Da_def[symmetric] C'
        by (auto dest:  simp: distinct_mset_in_diff minus_notin_trivial
            intro: mset_as_position.intros)
    next
      case SomeF
      have atm_Da_le: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
        using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> a_le_D] atms_le_xs
        by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
      define Da where
        \<open>Da = Neg (atm_of (D ! a))\<close>
      have uDa_C:  \<open>-Da \<notin># C\<close> and DaC: \<open>Da \<in># C\<close>
        using if_cond mset_as_position_in_iff_nth[OF map', of \<open>D ! a\<close>] SomeF
          if_cond mset_as_position_in_iff_nth[OF map', of \<open>-D ! a\<close>] D_a_notin uD_a_notin atm_Da_le
        by (cases \<open>D!a\<close>; auto simp: is_in_lookup_conflict_def is_pos_neg_not_is_pos Da_def
            split: option.splits bool.splits
            dest: in_diffD)+
      have [simp]: \<open>add_mset (- D ! a) (add_mset (D ! a) E) =  add_mset (- Da) (add_mset (Da) E)\<close> for E
        by (cases \<open>D!a\<close>; auto simp: is_in_lookup_conflict_def is_pos_neg_not_is_pos Da_def
            split: option.splits bool.splits
            dest: in_diffD)+
      have \<open>D ! a = Da \<or> D ! a = -Da\<close>
        by (cases \<open>D ! a\<close>) (auto simp: Da_def)
      obtain C' where C': \<open>C = add_mset Da C'\<close>
        using multi_member_split[OF DaC] by blast
      have [simp]: \<open>- Da \<notin># C'\<close> \<open>D ! a \<notin># C'\<close> \<open>Da \<notin># C'\<close> \<open>-D ! a \<notin># C'\<close>
        using uL_C_if_L_C[of \<open>D ! a\<close>] uL_C_if_L_C[of \<open>D ! a\<close>] C' dist_C unfolding Da_def
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+
      have [simp]: \<open>atm_of (D ! a) = atm_of Da\<close>
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+

      have [simp]: \<open>Da \<notin> set (take a D)\<close> \<open>Da \<notin> uminus ` set (take a D)\<close>
        \<open>- Da \<notin> set (take a D) \<close> \<open>-Da \<notin>  uminus ` set (take a D)\<close>
        using D_a_notin uD_a_notin
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+
      have [simp]: \<open>{#Pos (atm_of Da), Neg (atm_of Da)#} = {#Da, - Da#}\<close>
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+

      have map'': \<open>mset_as_position (b[atm_of Da := None])
          (remdups_mset (mset (take a D) + (C' - (mset (take a D) + uminus `# mset (take a D)))))\<close>
        using mset_as_position_remove[of b _ \<open>atm_of Da\<close>, OF map'] atm_Da_le
        by (auto simp: C')

      have map'':\<open>mset_as_position (b[atm_of Da := Some (is_pos (D ! a))])
        (add_mset (D ! a) (remdups_mset (mset (take a D) +
          (C' - (mset (take a D) + uminus `# mset (take a D))))))\<close>
        apply (rule mset_as_position.add[OF map''])
        subgoal using atm_Da_le by simp
        subgoal using dist_C by (auto simp: C' distinct_mset_in_diff)
        subgoal using dist_C by (auto simp: C' distinct_mset_in_diff)
        subgoal by auto
        done
      show ?thesis
        using uDa_C SomeF dist_C  map'' atms_le_xs
        unfolding option_conflict_rel_def conflict_rel_def add_to_lookup_conflict_def ab Da_def[symmetric] C'
        by (auto dest:  simp: distinct_mset_in_diff minus_notin_trivial
            intro: mset_as_position.intros)
    qed
    have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n
     ((mset (take a D) +
      (C -
       add_mset (- D ! a)
        (add_mset (D ! a)
          (mset (take a D) + uminus `# mset (take a D))))))\<close>
      by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF lits[unfolded literals_are_in_\<L>\<^sub>i\<^sub>n_remdups]])
         (auto simp: diff_le_mono2_mset)
    moreover {
      have K: \<open>D ! a = Neg L \<Longrightarrow>is_in_lookup_conflict (ab, b) (Neg L) \<Longrightarrow> L < length xs  \<Longrightarrow>
          Pos L \<notin># C \<Longrightarrow> Neg L \<notin># C \<Longrightarrow> False\<close>
        for L
      using  mset_as_position_in_iff_nth[OF map', of \<open>Pos L\<close>] that
        mset_as_position_in_iff_nth[OF map', of \<open>Neg L\<close>] Da_take
      by (cases \<open>D ! a\<close>)
       (auto simp: is_in_lookup_conflict_def dist_C distinct_mset_in_diff
          split: option.splits bool.splits
          dest: in_diffD)
      have K': \<open>D ! a = Pos L \<Longrightarrow>is_in_lookup_conflict (ab, b) (Pos L) \<Longrightarrow> L < length xs  \<Longrightarrow>
          Pos L \<notin># C \<Longrightarrow> Neg L \<notin># C \<Longrightarrow> False\<close>
        for L
      using  mset_as_position_in_iff_nth[OF map', of \<open>Pos L\<close>] that
        mset_as_position_in_iff_nth[OF map', of \<open>Neg L\<close>] Da_take
      by (cases \<open>D ! a\<close>)
       (auto simp: is_in_lookup_conflict_def dist_C distinct_mset_in_diff
          split: option.splits bool.splits
          dest: in_diffD)
      have \<open>card_max_lvl M (remdups_mset (?C' a)) = card_max_lvl M (remdups_mset (?C' (Suc a)))\<close>
      apply (rule card_max_lvl_distinct_cong)
      subgoal for L
        apply (cases \<open>D ! a\<close>)
        supply get_level_uminus[of M \<open>Pos L\<close>, simplified, simp]
        using if_cond \<open>D ! a \<notin> set (take a D)\<close> \<open>- D ! a \<notin> set (take a D)\<close>
          get_level_uminus[of M \<open>Pos L\<close>, simplified]
        by (auto simp: distinct_mset_in_diff dist_C image_Un atm_of_notin_atms_of_iff
            atm_iff_pos_or_neg_lit uminus_lit_swap eq_commute[of \<open>Neg _\<close> \<open>- _\<close>]
             eq_commute[of \<open>Pos _\<close> \<open>- _\<close>])
      subgoal for L
        apply (cases \<open>D ! a\<close>)
        supply get_level_uminus[of M \<open>Pos L\<close>, simplified, simp]
        using if_cond \<open>D ! a \<notin> set (take a D)\<close> \<open>- D ! a \<notin> set (take a D)\<close>
          get_level_uminus[of M \<open>Pos L\<close>, simplified] atm_D_a_le_xs K[of L] K'[of L]
        apply (auto split: )
        apply (auto simp: distinct_mset_in_diff dist_C image_Un atm_of_notin_atms_of_iff
            atm_iff_pos_or_neg_lit uminus_lit_swap eq_commute[of \<open>Neg _\<close> \<open>- _\<close>]
             eq_commute[of \<open>Pos _\<close> \<open>- _\<close>])
        done
      subgoal by simp
      subgoal using map' mset_as_position_tautology by blast
      subgoal by simp
      subgoal using ocr unfolding option_conflict_rel_def conflict_rel_def
        by (auto dest!: mset_as_position_tautology)
      done }
    ultimately show ?I'
      using D_a_notin uD_a_notin ocr lits if_cond atm_D_a_le_xs
      unfolding I'_def lookup_conflict_merge'_step_def Let_def
      by (auto simp: minus_notin_trivial literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
          card_max_lvl_add_mset aa)
  qed

  have dist_D: \<open>distinct_mset (mset D)\<close>
    using dist by auto
  have dist_CD: \<open>distinct_mset (C - mset D - uminus `# mset D)\<close>
    using \<open>distinct_mset C\<close> by auto
  have confl: \<open>lookup_conflict_merge M D (b, n, xs) clvls
    \<le> \<Down> (option_conflict_rel \<times>\<^sub>r Id)
       (RES {(Some (mset D \<union># (C - mset D - uminus `# mset D)),
              card_max_lvl M (mset D \<union># (C - mset D - uminus `# mset D)))})\<close>
    unfolding lookup_conflict_merge_aa_def lookup_conflict_merge_def PR_CONST_def
    distinct_mset_rempdups_union_mset[OF dist_D dist_CD] I_def[symmetric] conc_fun_SPEC
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(j, _). length D - j)\<close> and
          I' = I'])
    subgoal by auto
    subgoal using clvls_uint_max Suc_N_uint_max unfolding uint_max_def I_def by auto
    subgoal using assms
      unfolding lookup_conflict_merge'_step_def Let_def option_conflict_rel_def I'_def
      by (auto simp add: uint_max_def lookup_conflict_merge'_step_def option_conflict_rel_def)
    subgoal by auto
    subgoal unfolding I_def by fast
    subgoal by (rule if_True_I)
    subgoal by (rule if_true_I')
    subgoal for b' n' s j zs
      using dist lits tauto
      by (auto simp: option_conflict_rel_def take_Suc_conv_app_nth
          literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l)
    subgoal by (rule if_False_I)
    subgoal by (rule if_False_I')
    subgoal by auto
    subgoal using assms by (auto simp: option_conflict_rel_def lookup_conflict_merge'_step_def Let_def
          I_def I'_def)
    done
  have count_D: \<open>count (mset D) a = 1 \<or> count (mset D) a = 0\<close> for a
    using dist_D unfolding distinct_mset_def by auto
  have count_C: \<open>count C a = 1 \<or> count C a = 0\<close> for a
    using \<open>distinct_mset C\<close> unfolding distinct_mset_def by auto
  have \<open>mset D \<union># (C - mset D - image_mset uminus (mset D)) =
      mset D \<union># (C - image_mset uminus (mset D))\<close>
    apply (rule multiset_eqI)
    subgoal for a
      using count_D[of a] count_C[of a] by (auto simp: max_def)
    done
  then show ?thesis
    using confl by simp
qed

lemma lookup_conflict_merge_aa_set_conflict:
  \<open>(uncurry4 lookup_conflict_merge_aa, uncurry4 conflict_merge) \<in>
    [\<lambda>((((M, N), i), xs), clvls). i < length N \<and> xs = None \<and> distinct (N ! i) \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i)) \<and> \<not>tautology (mset (N ! i)) \<and> clvls = 0]\<^sub>f
    \<langle>Id\<rangle>list_rel \<times>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f option_conflict_rel \<times>\<^sub>f nat_rel \<rightarrow>
      \<langle>option_conflict_rel \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
proof -
  have [simp]: \<open>\<not>tautology (mset C) \<Longrightarrow> j < length C \<Longrightarrow> -C ! j \<notin> set (take j C)\<close> for j C
    by (meson in_multiset_in_set in_set_takeD nth_mem_mset tautology_minus)
  have [simp]: \<open>distinct C \<Longrightarrow> j < length C \<Longrightarrow> C ! j \<notin> set (take j C)\<close> for j C
    by (simp add: index_nth_id index_take)
  have H: \<open>lookup_conflict_merge_aa M N i (b, n, xs) clvls \<le> \<Down> (option_conflict_rel \<times>\<^sub>r nat_rel)
      (conflict_merge M N i None clvls)\<close>
    if
      \<open>i < length N\<close> and
      ocr: \<open>((b, n, xs), None) \<in> option_conflict_rel\<close> and
     dist: \<open>distinct (N! i)\<close> and
     lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i))\<close> and
     tauto: \<open>\<not>tautology (mset (N ! i))\<close> and
     \<open>clvls = 0\<close>
    for b n xs N i M clvls
  proof -
    have [simp]: \<open>remdups_mset (mset (N ! i)) = mset (N!i)\<close>
      using distinct_mset_remdups_mset_id[of \<open>mset (N!i)\<close>] dist by auto
    have lookup_conflict_merge_normalise: \<open>lookup_conflict_merge M C (b, zs) = lookup_conflict_merge M C (False, zs)\<close>
      for M C zs
      unfolding lookup_conflict_merge_def by auto
    have T: \<open>((False, n, xs), Some {#}) \<in> option_conflict_rel\<close>
      using ocr unfolding option_conflict_rel_def by auto
    then show ?thesis unfolding lookup_conflict_merge_aa_def conflict_merge_def
      using lookup_conflict_merge'_spec[of False n xs \<open>{#}\<close> \<open>N!i\<close>] that dist
      by (auto simp: lookup_conflict_merge_normalise)
  qed
  show ?thesis
    unfolding lookup_conflict_merge_def uncurry_def
    by (intro nres_relI frefI) (auto simp: H)
qed

theorem lookup_conflict_merge_code_set_conflict[sepref_fr_rules]:
  \<open>(uncurry4 lookup_conflict_merge_code, uncurry4 conflict_merge) \<in>
  [\<lambda>((((M, N), i), xs), clvls). clvls = 0 \<and> i < length N \<and> xs = None \<and> distinct (N ! i) \<and>
    literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i)) \<and> \<not> tautology (mset (N ! i))]\<^sub>a
  trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
    conflict_option_assn *a uint32_nat_assn\<close>
   (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
   have H: \<open>?c
  \<in> [comp_PRE
     (\<langle>Id\<rangle>list_rel \<times>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f
      option_conflict_rel \<times>\<^sub>f
      nat_rel)
     (\<lambda>((((M, N), i), xs), clvls).
         i < length N \<and>
         xs = None \<and>
         distinct (N ! i) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i)) \<and>
         \<not> tautology (mset (N ! i)) \<and> clvls = 0)
     (\<lambda>_ ((((M, N), i), _, xs), _).
         i < length N \<and>
         (\<forall>j<length (N ! i). atm_of (N ! i ! j) < length (snd xs)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i)))
     (\<lambda>_. True)]\<^sub>a hrp_comp
                    ((hr_comp trail_pol_assn trail_pol)\<^sup>k *\<^sub>a
                     clauses_ll_assn\<^sup>k *\<^sub>a
                     nat_assn\<^sup>k *\<^sub>a
                     conflict_option_rel_assn\<^sup>d *\<^sub>a
                     uint32_nat_assn\<^sup>k)
                    (\<langle>Id\<rangle>list_rel \<times>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f
                     nat_rel \<times>\<^sub>f
                     option_conflict_rel \<times>\<^sub>f
                     nat_rel) \<rightarrow> hr_comp
                                  (conflict_option_rel_assn *a
                                   uint32_nat_assn)
                                  (option_conflict_rel \<times>\<^sub>f nat_rel)\<close>
   (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
     using hfref_compI_PRE_aux[OF lookup_conflict_merge_code.refine[unfolded PR_CONST_def]
        lookup_conflict_merge_aa_set_conflict[unfolded PR_CONST_def], OF isasat_input_bounded_axioms]
     unfolding PR_CONST_def
     .
  have pre: \<open>?pre' = ?pre\<close>
    by (intro ext) (auto simp: comp_PRE_def in_br_conv list_mset_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        literals_to_update_wl_empty_def option_conflict_rel_def conflict_rel_def
        dest: literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp conflict_option_assn_def
    by (auto simp: prod_hrp_comp hrp_comp_def hr_comp_invalid)

  have post: \<open>?f' = ?f\<close>
    by (auto simp: list_assn_list_mset_rel_eq_list_mset_assn
       conflict_option_assn_def)
  show ?thesis using H unfolding PR_CONST_def pre post im .
qed


definition (in -) is_in_conflict :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> bool\<close> where
  \<open>is_in_conflict L C \<longleftrightarrow> L \<in># the C\<close>

definition (in -) is_in_lookup_option_conflict :: \<open>nat literal \<Rightarrow> (bool \<times> nat \<times> bool option list) \<Rightarrow> bool\<close> where
  \<open>is_in_lookup_option_conflict = (\<lambda>L (_, _, xs). xs ! atm_of L = Some (is_pos L))\<close>

lemma is_in_lookup_option_conflict_is_in_conflict:
  \<open>(uncurry (RETURN oo is_in_lookup_option_conflict), uncurry (RETURN oo is_in_conflict)) \<in>
     [\<lambda>(L, C). C \<noteq> None \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>r option_conflict_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro nres_relI frefI)
  subgoal for Lxs LC
    using conflict_rel_atm_in_iff[of _ \<open>snd (snd (snd Lxs))\<close>]
    apply (cases Lxs)
    by (auto simp: is_in_lookup_option_conflict_def is_in_conflict_def option_conflict_rel_def)
  done

sepref_definition (in -) is_in_lookup_option_conflict_code
  is \<open>uncurry (RETURN oo is_in_lookup_option_conflict)\<close>
  :: \<open>[\<lambda>(L, (b, n, xs)). atm_of L < length xs]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a (bool_assn *a conflict_rel_assn)\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_in_lookup_option_conflict_def
  by sepref


lemma is_in_lookup_option_conflict_code_is_in_conflict[sepref_fr_rules]:
  \<open>(uncurry is_in_lookup_option_conflict_code,
     uncurry (RETURN oo is_in_conflict)) \<in>
    [\<lambda>(L, C). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> C \<noteq> None]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>k  \<rightarrow> bool_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (Id \<times>\<^sub>f option_conflict_rel) (\<lambda>(L, C). C \<noteq> None \<and> L \<in> snd ` D\<^sub>0)
          (\<lambda>_ (L, b, n, xs). atm_of L < length xs)
          (\<lambda>_. True)]\<^sub>a
      hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a (bool_assn *a conflict_rel_assn)\<^sup>k) (Id \<times>\<^sub>f option_conflict_rel)
       \<rightarrow>
      hr_comp bool_assn bool_rel\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF is_in_lookup_option_conflict_code.refine is_in_lookup_option_conflict_is_in_conflict]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff conflict_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    conflict_assn_def conflict_option_assn_def
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
end