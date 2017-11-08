theory CDCL_Two_Watched_Literals_Lookup_Conflict
  imports CDCL_Two_Watched_Literals_Watch_List_Domain
    CDCL_Two_Watched_Literals_Watch_List_Code_Common
    CDCL_Two_Watched_Literals_IsaSAT_Trail
    CDCL_Conflict_Minimisation
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

definition (in -) is_in_lookup_conflict where
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

lemma (in isasat_input_ops)mset_as_position_remove:
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
  [simp]: \<open>is_in_conflict L C \<longleftrightarrow> L \<in># the C\<close>

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
  \<open>(RETURN o id, conflict_from_lookup) \<in> [\<lambda>(n, xs). \<exists>D. ((n, xs), D) \<in> conflict_rel]\<^sub>f Id \<rightarrow>
    \<langle>conflict_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: conflict_rel_def conflict_from_lookup_def RETURN_RES_refine_iff)

end

definition confl_find_next_index_spec where
 \<open>confl_find_next_index_spec = (\<lambda>(n, xs) i.
     SPEC(\<lambda>j. (j \<ge> i \<and> j < length xs \<and> xs ! j \<noteq> None \<and>
        (\<forall>k. k \<ge> i \<longrightarrow> k < j \<longrightarrow> xs ! k = None))))\<close>

definition confl_find_next_index :: \<open>conflict_rel \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
   \<open>confl_find_next_index = (\<lambda>(n, xs) i.
      WHILE\<^sub>T\<^bsup>\<lambda>j. j < length xs \<and> (\<forall>k. k \<ge> i \<longrightarrow> k < j \<longrightarrow> xs ! k = None) \<and> j \<ge> i\<^esup>
           (\<lambda>j. xs ! j = None)
           (\<lambda>j. RETURN (j + 1))
           i
    )
\<close>


context isasat_input_ops
begin

lemma confl_find_next_index_confl_find_next_index_spec:
  assumes ocr: \<open>((n, xs), D) \<in> conflict_rel\<close> and \<open>n > 0\<close> and i_xs: \<open>i < length xs\<close> and
    le_i: \<open>\<forall>k<i. xs ! k = None\<close>
  shows
    \<open>confl_find_next_index (n, xs) i \<le> confl_find_next_index_spec (n,xs) i\<close>
proof -
  have
    n_D: \<open>n = size D\<close> and
    map: \<open>mset_as_position xs D\<close> and
    \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close>
    using ocr unfolding conflict_rel_def by auto
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
      using ex_not_none by fastforce
  qed
  show ?thesis
    unfolding confl_find_next_index_def confl_find_next_index_spec_def prod.case
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>i. length xs - i)\<close>])
    subgoal by auto
    subgoal by (rule i_xs)
    subgoal by auto
    subgoal by auto
    subgoal for j by (rule Sucj_le_xs)
    subgoal for j j'
      using nat_less_le by fastforce
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

end

definition iterate_over_conflict_inv where
  \<open>iterate_over_conflict_inv D\<^sub>0 = (\<lambda>(D, D', s). D \<subseteq># D\<^sub>0)\<close>

definition iterate_over_conflict
  :: \<open>('v clause \<Rightarrow> 'v literal \<Rightarrow> 'state \<Rightarrow> ('state \<times> bool) nres) \<Rightarrow>
      'v clause \<Rightarrow> 'state \<Rightarrow> ('v clause \<times> 'state) nres\<close>
where
  \<open>iterate_over_conflict f D\<^sub>0 s = do {
    (D, _, s) \<leftarrow>
       WHILE\<^sub>T\<^bsup>iterate_over_conflict_inv D\<^sub>0\<^esup>
       (\<lambda>(D, D', s). D' \<noteq> {#})
       (\<lambda>(D, D', s). do{
          ASSERT(D \<noteq> {#});
          x \<leftarrow> SPEC (\<lambda>x. x \<in># D');
          (s', keep) \<leftarrow> f D x s;
          if keep
          then RETURN (D, remove1_mset x D', s')
          else RETURN (remove1_mset x D, remove1_mset x D', s')
          })
       (D\<^sub>0, D\<^sub>0, s);
     RETURN (D, s)
}\<close>


definition iterate_over_lookup_conflict_inv where
  \<open>iterate_over_lookup_conflict_inv D = (\<lambda>((n, xs), m, i, s). n \<ge> m)\<close>

definition iterate_over_lookup_conflict
  :: \<open>(conflict_rel \<Rightarrow> nat literal \<Rightarrow> 'state \<Rightarrow> ('state \<times> bool) nres) \<Rightarrow>
      conflict_rel \<Rightarrow> 'state \<Rightarrow> (conflict_rel \<times> 'state) nres\<close>
where
  \<open>iterate_over_lookup_conflict  = (\<lambda>f (n, xs) s. do {
    (D, _, _, s) \<leftarrow>
       WHILE\<^sub>T\<^bsup>iterate_over_lookup_conflict_inv (n, xs)\<^esup>
         (\<lambda>((n, xs), m, i, s). m > 0)
         (\<lambda>((n, xs), m, i, s). do{
            ASSERT(m > 0);
            x \<leftarrow> confl_find_next_index_spec (m, xs) i;
            (s', keep) \<leftarrow> f (n, xs) (if the (xs ! x) then Pos x else Neg x) s;
            ASSERT(x < length xs);
            ASSERT(m \<ge> 1);
            ASSERT(n \<ge> 1);
            if keep
            then RETURN ((n, xs), m - 1, x+1, s')
            else RETURN ((n - 1, xs[x := None]), m - 1, x+1, s')
          })
         ((n, xs), n, 0, s);
     RETURN (D, s)
  })\<close>

context isasat_input_ops
begin

lemma iterate_over_lookup_conflict_iterate_over_conflict:
  fixes D :: \<open>nat clause\<close> and s :: 'state and s' :: 'state2 and Rstate :: \<open>('state2 \<times> 'state) set\<close> and
    f' :: \<open>conflict_rel \<Rightarrow> nat literal \<Rightarrow> 'state2 \<Rightarrow> ('state2 \<times> bool) nres\<close> and
    f :: \<open>nat clause \<Rightarrow> nat literal \<Rightarrow> 'state \<Rightarrow> ('state \<times> bool) nres\<close>
  assumes
    D'_D: \<open>(D', D) \<in> conflict_rel\<close> and
    f'_f: \<open>\<And>E' E s s' x. (E', E) \<in> conflict_rel \<Longrightarrow> (s', s) \<in> Rstate \<Longrightarrow> x \<in># D \<Longrightarrow>
          f' E' x s' \<le> \<Down> (Rstate \<times>\<^sub>r bool_rel) (f E x s)\<close> and
    s'_s: \<open>(s', s) \<in> Rstate\<close>
  shows
    \<open>iterate_over_lookup_conflict f' D' s' \<le> \<Down> (conflict_rel \<times>\<^sub>r Rstate) (iterate_over_conflict f D s)\<close>
proof -
  obtain n\<^sub>0 xs\<^sub>0 where D'[simp]: \<open>D' = (n\<^sub>0, xs\<^sub>0)\<close>
    by (cases D')
  define R where
    \<open>R = {(((n, xs), m, i, s' :: 'state2), (F :: nat clause, E :: nat clause, s :: 'state)).
            ((n, xs), F) \<in> conflict_rel \<and>
            i \<le> length xs \<and>
            ((m, replicate i None @ drop i xs), E) \<in> conflict_rel \<and>
            (s', s) \<in> Rstate \<and>
            n \<ge> m \<and>
            F \<subseteq># D \<and>
            E \<subseteq># F
        }\<close>
  have init_args_ref:
    \<open>iterate_over_conflict_inv D (D, D, s) \<Longrightarrow> (((n\<^sub>0, xs\<^sub>0), n\<^sub>0, 0, s'), D, D, s) \<in> R\<close>
    using D'_D s'_s unfolding R_def by auto

  have init_lo_inv: \<open>iterate_over_lookup_conflict_inv (n\<^sub>0, xs\<^sub>0) s'\<close>
    if
      \<open>(s', s) \<in> R\<close> and
      \<open>iterate_over_conflict_inv D s\<close>
    for s' s
  proof -
    show ?thesis
      using that unfolding iterate_over_lookup_conflict_inv_def by (auto simp: R_def)
  qed
  have cond: \<open>(0 < m) = (D' \<noteq> {#})\<close>
    if
      st'_st: \<open>(st', st) \<in> R\<close> and
      \<open>iterate_over_lookup_conflict_inv (n\<^sub>0, xs\<^sub>0) st'\<close> and
      \<open>iterate_over_conflict_inv D st\<close> and
      st:
        \<open>nxs = (n, xs)\<close>
        \<open>x2b = (j, x2c)\<close>
        \<open>x2a = (m, x2b)\<close>
        \<open>st' = (nxs, x2a)\<close>
        \<open>x2d = (D', s)\<close>
        \<open>st = (E, x2d)\<close>
    for st' st nxs n xs x2a m x2b j x2c x2d D' s E
  proof -
    show ?thesis
      using st'_st unfolding st
      by (cases D') (auto simp: R_def conflict_rel_def)
  qed
  have confl_find_next_index_spec_le:
    \<open>confl_find_next_index_spec (x1d, x2b) x1e
      \<le> \<Down> {(j, x). x2b ! j \<noteq> None \<and> x = (if the (x2b!j) then Pos j else Neg j) \<and>
             j < length x2b \<and> x1e \<le> j \<and> (\<forall>k\<ge>x1e. k < j \<longrightarrow> x2b ! k = None)}
          (SPEC (\<lambda>x. x \<in># x1a))\<close>
    (is \<open>_ \<le> \<Down> ?confl _\<close>)
    if
      R: \<open>(x, x') \<in> R\<close> and
      st:
        \<open>x2 = (x1a, x2a)\<close>
        \<open>x' = (x1, x2)\<close>
        \<open>x1b = (x1c, x2b)\<close>
        \<open>x2d = (x1e, x2e)\<close>
        \<open>x2c = (x1d, x2d)\<close>
        \<open>x = (x1b, x2c)\<close> and
        \<open>x1 \<noteq> {#}\<close> and
      x1d: \<open>0 < x1d\<close>
    for x x' x1 x2 x1a x2a x1b x1c x2b x2c x1d x2d x1e x2e
  proof -
    have map: \<open>mset_as_position (replicate x1e None @ drop x1e x2b) x1a\<close>
      using R unfolding st R_def conflict_rel_def
      by auto
    show ?thesis
      unfolding confl_find_next_index_spec_def st
      apply clarify
      apply (rule RES_refine)
      subgoal for s
        using x1d mset_as_position_in_iff_nth[OF map, of \<open>Pos s\<close>]
          x1d mset_as_position_in_iff_nth[OF map, of \<open>Neg s\<close>]
        by (auto simp: nth_append intro!: )
      done
  qed
  have f'_f_ref: \<open>f' (x1c, x2b) (if the (x2b ! xa) then Pos xa else Neg xa) x2e
      \<le> \<Down> (Rstate \<times>\<^sub>r bool_rel)
          (f x1 xb x2a)\<close>
    if
      R: \<open>(x, x') \<in> R\<close> and
      st:
        \<open>x2 = (x1a, x2a)\<close>
        \<open>x' = (x1, x2)\<close>
        \<open>x1b = (x1c, x2b)\<close>
        \<open>x2d = (x1e, x2e)\<close>
        \<open>x2c = (x1d, x2d)\<close>
        \<open>x = (x1b, x2c)\<close> and
      xb_x1a: \<open>xb \<in> {x. x \<in># x1a}\<close> and
      \<open>x1 \<noteq> {#}\<close> and
      \<open>0 < x1d\<close> and
      x: \<open>(xa, xb) \<in> ?confl x2b x1e\<close>
    for x x' x1 x2 x1a x2a x1b x1c x2b x2c x1d x2d x1e x2e xa xb
  proof -
    have xb: \<open>(if the (x2b ! xa) then Pos xa else Neg xa) = xb\<close>
      using x st by auto
    have 2: \<open>((x1c, x2b), x1) \<in> conflict_rel\<close>
      using R x unfolding R_def st by auto
    moreover have 1: \<open>(x2e, x2a) \<in> Rstate\<close>
      using R x unfolding R_def st by auto
    moreover have 3: \<open>xb \<in># D\<close>
      using xb_x1a R unfolding R_def st by auto
    ultimately show ?thesis
      unfolding xb
      by (rule f'_f)
  qed
  have loop_keep: \<open>(((x1c, x2b), x1d - 1, xa + 1, x1g), x1, remove1_mset xb x1a, x1f) \<in> R\<close> and
   loop_dont_keep: \<open>(((x1c - 1, x2b[xa := None]), x1d - 1, xa + 1, x1g),
           remove1_mset xb x1, remove1_mset xb x1a, x1f) \<in> R\<close>
    if
      R: \<open>(x, x') \<in> R\<close> and
      st:
        \<open>x2 = (x1a, x2a)\<close>
        \<open>x' = (x1, x2)\<close>
        \<open>x1b = (x1c, x2b)\<close>
        \<open>x2d = (x1e, x2e)\<close>
        \<open>x2c = (x1d, x2d)\<close>
        \<open>x = (x1b, x2c)\<close>
        \<open>x'a = (x1f, x2f)\<close>
        \<open>xc = (x1g, x2g)\<close> and
      xa_xb: \<open>(xa, xb) \<in> ?confl x2b x1e\<close> and
      xb_x1a: \<open>xb \<in> {x. x \<in># x1a}\<close> and
      F: \<open>(xc, x'a) \<in> Rstate \<times>\<^sub>f bool_rel\<close> and
      xa_length_xb: \<open>xa < length x2b\<close>
    for x x' x1 x2 x1a x2a x1b x1c x2b x2c x1d x2d x1e x2e xa xb xc x'a x1f
       x2f x1g x2g
  proof -
    have [simp]: \<open>(x1g, x1f) \<in> Rstate\<close>
      using F unfolding st by auto
    have
      x1c_x1[simp]: \<open>((x1c, x2b), x1) \<in> conflict_rel\<close> and
      [simp]: \<open>x1e \<le> length x2b\<close> and
      x1d_x1a: \<open>((x1d, replicate x1e None @ drop x1e x2b), x1a) \<in> conflict_rel\<close> and
      \<open>(x2e, x2a) \<in> Rstate\<close> and
      x1d_x1c: \<open>x1d \<le> x1c\<close> and
      incls: \<open>x1 \<subseteq># D\<close> \<open>x1a \<subseteq># x1\<close>
      using R unfolding R_def st
      by auto
    have
      xa_le_x2b: \<open>xa < length x2b\<close> and
      x1e_xa: \<open>x1e \<le> xa\<close> and
      x1e_xa_None: \<open>\<forall>k\<ge>x1e. k < xa \<longrightarrow> x2b ! k = None\<close> and
      xb: \<open>xb = (if the (x2b ! xa) then Pos xa else Neg xa)\<close> and
      no_none: \<open>x2b ! xa \<noteq> None\<close>
      using xa_xb by auto
    have 1: \<open>drop x1e x2b = take (xa - x1e) (drop x1e x2b) @ drop xa x2b\<close>
      by (rule drop_take_drop_drop) (use x1e_xa in auto)
    have 2: \<open>take (xa - x1e) (drop x1e x2b) = replicate (xa - x1e) None\<close>
    proof (cases \<open>0 < xa - x1e\<close>)
      case True
      show ?thesis
        apply (rule list_eq_replicate_iff_nempty[THEN iffD2])
        subgoal using True by auto
        subgoal using x1e_xa x1e_xa_None xa_le_x2b True
          apply (auto simp: in_set_take_conv_nth Bex_def)
          by (metis \<open>0 < xa - x1e\<close> \<open>x1e \<le> length x2b\<close> add.right_neutral nth_drop order_mono_setup.refl)
        done
    next
      case False
      then show ?thesis by auto
    qed

    have 3: \<open>replicate x1e None @ drop x1e x2b = replicate xa None @ drop xa x2b\<close>
      apply (subst 1)
      apply (subst 2)
      using x1e_xa by (auto simp: replicate_add[symmetric])
    have
      x1d: \<open>x1d = size x1a\<close> and
      map: \<open>mset_as_position (replicate x1e None @ drop x1e x2b) x1a\<close> and
      L_all_x2b: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length x2b\<close>
      using x1d_x1a unfolding conflict_rel_def by auto

    have 4: \<open>(replicate xa None @ drop xa x2b)[xa := None] = replicate (Suc xa) None @ drop (Suc xa) x2b\<close>
      apply (subst Cons_nth_drop_Suc[symmetric])
      subgoal by (rule xa_le_x2b)
      subgoal by (auto simp: list_update_append replicate_Suc_conv_snoc simp del: replicate_Suc)
      done
    have [simp]: \<open>x1a - {#Pos xa, Neg xa#} = remove1_mset xb x1a\<close>
      using mset_as_position_in_iff_nth[OF map, of \<open>Pos xa\<close>]
        mset_as_position_in_iff_nth[OF map, of \<open>Neg xa\<close>] xa_le_x2b no_none
      unfolding 3 4 xb
      by (auto simp: nth_append dest!: multi_member_split)

    have \<open>mset_as_position (replicate (Suc xa) None @ drop (Suc xa) x2b)
        (remove1_mset xb x1a)\<close>
      using mset_as_position_remove[OF map, of \<open>xa\<close>] xa_le_x2b
      by (auto simp del: replicate_Suc simp: 3 4)

    then have map':
      \<open>((x1d - Suc 0, replicate (Suc xa) None @ drop (Suc xa) x2b), remove1_mset xb x1a)
        \<in> conflict_rel\<close>
      using xb_x1a x1d L_all_x2b
      by (auto simp: size_remove1_mset_If conflict_rel_def simp del: replicate_Suc)
    show H: \<open>(((x1c, x2b), x1d - 1, xa + 1, x1g), x1, remove1_mset xb x1a, x1f) \<in> R\<close>
      using xa_xb x1d_x1c map' incls unfolding R_def
      by (auto intro: subset_mset.order.trans diff_subset_eq_self)

    have
      \<open>x1c = size x1\<close> and
      map: \<open>mset_as_position x2b x1\<close> and
      \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length x2b\<close>
      using x1c_x1 unfolding conflict_rel_def by auto
    have [simp]: \<open>x1 - {#Pos xa, Neg xa#} = remove1_mset xb x1\<close> \<open>xb \<in># x1\<close>
      using mset_as_position_in_iff_nth[OF map, of \<open>Pos xa\<close>]
        mset_as_position_in_iff_nth[OF map, of \<open>Neg xa\<close>] xa_le_x2b no_none
      unfolding 3 4 xb
      by (auto simp: nth_append dest!: multi_member_split)
    have \<open>mset_as_position (x2b[xa := None]) (remove1_mset xb x1)\<close>
      using mset_as_position_remove[OF map, of \<open>xa\<close>] xa_le_x2b
      by (auto simp del: replicate_Suc simp: 3 4)

    then have \<open>((x1c - Suc 0, x2b[xa := None]), remove1_mset xb x1) \<in> conflict_rel\<close>
      using x1c_x1 unfolding conflict_rel_def
      by (auto simp: size_remove1_mset_If)
    moreover have  \<open>x1d - Suc 0 \<le> x1c - Suc 0\<close>
      using diff_le_mono x1d_x1c by blast
    ultimately show \<open>(((x1c - 1, x2b[xa := None]), x1d - 1, xa + 1, x1g),
           remove1_mset xb x1, remove1_mset xb x1a, x1f) \<in> R\<close>
      using xa_le_x2b H incls unfolding R_def
      by (auto intro: subset_mset.order.trans diff_subset_eq_self mset_le_subtract)
  qed
  show ?thesis
    unfolding iterate_over_lookup_conflict_def iterate_over_conflict_def D' prod.case
    apply (refine_vcg  WHILEIT_refine[where R = R])
    subgoal by (rule init_args_ref)
    subgoal for s' s by (rule init_lo_inv)
    subgoal for st' st nxs n xs x2a m x2b j x2c E x2d E' s by (rule cond)
    subgoal by auto
    apply (rule confl_find_next_index_spec_le; assumption)
           apply (rule f'_f_ref; assumption)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: iterate_over_lookup_conflict_inv_def)
    subgoal by auto
    subgoal for x x' x1 x2 x1a x2a x1b x1c x2b x2c x1d x2d x1e x2e xa xb xc x'a x1f
       x2f x1g x2g
      by (rule loop_keep)
    subgoal for x x' x1 x2 x1a x2a x1b x1c x2b x2c x1d x2d x1e x2e xa xb xc x'a x1f
       x2f x1g x2g
      by (rule loop_dont_keep)
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d
      unfolding R_def by (cases x1b) auto
    done
qed

end


definition lit_redundant_rec_wl_lookup :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> conflict_rel \<Rightarrow>
     _ \<Rightarrow> _ \<Rightarrow>
      (_ \<times> _ \<times> bool) nres\<close>
where
  \<open>lit_redundant_rec_wl_lookup M NU D cach analysis =
      WHILE\<^sub>T\<^bsup>lit_redundant_rec_wl_inv M NU D\<^esup>
        (\<lambda>(cach, analyse, b). analyse \<noteq> [])
        (\<lambda>(cach, analyse, b). do {
            ASSERT(analyse \<noteq> []);
            ASSERT(fst (last analyse) < length NU);
            let C = NU ! fst (last analyse);
            ASSERT(length C > 0); (* \<ge> 2 ? *)
            let i = snd (last analyse);
            ASSERT(C!0 \<in> lits_of_l M);
            if i \<ge> length C
            then
               RETURN(cach (atm_of (C ! 0) := SEEN_REMOVABLE), butlast analyse, True)
            else do {
               let (L, analyse) = get_literal_and_remove_of_analyse_wl C analyse;
               ASSERT(-L \<in> lits_of_l M);
               if (get_level M L = zero_uint32_nat \<or> conflict_min_cach cach (atm_of L) = SEEN_REMOVABLE \<or> is_in_lookup_conflict D L)
               then RETURN (cach, analyse, False)
               else do {
                  C \<leftarrow> get_propagation_reason M L;
                  case C of
                    Some C \<Rightarrow> RETURN (cach, analyse @ [(C, 1)], False)
                  | None \<Rightarrow> do {
                      cach \<leftarrow> mark_failed_lits_wl analyse cach;
                      RETURN (cach, [], False)
                  }
              }
          }
        })
       (cach, analysis, False)\<close>

context isasat_input_ops
begin

lemma lit_redundant_rec_wl_lookup_lit_redundant_rec_wl:
  assumes D'_D: \<open>(D', D) \<in> conflict_rel\<close> and
    M: \<open>\<forall>a \<in> lits_of_l M. a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    \<open>M \<Turnstile>as CNot D\<close> and
    n_d: \<open>no_dup M\<close>
  shows
   \<open>lit_redundant_rec_wl_lookup M NU D' cach analysis \<le> \<Down> Id
      (lit_redundant_rec_wl M NU D cach analysis)\<close>
proof -
  have [simp]: \<open>is_in_lookup_conflict D' x \<longleftrightarrow> x \<in># D\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>) if \<open>-x \<in> lits_of_l M\<close> for x
  proof
    assume ?B
    then show ?A
      using D'_D mset_as_position_nth[of \<open>snd D'\<close> D x] M that
      unfolding conflict_rel_def
      by (auto simp: is_in_lookup_conflict_def split: option.splits)
  next
    assume ?A
    moreover have \<open>atm_of x < length (snd D')\<close>
      using M that D'_D
      unfolding conflict_rel_def
      by (cases D') (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    moreover have \<open>-x \<notin># D\<close>
      using \<open>M \<Turnstile>as CNot D\<close> n_d in_CNot_implies_uminus(2) no_dup_consistentD that by blast
    ultimately show ?B
      using D'_D mset_as_position_in_iff_nth[of \<open>snd D'\<close> D x] M that
        mset_as_position_in_iff_nth[of \<open>snd D'\<close> D \<open>-x\<close>]
      unfolding conflict_rel_def
      by (cases x) (auto simp: is_in_lookup_conflict_def split: option.splits)
  qed

  have [refine_vcg]: \<open>(a, b) \<in> Id \<Longrightarrow> (a, b) \<in> \<langle>Id\<rangle>option_rel\<close> for a b by auto
  have [refine_vcg]: \<open>get_propagation_reason M x
    \<le> \<Down> Id (get_propagation_reason M y)\<close> if \<open>x = y\<close> for x y
    unfolding that by auto
  have [refine_vcg]: \<open>mark_failed_lits_wl a b
    \<le> \<Down> Id
        (mark_failed_lits_wl a' b')\<close> if \<open>a = a'\<close> and \<open>b = b'\<close> for a a' b b'
    unfolding that by auto
  show ?thesis
    unfolding lit_redundant_rec_wl_lookup_def lit_redundant_rec_wl_def
    apply (refine_vcg)
    subgoal by auto
    subgoal by (auto simp: lit_redundant_rec_wl_inv_def)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: lit_redundant_rec_wl_inv_def elim!: neq_Nil_revE)
    subgoal by (auto simp: lit_redundant_rec_wl_inv_def elim!: neq_Nil_revE)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

abbreviation (in -)analyse_refinement_assn where
  \<open>analyse_refinement_assn \<equiv> arl_assn (nat_assn *a nat_assn)\<close>

end


context isasat_input_bounded
begin

sepref_thm sers
  is \<open>uncurry4 lit_redundant_rec_wl_lookup\<close>
  :: \<open>[\<lambda>((((M, NU), D), cach), analysis).
         (\<forall>a \<in> lits_of_l M. atm_of a \<in># \<A>\<^sub>i\<^sub>n) (* replace by the proper function on the trail *) \<and>
        (\<forall>a \<in> lits_of_l M. -a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l)
      ]\<^sub>a

      trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a conflict_rel_assn\<^sup>k *\<^sub>a
       cach_refinement_assn\<^sup>d *\<^sub>a analyse_refinement_assn\<^sup>d \<rightarrow>
      cach_refinement_assn *a analyse_refinement_assn *a bool_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim!] image_image[simp]
  unfolding lit_redundant_rec_wl_lookup_def
    conflict_min_cach_set_removable_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
  apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
           apply sepref_dbg_trans_step_keep
                      apply sepref_dbg_side_unfold apply (auto simp: )[]
  oops

end


end
