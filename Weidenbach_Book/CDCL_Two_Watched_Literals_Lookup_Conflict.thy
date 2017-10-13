theory CDCL_Two_Watched_Literals_Lookup_Conflict
  imports CDCL_Two_Watched_Literals_Watch_List_Domain
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
    conflict_rel_size: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C \<Longrightarrow> size C \<le> upperN div 2\<close>
proof -
  have mset: \<open>mset_as_position xs C\<close> and \<open>n = size C\<close> and \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close>
    using c unfolding conflict_rel_def by fast+
  show \<open>\<not>tautology C\<close>
    using mset
    apply (induction rule: mset_as_position.induct)
    subgoal by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def)
    subgoal by (auto simp: tautology_add_mset)
    done
  have \<open>distinct_mset C\<close>
    using mset mset_as_position_distinct_mset by blast
  then show \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C \<Longrightarrow> size C \<le> upperN div 2\<close>
    using simple_clss_size_upper_div2[of \<open>C\<close>] \<open>\<not>tautology C\<close> by auto
qed

type_synonym (in -) conflict_assn = "uint32 \<times> bool option array"

definition conflict_assn :: "nat clause \<Rightarrow> conflict_assn \<Rightarrow> assn" where
\<open>conflict_assn = hr_comp (uint32_nat_assn *assn array_assn (option_assn bool_assn)) conflict_rel\<close>

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
 \<open>conflict_rel_assn \<equiv> (uint32_nat_assn *assn array_assn (option_assn bool_assn))\<close>

type_synonym (in -) conflict_option_rel = \<open>bool \<times>nat \<times> bool option list\<close>

abbreviation (in -)conflict_option_rel_assn :: \<open>conflict_option_rel \<Rightarrow> conflict_option_assn \<Rightarrow> assn\<close> where
 \<open>conflict_option_rel_assn \<equiv> (bool_assn *assn conflict_rel_assn)\<close>

definition conflict_option_assn
  :: \<open>nat clause option \<Rightarrow> conflict_option_assn \<Rightarrow> assn\<close>
where
  \<open>conflict_option_assn =
     hr_comp (bool_assn *assn uint32_nat_assn *assn array_assn (option_assn bool_assn))
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

definition size_conflict_extract :: \<open>_ \<Rightarrow> nat\<close> where
  \<open>size_conflict_extract = (\<lambda>((_, n, _), _). n)\<close>

definition size_conflict_wl_int :: \<open>_ \<Rightarrow> nat\<close> where
  \<open>size_conflict_wl_int = (\<lambda>(M, N, U, D, _, _, _, _). size_conflict_extract D)\<close>

lemma size_conflict_extract[sepref_fr_rules]:
   \<open>(return o (\<lambda>((_, n, _), _). n), RETURN o size_conflict_extract) \<in>
   (((bool_assn *assn conflict_rel_assn) *assn
         option_assn (unat_lit_assn *assn uint32_nat_assn)))\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding size_conflict_extract_def
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

end