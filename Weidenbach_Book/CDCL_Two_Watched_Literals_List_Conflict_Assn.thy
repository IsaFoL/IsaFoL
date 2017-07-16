theory CDCL_Two_Watched_Literals_List_Conflict_Assn
  imports CDCL_Two_Watched_Literals_List_Watched_Domain
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

(*TODO Move*)
lemma (in -) is_pos_neg_not_is_pos: \<open>is_pos (- L) \<longleftrightarrow> \<not>is_pos L\<close>
  by (cases L) auto
(*End Move*)

lemma mset_as_position_in_iff_nth:
  \<open>mset_as_position xs P \<Longrightarrow> atm_of L < length xs \<Longrightarrow> L \<in># P \<longleftrightarrow> xs ! (atm_of L) = Some (is_pos L)\<close>
  by (induction rule: mset_as_position.induct)
    (auto simp: nth_list_update' atm_of_eq_atm_of is_pos_neg_not_is_pos
      dest: mset_as_position_atm_le_length)

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

context twl_array_code_ops
begin

type_synonym (in -) conflict_rel = "nat \<times> bool option list"

definition conflict_rel :: "(conflict_rel \<times> nat literal multiset) set" where
\<open>conflict_rel = {((n, xs), C). n = size C \<and> mset_as_position xs C \<and>
   (\<forall>L\<in>atms_of N\<^sub>1. L < length xs)}\<close>

lemma conflict_rel_empty_iff: \<open>((n, xs), C) \<in> conflict_rel \<Longrightarrow> n = 0 \<longleftrightarrow> C = {#}\<close>
  by (auto simp: conflict_rel_def)

lemma conflict_atm_le_length: \<open>((n, xs), C) \<in> conflict_rel \<Longrightarrow> L \<in> atms_of N\<^sub>1 \<Longrightarrow> L < length xs\<close>
  by (auto simp: conflict_rel_def)


lemma conflict_le_length:
  assumes
    c_rel: \<open>((n, xs), C) \<in> conflict_rel\<close> and
    L_N\<^sub>1: \<open>L \<in># N\<^sub>1\<close>
  shows \<open>atm_of L < length xs\<close>
proof -
  have
    size: \<open>n = size C\<close> and
    mset_pos: \<open>mset_as_position xs C\<close> and
    atms_le: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length xs\<close>
    using c_rel unfolding conflict_rel_def by blast+
  have \<open>atm_of L \<in> atms_of N\<^sub>1\<close>
    using L_N\<^sub>1 by (simp add: atms_of_def)
  then show ?thesis
    using atms_le by blast
qed

lemma conflict_rel_atm_in_iff:
  \<open>((n, xs), C) \<in> conflict_rel \<Longrightarrow> L \<in># N\<^sub>1 \<Longrightarrow> L \<in>#C \<longleftrightarrow> xs!(atm_of L) = Some (is_pos L)\<close>
  by (rule mset_as_position_in_iff_nth)
     (auto simp: conflict_rel_def atms_of_def)

type_synonym (in -) conflict_assn = "uint32 \<times> bool option array"

definition conflict_assn :: "nat clause \<Rightarrow> conflict_assn \<Rightarrow> assn" where
\<open>conflict_assn = hr_comp (uint32_nat_assn *assn array_assn (option_assn bool_assn)) conflict_rel\<close>

definition option_conflict_rel where
\<open>option_conflict_rel = {((b,(n,xs)), C). b = (C = None) \<and>
   (C = None \<longrightarrow> ((n,xs), {#}) \<in> conflict_rel) \<and>
   (C \<noteq> None \<longrightarrow> ((n,xs), the C) \<in> conflict_rel)}
   \<close>

lemma option_conflict_rel_conflict_rel_iff: \<open>((False, (n, xs)), Some C) \<in> option_conflict_rel \<longleftrightarrow>
   ((n, xs), C) \<in> conflict_rel\<close>
   unfolding option_conflict_rel_def by auto


type_synonym (in -) conflict_option_assn = "bool \<times> uint32 \<times> bool option array"

definition conflict_option_assn :: \<open>nat clause option \<Rightarrow> conflict_option_assn \<Rightarrow> assn\<close> where
\<open>conflict_option_assn = 
   hr_comp (bool_assn *assn uint32_nat_assn *assn array_assn (option_assn bool_assn)) 
     option_conflict_rel\<close>

end

end