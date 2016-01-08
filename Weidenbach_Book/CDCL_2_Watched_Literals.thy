theory CDCL_2_Watched_Literals
imports CDCL_FW (* Have to decide which import is the best *)
begin

text \<open>Only the 2-watched literals have to be verified here: the backtrack level and the trail can
  remain separate.\<close>

datatype 'v w_clause =
  W_Clause (watched: "'v clause") (not_watched: "'v clause")

type_synonym 'v two_wl_struct =
  "('v, nat, 'v clause) annoted_lits \<times> 'v w_clause multiset \<times> 'v w_clause multiset \<times> nat \<times>
   'v clause conflicting_clause \<times> ('v, nat, 'v clause) marked_lit set"
abbreviation trail :: "'v two_wl_struct \<Rightarrow> ('v, nat, 'v clause) annoted_lits" where
"trail \<equiv> \<lambda>(M, _). M"

abbreviation init_clss :: "'v two_wl_struct \<Rightarrow> 'v w_clause multiset" where
"init_clss \<equiv> \<lambda>(_,N, _). N"

abbreviation learned_clss :: "'v two_wl_struct \<Rightarrow> 'v w_clause multiset" where
"learned_clss \<equiv> \<lambda>(_,_, U, _). U"

abbreviation backtrack_lvl :: "'v two_wl_struct \<Rightarrow> nat" where
"backtrack_lvl \<equiv> \<lambda>(_,_, _,k, _). k"

abbreviation conflicting :: "'v two_wl_struct \<Rightarrow> 'v clause conflicting_clause" where
"conflicting \<equiv> \<lambda>(_,_, _,_, C, _). C"

abbreviation candidates :: "'v two_wl_struct \<Rightarrow> ('v, nat, 'v clause) marked_lit set" where
"candidates \<equiv> \<lambda>(_,_, _,_, _, Cs). Cs"

definition clauses where
"clauses S = init_clss S + learned_clss S"

locale structure_2_WL =
  fixes sel :: "'v multiset \<Rightarrow> 'v"
   assumes sel[simp, intro]: "\<And>S. S \<noteq> {#} \<Longrightarrow> sel S \<in># S"
begin

(* Stupid but very general... *)
function find_in_mset where
"find_in_mset P M =
  (if M = {#} then None
  else
    (let a = sel M in
    if P a then Some a else find_in_mset P (M - {#a#})))"
by auto
termination
  apply (relation "measure (size o snd)") by (simp_all add: size_Diff1_less)
declare find_in_mset.simps[simp del]

lemma find_in_mset_empty[simp]:
  "find_in_mset P {#} = None"
  by (simp add: find_in_mset.simps)

lemma find_in_mset_found[simp]:
  "M \<noteq> {#} \<Longrightarrow> P (sel M) \<Longrightarrow> find_in_mset P M = Some (sel M)"
  by (simp add: find_in_mset.simps)

lemma find_in_mset_not_found[simp]:
  "M \<noteq> {#} \<Longrightarrow> \<not>P (sel M) \<Longrightarrow> find_in_mset P M =  find_in_mset P (M - {#sel M#})"
  unfolding find_in_mset.simps[of P M] by simp

lemma "find_in_mset P M = None \<longleftrightarrow> (\<forall>m\<in>#M. \<not>P m)"
proof (induction "size M" arbitrary: M)
  case 0
  then show ?case by simp
next
  case (Suc n) note IH = this(1) and n = this(2)
  let ?a = "sel M"
  have [simp]: "M \<noteq> {#}"
    using n by auto
  then have "M = (M - {#?a#}) + {#?a#}"
    by (auto simp: ac_simps multiset_eq_iff)
  show ?case
    proof (cases "P ?a")
      case True
      then show ?thesis by auto
    next
      case False
      have "n = size (M - {#sel M#})"
        using n by (simp add: size_Diff_singleton_if)
      from IH[OF this] show ?thesis using False
        by (smt \<open>M \<noteq> {#}\<close> ball_msetE ball_msetI count_diff count_single diff_zero
          structure_2_WL.find_in_mset.simps structure_2_WL_axioms)
    qed
qed

lemma "find_in_mset P M = Some a \<Longrightarrow> a\<in>#M \<and> P a"
proof (induction "size M" arbitrary: M)
  case 0
  then show ?case by simp
next
  case (Suc n) note IH = this(1) and n = this(2) and H = this(3)
  let ?a = "sel M"
  have [simp]: "M \<noteq> {#}"
    using n by auto
  then have "M = (M - {#?a#}) + {#?a#}"
    by (auto simp: ac_simps multiset_eq_iff)
  show ?case
    proof (cases "P ?a")
      case True
      then show ?thesis using H by auto
    next
      case False
      have "n = size (M - {#sel M#})"
        using n by (simp add: size_Diff_singleton_if)
      from IH[OF this] show ?thesis using False H by auto
    qed
qed

fun one_is_true :: "'v w_clause \<Rightarrow> 'v two_wl_struct \<Rightarrow> bool"  where
"one_is_true (W_Clause w _) S = (\<exists>L\<in># w. L \<in> lits_of (trail S))"

fun one_is_false_and_candidate :: "'v w_clause \<Rightarrow> 'v two_wl_struct \<Rightarrow> bool" where
"one_is_false_and_candidate (W_Clause w uw) S =
  (\<exists>L\<in># w. \<exists>L' \<in># w - {#L#}.  -L \<in> lits_of (trail S) \<and> Propagated L' (w + uw) \<in> (candidates S))"

fun two_unassigned :: "'v w_clause \<Rightarrow> 'v two_wl_struct \<Rightarrow> bool" where
"two_unassigned (W_Clause w _) S \<longleftrightarrow> (\<forall>L \<in># w. undefined_lit L ((trail S)))"

text \<open>There are two watched literals except when there is no literal to watch.\<close>
fun less_than_two_watched :: "'v w_clause \<Rightarrow> 'v two_wl_struct \<Rightarrow> bool" where
"less_than_two_watched C S \<longleftrightarrow>
  (size (watched C) \<le> 2
    \<and> (size (watched C) \<le> 1 \<longrightarrow> not_watched C = {#}))"

definition watched_lits :: "'v two_wl_struct \<Rightarrow> bool"  where
"watched_lits S =
  (\<forall>C \<in># clauses S. less_than_two_watched C S
    \<and> (one_is_true C S \<or> two_unassigned C S \<or> less_than_two_watched C S))"

fun tl_trail :: "'v two_wl_struct  \<Rightarrow>  'v two_wl_struct " where
"tl_trail (M, S) = (tl M, S)"

lemma tl_trail:
  "watched_lits S \<Longrightarrow> watched_lits (tl_trail S)"
  unfolding watched_lits_def by (cases S) (auto simp: clauses_def)

end

end