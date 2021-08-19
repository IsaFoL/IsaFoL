(* Title:        Preliminaries of the Splitting Framework
 * Author:       Sophie Tourret <stourret at mpi-inf.mpg.de>, 2020 *)

theory Preliminaries
  imports Saturation_Framework.Calculus 
    "HOL-Library.Library"
  (* Finite_Set *)
begin
  
  (* formalizing negated formulas uncovered a mistake in the corresponding paper-definition
  (sect. 2.1) *)
datatype 'a neg = Pos "'a" | Neg "'a neg" (* ("\<sim>_" 55) (*| Pos (nval_of: "'a neg") *) term "\<sim>F" *)

fun to_V :: "'a neg \<Rightarrow> 'a" where
  "to_V (Pos C) = C" |
  "to_V (Neg C) = to_V C"

lemma tov_set[simp]: \<open>{to_V C |C. to_V C \<in> A} = A\<close>
  by (smt (verit, del_insts) mem_Collect_eq subsetI subset_antisym to_V.simps(1))

fun is_Pos :: "'a neg \<Rightarrow> bool" where
  "is_Pos (Pos C) = True" |
  "is_Pos (Neg C) = (\<not>(is_Pos C))"
  
lemma pos_neg_union: \<open>{P C |C. Q C \<and> is_Pos C} \<union> {P C |C. Q C \<and> \<not> is_Pos C} = {P C |C. Q C}\<close>
  by blast

fun is_in :: "'a neg \<Rightarrow> 'a neg set \<Rightarrow> bool" (infix "\<in>\<^sub>v" 90) where
  \<open>(Pos C) \<in>\<^sub>v J = (\<exists>v\<in>J. is_Pos v \<and> to_V v = C)\<close> |
  \<open>(Neg C) \<in>\<^sub>v J = (\<exists>v\<in>J. (is_Pos v = is_Pos (Neg C)) \<and> to_V v = to_V C)\<close>

locale consequence_relation =
  fixes
    bot :: "'f" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  assumes
    bot_entails_empty: "{bot} \<Turnstile> {}" and
    entails_reflexive: "{C} \<Turnstile> {C}" and
    entails_subsets: "M \<subseteq> N \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> M \<Turnstile> P \<Longrightarrow> N \<Turnstile> Q" and
    entails_supsets: "(\<forall>M' N'. (M' \<supseteq> M \<and> N' \<supseteq> N \<and> M' \<union> N' = UNIV) \<longrightarrow> M' \<Turnstile> N') \<Longrightarrow> M \<Turnstile> N"
    (* the version of D4 below was relaxed to fix lemma 6, which was found broken due to the forma *)
    (* entails_each: "M \<Turnstile> P \<Longrightarrow> \<forall>C\<in>M. N \<Turnstile> Q \<union> {C} \<Longrightarrow> \<forall>D\<in>P. N \<union> {D} \<Turnstile> Q \<Longrightarrow> N \<Turnstile> Q" *)
    (* this was an earlier version of entails_each: "M \<Turnstile> N \<Longrightarrow> (\<forall>D\<in>N. M \<union> {D} \<Turnstile> P) \<Longrightarrow> M \<Turnstile> P"
    it was detected to be unsufficient thanks to the forma*)
begin

lemma entails_each: "M \<Turnstile> P \<Longrightarrow> \<forall>C\<in>M. N \<Turnstile> Q \<union> {C} \<Longrightarrow> \<forall>D\<in>P. N \<union> {D} \<Turnstile> Q \<Longrightarrow> N \<Turnstile> Q" 
proof -
  fix M P N Q
  assume m_entails_p: \<open>M \<Turnstile> P\<close>
    and n_to_q_m: \<open>\<forall>C\<in>M. N \<Turnstile> Q \<union> {C}\<close>
    and n_p_to_q: \<open>\<forall>D\<in>P. N \<union> {D} \<Turnstile> Q\<close>
  have \<open>\<forall>M' N'. (M' \<supseteq> N \<and> N' \<supseteq> Q \<and> M' \<union> N' = UNIV) \<longrightarrow> M' \<Turnstile> N'\<close>
  proof clarsimp
    fix M' N'
    assume n_sub_mp: \<open>M' \<supseteq> N\<close> and
      q_sub_np: \<open>N' \<supseteq> Q\<close> and
      union_univ: \<open>M' \<union> N' = UNIV\<close>
    consider (a) "\<not> (M' \<inter> P = {})" | (b) "\<not> (N' \<inter> M = {})" | (c) "P \<subseteq> N' \<and> M \<subseteq> M'"
      using union_univ by auto 
    then show \<open>M' \<Turnstile> N'\<close>
    proof cases
      case a
      assume \<open>M' \<inter> P \<noteq> {}\<close>
      then obtain D where d_in: \<open>D \<in> M' \<inter> P\<close> by auto
      then have \<open>N \<union> {D} \<subseteq> M'\<close> using n_sub_mp by auto
      moreover have \<open>N \<union> {D} \<Turnstile> Q\<close> using n_p_to_q d_in by blast
      ultimately show ?thesis
        using entails_subsets[OF _ q_sub_np] by blast
    next
      case b
      assume \<open>N' \<inter> M \<noteq> {}\<close>
      then obtain C where c_in: \<open>C \<in> M \<inter> N'\<close> by auto
      then have \<open>Q \<union> {C} \<subseteq> N'\<close> using q_sub_np by auto
      moreover have \<open>N \<Turnstile> Q \<union> {C}\<close> using n_to_q_m c_in by blast
      ultimately show ?thesis
        using entails_subsets[OF n_sub_mp] by blast
    next
      case c
      then show ?thesis
        using entails_subsets[OF _ _ m_entails_p] by simp
    qed      
  qed
  then show \<open>N \<Turnstile> Q\<close>
    using entails_supsets by simp
qed


lemma entails_bot_to_entails_empty: \<open>{} \<Turnstile> {bot} \<Longrightarrow> {} \<Turnstile> {}\<close>
  using entails_reflexive[of bot] entails_each[of "{}" "{bot}" "{}" "{}"] bot_entails_empty
  by auto

abbreviation equi_entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" where
  "equi_entails M N \<equiv> (M \<Turnstile> N \<and> N \<Turnstile> M)"

lemma entails_cond_reflexive: \<open>N \<noteq> {} \<Longrightarrow> N \<Turnstile> N\<close>
  using entails_reflexive entails_subsets by (meson bot.extremum from_nat_into insert_subset)
    
  (* This lemma shows that an entailment such that {} \<Turnstile> {} is useless, it may or may not help better
  understand what this entailment is depending on who you ask ^_^' *)
lemma entails_empty_reflexive_dangerous: \<open>{} \<Turnstile> {} \<Longrightarrow> M \<Turnstile> N\<close>
  using entails_subsets[of "{}" M "{}" N] by simp

definition entails_conjunctive :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>\<inter>" 50) where
  "M \<Turnstile>\<inter> N \<equiv> \<forall>C\<in>N. M \<Turnstile> {C}"

sublocale Calculus.consequence_relation "{bot}" "(\<Turnstile>\<inter>)"
proof
  show "{bot} \<noteq> {}" by simp
next
  fix B N
  assume b_in: "B \<in> {bot}"
  then have b_is: "B = bot" by simp
  show "{B} \<Turnstile>\<inter> N"
    unfolding entails_conjunctive_def
    using entails_subsets[of "{B}" "{B}" "{}"] b_is bot_entails_empty by blast
next
  fix M N
  assume m_subs: "(M :: 'f set) \<subseteq> N"
  show \<open>N \<Turnstile>\<inter> M\<close> unfolding entails_conjunctive_def
  proof
    fix C
    assume "C \<in> M"
    then have c_subs: \<open>{C} \<subseteq> N\<close> using m_subs by fast
    show \<open>N \<Turnstile> {C}\<close> using entails_subsets[OF c_subs _ entails_reflexive[of C]] by simp 
  qed
next
  fix M N
  assume \<open>\<forall>C\<in>M. N \<Turnstile>\<inter> {C}\<close>
  then show \<open>N \<Turnstile>\<inter> M\<close>
    unfolding entails_conjunctive_def by blast
next
  fix M N P
  assume
    trans1: \<open>M \<Turnstile>\<inter> N\<close> and
    trans2: \<open>N \<Turnstile>\<inter> P\<close>
  show \<open>M \<Turnstile>\<inter> P\<close> unfolding entails_conjunctive_def
  proof
    fix C
    assume \<open>C \<in> P\<close>
    then have n_to_c: \<open>N \<Turnstile> {C}\<close> using trans2 unfolding entails_conjunctive_def by simp
    have "M \<union> {C} \<Turnstile> {C}"
      using entails_subsets[OF _ _ entails_reflexive[of C], of "M \<union> {C}" "{C}"] by fast
    then have m_c_to_c: \<open>\<forall>D\<in>{C}. M \<union> {D} \<Turnstile> {C}\<close> by blast
    have m_to_c_n: "\<forall>D\<in>N. M \<Turnstile> {C} \<union> {D}"
      using trans1 entails_subsets[of M M] unfolding entails_conjunctive_def by blast 
    show \<open>M \<Turnstile> {C}\<close>
      using entails_each[OF n_to_c m_to_c_n m_c_to_c] unfolding entails_conjunctive_def .
  qed
qed

definition entails_neg :: "'f neg set \<Rightarrow> 'f neg set \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<sim>" 50) where
  "entails_neg M N \<equiv> {to_V C |C. C \<in> M \<and> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<Turnstile>
  {to_V C |C. C \<in> N \<and> is_Pos C} \<union> {to_V C |C. C \<in> M \<and> \<not> is_Pos C} "

definition all_ext :: "'f neg set \<Rightarrow> 'f neg set" where
  "all_ext M = (\<Union>C\<in>M. {D. to_V D = to_V C \<and> is_Pos D = is_Pos C})" 

lemma self_in_all_ext: \<open>M \<subseteq> all_ext M\<close>
  unfolding all_ext_def by auto 

lemma rm_all_ext: \<open>{to_V C |C. C \<in> all_ext M \<and> is_Pos C} = {to_V C |C. C \<in> M \<and> is_Pos C}\<close>
  unfolding all_ext_def by blast 

lemma rm_all_ext_neg: \<open>{to_V C |C. C \<in> all_ext M \<and> \<not> is_Pos C} = {to_V C |C. C \<in> M \<and> \<not> is_Pos C}\<close>
  unfolding all_ext_def by blast 

definition all_ext_complement :: "'f neg set \<Rightarrow> 'f neg set" where
  "all_ext_complement M = (\<Union>C\<in>M. {D. to_V D = to_V C \<and> is_Pos D \<noteq> is_Pos C})" 


lemma rm_all_ext_comp: \<open>{to_V C |C. C \<in> all_ext_complement M \<and> is_Pos C} =
  {to_V C |C. C \<in> M \<and> \<not> is_Pos C}\<close>
proof (intro equalityI subsetI)
  fix x
  assume \<open>x \<in> {to_V C |C. C \<in> all_ext_complement M \<and> is_Pos C}\<close>
  then obtain C where x_is: \<open>to_V C = x\<close> and c_in: \<open>C \<in> all_ext_complement M\<close> and c_pos: \<open>is_Pos C\<close>
    by blast 
  obtain D where tov_eq: \<open>to_V D = to_V C\<close> and d_neg: \<open>\<not> is_Pos D\<close> and d_in: \<open>D \<in> M\<close>
    using c_in c_pos unfolding all_ext_complement_def
    by auto
  then show \<open>x \<in> {to_V C |C. C \<in> M \<and> \<not> is_Pos C}\<close>
    using x_is by auto 
next
  fix x
  assume \<open>x \<in> {to_V C |C. C \<in> M \<and> \<not> is_Pos C}\<close>
  then obtain C where \<open>x = to_V C\<close> and \<open>C \<in> M\<close> and \<open>\<not> is_Pos C\<close>
    by blast 
  then have \<open>Pos x \<in> all_ext_complement M\<close>
    unfolding all_ext_complement_def by auto 
  then show \<open>x \<in> {to_V C |C. C \<in> all_ext_complement M \<and> is_Pos C}\<close>
    by force 
qed

lemma rm_all_ext_comp_neg: \<open>{to_V C |C. C \<in> all_ext_complement M \<and> \<not> is_Pos C} =
  {to_V C |C. C \<in> M \<and> is_Pos C}\<close>
proof (intro equalityI subsetI)
  fix x
  assume \<open>x \<in> {to_V C |C. C \<in> all_ext_complement M \<and> \<not> is_Pos C}\<close>
  then obtain C where x_is: \<open>to_V C = x\<close> and c_in: \<open>C \<in> all_ext_complement M\<close>
    and c_pos: \<open>\<not> is_Pos C\<close>
    by blast 
  obtain D where tov_eq: \<open>to_V D = to_V C\<close> and d_neg: \<open>is_Pos D\<close> and d_in: \<open>D \<in> M\<close>
    using c_in c_pos unfolding all_ext_complement_def
    by auto
  then show \<open>x \<in> {to_V C |C. C \<in> M \<and> is_Pos C}\<close>
    using x_is by auto 
next
  fix x
  assume \<open>x \<in> {to_V C |C. C \<in> M \<and> is_Pos C}\<close>
  then obtain C where \<open>x = to_V C\<close> and \<open>C \<in> M\<close> and \<open>is_Pos C\<close>
    by blast 
  then have \<open>Neg (Pos x) \<in> all_ext_complement M\<close>
    unfolding all_ext_complement_def by auto 
  then show \<open>x \<in> {to_V C |C. C \<in> all_ext_complement M \<and> \<not> is_Pos C}\<close>
    by force 
qed
  
lemma all_ext_and_comp: \<open>all_ext M \<union> all_ext_complement M = {C. to_V C \<in> to_V ` M}\<close>
  unfolding all_ext_def all_ext_complement_def by auto 

lemma ext_cons_rel: \<open>consequence_relation (Pos bot) entails_neg\<close>
proof
  show "entails_neg {Pos bot} {}"
    unfolding entails_neg_def using bot_entails_empty by simp
next
  fix C
  show \<open>entails_neg {C} {C}\<close>
    unfolding entails_neg_def using entails_cond_reflexive by auto
next
  fix M N P Q
  assume
    subs1: "M \<subseteq> N" and
    subs2: "P \<subseteq> Q" and
    entails1: "entails_neg M P"
  have union_subs1: \<open>{to_V C |C. C \<in> M \<and> is_Pos C} \<union> {to_V C |C. C \<in> P \<and> \<not> is_Pos C} \<subseteq>
    {to_V C |C. C \<in> N \<and> is_Pos C} \<union> {to_V C |C. C \<in> Q \<and> \<not> is_Pos C}\<close>
    using subs1 subs2 by auto
  have union_subs2: \<open>{to_V C |C. C \<in> P \<and> is_Pos C} \<union> {to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<subseteq>
    {to_V C |C. C \<in> Q \<and> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> \<not> is_Pos C}\<close>
    using subs1 subs2 by auto
  have union_entails1: "{to_V C |C. C \<in> M \<and> is_Pos C} \<union> {to_V C |C. C \<in> P \<and> \<not> is_Pos C} \<Turnstile>
    {to_V C |C. C \<in> P \<and> is_Pos C} \<union> {to_V C |C. C \<in> M \<and> \<not> is_Pos C}"
    using entails1 unfolding entails_neg_def .
  show \<open>entails_neg N Q\<close>
    using entails_subsets[OF union_subs1 union_subs2 union_entails1] unfolding entails_neg_def .
next
  fix M N
  assume all_supsets_entails: \<open>\<forall>M' N'. M \<subseteq> M' \<and> N \<subseteq> N' \<and> M' \<union> N' = UNIV \<longrightarrow> M' \<Turnstile>\<^sub>\<sim> N'\<close>
  have \<open>\<forall>M' N'. {to_V C |C. C \<in> M \<and> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<subseteq> M' \<and>
    {to_V C |C. C \<in> N \<and> is_Pos C} \<union> {to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<subseteq> N' \<and> M' \<union> N' = UNIV \<longrightarrow>
    M' \<Turnstile> N'\<close>
  proof clarsimp
    fix M' N'
    assume m_pos_subs: \<open>{to_V C |C. C \<in> M \<and> is_Pos C} \<subseteq> M'\<close> and
      n_neg_subs: \<open>{to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<subseteq> M' \<close> and
      n_pos_subs: \<open>{to_V C |C. C \<in> N \<and> is_Pos C} \<subseteq> N'\<close> and
      m_neg_subs: \<open>{to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<subseteq> N'\<close> and
      union_univ: \<open>M' \<union> N' = UNIV\<close>
    show \<open>M' \<Turnstile> N'\<close>
    proof (cases "M' \<inter> N' = {}")
      case True
      assume inter_empty: \<open>M' \<inter> N' = {}\<close>
    define X where \<open>X = all_ext M \<union> all_ext_complement N \<union>
      {C. is_Pos C \<and> to_V C \<in> M' - (to_V ` (M \<union> N))} \<union>
      {C. \<not> is_Pos C \<and> to_V C \<in> N' - (to_V ` (M \<union> N))}\<close>
    define Y where \<open>Y = all_ext N \<union> all_ext_complement M \<union>
      {C. is_Pos C \<and> to_V C \<in> N' - (to_V ` (M \<union> N))} \<union>
      {C. \<not> is_Pos C \<and> to_V C \<in> M' - (to_V ` (M \<union> N))}\<close>
    have \<open>UNIV = X \<union> Y\<close> unfolding X_def Y_def 
    proof (intro UNIV_eq_I)
      fix x
      consider (a) "x \<in> {C. to_V C \<in> to_V ` M}" | (b) "x \<in> {C. to_V C \<in> to_V ` N}" |
        (c) "x \<in> {C. to_V C \<in> (M' \<union> N' - to_V ` (M \<union> N))}"
        using union_univ by blast 
      then show \<open>x \<in> all_ext M \<union> all_ext_complement N \<union>
        {C. is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<union>
        {C. \<not> is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<union>
        (all_ext N \<union> all_ext_complement M \<union> {C. is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<union>
        {C. \<not> is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)})\<close>
      proof cases
        case a
        have \<open>x \<in> all_ext M \<union> all_ext_complement M\<close>
          using all_ext_and_comp[of M] a by simp
        then show ?thesis by auto 
      next
        case b
        have \<open>x \<in> all_ext N \<union> all_ext_complement N\<close>
          using all_ext_and_comp[of N] b by simp
        then show ?thesis by auto 
      next
        case c
        then show ?thesis by fast 
      qed
    qed
    moreover have \<open>M \<subseteq> X\<close> 
      unfolding X_def using self_in_all_ext[of M] by auto 
    moreover have \<open>N \<subseteq> Y\<close>
      unfolding Y_def  using self_in_all_ext[of N] by auto
    ultimately have x_entails_neg_y: \<open>X \<Turnstile>\<^sub>\<sim> Y\<close>
      using all_supsets_entails by auto
    show \<open>M' \<Turnstile> N'\<close>
    proof -
      have \<open>{to_V C |C. C \<in> {C. is_Pos C \<and> to_V C \<in> K - to_V ` (M \<union> N)} \<and> is_Pos C} =
        K - to_V ` (M \<union> N)\<close> for K
      proof (intro equalityI subsetI)
        fix x
        assume \<open>x \<in> {to_V C |C. C \<in> {C. is_Pos C \<and> to_V C \<in> K - to_V ` (M \<union> N)} \<and> is_Pos C}\<close>
        then show \<open>x \<in> K - to_V ` (M \<union> N)\<close>
          by fast 
      next
        fix x
        assume \<open>x \<in> K - to_V ` (M \<union> N)\<close>
        then have \<open>Pos x \<in> {C. is_Pos C \<and> to_V C \<in> K - to_V ` (M \<union> N)}\<close>
          by simp
        then show \<open>x \<in> {to_V C |C. C \<in> {C. is_Pos C \<and> to_V C \<in> K - to_V ` (M \<union> N)} \<and> is_Pos C}\<close>
          by (metis (mono_tags, lifting) mem_Collect_eq to_V.simps(1))
      qed
      have
        \<open>{to_V C |C. C \<in> {C. \<not> is_Pos C \<and> to_V C \<in> K - to_V ` (M \<union> N)} \<and> is_Pos C} = {}\<close> for K
        by blast 
      have \<open>{to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<inter> M' = {}\<close>
        using m_neg_subs inter_empty by auto 
      have \<open>{to_V C |C. C \<in> N \<and> is_Pos C} \<inter> M' = {}\<close>
        using n_pos_subs inter_empty by auto 

      have \<open>{to_V C |C. C \<in> X \<and> is_Pos C} \<union> {to_V C |C. C \<in> Y \<and> \<not> is_Pos C} =
        {to_V C |C. C \<in> M \<and> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<union> (M' - to_V ` (M \<union> N))\<close>
        unfolding X_def Y_def
      proof -
        have \<open>{to_V C |C. C \<in> all_ext M \<union> all_ext_complement N \<union>
          {C. is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<union>
          {C. \<not> is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext N \<union> all_ext_complement M \<union>
          {C. is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<union>
          {C. \<not> is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<and> \<not> is_Pos C} =
          {to_V C |C. C \<in> all_ext M \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext_complement N \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. \<not> is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext N \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext_complement M \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. \<not> is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<and> \<not> is_Pos C}\<close>
          by auto
        also have \<open>{to_V C |C. C \<in> all_ext M \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext_complement N \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. \<not> is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext N \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext_complement M \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. \<not> is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<and> \<not> is_Pos C} =
          {to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> M \<and> is_Pos C} \<union>
          {to_V C |C. to_V C \<in> M' - to_V ` (M \<union> N) \<and> is_Pos C} \<union>
          {to_V C |C. to_V C \<in> M' - to_V ` (M \<union> N) \<and> \<not> is_Pos C}\<close>
          using rm_all_ext[of M] rm_all_ext_neg[of N] rm_all_ext_comp[of N]
            rm_all_ext_comp_neg[of M] by auto 
        also have \<open>{to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> M \<and> is_Pos C} \<union>
          {to_V C |C. to_V C \<in> M' - to_V ` (M \<union> N) \<and> is_Pos C} \<union>
          {to_V C |C. to_V C \<in> M' - to_V ` (M \<union> N) \<and> \<not> is_Pos C} =
          {to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> M \<and> is_Pos C} \<union>
          {to_V C |C. to_V C \<in> (M' - to_V ` (M \<union> N))}\<close>
          by fast 
        also have \<open>{to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> M \<and> is_Pos C} \<union>
          {to_V C |C. to_V C \<in> (M' - to_V ` (M \<union> N))} =
          {to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> M \<and> is_Pos C} \<union>
          (M' - to_V ` (M \<union> N))\<close> 
          by (metis tov_set) 
        finally
        show \<open>{to_V C |C. C \<in> all_ext M \<union> all_ext_complement N \<union>
          {C. is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<union>
          {C. \<not> is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext N \<union> all_ext_complement M \<union>
          {C. is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<union>
          {C. \<not> is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<and> \<not> is_Pos C} =
          {to_V C |C. C \<in> M \<and> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<union> (M' - to_V ` (M \<union> N))\<close>
          by auto
      qed
      also have \<open>{to_V C |C. C \<in> M \<and> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> \<not> is_Pos C}
        \<union> (M' - to_V ` (M \<union> N)) = M'\<close>
      proof (intro equalityI subsetI)
        fix x
        assume \<open>x \<in> {to_V C |C. C \<in> M \<and> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<union>
           (M' - to_V ` (M \<union> N))\<close>
        then show \<open>x \<in> M'\<close>
          using m_pos_subs n_neg_subs by auto 
      next
        fix x
        assume x_in: \<open>x \<in> M'\<close>
        have x_from_m: \<open> x \<in> to_V ` M \<Longrightarrow> x \<in> {to_V C |C. C \<in> M \<and> is_Pos C}\<close>
        proof -
          assume \<open>x \<in> to_V ` M\<close>
          then obtain C where c_in: \<open>C \<in> M\<close> and x_is: \<open>to_V C = x\<close> by blast
          have \<open>is_Pos C\<close>
          proof (rule ccontr)
            assume \<open>\<not> is_Pos C\<close>
            then have \<open>x \<in> {to_V C |C. C \<in> M \<and> \<not> is_Pos C}\<close>
              using c_in x_is by auto 
            then show \<open>False\<close>
              using x_in inter_empty m_neg_subs by blast 
          qed
          then show \<open>x \<in> {to_V C |C. C \<in> M \<and> is_Pos C}\<close>
            using c_in x_is by auto 
        qed
        have x_from_n: \<open> x \<in> to_V ` N \<Longrightarrow> x \<in> {to_V C |C. C \<in> N \<and> \<not> is_Pos C}\<close>
        proof - 
          assume \<open>x \<in> to_V ` N\<close>
          then obtain C where c_in: \<open>C \<in> N\<close> and x_is: \<open>to_V C = x\<close> by blast
          have \<open>\<not> is_Pos C\<close>
          proof (rule ccontr)
            assume \<open>\<not> \<not> is_Pos C\<close>
            then have \<open>x \<in> {to_V C |C. C \<in> N \<and> is_Pos C}\<close>
              using c_in x_is by auto 
            then show \<open>False\<close>
              using x_in inter_empty n_pos_subs by blast 
          qed
          then show \<open>x \<in> {to_V C |C. C \<in> N \<and> \<not> is_Pos C}\<close>
            using c_in x_is by auto
        qed
        consider (a) "x \<in> M' - to_V ` (M \<union> N)" | (b) "x \<in> to_V ` M" | (c) "x \<in> to_V ` N"
          using x_in by blast 
        then show \<open>x \<in> {to_V C |C. C \<in> M \<and> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<union>
          (M' - to_V ` (M \<union> N))\<close>
          using x_from_m x_from_n by auto
      qed
      finally have xy_to_mp: \<open>{to_V C |C. C \<in> X \<and> is_Pos C} \<union> {to_V C |C. C \<in> Y \<and> \<not> is_Pos C} = M'\<close> .
        
      have \<open>{to_V C |C. C \<in> X \<and> \<not> is_Pos C} \<union> {to_V C |C. C \<in> Y \<and> is_Pos C} =
        {to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> is_Pos C} \<union> (N' - to_V ` (M \<union> N))\<close>
        unfolding X_def Y_def
      proof -
        have \<open>{to_V C |C. C \<in> all_ext M \<union> all_ext_complement N \<union>
          {C. is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<union>
          {C. \<not> is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext N \<union> all_ext_complement M \<union>
          {C. is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<union>
          {C. \<not> is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<and> is_Pos C} =
          {to_V C |C. C \<in> all_ext M \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext_complement N \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. \<not> is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext N \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext_complement M \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. \<not> is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<and> is_Pos C}\<close>
          by auto
        also have \<open>{to_V C |C. C \<in> all_ext M \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext_complement N \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. \<not> is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext N \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext_complement M \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> {C. \<not> is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<and> is_Pos C} =
          {to_V C |C. C \<in> N \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<union>
          {to_V C |C. to_V C \<in> N' - to_V ` (M \<union> N) \<and> is_Pos C} \<union>
          {to_V C |C. to_V C \<in> N' - to_V ` (M \<union> N) \<and> \<not> is_Pos C}\<close>
          using rm_all_ext[of N] rm_all_ext_neg[of M] rm_all_ext_comp[of M]
            rm_all_ext_comp_neg[of N] by auto 
        also have \<open>{to_V C |C. C \<in> N \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<union>
          {to_V C |C. to_V C \<in> N' - to_V ` (M \<union> N) \<and> is_Pos C} \<union>
          {to_V C |C. to_V C \<in> N' - to_V ` (M \<union> N) \<and> \<not> is_Pos C} =
          {to_V C |C. C \<in> N \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<union>
          {to_V C |C. to_V C \<in> (N' - to_V ` (M \<union> N))}\<close>
          by fast 
        also have \<open>{to_V C |C. C \<in> N \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<union>
          {to_V C |C. to_V C \<in> (N' - to_V ` (M \<union> N))} =
          {to_V C |C. C \<in> N \<and> is_Pos C} \<union>
          {to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<union>
          (N' - to_V ` (M \<union> N))\<close> 
          by (metis tov_set) 
        finally
        show \<open>{to_V C |C. C \<in> all_ext M \<union> all_ext_complement N \<union>
          {C. is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<union>
          {C. \<not> is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<and> \<not> is_Pos C} \<union>
          {to_V C |C. C \<in> all_ext N \<union> all_ext_complement M \<union>
          {C. is_Pos C \<and> to_V C \<in> N' - to_V ` (M \<union> N)} \<union>
          {C. \<not> is_Pos C \<and> to_V C \<in> M' - to_V ` (M \<union> N)} \<and> is_Pos C} =
          {to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> is_Pos C} \<union> (N' - to_V ` (M \<union> N))\<close>
          by auto
      qed
      also have \<open>{to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> is_Pos C}
        \<union> (N' - to_V ` (M \<union> N)) = N'\<close>
      proof (intro equalityI subsetI)
        fix x
        assume \<open>x \<in> {to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> is_Pos C} \<union>
           (N' - to_V ` (M \<union> N))\<close>
        then show \<open>x \<in> N'\<close>
          using n_pos_subs m_neg_subs by auto 
      next
        fix x
        assume x_in: \<open>x \<in> N'\<close>
        have x_from_m: \<open> x \<in> to_V ` M \<Longrightarrow> x \<in> {to_V C |C. C \<in> M \<and> \<not> is_Pos C}\<close>
        proof -
          assume \<open>x \<in> to_V ` M\<close>
          then obtain C where c_in: \<open>C \<in> M\<close> and x_is: \<open>to_V C = x\<close> by blast
          have \<open>\<not> is_Pos C\<close>
          proof (rule ccontr)
            assume \<open>\<not> \<not> is_Pos C\<close>
            then have \<open>x \<in> {to_V C |C. C \<in> M \<and> is_Pos C}\<close>
              using c_in x_is by auto 
            then show \<open>False\<close>
              using x_in inter_empty m_pos_subs by blast 
          qed
          then show \<open>x \<in> {to_V C |C. C \<in> M \<and> \<not> is_Pos C}\<close>
            using c_in x_is by auto 
        qed
        have x_from_n: \<open> x \<in> to_V ` N \<Longrightarrow> x \<in> {to_V C |C. C \<in> N \<and> is_Pos C}\<close>
        proof - 
          assume \<open>x \<in> to_V ` N\<close>
          then obtain C where c_in: \<open>C \<in> N\<close> and x_is: \<open>to_V C = x\<close> by blast
          have \<open>is_Pos C\<close>
          proof (rule ccontr)
            assume \<open>\<not> is_Pos C\<close>
            then have \<open>x \<in> {to_V C |C. C \<in> N \<and> \<not> is_Pos C}\<close>
              using c_in x_is by auto 
            then show \<open>False\<close>
              using x_in inter_empty n_neg_subs by blast 
          qed
          then show \<open>x \<in> {to_V C |C. C \<in> N \<and> is_Pos C}\<close>
            using c_in x_is by auto
        qed
        consider (a) "x \<in> N' - to_V ` (M \<union> N)" | (b) "x \<in> to_V ` M" | (c) "x \<in> to_V ` N"
          using x_in by blast 
        then show \<open>x \<in> {to_V C |C. C \<in> M \<and> \<not> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> is_Pos C} \<union>
          (N' - to_V ` (M \<union> N))\<close>
          using x_from_m x_from_n by auto
      qed
      finally have xy_to_np: \<open>{to_V C |C. C \<in> X \<and> \<not> is_Pos C} \<union> {to_V C |C. C \<in> Y \<and> is_Pos C} = N'\<close> .

      show \<open>M' \<Turnstile> N'\<close> 
        using xy_to_mp xy_to_np x_entails_neg_y unfolding entails_neg_def
        by (smt (z3) inf_sup_aci(5))
    qed
  next
    case False
    assume inter_not_empty: \<open>M' \<inter> N' \<noteq> {}\<close>
    then obtain C where \<open>C \<in> M' \<inter> N'\<close> by blast 
    then show \<open>M' \<Turnstile> N'\<close> using entails_reflexive entails_subsets
      by (meson Int_lower1 Int_lower2 entails_cond_reflexive inter_not_empty)
    qed
  qed
  then show \<open>M \<Turnstile>\<^sub>\<sim> N\<close>
    unfolding entails_neg_def
    using entails_supsets[of "{to_V C |C. C \<in> M \<and> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> \<not> is_Pos C}"
      "{to_V C |C. C \<in> N \<and> is_Pos C} \<union> {to_V C |C. C \<in> M \<and> \<not> is_Pos C}"]
    by auto 
qed


interpretation neg_ext_cons_rel: consequence_relation "Pos bot" entails_neg
  using ext_cons_rel by simp 
    
    (* Splitting report Lemma 1 *)
lemma pos_neg_entails_bot: \<open>{C} \<union> {Neg C} \<Turnstile>\<^sub>\<sim> {Pos bot}\<close>
proof -
  have \<open>{C} \<union> {Neg C} \<Turnstile>\<^sub>\<sim> {}\<close> unfolding entails_neg_def
    by (smt (verit, ccfv_threshold) Collect_empty_eq Un_empty Un_insert_right empty_iff
      empty_subsetI entails_reflexive entails_subsets insertI1 insert_iff insert_subset
      is_Pos.simps(2) mem_Collect_eq singletonD sup_bot.right_neutral sup_bot_left to_V.simps(2))
  then show ?thesis using neg_ext_cons_rel.entails_subsets by blast 
qed

end
  


locale sound_inference_system =
  inference_system Inf + sound_cons: consequence_relation bot entails_sound
  for
    Inf :: "'f inference set" and
    bot :: "'f" and
    entails_sound :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>s" 50)
  + assumes
    sound: "\<iota> \<in> Inf \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s {concle_of \<iota>}"
    
   (* There are several options to represent sequences that I considered:
      - using everywhere a type \<open>nat \<Rightarrow> 'f set\<close> (pros: super simple, cons: maintenance heavy, i.e. any
    change must be propagated everywhere)
      - creating an abstract type as in Multiset.thy for the above type (pros: clean, cons: requires
    lifted definitions, i.e. more work)
      - restricting the lazy list codatatype used in RP and the saturation framework to only
    infinite lists (pros: closest to previous work, cons: propagate the restriction everywhere)
      - using one of the existing theory about infinite lists (which one?): HOL-library.Stream,
    lazy lists, infinite lists...

    Temporary conclusion: I'll try the last option with the Stream library.
    *)

no_notation IArray.sub (infixl "!!" 100)
  
definition is_derivation :: "('f set \<Rightarrow> 'f set \<Rightarrow> bool) \<Rightarrow> ('f set stream) \<Rightarrow> bool" where
  "is_derivation R Ns \<equiv> \<forall>i. R (Ns !! i) (Ns !! (Suc i))"
  
definition terminates :: "'f set stream \<Rightarrow> bool" where
  "terminates Ns \<equiv> \<exists>i. \<forall>j>i. Ns !! j = Ns !! i"

definition lim_inf :: "'f set stream \<Rightarrow> 'f set" where
  "lim_inf Ns = (\<Union>i. \<Inter>j \<in> {j. i \<le> j}. Ns !! j)"

abbreviation limit :: "'f set stream \<Rightarrow> 'f set" where "limit Ns \<equiv> lim_inf Ns"

definition lim_sup :: "'f set stream \<Rightarrow> 'f set" where
  "lim_sup Ns = (\<Inter>i. \<Union>j \<in> {j. i \<le> j}. Ns !! j)"

locale calculus = inference_system Inf + consequence_relation bot entails
  for
    bot :: "'f" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  + fixes
    Red_I :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set"
  assumes
    Red_I_to_Inf: "Red_I N \<subseteq> Inf" and
    Red_F_Bot: "N \<Turnstile> {bot} \<Longrightarrow> N - Red_F N \<Turnstile> {bot}" and (* /!\ check if this is ok *)
    Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'" and
    Red_I_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_I N \<subseteq> Red_I N'" and
    Red_F_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')" and
    Red_I_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_I N \<subseteq> Red_I (N - N')" and
    Red_I_of_Inf_to_N: "\<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_I N"
begin

definition saturated :: "'f set \<Rightarrow> bool" where
  "saturated N \<longleftrightarrow> Inf_from N \<subseteq> Red_I N"
  
definition Red_I_strict :: "'f set \<Rightarrow> 'f inference set" where
  "Red_I_strict N = {\<iota>. \<iota> \<in> Red_I N \<or> (\<iota> \<in> Inf \<and> bot \<in> N)}"
  
definition Red_F_strict :: "'f set \<Rightarrow> 'f set" where
  "Red_F_strict N = {C. C \<in> Red_F N \<or> (bot \<in> N \<and> C \<noteq> bot)}"
  
(* This proof helped detect a lack of precision in rmk 3 (missing restriction in the hypotheses *)
lemma strict_calc_if_nobot:
  "\<forall>N. bot \<notin> Red_F N \<Longrightarrow> calculus bot Inf entails Red_I_strict Red_F_strict"
proof
  fix N
  show \<open>Red_I_strict N \<subseteq> Inf\<close> unfolding Red_I_strict_def using Red_I_to_Inf by blast
next
  fix N
  assume
    bot_notin: "\<forall>N. bot \<notin> Red_F N" and
    entails_bot: \<open>N \<Turnstile> {bot}\<close>
  show \<open>N - Red_F_strict N \<Turnstile> {bot}\<close>
  proof (cases "bot \<in> N")
    assume bot_in: "bot \<in> N"
    have \<open>bot \<notin> Red_F N\<close> using bot_notin by blast
    then have \<open>bot \<notin> Red_F_strict N\<close> unfolding Red_F_strict_def by blast 
    then have \<open>Red_F_strict N = UNIV - {bot}\<close>
      unfolding Red_F_strict_def using bot_in by blast
    then have \<open>N - Red_F_strict N = {bot}\<close> using bot_in by blast
    then show \<open>N - Red_F_strict N \<Turnstile> {bot}\<close> using entails_reflexive[of bot] by simp
  next
    assume \<open>bot \<notin> N\<close>
    then have \<open>Red_F_strict N = Red_F N\<close> unfolding Red_F_strict_def by blast
    then show \<open>N - Red_F_strict N \<Turnstile> {bot}\<close> using Red_F_Bot[OF entails_bot] by simp
  qed
next
  fix N N' :: "'f set"
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>Red_F_strict N \<subseteq> Red_F_strict N'\<close>
    unfolding Red_F_strict_def using Red_F_of_subset by blast
next
  fix N N' :: "'f set"
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>Red_I_strict N \<subseteq> Red_I_strict N'\<close>
    unfolding Red_I_strict_def using Red_I_of_subset by blast
next
  fix N' N
  assume
    bot_notin: "\<forall>N. bot \<notin> Red_F N" and
    subs_red: "N' \<subseteq> Red_F_strict N"
  have \<open>bot \<notin> Red_F_strict N\<close>
    using bot_notin unfolding Red_F_strict_def by blast
  then have nbot_in: \<open>bot \<notin> N'\<close> using subs_red by blast 
  show \<open>Red_F_strict N \<subseteq> Red_F_strict (N - N')\<close>
  proof (cases "bot \<in> N")
    case True
    then have bot_in: "bot \<in> N - N'" using nbot_in by blast
    then show ?thesis unfolding Red_F_strict_def using bot_notin by force
  next
    case False
    then have eq_red: "Red_F_strict N = Red_F N" unfolding Red_F_strict_def by simp
    then have "N' \<subseteq> Red_F N" using subs_red by simp
    then have "Red_F N \<subseteq> Red_F (N - N')" using Red_F_of_Red_F_subset by simp
    then show ?thesis using eq_red Red_F_strict_def by blast 
  qed
next
  fix N' N
  assume
    "\<forall>N. bot \<notin> Red_F N" and
    subs_red: "N' \<subseteq> Red_F_strict N"
  then have bot_notin: "bot \<notin> N'" unfolding Red_F_strict_def by blast 
  then show "Red_I_strict N \<subseteq> Red_I_strict (N - N')"
  proof (cases "bot \<in> N")
    case True
    then show ?thesis
      unfolding Red_I_strict_def using bot_notin Red_I_to_Inf by fastforce 
  next
    case False
    then show ?thesis
      using bot_notin Red_I_to_Inf subs_red Red_I_of_Red_F_subset 
      unfolding Red_I_strict_def Red_F_strict_def by simp
  qed
next
  fix \<iota> N
  assume "\<iota> \<in> Inf"
  then show "concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_I_strict N"
    unfolding Red_I_strict_def using Red_I_of_Inf_to_N Red_I_to_Inf by simp
qed

definition weakly_fair :: "'f set stream \<Rightarrow> bool" where
  "weakly_fair Ns \<equiv> Inf_from (lim_inf Ns) \<subseteq> (\<Union>i. (Red_I (Ns !! i)))"

abbreviation fair :: "'f set stream \<Rightarrow> bool" where "fair N \<equiv> weakly_fair N"

definition derive :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<rhd>" 50) where
  "M \<rhd> N \<equiv> (M - N \<subseteq> Red_F N)"

(* for reference, the definition used in the saturation framework *)
(* inductive "derive" :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<rhd>" 50) where
     derive: "M - N \<subseteq> Red_F N \<Longrightarrow> M \<rhd> N" *)

lemma derive_refl: "M \<rhd> M" unfolding derive_def by simp

lemma deriv_red_in: \<open>M \<rhd> N \<Longrightarrow> Red_F M \<subseteq> N \<union> Red_F N\<close>
proof -
  fix M N
  assume deriv: \<open>M \<rhd> N\<close>
  then have \<open>M \<subseteq> N \<union> Red_F N\<close>
    unfolding derive_def by blast 
  then have red_m_in: \<open>Red_F M \<subseteq> Red_F (N \<union> Red_F N)\<close>
    using Red_F_of_subset by blast 
  have \<open>Red_F (N \<union> Red_F N) \<subseteq> Red_F (N \<union> Red_F N - (Red_F N - N))\<close>
    using Red_F_of_Red_F_subset[of "Red_F N - N" "N \<union> Red_F N"]
      Red_F_of_subset[of "N" "N \<union> Red_F N"] by fast
  then have \<open>Red_F (N \<union> Red_F N) \<subseteq> Red_F N\<close>
    by (metis Diff_subset_conv Red_F_of_subset Un_Diff_cancel lfp.leq_trans subset_refl sup.commute)
  then show \<open>Red_F M \<subseteq> N \<union> Red_F N\<close> using red_m_in by blast
qed

lemma derive_trans: "M \<rhd> N \<Longrightarrow> N \<rhd> N' \<Longrightarrow> M \<rhd> N'" 
  using deriv_red_in by (smt Diff_subset_conv derive_def subset_trans sup.absorb_iff2)

end
  
locale sound_calculus = sound_inference_system Inf bot entails_sound +
  consequence_relation bot entails
  for
    bot :: "'f" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) and
    entails_sound :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>s" 50)
    + fixes
    Red_I :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set"
    assumes
      Red_I_to_Inf: "Red_I N \<subseteq> Inf" and
      Red_F_Bot: "N \<Turnstile> {bot} \<Longrightarrow> N - Red_F N \<Turnstile> {bot}" and (* /!\ check if this is ok *)
      Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'" and
      Red_I_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_I N \<subseteq> Red_I N'" and
      Red_F_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')" and
      Red_I_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_I N \<subseteq> Red_I (N - N')" and
      Red_I_of_Inf_to_N: "\<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_I N"
begin

sublocale calculus bot Inf entails
  by (simp add: Preliminaries.calculus.intro Preliminaries.calculus_axioms.intro Red_F_Bot
    Red_F_of_Red_F_subset Red_F_of_subset Red_I_of_Inf_to_N Red_I_of_Red_F_subset Red_I_of_subset
    Red_I_to_Inf consequence_relation_axioms)
end
      
locale statically_complete_calculus = calculus +
  assumes statically_complete: "saturated N \<Longrightarrow> N \<Turnstile> {bot} \<Longrightarrow> bot \<in> N"
begin

lemma inf_from_subs: "M \<subseteq> N \<Longrightarrow> Inf_from M \<subseteq> Inf_from N"
  unfolding Inf_from_def by blast
    
    (* Splitting report Lemma 3 *)
lemma nobot_in_Red: \<open>bot \<notin> Red_F N\<close>
proof -
  have \<open>UNIV \<Turnstile> {bot}\<close>
    using entails_reflexive[of bot] entails_subsets[of "{bot}" UNIV "{bot}" "{bot}"] by fast
  then have non_red_entails_bot: \<open>UNIV - (Red_F UNIV) \<Turnstile> {bot}\<close> using Red_F_Bot[of UNIV] by simp
  have \<open>Inf_from UNIV \<subseteq> Red_I UNIV\<close>
    unfolding Inf_from_def using Red_I_of_Inf_to_N[of _ UNIV] by blast
  then have sat_non_red: \<open>saturated (UNIV - Red_F UNIV)\<close>
    unfolding saturated_def Inf_from_def using Red_I_of_Red_F_subset[of "Red_F UNIV" UNIV] by blast 
  have \<open>bot \<notin> Red_F UNIV\<close> 
    using statically_complete[OF sat_non_red non_red_entails_bot] by fast
  then show ?thesis using Red_F_of_subset[of _ UNIV] by auto
qed
  
  (* Splitting report Remark 4 *)
interpretation strict_calculus:
  statically_complete_calculus bot Inf entails Red_I_strict Red_F_strict
proof -
  interpret strict_calc: calculus bot Inf entails Red_I_strict Red_F_strict
  using strict_calc_if_nobot nobot_in_Red by blast 
    (* next property is not needed for the proof, but it is one of the claims from Rmk 3
    that must be verified *)
  have \<open>saturated N \<Longrightarrow> strict_calc.saturated N\<close>
    unfolding saturated_def strict_calc.saturated_def Red_I_strict_def by blast
  have \<open>strict_calc.saturated N \<Longrightarrow> N \<Turnstile> {bot} \<Longrightarrow> bot \<in> N\<close> for N
  proof -
    assume
      strict_sat: "strict_calc.saturated N" and
      entails_bot: "N \<Turnstile> {bot}"
    have \<open>bot \<notin> N \<Longrightarrow> Red_I_strict N = Red_I N\<close> unfolding Red_I_strict_def by simp
    then have \<open>bot \<notin> N \<Longrightarrow> saturated N\<close>
      unfolding saturated_def using strict_sat by (simp add: strict_calc.saturated_def) 
    then have \<open>bot \<notin> N \<Longrightarrow> bot \<in> N\<close>
      using statically_complete[OF _ entails_bot] by simp
    then show \<open>bot \<in> N\<close> by auto 
  qed
  then show \<open>statically_complete_calculus bot Inf entails Red_I_strict Red_F_strict\<close>
    unfolding statically_complete_calculus_def statically_complete_calculus_axioms_def
    using strict_calc.calculus_axioms by blast
qed

end

locale dynamically_complete_calculus = calculus +
  assumes dynamically_complete:
    \<open>is_derivation (\<rhd>) Ns \<Longrightarrow> fair Ns \<Longrightarrow> shd Ns \<Turnstile> {bot} \<Longrightarrow> \<exists>i. bot \<in> Ns !! i\<close>

    (* First attempt at formalizing sect. 2.3 *)
    (* below, I force 'v to be countable, but not infinite, alternative, enforce bijection with nat
    in the first locale where it is used? *)

    (* records are definitely overkill for this *)
(* record ('f, 'v::countable) AF =
 *   F :: 'f
 *     A :: "'v neg set" *)
    
    (* discussions on this datatype allowed to detect a spurious assumption: 'v doesn't need to be
    infinite*)
    (* TODO: should "countable" be added as a requirement of the AF_calculus locale? *)
datatype ('f, 'v::countable) AF = Pair (F_of: "'f") (A_of: "'v neg set")

definition is_interpretation :: "'v neg set \<Rightarrow> bool" where
  \<open>is_interpretation J = (\<forall>v1\<in>J. (\<forall>v2\<in>J. (to_V v1 = to_V v2 \<longrightarrow> is_Pos v1 = is_Pos v2)))\<close>
  
  (* TODO: find a shorter name for this type (?) *)
typedef 'v propositional_interpretation = "{J :: 'v neg set. is_interpretation J}"
proof
  show \<open>{} \<in> {J. is_interpretation J}\<close> unfolding is_interpretation_def by blast 
qed
  
  find_theorems name: Abs name: propositional_interpretation

abbreviation "interp_of \<equiv> Abs_propositional_interpretation"
abbreviation "strip \<equiv> Rep_propositional_interpretation"

context
begin
  setup_lifting type_definition_propositional_interpretation

  lift_definition belong_to :: "'v neg \<Rightarrow> 'v propositional_interpretation \<Rightarrow> bool" (infix "\<in>\<^sub>J" 90)
    is "(\<in>\<^sub>v)::('v neg \<Rightarrow> 'v neg set \<Rightarrow> bool)" .
end

definition total :: "'v propositional_interpretation \<Rightarrow> bool" where
  \<open>total J \<equiv> (\<forall>v. (\<exists>v\<^sub>J. v\<^sub>J \<in>\<^sub>J J \<and> to_V v\<^sub>J = v))\<close>
  
typedef 'v total_interpretation = "{J :: 'v propositional_interpretation. total J}"
proof
  show \<open>interp_of (Pos ` (UNIV :: 'v set)) \<in> {J. total J}\<close>
    unfolding total_def   
  proof 
    show "\<forall>v. \<exists>v\<^sub>J. v\<^sub>J \<in>\<^sub>J interp_of (range Pos) \<and> to_V v\<^sub>J = v"
    proof
      fix v
      have "Pos v \<in>\<^sub>J interp_of (range Pos) \<and> to_V (Pos v) = v"
        by (simp add: Abs_propositional_interpretation_inverse belong_to.rep_eq is_interpretation_def)
      then show "\<exists>v\<^sub>J. v\<^sub>J \<in>\<^sub>J interp_of (range Pos) \<and> to_V v\<^sub>J = v" by blast
    qed
  qed
qed

abbreviation "total_interp_of \<equiv> (\<lambda>x. Abs_total_interpretation (interp_of x))"
abbreviation "total_strip \<equiv> (\<lambda>x. strip (Rep_total_interpretation x))"
  
context
begin
  (* TODO : seems the command below fails. What is its impact? *)
  setup_lifting type_definition_total_interpretation

  lift_definition belong_to_total :: "'v neg \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" (infix "\<in>\<^sub>t" 90)
    is "(\<in>\<^sub>J)::('v neg \<Rightarrow> 'v propositional_interpretation \<Rightarrow> bool)" .
end
  (* TODO? If propositional_interpretation is never used, directly define total_interpretation from
  \<t>erm \<open>'v neg set\<close> *)

lemma neg_prop_interp: \<open>(v::'v neg) \<in>\<^sub>J J \<Longrightarrow> \<not> ((Neg v) \<in>\<^sub>J J)\<close>
proof transfer
  fix v J
  assume
    j_is: \<open>is_interpretation (J:: 'v neg set)\<close> and
    v_in: \<open>v \<in>\<^sub>v J\<close>
  then show \<open>\<not> Neg v \<in>\<^sub>v J\<close>
  proof (induction v)
    case (Pos C)
    then show ?case
      using is_in.simps(2)[of "Pos C"] is_in.simps(1) unfolding is_interpretation_def
      by (metis is_Pos.simps(1) is_Pos.simps(2) to_V.simps(1))
  next
    case (Neg w)
    then show ?case
      unfolding is_interpretation_def 
      by (metis is_Pos.simps(2) is_in.simps(2) to_V.simps(2))
  qed
qed

lemma neg_total_interp: \<open>(v::'v neg) \<in>\<^sub>t J \<Longrightarrow> \<not> ((Neg v) \<in>\<^sub>t J)\<close>
proof transfer
  fix v J
  assume v_in: \<open>v \<in>\<^sub>J J\<close>
  show \<open>\<not> Neg v \<in>\<^sub>J J\<close>
    using neg_prop_interp[OF v_in] by simp
qed


definition to_AF :: "'f \<Rightarrow> ('f, 'v::countable) AF" where
  \<open>to_AF C = Pair C {}\<close>

definition Neg_set :: "'v neg set \<Rightarrow> 'v neg set" ("\<sim>_" 55) where
  \<open>\<sim>V \<equiv> {Neg v |v. v \<in> V}\<close>

definition F_of_Inf :: "(('f, 'v::countable) AF) inference \<Rightarrow> 'f inference" where
  \<open>F_of_Inf \<iota>AF = (Infer (map F_of (prems_of \<iota>AF)) (F_of (concl_of \<iota>AF)))\<close>
  
(* locale propositional_interpretations =
 *   fixes
 *     \<J> :: "'v::countable neg set set"
 *   assumes
 *     all_interp: "J \<in> \<J> \<Longrightarrow> is_interpretation J" and
  *     all_in_J: "is_interpretation J \<Longrightarrow> J \<in> \<J>" *)


locale AF_calculus = sound_calculus bot Inf entails entails_sound Red_I Red_F
  (* + propositional_interpretations \<J>*)
  for
    bot :: "'f" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) and
    entails_sound :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>s" 50) and
    Red_I :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set"
  + fixes
    V:: "'v::countable itself" and
    (* \<J> :: "'v::countable neg set set" and *)
    fml :: "'v \<Rightarrow> 'f"
    assumes
      entails_sound_compact: \<open>M \<Turnstile>s N \<Longrightarrow> (\<exists>M'\<subseteq>M. (\<exists>N'\<subseteq>N. finite M' \<and> finite N' \<and> M' \<Turnstile>s N'))\<close>
    (*  j_is: \<open>\<J> = {J. is_interpretation J}\<close>*)
begin
  
  (* various attempts at representing the "enabled" concept *)
(* definition enabled0 :: "('f, 'v) AF \<Rightarrow> 'v neg set \<Rightarrow> bool" where
 *   \<open>enabled0 C J = (J \<in> \<J> \<and> ((A_of C) \<subseteq> J \<or> (F_of C = bot \<and> (\<sim> (A_of C)) \<inter> J = {})))\<close> *)

  (* J must be an interpretation, but this could also be verified outside of the definitions *)
(* inductive "enabled" :: "('f, 'v) AF \<Rightarrow> 'v neg set \<Rightarrow> bool" where
 *   cond1: "J \<in> \<J> \<Longrightarrow> (A_of C) \<subseteq> J \<Longrightarrow> enabled C J" |
  *   cond2: "J \<in> \<J> \<Longrightarrow> (F_of C = bot \<and> (\<sim> (A_of C)) \<inter> J = {}) \<Longrightarrow> enabled C J" *)
  
(* inductive "enabled" :: "('f, 'v) AF \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" where
 *   cond1: "(A_of C) \<subseteq> (total_strip J) \<Longrightarrow> enabled C J" |
  *   cond2: "(F_of C = bot \<and> (\<sim> (A_of C)) \<inter> (total_strip J) = {}) \<Longrightarrow> enabled C J" *)

definition \<iota>F_of :: "('f, 'v) AF inference \<Rightarrow> 'f inference" where
  \<open>\<iota>F_of \<iota> = Infer (List.map F_of (prems_of \<iota>)) (F_of (concl_of \<iota>))\<close>
  
definition propositional_projection :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set" ("proj\<^sub>\<bottom>") where
  \<open>proj\<^sub>\<bottom> N = {C. C \<in> N \<and> F_of C = bot}\<close>

definition enabled :: "('f, 'v) AF \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" where
  "enabled C J \<equiv> (A_of C) \<subseteq> (total_strip J)"

definition enabled_set :: "('f, 'v) AF set \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" where
  \<open>enabled_set N J = (\<forall>C\<in>N. enabled C J)\<close>

definition enabled_inf :: "('f, 'v) AF inference \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" where
  \<open>enabled_inf \<iota> J = (\<forall>C\<in> set (prems_of \<iota>). enabled C J)\<close>
  
definition enabled_projection :: "('f, 'v) AF set \<Rightarrow> 'v total_interpretation \<Rightarrow> 'f set"
  (infix "proj\<^sub>J" 60)  where
  \<open>N proj\<^sub>J J = {F_of C | C. C \<in> N \<and> enabled C J}\<close>

definition enabled_projection_Inf :: "('f, 'v) AF inference set \<Rightarrow> 'v total_interpretation \<Rightarrow>
  'f inference set" (infix "\<iota>proj\<^sub>J" 60) where
  \<open>I \<iota>proj\<^sub>J J = {\<iota>F_of \<iota> | \<iota>. \<iota> \<in> I \<and> enabled_inf \<iota> J}\<close>

fun fml_ext :: "'v neg \<Rightarrow> 'f neg" where
  "fml_ext (Pos v) = Pos (fml v)" |
  "fml_ext (Neg v) = Neg (fml_ext v)"

definition sound_consistent :: "'v total_interpretation \<Rightarrow> bool" where
  \<open>sound_consistent J \<equiv> \<not> (sound_cons.entails_neg (fml_ext ` (total_strip J)) {Pos bot})\<close>
  
  (* most probably overkill *)
(* abbreviation F_of_set :: "('f, 'v) AF set \<Rightarrow> 'f set" where
  \<open>F_of_set N \<equiv> F_of ` N\<close> *)
 
definition propositional_model :: "'v total_interpretation \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>p" 50)
  where
  \<open>J \<Turnstile>\<^sub>p N \<equiv> bot \<notin> ((proj\<^sub>\<bottom> N) proj\<^sub>J J)\<close>

definition sound_propositional_model :: "'v total_interpretation \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool"
  (infix "\<Turnstile>s\<^sub>p" 50) where
  \<open>J \<Turnstile>s\<^sub>p N \<equiv> (bot \<notin> ((enabled_projection (propositional_projection N) J)) \<or>
    \<not> sound_consistent J)\<close>

definition propositionally_unsatisfiable :: "('f, 'v) AF set \<Rightarrow> bool" where
  \<open>propositionally_unsatisfiable N \<equiv> \<forall>J. \<not> (J \<Turnstile>\<^sub>p N)\<close>
 
definition AF_entails :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>A\<^sub>F" 50) where
  \<open>AF_entails M N \<equiv> (\<forall>J. (enabled_set N J \<longrightarrow> M proj\<^sub>J J \<Turnstile> F_of ` N))\<close>
  
definition AF_entails_sound :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool" (infix "\<Turnstile>s\<^sub>A\<^sub>F" 50) where
  \<open>AF_entails_sound M N \<equiv> (\<forall>J. (enabled_set N J \<longrightarrow>
  sound_cons.entails_neg ((fml_ext ` (total_strip J)) \<union> (Pos ` (M proj\<^sub>J J))) (Pos ` F_of ` N)))\<close>
  
  (* Splitting report Lemma 5, 1/2 *)
sublocale AF_cons_rel: consequence_relation "to_AF bot" AF_entails
proof
  show \<open>{to_AF bot} \<Turnstile>\<^sub>A\<^sub>F {}\<close>
    unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def
    using bot_entails_empty by simp
next
  fix C
  show \<open>{C} \<Turnstile>\<^sub>A\<^sub>F {C}\<close>
    unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
    using entails_reflexive by simp
next
  fix M N P Q
  assume m_in_n: \<open>M \<subseteq> N\<close> and
    p_in_q: \<open>P \<subseteq> Q\<close> and
    m_entails_p: \<open>M \<Turnstile>\<^sub>A\<^sub>F P\<close>
  show \<open>N \<Turnstile>\<^sub>A\<^sub>F Q\<close>
    unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
  proof (rule allI, rule impI)
    fix J
    assume q_enabled: \<open>\<forall>C\<in>Q. A_of C \<subseteq> total_strip J\<close>
    have \<open>{F_of C |C. C \<in> M \<and> A_of C \<subseteq> total_strip J} \<subseteq> {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J}\<close>
      using m_in_n by blast
    moreover have \<open>F_of ` P \<subseteq> F_of ` Q\<close>
      using p_in_q by blast
    ultimately show \<open>{F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J} \<Turnstile> F_of ` Q\<close>
      using m_entails_p  entails_subsets
      unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
      by (metis (mono_tags, lifting) q_enabled p_in_q subset_iff)
  qed
next
  fix M N
  assume \<open>\<forall>M' N'. M \<subseteq> M' \<and> N \<subseteq> N' \<and> M' \<union> N' = UNIV \<longrightarrow> M' \<Turnstile>\<^sub>A\<^sub>F N'\<close>
  show \<open>M \<Turnstile>\<^sub>A\<^sub>F N\<close>
    sorry
  (* fix M P N Q
  assume
    m_entails_p: \<open>M \<Turnstile>\<^sub>A\<^sub>F P\<close> and
    n_to_q_m: \<open>\<forall>C\<in>M. N \<Turnstile>\<^sub>A\<^sub>F Q \<union> {C}\<close> and
    n_p_to_q: \<open>\<forall>D\<in>P. N \<union> {D} \<Turnstile>\<^sub>A\<^sub>F Q\<close> 
  show \<open>N \<Turnstile>\<^sub>A\<^sub>F Q\<close>
    unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
  proof (rule allI, rule impI)
    fix J
    assume q_enabled: \<open>\<forall>C\<in>Q. A_of C \<subseteq> total_strip J\<close>
    show \<open>{F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J} \<Turnstile> F_of ` Q\<close>
    proof (cases "\<forall>C\<in>P. A_of C \<subseteq> total_strip J")  
    assume
      p_enabled: \<open>\<forall>C\<in>P. A_of C \<subseteq> total_strip J\<close> (* and *)
      (* m_enabled: \<open>\<forall>C\<in>M. A_of C \<subseteq> total_strip J\<close> *)
    define M\<^sub>J :: "('f, 'v) AF set" where "M\<^sub>J = {C. C \<in> M \<and> A_of C \<subseteq> total_strip J}"
    then have mj_enabled: \<open>\<forall>C\<in>M\<^sub>J. A_of C \<subseteq> total_strip J\<close>
      by blast 
    have simp_m: \<open>{F_of C |C. C \<in> M\<^sub>J \<and> A_of C \<subseteq> total_strip J} = F_of ` M\<^sub>J\<close>
      using mj_enabled by blast 
    have \<open>{F_of C |C. C \<in> P \<and> A_of C \<subseteq> total_strip J} = F_of ` P\<close>
      using p_enabled by blast 
    have each_hyp1: \<open>F_of ` M\<^sub>J \<Turnstile> F_of ` P\<close>
      using m_entails_p simp_m p_enabled 
      unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
      by (simp add: M\<^sub>J_def setcompr_eq_image)
    have \<open>\<forall>C\<in>M\<^sub>J. (\<forall>C\<in>Q \<union> {C}. A_of C \<subseteq> total_strip J)\<close> using mj_enabled q_enabled by fast
    then have \<open>\<forall>C\<in>M\<^sub>J. {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J} \<Turnstile> F_of ` (Q \<union> {C})\<close>
      using n_to_q_m M\<^sub>J_def
      unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
       by blast 
     then have each_hyp2:
       \<open>\<forall>C\<in>F_of ` M\<^sub>J. {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J} \<Turnstile> F_of ` Q \<union> {C}\<close>
      by force
    have \<open>\<forall>D\<in>P. {F_of C |C. C \<in> N \<union> {D} \<and> A_of C \<subseteq> total_strip J} \<Turnstile> F_of ` Q\<close> 
      using n_p_to_q q_enabled
      unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
      by blast 
    moreover have \<open>\<forall>D\<in>P. {F_of C |C. C \<in> N \<union> {D} \<and> A_of C \<subseteq> total_strip J} =
      {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J} \<union> {F_of C |C. C \<in> {D}}\<close>
      using p_enabled
      by blast 
    ultimately have each_hyp3:
      \<open>\<forall>D\<in>F_of ` P. {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J} \<union> {D} \<Turnstile> F_of ` Q\<close>
      by auto
    show \<open>{F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J} \<Turnstile> F_of ` Q\<close>
      using entails_each[OF each_hyp1 each_hyp2 each_hyp3] .
  next
    assume
      p_not_enabled: \<open>\<not> (\<forall>C\<in>P. A_of C \<subseteq> total_strip J)\<close>
    then obtain D where d_in: "D \<in> P" and d_not_enabled: "\<not> (A_of D \<subseteq> total_strip J)"
      by fast
    have \<open>{F_of C |C. C \<in> N \<union> {D} \<and> A_of C \<subseteq> total_strip J} \<Turnstile> F_of ` Q\<close>
      using n_p_to_q q_enabled d_in
      unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
      by blast 
    then show \<open>{F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J} \<Turnstile> F_of ` Q\<close>
      using d_not_enabled 
        by (smt (verit, best) Collect_cong Un_iff mem_Collect_eq singleton_conv2)
    qed
  qed *)
qed

interpretation ext_cons_rel_std: consequence_relation "Pos (to_AF bot)" AF_cons_rel.entails_neg
  using AF_cons_rel.ext_cons_rel .

interpretation sound_cons_rel: consequence_relation "Pos bot" sound_cons.entails_neg
  using sound_cons.ext_cons_rel .
    
(* Splitting report Lemma 5, 2/2 *)
interpretation AF_sound_cons_rel: consequence_relation "to_AF bot" AF_entails_sound
proof
  have \<open>{Pos bot} \<subseteq> Pos ` {F_of C |C. C \<in> {to_AF bot} \<and>
    A_of C \<subseteq> total_strip (J :: 'v total_interpretation)}\<close>
    unfolding to_AF_def by simp
  then show \<open>{to_AF bot} \<Turnstile>s\<^sub>A\<^sub>F {}\<close>
    using sound_cons_rel.bot_entails_empty sound_cons_rel.entails_subsets
    unfolding AF_entails_sound_def enabled_def enabled_projection_def
    by (smt (verit, ccfv_threshold) AF.sel(1) AF.sel(2) UnCI bot.extremum image_eqI insertI1
      mem_Collect_eq singletonD subsetI to_AF_def)
next
  fix C :: "('f, 'v) AF"
  have \<open>Pos ` {F_of Ca |Ca. Ca \<in> {C} \<and> A_of Ca \<subseteq> total_strip J} \<subseteq> (Pos ` F_of ` {C})\<close>
    by auto
  show \<open>{C} \<Turnstile>s\<^sub>A\<^sub>F {C}\<close>
    unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
    using sound_cons_rel.entails_reflexive[of "Pos (F_of C)"] sound_cons_rel.entails_subsets 
    by (smt (verit, ccfv_SIG) UnCI empty_subsetI imageI insert_subset mem_Collect_eq singletonI)
next
  fix M N P Q
  assume m_in_n: \<open>M \<subseteq> N\<close> and
    p_in_q: \<open>P \<subseteq> Q\<close> and
    m_entails_p: \<open>M \<Turnstile>s\<^sub>A\<^sub>F P\<close>
  show \<open>N \<Turnstile>s\<^sub>A\<^sub>F Q\<close>
    unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
  proof (rule allI, rule impI)
    fix J
    assume q_enabled: \<open>\<forall>C\<in>Q. A_of C \<subseteq> total_strip J\<close>
    have \<open>{F_of C |C. C \<in> M \<and> A_of C \<subseteq> total_strip J} \<subseteq>
      {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J}\<close>
      using m_in_n by blast
    moreover have \<open>F_of ` P \<subseteq> F_of ` Q\<close>
      using p_in_q by blast
    ultimately show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union>
      Pos ` {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J}) (Pos ` F_of ` Q)\<close>
      using m_entails_p  sound_cons_rel.entails_subsets m_in_n
      unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
      by (smt (z3) Un_iff consequence_relation.entails_subsets imageE image_eqI mem_Collect_eq
        p_in_q q_enabled sound_cons_rel.consequence_relation_axioms subset_iff)
  qed 
next
  fix M N
  assume \<open>\<forall>M' N'. M \<subseteq> M' \<and> N \<subseteq> N' \<and> M' \<union> N' = UNIV \<longrightarrow> M' \<Turnstile>s\<^sub>A\<^sub>F N'\<close>
  show \<open>M \<Turnstile>s\<^sub>A\<^sub>F N\<close>
    sorry
(*  fix M P N Q
  assume
    m_entails_p: "M \<Turnstile>s\<^sub>A\<^sub>F P" and
    n_to_q_m: "\<forall>C\<in>M. N \<Turnstile>s\<^sub>A\<^sub>F Q \<union> {C}" and
    n_p_to_q: "\<forall>D\<in>P. N \<union> {D} \<Turnstile>s\<^sub>A\<^sub>F Q"
  show \<open>N \<Turnstile>s\<^sub>A\<^sub>F Q\<close>
    unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
  proof (rule allI, rule impI)
    fix J
    assume q_enabled: \<open>\<forall>C\<in>Q. A_of C \<subseteq> total_strip J\<close>
    show \<open>sound_cons.entails_neg
      (fml_ext ` total_strip J \<union> Pos ` {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J})
      (Pos ` F_of ` Q)\<close>
    proof (cases "\<forall>C\<in>P. A_of C \<subseteq> total_strip J")  
    assume
      p_enabled: \<open>\<forall>C\<in>P. A_of C \<subseteq> total_strip J\<close>
    define M\<^sub>J :: "('f, 'v) AF set" where "M\<^sub>J = {C. C \<in> M \<and> A_of C \<subseteq> total_strip J}"
    have each_hyp1:
      \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> (Pos ` F_of ` M\<^sub>J)) (Pos ` F_of ` P)\<close>
      using m_entails_p p_enabled 
      unfolding to_AF_def AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
      by (simp add: M\<^sub>J_def setcompr_eq_image)
    have \<open>\<forall>C\<in>M\<^sub>J. (\<forall>C\<in>Q \<union> {C}. A_of C \<subseteq> total_strip J)\<close>
      using q_enabled M\<^sub>J_def by fastforce
    then have \<open>\<forall>C\<in>M\<^sub>J. sound_cons.entails_neg
      (fml_ext ` total_strip J \<union> Pos ` {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J})
      (Pos ` F_of `( Q \<union> {C}))\<close>
      using n_to_q_m q_enabled 
      unfolding to_AF_def AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
      by (metis (no_types, lifting) M\<^sub>J_def mem_Collect_eq) 
    moreover have \<open>\<forall>C\<in>fml_ext ` total_strip J. sound_cons.entails_neg
      (fml_ext ` total_strip J \<union> Pos ` {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J})
      (Pos ` F_of `  Q \<union> {C})\<close>
      using sound_cons_rel.entails_reflexive sound_cons_rel.entails_subsets 
       by (meson UnCI empty_subsetI insert_subset subsetI) 
    ultimately have each_hyp2:
      \<open>\<forall>C\<in>fml_ext ` total_strip J \<union> Pos ` F_of ` M\<^sub>J. sound_cons.entails_neg
      (fml_ext ` total_strip J \<union> Pos ` {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J})
      (Pos ` F_of ` Q \<union> {C})\<close>
      by auto
    have \<open>\<forall>D\<in>P. sound_cons.entails_neg
      (fml_ext ` total_strip J \<union> Pos ` {F_of C |C. C \<in> N \<union> {D} \<and> A_of C \<subseteq> total_strip J})
      (Pos ` F_of ` Q)\<close>
      using n_p_to_q q_enabled
      unfolding to_AF_def AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
      by blast
    moreover have \<open>\<forall>D\<in>P. Pos ` {F_of C |C. C \<in> N \<union> {D} \<and> A_of C \<subseteq> total_strip J} =
      Pos ` {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J} \<union> Pos ` F_of ` {D}\<close>
      using p_enabled by blast 
    ultimately have each_hyp3: \<open>\<forall>D\<in>Pos ` F_of ` P. sound_cons.entails_neg
      (fml_ext ` total_strip J \<union> Pos ` {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J} \<union> {D})
      (Pos ` F_of ` Q)\<close>
      by simp
    show \<open>sound_cons.entails_neg
      (fml_ext ` total_strip J \<union> Pos ` {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J})
      (Pos ` F_of ` Q)\<close>
      using sound_cons_rel.entails_each[OF each_hyp1 each_hyp2 each_hyp3] .
  next
    assume
      p_not_enabled: \<open>\<not> (\<forall>C\<in>P. A_of C \<subseteq> total_strip J)\<close>
    then obtain D where d_in: "D \<in> P" and d_not_enabled: "\<not> (A_of D \<subseteq> total_strip J)"
      by fast
    have \<open>sound_cons.entails_neg
      (fml_ext ` total_strip J \<union> Pos ` {F_of C |C. C \<in> N \<union> {D} \<and> A_of C \<subseteq> total_strip J})
      (Pos ` F_of ` Q)\<close>
      using n_p_to_q q_enabled d_in
      unfolding to_AF_def AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
      by blast 
    then show \<open>sound_cons.entails_neg
      (fml_ext ` total_strip J \<union> Pos ` {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J})
      (Pos ` F_of ` Q)\<close>
      using d_not_enabled 
      by (smt (verit, best) Collect_cong Un_iff mem_Collect_eq singleton_conv2)
    qed 
  qed *)
qed

lemma sound_entail_tautology: "{} \<Turnstile>s\<^sub>A\<^sub>F {Pair (fml (v::'v)) {Pos v}}"
  unfolding AF_entails_sound_def enabled_projection_def enabled_set_def total_def
    sound_cons.entails_neg_def enabled_def
proof (simp, rule allI, rule impI)
  fix J 
  assume \<open>Pos v \<in> total_strip J\<close>
  then have \<open>fml v \<in> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C}\<close>
    by force
  then show \<open>{to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<Turnstile>s
    insert (fml v) {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}\<close>
    by (meson Set.insert_mono empty_subsetI insert_subset sound_cons.entails_reflexive
      sound_cons.entails_subsets)
qed
  
  (* this is a counter-example to an early version of the lemma below
   * without the precondition \<not> {} \<Turnstile> {} *)
lemma cex_entailments_inclusion:
  assumes
    tautoAF: \<open>{} \<Turnstile>\<^sub>A\<^sub>F {}\<close> and
    sound_notautoAF: \<open>\<not> ({} \<Turnstile>s\<^sub>A\<^sub>F {to_AF bot})\<close>
  shows \<open>\<exists>C D. proj\<^sub>\<bottom> C \<Turnstile>\<^sub>A\<^sub>F proj\<^sub>\<bottom> D \<and> \<not> (proj\<^sub>\<bottom> C \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> D)\<close> 
proof (rule exI, rule exI)
  have \<open>\<forall>J. enabled_set {} J\<close> unfolding enabled_set_def enabled_def by blast 
  then have tautoF: \<open>{} \<Turnstile> {}\<close> using tautoAF unfolding AF_entails_def enabled_projection_def by simp
  have empty_entails: \<open>{} \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    using entails_empty_reflexive_dangerous[OF tautoF] unfolding AF_entails_def by blast 
  define C  :: "('f, 'v) AF set" where \<open>C = {}\<close>
  then have c_is: \<open>proj\<^sub>\<bottom> C = {}\<close> unfolding propositional_projection_def by blast 
  define D :: "('f, 'v) AF set" where \<open>D = {to_AF bot}\<close> 
  then have d_is: \<open>proj\<^sub>\<bottom> D = {to_AF bot}\<close>
    unfolding propositional_projection_def to_AF_def
    by (metis (mono_tags, lifting) AF.sel(1) mem_Collect_eq singletonD subsetI subset_antisym)
  have pos: \<open>proj\<^sub>\<bottom> C \<Turnstile>\<^sub>A\<^sub>F proj\<^sub>\<bottom> D\<close> using c_is d_is empty_entails by auto 
  have neg: \<open>\<not> (proj\<^sub>\<bottom> C \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> D)\<close> using c_is d_is sound_notautoAF by auto 
  show \<open>proj\<^sub>\<bottom> C \<Turnstile>\<^sub>A\<^sub>F proj\<^sub>\<bottom> D \<and> \<not> proj\<^sub>\<bottom> C \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> D\<close> using pos neg by auto 
qed

lemma entails_in_sound_entails_for_prop_clauses:
  assumes
    entails_useful: \<open>\<not> {} \<Turnstile>\<^sub>A\<^sub>F {}\<close> and
    entails_nonsound: \<open>proj\<^sub>\<bottom> C\<^sub>1 \<Turnstile>\<^sub>A\<^sub>F proj\<^sub>\<bottom> C\<^sub>2\<close>
  shows \<open>proj\<^sub>\<bottom> C\<^sub>1 \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> C\<^sub>2\<close>
proof -
  show \<open>proj\<^sub>\<bottom> C\<^sub>1 \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> C\<^sub>2\<close>
    unfolding AF_entails_sound_def 
  proof
    fix J
    show \<open>enabled_set (proj\<^sub>\<bottom> C\<^sub>2) J \<longrightarrow> sound_cons.entails_neg
      (fml_ext ` total_strip J \<union> Pos ` (proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J)) (Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2)\<close>
    proof
      assume enabled_c2: \<open>enabled_set (proj\<^sub>\<bottom> C\<^sub>2) J\<close>
      have empty_bot_proj_c1: \<open>F_of ` proj\<^sub>\<bottom> C\<^sub>1 = {} \<or> F_of ` proj\<^sub>\<bottom> C\<^sub>1 = {bot}\<close>
        unfolding propositional_projection_def enabled_projection_def by force
      have empty_bot_proj_c2: \<open>F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {} \<or> F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {bot}\<close>
        unfolding propositional_projection_def enabled_projection_def by force
          {
      assume \<open>(proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J) = {}\<close>
      then have \<open>False\<close>
        using entails_useful entails_nonsound empty_bot_proj_c2
        by (metis AF_entails_def enabled_c2 entails_bot_to_entails_empty
          entails_empty_reflexive_dangerous)
            }
      then have c1_to_bot: \<open>(proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J) = {bot}\<close>
        unfolding enabled_projection_def using empty_bot_proj_c1
        by (smt (verit, best) Collect_cong emptyE empty_Collect_eq mem_Collect_eq rev_image_eqI
          singleton_conv2)
      have \<open>Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {} \<or> Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {Pos bot}\<close>
        unfolding propositional_projection_def enabled_projection_def by force
      then have \<open>{C. C \<in> Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 \<and> \<not> is_Pos C} = {}\<close>
        by auto
      then have c2_to_empty: \<open>{to_V C | C. C \<in> Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 \<and> \<not> is_Pos C} = {}\<close>
        by auto
      have \<open>bot \<in> {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J) \<and> is_Pos C}\<close>
        using c1_to_bot by force 
      then show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J))
        (Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2)\<close>
        unfolding sound_cons.entails_neg_def
        using sound_cons.bot_entails_empty sound_cons.entails_subsets
        by (smt (z3) c2_to_empty empty_subsetI insert_subset sup_bot.right_neutral)
    qed 
  qed 
qed

lemma [simp]: \<open>F_of ` to_AF ` N = N\<close>
  unfolding to_AF_def by force

lemma [simp]: \<open>to_AF ` M proj\<^sub>J J = M\<close>
  unfolding to_AF_def enabled_projection_def enabled_def by force

lemma [simp]: \<open>enabled_set (to_AF ` N) J\<close>
  unfolding enabled_set_def enabled_def to_AF_def by simp

lemma [simp]: \<open>{to_V C |C. C \<in> Pos ` N \<and> \<not> is_Pos C} = {}\<close>
  by auto
    
lemma [simp]: \<open>{to_V C |C. C \<in> U \<union> Pos ` M \<and> \<not> is_Pos C} = {to_V C |C. C \<in> U \<and> \<not> is_Pos C}\<close>
  by auto

  (* Splitting report Lemma 6, 1/2 *)
lemma \<open>(to_AF ` M \<Turnstile>\<^sub>A\<^sub>F to_AF ` N) \<equiv> (M \<Turnstile> N)\<close>
  unfolding AF_entails_def by simp

lemma distrib_union_in_set: \<open>{f a |a. a\<in> B \<union> C \<and> D a} = {f a| a. a\<in>B\<and>D a} \<union> {f a| a. a\<in>C \<and> D a}\<close>
  by blast
    
lemma [simp]: \<open>{to_V C |C. C \<in> Pos ` M \<and> is_Pos C} = M\<close>
  by force


lemma finite_subsets_split: \<open>\<forall>J. \<exists>A. finite A \<and> A \<subseteq> B J \<union> C \<Longrightarrow>
  \<exists>A1 A2. finite A1 \<and> finite A2 \<and> A1 \<subseteq> B J \<and> A2 \<subseteq> C\<close>
  by blast 

lemma finite_subset_image_with_prop:
  assumes "finite B"
  shows "B \<subseteq> {f x |x. x \<in> A \<and> P x} \<Longrightarrow> \<exists>C\<subseteq>A. finite C \<and> B = f ` C \<and> (\<forall>x\<in>C. P x)"
  using assms
proof induct
  case empty
  then show ?case by simp
next
  case insert
  then show ?case
    by (clarsimp simp del: image_insert simp add: image_insert [symmetric]) blast
qed

  (* Splitting report Lemma 6, 2/2 *)
lemma \<open>(to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N) \<equiv> (M \<Turnstile>s N)\<close>
proof -
  fix M N
    {
  assume \<open>to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N\<close>
  then have \<open> \<forall>J. (\<exists>M' N'. finite M' \<and> finite N' \<and>
    M' \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` M \<and> is_Pos C} \<and>
    N' \<subseteq> N \<union>
    {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` M \<and> \<not> is_Pos C} \<and>
    M' \<Turnstile>s N')\<close>
    using entails_sound_compact unfolding AF_entails_sound_def sound_cons.entails_neg_def
    by (simp, meson)
  moreover have \<open>\<forall>J. {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` M \<and> is_Pos C} =
    {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> {to_V C |C. C \<in> Pos ` M \<and> is_Pos C}\<close>
    by blast
  moreover have \<open>\<forall>J. {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` M \<and> \<not> is_Pos C} =
    {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<union> {to_V C |C. C \<in> Pos ` M \<and> \<not> is_Pos C}\<close>
    by blast
  ultimately have finite_sound_entails_m'_n': \<open>\<forall>J. (\<exists>M' N'. finite M' \<and> finite N' \<and>
    M' \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> M \<and>
    N' \<subseteq> N \<union> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<and>
    M' \<Turnstile>s N')\<close>
    by auto 
  have finite_sound_entails_m'_n'_jpos_jneg:
    \<open>\<forall>J. \<exists>fml_Jpos fml_Jneg M' N'. finite fml_Jpos \<and> finite fml_Jneg \<and> finite M' \<and> finite N' \<and>
    M' \<subseteq> M \<and> N' \<subseteq> N \<and> fml_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<and>
    fml_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<and>
    fml_Jpos \<union> M' \<Turnstile>s fml_Jneg \<union> N'\<close>
  proof
    fix J
    obtain M' N' where finite_m': "finite M'" and finite_n': "finite N'" and
      m'_sub: "M' \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<union> M" and
      n'_sub: "N' \<subseteq> N \<union> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}" and
      m'_entails_n': "M' \<Turnstile>s N'"
      using finite_sound_entails_m'_n' by meson
    obtain M1 fml_Jpos where m'_split: "M1 \<union> fml_Jpos = M'" and m1_sub: "M1 \<subseteq> M" and
      j1_sub: "fml_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C}"
      using m'_sub by (smt (z3) Un_commute subset_UnE) 
    have finite_m1_j1: "finite M1" "finite fml_Jpos"
      using m'_split finite_m' by auto
    obtain N1 fml_Jneg where n'_split: "N1 \<union> fml_Jneg = N'" and n1_sub: "N1 \<subseteq> N" and
      j2_sub: "fml_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}"
      using n'_sub by (smt (z3) Un_commute subset_UnE) 
    have finite_n1_j2: "finite N1" "finite fml_Jneg"
      using n'_split finite_n' by auto 
    have unions_entail: \<open>M1 \<union> fml_Jpos \<Turnstile>s N1 \<union> fml_Jneg\<close>
      using m'_entails_n' m'_split n'_split
      by metis
    show \<open>\<exists>fml_Jpos fml_Jneg M' N'. finite fml_Jpos \<and> finite fml_Jneg \<and> finite M' \<and> finite N' \<and>
      M' \<subseteq> M \<and> N' \<subseteq> N \<and> fml_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<and>
      fml_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<and>
      fml_Jpos \<union> M' \<Turnstile>s fml_Jneg \<union> N'\<close>
      using finite_m1_j1 finite_n1_j2 m1_sub n1_sub j1_sub j2_sub unions_entail 
      by (smt (verit, best) Un_commute) 
   qed   
   have finite_sound_entail_fml_j_pos_neg:
     \<open>\<forall>J. \<exists>fml_Jpos fml_Jneg. finite fml_Jpos \<and> finite fml_Jneg \<and>
     fml_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<and>
     fml_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<and>
     fml_Jpos \<union> M \<Turnstile>s fml_Jneg \<union> N\<close>
   proof
     fix J
     obtain M' N' fml_Jpos fml_Jneg where finite_jpos: "finite fml_Jpos" and
       finite_jneg: "finite fml_Jneg" and "finite M'" and "finite N'" and m'_subs:"M' \<subseteq> M" and
       n'_subs:"N' \<subseteq> N" and
       jpos_subs: "fml_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C}" and
       jneg_subs: "fml_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}" and
       sound_entails:"fml_Jpos \<union> M' \<Turnstile>s fml_Jneg \<union> N'"
       using finite_sound_entails_m'_n'_jpos_jneg by meson
     have \<open>fml_Jpos \<union> M \<Turnstile>s fml_Jneg \<union> N\<close>
       using sound_cons.entails_subsets m'_subs n'_subs sound_entails by (meson Un_mono subset_refl) 
     then show \<open>\<exists>fml_Jpos fml_Jneg. finite fml_Jpos \<and> finite fml_Jneg \<and> 
       fml_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C} \<and>
       fml_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C} \<and>
       fml_Jpos \<union> M \<Turnstile>s fml_Jneg \<union> N\<close>
       using finite_jpos finite_jneg jpos_subs jneg_subs 
       by blast
   qed 
   have finite_sound_entail_fml_j:
     \<open>\<forall>J. \<exists>fml_Jfin. finite fml_Jfin \<and> fml_Jfin \<subseteq> fml_ext ` total_strip J \<and>
     {to_V C |C. C \<in> fml_Jfin \<and> is_Pos C} \<union> M \<Turnstile>s {to_V C |C. C \<in> fml_Jfin \<and> \<not> is_Pos C} \<union> N\<close>
   proof
     fix J
     obtain toV_Jpos toV_Jneg where fin_vpos: "finite toV_Jpos" and fin_vneg: "finite toV_Jneg" and
       jpos_subs: "toV_Jpos \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> is_Pos C}" and
       jneg_subs: "toV_Jneg \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<and> \<not> is_Pos C}" and
       pos_entails_neg: "toV_Jpos \<union> M \<Turnstile>s toV_Jneg \<union> N"
       using finite_sound_entail_fml_j_pos_neg by meson 
     have \<open>\<exists>Jpos\<subseteq>fml_ext ` total_strip J. finite Jpos \<and> toV_Jpos = to_V ` Jpos \<and>
       (\<forall>C\<in>Jpos. is_Pos C)\<close>
       using finite_subset_image_with_prop[OF fin_vpos,
         of "\<lambda>x. to_V x"  "fml_ext ` total_strip J" is_Pos, OF jpos_subs]
       by blast 
     then obtain Jpos where fpos_subs: \<open>Jpos \<subseteq> fml_ext ` total_strip J\<close> and
       fin_fpos: \<open>finite Jpos\<close> and v_to_f_pos: \<open>toV_Jpos = to_V ` Jpos\<close> and
       pos_all_pos: \<open>\<forall>C\<in>Jpos. is_Pos C\<close>
       by blast
     have \<open>\<exists>Jneg\<subseteq>fml_ext ` total_strip J. finite Jneg \<and> toV_Jneg = to_V ` Jneg \<and>
       (\<forall>C\<in>Jneg. \<not> is_Pos C)\<close>
       using finite_subset_image_with_prop[OF fin_vneg,
         of "\<lambda>x. to_V x"  "fml_ext ` total_strip J" "\<lambda>x. \<not> is_Pos x", OF jneg_subs]
       by blast 
     then obtain Jneg where fneg_subs: \<open>Jneg \<subseteq> fml_ext ` total_strip J\<close> and
       fin_fneg: \<open>finite Jneg\<close> and v_to_f_neg: \<open>toV_Jneg = to_V ` Jneg\<close> and
       neg_all_neg: \<open>\<forall>C\<in>Jneg. \<not> is_Pos C\<close>
       by blast
     define fml_Jfin where "fml_Jfin = Jpos \<union> Jneg"
     have \<open>{to_V C |C. C \<in> fml_Jfin \<and> is_Pos C} = to_V ` Jpos\<close>
       using pos_all_pos neg_all_neg unfolding fml_Jfin_def by blast 
     moreover have \<open>{to_V C |C. C \<in> fml_Jfin \<and> \<not> is_Pos C} = to_V ` Jneg\<close>
       using pos_all_pos neg_all_neg unfolding fml_Jfin_def by blast 
     moreover have \<open>finite fml_Jfin\<close> using fin_fneg fin_fpos unfolding fml_Jfin_def by blast 
     moreover have \<open>fml_Jfin \<subseteq> fml_ext ` total_strip J\<close>
       using fneg_subs fpos_subs unfolding fml_Jfin_def by blast 
     ultimately show \<open>\<exists>fml_Jfin. finite fml_Jfin \<and> fml_Jfin \<subseteq> fml_ext ` total_strip J \<and>
       {to_V C |C. C \<in> fml_Jfin \<and> is_Pos C} \<union> M \<Turnstile>s {to_V C |C. C \<in> fml_Jfin \<and> \<not> is_Pos C} \<union> N\<close>
       using pos_entails_neg v_to_f_pos v_to_f_neg
       by fastforce
   qed
   have \<open>\<forall>J. \<exists>Jfin. finite Jfin \<and> Jfin \<subseteq> total_strip J \<and>
     {to_V C |C. C \<in> fml_ext ` Jfin \<and> is_Pos C} \<union> M \<Turnstile>s
       {to_V C |C. C \<in> fml_ext ` Jfin \<and> \<not> is_Pos C} \<union> N\<close>
   proof
     fix J
     obtain fml_Jfin where "finite fml_Jfin" and "fml_Jfin \<subseteq> fml_ext ` total_strip J" and
       fml_sound_entails: "{to_V C |C. C \<in> fml_Jfin \<and> is_Pos C} \<union> M \<Turnstile>s
         {to_V C |C. C \<in> fml_Jfin \<and> \<not> is_Pos C} \<union> N"
       using finite_sound_entail_fml_j by blast
     then have \<open>\<exists>Jfin. finite Jfin \<and> Jfin \<subseteq> total_strip J \<and> fml_ext ` Jfin = fml_Jfin\<close>
       by (metis (no_types, hide_lams) finite_subset_image)
     then obtain Jfin where "finite Jfin" and "Jfin \<subseteq> total_strip J" and
       fml_jfin_is: "fml_ext ` Jfin = fml_Jfin"
       by blast
     moreover have \<open>{to_V C |C. C \<in> fml_ext ` Jfin \<and> is_Pos C} \<union> M \<Turnstile>s
       {to_V C |C. C \<in> fml_ext ` Jfin \<and> \<not> is_Pos C} \<union> N\<close>
       using fml_sound_entails fml_jfin_is by blast
     ultimately show \<open>\<exists>Jfin. finite Jfin \<and> Jfin \<subseteq> total_strip J \<and>
       {to_V C |C. C \<in> fml_ext ` Jfin \<and> is_Pos C} \<union> M \<Turnstile>s
         {to_V C |C. C \<in> fml_ext ` Jfin \<and> \<not> is_Pos C} \<union> N\<close>
       by blast 
   qed
   then obtain to_Jfin :: "'v total_interpretation \<Rightarrow> 'v neg set" where
     fin_to_Jfin: "finite (to_Jfin J)" and "(to_Jfin J) \<subseteq> total_strip J" and
     "{to_V C |C. C \<in> fml_ext ` (to_Jfin J) \<and> is_Pos C} \<union> M \<Turnstile>s
       {to_V C |C. C \<in> fml_ext ` (to_Jfin J) \<and> \<not> is_Pos C} \<union> N" for J
     by meson
   define Vfin :: "'v set" where "Vfin = to_V ` (\<Union>J. to_Jfin J)"
   have \<open>finite Vfin\<close>
   proof -
     have \<open>finite  (\<Union>J. to_Jfin J)\<close>
       using fin_to_Jfin sorry (* /!\ I suspect this does not hold /!\ *)
     have \<open>\<forall>J. finite (to_V ` (to_Jfin J))\<close>
     proof
       fix J
       show \<open>finite (to_V ` (to_Jfin J))\<close>
         using finite_imageI[OF fin_to_Jfin, of to_V] by blast
     qed
           
     
      find_theorems finite "\<Union>_. _" 


oops

 (*   have \<open>\<forall>J. \<exists>Jfin. finite (strip Jfin) \<and>
 *      strip Jfin \<subseteq> total_strip J \<and>
 *      {to_V C |C. C \<in> fml_ext ` strip Jfin \<and> is_Pos C} \<union> M \<Turnstile>s
 *        {to_V C |C. C \<in> fml_ext ` strip Jfin \<and> \<not> is_Pos C} \<union> N\<close>
 *    proof
 *      fix J
 *          find_theorems "total_strip _"
 *      obtain Jfin where "{to_V C |C. C \<in> fml_ext ` strip Jfin} = fml_Jpos \<union> fml_Jneg"
 * sorry
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 *    have \<open>\<exists>V. finite V \<and> (\<forall>J. \<exists>Jfin. finite (strip Jfin) \<and>
 *      strip Jfin \<subseteq> total_strip J \<and>
 *      {to_V C |C. C \<in> fml_ext ` strip Jfin \<and> is_Pos C} \<union> M \<Turnstile>s
 *        {to_V C |C. C \<in> fml_ext ` strip Jfin \<and> \<not> is_Pos C} \<union> N \<and>
 *      TODO)\<close>
 * 
 *      
 *      sorry *)



(*   then have \<open>\<exists>J's\<subseteq>total_strip J. finite J's \<and>
 *     {to_V C |C. (C \<in> fml_ext ` J's \<or> C \<in> Pos ` M) \<and> is_Pos C} \<union>
 *     {to_V C |C. C \<in> Pos ` N \<and> \<not> is_Pos C} \<Turnstile>s
 *       {to_V C |C. C \<in> Pos ` N \<and> is_Pos C} \<union>
 *       {to_V C |C. (C \<in> fml_ext ` J's \<or> C \<in> Pos ` M) \<and> \<not> is_Pos C} \<close>
 *     using entails_sound_compact unfolding AF_entails_sound_def sound_cons.entails_neg_def
 *     sorry
 *   have \<open>M \<Turnstile>s N\<close>
 *     unfolding AF_entails_def
 *     sorry
 *       }
 *   moreover {
 *   assume m_to_n: \<open>M \<Turnstile>s N\<close>
 *   have \<open>to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N\<close>
 *     unfolding AF_entails_sound_def sound_cons.entails_neg_def 
 *   proof (simp, rule allI)
 *     fix J
 *     have \<open>M \<subseteq> {to_V C |C. (C \<in> fml_ext ` total_strip J \<or> C \<in> Pos ` M) \<and> is_Pos C}\<close>
 *       by force
 *     then show \<open>{to_V C |C. (C \<in> fml_ext ` total_strip J \<or> C \<in> Pos ` M) \<and> is_Pos C} \<Turnstile>s
 *         N \<union> {to_V C |C. (C \<in> fml_ext ` total_strip J \<or> C \<in> Pos ` M) \<and> \<not> is_Pos C}\<close>
 *       using m_to_n by (meson sound_cons.entails_subsets sup.cobounded1)
 *   qed
 *       }
 *   ultimately show \<open>to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N \<equiv> M \<Turnstile>s N\<close>
 *     by argo
 * qed *)
 
end

end
