(* Title:        Preliminaries of the Splitting Framework
* Author:       Sophie Tourret <stourret at mpi-inf.mpg.de>, 2020 *)

theory Preliminaries
  imports Saturation_Framework.Calculus
  (* Finite_Set *)
begin
  
  (* formalizing negated formulas uncovered a mistake in the corresponding paper-definition
  (sect. 2.1 *)
datatype 'f neg = Pos "'f" | Neg "'f neg" (* ("\<sim>_" 55) (*| Pos (nval_of: "'f neg") *) term "\<sim>F" *)

fun to_F :: "'f neg \<Rightarrow> 'f" where
  "to_F (Pos C) = C" |
  "to_F (Neg C) = to_F C"

fun is_Pos :: "'f neg \<Rightarrow> bool" where
  "is_Pos (Pos C) = True" |
  "is_Pos (Neg C) = (\<not>(is_Pos C))"

locale consequence_relation =
  fixes
    bot :: "'f" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  assumes
    bot_entails_empty: "{bot} \<Turnstile> {}" and
    entails_reflexive: "{C} \<Turnstile> {C}" and
    entails_subsets: "M \<subseteq> N \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> M \<Turnstile> P \<Longrightarrow> N \<Turnstile> Q" and
    entails_each: "M \<Turnstile> P \<Longrightarrow> \<forall>C\<in>M. N \<Turnstile> Q \<union> {C} \<Longrightarrow> \<forall>D\<in>P. N \<union> {D} \<Turnstile> Q \<Longrightarrow> N \<Turnstile> Q"
    (* this was an earlier version of entails_each: "M \<Turnstile> N \<Longrightarrow> (\<forall>D\<in>N. M \<union> {D} \<Turnstile> P) \<Longrightarrow> M \<Turnstile> P"
    it was detected to be unsufficient thanks to the forma*)
begin

abbreviation equi_entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>|" 50) where
  "M \<Turnstile>| N \<equiv> (M \<Turnstile> N \<and> N \<Turnstile> M)"

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

definition entails_neg :: "'f neg set \<Rightarrow> 'f neg set \<Rightarrow> bool" where
  "entails_neg M N \<equiv> {to_F C |C. C \<in> M \<and> is_Pos C} \<union> {to_F C |C. C \<in> N \<and> \<not> is_Pos C} \<Turnstile>
      {to_F C |C. C \<in> N \<and> is_Pos C} \<union> {to_F C |C. C \<in> M \<and> \<not> is_Pos C} "
  
interpretation ext_cons_rel2: consequence_relation "Pos bot" entails_neg
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
  have union_subs1: \<open>{to_F C |C. C \<in> M \<and> is_Pos C} \<union> {to_F C |C. C \<in> P \<and> \<not> is_Pos C} \<subseteq>
    {to_F C |C. C \<in> N \<and> is_Pos C} \<union> {to_F C |C. C \<in> Q \<and> \<not> is_Pos C}\<close>
    using subs1 subs2 by auto
  have union_subs2: \<open>{to_F C |C. C \<in> P \<and> is_Pos C} \<union> {to_F C |C. C \<in> M \<and> \<not> is_Pos C} \<subseteq>
    {to_F C |C. C \<in> Q \<and> is_Pos C} \<union> {to_F C |C. C \<in> N \<and> \<not> is_Pos C}\<close>
    using subs1 subs2 by auto
  have union_entails1: "{to_F C |C. C \<in> M \<and> is_Pos C} \<union> {to_F C |C. C \<in> P \<and> \<not> is_Pos C} \<Turnstile>
    {to_F C |C. C \<in> P \<and> is_Pos C} \<union> {to_F C |C. C \<in> M \<and> \<not> is_Pos C}"
    using entails1 unfolding entails_neg_def .
  show \<open>entails_neg N Q\<close>
    using entails_subsets[OF union_subs1 union_subs2 union_entails1] unfolding entails_neg_def .
next
  fix M P N Q
  assume
    D4_hyp1: "entails_neg M P" and
    n_to_qm: "\<forall>C\<in>M. entails_neg N (Q \<union> {C})" and
    np_to_q: "\<forall>D\<in>P. entails_neg (N \<union> {D}) Q"
  define NpQm where "NpQm = {to_F C |C. C \<in> N \<and> is_Pos C} \<union> {to_F C |C. C \<in> Q \<and> \<not> is_Pos C}"
  define NmQp where "NmQp = {to_F C |C. C \<in> Q \<and> is_Pos C} \<union> {to_F C |C. C \<in> N \<and> \<not> is_Pos C}"
  define MpPm where "MpPm = {to_F C |C. C \<in> M \<and> is_Pos C} \<union> {to_F C |C. C \<in> P \<and> \<not> is_Pos C}"
  define MmPp where "MmPp = {to_F C |C. C \<in> P \<and> is_Pos C} \<union> {to_F C |C. C \<in> M \<and> \<not> is_Pos C}"
    
  have "Cn \<in> M \<Longrightarrow> is_Pos Cn \<Longrightarrow>
    {to_F Ca |Ca. Ca \<in> Q \<union> {Cn} \<and> \<not> is_Pos Ca} = {to_F Ca |Ca. Ca \<in> Q \<and> \<not> is_Pos Ca}" for Cn
    by blast
  also have "Cn \<in> M \<Longrightarrow> is_Pos Cn \<Longrightarrow> {to_F Ca |Ca. Ca \<in> Q \<union> {Cn} \<and> is_Pos Ca} =
    {to_F Ca |Ca. Ca \<in> Q \<and> is_Pos Ca} \<union> {to_F Cn}" for Cn
    by blast
  ultimately have m_pos: \<open>Cn \<in> M \<Longrightarrow> is_Pos Cn \<Longrightarrow> NpQm \<Turnstile> NmQp \<union> {to_F Cn}\<close> for Cn
    using n_to_qm unfolding entails_neg_def NpQm_def NmQp_def by force
  have entails_m_pos: \<open>\<forall>C\<in>{to_F C |C. C \<in> M \<and> is_Pos C}. NpQm \<Turnstile> NmQp \<union> {C}\<close>
  proof
    fix C
    assume "C \<in> {to_F C |C. C \<in> M \<and> is_Pos C}"
    then obtain Ca where "to_F Ca = C" "Ca \<in> M" "is_Pos Ca" by blast
    then show "NpQm \<Turnstile> NmQp \<union> {C}"
      using m_pos[of Ca] by blast
  qed
    
  have "Cn \<in> P \<Longrightarrow> \<not> is_Pos Cn \<Longrightarrow> {to_F Ca |Ca. Ca \<in> N \<union> {Cn} \<and> \<not> is_Pos Ca} =
    {to_F Ca |Ca. Ca \<in> N \<and> \<not> is_Pos Ca} \<union> {to_F Cn}" for Cn
    by blast
  also have "Cn \<in> P \<Longrightarrow> \<not> is_Pos Cn \<Longrightarrow>
    {to_F Ca |Ca. Ca \<in> N \<union> {Cn} \<and> is_Pos Ca} = {to_F Ca |Ca. Ca \<in> N \<and> is_Pos Ca}" for Cn
    by blast
  ultimately have p_neg: \<open>Cn \<in> P \<Longrightarrow> \<not> is_Pos Cn \<Longrightarrow> NpQm \<Turnstile> NmQp \<union> {to_F Cn}\<close> for Cn
    using np_to_q unfolding entails_neg_def NpQm_def NmQp_def by force
  have entails_p_neg: \<open>\<forall>C\<in>{to_F C |C. C \<in> P \<and> \<not> is_Pos C}. NpQm \<Turnstile> NmQp \<union> {C}\<close>
  proof
    fix C
    assume "C \<in> {to_F C |C. C \<in> P \<and> \<not> is_Pos C}"
    then obtain Ca where "to_F Ca = C" "Ca \<in> P" "\<not> is_Pos Ca" by blast
    then show "NpQm \<Turnstile> NmQp \<union> {C}"
      using p_neg[of Ca] by blast
  qed

  have D4_hyp2: \<open>\<forall>C\<in>MpPm. NpQm \<Turnstile> NmQp \<union> {C}\<close>
    using entails_m_pos entails_p_neg unfolding MpPm_def by fast
      
  have "Cn \<in> M \<Longrightarrow> \<not> is_Pos Cn \<Longrightarrow> {to_F Ca |Ca. Ca \<in> Q \<union> {Cn} \<and> \<not> is_Pos Ca} =
    {to_F Ca |Ca. Ca \<in> Q \<and> \<not> is_Pos Ca} \<union> {to_F Cn}" for Cn
    by blast
  also have "Cn \<in> M \<Longrightarrow> \<not> is_Pos Cn \<Longrightarrow>
    {to_F Ca |Ca. Ca \<in> Q \<union> {Cn} \<and> is_Pos Ca} = {to_F Ca |Ca. Ca \<in> Q \<and> is_Pos Ca}" for Cn
    by blast
  ultimately have m_neg: \<open>Cn \<in> M \<Longrightarrow> \<not> is_Pos Cn \<Longrightarrow> NpQm  \<union> {to_F Cn} \<Turnstile> NmQp\<close> for Cn
    using n_to_qm unfolding entails_neg_def NpQm_def NmQp_def by force
  have entails_m_neg: \<open>\<forall>C\<in>{to_F C |C. C \<in> M \<and> \<not> is_Pos C}. NpQm \<union> {C} \<Turnstile> NmQp\<close>
  proof
    fix C
    assume "C \<in> {to_F C |C. C \<in> M \<and> \<not> is_Pos C}"
    then obtain Ca where "to_F Ca = C" "Ca \<in> M" "\<not> is_Pos Ca" by blast
    then show "NpQm \<union> {C} \<Turnstile> NmQp"
      using m_neg[of Ca] by blast
  qed
    
  have "Cn \<in> P \<Longrightarrow> is_Pos Cn \<Longrightarrow> {to_F Ca |Ca. Ca \<in> N \<union> {Cn} \<and> \<not> is_Pos Ca} =
    {to_F Ca |Ca. Ca \<in> N \<and> \<not> is_Pos Ca}" for Cn
    by blast
  also have "Cn \<in> P \<Longrightarrow> is_Pos Cn \<Longrightarrow> {to_F Ca |Ca. Ca \<in> N \<union> {Cn} \<and> is_Pos Ca} =
    {to_F Ca |Ca. Ca \<in> N \<and> is_Pos Ca} \<union> {to_F Cn}" for Cn
    by blast
  ultimately have p_pos: \<open>Cn \<in> P \<Longrightarrow> is_Pos Cn \<Longrightarrow> NpQm \<union> {to_F Cn} \<Turnstile> NmQp\<close> for Cn
    using np_to_q unfolding entails_neg_def NpQm_def NmQp_def by force
  have entails_p_pos: \<open>\<forall>C\<in>{to_F C |C. C \<in> P \<and> is_Pos C}. NpQm \<union> {C} \<Turnstile> NmQp\<close>
  proof
    fix C
    assume "C \<in> {to_F C |C. C \<in> P \<and> is_Pos C}"
    then obtain Ca where "to_F Ca = C" "Ca \<in> P" "is_Pos Ca" by blast
    then show "NpQm \<union> {C} \<Turnstile> NmQp"
      using p_pos[of Ca] by blast
  qed

  have D4_hyp3: \<open>\<forall>C\<in>MmPp. NpQm \<union> {C} \<Turnstile> NmQp\<close>
    using entails_m_neg entails_p_pos unfolding MmPp_def by fast

  show "entails_neg N Q"
    using entails_each[OF _ D4_hyp2 D4_hyp3] D4_hyp1
    unfolding entails_neg_def MpPm_def MmPp_def NpQm_def NmQp_def
    by blast
qed

end
   


locale sound_inference_system = inference_system Inf + consequence_relation bot entails_sound
  for
    Inf :: "'f inference set" and
    bot :: "'f" and
    entails_sound :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>s" 50)
  + assumes
    sound: "\<iota> \<in> Inf \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s {concle_of \<iota>}"
    

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

end
  
locale statically_complete_calculus = calculus +
  assumes statically_complete: "saturated N \<Longrightarrow> N \<Turnstile> {bot} \<Longrightarrow> bot \<in> N"
begin

lemma inf_from_subs: "M \<subseteq> N \<Longrightarrow> Inf_from M \<subseteq> Inf_from N"
  unfolding Inf_from_def by blast

lemma \<open>bot \<notin> Red_F N\<close>
proof -
  (* first "have" is not needed, TODO: remove here and in paper proof *)
  have \<open>saturated UNIV\<close>
    unfolding saturated_def Inf_from_def by (simp add: Red_I_of_Inf_to_N subsetI)
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

end


end
    