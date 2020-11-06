(* Title:        Preliminaries of the Splitting Framework
* Author:       Sophie Tourret <stourret at mpi-inf.mpg.de>, 2020 *)

theory Preliminaries
  imports Saturation_Framework.Calculus
  (* Finite_Set *)
begin
  
  (* formalizing negated formulas uncovered a mistake in the corresponding paper-definition *)
datatype 'f neg = Pos "'f" | Neg "'f neg" (* ("\<sim>_" 55) (*| Pos (nval_of: "'f neg") *) term "\<sim>F" *)

fun to_F :: "'f neg \<Rightarrow> 'f" where
  "to_F (Pos C) = C" |
  "to_F (Neg C) = to_F C"
  (* "to_F (Pos C) = to_F C" |*)
  
fun simplify_Neg :: "'f neg \<Rightarrow> 'f neg" where
  "simplify_Neg (Pos C) = Pos C" |
  "simplify_Neg (Neg (Pos C)) = Neg (Pos C)" |
  "simplify_Neg (Neg (Neg C)) = simplify_Neg C"

fun has_Pos_const :: "'f neg \<Rightarrow> bool" where 
  "has_Pos_const (Pos C) = True" |
  "has_Pos_const (Neg C) = False"
  
fun is_Pos :: "'f neg \<Rightarrow> bool" where
  "is_Pos (Pos C) = True" |
  "is_Pos (Neg C) = (\<not>(is_Pos C))"

lemma \<open>is_Pos C \<Longrightarrow> is_Pos (simplify_Neg C)\<close>
proof (induct C rule: simplify_Neg.induct)
  case (1 Ca)
  then show "is_Pos (simplify_Neg (Pos Ca))" by simp
next
  case (2 Ca)
  then have "False" by simp
  then show \<open>is_Pos (simplify_Neg (Neg (Pos Ca)))\<close> by blast
next
  case (3 Ca)
oops    

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
  "entails_neg M N \<equiv>
    {C. Pos C \<in> simplify_Neg ` M} \<union> {to_F C |C. Neg C \<in> simplify_Neg ` N} \<Turnstile>
      {C. Pos C \<in> simplify_Neg ` N} \<union> {to_F C |C. Neg C \<in> simplify_Neg ` M} "

definition entails_neg2 :: "'f neg set \<Rightarrow> 'f neg set \<Rightarrow> bool" where
  "entails_neg2 M N \<equiv>
    {to_F C |C. C \<in> M \<and> is_Pos C} \<union> {to_F C |C. C \<in> N \<and> \<not> is_Pos C} \<Turnstile>
      {to_F C |C. C \<in> N \<and> is_Pos C} \<union> {to_F C |C. C \<in> M \<and> \<not> is_Pos C} "
  
sublocale ext_cons_rel2: consequence_relation "Pos bot" entails_neg2
proof
  show "entails_neg2 {Pos bot} {}"
    unfolding entails_neg2_def using bot_entails_empty by simp
next
  fix C
  show \<open>entails_neg2 {C} {C}\<close>
    unfolding entails_neg2_def using entails_cond_reflexive by auto
next
  fix M N P Q
  assume
    subs1: "M \<subseteq> N" and
    subs2: "P \<subseteq> Q" and
    entails1: "entails_neg2 M P"
  have union_subs1: \<open>{to_F C |C. C \<in> M \<and> is_Pos C} \<union> {to_F C |C. C \<in> P \<and> \<not> is_Pos C} \<subseteq>
    {to_F C |C. C \<in> N \<and> is_Pos C} \<union> {to_F C |C. C \<in> Q \<and> \<not> is_Pos C}\<close>
    using subs1 subs2 by auto
  have union_subs2: \<open>{to_F C |C. C \<in> P \<and> is_Pos C} \<union> {to_F C |C. C \<in> M \<and> \<not> is_Pos C} \<subseteq>
    {to_F C |C. C \<in> Q \<and> is_Pos C} \<union> {to_F C |C. C \<in> N \<and> \<not> is_Pos C}\<close>
    using subs1 subs2 by auto
  have union_entails1: "{to_F C |C. C \<in> M \<and> is_Pos C} \<union> {to_F C |C. C \<in> P \<and> \<not> is_Pos C} \<Turnstile>
    {to_F C |C. C \<in> P \<and> is_Pos C} \<union> {to_F C |C. C \<in> M \<and> \<not> is_Pos C}"
    using entails1 unfolding entails_neg2_def .
  show \<open>entails_neg2 N Q\<close>
    using entails_subsets[OF union_subs1 union_subs2 union_entails1] unfolding entails_neg2_def .
next
    oops
  
sublocale ext_cons_rel: consequence_relation "Pos bot" entails_neg
proof
  show "entails_neg {Pos bot} {}"
    unfolding entails_neg_def using bot_entails_empty by simp
next
  fix C
  show \<open>entails_neg {C} {C}\<close>
  proof (cases "is_Pos C")
    case True
    then obtain D where "simplify_Neg C = Pos D" using simplify_Neg.elims 

      oops

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
    Red_F_Bot: "N \<Turnstile> {bot} \<Longrightarrow> N - Red_F N \<Turnstile> {}" and (* /!\ check if this is ok *)
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

lemma \<open>bot \<notin> Red_F N\<close>
proof -
  have \<open>saturated UNIV\<close>
    unfolding saturated_def Inf_from_def by (simp add: Red_I_of_Inf_to_N subsetI)
  have \<open>UNIV \<Turnstile> {bot}\<close>
    using entails_reflexive[of bot] entails_subsets[of "{bot}" UNIV "{bot}" "{bot}"] by fast
  have \<open>bot \<notin> Red_F UNIV\<close> sorry
  then show ?thesis using Red_F_of_subset[of _ UNIV] by auto
qed

end


end
    