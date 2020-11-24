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

fun is_Pos :: "'a neg \<Rightarrow> bool" where
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
  "entails_neg M N \<equiv> {to_V C |C. C \<in> M \<and> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> \<not> is_Pos C} \<Turnstile>
      {to_V C |C. C \<in> N \<and> is_Pos C} \<union> {to_V C |C. C \<in> M \<and> \<not> is_Pos C} "
  
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
  fix M P N Q
  assume
    D4_hyp1: "entails_neg M P" and
    n_to_qm: "\<forall>C\<in>M. entails_neg N (Q \<union> {C})" and
    np_to_q: "\<forall>D\<in>P. entails_neg (N \<union> {D}) Q"
  define NpQm where "NpQm = {to_V C |C. C \<in> N \<and> is_Pos C} \<union> {to_V C |C. C \<in> Q \<and> \<not> is_Pos C}"
  define NmQp where "NmQp = {to_V C |C. C \<in> Q \<and> is_Pos C} \<union> {to_V C |C. C \<in> N \<and> \<not> is_Pos C}"
  define MpPm where "MpPm = {to_V C |C. C \<in> M \<and> is_Pos C} \<union> {to_V C |C. C \<in> P \<and> \<not> is_Pos C}"
  define MmPp where "MmPp = {to_V C |C. C \<in> P \<and> is_Pos C} \<union> {to_V C |C. C \<in> M \<and> \<not> is_Pos C}"
    
  have "Cn \<in> M \<Longrightarrow> is_Pos Cn \<Longrightarrow>
    {to_V Ca |Ca. Ca \<in> Q \<union> {Cn} \<and> \<not> is_Pos Ca} = {to_V Ca |Ca. Ca \<in> Q \<and> \<not> is_Pos Ca}" for Cn
    by blast
  also have "Cn \<in> M \<Longrightarrow> is_Pos Cn \<Longrightarrow> {to_V Ca |Ca. Ca \<in> Q \<union> {Cn} \<and> is_Pos Ca} =
    {to_V Ca |Ca. Ca \<in> Q \<and> is_Pos Ca} \<union> {to_V Cn}" for Cn
    by blast
  ultimately have m_pos: \<open>Cn \<in> M \<Longrightarrow> is_Pos Cn \<Longrightarrow> NpQm \<Turnstile> NmQp \<union> {to_V Cn}\<close> for Cn
    using n_to_qm unfolding entails_neg_def NpQm_def NmQp_def by force
  have entails_m_pos: \<open>\<forall>C\<in>{to_V C |C. C \<in> M \<and> is_Pos C}. NpQm \<Turnstile> NmQp \<union> {C}\<close>
  proof
    fix C
    assume "C \<in> {to_V C |C. C \<in> M \<and> is_Pos C}"
    then obtain Ca where "to_V Ca = C" "Ca \<in> M" "is_Pos Ca" by blast
    then show "NpQm \<Turnstile> NmQp \<union> {C}"
      using m_pos[of Ca] by blast
  qed
    
  have "Cn \<in> P \<Longrightarrow> \<not> is_Pos Cn \<Longrightarrow> {to_V Ca |Ca. Ca \<in> N \<union> {Cn} \<and> \<not> is_Pos Ca} =
    {to_V Ca |Ca. Ca \<in> N \<and> \<not> is_Pos Ca} \<union> {to_V Cn}" for Cn
    by blast
  also have "Cn \<in> P \<Longrightarrow> \<not> is_Pos Cn \<Longrightarrow>
    {to_V Ca |Ca. Ca \<in> N \<union> {Cn} \<and> is_Pos Ca} = {to_V Ca |Ca. Ca \<in> N \<and> is_Pos Ca}" for Cn
    by blast
  ultimately have p_neg: \<open>Cn \<in> P \<Longrightarrow> \<not> is_Pos Cn \<Longrightarrow> NpQm \<Turnstile> NmQp \<union> {to_V Cn}\<close> for Cn
    using np_to_q unfolding entails_neg_def NpQm_def NmQp_def by force
  have entails_p_neg: \<open>\<forall>C\<in>{to_V C |C. C \<in> P \<and> \<not> is_Pos C}. NpQm \<Turnstile> NmQp \<union> {C}\<close>
  proof
    fix C
    assume "C \<in> {to_V C |C. C \<in> P \<and> \<not> is_Pos C}"
    then obtain Ca where "to_V Ca = C" "Ca \<in> P" "\<not> is_Pos Ca" by blast
    then show "NpQm \<Turnstile> NmQp \<union> {C}"
      using p_neg[of Ca] by blast
  qed

  have D4_hyp2: \<open>\<forall>C\<in>MpPm. NpQm \<Turnstile> NmQp \<union> {C}\<close>
    using entails_m_pos entails_p_neg unfolding MpPm_def by fast
      
  have "Cn \<in> M \<Longrightarrow> \<not> is_Pos Cn \<Longrightarrow> {to_V Ca |Ca. Ca \<in> Q \<union> {Cn} \<and> \<not> is_Pos Ca} =
    {to_V Ca |Ca. Ca \<in> Q \<and> \<not> is_Pos Ca} \<union> {to_V Cn}" for Cn
    by blast
  also have "Cn \<in> M \<Longrightarrow> \<not> is_Pos Cn \<Longrightarrow>
    {to_V Ca |Ca. Ca \<in> Q \<union> {Cn} \<and> is_Pos Ca} = {to_V Ca |Ca. Ca \<in> Q \<and> is_Pos Ca}" for Cn
    by blast
  ultimately have m_neg: \<open>Cn \<in> M \<Longrightarrow> \<not> is_Pos Cn \<Longrightarrow> NpQm  \<union> {to_V Cn} \<Turnstile> NmQp\<close> for Cn
    using n_to_qm unfolding entails_neg_def NpQm_def NmQp_def by force
  have entails_m_neg: \<open>\<forall>C\<in>{to_V C |C. C \<in> M \<and> \<not> is_Pos C}. NpQm \<union> {C} \<Turnstile> NmQp\<close>
  proof
    fix C
    assume "C \<in> {to_V C |C. C \<in> M \<and> \<not> is_Pos C}"
    then obtain Ca where "to_V Ca = C" "Ca \<in> M" "\<not> is_Pos Ca" by blast
    then show "NpQm \<union> {C} \<Turnstile> NmQp"
      using m_neg[of Ca] by blast
  qed
    
  have "Cn \<in> P \<Longrightarrow> is_Pos Cn \<Longrightarrow> {to_V Ca |Ca. Ca \<in> N \<union> {Cn} \<and> \<not> is_Pos Ca} =
    {to_V Ca |Ca. Ca \<in> N \<and> \<not> is_Pos Ca}" for Cn
    by blast
  also have "Cn \<in> P \<Longrightarrow> is_Pos Cn \<Longrightarrow> {to_V Ca |Ca. Ca \<in> N \<union> {Cn} \<and> is_Pos Ca} =
    {to_V Ca |Ca. Ca \<in> N \<and> is_Pos Ca} \<union> {to_V Cn}" for Cn
    by blast
  ultimately have p_pos: \<open>Cn \<in> P \<Longrightarrow> is_Pos Cn \<Longrightarrow> NpQm \<union> {to_V Cn} \<Turnstile> NmQp\<close> for Cn
    using np_to_q unfolding entails_neg_def NpQm_def NmQp_def by force
  have entails_p_pos: \<open>\<forall>C\<in>{to_V C |C. C \<in> P \<and> is_Pos C}. NpQm \<union> {C} \<Turnstile> NmQp\<close>
  proof
    fix C
    assume "C \<in> {to_V C |C. C \<in> P \<and> is_Pos C}"
    then obtain Ca where "to_V Ca = C" "Ca \<in> P" "is_Pos Ca" by blast
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
  
locale statically_complete_calculus = calculus +
  assumes statically_complete: "saturated N \<Longrightarrow> N \<Turnstile> {bot} \<Longrightarrow> bot \<in> N"
begin

lemma inf_from_subs: "M \<subseteq> N \<Longrightarrow> Inf_from M \<subseteq> Inf_from N"
  unfolding Inf_from_def by blast

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
datatype ('f, 'v::countable) AF = Pair (F_of: "'f") (A_of: "'v neg set")

definition is_interpretation :: "'v neg set \<Rightarrow> bool" where
  \<open>is_interpretation J = (\<forall>v1\<in>J. (\<forall>v2\<in>J. (to_V v1 = to_V v2 \<longrightarrow> is_Pos v1 = is_Pos v2)))\<close>

definition to_AF :: "'f \<Rightarrow> ('f, 'v::countable) AF" where
  \<open>to_AF C = Pair C {}\<close>

(* definition enabled :: "('f, 'v::countable) AF \<Rightarrow> 'v neg set \<Rightarrow> bool" where
 *   \<open>enabled C J = ((A_of C) \<subseteq> J \<or> (F_of C = bot \<and> True))\<close> *)

end
