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
    entails_each: "M \<Turnstile> P \<Longrightarrow> \<forall>C\<in>M. N \<Turnstile> Q \<union> {C} \<Longrightarrow> \<forall>D\<in>P. N \<union> {D} \<Turnstile> Q \<Longrightarrow> N \<Turnstile> Q"
    (* this was an earlier version of entails_each: "M \<Turnstile> N \<Longrightarrow> (\<forall>D\<in>N. M \<union> {D} \<Turnstile> P) \<Longrightarrow> M \<Turnstile> P"
    it was detected to be unsufficient thanks to the forma*)
begin

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
  (* assumes
    j_is: \<open>\<J> = {J. is_interpretation J}\<close>*)
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
  fix M P N Q
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
    then have each_hyp2: \<open>\<forall>C\<in>F_of ` M\<^sub>J. {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J} \<Turnstile> F_of ` Q \<union> {C}\<close>
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
  qed
qed

  find_theorems name: entails_neg
  
  (* duplicated from the consequence_relation locale because it can't be a sublocale *)
interpretation ext_cons_rel_sound: consequence_relation "Pos bot" AF_cons_rel.entails_neg
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


interpretation sound_cons_rel: consequence_relation "Pos bot" sound_cons.entails_neg
  using sound_cons.ext_cons_rel .
    
    find_theorems name: sound_cons_rel name: entails
  
interpretation AF_sound_cons_rel: consequence_relation "to_AF bot" AF_entails_sound
proof
  have \<open>{Pos bot} \<subseteq> Pos ` {F_of C |C. C \<in> {to_AF bot} \<and> A_of C \<subseteq> total_strip J}\<close>
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
  then show \<open>{C} \<Turnstile>s\<^sub>A\<^sub>F {C}\<close>
    unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
    using sound_cons_rel.entails_reflexive sound_cons_rel.entails_subsets 
      by (smt (z3) UnCI empty_is_image imageE image_eqI image_insert mem_Collect_eq subsetI)
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
    have \<open>{F_of C |C. C \<in> M \<and> A_of C \<subseteq> total_strip J} \<subseteq> {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J}\<close>
      using m_in_n by blast
    moreover have \<open>F_of ` P \<subseteq> F_of ` Q\<close>
      using p_in_q by blast
    ultimately show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union>
      Pos ` {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J}) (Pos ` F_of ` Q)\<close>
      using m_entails_p  sound_cons_rel.entails_subsets
      unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
       proof - (* suggested by sledgehammer but not terminating *)
    assume a1: "\<forall>J. (\<forall>C\<in>P. A_of C \<subseteq> total_strip J) \<longrightarrow> sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` {F_of C |C. C \<in> M \<and> A_of C \<subseteq> total_strip J}) (Pos ` F_of ` P)"
    have f2: "(v2_16 (fml_ext ` total_strip J \<union> Pos ` {F_of a |a. a \<in> N \<and> A_of a \<subseteq> total_strip J}) (fml_ext ` total_strip J \<union> Pos ` {F_of a |a. a \<in> M \<and> A_of a \<subseteq> total_strip J}) \<notin> fml_ext ` total_strip J \<union> Pos ` {F_of a |a. a \<in> M \<and> A_of a \<subseteq> total_strip J} \<or> v2_16 (fml_ext ` total_strip J \<union> Pos ` {F_of a |a. a \<in> N \<and> A_of a \<subseteq> total_strip J}) (fml_ext ` total_strip J \<union> Pos ` {F_of a |a. a \<in> M \<and> A_of a \<subseteq> total_strip J}) \<in> fml_ext ` total_strip J \<union> Pos ` {F_of a |a. a \<in> N \<and> A_of a \<subseteq> total_strip J}) \<or> v2_16 (fml_ext ` total_strip J \<union> Pos ` {F_of a |a. a \<in> N \<and> A_of a \<subseteq> total_strip J}) (fml_ext ` total_strip J \<union> Pos ` {F_of a |a. a \<in> M \<and> A_of a \<subseteq> total_strip J}) \<in> Pos ` {F_of a |a. a \<in> M \<and> A_of a \<subseteq> total_strip J}"
      by force
    obtain ff :: "'f set \<Rightarrow> 'f set \<Rightarrow> 'f" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (ff x0 x1 \<in> x1 \<and> ff x0 x1 \<notin> x0)"
      by moura
    then have f3: "\<forall>F Fa. (\<not> F \<subseteq> Fa \<or> (\<forall>f. f \<notin> F \<or> f \<in> Fa)) \<and> (F \<subseteq> Fa \<or> ff Fa F \<in> F \<and> ff Fa F \<notin> Fa)"
      by blast
    obtain nn :: "'f neg set \<Rightarrow> 'f neg set \<Rightarrow> 'f neg" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (nn x0 x1 \<in> x1 \<and> nn x0 x1 \<notin> x0)"
      by moura
    then have f4: "\<forall>N Na. (\<not> N \<subseteq> Na \<or> (\<forall>n. n \<notin> N \<or> n \<in> Na)) \<and> (N \<subseteq> Na \<or> nn Na N \<in> N \<and> nn Na N \<notin> Na)"
      by blast
    have f5: "Pos ` F_of ` P \<subseteq> Pos ` F_of ` Q"
      using f3 \<open>F_of ` P \<subseteq> F_of ` Q\<close> by force
    obtain aa :: "'v total_interpretation \<Rightarrow> ('f, 'v) AF" where
      f6: "\<forall>t. aa t \<in> P \<and> \<not> A_of (aa t) \<subseteq> total_strip t \<or> sound_cons.entails_neg (fml_ext ` total_strip t \<union> Pos ` {F_of a |a. a \<in> M \<and> A_of a \<subseteq> total_strip t}) (Pos ` F_of ` P)"
      using a1 by meson
    have f7: "\<forall>a. a \<notin> P \<or> a \<in> Q"
      using p_in_q by auto
    have "\<forall>f. f \<notin> {F_of a |a. a \<in> M \<and> A_of a \<subseteq> total_strip J} \<or> f \<in> {F_of a |a. a \<in> N \<and> A_of a \<subseteq> total_strip J}"
      using f3 \<open>{F_of C |C. C \<in> M \<and> A_of C \<subseteq> total_strip J} \<subseteq> {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J}\<close> by presburger
    then have "fml_ext ` total_strip J \<union> Pos ` {F_of a |a. a \<in> M \<and> A_of a \<subseteq> total_strip J} \<subseteq> fml_ext ` total_strip J \<union> Pos ` {F_of a |a. a \<in> N \<and> A_of a \<subseteq> total_strip J}"
      using f4 f2 sorry
    then show ?thesis
      using f7 f6 f5 by (meson consequence_relation.entails_subsets q_enabled sound_cons_rel.consequence_relation_axioms)
  qed 
        (* by (metis (mono_tags, lifting) q_enabled p_in_q subset_iff) *)
        sorry
  qed










































next
  fix M P N Q
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
    then have each_hyp2: \<open>\<forall>C\<in>F_of ` M\<^sub>J. {F_of C |C. C \<in> N \<and> A_of C \<subseteq> total_strip J} \<Turnstile> F_of ` Q \<union> {C}\<close>
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
  qed
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

(* lemma entails_bot_to_entails_empty: \<open>{} \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<Longrightarrow> {} \<Turnstile>\<^sub>A\<^sub>F {}\<close>
 *   unfolding AF_entails_def 
 * proof simp
 *   assume \<open>\<forall>J. enabled_set {to_AF bot} J \<longrightarrow> {} proj\<^sub>J J \<Turnstile> {F_of (to_AF bot)}\<close>
 *   then have \<open>{} \<Turnstile> {bot}\<close>
 *     unfolding enabled_set_def enabled_def by (simp add: enabled_projection_def to_AF_def)
 *   then have empty_entails_empty: \<open>{} \<Turnstile> {}\<close>
 *     using entails_reflexive[of bot] entails_each[of "{}" "{bot}" "{}" "{}"] bot_entails_empty
 *     by auto
 *   then show \<open>\<forall>J. enabled_set {} J \<longrightarrow> {} proj\<^sub>J J \<Turnstile> {}\<close>
 *     using entails_empty_reflexive_dangerous by simp
 * qed *)


lemma entails_in_sound_entails_for_prop_clauses:
  \<open>\<not> {} \<Turnstile>\<^sub>A\<^sub>F {} \<Longrightarrow> proj\<^sub>\<bottom> C\<^sub>1 \<Turnstile>\<^sub>A\<^sub>F proj\<^sub>\<bottom> C\<^sub>2 \<Longrightarrow> proj\<^sub>\<bottom> C\<^sub>1 \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> C\<^sub>2\<close>
proof -
  assume
    entails_useful: \<open>\<not> {} \<Turnstile>\<^sub>A\<^sub>F {}\<close> and
    entails_nonsound: \<open>proj\<^sub>\<bottom> C\<^sub>1 \<Turnstile>\<^sub>A\<^sub>F proj\<^sub>\<bottom> C\<^sub>2\<close>
  show \<open>proj\<^sub>\<bottom> C\<^sub>1 \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> C\<^sub>2\<close>
    unfolding AF_entails_sound_def 
  proof
    fix J
    show \<open>enabled_set (proj\<^sub>\<bottom> C\<^sub>2) J \<longrightarrow> sound_cons.entails_neg
      (fml_ext ` total_strip J \<union> Pos ` (proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J)) (Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2)\<close>
    proof
      assume enabled_c2: \<open>enabled_set (proj\<^sub>\<bottom> C\<^sub>2) J\<close>
      have \<open>F_of ` proj\<^sub>\<bottom> C\<^sub>1 = {} \<or> F_of ` proj\<^sub>\<bottom> C\<^sub>1 = {bot}\<close>
        unfolding propositional_projection_def enabled_projection_def by force
      then have \<open>(proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J) = {bot}\<close>
        (* unfolding enabled_projection_def using AF_entails.entails_bot_to_entails_empty *)
        sorry
      then have \<open>{C. C \<in> Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 \<and> \<not> is_Pos C} = {}\<close>
        by auto
      have \<open>Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {} \<or> Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {Pos bot}\<close>
        unfolding propositional_projection_def enabled_projection_def by force
      then have \<open>{C. C \<in> Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 \<and> \<not> is_Pos C} = {}\<close>
        by auto

      show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J))
        (Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2)\<close>
        unfolding sound_cons.entails_neg_def
    oops
      


(* lemma entails_in_sound_entails_for_prop_clauses:
 *   \<open>\<not> {} \<Turnstile>\<^sub>A\<^sub>F {} \<Longrightarrow> proj\<^sub>\<bottom> C\<^sub>1 \<Turnstile>\<^sub>A\<^sub>F proj\<^sub>\<bottom> C\<^sub>2 \<Longrightarrow> proj\<^sub>\<bottom> C\<^sub>1 \<Turnstile>s\<^sub>A\<^sub>F proj\<^sub>\<bottom> C\<^sub>2\<close>
 *   unfolding AF_entails_sound_def AF_entails_def sound_cons.entails_neg_def
 * proof 
 *   fix J
 *   assume
 *     not_useless: \<open>\<not> {} \<Turnstile>\<^sub>A\<^sub>F {}\<close> and
 *     entails_AF: \<open>\<forall>J. enabled_set (proj\<^sub>\<bottom> C\<^sub>2) J \<longrightarrow> proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J \<Turnstile> F_of ` proj\<^sub>\<bottom> C\<^sub>2\<close>
 *   have simp_c2: \<open>F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {} \<or> F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {bot}\<close>
 *     unfolding propositional_projection_def enabled_projection_def by force
 *   have simp_entails_AF: \<open>proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J \<Turnstile> F_of ` proj\<^sub>\<bottom> C\<^sub>2\<close>
 *     using simp_c2 entails_AF unfolding enabled_set_def enabled_def 
 *   have simp_c1: \<open>proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J = {} \<or> proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J = {bot}\<close> 
 *     unfolding propositional_projection_def enabled_projection_def by force
 *   then have terrible: \<open>proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J = {} \<Longrightarrow> {} \<Turnstile>\<^sub>A\<^sub>F {}\<close>
 *     using entails_bot_to_entails_empty entails_AF sorry
 *   then have simp_simp_c1: \<open>proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J = {bot}\<close>
 *     using not_useless simp_c1 by argo
 *     
 *   show \<open>enabled_set (proj\<^sub>\<bottom> C\<^sub>2) J \<longrightarrow>
 *     {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J) \<and> is_Pos C} \<union>
 *     {to_V C |C. C \<in> Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 \<and> \<not> is_Pos C} \<Turnstile>s
 *     {to_V C |C. C \<in> Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 \<and> is_Pos C} \<union>
 *     {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J) \<and> \<not> is_Pos C}\<close>
 *   proof
 *     assume \<open>enabled_set (proj\<^sub>\<bottom> C\<^sub>2) J\<close>
 *     then have \<open>proj\<^sub>\<bottom> C\<^sub>1 proj\<^sub>J J \<Turnstile> F_of ` proj\<^sub>\<bottom> C\<^sub>2\<close> using entails_AF by simp
 *     have simp_c2: \<open>F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {} \<or> F_of ` proj\<^sub>\<bottom> C\<^sub>2 = {bot}\<close>
 *       unfolding propositional_projection_def enabled_projection_def by force
 *     have \<open>{to_V C |C. C \<in> Pos ` F_of ` proj\<^sub>\<bottom> C\<^sub>2 \<and> \<not> is_Pos C} = {}\<close> by auto
 *   (\* show \<open>enabled_set C\<^sub>2 J \<longrightarrow>
 *    *   {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (C\<^sub>1 proj\<^sub>J J) \<and> is_Pos C} \<union>
 *    *   {to_V C |C. C \<in> Pos ` F_of ` C\<^sub>2 \<and> \<not> is_Pos C} \<Turnstile>s
 *    *   {to_V C |C. C \<in> Pos ` F_of ` C\<^sub>2 \<and> is_Pos C} \<union>
 *    *   {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (C\<^sub>1 proj\<^sub>J J) \<and> \<not> is_Pos C}\<close>
 *    * proof
 *    *   assume \<open>enabled_set C\<^sub>2 J\<close>
 *    *   then have entails_F: \<open>C\<^sub>1 proj\<^sub>J J \<Turnstile> F_of ` C\<^sub>2\<close> using entails_AF by simp
 *    *   have in_left: \<open>C\<^sub>1 proj\<^sub>J J \<subseteq> {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (C\<^sub>1 proj\<^sub>J J) \<and> is_Pos C}\<close>
 *    *     by force 
 *    *   moreover have in_right: \<open>F_of ` C\<^sub>2 \<subseteq> {to_V C |C. C \<in> Pos ` F_of ` C\<^sub>2 \<and> is_Pos C}\<close>
 *    *     by force
 *    *   ultimately show \<open>{to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (C\<^sub>1 proj\<^sub>J J) \<and> is_Pos C} \<union>
 *    *     {to_V C |C. C \<in> Pos ` F_of ` C\<^sub>2 \<and> \<not> is_Pos C} \<Turnstile>s
 *    *     {to_V C |C. C \<in> Pos ` F_of ` C\<^sub>2 \<and> is_Pos C} \<union>
 *    *     {to_V C |C. C \<in> fml_ext ` total_strip J \<union> Pos ` (C\<^sub>1 proj\<^sub>J J) \<and> \<not> is_Pos C}\<close>
 *    *     using entails_F sound_cons.entails_subsets *\)
 *     oops
 * end *)

end
