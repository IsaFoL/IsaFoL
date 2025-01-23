theory Calculi_And_Annotations
  imports Disjunctive_Consequence_Relations
begin


section \<open>Calculi and Derivations\<close>

context
begin

no_notation Extended.extended.Pinf (\<open>\<infinity>\<close>)

typedef 'a infinite_llist = \<open>{ l :: 'a llist. llength l = \<infinity> }\<close>
  morphisms to_llist Abs_infinite_llist
  using llength_inf_llist
  by blast

setup_lifting type_definition_infinite_llist

lift_definition llmap :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a infinite_llist \<Rightarrow> 'b infinite_llist\<close> is lmap
  by auto

lift_definition llnth :: \<open>'a infinite_llist \<Rightarrow> nat \<Rightarrow> 'a\<close> is lnth .

lift_definition Liminf_infinite_llist :: \<open>'a set infinite_llist \<Rightarrow> 'a set\<close> is Liminf_llist .

lift_definition Limsup_infinite_llist :: \<open>'a set infinite_llist \<Rightarrow> 'a set\<close> is Limsup_llist .

lift_definition Sup_infinite_llist :: \<open>'a set infinite_llist \<Rightarrow> 'a set\<close> is Sup_llist .

lift_definition llhd :: \<open>'a infinite_llist \<Rightarrow> 'a\<close> is lhd .

lemma llength_of_to_llist_is_infinite: \<open>llength (to_llist L) = \<infinity>\<close>
  using to_llist
  by auto

end (* unnamed context *)

locale sound_inference_system =
  inference_system Inf + sound_cons: consequence_relation bot entails_sound
  for
    Inf :: "'f inference set" and
    bot :: "'f" and
    entails_sound :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>s" 50)
  + assumes
    sound: "\<iota> \<in> Inf \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s {concl_of \<iota>}"
    
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

    Update: option 3 seems way easier to interact with the Saturation Framework.
    *)

no_notation IArray.sub (infixl "!!" 100)
  
definition is_derivation :: "('f set \<Rightarrow> 'f set \<Rightarrow> bool) \<Rightarrow> ('f set infinite_llist) \<Rightarrow> bool" where
  "is_derivation R Ns \<equiv> \<forall>i. R (llnth Ns i) (llnth Ns (Suc i))"
  
definition terminates :: "'f set infinite_llist \<Rightarrow> bool" where
  "terminates Ns \<equiv> \<exists>i. \<forall>j>i. llnth Ns j = llnth Ns i"

abbreviation \<open>lim_inf \<equiv> Liminf_infinite_llist\<close>

abbreviation limit :: "'f set infinite_llist \<Rightarrow> 'f set" where "limit Ns \<equiv> lim_inf Ns"

abbreviation lim_sup :: \<open>'f set infinite_llist \<Rightarrow> 'f set\<close> where
  \<open>lim_sup Ns \<equiv> Limsup_infinite_llist Ns\<close>

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
    Red_F_Bot: "N \<Turnstile> {bot} \<Longrightarrow> N - Red_F N \<Turnstile> {bot}" and
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

definition weakly_fair :: "'f set infinite_llist \<Rightarrow> bool" where
  \<open>weakly_fair Ns \<equiv> Inf_from (Liminf_infinite_llist Ns) \<subseteq> Sup_infinite_llist (llmap Red_I Ns)\<close>
  (* "weakly_fair Ns \<equiv> Inf_from (lim_inf Ns) \<subseteq> (\<Union>i. (Red_I (Ns !! i)))" *)

abbreviation fair :: "'f set infinite_llist \<Rightarrow> bool" where "fair N \<equiv> weakly_fair N"

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
  by (simp add: calculus.intro calculus_axioms.intro Red_F_Bot
    Red_F_of_Red_F_subset Red_F_of_subset Red_I_of_Inf_to_N Red_I_of_Red_F_subset Red_I_of_subset
    Red_I_to_Inf consequence_relation_axioms)
end
      
locale statically_complete_calculus = calculus +
  assumes statically_complete: "saturated N \<Longrightarrow> N \<Turnstile> {bot} \<Longrightarrow> bot \<in> N"
begin

lemma inf_from_subs: "M \<subseteq> N \<Longrightarrow> Inf_from M \<subseteq> Inf_from N"
  unfolding Inf_from_def by blast
    
    (* Splitting report Lemma 2 *)
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
  
  (* Splitting report Remark 3 *)
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
    \<open>is_derivation (\<rhd>) Ns \<Longrightarrow> fair Ns \<Longrightarrow> llhd Ns \<Turnstile> {bot} \<Longrightarrow> \<exists>i. bot \<in> llnth Ns i\<close>


(*******************************************)
section \<open>Annotated Formulas and Consequence Relations\<close>


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
datatype ('f, 'v::countable) AF = Pair (F_of: "'f") (A_of: "'v sign fset")

definition is_interpretation :: "'v sign set \<Rightarrow> bool" where
  \<open>is_interpretation J = (\<forall>v1\<in>J. (\<forall>v2\<in>J. (to_V v1 = to_V v2 \<longrightarrow> v1 = v2)))\<close>
  
  (* TODO: find a shorter name for this type (?) *)
typedef 'v propositional_interpretation = "{J :: 'v sign set. is_interpretation J}"
proof
  show \<open>{} \<in> {J. is_interpretation J}\<close> unfolding is_interpretation_def by blast 
qed
  
abbreviation "interp_of \<equiv> Abs_propositional_interpretation"
abbreviation "strip \<equiv> Rep_propositional_interpretation"

setup_lifting type_definition_propositional_interpretation

lift_definition belong_to :: "'v sign \<Rightarrow> 'v propositional_interpretation \<Rightarrow> bool" (infix "\<in>\<^sub>J" 90)
  is "(\<in>)::('v sign \<Rightarrow> 'v sign set \<Rightarrow> bool)" .

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

lemma neg_notin_total_strip [simp]: \<open>(neg a \<notin> total_strip J) = (a \<in> total_strip J)\<close>
proof
  assume neg_a_notin: \<open>neg a \<notin> total_strip J\<close>
  have \<open>\<exists>b. to_V a = to_V b \<and> b \<in> total_strip J\<close>
    by (metis Rep_total_interpretation belong_to.rep_eq mem_Collect_eq total_def)
  then show \<open>a \<in> total_strip J\<close>
    using neg_a_notin by (metis neg.simps to_V.elims)
next
  assume a_in: \<open>a \<in> total_strip J\<close>
  then have \<open>\<exists>b. to_V a = to_V b \<and> b \<notin> total_strip J\<close>
    by (metis Rep_propositional_interpretation is_interpretation_def mem_Collect_eq sign.simps(4)
        to_V.simps)
  then show \<open>neg a \<notin> total_strip J\<close>
    using a_in by (metis neg.simps to_V.elims)
qed

lemma neg_in_total_strip [simp]: \<open>(neg a \<in> total_strip J) = (a \<notin> total_strip J)\<close>
proof
  assume neg_a_notin: \<open>neg a \<in> total_strip J\<close>
  have \<open>\<exists>b. to_V a = to_V b \<and> b \<notin> total_strip J\<close>
   by (metis Rep_propositional_interpretation is_interpretation_def mem_Collect_eq sign.simps(4)
        to_V.simps)
  then show \<open>a \<notin> total_strip J\<close>
    using neg_a_notin by (metis neg.simps to_V.elims)
next
  assume a_in: \<open>a \<notin> total_strip J\<close>
  then have \<open>\<exists>b. to_V a = to_V b \<and> b \<in> total_strip J\<close>
    by (metis Rep_total_interpretation belong_to.rep_eq mem_Collect_eq total_def)
  then show \<open>neg a \<in> total_strip J\<close>
    using a_in by (metis neg.simps to_V.elims)
qed

setup_lifting type_definition_total_interpretation

lift_definition belong_to_total :: "'v sign \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" (infix "\<in>\<^sub>t" 90)
  is "(\<in>\<^sub>J)::('v sign \<Rightarrow> 'v propositional_interpretation \<Rightarrow> bool)" .

lemma in_total_to_strip [simp]: \<open>a \<in>\<^sub>t J \<longleftrightarrow> a \<in> total_strip J\<close>
  unfolding belong_to_total_def belong_to_def by simp

lemma neg_prop_interp: \<open>(v::'v sign) \<in>\<^sub>J J \<Longrightarrow> \<not> ((neg v) \<in>\<^sub>J J)\<close>
proof transfer
  fix v J
  assume
    j_is: \<open>is_interpretation (J:: 'v sign set)\<close> and
    v_in: \<open>v \<in> J\<close>
  then show \<open>\<not> (neg v) \<in> J\<close>
  proof (cases v)
    case (Pos C)
    then show ?thesis
      using is_Pos.simps
      by (metis is_interpretation_def j_is neg.simps(1) to_V.simps v_in)
  next
    case (Neg C)
    then show ?thesis
      using j_is v_in
      using is_interpretation_def by fastforce
  qed
qed

lemma neg_total_interp: \<open>(v::'v sign) \<in>\<^sub>t J \<Longrightarrow> \<not> ((neg v) \<in>\<^sub>t J)\<close>
proof transfer
  fix v J
  assume v_in: \<open>v \<in>\<^sub>J (J :: 'v propositional_interpretation)\<close>
  show \<open>\<not> neg v \<in>\<^sub>J J\<close>
    using neg_prop_interp[OF v_in] by simp
qed

lemma neg_notin_total_interp: \<open>\<not> (v \<in>\<^sub>t J) \<Longrightarrow> ((neg v) \<in>\<^sub>t J)\<close>
proof transfer
  fix v::"'v sign" and J
  assume 
    tot: \<open>total J\<close> and
    not_in: \<open>\<not> v \<in>\<^sub>J J\<close>
  show \<open>neg v \<in>\<^sub>J J\<close>
    using tot not_in unfolding total_def
    by (metis belong_to_total.abs_eq eq_onp_def in_total_to_strip neg_in_total_strip tot)
qed

definition to_AF :: "'f \<Rightarrow> ('f, 'v::countable) AF" where
  \<open>to_AF C = Pair C {||}\<close>

lemma F_of_to_AF: \<open>F_of (to_AF \<C>) = \<C>\<close>
  unfolding to_AF_def
  by auto

lemma A_of_to_AF: \<open>A_of (to_AF \<C>) = {||}\<close>
  unfolding to_AF_def
  by auto

lemma F_of_circ_to_AF_is_id [simp]: \<open>F_of \<circ> to_AF = id\<close>
  by (fastforce simp: F_of_to_AF)

lemma A_of_circ_to_AF_is_empty_set [simp]: \<open>A_of \<circ> to_AF = (\<lambda> _. {||})\<close>
  by (fastforce simp: A_of_to_AF) 

lemma F_of_propositional_clauses [simp]:
  \<open>(\<forall> x \<in> set \<N>. F_of x = bot) \<Longrightarrow> map F_of \<N> = map (\<lambda> _. bot) \<N>\<close>
  using map_eq_conv
  by blast

lemma F_of_Pair [simp]: \<open>F_of \<circ> (\<lambda>(x, y). AF.Pair x y) = (\<lambda>(x, y). x)\<close>
  by (smt (verit, ccfv_SIG) AF.sel(1) comp_apply cond_case_prod_eta old.prod.case)

lemma A_of_Pair [simp]: \<open>A_of \<circ> (\<lambda>(x, y). AF.Pair x y) = (\<lambda>(x, y). y)\<close>
  by fastforce

lemma map_A_of_map2_Pair: \<open>length A = length B \<Longrightarrow> map A_of (map2 AF.Pair A B) = B\<close>
proof -
  assume \<open>length A = length B\<close>
  then have \<open>map2 (\<lambda> x y. y) A B = B\<close>
    by (metis map_eq_conv map_snd_zip snd_def)
  then show ?thesis
    by auto 
qed  

definition Neg_set :: "'v sign set \<Rightarrow> 'v sign set" ("\<sim>_" 55) where
  \<open>\<sim>V \<equiv> {neg v |v. v \<in> V}\<close>

definition F_of_Inf :: "(('f, 'v::countable) AF) inference \<Rightarrow> 'f inference" where
  \<open>F_of_Inf \<iota>\<^sub>A\<^sub>F = (Infer (map F_of (prems_of \<iota>\<^sub>A\<^sub>F)) (F_of (concl_of \<iota>\<^sub>A\<^sub>F)))\<close>

section \<open>Lifting Calculi to Add Annotations\<close>

locale AF_calculus_lifting = sound_calculus bot Inf entails entails_sound Red\<^sub>I Red_F
  (* + propositional_interpretations \<J>*)
  for
    bot :: "'f" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) and
    entails_sound :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>s" 50) and
    Red\<^sub>I :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set"
  + fixes
    (* V:: "'v::countable itself" and *)
    (* \<J> :: "'v::countable neg set set" and *)
    fml :: \<open>'v :: countable \<Rightarrow> 'f\<close> and 
    asn :: \<open>'f sign \<Rightarrow> 'v sign set\<close>
  assumes
    fml_entails_C: \<open>\<forall> a \<in> asn C. sound_cons.entails_neg {map_sign fml a} {C}\<close> and
    C_entails_fml: \<open>\<forall> a \<in> asn C. sound_cons.entails_neg {C} {map_sign fml a}\<close> and
    asn_not_empty: \<open>asn C \<noteq> {}\<close>
begin

notation sound_cons.entails_neg (infix \<open>\<Turnstile>s\<^sub>\<sim>\<close> 50)

lemma equi_entails_if_a_in_asns: \<open>a \<in> asn C \<Longrightarrow> a \<in> asn D \<Longrightarrow> {C} \<Turnstile>s\<^sub>\<sim> {D} \<and> {D} \<Turnstile>s\<^sub>\<sim> {C}\<close>
  by (smt (verit) C_entails_fml Un_commute consequence_relation.entails_cut fml_entails_C
    sound_cons.ext_cons_rel sup_bot_left)

lemma equi_entails_if_neg_a_in_asn:
  \<open>a \<in> asn C \<Longrightarrow> neg a \<in> asn D \<Longrightarrow> {C} \<Turnstile>s\<^sub>\<sim> {neg D} \<and> {neg D} \<Turnstile>s\<^sub>\<sim> {C}\<close>
proof (intro conjI)
  assume a_in_asn_C: \<open>a \<in> asn C\<close> and
         neg_a_in_asn_D: \<open>neg a \<in> asn D\<close>

  have fml_neg_is_neg_fml: \<open>map_sign fml (neg x) = neg (map_sign fml x)\<close> for x
    by (smt (verit, ccfv_threshold) neg.simps(1) neg_neg_A_is_A sign.simps(10) sign.simps(9)
        to_V.elims)  

  have \<open>{C} \<Turnstile>s\<^sub>\<sim> {map_sign fml a}\<close>
    using a_in_asn_C C_entails_fml
    by blast
  then have \<open>{C} \<Turnstile>s\<^sub>\<sim> {neg D, map_sign fml a}\<close>
    by (smt (verit, best) Un_upper2 consequence_relation.entails_subsets insert_is_Un
        sound_cons.ext_cons_rel sup_ge1)
  moreover have \<open>{D} \<Turnstile>s\<^sub>\<sim> {map_sign fml (neg a)}\<close>
    using neg_a_in_asn_D C_entails_fml
    by blast
  then have \<open>{neg (neg D)} \<Turnstile>s\<^sub>\<sim> {neg (map_sign fml a)}\<close>
    by (simp add: fml_neg_is_neg_fml)
  then have \<open>{map_sign fml a} \<Turnstile>s\<^sub>\<sim> {neg D}\<close>
    using sound_cons.swap_neg_in_entails_neg
    by blast 
  then have \<open>{map_sign fml a, C} \<Turnstile>s\<^sub>\<sim> {neg D}\<close>
    by (smt (verit, best) consequence_relation.entails_subsets insert_is_Un sound_cons.ext_cons_rel
        sup_ge1)
  ultimately show \<open>{C} \<Turnstile>s\<^sub>\<sim> {neg D}\<close>
    using consequence_relation.entails_cut
    by (smt (verit, ccfv_threshold) Un_commute insert_is_Un sound_cons.ext_cons_rel sup.idem)
next
  assume a_in_asn_C: \<open>a \<in> asn C\<close> and
         neg_a_in_asn_D: \<open>neg a \<in> asn D\<close>

  have fml_neg_is_neg_fml: \<open>map_sign fml (neg x) = neg (map_sign fml x)\<close> for x
    by (smt (verit, ccfv_threshold) neg.simps(1) neg_neg_A_is_A sign.simps(10) sign.simps(9)
        to_V.elims)  

  have \<open>{map_sign fml a} \<Turnstile>s\<^sub>\<sim> {C}\<close>
    using a_in_asn_C fml_entails_C
    by blast
  then have \<open>{neg D, map_sign fml a} \<Turnstile>s\<^sub>\<sim> {C}\<close>
    by (smt (verit, best) Un_upper2 consequence_relation.entails_subsets insert_is_Un
        sound_cons.ext_cons_rel sup_ge1)
  moreover have \<open>{map_sign fml (neg a)} \<Turnstile>s\<^sub>\<sim> {D}\<close>
    using neg_a_in_asn_D fml_entails_C
    by blast
  then have \<open>{neg (map_sign fml a)} \<Turnstile>s\<^sub>\<sim> {neg (neg D)}\<close>
    by (simp add: fml_neg_is_neg_fml)
  then have \<open>{neg D} \<Turnstile>s\<^sub>\<sim> {map_sign fml a}\<close>
    using sound_cons.swap_neg_in_entails_neg
    by blast
  then have \<open>{neg D} \<Turnstile>s\<^sub>\<sim> {map_sign fml a, C}\<close>
    by (smt (verit, best) consequence_relation.entails_subsets insert_is_Un sound_cons.ext_cons_rel
        sup_ge1)
  ultimately show \<open>{neg D} \<Turnstile>s\<^sub>\<sim> {C}\<close>
    using consequence_relation.entails_cut
    by (smt (verit, ccfv_threshold) Un_commute insert_is_Un sound_cons.ext_cons_rel sup.idem)
qed

definition \<iota>F_of :: "('f, 'v) AF inference \<Rightarrow> 'f inference" where
  \<open>\<iota>F_of \<iota> = Infer (List.map F_of (prems_of \<iota>)) (F_of (concl_of \<iota>))\<close>
  
definition propositional_projection :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set" ("proj\<^sub>\<bottom>") where
  \<open>proj\<^sub>\<bottom> \<N> = {\<C>. \<C> \<in> \<N> \<and> F_of \<C> = bot}\<close>

lemma prop_proj_in: \<open>proj\<^sub>\<bottom> \<N> \<subseteq> \<N>\<close>
  unfolding propositional_projection_def by blast

definition enabled :: "('f, 'v) AF \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" where
  "enabled \<C> J \<equiv> fset (A_of \<C>) \<subseteq> (total_strip J)"

lemma subformula_of_enabled_formula_is_enabled: \<open>A_of \<C> |\<subset>| A_of \<C>' \<Longrightarrow> enabled \<C>' J \<Longrightarrow> enabled \<C> J\<close>
  unfolding enabled_def
  by (meson less_eq_fset.rep_eq pfsubset_imp_fsubset subset_trans)

lemma enabled_iff: \<open>A_of \<C> = A_of \<C>' \<Longrightarrow> enabled \<C> J \<longleftrightarrow> enabled \<C>' J\<close>
  unfolding enabled_def
  by simp

definition enabled_set :: "('f, 'v) AF set \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" where
  \<open>enabled_set \<N> J = (\<forall>\<C>\<in>\<N>. enabled \<C> J)\<close>

lemma enabled_set_singleton [simp]: \<open>enabled_set {\<C>} J \<longleftrightarrow> enabled \<C> J\<close>
  by (auto simp add: enabled_set_def)

definition enabled_inf :: "('f, 'v) AF inference \<Rightarrow> 'v total_interpretation \<Rightarrow> bool" where
  \<open>enabled_inf \<iota> J = (\<forall>\<C>\<in> set (prems_of \<iota>). enabled \<C> J)\<close>
  
definition enabled_projection :: "('f, 'v) AF set \<Rightarrow> 'v total_interpretation \<Rightarrow> 'f set"
  (infix "proj\<^sub>J" 60)  where
  \<open>\<N> proj\<^sub>J J = {F_of \<C> |\<C>. \<C> \<in> \<N> \<and> enabled \<C> J}\<close>

lemma Union_of_enabled_projection_is_enabled_projection: \<open>(\<Union> \<C> \<in> \<N>. {\<C>} proj\<^sub>J \<J>) = \<N> proj\<^sub>J \<J>\<close>
  unfolding enabled_projection_def
  by blast

lemma projection_of_enabled_subset:
  \<open>fset B \<subseteq> total_strip J \<Longrightarrow> {AF.Pair C (A |\<union>| B)} proj\<^sub>J J = {AF.Pair C A} proj\<^sub>J J\<close>
  unfolding enabled_projection_def enabled_def
  by auto

lemma Un_of_enabled_projection_is_enabled_projection_of_Un:
  \<open>(\<Union> x. P x) proj\<^sub>J J = (\<Union> x. P x proj\<^sub>J J)\<close>
proof (intro subset_antisym subsetI)
  fix x
  assume \<open>x \<in> (\<Union> x. P x) proj\<^sub>J J\<close>
  then have \<open>\<exists> y. x = F_of y \<and> enabled y J \<and> y \<in> (\<Union> x. P x)\<close>
    unfolding enabled_projection_def
    by blast
  then have \<open>\<exists> y. x = F_of y \<and> enabled y J \<and> (\<exists> z. y \<in> P z)\<close>
    by blast
  then have \<open>\<exists> y. \<exists> z. x = F_of y \<and> enabled y J \<and> y \<in> P z\<close>
    by blast
  then show \<open>x \<in> (\<Union> x. P x proj\<^sub>J J)\<close>
    unfolding enabled_projection_def
    by blast
next
  fix x
  assume \<open>x \<in> (\<Union> x. P x proj\<^sub>J J)\<close>
  then have \<open>\<exists> y. x \<in> P y proj\<^sub>J J\<close>
    by blast
  then have \<open>\<exists> y. \<exists> z. x = F_of z \<and> enabled z J \<and> z \<in> P y\<close>
    unfolding enabled_projection_def
    by blast
  then show \<open>x \<in> (\<Union> x. P x) proj\<^sub>J J\<close>
    unfolding enabled_projection_def
    by blast
qed

lemma enabled_projection_of_Int_is_Int_of_enabled_projection:
  \<open>x \<in> (\<Inter> S) proj\<^sub>J J \<Longrightarrow> x \<in> \<Inter> { x proj\<^sub>J J | x. x \<in> S }\<close>
  unfolding enabled_projection_def
  by blast

definition enabled_projection_Inf :: "('f, 'v) AF inference set \<Rightarrow> 'v total_interpretation \<Rightarrow>
  'f inference set" (infix "\<iota>proj\<^sub>J" 60) where
  \<open>I \<iota>proj\<^sub>J J = {\<iota>F_of \<iota> | \<iota>. \<iota> \<in> I \<and> enabled_inf \<iota> J}\<close>

fun fml_ext :: "'v sign \<Rightarrow> 'f sign" where
  "fml_ext (Pos v) = Pos (fml v)" |
  "fml_ext (Neg v) = Neg (fml v)"

lemma fml_ext_is_mapping: \<open>fml_ext v = map_sign fml v\<close>
  by (metis fml_ext.cases fml_ext.simps(1) fml_ext.simps(2) sign.simps(10) sign.simps(9)) 

lemma fml_ext_preserves_sign: "is_Pos v \<equiv> is_Pos (fml_ext v)"
  by (induct v, auto)

lemma to_V_fml_ext [simp]: \<open>to_V (fml_ext v) = fml (to_V v)\<close>
  by (induct v, auto) 

lemma fml_ext_preserves_val: \<open>to_V v1 = to_V v2 \<Longrightarrow> to_V (fml_ext v1) = to_V (fml_ext v2)\<close>
  by simp
 
definition sound_consistent :: "'v total_interpretation \<Rightarrow> bool" where
  \<open>sound_consistent J \<equiv> \<not> (sound_cons.entails_neg (fml_ext ` (total_strip J)) {Pos bot})\<close>
  
(* TODO: try alternative def that makes use of prop semantic from AFP to ease use of compactness *)
(* connection to compactness from AFP used but could it be made more direct? *)
definition propositional_model :: "'v total_interpretation \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool"
  (infix "\<Turnstile>\<^sub>p" 50) where
  \<open>J \<Turnstile>\<^sub>p \<N> \<equiv> bot \<notin> ((proj\<^sub>\<bottom> \<N>) proj\<^sub>J J)\<close>

lemma \<open>J \<Turnstile>\<^sub>p {}\<close> 
  unfolding propositional_model_def enabled_projection_def propositional_projection_def by blast
 
definition propositional_model2 :: "'v total_interpretation \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool"
  (infix "\<Turnstile>\<^sub>p2" 50) where
  \<open>J \<Turnstile>\<^sub>p2 \<N> \<equiv> ({} = ((proj\<^sub>\<bottom> \<N>) proj\<^sub>J J))\<close>

lemma subset_model_p2: \<open>\<N>' \<subseteq> \<N> \<Longrightarrow> J \<Turnstile>\<^sub>p2 \<N> \<Longrightarrow> J \<Turnstile>\<^sub>p2 \<N>'\<close>
  by (simp add: enabled_projection_def propositional_model2_def propositional_projection_def 
      subset_eq)

lemma subset_not_model: \<open>\<not> J \<Turnstile>\<^sub>p2 \<N> \<Longrightarrow> \<N> = \<N>\<^sub>1 \<union> \<N>\<^sub>2 \<Longrightarrow> J \<Turnstile>\<^sub>p2 \<N>\<^sub>1 \<Longrightarrow> \<not> J \<Turnstile>\<^sub>p2 \<N>\<^sub>2\<close>
  unfolding propositional_model2_def propositional_projection_def enabled_projection_def by blast

lemma supset_not_model_p2: \<open>\<N>' \<subseteq> \<N> \<Longrightarrow> \<not> J \<Turnstile>\<^sub>p2 \<N>' \<Longrightarrow> \<not> J \<Turnstile>\<^sub>p2 \<N>\<close>
  using subset_model_p2 by blast

fun sign_to_atomic_formula :: "'v sign \<Rightarrow> 'v formula" where
  \<open>sign_to_atomic_formula (Pos v) = Atom v\<close> |
  \<open>sign_to_atomic_formula (Neg v) = Not (Atom v)\<close>

definition sign_set_to_formula_set :: "'v sign set \<Rightarrow> 'v formula set" where
  \<open>sign_set_to_formula_set A = sign_to_atomic_formula ` A\<close>

lemma form_shape_sign_set: \<open>\<forall>f\<in>sign_set_to_formula_set A. \<exists>v. f = Atom v \<or> f = Not (Atom v)\<close>
  unfolding sign_set_to_formula_set_def
  by (metis image_iff sign_to_atomic_formula.elims)

definition AF_to_formula_set :: "('f, 'v) AF \<Rightarrow> 'v formula set" where
  (* /!\ this formula set is to be understood as a disjunction *)
  \<open>AF_to_formula_set \<C> = sign_set_to_formula_set (neg ` fset (A_of \<C>))\<close>

definition AF_to_formula :: "('f, 'v) AF \<Rightarrow> 'v formula" where
  \<open>AF_to_formula \<C> = BigOr (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>))))\<close>

lemma form_shape_AF: \<open>\<forall>f\<in>AF_to_formula_set \<C>. \<exists>v. f = Atom v \<or> f = Not (Atom v)\<close>
  using form_shape_sign_set unfolding AF_to_formula_set_def by simp

definition AF_proj_to_formula_set_set :: "('f, 'v) AF set \<Rightarrow> 'v formula set set" where
  (* /!\ formula set set represents here a conjuction of disjunctions *)
  \<open>AF_proj_to_formula_set_set \<N> = AF_to_formula_set ` (proj\<^sub>\<bottom> \<N>)\<close>

definition AF_proj_to_formula_set :: "('f, 'v) AF set \<Rightarrow> 'v formula set" where
  \<open>AF_proj_to_formula_set \<N> = AF_to_formula ` (proj\<^sub>\<bottom> \<N>)\<close>

definition AF_assertions_to_formula :: "('f, 'v) AF \<Rightarrow> 'v formula" where
  \<open>AF_assertions_to_formula \<C> = BigAnd (map sign_to_atomic_formula (list_of_fset (A_of \<C>)))\<close>

definition AF_assertions_to_formula_set :: "('f, 'v) AF set \<Rightarrow> 'v formula set" where
  \<open>AF_assertions_to_formula_set \<N> = AF_assertions_to_formula ` \<N>\<close>

lemma F_to_\<C>_set: \<open>\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>\<C>\<in>proj\<^sub>\<bottom> \<N>. F =
  sign_to_atomic_formula ` neg ` fset (A_of \<C>)\<close>
  unfolding AF_proj_to_formula_set_set_def AF_to_formula_set_def sign_set_to_formula_set_def
  by auto
(* TODO: show to Mathias: sledgehammer suggests "by blast" (for all provers) but this fails *)

lemma F_to_\<C>: \<open>\<forall>F\<in>AF_proj_to_formula_set \<N>. \<exists>\<C>\<in>proj\<^sub>\<bottom> \<N>. F =
   BigOr (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>))))\<close>
  unfolding AF_proj_to_formula_set_def AF_to_formula_def by auto

lemma \<C>_to_F_set: \<open>\<forall>\<C>\<in>proj\<^sub>\<bottom> \<N>. \<exists>F\<in>AF_proj_to_formula_set_set \<N>. F =
  sign_to_atomic_formula ` neg ` fset (A_of \<C>)\<close>
  unfolding AF_proj_to_formula_set_set_def AF_to_formula_set_def sign_set_to_formula_set_def
  by auto

lemma \<C>_to_F: \<open>\<forall>\<C>\<in>proj\<^sub>\<bottom> \<N>. \<exists>F\<in>AF_proj_to_formula_set \<N>. F =
  BigOr (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>))))\<close>
  unfolding AF_proj_to_formula_set_def AF_to_formula_def by auto

lemma form_shape_proj: \<open>\<forall>f\<in>\<Union> (AF_proj_to_formula_set_set \<N>). \<exists>v. f = Atom v \<or> f = Not (Atom v)\<close>
  using form_shape_AF unfolding AF_proj_to_formula_set_set_def by simp

definition to_valuation :: "'v total_interpretation \<Rightarrow> 'v valuation" where
  \<open>to_valuation J = (\<lambda>a. Pos a \<in>\<^sub>t J)\<close>

lemma val_strip_pos: \<open>to_valuation J a \<equiv> Pos a \<in> total_strip J\<close>
  unfolding to_valuation_def belong_to_total_def belong_to_def by simp

lemma val_strip_neg: \<open>(\<not> to_valuation J a) = (Neg a \<in> total_strip J)\<close>
proof -
  have \<open>(\<not> to_valuation J a) = (\<not> Pos a \<in> total_strip J)\<close>
    using val_strip_pos by simp
  also have \<open>(\<not> Pos a \<in> total_strip J) = (Neg a \<in> total_strip J)\<close>
  proof
    fix a J
    assume not_pos: \<open>Pos (a::'v) \<notin> total_strip J\<close>
    have \<open>is_interpretation (total_strip J)\<close>
      using Rep_propositional_interpretation by blast 
    then show \<open>Neg a \<in> total_strip J\<close> 
      unfolding is_interpretation_def using total_def not_pos
      by (metis Rep_total_interpretation belong_to.rep_eq mem_Collect_eq to_V.elims)
  next
    assume neg: \<open>Neg a \<in> total_strip J\<close>
    have \<open>is_interpretation (total_strip J)\<close>
      using Rep_propositional_interpretation by blast
    then show \<open>Pos a \<notin> total_strip J\<close>
      unfolding is_interpretation_def using neg
    by (metis sign.distinct(1) to_V.simps(1) to_V.simps(2))
  qed
  finally show \<open>(\<not> to_valuation J a) = (Neg a \<in> total_strip J)\<close> .
qed

lemma equiv_prop_entails: \<open>(J \<Turnstile>\<^sub>p \<N>) \<longleftrightarrow> (J \<Turnstile>\<^sub>p2 \<N>)\<close>
  unfolding propositional_model_def propositional_model2_def propositional_projection_def
    enabled_projection_def
  by blast

(* The interest of this first semantic characterization is that it is computable, but it is not
   convenient to apply the compactness results *)
lemma equiv_prop_entail2_sema:
  \<open>(J \<Turnstile>\<^sub>p2 \<N>) \<longleftrightarrow> (\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>f\<in>F. formula_semantics (to_valuation J) f)\<close>
  unfolding propositional_model2_def enabled_projection_def enabled_def
proof
  assume empty_proj: \<open>{} = {F_of \<C> |\<C>. \<C> \<in> proj\<^sub>\<bottom> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
  then have \<open>\<forall>\<C>\<in>proj\<^sub>\<bottom> \<N>. \<exists>v\<in>fset (A_of \<C>). neg v \<in> total_strip J\<close> 
    by (smt (verit, ccfv_SIG) empty_iff mem_Collect_eq neg.elims subsetI
        val_strip_neg val_strip_pos)
  show \<open>\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>f\<in>F. formula_semantics (to_valuation J) f\<close>
  proof
    fix F
    assume F_in: \<open>F \<in> AF_proj_to_formula_set_set \<N>\<close>
    then obtain \<C> where \<open>\<C> \<in> proj\<^sub>\<bottom> \<N>\<close> and F_from_\<C>: \<open>F = sign_to_atomic_formula ` neg ` fset (A_of \<C>)\<close>
      using F_to_\<C>_set by meson
    then have \<open>\<exists>v\<in>fset (A_of \<C>). v \<notin> total_strip J\<close>
      using empty_proj by blast
    then obtain v where v_in: \<open>v \<in> fset (A_of \<C>)\<close> and v_notin: \<open>v \<notin> total_strip J\<close> by auto
    define f where \<open>f = sign_to_atomic_formula (neg v)\<close>
    then have \<open>formula_semantics (to_valuation J) f\<close>
      using v_notin
      by (smt (z3) belong_to.rep_eq belong_to_total.rep_eq formula_semantics.simps neg.elims
          sign_to_atomic_formula.simps to_valuation_def val_strip_neg)
    moreover have \<open>f \<in> F\<close>
      using F_from_\<C> v_in f_def by blast
    ultimately show \<open>\<exists>f\<in>F. formula_semantics (to_valuation J) f\<close> by auto
  qed
next
  assume F_sat: \<open>\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>f\<in>F. formula_semantics (to_valuation J) f\<close>
  have \<open>\<forall>\<C>\<in>proj\<^sub>\<bottom> \<N>. \<exists>v\<in>fset (A_of \<C>). neg v \<in> total_strip J\<close>
  proof
    fix \<C>
    assume \<open>\<C> \<in> proj\<^sub>\<bottom> \<N>\<close>
    then obtain F where \<open>F \<in> AF_proj_to_formula_set_set \<N>\<close> and
      F_from_\<C>: \<open>F = sign_to_atomic_formula ` neg ` fset (A_of \<C>)\<close>
      using \<C>_to_F_set by blast
    then have \<open>\<exists>f\<in>F. formula_semantics (to_valuation J) f\<close>
      using F_sat by blast
    then obtain f where f_in: \<open>f \<in> F\<close> and sat_f: \<open>formula_semantics (to_valuation J) f\<close>
      by blast
    then obtain v where v_is: \<open>f = sign_to_atomic_formula (neg v)\<close> and v_in: \<open>v \<in> fset (A_of \<C>)\<close>
      using F_from_\<C> by blast
    then have \<open>neg v \<in> total_strip J\<close>
      using sat_f unfolding to_valuation_def
      by (smt (z3) belong_to.rep_eq belong_to_total.rep_eq formula_semantics.simps sign.exhaust
          sign_to_atomic_formula.simps val_strip_neg val_strip_pos)
    then show \<open>\<exists>v\<in>fset (A_of \<C>). neg v \<in> total_strip J\<close>
      using v_in by auto
  qed
  then show \<open>{} = {F_of \<C> |\<C>. \<C> \<in> proj\<^sub>\<bottom> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
    by (smt (verit, ccfv_threshold) empty_Collect_eq is_Pos.cases neg.simps(1) neg.simps(2) subsetD
        val_strip_neg val_strip_pos)
qed

lemma fset_map2: \<open>v \<in> fset A \<Longrightarrow> g (f v) \<in> set (map g (map f (list_of_fset A)))\<close>
proof -
  assume \<open>v \<in> fset A\<close>
  then show \<open>g (f v) \<in> set (map g (map f (list_of_fset A)))\<close>
    unfolding list_of_fset_def
    by (smt (verit, ccfv_SIG) exists_fset_of_list fset_of_list.rep_eq imageI list.set_map someI_ex)
qed

(* this characterization can be used to apply the compactness from Michaelis & Nipkow but it uses
   something that can't be computed (SOME) *)
lemma equiv_prop_entail2_sema2:
  \<open>(J \<Turnstile>\<^sub>p2 \<N>) \<longleftrightarrow> (\<forall>F\<in>AF_proj_to_formula_set \<N>. formula_semantics (to_valuation J) F)\<close>
  unfolding propositional_model2_def enabled_projection_def enabled_def
proof
  assume empty_proj: \<open>{} = {F_of \<C> |\<C>. \<C> \<in> proj\<^sub>\<bottom> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
  show \<open>\<forall>F\<in>AF_proj_to_formula_set \<N>. formula_semantics (to_valuation J) F\<close>
  proof
    fix F
    assume F_in: \<open>F \<in> AF_proj_to_formula_set \<N>\<close>
    then obtain \<C> where \<open>\<C> \<in> proj\<^sub>\<bottom> \<N>\<close> and 
      F_from_\<C>: \<open>F = BigOr (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>))))\<close>
      using F_to_\<C> by meson
    then have \<open>\<exists>v\<in>fset (A_of \<C>). v \<notin> total_strip J\<close>
      using empty_proj by blast
    then obtain v where v_in: \<open>v \<in> fset (A_of \<C>)\<close> and v_notin: \<open>v \<notin> total_strip J\<close> by auto
    define f where \<open>f = sign_to_atomic_formula (neg v)\<close>
    then have \<open>formula_semantics (to_valuation J) f\<close>
      using v_notin
      by (smt (z3) belong_to.rep_eq belong_to_total.rep_eq formula_semantics.simps neg.elims
          sign_to_atomic_formula.simps to_valuation_def val_strip_neg)
    moreover have \<open>f \<in> set (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>))))\<close>
      unfolding f_def using fset_map2[OF v_in, of sign_to_atomic_formula neg] .
    ultimately have \<open>\<exists>f\<in>set (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>)))).
     formula_semantics (to_valuation J) f\<close>
      by blast
    then show \<open>formula_semantics (to_valuation J) F\<close>
      using BigOr_semantics[of "to_valuation J"
          "map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>)))"] F_from_\<C>
      by meson
    qed
next
  assume F_sat: \<open>\<forall>F\<in>AF_proj_to_formula_set \<N>. formula_semantics (to_valuation J) F\<close>
  have \<open>\<forall>\<C>\<in>proj\<^sub>\<bottom> \<N>. \<exists>v\<in>fset (A_of \<C>). neg v \<in> total_strip J\<close>
  proof
    fix \<C>
    assume \<C>_in: \<open>\<C> \<in> proj\<^sub>\<bottom> \<N>\<close>
    define F where \<open>F = AF_to_formula \<C>\<close>
    then have \<open>F \<in> AF_proj_to_formula_set \<N>\<close>
      unfolding AF_proj_to_formula_set_def using \<C>_in by blast
    then have \<open>formula_semantics (to_valuation J) F\<close> using F_sat by blast
    then have \<open>\<exists>f\<in>set (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>)))).
      formula_semantics (to_valuation J) f\<close>
      using BigOr_semantics[of "to_valuation J"] unfolding F_def AF_to_formula_def by simp
    then obtain f where 
      f_in: \<open>f \<in> set (map sign_to_atomic_formula (map neg (list_of_fset (A_of \<C>))))\<close>
      and val_f: \<open>formula_semantics (to_valuation J) f\<close> by blast
    obtain v where v_in: \<open>v \<in> fset (A_of \<C>)\<close> and f_is: \<open>f = sign_to_atomic_formula (neg v)\<close>
      using f_in unfolding list_of_fset_def
      by (smt (z3) exists_fset_of_list fset_of_list.rep_eq image_iff list.set_map someI)
    have \<open>neg v \<in> total_strip J\<close>
      using f_is val_f unfolding to_valuation_def
      by (metis (mono_tags, lifting) belong_to.rep_eq belong_to_total.rep_eq 
          formula_semantics.simps(1) formula_semantics.simps(3) sign_to_atomic_formula.cases
          sign_to_atomic_formula.simps(1) sign_to_atomic_formula.simps(2) val_f val_strip_neg)
    then show \<open>\<exists>v\<in>fset (A_of \<C>). neg v \<in> total_strip J\<close>
      using v_in by blast
  qed
  then show \<open>{} = {F_of \<C> |\<C>. \<C> \<in> proj\<^sub>\<bottom> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
    by (smt (verit, ccfv_threshold) empty_Collect_eq is_Pos.cases neg.simps(1) neg.simps(2) subsetD
        val_strip_neg val_strip_pos)
qed

lemma equiv_prop_entail_sema:
  \<open>(J \<Turnstile>\<^sub>p \<N>) \<longleftrightarrow> (\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>f\<in>F. formula_semantics (to_valuation J) f)\<close>
  using equiv_prop_entails equiv_prop_entail2_sema by presburger

definition propositional_model3 :: "'v total_interpretation \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool"
  (infix "\<Turnstile>\<^sub>p3" 50) where
  \<open>J \<Turnstile>\<^sub>p3 \<N> \<equiv> (\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>f\<in>F. formula_semantics (to_valuation J) f)\<close>

lemma \<open>f ` fset A = set (map f (list_of_fset A))\<close>
proof
  show \<open>f ` fset A \<subseteq> set (map f (list_of_fset A))\<close>
  proof
    fix v
    assume v_in: \<open>v \<in> f ` fset A\<close>
    then obtain a where "a |\<in>| A" "f a = v"
     by blast 
    then show \<open>v \<in> set (map f (list_of_fset A))\<close>
      unfolding list_of_fset_def
      by (metis fset_map2 list_of_fset_def map_ident)
  qed
next
  show \<open>set (map f (list_of_fset A)) \<subseteq> f ` fset A\<close>
  proof
    fix v
    assume \<open>v \<in> set (map f (list_of_fset A))\<close>
    then obtain a where "a |\<in>| A" "f a = v"
      unfolding list_of_fset_def
      by (metis (mono_tags, lifting) exists_fset_of_list fimage.rep_eq fimageE fset_of_list.rep_eq 
          set_map someI_ex)
    then show \<open>v \<in> f ` fset A\<close>
      by blast
  qed
qed

lemma equiv_prop_sema1_sema2:
  \<open>(\<forall>F\<in>AF_proj_to_formula_set_set \<N>. \<exists>f\<in>F. formula_semantics (to_valuation J) f) \<longleftrightarrow>
   (\<forall>F\<in>AF_proj_to_formula_set \<N>. formula_semantics (to_valuation J) F)\<close>
  using equiv_prop_entail2_sema2 equiv_prop_entail2_sema by auto


lemma equiv_enabled_assertions_sema:
  \<open>(enabled_set \<N> J) \<longleftrightarrow> (\<forall>F\<in>AF_assertions_to_formula_set \<N>. formula_semantics (to_valuation J) F)\<close>
  unfolding enabled_projection_def enabled_def enabled_set_def
proof
  assume enab_N: \<open>\<forall>\<C>\<in>\<N>. fset (A_of \<C>) \<subseteq> total_strip J\<close> 
  show \<open>\<forall>F\<in>AF_assertions_to_formula_set \<N>. formula_semantics (to_valuation J) F\<close>
  proof
    fix F
    assume F_in: \<open>F \<in> AF_assertions_to_formula_set \<N>\<close>
    then obtain \<C> where \<C>_in: \<open>\<C> \<in> \<N>\<close> and 
      F_from_\<C>: \<open>F = BigAnd (map sign_to_atomic_formula (list_of_fset (A_of \<C>)))\<close>
      unfolding AF_assertions_to_formula_def AF_assertions_to_formula_set_def by auto
    have \<open>\<forall>f\<in>set (map sign_to_atomic_formula (list_of_fset (A_of \<C>))).
      formula_semantics (to_valuation J) f\<close>
    proof
      fix f
      assume f_in: \<open>f \<in> set (map sign_to_atomic_formula (list_of_fset (A_of \<C>)))\<close>
      define L where \<open>L = (list_of_fset (A_of \<C>))\<close>
      then obtain a v where f_is: \<open>sign_to_atomic_formula a = f\<close> and a_in: \<open>a \<in> set L\<close>
        and v_is: \<open>to_V a = v\<close>
        using f_in by auto
      have \<open>a \<in> fset (A_of \<C>)\<close>
        using a_in unfolding L_def by (smt (verit, ccfv_threshold) exists_fset_of_list
            fset_of_list.rep_eq list_of_fset_def someI_ex)
      then have a_in: \<open>a \<in> total_strip J\<close>
        using enab_N \<C>_in by blast
      consider (Pos) "a = Pos v" | (Neg) \<open>a = Neg v\<close>
        using v_is is_Neg_to_V is_Pos_to_V by blast
      then show \<open>formula_semantics (to_valuation J) f\<close>
      proof cases
        case Pos
        then have \<open>f = Atom v\<close> using f_is by auto
        then show ?thesis
          using a_in unfolding to_valuation_def belong_to_total_def belong_to_def
          by (simp add: Pos)
      next
        case Neg
        then have \<open>f = Not (Atom v)\<close> using f_is by auto
        then show ?thesis
          using a_in Neg to_valuation_def val_strip_neg by force
      qed
    qed
    then show \<open>formula_semantics (to_valuation J) F\<close>
      using BigAnd_semantics[of "to_valuation J"
          "map sign_to_atomic_formula (list_of_fset (A_of \<C>))"] F_from_\<C> by blast
  qed
next
  assume F_sat: \<open>\<forall>F\<in>AF_assertions_to_formula_set \<N>. formula_semantics (to_valuation J) F\<close>
  have \<open>\<forall>\<C>\<in>\<N>. \<forall>a\<in>fset (A_of \<C>). a \<in> total_strip J\<close>
  proof clarify
    fix \<C> a
    assume 
      \<C>_in: \<open>\<C> \<in> \<N>\<close> and
      a_in: \<open>a \<in> fset (A_of \<C>)\<close>
    define F where \<open>F = AF_assertions_to_formula \<C>\<close>
    then have \<open>F \<in> AF_assertions_to_formula_set \<N>\<close>
      unfolding AF_assertions_to_formula_set_def using \<C>_in by blast
    then have \<open>formula_semantics (to_valuation J) F\<close> using F_sat by blast
    then have all_f_sat: \<open>\<forall>f\<in>set (map sign_to_atomic_formula (list_of_fset (A_of \<C>))).
      formula_semantics (to_valuation J) f\<close>
      using BigAnd_semantics[of "to_valuation J"] unfolding F_def AF_assertions_to_formula_def
      by simp
    define f where \<open>f = sign_to_atomic_formula a\<close>
    then have \<open>f \<in> set (map sign_to_atomic_formula (list_of_fset (A_of \<C>)))\<close>
      using a_in fset_map2 by fastforce
    then have f_sat: \<open>formula_semantics (to_valuation J) f\<close>
      using all_f_sat by auto
    then show \<open>a \<in> total_strip J\<close>
      using f_def unfolding to_valuation_def
      by (metis f_sat belong_to.rep_eq belong_to_total.rep_eq formula_semantics.simps(1)
          formula_semantics.simps(3) sign_to_atomic_formula.elims val_strip_neg)
  qed
  then show \<open>\<forall>\<C>\<in>\<N>. fset (A_of \<C>) \<subseteq> total_strip J\<close> by blast
qed

definition sound_propositional_model :: "'v total_interpretation \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool"
  (infix "\<Turnstile>s\<^sub>p" 50) where
  \<open>J \<Turnstile>s\<^sub>p \<N> \<equiv> (bot \<notin> ((enabled_projection (propositional_projection \<N>) J)) \<or>
    \<not> sound_consistent J)\<close>

definition propositionally_unsatisfiable :: "('f, 'v) AF set \<Rightarrow> bool" where
  \<open>propositionally_unsatisfiable \<N> \<equiv> \<forall>J. \<not> (J \<Turnstile>\<^sub>p \<N>)\<close>

(* TODO: move in Sema? *)
lemma unsat_simp: 
  assumes 
    \<open>\<not> sat (S' \<union> S::'v formula set)\<close>
    \<open>sat S'\<close>
    \<open>\<Union> (atoms ` S') \<inter> \<Union> (atoms ` S) = {}\<close>
  shows
    \<open>\<not> sat S\<close>
  unfolding sat_def
proof
  assume contra: \<open>\<exists>\<A>. \<forall>F\<in>S. formula_semantics \<A> F\<close>
  then obtain \<A>S where AS_is: \<open>\<forall>F\<in>S. formula_semantics \<A>S F\<close> by blast
  obtain \<A>F where AF_is: \<open>\<forall>F\<in>S'. formula_semantics \<A>F F\<close> using assms(2) unfolding sat_def by blast
  define \<A> where \<open>\<A> = (\<lambda>a. if a \<in> \<Union> (atoms ` S') then \<A>F a else \<A>S a)\<close>
  have \<open>\<forall>F\<in>S'. formula_semantics \<A> F\<close>
    using AF_is relevant_atoms_same_semantics unfolding \<A>_def
    by (smt (verit, best) UN_I)
  moreover have \<open>\<forall>F\<in>S. formula_semantics \<A> F\<close>
    using AS_is relevant_atoms_same_semantics assms(3) unfolding \<A>_def
    by (smt (verit, del_insts) Int_iff UN_I empty_iff)
  ultimately have \<open>\<forall>F'\<in>(S'\<union>S). formula_semantics \<A> F'\<close> by blast
  then show False
    using assms(1) unfolding sat_def by blast
qed

lemma proj_to_form_un: \<open>AF_proj_to_formula_set (A \<union> B) = 
  AF_proj_to_formula_set A \<union> AF_proj_to_formula_set B\<close>
  unfolding AF_proj_to_formula_set_def propositional_projection_def by blast

lemma unsat_AF_simp: 
  assumes 
    \<open>\<not> sat (AF_proj_to_formula_set (S' \<union> S))\<close>
    \<open>sat (AF_proj_to_formula_set S')\<close>
    \<open>\<Union> (atoms ` (AF_proj_to_formula_set S')) \<inter> \<Union> (atoms ` (AF_proj_to_formula_set S)) = {}\<close>
  shows
    \<open>\<not> sat (AF_proj_to_formula_set S)\<close>
  using unsat_simp assms proj_to_form_un by metis

lemma set_list_of_fset[simp]: \<open>set (list_of_fset A) = fset A\<close>
  unfolding list_of_fset_def
  by (smt (verit, del_insts) exists_fset_of_list fset_of_list.rep_eq someI_ex)

lemma vars_in_assertion: \<open>to_V ` (set (list_of_fset A)) = to_V ` (fset A)\<close>
  by simp

lemma atoms_bigor: \<open>atoms (BigOr L) = \<Union> (atoms ` (set L))\<close>
  unfolding BigOr_def by (induction L) auto

lemma atoms_neg: \<open>atoms (sign_to_atomic_formula (neg A)) = atoms (sign_to_atomic_formula A)\<close>
  by (metis formula.simps(92) neg.elims sign_to_atomic_formula.simps(1)
      sign_to_atomic_formula.simps(2))

find_theorems set  list_of_fset

lemma set_maps_list_of_fset: \<open>set (map sign_to_atomic_formula (map neg (list_of_fset A))) = 
  sign_to_atomic_formula ` neg ` fset A\<close>
  using set_map by auto

lemma atoms_to_V_mono: \<open>atoms (sign_to_atomic_formula A) = {to_V A}\<close>
  by (metis formula.set(1) formula.set(3) sign_to_atomic_formula.simps(1)
      sign_to_atomic_formula.simps(2) to_V.elims)

lemma atoms_to_V: \<open>\<Union>(atoms ` sign_to_atomic_formula ` A) = to_V ` A\<close>
proof -
  have \<open>\<Union>(atoms ` sign_to_atomic_formula ` A) = \<Union>{{to_V a} |a. a \<in> A}\<close>
    using atoms_to_V_mono by auto
  also have \<open>... = to_V ` A\<close>
    by blast
  finally show \<open>\<Union>(atoms ` sign_to_atomic_formula ` A) = to_V ` A\<close> .
qed

lemma atoms_to_V_AF: \<open>atoms (AF_to_formula (Pair C A)) = to_V ` (fset A)\<close>
proof -
  have \<open>atoms (AF_to_formula (Pair C A)) = \<Union> (atoms ` sign_to_atomic_formula ` fset A)\<close>
    using atoms_bigor set_maps_list_of_fset atoms_neg unfolding AF_to_formula_def
    by (smt (z3) AF.sel(2) image_iff subsetI subset_antisym)
  also have \<open>... = to_V ` (fset A)\<close>
    using atoms_to_V by auto
  ultimately show \<open>atoms (AF_to_formula (Pair C A)) = to_V ` (fset A)\<close> by simp
qed

lemma atoms_to_V_A_of: \<open>atoms (AF_to_formula \<C>) = to_V ` (fset (A_of \<C>))\<close>
  using atoms_to_V_AF
  by (metis AF.collapse)

lemma atoms_to_V_un: \<open>\<Union>(atoms ` AF_to_formula ` \<S>) = \<Union>{to_V ` fset A |A. A \<in> A_of ` \<S>}\<close>
proof -
  have \<open>(x \<in> (atoms ` AF_to_formula ` \<S>)) = (x \<in> {to_V ` (fset A) |A. A \<in> A_of ` \<S>})\<close> for x
    using atoms_to_V_A_of by blast
  then show ?thesis
    by (smt (verit, ccfv_SIG) Collect_cong Sup_set_def UNION_singleton_eq_range mem_Collect_eq)
qed

lemma atoms_simp: \<open>\<Union> (atoms ` (AF_proj_to_formula_set S)) = to_V ` \<Union> (fset ` (A_of ` (proj\<^sub>\<bottom> S)))\<close>
proof -
  have \<open>\<Union> (atoms ` (AF_proj_to_formula_set S)) = \<Union>{to_V ` fset A | A. A \<in> A_of ` (proj\<^sub>\<bottom> S)}\<close>
    unfolding AF_proj_to_formula_set_def using atoms_to_V_un by auto
  also have \<open>... = to_V ` \<Union> (fset ` (A_of ` (proj\<^sub>\<bottom> S)))\<close>
    by blast
  finally show ?thesis .
qed

lemma val_from_interp: \<open>\<forall>\<A>. \<exists>J. \<A> = to_valuation J\<close>
proof
  fix \<A>
  define J_bare where \<open>J_bare = {Pos a |(a::'v). \<A> a} \<union> {Neg a |a. \<not> \<A> a}\<close>
  then have interp_J_bare: \<open>is_interpretation J_bare\<close>
    unfolding is_interpretation_def
    by force
  then have total_J_bare: \<open>total (interp_of J_bare)\<close>
    unfolding total_def using J_bare_def
    by (metis (mono_tags, lifting) Abs_propositional_interpretation_inverse Un_iff belong_to.rep_eq
        mem_Collect_eq to_V.simps)
  define J where \<open>J = total_interp_of J_bare\<close>
  have \<open>\<A> = to_valuation J\<close>
  proof
    fix a::'v
    show \<open>\<A> a = to_valuation J a\<close>
      using J_def J_bare_def Abs_propositional_interpretation_inverse 
        Abs_total_interpretation_inverse interp_J_bare total_J_bare to_valuation_def val_strip_pos
      by fastforce
  qed
  then show \<open>\<exists>J. \<A> = to_valuation J\<close>
    by fast
qed

lemma interp_from_val: \<open>\<forall>J. \<exists>\<A>. \<A> = to_valuation J\<close>
  unfolding to_valuation_def by auto


(* TODO: move in Compactness? *)
lemma compactness_unsat: \<open>(\<not> sat (S::'v formula set)) \<longleftrightarrow> (\<exists>s\<subseteq>S. finite s \<and> \<not> sat s)\<close>
  using compactness[of S] unfolding fin_sat_def by blast

lemma never_enabled_finite_subset: 
  \<open>\<forall>J. \<not> enabled_set \<N> J \<Longrightarrow> \<exists>\<N>'\<subseteq>\<N>. finite \<N>' \<and> (\<forall>J. \<not> enabled_set \<N>' J)\<close>
proof -
  assume not_enab_N: \<open>\<forall>J. \<not> enabled_set \<N> J\<close>
  then have \<open>\<not> sat (AF_assertions_to_formula_set \<N>)\<close>
    unfolding sat_def using equiv_enabled_assertions_sema[of \<N>] val_from_interp
    by metis
  then obtain S' where S'_sub: \<open>S' \<subseteq> AF_assertions_to_formula ` \<N>\<close> and S'_fin: \<open>finite S'\<close> and
    S'_unsat: \<open>\<not> sat S'\<close>
    using compactness_unsat unfolding AF_assertions_to_formula_set_def by metis
  obtain \<N>' where N'_sub: \<open>\<N>' \<subseteq> \<N>\<close> and N'_fin: \<open>finite \<N>'\<close>
    and S'_im: \<open>S' = AF_assertions_to_formula ` \<N>'\<close>
    using finite_subset_image[OF S'_fin S'_sub] by blast
  have not_enab_N': \<open>\<forall>J. \<not> enabled_set \<N>' J\<close>
    using equiv_enabled_assertions_sema[of \<N>'] S'_unsat S'_im interp_from_val 
    unfolding sat_def AF_assertions_to_formula_set_def by blast
  then show \<open>\<exists>\<N>' \<subseteq> \<N>. finite \<N>' \<and> (\<forall>J. \<not> enabled_set \<N>' J)\<close>
    using N'_sub N'_fin by auto
qed


lemma compactness_AF_proj: \<open>(\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>) \<longleftrightarrow> (\<exists>\<N>'\<subseteq>\<N>. finite \<N>' \<and> (\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>'))\<close>
proof -
  define \<F> where \<open>\<F> = AF_proj_to_formula_set \<N>\<close>
  have \<open>(\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>) \<longleftrightarrow> (\<forall>J. \<exists>F\<in>\<F>. \<not> formula_semantics (to_valuation J) F)\<close>
    by (simp add: \<F>_def equiv_prop_entail2_sema2)
  also have 
    \<open>(\<forall>J. \<exists>F\<in>\<F>. \<not> formula_semantics (to_valuation J) F) \<longleftrightarrow> (\<forall>\<A>. \<exists>F\<in>\<F>. \<not> formula_semantics \<A> F)\<close>
    using val_from_interp by metis
  also have \<open>(\<forall>\<A>. \<exists>F\<in>\<F>. \<not> formula_semantics \<A> F) \<longleftrightarrow> (\<not> sat \<F>)\<close>
    unfolding sat_def by blast
  also have \<open>(\<not> sat \<F>) \<longleftrightarrow> (\<exists>\<F>'\<subseteq>\<F>. finite \<F>' \<and> \<not> sat \<F>')\<close>
    using compactness_unsat[of \<F>] .
  also have \<open>(\<exists>\<F>'\<subseteq>\<F>. finite \<F>' \<and> \<not> sat \<F>') \<longleftrightarrow> (\<exists>\<F>'\<subseteq>\<F>. finite \<F>' \<and> (\<forall>\<A>. \<exists>F\<in>\<F>'. \<not> formula_semantics \<A> F))\<close>
    unfolding sat_def by auto
  also have \<open>... \<longleftrightarrow> (\<exists>\<F>'\<subseteq>\<F>. finite \<F>' \<and> (\<forall>J. \<exists>F\<in>\<F>'. \<not> formula_semantics (to_valuation J) F))\<close>
    by (metis val_from_interp)
  also have \<open>... \<longleftrightarrow> (\<exists>\<N>'\<subseteq>\<N>. finite \<N>' \<and> (\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>'))\<close>
  proof
    assume \<open>\<exists>\<F>'\<subseteq>\<F>. finite \<F>' \<and> (\<forall>J. \<exists>F\<in>\<F>'. \<not> formula_semantics (to_valuation J) F)\<close>
    then obtain \<F>' where F'_sub: \<open>\<F>'\<subseteq>\<F>\<close> and F'_fin: \<open>finite \<F>'\<close> and
      F'_unsat: \<open>\<forall>J. \<exists>F\<in>\<F>'. \<not> formula_semantics (to_valuation J) F\<close>
      by auto
    have \<open>\<forall>F\<in>\<F>'. \<exists>\<C>\<in>(proj\<^sub>\<bottom> \<N>). AF_to_formula \<C> = F\<close>
      using F'_sub \<F>_def unfolding AF_proj_to_formula_set_def by blast
    then obtain \<N>' where F'_is_map: \<open>\<F>' = AF_to_formula ` \<N>'\<close> and N'_in_proj: \<open>\<N>' \<subseteq> proj\<^sub>\<bottom> \<N>\<close> and
      N'_fin: \<open>finite \<N>'\<close>
      using F'_fin
      by (metis AF_proj_to_formula_set_def F'_sub \<F>_def finite_subset_image)
    have \<open>proj\<^sub>\<bottom> \<N>' = \<N>'\<close>                               
      using N'_in_proj unfolding propositional_projection_def by blast
    then have F'_is: \<open>\<F>' = AF_proj_to_formula_set \<N>'\<close>
      unfolding AF_proj_to_formula_set_def using F'_is_map by simp
    have N'_sub: \<open>\<N>' \<subseteq> \<N>\<close>
      using prop_proj_in N'_in_proj by auto
    have N'_unsat: \<open>\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>'\<close>
      using equiv_prop_entail2_sema2[of _ \<N>'] F'_is F'_unsat 
      by blast
    show \<open>\<exists>\<N>'\<subseteq>\<N>. finite \<N>' \<and> (\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>')\<close>
      using N'_sub N'_fin N'_unsat by blast
  next
    assume \<open>\<exists>\<N>'\<subseteq>\<N>. finite \<N>' \<and> (\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>')\<close>
    then obtain \<N>' where N'_sub: \<open>\<N>' \<subseteq> \<N>\<close> and N'_fin: \<open>finite \<N>'\<close> and N'_unsat: \<open>\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>'\<close>
      by auto
    define \<F>' where \<open>\<F>' = AF_proj_to_formula_set \<N>'\<close>
    then have \<open>\<F>' \<subseteq> \<F>\<close>
      using N'_sub unfolding \<F>_def AF_proj_to_formula_set_def propositional_projection_def by blast
    moreover have \<open>finite \<F>'\<close>
      using \<F>'_def N'_fin unfolding AF_proj_to_formula_set_def propositional_projection_def by simp
    moreover have \<open>\<forall>J. \<exists>F\<in>\<F>'. \<not> formula_semantics (to_valuation J) F\<close>
      using N'_unsat equiv_prop_entail2_sema2[of _ \<N>'] unfolding \<F>'_def by blast
    ultimately show \<open>\<exists>\<F>'\<subseteq>\<F>. finite \<F>' \<and> (\<forall>J. \<exists>F\<in>\<F>'. \<not> formula_semantics (to_valuation J) F)\<close>
      by auto
  qed
  finally show \<open>(\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>) \<longleftrightarrow> (\<exists>\<N>'\<subseteq>\<N>. finite \<N>' \<and> (\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<N>'))\<close>
    .
qed

lemma prop_unsat_compactness:
  \<open>propositionally_unsatisfiable A \<Longrightarrow> \<exists> B \<subseteq> A. finite B \<and> propositionally_unsatisfiable B\<close>
  by (meson compactness_AF_proj equiv_prop_entails propositionally_unsatisfiable_def)

definition \<E>_from :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> where
  \<open>\<E>_from \<N> \<equiv> {Pair bot {|neg a|} |a. \<exists>\<C>\<in>\<N>. a \<in> fset (A_of \<C>)}\<close>

lemma prop_proj_\<E>_from: \<open>proj\<^sub>\<bottom> (\<E>_from \<N>) = \<E>_from \<N>\<close>
  unfolding propositional_projection_def \<E>_from_def by auto

lemma prop_proj_sub: \<open>proj\<^sub>\<bottom> \<N> = \<N> \<Longrightarrow> \<N>' \<subseteq> \<N> \<Longrightarrow> proj\<^sub>\<bottom> \<N>' = \<N>'\<close>
  unfolding propositional_projection_def by blast

lemma prop_proj_distrib: \<open>proj\<^sub>\<bottom> (A \<union> B) = proj\<^sub>\<bottom> A \<union> proj\<^sub>\<bottom> B\<close>
  unfolding propositional_projection_def by blast

lemma v_in_\<E>: \<open>Pair bot {|Pos v|} \<in> \<E>_from \<N> \<or> Pair bot {|Neg v|} \<in> \<E>_from \<N> \<Longrightarrow>
  \<exists>\<C>\<in>\<N>. v \<in> to_V ` (fset (A_of \<C>))\<close>
  unfolding \<E>_from_def by (smt (verit, ccfv_threshold) AF.sel(2) fthe_felem_eq image_iff
    mem_Collect_eq neg.simps(1) neg.simps(2) to_V.elims to_V.simps(1) to_V.simps(2))

lemma a_in_\<E>: \<open>\<exists>J. J \<Turnstile>\<^sub>p2 \<E>_from \<N> \<Longrightarrow> Pair bot {|neg a|} \<in> \<E>_from \<N> \<Longrightarrow>
  \<not> (Pair bot {|a|} \<in> \<E>_from \<N>)\<close>
proof
  assume
    e_sat: \<open>\<exists>J. J \<Turnstile>\<^sub>p2 \<E>_from \<N>\<close>  and
    neg_a_in: \<open>Pair bot {|neg a|} \<in> \<E>_from \<N>\<close> and
    a_in: \<open>AF.Pair bot {|a|} \<in> \<E>_from \<N>\<close>
  obtain J where J_sat_e: \<open>J \<Turnstile>\<^sub>p2 \<E>_from \<N>\<close>
    using e_sat by blast
  have neg_a_in_J: \<open>neg a \<in> total_strip J\<close>
    using a_in J_sat_e unfolding propositional_model2_def \<E>_from_def enabled_projection_def
      propositional_projection_def enabled_def by (smt (verit, ccfv_SIG) AF.collapse AF.inject
      bot_fset.rep_eq empty_iff empty_subsetI finsert.rep_eq insert_subset mem_Collect_eq
      neg.simps(1) neg.simps(2) to_V.elims val_strip_neg val_strip_pos)
  have \<open>neg a \<in> total_strip J \<Longrightarrow> \<not> J \<Turnstile>\<^sub>p2 \<E>_from \<N>\<close>
    using neg_a_in J_sat_e enabled_def
      enabled_projection_def prop_proj_\<E>_from propositional_model2_def by fastforce
  then show False
    using neg_a_in_J J_sat_e by blast
qed

lemma equiv_\<E>_enabled_\<N>:
  shows \<open>J \<Turnstile>\<^sub>p2 \<E>_from \<N> \<longleftrightarrow> enabled_set \<N> J\<close>
  unfolding propositional_model2_def enabled_set_def enabled_def propositional_projection_def
    enabled_projection_def
proof
  assume empty_proj_E: \<open>{} = {F_of \<C> |\<C>. \<C> \<in> {\<C> \<in> \<E>_from \<N>. F_of \<C> = bot} \<and>
    fset (A_of \<C>) \<subseteq> total_strip J}\<close>
  have \<open>\<forall>\<C>\<in>\<E>_from \<N>. F_of \<C> = bot\<close> using \<E>_from_def[of \<N>] by auto
  then have a_in_E: \<open>\<forall>\<C>\<in>\<E>_from \<N>. \<exists>a\<in>fset (A_of \<C>). a \<notin> total_strip J\<close>
    using empty_proj_E by blast
  then have \<open>\<forall>\<C>\<in>\<E>_from \<N>. \<forall>a\<in>fset (A_of \<C>). a \<notin> total_strip J\<close>
    unfolding \<E>_from_def by fastforce
  moreover have \<open>\<forall>\<C>\<in>\<N>. \<forall>a\<in>fset (A_of \<C>). \<exists>\<C>'\<in>\<E>_from \<N>. neg a \<in> fset (A_of \<C>')\<close>
    unfolding \<E>_from_def by fastforce
  ultimately have \<open>\<forall>\<C>\<in>\<N>. \<forall>a\<in>fset (A_of \<C>). a \<in> total_strip J\<close>
    by fastforce
  then show \<open>\<forall>\<C>\<in>\<N>. fset (A_of \<C>) \<subseteq> total_strip J\<close>
    by blast
next
  assume enabled_\<C>: \<open>\<forall>\<C>\<in>\<N>. fset (A_of \<C>) \<subseteq> total_strip J\<close>
  have \<open>\<forall>\<C>\<in>\<E>_from \<N>. \<forall>a\<in>fset (A_of \<C>). \<exists>\<C>'\<in>\<N>. neg a \<in> fset (A_of \<C>')\<close>
    unfolding \<E>_from_def
    by (smt (verit) AF.exhaust_sel AF.inject bot_fset.rep_eq empty_iff finsert.rep_eq insertE
        is_Pos.cases mem_Collect_eq neg.simps)
  then have \<open>\<forall>\<C>\<in>\<E>_from \<N>. \<forall>a\<in>fset (A_of \<C>). a \<notin> total_strip J\<close>
    using enabled_\<C> by (meson belong_to.rep_eq neg_prop_interp subsetD)
  then have \<open>\<forall>\<C>\<in>\<E>_from \<N>. (\<not> fset (A_of \<C>) \<subseteq> total_strip J)\<close>
    using \<E>_from_def by fastforce
  then show \<open>{} = {F_of \<C> |\<C>. \<C> \<in> {\<C> \<in> \<E>_from \<N>. F_of \<C> = bot} \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
    by blast
qed

definition AF_entails :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>A\<^sub>F" 50) where
  \<open>AF_entails \<M> \<N> \<equiv> (\<forall>J. (enabled_set \<N> J \<longrightarrow> \<M> proj\<^sub>J J \<Turnstile> F_of ` \<N>))\<close>

lemma prop_unsat_to_AF_entails_bot: \<open>propositionally_unsatisfiable \<M> \<Longrightarrow> \<M> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
proof -
  assume prop_unsat_\<M>: \<open>propositionally_unsatisfiable \<M>\<close>
  then show \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    unfolding AF_entails_def
  proof (intro allI impI)
    fix J
    assume \<open>enabled_set {to_AF bot} J\<close>
    have \<open>bot \<in> (proj\<^sub>\<bottom> \<M>) proj\<^sub>J J\<close>
      using prop_unsat_\<M>
      unfolding propositionally_unsatisfiable_def propositional_model_def
      by blast
    then have \<open>bot \<in> \<M> proj\<^sub>J J\<close>
      using enabled_projection_def prop_proj_in
      by fastforce
    then have \<open>\<M> proj\<^sub>J J \<Turnstile> {bot}\<close>
      using bot_entails_empty entails_subsets
      by (meson empty_subsetI insert_subset)
    then show \<open>\<M> proj\<^sub>J J \<Turnstile> F_of ` {to_AF bot}\<close>
      by (auto simp add: F_of_to_AF)
  qed
qed

lemma \<open>enabled_set {} J\<close>
  unfolding enabled_set_def by blast

lemma \<open>(\<forall>J. \<not> (enabled_set \<N> J)) \<Longrightarrow> (\<M> \<Turnstile>\<^sub>A\<^sub>F \<N>)\<close>
  unfolding AF_entails_def by blast
  
definition AF_entails_sound :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool" (infix "\<Turnstile>s\<^sub>A\<^sub>F" 50) where
  \<open>AF_entails_sound \<M> \<N> \<equiv> (\<forall>J. (enabled_set \<N> J \<longrightarrow>
  sound_cons.entails_neg ((fml_ext ` (total_strip J)) \<union> (Pos ` (\<M> proj\<^sub>J J))) (Pos ` F_of ` \<N>)))\<close>

lemma distrib_proj: \<open>\<M> \<union> \<N> proj\<^sub>J J = (\<M> proj\<^sub>J J) \<union> (\<N> proj\<^sub>J J)\<close>
  unfolding enabled_projection_def by auto

lemma distrib_proj_singleton: \<open>\<M> \<union> {\<C>} proj\<^sub>J J = (\<M> proj\<^sub>J J) \<union> ({\<C>} proj\<^sub>J J)\<close>
  unfolding enabled_projection_def by auto

lemma enabled_union2: \<open>enabled_set (\<M> \<union> \<N>) J \<Longrightarrow> enabled_set \<N> J\<close>
  unfolding enabled_set_def by blast

lemma enabled_union1: \<open>enabled_set (\<M> \<union> \<N>) J \<Longrightarrow> enabled_set \<M> J\<close>
  unfolding enabled_set_def by blast

lemma finite_subset_image_strong:
  assumes "finite U" and
    "(\<forall>C \<in> U. (\<exists>D \<in> W. P D = C \<and> Q D))"
  shows "\<exists>W'\<subseteq>W. finite W' \<and> U = P ` W' \<and> (\<forall>D'\<in> W'. Q D')"
  using assms
proof (induction U rule: finite_induct)
  case empty
  then show ?case by blast
next
  case (insert D' U)
  then obtain C' W'' where wpp_and_cp_assms: "W'' \<subseteq> W" "finite W''" "U = P ` W''" "\<forall>a \<in> W''. Q a"
    "C' \<in> W" "P C' = D'" "Q C'"
    by auto
  define W' where "W' = insert C' W''"
  then have \<open>(insert C' W') \<subseteq>W \<and> finite (insert C' W') \<and> insert D' U = P ` (insert C' W') \<and>
             (\<forall>a\<in>(insert C' W'). Q a)\<close>
    using wpp_and_cp_assms by blast
  then show ?case
    by blast
qed

lemma all_to_ex: \<open>\<forall>x. P x \<Longrightarrow> \<exists>x. P x\<close> for P by blast

lemma three_skolems:
  assumes \<open>\<And>U. P U  \<Longrightarrow> \<exists>X Y Z. Q U X Y Z\<close>
  shows \<open>(\<And>X_of Y_of Z_of. (\<And>U. P U \<Longrightarrow> Q U (X_of U) (Y_of U) (Z_of U)) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  using assms
  by metis

lemma finite_subset_with_prop:
  assumes \<open>\<exists>Js. A = f ` Js \<and> (\<forall>J\<in>Js. P J)\<close> and
    \<open>finite C\<close> and
    \<open>B = C \<inter> A\<close>
  shows \<open>\<exists>Js. B = f ` Js \<and> (\<forall>J\<in>Js. P J) \<and> finite Js\<close>
proof -
  have B_fin: \<open>finite B\<close> using assms(2) assms(3) by simp
  have B_sub: \<open>B \<subseteq> A\<close> using assms(2) assms(3) by auto
  obtain Js where A_is: \<open>A = f ` Js\<close> and P_Js: \<open>\<forall>J\<in>Js. P J\<close>
    using assms(1) by blast
  then have \<open>\<forall>b\<in>B. \<exists>J\<in>Js. b = f J \<and> P J\<close>
    using B_sub by blast
  then obtain Js' where \<open>B = f ` Js'\<close> and \<open>finite Js'\<close> \<open>\<forall>J\<in>Js'. P J\<close>
    using B_fin by (smt (verit, ccfv_threshold) B_sub assms(1) finite_subset_image subsetD)
  then show \<open>\<exists>Js. B = f ` Js \<and> (\<forall>J\<in>Js. P J) \<and> finite Js\<close>
    by blast
qed

lemma to_V_neg [simp]: \<open>to_V (neg a) = to_V a\<close>
  by (metis is_Neg_to_V is_Pos_to_V neg.simps(1) neg.simps(2) to_V.simps(1) to_V.simps(2))

  (* Splitting report Lemma 4, 1/2 *)
sublocale AF_cons_rel: consequence_relation "to_AF bot" AF_entails
proof
  show \<open>{to_AF bot} \<Turnstile>\<^sub>A\<^sub>F {}\<close>
    unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def
    using bot_entails_empty by simp
next
  fix \<C>
  show \<open>{\<C>} \<Turnstile>\<^sub>A\<^sub>F {\<C>}\<close>
    unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
    using entails_reflexive by simp
next
  fix \<M> \<N> \<P> \<Q>
  assume m_in_n: \<open>\<M> \<subseteq> \<N>\<close> and
    p_in_q: \<open>\<P> \<subseteq> \<Q>\<close> and
    m_entails_p: \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F \<P>\<close>
  show \<open>\<N> \<Turnstile>\<^sub>A\<^sub>F \<Q>\<close>
    unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
  proof (rule allI, rule impI)
    fix J
    assume q_enabled: \<open>\<forall>\<C>\<in>\<Q>. fset (A_of \<C>) \<subseteq> total_strip J\<close>
    have \<open>{F_of \<C> |\<C>. \<C> \<in> \<M> \<and> fset (A_of \<C>) \<subseteq> total_strip J} \<subseteq> 
      {F_of \<C> |\<C>. \<C> \<in> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
      using m_in_n by blast
    moreover have \<open>F_of ` \<P> \<subseteq> F_of ` \<Q>\<close>
      using p_in_q by blast
    ultimately show \<open>{F_of \<C> |\<C>. \<C> \<in> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J} \<Turnstile> F_of ` \<Q>\<close>
      using m_entails_p  entails_subsets
      unfolding to_AF_def AF_entails_def enabled_def enabled_projection_def enabled_set_def
      by (metis (mono_tags, lifting) q_enabled p_in_q subset_iff)
  qed
next
  fix \<M> \<N> \<C> \<M>' \<N>'
  assume
    entails_c: \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F \<N> \<union> {\<C>}\<close> and
    c_entails: \<open>\<M>' \<union> {\<C>} \<Turnstile>\<^sub>A\<^sub>F \<N>'\<close>
  show \<open>\<M> \<union> \<M>' \<Turnstile>\<^sub>A\<^sub>F \<N> \<union> \<N>'\<close>
    unfolding AF_entails_def
  proof (intro allI impI)
    fix J
    assume enabled_n: \<open>enabled_set (\<N> \<union> \<N>') J\<close>
    {
      assume enabled_c: \<open>enabled_set {\<C>} J\<close>
      then have proj_enabled_c: \<open>{\<C>} proj\<^sub>J J = {F_of \<C>}\<close> 
        unfolding enabled_projection_def using enabled_set_def by blast 
      have cut_hyp1: \<open>\<M> proj\<^sub>J J \<Turnstile> F_of ` \<N> \<union> {F_of \<C>}\<close>
        using entails_c enabled_n enabled_c unfolding AF_entails_def by (simp add: enabled_set_def)
      have \<open>(\<M>' \<union> {\<C>}) proj\<^sub>J J \<Turnstile> F_of ` \<N>'\<close>
        using c_entails enabled_union2[of \<N> \<N>' J, OF enabled_n] unfolding AF_entails_def by simp
      then have cut_hyp2: \<open>(\<M>' proj\<^sub>J J) \<union> {F_of \<C>} \<Turnstile> F_of ` \<N>'\<close>
        using proj_enabled_c distrib_proj_singleton by metis
      have \<open>\<M> \<union> \<M>' proj\<^sub>J J \<Turnstile> F_of ` (\<N> \<union> \<N>')\<close>
        using entails_cut[OF cut_hyp1 cut_hyp2] distrib_proj by (simp add: image_Un) 
    }
    moreover
    {
      assume not_enabled_c: \<open>\<not> enabled_set {\<C>} J\<close>
      then have \<open>\<M>' \<union> {\<C>} proj\<^sub>J J = \<M>' proj\<^sub>J J\<close>
        unfolding enabled_projection_def enabled_set_def by auto
      then have \<open>\<M>' proj\<^sub>J J \<Turnstile> F_of ` \<N>'\<close>
        using c_entails enabled_n unfolding AF_entails_def by (metis enabled_union2) 
      then have \<open>\<M> \<union> \<M>' proj\<^sub>J J \<Turnstile> F_of ` (\<N> \<union> \<N>')\<close>
        using entails_subsets by (metis distrib_proj image_Un sup.cobounded2) 
    }
    ultimately show \<open>\<M> \<union> \<M>' proj\<^sub>J J \<Turnstile> F_of ` (\<N> \<union> \<N>')\<close>
      by blast 
    qed
next
  fix \<M> \<N>
  assume m_entails_n: \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F \<N>\<close>
  consider (NotEnabled) \<open>\<forall>J. \<not> enabled_set \<N> J\<close> | (Enabled) \<open>\<exists>J. enabled_set \<N> J\<close> by blast
  then show \<open>\<exists>M' N'. M' \<subseteq> \<M> \<and> N' \<subseteq> \<N> \<and> finite M' \<and> finite N' \<and> M' \<Turnstile>\<^sub>A\<^sub>F N'\<close>
  proof cases
    case NotEnabled
    then obtain \<N>' where N'_sub: \<open>\<N>' \<subseteq> \<N>\<close> and N'_fin: \<open>finite \<N>'\<close> and
      sub_not_enab: \<open>\<forall>J. \<not> enabled_set \<N>' J\<close>
      using never_enabled_finite_subset[of \<N>] by blast
    obtain \<M>' where \<open>\<M>' \<subseteq> \<M>\<close> and \<open>finite \<M>'\<close> and \<open>\<M>' \<Turnstile>\<^sub>A\<^sub>F \<N>'\<close>
      using sub_not_enab unfolding AF_entails_def by blast
    then show ?thesis using N'_sub N'_fin by blast
  next
    case Enabled
    then obtain J' where J'_is: \<open>enabled_set \<N> J'\<close> by auto
    {
      fix J
      assume enabled_N: \<open>enabled_set \<N> J\<close>
      then have \<open>\<M> proj\<^sub>J J \<Turnstile> F_of ` \<N>\<close>
        using m_entails_n unfolding AF_entails_def by simp 
      then obtain M' N' where mp_proj: \<open>M' \<subseteq> \<M> proj\<^sub>J J\<close> and
        np_proj: \<open>N' \<subseteq> F_of ` \<N>\<close> and mp_fin: \<open>finite M'\<close> and np_fin: \<open>finite N'\<close> and
        mp_entails_np: \<open>M' \<Turnstile> N'\<close>
        using entails_compactness by metis
          
      have mp_with_f_of: \<open>\<forall>C \<in> M'. \<exists>\<C> \<in> \<M>. F_of \<C> = C \<and> enabled \<C> J\<close> 
        using mp_proj unfolding enabled_projection_def by blast
      have \<open>\<exists>\<M>'\<subseteq> \<M>. finite \<M>' \<and> M' = F_of ` \<M>' \<and> enabled_set \<M>' J\<close>
        using finite_subset_image_strong[OF mp_fin mp_with_f_of]
        unfolding enabled_set_def by blast
      then have m_fin_subset: \<open>\<exists>\<M>' \<subseteq> \<M>. finite \<M>' \<and> M' = \<M>' proj\<^sub>J J\<close>
        unfolding enabled_projection_def enabled_set_def by blast
          
      have np_with_f_of: \<open>\<forall>C \<in> N'. \<exists>\<C> \<in> \<N>. F_of \<C> = C\<close> 
        using np_proj unfolding enabled_projection_def by blast
      have n_fin_subset: \<open>\<exists>\<N>'\<subseteq> \<N>. finite \<N>' \<and> N' = F_of ` \<N>'\<close>
        using finite_subset_image[OF np_fin np_proj] .
          
      obtain \<M>' \<N>' where m_n_subs: \<open>\<M>' \<subseteq> \<M>\<close> \<open>\<N>' \<subseteq> \<N>\<close> \<open>finite \<M>'\<close> \<open>finite \<N>'\<close> \<open>M' = \<M>' proj\<^sub>J J\<close>
        \<open>N' = F_of ` \<N>'\<close>
        using m_fin_subset n_fin_subset by blast 
      then have m_proj: \<open>\<M>' proj\<^sub>J J \<Turnstile> F_of ` \<N>'\<close>
        using mp_entails_np by simp
          
      have enabled_N': \<open>enabled_set \<N>' J\<close>
        using enabled_N m_n_subs(2) unfolding enabled_set_def by blast

      let ?\<M>'_sel\<^sub>J = \<open>{\<C>. \<C> \<in> \<M>' \<and> enabled \<C> J}\<close>
      have \<open>?\<M>'_sel\<^sub>J \<subseteq> \<M>'\<close> by simp
      have \<open>finite (\<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> \<N>' \<union> ?\<M>'_sel\<^sub>J})\<close> (*{a. \<exists>\<C>\<in>\<N>'. a \<in> (fset (A_of \<C>)) }\<close>*)
        using m_n_subs(3) m_n_subs(4) by auto
      then obtain A\<^sub>\<J>\<^sub>' where AJ_is: \<open>fset A\<^sub>\<J>\<^sub>' = \<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> \<N>' \<union> ?\<M>'_sel\<^sub>J}\<close>
        by (smt (verit, best) fset_cases mem_Collect_eq)
      define \<J>' where \<open>\<J>' = Pair bot A\<^sub>\<J>\<^sub>' \<close>
      have \<open>\<forall>a\<in>fset (A_of \<J>'). a \<in>\<^sub>t J\<close>
      proof
        fix a
        assume \<open>a \<in> fset (A_of \<J>')\<close>
        then have \<open>\<exists>\<C>\<in>\<N>' \<union> ?\<M>'_sel\<^sub>J. a \<in> fset (A_of \<C>)\<close>
          unfolding \<J>'_def using AJ_is by auto
        then show \<open>a \<in>\<^sub>t J\<close> 
          using enabled_N' unfolding enabled_set_def enabled_def belong_to_total_def belong_to_def
          by auto 
      qed
      moreover have \<open>F_of \<J>' = bot\<close>
        unfolding \<J>'_def
        by simp
      moreover have \<open>\<forall>\<C>\<in>\<N>'. fset (A_of \<C>) \<subseteq> fset (A_of \<J>')\<close>
        using AJ_is \<J>'_def by auto
          
      ultimately have 
        \<open>\<exists>\<M>' \<N>' \<J>'. \<M>' \<subseteq> \<M> \<and> \<N>' \<subseteq> \<N> \<and> finite \<M>' \<and> finite \<N>' \<and> \<M>' proj\<^sub>J J \<Turnstile> F_of ` \<N>' \<and>
        enabled_set \<N>' J \<and> F_of \<J>' = bot \<and> (\<forall>a\<in>fset (A_of \<J>'). a \<in>\<^sub>t J) \<and>
        (fset (A_of \<J>') = \<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> \<N>' \<union> {\<C>. \<C> \<in> \<M>' \<and> enabled \<C> J}})\<close>
        using enabled_N' m_n_subs m_proj AJ_is \<J>'_def
        by (metis (mono_tags, lifting) AF.sel(2))
    }
        
    (* In the pen-and-paper proof, the \<J>'_of function is left vague, but in Isabelle the last
          conjunct that fully defines it is extremelly important. Non trivial is the addition of
          constraints from the enabled formulas in \<M>'_of J, but it is necessary to ensure that
          \<open>(\<M>'_of J') proj\<^sub>J J' \<subseteq> (\<M>'_of J') proj\<^sub>J J\<close> close to the end of the proof*)
    then obtain \<M>'_of \<N>'_of \<J>'_of where 
      fsets_from_J: \<open>enabled_set \<N> J \<Longrightarrow> \<M>'_of J \<subseteq> \<M> \<and> \<N>'_of J \<subseteq> \<N> \<and> finite (\<M>'_of J) \<and> 
      finite (\<N>'_of J) \<and> (\<M>'_of J) proj\<^sub>J J \<Turnstile> F_of ` (\<N>'_of J) \<and> enabled_set (\<N>'_of J) J \<and>
      F_of (\<J>'_of J) = bot \<and> (\<forall>a\<in>fset (A_of (\<J>'_of J)). a \<in>\<^sub>t J) \<and>
      (fset (A_of (\<J>'_of J)) = \<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> (\<N>'_of J) \<union>
        {\<C>. \<C> \<in> (\<M>'_of J) \<and> enabled \<C> J}})\<close> for J 
      using three_skolems[of "\<lambda>U. enabled_set \<N> U" 
        "\<lambda>J \<M>' \<N>' \<J>'. \<M>' \<subseteq> \<M> \<and> \<N>' \<subseteq> \<N> \<and> finite \<M>' \<and> finite \<N>' \<and> \<M>' proj\<^sub>J J \<Turnstile> F_of ` \<N>' \<and> 
        enabled_set \<N>' J \<and> F_of \<J>' = bot \<and> (\<forall>a\<in>fset (A_of \<J>'). a \<in>\<^sub>t J) \<and>
        (fset (A_of \<J>') = \<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> \<N>' \<union> {\<C>. \<C> \<in> \<M>' \<and> enabled \<C> J}})"]
      by force
        
    let ?\<J>'_set = \<open>{\<J>'_of J |J. enabled_set \<N> J}\<close>
    have ex_Js: \<open>\<exists>Js. ?\<J>'_set = \<J>'_of ` Js \<and> (\<forall>J\<in>Js. enabled_set \<N> J)\<close>
      by blast
    have proj_prop_J': \<open>proj\<^sub>\<bottom> ?\<J>'_set = ?\<J>'_set\<close>
      using fsets_from_J unfolding propositional_projection_def by blast
    let ?\<N>'_un = \<open>\<Union>{\<N>'_of J |J. enabled_set \<N> J}\<close>
    let ?\<M>'_un = \<open>\<Union>{{\<C>. \<C> \<in> \<M>'_of J \<and> enabled \<C> J} |J. enabled_set \<N> J}\<close>
    have A_of_enabled: \<open>enabled_set \<N> J \<Longrightarrow> (fset (A_of (\<J>'_of J)) =
      \<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> (\<N>'_of J) \<union> {\<C>. \<C> \<in> (\<M>'_of J) \<and> enabled \<C> J}})\<close> for J
      using fsets_from_J by presburger
    have A_of_eq: \<open>\<Union> (fset ` A_of ` ?\<J>'_set) = 
      \<Union> (fset ` A_of ` ?\<N>'_un) \<union> \<Union> (fset ` A_of ` ?\<M>'_un)\<close>
    proof -
      have \<open>\<Union> (fset ` A_of ` ?\<J>'_set) = \<Union>{fset (A_of (\<J>'_of J)) |J. enabled_set \<N> J}\<close>
        by blast
      also have \<open>... = \<Union>{\<Union>{fset (A_of \<C>) |\<C>. \<C> \<in>
        (\<N>'_of J) \<union> {\<C>. \<C> \<in> (\<M>'_of J) \<and> enabled \<C> J}} |J. enabled_set \<N> J}\<close>
        using A_of_enabled by (metis (no_types, lifting))
      also have \<open>... = \<Union>(fset ` A_of ` (?\<N>'_un \<union> ?\<M>'_un))\<close> by blast
      finally show \<open>\<Union>(fset ` A_of ` ?\<J>'_set) =
        \<Union>(fset ` A_of ` ?\<N>'_un) \<union> \<Union> (fset ` A_of ` ?\<M>'_un)\<close>
        by simp
    qed
      
    have \<open>\<forall>J. \<not> (enabled_set \<N> J) \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 (\<E>_from \<N>))\<close>
      using equiv_\<E>_enabled_\<N> by blast
    then have not_enab_case: \<open>\<forall>J. \<not> (enabled_set \<N> J) \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 ?\<J>'_set \<union> (\<E>_from \<N>))\<close>
      using supset_not_model_p2 Un_upper2 by blast
    have \<open>\<forall>J. enabled_set \<N> J \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 ?\<J>'_set)\<close>
    proof clarsimp
      fix J
      assume
        enab_N_loc: \<open>enabled_set \<N> J\<close> and
        entails_J: \<open>(J \<Turnstile>\<^sub>p2 ?\<J>'_set)\<close>
      have A_ok: \<open>fset (A_of (\<J>'_of J)) \<subseteq> total_strip J\<close>
        using enab_N_loc fsets_from_J by force
      then have \<open>proj\<^sub>\<bottom> {\<J>'_of J} proj\<^sub>J J = {bot}\<close>
        using enab_N_loc fsets_from_J unfolding propositional_projection_def enabled_projection_def
        by (simp add: enabled_def)
      then have \<open>\<not> J \<Turnstile>\<^sub>p2 ?\<J>'_set\<close>
        using A_ok enab_N_loc unfolding propositional_model2_def enabled_def enabled_projection_def
          proj_prop_J' by auto
      then show False 
        using entails_J by auto
    qed
    then have enab_case: \<open>\<forall>J. (enabled_set \<N> J) \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 ?\<J>'_set \<union> (\<E>_from \<N>))\<close>
      using supset_not_model_p2 Un_upper2 by blast
    have \<open>\<forall>J. \<not> (J \<Turnstile>\<^sub>p2 (?\<J>'_set \<union> (\<E>_from \<N>)))\<close>
      using not_enab_case enab_case by blast

    then obtain \<S> where S_sub: \<open>\<S> \<subseteq> ?\<J>'_set \<union> (\<E>_from \<N>)\<close> and S_fin: \<open>finite \<S>\<close> and
      S_unsat: \<open>\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<S>\<close>
      using compactness_AF_proj by meson
    have E_sat: \<open>sat (AF_proj_to_formula_set (\<E>_from \<N>))\<close>
      unfolding sat_def using J'_is equiv_\<E>_enabled_\<N> equiv_prop_entail2_sema2 by blast
    define \<S>\<^sub>\<J> where \<open>\<S>\<^sub>\<J> = \<S> \<inter> ?\<J>'_set\<close>
    define \<S>\<^sub>\<E> where \<open>\<S>\<^sub>\<E> = \<S> \<inter> (\<E>_from \<N>)\<close>
    define \<S>\<^sub>\<E>' where \<open>\<S>\<^sub>\<E>' = {\<C>. \<C> \<in> \<S>\<^sub>\<E> \<and> (to_V ` (fset (A_of \<C>))) \<subseteq> (to_V ` \<Union> (fset ` A_of ` \<S>\<^sub>\<J>))}\<close>
    define \<S>' where \<open>\<S>' = \<S>\<^sub>\<J> \<union> \<S>\<^sub>\<E>'\<close>
    have proj_S':  \<open>proj\<^sub>\<bottom>  \<S>' = \<S>'\<close>
      using proj_prop_J' prop_proj_\<E>_from S_sub prop_proj_sub prop_proj_distrib
      unfolding \<S>'_def \<S>\<^sub>\<J>_def \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def
      by (smt (verit) Int_iff mem_Collect_eq subsetI)
    have S_is: \<open>\<S> = (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>') \<union> \<S>'\<close>
      using S_sub \<S>\<^sub>\<J>_def \<S>\<^sub>\<E>_def \<S>'_def \<S>\<^sub>\<E>'_def by blast
    have a_from_E_to_J: \<open>neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<E>') \<Longrightarrow> a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close> for a
    proof -
      fix a
      assume nega_in: \<open>neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<E>')\<close>
      then have \<open>to_V (neg a) \<in> to_V ` \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
        unfolding \<S>\<^sub>\<E>'_def by blast
      then have a_or_nega_in: \<open>a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>) \<or> neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
        by (smt (verit) imageE neg.simps(1) neg.simps(2) to_V.elims) 
      obtain \<C>1 where \<open>\<C>1 \<in> \<E>_from \<N>\<close> and \<open>neg a \<in> fset (A_of \<C>1)\<close>
        using nega_in unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def \<E>_from_def by blast
      then obtain \<C> where \<open>\<C> \<in> \<N>\<close> and \<open>a \<in> fset (A_of \<C>)\<close>
        unfolding \<E>_from_def by (smt (verit) AF.sel(2) bot_fset.rep_eq empty_iff finsert.rep_eq
          insert_iff mem_Collect_eq neg.simps(1) neg.simps(2) to_V.elims)
      then have in_N_in_J: \<open>\<forall>J. (enabled_set \<N> J \<longrightarrow> a \<in>\<^sub>t J)\<close>
        using in_total_to_strip unfolding enabled_set_def enabled_def by blast 
      have \<open>b \<in>  \<Union>(fset ` A_of ` \<S>\<^sub>\<J>) \<Longrightarrow> (\<exists>J. enabled_set \<N> J \<and> b \<in>\<^sub>t J)\<close> for b
      proof clarsimp
        fix \<C>2
        assume C2_in: \<open>\<C>2 \<in> \<S>\<^sub>\<J>\<close> and
          b_in: \<open>b \<in> fset (A_of \<C>2)\<close>
        obtain J where enab_J: \<open>enabled_set \<N> J\<close> and \<open>\<C>2 = \<J>'_of J\<close>
          using C2_in unfolding \<S>\<^sub>\<J>_def by blast
        then have \<open>b \<in> total_strip J\<close>
          using b_in fsets_from_J by auto
        then show \<open>\<exists>J. enabled_set \<N> J \<and> b \<in> total_strip J\<close>
          using enab_J by blast
      qed
      then have \<open>\<not>  neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
        using in_N_in_J by fastforce 
      then show \<open>a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
        using a_or_nega_in by blast
    qed
    have empty_inter_in_S: \<open>to_V ` \<Union> (fset ` A_of ` (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>')) \<inter> to_V ` \<Union> (fset ` A_of ` \<S>') = {}\<close>
    proof (rule ccontr)
      assume contra: \<open>to_V ` \<Union> (fset ` A_of ` (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>')) \<inter> to_V ` \<Union> (fset ` A_of ` \<S>') \<noteq> {}\<close>
      then obtain v where v_in1: \<open>v \<in> to_V ` \<Union> (fset ` A_of ` (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))\<close>
        and v_in2: \<open>v \<in> to_V ` \<Union> (fset ` A_of ` \<S>')\<close> by blast
      obtain \<C> where C_in: \<open>\<C> \<in> \<S>\<^sub>\<E> - \<S>\<^sub>\<E>'\<close> and v_in_C: \<open>v \<in> to_V ` (fset (A_of \<C>))\<close>
        using v_in1 by blast
      obtain a where C_is1: \<open>\<C> = Pair bot {|a|}\<close>
        using C_in unfolding \<S>\<^sub>\<E>_def \<E>_from_def by blast
      then have v_is: \<open>v = to_V a\<close>
        using v_in_C by simp
      obtain \<C>' where C'_in: \<open>\<C>' \<in> \<S>'\<close> and v_in_C': \<open>v \<in> to_V ` (fset (A_of \<C>'))\<close>
        using v_in2 by blast
      then obtain a' where v_is': \<open>v = to_V a'\<close> and a'_in: \<open>a' \<in> fset (A_of \<C>')\<close>
        by blast
      consider (J) \<open>\<C>' \<in> \<S>\<^sub>\<J>\<close> | (E') \<open>\<C>' \<in> \<S>\<^sub>\<E>'\<close>
        using C'_in \<S>'_def by blast
      then show False
      proof cases
        case J
        then have \<open>to_V ` (fset (A_of \<C>')) \<subseteq> (to_V ` \<Union> (fset ` A_of ` \<S>\<^sub>\<J>))\<close>
          by blast
        then have \<open>to_V ` (fset (A_of \<C>)) \<subseteq> (to_V ` \<Union> (fset ` A_of ` \<S>\<^sub>\<J>))\<close>
          using C_is1 v_in_C' v_is by auto
        then have \<open>\<C> \<in> \<S>\<^sub>\<E>'\<close>
          unfolding \<S>\<^sub>\<E>'_def using C_in by blast
        then show False
          using C_in by blast
      next
        case E'
        then consider (a) \<open>\<C>' = Pair bot {|a|}\<close> | (nega) \<open>\<C>' = Pair bot {|neg a|}\<close>
          unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def \<E>_from_def using v_in_C' v_is
            AF.sel(2) IntE empty_iff fset_simps(1) fset_simps(2) image_iff insert_iff
            mem_Collect_eq neg.simps(1) neg.simps(2) to_V.elims
          by (smt (verit, del_insts))
          (* by (smt (verit)) (* Solver verit: Solver terminated abnormally with error code 1 *)*)
        then show False 
        proof cases
          case a
          then show ?thesis
            using E' a_in_\<E> Enabled equiv_\<E>_enabled_\<N> C_in C_is1 unfolding \<S>\<^sub>\<E>_def \<S>\<^sub>\<E>'_def 
            by blast
        next
          case nega
          have \<open>\<C>' \<in> \<E>_from \<N>\<close> 
            using E' unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def by auto
          moreover have \<open>\<C> \<in> \<E>_from \<N>\<close>
            using C_in unfolding \<S>\<^sub>\<E>_def by auto
          find_theorems \<E>_from
          ultimately show ?thesis
            using a_in_\<E> nega C_is1 Enabled equiv_\<E>_enabled_\<N> by blast
        qed
      qed
    qed
    then have empty_inter: \<open>\<Union> (atoms ` (AF_proj_to_formula_set (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))) \<inter>
      \<Union> (atoms ` (AF_proj_to_formula_set \<S>')) = {}\<close>
      using atoms_simp proj_S' prop_proj_distrib prop_proj_sub
      by (smt (verit, ccfv_threshold) S_sub Un_subset_iff \<open>\<S> = \<S>\<^sub>\<E> - \<S>\<^sub>\<E>' \<union> \<S>'\<close> proj_prop_J'
        prop_proj_\<E>_from)
    have sat_rest: \<open>sat (AF_proj_to_formula_set (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))\<close>
      using E_sat unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def AF_proj_to_formula_set_def
        propositional_projection_def sat_def by blast
    have S'_unsat: \<open>\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<S>'\<close>
      using unsat_AF_simp[OF _ sat_rest empty_inter] S_unsat equiv_prop_entail2_sema2 S_is
        val_from_interp unfolding sat_def by metis
    have ex_fin_Js: \<open>\<exists>Js. \<S>\<^sub>\<J> = \<J>'_of ` Js \<and> (\<forall>J\<in>Js. enabled_set \<N> J) \<and> finite Js\<close>
      using finite_subset_with_prop[OF ex_Js S_fin \<S>\<^sub>\<J>_def] .
    then obtain Js where Js_fin: \<open>finite Js\<close> and Js_enab: \<open>\<forall>J\<in>Js. enabled_set \<N> J\<close> and
      Js_is: \<open>\<J>'_of ` Js = \<S>\<^sub>\<J>\<close>
      by blast

    have fin_inter: \<open>finite (\<Union>(fset ` A_of ` \<S>\<^sub>\<J>) \<inter> \<Union>(fset ` A_of ` \<N>))\<close>
    proof
      have \<open>finite (\<Union>(fset ` A_of ` \<S>\<^sub>\<J>))\<close>
        unfolding \<S>\<^sub>\<J>_def using S_fin image_Int_subset by simp
      then show \<open>(finite (\<Union>(fset ` A_of ` \<S>\<^sub>\<J>))) \<or> (finite (\<Union> (fset ` A_of ` \<N>)))\<close>
        by auto
    qed
    have \<open>\<forall>a\<in>(\<Union>(fset ` A_of ` \<N>)). \<exists>\<C>\<in>\<N>. a \<in> fset (A_of \<C>)\<close>
      by blast
    then obtain f where f_def: \<open>\<forall>a\<in>(\<Union>(fset ` A_of ` \<N>)). f a \<in> \<N> \<and> a \<in> fset (A_of (f a))\<close>
      by metis
        (* the fact that \<N>\<^sub>\<J> is needed in the proof was found during the isabelle verification *)
    define \<N>\<^sub>\<J> where \<open>\<N>\<^sub>\<J> = (f ` (\<Union>(fset ` A_of ` \<S>\<^sub>\<J>) \<inter> \<Union>(fset ` A_of ` \<N>)))\<close>
    have nj_fin: \<open>finite \<N>\<^sub>\<J>\<close>
      unfolding \<N>\<^sub>\<J>_def using fin_inter by blast
    have nj_sub: \<open>\<N>\<^sub>\<J> \<subseteq> \<N>\<close>
      unfolding \<N>\<^sub>\<J>_def using f_def by blast
    have nj_as: \<open>(\<forall>a\<in>(\<Union>(fset ` A_of ` \<S>\<^sub>\<J>))\<inter>(\<Union>(fset ` A_of ` \<N>)).
      a \<in> \<Union>(fset ` A_of ` \<N>\<^sub>\<J>))\<close>
      unfolding \<N>\<^sub>\<J>_def using f_def by fast
        
    define \<M>' where \<open>\<M>' = \<Union>{\<M>'_of J |J. J \<in> Js}\<close>
    define \<N>' where  \<open>\<N>' = \<Union>{\<N>'_of J |J. J \<in> Js} \<union> \<N>\<^sub>\<J>\<close>
    then have \<open>\<M>' \<subseteq> \<M>\<close>
      unfolding \<M>'_def using fsets_from_J Js_enab by fast
    moreover have \<open>\<N>' \<subseteq> \<N>\<close>
      unfolding \<N>'_def using fsets_from_J Js_enab nj_sub by fast
    moreover have \<open>finite \<M>'\<close>
      unfolding \<M>'_def using fsets_from_J Js_fin Js_enab by auto
    moreover have \<open>finite \<N>'\<close>
      unfolding \<N>'_def using fsets_from_J Js_fin Js_enab nj_fin by auto
    moreover have \<open>\<M>' \<Turnstile>\<^sub>A\<^sub>F \<N>'\<close> unfolding AF_entails_def
    proof clarsimp
      fix J
      assume enab_N': \<open>enabled_set \<N>' J\<close>
      then have \<open>J \<Turnstile>\<^sub>p2 \<E>_from \<N>'\<close>
        using equiv_\<E>_enabled_\<N> by auto
      moreover have \<open>\<S>\<^sub>\<E>' \<subseteq> \<E>_from \<N>'\<close>
        proof
          fix \<C> 
          assume C_in: \<open>\<C> \<in> \<S>\<^sub>\<E>'\<close>
          then obtain a where C_is: \<open>\<C> = Pair bot {|neg a|}\<close>
            unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def \<E>_from_def by blast
          then have \<open>neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<E>')\<close>
            using C_in using image_iff by fastforce
          then have a_in_SJ: \<open>a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
            using a_from_E_to_J by presburger
          have \<open>\<exists>\<C>'\<in>\<N>. a \<in> fset (A_of \<C>')\<close>
            using C_is C_in unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def by (smt (verit, ccfv_threshold)
              AF.sel(2) IntE J'_is \<E>_from_def a_in_\<E> bot_fset.rep_eq empty_iff equiv_\<E>_enabled_\<N>
              finsert.rep_eq insert_iff mem_Collect_eq to_V.elims to_V_neg)
          then have \<open>a \<in> \<Union>(fset ` A_of ` \<N>)\<close>
            by blast 
          then have \<open>a \<in> \<Union>(fset ` A_of ` \<N>')\<close>
            using nj_as a_in_SJ unfolding \<N>'_def by simp 
          then show \<open>\<C> \<in> \<E>_from \<N>'\<close>
            using C_is unfolding \<E>_from_def by blast
        qed
      ultimately have \<open>J \<Turnstile>\<^sub>p2 \<S>\<^sub>\<E>'\<close>
        unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def using subset_model_p2 by (metis (no_types, lifting))
      then have \<open>\<not> J \<Turnstile>\<^sub>p2 \<S>\<^sub>\<J>\<close>
        using subset_not_model S'_unsat unfolding \<S>'_def by blast
      then have  \<open>\<exists>J'\<in>Js. fset (A_of (\<J>'_of J')) \<subseteq> total_strip J\<close>
        unfolding propositional_model2_def \<S>\<^sub>\<J>_def propositional_projection_def
          enabled_projection_def using Js_is
        by (smt (verit) Collect_cong Set.empty_def \<S>\<^sub>\<J>_def enabled_def image_iff mem_Collect_eq)
      then obtain J' where J'_in: \<open>J' \<in> Js\<close> and A_of_J'_in: \<open>fset (A_of (\<J>'_of J')) \<subseteq> total_strip J\<close>
        by blast
      then have enab_nj': \<open>enabled_set \<N> J'\<close>
        using Js_enab by blast
      then have \<open>(\<M>'_of J') proj\<^sub>J J' \<Turnstile> F_of ` (\<N>'_of J')\<close>
        using fsets_from_J by auto
      moreover have \<open>(\<M>'_of J') proj\<^sub>J J' \<subseteq> (\<M>'_of J') proj\<^sub>J J\<close>
      proof -
        have \<open>\<C> \<in> \<M>'_of J' \<Longrightarrow> enabled \<C> J' \<Longrightarrow> enabled \<C> J\<close> for \<C>
        proof -
          assume C_in: \<open>\<C> \<in> \<M>'_of J'\<close> and
            \<open>enabled \<C> J'\<close>
          then have \<open>fset (A_of \<C>) \<subseteq> fset (A_of (\<J>'_of J'))\<close>
            using fsets_from_J[OF enab_nj'] by blast
          then show \<open>enabled \<C> J\<close>
            using A_of_J'_in unfolding enabled_def by auto
        qed
        then have \<open>(\<C> \<in> \<M>'_of J' \<and> enabled \<C> J') \<Longrightarrow> (\<C> \<in> \<M>'_of J' \<and> enabled \<C> J)\<close> for \<C>
          by (smt (verit, ccfv_threshold))
        then have \<open>{\<C>. \<C> \<in> \<M>'_of J' \<and> enabled \<C> J'} \<subseteq> {\<C>. \<C> \<in> \<M>'_of J' \<and> enabled \<C> J}\<close>
          by blast
        then show \<open>(\<M>'_of J') proj\<^sub>J J' \<subseteq> (\<M>'_of J') proj\<^sub>J J\<close>
          unfolding enabled_projection_def by blast
      qed
      ultimately have entails_one: \<open>(\<M>'_of J') proj\<^sub>J J \<Turnstile> F_of ` (\<N>'_of J')\<close>
        using entails_subsets by blast
      have subs_M: \<open>\<M>'_of J' proj\<^sub>J J \<subseteq> \<M>' proj\<^sub>J J\<close>
        using J'_in using enabled_projection_def unfolding \<M>'_def by auto
      have subs_N: \<open>F_of ` (\<N>'_of J') \<subseteq> F_of ` \<N>'\<close>
        using J'_in unfolding \<N>'_def by blast
      show \<open>\<M>' proj\<^sub>J J \<Turnstile> F_of ` \<N>'\<close>
        using entails_subsets[OF subs_M subs_N entails_one] .
    qed

    ultimately show \<open>\<exists>\<M>' \<N>'. \<M>' \<subseteq> \<M> \<and> \<N>' \<subseteq> \<N> \<and> finite \<M>' \<and> finite \<N>' \<and> \<M>' \<Turnstile>\<^sub>A\<^sub>F \<N>'\<close>
      by blast
  qed
qed

sublocale neg_ext_sound_cons_rel: consequence_relation "Pos bot" sound_cons.entails_neg
  using sound_cons.ext_cons_rel by simp

(* Splitting report Lemma 4, 2/2 *)
lemma AF_ext_sound_cons_rel: \<open>consequence_relation (to_AF bot) AF_entails_sound\<close>
(* TODO: check if this belongs here or if this needs to be moved somewhere else? *)
proof (standard)
  show \<open>{to_AF bot} \<Turnstile>s\<^sub>A\<^sub>F {}\<close>
   (* using sound_cons.bot_entails_empty sound_cons.entails_subsets *)
   unfolding AF_entails_sound_def enabled_def enabled_projection_def
  proof clarsimp
   fix J
   assume \<open>enabled_set {} J\<close>
   have bot_in: \<open>{Pos bot} \<subseteq> Pos ` {C. C = F_of (to_AF bot) \<and> fset (A_of (to_AF bot)) \<subseteq> total_strip J}\<close>
     unfolding to_AF_def by simp
   show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union>
     Pos ` {C. C = F_of (to_AF bot) \<and> fset (A_of (to_AF bot)) \<subseteq> total_strip J}) {}\<close>
     using sound_cons.bot_entails_empty sound_cons.entails_subsets bot_in
     by (smt (verit, ccfv_threshold) AF.sel(2) Un_iff bot_fset.rep_eq
       consequence_relation.bot_entails_empty consequence_relation.entails_subsets empty_subsetI
       image_iff mem_Collect_eq sound_cons.ext_cons_rel subset_eq to_AF_def)
 qed
next
  fix \<C> :: "('f, 'v) AF"
  have \<open>Pos ` {F_of Ca |Ca. Ca \<in> {\<C>} \<and> fset (A_of Ca) \<subseteq> total_strip J} \<subseteq> (Pos ` F_of ` {\<C>})\<close>
    by auto
  show \<open>{\<C>} \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
    unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
  proof clarsimp
    fix J
    assume \<open>fset (A_of \<C>) \<subseteq> total_strip J\<close>
    show \<open>sound_cons.entails_neg (Pos (F_of \<C>) \<triangleright> fml_ext ` total_strip J) {Pos (F_of \<C>)}\<close>
      using sound_cons.entails_reflexive[of "F_of \<C>"]
      by (smt (verit, best) Set.insert_mono bot.extremum consequence_relation.entails_reflexive
        consequence_relation.entails_subsets sound_cons.ext_cons_rel)
  qed
next
  fix \<M> \<N> \<P> \<Q>
  assume m_in_n: \<open>\<M> \<subseteq> \<N>\<close> and
    p_in_q: \<open>\<P> \<subseteq> \<Q>\<close> and
    m_entails_p: \<open>\<M> \<Turnstile>s\<^sub>A\<^sub>F \<P>\<close>
  show \<open>\<N> \<Turnstile>s\<^sub>A\<^sub>F \<Q>\<close>
    unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
  proof clarsimp
    fix J
    assume q_enabled: \<open>\<forall>\<C>\<in>\<Q>. fset (A_of \<C>) \<subseteq> total_strip J\<close>
    have \<open>{F_of \<C> |\<C>. \<C> \<in> \<M> \<and> fset (A_of \<C>) \<subseteq> total_strip J} \<subseteq>
      {F_of \<C> |\<C>. \<C> \<in> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
      using m_in_n by blast
    moreover have \<open>F_of ` \<P> \<subseteq> F_of ` \<Q>\<close>
      using p_in_q by blast
    ultimately show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union>
      Pos ` {F_of \<C> |\<C>. \<C> \<in> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}) (Pos ` F_of ` \<Q>)\<close>
      using m_entails_p sound_cons.entails_subsets m_in_n p_in_q q_enabled
      unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
      by (smt (z3) Un_iff consequence_relation.entails_subsets image_iff mem_Collect_eq
        sound_cons.ext_cons_rel subset_eq)
  qed
next
  fix \<M> \<N> \<C> \<M>' \<N>'
  assume
    entails_c: \<open>\<M> \<Turnstile>s\<^sub>A\<^sub>F \<N> \<union> {\<C>}\<close> and
    c_entails: \<open>\<M>' \<union> {\<C>} \<Turnstile>s\<^sub>A\<^sub>F \<N>'\<close>
  show \<open>\<M> \<union> \<M>' \<Turnstile>s\<^sub>A\<^sub>F \<N> \<union> \<N>'\<close>
    unfolding AF_entails_sound_def
  proof (intro allI impI)
    fix J
    assume enabled_n: \<open>enabled_set (\<N> \<union> \<N>') J\<close>
    {
      assume enabled_c: \<open>enabled_set {\<C>} J\<close>
      then have proj_enabled_c: \<open>{\<C>} proj\<^sub>J J = {F_of \<C>}\<close>
        unfolding enabled_projection_def using enabled_set_def by blast
      have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M> proj\<^sub>J J))
        (Pos ` F_of ` (\<N> \<union> {\<C>}))\<close>
        using entails_c enabled_n enabled_c unfolding AF_entails_sound_def
        by (metis Un_iff enabled_set_def)
      then have cut_hyp1: \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M> proj\<^sub>J J))
        (Pos ` F_of ` \<N> \<union> {Pos (F_of \<C>)})\<close>
        by force
      have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M>' \<union> {\<C>} proj\<^sub>J J))
        (Pos ` F_of ` \<N>')\<close>
        using c_entails enabled_n enabled_union2 unfolding AF_entails_sound_def by blast
      then have cut_hyp2: \<open>sound_cons.entails_neg
        (fml_ext ` total_strip J \<union> Pos ` (\<M>' proj\<^sub>J J) \<union> {Pos (F_of \<C>)}) (Pos ` F_of ` \<N>')\<close>
       by (metis Un_empty_right Un_insert_right distrib_proj image_insert proj_enabled_c)
       have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M> \<union> \<M>' proj\<^sub>J J))
         (Pos ` F_of ` (\<N> \<union> \<N>'))\<close>
         using neg_ext_sound_cons_rel.entails_cut[OF cut_hyp1 cut_hyp2]  distrib_proj[of \<M> \<M>' J]
           image_Un by (smt (verit, del_insts) Un_commute Un_left_absorb Un_left_commute)
    }
    moreover
    {
      assume not_enabled_c: \<open>\<not> enabled_set {\<C>} J\<close>
      then have \<open>\<M>' \<union> {\<C>} proj\<^sub>J J = \<M>' proj\<^sub>J J\<close>
        unfolding enabled_projection_def enabled_set_def by auto
      then have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M>' proj\<^sub>J J))
        (Pos ` F_of ` \<N>')\<close>
        using c_entails enabled_n enabled_union2 unfolding AF_entails_sound_def by metis
      then have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M> \<union> \<M>' proj\<^sub>J J))
        (Pos ` F_of ` (\<N> \<union> \<N>'))\<close>
        using neg_ext_sound_cons_rel.entails_subsets
        by (smt (verit, del_insts) Un_iff distrib_proj image_Un subsetI)
    }
    ultimately
    show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M> \<union> \<M>' proj\<^sub>J J))
      (Pos ` F_of ` (\<N> \<union> \<N>'))\<close>
      by blast
  qed
next
  fix \<M> \<N>
  assume m_entails_n: \<open>\<M> \<Turnstile>s\<^sub>A\<^sub>F \<N>\<close>
  consider (NotEnabled) \<open>\<forall>J. \<not> enabled_set \<N> J\<close> | (Enabled) \<open>\<exists>J. enabled_set \<N> J\<close> by blast
  then show \<open>\<exists>M' N'. M' \<subseteq> \<M> \<and> N' \<subseteq> \<N> \<and> finite M' \<and> finite N' \<and> M' \<Turnstile>s\<^sub>A\<^sub>F N'\<close>
  proof cases
    case NotEnabled
    then obtain \<N>' where N'_sub: \<open>\<N>' \<subseteq> \<N>\<close> and N'_fin: \<open>finite \<N>'\<close> and
      sub_not_enab: \<open>\<forall>J. \<not> enabled_set \<N>' J\<close>
      using never_enabled_finite_subset[of \<N>] by blast
    obtain \<M>' where \<open>\<M>' \<subseteq> \<M>\<close> and \<open>finite \<M>'\<close> and \<open>\<M>' \<Turnstile>s\<^sub>A\<^sub>F \<N>'\<close>
      using sub_not_enab unfolding AF_entails_sound_def by blast
    then show ?thesis using N'_sub N'_fin by blast
  next
    case Enabled
    then obtain J' where J'_is: \<open>enabled_set \<N> J'\<close> by auto
    {
      fix J
      assume enabled_N: \<open>enabled_set \<N> J\<close>
      then have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M> proj\<^sub>J J)) (Pos ` F_of ` \<N>)\<close>
        using m_entails_n unfolding AF_entails_sound_def by blast
      then obtain MJ' N' where mj_in: \<open>MJ' \<subseteq> fml_ext ` total_strip J \<union> Pos ` (\<M> proj\<^sub>J J)\<close> and
        np_proj: \<open>N' \<subseteq> Pos ` F_of ` \<N>\<close> and mjp_fin: \<open>finite MJ'\<close> and np_fin: \<open>finite N'\<close> and
        mjp_entails_np: \<open>sound_cons.entails_neg  MJ' N'\<close>
        using neg_ext_sound_cons_rel.entails_compactness by metis

      define M' where "M' = MJ' \<inter> Pos ` (\<M> proj\<^sub>J J)"
      then have mp_fin: \<open>finite M'\<close>
        using mjp_fin by auto
      have mp_with_f_of: \<open>\<forall>C \<in> M'. \<exists>\<C> \<in> \<M>. Pos (F_of \<C>) = C \<and> enabled \<C> J\<close>
        using mj_in unfolding enabled_projection_def M'_def by blast
      have \<open>\<exists>\<M>'\<subseteq> \<M>. finite \<M>' \<and> M' = Pos ` F_of ` \<M>' \<and> enabled_set \<M>' J\<close>
        using finite_subset_image_strong[of M' \<M> "(\<lambda>x. Pos (F_of x))" "\<lambda>x. enabled x J", OF mp_fin mp_with_f_of]
        unfolding enabled_set_def by blast
      then have ex_mp: \<open>\<exists>\<M>'\<subseteq>\<M>. finite \<M>' \<and> Pos ` (\<M>' proj\<^sub>J J) = M'\<close>
        unfolding enabled_projection_def enabled_set_def by blast
      then obtain \<M>' where mp_props: \<open>\<M>' \<subseteq> \<M>\<close> \<open>finite \<M>'\<close> \<open>Pos ` (\<M>' proj\<^sub>J J) = M'\<close> by auto

      let ?\<M>'_sel\<^sub>J = \<open>{\<C>. \<C> \<in> \<M>' \<and> enabled \<C> J}\<close>
      have \<open>?\<M>'_sel\<^sub>J \<subseteq> \<M>'\<close> by simp
      have \<open>finite (\<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> ?\<M>'_sel\<^sub>J})\<close> (*{a. \<exists>\<C>\<in>\<N>'. a \<in> (fset (A_of \<C>)) }\<close>*)
        using mp_props by auto
      then obtain \<A>\<^sub>\<M>\<^sub>' where AM_is: \<open>fset \<A>\<^sub>\<M>\<^sub>' = (\<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> ?\<M>'_sel\<^sub>J})\<close>
        using fin_set_fset by fastforce
      then have AM_in_J: \<open>fset \<A>\<^sub>\<M>\<^sub>' \<subseteq> total_strip J\<close>
        unfolding enabled_def by blast
      define J' where "J' = (MJ' \<inter> fml_ext ` total_strip J)"
      then have jp_fin: \<open>finite J'\<close>
        using mjp_fin by blast
      then obtain \<J>' where jp_props: "\<J>' \<subseteq> total_strip J" "fml_ext ` \<J>' = J'" "finite \<J>'"
        using J'_def by (metis Int_lower2 finite_subset_image)
      then obtain \<A>\<^sub>\<J>\<^sub>' where AJ_is: \<open>fset \<A>\<^sub>\<J>\<^sub>' = \<J>'\<close>
        using fin_set_fset by blast
      then have AJ_in_J: \<open>fset \<A>\<^sub>\<J>\<^sub>' \<subseteq> total_strip J\<close>
        using jp_props by auto
      define \<J>\<^sub>f' where \<open>\<J>\<^sub>f' = Pair bot (\<A>\<^sub>\<J>\<^sub>' |\<union>| \<A>\<^sub>\<M>\<^sub>')\<close>
      then have Jf_in: \<open>fset (A_of \<J>\<^sub>f') \<subseteq> total_strip J\<close> using AM_in_J AJ_in_J by simp
      have Jf_bot: \<open>F_of \<J>\<^sub>f' = bot\<close> using \<J>\<^sub>f'_def by auto
      have AM_in_Jf: \<open>\<forall>\<C>\<in>\<M>'. enabled \<C> J \<longrightarrow> fset (A_of \<C>) \<subseteq> fset (A_of \<J>\<^sub>f')\<close>
        using \<J>\<^sub>f'_def AM_is by auto

      have np_with_f_of: \<open>\<forall>C \<in> N'. \<exists>\<C> \<in> \<N>. Pos (F_of \<C>) = C\<close>
        using np_proj unfolding enabled_projection_def by blast
      have n_fin_subset: \<open>\<exists>\<N>'\<subseteq> \<N>. finite \<N>' \<and> N' = Pos ` F_of ` \<N>'\<close>
        using finite_subset_image[OF np_fin, of "\<lambda>x. Pos (F_of x)" \<N>] np_proj by auto
      then obtain \<N>' where np_props: \<open>\<N>' \<subseteq> \<N>\<close> \<open>finite \<N>'\<close> \<open>N' = Pos ` F_of ` \<N>'\<close>
        by blast
      have enab_np: \<open>enabled_set \<N>' J\<close>
        using enabled_N np_props unfolding enabled_set_def by blast

      have mjp_is: \<open>MJ' = Pos ` (\<M>' proj\<^sub>J J) \<union> fml_ext ` \<J>'\<close>
        using mj_in M'_def J'_def mp_props jp_props by auto
      have \<open>sound_cons.entails_neg ((Pos ` (\<M>' proj\<^sub>J J))\<union> fml_ext ` \<J>') (Pos ` F_of ` \<N>')\<close>
        using np_props mjp_entails_np unfolding mjp_is by blast
      then have fin_entail: \<open>sound_cons.entails_neg ((Pos ` (\<M>' proj\<^sub>J J))\<union> fml_ext ` (fset (A_of \<J>\<^sub>f'))) (Pos ` F_of ` \<N>')\<close>
        using neg_ext_sound_cons_rel.entails_subsets[of
          "(Pos ` (\<M>' proj\<^sub>J J))\<union> fml_ext ` \<J>'" "(Pos ` (\<M>' proj\<^sub>J J))\<union> fml_ext ` (fset (A_of \<J>\<^sub>f'))"
          "Pos ` F_of ` \<N>'" "Pos ` F_of ` \<N>'"] AJ_is unfolding \<J>\<^sub>f'_def by (simp add: image_Un subsetI)

      have \<open>\<exists>\<M>' \<N>' \<J>'. \<M>' \<subseteq> \<M> \<and> fset (A_of \<J>') \<subseteq> total_strip J \<and> \<N>' \<subseteq> \<N> \<and>
        finite \<M>'  \<and> finite \<N>' \<and> F_of \<J>' = bot \<and> enabled_set \<N>' J \<and>
        (\<forall>\<C>\<in>\<M>'. enabled \<C> J \<longrightarrow> fset (A_of \<C>) \<subseteq> fset (A_of \<J>')) \<and>
        sound_cons.entails_neg ((Pos ` (\<M>' proj\<^sub>J J))\<union> fml_ext ` (fset (A_of \<J>'))) (Pos ` F_of ` \<N>')\<close>
        using mp_props np_props fin_entail enab_np Jf_in Jf_bot \<J>\<^sub>f'_def AJ_is AM_is AM_in_Jf AF.sel(2) by blast
    }

    then obtain \<M>'_of \<N>'_of \<J>'_of where
      fsets_from_J: \<open>enabled_set \<N> J \<Longrightarrow> \<M>'_of J \<subseteq> \<M> \<and> fset (A_of (\<J>'_of J)) \<subseteq> total_strip J \<and> \<N>'_of J \<subseteq> \<N> \<and>
      finite (\<M>'_of J) \<and> finite (\<N>'_of J) \<and> F_of (\<J>'_of J) = bot \<and> enabled_set (\<N>'_of J) J \<and>
      (\<forall>\<C>\<in>(\<M>'_of J). enabled \<C> J \<longrightarrow> fset (A_of \<C>) \<subseteq> fset (A_of (\<J>'_of J))) \<and>
      sound_cons.entails_neg (Pos ` (\<M>'_of J proj\<^sub>J J) \<union> fml_ext ` (fset (A_of (\<J>'_of J)))) (Pos ` F_of ` \<N>'_of J) \<close> for J
      by metis

    let ?\<J>'_set = \<open>{\<J>'_of J |J. enabled_set \<N> J}\<close>
    have ex_Js: \<open>\<exists>Js. ?\<J>'_set = \<J>'_of ` Js \<and> (\<forall>J\<in>Js. enabled_set \<N> J)\<close>
      by blast
    have proj_prop_J': \<open>proj\<^sub>\<bottom> ?\<J>'_set = ?\<J>'_set\<close>
      using fsets_from_J unfolding propositional_projection_def by blast
    let ?\<N>'_un = \<open>\<Union>{\<N>'_of J |J. enabled_set \<N> J}\<close>
    let ?\<M>'_un = \<open>\<Union>{{\<C>. \<C> \<in> \<M>'_of J \<and> enabled \<C> J} |J. enabled_set \<N> J}\<close>

    have \<open>\<forall>J. \<not> (enabled_set \<N> J) \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 (\<E>_from \<N>))\<close>
      using equiv_\<E>_enabled_\<N> by blast
    then have not_enab_case: \<open>\<forall>J. \<not> (enabled_set \<N> J) \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 ?\<J>'_set \<union> (\<E>_from \<N>))\<close>
      using supset_not_model_p2 Un_upper2 by blast
    have \<open>\<forall>J. enabled_set \<N> J \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 ?\<J>'_set)\<close>
    proof clarsimp
      fix J
      assume
        enab_N_loc: \<open>enabled_set \<N> J\<close> and
        entails_J: \<open>(J \<Turnstile>\<^sub>p2 ?\<J>'_set)\<close>
      have A_ok: \<open>fset (A_of (\<J>'_of J)) \<subseteq> total_strip J\<close>
        using enab_N_loc fsets_from_J by force
      then have \<open>proj\<^sub>\<bottom> {\<J>'_of J} proj\<^sub>J J = {bot}\<close>
        using enab_N_loc fsets_from_J unfolding propositional_projection_def enabled_projection_def
        by (simp add: enabled_def)
      then have \<open>\<not> J \<Turnstile>\<^sub>p2 ?\<J>'_set\<close>
        using A_ok enab_N_loc unfolding propositional_model2_def enabled_def enabled_projection_def
          proj_prop_J' by auto
      then show False
        using entails_J by auto
    qed
    then have enab_case: \<open>\<forall>J. (enabled_set \<N> J) \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 ?\<J>'_set \<union> (\<E>_from \<N>))\<close>
      using supset_not_model_p2 Un_upper2 by blast
    have \<open>\<forall>J. \<not> (J \<Turnstile>\<^sub>p2 (?\<J>'_set \<union> (\<E>_from \<N>)))\<close>
      using not_enab_case enab_case by blast

    then obtain \<S> where S_sub: \<open>\<S> \<subseteq> ?\<J>'_set \<union> (\<E>_from \<N>)\<close> and S_fin: \<open>finite \<S>\<close> and
      S_unsat: \<open>\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<S>\<close>
      using compactness_AF_proj by meson
    have E_sat: \<open>sat (AF_proj_to_formula_set (\<E>_from \<N>))\<close>
      unfolding sat_def using J'_is equiv_\<E>_enabled_\<N> equiv_prop_entail2_sema2 by blast
    define \<S>\<^sub>\<J> where \<open>\<S>\<^sub>\<J> = \<S> \<inter> ?\<J>'_set\<close>
    define \<S>\<^sub>\<E> where \<open>\<S>\<^sub>\<E> = \<S> \<inter> (\<E>_from \<N>)\<close>
    define \<S>\<^sub>\<E>' where \<open>\<S>\<^sub>\<E>' = {\<C>. \<C> \<in> \<S>\<^sub>\<E> \<and> (to_V ` (fset (A_of \<C>))) \<subseteq> (to_V ` \<Union> (fset ` A_of ` \<S>\<^sub>\<J>))}\<close>
    define \<S>' where \<open>\<S>' = \<S>\<^sub>\<J> \<union> \<S>\<^sub>\<E>'\<close>
    have proj_S':  \<open>proj\<^sub>\<bottom>  \<S>' = \<S>'\<close>
      using proj_prop_J' prop_proj_\<E>_from S_sub prop_proj_sub prop_proj_distrib
      unfolding \<S>'_def \<S>\<^sub>\<J>_def \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def
      by (smt (verit) Int_iff mem_Collect_eq subsetI)
    have S_is: \<open>\<S> = (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>') \<union> \<S>'\<close>
      using S_sub \<S>\<^sub>\<J>_def \<S>\<^sub>\<E>_def \<S>'_def \<S>\<^sub>\<E>'_def by blast
    have a_from_E_to_J: \<open>neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<E>') \<Longrightarrow> a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close> for a
    proof -
      fix a
      assume nega_in: \<open>neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<E>')\<close>
      then have \<open>to_V (neg a) \<in> to_V ` \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
        unfolding \<S>\<^sub>\<E>'_def by blast
      then have a_or_nega_in: \<open>a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>) \<or> neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
        by (smt (verit) imageE neg.simps(1) neg.simps(2) to_V.elims)
      obtain \<C>1 where \<open>\<C>1 \<in> \<E>_from \<N>\<close> and \<open>neg a \<in> fset (A_of \<C>1)\<close>
        using nega_in unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def \<E>_from_def by blast
      then obtain \<C> where \<open>\<C> \<in> \<N>\<close> and \<open>a \<in> fset (A_of \<C>)\<close>
        unfolding \<E>_from_def by (smt (verit) AF.sel(2) bot_fset.rep_eq empty_iff finsert.rep_eq
          insert_iff mem_Collect_eq neg.simps(1) neg.simps(2) to_V.elims)
      then have in_N_in_J: \<open>\<forall>J. (enabled_set \<N> J \<longrightarrow> a \<in>\<^sub>t J)\<close>
        using in_total_to_strip unfolding enabled_set_def enabled_def by blast
      have \<open>b \<in>  \<Union>(fset ` A_of ` \<S>\<^sub>\<J>) \<Longrightarrow> (\<exists>J. enabled_set \<N> J \<and> b \<in>\<^sub>t J)\<close> for b
      proof clarsimp
        fix \<C>2
        assume C2_in: \<open>\<C>2 \<in> \<S>\<^sub>\<J>\<close> and
          b_in: \<open>b \<in> fset (A_of \<C>2)\<close>
        obtain J where enab_J: \<open>enabled_set \<N> J\<close> and \<open>\<C>2 = \<J>'_of J\<close>
          using C2_in unfolding \<S>\<^sub>\<J>_def by blast
        then have \<open>b \<in> total_strip J\<close>
          using b_in fsets_from_J by (meson basic_trans_rules(31))
        then show \<open>\<exists>J. enabled_set \<N> J \<and> b \<in> total_strip J\<close>
          using enab_J by blast
      qed
      then have \<open>\<not>  neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
        using in_N_in_J by fastforce
      then show \<open>a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
        using a_or_nega_in by blast
    qed
    have empty_inter_in_S: \<open>to_V ` \<Union> (fset ` A_of ` (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>')) \<inter> to_V ` \<Union> (fset ` A_of ` \<S>') = {}\<close>
    proof (rule ccontr)
      assume contra: \<open>to_V ` \<Union> (fset ` A_of ` (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>')) \<inter> to_V ` \<Union> (fset ` A_of ` \<S>') \<noteq> {}\<close>
      then obtain v where v_in1: \<open>v \<in> to_V ` \<Union> (fset ` A_of ` (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))\<close>
        and v_in2: \<open>v \<in> to_V ` \<Union> (fset ` A_of ` \<S>')\<close> by blast
      obtain \<C> where C_in: \<open>\<C> \<in> \<S>\<^sub>\<E> - \<S>\<^sub>\<E>'\<close> and v_in_C: \<open>v \<in> to_V ` (fset (A_of \<C>))\<close>
        using v_in1 by blast
      obtain a where C_is1: \<open>\<C> = Pair bot {|a|}\<close>
        using C_in unfolding \<S>\<^sub>\<E>_def \<E>_from_def by blast
      then have v_is: \<open>v = to_V a\<close>
        using v_in_C by simp
      obtain \<C>' where C'_in: \<open>\<C>' \<in> \<S>'\<close> and v_in_C': \<open>v \<in> to_V ` (fset (A_of \<C>'))\<close>
        using v_in2 by blast
      then obtain a' where v_is': \<open>v = to_V a'\<close> and a'_in: \<open>a' \<in> fset (A_of \<C>')\<close>
        by blast
      consider (J) \<open>\<C>' \<in> \<S>\<^sub>\<J>\<close> | (E') \<open>\<C>' \<in> \<S>\<^sub>\<E>'\<close>
        using C'_in \<S>'_def by blast
      then show False
      proof cases
        case J
        then have \<open>to_V ` (fset (A_of \<C>')) \<subseteq> (to_V ` \<Union> (fset ` A_of ` \<S>\<^sub>\<J>))\<close>
          by blast
        then have \<open>to_V ` (fset (A_of \<C>)) \<subseteq> (to_V ` \<Union> (fset ` A_of ` \<S>\<^sub>\<J>))\<close>
          using C_is1 v_in_C' v_is by auto
        then have \<open>\<C> \<in> \<S>\<^sub>\<E>'\<close>
          unfolding \<S>\<^sub>\<E>'_def using C_in by blast
        then show False
          using C_in by blast
      next
        case E'
        then consider (a) \<open>\<C>' = Pair bot {|a|}\<close> | (nega) \<open>\<C>' = Pair bot {|neg a|}\<close>
          unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def \<E>_from_def using v_in_C' v_is
            AF.sel(2) IntE empty_iff fset_simps(1) fset_simps(2) image_iff insert_iff
            mem_Collect_eq neg.simps(1) neg.simps(2) to_V.elims
          by (smt (verit, del_insts))
          (* by (smt (verit)) (* Solver verit: Solver terminated abnormally with error code 1 *)*)
        then show False
        proof cases
          case a
          then show ?thesis
            using E' a_in_\<E> Enabled equiv_\<E>_enabled_\<N> C_in C_is1 unfolding \<S>\<^sub>\<E>_def \<S>\<^sub>\<E>'_def
            by blast
        next
          case nega
          have \<open>\<C>' \<in> \<E>_from \<N>\<close>
            using E' unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def by auto
          moreover have \<open>\<C> \<in> \<E>_from \<N>\<close>
            using C_in unfolding \<S>\<^sub>\<E>_def by auto
          find_theorems \<E>_from
          ultimately show ?thesis
            using a_in_\<E> nega C_is1 Enabled equiv_\<E>_enabled_\<N> by blast
        qed
      qed
    qed
    then have empty_inter: \<open>\<Union> (atoms ` (AF_proj_to_formula_set (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))) \<inter>
      \<Union> (atoms ` (AF_proj_to_formula_set \<S>')) = {}\<close>
      using atoms_simp proj_S' prop_proj_distrib prop_proj_sub
      by (smt (verit, ccfv_threshold) S_sub Un_subset_iff \<open>\<S> = \<S>\<^sub>\<E> - \<S>\<^sub>\<E>' \<union> \<S>'\<close> proj_prop_J'
        prop_proj_\<E>_from)
    have sat_rest: \<open>sat (AF_proj_to_formula_set (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))\<close>
      using E_sat unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def AF_proj_to_formula_set_def
        propositional_projection_def sat_def by blast
    have S'_unsat: \<open>\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<S>'\<close>
      using unsat_AF_simp[OF _ sat_rest empty_inter] S_unsat equiv_prop_entail2_sema2 S_is
        val_from_interp unfolding sat_def by metis
    have ex_fin_Js: \<open>\<exists>Js. \<S>\<^sub>\<J> = \<J>'_of ` Js \<and> (\<forall>J\<in>Js. enabled_set \<N> J) \<and> finite Js\<close>
      using finite_subset_with_prop[OF ex_Js S_fin \<S>\<^sub>\<J>_def] .
    then obtain Js where Js_fin: \<open>finite Js\<close> and Js_enab: \<open>\<forall>J\<in>Js. enabled_set \<N> J\<close> and
      Js_is: \<open>\<J>'_of ` Js = \<S>\<^sub>\<J>\<close>
      by blast

    have fin_inter: \<open>finite (\<Union>(fset ` A_of ` \<S>\<^sub>\<J>) \<inter> \<Union>(fset ` A_of ` \<N>))\<close>
    proof
      have \<open>finite (\<Union>(fset ` A_of ` \<S>\<^sub>\<J>))\<close>
        unfolding \<S>\<^sub>\<J>_def using S_fin image_Int_subset by simp
      then show \<open>(finite (\<Union>(fset ` A_of ` \<S>\<^sub>\<J>))) \<or> (finite (\<Union> (fset ` A_of ` \<N>)))\<close>
        by auto
    qed
    have \<open>\<forall>a\<in>(\<Union>(fset ` A_of ` \<N>)). \<exists>\<C>\<in>\<N>. a \<in> fset (A_of \<C>)\<close>
      by blast
    then obtain f where f_def: \<open>\<forall>a\<in>(\<Union>(fset ` A_of ` \<N>)). f a \<in> \<N> \<and> a \<in> fset (A_of (f a))\<close>
      by metis
    define \<N>\<^sub>\<J> where \<open>\<N>\<^sub>\<J> = (f ` (\<Union>(fset ` A_of ` \<S>\<^sub>\<J>) \<inter> \<Union>(fset ` A_of ` \<N>)))\<close>
    have nj_fin: \<open>finite \<N>\<^sub>\<J>\<close>
      unfolding \<N>\<^sub>\<J>_def using fin_inter by blast
    have nj_sub: \<open>\<N>\<^sub>\<J> \<subseteq> \<N>\<close>
      unfolding \<N>\<^sub>\<J>_def using f_def by blast
    have nj_as: \<open>(\<forall>a\<in>(\<Union>(fset ` A_of ` \<S>\<^sub>\<J>))\<inter>(\<Union>(fset ` A_of ` \<N>)).
      a \<in> \<Union>(fset ` A_of ` \<N>\<^sub>\<J>))\<close>
      unfolding \<N>\<^sub>\<J>_def using f_def by fast

    define \<M>' where \<open>\<M>' = \<Union>{\<M>'_of J |J. J \<in> Js}\<close>
    define \<N>' where  \<open>\<N>' = \<Union>{\<N>'_of J |J. J \<in> Js} \<union> \<N>\<^sub>\<J>\<close>
    then have \<open>\<M>' \<subseteq> \<M>\<close>
      unfolding \<M>'_def using fsets_from_J Js_enab by fast
    moreover have \<open>\<N>' \<subseteq> \<N>\<close>
      unfolding \<N>'_def using fsets_from_J Js_enab nj_sub by fast
    moreover have \<open>finite \<M>'\<close>
      unfolding \<M>'_def using fsets_from_J Js_fin Js_enab by auto
    moreover have \<open>finite \<N>'\<close>
      unfolding \<N>'_def using fsets_from_J Js_fin Js_enab nj_fin by auto
    moreover have \<open>\<M>' \<Turnstile>s\<^sub>A\<^sub>F \<N>'\<close> unfolding AF_entails_sound_def
    proof clarsimp
      fix J
      assume enab_N': \<open>enabled_set \<N>' J\<close>
      then have \<open>J \<Turnstile>\<^sub>p2 \<E>_from \<N>'\<close>
        using equiv_\<E>_enabled_\<N> by auto
      moreover have \<open>\<S>\<^sub>\<E>' \<subseteq> \<E>_from \<N>'\<close>
        proof
          fix \<C>
          assume C_in: \<open>\<C> \<in> \<S>\<^sub>\<E>'\<close>
          then obtain a where C_is: \<open>\<C> = Pair bot {|neg a|}\<close>
            unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def \<E>_from_def by blast
          then have \<open>neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<E>')\<close>
            using C_in using image_iff by fastforce
          then have a_in_SJ: \<open>a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
            using a_from_E_to_J by presburger
          have \<open>\<exists>\<C>'\<in>\<N>. a \<in> fset (A_of \<C>')\<close>
            using C_is C_in unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def by (smt (verit, ccfv_threshold)
              AF.sel(2) IntE J'_is \<E>_from_def a_in_\<E> bot_fset.rep_eq empty_iff equiv_\<E>_enabled_\<N>
              finsert.rep_eq insert_iff mem_Collect_eq to_V.elims to_V_neg)
          then have \<open>a \<in> \<Union>(fset ` A_of ` \<N>)\<close>
            by blast
          then have \<open>a \<in> \<Union>(fset ` A_of ` \<N>')\<close>
            using nj_as a_in_SJ unfolding \<N>'_def by simp
          then show \<open>\<C> \<in> \<E>_from \<N>'\<close>
            using C_is unfolding \<E>_from_def by blast
        qed
      ultimately have \<open>J \<Turnstile>\<^sub>p2 \<S>\<^sub>\<E>'\<close>
        unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def using subset_model_p2 by (metis (no_types, lifting))
      then have \<open>\<not> J \<Turnstile>\<^sub>p2 \<S>\<^sub>\<J>\<close>
        using subset_not_model S'_unsat unfolding \<S>'_def by blast
      then have  \<open>\<exists>J'\<in>Js. fset (A_of (\<J>'_of J')) \<subseteq> total_strip J\<close>
        unfolding propositional_model2_def \<S>\<^sub>\<J>_def propositional_projection_def
          enabled_projection_def using Js_is
        by (smt (verit) Collect_cong Set.empty_def \<S>\<^sub>\<J>_def enabled_def image_iff mem_Collect_eq)
      then obtain J' where J'_in: \<open>J' \<in> Js\<close> and A_of_J'_in: \<open>fset (A_of (\<J>'_of J')) \<subseteq> total_strip J\<close>
        by blast
      then have enab_nj': \<open>enabled_set \<N> J'\<close>
        using Js_enab by blast
      then have \<open>sound_cons.entails_neg (Pos ` (\<M>'_of J' proj\<^sub>J J') \<union>
        fml_ext ` (fset (A_of (\<J>'_of J')))) (Pos ` F_of ` \<N>'_of J')\<close>
        using fsets_from_J by auto
      moreover have \<open>(\<M>'_of J') proj\<^sub>J J' \<subseteq> (\<M>'_of J') proj\<^sub>J J\<close>
      proof -
        have \<open>\<C> \<in> \<M>'_of J' \<Longrightarrow> enabled \<C> J' \<Longrightarrow> enabled \<C> J\<close> for \<C>
        proof -
          assume C_in: \<open>\<C> \<in> \<M>'_of J'\<close> and
            \<open>enabled \<C> J'\<close>
          then have \<open>fset (A_of \<C>) \<subseteq> fset (A_of (\<J>'_of J'))\<close>
            using fsets_from_J[OF enab_nj'] by blast
          then show \<open>enabled \<C> J\<close>
            using A_of_J'_in unfolding enabled_def by auto
        qed
        then have \<open>(\<C> \<in> \<M>'_of J' \<and> enabled \<C> J') \<Longrightarrow> (\<C> \<in> \<M>'_of J' \<and> enabled \<C> J)\<close> for \<C>
          by (smt (verit, ccfv_threshold))
        then have \<open>{\<C>. \<C> \<in> \<M>'_of J' \<and> enabled \<C> J'} \<subseteq> {\<C>. \<C> \<in> \<M>'_of J' \<and> enabled \<C> J}\<close>
          by blast
        then show \<open>(\<M>'_of J') proj\<^sub>J J' \<subseteq> (\<M>'_of J') proj\<^sub>J J\<close>
          unfolding enabled_projection_def by blast
      qed
      ultimately have entails_one:  \<open>sound_cons.entails_neg
        (Pos ` (\<M>'_of J' proj\<^sub>J J) \<union> fml_ext ` (fset (A_of (\<J>'_of J')))) (Pos ` F_of ` \<N>'_of J')\<close>
        using sound_cons.entails_subsets
        by (smt (verit, ccfv_SIG) Un_absorb1 Un_assoc Un_left_commute image_Un
          neg_ext_sound_cons_rel.entails_subsets subset_refl sup.cobounded1)
      have subs_MJ: \<open>Pos ` (\<M>'_of J' proj\<^sub>J J) \<union>
        fml_ext ` (fset (A_of (\<J>'_of J'))) \<subseteq> Pos ` (\<M>' proj\<^sub>J J) \<union> fml_ext ` (total_strip J)\<close>
        using J'_in A_of_J'_in using enabled_projection_def unfolding \<M>'_def by auto
      have subs_N: \<open>Pos ` F_of ` (\<N>'_of J') \<subseteq> Pos ` F_of ` \<N>'\<close>
        using J'_in unfolding \<N>'_def by blast
      show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M>' proj\<^sub>J J))
        (Pos ` F_of ` \<N>')\<close>
        using neg_ext_sound_cons_rel.entails_subsets[OF subs_MJ subs_N entails_one]
        by (simp add: Un_commute)
    qed

    ultimately
    show \<open>\<exists>\<M>' \<N>'. \<M>' \<subseteq> \<M> \<and> \<N>' \<subseteq> \<N> \<and> finite \<M>' \<and> finite \<N>' \<and> \<M>' \<Turnstile>s\<^sub>A\<^sub>F \<N>'\<close>
      by blast
  qed
qed
  
interpretation AF_sound_cons_rel: consequence_relation "to_AF bot" AF_entails_sound
  by (rule AF_ext_sound_cons_rel)

lemma f_of_to_AF [simp]: \<open>F_of ` to_AF ` N = N\<close>
  unfolding to_AF_def by force

lemma to_AF_proj_J [simp]: \<open>to_AF ` M proj\<^sub>J J = M\<close>
  unfolding to_AF_def enabled_projection_def enabled_def by force

lemma enabled_to_AF_set [simp]: \<open>enabled_set (to_AF ` N) J\<close>
  unfolding enabled_set_def enabled_def to_AF_def by simp

lemma pos_not_pos_empty [simp]: \<open>{to_V C |C. C \<in> Pos ` N \<and> \<not> is_Pos C} = {}\<close>
  by auto
    
lemma pos_not_pos_simp [simp]:
  \<open>{to_V C |C. C \<in> U \<union> Pos ` M \<and> \<not> is_Pos C} = {to_V C |C. C \<in> U \<and> \<not> is_Pos C}\<close>
  by auto

lemma pos_pos_simp [simp]: \<open>{to_V C |C. C \<in> Pos ` F_of ` N \<and> is_Pos C} = F_of ` N\<close>
  by force 

lemma proj_F_of [simp]: \<open>{C. F_of C \<in> M} proj\<^sub>J J = M\<close>
proof (intro equalityI subsetI)
  fix x
  assume x_in: \<open>x \<in> {C. F_of C \<in> M} proj\<^sub>J J\<close>
  define C::"('f,'v) AF" where \<open>C = to_AF x\<close>
  then show \<open>x \<in> M\<close> 
    using x_in unfolding enabled_projection_def enabled_def to_AF_def by auto 
next
  fix x
  assume x_in: \<open>x \<in> M\<close>
  define C::"('f,'v) AF" where \<open>C = to_AF x\<close>
  then show \<open>x \<in>  {C. F_of C \<in> M} proj\<^sub>J J\<close> 
    using x_in unfolding enabled_projection_def enabled_def to_AF_def
    by (metis (mono_tags, lifting) AF.sel(1) AF.sel(2) bot_fset.rep_eq empty_subsetI mem_Collect_eq)
qed 

lemma f_of_F_of [simp]: \<open>F_of ` {C. F_of C \<in> M} = M\<close>
proof (intro equalityI subsetI)
  fix x
  assume x_in: \<open>x \<in> F_of ` {C. F_of C \<in> M}\<close>
  define C where \<open>C = to_AF x\<close>
  then show \<open>x \<in> M\<close>
    using x_in by blast 
next
  fix x
  assume x_in: \<open>x \<in> M\<close>
  define C where \<open>C = to_AF x\<close>
  then show \<open>x \<in> F_of ` {C. F_of C \<in> M}\<close>
    using x_in by (smt (z3) AF.sel(1) imageI mem_Collect_eq) 
qed
  
lemma set_on_union_triple_split: \<open>{f C |C. C \<in> M \<union> N \<union> g J \<and> l C J} = {f C |C. C \<in> M \<and> l C J} \<union>
  {f C |C. C \<in> N \<and> l C J} \<union> {f C |C. C \<in> g J \<and> l C J}\<close>
  by blast 

lemma not_enabled_enabled_empty [simp]:
  \<open>{F_of C |C. C \<in> {C. F_of C \<in> Q' \<and> \<not> enabled C J} \<and> enabled C J} = {}\<close>
proof (intro equalityI subsetI)
  fix x
  assume x_in: \<open>x \<in> {F_of C |C. C \<in> {C. F_of C \<in> Q' \<and> \<not> enabled C J} \<and> enabled C J}\<close>
  then obtain C where \<open>F_of C = x\<close> and c_in: \<open>C \<in> {C. F_of C \<in> Q' \<and> \<not> enabled C J}\<close> and
    enab_c: \<open>enabled C J\<close>
    by blast
  then have \<open>\<not> enabled C J\<close> using c_in by blast 
  then have \<open>False\<close> using enab_c by auto 
  then show \<open>x \<in> {}\<close> by auto 
qed auto

lemma f_of_simp_enabled [simp]: \<open>{F_of C |C. F_of C \<in> M \<and> enabled C J} = M\<close>
  unfolding enabled_def
  by (smt (verit, best) AF.sel(1) AF.sel(2) bot_fset.rep_eq empty_subsetI mem_Collect_eq subsetI
      subset_antisym)

lemma f_of_enabled_simp [simp]: \<open>F_of ` {C. F_of C \<in> M \<and> enabled C J} = M\<close>
proof -
  have \<open>F_of ` {C. F_of C \<in> M \<and> enabled C J} = {F_of C |C. F_of C \<in> M \<and> enabled C J}\<close>
    by blast 
  then show ?thesis by simp
qed

(* Splitting report Lemma 6, 1/2 *)
lemma \<open>(to_AF ` M \<Turnstile>\<^sub>A\<^sub>F to_AF ` N) \<equiv> (M \<Turnstile> N)\<close>
  unfolding AF_entails_def by simp

sublocale ext_cons_rel_std: consequence_relation "Pos (to_AF bot)" AF_cons_rel.entails_neg
  using AF_cons_rel.ext_cons_rel .

sublocale sound_cons_rel: consequence_relation "Pos bot" sound_cons.entails_neg
  using sound_cons.ext_cons_rel .

lemma [simp]: \<open>{C. Pos C \<in> Pos ` N} = N\<close> by auto
lemma [simp]: \<open>{C. Neg C \<in> Pos ` N} = {}\<close> by auto
lemma [simp]: \<open>{C. Neg C \<in> P \<or> Neg C \<in> Pos ` M} = {C. Neg C \<in> P}\<close> by blast
lemma [simp]: \<open>{C. Pos C \<in> P \<or> Pos C \<in> Pos ` M} = {C. Pos C \<in> P} \<union> M\<close> by auto
    
(* Splitting report Lemma 6, 2/2 *)
lemma \<open>(to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N) \<equiv> (M \<Turnstile>s N)\<close>
proof -
  {
    fix M N
    assume m_to_n: \<open>M \<Turnstile>s N\<close>
    have \<open>to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N\<close>
      unfolding AF_entails_sound_def sound_cons.entails_neg_def 
    proof (simp, rule allI)
      fix J
      have m_in: \<open>M \<subseteq> {to_V C |C. (C \<in> fml_ext ` total_strip J \<or> C \<in> Pos ` M) \<and> is_Pos C}\<close>
        by force
      show \<open> {C. Pos C \<in> fml_ext ` total_strip J} \<union> M \<Turnstile>s
        N \<union> {C. Neg C \<in> fml_ext ` total_strip J}\<close>
        using m_to_n m_in by (meson Un_subset_iff sound_cons.entails_subsets subset_refl)
    qed
  } moreover {
    fix M N
    assume m_af_entails_n: \<open>to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N\<close>
    have supsets_entail: \<open>\<forall>M' N'. (M' \<supseteq> M \<and> N' \<supseteq> N \<and> M' \<union> N' = UNIV) \<longrightarrow> M' \<Turnstile>s N'\<close>
    proof clarsimp 
      fix M' N'
      assume m_in: \<open>M \<subseteq> M'\<close> and
        n_in: \<open>N \<subseteq> N'\<close> and
        union_mnp_is_univ: \<open>M' \<union> N' = UNIV\<close>
      {
        assume \<open>M' \<inter> N' \<noteq> {}\<close>
        then have \<open>M' \<Turnstile>s N'\<close>
          using sound_cons.entails_reflexive sound_cons.entails_subsets
          by (meson Int_lower1 Int_lower2 sound_cons.entails_cond_reflexive)
      }
      moreover {
        assume empty_inter_mp_np: \<open>M' \<inter> N' = {}\<close>
        define Jpos where \<open>Jpos = {v. to_V (fml_ext v) \<in> M' \<and> is_Pos v}\<close>
        define Jneg where \<open>Jneg = {v |v. to_V (fml_ext v) \<notin> M' \<and> \<not> is_Pos v}\<close>
        have total_J_pos_neg: \<open>to_V ` (Jpos \<union> Jneg) = UNIV\<close>
        proof
          show \<open>to_V ` (Jpos \<union> Jneg) \<subseteq> UNIV\<close> by simp
        next
          show \<open>UNIV \<subseteq> to_V ` (Jpos \<union> Jneg) \<close>
          proof
            fix v::"'v"
            define v_p where \<open>v_p = Pos v\<close>
            define v_n where \<open>v_n = Neg v\<close>
            have \<open>v_p \<notin> Jpos \<Longrightarrow> v_n \<in> Jneg\<close>
              unfolding v_p_def v_n_def Jpos_def Jneg_def by simp
            then show \<open>v \<in> to_V ` (Jpos \<union> Jneg)\<close>
              unfolding v_p_def v_n_def by force
          qed
        qed
        define Jstrip where \<open>Jstrip = Jpos \<union> Jneg\<close>
        have interp_Jstrip: \<open>is_interpretation Jstrip\<close>
          unfolding is_interpretation_def 
        proof (clarsimp, rule ccontr)
          fix v1 v2
          assume v1_in: \<open>v1 \<in> Jstrip\<close> and
            v2_in: \<open>v2 \<in> Jstrip\<close> and
            v12_eq: \<open>to_V v1 = to_V v2\<close> and
            contra: \<open>v1 \<noteq> v2\<close>
          have pos_neg_cases: \<open>(v1 \<in> Jpos \<and> v2 \<in> Jneg) \<or> (v1 \<in> Jneg \<and> v2 \<in> Jpos)\<close>
            using v1_in v2_in contra unfolding Jstrip_def Jpos_def Jneg_def
            by (smt (z3) Collect_mono_iff Collect_subset Un_def is_Neg_to_V is_Pos_to_V v12_eq)
          then have \<open>to_V (fml_ext v1) \<noteq> to_V (fml_ext v2)\<close>
            using empty_inter_mp_np unfolding Jneg_def Jpos_def by auto 
          then show \<open>False\<close>
            using fml_ext_preserves_val[OF v12_eq] by blast 
        qed
        then obtain Jinterp where Jinterp_is: "strip Jinterp = Jstrip"
          by (metis Rep_propositional_interpretation_cases mem_Collect_eq)
        have \<open>total Jinterp\<close>
          unfolding total_def
        proof
          fix v
          define v_p::"'v sign" where "v_p = Pos v"
          define v_n::"'v sign" where "v_n = Neg v"
          have "v_p \<in> Jpos \<or> v_n \<in> Jneg"
            unfolding v_p_def v_n_def Jpos_def Jneg_def by simp
          then have "v_p \<in> Jstrip \<or> v_n \<in> Jstrip"
            unfolding Jstrip_def by fast
          then have \<open>v_p \<in>\<^sub>J Jinterp \<or> v_n \<in>\<^sub>J Jinterp\<close>
            using Jinterp_is unfolding belong_to_def by simp
          then show \<open>\<exists>v\<^sub>J. v\<^sub>J \<in>\<^sub>J Jinterp \<and> to_V v\<^sub>J = v\<close>
            using v_p_def v_n_def by auto
        qed
        then obtain Jtotal where Jtotal_is: "total_strip Jtotal = Jstrip"
          using Jinterp_is by (metis Rep_total_interpretation_cases mem_Collect_eq)
        have \<open>enabled_set (to_AF ` N) Jtotal\<close>
          unfolding enabled_set_def to_AF_def enabled_def using Jtotal_is Jstrip_def Jneg_def
          by simp
        then have \<open>fml_ext ` total_strip Jtotal \<union> Pos ` M \<Turnstile>s\<^sub>\<sim> Pos ` N\<close>
          using m_af_entails_n unfolding AF_entails_sound_def by simp
        then have entails_m_n_jtot: \<open>{C. Pos C \<in> fml_ext ` total_strip Jtotal} \<union> M  \<Turnstile>s
           N \<union> {C. Neg C \<in> fml_ext ` total_strip Jtotal}\<close>
          unfolding sound_cons.entails_neg_def by simp
        have \<open>{C. Pos C \<in> fml_ext ` total_strip Jtotal} \<subseteq> M'\<close>
          unfolding Jtotal_is Jstrip_def Jpos_def Jneg_def
          by (smt (verit, ccfv_threshold) UnE fml_ext_preserves_sign imageE is_Pos.simps(1)
            mem_Collect_eq subsetI to_V.simps(1))
        then have sub_mp: \<open>{C. Pos C \<in> fml_ext ` total_strip Jtotal} \<union> M \<subseteq> M'\<close>
          using m_in by simp
        have \<open>{C. Neg C \<in> fml_ext ` total_strip Jtotal} \<subseteq> N'\<close>
          unfolding Jtotal_is Jstrip_def Jpos_def Jneg_def
        proof -
          have \<open>{C. Neg C \<in> fml_ext ` {v. to_V (fml_ext v) \<in> M' \<and> is_Pos v}} = {}\<close>
            using fml_ext_preserves_sign is_Pos.simps(1)
            by (smt (verit, ccfv_SIG) empty_iff imageE is_Pos.simps(2) mem_Collect_eq subsetI
              subset_antisym)
          moreover have \<open>{C. Neg C \<in> fml_ext ` {v |v. to_V (fml_ext v) \<notin> M' \<and> \<not> is_Pos v}} \<subseteq> N'\<close>
            using fml_ext_preserves_sign is_Pos.simps(2)
          proof -
            have \<open>{C. Neg C \<in> fml_ext ` {v |v. to_V (fml_ext v) \<notin> M' \<and> \<not> is_Pos v}} =
              {C. Neg C \<in> fml_ext ` {v |v. to_V (fml_ext v) \<in> N' \<and> \<not> is_Pos v}}\<close>
              using empty_inter_mp_np union_mnp_is_univ by auto 
            also have \<open>{C. Neg C \<in> fml_ext ` {v |v. to_V (fml_ext v) \<in> N' \<and> \<not> is_Pos v}} \<subseteq> N'\<close>
              using fml_ext_preserves_sign is_Pos.simps(2)
              by (smt (verit, best) imageE mem_Collect_eq subsetI to_V.simps(2))      
            finally show \<open>{C. Neg C \<in> fml_ext ` {v |v. to_V (fml_ext v) \<notin> M' \<and> \<not> is_Pos v}} \<subseteq> N'\<close> .
                  (* by (smt (verit) UNIV_I UnE image_iff mem_Collect_eq subsetI to_V.simps(2) union_mnp_is_univ) *) (* proof suggested but fails to terminate *)
          qed
          ultimately show \<open>{C. Neg C \<in> fml_ext `
            ({v. to_V (fml_ext v) \<in> M' \<and> is_Pos v} \<union>
            {v |v. to_V (fml_ext v) \<notin> M' \<and> \<not> is_Pos v})}
            \<subseteq> N'\<close>
            by blast
        qed
        then have sub_np: \<open>N \<union> {C. Neg C \<in> fml_ext ` total_strip Jtotal} \<subseteq> N'\<close>
          using n_in by blast
        have \<open>M' \<Turnstile>s N'\<close>
          using sound_cons.entails_subsets[OF sub_mp sub_np entails_m_n_jtot] .
      }
      ultimately show "M' \<Turnstile>s N'" by blast
    qed
    then have \<open>M \<Turnstile>s N\<close>
      using sound_cons.entails_supsets by simp
  }
  ultimately show \<open>(to_AF ` M \<Turnstile>s\<^sub>A\<^sub>F to_AF ` N) \<equiv> (M \<Turnstile>s N)\<close>
    by (smt (verit, best))
qed

lemma strong_entails_bot_cases: \<open>\<N> \<union> {AF.Pair bot A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B} \<Longrightarrow>
  (\<forall> J. fset B \<subseteq> total_strip J \<longrightarrow>
    (fml_ext ` total_strip J \<union> Pos ` (\<N> proj\<^sub>J J)) \<Turnstile>s\<^sub>\<sim> {Pos bot} \<or> fset A \<subseteq> total_strip J)\<close>
proof -
  assume \<open>\<N> \<union> {AF.Pair bot A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B}\<close>
  then have \<open>fset B \<subseteq> total_strip J \<Longrightarrow>
              (fml_ext ` total_strip J \<union> Pos ` (\<N> proj\<^sub>J J) \<union> Pos ` ({AF.Pair bot A} proj\<^sub>J J))
              \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
    for J
    unfolding AF_entails_sound_def
    by (metis (no_types, lifting) AF.sel(1) AF.sel(2) distrib_proj_singleton enabled_def
         enabled_set_def image_Un image_empty image_insert singletonD sup_assoc)
  then have \<open>fset B \<subseteq> total_strip J \<Longrightarrow>
        ((fml_ext ` total_strip J) \<union> Pos ` (\<N> proj\<^sub>J J)) \<Turnstile>s\<^sub>\<sim> {Pos bot} \<or> enabled (AF.Pair bot A) J\<close>
    for J 
    by (smt (verit, ccfv_SIG) enabled_projection_def ex_in_conv image_empty
         mem_Collect_eq singletonD sup_bot_right)
  then show ?thesis
    by (simp add: enabled_def)
qed

lemma strong_entails_bot_cases_Union:
  \<open>\<N> \<union> \<M> \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B} \<Longrightarrow> (\<forall> x \<in> \<M>. F_of x = bot) \<Longrightarrow>
    (\<forall> J. fset B \<subseteq> total_strip J \<longrightarrow>
      (fml_ext ` total_strip J \<union> Pos ` (\<N> proj\<^sub>J J)) \<Turnstile>s\<^sub>\<sim> {Pos bot} \<or>
      (\<exists> A \<in> A_of ` \<M>. fset A \<subseteq> total_strip J))\<close>
proof -
  assume \<N>_union_\<M>_entails_Pair_bot_B: \<open>\<N> \<union> \<M> \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B}\<close> and
         \<open>\<forall> x \<in> \<M>. F_of x = bot\<close>
  then show ?thesis
  proof (cases \<open>\<M> = {}\<close>)
    case True
    then show ?thesis
      using AF_entails_sound_def \<N>_union_\<M>_entails_Pair_bot_B enabled_def enabled_set_def
      by auto
  next
    case False
    then show ?thesis
    proof (intro allI impI)
      fix J
      assume B_in_J: \<open>fset B \<subseteq> total_strip J\<close>
      then show \<open>(fml_ext ` total_strip J \<union> Pos ` (\<N> proj\<^sub>J J)) \<Turnstile>s\<^sub>\<sim> {Pos bot} \<or>
                    (\<exists> A \<in> A_of ` \<M>. fset A \<subseteq> total_strip J)\<close>
      proof (cases \<open>\<exists> A \<in> A_of ` \<M>. fset A \<subseteq> total_strip J\<close>)
        case True
        then show ?thesis
          by blast
      next
        case False
        then have \<open>\<forall> A \<in> A_of ` \<M>. \<not> fset A \<subseteq> total_strip J\<close>
          by blast
        then have \<open>\<M> proj\<^sub>J J = {}\<close>
          by (simp add: enabled_def enabled_projection_def)
        then show ?thesis
          using \<N>_union_\<M>_entails_Pair_bot_B[unfolded AF_entails_sound_def, rule_format]
                B_in_J distrib_proj enabled_def enabled_set_def
          by fastforce
      qed
    qed
  qed
qed


lemma AF_entails_sound_right_disjunctive: \<open>(\<exists> \<C>' \<in> A. \<M> \<Turnstile>s\<^sub>A\<^sub>F {\<C>'}) \<Longrightarrow> \<M> \<Turnstile>s\<^sub>A\<^sub>F A\<close>
proof -
  assume \<open>\<exists> \<C>' \<in> A. \<M> \<Turnstile>s\<^sub>A\<^sub>F {\<C>'}\<close>
  then obtain \<C>' where \<open>\<M> \<Turnstile>s\<^sub>A\<^sub>F {\<C>'}\<close> and
                       \<open>\<C>' \<in> A\<close>
    by blast
  then show \<open>\<M> \<Turnstile>s\<^sub>A\<^sub>F A\<close>
    by (meson AF_sound_cons_rel.entails_subsets empty_subsetI insert_subset subset_refl)
qed

subsection \<open>Local saturation\<close>

text \<open> To fully capture completeness for splitting, we need to use weaker notions of saturation and
 fairness.\<close>

(* Report definition 23 *)
definition locally_saturated :: \<open>('f, 'v) AF set \<Rightarrow> bool\<close> where
  \<open>locally_saturated \<N> \<equiv>
    to_AF bot \<in> \<N> \<or>
    (\<exists> J :: 'v total_interpretation. J \<Turnstile>\<^sub>p \<N> \<and> saturated (\<N> proj\<^sub>J J))\<close>
    (* NOTE: in the paper, the propositional projection is explicit.
     * In our case, it is hidden within the definition for @{const propositional_model}. *)

(* Report definition 26 *)
definition locally_fair :: \<open>('f, 'v) AF set infinite_llist \<Rightarrow> bool\<close> where
  \<open>locally_fair \<N>i \<equiv>
     (\<exists> i. to_AF bot \<in> llnth \<N>i i)
   \<or> (\<exists> J :: 'v total_interpretation. J \<Turnstile>\<^sub>p lim_inf \<N>i \<and>
        Inf_from (lim_inf \<N>i proj\<^sub>J J) \<subseteq> (\<Union> i. Red\<^sub>I (llnth \<N>i i proj\<^sub>J J)))\<close>

end (* locale AF_calculus_lifting *)

locale strong_statically_complete_AF_calculus_lifting =  
  AF_calculus_lifting  bot Inf entails entails_sound Red\<^sub>I Red_F fml asn
  + S_calculus: calculus "to_AF bot" SInf AF_entails SRed\<^sub>I SRed\<^sub>F
  for
    bot :: "'f" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) and
    entails_sound :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>s" 50) and
    Red\<^sub>I :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set" and
    fml :: \<open>'v :: countable \<Rightarrow> 'f\<close> and 
    asn :: \<open>'f sign \<Rightarrow> 'v sign set\<close> and
    SInf :: "('f, 'v) AF inference set" and
    SRed\<^sub>I :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set" and
    SRed\<^sub>F :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set"
  + assumes
    strong_static_completeness: \<open>locally_saturated \<N> \<Longrightarrow> \<N> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<Longrightarrow> to_AF bot \<in> \<N>\<close>

locale strong_dynamically_complete_AF_calculus_lifting =  
  AF_calculus_lifting  bot Inf entails entails_sound Red\<^sub>I Red_F fml asn
  + S_calculus: calculus "to_AF bot" SInf AF_entails SRed\<^sub>I SRed\<^sub>F
  for
    bot :: "'f" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) and
    entails_sound :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>s" 50) and
    Red\<^sub>I :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set" and
    fml :: \<open>'v :: countable \<Rightarrow> 'f\<close> and 
    asn :: \<open>'f sign \<Rightarrow> 'v sign set\<close> and
    SInf :: "('f, 'v) AF inference set" and
    SRed\<^sub>I :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set" and
    SRed\<^sub>F :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set"
  + assumes
    strong_dynamic_completeness: \<open>is_derivation S_calculus.derive \<N>i \<Longrightarrow> locally_fair \<N>i \<Longrightarrow>
      llhd \<N>i \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<Longrightarrow> \<exists>i. to_AF bot \<in> llnth \<N>i i\<close>


end