(* Title:        Formalizing an abstract calculus based on splitting in a modular way
 * Author:       Ghilain Bergeron <ghilain.bergeron at inria.fr>, 2023
 *               Sophie Tourret <sophie.tourret at inria.fr>, 2024 *)

theory Modular_Splitting_Calculus
  imports
    Calculi_And_Annotations
    Light_Lifting_to_Non_Ground_Calculi
    List_Extra
    FSet_Extra
begin


section \<open>Core splitting calculus\<close>
                                                                                          
text \<open>
  In this section, we formalize an abstract version of a splitting calculus.
  We start by considering only two basic rules:
  \<^item> \textsc{Base} performs an inference from our inference system;
  \<^item> \textsc{Unsat} replaces a set of prosopositionally unsatisfiable formulas with \<open>\<bottom>\<close>.
\<close>

locale annotated_calculus = calculus_with_annotated_consrel bot FInf entails entails_sound FRed\<^sub>I 
  FRed\<^sub>F fml asn
  for bot :: 'f and
      FInf :: \<open>'f inference set\<close> and
      entails :: \<open>[ 'f set, 'f set ] \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) and
      entails_sound :: \<open>[ 'f set, 'f set ] \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50) and
      FRed\<^sub>I :: \<open>'f set \<Rightarrow> 'f inference set\<close> and
      FRed\<^sub>F :: \<open>'f set \<Rightarrow> 'f set\<close> and
      fml :: \<open>'v :: countable \<Rightarrow> 'f\<close> and
      asn :: \<open>'f sign \<Rightarrow> 'v sign set\<close> 
  + assumes
      (* D6 *)
      entails_nontrivial: \<open>\<not> {} \<Turnstile> {}\<close> and
      (* R5 *)
      reducedness: \<open>Inf_between UNIV (FRed\<^sub>F N) \<subseteq> FRed\<^sub>I N\<close> and
      (* R6 *)
      complete: \<open>bot \<notin> FRed\<^sub>F N\<close> and
      (* R7 *)
      all_red_to_bot: \<open>\<C> \<noteq> bot \<Longrightarrow> \<C> \<in> FRed\<^sub>F {bot}\<close>
begin

notation sound_cons.entails_neg (infix \<open>\<Turnstile>s\<^sub>\<sim>\<close> 50) 

subsection \<open>The inference rules\<close>

(* The basic SInf inference system, with the two basic rules BASE and UNSAT.
 *
 * \<open>Splitting_rules \<iota>\<close> means that \<open>\<iota>\<close> is an inference rule of the system S *)

text \<open>
  Every inference rule $X$ is defined using two functions: $X\_pre$ and $X\_inf$.
  $X\_inf$ is the inference rule itself, while $X\_pre$ are side-conditions for
  the rule to be applicable.
\<close>

abbreviation base_pre :: \<open>('f, 'v) AF list \<Rightarrow> 'f \<Rightarrow> bool\<close> where
  \<open>base_pre \<N> D \<equiv> Infer (map F_of \<N>) D \<in> FInf\<close>

abbreviation base_inf :: \<open>('f, 'v) AF list \<Rightarrow> 'f \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>base_inf \<N> D \<equiv> Infer \<N> (Pair D (ffUnion (fset_of_list (map A_of \<N>))))\<close>

abbreviation unsat_pre :: \<open>('f, 'v) AF list \<Rightarrow> bool\<close> where
  \<open>unsat_pre \<N> \<equiv> (\<forall> x \<in> set \<N>. F_of x = bot) \<and> propositionally_unsatisfiable (set \<N>)\<close>

abbreviation unsat_inf :: \<open>('f, 'v) AF list \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>unsat_inf \<N> \<equiv> Infer \<N> (to_AF bot)\<close>

text \<open>
  We consider first only the inference rules \textsc{Base} and \textsc{Unsat}. The optional 
  inference and simplification rules are handled separately in the locales 
  \<open>splitting_calculus_extensions\<close> and \<open>splitting_calculus_with_simps\<close> respectively.
\<close>

inductive_set SInf :: \<open>('f, 'v) AF inference set\<close> where
  base: \<open>base_pre \<N> D \<Longrightarrow> base_inf \<N> D \<in> SInf\<close>
| unsat: \<open>unsat_pre \<N> \<Longrightarrow> unsat_inf \<N> \<in> SInf\<close> 

text \<open>
  The predicates in @{term Splitting_rules} form a valid inference system.
\<close>
interpretation SInf_inf_system: inference_system SInf .

lemma not_empty_entails_bot: \<open>\<not>{} \<Turnstile> {bot}\<close>
  using entails_bot_to_entails_empty entails_nontrivial
  by blast

text \<open>
  The proof for Lemma 13 is split into two parts, for each inclusion in the set equality.
\<close>

(* Report lemma 13 1/2 *)
lemma SInf_commutes_Inf1:
  \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J \<subseteq> Inf_from (\<N> proj\<^sub>J J)\<close>
proof (intro subsetI)
  fix \<iota>\<^sub>S
  assume bot_not_in_proj: \<open>bot \<notin> \<N> proj\<^sub>J J\<close> and
         \<iota>\<^sub>S_is_inf: \<open>\<iota>\<^sub>S \<in> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J\<close>

  have no_enabled_prop_clause_in_\<N>: \<open>\<forall> \<C> \<in> \<N>. enabled \<C> J \<longrightarrow> F_of \<C> \<noteq> bot\<close>
    using bot_not_in_proj
    unfolding enabled_projection_def
    by blast

  obtain \<iota>\<^sub>F where \<iota>\<^sub>S_is: \<open>\<iota>\<^sub>S = \<iota>F_of \<iota>\<^sub>F\<close> and
                 \<iota>\<^sub>F_is_inf: \<open>\<iota>\<^sub>F \<in> inference_system.Inf_from SInf \<N>\<close> and
                 \<iota>\<^sub>F_is_enabled: \<open>enabled_inf \<iota>\<^sub>F J\<close>
    using \<iota>\<^sub>S_is_inf enabled_projection_Inf_def
    by auto
  then have \<iota>\<^sub>F_in_S: \<open>\<iota>\<^sub>F \<in> SInf\<close>
    by (simp add: inference_system.Inf_from_def)
  moreover have prems_of_\<iota>\<^sub>F_subset_\<N>: \<open>set (prems_of \<iota>\<^sub>F) \<subseteq> \<N>\<close>
    using \<iota>\<^sub>F_is_inf
    by (simp add: inference_system.Inf_from_def)
  moreover have \<open>\<iota>F_of \<iota>\<^sub>F \<in> FInf\<close>
    unfolding \<iota>F_of_def
    using \<iota>\<^sub>F_in_S
  proof (cases \<iota>\<^sub>F rule: SInf.cases)
    case (base \<N> D)
    then show \<open>base_pre (prems_of \<iota>\<^sub>F) (F_of (concl_of \<iota>\<^sub>F))\<close>
      by auto
  next
    case (unsat \<N>)
    moreover have \<open>enabled_inf \<iota>\<^sub>F J\<close>
      using \<iota>\<^sub>F_is_enabled
      by fastforce
    then have \<open>\<forall> \<C> \<in> set \<N>. F_of \<C> \<noteq> bot\<close>
      by (metis enabled_inf_def inference.sel(1) local.unsat(1) no_enabled_prop_clause_in_\<N>
           prems_of_\<iota>\<^sub>F_subset_\<N> subset_eq)
    then have \<open>False\<close>
      using not_empty_entails_bot unsat(2) enabled_projection_def prop_proj_in
        propositional_model_def propositionally_unsatisfiable_def by auto
    ultimately show \<open>base_pre (prems_of \<iota>\<^sub>F) (F_of (concl_of \<iota>\<^sub>F))\<close>
      by blast
  qed
  moreover have \<open>set (prems_of (\<iota>F_of \<iota>\<^sub>F)) \<subseteq> \<N> proj\<^sub>J J\<close>
    using \<iota>\<^sub>F_is_enabled prems_of_\<iota>\<^sub>F_subset_\<N>
    by (auto simp add: enabled_inf_def enabled_projection_def \<iota>F_of_def)
  ultimately have \<open>\<iota>F_of \<iota>\<^sub>F \<in> Inf_from (\<N> proj\<^sub>J J)\<close>
    by (simp add: Inf_from_def)
  then show \<open>\<iota>\<^sub>S \<in> Inf_from (\<N> proj\<^sub>J J)\<close>
    by (simp add: \<iota>\<^sub>S_is)
qed

(* Report lemma 13 2/2 *)
lemma SInf_commutes_Inf2:
  \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> Inf_from (\<N> proj\<^sub>J J) \<subseteq> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J\<close>
proof (intro subsetI)
  fix \<iota>\<^sub>F
  assume bot_not_in_proj: \<open>bot \<notin> \<N> proj\<^sub>J J\<close> and
         \<iota>\<^sub>F_in_inf: \<open>\<iota>\<^sub>F \<in> Inf_from (\<N> proj\<^sub>J J)\<close>

  have \<iota>\<^sub>F_is_Inf: \<open>\<iota>\<^sub>F \<in> FInf\<close>
    using Inf_if_Inf_from \<iota>\<^sub>F_in_inf
    by blast
  have \<open>set (prems_of \<iota>\<^sub>F) \<subseteq> \<N> proj\<^sub>J J\<close>
    using Inf_from_def \<iota>\<^sub>F_in_inf
    by blast
  then have \<open>\<forall> \<C> \<in> set (prems_of \<iota>\<^sub>F). \<exists> A. Pair \<C> A \<in> \<N> \<and> enabled (Pair \<C> A) J\<close>
    by (smt (verit, ccfv_SIG) AF.collapse enabled_projection_def mem_Collect_eq subsetD)
  then have \<open>list_all (\<lambda> \<C>. \<exists> A. Pair \<C> A \<in> \<N> \<and> enabled (Pair \<C> A) J) (prems_of \<iota>\<^sub>F)\<close>
    using Ball_set
    by blast
  then obtain As where
      length_As_is_length_prems_\<iota>\<^sub>F: \<open>length (prems_of \<iota>\<^sub>F) = length As\<close> and
      As_def: \<open>\<forall> (C, A) \<in> set (zip (prems_of \<iota>\<^sub>F) As). Pair C A \<in> \<N> \<and> enabled (Pair C A) J\<close>
    by (smt (verit, del_insts) Ball_set_list_all list_all2_iff list_all_exists_is_exists_list_all2)
  define \<iota>\<^sub>S where
    \<open>\<iota>\<^sub>S \<equiv> Infer [ Pair \<C> A. (\<C>, A) \<leftarrow> zip (prems_of \<iota>\<^sub>F) As ]
                (Pair (concl_of \<iota>\<^sub>F) (ffUnion (fset_of_list As)))\<close>
  have \<iota>\<^sub>F_is_Inf2: \<open>Infer (map F_of [ Pair \<C> A. (\<C>, A) \<leftarrow> zip (prems_of \<iota>\<^sub>F) As ]) (concl_of \<iota>\<^sub>F) \<in> FInf\<close>
    using length_As_is_length_prems_\<iota>\<^sub>F
    by (auto simp add: \<iota>\<^sub>F_is_Inf)
  then have \<iota>\<^sub>S_is_SInf: \<open>\<iota>\<^sub>S \<in> SInf\<close>
    using SInf.base[OF \<iota>\<^sub>F_is_Inf2] length_As_is_length_prems_\<iota>\<^sub>F
    unfolding \<iota>\<^sub>S_def
    by auto
  moreover have \<open>set (prems_of \<iota>\<^sub>S) \<subseteq> \<N>\<close>
    unfolding \<iota>\<^sub>S_def
    using As_def
    by auto
  then have \<open>\<iota>\<^sub>S \<in> inference_system.Inf_from SInf \<N>\<close>
    using inference_system.Inf_from_def \<iota>\<^sub>S_is_SInf
    by blast
  moreover have \<open>\<iota>F_of \<iota>\<^sub>S = \<iota>\<^sub>F\<close>
    unfolding \<iota>\<^sub>S_def \<iota>F_of_def
    by (simp add: length_As_is_length_prems_\<iota>\<^sub>F)
  moreover have \<open>enabled_inf \<iota>\<^sub>S J\<close>
    unfolding enabled_inf_def \<iota>\<^sub>S_def
    using As_def
    by auto
  ultimately have \<open>\<exists> \<iota>'. \<iota>\<^sub>F = \<iota>F_of \<iota>' \<and> \<iota>' \<in> inference_system.Inf_from SInf \<N> \<and> enabled_inf \<iota>' J\<close>
    by blast
  then show \<open>\<iota>\<^sub>F \<in> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J\<close>
    unfolding enabled_projection_Inf_def
    by simp
qed

text \<open>
  We use @{thm SInf_commutes_Inf1} and @{thm SInf_commutes_Inf2} to put the Lemma 13
  together into a single proof.
\<close>

(* Report lemma 13 *)
lemma SInf_commutes_Inf:
  \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J = Inf_from (\<N> proj\<^sub>J J)\<close>
  using SInf_commutes_Inf1 SInf_commutes_Inf2
  by blast

(* Report theorem 14 for the cases Base and Unsat *)
theorem SInf_sound_wrt_entails_sound: \<open>\<iota>\<^sub>S \<in> SInf \<Longrightarrow> set (prems_of \<iota>\<^sub>S) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>\<^sub>S}\<close>
proof -
  assume \<open>\<iota>\<^sub>S \<in> SInf\<close>
  then show \<open>set (prems_of \<iota>\<^sub>S) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>\<^sub>S}\<close>
  proof (cases \<iota>\<^sub>S rule: SInf.cases)
    case (base \<N> D)
    assume \<open>base_pre \<N> D\<close>
    then have inf_is_sound: \<open>set (map F_of \<N>) \<Turnstile>s {D}\<close>
      using sound
      by fastforce
    then show ?thesis
      unfolding AF_entails_sound_def sound_cons.entails_neg_def
    proof (intro allI impI)
      fix J
      assume \<open>enabled_set {concl_of \<iota>\<^sub>S} J\<close>
      then have Pair_D_A_of_\<N>_is_enabled: \<open>enabled_set {concl_of \<iota>\<^sub>S} J\<close>
        using base
        by simp
      then have \<open>F_of ` {concl_of \<iota>\<^sub>S} = {D}\<close>
        using base
        by simp
      moreover have \<open>fset (ffUnion (fset_of_list (map A_of \<N>))) \<subseteq> total_strip J\<close>
        using Pair_D_A_of_\<N>_is_enabled
        unfolding enabled_set_def enabled_def
        by (simp add: local.base(1))
      then have \<open>fBall (fset_of_list (map A_of \<N>)) (\<lambda> As. fset As \<subseteq> total_strip J)\<close>
        using fset_ffUnion_subset_iff_all_fsets_subset
        by fast
      then have \<open>\<forall> As \<in> set (map A_of \<N>). fset As \<subseteq> total_strip J\<close>
        by (meson fset_of_list_elem)
      then have \<open>\<forall> \<C> \<in> set \<N>. enabled \<C> J\<close>
        unfolding enabled_def
        by simp
      then have \<open>set \<N> proj\<^sub>J J = F_of ` set \<N>\<close>
        unfolding enabled_projection_def
        by auto
      moreover have \<open>{C. Pos C \<in> fml_ext ` total_strip J \<union> Pos ` F_of ` set \<N>} \<Turnstile>s {D}\<close>
        using inf_is_sound
       by (smt (verit, ccfv_threshold) UnCI imageI list.set_map mem_Collect_eq
            sound_cons.entails_subsets subsetI)  
      moreover have \<open>{C. Neg C \<in> Pos ` F_of ` {concl_of \<iota>\<^sub>S}} = {}\<close>
        by fast
      ultimately show \<open>{C. Pos C \<in> fml_ext ` total_strip J \<union> Pos ` (set (prems_of \<iota>\<^sub>S) proj\<^sub>J J)} \<union>
                       {C. Neg C \<in> Pos ` F_of ` {concl_of \<iota>\<^sub>S}} \<Turnstile>s
                       {C. Pos C \<in> Pos ` F_of ` {concl_of \<iota>\<^sub>S}} \<union>
                       {C. Neg C \<in> fml_ext ` total_strip J \<union> Pos ` (set (prems_of \<iota>\<^sub>S) proj\<^sub>J J)}\<close>
        (* /!\ Careful, this one is a little bit slow (enough to be noticed) /!\ *)
        using base
        by (smt (verit, del_insts) UnCI imageI inference.sel(1) inference.sel(2) mem_Collect_eq
             sound_cons.entails_subsets subsetI)
    qed
  next
    case (unsat \<N>)
    assume pre_cond: \<open>unsat_pre \<N>\<close>
    then have heads_of_\<N>_are_bot: \<open>\<forall> x \<in> set \<N>. F_of x = bot\<close> and
              \<N>_is_prop_unsat: \<open>propositionally_unsatisfiable (set \<N>)\<close>
      by blast+
    then have \<open>proj\<^sub>\<bottom> (set \<N>) = set \<N>\<close>
      using heads_of_\<N>_are_bot propositional_projection_def
      by blast
    then have \<open>\<forall> J. bot \<in> (set \<N>) proj\<^sub>J J\<close>
      using \<N>_is_prop_unsat propositional_model_def propositionally_unsatisfiable_def
      by force
    then show ?thesis
      unfolding AF_entails_sound_def sound_cons.entails_neg_def
      using unsat
      by auto
         (smt (verit) Un_insert_right insertI1 insert_absorb sound_cons.bot_entails_empty
          sound_cons.entails_subsets subsetI sup_bot_right)  
  qed
qed

text \<open>The lifted calculus provides a consequence relation and a sound inference system.\<close>
interpretation AF_sound_cons_rel: consequence_relation \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  by (rule AF_ext_sound_cons_rel)

interpretation SInf_sound_inf_system: sound_inference_system SInf \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  by (standard, auto simp add: SInf_sound_wrt_entails_sound)


subsection \<open>The redundancy criterion\<close>

(* Report definition 15: splitting redundancy criterion *)
definition SRed\<^sub>F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> where
  \<open>SRed\<^sub>F \<N> = { AF.Pair C A | C A. \<forall> \<J>. total_strip \<J> \<supseteq> fset A \<longrightarrow> C \<in> FRed\<^sub>F (\<N> proj\<^sub>J \<J>) }
            \<union> { AF.Pair C A | C A. \<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> A_of \<C> |\<subset>| A }\<close>

definition SRed\<^sub>I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> where
  \<open>SRed\<^sub>I \<N> = { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and>
                 (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> FRed\<^sub>I (\<N> proj\<^sub>J \<J>)) }
           \<union> { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> \<N> }\<close>

(* Report lemma 16 *)
lemma sredI_\<N>_proj_J_subset_redI_proj_J: \<open>to_AF bot \<notin> \<N> \<Longrightarrow> (SRed\<^sub>I \<N>) \<iota>proj\<^sub>J J \<subseteq> FRed\<^sub>I (\<N> proj\<^sub>J J)\<close>
proof -
  assume \<open>to_AF bot \<notin> \<N>\<close>
  then have SRed\<^sub>I_\<N>_is:
    \<open>SRed\<^sub>I \<N> = { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and>
                   (\<forall> \<J>. {base_inf \<M> \<C>} \<iota>proj\<^sub>J \<J> \<subseteq> FRed\<^sub>I (\<N> proj\<^sub>J \<J>)) }\<close>
    using SRed\<^sub>I_def
    by auto
  then show \<open>(SRed\<^sub>I \<N>) \<iota>proj\<^sub>J J \<subseteq> FRed\<^sub>I (\<N> proj\<^sub>J J)\<close>
  proof (cases \<open>(SRed\<^sub>I \<N>) \<iota>proj\<^sub>J J = {}\<close>)
    case True
    then show ?thesis
      by fast
  next
    case False
    then obtain \<iota>\<^sub>S where \<open>\<iota>\<^sub>S \<in> SRed\<^sub>I \<N>\<close>
      using enabled_projection_Inf_def
      by fastforce
    then have \<open>{\<iota>\<^sub>S} \<iota>proj\<^sub>J J \<subseteq> FRed\<^sub>I (\<N> proj\<^sub>J J)\<close>
      using SRed\<^sub>I_\<N>_is
      by auto
    then show ?thesis
      using SRed\<^sub>I_\<N>_is enabled_projection_Inf_def
      by force
  qed
qed

(* Report lemma 17 *)
lemma bot_not_in_sredF_\<N>: \<open>to_AF bot \<notin> SRed\<^sub>F \<N>\<close>
proof -
  have \<open>to_AF bot \<notin> { AF.Pair C A | C A. \<forall> \<J>. total_strip \<J> \<supseteq> fset A \<longrightarrow> C \<in> FRed\<^sub>F (\<N> proj\<^sub>J \<J>) }\<close>
    by (simp add: complete to_AF_def)
  moreover have \<open>to_AF bot \<notin> { AF.Pair C A | C A. \<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> A_of \<C> |\<subset>| A }\<close>
    by (simp add: to_AF_def)
  moreover have \<open>to_AF bot \<notin> { AF.Pair C A | C A. \<forall> J. \<not> fset A \<subseteq> total_strip J }\<close>
    by (simp add: to_AF_def)
  ultimately show ?thesis
    using SRed\<^sub>F_def
    by auto
qed

text \<open>
  We need to set things up for the proof of lemma 18.
  We first restrict @{const SRed\<^sub>I} to \textsc{Base} inferences (under the name \<open>ARed\<^sub>I\<close>) and show
  that it is a redundancy criterion.
  And then we consider the case of \textsc{Unsat} inferences separately.
\<close>

definition ARed\<^sub>F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> where
  \<open>ARed\<^sub>F \<N> \<equiv> SRed\<^sub>F \<N>\<close>

definition ARed\<^sub>I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> where
  \<open>ARed\<^sub>I \<N> \<equiv> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and>
                  (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> FRed\<^sub>I (\<N> proj\<^sub>J \<J>)) }\<close>

definition AInf :: \<open>('f, 'v) AF inference set\<close> where
  \<open>AInf \<equiv> { base_inf \<N> D | \<N> D. base_pre \<N> D }\<close>

definition \<G>\<^sub>F :: \<open>'v total_interpretation \<Rightarrow> ('f, 'v) AF \<Rightarrow> 'f set\<close> where
  \<open>\<G>\<^sub>F \<J> \<C> \<equiv> {\<C>} proj\<^sub>J \<J>\<close>

definition \<G>\<^sub>I :: \<open>'v total_interpretation \<Rightarrow> ('f, 'v) AF inference \<Rightarrow> 'f inference set\<close> where
  \<open>\<G>\<^sub>I \<J> \<iota> \<equiv> {\<iota>} \<iota>proj\<^sub>J \<J>\<close>

text \<open>We define a wellfounded ordering on A-formulas to strengthen @{const ARed\<^sub>I}.
  Basically, \<open>A \<leftarrow> \<C> \<sqsupset> A \<leftarrow> \<C>'\<close> if \<open>\<C> \<subset> \<C>'\<close>.\<close> 

definition tiebreaker_order :: \<open>('f, 'v :: countable) AF rel\<close> where
  \<open>tiebreaker_order \<equiv> { (\<C>, \<C>'). F_of \<C> = F_of \<C>' \<and> A_of \<C> |\<subset>| A_of \<C>' }\<close>

abbreviation sqsupset_is_tiebreaker_order (infix \<open>\<sqsupset>\<close> 50) where
  \<open>\<C> \<sqsupset> \<C>' \<equiv> (\<C>, \<C>') \<in> tiebreaker_order\<close>

lemma tiebreaker_order_is_strict_partial_order: \<open>po_on (\<sqsupset>) UNIV\<close>
  unfolding po_on_def irreflp_on_def transp_on_def tiebreaker_order_def
  by auto

lemma wfp_on_fsubset: \<open>wfp_on (|\<subset>|) UNIV\<close>
  using wf_fsubset
  by auto

lemma wfp_on_tiebreaker_order: \<open>wfp_on (\<sqsupset>) (UNIV :: ('f, 'v) AF set)\<close>
  unfolding wfp_on_def
proof (intro notI)
  assume \<open>\<exists> f. \<forall> i. f i \<in> UNIV \<and> f (Suc i) \<sqsupset> f i\<close>
  then obtain f where f_is: \<open>\<forall> i. f i \<in> UNIV \<and> f (Suc i) \<sqsupset> f i\<close>
    by auto
  define f' where \<open>f' = (\<lambda> i. A_of (f i))\<close>

  have \<open>\<forall> i. f' i \<in> UNIV \<and> f' (Suc i) |\<subset>| f' i\<close>
    using f_is
    unfolding f'_def tiebreaker_order_def
    by auto
  then show \<open>False\<close>
    using wfp_on_fsubset
    unfolding wfp_on_def
    by blast
qed

text \<open>We can lift inferences from \<open>FRed\<^sub>I\<close> to \<open>ARed\<^sub>I\<close>.\<close>
interpretation lift_from_FRed_to_ARed: light_tiebreaker_lifting \<open>{to_AF bot}\<close> AInf \<open>{bot}\<close> \<open>(\<Turnstile>\<inter>)\<close>
  FInf FRed\<^sub>I FRed\<^sub>F \<open>\<G>\<^sub>F \<J>\<close> \<open>Some \<circ> \<G>\<^sub>I \<J>\<close> \<open>\<lambda>_. (\<sqsupset>)\<close>
proof (standard)
  fix N
  show \<open>FRed\<^sub>I N \<subseteq> FInf\<close>
    using Red_I_to_Inf
    by presburger
next
  fix B N
  assume \<open>B \<in> {bot}\<close> and
         \<open>N \<Turnstile>\<inter> {B}\<close>
  then show \<open>N - FRed\<^sub>F N \<Turnstile>\<inter> {B}\<close>
    using Red_F_Bot consequence_relation.entails_conjunctive_def consequence_relation_axioms
    by fastforce
next
  fix N N' :: \<open>'f set\<close>
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>FRed\<^sub>F N \<subseteq> FRed\<^sub>F N'\<close>
    using Red_F_of_subset
    by presburger
next
  fix N N' :: \<open>'f set\<close>
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>FRed\<^sub>I N \<subseteq> FRed\<^sub>I N'\<close>
    using Red_I_of_subset
    by presburger
next
  fix N N'
  assume \<open>N' \<subseteq> FRed\<^sub>F N\<close>
  then show \<open>FRed\<^sub>F N \<subseteq> FRed\<^sub>F (N - N')\<close>
    using Red_F_of_Red_F_subset
    by presburger
next
  fix N N'
  assume \<open>N' \<subseteq> FRed\<^sub>F N\<close>
  then show \<open>FRed\<^sub>I N \<subseteq> FRed\<^sub>I (N - N')\<close>
    using Red_I_of_Red_F_subset
    by presburger
next
  fix \<iota> N
  assume \<open>\<iota> \<in> FInf\<close> and
         \<open>concl_of \<iota> \<in> N\<close>
  then show \<open>\<iota> \<in> FRed\<^sub>I N\<close>
    using Red_I_of_Inf_to_N
    by blast
next
  show \<open>{to_AF bot} \<noteq> {}\<close>
    by fast
next
  fix B :: \<open>('f, 'v) AF\<close>
  assume \<open>B \<in> {to_AF bot}\<close>
  then show \<open>\<G>\<^sub>F \<J> B \<noteq> {}\<close>
    by (simp add: \<G>\<^sub>F_def enabled_def enabled_projection_def to_AF_def)
next
  fix B :: \<open>('f, 'v) AF\<close>
  assume \<open>B \<in> {to_AF bot}\<close>
  then show \<open>\<G>\<^sub>F \<J> B \<subseteq> {bot}\<close>
    using \<G>\<^sub>F_def enabled_projection_def
    by (auto simp add: F_of_to_AF) 
next
  fix \<iota>\<^sub>A
  assume \<iota>\<^sub>A_is_ainf: \<open>\<iota>\<^sub>A \<in> AInf\<close> and
         \<open>(Some \<circ> \<G>\<^sub>I \<J>) \<iota>\<^sub>A \<noteq> None\<close>
  have \<open>\<G>\<^sub>I \<J> \<iota>\<^sub>A \<subseteq> FRed\<^sub>I (\<G>\<^sub>F \<J> (concl_of \<iota>\<^sub>A))\<close>
  proof (intro subsetI)
    fix x
    assume x_in_\<G>\<^sub>I_of_\<iota>\<^sub>A: \<open>x \<in> \<G>\<^sub>I \<J> \<iota>\<^sub>A\<close>
    then obtain \<N> D where \<iota>\<^sub>A_is: \<open>\<iota>\<^sub>A = base_inf \<N> D\<close> and
                           infer_\<N>_D_is_inf: \<open>base_pre \<N> D\<close>
      using AInf_def \<iota>\<^sub>A_is_ainf
      by auto
    moreover have \<iota>\<^sub>A_is_enabled: \<open>enabled_inf \<iota>\<^sub>A \<J>\<close> and
                  x_is: \<open>x = \<iota>F_of \<iota>\<^sub>A\<close>
      using \<G>\<^sub>I_def enabled_projection_Inf_def x_in_\<G>\<^sub>I_of_\<iota>\<^sub>A
      by auto
    then have \<open>prems_of \<iota>\<^sub>A = \<N>\<close>
      using \<iota>\<^sub>A_is
      by auto
    then have \<open>fBall (fset_of_list (map A_of \<N>)) (\<lambda> As. fset As \<subseteq> total_strip \<J>)\<close>
      using \<iota>\<^sub>A_is \<iota>\<^sub>A_is_enabled
      unfolding enabled_inf_def enabled_def
      by (simp add: fBall_fset_of_list_iff_Ball_set)
    then have \<open>fset (ffUnion (A_of |`| fset_of_list \<N>)) \<subseteq> total_strip \<J>\<close>
      by (simp add: fset_ffUnion_subset_iff_all_fsets_subset)
    then have \<open>enabled (AF.Pair D (ffUnion (A_of |`| fset_of_list \<N>))) \<J>\<close>
      unfolding enabled_def
      by auto
    then have \<open>{AF.Pair D (ffUnion (fset_of_list (map A_of \<N>)))} proj\<^sub>J \<J> = {D}\<close>
      unfolding enabled_projection_def F_of_def
      using \<iota>\<^sub>A_is_enabled \<iota>\<^sub>A_is
      by auto
    then have \<open>x \<in> FRed\<^sub>I (\<G>\<^sub>F \<J> (Pair D (ffUnion (fset_of_list (map A_of \<N>)))))\<close>
      using x_in_\<G>\<^sub>I_of_\<iota>\<^sub>A \<iota>\<^sub>A_is_enabled x_is infer_\<N>_D_is_inf \<iota>\<^sub>A_is
      unfolding \<G>\<^sub>I_def \<G>\<^sub>F_def \<iota>F_of_def
      by (simp add: Red_I_of_Inf_to_N)
    then show \<open>x \<in> FRed\<^sub>I (\<G>\<^sub>F \<J> (concl_of \<iota>\<^sub>A))\<close>
      by (simp add: \<iota>\<^sub>A_is)
  qed
  then show \<open>the ((Some \<circ> \<G>\<^sub>I \<J>) \<iota>\<^sub>A) \<subseteq> FRed\<^sub>I (\<G>\<^sub>F \<J> (concl_of \<iota>\<^sub>A))\<close>
    by simp
next
  fix g
  show \<open>po_on (\<sqsupset>) UNIV\<close>
    using tiebreaker_order_is_strict_partial_order
    by blast
next
  fix g
  show \<open>wfp_on (\<sqsupset>) UNIV\<close>
    using wfp_on_tiebreaker_order
    by blast
qed

(* It was left as an exercice to check ARed\<^sub>I and FRed\<^sub>I\<^sup>\<inter>\<^sup>\<G> coincide, meaning that the set of 
 * redundant inferences according to ARed\<^sub>I is the same as the intersection of all sets of redundant
 *  inferences according to FRed\<^sub>I\<^sup>\<inter>\<^sup>\<G>. *)
lemma ARed\<^sub>I_is_FRed\<^sub>I: \<open>ARed\<^sub>I \<N> = (\<Inter> J. lift_from_FRed_to_ARed.Red_I_\<G> J \<N>)\<close>
proof (intro subset_antisym subsetI)
  fix \<iota>
  assume \<open>\<iota> \<in> ARed\<^sub>I \<N>\<close>
  then obtain \<M> \<C> where \<iota>_is: \<open>\<iota> = base_inf \<M> \<C>\<close> and
                         Infer_\<M>_\<C>_in_Inf: \<open>base_pre \<M> \<C>\<close> and
                         \<iota>_in_FRed\<^sub>I: \<open>\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> FRed\<^sub>I (\<N> proj\<^sub>J \<J>)\<close>
    using ARed\<^sub>I_def
    by fastforce
  then have \<iota>_is_AInf: \<open>\<iota> \<in> AInf\<close>
    using AInf_def
    by blast
  then have \<open>\<forall> J. {\<iota>} \<iota>proj\<^sub>J J \<subseteq> FRed\<^sub>I (\<Union> (\<G>\<^sub>F J ` \<N>))\<close>
    unfolding \<G>\<^sub>F_def
    using \<iota>_in_FRed\<^sub>I \<iota>_is Union_of_enabled_projection_is_enabled_projection
    by auto
  then have \<open>\<forall> J. \<iota> \<in> lift_from_FRed_to_ARed.Red_I_\<G> J \<N>\<close>
    using \<iota>_is_AInf
    unfolding lift_from_FRed_to_ARed.Red_I_\<G>_def \<G>\<^sub>I_def
    by auto
  then show \<open>\<iota> \<in> (\<Inter> J. lift_from_FRed_to_ARed.Red_I_\<G> J \<N>)\<close>
    by blast
next
  fix \<iota>
  assume \<iota>_in_FRed\<^sub>I_\<G>: \<open>\<iota> \<in> (\<Inter> J. lift_from_FRed_to_ARed.Red_I_\<G> J \<N>)\<close>
  then have \<iota>_is_AInf: \<open>\<iota> \<in> AInf\<close> and
            all_J_\<G>\<^sub>I_subset_FRed\<^sub>I: \<open>\<forall> J. \<G>\<^sub>I J \<iota> \<subseteq> FRed\<^sub>I (\<Union> (\<G>\<^sub>F J ` \<N>))\<close>
    unfolding lift_from_FRed_to_ARed.Red_I_\<G>_def
    by auto
  then obtain \<M> \<C> where \<iota>_is: \<open>\<iota> = base_inf \<M> \<C>\<close> and
                         Infer_\<M>_\<C>_is_Inf: \<open>base_pre \<M> \<C>\<close>
    using AInf_def
    by auto
  then obtain \<iota>\<^sub>F where \<iota>\<^sub>F_is: \<open>\<iota>\<^sub>F = \<iota>F_of \<iota>\<close>
    by auto
  then have \<open>\<exists> \<M> \<C>. \<iota> = base_inf \<M> \<C> \<and> base_pre \<M> \<C> \<and>
               (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> FRed\<^sub>I (\<N> proj\<^sub>J \<J>))\<close>
    using \<iota>_is Infer_\<M>_\<C>_is_Inf all_J_\<G>\<^sub>I_subset_FRed\<^sub>I
    unfolding \<G>\<^sub>I_def \<G>\<^sub>F_def
    using Union_of_enabled_projection_is_enabled_projection
    by fastforce
  then show \<open>\<iota> \<in> ARed\<^sub>I \<N>\<close>
    unfolding ARed\<^sub>I_def
    by auto
qed

(* Check that ARed\<^sub>F and FRed\<^sub>F\<^bsup>\<inter>\<G>,\<sqsupset>\<^esup> coincide *)
lemma ARed\<^sub>F_is_FRed\<^sub>F: \<open>ARed\<^sub>F \<N> = (\<Inter> J. lift_from_FRed_to_ARed.Red_F_\<G> J \<N>)\<close>
proof (intro subset_antisym subsetI)
  fix \<C>
  assume \<C>_in_ARed\<^sub>F: \<open>\<C> \<in> ARed\<^sub>F \<N>\<close>
  then obtain C A where \<C>_is: \<open>\<C> = AF.Pair C A\<close>
    unfolding ARed\<^sub>F_def SRed\<^sub>F_def
    by blast
  consider (a) \<open>\<forall> \<J>. fset A \<subseteq> total_strip \<J> \<longrightarrow> C \<in> FRed\<^sub>F (\<N> proj\<^sub>J \<J>)\<close> |
           (b) \<open>\<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> A_of \<C> |\<subset>| A\<close>
    using \<C>_in_ARed\<^sub>F \<C>_is
    unfolding ARed\<^sub>F_def SRed\<^sub>F_def
    by blast
  then show \<open>\<C> \<in> (\<Inter> J. lift_from_FRed_to_ARed.Red_F_\<G> J \<N>)\<close>
    unfolding lift_from_FRed_to_ARed.Red_F_\<G>_def
  proof (cases)
    case a
    then have \<open>\<forall> J. \<forall> D \<in> \<G>\<^sub>F J \<C>. D \<in> FRed\<^sub>F (\<Union> (\<G>\<^sub>F J ` \<N>))\<close>
      unfolding Red\<^sub>F_strict_def \<G>\<^sub>F_def
      using Union_of_enabled_projection_is_enabled_projection \<C>_is enabled_projection_def
            \<C>_is complete enabled_projection_def
      using enabled_def
      by force
    then have \<open>\<C> \<in> (\<Inter> J. { C. \<forall> D \<in> \<G>\<^sub>F J C. D \<in> FRed\<^sub>F (\<Union> (\<G>\<^sub>F J ` \<N>)) })\<close>
      by blast
    then show \<open>\<C> \<in> (\<Inter> J. { C. \<forall> D \<in> \<G>\<^sub>F J C. D \<in> FRed\<^sub>F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or>
                              (\<exists> E \<in> \<N>. E \<sqsupset> C \<and> D \<in> \<G>\<^sub>F J E) })\<close>
      by blast
  next
    case b
    then have \<open>\<forall> J. \<forall> D \<in> \<G>\<^sub>F J \<C>. \<exists> E \<in> \<N>. E \<sqsupset> \<C> \<and> D \<in> \<G>\<^sub>F J E\<close>
      unfolding \<G>\<^sub>F_def tiebreaker_order_def enabled_projection_def
      using subformula_of_enabled_formula_is_enabled
      (* /!\ Careful, a bit slow (\<sim> 1s) /!\ *)
      by (smt (verit, ccfv_SIG) AF.sel(1) AF.sel(2) \<C>_is case_prodI mem_Collect_eq
           singletonD singletonI)
    then have \<open>\<C> \<in> (\<Inter> J. { C. \<forall> D \<in> \<G>\<^sub>F J C. \<exists> E \<in> \<N>. E \<sqsupset> C \<and> D \<in> \<G>\<^sub>F J E })\<close>
      by blast
    then show \<open>\<C> \<in> (\<Inter> J. { C. \<forall> D \<in> \<G>\<^sub>F J C. D \<in> FRed\<^sub>F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or>
                              (\<exists> E \<in> \<N>. E \<sqsupset> C \<and> D \<in> \<G>\<^sub>F J E) })\<close>
      by blast
  qed
next
  fix \<C>
  assume \<C>_in_FRed\<^sub>F_\<G>: \<open>\<C> \<in> (\<Inter> J. lift_from_FRed_to_ARed.Red_F_\<G> J \<N>)\<close>
  then have \<C>_in_FRed\<^sub>F_\<G>_unfolded:
    \<open>\<forall> J. \<forall> D \<in> \<G>\<^sub>F J \<C>. D \<in> FRed\<^sub>F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> \<C> \<and> D \<in> \<G>\<^sub>F J E)\<close>
    unfolding lift_from_FRed_to_ARed.Red_F_\<G>_def
    by blast
  then have \<C>_in_FRed\<^sub>F_\<G>_if_enabled:
    \<open>\<forall> J. enabled \<C> J \<longrightarrow> F_of \<C> \<in> FRed\<^sub>F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> \<C> \<and> F_of \<C> \<in> \<G>\<^sub>F J E)\<close>
    unfolding \<G>\<^sub>F_def enabled_projection_def
    by auto
  obtain C A where \<C>_is: \<open>\<C> = AF.Pair C A\<close>
    by (meson AF.exhaust_sel)
  then have
    \<open>\<forall> J. fset A \<subseteq> total_strip J \<longrightarrow>
      C \<in> FRed\<^sub>F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> \<C> \<and> C \<in> \<G>\<^sub>F J E)\<close>
    using \<C>_in_FRed\<^sub>F_\<G>_if_enabled
    unfolding enabled_def
    by simp
  then show \<open>\<C> \<in> ARed\<^sub>F \<N>\<close>
    using \<C>_is \<C>_in_FRed\<^sub>F_\<G>_if_enabled
    unfolding ARed\<^sub>F_def SRed\<^sub>F_def \<G>\<^sub>F_def enabled_def tiebreaker_order_def
    using Union_of_enabled_projection_is_enabled_projection
    by auto
qed

(* Check that both \<Turnstile>\<^sub>A\<^sub>F and \<Turnstile>\<^sub>\<G>\<^sup>\<inter> coincide *)
lemma entails_is_entails_\<G>: \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F {\<C>} \<longleftrightarrow> (\<forall> \<J>. lift_from_FRed_to_ARed.entails_\<G> \<J> \<M> {\<C>})\<close>
proof (intro iffI allI)
  fix \<J>
  assume \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F {\<C>}\<close>
  then show \<open>lift_from_FRed_to_ARed.entails_\<G> \<J> \<M> {\<C>}\<close>
    unfolding \<G>\<^sub>F_def AF_entails_def enabled_projection_def enabled_set_def entails_conjunctive_def
    by (simp add: Union_of_singleton_is_setcompr)
next
  assume entails_\<G>_\<M>_\<C>: \<open>\<forall> \<J>. lift_from_FRed_to_ARed.entails_\<G> \<J> \<M> {\<C>}\<close>
  show \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F {\<C>}\<close>
    unfolding \<G>\<^sub>F_def AF_entails_def enabled_set_def
    proof (intro allI impI)
      fix J
      assume \<open>\<forall> \<C> \<in> {\<C>}. enabled \<C> J\<close>
      then show \<open>\<M> proj\<^sub>J J \<Turnstile> F_of ` {\<C>}\<close>
        using entails_\<G>_\<M>_\<C>
        unfolding \<G>\<^sub>F_def enabled_projection_def entails_conjunctive_def
        by (simp add: Union_of_singleton_is_setcompr)
    qed
qed

(* We put here a collection of useful lemmas when deriving facts about SInf, SRed\<^sub>I and SRed\<^sub>F. *)

lemma SRed\<^sub>I_in_SInf: \<open>SRed\<^sub>I N \<subseteq> SInf\<close>
  using SRed\<^sub>I_def SInf.simps
  by force

lemma SRed\<^sub>F_entails_bot: \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<Longrightarrow> N - SRed\<^sub>F N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
proof -
  fix N

  have And_to_Union:
    \<open>\<And> J. N - lift_from_FRed_to_ARed.Red_F_\<G> J N \<subseteq> (\<Union> J. N - lift_from_FRed_to_ARed.Red_F_\<G> J N)\<close>
    by blast

  assume N_entails_bot: \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  have \<open>lift_from_FRed_to_ARed.entails_\<G> J N {to_AF bot} \<Longrightarrow>
         lift_from_FRed_to_ARed.entails_\<G> J (N - lift_from_FRed_to_ARed.Red_F_\<G> J N) {to_AF bot}\<close>
    for J
    using lift_from_FRed_to_ARed.Red_F_Bot_F
    by blast
  then have \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<Longrightarrow> N - ARed\<^sub>F N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  proof -
    assume \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close> and
           \<open>\<And> J. lift_from_FRed_to_ARed.entails_\<G> J N {to_AF bot} \<Longrightarrow>
            lift_from_FRed_to_ARed.entails_\<G> J (N - lift_from_FRed_to_ARed.Red_F_\<G> J N) {to_AF bot}\<close>
    then have FRed\<^sub>F_\<G>_entails_\<G>_bot:
      \<open>lift_from_FRed_to_ARed.entails_\<G> J (N - lift_from_FRed_to_ARed.Red_F_\<G> J N) {to_AF bot}\<close>
      for J
      using entails_is_entails_\<G>
      by blast
    then have
      \<open>lift_from_FRed_to_ARed.entails_\<G> J (\<Union> J. N - lift_from_FRed_to_ARed.Red_F_\<G> J N) {to_AF bot}\<close>
      for J
      using And_to_Union
      by (meson lift_from_FRed_to_ARed.entails_trans lift_from_FRed_to_ARed.subset_entailed)
    then show \<open>N - ARed\<^sub>F N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
      using ARed\<^sub>F_is_FRed\<^sub>F entails_is_entails_\<G>
      by fastforce
  qed
  then show \<open>N - SRed\<^sub>F N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    using ARed\<^sub>F_def N_entails_bot
    by force
qed

lemma SRed\<^sub>F_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> SRed\<^sub>F N \<subseteq> SRed\<^sub>F N'\<close>
proof -
  fix N N' :: \<open>('f, 'v) AF set\<close>
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>SRed\<^sub>F N \<subseteq> SRed\<^sub>F N'\<close>
    unfolding SRed\<^sub>F_def enabled_projection_def
    (* /!\ Takes a bit of time /!\ *)
    by auto
      (smt (verit, best) Collect_mono Red_F_of_subset subset_iff)
qed

lemma SRed\<^sub>I_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> SRed\<^sub>I N \<subseteq> SRed\<^sub>I N'\<close>
proof -
  fix N N' :: \<open>('f, 'v) AF set\<close>
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>SRed\<^sub>I N \<subseteq> SRed\<^sub>I N'\<close>
    unfolding SRed\<^sub>I_def enabled_projection_Inf_def enabled_projection_def enabled_inf_def \<iota>F_of_def
    (* /!\ This is a bit slow (between 5 and 10s), but this works... /!\ *)
    by (auto, (smt (verit, best) Red_I_of_subset mem_Collect_eq subset_iff)+)
qed

lemma SRed\<^sub>F_of_SRed\<^sub>F_subset_F: \<open>N' \<subseteq> SRed\<^sub>F N \<Longrightarrow> SRed\<^sub>F N \<subseteq> SRed\<^sub>F (N - N')\<close>
proof -
  fix N N'
  assume N'_subset_SRed\<^sub>F_N: \<open>N' \<subseteq> SRed\<^sub>F N\<close>
  have \<open>N' \<subseteq> ARed\<^sub>F N \<Longrightarrow> ARed\<^sub>F N \<subseteq> ARed\<^sub>F (N - N')\<close>
    using lift_from_FRed_to_ARed.Red_F_of_Red_F_subset_F
  proof -
    assume N'_subset_ARed\<^sub>F_N: \<open>N' \<subseteq> ARed\<^sub>F N\<close> and
           \<open>(\<And> N' \<J> N. N' \<subseteq> lift_from_FRed_to_ARed.Red_F_\<G> \<J> N \<Longrightarrow>
              lift_from_FRed_to_ARed.Red_F_\<G> \<J> N \<subseteq> lift_from_FRed_to_ARed.Red_F_\<G> \<J> (N - N'))\<close>
    then have \<open>\<And> N' N. N' \<subseteq> (\<Inter> \<J>. lift_from_FRed_to_ARed.Red_F_\<G> \<J> N) \<Longrightarrow>
                  (\<Inter> \<J>. lift_from_FRed_to_ARed.Red_F_\<G> \<J> N) \<subseteq>
                    (\<Inter> \<J>. lift_from_FRed_to_ARed.Red_F_\<G> \<J> (N - N'))\<close>
      by (meson INF_mono' UNIV_I le_INF_iff)
    then show \<open>ARed\<^sub>F N \<subseteq> ARed\<^sub>F (N - N')\<close>
      using ARed\<^sub>F_is_FRed\<^sub>F N'_subset_ARed\<^sub>F_N
      by presburger
  qed
  then show \<open>SRed\<^sub>F N \<subseteq> SRed\<^sub>F (N - N')\<close>
    by (simp add: ARed\<^sub>F_def N'_subset_SRed\<^sub>F_N)
qed

lemma SRed\<^sub>I_of_SRed\<^sub>F_subset_F: \<open>N' \<subseteq> SRed\<^sub>F N \<Longrightarrow> SRed\<^sub>I N \<subseteq> SRed\<^sub>I (N - N')\<close>
proof -
  fix N N'
  assume N'_subset_SRed\<^sub>F_N: \<open>N' \<subseteq> SRed\<^sub>F N\<close>
  have works_for_ARed\<^sub>I: \<open>N' \<subseteq> ARed\<^sub>F N \<Longrightarrow> ARed\<^sub>I N \<subseteq> ARed\<^sub>I (N - N')\<close>
    using lift_from_FRed_to_ARed.Red_I_of_Red_F_subset_F
  proof -
    assume N'_subset_ARed\<^sub>F_N: \<open>N' \<subseteq> ARed\<^sub>F N\<close> and
           \<open>(\<And> N' \<J> N. N' \<subseteq> lift_from_FRed_to_ARed.Red_F_\<G> \<J> N \<Longrightarrow>
               lift_from_FRed_to_ARed.Red_I_\<G> \<J> N \<subseteq> lift_from_FRed_to_ARed.Red_I_\<G> \<J> (N - N'))\<close>
    then have \<open>\<And> N' N. N' \<subseteq> (\<Inter> \<J>. lift_from_FRed_to_ARed.Red_F_\<G> \<J> N) \<Longrightarrow>
                  (\<Inter> \<J>. lift_from_FRed_to_ARed.Red_I_\<G> \<J> N) \<subseteq>
                    (\<Inter> \<J>. lift_from_FRed_to_ARed.Red_I_\<G> \<J> (N - N'))\<close>
      by (metis (no_types, lifting) INF_mono' UNIV_I le_INF_iff)
    then show \<open>ARed\<^sub>I N \<subseteq> ARed\<^sub>I (N - N')\<close>
      using ARed\<^sub>I_is_FRed\<^sub>I ARed\<^sub>F_is_FRed\<^sub>F N'_subset_ARed\<^sub>F_N
      by presburger
  qed
  moreover have \<open>unsat_pre \<N> \<Longrightarrow> unsat_inf \<N> \<in> SRed\<^sub>I (N - N')\<close> 
    if \<iota>_is_redundant: \<open>unsat_inf \<N> \<in> SRed\<^sub>I N\<close>
    for \<N>
    using bot_not_in_sredF_\<N> N'_subset_SRed\<^sub>F_N \<iota>_is_redundant
    unfolding SRed\<^sub>I_def SRed\<^sub>F_def
    (* /!\ Quite slow... /!\ *)
    by (smt (verit, del_insts) ARed\<^sub>F_def ARed\<^sub>I_def Diff_iff N'_subset_SRed\<^sub>F_N Un_iff
         bot_not_in_sredF_\<N> works_for_ARed\<^sub>I mem_Collect_eq subsetD)
  ultimately show \<open>SRed\<^sub>I N \<subseteq> SRed\<^sub>I (N - N')\<close>
    using N'_subset_SRed\<^sub>F_N bot_not_in_sredF_\<N>
    unfolding SRed\<^sub>F_def ARed\<^sub>F_def SRed\<^sub>I_def ARed\<^sub>I_def
    (* /!\ A bit slow /!\ *)
    by (smt (verit, del_insts) Collect_cong Diff_iff N'_subset_SRed\<^sub>F_N Un_iff
         bot_not_in_sredF_\<N> subset_iff)
qed

lemma SRed\<^sub>I_of_SInf_to_N_F: \<open>\<iota>\<^sub>S \<in> SInf \<Longrightarrow> concl_of \<iota>\<^sub>S \<in> N \<Longrightarrow> \<iota>\<^sub>S \<in> SRed\<^sub>I N\<close>
proof -
  fix \<iota>\<^sub>S N
  assume \<open>\<iota>\<^sub>S \<in> SInf\<close> and
         concl_\<iota>\<^sub>S_in_N: \<open>concl_of \<iota>\<^sub>S \<in> N\<close>
  then show \<open>\<iota>\<^sub>S \<in> SRed\<^sub>I N\<close>
    unfolding SRed\<^sub>I_def
  proof (cases \<iota>\<^sub>S rule: SInf.cases)
    case (base \<N> D)
    obtain \<M> \<C> where \<iota>\<^sub>S_is: \<open>\<iota>\<^sub>S = base_inf \<M> \<C>\<close> and
                      Infer_\<M>_\<C>_is_Inf: \<open>base_pre \<M> \<C>\<close>
      using base
      by blast
    have \<open>\<forall> J. { base_inf \<M> \<C> } \<iota>proj\<^sub>J J \<subseteq> FRed\<^sub>I (N proj\<^sub>J J)\<close>
      unfolding enabled_projection_Inf_def enabled_projection_def \<iota>F_of_def enabled_inf_def
    proof (intro allI subsetI, simp)
      fix J
      assume all_enabled_in_\<M>: \<open>\<forall> \<C> \<in> set \<M>. enabled \<C> J\<close>
      then have A_of_\<M>_to_\<C>_in_N: \<open>AF.Pair \<C> (ffUnion (fset_of_list (map A_of \<M>))) \<in> N\<close>
        using \<iota>\<^sub>S_is concl_\<iota>\<^sub>S_in_N
        by auto
      moreover have \<open>fBall (fset_of_list \<M>) (\<lambda> x. fset (A_of x) \<subseteq> total_strip J)\<close>
        using all_enabled_in_\<M>
        unfolding enabled_def
        by (simp add: fset_of_list_elem)
      then have \<open>fBall (A_of |`| fset_of_list \<M>) (\<lambda> x. fset x \<subseteq> total_strip J)\<close>
        by auto
      then have \<open>enabled (AF.Pair \<C> (ffUnion (A_of |`| fset_of_list \<M>))) J\<close>
        using A_of_\<M>_to_\<C>_in_N
        unfolding enabled_def
        using fset_ffUnion_subset_iff_all_fsets_subset
        by (metis AF.sel(2))
      ultimately show \<open>Infer (map F_of \<M>) \<C> \<in> FRed\<^sub>I {F_of \<C> | \<C>. \<C> \<in> N \<and> enabled \<C> J}\<close>
        by (metis (mono_tags, lifting) AF.sel(1) Infer_\<M>_\<C>_is_Inf Red_I_of_Inf_to_N
             fset_of_list_map inference.sel(2) mem_Collect_eq)
    qed
    then have \<open>\<iota>\<^sub>S \<in> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and>
                        (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> FRed\<^sub>I (N proj\<^sub>J \<J>))}\<close>
      using \<iota>\<^sub>S_is Infer_\<M>_\<C>_is_Inf
      by auto
    then show \<open>\<iota>\<^sub>S \<in> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and>
                       (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> FRed\<^sub>I (N proj\<^sub>J \<J>)) } \<union>
                    { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> N }\<close>
      by fast
  next
    case (unsat \<N>)
    then have \<open>\<iota>\<^sub>S \<in> { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> N}\<close>
      using concl_\<iota>\<^sub>S_in_N
      by fastforce
    then show \<open>\<iota>\<^sub>S \<in> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and>
                        (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> FRed\<^sub>I (N proj\<^sub>J \<J>)) } \<union>
                    { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> N }\<close>
      by fast
  qed
qed

end (* locale annotated_calculus *)


subsection \<open>Standard completeness\<close>

context annotated_calculus
begin

(* This is a bundle containing some rules which are mostly used together.
 * Its purpose is simply to reduce the visual clutter from long proofs. *)
lemmas SRed_rules = SRed\<^sub>F_entails_bot SRed\<^sub>F_of_subset_F SRed\<^sub>I_of_subset_F SRed\<^sub>F_of_SRed\<^sub>F_subset_F
                    SRed\<^sub>I_of_SRed\<^sub>F_subset_F SRed\<^sub>I_of_SInf_to_N_F SRed\<^sub>I_in_SInf

(* Report lemma 18 *)
sublocale S_calculus: calculus \<open>to_AF bot\<close> SInf AF_entails SRed\<^sub>I SRed\<^sub>F
  by (standard; simp add: SRed_rules)

(* Report lemma 20 *)
lemma S_saturated_to_F_saturated: \<open>S_calculus.saturated \<N> \<Longrightarrow> saturated (\<N> proj\<^sub>J \<J>)\<close>
proof -
  assume \<N>_is_S_saturated: \<open>S_calculus.saturated \<N>\<close>
  then show \<open>saturated (\<N> proj\<^sub>J \<J>)\<close>
    unfolding saturated_def S_calculus.saturated_def
  proof (intro subsetI)
    fix \<iota>\<^sub>F
    assume \<open>\<iota>\<^sub>F \<in> Inf_from (\<N> proj\<^sub>J \<J>)\<close>
    then have \<iota>\<^sub>F_is_Inf: \<open>\<iota>\<^sub>F \<in> FInf\<close> and
              prems_of_\<iota>\<^sub>F_in_\<N>_proj_\<J>: \<open>set (prems_of \<iota>\<^sub>F) \<subseteq> \<N> proj\<^sub>J \<J>\<close>
      unfolding Inf_from_def
      by auto
    moreover have \<open>\<forall> C \<in> set (prems_of \<iota>\<^sub>F). \<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> enabled \<C> \<J>\<close>
      using prems_of_\<iota>\<^sub>F_in_\<N>_proj_\<J>
      unfolding enabled_projection_def
      by blast
    then have \<open>list_all (\<lambda> C. \<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> enabled \<C> \<J>) (prems_of \<iota>\<^sub>F)\<close>
      using Ball_set
      by blast
    then have \<open>\<exists> \<C>s. length \<C>s = length (prems_of \<iota>\<^sub>F) \<and>
                     list_all2 (\<lambda> C \<C>. \<C> \<in> \<N> \<and> F_of \<C> = C \<and> enabled \<C> \<J>) (prems_of \<iota>\<^sub>F) \<C>s\<close>
      using list_all_ex_to_ex_list_all2
      by (smt (verit, best) Ball_set)
    then have \<open>\<exists> As. length As = length (prems_of \<iota>\<^sub>F) \<and>
                     list_all2 (\<lambda> C A. AF.Pair C A \<in> \<N> \<and> enabled (AF.Pair C A) \<J>) (prems_of \<iota>\<^sub>F) As\<close>
      by (smt (verit, del_insts) AF.exhaust AF.sel(1) list.pred_mono_strong
          list_all_ex_to_ex_list_all2)
    then have \<open>\<exists> As. length As = length (prems_of \<iota>\<^sub>F) \<and>
                     list_all (\<lambda> \<C>. \<C> \<in> \<N> \<and> enabled \<C> \<J>) (map2 AF.Pair (prems_of \<iota>\<^sub>F) As)\<close>
      using list_all2_to_map[where f = \<open>\<lambda> C A. AF.Pair C A\<close>]
      by (smt (verit) list_all2_mono)
    then obtain As :: \<open>'v sign fset list\<close>
                   where \<open>\<forall> \<C> \<in> set (map2 AF.Pair (prems_of \<iota>\<^sub>F) As). \<C> \<in> \<N> \<and> enabled \<C> \<J>\<close> and
                         length_As_eq_length_prems: \<open>length As = length (prems_of \<iota>\<^sub>F)\<close>
      by (metis (no_types, lifting) Ball_set_list_all)
    then have set_prems_As_subset_\<N>: \<open>set (map2 AF.Pair (prems_of \<iota>\<^sub>F) As) \<subseteq> \<N>\<close> and
              all_enabled: \<open>\<forall> \<C> \<in> set (map2 AF.Pair (prems_of \<iota>\<^sub>F) As). enabled \<C> \<J>\<close>
      by auto

    let ?prems = \<open>map2 AF.Pair (prems_of \<iota>\<^sub>F) As\<close>

    have \<open>set ?prems \<subseteq> \<N>\<close>
      using set_prems_As_subset_\<N> .
    moreover have \<open>length ?prems = length (prems_of \<iota>\<^sub>F)\<close>
      using length_As_eq_length_prems
      by simp
    then have F_of_dummy_prems_is_prems_of_\<iota>\<^sub>F: \<open>map F_of ?prems = prems_of \<iota>\<^sub>F\<close>
      by (simp add: length_As_eq_length_prems)
    moreover have \<open>\<forall> \<C> \<in> set (map A_of (map2 AF.Pair (prems_of \<iota>\<^sub>F) As)). fset \<C> \<subseteq> total_strip \<J>\<close>
      using
        all_enabled ball_set_f_to_ball_set_map[where P = \<open>\<lambda> x. fset x \<subseteq> total_strip \<J>\<close> and f = A_of]
      unfolding enabled_def
      by blast
    then have \<open>\<forall> \<C> \<in> set As. fset \<C> \<subseteq> total_strip \<J>\<close>
      using map_A_of_map2_Pair length_As_eq_length_prems
      by metis
    then have \<open>fset (ffUnion (fset_of_list As)) \<subseteq> total_strip \<J>\<close>
      using all_enabled
      unfolding enabled_def[of _ \<J>]
      by (simp add: fBall_fset_of_list_iff_Ball_set fset_ffUnion_subset_iff_all_fsets_subset)
    then have base_inf_enabled: \<open>enabled_inf (base_inf ?prems (concl_of \<iota>\<^sub>F)) \<J>\<close>
      using all_enabled enabled_inf_def
      by auto
    moreover have pre_holds: \<open>base_pre ?prems (concl_of \<iota>\<^sub>F)\<close>
      using \<iota>\<^sub>F_is_Inf F_of_dummy_prems_is_prems_of_\<iota>\<^sub>F
      by force
    moreover have \<iota>F_of_base_inf_is_\<iota>\<^sub>F: \<open>\<iota>F_of (base_inf ?prems (concl_of \<iota>\<^sub>F)) = \<iota>\<^sub>F\<close>
      using F_of_dummy_prems_is_prems_of_\<iota>\<^sub>F \<iota>F_of_def
      by force
    ultimately have \<iota>\<^sub>F_in_Inf_\<N>_proj_\<J>: \<open>\<iota>\<^sub>F \<in> (S_calculus.Inf_from \<N>) \<iota>proj\<^sub>J \<J>\<close>
      using SInf.base[OF pre_holds]
      unfolding enabled_projection_Inf_def S_calculus.Inf_from_def
      by (metis (mono_tags, lifting) inference.sel(1) mem_Collect_eq)
    then have \<open>\<exists> \<M> D. base_inf \<M> D \<in> S_calculus.Inf_from \<N> \<and>
                \<iota>F_of (base_inf \<M> D) = \<iota>\<^sub>F \<and> enabled_inf (base_inf \<M> D) \<J>\<close>
      using \<iota>F_of_base_inf_is_\<iota>\<^sub>F
      unfolding enabled_projection_Inf_def
      by (metis (mono_tags, lifting) CollectI S_calculus.Inf_from_def SInf.base
          base_inf_enabled inference.sel(1) pre_holds set_prems_As_subset_\<N>)
    then obtain \<M> D where base_inf_in_Inf_\<N>: \<open>base_inf \<M> D \<in> S_calculus.Inf_from \<N>\<close> and
                           \<iota>F_of_base_inf_is_\<iota>\<^sub>F: \<open>\<iota>F_of (base_inf \<M> D) = \<iota>\<^sub>F\<close> and
                           base_inf_enabled: \<open>enabled_inf (base_inf \<M> D) \<J>\<close>
      by blast
    then have \<open>base_inf \<M> D \<in> SRed\<^sub>I \<N>\<close>
      using \<N>_is_S_saturated
      unfolding S_calculus.saturated_def
      by blast
    moreover have \<open>base_pre \<M> D\<close>
      using \<iota>F_of_base_inf_is_\<iota>\<^sub>F \<iota>\<^sub>F_is_Inf
      by (simp add: \<iota>F_of_def)
    ultimately show \<open>\<iota>\<^sub>F \<in> FRed\<^sub>I (\<N> proj\<^sub>J \<J>)\<close>
      using \<iota>\<^sub>F_in_Inf_\<N>_proj_\<J> \<iota>F_of_base_inf_is_\<iota>\<^sub>F base_inf_enabled
      unfolding SRed\<^sub>I_def enabled_projection_Inf_def \<iota>F_of_def enabled_def enabled_projection_def
      by auto
         (metis (mono_tags, lifting) AF.sel(2) F_of_to_AF Red_I_of_Inf_to_N bot_fset.rep_eq
          empty_subsetI inference.sel(2) mem_Collect_eq to_AF_def)
  qed
qed

(* This is easier to type than \<open>AF_cons_rel.entails_conjunctive\<close>, and looks more beautiful. *)
notation AF_cons_rel.entails_conjunctive (infix \<open>\<Turnstile>\<inter>\<^sub>A\<^sub>F\<close> 50)

(* Report theorem 21 *)
theorem S_calculus_statically_complete:
  assumes F_statically_complete: \<open>statically_complete_calculus bot FInf (\<Turnstile>) FRed\<^sub>I FRed\<^sub>F\<close>
  shows \<open>statically_complete_calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
  using F_statically_complete
  unfolding statically_complete_calculus_def statically_complete_calculus_axioms_def
proof (intro conjI allI impI; elim conjE)
  show \<open>calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
    using S_calculus.calculus_axioms
    by force
next
  fix N
  assume \<open>calculus bot FInf (\<Turnstile>) FRed\<^sub>I FRed\<^sub>F\<close> and
         if_F_saturated_and_N_entails_bot_then_bot_in_N:
           \<open>\<forall> N. saturated N \<longrightarrow> N \<Turnstile> {bot} \<longrightarrow> bot \<in> N\<close> and
         N_is_S_saturated: \<open>S_calculus.saturated N\<close> and
         N_entails_bot: \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  then have N_proj_\<J>_entails_bot: \<open>\<forall> \<J>. N proj\<^sub>J \<J> \<Turnstile> {bot}\<close>
    unfolding AF_entails_def
    using F_of_to_AF[of bot]
    by (smt (verit) enabled_to_AF_set image_empty image_insert)
  then have N_proj_\<J>_F_saturated: \<open>\<forall> \<J>. saturated (N proj\<^sub>J \<J>)\<close>
    using N_is_S_saturated
    using S_saturated_to_F_saturated
    by blast
  then have \<open>\<forall> \<J>. bot \<in> N proj\<^sub>J \<J>\<close>
    using N_proj_\<J>_entails_bot if_F_saturated_and_N_entails_bot_then_bot_in_N
    by presburger
  then have prop_proj_N_is_prop_unsat: \<open>propositionally_unsatisfiable (proj\<^sub>\<bottom> N)\<close>
    unfolding enabled_projection_def propositional_model_def propositional_projection_def
      propositionally_unsatisfiable_def
    by fast
  then have \<open>proj\<^sub>\<bottom> N \<noteq> {}\<close>
    unfolding propositionally_unsatisfiable_def propositional_model_def
    using enabled_projection_def prop_proj_in
    by auto
  then have \<open>\<exists> \<M>. set \<M> \<subseteq> proj\<^sub>\<bottom> N \<and> finite (set \<M>) \<and> propositionally_unsatisfiable (set \<M>)\<close>
    by (metis finite_list prop_proj_N_is_prop_unsat prop_unsat_compactness)
  then obtain \<M> where \<M>_subset_prop_proj_N: \<open>set \<M> \<subseteq> proj\<^sub>\<bottom> N\<close> and
                       \<M>_subset_N: \<open>set \<M> \<subseteq> N\<close> and
                       \<open>finite (set \<M>)\<close> and
                       \<M>_prop_unsat: \<open>propositionally_unsatisfiable (set \<M>)\<close> and
                       \<M>_not_empty: \<open>\<M> \<noteq> []\<close>
    by (smt (verit, del_insts) AF_cons_rel.entails_bot_to_entails_empty
        AF_cons_rel.entails_empty_reflexive_dangerous compactness_AF_proj equiv_prop_entails
        finite_list image_empty prop_proj_N_is_prop_unsat prop_proj_in propositional_model2_def
        propositionally_unsatisfiable_def set_empty2 subset_empty subset_trans to_AF_proj_J)
  then have \<open>unsat_inf \<M> \<in> S_calculus.Inf_from N\<close> and
            Infer_\<M>_bot_in_SInf: \<open>unsat_inf \<M> \<in> SInf\<close>
    using SInf.unsat S_calculus.Inf_from_def propositional_projection_def
    by fastforce+ 
  then have \<open>unsat_inf \<M> \<in> SRed\<^sub>I N\<close>
    using N_is_S_saturated S_calculus.saturated_def
    by blast
  then show \<open>to_AF bot \<in> N\<close>
    unfolding SRed\<^sub>I_def
  proof (elim UnE)
    assume \<open>unsat_inf \<M> \<in> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and>
      (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> FRed\<^sub>I (N proj\<^sub>J \<J>)) }\<close>
    then have \<open>unsat_inf \<M> = base_inf \<M> bot\<close>
      by (smt (verit, best) AF.exhaust_sel AF.sel(2) F_of_to_AF inference.inject mem_Collect_eq)
    then have \<open>to_AF bot = AF.Pair bot (ffUnion (A_of |`| fset_of_list \<M>))\<close>
      by simp
    then have \<open>ffUnion (A_of |`| fset_of_list \<M>) = {||}\<close>
      by (metis AF.sel(2) A_of_to_AF)
    then consider (\<M>_empty) \<open>A_of |`| fset_of_list \<M> = {||}\<close> |
                  (no_assertions_in_\<M>) \<open>fBall (A_of |`| fset_of_list \<M>) (\<lambda> x. x = {||})\<close>
      using Union_empty_if_set_empty_or_all_empty
      by auto
    then show ?thesis
    proof (cases)
      case \<M>_empty
      then have \<open>fset_of_list \<M> = {||}\<close>
        by blast
      then have \<open>\<M> = []\<close>
        by (metis bot_fset.rep_eq fset_of_list.rep_eq set_empty2)
      then show ?thesis
        using \<M>_not_empty
        by contradiction
    next
      case no_assertions_in_\<M>
      then have \<open>fBall (fset_of_list \<M>) (\<lambda> x. A_of x = {||})\<close>
        using fBall_fimage_is_fBall
        by simp
      then have \<open>\<forall> x \<in> set \<M>. A_of x = {||}\<close>
        using fBall_fset_of_list_iff_Ball_set
        by fast
      then have \<open>to_AF bot \<in> set \<M>\<close>
        using \<M>_subset_prop_proj_N \<M>_not_empty
        unfolding propositional_projection_def to_AF_def
        by (metis (mono_tags, lifting) AF.exhaust_sel CollectD ex_in_conv set_empty subset_code(1))
      then show ?thesis
        using \<M>_subset_N
        by blast
    qed
  next
    assume \<open>unsat_inf \<M> \<in> { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> N }\<close>
    then show ?thesis
      by fastforce
  qed
qed


(*<*)
lemma entails_conj_is_entails_disj_if_right_singleton: \<open>\<M> \<Turnstile>\<inter>\<^sub>A\<^sub>F {\<C>} \<longleftrightarrow> \<M> \<Turnstile>\<^sub>A\<^sub>F {\<C>}\<close>
  unfolding AF_cons_rel.entails_conjunctive_def
  by blast

lemma S_with_conj_is_calculus: \<open>Calculus.calculus {to_AF bot} SInf (\<Turnstile>\<inter>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
proof (standard; (simp only: SRed_rules)?)
  fix N B
  show \<open>B \<in> {to_AF bot} \<Longrightarrow> N \<Turnstile>\<inter>\<^sub>A\<^sub>F {B} \<Longrightarrow> N - SRed\<^sub>F N \<Turnstile>\<inter>\<^sub>A\<^sub>F {B}\<close>
    by (simp add: AF_cons_rel.entails_conjunctive_def SRed\<^sub>F_entails_bot)
qed

lemma saturated_equiv: \<open>S_calculus.saturated N \<longleftrightarrow> Calculus.calculus.saturated SInf SRed\<^sub>I N\<close>
  by (meson Calculus.calculus.saturated_def S_calculus.saturated_def S_with_conj_is_calculus)

lemma derivation_equiv:
  \<open>is_derivation S_calculus.derive Ns \<longleftrightarrow> chain (Calculus.calculus.derive SRed\<^sub>F) (to_llist Ns)\<close>
proof -
  have \<open>S_calculus.derive M N \<longleftrightarrow> Calculus.calculus.derive SRed\<^sub>F M N\<close> for M N
    unfolding S_calculus.derive_def
  proof (intro iffI)
    show \<open>M - N \<subseteq> SRed\<^sub>F N \<Longrightarrow> Calculus.calculus.derive SRed\<^sub>F M N\<close>
      using S_with_conj_is_calculus calculus.derive.intros
      by blast
  next
    assume \<open>Calculus.calculus.derive SRed\<^sub>F M N\<close>
    then have \<open>M - N \<subseteq> SRed\<^sub>F N\<close>
      by (meson S_with_conj_is_calculus calculus.derive.cases)
    then show \<open>M - N \<subseteq> SRed\<^sub>F N\<close> .
  qed
  moreover have \<open>(\<forall> i. R (llnth M i) (llnth M (Suc i))) \<longleftrightarrow> chain R (to_llist M)\<close> for R M
  proof (intro iffI)
    assume all_of_M_in_rel: \<open>\<forall> i. R (llnth M i) (llnth M (Suc i))\<close>
    then show \<open>chain R (to_llist M)\<close>
    proof -
      have \<open>\<not> lnull (to_llist M)\<close>
        by (metis enat.simps(3) llength_eq_0 llength_of_to_llist_is_infinite zero_enat_def)
      moreover have \<open>\<forall> j. enat (j + 1) < \<infinity> \<longrightarrow> R (llnth M j) (llnth M (Suc j))\<close>
        using all_of_M_in_rel
        by blast
      then have \<open>\<forall> j. enat (j + 1) < \<infinity> \<longrightarrow> R (lnth (to_llist M) j) (lnth (to_llist M) (Suc j))\<close>
        by (simp add: llnth.rep_eq)
      ultimately show \<open>chain R (to_llist M)\<close>
        by (metis Suc_eq_plus1 all_of_M_in_rel llnth.rep_eq lnth_rel_chain)
    qed
  next
    assume chain_R_M: \<open>chain R (to_llist M)\<close>
    then show \<open>\<forall> i. R (llnth M i) (llnth M (Suc i))\<close>
    proof (intro allI)
      fix i
      have \<open>enat i < \<infinity>\<close>
        using enat_ord_code(4)
        by presburger
      then have \<open>R (lnth (to_llist M) i) (lnth (to_llist M) (Suc i))\<close>
        by (simp add: chain_R_M chain_lnth_rel llength_of_to_llist_is_infinite)
      then show \<open>R (llnth M i) (llnth M (Suc i))\<close>
        by (simp add: llnth.rep_eq)
    qed
  qed
  ultimately have
    \<open>(\<forall> i. S_calculus.derive (llnth Ns i) (llnth Ns (Suc i))) \<longleftrightarrow>
     chain (Calculus.calculus.derive SRed\<^sub>F) (to_llist Ns)\<close>
    by metis
  then show ?thesis
    by (simp add: is_derivation_def)
qed

lemma fair_equiv: \<open>S_calculus.fair Ns \<longleftrightarrow> Calculus.calculus.fair SInf SRed\<^sub>I (to_llist Ns)\<close>
proof -
  have \<open>S_calculus.Inf_from (Liminf_llist (to_llist Ns)) \<subseteq> Sup_llist (lmap SRed\<^sub>I (to_llist Ns)) \<longleftrightarrow>
        S_calculus.Inf_from (Liminf_infinite_llist Ns) \<subseteq> Sup_infinite_llist (llmap SRed\<^sub>I Ns)\<close>
    by transfer meson
  then show ?thesis
    using S_calculus.weakly_fair_def S_with_conj_is_calculus calculus.fair_def
    by blast
qed
(*>*)



text \<open>
  The following proof works as follows.

  We assume that \<open>(Inf, (Red\<^sub>I, Red\<^sub>F))\<close>.
  From that and theorem @{thm S_calculus_statically_complete}, we obtain that
    \<open>(SInf, (SRed\<^sub>I, SRed\<^sub>F))\<close> is statically complete.
  This means that for all \<open>\<N> \<subseteq> UNIV\<close>, if \<open>\<N>\<close> is saturated w.r.t. \<open>(SInf, SRed\<^sub>I)\<close>
    and \<open>\<N> \<Turnstile>\<union>\<^sub>A\<^sub>F {\<bottom>}\<close> then \<open>\<bottom> \<in> \<N>\<close>.
  Since \<open>\<Turnstile>\<union>\<^sub>A\<^sub>F \<equiv> \<Turnstile>\<inter>\<^sub>A\<^sub>F\<close> when the right hand side is a singleton set, we have that
    for all \<open>\<N> \<subseteq> UNIV\<close>, if \<open>\<N>\<close> is saturated w.r.t. \<open>(SInf, SRed\<^sub>I)\<close> and \<open>\<N> \<Turnstile>\<inter>\<^sub>A\<^sub>F {\<bottom>}\<close> then \<open>\<bottom> \<in> \<N>\<close>.

  Because \<open>\<Turnstile>\<inter>\<^sub>A\<^sub>F\<close> is a consequence relation for the Saturation Framework, we can derive
      that \<open>(SInf, (SRed\<^sub>I, SRed\<^sub>F))\<close> is dynamically complete (using the conjunctive entailment).
  We then proceed as above but in the opposite way to show that \<open>(SInf, (SRed\<^sub>I, SRed\<^sub>F))\<close>
      is dynamically complete using the disjunctive entailment \<open>\<Turnstile>\<union>\<^sub>A\<^sub>F\<close>.
\<close>

(* Report corollary 22 *)
corollary S_calculus_dynamically_complete:
  assumes F_statically_complete: \<open>statically_complete_calculus bot FInf (\<Turnstile>) FRed\<^sub>I FRed\<^sub>F\<close>
  shows \<open>dynamically_complete_calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
proof -
  have \<open>statically_complete_calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
    using S_calculus_statically_complete F_statically_complete
    by blast
  then have \<open>statically_complete_calculus_axioms (to_AF bot) SInf (\<Turnstile>\<inter>\<^sub>A\<^sub>F) SRed\<^sub>I\<close>
    using entails_conj_is_entails_disj_if_right_singleton[where ?\<C> = \<open>to_AF bot\<close>]
    unfolding statically_complete_calculus_def statically_complete_calculus_axioms_def
    by blast
  then have \<open>Calculus.statically_complete_calculus_axioms {to_AF bot} SInf (\<Turnstile>\<inter>\<^sub>A\<^sub>F) SRed\<^sub>I\<close>
    unfolding statically_complete_calculus_axioms_def
      Calculus.statically_complete_calculus_axioms_def
    using saturated_equiv
    by blast
  then have \<open>Calculus.statically_complete_calculus {to_AF bot} SInf (\<Turnstile>\<inter>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
    using Calculus.statically_complete_calculus.intro S_with_conj_is_calculus
    by blast
  then have \<open>Calculus.dynamically_complete_calculus {to_AF bot} SInf (\<Turnstile>\<inter>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
    using S_with_conj_is_calculus calculus.dyn_equiv_stat
    by blast
  then have \<open>Calculus.dynamically_complete_calculus_axioms {to_AF bot} SInf (\<Turnstile>\<inter>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
    using Calculus.dynamically_complete_calculus_def
    by blast
  then have \<open>dynamically_complete_calculus_axioms (to_AF bot) SInf (\<Turnstile>\<inter>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
    unfolding dynamically_complete_calculus_axioms_def
      Calculus.dynamically_complete_calculus_axioms_def
    by (metis derivation_equiv fair_equiv llhd.rep_eq llnth.rep_eq singletonD singletonI)
  then have \<open>dynamically_complete_calculus_axioms (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
    unfolding dynamically_complete_calculus_axioms_def
    using entails_conj_is_entails_disj_if_right_singleton
    by presburger
  then show \<open>dynamically_complete_calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
    by (simp add: dynamically_complete_calculus_def
        S_calculus.calculus_axioms)
qed





subsection \<open>Strong completeness\<close>

(* Report theorem 24 *)
theorem S_calculus_strong_statically_complete:
  assumes F_statically_complete: \<open>statically_complete_calculus bot FInf (\<Turnstile>) FRed\<^sub>I FRed\<^sub>F\<close> and
          \<N>_locally_saturated: \<open>locally_saturated \<N>\<close> and
          \<N>_entails_bot: \<open>\<N> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  shows \<open>to_AF bot \<in> \<N>\<close>
  using \<N>_locally_saturated
  unfolding locally_saturated_def
proof (elim disjE)
  show \<open>to_AF bot \<in> \<N> \<Longrightarrow> to_AF bot \<in> \<N>\<close>
    by blast
next
  assume \<open>\<exists> J. J \<Turnstile>\<^sub>p \<N> \<and> saturated (\<N> proj\<^sub>J J)\<close>
  then obtain J where J_prop_model_of_\<N>: \<open>J \<Turnstile>\<^sub>p \<N>\<close> and
                      \<N>_proj_J_saturated: \<open>saturated (\<N> proj\<^sub>J J)\<close>
    by blast
  then have \<open>\<N> proj\<^sub>J J \<Turnstile> {bot}\<close>
    using \<N>_entails_bot AF_entails_def enabled_to_AF_set
    by (metis (no_types, lifting) f_of_to_AF image_insert image_is_empty) 
  then have \<open>bot \<in> \<N> proj\<^sub>J J\<close>
    using \<N>_proj_J_saturated F_statically_complete
    by (simp add: statically_complete_calculus.statically_complete)
  then show \<open>to_AF bot \<in> \<N>\<close>
    using J_prop_model_of_\<N>
    using enabled_projection_def propositional_model_def propositional_projection_def
    by force
qed

(*<*)
lemma SRed_of_lim_inf:
  \<open>SRed\<^sub>F (lim_inf \<N>i) proj\<^sub>J J \<subseteq> FRed\<^sub>F (lim_inf \<N>i proj\<^sub>J J) \<union> (lim_inf \<N>i proj\<^sub>J J)\<close>
proof (intro subsetI)
  fix f
  assume \<open>f \<in> SRed\<^sub>F (lim_inf \<N>i) proj\<^sub>J J\<close>
  then show \<open>f \<in> FRed\<^sub>F (lim_inf \<N>i proj\<^sub>J J) \<union> (lim_inf \<N>i proj\<^sub>J J)\<close>
    unfolding SRed\<^sub>F_def enabled_projection_def enabled_def
    using less_eq_fset.rep_eq
    by (auto, fastforce)
qed

lemma bot_at_i_implies_bot_at_liminf:
  \<open>is_derivation S_calculus.derive \<N>i \<Longrightarrow> to_AF bot \<in> llnth \<N>i i \<Longrightarrow> to_AF bot \<in> lim_inf \<N>i\<close>
proof -
  assume \<N>i_is_derivation: \<open>is_derivation S_calculus.derive \<N>i\<close> and
         bot_at_i: \<open>to_AF bot \<in> llnth \<N>i i\<close>
  then have \<open>\<forall> i. llnth \<N>i i - llnth \<N>i (Suc i) \<subseteq> SRed\<^sub>F (llnth \<N>i (Suc i))\<close>
    unfolding is_derivation_def S_calculus.derive_def
    by blast
  then show ?thesis
    using bot_at_i
  proof (transfer fixing: bot i FRed\<^sub>F)
    fix \<N>i'
    assume llength_is_infinity: \<open>llength \<N>i' = \<infinity>\<close> and
           bot_at_i: \<open>to_AF bot \<in> lnth \<N>i' i\<close> and
           all_at_i_minus_next_i_are_redundant:
             \<open>\<forall> i. lnth \<N>i' i - lnth \<N>i' (Suc i) \<subseteq> SRed\<^sub>F (lnth \<N>i' (Suc i))\<close>
    then have \<open>to_AF bot \<in> lnth \<N>i' (Suc i)\<close>
      using bot_not_in_sredF_\<N>
      by auto
    then have \<open>\<forall> j \<ge> i. to_AF bot \<in> lnth \<N>i' j\<close>
    proof (intro allI impI)
      fix j
      assume \<open>i \<le> j\<close>
      then show \<open>to_AF bot \<in> lnth \<N>i' j\<close>
      proof (induct j rule: full_nat_induct)
        case less: (1 n)
        show ?case
        proof (cases \<open>i = n\<close>)
          case True
          then show ?thesis
            using bot_at_i
            by force
        next
          case False
          then have i_less_than_n: \<open>i < n\<close>
            using le_eq_less_or_eq less.prems
            by presburger
          then have n_positive: \<open>n > 0\<close>
            by force
          then have \<open>to_AF bot \<in> lnth \<N>i' (n - 1)\<close>
            using i_less_than_n less.hyps
            by fastforce
          then show ?thesis
            using all_at_i_minus_next_i_are_redundant[rule_format, of \<open>n - 1\<close>]
                  bot_not_in_sredF_\<N> n_positive
            by auto
        qed
      qed
    qed
    then have \<open>\<exists> i. \<forall> j \<ge> i. to_AF bot \<in> lnth \<N>i' j\<close>
      by blast
    then show \<open>to_AF bot \<in> Liminf_llist \<N>i'\<close>
      using llength_is_infinity
      unfolding Liminf_llist_def
      by auto
  qed
qed

lemma Red_I_of_inf_FRed\<^sub>F_subset_Red_I_of_inf:
  \<open>FRed\<^sub>I ((lim_inf \<N>i proj\<^sub>J J) \<union> FRed\<^sub>F (lim_inf \<N>i proj\<^sub>J J)) = FRed\<^sub>I (lim_inf \<N>i proj\<^sub>J J)\<close>
proof (intro subset_antisym)
  have \<open>FRed\<^sub>F (lim_inf \<N>i proj\<^sub>J J) \<subseteq> FRed\<^sub>F ((lim_inf \<N>i proj\<^sub>J J) \<union> FRed\<^sub>F (lim_inf \<N>i proj\<^sub>J J))\<close>
    by (simp add: Red_F_of_subset)
  then show \<open>FRed\<^sub>I ((lim_inf \<N>i proj\<^sub>J J) \<union> FRed\<^sub>F (lim_inf \<N>i proj\<^sub>J J)) \<subseteq> FRed\<^sub>I (lim_inf \<N>i proj\<^sub>J J)\<close>
    by (smt (verit, del_insts) DiffE Red_I_of_Red_F_subset Red_I_of_subset Un_iff subset_iff) 
next
  show \<open>FRed\<^sub>I (lim_inf \<N>i proj\<^sub>J J) \<subseteq> FRed\<^sub>I ((lim_inf \<N>i proj\<^sub>J J) \<union> FRed\<^sub>F (lim_inf \<N>i proj\<^sub>J J))\<close>
    by (simp add: Red_I_of_subset)
qed
(*>*)



(* Report lemma 27 *)
lemma locally_fair_derivation_is_saturated_at_liminf:
  \<open>is_derivation S_calculus.derive \<N>i \<Longrightarrow> locally_fair \<N>i \<Longrightarrow> locally_saturated (lim_inf \<N>i)\<close>
proof -
  assume \<N>i_is_derivation: \<open>is_derivation S_calculus.derive \<N>i\<close> and
         \<open>locally_fair \<N>i\<close>
  then show \<open>locally_saturated (lim_inf \<N>i)\<close>
    unfolding locally_fair_def
  proof (elim disjE)
    assume \<open>\<exists> i. to_AF bot \<in> llnth \<N>i i\<close>
    then obtain i where \<open>to_AF bot \<in> llnth \<N>i i\<close>
      by blast
    then have \<open>to_AF bot \<in> lim_inf \<N>i\<close>
      using bot_at_i_implies_bot_at_liminf[OF \<N>i_is_derivation]
      by blast
    then show ?thesis
      unfolding locally_saturated_def
      by blast
  next
    assume \<open>\<exists> J. J \<Turnstile>\<^sub>p limit \<N>i \<and> Inf_from (limit \<N>i proj\<^sub>J J) \<subseteq> (\<Union> i. FRed\<^sub>I (llnth \<N>i i proj\<^sub>J J))\<close>
    then obtain J where J_prop_model_of_limit: \<open>J \<Turnstile>\<^sub>p limit \<N>i\<close> and
                        all_inf_of_limit_are_redundant:
                          \<open>Inf_from (limit \<N>i proj\<^sub>J J) \<subseteq> (\<Union> i. FRed\<^sub>I (llnth \<N>i i proj\<^sub>J J))\<close>
      by blast
    then have \<open>\<forall> i. llnth \<N>i i \<subseteq> lim_inf \<N>i \<union> SRed\<^sub>F (lim_inf \<N>i)\<close>
      using Calculus.calculus.i_in_Liminf_or_Red_F[OF S_with_conj_is_calculus, of \<open>to_llist \<N>i\<close>]
            derivation_equiv[of \<open>\<N>i\<close>]
      by (simp add: Liminf_infinite_llist.rep_eq \<N>i_is_derivation llength_of_to_llist_is_infinite
          llnth.rep_eq sup_commute)
    then have \<open>\<forall> i. llnth \<N>i i proj\<^sub>J J \<subseteq> (lim_inf \<N>i proj\<^sub>J J) \<union> FRed\<^sub>F (lim_inf \<N>i proj\<^sub>J J)\<close>
      by (smt (verit, best) SRed_of_lim_inf UN_iff UnE UnI1 Un_commute
          Union_of_enabled_projection_is_enabled_projection subset_iff)
    then have FRed\<^sub>I_in_Red_I_of_FRed\<^sub>F:
      \<open>(\<Union> i. FRed\<^sub>I (llnth \<N>i i proj\<^sub>J J)) \<subseteq>
        (\<Union> i. FRed\<^sub>I ((lim_inf \<N>i proj\<^sub>J J) \<union> FRed\<^sub>F (lim_inf \<N>i proj\<^sub>J J)))\<close>
      by (meson Red_I_of_subset SUP_mono UNIV_I)
    then have \<open>(\<Union> i. FRed\<^sub>I (llnth \<N>i i proj\<^sub>J J)) \<subseteq> (\<Union> i. FRed\<^sub>I (lim_inf \<N>i proj\<^sub>J J))\<close>
      using Red_I_of_inf_FRed\<^sub>F_subset_Red_I_of_inf
      by auto
    then show ?thesis
      unfolding locally_saturated_def
      using J_prop_model_of_limit all_inf_of_limit_are_redundant saturated_def
      by force
  qed
qed

(*<*)
lemma llhd_is_llnth_0: \<open>llhd S = llnth S 0\<close>
  by (transfer, metis infinity_ne_i0 llength_lnull lnth_0_conv_lhd)
(*>*)



(* Report theorem 28 (proof 1) *)
theorem S_calculus_strong_dynamically_complete:
  assumes F_statically_complete: \<open>statically_complete_calculus bot FInf (\<Turnstile>) FRed\<^sub>I FRed\<^sub>F\<close> and
          \<N>i_is_derivation: \<open>is_derivation S_calculus.derive \<N>i\<close> and
          \<N>i_is_locally_fair: \<open>locally_fair \<N>i\<close> and
          \<N>i0_entails_bot: \<open>llhd \<N>i \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  shows \<open>\<exists> i. to_AF bot \<in> llnth \<N>i i\<close>
proof -
  have \<open>llhd \<N>i \<subseteq> (\<Union> i. llnth \<N>i i)\<close>
    by (simp add: SUP_upper llhd_is_llnth_0)
  then have \<open>(\<Union> i. llnth \<N>i i) \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    using \<N>i0_entails_bot
    by (meson AF_cons_rel.entails_trans AF_cons_rel.subset_entailed
        entails_conj_is_entails_disj_if_right_singleton)
  then have \<open>(\<Union> i. llnth \<N>i i) - SRed\<^sub>F (\<Union> i. llnth \<N>i i) \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    using SRed\<^sub>F_entails_bot
    by blast
  moreover have \<open>chain (Calculus.calculus.derive SRed\<^sub>F) (to_llist \<N>i)\<close>
    using derivation_equiv[of \<open>\<N>i\<close>] \<N>i_is_derivation
    by blast
  then have \<open>Sup_llist (to_llist \<N>i) - Liminf_llist (to_llist \<N>i) \<subseteq> SRed\<^sub>F (Sup_llist (to_llist \<N>i))\<close>
    using Calculus.calculus.Red_in_Sup[OF S_with_conj_is_calculus]
    by blast
  then have \<open>(\<Union> i. llnth \<N>i i) - SRed\<^sub>F (\<Union> i. llnth \<N>i i) \<subseteq> lim_inf \<N>i\<close>
    by (transfer fixing: FRed\<^sub>F, unfold Sup_llist_def Liminf_llist_def, auto)
  ultimately have \<N>i_inf_entails_bot: \<open>lim_inf \<N>i \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    by (meson AF_cons_rel.entails_subsets subset_iff)
  then have \<N>i_inf_locally_saturated: \<open>locally_saturated (lim_inf \<N>i)\<close>
    using \<N>i_is_derivation \<N>i_is_locally_fair
    using locally_fair_derivation_is_saturated_at_liminf
    by blast
  then have \<open>to_AF bot \<in> lim_inf \<N>i\<close>
    using F_statically_complete S_calculus_strong_statically_complete \<N>i_inf_entails_bot
    by blast
  then show \<open>\<exists> i. to_AF bot \<in> llnth \<N>i i\<close>
    by (transfer fixing: bot)
       (meson Liminf_llist_imp_exists_index)
qed

end (* context annotated_calculus *)

section \<open>Extensions: Inferences and simplifications\<close>

subsection \<open>Simplifications\<close>

datatype 'f simplification =
  Simplify (S_from: \<open>'f set\<close>) (S_to: \<open>'f set\<close>)

text \<open>
  Simplification rules are said to be sound if every conclusion is entailed by all premises.
  We could have also used our conjunctive entailment
  @{const consequence_relation.entails_conjunctive}, but it is defined that way so there is
  nothing to worry about.
\<close>

locale AF_calculus = sc: sound_calculus bot Inf entails entails_sound Red\<^sub>I Red\<^sub>F
  for
    bot :: "('f, 'v :: countable) AF" and
    Inf :: \<open>('f, 'v) AF inference set\<close> and
    entails :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool" and
    entails_sound :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool" and
    Red\<^sub>I :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set" and
    Red\<^sub>F :: "('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set"

locale AF_calculus_extended = 
  AF_calculus bot Inf entails entails_sound Red\<^sub>I Red\<^sub>F
  for bot :: \<open>('f, 'v :: countable) AF\<close> and
      Inf :: \<open>('f, 'v) AF inference set\<close> and
      entails :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> and
      entails_sound :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50) and
      Red\<^sub>I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> and
      Red\<^sub>F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close>
  + fixes
      Simps :: \<open>('f, 'v) AF simplification set\<close> and
      OptInfs :: \<open>('f, 'v) AF inference set\<close>
    assumes
      simps_simp: \<open>\<delta> \<in> Simps \<Longrightarrow> (S_from \<delta> - S_to \<delta>) \<subseteq> Red\<^sub>F (S_to \<delta>)\<close> and
      simps_sound: \<open>\<delta> \<in> Simps \<Longrightarrow> \<forall>\<C> \<in> S_to \<delta>. S_from \<delta> \<Turnstile>s {\<C>}\<close> and
      (* no_infinite_simps: \<open>finite (S_from \<delta>) \<Longrightarrow> \<delta> \<in> Simps \<Longrightarrow> finite (S_to \<delta>)\<close> and *)
      infs_sound: \<open>\<iota> \<in> OptInfs \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s {concl_of \<iota>}\<close>
begin

lemma simp_in_derivations: \<open>\<delta> \<in> Simps \<Longrightarrow> 
  sc.derive (\<M> \<union> S_from \<delta>) (\<M> \<union> S_to \<delta>)\<close>
  unfolding sc.derive_def
proof 
  fix C
  assume d_in: \<open>\<delta> \<in> Simps\<close> and
    \<open>C \<in> \<M> \<union> S_from \<delta> - (\<M> \<union> S_to \<delta>)\<close>
  then have \<open>C \<in> S_from \<delta> - S_to \<delta>\<close>
    by blast
  then show \<open>C \<in> Red\<^sub>F (\<M> \<union> S_to \<delta>)\<close>
    using simps_simp[OF d_in] by (meson sc.Red_F_of_subset subset_eq sup.cobounded2)
qed

lemma opt_infs_in_derivations: \<open>\<iota> \<in> OptInfs \<Longrightarrow> 
  sc.derive (\<M> \<union> set (prems_of \<iota>)) (\<M> \<union> set (prems_of \<iota>) \<union> {concl_of \<iota>})\<close>
  unfolding sc.derive_def
proof 
  fix C
  assume \<open>\<iota> \<in> OptInfs\<close> and
    C_in: \<open>C \<in> \<M> \<union> set (prems_of \<iota>) - (\<M> \<union> set (prems_of \<iota>) \<union> {concl_of \<iota>})\<close>
  have \<open>\<M> \<union> set (prems_of \<iota>) - (\<M> \<union> set (prems_of \<iota>) \<union> {concl_of \<iota>}) = {}\<close>
    by blast
  then have False using C_in by auto
  then show \<open>C \<in> Red\<^sub>F (\<M> \<union> set (prems_of \<iota>) \<union> {concl_of \<iota>})\<close>
    by auto
qed

end

text \<open>Empty sets of simplifications and optional inferences are accepted in 
  term\<open>locale AF_calculus_extended\<close>\<close>

context AF_calculus
begin

sublocale empty_simps: 
  AF_calculus_extended bot Inf entails entails_sound Red\<^sub>I Red\<^sub>F 
  "{} :: ('f, 'v) AF simplification set" "{} :: ('f, 'v) AF inference set" 
  by (unfold_locales, auto)

end (* context AF_calculus *)


text \<open>
  Here we extend our basic calculus with simplification rules, one at a time:
  \<^item> \textsc{Split} performs a $n$-ary case analysis on the head of the premise;
  \<^item> \textsc{Collect} performs garbage collection on clauses which contain propositionally
  unsatisfiable heads;
  \<^item> \textsc{Trim} removes assertions which are entailed by others.
\<close>

subsubsection \<open>The Split Rule\<close>

locale AF_calculus_with_split =
  base_calculus: AF_calculus_extended bot SInf entails entails_sound SRed\<^sub>I
  SRed\<^sub>F Simps OptInfs
  for bot :: \<open>('f, 'v :: countable) AF\<close> and
      SInf :: \<open>('f, 'v) AF inference set\<close> and
      entails :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>A\<^sub>F\<close> 50) and
      entails_sound :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>A\<^sub>Fs\<close> 50) and
      SRed\<^sub>I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> and
      SRed\<^sub>F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> and
      Simps :: \<open>('f, 'v) AF simplification set\<close> and
      OptInfs :: \<open>('f, 'v) AF inference set\<close>
  + fixes
      splittable :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> bool\<close>
    assumes
(*      split_creates_singleton_assertion_sets: 
        \<open>splittable \<C> \<C>s \<Longrightarrow> \<D> |\<in>| \<C>s \<Longrightarrow> (\<exists> (a :: 'v sign). A_of \<D> = {| a |})\<close>  and
      split_not_empty: \<open>splittable \<C> \<C>s \<Longrightarrow> \<C>s \<noteq>  {||}\<close> and *)
      split_sound1: \<open>splittable \<C> \<C>s \<Longrightarrow>
        {\<C>} \<Turnstile>\<^sub>A\<^sub>Fs {AF.Pair (F_of bot) (ffUnion (fimage neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>)}\<close> and
      split_sound2: \<open>splittable \<C> \<C>s \<Longrightarrow> \<forall> \<C>' \<in> fset \<C>s. {\<C>} \<Turnstile>\<^sub>A\<^sub>Fs {\<C>'}\<close> and
      split_simp: \<open>splittable \<C> \<C>s \<Longrightarrow> \<C> \<in> SRed\<^sub>F 
        ({AF.Pair (F_of bot) (ffUnion ((|`|) neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>)} \<union> fset \<C>s)\<close>
begin

text \<open>
  Rule definitions follow a similar naming convention to our two inference rules
  \textsc{Base} and \textsc{Unsat} defined in @{locale annotated_calculus}:
  $X\_simp$ is the definition of the simplification rule, while $X\_pre$ is some
  precondition which must hold for the rule to be applicable.
\<close> 

abbreviation split_pre :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> bool\<close> where
  \<open>split_pre \<C> \<C>s \<equiv> splittable \<C> \<C>s\<close>

abbreviation split_res :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> ('f, 'v) AF set\<close> where
  \<open>split_res \<C> \<C>s \<equiv> 
    (insert (AF.Pair (F_of bot) (ffUnion (fimage neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>)) (fset \<C>s))\<close>

abbreviation split_simp :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> ('f, 'v) AF simplification\<close> where
  \<open>split_simp \<C> \<C>s \<equiv> Simplify {\<C>} (split_res \<C> \<C>s)\<close>

(* Report definition 9 (Simps extended with Split) *)
inductive_set Simps_with_Split :: \<open>('f, 'v) AF simplification set\<close> where
  split: \<open>split_pre \<C> \<C>s \<Longrightarrow> split_simp \<C> \<C>s \<in> Simps_with_Split\<close>
| other: \<open>simp \<in> Simps \<Longrightarrow> simp \<in> Simps_with_Split\<close>

(*
lemma no_infinite_simps: \<open>finite (S_from \<iota>) \<Longrightarrow> \<iota> \<in> Simps_with_Split \<Longrightarrow> finite (S_to \<iota>)\<close>
  using Simps_with_Split.cases base_calculus.no_infinite_simps
  by force 
*)

(* Report theorem 14 for Simps extended with Split *)
theorem Inf_with_split_sound_wrt_entails_sound:
  \<open>\<iota> \<in> Simps_with_Split \<Longrightarrow> \<forall> \<C> \<in> S_to \<iota>. S_from \<iota> \<Turnstile>\<^sub>A\<^sub>Fs {\<C>}\<close>
proof -
  assume \<iota>_is_simp_rule: \<open>\<iota> \<in> Simps_with_Split\<close>
  then show \<open>\<forall> \<C> \<in> S_to \<iota>. S_from \<iota> \<Turnstile>\<^sub>A\<^sub>Fs {\<C>}\<close>
  proof (intro ballI)
    fix \<C>
    assume \<C>_is_consq_of_\<iota>: \<open>\<C> \<in> S_to \<iota>\<close>
    show \<open>S_from \<iota> \<Turnstile>\<^sub>A\<^sub>Fs {\<C>}\<close>
      using \<iota>_is_simp_rule
    proof (cases rule: Simps_with_Split.cases)
      case (split \<C>' \<C>s)

      have \<open>S_from \<iota> \<Turnstile>\<^sub>A\<^sub>Fs {AF.Pair (F_of bot) (ffUnion (fimage neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>')}\<close>
        using split_sound1 split by auto
      moreover have \<open>\<forall>\<C>' \<in> fset \<C>s. S_from \<iota> \<Turnstile>\<^sub>A\<^sub>Fs {\<C>'}\<close>
        using split_sound2 split by auto
      ultimately show ?thesis
        using \<C>_is_consq_of_\<iota> split(1) unfolding S_to_def by auto
    next
      case other
      then show ?thesis
        using \<C>_is_consq_of_\<iota> base_calculus.simps_sound by auto
    qed
  qed
qed

(* Report theorem 19 for Split *)
lemma split_redundant: \<open>split_pre \<C> \<C>s \<Longrightarrow> \<C> \<in> SRed\<^sub>F (split_res \<C> \<C>s)\<close>
proof -
  assume pre_cond: \<open>split_pre \<C> \<C>s\<close>
  then show \<open>\<C> \<in> SRed\<^sub>F (split_res \<C> \<C>s)\<close>
    using split_simp by simp
qed

(* Report theorem 19 for Simps extended with Split *)
lemma simps_with_split_are_simps: \<open>\<iota> \<in> Simps_with_Split \<Longrightarrow> (S_from \<iota> - S_to \<iota>) \<subseteq> SRed\<^sub>F (S_to \<iota>)\<close>
proof
  fix \<C>
  assume i_in: \<open>\<iota> \<in> Simps_with_Split\<close> and
    C_in: \<open>\<C> \<in> S_from \<iota> - S_to \<iota>\<close>
  then show \<open>\<C> \<in> SRed\<^sub>F (S_to \<iota>)\<close>
  proof (cases rule: Simps_with_Split.cases)
    case (split \<C>' \<C>s)
    then have \<open>\<C> = \<C>'\<close> using C_in by auto
    moreover have \<open>S_to \<iota> = split_res \<C>' \<C>s\<close> using split(1) simplification.sel(2) by auto
    ultimately show ?thesis
      using split_redundant[OF split(2)] by presburger
  next
    case other
    then show ?thesis
      using base_calculus.simps_simp C_in by blast
  qed
qed

sublocale AF_calc_ext: AF_calculus_extended bot SInf entails entails_sound 
  SRed\<^sub>I SRed\<^sub>F Simps_with_Split OptInfs
  using simps_with_split_are_simps Inf_with_split_sound_wrt_entails_sound (*no_infinite_simps*)
  base_calculus.infs_sound  by (unfold_locales, auto)

end (* locale AF_calculus_with_split *)

locale splitting_calculus =
  core: annotated_calculus bot Inf entails entails_sound Red\<^sub>I Red\<^sub>F fml asn 
  for bot :: 'f and
      Inf :: \<open>'f inference set\<close> and
      entails :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) and
      entails_sound :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50) and
      Red\<^sub>I :: \<open>'f set \<Rightarrow> 'f inference set\<close> and
      Red\<^sub>F :: \<open>'f set \<Rightarrow> 'f set\<close> and
      fml :: \<open>'v :: countable \<Rightarrow> 'f\<close> and
      asn :: \<open>'f sign \<Rightarrow> ('v :: countable) sign set\<close>
begin

interpretation AF_sound_cons_rel: consequence_relation \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  by (rule core.AF_ext_sound_cons_rel)

interpretation SInf_sound_inf_system: sound_inference_system core.SInf \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  by (standard, auto simp add: core.SInf_sound_wrt_entails_sound)

text \<open>
  Rule definitions follow a similar naming convention to our two inference rules
  \textsc{Base} and \textsc{Unsat} defined in @{locale annotated_calculus}:
  $X\_simp$ is the definition of the simplification rule, while $X\_pre$ is some
  precondition which must hold for the rule to be applicable.
\<close> 

definition split_form :: \<open>'f \<Rightarrow> 'f fset \<Rightarrow> bool\<close> where
  \<open>split_form C Cs \<longleftrightarrow> C \<noteq> bot \<and> fcard Cs \<ge> 2
                    \<and> {C} \<Turnstile>s fset Cs \<and> (\<forall> C'. C' |\<in>| Cs \<longrightarrow> C \<in> Red\<^sub>F {C'})\<close>

definition mk_split :: \<open>'f \<Rightarrow> 'f fset \<Rightarrow> ('f, 'v) AF fset\<close> where
  \<open>split_form C Cs \<Longrightarrow> mk_split C Cs \<equiv> (\<lambda> C'. AF.Pair C' {| SOME a. a \<in> asn (Pos C') |}) |`| Cs\<close>

definition splittable :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> bool\<close> where
  \<open>splittable \<C> \<C>s \<equiv> split_form (F_of \<C>) (F_of |`| \<C>s) \<and> mk_split (F_of \<C>) (F_of |`| \<C>s) = \<C>s\<close>

lemma split_creates_singleton_assertion_sets:
  \<open>splittable \<C> \<C>s \<Longrightarrow> A |\<in>| \<C>s \<Longrightarrow> (\<exists> a. A_of A = {| a |})\<close>
  using mk_split_def unfolding splittable_def by (metis (no_types, lifting) AF.sel(2) fimageE)

lemma split_all_assertion_sets_asn:
  \<open>splittable \<C> \<C>s \<Longrightarrow> A |\<in>| \<C>s \<Longrightarrow> (\<exists> a. A_of A = {|a|} \<and> a \<in> asn (Pos (F_of A)))\<close>
proof -
  assume pre_cond: \<open>splittable \<C> \<C>s\<close> and
         A_elem_As: \<open>A |\<in>| \<C>s\<close>
  then have pre_cond1: \<open>split_form (F_of \<C>) (F_of |`| \<C>s)\<close> and
    pre_cond2: \<open>mk_split (F_of \<C>) (F_of |`| \<C>s) = \<C>s\<close>
    unfolding splittable_def by auto
  have mk_split_applied_def: \<open>mk_split (F_of \<C>) (F_of |`| \<C>s) \<equiv> 
    (\<lambda> C'. AF.Pair C' {| SOME a. a \<in> asn (Pos C') |}) |`| (F_of |`| \<C>s)\<close>
    using mk_split_def pre_cond unfolding splittable_def by (smt (verit, del_insts))
  have \<open>\<exists> a. A_of A = {|a|}\<close>
    using pre_cond A_elem_As by (simp add: split_creates_singleton_assertion_sets)
  then obtain a where A_of_A_singleton_a: \<open>A_of A = {|a|}\<close>
    by blast
  then have \<open>a \<in> asn (Pos (F_of A))\<close>
    using pre_cond2 A_elem_As core.asn_not_empty some_in_eq unfolding mk_split_applied_def
    by (smt (z3) AF.exhaust_sel AF.inject FSet.fsingletonE fimage.rep_eq finsertI1 imageE someI_ex)
  then show \<open>\<exists> a. A_of A = {|a|} \<and> a \<in> asn (Pos (F_of A))\<close>
    using A_of_A_singleton_a by blast
qed

lemma split_all_pairs_in_As_in_Cs: \<open>splittable \<C> \<C>s \<Longrightarrow> (\<forall> P. P |\<in>| \<C>s \<longrightarrow> F_of P |\<in>| (F_of |`| \<C>s))\<close>
  using mk_split_def
  by fastforce

lemma split_all_pairs_in_Cs_in_As:
  \<open>splittable \<C> \<C>s \<Longrightarrow> (\<forall> C. C |\<in>| (F_of |`| \<C>s) \<longrightarrow> (\<exists> a. AF.Pair C {|a|} |\<in>| \<C>s))\<close>
  using mk_split_def unfolding splittable_def
  by fastforce

lemma split_not_empty: \<open>splittable \<C> \<C>s \<Longrightarrow> \<C>s \<noteq>  {||}\<close>
  unfolding splittable_def split_form_def
  by (metis bot_nat_0.extremum fcard_fempty fimage_fempty le_antisym nat.simps(3) numerals(2))

notation core.sound_cons.entails_neg (infix \<open>\<Turnstile>s\<^sub>\<sim>\<close> 50)

lemma split_sound1: \<open>splittable \<C> \<C>s \<Longrightarrow>
  {\<C>} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot (ffUnion (fimage neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>)}\<close>
proof -
  assume split_cond: \<open>splittable \<C> \<C>s\<close>
  then have split_form: \<open>split_form (F_of \<C>) (F_of |`| \<C>s)\<close> and 
    split_mk: \<open>mk_split (F_of \<C>) (F_of |`| \<C>s) = \<C>s\<close>
    unfolding splittable_def by auto
  define Cs where \<open>Cs = F_of |`| \<C>s\<close>
  have Cs_not_empty: \<open>Cs \<noteq> {||}\<close>
    using split_cond split_not_empty unfolding Cs_def by blast
  then have \<C>s_not_empty: \<open>\<C>s \<noteq> {||}\<close>
    using mk_split_def[of \<open>F_of \<C>\<close> \<open>Cs\<close>] split_mk split_form
    fimage_of_non_fempty_is_non_fempty[OF Cs_not_empty] unfolding Cs_def by fastforce
  have \<open>fcard Cs \<ge> 1\<close>
    by (simp add: Cs_not_empty Suc_le_eq non_zero_fcard_of_non_empty_set)
  then have card_fset_Cs_ge_1: \<open>card (Pos ` fset Cs) \<ge> 1\<close>
    by (metis Cs_not_empty bot_fset.rep_eq card_eq_0_iff empty_is_image finite_fset finite_imageI
        fset_cong less_one linorder_not_le)
  have \<open>{F_of \<C>} \<Turnstile>s fset Cs\<close>
    using split_form unfolding Cs_def split_form_def by blast
  then have F_of_\<C>_entails_Cs: \<open>{Pos (F_of \<C>)} \<Turnstile>s\<^sub>\<sim> Pos ` fset Cs\<close>
    unfolding core.sound_cons.entails_neg_def
    by (smt (verit, del_insts) UnCI imageI mem_Collect_eq singleton_conv
        core.sound_cons.entails_subsets subsetI)

  have finite_image_Pos_Cs: \<open>finite (Pos ` fset Cs)\<close>
    using finite_fset by blast

  have all_C\<^sub>i_entail_bot: \<open>fset (ffUnion (fimage neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>) \<subseteq> total_strip J
   \<Longrightarrow> AF.Pair C\<^sub>i {|a\<^sub>i|} |\<in>| \<C>s \<Longrightarrow> (core.fml_ext ` total_strip J) \<union> {Pos C\<^sub>i} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
    for J C\<^sub>i a\<^sub>i
  proof -
    fix J \<C>\<^sub>i a\<^sub>i
    assume \<open>fset (ffUnion (fimage neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>) \<subseteq> total_strip J\<close> and
      Pair_\<C>\<^sub>i_a\<^sub>i_in_As: \<open>AF.Pair \<C>\<^sub>i {|a\<^sub>i|} |\<in>| \<C>s\<close>
    then have \<open>neg a\<^sub>i \<in> total_strip J\<close>
      using mk_disjoint_finsert
      by fastforce
    then have neg_fml_a\<^sub>i_in_J: \<open>neg (core.fml_ext a\<^sub>i) \<in> core.fml_ext ` total_strip J\<close>
      by (metis core.fml_ext.simps(1) core.fml_ext.simps(2) image_iff is_Neg_to_V is_Pos_to_V
          neg.simps(1) neg.simps(2))
    moreover have a\<^sub>i_in_asn_\<C>\<^sub>i: \<open>a\<^sub>i \<in> asn (Pos \<C>\<^sub>i)\<close>
      using split_all_assertion_sets_asn[OF split_cond Pair_\<C>\<^sub>i_a\<^sub>i_in_As]
      by auto
    moreover have \<open>{Pos \<C>\<^sub>i} \<Turnstile>s\<^sub>\<sim> {Pos \<C>\<^sub>i}\<close>
      by (meson consequence_relation.entails_reflexive core.sound_cons.ext_cons_rel)
    then have \<open>(core.fml_ext ` (total_strip J - {neg a\<^sub>i}) \<union> {Pos \<C>\<^sub>i}) \<Turnstile>s\<^sub>\<sim> {Pos \<C>\<^sub>i, Pos bot}\<close>
      by (smt (verit, best) Un_upper2 consequence_relation.entails_subsets insert_is_Un
          core.sound_cons.ext_cons_rel sup_ge1)
    ultimately show \<open>core.sound_cons.entails_neg ((core.fml_ext ` total_strip J) \<union> {Pos \<C>\<^sub>i}) {Pos bot}\<close>
    proof -
      have \<open>(core.fml_ext ` total_strip J \<union> {core.fml_ext a\<^sub>i}) \<Turnstile>s\<^sub>\<sim> ({Pos bot} \<union> {})\<close>
        by (smt (z3) Bex_def_raw UnCI Un_commute Un_insert_right Un_upper2 neg_fml_a\<^sub>i_in_J
            consequence_relation.entails_subsets insert_is_Un insert_subset
            core.sound_cons.ext_cons_rel core.sound_cons.pos_neg_entails_bot)
      then show ?thesis
        by (smt (verit, ccfv_threshold) core.C_entails_fml Un_commute a\<^sub>i_in_asn_\<C>\<^sub>i
            consequence_relation.entails_cut core.fml_ext_is_mapping insert_is_Un
            core.sound_cons.ext_cons_rel) 
    qed
  qed
  then have \<open>fset (ffUnion (fimage neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>) \<subseteq> total_strip J \<Longrightarrow>
         ((core.fml_ext ` total_strip J) \<union> {Pos (F_of \<C>)}) \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close> for J 
    unfolding splittable_def
  proof -
    fix J
    assume \<open>fset (ffUnion (fimage neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>) \<subseteq> total_strip J\<close>
    then have C\<^sub>i_head_of_pair_entails_bot:
      \<open>AF.Pair C\<^sub>i {|a\<^sub>i|} |\<in>| \<C>s \<Longrightarrow> (core.fml_ext ` total_strip J) \<union> {Pos C\<^sub>i} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
      for C\<^sub>i a\<^sub>i
      using all_C\<^sub>i_entail_bot
      by blast
    then have \<open>C\<^sub>i |\<in>| Cs \<Longrightarrow> (core.fml_ext ` total_strip J) \<union> {Pos C\<^sub>i} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
      for C\<^sub>i
    proof -
      fix C\<^sub>i
      assume \<open>C\<^sub>i |\<in>| Cs\<close>
      then have \<open>\<exists> a\<^sub>i. AF.Pair C\<^sub>i {|a\<^sub>i|} |\<in>| \<C>s\<close>
        using split_all_pairs_in_Cs_in_As[OF split_cond] unfolding Cs_def by presburger
      then obtain a\<^sub>i where \<open>AF.Pair C\<^sub>i {|a\<^sub>i|} |\<in>| \<C>s\<close>
        by blast
      then show \<open>(core.fml_ext ` total_strip J) \<union> {Pos C\<^sub>i} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
        using C\<^sub>i_head_of_pair_entails_bot by blast
    qed
    then show \<open>(core.fml_ext ` total_strip J) \<union> {Pos (F_of \<C>)} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
      using core.sound_cons.entails_of_entails_iff[OF F_of_\<C>_entails_Cs finite_image_Pos_Cs
          card_fset_Cs_ge_1] by blast
  qed
  then have
    \<open>fset (ffUnion (fimage neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>) \<subseteq> total_strip J \<Longrightarrow>
         ((core.fml_ext ` total_strip J) \<union> Pos ` ({\<C>} proj\<^sub>J J)) \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
    for J 
    using split_cond by (simp add: core.enabled_def core.enabled_projection_def)

  then show \<open>{\<C>} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot (ffUnion (fimage neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>)}\<close>
    unfolding core.AF_entails_sound_def using core.enabled_def core.enabled_set_def by simp
qed

lemma split_sound2: \<open>splittable \<C> \<C>s \<Longrightarrow> \<forall> \<C>' \<in> fset \<C>s. {\<C>} \<Turnstile>s\<^sub>A\<^sub>F {\<C>'}\<close>
proof
  fix \<C>'
  assume split_cond: \<open>splittable \<C> \<C>s\<close> and \<C>'_in: \<open>\<C>' |\<in>| \<C>s\<close>
  have \<open>C'' |\<in>| \<C>s \<Longrightarrow> fset (A_of C'') \<subseteq> total_strip J \<Longrightarrow>
         (core.fml_ext ` total_strip J) \<union> Pos ` ({\<C>} proj\<^sub>J J) \<Turnstile>s\<^sub>\<sim> {Pos (F_of C'')}\<close> for J C''
  proof -
    fix J C''
    assume C''_in_As: \<open>C'' |\<in>| \<C>s\<close> and
      A_of_C''_subset_J: \<open>fset (A_of C'') \<subseteq> total_strip J\<close>
    then have \<open>\<exists> a\<^sub>i. a\<^sub>i \<in> asn (Pos (F_of C'')) \<and> A_of C'' = {| a\<^sub>i |}\<close>
      using split_all_assertion_sets_asn[OF split_cond C''_in_As] by blast
    then obtain a\<^sub>i where a\<^sub>i_in_asn_F_of_C'': \<open>a\<^sub>i \<in> asn (Pos (F_of C''))\<close> and
      A_of_C''_is: \<open>A_of C'' = {| a\<^sub>i |}\<close>
      by blast
    then show \<open>(core.fml_ext ` total_strip J) \<union> Pos ` ({\<C>} proj\<^sub>J J) \<Turnstile>s\<^sub>\<sim> {Pos (F_of C'')}\<close>
      by (smt (verit, best) A_of_C''_subset_J consequence_relation.entails_subsets empty_subsetI
          finsert.rep_eq core.fml_entails_C core.fml_ext_is_mapping image_eqI insert_is_Un 
          insert_subset core.sound_cons.ext_cons_rel sup_ge1)
  qed
  then have unfolded_AF_sound_entails: \<open>C'' \<in> fset \<C>s \<Longrightarrow> fset (A_of C'') \<subseteq> total_strip J \<Longrightarrow>
         (core.fml_ext ` total_strip J) \<union> Pos ` ({\<C>} proj\<^sub>J J) \<Turnstile>s\<^sub>\<sim> {Pos (F_of C'')}\<close> for J C''
    by fast

  show \<open>{\<C>} \<Turnstile>s\<^sub>A\<^sub>F {\<C>'}\<close>
   unfolding core.AF_entails_sound_def core.enabled_set_def core.enabled_def
   using unfolded_AF_sound_entails[OF \<C>'_in] split_cond \<C>'_in by auto
qed

lemma split_simp: \<open>splittable \<C> \<C>s \<Longrightarrow> \<C> \<in> 
  core.SRed\<^sub>F ({ AF.Pair bot (ffUnion ((|`|) neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>) } \<union> fset \<C>s)\<close>
proof -
  assume split_cond: \<open>splittable \<C> \<C>s\<close>
  define Cs where \<open>Cs = F_of |`| \<C>s\<close>
  then have F_of_\<C>_not_bot: \<open>F_of \<C> \<noteq> bot\<close> and
    \<open>fcard Cs \<ge> 2\<close> and
    \<open>{F_of \<C>} \<Turnstile>s fset Cs\<close> and
    \<C>_red_to_splitted_\<C>s: \<open>\<forall> C'. C' |\<in>| Cs \<longrightarrow> F_of \<C> \<in> Red\<^sub>F {C'}\<close>
    using split_cond unfolding splittable_def split_form_def
    by blast+
  then have \<open>\<forall> J. core.enabled \<C> J \<longrightarrow>
    F_of \<C> \<in> Red\<^sub>F (({ AF.Pair bot (ffUnion (fimage neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>) } proj\<^sub>J J)
    \<union> (fset \<C>s proj\<^sub>J J))\<close>
  proof (intro allI impI)
    fix J
    assume \<C>_enabled: \<open>core.enabled \<C> J\<close>
    then show
      \<open>F_of \<C> \<in> Red\<^sub>F (({ AF.Pair bot (ffUnion (fimage neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>) } proj\<^sub>J J)
       \<union> (fset \<C>s proj\<^sub>J J))\<close>
    proof (cases \<open>\<exists>A. A |\<in>| A_of |`| \<C>s \<and> (\<exists> a. a |\<in>| A \<and> a \<in> total_strip J)\<close>)
      case True
      then have ex_C_enabled_in_As: \<open>\<exists> C. C |\<in>| \<C>s \<and> core.enabled C J\<close>
        using core.enabled_def split_creates_singleton_assertion_sets split_cond
        by fastforce
      then have \<open>\<exists> C. C \<in> fset \<C>s proj\<^sub>J J\<close>
        by (simp add: core.enabled_projection_def)
      then show ?thesis
        using \<C>_red_to_splitted_\<C>s split_cond core.Red_F_of_subset[of \<open>fset \<C>s proj\<^sub>J J\<close>]
          mk_split_def by (smt (z3) CollectD Cs_def basic_trans_rules(31) core.enabled_projection_def
          core.sound_calculus_axioms insert_subset le_sup_iff sound_calculus.Red_F_of_subset
          split_all_pairs_in_As_in_Cs sup_bot.right_neutral sup_ge1)
    next
      case False
      then have \<open>fset \<C>s proj\<^sub>J J = {}\<close>
        using split_creates_singleton_assertion_sets[OF split_cond]
        by (smt (verit, del_insts) Collect_empty_eq core.enabled_def core.enabled_projection_def
            fimage_finsert finsert.rep_eq finsertCI insert_subset mk_disjoint_finsert)
      moreover have \<open>\<forall> A. A |\<in>| A_of |`| \<C>s \<longrightarrow> (\<forall> a. a |\<in>| A \<longrightarrow> \<not> a \<in> total_strip J)\<close>
        using False
        by blast
      then have \<open>\<forall> A. A |\<in>| A_of |`| \<C>s \<longrightarrow> (\<forall> a. a |\<in>| A \<longrightarrow> neg a \<in> total_strip J)\<close>
        by auto
      then have \<open>fset (ffUnion ((fimage neg \<circ> A_of) |`| \<C>s)) \<subseteq> total_strip J\<close>
        by (smt (verit, best) fimage_iff fset.map_comp fset_ffUnion_subset_iff_all_fsets_subset subsetI)
      then have \<open>fset (ffUnion ((fimage neg \<circ> A_of) |`| \<C>s) |\<union>| A_of \<C>) \<subseteq> total_strip J\<close>
        using \<C>_enabled
        by (simp add: core.enabled_def)
      then have \<open>{AF.Pair bot (ffUnion ((fimage neg \<circ> A_of) |`| \<C>s) |\<union>| A_of \<C>)} proj\<^sub>J J = {bot}\<close>
        unfolding core.enabled_projection_def core.enabled_def
        by auto
      ultimately show ?thesis
        by (simp add: F_of_\<C>_not_bot core.all_red_to_bot)
    qed
  qed
  then show \<open>\<C> \<in> core.SRed\<^sub>F ({ AF.Pair bot (ffUnion ((|`|) neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>) } \<union> fset \<C>s)\<close>
    unfolding core.SRed\<^sub>F_def core.enabled_def
    by (intro UnI1) (smt (verit, ccfv_threshold) AF.collapse CollectI core.distrib_proj)
qed

sublocale empty_simps: AF_calculus_extended "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" 
  "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I core.SRed\<^sub>F "{}" "{}"
proof
  show \<open>core.SRed\<^sub>I N \<subseteq> core.SInf\<close> for N
    using core.SRed\<^sub>I_in_SInf .
next
  show \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<Longrightarrow> N - core.SRed\<^sub>F N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close> for N
    using core.SRed\<^sub>F_entails_bot .
next
  show \<open>N \<subseteq> N' \<Longrightarrow> core.SRed\<^sub>F N \<subseteq> core.SRed\<^sub>F N'\<close> for N N'
    using core.SRed\<^sub>F_of_subset_F .
next
  show \<open>N \<subseteq> N' \<Longrightarrow> core.SRed\<^sub>I N \<subseteq> core.SRed\<^sub>I N'\<close> for N N'
    using core.SRed\<^sub>I_of_subset_F .
next
  show \<open>N' \<subseteq> core.SRed\<^sub>F N \<Longrightarrow> core.SRed\<^sub>F N \<subseteq> core.SRed\<^sub>F (N - N')\<close> for N N'
    using core.SRed\<^sub>F_of_SRed\<^sub>F_subset_F .
next
  show \<open>N' \<subseteq> core.SRed\<^sub>F N \<Longrightarrow> core.SRed\<^sub>I N \<subseteq> core.SRed\<^sub>I (N - N')\<close> for N N'
    using core.SRed\<^sub>I_of_SRed\<^sub>F_subset_F .
next
  show \<open>\<iota> \<in> core.SInf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> core.SRed\<^sub>I N\<close> for \<iota> N
    using core.S_calculus.Red_I_of_Inf_to_N .
next
  show \<open>\<iota> \<in> {} \<Longrightarrow> S_from \<iota> - S_to \<iota> \<subseteq> core.SRed\<^sub>F (S_to \<iota>)\<close> for \<iota>
    by simp
next
  show \<open>\<iota> \<in> {} \<Longrightarrow> \<forall>\<C>\<in>S_to \<iota>. S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close> for \<iota>
    by blast
(*next
  show \<open>finite (S_from \<iota>) \<Longrightarrow> \<iota> \<in> {} \<Longrightarrow> finite (S_to \<iota>)\<close> for \<iota> :: "('f, 'v) AF simplification"
    by blast*)
next
  show \<open>\<iota> \<in> {} \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>}\<close> for \<iota>
    by blast
qed

lemma extend_simps_with_split:
  assumes
    \<open>AF_calculus_extended (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I 
      core.SRed\<^sub>F Simps OptInfs\<close>
  shows
    \<open>AF_calculus_with_split (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I core.SRed\<^sub>F Simps OptInfs
       splittable\<close>
proof -
  interpret sound_simps: AF_calculus_extended "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)"
    "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I core.SRed\<^sub>F Simps OptInfs
    using assms .
  show ?thesis
  proof
(*  show \<open>splittable \<C> \<C>s \<Longrightarrow> \<D> |\<in>| \<C>s \<Longrightarrow> \<exists>a. A_of \<D> = {|a|}\<close> for \<C> \<C>s \<D>
    using split_creates_singleton_assertion_sets .
  next
    show \<open>splittable \<C> \<C>s \<Longrightarrow> \<C>s \<noteq> {||}\<close> for \<C> \<C>s
      using split_not_empty . 
  next *)
    show \<open>splittable \<C> \<C>s \<Longrightarrow>
    {\<C>} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair (F_of (to_AF bot)) (ffUnion ((|`|) neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>)}\<close> for \<C> \<C>s
      using split_sound1 by (simp add: F_of_to_AF)
  next
    show \<open>splittable \<C> \<C>s \<Longrightarrow> \<forall>\<C>'|\<in>|\<C>s. {\<C>} \<Turnstile>s\<^sub>A\<^sub>F {\<C>'}\<close> for \<C> \<C>s
      using split_sound2 .
  next
    show \<open>splittable \<C> \<C>s \<Longrightarrow> \<C> \<in> core.SRed\<^sub>F 
    ({AF.Pair (F_of (to_AF bot)) (ffUnion ((|`|) neg |`| A_of |`| \<C>s) |\<union>| A_of \<C>)} \<union> fset \<C>s)\<close>
      for \<C> \<C>s
      using split_simp by (simp add: F_of_to_AF)
  qed
qed

interpretation splitting_calc_with_split:
  AF_calculus_with_split "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I core.SRed\<^sub>F "{}" "{}" splittable
  using extend_simps_with_split[OF empty_simps.AF_calculus_extended_axioms] .

end (* locale splitting_calculus *)

subsubsection \<open>The Collect Rule\<close>

locale AF_calculus_with_collect =  base_calculus: AF_calculus_extended bot SInf
  entails entails_sound SRed\<^sub>I SRed\<^sub>F Simps OptInfs
  for bot :: \<open>('f, 'v :: countable) AF\<close> and
      SInf :: \<open>('f, 'v) AF inference set\<close> and
      entails :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>A\<^sub>F\<close> 50) and
      entails_sound :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<^sub>A\<^sub>F\<close> 50) and
      SRed\<^sub>I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> and
      SRed\<^sub>F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> and
      Simps :: \<open>('f, 'v) AF simplification set\<close> and
      OptInfs :: \<open>('f, 'v) AF inference set\<close>
  + assumes
    collect_redundant: \<open>F_of \<C> \<noteq> F_of bot \<and> \<M> \<Turnstile>\<^sub>A\<^sub>F {AF.Pair (F_of bot) (A_of \<C>)} \<and> 
      (\<forall> \<C> \<in> \<M>. F_of \<C> = F_of bot) \<Longrightarrow> \<C> \<in> SRed\<^sub>F \<M>\<close>
begin

interpretation AF_sound_cons_rel: consequence_relation bot \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  using base_calculus.sc.sound_cons.consequence_relation_axioms .

interpretation SInf_sound_inf_system: sound_inference_system SInf bot \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  using base_calculus.sc.sound_inference_system_axioms .

abbreviation collect_pre :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> where
  \<open>collect_pre \<C> \<M> \<equiv> 
    F_of \<C> \<noteq> F_of bot \<and> \<M> \<Turnstile>\<^sub>A\<^sub>F {AF.Pair (F_of bot) (A_of \<C>)} \<and> (\<forall> \<C> \<in> \<M>. F_of \<C> = F_of bot)\<close>

abbreviation collect_simp :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF set \<Rightarrow> ('f, 'v) AF simplification\<close> where
  \<open>collect_simp \<C> \<M> \<equiv> Simplify (insert \<C> \<M>) \<M>\<close>

(* Report definition 9 (Collect only) *)
inductive_set Simps_with_Collect :: \<open>('f, 'v) AF simplification set\<close> where
  collect: \<open>collect_pre \<C> \<M> \<Longrightarrow> collect_simp \<C> \<M> \<in> Simps_with_Collect\<close>
| other: \<open>\<iota> \<in> Simps \<Longrightarrow> \<iota> \<in> Simps_with_Collect\<close>

(*
lemma no_infinite_simp_set: \<open>finite (S_from \<iota>) \<Longrightarrow> \<iota> \<in> Simps_with_Collect \<Longrightarrow> finite (S_to \<iota>)\<close>
  using Simps_with_Collect.cases base_calculus.no_infinite_simps by force 
*)

(* Report theorem 14 for simps extended with Collect *)
theorem SInf_with_collect_sound_wrt_entails_sound: 
  \<open>\<iota> \<in> Simps_with_Collect \<Longrightarrow> \<forall> \<C> \<in> S_to \<iota>. S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
proof -
  assume \<iota>_is_simp_rule: \<open>\<iota> \<in> Simps_with_Collect\<close>
  then show \<open>\<forall> \<C> \<in> S_to \<iota>. S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
  proof (intro ballI)
    fix \<C>
    assume \<C>_is_consq_of_\<iota>: \<open>\<C> \<in> S_to \<iota>\<close>
    show \<open>S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
      using \<iota>_is_simp_rule
    proof (cases rule: Simps_with_Collect.cases)
      case (collect \<C>' \<N>)
      then show ?thesis
        using \<C>_is_consq_of_\<iota> by (metis base_calculus.sc.sound_cons.entails_conjunctive_def 
            base_calculus.sc.sound_cons.subset_entailed simplification.sel(1) simplification.sel(2)
            subset_insertI)
    next
      case other
      then show ?thesis
        using base_calculus.simps_sound \<C>_is_consq_of_\<iota> by auto
    qed
  qed
qed

(* Report theorem 19 for Collect *)
theorem simps_with_collect_are_simps: 
  \<open>\<iota> \<in> Simps_with_Collect \<Longrightarrow> (S_from \<iota> - S_to \<iota>) \<subseteq> SRed\<^sub>F (S_to \<iota>)\<close>
proof
  fix \<C>
  assume \<iota>_is_simp_rule: \<open>\<iota> \<in> Simps_with_Collect\<close> and
    C_in: \<open>\<C> \<in> S_from \<iota> - S_to \<iota>\<close>
  then show \<open>\<C> \<in> SRed\<^sub>F (S_to \<iota>)\<close>
  proof (cases rule: Simps_with_Collect.cases)
    case (collect \<C>' \<M>)
    then have \<open>\<C> = \<C>'\<close>
      using C_in by auto
    moreover have \<open>S_to \<iota> = \<M>\<close>
      using collect(1) by simp
    ultimately show ?thesis
      using collect_redundant[OF collect(2)] by blast
  next
    case other
    then show ?thesis
      using base_calculus.simps_simp C_in by blast
  qed
qed

sublocale AF_calc_ext: AF_calculus_extended bot SInf entails entails_sound SRed\<^sub>I SRed\<^sub>F
  Simps_with_Collect OptInfs
  using simps_with_collect_are_simps SInf_with_collect_sound_wrt_entails_sound (*no_infinite_simp_set*)
    base_calculus.infs_sound by (unfold_locales, auto)

end (* locale AF_calculus_with_collect *)

context splitting_calculus
begin

(* part of report theorem 19 for Collect *)
lemma collect_redundant: \<open>F_of \<C> \<noteq> bot \<and> \<M> \<Turnstile>\<^sub>A\<^sub>F {AF.Pair bot (A_of \<C>)} \<and> 
      (\<forall> \<C> \<in> \<M>. F_of \<C> = bot) \<Longrightarrow> \<C> \<in> core.SRed\<^sub>F \<M>\<close>
proof clarsimp
  assume 
    head_\<C>_not_bot: \<open>F_of \<C> \<noteq> bot\<close> and
    \<M>_entails_bot_\<C>: \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F {AF.Pair bot (A_of \<C>)}\<close> and
    all_heads_are_bot_in_\<M>: \<open>\<forall> \<C> \<in> \<M>. F_of \<C> = bot\<close>
  have \<open>\<And> J. (\<exists> \<C>' \<in> \<M>. core.enabled \<C>' J) \<Longrightarrow> core.enabled \<C> J 
          \<Longrightarrow> F_of \<C> \<in> Red\<^sub>F (\<M> proj\<^sub>J J)\<close> and
       \<open>\<And> J. \<not> (\<exists> \<C>' \<in> \<M>. core.enabled \<C>' J) \<Longrightarrow> core.enabled \<C> J \<Longrightarrow> False\<close>
  proof -
    fix J
    assume \<C>_enabled: \<open>core.enabled \<C> J\<close> and
           \<open>\<exists> \<C>' \<in> \<M>. core.enabled \<C>' J\<close>
    then have \<open>\<M> proj\<^sub>J J = {bot}\<close>
      using all_heads_are_bot_in_\<M> unfolding core.enabled_projection_def by fast
    then show \<open>F_of \<C> \<in> Red\<^sub>F (\<M> proj\<^sub>J J)\<close>
      using core.all_red_to_bot[OF head_\<C>_not_bot] by simp
  next
    fix J
    assume \<C>_enabled: \<open>core.enabled \<C> J\<close> and
           \<open>\<not> (\<exists> \<C>' \<in> \<M>. core.enabled \<C>' J)\<close>
    then have \<M>_proj_J_empty: \<open>\<M> proj\<^sub>J J = {}\<close>
      unfolding core.enabled_projection_def by blast
    moreover have \<open>core.enabled (AF.Pair bot (A_of \<C>)) J\<close>
      using \<C>_enabled by (auto simp add: core.enabled_def)
    ultimately have \<open>{} \<Turnstile> {bot}\<close>
      using \<M>_entails_bot_\<C> using core.AF_entails_def by auto
    then show \<open>False\<close>
      using core.entails_bot_to_entails_empty core.entails_nontrivial by blast
  qed
  then show \<open>\<C> \<in> core.SRed\<^sub>F \<M>\<close>
    unfolding core.SRed\<^sub>F_def core.enabled_def by (smt (verit, ccfv_SIG) AF.collapse CollectI UnI1)
qed

lemma extend_simps_with_collect: 
  assumes
    \<open>AF_calculus_extended (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I 
      core.SRed\<^sub>F Simps OptInfs\<close>
  shows
    \<open>AF_calculus_with_collect (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I core.SRed\<^sub>F Simps OptInfs\<close>
proof -
  interpret sound_simps: 
    AF_calculus_extended "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I
      core.SRed\<^sub>F Simps
    using assms .
  show ?thesis
  proof
    fix \<C> \<M>
    show \<open>F_of \<C> \<noteq> F_of (to_AF bot) \<and> \<M> \<Turnstile>\<^sub>A\<^sub>F {AF.Pair (F_of (to_AF bot)) (A_of \<C>)} \<and> 
      (\<forall>\<C>\<in>\<M>. F_of \<C> = F_of (to_AF bot)) \<Longrightarrow> \<C> \<in> core.SRed\<^sub>F \<M>\<close>
      using collect_redundant by (simp add: F_of_to_AF)
  qed
qed

interpretation splitting_calc_with_collect:
  AF_calculus_with_collect "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I core.SRed\<^sub>F "{}" "{}"
  using extend_simps_with_collect[OF empty_simps.AF_calculus_extended_axioms] .

end (* context splitting_calculus *)

subsubsection \<open>The Trim Rule\<close>

locale AF_calculus_with_trim =  base_calculus: AF_calculus_extended bot SInf 
  entails entails_sound SRed\<^sub>I SRed\<^sub>F Simps OptInfs
  for bot :: \<open>('f, 'v :: countable) AF\<close> and
      SInf :: \<open>('f, 'v) AF inference set\<close> and
      entails :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>A\<^sub>F\<close> 50) and
      entails_sound :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<^sub>A\<^sub>F\<close> 50) and
      SRed\<^sub>I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> and
      SRed\<^sub>F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> and
      Simps :: \<open>('f, 'v) AF simplification set\<close> and
      OptInfs :: \<open>('f, 'v) AF inference set\<close>
  + assumes
    trim_sound: \<open>A_of \<C> = A |\<union>| B \<and> F_of \<C> \<noteq> F_of bot \<and> 
      \<M> \<union> {AF.Pair (F_of bot) A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair (F_of bot) B} \<and>
      (\<forall>\<C>\<in>\<M>. F_of \<C> = (F_of bot)) \<and> A |\<inter>| B = {||} \<and> A \<noteq> {||}
        \<Longrightarrow> insert \<C> \<M> \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair (F_of \<C>) B}\<close> and
    trim_redundant: \<open>A_of \<C> = A |\<union>| B \<and> F_of \<C> \<noteq> F_of bot \<and> 
      \<M> \<union> {AF.Pair (F_of bot) A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair (F_of bot) B} \<and>
      (\<forall>\<C>\<in>\<M>. F_of \<C> = (F_of bot)) \<and> A |\<inter>| B = {||} \<and> A \<noteq> {||}
        \<Longrightarrow> \<C> \<in> SRed\<^sub>F (\<M> \<union> { AF.Pair (F_of \<C>) B })\<close>

begin

interpretation AF_sound_cons_rel: consequence_relation bot \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  using base_calculus.sc.sound_cons.consequence_relation_axioms .

interpretation SInf_sound_inf_system: sound_inference_system SInf bot \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  using base_calculus.sc.sound_inference_system_axioms .

abbreviation trim_pre :: \<open>('f, 'v) AF \<Rightarrow> 'v sign fset \<Rightarrow> 'v sign fset \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> where
  \<open>trim_pre \<C> A B \<M> \<equiv> A_of \<C> = A |\<union>| B \<and> F_of \<C> \<noteq> F_of bot \<and>
                       \<M> \<union> { AF.Pair (F_of bot) A } \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair (F_of bot) B } \<and>
                       (\<forall> \<C> \<in> \<M>. F_of \<C> = (F_of bot)) \<and> A |\<inter>| B = {||} \<and> A \<noteq> {||}\<close>

abbreviation trim_simp :: \<open>('f, 'v) AF \<Rightarrow> 'v sign fset \<Rightarrow> 'v sign fset \<Rightarrow> ('f, 'v) AF set \<Rightarrow>
  ('f, 'v) AF simplification\<close> where
  \<open>trim_simp \<C> A B \<M> \<equiv> Simplify (insert \<C> \<M>) (insert (AF.Pair (F_of \<C>) B) \<M>)\<close>

(* Report definition 9 (Trim only) *)
inductive_set Simps_with_Trim :: \<open>('f, 'v) AF simplification set\<close> where
  trim: \<open>trim_pre \<C> A B \<M> \<Longrightarrow> trim_simp \<C> A B \<M> \<in> Simps_with_Trim\<close>
| other: \<open>\<iota> \<in> Simps \<Longrightarrow> \<iota> \<in> Simps_with_Trim\<close>

(*
lemma no_infinite_simp_set: \<open>finite (S_from \<iota>) \<Longrightarrow> \<iota> \<in> Simps_with_Trim \<Longrightarrow> finite (S_to \<iota>)\<close>
  using Simps_with_Trim.cases base_calculus.no_infinite_simps by force
*)

theorem SInf_with_trim_sound_wrt_entails_sound: 
  \<open>\<iota> \<in> Simps_with_Trim \<Longrightarrow> \<forall> \<C> \<in> S_to \<iota>. S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
proof -
  assume \<iota>_is_simp_rule: \<open>\<iota> \<in> Simps_with_Trim\<close>
  then show \<open>\<forall> \<C> \<in> S_to \<iota>. S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
  proof (intro ballI)
    fix \<C>
    assume \<C>_is_consq_of_\<iota>: \<open>\<C> \<in> S_to \<iota>\<close>
    show \<open>S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
      using \<iota>_is_simp_rule
    proof (cases rule: Simps_with_Trim.cases)
      case (trim \<C>' A B \<N>)
      then have \<open>A_of \<C>' = A |\<union>| B\<close> and
        \<open>F_of \<C>' \<noteq> F_of bot\<close> and
        \<N>_and_Pair_bot_A_entails_Pair_bot_B: 
        \<open>\<N> \<union> {AF.Pair (F_of bot) A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair (F_of bot) B}\<close> and
        all_heads_in_\<N>_are_bot: \<open>(\<forall> \<C> \<in> \<N>. F_of \<C> = F_of bot)\<close> and
        \<open>A |\<inter>| B = {||}\<close> and
        \<open>A \<noteq> {||}\<close>
        by blast+
      consider \<open>\<C> = AF.Pair (F_of \<C>') B\<close> | \<open>\<C> \<in> \<N>\<close>
        using \<C>_is_consq_of_\<iota> trim(1) by auto
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          using trim_sound[OF trim(2)] trim(1) by fastforce
      next
        case 2
        then show ?thesis
          using trim(1) by (metis base_calculus.sc.sound_cons.entails_reflexive 
              base_calculus.sc.sound_cons.entails_subsets empty_subsetI insertI2 insert_subset
              simplification.sel(1) subset_singleton_iff)
      qed
    next
      case other
      show ?thesis
        using base_calculus.simps_sound[OF other] \<C>_is_consq_of_\<iota> by auto
    qed
  qed
qed

(* Report theorem 19 for Trim *)
theorem simps_with_trim_are_simps: 
  \<open>\<iota> \<in> Simps_with_Trim \<Longrightarrow> (S_from \<iota> - S_to \<iota>) \<subseteq> SRed\<^sub>F (S_to \<iota>)\<close>
proof
  fix \<C>
  assume \<open>\<iota> \<in> Simps_with_Trim\<close> and
    C_in: \<open>\<C> \<in> S_from \<iota> - S_to \<iota>\<close>
  then show \<open>\<C> \<in> SRed\<^sub>F (S_to \<iota>)\<close>
  proof (cases rule: Simps_with_Trim.cases)
    case (trim \<C>' A B \<M>)
    then have \<open>\<C>' = \<C>\<close> using C_in by auto
    then show ?thesis
      using trim_redundant[OF trim(2)] trim(1) by simp
  next
    case other
    then show ?thesis
      using base_calculus.simps_simp C_in by auto
  qed
qed

sublocale AF_calc_ext: AF_calculus_extended bot SInf entails entails_sound SRed\<^sub>I SRed\<^sub>F
  Simps_with_Trim OptInfs
  using simps_with_trim_are_simps SInf_with_trim_sound_wrt_entails_sound (*no_infinite_simp_set*)
    base_calculus.infs_sound by (unfold_locales, auto)

end (* locale AF_calculus_with_trim *)

context splitting_calculus
begin

lemma trim_sound: \<open>A_of \<C>' = A |\<union>| B \<and> F_of \<C>' \<noteq> bot \<and> 
      \<N> \<union> {AF.Pair bot A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B} \<and>
      (\<forall>\<C>\<in>\<N>. F_of \<C> = bot) \<and> A |\<inter>| B = {||} \<and> A \<noteq> {||}
        \<Longrightarrow> \<C> = AF.Pair (F_of \<C>') B \<Longrightarrow> insert \<C>' \<N> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
proof clarsimp
  assume A_of_Cp: \<open>A_of \<C>' = A |\<union>| B\<close> and
    F_of_Cp: \<open>F_of \<C>' \<noteq> bot\<close> and
    A_in_N_entails_B: \<open>AF.Pair bot A \<triangleright> \<N> \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B}\<close> and
    all_heads_in_\<N>_are_bot: \<open>(\<forall> \<C> \<in> \<N>. F_of \<C> = bot)\<close> and
    A_int_B: \<open>A |\<inter>| B = {||}\<close> and
    A_neq: \<open>A \<noteq> {||}\<close>
  have \<N>_and_Pair_bot_A_entails_Pair_bot_B: \<open>\<N> \<union> {AF.Pair bot A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B}\<close>
    using A_in_N_entails_B by auto
  let ?\<C> = \<open>AF.Pair (F_of \<C>') B\<close>
  have neg_entails_version:
    \<open>core.enabled  ?\<C> J \<Longrightarrow>
           core.fml_ext ` total_strip J \<union> Pos ` (insert (AF.Pair (F_of \<C>') A) \<N> proj\<^sub>J J)
             \<Turnstile>s\<^sub>\<sim> {Pos (F_of ?\<C>)}\<close>
    for J
  proof -
    fix J
    assume \<open>core.enabled ?\<C> J\<close>
    then have B_in_J: \<open>fset B \<subseteq> total_strip J\<close>
      by (simp add: core.enabled_def)
    then consider (fml_unsat) \<open>core.sound_cons.entails_neg (core.fml_ext ` total_strip J) {Pos bot}\<close> |
      (\<N>_unsat) \<open>\<exists> A' \<in> A_of ` \<N>. fset A' \<subseteq> total_strip J\<close> |
      (A_subset_J) \<open>fset A \<subseteq> total_strip J\<close>
      using core.strong_entails_bot_cases[OF \<N>_and_Pair_bot_A_entails_Pair_bot_B, rule_format,
          OF B_in_J]
        core.strong_entails_bot_cases_Union[rule_format, OF _ _ B_in_J]
      by (smt (verit, ccfv_SIG) Un_commute core.enabled_def core.enabled_projection_def equals0I
          image_iff mem_Collect_eq sup_bot_left)
    then show
      \<open>core.fml_ext ` total_strip J \<union> Pos ` (insert (AF.Pair (F_of \<C>') A) \<N> proj\<^sub>J J)
               \<Turnstile>s\<^sub>\<sim> {Pos (F_of ?\<C>)}\<close>
    proof cases
      case fml_unsat
      then have \<open>(core.fml_ext ` total_strip J) \<Turnstile>s\<^sub>\<sim> {Pos bot, Pos (F_of \<C>')}\<close>
        by (smt (verit, best) Un_absorb consequence_relation.entails_subsets insert_is_Un
            core.sound_cons.ext_cons_rel sup_ge1)
      moreover have \<open>((core.fml_ext ` total_strip J) \<union> {Pos bot}) \<Turnstile>s\<^sub>\<sim> {Pos (F_of \<C>')}\<close>
        by (smt (verit, del_insts) Un_commute Un_upper2 empty_subsetI insert_subset
            mem_Collect_eq core.sound_cons.bot_entails_empty core.sound_cons.entails_neg_def
            core.sound_cons.entails_subsets)
      ultimately have \<open>(core.fml_ext ` total_strip J) \<Turnstile>s\<^sub>\<sim> {Pos (F_of \<C>')}\<close>
        using consequence_relation.entails_cut core.sound_cons.ext_cons_rel
        by fastforce
      then show ?thesis
        by (smt (verit, best) AF.sel(1) consequence_relation.entails_subsets
            insert_is_Un core.sound_cons.ext_cons_rel sup_ge1)
    next
      case \<N>_unsat
      then have \<open>bot \<in> \<N> proj\<^sub>J J\<close>
        unfolding core.enabled_projection_def core.enabled_def
        using all_heads_in_\<N>_are_bot by fastforce
      then have \<open>(Pos ` (\<N> proj\<^sub>J J)) \<Turnstile>s\<^sub>\<sim> {}\<close>
        by (smt (verit, del_insts) consequence_relation.bot_entails_empty
            consequence_relation.entails_subsets image_insert insert_is_Un mk_disjoint_insert
            core.sound_cons.ext_cons_rel sup_bot_right sup_ge1)
      then show ?thesis
        by (smt (verit, ccfv_threshold) Un_upper2 consequence_relation.entails_subsets
            core.distrib_proj image_Un insert_is_Un core.sound_cons.ext_cons_rel sup_assoc)
    next
      case A_subset_J
      then have pair_bot_A_enabled: \<open>core.enabled (AF.Pair bot A) J\<close>
        by (simp add: core.enabled_def)
      then have \<open>{Pos (F_of \<C>')} \<Turnstile>s\<^sub>\<sim> {Pos (F_of \<C>')}\<close>
        by (meson consequence_relation.entails_reflexive core.sound_cons.ext_cons_rel)
      then have \<open>(Pos ` ({AF.Pair (F_of \<C>') A} proj\<^sub>J J)) \<Turnstile>s\<^sub>\<sim> {Pos (F_of \<C>')}\<close>
        using pair_bot_A_enabled  core.enabled_def core.enabled_projection_def
        by force
      then show ?thesis
        by (smt (verit, ccfv_threshold) AF.sel(1) Un_commute Un_upper2
            consequence_relation.entails_subsets core.distrib_proj image_Un insert_is_Un
            core.sound_cons.ext_cons_rel)
    qed
  qed
  have trim_assms: \<open>A_of \<C>' = A |\<union>| B \<and> F_of \<C>' \<noteq> bot \<and> \<N> \<union> {AF.Pair bot A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B} \<and>
   (\<forall>\<C>\<in>\<N>. F_of \<C> = bot) \<and> A |\<inter>| B = {||} \<and> A \<noteq> {||}\<close>
    using A_of_Cp F_of_Cp \<N>_and_Pair_bot_A_entails_Pair_bot_B all_heads_in_\<N>_are_bot A_int_B A_neq
    by blast
  show \<open>\<C>' \<triangleright> \<N> \<Turnstile>s\<^sub>A\<^sub>F {?\<C>}\<close>
    unfolding core.AF_entails_sound_def core.enabled_set_def
    by (smt (verit, ccfv_threshold) AF.collapse AF.sel(2) A_of_Cp core.distrib_proj core.enabled_def
        core.projection_of_enabled_subset image_empty image_insert insertCI insert_is_Un 
        neg_entails_version)
qed

(* part of Report theorem 19 for Trim *)
theorem trim_redundant: \<open>A_of \<C> = A |\<union>| B \<and>
       F_of \<C> \<noteq> bot \<and>
       \<M> \<union> {AF.Pair bot A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B} \<and>
       (\<forall>\<C>\<in>\<M>. F_of \<C> = bot) \<and> A |\<inter>| B = {||} \<and> A \<noteq> {||} \<Longrightarrow>
 \<C> \<in> core.SRed\<^sub>F (\<M> \<union> { AF.Pair (F_of \<C>) B })\<close>
proof clarsimp
  assume  A_of_\<C>_is: \<open>A_of \<C> = A |\<union>| B\<close> and
            \<open>F_of \<C> \<noteq> bot\<close> and
            \<M>_and_A_entail_bot_B: \<open>AF.Pair bot A \<triangleright> \<M> \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B}\<close> and
            \<open>\<forall>\<C> \<in> \<M>. F_of \<C> = bot\<close> and
            A_B_disjoint: \<open>A |\<inter>| B = {||}\<close> and
            A_not_empty: \<open>A \<noteq> {||}\<close>
  then have \<open>\<exists> \<C>' \<in> \<M> \<union> {AF.Pair (F_of \<C>) B}. (F_of \<C>' = F_of \<C> \<and> A_of \<C>' |\<subset>| A_of \<C>)\<close>
    by auto
  then show \<open>\<C> \<in> core.SRed\<^sub>F (AF.Pair (F_of \<C>) B \<triangleright> \<M>)\<close>
    unfolding core.SRed\<^sub>F_def
    by (smt (verit, del_insts) AF.collapse CollectI Un_iff insert_iff singletonD)
qed

lemma extend_simps_with_trim: 
  assumes
    \<open>AF_calculus_extended (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I 
      core.SRed\<^sub>F Simps OptInfs\<close>
  shows
    \<open>AF_calculus_with_trim (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I core.SRed\<^sub>F Simps OptInfs\<close>
proof -
  interpret sound_simps: 
    AF_calculus_extended "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I 
      core.SRed\<^sub>F Simps OptInfs
    using assms .
  show ?thesis
  proof
    fix \<C> A B \<M>
    assume \<open>A_of \<C> = A |\<union>| B \<and>
       F_of \<C> \<noteq> F_of (to_AF bot) \<and>
       \<M> \<union> {AF.Pair (F_of (to_AF bot)) A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair (F_of (to_AF bot)) B} \<and>
       (\<forall>\<C>\<in>\<M>. F_of \<C> = F_of (to_AF bot)) \<and> A |\<inter>| B = {||} \<and> A \<noteq> {||}\<close>
    then show \<open>\<C> \<triangleright> \<M> \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair (F_of \<C>) B}\<close>
      using trim_sound F_of_to_AF by metis
  next
    fix \<C> A B \<M>
    assume \<open>A_of \<C> = A |\<union>| B \<and>
       F_of \<C> \<noteq> F_of (to_AF bot) \<and>
       \<M> \<union> {AF.Pair (F_of (to_AF bot)) A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair (F_of (to_AF bot)) B} \<and>
       (\<forall>\<C>\<in>\<M>. F_of \<C> = F_of (to_AF bot)) \<and> A |\<inter>| B = {||} \<and> A \<noteq> {||}\<close>
    then show \<open>\<C> \<in> core.SRed\<^sub>F (\<M> \<union> {AF.Pair (F_of \<C>) B})\<close>
      using trim_redundant F_of_to_AF by metis
  qed
qed

interpretation splitting_calc_with_trim:
  AF_calculus_with_trim "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I core.SRed\<^sub>F "{}" "{}"
  using extend_simps_with_trim[OF empty_simps.AF_calculus_extended_axioms] .

end (* context splitting_calculus *)


subsection \<open>Extra Inferences\<close>

text \<open>
  We extend our basic splitting calculus with new optional rules:
  \<^item> \textsc{StrongUnsat} is a variant of \textsc{Unsat} which uses the sound entailment
    instead of the "normal" entailment;
  \<^item> \textsc{Approx} is a very special case for \textsc{Split} where $n = 1$;
  \<^item> \textsc{Tauto} inserts a new formula which is always true.
\<close>

subsubsection \<open>The StrongUnsat Rule\<close>

locale AF_calculus_with_strong_unsat = 
  base: AF_calculus_extended bot SInf entails entails_sound Red_I Red_F Simps
    OptInfs
  for bot :: \<open>('f, 'v :: countable) AF\<close> and
      SInf :: \<open>('f, 'v) AF inference set\<close> and
      entails :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> and
      entails_sound :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<^sub>A\<^sub>F\<close> 50) and
      Red_I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> and
      Red_F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> and
      Simps :: \<open>('f, 'v) AF simplification set\<close> and
      OptInfs :: \<open>('f, 'v) AF inference set\<close>
begin

text \<open>
  We follow the same naming conventions for our new inference rules as for the two inference rules
  defined in @{locale annotated_calculus}.
  $X\_inf$ defines the inference rule, while $X\_pre$ is the precondition for the application of
  the inference rule.
\<close>

abbreviation strong_unsat_pre :: \<open>('f, 'v) AF list \<Rightarrow> bool\<close> where
  \<open>strong_unsat_pre \<M> \<equiv> (set \<M> \<Turnstile>s\<^sub>A\<^sub>F {bot}) \<and> (\<forall> x \<in> set \<M>. F_of x = (F_of bot))\<close>

abbreviation strong_unsat_inf :: \<open>('f, 'v) AF list \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>strong_unsat_inf \<M> \<equiv> Infer \<M> bot\<close>

text \<open>Instead of considering an inference system with only the new rule, here \textsc{StrongUnsat},
  we instead add it to the inference system provided so that it is possible to extend the system 
  rule by rule in a modular way.\<close> 
  
(* Report definition 9 (cont) *)
inductive_set OptInfs_with_strong_unsat :: \<open>('f, 'v) AF inference set\<close> where
  strong_unsat: \<open>strong_unsat_pre \<M> \<Longrightarrow> strong_unsat_inf \<M> \<in> OptInfs_with_strong_unsat\<close>
| from_OptInf: \<open>\<iota> \<in> OptInfs \<Longrightarrow> \<iota> \<in> OptInfs_with_strong_unsat\<close>

(* Report theorem 14 for StrongUnsat *)
theorem OptInf_with_strong_unsat_sound_wrt_entails_sound: 
  \<open>\<iota> \<in> OptInfs_with_strong_unsat \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>}\<close>
proof -
  assume \<open>\<iota> \<in> OptInfs_with_strong_unsat\<close>
  then show ?thesis
  proof (cases \<iota> rule: OptInfs_with_strong_unsat.cases)
    case (strong_unsat \<M>)
    then show ?thesis
      by simp
  next
    case from_OptInf
    then show ?thesis
      using base.infs_sound by blast 
  qed
qed

interpretation AF_sound_cons_rel: consequence_relation bot \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  using base.sc.sound_cons.consequence_relation_axioms .

interpretation SInf_sound_inf_system: sound_inference_system SInf bot \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  using base.sc.sound_inference_system_axioms .

definition Red_I_ext where
  \<open>Red_I_ext \<N> = Red_I \<N> \<union> { strong_unsat_inf \<M> | \<M>. strong_unsat_pre \<M> \<and> bot \<in> \<N> }\<close>

interpretation AF_calc_with_strong_unsat: 
  AF_calculus bot SInf entails entails_sound Red_I Red_F
  using base.AF_calculus_axioms .

sublocale AF_calc_ext: AF_calculus_extended bot SInf entails entails_sound Red_I Red_F
  Simps OptInfs_with_strong_unsat
  using base.simps_simp base.simps_sound (*base.no_infinite_simps *)
OptInf_with_strong_unsat_sound_wrt_entails_sound
  by (unfold_locales, auto)

end (* locale AF_calculus_with_strong_unsat *)

context splitting_calculus
begin

lemma extend_infs_with_strong_unsat: 
  assumes
    \<open>AF_calculus_extended (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I 
      core.SRed\<^sub>F Simps OptInfs\<close>
  shows
    \<open>AF_calculus_with_strong_unsat (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I core.SRed\<^sub>F Simps 
      OptInfs\<close>
  using AF_calculus_with_strong_unsat.intro assms by blast

interpretation splitting_calc_with_strong_unsat: AF_calculus_with_strong_unsat "to_AF bot" core.SInf
  "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I core.SRed\<^sub>F "{}" "{}"
  using 
    extend_infs_with_strong_unsat[OF empty_simps.AF_calculus_extended_axioms] .

end (* context splitting_calculus *)

subsubsection \<open>The Tauto Rule\<close>

locale AF_calculus_with_tauto = 
  base: AF_calculus_extended bot SInf entails entails_sound Red_I Red_F Simps
  OptInfs
  for bot :: \<open>('f, 'v :: countable) AF\<close> and
      SInf :: \<open>('f, 'v) AF inference set\<close> and
      entails :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> and
      entails_sound :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<^sub>A\<^sub>F\<close> 50) and
      Red_I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> and
      Red_F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> and
      Simps :: \<open>('f, 'v) AF simplification set\<close> and
      OptInfs :: \<open>('f, 'v) AF inference set\<close>
begin

abbreviation tauto_pre :: \<open>('f, 'v) AF \<Rightarrow> bool\<close> where
  \<open>tauto_pre \<C> \<equiv> {} \<Turnstile>s\<^sub>A\<^sub>F { \<C> }\<close>

abbreviation tauto_inf :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>tauto_inf \<C> \<equiv> Infer [] \<C>\<close>

(* Report definition 9 (cont) *)
inductive_set OptInfs_with_tauto :: \<open>('f, 'v) AF inference set\<close> where
  tauto: \<open>tauto_pre \<C> \<Longrightarrow> tauto_inf \<C> \<in> OptInfs_with_tauto\<close>
| from_OptInfs: \<open>\<iota> \<in> OptInfs \<Longrightarrow> \<iota> \<in> OptInfs_with_tauto\<close> 

(* Report theorem 14 for Tauto *)
theorem OptInfs_with_tauto_sound_wrt_entails_sound: \<open>\<iota> \<in> OptInfs_with_tauto \<Longrightarrow> 
  set (prems_of \<iota>) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>}\<close>
proof -
  assume \<open>\<iota> \<in> OptInfs_with_tauto\<close>
  then show ?thesis
  proof (cases \<iota> rule: OptInfs_with_tauto.cases)
    case (tauto \<C>)
    then show ?thesis
      by auto
  next
    case from_OptInfs
    then show ?thesis
      using base.infs_sound by blast
  qed
qed

sublocale AF_calc_ext: AF_calculus_extended bot SInf entails "(\<Turnstile>s\<^sub>A\<^sub>F)" Red_I 
  Red_F Simps OptInfs_with_tauto
  using OptInfs_with_tauto_sound_wrt_entails_sound base.simps_sound base.simps_simp 
   (* base.no_infinite_simps *)
  by (unfold_locales, auto)

end (* locale AF_calculus_with_tauto *)

context splitting_calculus
begin


lemma extend_infs_with_tauto: 
  assumes
    \<open>AF_calculus_extended (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I 
      core.SRed\<^sub>F Simps OptInfs\<close>
  shows
    \<open>AF_calculus_with_tauto (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I core.SRed\<^sub>F Simps OptInfs\<close>
  using AF_calculus_with_tauto.intro assms by blast


interpretation splitting_calc_with_tauto:
  AF_calculus_with_tauto "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I core.SRed\<^sub>F "{}" "{}"
  using extend_infs_with_tauto[OF empty_simps.AF_calculus_extended_axioms] .

end (* context splitting_calculus *)

subsubsection \<open>The Approx Rule\<close>

locale AF_calculus_with_approx = 
  base: AF_calculus_extended bot SInf entails entails_sound Red_I Red_F Simps
    OptInfs
  for bot :: \<open>('f, 'v :: countable) AF\<close> and
      SInf :: \<open>('f, 'v) AF inference set\<close> and
      entails :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> and
      entails_sound :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<^sub>A\<^sub>F\<close> 50) and
      Red_I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> and
      Red_F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> and
      Simps :: \<open>('f, 'v) AF simplification set\<close> and
      OptInfs :: \<open>('f, 'v) AF inference set\<close>
  + fixes
      approximates :: \<open>'v sign \<Rightarrow> ('f, 'v) AF \<Rightarrow> bool\<close>
    assumes
      approx_sound: \<open>approximates a \<C> \<Longrightarrow> {\<C>} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair (F_of bot) (finsert (neg a) (A_of \<C>))}\<close>
begin

abbreviation approx_pre :: \<open>'v sign \<Rightarrow> ('f, 'v) AF \<Rightarrow> bool\<close> where
  \<open>approx_pre a \<C> \<equiv> approximates a \<C>\<close>

abbreviation approx_inf :: \<open>('f, 'v) AF \<Rightarrow> 'v sign \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>approx_inf \<C> a \<equiv> Infer [\<C>] (AF.Pair (F_of bot) (finsert (neg a) (A_of \<C>)))\<close>
  
(* Report definition 9 (cont) *)
inductive_set OptInfs_with_approx :: \<open>('f, 'v) AF inference set\<close> where
  approx: \<open>approx_pre a \<C> \<Longrightarrow> approx_inf \<C> a \<in> OptInfs_with_approx\<close>
| from_OptInfs: \<open>\<iota> \<in> OptInfs \<Longrightarrow> \<iota> \<in> OptInfs_with_approx\<close> 

(* Report theorem 14 for Approx *)
theorem OptInfs_with_approx_sound_wrt_entails_sound:
  \<open>\<iota> \<in> OptInfs_with_approx \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>}\<close>
proof -
  assume \<open>\<iota> \<in> OptInfs_with_approx\<close>
  then show ?thesis
  proof (cases \<iota> rule: OptInfs_with_approx.cases)
    case (approx a \<C>)
    show ?thesis
      using approx_sound[OF approx(2)] approx(1) by simp
  next
    case from_OptInfs
    show ?thesis
      using base.infs_sound[OF from_OptInfs] .
  qed
qed

sublocale AF_calc_ext: AF_calculus_extended bot SInf entails "(\<Turnstile>s\<^sub>A\<^sub>F)" Red_I Red_F Simps
  OptInfs_with_approx
  using OptInfs_with_approx_sound_wrt_entails_sound base.simps_sound base.simps_simp 
    (* base.no_infinite_simps*)
  by (unfold_locales, auto)

end (* locale AF_calculus_with_approx *)

context splitting_calculus
begin

definition approximates :: \<open>'v sign \<Rightarrow> ('f, 'v) AF \<Rightarrow> bool\<close> where
  \<open>approximates a \<C> \<equiv> a \<in> asn (Pos (F_of \<C>))\<close>

lemma approx_sound: \<open>approximates a \<C> \<Longrightarrow> {\<C>} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot (finsert (neg a) (A_of \<C>))}\<close>
proof -
  assume approx_a_C: \<open>approximates a \<C>\<close>
  then have
    \<open>core.enabled (AF.Pair bot (finsert (neg a) (A_of \<C>))) J \<Longrightarrow>
       (core.fml_ext ` total_strip J) \<union> {Pos (F_of \<C>)} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
    for J 
  proof -
    fix J
    assume \<open>core.enabled (AF.Pair bot (finsert (neg a) (A_of \<C>))) J\<close>
    then have \<open>fset (finsert (neg a) (A_of \<C>)) \<subseteq> total_strip J\<close>
      unfolding core.enabled_def
      by simp
    then have neg_fml_ext_in_J: \<open>neg (core.fml_ext a) \<in> core.fml_ext ` total_strip J\<close>
      by (smt (verit, ccfv_threshold) finsert.rep_eq core.fml_ext.elims core.fml_ext.simps(1)
          core.fml_ext.simps(2) image_iff insert_subset neg.simps(1) neg.simps(2))
    moreover have \<open>{Pos (F_of \<C>)} \<Turnstile>s\<^sub>\<sim> {Pos (F_of \<C>)}\<close>
      using core.equi_entails_if_a_in_asns approx_a_C unfolding approximates_def
      by blast
    then have \<open>(core.fml_ext ` (total_strip J - {neg a})) \<union> {Pos (F_of \<C>)} \<Turnstile>s\<^sub>\<sim> 
        {Pos bot, Pos (F_of \<C>)}\<close>
      by (metis (no_types, lifting) consequence_relation.entails_subsets insert_is_Un
          core.sound_cons.ext_cons_rel sup.cobounded2)
    ultimately show \<open>(core.fml_ext ` total_strip J) \<union> {Pos (F_of \<C>)} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
    proof -
      have \<open>core.fml_ext ` total_strip J \<union> {core.fml_ext a} \<Turnstile>s\<^sub>\<sim> ({Pos bot} \<union> {})\<close>
        by (smt (z3) Bex_def_raw UnCI Un_commute Un_insert_right Un_upper2 neg_fml_ext_in_J
            consequence_relation.entails_subsets insert_is_Un insert_subset
            core.sound_cons.ext_cons_rel core.sound_cons.pos_neg_entails_bot)
      then show ?thesis
        using approx_a_C unfolding approximates_def
        by (smt (verit) Un_commute Un_empty_right core.C_entails_fml core.fml_ext_is_mapping 
            core.neg_ext_sound_cons_rel.entails_cut)
    qed
  qed
  then have
    \<open>core.enabled_set {AF.Pair bot (finsert (neg a) (A_of \<C>))} J \<Longrightarrow>
       core.fml_ext ` total_strip J \<union> Pos ` ({\<C>} proj\<^sub>J J) \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
    for J 
    unfolding core.enabled_projection_def core.enabled_def core.enabled_set_def
    by auto 
  then show \<open>{\<C>} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot (finsert (neg a) (A_of \<C>))}\<close>
    unfolding core.AF_entails_sound_def by auto
qed

lemma extend_infs_with_approx: 
  assumes
    \<open>AF_calculus_extended (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I core.SRed\<^sub>F Simps
      OptInfs\<close>
  shows
    \<open>AF_calculus_with_approx (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I core.SRed\<^sub>F Simps 
       OptInfs approximates\<close>
  using AF_calculus_with_approx.intro[OF assms] approx_sound
  by (simp add: AF_calculus_with_approx_axioms_def F_of_to_AF)

interpretation splitting_calc_with_approx:
  AF_calculus_with_approx "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I core.SRed\<^sub>F "{}" "{}"
    approximates
  using extend_infs_with_approx[OF empty_simps.AF_calculus_extended_axioms] .

end (* context splitting_calculus *)

subsection \<open>Combining all simplifications and optional inferences\<close>

text \<open>We have augmented the core calculus with each simplification and optional rule separately. We
  now show how to augment the core calculus with all of them in succession.\<close>
context splitting_calculus
begin

interpretation with_A: AF_calculus_with_approx "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I
  core.SRed\<^sub>F "{}" "{}" approximates
  using extend_infs_with_approx[OF empty_simps.AF_calculus_extended_axioms] .

interpretation with_AT: AF_calculus_with_tauto "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I
  core.SRed\<^sub>F "{}" with_A.OptInfs_with_approx
  using 
    extend_infs_with_tauto[OF with_A.AF_calc_ext.AF_calculus_extended_axioms] .

interpretation with_ATS: AF_calculus_with_strong_unsat "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)"
  core.SRed\<^sub>I core.SRed\<^sub>F "{}" with_AT.OptInfs_with_tauto
  using extend_infs_with_strong_unsat[OF 
      with_AT.AF_calc_ext.AF_calculus_extended_axioms] .

interpretation with_ATS_T: AF_calculus_with_trim "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I
  core.SRed\<^sub>F "{}" with_ATS.OptInfs_with_strong_unsat
  using extend_simps_with_trim[OF
    with_ATS.AF_calc_ext.AF_calculus_extended_axioms] .

interpretation with_ATS_TC: AF_calculus_with_collect "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" 
  core.SRed\<^sub>I core.SRed\<^sub>F with_ATS_T.Simps_with_Trim with_ATS.OptInfs_with_strong_unsat
  using extend_simps_with_collect[OF
    with_ATS_T.AF_calc_ext.AF_calculus_extended_axioms] .

interpretation with_all: AF_calculus_with_split "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" 
  core.SRed\<^sub>I core.SRed\<^sub>F with_ATS_TC.Simps_with_Collect with_ATS.OptInfs_with_strong_unsat splittable
  using extend_simps_with_split[OF
    with_ATS_TC.AF_calc_ext.AF_calculus_extended_axioms] .

interpretation full_splitting_calculus: AF_calculus_extended "to_AF bot" 
  core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)" "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I core.SRed\<^sub>F with_all.Simps_with_Split  
  with_ATS.OptInfs_with_strong_unsat
  using with_all.AF_calc_ext.AF_calculus_extended_axioms .

text \<open>Simplifications and optional inferences can be integrated in derivations. This is made obvious
  by the following two lemmas.\<close>

lemma simp_in_derivations: \<open>\<delta> \<in> with_all.Simps_with_Split \<Longrightarrow> 
  core.S_calculus.derive (\<M> \<union> S_from \<delta>) (\<M> \<union> S_to \<delta>)\<close>
  unfolding core.S_calculus.derive_def
proof 
  fix C
  assume d_in: \<open>\<delta> \<in> with_all.Simps_with_Split\<close> and
    \<open>C \<in> \<M> \<union> S_from \<delta> - (\<M> \<union> S_to \<delta>)\<close>
  then have \<open>C \<in> S_from \<delta> - S_to \<delta>\<close>
    by blast
  then show \<open>C \<in> core.SRed\<^sub>F (\<M> \<union> S_to \<delta>)\<close>
    using with_all.AF_calc_ext.simps_simp[OF d_in] by (meson core.annotated_calculus_axioms
        annotated_calculus.SRed\<^sub>F_of_subset_F in_mono inf_sup_ord(4))
qed

lemma opt_infs_in_derivations: \<open>\<iota> \<in> with_ATS.OptInfs_with_strong_unsat \<Longrightarrow> 
  core.S_calculus.derive (\<M> \<union> set (prems_of \<iota>)) (\<M> \<union> set (prems_of \<iota>) \<union> {concl_of \<iota>})\<close>
  unfolding core.S_calculus.derive_def
proof 
  fix C
  assume \<open>\<iota> \<in> with_ATS.OptInfs_with_strong_unsat\<close> and
    C_in: \<open>C \<in> \<M> \<union> set (prems_of \<iota>) - (\<M> \<union> set (prems_of \<iota>) \<union> {concl_of \<iota>})\<close>
  have \<open>\<M> \<union> set (prems_of \<iota>) - (\<M> \<union> set (prems_of \<iota>) \<union> {concl_of \<iota>}) = {}\<close>
    by blast
  then have False using C_in by auto
  then show \<open>C \<in> core.SRed\<^sub>F (\<M> \<union> set (prems_of \<iota>) \<union> {concl_of \<iota>})\<close>
    by auto
qed

end (* context splitting_calculus *)

subsection \<open>The BinSplit Simplification Rule\<close>

text \<open>For the sake of the Lightweight Avatar calculus, we define the \textsc{BinSplit} 
  simplification rule, and show that it is indeed a sound simplification rule as in the case of the 
  Split rule.\<close>
locale AF_calculus_with_binsplit =
  base_calculus: AF_calculus_extended bot SInf entails entails_sound SRed\<^sub>I
  SRed\<^sub>F Simps OptInfs
  for bot :: \<open>('f, 'v :: countable) AF\<close> and
      SInf :: \<open>('f, 'v) AF inference set\<close> and
      entails :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>A\<^sub>F\<close> 50) and
      entails_sound :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<^sub>A\<^sub>F\<close> 50) and
      SRed\<^sub>I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> and
      SRed\<^sub>F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> and
      Simps :: \<open>('f, 'v) AF simplification set\<close> and
      OptInfs :: \<open>('f, 'v) AF inference set\<close>
  + fixes
      bin_splittable :: \<open>('f, 'v) AF \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> bool\<close>
    assumes
      binsplit_prem_entails_cons: \<open>bin_splittable \<C> C1 C2 \<C>s \<Longrightarrow> \<forall> \<C>' \<in> fset \<C>s. {\<C>} \<Turnstile>s\<^sub>A\<^sub>F {\<C>'}\<close> and
      binsplit_simp: \<open>bin_splittable \<C> C1 C2 \<C>s \<Longrightarrow> \<C> \<in> SRed\<^sub>F (fset \<C>s)\<close>
begin

text \<open>
  We use the same naming convention as for the other rules, where
  $X\_pre$ is the condition which must hold for the rule to be applicable, $X\_res$ is its
  resultant and $X\_simp$ is the simplification rule itself.
\<close>

abbreviation bin_split_pre :: \<open>('f, 'v) AF \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> bool\<close> where
  \<open>bin_split_pre \<C> C1 C2 \<C>s \<equiv> bin_splittable \<C> C1 C2 \<C>s\<close>

abbreviation bin_split_res :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> ('f, 'v) AF set\<close> where
  \<open>bin_split_res \<C> \<C>s \<equiv> fset \<C>s\<close>

abbreviation bin_split_simp :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> ('f, 'v) AF simplification\<close> where
  \<open>bin_split_simp \<C> \<C>s \<equiv> Simplify {\<C>} (bin_split_res \<C> \<C>s)\<close>

inductive_set Simps_with_BinSplit :: \<open>('f, 'v) AF simplification set\<close> where
  binsplit: \<open>bin_split_pre \<C> C1 C2 \<C>s \<Longrightarrow> bin_split_simp \<C> \<C>s \<in> Simps_with_BinSplit\<close> 
| other: \<open>simp \<in> Simps \<Longrightarrow> simp \<in> Simps_with_BinSplit\<close>

(*
lemma no_infinite_simps: \<open>finite (S_from \<iota>) \<Longrightarrow> \<iota> \<in> Simps_with_BinSplit \<Longrightarrow> finite (S_to \<iota>)\<close>
  using Simps_with_BinSplit.cases base_calculus.no_infinite_simps
  by force
*)

(* Report theorem 14 for Simps extended with BinSplit *)
theorem SInf_with_binsplit_sound_wrt_entails_sound:
  \<open>\<iota> \<in> Simps_with_BinSplit \<Longrightarrow> \<forall> \<C> \<in> S_to \<iota>. S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
proof -
  assume \<iota>_is_simp_rule: \<open>\<iota> \<in> Simps_with_BinSplit\<close>
  then show \<open>\<forall> \<C> \<in> S_to \<iota>. S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
  proof (intro ballI)
    fix \<C>
    assume \<C>_is_consq_of_\<iota>: \<open>\<C> \<in> S_to \<iota>\<close>
    show \<open>S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
      using \<iota>_is_simp_rule
    proof (cases rule: Simps_with_BinSplit.cases)
      case (binsplit \<C>' C1 C2 \<C>s)
      then have \<open>\<forall>\<C>' \<in> fset \<C>s. S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>'}\<close>
        using binsplit_prem_entails_cons by auto
      then show ?thesis
        using \<C>_is_consq_of_\<iota> binsplit unfolding S_to_def by auto
    next
      case other
      then show ?thesis
        using \<C>_is_consq_of_\<iota> base_calculus.simps_sound by auto
    qed
  qed
qed

(* Report theorem 19 for BinSplit *)
lemma binsplit_redundant: \<open>bin_split_pre \<C> C1 C2 \<C>s \<Longrightarrow> \<C> \<in> SRed\<^sub>F (bin_split_res \<C> \<C>s)\<close>
proof -
  assume pre_cond: \<open>bin_split_pre \<C> C1 C2 \<C>s\<close>
  then show \<open>\<C> \<in> SRed\<^sub>F (bin_split_res \<C> \<C>s)\<close>
    using binsplit_simp by simp
qed

(* Report theorem 19 for Simps extended with Split *)
lemma simps_with_binsplit_are_simps: 
  \<open>\<iota> \<in> Simps_with_BinSplit \<Longrightarrow> (S_from \<iota> - S_to \<iota>) \<subseteq> SRed\<^sub>F (S_to \<iota>)\<close>
proof
  fix \<C>
  assume i_in: \<open>\<iota> \<in> Simps_with_BinSplit\<close> and
    C_in: \<open>\<C> \<in> S_from \<iota> - S_to \<iota>\<close>
  then show \<open>\<C> \<in> SRed\<^sub>F (S_to \<iota>)\<close>
  proof (cases rule: Simps_with_BinSplit.cases)
    case (binsplit \<C>' C1 C2 \<C>s)
    then have \<open>\<C> = \<C>'\<close> using C_in by auto
    moreover have \<open>S_to \<iota> = bin_split_res \<C>' \<C>s\<close> using binsplit(1) simplification.sel(2) by auto
    ultimately show ?thesis
      using binsplit_redundant[OF binsplit(2)] by presburger
  next
    case other
    then show ?thesis
      using base_calculus.simps_simp C_in by blast
  qed
qed

sublocale AF_calc_ext: AF_calculus_extended bot SInf entails entails_sound 
  SRed\<^sub>I SRed\<^sub>F Simps_with_BinSplit OptInfs
  using simps_with_binsplit_are_simps SInf_with_binsplit_sound_wrt_entails_sound (*no_infinite_simps*)
  base_calculus.infs_sound  by (unfold_locales, auto)

end (* AF_calculus_with_binsplit *)

context splitting_calculus
begin

definition mk_bin_split :: \<open>('f, 'v) AF \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> ('f, 'v) AF fset\<close> where
  \<open>split_form (F_of \<C>) {|C1, C2|} \<Longrightarrow> mk_bin_split \<C> C1 C2 \<equiv> 
    let a = (SOME a. a \<in> asn (sign.Pos C1))
    in {|AF.Pair C1 (finsert a (A_of \<C>)), AF.Pair C2 (finsert (neg a) (A_of \<C>))|}\<close> 

definition bin_splittable :: \<open>('f, 'v) AF \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> bool\<close> where
  \<open>bin_splittable \<C> C1 C2 \<C>s \<equiv> split_form (F_of \<C>) {|C1, C2|} \<and> mk_bin_split \<C> C1 C2 = \<C>s\<close>

theorem binsplit_prem_entails_cons: \<open>bin_splittable \<C> C1 C2 \<C>s \<Longrightarrow> \<forall> \<C>' \<in> fset \<C>s. {\<C>} \<Turnstile>s\<^sub>A\<^sub>F {\<C>'}\<close>
proof (intro ballI)
  fix \<C>'
  assume C_u_D_splittable: \<open>bin_splittable \<C> C1 C2 \<C>s\<close> and
    \<C>'_in: \<open>\<C>' |\<in>| \<C>s\<close>
  then have split_fm: \<open>split_form (F_of \<C>) {|C1, C2|}\<close> and
    make_split: \<open>mk_bin_split \<C> C1 C2 = \<C>s\<close>
    unfolding bin_splittable_def by blast+
  have \<open>\<C>' \<in> (let a = SOME a. a \<in> asn (sign.Pos C1)
        in {AF.Pair C1 (finsert a (A_of \<C>)), AF.Pair C2 (finsert (neg a) (A_of \<C>))})\<close>
    using make_split mk_bin_split_def[OF split_fm] \<C>'_in by (metis bot_fset.rep_eq fset_simps(2))
  then obtain a where
    a_in_asn_pos_C1: \<open>a \<in> asn (sign.Pos C1)\<close> and
    \<C>'_is: \<open>\<C>' = AF.Pair C1 (finsert a (A_of \<C>)) \<or> \<C>' = AF.Pair C2 (finsert (neg a) (A_of \<C>))\<close>
    using core.asn_not_empty insert_iff singletonD some_in_eq by metis
  consider (C1) \<open>\<C>' = AF.Pair C1 (finsert a (A_of \<C>))\<close> 
    | (C2) \<open>\<C>' = AF.Pair C2 (finsert (neg a) (A_of \<C>))\<close>
    using \<C>'_is by blast
  then show \<open>{\<C>} \<Turnstile>s\<^sub>A\<^sub>F {\<C>'}\<close>
    unfolding core.AF_entails_sound_def core.enabled_set_def core.enabled_def
  proof (cases, clarsimp)
    case C1
    fix J
    assume \<open>\<C>' = AF.Pair C1 (finsert a (A_of \<C>))\<close>
      and \<open>a \<in> total_strip J\<close>
      and \<open>fset (A_of \<C>) \<subseteq> total_strip J\<close>
    then show \<open>core.fml_ext ` total_strip J \<union> sign.Pos ` ({\<C>} proj\<^sub>J J) \<Turnstile>s\<^sub>\<sim> {sign.Pos C1}\<close>
      using a_in_asn_pos_C1 by (smt (verit, best) core.fml_entails_C core.fml_ext_is_mapping 
          core.neg_ext_sound_cons_rel.entails_subsets image_eqI singletonD subsetI sup_ge1)
  next
    case C2
    then show \<open>\<forall>J. (\<forall>\<C>\<in>{\<C>'}. fset (A_of \<C>) \<subseteq> total_strip J) \<longrightarrow> 
      core.fml_ext ` total_strip J \<union> sign.Pos ` ({\<C>} proj\<^sub>J J) \<Turnstile>s\<^sub>\<sim> sign.Pos ` F_of ` {\<C>'}\<close>
    proof clarsimp
      fix J
      assume \<C>'_is_C2: \<open>\<C>' = AF.Pair C2 (finsert (neg a) (A_of \<C>))\<close>
        and a_notin: \<open>a \<notin> total_strip J\<close>
        and in_J: \<open>fset (A_of \<C>) \<subseteq> total_strip J\<close>
      have \<open>{F_of \<C>} \<Turnstile>s fset {|C1, C2|}\<close>
        using split_fm unfolding split_form_def by blast
      then have \<open>{sign.Neg C1} \<union> {sign.Pos (F_of \<C>)} \<Turnstile>s\<^sub>\<sim> {sign.Pos C2}\<close>
        unfolding core.sound_cons.entails_neg_def by simp
      moreover have neg_fml_a_in: \<open>neg (map_sign fml a) \<in> core.fml_ext ` total_strip J\<close>
        using a_notin by (smt (z3) core.fml_ext.elims core.fml_ext.simps(1) core.fml_ext.simps(2) 
            core.fml_ext_is_mapping image_iff neg.simps(1) neg.simps(2) neg_in_total_strip)
      ultimately have neg_fml_a_in_entails: 
        \<open>{neg (map_sign fml a)} \<union> {sign.Pos (F_of \<C>)} \<Turnstile>s\<^sub>\<sim> {sign.Pos C2}\<close>
        using core.fml_entails_C core.C_entails_fml 
        by (metis a_in_asn_pos_C1 consequence_relation.swap_neg_in_entails_neg 
            core.neg_ext_sound_cons_rel.entails_cut core.sound_cons.consequence_relation_axioms 
            insert_is_Un neg.simps(1) sup_commute)
      have \<open>core.fml_ext ` total_strip J \<union> {sign.Pos (F_of \<C>)} \<Turnstile>s\<^sub>\<sim> {sign.Pos C2}\<close>
      proof -
        have f1: "\<forall>S. neg (map_sign fml a) \<triangleright> S \<subseteq> S \<union> core.fml_ext ` total_strip J"
          using neg_fml_a_in by blast
        have "\<forall>S s Sa. (s::'f sign) \<triangleright> Sa \<subseteq> Sa \<union> (s \<triangleright> S)"
          by force
        then show ?thesis
          using f1 
          by (metis (no_types) neg_fml_a_in_entails 
              core.neg_ext_sound_cons_rel.entails_subsets insert_is_Un sup_ge1)
      qed
      moreover have \<open>{\<C>} proj\<^sub>J J = {(F_of \<C>)}\<close>
        using in_J unfolding core.enabled_projection_def core.enabled_def by blast
      ultimately show \<open>core.fml_ext ` total_strip J \<union> sign.Pos ` ({\<C>} proj\<^sub>J J) \<Turnstile>s\<^sub>\<sim> {sign.Pos C2}\<close>
        by simp
    qed   
  qed
qed

theorem binsplit_simp: \<open>bin_splittable \<C> C1 C2 \<C>s \<Longrightarrow> \<C> \<in> core.SRed\<^sub>F (fset \<C>s)\<close>
proof -
  assume \<open>bin_splittable \<C> C1 C2 \<C>s\<close>
  then have split_fm: \<open>split_form (F_of \<C>) {|C1, C2|}\<close> and
    make_split: \<open>mk_bin_split \<C> C1 C2 = \<C>s\<close>
    unfolding bin_splittable_def by blast+
  have F_entailment: \<open>{F_of \<C>} \<Turnstile>s fset {|C1, C2|}\<close>
    using split_fm unfolding split_form_def by blast
  have C_D_make_C_u_D_redundant: \<open>\<forall>C'. C' |\<in>| {|C1, C2|} \<longrightarrow> F_of \<C> \<in> Red\<^sub>F {C'}\<close>
    by (meson split_fm split_form_def)
  have a_ex: \<open>\<exists> a \<in> asn (sign.Pos C1). 
      fset \<C>s = {AF.Pair C1 (finsert a (A_of \<C>)), AF.Pair C2 (finsert (neg a) (A_of \<C>))}\<close>
    by (metis mk_bin_split_def[OF split_fm] bot_fset.rep_eq core.asn_not_empty finsert.rep_eq
        make_split some_in_eq)
  then obtain a where a_in: \<open>a \<in> asn (sign.Pos C1)\<close> and 
    \<C>s_is: \<open>fset \<C>s = {AF.Pair C1 (finsert a (A_of \<C>)), AF.Pair C2 (finsert (neg a) (A_of \<C>))}\<close>
    by blast
  show \<open>\<C> \<in> core.SRed\<^sub>F (fset \<C>s)\<close>
  proof -
    have \<open>\<forall>\<J>. fset (A_of \<C>) \<subseteq> total_strip \<J> \<longrightarrow> (F_of \<C>) \<in> Red\<^sub>F ((fset \<C>s) proj\<^sub>J \<J>)\<close>
    proof (intro allI impI)
      fix \<J>
      assume A_in_\<J>: \<open>fset (A_of \<C>) \<subseteq> total_strip \<J>\<close>
            then have a_or_neg_a_in_\<J>: \<open>a \<in> total_strip \<J> \<or> neg a \<in> total_strip \<J>\<close>
        by simp
      then have a_or_neg_a_in_\<J>: \<open>fset (finsert a (A_of \<C>)) \<subseteq> total_strip \<J> \<or>
          fset (finsert (neg a) (A_of \<C>)) \<subseteq> total_strip \<J>\<close>
        by (simp add: A_in_\<J>)
      have \<open>(fset \<C>s) proj\<^sub>J \<J> \<subseteq> {C1, C2}\<close>
        using \<C>s_is core.enabled_projection_def
        by auto
      moreover have \<open>(fset \<C>s) proj\<^sub>J \<J> \<noteq> {}\<close>
        unfolding core.enabled_projection_def using a_or_neg_a_in_\<J> \<C>s_is
        by (metis (mono_tags, lifting) AF.sel(2) core.enabled_def empty_iff insertCI mem_Collect_eq) 
      ultimately show \<open>(F_of \<C>) \<in> Red\<^sub>F ((fset \<C>s) proj\<^sub>J \<J>)\<close>
        using C_D_make_C_u_D_redundant
        by (smt (verit, del_insts) core.Red_F_of_subset all_not_in_conv empty_subsetI
            finsertCI insert_iff insert_subset subsetD)
    qed
    then show ?thesis
      unfolding core.SRed\<^sub>F_def by (smt (verit, ccfv_threshold) AF.collapse UnCI mem_Collect_eq)
  qed
qed

lemma extend_simps_with_binsplit: 
  assumes
    \<open>AF_calculus_extended (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I 
      core.SRed\<^sub>F Simps OptInfs\<close>
  shows
    \<open>AF_calculus_with_binsplit (to_AF bot) core.SInf (\<Turnstile>\<^sub>A\<^sub>F) (\<Turnstile>s\<^sub>A\<^sub>F) core.SRed\<^sub>I core.SRed\<^sub>F Simps 
      OptInfs bin_splittable\<close>
proof -
  interpret sound_simps: AF_calculus_extended "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)"
    "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I core.SRed\<^sub>F Simps OptInfs
    using assms .
  show ?thesis
  proof
    show \<open>bin_splittable \<C> C1 C2 \<C>s \<Longrightarrow> \<forall>\<C>'|\<in>|\<C>s. {\<C>} \<Turnstile>s\<^sub>A\<^sub>F {\<C>'}\<close> for \<C> C1 C2 \<C>s
      using binsplit_prem_entails_cons .
  next
    show \<open>bin_splittable \<C> C1 C2 \<C>s \<Longrightarrow> \<C> \<in> core.SRed\<^sub>F (fset \<C>s)\<close> for \<C> C1 C2 \<C>s
      using binsplit_simp .
  qed
qed

interpretation splitting_calc_with_binsplit: AF_calculus_with_binsplit "to_AF bot" core.SInf "(\<Turnstile>\<^sub>A\<^sub>F)"
  "(\<Turnstile>s\<^sub>A\<^sub>F)" core.SRed\<^sub>I core.SRed\<^sub>F "{}" "{}" bin_splittable
  using extend_simps_with_binsplit[OF empty_simps.AF_calculus_extended_axioms]
  .

end (* locale splitting_calculus *)

end