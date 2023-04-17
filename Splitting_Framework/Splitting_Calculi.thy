(* Title:        Formalizing an abstract calculus based on splitting
 * Author:       Ghilain Bergeron <ghilain.bergeron at inria.fr>, 2023 *)
theory Splitting_Calculi
  imports
    Preliminaries_With_Zorn
    Light_Lifting_to_Non_Ground_Calculi
begin

section \<open>Splitting calculi\<close>

text \<open>
  In this section, we formalize an abstract version of a splitting calculus.
  We start by considering only two basic rules:
  \<^item> \textsc{Base} performs an inference from our inference system;
  \<^item> \textsc{Unsat} closes a branch if the set of assumptions is unsatisfiable.
\<close>

locale splitting_calculus = AF_calculus bot Inf entails entails_sound Red_I Red_F V fml
  for bot :: 'f and
      Inf :: \<open>'f inference set\<close> and
      entails :: \<open>[ 'f set, 'f set ] \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) and
      entails_sound :: \<open>[ 'f set, 'f set ] \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50) and
      Red_I :: \<open>'f set \<Rightarrow> 'f inference set\<close> and
      Red_F :: \<open>'f set \<Rightarrow> 'f set\<close> and
      V :: \<open>'v :: countable itself\<close> and
      fml :: \<open>'v \<Rightarrow> 'f\<close>
  + assumes
      (* D6 *)
      entails_nontrivial: \<open>\<not> {} \<Turnstile> {}\<close> and
      (* R5 *)
      reducedness: \<open>Inf_between UNIV (Red_F N) \<subseteq> Red_I N\<close> and
      (* R6 *)
      complete: \<open>bot \<notin> Red_F N\<close> and
      (* R7 *)
      all_red_to_bot: \<open>\<C> \<noteq> bot \<Longrightarrow> \<C> \<in> Red_F {bot}\<close>
begin
  
subsection \<open>The inference rules\<close>

(* The basic SInf inference system, with the two basic rules BASE and UNSAT.
 *
 * \<open>Splitting_rules \<iota>\<close> means that \<open>\<iota>\<close> is an inference rule of the system S *)

text \<open>
  Every inference rule $X$ is defined using two functions: $X\_pre$ and $X\_inf$.
  $X\_inf$ is the inference rule itself, while $X\_pre$ are side-conditions for the rule to be applicable.
\<close>

abbreviation base_pre :: \<open>('f, 'v) AF list \<Rightarrow> 'f \<Rightarrow> bool\<close> where
  \<open>base_pre \<N> D \<equiv> Infer (map F_of \<N>) D \<in> Inf\<close>

abbreviation base_inf :: \<open>('f, 'v) AF list \<Rightarrow> 'f \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>base_inf \<N> D \<equiv> Infer \<N> (Pair D (ffUnion (fset_of_list (map A_of \<N>))))\<close>

abbreviation unsat_pre :: \<open>('f, 'v) AF list \<Rightarrow> bool\<close> where
  \<open>unsat_pre \<N> \<equiv> (\<forall> x \<in> set \<N>. F_of x = bot) \<and> propositionally_unsatisfiable (set \<N>) \<and> \<N> \<noteq> []\<close>

abbreviation unsat_inf :: \<open>('f, 'v) AF list \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>unsat_inf \<N> \<equiv> Infer \<N> (to_AF bot)\<close>

inductive Splitting_rules :: \<open>('f, 'v) AF inference \<Rightarrow> bool\<close> where
  base: \<open>base_pre \<N> D \<Longrightarrow> Splitting_rules (base_inf \<N> D)\<close>
| unsat: \<open>unsat_pre \<N> \<Longrightarrow> Splitting_rules (unsat_inf \<N>)\<close>

text \<open>
  All optional rules are later included within our framework, as the main results do not fully depend on them.
  For now, we only care about \textsc{Base} and \textsc{Unsat}.
\<close>

abbreviation SInf :: \<open>('f, 'v) AF inference set\<close> where
  \<open>SInf \<equiv> {I. Splitting_rules I}\<close>

text \<open>
  The predicates in @{term Splitting_rules} form a valid inference system.
\<close>

interpretation SInf_inf_system: inference_system SInf .

(*<*)
lemma F_of_to_AF [simp]: \<open>F_of (to_AF \<C>) = \<C>\<close>
  unfolding to_AF_def
  by auto

lemma A_of_to_AF [simp]: \<open>A_of (to_AF \<C>) = {||}\<close>
  unfolding to_AF_def
  by auto

lemma F_of_propositional_clauses [simp]: \<open>(\<forall> x \<in> set \<N>. F_of x = bot) \<Longrightarrow> map F_of \<N> = map (\<lambda> _. bot) \<N>\<close>
  using map_eq_conv
  by blast

lemma set_map_is_image: \<open>set (map f l) = f ` set l\<close>
  by fastforce
(*>*)


text \<open>
  The proof for Lemma 13 is split into two parts, for each case of the set equality.
\<close>

(* Report lemma 13 1/2 *)
lemma SInf_commutes_Inf1: \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J \<subseteq> Inf_from (\<N> proj\<^sub>J J)\<close>
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
  then have \<iota>\<^sub>F_in_S: \<open>Splitting_rules \<iota>\<^sub>F\<close>
    by (simp add: inference_system.Inf_from_def)
  moreover have prems_of_\<iota>\<^sub>F_subset_\<N>: \<open>set (prems_of \<iota>\<^sub>F) \<subseteq> \<N>\<close>
    using \<iota>\<^sub>F_is_inf
    by (simp add: inference_system.Inf_from_def)
  moreover have \<open>\<iota>F_of \<iota>\<^sub>F \<in> Inf\<close>
    unfolding \<iota>F_of_def
    using \<iota>\<^sub>F_in_S
  proof (cases \<iota>\<^sub>F rule: Splitting_rules.cases)
    case (base \<N> D)
    then show \<open>base_pre (prems_of \<iota>\<^sub>F) (F_of (concl_of \<iota>\<^sub>F))\<close>
      by auto
  next
    case (unsat \<N>)
    moreover have \<open>enabled_inf \<iota>\<^sub>F J\<close>
      using \<iota>\<^sub>F_is_enabled
      by fastforce
    then have \<open>\<forall> \<C> \<in> set \<N>. F_of \<C> \<noteq> bot\<close>
      by (metis enabled_inf_def inference.sel(1) local.unsat(1) no_enabled_prop_clause_in_\<N> prems_of_\<iota>\<^sub>F_subset_\<N> subset_eq)
    then have \<open>False\<close>
      by (simp add: local.unsat(2))
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


(*<*)
lemma map2_first_is_first [simp]: \<open>length x = length y \<Longrightarrow> map2 (\<lambda>x y. x) x y = x\<close>
  by (metis fst_def map_eq_conv map_fst_zip)

lemma map2_second_is_second [simp]: \<open>length A = length B \<Longrightarrow> map2 (\<lambda> x y. y) A B = B\<close>
  by (metis map_eq_conv map_snd_zip snd_def)

lemma fimage_snd_zip_is_snd [simp]: \<open>length x = length y \<Longrightarrow> (\<lambda>(x, y). y) |`| fset_of_list (zip x y) = fset_of_list y\<close>
proof -
  assume length_x_eq_length_y: \<open>length x = length y\<close>
  have \<open>(\<lambda>(x, y). y) |`| fset_of_list A = fset_of_list (map (\<lambda>(x, y). y) A)\<close> for A
    by auto
  then show ?thesis
    using length_x_eq_length_y
    by (smt (verit, ccfv_SIG) cond_case_prod_eta map_snd_zip snd_conv)
qed

lemma F_of_Pair [simp]: \<open>F_of \<circ> (\<lambda>(x, y). Pair x y) = (\<lambda>(x, y). x)\<close>
  by (smt (verit, ccfv_SIG) AF.sel(1) comp_apply cond_case_prod_eta old.prod.case)

lemma A_of_Pair [simp]: \<open>A_of \<circ> (\<lambda>(x, y). Pair x y) = (\<lambda>(x, y). y)\<close>
  by fastforce

lemma list_all_exists_is_exists_list_all2:
  assumes \<open>list_all (\<lambda> x. \<exists> y. P x y) xs\<close>
  shows \<open>\<exists> ys. list_all2 P xs ys\<close>
  using assms
  by (induct xs, auto)
(*>*)



(* Report lemma 13 2/2 *)
lemma SInf_commutes_Inf2: \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> Inf_from (\<N> proj\<^sub>J J) \<subseteq> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J\<close>
proof (intro subsetI)
  fix \<iota>\<^sub>F
  assume bot_not_in_proj: \<open>bot \<notin> \<N> proj\<^sub>J J\<close> and
         \<iota>\<^sub>F_in_inf: \<open>\<iota>\<^sub>F \<in> Inf_from (\<N> proj\<^sub>J J)\<close>

  have \<iota>\<^sub>F_is_Inf: \<open>\<iota>\<^sub>F \<in> Inf\<close>
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
  then obtain As where length_As_is_length_prems_\<iota>\<^sub>F: \<open>length (prems_of \<iota>\<^sub>F) = length As\<close> and
                       As_def: \<open>\<forall> (C, A) \<in> set (zip (prems_of \<iota>\<^sub>F) As). Pair C A \<in> \<N> \<and> enabled (Pair C A) J\<close>
    by (smt (verit, del_insts) Ball_set_list_all list_all2_iff list_all_exists_is_exists_list_all2)
  define \<iota>\<^sub>S where
    \<open>\<iota>\<^sub>S \<equiv> Infer [ Pair \<C> A. (\<C>, A) \<leftarrow> zip (prems_of \<iota>\<^sub>F) As ] (Pair (concl_of \<iota>\<^sub>F) (ffUnion (fset_of_list As)))\<close>
  have \<iota>\<^sub>F_is_Inf2: \<open>Infer (map F_of [ Pair \<C> A. (\<C>, A) \<leftarrow> zip (prems_of \<iota>\<^sub>F) As ]) (concl_of \<iota>\<^sub>F) \<in> Inf\<close>
    using length_As_is_length_prems_\<iota>\<^sub>F
    by (auto simp add: \<iota>\<^sub>F_is_Inf)
  then have \<iota>\<^sub>S_is_SInf: \<open>\<iota>\<^sub>S \<in> SInf\<close>
    using Splitting_rules.base[OF \<iota>\<^sub>F_is_Inf2] length_As_is_length_prems_\<iota>\<^sub>F
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
  We use @{thm SInf_commutes_Inf1} and @{thm SInf_commutes_Inf2} to put the Lemma 13 together into a single proof.
  It is not needed but better reflects the content of the article.
\<close>

(* Report lemma 13 *)
lemma SInf_commutes_Inf: \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J = Inf_from (\<N> proj\<^sub>J J)\<close>
  using SInf_commutes_Inf1 SInf_commutes_Inf2
  by blast



(*<*)
lemma if_in_ffUnion_then_in_subset: \<open>x |\<in>| ffUnion A \<Longrightarrow> \<exists> a. a |\<in>| A \<and> x |\<in>| a\<close>
  by (induct \<open>A\<close> rule: fset_induct, fastforce+)

lemma fset_ffUnion_subset_iff_all_fsets_subset: \<open>fset (ffUnion A) \<subseteq> B \<longleftrightarrow> fBall A (\<lambda> x. fset x \<subseteq> B)\<close>
proof (intro fBallI subsetI iffI)
  fix a x
  assume ffUnion_A_subset_B: \<open>fset (ffUnion A) \<subseteq> B\<close> and
         a_in_A: \<open>a |\<in>| A\<close> and
         x_in_fset_a: \<open>x \<in> fset a\<close>
  then have \<open>x |\<in>| a\<close>
    by (simp add: fmember.rep_eq)
  then have \<open>x |\<in>| ffUnion A\<close>
    by (metis a_in_A ffunion_insert funion_iff set_finsert)
  then show \<open>x \<in> B\<close>
    by (meson ffUnion_A_subset_B fmember.rep_eq subsetD)
next
  fix x
  assume all_in_A_subset_B: \<open>fBall A (\<lambda> x. fset x \<subseteq> B)\<close> and
         \<open>x \<in> fset (ffUnion A)\<close>
  then have \<open>x |\<in>| ffUnion A\<close>
    by (simp add: fmember.rep_eq)
  then obtain a where \<open>a |\<in>| A\<close> and
                      x_in_a: \<open>x |\<in>| a\<close>
    by (meson if_in_ffUnion_then_in_subset)
  then have \<open>fset a \<subseteq> B\<close>
    using all_in_A_subset_B
    by blast
  then show \<open>x \<in> B\<close>
    by (meson fmember.rep_eq subsetD x_in_a)
qed

lemma fBall_fset_of_list_iff_Ball_set: \<open>fBall (fset_of_list A) P \<longleftrightarrow> Ball (set A) P\<close>
  by (simp add: fBall.rep_eq fset_of_list.rep_eq)
(*>*)



(* Report theorem 14 *)
theorem SInf_sound_wrt_entails_sound: \<open>\<iota> \<in> SInf \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>}\<close>
proof -
  assume \<open>\<iota> \<in> SInf\<close>
  then have \<open>Splitting_rules \<iota>\<close>
    by simp
  then show \<open>set (prems_of \<iota>) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>}\<close>
  proof (cases \<iota> rule: Splitting_rules.cases)
    case (base \<N> D)
    assume \<open>base_pre \<N> D\<close>
    then have inf_is_sound: \<open>set (map F_of \<N>) \<Turnstile>s {D}\<close>
      using sound
      by fastforce
    then show ?thesis
      unfolding AF_entails_sound_def sound_cons.entails_neg_def
    proof (intro allI impI)
      fix J
      assume \<open>enabled_set {concl_of \<iota>} J\<close>
      then have Pair_D_A_of_\<N>_is_enabled: \<open>enabled_set {concl_of \<iota>} J\<close>
        using base
        by simp
      then have \<open>F_of ` {concl_of \<iota>} = {D}\<close>
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
        by (meson fBall_fset_of_list_iff_Ball_set)
      then have \<open>\<forall> \<C> \<in> set \<N>. enabled \<C> J\<close>
        unfolding enabled_def
        by simp
      then have \<open>set \<N> proj\<^sub>J J = F_of ` set \<N>\<close>
        unfolding enabled_projection_def
        by auto
      moreover have \<open>{C. Pos C \<in> fml_ext ` total_strip J \<union> Pos ` F_of ` set \<N>} \<Turnstile>s {D}\<close>
        using inf_is_sound
        by (smt (verit, ccfv_threshold) UnCI imageI mem_Collect_eq set_map_is_image sound_cons.entails_subsets subsetI)
      moreover have \<open>{C. Neg C \<in> Pos ` F_of ` {concl_of \<iota>}} = {}\<close>
        by fast
      ultimately show \<open>{C. Pos C \<in> fml_ext ` total_strip J \<union> Pos ` (set (prems_of \<iota>) proj\<^sub>J J)} \<union>
                       {C. Neg C \<in> Pos ` F_of ` {concl_of \<iota>}} \<Turnstile>s
                       {C. Pos C \<in> Pos ` F_of ` {concl_of \<iota>}} \<union>
                       {C. Neg C \<in> fml_ext ` total_strip J \<union> Pos ` (set (prems_of \<iota>) proj\<^sub>J J)}\<close>
        (* /!\ Careful, this one is a little bit slow (enough to be noticed) /!\ *)
        using base
        by (smt (verit, del_insts) UnCI imageI inference.sel(1) inference.sel(2) mem_Collect_eq sound_cons.entails_subsets subsetI)
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
         (metis (no_types, lifting) empty_subsetI image_eqI insert_subset mem_Collect_eq sound_cons.bot_entails_empty
                                    sound_cons.entails_subsets)
  qed
qed

interpretation AF_sound_cons_rel: consequence_relation \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  by (rule AF_ext_sound_cons_rel)

interpretation SInf_sound_inf_system: sound_inference_system SInf \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  by (standard, auto simp add: SInf_sound_wrt_entails_sound)



subsection \<open>The redundancy criterion\<close>

(* Report definition 15: splitting redundancy criterion *)
definition SRed\<^sub>F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> where
  \<open>SRed\<^sub>F \<N> = { AF.Pair C A | C A. \<forall> \<J>. total_strip \<J> \<supseteq> fset A \<longrightarrow> C \<in> Red_F (\<N> proj\<^sub>J \<J>) }
            \<union> { AF.Pair C A | C A. \<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> A_of \<C> |\<subset>| A }\<close>

definition SRed\<^sub>I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> where
  \<open>SRed\<^sub>I \<N> = { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (\<N> proj\<^sub>J \<J>)) }
           \<union> { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> \<N> }\<close>



(* Report lemma 16 *)
lemma sredI_\<N>_proj_J_subset_redI_proj_J: \<open>to_AF bot \<notin> \<N> \<Longrightarrow> (SRed\<^sub>I \<N>) \<iota>proj\<^sub>J J \<subseteq> Red_I (\<N> proj\<^sub>J J)\<close>
proof -
  assume \<open>to_AF bot \<notin> \<N>\<close>
  then have SRed\<^sub>I_\<N>_is: \<open>SRed\<^sub>I \<N> = { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall> \<J>. {base_inf \<M> \<C>} \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (\<N> proj\<^sub>J \<J>)) }\<close>
    using SRed\<^sub>I_def
    by auto
  then show \<open>(SRed\<^sub>I \<N>) \<iota>proj\<^sub>J J \<subseteq> Red_I (\<N> proj\<^sub>J J)\<close>
  proof (cases \<open>(SRed\<^sub>I \<N>) \<iota>proj\<^sub>J J = {}\<close>)
    case True
    then show ?thesis
      by fast
  next
    case False
    then obtain \<iota>\<^sub>S where \<open>\<iota>\<^sub>S \<in> SRed\<^sub>I \<N>\<close>
      using enabled_projection_Inf_def
      by fastforce
    then have \<open>{\<iota>\<^sub>S} \<iota>proj\<^sub>J J \<subseteq> Red_I (\<N> proj\<^sub>J J)\<close>
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
  have \<open>to_AF bot \<notin> { AF.Pair C A | C A. \<forall> \<J>. total_strip \<J> \<supseteq> fset A \<longrightarrow> C \<in> Red_F (\<N> proj\<^sub>J \<J>) }\<close>
    by (simp add: complete to_AF_def)
  moreover have \<open>to_AF bot \<notin> { AF.Pair C A | C A. \<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> A_of \<C> |\<subset>| A }\<close>
    by (simp add: to_AF_def)
  moreover have \<open>to_AF bot \<notin> { AF.Pair C A | C A. \<forall> J. \<not> fset A \<subseteq> total_strip J }\<close>
    by (simp add: to_AF_def)
  ultimately show ?thesis
    using SRed\<^sub>F_def
    by auto
qed



definition ARed\<^sub>F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> where
  \<open>ARed\<^sub>F \<N> \<equiv> SRed\<^sub>F \<N>\<close>

definition ARed\<^sub>I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> where
  \<open>ARed\<^sub>I \<N> \<equiv> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (\<N> proj\<^sub>J \<J>)) }\<close>

definition AInf :: \<open>('f, 'v) AF inference set\<close> where
  \<open>AInf \<equiv> { base_inf \<N> D | \<N> D. base_pre \<N> D }\<close>

definition \<G>\<^sub>F :: \<open>'v total_interpretation \<Rightarrow> ('f, 'v) AF \<Rightarrow> 'f set\<close> where
  \<open>\<G>\<^sub>F \<J> \<C> \<equiv> {\<C>} proj\<^sub>J \<J>\<close>

definition \<G>\<^sub>I :: \<open>'v total_interpretation \<Rightarrow> ('f, 'v) AF inference \<Rightarrow> 'f inference set\<close> where
  \<open>\<G>\<^sub>I \<J> \<iota> \<equiv> {\<iota>} \<iota>proj\<^sub>J \<J>\<close>

definition tiebreaker_order :: \<open>('f, 'v :: countable) AF rel\<close> where
  \<open>tiebreaker_order \<equiv> { (\<C>, \<C>'). F_of \<C> = F_of \<C>' \<and> A_of \<C> |\<subset>| A_of \<C>' }\<close>

abbreviation sqsupset_is_tiebreaker_order (infix \<open>\<sqsupset>\<close> 50) where
  \<open>\<C> \<sqsupset> \<C>' \<equiv> (\<C>, \<C>') \<in> tiebreaker_order\<close>

(*<*)
lemma tiebreaker_order_is_strict_partial_order: \<open>po_on (\<sqsupset>) UNIV\<close>
  unfolding po_on_def irreflp_on_def transp_on_def tiebreaker_order_def
  by auto

lemma wf_fsubset: \<open>wfP (|\<subset>|)\<close>
proof -
  have \<open>wfP (\<lambda> A B. fcard A < fcard B)\<close>
    by (metis (no_types, lifting) in_measure wfPUNIVI wf_induct wf_measure)
  then show \<open>wfP (|\<subset>|)\<close>
    by (smt (verit, ccfv_threshold) pfsubset_fcard_mono wfPUNIVI wfP_induct)
qed

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
(*>*)

sublocale lift_from_ARed_to_FRed: light_tiebreaker_lifting \<open>{to_AF bot}\<close> AInf \<open>{bot}\<close> \<open>(\<Turnstile>\<inter>)\<close> Inf Red_I
                                                           Red_F \<open>\<G>\<^sub>F \<J>\<close> \<open>Some \<circ> \<G>\<^sub>I \<J>\<close> \<open>\<lambda>_. (\<sqsupset>)\<close>
proof (standard)
  fix N
  show \<open>Red_I N \<subseteq> Inf\<close>
    using Red_I_to_Inf
    by presburger
next
  fix B N
  assume \<open>B \<in> {bot}\<close> and
         \<open>N \<Turnstile>\<inter> {B}\<close>
  then show \<open>N - Red_F N \<Turnstile>\<inter> {B}\<close>
    using Red_F_Bot consequence_relation.entails_conjunctive_def consequence_relation_axioms
    by fastforce
next
  fix N N' :: \<open>'f set\<close>
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>Red_F N \<subseteq> Red_F N'\<close>
    using Red_F_of_subset
    by presburger
next
  fix N N' :: \<open>'f set\<close>
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>Red_I N \<subseteq> Red_I N'\<close>
    using Red_I_of_subset
    by presburger
next
  fix N N'
  assume \<open>N' \<subseteq> Red_F N\<close>
  then show \<open>Red_F N \<subseteq> Red_F (N - N')\<close>
    using Red_F_of_Red_F_subset
    by presburger
next
  fix N N'
  assume \<open>N' \<subseteq> Red_F N\<close>
  then show \<open>Red_I N \<subseteq> Red_I (N - N')\<close>
    using Red_I_of_Red_F_subset
    by presburger
next
  fix \<iota> N
  assume \<open>\<iota> \<in> Inf\<close> and
         \<open>concl_of \<iota> \<in> N\<close>
  then show \<open>\<iota> \<in> Red_I N\<close>
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
    by auto
next
  fix \<iota>\<^sub>A
  assume \<iota>\<^sub>A_is_ainf: \<open>\<iota>\<^sub>A \<in> AInf\<close> and
         \<open>(Some \<circ> \<G>\<^sub>I \<J>) \<iota>\<^sub>A \<noteq> None\<close>
  have \<open>\<G>\<^sub>I \<J> \<iota>\<^sub>A \<subseteq> Red_I (\<G>\<^sub>F \<J> (concl_of \<iota>\<^sub>A))\<close>
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
    then have \<open>x \<in> Red_I (\<G>\<^sub>F \<J> (Pair D (ffUnion (fset_of_list (map A_of \<N>)))))\<close>
      using x_in_\<G>\<^sub>I_of_\<iota>\<^sub>A \<iota>\<^sub>A_is_enabled x_is infer_\<N>_D_is_inf \<iota>\<^sub>A_is
      unfolding \<G>\<^sub>I_def \<G>\<^sub>F_def \<iota>F_of_def
      by (simp add: Red_I_of_Inf_to_N)
    then show \<open>x \<in> Red_I (\<G>\<^sub>F \<J> (concl_of \<iota>\<^sub>A))\<close>
      by (simp add: \<iota>\<^sub>A_is)
  qed
  then show \<open>the ((Some \<circ> \<G>\<^sub>I \<J>) \<iota>\<^sub>A) \<subseteq> Red_I (\<G>\<^sub>F \<J> (concl_of \<iota>\<^sub>A))\<close>
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

(*<*)
lemma Union_of_enabled_projection_is_enabled_projection: \<open>(\<Union> \<C> \<in> \<N>. {\<C>} proj\<^sub>J \<J>) = \<N> proj\<^sub>J \<J>\<close>
  unfolding enabled_projection_def
  by blast
(*>*)

(* It was left as an exercice to check ARed\<^sub>I and FRed\<^sub>I\<^bsup>\<inter>\<G>\<^esup> coincide, meaning that the set of redundant inferences
 * according to ARed\<^sub>I is the same as the intersection of all sets of redundant inferences according to FRed\<^sub>I\<^bsup>\<inter>\<G>\<^esup>. *)
lemma ARed\<^sub>I_is_FRed\<^sub>I: \<open>ARed\<^sub>I \<N> = (\<Inter> J. lift_from_ARed_to_FRed.Red_I_\<G> J \<N>)\<close>
proof (intro subset_antisym subsetI)
  fix \<iota>
  assume \<open>\<iota> \<in> ARed\<^sub>I \<N>\<close>
  then obtain \<M> \<C> where \<iota>_is: \<open>\<iota> = base_inf \<M> \<C>\<close> and
                         Infer_\<M>_\<C>_in_Inf: \<open>base_pre \<M> \<C>\<close> and
                         \<iota>_in_Red_I: \<open>\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (\<N> proj\<^sub>J \<J>)\<close>
    using ARed\<^sub>I_def
    by fastforce
  then have \<iota>_is_AInf: \<open>\<iota> \<in> AInf\<close>
    using AInf_def
    by blast
  then have \<open>\<forall> J. {\<iota>} \<iota>proj\<^sub>J J \<subseteq> Red_I (\<Union> (\<G>\<^sub>F J ` \<N>))\<close>
    unfolding \<G>\<^sub>F_def
    using \<iota>_in_Red_I \<iota>_is Union_of_enabled_projection_is_enabled_projection
    by auto
  then have \<open>\<forall> J. \<iota> \<in> lift_from_ARed_to_FRed.Red_I_\<G> J \<N>\<close>
    using \<iota>_is_AInf
    unfolding lift_from_ARed_to_FRed.Red_I_\<G>_def \<G>\<^sub>I_def
    by auto
  then show \<open>\<iota> \<in> (\<Inter> J. lift_from_ARed_to_FRed.Red_I_\<G> J \<N>)\<close>
    by blast
next
  fix \<iota>
  assume \<iota>_in_Red_I_\<G>: \<open>\<iota> \<in> (\<Inter> J. lift_from_ARed_to_FRed.Red_I_\<G> J \<N>)\<close>
  then have \<iota>_is_AInf: \<open>\<iota> \<in> AInf\<close> and
            all_J_\<G>\<^sub>I_subset_Red_I: \<open>\<forall> J. \<G>\<^sub>I J \<iota> \<subseteq> Red_I (\<Union> (\<G>\<^sub>F J ` \<N>))\<close>
    unfolding lift_from_ARed_to_FRed.Red_I_\<G>_def
    by auto
  then obtain \<M> \<C> where \<iota>_is: \<open>\<iota> = base_inf \<M> \<C>\<close> and
                         Infer_\<M>_\<C>_is_Inf: \<open>base_pre \<M> \<C>\<close>
    using AInf_def
    by auto
  then obtain \<iota>\<^sub>F where \<iota>\<^sub>F_is: \<open>\<iota>\<^sub>F = \<iota>F_of \<iota>\<close>
    by auto
  then have \<open>\<exists> \<M> \<C>. \<iota> = base_inf \<M> \<C> \<and> base_pre \<M> \<C> \<and> (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (\<N> proj\<^sub>J \<J>))\<close>
    using \<iota>_is Infer_\<M>_\<C>_is_Inf all_J_\<G>\<^sub>I_subset_Red_I
    unfolding \<G>\<^sub>I_def \<G>\<^sub>F_def
    using Union_of_enabled_projection_is_enabled_projection
    by fastforce
  then show \<open>\<iota> \<in> ARed\<^sub>I \<N>\<close>
    unfolding ARed\<^sub>I_def
    by auto
qed

(*<*)
lemma subformula_of_enabled_formula_is_enabled: \<open>A_of \<C> |\<subset>| A_of \<C>' \<Longrightarrow> enabled \<C>' J \<Longrightarrow> enabled \<C> J\<close>
  unfolding enabled_def
  by (meson less_eq_fset.rep_eq pfsubset_imp_fsubset subset_trans)
(*>*)

(* Check that ARed\<^sub>F and FRed\<^sub>F\<^bsup>\<inter>\<G>,\<sqsupset>\<^esup> coincide *)
lemma ARed\<^sub>F_is_FRed\<^sub>F: \<open>ARed\<^sub>F \<N> = (\<Inter> J. lift_from_ARed_to_FRed.Red_F_\<G> J \<N>)\<close>
proof (intro subset_antisym subsetI)
  fix \<C>
  assume \<C>_in_ARed\<^sub>F: \<open>\<C> \<in> ARed\<^sub>F \<N>\<close>
  then obtain C A where \<C>_is: \<open>\<C> = AF.Pair C A\<close>
    unfolding ARed\<^sub>F_def SRed\<^sub>F_def
    by blast
  consider (a) \<open>\<forall> \<J>. fset A \<subseteq> total_strip \<J> \<longrightarrow> C \<in> Red_F (\<N> proj\<^sub>J \<J>)\<close> |
           (b) \<open>\<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> A_of \<C> |\<subset>| A\<close>
    using \<C>_in_ARed\<^sub>F \<C>_is
    unfolding ARed\<^sub>F_def SRed\<^sub>F_def
    by blast
  then show \<open>\<C> \<in> (\<Inter> J. lift_from_ARed_to_FRed.Red_F_\<G> J \<N>)\<close>
    unfolding lift_from_ARed_to_FRed.Red_F_\<G>_def
  proof (cases)
    case a
    then have \<open>\<forall> J. \<forall> D \<in> \<G>\<^sub>F J \<C>. D \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>))\<close>
      unfolding Red_F_strict_def \<G>\<^sub>F_def
      using Union_of_enabled_projection_is_enabled_projection \<C>_is enabled_projection_def
            \<C>_is complete enabled_projection_def
      using enabled_def
      by force
    then have \<open>\<C> \<in> (\<Inter> J. { C. \<forall> D \<in> \<G>\<^sub>F J C. D \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>)) })\<close>
      by blast
    then show \<open>\<C> \<in> (\<Inter> J. { C. \<forall> D \<in> \<G>\<^sub>F J C. D \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> C \<and> D \<in> \<G>\<^sub>F J E) })\<close>
      by blast
  next
    case b
    then have \<open>\<forall> J. \<forall> D \<in> \<G>\<^sub>F J \<C>. \<exists> E \<in> \<N>. E \<sqsupset> \<C> \<and> D \<in> \<G>\<^sub>F J E\<close>
      unfolding \<G>\<^sub>F_def tiebreaker_order_def enabled_projection_def
      using subformula_of_enabled_formula_is_enabled
      (* /!\ Careful, a bit slow (\<sim> 1s) /!\ *)
      by (smt (verit, ccfv_SIG) AF.sel(1) AF.sel(2) \<C>_is case_prodI mem_Collect_eq singletonD singletonI)
    then have \<open>\<C> \<in> (\<Inter> J. { C. \<forall> D \<in> \<G>\<^sub>F J C. \<exists> E \<in> \<N>. E \<sqsupset> C \<and> D \<in> \<G>\<^sub>F J E })\<close>
      by blast
    then show \<open>\<C> \<in> (\<Inter> J. { C. \<forall> D \<in> \<G>\<^sub>F J C. D \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> C \<and> D \<in> \<G>\<^sub>F J E) })\<close>
      by blast
  qed
next
  fix \<C>
  assume \<C>_in_Red_F_\<G>: \<open>\<C> \<in> (\<Inter> J. lift_from_ARed_to_FRed.Red_F_\<G> J \<N>)\<close>
  then have \<C>_in_Red_F_\<G>_unfolded: \<open>\<forall> J. \<forall> D \<in> \<G>\<^sub>F J \<C>. D \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> \<C> \<and> D \<in> \<G>\<^sub>F J E)\<close>
    unfolding lift_from_ARed_to_FRed.Red_F_\<G>_def
    by blast
  then have \<C>_in_Red_F_\<G>_if_enabled: \<open>\<forall> J. enabled \<C> J \<longrightarrow> F_of \<C> \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> \<C> \<and> F_of \<C> \<in> \<G>\<^sub>F J E)\<close>
    unfolding \<G>\<^sub>F_def enabled_projection_def
    by auto
  obtain C A where \<C>_is: \<open>\<C> = AF.Pair C A\<close>
    by (meson AF.exhaust_sel)
  then have \<open>\<forall> J. fset A \<subseteq> total_strip J \<longrightarrow> C \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> \<C> \<and> C \<in> \<G>\<^sub>F J E)\<close>
    using \<C>_in_Red_F_\<G>_if_enabled
    unfolding enabled_def
    by simp
  then show \<open>\<C> \<in> ARed\<^sub>F \<N>\<close>
    using \<C>_is \<C>_in_Red_F_\<G>_if_enabled
    unfolding ARed\<^sub>F_def SRed\<^sub>F_def \<G>\<^sub>F_def enabled_def tiebreaker_order_def
    using Union_of_enabled_projection_is_enabled_projection
    by auto
qed

(*<*)
lemma Union_of_singleton_is_setcompr: \<open>(\<Union> x \<in> A. { y. y = f x \<and> P x }) = { f x | x. x \<in> A \<and> P x }\<close>
  by auto
(*>*)

(* Check that both \<Turnstile>\<^sub>A\<^sub>F and \<Turnstile>\<^sub>\<G>\<^sup>\<inter> coincide *)
lemma entails_is_entails_\<G>: \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F {\<C>} \<longleftrightarrow> (\<forall> \<J>. lift_from_ARed_to_FRed.entails_\<G> \<J> \<M> {\<C>})\<close>
proof (intro iffI allI)
  fix \<J>
  assume \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F {\<C>}\<close>
  then show \<open>lift_from_ARed_to_FRed.entails_\<G> \<J> \<M> {\<C>}\<close>
    unfolding \<G>\<^sub>F_def AF_entails_def enabled_projection_def enabled_set_def entails_conjunctive_def
    by (simp add: Union_of_singleton_is_setcompr)
next
  assume entails_\<G>_\<M>_\<C>: \<open>\<forall> \<J>. lift_from_ARed_to_FRed.entails_\<G> \<J> \<M> {\<C>}\<close>
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
  using SRed\<^sub>I_def Splitting_rules.simps
  by force

lemma SRed\<^sub>F_entails_bot: \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<Longrightarrow> N - SRed\<^sub>F N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
proof -
  fix N

  have And_to_Union: \<open>\<And> J. N - lift_from_ARed_to_FRed.Red_F_\<G> J N \<subseteq> (\<Union> J. N - lift_from_ARed_to_FRed.Red_F_\<G> J N)\<close>
    by blast

  assume N_entails_bot: \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  have \<open>lift_from_ARed_to_FRed.entails_\<G> J N {to_AF bot} \<Longrightarrow> lift_from_ARed_to_FRed.entails_\<G> J (N - lift_from_ARed_to_FRed.Red_F_\<G> J N) {to_AF bot}\<close> for J
    using lift_from_ARed_to_FRed.Red_F_Bot_F
    by blast
  then have \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<Longrightarrow> N - ARed\<^sub>F N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  proof -
    assume \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close> and
           \<open>\<And> J. lift_from_ARed_to_FRed.entails_\<G> J N {to_AF bot} \<Longrightarrow> lift_from_ARed_to_FRed.entails_\<G> J (N - lift_from_ARed_to_FRed.Red_F_\<G> J N) {to_AF bot}\<close>
    then have Red_F_\<G>_entails_\<G>_bot: \<open>\<And> J. lift_from_ARed_to_FRed.entails_\<G> J (N - lift_from_ARed_to_FRed.Red_F_\<G> J N) {to_AF bot}\<close>
      using entails_is_entails_\<G>
      by blast
    then have \<open>\<And> J. lift_from_ARed_to_FRed.entails_\<G> J (\<Union> J. N - lift_from_ARed_to_FRed.Red_F_\<G> J N) {to_AF bot}\<close>
      using And_to_Union
      by (meson lift_from_ARed_to_FRed.entails_trans lift_from_ARed_to_FRed.subset_entailed)
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
    using lift_from_ARed_to_FRed.Red_F_of_Red_F_subset_F
  proof -
    assume N'_subset_ARed\<^sub>F_N: \<open>N' \<subseteq> ARed\<^sub>F N\<close> and
           \<open>(\<And> N' \<J> N. N' \<subseteq> lift_from_ARed_to_FRed.Red_F_\<G> \<J> N \<Longrightarrow>
              lift_from_ARed_to_FRed.Red_F_\<G> \<J> N \<subseteq> lift_from_ARed_to_FRed.Red_F_\<G> \<J> (N - N'))\<close>
    then have \<open>\<And> N' N. N' \<subseteq> (\<Inter> \<J>. lift_from_ARed_to_FRed.Red_F_\<G> \<J> N) \<Longrightarrow>
                  (\<Inter> \<J>. lift_from_ARed_to_FRed.Red_F_\<G> \<J> N) \<subseteq> (\<Inter> \<J>. lift_from_ARed_to_FRed.Red_F_\<G> \<J> (N - N'))\<close>
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
    using lift_from_ARed_to_FRed.Red_I_of_Red_F_subset_F
  proof -
    assume N'_subset_ARed\<^sub>F_N: \<open>N' \<subseteq> ARed\<^sub>F N\<close> and
           \<open>(\<And> N' \<J> N. N' \<subseteq> lift_from_ARed_to_FRed.Red_F_\<G> \<J> N \<Longrightarrow>
               lift_from_ARed_to_FRed.Red_I_\<G> \<J> N \<subseteq> lift_from_ARed_to_FRed.Red_I_\<G> \<J> (N - N'))\<close>
    then have \<open>\<And> N' N. N' \<subseteq> (\<Inter> \<J>. lift_from_ARed_to_FRed.Red_F_\<G> \<J> N) \<Longrightarrow>
                  (\<Inter> \<J>. lift_from_ARed_to_FRed.Red_I_\<G> \<J> N) \<subseteq> (\<Inter> \<J>. lift_from_ARed_to_FRed.Red_I_\<G> \<J> (N - N'))\<close>
      by (metis (no_types, lifting) INF_mono' UNIV_I le_INF_iff)
    then show \<open>ARed\<^sub>I N \<subseteq> ARed\<^sub>I (N - N')\<close>
      using ARed\<^sub>I_is_FRed\<^sub>I ARed\<^sub>F_is_FRed\<^sub>F N'_subset_ARed\<^sub>F_N
      by presburger
  qed
  moreover have \<open>unsat_inf \<N> \<in> SRed\<^sub>I (N - N')\<close> if \<open>unsat_pre \<N>\<close> and
                                                   \<iota>_is_redundant: \<open>unsat_inf \<N> \<in> SRed\<^sub>I N\<close> for \<N>
    using bot_not_in_sredF_\<N> N'_subset_SRed\<^sub>F_N \<iota>_is_redundant
    unfolding SRed\<^sub>I_def SRed\<^sub>F_def
    (* /!\ Quite slow... /!\ *)
    by (smt (verit, del_insts) ARed\<^sub>F_def ARed\<^sub>I_def Diff_iff N'_subset_SRed\<^sub>F_N Un_iff bot_not_in_sredF_\<N> works_for_ARed\<^sub>I mem_Collect_eq subsetD)
  ultimately show \<open>SRed\<^sub>I N \<subseteq> SRed\<^sub>I (N - N')\<close>
    using N'_subset_SRed\<^sub>F_N bot_not_in_sredF_\<N>
    unfolding SRed\<^sub>F_def ARed\<^sub>F_def SRed\<^sub>I_def ARed\<^sub>I_def
    (* /!\ A bit slow /!\ *)
    by (smt (verit, del_insts) Collect_cong Diff_iff N'_subset_SRed\<^sub>F_N Un_iff bot_not_in_sredF_\<N> subset_iff)
qed

lemma SRed\<^sub>I_of_SInf_to_N_F: \<open>\<iota>\<^sub>S \<in> SInf \<Longrightarrow> concl_of \<iota>\<^sub>S \<in> N \<Longrightarrow> \<iota>\<^sub>S \<in> SRed\<^sub>I N\<close>
proof -
  fix \<iota>\<^sub>S N
  assume \<open>\<iota>\<^sub>S \<in> SInf\<close> and
         concl_\<iota>\<^sub>S_in_N: \<open>concl_of \<iota>\<^sub>S \<in> N\<close>
  then have \<open>Splitting_rules \<iota>\<^sub>S\<close>
    by blast
  then show \<open>\<iota>\<^sub>S \<in> SRed\<^sub>I N\<close>
    unfolding SRed\<^sub>I_def
  proof (cases \<iota>\<^sub>S rule: Splitting_rules.cases)
    case (base \<N> D)
    obtain \<M> \<C> where \<iota>\<^sub>S_is: \<open>\<iota>\<^sub>S = base_inf \<M> \<C>\<close> and
                      Infer_\<M>_\<C>_is_Inf: \<open>base_pre \<M> \<C>\<close>
      using base
      by blast
    have \<open>\<forall> J. { base_inf \<M> \<C> } \<iota>proj\<^sub>J J \<subseteq> Red_I (N proj\<^sub>J J)\<close>
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
        by (meson fBall_fset_of_list_iff_Ball_set)
      then have \<open>fBall (A_of |`| fset_of_list \<M>) (\<lambda> x. fset x \<subseteq> total_strip J)\<close>
        by auto
      then have \<open>enabled (AF.Pair \<C> (ffUnion (A_of |`| fset_of_list \<M>))) J\<close>
        using A_of_\<M>_to_\<C>_in_N
        unfolding enabled_def
        using fset_ffUnion_subset_iff_all_fsets_subset
        by (metis AF.sel(2))
      ultimately show \<open>Infer (map F_of \<M>) \<C> \<in> Red_I {F_of \<C> |\<C>. \<C> \<in> N \<and> enabled \<C> J}\<close>
        by (metis (mono_tags, lifting) AF.sel(1) Infer_\<M>_\<C>_is_Inf Red_I_of_Inf_to_N fset_of_list_map inference.sel(2) mem_Collect_eq)
    qed
    then have \<open>\<iota>\<^sub>S \<in> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall>\<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (N proj\<^sub>J \<J>))}\<close>
      using \<iota>\<^sub>S_is Infer_\<M>_\<C>_is_Inf
      by auto
    then show \<open>\<iota>\<^sub>S \<in> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall>\<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (N proj\<^sub>J \<J>)) } \<union>
                    { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> N }\<close>
      by fast
  next
    case (unsat \<N>)
    then have \<open>\<iota>\<^sub>S \<in> { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> N}\<close>
      using concl_\<iota>\<^sub>S_in_N
      by fastforce
    then show \<open>\<iota>\<^sub>S \<in> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall>\<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (N proj\<^sub>J \<J>)) } \<union>
                    { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> N }\<close>
      by fast
  qed
qed

end (* locale splitting_calculus *)

locale splitting_calculus_with_asn = splitting_calculus bot Inf entails entails_sound Red_I Red_F V fml
  for bot :: 'f and
      Inf :: \<open>'f inference set\<close> and
      entails :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) and
      entails_sound :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50) and
      Red_I :: \<open>'f set \<Rightarrow> 'f inference set\<close> and
      Red_F :: \<open>'f set \<Rightarrow> 'f set\<close> and
      V :: \<open>'v :: countable itself\<close> and
      fml :: \<open>'v \<Rightarrow> 'f\<close>
  + fixes asn :: \<open>'f sign \<Rightarrow> 'v sign set\<close>
    assumes fml_entails_C: \<open>\<forall> a \<in> asn C. sound_cons.entails_neg {fml_ext a} {C}\<close> and
            C_entails_fml: \<open>\<forall> a \<in> asn C. sound_cons.entails_neg {C} {fml_ext a}\<close> and
            asn_not_empty: \<open>asn C \<noteq> {}\<close>
begin

lemma neg_neg_A_is_A [simp]: \<open>neg (neg A) = A\<close>
  by (metis neg.simps(1) neg.simps(2) to_V.elims)

lemma swap_neg_in_entails_neg: \<open>sound_cons.entails_neg {neg A} {neg B} \<longleftrightarrow> sound_cons.entails_neg {B} {A}\<close>
  unfolding sound_cons.entails_neg_def
  by (smt (verit, ccfv_threshold) Collect_cong Un_commute mem_Collect_eq neg.simps(1) neg_neg_A_is_A singleton_conv2)

lemma \<C>_bientails_\<C>':
  \<open>a \<in> asn \<C> \<Longrightarrow> a \<in> asn \<C>' \<Longrightarrow> sound_cons.entails_neg {\<C>} {\<C>'}\<close>
  \<open>a \<in> asn \<C> \<Longrightarrow> a \<in> asn \<C>' \<Longrightarrow> sound_cons.entails_neg {\<C>'} {\<C>}\<close>
  \<open>a \<in> asn \<C> \<Longrightarrow> neg a \<in> asn \<C>' \<Longrightarrow> sound_cons.entails_neg {\<C>} {neg \<C>'}\<close>
  \<open>a \<in> asn \<C> \<Longrightarrow> neg a \<in> asn \<C>' \<Longrightarrow> sound_cons.entails_neg {neg \<C>'} {\<C>}\<close>
proof -
  assume \<open>a \<in> asn \<C>\<close> and
         \<open>a \<in> asn \<C>'\<close>
  then show \<open>sound_cons.entails_neg {\<C>} {\<C>'}\<close>
    using fml_entails_C C_entails_fml
    by (smt (verit) Un_commute consequence_relation.entails_cut insert_is_Un sound_cons.ext_cons_rel)
next
  assume \<open>a \<in> asn \<C>\<close> and
         \<open>a \<in> asn \<C>'\<close>
  then show \<open>sound_cons.entails_neg {\<C>'} {\<C>}\<close>
    using fml_entails_C C_entails_fml
    by (smt (verit) Un_commute consequence_relation.entails_cut insert_is_Un sound_cons.ext_cons_rel)
next
  assume a_in_asn_\<C>: \<open>a \<in> asn \<C>\<close> and
         neg_a_in_asn_\<C>': \<open>neg a \<in> asn \<C>'\<close>

  have \<open>sound_cons.entails_neg {\<C>} {fml_ext a}\<close>
    using a_in_asn_\<C> C_entails_fml
    by blast
  then have \<open>sound_cons.entails_neg {\<C>} {neg \<C>', fml_ext a}\<close>
    by (smt (verit, best) Un_upper2 consequence_relation.entails_subsets insert_is_Un sound_cons.ext_cons_rel sup_ge1)
  moreover have \<open>sound_cons.entails_neg {\<C>'} {fml_ext (neg a)}\<close>
    using neg_a_in_asn_\<C>' C_entails_fml
    by blast
  then have \<open>sound_cons.entails_neg {neg (neg \<C>')} {neg (fml_ext a)}\<close>
    (* /!\ A bit slow /!\ *)
    by (metis fml_ext.simps(1) fml_ext.simps(2) neg.simps(1) neg_neg_A_is_A to_V.elims)
  then have \<open>sound_cons.entails_neg {fml_ext a} {neg \<C>'}\<close>
    using swap_neg_in_entails_neg
    by blast
  then have \<open>sound_cons.entails_neg {fml_ext a, \<C>} {neg \<C>'}\<close>
    by (smt (verit, best) consequence_relation.entails_subsets insert_is_Un sound_cons.ext_cons_rel sup_ge1)
  ultimately show \<open>sound_cons.entails_neg {\<C>} {neg \<C>'}\<close>
    using consequence_relation.entails_cut
    by (smt (verit, ccfv_threshold) Un_commute insert_is_Un sound_cons.ext_cons_rel sup.idem)
next
  assume a_in_asn_\<C>: \<open>a \<in> asn \<C>\<close> and
         neg_a_in_asn_\<C>': \<open>neg a \<in> asn \<C>'\<close>

  have \<open>sound_cons.entails_neg {fml_ext a} {\<C>}\<close>
    using a_in_asn_\<C> fml_entails_C
    by blast
  then have \<open>sound_cons.entails_neg {neg \<C>', fml_ext a} {\<C>}\<close>
    by (smt (verit, best) Un_upper2 consequence_relation.entails_subsets insert_is_Un sound_cons.ext_cons_rel sup_ge1)
  moreover have \<open>sound_cons.entails_neg {fml_ext (neg a)} {\<C>'}\<close>
    using neg_a_in_asn_\<C>' fml_entails_C
    by blast
  then have \<open>sound_cons.entails_neg {neg (fml_ext a)} {neg (neg \<C>')}\<close>
    (* /!\ A bit slow /!\ *)
    by (metis fml_ext.simps(1) fml_ext.simps(2) neg.simps(1) neg_neg_A_is_A to_V.elims)
  then have \<open>sound_cons.entails_neg {neg \<C>'} {fml_ext a}\<close>
    using swap_neg_in_entails_neg
    by blast
  then have \<open>sound_cons.entails_neg {neg \<C>'} {fml_ext a, \<C>}\<close>
    by (smt (verit, best) consequence_relation.entails_subsets insert_is_Un sound_cons.ext_cons_rel sup_ge1)
  ultimately show \<open>sound_cons.entails_neg {neg \<C>'} {\<C>}\<close>
    using consequence_relation.entails_cut
    by (smt (verit, ccfv_threshold) Un_commute insert_is_Un sound_cons.ext_cons_rel sup.idem)
qed

end (* locale splitting_calculus_with_asn *)

text \<open>
  Here, we extend our basic calculus with simplification rules:
  \<^item> \textsc{Split} performs a $n$-ary case analysis on the head of the premise;
  \<^item> \textsc{Collect} performs garbage collection on clauses which contain propositionally unsatisfiable heads;
  \<^item> \textsc{Trim} removes assertions which are entailed by others.
\<close>

datatype 'f simplification =
  Simplify (S_from: \<open>'f set\<close>) (S_to: \<open>'f set\<close>)

text \<open>
  Simplification rules are said to be sound if every conclusion is entailed by all premises.
  We could have also used our conjunctive entailment @{const consequence_relation.entails_conjunctive}, but it is defined that way
  so there is nothing to worry about.
\<close>

locale sound_simplification_rules =
  sound_inference_system Inf bot entails_sound
  for bot :: 'f and
      Inf :: \<open>'f inference set\<close> and
      entails_sound :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50)
  + fixes
      Simps :: \<open>'f simplification set\<close>
    assumes
      sound_simplifications: \<open>\<iota> \<in> Simps \<Longrightarrow> \<forall> \<C> \<in> \<M> \<union> S_to \<iota>. \<M> \<union> S_from \<iota> \<Turnstile>s {\<C>}\<close>

locale splitting_calculus_with_simps =
  splitting_calculus_with_asn bot Inf entails entails_sound Red_I Red_F V fml asn
  for bot :: 'f and
      Inf :: \<open>'f inference set\<close> and
      entails :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) and
      entails_sound :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50) and
      Red_I :: \<open>'f set \<Rightarrow> 'f inference set\<close> and
      Red_F :: \<open>'f set \<Rightarrow> 'f set\<close> and
      V :: \<open>'v :: countable itself\<close> and
      fml :: \<open>'v \<Rightarrow> 'f\<close> and
      asn :: \<open>'f sign \<Rightarrow> 'v sign set\<close>
begin

interpretation AF_sound_cons_rel: consequence_relation \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  by (rule AF_ext_sound_cons_rel)

interpretation SInf_sound_inf_system: sound_inference_system SInf \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  by (standard, auto simp add: SInf_sound_wrt_entails_sound)

definition splittable :: \<open>'f \<Rightarrow> 'f fset \<Rightarrow> bool\<close> where
  \<open>splittable C Cs \<longleftrightarrow> C \<noteq> bot \<and> fcard Cs \<ge> 2 \<and> {C} \<Turnstile>s fset Cs \<and> (\<forall> C'. C' |\<in>| Cs \<longrightarrow> C \<in> Red_F {C'})\<close>

definition mk_split :: \<open>'f \<Rightarrow> 'f fset \<Rightarrow> ('f, 'v) AF fset\<close> where
  \<open>splittable C Cs \<Longrightarrow> mk_split C Cs \<equiv> (\<lambda> C'. AF.Pair C' {| SOME a. a \<in> asn (Pos C') |}) |`| Cs\<close>

abbreviation split_pre :: \<open>('f, 'v) AF \<Rightarrow> 'f fset \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> bool\<close> where
  \<open>split_pre \<C> Cs As \<equiv> splittable (F_of \<C>) Cs \<and> mk_split (F_of \<C>) Cs = As\<close>

(*<*)
lemma split_creates_singleton_assertion_sets: \<open>split_pre \<C> Cs As \<Longrightarrow> A |\<in>| As \<Longrightarrow> (\<exists> a. A_of A = {| a |})\<close>
  using mk_split_def
  by force

lemma split_all_assertion_sets_asn: \<open>split_pre \<C> Cs As \<Longrightarrow> A |\<in>| As \<Longrightarrow> (\<exists> a. A_of A = {|a|} \<and> a \<in> asn (Pos (F_of A)))\<close>
proof -
  assume pre_cond: \<open>split_pre \<C> Cs As\<close> and
         A_elem_As: \<open>A |\<in>| As\<close>
  then have \<open>\<exists> a. A_of A = {|a|}\<close>
    by (simp add: split_creates_singleton_assertion_sets)
  then obtain a where A_of_A_singleton_a: \<open>A_of A = {|a|}\<close>
    by blast
  then have \<open>a \<in> asn (Pos (F_of A))\<close>
    using pre_cond mk_split_def A_elem_As
    using asn_not_empty some_in_eq
    by (auto, blast)
  then show \<open>\<exists> a. A_of A = {|a|} \<and> a \<in> asn (Pos (F_of A))\<close>
    using A_of_A_singleton_a
    by blast
qed

lemma split_all_pairs_in_As_in_Cs: \<open>split_pre \<C> Cs As \<Longrightarrow> (\<forall> P. P |\<in>| As \<longrightarrow> F_of P |\<in>| Cs)\<close>
  using mk_split_def
  by fastforce

lemma split_all_pairs_in_Cs_in_As: \<open>split_pre \<C> Cs As \<Longrightarrow> (\<forall> C. C |\<in>| Cs \<longrightarrow> (\<exists> a. AF.Pair C {|a|} |\<in>| As))\<close>
  using mk_split_def
  by fastforce
(*>*)

abbreviation split_simp :: \<open>('f, 'v) AF \<Rightarrow> 'f fset \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> ('f, 'v) AF simplification\<close> where
  \<open>split_simp \<C> Cs As \<equiv> Simplify { \<C> } (insert (AF.Pair bot (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>)) (fset As))\<close>

abbreviation collect_pre :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> where
  \<open>collect_pre \<C> \<M> \<equiv> F_of \<C> \<noteq> bot \<and> \<M> \<Turnstile>\<^sub>A\<^sub>F { AF.Pair bot (A_of \<C>) } \<and> (\<forall> \<C> \<in> \<M>. F_of \<C> = bot)\<close>

abbreviation collect_simp :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF set \<Rightarrow> ('f, 'v) AF simplification\<close> where
  \<open>collect_simp \<C> \<M> \<equiv> Simplify (insert \<C> \<M>) \<M>\<close>

abbreviation trim_pre :: \<open>('f, 'v) AF \<Rightarrow> 'v sign fset \<Rightarrow> 'v sign fset \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> where
  \<open>trim_pre \<C> A B \<M> \<equiv> A_of \<C> = A |\<union>| B \<and> F_of \<C> \<noteq> bot \<and> \<M> \<union> { AF.Pair bot A } \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair bot B } \<and>
                       (\<forall> \<C> \<in> \<M>. F_of \<C> = bot) \<and> A |\<inter>| B = {||} \<and> A \<noteq> {||}\<close>

abbreviation trim_simp :: \<open>('f, 'v) AF \<Rightarrow> 'v sign fset \<Rightarrow> 'v sign fset \<Rightarrow> ('f, 'v) AF set \<Rightarrow> ('f, 'v) AF simplification\<close> where
  \<open>trim_simp \<C> A B \<M> \<equiv> Simplify (insert \<C> \<M>) (insert (AF.Pair (F_of \<C>) B) \<M>)\<close>

inductive Simplification_rules :: \<open>('f, 'v) AF simplification \<Rightarrow> bool\<close> where
  split: \<open>split_pre \<C> Cs As \<Longrightarrow> Simplification_rules (split_simp \<C> Cs As)\<close> |
  collect: \<open>collect_pre \<C> \<M> \<Longrightarrow> Simplification_rules (collect_simp \<C> \<M>)\<close> |
  trim: \<open>trim_pre \<C> A B \<M> \<Longrightarrow> Simplification_rules (trim_simp \<C> A B \<M>)\<close>

abbreviation Simps :: \<open>('f, 'v) AF simplification set\<close> where
  \<open>Simps \<equiv> { \<iota>. Simplification_rules \<iota> }\<close>

(*<*)
lemma projection_of_enabled_subset: \<open>fset B \<subseteq> total_strip J \<Longrightarrow> {AF.Pair C (A |\<union>| B)} proj\<^sub>J J = {AF.Pair C A} proj\<^sub>J J\<close>
  unfolding enabled_projection_def enabled_def
  by auto

lemma strong_entails_bot_cases: \<open>\<N> \<union> {AF.Pair bot A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B} \<Longrightarrow>
            (\<forall> J. fset B \<subseteq> total_strip J \<longrightarrow> sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<N> proj\<^sub>J J)) {Pos bot}
                                              \<or> fset A \<subseteq> total_strip J)\<close>
proof -
  assume \<open>\<N> \<union> {AF.Pair bot A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B}\<close>
  then have \<open>\<And> J. fset B \<subseteq> total_strip J \<Longrightarrow>
                   sound_cons.entails_neg ((fml_ext ` total_strip J) \<union> Pos ` (\<N> proj\<^sub>J J) \<union> Pos ` ({AF.Pair bot A} proj\<^sub>J J)) {Pos bot}\<close>
    unfolding AF_entails_sound_def
    by (metis (no_types, lifting) AF.sel(1) AF.sel(2) distrib_proj_singleton enabled_def enabled_set_def image_Un
                                  image_empty image_insert singletonD sup_assoc)
  then have \<open>\<And> J. fset B \<subseteq> total_strip J \<Longrightarrow>
                  sound_cons.entails_neg ((fml_ext ` total_strip J) \<union> Pos ` (\<N> proj\<^sub>J J)) {Pos bot} \<or> enabled (AF.Pair bot A) J\<close>
    by (smt (verit, ccfv_SIG) enabled_projection_def ex_in_conv image_empty mem_Collect_eq singletonD sup_bot_right)
  then show ?thesis
    by (simp add: enabled_def)
qed

lemma strong_entails_bot_cases_Union: \<open>\<N> \<union> \<M> \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B} \<Longrightarrow> (\<forall> x \<in> \<M>. F_of x = bot) \<Longrightarrow>
                (\<forall> J. fset B \<subseteq> total_strip J \<longrightarrow> sound_cons.entails_neg ((fml_ext ` total_strip J) \<union> Pos ` (\<N> proj\<^sub>J J)) {Pos bot}
                           \<or> (\<exists> A \<in> A_of ` \<M>. fset A \<subseteq> total_strip J))\<close>
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
      then show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<N> proj\<^sub>J J)) {Pos bot} \<or>
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

lemma non_zero_fcard_of_non_empty_set: \<open>fcard A > 0 \<longleftrightarrow> A \<noteq> {||}\<close>
  by (metis bot.not_eq_extremum fcard_fempty less_numeral_extra(3) pfsubset_fcard_mono)

lemma fimage_of_non_fempty_is_non_fempty: \<open>A \<noteq> {||} \<Longrightarrow> f |`| A \<noteq> {||}\<close>
  by blast

notation sound_cons.entails_neg (infix \<open>\<Turnstile>s\<^sub>\<sim>\<close> 50)

lemma entails_of_entails_iff: \<open>{C} \<Turnstile>s\<^sub>\<sim> Cs \<Longrightarrow> finite Cs \<Longrightarrow> card Cs \<ge> 1 \<Longrightarrow>
                                     (\<forall> C\<^sub>i \<in> Cs. \<M> \<union> {C\<^sub>i} \<Turnstile>s\<^sub>\<sim> {Pos bot}) \<Longrightarrow> \<M> \<union> {C} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
proof -
  assume \<open>{C} \<Turnstile>s\<^sub>\<sim> Cs\<close> and
         finite_Cs: \<open>finite Cs\<close> and
         Cs_not_empty: \<open>card Cs \<ge> 1\<close> and
         all_C\<^sub>i_entail_bot: \<open>\<forall> C\<^sub>i \<in> Cs. \<M> \<union> {C\<^sub>i} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
  then have \<open>\<M> \<union> {C} \<Turnstile>s\<^sub>\<sim> Cs\<close>
    by (meson Un_upper2 consequence_relation.entails_subsets sound_cons.ext_cons_rel subsetI)
  then show \<open>\<M> \<union> {C} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
    using Cs_not_empty all_C\<^sub>i_entail_bot
  proof (induct rule: finite_ne_induct[OF finite_Cs])
    case 1
    then show ?case
      using Cs_not_empty
      by force
  next
    case (2 x)
    then show ?case
      using consequence_relation.entails_cut sound_cons.ext_cons_rel
      by fastforce
  next
    case insert: (3 x F)

    have card_F_ge_1: \<open>card F \<ge> 1\<close>
      by (meson card_0_eq insert.hyps(1) insert.hyps(2) less_one linorder_not_less)

    have \<open>\<M> \<union> {C} \<Turnstile>s\<^sub>\<sim> {Pos bot, x} \<union> F\<close>
      by (smt (verit, ccfv_threshold) Un_insert_left Un_insert_right Un_upper2 consequence_relation.entails_subsets
                                      insert.prems(1) insert_is_Un sound_cons.ext_cons_rel)
    then have \<open>\<M> \<union> {C} \<Turnstile>s\<^sub>\<sim> {Pos bot} \<union> {x} \<union> F\<close>
      by (metis insert_is_Un)
    moreover have \<open>\<M> \<union> {C} \<union> {x} \<Turnstile>s\<^sub>\<sim> {Pos bot} \<union> F\<close>
      by (smt (verit, ccfv_SIG) Un_upper2 consequence_relation.entails_subsets insert.prems(3) insertCI
                                sound_cons.ext_cons_rel sup_assoc sup_ge1 sup_left_commute)
    ultimately have \<open>\<M> \<union> {C} \<Turnstile>s\<^sub>\<sim> {Pos bot} \<union> F\<close>
      using consequence_relation.entails_cut sound_cons.ext_cons_rel
      by fastforce
    then have \<open>\<M> \<union> {C} \<Turnstile>s\<^sub>\<sim> F\<close>
      using consequence_relation.bot_entails_empty consequence_relation.entails_cut sound_cons.ext_cons_rel
      by fastforce
    then show ?case
      using insert card_F_ge_1
      by blast
  qed
qed
(*>*)



(* Report theorem 14 *)
theorem SInf_with_simps_sound_wrt_entails_sound: \<open>\<iota> \<in> Simps \<Longrightarrow> \<forall> \<C> \<in> S_to \<iota>. S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
proof -
  assume \<open>\<iota> \<in> Simps\<close>
  then have \<iota>_is_simp_rule: \<open>Simplification_rules \<iota>\<close>
    by simp
  then show \<open>\<forall> \<C> \<in> S_to \<iota>. S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
  proof (intro ballI)
    fix \<C>
    assume \<C>_is_consq_of_\<iota>: \<open>\<C> \<in> S_to \<iota>\<close>
    show \<open>S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
      using \<iota>_is_simp_rule
    proof (cases rule: Simplification_rules.cases)
      case (split \<C>' Cs As)

      have pre_cond: \<open>split_pre \<C>' Cs As\<close>
        using split(2) .

      have Cs_not_empty: \<open>Cs \<noteq> {||}\<close>
        using split(2)
        unfolding splittable_def
        by (metis bot_nat_0.extremum_unique fcard_fempty nat.simps(3) numerals(2))
      then have As_not_empty: \<open>As \<noteq> {||}\<close>
        using mk_split_def[of \<open>F_of \<C>'\<close> \<open>Cs\<close>] splittable_def fimage_of_non_fempty_is_non_fempty[OF Cs_not_empty]
              split(2)
        by blast

      have \<open>fcard Cs \<ge> 1\<close>
        by (simp add: Cs_not_empty Suc_le_eq non_zero_fcard_of_non_empty_set)
      then have card_fset_Cs_ge_1: \<open>card (Pos ` fset Cs) \<ge> 1\<close>
        by (metis Cs_not_empty bot_fset.rep_eq card_eq_0_iff empty_is_image finite_fset finite_imageI fset_cong
                less_one linorder_not_le)

      have \<open>{F_of \<C>'} \<Turnstile>s fset Cs\<close>
        using split(2)
        unfolding splittable_def[of \<open>F_of \<C>'\<close> \<open>Cs\<close>]
        by blast
      then have F_of_\<C>_entails_Cs: \<open>{Pos (F_of \<C>')} \<Turnstile>s\<^sub>\<sim> Pos ` fset Cs\<close>
        unfolding sound_cons.entails_neg_def
        by (smt (verit, del_insts) UnCI imageI mem_Collect_eq singleton_conv sound_cons.entails_subsets subsetI)

      have finite_image_Pos_Cs: \<open>finite (Pos ` fset Cs)\<close>
        using finite_fset
        by blast

      have all_C\<^sub>i_entail_bot: \<open>\<And> J C\<^sub>i a\<^sub>i. fset (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>') \<subseteq> total_strip J \<Longrightarrow>
                                   AF.Pair C\<^sub>i {|a\<^sub>i|} |\<in>| As \<Longrightarrow> (fml_ext ` total_strip J) \<union> {Pos C\<^sub>i} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
      (* Same as for APPROX *)
      proof -
        fix J \<C>\<^sub>i a\<^sub>i
        assume \<open>fset (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>') \<subseteq> total_strip J\<close> and
               Pair_\<C>\<^sub>i_a\<^sub>i_in_As: \<open>AF.Pair \<C>\<^sub>i {|a\<^sub>i|} |\<in>| As\<close>
        then have \<open>neg a\<^sub>i \<in> total_strip J\<close>
          using mk_disjoint_finsert
          by fastforce
        then have neg_fml_a\<^sub>i_in_J: \<open>neg (fml_ext a\<^sub>i) \<in> fml_ext ` total_strip J\<close>
          by (metis fml_ext.simps(1) fml_ext.simps(2) image_iff is_Neg_to_V is_Pos_to_V neg.simps(1) neg.simps(2))
        moreover have a\<^sub>i_in_asn_\<C>\<^sub>i: \<open>a\<^sub>i \<in> asn (Pos \<C>\<^sub>i)\<close>
          using split_all_assertion_sets_asn[OF split(2) Pair_\<C>\<^sub>i_a\<^sub>i_in_As]
          by auto
        moreover have \<open>sound_cons.entails_neg {Pos \<C>\<^sub>i} {Pos \<C>\<^sub>i}\<close>
          by (meson consequence_relation.entails_reflexive sound_cons.ext_cons_rel)
        then have \<open>sound_cons.entails_neg (fml_ext ` (total_strip J - {neg a\<^sub>i}) \<union> {Pos \<C>\<^sub>i}) {Pos \<C>\<^sub>i, Pos bot}\<close>
          by (smt (verit, best) Un_upper2 consequence_relation.entails_subsets insert_is_Un sound_cons.ext_cons_rel sup_ge1)
        ultimately show \<open>sound_cons.entails_neg ((fml_ext ` total_strip J) \<union> {Pos \<C>\<^sub>i}) {Pos bot}\<close>
        proof -
          have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> {fml_ext a\<^sub>i}) ({Pos bot} \<union> {})\<close>
            by (smt (z3) Bex_def_raw UnCI Un_commute Un_insert_right Un_upper2 neg_fml_a\<^sub>i_in_J consequence_relation.entails_subsets
                         insert_is_Un insert_subset sound_cons.ext_cons_rel sound_cons.pos_neg_entails_bot)
          then show ?thesis
            by (smt (z3) C_entails_fml Un_commute a\<^sub>i_in_asn_\<C>\<^sub>i consequence_relation.entails_cut insert_is_Un sound_cons.ext_cons_rel)
        qed
      qed
      then have \<open>\<And> J. fset (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>') \<subseteq> total_strip J \<Longrightarrow>
                           sound_cons.entails_neg ((fml_ext ` total_strip J) \<union> {Pos (F_of \<C>')}) {Pos bot}\<close>
        unfolding splittable_def
      proof -
        fix J
        assume \<open>fset (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>') \<subseteq> total_strip J\<close>
        then have C\<^sub>i_head_of_pair_entails_bot: \<open>\<And> C\<^sub>i a\<^sub>i. AF.Pair C\<^sub>i {|a\<^sub>i|} |\<in>| As \<Longrightarrow>
                                                      (fml_ext ` total_strip J) \<union> {Pos C\<^sub>i} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
          using all_C\<^sub>i_entail_bot
          by blast
        then have \<open>\<And> C\<^sub>i. C\<^sub>i |\<in>| Cs \<Longrightarrow> (fml_ext ` total_strip J) \<union> {Pos C\<^sub>i} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
        proof -
          fix C\<^sub>i
          assume \<open>C\<^sub>i |\<in>| Cs\<close>
          then have \<open>\<exists> a\<^sub>i. AF.Pair C\<^sub>i {|a\<^sub>i|} |\<in>| As\<close>
            using split_all_pairs_in_Cs_in_As[OF split(2)]
            by presburger
          then obtain a\<^sub>i where \<open>AF.Pair C\<^sub>i {|a\<^sub>i|} |\<in>| As\<close>
            by blast
          then show \<open>(fml_ext ` total_strip J) \<union> {Pos C\<^sub>i} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
            using C\<^sub>i_head_of_pair_entails_bot
            by blast
        qed
        then show \<open>(fml_ext ` total_strip J) \<union> {Pos (F_of \<C>')} \<Turnstile>s\<^sub>\<sim> {Pos bot}\<close>
          using entails_of_entails_iff[OF F_of_\<C>_entails_Cs finite_image_Pos_Cs card_fset_Cs_ge_1]
          by (metis (no_types, opaque_lifting) image_iff notin_fset)
      qed
      then have \<open>\<And> J. fset (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>') \<subseteq> total_strip J \<Longrightarrow>
                           sound_cons.entails_neg ((fml_ext ` total_strip J) \<union> Pos ` (S_from \<iota> proj\<^sub>J J)) {Pos bot}\<close>
        using split(2)
        by (simp add: split(1) enabled_def enabled_projection_def)
      then have \<open>S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair bot (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>') }\<close>
        unfolding AF_entails_sound_def
        using enabled_def enabled_set_def
        by auto
      moreover have \<open>\<And> J C''. C'' |\<in>| As \<Longrightarrow> fset (A_of C'') \<subseteq> total_strip J \<Longrightarrow>
                          (fml_ext ` total_strip J) \<union> Pos ` ({\<C>'} proj\<^sub>J J) \<Turnstile>s\<^sub>\<sim> {Pos (F_of C'')}\<close>
      proof -
        fix J C''
        assume C''_in_As: \<open>C'' |\<in>| As\<close> and
               A_of_C''_subset_J: \<open>fset (A_of C'') \<subseteq> total_strip J\<close>
        then have \<open>\<exists> a\<^sub>i. a\<^sub>i \<in> asn (Pos (F_of C'')) \<and> A_of C'' = {| a\<^sub>i |}\<close>
          using split_all_assertion_sets_asn[OF pre_cond C''_in_As]
          by blast
        then obtain a\<^sub>i where a\<^sub>i_in_asn_F_of_C'': \<open>a\<^sub>i \<in> asn (Pos (F_of C''))\<close> and
                             A_of_C''_is: \<open>A_of C'' = {| a\<^sub>i |}\<close>
          by blast
        then have \<open>a\<^sub>i \<in> total_strip J\<close>
          using A_of_C''_subset_J
          by simp
        then show \<open>(fml_ext ` total_strip J) \<union> Pos ` ({\<C>'} proj\<^sub>J J) \<Turnstile>s\<^sub>\<sim> {Pos (F_of C'')}\<close>
          by (smt (verit, ccfv_threshold) Un_commute Un_upper2 a\<^sub>i_in_asn_F_of_C'' consequence_relation.entails_subsets
                                          fml_entails_C image_eqI insert_subset sound_cons.ext_cons_rel sup_bot_right)
      qed
      then have \<open>\<And> J C''. C'' \<in> fset As \<Longrightarrow> fset (A_of C'') \<subseteq> total_strip J \<Longrightarrow>
                          (fml_ext ` total_strip J) \<union> Pos ` ({\<C>'} proj\<^sub>J J) \<Turnstile>s\<^sub>\<sim> {Pos (F_of C'')}\<close>
        by (meson notin_fset)
      then have \<open>\<forall> \<C>'' \<in> fset As. S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>''}\<close>
        unfolding AF_entails_sound_def enabled_set_def enabled_def
        using split(1)
        by auto
      ultimately show ?thesis
        using \<C>_is_consq_of_\<iota> split(1)
        unfolding S_to_def
        by auto
    next
      case (collect \<C>' \<N>)
      then show ?thesis
        using \<C>_is_consq_of_\<iota>
        by (metis AF_sound_cons_rel.entails_conjunctive_def AF_sound_cons_rel.subset_entailed insert_iff simplification.sel(1)
                  simplification.sel(2) subset_refl)
    next
      case (trim \<C>' A B \<N>)
      then have \<open>A_of \<C>' = A |\<union>| B\<close> and
                \<open>F_of \<C>' \<noteq> bot\<close> and
                \<N>_and_Pair_bot_A_entails_Pair_bot_B: \<open>\<N> \<union> {AF.Pair bot A} \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair bot B}\<close> and
                all_heads_in_\<N>_are_bot: \<open>(\<forall> \<C> \<in> \<N>. F_of \<C> = bot)\<close> and
                \<open>A |\<inter>| B = {||}\<close> and
                \<open>A \<noteq> {||}\<close>
        by blast+
      then show ?thesis
        using trim projection_of_enabled_subset \<C>_is_consq_of_\<iota>
      proof (clarsimp, elim disjE)
        assume \<C>_is: \<open>\<C> = AF.Pair (F_of \<C>') B\<close>
        then have \<open>\<And> J. enabled \<C> J \<Longrightarrow> fml_ext ` total_strip J \<union> Pos ` (insert (AF.Pair (F_of \<C>') A) \<N> proj\<^sub>J J) \<Turnstile>s\<^sub>\<sim> {Pos (F_of \<C>)}\<close>
        proof -
          fix J
          assume \<open>enabled \<C> J\<close>
          then have B_in_J: \<open>fset B \<subseteq> total_strip J\<close>
            by (simp add: \<C>_is enabled_def)
          then consider (fml_unsat) \<open>sound_cons.entails_neg (fml_ext ` total_strip J) {Pos bot}\<close> |
                         (\<N>_unsat) \<open>\<exists> A' \<in> A_of ` \<N>. fset A' \<subseteq> total_strip J\<close> |
                         (A_subset_J) \<open>fset A \<subseteq> total_strip J\<close>
            using strong_entails_bot_cases[OF \<N>_and_Pair_bot_A_entails_Pair_bot_B, rule_format, OF B_in_J]
                  strong_entails_bot_cases_Union[rule_format, OF _ _ B_in_J]
            by (smt (verit, ccfv_SIG) Un_commute enabled_def enabled_projection_def equals0I image_iff mem_Collect_eq sup_bot_left)
          then show \<open>fml_ext ` total_strip J \<union> Pos ` (insert (AF.Pair (F_of \<C>') A) \<N> proj\<^sub>J J) \<Turnstile>s\<^sub>\<sim> {Pos (F_of \<C>)}\<close>
          proof cases
            case fml_unsat
            then have \<open>sound_cons.entails_neg (fml_ext ` total_strip J) {Pos bot, Pos (F_of \<C>')}\<close>
              by (smt (verit, best) Un_absorb consequence_relation.entails_subsets insert_is_Un sound_cons.ext_cons_rel sup_ge1)
            moreover have \<open>sound_cons.entails_neg ((fml_ext ` total_strip J) \<union> {Pos bot}) {Pos (F_of \<C>')}\<close>
              by (smt (verit, del_insts) Un_commute Un_upper2 empty_subsetI insert_subset mem_Collect_eq sound_cons.bot_entails_empty
                                         sound_cons.entails_neg_def sound_cons.entails_subsets)
            ultimately have \<open>sound_cons.entails_neg (fml_ext ` total_strip J) {Pos (F_of \<C>')}\<close>
              using consequence_relation.entails_cut sound_cons.ext_cons_rel
              by fastforce
            then show ?thesis
              by (smt (verit, best) AF.sel(1) \<C>_is consequence_relation.entails_subsets insert_is_Un sound_cons.ext_cons_rel sup_ge1)
          next
            case \<N>_unsat
            then have \<open>bot \<in> \<N> proj\<^sub>J J\<close>
              unfolding enabled_projection_def enabled_def
              using local.trim(2)
              by fastforce
            then have \<open>sound_cons.entails_neg (Pos ` (\<N> proj\<^sub>J J)) {}\<close>
              by (smt (verit, del_insts) consequence_relation.bot_entails_empty consequence_relation.entails_subsets image_insert
                                         insert_is_Un mk_disjoint_insert sound_cons.ext_cons_rel sup_bot_right sup_ge1)
            then show ?thesis
              by (smt (verit, ccfv_threshold) Un_upper2 consequence_relation.entails_subsets distrib_proj
                                              image_Un insert_is_Un sound_cons.ext_cons_rel sup_assoc)
          next
            case A_subset_J
            then have pair_bot_A_enabled: \<open>enabled (AF.Pair bot A) J\<close>
              by (simp add: enabled_def)
            then have \<open>sound_cons.entails_neg {Pos (F_of \<C>')} {Pos (F_of \<C>')}\<close>
               by (meson consequence_relation.entails_reflexive sound_cons.ext_cons_rel)
            then have \<open>sound_cons.entails_neg (Pos ` ({AF.Pair (F_of \<C>') A} proj\<^sub>J J)) {Pos (F_of \<C>')}\<close>
              using pair_bot_A_enabled enabled_def enabled_projection_def
              by force
            then show ?thesis
              by (smt (verit, ccfv_threshold) AF.sel(1) Un_commute Un_upper2 \<C>_is consequence_relation.entails_subsets
                                              distrib_proj image_Un insert_is_Un sound_cons.ext_cons_rel)
          qed
        qed
        then show \<open>insert \<C>' \<N> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
          unfolding AF_entails_sound_def enabled_set_def
          by (smt (verit, best) AF.collapse AF.sel(2) Un_insert_right \<C>_is distrib_proj_singleton enabled_def image_empty image_insert
                                insertCI local.trim(2) projection_of_enabled_subset sup_bot_right)
      next
        show \<open>\<C> \<in> \<N> \<Longrightarrow> insert \<C>' \<N> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
          by (metis AF_sound_cons_rel.entails_conjunctive_def AF_sound_cons_rel.subset_entailed Un_upper2 insert_is_Un)
      qed
    qed
  qed
qed



lemma SInf_with_simps_sound_wrt_entails_sound2: \<open>\<iota> \<in> Simps \<Longrightarrow> \<forall> \<C> \<in> \<M> \<union> S_to \<iota>. \<M> \<union> S_from \<iota> \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
  using SInf_with_simps_sound_wrt_entails_sound
  by (meson AF_sound_cons_rel.entails_conjunctive_def AF_sound_cons_rel.entails_subsets
            AF_sound_cons_rel.subset_entailed Un_iff Un_upper2 subset_refl)

interpretation Simps_sound: sound_simplification_rules \<open>to_AF bot\<close> SInf \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close> Simps
  by (standard, auto simp add: SInf_with_simps_sound_wrt_entails_sound2)

(*<*)
lemma enabled_set_singleton [simp]: \<open>enabled_set {\<C>} J \<longleftrightarrow> enabled \<C> J\<close>
  by (auto simp add: enabled_set_def)
(*>*)



(* Report theorem 19 *)
theorem simplification_to_redundant:
  \<open>split_pre \<C> Cs As \<Longrightarrow> \<C> \<in> SRed\<^sub>F ({ AF.Pair bot (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>) } \<union> fset As)\<close>
  \<open>collect_pre \<C> \<M> \<Longrightarrow> \<C> \<in> SRed\<^sub>F \<M>\<close>
  \<open>trim_pre \<C> A B \<M> \<Longrightarrow> \<C> \<in> SRed\<^sub>F (\<M> \<union> { AF.Pair (F_of \<C>) B })\<close>
proof -
  assume pre_cond: \<open>split_pre \<C> Cs As\<close>
  then have F_of_\<C>_not_bot: \<open>F_of \<C> \<noteq> bot\<close> and
            \<open>fcard Cs \<ge> 2\<close> and
            \<open>{ F_of \<C> } \<Turnstile>s fset Cs\<close> and
            \<C>_red_to_splitted_\<C>s: \<open>\<forall> C'. C' |\<in>| Cs \<longrightarrow> F_of \<C> \<in> Red_F {C'}\<close> and
            splittable_pre: \<open>splittable (F_of \<C>) Cs\<close> and
            split_to_As: \<open>mk_split (F_of \<C>) Cs = As\<close>
    using split_def splittable_def
    by blast+
  then have \<open>\<forall> J. enabled \<C> J \<longrightarrow> F_of \<C> \<in> Red_F (({ AF.Pair bot (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>) } proj\<^sub>J J)
                                                   \<union> (fset As proj\<^sub>J J))\<close>
  proof (intro allI impI)
    fix J
    assume \<C>_enabled: \<open>enabled \<C> J\<close>
    then show \<open>F_of \<C> \<in> Red_F (({ AF.Pair bot (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>) } proj\<^sub>J J) \<union> (fset As proj\<^sub>J J))\<close>
    proof (cases \<open>\<exists> A. A |\<in>| A_of |`| As \<and> (\<exists> a. a |\<in>| A \<and> a \<in> total_strip J)\<close>)
      case True
      then have ex_C_enabled_in_As: \<open>\<exists> C. C |\<in>| As \<and> enabled C J\<close>
        using enabled_def split_creates_singleton_assertion_sets pre_cond
        by fastforce
      then have \<open>\<exists> C. C \<in> fset As proj\<^sub>J J\<close>
        by (simp add: enabled_projection_def fmember.rep_eq)
      then show ?thesis
        using \<C>_red_to_splitted_\<C>s split_to_As Red_F_of_subset[of \<open>fset As proj\<^sub>J J\<close>]
        unfolding mk_split_def[OF splittable_pre]
        by (smt (verit, del_insts) AF.sel(1) CollectI Red_F_of_subset Un_subset_iff ex_C_enabled_in_As enabled_projection_def
                                   fimageE fmember.rep_eq insert_subset subset_iff sup_bot_right)
    next
      case False
      then have \<open>fset As proj\<^sub>J J = {}\<close>
        using split_creates_singleton_assertion_sets[OF pre_cond]
        by (smt (verit, del_insts) Collect_empty_eq enabled_def enabled_projection_def fimage_finsert finsert.rep_eq
                                   finsertCI insert_subset mk_disjoint_finsert notin_fset)
      moreover have \<open>\<forall> A. A |\<in>| A_of |`| As \<longrightarrow> (\<forall> a. a |\<in>| A \<longrightarrow> \<not> a \<in> total_strip J)\<close>
        using False
        by blast
      then have \<open>\<forall> A. A |\<in>| A_of |`| As \<longrightarrow> (\<forall> a. a |\<in>| A \<longrightarrow> neg a \<in> total_strip J)\<close>
        by auto
      then have \<open>fset (ffUnion ((fimage neg \<circ> A_of) |`| As)) \<subseteq> total_strip J\<close>
        (* /!\ Slow enough to be noticed /!\ *)
        by (smt (verit, ccfv_threshold) fimageE fset.map_comp if_in_ffUnion_then_in_subset notin_fset subsetI)
      then have \<open>fset (ffUnion ((fimage neg \<circ> A_of) |`| As) |\<union>| A_of \<C>) \<subseteq> total_strip J\<close>
        using \<C>_enabled
        by (simp add: enabled_def)
      then have \<open>{AF.Pair bot (ffUnion ((fimage neg \<circ> A_of) |`| As) |\<union>| A_of \<C>)} proj\<^sub>J J = {bot}\<close>
        unfolding enabled_projection_def enabled_def
        by auto
      ultimately show ?thesis
        by (simp add: F_of_\<C>_not_bot all_red_to_bot)
    qed
  qed
  then show \<open>\<C> \<in> SRed\<^sub>F ({ AF.Pair bot (ffUnion ((|`|) neg |`| A_of |`| As) |\<union>| A_of \<C>) } \<union> fset As)\<close>
    unfolding SRed\<^sub>F_def enabled_def
    by (intro UnI1)
       (smt (verit, ccfv_threshold) AF.collapse CollectI distrib_proj)
next
  assume \<open>collect_pre \<C> \<M>\<close>
  then have head_\<C>_not_bot: \<open>F_of \<C> \<noteq> bot\<close> and
            \<M>_entails_bot_\<C>: \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F { AF.Pair bot (A_of \<C>) }\<close> and
            all_heads_are_bot_in_\<M>: \<open>\<forall> \<C> \<in> \<M>. F_of \<C> = bot\<close>
    by blast+
  have \<open>\<And> J. (\<exists> \<C>' \<in> \<M>. enabled \<C>' J) \<Longrightarrow> enabled \<C> J \<Longrightarrow> F_of \<C> \<in> Red_F (\<M> proj\<^sub>J J)\<close> and
       \<open>\<And> J. \<not> (\<exists> \<C>' \<in> \<M>. enabled \<C>' J) \<Longrightarrow> enabled \<C> J \<Longrightarrow> False\<close>
  proof -
    fix J
    assume \<C>_enabled: \<open>enabled \<C> J\<close> and
           \<open>\<exists> \<C>' \<in> \<M>. enabled \<C>' J\<close>
    then have \<open>\<M> proj\<^sub>J J = {bot}\<close>
      using all_heads_are_bot_in_\<M>
      unfolding enabled_projection_def
      by fast
    then show \<open>F_of \<C> \<in> Red_F (\<M> proj\<^sub>J J)\<close>
      using all_red_to_bot[OF head_\<C>_not_bot]
      by simp
  next
    fix J
    assume \<C>_enabled: \<open>enabled \<C> J\<close> and
           \<open>\<not> (\<exists> \<C>' \<in> \<M>. enabled \<C>' J)\<close>
    then have \<M>_proj_J_empty: \<open>\<M> proj\<^sub>J J = {}\<close>
      unfolding enabled_projection_def
      by blast
    moreover have \<open>enabled (AF.Pair bot (A_of \<C>)) J\<close>
      using \<C>_enabled
      by (auto simp add: enabled_def)
    ultimately have \<open>{} \<Turnstile> {bot}\<close>
      using \<M>_entails_bot_\<C>
      using AF_entails_def
      by auto
    then show \<open>False\<close>
      using entails_bot_to_entails_empty entails_nontrivial
      by blast
  qed
  then show \<open>\<C> \<in> SRed\<^sub>F \<M>\<close>
    unfolding SRed\<^sub>F_def enabled_def
    by (smt (verit, ccfv_SIG) AF.collapse CollectI UnI1)
next
  assume pre_cond: \<open>trim_pre \<C> A B \<M>\<close>
  then have A_of_\<C>_is: \<open>A_of \<C> = A |\<union>| B\<close> and
            \<open>F_of \<C> \<noteq> bot\<close> and
            \<M>_and_A_entail_bot_B: \<open>\<M> \<union> { AF.Pair bot A } \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair bot B }\<close> and
            \<open>\<forall> \<C> \<in> \<M>. F_of \<C> = bot\<close> and
            A_B_disjoint: \<open>A |\<inter>| B = {||}\<close> and
            A_not_empty: \<open>A \<noteq> {||}\<close>
    by blast+
  then have \<open>\<exists> \<C>' \<in> \<M> \<union> {AF.Pair (F_of \<C>) B}. F_of \<C>' = F_of \<C> \<and> A_of \<C>' |\<subset>| A_of \<C>\<close>
    by auto
  then show \<open>\<C> \<in> SRed\<^sub>F (\<M> \<union> { AF.Pair (F_of \<C>) B })\<close>
    unfolding SRed\<^sub>F_def
    (* /!\ A little bit slow /!\ *)
    by (smt (verit, del_insts) AF.collapse AF.sel(1) AF.sel(2) CollectI UnI1 UnI2 inf_sup_absorb insert_subset
                               order_le_imp_less_or_eq pre_cond sup.cobounded2)
qed

end (* locale splitting_calculus_with_simps *)

text \<open>
  We extend our basic splitting calculus with new optional rules:
  \<^item> \textsc{StrongUnsat} is a variant of \textsc{Unsat} which uses the sound entailment instead of the "normal" entailment;
  \<^item> \textsc{Approx} is a very special case for \textsc{Split} where $n = 1$;
  \<^item> \textsc{Tauto} inserts a new formula which is always true.
\<close>

locale splitting_calculus_extensions =
  splitting_calculus_with_asn bot Inf entails entails_sound Red_I Red_F V fml asn
  for bot :: 'f and
      Inf :: \<open>'f inference set\<close> and
      entails :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) and
      entails_sound :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50) and
      Red_I :: \<open>'f set \<Rightarrow> 'f inference set\<close> and
      Red_F :: \<open>'f set \<Rightarrow> 'f set\<close> and
      V :: \<open>'v :: countable itself\<close> and
      fml :: \<open>'v \<Rightarrow> 'f\<close> and
      asn :: \<open>'f sign \<Rightarrow> 'v sign set\<close>
begin

abbreviation strong_unsat_pre :: \<open>('f, 'v) AF list \<Rightarrow> bool\<close> where
  \<open>strong_unsat_pre \<M> \<equiv> set \<M> \<Turnstile>s\<^sub>A\<^sub>F {to_AF bot} \<and> (\<forall> x \<in> set \<M>. F_of x = bot)\<close>

abbreviation strong_unsat_inf :: \<open>('f, 'v) AF list \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>strong_unsat_inf \<M> \<equiv> Infer \<M> (to_AF bot)\<close>

abbreviation tauto_pre :: \<open>('f, 'v) AF \<Rightarrow> bool\<close> where
  \<open>tauto_pre \<C> \<equiv> {} \<Turnstile>s\<^sub>A\<^sub>F { \<C> }\<close>

abbreviation tauto_inf :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>tauto_inf \<C> \<equiv> Infer [] \<C>\<close>

abbreviation approx_pre :: \<open>'v sign \<Rightarrow> ('f, 'v) AF \<Rightarrow> bool\<close> where
  \<open>approx_pre a \<C> \<equiv> a \<in> asn (Pos (F_of \<C>))\<close>

abbreviation approx_inf :: \<open>('f, 'v) AF \<Rightarrow> 'v sign \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>approx_inf \<C> a \<equiv> Infer [\<C>] (AF.Pair bot (finsert (neg a) (A_of \<C>)))\<close>

inductive Splitting_rules2 :: \<open>('f, 'v) AF inference \<Rightarrow> bool\<close> where
  strong_unsat: \<open>strong_unsat_pre \<M> \<Longrightarrow> Splitting_rules2 (strong_unsat_inf \<M>)\<close> |
  tauto: \<open>tauto_pre \<C> \<Longrightarrow> Splitting_rules2 (tauto_inf \<C>)\<close> |
  approx: \<open>approx_pre a \<C> \<Longrightarrow> Splitting_rules2 (approx_inf \<C> a)\<close>

abbreviation SInf2 :: \<open>('f, 'v) AF inference set\<close> where
  \<open>SInf2 \<equiv> SInf \<union> {\<iota>. Splitting_rules2 \<iota>}\<close>

(*<*)
lemma enabled_iff: \<open>A_of \<C> = A_of \<C>' \<Longrightarrow> enabled \<C> J \<longleftrightarrow> enabled \<C>' J\<close>
  unfolding enabled_def
  by simp
(*>*)



(* Report theorem 14 (cont) *)
theorem SInf2_sound_wrt_entails_sound: \<open>\<iota> \<in> SInf2 \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>}\<close>
proof (elim UnE)
  show \<open>\<iota> \<in> SInf \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>}\<close>
    using SInf_sound_wrt_entails_sound .
next
  assume \<open>\<iota> \<in> Collect Splitting_rules2\<close>
  then have \<open>Splitting_rules2 \<iota>\<close>
    by simp
  then show \<open>set (prems_of \<iota>) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>}\<close>
  proof (cases \<iota> rule: Splitting_rules2.cases)
    case (strong_unsat \<M>)
    then show ?thesis
      by simp
  next
    case (tauto \<C>)
    then show ?thesis
      by auto
  next
    case (approx a \<C>)
    then have \<open>\<And> J. enabled (AF.Pair bot (finsert (neg a) (A_of \<C>))) J \<Longrightarrow>
                       sound_cons.entails_neg ((fml_ext ` total_strip J) \<union> {Pos (F_of \<C>)}) {Pos bot}\<close>
    proof -
      fix J
      assume \<open>enabled (AF.Pair bot (finsert (neg a) (A_of \<C>))) J\<close>
      then have \<open>fset (finsert (neg a) (A_of \<C>)) \<subseteq> total_strip J\<close>
        unfolding enabled_def
        by simp
      then have neg_fml_ext_in_J: \<open>neg (fml_ext a) \<in> fml_ext ` total_strip J\<close>
        by (smt (verit, ccfv_threshold) finsert.rep_eq fml_ext.elims fml_ext.simps(1) fml_ext.simps(2) image_iff
                                        insert_subset neg.simps(1) neg.simps(2))
      moreover have \<open>sound_cons.entails_neg {Pos (F_of \<C>)} {Pos (F_of \<C>)}\<close>
        using \<C>_bientails_\<C>'(2) local.approx(2)
        by presburger
      then have \<open>sound_cons.entails_neg ((fml_ext ` (total_strip J - {neg a})) \<union> {Pos (F_of \<C>)}) {Pos bot, Pos (F_of \<C>)}\<close>
        by (metis (no_types, lifting) consequence_relation.entails_subsets insert_is_Un sound_cons.ext_cons_rel sup.cobounded2)
      ultimately show \<open>sound_cons.entails_neg ((fml_ext ` total_strip J) \<union> {Pos (F_of \<C>)}) {Pos bot}\<close>
      (* Sledgehammer produced this?????
       * Well nice one I guess. *)
      proof -
        have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> {fml_ext a}) ({Pos bot} \<union> {})\<close>
          by (smt (z3) Bex_def_raw UnCI Un_commute Un_insert_right Un_upper2 neg_fml_ext_in_J consequence_relation.entails_subsets
                       insert_is_Un insert_subset sound_cons.ext_cons_rel sound_cons.pos_neg_entails_bot)
        then show ?thesis
          by (smt (z3) C_entails_fml Un_commute consequence_relation.entails_cut insert_is_Un local.approx(2) sound_cons.ext_cons_rel)
      qed
    qed
    then have \<open>\<And> J. enabled_set {AF.Pair bot (finsert (neg a) (A_of \<C>))} J \<Longrightarrow>
                       sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` ({\<C>} proj\<^sub>J J)) {Pos bot}\<close>
      unfolding enabled_projection_def enabled_def enabled_set_def
      by auto
    then show ?thesis
      unfolding AF_entails_sound_def
      using approx
      by auto
  qed
qed



interpretation AF_sound_cons_rel: consequence_relation \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  by (rule AF_ext_sound_cons_rel)

interpretation SInf2_sound_inf_system: sound_inference_system SInf2 \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  by (standard, auto simp add: SInf2_sound_wrt_entails_sound)

end (* locale splitting_calculus_extensions *)

subsection \<open>Standard saturation\<close>

context splitting_calculus
begin

(* This is a bundle containing some rules which are mostly used together.
 * Its purpose is simply to reduce the visual clutter from long proofs. *)
lemmas SRed_rules = SRed\<^sub>F_entails_bot SRed\<^sub>F_of_subset_F SRed\<^sub>I_of_subset_F SRed\<^sub>F_of_SRed\<^sub>F_subset_F
                    SRed\<^sub>I_of_SRed\<^sub>F_subset_F SRed\<^sub>I_of_SInf_to_N_F SRed\<^sub>I_in_SInf

(* Report lemma 18 *)
sublocale S_calculus: calculus \<open>to_AF bot\<close> SInf AF_entails SRed\<^sub>I SRed\<^sub>F
  by (standard; simp add: SRed_rules)

(*<*)
alias S_saturated = S_calculus.saturated
alias F_saturated = local.saturated

lemma F_of_circ_to_AF_is_id [simp]: \<open>F_of \<circ> to_AF = id\<close>
  by fastforce

lemma A_of_circ_to_AF_is_empty_set [simp]: \<open>A_of \<circ> to_AF = (\<lambda> _. {||})\<close>
  by fastforce

lemma map_A_of_map2_Pair: \<open>length A = length B \<Longrightarrow> map A_of (map2 AF.Pair A B) = B\<close>
  by auto

lemma ball_set_f_to_ball_set_map: \<open>(\<forall> x \<in> set A. P (f x)) \<longleftrightarrow> (\<forall> x \<in> set (map f A). P x)\<close>
  by simp

lemma list_all_ex_to_ex_list_all2:
  \<open>list_all (\<lambda> x. \<exists> y. P x y) A \<longleftrightarrow> (\<exists> ys. length A = length ys \<and> list_all2 (\<lambda> x y. P x y) A ys)\<close>
  by (metis list_all2_conv_all_nth list_all_exists_is_exists_list_all2 list_all_length)

lemma list_all2_to_map:
  assumes lengths_eq: \<open>length A = length B\<close>
  shows \<open>list_all2 (\<lambda> x y. P (f x y)) A B \<longleftrightarrow> list_all P (map2 f A B)\<close>
proof -
  have \<open>list_all2 (\<lambda> x y. P (f x y)) A B \<longleftrightarrow> list_all (\<lambda> (x, y). P (f x y)) (zip A B)\<close>
    by (simp add: lengths_eq list_all2_iff list_all_iff)
  also have \<open>... \<longleftrightarrow> list_all (\<lambda> x. P x) (map2 f A B)\<close>
    by (simp add: case_prod_beta list_all_iff)
  finally show ?thesis .
qed
(*>*)



(* Report lemma 20 *)
lemma S_saturated_to_F_saturated: \<open>S_saturated \<N> \<Longrightarrow> F_saturated (\<N> proj\<^sub>J \<J>)\<close>
proof -
  assume \<N>_is_S_saturated: \<open>S_calculus.saturated \<N>\<close>
  then show \<open>saturated (\<N> proj\<^sub>J \<J>)\<close>
    unfolding saturated_def S_calculus.saturated_def
  proof (intro subsetI)
    fix \<iota>\<^sub>F
    assume \<open>\<iota>\<^sub>F \<in> Inf_from (\<N> proj\<^sub>J \<J>)\<close>
    then have \<iota>\<^sub>F_is_Inf: \<open>\<iota>\<^sub>F \<in> Inf\<close> and
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
      by (smt (verit, del_insts) AF.exhaust AF.sel(1) list.pred_mono_strong list_all_ex_to_ex_list_all2)
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
      using all_enabled ball_set_f_to_ball_set_map[where P = \<open>\<lambda> x. fset x \<subseteq> total_strip \<J>\<close> and f = A_of]
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
      using Splitting_rules.base[OF pre_holds]
      unfolding enabled_projection_Inf_def S_calculus.Inf_from_def
      by (metis (mono_tags, lifting) inference.sel(1) mem_Collect_eq)
    then have \<open>\<exists> \<M> D. base_inf \<M> D \<in> S_calculus.Inf_from \<N> \<and> \<iota>F_of (base_inf \<M> D) = \<iota>\<^sub>F \<and> enabled_inf (base_inf \<M> D) \<J>\<close>
      using \<iota>F_of_base_inf_is_\<iota>\<^sub>F
      unfolding enabled_projection_Inf_def
      by (metis (mono_tags, lifting) CollectI S_calculus.Inf_from_def Splitting_rules.base base_inf_enabled
                                     inference.sel(1) pre_holds set_prems_As_subset_\<N>)
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
    ultimately show \<open>\<iota>\<^sub>F \<in> Red_I (\<N> proj\<^sub>J \<J>)\<close>
      using \<iota>\<^sub>F_in_Inf_\<N>_proj_\<J> \<iota>F_of_base_inf_is_\<iota>\<^sub>F base_inf_enabled
      unfolding SRed\<^sub>I_def enabled_projection_Inf_def \<iota>F_of_def enabled_def enabled_projection_def
      by auto
         (metis (mono_tags, lifting) AF.sel(2) F_of_to_AF Red_I_of_Inf_to_N bot_fset.rep_eq empty_subsetI
                                     inference.sel(2) mem_Collect_eq to_AF_def)
  qed
qed

(*<*)
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
      by auto
  qed
qed

lemma Union_empty_if_set_empty_or_all_empty: \<open>ffUnion A = {||} \<Longrightarrow> A = {||} \<or> fBall A (\<lambda> x. x = {||})\<close>
  by (metis (mono_tags, lifting) fBallI ffunion_insert finsert_absorb funion_fempty_right)

lemma fBall_fimage_is_fBall: \<open>fBall (f |`| A) P \<longleftrightarrow> fBall A (\<lambda> x. P (f x))\<close>
  by auto

lemma prop_unsat_compactness: \<open>propositionally_unsatisfiable A \<Longrightarrow> \<exists> B \<subseteq> A. finite B \<and> propositionally_unsatisfiable B\<close>
  by (meson compactness_AF_proj equiv_prop_entails propositionally_unsatisfiable_def)
(*>*)

interpretation AF_sound_cons_rel: consequence_relation \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  by (rule AF_ext_sound_cons_rel)

(* This is easier to type than \<open>AF_cons_rel.entails_conjunctive\<close>, and looks more beautiful. *)
notation AF_cons_rel.entails_conjunctive (infix \<open>\<Turnstile>\<inter>\<^sub>A\<^sub>F\<close> 50)



(* Report theorem 21 *)
theorem S_calculus_statically_complete:
  assumes F_statically_complete: \<open>statically_complete_calculus bot Inf (\<Turnstile>) Red_I Red_F\<close>
  shows \<open>statically_complete_calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
  using F_statically_complete
  unfolding statically_complete_calculus_def statically_complete_calculus_axioms_def
proof (intro conjI allI impI; elim conjE)
  show \<open>Preliminaries_With_Zorn.calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
    using S_calculus.calculus_axioms
    by force
next
  fix N
  assume \<open>Preliminaries_With_Zorn.calculus bot Inf (\<Turnstile>) Red_I Red_F\<close> and
         if_F_saturated_and_N_entails_bot_then_bot_in_N: \<open>\<forall> N. F_saturated N \<longrightarrow> N \<Turnstile> {bot} \<longrightarrow> bot \<in> N\<close> and
         N_is_S_saturated: \<open>S_saturated N\<close> and
         N_entails_bot: \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  then have N_proj_\<J>_entails_bot: \<open>\<forall> \<J>. N proj\<^sub>J \<J> \<Turnstile> {bot}\<close>
    unfolding AF_entails_def
    using F_of_to_AF[of bot]
    by (smt (verit) enabled_to_AF_set image_empty image_insert)
  then have N_proj_\<J>_F_saturated: \<open>\<forall> \<J>. F_saturated (N proj\<^sub>J \<J>)\<close>
    using N_is_S_saturated
    using S_saturated_to_F_saturated
    by blast
  then have \<open>\<forall> \<J>. bot \<in> N proj\<^sub>J \<J>\<close>
    using N_proj_\<J>_entails_bot if_F_saturated_and_N_entails_bot_then_bot_in_N
    by presburger
  then have prop_proj_N_is_prop_unsat: \<open>propositionally_unsatisfiable (proj\<^sub>\<bottom> N)\<close>
    unfolding enabled_projection_def propositional_model_def propositional_projection_def propositionally_unsatisfiable_def
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
    by (smt (verit, del_insts) AF_cons_rel.entails_bot_to_entails_empty AF_cons_rel.entails_empty_reflexive_dangerous
                               compactness_AF_proj equiv_prop_entails finite_list image_empty prop_proj_N_is_prop_unsat
                               prop_proj_in propositional_model2_def propositionally_unsatisfiable_def set_empty2
                               subset_empty subset_trans to_AF_proj_J)
  then have \<open>unsat_inf \<M> \<in> S_calculus.Inf_from N\<close> and
            Infer_\<M>_bot_in_SInf: \<open>unsat_inf \<M> \<in> SInf\<close>
    using \<M>_not_empty \<M>_subset_prop_proj_N Splitting_rules.unsat S_calculus.Inf_if_Inf_from
    unfolding S_calculus.Inf_from_def propositionally_unsatisfiable_def propositional_model_def propositional_projection_def
    by fastforce+
  then have \<open>unsat_inf \<M> \<in> SRed\<^sub>I N\<close>
    using N_is_S_saturated S_calculus.saturated_def
    by blast
  then show \<open>to_AF bot \<in> N\<close>
    unfolding SRed\<^sub>I_def
  proof (elim UnE)
    assume \<open>unsat_inf \<M> \<in> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (N proj\<^sub>J \<J>)) }\<close>
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
        by meson
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

lemma saturated_equiv: \<open>S_saturated N \<longleftrightarrow> Calculus.calculus.saturated SInf SRed\<^sub>I N\<close>
  by (meson Calculus.calculus.saturated_def S_calculus.saturated_def S_with_conj_is_calculus)

lemma derivation_equiv: \<open>is_derivation S_calculus.derive Ns \<longleftrightarrow> chain (Calculus.calculus.derive SRed\<^sub>F) (to_llist Ns)\<close>
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
  ultimately have \<open>(\<forall> i. S_calculus.derive (llnth Ns i) (llnth Ns (Suc i))) \<longleftrightarrow> chain (Calculus.calculus.derive SRed\<^sub>F) (to_llist Ns)\<close>
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
  From that and theorem @{thm S_calculus_statically_complete}, we obtain that \<open>(SInf, (SRed\<^sub>I, SRed\<^sub>F))\<close> is statically complete.
  This means that for all \<open>\<N> \<subseteq> UNIV\<close>, if \<open>\<N>\<close> is saturated w.r.t. \<open>(SInf, SRed\<^sub>I)\<close> and \<open>\<N> \<Turnstile>\<union>\<^sub>A\<^sub>F {\<bottom>}\<close> then \<open>\<bottom> \<in> \<N>\<close>.
  Since \<open>\<Turnstile>\<union>\<^sub>A\<^sub>F \<equiv> \<Turnstile>\<inter>\<^sub>A\<^sub>F\<close> when the right hand side is a singleton set, we have that for all \<open>\<N> \<subseteq> UNIV\<close>, if \<open>\<N>\<close> is saturated w.r.t. \<open>(SInf, SRed\<^sub>I)\<close>
  and \<open>\<N> \<Turnstile>\<inter>\<^sub>A\<^sub>F {\<bottom>}\<close> then \<open>\<bottom> \<in> \<N>\<close>.

  Because \<open>\<Turnstile>\<inter>\<^sub>A\<^sub>F\<close> is a consequence relation for the Saturation Framework, we can derive that \<open>(SInf, (SRed\<^sub>I, SRed\<^sub>F))\<close> is dynamically complete
  (using the conjunctive entailment).
  We then proceed as above but in the opposite way to show that \<open>(SInf, (SRed\<^sub>I, SRed\<^sub>F))\<close> is dynamically complete
  using the disjunctive entailment \<open>\<Turnstile>\<union>\<^sub>A\<^sub>F\<close>.
\<close>

(* Report corollary 22 *)
corollary S_calculus_dynamically_complete:
  assumes F_statically_complete: \<open>statically_complete_calculus bot Inf (\<Turnstile>) Red_I Red_F\<close>
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
    unfolding statically_complete_calculus_axioms_def Calculus.statically_complete_calculus_axioms_def
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
    unfolding dynamically_complete_calculus_axioms_def Calculus.dynamically_complete_calculus_axioms_def
    by (metis derivation_equiv fair_equiv llhd.rep_eq llnth.rep_eq singletonD singletonI)
  then have \<open>dynamically_complete_calculus_axioms (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
    unfolding dynamically_complete_calculus_axioms_def
    using entails_conj_is_entails_disj_if_right_singleton
    by presburger
  then show \<open>dynamically_complete_calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
    by (simp add: Preliminaries_With_Zorn.dynamically_complete_calculus_def S_calculus.calculus_axioms)
qed



subsection \<open>Local saturation\<close>

text \<open>
  To fully capture splitting, we need to use a weaker notion of saturation and fairness.
\<close>

(* Report definition 23 *)
definition locally_saturated :: \<open>('f, 'v) AF inference set \<Rightarrow> (('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set) \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> where
  \<open>locally_saturated S_Inf SRed_I \<N> \<equiv> to_AF bot \<in> \<N> \<or>
                                      (\<exists> J :: 'v total_interpretation. J \<Turnstile>\<^sub>p \<N> \<and> saturated (\<N> proj\<^sub>J J))\<close>
                                      (* NOTE: in the paper, the propositional projection is explicit.
                                       * In our case, it is hidden within the definition for @{const propositional_model}. *)
(* NOTE: what's the point of S_Inf and SRed_I if we are not using them in our definition? *)



(* Report theorem 24 *)
theorem S_calculus_strong_statically_complete:
  assumes F_statically_complete: \<open>statically_complete_calculus bot Inf (\<Turnstile>) Red_I Red_F\<close> and
          \<N>_locally_saturated: \<open>locally_saturated SInf SRed\<^sub>I \<N>\<close> and
          \<N>_entails_bot: \<open>\<N> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  shows \<open>to_AF bot \<in> \<N>\<close>
  using \<N>_locally_saturated
  unfolding locally_saturated_def
proof (elim disjE)
  show \<open>to_AF bot \<in> \<N> \<Longrightarrow> to_AF bot \<in> \<N>\<close>
    by blast
next
  assume \<open>\<exists> J. J \<Turnstile>\<^sub>p \<N> \<and> F_saturated (\<N> proj\<^sub>J J)\<close>
  then obtain J where J_prop_model_of_\<N>: \<open>J \<Turnstile>\<^sub>p \<N>\<close> and
                      \<N>_proj_J_saturated: \<open>F_saturated (\<N> proj\<^sub>J J)\<close>
    by blast
  then have \<open>\<N> proj\<^sub>J J \<Turnstile> {bot}\<close>
    using \<N>_entails_bot AF_entails_def enabled_to_AF_set
    by fastforce
  then have \<open>bot \<in> \<N> proj\<^sub>J J\<close>
    using \<N>_proj_J_saturated F_statically_complete
    by (simp add: Preliminaries_With_Zorn.statically_complete_calculus.statically_complete)
  then show \<open>to_AF bot \<in> \<N>\<close>
    using J_prop_model_of_\<N>
    using enabled_projection_def propositional_model_def propositional_projection_def
    by force
qed



(* Report definition 26 *)
definition locally_fair :: \<open>('f, 'v) AF set infinite_llist \<Rightarrow> ('f, 'v) AF inference set \<Rightarrow> (('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set) \<Rightarrow> bool\<close> where
  \<open>locally_fair \<N>i S_Inf SRed_I \<equiv> (\<exists> i. to_AF bot \<in> llnth \<N>i i)
                                 \<or> (\<exists> J :: 'v total_interpretation. J \<Turnstile>\<^sub>p lim_inf \<N>i \<and>
                                                                    Inf_from (lim_inf \<N>i proj\<^sub>J J) \<subseteq> (\<Union> i. Red_I (llnth \<N>i i proj\<^sub>J J)))\<close>

(*<*)
lemma SRed_of_lim_inf: \<open>SRed\<^sub>F (lim_inf \<N>i) proj\<^sub>J J \<subseteq> Red_F (lim_inf \<N>i proj\<^sub>J J) \<union> (lim_inf \<N>i proj\<^sub>J J)\<close>
proof (intro subsetI)
  fix f
  assume \<open>f \<in> SRed\<^sub>F (lim_inf \<N>i) proj\<^sub>J J\<close>
  then show \<open>f \<in> Red_F (lim_inf \<N>i proj\<^sub>J J) \<union> (lim_inf \<N>i proj\<^sub>J J)\<close>
    unfolding SRed\<^sub>F_def enabled_projection_def enabled_def
    using less_eq_fset.rep_eq
    by (auto, fastforce)
qed

lemma bot_at_i_implies_bot_at_liminf: \<open>is_derivation S_calculus.derive \<N>i \<Longrightarrow> to_AF bot \<in> llnth \<N>i i \<Longrightarrow> to_AF bot \<in> lim_inf \<N>i\<close>
proof -
  assume \<N>i_is_derivation: \<open>is_derivation S_calculus.derive \<N>i\<close> and
         bot_at_i: \<open>to_AF bot \<in> llnth \<N>i i\<close>
  then have \<open>\<forall> i. llnth \<N>i i - llnth \<N>i (Suc i) \<subseteq> SRed\<^sub>F (llnth \<N>i (Suc i))\<close>
    unfolding is_derivation_def S_calculus.derive_def
    by blast
  then show ?thesis
    using bot_at_i
  proof (transfer fixing: bot i Red_F)
    fix \<N>i'
    assume llength_is_infinity: \<open>llength \<N>i' = \<infinity>\<close> and
           bot_at_i: \<open>to_AF bot \<in> lnth \<N>i' i\<close> and
           all_at_i_minus_next_i_are_redundant: \<open>\<forall> i. lnth \<N>i' i - lnth \<N>i' (Suc i) \<subseteq> SRed\<^sub>F (lnth \<N>i' (Suc i))\<close>
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
            using all_at_i_minus_next_i_are_redundant[rule_format, of \<open>n - 1\<close>] bot_not_in_sredF_\<N> n_positive
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

lemma Red_I_of_inf_Red_F_subset_Red_I_of_inf: \<open>Red_I ((lim_inf \<N>i proj\<^sub>J J) \<union> Red_F (lim_inf \<N>i proj\<^sub>J J)) = Red_I (lim_inf \<N>i proj\<^sub>J J)\<close>
proof (intro subset_antisym)
  have \<open>Red_F (lim_inf \<N>i proj\<^sub>J J) \<subseteq> Red_F ((lim_inf \<N>i proj\<^sub>J J) \<union> Red_F (lim_inf \<N>i proj\<^sub>J J))\<close>
    by (simp add: Red_F_of_subset)
  then show \<open>Red_I ((lim_inf \<N>i proj\<^sub>J J) \<union> Red_F (lim_inf \<N>i proj\<^sub>J J)) \<subseteq> Red_I (lim_inf \<N>i proj\<^sub>J J)\<close>
   by (smt (verit, del_insts) DiffE Red_I_of_subset Un_iff lift_from_ARed_to_FRed.ground.Red_I_without_red_F subset_iff)
next
  show \<open>Red_I (lim_inf \<N>i proj\<^sub>J J) \<subseteq> Red_I ((lim_inf \<N>i proj\<^sub>J J) \<union> Red_F (lim_inf \<N>i proj\<^sub>J J))\<close>
    by (simp add: Red_I_of_subset)
qed
(*>*)



(* Report lemma 27 *)
lemma locally_fair_derivation_is_saturated_at_liminf: \<open>\<lbrakk> is_derivation S_calculus.derive \<N>i; locally_fair \<N>i SInf SRed\<^sub>I \<rbrakk> \<Longrightarrow>
                                                           locally_saturated SInf SRed\<^sub>I (lim_inf \<N>i)\<close>
proof -
  assume \<N>i_is_derivation: \<open>is_derivation S_calculus.derive \<N>i\<close> and
         \<open>locally_fair \<N>i SInf SRed\<^sub>I\<close>
  then show \<open>locally_saturated SInf SRed\<^sub>I (lim_inf \<N>i)\<close>
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
    assume \<open>\<exists> J. J \<Turnstile>\<^sub>p limit \<N>i \<and> Inf_from (limit \<N>i proj\<^sub>J J) \<subseteq> (\<Union> i. Red_I (llnth \<N>i i proj\<^sub>J J))\<close>
    then obtain J where J_prop_model_of_limit: \<open>J \<Turnstile>\<^sub>p limit \<N>i\<close> and
                        all_inf_of_limit_are_redundant: \<open>Inf_from (limit \<N>i proj\<^sub>J J) \<subseteq> (\<Union> i. Red_I (llnth \<N>i i proj\<^sub>J J))\<close>
      by blast
    then have \<open>\<forall> i. llnth \<N>i i \<subseteq> lim_inf \<N>i \<union> SRed\<^sub>F (lim_inf \<N>i)\<close>
      using Calculus.calculus.i_in_Liminf_or_Red_F[OF S_with_conj_is_calculus, of \<open>to_llist \<N>i\<close>] derivation_equiv[of \<open>\<N>i\<close>]
      by (simp add: Liminf_infinite_llist.rep_eq \<N>i_is_derivation llength_of_to_llist_is_infinite llnth.rep_eq sup_commute)
    then have \<open>\<forall> i. llnth \<N>i i proj\<^sub>J J \<subseteq> (lim_inf \<N>i proj\<^sub>J J) \<union> Red_F (lim_inf \<N>i proj\<^sub>J J)\<close>
      by (smt (verit, best) SRed_of_lim_inf UN_iff UnE UnI1 Un_commute Union_of_enabled_projection_is_enabled_projection subset_iff)
    then have Red_I_in_Red_I_of_Red_F: \<open>(\<Union> i. Red_I (llnth \<N>i i proj\<^sub>J J)) \<subseteq> (\<Union> i. Red_I ((lim_inf \<N>i proj\<^sub>J J) \<union> Red_F (lim_inf \<N>i proj\<^sub>J J)))\<close>
      by (meson Red_I_of_subset SUP_mono UNIV_I)
    then have \<open>(\<Union> i. Red_I (llnth \<N>i i proj\<^sub>J J)) \<subseteq> (\<Union> i. Red_I (lim_inf \<N>i proj\<^sub>J J))\<close>
      using Red_I_of_inf_Red_F_subset_Red_I_of_inf
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
theorem S_calculus_strong_dynamically_complete1:
  assumes F_statically_complete: \<open>statically_complete_calculus bot Inf (\<Turnstile>) Red_I Red_F\<close> and
          \<N>i_is_derivation: \<open>is_derivation S_calculus.derive \<N>i\<close> and
          \<N>i_is_locally_fair: \<open>locally_fair \<N>i SInf SRed\<^sub>I\<close> and
          \<N>i0_entails_bot: \<open>llhd \<N>i \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  shows \<open>\<exists> i. to_AF bot \<in> llnth \<N>i i\<close>
proof -
  have \<open>llhd \<N>i \<subseteq> (\<Union> i. llnth \<N>i i)\<close>
    by (simp add: SUP_upper llhd_is_llnth_0)
  then have \<open>(\<Union> i. llnth \<N>i i) \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    using \<N>i0_entails_bot
    by (meson AF_cons_rel.entails_trans AF_cons_rel.subset_entailed entails_conj_is_entails_disj_if_right_singleton)
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
    by (transfer fixing: Red_F, unfold Sup_llist_def Liminf_llist_def, auto)
  ultimately have \<N>i_inf_entails_bot: \<open>lim_inf \<N>i \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    by (meson AF_cons_rel.entails_subsets subset_iff)
  then have \<N>i_inf_locally_saturated: \<open>locally_saturated SInf SRed\<^sub>I (lim_inf \<N>i)\<close>
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



(*<*)
lemma Un_of_enabled_projection_is_enabled_projection_of_Un: \<open>(\<Union> x. P x) proj\<^sub>J J = (\<Union> x. P x proj\<^sub>J J)\<close>
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

lemma enabled_projection_of_Int_is_Int_of_enabled_projection: \<open>x \<in> (\<Inter> S) proj\<^sub>J J \<Longrightarrow> x \<in> \<Inter> { x proj\<^sub>J J | x. x \<in> S }\<close>
  unfolding enabled_projection_def
  by blast
(*>*)

(* lemma bot_at_i_proj_J_implies_bot_at_liminf_proj_J: \<open>is_derivation S_calculus.derive \<N>i \<Longrightarrow>
                                                          bot \<in> llnth \<N>i i proj\<^sub>J J \<Longrightarrow> bot \<in> lim_inf \<N>i proj\<^sub>J J\<close>
proof -
  assume \<open>is_derivation S_calculus.derive \<N>i\<close> and
         bot_at_i: \<open>bot \<in> llnth \<N>i i proj\<^sub>J J\<close>
  then have \<open>\<forall> i. llnth \<N>i i - llnth \<N>i (Suc i) \<subseteq> SRed\<^sub>F (llnth \<N>i (Suc i))\<close>
    unfolding is_derivation_def S_calculus.derive_def
    by blast
  then show ?thesis
    using bot_at_i
  proof (transfer fixing: Red_F bot J i)
    fix \<N>i
    assume llength_is_infinity: \<open>llength \<N>i = \<infinity>\<close> and
           \<open>\<forall> i. lnth \<N>i i - lnth \<N>i (Suc i) \<subseteq> SRed\<^sub>F (lnth \<N>i (Suc i))\<close> and
           bot_at_i: \<open>bot \<in> lnth \<N>i i proj\<^sub>J J\<close>
    then have all_at_i_minus_next_i_are_redundant:
              \<open>\<forall> i. \<forall> x \<in> lnth \<N>i i - lnth \<N>i (Suc i). (\<forall> \<J>. fset (A_of x) \<subseteq> total_strip \<J> \<longrightarrow> F_of x \<in> Red_F (lnth \<N>i (Suc i) proj\<^sub>J \<J>)) \<or>
                                                        (\<exists> \<C> \<in> lnth \<N>i (Suc i). F_of \<C> = F_of x \<and> A_of \<C> |\<subset>| A_of x)\<close>
      unfolding SRed\<^sub>F_def
      by force
    then have \<open>\<exists> A. AF.Pair bot A \<in> lnth \<N>i i \<and> fset A \<subseteq> total_strip J\<close>
      using bot_at_i
      unfolding enabled_projection_def enabled_def
      by force
    then obtain A where Pair_bot_A_at_i: \<open>AF.Pair bot A \<in> lnth \<N>i i\<close> and
                        A_in_J: \<open>fset A \<subseteq> total_strip J\<close>
      by blast
    then have \<open>\<exists> B k. B |\<subseteq>| A \<and> k \<ge> i \<and> AF.Pair bot B \<in> lnth \<N>i k \<longrightarrow> (\<forall> C j. j \<ge> i \<and> C |\<subset>| B \<longrightarrow> AF.Pair bot C \<notin> lnth \<N>i j)\<close>
      by blast
    then have \<open>\<exists> B k. \<forall> C j. B |\<subseteq>| A \<and> k \<ge> i \<and> AF.Pair bot B \<in> lnth \<N>i k \<and> j \<ge> i \<and> C |\<subset>| B \<longrightarrow> AF.Pair bot C \<notin> lnth \<N>i j\<close>
      by blast
    then obtain B and k where \<open>\<forall> C j. B |\<subseteq>| A \<and> k \<ge> i \<and> AF.Pair bot B \<in> lnth \<N>i k \<and> j \<ge> i \<and> C |\<subset>| B \<longrightarrow> AF.Pair bot C \<notin> lnth \<N>i j\<close>
      by blast
    then have \<open>B |\<subseteq>| A \<and> k \<ge> i \<and> AF.Pair bot B \<in> lnth \<N>i k \<longrightarrow> (\<forall> C j. j \<ge> i \<and> C |\<subset>| B \<longrightarrow> AF.Pair bot C \<notin> lnth \<N>i j)\<close>
      by blast
    then have \<open>B |\<subseteq>| A \<and> k \<ge> i \<and> AF.Pair bot B \<in> lnth \<N>i k \<and> (\<forall> C j. j \<ge> i \<and> C |\<subset>| B \<longrightarrow> AF.Pair bot C \<notin> lnth \<N>i j)\<close>
      (* TODO: this should be trivial, if the left part of the implication is really true...
       *
       * It seems that the problem is the implication itself... *)
      sorry
    then have B_in_A: \<open>B |\<subseteq>| A\<close> and
              k_ge_i: \<open>k \<ge> i\<close> and
              Pair_bot_B_at_k: \<open>AF.Pair bot B \<in> lnth \<N>i k\<close> and
              no_subset_of_B_in_deriv: \<open>\<forall> C j. j \<ge> i \<and> C |\<subset>| B \<longrightarrow> AF.Pair bot C \<notin> lnth \<N>i j\<close>
      by blast+
    then have B_in_J: \<open>fset B \<subseteq> total_strip J\<close>
      by (meson A_in_J dual_order.trans less_eq_fset.rep_eq)
    then have \<open>\<forall> j \<ge> k. AF.Pair bot B \<in> lnth \<N>i j\<close>
    proof (intro allI impI)
      fix j
      assume k_le_j: \<open>k \<le> j\<close>
      then show \<open>AF.Pair bot B \<in> lnth \<N>i j\<close>
      proof (induct j rule: full_nat_induct)
        case less: (1 n)
        then show ?case
        proof (cases \<open>k = n\<close>)
          case True
          then show ?thesis
            using Pair_bot_B_at_k k_le_j less.hyps not_less_eq_eq
            by blast
        next
          case False
          then have j_lt_n: \<open>k < n\<close>
            using less.prems
            by linarith
          then have n_positive: \<open>n > 0\<close>
            using zero_less_iff_neq_zero
            by blast
          then show ?thesis
          proof (cases \<open>B = {||}\<close>)
            case True
            then show ?thesis
              using all_at_i_minus_next_i_are_redundant[rule_format, where ?i=\<open>n - 1\<close> and ?x=\<open>AF.Pair bot B\<close>]
                    False complete less.hyps less.prems
              by auto
          next
            case False
            then show ?thesis
              using all_at_i_minus_next_i_are_redundant[rule_format, where ?i=\<open>n - 1\<close> and ?x=\<open>AF.Pair bot B\<close>]
              by (smt (z3) AF.exhaust AF.sel(1) AF.sel(2) B_in_J Diff_iff One_nat_def Suc_leI Suc_le_mono Suc_pred B_in_A k_ge_i
                           Pair_bot_B_at_k no_subset_of_B_in_deriv complete j_lt_n le_Suc_eq le_trans less.hyps n_positive)
          qed
        qed
      qed
    qed
    then have \<open>AF.Pair bot B \<in> (\<Union> i. \<Inter> { lnth \<N>i j | j. j \<ge> i })\<close>
      by blast
    then have \<open>bot \<in> (\<Union> i. \<Inter> (lnth \<N>i ` { j. i \<le> j })) proj\<^sub>J J\<close>
      using B_in_J
      unfolding enabled_projection_def enabled_def
      (* /!\ A bit slow /!\ *)
      by (smt (verit) AF.sel(1) AF.sel(2) INT_I Inter_iff UN_iff mem_Collect_eq)
    then show \<open>bot \<in> Liminf_llist \<N>i proj\<^sub>J J\<close>
      using llength_is_infinity
      unfolding Liminf_llist_def
      by auto
  qed
qed *)

(* lemma inf_from_limit_all_redundant: \<open>J \<Turnstile>\<^sub>p limit \<N>i \<Longrightarrow> Inf_from (limit \<N>i proj\<^sub>J J) \<subseteq> (\<Union> i. Red_I (llnth \<N>i i proj\<^sub>J J)) \<Longrightarrow> S_calculus.fair \<N>i\<close>
  unfolding S_calculus.weakly_fair_def
proof (transfer fixing: bot J Inf Red_I, intro subsetI)
  fix \<N>i \<iota>\<^sub>S
  assume length_\<N>i_is_infinite: \<open>llength \<N>i = \<infinity>\<close> and
         J_prop_model_of_lim_inf: \<open>J \<Turnstile>\<^sub>p Liminf_llist \<N>i\<close> and
         \<open>Inf_from (Liminf_llist \<N>i proj\<^sub>J J) \<subseteq> (\<Union> i. Red_I (lnth \<N>i i proj\<^sub>J J))\<close> and
         \<open>\<iota>\<^sub>S \<in> S_calculus.Inf_from (Liminf_llist \<N>i)\<close>
  then have \<iota>\<^sub>S_is_splitting_rule: \<open>Splitting_rules \<iota>\<^sub>S\<close> and
            prems_of_\<iota>\<^sub>S_at_limit: \<open>set (prems_of \<iota>\<^sub>S) \<subseteq> Liminf_llist \<N>i\<close> and
            inf_redundant_at_some_i_if: \<open>\<forall> \<iota>\<^sub>F \<in> Inf. (\<forall> C \<in> set (prems_of \<iota>\<^sub>F). \<exists> \<C> \<in> Liminf_llist \<N>i. C = F_of \<C> \<and> enabled \<C> J) \<longrightarrow>
                                              (\<exists> i. \<iota>\<^sub>F \<in> Red_I (lnth \<N>i i proj\<^sub>J J))\<close>
    unfolding S_calculus.Inf_from_def Inf_from_def enabled_projection_def
    by blast+
  then have \<open>\<exists> i. \<iota>\<^sub>S \<in> SRed\<^sub>I (lnth \<N>i i)\<close>
  proof (cases \<iota>\<^sub>S)
    case (base \<N> D)
    then have \<open>set \<N> \<subseteq> Liminf_llist \<N>i\<close>
      by (metis inference.sel(1) prems_of_\<iota>\<^sub>S_at_limit)
    then have \<open>\<forall> C \<in> set (map F_of \<N>). \<exists> \<C> \<in> Liminf_llist \<N>i. C = F_of \<C> \<and> enabled \<C> J\<close>
      (* Can we prove that?
       *
       * We need to prove that \<open>\<forall> C \<in> set (prems_of \<iota>\<^sub>F). \<exists> \<C> \<in> Liminf_llist \<N>i. C = F_of \<C> \<and> enabled \<C> J\<close>.
       * However, while the \<open>C = F_of \<C>\<close> part is mostly trivial, \<open>enabled \<C> J\<close> is not.
       * *)
      sorry
    then have \<open>\<exists> i. Infer (map F_of \<N>) D \<in> Red_I (lnth \<N>i i proj\<^sub>J J)\<close>
      using inf_redundant_at_some_i_if
      by (simp add: local.base(2))
    then obtain i where \<open>Infer (map F_of \<N>) D \<in> Red_I (lnth \<N>i i proj\<^sub>J J)\<close>
      by blast
    then have \<open>\<forall> \<J>. {base_inf \<N> D} \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (lnth \<N>i i proj\<^sub>J \<J>)\<close>
      (* But can we prove that?
       *
       * We know that \<open>Infer (map F_of \<N>) D \<in> Red_I (lnth \<N>i i proj\<^sub>J J)\<close> but here we need to prove that
       * \<open>Infer (map F_of \<N>) D \<in> Red_I (lnth \<N>i i proj\<^sub>J \<J>)\<close> for all \<J> such that \<open>F_of ` \<N> \<subseteq> total_strip J\<close>.
       * *)
    proof (intro allI subsetI)
      fix \<iota>\<^sub>F J'
      assume \<open>\<iota>\<^sub>F \<in> {base_inf \<N> D} \<iota>proj\<^sub>J J'\<close>
      then have \<open>\<iota>\<^sub>F = Infer (map F_of \<N>) D\<close> and
                \<open>enabled_inf (base_inf \<N> D) J'\<close>
        unfolding enabled_projection_Inf_def
        using \<iota>F_of_def
        by force+
      then show \<open>\<iota>\<^sub>F \<in> Red_I (lnth \<N>i i proj\<^sub>J J')\<close>
        sorry
    qed
    then show ?thesis
      unfolding SRed\<^sub>I_def
      using base
      by auto
  next
    case (unsat \<N>)
    then show ?thesis
      sorry
  qed
  then show \<open>\<iota>\<^sub>S \<in> Sup_llist (lmap SRed\<^sub>I \<N>i)\<close>
    unfolding Sup_llist_def
    by (simp add: length_\<N>i_is_infinite)
qed *)

(* TODO: This is the second proof for theorem 28.
 * Currently, proof 1 is done, but this proof appears to be more troublesome.
 * See later, maybe towards the end of my internship, if this is actually doable.
 *
 * (* Report theorem 28 (proof 2) *)
theorem S_calculus_strong_dynamically_complete2:
  assumes F_statically_complete: \<open>statically_complete_calculus bot Inf (\<Turnstile>) Red_I Red_F\<close> and
          \<N>i_is_derivation: \<open>is_derivation S_calculus.derive \<N>i\<close> and
          \<N>i_is_locally_fair: \<open>locally_fair \<N>i SInf SRed\<^sub>I\<close> and
          \<N>i0_entails_bot: \<open>llhd \<N>i \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  shows \<open>\<exists> i. to_AF bot \<in> llnth \<N>i i\<close>
  using \<N>i_is_locally_fair
  unfolding locally_fair_def
proof (elim disjE)
  show \<open>\<exists> i. to_AF bot \<in> llnth \<N>i i \<Longrightarrow> \<exists> i. to_AF bot \<in> llnth \<N>i i\<close>
    by blast
next
  assume \<open>\<exists> J. J \<Turnstile>\<^sub>p limit \<N>i \<and> Inf_from (limit \<N>i proj\<^sub>J J) \<subseteq> (\<Union> i. Red_I (llnth \<N>i i proj\<^sub>J J))\<close>
  then obtain J where J_prop_model_of_limit_\<N>i: \<open>J \<Turnstile>\<^sub>p limit \<N>i\<close> and
                      all_inf_from_limit_are_redundant: \<open>Inf_from (limit \<N>i proj\<^sub>J J) \<subseteq> (\<Union> i. Red_I (llnth \<N>i i proj\<^sub>J J))\<close>
    by blast
  have \<open>\<exists> i. bot \<in> llnth \<N>i i proj\<^sub>J J\<close>
    using S_calculus_dynamically_complete[OF F_statically_complete,
                                          unfolded dynamically_complete_calculus_def dynamically_complete_calculus_axioms_def,
                                          THEN conjunct2, rule_format,
                                          OF \<N>i_is_derivation
                                             inf_from_limit_all_redundant[OF J_prop_model_of_limit_\<N>i all_inf_from_limit_are_redundant]
                                             \<N>i0_entails_bot]
    using enabled_projection_def ex_in_conv to_AF_proj_J
    by fastforce
  then obtain i where \<open>bot \<in> llnth \<N>i i proj\<^sub>J J\<close>
    by blast
  then have \<open>bot \<in> limit \<N>i proj\<^sub>J J\<close>
    using bot_at_i_proj_J_implies_bot_at_liminf_proj_J[OF \<N>i_is_derivation]
    by blast
  then show \<open>\<exists> i. to_AF bot \<in> llnth \<N>i i\<close>
    using J_prop_model_of_limit_\<N>i enabled_projection_def propositional_model_def propositional_projection_def
    by auto
qed *)

end (* context splitting_calculus *)



(* (* NOTE: see if we actually do this *)
subsection \<open>Full splitting calculus\<close>

text \<open>
  We now put everything together to form the splitting calculus defined in the article.
\<close>

locale full_splitting_calculus = splitting_calculus_extensions bot Inf entails entails_sound Red_I Red_F V fml asn +
                                 splitting_calculus_with_simps bot Inf entails entails_sound Red_I Red_F V fml asn
  for bot :: 'f and
      Inf :: \<open>'f inference set\<close> and
      entails :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) and
      entails_sound :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50) and
      Red_I :: \<open>'f set \<Rightarrow> 'f inference set\<close> and
      Red_F :: \<open>'f set \<Rightarrow> 'f set\<close> and
      V :: \<open>'v :: countable itself\<close> and
      fml :: \<open>'v \<Rightarrow> 'f\<close> and
      asn :: \<open>'f sign \<Rightarrow> 'v sign set\<close>
begin

(* TODO: define Splitting_Inf which allows for simplification over premises of inferences in SInf2 *)
(* TODO: prove that theorem 14 holds for Splitting_Inf *)
(* TODO: prove that lemma 13 holds for Splitting_Inf *)

end (* locale full_splitting_calculus *)
*)


end (* theory Splitting_Calculi *)
