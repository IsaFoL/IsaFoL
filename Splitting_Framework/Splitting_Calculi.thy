theory Splitting_Calculi
  imports
    Preliminaries_With_Zorn
begin

locale splitting_calculus = AF_calculus bot Inf entails entails_sound Red_I Red_F V fml
  for
    bot :: 'f and
    Inf :: \<open>'f inference set\<close> and
    entails :: \<open>[ 'f set, 'f set ] \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) and
    entails_sound :: \<open>[ 'f set, 'f set ] \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50) and
    Red_I :: \<open>'f set \<Rightarrow> 'f inference set\<close> and
    Red_F :: \<open>'f set \<Rightarrow> 'f set\<close> and
    V :: \<open>'v :: countable itself\<close> and
    fml :: \<open>'v \<Rightarrow> 'f\<close>
  + assumes
      (* D6 *)
      entails_sound_nontrivial: \<open>\<not> {} \<Turnstile>s {}\<close> and
      (* R5 *)
      reducedness: \<open>Inf_between UNIV (Red_F N) \<subseteq> Red_I N\<close> and
      (* R6 *)
      complete: \<open>bot \<notin> Red_F N\<close> and
      (* R7 *)
      all_red_to_bot: \<open>\<C> \<noteq> bot \<Longrightarrow> \<C> \<in> Red_F {bot}\<close>
begin

(* Propositional clauses are of the form \<open>\<bottom> \<leftarrow> A\<close> *)
abbreviation propositional_clause :: \<open>('f, 'v) AF \<Rightarrow> bool\<close> where
  \<open>propositional_clause \<C> \<equiv> F_of \<C> = bot\<close>

(* Inference rules *)

(* The basic SInf inference system, with the two basic rules BASE and UNSAT.
 *
 * \<open>S \<iota>\<close> means that \<open>\<iota>\<close> is an inference rule of the system S *)
inductive S :: \<open>('f, 'v) AF inference \<Rightarrow> bool\<close> where
  base: \<open>\<lbrakk> Infer (map F_of \<N>) D \<in> Inf \<rbrakk> \<Longrightarrow> S (Infer \<N> (Pair D (ffUnion (fset_of_list (map A_of \<N>)))))\<close>
| unsat: \<open>\<lbrakk> \<forall> x \<in> set \<N>. propositional_clause x; set \<N> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}; \<N> \<noteq> [] \<rbrakk> \<Longrightarrow> S (Infer \<N> (to_AF bot))\<close>
     (* NOTE: can we have that \<open>\<N>\<close> is \<open>[]\<close>? *)
(* | strong_unsat: \<open>\<lbrakk> \<forall> x \<in> set \<N>. propositional_clause x; set \<N> \<Turnstile>s\<^sub>A\<^sub>F {to_AF bot} \<rbrakk> \<Longrightarrow> S (Infer \<N> (to_AF bot))\<close>
| approx: \<open>\<lbrakk> a \<in> asn (to_F \<C>) \<rbrakk> \<Longrightarrow> S (Infer [\<C>] (Pair bot (finsert (neg a) (to_A \<C>))))\<close>
| tauto: \<open>\<lbrakk> \<not> propositional_clause \<C>; {} \<Turnstile>s\<^sub>A\<^sub>F {\<C>} \<rbrakk> \<Longrightarrow> S (Infer [] \<C>)\<close> *)

(* All the simplification rules of the SInf inference system: SPLIT, COLLECT and TRIM. *)
(* inductive S_simps :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close>
  (infix \<open>\<equiv>\<^sub>S\<close> 50) where
  collect: \<open>\<lbrakk> \<not> propositional_clause \<C>; \<N> \<Turnstile>s\<^sub>A\<^sub>F {Pair bot (to_A \<C>)} \<rbrakk> \<Longrightarrow> \<N> \<union> {\<C>} \<equiv>\<^sub>S \<N>\<close> |
  trim: \<open>\<lbrakk> \<not> propositional_clause \<C>; to_A \<C> = A |\<union>| B; \<N> \<union> {Pair bot A} \<Turnstile>s\<^sub>A\<^sub>F {Pair bot B} \<rbrakk> \<Longrightarrow> \<N> \<union> {\<C>} \<equiv>\<^sub>S \<N> \<union> {Pair (to_F \<C>) B}\<close> |
        (* Should we require here that A and B be non empty? It doesn't really make sense to apply those rules
        * if this is not the case, though it does not cause any error... *)
  split: \<open>\<lbrakk> \<not> propositional_clause \<C>; split C Cs \<rbrakk> \<Longrightarrow> \<N> \<union> {\<C>} \<equiv>\<^sub>S \<N> \<union> {Pair bot (Abs_fset (neg ` snd ` Cs))} \<union> {Pair C {|neg a|} | C a. (C, a) \<in> Cs}\<close>

inductive_set SInf :: \<open>('f, 'v) AF inference set\<close> where
  infer: \<open>S I \<Longrightarrow> I \<in> SInf\<close> |
  simp: \<open>\<lbrakk> set P \<equiv>\<^sub>S set P'; Infer P C \<in> SInf \<rbrakk> \<Longrightarrow> Infer P' C \<in> SInf\<close> *)

abbreviation SInf :: \<open>('f, 'v) AF inference set\<close> where
  \<open>SInf \<equiv> {I. S I}\<close>

lemma F_of_to_AF [simp]: \<open>F_of (to_AF \<C>) = \<C>\<close>
  unfolding to_AF_def
  by auto

lemma F_of_propositional_clauses [simp]: \<open>(\<forall> x \<in> set \<N>. propositional_clause x) \<Longrightarrow> map F_of \<N> = map (\<lambda> _. bot) \<N>\<close>
  using map_eq_conv
  by blast

lemma set_map_is_image: \<open>set (map f l) = f ` set l\<close>
  by fastforce

(* Report lemma 13 1/2 *)
lemma SInf_commutes_Inf1: \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J \<subseteq> Inf_from (\<N> proj\<^sub>J J)\<close>
proof (intro subsetI)
  fix x
  assume bot_not_in_proj: \<open>bot \<notin> \<N> proj\<^sub>J J\<close> and
         x_is_inf: \<open>x \<in> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J\<close>

  have no_enabled_prop_clause_in_\<N>: \<open>\<forall> \<C> \<in> \<N>. enabled \<C> J \<longrightarrow> \<not> propositional_clause \<C>\<close>
    using bot_not_in_proj
    unfolding enabled_projection_def
    by blast

  obtain \<iota> where x_is: \<open>x = \<iota>F_of \<iota>\<close> and
                 \<iota>_is_inf: \<open>\<iota> \<in> inference_system.Inf_from SInf \<N>\<close> and
                 \<iota>_is_enabled: \<open>enabled_inf \<iota> J\<close>
    using x_is_inf enabled_projection_Inf_def
    by auto
  then have \<iota>_in_S: \<open>S \<iota>\<close>
    by (simp add: inference_system.Inf_from_def)
  moreover have prems_of_\<iota>_subset_\<N>: \<open>set (prems_of \<iota>) \<subseteq> \<N>\<close>
    using \<iota>_is_inf
    by (simp add: inference_system.Inf_from_def)
  moreover have \<open>\<iota>F_of \<iota> \<in> Inf\<close>
    unfolding \<iota>F_of_def
  proof (cases \<iota> rule: S.cases)
    (* NOTE: using \<open>case ...\<close> does not work here because of the first case.
     * May this come from the definition of \<open>S\<close>? *)
    show \<open>S \<iota>\<close>
      by (simp add: \<iota>_in_S)
  next
    fix \<N> D
    assume \<iota>_def: \<open>\<iota> = Infer \<N> (AF.Pair D (ffUnion (fset_of_list (map A_of \<N>))))\<close>
       and inf_from_\<N>_to_D: \<open>Infer (map F_of \<N>) D \<in> Inf\<close>
    show \<open>Infer (map F_of (prems_of \<iota>)) (F_of (concl_of \<iota>)) \<in> Inf\<close>
      by (auto simp add: \<iota>_def inf_from_\<N>_to_D)
  next
    fix \<N> D
    assume \<iota>_def: \<open>\<iota> = Infer \<N> (to_AF bot)\<close>
       and all_clauses_in_\<N>_propositional: \<open>\<forall> \<C> \<in> set \<N>. propositional_clause \<C>\<close>
       and \<open>set \<N> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
       and \<N>_not_empty: \<open>\<N> \<noteq> []\<close>
    moreover have \<open>enabled_inf \<iota> J\<close>
      using \<iota>_is_enabled
      by fastforce
    then have \<open>\<forall> \<C> \<in> set \<N>. \<not> propositional_clause \<C>\<close>
      by (metis \<iota>_def enabled_inf_def inference.sel(1) no_enabled_prop_clause_in_\<N> prems_of_\<iota>_subset_\<N> subset_eq)
    then have \<open>False\<close>
      using all_clauses_in_\<N>_propositional \<N>_not_empty
      by fastforce
    ultimately show \<open>Infer (map F_of (prems_of \<iota>)) (F_of (concl_of \<iota>)) \<in> Inf\<close>
      by blast
  qed
  moreover have \<open>set (prems_of (\<iota>F_of \<iota>)) \<subseteq> \<N> proj\<^sub>J J\<close>
    using \<iota>_is_enabled prems_of_\<iota>_subset_\<N>
    by (auto simp add: enabled_inf_def enabled_projection_def \<iota>F_of_def)
  ultimately have \<open>\<iota>F_of \<iota> \<in> Inf_from (\<N> proj\<^sub>J J)\<close>
    by (simp add: Inf_from_def)
  then show \<open>x \<in> Inf_from (\<N> proj\<^sub>J J)\<close>
    by (simp add: x_is)
qed

(* Report lemma 13 2/2 *)
lemma SInf_commutes_Inf2: \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> Inf_from (\<N> proj\<^sub>J J) \<subseteq> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J\<close>
proof (intro subsetI)
  fix \<iota>
  assume bot_not_in_proj: \<open>bot \<notin> \<N> proj\<^sub>J J\<close> and
         \<iota>_in_inf: \<open>\<iota> \<in> Inf_from (\<N> proj\<^sub>J J)\<close>

  have \<iota>_is_inf: \<open>\<iota> \<in> Inf\<close>
    using Inf_if_Inf_from \<iota>_in_inf
    by blast
  moreover have \<open>set (prems_of \<iota>) \<subseteq> \<N> proj\<^sub>J J\<close>
    using Inf_from_def \<iota>_in_inf
    by auto
  then have all_prems_enabled: \<open>set (prems_of \<iota>) \<subseteq> {F_of \<C> | \<C>. \<C> \<in> \<N> \<and> enabled \<C> J}\<close>
    unfolding enabled_projection_def
    by simp
  moreover obtain \<iota>' where \<iota>'_def: \<open>\<iota> = \<iota>F_of \<iota>'\<close>
    by (metis F_of_to_AF \<iota>F_of_def ex_map_conv inference.exhaust_sel inference.sel(1) inference.sel(2))
  then have \<iota>'_in_S: \<open>S \<iota>'\<close>
    sorry
  moreover have \<open>prems_of \<iota> = map F_of (prems_of \<iota>')\<close>
    using \<iota>'_def
    unfolding \<iota>F_of_def
    by auto
  then have prems_\<iota>'_all_enabled: \<open>set (prems_of \<iota>') \<subseteq> { \<C> \<in> \<N>. enabled \<C> J }\<close>
    sorry
  then have \<open>\<forall> \<C> \<in> set (prems_of \<iota>'). enabled \<C> J\<close>
    by blast
  then have \<open>enabled_inf \<iota>' J\<close>
    using enabled_inf_def
    by auto
  moreover have \<open>\<iota>' \<in> inference_system.Inf_from SInf \<N>\<close>
    using \<iota>'_in_S prems_\<iota>'_all_enabled inference_system.Inf_from_def
    by fast
  ultimately have \<open>\<exists> \<iota>'. \<iota> = \<iota>F_of \<iota>' \<and> \<iota>' \<in> inference_system.Inf_from SInf \<N> \<and> enabled_inf \<iota>' J\<close>
    using \<iota>'_def
    by blast
  then show \<open>\<iota> \<in> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J\<close>
    unfolding enabled_projection_Inf_def
    by simp
qed

end (* locale splitting_calculus *)

end (* theory Splitting_Calculi *)
