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

(* Inference rules *)

(* The basic SInf inference system, with the two basic rules BASE and UNSAT.
 *
 * \<open>S \<iota>\<close> means that \<open>\<iota>\<close> is an inference rule of the system S *)
inductive S :: \<open>('f, 'v) AF inference \<Rightarrow> bool\<close> where
  base: \<open>\<lbrakk> Infer (map F_of \<N>) D \<in> Inf \<rbrakk> \<Longrightarrow> S (Infer \<N> (Pair D (ffUnion (fset_of_list (map A_of \<N>)))))\<close>
| unsat: \<open>\<lbrakk> \<forall> x \<in> set \<N>. F_of x = bot; propositionally_unsatisfiable (set \<N>); \<N> \<noteq> [] \<rbrakk> \<Longrightarrow> S (Infer \<N> (to_AF bot))\<close>
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

lemma F_of_propositional_clauses [simp]: \<open>(\<forall> x \<in> set \<N>. F_of x = bot) \<Longrightarrow> map F_of \<N> = map (\<lambda> _. bot) \<N>\<close>
  using map_eq_conv
  by blast

lemma set_map_is_image: \<open>set (map f l) = f ` set l\<close>
  by fastforce

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
  then have \<iota>\<^sub>F_in_S: \<open>S \<iota>\<^sub>F\<close>
    by (simp add: inference_system.Inf_from_def)
  moreover have prems_of_\<iota>\<^sub>F_subset_\<N>: \<open>set (prems_of \<iota>\<^sub>F) \<subseteq> \<N>\<close>
    using \<iota>\<^sub>F_is_inf
    by (simp add: inference_system.Inf_from_def)
  moreover have \<open>\<iota>F_of \<iota>\<^sub>F \<in> Inf\<close>
    unfolding \<iota>F_of_def
  proof (cases \<iota>\<^sub>F rule: S.cases)
    (* NOTE: using \<open>case ...\<close> does not work here because of the first case.
     * May this come from the definition of \<open>S\<close>? *)
    show \<open>S \<iota>\<^sub>F\<close>
      by (simp add: \<iota>\<^sub>F_in_S)
  next
    fix \<N> D
    assume \<iota>\<^sub>F_def: \<open>\<iota>\<^sub>F = Infer \<N> (AF.Pair D (ffUnion (fset_of_list (map A_of \<N>))))\<close>
       and inf_from_\<N>_to_D: \<open>Infer (map F_of \<N>) D \<in> Inf\<close>
    show \<open>Infer (map F_of (prems_of \<iota>\<^sub>F)) (F_of (concl_of \<iota>\<^sub>F)) \<in> Inf\<close>
      by (auto simp add: \<iota>\<^sub>F_def inf_from_\<N>_to_D)
  next
    fix \<N> D
    assume \<iota>\<^sub>F_def: \<open>\<iota>\<^sub>F = Infer \<N> (to_AF bot)\<close>
       and all_clauses_in_\<N>_propositional: \<open>\<forall> \<C> \<in> set \<N>. F_of \<C> = bot\<close>
       and \<open>propositionally_unsatisfiable (set \<N>)\<close>
       and \<N>_not_empty: \<open>\<N> \<noteq> []\<close>
    moreover have \<open>enabled_inf \<iota>\<^sub>F J\<close>
      using \<iota>\<^sub>F_is_enabled
      by fastforce
    then have \<open>\<forall> \<C> \<in> set \<N>. F_of \<C> \<noteq> bot\<close>
      by (metis \<iota>\<^sub>F_def enabled_inf_def inference.sel(1) no_enabled_prop_clause_in_\<N> prems_of_\<iota>\<^sub>F_subset_\<N> subset_eq)
    then have \<open>False\<close>
      using all_clauses_in_\<N>_propositional \<N>_not_empty
      by fastforce
    ultimately show \<open>Infer (map F_of (prems_of \<iota>\<^sub>F)) (F_of (concl_of \<iota>\<^sub>F)) \<in> Inf\<close>
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

lemma map2_first_is_first [simp]: \<open>length x = length y \<Longrightarrow> map2 (\<lambda>x y. x) x y = x\<close>
  by (metis fst_def map_eq_conv map_fst_zip)

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
(*  then have \<open>\<exists> As. list_all2 (\<lambda> C A. Pair C A \<in> \<N> \<and> enabled (Pair C A) J) (prems_of \<iota>\<^sub>F) As\<close>
     by (simp add: list_all_exists_is_exists_list_all2) *)
(*  then have \<open>\<exists> As. length (prems_of \<iota>\<^sub>F) = length As \<and> (\<forall> (C, A) \<in> set (zip (prems_of \<iota>\<^sub>F) As). Pair C A \<in> \<N> \<and> enabled (Pair C A) J)\<close>
    by (meson list_all2_iff) *)
  then obtain As where length_As_is_length_prems_\<iota>\<^sub>F: \<open>length (prems_of \<iota>\<^sub>F) = length As\<close> and
                       As_def: \<open>\<forall> (C, A) \<in> set (zip (prems_of \<iota>\<^sub>F) As). Pair C A \<in> \<N> \<and> enabled (Pair C A) J\<close>
    by (smt (verit, del_insts) Ball_set_list_all list_all2_iff list_all_exists_is_exists_list_all2)
  define \<iota>\<^sub>S where
    \<open>\<iota>\<^sub>S \<equiv> Infer [ Pair \<C> A. (\<C>, A) \<leftarrow> zip (prems_of \<iota>\<^sub>F) As ] (Pair (concl_of \<iota>\<^sub>F) (ffUnion (fset_of_list As)))\<close>
  have \<iota>\<^sub>F_is_Inf2: \<open>Infer (map F_of [ Pair \<C> A. (\<C>, A) \<leftarrow> zip (prems_of \<iota>\<^sub>F) As ]) (concl_of \<iota>\<^sub>F) \<in> Inf\<close>
    using length_As_is_length_prems_\<iota>\<^sub>F
    by (auto simp add: \<iota>\<^sub>F_is_Inf)
  then have \<iota>\<^sub>S_is_SInf: \<open>\<iota>\<^sub>S \<in> SInf\<close>
    using S.base[OF \<iota>\<^sub>F_is_Inf2] length_As_is_length_prems_\<iota>\<^sub>F
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

(* Report lemma 13 *)
lemma SInf_commutes_Inf: \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J = Inf_from (\<N> proj\<^sub>J J)\<close>
  using SInf_commutes_Inf1 SInf_commutes_Inf2
  by blast

lemma fset_ffUnion_subset_has_all_fsets_subset: \<open>fset (ffUnion A) \<subseteq> B \<Longrightarrow> fBall A (\<lambda> x. fset x \<subseteq> B)\<close>
proof (intro fBallI subsetI)
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
qed

lemma fBall_fset_of_list: \<open>fBall (fset_of_list A) P \<longleftrightarrow> Ball (set A) P\<close>
  by (simp add: fBall.rep_eq fset_of_list.rep_eq)

(* Report theorem 14 *)
theorem Sinf_sound_wrt_entails_sound:
  \<open>\<lbrakk> \<forall> x \<in> set \<N>. F_of x = bot; propositionally_unsatisfiable (set \<N>); \<N> \<noteq> [] \<rbrakk> \<Longrightarrow> set \<N> \<Turnstile>s\<^sub>A\<^sub>F {to_AF bot}\<close>
  \<open>\<lbrakk> Infer (map F_of \<N>) D \<in> Inf \<rbrakk> \<Longrightarrow> set \<N> \<Turnstile>s\<^sub>A\<^sub>F {AF.Pair D (ffUnion (fset_of_list (map A_of \<N>)))}\<close>
proof -
  assume heads_of_\<N>_are_bot: \<open>\<forall> x \<in> set \<N>. F_of x = bot\<close> and
         \<N>_is_prop_unsat: \<open>propositionally_unsatisfiable (set \<N>)\<close> and
         \<N>_not_empty: \<open>\<N> \<noteq> []\<close>
  then have \<open>proj\<^sub>\<bottom> (set \<N>) = set \<N>\<close>
    using heads_of_\<N>_are_bot propositional_projection_def
    by blast
  then have \<open>\<forall> J. bot \<in> (set \<N>) proj\<^sub>J J\<close>
    using \<N>_is_prop_unsat propositional_model_def propositionally_unsatisfiable_def
    by force
  then show \<open>set \<N> \<Turnstile>s\<^sub>A\<^sub>F {to_AF bot}\<close>
    unfolding AF_entails_sound_def sound_cons.entails_neg_def
    by (metis (no_types, lifting) UnCI empty_subsetI image_eqI insert_subset mem_Collect_eq sound_cons.bot_entails_empty sound_cons.entails_subsets)
next
  assume \<open>Infer (map F_of \<N>) D \<in> Inf\<close>
  then have inf_is_sound: \<open>set (map F_of \<N>) \<Turnstile>s {D}\<close>
    using sound
    by fastforce
  then show \<open>set \<N> \<Turnstile>s\<^sub>A\<^sub>F {Pair D (ffUnion (fset_of_list (map A_of \<N>)))}\<close>
    unfolding AF_entails_sound_def sound_cons.entails_neg_def
  proof (intro allI impI)
    fix J
    assume Pair_D_A_of_\<N>_is_enabled: \<open>enabled_set {AF.Pair D (ffUnion (fset_of_list (map A_of \<N>)))} J\<close>
    then have \<open>F_of ` {AF.Pair D (ffUnion (fset_of_list (map A_of \<N>)))} = {D}\<close>
      by simp
    moreover have \<open>fset (ffUnion (fset_of_list (map A_of \<N>))) \<subseteq> total_strip J\<close>
      using Pair_D_A_of_\<N>_is_enabled
      unfolding enabled_set_def enabled_def
      by auto
    then have \<open>fBall (fset_of_list (map A_of \<N>)) (\<lambda> As. fset As \<subseteq> total_strip J)\<close>
      using fset_ffUnion_subset_has_all_fsets_subset
      by fast
    then have \<open>\<forall> As \<in> set (map A_of \<N>). fset As \<subseteq> total_strip J\<close>
      using fBall_fset_of_list
      by metis
    then have \<open>\<forall> \<C> \<in> set \<N>. enabled \<C> J\<close>
      unfolding enabled_def
      by simp
    then have \<open>set \<N> proj\<^sub>J J = F_of ` set \<N>\<close>
      unfolding enabled_projection_def
      by auto
    moreover have \<open>{C. Pos C \<in> fml_ext ` total_strip J \<union> Pos ` F_of ` set \<N>} \<Turnstile>s {D}\<close>
      using inf_is_sound
      by (smt (verit, ccfv_threshold) UnCI imageI mem_Collect_eq set_map_is_image sound_cons.entails_subsets subsetI)
    moreover have \<open>{C. Neg C \<in> Pos ` F_of ` {AF.Pair D (ffUnion (fset_of_list (map A_of \<N>)))}} = {}\<close>
      by fast
    ultimately show \<open>{C. Pos C \<in> fml_ext ` total_strip J \<union> Pos ` (set \<N> proj\<^sub>J J)} \<union>
                     {C. Neg C \<in> Pos ` F_of ` {AF.Pair D (ffUnion (fset_of_list (map A_of \<N>)))}} \<Turnstile>s
                     {C. Pos C \<in> Pos ` F_of ` {AF.Pair D (ffUnion (fset_of_list (map A_of \<N>)))}} \<union>
                     {C. Neg C \<in> fml_ext ` total_strip J \<union> Pos ` (set \<N> proj\<^sub>J J)}\<close>
      (* Careful, this one is a little bit slow (enough to be noticed) *)
      by (smt (verit, del_insts) UnCI empty_subsetI image_insert insert_subset mem_Collect_eq sound_cons.entails_subsets subsetI)
  qed
qed

end (* locale splitting_calculus *)

end (* theory Splitting_Calculi *)
