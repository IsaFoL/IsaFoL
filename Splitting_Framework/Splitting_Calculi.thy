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
  base: \<open>\<lbrakk> Infer (map to_F \<N>) D \<in> Inf \<rbrakk> \<Longrightarrow> S (Infer \<N> (Pair D (ffUnion (fset_of_list (map to_A \<N>)))))\<close>
| unsat: \<open>\<lbrakk> \<forall> x \<in> set \<N>. propositional_clause x; set \<N> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<rbrakk> \<Longrightarrow> S (Infer \<N> (to_AF bot))\<close>
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

lemma SInf_cong_if:
  assumes \<open>map F_of (prems_of \<iota>) = map F_of (prems_of \<iota>')\<close>
      and \<open>F_of (concl_of \<iota>) = F_of (concl_of \<iota>')\<close>
      and \<open>\<iota>' \<in> inference_system.Inf_from SInf \<N>\<close>
      and \<open>enabled_inf \<iota>' J\<close>
  shows \<open>\<iota> \<in> inference_system.Inf_from SInf \<N>\<close>
proof -
  have \<open>S \<iota>'\<close>
    using assms(3)
    by (simp add: inference_system.Inf_from_def)
  moreover have \<open>enabled_inf \<iota>' J\<close>
    using assms(3) assms(4)
    by linarith
  show \<open>\<iota> \<in> inference_system.Inf_from SInf \<N>\<close>
    sorry
qed


(* Report lemma 13 1/2 *)
lemma SInf_commutes_Inf1: \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J \<subseteq> Inf_from (\<N> proj\<^sub>J J)\<close>
proof (intro subsetI)
  fix x
  assume 1: \<open>bot \<notin> \<N> proj\<^sub>J J\<close> and
         2: \<open>x \<in> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J\<close>

  have no_enabled_prop_clause_in_\<N>: \<open>\<forall> \<C> \<in> \<N>. enabled \<C> J \<longrightarrow> \<not> propositional_clause \<C>\<close>
    using "1"
    unfolding enabled_projection_def
    by blast

  obtain \<iota> where x_is: \<open>x = \<iota>F_of \<iota>\<close>
    using "2" enabled_projection_Inf_def
    by auto
  have \<open>\<iota> \<in> inference_system.Inf_from SInf \<N>\<close>
    using "2"
    unfolding enabled_projection_Inf_def \<iota>F_of_def x_is
    apply auto
    sorry
  moreover have \<iota>_is_enabled: \<open>enabled_inf \<iota> J\<close>
    using "2"
    unfolding enabled_projection_Inf_def x_is
    sorry
  moreover have \<open>S \<iota>\<close>
    using calculation(1)
    by (simp add: inference_system.Inf_from_def)
  moreover have prems_of_\<iota>_subset_\<N>: \<open>set (prems_of \<iota>) \<subseteq> \<N>\<close>
    using calculation(1)
    by (simp add: inference_system.Inf_from_def)
  moreover have \<open>\<iota>F_of \<iota> \<in> Inf\<close>
    unfolding \<iota>F_of_def
    sorry
  moreover have \<open>set (prems_of (\<iota>F_of \<iota>)) \<subseteq> \<N> proj\<^sub>J J\<close>
    using \<iota>_is_enabled prems_of_\<iota>_subset_\<N>
    by (auto simp add: enabled_inf_def enabled_projection_def \<iota>F_of_def)
  ultimately have \<open>\<iota>F_of \<iota> \<in> Inf_from (\<N> proj\<^sub>J J)\<close>
    by (simp add: Inf_from_def)
  then show \<open>x \<in> Inf_from (\<N> proj\<^sub>J J)\<close>
    by (simp add: x_is)
qed

(* Report lemma 13 2/2 *)
lemma SInf_commutes_Inf2: \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> Inf_from (\<N> proj\<^sub>J J) \<subseteq> (inference_system.Inf_from SIng \<N>) \<iota>proj\<^sub>J J\<close>
  sorry

end (* locale splitting_calculus *)

end (* theory Splitting_Calculi *)
