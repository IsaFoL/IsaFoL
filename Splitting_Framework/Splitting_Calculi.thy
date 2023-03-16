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
  + fixes
      asn :: \<open>'f \<Rightarrow> 'v sign set\<close> and
      splittable :: \<open>[ 'f, 'f set ] \<Rightarrow> bool\<close>
    assumes
      (* D6 *)
      entails_sound_nontrivial: \<open>\<not> {} \<Turnstile>s {}\<close> and
      (* R5 *)
      reducedness: \<open>Inf_between UNIV (Red_F N) \<subseteq> Red_I N\<close> and
      (* R6 *)
      complete: \<open>bot \<notin> Red_F N\<close> and
      (* R7 *)
      all_red_to_bot: \<open>\<C> \<noteq> bot \<Longrightarrow> \<C> \<in> Red_F {bot}\<close> and

      splittable_if1: \<open>splittable \<C> \<N> \<Longrightarrow> card \<N> \<ge> 2\<close> and
      splittable_if2: \<open>splittable \<C> \<N> \<Longrightarrow> {\<C>} \<Turnstile>s \<N>\<close> and
      splittable_if3: \<open>splittable \<C> \<N> \<Longrightarrow> \<forall> C \<in> \<N>. \<C> \<in> Red_F {C}\<close>
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
  \<open>SInf ≡ {I. S I}\<close>

end (* locale splitting_calculus *)

end (* theory Splitting_Calculi *)
