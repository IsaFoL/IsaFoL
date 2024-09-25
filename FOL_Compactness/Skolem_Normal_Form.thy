(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023 *)

theory Skolem_Normal_Form
imports
  Prenex_Normal_Form
begin

lemma holds_exists:
  assumes \<open>is_interpretation (functions_term t, preds) (I :: (nat, nat) term intrp)\<close> and
    \<open>is_valuation I \<beta>\<close> and 
    \<open>I\<^bold>, \<beta> \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x t))\<close>
  shows \<open>I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
proof -
  have \<open>(\<lambda>v. \<lbrakk>subst x t v\<rbrakk>\<^bsup>I,\<beta>\<^esup>) = \<beta>(x := \<lbrakk>t\<rbrakk>\<^bsup>I,\<beta>\<^esup>)\<close>
  proof -
    have "\<forall>n. \<lbrakk>subst x t n\<rbrakk>\<^bsup>I,\<beta>\<^esup> = (\<beta>(x := \<lbrakk>t\<rbrakk>\<^bsup>I,\<beta>\<^esup>)) n"
      by (simp add: subst_def)
    then show ?thesis
      by blast
  qed
  moreover have \<open>\<lbrakk>t\<rbrakk>\<^bsup>I,\<beta>\<^esup> \<in> dom I\<close>
    using assms(1)
  proof (induct t)
    case (Var x)
    then show ?case
      using assms(2) by auto
  next
    case (Fun f ts)
 (*   have \<open>(f, length ts) \<in> functions_term (Fun f ts)\<close>
      by force*)
    then have \<open>u \<in> set ts \<Longrightarrow> \<lbrakk>u\<rbrakk>\<^bsup>I,\<beta>\<^esup> \<in> FOL_Semantics.dom I\<close> for u
      by (smt (z3) UN_iff Un_iff eq_fst_iff functions_term.simps(2) is_interpretation_def)
    then show ?case
      using eval.simps(2) fst_conv imageE length_map list.set_map list_all_set
      sorry
      (* by (smt (verit, del_insts) Fun.prems Un_insert_left functions_term.simps(2) insert_iff
          is_interpretation_def) *)
  qed
  ultimately have \<open>\<exists>a \<in> dom I. I\<^bold>, \<beta>(x := a) \<Turnstile> \<phi>\<close>
    using assms(3) swap_subst_eval[of I \<beta> \<phi> "subst x t"] by auto
  then show ?thesis
    using holds_exists by blast
qed

find_consts "_ set \<Rightarrow> _ list"

definition skolem1 :: "nat \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where
  \<open>skolem1 f x \<phi> = \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Fun f (map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))))\<close>


lemma fvt_var_x_simp: 
  \<open>FVT (Var x \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV \<phi> - {x}))))) = FV \<phi> - {x}\<close>
proof -
  have remove_list: 
    \<open>set (map Var (sorted_list_of_set (FV \<phi> - {x}))) = Var ` (FV \<phi> - {x})\<close>
    using set_map set_sorted_list_of_set using finite_FV by auto
  have \<open>FVT (Var x \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV \<phi> - {x}))))) =
    FVT (Fun f (map Var (sorted_list_of_set (FV \<phi> - {x}))))\<close> 
    by simp
  also have \<open>... = \<Union> (FVT ` set (map Var (sorted_list_of_set (FV \<phi> - {x}))))\<close>
    using term.set(4) by metis
  also have \<open>... = \<Union> (FVT ` Var ` (FV \<phi> - {x}))\<close>
    using remove_list by auto
  also have \<open>... = FV \<phi> - {x}\<close>
    by force
  finally show ?thesis .
qed


(* holds M v p /\
     (Dom M = Dom M') /\
     (!P zs. Pred M P zs = Pred M' P zs) /\
     (!f zs.
          f,LENGTH zs IN functions_form p ==> (Fun M f zs = Fun M' f zs))
     ==> holds M' v p` *)
(* essentially a repeat of holds_indep_intrp_if... needed? 
Seems to be lemma3 in skolem.ml [Larry]*)
lemma holds_indep_intrp_if2:
  fixes I I' :: "'a intrp"
  shows
 \<open>I\<^bold>, \<beta> \<Turnstile> \<phi> \<Longrightarrow> dom I = dom I' \<Longrightarrow>
  (\<forall>p. intrp_rel I p  = intrp_rel I' p) \<Longrightarrow>
  (\<forall>f zs. (f, length zs) \<in> functions_form \<phi> \<longrightarrow> (intrp_fn I f zs = intrp_fn I' f zs)) \<Longrightarrow>
  I'\<^bold>, \<beta> \<Turnstile> \<phi>\<close>
  using holds_indep_intrp_if by blast

lemma fun_upds_prop: \<open>length xs = length zs \<Longrightarrow> \<forall>z\<in>set zs. P z \<Longrightarrow> \<forall>v. P (g v) \<Longrightarrow> \<forall>v. P ((foldr (\<lambda>kv f. fun_upd f (fst kv) (snd kv)) (zip xs zs) g) v)\<close>
proof (induction zs arbitrary: xs g)
  case Nil
  then show ?case
    by simp
next
  case (Cons a zs)
  obtain x xsp where xs_is: \<open>xs = x # xsp\<close>
    using Cons(2) by (metis length_Suc_conv)
  with Cons show ?case
    by auto
qed

(*lemma \<open>(\<forall>kv \<in> set zs. P (f (fst kv) (snd kv))) \<Longrightarrow> (\<forall>v. P (x v)) \<Longrightarrow> (\<forall>v. P (\<lambda>zs (fold (\<lambda>kv f. fun_upd f (fst kv) (snd kv)) zs x)))\<close>*)

lemma \<open>{z. \<exists>y. y \<in> FV \<phi> \<and> z \<in> functions_term (Var y \<cdot> subst x t)} = functions_term t \<or>
   {z. \<exists>y. y \<in> FV \<phi> \<and> z \<in> functions_term (Var y \<cdot> subst x t)} = {}\<close>
proof -
  have \<open>y \<noteq> x \<Longrightarrow> functions_term (Var y \<cdot> subst x t) = {}\<close> for y
    by (simp add: subst_def)
  moreover have \<open>y = x \<Longrightarrow> functions_term (Var y \<cdot> subst x t) = functions_term t\<close> for y
    by simp
  ultimately show ?thesis
    by blast
qed

lemma func_form_subst: \<open>x \<in> FV \<phi> \<Longrightarrow> (f, length ts) \<in> functions_form (\<phi>  \<cdot>\<^sub>f\<^sub>m subst x (Fun f ts))\<close>
proof (induction \<phi> rule: functions_form.induct)
  case 1
  then show ?case by simp
next
  case (2 p ts)
  then show ?case
    by (metis (no_types, lifting) UnCI eval_term.simps(1) formsubst_functions_form 
        functions_term.simps(2) mem_Collect_eq singletonI subst_simps(1))
next
  case (3 \<phi> \<psi>)
  then show ?case
    by auto
next
  case (4 y \<phi>)
  then show ?case
    by (metis (no_types, lifting) UnI2 Un_commute eval_term.simps(1) formsubst_functions_form 
        functions_term.simps(2) mem_Collect_eq singletonI subst_simps(1))
qed
  
end