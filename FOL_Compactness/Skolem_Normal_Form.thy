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
    \<open>I, \<beta> \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x t))\<close>
  shows \<open>I, \<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
proof -
  have \<open>(\<lambda>v. \<lbrakk>subst x t v\<rbrakk>\<^bsup>I,\<beta>\<^esup>) = \<beta>(x := \<lbrakk>t\<rbrakk>\<^bsup>I,\<beta>\<^esup>)\<close>
  proof -
    have "\<forall>n. \<lbrakk>subst x t n\<rbrakk>\<^bsup>I,\<beta>\<^esup> = (\<beta>(x := \<lbrakk>t\<rbrakk>\<^bsup>I,\<beta>\<^esup>)) n"
      by (simp add: subst_def)
    then show ?thesis
      by blast
  qed
  moreover have \<open>\<lbrakk>t\<rbrakk>\<^bsup>I,\<beta>\<^esup> \<in> dom I\<close>
    using interpretation_termval[OF assms(1) assms(2)] .
  ultimately have \<open>\<exists>a \<in> dom I. I, \<beta>(x := a) \<Turnstile> \<phi>\<close>
    using assms(3) swap_subst_eval[of I \<beta> \<phi> "subst x t"] by auto
  then show ?thesis
    using holds_exists by blast
qed

find_consts "_ set \<Rightarrow> _ list"

definition skolem1 :: "nat \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where
  \<open>skolem1 f x \<phi> = \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Fun f (map (\<lambda>x. Var x) (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))))\<close>


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
(* essentially a repeat of holds_indep_intrp_if... needed? *)
lemma \<open>(I :: 'a intrp), \<beta> \<Turnstile> \<phi> \<Longrightarrow> dom I = dom (I' :: 'a intrp) \<Longrightarrow>
  (\<forall>p. intrp_rel I p  = intrp_rel I' p) \<Longrightarrow>
  (\<forall>f zs. (f, length zs) \<in> functions_form \<phi> \<longrightarrow> (intrp_fn I f zs = intrp_fn I' f zs)) \<Longrightarrow>
  I', \<beta> \<Turnstile> \<phi>\<close>
  using holds_indep_intrp_if by blast

lemma holds_skolem1: 
  assumes prenex_ex_phi: \<open>is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close> and
    \<open>\<not> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<in> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
  shows \<open>is_prenex (skolem1 f x \<phi>) \<and>
  FV (skolem1 f x \<phi>) = FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<and>
  size (skolem1 f x \<phi>) < size (\<^bold>\<exists>x\<^bold>. \<phi>) \<and>
  predicates_form (skolem1 f x \<phi>) = predicates_form (\<^bold>\<exists>x\<^bold>. \<phi>) \<and>
  functions_form (\<^bold>\<exists>x\<^bold>. \<phi>) \<subseteq> functions_form (skolem1 f x \<phi>) \<and>
  functions_form (skolem1 f x \<phi>) \<subseteq> insert (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) (functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)) \<and>
  (\<forall>(I :: 'a intrp). is_interpretation (language {\<phi>}) I \<and>
    \<not> (dom I = {}) \<and>
    (\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> I, \<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>)) \<longrightarrow>
    (\<exists>(M :: 'a intrp). dom M = dom I \<and>
    intrp_rel M = intrp_rel I \<and>
    (\<forall>g zs. \<not>(g = f) \<or> \<not>(length zs = card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<longrightarrow> intrp_fn M g zs = intrp_fn I g zs) \<and>
    is_interpretation (language {skolem1 f x \<phi>}) M \<and>
    (\<forall>\<beta>. is_valuation M \<beta> \<longrightarrow> M, \<beta> \<Turnstile> (skolem1 f x \<phi>)))) \<and>
  (\<forall>(N :: 'a intrp). is_interpretation (language {skolem1 f x \<phi>}) N \<and>
    \<not> (dom N = {}) \<longrightarrow>
    (\<forall>\<beta>. is_valuation N \<beta> \<and> N, \<beta> \<Turnstile> (skolem1 f x \<phi>) \<longrightarrow> N, \<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>)))
\<close>
proof (clarsimp)
  have \<open>is_prenex (skolem1 f x \<phi>)\<close>
    using prenex_ex_phi prenex_formsubst1
    by (metis form.sel(3) form.sel(6) prenex_imp qfree_no_quantif skolem1_def)

  moreover have \<open>FV (skolem1 f x \<phi>) = FV \<phi> - {x}\<close>
  proof
    show \<open>FV (skolem1 f x \<phi>) \<subseteq> FV \<phi> - {x}\<close>
    proof
      fix z
      assume \<open>z \<in> FV (skolem1 f x \<phi>)\<close>
      then obtain y where y_in: \<open>y \<in> FV \<phi>\<close> and 
        z_in: \<open>z \<in> FVT (Var y \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV \<phi> - {x})))))\<close>
        unfolding skolem1_def using formsubst_fv FV_exists by auto

      have \<open>y \<noteq> x \<Longrightarrow> z = y\<close>
        using z_in subst_def by (metis Term.term.simps(17) eval_term.simps(1) fun_upd_other singletonD)
      then have neq_x: \<open>y \<noteq> x \<Longrightarrow> z \<in> FV \<phi> - {x}\<close>
        using y_in by blast

      have eq_x: \<open>y = x \<Longrightarrow> z \<in> FV \<phi> - {x}\<close>
        using fvt_var_x_simp z_in by blast
      show \<open>z \<in> FV \<phi> - {x}\<close>
        using neq_x eq_x by blast
    qed
  next
    show \<open>FV \<phi> - {x} \<subseteq> FV (skolem1 f x \<phi>)\<close>
    proof
      fix z
      assume z_in: \<open>z \<in> FV \<phi> - {x}\<close>
      then have \<open>FVT (Var z \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>)))))) = {z}\<close>
        by (simp add: subst_def)
      then show \<open>z \<in> FV (skolem1 f x \<phi>)\<close>
        unfolding skolem1_def using z_in formsubst_fv by blast
    qed
  qed

  moreover have \<open>size (skolem1 f x \<phi>) < Suc (Suc (Suc (size \<phi>)))\<close>
    unfolding skolem1_def by (simp add: size_indep_subst)

  moreover have \<open>predicates_form (skolem1 f x \<phi>) = predicates_form \<phi>\<close>
    unfolding skolem1_def using formsubst_predicates by blast

  moreover have \<open>functions_form \<phi> \<subseteq> functions_form (skolem1 f x \<phi>)\<close>
    unfolding skolem1_def by (simp add: formsubst_functions_form)

  moreover have \<open>functions_form (skolem1 f x \<phi>) \<subseteq> (f, card (FV \<phi> - {x})) \<triangleright> functions_form \<phi>\<close>
  proof
    fix g
    assume g_in: \<open>g \<in> functions_form (skolem1 f x \<phi>)\<close>
    then have \<open>g \<in> functions_form \<phi> \<union> {g. \<exists>y. y \<in> FV \<phi> \<and> 
      g \<in> functions_term (Var y \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>)))))))}\<close>
      unfolding skolem1_def using formsubst_functions_form
      by blast
    moreover have \<open>{g. \<exists>y. y \<in> FV \<phi> \<and> g \<in> functions_term (Var y \<cdot> subst x (Fun f (map Var 
      (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>)))))))} \<subseteq> (f, card (FV \<phi> - {x})) \<triangleright> functions_form \<phi>\<close>
    proof
      fix h
      assume \<open>h \<in> {g. \<exists>y. y \<in> FV \<phi> \<and> g \<in> functions_term (Var y \<cdot> subst x (Fun f (map Var 
      (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>)))))))}\<close>
      then obtain y where y_in: \<open>y \<in> FV \<phi>\<close> and h_in: 
        \<open>h \<in> functions_term (Var y \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>)))))))\<close>
        by blast
      have \<open>y \<noteq> x \<Longrightarrow> h \<in> functions_term (Var y)\<close>
        using h_in by (simp add: subst_def)
      then have y_neq_x_case: \<open>y \<noteq> x \<Longrightarrow> h \<in> functions_form \<phi>\<close>
        using y_in by simp
      have \<open>functions_term (Var x \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>))))))) =
        functions_term (Fun f (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>))))))\<close>
        by (simp add: subst_def)
      have len_card: \<open>length (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>))))) = card (FV \<phi> - {x})\<close>
        by simp
      have \<open>\<forall>t \<in> set (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>))))). functions_term t = {}\<close>
      proof
        fix t :: "(nat, nat) term"
        assume \<open>t \<in> set (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>)))))\<close>
        then have \<open>t \<in> Var ` set (sorted_list_of_set (FV \<phi> - {x}))\<close>
          using FV_exists set_sorted_list_of_set finite_FV by auto
        then show \<open>functions_term t = {}\<close>
          by auto
      qed
      then have \<open>functions_term (Fun f (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>)))))) = 
        {(f, card (FV \<phi> - {x}))}\<close>
        using len_card by simp
      then have y_eq_x_case: \<open>y = x \<Longrightarrow> h = (f, card (FV \<phi> - {x}))\<close>
        using y_in h_in by auto
      show \<open>h \<in> (f, card (FV \<phi> - {x})) \<triangleright> functions_form \<phi>\<close>
        using y_neq_x_case y_eq_x_case by blast
    qed
    ultimately show \<open>g \<in> (f, card (FV \<phi> - {x})) \<triangleright> functions_form \<phi>\<close>
      by blast
  qed

  moreover have \<open>\<forall>(I :: 'a intrp). is_interpretation (language {\<phi>}) I \<and> dom I \<noteq> {} \<and>
         (\<forall>\<beta>. (\<forall>v. \<beta> v \<in> dom I) \<longrightarrow> (\<exists>a\<in>dom I. I,\<beta>(x := a) \<Turnstile> \<phi>)) \<longrightarrow>
         (\<exists>M. dom M = dom I \<and>
              intrp_rel M = intrp_rel I \<and>
              (\<forall>g zs. (g = f \<longrightarrow> length zs \<noteq> card (FV \<phi> - {x})) \<longrightarrow>
                 intrp_fn M g zs = intrp_fn I g zs) \<and>
              is_interpretation (language {skolem1 f x \<phi>}) M \<and>
              (\<forall>\<beta>. (\<forall>v. \<beta> v \<in> dom M) \<longrightarrow> M,\<beta> \<Turnstile> skolem1 f x \<phi>))\<close>
    unfolding skolem1_def using holds_indep_intrp_if sorry

  moreover have \<open>\<forall>N. is_interpretation (language {skolem1 f x \<phi>}) N \<and> dom N \<noteq> {} \<longrightarrow>
         (\<forall>\<beta>. (\<forall>v. \<beta> v \<in> dom N) \<and>
         N,\<beta> \<Turnstile> skolem1 f x \<phi> \<longrightarrow> (\<exists>a\<in>dom N. N,\<beta>(x := a) \<Turnstile> \<phi>))\<close>
    unfolding skolem1_def using holds_exists 
    sorry

  ultimately show \<open>is_prenex (skolem1 f x \<phi>) \<and>
    FV (skolem1 f x \<phi>) = FV \<phi> - {x} \<and>
    size (skolem1 f x \<phi>) < Suc (Suc (Suc (size \<phi>))) \<and>
    predicates_form (skolem1 f x \<phi>) = predicates_form \<phi> \<and>
    functions_form \<phi> \<subseteq> functions_form (skolem1 f x \<phi>) \<and>
    functions_form (skolem1 f x \<phi>) \<subseteq> (f, card (FV \<phi> - {x})) \<triangleright> functions_form \<phi> \<and>
    (\<forall>I. is_interpretation (language {\<phi>}) I \<and> dom I \<noteq> {} \<and>
         (\<forall>\<beta>. (\<forall>v. \<beta> v \<in> dom I) \<longrightarrow> (\<exists>a\<in>dom I. I,\<beta>(x := a) \<Turnstile> \<phi>)) \<longrightarrow>
         (\<exists>M. dom M = dom I \<and>
              intrp_rel M = intrp_rel I \<and>
              (\<forall>g zs. (g = f \<longrightarrow> length zs \<noteq> card (FV \<phi> - {x})) \<longrightarrow>
                 intrp_fn M g zs = intrp_fn I g zs) \<and>
              is_interpretation (language {skolem1 f x \<phi>}) M \<and>
              (\<forall>\<beta>. (\<forall>v. \<beta> v \<in> dom M) \<longrightarrow> M,\<beta> \<Turnstile> skolem1 f x \<phi>))) \<and>
    (\<forall>N. is_interpretation (language {skolem1 f x \<phi>}) N \<and> dom N \<noteq> {} \<longrightarrow>
         (\<forall>\<beta>. (\<forall>v. \<beta> v \<in> dom N) \<and>
         N,\<beta> \<Turnstile> skolem1 f x \<phi> \<longrightarrow> (\<exists>a\<in>dom N. N,\<beta>(x := a) \<Turnstile> \<phi>)))\<close>
    by blast
qed

end