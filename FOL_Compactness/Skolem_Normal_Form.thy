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

lemma fun_upds_prop: \<open>length xs = length zs \<Longrightarrow> \<forall>z\<in>set zs. P z \<Longrightarrow> \<forall>v. P (g v) \<Longrightarrow> \<forall>v. P ((fold (\<lambda>kv f. fun_upd f (fst kv) (snd kv)) (zip xs zs) g) v)\<close>
proof (induction zs arbitrary: xs g)
  case Nil
  then show ?case
    by simp
next
  case (Cons a zs)
  obtain x xsp where xs_is: \<open>xs = x # xsp\<close>
    using Cons(2) by (metis length_Suc_conv)
  then have fold_simp: \<open>fold (\<lambda>kv f. f(fst kv := snd kv)) (zip xs (a # zs)) g = fold (\<lambda>kv f. f(fst kv := snd kv)) (zip xsp zs) (g(x := a))\<close>
    by simp
  have \<open>length xsp = length zs\<close>
    using xs_is Cons(2) by simp
  moreover have \<open>\<forall>a\<in>set zs. P a\<close>
    using Cons(3) by simp
  moreover have \<open>\<forall>v. P ((g(x := a)) v)\<close>
    using Cons(4) Cons(3) by simp
  ultimately have \<open>\<forall>v. P (fold (\<lambda>kv f. f(fst kv := snd kv)) (zip xsp zs) (g(x := a)) v)\<close>
    using Cons(1) by blast
  then show ?case
    using fold_simp by presburger
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

  moreover have pred_form_eq: \<open>predicates_form (skolem1 f x \<phi>) = predicates_form \<phi>\<close>
    unfolding skolem1_def using formsubst_predicates by blast

  moreover have func_form_low: \<open>functions_form \<phi> \<subseteq> functions_form (skolem1 f x \<phi>)\<close>
    unfolding skolem1_def by (simp add: formsubst_functions_form)

  moreover have func_form_up: \<open>functions_form (skolem1 f x \<phi>) \<subseteq> 
    (f, card (FV \<phi> - {x})) \<triangleright> functions_form \<phi>\<close>
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
  proof clarsimp
    fix I :: "'a intrp"
    assume interp_I: \<open>is_interpretation (language {\<phi>}) I\<close> and
      nempty_I: \<open>dom I \<noteq> {}\<close> and
      ex_a_mod_phi: \<open>\<forall>\<beta>. (\<forall>v. \<beta> v \<in> dom I) \<longrightarrow> (\<exists>a\<in>dom I. I,\<beta>(x := a) \<Turnstile> \<phi>)\<close>
    define intrp_f where \<open>intrp_f = (\<lambda>zs. (fold (\<lambda>kv f. fun_upd f (fst kv) (snd kv))
                        (zip (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) zs) (\<lambda>z. SOME c. c \<in> dom I)))\<close>
    have M_is_struct: \<open>struct (dom I) (\<lambda>g zs. if ((g = f) \<and> (length zs = card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))
                      then (SOME a. a \<in> dom I \<and> (I, (intrp_f zs)(x := a) \<Turnstile> \<phi>))
                      else intrp_fn I g zs) (intrp_rel I)\<close>
    proof
      show \<open>dom I \<noteq> {}\<close>
        using nempty_I .
    next
      show  \<open>\<forall>fa zs. (\<forall>e\<in>set zs. e \<in> dom I) \<longrightarrow> (if fa = f \<and> length zs = card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))
        then SOME a. a \<in> dom I \<and> I, (intrp_f zs)(x := a) \<Turnstile> \<phi>
        else intrp_fn I fa zs) \<in> dom I\<close>
      proof (clarsimp, rule conjI, (rule impI)+)
        fix fa and zs :: "'a list"
        assume len_zs: \<open>fa = f \<and> length zs = card (FV \<phi> - {x})\<close> and
          zs_in: \<open>\<forall>e\<in>set zs. e \<in> dom I\<close>
        have len_eq: \<open>length (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) = length zs\<close>
          using len_zs by simp
        have \<open>\<forall>v. (intrp_f zs) v \<in> dom I\<close>
          using fun_upds_prop[OF len_eq zs_in] unfolding intrp_f_def
          by (simp add: nempty_I some_in_eq)
        then have \<open>\<exists>a. a \<in> dom I \<and> I, (intrp_f zs)(x := a) \<Turnstile> \<phi>\<close>
          using ex_a_mod_phi by blast
        then show \<open>(SOME a. a \<in> dom I \<and> I,(intrp_f zs)(x := a) \<Turnstile> \<phi>) \<in> dom I\<close>
          by (metis (no_types, lifting) someI_ex)
      next
        fix fa and zs :: "'a list"
        show \<open>(fa = f \<longrightarrow> length zs \<noteq> card (FV \<phi> - {x})) \<longrightarrow> (\<forall>e\<in>set zs. e \<in> dom I) \<longrightarrow>
          intrp_fn I fa zs \<in> dom I\<close>
        proof clarsimp
          assume \<open>fa = f \<longrightarrow> length zs \<noteq> card (FV \<phi> - {x})\<close> and
            zs_in: \<open>\<forall>e\<in>set zs. e \<in> dom I\<close>
          then show \<open>intrp_fn I fa zs \<in> dom I\<close>
            using FN_dom_to_dom by blast
        qed
      qed
    next
      show \<open>\<forall>p. \<forall>es\<in>intrp_rel I p. \<forall>e\<in>set es. e \<in> dom I\<close>
        by (meson intrp_is_struct struct_def)
    qed
    define M :: "'a intrp" where \<open>M =  Abs_intrp
                    ((dom I), 
                    (\<lambda>g zs. if ((g = f) \<and> (length zs = card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))
                      then (SOME a. a \<in> dom I \<and> (I, (intrp_f zs)(x := a) \<Turnstile> \<phi>))
                      else intrp_fn I g zs),
                    (intrp_rel I))\<close>
    have dom_M_I_eq: \<open>dom M = dom I\<close>
      using M_is_struct unfolding M_def by simp
    have intrp_rel_eq: \<open>intrp_rel M = intrp_rel I\<close>
      using M_is_struct unfolding M_def by simp
    have intrp_fn_eq: \<open>(\<forall>g zs. (g = f \<longrightarrow> length zs \<noteq> card (FV \<phi> - {x})) \<longrightarrow>
                 intrp_fn M g zs = intrp_fn I g zs)\<close>
      using M_is_struct unfolding M_def by simp
    have in_dom_I: \<open>fold (\<lambda>l b. b \<and> l \<in> dom M) zs True \<Longrightarrow> length zs = card (FV \<phi> - {x}) \<Longrightarrow> intrp_fn M f zs \<in> dom I\<close> for zs
    proof -
      assume len_eq: \<open>length zs = card (FV \<phi> - {x})\<close> and
        zs_in: \<open>fold (\<lambda>l b. b \<and> l \<in> dom M) zs True\<close>
      have len_eq2: \<open>length (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) = length zs\<close>
        using len_eq by simp
      have \<open>fold (\<lambda>l b. b \<and> l \<in> dom M) zs B = (B \<and> (\<forall>z \<in> set zs. z \<in> dom M))\<close> for B
      proof (induction zs arbitrary: B)
        case Nil
        then show ?case by simp
      next
        case (Cons a zs)
        then have \<open>fold (\<lambda>l b. b \<and> l \<in> dom M) (a # zs) B = fold (\<lambda>l b. b \<and> l \<in> dom M) zs (B \<and> a \<in> dom M)\<close>
          using fold.simps(2) by simp
        also have \<open>... = (B \<and> a \<in> dom M \<and> (\<forall>z \<in> set zs. z \<in> dom M))\<close>
          using Cons[of "B \<and> a \<in> dom M"] by presburger
        finally show ?case 
          by simp
      qed
      then have zs_in2: \<open>\<forall>z\<in>set zs. z \<in> dom I\<close>
        using zs_in dom_M_I_eq by simp
      have \<open>(intrp_fn M) f zs = (SOME a. a \<in> dom I \<and> I, (intrp_f zs)(x := a) \<Turnstile> \<phi>)\<close>
        unfolding M_def using len_eq M_is_struct by auto
      have \<open>\<forall>v. (intrp_f zs) v \<in> dom I\<close>
          using fun_upds_prop[OF len_eq2 zs_in2] nempty_I some_in_eq unfolding intrp_f_def
          by (metis (no_types, lifting) Eps_cong)
      then show \<open>intrp_fn M f zs \<in> dom I\<close>
        using nempty_I ex_a_mod_phi by (metis FN_dom_to_dom dom_M_I_eq zs_in2)
    qed
    have is_interp_M: \<open>is_interpretation (language {skolem1 f x \<phi>}) M\<close>
      unfolding is_interpretation_def
    proof clarsimp
      fix fa l
      assume in_skol: \<open>(fa, length l) \<in> fst (language {skolem1 f x \<phi>})\<close> and
        in_dom_M: \<open>fold (\<lambda>l b. b \<and> l \<in> dom M) l True\<close>
      have l_in_dom_I: \<open>list_all (\<lambda>x. x \<in> dom I) l\<close>
        using in_dom_M dom_M_I_eq by simp
      have \<open>(fa, length l) \<in> fst (language {\<phi>}) \<or> (fa, length l) = (f, card (FV \<phi> - {x}))\<close>
        using in_skol pred_form_eq func_form_low func_form_up lang_singleton by auto
      then show \<open>intrp_fn M fa l \<in> dom M\<close>
        using interp_I dom_M_I_eq intrp_fn_eq in_dom_I[OF in_dom_M]
        unfolding language_def is_interpretation_def
        by (metis l_in_dom_I prod.inject)
    qed
    find_theorems " _, _ \<Turnstile> _" name: subs
    thm holds_indep_intrp_if swap_subst_eval subst_lemma_terms
    have holds_M_phi: \<open>\<forall>\<beta>. (\<forall>v. \<beta> v \<in> dom M) \<longrightarrow> M,\<beta> \<Turnstile> skolem1 f x \<phi>\<close>
    proof clarsimp
      fix \<beta> :: "nat \<Rightarrow> 'a"
      assume \<open>\<forall>v. \<beta> v \<in> dom M\<close>
      then have \<open>\<exists>a\<in>dom I. I,\<beta>(x := a) \<Turnstile> \<phi>\<close>
        using ex_a_mod_phi dom_M_I_eq by blast
      then show \<open>M,\<beta> \<Turnstile> skolem1 f x \<phi>\<close>
        unfolding skolem1_def using swap_subst_eval subst_lemma_terms sledgehammer
        sorry
    qed
    show \<open>\<exists>M. dom M = dom I \<and>
      intrp_rel M = intrp_rel I \<and>
      (\<forall>g zs. (g = f \<longrightarrow> length zs \<noteq> card (FV \<phi> - {x})) \<longrightarrow> intrp_fn M g zs = intrp_fn I g zs) \<and>
      is_interpretation (language {skolem1 f x \<phi>}) M \<and>
      (\<forall>\<beta>. (\<forall>v. \<beta> v \<in> dom M) \<longrightarrow> M,\<beta> \<Turnstile> skolem1 f x \<phi>)\<close>
      using dom_M_I_eq intrp_rel_eq intrp_fn_eq is_interp_M holds_M_phi by blast
  qed

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
    (\<forall>(I :: 'a intrp). is_interpretation (language {\<phi>}) I \<and> dom I \<noteq> {} \<and>
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