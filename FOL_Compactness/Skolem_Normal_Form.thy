(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023-2024
 *               Larry Paulson <lp15 at cam.ac.edu>, 2024 *)

theory Skolem_Normal_Form
imports
  Prenex_Normal_Form
  Naturals_Injection
  "HOL-ex.Sketch_and_Explore"
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
    then have \<open>u \<in> set ts \<Longrightarrow> \<lbrakk>u\<rbrakk>\<^bsup>I,\<beta>\<^esup> \<in> FOL_Semantics.dom I\<close> for u
      by (smt (z3) UN_iff Un_iff eq_fst_iff functions_term.simps(2) is_interpretation_def)
    then show ?case
      using eval.simps(2) fst_conv imageE length_map list.set_map list_all_set assms(2)
      unfolding is_valuation_def
      by (smt (verit, best) Fun.prems Un_insert_left functions_term.simps(2) insert_iff 
          is_interpretation_def subsetI)
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

(* the following lemmas may be useful*)
lemma holds_formsubst:
   "M\<^bold>,v \<Turnstile> (p \<cdot>\<^sub>f\<^sub>m i) \<longleftrightarrow> M\<^bold>,(\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>M,v\<^esup>) \<circ> i \<Turnstile> p"
  by (simp add: holds_indep_\<beta>_if swap_subst_eval)

lemma holds_formsubst1:
   "M\<^bold>,v \<Turnstile> (p \<cdot>\<^sub>f\<^sub>m Var(x:=t)) \<longleftrightarrow> M\<^bold>,v(x := \<lbrakk>t\<rbrakk>\<^bsup>M,v\<^esup>) \<Turnstile> p"
  by (simp add: holds_indep_\<beta>_if swap_subst_eval)

lemma holds_formsubst2:
   "M\<^bold>,v \<Turnstile> (p \<cdot>\<^sub>f\<^sub>m subst x t) \<longleftrightarrow> M\<^bold>,v(x := \<lbrakk>t\<rbrakk>\<^bsup>M,v\<^esup>) \<Turnstile> p"
  by (simp add: holds_formsubst1 subst_def)

lemma size_nonzero [simp]: "size fm > 0"
  by (induction fm) auto

(* I think it's better to handle the conjuncts of the original giant formula separately, 
   possibly combining them at the end if it is really necessary.
  I believe it is a mistake to use so many abbreviations:
  ((\<^bold>\<forall>x\<^bold>. \<phi> \<^bold>\<longrightarrow> \<^bold>\<bottom>) \<^bold>\<longrightarrow> \<^bold>\<bottom>) and (\<^bold>\<exists>x\<^bold>. \<phi>) are tactically identical, which is not obvious.*)
lemma  
  assumes prenex_ex_phi: \<open>is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close> 
    and notin_ff: \<open>\<not> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<in> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
  shows holds_skolem1a: "is_prenex (skolem1 f x \<phi>)" (is "?A")
      and holds_skolem1b: "FV (skolem1 f x \<phi>) = FV (\<^bold>\<exists>x\<^bold>. \<phi>)" (is "?B")
      and holds_skolem1c: 
        "Prenex_Normal_Form.size (skolem1 f x \<phi>) < Prenex_Normal_Form.size (\<^bold>\<exists>x\<^bold>. \<phi>)" (is "?C")
      and holds_skolem1d: "predicates_form (skolem1 f x \<phi>) = predicates_form (\<^bold>\<exists>x\<^bold>. \<phi>)" (is "?D")
      and holds_skolem1e: "functions_form (\<^bold>\<exists>x\<^bold>. \<phi>) \<subseteq> functions_form (skolem1 f x \<phi>)" (is "?E")
      and holds_skolem1f: "functions_form (skolem1 f x \<phi>) 
                          \<subseteq> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<triangleright> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)" (is "?F")
proof -
  show ?A
    by (metis form.inject(2) form.inject(3) prenex_ex_phi prenex_formsubst prenex_imp 
        qfree_no_quantif skolem1_def)
  show ?B
  proof
    show \<open>FV (skolem1 f x \<phi>) \<subseteq> FV (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
    proof
      fix z
      assume \<open>z \<in> FV (skolem1 f x \<phi>)\<close>
      then obtain y where y_in: \<open>y \<in> FV \<phi>\<close> and 
        z_in: \<open>z \<in> FVT (Var y \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV \<phi> - {x})))))\<close>
        unfolding skolem1_def using formsubst_fv FV_exists by auto
      then have neq_x: \<open>y \<noteq> x \<Longrightarrow> z \<in> FV \<phi> - {x}\<close>
        by (simp add: subst_def)
      then show \<open>z \<in> FV (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
        using fvt_var_x_simp z_in by force
    qed
  next
    show \<open>FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<subseteq> FV (skolem1 f x \<phi>)\<close>
    proof
      fix z
      assume z_in: \<open>z \<in> FV (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
      then have \<open>FVT (Var z \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>)))))) = {z}\<close>
        by (simp add: subst_def)
      then show \<open>z \<in> FV (skolem1 f x \<phi>)\<close>
        unfolding skolem1_def using z_in formsubst_fv by auto
    qed
  qed
  show ?C
    by (simp add: size_indep_subst skolem1_def)
  show ?D
    by (simp add: formsubst_predicates skolem1_def)
  show ?E
    by (simp add: formsubst_functions_form skolem1_def)
  show ?F
  proof
    fix g
    assume g_in: \<open>g \<in> functions_form (skolem1 f x \<phi>)\<close>
    then have \<open>g \<in> functions_form \<phi> \<union> {g. \<exists>y. y \<in> FV \<phi> \<and> 
      g \<in> functions_term (Var y \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>)))))))}\<close>
      unfolding skolem1_def using formsubst_functions_form
      by blast
    moreover have \<open>{g. \<exists>y \<in> FV \<phi>. 
      g \<in> functions_term (Var y \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>)))))))} 
                   \<subseteq> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<triangleright> functions_form \<phi>\<close>
    proof
      fix h
      assume \<open>h \<in> {g. \<exists>y \<in> FV \<phi>. g \<in> functions_term (Var y \<cdot> subst x (Fun f (map Var 
      (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>)))))))}\<close>
      then obtain y where y_in: \<open>y \<in> FV \<phi>\<close> and h_in: 
        \<open>h \<in> functions_term (Var y \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>)))))))\<close>
        by blast
      then have y_neq_x_case: \<open>y \<noteq> x \<Longrightarrow> h \<in> functions_form \<phi>\<close>
        by (simp add: subst_def)
      have \<open>functions_term (Var x \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>))))))) =
        functions_term (Fun f (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>))))))\<close>
        by (simp add: subst_def)
      have \<open>functions_term (Fun f (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>)))))) = 
        {(f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>)))}\<close>
        by auto
      then have y_eq_x_case: \<open>y = x \<Longrightarrow> h = (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>)))\<close>
        using y_in h_in by auto
      show \<open>h \<in> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<triangleright> functions_form \<phi>\<close>
        using y_neq_x_case y_eq_x_case by blast
    qed
    ultimately show \<open>g \<in> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<triangleright> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
      by auto
  qed
qed

definition "define_fn \<equiv> \<lambda>FN f n h. \<lambda>g zs. if g=f \<and> length zs = n then h zs else FN g zs"

lemma holds_skolem1g:
  assumes prenex_ex_phi: \<open>is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close> 
    and notin_ff: \<open>\<not> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<in> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
  fixes I :: "'a intrp"  (* some ambiguity here about the correct type ??*)
   assumes interp_I: "is_interpretation (language {\<phi>}) I"
    and nempty_I: "dom I \<noteq> {}" 
    and valid: "\<And>\<beta>. is_valuation I \<beta> \<Longrightarrow> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>)"
  obtains M where "dom M = dom I" 
                  "intrp_rel M = intrp_rel I"
                  "\<And>g zs. g \<noteq> f \<or> length zs \<noteq> card (FV (\<^bold>\<exists>x\<^bold>. \<phi>)) \<Longrightarrow> intrp_fn M g zs = intrp_fn I g zs"
                  "is_interpretation (language {skolem1 f x \<phi>}) M" 
                  "\<And>\<beta>. is_valuation M \<beta> \<Longrightarrow> M\<^bold>,\<beta> \<Turnstile> skolem1 f x \<phi>"
proof -
  have ex_a_mod_phi: "\<exists>a\<in>dom I. I\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>"
    if "\<forall>v. \<beta> v \<in> dom I" for \<beta> 
    using that FOL_Semantics.holds_exists is_valuation_def valid by blast
  define intrp_f where  \<comment> \<open>Using @{term fold} instead causes complications\<close>
    \<open>intrp_f \<equiv> \<lambda>zs. foldr (\<lambda>kv f. fun_upd f (fst kv) (snd kv))
                          (zip (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) zs) (\<lambda>z. SOME c. c \<in> dom I)\<close>
  define thex where "thex \<equiv> \<lambda>zs. SOME a. a \<in> dom I \<and> (I\<^bold>, (intrp_f zs)(x:=a) \<Turnstile> \<phi>)"
  define FN where "FN \<equiv> define_fn (intrp_fn I) f (card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) thex"

  have M_is_struct [simp]: \<open>struct (dom I)\<close>
  proof
    show \<open>dom I \<noteq> {}\<close>
      using nempty_I .
  qed
  define M :: "'a intrp" where \<open>M =  Abs_intrp (dom I, FN, intrp_rel I)\<close>
  show ?thesis
  proof
    show dom_M_I_eq: \<open>dom M = dom I\<close>
      using M_is_struct unfolding M_def by simp
    show intrp_rel_eq: \<open>intrp_rel M = intrp_rel I\<close>
      using M_is_struct unfolding M_def by simp
    show intrp_fn_eq: "\<And>g zs. g \<noteq> f \<or> length zs \<noteq> card (FV (\<^bold>\<exists>x\<^bold>. \<phi>)) \<Longrightarrow> 
      intrp_fn M g zs = intrp_fn I g zs"
      using M_is_struct unfolding M_def FN_def define_fn_def
      by fastforce
   have in_dom_I: \<open>intrp_fn M f zs \<in> dom I\<close> 
      if len_eq: \<open>length zs = card (FV \<phi> - {x})\<close> and zs_in: \<open>set zs \<subseteq> dom M\<close>
        for zs
    proof -
      have len_eq2: \<open>length (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) = length zs\<close>
        using len_eq by simp
      have zs_in2: \<open>\<forall>z\<in>set zs. z \<in> dom I\<close>
        using dom_M_I_eq zs_in by force
      have fn_is_thex: \<open>(intrp_fn M) f zs = thex zs\<close>
        using len_eq M_is_struct by (auto simp: M_def FN_def define_fn_def)
      have \<open>\<forall>v. (intrp_f zs) v \<in> dom I\<close>
        using fun_upds_prop[OF len_eq2 zs_in2] nempty_I some_in_eq unfolding intrp_f_def
        by (metis (mono_tags))
      then show \<open>intrp_fn M f zs \<in> dom I\<close>
        using nempty_I ex_a_mod_phi interp_I unfolding is_interpretation_def
        by (metis (mono_tags, lifting) fn_is_thex someI_ex thex_def)
    qed
    show \<open>is_interpretation (language {skolem1 f x \<phi>}) M\<close>
      unfolding is_interpretation_def
    proof clarsimp
      fix g l
      assume in_skol: \<open>(g, length l) \<in> fst (language {skolem1 f x \<phi>})\<close> and in_dom_M: \<open>set l \<subseteq> dom M\<close>
      have \<open>(g, length l) \<in> fst (language {\<phi>}) \<or> (g, length l) = (f, card (FV \<phi> - {x}))\<close>
        using holds_skolem1f in_skol lang_singleton notin_ff prenex_ex_phi by auto
      then show \<open>intrp_fn M g l \<in> dom M\<close>
        using interp_I dom_M_I_eq intrp_fn_eq in_dom_I in_dom_M
        unfolding language_def is_interpretation_def
        by (metis FV_exists prod.inject)
    qed
    show "M\<^bold>,\<beta> \<Turnstile> skolem1 f x \<phi>" if "is_valuation M \<beta>" for \<beta>
    proof -
      have "M\<^bold>,\<beta>(x:=thex (map \<beta> (sorted_list_of_set(FV(\<^bold>\<exists>x\<^bold>. \<phi>))))) \<Turnstile> \<phi>"
      proof (rule holds_indep_intrp_if2)
        have "I\<^bold>, (intrp_f (map \<beta> (sorted_list_of_set(FV(\<^bold>\<exists>x\<^bold>. \<phi>)))))(x:=a) \<Turnstile> \<phi>  \<longleftrightarrow>  I\<^bold>, \<beta>(x:=a) \<Turnstile> \<phi>"
          for a
        proof (intro holds_indep_\<beta>_if strip)
          fix v
          assume "v \<in> FV \<phi>"
          then have "v=x \<or> v \<in> FV (\<^bold>\<exists>x\<^bold>. \<phi>)"
            using FV_exists by blast
          moreover have 
            "foldr (\<lambda>kv f. f(fst kv := snd kv)) (zip vs (map \<beta> vs)) (\<lambda>z. SOME c. c \<in> dom I) w = \<beta> w"
            if "w \<in> set vs" "set vs \<subseteq> FV (\<^bold>\<exists>x\<^bold>. \<phi>)" for vs w
            using that by (induction vs) auto
          ultimately
          show "((intrp_f (map \<beta> (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))) (x := a)) v = (\<beta>(x := a)) v"
            using finite_FV intrp_f_def by auto
        qed
        then show "I\<^bold>,\<beta> (x := thex (map \<beta> (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))) \<Turnstile> \<phi>"
          by (metis (mono_tags, lifting) dom_M_I_eq ex_a_mod_phi is_valuation_def that thex_def
              verit_sko_ex')
        show "dom I = dom M"
          using dom_M_I_eq by auto
        show "\<forall>p. intrp_rel I p = intrp_rel M p"
          using intrp_rel_eq by auto
        show "\<forall>f zs. (f, length zs) \<in> functions_form \<phi> \<longrightarrow> intrp_fn I f zs = intrp_fn M f zs"
          using functions_form.simps notin_ff intrp_fn_eq 
          by (metis sup_bot.right_neutral)
      qed
      moreover have "FN f (map \<beta> (sorted_list_of_set (FV \<phi> - {x}))) = 
        thex (map \<beta> (sorted_list_of_set (FV \<phi> - {x})))"
        by (simp add: FN_def define_fn_def)
      ultimately show ?thesis
        by (simp add: holds_formsubst2 skolem1_def M_def o_def)
    qed
  qed
qed

lemma holds_skolem1h:
  assumes prenex_ex_phi: \<open>is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close> and \<open>\<not> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<in> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
  assumes is_intrp: "is_interpretation (language {skolem1 f x \<phi>}) N"
      and nempty_N: "FOL_Semantics.dom N \<noteq> {}"
      and is_val: "is_valuation N \<beta>"
      and skol_holds: "N\<^bold>,\<beta> \<Turnstile> skolem1 f x \<phi>"
    shows "N\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>)"
proof -
  have \<open>\<exists>a\<in>dom N. N\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>\<close>
  proof -
    have \<open>N\<^bold>,(\<lambda>v. \<lbrakk>subst x (Fun f (map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))) v\<rbrakk>\<^bsup>N,\<beta>\<^esup>) \<Turnstile> \<phi>\<close>
      by (metis skol_holds skolem1_def swap_subst_eval)
    then have holds_eval_f: \<open>N\<^bold>,\<beta>(x := \<lbrakk>Fun f (map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))\<rbrakk>\<^bsup>N,\<beta>\<^esup>) \<Turnstile> \<phi>\<close>
      by (smt (verit, best) eval.simps(1) fun_upd_other fun_upd_same holds_indep_\<beta>_if subst_def)
    show \<open>\<exists>a\<in>dom N. N\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>\<close>
    proof (cases \<open>x \<in> FV \<phi>\<close>)
      case True
      have eval_to_intrp: \<open>\<lbrakk>Fun f (map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))\<rbrakk>\<^bsup>N,\<beta>\<^esup> =
        intrp_fn N f [\<lbrakk>t\<rbrakk>\<^bsup>N,\<beta>\<^esup>. t \<leftarrow> map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>)))]\<close>
        by simp

      have \<open>[\<lbrakk>t\<rbrakk>\<^bsup>N,\<beta>\<^esup>. t \<leftarrow> map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>)))] =
        [\<beta> t. t \<leftarrow> (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>)))]\<close>
        by auto
      then have all_in_dom: \<open>set [\<lbrakk>t\<rbrakk>\<^bsup>N,\<beta>\<^esup>. t \<leftarrow> map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>)))] \<subseteq> dom N\<close>
        using is_val by auto
      have \<open>(f, length [\<lbrakk>t\<rbrakk>\<^bsup>N,\<beta>\<^esup>. t \<leftarrow> map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>)))]) \<in>
        functions_form (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Fun f (map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))))\<close>
        using func_form_subst[OF True] is_intrp lang_singleton 
        unfolding skolem1_def is_interpretation_def by (metis length_map)
      then have \<open>\<lbrakk>Fun f (map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))\<rbrakk>\<^bsup>N,\<beta>\<^esup> \<in> dom N\<close>
        using is_intrp eval_to_intrp  all_in_dom unfolding is_interpretation_def skolem1_def
        by (metis fst_conv lang_singleton)
      then show ?thesis 
        using holds_eval_f by blast
    next
      case False
      obtain a where a_in: \<open>a \<in> dom N\<close>
        using nempty_N by blast
      then have \<open>N\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>\<close>
        using holds_eval_f False by (metis fun_upd_other holds_indep_\<beta>_if)
      then show ?thesis
        using a_in by blast
    qed
  qed
  then show ?thesis
    by simp
qed

lemma holds_skolem1: 
  assumes \<open>is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close> and \<open>\<not> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<in> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
  shows \<open>is_prenex (skolem1 f x \<phi>) \<and>
  FV (skolem1 f x \<phi>) = FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<and>
  size (skolem1 f x \<phi>) < size (\<^bold>\<exists>x\<^bold>. \<phi>) \<and>
  predicates_form (skolem1 f x \<phi>) = predicates_form (\<^bold>\<exists>x\<^bold>. \<phi>) \<and>
  functions_form (\<^bold>\<exists>x\<^bold>. \<phi>) \<subseteq> functions_form (skolem1 f x \<phi>) \<and>
  functions_form (skolem1 f x \<phi>) \<subseteq> insert (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) (functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)) \<and>
  (\<forall>(I :: 'a intrp). is_interpretation (language {\<phi>}) I \<and>
    \<not> (dom I = {}) \<and>
    (\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>))) \<longrightarrow>
    (\<exists>(M :: 'a intrp). dom M = dom I \<and>
      intrp_rel M = intrp_rel I \<and>
      (\<forall>g zs. \<not>g=f \<or> \<not>(length zs = card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<longrightarrow> intrp_fn M g zs = intrp_fn I g zs) \<and>
      is_interpretation (language {skolem1 f x \<phi>}) M \<and>
      (\<forall>\<beta>. is_valuation M \<beta> \<longrightarrow> (M\<^bold>, \<beta> \<Turnstile> (skolem1 f x \<phi>))))) \<and>
  (\<forall>(N :: 'a intrp). is_interpretation (language {skolem1 f x \<phi>}) N \<and>
    \<not> (dom N = {}) \<longrightarrow>
    (\<forall>\<beta>. is_valuation N \<beta> \<and> (N\<^bold>, \<beta> \<Turnstile> (skolem1 f x \<phi>)) \<longrightarrow> (N\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>))))
\<close>
  by (smt (verit, ccfv_SIG) assms holds_skolem1a holds_skolem1b holds_skolem1c holds_skolem1d
      holds_skolem1e holds_skolem1f holds_skolem1g holds_skolem1h)

(* Skolems_EXISTENCE in hol-light *)
lemma skolems_ex: \<open>\<exists>skolems. \<forall>\<phi>. skolems \<phi> = (\<lambda>k. ppat (\<lambda>x \<psi>. \<^bold>\<forall>x\<^bold>. (skolems \<psi> k))
  (\<lambda>x \<psi>. skolems (skolem1 (numpair J k) x \<psi>) (Suc k)) (\<lambda>\<psi>. \<psi>) \<phi>)\<close>
proof (rule size_rec, (rule allI)+, (rule impI))
  fix skolems :: "form \<Rightarrow> nat \<Rightarrow> form" and g \<phi>
  assume IH: \<open>\<forall>z. size z < size \<phi> \<longrightarrow> skolems z = g z\<close>
  show "(\<lambda>k. 
    ppat (\<lambda>x \<psi>. \<^bold>\<forall> x\<^bold>. skolems \<psi> k) (\<lambda>x \<psi>. skolems (skolem1 (numpair J k) x \<psi>) (Suc k))(\<lambda>\<psi>. \<psi>) \<phi>) = 
    (\<lambda>k. ppat (\<lambda>x \<psi>. \<^bold>\<forall> x\<^bold>. g \<psi> k) (\<lambda>x \<psi>. g (skolem1 (numpair J k) x \<psi>) (Suc k)) (\<lambda>\<psi>. \<psi>) \<phi>)"
  proof (cases "\<exists>x \<phi>'. \<phi> = \<^bold>\<forall>x\<^bold>. \<phi>'")
    case True
    then obtain x \<phi>' where phi_is: "\<phi> = \<^bold>\<forall>x\<^bold>. \<phi>'"
      by blast
    then have smaller: \<open>size (\<phi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<phi>\<close> for \<sigma>
      using size_indep_subst by simp
    have ppat_to_skol: \<open>(ppat (\<lambda>x \<psi>. \<^bold>\<forall>x\<^bold>. (skolems \<psi> k))
      (\<lambda>x \<psi>. skolems (skolem1 (numpair J k) x \<psi>) (Suc k)) (\<lambda>\<psi>. \<psi>) \<phi>) = (\<^bold>\<forall>x\<^bold>. skolems \<phi>' k)\<close> for k
      unfolding ppat_def by (simp add: phi_is)
    have skol_to_g: \<open>(\<^bold>\<forall>x\<^bold>. skolems \<phi>' k) = (\<^bold>\<forall> x\<^bold>. g \<phi>' k)\<close> for k
      using IH smaller by (simp add: phi_is)
    have g_to_ppat: \<open>(\<^bold>\<forall> x\<^bold>. g \<phi>' k) = 
      ppat (\<lambda>x \<psi>. \<^bold>\<forall> x\<^bold>. g \<psi> k) (\<lambda>x \<psi>. g (skolem1 (numpair J k) x \<psi>) (Suc k)) (\<lambda>\<psi>. \<psi>) \<phi>\<close> for k
      unfolding ppat_def using phi_is by simp
    show ?thesis
      using ppat_to_skol skol_to_g g_to_ppat by auto
  next
    case False
    assume falseAll: \<open>\<not>(\<exists>x \<phi>'. \<phi> = \<^bold>\<forall> x\<^bold>. \<phi>')\<close>
    then show ?thesis
    proof (cases "\<exists>x \<phi>'. \<phi> = \<^bold>\<exists>x\<^bold>. \<phi>'")
      case True
      then obtain x \<phi>' where phi_is: "\<phi> = \<^bold>\<exists>x\<^bold>. \<phi>'"
        by blast
      then have smaller: \<open>size (\<phi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<phi>\<close> for \<sigma>
        using size_indep_subst by simp
      have  ppat_to_skol: \<open>(ppat (\<lambda>x \<psi>. \<^bold>\<forall>x\<^bold>. (skolems \<psi> k))
      (\<lambda>x \<psi>. skolems (skolem1 (numpair J k) x \<psi>) (Suc k)) (\<lambda>\<psi>. \<psi>) \<phi>) =
       skolems (skolem1 (numpair J k) x \<phi>') (Suc k)\<close> for k
        unfolding ppat_def using phi_is by simp
      have skol_to_g: \<open>skolems (skolem1 (numpair J k) x \<phi>') (Suc k) = 
        g (skolem1 (numpair J k) x \<phi>') (Suc k)\<close> for k
        using IH smaller phi_is by (simp add: skolem1_def)
      have g_to_ppat: \<open>g (skolem1 (numpair J k) x \<phi>') (Suc k) = 
        ppat (\<lambda>x \<psi>. \<^bold>\<forall> x\<^bold>. g \<psi> k) (\<lambda>x \<psi>. g (skolem1 (numpair J k) x \<psi>) (Suc k)) (\<lambda>\<psi>. \<psi>) \<phi>\<close> for k
        unfolding ppat_def using phi_is by simp
      show ?thesis
        using ppat_to_skol skol_to_g g_to_ppat by simp
    next
      case False
      then show ?thesis
        using falseAll ppat_last unfolding ppat_def by auto
    qed
  qed
qed

consts skolems :: "nat \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form"
specification (skolems)
  skolems_eq: \<open>\<And>J \<psi> k. skolems J \<psi> k 
              = ppat (\<lambda>x \<phi>'. \<^bold>\<forall>x\<^bold>. (skolems J \<phi>' k))  (\<lambda>x \<phi>'. skolems J (skolem1 (numpair J k) x \<phi>') (Suc k)) (\<lambda>\<phi>. \<phi>) \<psi>\<close>
  using skolems_ex by meson

lemma holds_skolems_induction:
  assumes n: "size p = n" and "is_prenex p" and "\<And>l m. (numpair J l, m) \<in> functions_form p \<Longrightarrow> l < k"
  shows "universal(skolems J p k)  \<and>
               (FV((skolems J p k)) = FV p) \<and>
               (predicates_form (skolems J p k) = predicates_form p) \<and>
                functions_form p \<subseteq> functions_form (skolems J p k) \<and>
                functions_form (skolems J p k) \<subseteq> {(numpair J l,m) | j l m. k \<le> l} \<union> functions_form p \<and>
                (\<forall>M. is_interpretation (language {p}) M \<and>
                     dom M \<noteq> {} \<and>
                     (\<forall>v. is_valuation M v \<longrightarrow> holds M v p)
                     \<longrightarrow> (\<exists>M'. (dom M' = dom M) \<and>
                              (intrp_rel M' = intrp_rel M) \<and>
                              (\<forall>g zs. intrp_fn M' g zs \<noteq> intrp_fn M g zs
                                    \<longrightarrow> (\<exists>l. k \<le> l \<and> g = numpair J l)) \<and>
                              is_interpretation (language {(skolems J p k)}) M' \<and>
                              (\<forall>v. is_valuation M' v
                                   \<longrightarrow> holds M' v (skolems J p k)))) \<and>
               (\<forall>N. is_interpretation (language {(skolems J p k)}) N \<and> dom M \<noteq> {}
                \<longrightarrow> (\<forall>v. is_valuation N v \<and> holds N v (skolems J p k) \<longrightarrow> holds N v p))"
  sorry

end
