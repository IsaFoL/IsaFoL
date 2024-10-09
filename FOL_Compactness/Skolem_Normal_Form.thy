(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023-2024
 *               Larry Paulson <lp15 at cam.ac.edu>, 2024 *)

theory Skolem_Normal_Form
imports
  Prenex_Normal_Form
  (*"HOL-Library.Nat_Bijection"*)
  (* Naturals_Injection *)
  Bumping
  "HOL-ex.Sketch_and_Explore"
begin

lemma witness_imp_holds_exists:
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
      using assms(2) by (auto simp: is_valuation_def)
  next
    case (Fun f ts)
    then have \<open>u \<in> set ts \<Longrightarrow> \<lbrakk>u\<rbrakk>\<^bsup>I,\<beta>\<^esup> \<in> dom I\<close> for u
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
   "M\<^bold>,\<beta> \<Turnstile> (p \<cdot>\<^sub>f\<^sub>m i) \<longleftrightarrow> M\<^bold>,(\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>M,\<beta>\<^esup>) \<circ> i \<Turnstile> p"
  by (simp add: holds_indep_\<beta>_if swap_subst_eval)

lemma holds_formsubst1:
   "M\<^bold>,\<beta> \<Turnstile> (p \<cdot>\<^sub>f\<^sub>m Var(x:=t)) \<longleftrightarrow> M\<^bold>,\<beta>(x := \<lbrakk>t\<rbrakk>\<^bsup>M,\<beta>\<^esup>) \<Turnstile> p"
  by (simp add: holds_indep_\<beta>_if swap_subst_eval)

lemma holds_formsubst2:
   "M\<^bold>,\<beta> \<Turnstile> (p \<cdot>\<^sub>f\<^sub>m subst x t) \<longleftrightarrow> M\<^bold>,\<beta>(x := \<lbrakk>t\<rbrakk>\<^bsup>M,\<beta>\<^esup>) \<Turnstile> p"
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
  fixes I :: "'a intrp" 
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
      and nempty_N: "dom N \<noteq> {}"
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
        using is_val by (auto simp: is_valuation_def)
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
proof (intro size_rec strip)
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
              = ppat (\<lambda>x \<phi>'. \<^bold>\<forall>x\<^bold>. (skolems J \<phi>' k)) (\<lambda>x \<phi>'. skolems J (skolem1 (numpair J k) x \<phi>') (Suc k)) (\<lambda>\<phi>. \<phi>) \<psi>\<close>
  using skolems_ex by meson

definition "skolems_bounded \<equiv> \<lambda>p J k. \<forall>l m. (numpair J l, m) \<in> functions_form p \<longrightarrow> l < k"

lemma skolems_bounded_mono: "\<lbrakk>skolems_bounded p J k'; k'\<le>k\<rbrakk> \<Longrightarrow> skolems_bounded p J k"
  by (meson dual_order.strict_trans1 skolems_bounded_def)

text \<open>Basic properties proved by induction on the number of Skolemisation steps. 
Harrison's gigantic conjunction broken up for more manageable proofs, at the cost of some repetition\<close>

text \<open>first, the simplest properties\<close>
lemma holds_skolems_induction_A:
  assumes "size p = n" and "is_prenex p" and "skolems_bounded p J k"
  shows "universal(skolems J p k) \<and>
         FV(skolems J p k) = FV p \<and>
         predicates_form (skolems J p k) = predicates_form p \<and>
         functions_form p \<subseteq> functions_form (skolems J p k) \<and>
         functions_form (skolems J p k) \<subseteq> {(numpair J l,m) | l m. k \<le> l} \<union> functions_form p"
  using assms
proof (induction n arbitrary: k p rule: less_induct)
  case (less n)
  show ?case
    using \<open>is_prenex p\<close>
  proof cases
    case 1
    then show ?thesis
      by (metis (no_types, lifting) ppat_last_qfree skolems_eq universal.simps UnCI subsetI)
  next
    case (2 \<phi> x)
    then have smaller: "Prenex_Normal_Form.size \<phi> < n" and skbo: "skolems_bounded \<phi> J k"
      using less.prems by (auto simp add: skolems_bounded_def)
    have skoeq: "skolems J p k = (\<^bold>\<forall> x\<^bold>. skolems J \<phi> k)"
      by (metis "2"(1) ppat_simpA skolems_eq)
    show ?thesis
      using less.IH [OF smaller refl \<open>is_prenex \<phi>\<close>, of k] skoeq
      by (simp add: 2 is_valuation_def lang_singleton skbo)
  next
    case (3 \<phi> x)
    define \<phi>' where "\<phi>' \<equiv> skolem1 (numpair J k) x \<phi>"
    have smaller: "Prenex_Normal_Form.size \<phi>' < n"
             and pair_notin_ff: "(numpair J k, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<notin> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)"
      using 3 holds_skolem1c less.prems unfolding \<phi>'_def skolems_bounded_def by blast+
    have pre: "is_prenex \<phi>'"
      using "3"(1) pair_notin_ff holds_skolem1a \<open>is_prenex p\<close> \<phi>'_def by blast
    define \<phi>'' where "\<phi>'' \<equiv> skolems J \<phi>' (Suc k)"
    have skos: "skolems J (\<^bold>\<exists>x\<^bold>. \<phi>) k = \<phi>''"
      by (metis \<phi>'_def \<phi>''_def ppat_simpB skolems_eq)
    have funsub: "functions_form p \<subseteq> functions_form \<phi>'" 
                 "functions_form \<phi>' \<subseteq> insert (numpair J k, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) (functions_form p)"
      using "3"(1) pair_notin_ff \<phi>'_def holds_skolem1e holds_skolem1f \<open>is_prenex p\<close> by presburger+
    have skbo: "skolems_bounded \<phi>' J (Suc k)"
      using \<open>skolems_bounded p J k\<close> unfolding skolems_bounded_def less_Suc_eq
      using funsub(2) by fastforce
    have FV: "FV \<phi>' = FV \<phi> - {x}"
      using "3"(1) pair_notin_ff holds_skolem1b \<open>is_prenex p\<close> \<phi>'_def by auto
    have preq: "predicates_form \<phi>' = predicates_form \<phi>"
      using \<phi>'_def formsubst_predicates skolem1_def by presburger
    show ?thesis
      using less.IH [OF smaller refl pre, of "Suc k"] skolems_eq [of J p] FV funsub 3
      by (force simp: preq skbo ppat_simpB simp flip: \<phi>'_def)
  qed
qed

text \<open>the final conjunct of the HOL Light version\<close>
lemma holds_skolems_induction_B:
  fixes N :: "'a intrp"
  assumes "size p = n" and "is_prenex p" and "skolems_bounded p J k"
    and "is_interpretation (language {skolems J p k}) N" "dom N \<noteq> {}"
    and "is_valuation N \<beta>" "N\<^bold>,\<beta> \<Turnstile> skolems J p k"
  shows "N\<^bold>,\<beta> \<Turnstile> p"
  using assms
proof (induction n arbitrary: N k p \<beta> rule: less_induct)
  case (less n)
  show ?case
    using \<open>is_prenex p\<close>
  proof cases
    case 1
    with less show ?thesis
      by (metis (no_types, lifting) ppat_last_qfree skolems_eq)
  next
    case (2 \<phi> x)
    then have smaller: "Prenex_Normal_Form.size \<phi> < n" and skbo: "skolems_bounded \<phi> J k"
      using less.prems by (auto simp add: skolems_bounded_def)
    have "skolems J p k = (\<^bold>\<forall> x\<^bold>. skolems J \<phi> k)"
      by (metis "2"(1) ppat_simpA skolems_eq)
    then show ?thesis
      using less.IH [OF smaller refl \<open>is_prenex \<phi>\<close>, of k] less.prems
      by (simp add: lang_singleton skbo valuation_valmod 2)
  next
    case (3 \<phi> x)
    define \<phi>' where "\<phi>' \<equiv> skolem1 (numpair J k) x \<phi>"
    have smaller: "Prenex_Normal_Form.size \<phi>' < n"
             and pair_notin_ff: "(numpair J k, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<notin> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)"
      using 3 holds_skolem1c less.prems unfolding \<phi>'_def skolems_bounded_def by blast+
    have pre: "is_prenex \<phi>'"
      using "3"(1) pair_notin_ff holds_skolem1a \<open>is_prenex p\<close> \<phi>'_def by blast
    define \<phi>'' where "\<phi>'' \<equiv> skolems J \<phi>' (Suc k)"
    have skos: "skolems J (\<^bold>\<exists>x\<^bold>. \<phi>) k = \<phi>''"
      by (metis \<phi>'_def \<phi>''_def ppat_simpB skolems_eq)
    have "functions_form \<phi>' \<subseteq> insert (numpair J k, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) (functions_form p)"
      using "3"(1) pair_notin_ff \<phi>'_def holds_skolem1f \<open>is_prenex p\<close> by presburger
    then have skbo: "skolems_bounded \<phi>' J (Suc k)"
      using \<open>skolems_bounded p J k\<close> unfolding skolems_bounded_def less_Suc_eq by fastforce
    have prex: "is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)"
      using 3 \<open>is_prenex p\<close> by blast
    have "functions_form (skolem1 (numpair J k) x \<phi>) \<subseteq> functions_form (skolems J \<phi>' (Suc k))"
      using \<phi>'_def holds_skolems_induction_A pre skbo by blast
    then show ?thesis
      using less.IH [OF smaller refl pre, of "Suc k"] less.prems skolems_eq [of J p] 
      apply (simp add: skbo ppat_simpB 3)
      using holds_skolem1h [of x \<phi> "numpair J k"] pair_notin_ff  \<open>is_prenex \<phi>'\<close>
      by (metis prex \<phi>'_def holds_exists interpretation_sublanguage lang_singleton) 
  qed
qed


text \<open>the penultimate conjunct of the HOL Light version\<close>
lemma holds_skolems_induction_C:
  fixes M :: "'a intrp"
  assumes "size p = n" and "is_prenex p" and "skolems_bounded p J k"
    and "is_interpretation (language {p}) M" "dom M \<noteq> {}" "satisfies M {p}"
  shows "\<exists>M'. dom M' = dom M \<and> intrp_rel M' = intrp_rel M \<and>
                  (\<forall>g zs. intrp_fn M' g zs \<noteq> intrp_fn M g zs
                        \<longrightarrow> (\<exists>l. k \<le> l \<and> g = numpair J l)) \<and>
                  is_interpretation (language {skolems J p k}) M' \<and>
                  satisfies M' {skolems J p k}"
  using assms
proof (induction n arbitrary: M k p rule: less_induct)
  case (less n)
  show ?case
    using \<open>is_prenex p\<close>
  proof cases
    case 1
    with less show ?thesis
      by (metis (no_types, lifting) ppat_last_qfree skolems_eq)
  next
    case (2 \<phi> x)
    then have smaller: "Prenex_Normal_Form.size \<phi> < n" and skbo: "skolems_bounded \<phi> J k"
      using less.prems by (auto simp add: skolems_bounded_def)
    have skoeq: "skolems J p k = (\<^bold>\<forall> x\<^bold>. skolems J \<phi> k)"
      by (metis "2"(1) ppat_simpA skolems_eq)
    show ?thesis
      using less.IH [OF smaller refl \<open>is_prenex \<phi>\<close>, of k M] skoeq less.prems
      apply (simp add: skbo 2 lang_singleton satisfies_def)
      by (metis fun_upd_triv is_valuation_def valuation_valmod)
  next
    case (3 \<phi> x)
    define \<phi>' where "\<phi>' \<equiv> skolem1 (numpair J k) x \<phi>"
    have smaller: "Prenex_Normal_Form.size \<phi>' < n"
             and pair_notin_ff: "(numpair J k, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<notin> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)"
      using 3 holds_skolem1c less.prems unfolding \<phi>'_def skolems_bounded_def by blast+
    have pre: "is_prenex \<phi>'"
      using "3"(1) pair_notin_ff holds_skolem1a \<open>is_prenex p\<close> \<phi>'_def by blast
    define \<phi>'' where "\<phi>'' \<equiv> skolems J \<phi>' (Suc k)"
    have skos: "skolems J (\<^bold>\<exists>x\<^bold>. \<phi>) k = \<phi>''"
      by (metis \<phi>'_def \<phi>''_def ppat_simpB skolems_eq)
    have "functions_form \<phi>' \<subseteq> insert (numpair J k, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) (functions_form p)"
      using "3"(1) pair_notin_ff \<phi>'_def holds_skolem1f \<open>is_prenex p\<close> by presburger
    then have skbo: "skolems_bounded \<phi>' J (Suc k)"
      unfolding skolems_bounded_def less_Suc_eq
      by (meson insert_iff less.prems(3) old.prod.inject prod_encode_eq skolems_bounded_def subsetD)
    have prex: "is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)"
      using "3"(1) \<open>is_prenex p\<close> by blast
    have **: "\<exists>M'. dom M' = dom M \<and> intrp_rel M' = intrp_rel M
           \<and> (\<forall>g. (\<exists>zs. intrp_fn M' g zs \<noteq> intrp_fn M g zs) \<longrightarrow> (\<exists>l\<ge>k. g = numpair J l)) 
           \<and> is_interpretation (language {skolems J \<phi>' (Suc k)}) M' 
           \<and> satisfies M' {skolems J \<phi>' (Suc k)}"
      if "is_interpretation (language {(\<^bold>\<exists>x\<^bold>. \<phi>)}) M"
        and "dom M \<noteq> {}"
        and M_extend: "\<And>\<beta>. is_valuation M \<beta> \<Longrightarrow> (\<exists>a \<in> dom M. M\<^bold>, \<beta>(x:=a) \<Turnstile> \<phi>)"
      for M :: "'a intrp"
    proof -
      have M: "is_interpretation (language {\<phi>}) M"
        using lang_singleton that(1) by auto
      with that show ?thesis
        using less.IH[OF smaller refl \<open>is_prenex \<phi>'\<close> skbo] 
        using holds_skolem1g [OF prex pair_notin_ff M] holds_exists
        by (smt (verit) \<phi>'_def nat_le_linear not_less_eq_eq satisfies_def singleton_iff)
    qed
    show ?thesis
      using less.IH [OF smaller refl pre, of "Suc k"] less.prems skolems_eq [of J p] **
      by (simp add: skbo ppat_simpB 3 \<phi>'_def satisfies_def)
  qed
qed

(* HOLDS_SKOLEMS_PRENEX in hol-light *)
corollary holds_skolems_prenex_A:
  assumes "is_prenex \<phi>" "skolems_bounded \<phi> K 0"
  shows "universal(skolems K \<phi> 0) \<and> (FV (skolems K \<phi> 0) = FV \<phi>) \<and>
         predicates_form (skolems K \<phi> 0) = predicates_form \<phi> \<and>
         functions_form \<phi> \<subseteq> functions_form (skolems K \<phi> 0) \<and>
         functions_form (skolems K \<phi> 0) \<subseteq> {(numpair K l,m) | l m. True} \<union> (functions_form \<phi>)"
  using holds_skolems_induction_A [OF refl assms] by simp

corollary holds_skolems_prenex_B:
  assumes "is_prenex \<phi>" "skolems_bounded \<phi> K 0"
      and "is_interpretation (language {skolems K \<phi> 0}) M" "dom M \<noteq> {}"
      and "is_valuation M \<beta>" "M\<^bold>,\<beta> \<Turnstile> skolems K \<phi> 0"
  shows "M\<^bold>,\<beta> \<Turnstile> \<phi>"
  using holds_skolems_induction_B [OF refl assms] by simp

corollary holds_skolems_prenex_C:
  assumes "is_prenex \<phi>" "skolems_bounded \<phi> K 0"
    and "is_interpretation (language {\<phi>}) M" "dom M \<noteq> {}" "satisfies M {\<phi>}"
  shows "\<exists>M'. dom M' = dom M \<and> intrp_rel M' = intrp_rel M \<and>
                  (\<forall>g zs. intrp_fn M' g zs \<noteq> intrp_fn M g zs
                        \<longrightarrow> (\<exists>l. 0 \<le> l \<and> g = numpair K l)) \<and>
                  is_interpretation (language {skolems K \<phi> 0}) M' \<and>
                  satisfies M' {skolems K \<phi> 0}"
  using holds_skolems_induction_C [OF refl assms] by simp

definition skopre where
  \<open>skopre k \<phi> = skolems k (prenex \<phi>) 0\<close>

(* SKOPRE in hol-light *)
lemma skopre_model: \<open>(\<forall>l m. \<not> ((numpair K l, m) \<in> functions_form \<phi>)) \<Longrightarrow>
  (universal (skopre K \<phi>) \<and>
    (FV (skopre K \<phi>) = FV \<phi>) \<and>
    (predicates_form (skopre K \<phi>) = predicates_form \<phi>) \<and>
    functions_form \<phi> \<subseteq> functions_form (skopre K \<phi>) \<and>
    functions_form (skopre K \<phi>) \<subseteq> 
      {(numpair K l, m) |l m. l \<in> UNIV \<and> m \<in> UNIV} \<union> (functions_form \<phi>) \<and>
    (\<forall>M. is_interpretation (language {\<phi>}) M \<and>
      \<not>(dom M = {}) \<and>
      (\<forall>\<beta>. is_valuation M \<beta> \<longrightarrow> M\<^bold>,\<beta> \<Turnstile> \<phi>) \<longrightarrow>
        (\<exists>M'. (dom M' = dom M) \<and>
        (intrp_rel M' = intrp_rel M) \<and>
        (\<forall>g zs. \<not> (intrp_fn M' g zs = intrp_fn M g zs) \<longrightarrow> (\<exists>l. g = numpair K l)) \<and>
        is_interpretation (language {(skopre K \<phi>)}) M' \<and>
        (\<forall>\<beta>. is_valuation M' \<beta> \<longrightarrow> M'\<^bold>,\<beta> \<Turnstile> (skopre K \<phi>)))) \<and>
    (\<forall>N. is_interpretation (language {(skopre K \<phi>)}) N \<and>
      \<not> (dom N = {}) \<longrightarrow>
      (\<forall>\<beta>. is_valuation N \<beta> \<and> (N\<^bold>,\<beta> \<Turnstile> (skopre K \<phi>)) \<longrightarrow> N\<^bold>,\<beta> \<Turnstile> \<phi>)))\<close>
  sorry

definition skolemize where
  \<open>skolemize \<phi> = skopre (num_of_form (bump_form \<phi>) + 1) (bump_form \<phi>)\<close>

(* SKOLEMIZE_WORKS in hol-light *)
lemma skolemize_works:
  \<open>(universal (skolemize \<phi>) \<and>
    (FV (skolemize \<phi>) = FV (bump_form \<phi>)) \<and>
    (predicates_form (skolemize \<phi>) = predicates_form (bump_form \<phi>)) \<and>
    functions_form (bump_form \<phi>) \<subseteq> functions_form (skolemize \<phi>) \<and>
    functions_form (skolemize \<phi>) \<subseteq> 
      {(numpair k l, m) |k l m. k = num_of_form(bump_form \<phi>) \<and> l \<in> UNIV \<and> m \<in> UNIV} \<union>
         (functions_form (bump_form \<phi>)) \<and>
    (\<forall>M. is_interpretation (language {bump_form \<phi>}) M \<and>
      \<not>(dom M = {}) \<and>
      (\<forall>\<beta>. is_valuation M \<beta> \<longrightarrow> M\<^bold>,\<beta> \<Turnstile> (bump_form \<phi>)) \<longrightarrow>
        (\<exists>M'. (dom M' = dom M) \<and>
        (intrp_rel M' = intrp_rel M) \<and>
        (\<forall>g zs. \<not> (intrp_fn M' g zs = intrp_fn M g zs) \<longrightarrow> 
          (\<exists>l. g = numpair (num_of_form(bump_form \<phi>)) l)) \<and>
        is_interpretation (language {(skolemize \<phi>)}) M' \<and>
        (\<forall>\<beta>. is_valuation M' \<beta> \<longrightarrow> M'\<^bold>,\<beta> \<Turnstile> (skolemize \<phi>)))) \<and>
    (\<forall>N. is_interpretation (language {(skolemize \<phi>)}) N \<and>
      \<not> (dom N = {}) \<longrightarrow>
      (\<forall>\<beta>. is_valuation N \<beta> \<and> (N\<^bold>,\<beta> \<Turnstile> (skolemize \<phi>)) \<longrightarrow> N\<^bold>,\<beta> \<Turnstile> (bump_form \<phi>))))\<close>
  sorry

(* FUNCTIONS_FORM_SKOLEMIZE in hol-light *)
lemma functions_form_skolemize: \<open>(f, m) \<in> functions_form (skolemize \<phi>) \<Longrightarrow>
  (\<exists>k. (f = numpair 0 k) \<and> (k,m) \<in> functions_form \<phi>) \<or>
  (\<exists>l. (f = numpair (num_of_form (bump_form \<phi>) + 1) l))\<close>
  sorry

definition skomod1 where
  \<open>skomod1 \<phi> M = (if (\<forall>\<beta>. is_valuation M \<beta> \<longrightarrow> M\<^bold>,\<beta> \<Turnstile> \<phi>)
    then (SOME M'. (dom M' = dom (bump_intrp M)) \<and>
      intrp_rel M' = intrp_rel (bump_intrp M) \<and>
      (\<forall>g zs. \<not>(intrp_fn M' g zs = intrp_fn (bump_intrp M) g zs) \<longrightarrow>
        (\<exists>l. g = numpair (num_of_form (bump_form \<phi>) + 1) l)) \<and>
      is_interpretation (language {skolemize \<phi>}) M' \<and>
      (\<forall>\<beta>. is_valuation M' \<beta> \<longrightarrow> M'\<^bold>,\<beta> \<Turnstile> (skolemize \<phi>)))
    else (Abs_intrp (dom M, (\<lambda>g zs. (SOME a. a \<in> dom M)), intrp_rel M)))\<close>

(* SKOMOD1_WORKS in hol-light *)
lemma skomod1_works:
  \<open>is_interpretation (language {\<phi>}) M \<and>
      \<not>(dom M = {}) \<longrightarrow>
        (dom (skomod1 \<phi> M) = dom (bump_intrp M)) \<and>
        (intrp_rel (skomod1 \<phi> M) = intrp_rel (bump_intrp M)) \<and>
        is_interpretation (language {skolemize \<phi>}) (skomod1 \<phi> M) \<and>
        (\<forall>\<beta>. is_valuation M \<beta> \<longrightarrow> M\<^bold>,\<beta> \<Turnstile> (\<phi>)) \<longrightarrow>
          (\<forall>g zs. \<not> (intrp_fn (skomod1 \<phi> M) g zs = intrp_fn (bump_intrp M) g zs) \<longrightarrow> 
            (\<exists>l. g = numpair (num_of_form (bump_form \<phi>) + 1) l)) \<and>
          (\<forall>\<beta>. is_valuation (skomod1 \<phi> M) \<beta> \<longrightarrow> (skomod1 \<phi> M)\<^bold>,\<beta> \<Turnstile> (skolemize \<phi>))\<close>
  sorry

definition skomod where
  \<open>skomod M = Abs_intrp (dom M, 
    (\<lambda>g zs. if numfst g = 0 then intrp_fn M (numsnd g) zs
      else intrp_fn (skomod1 (unbump_form (form_of_num ((numfst g) - 1))) M ) g zs),
    intrp_rel M)\<close>

(* SKOMOD_INTERPRETATION in hol-light *)
lemma skomod_interpretation: \<open>is_interpretation (language {\<phi>}) M \<and> \<not> (dom M = {}) \<Longrightarrow>
  is_interpretation (language {skolemize \<phi>}) (skomod M)\<close>
  sorry

(* SKOMOD_WORKS in hol-light *)
lemma skomod_works: \<open>is_interpretation (language {\<phi>}) M \<and> \<not> (dom M = {}) \<Longrightarrow>
  (\<forall>\<beta>. is_valuation M \<beta> \<longrightarrow> M\<^bold>,\<beta> \<Turnstile> \<phi>) \<longleftrightarrow> 
  (\<forall>\<beta>. is_valuation (skomod M) \<beta> \<longrightarrow> (skomod M)\<^bold>,\<beta> \<Turnstile> (skolemize \<phi>))\<close>
  sorry

(* SKOLEMIZE_SATISFIABLE *)
lemma skolemize_satisfiable: \<open>(\<exists>M. \<not> (dom M = {}) \<and> is_interpretation (language S) M \<and> 
  satisfies M S) \<longleftrightarrow> (\<exists>M. \<not> (dom M = {}) \<and> is_interpretation (language {skolemize \<phi> |\<phi>. \<phi> \<in> S}) M 
  \<and> satisfies M {skolemize \<phi> |\<phi>. \<phi> \<in> S})\<close>
  sorry


fun specialize :: "form \<Rightarrow> form" where
  \<open>specialize \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>specialize (Atom p ts) = Atom p ts\<close>
| \<open>specialize (\<phi> \<^bold>\<longrightarrow> \<psi>) = \<phi> \<^bold>\<longrightarrow> \<psi>\<close>
| \<open>specialize (\<^bold>\<forall>x\<^bold>. \<phi>) = specialize \<phi>\<close>


(* SPECIALIZE_SATISFIES in hol-light *)
lemma specialize_satisfies: 
  \<open>\<not> (dom M = {}) \<Longrightarrow> (satisfies M s \<longleftrightarrow> satisfies M {specialize \<phi> |\<phi>. \<phi> \<in> s})\<close>
  sorry

(* SPECIALIZE_QFREE in hol-light *)
lemma specialize_qfree: \<open>universal \<phi> \<Longrightarrow> qfree (specialize \<phi>)\<close>
  sorry

(* SPECIALIZE_LANGUAGE in hol-light *)
lemma specialize_language: \<open>language {specialize \<phi> |\<phi>. \<phi> \<in> s} = language s\<close>
  unfolding language_def functions_forms_def predicates_def
  sorry

definition skolem :: "form \<Rightarrow> form" where
  \<open>skolem \<phi> = specialize(skolemize \<phi>)\<close>

lemma skolem_qfree: \<open>qfree (skolem \<phi>)\<close>
  sorry

lemma skolem_satisfiable: \<open>(\<exists>M. \<not> (dom M = {}) \<and> interpretation (language s) M \<and> satisfies M s)
  = (\<exists>M. \<not> (dom M = {}) \<and> interpretation (language {skolem \<phi> |\<phi>. \<phi> \<in> s}) M \<and> 
      satisfies M {skolem \<phi> |\<phi>. \<phi> \<in> s})\<close>
  sorry

end
