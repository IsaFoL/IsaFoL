theory Porting

imports Skolem_Normal_Form "HOL-ex.Sketch_and_Explore"

begin

(*Sema.formula_semantics and holds both use the symbol \<Turnstile> !*)

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
      and holds_skolem1c: "Prenex_Normal_Form.size (skolem1 f x \<phi>) < Prenex_Normal_Form.size (\<^bold>\<exists>x\<^bold>. \<phi>)" (is "?C")
      and holds_skolem1d: "predicates_form (skolem1 f x \<phi>) = predicates_form (\<^bold>\<exists>x\<^bold>. \<phi>)" (is "?D")
      and holds_skolem1e: "functions_form (\<^bold>\<exists>x\<^bold>. \<phi>) \<subseteq> functions_form (skolem1 f x \<phi>)" (is "?E")
      and holds_skolem1f: "functions_form (skolem1 f x \<phi>) 
                          \<subseteq> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<triangleright> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)" (is "?F")
proof -
  show ?A
    by (metis form.inject(2) form.inject(3) prenex_ex_phi prenex_formsubst prenex_imp qfree_no_quantif skolem1_def)
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
    moreover have \<open>{g. \<exists>y \<in> FV \<phi>. g \<in> functions_term (Var y \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV ((\<^bold>\<exists>x\<^bold>. \<phi>)))))))} 
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
(*  next
    show \<open>\<forall>g zs. (\<forall>e\<in>set zs. e \<in> dom I) \<longrightarrow> FN g zs \<in> dom I\<close>
      unfolding FN_def define_fn_def
    proof (clarsimp, intro conjI strip)
      fix g and zs :: "'a list"
      assume len_zs: \<open>g = f \<and> length zs = card (FV \<phi> - {x})\<close> and
        zs_in: \<open>\<forall>e\<in>set zs. e \<in> dom I\<close>
      have len_eq: \<open>length (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) = length zs\<close>
        using len_zs by simp
      have \<open>\<forall>v. (intrp_f zs) v \<in> dom I\<close>
        using fun_upds_prop[OF len_eq zs_in] by (simp add: nempty_I some_in_eq intrp_f_def)
      then have \<open>\<exists>a. a \<in> dom I \<and> I, (intrp_f zs)(x := a) \<Turnstile> \<phi>\<close>
        using ex_a_mod_phi by blast
      then show \<open>thex zs \<in> dom I\<close>
        unfolding thex_def by (metis (no_types, lifting) someI_ex)
    next
      fix g and zs :: "'a list"
      assume "g = f \<longrightarrow> length zs \<noteq> card (FV \<phi> - {x})" "\<forall>e\<in>set zs. e \<in> dom I"
      show \<open>intrp_fn I g zs \<in> dom I\<close>
        using FN_dom_to_dom \<open>\<forall>e\<in>set zs. e \<in> dom I\<close> by blast
    qed
  next
    show \<open>\<forall>p. \<forall>es\<in>intrp_rel I p. \<forall>e\<in>set es. e \<in> dom I\<close>
      by (meson intrp_is_struct struct_def) *)
  qed
  define M :: "'a intrp" where \<open>M =  Abs_intrp (dom I, FN, intrp_rel I)\<close>
  show thesis
  proof
    show dom_M_I_eq: \<open>dom M = dom I\<close>
      using M_is_struct unfolding M_def by simp
    show intrp_rel_eq: \<open>intrp_rel M = intrp_rel I\<close>
      using M_is_struct unfolding M_def by simp
    show intrp_fn_eq: "\<And>g zs. g \<noteq> f \<or> length zs \<noteq> card (FV (\<^bold>\<exists>x\<^bold>. \<phi>)) \<Longrightarrow> intrp_fn M g zs = intrp_fn I g zs"
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
        using nempty_I ex_a_mod_phi sorry (* by (metis FN_dom_to_dom dom_M_I_eq zs_in2) *)
    qed
    show is_interp_M: \<open>is_interpretation (language {skolem1 f x \<phi>}) M\<close>
      unfolding is_interpretation_def
    proof clarsimp
      fix g l
      assume in_skol: \<open>(g, length l) \<in> fst (language {skolem1 f x \<phi>})\<close> and in_dom_M: \<open>set l \<subseteq> dom M\<close>
      have \<open>(g, length l) \<in> fst (language {\<phi>}) \<or> (g, length l) = (f, card (FV \<phi> - {x}))\<close>
        using holds_skolem1f in_skol lang_singleton notin_ff prenex_ex_phi by auto
      then show \<open>intrp_fn M g l \<in> dom M\<close>
        using interp_I dom_M_I_eq intrp_fn_eq in_dom_I in_dom_M
        unfolding language_def is_interpretation_def
        sorry
        (*by (meson FN_dom_to_dom subsetD)*)
    qed

    show "M\<^bold>,\<beta> \<Turnstile> skolem1 f x \<phi>" if "is_valuation M \<beta>" for \<beta>
    proof -
      have "M\<^bold>,\<beta>(x:=thex (map \<beta> (sorted_list_of_set(FV(\<^bold>\<exists>x\<^bold>. \<phi>))))) \<Turnstile> \<phi>"
      proof (rule holds_indep_intrp_if2)
        have "I\<^bold>, (intrp_f (map \<beta> (sorted_list_of_set(FV(\<^bold>\<exists>x\<^bold>. \<phi>)))))(x:=a) \<Turnstile> \<phi>  \<longleftrightarrow>  I\<^bold>, \<beta>(x:=a) \<Turnstile> \<phi>"  for a
        proof (intro holds_indep_\<beta>_if strip)
          fix v
          assume "v \<in> FV \<phi>"
          then have "v=x \<or> v \<in> FV (\<^bold>\<exists>x\<^bold>. \<phi>)"
            using FV_exists by blast
          moreover have "foldr (\<lambda>kv f. f(fst kv := snd kv)) (zip vs (map \<beta> vs)) (\<lambda>z. SOME c. c \<in> dom I) w = \<beta> w"
            if "w \<in> set vs" "set vs \<subseteq> FV (\<^bold>\<exists>x\<^bold>. \<phi>)" for vs w
            using that by (induction vs) auto
          ultimately
          show "((intrp_f (map \<beta> (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))) (x := a)) v = (\<beta>(x := a)) v"
            using finite_FV intrp_f_def by auto
        qed
        then show "I\<^bold>,\<beta> (x := thex (map \<beta> (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))) \<Turnstile> \<phi>"
          by (metis (mono_tags, lifting) dom_M_I_eq ex_a_mod_phi is_valuation_def that thex_def verit_sko_ex')
        show "dom I = dom M"
          using dom_M_I_eq by auto
        show "\<forall>p. intrp_rel I p = intrp_rel M p"
          using intrp_rel_eq by auto
        show "\<forall>f zs. (f, length zs) \<in> functions_form \<phi> \<longrightarrow> intrp_fn I f zs = intrp_fn M f zs"
          using functions_form.simps notin_ff intrp_fn_eq 
          by (metis sup_bot.right_neutral)
      qed
      moreover have "FN f (map \<beta> (sorted_list_of_set (FV \<phi> - {x}))) = thex (map \<beta> (sorted_list_of_set (FV \<phi> - {x})))"
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

end
