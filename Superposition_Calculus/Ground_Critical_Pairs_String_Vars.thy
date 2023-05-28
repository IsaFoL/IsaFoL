theory Ground_Critical_Pairs_String_Vars
  imports
    CR.Critical_Pairs
    Ground_Critical_Pairs
begin

lemma ballI2: "(\<And>x y. (x, y) \<in> A \<Longrightarrow> P x y) \<Longrightarrow> \<forall>(x, y) \<in> A. P x y"
  by auto

abbreviation is_ground_trm where
  "is_ground_trm t \<equiv> vars_term t = {}"

lemma mem_ground_critical_pairs_if_mem_critical_pairs:
  fixes s t :: "('f, string) term"
  assumes
    ground_P: "\<forall>(s, t) \<in> P. is_ground_trm s \<and> is_ground_trm t" and
    ground_R: "\<forall>(s, t) \<in> R. is_ground_trm s \<and> is_ground_trm t" and
    crit_pair: "(b, s, t) \<in> critical_pairs P R"
  shows "(s, t) \<in> ground_critical_pairs P R"
proof -
  from crit_pair obtain ctxt l r l' r' l'' \<sigma> \<tau> where
    "b = (ctxt = \<box>)" and
    "s = (ctxt \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>" and
    "t = r \<cdot> \<sigma>" and
    "(l, r) \<in> P" and
    "(l', r') \<in> R" and
    "l = ctxt\<langle>l''\<rangle>" and
    "is_Fun l''" and
    mgu: "mgu_var_disjoint_string l'' l' = Some (\<sigma>, \<tau>)"
    unfolding critical_pairs_def by auto

  from ground_P have "is_ground_trm l" and "is_ground_trm r"
    using \<open>(l, r) \<in> P\<close> by auto

  from ground_R have "is_ground_trm l'" and "is_ground_trm r'"
    using \<open>(l', r') \<in> R\<close> by auto

  have "vars_ctxt ctxt = {}" and "is_ground_trm l''"
    using \<open>is_ground_trm l\<close>
    unfolding \<open>l = ctxt\<langle>l''\<rangle>\<close>
    by (simp_all add: vars_term_ctxt_apply)

  have "l'' = l'"
    using mgu \<open>is_ground_trm l''\<close> \<open>is_ground_trm l'\<close>
    by (metis empty_iff mgu_var_disjoint_string_sound subst_apply_term_empty term_subst_eq_conv)

  show ?thesis
    unfolding ground_critical_pairs_def mem_Collect_eq
  proof (intro exI conjI)
    show "(ctxt\<langle>l''\<rangle>, r) \<in> P"
      using \<open>(l, r) \<in> P\<close>
      unfolding \<open>l = ctxt\<langle>l''\<rangle>\<close>
      by argo
  next
    show "(l'', r') \<in> R"
      unfolding \<open>l'' = l'\<close>
      using \<open>(l', r') \<in> R\<close>
      by argo
  next
    show "(s, t) = (ctxt\<langle>r'\<rangle>, r)"
      unfolding \<open>s = (ctxt \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>\<close> \<open>t = r \<cdot> \<sigma>\<close>
      using \<open>vars_ctxt ctxt = {}\<close> \<open>is_ground_trm r'\<close> \<open>is_ground_trm r\<close>
      by (metis ctxt_subst_eq ctxt_subst_id empty_iff subst.cop_nil term_subst_eq_conv)
  qed
qed

lemma mem_critical_pairs_if_mem_ground_critical_pairs:
  fixes s t :: "('f, string) term"
  assumes
    ground_P: "\<forall>(s, t) \<in> P. is_ground_trm s \<and> is_ground_trm t" and
    ground_R: "\<forall>(s, t) \<in> R. is_ground_trm s \<and> is_ground_trm t" and
    crit_pair: "(s, t) \<in> ground_critical_pairs P R"
  shows "\<exists>b. (b, s, t) \<in> critical_pairs P R"
proof -
  from crit_pair obtain ctxt l r\<^sub>P r\<^sub>R where
    "(s, t) = (ctxt\<langle>r\<^sub>R\<rangle>, r\<^sub>P)" and
    "(ctxt\<langle>l\<rangle>, r\<^sub>P) \<in> P" and
    "(l, r\<^sub>R) \<in> R"
    unfolding ground_critical_pairs_def by auto

  from ground_P have "vars_ctxt ctxt = {}" and "is_ground_trm l" and "is_ground_trm r\<^sub>P"
    unfolding atomize_conj
    using \<open>(ctxt\<langle>l\<rangle>, r\<^sub>P) \<in> P\<close> vars_term_ctxt_apply by fastforce

  from ground_R have "is_ground_trm r\<^sub>R"
    using \<open>(l, r\<^sub>R) \<in> R\<close> by auto

  obtain \<mu>\<^sub>1 \<mu>\<^sub>2 where mgu: "mgu_var_disjoint_string l l = Some (\<mu>\<^sub>1, \<mu>\<^sub>2)"
    using mgu_var_disjoint_string_complete by blast

  show ?thesis
  proof (intro exI critical_pairsI)
    show "(ctxt\<langle>l\<rangle>, r\<^sub>P) \<in> P"
      using \<open>(ctxt\<langle>l\<rangle>, r\<^sub>P) \<in> P\<close> .
  next
    show "(l, r\<^sub>R) \<in> R"
      using \<open>(l, r\<^sub>R) \<in> R\<close> .
  next
    show "ctxt\<langle>l\<rangle> = ctxt\<langle>l\<rangle>" ..
  next
    show "is_Fun l"
      using \<open>is_ground_trm l\<close> by fastforce
  next
    show "mgu_var_disjoint_string l l = Some (\<mu>\<^sub>1, \<mu>\<^sub>2)"
      using mgu .
  next
    show "t = r\<^sub>P \<cdot> \<mu>\<^sub>1"
      using \<open>(s, t) = (ctxt\<langle>r\<^sub>R\<rangle>, r\<^sub>P)\<close> \<open>is_ground_trm r\<^sub>P\<close>
      by (simp add: subst_apply_term_ident)
  next
    show "s = (ctxt \<cdot>\<^sub>c \<mu>\<^sub>1)\<langle>r\<^sub>R \<cdot> \<mu>\<^sub>2\<rangle>"
      using \<open>(s, t) = (ctxt\<langle>r\<^sub>R\<rangle>, r\<^sub>P)\<close> \<open>vars_ctxt ctxt = {}\<close> \<open>is_ground_trm r\<^sub>R\<close>
      by (metis Pair_inject ctxt_subst_eq ctxt_subst_id empty_iff inf_bot_left
          subst_apply_term_ident)
  next
    show "(ctxt = \<box>) = (ctxt = \<box>)" ..
  qed
qed

lemma ground_critical_pair_lemma:
  fixes R :: "('f, string) trs"
  assumes ground_R: "\<forall>(s, t) \<in> R. is_ground_trm s \<and> is_ground_trm t"
  shows "WCR (rstep R) \<longleftrightarrow> (\<forall> (s, t) \<in> ground_critical_pairs R R. (s, t) \<in> (rstep R)\<^sup>\<down>)"
  unfolding critical_pair_lemma
  using mem_critical_pairs_if_mem_ground_critical_pairs[OF ground_R ground_R]
  using mem_ground_critical_pairs_if_mem_critical_pairs[OF ground_R ground_R]
  by (metis (no_types, lifting) case_prodD case_prodI2)

global_interpretation ground_critical_pair_lemma "undefined :: 'f" "undefined :: string"
proof unfold_locales
  fix R :: "('f, string) trs"
  assume "vars_trs R = {}"
  hence ground_R: "\<forall>(s, t)\<in>R. is_ground_trm s \<and> is_ground_trm t"
    by (auto simp add: vars_trs_def vars_rule_def)
  show "WCR (rstep R) = (ground_critical_pairs R R \<subseteq> (rstep R)\<^sup>\<down>)"
    using ground_critical_pair_lemma[OF ground_R] by auto
qed

end