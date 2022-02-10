theory Prop_Abstract_Transformation
imports Entailment_Definition.Prop_Logic Weidenbach_Book_Base.Wellfounded_More

begin

text \<open>This file is devoted to abstract properties of the transformations, like consistency
  preservation and lifting from terms to proposition. \<close>


section \<open>Rewrite Systems and Properties\<close>

subsection \<open>Lifting of Rewrite Rules\<close>

text \<open>We can lift a rewrite relation r over a full1 formula: the relation \<open>r\<close> works on terms,
  while \<open>propo_rew_step\<close> works on formulas.\<close>

inductive propo_rew_step :: "('v propo \<Rightarrow> 'v propo \<Rightarrow> bool) \<Rightarrow> 'v propo \<Rightarrow> 'v propo \<Rightarrow> bool"
  for r :: "'v propo \<Rightarrow> 'v propo \<Rightarrow> bool" where
global_rel: "r \<phi> \<psi> \<Longrightarrow> propo_rew_step r \<phi> \<psi>" |
propo_rew_one_step_lift: "propo_rew_step r \<phi> \<phi>' \<Longrightarrow> wf_conn c (\<psi>s @ \<phi> # \<psi>s')
  \<Longrightarrow> propo_rew_step r (conn c (\<psi>s @ \<phi> # \<psi>s')) (conn c (\<psi>s @ \<phi>'# \<psi>s'))"

text \<open>Here is a more precise link between the lifting and the subformulas: if a rewriting takes
  place between @{term \<phi>} and @{term \<phi>'}, then there are two subformulas @{term \<psi>} in @{term \<phi>} and
  @{term \<psi>'} in @{term \<phi>'}, @{term \<psi>'} is the result of the rewriting of @{term r} on @{term \<psi>}. \<close>

text \<open>This lemma is only a health condition:\<close>
lemma propo_rew_step_subformula_imp:
shows "propo_rew_step r \<phi> \<phi>' \<Longrightarrow> \<exists> \<psi> \<psi>'. \<psi> \<preceq> \<phi> \<and> \<psi>' \<preceq> \<phi>' \<and> r \<psi> \<psi>'"
  apply (induct rule: propo_rew_step.induct)
    using subformula.simps subformula_into_subformula apply blast
  using wf_conn_no_arity_change subformula_into_subformula wf_conn_no_arity_change_helper
  in_set_conv_decomp by metis


text \<open>The converse is moreover true: if there is a @{term \<psi>} and @{term \<psi>'}, then every formula
  @{term \<phi>} containing @{term \<psi>}, can be rewritten into a formula @{term \<phi>'}, such that it contains
  @{term \<phi>'}. \<close>
lemma propo_rew_step_subformula_rec:
  fixes \<psi> \<psi>' \<phi> :: "'v propo"
  shows "\<psi> \<preceq> \<phi> \<Longrightarrow> r \<psi> \<psi>' \<Longrightarrow> (\<exists>\<phi>'. \<psi>' \<preceq> \<phi>' \<and> propo_rew_step r \<phi> \<phi>')"
proof (induct \<phi> rule: subformula.induct)
  case subformula_refl
  then have "propo_rew_step r \<psi> \<psi>'" using propo_rew_step.intros by auto
  moreover have "\<psi>' \<preceq> \<psi>'" using Prop_Logic.subformula_refl by auto
  ultimately show "\<exists>\<phi>'. \<psi>' \<preceq> \<phi>' \<and> propo_rew_step r \<psi> \<phi>'" by fastforce
next
  case (subformula_into_subformula \<psi>'' l c)
  note IH = this(4) and r = this(5) and \<psi>'' = this(1) and wf = this(2) and incl = this(3)
  then obtain \<phi>' where *: "\<psi>' \<preceq> \<phi>' \<and> propo_rew_step r \<psi>'' \<phi>'" by metis
  moreover obtain \<xi> \<xi>' :: "'v propo list" where
    l: "l = \<xi> @ \<psi>'' # \<xi>'" using List.split_list \<psi>'' by metis
  ultimately have "propo_rew_step r (conn c l) (conn c (\<xi> @ \<phi>' # \<xi>'))"
    using propo_rew_step.intros(2) wf by metis
  moreover have "\<psi>' \<preceq> conn c (\<xi> @ \<phi>' # \<xi>')"
    using wf * wf_conn_no_arity_change Prop_Logic.subformula_into_subformula
    by (metis (no_types) in_set_conv_decomp l wf_conn_no_arity_change_helper)
  ultimately show "\<exists>\<phi>'. \<psi>' \<preceq> \<phi>' \<and> propo_rew_step r (conn c l) \<phi>'" by metis
qed

lemma propo_rew_step_subformula:
  "(\<exists>\<psi> \<psi>'. \<psi> \<preceq> \<phi> \<and> r \<psi> \<psi>') \<longleftrightarrow> (\<exists>\<phi>'. propo_rew_step r \<phi> \<phi>')"
  using propo_rew_step_subformula_imp propo_rew_step_subformula_rec by metis+

lemma consistency_decompose_into_list:
  assumes wf: "wf_conn c l" and wf': "wf_conn c l'"
  and same: "\<forall>n. A \<Turnstile> l ! n \<longleftrightarrow> (A \<Turnstile> l' ! n)"
  shows "A \<Turnstile> conn c l \<longleftrightarrow> A \<Turnstile> conn c l'"
proof (cases c rule: connective_cases_arity_2)
  case nullary
  then show "(A \<Turnstile> conn c l) \<longleftrightarrow> (A \<Turnstile> conn c l')" using wf wf' by auto
next
  case unary note c = this
  then obtain a where l: "l = [a]" using wf_conn_Not_decomp wf by metis
  obtain a' where l': "l' = [a']" using wf_conn_Not_decomp wf' c by metis
  have "A \<Turnstile> a \<longleftrightarrow> A \<Turnstile> a'" using l l' by (metis nth_Cons_0 same)
  then show "A \<Turnstile> conn c l \<longleftrightarrow> A \<Turnstile> conn c l'" using l l' c by auto
next
  case binary note c = this
  then obtain a b where l: "l = [a, b]"
    using wf_conn_bin_list_length list_length2_decomp wf by metis
  obtain a' b' where l': "l' = [a', b']"
    using wf_conn_bin_list_length list_length2_decomp wf' c by metis

  have p: "A \<Turnstile> a \<longleftrightarrow> A \<Turnstile> a'" "A \<Turnstile> b \<longleftrightarrow> A \<Turnstile> b'"
    using l l' same by (metis diff_Suc_1 nth_Cons' nat.distinct(2))+
  show "A \<Turnstile> conn c l \<longleftrightarrow> A \<Turnstile> conn c l'"
    using wf c p unfolding binary_connectives_def l l' by auto
qed

text \<open>Relation between @{term propo_rew_step} and the rewriting we have seen before:
  @{term "propo_rew_step r \<phi> \<phi>'"} means that we rewrite @{term \<psi>} inside @{term \<phi>}
  (ie at a path @{term p}) into @{term \<psi>'}.\<close>
lemma propo_rew_step_rewrite:
  fixes \<phi> \<phi>' :: "'v propo" and r :: "'v propo \<Rightarrow> 'v propo \<Rightarrow> bool"
  assumes "propo_rew_step r \<phi> \<phi>'"
  shows "\<exists>\<psi> \<psi>' p. r \<psi> \<psi>' \<and> path_to p \<phi> \<psi> \<and> replace_at p \<phi> \<psi>' = \<phi>'"
  using assms
proof (induct rule: propo_rew_step.induct)
  case(global_rel \<phi> \<psi>)
  moreover have "path_to [] \<phi> \<phi>" by auto
  moreover have "replace_at [] \<phi> \<psi> = \<psi>" by auto
  ultimately show ?case by metis
next
  case (propo_rew_one_step_lift \<phi> \<phi>' c \<xi> \<xi>') note rel = this(1) and IH0 = this(2) and corr = this(3)
  obtain \<psi> \<psi>' p where IH: "r \<psi> \<psi>' \<and> path_to p \<phi> \<psi> \<and> replace_at p \<phi> \<psi>' = \<phi>'" using IH0 by metis

  {
     fix x :: "'v"
     assume "c = CT \<or> c = CF \<or> c = CVar x"
     then have False using corr by auto
     then have "\<exists>\<psi> \<psi>' p. r \<psi> \<psi>' \<and> path_to p (conn c (\<xi>@ (\<phi> # \<xi>'))) \<psi>
                       \<and> replace_at p (conn c (\<xi>@ (\<phi> # \<xi>'))) \<psi>' = conn c (\<xi>@ (\<phi>' # \<xi>')) "
       by fast
  }
  moreover {
     assume c: "c = CNot"
     then have empty: "\<xi> =[]" "\<xi>'=[]" using corr by auto
     have "path_to (L#p) (conn c (\<xi>@ (\<phi> # \<xi>'))) \<psi>"
       using c empty IH wf_conn_unary path_to_l by fastforce
     moreover have "replace_at (L#p) (conn c (\<xi>@ (\<phi> # \<xi>'))) \<psi>' = conn c (\<xi>@ (\<phi>' # \<xi>'))"
       using c empty IH by auto
     ultimately have "\<exists>\<psi> \<psi>' p. r \<psi> \<psi>' \<and> path_to p (conn c (\<xi>@ (\<phi> # \<xi>'))) \<psi>
                               \<and> replace_at p (conn c (\<xi>@ (\<phi> # \<xi>'))) \<psi>' = conn c (\<xi>@ (\<phi>' # \<xi>'))"
     using IH by metis
  }
  moreover {
     assume c: "c \<in> binary_connectives"
     have "length (\<xi>@ \<phi> # \<xi>') = 2" using wf_conn_bin_list_length corr c by metis
     then have "length \<xi> + length \<xi>' = 1" by auto
     then have ld: "(length \<xi> = 1 \<and> length \<xi>' = 0) \<or> (length \<xi> = 0 \<and> length \<xi>' = 1) " by arith
     obtain a b where ab: "(\<xi>=[] \<and> \<xi>'=[b]) \<or> (\<xi>=[a] \<and> \<xi>'=[])"
       using ld by (case_tac \<xi>, case_tac \<xi>', auto)
     {
        assume \<phi>: "\<xi>=[] \<and> \<xi>'=[b]"
        have "path_to (L#p) (conn c (\<xi>@ (\<phi> # \<xi>'))) \<psi>"
          using \<phi> c IH ab corr by (simp add: path_to_l)
        moreover have "replace_at (L#p) (conn c (\<xi>@ (\<phi> # \<xi>'))) \<psi>' = conn c (\<xi>@ (\<phi>' # \<xi>'))"
          using c IH ab \<phi> unfolding binary_connectives_def by auto
        ultimately have "\<exists>\<psi> \<psi>' p. r \<psi> \<psi>' \<and> path_to p (conn c (\<xi>@ (\<phi> # \<xi>'))) \<psi>
          \<and> replace_at p (conn c (\<xi>@ (\<phi> # \<xi>'))) \<psi>' = conn c (\<xi>@ (\<phi>' # \<xi>')) "
          using IH by metis
     }
     moreover {
        assume \<phi>: "\<xi>=[a]" " \<xi>'=[]"
        then have "path_to (R#p) (conn c (\<xi>@ (\<phi> # \<xi>'))) \<psi>"
          using c IH corr path_to_r corr \<phi>  by (simp add: path_to_r)
        moreover have "replace_at (R#p) (conn c (\<xi>@ (\<phi> # \<xi>'))) \<psi>' = conn c (\<xi>@ (\<phi>' # \<xi>'))"
          using c IH ab \<phi> unfolding binary_connectives_def by auto
        ultimately have ?case using IH by metis
     }
     ultimately have ?case using ab by blast
  }
  ultimately show ?case using connective_cases_arity by blast
qed



subsection \<open>Consistency Preservation\<close>

text \<open>We define \<open>preserve_models\<close>: it means that a relation preserves consistency.\<close>
definition preserve_models where
"preserve_models r \<longleftrightarrow> (\<forall>\<phi> \<psi>. r \<phi> \<psi> \<longrightarrow> (\<forall>A. A \<Turnstile> \<phi> \<longleftrightarrow> A \<Turnstile> \<psi>))"


lemma propo_rew_step_preservers_val_explicit:
"propo_rew_step r \<phi> \<psi> \<Longrightarrow> preserve_models r \<Longrightarrow> propo_rew_step r \<phi> \<psi> \<Longrightarrow> (\<forall>A. A \<Turnstile>\<phi> \<longleftrightarrow> A\<Turnstile>\<psi>)"
  unfolding preserve_models_def
proof (induction rule: propo_rew_step.induct)
  case global_rel
  then show ?case by simp
next
  case (propo_rew_one_step_lift \<phi> \<phi>' c \<xi> \<xi>') note rel = this(1) and wf = this(2)
    and IH = this(3)[OF this(4) this(1)]  and consistent = this(4)
  {
    fix A
    from IH have "\<forall>n. (A \<Turnstile> (\<xi> @ \<phi> # \<xi>') ! n) = (A \<Turnstile> (\<xi> @ \<phi>' # \<xi>') ! n)"
      by (metis (mono_tags, opaque_lifting) list_update_length nth_Cons_0 nth_append_length_plus
        nth_list_update_neq)
    then have " (A \<Turnstile> conn c (\<xi> @ \<phi> # \<xi>')) = (A \<Turnstile> conn c (\<xi> @ \<phi>' # \<xi>'))"
      by (meson consistency_decompose_into_list wf wf_conn_no_arity_change_helper
        wf_conn_no_arity_change)
  }
  then show "\<forall>A. A \<Turnstile> conn c (\<xi> @ \<phi> # \<xi>') \<longleftrightarrow> A \<Turnstile> conn c (\<xi> @ \<phi>' # \<xi>')" by auto
qed


lemma propo_rew_step_preservers_val':
  assumes "preserve_models r"
  shows "preserve_models (propo_rew_step r)"
  using assms by (simp add: preserve_models_def propo_rew_step_preservers_val_explicit)


lemma preserve_models_OO[intro]:
"preserve_models f \<Longrightarrow> preserve_models g \<Longrightarrow> preserve_models (f OO g) "
  unfolding preserve_models_def by auto


lemma star_consistency_preservation_explicit:
  assumes "(propo_rew_step r)^** \<phi> \<psi>" and "preserve_models r"
  shows "\<forall>A. A \<Turnstile> \<phi> \<longleftrightarrow> A \<Turnstile> \<psi>"
  using assms by (induct rule: rtranclp_induct)
    (auto simp add: propo_rew_step_preservers_val_explicit)

lemma star_consistency_preservation:
"preserve_models r \<Longrightarrow>  preserve_models (propo_rew_step r)^**"
  by (simp add: star_consistency_preservation_explicit preserve_models_def)

subsection "Full Lifting"
text \<open>In the previous a relation was lifted to a formula, now we define the relation such it is
  applied as long as possible. The definition is thus simply: it can be derived and nothing more can
  be derived.\<close>

lemma full_ropo_rew_step_preservers_val[simp]:
"preserve_models r \<Longrightarrow> preserve_models (full (propo_rew_step r))"
  by (metis full_def preserve_models_def star_consistency_preservation)

lemma full_propo_rew_step_subformula:
"full (propo_rew_step r) \<phi>' \<phi> \<Longrightarrow> \<not>(\<exists> \<psi> \<psi>'. \<psi> \<preceq> \<phi> \<and> r \<psi> \<psi>')"
  unfolding full_def using propo_rew_step_subformula_rec by metis


section \<open>Transformation testing\<close>

subsection \<open>Definition and first Properties\<close>
text \<open>To prove correctness of our transformation, we create a @{term all_subformula_st} predicate.
  It tests recursively all subformulas. At each step, the actual formula is tested. The aim of this
  @{term test_symb} function is to test locally some properties of the formulas (i.e. at the level
  of the connective or at first level). This allows a clause description between the rewrite
  relation and the @{term test_symb}\<close>


definition all_subformula_st :: "('a propo \<Rightarrow> bool) \<Rightarrow> 'a propo \<Rightarrow> bool" where
"all_subformula_st test_symb \<phi> \<equiv> \<forall>\<psi>. \<psi> \<preceq> \<phi> \<longrightarrow> test_symb \<psi>"


lemma test_symb_imp_all_subformula_st[simp]:
  "test_symb FT \<Longrightarrow> all_subformula_st test_symb FT"
  "test_symb FF \<Longrightarrow> all_subformula_st test_symb FF"
  "test_symb (FVar x) \<Longrightarrow> all_subformula_st test_symb (FVar x)"
  unfolding all_subformula_st_def using subformula_leaf by metis+


lemma all_subformula_st_test_symb_true_phi:
  "all_subformula_st test_symb \<phi> \<Longrightarrow> test_symb \<phi>"
  unfolding all_subformula_st_def by auto

lemma all_subformula_st_decomp_imp:
  "wf_conn c l \<Longrightarrow> (test_symb (conn c l) \<and> (\<forall>\<phi>\<in> set l. all_subformula_st test_symb \<phi>))
  \<Longrightarrow> all_subformula_st test_symb (conn c l)"
  unfolding all_subformula_st_def by auto


text \<open>To ease the finding of proofs, we give some explicit theorem about the decomposition.\<close>
lemma all_subformula_st_decomp_rec:
  "all_subformula_st test_symb (conn c l) \<Longrightarrow> wf_conn c l
    \<Longrightarrow> (test_symb (conn c l) \<and> (\<forall>\<phi>\<in> set l. all_subformula_st test_symb \<phi>))"
  unfolding all_subformula_st_def by auto

lemma all_subformula_st_decomp:
  fixes c :: "'v connective" and l :: "'v propo list"
  assumes "wf_conn c l"
  shows "all_subformula_st test_symb (conn c l)
    \<longleftrightarrow> (test_symb (conn c l) \<and> (\<forall>\<phi>\<in> set l. all_subformula_st test_symb \<phi>))"
  using assms all_subformula_st_decomp_rec all_subformula_st_decomp_imp by metis

lemma helper_fact: "c \<in> binary_connectives \<longleftrightarrow> (c = COr \<or> c = CAnd \<or> c = CEq \<or> c = CImp)"
  unfolding binary_connectives_def by auto
lemma all_subformula_st_decomp_explicit[simp]:
  fixes \<phi> \<psi> :: "'v propo"
  shows "all_subformula_st test_symb (FAnd \<phi> \<psi>)
      \<longleftrightarrow> (test_symb (FAnd \<phi> \<psi>) \<and> all_subformula_st test_symb \<phi> \<and> all_subformula_st test_symb \<psi>)"
  and "all_subformula_st test_symb (FOr \<phi> \<psi>)
     \<longleftrightarrow> (test_symb (FOr \<phi> \<psi>) \<and>  all_subformula_st test_symb \<phi> \<and> all_subformula_st test_symb \<psi>)"
  and "all_subformula_st test_symb (FNot \<phi>)
     \<longleftrightarrow> (test_symb (FNot \<phi>) \<and>  all_subformula_st test_symb \<phi>)"
  and "all_subformula_st test_symb (FEq \<phi> \<psi>)
     \<longleftrightarrow> (test_symb (FEq \<phi> \<psi>) \<and>  all_subformula_st test_symb \<phi> \<and> all_subformula_st test_symb \<psi>)"
  and "all_subformula_st test_symb (FImp \<phi> \<psi>)
     \<longleftrightarrow> (test_symb (FImp \<phi> \<psi>) \<and> all_subformula_st test_symb \<phi> \<and> all_subformula_st test_symb \<psi>)"
proof -
  have "all_subformula_st test_symb (FAnd \<phi> \<psi>) \<longleftrightarrow> all_subformula_st test_symb (conn CAnd [\<phi>, \<psi>])"
    by auto
  moreover have "\<dots> \<longleftrightarrow>test_symb (conn CAnd [\<phi>, \<psi>])\<and>(\<forall>\<xi>\<in> set [\<phi>, \<psi>]. all_subformula_st test_symb \<xi>)"
    using all_subformula_st_decomp wf_conn_helper_facts(5) by metis
  finally show "all_subformula_st test_symb (FAnd \<phi> \<psi>)
    \<longleftrightarrow> (test_symb (FAnd \<phi> \<psi>) \<and> all_subformula_st test_symb \<phi> \<and> all_subformula_st test_symb \<psi>)"
    by simp

  have "all_subformula_st test_symb (FOr \<phi> \<psi>) \<longleftrightarrow> all_subformula_st test_symb (conn COr [\<phi>, \<psi>])"
    by auto
  moreover have "\<dots>\<longleftrightarrow>
    (test_symb (conn COr [\<phi>, \<psi>]) \<and> (\<forall>\<xi>\<in> set [\<phi>, \<psi>]. all_subformula_st test_symb \<xi>))"
    using all_subformula_st_decomp wf_conn_helper_facts(6) by metis
  finally show "all_subformula_st test_symb (FOr \<phi> \<psi>)
    \<longleftrightarrow> (test_symb (FOr \<phi> \<psi>) \<and> all_subformula_st test_symb \<phi> \<and> all_subformula_st test_symb \<psi>)"
    by simp

  have "all_subformula_st test_symb (FEq \<phi> \<psi>) \<longleftrightarrow> all_subformula_st test_symb (conn CEq [\<phi>, \<psi>])"
    by auto
  moreover have "\<dots>
    \<longleftrightarrow> (test_symb (conn CEq [\<phi>, \<psi>]) \<and> (\<forall>\<xi>\<in> set [\<phi>, \<psi>]. all_subformula_st test_symb \<xi>))"
    using all_subformula_st_decomp wf_conn_helper_facts(8) by metis
  finally show "all_subformula_st test_symb (FEq \<phi> \<psi>)
    \<longleftrightarrow> (test_symb (FEq \<phi> \<psi>) \<and> all_subformula_st test_symb \<phi> \<and> all_subformula_st test_symb \<psi>)"
    by simp

  have "all_subformula_st test_symb (FImp \<phi> \<psi>) \<longleftrightarrow> all_subformula_st test_symb (conn CImp [\<phi>, \<psi>])"
    by auto
  moreover have "\<dots>
    \<longleftrightarrow>(test_symb (conn CImp [\<phi>, \<psi>]) \<and> (\<forall>\<xi>\<in> set [\<phi>, \<psi>]. all_subformula_st test_symb \<xi>))"
    using all_subformula_st_decomp wf_conn_helper_facts(7) by metis
  finally show "all_subformula_st test_symb (FImp \<phi> \<psi>)
    \<longleftrightarrow> (test_symb (FImp \<phi> \<psi>) \<and> all_subformula_st test_symb \<phi> \<and> all_subformula_st test_symb \<psi>)"
    by simp

  have "all_subformula_st test_symb (FNot \<phi>) \<longleftrightarrow> all_subformula_st test_symb (conn CNot [\<phi>])"
    by auto
  moreover have "\<dots> = (test_symb (conn CNot [\<phi>]) \<and> (\<forall>\<xi>\<in> set [\<phi>]. all_subformula_st test_symb \<xi>))"
    using all_subformula_st_decomp wf_conn_helper_facts(1) by metis
  finally show "all_subformula_st test_symb (FNot \<phi>)
    \<longleftrightarrow> (test_symb (FNot \<phi>) \<and> all_subformula_st test_symb \<phi>)" by simp
qed



text \<open>As @{term all_subformula_st} tests recursively, the function is true on every subformula. \<close>
lemma subformula_all_subformula_st:
  "\<psi> \<preceq> \<phi> \<Longrightarrow> all_subformula_st test_symb \<phi> \<Longrightarrow> all_subformula_st test_symb \<psi>"
  by (induct rule: subformula.induct, auto simp add: all_subformula_st_decomp)


text \<open>The following theorem @{prop no_test_symb_step_exists} shows the link between the
  @{term test_symb} function and the corresponding rewrite relation @{term r}: if we assume that if
  every time @{term test_symb} is true, then a @{term r} can be applied, finally as long as
  @{term "\<not> all_subformula_st test_symb \<phi>"}, then something can be rewritten in @{term \<phi>}.\<close>
lemma no_test_symb_step_exists:
  fixes r:: "'v propo \<Rightarrow> 'v propo \<Rightarrow> bool" and test_symb:: "'v propo \<Rightarrow> bool" and x :: "'v"
  and \<phi> :: "'v propo"
  assumes
    test_symb_false_nullary: "\<forall>x. test_symb FF \<and> test_symb FT \<and> test_symb (FVar x)" and
    "\<forall>\<phi>'. \<phi>' \<preceq> \<phi> \<longrightarrow> (\<not>test_symb \<phi>') \<longrightarrow>  (\<exists> \<psi>. r \<phi>' \<psi>)" and
    "\<not> all_subformula_st test_symb \<phi>"
  shows "\<exists>\<psi> \<psi>'. \<psi> \<preceq> \<phi> \<and> r \<psi> \<psi>'"
  using assms
proof (induct \<phi> rule: propo_induct_arity)
  case (nullary \<phi> x)
  then show "\<exists>\<psi> \<psi>'. \<psi> \<preceq> \<phi> \<and> r \<psi> \<psi>'"
    using wf_conn_nullary test_symb_false_nullary by fastforce
next
  case (unary \<phi>) note IH = this(1)[OF this(2)] and r = this(2)  and nst = this(3) and subf = this(4)
  from r IH nst have H: " \<not> all_subformula_st test_symb \<phi> \<Longrightarrow> \<exists>\<psi>. \<psi> \<preceq> \<phi> \<and> (\<exists>\<psi>'. r \<psi> \<psi>')"
    by (metis subformula_in_subformula_not subformula_refl subformula_trans)
  {
    assume n: "\<not>test_symb (FNot \<phi>)"
    obtain \<psi> where "r (FNot \<phi>) \<psi>" using subformula_refl r n nst by blast
    moreover have "FNot \<phi> \<preceq> FNot \<phi>" using subformula_refl by auto
    ultimately have "\<exists>\<psi> \<psi>'. \<psi> \<preceq> FNot \<phi> \<and> r \<psi> \<psi>'" by metis
  }
  moreover {
    assume n: "test_symb (FNot \<phi>)"
    then have "\<not> all_subformula_st test_symb \<phi>"
      using all_subformula_st_decomp_explicit(3) nst subf by blast
    then have "\<exists>\<psi> \<psi>'. \<psi> \<preceq> FNot \<phi> \<and> r \<psi> \<psi>'"
      using H subformula_in_subformula_not subformula_refl subformula_trans by blast
  }
  ultimately show "\<exists>\<psi> \<psi>'. \<psi> \<preceq> FNot \<phi> \<and> r \<psi> \<psi>'" by blast
next
  case (binary \<phi> \<phi>1 \<phi>2)
  note IH\<phi>1_0 = this(1)[OF this(4)] and IH\<phi>2_0 = this(2)[OF this(4)] and r = this(4)
    and \<phi> = this(3) and le = this(5) and nst = this(6)

  obtain c :: "'v connective" where
    c: "(c = CAnd \<or> c = COr \<or> c = CImp \<or> c = CEq) \<and> conn c [\<phi>1, \<phi>2] = \<phi>"
    using \<phi> by fastforce

  then have corr: "wf_conn c [\<phi>1, \<phi>2]" using wf_conn.simps unfolding binary_connectives_def by auto
  have inc: "\<phi>1 \<preceq> \<phi>" "\<phi>2 \<preceq> \<phi>" using binary_connectives_def c subformula_in_binary_conn by blast+
  from r IH\<phi>1_0 have IH\<phi>1: "\<not> all_subformula_st test_symb \<phi>1 \<Longrightarrow> \<exists>\<psi> \<psi>'. \<psi> \<preceq> \<phi>1 \<and> r \<psi> \<psi>'"
    using inc(1) subformula_trans le by blast
  from r IH\<phi>2_0 have IH\<phi>2: "\<not> all_subformula_st test_symb \<phi>2 \<Longrightarrow> \<exists>\<psi>. \<psi> \<preceq> \<phi>2 \<and> (\<exists>\<psi>'. r \<psi> \<psi>')"
    using inc(2) subformula_trans le by blast
  have cases: "\<not>test_symb \<phi> \<or> \<not>all_subformula_st test_symb \<phi>1 \<or> \<not>all_subformula_st test_symb \<phi>2"
    using c nst by auto
  show "\<exists>\<psi> \<psi>'. \<psi> \<preceq> \<phi> \<and> r \<psi> \<psi>'"
    using IH\<phi>1 IH\<phi>2 subformula_trans inc subformula_refl cases le by blast
qed

subsection \<open>Invariant conservation\<close>
text \<open>If two rewrite relation are independant (or at least independant enough), then the property
  characterizing the first relation @{term "all_subformula_st test_symb"} remains true. The next
  show the same property, with changes in the assumptions.\<close>

text \<open>The assumption @{term "\<forall>\<phi>' \<psi>. \<phi>' \<preceq> \<Phi> \<longrightarrow> r \<phi>' \<psi> \<longrightarrow> all_subformula_st test_symb \<phi>'
  \<longrightarrow> all_subformula_st test_symb \<psi>"} means that rewriting with @{term r} does not mess up the
  property we want to preserve locally.\<close>

text \<open>The previous assumption is not enough to go from @{term r} to @{term "propo_rew_step r"}: we
  have to add the assumption that rewriting inside does not mess up the term:
  @{term "\<forall>(c:: 'v connective) \<xi> \<phi> \<xi>' \<phi>'. \<phi> \<preceq> \<Phi> \<longrightarrow> propo_rew_step r \<phi> \<phi>'
  \<longrightarrow> wf_conn c (\<xi> @ \<phi> # \<xi>') \<longrightarrow> test_symb (conn c (\<xi> @ \<phi> # \<xi>')) \<longrightarrow> test_symb \<phi>'
  \<longrightarrow> test_symb (conn c (\<xi> @ \<phi>' # \<xi>'))"}\<close>


subsubsection \<open>Invariant while lifting of the Rewriting Relation\<close>

text \<open>The condition @{term "\<phi> \<preceq> \<Phi>"} (that will by used with @{term "\<Phi> = \<phi>"} most of the time) is
  here to ensure that the recursive conditions on @{term "\<Phi>"} will moreover hold for the subterm
  we are rewriting. For example if there is no equivalence symbol in @{term "\<Phi>"}, we do not have to
  care about equivalence symbols in the two previous assumptions.\<close>

lemma propo_rew_step_inv_stay':
  fixes r:: "'v propo \<Rightarrow> 'v propo \<Rightarrow> bool" and test_symb:: "'v propo \<Rightarrow> bool" and x :: "'v"
  and \<phi> \<psi> \<Phi>:: "'v propo"
  assumes H: "\<forall>\<phi>' \<psi>. \<phi>' \<preceq> \<Phi> \<longrightarrow> r \<phi>' \<psi> \<longrightarrow> all_subformula_st test_symb \<phi>'
    \<longrightarrow> all_subformula_st test_symb \<psi>"
  and H': "\<forall>(c:: 'v connective) \<xi> \<phi> \<xi>' \<phi>'. \<phi> \<preceq> \<Phi> \<longrightarrow> propo_rew_step r \<phi> \<phi>'
    \<longrightarrow> wf_conn c (\<xi> @ \<phi> # \<xi>') \<longrightarrow> test_symb (conn c (\<xi> @ \<phi> # \<xi>')) \<longrightarrow> test_symb \<phi>'
    \<longrightarrow> test_symb (conn c (\<xi> @ \<phi>' # \<xi>'))" and
    "propo_rew_step r \<phi> \<psi>" and
    "\<phi> \<preceq> \<Phi>" and
    "all_subformula_st test_symb \<phi>"
  shows "all_subformula_st test_symb \<psi>"
  using assms(3-5)
proof (induct rule: propo_rew_step.induct)
  case global_rel
  then show ?case using H by simp
next
  case (propo_rew_one_step_lift \<phi> \<phi>' c \<xi> \<xi>')
  note rel = this(1) and \<phi> = this(2) and corr = this(3) and \<Phi> = this(4) and nst = this(5)
  have sq: "\<phi> \<preceq> \<Phi>"
    using \<Phi> corr subformula_into_subformula subformula_refl subformula_trans
    by (metis in_set_conv_decomp)
  from corr have "\<forall> \<psi>. \<psi> \<in> set (\<xi> @ \<phi> # \<xi>') \<longrightarrow> all_subformula_st test_symb \<psi>"
    using all_subformula_st_decomp nst by blast
  then have *: "\<forall>\<psi>. \<psi> \<in> set (\<xi> @ \<phi>' # \<xi>') \<longrightarrow> all_subformula_st test_symb \<psi>" using \<phi> sq by fastforce
  then have "test_symb \<phi>'" using all_subformula_st_test_symb_true_phi by auto
  moreover from corr nst have "test_symb (conn c (\<xi> @ \<phi> # \<xi>'))"
    using all_subformula_st_decomp by blast
  ultimately have test_symb: "test_symb (conn c (\<xi> @ \<phi>' # \<xi>'))" using H' sq corr rel by blast

  have "wf_conn c (\<xi> @ \<phi>' # \<xi>')"
    by (metis wf_conn_no_arity_change_helper corr wf_conn_no_arity_change)
  then show "all_subformula_st test_symb (conn c (\<xi> @ \<phi>' # \<xi>'))"
    using * test_symb by (metis all_subformula_st_decomp)
qed


text \<open>The need for @{term "\<phi> \<preceq> \<Phi>"} is not always necessary, hence we moreover have a version
  without inclusion. \<close>
lemma propo_rew_step_inv_stay:
  fixes r:: "'v propo \<Rightarrow> 'v propo \<Rightarrow> bool" and test_symb:: "'v propo \<Rightarrow> bool" and x :: "'v"
  and \<phi> \<psi> :: "'v propo"
  assumes
    H: "\<forall>\<phi>' \<psi>. r \<phi>' \<psi> \<longrightarrow> all_subformula_st test_symb \<phi>' \<longrightarrow> all_subformula_st test_symb \<psi>" and
    H': "\<forall>(c:: 'v connective) \<xi> \<phi> \<xi>' \<phi>'. wf_conn c (\<xi> @ \<phi> # \<xi>') \<longrightarrow> test_symb (conn c (\<xi> @ \<phi> # \<xi>'))
      \<longrightarrow> test_symb \<phi>' \<longrightarrow> test_symb (conn c (\<xi> @ \<phi>' # \<xi>'))" and
    "propo_rew_step r \<phi> \<psi>" and
    "all_subformula_st test_symb \<phi>"
  shows "all_subformula_st test_symb \<psi>"
  using propo_rew_step_inv_stay'[of \<phi> r test_symb \<phi> \<psi>] assms subformula_refl by metis


text \<open>The lemmas can be lifted to @{term "full (propo_rew_step r)"} instead of
  @{term propo_rew_step}\<close>

subsubsection \<open>Invariant after all Rewriting\<close>

lemma full_propo_rew_step_inv_stay_with_inc:
  fixes r:: "'v propo \<Rightarrow> 'v propo \<Rightarrow> bool" and test_symb:: "'v propo \<Rightarrow> bool" and x :: "'v"
  and \<phi> \<psi> :: "'v propo"
  assumes
    H: "\<forall> \<phi> \<psi>. propo_rew_step r \<phi> \<psi> \<longrightarrow> all_subformula_st test_symb \<phi>
      \<longrightarrow> all_subformula_st test_symb \<psi>" and
    H': "\<forall>(c:: 'v connective) \<xi> \<phi> \<xi>' \<phi>'. \<phi> \<preceq> \<Phi> \<longrightarrow> propo_rew_step r \<phi> \<phi>'
      \<longrightarrow> wf_conn c (\<xi> @ \<phi> # \<xi>') \<longrightarrow> test_symb (conn c (\<xi> @ \<phi> # \<xi>')) \<longrightarrow> test_symb \<phi>'
      \<longrightarrow> test_symb (conn c (\<xi> @ \<phi>' # \<xi>'))" and
      "\<phi> \<preceq> \<Phi>" and
    full: "full (propo_rew_step r) \<phi> \<psi>" and
    init: "all_subformula_st test_symb \<phi>"
  shows "all_subformula_st test_symb \<psi>"
  using assms unfolding full_def
proof -
  have rel: "(propo_rew_step r)\<^sup>*\<^sup>* \<phi> \<psi>"
    using full unfolding full_def by auto
  then show "all_subformula_st test_symb \<psi> "
    using init
    proof (induct rule: rtranclp_induct)
      case base
      then show "all_subformula_st test_symb \<phi>" by blast
    next
      case (step b c) note star = this(1) and IH = this(3) and one = this(2) and all = this(4)
      then have "all_subformula_st test_symb b" by metis
      then show "all_subformula_st test_symb c" using propo_rew_step_inv_stay' H H' rel one by auto
    qed
qed

lemma full_propo_rew_step_inv_stay':
  fixes r:: "'v propo \<Rightarrow> 'v propo \<Rightarrow> bool" and test_symb:: "'v propo \<Rightarrow> bool" and x :: "'v"
  and \<phi> \<psi> :: "'v propo"
  assumes
    H: "\<forall> \<phi> \<psi>. propo_rew_step r \<phi> \<psi> \<longrightarrow> all_subformula_st test_symb \<phi>
      \<longrightarrow> all_subformula_st test_symb \<psi>" and
    H': "\<forall>(c:: 'v connective) \<xi> \<phi> \<xi>' \<phi>'. propo_rew_step r \<phi> \<phi>' \<longrightarrow> wf_conn c (\<xi> @ \<phi> # \<xi>')
      \<longrightarrow> test_symb (conn c (\<xi> @ \<phi> # \<xi>')) \<longrightarrow> test_symb \<phi>' \<longrightarrow> test_symb (conn c (\<xi> @ \<phi>' # \<xi>'))" and
    full: "full (propo_rew_step r) \<phi> \<psi>" and
    init: "all_subformula_st test_symb \<phi>"
  shows "all_subformula_st test_symb \<psi>"
  using full_propo_rew_step_inv_stay_with_inc[of r test_symb \<phi>] assms subformula_refl by metis

lemma full_propo_rew_step_inv_stay:
  fixes r:: "'v propo \<Rightarrow> 'v propo \<Rightarrow> bool" and test_symb:: "'v propo \<Rightarrow> bool" and x :: "'v"
  and \<phi> \<psi> :: "'v propo"
  assumes
    H: "\<forall>\<phi> \<psi>. r \<phi> \<psi> \<longrightarrow> all_subformula_st test_symb \<phi> \<longrightarrow> all_subformula_st test_symb \<psi>" and
    H': "\<forall>(c:: 'v connective) \<xi> \<phi> \<xi>' \<phi>'. wf_conn c (\<xi> @ \<phi> # \<xi>') \<longrightarrow> test_symb (conn c (\<xi> @ \<phi> # \<xi>'))
      \<longrightarrow> test_symb \<phi>' \<longrightarrow> test_symb (conn c (\<xi> @ \<phi>' # \<xi>'))" and
    full: "full (propo_rew_step r) \<phi> \<psi>" and
    init: "all_subformula_st test_symb \<phi>"
  shows "all_subformula_st test_symb \<psi>"
  unfolding full_def
proof -
  have rel: "(propo_rew_step r)^** \<phi> \<psi>"
    using full unfolding full_def by auto
  then show "all_subformula_st test_symb \<psi>"
    using init
    proof (induct rule: rtranclp_induct)
      case base
      then show "all_subformula_st test_symb \<phi>" by blast
    next
      case (step b c)
      note star = this(1) and IH = this(3) and one = this(2) and all = this(4)
      then have "all_subformula_st test_symb b" by metis
      then show "all_subformula_st test_symb c"
        using propo_rew_step_inv_stay subformula_refl H H' rel one by auto
    qed
qed


lemma full_propo_rew_step_inv_stay_conn:
  fixes r:: "'v propo \<Rightarrow> 'v propo \<Rightarrow> bool" and test_symb:: "'v propo \<Rightarrow> bool" and x :: "'v"
  and \<phi> \<psi> :: "'v propo"
  assumes
    H: "\<forall>\<phi> \<psi>. r \<phi> \<psi> \<longrightarrow> all_subformula_st test_symb \<phi> \<longrightarrow> all_subformula_st test_symb \<psi>" and
    H': "\<forall>(c:: 'v connective) l l'. wf_conn c l \<longrightarrow> wf_conn c l'
      \<longrightarrow> (test_symb (conn c l) \<longleftrightarrow> test_symb (conn c l'))" and
    full: "full (propo_rew_step r) \<phi> \<psi>" and
    init: "all_subformula_st test_symb \<phi>"
  shows "all_subformula_st test_symb \<psi>"
proof -
  have "\<And>(c:: 'v connective) \<xi> \<phi> \<xi>' \<phi>'. wf_conn c (\<xi> @ \<phi> # \<xi>')
    \<Longrightarrow> test_symb (conn c (\<xi> @ \<phi> # \<xi>')) \<Longrightarrow> test_symb \<phi>' \<Longrightarrow> test_symb (conn c (\<xi> @ \<phi>' # \<xi>'))"
    using H'  by (metis wf_conn_no_arity_change_helper wf_conn_no_arity_change)
  then show "all_subformula_st test_symb \<psi>"
    using H full init full_propo_rew_step_inv_stay by blast
qed

end
