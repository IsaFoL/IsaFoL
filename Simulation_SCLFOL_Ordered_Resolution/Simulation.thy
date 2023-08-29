theory Simulation
  imports
    Simple_Clause_Learning.SCL_FOL
    Simple_Clause_Learning.Initial_Literals_Generalize_Learned_Literals
    Superposition_Calculus.Ground_Ordered_Resolution
begin

section \<open>Move to HOL\<close>

syntax
  "_FFilter" :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> 'a fset" ("(1{|_ |\<in>| _./ _|})")
translations
  "{|x |\<in>| X. P|}" == "CONST ffilter (\<lambda>x. P) X"

lemma rtranclp_rtranclp_compose_if_right_unique:
  assumes runique: "right_unique R" and "R\<^sup>*\<^sup>* a b" and "R\<^sup>*\<^sup>* a c"
  shows "R\<^sup>*\<^sup>* a b \<and> R\<^sup>*\<^sup>* b c \<or> R\<^sup>*\<^sup>* a c \<and> R\<^sup>*\<^sup>* c b"
  using assms(2,3)
proof (induction b arbitrary: c rule: rtranclp_induct)
  case base
  thus ?case
    by simp
next
  case (step a' b)
  with runique show ?case
    by (metis converse_rtranclpE right_uniqueD rtranclp.rtrancl_into_rtrancl)
qed

lemma right_unique_terminating_rtranclp:
  assumes "right_unique R"
  shows "right_unique (\<lambda>x y. R\<^sup>*\<^sup>* x y \<and> (\<nexists>z. R y z))"
  unfolding right_unique_def
  using rtranclp_rtranclp_compose_if_right_unique[OF \<open>right_unique R\<close>]
  by (metis converse_rtranclpE)

lemma ex_terminating_rtranclp:
  assumes wf: "wfP R\<inverse>\<inverse>"
  shows "\<exists>y. R\<^sup>*\<^sup>* x y \<and> (\<nexists>z. R y z)"
proof (cases "\<exists>y. R x y")
  case True
  with wf show ?thesis
    by (induction rule: wfP_induct_rule)
      (metis converse_rtranclp_into_rtranclp conversep_iff r_into_rtranclp)
next
  case False
  thus ?thesis 
    by blast
qed

lemma ex1_subset_eq_image_if_bij_betw:
  fixes f :: "'a \<Rightarrow> 'b" and X :: "'a set" and Y :: "'b set"
  assumes "bij_betw f X Y" and "Y' \<subseteq> Y"
  shows "\<exists>!X'. X' \<subseteq> X \<and> Y' = f ` X'"
  using assms
  by (metis bij_betw_def inv_into_image_cancel subset_image_iff)

lemma Collect_eq_image_filter_Collect_if_bij_betw:
  fixes f :: "'a \<Rightarrow> 'b" and X :: "'a set" and Y :: "'b set"
  assumes bij: "bij_betw f X Y" and sub: "{y. P y} \<subseteq> Y"
  shows "{y. P y} = f ` {x. x \<in> X \<and> P (f x)}"
  using ex1_subset_eq_image_if_bij_betw[OF bij sub]
  by (smt (verit, best) Collect_cong image_def in_mono mem_Collect_eq)

definition is_maximal_in_set_wrt where
  "is_maximal_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. \<not> (R x y))"

definition is_greatest_in_set_wrt where
  "is_greatest_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X - {x}. R y x)"

lemma Uniq_is_maximal_set_wrt:
  "totalp_on X R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. is_maximal_in_set_wrt R X x"
  by (rule Uniq_I) (metis insert_Diff insert_iff is_maximal_in_set_wrt_def totalp_onD)

lemma "finite A \<Longrightarrow> asymp_on A R \<Longrightarrow> transp_on A R \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>m. is_maximal_in_set_wrt R A m"
  using Finite_Set.bex_max_element[of A R]
  by (metis DiffE insert_iff is_maximal_in_set_wrt_def)

lemma is_maximal_in_set_wrt_iff_is_greatest_in_set_wrt:
  assumes asym: "asymp_on X R" and tot: "totalp_on X R"
  shows "is_maximal_in_set_wrt R X x \<longleftrightarrow> is_greatest_in_set_wrt R X x"
proof (rule iffI)
  from tot show "is_maximal_in_set_wrt R X x \<Longrightarrow> is_greatest_in_set_wrt R X x"
    unfolding is_maximal_in_set_wrt_def is_greatest_in_set_wrt_def
    by (metis Diff_iff insertCI totalp_onD)
next
  from asym show "is_greatest_in_set_wrt R X x \<Longrightarrow> is_maximal_in_set_wrt R X x"
    unfolding is_maximal_in_set_wrt_def is_greatest_in_set_wrt_def
    by (metis Diff_iff asymp_onD)
qed

lemma is_greatest_in_set_wrt_iff:
  "is_greatest_in_set_wrt R X x \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<noteq> x \<longrightarrow> R y x)"
  unfolding is_greatest_in_set_wrt_def
  by blast


section \<open>Move to HOL-Library\<close>

syntax
  "_FFilter" :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> 'a fset" ("(1{|_ |\<in>| _./ _|})")

translations
  "{|x |\<in>| X. P|}" == "CONST ffilter (\<lambda>x. P) X"


section \<open>Move to Superposition_Calculus\<close>

lemma (in ground_ordered_resolution_calculus) unique_ground_resolution:
  shows "\<exists>\<^sub>\<le>\<^sub>1C. ground_resolution P1 P2 C"
proof (intro Uniq_I)
  fix C C'
  assume "ground_resolution P1 P2 C" and "ground_resolution P1 P2 C'"
  thus "C = C'"
    unfolding ground_resolution.simps
    apply (elim exE conjE)
    apply simp
    using Uniq_is_maximal_wrt[OF totalp_on_less_lit]
    using Uniq_is_maximal_wrt_reflclp[OF totalp_on_less_lit]
    by (metis Uniq_D add_mset_add_mset_same_iff literal.inject(1))
qed

lemma (in ground_ordered_resolution_calculus) unique_ground_factoring:
  shows "\<exists>\<^sub>\<le>\<^sub>1C. ground_factoring P C"
proof (intro Uniq_I)
  fix P C C'
  assume "ground_factoring P C" and "ground_factoring P C'"
  thus "C = C'"
    unfolding ground_factoring.simps
    apply (elim exE conjE)
    apply simp
    using Uniq_is_maximal_wrt[OF totalp_on_less_lit]
    by (metis Uniq_D add_mset_add_mset_same_iff)
qed

lemma (in ground_ordered_resolution_calculus) termination_ground_factoring:
  "wfP ground_factoring\<inverse>\<inverse>"
proof (rule wfP_if_convertible_to_wfP)
  show "\<And>x y. ground_factoring\<inverse>\<inverse> x y \<Longrightarrow> x \<prec>\<^sub>c y"
    using ground_factoring_smaller_conclusion by simp
next
  show "wfP (\<prec>\<^sub>c)"
    by simp
qed


section \<open>Move somewhere?\<close>

definition Max_mset_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a option" where
  "Max_mset_wrt R M = (if M = {#} then None else Some (THE x. is_maximal_wrt R x M))"

lemma Max_mset_wrt_eq_None[simp]: "Max_mset_wrt R M = None \<longleftrightarrow> M = {#}"
  by (simp add: Max_mset_wrt_def)

lemma Max_mset_wrt_eq_Some_if_is_maximal_wrt:
  assumes tot: "totalp_on (set_mset M) R"
  shows "is_maximal_wrt R x M \<Longrightarrow> Max_mset_wrt R M = Some x"
  using the1_equality'[OF Uniq_is_maximal_wrt[OF tot]]
  by (metis Max_mset_wrt_def empty_iff is_maximal_wrt_def set_mset_empty)

lemma is_maximal_wrt_if_Max_mset_wrt_eq_Some:
  assumes
    trans: "transp_on (set_mset M) R" and
    asym: "asymp_on (set_mset M) R" and
    tot: "totalp_on (set_mset M) R" and
    max: "Max_mset_wrt R M = Some x"
  shows "is_maximal_wrt R x M"
proof -
  from max have "M \<noteq> {#}" and "(THE x. is_maximal_wrt R x M) = x"
    unfolding atomize_conj Max_mset_wrt_def
    by (metis option.discI option.inject)

  obtain y where "is_maximal_wrt R y M"
    using ex_is_maximal_wrt_if_not_empty[OF trans asym \<open>M \<noteq> {#}\<close>] by metis

  moreover have "\<exists>\<^sub>\<le>\<^sub>1L. is_maximal_wrt R L M"
    using Uniq_is_maximal_wrt[OF tot] by assumption

  ultimately have "\<exists>!L. is_maximal_wrt R L M"
    by (intro Uniq_implies_ex1)
  hence "is_maximal_wrt R (THE x. is_maximal_wrt R x M) M"
    by (rule theI')
  thus ?thesis
    unfolding \<open>(THE x. is_maximal_wrt R x M) = x\<close>
    by assumption
qed

lemma Max_mset_wrt_eq_Some[simp]:
  assumes
    trans: "transp_on (set_mset M) R" and
    asym: "asymp_on (set_mset M) R" and
    tot: "totalp_on (set_mset M) R"
  shows "Max_mset_wrt R M = Some x \<longleftrightarrow> is_maximal_wrt R x M"
  using assms Max_mset_wrt_eq_Some_if_is_maximal_wrt is_maximal_wrt_if_Max_mset_wrt_eq_Some
  by metis


lemma ground_iff_vars_term_empty: "ground t \<longleftrightarrow> vars_term t = {}"
proof (rule iffI)
  show "ground t \<Longrightarrow> vars_term t = {}"
    by (rule ground_vars_term_empty)
next
  show "vars_term t = {} \<Longrightarrow> ground t"
    by (induction t) simp_all
qed

lemma is_ground_atm_eq_ground[iff]: "is_ground_atm = ground"
proof (rule ext)
  fix t :: "('v, 'f) Term.term"
  show "is_ground_atm t = ground t"
    by (simp only: is_ground_atm_iff_vars_empty ground_iff_vars_term_empty)
qed

definition lit_of_glit where
  "lit_of_glit = map_literal term_of_gterm"

definition glit_of_lit where
  "glit_of_lit = map_literal gterm_of_term"

definition cls_of_gcls where
  "cls_of_gcls = image_mset lit_of_glit"

definition gcls_of_cls where
  "gcls_of_cls = image_mset glit_of_lit"

lemma atm_of_lit_of_glit_conv: "atm_of (lit_of_glit L) = term_of_gterm (atm_of L)"
  by (cases L) (simp_all add: lit_of_glit_def)

definition atms_of_clss where
  "atms_of_clss N = (\<Union>C \<in> N. atms_of C)"

definition lit_occures_in_clss where
  "lit_occures_in_clss L N \<longleftrightarrow> fBex N (\<lambda>C. L \<in># C)"


section \<open>Simulation\<close>

type_synonym ('f, 'v) scl_fol_sim_state =
  "('f, 'v) SCL_FOL.state \<times> nat \<times> 'f gterm clause \<times> ('f gterm clause \<Rightarrow> 'f gterm clause)"

locale simulation_SCLFOL_ground_ordered_resolution =
  renaming_apart renaming_vars
  for renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v" +
  fixes
    less_trm :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50)
  assumes
    transp_less_trm[simp]: "transp (\<prec>\<^sub>t)" and
    asymp_less_trm[intro]: "asymp (\<prec>\<^sub>t)" and
    wfP_less_trm[intro]: "wfP (\<prec>\<^sub>t)" and
    totalp_less_trm[intro]: "totalp (\<prec>\<^sub>t)" and
    finite_less_trm: "\<And>\<beta>. finite {x. x \<prec>\<^sub>t \<beta>}" and
    less_trm_compatible_with_gctxt[simp]: "\<And>ctxt t t'. t \<prec>\<^sub>t t' \<Longrightarrow> ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t'\<rangle>\<^sub>G" and
    less_trm_if_subterm[simp]: "\<And>t ctxt. ctxt \<noteq> \<box>\<^sub>G \<Longrightarrow> t \<prec>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
begin

subsection \<open>Ground ordered resolution for ground terms\<close>

interpretation ord_res: ground_ordered_resolution_calculus "(\<prec>\<^sub>t)" "\<lambda>_. {#}"
  by unfold_locales auto

interpretation linorder_trm: linorder "(\<preceq>\<^sub>t)" "(\<prec>\<^sub>t)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>t y) = (x \<preceq>\<^sub>t y \<and> \<not> y \<preceq>\<^sub>t x)"
    by (metis asympD asymp_less_trm reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>t x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>t y \<Longrightarrow> y \<preceq>\<^sub>t z \<Longrightarrow> x \<preceq>\<^sub>t z"
    by (meson transpE transp_less_trm transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>t y \<Longrightarrow> y \<preceq>\<^sub>t x \<Longrightarrow> x = y"
    by (metis asympD asymp_less_trm reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>t y \<or> y \<preceq>\<^sub>t x"
    by (metis reflclp_iff totalpD totalp_less_trm)
qed

interpretation linorder_lit: linorder "(\<preceq>\<^sub>l)" "(\<prec>\<^sub>l)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>l y) = (x \<preceq>\<^sub>l y \<and> \<not> y \<preceq>\<^sub>l x)"
    by (metis asympD ord_res.asymp_less_lit reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>l x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>l y \<Longrightarrow> y \<preceq>\<^sub>l z \<Longrightarrow> x \<preceq>\<^sub>l z"
    by (meson transpE ord_res.transp_less_lit transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>l y \<Longrightarrow> y \<preceq>\<^sub>l x \<Longrightarrow> x = y"
    by (metis asympD ord_res.asymp_less_lit reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>l y \<or> y \<preceq>\<^sub>l x"
    by (metis reflclp_iff totalpD ord_res.totalp_less_lit)
qed

interpretation linorder_cls: linorder "(\<preceq>\<^sub>c)" "(\<prec>\<^sub>c)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>c y) = (x \<preceq>\<^sub>c y \<and> \<not> y \<preceq>\<^sub>c x)"
    by (metis asympD ord_res.asymp_less_cls reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>c x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>c y \<Longrightarrow> y \<preceq>\<^sub>c z \<Longrightarrow> x \<preceq>\<^sub>c z"
    by (meson transpE ord_res.transp_less_cls transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>c y \<Longrightarrow> y \<preceq>\<^sub>c x \<Longrightarrow> x = y"
    by (metis asympD ord_res.asymp_less_cls reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>c y \<or> y \<preceq>\<^sub>c x"
    by (metis reflclp_iff totalpD ord_res.totalp_less_cls)
qed

subsection \<open>Lemmas about going between ground and first-order terms\<close>

lemma ex1_gterm_of_term:
  fixes t :: "'f gterm"
  shows "\<exists>!(t' :: ('f, 'v) term). ground t' \<and> t = gterm_of_term t'"
proof (rule ex1I)
  show "ground (term_of_gterm t) \<and> t = gterm_of_term (term_of_gterm t)"
    by simp
next
  fix t' :: "('f, 'v) term"
  show "ground t' \<and> t = gterm_of_term t' \<Longrightarrow> t' = term_of_gterm t"
    by (induction t') (simp_all add: map_idI)
qed

lemma binj_betw_gterm_of_term: "bij_betw gterm_of_term {t. ground t} UNIV"
  unfolding bij_betw_def
proof (rule conjI)
  show "inj_on gterm_of_term {t. ground t}"
    by (metis gterm_of_term_inj mem_Collect_eq)
next
  show "gterm_of_term ` {t. ground t} = UNIV"
  proof (rule Set.subset_antisym)
    show "gterm_of_term ` {t. Term_Context.ground t} \<subseteq> UNIV"
      by simp
  next
    show "UNIV \<subseteq> gterm_of_term ` {t. Term_Context.ground t}"
      by (metis (mono_tags, opaque_lifting) ground_term_of_gterm image_iff mem_Collect_eq subsetI
          term_of_gterm_inv)
  qed
qed


subsection \<open>SCL(FOL) for first-order terms\<close>

interpretation scl_fol: scl_fol_calculus renaming_vars
  "\<lambda>x y. ground x \<and> ground y \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term y"
proof unfold_locales
  fix \<beta> :: "('f, 'v) term"

  have Collect_gterms_eq: "\<And>P. {y. P y} = gterm_of_term ` {t. ground t \<and> P (gterm_of_term t)}"
    using Collect_eq_image_filter_Collect_if_bij_betw[OF binj_betw_gterm_of_term subset_UNIV]
    by auto

  have "{t\<^sub>G. t\<^sub>G \<prec>\<^sub>t gterm_of_term \<beta>} = gterm_of_term ` {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    using Collect_gterms_eq[of "\<lambda>t\<^sub>G. t\<^sub>G \<prec>\<^sub>t gterm_of_term \<beta>"] .
  hence "finite (gterm_of_term ` {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>})"
    using finite_less_trm[of "gterm_of_term \<beta>"] by metis
  moreover have "inj_on gterm_of_term {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    by (rule gterm_of_term_inj) simp
  ultimately have "finite {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    using finite_imageD by blast
  thus "finite {x. ground x \<and> ground \<beta> \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    using not_finite_existsD by force
qed


subsection \<open>Strategy for ground ordered resolution\<close>

lemma true_cls_if_true_lit_in: "L \<in># C \<Longrightarrow> I \<TTurnstile>l L \<Longrightarrow> I \<TTurnstile> C"
  by auto

definition is_minimal_wrt where
  "is_minimal_wrt R x X \<longleftrightarrow> x |\<in>| X \<and> fBall X (\<lambda>y. y \<noteq> x \<longrightarrow> \<not> (R y x))"

lemma obtains_minimal_wrt_fset:
  assumes "asymp_on (fset X) R" and "transp_on (fset X) R" and "X \<noteq> {||}"
  obtains x where "is_minimal_wrt R x X"
  using Finite_Set.bex_min_element[OF finite_fset assms(1,2)]
  unfolding is_minimal_wrt_def
  using assms(3) by auto

definition is_min_false_clause :: "'f gterm clause fset \<Rightarrow> 'f gterm clause \<Rightarrow> bool" where
  "is_min_false_clause N C \<longleftrightarrow>
    is_minimal_wrt (\<prec>\<^sub>c) C
      {|C |\<in>| N. \<not> (\<Union>D \<in> {D \<in> fset N. D \<preceq>\<^sub>c C}. ord_res.production (fset N) D) \<TTurnstile> C|}"

definition ord_res_mod_op_strategy :: "'f gterm clause fset \<Rightarrow> 'f gterm clause fset \<Rightarrow> bool" where
  "ord_res_mod_op_strategy N N' \<longleftrightarrow> (\<exists>C L.
    is_min_false_clause N C \<and> ord_res.is_maximal_lit L C \<and>
      (case L of
        Neg A \<Rightarrow> \<comment> \<open>Case 3\<close>
        fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (Pos A) D \<and>
          (\<exists>CD. ord_res.ground_resolution C D CD \<and> N' = finsert CD N))
      | Pos A \<Rightarrow> \<comment> \<open>Case 4\<close>
        \<not> ord_res.is_strictly_maximal_lit (Pos A) C \<and>
          (\<exists>C'. ord_res.ground_factoring C C')))"

lemma
  assumes
    C_min_false: "is_min_false_clause N C" and
    Neg_A_max: "ord_res.is_maximal_lit (Neg A) C"
  shows "fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (Pos A) D)"
proof -
  from C_min_false have
    C_in: "C |\<in>| N" and
    C_false: "\<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C}) \<TTurnstile> C" and
    C_min: "fBall {|C |\<in>| N. \<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C}) \<TTurnstile> C|}
      (\<lambda>y. C \<noteq> y \<longrightarrow> C \<prec>\<^sub>c y)"
    unfolding atomize_conj is_min_false_clause_def
    by (metis (mono_tags, lifting) ffmember_filter is_minimal_wrt_def linorder_cls.not_less
        reflclp_iff)

  from C_false have "\<nexists>A. A \<in> ord_res.production (fset N) C"
    apply (intro notI)
    apply (elim exE)
    by (metis (no_types, lifting) SUP_absorb UnI1 is_maximal_wrt_def linorder_cls.order_eq_iff
        mem_Collect_eq ord_res.mem_productionE pos_literal_in_imp_true_cls)
  hence C_unproductive: "ord_res.production (fset N) C = {}"
    using ord_res.production_eq_empty_or_singleton[of "fset N" C] by simp

  from Neg_A_max have "Neg A \<in># C"
    by (simp add: is_maximal_wrt_def)

  from C_false have "\<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C}) \<TTurnstile>l Neg A"
    using true_cls_if_true_lit_in[OF \<open>Neg A \<in># C\<close>]
    by meson
  hence "A \<in> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C})"
    by simp
  with C_unproductive have "A \<in> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<prec>\<^sub>c C})"
    by blast
  then obtain D where
    D_in: "D |\<in>| N" and D_lt_C: "D \<prec>\<^sub>c C" and D_productive: "A \<in> ord_res.production (fset N) D"
    by auto

  from D_productive have "ord_res.is_strictly_maximal_lit (Pos A) D"
    using ord_res.mem_productionE by metis
  thus ?thesis
    using D_in D_lt_C by metis
qed

lemma
  assumes
    C_max_lit: "ord_res.is_maximal_lit (Neg A) C" and
    D_in: "D |\<in>| N" and
    D_lt: "D \<prec>\<^sub>c C" and
    D_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) D"
  shows "\<exists>CD. ord_res.ground_resolution C D CD"
proof -
  from C_max_lit obtain C' where C_def: "C = add_mset (Neg A) C'"
    by (meson is_maximal_wrt_def mset_add)

  from D_max_lit obtain D' where D_def: "D = add_mset (Pos A) D'"
    by (meson is_maximal_wrt_def mset_add)

  show ?thesis
  proof (rule exI)
    show "ord_res.ground_resolution C D (C' + D')"
      using ord_res.ground_resolutionI[of C A C' D D']
      using C_def D_def D_lt C_max_lit D_max_lit by metis
  qed
qed

lemma
  assumes
    C_min_false: "is_min_false_clause N C" and
    C_max_lit: "ord_res.is_maximal_lit (Pos A) C"
  shows "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
proof -
  from C_max_lit obtain C' where C_def: "C = add_mset (Pos A) C'"
    by (meson is_maximal_wrt_def mset_add)

  from C_min_false have
    C_in: "C |\<in>| N" and
    C_false: "\<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C}) \<TTurnstile> C" and
    C_min: "fBall {|C |\<in>| N. \<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<preceq>\<^sub>c C}) \<TTurnstile> C|}
      (\<lambda>y. C \<noteq> y \<longrightarrow> C \<prec>\<^sub>c y)"
    unfolding atomize_conj is_min_false_clause_def
    by (metis (mono_tags, lifting) ffmember_filter is_minimal_wrt_def linorder_cls.not_less
        reflclp_iff)

  from C_false have "\<nexists>A. A \<in> ord_res.production (fset N) C"
    apply (intro notI)
    apply (elim exE)
    by (metis (no_types, lifting) SUP_absorb UnI1 is_maximal_wrt_def linorder_cls.order_eq_iff
        mem_Collect_eq ord_res.mem_productionE pos_literal_in_imp_true_cls)
  hence C_unproductive: "ord_res.production (fset N) C = {}"
    using ord_res.production_eq_empty_or_singleton[of "fset N" C] by simp

  have "{D \<in> fset N. D \<preceq>\<^sub>c C} = {D \<in> fset N. D \<prec>\<^sub>c C} \<union> {D \<in> fset N. D = C}"
    by fastforce
  with C_unproductive have
    "\<Union> (ord_res.production (fset N) ` {D \<in> fset N. D \<preceq>\<^sub>c C}) =
     \<Union> (ord_res.production (fset N) ` {D \<in> fset N. D \<prec>\<^sub>c C})"
    by simp
  with C_false have C_false': "\<not> \<Union> (ord_res.production (fset N) ` {D. D |\<in>| N \<and> D \<prec>\<^sub>c C}) \<TTurnstile> C"
    by simp

  from C_unproductive have "A \<notin> ord_res.production (fset N) C"
    by simp
  thus ?thesis
  proof (rule contrapos_nn)
    assume "ord_res.is_strictly_maximal_lit (Pos A) C"
    then show "A \<in> ord_res.production (fset N) C"
      unfolding ord_res.production.simps[of "fset N" C] mem_Collect_eq
      using C_in C_def C_false' by metis
  qed
qed

lemma
  assumes
    C_max_lit: "ord_res.is_maximal_lit (Pos A) C" and
    C_not_max_lit: "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
  shows "\<exists>C'. ord_res.ground_factoring C C'"
proof -
  from C_max_lit C_not_max_lit have "count C (Pos A) > 1"
    by (simp add: in_diff_count is_maximal_wrt_def)
  then obtain C' where C_def: "C = add_mset (Pos A) (add_mset (Pos A) C')"
    by (metis C_max_lit C_not_max_lit count_greater_zero_iff dual_order.strict_trans insert_DiffM
        less_numeral_extra(1) lift_is_maximal_wrt_to_is_maximal_wrt_reflclp)
  
  show ?thesis
  proof (rule exI)
    show "ord_res.ground_factoring C (add_mset (Pos A) C')"
      using ord_res.ground_factoringI[of C A C']
      using C_def C_max_lit by metis
  qed
qed

definition sfac :: "'f gterm clause \<Rightarrow> 'f gterm clause" where
  "sfac C = (THE C'. ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"

lemma
  shows "sfac C = C \<or> (\<exists>!C'. sfac C = C' \<and> ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C''))"
proof -
  have "right_unique (\<lambda>x y. ord_res.ground_factoring\<^sup>*\<^sup>* x y \<and> (\<nexists>z. ord_res.ground_factoring y z))"
    using ord_res.unique_ground_factoring right_unique_terminating_rtranclp right_unique_iff
    by blast

  moreover obtain C' where "ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')"
    using ex_terminating_rtranclp[OF ord_res.termination_ground_factoring]
    by metis

  ultimately have "sfac C = C'"
    by (simp add: sfac_def right_unique_def the_equality)

  then show ?thesis
    using \<open>ord_res.ground_factoring\<^sup>*\<^sup>* C C' \<and> (\<nexists>C''. ord_res.ground_factoring C' C'')\<close> by blast
qed

inductive scl_reso1_step1 :: "_ \<Rightarrow> ('f, 'v) scl_fol_sim_state \<Rightarrow> ('f, 'v) scl_fol_sim_state \<Rightarrow> bool" for N\<^sub>0 where
  scl_reso1_step1I: "\<F> C \<prec>\<^sub>c \<F> D \<Longrightarrow> \<not> fBex (N\<^sub>0 |\<union>| fimage gcls_of_cls U) (\<lambda>D'. \<F> C \<prec>\<^sub>c \<F> D' \<and> \<F> D' \<prec>\<^sub>c \<F> D) \<Longrightarrow>
  ord_res.is_maximal_lit L D \<Longrightarrow>
  sorted_wrt (\<prec>\<^sub>l) Ks \<Longrightarrow> (\<forall>K \<in> set Ks. is_neg K \<and> K \<prec>\<^sub>l L \<and>
    \<not> trail_defined_lit \<Gamma> (lit_of_glit K) \<and>
    lit_occures_in_clss K N\<^sub>0) \<Longrightarrow>
  \<Gamma>' = foldl trail_decide \<Gamma> (map lit_of_glit Ks) \<Longrightarrow>
  scl_reso1_step1 N\<^sub>0 ((\<Gamma>, U, None), i, C, \<F>) ((\<Gamma>', U, None), i, D, \<F>)"

lemma correctness_scl_reso1_step1:
  fixes N\<^sub>0 :: "'f gterm clause fset"
  assumes
    \<beta>\<^sub>G_greatest: "is_greatest_in_set_wrt (\<prec>\<^sub>t) (atms_of_clss (fset N\<^sub>0)) \<beta>\<^sub>G" and
    step: "scl_reso1_step1 N\<^sub>0 (S, i, C, \<F>) (S', i', C', \<F>')"
  defines "\<beta> \<equiv> term_of_gterm \<beta>\<^sub>G"
  shows "(scl_fol.decide (fimage cls_of_gcls N\<^sub>0) \<beta>)\<^sup>*\<^sup>* S S'"
  using step
proof (cases N\<^sub>0 "(S, i, C, \<F>)" "(S', i', C', \<F>')" rule: scl_reso1_step1.cases)
  case hyps: (scl_reso1_step1I U L Ks \<Gamma> \<Gamma>')
  then show ?thesis
  proof (induction Ks arbitrary: S \<Gamma>)
    case Nil
    hence "S' = S"
      by simp
    thus ?case
      by simp
  next
    case (Cons K Ks)
    note ball_K_Ks = \<open>\<forall>K\<in>set (K # Ks). is_neg K \<and> K \<prec>\<^sub>l L \<and>
        \<not> trail_defined_lit \<Gamma> (lit_of_glit K) \<and> lit_occures_in_clss K N\<^sub>0\<close>

    from ball_K_Ks have "\<not> trail_defined_lit \<Gamma> (lit_of_glit K)" "lit_occures_in_clss K N\<^sub>0"
      by simp_all

    from Cons have "(scl_fol.decide (fimage cls_of_gcls N\<^sub>0) \<beta>)\<^sup>*\<^sup>* (trail_decide \<Gamma> (lit_of_glit K), U, None) S'"
    proof (intro Cons.IH[OF refl] ballI)
      show "\<Gamma>' = foldl trail_decide (trail_decide \<Gamma> (lit_of_glit K)) (map lit_of_glit Ks)"
        by (simp add: \<open>\<Gamma>' = foldl trail_decide \<Gamma> (map lit_of_glit (K # Ks))\<close>)
    next
      show "sorted_wrt (\<prec>\<^sub>l) Ks"
        using \<open>sorted_wrt (\<prec>\<^sub>l) (K # Ks)\<close> by simp
    next
      from \<open>sorted_wrt (\<prec>\<^sub>l) (K # Ks)\<close> have "distinct (K # Ks)"
        using linorder_lit.strict_sorted_iff by blast

      fix Ka assume "Ka \<in> set Ks"
      hence "\<not> trail_defined_lit \<Gamma> (lit_of_glit Ka)"
        using ball_K_Ks by simp

      from \<open>Ka \<in> set Ks\<close> have "is_neg K" and "is_neg Ka"
        using ball_K_Ks by simp_all
      hence "atm_of K \<noteq> atm_of Ka"
        using \<open>distinct (K # Ks)\<close>
        by (metis \<open>Ka \<in> set Ks\<close> distinct.simps(2) literal.expand)
      hence "term_of_gterm (atm_of Ka) \<noteq> term_of_gterm (atm_of K)"
        using inj_term_of_gterm[of UNIV, THEN injD] by metis
      hence "\<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit Ka)"
        using \<open>\<not> trail_defined_lit \<Gamma> (lit_of_glit K)\<close> \<open>\<not> trail_defined_lit \<Gamma> (lit_of_glit Ka)\<close>
        by (simp add: trail_defined_lit_iff decide_lit_def atm_of_lit_of_glit_conv)
      thus "is_neg Ka \<and> Ka \<prec>\<^sub>l L \<and>
        \<not> trail_defined_lit (trail_decide \<Gamma> (lit_of_glit K)) (lit_of_glit Ka) \<and>
        lit_occures_in_clss Ka N\<^sub>0"
        using ball_K_Ks \<open>Ka \<in> set Ks\<close>
        by simp
    qed

    moreover have "scl_fol.decide (fimage cls_of_gcls N\<^sub>0) \<beta> (\<Gamma>, U, None) (trail_decide \<Gamma> (lit_of_glit K), U, None)"
    proof (intro scl_fol.decideI[of _ _ Var, simplified])
      show "\<not> trail_defined_lit \<Gamma> (lit_of_glit K)"
        using \<open>\<not> trail_defined_lit \<Gamma> (lit_of_glit K)\<close> .
    next
      show "is_ground_lit (lit_of_glit K)"
        by (cases K) (simp_all add: is_ground_lit_def atm_of_lit_of_glit_conv)
    next
      show "fBex (cls_of_gcls |`| N\<^sub>0) ((\<in>#) (lit_of_glit K))"
        using \<open>lit_occures_in_clss K N\<^sub>0\<close>
        unfolding lit_occures_in_clss_def
        by (metis cls_of_gcls_def finsertI1 finsert_fimage imageI multiset.set_map)
    next
      have "atm_of K \<in> atms_of_clss (fset N\<^sub>0)"
        using \<open>lit_occures_in_clss K N\<^sub>0\<close>
        unfolding lit_occures_in_clss_def atms_of_clss_def
        by (metis Union_iff atms_of_def image_eqI)
      thus "ground (atm_of (lit_of_glit K)) \<and> ground \<beta> \<and>
        gterm_of_term (atm_of (lit_of_glit K)) \<prec>\<^sub>t gterm_of_term \<beta> \<or> atm_of (lit_of_glit K) = \<beta>"
        using \<beta>\<^sub>G_greatest
        by (auto simp add: atm_of_lit_of_glit_conv \<beta>_def is_greatest_in_set_wrt_iff)
    qed

    ultimately show ?case
      unfolding \<open>S = (\<Gamma>, U, None)\<close> \<open>S' = (\<Gamma>', U, None)\<close>
        \<open>\<Gamma>' = foldl trail_decide \<Gamma> (map lit_of_glit (K # Ks))\<close>
      by simp
  qed
qed

end
 
end