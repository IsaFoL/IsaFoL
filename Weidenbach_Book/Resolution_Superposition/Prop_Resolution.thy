theory Prop_Resolution
imports Entailment_Definition.Partial_Herbrand_Interpretation
  Weidenbach_Book_Base.WB_List_More
  Weidenbach_Book_Base.Wellfounded_More

begin
chapter \<open>Resolution-based techniques\<close>

text \<open>This chapter contains the formalisation of resolution and superposition.\<close>


section \<open>Resolution\<close>

subsection \<open>Simplification Rules\<close>

inductive simplify :: "'v clause_set \<Rightarrow> 'v clause_set \<Rightarrow> bool" for N :: "'v clause set" where
tautology_deletion:
  "add_mset (Pos P) (add_mset (Neg P) A) \<in> N \<Longrightarrow> simplify N (N - {add_mset (Pos P) (add_mset (Neg P) A)})"|
condensation:
  "add_mset L (add_mset L A) \<in> N \<Longrightarrow> simplify N (N - {add_mset L (add_mset L A)} \<union> {add_mset L A})" |
subsumption:
  "A \<in> N \<Longrightarrow> A \<subset># B \<Longrightarrow> B \<in> N \<Longrightarrow> simplify N (N - {B})"

lemma simplify_preserve_models':
  fixes N N' :: "'v clause_set"
  assumes "simplify N N'"
  and "total_over_m I N"
  shows "I \<Turnstile>s N' \<longrightarrow> I \<Turnstile>s N"
  using assms
proof (induct rule: simplify.induct)
  case (tautology_deletion P A)
  then have "I \<Turnstile> add_mset (Pos P) (add_mset (Neg P) A)"
    by (fastforce dest: mk_disjoint_insert)
  then show ?case by (metis Un_Diff_cancel2 true_clss_singleton true_clss_union)
next
  case (condensation A P)
  then show ?case
    by (fastforce dest: mk_disjoint_insert)
next
  case (subsumption A B)
  have "A \<noteq> B" using subsumption.hyps(2) by auto
  then have "I \<Turnstile>s N - {B} \<Longrightarrow> I \<Turnstile> A" using \<open>A \<in> N\<close> by (simp add: true_clss_def)
  moreover have "I \<Turnstile> A \<Longrightarrow> I \<Turnstile> B" using \<open>A <# B\<close> by auto
  ultimately show ?case by (metis insert_Diff_single true_clss_insert)
qed

lemma simplify_preserve_models:
  fixes N N' :: "'v clause_set"
  assumes "simplify N N'"
  and "total_over_m I N"
  shows "I \<Turnstile>s N \<longrightarrow> I \<Turnstile>s N'"
  using assms apply (induct rule: simplify.induct)
  using true_clss_def by fastforce+

lemma simplify_preserve_models'':
  fixes N N' :: "'v clause_set"
  assumes "simplify N N'"
  and "total_over_m I N'"
  shows "I \<Turnstile>s N \<longrightarrow> I \<Turnstile>s N'"
  using assms apply (induct rule: simplify.induct)
  using true_clss_def by fastforce+

lemma simplify_preserve_models_eq:
  fixes N N' :: "'v clause_set"
  assumes "simplify N N'"
  and "total_over_m I N"
  shows "I \<Turnstile>s N \<longleftrightarrow> I \<Turnstile>s N'"
  using simplify_preserve_models simplify_preserve_models' assms by blast

lemma simplify_preserves_finite:
 assumes "simplify \<psi> \<psi>'"
 shows "finite \<psi> \<longleftrightarrow> finite \<psi>'"
 using assms by (induct rule: simplify.induct, auto simp add: remove_def)

lemma rtranclp_simplify_preserves_finite:
 assumes "rtranclp simplify \<psi> \<psi>'"
 shows "finite \<psi> \<longleftrightarrow> finite \<psi>'"
 using assms by (induct rule: rtranclp_induct) (auto simp add: simplify_preserves_finite)

lemma simplify_atms_of_ms:
  assumes "simplify \<psi> \<psi>'"
  shows "atms_of_ms \<psi>' \<subseteq> atms_of_ms \<psi>"
  using assms unfolding atms_of_ms_def
proof (induct rule: simplify.induct)
  case (tautology_deletion A P)
  then show ?case by auto
next
  case (condensation P A)
  moreover have "A + {#P#} + {#P#} \<in> \<psi> \<Longrightarrow> \<exists>x\<in>\<psi>. atm_of P \<in> atm_of ` set_mset x"
    by (metis Un_iff atms_of_def atms_of_plus atms_of_singleton insert_iff)
  ultimately show ?case by (auto simp add: atms_of_def)
next
  case (subsumption A P)
  then show ?case by auto
qed

lemma rtranclp_simplify_atms_of_ms:
  assumes "rtranclp simplify \<psi> \<psi>'"
  shows "atms_of_ms \<psi>' \<subseteq> atms_of_ms \<psi>"
  using assms apply (induct rule: rtranclp_induct)
   apply (fastforce intro: simplify_atms_of_ms)
  using simplify_atms_of_ms by blast

lemma factoring_imp_simplify:
  assumes "{#L, L#} + C \<in> N"
  shows "\<exists>N'. simplify N N'"
proof -
  have "add_mset L (add_mset L C) \<in> N" using assms by (simp add: add.commute union_lcomm)
  from condensation[OF this] show ?thesis by blast
qed


subsection \<open>Unconstrained Resolution\<close>

type_synonym 'v uncon_state = "'v clause_set"

inductive uncon_res :: "'v uncon_state \<Rightarrow> 'v uncon_state \<Rightarrow> bool" where
resolution:
  "{#Pos p#} + C \<in> N \<Longrightarrow> {#Neg p#} + D \<in> N \<Longrightarrow> (add_mset (Pos p) C, add_mset (Neg P) D) \<notin> already_used
    \<Longrightarrow> uncon_res N (N \<union> {C + D})" |
factoring: "{#L#} + {#L#} + C \<in> N \<Longrightarrow> uncon_res N (insert (add_mset L C) N)"

lemma uncon_res_increasing:
  assumes "uncon_res S S'" and "\<psi> \<in> S"
  shows "\<psi> \<in> S'"
  using assms by (induct rule: uncon_res.induct) auto

lemma rtranclp_uncon_inference_increasing:
  assumes "rtranclp uncon_res S S'" and "\<psi> \<in> S"
  shows "\<psi> \<in> S'"
  using assms by (induct rule: rtranclp_induct) (auto simp add: uncon_res_increasing)


subsubsection \<open>Subsumption\<close>

definition subsumes :: "'a literal multiset \<Rightarrow> 'a literal multiset \<Rightarrow> bool" where
"subsumes \<chi> \<chi>' \<longleftrightarrow>
  (\<forall>I. total_over_m I {\<chi>'} \<longrightarrow> total_over_m I {\<chi>})
  \<and> (\<forall>I. total_over_m I {\<chi>} \<longrightarrow> I \<Turnstile> \<chi> \<longrightarrow> I \<Turnstile> \<chi>')"

lemma subsumes_refl[simp]:
  "subsumes \<chi> \<chi>"
  unfolding subsumes_def by auto


lemma subsumes_subsumption:
  assumes "subsumes D \<chi>"
  and "C \<subset># D" and "\<not>tautology \<chi>"
  shows "subsumes C \<chi>" unfolding subsumes_def
  using assms subsumption_total_over_m subsumption_chained unfolding subsumes_def
  by (blast intro!: subset_mset.less_imp_le)

lemma subsumes_tautology:
  assumes "subsumes (add_mset (Pos P) (add_mset (Neg P) C)) \<chi>"
  shows "tautology \<chi>"
  using assms unfolding subsumes_def by (auto simp add: tautology_def)


subsection \<open>Inference Rule\<close>

type_synonym 'v state = "'v clause_set \<times> ('v clause \<times> 'v clause) set"

inductive inference_clause :: "'v state \<Rightarrow> 'v clause \<times> ('v clause \<times> 'v clause) set \<Rightarrow> bool"
  (infix "\<Rightarrow>\<^sub>\<Res>" 100) where
resolution:
  "{#Pos p#} + C \<in> N \<Longrightarrow> {#Neg p#} + D \<in> N \<Longrightarrow> ({#Pos p#} + C, {#Neg p#} + D) \<notin> already_used
  \<Longrightarrow> inference_clause (N, already_used) (C + D, already_used \<union> {({#Pos p#} + C, {#Neg p#} + D)})" |
factoring: "{#L, L#} + C \<in> N \<Longrightarrow> inference_clause (N, already_used) (C + {#L#}, already_used)"

inductive inference :: "'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
inference_step: "inference_clause S (clause, already_used)
  \<Longrightarrow> inference S (fst S \<union> {clause}, already_used)"


abbreviation already_used_inv
  :: "'a literal multiset set \<times> ('a literal multiset \<times> 'a literal multiset) set \<Rightarrow> bool" where
"already_used_inv state \<equiv>
  (\<forall>(A, B) \<in> snd state. \<exists>p. Pos p \<in># A \<and> Neg p \<in># B \<and>
          ((\<exists>\<chi> \<in> fst state. subsumes \<chi> ((A - {#Pos p#}) + (B - {#Neg p#})))
            \<or> tautology ((A - {#Pos p#}) + (B - {#Neg p#}))))"

lemma inference_clause_preserves_already_used_inv:
  assumes "inference_clause S S'"
  and "already_used_inv S"
  shows "already_used_inv (fst S \<union> {fst S'}, snd S')"
  using assms apply (induct rule: inference_clause.induct)
  by fastforce+

lemma inference_preserves_already_used_inv:
  assumes "inference S S'"
  and "already_used_inv S"
  shows "already_used_inv S'"
  using assms
proof (induct rule: inference.induct)
  case (inference_step S clause already_used)
  then show ?case
    using inference_clause_preserves_already_used_inv[of S "(clause, already_used)"] by simp
qed

lemma rtranclp_inference_preserves_already_used_inv:
  assumes "rtranclp inference S S'"
  and "already_used_inv S"
  shows "already_used_inv S'"
  using assms apply (induct rule: rtranclp_induct, simp)
  using inference_preserves_already_used_inv unfolding tautology_def by fast

lemma subsumes_condensation:
  assumes "subsumes (C + {#L#} + {#L#}) D"
  shows "subsumes (C + {#L#}) D"
  using assms unfolding subsumes_def by simp

lemma simplify_preserves_already_used_inv:
  assumes "simplify N N'"
  and "already_used_inv (N, already_used)"
  shows "already_used_inv (N', already_used)"
  using assms
proof (induct rule: simplify.induct)
  case (condensation C L)
  then show ?case
    using subsumes_condensation by simp fast
next
  {
     fix a:: 'a and A :: "'a set" and P
     have "(\<exists>x \<in> Set.remove a A. P x) \<longleftrightarrow> (\<exists>x \<in> A. x \<noteq> a \<and> P x)" by auto
  } note ex_member_remove = this
  {
    fix a a0 :: "'v clause" and A :: "'v clause_set" and y
    assume "a \<in> A" and "a0 \<subset># a"
    then have "(\<exists>x \<in> A. subsumes x y) \<longleftrightarrow> (subsumes a y \<or> (\<exists>x \<in> A. x \<noteq> a \<and> subsumes x y))"
      by auto
  } note tt2 = this
  case (subsumption A B) note A = this(1) and AB = this(2) and B = this(3) and inv = this(4)
  show ?case
    proof (standard, standard)
      fix x a b
      assume x: "x \<in> snd (N - {B}, already_used)" and [simp]: "x = (a, b)"
      obtain p where p: "Pos p \<in># a \<and> Neg p \<in># b" and
        q: "(\<exists>\<chi>\<in>N. subsumes \<chi> (a - {#Pos p#} + (b - {#Neg p#})))
          \<or> tautology (a - {#Pos p#} + (b - {#Neg p#}))"
        using inv x by fastforce
      consider (taut) "tautology (a - {#Pos p#} + (b - {#Neg p#}))" |
        (\<chi>) \<chi> where "\<chi> \<in> N" "subsumes \<chi> (a - {#Pos p#} + (b - {#Neg p#}))"
          "\<not>tautology (a - {#Pos p#} + (b - {#Neg p#}))"
        using q by auto
      then show
        "\<exists>p. Pos p \<in># a \<and> Neg p \<in># b
             \<and> ((\<exists>\<chi>\<in>fst (N - {B}, already_used). subsumes \<chi> (a - {#Pos p#} + (b - {#Neg p#})))
                 \<or> tautology (a - {#Pos p#} + (b - {#Neg p#})))"
        proof cases
          case taut
          then show ?thesis using p by auto
        next
          case \<chi> note H = this
          show ?thesis using p A AB B subsumes_subsumption[OF _ AB H(3)] H(1,2) by fastforce
        qed
    qed
next
  case (tautology_deletion P C)
  then show ?case
  proof clarify
    fix a b
    assume "add_mset (Pos P) (add_mset (Neg P) C) \<in> N"
    assume "already_used_inv (N, already_used)"
    and "(a, b) \<in> snd (N - {add_mset (Pos P) (add_mset (Neg P) C)}, already_used)"
    then obtain p where
      "Pos p \<in># a \<and> Neg p \<in># b \<and>
        ((\<exists>\<chi>\<in>fst (N \<union> {add_mset (Pos P) (add_mset (Neg P) C)}, already_used).
              subsumes \<chi> (a - {#Pos p#} + (b - {#Neg p#})))
          \<or> tautology (a - {#Pos p#} + (b - {#Neg p#})))"
      by fastforce
    moreover have "tautology (add_mset (Pos P) (add_mset (Neg P) C))" by auto
    ultimately show
      "\<exists>p. Pos p \<in># a \<and> Neg p \<in># b \<and>
      ((\<exists>\<chi>\<in>fst (N - {add_mset (Pos P) (add_mset (Neg P) C)}, already_used).
        subsumes \<chi> (remove1_mset (Pos p) a + remove1_mset (Neg p) b)) \<or>
        tautology (remove1_mset (Pos p) a + remove1_mset (Neg p) b))"
      by (metis (no_types) Diff_iff Un_insert_right empty_iff fst_conv insertE subsumes_tautology
        sup_bot.right_neutral)
  qed
qed


lemma
  factoring_satisfiable: "I \<Turnstile> add_mset L (add_mset L C) \<longleftrightarrow> I \<Turnstile> add_mset L C" and
  resolution_satisfiable:
    "consistent_interp I \<Longrightarrow> I \<Turnstile> add_mset (Pos p) C \<Longrightarrow> I \<Turnstile> add_mset (Neg p) D \<Longrightarrow> I \<Turnstile> C + D" and
    factoring_same_vars: "atms_of (add_mset L (add_mset L C)) = atms_of (add_mset L C)"
  unfolding true_cls_def consistent_interp_def by (fastforce split: if_split_asm)+

lemma inference_increasing:
  assumes "inference S S'" and "\<psi> \<in> fst S"
  shows "\<psi> \<in> fst S'"
  using assms by (induct rule: inference.induct, auto)

lemma rtranclp_inference_increasing:
  assumes "rtranclp inference S S'" and "\<psi> \<in> fst S"
  shows "\<psi> \<in> fst S'"
  using assms by (induct rule: rtranclp_induct, auto simp add: inference_increasing)

lemma inference_clause_already_used_increasing:
  assumes "inference_clause S S'"
  shows "snd S \<subseteq> snd S'"
  using assms by (induct rule:inference_clause.induct, auto)


lemma inference_already_used_increasing:
  assumes "inference S S'"
  shows "snd S \<subseteq> snd S'"
  using assms apply (induct rule:inference.induct)
  using inference_clause_already_used_increasing by fastforce

lemma inference_clause_preserve_models:
  fixes N N' :: "'v clause_set"
  assumes "inference_clause T T'"
  and "total_over_m I (fst T)"
  and consistent: "consistent_interp I"
  shows "I \<Turnstile>s fst T \<longleftrightarrow> I \<Turnstile>s fst T \<union> {fst T'}"
  using assms apply (induct rule: inference_clause.induct)
  unfolding consistent_interp_def true_clss_def by auto force+


lemma inference_preserve_models:
  fixes N N' :: "'v clause_set"
  assumes "inference T T'"
  and "total_over_m I (fst T)"
  and consistent: "consistent_interp I"
  shows "I \<Turnstile>s fst T \<longleftrightarrow> I \<Turnstile>s fst T'"
  using assms apply (induct rule: inference.induct)
  using inference_clause_preserve_models by fastforce

lemma inference_clause_preserves_atms_of_ms:
  assumes "inference_clause S S'"
  shows "atms_of_ms (fst (fst S \<union> {fst S'}, snd S')) \<subseteq> atms_of_ms (fst S)"
  using assms by (induct rule: inference_clause.induct) (auto dest!: atms_of_atms_of_ms_mono)

lemma inference_preserves_atms_of_ms:
  fixes N N' :: "'v clause_set"
  assumes "inference T T'"
  shows "atms_of_ms (fst T') \<subseteq> atms_of_ms (fst T)"
  using assms apply (induct rule: inference.induct)
  using inference_clause_preserves_atms_of_ms by fastforce

lemma inference_preserves_total:
  fixes N N' :: "'v clause_set"
  assumes "inference (N, already_used) (N', already_used')"
  shows "total_over_m I N \<Longrightarrow> total_over_m I N'"
    using assms inference_preserves_atms_of_ms unfolding total_over_m_def total_over_set_def
    by fastforce


lemma rtranclp_inference_preserves_total:
  assumes "rtranclp inference T T'"
  shows "total_over_m I (fst T) \<Longrightarrow> total_over_m I (fst T')"
  using assms by (induct rule: rtranclp_induct, auto simp add: inference_preserves_total)

lemma rtranclp_inference_preserve_models:
  assumes "rtranclp inference N N'"
  and "total_over_m I (fst N)"
  and consistent: "consistent_interp I"
  shows "I \<Turnstile>s fst N \<longleftrightarrow> I \<Turnstile>s fst N'"
  using assms apply (induct rule: rtranclp_induct)
  apply (simp add: inference_preserve_models)
  using inference_preserve_models rtranclp_inference_preserves_total by blast

lemma inference_preserves_finite:
  assumes "inference \<psi> \<psi>'" and "finite (fst \<psi>)"
  shows "finite (fst \<psi>')"
  using assms by (induct rule: inference.induct, auto simp add: simplify_preserves_finite)


lemma inference_clause_preserves_finite_snd:
  assumes "inference_clause \<psi> \<psi>'" and "finite (snd \<psi>)"
  shows "finite (snd \<psi>')"
  using assms by (induct rule: inference_clause.induct, auto)


lemma inference_preserves_finite_snd:
  assumes "inference \<psi> \<psi>'" and "finite (snd \<psi>)"
  shows "finite (snd \<psi>')"
  using assms inference_clause_preserves_finite_snd by (induct rule: inference.induct, fastforce)


lemma rtranclp_inference_preserves_finite:
  assumes "rtranclp inference \<psi> \<psi>'" and "finite (fst \<psi>)"
  shows "finite (fst \<psi>')"
  using assms by (induct rule: rtranclp_induct)
    (auto simp add: simplify_preserves_finite inference_preserves_finite)

lemma consistent_interp_insert:
  assumes "consistent_interp I"
  and "atm_of P \<notin> atm_of ` I"
  shows "consistent_interp (insert P I)"
proof -
  have P: "insert P I = I \<union> {P}" by auto
  show ?thesis unfolding P
  apply (rule consistent_interp_disjoint)
  using assms by (auto simp: image_iff)
qed

lemma simplify_clause_preserves_sat:
  assumes simp: "simplify \<psi> \<psi>'"
  and "satisfiable \<psi>'"
  shows "satisfiable \<psi>"
  using assms
proof induction
  case (tautology_deletion P A) note AP = this(1) and sat = this(2)
  let ?A' = "add_mset (Pos P) (add_mset (Neg P) A)"
  let ?\<psi>' = "\<psi> - {?A'}"
  obtain I where
    I: "I \<Turnstile>s ?\<psi>'" and
    cons: "consistent_interp I" and
    tot: "total_over_m I ?\<psi>'"
    using sat unfolding satisfiable_def by auto
  { assume "Pos P \<in> I \<or> Neg P \<in> I"
    then have "I \<Turnstile> ?A'" by auto
    then have "I \<Turnstile>s \<psi>" using I by (metis insert_Diff tautology_deletion.hyps true_clss_insert)
    then have "?case" using cons tot by auto
  }
  moreover {
    assume Pos: "Pos P \<notin> I" and Neg: "Neg P \<notin> I"
    then have "consistent_interp (I \<union> {Pos P})" using cons by simp
    moreover have I'A: "I \<union> {Pos P} \<Turnstile> ?A'" by auto
    have "{Pos P} \<union> I \<Turnstile>s \<psi> - {?A'}"
      using \<open>I \<Turnstile>s \<psi> - {?A'}\<close> true_clss_union_increase' by blast
    then have "I \<union> {Pos P} \<Turnstile>s \<psi>"
      by (metis (no_types) Un_empty_right Un_insert_left Un_insert_right I'A insert_Diff
        sup_bot.left_neutral tautology_deletion.hyps true_clss_insert)
    ultimately have ?case using satisfiable_carac' by blast
  }
  ultimately show ?case by blast
next
  case (condensation L A) note AL = this(1) and sat = this(2)
  let ?A' = "add_mset L A"
  let ?A = "add_mset L (add_mset L A)"
  have f3: "simplify \<psi> (\<psi> - {?A} \<union> {?A'})"
    using AL simplify.condensation by blast
  obtain LL :: "'a literal set" where
    f4: "LL \<Turnstile>s \<psi> - {?A} \<union> {?A'}
      \<and> consistent_interp LL
      \<and> total_over_m LL (\<psi> - {?A} \<union> {?A'})"
    using sat by (meson satisfiable_def)
  have f5: "insert (A + {#L#} + {#L#}) (\<psi> - {A + {#L#} + {#L#}}) = \<psi>"
    using AL by fastforce
  have "atms_of (?A') = atms_of (?A)"
    by simp
  then show ?case
    using f5 f4 f3 by (metis Un_insert_right add_mset_add_single atms_of_ms_insert satisfiable_carac
        simplify_preserve_models' sup_bot.right_neutral total_over_m_def)
next
  case (subsumption A B) note A = this(1) and AB = this(2) and B = this(3) and sat = this(4)
  let ?\<psi>' = "\<psi> - {B}"
  obtain I where I: "I \<Turnstile>s ?\<psi>'" and cons: "consistent_interp I" and tot: "total_over_m I ?\<psi>'"
    using sat unfolding satisfiable_def by auto
  have "I \<Turnstile> A" using A I by (metis AB Diff_iff subset_mset.less_irrefl singletonD true_clss_def)
  then have "I \<Turnstile> B" using AB subset_mset.less_imp_le true_cls_mono_leD by blast
  then have "I \<Turnstile>s \<psi>" using I by (metis insert_Diff_single true_clss_insert)
  then show ?case using cons satisfiable_carac' by blast
qed

lemma simplify_preserves_unsat:
  assumes "inference \<psi> \<psi>'"
  shows "satisfiable (fst \<psi>') \<longrightarrow> satisfiable (fst \<psi>)"
  using assms apply (induct rule: inference.induct)
  using satisfiable_decreasing by (metis fst_conv)+

lemma inference_preserves_unsat:
  assumes "inference\<^sup>*\<^sup>* S S'"
  shows "satisfiable (fst S') \<longrightarrow>  satisfiable (fst S)"
  using assms apply (induct rule: rtranclp_induct)
  apply simp_all
  using simplify_preserves_unsat by blast

datatype 'v sem_tree = Node "'v" "'v sem_tree" "'v sem_tree" | Leaf

fun sem_tree_size :: "'v sem_tree \<Rightarrow> nat" where
"sem_tree_size Leaf = 0" |
"sem_tree_size (Node _ ag ad) = 1 + sem_tree_size ag + sem_tree_size ad"

lemma sem_tree_size[case_names bigger]:
  "(\<And>xs:: 'v sem_tree. (\<And>ys:: 'v sem_tree. sem_tree_size ys < sem_tree_size xs \<Longrightarrow> P ys) \<Longrightarrow> P xs)
  \<Longrightarrow> P xs"
  by (fact Nat.measure_induct_rule)


fun partial_interps :: "'v sem_tree \<Rightarrow> 'v partial_interp \<Rightarrow> 'v clause_set \<Rightarrow> bool" where
"partial_interps Leaf I \<psi> = (\<exists>\<chi>. \<not> I \<Turnstile> \<chi> \<and> \<chi> \<in> \<psi> \<and> total_over_m I {\<chi>})" |
"partial_interps (Node v ag ad) I \<psi> \<longleftrightarrow>
  (partial_interps ag (I \<union> {Pos v}) \<psi> \<and> partial_interps ad (I\<union> {Neg v}) \<psi>)"


lemma simplify_preserve_partial_leaf:
  "simplify N N' \<Longrightarrow> partial_interps Leaf I N \<Longrightarrow> partial_interps Leaf I N'"
  apply (induct rule: simplify.induct)
    using union_lcomm apply auto[1]
   apply (simp)
   apply (metis atms_of_remdups_mset remdups_mset_singleton_sum true_cls_add_mset union_single_eq_member)
  apply auto
  by (metis atms_of_ms_emtpy_set subsumption_total_over_m total_over_m_def total_over_m_insert
      total_over_set_empty true_cls_mono_leD)

lemma simplify_preserve_partial_tree:
  assumes "simplify N N'"
  and "partial_interps t I N"
  shows "partial_interps t I N'"
  using assms apply (induct t arbitrary: I, simp)
  using simplify_preserve_partial_leaf by metis


lemma inference_preserve_partial_tree:
  assumes "inference S S'"
  and "partial_interps t I (fst S)"
  shows "partial_interps t I (fst S')"
  using assms apply (induct t arbitrary: I, simp_all)
  by (meson inference_increasing)


lemma rtranclp_inference_preserve_partial_tree:
  assumes "rtranclp inference N N'"
  and "partial_interps t I (fst N)"
  shows "partial_interps t I (fst N')"
  using assms apply (induct rule: rtranclp_induct, auto)
  using inference_preserve_partial_tree by force


function build_sem_tree :: "'v :: linorder set \<Rightarrow> 'v clause_set \<Rightarrow> 'v sem_tree" where
"build_sem_tree atms \<psi> =
  (if atms = {} \<or> \<not> finite atms
  then Leaf
  else Node (Min atms) (build_sem_tree (Set.remove (Min atms) atms) \<psi>)
     (build_sem_tree (Set.remove (Min atms) atms) \<psi>))"
by auto
termination
  apply (relation "measure (\<lambda>(A, _).  card A)", simp_all)
  apply (metis Min_in card_Diff1_less remove_def)+
done
declare build_sem_tree.induct[case_names tree]

lemma unsatisfiable_empty[simp]:
  "\<not>unsatisfiable {}"
   unfolding satisfiable_def apply auto
  using consistent_interp_def unfolding total_over_m_def total_over_set_def atms_of_ms_def by blast

lemma partial_interps_build_sem_tree_atms_general:
  fixes \<psi> :: "'v :: linorder clause_set" and p :: "'v literal list"
  assumes unsat: "unsatisfiable \<psi>" and "finite \<psi>" and "consistent_interp I"
  and "finite atms"
  and "atms_of_ms \<psi> = atms \<union> atms_of_s I" and "atms \<inter> atms_of_s I = {}"
  shows "partial_interps (build_sem_tree atms \<psi>) I \<psi>"
  using assms
proof (induct arbitrary: I rule: build_sem_tree.induct)
  case (1 atms \<psi> Ia) note IH1 = this(1) and IH2 = this(2) and unsat = this(3) and finite = this(4)
    and cons = this(5)  and f = this(6) and un = this(7) and disj = this(8)
  {
    assume atms: "atms = {}"
    then have atmsIa: "atms_of_ms \<psi> = atms_of_s Ia" using un by auto
    then have "total_over_m Ia \<psi>" unfolding total_over_m_def atmsIa by auto
    then have \<chi>: "\<exists>\<chi> \<in> \<psi>. \<not> Ia \<Turnstile> \<chi>"
      using unsat cons unfolding true_clss_def satisfiable_def by auto
    then have "build_sem_tree atms \<psi> = Leaf" using atms by auto
    moreover
      have tot: "\<And>\<chi>. \<chi> \<in> \<psi> \<Longrightarrow> total_over_m Ia {\<chi>}"
      unfolding total_over_m_def total_over_set_def atms_of_ms_def atms_of_s_def
      using atmsIa atms_of_ms_def by fastforce
    have "partial_interps Leaf Ia \<psi>"
      using \<chi> tot by (auto simp add: total_over_m_def total_over_set_def atms_of_ms_def)

      ultimately have ?case by metis
  }
  moreover {
    assume atms: "atms \<noteq> {}"
    have "build_sem_tree atms \<psi> = Node (Min atms) (build_sem_tree (Set.remove (Min atms) atms) \<psi>)
       (build_sem_tree (Set.remove (Min atms) atms) \<psi>)"
      using build_sem_tree.simps[of "atms" \<psi>] f atms by metis

    have "consistent_interp (Ia \<union> {Pos (Min atms)})" unfolding consistent_interp_def
      by (metis Int_iff Min_in Un_iff atm_of_uminus atms cons consistent_interp_def disj empty_iff
        f in_atms_of_s_decomp insert_iff literal.distinct(1) literal.exhaust_sel literal.sel(2)
        uminus_Neg uminus_Pos)
    moreover have "atms_of_ms \<psi> = Set.remove (Min atms) atms \<union> atms_of_s (Ia \<union> {Pos (Min atms)})"
      using Min_in atms f un by fastforce
    moreover have disj': "Set.remove (Min atms) atms \<inter> atms_of_s (Ia \<union> {Pos (Min atms)}) = {}"
      by simp (metis disj disjoint_iff_not_equal member_remove)
    moreover have "finite (Set.remove (Min atms) atms)" using f by (simp add: remove_def)
    ultimately have subtree1: "partial_interps (build_sem_tree (Set.remove (Min atms) atms) \<psi>)
        (Ia \<union> {Pos (Min atms)}) \<psi>"
      using IH1[of "Ia \<union> {Pos (Min (atms))}"] atms f unsat finite by metis

    have "consistent_interp (Ia \<union> {Neg (Min atms)})" unfolding consistent_interp_def
      by (metis Int_iff Min_in Un_iff atm_of_uminus atms cons consistent_interp_def disj empty_iff
        f in_atms_of_s_decomp insert_iff literal.distinct(1) literal.exhaust_sel literal.sel(2)
        uminus_Neg)
    moreover have "atms_of_ms \<psi> = Set.remove (Min atms) atms \<union> atms_of_s (Ia \<union> {Neg (Min atms)})"
      using \<open>atms_of_ms \<psi> = Set.remove (Min atms) atms \<union> atms_of_s (Ia \<union> {Pos (Min atms)})\<close> by blast

    moreover have disj': "Set.remove (Min atms) atms \<inter> atms_of_s (Ia \<union> {Neg (Min atms)}) = {}"
      using disj by auto
    moreover have "finite (Set.remove (Min atms) atms)" using f by (simp add: remove_def)
    ultimately have subtree2: "partial_interps (build_sem_tree (Set.remove (Min atms) atms) \<psi>)
        (Ia \<union> {Neg (Min atms)}) \<psi>"
      using IH2[of "Ia \<union> {Neg (Min (atms))}"]  atms f unsat finite by metis

    then have ?case
      using IH1 subtree1 subtree2 f local.finite unsat atms by simp
  }
  ultimately show ?case by metis
qed


lemma partial_interps_build_sem_tree_atms:
  fixes \<psi> :: "'v :: linorder clause_set" and p :: "'v literal list"
  assumes unsat: "unsatisfiable \<psi>" and finite: "finite \<psi>"
  shows "partial_interps (build_sem_tree (atms_of_ms \<psi>) \<psi>) {} \<psi>"
proof -
  have "consistent_interp {}" unfolding consistent_interp_def by auto
  moreover have "atms_of_ms \<psi> = atms_of_ms \<psi> \<union> atms_of_s {}" unfolding atms_of_s_def by auto
  moreover have "atms_of_ms \<psi> \<inter> atms_of_s {} = {} " unfolding atms_of_s_def by auto
  moreover have "finite (atms_of_ms \<psi>)" unfolding atms_of_ms_def using finite by simp
  ultimately show "partial_interps (build_sem_tree (atms_of_ms \<psi>) \<psi>) {} \<psi>"
    using partial_interps_build_sem_tree_atms_general[of "\<psi>" "{}" "atms_of_ms \<psi>"] assms by metis
qed

lemma can_decrease_count:
  fixes \<psi>'' :: "'v clause_set \<times> ('v clause \<times> 'v clause \<times> 'v) set"
  assumes "count \<chi> L = n"
  and "L \<in># \<chi>" and "\<chi> \<in> fst \<psi>"
  shows "\<exists>\<psi>' \<chi>'. inference\<^sup>*\<^sup>* \<psi> \<psi>' \<and> \<chi>' \<in> fst \<psi>' \<and> (\<forall>L. L \<in># \<chi> \<longleftrightarrow> L \<in># \<chi>')
                 \<and> count \<chi>' L = 1
                 \<and> (\<forall>\<phi>. \<phi> \<in> fst \<psi> \<longrightarrow> \<phi> \<in> fst \<psi>')
                 \<and> (I \<Turnstile> \<chi> \<longleftrightarrow> I \<Turnstile> \<chi>')
                 \<and> (\<forall>I'. total_over_m I' {\<chi>} \<longrightarrow> total_over_m I' {\<chi>'})"
  using assms
proof (induct n arbitrary: \<chi> \<psi>)
  case 0
  then show ?case by (simp add: not_in_iff[symmetric])
next
   case (Suc n \<chi>)
   note IH = this(1) and count = this(2) and L = this(3) and \<chi> = this(4)
   {
     assume "n = 0"
     then have "inference\<^sup>*\<^sup>* \<psi> \<psi>"
     and "\<chi> \<in> fst \<psi>"
     and "\<forall>L. (L \<in># \<chi>) \<longleftrightarrow> (L \<in># \<chi>)"
     and "count \<chi> L = (1::nat)"
     and "\<forall>\<phi>. \<phi> \<in> fst \<psi> \<longrightarrow> \<phi> \<in> fst \<psi>"
       by (auto simp add: count L \<chi>)
     then have ?case by metis
   }
   moreover {
     assume "n > 0"
     then have "\<exists>C. \<chi> = C + {#L, L#}"
       by (metis Suc_inject union_mset_add_mset_right add_mset_add_single count_add_mset count_inI
           less_not_refl3 local.count mset_add zero_less_Suc)
     then obtain C where C: "\<chi> = C + {#L, L#}" by metis
     let ?\<chi>' = "C +{#L#}"
     let ?\<psi>' = "(fst \<psi> \<union> {?\<chi>'}, snd \<psi>)"
     have \<phi>: "\<forall>\<phi> \<in> fst \<psi>. (\<phi> \<in> fst \<psi> \<or> \<phi> \<noteq> ?\<chi>') \<longleftrightarrow> \<phi> \<in> fst ?\<psi>'" unfolding C by auto
     have inf: "inference \<psi> ?\<psi>'"
       using C factoring \<chi> prod.collapse union_commute inference_step
       by (metis add_mset_add_single)
     moreover have count': "count ?\<chi>' L = n" using C count by auto
     moreover have L\<chi>': "L \<in># ?\<chi>'" by auto
     moreover have \<chi>'\<psi>': "?\<chi>' \<in> fst ?\<psi>'" by auto
     ultimately obtain \<psi>''  and \<chi>''
     where
       "inference\<^sup>*\<^sup>* ?\<psi>' \<psi>''" and
       \<alpha>: "\<chi>'' \<in> fst \<psi>''" and
       "\<forall>La. (La \<in># ?\<chi>') \<longleftrightarrow> (La \<in># \<chi>'')" and
       \<beta>: "count \<chi>'' L = (1::nat)" and
       \<phi>': "\<forall>\<phi>. \<phi> \<in> fst ?\<psi>' \<longrightarrow> \<phi> \<in> fst \<psi>''" and
       I\<chi>: "I \<Turnstile> ?\<chi>' \<longleftrightarrow> I \<Turnstile> \<chi>''" and
       tot: "\<forall>I'. total_over_m I' {?\<chi>'} \<longrightarrow> total_over_m I' {\<chi>''}"
       using IH[of ?\<chi>' ?\<psi>'] count' L\<chi>' \<chi>'\<psi>' by blast

     then have "inference\<^sup>*\<^sup>* \<psi> \<psi>''"
     and "\<forall>La. (La \<in># \<chi>) \<longleftrightarrow> (La \<in># \<chi>'')"
     using inf unfolding C by auto
     moreover have "\<forall>\<phi>. \<phi> \<in> fst \<psi> \<longrightarrow> \<phi> \<in> fst \<psi>''" using \<phi> \<phi>' by metis
     moreover have "I \<Turnstile> \<chi> \<longleftrightarrow> I \<Turnstile> \<chi>''" using I\<chi> unfolding true_cls_def C by auto
     moreover have "\<forall>I'. total_over_m I' {\<chi>} \<longrightarrow> total_over_m I' {\<chi>''}"
       using tot unfolding C total_over_m_def by auto
     ultimately have ?case using \<phi> \<phi>' \<alpha> \<beta>  by metis
  }
  ultimately show ?case by auto
qed

lemma can_decrease_tree_size:
  fixes \<psi> :: "'v state" and tree :: "'v sem_tree"
  assumes "finite (fst \<psi>)" and "already_used_inv \<psi>"
  and "partial_interps tree I (fst \<psi>)"
  shows "\<exists>(tree':: 'v sem_tree) \<psi>'. inference\<^sup>*\<^sup>* \<psi> \<psi>' \<and> partial_interps tree' I (fst \<psi>')
             \<and> (sem_tree_size tree' < sem_tree_size tree \<or> sem_tree_size tree = 0)"
  using assms
proof (induct arbitrary: I rule: sem_tree_size)
  case (bigger xs I) note IH = this(1) and finite = this(2) and a_u_i = this(3) and part = this(4)

  {
    assume "sem_tree_size xs = 0"
    then have "?case" using part by blast
  }

  moreover {
    assume sn0: "sem_tree_size xs > 0"
    obtain ag ad v where xs: "xs = Node v ag ad" using sn0 by (cases xs, auto)
    {
      assume "sem_tree_size ag = 0" and "sem_tree_size ad = 0"
      then have ag: "ag = Leaf" and ad: "ad = Leaf" by (cases ag,  auto) (cases ad,  auto)

      then obtain \<chi> \<chi>' where
        \<chi>: "\<not> I \<union> {Pos v} \<Turnstile> \<chi>" and
        tot\<chi>: "total_over_m (I \<union> {Pos v}) {\<chi>}" and
        \<chi>\<psi>: "\<chi> \<in> fst \<psi>" and
        \<chi>': "\<not> I \<union> {Neg v} \<Turnstile> \<chi>'" and
        tot\<chi>': "total_over_m (I \<union> {Neg v}) {\<chi>'}" and
        \<chi>'\<psi>: "\<chi>' \<in> fst \<psi>"
        using part unfolding xs by auto
      have Posv: "Pos v \<notin># \<chi>" using \<chi> unfolding true_cls_def true_lit_def by auto
      have Negv: "Neg v \<notin># \<chi>'" using \<chi>' unfolding true_cls_def true_lit_def by auto
      {
        assume Neg\<chi>: "Neg v \<notin># \<chi>"
        have "\<not> I \<Turnstile> \<chi>" using \<chi> Posv unfolding true_cls_def true_lit_def by auto
        moreover have "total_over_m I {\<chi>}"
          using Posv Neg\<chi> atm_imp_pos_or_neg_lit tot\<chi> unfolding total_over_m_def total_over_set_def
          by fastforce
        ultimately have "partial_interps Leaf I (fst \<psi>)"
        and "sem_tree_size Leaf < sem_tree_size xs"
        and "inference\<^sup>*\<^sup>* \<psi> \<psi>"
          unfolding xs by (auto simp add: \<chi>\<psi>)
      }
      moreover {
        assume Pos\<chi>: "Pos v \<notin># \<chi>'"
        then have I\<chi>: "\<not> I \<Turnstile> \<chi>'" using \<chi>' Posv unfolding true_cls_def true_lit_def by auto
        moreover have "total_over_m I {\<chi>'}"
          using Negv Pos\<chi> atm_imp_pos_or_neg_lit tot\<chi>'
          unfolding total_over_m_def total_over_set_def by fastforce
        ultimately have "partial_interps Leaf I (fst \<psi>)" and
          "sem_tree_size Leaf < sem_tree_size xs" and
          "inference\<^sup>*\<^sup>* \<psi> \<psi>"
          using \<chi>'\<psi> I\<chi> unfolding xs by auto
      }
      moreover {
        assume neg: "Neg v \<in># \<chi>" and pos: "Pos v \<in># \<chi>'"
        then obtain \<psi>' \<chi>2 where inf: "rtranclp inference \<psi> \<psi>'" and \<chi>2incl: "\<chi>2 \<in> fst \<psi>'"
          and \<chi>\<chi>2_incl: "\<forall>L. L \<in># \<chi> \<longleftrightarrow> L \<in># \<chi>2"
          and count\<chi>2: "count \<chi>2 (Neg v) = 1"
          and \<phi>: "\<forall>\<phi>::'v literal multiset. \<phi> \<in> fst \<psi> \<longrightarrow> \<phi> \<in> fst \<psi>'"
          and I\<chi>: "I \<Turnstile> \<chi> \<longleftrightarrow> I \<Turnstile> \<chi>2"
          and tot_imp\<chi>: "\<forall>I'. total_over_m I' {\<chi>} \<longrightarrow> total_over_m I' {\<chi>2}"
          using can_decrease_count[of \<chi> "Neg v" "count \<chi> (Neg v)" \<psi> I] \<chi>\<psi> \<chi>'\<psi> by auto

        have "\<chi>' \<in> fst \<psi>'" by (simp add: \<chi>'\<psi> \<phi>)
        with pos
        obtain \<psi>'' \<chi>2' where
        inf': "inference\<^sup>*\<^sup>* \<psi>' \<psi>''"
        and \<chi>2'_incl: "\<chi>2' \<in> fst \<psi>''"
        and \<chi>'\<chi>2_incl: "\<forall>L::'v literal. (L \<in># \<chi>') = (L \<in># \<chi>2')"
        and count\<chi>2': "count \<chi>2' (Pos v) = (1::nat)"
        and \<phi>': "\<forall>\<phi>::'v literal multiset. \<phi> \<in> fst \<psi>' \<longrightarrow> \<phi> \<in> fst \<psi>''"
        and I\<chi>': "I \<Turnstile> \<chi>' \<longleftrightarrow> I \<Turnstile> \<chi>2'"
        and tot_imp\<chi>': "\<forall>I'. total_over_m I' {\<chi>'} \<longrightarrow> total_over_m I' {\<chi>2'}"
        using can_decrease_count[of \<chi>' "Pos v" " count \<chi>' (Pos v)" \<psi>' I] by auto

        define C where C: "C = \<chi>2 - {#Neg v#}"

        then have \<chi>2: "\<chi>2 = C + {#Neg v#}" and negC: "Neg v \<notin># C" and posC: "Pos v \<notin># C"
            using \<chi>\<chi>2_incl neg apply auto[]
           using C \<chi>\<chi>2_incl neg count\<chi>2 count_eq_zero_iff apply fastforce
          using C Posv \<chi>\<chi>2_incl in_diffD by fastforce

        obtain C' where
          \<chi>2': "\<chi>2' = C' + {#Pos v#}" and
          posC': "Pos v \<notin># C'" and
          negC': "Neg v \<notin># C'"
          proof -
            assume a1: "\<And>C'. \<lbrakk>\<chi>2' = C' + {#Pos v#}; Pos v \<notin># C'; Neg v \<notin># C'\<rbrakk> \<Longrightarrow> thesis"
            have f2: "\<And>n. (n::nat) - n = 0"
              by simp
            have "Neg v \<notin># \<chi>2' - {#Pos v#}"
              using Negv \<chi>'\<chi>2_incl by (auto simp: not_in_iff)
            have "count {#Pos v#} (Pos v) = 1"
              by simp
            then show ?thesis
              by (metis \<chi>'\<chi>2_incl \<open>Neg v \<notin># \<chi>2' - {#Pos v#}\<close> a1 count\<chi>2' count_diff f2
                insert_DiffM2 less_numeral_extra(3) mem_Collect_eq pos set_mset_def)
          qed

        have "already_used_inv \<psi>'"
          using rtranclp_inference_preserves_already_used_inv[of \<psi> \<psi>'] a_u_i inf by blast
        then have a_u_i_\<psi>'': "already_used_inv \<psi>''"
          using rtranclp_inference_preserves_already_used_inv a_u_i inf' unfolding tautology_def
          by simp

        have totC: "total_over_m I {C}"
          using tot_imp\<chi> tot\<chi> tot_over_m_remove[of I "Pos v" C] negC posC unfolding \<chi>2
          by (metis total_over_m_sum uminus_Neg uminus_of_uminus_id)
        have totC': "total_over_m I {C'}"
          using tot_imp\<chi>' tot\<chi>' total_over_m_sum tot_over_m_remove[of I "Neg v" C'] negC' posC'
          unfolding \<chi>2' by (metis total_over_m_sum uminus_Neg)
        have "\<not> I \<Turnstile> C + C'"
          using \<chi> I\<chi> \<chi>' I\<chi>' unfolding \<chi>2 \<chi>2' true_cls_def by auto
        then have part_I_\<psi>''': "partial_interps Leaf I (fst \<psi>'' \<union> {C + C'})"
          using totC totC' by simp
            (metis \<open>\<not> I \<Turnstile> C + C'\<close> atms_of_ms_singleton total_over_m_def total_over_m_sum)
        {
          assume "({#Pos v#} + C', {#Neg v#} + C) \<notin> snd \<psi>''"
          then have inf'': " inference \<psi>'' (fst \<psi>'' \<union> {C + C'}, snd \<psi>'' \<union> {(\<chi>2', \<chi>2)})"
            using add.commute \<phi>' \<chi>2incl \<open>\<chi>2' \<in> fst \<psi>''\<close>  unfolding \<chi>2 \<chi>2'
            by (metis prod.collapse inference_step resolution)
          have "inference\<^sup>*\<^sup>* \<psi> (fst \<psi>'' \<union> {C + C'}, snd \<psi>'' \<union> {(\<chi>2', \<chi>2)})"
            using inf inf' inf''  rtranclp_trans by auto
          moreover have "sem_tree_size Leaf < sem_tree_size xs" unfolding xs by auto
          ultimately have "?case" using part_I_\<psi>''' by (metis fst_conv)
        }
        moreover {
          assume a: "({#Pos v#} + C', {#Neg v#} + C) \<in> snd \<psi>''"
          then have "(\<exists>\<chi> \<in> fst \<psi>''. (\<forall>I. total_over_m I {C+C'} \<longrightarrow> total_over_m I {\<chi>})
                     \<and> (\<forall>I. total_over_m I {\<chi>} \<longrightarrow> I \<Turnstile> \<chi> \<longrightarrow> I \<Turnstile> C' + C))
                 \<or> tautology (C' + C)"
            proof -
              obtain p where p: "Pos p \<in># ({#Pos v#} + C')" and
              n: "Neg p \<in># ({#Neg v#} + C)" and
              decomp: "((\<exists>\<chi>\<in>fst \<psi>''.
                         (\<forall>I. total_over_m I {({#Pos v#} + C') - {#Pos p#}
                                 + (({#Neg v#} + C) - {#Neg p#})}
                            \<longrightarrow> total_over_m I {\<chi>})
                         \<and> (\<forall>I. total_over_m I {\<chi>} \<longrightarrow> I \<Turnstile> \<chi>
                            \<longrightarrow> I \<Turnstile> ({#Pos v#} + C') - {#Pos p#} + (({#Neg v#} + C) - {#Neg p#}))
                        )
                      \<or> tautology (({#Pos v#} + C') - {#Pos p#} + (({#Neg v#} + C) - {#Neg p#})))"
                using a by (blast intro: allE[OF a_u_i_\<psi>''[unfolded subsumes_def Ball_def],
                    of "({#Pos v#} + C', {#Neg v#} + C)"])
              { assume "p \<noteq> v"
                then have "Pos p \<in># C' \<and> Neg p \<in># C" using p n by force
                then have ?thesis unfolding Bex_def by auto
              }
              moreover {
                assume "p = v"
               then have "?thesis" using decomp by (metis add.commute add_diff_cancel_left')
              }
              ultimately show ?thesis by auto
            qed
          moreover {
            assume "\<exists>\<chi> \<in> fst \<psi>''. (\<forall>I. total_over_m I {C+C'} \<longrightarrow> total_over_m I {\<chi>})
              \<and> (\<forall>I. total_over_m I {\<chi>} \<longrightarrow> I \<Turnstile> \<chi> \<longrightarrow> I \<Turnstile> C' + C)"
            then obtain \<theta> where \<theta>: "\<theta> \<in> fst \<psi>''" and
              tot_\<theta>_CC': "\<forall>I. total_over_m I {C+C'} \<longrightarrow> total_over_m I {\<theta>}" and
              \<theta>_inv: "\<forall>I. total_over_m I {\<theta>} \<longrightarrow> I \<Turnstile> \<theta> \<longrightarrow> I \<Turnstile> C' + C" by blast
            have "partial_interps Leaf I (fst \<psi>'')"
              using tot_\<theta>_CC' \<theta> \<theta>_inv totC totC' \<open>\<not> I \<Turnstile> C + C'\<close> total_over_m_sum by fastforce
            moreover have "sem_tree_size Leaf < sem_tree_size xs" unfolding xs by auto
            ultimately have ?case by (metis inf inf' rtranclp_trans)
          }
          moreover {
            assume tautCC': "tautology (C' + C)"
            have "total_over_m I {C'+C}" using totC totC' total_over_m_sum by auto
            then have "\<not>tautology (C' + C)"
              using \<open>\<not> I \<Turnstile> C + C'\<close> unfolding add.commute[of C C'] total_over_m_def
              unfolding tautology_def by auto
            then have False using tautCC'  unfolding tautology_def by auto
          }
          ultimately have ?case by auto
        }
        ultimately have ?case by auto
      }
      ultimately have ?case using part by (metis (no_types) sem_tree_size.simps(1))
    }
    moreover {
      assume size_ag: "sem_tree_size ag > 0"
      have "sem_tree_size ag < sem_tree_size xs" unfolding xs by auto
      moreover have "partial_interps ag (I \<union> {Pos v}) (fst \<psi>)"
        and partad: "partial_interps ad (I \<union> {Neg v}) (fst \<psi>)"
        using part partial_interps.simps(2) unfolding xs by metis+
      moreover have "sem_tree_size ag < sem_tree_size xs \<longrightarrow> finite (fst \<psi>) \<longrightarrow> already_used_inv \<psi>
        \<longrightarrow> ( partial_interps ag (I \<union> {Pos v}) (fst \<psi>) \<longrightarrow>
        (\<exists>tree' \<psi>'. inference\<^sup>*\<^sup>* \<psi> \<psi>' \<and> partial_interps tree' (I \<union> {Pos v}) (fst \<psi>')
          \<and> (sem_tree_size tree' < sem_tree_size ag \<or> sem_tree_size ag = 0)))"
          using IH by auto
      ultimately obtain \<psi>' :: "'v state" and tree' :: "'v sem_tree" where
        inf: "inference\<^sup>*\<^sup>* \<psi> \<psi>'"
        and part: "partial_interps tree' (I \<union> {Pos v}) (fst \<psi>')"
        and size: "sem_tree_size tree' < sem_tree_size ag \<or> sem_tree_size ag = 0"
        using finite part rtranclp.rtrancl_refl a_u_i by blast

      have "partial_interps ad (I \<union> {Neg v}) (fst \<psi>')"
        using rtranclp_inference_preserve_partial_tree inf partad by metis
      then have "partial_interps (Node v tree' ad) I (fst \<psi>')" using part by auto
      then have ?case using inf size size_ag part unfolding xs by fastforce
    }
    moreover {
      assume size_ad: "sem_tree_size ad > 0"
      have "sem_tree_size ad < sem_tree_size xs" unfolding xs by auto
      moreover have partag: "partial_interps ag (I \<union> {Pos v}) (fst \<psi>)" and
        "partial_interps ad (I \<union> {Neg v}) (fst \<psi>)"
        using part partial_interps.simps(2) unfolding xs by metis+
      moreover have "sem_tree_size ad < sem_tree_size xs \<longrightarrow> finite (fst \<psi>) \<longrightarrow> already_used_inv \<psi>
        \<longrightarrow> ( partial_interps ad (I \<union> {Neg v}) (fst \<psi>)
        \<longrightarrow> (\<exists>tree' \<psi>'. inference\<^sup>*\<^sup>* \<psi> \<psi>' \<and> partial_interps tree' (I \<union> {Neg v}) (fst \<psi>')
            \<and> (sem_tree_size tree' < sem_tree_size ad \<or> sem_tree_size ad = 0)))"
        using IH by auto
      ultimately obtain \<psi>' :: "'v state" and tree' :: "'v sem_tree" where
        inf: "inference\<^sup>*\<^sup>* \<psi> \<psi>'"
        and part: "partial_interps tree' (I \<union> {Neg v}) (fst \<psi>')"
        and size: "sem_tree_size tree' < sem_tree_size ad \<or> sem_tree_size ad = 0"
        using finite part rtranclp.rtrancl_refl a_u_i by blast

      have "partial_interps ag (I \<union> {Pos v}) (fst \<psi>')"
        using rtranclp_inference_preserve_partial_tree inf partag by metis
      then have "partial_interps (Node v ag tree') I (fst \<psi>')" using part by auto
      then have "?case" using inf size size_ad unfolding xs by fastforce
    }
    ultimately have ?case by auto
  }
  ultimately show ?case by auto
qed

lemma inference_completeness_inv:
  fixes \<psi> :: "'v ::linorder state"
  assumes
    unsat: "\<not>satisfiable (fst \<psi>)" and
    finite: "finite (fst \<psi>)" and
    a_u_v: "already_used_inv \<psi>"
  shows "\<exists>\<psi>'. (inference\<^sup>*\<^sup>* \<psi> \<psi>' \<and> {#} \<in> fst \<psi>')"
proof -
  obtain tree where "partial_interps tree {} (fst \<psi>)"
    using partial_interps_build_sem_tree_atms assms by metis
  then show ?thesis
    using unsat finite a_u_v
    proof (induct tree arbitrary: \<psi> rule: sem_tree_size)
      case (bigger tree \<psi>) note H = this
      {
        fix \<chi>
        assume tree: "tree = Leaf"
        obtain \<chi> where \<chi>: "\<not> {} \<Turnstile> \<chi>" and tot\<chi>: "total_over_m {} {\<chi>}" and \<chi>\<psi>: "\<chi> \<in> fst \<psi>"
          using H unfolding tree by auto
        moreover have "{#} = \<chi>"
          using tot\<chi> unfolding total_over_m_def total_over_set_def by fastforce
        moreover have "inference\<^sup>*\<^sup>* \<psi> \<psi>" by auto
        ultimately have ?case by metis
      }
      moreover {
        fix v tree1 tree2
        assume tree: "tree = Node v tree1 tree2"
        obtain
          tree' \<psi>' where inf: "inference\<^sup>*\<^sup>* \<psi> \<psi>'" and
          part': "partial_interps tree' {} (fst \<psi>')" and
          decrease: "sem_tree_size tree' < sem_tree_size tree \<or> sem_tree_size tree = 0"
          using can_decrease_tree_size[of \<psi>] H(2,4,5)  unfolding tautology_def by meson
        have "sem_tree_size tree' < sem_tree_size tree" using decrease unfolding tree by auto
        moreover have "finite (fst \<psi>')" using rtranclp_inference_preserves_finite inf H(4) by metis
        moreover have "unsatisfiable (fst \<psi>')"
          using inference_preserves_unsat inf bigger.prems(2) by blast
        moreover have "already_used_inv \<psi>'"
          using H(5) inf rtranclp_inference_preserves_already_used_inv[of \<psi> \<psi>'] by auto
        ultimately have ?case using inf rtranclp_trans part' H(1) by fastforce
      }
      ultimately show ?case by (cases tree, auto)
   qed
qed

lemma inference_completeness:
  fixes \<psi> :: "'v ::linorder state"
  assumes unsat: "\<not>satisfiable (fst \<psi>)"
  and finite: "finite (fst \<psi>)"
  and "snd \<psi> = {}"
  shows "\<exists>\<psi>'. (rtranclp inference \<psi> \<psi>' \<and> {#} \<in> fst \<psi>')"
proof -
  have "already_used_inv \<psi>" unfolding assms by auto
  then show ?thesis using assms inference_completeness_inv by blast
qed

lemma inference_soundness:
  fixes \<psi> :: "'v ::linorder state"
  assumes "rtranclp inference \<psi> \<psi>'" and "{#} \<in> fst \<psi>'"
  shows "unsatisfiable (fst \<psi>)"
  using assms by (meson rtranclp_inference_preserve_models satisfiable_def true_cls_empty
    true_clss_def)

lemma inference_soundness_and_completeness:
fixes \<psi> :: "'v ::linorder state"
assumes finite: "finite (fst \<psi>)"
and "snd \<psi> = {}"
shows "(\<exists>\<psi>'. (inference\<^sup>*\<^sup>* \<psi> \<psi>' \<and> {#} \<in> fst \<psi>')) \<longleftrightarrow> unsatisfiable (fst \<psi>)"
  using assms inference_completeness inference_soundness by metis

subsection \<open>Lemma about the Simplified State\<close>

abbreviation "simplified \<psi> \<equiv> (no_step simplify \<psi>)"

lemma simplified_count:
  assumes simp: "simplified \<psi>" and \<chi>: "\<chi> \<in> \<psi>"
  shows "count \<chi> L \<le> 1"
proof -
  {
    let ?\<chi>' = "\<chi> - {#L, L#}"
    assume "count \<chi> L \<ge> 2"
    then have f1: "count (\<chi> - {#L, L#} + {#L, L#}) L = count \<chi> L"
      by simp
    then have "L \<in># \<chi> - {#L#}"
      by (metis (no_types) add.left_neutral add_diff_cancel_left' count_union diff_diff_add
        diff_single_trivial insert_DiffM mem_Collect_eq multi_member_this not_gr0 set_mset_def)
    then have \<chi>': "{#L, L#} + ?\<chi>' = \<chi>"
      using f1 in_diffD insert_DiffM by fastforce

    have "\<exists>\<psi>'. simplify \<psi> \<psi>'"
      by (metis (no_types, hide_lams) \<chi> \<chi>' factoring_imp_simplify)
    then have False using simp by auto
  }
  then show ?thesis by arith
qed

lemma simplified_no_both:
  assumes simp: "simplified \<psi>" and \<chi>: "\<chi> \<in> \<psi>"
  shows "\<not> (L \<in># \<chi> \<and> -L \<in># \<chi>)"
proof (rule ccontr)
  assume "\<not> \<not> (L \<in># \<chi> \<and> - L \<in># \<chi>)"
  then have "L \<in># \<chi> \<and> - L \<in># \<chi>" by metis
  then obtain \<chi>' where "\<chi> = add_mset (Pos (atm_of L)) (add_mset (Neg (atm_of L)) \<chi>')"
    by (cases L) (auto dest!: multi_member_split simp: add_eq_conv_ex)
  then show False using \<chi> simp tautology_deletion by fast
qed

lemma add_mset_Neg_Pos_commute[simp]:
  "add_mset (Neg P) (add_mset (Pos P) C) = add_mset (Pos P) (add_mset (Neg P) C)"
  by (rule add_mset_commute)

lemma simplified_not_tautology:
  assumes "simplified {\<psi>}"
  shows "~tautology \<psi>"
proof (rule ccontr)
  assume "~ ?thesis"
  then obtain p where "Pos p \<in># \<psi> \<and> Neg p \<in># \<psi>" using tautology_decomp by metis
  then obtain \<chi> where "\<psi> = \<chi> + {#Pos p#} + {#Neg p#}"
    by (auto dest!: multi_member_split simp: add_eq_conv_ex)
  then have "~ simplified {\<psi>}" by (auto intro: tautology_deletion)
  then show False using assms by auto
qed

lemma simplified_remove:
  assumes "simplified {\<psi>}"
  shows "simplified {\<psi> - {#l#}}"
proof (rule ccontr)
  assume ns: "\<not> simplified {\<psi> - {#l#}}"
  {
    assume "l \<notin># \<psi>"
    then have "\<psi> - {#l#} = \<psi>" by simp
    then have False using ns assms by auto
  }
  moreover {
    assume l\<psi>: "l \<in># \<psi>"
    have A: "\<And>A. A \<in> {\<psi> - {#l#}} \<longleftrightarrow> add_mset l A \<in> {\<psi>}" by (auto simp add: l\<psi>)
    obtain l' where l': "simplify {\<psi> - {#l#}} l'" using ns by metis
    then have "\<exists>l'. simplify {\<psi>} l'"
      proof (induction rule: simplify.induct)
        case (tautology_deletion P A)
        then have "{#Neg P#} + ({#Pos P#} + (A + {#l#})) \<in> {\<psi>}"
          using A by auto
        then show ?thesis
          using simplified_no_both by fastforce
      next
        case (condensation L A)
        have "add_mset l (add_mset L (add_mset L A)) \<in> {\<psi>}"
          using condensation.hyps unfolding A by blast
        then have "{#L, L#} + (A + {#l#}) \<in> {\<psi>}"
          by auto
        then show ?case
          using factoring_imp_simplify by blast
      next
        case (subsumption A B)
        then show ?case by blast
      qed
    then have False using assms(1) by blast
  }
  ultimately show False by auto
qed


lemma in_simplified_simplified:
  assumes simp: "simplified \<psi>" and incl: "\<psi>' \<subseteq> \<psi>"
  shows "simplified \<psi>'"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain \<psi>'' where "simplify \<psi>' \<psi>''" by metis
    then have "\<exists>l'. simplify \<psi> l'"
      proof (induction rule: simplify.induct)
        case (tautology_deletion A P)
        then show ?thesis using simplify.tautology_deletion[of "A" P "\<psi>"] incl by blast
      next
        case (condensation A L)
        then show ?case using simplify.condensation[of A L "\<psi>"] incl by blast
      next
        case (subsumption A B)
        then show ?case using simplify.subsumption[of A "\<psi>" B] incl by auto
      qed
  then show False using assms(1) by blast
qed

lemma simplified_in:
  assumes "simplified \<psi>"
  and "N \<in> \<psi>"
  shows "simplified {N}"
  using assms by (metis Set.set_insert empty_subsetI in_simplified_simplified insert_mono)

lemma subsumes_imp_formula:
  assumes "\<psi> \<le># \<phi>"
  shows "{\<psi>} \<Turnstile>p \<phi>"
  unfolding true_clss_cls_def apply auto
  using assms true_cls_mono_leD by blast

lemma simplified_imp_distinct_mset_tauto:
  assumes simp: "simplified \<psi>'"
  shows "distinct_mset_set \<psi>'" and "\<forall>\<chi> \<in> \<psi>'. \<not>tautology \<chi>"
proof -
  show "\<forall>\<chi> \<in> \<psi>'. \<not>tautology \<chi>"
    using simp by (auto simp add: simplified_in simplified_not_tautology)

  show "distinct_mset_set \<psi>'"
    proof (rule ccontr)
      assume "\<not>?thesis"
      then obtain \<chi> where "\<chi> \<in> \<psi>'" and "\<not>distinct_mset \<chi>" unfolding distinct_mset_set_def by auto
      then obtain L where "count \<chi> L \<ge> 2"
        unfolding distinct_mset_def
        by (meson count_greater_eq_one_iff le_antisym simp simplified_count)
      then show False by (metis Suc_1 \<open>\<chi> \<in> \<psi>'\<close> not_less_eq_eq simp simplified_count)
    qed
qed

lemma simplified_no_more_full1_simplified:
  assumes "simplified \<psi>"
  shows "\<not>full1 simplify \<psi> \<psi>'"
  using assms unfolding full1_def by (meson tranclpD)


subsection \<open>Resolution and Invariants\<close>

inductive resolution :: "'v state \<Rightarrow> 'v state \<Rightarrow> bool" where
full1_simp: "full1 simplify N N' \<Longrightarrow> resolution (N, already_used) (N', already_used)" |
inferring: "inference (N, already_used) (N', already_used') \<Longrightarrow> simplified N
  \<Longrightarrow> full simplify N' N'' \<Longrightarrow> resolution (N, already_used) (N'', already_used')"

subsubsection \<open>Invariants\<close>

lemma resolution_finite:
  assumes "resolution \<psi> \<psi>'" and "finite (fst \<psi>)"
  shows "finite (fst \<psi>')"
  using assms by (induct rule: resolution.induct)
    (auto simp add: full1_def full_def rtranclp_simplify_preserves_finite
      dest: tranclp_into_rtranclp inference_preserves_finite)

lemma rtranclp_resolution_finite:
  assumes "resolution\<^sup>*\<^sup>* \<psi> \<psi>'" and "finite (fst \<psi>)"
  shows "finite (fst \<psi>')"
  using assms by (induct rule: rtranclp_induct, auto simp add: resolution_finite)

lemma resolution_finite_snd:
  assumes "resolution \<psi> \<psi>'" and "finite (snd \<psi>)"
  shows "finite (snd \<psi>')"
  using assms apply (induct rule: resolution.induct, auto simp add: inference_preserves_finite_snd)
  using inference_preserves_finite_snd snd_conv by metis

lemma rtranclp_resolution_finite_snd:
  assumes "resolution\<^sup>*\<^sup>* \<psi> \<psi>'" and "finite (snd \<psi>)"
  shows "finite (snd \<psi>')"
  using assms by (induct rule: rtranclp_induct, auto simp add: resolution_finite_snd)

lemma resolution_always_simplified:
 assumes "resolution \<psi> \<psi>'"
 shows "simplified (fst \<psi>')"
 using assms by (induct rule: resolution.induct)
   (auto simp add: full1_def full_def)

lemma tranclp_resolution_always_simplified:
  assumes "tranclp resolution \<psi> \<psi>'"
  shows "simplified (fst \<psi>')"
  using assms by (induct rule: tranclp.induct, auto simp add: resolution_always_simplified)

lemma resolution_atms_of:
  assumes "resolution \<psi> \<psi>'" and "finite (fst \<psi>)"
  shows "atms_of_ms (fst \<psi>') \<subseteq> atms_of_ms (fst \<psi>)"
  using assms apply (induct rule: resolution.induct)
    apply(simp add: rtranclp_simplify_atms_of_ms tranclp_into_rtranclp full1_def )
  by (metis (no_types, lifting) contra_subsetD fst_conv full_def
    inference_preserves_atms_of_ms rtranclp_simplify_atms_of_ms subsetI)

lemma rtranclp_resolution_atms_of:
  assumes "resolution\<^sup>*\<^sup>* \<psi> \<psi>'" and "finite (fst \<psi>)"
  shows "atms_of_ms (fst \<psi>') \<subseteq> atms_of_ms (fst \<psi>)"
  using assms apply (induct rule: rtranclp_induct)
  using resolution_atms_of rtranclp_resolution_finite by blast+

lemma resolution_include:
  assumes res: "resolution \<psi> \<psi>'" and finite: "finite (fst \<psi>)"
  shows "fst \<psi>' \<subseteq> simple_clss (atms_of_ms (fst \<psi>))"
proof -
  have finite': "finite (fst \<psi>')" using local.finite res resolution_finite by blast
  have "simplified (fst \<psi>')" using res finite' resolution_always_simplified by blast
  then have "fst \<psi>' \<subseteq> simple_clss (atms_of_ms (fst \<psi>'))"
    using simplified_in_simple_clss finite' simplified_imp_distinct_mset_tauto[of "fst \<psi>'"] by auto
  moreover have "atms_of_ms (fst \<psi>') \<subseteq> atms_of_ms (fst \<psi>)"
    using res finite resolution_atms_of[of \<psi> \<psi>'] by auto
  ultimately show ?thesis by (meson atms_of_ms_finite local.finite order.trans rev_finite_subset
    simple_clss_mono)
qed

lemma rtranclp_resolution_include:
  assumes res: "tranclp resolution \<psi> \<psi>'" and finite: "finite (fst \<psi>)"
  shows "fst \<psi>' \<subseteq> simple_clss (atms_of_ms (fst \<psi>))"
  using assms apply (induct rule: tranclp.induct)
    apply (simp add: resolution_include)
  by (meson simple_clss_mono order_trans resolution_include
    rtranclp_resolution_atms_of rtranclp_resolution_finite tranclp_into_rtranclp)

abbreviation already_used_all_simple
  :: "('a literal multiset \<times> 'a literal multiset) set \<Rightarrow> 'a set \<Rightarrow> bool" where
"already_used_all_simple already_used vars \<equiv>
(\<forall> (A, B) \<in> already_used. simplified {A} \<and> simplified {B} \<and> atms_of A \<subseteq> vars \<and> atms_of B \<subseteq> vars)"

lemma already_used_all_simple_vars_incl:
  assumes "vars \<subseteq> vars'"
  shows "already_used_all_simple a vars \<Longrightarrow> already_used_all_simple a vars'"
  using assms by fast

lemma inference_clause_preserves_already_used_all_simple:
  assumes "inference_clause S S'"
  and "already_used_all_simple (snd S) vars"
  and "simplified (fst S)"
  and "atms_of_ms (fst S) \<subseteq> vars"
  shows "already_used_all_simple (snd (fst S \<union> {fst S'}, snd S')) vars"
  using assms
proof (induct rule: inference_clause.induct)
  case (factoring L C N already_used)
  then show ?case by (simp add: simplified_in factoring_imp_simplify)
next
  case (resolution P C N D already_used) note H = this
  show ?case apply clarify
    proof -
      fix A B v
      assume "(A, B) \<in> snd (fst (N, already_used)
        \<union> {fst (C + D, already_used \<union> {({#Pos P#} + C, {#Neg P#} + D)})},
           snd (C + D, already_used \<union> {({#Pos P#} + C, {#Neg P#} + D)}))"
      then have "(A, B) \<in> already_used \<or> (A, B) = ({#Pos P#} + C, {#Neg P#} + D)" by auto
      moreover {
        assume "(A, B) \<in> already_used"
        then have "simplified {A} \<and> simplified {B} \<and> atms_of A \<subseteq> vars \<and> atms_of B \<subseteq> vars"
          using H(4) by auto
      }
      moreover {
        assume eq: "(A, B) = ({#Pos P#} + C, {#Neg P#} + D)"
        then have "simplified {A}" using simplified_in H(1,5) by auto
        moreover have "simplified {B}" using eq simplified_in H(2,5) by auto
        moreover have "atms_of A \<subseteq> atms_of_ms N"
          using eq H(1)
          using atms_of_atms_of_ms_mono[of A N] by auto
        moreover have "atms_of B \<subseteq> atms_of_ms N"
          using eq H(2) atms_of_atms_of_ms_mono[of B N] by auto
        ultimately have "simplified {A} \<and> simplified {B} \<and> atms_of A \<subseteq> vars \<and> atms_of B \<subseteq> vars"
          using H(6) by auto
      }
      ultimately show "simplified {A} \<and> simplified {B} \<and> atms_of A \<subseteq> vars \<and> atms_of B \<subseteq> vars"
        by fast
    qed
qed

lemma inference_preserves_already_used_all_simple:
  assumes "inference S S'"
  and "already_used_all_simple (snd S) vars"
  and "simplified (fst S)"
  and "atms_of_ms (fst S) \<subseteq> vars"
  shows "already_used_all_simple (snd S') vars"
  using assms
proof (induct rule: inference.induct)
  case (inference_step S clause already_used)
  then show ?case
    using inference_clause_preserves_already_used_all_simple[of S "(clause, already_used)" vars]
    by auto
qed

lemma already_used_all_simple_inv:
  assumes "resolution S S'"
  and "already_used_all_simple (snd S) vars"
  and "atms_of_ms (fst S) \<subseteq> vars"
  shows "already_used_all_simple (snd S') vars"
  using assms
proof (induct rule: resolution.induct)
  case (full1_simp N N')
  then show ?case by simp
next
  case (inferring N already_used N' already_used' N'')
  then show "already_used_all_simple (snd (N'', already_used')) vars"
    using inference_preserves_already_used_all_simple[of "(N, already_used)"] by simp
qed

lemma rtranclp_already_used_all_simple_inv:
  assumes "resolution\<^sup>*\<^sup>* S S'"
  and "already_used_all_simple (snd S) vars"
  and "atms_of_ms (fst S) \<subseteq> vars"
  and "finite (fst S)"
  shows "already_used_all_simple (snd S') vars"
  using assms
proof (induct rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step S' S'') note infstar = this(1) and IH = this(3) and res = this(2) and
    already = this(4) and atms = this(5) and finite = this(6)
  have "already_used_all_simple (snd S') vars" using IH already atms finite by simp
  moreover have "atms_of_ms (fst S') \<subseteq> atms_of_ms (fst S)"
    by (simp add: infstar local.finite rtranclp_resolution_atms_of)
  then have "atms_of_ms (fst S') \<subseteq> vars" using atms by auto
  ultimately show ?case
    using already_used_all_simple_inv[OF res] by simp
qed

lemma inference_clause_simplified_already_used_subset:
  assumes "inference_clause S S'"
  and "simplified (fst S)"
  shows "snd S \<subset> snd S'"
  using assms apply (induct rule: inference_clause.induct)
   using factoring_imp_simplify apply (simp; blast)
  using factoring_imp_simplify by force

lemma inference_simplified_already_used_subset:
  assumes "inference S S'"
  and "simplified (fst S)"
  shows "snd S \<subset> snd S'"
  using assms apply (induct rule: inference.induct)
  by (metis inference_clause_simplified_already_used_subset snd_conv)

lemma resolution_simplified_already_used_subset:
  assumes "resolution S S'"
  and "simplified (fst S)"
  shows "snd S \<subset> snd S'"
  using assms apply (induct rule: resolution.induct, simp_all add: full1_def)
  apply (meson tranclpD)
  by (metis inference_simplified_already_used_subset fst_conv snd_conv)

lemma tranclp_resolution_simplified_already_used_subset:
  assumes "tranclp resolution S S'"
  and "simplified (fst S)"
  shows "snd S \<subset> snd S'"
  using assms apply (induct rule: tranclp.induct)
  using resolution_simplified_already_used_subset apply metis
  by (meson tranclp_resolution_always_simplified resolution_simplified_already_used_subset
    less_trans)

abbreviation "already_used_top vars \<equiv> simple_clss vars \<times> simple_clss vars"

lemma already_used_all_simple_in_already_used_top:
  assumes "already_used_all_simple s vars" and "finite vars"
  shows "s \<subseteq> already_used_top vars"
proof
  fix x
  assume x_s: "x \<in> s"
  obtain A B where x: "x = (A, B)" by (cases x, auto)
  then have "simplified {A}" and "atms_of A \<subseteq> vars" using assms(1) x_s by fastforce+
  then have A: "A \<in> simple_clss vars"
    using simple_clss_mono[of "atms_of A" vars] x assms(2)
    simplified_imp_distinct_mset_tauto[of "{A}"]
    distinct_mset_not_tautology_implies_in_simple_clss by fast
  moreover have "simplified {B}" and "atms_of B \<subseteq> vars" using assms(1) x_s x by fast+
  then have B: "B \<in> simple_clss vars"
    using simplified_imp_distinct_mset_tauto[of "{B}"]
    distinct_mset_not_tautology_implies_in_simple_clss
    simple_clss_mono[of "atms_of B" vars] x assms(2) by fast
  ultimately show "x \<in> simple_clss vars \<times> simple_clss vars"
    unfolding x by auto
qed

lemma already_used_top_finite:
  assumes "finite vars"
  shows "finite (already_used_top vars)"
  using simple_clss_finite assms by auto

lemma already_used_top_increasing:
  assumes "var \<subseteq> var'" and "finite var'"
  shows "already_used_top var \<subseteq> already_used_top var'"
  using assms simple_clss_mono by auto

lemma already_used_all_simple_finite:
  fixes s :: "('a literal multiset \<times> 'a literal multiset) set" and vars :: "'a set"
  assumes "already_used_all_simple s vars" and "finite vars"
  shows "finite s"
  using assms already_used_all_simple_in_already_used_top[OF assms(1)]
  rev_finite_subset[OF already_used_top_finite[of vars]] by auto

abbreviation "card_simple vars \<psi> \<equiv> card (already_used_top vars - \<psi>)"

lemma resolution_card_simple_decreasing:
  assumes res: "resolution \<psi> \<psi>'"
  and a_u_s: "already_used_all_simple (snd \<psi>) vars"
  and finite_v: "finite vars"
  and finite_fst: "finite (fst \<psi>)"
  and finite_snd: "finite (snd \<psi>)"
  and simp: "simplified (fst \<psi>)"
  and "atms_of_ms (fst \<psi>) \<subseteq> vars"
  shows "card_simple vars (snd \<psi>') < card_simple vars (snd \<psi>)"
proof -
  let ?vars = "vars"
  let ?top = "simple_clss ?vars \<times> simple_clss ?vars"
  have 1: "card_simple vars (snd \<psi>) = card ?top - card (snd \<psi>)"
    using card_Diff_subset finite_snd already_used_all_simple_in_already_used_top[OF a_u_s]
    finite_v by metis
  have a_u_s': "already_used_all_simple (snd \<psi>') vars"
    using already_used_all_simple_inv res a_u_s assms(7) by blast
  have f: "finite (snd \<psi>')" using already_used_all_simple_finite a_u_s' finite_v by auto
  have 2: "card_simple vars (snd \<psi>') = card ?top - card (snd \<psi>')"
    using card_Diff_subset[OF f] already_used_all_simple_in_already_used_top[OF a_u_s' finite_v]
    by auto
  have "card (already_used_top vars) \<ge> card (snd \<psi>')"
    using already_used_all_simple_in_already_used_top[OF a_u_s' finite_v]
    card_mono[of "already_used_top vars" "snd \<psi>'"] already_used_top_finite[OF finite_v] by metis
  then show ?thesis
    using psubset_card_mono[OF f resolution_simplified_already_used_subset[OF res simp]]
    unfolding 1 2 by linarith
qed


lemma tranclp_resolution_card_simple_decreasing:
  assumes "tranclp resolution \<psi> \<psi>'" and finite_fst: "finite (fst \<psi>)"
  and "already_used_all_simple (snd \<psi>) vars"
  and "atms_of_ms (fst \<psi>) \<subseteq> vars"
  and finite_v: "finite vars"
  and finite_snd: "finite (snd \<psi>)"
  and "simplified (fst \<psi>)"
  shows "card_simple vars (snd \<psi>') < card_simple vars (snd \<psi>)"
  using assms
proof (induct rule: tranclp_induct)
  case (base \<psi>')
  then show ?case by (simp add: resolution_card_simple_decreasing)
next
  case (step \<psi>' \<psi>'') note res = this(1) and res' = this(2) and a_u_s = this(5) and
    atms = this(6) and f_v = this(7) and f_fst = this(4) and H = this
  then have "card_simple vars (snd \<psi>') < card_simple vars (snd \<psi>)" by auto
  moreover have a_u_s': "already_used_all_simple (snd \<psi>') vars"
    using rtranclp_already_used_all_simple_inv[OF tranclp_into_rtranclp[OF res] a_u_s atms f_fst] .
  have "finite (fst \<psi>')"
    by (meson finite_fst res rtranclp_resolution_finite tranclp_into_rtranclp)
  moreover have "finite (snd \<psi>')" using already_used_all_simple_finite[OF a_u_s' f_v] .
  moreover have "simplified (fst \<psi>')" using res tranclp_resolution_always_simplified by blast
  moreover have "atms_of_ms (fst \<psi>') \<subseteq> vars"
    by (meson atms f_fst order.trans res rtranclp_resolution_atms_of tranclp_into_rtranclp)
  ultimately show ?case
    using resolution_card_simple_decreasing[OF res' a_u_s' f_v] f_v
    less_trans[of "card_simple vars (snd \<psi>'')" "card_simple vars (snd \<psi>')"
      "card_simple vars (snd \<psi>)"]
    by blast
qed


lemma tranclp_resolution_card_simple_decreasing_2:
  assumes "tranclp resolution \<psi> \<psi>'"
  and finite_fst: "finite (fst \<psi>)"
  and empty_snd: "snd \<psi> = {}"
  and "simplified (fst \<psi>)"
  shows "card_simple (atms_of_ms (fst \<psi>)) (snd \<psi>') < card_simple (atms_of_ms (fst \<psi>)) (snd \<psi>)"
proof -
  let ?vars = "atms_of_ms (fst \<psi>)"
  have "already_used_all_simple (snd \<psi>) ?vars" unfolding empty_snd by auto
  moreover have "atms_of_ms (fst \<psi>) \<subseteq> ?vars" by auto
  moreover have finite_v: "finite ?vars" using finite_fst by auto
  moreover have finite_snd: "finite (snd \<psi>)" unfolding empty_snd by auto
  ultimately show ?thesis
    using assms(1,2,4) tranclp_resolution_card_simple_decreasing[of \<psi> \<psi>'] by presburger
qed


subsubsection \<open>Well-Foundness of the Relation\<close>

lemma wf_simplified_resolution:
  assumes f_vars: "finite vars"
  shows "wf {(y:: 'v:: linorder state, x). (atms_of_ms (fst x) \<subseteq> vars \<and> simplified (fst x)
    \<and> finite (snd x) \<and> finite (fst x) \<and> already_used_all_simple (snd x) vars) \<and> resolution x y}"
proof -
  {
    fix a b :: "'v::linorder state"
    assume "(b, a) \<in> {(y, x). (atms_of_ms (fst x) \<subseteq> vars \<and> simplified (fst x) \<and> finite (snd x)
      \<and> finite (fst x) \<and> already_used_all_simple (snd x) vars) \<and> resolution x y}"
    then have
      "atms_of_ms (fst a) \<subseteq> vars" and
      simp: "simplified (fst a)" and
      "finite (snd a)" and
      "finite (fst a)" and
      a_u_v: "already_used_all_simple (snd a) vars" and
      res: "resolution a b" by auto
    have "finite (already_used_top vars)" using f_vars already_used_top_finite by blast
    moreover have "already_used_top vars \<subseteq> already_used_top vars" by auto
    moreover have "snd b \<subseteq> already_used_top vars"
      using already_used_all_simple_in_already_used_top[of "snd b" vars]
      a_u_v already_used_all_simple_inv[OF res] \<open>finite (fst a)\<close> \<open>atms_of_ms (fst a) \<subseteq> vars\<close> f_vars
      by presburger
    moreover have "snd a \<subset> snd b" using resolution_simplified_already_used_subset[OF res simp] .
    ultimately have "finite (already_used_top vars) \<and> already_used_top vars \<subseteq> already_used_top vars
      \<and> snd b \<subseteq> already_used_top vars \<and> snd a \<subset> snd b" by metis
  }
  then show ?thesis using wf_bounded_set[of "{(y:: 'v:: linorder state, x).
    (atms_of_ms (fst x) \<subseteq> vars
    \<and> simplified (fst x) \<and> finite (snd x) \<and> finite (fst x)\<and> already_used_all_simple (snd x) vars)
    \<and> resolution x y}" "\<lambda>_. already_used_top vars" "snd"] by auto
qed

lemma wf_simplified_resolution':
  assumes f_vars: "finite vars"
  shows "wf {(y:: 'v:: linorder state, x). (atms_of_ms (fst x) \<subseteq> vars \<and> \<not>simplified (fst x)
    \<and> finite (snd x) \<and> finite (fst x) \<and> already_used_all_simple (snd x) vars) \<and> resolution x y}"
  unfolding wf_def
   apply (simp add: resolution_always_simplified)
  by (metis (mono_tags, hide_lams) fst_conv resolution_always_simplified)

lemma wf_resolution:
  assumes f_vars: "finite vars"
  shows "wf ({(y:: 'v:: linorder state, x). (atms_of_ms (fst x) \<subseteq> vars \<and> simplified (fst x)
        \<and> finite (snd x) \<and> finite (fst x) \<and> already_used_all_simple (snd x) vars) \<and> resolution x y}
    \<union> {(y, x). (atms_of_ms (fst x) \<subseteq> vars \<and> \<not> simplified (fst x) \<and> finite (snd x) \<and> finite (fst x)
       \<and> already_used_all_simple (snd x) vars) \<and> resolution x y})" (is "wf (?R \<union> ?S)")
proof -
  have "Domain ?R Int Range ?S = {}" using resolution_always_simplified by auto blast
  then show "wf (?R \<union> ?S)"
    using wf_simplified_resolution[OF f_vars] wf_simplified_resolution'[OF f_vars] wf_Un[of ?R ?S]
    by fast
qed

lemma rtrancp_simplify_already_used_inv:
  assumes "simplify\<^sup>*\<^sup>* S S'"
  and "already_used_inv (S, N)"
  shows "already_used_inv (S', N)"
  using assms apply induction
  using simplify_preserves_already_used_inv by fast+

lemma full1_simplify_already_used_inv:
  assumes "full1 simplify S S'"
  and "already_used_inv (S, N)"
  shows "already_used_inv (S', N)"
  using assms tranclp_into_rtranclp[of simplify S S'] rtrancp_simplify_already_used_inv
  unfolding full1_def by fast

lemma full_simplify_already_used_inv:
  assumes "full simplify S S'"
  and "already_used_inv (S, N)"
  shows "already_used_inv (S', N)"
  using assms rtrancp_simplify_already_used_inv unfolding full_def by fast
lemma resolution_already_used_inv:
  assumes "resolution S S'"
  and "already_used_inv S"
  shows "already_used_inv S'"
  using assms
proof induction
  case (full1_simp N N' already_used)
  then show ?case using full1_simplify_already_used_inv by fast
next
  case (inferring N already_used N' already_used' N''') note inf = this(1) and full = this(3) and
    a_u_v = this(4)
  then show ?case
    using inference_preserves_already_used_inv[OF inf a_u_v] full_simplify_already_used_inv full
    by fast
qed

lemma rtranclp_resolution_already_used_inv:
  assumes "resolution\<^sup>*\<^sup>* S S'"
  and "already_used_inv S"
  shows "already_used_inv S'"
  using assms apply induction
  using resolution_already_used_inv by fast+

lemma rtanclp_simplify_preserves_unsat:
  assumes "simplify\<^sup>*\<^sup>* \<psi> \<psi>'"
  shows "satisfiable \<psi>' \<longrightarrow> satisfiable \<psi>"
  using assms apply induction
  using simplify_clause_preserves_sat by blast+

lemma full1_simplify_preserves_unsat:
  assumes "full1 simplify \<psi> \<psi>'"
  shows "satisfiable \<psi>' \<longrightarrow> satisfiable \<psi>"
  using assms rtanclp_simplify_preserves_unsat[of \<psi> \<psi>'] tranclp_into_rtranclp
  unfolding full1_def by metis

lemma full_simplify_preserves_unsat:
  assumes "full simplify \<psi> \<psi>'"
  shows "satisfiable \<psi>' \<longrightarrow> satisfiable \<psi>"
  using assms rtanclp_simplify_preserves_unsat[of \<psi> \<psi>'] unfolding full_def by metis

lemma resolution_preserves_unsat:
  assumes "resolution \<psi> \<psi>'"
  shows "satisfiable (fst \<psi>') \<longrightarrow> satisfiable (fst \<psi>)"
  using assms apply (induct rule: resolution.induct)
  using full1_simplify_preserves_unsat apply (metis fst_conv)
  using full_simplify_preserves_unsat simplify_preserves_unsat by fastforce

lemma rtranclp_resolution_preserves_unsat:
  assumes "resolution\<^sup>*\<^sup>* \<psi> \<psi>'"
  shows "satisfiable (fst \<psi>') \<longrightarrow> satisfiable (fst \<psi>)"
  using assms apply induction
  using resolution_preserves_unsat by fast+

lemma rtranclp_simplify_preserve_partial_tree:
  assumes "simplify\<^sup>*\<^sup>* N N'"
  and "partial_interps t I N"
  shows "partial_interps t I N'"
  using assms apply (induction, simp)
  using simplify_preserve_partial_tree by metis

lemma full1_simplify_preserve_partial_tree:
  assumes "full1 simplify N N'"
  and "partial_interps t I N"
  shows "partial_interps t I N'"
  using assms rtranclp_simplify_preserve_partial_tree[of N N' t I] tranclp_into_rtranclp
  unfolding full1_def by fast

lemma full_simplify_preserve_partial_tree:
  assumes "full simplify N N'"
  and "partial_interps t I N"
  shows "partial_interps t I N'"
  using assms rtranclp_simplify_preserve_partial_tree[of N N' t I] tranclp_into_rtranclp
  unfolding full_def by fast

lemma resolution_preserve_partial_tree:
  assumes "resolution S S'"
  and "partial_interps t I (fst S)"
  shows "partial_interps t I (fst S')"
  using assms apply induction
    using full1_simplify_preserve_partial_tree fst_conv apply metis
  using full_simplify_preserve_partial_tree inference_preserve_partial_tree by fastforce

lemma rtranclp_resolution_preserve_partial_tree:
  assumes "resolution\<^sup>*\<^sup>* S S'"
  and "partial_interps t I (fst S)"
  shows "partial_interps t I (fst S')"
  using assms apply induction
  using resolution_preserve_partial_tree by fast+
  thm nat_less_induct nat.induct

lemma nat_ge_induct[case_names 0 Suc]:
  assumes "P 0"
  and "\<And>n. (\<And>m. m<Suc n \<Longrightarrow> P m) \<Longrightarrow> P (Suc n)"
  shows "P n"
  using assms apply (induct rule: nat_less_induct)
  by (rename_tac n, case_tac n) auto

lemma wf_always_more_step_False:
  assumes "wf R"
  shows "(\<forall>x. \<exists>z. (z, x)\<in>R) \<Longrightarrow> False"
 using assms unfolding wf_def by (meson Domain.DomainI assms wfE_min)

lemma finite_finite_mset_element_of_mset[simp]:
  assumes "finite N"
  shows "finite {f \<phi> L |\<phi> L. \<phi> \<in> N \<and> L \<in># \<phi> \<and> P \<phi> L}"
  using assms
proof (induction N rule: finite_induct)
  case empty
  show ?case by auto
next
  case (insert x N) note finite = this(1) and IH = this(3)
  have "{f \<phi> L |\<phi> L. (\<phi> = x \<or> \<phi> \<in> N) \<and> L \<in># \<phi> \<and> P \<phi> L} \<subseteq> {f x L | L. L \<in># x \<and> P x L}
    \<union> {f \<phi> L |\<phi> L. \<phi> \<in> N \<and> L \<in># \<phi> \<and> P \<phi> L}" by auto
  moreover have "finite {f x L | L. L \<in># x}" by auto
  ultimately show ?case using IH finite_subset by fastforce
qed


definition sum_count_ge_2 :: "'a multiset set \<Rightarrow> nat" ("\<Xi>") where
"sum_count_ge_2 \<equiv> folding.F (\<lambda>\<phi>. (+)(sum_mset {#count \<phi> L |L \<in># \<phi>. 2 \<le> count \<phi> L#})) 0"


interpretation sum_count_ge_2:
  folding "\<lambda>\<phi>. (+)(sum_mset {#count \<phi> L |L \<in># \<phi>. 2 \<le> count \<phi> L#})" 0
rewrites
  "folding.F (\<lambda>\<phi>. (+)(sum_mset {#count \<phi> L |L \<in># \<phi>. 2 \<le> count \<phi> L#})) 0 = sum_count_ge_2"
proof -
  show "folding (\<lambda>\<phi>. (+) (sum_mset (image_mset (count \<phi>) {# L \<in># \<phi>. 2 \<le> count \<phi> L#})))"
    by standard auto
  then interpret sum_count_ge_2:
    folding "\<lambda>\<phi>. (+)(sum_mset {#count \<phi> L |L \<in># \<phi>. 2 \<le> count \<phi> L#})" 0 .
  show "folding.F (\<lambda>\<phi>. (+) (sum_mset (image_mset (count \<phi>) {# L \<in># \<phi>. 2 \<le> count \<phi> L#}))) 0
    = sum_count_ge_2" by (auto simp add: sum_count_ge_2_def)
qed

lemma finite_incl_le_setsum:
 "finite (B::'a multiset set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> \<Xi> A \<le> \<Xi> B"
proof (induction arbitrary:A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a F) note finite = this(1) and aF = this(2) and IH = this(3) and AF = this(4)
  show ?case
    proof (cases "a \<in> A")
      assume "a \<notin> A"
      then have "A \<subseteq> F" using AF by auto
      then show ?case using IH[of A] by (simp add: aF local.finite)
    next
      assume aA: "a \<in> A"
      then have "A - {a} \<subseteq> F" using AF by auto
      then have "\<Xi> (A - {a}) \<le> \<Xi> F" using IH by blast
      then show ?case
         proof -
           obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
             "\<forall>x0 x1. (\<exists>v2. x0 = x1 + v2) = (x0 = x1 + nn x0 x1)"
             by moura
           then have "\<Xi> F = \<Xi> (A - {a}) + nn (\<Xi> F) (\<Xi> (A - {a}))"
             by (meson \<open>\<Xi> (A - {a}) \<le> \<Xi> F\<close> le_iff_add)
           then show ?thesis
             by (metis (no_types) le_iff_add aA aF add.assoc finite.insertI finite_subset
               insert.prems local.finite sum_count_ge_2.insert sum_count_ge_2.remove)
         qed
    qed
qed

lemma simplify_finite_measure_decrease:
  "simplify N N' \<Longrightarrow> finite N \<Longrightarrow> card N' + \<Xi> N' < card N + \<Xi> N"
proof (induction rule: simplify.induct)
  case (tautology_deletion P A) note an = this(1) and fin = this(2)
  let ?N' = "N - {add_mset (Pos P) (add_mset (Neg P) A)}"
  have "card ?N' < card N"
    by (meson card_Diff1_less tautology_deletion.hyps tautology_deletion.prems)
  moreover have "?N' \<subseteq> N" by auto
  then have "sum_count_ge_2 ?N' \<le> sum_count_ge_2 N" using finite_incl_le_setsum[OF fin] by blast
  ultimately show ?case by linarith
next
  case (condensation L A) note AN = this(1) and fin = this(2)
  let ?C' = "add_mset L A"
  let ?C = "add_mset L ?C'"
  let ?N' = "N - {?C} \<union> {?C'}"
  have "card ?N' \<le> card N"
    using AN by (metis (no_types, lifting) Diff_subset Un_empty_right Un_insert_right card.remove
      card_insert_if card_mono fin finite_Diff order_refl)
  moreover have "\<Xi> {?C'} < \<Xi> {?C}"
  proof -
    have mset_decomp:
      "{# La \<in># A. (L = La \<longrightarrow> La \<in># A) \<and> (L \<noteq> La \<longrightarrow> 2 \<le> count A La)#}
        =  {# La \<in># A. L \<noteq> La \<and> 2 \<le> count A La#} +
          {# La \<in># A. L = La \<and> Suc 0 \<le> count A L#}"
      by (auto simp: multiset_eq_iff ac_simps)
    have mset_decomp2: "{# La \<in># A. L \<noteq> La \<longrightarrow> 2 \<le> count A La#} =
        {# La \<in># A. L \<noteq> La \<and> 2 \<le> count A La#} + replicate_mset (count A L) L"
      by (auto simp: multiset_eq_iff)
    have *: "(\<Sum>x\<in>#B. if L = x then Suc (count A x) else count A x) \<le>
        (\<Sum>x\<in>#B. if L = x then Suc (count (add_mset L A) x) else count (add_mset L A) x)"
      for B
      by (auto intro!: sum_mset_mono)
    show ?thesis
      using *[of "{#La \<in># A. L \<noteq> La \<and> 2 \<le> count A La#}"]
      by (auto simp: mset_decomp mset_decomp2 filter_mset_eq)
  qed
  have "\<Xi> ?N' < \<Xi> N"
    proof cases
      assume a1: "?C' \<in> N"
      then show ?thesis
        proof -
          have f2: "\<And>m M. insert (m::'a literal multiset) (M - {m}) = M \<union> {} \<or> m \<notin> M"
            using Un_empty_right insert_Diff by blast
          have f3: "\<And>m M Ma. insert (m::'a literal multiset) M - insert m Ma = M - insert m Ma"
            by simp
          then have f4: "\<And>M m. M - {m::'a literal multiset} = M \<union> {} \<or> m \<in> M"
            using Diff_insert_absorb Un_empty_right by fastforce
          have f5: "insert ?C N = N"
            using f3 f2 Un_empty_right condensation.hyps insert_iff by fastforce
          have "\<And>m M. insert (m::'a literal multiset) M = M \<union> {} \<or> m \<notin> M"
            using f3 f2 Un_empty_right add.right_neutral insert_iff by fastforce
          then have "\<Xi> (N - {?C}) < \<Xi> N"
            using f5 f4 by (metis Un_empty_right \<open>\<Xi> {?C'} < \<Xi> {?C}\<close>
              add.right_neutral add_diff_cancel_left' add_gr_0 diff_less fin finite.emptyI not_le
              sum_count_ge_2.empty sum_count_ge_2.insert_remove trans_le_add2)
          then show ?thesis
            using f3 f2 a1 by (metis (no_types) Un_empty_right Un_insert_right condensation.hyps
              insert_iff multi_self_add_other_not_self)
        qed
    next
      assume "?C' \<notin> N"
      have mset_decomp:
        "{# La \<in># A. (L = La \<longrightarrow> Suc 0 \<le> count A La) \<and> (L \<noteq> La \<longrightarrow> 2 \<le> count A La)#}
        =  {# La \<in># A. L \<noteq> La \<and> 2 \<le> count A La#} +
          {# La \<in># A. L = La \<and> Suc 0 \<le> count A L#}"
           by (auto simp: multiset_eq_iff ac_simps)
      have mset_decomp2: "{# La \<in># A. L \<noteq> La \<longrightarrow> 2 \<le> count A La#} =
        {# La \<in># A. L \<noteq> La \<and> 2 \<le> count A La#} + replicate_mset (count A L) L"
        by (auto simp: multiset_eq_iff)

      show ?thesis
        using \<open>\<Xi> {?C'} < \<Xi> {?C}\<close> condensation.hyps fin
        sum_count_ge_2.remove[of _ ?C] \<open>?C' \<notin> N\<close>
        by (auto simp: mset_decomp mset_decomp2 filter_mset_eq)
    qed
  ultimately show ?case by linarith
next
  case (subsumption A B) note AN = this(1) and AB = this(2) and BN = this(3) and fin = this(4)
  have "card (N - {B}) < card N" using BN by (meson card_Diff1_less subsumption.prems)
  moreover have "\<Xi> (N - {B}) \<le> \<Xi> N"
    by (simp add: Diff_subset finite_incl_le_setsum subsumption.prems)
  ultimately show ?case by linarith
qed

lemma simplify_terminates:
  "wf {(N', N). finite N \<and> simplify N N'}"
   apply (rule wfP_if_measure[of finite simplify "\<lambda>N. card N + \<Xi> N"])
  using simplify_finite_measure_decrease by blast


lemma wf_terminates:
  assumes "wf r"
  shows "\<exists>N'.(N', N)\<in> r\<^sup>*  \<and> (\<forall>N''. (N'', N')\<notin> r)"
proof -
  let ?P = "\<lambda>N. (\<exists>N'.(N', N)\<in> r\<^sup>*  \<and> (\<forall>N''. (N'', N')\<notin> r))"
  have "\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> ?P y) \<longrightarrow> ?P x"
    proof clarify
      fix x
      assume H: "\<forall>y. (y, x) \<in> r \<longrightarrow> ?P y"
      { assume "\<exists>y. (y, x) \<in> r"
        then obtain y where y: "(y, x) \<in> r" by blast
        then have "?P y" using H by blast
        then have "?P x" using y by (meson rtrancl.rtrancl_into_rtrancl)
      }
      moreover {
        assume "\<not>(\<exists>y. (y, x) \<in> r)"
        then have "?P x" by auto
      }
      ultimately show "?P x" by blast
    qed
  moreover have "(\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> ?P y) \<longrightarrow> ?P x) \<longrightarrow> All ?P"
    using assms unfolding wf_def by (rule allE)
  ultimately have "All ?P" by blast
  then show "?P N" by blast
qed

lemma rtranclp_simplify_terminates:
  assumes fin: "finite N"
  shows "\<exists>N'. simplify\<^sup>*\<^sup>* N N' \<and> simplified N'"
proof -
  have H: "{(N', N). finite N \<and> simplify N N'} = {(N', N). simplify N N' \<and> finite N}" by auto
  then have wf: "wf {(N', N). simplify N N' \<and> finite N}"
    using simplify_terminates by (simp add: H)
  obtain N' where N': "(N', N)\<in> {(b, a). simplify a b \<and> finite a}\<^sup>*" and
    more: "\<forall>N''. (N'', N')\<notin> {(b, a). simplify a b \<and> finite a}"
    using Prop_Resolution.wf_terminates[OF wf, of N] by blast
  have 1: "simplify\<^sup>*\<^sup>* N N'"
    using N' by (induction rule: rtrancl.induct) auto
  then have "finite N'" using fin rtranclp_simplify_preserves_finite by blast
  then have 2: "\<forall>N''. \<not>simplify N' N''" using more by auto

  show ?thesis using 1 2 by blast
qed

lemma finite_simplified_full1_simp:
  assumes "finite N"
  shows "simplified N \<or> (\<exists>N'. full1 simplify N N')"
  using rtranclp_simplify_terminates[OF assms] unfolding full1_def
  by (metis Nitpick.rtranclp_unfold)

lemma finite_simplified_full_simp:
  assumes "finite N"
  shows "\<exists>N'. full simplify N N'"
  using rtranclp_simplify_terminates[OF assms] unfolding full_def by metis

lemma can_decrease_tree_size_resolution:
  fixes \<psi> :: "'v state" and tree :: "'v sem_tree"
  assumes "finite (fst \<psi>)" and "already_used_inv \<psi>"
  and "partial_interps tree I (fst \<psi>)"
  and "simplified (fst \<psi>)"
  shows "\<exists>(tree':: 'v sem_tree) \<psi>'. resolution\<^sup>*\<^sup>* \<psi> \<psi>' \<and> partial_interps tree' I (fst \<psi>')
    \<and> (sem_tree_size tree' < sem_tree_size tree \<or> sem_tree_size tree = 0)"
  using assms
proof (induct arbitrary: I rule: sem_tree_size)
  case (bigger xs I) note IH = this(1) and finite = this(2) and a_u_i = this(3) and part = this(4)
    and simp = this(5)

  { assume "sem_tree_size xs = 0"
    then have ?case using part by blast
  }

  moreover {
    assume sn0: "sem_tree_size xs > 0"
    obtain ag ad v where xs: "xs = Node v ag ad" using sn0 by (cases xs, auto)
    {
       assume "sem_tree_size ag = 0 \<and> sem_tree_size ad = 0"
       then have ag: "ag = Leaf" and ad: "ad = Leaf" by (cases ag, auto, cases ad, auto)

       then obtain \<chi> \<chi>' where
         \<chi>: "\<not> I \<union> {Pos v} \<Turnstile> \<chi>" and
         tot\<chi>: "total_over_m (I \<union> {Pos v}) {\<chi>}" and
         \<chi>\<psi>: "\<chi> \<in> fst \<psi>" and
         \<chi>': "\<not> I \<union> {Neg v} \<Turnstile> \<chi>'" and
         tot\<chi>': "total_over_m (I \<union> {Neg v}) {\<chi>'}" and \<chi>'\<psi>: "\<chi>' \<in> fst \<psi>"
         using part unfolding xs by auto
       have Posv: "Pos v \<notin># \<chi>" using \<chi> unfolding true_cls_def true_lit_def by auto
       have Negv: "Neg v \<notin># \<chi>'" using \<chi>' unfolding true_cls_def true_lit_def by auto
       {
         assume Neg\<chi>: "Neg v \<notin># \<chi>"
         then have "\<not> I \<Turnstile> \<chi>" using \<chi> Posv unfolding true_cls_def true_lit_def by auto
         moreover have "total_over_m I {\<chi>}"
           using Posv Neg\<chi> atm_imp_pos_or_neg_lit tot\<chi> unfolding total_over_m_def total_over_set_def
           by fastforce
         ultimately have "partial_interps Leaf I (fst \<psi>)"
           and "sem_tree_size Leaf < sem_tree_size xs"
           and "resolution\<^sup>*\<^sup>* \<psi> \<psi>"
           unfolding xs by (auto simp add: \<chi>\<psi>)
       }
       moreover {
          assume Pos\<chi>: "Pos v \<notin># \<chi>'"
          then have I\<chi>: "\<not> I \<Turnstile> \<chi>'" using \<chi>' Posv unfolding true_cls_def true_lit_def by auto
          moreover have "total_over_m I {\<chi>'}"
            using Negv Pos\<chi> atm_imp_pos_or_neg_lit tot\<chi>'
            unfolding total_over_m_def total_over_set_def by fastforce
          ultimately have "partial_interps Leaf I (fst \<psi>)"
            and "sem_tree_size Leaf < sem_tree_size xs"
            and "resolution\<^sup>*\<^sup>* \<psi> \<psi>"
            using \<chi>'\<psi> I\<chi> unfolding xs by auto
       }
       moreover {
          assume neg: "Neg v \<in># \<chi>" and pos: "Pos v \<in># \<chi>'"
          have "count \<chi> (Neg v) = 1"
            using simplified_count[OF simp \<chi>\<psi>] neg
            by (simp add: dual_order.antisym)
          have "count \<chi>' (Pos v) = 1"
            using simplified_count[OF simp \<chi>'\<psi>] pos
            by (simp add: dual_order.antisym)

          obtain C where \<chi>C: "\<chi> = add_mset (Neg v) C" and negC: "Neg v \<notin># C" and posC: "Pos v \<notin># C"
            by (metis (no_types, lifting) One_nat_def Posv \<open>count \<chi> (Neg v) = 1\<close>
                \<open>count \<chi>' (Pos v) = 1\<close> count_add_mset count_greater_eq_Suc_zero_iff insert_DiffM
                le_numeral_extra(2) nat.inject pos)

          obtain C' where
            \<chi>C': "\<chi>' = add_mset (Pos v) C'" and
            posC': "Pos v \<notin># C'" and
            negC': "Neg v \<notin># C'"
            by (metis (no_types, lifting) Negv One_nat_def \<open>count \<chi>' (Pos v) = 1\<close> count_add_mset
                count_eq_zero_iff mset_add nat.inject pos)

          have totC: "total_over_m I {C}"
            using tot\<chi> tot_over_m_remove[of I "Pos v" C] negC posC unfolding \<chi>C by auto
          have totC': "total_over_m I {C'}"
            using tot\<chi>' total_over_m_sum tot_over_m_remove[of I "Neg v" C'] negC' posC'
            unfolding \<chi>C' by auto
          have "\<not> I \<Turnstile> C + C'"
            using \<chi> \<chi>' \<chi>C \<chi>C' by auto
          then have part_I_\<psi>''': "partial_interps Leaf I (fst \<psi> \<union> {C + C'})"
            using totC totC' \<open>\<not> I \<Turnstile> C + C'\<close> by (metis Un_insert_right insertI1
              partial_interps.simps(1) total_over_m_sum)
          {
            assume "(add_mset (Pos v) C', add_mset (Neg v) C) \<notin> snd \<psi>"
            then have inf'': "inference \<psi> (fst \<psi> \<union> {C + C'}, snd \<psi> \<union> {(\<chi>', \<chi>)})"
              by (metis \<chi>'\<psi> \<chi>C \<chi>C' \<chi>\<psi> add_mset_add_single inference_clause.resolution
                  inference_step prod.collapse union_commute)
            obtain N' where full: "full simplify (fst \<psi> \<union> {C + C'}) N'"
              by (metis finite_simplified_full_simp fst_conv inf'' inference_preserves_finite
                local.finite)
            have "resolution \<psi> (N', snd \<psi> \<union> {(\<chi>', \<chi>)})"
              using resolution.intros(2)[OF _ simp full, of "snd \<psi>" "snd \<psi> \<union> {(\<chi>', \<chi>)}"] inf''
              by (metis surjective_pairing)
            moreover have "partial_interps Leaf I N'"
              using full_simplify_preserve_partial_tree[OF full part_I_\<psi>'''] .
            moreover have "sem_tree_size Leaf < sem_tree_size xs" unfolding xs by auto
            ultimately have ?case
              by (metis (no_types) prod.sel(1) rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
          }
          moreover {
            assume a: "({#Pos v#} + C', {#Neg v#} + C) \<in> snd \<psi>"
            then have "(\<exists>\<chi> \<in> fst \<psi>. (\<forall>I. total_over_m I {C+C'} \<longrightarrow> total_over_m I {\<chi>})
                \<and> (\<forall>I. total_over_m I {\<chi>} \<longrightarrow> I \<Turnstile> \<chi> \<longrightarrow> I \<Turnstile> C' + C)) \<or> tautology (C' + C)"
              proof -
                obtain p where p: "Pos p \<in># ({#Pos v#} + C') \<and> Neg p \<in># ({#Neg v#} + C)
                  \<and>((\<exists>\<chi>\<in>fst \<psi>. (\<forall>I. total_over_m I {({#Pos v#} + C') - {#Pos p#} + (({#Neg v#} + C) - {#Neg p#})} \<longrightarrow> total_over_m I {\<chi>}) \<and> (\<forall>I. total_over_m I {\<chi>} \<longrightarrow> I \<Turnstile> \<chi> \<longrightarrow> I \<Turnstile> ({#Pos v#} + C') - {#Pos p#} + (({#Neg v#} + C) - {#Neg p#}))) \<or> tautology (({#Pos v#} + C') - {#Pos p#} + (({#Neg v#} + C) - {#Neg p#})))"
                  using a by (blast intro: allE[OF a_u_i[unfolded subsumes_def Ball_def],
                      of " ({#Pos v#} + C', {#Neg v#} + C)"])
                { assume "p \<noteq> v"
                  then have "Pos p \<in># C' \<and> Neg p \<in># C" using p by force
                  then have ?thesis by auto
                }
                moreover {
                  assume "p = v"
                 then have "?thesis" using p by (metis add.commute add_diff_cancel_left')
                }
                ultimately show ?thesis by auto
              qed
            moreover {
              assume "\<exists>\<chi> \<in> fst \<psi>. (\<forall>I. total_over_m I {C+C'} \<longrightarrow> total_over_m I {\<chi>})
                \<and> (\<forall>I. total_over_m I {\<chi>} \<longrightarrow> I \<Turnstile> \<chi> \<longrightarrow> I \<Turnstile> C' + C)"
              then obtain \<theta> where
                \<theta>: "\<theta> \<in> fst \<psi>" and
                tot_\<theta>_CC': "\<forall>I. total_over_m I {C+C'} \<longrightarrow> total_over_m I {\<theta>}" and
                \<theta>_inv: "\<forall>I. total_over_m I {\<theta>} \<longrightarrow> I \<Turnstile> \<theta> \<longrightarrow> I \<Turnstile> C' + C" by blast
              have "partial_interps Leaf I (fst \<psi>)"
                using tot_\<theta>_CC' \<theta> \<theta>_inv totC totC' \<open>\<not> I \<Turnstile> C + C'\<close> total_over_m_sum by fastforce
              moreover have "sem_tree_size Leaf < sem_tree_size xs" unfolding xs by auto
              ultimately have ?case by blast
            }
            moreover {
              assume tautCC': "tautology (C' + C)"
              have "total_over_m I {C'+C}" using totC totC' total_over_m_sum by auto
              then have "\<not>tautology (C' + C)"
                using \<open>\<not> I \<Turnstile> C + C'\<close> unfolding add.commute[of C C'] total_over_m_def
                unfolding tautology_def by auto
              then have False using tautCC'  unfolding tautology_def by auto
            }
            ultimately have ?case by auto
          }
          ultimately have ?case by auto
       }
       ultimately have ?case using part by (metis (no_types) sem_tree_size.simps(1))
    }
    moreover {
      assume size_ag: "sem_tree_size ag > 0"
      have "sem_tree_size ag < sem_tree_size xs" unfolding xs by auto
      moreover have "partial_interps ag (I \<union> {Pos v}) (fst \<psi>)"
      and partad: "partial_interps ad (I \<union> {Neg v}) (fst \<psi>)"
        using part partial_interps.simps(2) unfolding xs by metis+
      moreover
        have "sem_tree_size ag < sem_tree_size xs \<Longrightarrow> finite (fst \<psi>) \<Longrightarrow> already_used_inv \<psi>
          \<Longrightarrow> partial_interps ag (I \<union> {Pos v}) (fst \<psi>) \<Longrightarrow> simplified (fst \<psi>)
          \<Longrightarrow> \<exists>tree' \<psi>'. resolution\<^sup>*\<^sup>* \<psi> \<psi>' \<and> partial_interps tree' (I \<union> {Pos v}) (fst \<psi>')
              \<and> (sem_tree_size tree' < sem_tree_size ag \<or> sem_tree_size ag = 0)"
          using IH[of ag "I \<union> {Pos v}"]  by auto
      ultimately obtain \<psi>' :: "'v state" and tree' :: "'v sem_tree" where
        inf: "resolution\<^sup>*\<^sup>* \<psi> \<psi>'"
        and part: "partial_interps tree' (I \<union> {Pos v}) (fst \<psi>')"
        and size: "sem_tree_size tree' < sem_tree_size ag \<or> sem_tree_size ag = 0"
        using finite part rtranclp.rtrancl_refl a_u_i simp by blast

      have "partial_interps ad (I \<union> {Neg v}) (fst \<psi>')"
        using rtranclp_resolution_preserve_partial_tree inf partad by fast
      then have "partial_interps (Node v tree' ad) I (fst \<psi>')" using part by auto
      then have ?case using inf size size_ag part unfolding xs by fastforce
    }
    moreover {
      assume size_ad: "sem_tree_size ad > 0"
      have "sem_tree_size ad < sem_tree_size xs" unfolding xs by auto
      moreover
        have
          partag: "partial_interps ag (I \<union> {Pos v}) (fst \<psi>)" and
          "partial_interps ad (I \<union> {Neg v}) (fst \<psi>)"
          using part partial_interps.simps(2) unfolding xs by metis+
      moreover have "sem_tree_size ad < sem_tree_size xs \<longrightarrow> finite (fst \<psi>) \<longrightarrow> already_used_inv \<psi>
        \<longrightarrow> ( partial_interps ad (I \<union> {Neg v}) (fst \<psi>) \<longrightarrow> simplified (fst \<psi>)
        \<longrightarrow> (\<exists>tree' \<psi>'. resolution\<^sup>*\<^sup>* \<psi> \<psi>' \<and> partial_interps tree' (I \<union> {Neg v}) (fst \<psi>')
              \<and> (sem_tree_size tree' < sem_tree_size ad \<or> sem_tree_size ad = 0)))"
        using IH by blast
      ultimately obtain \<psi>' :: "'v state" and tree' :: "'v sem_tree" where
        inf: "resolution\<^sup>*\<^sup>* \<psi> \<psi>'"
        and part: "partial_interps tree' (I \<union> {Neg v}) (fst \<psi>')"
        and size: "sem_tree_size tree' < sem_tree_size ad \<or> sem_tree_size ad = 0"
        using finite part rtranclp.rtrancl_refl a_u_i simp by blast

      have "partial_interps ag (I \<union> {Pos v}) (fst \<psi>')"
        using rtranclp_resolution_preserve_partial_tree inf partag by fast
      then have "partial_interps (Node v ag tree') I (fst \<psi>')" using part by auto
      then have "?case" using inf size size_ad unfolding xs by fastforce
    }
     ultimately have ?case by auto
  }
  ultimately show ?case by auto
qed

lemma resolution_completeness_inv:
  fixes \<psi> :: "'v ::linorder state"
  assumes
    unsat: "\<not>satisfiable (fst \<psi>)" and
    finite: "finite (fst \<psi>)" and
    a_u_v: "already_used_inv \<psi>"
  shows "\<exists>\<psi>'. (resolution\<^sup>*\<^sup>* \<psi> \<psi>' \<and> {#} \<in> fst \<psi>')"
proof -
  obtain tree where "partial_interps tree {} (fst \<psi>)"
    using partial_interps_build_sem_tree_atms assms by metis
  then show ?thesis
    using unsat finite a_u_v
    proof (induct tree arbitrary: \<psi> rule: sem_tree_size)
      case (bigger tree \<psi>) note H = this
      {
        fix \<chi>
        assume tree: "tree = Leaf"
        obtain \<chi> where \<chi>: "\<not> {} \<Turnstile> \<chi>" and tot\<chi>: "total_over_m {} {\<chi>}" and \<chi>\<psi>: "\<chi> \<in> fst \<psi>"
          using H unfolding tree by auto
        moreover have "{#} = \<chi>"
          using H atms_empty_iff_empty tot\<chi>
          unfolding true_cls_def total_over_m_def total_over_set_def by fastforce
        moreover have "resolution\<^sup>*\<^sup>* \<psi> \<psi>" by auto
        ultimately have ?case by metis
      }
      moreover {
        fix v tree1 tree2
        assume tree: "tree = Node v tree1 tree2"
        obtain \<psi>\<^sub>0 where \<psi>\<^sub>0: "resolution\<^sup>*\<^sup>* \<psi> \<psi>\<^sub>0" and simp: "simplified (fst \<psi>\<^sub>0)"
          proof -
            { assume "simplified (fst \<psi>)"
              moreover have "resolution\<^sup>*\<^sup>* \<psi> \<psi>" by auto
              ultimately have "thesis" using that by blast
            }
            moreover {
              assume "\<not>simplified (fst \<psi>)"
              then have "\<exists>\<psi>'.  full1 simplify (fst \<psi>) \<psi>'"
                by (metis Nitpick.rtranclp_unfold bigger.prems(3) full1_def
                  rtranclp_simplify_terminates)
              then obtain N where "full1 simplify (fst \<psi>) N" by metis
              then have "resolution \<psi> (N, snd \<psi>)"
                using resolution.intros(1)[of "fst \<psi>" N "snd \<psi>"] by auto
              moreover have "simplified N"
                using \<open>full1 simplify (fst \<psi>) N\<close> unfolding full1_def by blast
              ultimately have ?thesis using that by force
            }
            ultimately show ?thesis by auto
          qed


        have p: "partial_interps tree {} (fst \<psi>\<^sub>0)"
        and uns: "unsatisfiable (fst \<psi>\<^sub>0)"
        and f: "finite (fst \<psi>\<^sub>0)"
        and a_u_v: "already_used_inv \<psi>\<^sub>0"
             using \<psi>\<^sub>0 bigger.prems(1) rtranclp_resolution_preserve_partial_tree apply blast
            using \<psi>\<^sub>0 bigger.prems(2) rtranclp_resolution_preserves_unsat apply blast
           using \<psi>\<^sub>0 bigger.prems(3) rtranclp_resolution_finite apply blast
          using rtranclp_resolution_already_used_inv[OF \<psi>\<^sub>0 bigger.prems(4)] by blast
        obtain tree' \<psi>' where
          inf: "resolution\<^sup>*\<^sup>* \<psi>\<^sub>0 \<psi>'" and
          part': "partial_interps tree' {} (fst \<psi>')" and
          decrease: "sem_tree_size tree' < sem_tree_size tree \<or> sem_tree_size tree = 0"
          using can_decrease_tree_size_resolution[OF f a_u_v p simp] unfolding tautology_def
          by meson
        have s: "sem_tree_size tree' < sem_tree_size tree" using decrease unfolding tree by auto
        have fin: "finite (fst \<psi>')"
          using f inf rtranclp_resolution_finite by blast
        have unsat: "unsatisfiable (fst \<psi>')"
          using rtranclp_resolution_preserves_unsat inf uns by metis
        have a_u_i': "already_used_inv \<psi>'"
          using a_u_v inf rtranclp_resolution_already_used_inv[of \<psi>\<^sub>0 \<psi>'] by auto
        have ?case
          using inf rtranclp_trans[of resolution] H(1)[OF s part' unsat fin a_u_i'] \<psi>\<^sub>0 by blast
      }
      ultimately show ?case by (cases tree, auto)
   qed
qed

lemma resolution_preserves_already_used_inv:
  assumes "resolution S S'"
  and "already_used_inv S"
  shows "already_used_inv S'"
  using assms
  apply (induct rule: resolution.induct)
   apply (rule full1_simplify_already_used_inv; simp)
  apply (rule full_simplify_already_used_inv, simp)
  apply (rule inference_preserves_already_used_inv, simp)
  apply blast
  done

lemma rtranclp_resolution_preserves_already_used_inv:
  assumes "resolution\<^sup>*\<^sup>* S S'"
  and "already_used_inv S"
  shows "already_used_inv S'"
  using assms
  apply (induct rule: rtranclp_induct)
   apply simp
  using resolution_preserves_already_used_inv by fast

lemma resolution_completeness:
  fixes \<psi> :: "'v ::linorder state"
  assumes unsat: "\<not>satisfiable (fst \<psi>)"
  and finite: "finite (fst \<psi>)"
  and "snd \<psi> = {}"
  shows "\<exists>\<psi>'. (resolution\<^sup>*\<^sup>* \<psi> \<psi>' \<and> {#} \<in> fst \<psi>')"
proof -
  have "already_used_inv \<psi>" unfolding assms by auto
  then show ?thesis using assms resolution_completeness_inv by blast
qed

lemma rtranclp_preserves_sat:
  assumes "simplify\<^sup>*\<^sup>* S S'"
  and "satisfiable S"
  shows "satisfiable S'"
  using assms apply induction
   apply simp
  by (meson satisfiable_carac satisfiable_def simplify_preserve_models_eq)

lemma resolution_preserves_sat:
  assumes "resolution S S'"
  and "satisfiable (fst S)"
  shows "satisfiable (fst S')"
  using assms apply (induction rule: resolution.induct)
   using rtranclp_preserves_sat tranclp_into_rtranclp unfolding full1_def apply fastforce
  by (metis fst_conv full_def inference_preserve_models rtranclp_preserves_sat
    satisfiable_carac' satisfiable_def)

lemma rtranclp_resolution_preserves_sat:
  assumes "resolution\<^sup>*\<^sup>* S S'"
  and "satisfiable (fst S)"
  shows "satisfiable (fst S')"
  using assms apply (induction rule: rtranclp_induct)
   apply simp
  using resolution_preserves_sat by blast

lemma resolution_soundness:
  fixes \<psi> :: "'v ::linorder state"
  assumes "resolution\<^sup>*\<^sup>* \<psi> \<psi>'" and "{#} \<in> fst \<psi>'"
  shows "unsatisfiable (fst \<psi>)"
  using assms by (meson rtranclp_resolution_preserves_sat satisfiable_def true_cls_empty
    true_clss_def)

lemma resolution_soundness_and_completeness:
fixes \<psi> :: "'v ::linorder state"
assumes finite: "finite (fst \<psi>)"
and snd: "snd \<psi> = {}"
shows "(\<exists>\<psi>'. (resolution\<^sup>*\<^sup>* \<psi> \<psi>' \<and> {#} \<in> fst \<psi>')) \<longleftrightarrow> unsatisfiable (fst \<psi>)"
  using assms resolution_completeness resolution_soundness by metis

lemma simplified_falsity:
  assumes simp: "simplified \<psi>"
  and "{#} \<in> \<psi>"
  shows "\<psi> = {{#}}"
proof (rule ccontr)
  assume H: "\<not> ?thesis"
  then obtain \<chi> where "\<chi> \<in> \<psi>" and "\<chi> \<noteq> {#}" using assms(2) by blast
  then have "{#} \<subset># \<chi>" by (simp add: subset_mset.zero_less_iff_neq_zero)
  then have "simplify \<psi> (\<psi> - {\<chi>})"
    using simplify.subsumption[OF assms(2) \<open>{#} \<subset># \<chi>\<close> \<open>\<chi> \<in> \<psi>\<close>] by blast
  then show False using simp by blast
qed


lemma simplify_falsity_in_preserved:
  assumes "simplify \<chi>s \<chi>s'"
  and "{#} \<in> \<chi>s"
  shows "{#} \<in> \<chi>s'"
  using assms
  by induction auto

lemma rtranclp_simplify_falsity_in_preserved:
  assumes "simplify\<^sup>*\<^sup>* \<chi>s \<chi>s'"
  and "{#} \<in> \<chi>s"
  shows "{#} \<in> \<chi>s'"
  using assms
  by induction (auto intro: simplify_falsity_in_preserved)

lemma resolution_falsity_get_falsity_alone:
  assumes "finite (fst \<psi>)"
  shows "(\<exists>\<psi>'. (resolution\<^sup>*\<^sup>* \<psi> \<psi>' \<and> {#} \<in> fst \<psi>')) \<longleftrightarrow> (\<exists>a_u_v. resolution\<^sup>*\<^sup>* \<psi> ({{#}}, a_u_v))"
    (is "?A \<longleftrightarrow> ?B")
proof
  assume ?B
  then show ?A by auto
next
  assume ?A
  then obtain \<chi>s a_u_v where \<chi>s: "resolution\<^sup>*\<^sup>* \<psi> (\<chi>s, a_u_v)" and F: "{#} \<in> \<chi>s" by auto
  { assume "simplified \<chi>s"
    then have ?B using simplified_falsity[OF _ F] \<chi>s by blast
  }
  moreover {
    assume "\<not> simplified \<chi>s"
    then obtain \<chi>s' where "full1 simplify \<chi>s \<chi>s'"
       by (metis \<chi>s assms finite_simplified_full1_simp fst_conv rtranclp_resolution_finite)
    then have "{#} \<in> \<chi>s'"
      unfolding full1_def by (meson F rtranclp_simplify_falsity_in_preserved
        tranclp_into_rtranclp)
    then have ?B
      by (metis \<chi>s \<open>full1 simplify \<chi>s \<chi>s'\<close> fst_conv full1_simp resolution_always_simplified
        rtranclp.rtrancl_into_rtrancl simplified_falsity)
  }
  ultimately show ?B by blast
qed

theorem resolution_soundness_and_completeness':
  fixes \<psi> :: "'v ::linorder state"
  assumes
    finite: "finite (fst \<psi>)"and
    snd: "snd \<psi> = {}"
  shows "(\<exists>a_u_v. (resolution\<^sup>*\<^sup>* \<psi> ({{#}}, a_u_v))) \<longleftrightarrow> unsatisfiable (fst \<psi>)"
  using assms resolution_completeness resolution_soundness resolution_falsity_get_falsity_alone
  by metis

end
