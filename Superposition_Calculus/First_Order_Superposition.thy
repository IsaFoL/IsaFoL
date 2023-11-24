theory First_Order_Superposition
  imports
    Saturation_Framework.Lifting_to_Non_Ground_Calculi
    Ground_Superposition
    First_Order_Clause
begin

section \<open>First-Order Layer\<close>

locale first_order_superposition_calculus =
  fixes
    less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) and
    less\<^sub>t\<^sub>G :: "'f ground_term \<Rightarrow> 'f ground_term \<Rightarrow> bool" (infix "\<prec>\<^sub>t\<^sub>G" 50) and
    select :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause" and
    select\<^sub>G :: "'f ground_atom clause \<Rightarrow> 'f ground_atom clause"
  assumes 
    less\<^sub>t\<^sub>G_less\<^sub>t: 
      "\<And>term\<^sub>1 term\<^sub>2. term\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>2 \<longleftrightarrow> to_term term\<^sub>1 \<prec>\<^sub>t to_term term\<^sub>2" and
    
    less\<^sub>t_transitive [intro]: "transp (\<prec>\<^sub>t)" and
    less\<^sub>t_asymmetric [intro]: "asymp (\<prec>\<^sub>t)" and

    less\<^sub>t\<^sub>G_wellfounded [intro]: "wfP (\<prec>\<^sub>t\<^sub>G)" and
    less\<^sub>t\<^sub>G_total [intro]: "totalp (\<prec>\<^sub>t\<^sub>G)" and
    
    less\<^sub>t\<^sub>G_context_compatible [simp]:
      "\<And>context term\<^sub>1 term\<^sub>2. term\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>2 \<Longrightarrow> context\<langle>term\<^sub>1\<rangle>\<^sub>G \<prec>\<^sub>t\<^sub>G context\<langle>term\<^sub>2\<rangle>\<^sub>G" and
    less\<^sub>t\<^sub>G_subterm_property [simp]: 
      "\<And>term context. context \<noteq> \<box>\<^sub>G \<Longrightarrow> term \<prec>\<^sub>t\<^sub>G context\<langle>term\<rangle>\<^sub>G" and

    less\<^sub>t_ground_subst_stability: 
      "\<And>term\<^sub>1 term\<^sub>2 (\<theta> :: 'v \<Rightarrow> ('f, 'v) term). 
        is_ground_term (term\<^sub>1 \<cdot>t \<theta>) \<Longrightarrow>
        is_ground_term (term\<^sub>2 \<cdot>t \<theta>) \<Longrightarrow>
        term\<^sub>1 \<prec>\<^sub>t term\<^sub>2 \<Longrightarrow>
        to_ground_term (term\<^sub>1 \<cdot>t \<theta>) \<prec>\<^sub>t\<^sub>G to_ground_term (term\<^sub>2 \<cdot>t \<theta>)" and
    
    select_subset: 
      "\<And>clause. select clause \<subseteq># clause" and
    select_negative: 
      "\<And>clause literal. literal \<in># select clause \<Longrightarrow> is_neg literal" and
    select_renaming_stability: 
      "\<And>clause \<rho>. is_renaming \<rho> \<Longrightarrow> select (clause \<cdot> \<rho>) = (select clause) \<cdot> \<rho>" and

    select\<^sub>G_select: "\<And>clause\<^sub>G. \<exists>clause \<theta>.
        is_ground_clause (clause \<cdot> \<theta>) \<and> 
        clause\<^sub>G = to_ground_clause (clause \<cdot> \<theta>) \<and> 
        select\<^sub>G clause\<^sub>G = to_ground_clause ((select clause) \<cdot> \<theta>)" and

    (* TODO: Use theorem from CeTA *)
    ground_critical_pair_theorem: "\<And>(R :: 'f gterm rel). ground_critical_pair_theorem R"
begin

(* TODO: Move this to example instantiation *)
definition is_ground_select :: "('f ground_atom clause \<Rightarrow> 'f ground_atom clause) \<Rightarrow> bool" where
  "is_ground_select ground_select = (\<forall>clause\<^sub>G. \<exists>clause \<theta>. 
        is_ground_clause (clause \<cdot> \<theta>)  \<and> 
        clause\<^sub>G = to_ground_clause (clause \<cdot> \<theta>) \<and> 
        ground_select clause\<^sub>G = to_ground_clause ((select clause) \<cdot> \<theta>))"

definition ground_selects where
  "ground_selects = { ground_select. is_ground_select ground_select }"

definition select\<^sub>G_simple where
  "select\<^sub>G_simple clause = to_ground_clause (select (to_clause clause))"

lemma "is_ground_select select\<^sub>G_simple"
  unfolding is_ground_select_def is_ground_select_def select\<^sub>G_simple_def
  by (metis to_clause_inverse ground_clause_is_ground subst_clause_Var_ident)
(* ----------- *)

lemmas less\<^sub>t_transitive_on = less\<^sub>t_transitive[THEN transp_on_subset, OF subset_UNIV]
lemmas less\<^sub>t_asymmetric_on = less\<^sub>t_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

lemma less\<^sub>t\<^sub>G_transitive [intro]: "transp (\<prec>\<^sub>t\<^sub>G)"
  using less\<^sub>t\<^sub>G_less\<^sub>t less\<^sub>t_transitive transpE transpI
  by metis

lemmas less\<^sub>t\<^sub>G_transitive_on = less\<^sub>t\<^sub>G_transitive[THEN transp_on_subset, OF subset_UNIV]

lemma less\<^sub>t\<^sub>G_asymmetric [intro]: "asymp (\<prec>\<^sub>t\<^sub>G)"
  by (simp add: wfP_imp_asymp less\<^sub>t\<^sub>G_wellfounded)

lemmas less\<^sub>t\<^sub>G_asymmetric_on = less\<^sub>t\<^sub>G_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

lemmas less\<^sub>t\<^sub>G_total_on = less\<^sub>t\<^sub>G_total[THEN totalp_on_subset, OF subset_UNIV]

lemma less\<^sub>t_less\<^sub>t\<^sub>G: 
  assumes "is_ground_term t1" and "is_ground_term t2"
  shows "t1 \<prec>\<^sub>t t2 \<longleftrightarrow> to_ground_term t1 \<prec>\<^sub>t\<^sub>G to_ground_term t2"
  by (simp add: assms less\<^sub>t\<^sub>G_less\<^sub>t)

lemma less\<^sub>t_total_on [intro]: "totalp_on (to_term ` terms\<^sub>G) (\<prec>\<^sub>t)"
  by (smt (verit, best) image_iff less\<^sub>t\<^sub>G_less\<^sub>t totalpD less\<^sub>t\<^sub>G_total_on totalp_on_def)

lemma select\<^sub>G_subset: "select\<^sub>G C \<subseteq># C"
  using select\<^sub>G_select
  by (metis select_subset to_ground_clause_def image_mset_subseteq_mono subst_clause_def)

lemma select_from_ground_clause1: 
  assumes "is_ground_clause clause" 
  shows "is_ground_clause (select clause)"
  using select_subset sub_ground_clause assms
  by metis

lemma select_from_ground_clause2: 
  assumes "literal \<in># select (to_clause clause)"  
  shows "is_ground_literal literal"
  using assms ground_literal_in_ground_clause(2) select_subset
  by blast

lemma select_from_ground_clause3: 
  assumes "is_ground_clause clause" "literal\<^sub>G \<in># to_ground_clause clause"
  shows "to_literal literal\<^sub>G \<in># clause"
  using assms 
  by (metis to_ground_clause_inverse ground_literal_in_ground_clause(3))

lemmas select_from_ground_clause = 
  select_from_ground_clause1
  select_from_ground_clause2
  select_from_ground_clause3

lemma select_subst1:
  assumes "is_ground_clause (clause \<cdot> \<theta>)"  
  shows "is_ground_clause (select clause \<cdot> \<theta>)" 
  using assms
  by (metis image_mset_subseteq_mono select_subset sub_ground_clause subst_clause_def)
  
lemma select_subst2: 
  assumes "literal \<in># select clause \<cdot> \<theta>"  
  shows "is_neg literal"
  using assms subst_neg_stable select_negative
  unfolding subst_clause_def
  by auto

lemmas select_subst = select_subst1 select_subst2

lemma select\<^sub>G_negative:
  assumes "literal \<in># select\<^sub>G clause\<^sub>G"
  shows "is_neg literal"
proof -
  obtain clause \<theta> where 
    is_ground: "is_ground_clause (clause \<cdot> \<theta>)" and
    select\<^sub>G: "select\<^sub>G clause\<^sub>G = to_ground_clause (select clause \<cdot> \<theta>)"
    using select\<^sub>G_select
    by blast

  show ?thesis
    using 
      select_from_ground_clause(3)[
          OF select_subst(1)[OF is_ground] assms[unfolded select\<^sub>G], 
          THEN select_subst(2)
      ]
    unfolding to_literal_def
    by simp
qed

abbreviation less_eq\<^sub>t (infix "\<preceq>\<^sub>t" 50) where
  "less_eq\<^sub>t \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

definition less\<^sub>l ::
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom literal \<Rightarrow> bool" (infix "\<prec>\<^sub>l" 50) where
  "less\<^sub>l literal\<^sub>1 literal\<^sub>2 \<equiv> multp (\<prec>\<^sub>t) (mset_lit literal\<^sub>1) (mset_lit literal\<^sub>2)"

abbreviation less_eq\<^sub>l (infix "\<preceq>\<^sub>l" 50) where
  "less_eq\<^sub>l \<equiv> (\<prec>\<^sub>l)\<^sup>=\<^sup>="

abbreviation less\<^sub>c ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" (infix "\<prec>\<^sub>c" 50) where
  "less\<^sub>c \<equiv> multp (\<prec>\<^sub>l)"

abbreviation less_eq\<^sub>c (infix "\<preceq>\<^sub>c" 50) where
  "less_eq\<^sub>c \<equiv> (\<prec>\<^sub>c)\<^sup>=\<^sup>="

abbreviation is_maximal\<^sub>l :: "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  "is_maximal\<^sub>l literal clause \<equiv> is_maximal_in_mset_wrt (\<prec>\<^sub>l) clause literal"

abbreviation is_strictly_maximal\<^sub>l :: 
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  "is_strictly_maximal\<^sub>l literal clause \<equiv> is_greatest_in_mset_wrt (\<prec>\<^sub>l) clause literal"

lemma less\<^sub>l_transitive [intro]: "transp (\<prec>\<^sub>l)"
  unfolding less\<^sub>l_def 
  using transp_multp[OF less\<^sub>t_transitive]
  by (metis (no_types, lifting) transpE transpI)

lemmas less\<^sub>l_transitive_on = less\<^sub>l_transitive[THEN transp_on_subset, OF subset_UNIV]
                                                            
lemma less\<^sub>l_asymmetric [intro]: "asymp (\<prec>\<^sub>l)"
  unfolding less\<^sub>l_def  multp_eq_multp\<^sub>H\<^sub>O[OF less\<^sub>t_asymmetric less\<^sub>t_transitive]
  using asymp_multp\<^sub>H\<^sub>O[OF less\<^sub>t_asymmetric less\<^sub>t_transitive]
  by (meson asympD asympI)

lemmas less\<^sub>l_asymmetric_on = less\<^sub>l_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

lemma less\<^sub>c_transitive [intro]: "transp (\<prec>\<^sub>c)"
  using transp_multp[OF less\<^sub>l_transitive].

lemmas less\<^sub>c_transitive_on = less\<^sub>c_transitive[THEN transp_on_subset, OF subset_UNIV]

lemma less\<^sub>c_asymmetric [intro]: "asymp (\<prec>\<^sub>c)"
  using asymp_multp[OF less\<^sub>l_asymmetric less\<^sub>l_transitive].

lemmas less\<^sub>c_asymmetric_on = less\<^sub>c_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

(* 
TODO: Rename stuff in ground superposition
*)
interpretation ground: ground_superposition_calculus "(\<prec>\<^sub>t\<^sub>G)" select\<^sub>G
  apply(unfold_locales)
  by(auto simp: select\<^sub>G_subset select\<^sub>G_negative ground_critical_pair_theorem)

notation ground.less_lit (infix "\<prec>\<^sub>l\<^sub>G" 50)
notation ground.less_cls (infix "\<prec>\<^sub>c\<^sub>G" 50)

notation ground.lesseq_trm (infix "\<preceq>\<^sub>t\<^sub>G" 50)
notation ground.lesseq_lit (infix "\<preceq>\<^sub>l\<^sub>G" 50)
notation ground.lesseq_cls (infix "\<preceq>\<^sub>c\<^sub>G" 50)

lemmas less\<^sub>l\<^sub>G_transitive_on = ground.transp_less_lit[THEN transp_on_subset, OF subset_UNIV]
lemmas less\<^sub>l\<^sub>G_asymmetric_on = ground.asymp_less_lit[THEN asymp_on_subset, OF subset_UNIV]
lemmas less\<^sub>l\<^sub>G_total_on = ground.totalp_less_lit[THEN totalp_on_subset, OF subset_UNIV]

lemmas less\<^sub>c\<^sub>G_transitive_on = ground.transp_less_cls[THEN transp_on_subset, OF subset_UNIV]
lemmas less\<^sub>c\<^sub>G_asymmetric_on = ground.asymp_less_cls[THEN asymp_on_subset, OF subset_UNIV]
lemmas less\<^sub>c\<^sub>G_total_on = ground.totalp_less_cls[THEN totalp_on_subset, OF subset_UNIV]

lemma not_less_eq\<^sub>t\<^sub>G: "\<not> term\<^sub>G\<^sub>2 \<preceq>\<^sub>t\<^sub>G term\<^sub>G\<^sub>1 \<longleftrightarrow> term\<^sub>G\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>G\<^sub>2"
  using asympD[OF less\<^sub>t\<^sub>G_asymmetric] totalpD[OF less\<^sub>t\<^sub>G_total]
  by blast

lemma less_eq\<^sub>t_less_eq\<^sub>t\<^sub>G:
  assumes "is_ground_term term\<^sub>1" and "is_ground_term term\<^sub>2" 
  shows "term\<^sub>1 \<preceq>\<^sub>t term\<^sub>2 \<longleftrightarrow> to_ground_term term\<^sub>1 \<preceq>\<^sub>t\<^sub>G to_ground_term term\<^sub>2"
  unfolding reflclp_iff less\<^sub>t_less\<^sub>t\<^sub>G[OF assms]
  using assms[THEN to_ground_term_inverse]
  by auto

lemma less_eq\<^sub>t\<^sub>G_less_eq\<^sub>t:
   "term\<^sub>G\<^sub>1 \<preceq>\<^sub>t\<^sub>G term\<^sub>G\<^sub>2 \<longleftrightarrow> to_term term\<^sub>G\<^sub>1 \<preceq>\<^sub>t to_term term\<^sub>G\<^sub>2"
  unfolding less_eq\<^sub>t_less_eq\<^sub>t\<^sub>G[OF ground_term_is_ground ground_term_is_ground] to_term_inverse
  by(rule refl)

lemma not_less_eq\<^sub>t: 
  assumes "is_ground_term term\<^sub>1" and "is_ground_term term\<^sub>2"
  shows "\<not> term\<^sub>2 \<preceq>\<^sub>t term\<^sub>1 \<longleftrightarrow> term\<^sub>1 \<prec>\<^sub>t term\<^sub>2"
  unfolding less\<^sub>t_less\<^sub>t\<^sub>G[OF assms] less_eq\<^sub>t_less_eq\<^sub>t\<^sub>G[OF assms(2, 1)] not_less_eq\<^sub>t\<^sub>G
  by (rule refl)

lemma less\<^sub>l\<^sub>G_less\<^sub>l: "literal\<^sub>G\<^sub>1 \<prec>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2 \<longleftrightarrow> to_literal literal\<^sub>G\<^sub>1 \<prec>\<^sub>l to_literal literal\<^sub>G\<^sub>2"
   using
     multp_image_mset_image_msetI[OF _ less\<^sub>t_transitive]
     multp_image_mset_image_msetD[OF _ less\<^sub>t_transitive_on to_term_inj]
   unfolding less\<^sub>l_def ground.less_lit_def less\<^sub>t\<^sub>G_less\<^sub>t mset_to_literal
   by blast

lemma less\<^sub>l_less\<^sub>l\<^sub>G: 
  assumes "is_ground_literal literal\<^sub>1" "is_ground_literal literal\<^sub>2" 
  shows "literal\<^sub>1 \<prec>\<^sub>l literal\<^sub>2 \<longleftrightarrow> to_ground_literal literal\<^sub>1 \<prec>\<^sub>l\<^sub>G to_ground_literal literal\<^sub>2"
  using assms
  by (simp add: less\<^sub>l\<^sub>G_less\<^sub>l)

lemma less\<^sub>l_total_on [intro]: "totalp_on (to_literal ` literals\<^sub>G) (\<prec>\<^sub>l)"
  by (smt (verit, best) image_iff less\<^sub>l\<^sub>G_less\<^sub>l totalpD less\<^sub>l\<^sub>G_total_on totalp_on_def)

lemma less_eq\<^sub>l_less_eq\<^sub>l\<^sub>G:
  assumes "is_ground_literal literal\<^sub>1" and "is_ground_literal literal\<^sub>2" 
  shows "literal\<^sub>1 \<preceq>\<^sub>l literal\<^sub>2 \<longleftrightarrow> to_ground_literal literal\<^sub>1 \<preceq>\<^sub>l\<^sub>G to_ground_literal literal\<^sub>2"
  unfolding reflclp_iff less\<^sub>l_less\<^sub>l\<^sub>G[OF assms]
  using assms[THEN to_ground_literal_inverse]
  by auto

lemma less_eq\<^sub>l\<^sub>G_less_eq\<^sub>l:
   "literal\<^sub>G\<^sub>1 \<preceq>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2 \<longleftrightarrow> to_literal literal\<^sub>G\<^sub>1 \<preceq>\<^sub>l to_literal literal\<^sub>G\<^sub>2"
  unfolding less_eq\<^sub>l_less_eq\<^sub>l\<^sub>G[OF ground_literal_is_ground ground_literal_is_ground] to_literal_inverse
  by(rule refl)

lemma maximal_lit_in_clause:
  assumes "ground.is_maximal_lit literal\<^sub>G clause\<^sub>G"
  shows "literal\<^sub>G \<in># clause\<^sub>G"
  using assms 
  unfolding is_maximal_in_mset_wrt_iff[OF less\<^sub>l\<^sub>G_transitive_on less\<^sub>l\<^sub>G_asymmetric_on]
  by simp

lemma maximal\<^sub>l_in_clause:
  assumes "is_maximal\<^sub>l literal clause"
  shows "literal \<in># clause"
  using assms 
  unfolding is_maximal_in_mset_wrt_iff[OF less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on]
  by simp

lemma is_maximal\<^sub>G\<^sub>l_iff_is_maximal\<^sub>l: 
  "ground.is_maximal_lit literal\<^sub>G clause\<^sub>G \<longleftrightarrow> is_maximal\<^sub>l (to_literal literal\<^sub>G) (to_clause clause\<^sub>G)"
   unfolding 
    is_maximal_in_mset_wrt_iff[OF less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on]
    is_maximal_in_mset_wrt_iff[OF less\<^sub>l\<^sub>G_transitive_on less\<^sub>l\<^sub>G_asymmetric_on]
    ground_literal_in_ground_clause(3)[symmetric]
   using 
     less\<^sub>l_less\<^sub>l\<^sub>G[OF ground_literal_is_ground ground_literal_in_ground_clause(2)] 
     ground_literal_in_ground_clause(2, 3)
   by (metis to_ground_literal_inverse to_literal_inverse)

lemmas less\<^sub>l_total_on_set_mset =
  less\<^sub>l_total_on[THEN totalp_on_subset, OF set_mset_to_clause_to_literal[THEN equalityD1]]

lemma is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l:
  "ground.is_strictly_maximal_lit literal\<^sub>G clause\<^sub>G 
    \<longleftrightarrow> is_strictly_maximal\<^sub>l (to_literal literal\<^sub>G) (to_clause clause\<^sub>G)"
  unfolding 
    is_greatest_in_mset_wrt_iff[OF less\<^sub>l\<^sub>G_transitive_on less\<^sub>l\<^sub>G_asymmetric_on less\<^sub>l\<^sub>G_total_on]
    is_greatest_in_mset_wrt_iff[OF less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on less\<^sub>l_total_on_set_mset]
    ground_literal_in_ground_clause(3)[symmetric]
    less\<^sub>l\<^sub>G_less\<^sub>l
    remove1_mset_to_literal
  by (simp add: set_mset_to_clause_to_literal)

lemma not_less_eq\<^sub>l\<^sub>G: "\<not> literal\<^sub>G\<^sub>2 \<preceq>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>1 \<longleftrightarrow> literal\<^sub>G\<^sub>1 \<prec>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2"
  using asympD[OF less\<^sub>l\<^sub>G_asymmetric_on] totalpD[OF less\<^sub>l\<^sub>G_total_on]
  by blast

lemma not_less_eq\<^sub>l: 
  assumes "is_ground_literal literal\<^sub>1" and "is_ground_literal literal\<^sub>2"
  shows "\<not> literal\<^sub>2 \<preceq>\<^sub>l literal\<^sub>1 \<longleftrightarrow> literal\<^sub>1 \<prec>\<^sub>l literal\<^sub>2"
  unfolding less\<^sub>l_less\<^sub>l\<^sub>G[OF assms] less_eq\<^sub>l_less_eq\<^sub>l\<^sub>G[OF assms(2, 1)] not_less_eq\<^sub>l\<^sub>G
  by(rule refl) 

lemma less\<^sub>c\<^sub>G_less\<^sub>c: 
  "clause\<^sub>G\<^sub>1 \<prec>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2 \<longleftrightarrow> to_clause clause\<^sub>G\<^sub>1 \<prec>\<^sub>c to_clause clause\<^sub>G\<^sub>2"
  using
     multp_image_mset_image_msetI[OF _ less\<^sub>l_transitive]
     multp_image_mset_image_msetD[OF _ less\<^sub>l_transitive to_literal_inj]
  unfolding less\<^sub>l\<^sub>G_less\<^sub>l to_clause_def
  by blast

lemma less\<^sub>c_less\<^sub>c\<^sub>G: 
  assumes "is_ground_clause clause\<^sub>1" "is_ground_clause clause\<^sub>2"
  shows "clause\<^sub>1 \<prec>\<^sub>c clause\<^sub>2 \<longleftrightarrow> to_ground_clause clause\<^sub>1 \<prec>\<^sub>c\<^sub>G  to_ground_clause clause\<^sub>2"
  using assms
  by (simp add: less\<^sub>c\<^sub>G_less\<^sub>c)

lemma less_eq\<^sub>c_less_eq\<^sub>c\<^sub>G:
  assumes "is_ground_clause clause\<^sub>1" and "is_ground_clause clause\<^sub>2" 
  shows "clause\<^sub>1 \<preceq>\<^sub>c clause\<^sub>2 \<longleftrightarrow> to_ground_clause clause\<^sub>1 \<preceq>\<^sub>c\<^sub>G to_ground_clause clause\<^sub>2"
  unfolding reflclp_iff less\<^sub>c_less\<^sub>c\<^sub>G[OF assms]
  using assms[THEN to_ground_clause_inverse]
  by auto

lemma less_eq\<^sub>c\<^sub>G_less_eq\<^sub>c:
   "clause\<^sub>G\<^sub>1 \<preceq>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2 \<longleftrightarrow> to_clause clause\<^sub>G\<^sub>1 \<preceq>\<^sub>c to_clause clause\<^sub>G\<^sub>2"
  unfolding less_eq\<^sub>c_less_eq\<^sub>c\<^sub>G[OF ground_clause_is_ground ground_clause_is_ground] to_clause_inverse
  by(rule refl)

lemma less\<^sub>c_total_on: "totalp_on (to_clause ` clauses) (\<prec>\<^sub>c)"
  by (smt ground.totalp_less_cls image_iff less\<^sub>c\<^sub>G_less\<^sub>c totalpD totalp_onI) 

lemma not_less_eq\<^sub>c\<^sub>G: "\<not> clause\<^sub>G\<^sub>2 \<preceq>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>1 \<longleftrightarrow> clause\<^sub>G\<^sub>1 \<prec>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2"
  using asympD[OF less\<^sub>c\<^sub>G_asymmetric_on] totalpD[OF less\<^sub>c\<^sub>G_total_on]
  by blast

lemma not_less_eq\<^sub>c: 
  assumes "is_ground_clause clause\<^sub>1" and "is_ground_clause clause\<^sub>2"
  shows "\<not> clause\<^sub>2 \<preceq>\<^sub>c clause\<^sub>1 \<longleftrightarrow> clause\<^sub>1 \<prec>\<^sub>c clause\<^sub>2"
  unfolding less\<^sub>c_less\<^sub>c\<^sub>G[OF assms] less_eq\<^sub>c_less_eq\<^sub>c\<^sub>G[OF assms(2, 1)] not_less_eq\<^sub>c\<^sub>G
  by(rule refl)

inductive superposition ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
where
  superpositionI: 
   "term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    vars_clause (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    \<P> \<in> {Pos, Neg} \<Longrightarrow>
    L\<^sub>1 = \<P> (Upair s\<^sub>1\<langle>u\<^sub>1\<rangle> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    (\<P> = Pos \<and> select P\<^sub>1 = {#} \<and> is_strictly_maximal\<^sub>l  (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)) \<or>
    (\<P> = Neg \<and> (select P\<^sub>1 = {#} \<and> is_maximal\<^sub>l (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> L\<^sub>1 \<in># select P\<^sub>1)) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (\<P> (Upair (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (s\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    superposition P\<^sub>1 P\<^sub>2 C"

inductive eq_resolution :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  eq_resolutionI: "
    P = add_mset L P' \<Longrightarrow>
    L = s\<^sub>1 !\<approx> s\<^sub>2 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{s\<^sub>1, s\<^sub>2}} \<Longrightarrow>
    select P = {#} \<and> is_maximal\<^sub>l (L \<cdot>l \<mu>) (P \<cdot> \<mu>) \<or> L \<in># select P \<Longrightarrow>
    C = P' \<cdot> \<mu> \<Longrightarrow>
    eq_resolution P C"

inductive eq_factoring :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  eq_factoringI: "
    P = add_mset L\<^sub>1 (add_mset L\<^sub>2 P') \<Longrightarrow>
    L\<^sub>1 = (s\<^sub>1 \<approx> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = (t\<^sub>2 \<approx> t\<^sub>2') \<Longrightarrow>
    select P = {#} \<and> is_maximal\<^sub>l (L\<^sub>1 \<cdot>l \<mu>) (P \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<mu>) \<Longrightarrow>
    term_subst.is_imgu \<mu> {{s\<^sub>1, t\<^sub>2}} \<Longrightarrow>
    C = add_mset (s\<^sub>1 \<approx> t\<^sub>2') (add_mset (s\<^sub>1' !\<approx> t\<^sub>2') P') \<cdot> \<mu> \<Longrightarrow>
    eq_factoring P C"

lemma is_renaming_var: "is_renaming Var"
  unfolding is_renaming_def
  by simp

lemma test1: "add_mset (L \<cdot>l \<theta>) (C \<cdot> \<theta>) = (add_mset L C) \<cdot> \<theta>"
  by (simp add: subst_clause_add_mset)

lemma test7: 
   fixes 
    s :: "('f, 'v) term" and
    s' :: "('f, 'v) term" and
    \<theta> :: "('f, 'v) subst"
  assumes
    "s \<cdot>t \<theta> = s' \<cdot>t \<theta>"
  shows
    "\<exists>(\<sigma> :: ('f, 'v) subst) \<tau>.  \<theta> = \<sigma> \<odot> \<tau> \<and> (\<forall>\<upsilon>. term_subst.is_unifiers \<upsilon> {{s, s'}} \<longrightarrow> (\<exists>\<sigma>'. \<upsilon> = \<sigma> \<odot> \<sigma>'))"
  using the_mgu[OF assms]
  by (metis subst_monoid_mult.mult.left_neutral)

lemma test8: 
   fixes 
    s :: "('f, 'v) term" and
    s' :: "('f, 'v) term" and
    \<theta> :: "('f, 'v) subst"
  assumes
    "s \<cdot>t \<theta> = s' \<cdot>t \<theta>"
  shows
    "\<exists>(\<sigma> :: ('f, 'v) subst) \<tau>.  \<theta> = \<sigma> \<odot> \<tau> \<and> term_subst.is_mgu \<sigma> {{s, s'}}"
  using assms
  unfolding term_subst.is_mgu_def term_subst.is_unifier_def term_subst.is_unifiers_def
  apply auto
proof -
  obtain tt :: "('f, 'v) Term.term set \<Rightarrow> ('f, 'v) Term.term" where
    f1: "\<forall>T. (card T \<noteq> Suc 0 \<or> T = {tt T}) \<and> (card T = Suc 0 \<or> (\<forall>t. T \<noteq> {t}))"
    by (metis card_1_singleton_iff)
  have "s' \<cdot>t the_mgu s' s = s \<cdot>t the_mgu s' s \<and> \<theta> = the_mgu s' s \<odot> \<theta>"
    by (metis (no_types) assms the_mgu)
  then show "\<exists>f. (\<exists>fa. \<theta> = f \<odot> fa) \<and> card {s \<cdot>t f::('f, 'v) Term.term, s' \<cdot>t f} \<le> Suc 0 \<and> (\<forall>fa. card {s \<cdot>t fa::('f, 'v) Term.term, s' \<cdot>t fa} \<le> Suc 0 \<longrightarrow> (\<exists>fb. fa = f \<odot> fb))"
    using f1 by (metis (no_types) card_Suc_eq insert_absorb2 insert_iff le_Suc_eq the_mgu)
qed

(* TODO: *)
lemma test9: 
   fixes 
    s :: "('f, 'v) term" and
    s' :: "('f, 'v) term" and
    \<theta> :: "('f, 'v) subst"
  assumes
    "s \<cdot>t \<theta> = s' \<cdot>t \<theta>"
  shows
    "\<exists>(\<sigma> :: ('f, 'v) subst) \<tau>.  \<theta> = \<sigma> \<odot> \<tau> \<and> term_subst.is_imgu \<sigma> {{s, s'}}"
  using assms
  unfolding term_subst.is_imgu_def term_subst.is_unifier_def term_subst.is_unifiers_def
  apply auto
proof-
  obtain tt :: "('f, 'v) Term.term set \<Rightarrow> ('f, 'v) Term.term" where
    f1: "\<forall>T. (card T \<noteq> Suc 0 \<or> T = {tt T}) \<and> (card T = Suc 0 \<or> (\<forall>t. T \<noteq> {t}))"
    by (metis card_1_singleton_iff)

  have "s' \<cdot>t the_mgu s' s = s \<cdot>t the_mgu s' s \<and> \<theta> = the_mgu s' s \<odot> \<theta>"
    by (metis (no_types) assms the_mgu)

  then show "\<exists>\<sigma>. (\<exists>\<tau>. \<theta> = \<sigma> \<odot> \<tau>) \<and> card {s \<cdot>t \<sigma>, s' \<cdot>t \<sigma>} \<le> Suc 0 \<and> (\<forall>\<tau>. card {s \<cdot>t \<tau> ::('f, 'v) Term.term, s' \<cdot>t \<tau>} \<le> Suc 0 \<longrightarrow> \<tau> = \<sigma> \<odot> \<tau>)"
    using f1
    by (smt (z3) card_insert_if finite.emptyI finite.insertI insert_absorb2 le_Suc_numeral le_antisym le_numeral_Suc le_numeral_extra(3) pred_numeral_simps(1) singletonD the_mgu)
qed


(* TODO: *)
lemma x: "a  \<noteq> a' \<Longrightarrow> mset_uprod a \<noteq> mset_uprod a'"
  apply(cases a; cases a')
  by (auto simp: add_eq_conv_ex)

lemma y: "a  \<noteq> a' \<Longrightarrow> mset_uprod a + mset_uprod a \<noteq> mset_uprod a' + mset_uprod a'"
  apply(cases a; cases a')
  by (auto simp: add_eq_conv_ex)

lemma x1: "a  \<noteq> a' \<Longrightarrow> mset_uprod a \<noteq> mset_uprod a' + mset_uprod a'"
  apply(cases a; cases a')
  by(auto simp: add_eq_conv_ex)

lemma x2: "mset_uprod a \<noteq> mset_uprod a' + mset_uprod a'"
  apply(cases a; cases a')
  by (metis add_cancel_right_left empty_not_add_mset mset_uprod_Upair x1)


lemma uneq_lit_uneq_mset_lit: "l \<noteq> l' \<Longrightarrow> mset_lit l \<noteq> mset_lit l'"
  apply(cases l; cases l')
     apply(auto simp: x x1 x2 y)
  by (metis x2)

lemma "multp (<) {# (1::nat), 2 #} {# 1, 3 #}"
  by (metis eval_nat_numeral(3) lessI less_multiset_def less_multiset_doubletons not_less_eq not_numeral_less_one)

lemma "multp (<) {# (2::nat), 3 #} {# 1, 4 #}"
  by (meson less_multiset_def less_multiset_doubletons numeral_less_iff semiring_norm(76) semiring_norm(78) semiring_norm(81))

lemma jasmin: 
  assumes "transp R"  "asymp R" "A = {# a1, a2 #}" "B = {# b1, b2 #}" "multp R A B"
  shows "count B a1 < count A a1 \<and> (R a1 b1 \<or> R a1 b2) \<and> (count B a2 < count A a2 \<and> (R a2 b1 \<or> R a2 b2) \<or> count A a2 \<le> count B a2)
       \<or> count B a2 < count A a2 \<and> (R a2 b1 \<or> R a2 b2) \<and> count A a1 \<le> count B a1"
  using assms
  unfolding multp_eq_multp\<^sub>H\<^sub>O[OF assms(2, 1)] multp\<^sub>H\<^sub>O_def
  by (smt (verit, del_insts) add_eq_conv_ex add_mset_remove_trivial count_add_mset count_eq_zero_iff
        count_greater_zero_iff in_diff_count linorder_le_less_linear order_less_imp_not_less 
        union_single_eq_member)

lemma multp\<^sub>D\<^sub>M_map_strong:
  assumes
    compat_f: "\<forall>x \<in># xs. \<forall>y \<in># ys. R x y \<longrightarrow> R (f x) (f y)" and
    ys_gt_xs: "multp\<^sub>D\<^sub>M R xs ys"
  shows "multp\<^sub>D\<^sub>M R (image_mset f xs) (image_mset f ys)"
proof -
  obtain Y X where
    y_nemp: "Y \<noteq> {#}" and y_sub_ys: "Y \<subseteq># ys" and xs_eq: "xs = ys - Y + X" and
    ex_y: "\<forall>x. x \<in># X \<longrightarrow> (\<exists>y. y \<in># Y \<and> R x y)"
    using ys_gt_xs[unfolded multp\<^sub>D\<^sub>M_def Let_def mset_map] by blast

  have x_sub_xs: "X \<subseteq># xs"
    using xs_eq by simp

  let ?fY = "image_mset f Y"
  let ?fX = "image_mset f X"

  show ?thesis
    unfolding multp\<^sub>D\<^sub>M_def 
  proof (intro exI conjI)
    show "image_mset f xs = image_mset f ys - ?fY + ?fX"
      using xs_eq[THEN arg_cong, of "image_mset f"] y_sub_ys 
      by (metis image_mset_Diff image_mset_union)
  next
    obtain y where y: "\<forall>x. x \<in># X \<longrightarrow> y x \<in># Y \<and> R x (y x)"
      using ex_y by moura

    show "\<forall>fx. fx \<in># ?fX \<longrightarrow> (\<exists>fy. fy \<in># ?fY \<and> R fx fy)"
    proof (intro allI impI)
      fix fx
      assume "fx \<in># ?fX"
      then obtain x where fx: "fx = f x" and x_in: "x \<in># X"
        by auto
      hence y_in: "y x \<in># Y" and y_gt: "R x (y x)"
        using y[rule_format, OF x_in] by blast+
      hence "f (y x) \<in># ?fY \<and> R (f x)(f (y x)) "
        using compat_f y_sub_ys x_sub_xs x_in
        by (metis image_eqI in_image_mset mset_subset_eqD)
      thus "\<exists>fy. fy \<in># ?fY \<and> R fx fy"
        unfolding fx by auto
    qed
  qed (auto simp: y_nemp y_sub_ys image_mset_subseteq_mono)
qed

lemma sure: "{#x \<cdot>t \<theta>. x \<in># mset_lit l#} = mset_lit (l \<cdot>l \<theta>)"
  unfolding subst_literal_def subst_atom_def
  by (cases l) (auto simp: mset_uprod_image_mset)

lemma sure2: "is_ground_literal (l \<cdot>l \<theta>) \<Longrightarrow> t \<in># mset_lit l \<Longrightarrow> is_ground_term (t \<cdot>t \<theta>)"
  apply(cases l) 
  by(auto simp add: subst_atom_def subst_literal uprod.set_map vars_atom_def)

lemma sure3: "is_ground_clause (c \<cdot> \<theta>) \<Longrightarrow> l \<in># c \<Longrightarrow> is_ground_literal (l \<cdot>l \<theta>)"
  by (metis is_ground_clause_add_mset multi_member_split subst_clause_add_mset)

lemma test:
  assumes "is_ground_term (t1 \<cdot>t \<theta>)" "is_ground_term (t2 \<cdot>t \<theta>)"  "t1 \<prec>\<^sub>t t2"
  shows "(t1 \<cdot>t \<theta>) \<prec>\<^sub>t (t2 \<cdot>t \<theta>)"
  using less\<^sub>t_ground_subst_stability[OF assms]
  unfolding 
    less\<^sub>t\<^sub>G_less\<^sub>t 
    to_ground_term_inverse[OF assms(1)]
    to_ground_term_inverse[OF assms(2)].

lemma less\<^sub>l_grounding_substitution: 
  assumes 
    "is_ground_literal (l \<cdot>l \<theta>)" 
    "is_ground_literal (l' \<cdot>l \<theta>)" 
    "l \<prec>\<^sub>l l'"
  shows
    "l \<cdot>l \<theta> \<prec>\<^sub>l l' \<cdot>l \<theta>"
proof-
  have base: "multp\<^sub>D\<^sub>M (\<prec>\<^sub>t) (mset_lit l) (mset_lit l')"
    using assms(3) less\<^sub>l_def multp_eq_multp\<^sub>D\<^sub>M by force

  have ground: 
    "\<And>t. t \<in># mset_lit l \<Longrightarrow> is_ground_term (t \<cdot>t \<theta>)" 
    "\<And>t'. t' \<in># mset_lit l' \<Longrightarrow> is_ground_term (t' \<cdot>t \<theta>)"
    unfolding sure2[OF assms(1)] sure2[OF assms(2)]
    by auto

  have "\<And>x y. x \<in># mset_lit l \<Longrightarrow> y \<in># mset_lit l' \<Longrightarrow> x \<prec>\<^sub>t y \<Longrightarrow> x \<cdot>t \<theta> \<prec>\<^sub>t y \<cdot>t \<theta>"
    using test[OF ground]
    by auto

  then have xy: "\<forall>x\<in>#  mset_lit l. \<forall>y\<in>#  mset_lit l'.  x \<prec>\<^sub>t y \<longrightarrow> x \<cdot>t \<theta> \<prec>\<^sub>t y \<cdot>t \<theta>" 
    by blast

  show ?thesis
    using multp\<^sub>D\<^sub>M_map_strong[OF xy base]
    unfolding less\<^sub>l_def multp_eq_multp\<^sub>D\<^sub>M[OF less\<^sub>t_asymmetric less\<^sub>t_transitive] sure.
qed

lemma less\<^sub>c_grounding_substitution: 
  assumes 
    "is_ground_clause (c \<cdot> \<theta>)" 
    "is_ground_clause (c' \<cdot> \<theta>)" 
    "c \<prec>\<^sub>c c'"
  shows
    "c \<cdot> \<theta> \<prec>\<^sub>c c' \<cdot> \<theta>"
proof-
  have ground: 
    "\<And>l. l \<in># c \<Longrightarrow> is_ground_literal (l \<cdot>l \<theta>)" 
    "\<And>l'. l' \<in># c' \<Longrightarrow> is_ground_literal (l' \<cdot>l \<theta>)"
    unfolding sure3[OF assms(1)] sure3[OF assms(2)]
    by auto

  have "\<And>x y. x \<in># c \<Longrightarrow> y \<in># c' \<Longrightarrow> x \<prec>\<^sub>l y \<Longrightarrow> x \<cdot>l \<theta> \<prec>\<^sub>l y \<cdot>l \<theta>"
    using less\<^sub>l_grounding_substitution[OF ground]
    by auto

  then have xy: "\<forall>x\<in>#  c. \<forall>y\<in># c'.  x \<prec>\<^sub>l y \<longrightarrow> x \<cdot>l \<theta> \<prec>\<^sub>l y \<cdot>l \<theta>" 
    by blast

  from assms(3) show ?thesis
    using multp\<^sub>D\<^sub>M_map_strong[OF xy] 
    unfolding multp_eq_multp\<^sub>D\<^sub>M[OF less\<^sub>l_asymmetric
 less\<^sub>l_transitive] 
    by (simp add: subst_clause_def)
qed

definition G_T :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) subst \<Rightarrow> 'f ground_atom clause set" where
  "G_T clause \<theta> = { ground_clause. ground_clause = to_ground_clause (clause \<cdot> \<theta>) }"

lemma ground_eq_resolution_implies_eq_resolution:
  assumes 
    P: "P = add_mset (s !\<approx> s') C" and
    P_is_ground: "is_ground_clause (P \<cdot> \<theta>)" and
    select: "to_clause (select\<^sub>G (to_ground_clause (P \<cdot> \<theta>))) = (select P) \<cdot> \<theta>" and
    ground_eq_resolution: "ground.ground_eq_resolution (to_ground_clause (P \<cdot> \<theta>)) (to_ground_clause (C \<cdot> \<theta>))"
  shows "\<exists>\<sigma>. eq_resolution P (C \<cdot> \<sigma>) \<and> to_ground_clause (P \<cdot> \<theta>) \<in> G_T P \<theta> \<and> to_ground_clause (C \<cdot> \<theta>) \<in> G_T (C \<cdot> \<sigma>) \<theta>"
  using ground_eq_resolution
proof(cases "to_ground_clause (P \<cdot> \<theta>)" "to_ground_clause (C \<cdot> \<theta>)" rule: ground.ground_eq_resolution.cases)
  case (ground_eq_resolutionI L t)

  have P_\<theta>: "P \<cdot> \<theta> = add_mset (to_literal L) (C \<cdot> \<theta>)"
    using ground_eq_resolutionI(1)
    by (metis P P_is_ground to_clause_def to_ground_clause_inverse image_mset_add_mset is_ground_clause_add_mset subst_clause_add_mset)

  then have P_\<theta>': "P \<cdot> \<theta> = add_mset ((s !\<approx> s') \<cdot>l \<theta>) (C \<cdot> \<theta>)"
    using P subst_clause_add_mset by blast

  then have "is_ground_literal ((s !\<approx> s') \<cdot>l \<theta>)" "is_ground_clause (C \<cdot> \<theta>)"
    using P_is_ground
    by auto

  have L: "to_literal L = (s !\<approx> s') \<cdot>l \<theta>" "L = to_ground_literal ((s !\<approx> s') \<cdot>l \<theta>)"
    using P_\<theta> P_\<theta>'
    by auto  

  have "(s !\<approx> s') \<cdot>l \<theta>  = to_literal (t !\<approx> t)"
    using ground_eq_resolutionI(2) L(1) by presburger

  then have s: "s \<cdot>t \<theta> = to_term t" and s': "s' \<cdot>t \<theta> = to_term t"
    by (simp_all add: to_literal_def to_atom_def subst_atom_def subst_literal)

  then have "s \<cdot>t \<theta> = s' \<cdot>t \<theta>"
    by simp

  then obtain \<sigma> \<tau> where \<sigma>: "term_subst.is_imgu \<sigma> {{s, s'}}" "\<theta> = \<sigma> \<odot> \<tau>"
    using test9
    by blast

  have eq: "eq_resolution P (C \<cdot> \<sigma>)"
  proof (rule eq_resolutionI)
    show "P = add_mset (s !\<approx> s') C"
      using P.
  next 
    show "s !\<approx> s' = s !\<approx> s'"
      by (rule refl)
  next
    show "term_subst.is_imgu \<sigma> {{s, s'}}"
      using \<sigma>(1).
  next
    have s: "select\<^sub>G (to_ground_clause (P \<cdot> \<theta>)) = to_ground_clause (select P \<cdot> \<theta>)"
      by (metis to_clause_inverse local.select)

    show "select P = {#} \<and> is_maximal\<^sub>l ((s !\<approx> s') \<cdot>l \<sigma>) (P \<cdot> \<sigma>) \<or> s !\<approx> s' \<in># select P"
    proof(cases "select\<^sub>G (to_ground_clause (P \<cdot> \<theta>)) = {#}")
      case True
      then have empty: "select P = {#}"
        by (metis to_clause_empty_mset image_mset_is_empty_iff local.select subst_clause_def)

      then have y: "is_maximal\<^sub>l ((s !\<approx> s') \<cdot>l \<theta>) (P \<cdot> \<theta>)"
        using ground_eq_resolutionI(3) True
        by (simp add: L(1) P_is_ground is_maximal\<^sub>G\<^sub>l_iff_is_maximal\<^sub>l)

      (* TODO: *)
      have max_lit: "is_maximal\<^sub>l (Neg (Upair s s') \<cdot>l \<sigma>) (P \<cdot> \<sigma>)"
      proof(rule ccontr)  
        assume a: "\<not> is_maximal\<^sub>l (Neg (Upair s s') \<cdot>l \<sigma>) (P \<cdot> \<sigma>)"

        then obtain L' where "(s !\<approx> s') \<cdot>l \<sigma> \<prec>\<^sub>l L' \<cdot>l \<sigma>" "is_ground_literal (L' \<cdot>l \<theta>)" "L' \<in># P \<cdot> \<theta>"
          using is_maximal_in_mset_wrt_iff[OF less\<^sub>l_transitive[THEN transp_on_subset] less\<^sub>l_asymmetric
[THEN asymp_on_subset]]
          by (smt (verit) L(1) L(2) P P_is_ground \<open>is_ground_literal (Neg (Upair s s') \<cdot>l \<theta>)\<close> \<sigma>(2) less\<^sub>l_asymmetric
 asymp_on_subset clause_subst_compose to_ground_literal_inverse is_ground_clause_add_mset less\<^sub>l\<^sub>G_less\<^sub>l less\<^sub>l_grounding_substitution literal_subst_compose multi_member_split not_less_eq\<^sub>l sup2CI test1 top_greatest less\<^sub>l_transitive transp_on_subset union_single_eq_member y)

        then have a: "is_ground_literal ((s !\<approx> s') \<cdot>l \<sigma> \<cdot>l \<tau>)"
          by (metis L(1) \<sigma>(2) literal_subst_compose ground_literal_is_ground)
      
        then have "Neg (Upair s s') \<cdot>l \<sigma> \<cdot>l \<tau> \<prec>\<^sub>l L' \<cdot>l \<sigma> \<cdot>l \<tau>"
          using less\<^sub>l_grounding_substitution
          by (metis \<open>Neg (Upair s s') \<cdot>l \<sigma> \<prec>\<^sub>l L' \<cdot>l \<sigma>\<close> \<open>is_ground_literal (L' \<cdot>l \<theta>)\<close> \<sigma>(2) literal_subst_compose)

        then have "\<not> is_maximal\<^sub>l (Neg (Upair s s') \<cdot>l \<sigma> \<cdot>l \<tau>) (P \<cdot> \<sigma> \<cdot> \<tau>)"
          using is_maximal_in_mset_wrt_iff[OF less\<^sub>l_transitive[THEN transp_on_subset] less\<^sub>l_asymmetric
[THEN asymp_on_subset]]
          by (metis P_is_ground \<open>L' \<in># P \<cdot> \<theta>\<close> \<sigma>(2) asympD less\<^sub>l_asymmetric
 clause_subst_compose ground_literal_in_ground_clause(1) subset_UNIV subst_ground_literal)
          
        with y show False 
          by (simp add: \<sigma>(2) clause_subst_compose literal_subst_compose)
      qed

      from empty max_lit show ?thesis
        by simp   
    next
      case False

      then have "L \<in># select\<^sub>G (to_ground_clause (P \<cdot> \<theta>))"
        using ground_eq_resolutionI(3) by blast

      then have x: "(s !\<approx> s') \<cdot>l \<theta> \<in># select P \<cdot> \<theta>"
        using select
        by (metis L(1) ground_literal_in_ground_clause(3))

      then have "Neg (Upair s s') \<in># select P"
        using select
        sorry

      with False show ?thesis 
        using ground_eq_resolutionI(3)
        by auto
    qed
  next
    show "C \<cdot> \<sigma> = C \<cdot> \<sigma>"
      by (rule refl)
  qed

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by simp

  have "to_ground_clause (C \<cdot> \<theta>) \<in> G_T (C \<cdot> \<sigma>) \<theta>"
    unfolding G_T_def clause_subst_compose[symmetric] \<sigma>_\<theta>
    by simp
   
  with eq show ?thesis
    unfolding G_T_def
    by blast
qed

lemma eq_resolution_iff_ground_eq_resolution:
  "eq_resolution (to_clause P) (to_clause C) \<longleftrightarrow> ground.ground_eq_resolution P C" 
proof (rule iffI)
  assume "eq_resolution (to_clause P) (to_clause C)"
  thus "ground.ground_eq_resolution P C"
  proof(cases rule: eq_resolution.cases)
    case (eq_resolutionI L P' t\<^sub>1 t\<^sub>2 \<mu>)
    
    then have "is_ground_clause P'"
      using ground_clause_is_ground[of P]
      by fastforce
  
    then have P'_is_C: "P' = to_clause C"
      using subst_ground_clause eq_resolutionI(5) by simp

    have [intro]: "is_ground_literal L" "is_ground_term t\<^sub>1" "is_ground_term t\<^sub>2" 
      using eq_resolutionI ground_literal_in_ground_clause(2)[of L P] vars_literal_split
      by fastforce+

    then have "t\<^sub>1 = t\<^sub>2"
      using eq_resolutionI ground_imgu_equals[of t\<^sub>1  t\<^sub>2]
      by simp

    then have [simp]: "L \<cdot>l \<mu> = L"
      using eq_resolutionI ground_literal_in_ground_clause(1)
      by (metis ground_clause_is_ground subst_ground_literal union_single_eq_member)
     
    show ?thesis 
    proof (rule ground.ground_eq_resolutionI)
      from eq_resolutionI show "P = add_mset (to_ground_literal L) C"
        by (metis P'_is_C to_clause_inverse to_ground_clause_def image_mset_add_mset)
    next
      show "to_ground_literal L = Neg (Upair (to_ground_term t\<^sub>1) (to_ground_term t\<^sub>1))"
        using \<open>t\<^sub>1 = t\<^sub>2\<close>
        by (simp add: to_ground_literal_def to_ground_atom_def eq_resolutionI)
    next
      show "(select\<^sub>G P = {#} \<and> ground.is_maximal_lit (to_ground_literal L) P) \<or> to_ground_literal L \<in># select\<^sub>G P"
      proof(cases "select\<^sub>G P")
        case empty
        then show ?thesis 
          using 
            eq_resolutionI(4) 
            to_ground_literal_inverse[OF \<open>is_ground_literal L\<close>]
            is_maximal\<^sub>G\<^sub>l_iff_is_maximal\<^sub>l[of P "to_ground_literal L"]
            
          unfolding to_ground_clause_def
          apply auto
          using eq_resolutionI(4) 
          sorry
          (*by simp*)
      next
        case add
        then show ?thesis
          sorry
          (*using eq_resolutionI(4) select\<^sub>G_empty_iff_select_empty
          by (metis empty_not_add_mset test)*)
      qed
    qed
  qed
next
  assume "ground.ground_eq_resolution P C"
  thus "eq_resolution (to_clause P) (to_clause C)"
   proof(cases P C rule: ground.ground_eq_resolution.cases)
   case (ground_eq_resolutionI L t)
    show ?thesis
    proof (rule eq_resolutionI)
      show "to_clause P = add_mset (to_literal L) (to_clause C)"
        using \<open>P = add_mset L C\<close> 
        unfolding to_clause_def
        by simp
    next
      show "to_literal L = Neg (Upair (to_term t) (to_term t))"
        using \<open>L = Neg (Upair t t)\<close>
        unfolding to_literal_def to_atom_def
        by simp
    next
      show "term_subst.is_imgu Var {{to_term t, to_term t}}"
        by simp
    next
      show "select (to_clause P) = {#} \<and> is_maximal\<^sub>l (to_literal L \<cdot>l Var) (to_clause P \<cdot> Var) 
          \<or> to_literal L \<in># select (to_clause P)"
        using 
          ground_eq_resolutionI
          is_maximal\<^sub>G\<^sub>l_iff_is_maximal\<^sub>l
          ground_literal_in_ground_clause(2) 
          select_subset
        unfolding to_ground_clause_def
        apply auto
        subgoal sorry
        subgoal sorry
        sorry
        (*by fastforce*)
    next
      show "to_clause C = to_clause C \<cdot> Var"
        by simp
    qed
  qed
qed

lemma eq_factoring_iff_ground_eq_factoring:
  "eq_factoring (to_clause P) (to_clause C) \<longleftrightarrow> ground.ground_eq_factoring P C"
proof (rule iffI)
  assume "eq_factoring (to_clause P) (to_clause C)"
  thus "ground.ground_eq_factoring P C"
  proof(cases rule: eq_factoring.cases)
    case (eq_factoringI L\<^sub>1 L\<^sub>2 P' s\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

    have is_ground_literal [intro]: "is_ground_literal L\<^sub>1"
      using eq_factoringI ground_clause_is_ground vars_clause_add_mset 
      by (metis sup_eq_bot_iff)

    have is_ground_trm [intro]: 
      "is_ground_term s\<^sub>1" 
      "is_ground_term s\<^sub>1'" 
      "is_ground_term t\<^sub>2"
      using eq_factoringI ground_clause_is_ground vars_literal_split vars_clause_add_mset
      by (metis sup_eq_bot_iff)+

    then have "s\<^sub>1 = t\<^sub>2"
      using ground_imgu_equals local.eq_factoringI(6) by blast

    have ground_substs [simp]: "L\<^sub>1 \<cdot>l \<mu> = L\<^sub>1" "s\<^sub>1 \<cdot>t \<mu> = s\<^sub>1" "s\<^sub>1' \<cdot>t \<mu> = s\<^sub>1'"
      using eq_factoringI is_ground_trm is_ground_literal
      by simp_all

    show ?thesis 
    proof (rule ground.ground_eq_factoringI)
      show "P = add_mset (to_ground_literal L\<^sub>1) (add_mset (to_ground_literal L\<^sub>2) (to_ground_clause P'))"
        by (metis to_clause_inverse to_ground_clause_def image_mset_add_mset eq_factoringI(1))
    next 
      show "to_ground_literal L\<^sub>1 = (to_ground_term s\<^sub>1 \<approx> to_ground_term s\<^sub>1')"
        by (simp add: to_ground_literal_def to_ground_atom_def eq_factoringI(2))
    next
      show "to_ground_literal L\<^sub>2 = (to_ground_term s\<^sub>1 \<approx> to_ground_term t\<^sub>2')"
        by (simp add: \<open>s\<^sub>1 = t\<^sub>2\<close> to_ground_literal_def to_ground_atom_def eq_factoringI(3))
    next
      show "select\<^sub>G P = {#}"
        sorry (*by (simp add: to_ground_clause_def eq_factoringI(4) wtf)*)
    next 
      show "ground.is_maximal_lit (to_ground_literal L\<^sub>1) P"
        using   
          eq_factoringI(4) 
          is_maximal\<^sub>G\<^sub>l_iff_is_maximal\<^sub>l 
          to_ground_literal_inverse[OF \<open>is_ground_literal L\<^sub>1\<close>]
        by simp
    next
      show "to_ground_term s\<^sub>1' \<prec>\<^sub>t\<^sub>G to_ground_term s\<^sub>1"
        using eq_factoringI(5)  
          less\<^sub>t\<^sub>G_total 
          to_ground_term_inverse[OF \<open>is_ground_term s\<^sub>1'\<close>]
          to_ground_term_inverse[OF \<open>is_ground_term s\<^sub>1\<close>]
          less\<^sub>t\<^sub>G_less\<^sub>t
          ground_substs
        by (metis reflclp_iff totalpD)
    next
      have [simp]: "add_mset (s\<^sub>1 \<approx> t\<^sub>2') (add_mset (Neg (Upair s\<^sub>1' t\<^sub>2')) P') \<cdot> \<mu>
          = add_mset (s\<^sub>1 \<approx> t\<^sub>2') (add_mset (Neg (Upair s\<^sub>1' t\<^sub>2')) P')"
        using is_ground_trm ground_clause_is_ground eq_factoringI subst_ground_clause
        by (metis to_clause_def msed_map_invR vars_literal_split vars_clause_add_mset vars_literal)

      then show "C = 
            add_mset 
               (Neg (Upair (to_ground_term s\<^sub>1') (to_ground_term t\<^sub>2'))) 
               (add_mset (to_ground_term s\<^sub>1 \<approx> to_ground_term t\<^sub>2') 
               (to_ground_clause P'))"
        unfolding to_clause_def 
        using eq_factoringI(7) to_ground_atom_def to_ground_literal_def 
              to_ground_clause_def to_clause_inverse add_mset_commute
        by (metis image_mset_add_mset literal.simps(9, 10) map_uprod_simps)
    qed
  qed
next
  assume "ground.ground_eq_factoring P C"
  thus "eq_factoring (to_clause P) (to_clause C)"
  proof(cases P C rule: ground.ground_eq_factoring.cases)
    case (ground_eq_factoringI L\<^sub>1 L\<^sub>2 P' t t' t'')
    show ?thesis 
    proof(rule eq_factoringI)
      show "to_clause P = add_mset (to_literal L\<^sub>1) (add_mset (to_literal L\<^sub>2) (to_clause P'))"
        by (simp add: to_clause_def ground_eq_factoringI(1))
    next
      show "to_literal L\<^sub>1 = to_term t \<approx> to_term t'"
        by (simp add: ground_eq_factoringI(2) to_literal_def to_atom_def)
    next
      show "to_literal L\<^sub>2 =  to_term t \<approx> to_term t''"
        by (simp add: ground_eq_factoringI(3) to_literal_def to_atom_def)
    next
      show "select (to_clause P) = {#} \<and> is_maximal\<^sub>l (to_literal L\<^sub>1 \<cdot>l Var) (to_clause P \<cdot> Var)"
        using  ground_eq_factoringI(4,5) is_maximal\<^sub>G\<^sub>l_iff_is_maximal\<^sub>l
        unfolding to_ground_clause_def
        (* sorry by simp *)
        sorry
    next
      show "\<not> to_term t \<cdot>t Var \<preceq>\<^sub>t to_term t' \<cdot>t Var" 
        using ground_eq_factoringI(6) asympD 
        unfolding less\<^sub>t\<^sub>G_less\<^sub>t
        by force
    next   
      show "term_subst.is_imgu Var {{to_term t, to_term t}}"
        by simp
    next
      show "to_clause C = 
              add_mset 
                  (to_term t \<approx> to_term t'') 
                  (add_mset (Neg (Upair (to_term t') (to_term t''))) 
                  (to_clause P')) 
              \<cdot> Var"
        by (simp add: to_clause_def ground_eq_factoringI(7) to_literal_def to_atom_def)
    qed
  qed
qed

lemma superposition_iff_ground_superposition:
   "superposition (to_clause P1) (to_clause P2) (to_clause C) \<longleftrightarrow> ground.ground_superposition P1 P2 C"
proof(rule iffI)
  assume "superposition (to_clause P1) (to_clause P2) (to_clause C)"
  thus " ground.ground_superposition P1 P2 C"
  proof(cases rule: superposition.cases)
    case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

    have \<P>_ground: "\<And>a. is_ground_atom a \<longleftrightarrow> is_ground_literal (\<P> a)" 
      using superpositionI(12) by fastforce

    have is_ground_L\<^sub>1 [intro]: "is_ground_literal L\<^sub>1"
      using superpositionI(4) is_ground_clause_add_mset ground_clause_is_ground
      by metis
      
    have is_ground_L\<^sub>2 [intro]: "is_ground_literal L\<^sub>2"
      using superpositionI(5) ground_literal_in_ground_clause(2)[of L\<^sub>2 P2] 
      by simp

    have is_ground_P\<^sub>1' [intro]: "is_ground_clause P\<^sub>1'"
      using superpositionI(4) is_ground_clause_add_mset ground_clause_is_ground 
      by metis

    have is_ground_P\<^sub>2' [intro]: "is_ground_clause P\<^sub>2'"
      using superpositionI(5) is_ground_clause_add_mset ground_clause_is_ground 
      by metis

    have is_ground_s\<^sub>1_u\<^sub>1 [intro]: "is_ground_term s\<^sub>1\<langle>u\<^sub>1\<rangle>"
      using is_ground_L\<^sub>1 superpositionI(7) ground_terms_in_ground_atom[of "s\<^sub>1\<langle>u\<^sub>1\<rangle>" s\<^sub>1'] \<P>_ground
      by blast

    then have is_ground_s\<^sub>1 [intro]: "is_ground_context s\<^sub>1"
      by simp
      
    have is_ground_u\<^sub>1 [intro]: "is_ground_term u\<^sub>1"
      using is_ground_s\<^sub>1_u\<^sub>1 by auto
   
    have is_ground_s\<^sub>1' [intro]: "is_ground_term s\<^sub>1'"
      using superpositionI(7) is_ground_L\<^sub>1 ground_terms_in_ground_atom(2) \<P>_ground
      by metis

    have is_ground_t\<^sub>2 [intro]: "is_ground_term t\<^sub>2"
      using superpositionI(8) is_ground_L\<^sub>2
      by (simp add: ground_terms_in_ground_atom)

    have is_ground_t\<^sub>2' [intro]: "is_ground_term t\<^sub>2'"
      using superpositionI(8) is_ground_L\<^sub>2
      by (simp add: ground_terms_in_ground_atom)

    have "u\<^sub>1 = t\<^sub>2"
      using superpositionI(10) ground_imgu_equals is_ground_t\<^sub>2 is_ground_u\<^sub>1 by auto
    
    obtain \<P>' :: "'f gterm uprod \<Rightarrow> 'f gterm uprod literal"
      where \<P>': "\<P>' = (if \<P> = Pos then Pos else Neg)"
      by simp
                              
    show ?thesis
    proof (rule ground.ground_superpositionI)
      show "P1 = add_mset (to_ground_literal L\<^sub>1) (to_ground_clause P\<^sub>1')"
        using superpositionI(4) to_ground_clause_add_mset
        by blast
    next
      show "P2 = add_mset (to_ground_literal L\<^sub>2) (to_ground_clause P\<^sub>2')"
        using superpositionI(5) to_ground_clause_add_mset
        by blast
    next
      show "P2 \<prec>\<^sub>c\<^sub>G P1"
        using 
          superpositionI(11) 
          not_less_eq\<^sub>c[of "to_clause P1" "to_clause P2"]
          less\<^sub>c_less\<^sub>c\<^sub>G
        by auto
    next
      show "\<P>' \<in> {Pos, Neg}"
        using superpositionI(6) 
        by (simp add: \<P>')
    next 
      show "to_ground_literal L\<^sub>1 = \<P>' (Upair (to_ground_context s\<^sub>1)\<langle>to_ground_term u\<^sub>1\<rangle>\<^sub>G (to_ground_term s\<^sub>1'))"
        unfolding 
          \<P>'
          superpositionI(7)
          ground_term_with_context(1)[OF is_ground_s\<^sub>1 is_ground_u\<^sub>1]
          ground_terms_in_ground_atom(1)[
            OF ground_term_with_context_is_ground(4), 
            OF is_ground_s\<^sub>1 is_ground_u\<^sub>1 is_ground_s\<^sub>1'
          ]
        using superpositionI(6)
        by(auto simp: ground_atom_in_ground_literal)  
    next
      show "to_ground_literal L\<^sub>2 = to_ground_term u\<^sub>1 \<approx> to_ground_term t\<^sub>2'"
        by (simp add: \<open>u\<^sub>1 = t\<^sub>2\<close> to_ground_literal_def superpositionI(8) to_ground_atom_def)
    next
      note is_ground_s\<^sub>1_u\<^sub>1 = ground_term_with_context_is_ground(4)[OF is_ground_s\<^sub>1 is_ground_u\<^sub>1]
      
      show "to_ground_term s\<^sub>1' \<prec>\<^sub>t\<^sub>G (to_ground_context s\<^sub>1)\<langle>to_ground_term u\<^sub>1\<rangle>\<^sub>G"
        using superpositionI(15) 
          
        unfolding 
          term_subst.subst_ident_if_ground[OF is_ground_s\<^sub>1_u\<^sub>1]
          term_subst.subst_ident_if_ground[OF is_ground_s\<^sub>1']
          not_less_eq\<^sub>t[OF is_ground_s\<^sub>1' is_ground_s\<^sub>1_u\<^sub>1]
          less\<^sub>t\<^sub>G_less\<^sub>t
          to_ground_term_inverse[OF is_ground_s\<^sub>1']
          ground_term_with_context(1)[OF is_ground_s\<^sub>1 is_ground_u\<^sub>1]
          to_ground_term_inverse[OF is_ground_s\<^sub>1_u\<^sub>1].
    next
      show "to_ground_term t\<^sub>2' \<prec>\<^sub>t\<^sub>G to_ground_term u\<^sub>1"
        using superpositionI(16)
        unfolding 
          \<open>u\<^sub>1 = t\<^sub>2\<close>
          term_subst.subst_ident_if_ground[OF is_ground_t\<^sub>2] 
          term_subst.subst_ident_if_ground[OF is_ground_t\<^sub>2']
          not_less_eq\<^sub>t[OF is_ground_t\<^sub>2' is_ground_t\<^sub>2] 
          less\<^sub>t_less\<^sub>t\<^sub>G[OF is_ground_t\<^sub>2' is_ground_t\<^sub>2].
    next 
      have totalp_ground: "totalp_on (set_mset (to_clause P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)) (\<prec>\<^sub>l)"
        by (simp add: less\<^sub>l_total_on set_mset_to_clause_to_literal)

      show "\<P>' = Pos \<and> select\<^sub>G P1 = {#} \<and> ground.is_strictly_maximal_lit  (to_ground_literal L\<^sub>1) P1 
          \<or> \<P>' = Neg 
              \<and> (select\<^sub>G P1 = {#} \<and> ground.is_maximal_lit (to_ground_literal L\<^sub>1) P1 \<or> to_ground_literal L\<^sub>1 \<in># select\<^sub>G P1)"
      proof(cases "\<P>' = Pos")
        case True
        then show ?thesis
          using 
            superpositionI(12)
            is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l[of P1 "to_ground_literal L\<^sub>1"]
          unfolding 
            \<P>' 
            to_ground_clause_def 
            subst_ground_literal[OF is_ground_L\<^sub>1] 
            to_ground_literal_inverse[OF is_ground_L\<^sub>1]
            subst_ground_clause[OF ground_clause_is_ground]
          sorry
          (*by (metis image_mset_empty literal.distinct(1))*)
      next
        case False
        then show ?thesis 
          using superpositionI(12)
          unfolding   
            \<P>' 
            to_ground_clause_def 
            subst_ground_literal[OF is_ground_L\<^sub>1] 
            subst_ground_clause[OF ground_clause_is_ground]
            is_maximal\<^sub>G\<^sub>l_iff_is_maximal\<^sub>l[
              of P1 "to_ground_literal L\<^sub>1", 
              unfolded to_ground_literal_inverse[OF is_ground_L\<^sub>1]
            ]
          sorry
          (*by auto*)
      qed 
    next 
      show "select\<^sub>G P2 = {#}"
        sorry (*by (simp add: to_ground_clause_def superpositionI(13) wtf)*)
    next 
      note is_strictly_maximal = is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l[
          of P2 "to_ground_literal L\<^sub>2", 
          unfolded to_ground_literal_inverse[OF is_ground_L\<^sub>2]
      ]

      show "ground.is_strictly_maximal_lit  (to_ground_literal L\<^sub>2) P2"
        using superpositionI(14)
        unfolding 
          subst_ground_literal[OF is_ground_L\<^sub>2] 
          subst_ground_clause[OF ground_clause_is_ground]
          is_strictly_maximal.
    next 
      note ground_context = ground_term_with_context_is_ground(4)[OF is_ground_s\<^sub>1 is_ground_t\<^sub>2']

      then have "is_ground_atom (Upair s\<^sub>1\<langle>t\<^sub>2'\<rangle> s\<^sub>1')"
        using is_ground_s\<^sub>1' ground_terms_in_ground_atom
        by metis
     
      then have ground_cls: "is_ground_clause (add_mset (\<P> (Upair s\<^sub>1\<langle>t\<^sub>2'\<rangle> s\<^sub>1')) (P\<^sub>1' + P\<^sub>2'))"
        using superpositionI(12) is_ground_P\<^sub>1' is_ground_P\<^sub>2' \<P>_ground
        by simp

      show "C = add_mset 
                  (\<P>' (Upair (to_ground_context s\<^sub>1)\<langle>to_ground_term t\<^sub>2'\<rangle>\<^sub>G (to_ground_term s\<^sub>1'))) 
                  (to_ground_clause P\<^sub>1' + to_ground_clause P\<^sub>2')"
        using 
          superpositionI(12, 17)
          to_ground_clause_add_mset[of C  "\<P> (Upair s\<^sub>1\<langle>t\<^sub>2'\<rangle> s\<^sub>1')" "(P\<^sub>1' + P\<^sub>2')"]
        unfolding 
          \<P>' 
          subst_ground_clause[OF is_ground_P\<^sub>1']
          subst_ground_clause[OF is_ground_P\<^sub>2']
          term_subst.subst_ident_if_ground[OF is_ground_t\<^sub>2'] 
          term_subst.subst_ident_if_ground[OF is_ground_s\<^sub>1'] 
          subst_ground_context[OF is_ground_s\<^sub>1]
          subst_ground_clause[OF ground_cls]
          ground_term_with_context(1)[OF is_ground_s\<^sub>1 is_ground_t\<^sub>2']
          ground_terms_in_ground_atom(1)[
            OF ground_term_with_context_is_ground(4)[OF  is_ground_s\<^sub>1 is_ground_t\<^sub>2']
            is_ground_s\<^sub>1'
          ]
        by(auto simp: ground_atom_in_ground_literal)
      qed
    qed
next
  assume "ground.ground_superposition P1 P2 C"
  thus "superposition (to_clause P1) (to_clause P2) (to_clause C)"
  proof(cases rule: ground.ground_superposition.cases)
    case (ground_superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s t s' t')

    obtain \<P>' :: "('f, 'v) term uprod \<Rightarrow> ('f, 'v) term uprod literal" 
      where \<P>': "\<P>' = (if \<P> = Pos then Pos else Neg)"
      by simp

    have \<P>'_pos_or_neg: "\<P>' = Neg \<or> \<P>' = Pos"
      using ground_superpositionI(4)
      unfolding \<P>' to_literal_def
      by simp

    show ?thesis
    proof(rule superpositionI)
      show "term_subst.is_renaming Var"
        by simp
    next
      show "term_subst.is_renaming Var"
        by simp
    next
      show "vars_clause (to_clause P1 \<cdot> Var) \<inter> vars_clause (to_clause P2 \<cdot> Var) = {}"
        by simp
    next
      show "to_clause P1 = add_mset (to_literal L\<^sub>1) (to_clause P\<^sub>1')"
        by (simp add: to_clause_def ground_superpositionI(1))
    next
      show "to_clause P2 = add_mset (to_literal L\<^sub>2) (to_clause P\<^sub>2')"
        by (simp add: to_clause_def ground_superpositionI(2))
    next
      show "\<P>' \<in> {Pos, Neg}"
        using \<P>'_pos_or_neg by auto
    next
      show "to_literal L\<^sub>1 = \<P>' (Upair (to_context s) \<langle>to_term t\<rangle> (to_term s'))"
        using ground_superpositionI(5, 9) 
        unfolding \<P>'
        by (smt (verit) ground_term_with_context(3) literal.simps(10) literal.simps(9) map_uprod_simps to_atom_def to_literal_def)
    next
      show "to_literal L\<^sub>2 = (to_term t) \<approx> (to_term t')"
        by (simp add: ground_superpositionI(6) to_literal_def to_atom_def)
    next 
      show "is_Fun (to_term t)"
        by (rule gterm_is_fun)
    next
      show "term_subst.is_imgu Var {{to_term t \<cdot>t Var, to_term t \<cdot>t Var}}"
        by simp
    next
      show " \<not> (\<prec>\<^sub>c)\<^sup>=\<^sup>= (to_clause P1 \<cdot> Var \<cdot> Var) (to_clause P2 \<cdot> Var \<cdot> Var)"
        using ground_superpositionI(3)  
        unfolding
          subst_clause_Var_ident
          not_less_eq\<^sub>c[OF ground_clause_is_ground ground_clause_is_ground]
          less\<^sub>c\<^sub>G_less\<^sub>c.
    next 
      show 
          "\<P>' = Pos 
            \<and> select (to_clause P1) = {#} 
            \<and> is_strictly_maximal\<^sub>l  (to_literal L\<^sub>1 \<cdot>l Var \<cdot>l Var) (to_clause P1 \<cdot> Var \<cdot> Var) 
         \<or> \<P>' = Neg 
            \<and> (select (to_clause P1) = {#} 
            \<and> is_maximal\<^sub>l (to_literal L\<^sub>1 \<cdot>l Var \<cdot>l Var) (to_clause P1 \<cdot> Var \<cdot> Var) 
            \<or> to_literal L\<^sub>1 \<in># select (to_clause P1))"
        proof(cases "\<P> = Pos")
          case True
          with ground_superpositionI(9) show ?thesis
            unfolding \<P>' to_ground_clause_def
            using literals_distinct is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
            (*by auto *) sorry
        next
          case False
          with ground_superpositionI(9) show ?thesis
            unfolding \<P>' to_ground_clause_def
            using literals_distinct is_maximal\<^sub>G\<^sub>l_iff_is_maximal\<^sub>l select_from_ground_clause(2)
            (* by auto*)
            sorry
        qed
    next
      show "select (to_clause P2) = {#}"
        using ground_superpositionI(10)
        unfolding to_ground_clause_def
        (*by simp*) sorry
    next
      show "is_strictly_maximal\<^sub>l (to_literal L\<^sub>2 \<cdot>l Var \<cdot>l Var) (to_clause P2 \<cdot> Var \<cdot> Var)"
        using ground_superpositionI(11) is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
        by simp
    next
      show "\<not> (to_context s)\<langle>to_term t\<rangle> \<cdot>t Var \<cdot>t Var \<preceq>\<^sub>t to_term s' \<cdot>t Var \<cdot>t Var"
        using ground_superpositionI(7)  
        unfolding 
          term_subst.subst_id_subst 
          not_less_eq\<^sub>t[OF ground_term_is_ground ground_term_is_ground]
          less\<^sub>t\<^sub>G_less\<^sub>t
          ground_term_with_context.
    next
      show "\<not> to_term t \<cdot>t Var \<cdot>t Var \<preceq>\<^sub>t to_term t' \<cdot>t Var \<cdot>t Var"
        using ground_superpositionI(8)
        unfolding 
          term_subst.subst_id_subst 
          not_less_eq\<^sub>t[OF ground_term_is_ground ground_term_is_ground]
          less\<^sub>t\<^sub>G_less\<^sub>t.
    next
      show "to_clause C = add_mset 
            (\<P>' (Upair (to_context s \<cdot>t\<^sub>c Var)\<langle>to_term t' \<cdot>t Var\<rangle> (to_term s' \<cdot>t Var))) 
              (to_clause P\<^sub>1' \<cdot> Var + to_clause P\<^sub>2' \<cdot> Var) \<cdot> Var"
      proof(cases "\<P>' = Pos")
        case True
        then show ?thesis
          using ground_superpositionI(12) 
          unfolding \<P>'
          by (smt (verit) ground_term_with_context(3) image_mset_add_mset image_mset_union literal.simps(9) literals_distinct(2) map_uprod_simps subst_apply_term_ctxt_apply_distrib subst_clause_Var_ident term_subst.subst_id_subst to_atom_def to_clause_def to_literal_def)
      next
        case False
        then have "\<P> = Neg"
          using ground_superpositionI(4)
          unfolding \<P>'
          by auto
     
        then show ?thesis
          using ground_superpositionI(12)
          unfolding \<P>'
          by (simp add: ground_term_with_context(3) to_atom_def to_clause_def to_literal_def)
      qed
    qed  
  qed
qed

subsubsection \<open>Alternative Specification of the Superposition Rule\<close>

inductive pos_superposition ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
where
  pos_superpositionI: "
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    vars_clause (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    L\<^sub>1 = (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = (t\<^sub>2 \<approx> t\<^sub>2') \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> (s\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    pos_superposition P\<^sub>1 P\<^sub>2 C"

lemma superposition_if_pos_superposition:
  assumes "pos_superposition P\<^sub>1 P\<^sub>2 C"
  shows "superposition P\<^sub>1 P\<^sub>2 C"
  using assms
proof (cases P\<^sub>1 P\<^sub>2 C rule: pos_superposition.cases)
  case (pos_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  then show ?thesis
    using superpositionI
    by fast
qed

inductive neg_superposition ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
where
  neg_superpositionI: "
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    vars_clause (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    L\<^sub>1 = Neg (Upair s\<^sub>1\<langle>u\<^sub>1\<rangle> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = (t\<^sub>2 \<approx> t\<^sub>2') \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<and> is_maximal\<^sub>l (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> L\<^sub>1 \<in># select P\<^sub>1 \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (Neg (Upair (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle>  (s\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    neg_superposition P\<^sub>1 P\<^sub>2 C"

lemma superposition_if_neg_superposition:
  assumes "neg_superposition P\<^sub>1 P\<^sub>2 C"
  shows "superposition P\<^sub>1 P\<^sub>2 C"
  using assms
proof (cases P\<^sub>1 P\<^sub>2 C rule: neg_superposition.cases)
  case (neg_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  then show ?thesis
    using superpositionI
    by fast
qed

lemma superposition_iff_pos_or_neg:
  "superposition P\<^sub>1 P\<^sub>2 C \<longleftrightarrow> pos_superposition P\<^sub>1 P\<^sub>2 C \<or> neg_superposition P\<^sub>1 P\<^sub>2 C"
proof (rule iffI)
  assume "superposition P\<^sub>1 P\<^sub>2 C"
  thus "pos_superposition P\<^sub>1 P\<^sub>2 C \<or> neg_superposition P\<^sub>1 P\<^sub>2 C"
  proof (cases P\<^sub>1 P\<^sub>2 C rule: superposition.cases)
    case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
    then show ?thesis
      using pos_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>]
      using neg_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>]
      by metis
  qed
next
  assume "pos_superposition P\<^sub>1 P\<^sub>2 C \<or> neg_superposition P\<^sub>1 P\<^sub>2 C"
  thus "superposition P\<^sub>1 P\<^sub>2 C"
    using superposition_if_neg_superposition superposition_if_pos_superposition by metis
qed


subsection \<open>First-Order Layer\<close>

definition F_Inf :: "('f, 'v) atom clause inference set" where
  "F_Inf \<equiv> 
    {Infer [P\<^sub>2, P\<^sub>1] C | P\<^sub>2 P\<^sub>1 C. superposition P\<^sub>1 P\<^sub>2 C} \<union>
    {Infer [P] C | P C. eq_resolution P C} \<union>
    {Infer [P] C | P C. eq_factoring P C}"

abbreviation F_Bot :: "('f, 'v) atom clause set" where
  "F_Bot \<equiv> {{#}}"

abbreviation true_clause :: 
  "'f ground_atom interp \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" (infix "\<TTurnstile>\<^sub>C" 50)  where
  "I \<TTurnstile>\<^sub>C C \<equiv> \<forall>\<theta>. term_subst.is_ground_subst \<theta> \<longrightarrow> I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"

abbreviation true_clauses :: 
  "'f ground_atom interp \<Rightarrow> ('f, 'v) atom clause set \<Rightarrow> bool" (infix "\<TTurnstile>\<^sub>C\<^sub>s" 50) where
  "I \<TTurnstile>\<^sub>C\<^sub>s \<C> \<equiv> \<forall>C\<in> \<C>. I \<TTurnstile>\<^sub>C C"

definition F_entails :: "('f, 'v) atom clause set \<Rightarrow> ('f, 'v) atom clause set \<Rightarrow> bool" where
  "F_entails N\<^sub>1 N\<^sub>2 \<longleftrightarrow> (\<forall>(I :: 'f gterm rel). 
    refl I \<longrightarrow> trans I \<longrightarrow> sym I \<longrightarrow> compatible_with_gctxt I \<longrightarrow>
    (\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile>\<^sub>C\<^sub>s N\<^sub>1 \<longrightarrow>
    (\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile>\<^sub>C\<^sub>s N\<^sub>2)"
 
lemma eq_resolution_sound:
  assumes step: "eq_resolution P C"
  shows "F_entails {P} {C}"
  using step
proof (cases P C rule: eq_resolution.cases)
  case (eq_resolutionI L P' s\<^sub>1 s\<^sub>2 \<mu>)
  have 
    "\<And>I \<theta>. \<lbrakk>
        refl I; 
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (P \<cdot> \<sigma>); 
        term_subst.is_ground_subst \<theta>
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"
  proof-
    fix I :: "'f gterm rel" and \<theta> :: "'v \<Rightarrow> ('f, 'v) Term.term"
    let ?I = "(\<lambda>(x, y). Upair x y) ` I"
    let ?P = "to_ground_clause (P \<cdot> \<mu> \<cdot> \<theta>)"
    let ?L = "to_ground_literal (L \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?P' = "to_ground_clause (P' \<cdot> \<mu> \<cdot> \<theta>)"
    let ?s\<^sub>1 = "to_ground_term (s\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?s\<^sub>2 = "to_ground_term (s\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"

     assume 
       ground_subst: "term_subst.is_ground_subst \<theta>" and 
       refl_I: "refl I" and 
       premise: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> to_ground_clause (P \<cdot> \<sigma>)"

     have "?I \<TTurnstile> ?P"
       using 
         premise[rule_format, of "\<mu> \<odot> \<theta>", OF ground_subst_compose[OF ground_subst]]
         clause_subst_compose
       by metis
      
     then obtain L' where L'_in_P: "L' \<in># ?P" and I_models_L': "?I \<TTurnstile>l L'"
       by (auto simp: true_cls_def)

     have [simp]: "?P = add_mset ?L ?P'"
       by (simp add: to_ground_clause_def local.eq_resolutionI(1) subst_clause_add_mset)

     have [simp]: "?L = (Neg (Upair ?s\<^sub>1 ?s\<^sub>2))"
       unfolding to_ground_literal_def eq_resolutionI(2) to_ground_atom_def
       by (simp add: subst_atom_def subst_literal)
       
     have [simp]: "?s\<^sub>1 = ?s\<^sub>2"
       using is_imgu_equals[OF eq_resolutionI(3)] by simp
      
     have "is_neg ?L"
       by (simp add: to_ground_literal_def eq_resolutionI(2) subst_literal)

     show "?I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"
      proof(cases "L' = ?L")
       case True
   
       then have "?I \<TTurnstile>l (Neg (atm_of ?L))"
         using I_models_L' by simp
  
       moreover have "atm_of L' \<in> ?I"
         using True reflD[OF refl_I, of ?s\<^sub>1] by auto
  
       ultimately show ?thesis
         using True by blast
     next
       case False
       then have "L' \<in># to_ground_clause (P' \<cdot> \<mu> \<cdot> \<theta>)"
         using L'_in_P by force
  
       then have "L' \<in># to_ground_clause (C \<cdot> \<theta>)"
         unfolding eq_resolutionI.
  
       then show ?thesis
         using I_models_L' by blast
     qed
   qed

  then show ?thesis 
    unfolding true_clss_singleton F_entails_def 
    by simp
qed

lemma eq_factoring_sound:
  assumes step: "eq_factoring P C"
  shows "F_entails {P} {C}"
  using step
proof (cases P C rule: eq_factoring.cases)
  case (eq_factoringI L\<^sub>1 L\<^sub>2 P' s\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  have 
    "\<And>I \<theta>. \<lbrakk>
        trans I; 
        sym I;
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (P \<cdot> \<sigma>); 
        term_subst.is_ground_subst \<theta>
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"
  proof-
    fix I :: "'f gterm rel" and \<theta> :: "'v \<Rightarrow> ('f, 'v) Term.term"
    let ?I = "(\<lambda>(x, y). Upair x y) ` I"
    let ?P = "to_ground_clause (P \<cdot> \<mu> \<cdot> \<theta>)"
    let ?P' = "to_ground_clause (P' \<cdot> \<mu> \<cdot> \<theta>)"
    let ?L\<^sub>1 = "to_ground_literal (L\<^sub>1 \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?L\<^sub>2 = "to_ground_literal (L\<^sub>2 \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?s\<^sub>1 = "to_ground_term (s\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?s\<^sub>1' = "to_ground_term (s\<^sub>1' \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2 = "to_ground_term (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2' = "to_ground_term (t\<^sub>2' \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?C = "to_ground_clause (C \<cdot> \<theta>)"

    assume 
      ground_subst: "term_subst.is_ground_subst \<theta>" and 
      trans_I: "trans I" and 
      sym_I: "sym I" and 
      premise: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> to_ground_clause (P \<cdot> \<sigma>)"

    have "?I \<TTurnstile> ?P"
       using 
         premise[rule_format, of "\<mu> \<odot> \<theta>", OF ground_subst_compose[OF ground_subst]]
         clause_subst_compose
       by metis

    then obtain L' where L'_in_P: "L' \<in># ?P" and I_models_L': "?I \<TTurnstile>l L'"
      by (auto simp: true_cls_def)

    then have s\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?s\<^sub>1"
      using is_imgu_equals[OF eq_factoringI(6)]
      by simp

    have L\<^sub>1: "?L\<^sub>1 = ?s\<^sub>1 \<approx> ?s\<^sub>1'"
      unfolding to_ground_literal_def eq_factoringI(2) to_ground_atom_def
      by (simp add: subst_atom_def subst_literal)

    have L\<^sub>2: "?L\<^sub>2 = ?t\<^sub>2 \<approx> ?t\<^sub>2'"
      unfolding to_ground_literal_def eq_factoringI(3) to_ground_atom_def
      by (simp add: subst_atom_def subst_literal)

    have C: "?C = add_mset (?s\<^sub>1 \<approx> ?t\<^sub>2') (add_mset (Neg (Upair ?s\<^sub>1' ?t\<^sub>2')) ?P')"
      unfolding eq_factoringI 
      by (simp add: to_ground_clause_def to_ground_literal_def subst_atom_def subst_clause_add_mset subst_literal
            to_ground_atom_def)

    show "?I \<TTurnstile> ?C"
    proof(cases "L' = ?L\<^sub>1 \<or> L' = ?L\<^sub>2")
      case True
      then have "I \<TTurnstile>l Pos (?s\<^sub>1, ?s\<^sub>1') \<or> I \<TTurnstile>l Pos (?s\<^sub>1, ?t\<^sub>2')"
        using ground.true_lit_uprod_iff_true_lit_prod[OF sym_I] I_models_L'
        by (metis L\<^sub>1 L\<^sub>2 s\<^sub>1_equals_t\<^sub>2)

      then have "I \<TTurnstile>l Pos (?s\<^sub>1, ?t\<^sub>2') \<or> I \<TTurnstile>l Neg (?s\<^sub>1', ?t\<^sub>2')"
        by (meson transD trans_I true_lit_simps(1) true_lit_simps(2))

      then have "?I \<TTurnstile>l ?s\<^sub>1 \<approx> ?t\<^sub>2' \<or> ?I \<TTurnstile>l Neg (Upair ?s\<^sub>1' ?t\<^sub>2')"
        unfolding ground.true_lit_uprod_iff_true_lit_prod[OF sym_I].

      then show ?thesis
        unfolding C
        by (metis true_cls_add_mset)
    next
      case False
      then have "L' \<in># ?P'"
        using L'_in_P
        unfolding eq_factoringI
        by (simp add: to_ground_clause_def subst_clause_add_mset)

      then have "L' \<in># to_ground_clause (C \<cdot> \<theta>)"
        by (simp add: to_ground_clause_def eq_factoringI(7) subst_clause_add_mset)

      then show ?thesis
        using I_models_L' by blast
    qed
  qed

  then show ?thesis
    unfolding true_clss_singleton F_entails_def 
    by simp
qed

lemma superposition_sound:
  assumes step: "superposition P1 P2 C"
  shows "F_entails {P1, P2} {C}"
  using step
proof (cases P1 P2 C rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

  have 
    "\<And>I \<theta>. \<lbrakk>
        refl I;
        trans I; 
        sym I;
        compatible_with_gctxt I;
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (P1 \<cdot> \<sigma>);
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (P2 \<cdot> \<sigma>); 
        term_subst.is_ground_subst \<theta>
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"
  proof -
    fix I :: "'f gterm rel" and \<theta> :: "'v \<Rightarrow> ('f, 'v) Term.term"

    let ?I = "(\<lambda>(x, y). Upair x y) ` I"

    let ?P1 = "to_ground_clause (P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<theta>)"
    let ?P2 = "to_ground_clause (P2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<theta>)"

    let ?L\<^sub>1 = "to_ground_literal (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?L\<^sub>2 = "to_ground_literal (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<theta>)"

    let ?P\<^sub>1' = "to_ground_clause (P\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<theta>)"
    let ?P\<^sub>2' = "to_ground_clause (P\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<theta>)"

    let ?s\<^sub>1 = "to_ground_context (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<theta>)"
    let ?s\<^sub>1' = "to_ground_term (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2 = "to_ground_term (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2' = "to_ground_term (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?u\<^sub>1 = "to_ground_term (u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"

    let ?\<P> = "if \<P> = Pos then Pos else Neg"

    let ?C = "to_ground_clause (C \<cdot> \<theta>)"

    assume 
      ground_subst: "term_subst.is_ground_subst \<theta>" and 
      refl_I: "refl I" and 
      trans_I: "trans I" and 
      sym_I: "sym I" and 
      compatible_with_ground_context_I: "compatible_with_gctxt I" and
      premise1: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> to_ground_clause (P1 \<cdot> \<sigma>)" and
      premise2: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> to_ground_clause (P2 \<cdot> \<sigma>)"

    have "?I \<TTurnstile> ?P1"
      using 
         premise1[rule_format, of "\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<theta>", OF ground_subst_compose[OF ground_subst]]
         clause_subst_compose
      by metis

    moreover have "?I \<TTurnstile> ?P2"
      using 
         premise2[rule_format, of "\<rho>\<^sub>2 \<odot> \<mu> \<odot> \<theta>", OF ground_subst_compose[OF ground_subst]]
         clause_subst_compose
      by metis

    ultimately obtain L\<^sub>1' L\<^sub>2' 
      where
        L\<^sub>1'_in_P1: "L\<^sub>1' \<in># ?P1" and 
        I_models_L\<^sub>1': "?I \<TTurnstile>l L\<^sub>1'" and
        L\<^sub>2'_in_P2: "L\<^sub>2' \<in># ?P2" and 
        I_models_L\<^sub>2': "?I \<TTurnstile>l L\<^sub>2'"
      by (auto simp: true_cls_def)

    have u\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?u\<^sub>1"
      using is_imgu_equals[OF superpositionI(10)]
      by simp

    have s\<^sub>1_u\<^sub>1: "?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G = to_ground_term (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<theta>)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>\<rangle>"
      using ground_term_with_context(1)[OF 
              is_ground_subst_is_ground_context[OF ground_subst] 
              is_ground_subst_is_ground_term[OF ground_subst]
            ]
      by blast

    have s\<^sub>1_t\<^sub>2': "(?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G  = to_ground_term (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<theta>)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>\<rangle>"
      using ground_term_with_context(1)[OF 
              is_ground_subst_is_ground_context[OF ground_subst] 
              is_ground_subst_is_ground_term[OF ground_subst]
            ]
      by blast
      
    have \<P>_pos_or_neg: "\<P> = Pos \<or> \<P> = Neg"
      using superpositionI(6) by blast

    then have L\<^sub>1: "?L\<^sub>1 = ?\<P> (Upair ?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G ?s\<^sub>1')"
      unfolding superpositionI to_ground_literal_def to_ground_atom_def
      by(auto simp: subst_atom_def subst_literal s\<^sub>1_u\<^sub>1)
    
    have C: "?C = add_mset (?\<P> (Upair (?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G (?s\<^sub>1'))) (?P\<^sub>1' + ?P\<^sub>2')"
      using \<P>_pos_or_neg
      unfolding s\<^sub>1_t\<^sub>2' superpositionI
      apply(cases "\<P> = Pos")
      by (simp_all add: to_ground_clause_def to_ground_literal_def subst_atom_def subst_clause_add_mset subst_clause_plus 
              subst_literal to_ground_atom_def)

    show "?I \<TTurnstile> ?C"
    proof (cases "L\<^sub>1' = ?L\<^sub>1")
      case L\<^sub>1'_def: True
      then have "?I \<TTurnstile>l ?L\<^sub>1"
        using superpositionI
        using I_models_L\<^sub>1' by blast

      show ?thesis
      proof (cases "L\<^sub>2' = ?L\<^sub>2")
        case L\<^sub>2'_def: True
        then have ts_in_I: "(?t\<^sub>2, ?t\<^sub>2') \<in> I"
          using I_models_L\<^sub>2' ground.true_lit_uprod_iff_true_lit_prod[OF sym_I] superpositionI(8)
          unfolding to_ground_literal_def to_ground_atom_def 
          by (smt (verit) literal.simps(9) map_uprod_simps subst_atom_def subst_literal true_lit_simps(1))

        have ?thesis if "\<P> = Pos"
        proof -
          from that have "(?s\<^sub>1\<langle>?t\<^sub>2\<rangle>\<^sub>G, ?s\<^sub>1') \<in> I"
            using I_models_L\<^sub>1' L\<^sub>1'_def L\<^sub>1 ground.true_lit_uprod_iff_true_lit_prod[OF sym_I] u\<^sub>1_equals_t\<^sub>2
            unfolding superpositionI 
            by (smt (verit, best) true_lit_simps(1))

          then have "(?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G, ?s\<^sub>1') \<in> I"
            using ts_in_I compatible_with_ground_context_I refl_I sym_I trans_I
            by (meson compatible_with_gctxtD refl_onD1 symD trans_onD)
          
          then have "?I \<TTurnstile>l ?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G  \<approx> ?s\<^sub>1'"
            by blast

          then show ?thesis 
            unfolding C that
            by (smt (verit) true_cls_add_mset)
        qed

        moreover have ?thesis if "\<P> = Neg"
        proof -
          from that have "(?s\<^sub>1\<langle>?t\<^sub>2\<rangle>\<^sub>G, ?s\<^sub>1') \<notin> I"
            using I_models_L\<^sub>1' L\<^sub>1'_def L\<^sub>1 ground.true_lit_uprod_iff_true_lit_prod[OF sym_I] u\<^sub>1_equals_t\<^sub>2
            unfolding superpositionI 
            by (smt (verit, ccfv_threshold) literals_distinct(2) true_lit_simps(2))
        
          then have "(?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G, ?s\<^sub>1') \<notin> I"
            using ts_in_I compatible_with_ground_context_I trans_I
            by (meson compatible_with_gctxtD transD)

          then have "?I \<TTurnstile>l Neg (Upair ?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G  ?s\<^sub>1')"
            by (meson ground.true_lit_uprod_iff_true_lit_prod(2) sym_I true_lit_simps(2))

          then show ?thesis 
            unfolding C that
            by (smt (verit, best) literals_distinct(1) true_cls_add_mset)
        qed

        ultimately show ?thesis
          using \<P>_pos_or_neg by blast
      next
        case False
        then have "L\<^sub>2' \<in># ?P\<^sub>2'"
          using L\<^sub>2'_in_P2
          unfolding superpositionI
          by (simp add: to_ground_clause_def subst_clause_add_mset)

        then have "?I \<TTurnstile> ?P\<^sub>2'"
          using I_models_L\<^sub>2' by blast

        then show ?thesis
          unfolding superpositionI
          by (simp add: to_ground_clause_def subst_clause_add_mset subst_clause_plus)
      qed
    next
      case False
      then have "L\<^sub>1' \<in># ?P\<^sub>1'"
        using L\<^sub>1'_in_P1
        unfolding superpositionI 
        by (simp add: to_ground_clause_def subst_clause_add_mset)

      then have "?I \<TTurnstile> ?P\<^sub>1'"
        using I_models_L\<^sub>1' by blast

      then show ?thesis 
        unfolding superpositionI
        by (simp add: to_ground_clause_def subst_clause_add_mset subst_clause_plus)
    qed
  qed

  then show ?thesis 
    unfolding true_clss_singleton true_clss_insert F_entails_def
    by simp
qed

definition ginfer_infer :: 
  "('f, 'v) atom clause inference \<Rightarrow> 'f ground_atom clause inference" 
  where
  "ginfer_infer infer = Infer (map to_ground_clause (prems_of infer)) (to_ground_clause (concl_of infer))"

definition infer_ginfer :: 
  "'f ground_atom clause inference \<Rightarrow> ('f, 'v) atom clause inference" 
  where
  "infer_ginfer infer = Infer (map to_clause (prems_of infer)) (to_clause (concl_of infer))"

definition is_ground_subst_list :: "('f, 'v) subst list \<Rightarrow> bool" where
  "is_ground_subst_list \<sigma>s \<longleftrightarrow> (\<forall>\<sigma> \<in> set \<sigma>s. term_subst.is_ground_subst \<sigma>)"

(*definition \<G>_F :: 
  "('f, 'v) atom clause \<Rightarrow> 'f ground_atom clause set" 
  where
  "\<G>_F C \<equiv> { to_ground_clause (C \<cdot> \<sigma>) | \<sigma>. term_subst.is_ground_subst \<sigma> }"

definition \<G>_I :: 
  "('f, 'v) atom clause inference \<Rightarrow> 'f ground_atom clause inference set option" 
  where
  "\<G>_I \<iota> = Some ({ginfer_infer (Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>)) |\<rho> \<rho>s.
     is_ground_subst_list \<rho>s \<and> term_subst.is_ground_subst \<rho>
     \<and> ginfer_infer (Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>)) \<in> G.G_Inf})"*)


definition Prec_F :: 
  "'f ground_atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" 
  where
  "Prec_F \<equiv> \<lambda>_ _ _. False"

interpretation F: sound_inference_system F_Inf F_Bot F_entails
proof unfold_locales
  show "\<And>\<iota>. \<iota> \<in> F_Inf \<Longrightarrow> F_entails (set (prems_of \<iota>)) {concl_of \<iota>}"
    using 
      F_Inf_def 
      eq_factoring_sound
      eq_resolution_sound
      superposition_sound
      F_entails_def
    by auto
next 
  show "F_Bot \<noteq> {}"
    by simp
next 
  have "\<And>\<theta> I. 
    term_subst.is_ground_subst \<theta> \<Longrightarrow> 
    (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause ({#} \<cdot> \<theta>) \<Longrightarrow> False"
    by (metis to_clause_empty_mset to_clause_inverse image_mset_is_empty_iff subst_clause_def 
          true_cls_empty)

  then show "\<And>B N1. B \<in> F_Bot \<Longrightarrow> F_entails {B} N1"
    unfolding true_clss_singleton F_entails_def
    by fastforce
next
  show "\<And>N2 N1. N2 \<subseteq> N1 \<Longrightarrow> F_entails N1 N2"
    by (auto simp: F_entails_def elim!: true_clss_mono[rotated])
next
  show "\<And>N2 N1. \<forall>C\<in>N2. F_entails N1 {C} \<Longrightarrow> F_entails N1 N2"
    unfolding F_entails_def
    by blast
next
  show "\<And>N1 N2 N3. \<lbrakk>F_entails N1 N2; F_entails N2 N3\<rbrakk> \<Longrightarrow> F_entails N1 N3 "
    using F_entails_def 
    by (smt (verit, best))
qed


  
(* Q = gs(S) 
  q = T
*)

interpretation F: lifting_intersection F_Inf ground.G_Bot "UNIV" "\<lambda> _. ground.G_Inf"
  "\<lambda>_. ground.G_entails" "\<lambda>_. ground.Red_I" "\<lambda>_. ground.Red_F" F_Bot "\<lambda>_.  \<G>_F" "\<lambda>_. \<G>_I" Prec_F
proof unfold_locales
  show "UNIV \<noteq> {}"
    by simp
next 
  have "consequence_relation ground.G_Bot ground.G_entails"
    apply unfold_locales
    apply auto
    using ground.G_entails_def apply blast
    unfolding ground.G_entails_def
    using subset_entailed apply auto
    by (simp add: true_clss_def)

  then show "\<forall>q\<in>UNIV. consequence_relation ground.G_Bot ground.G_entails"
    ..
next
  show  "\<forall>q\<in>UNIV. tiebreaker_lifting F_Bot F_Inf ground.G_Bot ground.G_entails ground.G_Inf ground.Red_I ground.Red_F \<G>_F \<G>_I Prec_F"
    sorry
qed

(*
interpretation F: statically_complete_calculus F_Bot F_Inf "F.entails_\<G>" F.Red_I_\<G> F.Red_F_\<G>
proof unfold_locales
  show "\<And>B N. B \<in> F_Bot \<Longrightarrow> F.saturated N \<Longrightarrow> F.entails_\<G> N {B} \<Longrightarrow> \<exists>B' \<in> F_Bot. B' \<in> N"
    sorry
qed *)

end

end