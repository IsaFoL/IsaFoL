theory First_Order_Ordering
  imports 
    First_Order_Clause
    Ground_Ordering
    Relation_Extra
    "Open_Induction.Restricted_Predicates"
begin

(* TODO: Move *)
context ground_ordering
begin

lemmas less\<^sub>l\<^sub>G_transitive_on = transp_less_lit[THEN transp_on_subset, OF subset_UNIV]
lemmas less\<^sub>l\<^sub>G_asymmetric_on = asymp_less_lit[THEN asymp_on_subset, OF subset_UNIV]
lemmas less\<^sub>l\<^sub>G_total_on = totalp_less_lit[THEN totalp_on_subset, OF subset_UNIV]

lemmas less\<^sub>c\<^sub>G_transitive_on = transp_less_cls[THEN transp_on_subset, OF subset_UNIV]
lemmas less\<^sub>c\<^sub>G_asymmetric_on = asymp_less_cls[THEN asymp_on_subset, OF subset_UNIV]
lemmas less\<^sub>c\<^sub>G_total_on = totalp_less_cls[THEN totalp_on_subset, OF subset_UNIV]

lemmas is_maximal_lit_def = is_maximal_in_mset_wrt_iff[OF less\<^sub>l\<^sub>G_transitive_on less\<^sub>l\<^sub>G_asymmetric_on]
lemmas is_strictly_maximal_lit_def = 
  is_strictly_maximal_in_mset_wrt_iff[OF less\<^sub>l\<^sub>G_transitive_on less\<^sub>l\<^sub>G_asymmetric_on]

end

(* TODO: 
   - to_term ` terms\<^sub>G as set of all ground_terms 
   - less\<^sub>t-prefixes actually not needed
*)
locale first_order_ordering =
  fixes
    less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50)
  assumes
    (* TODO: It should be enough to have these on ground terms*)
    less\<^sub>t_transitive [intro]: "transp (\<prec>\<^sub>t)" and
    less\<^sub>t_asymmetric [intro]: "asymp (\<prec>\<^sub>t)" and 

    less\<^sub>t_wellfounded_on [intro]: "wfp_on (\<prec>\<^sub>t) {term. is_ground_term term}" and
    less\<^sub>t_total_on [intro]: "totalp_on {term. is_ground_term term} (\<prec>\<^sub>t)" and
    
    less\<^sub>t_ground_context_compatible:
      "\<And>context term\<^sub>1 term\<^sub>2. 
        term\<^sub>1 \<prec>\<^sub>t term\<^sub>2 \<Longrightarrow>
        is_ground_term term\<^sub>1 \<Longrightarrow> 
        is_ground_term term\<^sub>2 \<Longrightarrow> 
        is_ground_context context \<Longrightarrow>
        context\<langle>term\<^sub>1\<rangle> \<prec>\<^sub>t context\<langle>term\<^sub>2\<rangle>" and
    less\<^sub>t_ground_subst_stability: 
      "\<And>term\<^sub>1 term\<^sub>2 (\<theta> :: 'v \<Rightarrow> ('f, 'v) term). 
        is_ground_term (term\<^sub>1 \<cdot>t \<theta>) \<Longrightarrow>
        is_ground_term (term\<^sub>2 \<cdot>t \<theta>) \<Longrightarrow>
        term\<^sub>1 \<prec>\<^sub>t term\<^sub>2 \<Longrightarrow>
        term\<^sub>1 \<cdot>t \<theta> \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<theta>" and
    less\<^sub>t_ground_subterm_property: 
      "\<And>term\<^sub>G context\<^sub>G.
         is_ground_term term\<^sub>G \<Longrightarrow>
         is_ground_context context\<^sub>G \<Longrightarrow> 
         context\<^sub>G \<noteq> \<box> \<Longrightarrow> 
         term\<^sub>G \<prec>\<^sub>t context\<^sub>G\<langle>term\<^sub>G\<rangle>"
begin

definition less\<^sub>t\<^sub>G :: "'f ground_term \<Rightarrow> 'f ground_term \<Rightarrow> bool" (infix "\<prec>\<^sub>t\<^sub>G" 50) where
  "term\<^sub>G\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>G\<^sub>2 \<equiv> to_term term\<^sub>G\<^sub>1 \<prec>\<^sub>t to_term term\<^sub>G\<^sub>2"

lemma less\<^sub>t_wellfounded_on': "wfp_on (\<prec>\<^sub>t) (to_term ` terms\<^sub>G)"
  using less\<^sub>t_wellfounded_on
  unfolding wfp_on_def
  by (metis (mono_tags) ground_term_is_ground imageE mem_Collect_eq)

lemma less\<^sub>t\<^sub>G_wellfounded [intro]: "wfP (\<prec>\<^sub>t\<^sub>G)"
proof -
  have "wfp_on (\<prec>\<^sub>t) (range to_term)"
    using less\<^sub>t_wellfounded_on' by metis
  hence "wfp_on (\<lambda>term\<^sub>G\<^sub>1 term\<^sub>G\<^sub>2. to_term term\<^sub>G\<^sub>1 \<prec>\<^sub>t to_term term\<^sub>G\<^sub>2) UNIV"
    unfolding wfp_on_image[symmetric] .
  hence "wfp_on (\<prec>\<^sub>t\<^sub>G) UNIV"
    unfolding less\<^sub>t\<^sub>G_def .
  thus "wfP (\<prec>\<^sub>t\<^sub>G)"
    unfolding wfp_on_UNIV .
qed

lemma less\<^sub>t_total_on': "totalp_on (to_term ` terms\<^sub>G) (\<prec>\<^sub>t)"
  using less\<^sub>t_total_on
  by (simp add: totalp_on_def)

lemma less\<^sub>t\<^sub>G_total [intro]: "totalp (\<prec>\<^sub>t\<^sub>G)"
  unfolding less\<^sub>t\<^sub>G_def
  using totalp_on_image[OF inj_term_of_gterm] less\<^sub>t_total_on'
  by blast

lemma less\<^sub>t\<^sub>G_context_compatible [simp]: 
  assumes "term\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>2"  
  shows "context\<langle>term\<^sub>1\<rangle>\<^sub>G \<prec>\<^sub>t\<^sub>G context\<langle>term\<^sub>2\<rangle>\<^sub>G"
  using assms less\<^sub>t_ground_context_compatible
  unfolding less\<^sub>t\<^sub>G_def
  by (metis ground_context_is_ground ground_term_is_ground ground_term_with_context(3)) 

lemma less\<^sub>t\<^sub>G_subterm_property [simp]: 
  assumes "context \<noteq> \<box>\<^sub>G" 
  shows "term \<prec>\<^sub>t\<^sub>G context\<langle>term\<rangle>\<^sub>G"
  using assms less\<^sub>t_ground_subterm_property
  unfolding less\<^sub>t\<^sub>G_def
  by (metis gctxt_of_ctxt.simps(1) ground_context_is_ground ground_term_is_ground ground_term_with_context3 to_context_inverse)

lemmas less\<^sub>t_transitive_on = less\<^sub>t_transitive[THEN transp_on_subset, OF subset_UNIV]
lemmas less\<^sub>t_asymmetric_on = less\<^sub>t_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

lemma less\<^sub>t\<^sub>G_transitive [intro]: "transp (\<prec>\<^sub>t\<^sub>G)"
  using less\<^sub>t\<^sub>G_def less\<^sub>t_transitive transpE transpI
  by (metis (full_types))

lemmas less\<^sub>t\<^sub>G_transitive_on = less\<^sub>t\<^sub>G_transitive[THEN transp_on_subset, OF subset_UNIV]

lemma less\<^sub>t\<^sub>G_asymmetric [intro]: "asymp (\<prec>\<^sub>t\<^sub>G)"
  by (simp add: wfP_imp_asymp less\<^sub>t\<^sub>G_wellfounded)

lemmas less\<^sub>t\<^sub>G_asymmetric_on = less\<^sub>t\<^sub>G_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

lemmas less\<^sub>t\<^sub>G_total_on = less\<^sub>t\<^sub>G_total[THEN totalp_on_subset, OF subset_UNIV]

lemma less\<^sub>t_less\<^sub>t\<^sub>G: 
  assumes "is_ground_term term\<^sub>1" and "is_ground_term term\<^sub>2"
  shows "term\<^sub>1 \<prec>\<^sub>t term\<^sub>2 \<longleftrightarrow> to_ground_term term\<^sub>1 \<prec>\<^sub>t\<^sub>G to_ground_term term\<^sub>2"
  by (simp add: assms less\<^sub>t\<^sub>G_def)

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

abbreviation is_maximal\<^sub>l :: 
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  "is_maximal\<^sub>l literal clause \<equiv> is_maximal_in_mset_wrt (\<prec>\<^sub>l) clause literal"

abbreviation is_strictly_maximal\<^sub>l :: 
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  "is_strictly_maximal\<^sub>l literal clause \<equiv> is_strictly_maximal_in_mset_wrt (\<prec>\<^sub>l) clause literal"

(* TODO: Is there a more concise way to write all these proofs? *)
lemma less\<^sub>l_transitive [intro]: "transp (\<prec>\<^sub>l)"
  unfolding less\<^sub>l_def 
  using transp_multp[OF less\<^sub>t_transitive]
  by (metis (no_types, lifting) transpE transpI)

lemmas less\<^sub>l_transitive_on = less\<^sub>l_transitive[THEN transp_on_subset, OF subset_UNIV]
                                                            
lemma less\<^sub>l_asymmetric [intro]: "asymp (\<prec>\<^sub>l)"
  unfolding less\<^sub>l_def  multp_eq_multp\<^sub>H\<^sub>O[OF less\<^sub>t_asymmetric less\<^sub>t_transitive]
  using asymp_multp\<^sub>H\<^sub>O[OF less\<^sub>t_asymmetric less\<^sub>t_transitive]
  by (meson asympD asympI)

lemmas less\<^sub>l_asymmetric_on [intro] = less\<^sub>l_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

lemmas is_maximal\<^sub>l_def = is_maximal_in_mset_wrt_iff[OF less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on]

lemmas is_strictly_maximal\<^sub>l_def =
  is_strictly_maximal_in_mset_wrt_iff[OF less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on]

lemmas is_maximal\<^sub>l_if_is_strictly_maximal\<^sub>l =
  is_maximal_in_mset_wrt_if_is_strictly_maximal_in_mset_wrt[OF 
    less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on
  ]

lemmas less\<^sub>c_transitive [intro] = transp_multp[OF less\<^sub>l_transitive]

lemmas less\<^sub>c_transitive_on [intro] = less\<^sub>c_transitive[THEN transp_on_subset, OF subset_UNIV]

lemmas less\<^sub>c_asymmetric [intro] = asymp_multp[OF less\<^sub>l_asymmetric less\<^sub>l_transitive]

lemmas less\<^sub>c_asymmetric_on [intro] = less\<^sub>c_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

lemma less\<^sub>l_ground_subst_stability: 
  assumes 
    "is_ground_literal (literal \<cdot>l \<theta>)" 
    "is_ground_literal (literal' \<cdot>l \<theta>)" 
  shows "literal \<prec>\<^sub>l literal' \<Longrightarrow> literal \<cdot>l \<theta> \<prec>\<^sub>l literal' \<cdot>l \<theta>"
  unfolding less\<^sub>l_def mset_mset_lit_subst[symmetric]
proof (elim multp_map_strong[rotated -1])
  show "asymp (\<prec>\<^sub>t)"
    using less\<^sub>t_asymmetric .
next
  show "transp (\<prec>\<^sub>t)"
    using less\<^sub>t_transitive .
next
  show "monotone_on (set_mset (mset_lit literal + mset_lit literal')) (\<prec>\<^sub>t) (\<prec>\<^sub>t) (\<lambda>term. term \<cdot>t \<theta>)"
    by (rule monotone_onI)
      (metis assms(1,2) less\<^sub>t_ground_subst_stability ground_term_in_ground_literal_subst union_iff)
qed

lemma less\<^sub>c_ground_subst_stability: 
  assumes 
    "is_ground_clause (clause \<cdot> \<theta>)" 
    "is_ground_clause (clause' \<cdot> \<theta>)" 
  shows "clause \<prec>\<^sub>c clause' \<Longrightarrow> clause \<cdot> \<theta> \<prec>\<^sub>c clause' \<cdot> \<theta>"
  unfolding subst_clause_def
proof (elim multp_map_strong[rotated -1])
  show "asymp (\<prec>\<^sub>l)"
    using less\<^sub>l_asymmetric .
next
  show "transp (\<prec>\<^sub>l)"
    using less\<^sub>l_transitive .
next
  show "monotone_on (set_mset (clause + clause')) (\<prec>\<^sub>l) (\<prec>\<^sub>l) (\<lambda>literal. literal \<cdot>l \<theta>)"
    by (rule monotone_onI)
      (metis assms(1,2) ground_literal_in_ground_clause_subst less\<^sub>l_ground_subst_stability union_iff)
qed

lemma less_eq\<^sub>t_ground_subst_stability:
  assumes "is_ground_term (term\<^sub>1 \<cdot>t \<theta>)" "is_ground_term (term\<^sub>2 \<cdot>t \<theta>)"  "term\<^sub>1 \<preceq>\<^sub>t term\<^sub>2"
  shows "term\<^sub>1 \<cdot>t \<theta> \<preceq>\<^sub>t term\<^sub>2 \<cdot>t \<theta>"
  using less\<^sub>t_ground_subst_stability[OF assms(1, 2)] assms(3)
  by auto

sublocale ground: ground_ordering "(\<prec>\<^sub>t\<^sub>G)" 
  apply unfold_locales
  by(simp_all add: less\<^sub>t\<^sub>G_transitive less\<^sub>t\<^sub>G_asymmetric less\<^sub>t\<^sub>G_wellfounded less\<^sub>t\<^sub>G_total)

notation ground.less_lit (infix "\<prec>\<^sub>l\<^sub>G" 50)
notation ground.less_cls (infix "\<prec>\<^sub>c\<^sub>G" 50)

notation ground.lesseq_trm (infix "\<preceq>\<^sub>t\<^sub>G" 50)
notation ground.lesseq_lit (infix "\<preceq>\<^sub>l\<^sub>G" 50)
notation ground.lesseq_cls (infix "\<preceq>\<^sub>c\<^sub>G" 50)

(* TODO: Move these similarly to first_order_ordering *)
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
  ..

lemma not_less_eq\<^sub>t: 
  assumes "is_ground_term term\<^sub>1" and "is_ground_term term\<^sub>2"
  shows "\<not> term\<^sub>2 \<preceq>\<^sub>t term\<^sub>1 \<longleftrightarrow> term\<^sub>1 \<prec>\<^sub>t term\<^sub>2"
  unfolding less\<^sub>t_less\<^sub>t\<^sub>G[OF assms] less_eq\<^sub>t_less_eq\<^sub>t\<^sub>G[OF assms(2, 1)] not_less_eq\<^sub>t\<^sub>G
  ..

lemma less\<^sub>l\<^sub>G_less\<^sub>l: "literal\<^sub>G\<^sub>1 \<prec>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2 \<longleftrightarrow> to_literal literal\<^sub>G\<^sub>1 \<prec>\<^sub>l to_literal literal\<^sub>G\<^sub>2"
  unfolding less\<^sub>l_def ground.less_lit_def less\<^sub>t\<^sub>G_def mset_to_literal
  using
     multp_image_mset_image_msetI[OF _ less\<^sub>t_transitive]
     multp_image_mset_image_msetD[OF _ less\<^sub>t_transitive_on to_term_inj]
   by blast

lemma less\<^sub>l_less\<^sub>l\<^sub>G: 
  assumes "is_ground_literal literal\<^sub>1" "is_ground_literal literal\<^sub>2" 
  shows "literal\<^sub>1 \<prec>\<^sub>l literal\<^sub>2 \<longleftrightarrow> to_ground_literal literal\<^sub>1 \<prec>\<^sub>l\<^sub>G to_ground_literal literal\<^sub>2"
  using assms
  by (simp add: less\<^sub>l\<^sub>G_less\<^sub>l)

lemma less\<^sub>l_total_on [intro]: "totalp_on (to_literal ` literals\<^sub>G) (\<prec>\<^sub>l)"
  by (smt (verit, best) image_iff less\<^sub>l\<^sub>G_less\<^sub>l totalpD ground.less\<^sub>l\<^sub>G_total_on totalp_on_def)

lemma less_eq\<^sub>l_less_eq\<^sub>l\<^sub>G:
  assumes "is_ground_literal literal\<^sub>1" and "is_ground_literal literal\<^sub>2" 
  shows "literal\<^sub>1 \<preceq>\<^sub>l literal\<^sub>2 \<longleftrightarrow> to_ground_literal literal\<^sub>1 \<preceq>\<^sub>l\<^sub>G to_ground_literal literal\<^sub>2"
  unfolding reflclp_iff less\<^sub>l_less\<^sub>l\<^sub>G[OF assms]
  using assms[THEN to_ground_literal_inverse]
  by auto

lemma less_eq\<^sub>l\<^sub>G_less_eq\<^sub>l:
   "literal\<^sub>G\<^sub>1 \<preceq>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2 \<longleftrightarrow> to_literal literal\<^sub>G\<^sub>1 \<preceq>\<^sub>l to_literal literal\<^sub>G\<^sub>2"
  unfolding 
    less_eq\<^sub>l_less_eq\<^sub>l\<^sub>G[OF ground_literal_is_ground ground_literal_is_ground] 
    to_literal_inverse
  ..

lemma maximal_lit_in_clause:
  assumes "ground.is_maximal_lit literal\<^sub>G clause\<^sub>G"
  shows "literal\<^sub>G \<in># clause\<^sub>G"
  using assms 
  unfolding ground.is_maximal_lit_def
  by(rule conjunct1)

lemma maximal\<^sub>l_in_clause:
  assumes "is_maximal\<^sub>l literal clause"
  shows "literal \<in># clause"
  using assms 
  unfolding is_maximal\<^sub>l_def
  by(rule conjunct1)

lemma strictly_maximal\<^sub>l_in_clause:
  assumes "is_strictly_maximal\<^sub>l literal clause"
  shows "literal \<in># clause"
  using assms 
  unfolding is_strictly_maximal\<^sub>l_def
  by(rule conjunct1)

lemma is_maximal_lit_iff_is_maximal\<^sub>l: 
  "ground.is_maximal_lit literal\<^sub>G clause\<^sub>G \<longleftrightarrow> is_maximal\<^sub>l (to_literal literal\<^sub>G) (to_clause clause\<^sub>G)"
   unfolding 
    is_maximal\<^sub>l_def
    ground.is_maximal_lit_def
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
    is_strictly_maximal_in_mset_wrt_iff_is_greatest_in_mset_wrt[OF 
      ground.less\<^sub>l\<^sub>G_transitive_on ground.less\<^sub>l\<^sub>G_asymmetric_on ground.less\<^sub>l\<^sub>G_total_on, symmetric
    ]
    ground.is_strictly_maximal_lit_def
    is_strictly_maximal\<^sub>l_def
    ground_literal_in_ground_clause(3)[symmetric]
    remove1_mset_to_literal
    ground_literal_in_ground_clause(4)
    less_eq\<^sub>l\<^sub>G_less_eq\<^sub>l
  ..
 
lemma not_less_eq\<^sub>l\<^sub>G: "\<not> literal\<^sub>G\<^sub>2 \<preceq>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>1 \<longleftrightarrow> literal\<^sub>G\<^sub>1 \<prec>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2"
  using asympD[OF ground.less\<^sub>l\<^sub>G_asymmetric_on] totalpD[OF ground.less\<^sub>l\<^sub>G_total_on]
  by blast

lemma not_less_eq\<^sub>l: 
  assumes "is_ground_literal literal\<^sub>1" and "is_ground_literal literal\<^sub>2"
  shows "\<not> literal\<^sub>2 \<preceq>\<^sub>l literal\<^sub>1 \<longleftrightarrow> literal\<^sub>1 \<prec>\<^sub>l literal\<^sub>2"
  unfolding less\<^sub>l_less\<^sub>l\<^sub>G[OF assms] less_eq\<^sub>l_less_eq\<^sub>l\<^sub>G[OF assms(2, 1)] not_less_eq\<^sub>l\<^sub>G
  ..

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
  by fastforce

lemma less_eq\<^sub>c\<^sub>G_less_eq\<^sub>c:
   "clause\<^sub>G\<^sub>1 \<preceq>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2 \<longleftrightarrow> to_clause clause\<^sub>G\<^sub>1 \<preceq>\<^sub>c to_clause clause\<^sub>G\<^sub>2"
  unfolding less_eq\<^sub>c_less_eq\<^sub>c\<^sub>G[OF ground_clause_is_ground ground_clause_is_ground] to_clause_inverse
  ..

lemma less\<^sub>c_total_on: "totalp_on (to_clause ` clauses) (\<prec>\<^sub>c)"
  by (smt ground.totalp_less_cls image_iff less\<^sub>c\<^sub>G_less\<^sub>c totalpD totalp_onI) 

lemma not_less_eq\<^sub>c\<^sub>G: "\<not> clause\<^sub>G\<^sub>2 \<preceq>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>1 \<longleftrightarrow> clause\<^sub>G\<^sub>1 \<prec>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2"
  using asympD[OF ground.less\<^sub>c\<^sub>G_asymmetric_on] totalpD[OF ground.less\<^sub>c\<^sub>G_total_on]
  by blast

lemma not_less_eq\<^sub>c: 
  assumes "is_ground_clause clause\<^sub>1" and "is_ground_clause clause\<^sub>2"
  shows "\<not> clause\<^sub>2 \<preceq>\<^sub>c clause\<^sub>1 \<longleftrightarrow> clause\<^sub>1 \<prec>\<^sub>c clause\<^sub>2"
  unfolding less\<^sub>c_less\<^sub>c\<^sub>G[OF assms] less_eq\<^sub>c_less_eq\<^sub>c\<^sub>G[OF assms(2, 1)] not_less_eq\<^sub>c\<^sub>G
  ..

lemma less\<^sub>t_less_eq\<^sub>t_ground_subst_stability:
  assumes 
    "is_ground_term (term\<^sub>1 \<cdot>t \<theta>)"
    "is_ground_term (term\<^sub>2 \<cdot>t \<theta>)"
    "term\<^sub>1 \<cdot>t \<theta> \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<theta>"
  shows
    "\<not> term\<^sub>2 \<preceq>\<^sub>t term\<^sub>1"
proof
  assume assumption: "term\<^sub>2 \<preceq>\<^sub>t term\<^sub>1"

  have "term\<^sub>2 \<cdot>t \<theta> \<preceq>\<^sub>t term\<^sub>1 \<cdot>t \<theta>"
    using less_eq\<^sub>t_ground_subst_stability[OF 
            assms(2, 1)
            assumption
           ].

  then show False 
    using assms(3)
    unfolding not_less_eq\<^sub>t[OF assms(1, 2), symmetric]
    by blast
qed

lemma less_eq\<^sub>l_ground_subst_stability:
  assumes   
    "is_ground_literal (literal\<^sub>1 \<cdot>l \<theta>)" 
    "is_ground_literal (literal\<^sub>2 \<cdot>l \<theta>)"  
    "literal\<^sub>1 \<preceq>\<^sub>l literal\<^sub>2"
  shows "literal\<^sub>1 \<cdot>l \<theta> \<preceq>\<^sub>l literal\<^sub>2 \<cdot>l \<theta>"
  using less\<^sub>l_ground_subst_stability[OF assms(1, 2)] assms(3)
  by auto

lemma less\<^sub>l_less_eq\<^sub>l_ground_subst_stability: assumes 
  "is_ground_literal (literal\<^sub>1 \<cdot>l \<theta>)"
  "is_ground_literal (literal\<^sub>2 \<cdot>l \<theta>)"
  "literal\<^sub>1 \<cdot>l \<theta> \<prec>\<^sub>l literal\<^sub>2 \<cdot>l \<theta>"
shows
  "\<not> literal\<^sub>2 \<preceq>\<^sub>l literal\<^sub>1"
  by (meson assms less_eq\<^sub>l_ground_subst_stability not_less_eq\<^sub>l)

lemma less_eq\<^sub>c_ground_subst_stability:
  assumes   
    "is_ground_clause (clause\<^sub>1 \<cdot> \<theta>)" 
    "is_ground_clause (clause\<^sub>2 \<cdot> \<theta>)"  
    "clause\<^sub>1 \<preceq>\<^sub>c clause\<^sub>2"
  shows "clause\<^sub>1 \<cdot> \<theta> \<preceq>\<^sub>c clause\<^sub>2 \<cdot> \<theta>"
  using less\<^sub>c_ground_subst_stability[OF assms(1, 2)] assms(3)
  by auto

lemma less\<^sub>c_less_eq\<^sub>c_ground_subst_stability: assumes 
  "is_ground_clause (clause\<^sub>1 \<cdot> \<theta>)"
  "is_ground_clause (clause\<^sub>2 \<cdot> \<theta>)"
  "clause\<^sub>1 \<cdot> \<theta> \<prec>\<^sub>c clause\<^sub>2 \<cdot> \<theta>"
shows
  "\<not> clause\<^sub>2 \<preceq>\<^sub>c clause\<^sub>1"
  by (meson assms less_eq\<^sub>c_ground_subst_stability not_less_eq\<^sub>c)
  
lemma is_maximal\<^sub>l_ground_subst_stability:
  assumes 
    clause_not_empty: "clause \<noteq> {#}" and
    clause_grounding: "is_ground_clause (clause \<cdot> \<theta>)" 
  obtains literal
  where "is_maximal\<^sub>l literal clause" "is_maximal\<^sub>l (literal \<cdot>l \<theta>) (clause \<cdot> \<theta>)"
proof-
  assume assumption: 
    "\<And>literal. is_maximal\<^sub>l literal clause \<Longrightarrow> is_maximal\<^sub>l (literal \<cdot>l \<theta>) (clause \<cdot> \<theta>) \<Longrightarrow> thesis"

  from clause_not_empty 
  have clause_grounding_not_empty: "clause \<cdot> \<theta> \<noteq> {#}"
    unfolding subst_clause_def
    by simp

  obtain literal where 
    literal: "literal \<in># clause" and
    literal_grounding_is_maximal: "is_maximal\<^sub>l (literal \<cdot>l \<theta>) (clause \<cdot> \<theta>)" 
    using
      ex_maximal_in_mset_wrt[OF less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on clause_grounding_not_empty]  
      maximal\<^sub>l_in_clause
    unfolding subst_clause_def
    by force

  from literal_grounding_is_maximal
  have no_bigger_than_literal: 
    "\<forall>literal' \<in># clause \<cdot> \<theta>. literal' \<noteq> literal \<cdot>l \<theta> \<longrightarrow> \<not> literal \<cdot>l \<theta> \<prec>\<^sub>l literal'"
    unfolding is_maximal\<^sub>l_def
    by simp

  show ?thesis
  proof(cases "is_maximal\<^sub>l literal clause")
    case True
    with literal_grounding_is_maximal assumption show ?thesis
      by blast
  next
    case False
    then obtain literal' where 
      literal': "literal' \<in># clause" "literal \<prec>\<^sub>l literal'" 
      unfolding is_maximal\<^sub>l_def
      using literal
      by blast 

    note literals_in_clause = literal(1) literal'(1)
    note literals_grounding = literals_in_clause[THEN 
        ground_literal_in_ground_clause_subst[OF clause_grounding]
      ]

    have "literal \<cdot>l \<theta> \<prec>\<^sub>l literal' \<cdot>l \<theta>"
      using less\<^sub>l_ground_subst_stability[OF literals_grounding literal'(2)].
   
    then have False
     using 
       no_bigger_than_literal
       literal_in_clause_subst[OF literal'(1)] 
     by (metis asymp_onD less\<^sub>l_asymmetric_on)
       
    then show ?thesis..
  qed
qed

lemma is_maximal\<^sub>l_ground_subst_stability':
  assumes 
   "literal \<in># clause"
   "is_ground_clause (clause \<cdot> \<theta>)"
   "is_maximal\<^sub>l (literal \<cdot>l \<theta>) (clause \<cdot> \<theta>)"
 shows 
   "is_maximal\<^sub>l literal clause"
proof(rule ccontr)
  assume "\<not> is_maximal\<^sub>l literal clause"
  
  then obtain literal' where literal':
      "literal \<prec>\<^sub>l literal'" 
      "literal' \<in># clause "
  using assms(1)
  unfolding is_maximal\<^sub>l_def
  by blast

  then have literal'_grounding: "is_ground_literal (literal' \<cdot>l \<theta>)"
    using assms(2) ground_literal_in_ground_clause_subst by blast

  have literal_grounding: "is_ground_literal (literal \<cdot>l \<theta>)"
    using assms(1) assms(2) ground_literal_in_ground_clause_subst by blast

  have literal_\<theta>_in_premise: "literal' \<cdot>l \<theta> \<in># clause \<cdot> \<theta>"
    using literal_in_clause_subst[OF literal'(2)]
    by simp
     
  have "literal \<cdot>l \<theta> \<prec>\<^sub>l literal' \<cdot>l \<theta>"
    using less\<^sub>l_ground_subst_stability[OF literal_grounding literal'_grounding literal'(1)].
  
  then have "\<not> is_maximal\<^sub>l (literal \<cdot>l \<theta>) (clause \<cdot> \<theta>)"
    using literal_\<theta>_in_premise 
    unfolding is_maximal\<^sub>l_def literal_subst_compose
    by (metis asympD less\<^sub>l_asymmetric)
  
  then show False
    using assms(3)
    by blast
qed

lemma unique_maximal_in_ground_clause:
  assumes
    "is_ground_clause clause" 
    "is_maximal\<^sub>l literal clause"
    "is_maximal\<^sub>l literal' clause"
  shows
    "literal = literal'"
  using assms(2, 3)
  unfolding is_maximal\<^sub>l_def
  by (metis assms(1) less\<^sub>l_total_on_set_mset to_ground_clause_inverse totalp_onD)

lemma unique_strictly_maximal_in_ground_clause:
  assumes
    "is_ground_clause clause" 
    "is_strictly_maximal\<^sub>l literal clause"
    "is_strictly_maximal\<^sub>l literal' clause"
  shows
    "literal = literal'"
proof-
  note are_maximal\<^sub>l = assms(2, 3)[THEN is_maximal\<^sub>l_if_is_strictly_maximal\<^sub>l]
   
  show ?thesis
    using unique_maximal_in_ground_clause[OF assms(1) are_maximal\<^sub>l].
qed

lemma is_strictly_maximal\<^sub>l_ground_subst_stability:
  assumes 
   clause_grounding: "is_ground_clause (clause \<cdot> \<theta>)" and
   ground_strictly_maximal: "is_strictly_maximal\<^sub>l literal\<^sub>G (clause \<cdot> \<theta>)"
 obtains literal where 
   "is_strictly_maximal\<^sub>l literal clause" "literal \<cdot>l \<theta> = literal\<^sub>G"
proof-
  assume assumption: "\<And>literal. 
    is_strictly_maximal\<^sub>l literal clause \<Longrightarrow> literal \<cdot>l \<theta> = literal\<^sub>G \<Longrightarrow> thesis"

  have clause_grounding_not_empty: "clause \<cdot> \<theta> \<noteq> {#}"
    using ground_strictly_maximal
    unfolding is_strictly_maximal\<^sub>l_def
    by fastforce

  have literal\<^sub>G_in_clause_grounding: "literal\<^sub>G \<in># clause \<cdot> \<theta>"
    using ground_strictly_maximal is_strictly_maximal\<^sub>l_def by blast

  obtain literal where literal: "literal \<in># clause" "literal \<cdot>l \<theta> = literal\<^sub>G"
    by (metis imageE literal\<^sub>G_in_clause_grounding multiset.set_map subst_clause_def)

  show ?thesis
  proof(cases "is_strictly_maximal\<^sub>l literal clause")
    case True
    then show ?thesis
      using assumption
      using literal(2) by blast
  next
    case False

    then obtain literal' where literal': 
      "literal' \<in># clause - {# literal #}"  
      "literal \<preceq>\<^sub>l literal'" 
      unfolding is_strictly_maximal\<^sub>l_def
      using literal(1)
      by blast 

    note literal_grounding = 
      ground_literal_in_ground_clause_subst[OF clause_grounding literal(1)]

    have literal'_grounding: "is_ground_literal (literal' \<cdot>l \<theta>)"
      using literal'(1) clause_grounding
      by (meson ground_literal_in_ground_clause_subst in_diffD)

    have "literal \<cdot>l \<theta> \<preceq>\<^sub>l literal' \<cdot>l \<theta>"
      using less_eq\<^sub>l_ground_subst_stability[OF literal_grounding literal'_grounding literal'(2)].

    then have False
      using literal_in_clause_subst[OF literal'(1)]  ground_strictly_maximal 
      unfolding 
        is_strictly_maximal\<^sub>l_def 
        literal(2)[symmetric]
        subst_clause_remove1_mset[OF literal(1)]
      by blast
   
    then show ?thesis..
  qed
qed

lemma is_strictly_maximal\<^sub>l_ground_subst_stability':
  assumes 
   "literal \<in># clause"
   "is_ground_clause (clause \<cdot> \<theta>)"
   "is_strictly_maximal\<^sub>l (literal \<cdot>l \<theta>) (clause \<cdot> \<theta>)"
 shows 
   "is_strictly_maximal\<^sub>l literal clause"
  using 
    is_maximal\<^sub>l_ground_subst_stability'[OF 
      assms(1,2) 
      is_maximal\<^sub>l_if_is_strictly_maximal\<^sub>l[OF assms(3)]
    ]
    assms(3)
  unfolding 
    is_strictly_maximal\<^sub>l_def is_maximal\<^sub>l_def
    subst_clause_remove1_mset[OF assms(1), symmetric]
  by (metis in_diffD literal_in_clause_subst reflclp_iff)

end

end
