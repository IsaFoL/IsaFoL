theory First_Order_Ordering
  imports 
    First_Order_Clause 
    "Open_Induction.Restricted_Predicates"
begin

(* TODO: Move *)
context ground_superposition_calculus
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
    less\<^sub>t_transitive [intro]: "transp (\<prec>\<^sub>t)" and
    less\<^sub>t_asymmetric [intro]: "asymp (\<prec>\<^sub>t)" and 

    less\<^sub>t_wellfounded_on [intro]: "\<And>terms\<^sub>G. wfp_on (\<prec>\<^sub>t) (to_term ` terms\<^sub>G)" and
    less\<^sub>t_total_on [intro]: "\<And>terms\<^sub>G. totalp_on (to_term ` terms\<^sub>G) (\<prec>\<^sub>t)" and
    
    less\<^sub>t_ground_context_compatible [simp]:
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
    less\<^sub>t_ground_subterm_property [simp]: 
      "\<And>term\<^sub>G context\<^sub>G.
         is_ground_term term\<^sub>G \<Longrightarrow>
         is_ground_context context\<^sub>G \<Longrightarrow> 
         context\<^sub>G \<noteq> \<box> \<Longrightarrow> 
         term\<^sub>G \<prec>\<^sub>t context\<^sub>G\<langle>term\<^sub>G\<rangle>"
begin

definition less\<^sub>t\<^sub>G :: "'f ground_term \<Rightarrow> 'f ground_term \<Rightarrow> bool" (infix "\<prec>\<^sub>t\<^sub>G" 50) where
  "term\<^sub>G\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>G\<^sub>2 \<equiv> to_term term\<^sub>G\<^sub>1 \<prec>\<^sub>t to_term term\<^sub>G\<^sub>2"

lemma less\<^sub>t\<^sub>G_wellfounded [intro]: "wfP (\<prec>\<^sub>t\<^sub>G)"
  unfolding less\<^sub>t\<^sub>G_def
  using 
    wfp_on_image[OF inj_term_of_gterm less\<^sub>t_wellfounded_on]
    wfp_on_UNIV
  by blast

lemma less\<^sub>t\<^sub>G_total [intro]: "totalp (\<prec>\<^sub>t\<^sub>G)"
  unfolding less\<^sub>t\<^sub>G_def
  using less\<^sub>t_total_on
  by (auto simp: inj_term_of_gterm totalp_on_image)

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
    "literal \<prec>\<^sub>l literal'"
  shows
    "literal \<cdot>l \<theta> \<prec>\<^sub>l literal' \<cdot>l \<theta>"
  using 
      less\<^sub>t_ground_subst_stability[OF assms(1, 2)[THEN ground_term_in_ground_literal_subst]]
      multp_map_strong[OF less\<^sub>t_asymmetric less\<^sub>t_transitive]  
      assms(3)
  unfolding less\<^sub>l_def mset_mset_lit_subst[symmetric]
  by metis

lemma less\<^sub>c_ground_subst_stability: 
  assumes 
    "is_ground_clause (clause \<cdot> \<theta>)" 
    "is_ground_clause (clause' \<cdot> \<theta>)" 
    "clause \<prec>\<^sub>c clause'"
  shows
    "clause \<cdot> \<theta> \<prec>\<^sub>c clause' \<cdot> \<theta>"
  using 
      less\<^sub>l_ground_subst_stability[OF assms(1, 2)[THEN ground_literal_in_ground_clause_subst]]
      multp_map_strong[OF less\<^sub>l_asymmetric less\<^sub>l_transitive]  
      assms(3)
  unfolding subst_clause_def
  by simp

lemma less_eq\<^sub>t_ground_subst_stability:
  assumes "is_ground_term (term\<^sub>1 \<cdot>t \<theta>)" "is_ground_term (term\<^sub>2 \<cdot>t \<theta>)"  "term\<^sub>1 \<preceq>\<^sub>t term\<^sub>2"
  shows "term\<^sub>1 \<cdot>t \<theta> \<preceq>\<^sub>t term\<^sub>2 \<cdot>t \<theta>"
  using less\<^sub>t_ground_subst_stability[OF assms(1, 2)] assms(3)
  by auto

end

end
