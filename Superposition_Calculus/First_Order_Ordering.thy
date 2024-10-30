theory First_Order_Ordering
  imports 
    First_Order_Clause
    Ground_Ordering
    Relation_Extra
begin

context ground_ordering
begin

lemmas less\<^sub>l\<^sub>G_transitive_on = literal_order.transp_on_less
lemmas less\<^sub>l\<^sub>G_asymmetric_on = literal_order.asymp_on_less
lemmas less\<^sub>l\<^sub>G_total_on = literal_order.totalp_on_less

lemmas less\<^sub>c\<^sub>G_transitive_on = clause_order.transp_on_less
lemmas less\<^sub>c\<^sub>G_asymmetric_on = clause_order.asymp_on_less
lemmas less\<^sub>c\<^sub>G_total_on = clause_order.totalp_on_less

lemmas is_maximal_lit_def = is_maximal_in_mset_wrt_iff[OF less\<^sub>l\<^sub>G_transitive_on less\<^sub>l\<^sub>G_asymmetric_on]
lemmas is_strictly_maximal_lit_def = 
  is_strictly_maximal_in_mset_wrt_iff[OF less\<^sub>l\<^sub>G_transitive_on less\<^sub>l\<^sub>G_asymmetric_on]

end

section \<open>First order ordering\<close>

locale first_order_ordering = term_ordering_lifting less\<^sub>t
  for
    less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) +
  assumes
    less\<^sub>t_total_on [intro]: "totalp_on {term. term.is_ground term} (\<prec>\<^sub>t)" and
    less\<^sub>t_wellfounded_on: "wfp_on {term. term.is_ground term} (\<prec>\<^sub>t)" and    
    less\<^sub>t_ground_context_compatible:
      "\<And>context term\<^sub>1 term\<^sub>2. 
        term\<^sub>1 \<prec>\<^sub>t term\<^sub>2 \<Longrightarrow>
        term.is_ground term\<^sub>1 \<Longrightarrow> 
        term.is_ground term\<^sub>2 \<Longrightarrow> 
        context.is_ground context \<Longrightarrow>
        context\<langle>term\<^sub>1\<rangle> \<prec>\<^sub>t context\<langle>term\<^sub>2\<rangle>" and
    less\<^sub>t_ground_subst_stability: 
      "\<And>term\<^sub>1 term\<^sub>2 (\<gamma> :: 'v \<Rightarrow> ('f, 'v) term). 
        term.is_ground (term\<^sub>1 \<cdot>t \<gamma>) \<Longrightarrow>
        term.is_ground (term\<^sub>2 \<cdot>t \<gamma>) \<Longrightarrow>
        term\<^sub>1 \<prec>\<^sub>t term\<^sub>2 \<Longrightarrow>
        term\<^sub>1 \<cdot>t \<gamma> \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<gamma>" and
    less\<^sub>t_ground_subterm_property: 
      "\<And>term\<^sub>G context\<^sub>G.
         term.is_ground term\<^sub>G \<Longrightarrow>
         context.is_ground context\<^sub>G \<Longrightarrow> 
         context\<^sub>G \<noteq> \<box> \<Longrightarrow> 
         term\<^sub>G \<prec>\<^sub>t context\<^sub>G\<langle>term\<^sub>G\<rangle>"
begin

lemmas less\<^sub>t_transitive = transp_less_trm 
lemmas less\<^sub>t_asymmetric = asymp_less_trm


subsection \<open>Definitions\<close>

abbreviation less_eq\<^sub>t (infix "\<preceq>\<^sub>t" 50) where
  "less_eq\<^sub>t \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

definition less\<^sub>t\<^sub>G :: "'f ground_term \<Rightarrow> 'f ground_term \<Rightarrow> bool" (infix "\<prec>\<^sub>t\<^sub>G" 50) where
  "term\<^sub>G\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>G\<^sub>2 \<equiv> term.from_ground term\<^sub>G\<^sub>1 \<prec>\<^sub>t term.from_ground term\<^sub>G\<^sub>2"

notation less_lit (infix "\<prec>\<^sub>l" 50)
notation less_cls (infix "\<prec>\<^sub>c" 50)

lemma
  assumes
    L_in: "L \<in># C" and
    subst_stability: "\<And>L K. L \<prec>\<^sub>l K \<Longrightarrow> (L \<cdot>l \<sigma>) \<prec>\<^sub>l (K \<cdot>l \<sigma>)" and
    L\<sigma>_max_in_C\<sigma>: "literal_order.is_maximal_in_mset (C \<cdot> \<sigma>) (L \<cdot>l \<sigma>)"
  shows "literal_order.is_maximal_in_mset C L"
proof -
  have L\<sigma>_in: "L \<cdot>l \<sigma> \<in># C \<cdot> \<sigma>" and L\<sigma>_max: "\<forall>y\<in>#C \<cdot> \<sigma>. y \<noteq> L \<cdot>l \<sigma> \<longrightarrow> \<not> L \<cdot>l \<sigma> \<prec>\<^sub>l y"
    using L\<sigma>_max_in_C\<sigma>
    unfolding atomize_conj literal_order.is_maximal_in_mset_iff
    by argo

  show "literal_order.is_maximal_in_mset C L"
    unfolding literal_order.is_maximal_in_mset_iff
  proof (intro conjI ballI impI)
    show "L \<in># C"
      using L_in .
  next
    show "\<And>y. y \<in># C \<Longrightarrow> y \<noteq> L \<Longrightarrow> \<not> L \<prec>\<^sub>l y"
      using subst_stability
      by (metis L\<sigma>_max clause.subst_in_to_set_subst literal_order.order.strict_iff_order)
  qed
qed

lemmas less\<^sub>l_def = less_lit_def
lemmas less\<^sub>c_def = less_cls_def

abbreviation less_eq\<^sub>l (infix "\<preceq>\<^sub>l" 50) where
  "less_eq\<^sub>l \<equiv> (\<prec>\<^sub>l)\<^sup>=\<^sup>="

abbreviation less_eq\<^sub>c (infix "\<preceq>\<^sub>c" 50) where
  "less_eq\<^sub>c \<equiv> (\<prec>\<^sub>c)\<^sup>=\<^sup>="

abbreviation is_maximal\<^sub>l :: 
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  "is_maximal\<^sub>l literal clause \<equiv> is_maximal_in_mset_wrt (\<prec>\<^sub>l) clause literal"

abbreviation is_strictly_maximal\<^sub>l :: 
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  "is_strictly_maximal\<^sub>l literal clause \<equiv> is_strictly_maximal_in_mset_wrt (\<prec>\<^sub>l) clause literal"


subsection \<open>Term ordering\<close>

lemmas less\<^sub>t_asymmetric_on = term_order.asymp_on_less
lemmas less\<^sub>t_irreflexive_on = term_order.irreflp_on_less
lemmas less\<^sub>t_transitive_on = term_order.transp_on_less

lemma less\<^sub>t_wellfounded_on': "Wellfounded.wfp_on (term.from_ground ` terms\<^sub>G) (\<prec>\<^sub>t)"
proof (rule Wellfounded.wfp_on_subset)
  show "Wellfounded.wfp_on {term. term.is_ground term} (\<prec>\<^sub>t)"
    using less\<^sub>t_wellfounded_on .
next
  show "term.from_ground ` terms\<^sub>G \<subseteq> {term. term.is_ground term}"
    by force
qed

lemma less\<^sub>t_total_on': "totalp_on (term.from_ground ` terms\<^sub>G) (\<prec>\<^sub>t)"
  using less\<^sub>t_total_on
  by (simp add: totalp_on_def)

lemma less\<^sub>t\<^sub>G_wellfounded: "wfp (\<prec>\<^sub>t\<^sub>G)"
proof -
  have "Wellfounded.wfp_on (range term.from_ground) (\<prec>\<^sub>t)"
    using less\<^sub>t_wellfounded_on' by metis
  hence "wfp (\<lambda>term\<^sub>G\<^sub>1 term\<^sub>G\<^sub>2. term.from_ground term\<^sub>G\<^sub>1 \<prec>\<^sub>t term.from_ground term\<^sub>G\<^sub>2)"
    unfolding Wellfounded.wfp_on_image[symmetric] .
  thus "wfp (\<prec>\<^sub>t\<^sub>G)"
    unfolding less\<^sub>t\<^sub>G_def .
qed

subsection \<open>Ground term ordering\<close>

lemma less\<^sub>t\<^sub>G_asymmetric [intro]: "asymp (\<prec>\<^sub>t\<^sub>G)"
  by (simp add: wfP_imp_asymp less\<^sub>t\<^sub>G_wellfounded)

lemmas less\<^sub>t\<^sub>G_asymmetric_on = less\<^sub>t\<^sub>G_asymmetric[THEN asymp_on_subset, OF subset_UNIV]

lemma less\<^sub>t\<^sub>G_transitive [intro]: "transp (\<prec>\<^sub>t\<^sub>G)"
  using less\<^sub>t\<^sub>G_def less\<^sub>t_transitive transpE transpI
  by (metis (full_types))

lemmas less\<^sub>t\<^sub>G_transitive_on = less\<^sub>t\<^sub>G_transitive[THEN transp_on_subset, OF subset_UNIV]

lemma less\<^sub>t\<^sub>G_total [intro]: "totalp (\<prec>\<^sub>t\<^sub>G)"
  unfolding less\<^sub>t\<^sub>G_def
  using totalp_on_image[OF inj_term_of_gterm] less\<^sub>t_total_on'
  by blast

lemmas less\<^sub>t\<^sub>G_total_on = less\<^sub>t\<^sub>G_total[THEN totalp_on_subset, OF subset_UNIV]

lemma less\<^sub>t\<^sub>G_context_compatible [simp]: 
  assumes "term\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>2"  
  shows "context\<langle>term\<^sub>1\<rangle>\<^sub>G \<prec>\<^sub>t\<^sub>G context\<langle>term\<^sub>2\<rangle>\<^sub>G"
  using assms less\<^sub>t_ground_context_compatible
  unfolding less\<^sub>t\<^sub>G_def
  by (metis context.ground_is_ground term.ground_is_ground ground_term_with_context(3)) 

lemma less\<^sub>t\<^sub>G_subterm_property [simp]: 
  assumes "context \<noteq> \<box>\<^sub>G" 
  shows "term \<prec>\<^sub>t\<^sub>G context\<langle>term\<rangle>\<^sub>G"
  using 
    assms
    less\<^sub>t_ground_subterm_property[OF term.ground_is_ground context.ground_is_ground] 
    context_from_ground_hole
  unfolding less\<^sub>t\<^sub>G_def ground_term_with_context(3)  
  by blast

lemma less\<^sub>t_less\<^sub>t\<^sub>G [clause_simp]: 
  assumes "term.is_ground term\<^sub>1" and "term.is_ground term\<^sub>2"
  shows "term\<^sub>1 \<prec>\<^sub>t term\<^sub>2 \<longleftrightarrow> term.to_ground term\<^sub>1 \<prec>\<^sub>t\<^sub>G term.to_ground term\<^sub>2"
  by (simp add: assms less\<^sub>t\<^sub>G_def)

lemma less_eq\<^sub>t_ground_subst_stability:
  assumes "term.is_ground (term\<^sub>1 \<cdot>t \<gamma>)" "term.is_ground (term\<^sub>2 \<cdot>t \<gamma>)"  "term\<^sub>1 \<preceq>\<^sub>t term\<^sub>2"
  shows "term\<^sub>1 \<cdot>t \<gamma> \<preceq>\<^sub>t term\<^sub>2 \<cdot>t \<gamma>"
  using less\<^sub>t_ground_subst_stability[OF assms(1, 2)] assms(3)
  by auto

subsection \<open>Literal ordering\<close>

lemmas less\<^sub>l_asymmetric [intro] = literal_order.asymp_on_less[of UNIV]
lemmas less\<^sub>l_asymmetric_on [intro] = literal_order.asymp_on_less

lemmas less\<^sub>l_transitive [intro] = literal_order.transp_on_less[of UNIV]
lemmas less\<^sub>l_transitive_on = literal_order.transp_on_less
                                                            
lemmas is_maximal\<^sub>l_def = is_maximal_in_mset_wrt_iff[OF less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on]

lemmas is_strictly_maximal\<^sub>l_def =
  is_strictly_maximal_in_mset_wrt_iff[OF less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on]

lemmas is_maximal\<^sub>l_if_is_strictly_maximal\<^sub>l =
  is_maximal_in_mset_wrt_if_is_strictly_maximal_in_mset_wrt[OF 
    less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on
  ]

lemma less\<^sub>l_ground_subst_stability: 
  assumes 
    "literal.is_ground (literal \<cdot>l \<gamma>)" 
    "literal.is_ground (literal' \<cdot>l \<gamma>)" 
  shows "literal \<prec>\<^sub>l literal' \<Longrightarrow> literal \<cdot>l \<gamma> \<prec>\<^sub>l literal' \<cdot>l \<gamma>"
  unfolding less\<^sub>l_def mset_mset_lit_subst[symmetric]
proof (elim multp_map_strong[rotated -1])
  show "monotone_on (set_mset (mset_lit literal + mset_lit literal')) (\<prec>\<^sub>t) (\<prec>\<^sub>t) (\<lambda>term. term \<cdot>t \<gamma>)"
    by (rule monotone_onI)
      (metis assms(1,2) less\<^sub>t_ground_subst_stability ground_term_in_ground_literal_subst union_iff)
qed (use less\<^sub>t_asymmetric less\<^sub>t_transitive in simp_all)

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

subsection \<open>Clause ordering\<close>

lemmas less\<^sub>c_asymmetric [intro] = clause_order.asymp_on_less[of UNIV]
lemmas less\<^sub>c_asymmetric_on [intro] = clause_order.asymp_on_less
lemmas less\<^sub>c_transitive [intro] = clause_order.transp_on_less[of UNIV]
lemmas less\<^sub>c_transitive_on [intro] = clause_order.transp_on_less

lemma less\<^sub>c_ground_subst_stability: 
  assumes 
    "clause.is_ground (clause \<cdot> \<gamma>)" 
    "clause.is_ground (clause' \<cdot> \<gamma>)" 
  shows "clause \<prec>\<^sub>c clause' \<Longrightarrow> clause \<cdot> \<gamma> \<prec>\<^sub>c clause' \<cdot> \<gamma>"
  unfolding clause.subst_def less\<^sub>c_def
proof (elim multp_map_strong[rotated -1])
  show "monotone_on (set_mset (clause + clause')) (\<prec>\<^sub>l) (\<prec>\<^sub>l) (\<lambda>literal. literal \<cdot>l \<gamma>)"
    by (rule monotone_onI)
      (metis assms(1,2) clause.to_set_is_ground_subst less\<^sub>l_ground_subst_stability union_iff)
qed (use less\<^sub>l_asymmetric less\<^sub>l_transitive in simp_all)

subsection \<open>Grounding\<close>

sublocale ground: ground_ordering "(\<prec>\<^sub>t\<^sub>G)" 
  apply unfold_locales
  by(simp_all add: less\<^sub>t\<^sub>G_transitive less\<^sub>t\<^sub>G_asymmetric less\<^sub>t\<^sub>G_wellfounded less\<^sub>t\<^sub>G_total)

notation ground.less_lit (infix "\<prec>\<^sub>l\<^sub>G" 50)
notation ground.less_cls (infix "\<prec>\<^sub>c\<^sub>G" 50)

notation ground.lesseq_trm (infix "\<preceq>\<^sub>t\<^sub>G" 50)
notation ground.lesseq_lit (infix "\<preceq>\<^sub>l\<^sub>G" 50)
notation ground.lesseq_cls (infix "\<preceq>\<^sub>c\<^sub>G" 50)

lemma not_less_eq\<^sub>t\<^sub>G: "\<not> term\<^sub>G\<^sub>2 \<preceq>\<^sub>t\<^sub>G term\<^sub>G\<^sub>1 \<longleftrightarrow> term\<^sub>G\<^sub>1 \<prec>\<^sub>t\<^sub>G term\<^sub>G\<^sub>2"
  using ground.term_order.not_le .

lemma less_eq\<^sub>t_less_eq\<^sub>t\<^sub>G:
  assumes "term.is_ground term\<^sub>1" and "term.is_ground term\<^sub>2" 
  shows "term\<^sub>1 \<preceq>\<^sub>t term\<^sub>2 \<longleftrightarrow> term.to_ground term\<^sub>1 \<preceq>\<^sub>t\<^sub>G term.to_ground term\<^sub>2"
  unfolding reflclp_iff less\<^sub>t_less\<^sub>t\<^sub>G[OF assms]
  using assms[THEN term.to_ground_inverse]
  by auto

lemma less_eq\<^sub>t\<^sub>G_less_eq\<^sub>t:
   "term\<^sub>G\<^sub>1 \<preceq>\<^sub>t\<^sub>G term\<^sub>G\<^sub>2 \<longleftrightarrow> term.from_ground term\<^sub>G\<^sub>1 \<preceq>\<^sub>t term.from_ground term\<^sub>G\<^sub>2"
  unfolding 
    less_eq\<^sub>t_less_eq\<^sub>t\<^sub>G[OF term.ground_is_ground term.ground_is_ground] 
    term.from_ground_inverse
  ..

lemma not_less_eq\<^sub>t: 
  assumes "term.is_ground term\<^sub>1" and "term.is_ground term\<^sub>2"
  shows "\<not> term\<^sub>2 \<preceq>\<^sub>t term\<^sub>1 \<longleftrightarrow> term\<^sub>1 \<prec>\<^sub>t term\<^sub>2"
  unfolding less\<^sub>t_less\<^sub>t\<^sub>G[OF assms] less_eq\<^sub>t_less_eq\<^sub>t\<^sub>G[OF assms(2, 1)] not_less_eq\<^sub>t\<^sub>G
  ..

lemma less\<^sub>l\<^sub>G_less\<^sub>l: 
  "literal\<^sub>G\<^sub>1 \<prec>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2 \<longleftrightarrow> literal.from_ground literal\<^sub>G\<^sub>1 \<prec>\<^sub>l literal.from_ground literal\<^sub>G\<^sub>2"
  unfolding less\<^sub>l_def ground.less_lit_def less\<^sub>t\<^sub>G_def mset_literal_from_ground
  using
     multp_image_mset_image_msetI[OF _ less\<^sub>t_transitive]
     multp_image_mset_image_msetD[OF _ less\<^sub>t_transitive_on term.inj_from_ground]
   by blast

lemma less\<^sub>l_less\<^sub>l\<^sub>G: 
  assumes "literal.is_ground literal\<^sub>1" "literal.is_ground literal\<^sub>2" 
  shows "literal\<^sub>1 \<prec>\<^sub>l literal\<^sub>2 \<longleftrightarrow> literal.to_ground literal\<^sub>1 \<prec>\<^sub>l\<^sub>G literal.to_ground literal\<^sub>2"
  using assms
  by (simp add: less\<^sub>l\<^sub>G_less\<^sub>l)

lemma less_eq\<^sub>l_less_eq\<^sub>l\<^sub>G:
  assumes "literal.is_ground literal\<^sub>1" and "literal.is_ground literal\<^sub>2" 
  shows "literal\<^sub>1 \<preceq>\<^sub>l literal\<^sub>2 \<longleftrightarrow> literal.to_ground literal\<^sub>1 \<preceq>\<^sub>l\<^sub>G literal.to_ground literal\<^sub>2"
  unfolding reflclp_iff less\<^sub>l_less\<^sub>l\<^sub>G[OF assms]
  using assms[THEN literal.to_ground_inverse]
  by auto

lemma less_eq\<^sub>l\<^sub>G_less_eq\<^sub>l:
   "literal\<^sub>G\<^sub>1 \<preceq>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2 \<longleftrightarrow> literal.from_ground literal\<^sub>G\<^sub>1 \<preceq>\<^sub>l literal.from_ground literal\<^sub>G\<^sub>2"
  unfolding 
    less_eq\<^sub>l_less_eq\<^sub>l\<^sub>G[OF literal.ground_is_ground literal.ground_is_ground] 
    literal.from_ground_inverse
  ..

lemma maximal_lit_in_clause:
  assumes "ground.is_maximal_lit literal\<^sub>G clause\<^sub>G"
  shows "literal\<^sub>G \<in># clause\<^sub>G"
  using assms 
  unfolding ground.is_maximal_lit_def
  by(rule conjunct1)

lemma is_maximal\<^sub>l_empty [simp]: 
  assumes "is_maximal\<^sub>l literal {#}"  
  shows False
  using assms maximal\<^sub>l_in_clause
  by fastforce

lemma is_strictly_maximal\<^sub>l_empty [simp]: 
  assumes "is_strictly_maximal\<^sub>l literal {#}"  
  shows False
  using assms strictly_maximal\<^sub>l_in_clause
  by fastforce

lemma is_maximal_lit_iff_is_maximal\<^sub>l: 
  "ground.is_maximal_lit literal\<^sub>G clause\<^sub>G \<longleftrightarrow> 
    is_maximal\<^sub>l (literal.from_ground literal\<^sub>G) (clause.from_ground clause\<^sub>G)"
   unfolding 
    is_maximal\<^sub>l_def
    ground.is_maximal_lit_def
    clause.ground_sub_in_ground[symmetric]
   using 
     less\<^sub>l_less\<^sub>l\<^sub>G[OF literal.ground_is_ground clause.sub_in_ground_is_ground] 
     clause.sub_in_ground_is_ground
     clause.ground_sub_in_ground
   by (metis literal.to_ground_inverse literal.from_ground_inverse)

lemma is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l:
  "ground.is_strictly_maximal_lit literal\<^sub>G clause\<^sub>G 
    \<longleftrightarrow> is_strictly_maximal\<^sub>l (literal.from_ground literal\<^sub>G) (clause.from_ground clause\<^sub>G)"
  unfolding 
    is_strictly_maximal_in_mset_wrt_iff_is_greatest_in_mset_wrt[OF 
      ground.less\<^sub>l\<^sub>G_transitive_on ground.less\<^sub>l\<^sub>G_asymmetric_on ground.less\<^sub>l\<^sub>G_total_on, symmetric
    ]
    ground.is_strictly_maximal_lit_def
    is_strictly_maximal\<^sub>l_def
    clause.ground_sub_in_ground[symmetric]
    remove1_mset_literal_from_ground
    clause.ground_sub
    less_eq\<^sub>l\<^sub>G_less_eq\<^sub>l
  ..
 
lemma not_less_eq\<^sub>l\<^sub>G: "\<not> literal\<^sub>G\<^sub>2 \<preceq>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>1 \<longleftrightarrow> literal\<^sub>G\<^sub>1 \<prec>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2"
  using asympD[OF ground.less\<^sub>l\<^sub>G_asymmetric_on] totalpD[OF ground.less\<^sub>l\<^sub>G_total_on]
  by blast

lemma not_less_eq\<^sub>l: 
  assumes "literal.is_ground literal\<^sub>1" and "literal.is_ground literal\<^sub>2"
  shows "\<not> literal\<^sub>2 \<preceq>\<^sub>l literal\<^sub>1 \<longleftrightarrow> literal\<^sub>1 \<prec>\<^sub>l literal\<^sub>2"
  unfolding less\<^sub>l_less\<^sub>l\<^sub>G[OF assms] less_eq\<^sub>l_less_eq\<^sub>l\<^sub>G[OF assms(2, 1)] not_less_eq\<^sub>l\<^sub>G
  ..

lemma less\<^sub>c\<^sub>G_less\<^sub>c: 
  "clause\<^sub>G\<^sub>1 \<prec>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2 \<longleftrightarrow> clause.from_ground clause\<^sub>G\<^sub>1 \<prec>\<^sub>c clause.from_ground clause\<^sub>G\<^sub>2"
proof (rule iffI)
  show "clause\<^sub>G\<^sub>1 \<prec>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2 \<Longrightarrow> clause.from_ground clause\<^sub>G\<^sub>1 \<prec>\<^sub>c clause.from_ground clause\<^sub>G\<^sub>2"
    unfolding less\<^sub>c_def
    by (auto simp: clause.from_ground_def ground.less_cls_def less\<^sub>l\<^sub>G_less\<^sub>l
        intro!: multp_image_mset_image_msetI elim: multp_mono_strong)
next
  have "transp (\<lambda>x y. literal.from_ground x \<prec>\<^sub>l literal.from_ground y)"
    by (metis (no_types, lifting) literal_order.less_trans transpI)
  thus "clause.from_ground clause\<^sub>G\<^sub>1 \<prec>\<^sub>c clause.from_ground clause\<^sub>G\<^sub>2 \<Longrightarrow> clause\<^sub>G\<^sub>1 \<prec>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2"
    unfolding ground.less_cls_def clause.from_ground_def less\<^sub>c_def
    by (auto simp: less\<^sub>l\<^sub>G_less\<^sub>l
        dest!: multp_image_mset_image_msetD[OF _ less\<^sub>l_transitive literal.inj_from_ground]
        elim!: multp_mono_strong)
qed

lemma less\<^sub>c_less\<^sub>c\<^sub>G: 
  assumes "clause.is_ground clause\<^sub>1" "clause.is_ground clause\<^sub>2"
  shows "clause\<^sub>1 \<prec>\<^sub>c clause\<^sub>2 \<longleftrightarrow> clause.to_ground clause\<^sub>1 \<prec>\<^sub>c\<^sub>G  clause.to_ground clause\<^sub>2"
  using assms
  by (simp add: less\<^sub>c\<^sub>G_less\<^sub>c)

lemma less_eq\<^sub>c_less_eq\<^sub>c\<^sub>G:
  assumes "clause.is_ground clause\<^sub>1" and "clause.is_ground clause\<^sub>2" 
  shows "clause\<^sub>1 \<preceq>\<^sub>c clause\<^sub>2 \<longleftrightarrow> clause.to_ground clause\<^sub>1 \<preceq>\<^sub>c\<^sub>G clause.to_ground clause\<^sub>2"
  unfolding reflclp_iff less\<^sub>c_less\<^sub>c\<^sub>G[OF assms]
  using assms[THEN clause.to_ground_inverse]
  by fastforce

lemma less_eq\<^sub>c\<^sub>G_less_eq\<^sub>c:
   "clause\<^sub>G\<^sub>1 \<preceq>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2 \<longleftrightarrow> clause.from_ground clause\<^sub>G\<^sub>1 \<preceq>\<^sub>c clause.from_ground clause\<^sub>G\<^sub>2"
  unfolding 
    less_eq\<^sub>c_less_eq\<^sub>c\<^sub>G[OF clause.ground_is_ground clause.ground_is_ground] 
    clause.from_ground_inverse
  ..

lemma not_less_eq\<^sub>c\<^sub>G: "\<not> clause\<^sub>G\<^sub>2 \<preceq>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>1 \<longleftrightarrow> clause\<^sub>G\<^sub>1 \<prec>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2"
  using asympD[OF ground.less\<^sub>c\<^sub>G_asymmetric_on] totalpD[OF ground.less\<^sub>c\<^sub>G_total_on]
  by blast

lemma not_less_eq\<^sub>c: 
  assumes "clause.is_ground clause\<^sub>1" and "clause.is_ground clause\<^sub>2"
  shows "\<not> clause\<^sub>2 \<preceq>\<^sub>c clause\<^sub>1 \<longleftrightarrow> clause\<^sub>1 \<prec>\<^sub>c clause\<^sub>2"
  unfolding less\<^sub>c_less\<^sub>c\<^sub>G[OF assms] less_eq\<^sub>c_less_eq\<^sub>c\<^sub>G[OF assms(2, 1)] not_less_eq\<^sub>c\<^sub>G
  ..

lemma less\<^sub>t_ground_context_compatible':
  assumes 
    "context.is_ground context" 
    "term.is_ground term" 
    "term.is_ground term'" 
    "context\<langle>term\<rangle> \<prec>\<^sub>t context\<langle>term'\<rangle>"
  shows "term \<prec>\<^sub>t term'"
  using assms 
  by (metis less\<^sub>t_ground_context_compatible not_less_eq\<^sub>t term_order.dual_order.asym 
        term_order.order.not_eq_order_implies_strict)
  

lemma less\<^sub>t_ground_context_compatible_iff:
   assumes 
    "context.is_ground context" 
    "term.is_ground term" 
    "term.is_ground term'" 
  shows "context\<langle>term\<rangle> \<prec>\<^sub>t context\<langle>term'\<rangle> \<longleftrightarrow> term \<prec>\<^sub>t term'"
  using assms less\<^sub>t_ground_context_compatible less\<^sub>t_ground_context_compatible'
  by blast

subsection \<open>Stability under ground substitution\<close>

lemma less\<^sub>t_less_eq\<^sub>t_ground_subst_stability:
  assumes 
    "term.is_ground (term\<^sub>1 \<cdot>t \<gamma>)"
    "term.is_ground (term\<^sub>2 \<cdot>t \<gamma>)"
    "term\<^sub>1 \<cdot>t \<gamma> \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<gamma>"
  shows
    "\<not> term\<^sub>2 \<preceq>\<^sub>t term\<^sub>1"
proof
  assume assumption: "term\<^sub>2 \<preceq>\<^sub>t term\<^sub>1"

  have "term\<^sub>2 \<cdot>t \<gamma> \<preceq>\<^sub>t term\<^sub>1 \<cdot>t \<gamma>"
    using less_eq\<^sub>t_ground_subst_stability[OF 
            assms(2, 1)
            assumption
           ].

  then show False 
    using assms(3) by order
qed

lemma less_eq\<^sub>l_ground_subst_stability:
  assumes   
    "literal.is_ground (literal\<^sub>1 \<cdot>l \<gamma>)" 
    "literal.is_ground (literal\<^sub>2 \<cdot>l \<gamma>)"  
    "literal\<^sub>1 \<preceq>\<^sub>l literal\<^sub>2"
  shows "literal\<^sub>1 \<cdot>l \<gamma> \<preceq>\<^sub>l literal\<^sub>2 \<cdot>l \<gamma>"
  using less\<^sub>l_ground_subst_stability[OF assms(1, 2)] assms(3)
  by auto

lemma less\<^sub>l_less_eq\<^sub>l_ground_subst_stability: assumes 
  "literal.is_ground (literal\<^sub>1 \<cdot>l \<gamma>)"
  "literal.is_ground (literal\<^sub>2 \<cdot>l \<gamma>)"
  "literal\<^sub>1 \<cdot>l \<gamma> \<prec>\<^sub>l literal\<^sub>2 \<cdot>l \<gamma>"
shows
  "\<not> literal\<^sub>2 \<preceq>\<^sub>l literal\<^sub>1"
  by (meson assms less_eq\<^sub>l_ground_subst_stability not_less_eq\<^sub>l)

lemma less_eq\<^sub>c_ground_subst_stability:
  assumes   
    "clause.is_ground (clause\<^sub>1 \<cdot> \<gamma>)" 
    "clause.is_ground (clause\<^sub>2 \<cdot> \<gamma>)"  
    "clause\<^sub>1 \<preceq>\<^sub>c clause\<^sub>2"
  shows "clause\<^sub>1 \<cdot> \<gamma> \<preceq>\<^sub>c clause\<^sub>2 \<cdot> \<gamma>"
  using less\<^sub>c_ground_subst_stability[OF assms(1, 2)] assms(3)
  by auto

lemma less\<^sub>c_less_eq\<^sub>c_ground_subst_stability: assumes 
  "clause.is_ground (clause\<^sub>1 \<cdot> \<gamma>)"
  "clause.is_ground (clause\<^sub>2 \<cdot> \<gamma>)"
  "clause\<^sub>1 \<cdot> \<gamma> \<prec>\<^sub>c clause\<^sub>2 \<cdot> \<gamma>"
shows
  "\<not> clause\<^sub>2 \<preceq>\<^sub>c clause\<^sub>1"
  by (meson assms less_eq\<^sub>c_ground_subst_stability not_less_eq\<^sub>c)
  
lemma is_maximal\<^sub>l_ground_subst_stability:
  assumes 
    clause_not_empty: "clause \<noteq> {#}" and
    clause_grounding: "clause.is_ground (clause \<cdot> \<gamma>)" 
  obtains literal
  where "is_maximal\<^sub>l literal clause" "is_maximal\<^sub>l (literal \<cdot>l \<gamma>) (clause \<cdot> \<gamma>)"
proof-
  assume assumption: 
    "\<And>literal. is_maximal\<^sub>l literal clause \<Longrightarrow> is_maximal\<^sub>l (literal \<cdot>l \<gamma>) (clause \<cdot> \<gamma>) \<Longrightarrow> thesis"

  from clause_not_empty 
  have clause_grounding_not_empty: "clause \<cdot> \<gamma> \<noteq> {#}"
    unfolding clause.subst_def
    by simp

  obtain literal where 
    literal: "literal \<in># clause" and
    literal_grounding_is_maximal: "is_maximal\<^sub>l (literal \<cdot>l \<gamma>) (clause \<cdot> \<gamma>)" 
    using
      ex_maximal_in_mset_wrt[OF less\<^sub>l_transitive_on less\<^sub>l_asymmetric_on clause_grounding_not_empty]  
      maximal\<^sub>l_in_clause
    unfolding clause.subst_def
    by force

  from literal_grounding_is_maximal
  have no_bigger_than_literal: 
    "\<forall>literal' \<in># clause \<cdot> \<gamma>. literal' \<noteq> literal \<cdot>l \<gamma> \<longrightarrow> \<not> literal \<cdot>l \<gamma> \<prec>\<^sub>l literal'"
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
         clause.to_set_is_ground_subst[OF _ clause_grounding]
      ]

    have "literal \<cdot>l \<gamma> \<prec>\<^sub>l literal' \<cdot>l \<gamma>"
      using less\<^sub>l_ground_subst_stability[OF literals_grounding literal'(2)].
   
    then have False
     using 
       no_bigger_than_literal
       clause.subst_in_to_set_subst[OF literal'(1)] 
     by (metis asymp_onD less\<^sub>l_asymmetric_on)
       
    then show ?thesis..
  qed
qed

lemma is_maximal\<^sub>l_ground_subst_stability':
  assumes 
   "literal \<in># clause"
   "clause.is_ground (clause \<cdot> \<gamma>)"
   "is_maximal\<^sub>l (literal \<cdot>l \<gamma>) (clause \<cdot> \<gamma>)"
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

  then have literal'_grounding: "literal.is_ground (literal' \<cdot>l \<gamma>)"
    using assms(2) clause.to_set_is_ground_subst by blast

  have literal_grounding: "literal.is_ground (literal \<cdot>l \<gamma>)"
    using assms(1) assms(2) clause.to_set_is_ground_subst by blast

  have literal_\<gamma>_in_premise: "literal' \<cdot>l \<gamma> \<in># clause \<cdot> \<gamma>"
    using clause.subst_in_to_set_subst[OF literal'(2)]
    by simp
     
  have "literal \<cdot>l \<gamma> \<prec>\<^sub>l literal' \<cdot>l \<gamma>"
    using less\<^sub>l_ground_subst_stability[OF literal_grounding literal'_grounding literal'(1)].
  
  then have "\<not> is_maximal\<^sub>l (literal \<cdot>l \<gamma>) (clause \<cdot> \<gamma>)"
    using literal_\<gamma>_in_premise 
    unfolding is_maximal\<^sub>l_def literal.subst_comp_subst
    by (metis asympD less\<^sub>l_asymmetric)
  
  then show False
    using assms(3)
    by blast
qed

lemma less\<^sub>l_total_on [intro]: "totalp_on (literal.from_ground ` literals\<^sub>G) (\<prec>\<^sub>l)"
  by (smt (verit, best) image_iff less\<^sub>l\<^sub>G_less\<^sub>l totalpD ground.less\<^sub>l\<^sub>G_total_on totalp_on_def)

lemmas less\<^sub>l_total_on_set_mset =
  less\<^sub>l_total_on[THEN totalp_on_subset, OF clause.to_set_from_ground[THEN equalityD1]]

lemma less\<^sub>c_total_on: "totalp_on (clause.from_ground ` clauses) (\<prec>\<^sub>c)"
  by (smt ground.clause_order.totalp_on_less image_iff less\<^sub>c\<^sub>G_less\<^sub>c totalpD totalp_onI)

lemma unique_maximal_in_ground_clause:
  assumes
    "clause.is_ground clause" 
    "is_maximal\<^sub>l literal clause"
    "is_maximal\<^sub>l literal' clause"
  shows
    "literal = literal'"
  using assms(2, 3)
  unfolding is_maximal\<^sub>l_def
  by (metis assms(1) less\<^sub>l_total_on_set_mset clause.to_ground_inverse totalp_onD)

lemma unique_strictly_maximal_in_ground_clause:
  assumes
    "clause.is_ground clause" 
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
   clause_grounding: "clause.is_ground (clause \<cdot> \<gamma>)" and
   ground_strictly_maximal: "is_strictly_maximal\<^sub>l literal\<^sub>G (clause \<cdot> \<gamma>)"
 obtains literal where 
   "is_strictly_maximal\<^sub>l literal clause" "literal \<cdot>l \<gamma> = literal\<^sub>G"
proof-
  assume assumption: "\<And>literal. 
    is_strictly_maximal\<^sub>l literal clause \<Longrightarrow> literal \<cdot>l \<gamma> = literal\<^sub>G \<Longrightarrow> thesis"

  have clause_grounding_not_empty: "clause \<cdot> \<gamma> \<noteq> {#}"
    using ground_strictly_maximal
    unfolding is_strictly_maximal\<^sub>l_def
    by fastforce

  have literal\<^sub>G_in_clause_grounding: "literal\<^sub>G \<in># clause \<cdot> \<gamma>"
    using ground_strictly_maximal is_strictly_maximal\<^sub>l_def by blast

  obtain literal where literal: "literal \<in># clause" "literal \<cdot>l \<gamma> = literal\<^sub>G"
    by (smt (verit, best) clause.subst_def imageE literal\<^sub>G_in_clause_grounding multiset.set_map)

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
       clause.to_set_is_ground_subst[OF literal(1) clause_grounding]

    have literal'_grounding: "literal.is_ground (literal' \<cdot>l \<gamma>)"
      using literal'(1) clause_grounding
      by (meson clause.to_set_is_ground_subst in_diffD)

    have "literal \<cdot>l \<gamma> \<preceq>\<^sub>l literal' \<cdot>l \<gamma>"
      using less_eq\<^sub>l_ground_subst_stability[OF literal_grounding literal'_grounding literal'(2)].

    then have False
      using  clause.subst_in_to_set_subst[OF literal'(1)]  ground_strictly_maximal 
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
   "clause.is_ground (clause \<cdot> \<gamma>)"
   "is_strictly_maximal\<^sub>l (literal \<cdot>l \<gamma>) (clause \<cdot> \<gamma>)"
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
  by (metis in_diffD clause.subst_in_to_set_subst reflclp_iff)

lemma less\<^sub>t_less\<^sub>l: 
  assumes "term\<^sub>1 \<prec>\<^sub>t term\<^sub>2"
  shows 
    "term\<^sub>1 \<approx> term\<^sub>3 \<prec>\<^sub>l term\<^sub>2 \<approx> term\<^sub>3"
    "term\<^sub>1 !\<approx> term\<^sub>3 \<prec>\<^sub>l term\<^sub>2 !\<approx> term\<^sub>3"
  using assms
  unfolding less\<^sub>l_def multp_eq_multp\<^sub>H\<^sub>O[OF less\<^sub>t_asymmetric less\<^sub>t_transitive] multp\<^sub>H\<^sub>O_def 
  by (auto simp: add_mset_eq_add_mset)

lemma less\<^sub>t_less\<^sub>l':
  assumes 
    "\<forall>term \<in> set_uprod (atm_of literal). term \<cdot>t \<sigma>' \<preceq>\<^sub>t term \<cdot>t \<sigma>"
    "\<exists>term \<in> set_uprod (atm_of literal). term \<cdot>t \<sigma>' \<prec>\<^sub>t term \<cdot>t \<sigma>"
  shows "literal \<cdot>l \<sigma>' \<prec>\<^sub>l literal \<cdot>l \<sigma>"
proof(cases literal)
  case (Pos atom)
  show ?thesis
  proof(cases atom)
    case (Upair term\<^sub>1 term\<^sub>2)
    have "term\<^sub>2 \<cdot>t \<sigma>' \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<sigma> \<Longrightarrow> 
          multp (\<prec>\<^sub>t) {#term\<^sub>1 \<cdot>t \<sigma>, term\<^sub>2 \<cdot>t \<sigma>'#} {#term\<^sub>1 \<cdot>t \<sigma>, term\<^sub>2 \<cdot>t \<sigma>#}"
      using multp_add_mset'[of "(\<prec>\<^sub>t)" "term\<^sub>2 \<cdot>t \<sigma>'"  "term\<^sub>2 \<cdot>t \<sigma>" "{#term\<^sub>1 \<cdot>t \<sigma>#}"] add_mset_commute
      by metis

    then show ?thesis 
      using assms
      unfolding less\<^sub>l_def Pos subst_literal(1) Upair subst_atom
      by (auto simp: multp_add_mset multp_add_mset')
  qed
next
  case (Neg atom)
  show ?thesis
   proof(cases atom)
     case (Upair term\<^sub>1 term\<^sub>2)
     have "term\<^sub>2 \<cdot>t \<sigma>' \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<sigma> \<Longrightarrow> 
            multp (\<prec>\<^sub>t) 
              {#term\<^sub>1 \<cdot>t \<sigma>, term\<^sub>1 \<cdot>t \<sigma>, term\<^sub>2 \<cdot>t \<sigma>', term\<^sub>2 \<cdot>t \<sigma>'#} 
              {#term\<^sub>1 \<cdot>t \<sigma>, term\<^sub>1 \<cdot>t \<sigma>, term\<^sub>2 \<cdot>t \<sigma>, term\<^sub>2 \<cdot>t \<sigma>#}"
       using multp_add_mset' multp_add_same[OF less\<^sub>t_asymmetric less\<^sub>t_transitive]
       by simp

     then show ?thesis 
      using assms
      unfolding less\<^sub>l_def Neg subst_literal(2) Upair subst_atom
      by (auto simp: multp_add_mset multp_add_mset' add_mset_commute)
  qed
qed

lemmas less\<^sub>c_add_mset = multp_add_mset_reflclp[OF less\<^sub>l_asymmetric less\<^sub>l_transitive, folded less\<^sub>c_def] 

lemmas less\<^sub>c_add_same = multp_add_same[OF less\<^sub>l_asymmetric less\<^sub>l_transitive, folded less\<^sub>c_def]

lemma less_eq\<^sub>l_less_eq\<^sub>c:
  assumes "\<forall>literal \<in># clause. literal \<cdot>l \<sigma>' \<preceq>\<^sub>l literal \<cdot>l \<sigma>"
  shows "clause \<cdot> \<sigma>' \<preceq>\<^sub>c clause \<cdot> \<sigma>"
  using assms 
  by(induction clause)(clause_auto simp: less\<^sub>c_add_same less\<^sub>c_add_mset)
   
lemma less\<^sub>l_less\<^sub>c:
  assumes 
    "\<forall>literal \<in># clause. literal \<cdot>l \<sigma>' \<preceq>\<^sub>l literal \<cdot>l \<sigma>"
    "\<exists>literal \<in># clause. literal \<cdot>l \<sigma>' \<prec>\<^sub>l literal \<cdot>l \<sigma>"
  shows "clause \<cdot> \<sigma>' \<prec>\<^sub>c clause \<cdot> \<sigma>"
  using assms
proof(induction clause)
  case empty
  then show ?case by auto
next
  case (add literal clause)
  then have less_eq: "\<forall>literal \<in># clause. literal \<cdot>l \<sigma>' \<preceq>\<^sub>l literal \<cdot>l \<sigma>"
    by (metis add_mset_remove_trivial in_diffD)

  show ?case 
  proof(cases "literal \<cdot>l \<sigma>' \<prec>\<^sub>l literal \<cdot>l \<sigma>")
    case True
    moreover have "clause \<cdot> \<sigma>' \<preceq>\<^sub>c clause \<cdot> \<sigma>"
      using less_eq\<^sub>l_less_eq\<^sub>c[OF less_eq].

    ultimately show ?thesis
      using less\<^sub>c_add_mset
      unfolding subst_clause_add_mset less\<^sub>c_def
      by blast
  next
    case False
    then have less: "\<exists>literal \<in># clause. literal \<cdot>l \<sigma>' \<prec>\<^sub>l literal \<cdot>l \<sigma>"
      using add.prems(2) by auto

   from False have eq: "literal \<cdot>l \<sigma>' = literal \<cdot>l \<sigma>"
      using add.prems(1) by force

   show ?thesis
     using add(1)[OF less_eq less] less\<^sub>c_add_same
     unfolding subst_clause_add_mset eq less\<^sub>c_def
     by blast
  qed
qed

subsection \<open>Substitution update\<close>

lemma less\<^sub>t_subst_upd:
  fixes \<gamma> :: "('f, 'v) subst"
  assumes 
    update_is_ground: "term.is_ground update" and
    update_less: "update \<prec>\<^sub>t \<gamma> var" and
    term_grounding: "term.is_ground (term \<cdot>t \<gamma>)" and
    var: "var \<in> term.vars term"
  shows "term \<cdot>t \<gamma>(var := update) \<prec>\<^sub>t term \<cdot>t \<gamma>"
  using assms(3, 4)
proof(induction "term")
  case Var
  then show ?case 
    using update_is_ground update_less
    by simp
next
  case (Fun f terms)

  then have "\<forall>term \<in> set terms. term \<cdot>t \<gamma>(var := update) \<preceq>\<^sub>t term \<cdot>t \<gamma>"
    by (metis eval_with_fresh_var is_ground_iff reflclp_iff term.set_intros(4))

  moreover then have "\<exists>term \<in> set terms. term \<cdot>t \<gamma>(var := update) \<prec>\<^sub>t term \<cdot>t \<gamma>"
    using Fun assms(2)
    by (metis (full_types) fun_upd_same  term.distinct(1) term.sel(4) term.set_cases(2) 
          term_order.dual_order.strict_iff_order term_subst_eq_rev)

  ultimately show ?case
    using Fun(2, 3)
  proof(induction "filter (\<lambda>term. term \<cdot>t \<gamma>(var := update) \<prec>\<^sub>t term \<cdot>t \<gamma>) terms" 
          arbitrary: terms)
    case Nil
    then show ?case
      unfolding empty_filter_conv
      by blast
  next
    case first: (Cons t ts)

    have update_grounding [simp]: "term.is_ground (t \<cdot>t \<gamma>(var := update))"
      using first.prems(3) update_is_ground first.hyps(2)
      by (metis (no_types, lifting) filter_eq_ConsD fun_upd_other fun_upd_same in_set_conv_decomp 
            is_ground_iff term.set_intros(4))

    then have t_grounding [simp]: "term.is_ground (t \<cdot>t \<gamma>)"
      using update_grounding Fun.prems(1,2)
      by (metis fun_upd_other is_ground_iff)
    
    show ?case
    proof(cases ts)
      case Nil
      then obtain ss1 ss2 where terms: "terms = ss1 @ t # ss2"
        using filter_eq_ConsD[OF first.hyps(2)[symmetric]]
        by blast

      have ss1: "\<forall>term \<in> set ss1. term \<cdot>t \<gamma>(var := update) = term \<cdot>t \<gamma>"
        using first.hyps(2) first.prems(1) 
        unfolding Nil terms
        by (smt (verit, del_insts) Un_iff append_Cons_eq_iff filter_empty_conv filter_eq_ConsD 
              set_append term_order.antisym_conv2)

      have ss2: "\<forall>term \<in> set ss2. term \<cdot>t \<gamma>(var := update) = term \<cdot>t \<gamma>"
        using first.hyps(2) first.prems(1) 
        unfolding Nil terms
        by (smt (verit, ccfv_SIG) Un_iff append_Cons_eq_iff filter_empty_conv filter_eq_ConsD 
              list.set_intros(2) set_append term_order.antisym_conv2)

      let ?context = "More f (map (\<lambda>term. (term \<cdot>t \<gamma>)) ss1) \<box> (map (\<lambda>term. (term \<cdot>t \<gamma>)) ss2)"

      have 1: "term.is_ground (t \<cdot>t \<gamma>)"
        using terms first(5)
        by auto

      moreover then have "term.is_ground (t \<cdot>t \<gamma>(var := update))"
        by (metis assms(1) fun_upd_other fun_upd_same is_ground_iff)

      moreover have "context.is_ground ?context"
        using terms first(5)
        by auto

      moreover have "t \<cdot>t \<gamma>(var := update) \<prec>\<^sub>t t \<cdot>t \<gamma>" 
        using first.hyps(2)
        by (meson Cons_eq_filterD)

      ultimately have "?context\<langle>t \<cdot>t \<gamma>(var := update)\<rangle> \<prec>\<^sub>t ?context\<langle>t \<cdot>t \<gamma>\<rangle>"
        using less\<^sub>t_ground_context_compatible
        by blast

      moreover have "Fun f terms \<cdot>t \<gamma>(var := update) = ?context\<langle>t \<cdot>t \<gamma>(var := update)\<rangle>"
        unfolding terms
        using ss1 ss2
        by simp

      moreover have "Fun f terms \<cdot>t \<gamma> = ?context\<langle>t \<cdot>t \<gamma>\<rangle>"
        unfolding terms
        by auto

      ultimately show ?thesis
        by argo
    next
      case (Cons t' ts')

      from first(2) 
      obtain ss1 ss2 where
        terms: "terms = ss1 @ t # ss2" and
        ss1: "\<forall>s\<in>set ss1. \<not> s \<cdot>t \<gamma>(var := update) \<prec>\<^sub>t s \<cdot>t \<gamma>" and
        less: "t \<cdot>t \<gamma>(var := update) \<prec>\<^sub>t t \<cdot>t \<gamma>" and 
        ts: "ts = filter (\<lambda>term. term \<cdot>t \<gamma>(var := update)\<prec>\<^sub>t term \<cdot>t \<gamma>) ss2"
        using Cons_eq_filter_iff[of t ts "(\<lambda>term. term \<cdot>t \<gamma>(var := update) \<prec>\<^sub>t term \<cdot>t \<gamma>)"]
        by blast

      let ?terms' = "ss1 @ (t \<cdot>t \<gamma>(var := update))  # ss2"

      have [simp]: "t \<cdot>t \<gamma>(var := update) \<cdot>t \<gamma> = t \<cdot>t \<gamma>(var := update)"
        using first.prems(3) update_is_ground
        unfolding terms
        by (simp add: is_ground_iff)

      have [simp]: "t \<cdot>t \<gamma>(var := update) \<cdot>t \<gamma>(var := update) = t \<cdot>t \<gamma>(var := update)"
        using first.prems(3) update_is_ground
        unfolding terms
        by (simp add: is_ground_iff)

      have "ts = filter (\<lambda>term. term \<cdot>t \<gamma>(var := update) \<prec>\<^sub>t term \<cdot>t \<gamma>) ?terms'" 
        using ss1 ts
        by auto
    
      moreover have "\<forall>term \<in> set ?terms'. term \<cdot>t \<gamma>(var := update) \<preceq>\<^sub>t term \<cdot>t \<gamma>"
        using first.prems(1)
        unfolding terms
        by simp
    
      moreover have "\<exists>term \<in> set ?terms'. term \<cdot>t \<gamma>(var := update) \<prec>\<^sub>t term \<cdot>t \<gamma>"
        using calculation(1) Cons neq_Nil_conv by force

      moreover have terms'_grounding: "term.is_ground (Fun f ?terms' \<cdot>t \<gamma>)"
        using first.prems(3)
        unfolding terms
        by simp
       
      moreover have "var \<in> term.vars (Fun f ?terms')"
        by (metis calculation(3) eval_with_fresh_var term.set_intros(4) term_order.less_irrefl)

      ultimately have less_terms': "Fun f ?terms' \<cdot>t \<gamma>(var := update) \<prec>\<^sub>t Fun f ?terms' \<cdot>t \<gamma>"
        using first.hyps(1) first.prems(3) by blast

      have context_grounding: "context.is_ground (More f ss1 \<box> ss2 \<cdot>t\<^sub>c \<gamma>)"
        using terms'_grounding
        by auto

      have "Fun f (ss1 @ t \<cdot>t \<gamma>(var := update) # ss2) \<cdot>t \<gamma> \<prec>\<^sub>t Fun f terms \<cdot>t \<gamma>"
        unfolding terms
        using less\<^sub>t_ground_context_compatible[OF less _ _ context_grounding]
        by simp

      with less_terms' show ?thesis 
        unfolding terms 
        by auto
    qed
  qed
qed

lemma less\<^sub>l_subst_upd:
  fixes \<gamma> :: "('f, 'v) subst"
  assumes 
    update_is_ground: "term.is_ground update" and
    update_less: "update \<prec>\<^sub>t \<gamma> var" and
    literal_grounding: "literal.is_ground (literal \<cdot>l \<gamma>)" and
    var: "var \<in> literal.vars literal"
  shows "literal \<cdot>l \<gamma>(var := update) \<prec>\<^sub>l literal \<cdot>l \<gamma>"
proof-
  note less\<^sub>t_subst_upd = less\<^sub>t_subst_upd[of _ \<gamma>, OF update_is_ground update_less] 

  have all_ground_terms: "\<forall>term \<in> set_uprod (atm_of literal). term.is_ground (term \<cdot>t \<gamma>)"
    using assms(3)
    apply(cases literal)
    by (simp add: ground_term_in_ground_literal_subst)+
     
  then have 
    "\<forall>term \<in> set_uprod (atm_of literal). 
       var \<in> term.vars term \<longrightarrow> term \<cdot>t \<gamma>(var := update) \<prec>\<^sub>t term \<cdot>t \<gamma>"
    using less\<^sub>t_subst_upd
    by blast

  moreover have
    "\<forall>term \<in> set_uprod (atm_of literal). 
       var \<notin> term.vars term \<longrightarrow> term \<cdot>t \<gamma>(var := update) = term \<cdot>t \<gamma>"
    by (meson eval_with_fresh_var)  

  ultimately have "\<forall>term \<in> set_uprod (atm_of literal). term \<cdot>t \<gamma>(var := update) \<preceq>\<^sub>t term \<cdot>t \<gamma>" 
    by blast

  moreover have "\<exists>term \<in> set_uprod (atm_of literal). term \<cdot>t \<gamma>(var := update) \<prec>\<^sub>t term \<cdot>t \<gamma>"
    using update_less var less\<^sub>t_subst_upd all_ground_terms
    unfolding literal.vars_def atom.vars_def set_literal_atm_of
    by blast

  ultimately show ?thesis
    using less\<^sub>t_less\<^sub>l'
    by blast
qed

lemma less\<^sub>c_subst_upd:
  assumes 
    update_is_ground: "term.is_ground update" and
    update_less: "update \<prec>\<^sub>t \<gamma> var" and
    literal_grounding: "clause.is_ground (clause \<cdot> \<gamma>)" and
    var: "var \<in> clause.vars clause"
  shows "clause \<cdot> \<gamma>(var := update) \<prec>\<^sub>c clause \<cdot> \<gamma>"
proof-
  note less\<^sub>l_subst_upd = less\<^sub>l_subst_upd[of _ \<gamma>, OF update_is_ground update_less] 

  have all_ground_literals: "\<forall>literal \<in># clause. literal.is_ground (literal \<cdot>l \<gamma>)"
    using clause.to_set_is_ground_subst[OF _ literal_grounding] by blast

  then have 
    "\<forall>literal \<in># clause. 
      var \<in> literal.vars literal \<longrightarrow> literal \<cdot>l \<gamma>(var := update) \<prec>\<^sub>l literal \<cdot>l \<gamma>"
    using less\<^sub>l_subst_upd
    by blast

  then have "\<forall>literal \<in># clause. literal \<cdot>l \<gamma>(var := update) \<preceq>\<^sub>l literal \<cdot>l \<gamma>"
    by fastforce

  moreover have "\<exists>literal \<in># clause. literal \<cdot>l \<gamma>(var := update) \<prec>\<^sub>l literal \<cdot>l \<gamma>"
    using update_less var less\<^sub>l_subst_upd all_ground_literals
    unfolding clause.vars_def
    by blast

  ultimately show ?thesis
    using less\<^sub>l_less\<^sub>c
    by blast
qed

end

end
