theory First_Order_Superposition_With_Grounding
  imports First_Order_Superposition
begin

locale first_order_superposition_calculus_with_grounding =
  first_order_superposition_calculus +
  fixes select\<^sub>G 
  assumes select\<^sub>G: "is_ground_select select\<^sub>G"
begin

lemma select\<^sub>G_subset: "select\<^sub>G clause \<subseteq># clause"
  using select\<^sub>G 
  unfolding is_ground_select_def
  by (metis select_subset to_ground_clause_def image_mset_subseteq_mono subst_clause_def)

lemma select\<^sub>G_negative:
  assumes "literal\<^sub>G \<in># select\<^sub>G clause\<^sub>G"
  shows "is_neg literal\<^sub>G"
proof -
  obtain clause \<theta> where 
    is_ground: "is_ground_clause (clause \<cdot> \<theta>)" and
    select\<^sub>G: "select\<^sub>G clause\<^sub>G = to_ground_clause (select clause \<cdot> \<theta>)"
    using select\<^sub>G
    unfolding is_ground_select_def
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

sublocale ground: ground_superposition_calculus "(\<prec>\<^sub>t\<^sub>G)" select\<^sub>G
  apply(unfold_locales)
  by(auto simp: select\<^sub>G_subset select\<^sub>G_negative ground_critical_pair_theorem)

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

lemma less\<^sub>t_less_eq\<^sub>t_ground_subst_stability: assumes 
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
  (* TODO: *)
  by (metis (no_types, lifting) assms(1) assms(2) assms(3) in_diffD is_maximal\<^sub>l_def is_maximal\<^sub>l_ground_subst_stability' is_maximal\<^sub>l_if_is_strictly_maximal\<^sub>l is_strictly_maximal\<^sub>l_def literal_in_clause_subst reflclp_iff subst_clause_remove1_mset)

end

end

    