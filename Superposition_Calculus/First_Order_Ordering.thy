theory First_Order_Ordering
  imports 
    Nonground_Clause
    Ground_Ordering
    Relation_Extra
begin

(* TODO: rename to not have "first order" in name*)
section \<open>First order ordering\<close>

locale first_order_ordering = grounded_term_ordering_lifting where 
  less\<^sub>t = less\<^sub>t 
  for
    less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) +
  assumes
    less\<^sub>t_ground_context_compatible [intro]:
      "\<And>c t\<^sub>1 t\<^sub>2.
        t\<^sub>1 \<prec>\<^sub>t t\<^sub>2 \<Longrightarrow>
        term.is_ground t\<^sub>1 \<Longrightarrow>
        term.is_ground t\<^sub>2 \<Longrightarrow>
        context.is_ground c \<Longrightarrow>
        c\<langle>t\<^sub>1\<rangle> \<prec>\<^sub>t c\<langle>t\<^sub>2\<rangle>" and
    less\<^sub>t_ground_subst_stability: 
      "\<And>t\<^sub>1 t\<^sub>2 (\<gamma> :: ('f, 'v) subst).
        term.is_ground (t\<^sub>1 \<cdot>t \<gamma>) \<Longrightarrow>
        term.is_ground (t\<^sub>2 \<cdot>t \<gamma>) \<Longrightarrow>
        t\<^sub>1 \<prec>\<^sub>t t\<^sub>2 \<Longrightarrow>
        t\<^sub>1 \<cdot>t \<gamma> \<prec>\<^sub>t t\<^sub>2 \<cdot>t \<gamma>" and
    less\<^sub>t_ground_subterm_property: 
      "\<And>t\<^sub>G c\<^sub>G.
        term.is_ground t\<^sub>G \<Longrightarrow>
        context.is_ground c\<^sub>G \<Longrightarrow>
        c\<^sub>G \<noteq> \<box> \<Longrightarrow>
        t\<^sub>G \<prec>\<^sub>t c\<^sub>G\<langle>t\<^sub>G\<rangle>"
begin

(*sublocale grounded_term_ordering_lifting where 
  less\<^sub>t = less\<^sub>t and from_ground = "term.from_ground"
  by unfold_locales (rule term.inj_from_ground)*)

(*lemma less\<^sub>t_wfp_on': "wfp_on {term. term.is_ground term} (\<prec>\<^sub>t)"
  using less\<^sub>t_wfp_on
  unfolding term.range_from_ground_iff_is_ground.

lemma less\<^sub>t_totalp_on': "totalp_on {term. term.is_ground term} (\<prec>\<^sub>t)"
  using less\<^sub>t_totalp_on
  unfolding term.range_from_ground_iff_is_ground.*)

(*sublocale ground: ground_ordering "(\<prec>\<^sub>t\<^sub>G)" 
proof unfold_locales 
  fix c t t'
  assume "t \<prec>\<^sub>t\<^sub>G t'"  
  then show "c\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t\<^sub>G c\<langle>t'\<rangle>\<^sub>G"
    using less\<^sub>t_ground_context_compatible
    unfolding less\<^sub>t\<^sub>G_def    
    by (metis context.ground_is_ground ground_term_with_context(3) term.ground_is_ground)
next
  fix t and c :: "'f ground_context"
  assume "c \<noteq> \<box>"
  then show "t \<prec>\<^sub>t\<^sub>G c\<langle>t\<rangle>\<^sub>G"
    using 
      less\<^sub>t_ground_subterm_property[OF term.ground_is_ground context.ground_is_ground] 
      context_from_ground_hole
    unfolding less\<^sub>t\<^sub>G_def ground_term_with_context(3)  
    by blast
qed*)

(* -- In lifting
lemma term_to_ground_less\<^sub>t\<^sub>G [clause_simp]: 
  assumes "term.is_ground t\<^sub>1" and "term.is_ground t\<^sub>2"
  shows "term.to_ground t\<^sub>1 \<prec>\<^sub>t\<^sub>G term.to_ground t\<^sub>2 \<longleftrightarrow> t\<^sub>1 \<prec>\<^sub>t t\<^sub>2"
  by (simp add: assms less\<^sub>t\<^sub>G_def)

lemma term_to_ground_less_eq\<^sub>t\<^sub>G [simp]:
  assumes "term.is_ground t\<^sub>1" and "term.is_ground t\<^sub>2" 
  shows "term.to_ground t\<^sub>1 \<preceq>\<^sub>t\<^sub>G term.to_ground t\<^sub>2 \<longleftrightarrow> t\<^sub>1 \<preceq>\<^sub>t t\<^sub>2"
  by (metis assms reflclp_iff term.to_ground_inverse term_to_ground_less\<^sub>t\<^sub>G)

lemma less_eq\<^sub>t\<^sub>G_term_from_ground [simp]:
   "t\<^sub>G\<^sub>1 \<preceq>\<^sub>t\<^sub>G t\<^sub>G\<^sub>2 \<longleftrightarrow> term.from_ground t\<^sub>G\<^sub>1 \<preceq>\<^sub>t term.from_ground t\<^sub>G\<^sub>2"
  unfolding less\<^sub>t\<^sub>G_def reflclp_iff 
  using term.from_ground_inverse
  by metis

  
lemma not_less_eq\<^sub>t [simp]: 
  assumes "term.is_ground term\<^sub>1" and "term.is_ground term\<^sub>2"
  shows "\<not> term\<^sub>2 \<preceq>\<^sub>t term\<^sub>1 \<longleftrightarrow> term\<^sub>1 \<prec>\<^sub>t term\<^sub>2"
  by (meson assms(1,2) term_order.restriction.not_less term_to_ground_less\<^sub>t\<^sub>G term_to_ground_less_eq\<^sub>t\<^sub>G)
  (*using ground.term_order.not_less
  by (meson assms(1,2) term_to_ground_less\<^sub>t\<^sub>G term_to_ground_less_eq\<^sub>t\<^sub>G)*)
--- -- 

(* TODO: Name + lifting *)
lemma less_eq\<^sub>t_ground_subst_stability:
  assumes "term.is_ground (term\<^sub>1 \<cdot>t \<gamma>)" "term.is_ground (term\<^sub>2 \<cdot>t \<gamma>)"  "term\<^sub>1 \<preceq>\<^sub>t term\<^sub>2"
  shows "term\<^sub>1 \<cdot>t \<gamma> \<preceq>\<^sub>t term\<^sub>2 \<cdot>t \<gamma>"
  using less\<^sub>t_ground_subst_stability[OF assms(1, 2)] assms(3)
  by auto*)


(* TODO: Name  + lifting? s 
lemma less\<^sub>l\<^sub>G_less\<^sub>l [simp]: 
  "literal\<^sub>G\<^sub>1 \<prec>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2 \<longleftrightarrow> literal.from_ground literal\<^sub>G\<^sub>1 \<prec>\<^sub>l literal.from_ground literal\<^sub>G\<^sub>2"
  unfolding less\<^sub>l_def less\<^sub>l\<^sub>G_def less\<^sub>t\<^sub>G_def mset_literal_from_ground
  using
     multp_image_mset_image_msetI
     multp_image_mset_image_msetD[OF _ term_order.transp_on_less term.inj_from_ground]
  (* TODO: *)
  by (simp add: literal'.from_ground_def mset_lit_image_mset)

lemma literal_to_ground_less\<^sub>l\<^sub>G [simp]: 
  assumes "literal.is_ground literal\<^sub>1" "literal.is_ground literal\<^sub>2" 
  shows "literal.to_ground literal\<^sub>1 \<prec>\<^sub>l\<^sub>G literal.to_ground literal\<^sub>2 \<longleftrightarrow> literal\<^sub>1 \<prec>\<^sub>l literal\<^sub>2"
  using assms
  by simp

lemma literal_to_ground_less_eq\<^sub>l\<^sub>G [simp]:
  assumes "literal.is_ground literal\<^sub>1" and "literal.is_ground literal\<^sub>2" 
  shows "literal.to_ground literal\<^sub>1 \<preceq>\<^sub>l\<^sub>G literal.to_ground literal\<^sub>2 \<longleftrightarrow> literal\<^sub>1 \<preceq>\<^sub>l literal\<^sub>2"
  using assms[THEN literal.to_ground_inverse]
  by auto

lemma less_eq\<^sub>l\<^sub>G_less_eq\<^sub>l [simp]:
   "literal\<^sub>G\<^sub>1 \<preceq>\<^sub>l\<^sub>G literal\<^sub>G\<^sub>2 \<longleftrightarrow> literal.from_ground literal\<^sub>G\<^sub>1 \<preceq>\<^sub>l literal.from_ground literal\<^sub>G\<^sub>2"
  using literal_to_ground_less_eq\<^sub>l\<^sub>G[OF literal.ground_is_ground literal.ground_is_ground]
  unfolding literal.from_ground_inverse.*)

subsection \<open>Literal ordering\<close>

(* TODO: Lifting 
lemma less\<^sub>l_ground_subst_stability: 
  assumes 
    "literal.is_ground (literal \<cdot>l \<gamma>)" 
    "literal.is_ground (literal' \<cdot>l \<gamma>)" 
  shows "literal \<prec>\<^sub>l literal' \<Longrightarrow> literal \<cdot>l \<gamma> \<prec>\<^sub>l literal' \<cdot>l \<gamma>"
  unfolding less\<^sub>l_def mset_mset_lit_subst[symmetric]
proof (elim multp_map_strong[rotated -1])
  show "monotone_on (set_mset (mset_lit literal + mset_lit literal')) (\<prec>\<^sub>t) (\<prec>\<^sub>t) (\<lambda>term. term \<cdot>t \<gamma>)"
    by (rule monotone_onI)
      (metis assms(1,2) less\<^sub>t_ground_subst_stability literal'.to_set_is_ground_subst union_iff)
qed simp

subsection \<open>Clause ordering\<close>

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
qed simp*)

subsection \<open>Grounding\<close>


(* TODO: Name *)


lemma not_less_eq\<^sub>l: 
  assumes "literal.is_ground literal\<^sub>1" and "literal.is_ground literal\<^sub>2"
  shows "\<not> literal\<^sub>2 \<preceq>\<^sub>l literal\<^sub>1 \<longleftrightarrow> literal\<^sub>1 \<prec>\<^sub>l literal\<^sub>2"
  using assms
  (* TODO: From literal_order.not_less_eq *)
  sorry
  
lemma less\<^sub>c\<^sub>G_less\<^sub>c: 
  "clause\<^sub>G\<^sub>1 \<prec>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2 \<longleftrightarrow> clause.from_ground clause\<^sub>G\<^sub>1 \<prec>\<^sub>c clause.from_ground clause\<^sub>G\<^sub>2"
  unfolding less\<^sub>c\<^sub>G_def..

lemma less\<^sub>c\<^sub>G_to_ground: 
  assumes "clause.is_ground clause\<^sub>1" "clause.is_ground clause\<^sub>2"
  shows "clause.to_ground clause\<^sub>1 \<prec>\<^sub>c\<^sub>G  clause.to_ground clause\<^sub>2 \<longleftrightarrow> clause\<^sub>1 \<prec>\<^sub>c clause\<^sub>2"
  using assms
  by (simp add: less\<^sub>c\<^sub>G_less\<^sub>c)

lemma less_eq\<^sub>c\<^sub>G_to_ground:
  assumes "clause.is_ground clause\<^sub>1" and "clause.is_ground clause\<^sub>2" 
  shows "clause.to_ground clause\<^sub>1 \<preceq>\<^sub>c\<^sub>G clause.to_ground clause\<^sub>2 \<longleftrightarrow> clause\<^sub>1 \<preceq>\<^sub>c clause\<^sub>2"
  unfolding reflclp_iff less\<^sub>c\<^sub>G_to_ground[OF assms]
  using assms[THEN clause.to_ground_inverse]
  by fastforce

lemma less_eq\<^sub>c\<^sub>G_less_eq\<^sub>c:
   "clause\<^sub>G\<^sub>1 \<preceq>\<^sub>c\<^sub>G clause\<^sub>G\<^sub>2 \<longleftrightarrow> clause.from_ground clause\<^sub>G\<^sub>1 \<preceq>\<^sub>c clause.from_ground clause\<^sub>G\<^sub>2"
  unfolding 
    less_eq\<^sub>c\<^sub>G_to_ground[OF clause.ground_is_ground clause.ground_is_ground, symmetric] 
    clause.from_ground_inverse
  ..

lemma not_less_eq\<^sub>c: 
  assumes "clause.is_ground clause\<^sub>1" and "clause.is_ground clause\<^sub>2"
  shows "\<not> clause\<^sub>2 \<preceq>\<^sub>c clause\<^sub>1 \<longleftrightarrow> clause\<^sub>1 \<prec>\<^sub>c clause\<^sub>2"
  using assms
  by (metis ground.clause_order.not_less less\<^sub>c\<^sub>G_to_ground less_eq\<^sub>c\<^sub>G_to_ground)

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

subsection \<open>Stability under ground substitution\<close> (* TODO: Lifting *)

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
  using assms
  using clause_order.leD less_eq\<^sub>c_ground_subst_stability by blast
  
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
      ex_maximal_in_mset_wrt[OF literal_order.transp_on_less literal_order.asymp_on_less clause_grounding_not_empty]  
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
     using literal_order.dual_order.strict_implies_not_eq by blast
       
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
    by fastforce
  
  then show False
    using assms(3)
    by blast
qed

(* TODO: Try to move these to the fitting others *)
lemma less\<^sub>l_total_on [intro]: "totalp_on (literal.from_ground ` literals\<^sub>G) (\<prec>\<^sub>l)"
  by (smt (verit, ccfv_SIG) image_iff literal.ground_is_ground not_less_eq\<^sub>l reflclp_iff totalp_on_def)

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
  using assms
  unfolding is_maximal\<^sub>l_def
  by (metis clause.to_set_is_ground literal_order.le_imp_less_or_eq not_less_eq\<^sub>l)

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

(* TODO: Put in right sections + naming *)

lemma less\<^sub>t_less\<^sub>l: 
  assumes "term\<^sub>1 \<prec>\<^sub>t term\<^sub>2"
  shows 
    "term\<^sub>1 \<approx> term\<^sub>3 \<prec>\<^sub>l term\<^sub>2 \<approx> term\<^sub>3"
    "term\<^sub>1 !\<approx> term\<^sub>3 \<prec>\<^sub>l term\<^sub>2 !\<approx> term\<^sub>3"
  using assms
  unfolding less\<^sub>l_def multp_eq_multp\<^sub>H\<^sub>O[OF less\<^sub>t_asymp less\<^sub>t_transp] multp\<^sub>H\<^sub>O_def 
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
       using multp_add_mset' multp_add_same[OF less\<^sub>t_asymp less\<^sub>t_transp]
       by simp

     then show ?thesis 
      using assms
      unfolding less\<^sub>l_def Neg subst_literal(2) Upair subst_atom
      by (auto simp: multp_add_mset multp_add_mset' add_mset_commute)
  qed
qed

lemma less\<^sub>c_add_mset: "l \<prec>\<^sub>l l' \<Longrightarrow>C \<preceq>\<^sub>c C' \<Longrightarrow> add_mset l C \<prec>\<^sub>c add_mset l' C'"
  by (simp add: less\<^sub>c_def multp_add_mset_reflclp)

(* TODO: lemmas less\<^sub>c_add_mset = multp_add_mset_reflclp[OF literal_order.asymp literal_order.transp, folded less\<^sub>c_def]  *)

lemmas less\<^sub>c_add_same = multp_add_same[OF literal_order.asymp literal_order.transp, folded less\<^sub>c_def]

lemma less_eq\<^sub>l_less_eq\<^sub>c:
  assumes "\<forall>literal \<in># clause. literal \<cdot>l \<sigma>' \<preceq>\<^sub>l literal \<cdot>l \<sigma>"
  shows "clause \<cdot> \<sigma>' \<preceq>\<^sub>c clause \<cdot> \<sigma>"
  using assms  less\<^sub>c_add_same less\<^sub>c_add_mset
  unfolding less\<^sub>c_def
  by(induction clause) (auto simp: empty_clause_is_ground)
 
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
      unfolding clause.add_subst less\<^sub>c_def
      by blast
  next
    case False
    then have less: "\<exists>literal \<in># clause. literal \<cdot>l \<sigma>' \<prec>\<^sub>l literal \<cdot>l \<sigma>"
      using add.prems(2) by auto

   from False have eq: "literal \<cdot>l \<sigma>' = literal \<cdot>l \<sigma>"
      using add.prems(1) by force

   show ?thesis
     using add(1)[OF less_eq less] less\<^sub>c_add_same
     unfolding clause.add_subst eq less\<^sub>c_def
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
    using literal'.to_set_is_ground_subst[OF _ assms(3)] 
    unfolding set_mset_set_uprod
    by blast   
     
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
