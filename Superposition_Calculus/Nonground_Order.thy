theory Nonground_Order
  imports
    Nonground_Term_Order
    Term_Order_Lifting
    Nonground_Clause
    Relation_Extra
begin

section \<open>Nonground Order\<close>

locale nonground_order_lifting = 
  total_grounded_multiset_extension +
  ground_subst_stable_total_multiset_extension +
  subst_update_stable_multiset_extension
begin

sublocale grounded_restricted_total_strict_order where
  less = multiset_extension and subst = "subst" and vars = vars and to_ground = to_ground and 
  from_ground = "from_ground"
  by unfold_locales

end

locale nonground_term_based_order_lifting = nonground_order_lifting where 
  id_subst = Var and comp_subst = "(\<odot>)" and base_vars = term.vars and base_less = less\<^sub>t and 
  base_subst = "(\<cdot>t)"
for less\<^sub>t

locale nonground_order =
  restricted_term_order_lifting where
  restriction = "range term.from_ground" and
  less\<^sub>t = "less\<^sub>t :: ('f, 'v) Term.term \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> bool" +
  term.order: nonground_term_order
begin

(* TODO: Find way to not have this twice *)
notation term.order.less\<^sub>G (infix "\<prec>\<^sub>t\<^sub>G" 50)
notation term.order.less_eq\<^sub>G (infix "\<preceq>\<^sub>t\<^sub>G" 50)

sublocale literal.order: nonground_term_based_order_lifting where 
  less = less\<^sub>t and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and sub_to_ground = term.to_ground and 
  sub_from_ground = term.from_ground and map = map_literal_term and to_set = literal_to_term_set and
  to_ground_map = map_literal_term and from_ground_map = map_literal_term and 
  ground_map = map_literal_term and to_set_ground = literal_to_term_set and to_mset = mset_lit
rewrites
  "\<And>l \<sigma>. functional_substitution_lifting.subst (\<cdot>t) map_literal_term l \<sigma> = literal.subst l \<sigma>" and
  "\<And>l. functional_substitution_lifting.vars term.vars literal_to_term_set l = literal.vars l" and
  "\<And>l\<^sub>G. grounding_lifting.from_ground term.from_ground map_literal_term l\<^sub>G 
    = literal.from_ground l\<^sub>G" and
  "\<And>l. grounding_lifting.to_ground term.to_ground map_literal_term l = literal.to_ground l"
  by unfold_locales (auto simp: inj_mset_lit mset_lit_image_mset)

notation literal.order.less\<^sub>G (infix "\<prec>\<^sub>l\<^sub>G" 50)
notation literal.order.less_eq\<^sub>G (infix "\<preceq>\<^sub>l\<^sub>G" 50)

sublocale literal.order.restriction: maximal_literal "(\<prec>\<^sub>l\<^sub>G)"
  by unfold_locales

sublocale clause.order: nonground_term_based_order_lifting where 
  less = "(\<prec>\<^sub>l)" and sub_subst = literal.subst and sub_vars = literal.vars and
  sub_to_ground = literal.to_ground and sub_from_ground = literal.from_ground and 
  map = image_mset and to_set = set_mset and to_ground_map = image_mset and 
  from_ground_map = image_mset and ground_map = image_mset and to_set_ground = set_mset and 
  to_mset = "\<lambda>x. x"
  by unfold_locales simp_all

(*TODO: Restore scoping again! *)
notation clause.order.less\<^sub>G (infix "\<prec>\<^sub>c\<^sub>G" 50)
notation clause.order.less_eq\<^sub>G (infix "\<preceq>\<^sub>c\<^sub>G" 50)

lemma obtain_maximal_literal:
  assumes 
    not_empty: "C \<noteq> {#}" and
    grounding: "clause.is_ground (C \<cdot> \<gamma>)" 
  obtains l
  where "is_maximal l C" "is_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
proof-

  have grounding_not_empty: "C \<cdot> \<gamma> \<noteq> {#}"
    using not_empty clause_subst_empty(2) 
    by blast
    
  obtain l where 
    l_in_C: "l \<in># C" and
    l_grounding_is_maximal: "is_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)" 
    using
      ex_maximal_in_mset_wrt[OF 
        literal.order.transp_on_less literal.order.asymp_on_less grounding_not_empty]  
      maximal_in_clause
    unfolding clause.subst_def
    by (metis (mono_tags, lifting) image_iff multiset.set_map)

  show ?thesis
  proof(cases "is_maximal l C")
    case True

    with l_grounding_is_maximal that 
    show ?thesis
      by blast
  next
    case False
    then obtain l' where 
      l'_in_C: "l' \<in># C" and 
      l_less_l': "l \<prec>\<^sub>l l'" 
      unfolding is_maximal_def
      using l_in_C
      by blast 

    note literals_in_C = l_in_C l'_in_C
    note literals_grounding = literals_in_C[THEN clause.to_set_is_ground_subst[OF _ grounding]]

    have "l \<cdot>l \<gamma> \<prec>\<^sub>l l' \<cdot>l \<gamma>"
      using literal.order.ground_subst_stability[OF literals_grounding l_less_l'].
   
    then have False
     using 
       l_grounding_is_maximal
       clause.subst_in_to_set_subst[OF l'_in_C] 
     unfolding is_maximal_def
     by force
       
    then show ?thesis..
  qed
qed

lemma obtain_strictly_maximal_literal:
  assumes 
   grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
   ground_strictly_maximal: "is_strictly_maximal l\<^sub>G (C \<cdot> \<gamma>)"
 obtains l where 
   "is_strictly_maximal l C" "l\<^sub>G = l \<cdot>l \<gamma>"
proof-
 
  have grounding_not_empty: "C \<cdot> \<gamma> \<noteq> {#}"
    using ground_strictly_maximal
    by simp

  have l\<^sub>G_in_grounding: "l\<^sub>G \<in># C \<cdot> \<gamma>"
    using strictly_maximal_in_clause[OF ground_strictly_maximal].
   
  obtain l where 
    l_in_C: "l \<in># C" and 
    l\<^sub>G [simp]: "l\<^sub>G = l \<cdot>l \<gamma>"
    using l\<^sub>G_in_grounding 
    unfolding clause.subst_def
    by blast

  show ?thesis
  proof(cases "is_strictly_maximal l C")
    case True
    show ?thesis
      using that[OF True l\<^sub>G].
  next
    case False

    then obtain l' where
      l'_in_C: "l' \<in># C - {# l #}" and
      l_less_eq_l': "l \<preceq>\<^sub>l l'" 
      unfolding is_strictly_maximal_def
      using l_in_C 
      by blast
      
    note l_grounding = 
       clause.to_set_is_ground_subst[OF l_in_C grounding]

    have l'_grounding: "literal.is_ground (l' \<cdot>l \<gamma>)"
      using l'_in_C grounding
      by (meson clause.to_set_is_ground_subst in_diffD)

    have "l \<cdot>l \<gamma> \<preceq>\<^sub>l l' \<cdot>l \<gamma>"
      using literal.order.less_eq.ground_subst_stability[OF l_grounding l'_grounding l_less_eq_l'].

    then have False
      using clause.subst_in_to_set_subst[OF l'_in_C] ground_strictly_maximal 
      unfolding is_strictly_maximal_def subst_clause_remove1_mset[OF l_in_C]
      by simp
   
    then show ?thesis..
  qed
qed

lemma is_maximal_if_grounding_is_maximal:
  assumes
   l_in_C: "l \<in># C" and
   C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
   l_grounding_is_maximal: "is_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
 shows
   "is_maximal l C"
proof(rule ccontr)
  assume "\<not> is_maximal l C"

  then obtain l' where l_less_l': "l \<prec>\<^sub>l l'" and l'_in_C: "l' \<in># C"
    using l_in_C
    unfolding is_maximal_def
    by blast

  have l'_grounding: "literal.is_ground (l' \<cdot>l \<gamma>)"
    using clause.to_set_is_ground_subst[OF l'_in_C C_grounding].

  have l_grounding: "literal.is_ground (l \<cdot>l \<gamma>)"
    using clause.to_set_is_ground_subst[OF l_in_C C_grounding].

  have l'_\<gamma>_in_C_\<gamma>: "l' \<cdot>l \<gamma> \<in># C \<cdot> \<gamma>"
    using clause.subst_in_to_set_subst[OF l'_in_C].
     
  have "l \<cdot>l \<gamma> \<prec>\<^sub>l l' \<cdot>l \<gamma>"
    using literal.order.ground_subst_stability[OF l_grounding l'_grounding l_less_l'].
  
  then have "\<not> is_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
    using l'_\<gamma>_in_C_\<gamma> 
    unfolding is_maximal_def literal.subst_comp_subst
    by fastforce
  
  then show False
    using l_grounding_is_maximal..
qed

lemma is_strictly_maximal_if_grounding_is_strictly_maximal:
  assumes 
   l_in_C: "l \<in># C" and
   grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
   grounding_strictly_maximal: "is_strictly_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
 shows 
   "is_strictly_maximal l C"
  using
    is_maximal_if_grounding_is_maximal[OF 
      l_in_C
      grounding
      is_maximal_if_is_strictly_maximal[OF grounding_strictly_maximal]
    ]
    grounding_strictly_maximal  
  unfolding 
    is_strictly_maximal_def is_maximal_def
    subst_clause_remove1_mset[OF l_in_C, symmetric]
    reflclp_iff
  by (metis in_diffD clause.subst_in_to_set_subst)

lemma unique_maximal_in_ground_clause:
  assumes
    "clause.is_ground C" 
    "is_maximal l C"
    "is_maximal l' C"
  shows
    "l = l'"
  using assms clause.to_set_is_ground literal.order.not_less_eq 
  unfolding is_maximal_def reflclp_iff
  by meson

lemma unique_strictly_maximal_in_ground_clause:
  assumes
    "clause.is_ground C" 
    "is_strictly_maximal l C"
    "is_strictly_maximal l' C"
  shows
    "l = l'"
  using assms unique_maximal_in_ground_clause 
  by blast

(* TODO: *)
lemma X:
  "multiset_extension.multiset_extension (\<prec>\<^sub>t\<^sub>G) mset_lit = (\<prec>\<^sub>l\<^sub>G)"
proof-
  interpret multiset_extension "(\<prec>\<^sub>t\<^sub>G)" mset_lit
    by unfold_locales

  interpret relation_restriction "(\<lambda>b1 b2. multp (\<prec>\<^sub>t) (mset_lit b1) (mset_lit b2))" literal.from_ground
    by unfold_locales

  show ?thesis
    unfolding multiset_extension_def
    unfolding term.order.less\<^sub>G_def
    unfolding literal.order.multiset_extension_def 
    unfolding R\<^sub>r_def
    unfolding literal.from_ground_def atom.from_ground_def
    by (metis mset_lit_image_mset multp_image_mset_image_msetD multp_image_mset_image_msetI strict_order.transp term.inj_from_ground
        term.order.strict_order_axioms)
qed

lemma Y:
  "multiset_extension.multiset_extension (multiset_extension.multiset_extension (\<prec>\<^sub>t\<^sub>G) mset_lit) (\<lambda>x. x) = (\<prec>\<^sub>c\<^sub>G)"
  unfolding X
proof-
  interpret multiset_extension "(\<prec>\<^sub>l\<^sub>G)" "(\<lambda>x. x)"
    by unfold_locales

  interpret relation_restriction "multp (\<prec>\<^sub>l)" "clause.from_ground"
    by unfold_locales

  show "multiset_extension.multiset_extension (\<prec>\<^sub>l\<^sub>G) (\<lambda>x. x) = (\<prec>\<^sub>c\<^sub>G)"
    unfolding multiset_extension_def
    unfolding literal.order.less\<^sub>G_def
    unfolding clause.order.multiset_extension_def 
    unfolding R\<^sub>r_def
    unfolding clause.from_ground_def
    by (metis literal.inj_from_ground literal.order.transp multp_image_mset_image_msetD multp_image_mset_image_msetI)
qed

sublocale ground: ground_order where
  less\<^sub>t = "(\<prec>\<^sub>t\<^sub>G)"
rewrites
  "multiset_extension.multiset_extension (\<prec>\<^sub>t\<^sub>G) mset_lit = (\<prec>\<^sub>l\<^sub>G)" and
  "multiset_extension.multiset_extension (\<prec>\<^sub>l\<^sub>G) (\<lambda>x. x) = (\<prec>\<^sub>c\<^sub>G)" 
    apply unfold_locales
  by(auto simp: X  Y[unfolded X])

(* TODO: naming *)

lemma less\<^sub>t_less\<^sub>l: 
  assumes "term\<^sub>1 \<prec>\<^sub>t term\<^sub>2"
  shows 
    less\<^sub>t_less\<^sub>l_pos: "term\<^sub>1 \<approx> term\<^sub>3 \<prec>\<^sub>l term\<^sub>2 \<approx> term\<^sub>3" and
    less\<^sub>t_less\<^sub>l_neg: "term\<^sub>1 !\<approx> term\<^sub>3 \<prec>\<^sub>l term\<^sub>2 !\<approx> term\<^sub>3"
  using assms
  unfolding less\<^sub>l_def
  by (auto simp: multp_add_mset multp_add_mset' multp_add_same)

lemma literal_order_all_less_eq_ex_less_set:
  assumes 
    "\<forall>term \<in> set_uprod (atm_of literal). term \<cdot>t \<sigma>' \<preceq>\<^sub>t term \<cdot>t \<sigma>"
    "\<exists>term \<in> set_uprod (atm_of literal). term \<cdot>t \<sigma>' \<prec>\<^sub>t term \<cdot>t \<sigma>"
  shows "literal \<cdot>l \<sigma>' \<prec>\<^sub>l literal \<cdot>l \<sigma>"
  using literal.order.all_less_eq_ex_less[OF assms[folded set_mset_set_uprod]].
 
lemma less\<^sub>c_add_mset:
  assumes "l \<prec>\<^sub>l l'" "C \<preceq>\<^sub>c C'"
  shows "add_mset l C \<prec>\<^sub>c add_mset l' C'"
  using assms multp_add_mset_reflclp[OF literal.order.asymp literal.order.transp]
  unfolding less\<^sub>c_def
  by blast

lemmas less\<^sub>c_add_same =
  multp_add_same[OF literal.order.asymp literal.order.transp, folded less\<^sub>c_def]

(* TODO: Scope *)
lemma less_eq\<^sub>l_less_eq\<^sub>c:
  assumes "\<forall>literal \<in># clause. literal \<cdot>l \<sigma>' \<preceq>\<^sub>l literal \<cdot>l \<sigma>"
  shows "clause \<cdot> \<sigma>' \<preceq>\<^sub>c clause \<cdot> \<sigma>"
  using clause.order.all_less_eq[OF assms]. 
 
lemma less\<^sub>l_less\<^sub>c:
  assumes 
    "\<forall>literal \<in># clause. literal \<cdot>l \<sigma>' \<preceq>\<^sub>l literal \<cdot>l \<sigma>"
    "\<exists>literal \<in># clause. literal \<cdot>l \<sigma>' \<prec>\<^sub>l literal \<cdot>l \<sigma>"
  shows "clause \<cdot> \<sigma>' \<prec>\<^sub>c clause \<cdot> \<sigma>"
  using clause.order.all_less_eq_ex_less[OF assms].

lemma ground_is_maximal_iff_is_maximal: 
  "literal.order.restriction.is_maximal l C \<longleftrightarrow> is_maximal (literal.from_ground l) (clause.from_ground C)"
  unfolding is_maximal_def literal.order.restriction.is_maximal_def
  by (smt (verit, del_insts) clause.to_set_from_ground image_iff literal.from_ground_inverse
      literal.order.restriction.less\<^sub>r_def)

lemma ground_is_strictly_maximal_iff_is_strictly_maximal: 
  "literal.order.restriction.is_strictly_maximal l C \<longleftrightarrow> is_strictly_maximal (literal.from_ground l) (clause.from_ground C)"
  by (metis (no_types, lifting) clause.ground_sub_in_ground ground_is_maximal_iff_is_maximal in_diffD is_maximal_def is_strictly_maximal_def
      is_strictly_maximal_in_mset_wrt_iff literal.order.dual_order.order_iff_strict literal.order.less_eq\<^sub>r_from_ground
      literal.order.restriction.restriction.asymp_on_less
      literal.order.restriction.restriction.is_maximal_in_mset_if_is_strictly_maximal_in_mset
      literal.order.restriction.restriction.transp_on_less remove1_mset_literal_from_ground)

declare term.order.ground_subst_iff_base_ground_subst [simp del]

end

end
