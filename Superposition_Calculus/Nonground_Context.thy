theory Nonground_Context
  imports 
    Nonground_Term
    Functional_Substitution_Lifting
begin

section \<open>Nonground Contexts and Substitutions\<close>

find_consts "('f,'a) actxt \<Rightarrow> 'a set"

lemma xx: "finite (set2_actxt c)"
  apply(induction c)
  by auto

locale clause_lifting' =
  based_functional_substitution_lifting where 
  base_subst = "(\<cdot>t)" and base_vars = term.vars and id_subst = Var and comp_subst = "(\<odot>)" + 
  all_subst_ident_iff_ground_lifting where id_subst = Var and comp_subst = "(\<odot>)" +
  grounding_lifting where id_subst = Var and comp_subst = "(\<odot>)" +
  renaming_variables_lifting where id_subst = Var and comp_subst = "(\<odot>)" +
  variables_in_base_imgu_lifting where id_subst = Var and comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars 

global_interpretation "context": clause_lifting' where 
    sub_vars = term.vars and sub_subst = "(\<cdot>t)" and to_set = "set2_actxt" and map = "map_args_actxt"
    and sub_to_ground = term.to_ground and sub_from_ground = term.from_ground 
    and to_ground_map = map_args_actxt and from_ground_map = map_args_actxt and ground_map = map_args_actxt
    and to_set_ground = set2_actxt
   rewrites 
    "\<And>c. context.vars c = vars_ctxt c" and 
    "\<And>c \<sigma>. context.subst c \<sigma> = c \<cdot>\<^sub>c \<sigma>"
    apply unfold_locales
          apply (simp add: actxt.map_comp fun.map_ident)
         apply (simp add: actxt.map_cong)
        apply (metis actxt.map_cong)
       apply (simp add: actxt.set_map(2))
            apply (metis actxt.set_intros(5) in_set_conv_decomp)
           apply (meson is_ground_iff)

          apply (simp add: actxt.set_map(2))
  apply (simp add: xx)
        apply (simp add: actxt.map_comp fun.map_ident)
  apply (simp add: actxt.set_map(2))
       apply (simp add: actxt.map_comp fun.map_ident)
  apply (simp add: actxt.map_comp fun.map_ident)
    apply (simp add: actxt.map_cong)
  (* TODO *)
  sorry


(*global_interpretation "context":
  grounding_lifting where 
    id_subst = Var and comp_subst = "(\<odot>)" and 
    sub_vars = term.vars and sub_subst = "(\<cdot>t)" and to_set = "set2_actxt" and map = "map_args_actxt"
    and sub_to_ground = term.to_ground and sub_from_ground = term.from_ground 
    and to_ground_map = map_args_actxt and from_ground_map = map_args_actxt and ground_map = map_args_actxt
    and to_set_ground = set2_actxt
  rewrites 
    "\<And>c. context.vars c = vars_ctxt c" and 
    "\<And>c \<sigma>. context.subst c \<sigma> = c \<cdot>\<^sub>c \<sigma>"
  apply unfold_locales
          apply (simp add: actxt.map_comp fun.map_ident)
         apply (simp add: actxt.map_cong)
        apply (metis actxt.map_cong)
       apply (simp add: actxt.set_map(2))
      apply (metis actxt.set_intros(5) in_set_conv_decomp)
     apply (simp add: actxt.set_map(2))
    apply (simp add: actxt.map_comp fun.map_ident)
   apply (simp add: actxt.map_comp fun.map_ident)
    apply (simp add: actxt.map_cong)
  sorry

global_interpretation "context": based_functional_substitution_lifting 
  where comp_subst = "(\<odot>)"  and id_subst = Var and sub_vars = term.vars and sub_subst = "(\<cdot>t)"
    and to_set = "set2_actxt" and map = "map_args_actxt" and base_subst = "(\<cdot>t)" 
    and base_vars = term.vars
  (*rewrites 
    "\<And>c. context.vars c = vars_ctxt c" and 
    "\<And>c \<sigma>. context.subst c \<sigma> = c \<cdot>\<^sub>c \<sigma>"*) +
  all_subst_ident_iff_ground_lifting where 
    id_subst = Var and comp_subst = "(\<odot>)"  and sub_vars = term.vars and sub_subst = "(\<cdot>t)" and to_set = "set2_actxt" and map = "map_args_actxt"
proof-
  interpret based_functional_substitution_lifting 
    where comp_subst = "(\<odot>)"  and id_subst = Var and sub_vars = term.vars and sub_subst = "(\<cdot>t)"
      and to_set = "set2_actxt" and map = "map_args_actxt" and base_subst = "(\<cdot>t)" 
      and base_vars = term.vars
  proof unfold_locales
    show "\<And>expr \<gamma>. (term.vars (expr \<cdot>t \<gamma>) = {}) = (\<forall>var\<in>term.vars expr. term.vars (\<gamma> var) = {})"
      by (simp add: is_ground_iff)
  qed auto

 fix c :: "('a, ('f, 'v) Term.term) actxt"
  show "context.vars c = vars_ctxt c"
    unfolding context.vars_def 
    apply(induction c) 
    by auto

  fix \<sigma> 
  show "context.subst c \<sigma> = c \<cdot>\<^sub>c \<sigma>"
  by blast

  show "based_functional_substitution_lifting (\<odot>) Var term.vars (\<cdot>t) map_args_actxt (\<cdot>t) term.vars set2_actxt"
    by unfold_locales

  show "all_subst_ident_iff_ground_lifting (\<odot>) term.vars (\<cdot>t) set2_actxt map_args_actxt Var"
  proof unfold_locales
    fix c :: "('l, ('k, 'j) Term.term) actxt"
    show "finite (set2_actxt c)"
      apply(induction c)
      by auto
  qed
qed

global_interpretation "context": all_subst_ident_iff_ground_lifting where 
  id_subst = Var and comp_subst = "(\<odot>)" and sub_vars = term.vars and sub_subst = "(\<cdot>t)"
  and to_set = "set2_actxt" and map = "map_args_actxt"
proof unfold_locales
  fix c :: "('c, ('b, 'a) Term.term) actxt"
  show "finite (set2_actxt c)"
    apply(induction c)
    by auto
qed*)

(* TODO: Try how much can be generalized using abstract contexts 
global_interpretation "context": all_subst_ident_iff_ground where 
  is_ground = "\<lambda>c. context.vars c = {}" and subst = "(\<cdot>t\<^sub>c)"
proof unfold_locales
  fix c :: "('f, 'v) context"
  show "context.vars c = {} = (\<forall>\<sigma>. c \<cdot>t\<^sub>c \<sigma> = c)"
  proof (intro iffI)
    show "context.vars c = {} \<Longrightarrow> \<forall>\<sigma>. c \<cdot>t\<^sub>c \<sigma> = c"
      by(induction c) (simp_all add: list.map_ident_strong)
  next
    assume "\<forall>\<sigma>. c \<cdot>t\<^sub>c \<sigma> = c"

    then have "\<And>t\<^sub>G. term.is_ground t\<^sub>G \<Longrightarrow> \<forall>\<sigma>. c\<langle>t\<^sub>G\<rangle> \<cdot>t \<sigma> = c\<langle>t\<^sub>G\<rangle>"
      by simp

    then have "\<And>t\<^sub>G. term.is_ground t\<^sub>G \<Longrightarrow> term.is_ground c\<langle>t\<^sub>G\<rangle>"
      by (meson is_ground_trm_iff_ident_forall_subst)

    then show "context.vars c = {}"
      by (metis sup.commute sup_bot_left vars_term_ctxt_apply vars_term_of_gterm)
  qed
next
  fix c :: "('f, 'v) context" and cs :: "('f, 'v) context set"
  assume finite: "finite cs" and non_ground: "context.vars c \<noteq> {}"

  then show "\<exists>\<sigma>. c \<cdot>t\<^sub>c \<sigma> \<noteq> c \<and> c \<cdot>t\<^sub>c \<sigma> \<notin> cs"
  proof(induction c arbitrary: cs)
    case Hole
    then show ?case
      by simp
  next
    case (More f ts c ts')

    show ?case
    proof(cases "context.vars c = {}")
      case True

      let ?sub_terms = 
        "\<lambda>c :: ('f, 'v) context. case c of More _ ts _ ts' \<Rightarrow> set ts \<union> set ts'  | _ \<Rightarrow> {}"

      let ?cs' = "set ts \<union> set ts' \<union> \<Union>(?sub_terms ` cs)"

      from True obtain t where t: "t \<in> set ts \<union> set ts'" and non_ground: "\<not>term.is_ground t"
        using More.prems by auto

      have "\<And>c. finite (?sub_terms c)"
      proof-  
        fix c
        show "finite (?sub_terms c)"
          by(cases c) simp_all
      qed

      then have "finite (\<Union>(?sub_terms ` cs))"
        using More.prems(1) by blast

      then have finite: "finite ?cs'"
        by blast

      obtain \<sigma> where \<sigma>: "t \<cdot>t \<sigma> \<noteq> t" and cs': "t \<cdot>t \<sigma> \<notin> ?cs'"
        using term.exists_non_ident_subst[OF finite non_ground]
        by blast

      then have "More f ts c ts' \<cdot>t\<^sub>c \<sigma> \<noteq> More f ts c ts'"
        using t set_map_id[of _  _ "\<lambda>t. t \<cdot>t \<sigma>"]
        by auto

      moreover have " More f ts c ts' \<cdot>t\<^sub>c \<sigma> \<notin> cs"
        using cs' t
        by auto

      ultimately show ?thesis
        by blast
    next
      case False

      let ?sub_contexts = "(\<lambda>c. case c of More _ _ c _ \<Rightarrow> c) ` {c \<in> cs. c \<noteq> \<box>}"

      have "finite ?sub_contexts"
        using More.prems(1)
        by auto

      then obtain \<sigma> where \<sigma>: "c \<cdot>t\<^sub>c \<sigma> \<noteq> c" and sub_contexts: "c \<cdot>t\<^sub>c \<sigma> \<notin> ?sub_contexts"
        using More.IH[OF _ False]
        by blast

      then have "More f ts c ts' \<cdot>t\<^sub>c \<sigma> \<noteq> More f ts c ts'"
        by simp

      moreover have "More f ts c ts' \<cdot>t\<^sub>c \<sigma> \<notin> cs"
        using sub_contexts image_iff
        by fastforce

      ultimately show ?thesis 
        by blast
    qed
  qed
qed
*)
(*global_interpretation "context": based_functional_substitution where
  subst = "(\<cdot>t\<^sub>c)" and vars = context.vars and id_subst = Var and comp_subst = "(\<odot>)" and 
  base_vars = term.vars and base_subst = "(\<cdot>t)"
proof(unfold_locales, unfold substitution_ops.is_ground_subst_def)
  fix c :: "('f, 'v) context"
  show "c \<cdot>t\<^sub>c Var = c"
    by (induction c) auto
next
  show "\<And>c \<sigma> \<tau>. c \<cdot>t\<^sub>c \<sigma> \<odot> \<tau> = c \<cdot>t\<^sub>c \<sigma> \<cdot>t\<^sub>c \<tau>"
    by simp
next
  show "\<And>c. context.vars c = {} \<Longrightarrow> \<forall>\<sigma>. c \<cdot>t\<^sub>c \<sigma> = c"
    using context.all_subst_ident_iff_ground by blast
next 
  show "\<And>c \<sigma> \<tau>. (\<And>x. x \<in> context.vars c \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> c \<cdot>t\<^sub>c \<sigma> = c \<cdot>t\<^sub>c \<tau>"
    using ctxt_subst_eq.
next
  fix \<gamma> :: "('f,'v) subst"

  show "(\<forall>c. context.vars (c \<cdot>t\<^sub>c \<gamma>) = {}) \<longleftrightarrow> (\<forall>t. term.vars (t \<cdot>t \<gamma>) = {})"
  proof(intro iffI allI equals0I)
    fix t x

    assume is_ground: "\<forall>c. context.vars (c \<cdot>t\<^sub>c \<gamma>) = {}" and vars: "x \<in> term.vars (t \<cdot>t \<gamma>)"

    have "\<And>f. context.vars (More f [t] Hole [] \<cdot>t\<^sub>c \<gamma>) = {}"
      using is_ground
      by presburger

    moreover have "\<And>f. x \<in> context.vars (More f [t] Hole [] \<cdot>t\<^sub>c \<gamma>)"
      using vars
      by simp

    ultimately show False
      by blast
  next
    fix c x
    assume is_ground: "\<forall>t. term.is_ground (t \<cdot>t \<gamma>)" and vars: "x \<in> context.vars (c \<cdot>t\<^sub>c \<gamma>)"

    have "\<And>t. term.is_ground (c\<langle>t\<rangle> \<cdot>t \<gamma>)"
      using is_ground
      by presburger

    moreover have "\<And>t. x \<in> term.vars (c\<langle>t\<rangle> \<cdot>t \<gamma>)"
      using vars
      by simp

    ultimately show False
      by blast
  qed
next
  fix c and \<gamma> :: "('f, 'v) subst"

  show "context.vars (c \<cdot>t\<^sub>c \<gamma>) = {} \<longleftrightarrow> (\<forall>x \<in> context.vars c. term.is_ground (\<gamma> x))"
    by(induction c)(auto simp: term.is_grounding_iff_vars_grounded)
qed

global_interpretation "context": finite_variables 
  where vars = "context.vars :: ('f, 'v) context \<Rightarrow> 'v set"
proof unfold_locales
  fix c :: "('f, 'v) context"

  have "\<And>t. finite (term.vars c\<langle>t\<rangle>)"
    using term.finite_vars by blast

  then show "finite (context.vars c)"
    unfolding vars_term_ctxt_apply finite_Un
    by simp
qed*)

(*global_interpretation "context": grounding where 
  vars = "context.vars :: ('f, 'v) context \<Rightarrow> 'v set" and id_subst = Var and comp_subst = "(\<odot>)" and 
  subst = "(\<cdot>t\<^sub>c)" and from_ground = context.from_ground and to_ground = context.to_ground
proof unfold_locales
  have "\<And>c. context.vars c = {} \<Longrightarrow> \<exists>c\<^sub>G. context.from_ground c\<^sub>G = c"
    by (metis Un_empty_left gctxt_of_ctxt_inv term.ground_exists term.to_ground_inverse 
        term_of_gterm_ctxt_apply_ground(1) vars_term_ctxt_apply)

  then show "{c. context.vars c = {}} = range context.from_ground"
    by force
next 
  show "\<And>c\<^sub>G. context.to_ground (context.from_ground c\<^sub>G) = c\<^sub>G"
    by simp
qed

global_interpretation  
  "context": renaming_variables where vars = context.vars and 
  is_renaming = context.is_renaming and id_subst = Var and subst = "(\<cdot>t\<^sub>c)" +
  "context": variables_imgu where vars = context.vars and base_is_imgu = term_subst.is_imgu and 
  subst = "(\<cdot>t\<^sub>c)" and base_vars = term.vars
proof unfold_locales
  fix c and \<rho> :: "('f, 'v) subst"
  assume "context.is_renaming \<rho>" 
  then have "\<And>t. Var ` term.vars (c\<langle>t\<rangle> \<cdot>t \<rho>) = \<rho> ` term.vars c\<langle>t\<rangle>"
    by (meson term.renaming_variables)
  
  then show "Var ` context.vars (c \<cdot>t\<^sub>c \<rho>) = \<rho> ` context.vars c"
    unfolding vars_term_ctxt_apply subst_apply_term_ctxt_apply_distrib
    by (metis Un_commute Un_empty_left is_ground_trm_iff_ident_forall_subst term.ground_exists)
next
  fix c unifiers and \<mu> :: "('f, 'v) subst"
  assume "finite unifiers" "\<forall>U\<in>unifiers. finite U" "term_subst.is_imgu \<mu> unifiers"
  
  then have "\<And>t. term.vars (c\<langle>t\<rangle> \<cdot>t \<mu>) \<subseteq> term.vars c\<langle>t\<rangle> \<union> \<Union> (term.vars ` \<Union> unifiers)"
    using term.vars_imgu
    by meson

  then show "context.vars (c \<cdot>t\<^sub>c \<mu>) \<subseteq> context.vars c \<union> \<Union> (term.vars ` \<Union> unifiers)"
    unfolding vars_term_ctxt_apply subst_apply_term_ctxt_apply_distrib
    by (metis le_sup_iff sup_bot.right_neutral term.ground_exists)
qed*)

lemma ground_ctxt_iff_context_is_ground: "ground_ctxt c \<longleftrightarrow> context.is_ground c"
  by(induction c)(simp_all add: term_context_ground_iff_term_is_ground)

end
