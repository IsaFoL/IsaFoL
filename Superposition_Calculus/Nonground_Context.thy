theory Nonground_Context
  imports 
    Nonground_Term
    Functional_Substitution_Lifting
begin

section \<open>Nonground Contexts and Substitutions\<close>

lemma finite_set2_actxt: "finite (set2_actxt c)"
  by(induction c) auto

global_interpretation "context": natural_functor where map = map_args_actxt and to_set = set2_actxt
proof unfold_locales
  show "\<And>t. \<exists>c. t \<in> set2_actxt c"
    by (metis actxt.set_intros(5) list.set_intros(1))
qed (auto 
    simp: actxt.set_map(2) actxt.map_comp fun.map_ident actxt.map_ident_strong 
    cong: actxt.map_cong)

global_interpretation "context": natural_functor_conversion 
  where map = map_args_actxt and to_set = set2_actxt and map_to = map_args_actxt 
    and map_from = map_args_actxt and map' = map_args_actxt and to_set' = set2_actxt
  by unfold_locales
    (auto simp: actxt.set_map(2) actxt.map_comp cong: actxt.map_cong)

global_interpretation "context": lifting_from_term where 
    sub_vars = term.vars and sub_subst = "(\<cdot>t)" and to_set = "set2_actxt" and map = map_args_actxt
    and sub_to_ground = term.to_ground and sub_from_ground = term.from_ground 
    and to_ground_map = map_args_actxt and from_ground_map = map_args_actxt 
    and ground_map = map_args_actxt and to_set_ground = set2_actxt
   rewrites 
    "\<And>c. context.vars c = vars_ctxt c" and 
    "\<And>c \<sigma>. context.subst c \<sigma> = c \<cdot>\<^sub>c \<sigma>"
proof -
  interpret lifting_from_term term.vars "(\<cdot>t)" map_args_actxt set2_actxt term.to_ground
    term.from_ground map_args_actxt map_args_actxt map_args_actxt set2_actxt
    by unfold_locales (auto simp: is_ground_iff finite_set2_actxt)

  fix c :: "('a, ('f, 'v) Term.term) actxt"
  show "vars c = vars_ctxt c"
    unfolding vars_def 
    by(induction c) auto

  fix \<sigma> 
  show "subst c \<sigma> = c \<cdot>\<^sub>c \<sigma>"
    unfolding subst_def
    by blast

  show "lifting_from_term term.vars (\<cdot>t) map_args_actxt set2_actxt term.to_ground term.from_ground
     map_args_actxt map_args_actxt map_args_actxt set2_actxt"
    by unfold_locales
qed

lemma ground_ctxt_iff_context_is_ground: "ground_ctxt c \<longleftrightarrow> context.is_ground c"
  by(induction c)(simp_all add: term_context_ground_iff_term_is_ground)

(* TODO: Names *)
lemma ground_term_with_context1:
  assumes "context.is_ground c" "term.is_ground t"
  shows "(context.to_ground c)\<langle>term.to_ground t\<rangle>\<^sub>G = term.to_ground c\<langle>t\<rangle>"
  using assms
  unfolding context.to_ground_def
  by(induction c) simp_all

lemma ground_term_with_context2:
  assumes "context.is_ground c"  
  shows "term.from_ground (context.to_ground c)\<langle>t\<^sub>G\<rangle>\<^sub>G = c\<langle>term.from_ground t\<^sub>G\<rangle>"
  using assms
  unfolding context.to_ground_def
  by(induction c) (simp_all add: context.to_ground_def map_idI)

lemma ground_term_with_context3: 
  "(context.from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<rangle> = term.from_ground c\<^sub>G\<langle>t\<^sub>G\<rangle>\<^sub>G"
  using ground_term_with_context2[OF context.ground_is_ground, symmetric]
  unfolding context.from_ground_inverse.

lemmas ground_term_with_context =
  ground_term_with_context1
  ground_term_with_context2
  ground_term_with_context3

lemma context_is_ground_context_compose1:
  assumes "context.is_ground (c \<circ>\<^sub>c c')"
  shows "context.is_ground c" "context.is_ground c'"
  using assms
  by(induction c) auto

lemma context_is_ground_context_compose2:
  assumes "context.is_ground c" "context.is_ground c'" 
  shows "context.is_ground (c \<circ>\<^sub>c c')"
  using assms
  by (meson ground_ctxt_comp ground_ctxt_iff_context_is_ground)

lemmas context_is_ground_context_compose = 
  context_is_ground_context_compose1 
  context_is_ground_context_compose2

lemma ground_context_subst:
  assumes 
    "context.is_ground c\<^sub>G" 
    "c\<^sub>G = (c \<cdot>t\<^sub>c \<sigma>) \<circ>\<^sub>c c'"
  shows 
    "c\<^sub>G = c \<circ>\<^sub>c c' \<cdot>t\<^sub>c \<sigma>"
  using assms 
proof(induction c)
  case Hole
  then show ?case
    by simp
next
  case More
  then show ?case
    using context_is_ground_context_compose1(2)
    by (metis subst_compose_ctxt_compose_distrib context.subst_ident_if_ground)
qed

lemma context_from_ground_hole: "context.from_ground c\<^sub>G = \<box> \<longleftrightarrow> c\<^sub>G = \<box>"
  by(cases c\<^sub>G) (simp_all add: context.from_ground_def)

lemma term_with_context_is_ground: "term.is_ground c\<langle>t\<rangle> \<longleftrightarrow> context.is_ground c \<and> term.is_ground t"
  by simp

end
