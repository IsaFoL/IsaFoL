theory Nonground_Entailment
  imports 
    Nonground_Clause 
    Term_Rewrite_System
    Entailment_Lifting
begin

section \<open>Entailment\<close>

lemma var_in_term:
  assumes "x \<in> term.vars t"
  obtains c where "t = c\<langle>Var x\<rangle>"
  using assms
proof(induction t)
  case Var
  then show ?case
    by (meson supteq_Var supteq_ctxtE)
next
  case (Fun f args)
  then obtain t' where "t' \<in> set args " "x \<in> term.vars t'"
    by (metis term.distinct(1) term.sel(4) term.set_cases(2))

  moreover then obtain args1 args2 where
    "args1 @ [t'] @ args2 = args"
    by (metis append_Cons append_Nil split_list)

  moreover then have "(More f args1 \<box> args2)\<langle>t'\<rangle> = Fun f args"
    by simp

  ultimately show ?case 
    using Fun(1)
    by (meson assms supteq_ctxtE that vars_term_supteq)
qed

lemma vars_term_ms_count:
  assumes "term.is_ground t"
  shows 
    "size {#x' \<in># vars_term_ms c\<langle>Var x\<rangle>. x' = x#} = Suc (size {#x' \<in># vars_term_ms c\<langle>t\<rangle>. x' = x#})"
  by(induction c)(auto simp: assms filter_mset_empty_conv)

locale clause_entailment =
  fixes I :: "('f gterm \<times> 'f gterm) set"
  assumes 
    trans: "trans I" and
    sym: "sym I" and
    compatible_with_gctxt: "compatible_with_gctxt I"
begin

lemma symmetric_context_congruence:
  assumes "(t, t') \<in> I"
  shows "(c\<langle>t\<rangle>\<^sub>G, t'') \<in> I \<longleftrightarrow> (c\<langle>t'\<rangle>\<^sub>G, t'') \<in> I"
  by (meson assms compatible_with_gctxt compatible_with_gctxtD sym trans symD transE)

sublocale "term": symmetric_base_entailment where vars = "term.vars :: ('f, 'v) term \<Rightarrow> 'v set" and 
  id_subst = Var and comp_subst = "(\<odot>)" and subst = "(\<cdot>t)" and to_ground = term.to_ground and 
  from_ground = term.from_ground
proof unfold_locales
  fix \<gamma> :: "('f, 'v) subst" and t t' update var

  assume 
    update_is_ground: "term.is_ground update" and
    var_grounding: "term.is_ground (\<gamma> var)" and
    var_update: "(term.to_ground (\<gamma> var), term.to_ground update) \<in> I" and
    term_grounding: "term.is_ground (t \<cdot>t \<gamma>)" and
    updated_term: "(term.to_ground (t \<cdot>t \<gamma>(var := update)), t') \<in> I"

  from term_grounding updated_term
  show "(term.to_ground (t \<cdot>t \<gamma>), t') \<in> I"
  proof(induction "size (filter_mset (\<lambda>var'. var' = var) (vars_term_ms t))" arbitrary: t)
    case 0

    then have "var \<notin> term.vars t"
      by (metis (mono_tags, lifting) filter_mset_empty_conv set_mset_vars_term_ms 
          size_eq_0_iff_empty)

    then have "t \<cdot>t \<gamma>(var := update) = t \<cdot>t \<gamma>"
      using term.subst_reduntant_upd 
      by (simp add: eval_with_fresh_var)

    with 0 show ?case
      by argo
  next
    case (Suc n)

    let ?context_to_ground = "map_args_actxt term.to_ground"

    have "var \<in> term.vars t"
      using Suc.hyps(2)
      by (metis (full_types) filter_mset_empty_conv nonempty_has_size set_mset_vars_term_ms 
          zero_less_Suc)

    then obtain c where t [simp]: "t = c\<langle>Var var\<rangle>"
      by (meson var_in_term)

    have [simp]: 
      "(?context_to_ground (c \<cdot>t\<^sub>c \<gamma>))\<langle>term.to_ground (\<gamma> var)\<rangle>\<^sub>G = term.to_ground (c\<langle>Var var\<rangle> \<cdot>t \<gamma>)"
      using Suc 
      by(induction c) simp_all

    have context_update [simp]: 
      "(?context_to_ground (c \<cdot>t\<^sub>c \<gamma>))\<langle>term.to_ground update\<rangle>\<^sub>G = term.to_ground (c\<langle>update\<rangle> \<cdot>t \<gamma>)"
      using Suc update_is_ground
      by(induction c) auto

    have "n = size {#var' \<in># vars_term_ms c\<langle>update\<rangle>. var' = var#}"
      using Suc vars_term_ms_count[OF update_is_ground, of var c]
      by auto

    moreover have "term.is_ground (c\<langle>update\<rangle> \<cdot>t \<gamma>)"
      using Suc.prems update_is_ground 
      by auto

    moreover have "(term.to_ground (c\<langle>update\<rangle> \<cdot>t \<gamma>(var := update)), t') \<in> I"
      using Suc.prems update_is_ground
      by auto

    moreover have "(term.to_ground update, term.to_ground (\<gamma> var)) \<in> I"
      using var_update sym
      by (metis symD)

    moreover have "(term.to_ground (c\<langle>update\<rangle> \<cdot>t \<gamma>), t') \<in> I"
      using Suc calculation
      by blast

    ultimately have "((?context_to_ground (c \<cdot>t\<^sub>c \<gamma>))\<langle>term.to_ground (\<gamma> var)\<rangle>\<^sub>G, t') \<in> I"
      using symmetric_context_congruence context_update
      by metis

    then show ?case 
      by simp
  qed
qed (rule sym)

sublocale atom: symmetric_entailment 
  where comp_subst = "(\<odot>)" and id_subst = Var 
    and base_subst = "(\<cdot>t)" and base_vars = term.vars and subst = "(\<cdot>a)" and vars = atom.vars
    and base_to_ground = term.to_ground and base_from_ground = term.from_ground and I = I 
    and entails_def = "\<lambda>a. atom.to_ground a \<in> upair ` I"
proof unfold_locales  
  fix a :: "('f, 'v) atom" and  \<gamma> var update P

  assume assms: 
    "term.is_ground update"
    "term.is_ground (\<gamma> var)" 
    "(term.to_ground (\<gamma> var), term.to_ground update) \<in> I"
    "atom.is_ground (a \<cdot>a \<gamma>)"
    "(atom.to_ground (a \<cdot>a \<gamma>(var := update)) \<in> upair ` I)"

  show "(atom.to_ground (a \<cdot>a \<gamma>) \<in> upair ` I)"
  proof(cases a)
    case (Upair t t')

    moreover have 
      "(term.to_ground (t' \<cdot>t \<gamma>), term.to_ground (t \<cdot>t \<gamma>)) \<in> I \<longleftrightarrow> 
       (term.to_ground (t \<cdot>t \<gamma>), term.to_ground (t' \<cdot>t \<gamma>)) \<in> I"
      by (metis local.sym symD)

    ultimately show ?thesis
      using assms
      unfolding atom.to_ground_def atom.subst_def atom.vars_def
      by(auto simp: sym term.simultaneous_congruence)
  qed
qed (simp_all add: sym)

sublocale literal: entailment_lifting_conj
  where comp_subst = "(\<odot>)" and id_subst = Var 
    and base_subst = "(\<cdot>t)" and base_vars = term.vars and sub_subst = "(\<cdot>a)" and sub_vars = atom.vars
    and base_to_ground = term.to_ground and base_from_ground = term.from_ground and I = I 
    and sub_entails = atom.entails and map = "map_literal" and to_set = "set_literal" 
    and is_negated = is_neg and entails_def = "\<lambda>l. upair ` I \<TTurnstile>l literal.to_ground l"
proof unfold_locales 
  fix l :: "('f, 'v) atom literal" 

  show "(upair ` I \<TTurnstile>l literal.to_ground l) = 
    (if is_neg l then Not else (\<lambda>x. x))
      (Finite_Set.fold (\<and>) True ((\<lambda>a. atom.to_ground a \<in> upair ` I) ` set_literal l))" 
    unfolding literal.vars_def literal.to_ground_def
    by(cases l)(auto)

qed (auto simp: subst_polarity_stable)

sublocale clause: entailment_lifting_disj
  where comp_subst = "(\<odot>)" and id_subst = Var 
    and base_subst = "(\<cdot>t)" and base_vars = term.vars 
    and base_to_ground = term.to_ground and base_from_ground = term.from_ground and I = I
    and sub_subst = "(\<cdot>l)" and sub_vars = literal.vars and sub_entails = literal.entails 
    and map = image_mset and to_set = set_mset and is_negated = "\<lambda>_. False" 
    and entails_def = "\<lambda>C. upair ` I \<TTurnstile> clause.to_ground C"
proof unfold_locales 
  fix C :: "('f, 'v) atom clause" 

  show "(upair ` I \<TTurnstile> clause.to_ground C) = 
    (if False then Not else (\<lambda>x. x)) (Finite_Set.fold (\<or>) False (literal.entails ` set_mset C))"
    unfolding clause.to_ground_def
    by(induction C) auto

qed auto

end

end
