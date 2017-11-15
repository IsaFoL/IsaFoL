theory AFP_Term imports Main begin

datatype (funs_term : 'f, vars_term : 'v) "term" =
  is_Var: Var (the_Var: 'v) |
  Fun 'f (args : "('f, 'v) term list")
where
  "args (Var _) = []"

text \<open>
  Reorient equations of the form @{term "Var x = t"} and @{term "Fun f ss = t"} to facilitate
  simplification.
\<close>
setup \<open>
  Reorient_Proc.add
    (fn Const (@{const_name Var}, _) $ _ => true | _ => false)
  #> Reorient_Proc.add
    (fn Const (@{const_name Fun}, _) $ _ $ _ => true | _ => false)
\<close>

simproc_setup reorient_Var ("Var x = t") = Reorient_Proc.proc
simproc_setup reorient_Fun ("Fun f ss = t") = Reorient_Proc.proc

lemma finite_vars_term [simp]:
  "finite (vars_term t)"
  by (induct t) simp_all

lemma finite_Union_vars_term:
  "finite (\<Union>t \<in> set ts. vars_term t)"
  by auto

text \<open>
  A \emph{substitution} is a mapping~$\sigma$ from variables to terms. We call a substitution that
  alters the type of variables a \emph{general substitution}, since it does not have all properties
  that are expected of (standard) substitutions (e.g., there is no empty substitution).
\<close>
type_synonym ('f, 'v, 'w) gsubst = "'v \<Rightarrow> ('f, 'w) term"
type_synonym ('f, 'v) subst  = "('f, 'v, 'v) gsubst"

fun subst_apply_term :: "('f, 'v) term \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) term" (infixl "\<cdot>" 67)
where
  "Var x \<cdot> \<sigma> = \<sigma> x" |
  "Fun f ss \<cdot> \<sigma> = Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ss)"

definition
  subst_compose :: "('f, 'u, 'v) gsubst \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'u, 'w) gsubst"
  (infixl "\<circ>\<^sub>s" 75)
where
  "\<sigma> \<circ>\<^sub>s \<tau> = (\<lambda>x. (\<sigma> x) \<cdot> \<tau>)"

lemma subst_subst_compose [simp]:
  "t \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>) = t \<cdot> \<sigma> \<cdot> \<tau>"
by (induct t \<sigma> rule: subst_apply_term.induct) (simp add: subst_compose_def)+

lemma subst_compose_assoc:
  "\<sigma> \<circ>\<^sub>s \<tau> \<circ>\<^sub>s \<mu> = \<sigma> \<circ>\<^sub>s (\<tau> \<circ>\<^sub>s \<mu>)"
proof (rule ext)
  fix x show "(\<sigma> \<circ>\<^sub>s \<tau> \<circ>\<^sub>s \<mu>) x = (\<sigma> \<circ>\<^sub>s (\<tau> \<circ>\<^sub>s \<mu>)) x"
  proof -
    have "(\<sigma> \<circ>\<^sub>s \<tau> \<circ>\<^sub>s \<mu>) x = \<sigma>(x) \<cdot> \<tau> \<cdot> \<mu>" by (simp add: subst_compose_def)
    also have "\<dots> = \<sigma>(x) \<cdot> (\<tau> \<circ>\<^sub>s \<mu>)" by simp
    finally show ?thesis by (simp add: subst_compose_def)
  qed
qed

lemma subst_apply_term_empty [simp]:
  "t \<cdot> Var = t"
proof (induct t)
  case (Fun f ts)
  from map_ext [rule_format, of ts _ id, OF Fun] show ?case by simp
qed simp

interpretation subst_monoid_mult: monoid_mult "Var" "op \<circ>\<^sub>s"
  by (unfold_locales)
     (simp add: subst_compose_assoc, simp_all add: subst_compose_def)

lemma term_subst_eq:
  assumes "\<And>x. x \<in> vars_term t \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "t \<cdot> \<sigma> = t \<cdot> \<tau>"
  using assms by (induct t) (auto)

lemma term_subst_eq_rev:
  "t \<cdot> \<sigma> = t \<cdot> \<tau> \<Longrightarrow> \<forall>x \<in> vars_term t. \<sigma> x = \<tau> x"
proof (induct t)
  case (Fun f ts)
  thus ?case by auto
qed simp

lemma term_subst_eq_conv:
  "(t \<cdot> \<sigma> = t \<cdot> \<tau>) = (\<forall>x \<in> vars_term t. \<sigma> x = \<tau> x)"
  using term_subst_eq [of t \<sigma> \<tau>] term_subst_eq_rev [of t \<sigma> \<tau>] by auto

lemma subst_term_eqI:
  assumes "(\<And>t. t \<cdot> \<sigma> = t \<cdot> \<tau>)"
  shows "\<sigma> = \<tau>"
proof (rule ext)
  fix x
  show "\<sigma> x = \<tau> x" using assms [of "Var x"] by simp
qed

definition subst_domain :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "subst_domain \<sigma> = {x. \<sigma> x \<noteq> Var x}"

definition var_renaming :: "('f, 'v) subst \<Rightarrow> bool" where
  "var_renaming \<sigma> \<longleftrightarrow> (\<forall>x. is_Var (\<sigma> x)) \<and> inj_on \<sigma> (subst_domain \<sigma>)"

end