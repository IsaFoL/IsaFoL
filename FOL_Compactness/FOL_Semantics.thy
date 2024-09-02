(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023 *)

theory FOL_Semantics
  imports
    Main FOL_Syntax
begin

locale struct =
  fixes
    M :: \<open>'m set\<close> and
    FN :: \<open>nat \<Rightarrow> 'm list \<Rightarrow> 'm\<close> and
    REL :: \<open>nat \<Rightarrow> 'm list set\<close> (* in hol-ligh a boolean is returned instead *)
  assumes
    M_nonempty: \<open>M \<noteq> {}\<close>

typedef 'm intrp =
  \<open>{ (M :: 'm set, FN :: nat \<Rightarrow> 'm list \<Rightarrow> 'm, REL :: nat \<Rightarrow> 'm list set). struct M}\<close>
  using struct.intro
  by fastforce

setup_lifting type_definition_intrp

lift_definition dom :: \<open>'m intrp \<Rightarrow> 'm set\<close> is fst .
lift_definition intrp_fn :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm list \<Rightarrow> 'm)\<close> is \<open>fst \<circ> snd\<close> .
lift_definition intrp_rel :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm list set)\<close> is \<open>snd \<circ> snd\<close> .

lemma intrp_is_struct: \<open>struct (dom \<M>)\<close>
  by transfer auto 

lemma dom_Abs_is_fst [simp]: \<open>struct M \<Longrightarrow> dom (Abs_intrp (M, FN, REL)) = M\<close>
  by (simp add: Abs_intrp_inverse dom.rep_eq) 

lemma intrp_fn_Abs_is_fst_snd [simp]: \<open>struct M \<Longrightarrow> intrp_fn (Abs_intrp (M, FN, REL)) = FN\<close>
  by (simp add: Abs_intrp_inverse intrp_fn.rep_eq) 

lemma intrp_rel_Abs_is_snd_snd [simp]: 
  \<open>struct M \<Longrightarrow> intrp_rel (Abs_intrp (M, FN, REL)) = REL\<close>
  by (simp add: Abs_intrp_inverse intrp_rel.rep_eq) 

(* in hol-ligh: valuation *)
definition is_valuation :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> bool\<close> where
  [simp]: \<open>is_valuation \<M> \<beta> \<longleftrightarrow> (\<forall> v. \<beta> v \<in> dom \<M>)\<close> 

lemma valuation_valmod: \<open>is_valuation \<M> \<beta> \<and> a \<in> dom \<M> \<Longrightarrow> is_valuation \<M> (\<beta>(x := a))\<close>
  by simp

fun eval (* HOL-Light: termval *)
  :: \<open>nterm \<Rightarrow> 'm intrp \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> 'm\<close>
  (\<open>\<lbrakk>_\<rbrakk>\<^bsup>_,_\<^esup>\<close> [50, 0, 0] 70) where
  \<open>\<lbrakk>Var v\<rbrakk>\<^bsup>_,\<beta>\<^esup> = \<beta> v\<close>
| \<open>\<lbrakk>Fun f ts\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = intrp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts]\<close> 

definition list_all :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  [simp]: \<open>list_all P ls \<longleftrightarrow> (fold (\<lambda>l b. b \<and> P l) ls True)\<close>

lemma fold_bool_prop: \<open>(fold (\<lambda>l b. b \<and> P l) ls b) = (b \<and> (\<forall>l\<in>set ls. P l))\<close>
  by (induction ls arbitrary: b) auto

lemma list_all_set: \<open>list_all P ls = (\<forall>l\<in>set ls. P l)\<close>
  unfolding list_all_def using fold_bool_prop by auto

definition is_interpretation where
  \<open>is_interpretation lang \<M> \<longleftrightarrow> 
    ((\<forall>f l. (f, length(l)) \<in> fst lang \<and> list_all (\<lambda>x. x \<in> dom \<M>) l \<longrightarrow> intrp_fn \<M> f l \<in> dom \<M>))\<close>

lemma interpretation_sublanguage: \<open>funs2 \<subseteq> funs1 \<Longrightarrow> is_interpretation (funs1, pred1) \<M>
  \<Longrightarrow> is_interpretation (funs2, preds2) \<M>\<close>
  unfolding is_interpretation_def by auto

(* Notation Warning: To prevent ambiguity with tuples, the comma is *bold* *)
fun holds
  :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> form \<Rightarrow> bool\<close> (\<open>_\<^bold>,_ \<Turnstile> _\<close> [50, 50, 80] 80) where
  \<open>\<M>\<^bold>,\<beta> \<Turnstile> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>\<M>\<^bold>,\<beta> \<Turnstile> Atom p ts \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> intrp_rel \<M> p\<close>
| \<open>\<M>\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi> \<longleftrightarrow> ((\<M>\<^bold>,\<beta> \<Turnstile> \<phi>) \<longrightarrow> (\<M>\<^bold>,\<beta> \<Turnstile> \<psi>))\<close>
| \<open>\<M>\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<longleftrightarrow> (\<forall>a \<in> dom \<M>. \<M>\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>)\<close>

lemma holds_exists: \<open>\<M>\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>) \<longleftrightarrow> (\<exists>a \<in> dom \<M>. \<M>\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>)\<close>
  by simp

lemma holds_indep_\<beta>_if:
  \<open>\<forall> v \<in> FV \<phi>. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v \<Longrightarrow> \<M>\<^bold>,\<beta>\<^sub>1 \<Turnstile> \<phi> \<longleftrightarrow> \<M>\<^bold>,\<beta>\<^sub>2 \<Turnstile> \<phi>\<close>
proof (induction \<phi> arbitrary: \<beta>\<^sub>1 \<beta>\<^sub>2)
  case Bot
  then show ?case
    by simp
next
  case (Atom p ts)
  then have \<open>\<forall> t \<in> set ts. \<forall> v \<in> FVT t. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v\<close>
    by simp 
  then have \<open>[\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>1\<^esup>. t \<leftarrow> ts] = [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>2\<^esup>. t \<leftarrow> ts]\<close>
  proof (induction ts) 
    case Nil
    then show ?case
      by simp
  next
    case (Cons a ts)
    then show ?case
    proof (induction a)
      case (Var x)
      then show ?case
        by simp 
    next
      case (Fun f ts')
      then have \<open>\<forall> t \<in> set ts'. \<forall> v \<in> FVT t. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v\<close>
        by simp 
      then have \<open>[\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>1\<^esup>. t \<leftarrow> ts'] = [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>2\<^esup>. t \<leftarrow> ts']\<close>
        using Cons.IH Fun.IH Fun.prems(2)
        by force
      then have \<open>intrp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>1\<^esup>. t \<leftarrow> ts'] = intrp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>2\<^esup>. t \<leftarrow> ts']\<close>
        by argo 
      then show ?case
        using Cons.IH Fun.prems(2)
        by force 
    qed
  qed
  then have \<open>[\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>1\<^esup>. t \<leftarrow> ts] \<in> intrp_rel \<M> p \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>2\<^esup>. t \<leftarrow> ts] \<in> intrp_rel \<M> p\<close>
    by argo
  then show ?case
    by simp
next
  case (Implies \<phi> \<psi>)
  then have
    \<open>\<forall>v \<in> FV \<phi>. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v\<close> and
    \<open>\<forall>v \<in> FV \<psi>. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v\<close>
    by auto
  then have
    \<open>\<M>\<^bold>,\<beta>\<^sub>1 \<Turnstile> \<phi> \<longleftrightarrow> \<M>\<^bold>,\<beta>\<^sub>2 \<Turnstile> \<phi>\<close> and
    \<open>\<M>\<^bold>,\<beta>\<^sub>1 \<Turnstile> \<psi> \<longleftrightarrow> \<M>\<^bold>,\<beta>\<^sub>2 \<Turnstile> \<psi>\<close>
    using Implies.IH by auto
  then show ?case
    by simp
next
  case (Forall x \<phi>)
  then have \<open>\<forall>a \<in> dom \<M>. (\<M>\<^bold>,\<beta>\<^sub>1(x := a) \<Turnstile> \<phi>) = (\<M>\<^bold>,\<beta>\<^sub>2(x := a) \<Turnstile> \<phi>)\<close>
    by simp
  then show ?case 
    by simp
qed

lemma holds_indep_intrp_if:
  fixes
    \<phi> :: form and
    \<M> \<M>' :: \<open>'m intrp\<close> 
  assumes
    dom_eq: \<open>dom \<M> = dom \<M>'\<close> and
    rel_eq: \<open>\<forall> p. intrp_rel \<M> p = intrp_rel \<M>' p\<close> and
    fn_eq: \<open>\<forall> f ts. (f, length ts) \<in> functions_form \<phi> \<longrightarrow> intrp_fn \<M> f ts = intrp_fn \<M>' f ts\<close>
  shows
    \<open>\<forall>\<beta>.  \<M>\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> \<M>'\<^bold>,\<beta> \<Turnstile> \<phi>\<close>
  using fn_eq
proof (intro allI impI, induction \<phi>)
  case (Atom p ts)

  have all_fn_sym_in: \<open>(\<Union> t \<in> set ts. functions_term t) \<subseteq> functions_form (Atom p ts)\<close> (is \<open>?A \<subseteq> _\<close>)
    by simp 

  have eval_tm_eq: \<open>\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>t\<rbrakk>\<^bsup>\<M>',\<beta>\<^esup>\<close>
    if \<open>functions_term t \<subseteq> functions_form (Atom p ts)\<close> 
    for t 
    using that
  proof (induction t) 
    case (Fun f ts') 

    have \<open>\<forall> t' \<in> set ts'. functions_term t' \<subseteq> functions_form (Atom p ts)\<close>
      using Fun.prems
      by auto
    moreover have \<open>(f, length [\<lbrakk>t'\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t' \<leftarrow> ts']) \<in> functions_form (Atom p ts)\<close>
      using Fun.prems
      by fastforce 
    ultimately show ?case
      using Fun.IH Atom.prems(1)[rule_format, of f \<open>[\<lbrakk>t'\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t' \<leftarrow> ts']\<close>] 
      by (smt (verit, del_insts) eval.simps(2) map_eq_conv)
  qed auto 

  have \<open>\<M>\<^bold>,\<beta> \<Turnstile> Atom p ts \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> intrp_rel \<M> p\<close>
    by simp
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> intrp_rel \<M>' p\<close>
    by (simp add: rel_eq)
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>',\<beta>\<^esup>. t \<leftarrow> ts] \<in> intrp_rel \<M>' p\<close>
    using eval_tm_eq all_fn_sym_in
    by (metis (mono_tags, lifting) UN_subset_iff map_eq_conv)
  also have \<open>... \<longleftrightarrow> \<M>'\<^bold>,\<beta> \<Turnstile> Atom p ts\<close>
    by auto 
  finally show ?case .
next
  case (Forall x \<phi>)

  have \<open>\<M>\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall> x\<^bold>. \<phi>) \<longleftrightarrow> (\<forall> a \<in> dom \<M>. \<M>\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>)\<close>
    by simp 
  also have \<open>... = (\<forall> a \<in> dom \<M>. \<M>'\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>)\<close>
    using Forall.IH Forall.prems by simp
  also have \<open>... = (\<forall> a \<in> dom \<M>'. \<M>'\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>)\<close>
    by (simp add: dom_eq)
  also have \<open>... = (\<M>'\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall> x\<^bold>. \<phi>))\<close>
    by auto 
  finally show ?case . 
qed auto

abbreviation (input) \<open>eval_subst \<M> \<beta> \<sigma> v \<equiv> \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>\<close>

(* HOL-Light: termval_termsubst *)
lemma subst_lemma_terms: \<open>\<lbrakk>t \<cdot> \<sigma>\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>t\<rbrakk>\<^bsup>\<M>,eval_subst \<M> \<beta> \<sigma>\<^esup>\<close>
proof (induction t)
  case (Var v)
  then show ?case
    by auto 
next
  case (Fun f ts)

  have \<open>\<lbrakk>Fun f ts \<cdot> \<sigma>\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>Fun f [t \<cdot> \<sigma>. t \<leftarrow> ts]\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>\<close>
    by auto
  also have \<open>... = intrp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> [t \<cdot> \<sigma>. t \<leftarrow> ts]]\<close>
    by auto 
  also have \<open>... = intrp_fn \<M> f [\<lbrakk>t \<cdot> \<sigma>\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts]\<close>
    unfolding map_map
    by (meson comp_apply)
  also have \<open>... = intrp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,eval_subst \<M> \<beta> \<sigma>\<^esup>. t \<leftarrow> ts]\<close>
    using Fun.IH
    by (smt (verit, best) map_eq_conv) 
  also have \<open>... = \<lbrakk>Fun f ts\<rbrakk>\<^bsup>\<M>,eval_subst \<M> \<beta> \<sigma>\<^esup>\<close>
    by auto 
  finally show ?case .
qed

lemma eval_indep_\<beta>_if:
  assumes \<open>\<forall> v \<in> FVT t. \<beta> v = \<beta>' v\<close>
  shows \<open>\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>'\<^esup>\<close>
    using assms
proof (induction t)
  case (Var v)
  then show ?case
    by auto 
next
  case (Fun f ts)
  then show ?case
    by (smt (verit, ccfv_SIG) eval.simps(2) map_eq_conv term.set_intros(4)) 
qed

lemma concat_map: \<open>[f t. t \<leftarrow> [g t. t \<leftarrow> ts]] = [f (g t). t \<leftarrow> ts]\<close> by simp

(* more general than hol-light: holds_formsubst1 holds_rename *)
lemma swap_subst_eval: \<open>\<M>\<^bold>,\<beta> \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<longleftrightarrow> \<M>\<^bold>,(\<lambda>v. eval_subst \<M> \<beta> \<sigma> v) \<Turnstile> \<phi>\<close>
proof (induction \<phi> arbitrary: \<sigma> \<beta>)
  case (Atom p ts)
  have \<open>\<M>\<^bold>,\<beta> \<Turnstile> (Atom p ts \<cdot>\<^sub>f\<^sub>m \<sigma>) \<longleftrightarrow> \<M>\<^bold>,\<beta> \<Turnstile> (Atom p [t \<cdot> \<sigma>. t \<leftarrow> ts])\<close>
    by auto
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> [t \<cdot> \<sigma>. t \<leftarrow> ts]] \<in> intrp_rel \<M> p\<close>
    by auto
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t \<cdot> \<sigma>\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> intrp_rel \<M> p\<close>
    using concat_map[of "\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>" "\<lambda>t. t \<cdot> \<sigma>"] by presburger
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,eval_subst \<M> \<beta> \<sigma>\<^esup>. t \<leftarrow> ts] \<in> intrp_rel \<M> p\<close>
    using subst_lemma_terms[of _ \<sigma> \<M> \<beta>] by auto
  finally show ?case
    by simp
next
  case (Forall x \<phi>)
  define \<sigma>' where "\<sigma>' = \<sigma>(x := Var x)"
  show ?case
  proof (cases "\<exists> y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y)")
    case False
    then have \<open>(\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall>x\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')\<close>
      using formsubst_def_switch \<sigma>'_def by fastforce
    then have \<open>\<M>\<^bold>,\<beta> \<Turnstile> ((\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = (\<forall>a \<in> dom \<M>. \<M>\<^bold>,\<beta>(x := a) \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'))\<close>
      by auto
    also have \<open>... = (\<forall>a \<in> dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) \<Turnstile> \<phi>)\<close>
      using Forall by blast
    also have \<open>... = (\<forall>a \<in> dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>)\<close>
    proof
      assume forward: \<open>\<forall>a \<in> dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) \<Turnstile> \<phi>\<close>
      show \<open>\<forall>a \<in> dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
      proof
        fix a
        assume \<open>a \<in> dom \<M>\<close>
        then have \<open>\<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) \<Turnstile> \<phi>\<close>
          using forward by blast
        moreover have \<open>\<forall>v\<in>FV \<phi>. (\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
        proof
          fix v
          assume \<open>v \<in> FV \<phi>\<close>
          then have \<open>v \<noteq> x \<Longrightarrow> \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by (metis (mono_tags, lifting) DiffI FV.simps(4) False eval_indep_\<beta>_if fun_upd_other singletonD)
          moreover have \<open>v = x \<Longrightarrow> \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            using \<sigma>'_def by auto
          ultimately show \<open>\<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by simp
        qed
        ultimately show \<open>\<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
          using holds_indep_\<beta>_if by fast
      qed
    next
      assume backward: \<open>\<forall>a \<in> dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
      show \<open>\<forall>a \<in> dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) \<Turnstile> \<phi>\<close>
      proof
        fix a
        assume \<open>a \<in> dom \<M>\<close>
        then have \<open>\<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
          using backward by blast
        moreover have \<open>\<forall>v\<in>FV \<phi>. (\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
        proof
          fix v
          assume \<open>v \<in> FV \<phi>\<close>
          then have \<open>v \<noteq> x \<Longrightarrow> \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by (metis (mono_tags, lifting) DiffI FV.simps(4) False eval_indep_\<beta>_if fun_upd_other singletonD)
          moreover have \<open>v = x \<Longrightarrow> \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            using \<sigma>'_def by auto
          ultimately show \<open>\<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by simp
        qed
        ultimately show \<open>\<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) \<Turnstile> \<phi>\<close>
          using holds_indep_\<beta>_if by fast
      qed
    qed
    also have \<open>... = (\<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>) \<Turnstile> (\<^bold>\<forall> x\<^bold>. \<phi>))\<close>
      by (smt (verit, ccfv_SIG) \<sigma>'_def fun_upd_apply holds.simps(4) holds_indep_\<beta>_if)
    finally show ?thesis .
  next
    case True
    then have x_ex: \<open>\<exists>y. y \<in> FV \<phi> - {x} \<and> x \<in> FVT (\<sigma>' y)\<close>
      by simp
    then have x_in: \<open>x \<in> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')\<close>
      using formsubst_fv
      by auto
    define z where \<open>z = variant (FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'))\<close>
    then have \<open>z \<noteq> x\<close>
      using x_in variant_form by auto
    have \<open>(\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> =  \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z))\<close>
      using z_def True formsubst_def_switch \<sigma>'_def by (smt (verit, best) formsubst.simps(4))
    then have \<open>\<M>\<^bold>,\<beta> \<Turnstile> ((\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = (\<forall>a \<in> dom \<M>. \<M>\<^bold>,\<beta>(z := a) \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z)))\<close>
      by auto
    also have \<open>... = (\<forall>a \<in> dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>)\<close>
      using Forall by blast
    also have \<open>... = (\<forall>a \<in> dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>)\<close>
    proof
      assume forward: \<open>\<forall>a\<in>dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>\<close>
      show \<open>\<forall>a\<in>dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
      proof
        fix a
        assume \<open>a \<in> dom \<M>\<close>
        then have \<open>\<M>\<^bold>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>\<close>
          using forward by blast
        moreover have \<open>\<forall>v\<in>FV \<phi>. (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = 
          ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
        proof
          fix v
          assume v_in: \<open>v \<in> FV \<phi>\<close>
          then have \<open>v \<noteq> x \<Longrightarrow> z \<notin> FVT (\<sigma> v)\<close>
            using z_def variant_form by (smt (verit, ccfv_threshold) \<sigma>'_def eval_term.simps(1) 
              formsubst_fv fun_upd_other mem_Collect_eq)
          then have \<open>v \<noteq> x \<Longrightarrow> \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup> = \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>\<close>
            by (simp add: eval_indep_\<beta>_if)
          then have \<open>v \<noteq> x \<Longrightarrow>
            (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by auto
          moreover have \<open>v = x \<Longrightarrow>
            (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by auto
          ultimately show 
            \<open>\<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup> = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by auto
        qed
        ultimately show \<open>\<M>\<^bold>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
          using holds_indep_\<beta>_if by fast
      qed
    next
      assume backward: \<open>\<forall>a\<in>dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
      show \<open>\<forall>a\<in>dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>\<close>
      proof
        fix a
        assume \<open>a \<in> dom \<M>\<close>
        then have \<open>\<M>\<^bold>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
          using backward by auto
        moreover have \<open>\<forall>v\<in>FV \<phi>. (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = 
          ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
        proof
          fix v
          assume v_in: \<open>v \<in> FV \<phi>\<close>
          then have \<open>v \<noteq> x \<Longrightarrow> z \<notin> FVT (\<sigma> v)\<close>
            using z_def variant_form by (smt (verit, ccfv_threshold) \<sigma>'_def eval_term.simps(1) 
              formsubst_fv fun_upd_other mem_Collect_eq)
          then have \<open>v \<noteq> x \<Longrightarrow> \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup> = \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>\<close>
            by (simp add: eval_indep_\<beta>_if)
          then have \<open>v \<noteq> x \<Longrightarrow>
            (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by auto
          moreover have \<open>v = x \<Longrightarrow>
            (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by auto
          ultimately show 
            \<open>\<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup> = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by auto
        qed
        ultimately show \<open>\<M>\<^bold>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>\<close>
          using holds_indep_\<beta>_if by fast
      qed
    qed
    also have \<open>... = (\<forall>a \<in> dom \<M>. \<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>)\<close>
      by (smt (verit, ccfv_SIG) fun_upd_apply holds_indep_\<beta>_if)
    also have \<open>... = (\<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>) \<Turnstile> (\<^bold>\<forall> x\<^bold>. \<phi>))\<close>
      by auto
    finally show ?thesis .
  qed
qed auto

definition satisfies :: "'m intrp \<Rightarrow> form set \<Rightarrow> bool" where
  \<open>satisfies \<M> S \<equiv> (\<forall>\<beta> \<phi>. is_valuation \<M> \<beta> \<and> \<phi> \<in> S \<longrightarrow> \<M>\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>


end