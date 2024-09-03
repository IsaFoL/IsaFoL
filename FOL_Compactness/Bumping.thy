(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2024 *)

theory Bumping
  imports FOL_Semantics Naturals_Injection
begin

(* bumpmod in hol-light *)
definition bump_intrp :: "'m intrp \<Rightarrow> 'm intrp" where
  \<open>bump_intrp \<M> = Abs_intrp ((dom \<M>), (\<lambda>k zs. (intrp_fn \<M>) (numsnd k) zs), (intrp_rel \<M>))\<close>

lemma bump_dom [simp]: \<open>dom (bump_intrp \<M>) = dom \<M>\<close>
proof -
  have is_struct: \<open>struct (dom \<M>)\<close> (*(\<lambda>k zs. (intrp_fn \<M>) (numsnd k) zs) (intrp_rel \<M>)\<close> *)
    by (simp add: intrp_is_struct)
  then show ?thesis unfolding bump_intrp_def using dom_Abs_is_fst by blast
qed

lemma bump_intrp_fn [simp]: \<open>intrp_fn (bump_intrp \<M>) (numpair 0 f) ts = intrp_fn \<M> f ts\<close>
proof -
  have is_struct: \<open>struct (dom \<M>)\<close> (* (\<lambda>k zs. (intrp_fn \<M>) (numsnd k) zs) (intrp_rel \<M>)\<close> *)
    by (smt (verit, best) intrp_is_struct struct_def)
  then show ?thesis unfolding bump_intrp_def by simp
qed

lemma bump_intrp_rel [simp]: \<open>intrp_rel (bump_intrp \<M>) n = intrp_rel \<M> n\<close>
  unfolding bump_intrp_def
  by (smt (verit) intrp_is_struct intrp_rel_Abs_is_snd_snd struct_def)

(* bumpterm in hol-light *)
fun bump_nterm :: "nterm \<Rightarrow> nterm" where
  \<open>bump_nterm (Var x) = Var x\<close>
| \<open>bump_nterm (Fun f ts) = Fun (numpair 0 f) (map bump_nterm ts)\<close>

(* bumpform in hol-light *)
fun bump_form :: "form \<Rightarrow> form" where
  \<open>bump_form \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>bump_form (Atom p ts) = Atom p (map bump_nterm ts)\<close>
| \<open>bump_form (\<phi> \<^bold>\<longrightarrow> \<psi>) = (bump_form \<phi>) \<^bold>\<longrightarrow> (bump_form \<psi>)\<close>
| \<open>bump_form (\<^bold>\<forall> x\<^bold>. \<phi>) = \<^bold>\<forall> x\<^bold>. (bump_form \<phi>)\<close>


find_theorems "_::nterm" name: induct

lemma bumpterm: \<open>\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>bump_nterm t\<rbrakk>\<^bsup>bump_intrp \<M>,\<beta>\<^esup>\<close>
proof (induct t)
  case (Var x)
  then show ?case
    by simp
next
  case (Fun f ts)
  then have \<open>intrp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] =
    intrp_fn \<M> f [\<lbrakk>bump_nterm t\<rbrakk>\<^bsup>bump_intrp \<M>,\<beta>\<^esup>. t \<leftarrow> ts]\<close>
    by (metis (no_types, lifting) map_eq_conv)
  also have \<open>... = 
    intrp_fn (bump_intrp \<M>) (numpair 0 f) [\<lbrakk>bump_nterm t\<rbrakk>\<^bsup>bump_intrp \<M>,\<beta>\<^esup>. t \<leftarrow> ts]\<close>
    by (simp add: bump_intrp_fn)
  also have \<open>... = 
    intrp_fn (bump_intrp \<M>) (numpair 0 f) [\<lbrakk>t\<rbrakk>\<^bsup>bump_intrp \<M>,\<beta>\<^esup>. t \<leftarrow> (map bump_nterm ts)]\<close>
    using map_eq_conv by fastforce
  ultimately show ?case by auto
qed

lemma bump_intrp_rel_holds: \<open>(map (\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>) ts \<in> intrp_rel \<M> n) =
  (map ((\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>bump_intrp \<M>,\<beta>\<^esup>) \<circ> bump_nterm) ts \<in> intrp_rel (bump_intrp \<M>) n)\<close>
proof -
  have \<open>(\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>) = (\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>bump_intrp \<M>,\<beta>\<^esup>) \<circ> bump_nterm\<close>
    using bumpterm by fastforce
  then have \<open>map (\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>) ts = map ((\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>bump_intrp \<M>,\<beta>\<^esup>) \<circ> bump_nterm) ts\<close>
    by simp
  then show ?thesis
    by (metis bump_intrp_rel)
qed

lemma bumpform: \<open>\<M>\<^bold>, \<beta> \<Turnstile> \<phi> = (bump_intrp \<M>)\<^bold>, \<beta> \<Turnstile> (bump_form \<phi>)\<close>
proof (induct \<phi> arbitrary: \<beta>)
  case Bot
  then show ?case
    unfolding bump_intrp_def by auto
next
  case (Atom x1 x2)
  then show ?case
    using bump_intrp_rel_holds by auto
next
  case (Implies \<phi>1 \<phi>2)
  then show ?case
    unfolding bump_intrp_def by auto
next
  case (Forall x1 \<phi>)
  have \<open>(\<forall>a \<in> dom \<M>. (bump_intrp \<M>)\<^bold>,\<beta>(x1 := a) \<Turnstile> bump_form \<phi>) = 
    (\<forall>a \<in> dom \<M>. \<M>\<^bold>,\<beta>(x1 := a) \<Turnstile> \<phi>)\<close>
    using Forall by presburger
  then show ?case
    by simp
qed

lemma functions_form_bumpform: \<open>(f, m) \<in> functions_form (bump_form \<phi>) \<Longrightarrow>
  \<exists>k. (f = numpair 0 k) \<and> (k, m) \<in> functions_form \<phi>\<close>
proof (induct \<phi>)
  case (Atom p ts)
  then have \<open>\<exists>t\<in>set ts. (f, m) \<in> functions_term (bump_nterm t)\<close> by simp
  then obtain t where t_in: \<open>t \<in> set ts\<close> and fm_in_t: \<open>(f, m) \<in> functions_term (bump_nterm t)\<close>
      by blast
  have \<open>\<exists>k. f = numpair 0 k \<and> (k, m) \<in> functions_term t\<close>
    using fm_in_t
  proof (induction t)
    case (Var x)
    then show ?case by auto
  next
    case (Fun g us)
    find_theorems bump_nterm
    have t_in_disj: \<open>functions_term (bump_nterm (Fun g us)) = 
      {((numpair 0 g), length us)} \<union> (\<Union> u \<in> set us. functions_term (bump_nterm u))\<close>
      by simp
    then show ?case
    proof (cases "(f, m) = ((numpair 0 g), length us)")
      case True
      then show ?thesis by auto
    next
      case False
      then have \<open>(f, m) \<in> (\<Union> u \<in> set us. functions_term (bump_nterm u))\<close>
        using t_in_disj
        using Fun.prems by blast
      then show ?thesis
        using Fun(1) by fastforce
    qed
  qed
  then have \<open>\<exists>k. f = numpair 0 k \<and> (\<exists>x\<in>set ts. (k, m) \<in> functions_term x)\<close>
    using t_in by blast
  then show ?case using Atom by simp
qed auto

lemma bumpform_interpretation: \<open>is_interpretation (language {\<phi>}) \<M> \<Longrightarrow>
  is_interpretation (language {(bump_form \<phi>)}) (bump_intrp \<M>)\<close>
  unfolding is_interpretation_def language_def
  by (metis bump_dom bump_intrp_fn fst_conv functions_form_bumpform lang_singleton language_def)

(* unbumpterm in hol-light *)
fun unbump_nterm :: "nterm \<Rightarrow> nterm" where
  \<open>unbump_nterm (Var x) = Var x\<close>
| \<open>unbump_nterm (Fun f ts) = Fun (numsnd f) (map unbump_nterm ts)\<close>

(* unbumpform in hol-light *)
fun unbump_form :: "form \<Rightarrow> form" where
  \<open>unbump_form \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>unbump_form (Atom p ts) = Atom p (map unbump_nterm ts)\<close>
| \<open>unbump_form (\<phi> \<^bold>\<longrightarrow> \<psi>) = (unbump_form \<phi>) \<^bold>\<longrightarrow> (unbump_form \<psi>)\<close>
| \<open>unbump_form (\<^bold>\<forall> x\<^bold>. \<phi>) = \<^bold>\<forall> x\<^bold>. (unbump_form \<phi>)\<close>

lemma unbumpterm [simp]: "unbump_nterm (bump_nterm t) = t"
  by (induct t) (simp add: list.map_ident_strong)+

lemma unbumpform [simp]: \<open>unbump_form (bump_form \<phi>) = \<phi>\<close>
  by (induct \<phi>) (simp add: list.map_ident_strong)+

(* unbumpmod in hol-light *)
definition unbump_intrp :: "'m intrp \<Rightarrow> 'm intrp" where
  \<open>unbump_intrp \<M> = Abs_intrp (dom \<M>, (\<lambda>k zs. (intrp_fn \<M>) (numpair 0 k) zs), (intrp_rel \<M>))\<close>

(* UNBUMPMOD_TERM in hol-light *)
lemma unbump_term_intrp: \<open>\<lbrakk>bump_nterm t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>t\<rbrakk>\<^bsup>unbump_intrp \<M>,\<beta>\<^esup>\<close>
proof (induct t)
  case (Fun f ts)
  then show ?case 
    unfolding unbump_intrp_def
    by (smt (verit, best) bump_nterm.simps(2) concat_map eval.simps(2) intrp_fn_Abs_is_fst_snd 
        intrp_is_struct list.map_cong0 struct_def)
qed simp

(*  UNBUMPMOD in hol-light *)
lemma unbump_holds: \<open>(\<M>\<^bold>,\<beta> \<Turnstile> bump_form \<phi>) = (unbump_intrp \<M>\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>
proof (induct \<phi> arbitrary: \<beta>)
  case Bot
  then show ?case
    by auto
next
  case (Atom p ts)
  then show ?case
    unfolding unbump_intrp_def
    by (smt (verit) bump_intrp_def bumpform dom_Abs_is_fst functions_form_bumpform
        holds_indep_intrp_if intrp_fn_Abs_is_fst_snd intrp_is_struct intrp_rel_Abs_is_snd_snd
        numsnd_simp struct_def)
next
  case (Implies \<phi>1 \<phi>2)
  then show ?case
    by auto
next
  case (Forall x \<phi>)
  then show ?case
    by (smt (verit, best) bump_form.simps(4) dom_Abs_is_fst holds.simps(4) intrp_is_struct 
        struct_def unbump_intrp_def)
qed

fun numlist :: "nat list \<Rightarrow> nat" where
  \<open>numlist [] = 0\<close>
| \<open>numlist (n # ls) = numpair n ((numlist ls) + 1) \<close>

lemma numlist_pos: \<open>l \<noteq> [] \<Longrightarrow> numlist l > 0\<close>
proof (induct l)
  case Nil
  then show ?case by blast
next
  case (Cons a l)
  then show ?case
    using numpair_def by auto
qed

lemma numlist_inj: \<open>(numlist l1 = numlist l2) \<equiv> (l1 = l2)\<close>
proof (induction l1 l2 rule: list_induct2')
  case 1
  then show ?case
    by blast
next
  case (2 x xs)
  then show ?case
    using numlist_pos by force
next
  case (3 y ys)
  then show ?case
    using numlist_pos by force
next
  case (4 x xs y ys)
  then show ?case
    by (metis Suc_eq_plus1 nat.simps(1) numlist.simps(2) numpair_inj)
qed

fun num_of_term :: "nterm \<Rightarrow> nat" where
  \<open>num_of_term (Var x) = numpair 0 x\<close>
| \<open>num_of_term (Fun f ts) = numpair 1 (numpair f (numlist (map num_of_term ts)))\<close>

(* to move in AFP theory First-Order Terms.Term *)
lemma term_induct2:
  "(\<And>x y. P (Var x) (Var y))
    \<Longrightarrow> (\<And>x g us. P (Var x) (Fun g us))
    \<Longrightarrow> (\<And>f ts y. P (Fun f ts) (Var y)) 
    \<Longrightarrow> (\<And>f ts g us. (\<And>p q. p \<in> set ts \<Longrightarrow> q \<in> set us \<Longrightarrow> P p q) \<Longrightarrow> P (Fun f ts) (Fun g us))
    \<Longrightarrow> P t1 t2"
proof (induction t2 arbitrary: t1)
  case (Var y)
  then show ?case by (metis is_FunE is_VarE)
next
  case (Fun g us)
  then have \<open>p \<in> set ts \<Longrightarrow> q \<in> set us \<Longrightarrow> P p q\<close> for ts p q
    by blast
  then show ?case
    using Fun by (metis is_FunE is_VarE)
qed
(************************************************)

lemma num_of_term_inj: \<open>num_of_term s = num_of_term t \<equiv> s = t\<close>
proof (induction s t rule: term_induct2)
  case (1 x y)
  then show ?case
    by (metis num_of_term.simps(1) numsnd_simp)
next
  case (2 x g us)
  then show ?case 
    by (metis Term.term.simps(4) le_refl not_one_le_zero num_of_term.elims numpair_inj)
next
  case (3 f ts y)
  then show ?case
    by (metis Term.term.simps(4) not_one_le_zero num_of_term.elims numpair_inj order_refl)
next
  case (4 f ts g us)
  have \<open>(Fun f ts = Fun g us) \<Longrightarrow> num_of_term (Fun f ts) = num_of_term (Fun g us)\<close>
    by auto
  moreover {
    assume \<open>num_of_term (Fun f ts) = num_of_term (Fun g us)\<close>
    then have \<open>numpair f (numlist (map num_of_term ts)) = numpair g (numlist (map num_of_term us))\<close>
      using numpair_inj num_of_term.simps(2) by metis
    then have fun_eq: \<open>f = g\<close> and nl_eq: \<open>numlist (map num_of_term ts) = (numlist (map num_of_term us))\<close>
      using numpair_inj by blast+
    then have "map num_of_term ts = map num_of_term us"
      using numlist_inj by auto
    then have args_eq: \<open>ts = us\<close>
      using 4 by (metis list.inj_map_strong)
    have \<open>Fun f ts = Fun g us\<close>
      using fun_eq args_eq by simp
  }
  ultimately show ?case by auto
qed























end