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
  have is_struct: \<open>struct (dom \<M>) (\<lambda>k zs. (intrp_fn \<M>) (numsnd k) zs) (intrp_rel \<M>)\<close> 
    by (smt (verit, best) intrp_is_struct struct_def)
  then show ?thesis unfolding bump_intrp_def using dom_Abs_is_fst by blast
qed

lemma bump_intrp_fn [simp]: \<open>intrp_fn (bump_intrp \<M>) (numpair 0 f) ts = intrp_fn \<M> f ts\<close>
proof -
  have is_struct: \<open>struct (dom \<M>) (\<lambda>k zs. (intrp_fn \<M>) (numsnd k) zs) (intrp_rel \<M>)\<close> 
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

lemma bumpterm: \<open>eval t \<M> \<beta> = eval (bump_nterm t) (bump_intrp \<M>) \<beta>\<close>
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

lemma bumpintrp: \<open>\<M>, \<beta> \<Turnstile> \<phi> = (bump_intrp \<M>), \<beta> \<Turnstile> (bump_form \<phi>)\<close>
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
  have \<open>(\<forall>a \<in> dom \<M>. (bump_intrp \<M>),\<beta>(x1 := a) \<Turnstile> bump_form \<phi>) = 
    (\<forall>a \<in> dom \<M>. \<M>,\<beta>(x1 := a) \<Turnstile> \<phi>)\<close>
    using Forall by presburger
  then show ?case
    by simp
qed

end