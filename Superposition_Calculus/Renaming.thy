theory Renaming
  imports 
    Fun_Extra 
    First_Order_Clause
begin

section \<open>Abstract Renaming\<close>

locale renaming =
  fixes variables :: "'v set"
  assumes infinite_variables: "infinite variables"
begin

(* TODO: generalize? *)
lemma renaming_exists: 
  assumes  
    "X \<subseteq> variables"
    "Y \<subseteq> variables"
    "finite X"
    "finite Y"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v) subst" where
    "term_subst.is_renaming \<rho>\<^sub>1" 
    "term_subst.is_renaming \<rho>\<^sub>2"
    "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
proof-
  let ?newVars = "variables - Y"

  have "infinite ?newVars"
    by (simp add: assms(4) infinite_variables)

  then obtain renaming where 
    renaming: "inj renaming" "renaming ` X \<subseteq> ?newVars"
    using obtain_inj_endo[OF assms(3)]
    by blast

   define \<rho>\<^sub>1 :: "('f, 'v) subst" where 
    \<rho>\<^sub>1: "\<rho>\<^sub>1  = (\<lambda>var. Var (renaming var))"

  have "inj \<rho>\<^sub>1" "(\<forall>x. is_Var (\<rho>\<^sub>1 x))"
    unfolding \<rho>\<^sub>1
    using renaming(1)
    by (simp_all add: inj_on_def)
    
  then have "term_subst.is_renaming \<rho>\<^sub>1"
    by (simp add: term_subst_is_renaming_iff)

  moreover have "term_subst.is_renaming Var"
    by simp

  moreover have "\<rho>\<^sub>1 ` X \<inter>  Var ` Y = {}"
    using \<rho>\<^sub>1 renaming(2) by auto

  ultimately show ?thesis  
    using that
    by blast
qed

end

end
