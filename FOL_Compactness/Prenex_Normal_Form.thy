(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023 *)

theory Prenex_Normal_Form  
imports
    Ground_FOL_Compactness
begin


inductive is_prenex :: "form \<Rightarrow> bool" where
  \<open>qfree \<phi> \<Longrightarrow> is_prenex \<phi>\<close> 
| \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>
| \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>

inductive_simps is_prenex_simps [simp]:
  "is_prenex Bot"
  "is_prenex (Atom p ts)"
  "is_prenex (\<phi> \<^bold>\<longrightarrow> \<psi>)"
  "is_prenex (\<^bold>\<forall> x\<^bold>. \<phi>)" 

lemma prenex_formsubst1: \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
proof (induction \<phi> arbitrary: \<sigma> rule: is_prenex.induct)
  case 1
  then show ?case using is_prenex.intros(1) qfree_formsubst
    by blast
next
  case (2 \<phi> x)
  then show ?case
    using formsubst_def_switch by (metis (no_types, lifting) formsubst.simps(4) is_prenex.intros(2))
next
  case (3 \<phi> x)
  then show ?case
    using formsubst_def_switch is_prenex.intros(3)
    by (smt (verit, del_insts) formsubst.simps(1) formsubst.simps(3) formsubst.simps(4))
qed

lemma prenex_formsubst2: \<open>is_prenex (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<Longrightarrow> is_prenex \<phi>\<close>
proof (induction \<open>\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>\<close> arbitrary: \<phi> \<sigma> rule: is_prenex.induct)
  case 1
  then show ?case
    using is_prenex.intros(1) qfree_formsubst by auto
next
  case (2 \<psi> x \<phi>)
  then obtain y \<phi>' where phi_is: \<open>\<phi> = \<^bold>\<forall>y\<^bold>. \<phi>'\<close>
    using formsubst_structure_all by metis
  then have \<open>\<exists>\<sigma>'. \<psi> = \<phi>'\<cdot>\<^sub>f\<^sub>m \<sigma>'\<close>
    using 2(3) by (metis (no_types, lifting) form.sel(6) formsubst.simps(4))
  then obtain \<sigma>' where \<open>\<psi> = \<phi>'\<cdot>\<^sub>f\<^sub>m \<sigma>'\<close>
    by blast
  then have \<open>is_prenex \<phi>'\<close>
    using 2(2) by blast
  then show ?case
    using phi_is by (simp add: is_prenex.intros(2))
next
  case (3 \<psi> x \<phi>)
  then obtain y \<phi>' where phi_is: \<open>\<phi> = \<^bold>\<exists>y\<^bold>. \<phi>'\<close>
    using formsubst_structure_ex by metis
  then have \<open>\<exists>\<sigma>'. \<psi> = \<phi>'\<cdot>\<^sub>f\<^sub>m \<sigma>'\<close>
    using 3(3) by (smt (verit, ccfv_threshold) form.inject(2) form.inject(3) formsubst.simps(3)
        formsubst.simps(4))
  then obtain \<sigma>' where \<open>\<psi> = \<phi>'\<cdot>\<^sub>f\<^sub>m \<sigma>'\<close>
    by blast
  then have \<open>is_prenex \<phi>'\<close>
    using 3(2) by blast
  then show ?case
    using phi_is by (simp add: is_prenex.intros(3))
qed

lemma prenex_formsubst: \<open>is_prenex (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<equiv> is_prenex \<phi>\<close>
  using prenex_formsubst1 prenex_formsubst2 by (smt (verit, ccfv_threshold))

lemma prenex_imp: \<open>is_prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) \<Longrightarrow> 
  qfree (\<phi> \<^bold>\<longrightarrow> \<psi>) \<or> (\<psi> = \<^bold>\<bottom> \<and> (\<exists>x \<phi>'. is_prenex \<phi>' \<and> \<phi> = (\<^bold>\<forall>x\<^bold>. \<phi>' \<^bold>\<longrightarrow> \<^bold>\<bottom>)))\<close>
  by (metis form.distinct(11) form.inject(2) is_prenex.cases)

inductive universal :: "form \<Rightarrow> bool" where
  \<open>qfree \<phi> \<Longrightarrow> universal \<phi>\<close>
| \<open>universal \<phi> \<Longrightarrow> universal (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>

inductive_simps universal_simps [simp]:
  "universal Bot"
  "universal (Atom p ts)"
  "universal (\<phi> \<^bold>\<longrightarrow> \<psi>)"
  "universal (\<^bold>\<forall> x\<^bold>. \<phi>)" 

fun size :: "form \<Rightarrow> nat" where
  \<open>size \<^bold>\<bottom> = 1\<close>
| \<open>size (Atom p ts) = 1\<close>
| \<open>size (\<phi> \<^bold>\<longrightarrow> \<psi>) = size \<phi> + size \<psi>\<close>
| \<open>size (\<^bold>\<forall> x\<^bold>. \<phi>) = 1 + size \<phi>\<close>

lemma wf_size: \<open>wfP (\<lambda>\<phi> \<psi>. size \<phi> < size \<psi>)\<close>
  by (simp add: wfp_if_convertible_to_nat)

lemma size_indep_subst: \<open>size (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = size \<phi>\<close>
proof (induction \<phi> arbitrary: \<sigma>)
  case (Forall x \<phi>)
  have \<open>\<exists>z \<sigma>'.(\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall>z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')\<close>
    by (meson formsubst.simps(4))
  then obtain z \<sigma>' where \<open>(\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall>z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')\<close>
    by blast
  then have \<open>size ((\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = size (\<^bold>\<forall>z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'))\<close>
    by argo
  also have \<open>... = size (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>
    using Forall by auto
  finally show ?case .
qed auto


lemma prenex_distinct: \<open>(\<^bold>\<forall>x\<^bold>. \<phi>) \<noteq> (\<^bold>\<exists>y\<^bold>. \<psi>)\<close>
  by auto

lemma uniq_all_x: "Uniq (\<lambda>x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p)" (* necessaire pour décharger le "THE" *)
  using Uniq_def by blast

lemma uniq_all_p: \<open>Uniq ((\<lambda>p. r = \<^bold>\<forall>(THE x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p)\<^bold>. p))\<close>
  using uniq_all_x Uniq_def
  by (smt (verit, ccfv_threshold) form.inject(3))

lemma uniq_ex_x: "Uniq (\<lambda>x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p)"
  using Uniq_def by blast

lemma uniq_ex_p: \<open>Uniq ((\<lambda>p. r = \<^bold>\<exists>(THE x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p)\<^bold>. p))\<close>
  using uniq_ex_x Uniq_def
  by (smt (verit, best) form.inject(2) form.inject(3))

definition ppat :: "(nat \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> (nat \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> (form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> form" where
  \<open>ppat A B C r = (if (\<exists>x p. r = \<^bold>\<forall>x\<^bold>. p) then
    A (THE x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p) (THE p. r = \<^bold>\<forall>(THE x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p)\<^bold>. p)
  else (if \<exists>x p. r = \<^bold>\<exists>x\<^bold>. p then
    B (THE x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p) (THE p. r = \<^bold>\<exists>(THE x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p)\<^bold>. p) 
   else C r))\<close>

lemma ppat_simpA: \<open>\<forall>x p. ppat A B C (\<^bold>\<forall>x\<^bold>. p) = A x p\<close>
  unfolding ppat_def by simp

lemma ppat_simpB: \<open>\<forall>x p. ppat A B C (\<^bold>\<exists>x\<^bold>. p) = B x p\<close>
  unfolding ppat_def by simp

(* simplified unneeded hypotheses: (\<forall>x p. ppat A B C (\<^bold>\<forall>x\<^bold>. p) = A x p) \<Longrightarrow> (\<forall>x p. ppat A B C (\<^bold>\<exists>x\<^bold>. p) = B x p) *)
lemma ppat_last: \<open>(\<forall>r. \<not>(\<exists>x p. r = \<^bold>\<forall>x\<^bold>. p) \<and> \<not>(\<exists>x p. r = \<^bold>\<exists>x\<^bold>. p)) \<Longrightarrow> ppat A B C r = C r\<close>
  by blast

(* idem here *)
lemma ppat_last_qfree: \<open>qfree r \<Longrightarrow> ppat A B C r = C r\<close>
  using qfree_no_quantif ppat_last by (simp add: ppat_def)

(* holds but useless because not recursive *)
lemma ppat_to_ex_qfree:
  \<open>(\<exists>f. (\<forall>x p q. f p (\<^bold>\<forall>x\<^bold>. q) = ((A :: form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form) p) x q) \<and>
  (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = (B p) x q) \<and> 
  (\<forall>p q. qfree q \<longrightarrow> f p q = (C p) q))\<close>
proof
  define f where \<open>f = (\<lambda>p q. ppat (A p) (B p) (C p) q)\<close>
  have A_eq: \<open>(\<forall>x p q. ppat (A p) (B p) (C p) (\<^bold>\<forall>x\<^bold>. q) = (A p) x q)\<close> and 
    B_eq: \<open>(\<forall>x p q. ppat (A p) (B p) (C p) (\<^bold>\<exists>x\<^bold>. q) = (B p) x q)\<close>
    unfolding ppat_def by simp+
  have  C_eq: \<open>(\<forall>p q. qfree q \<longrightarrow> ppat (A p) (B p) (C p) q = (C p) q)\<close>
    using ppat_last_qfree by blast
  show \<open>(\<forall>x p q. f p (\<^bold>\<forall> x\<^bold>. q) = A p x q) \<and> (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = B p x q) \<and> (\<forall>p q. qfree q \<longrightarrow> f p q = (C p) q)\<close>
    using A_eq B_eq C_eq unfolding f_def by blast
qed

term \<open>\<forall>\<phi>. \<exists>g. \<forall>\<psi>. g \<psi> = ppat (A g \<phi>) (B g \<phi>) (C \<phi>) \<psi>\<close> (* proven subgoal abstraction *)
term \<open>\<exists>f. \<forall>\<phi> \<psi>. f \<phi> \<psi> = ppat (prenex_right_forall f \<phi>) (prenex_right_exists f \<phi>) ((\<^bold>\<longrightarrow>) \<phi>) \<psi>\<close> (* same after choice *)
term \<open>A g \<phi> = (\<lambda>x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. g (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
term \<open>A = (\<lambda>g \<phi> x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. g (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>


lemma size_rec: 
  \<open>\<forall>f g x. (\<forall>(z::form). size z < size x \<longrightarrow> (f z = g z)) \<longrightarrow> (H f x = H g x) \<Longrightarrow> (\<exists>f. \<forall>x. f x = H f x)\<close>
  using wfrec [of "measure size" H] by (metis cut_apply in_measure wf_measure)

abbreviation prenex_right_forall :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where 
  \<open>prenex_right_forall \<equiv> 
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. p \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>

abbreviation prenex_right_exists :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where 
  \<open>prenex_right_exists \<equiv> 
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. p \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>

lemma prenex_right_ex: 
  \<open>\<exists>prenex_right. (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>)
    \<and> (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>)
    \<and> (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
proof -
  have \<open>\<forall>\<phi>. \<exists>prenex_right_only. \<forall>\<psi>. prenex_right_only \<psi> = ppat 
    (\<lambda>x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. prenex_right_only (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))
    (\<lambda>x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. prenex_right_only (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))
    (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
  proof
    fix \<phi>
    define A where \<open>A = (\<lambda>g x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. g (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
    define B where \<open>B = (\<lambda>p x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. p (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
    show \<open>\<exists>prenex_right_only. \<forall>\<psi>. prenex_right_only \<psi> = 
      ppat (A prenex_right_only) (B prenex_right_only) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
    proof (rule size_rec, (rule allI)+, (rule impI))
      fix prenex_right_only g:: "form \<Rightarrow> form" and \<psi>
      assume IH: \<open>\<forall>z. size z < size \<psi> \<longrightarrow> prenex_right_only z = g z\<close>
      show \<open>ppat (A prenex_right_only) (B prenex_right_only) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi> =
        ppat (A g) (B g) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
      proof (cases "\<exists>x \<psi>'. \<psi> = \<^bold>\<forall>x\<^bold>. \<psi>'")
        case True
        then obtain x \<psi>' where psi_is: "\<psi> = \<^bold>\<forall>x\<^bold>. \<psi>'"
          by blast
        then have smaller: \<open>size (\<psi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<psi>\<close> for \<sigma>
          using size_indep_subst by simp
        have \<open>ppat (A prenex_right_only) (B prenex_right_only) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi> = 
          A prenex_right_only x \<psi>'\<close>
          unfolding ppat_def by (simp add: psi_is)
        also have \<open>... = A g x \<psi>'\<close>
          unfolding A_def using IH smaller by presburger
        also have \<open>... = ppat (A g) (B g) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
          unfolding ppat_def by (simp add: psi_is)
        finally show ?thesis .
      next
        case False
        assume falseAll: \<open>\<not>(\<exists>x \<psi>'. \<psi> = \<^bold>\<forall> x\<^bold>. \<psi>')\<close>
        then show ?thesis
        proof (cases "\<exists>x \<psi>'. \<psi> = \<^bold>\<exists>x\<^bold>. \<psi>'")
          case True
          then obtain x \<psi>' where psi_is: "\<psi> = \<^bold>\<exists>x\<^bold>. \<psi>'"
            by blast
          then have smaller: \<open>size (\<psi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<psi>\<close> for \<sigma>
            using size_indep_subst by simp
        have \<open>ppat (A prenex_right_only) (B prenex_right_only) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi> = 
          B prenex_right_only x \<psi>'\<close>
          unfolding ppat_def by (simp add: psi_is)
        also have \<open>... = B g x \<psi>'\<close>
          unfolding B_def using IH smaller by presburger
        also have \<open>... = ppat (A g) (B g) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
          unfolding ppat_def by (simp add: psi_is)
        finally show ?thesis .
        next
          case False
          then show ?thesis
            using falseAll ppat_last unfolding ppat_def by argo
        qed 
      qed
    qed
  qed
  then have \<open>\<exists>prenex_right. \<forall>\<phi> \<psi>. prenex_right \<phi> \<psi> = ppat
                (prenex_right_forall prenex_right \<phi>)
                (prenex_right_exists prenex_right \<phi>) 
                ((\<^bold>\<longrightarrow>) \<phi>) \<psi>\<close>
    using choice[of "\<lambda>\<phi> p. \<forall>\<psi>. p \<psi> =
            ppat (\<lambda>x \<psi>. let y = variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in \<^bold>\<forall>y\<^bold>. p (\<psi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)))
              (\<lambda>x \<psi>. let y = variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. p (\<psi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))))
              ((\<^bold>\<longrightarrow>) \<phi>) \<psi>"] by blast
  then obtain prenex_right where prenex_right_is: \<open>\<forall>\<phi> \<psi>. prenex_right \<phi> \<psi> = 
    ppat (prenex_right_forall prenex_right \<phi>) (prenex_right_exists prenex_right \<phi>) ((\<^bold>\<longrightarrow>) \<phi>) \<psi>\<close>
    by blast
(* then show each property separately *)
  have \<open>\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>\<close>
    using prenex_right_is unfolding ppat_def by simp
  moreover have \<open>\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>\<close>
    using prenex_right_is unfolding ppat_def by simp
  moreover have \<open>\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>)\<close>
    using prenex_right_is by (metis (no_types, lifting) ppat_last_qfree)
  ultimately show ?thesis
    by blast
qed

(* is it unique? \<rightarrow> No, it is undefined in the last case if \<not>qfree \<phi>. Use SOME, not THE  *)
consts prenex_right :: "form \<Rightarrow> form \<Rightarrow> form"
specification (prenex_right) \<open>
  (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>) \<and>
  (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>) \<and>
  (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
  using prenex_right_ex by blast

lemma prenex_right_qfree_case: \<open>qfree \<psi> \<Longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>)\<close>
proof -
  assume qfree_psi: "qfree \<psi>"
  have \<open>((\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall p \<phi> x \<psi>) \<and>
  (\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists p \<phi> x \<psi>) \<and>
  (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> p \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))) \<Longrightarrow> (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> p \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close> (is "?P p \<Longrightarrow> ?Q p") for p 
    by argo
  then have \<open>(\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
    using someI2_ex[of ?P ?Q] prenex_right_def prenex_right_ex by presburger
  then show ?thesis
    using qfree_psi by blast
qed

lemma prenex_right_all_case: \<open>prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>\<close>
proof -
  have all_cases_imp_all_case: \<open>((\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall p \<phi> x \<psi>) \<and>
   (\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists p \<phi> x \<psi>) \<and>
   (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> p \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))) \<Longrightarrow>
   (p \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall p \<phi> x \<psi>)\<close> (is "?P p \<Longrightarrow> ?Q p") for p
    by meson
  then have \<open>prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>\<close>
    using someI2_ex[of ?P ?Q] prenex_right_def prenex_right_ex by presburger
  then show ?thesis .
qed

lemma prenex_right_exist_case: \<open>prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>\<close>
proof -
  have ex_cases_imp_ex_case: \<open>((\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall p \<phi> x \<psi>) \<and>
   (\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists p \<phi> x \<psi>) \<and>
   (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> p \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))) \<Longrightarrow>
   (p \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists p \<phi> x \<psi>)\<close> (is "?P p \<Longrightarrow> ?Q p") for p
    by meson
  then have \<open>prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>\<close>
    using someI2_ex[of ?P ?Q] prenex_right_def prenex_right_ex by presburger
  then show ?thesis .
qed

lemma prenex_right_exists_shape_case: 
  \<open>\<exists>x2 \<sigma>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = \<^bold>\<exists>x2\<^bold>. prenex_right \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
proof -
  have all_cases_imp_all_case: \<open>((\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall p \<phi> x \<psi>) \<and>
   (\<forall>\<phi> x \<psi>. p \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists p \<phi> x \<psi>) \<and>
   (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> p \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))) \<Longrightarrow>
   (\<exists>x2 \<sigma>. p \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = \<^bold>\<exists>x2\<^bold>. p \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m \<sigma>))\<close> (is "?P p \<Longrightarrow> ?Q p") for p
    by meson
  then have \<open>\<exists>x2 \<sigma>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = \<^bold>\<exists>x2\<^bold>. prenex_right \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
    using someI2_ex[of ?P ?Q] prenex_right_def prenex_right_ex by presburger
  then show ?thesis .
qed


abbreviation prenex_left_forall :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where 
  \<open>prenex_left_forall \<equiv> 
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))) \<psi>)))\<close>

abbreviation prenex_left_exists :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where 
  \<open>prenex_left_exists \<equiv> 
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<forall>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))) \<psi>)))\<close>

lemma prenex_left_ex:
  \<open>\<exists>prenex_left. (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = prenex_left_forall prenex_left \<phi> x \<psi>)
    \<and> (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>)
    \<and> (\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>)\<close>
proof -
  have \<open>\<forall>\<psi>. \<exists>prenex_left_only. \<forall>\<phi>. prenex_left_only \<phi> = ppat
    (\<lambda>x \<phi>. (let y = variant(FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. prenex_left_only (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))
    (\<lambda>x \<phi>. (let y = variant(FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<forall>y\<^bold>. prenex_left_only (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))
    (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
  proof
    fix \<psi>
    define A where \<open>A = (\<lambda>g x \<phi>. (let y = variant(FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. g (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
    define B where \<open>B = (\<lambda>p x \<phi>. (let y = variant(FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<forall>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
    show \<open>\<exists>prenex_left_only. \<forall>\<phi>. prenex_left_only \<phi> =
      ppat (A prenex_left_only) (B prenex_left_only) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
    proof (rule size_rec, (rule allI)+, (rule impI))
      fix prenex_left_only g:: "form \<Rightarrow> form" and \<phi>
      assume IH: \<open>\<forall>z. size z < size \<phi> \<longrightarrow> prenex_left_only z = g z\<close>
      show \<open>ppat (A prenex_left_only) (B prenex_left_only) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi> =
        ppat (A g) (B g) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
      proof (cases "\<exists>x \<phi>'. \<phi> = \<^bold>\<forall>x\<^bold>. \<phi>'")
        case True
        then obtain x \<phi>' where phi_is: "\<phi> = \<^bold>\<forall>x\<^bold>. \<phi>'"
          by blast
        then have smaller: \<open>size (\<phi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<phi>\<close> for \<sigma>
          using size_indep_subst by simp
        have \<open>ppat (A prenex_left_only) (B prenex_left_only) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi> = 
          A prenex_left_only x \<phi>'\<close>
          unfolding ppat_def by (simp add: phi_is)
        also have \<open>... = A g x \<phi>'\<close>
          unfolding A_def using IH smaller by presburger
        also have \<open>... = ppat (A g) (B g) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
          unfolding ppat_def by (simp add: phi_is)
        finally show ?thesis .
      next
        case False
        assume falseAll: \<open>\<not>(\<exists>x \<phi>'. \<phi> = \<^bold>\<forall> x\<^bold>. \<phi>')\<close>
        then show ?thesis
        proof (cases "\<exists>x \<phi>'. \<phi> = \<^bold>\<exists>x\<^bold>. \<phi>'")
          case True
          then obtain x \<phi>' where phi_is: "\<phi> = \<^bold>\<exists>x\<^bold>. \<phi>'"
            by blast
          then have smaller: \<open>size (\<phi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<phi>\<close> for \<sigma>
            using size_indep_subst by simp
        have \<open>ppat (A prenex_left_only) (B prenex_left_only) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi> = 
          B prenex_left_only x \<phi>'\<close>
          unfolding ppat_def by (simp add: phi_is)
        also have \<open>... = B g x \<phi>'\<close>
          unfolding B_def using IH smaller by presburger
        also have \<open>... = ppat (A g) (B g) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
          unfolding ppat_def by (simp add: phi_is)
        finally show ?thesis .
        next
          case False
          then show ?thesis
            using falseAll ppat_last unfolding ppat_def by argo
        qed 
      qed
    qed
  qed
  then have \<open>\<exists>prenex_left_argswap. \<forall>\<psi> \<phi>. prenex_left_argswap \<psi> \<phi> = ppat
    (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. prenex_left_argswap \<psi> (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))))
    (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in \<^bold>\<forall> y\<^bold>. prenex_left_argswap \<psi> (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)))
    (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
    using choice[of "\<lambda>\<psi> p. \<forall>\<phi>. p \<phi> =
            ppat (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))))
              (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in \<^bold>\<forall>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)))
              (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>"] by blast
  then have \<open>\<exists>prenex_left. \<forall>\<phi> \<psi>. prenex_left \<phi> \<psi> = ppat
    (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. prenex_left (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)) \<psi>))
    (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in \<^bold>\<forall> y\<^bold>. prenex_left (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)) \<psi>)
    (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
    by force
  then obtain prenex_left where prenex_left_is: \<open>\<forall>\<phi> \<psi>. prenex_left \<phi> \<psi> = ppat
    (\<lambda>x \<phi>. prenex_left_forall prenex_left \<phi> x \<psi>)
    (\<lambda>x \<phi>. prenex_left_exists prenex_left \<phi> x \<psi>)
    (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
    by blast
  have \<open>\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> =  prenex_left_forall prenex_left \<phi> x \<psi>\<close>
    using prenex_left_is unfolding ppat_def by simp
  moreover have \<open>\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>\<close>
    using prenex_left_is unfolding ppat_def by simp
  moreover have \<open>\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>\<close>
    using prenex_left_is by (metis (no_types, lifting) ppat_last_qfree)
  ultimately show ?thesis
    by blast
qed

definition prenex_left where \<open>prenex_left = (SOME prenex_left.
  (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = prenex_left_forall prenex_left \<phi> x \<psi>) \<and>
  (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>) \<and>
  (\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>))\<close>

lemma prenex_left_forall_case: \<open>prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = prenex_left_forall prenex_left \<phi> x \<psi>\<close>
  unfolding prenex_left_def by (smt (verit, del_insts) prenex_left_ex some_eq_ex)

lemma prenex_left_qfree_case: \<open>qfree \<phi> \<Longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>\<close>
  unfolding prenex_left_def by (smt (verit, del_insts) prenex_left_ex some_eq_ex)

lemma prenex_left_exists_case: \<open>prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>\<close>
  unfolding prenex_left_def by (smt (verit, del_insts) prenex_left_ex some_eq_ex)

lemma prenex_left_exists_shape_case: 
  \<open>\<exists>x2 \<sigma>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = \<^bold>\<forall>x2\<^bold>. prenex_left (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<psi>\<close>
  using prenex_left_exists_case by metis


fun prenex where
  \<open>prenex \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>prenex (Atom p ts) = Atom p ts\<close>
| \<open>prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) = prenex_left (prenex \<phi>) (prenex \<psi>)\<close>
| \<open>prenex (\<^bold>\<forall>x\<^bold>. \<phi>) = \<^bold>\<forall>x\<^bold>. (prenex \<phi>)\<close>

lemma holds_indep_forall:
  assumes y_notin: \<open>y \<notin> FV (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>
  shows \<open>(I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
proof (cases \<open>y = x\<close>)
  case False
  then have y_notin_phi: \<open>y \<notin> FV \<phi>\<close> using y_notin by simp
  have beta_equiv: \<open>\<forall>w \<in> FV \<phi>. (\<lambda>v. termsubst I (\<beta>(y := a)) (subst x (Var y)) v) w = (\<beta>(x := a)) w\<close> for a
  proof
    fix w
    assume w_in: \<open>w \<in> FV \<phi>\<close>
    have \<open>w = x \<Longrightarrow> (\<lambda>v. termsubst I (\<beta>(y := a)) (subst x (Var y)) v) w = (\<beta>(x := a)) w\<close>
      by simp
    moreover have \<open>w \<noteq> x \<Longrightarrow> (\<lambda>v. termsubst I (\<beta>(y := a)) (subst x (Var y)) v) w = (\<beta>(x := a)) w\<close>
      using y_notin_phi by (metis w_in eval.simps(1) fun_upd_other subst_def)
    ultimately show \<open>(\<lambda>v. termsubst I (\<beta>(y := a)) (subst x (Var y)) v) w = (\<beta>(x := a)) w\<close>
      by argo
  qed
  have \<open>I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<equiv> (\<forall>a \<in> dom I. I\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>)\<close>
    by simp
  also have \<open>... \<equiv> (\<forall>a \<in> dom I. I\<^bold>,(\<lambda>v. termsubst I (\<beta>(y := a)) (subst x (Var y)) v) \<Turnstile> \<phi>)\<close>
    using holds_indep_\<beta>_if[OF beta_equiv] by presburger
  also have \<open>... \<equiv> (\<forall>a \<in> dom I. I\<^bold>,\<beta>(y := a) \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
    using swap_subst_eval[of I _ \<phi> "subst x (Var y)"] by presburger
  also have \<open>... \<equiv> (I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
    by simp
  finally show ?thesis
      by argo
qed auto

lemma forall_imp_commute:
  assumes y_notin: \<open>y \<notin> FV \<phi>\<close>
  shows \<open>((I :: 'a intrp)\<^bold>, \<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>y\<^bold>. \<psi>))  \<longleftrightarrow>  I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
proof -
  have \<open>((I\<^bold>, \<beta> \<Turnstile> \<phi>) \<longrightarrow> (\<forall>a \<in> dom I. I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>))  \<longleftrightarrow>
    (\<forall>a \<in> dom I. (I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>))\<close>
    by (smt (verit, del_insts) fun_upd_other holds_indep_\<beta>_if assms)
  then show ?thesis
    by simp
qed

lemma forall_imp_exists: 
  assumes y_notin: \<open>y \<notin> FV \<psi>\<close>
  shows \<open>((I :: 'a intrp)\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<forall>y\<^bold>.\<phi>) \<^bold>\<longrightarrow>  \<psi>)  \<longleftrightarrow>  I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. (\<phi> \<^bold>\<longrightarrow> \<psi>)))\<close>
proof -
  have \<open>((\<forall>a \<in> dom I. I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi>) \<longrightarrow> (I\<^bold>, \<beta> \<Turnstile> \<psi>)) \<longleftrightarrow>  (\<exists>a \<in> dom I. (I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>))\<close>
    using empty_iff list.set(1)
    by (smt (verit, best) equals0I intrp_is_struct struct_def)
  also have \<open>... \<longleftrightarrow> (\<exists>a \<in> dom I. (I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>))\<close>
    using holds_indep_\<beta>_if by (smt (verit, del_insts) fun_upd_other y_notin)
  finally show ?thesis
    by simp
qed

lemma exists_imp_forall: 
  assumes y_notin: \<open>y \<notin> FV \<psi>\<close>
  shows \<open>(I\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<exists>y\<^bold>.\<phi>) \<^bold>\<longrightarrow>  \<psi>)  \<longleftrightarrow>  I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. (\<phi> \<^bold>\<longrightarrow> \<psi>)))\<close>
proof -
  have \<open>(\<exists>a \<in> dom I. I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi>) \<longrightarrow> (I\<^bold>, \<beta> \<Turnstile> \<psi>) \<equiv>
    (\<forall>a \<in> dom I. (I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>))\<close>
    using empty_iff list.set(1) by (smt (verit, ccfv_threshold))
  also have \<open>... \<equiv> (\<forall>a \<in> dom I. (I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>))\<close>
    using holds_indep_\<beta>_if by (smt (verit, del_insts) fun_upd_other y_notin)
  finally show ?thesis
    by simp
qed

lemma exists_imp_commute: 
  assumes y_notin: \<open>y \<notin> FV \<phi>\<close>
  shows \<open>((I :: 'a intrp)\<^bold>, \<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>y\<^bold>. \<psi>)) \<longleftrightarrow> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
proof -
  have \<open>((I\<^bold>, \<beta> \<Turnstile> \<phi>) \<longrightarrow> (\<exists>a \<in> dom I. I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>)) \<longleftrightarrow>
   (\<exists>a \<in> dom I. (I\<^bold>, \<beta> \<Turnstile> \<phi>) \<longrightarrow> (I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>))\<close>
    by (smt (verit) equals0I intrp_is_struct struct_def)
  also have \<open>... \<longleftrightarrow> (\<exists>a \<in> dom I. (I\<^bold>,\<beta>(y := a) \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta>(y := a) \<Turnstile> \<psi>))\<close>
    using y_notin by (smt (verit, ccfv_threshold) fun_upd_other holds_indep_\<beta>_if)
  finally show ?thesis
    using holds_exists by simp
qed


lemma holds_indep_exists: 
  \<open>y \<notin> FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<Longrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>)  \<longleftrightarrow>  I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
  by (metis FV.simps(1,3) formsubst.simps(1,3) holds.simps(3) holds_indep_forall sup_bot.right_neutral)

(* sublemmas for is_prenex(prenex _)*)

(* holds M (v:num->A) (p --> !!y (formsubst (valmod (x,V y) V) q)) *)
lemma prenex_right_forall_is:
  assumes \<open>dom I \<noteq> {}\<close> 
  shows \<open>((I\<^bold>, \<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>x\<^bold>. \<psi>))  \<longleftrightarrow>
  (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>(variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)))\<^bold>. 
             (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>))))))))))\<close> (is "?lhs = ?rhs")
proof -
  define y where \<open>y = variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>))\<close>
  then have y_notin1: \<open>y \<notin> FV \<phi>\<close> and y_notin2: \<open>y \<notin> FV (\<^bold>\<forall>x\<^bold>. \<psi>)\<close>
  using variant_finite finite_FV by (meson UnCI finite_UnI)+
  have \<open>?lhs \<longleftrightarrow> I\<^bold>, \<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>y\<^bold>. \<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
    using holds_indep_forall y_notin2
    by (smt (verit, ccfv_SIG) holds.simps(3))
  also have \<open>... \<longleftrightarrow> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
    using forall_imp_commute[OF y_notin1, of I \<beta> "\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))"] .
  finally show ?thesis
    unfolding y_def .
qed

lemma prenex_right_exists_is:
  assumes \<open>dom I \<noteq> {}\<close> 
  shows \<open>((I\<^bold>, \<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>x\<^bold>. \<psi>))  \<longleftrightarrow>
  (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>(variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)))\<^bold>. 
             (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>))))))))))\<close> (is "?lhs = ?rhs")
proof -
  define y where \<open>y = variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>))\<close>
  then have y_notin1: \<open>y \<notin> FV \<phi>\<close> and y_notin2: \<open>y \<notin> FV (\<^bold>\<exists>x\<^bold>. \<psi>)\<close>
  using variant_finite finite_FV by (meson UnCI finite_UnI)+
  have \<open>?lhs \<longleftrightarrow> I\<^bold>, \<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>y\<^bold>. \<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
    using holds_indep_exists y_notin2 holds_exists by (smt (verit) holds.simps(3))
  also have \<open>... \<longleftrightarrow> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. \<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
    using exists_imp_commute[OF y_notin1, of I \<beta> "\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))"] .
  finally show ?thesis
    unfolding y_def .
qed

lemma prenex_left_forall_is:
  assumes \<open>dom I \<noteq> {}\<close> 
  shows \<open>(I\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<forall>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>)) \<equiv> (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>(variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>.
               ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>)))\<close>
  using forall_imp_exists holds_indep_forall holds.simps(3)
  by (smt (verit, del_insts) FV.simps(3) UnI2 sup.commute variant_form)

lemma prenex_left_exists_is:
  assumes \<open>dom I \<noteq> {}\<close> 
  shows \<open>(I\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<exists>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>)) \<equiv> (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>(variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>.
               ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>)))\<close>
  using exists_imp_forall holds_indep_exists holds.simps(3)
  by (smt (verit, ccfv_SIG) FV.simps(3) UnCI finite_FV variant_finite)

(* sublemmas for prenex prop on FV *)
lemma prenex_right_forall_FV: \<open>FV (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>x\<^bold>. \<psi>)) =
  FV (\<^bold>\<forall>(variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)))\<^bold>. (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>))))))))\<close>
  using formsubst_rename
  by (metis Diff_empty Diff_insert0 FV.simps(3) FV.simps(4) Un_Diff finite_FV variant_finite)

lemma prenex_right_exists_FV: \<open>FV (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>x\<^bold>. \<psi>)) =
  FV (\<^bold>\<forall>(variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)))\<^bold>. (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>))))))))\<close>
  using formsubst_rename prenex_right_forall_FV by force

lemma prenex_left_forall_FV: \<open>FV ((\<^bold>\<forall>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>) =
  FV (\<^bold>\<exists>(variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>. ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>))\<close>
  using formsubst_rename
  by (metis Diff_idemp Diff_insert_absorb FV.simps(3) FV.simps(4) Un_Diff finite_FV variant_finite FV_exists)

lemma prenex_left_exists_FV: \<open>FV ((\<^bold>\<exists>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>) =
  FV (\<^bold>\<forall>(variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>. ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>))\<close>
  using formsubst_rename FV_exists prenex_left_forall_FV by auto

(* sublemmas for prenex prop on language *)
lemma prenex_right_forall_language: \<open>language {\<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>x\<^bold>. \<psi>)} =
  language {\<^bold>\<forall>(variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)))\<^bold>. (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)))))))}\<close>
  using lang_singleton formsubst_functions_form formsubst_predicates formsubst_language_rename by auto

lemma prenex_right_exists_language: \<open>language {\<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>x\<^bold>. \<psi>)} =
  language {\<^bold>\<exists>(variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)))\<^bold>. (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)))))))}\<close>
  using lang_singleton formsubst_functions_form formsubst_predicates formsubst_language_rename by auto

lemma prenex_left_forall_language: \<open>language {(\<^bold>\<forall>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>} =
  language {\<^bold>\<exists>(variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>. ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>)}\<close>
  using lang_singleton formsubst_functions_form formsubst_predicates formsubst_language_rename by auto

lemma prenex_left_exists_language: \<open>language {(\<^bold>\<exists>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>} =
  language {\<^bold>\<forall>(variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>. ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>)}\<close>
  using lang_singleton formsubst_functions_form formsubst_predicates formsubst_language_rename by auto

(* prenex properties lemmas *)
lemma prenex_props_forall: \<open>P \<and> FV \<phi> = FV \<psi> \<and> language {\<phi>} = language {\<psi>} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>)) \<Longrightarrow>
  P \<and> FV (\<^bold>\<forall>x\<^bold>. \<phi>) = FV (\<^bold>\<forall>x\<^bold>. \<psi>) \<and> language {(\<^bold>\<forall>x\<^bold>. \<phi>)} = language {(\<^bold>\<forall>x\<^bold>. \<psi>)} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<psi>)))
\<close>
  using lang_singleton by simp

lemma prenex_props_exists: \<open>P \<and> FV \<phi> = FV \<psi> \<and> language {\<phi>} = language {\<psi>} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>)) \<Longrightarrow>
  P \<and> FV (\<^bold>\<exists>x\<^bold>. \<phi>) = FV (\<^bold>\<exists>x\<^bold>. \<psi>) \<and> language {(\<^bold>\<exists>x\<^bold>. \<phi>)} = language {(\<^bold>\<exists>x\<^bold>. \<psi>)} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>) \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<psi>)))
\<close>
  using lang_singleton by simp

lemma prenex_right_props_imp0:
  assumes \<open>qfree \<phi>\<close>
  shows \<open>is_prenex \<psi> \<Longrightarrow> is_prenex (prenex_right \<phi> \<psi>)\<close>
proof (induction \<psi> rule: measure_induct_rule [of size])
  case (less \<psi>)
  show ?case
  proof (cases rule: is_prenex.cases[OF \<open>is_prenex \<psi>\<close>])
    case (1 \<xi>)
    then show ?thesis
      by (simp add: assms prenex_right_qfree_case)
  next
    case (2 \<xi> x)
    then have \<open>prenex_right \<phi> \<psi> = prenex_right_forall prenex_right \<phi> x \<xi>\<close>
      using prenex_right_all_case by blast
    then show \<open>is_prenex (prenex_right \<phi> \<psi>)\<close>
      using less 2 by (auto simp: Let_def prenex_formsubst1 size_indep_subst)
  next
    case (3 \<xi> x)
    then have \<open>\<exists>y \<sigma>. prenex_right \<phi> \<psi> = \<^bold>\<exists>y\<^bold>. prenex_right \<phi> (\<xi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
      using prenex_right_exists_shape_case by presburger
    then obtain y \<sigma> where pr_is: \<open>prenex_right \<phi> \<psi> = \<^bold>\<exists>y\<^bold>. prenex_right \<phi> (\<xi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
      by blast
    have size_xp: \<open>size (\<xi> \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<psi>\<close> 
      using 3(1) size_indep_subst by auto
    have \<open>is_prenex (\<xi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
      using 3(2) prenex_formsubst1 by blast
    then have \<open>is_prenex (prenex_right \<phi> (\<xi> \<cdot>\<^sub>f\<^sub>m \<sigma>))\<close>
      using less size_xp by blast
    then show ?thesis
      using is_prenex.intros(3) pr_is by presburger
  qed
qed

lemma prenex_right_props_imp: 
  assumes \<open>qfree \<phi>\<close>
  shows \<open>is_prenex \<psi> \<Longrightarrow> 
         is_prenex (prenex_right \<phi> \<psi>) \<and>
         FV (prenex_right \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
         language {prenex_right \<phi> \<psi>} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)} \<and>
         (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> ((I\<^bold>,\<beta> \<Turnstile> (prenex_right \<phi> \<psi>)) \<longleftrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> \<psi>))))\<close>
        (is \<open>is_prenex \<psi> \<Longrightarrow> ?P \<psi>\<close>)
proof (induction \<psi> rule: measure_induct_rule [of size])
  case (less \<psi>)
  show ?case
  proof (cases rule: is_prenex.cases[OF \<open>is_prenex \<psi>\<close>])
    case (1 \<xi>)
    then show ?thesis
      using prenex_right_qfree_case \<open>qfree \<phi>\<close> is_prenex.intros(1) qfree.simps(3) by presburger
  next
    case (2 \<xi> x)
    have pr_is1:\<open>prenex_right \<phi> \<psi> = prenex_right_forall prenex_right \<phi> x \<xi>\<close>
      using 2 prenex_right_all_case by blast
    define y where \<open>y = variant (FV \<phi> \<union> FV (\<^bold>\<forall> x\<^bold>. \<xi>))\<close>
    then have pr_is2: \<open>prenex_right \<phi> \<psi> = \<^bold>\<forall>y\<^bold>. prenex_right \<phi> (\<xi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
      using \<open>qfree \<phi>\<close> 2(2) pr_is1  unfolding y_def by meson
    have \<open>is_prenex (\<xi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
      using prenex_formsubst1 2(2) by presburger
    then have p_xps: \<open>?P (\<xi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
      using less 2(1) less_Suc_eq plus_1_eq_Suc size.simps(4) size_indep_subst by presburger
    have \<open>is_prenex (prenex_right \<phi> \<psi>)\<close>
      using prenex_right_props_imp0 \<open>is_prenex \<psi>\<close> \<open>qfree \<phi>\<close> by blast
    moreover have \<open>FV (prenex_right \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>)\<close>
      using prenex_right_forall_FV[of \<phi> x \<xi>] by (metis 2(1) FV.simps(4) p_xps pr_is1 y_def)
    moreover have \<open>language {prenex_right \<phi> \<psi>} = language {\<phi> \<^bold>\<longrightarrow> \<psi>}\<close>
      using prenex_right_forall_language
      by (metis "2"(1) functions_form.simps(4) lang_singleton p_xps pr_is1 predicates_form.simps(4) y_def)
    moreover have \<open>(\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> prenex_right \<phi> \<psi> = I\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi>)\<close>
    proof clarsimp
      fix I :: "'a intrp" and \<beta>
      assume \<open>dom I \<noteq> {}\<close>
      then show \<open>I\<^bold>,\<beta> \<Turnstile> prenex_right \<phi> \<psi> = (I\<^bold>,\<beta> \<Turnstile> \<phi> \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>)\<close>
        using prenex_right_forall_is by (smt (verit, del_insts) 2(1) holds.simps(3) p_xps
            pr_is1 prenex_props_forall y_def)
    qed
    ultimately show ?thesis
      by blast
  next
    case (3 \<xi> x)
    have pr_is1:\<open>prenex_right \<phi> \<psi> = prenex_right_exists prenex_right \<phi> x \<xi>\<close>
      using 3 prenex_right_exist_case by blast
    define y where \<open>y = variant (FV \<phi> \<union> FV (\<^bold>\<exists> x\<^bold>. \<xi>))\<close>
    then have pr_is2: \<open>prenex_right \<phi> \<psi> = \<^bold>\<exists>y\<^bold>. prenex_right \<phi> (\<xi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
      using \<open>qfree \<phi>\<close> 3(2) pr_is1  unfolding y_def by meson
    have \<open>is_prenex (\<xi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
      using prenex_formsubst1 3(2) by presburger
    then have p_xps: \<open>?P (\<xi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
      using less 3(1) less_Suc_eq plus_1_eq_Suc size.simps size_indep_subst by simp
    have \<open>is_prenex (prenex_right \<phi> \<psi>)\<close>
      using prenex_right_props_imp0 \<open>is_prenex \<psi>\<close> \<open>qfree \<phi>\<close> by blast
    moreover have \<open>FV (prenex_right \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>)\<close>
      using prenex_right_exists_FV[of \<phi> x \<xi>] by (metis 3(1) FV.simps(4) FV_exists p_xps
          pr_is1 y_def)
    moreover have \<open>language {prenex_right \<phi> \<psi>} = language {\<phi> \<^bold>\<longrightarrow> \<psi>}\<close>
      using prenex_right_forall_language by (smt (verit) "3"(1) p_xps pr_is1 
          prenex_props_exists prenex_right_exists_language y_def)
    moreover have \<open>(\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> prenex_right \<phi> \<psi> = I\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi>)\<close>
      by (smt (verit, best) "3"(1) p_xps pr_is2 prenex_props_exists prenex_right_exists_is y_def)
    ultimately show ?thesis
      by blast
  qed
qed
    
lemma prenex_right_props: 
  \<open>qfree \<phi> \<and> is_prenex \<psi> \<Longrightarrow>
  is_prenex (prenex_right \<phi> \<psi>) \<and>
  FV (prenex_right \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
  language {prenex_right \<phi> \<psi>} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> ((I\<^bold>,\<beta> \<Turnstile> (prenex_right \<phi> \<psi>)) \<longleftrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> \<psi>))))\<close>
  using prenex_right_props_imp by meson


lemma prenex_left_props_imp0:
  assumes \<open>is_prenex \<psi>\<close>
  shows \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (prenex_left \<phi> \<psi>)\<close>
proof (induction \<phi> rule: measure_induct_rule [of size])
  case (less \<phi>)
  show ?case
  proof (cases rule: is_prenex.cases[OF \<open>is_prenex \<phi>\<close>])
    case (1 \<xi>)
    then show ?thesis
      using \<open>is_prenex \<phi>\<close> prenex_right_props prenex_left_qfree_case \<open>is_prenex \<psi>\<close> by presburger
  next
    case (2 \<xi> x)
    then have \<open>prenex_left \<phi> \<psi> = prenex_left_forall prenex_left \<xi> x \<psi>\<close>
      using prenex_left_forall_case by blast
    then show \<open>is_prenex (prenex_left \<phi> \<psi>)\<close>
      using less 2 by (metis is_prenex.intros(3) lessI plus_1_eq_Suc prenex_formsubst1 size.simps(4) size_indep_subst)
  next
    case (3 \<xi> x)
    then have \<open>\<exists>y \<sigma>. prenex_left \<phi> \<psi> = \<^bold>\<forall>y\<^bold>. prenex_left (\<xi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<psi>\<close>
      using prenex_left_exists_shape_case by presburger
    then obtain y \<sigma> where pr_is: \<open>prenex_left \<phi> \<psi> = \<^bold>\<forall>y\<^bold>. prenex_left (\<xi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<psi>\<close>
      by blast
    have size_xp: \<open>size (\<xi> \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<phi>\<close> 
      using 3(1) size_indep_subst by auto
    have \<open>is_prenex (\<xi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
      using 3(2) prenex_formsubst1 by blast
    then have \<open>is_prenex (prenex_left (\<xi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<psi>)\<close>
      using less size_xp by blast
    then show ?thesis
      using is_prenex.intros pr_is by presburger
  qed
qed

lemma prenex_left_props_imp:
  assumes \<open>is_prenex \<psi>\<close>
  shows \<open>is_prenex \<phi> \<Longrightarrow>
        is_prenex (prenex_left \<phi> \<psi>) \<and>
        FV (prenex_left \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
        (language {(prenex_left \<phi> \<psi>)} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)}) \<and>
        (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> prenex_left \<phi> \<psi> \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
    (is \<open>is_prenex \<phi> \<Longrightarrow> ?P \<phi>\<close>)
proof (induction \<phi> rule: measure_induct_rule [of size])
  case (less \<xi>)
  show ?case 
  proof (cases rule: is_prenex.cases[OF \<open>is_prenex \<xi>\<close>])
    case (1 \<xi>')
    then show ?thesis
      using prenex_right_qfree_case \<open>is_prenex \<psi>\<close> 
      by (simp add: prenex_left_qfree_case prenex_right_props)
  next
    case (2 \<xi>' x)
    have pr_is1:\<open>prenex_left \<xi> \<psi> = prenex_left_forall prenex_left \<xi>' x \<psi>\<close>
      using 2 prenex_left_forall_case by blast
    define y where \<open>y = variant (FV (\<^bold>\<forall>x\<^bold>. \<xi>') \<union> FV \<psi>)\<close>
    then have pr_is2: \<open>prenex_left \<xi> \<psi> = \<^bold>\<exists>y\<^bold>. prenex_left (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y)) \<psi>\<close>
      using \<open>is_prenex \<psi>\<close> 2(2) pr_is1  unfolding y_def by meson
    have \<open>is_prenex (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
      using prenex_formsubst1 2(2) by presburger
    then have p_xps: \<open>?P (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
      using less 2(1) less_Suc_eq plus_1_eq_Suc size.simps(4) size_indep_subst by presburger
    have \<open>is_prenex (prenex_left \<xi> \<psi>)\<close>
      using prenex_left_props_imp0 \<open>is_prenex \<xi>\<close> \<open>is_prenex \<psi>\<close> by blast
    moreover have \<open>FV (prenex_left \<xi> \<psi>) = FV (\<xi> \<^bold>\<longrightarrow> \<psi>)\<close>
      using prenex_left_forall_FV[of x \<xi>' \<psi>] by (metis 2(1) FV_exists p_xps pr_is1 y_def)
    moreover have \<open>language {prenex_left \<xi> \<psi>} = language {\<xi> \<^bold>\<longrightarrow> \<psi>}\<close>
      using prenex_left_forall_language 
      by (smt (verit, ccfv_threshold) 2(1) p_xps pr_is1 prenex_props_exists y_def)
    moreover have \<open>(\<And>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<Longrightarrow> I\<^bold>,\<beta> \<Turnstile> prenex_left \<xi> \<psi> = I\<^bold>,\<beta> \<Turnstile> \<xi> \<^bold>\<longrightarrow> \<psi>)\<close>
      by (metis "2"(1) holds_exists p_xps pr_is2 prenex_left_forall_is y_def)
    ultimately show \<open>?P \<xi>\<close>
      by blast
  next
    case (3 \<xi>' x)
    have pr_is1:\<open>prenex_left \<xi> \<psi> = prenex_left_exists prenex_left \<xi>' x \<psi>\<close>
      using 3 prenex_left_exists_case by blast
    define y where \<open>y = variant (FV (\<^bold>\<exists> x\<^bold>. \<xi>') \<union> FV \<psi>)\<close>
    then have pr_is2: \<open>prenex_left \<xi> \<psi> = \<^bold>\<forall>y\<^bold>. prenex_left (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y)) \<psi>\<close>
      using \<open>is_prenex \<psi>\<close> 3(2) pr_is1  unfolding y_def by meson
    have \<open>is_prenex (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
      using prenex_formsubst1 3(2) by presburger
    then have p_xps: \<open>?P (\<xi>' \<cdot>\<^sub>f\<^sub>m subst x (Var y))\<close>
      using less 3(1) less_Suc_eq plus_1_eq_Suc size.simps size_indep_subst by simp
    have \<open>is_prenex (prenex_left \<xi> \<psi>)\<close>
      using prenex_left_props_imp0 \<open>is_prenex \<xi>\<close> \<open>is_prenex \<psi>\<close> by blast
    moreover have \<open>FV (prenex_left \<xi> \<psi>) = FV (\<xi> \<^bold>\<longrightarrow> \<psi>)\<close>
      using prenex_left_exists_FV[of x \<xi>' \<psi>] by (metis 3(1) FV.simps(4) p_xps
          pr_is1 y_def)
    moreover have \<open>language {prenex_left \<xi> \<psi>} = language {\<xi> \<^bold>\<longrightarrow> \<psi>}\<close>
      using prenex_left_exists_language[of x \<xi>' \<psi>] 
      by (smt (verit) 3(1) p_xps pr_is2 prenex_props_forall y_def)
    moreover have \<open>(\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> 
        I\<^bold>,\<beta> \<Turnstile> prenex_left \<xi> \<psi> = I\<^bold>,\<beta> \<Turnstile> \<xi> \<^bold>\<longrightarrow> \<psi>)\<close>
      by (metis "3"(1) holds.simps(4) p_xps pr_is2 prenex_left_exists_is y_def)
    ultimately show \<open>?P \<xi>\<close>
      by blast
  qed
qed

lemma prenex_left_props: 
  \<open>is_prenex \<phi> \<and> is_prenex \<psi> \<Longrightarrow> 
        is_prenex (prenex_left \<phi> \<psi>) \<and>
        FV (prenex_left \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
        (language {(prenex_left \<phi> \<psi>)} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)}) \<and>
        (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> prenex_left \<phi> \<psi> \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
  using prenex_left_props_imp by meson

theorem prenex_props: \<open>is_prenex (prenex \<phi>) \<and> (FV (prenex \<phi>) = FV \<phi>) \<and> 
  (language {prenex \<phi>} = language {\<phi>}) \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>, \<beta> \<Turnstile> (prenex \<phi>)) \<longleftrightarrow> (I\<^bold>, \<beta> \<Turnstile> \<phi>))\<close>
proof (induction \<phi> rule: form.induct)
  case Bot
  then show ?case
    by (metis is_prenex.simps prenex.simps(1) qfree.simps(1))
next
  case (Atom p ts)
  then show ?case
    using is_prenex.intros(1) prenex.simps(2) qfree.simps(2) by presburger
next
  case (Implies \<phi> \<psi>)
  have \<open>is_prenex (prenex (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
    using Implies prenex_left_props prenex.simps(3) by presburger
  moreover have \<open>FV (prenex (\<phi> \<^bold>\<longrightarrow> \<psi>)) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>)\<close>
    using Implies prenex_left_props prenex.simps(3) FV.simps(3) by presburger
  moreover have \<open>language {prenex (\<phi> \<^bold>\<longrightarrow> \<psi>)} = language {\<phi> \<^bold>\<longrightarrow> \<psi>}\<close>
    using Implies prenex_left_props prenex.simps(3) lang_singleton 
      functions_form.simps(3) predicates_form.simps(3) by (metis prod.inject)
  moreover have \<open>\<forall>(I::'a intrp) \<beta>. FOL_Semantics.dom I \<noteq> {} \<longrightarrow>
    I\<^bold>,\<beta> \<Turnstile> prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) = I\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi>\<close>
    using Implies prenex_left_props holds.simps(3) prenex.simps(3) by metis
  ultimately show ?case by blast
next
  case (Forall x \<phi>)
  have \<open>is_prenex (prenex (\<^bold>\<forall>x\<^bold>. \<phi>))\<close>
    using Forall using is_prenex.intros(2) prenex.simps(4) by presburger
  moreover have fv_indep_prenex: \<open>FV (prenex (\<^bold>\<forall>x\<^bold>. \<phi>)) = FV (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>
    using Forall FV.simps(4) prenex.simps(4) by presburger
  moreover have \<open>language {prenex (\<^bold>\<forall>x\<^bold>. \<phi>)} = language {\<^bold>\<forall>x\<^bold>. \<phi>}\<close>
    using Forall prenex.simps(4) functions_form.simps(4) predicates_form.simps(4)
    unfolding language_def functions_forms_def predicates_def by simp
  moreover have \<open>(\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> I\<^bold>,\<beta> \<Turnstile> prenex (\<^bold>\<forall>x\<^bold>. \<phi>) = I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>))\<close>
    using Forall holds.simps(4) by simp
  ultimately show ?case by blast
qed

corollary is_prenex_prenex [simp]: \<open>is_prenex (prenex \<phi>)\<close> 
  and FV_prenex [simp]: \<open>FV (prenex \<phi>) = FV \<phi>\<close>
  and language_prenex [simp]: \<open>language {prenex \<phi>} = language {\<phi>}\<close>
  by (auto simp: prenex_props)

corollary prenex_holds [simp]: \<open>dom I \<noteq> {} \<Longrightarrow> (I\<^bold>,\<beta> \<Turnstile> (prenex \<phi>)) \<longleftrightarrow> (I\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>
  by (simp add: prenex_props)

lemma prenex_satisfies [simp]:
  assumes "dom M \<noteq> {}" 
  shows "satisfies M {prenex \<phi>} \<longleftrightarrow> satisfies M {\<phi>}"
  using assms prenex_holds by (fastforce simp: satisfies_def)

end
