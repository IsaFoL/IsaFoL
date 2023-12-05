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

inductive universal :: "form \<Rightarrow> bool" where
  \<open>qfree \<phi> \<Longrightarrow> universal \<phi>\<close>
| \<open>universal \<phi> \<Longrightarrow> universal (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>

fun size :: "form \<Rightarrow> nat" where
  \<open>size \<^bold>\<bottom> = 1\<close>
| \<open>size (Atom p ts) = 1\<close>
| \<open>size (\<phi> \<^bold>\<longrightarrow> \<psi>) = size \<phi> + size \<psi>\<close>
| \<open>size (\<^bold>\<forall> x\<^bold>. \<phi>) = 1 + size \<phi>\<close>

lemma wf_size: \<open>wfP (\<lambda>\<phi> \<psi>. size \<phi> < size \<psi>)\<close>
  by (simp add: wfP_if_convertible_to_nat)

(*
instantiation form :: wellorder
begin

definition less_eq_form where less_eq_size: \<open>\<phi> \<le> \<psi> \<longleftrightarrow> (size \<phi> = size \<psi>) \<or> (size \<phi> < size \<psi>)\<close>

definition less_form where less_size: \<open>\<phi> < \<psi> \<longleftrightarrow> size \<phi> < size \<psi>\<close>

instance
proof
  fix \<phi> \<psi>::form
  show \<open>(\<phi> < \<psi>) = (\<phi> \<le> \<psi> \<and> \<not> \<psi> \<le> \<phi>)\<close>
    using less_eq_size less_size by presburger
next
  fix \<phi>::form
  show \<open>\<phi> \<le> \<phi>\<close> 
    using less_eq_size by simp
next
  fix \<phi> \<psi> \<xi>::form
  show \<open>\<phi> \<le> \<psi> \<Longrightarrow> \<psi> \<le> \<xi> \<Longrightarrow> \<phi> \<le> \<xi>\<close>
    using less_eq_size by auto
next
  fix \<phi> \<psi>::form
  show \<open>\<phi> \<le> \<psi> \<Longrightarrow> \<psi> \<le> \<phi> \<Longrightarrow> \<phi> = \<psi>\<close>
(* not true! ! ! *)
    oops
end
*)

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

(*
inductive to_prenex to_prenex_left to_prenex_right where
  \<open>to_prenex \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>to_prenex (Atom p ts) = Atom p ts\<close>
| \<open>to_prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) = to_prenex_left (to_prenex \<phi>) (to_prenex \<psi>)\<close>
| \<open>to_prenex (\<^bold>\<forall>x\<^bold>. \<phi>) = \<^bold>\<forall>x\<^bold>. (to_prenex \<phi>)\<close>
| \<open>to_prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = \<^bold>\<forall>x\<^bold>. (to_prenex_left \<phi> \<psi>)\<close> (*TODO: just a test, to correct *)
| \<open>to_prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = \<^bold>\<exists>x\<^bold>. (to_prenex_right \<phi> \<psi>)\<close>
| \<open>qfree \<phi> \<Longrightarrow> to_prenex_left \<phi> \<psi> = \<phi> \<^bold>\<longrightarrow> \<psi>\<close>
| \<open>to_prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = \<^bold>\<forall>x\<^bold>. (to_prenex_right \<phi> \<psi>)\<close>
*)
(*   let y = VARIANT(FV(p) UNION FV(!!x q)) in
                   !!y (Prenex_right p (formsubst (valmod (x,V y) V) q)))  *)

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

(*
lemma ppat_to_ex_qfree_rec:
  assumes
    \<open>\<exists>(g :: form \<Rightarrow> form). \<forall>p q. g q = ppat (A g p) (B g p) (C p) q\<close>
  shows
    \<open>(\<exists>f. (\<forall>x p q. f p (\<^bold>\<forall>x\<^bold>. q) = A (f p) p x q) \<and>
      (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = B (f p) p x q) \<and> 
      (\<forall>p q. qfree q \<longrightarrow> f p q = C p q))\<close>
  using assms ppat_last_qfree
sorry


lemma ppat_to_ex_qfree_rec2:
  assumes
    \<open>\<forall>(p :: form). \<exists>g. \<forall>q. g q = ppat (A p g) (B p g) (C p) q\<close>
  shows
    \<open>(\<exists>f. (\<forall>x p q. f p (\<^bold>\<forall>x\<^bold>. q) = (A p (f p) x q)) \<and>
      (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = B p (f p) x q) \<and> 
      (\<forall>p q. qfree q \<longrightarrow> f p q = C p q))\<close>
sorry
*)

thm wf_induct

lemma "wfP ((<) :: (nat \<Rightarrow> nat \<Rightarrow> bool))"
  using wfP_less .

thm wfP_less

(*(!f g x. (!z. z << x ==> (f z = g z) /\ S z (f z))
                      ==> (H f x = H g x) /\ S x (H f x))
             ==> ?f:A->B. !x. (f x = H f x)`, *)

(*
WF_EQ = prove
 (`WF(<<) <=> !P:A->bool. (?x. P(x)) <=> (?x. P(x) /\ !y. y << x ==> ~P(y))`
*)

lemma wfP_eq: \<open>wfP ((<) :: ('a::ord \<Rightarrow> 'a \<Rightarrow> bool)) \<Longrightarrow> ((\<exists>(x::'a). P x) \<equiv> (\<exists>x. P x \<and> (\<forall>y. y < x \<longrightarrow> \<not>P y)))\<close>
  by (smt (verit) mem_Collect_eq wfP_eq_minimal)

(*
WF_IND = prove
 (`WF(<<) <=> !P:A->bool. (!x. (!y. y << x ==> P(y)) ==> P(x)) ==> !x. P(x)`,
*)
lemma wfP_ind: \<open>wfP ((<) :: ('a::ord \<Rightarrow> 'a \<Rightarrow> bool)) \<Longrightarrow>
  (\<forall>(x::'a). (\<forall>y. y <  x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x. P x)\<close>
  by (metis wfP_induct)

lemma dependent_wfP_choice:
  fixes P :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "wfP R"
    and adm: "\<And>f g x r. (\<And>z. R z x \<Longrightarrow> f z = g z) \<Longrightarrow> P f x r = P g x r"
    and P: "\<And>x f. (\<And>y. R y x \<Longrightarrow> P f y (f y)) \<Longrightarrow> \<exists>r. P f x r"
  shows "\<exists>f. \<forall>x. P f x (f x)"
proof -
  have wf_R: \<open>wf {(x,y). R x y}\<close> using assms(1) unfolding wfP_def .
  have eq_P: \<open>(\<forall>z. (z, x) \<in> {(x, y). R x y} \<longrightarrow> f z = g z) \<Longrightarrow> P f x r = P g x r\<close> for f g x r
    using assms(2) by blast
  have ex_P: \<open>(\<forall>y. (y, x) \<in> {(x, y). R x y} \<longrightarrow> P f y (f y)) \<Longrightarrow> \<exists>r. P f x r\<close> for x f
    using assms(3) by blast
  show \<open>\<exists>f. \<forall>x. P f x (f x)\<close>
    using dependent_wf_choice[of "{(x,y). R x y}" P, OF wf_R] eq_P ex_P by blast
qed

lemma dependent_wfP_choice2:
  fixes P :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes "wfP R"
    and adm: "\<And>f g x r. (\<And>z. R z x \<Longrightarrow> f z = g z) \<Longrightarrow> P f x = P g x"
  shows "\<exists>f. \<forall>x. P f x = (f x)"
proof -
  have adm_rel: \<open>(\<forall>z. R z x \<longrightarrow> f z = g z) \<Longrightarrow> (P f x = r) = (P g x = r)\<close> for f g x r
    using adm by fastforce
  have P_rel: \<open>(\<forall>y. R y x \<longrightarrow> P f y = (f y)) \<Longrightarrow> \<exists>r. P f x = r\<close> for x f
    by simp
  show "\<exists>f. \<forall>x. P f x = (f x)"
    using dependent_wfP_choice[of R \<open>\<lambda>f x r. P f x = r\<close>] assms(1) adm_rel P_rel by blast
qed

lemma size_rec: 
  \<open>\<forall>f g x. (\<forall>(z::form). size z < size x \<longrightarrow> (f z = g z)) \<longrightarrow> (H f x = H g x) \<Longrightarrow> (\<exists>f. \<forall>x. f x = H f x)\<close>
  using dependent_wfP_choice2[OF wf_size] by metis

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

 (* is it unique? \<rightarrow> No, it is undefined in the last case if \<not>qfree \<phi>. Use SOME  *)
definition prenex_right where "prenex_right = (SOME prenex_right.
  (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>) \<and>
  (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>) \<and>
  (\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>)))"

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

fun prenex where
  \<open>prenex \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>prenex (Atom p ts) = Atom p ts\<close>
| \<open>prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) = prenex_left (prenex \<phi>) (prenex \<psi>)\<close>
| \<open>prenex (\<^bold>\<forall>x\<^bold>. \<phi>) = \<^bold>\<forall>x\<^bold>. (prenex \<phi>)\<close>

theorem \<open>is_prenex (prenex \<phi>) \<and> (FV (prenex \<phi>) = FV \<phi>) \<and> (language {prenex \<phi>} = language {\<phi>}) \<and>
  (\<forall>I \<beta>. \<not>(dom I = {}) \<longrightarrow> (I, \<beta> \<Turnstile> (prenex \<phi>)) \<longleftrightarrow> (I, \<beta> \<Turnstile> \<phi>))\<close>
proof (induction \<phi> rule: form.induct)
  case Bot
  then show ?case
    by (metis is_prenex.simps prenex.simps(1) qfree.simps(1))
next
  case (Atom x1 x2)
  then show ?case
    using is_prenex.intros(1) prenex.simps(2) qfree.simps(2) by presburger
next
  case (Implies x1 x2)
  then show ?case sorry
next
  case (Forall x1 x2)
  have \<open>is_prenex (prenex (\<^bold>\<forall> x1\<^bold>. x2))\<close>
    using Forall using is_prenex.intros(2) prenex.simps(4) by presburger
  moreover have \<open>FV (prenex (\<^bold>\<forall> x1\<^bold>. x2)) = FV (\<^bold>\<forall> x1\<^bold>. x2)\<close>
    using Forall FV.simps(4) prenex.simps(4) by presburger
  moreover have \<open>language {prenex (\<^bold>\<forall> x1\<^bold>. x2)} = language {\<^bold>\<forall> x1\<^bold>. x2}\<close>
    using Forall
    sorry
  moreover have \<open>(\<forall>I \<beta>. Harrison_FOL_Compactness.dom I \<noteq> {} \<longrightarrow>
    I,\<beta> \<Turnstile> prenex (\<^bold>\<forall> x1\<^bold>. x2) = I,\<beta> \<Turnstile> (\<^bold>\<forall> x1\<^bold>. x2))\<close>
    using Forall
    sorry
  then show ?case
    sorry
qed


end