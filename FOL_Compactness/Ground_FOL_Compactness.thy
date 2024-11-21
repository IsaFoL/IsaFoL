(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023 *)

theory Ground_FOL_Compactness  
imports
    FOL_Semantics
begin


fun qfree :: \<open>form \<Rightarrow> bool\<close> where
  \<open>qfree \<^bold>\<bottom> = True\<close>
| \<open>qfree (Atom p ts) = True\<close>
| \<open>qfree (\<phi> \<^bold>\<longrightarrow> \<psi>) = (qfree \<phi> \<and> qfree \<psi>)\<close>
| \<open>qfree (\<^bold>\<forall> x\<^bold>. \<phi>) = False\<close>

lemma qfree_iff_BV_empty: "qfree \<phi> \<longleftrightarrow> BV \<phi> = {}"
  by (induction \<phi>) auto

lemma qfree_no_quantif: \<open>qfree r \<Longrightarrow> \<not>(\<exists>x p. r = \<^bold>\<forall>x\<^bold>. p) \<and> \<not>(\<exists>x p. r = \<^bold>\<exists>x\<^bold>. p)\<close>
  using qfree.simps(3) qfree.simps(4) by blast

lemma qfree_formsubst: \<open>qfree \<phi> \<equiv> qfree (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
proof (induction \<phi>)
  case (Forall x \<phi>)
  then show ?case 
    using formsubst_def_switch by (metis (no_types, lifting) formsubst.simps(4) qfree_no_quantif)
qed simp+

(* typedef qfree_form = \<open>{\<phi>::form. qfree \<phi>}\<close>
  using qfree.simps(1) by blast 

setup_lifting type_definition_qfree_form *)

(* != propositional compactness is not proved as in Harrison.
      Instead the existing AFP entry is reused *)

fun form_to_formula :: "form \<Rightarrow> (nat\<times>nterm list) formula" where
  \<open>form_to_formula \<^bold>\<bottom> = \<bottom>\<close>
| \<open>form_to_formula (Atom p ts) = formula.Atom (p,ts)\<close>
| \<open>form_to_formula (\<phi> \<^bold>\<longrightarrow> \<psi>) = Imp (form_to_formula \<phi>) (form_to_formula \<psi>)\<close>
| \<open>form_to_formula (\<^bold>\<forall> x\<^bold>. \<phi>) = \<bottom>\<close>

fun pholds :: \<open>(form \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool\<close> (\<open>_ \<Turnstile>\<^sub>p _\<close> [30, 80] 80) where
  \<open>I \<Turnstile>\<^sub>p \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>I \<Turnstile>\<^sub>p Atom p ts \<longleftrightarrow> I (Atom p ts)\<close>
| \<open>I \<Turnstile>\<^sub>p \<phi> \<^bold>\<longrightarrow> \<psi> \<longleftrightarrow> ((I \<Turnstile>\<^sub>p \<phi>) \<longrightarrow> (I \<Turnstile>\<^sub>p \<psi>))\<close>
| \<open>I \<Turnstile>\<^sub>p (\<^bold>\<forall> x\<^bold>. \<phi>) \<longleftrightarrow> I (\<^bold>\<forall> x\<^bold>. \<phi>)\<close>

definition psatisfiable :: "form set \<Rightarrow> bool" where
  \<open>psatisfiable S \<equiv> \<exists>I. \<forall>\<phi>\<in>S. I \<Turnstile>\<^sub>p \<phi>\<close>

abbreviation psatisfies where \<open>psatisfies I \<Phi> \<equiv> \<forall>\<phi>\<in>\<Phi>. pholds I \<phi>\<close>

definition val_to_prop_val :: "(form \<Rightarrow> bool) \<Rightarrow> ((nat \<times> nterm list) \<Rightarrow> bool)" where
  \<open>val_to_prop_val I = (\<lambda>x. I (Atom (fst x) (snd x)))\<close>

lemma pentails_equiv: \<open>qfree \<phi> \<Longrightarrow> (I \<Turnstile>\<^sub>p \<phi> \<equiv> (val_to_prop_val I) \<Turnstile> (form_to_formula \<phi>))\<close>
proof (induction \<phi>)
  case Bot
  then show ?case
    unfolding val_to_prop_val_def by simp
next
  case (Atom x1 x2)
  then show ?case
    unfolding val_to_prop_val_def by simp
next
  case (Implies \<phi>1 \<phi>2)
  then have \<open>qfree \<phi>1\<close> and \<open>qfree \<phi>2\<close> by simp+
  then have \<open>I \<Turnstile>\<^sub>p \<phi>1 = val_to_prop_val I \<Turnstile> form_to_formula \<phi>1\<close> and
            \<open>I \<Turnstile>\<^sub>p \<phi>2 = val_to_prop_val I \<Turnstile> form_to_formula \<phi>2\<close>
    using Implies(1) Implies(2) by simp+
  then show ?case by simp
next
  case (Forall x1 \<phi>)
  then have False by simp
  then show ?case by simp
qed

lemma pentails_equiv_set:
  assumes all_qfree: \<open>\<forall>\<phi>\<in>S. qfree \<phi>\<close>
  shows \<open>psatisfiable S \<equiv> sat (form_to_formula ` S)\<close>
proof -
  {
    assume psat_s: \<open>psatisfiable S\<close>
    then obtain I where I_is: \<open>\<forall>\<phi>\<in>S. I \<Turnstile>\<^sub>p \<phi>\<close>
      unfolding psatisfiable_def by blast
    define \<A> where \<open>\<A> = val_to_prop_val I\<close>
    then have \<open>\<forall>\<phi>\<in>S. \<A> \<Turnstile> (form_to_formula \<phi>)\<close>
      using pentails_equiv all_qfree I_is by blast
    then have \<open>sat (form_to_formula ` S)\<close>
      unfolding sat_def by blast
  }
  moreover {
    assume \<open>sat (form_to_formula ` S)\<close>
    then obtain \<A> where a_is: \<open>\<forall>\<phi>\<in>S. \<A> \<Turnstile> form_to_formula \<phi>\<close>
      by (meson image_eqI sat_def)
    define I where i_is: \<open>I = (\<lambda>x. \<A> (pred x, args x))\<close>
    then have \<open>\<A> = val_to_prop_val I\<close>
      unfolding val_to_prop_val_def by simp
    then have \<open>\<forall>\<phi>\<in>S. I \<Turnstile>\<^sub>p \<phi>\<close>
      using pentails_equiv all_qfree a_is by blast
    then have \<open>psatisfiable S\<close>
      unfolding psatisfiable_def by auto
  }
  ultimately show \<open>psatisfiable S \<equiv> sat (form_to_formula ` S)\<close>
    by argo
qed

definition finsat :: "form set \<Rightarrow> bool" where
  \<open>finsat S \<equiv> \<forall>T\<subseteq>S. finite T \<longrightarrow> psatisfiable T\<close>

lemma finsat_fin_sat_eq:
  assumes all_qfree: \<open>\<forall>\<phi>\<in>S. qfree \<phi>\<close>
  shows \<open>finsat S \<equiv> fin_sat (form_to_formula ` S)\<close>
proof -
  {
    assume finsat_s: \<open>finsat S\<close>
    have \<open>fin_sat (form_to_formula ` S)\<close>
      unfolding fin_sat_def
    proof clarsimp
      fix s
      assume 
        s_in: \<open>s \<subseteq> form_to_formula ` S\<close> and
        fin_s: \<open>finite s\<close>
      then obtain t where \<open>t \<subseteq> S\<close> and \<open>s = form_to_formula ` t\<close> and \<open>finite t\<close>
        by (meson finite_subset_image)
      then show \<open>sat s\<close>
        using pentails_equiv_set[of t] all_qfree by (meson finsat_s finsat_def subsetD)
      qed
  }
  moreover
  {
    assume fin_sat_s: \<open>fin_sat (form_to_formula ` S)\<close>
    have \<open>finsat S\<close>
      unfolding finsat_def
    proof clarsimp
      fix T
      assume
        \<open>T \<subseteq> S\<close> and
        \<open>finite T\<close>
      then show \<open>psatisfiable T\<close>
        using pentails_equiv_set fin_sat_s unfolding fin_sat_def
        by (meson assms finite_imageI image_mono subset_iff)
    qed
  }
  ultimately show \<open>finsat S \<equiv> fin_sat (form_to_formula ` S)\<close>
    by argo
qed

lemma psatisfiable_mono: \<open>psatisfiable S  \<Longrightarrow> T \<subseteq> S \<Longrightarrow> psatisfiable T\<close>
  unfolding psatisfiable_def by blast

lemma finsat_mono: \<open>finsat S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> finsat T\<close>
  unfolding finsat_def by blast

lemma finsat_satisfiable: \<open>psatisfiable S \<Longrightarrow> finsat S\<close>
  unfolding psatisfiable_def finsat_def by blast

lemma prop_compactness: \<open>(\<forall>\<phi> \<in> S. qfree \<phi>) \<Longrightarrow> finsat S = psatisfiable S\<close>
proof -
  assume all_qfree: \<open>\<forall>\<phi> \<in> S. qfree \<phi>\<close>
  have \<open>finsat S = fin_sat (form_to_formula ` S)\<close>
    using finsat_fin_sat_eq[OF all_qfree] by simp
  also have \<open>... = sat (form_to_formula ` S)\<close>
    using compactness[of "form_to_formula ` S"] by argo
      (* for this step, countability of formula and term was critical!!!*)
  also have \<open>... = psatisfiable S\<close>
    using pentails_equiv_set[OF all_qfree] by simp
  finally show \<open>finsat S = psatisfiable S\<close>
    . 
qed

end