theory Prop_Normalisation
imports Entailment_Definition.Prop_Logic Prop_Abstract_Transformation Nested_Multisets_Ordinals.Multiset_More
begin

text \<open>Given the previous definition about abstract rewriting and theorem about them, we now have the
  detailed rule making the transformation into CNF/DNF.\<close>

section \<open>Rewrite Rules\<close>
text \<open>The idea of Christoph Weidenbach's book is to remove gradually the operators: first
  equivalencies, then implication, after that the unused true/false and finally the reorganizing the
  or/and.  We will prove each transformation seperately.\<close>


subsection \<open>Elimination of the Equivalences\<close>

text \<open>The first transformation consists in removing every equivalence symbol.\<close>
inductive elim_equiv :: "'v propo \<Rightarrow> 'v propo \<Rightarrow> bool" where
elim_equiv[simp]: "elim_equiv (FEq \<phi> \<psi>) (FAnd (FImp \<phi> \<psi>)  (FImp \<psi> \<phi>))"

lemma elim_equiv_transformation_consistent:
"A \<Turnstile> FEq \<phi> \<psi> \<longleftrightarrow> A \<Turnstile> FAnd (FImp \<phi> \<psi>) (FImp \<psi> \<phi>)"
  by auto

lemma elim_equiv_explicit: "elim_equiv \<phi> \<psi> \<Longrightarrow> \<forall>A. A \<Turnstile> \<phi> \<longleftrightarrow> A \<Turnstile> \<psi>"
  by (induct rule: elim_equiv.induct, auto)

lemma elim_equiv_consistent: "preserve_models elim_equiv"
  unfolding preserve_models_def by (simp add: elim_equiv_explicit)

lemma elimEquv_lifted_consistant:
  "preserve_models (full (propo_rew_step elim_equiv))"
  by (simp add: elim_equiv_consistent)


text \<open>This function ensures that there is no equivalencies left in the formula tested by
  @{term no_equiv_symb}.\<close>
fun no_equiv_symb :: "'v propo \<Rightarrow> bool" where
"no_equiv_symb (FEq _ _) = False" |
"no_equiv_symb _ = True"


text \<open>Given the definition of @{term no_equiv_symb}, it does not depend on the formula, but only on
  the connective used.\<close>
lemma no_equiv_symb_conn_characterization[simp]:
  fixes c :: "'v connective" and l :: "'v propo list"
  assumes wf: "wf_conn c l"
  shows "no_equiv_symb (conn c l) \<longleftrightarrow> c \<noteq> CEq"
    by (metis connective.distinct(13,25,35,43) wf no_equiv_symb.elims(3) no_equiv_symb.simps(1)
      wf_conn.cases wf_conn_list(6))

definition no_equiv where "no_equiv = all_subformula_st no_equiv_symb"

lemma no_equiv_eq[simp]:
  fixes \<phi> \<psi> :: "'v propo"
  shows
    "\<not>no_equiv (FEq \<phi> \<psi>)"
    "no_equiv FT"
    "no_equiv FF"
  using no_equiv_symb.simps(1) all_subformula_st_test_symb_true_phi unfolding no_equiv_def by auto

text \<open>The following lemma helps to reconstruct @{term no_equiv} expressions: this representation is
  easier to use than the set definition.\<close>


lemma all_subformula_st_decomp_explicit_no_equiv[iff]:
fixes \<phi> \<psi> :: "'v propo"
shows
  "no_equiv (FNot \<phi>) \<longleftrightarrow> no_equiv \<phi>"
  "no_equiv (FAnd \<phi> \<psi>) \<longleftrightarrow> (no_equiv \<phi> \<and> no_equiv \<psi>)"
  "no_equiv (FOr \<phi> \<psi>) \<longleftrightarrow> (no_equiv \<phi> \<and> no_equiv \<psi>)"
  "no_equiv (FImp \<phi> \<psi>) \<longleftrightarrow> (no_equiv \<phi> \<and> no_equiv \<psi>)"
  by (auto simp: no_equiv_def)

text \<open>A theorem to show the link between the rewrite relation @{term elim_equiv} and the function
  @{term no_equiv_symb}. This theorem is one of the assumption we need to characterize the
  transformation.\<close>
lemma no_equiv_elim_equiv_step:
  fixes \<phi> :: "'v propo"
  assumes no_equiv: "\<not> no_equiv \<phi>"
  shows "\<exists>\<psi> \<psi>'. \<psi> \<preceq> \<phi> \<and> elim_equiv \<psi> \<psi>'"
proof -
  have test_symb_false_nullary:
    "\<forall>x::'v. no_equiv_symb FF \<and> no_equiv_symb FT \<and> no_equiv_symb (FVar x)"
    unfolding no_equiv_def by auto
  moreover {
    fix c:: "'v connective" and l :: "'v propo list" and \<psi> :: "'v propo"
      assume a1: "elim_equiv (conn c l) \<psi>"
      have "\<And>p pa. \<not> elim_equiv (p::'v propo) pa \<or> \<not> no_equiv_symb p"
        using elim_equiv.cases no_equiv_symb.simps(1) by blast
      then have "elim_equiv (conn c l) \<psi> \<Longrightarrow> \<not>no_equiv_symb (conn c l) " using a1 by metis
  }
  moreover have H': "\<forall>\<psi>. \<not>elim_equiv FT \<psi>" "\<forall>\<psi>. \<not>elim_equiv FF \<psi>" "\<forall>\<psi> x. \<not>elim_equiv (FVar x) \<psi>"
    using elim_equiv.cases by auto
  moreover have "\<And>\<phi>. \<not> no_equiv_symb \<phi> \<Longrightarrow> \<exists>\<psi>. elim_equiv \<phi> \<psi>"
    by (case_tac \<phi>, auto simp: elim_equiv.simps)
  then have "\<And>\<phi>'. \<phi>' \<preceq> \<phi> \<Longrightarrow> \<not>no_equiv_symb \<phi>' \<Longrightarrow>  \<exists>\<psi>. elim_equiv \<phi>' \<psi>" by force
  ultimately show ?thesis
    using no_test_symb_step_exists no_equiv test_symb_false_nullary unfolding no_equiv_def by blast
qed

text \<open>Given all the previous theorem and the characterization, once we have rewritten everything,
  there is no equivalence symbol any more.\<close>
lemma no_equiv_full_propo_rew_step_elim_equiv:
  "full (propo_rew_step elim_equiv) \<phi> \<psi> \<Longrightarrow> no_equiv \<psi>"
  using full_propo_rew_step_subformula no_equiv_elim_equiv_step by blast


subsection \<open>Eliminate Implication\<close>

text \<open>After that, we can eliminate the implication symbols.\<close>
inductive elim_imp :: "'v propo \<Rightarrow> 'v propo \<Rightarrow> bool" where
[simp]: "elim_imp (FImp \<phi> \<psi>) (FOr (FNot \<phi>) \<psi>)"

lemma elim_imp_transformation_consistent:
  "A \<Turnstile> FImp \<phi> \<psi> \<longleftrightarrow> A \<Turnstile> FOr (FNot \<phi>) \<psi>"
  by auto

lemma elim_imp_explicit: "elim_imp \<phi> \<psi> \<Longrightarrow> \<forall>A. A \<Turnstile> \<phi> \<longleftrightarrow> A \<Turnstile> \<psi>"
  by (induct \<phi> \<psi> rule: elim_imp.induct, auto)

lemma elim_imp_consistent: "preserve_models elim_imp"
  unfolding preserve_models_def by (simp add: elim_imp_explicit)

lemma elim_imp_lifted_consistant:
  "preserve_models (full (propo_rew_step elim_imp))"
  by (simp add: elim_imp_consistent)

fun no_imp_symb where
"no_imp_symb (FImp _ _) = False" |
"no_imp_symb _ = True"

lemma no_imp_symb_conn_characterization:
  "wf_conn c l \<Longrightarrow> no_imp_symb (conn c l) \<longleftrightarrow> c \<noteq> CImp"
  by (induction rule: wf_conn_induct) auto

definition no_imp where "no_imp \<equiv> all_subformula_st no_imp_symb"
declare no_imp_def[simp]

lemma no_imp_Imp[simp]:
  "\<not>no_imp (FImp \<phi> \<psi>)"
  "no_imp FT"
  "no_imp FF"
  unfolding no_imp_def by auto

lemma all_subformula_st_decomp_explicit_imp[simp]:
  fixes \<phi> \<psi> :: "'v propo"
  shows
    "no_imp (FNot \<phi>) \<longleftrightarrow> no_imp \<phi>"
    "no_imp (FAnd \<phi> \<psi>) \<longleftrightarrow> (no_imp \<phi> \<and> no_imp \<psi>)"
    "no_imp (FOr \<phi> \<psi>) \<longleftrightarrow> (no_imp \<phi> \<and> no_imp \<psi>)"
  by auto


text \<open>Invariant of the @{term elim_imp} transformation\<close>
lemma elim_imp_no_equiv:
  "elim_imp \<phi> \<psi> \<Longrightarrow> no_equiv \<phi> \<Longrightarrow>  no_equiv \<psi>"
  by (induct \<phi> \<psi> rule: elim_imp.induct, auto)

lemma elim_imp_inv:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "full (propo_rew_step elim_imp) \<phi> \<psi>" and "no_equiv \<phi>"
  shows "no_equiv \<psi>"
  using full_propo_rew_step_inv_stay_conn[of elim_imp no_equiv_symb \<phi> \<psi>] assms elim_imp_no_equiv
    no_equiv_symb_conn_characterization unfolding no_equiv_def by metis

lemma no_no_imp_elim_imp_step_exists:
  fixes \<phi> :: "'v propo"
  assumes no_equiv: "\<not> no_imp \<phi>"
  shows "\<exists>\<psi> \<psi>'. \<psi> \<preceq> \<phi> \<and> elim_imp \<psi> \<psi>'"
proof -
  have test_symb_false_nullary: "\<forall>x. no_imp_symb FF \<and> no_imp_symb FT \<and> no_imp_symb (FVar (x:: 'v))"
    by auto
  moreover {
     fix c:: "'v connective" and l :: "'v propo list" and \<psi> :: "'v propo"
     have H: "elim_imp (conn c l) \<psi> \<Longrightarrow> \<not>no_imp_symb (conn c l)"
       by (auto elim: elim_imp.cases)
    }
  moreover
    have H': "\<forall>\<psi>. \<not>elim_imp FT \<psi>" "\<forall>\<psi>. \<not>elim_imp FF \<psi>" "\<forall>\<psi> x. \<not>elim_imp (FVar x) \<psi>"
      by (auto elim: elim_imp.cases)+
  moreover
    have "\<And>\<phi>. \<not> no_imp_symb \<phi> \<Longrightarrow> \<exists>\<psi>. elim_imp \<phi> \<psi>"
      by (case_tac \<phi>) (force simp: elim_imp.simps)+
    then have "\<And>\<phi>'. \<phi>' \<preceq> \<phi> \<Longrightarrow> \<not>no_imp_symb \<phi>' \<Longrightarrow>  \<exists> \<psi>. elim_imp \<phi>' \<psi>" by force
  ultimately show ?thesis
    using no_test_symb_step_exists no_equiv test_symb_false_nullary unfolding no_imp_def by blast
qed

lemma no_imp_full_propo_rew_step_elim_imp: "full (propo_rew_step elim_imp) \<phi> \<psi> \<Longrightarrow> no_imp \<psi>"
  using full_propo_rew_step_subformula no_no_imp_elim_imp_step_exists by blast


subsection "Eliminate all the True and False in the formula"
text \<open>Contrary to the book, we have to give the transformation and the ``commutative''
  transformation. The latter is implicit in the book.\<close>
inductive elimTB where
ElimTB1: "elimTB (FAnd \<phi> FT) \<phi>" |
ElimTB1': "elimTB (FAnd FT \<phi>) \<phi>" |

ElimTB2: "elimTB (FAnd \<phi> FF) FF" |
ElimTB2': "elimTB (FAnd FF \<phi>) FF" |

ElimTB3: "elimTB (FOr \<phi> FT) FT" |
ElimTB3': "elimTB (FOr FT \<phi>) FT" |

ElimTB4: "elimTB (FOr \<phi> FF) \<phi>" |
ElimTB4': "elimTB (FOr FF \<phi>) \<phi>" |

ElimTB5: "elimTB (FNot FT) FF" |
ElimTB6: "elimTB (FNot FF) FT"


lemma elimTB_consistent: "preserve_models elimTB"
proof -
  {
    fix \<phi> \<psi>:: "'b propo"
    have "elimTB \<phi> \<psi> \<Longrightarrow> \<forall>A. A \<Turnstile> \<phi> \<longleftrightarrow> A \<Turnstile> \<psi>" by (induction rule: elimTB.inducts) auto
  }
  then show ?thesis using preserve_models_def by auto
qed

inductive no_T_F_symb :: "'v propo \<Rightarrow> bool" where
no_T_F_symb_comp: "c \<noteq> CF \<Longrightarrow> c \<noteq> CT \<Longrightarrow> wf_conn c l \<Longrightarrow> (\<forall>\<phi> \<in> set l. \<phi> \<noteq> FT \<and> \<phi> \<noteq> FF)
  \<Longrightarrow> no_T_F_symb (conn c l)"


lemma wf_conn_no_T_F_symb_iff[simp]:
  "wf_conn c \<psi>s \<Longrightarrow>
    no_T_F_symb (conn c \<psi>s) \<longleftrightarrow> (c \<noteq> CF \<and> c \<noteq> CT \<and> (\<forall>\<psi>\<in>set \<psi>s. \<psi> \<noteq> FF \<and> \<psi> \<noteq> FT))"
  unfolding no_T_F_symb.simps apply (cases c)
          using wf_conn_list(1) apply fastforce
         using wf_conn_list(2) apply fastforce
        using wf_conn_list(3) apply fastforce
       apply (metis (no_types, hide_lams) conn_inj connective.distinct(5,17))
      using conn_inj apply blast+
  done

lemma wf_conn_no_T_F_symb_iff_explicit[simp]:
  "no_T_F_symb (FAnd \<phi> \<psi>) \<longleftrightarrow> (\<forall>\<chi> \<in> set [\<phi>, \<psi>]. \<chi> \<noteq> FF \<and> \<chi> \<noteq> FT)"
  "no_T_F_symb (FOr \<phi> \<psi>) \<longleftrightarrow> (\<forall>\<chi> \<in> set [\<phi>, \<psi>]. \<chi> \<noteq> FF \<and> \<chi> \<noteq> FT)"
  "no_T_F_symb (FEq \<phi> \<psi>) \<longleftrightarrow> (\<forall>\<chi> \<in> set [\<phi>, \<psi>]. \<chi> \<noteq> FF \<and> \<chi> \<noteq> FT)"
  "no_T_F_symb (FImp \<phi> \<psi>) \<longleftrightarrow> (\<forall>\<chi> \<in> set [\<phi>, \<psi>]. \<chi> \<noteq> FF \<and> \<chi> \<noteq> FT)"
     apply (metis conn.simps(36) conn.simps(37) conn.simps(5) propo.distinct(19)
       wf_conn_helper_facts(5)  wf_conn_no_T_F_symb_iff)
    apply (metis conn.simps(36) conn.simps(37) conn.simps(6) propo.distinct(22)
      wf_conn_helper_facts(6) wf_conn_no_T_F_symb_iff)
   using wf_conn_no_T_F_symb_iff apply fastforce
  by (metis conn.simps(36) conn.simps(37) conn.simps(7) propo.distinct(23) wf_conn_helper_facts(7)
    wf_conn_no_T_F_symb_iff)


lemma no_T_F_symb_false[simp]:
  fixes c :: "'v connective"
  shows
    "\<not>no_T_F_symb (FT :: 'v propo)"
    "\<not>no_T_F_symb (FF :: 'v propo)"
    by (metis (no_types) conn.simps(1,2) wf_conn_no_T_F_symb_iff wf_conn_nullary)+

lemma no_T_F_symb_bool[simp]:
  fixes x :: "'v"
  shows "no_T_F_symb (FVar x)"
  using no_T_F_symb_comp wf_conn_nullary by (metis connective.distinct(3, 15) conn.simps(3)
    empty_iff list.set(1))


lemma no_T_F_symb_fnot_imp:
  "\<not>no_T_F_symb (FNot \<phi>) \<Longrightarrow> \<phi> = FT \<or> \<phi> = FF"
proof (rule ccontr)
  assume n: "\<not> no_T_F_symb (FNot \<phi>)"
  assume "\<not> (\<phi> = FT \<or> \<phi> = FF)"
  then have "\<forall>\<phi>' \<in> set [\<phi>]. \<phi>'\<noteq>FT \<and> \<phi>'\<noteq>FF" by auto
  moreover have "wf_conn CNot [\<phi>]" by simp
  ultimately have "no_T_F_symb (FNot \<phi>)"
    using no_T_F_symb.intros by (metis conn.simps(4) connective.distinct(5,17))
  then show "False" using n by blast
qed

lemma no_T_F_symb_fnot[simp]:
  "no_T_F_symb (FNot \<phi>) \<longleftrightarrow> \<not>(\<phi> = FT \<or> \<phi> = FF)"
  using no_T_F_symb.simps no_T_F_symb_fnot_imp by (metis conn_inj_not(2) list.set_intros(1))

text \<open>Actually it is not possible to remover every @{term FT} and @{term FF}: if the formula is
  equal to true or false, we can not remove it.\<close>
inductive no_T_F_symb_except_toplevel where
no_T_F_symb_except_toplevel_true[simp]: "no_T_F_symb_except_toplevel FT" |
no_T_F_symb_except_toplevel_false[simp]: "no_T_F_symb_except_toplevel FF" |
noTrue_no_T_F_symb_except_toplevel[simp]: "no_T_F_symb \<phi> \<Longrightarrow> no_T_F_symb_except_toplevel \<phi>"

lemma no_T_F_symb_except_toplevel_bool:
  fixes x :: "'v"
  shows "no_T_F_symb_except_toplevel (FVar x)"
  by simp

lemma no_T_F_symb_except_toplevel_not_decom:
  "\<phi> \<noteq> FT \<Longrightarrow> \<phi> \<noteq> FF \<Longrightarrow> no_T_F_symb_except_toplevel (FNot \<phi>)"
  by simp

lemma no_T_F_symb_except_toplevel_bin_decom:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "\<phi> \<noteq> FT" and "\<phi> \<noteq> FF" and "\<psi> \<noteq> FT" and "\<psi> \<noteq> FF"
  and c: "c\<in> binary_connectives"
  shows "no_T_F_symb_except_toplevel (conn c [\<phi>, \<psi>])"
  by (metis (no_types, lifting) assms c conn.simps(4) list.discI noTrue_no_T_F_symb_except_toplevel
    wf_conn_no_T_F_symb_iff no_T_F_symb_fnot set_ConsD wf_conn_binary wf_conn_helper_facts(1)
    wf_conn_list_decomp(1,2))

lemma no_T_F_symb_except_toplevel_if_is_a_true_false:
  fixes l :: "'v propo list" and c :: "'v connective"
  assumes corr: "wf_conn c l"
  and "FT \<in> set l \<or> FF \<in> set l"
  shows "\<not>no_T_F_symb_except_toplevel (conn c l)"
  by (metis assms empty_iff no_T_F_symb_except_toplevel.simps wf_conn_no_T_F_symb_iff set_empty
    wf_conn_list(1,2))


lemma no_T_F_symb_except_top_level_false_example[simp]:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "\<phi> = FT \<or> \<psi> = FT \<or> \<phi> = FF \<or> \<psi> = FF"
  shows
    "\<not> no_T_F_symb_except_toplevel (FAnd \<phi> \<psi>)"
    "\<not> no_T_F_symb_except_toplevel (FOr \<phi> \<psi>)"
    "\<not> no_T_F_symb_except_toplevel (FImp \<phi> \<psi>)"
    "\<not> no_T_F_symb_except_toplevel (FEq \<phi> \<psi>)"
  using assms no_T_F_symb_except_toplevel_if_is_a_true_false unfolding binary_connectives_def
    by (metis (no_types) conn.simps(5-8) insert_iff list.simps(14-15) wf_conn_helper_facts(5-8))+

lemma no_T_F_symb_except_top_level_false_not[simp]:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "\<phi> = FT \<or> \<phi> = FF"
  shows
    "\<not> no_T_F_symb_except_toplevel (FNot \<phi>)"
  by (simp add: assms no_T_F_symb_except_toplevel.simps)

text \<open>This is the local extension of @{const no_T_F_symb_except_toplevel}.\<close>
definition no_T_F_except_top_level where
"no_T_F_except_top_level \<equiv> all_subformula_st no_T_F_symb_except_toplevel"

text \<open>This is another property we will use. While this version might seem to be the one we want to
  prove, it is not since @{term FT} can not be reduced.\<close>
definition no_T_F where
"no_T_F \<equiv> all_subformula_st no_T_F_symb"

lemma no_T_F_except_top_level_false:
  fixes l :: "'v propo list" and c :: "'v connective"
  assumes "wf_conn c l"
  and "FT \<in> set l \<or> FF \<in> set l"
  shows "\<not>no_T_F_except_top_level (conn c l)"
  by (simp add: all_subformula_st_decomp assms no_T_F_except_top_level_def
    no_T_F_symb_except_toplevel_if_is_a_true_false)

lemma no_T_F_except_top_level_false_example[simp]:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "\<phi> = FT \<or> \<psi> = FT \<or> \<phi> = FF \<or> \<psi> = FF"
  shows
    "\<not>no_T_F_except_top_level (FAnd \<phi> \<psi>)"
    "\<not>no_T_F_except_top_level (FOr \<phi> \<psi>)"
    "\<not>no_T_F_except_top_level (FEq \<phi> \<psi>)"
    "\<not>no_T_F_except_top_level (FImp \<phi> \<psi>)"
  by (metis all_subformula_st_test_symb_true_phi assms no_T_F_except_top_level_def
    no_T_F_symb_except_top_level_false_example)+


lemma no_T_F_symb_except_toplevel_no_T_F_symb:
  "no_T_F_symb_except_toplevel \<phi> \<Longrightarrow> \<phi> \<noteq> FF \<Longrightarrow> \<phi> \<noteq> FT \<Longrightarrow> no_T_F_symb \<phi>"
  by (induct rule: no_T_F_symb_except_toplevel.induct, auto)

text \<open>The two following lemmas give the precise link between the two definitions.\<close>
lemma no_T_F_symb_except_toplevel_all_subformula_st_no_T_F_symb:
  "no_T_F_except_top_level \<phi> \<Longrightarrow> \<phi> \<noteq> FF \<Longrightarrow> \<phi> \<noteq> FT \<Longrightarrow> no_T_F \<phi>"
  unfolding no_T_F_except_top_level_def no_T_F_def apply (induct \<phi>)
  using no_T_F_symb_fnot by fastforce+

lemma no_T_F_no_T_F_except_top_level:
  "no_T_F \<phi> \<Longrightarrow> no_T_F_except_top_level \<phi>"
  unfolding no_T_F_except_top_level_def no_T_F_def
  unfolding all_subformula_st_def by auto

lemma no_T_F_except_top_level_simp[simp]:  "no_T_F_except_top_level FF" "no_T_F_except_top_level FT"
  unfolding no_T_F_except_top_level_def by auto

lemma no_T_F_no_T_F_except_top_level'[simp]:
  "no_T_F_except_top_level \<phi> \<longleftrightarrow> (\<phi> = FF \<or> \<phi> = FT \<or> no_T_F \<phi>)"
  using no_T_F_symb_except_toplevel_all_subformula_st_no_T_F_symb no_T_F_no_T_F_except_top_level
  by auto

lemma no_T_F_bin_decomp[simp]:
  assumes c: "c \<in> binary_connectives"
  shows "no_T_F (conn c [\<phi>, \<psi>]) \<longleftrightarrow> (no_T_F \<phi> \<and> no_T_F \<psi>)"
proof -
  have wf: "wf_conn c [\<phi>, \<psi>]" using c by auto
  then have "no_T_F (conn c [\<phi>, \<psi>]) \<longleftrightarrow> (no_T_F_symb (conn c [\<phi>, \<psi>]) \<and> no_T_F \<phi> \<and> no_T_F \<psi>)"
    by (simp add: all_subformula_st_decomp no_T_F_def)
  then show "no_T_F (conn c [\<phi>, \<psi>]) \<longleftrightarrow> (no_T_F \<phi> \<and> no_T_F \<psi>)"
    using c wf all_subformula_st_decomp list.discI no_T_F_def no_T_F_symb_except_toplevel_bin_decom
      no_T_F_symb_except_toplevel_no_T_F_symb no_T_F_symb_false(1,2) wf_conn_helper_facts(2,3)
      wf_conn_list(1,2) by metis
qed

lemma no_T_F_bin_decomp_expanded[simp]:
  assumes c: "c = CAnd \<or> c = COr \<or> c = CEq \<or> c = CImp"
  shows "no_T_F (conn c [\<phi>, \<psi>]) \<longleftrightarrow> (no_T_F \<phi> \<and> no_T_F \<psi>)"
  using no_T_F_bin_decomp assms unfolding binary_connectives_def by blast

lemma no_T_F_comp_expanded_explicit[simp]:
  fixes \<phi> \<psi> :: "'v propo"
  shows
    "no_T_F (FAnd \<phi> \<psi>) \<longleftrightarrow> (no_T_F \<phi> \<and> no_T_F \<psi>)"
    "no_T_F (FOr \<phi> \<psi>)  \<longleftrightarrow> (no_T_F \<phi> \<and> no_T_F \<psi>)"
    "no_T_F (FEq \<phi> \<psi>)  \<longleftrightarrow> (no_T_F \<phi> \<and> no_T_F \<psi>)"
    "no_T_F (FImp \<phi> \<psi>) \<longleftrightarrow> (no_T_F \<phi> \<and> no_T_F \<psi>)"
  using conn.simps(5-8) no_T_F_bin_decomp_expanded by (metis (no_types))+

lemma no_T_F_comp_not[simp]:
  fixes \<phi> \<psi> :: "'v propo"
  shows "no_T_F (FNot \<phi>) \<longleftrightarrow> no_T_F \<phi>"
  by (metis all_subformula_st_decomp_explicit(3) all_subformula_st_test_symb_true_phi no_T_F_def
    no_T_F_symb_false(1,2) no_T_F_symb_fnot_imp)

lemma no_T_F_decomp:
  fixes \<phi> \<psi> :: "'v propo"
  assumes \<phi>: "no_T_F (FAnd \<phi> \<psi>) \<or> no_T_F (FOr \<phi> \<psi>) \<or> no_T_F (FEq \<phi> \<psi>) \<or> no_T_F (FImp \<phi> \<psi>)"
  shows "no_T_F \<psi>" and "no_T_F \<phi>"
  using assms by auto

lemma no_T_F_decomp_not:
  fixes \<phi> :: "'v propo"
  assumes \<phi>: "no_T_F (FNot \<phi>)"
  shows "no_T_F \<phi>"
  using assms by auto

lemma no_T_F_symb_except_toplevel_step_exists:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "no_equiv \<phi>" and "no_imp \<phi>"
  shows "\<psi> \<preceq> \<phi> \<Longrightarrow> \<not> no_T_F_symb_except_toplevel \<psi> \<Longrightarrow> \<exists>\<psi>'. elimTB \<psi> \<psi>'"
proof (induct \<psi> rule: propo_induct_arity)
  case (nullary \<phi>' x)
  then have "False" using no_T_F_symb_except_toplevel_true no_T_F_symb_except_toplevel_false by auto
  then show ?case by blast
next
  case (unary \<psi>)
  then have "\<psi> = FF \<or> \<psi> = FT" using no_T_F_symb_except_toplevel_not_decom by blast
  then show ?case using ElimTB5 ElimTB6 by blast
next
  case (binary \<phi>' \<psi>1 \<psi>2)
  note IH1 = this(1) and IH2 = this(2) and \<phi>' = this(3) and F\<phi> = this(4) and n = this(5)
  {
    assume "\<phi>' = FImp \<psi>1 \<psi>2 \<or> \<phi>' = FEq \<psi>1 \<psi>2"
    then have "False" using n F\<phi> subformula_all_subformula_st assms
      by (metis (no_types) no_equiv_eq(1) no_equiv_def no_imp_Imp(1) no_imp_def)
    then have ?case by blast
  }
  moreover {
    assume \<phi>': "\<phi>' = FAnd \<psi>1 \<psi>2 \<or> \<phi>' = FOr \<psi>1 \<psi>2"
    then have "\<psi>1 = FT \<or> \<psi>2 = FT \<or> \<psi>1 = FF \<or> \<psi>2 = FF"
      using no_T_F_symb_except_toplevel_bin_decom conn.simps(5,6) n unfolding binary_connectives_def
      by fastforce+
    then have ?case using elimTB.intros \<phi>' by blast
  }
  ultimately show ?case using \<phi>' by blast
qed

lemma no_T_F_except_top_level_rew:
  fixes \<phi> :: "'v propo"
  assumes noTB: "\<not> no_T_F_except_top_level \<phi>" and no_equiv: "no_equiv \<phi>" and no_imp: "no_imp \<phi>"
  shows "\<exists>\<psi> \<psi>'. \<psi> \<preceq> \<phi> \<and> elimTB \<psi> \<psi>' "
proof -
  have test_symb_false_nullary: "\<forall>x. no_T_F_symb_except_toplevel (FF:: 'v propo)
    \<and> no_T_F_symb_except_toplevel FT \<and> no_T_F_symb_except_toplevel (FVar (x:: 'v))" by auto
  moreover {
     fix c:: "'v connective" and l :: "'v propo list" and \<psi> :: "'v propo"
     have H: "elimTB (conn c l) \<psi> \<Longrightarrow> \<not>no_T_F_symb_except_toplevel (conn c l) "
       by (cases "conn c l" rule: elimTB.cases, auto)
  }
  moreover {
     fix x :: "'v"
     have H': "no_T_F_except_top_level FT" " no_T_F_except_top_level FF"
       "no_T_F_except_top_level (FVar x)"
       by (auto simp: no_T_F_except_top_level_def test_symb_false_nullary)
  }
  moreover {
     fix \<psi>
     have "\<psi> \<preceq> \<phi> \<Longrightarrow> \<not> no_T_F_symb_except_toplevel \<psi> \<Longrightarrow> \<exists>\<psi>'. elimTB \<psi> \<psi>'"
       using no_T_F_symb_except_toplevel_step_exists no_equiv no_imp by auto
  }
  ultimately show ?thesis
    using no_test_symb_step_exists noTB unfolding no_T_F_except_top_level_def by blast
qed

lemma elimTB_inv:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "full (propo_rew_step elimTB) \<phi> \<psi> "
  and "no_equiv \<phi>" and "no_imp \<phi>"
  shows "no_equiv \<psi>" and "no_imp \<psi>"
proof -
  {
     fix \<phi> \<psi> :: "'v propo"
     have H: "elimTB \<phi> \<psi> \<Longrightarrow> no_equiv \<phi> \<Longrightarrow>  no_equiv \<psi>"
       by (induct \<phi> \<psi> rule: elimTB.induct, auto)
  }
  then show "no_equiv \<psi>"
    using full_propo_rew_step_inv_stay_conn[of elimTB no_equiv_symb \<phi> \<psi>]
      no_equiv_symb_conn_characterization assms unfolding no_equiv_def by metis
next
  {
     fix \<phi> \<psi> :: "'v propo"
     have H: "elimTB \<phi> \<psi> \<Longrightarrow> no_imp \<phi> \<Longrightarrow> no_imp \<psi>"
       by (induct \<phi> \<psi> rule: elimTB.induct, auto)
  }
  then show "no_imp \<psi>"
    using full_propo_rew_step_inv_stay_conn[of elimTB no_imp_symb \<phi> \<psi>] assms
      no_imp_symb_conn_characterization unfolding no_imp_def by metis
qed

lemma elimTB_full_propo_rew_step:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "no_equiv \<phi>" and "no_imp \<phi>" and "full (propo_rew_step elimTB) \<phi> \<psi>"
  shows "no_T_F_except_top_level \<psi>"
  using full_propo_rew_step_subformula no_T_F_except_top_level_rew assms elimTB_inv by fastforce


subsection "PushNeg"
text \<open>Push the negation inside the formula, until the litteral.\<close>
inductive pushNeg where
PushNeg1[simp]: "pushNeg (FNot (FAnd \<phi> \<psi>)) (FOr (FNot \<phi>) (FNot \<psi>))" |
PushNeg2[simp]: "pushNeg (FNot (FOr \<phi> \<psi>)) (FAnd (FNot \<phi>) (FNot \<psi>))" |
PushNeg3[simp]: "pushNeg (FNot (FNot \<phi>)) \<phi>"


lemma pushNeg_transformation_consistent:
"A \<Turnstile> FNot (FAnd \<phi> \<psi>) \<longleftrightarrow> A \<Turnstile> (FOr (FNot \<phi>) (FNot \<psi>))"
"A \<Turnstile> FNot (FOr \<phi> \<psi>)  \<longleftrightarrow> A \<Turnstile> (FAnd (FNot \<phi>) (FNot \<psi>))"
"A \<Turnstile> FNot (FNot \<phi>)   \<longleftrightarrow> A \<Turnstile> \<phi>"
  by auto


lemma pushNeg_explicit: "pushNeg \<phi> \<psi> \<Longrightarrow> \<forall>A. A \<Turnstile> \<phi> \<longleftrightarrow> A \<Turnstile> \<psi>"
  by (induct \<phi> \<psi> rule: pushNeg.induct, auto)

lemma pushNeg_consistent: "preserve_models pushNeg"
  unfolding preserve_models_def by (simp add: pushNeg_explicit)


lemma pushNeg_lifted_consistant:
"preserve_models (full (propo_rew_step pushNeg))"
  by (simp add: pushNeg_consistent)

fun simple where
"simple FT = True" |
"simple FF = True" |
"simple (FVar _) = True" |
"simple _ = False"

lemma simple_decomp:
  "simple \<phi> \<longleftrightarrow> (\<phi> = FT \<or> \<phi> = FF \<or> (\<exists>x. \<phi> = FVar x))"
  by (cases \<phi>) auto

lemma subformula_conn_decomp_simple:
  fixes \<phi> \<psi> :: "'v propo"
  assumes s: "simple \<psi>"
  shows "\<phi> \<preceq> FNot \<psi> \<longleftrightarrow> (\<phi> = FNot \<psi> \<or> \<phi> = \<psi>)"
proof -
  have "\<phi> \<preceq> conn CNot [\<psi>] \<longleftrightarrow> (\<phi> = conn CNot [\<psi>] \<or> (\<exists> \<psi>\<in> set [\<psi>]. \<phi> \<preceq> \<psi>))"
    using subformula_conn_decomp wf_conn_helper_facts(1) by metis
  then show "\<phi> \<preceq> FNot \<psi> \<longleftrightarrow> (\<phi> = FNot \<psi> \<or> \<phi> = \<psi>)" using s by (auto simp: simple_decomp)
qed

lemma subformula_conn_decomp_explicit[simp]:
  fixes \<phi> :: "'v propo" and x :: "'v"
  shows
    "\<phi> \<preceq> FNot FT \<longleftrightarrow> (\<phi> = FNot FT \<or> \<phi> = FT)"
    "\<phi> \<preceq> FNot FF \<longleftrightarrow> (\<phi> = FNot FF \<or> \<phi> = FF)"
    "\<phi> \<preceq> FNot (FVar x) \<longleftrightarrow> (\<phi> = FNot (FVar x) \<or> \<phi> = FVar x)"
  by (auto simp: subformula_conn_decomp_simple)


fun simple_not_symb where
"simple_not_symb (FNot \<phi>) = (simple \<phi>)" |
"simple_not_symb _ = True"

definition simple_not where
"simple_not = all_subformula_st simple_not_symb"
declare simple_not_def[simp]

lemma simple_not_Not[simp]:
  "\<not> simple_not (FNot (FAnd \<phi> \<psi>))"
  "\<not> simple_not (FNot (FOr \<phi> \<psi>))"
  by auto

lemma simple_not_step_exists:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "no_equiv \<phi>" and "no_imp \<phi>"
  shows "\<psi> \<preceq> \<phi> \<Longrightarrow> \<not> simple_not_symb \<psi> \<Longrightarrow> \<exists>\<psi>'. pushNeg \<psi> \<psi>'"
  apply (induct \<psi>, auto)
  apply (rename_tac \<psi>, case_tac \<psi>, auto intro: pushNeg.intros)
  by (metis assms(1,2) no_imp_Imp(1) no_equiv_eq(1) no_imp_def no_equiv_def
    subformula_in_subformula_not subformula_all_subformula_st)+

lemma simple_not_rew:
  fixes \<phi> :: "'v propo"
  assumes noTB: "\<not> simple_not \<phi>" and no_equiv: "no_equiv \<phi>" and no_imp: "no_imp \<phi>"
  shows "\<exists>\<psi> \<psi>'. \<psi> \<preceq> \<phi> \<and> pushNeg \<psi> \<psi>'"
proof -
  have "\<forall>x. simple_not_symb (FF:: 'v propo) \<and> simple_not_symb FT \<and> simple_not_symb (FVar (x:: 'v))"
    by auto
  moreover {
     fix c:: "'v connective" and l :: "'v propo list" and \<psi> :: "'v propo"
     have H: "pushNeg (conn c l) \<psi> \<Longrightarrow> \<not>simple_not_symb (conn c l)"
       by (cases "conn c l" rule: pushNeg.cases) auto
  }
  moreover {
     fix x :: "'v"
     have H': "simple_not FT" "simple_not FF" "simple_not (FVar x)"
       by simp_all
  }
  moreover {
     fix \<psi> :: "'v propo"
     have "\<psi> \<preceq> \<phi> \<Longrightarrow> \<not> simple_not_symb \<psi> \<Longrightarrow> \<exists>\<psi>'. pushNeg \<psi> \<psi>'"
       using simple_not_step_exists no_equiv no_imp by blast
  }
  ultimately show ?thesis using no_test_symb_step_exists noTB unfolding simple_not_def by blast
qed

lemma no_T_F_except_top_level_pushNeg1:
  "no_T_F_except_top_level (FNot (FAnd \<phi> \<psi>)) \<Longrightarrow> no_T_F_except_top_level (FOr (FNot \<phi>) (FNot \<psi>))"
  using no_T_F_symb_except_toplevel_all_subformula_st_no_T_F_symb no_T_F_comp_not no_T_F_decomp(1)
    no_T_F_decomp(2) no_T_F_no_T_F_except_top_level by (metis no_T_F_comp_expanded_explicit(2)
      propo.distinct(5,17))

lemma no_T_F_except_top_level_pushNeg2:
  "no_T_F_except_top_level (FNot (FOr \<phi> \<psi>)) \<Longrightarrow> no_T_F_except_top_level (FAnd (FNot \<phi>) (FNot \<psi>))"
  by auto

lemma no_T_F_symb_pushNeg:
  "no_T_F_symb (FOr (FNot \<phi>') (FNot \<psi>'))"
  "no_T_F_symb (FAnd (FNot \<phi>') (FNot \<psi>'))"
  "no_T_F_symb (FNot (FNot \<phi>'))"
  by auto

lemma propo_rew_step_pushNeg_no_T_F_symb:
  "propo_rew_step pushNeg \<phi> \<psi> \<Longrightarrow> no_T_F_except_top_level \<phi> \<Longrightarrow> no_T_F_symb \<phi> \<Longrightarrow> no_T_F_symb \<psi>"
  apply (induct rule: propo_rew_step.induct)
  apply (cases rule: pushNeg.cases)
  apply simp_all
  apply (metis no_T_F_symb_pushNeg(1))
  apply (metis no_T_F_symb_pushNeg(2))
  apply (simp, metis all_subformula_st_test_symb_true_phi no_T_F_def)
proof -
  fix \<phi> \<phi>':: "'a propo" and c:: "'a connective" and \<xi> \<xi>':: "'a propo list"
  assume rel: "propo_rew_step pushNeg \<phi> \<phi>'"
  and IH: "no_T_F \<phi> \<Longrightarrow> no_T_F_symb \<phi> \<Longrightarrow> no_T_F_symb \<phi>'"
  and wf: "wf_conn c (\<xi> @ \<phi> # \<xi>')"
  and n: "conn c (\<xi> @ \<phi> # \<xi>') = FF \<or> conn c (\<xi> @ \<phi> # \<xi>') = FT \<or> no_T_F (conn c (\<xi> @ \<phi> # \<xi>'))"
  and x: "c \<noteq> CF \<and> c \<noteq> CT \<and> \<phi> \<noteq> FF \<and> \<phi> \<noteq> FT \<and> (\<forall>\<psi> \<in> set \<xi> \<union> set \<xi>'. \<psi> \<noteq> FF \<and> \<psi> \<noteq> FT)"
  then have "c \<noteq> CF \<and> c \<noteq> CF \<and> wf_conn c (\<xi> @ \<phi>' # \<xi>')"
    using wf_conn_no_arity_change_helper wf_conn_no_arity_change by metis
  moreover have n': "no_T_F (conn c (\<xi> @ \<phi> # \<xi>'))" using n by (simp add: wf wf_conn_list(1,2))
  moreover
  {
    have "no_T_F \<phi>"
      by (metis Un_iff all_subformula_st_decomp list.set_intros(1)  n' wf no_T_F_def set_append)
    moreover then have "no_T_F_symb \<phi>"
      by (simp add: all_subformula_st_test_symb_true_phi no_T_F_def)
    ultimately have "\<phi>' \<noteq> FF \<and> \<phi>' \<noteq> FT"
      using IH no_T_F_symb_false(1) no_T_F_symb_false(2) by blast
    then have "\<forall>\<psi>\<in> set (\<xi> @ \<phi>' # \<xi>'). \<psi> \<noteq> FF \<and> \<psi> \<noteq> FT" using x by auto
  }
  ultimately show "no_T_F_symb (conn c (\<xi> @ \<phi>' # \<xi>'))" by (simp add: x)
qed

lemma propo_rew_step_pushNeg_no_T_F:
  "propo_rew_step pushNeg \<phi> \<psi> \<Longrightarrow> no_T_F \<phi> \<Longrightarrow> no_T_F \<psi>"
proof (induct rule: propo_rew_step.induct)
  case global_rel
  then show ?case
    by (metis (no_types, lifting) no_T_F_symb_except_toplevel_all_subformula_st_no_T_F_symb
      no_T_F_def no_T_F_except_top_level_pushNeg1 no_T_F_except_top_level_pushNeg2
      no_T_F_no_T_F_except_top_level all_subformula_st_decomp_explicit(3) pushNeg.simps
      simple.simps(1,2,5,6))
next
  case (propo_rew_one_step_lift \<phi> \<phi>' c \<xi> \<xi>')
  note rel = this(1) and IH = this(2) and wf = this(3) and no_T_F = this(4)
  moreover have wf': "wf_conn c (\<xi> @ \<phi>' # \<xi>')"
    using wf_conn_no_arity_change wf_conn_no_arity_change_helper wf by metis
  ultimately show "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))"
    using all_subformula_st_test_symb_true_phi
    by (fastforce simp: no_T_F_def all_subformula_st_decomp wf wf')
qed


lemma pushNeg_inv:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "full (propo_rew_step pushNeg) \<phi> \<psi>"
  and "no_equiv \<phi>" and "no_imp \<phi>" and "no_T_F_except_top_level \<phi>"
  shows "no_equiv \<psi>" and "no_imp \<psi>" and "no_T_F_except_top_level \<psi>"
proof -
  {
    fix \<phi> \<psi> :: "'v propo"
    assume rel: "propo_rew_step pushNeg \<phi> \<psi>"
    and no: "no_T_F_except_top_level \<phi>"
    then have " no_T_F_except_top_level \<psi>"
      proof -
        {
          assume "\<phi> = FT \<or> \<phi> = FF"
          from rel this have False
            apply (induct rule: propo_rew_step.induct)
              using pushNeg.cases apply blast
            using wf_conn_list(1) wf_conn_list(2) by auto
          then have "no_T_F_except_top_level \<psi>" by blast
        }
        moreover {
          assume "\<phi> \<noteq> FT \<and> \<phi> \<noteq> FF"
          then have "no_T_F \<phi>"
            by (metis no no_T_F_symb_except_toplevel_all_subformula_st_no_T_F_symb)
          then have "no_T_F \<psi>"
            using propo_rew_step_pushNeg_no_T_F rel by auto
          then have "no_T_F_except_top_level \<psi>" by (simp add: no_T_F_no_T_F_except_top_level)
        }
        ultimately show "no_T_F_except_top_level \<psi>" by metis
      qed
  }
  moreover {
     fix c :: "'v connective" and \<xi> \<xi>' :: "'v propo list" and \<zeta> \<zeta>' :: "'v propo"
     assume rel: "propo_rew_step pushNeg \<zeta> \<zeta>'"
     and incl: "\<zeta> \<preceq> \<phi>"
     and corr: "wf_conn c (\<xi> @ \<zeta> # \<xi>')"
     and no_T_F: "no_T_F_symb_except_toplevel (conn c (\<xi> @ \<zeta> # \<xi>'))"
     and n: "no_T_F_symb_except_toplevel \<zeta>'"
     have "no_T_F_symb_except_toplevel (conn c (\<xi> @ \<zeta>' # \<xi>'))"
     proof
       have p: "no_T_F_symb (conn c (\<xi> @ \<zeta> # \<xi>'))"
         using corr wf_conn_list(1) wf_conn_list(2) no_T_F_symb_except_toplevel_no_T_F_symb no_T_F
         by blast
       have l: "\<forall>\<phi>\<in>set (\<xi> @ \<zeta> # \<xi>'). \<phi> \<noteq> FT \<and> \<phi> \<noteq> FF"
         using corr wf_conn_no_T_F_symb_iff p by blast
       from rel incl have "\<zeta>'\<noteq>FT \<and>\<zeta>'\<noteq>FF"
         apply (induction \<zeta> \<zeta>' rule: propo_rew_step.induct)
         apply (cases rule: pushNeg.cases, auto)
         by (metis assms(4) no_T_F_symb_except_top_level_false_not no_T_F_except_top_level_def
           all_subformula_st_test_symb_true_phi subformula_in_subformula_not
           subformula_all_subformula_st append_is_Nil_conv list.distinct(1)
           wf_conn_no_arity_change_helper wf_conn_list(1,2) wf_conn_no_arity_change)+
       then have "\<forall>\<phi> \<in> set (\<xi> @ \<zeta>' # \<xi>'). \<phi> \<noteq> FT \<and> \<phi> \<noteq> FF" using l by auto
       moreover have "c \<noteq> CT \<and> c \<noteq> CF" using corr by auto
       ultimately show "no_T_F_symb (conn c (\<xi> @ \<zeta>' # \<xi>'))"
         by (metis corr no_T_F_symb_comp wf_conn_no_arity_change wf_conn_no_arity_change_helper)
     qed
  }
  ultimately show "no_T_F_except_top_level \<psi>"
    using full_propo_rew_step_inv_stay_with_inc[of pushNeg no_T_F_symb_except_toplevel \<phi>] assms
      subformula_refl unfolding no_T_F_except_top_level_def full_unfold by metis
next
  {
    fix \<phi> \<psi> :: "'v propo"
    have H: "pushNeg \<phi> \<psi> \<Longrightarrow> no_equiv \<phi> \<Longrightarrow> no_equiv \<psi>"
      by (induct \<phi> \<psi> rule: pushNeg.induct, auto)
  }
  then show "no_equiv \<psi>"
    using full_propo_rew_step_inv_stay_conn[of pushNeg no_equiv_symb \<phi> \<psi>]
    no_equiv_symb_conn_characterization assms unfolding no_equiv_def full_unfold by metis
next
  {
    fix \<phi> \<psi> :: "'v propo"
    have H: "pushNeg \<phi> \<psi> \<Longrightarrow> no_imp \<phi> \<Longrightarrow>  no_imp \<psi>"
      by (induct \<phi> \<psi> rule: pushNeg.induct, auto)
  }
  then show "no_imp \<psi>"
    using full_propo_rew_step_inv_stay_conn[of pushNeg no_imp_symb \<phi> \<psi>] assms
      no_imp_symb_conn_characterization unfolding no_imp_def full_unfold by metis
qed


lemma pushNeg_full_propo_rew_step:
  fixes \<phi> \<psi> :: "'v propo"
  assumes
    "no_equiv \<phi>" and
    "no_imp \<phi>" and
    "full (propo_rew_step pushNeg) \<phi> \<psi>" and
    "no_T_F_except_top_level \<phi>"
  shows "simple_not \<psi>"
  using assms full_propo_rew_step_subformula pushNeg_inv(1,2) simple_not_rew by blast


subsection \<open>Push Inside\<close>

inductive push_conn_inside :: "'v connective \<Rightarrow> 'v connective \<Rightarrow> 'v propo \<Rightarrow> 'v propo \<Rightarrow> bool"
  for c c':: "'v connective" where
push_conn_inside_l[simp]: "c = CAnd \<or> c = COr \<Longrightarrow> c' = CAnd \<or> c' = COr
  \<Longrightarrow> push_conn_inside c c' (conn c [conn c' [\<phi>1, \<phi>2], \<psi>])
        (conn c' [conn c [\<phi>1, \<psi>], conn c [\<phi>2, \<psi>]])" |
push_conn_inside_r[simp]: "c = CAnd \<or> c = COr \<Longrightarrow> c' = CAnd \<or> c' = COr
  \<Longrightarrow> push_conn_inside c c' (conn c [\<psi>, conn c' [\<phi>1, \<phi>2]])
    (conn c' [conn c [\<psi>, \<phi>1], conn c [\<psi>, \<phi>2]])"


lemma push_conn_inside_explicit: "push_conn_inside c c' \<phi> \<psi> \<Longrightarrow> \<forall>A. A\<Turnstile>\<phi> \<longleftrightarrow> A\<Turnstile>\<psi>"
  by (induct \<phi> \<psi> rule: push_conn_inside.induct, auto)

lemma push_conn_inside_consistent: "preserve_models (push_conn_inside c c')"
  unfolding preserve_models_def by (simp add: push_conn_inside_explicit)

lemma propo_rew_step_push_conn_inside[simp]:
 "\<not>propo_rew_step (push_conn_inside c c') FT \<psi>" "\<not>propo_rew_step (push_conn_inside c c') FF \<psi>"
 proof -
  {
    {
      fix \<phi> \<psi>
      have "push_conn_inside c c' \<phi> \<psi> \<Longrightarrow> \<phi> = FT \<or> \<phi> = FF \<Longrightarrow> False"
        by (induct rule: push_conn_inside.induct, auto)
    } note H = this
    fix \<phi>
    have "propo_rew_step (push_conn_inside c c') \<phi> \<psi> \<Longrightarrow> \<phi> = FT \<or> \<phi> = FF \<Longrightarrow> False"
      apply (induct rule: propo_rew_step.induct, auto simp: wf_conn_list(1) wf_conn_list(2))
      using H by blast+
  }
  then show
    "\<not>propo_rew_step (push_conn_inside c c') FT \<psi>"
    "\<not>propo_rew_step (push_conn_inside c c') FF \<psi>" by blast+
qed


inductive not_c_in_c'_symb:: "'v connective \<Rightarrow> 'v connective \<Rightarrow> 'v propo \<Rightarrow> bool" for c c' where
not_c_in_c'_symb_l[simp]: "wf_conn c [conn c' [\<phi>, \<phi>'], \<psi>] \<Longrightarrow> wf_conn c' [\<phi>, \<phi>']
  \<Longrightarrow> not_c_in_c'_symb c c' (conn c [conn c' [\<phi>, \<phi>'], \<psi>])" |
not_c_in_c'_symb_r[simp]: "wf_conn c [\<psi>, conn c' [\<phi>, \<phi>']] \<Longrightarrow> wf_conn c' [\<phi>, \<phi>']
  \<Longrightarrow> not_c_in_c'_symb c c' (conn c [\<psi>, conn c' [\<phi>, \<phi>']])"

abbreviation "c_in_c'_symb c c' \<phi> \<equiv> \<not>not_c_in_c'_symb c c' \<phi>"


lemma c_in_c'_symb_simp:
  "not_c_in_c'_symb c c' \<xi> \<Longrightarrow> \<xi> = FF \<or> \<xi> = FT \<or> \<xi> = FVar x \<or> \<xi> = FNot FF \<or> \<xi> = FNot FT
    \<or> \<xi> = FNot (FVar x)\<Longrightarrow> False"
  apply (induct rule: not_c_in_c'_symb.induct, auto simp: wf_conn.simps wf_conn_list(1-3))
  using conn_inj_not(2) wf_conn_binary unfolding binary_connectives_def by fastforce+

lemma c_in_c'_symb_simp'[simp]:
  "\<not>not_c_in_c'_symb c c' FF"
  "\<not>not_c_in_c'_symb c c' FT"
  "\<not>not_c_in_c'_symb c c' (FVar x)"
  "\<not>not_c_in_c'_symb c c' (FNot FF)"
  "\<not>not_c_in_c'_symb c c' (FNot FT)"
  "\<not>not_c_in_c'_symb c c' (FNot (FVar x))"
  using c_in_c'_symb_simp by metis+

definition c_in_c'_only where
"c_in_c'_only c c' \<equiv> all_subformula_st (c_in_c'_symb c c')"

lemma c_in_c'_only_simp[simp]:
  "c_in_c'_only c c' FF"
  "c_in_c'_only c c' FT"
  "c_in_c'_only c c' (FVar x)"
  "c_in_c'_only c c' (FNot FF)"
  "c_in_c'_only c c' (FNot FT)"
  "c_in_c'_only c c' (FNot (FVar x))"
  unfolding c_in_c'_only_def by auto


lemma not_c_in_c'_symb_commute:
  "not_c_in_c'_symb c c' \<xi> \<Longrightarrow> wf_conn c [\<phi>, \<psi>] \<Longrightarrow> \<xi> = conn c [\<phi>, \<psi>]
    \<Longrightarrow> not_c_in_c'_symb c c' (conn c [\<psi>, \<phi>])"
proof (induct rule: not_c_in_c'_symb.induct)
  case (not_c_in_c'_symb_r \<phi>' \<phi>'' \<psi>') note H = this
  then have \<psi>: "\<psi> = conn c' [\<phi>'', \<psi>']" using conn_inj by auto
  have "wf_conn c [conn c' [\<phi>'', \<psi>'], \<phi>]"
    using H(1) wf_conn_no_arity_change length_Cons by metis
  then show "not_c_in_c'_symb c c' (conn c [\<psi>, \<phi>])"
    unfolding \<psi> using not_c_in_c'_symb.intros(1) H by auto
next
  case (not_c_in_c'_symb_l \<phi>' \<phi>'' \<psi>') note H = this
  then have "\<phi> = conn c' [\<phi>', \<phi>'']" using conn_inj by auto
  moreover have "wf_conn c [\<psi>', conn c' [\<phi>', \<phi>'']]"
    using H(1) wf_conn_no_arity_change length_Cons by metis
  ultimately show "not_c_in_c'_symb c c' (conn c [\<psi>, \<phi>])"
    using not_c_in_c'_symb.intros(2) conn_inj not_c_in_c'_symb_l.hyps
      not_c_in_c'_symb_l.prems(1,2) by blast
qed

lemma not_c_in_c'_symb_commute':
  "wf_conn c [\<phi>, \<psi>] \<Longrightarrow> c_in_c'_symb c c' (conn c [\<phi>, \<psi>])  \<longleftrightarrow> c_in_c'_symb c c' (conn c [\<psi>, \<phi>])"
  using not_c_in_c'_symb_commute wf_conn_no_arity_change by (metis length_Cons)

lemma not_c_in_c'_comm:
  assumes wf: "wf_conn c [\<phi>, \<psi>]"
  shows "c_in_c'_only c c' (conn c [\<phi>, \<psi>]) \<longleftrightarrow> c_in_c'_only c c' (conn c [\<psi>, \<phi>])" (is "?A \<longleftrightarrow> ?B")
proof -
  have "?A \<longleftrightarrow> (c_in_c'_symb c c' (conn c [\<phi>, \<psi>])
               \<and> (\<forall>\<xi> \<in> set [\<phi>, \<psi>]. all_subformula_st (c_in_c'_symb c c') \<xi>))"
    using all_subformula_st_decomp wf unfolding c_in_c'_only_def by fastforce
  also have "\<dots> \<longleftrightarrow> (c_in_c'_symb c c' (conn c [\<psi>, \<phi>])
                    \<and> (\<forall>\<xi> \<in> set [\<psi>, \<phi>]. all_subformula_st (c_in_c'_symb c c') \<xi>))"
    using not_c_in_c'_symb_commute' wf by auto
  also
    have "wf_conn c [\<psi>, \<phi>]" using wf_conn_no_arity_change wf by (metis length_Cons)
    then have "(c_in_c'_symb c c' (conn c [\<psi>, \<phi>])
             \<and> (\<forall>\<xi> \<in> set [\<psi>, \<phi>]. all_subformula_st (c_in_c'_symb c c') \<xi>))
           \<longleftrightarrow> ?B"
      using all_subformula_st_decomp unfolding c_in_c'_only_def by fastforce
  finally show ?thesis .
qed

lemma not_c_in_c'_simp[simp]:
  fixes \<phi>1 \<phi>2 \<psi> :: "'v propo" and x :: "'v"
  shows
  "c_in_c'_symb c c' FT"
  "c_in_c'_symb c c' FF"
  "c_in_c'_symb c c' (FVar x)"
  "wf_conn c [conn c' [\<phi>1, \<phi>2], \<psi>] \<Longrightarrow> wf_conn c' [\<phi>1, \<phi>2]
    \<Longrightarrow> \<not> c_in_c'_only c c' (conn c [conn c' [\<phi>1, \<phi>2], \<psi>])"
  apply (simp_all add: c_in_c'_only_def)
  using all_subformula_st_test_symb_true_phi not_c_in_c'_symb_l by blast

lemma c_in_c'_symb_not[simp]:
  fixes c c' :: "'v connective" and \<psi> :: "'v propo"
  shows "c_in_c'_symb c c' (FNot \<psi>)"
proof -
  {
    fix \<xi> :: "'v propo"
    have "not_c_in_c'_symb c c' (FNot \<psi>) \<Longrightarrow> False"
      apply (induct "FNot \<psi>" rule: not_c_in_c'_symb.induct)
      using conn_inj_not(2) by blast+
  }
 then show ?thesis by auto
qed

lemma c_in_c'_symb_step_exists:
  fixes \<phi> :: "'v propo"
  assumes c: "c = CAnd \<or> c = COr" and c': "c' = CAnd \<or> c' = COr"
  shows "\<psi> \<preceq> \<phi> \<Longrightarrow> \<not> c_in_c'_symb c c' \<psi> \<Longrightarrow> \<exists>\<psi>'. push_conn_inside c c' \<psi> \<psi>'"
  apply (induct \<psi> rule: propo_induct_arity)
  apply auto[2]
proof -
  fix \<psi>1 \<psi>2 \<phi>':: "'v propo"
  assume IH\<psi>1: "\<psi>1 \<preceq> \<phi> \<Longrightarrow> \<not> c_in_c'_symb c c' \<psi>1 \<Longrightarrow> Ex (push_conn_inside c c' \<psi>1)"
  and IH\<psi>2: "\<psi>1 \<preceq> \<phi> \<Longrightarrow> \<not> c_in_c'_symb c c' \<psi>1 \<Longrightarrow> Ex (push_conn_inside c c' \<psi>1)"
  and \<phi>': "\<phi>' = FAnd \<psi>1 \<psi>2 \<or> \<phi>' = FOr \<psi>1 \<psi>2 \<or> \<phi>' = FImp \<psi>1 \<psi>2 \<or> \<phi>' = FEq \<psi>1 \<psi>2"
  and in\<phi>: "\<phi>' \<preceq> \<phi>" and n0: "\<not>c_in_c'_symb c c' \<phi>'"
  then have n: "not_c_in_c'_symb c c' \<phi>'" by auto
  {
    assume \<phi>': "\<phi>' = conn c [\<psi>1, \<psi>2]"
    obtain a b where "\<psi>1 = conn c' [a, b] \<or> \<psi>2 = conn c' [a, b]"
      using n \<phi>' apply (induct rule: not_c_in_c'_symb.induct)
      using c by force+
    then have "Ex (push_conn_inside c c' \<phi>')"
      unfolding \<phi>' apply auto
      using push_conn_inside.intros(1) c c' apply blast
      using push_conn_inside.intros(2) c c' by blast
  }
  moreover {
     assume \<phi>': "\<phi>' \<noteq> conn c [\<psi>1, \<psi>2]"
     have "\<forall>\<phi> c ca. \<exists>\<phi>1 \<psi>1 \<psi>2 \<psi>1' \<psi>2' \<phi>2'. conn (c::'v connective) [\<phi>1, conn ca [\<psi>1, \<psi>2]] = \<phi>
             \<or> conn c [conn ca [\<psi>1', \<psi>2'], \<phi>2'] = \<phi> \<or> c_in_c'_symb c ca \<phi>"
       by (metis not_c_in_c'_symb.cases)
     then have "Ex (push_conn_inside c c' \<phi>')"
       by (metis (no_types) c c' n push_conn_inside_l push_conn_inside_r)
  }
  ultimately show "Ex (push_conn_inside c c' \<phi>')" by blast
qed


lemma c_in_c'_symb_rew:
  fixes \<phi> :: "'v propo"
  assumes noTB: "\<not>c_in_c'_only c c' \<phi>"
  and c: "c = CAnd \<or> c = COr" and c': "c' = CAnd \<or> c' = COr"
  shows "\<exists>\<psi> \<psi>'. \<psi> \<preceq> \<phi> \<and> push_conn_inside c c' \<psi> \<psi>' "
proof -
  have test_symb_false_nullary:
    "\<forall>x. c_in_c'_symb c c' (FF:: 'v propo) \<and> c_in_c'_symb c c' FT
      \<and> c_in_c'_symb c c' (FVar (x:: 'v))"
    by auto
  moreover {
    fix x :: "'v"
    have H': "c_in_c'_symb c c' FT" "c_in_c'_symb c c' FF" "c_in_c'_symb c c' (FVar x)"
      by simp+
  }
  moreover {
    fix \<psi> :: "'v propo"
    have "\<psi> \<preceq> \<phi> \<Longrightarrow> \<not> c_in_c'_symb c c' \<psi> \<Longrightarrow> \<exists>\<psi>'. push_conn_inside c c' \<psi> \<psi>'"
      by (auto simp: assms(2) c' c_in_c'_symb_step_exists)
  }
  ultimately show ?thesis using noTB no_test_symb_step_exists[of "c_in_c'_symb c c'"]
    unfolding c_in_c'_only_def by metis
qed

lemma push_conn_insidec_in_c'_symb_no_T_F:
  fixes \<phi> \<psi> :: "'v propo"
  shows "propo_rew_step (push_conn_inside c c') \<phi> \<psi> \<Longrightarrow> no_T_F \<phi> \<Longrightarrow> no_T_F \<psi>"
proof (induct rule: propo_rew_step.induct)
  case (global_rel \<phi> \<psi>)
  then show "no_T_F \<psi>"
    by (cases rule: push_conn_inside.cases, auto)
next
  case (propo_rew_one_step_lift \<phi> \<phi>' c \<xi> \<xi>')
  note rel = this(1) and IH = this(2) and wf = this(3) and no_T_F = this(4)
  have "no_T_F \<phi>"
    using wf no_T_F no_T_F_def subformula_into_subformula subformula_all_subformula_st
    subformula_refl by (metis (no_types) in_set_conv_decomp)
  then have \<phi>': "no_T_F \<phi>'" using IH by blast

  have "\<forall>\<zeta> \<in> set (\<xi> @ \<phi> # \<xi>'). no_T_F \<zeta>" by (metis wf no_T_F no_T_F_def all_subformula_st_decomp)
  then have n: "\<forall>\<zeta> \<in> set (\<xi> @ \<phi>' # \<xi>'). no_T_F \<zeta>" using \<phi>' by auto
  then have n': "\<forall>\<zeta> \<in> set (\<xi> @ \<phi>' # \<xi>'). \<zeta> \<noteq>  FF \<and> \<zeta> \<noteq> FT"
    using \<phi>' by (metis no_T_F_symb_false(1) no_T_F_symb_false(2) no_T_F_def
      all_subformula_st_test_symb_true_phi)

  have wf': "wf_conn c (\<xi> @ \<phi>' # \<xi>')"
    using wf wf_conn_no_arity_change by (metis wf_conn_no_arity_change_helper)
  {
    fix x :: "'v"
    assume "c = CT \<or> c = CF \<or> c = CVar x"
    then have "False" using wf by auto
    then have "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))" by blast
  }
  moreover {
    assume c: "c = CNot"
    then have "\<xi> = []" "\<xi>' = []" using wf by auto
    then have "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))"
      using c by (metis \<phi>' conn.simps(4) no_T_F_symb_false(1,2) no_T_F_symb_fnot no_T_F_def
        all_subformula_st_decomp_explicit(3) all_subformula_st_test_symb_true_phi self_append_conv2)
  }
  moreover {
    assume c: "c \<in> binary_connectives"
    then have "no_T_F_symb (conn c (\<xi> @ \<phi>' # \<xi>'))" using wf' n' no_T_F_symb.simps by fastforce
    then have "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))"
      by (metis all_subformula_st_decomp_imp wf' n no_T_F_def)
  }
  ultimately show "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))" using connective_cases_arity by auto
qed


lemma simple_propo_rew_step_push_conn_inside_inv:
"propo_rew_step (push_conn_inside c c') \<phi> \<psi> \<Longrightarrow> simple \<phi> \<Longrightarrow> simple \<psi>"
  apply (induct rule: propo_rew_step.induct)
  apply (rename_tac \<phi>, case_tac \<phi>, auto simp: push_conn_inside.simps)[]
  by (metis append_is_Nil_conv list.distinct(1) simple.elims(2) wf_conn_list(1-3))


lemma simple_propo_rew_step_inv_push_conn_inside_simple_not:
  fixes c c' :: "'v connective" and \<phi> \<psi> :: "'v propo"
  shows "propo_rew_step (push_conn_inside c c') \<phi> \<psi> \<Longrightarrow> simple_not \<phi> \<Longrightarrow> simple_not \<psi>"
proof (induct rule: propo_rew_step.induct)
  case (global_rel \<phi> \<psi>)
  then show ?case by (cases \<phi>, auto simp: push_conn_inside.simps)
next
  case (propo_rew_one_step_lift \<phi> \<phi>' ca \<xi> \<xi>') note rew = this(1) and IH = this(2) and wf = this(3)
   and simple = this(4)
  show ?case
    proof (cases ca rule: connective_cases_arity)
      case nullary
      then show ?thesis using propo_rew_one_step_lift by auto
    next
      case binary note ca = this
      obtain a b where ab: "\<xi> @ \<phi>' # \<xi>' = [a, b]"
        using wf ca list_length2_decomp wf_conn_bin_list_length
        by (metis (no_types) wf_conn_no_arity_change_helper)
      have "\<forall>\<zeta> \<in> set (\<xi> @ \<phi> # \<xi>'). simple_not \<zeta>"
        by (metis wf all_subformula_st_decomp simple simple_not_def)
      then have "\<forall>\<zeta> \<in> set (\<xi> @ \<phi>' # \<xi>'). simple_not \<zeta>" using IH by simp
      moreover have "simple_not_symb (conn ca (\<xi> @ \<phi>' # \<xi>'))" using ca
      by (metis ab conn.simps(5-8) helper_fact simple_not_symb.simps(5) simple_not_symb.simps(6)
          simple_not_symb.simps(7) simple_not_symb.simps(8))
      ultimately show ?thesis
        by (simp add: ab all_subformula_st_decomp ca)
    next
      case unary
      then show ?thesis
         using rew simple_propo_rew_step_push_conn_inside_inv[OF rew] IH local.wf simple by auto
    qed
qed

lemma propo_rew_step_push_conn_inside_simple_not:
  fixes \<phi> \<phi>' :: "'v propo" and \<xi> \<xi>' :: "'v propo list" and c :: "'v connective"
  assumes
    "propo_rew_step (push_conn_inside c c') \<phi> \<phi>'" and
    "wf_conn c (\<xi> @ \<phi> # \<xi>')" and
    "simple_not_symb (conn c (\<xi> @ \<phi> # \<xi>'))" and
    "simple_not_symb \<phi>'"
  shows "simple_not_symb (conn c (\<xi> @ \<phi>' # \<xi>'))"
  using assms
proof (induction rule: propo_rew_step.induct)
print_cases
  case (global_rel)
  then show ?case
    by (metis conn.simps(12,17) list.discI push_conn_inside.cases simple_not_symb.elims(3)
      wf_conn_helper_facts(5) wf_conn_list(2) wf_conn_list(8) wf_conn_no_arity_change
      wf_conn_no_arity_change_helper)
next
  case (propo_rew_one_step_lift \<phi> \<phi>' c' \<chi>s \<chi>s') note tel = this(1) and wf = this(2) and
    IH = this(3) and wf' = this(4) and simple' = this(5) and simple = this(6)
  then show ?case
    proof (cases c' rule: connective_cases_arity)
      case nullary
      then show ?thesis using wf simple simple' by auto
    next
      case binary note c = this(1)
      have corr': "wf_conn c (\<xi> @ conn c' (\<chi>s @ \<phi>' # \<chi>s') # \<xi>')"
        using wf wf_conn_no_arity_change
        by (metis wf' wf_conn_no_arity_change_helper)
      then show ?thesis
        using c propo_rew_one_step_lift wf
        by (metis conn.simps(17) connective.distinct(37) propo_rew_step_subformula_imp
          push_conn_inside.cases simple_not_symb.elims(3) wf_conn.simps wf_conn_list(2,8))
    next
      case unary
      then have empty: "\<chi>s = []" "\<chi>s' = []" using wf by auto
      then show ?thesis using simple unary simple' wf wf'
        by (metis connective.distinct(37) connective.distinct(39) propo_rew_step_subformula_imp
          push_conn_inside.cases simple_not_symb.elims(3) tel wf_conn_list(8)
          wf_conn_no_arity_change wf_conn_no_arity_change_helper)
    qed
qed

lemma push_conn_inside_not_true_false:
  "push_conn_inside c c' \<phi> \<psi> \<Longrightarrow> \<psi> \<noteq> FT \<and> \<psi> \<noteq> FF"
  by (induct rule: push_conn_inside.induct, auto)

lemma push_conn_inside_inv:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "full (propo_rew_step (push_conn_inside c c')) \<phi> \<psi>"
  and "no_equiv \<phi>" and "no_imp \<phi>" and "no_T_F_except_top_level \<phi>" and "simple_not \<phi>"
  shows "no_equiv \<psi>" and "no_imp \<psi>" and "no_T_F_except_top_level \<psi>" and "simple_not \<psi>"
proof -
  {
     {
        fix \<phi> \<psi> :: "'v propo"
        have H: "push_conn_inside c c' \<phi> \<psi> \<Longrightarrow> all_subformula_st simple_not_symb \<phi>
          \<Longrightarrow> all_subformula_st simple_not_symb \<psi>"
          by (induct \<phi> \<psi> rule: push_conn_inside.induct, auto)
     } note H = this

    fix \<phi> \<psi> :: "'v propo"
    have H: "propo_rew_step (push_conn_inside c c') \<phi> \<psi> \<Longrightarrow> all_subformula_st simple_not_symb \<phi>
      \<Longrightarrow> all_subformula_st simple_not_symb \<psi>"
      apply (induct \<phi> \<psi> rule: propo_rew_step.induct)
      using H apply simp
      proof (rename_tac \<phi> \<phi>' ca \<psi>s \<psi>s', case_tac ca rule: connective_cases_arity)
        fix \<phi> \<phi>' :: "'v propo" and c:: "'v connective" and \<xi> \<xi>':: "'v propo list"
        and x:: "'v"
        assume "wf_conn c (\<xi> @ \<phi> # \<xi>')"
        and " c = CT \<or> c = CF \<or> c = CVar x"
        then have "\<xi> @ \<phi> # \<xi>' = []" by auto
        then have False by auto
        then show "all_subformula_st simple_not_symb (conn c (\<xi> @ \<phi>' # \<xi>'))" by blast
      next
        fix \<phi> \<phi>' :: "'v propo" and ca:: "'v connective" and \<xi> \<xi>':: "'v propo list"
        and x :: "'v"
        assume rel: "propo_rew_step (push_conn_inside c c') \<phi> \<phi>'"
        and \<phi>_\<phi>': "all_subformula_st simple_not_symb \<phi> \<Longrightarrow> all_subformula_st simple_not_symb \<phi>'"
        and corr: "wf_conn ca (\<xi> @ \<phi> # \<xi>')"
        and n: "all_subformula_st simple_not_symb (conn ca (\<xi> @ \<phi> # \<xi>'))"
        and c: "ca = CNot"

        have empty: "\<xi> = []" "\<xi>' = []" using c corr by auto
        then have simple_not:"all_subformula_st simple_not_symb (FNot \<phi>)" using corr c n by auto
        then have "simple \<phi>"
          using all_subformula_st_test_symb_true_phi simple_not_symb.simps(1) by blast
        then have "simple \<phi>'"
          using rel simple_propo_rew_step_push_conn_inside_inv by blast
        then show "all_subformula_st simple_not_symb (conn ca (\<xi> @ \<phi>' # \<xi>'))" using c empty
          by (metis simple_not \<phi>_\<phi>' append_Nil conn.simps(4) all_subformula_st_decomp_explicit(3)
            simple_not_symb.simps(1))
      next
        fix \<phi> \<phi>' :: "'v propo" and ca :: "'v connective" and \<xi> \<xi>' :: "'v propo list"
        and x :: "'v"
        assume rel: "propo_rew_step (push_conn_inside c c') \<phi> \<phi>'"
        and n\<phi>: "all_subformula_st simple_not_symb \<phi> \<Longrightarrow>  all_subformula_st simple_not_symb \<phi>'"
        and corr: "wf_conn ca (\<xi> @ \<phi> # \<xi>')"
        and n: "all_subformula_st simple_not_symb (conn ca (\<xi> @ \<phi> # \<xi>'))"
        and c: "ca \<in> binary_connectives"

        have "all_subformula_st simple_not_symb \<phi>"
          using n c corr all_subformula_st_decomp by fastforce
        then have \<phi>': " all_subformula_st simple_not_symb \<phi>'" using n\<phi> by blast
        obtain a b where ab: "[a, b] = (\<xi> @ \<phi> # \<xi>')"
          using corr c list_length2_decomp wf_conn_bin_list_length by metis
        then have "\<xi> @ \<phi>' # \<xi>' = [a, \<phi>'] \<or> (\<xi> @ \<phi>' # \<xi>') = [\<phi>', b]"
          using ab by (metis (no_types, hide_lams) append_Cons append_Nil append_Nil2
            append_is_Nil_conv butlast.simps(2) butlast_append list.sel(3) tl_append2)
        moreover
        {
           fix \<chi> :: "'v propo"
           have wf': "wf_conn ca [a, b]"
             using ab corr by presburger
           have "all_subformula_st simple_not_symb (conn ca [a, b])"
             using ab n by presburger
           then have "all_subformula_st simple_not_symb \<chi> \<or> \<chi> \<notin> set (\<xi> @ \<phi>' # \<xi>')"
             using wf' by (metis (no_types) \<phi>' all_subformula_st_decomp calculation insert_iff
               list.set(2))
        }
        then have "\<forall>\<phi>. \<phi> \<in> set (\<xi> @ \<phi>' # \<xi>') \<longrightarrow> all_subformula_st simple_not_symb \<phi>"
            by (metis (no_types))

        moreover have "simple_not_symb (conn ca (\<xi> @ \<phi>' # \<xi>'))"
          using ab conn_inj_not(1) corr wf_conn_list_decomp(4) wf_conn_no_arity_change
            not_Cons_self2 self_append_conv2 simple_not_symb.elims(3) by (metis (no_types) c
            calculation(1) wf_conn_binary)
        moreover have "wf_conn ca (\<xi> @ \<phi>' # \<xi>')" using c calculation(1) by auto
        ultimately show "all_subformula_st simple_not_symb (conn ca (\<xi> @ \<phi>' # \<xi>'))"
          by (metis all_subformula_st_decomp_imp)
      qed
  }
  moreover {
     fix ca :: "'v connective" and \<xi> \<xi>' :: "'v propo list" and \<phi> \<phi>' :: "'v propo"
     have "propo_rew_step (push_conn_inside c c') \<phi> \<phi>' \<Longrightarrow> wf_conn ca (\<xi> @ \<phi> # \<xi>')
       \<Longrightarrow> simple_not_symb (conn ca (\<xi> @ \<phi> # \<xi>')) \<Longrightarrow> simple_not_symb \<phi>'
       \<Longrightarrow> simple_not_symb (conn ca (\<xi> @ \<phi>' # \<xi>'))"
       by (metis append_self_conv2 conn.simps(4) conn_inj_not(1) simple_not_symb.elims(3)
         simple_not_symb.simps(1) simple_propo_rew_step_push_conn_inside_inv
         wf_conn_no_arity_change_helper wf_conn_list_decomp(4) wf_conn_no_arity_change)
  }
  ultimately show "simple_not \<psi>"
    using full_propo_rew_step_inv_stay'[of "push_conn_inside c c'" "simple_not_symb"] assms
    unfolding no_T_F_except_top_level_def simple_not_def full_unfold by metis
next
  {
    fix \<phi> \<psi> :: "'v propo"
    have H: "propo_rew_step (push_conn_inside c c') \<phi> \<psi> \<Longrightarrow> no_T_F_except_top_level \<phi>
      \<Longrightarrow>  no_T_F_except_top_level \<psi>"
      proof -
        assume rel: "propo_rew_step (push_conn_inside c c') \<phi> \<psi>"
        and "no_T_F_except_top_level \<phi>"
        then have "no_T_F \<phi> \<or> \<phi> = FF \<or> \<phi> = FT"
          by (metis no_T_F_symb_except_toplevel_all_subformula_st_no_T_F_symb)
        moreover {
          assume "\<phi> = FF \<or> \<phi> = FT"
          then have False using rel propo_rew_step_push_conn_inside by blast
          then have "no_T_F_except_top_level \<psi>" by blast
        }
        moreover {
          assume "no_T_F \<phi> \<and> \<phi> \<noteq> FF \<and> \<phi> \<noteq> FT"
          then have "no_T_F \<psi>" using rel push_conn_insidec_in_c'_symb_no_T_F by blast
          then have "no_T_F_except_top_level \<psi>" using no_T_F_no_T_F_except_top_level by blast
        }
        ultimately show "no_T_F_except_top_level \<psi>" by blast
      qed
  }
  moreover {
     fix ca :: "'v connective" and \<xi> \<xi>' :: "'v propo list" and \<phi> \<phi>' :: "'v propo"
     assume rel: "propo_rew_step (push_conn_inside c c') \<phi> \<phi>'"
     assume corr: "wf_conn ca (\<xi> @ \<phi> # \<xi>')"
     then have c: "ca \<noteq> CT \<and> ca \<noteq> CF" by auto
     assume no_T_F: "no_T_F_symb_except_toplevel (conn ca (\<xi> @ \<phi> # \<xi>'))"
     have "no_T_F_symb_except_toplevel (conn ca (\<xi> @ \<phi>' # \<xi>'))"
     proof
       have c: "ca \<noteq> CT \<and> ca \<noteq> CF" using corr by auto
       have \<zeta>: "\<forall>\<zeta>\<in> set (\<xi> @ \<phi> # \<xi>'). \<zeta>\<noteq>FT \<and> \<zeta> \<noteq> FF"
         using corr no_T_F no_T_F_symb_except_toplevel_if_is_a_true_false by blast
       then have "\<phi> \<noteq> FT \<and> \<phi> \<noteq> FF" by auto
       from rel this have "\<phi>' \<noteq> FT \<and> \<phi>' \<noteq> FF"
         apply (induct rule: propo_rew_step.induct)
         by (metis append_is_Nil_conv conn.simps(2) conn_inj list.distinct(1)
           wf_conn_helper_facts(3) wf_conn_list(1) wf_conn_no_arity_change
           wf_conn_no_arity_change_helper push_conn_inside_not_true_false)+
       then have "\<forall>\<zeta> \<in> set (\<xi> @ \<phi>' # \<xi>'). \<zeta> \<noteq> FT \<and> \<zeta> \<noteq> FF" using \<zeta> by auto
       moreover have "wf_conn ca (\<xi> @ \<phi>' # \<xi>')"
         using corr wf_conn_no_arity_change by (metis wf_conn_no_arity_change_helper)
       ultimately show "no_T_F_symb (conn ca (\<xi> @ \<phi>' # \<xi>'))" using no_T_F_symb.intros c by metis
     qed
  }
  ultimately show "no_T_F_except_top_level \<psi>"
    using full_propo_rew_step_inv_stay'[of "push_conn_inside c c'" "no_T_F_symb_except_toplevel"]
    assms unfolding no_T_F_except_top_level_def full_unfold by metis

next
  {
    fix \<phi> \<psi> :: "'v propo"
    have H: "push_conn_inside c c' \<phi> \<psi> \<Longrightarrow> no_equiv \<phi> \<Longrightarrow> no_equiv \<psi>"
      by (induct \<phi> \<psi> rule: push_conn_inside.induct, auto)
  }
  then show "no_equiv \<psi>"
    using full_propo_rew_step_inv_stay_conn[of "push_conn_inside c c'" no_equiv_symb] assms
    no_equiv_symb_conn_characterization unfolding no_equiv_def by metis

next
  {
    fix \<phi> \<psi> :: "'v propo"
    have H: "push_conn_inside c c' \<phi> \<psi> \<Longrightarrow> no_imp \<phi> \<Longrightarrow>  no_imp \<psi>"
      by (induct \<phi> \<psi> rule: push_conn_inside.induct, auto)
  }
  then show "no_imp \<psi>"
    using full_propo_rew_step_inv_stay_conn[of "push_conn_inside c c'" no_imp_symb] assms
    no_imp_symb_conn_characterization unfolding no_imp_def by metis
qed


lemma push_conn_inside_full_propo_rew_step:
  fixes \<phi> \<psi> :: "'v propo"
  assumes
    "no_equiv \<phi>" and
    "no_imp \<phi>" and
    "full (propo_rew_step (push_conn_inside c c')) \<phi> \<psi>" and
    "no_T_F_except_top_level \<phi>" and
    "simple_not \<phi>" and
    "c = CAnd \<or> c = COr" and
    "c' = CAnd \<or> c' = COr"
  shows "c_in_c'_only c c' \<psi>"
  using c_in_c'_symb_rew assms full_propo_rew_step_subformula by blast


subsubsection \<open>Only one type of connective in the formula (+ not)\<close>
inductive only_c_inside_symb :: "'v connective \<Rightarrow> 'v propo \<Rightarrow> bool" for c :: "'v connective" where
simple_only_c_inside[simp]: "simple \<phi> \<Longrightarrow>  only_c_inside_symb c \<phi>" |
simple_cnot_only_c_inside[simp]: "simple \<phi> \<Longrightarrow>  only_c_inside_symb c (FNot \<phi>)" |
only_c_inside_into_only_c_inside: "wf_conn c l \<Longrightarrow> only_c_inside_symb c (conn c l)"


lemma only_c_inside_symb_simp[simp]:
  "only_c_inside_symb c FF" "only_c_inside_symb c FT" "only_c_inside_symb c (FVar x)" by auto


definition only_c_inside where "only_c_inside c = all_subformula_st (only_c_inside_symb c)"

lemma only_c_inside_symb_decomp:
  "only_c_inside_symb c \<psi> \<longleftrightarrow> (simple \<psi>
                                \<or> (\<exists> \<phi>'. \<psi> = FNot \<phi>' \<and> simple \<phi>')
                                \<or> (\<exists>l. \<psi> = conn c l \<and> wf_conn c l))"
  by (auto simp: only_c_inside_symb.intros(3)) (induct rule: only_c_inside_symb.induct, auto)

lemma only_c_inside_symb_decomp_not[simp]:
  fixes c :: "'v connective"
  assumes c: "c \<noteq> CNot"
  shows "only_c_inside_symb c (FNot \<psi>) \<longleftrightarrow> simple \<psi>"
  apply (auto simp: only_c_inside_symb.intros(3))
  by (induct "FNot \<psi>" rule: only_c_inside_symb.induct, auto simp: wf_conn_list(8) c)

lemma only_c_inside_decomp_not[simp]:
  assumes c: "c \<noteq> CNot"
  shows "only_c_inside c (FNot \<psi>) \<longleftrightarrow> simple \<psi>"
  by (metis (no_types, hide_lams) all_subformula_st_def all_subformula_st_test_symb_true_phi c
    only_c_inside_def only_c_inside_symb_decomp_not simple_only_c_inside
    subformula_conn_decomp_simple)


lemma only_c_inside_decomp:
  "only_c_inside c \<phi> \<longleftrightarrow>
    (\<forall>\<psi>. \<psi> \<preceq> \<phi> \<longrightarrow> (simple \<psi> \<or> (\<exists> \<phi>'. \<psi> = FNot \<phi>' \<and> simple \<phi>')
                    \<or> (\<exists>l. \<psi> = conn c l \<and> wf_conn c l)))"
  unfolding only_c_inside_def by (auto simp: all_subformula_st_def only_c_inside_symb_decomp)

lemma only_c_inside_c_c'_false:
  fixes c c' :: "'v connective" and l :: "'v propo list" and \<phi> :: "'v propo"
  assumes cc': "c \<noteq> c'" and c: "c = CAnd \<or> c = COr" and c': "c' = CAnd \<or> c' = COr"
  and only: "only_c_inside c \<phi>" and incl: "conn c' l \<preceq> \<phi>" and wf: "wf_conn c' l"
  shows False
proof -
  let ?\<psi> = "conn c' l"
  have "simple ?\<psi> \<or> (\<exists> \<phi>'. ?\<psi> = FNot \<phi>' \<and> simple \<phi>') \<or> (\<exists>l. ?\<psi> = conn c l \<and> wf_conn c l)"
    using only_c_inside_decomp only incl by blast
  moreover have "\<not> simple ?\<psi>"
    using wf simple_decomp by (metis c' connective.distinct(19) connective.distinct(7,9,21,29,31)
      wf_conn_list(1-3))
  moreover
    {
      fix \<phi>'
      have "?\<psi> \<noteq> FNot \<phi>'" using c' conn_inj_not(1) wf by blast
    }
  ultimately obtain l :: "'v propo list" where "?\<psi> = conn c l \<and> wf_conn c l" by metis
  then have "c = c'" using conn_inj wf by metis
  then show False using cc' by auto
qed

lemma only_c_inside_implies_c_in_c'_symb:
  assumes \<delta>: "c \<noteq> c'" and c: "c = CAnd \<or> c = COr" and c': "c' = CAnd \<or> c' = COr"
  shows "only_c_inside c \<phi> \<Longrightarrow> c_in_c'_symb c c' \<phi>"
  apply (rule ccontr)
  apply (cases rule: not_c_in_c'_symb.cases, auto)
  by (metis \<delta> c c' connective.distinct(37,39) list.distinct(1) only_c_inside_c_c'_false
    subformula_in_binary_conn(1,2) wf_conn.simps)+

lemma c_in_c'_symb_decomp_level1:
  fixes l :: "'v propo list" and c c' ca :: "'v connective"
  shows "wf_conn ca l \<Longrightarrow> ca \<noteq> c \<Longrightarrow> c_in_c'_symb c c' (conn ca l)"
proof -
  have "not_c_in_c'_symb c c' (conn ca l) \<Longrightarrow>  wf_conn ca l \<Longrightarrow> ca = c"
    by (induct "conn ca l" rule: not_c_in_c'_symb.induct, auto simp: conn_inj)
  then show "wf_conn ca l \<Longrightarrow> ca \<noteq> c \<Longrightarrow> c_in_c'_symb c c' (conn ca l)" by blast
qed


lemma only_c_inside_implies_c_in_c'_only:
  assumes \<delta>: "c \<noteq> c'" and c: "c = CAnd \<or> c = COr" and c': "c' = CAnd \<or> c' = COr"
  shows "only_c_inside c \<phi> \<Longrightarrow> c_in_c'_only c c' \<phi>"
  unfolding c_in_c'_only_def all_subformula_st_def
  using only_c_inside_implies_c_in_c'_symb
    by (metis all_subformula_st_def assms(1) c c' only_c_inside_def subformula_trans)


lemma c_in_c'_symb_c_implies_only_c_inside:
  assumes \<delta>: "c = CAnd \<or> c = COr" "c' = CAnd \<or> c' = COr" "c \<noteq> c'" and wf: "wf_conn c [\<phi>, \<psi>]"
  and inv: "no_equiv (conn c l)" "no_imp (conn c l)" "simple_not (conn c l)"
  shows "wf_conn c l \<Longrightarrow> c_in_c'_only c c' (conn c l) \<Longrightarrow> (\<forall>\<psi>\<in> set l. only_c_inside c \<psi>)"
using inv
proof (induct "conn c l" arbitrary: l rule: propo_induct_arity)
  case (nullary x)
  then show ?case by (auto simp: wf_conn_list assms)
next
  case (unary \<phi> la)
  then have "c = CNot \<and> la = [\<phi>]" by (metis (no_types) wf_conn_list(8))
  then show ?case using assms(2) assms(1) by blast
next
  case (binary \<phi>1 \<phi>2)
  note IH\<phi>1 = this(1) and IH\<phi>2 = this(2) and \<phi> = this(3) and only = this(5) and wf = this(4)
    and no_equiv = this(6) and no_imp = this(7) and simple_not = this(8)
  then have l: "l = [\<phi>1, \<phi>2]" by (meson wf_conn_list(4-7))
  let ?\<phi> = "conn c l"

  obtain c1 l1 c2 l2 where \<phi>1: "\<phi>1 = conn c1 l1" and wf\<phi>1: "wf_conn c1 l1"
    and \<phi>2: "\<phi>2 = conn c2 l2" and wf\<phi>2: "wf_conn c2 l2" using exists_c_conn by metis
  then have c_in_only\<phi>1: "c_in_c'_only c c' (conn c1 l1)" and "c_in_c'_only c c' (conn c2 l2)"
    using only l unfolding c_in_c'_only_def using assms(1) by auto
  have inc\<phi>1: "\<phi>1 \<preceq> ?\<phi>" and inc\<phi>2: "\<phi>2 \<preceq> ?\<phi>"
    using \<phi>1 \<phi>2 \<phi> local.wf by (metis conn.simps(5-8) helper_fact subformula_in_binary_conn(1,2))+

  have c1_eq: "c1 \<noteq> CEq" and c2_eq: "c2 \<noteq> CEq"
    unfolding no_equiv_def using inc\<phi>1 inc\<phi>2 by (metis \<phi>1 \<phi>2 wf\<phi>1 wf\<phi>2 assms(1) no_equiv
      no_equiv_eq(1) no_equiv_symb.elims(3) no_equiv_symb_conn_characterization wf_conn_list(4,5)
      no_equiv_def subformula_all_subformula_st)+
  have c1_imp: "c1 \<noteq> CImp" and c2_imp: "c2 \<noteq> CImp"
    using no_imp by (metis \<phi>1 \<phi>2 all_subformula_st_decomp_explicit_imp(2,3) assms(1)
      conn.simps(5,6) l no_imp_Imp(1) no_imp_symb.elims(3) no_imp_symb_conn_characterization
      wf\<phi>1 wf\<phi>2 all_subformula_st_decomp no_imp_symb_conn_characterization)+
  have c1c: "c1 \<noteq> c'"
    proof
      assume c1c: "c1 = c'"
      then obtain \<xi>1 \<xi>2 where l1: "l1 = [\<xi>1, \<xi>2]"
        by (metis assms(2) connective.distinct(37,39) helper_fact wf\<phi>1 wf_conn.simps
          wf_conn_list_decomp(1-3))
      have "c_in_c'_only c c' (conn c [conn c' l1, \<phi>2])" using c1c l only \<phi>1 by auto
      moreover have "not_c_in_c'_symb c c' (conn c [conn c' l1, \<phi>2])"
        using l1 \<phi>1 c1c l local.wf not_c_in_c'_symb_l wf\<phi>1 by blast
      ultimately show False using \<phi>1 c1c l l1 local.wf not_c_in_c'_simp(4) wf\<phi>1 by blast
   qed
  then have "(\<phi>1 = conn c l1 \<and> wf_conn c l1) \<or> (\<exists>\<psi>1. \<phi>1 = FNot \<psi>1) \<or> simple \<phi>1"
    by (metis \<phi>1 assms(1-3) c1_eq c1_imp simple.elims(3) wf\<phi>1 wf_conn_list(4) wf_conn_list(5-7))
  moreover {
    assume "\<phi>1 = conn c l1 \<and> wf_conn c l1"
    then have "only_c_inside c \<phi>1"
      by (metis IH\<phi>1 \<phi>1 all_subformula_st_decomp_imp inc\<phi>1 no_equiv no_equiv_def no_imp no_imp_def
        c_in_only\<phi>1 only_c_inside_def only_c_inside_into_only_c_inside simple_not simple_not_def
        subformula_all_subformula_st)
  }
  moreover {
    assume "\<exists>\<psi>1. \<phi>1 = FNot \<psi>1"
    then obtain \<psi>1 where "\<phi>1 = FNot \<psi>1" by metis
    then have "only_c_inside c \<phi>1"
      by (metis all_subformula_st_def assms(1) connective.distinct(37,39) inc\<phi>1
        only_c_inside_decomp_not simple_not simple_not_def simple_not_symb.simps(1))
  }
  moreover {
    assume "simple \<phi>1"
    then have "only_c_inside c \<phi>1"
      by (metis all_subformula_st_decomp_explicit(3) assms(1) connective.distinct(37,39)
        only_c_inside_decomp_not only_c_inside_def)
  }
  ultimately have only_c_inside\<phi>1: "only_c_inside c \<phi>1" by metis

  have c_in_only\<phi>2: "c_in_c'_only c c' (conn c2 l2)"
    using only l \<phi>2 wf\<phi>2 assms unfolding c_in_c'_only_def by auto
  have c2c: "c2 \<noteq> c'"
    proof
      assume c2c: "c2 = c'"
      then obtain \<xi>1 \<xi>2 where l2: "l2 = [\<xi>1, \<xi>2]"
       by (metis assms(2) wf\<phi>2 wf_conn.simps connective.distinct(7,9,19,21,29,31,37,39))
      then have "c_in_c'_symb c c' (conn c [\<phi>1, conn c' l2])"
        using c2c l only \<phi>2 all_subformula_st_test_symb_true_phi unfolding c_in_c'_only_def by auto
      moreover have "not_c_in_c'_symb c c' (conn c [\<phi>1, conn c' l2])"
        using assms(1) c2c l2 not_c_in_c'_symb_r wf\<phi>2 wf_conn_helper_facts(5,6) by metis
      ultimately show False by auto
    qed
  then have "(\<phi>2 = conn c l2 \<and> wf_conn c l2) \<or> (\<exists>\<psi>2. \<phi>2 = FNot \<psi>2) \<or> simple \<phi>2"
    using c2_eq by (metis \<phi>2 assms(1-3) c2_eq c2_imp simple.elims(3) wf\<phi>2 wf_conn_list(4-7))
  moreover {
    assume "\<phi>2 = conn c l2 \<and> wf_conn c l2"
    then have "only_c_inside c \<phi>2"
      by (metis IH\<phi>2 \<phi>2 all_subformula_st_decomp inc\<phi>2 no_equiv no_equiv_def no_imp no_imp_def
        c_in_only\<phi>2 only_c_inside_def only_c_inside_into_only_c_inside simple_not simple_not_def
        subformula_all_subformula_st)
  }
  moreover {
    assume "\<exists>\<psi>2. \<phi>2 = FNot \<psi>2"
    then obtain \<psi>2 where "\<phi>2 = FNot \<psi>2" by metis
    then have "only_c_inside c \<phi>2"
      by (metis all_subformula_st_def assms(1-3) connective.distinct(38,40) inc\<phi>2
        only_c_inside_decomp_not simple_not simple_not_def simple_not_symb.simps(1))
  }
  moreover {
    assume "simple \<phi>2"
    then have "only_c_inside c \<phi>2"
      by (metis all_subformula_st_decomp_explicit(3) assms(1) connective.distinct(37,39)
        only_c_inside_decomp_not only_c_inside_def)
  }
  ultimately have only_c_inside\<phi>2: "only_c_inside c \<phi>2" by metis
  show ?case using l only_c_inside\<phi>1 only_c_inside\<phi>2 by auto
qed



subsubsection \<open>Push Conjunction\<close>

definition pushConj where "pushConj = push_conn_inside CAnd COr"

lemma pushConj_consistent: "preserve_models pushConj"
  unfolding pushConj_def by (simp add: push_conn_inside_consistent)

definition and_in_or_symb where "and_in_or_symb = c_in_c'_symb CAnd COr"

definition and_in_or_only where
"and_in_or_only = all_subformula_st (c_in_c'_symb CAnd COr)"

lemma pushConj_inv:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "full (propo_rew_step pushConj) \<phi> \<psi>"
  and "no_equiv \<phi>" and "no_imp \<phi>" and "no_T_F_except_top_level \<phi>" and "simple_not \<phi>"
  shows "no_equiv \<psi>" and "no_imp \<psi>" and "no_T_F_except_top_level \<psi>" and "simple_not \<psi>"
  using push_conn_inside_inv assms unfolding pushConj_def by metis+


lemma pushConj_full_propo_rew_step:
  fixes \<phi> \<psi> :: "'v propo"
  assumes
    "no_equiv \<phi>" and
    "no_imp \<phi>" and
    "full (propo_rew_step pushConj) \<phi> \<psi>" and
    "no_T_F_except_top_level \<phi>" and
    "simple_not \<phi>"
  shows "and_in_or_only \<psi>"
  using assms push_conn_inside_full_propo_rew_step
  unfolding pushConj_def and_in_or_only_def c_in_c'_only_def by (metis (no_types))



subsubsection \<open>Push Disjunction\<close>
definition pushDisj where "pushDisj = push_conn_inside COr CAnd"

lemma pushDisj_consistent: "preserve_models pushDisj"
  unfolding pushDisj_def by (simp add: push_conn_inside_consistent)

definition or_in_and_symb where "or_in_and_symb = c_in_c'_symb COr CAnd"

definition or_in_and_only where
"or_in_and_only = all_subformula_st (c_in_c'_symb COr CAnd)"


lemma not_or_in_and_only_or_and[simp]:
  "~or_in_and_only (FOr (FAnd \<psi>1 \<psi>2) \<phi>')"
  unfolding or_in_and_only_def
  by (metis all_subformula_st_test_symb_true_phi conn.simps(5-6) not_c_in_c'_symb_l
    wf_conn_helper_facts(5) wf_conn_helper_facts(6))

lemma pushDisj_inv:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "full (propo_rew_step pushDisj) \<phi> \<psi>"
  and "no_equiv \<phi>" and "no_imp \<phi>" and "no_T_F_except_top_level \<phi>" and "simple_not \<phi>"
  shows "no_equiv \<psi>" and "no_imp \<psi>" and "no_T_F_except_top_level \<psi>" and "simple_not \<psi>"
  using push_conn_inside_inv assms unfolding pushDisj_def by metis+

lemma pushDisj_full_propo_rew_step:
  fixes \<phi> \<psi> :: "'v propo"
  assumes
    "no_equiv \<phi>" and
    "no_imp \<phi>" and
    "full (propo_rew_step pushDisj) \<phi> \<psi>" and
    "no_T_F_except_top_level \<phi>" and
    "simple_not \<phi>"
  shows "or_in_and_only \<psi>"
  using assms push_conn_inside_full_propo_rew_step
  unfolding pushDisj_def or_in_and_only_def c_in_c'_only_def by (metis (no_types))


section \<open>The Full Transformations\<close>

subsection \<open>Abstract Definition\<close>

text \<open>The normal form is a super group of groups\<close>

inductive grouped_by :: "'a connective \<Rightarrow> 'a propo \<Rightarrow> bool" for c where
simple_is_grouped[simp]: "simple \<phi> \<Longrightarrow> grouped_by c \<phi>" |
simple_not_is_grouped[simp]: "simple \<phi> \<Longrightarrow> grouped_by c (FNot \<phi>)" |
connected_is_group[simp]: "grouped_by c \<phi> \<Longrightarrow>  grouped_by c \<psi> \<Longrightarrow> wf_conn c [\<phi>, \<psi>]
  \<Longrightarrow> grouped_by c (conn c [\<phi>, \<psi>])"

lemma simple_clause[simp]:
  "grouped_by c FT"
  "grouped_by c FF"
  "grouped_by c (FVar x)"
  "grouped_by c (FNot FT)"
  "grouped_by c (FNot FF)"
  "grouped_by c (FNot (FVar x))"
  by simp+

lemma only_c_inside_symb_c_eq_c':
  "only_c_inside_symb c (conn c' [\<phi>1, \<phi>2]) \<Longrightarrow> c' = CAnd \<or> c' = COr \<Longrightarrow> wf_conn c' [\<phi>1, \<phi>2]
    \<Longrightarrow> c' = c"
  by (induct "conn c' [\<phi>1, \<phi>2]" rule: only_c_inside_symb.induct, auto simp: conn_inj)


lemma only_c_inside_c_eq_c':
  "only_c_inside c (conn c' [\<phi>1, \<phi>2]) \<Longrightarrow>  c' = CAnd \<or> c' = COr \<Longrightarrow> wf_conn c' [\<phi>1, \<phi>2] \<Longrightarrow> c = c'"
  unfolding only_c_inside_def all_subformula_st_def using only_c_inside_symb_c_eq_c' subformula_refl
  by blast

lemma only_c_inside_imp_grouped_by:
  assumes c: "c \<noteq> CNot" and c': "c' = CAnd \<or> c' = COr"
  shows "only_c_inside c \<phi> \<Longrightarrow> grouped_by c \<phi>" (is "?O \<phi> \<Longrightarrow> ?G \<phi>")
proof (induct \<phi> rule: propo_induct_arity)
  case (nullary \<phi> x)
  then show "?G \<phi>" by auto
next
  case (unary \<psi>)
  then show "?G (FNot \<psi>)" by (auto simp: c)
next
  case (binary \<phi> \<phi>1 \<phi>2)
  note IH\<phi>1 = this(1) and IH\<phi>2 = this(2) and \<phi> = this(3) and only = this(4)
  have \<phi>_conn: "\<phi> = conn c [\<phi>1, \<phi>2]" and wf: "wf_conn c [\<phi>1, \<phi>2]"
    proof -
      obtain c'' l'' where \<phi>_c'': "\<phi> = conn c'' l''" and wf: "wf_conn c'' l''"
        using exists_c_conn by metis
      then have l'': "l'' = [\<phi>1, \<phi>2]" using \<phi> by (metis wf_conn_list(4-7))
      have "only_c_inside_symb c (conn c'' [\<phi>1, \<phi>2])"
        using only all_subformula_st_test_symb_true_phi
        unfolding only_c_inside_def \<phi>_c'' l'' by metis
      then have "c = c''"
        by (metis \<phi> \<phi>_c'' conn_inj conn_inj_not(2) l'' list.distinct(1) list.inject wf
          only_c_inside_symb.cases simple.simps(5-8))
      then show "\<phi> = conn c [\<phi>1, \<phi>2]" and "wf_conn c [\<phi>1, \<phi>2]" using \<phi>_c'' wf l'' by auto
    qed
  have "grouped_by c \<phi>1" using wf IH\<phi>1 IH\<phi>2 \<phi>_conn only \<phi> unfolding only_c_inside_def by auto
  moreover have "grouped_by c \<phi>2"
    using wf \<phi> IH\<phi>1 IH\<phi>2 \<phi>_conn only unfolding only_c_inside_def by auto
  ultimately show "?G \<phi>" using \<phi>_conn connected_is_group local.wf by blast
qed


lemma grouped_by_false:
  "grouped_by c (conn c' [\<phi>, \<psi>]) \<Longrightarrow> c \<noteq> c' \<Longrightarrow> wf_conn c' [\<phi>, \<psi>] \<Longrightarrow> False"
  apply (induct "conn c' [\<phi>, \<psi>]" rule: grouped_by.induct)
  apply (auto simp: simple_decomp wf_conn_list, auto simp: conn_inj)
  by (metis list.distinct(1) list.sel(3) wf_conn_list(8))+

text \<open>Then the CNF form is a conjunction of clauses: every clause is in CNF form and two formulas in
  CNF form can be related by an and.\<close>
inductive super_grouped_by:: "'a connective \<Rightarrow> 'a connective \<Rightarrow> 'a propo \<Rightarrow> bool" for c c' where
grouped_is_super_grouped[simp]: "grouped_by c \<phi> \<Longrightarrow> super_grouped_by c c' \<phi>" |
connected_is_super_group: "super_grouped_by c c' \<phi> \<Longrightarrow> super_grouped_by c c' \<psi> \<Longrightarrow> wf_conn c [\<phi>, \<psi>]
  \<Longrightarrow> super_grouped_by c c' (conn c' [\<phi>, \<psi>])"

lemma simple_cnf[simp]:
  "super_grouped_by c c' FT"
  "super_grouped_by c c' FF"
  "super_grouped_by c c' (FVar x)"
  "super_grouped_by c c' (FNot FT)"
  "super_grouped_by c c' (FNot FF)"
  "super_grouped_by c c' (FNot (FVar x))"
  by auto

lemma c_in_c'_only_super_grouped_by:
  assumes c: "c = CAnd \<or> c = COr" and c': "c' = CAnd \<or> c' = COr" and cc': "c \<noteq> c'"
  shows "no_equiv \<phi> \<Longrightarrow> no_imp \<phi> \<Longrightarrow> simple_not \<phi> \<Longrightarrow> c_in_c'_only c c' \<phi>
    \<Longrightarrow> super_grouped_by c c' \<phi>"
    (is "?NE \<phi> \<Longrightarrow> ?NI \<phi> \<Longrightarrow> ?SN \<phi> \<Longrightarrow> ?C \<phi> \<Longrightarrow> ?S \<phi>")
proof (induct \<phi> rule: propo_induct_arity)
  case (nullary \<phi> x)
  then show "?S \<phi>" by auto
next
  case (unary \<phi>)
  then have "simple_not_symb (FNot \<phi>)"
    using all_subformula_st_test_symb_true_phi unfolding simple_not_def by blast
  then have "\<phi> = FT \<or> \<phi> = FF \<or> (\<exists> x. \<phi> = FVar x)" by (cases \<phi>, auto)
  then show "?S (FNot \<phi>)" by auto
next
  case (binary \<phi> \<phi>1 \<phi>2)
  note IH\<phi>1 = this(1) and IH\<phi>2 = this(2) and no_equiv = this(4) and no_imp = this(5)
    and simpleN = this(6) and c_in_c'_only = this(7) and \<phi>' = this(3)
  {
    assume "\<phi> = FImp \<phi>1 \<phi>2 \<or> \<phi> = FEq \<phi>1 \<phi>2"
    then have False using no_equiv no_imp by auto
    then have "?S \<phi>" by auto
  }
  moreover {
    assume \<phi>: "\<phi> = conn c' [\<phi>1, \<phi>2] \<and> wf_conn c' [\<phi>1, \<phi>2]"
    have c_in_c'_only: "c_in_c'_only c c' \<phi>1 \<and> c_in_c'_only c c' \<phi>2 \<and> c_in_c'_symb c c' \<phi>"
      using c_in_c'_only \<phi>' unfolding c_in_c'_only_def by auto
    have "super_grouped_by c c' \<phi>1" using \<phi> c' no_equiv no_imp simpleN IH\<phi>1 c_in_c'_only by auto
    moreover have "super_grouped_by c c' \<phi>2"
      using \<phi> c' no_equiv no_imp simpleN IH\<phi>2 c_in_c'_only by auto
    ultimately have "?S \<phi>"
      using super_grouped_by.intros(2) \<phi> by (metis c wf_conn_helper_facts(5,6))
  }
  moreover {
    assume \<phi>: "\<phi> = conn c [\<phi>1, \<phi>2] \<and> wf_conn c [\<phi>1, \<phi>2]"
    then have "only_c_inside c \<phi>1 \<and> only_c_inside c \<phi>2"
      using c_in_c'_symb_c_implies_only_c_inside c c' c_in_c'_only list.set_intros(1)
        wf_conn_helper_facts(5,6)  no_equiv no_imp simpleN last_ConsL last_ConsR last_in_set
        list.distinct(1) by (metis (no_types, hide_lams) cc')
    then have "only_c_inside c (conn c [\<phi>1, \<phi>2])"
      unfolding only_c_inside_def using \<phi>
      by (simp add: only_c_inside_into_only_c_inside all_subformula_st_decomp)
    then have "grouped_by c \<phi>" using \<phi> only_c_inside_imp_grouped_by c by blast
    then have "?S \<phi>" using super_grouped_by.intros(1) by metis
  }
  ultimately show "?S \<phi>" by (metis \<phi>' c c' cc' conn.simps(5,6) wf_conn_helper_facts(5,6))
qed


subsection \<open>Conjunctive Normal Form\<close>

subsubsection \<open>Definition\<close>

definition is_conj_with_TF where "is_conj_with_TF == super_grouped_by COr CAnd"

lemma or_in_and_only_conjunction_in_disj:
  shows "no_equiv \<phi> \<Longrightarrow> no_imp \<phi> \<Longrightarrow> simple_not \<phi> \<Longrightarrow> or_in_and_only \<phi> \<Longrightarrow> is_conj_with_TF \<phi>"
  using c_in_c'_only_super_grouped_by
  unfolding is_conj_with_TF_def or_in_and_only_def c_in_c'_only_def
  by (simp add: c_in_c'_only_def c_in_c'_only_super_grouped_by)

definition is_cnf where
"is_cnf \<phi> \<equiv> is_conj_with_TF \<phi> \<and> no_T_F_except_top_level \<phi>"

subsubsection \<open>Full CNF transformation\<close>

text \<open>The full1 CNF transformation consists simply in chaining all the transformation defined
  before.\<close>
definition cnf_rew where "cnf_rew =
  (full (propo_rew_step elim_equiv)) OO
  (full (propo_rew_step elim_imp)) OO
  (full (propo_rew_step elimTB)) OO
  (full (propo_rew_step pushNeg)) OO
  (full (propo_rew_step pushDisj))"

lemma cnf_rew_equivalent: "preserve_models cnf_rew"
  by (simp add: cnf_rew_def elimEquv_lifted_consistant elim_imp_lifted_consistant elimTB_consistent
    preserve_models_OO pushDisj_consistent pushNeg_lifted_consistant)

(*TODO Redo proof*)
lemma cnf_rew_is_cnf: "cnf_rew \<phi> \<phi>' \<Longrightarrow> is_cnf \<phi>'"
  apply (unfold cnf_rew_def OO_def)
  apply auto
proof -
  fix \<phi> \<phi>Eq \<phi>Imp \<phi>TB \<phi>Neg \<phi>Disj :: "'v propo"
  assume Eq: "full (propo_rew_step elim_equiv) \<phi> \<phi>Eq"
  then have no_equiv: "no_equiv \<phi>Eq" using no_equiv_full_propo_rew_step_elim_equiv by blast

  assume Imp: "full (propo_rew_step elim_imp) \<phi>Eq \<phi>Imp"
  then have no_imp: "no_imp \<phi>Imp" using no_imp_full_propo_rew_step_elim_imp by blast
  have no_imp_inv: "no_equiv \<phi>Imp" using no_equiv Imp elim_imp_inv by blast

  assume TB: "full (propo_rew_step elimTB) \<phi>Imp \<phi>TB"
  then have noTB: "no_T_F_except_top_level \<phi>TB"
    using no_imp_inv no_imp elimTB_full_propo_rew_step by blast
  have noTB_inv: "no_equiv \<phi>TB" "no_imp \<phi>TB" using elimTB_inv TB no_imp no_imp_inv by blast+

  assume Neg: "full (propo_rew_step pushNeg) \<phi>TB \<phi>Neg"
  then have noNeg: "simple_not \<phi>Neg"
    using noTB_inv noTB pushNeg_full_propo_rew_step by blast
  have noNeg_inv: "no_equiv \<phi>Neg" "no_imp \<phi>Neg" "no_T_F_except_top_level \<phi>Neg"
    using pushNeg_inv Neg noTB noTB_inv by blast+

  assume Disj: "full (propo_rew_step pushDisj) \<phi>Neg \<phi>Disj"
  then have no_Disj: "or_in_and_only \<phi>Disj"
    using noNeg_inv noNeg pushDisj_full_propo_rew_step by blast
  have noDisj_inv: "no_equiv \<phi>Disj" "no_imp \<phi>Disj" "no_T_F_except_top_level \<phi>Disj"
    "simple_not \<phi>Disj"
  using pushDisj_inv Disj noNeg noNeg_inv by blast+

  moreover have "is_conj_with_TF \<phi>Disj"
    using or_in_and_only_conjunction_in_disj noDisj_inv no_Disj by blast
  ultimately show "is_cnf \<phi>Disj" unfolding is_cnf_def by blast
qed

subsection \<open>Disjunctive Normal Form\<close>

subsubsection \<open>Definition\<close>

definition is_disj_with_TF where "is_disj_with_TF \<equiv> super_grouped_by CAnd COr"

lemma and_in_or_only_conjunction_in_disj:
  shows "no_equiv \<phi> \<Longrightarrow> no_imp \<phi> \<Longrightarrow> simple_not \<phi> \<Longrightarrow> and_in_or_only \<phi> \<Longrightarrow> is_disj_with_TF \<phi>"
  using c_in_c'_only_super_grouped_by
  unfolding is_disj_with_TF_def and_in_or_only_def c_in_c'_only_def
  by (simp add: c_in_c'_only_def c_in_c'_only_super_grouped_by)

definition is_dnf :: "'a propo \<Rightarrow> bool" where
"is_dnf \<phi> \<longleftrightarrow> is_disj_with_TF \<phi> \<and> no_T_F_except_top_level \<phi>"


subsubsection \<open>Full DNF transform\<close>

text \<open>The full1 DNF transformation consists simply in chaining all the transformation defined
  before.\<close>
definition dnf_rew where "dnf_rew \<equiv>
  (full (propo_rew_step elim_equiv)) OO
  (full (propo_rew_step elim_imp)) OO
  (full (propo_rew_step elimTB)) OO
  (full (propo_rew_step pushNeg)) OO
  (full (propo_rew_step pushConj))"

lemma dnf_rew_consistent: "preserve_models dnf_rew"
  by (simp add: dnf_rew_def elimEquv_lifted_consistant elim_imp_lifted_consistant elimTB_consistent
    preserve_models_OO pushConj_consistent pushNeg_lifted_consistant)

theorem dnf_transformation_correction:
    "dnf_rew \<phi> \<phi>' \<Longrightarrow> is_dnf \<phi>'"
  apply (unfold dnf_rew_def OO_def)
  by (meson and_in_or_only_conjunction_in_disj elimTB_full_propo_rew_step elimTB_inv(1,2)
    elim_imp_inv is_dnf_def no_equiv_full_propo_rew_step_elim_equiv
    no_imp_full_propo_rew_step_elim_imp pushConj_full_propo_rew_step pushConj_inv(1-4)
    pushNeg_full_propo_rew_step pushNeg_inv(1-3))

section \<open>More aggressive simplifications: Removing true and false at the beginning\<close>

subsection \<open>Transformation\<close>
text \<open>We should remove @{term FT} and @{term FF} at the beginning and not in the middle of the
  algorithm. To do this, we have to use more rules (one for each connective):\<close>
inductive elimTBFull where
ElimTBFull1[simp]: "elimTBFull (FAnd \<phi> FT) \<phi>" |
ElimTBFull1'[simp]: "elimTBFull (FAnd FT \<phi>) \<phi>" |

ElimTBFull2[simp]: "elimTBFull (FAnd \<phi> FF) FF" |
ElimTBFull2'[simp]: "elimTBFull (FAnd FF \<phi>) FF" |

ElimTBFull3[simp]: "elimTBFull (FOr \<phi> FT) FT" |
ElimTBFull3'[simp]: "elimTBFull (FOr FT \<phi>) FT" |

ElimTBFull4[simp]: "elimTBFull (FOr \<phi> FF) \<phi>" |
ElimTBFull4'[simp]: "elimTBFull (FOr FF \<phi>) \<phi>" |

ElimTBFull5[simp]: "elimTBFull (FNot FT) FF" |
ElimTBFull5'[simp]: "elimTBFull (FNot FF) FT" |

ElimTBFull6_l[simp]: "elimTBFull (FImp FT \<phi>) \<phi>" |
ElimTBFull6_l'[simp]: "elimTBFull (FImp FF \<phi>) FT" |
ElimTBFull6_r[simp]: "elimTBFull (FImp \<phi> FT) FT" |
ElimTBFull6_r'[simp]: "elimTBFull (FImp \<phi> FF) (FNot \<phi>)" |

ElimTBFull7_l[simp]: "elimTBFull (FEq FT \<phi>) \<phi>" |
ElimTBFull7_l'[simp]: "elimTBFull (FEq FF \<phi>) (FNot \<phi>)" |
ElimTBFull7_r[simp]: "elimTBFull (FEq \<phi> FT) \<phi>" |
ElimTBFull7_r'[simp]: "elimTBFull (FEq \<phi> FF) (FNot \<phi>)"

text \<open>The transformation is still consistent.\<close>
lemma elimTBFull_consistent: "preserve_models elimTBFull"
proof -
  {
    fix \<phi> \<psi>:: "'b propo"
    have "elimTBFull \<phi> \<psi> \<Longrightarrow> \<forall>A. A \<Turnstile> \<phi> \<longleftrightarrow> A \<Turnstile> \<psi>"
      by (induct_tac rule: elimTBFull.inducts, auto)
  }
  then show ?thesis using preserve_models_def by auto
qed

text \<open>Contrary to the theorem @{thm [source] no_T_F_symb_except_toplevel_step_exists}, we do not
  need the assumption @{term "no_equiv \<phi>"} and @{term "no_imp \<phi>"}, since our transformation is
  more general.\<close>
lemma no_T_F_symb_except_toplevel_step_exists':
  fixes \<phi> :: "'v propo"
  shows "\<psi> \<preceq> \<phi> \<Longrightarrow> \<not> no_T_F_symb_except_toplevel \<psi> \<Longrightarrow> \<exists>\<psi>'. elimTBFull \<psi> \<psi>'"
proof (induct \<psi> rule: propo_induct_arity)
  case (nullary \<phi>')
  then have False using no_T_F_symb_except_toplevel_true no_T_F_symb_except_toplevel_false by auto
  then show "Ex (elimTBFull \<phi>')" by blast
next
  case (unary \<psi>)
  then have "\<psi> = FF \<or> \<psi> = FT" using no_T_F_symb_except_toplevel_not_decom by blast
  then show "Ex (elimTBFull (FNot \<psi>))" using ElimTBFull5 ElimTBFull5' by blast
next
  case (binary \<phi>' \<psi>1 \<psi>2)
  then have "\<psi>1 = FT \<or> \<psi>2 = FT \<or> \<psi>1 = FF \<or> \<psi>2 = FF"
    by (metis binary_connectives_def conn.simps(5-8) insertI1 insert_commute
      no_T_F_symb_except_toplevel_bin_decom binary.hyps(3))
  then show "Ex (elimTBFull \<phi>')" using elimTBFull.intros binary.hyps(3)  by blast
qed

text \<open>The same applies here. We do not need the assumption, but the deep link between
  @{term "\<not> no_T_F_except_top_level \<phi>"} and the existence of a rewriting step, still exists.\<close>
lemma no_T_F_except_top_level_rew':
  fixes \<phi> :: "'v propo"
  assumes noTB: "\<not> no_T_F_except_top_level \<phi>"
  shows "\<exists>\<psi> \<psi>'. \<psi> \<preceq> \<phi> \<and> elimTBFull \<psi> \<psi>'"
proof -
  have test_symb_false_nullary:
    "\<forall>x. no_T_F_symb_except_toplevel (FF:: 'v propo) \<and> no_T_F_symb_except_toplevel FT
      \<and> no_T_F_symb_except_toplevel (FVar (x:: 'v))"
    by auto
  moreover {
    fix c:: "'v connective" and l :: "'v propo list" and \<psi> :: "'v propo"
    have H: "elimTBFull (conn c l) \<psi> \<Longrightarrow> \<not>no_T_F_symb_except_toplevel (conn c l)"
      by (cases "conn c l" rule: elimTBFull.cases) auto
  }
  ultimately show ?thesis
    using no_test_symb_step_exists[of no_T_F_symb_except_toplevel \<phi> elimTBFull] noTB
    no_T_F_symb_except_toplevel_step_exists' unfolding no_T_F_except_top_level_def by metis
qed



lemma elimTBFull_full_propo_rew_step:
  fixes \<phi> \<psi> :: "'v propo"
  assumes "full (propo_rew_step elimTBFull) \<phi> \<psi>"
  shows "no_T_F_except_top_level \<psi>"
  using full_propo_rew_step_subformula no_T_F_except_top_level_rew' assms by fastforce

subsection \<open>More invariants\<close>
text \<open>As the aim is to use the transformation as the first transformation, we have to show some more
  invariants for @{term elim_equiv} and @{term elim_imp}. For the other transformation, we have
  already proven it.\<close>
lemma propo_rew_step_ElimEquiv_no_T_F: "propo_rew_step elim_equiv \<phi> \<psi> \<Longrightarrow> no_T_F \<phi> \<Longrightarrow>  no_T_F \<psi>"
proof (induct rule: propo_rew_step.induct)
  fix \<phi>' :: "'v propo" and \<psi>' :: "'v propo"
  assume a1: "no_T_F \<phi>'"
  assume a2: "elim_equiv \<phi>' \<psi>'"
  have "\<forall>x0 x1. (\<not> elim_equiv (x1 :: 'v propo) x0 \<or> (\<exists>v2 v3 v4 v5 v6 v7. x1 = FEq v2 v3
    \<and> x0 = FAnd (FImp v4 v5) (FImp v6 v7) \<and> v2 = v4 \<and> v4 = v7 \<and> v3 = v5 \<and> v3 = v6))
 = (\<not> elim_equiv x1 x0 \<or> (\<exists>v2 v3 v4 v5 v6 v7. x1 = FEq v2 v3
    \<and> x0 = FAnd (FImp v4 v5) (FImp v6 v7) \<and> v2 = v4 \<and> v4 = v7 \<and> v3 = v5 \<and> v3 = v6))"
    by meson
  then have "\<forall>p pa. \<not> elim_equiv (p :: 'v propo) pa \<or> (\<exists>pb pc pd pe pf pg. p = FEq pb pc
    \<and> pa = FAnd (FImp pd pe) (FImp pf pg) \<and> pb = pd \<and> pd = pg \<and> pc = pe \<and> pc = pf)"
    using elim_equiv.cases by force
  then show "no_T_F \<psi>'" using a1 a2 by fastforce
next
  fix \<phi> \<phi>' :: "'v propo" and \<xi> \<xi>' :: "'v propo list" and c :: "'v connective"
  assume rel: "propo_rew_step elim_equiv \<phi> \<phi>'"
  and IH: "no_T_F \<phi> \<Longrightarrow> no_T_F \<phi>'"
  and corr: "wf_conn c (\<xi> @ \<phi> # \<xi>')"
  and no_T_F: "no_T_F (conn c (\<xi> @ \<phi> # \<xi>'))"
  {
    assume c: "c = CNot"
    then have empty: "\<xi> = []" "\<xi>' = []" using corr by auto
    then have "no_T_F \<phi>" using no_T_F c no_T_F_decomp_not by auto
    then have "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))" using c empty no_T_F_comp_not IH by auto
  }
  moreover {
    assume c: "c \<in> binary_connectives"
    obtain a b where ab: "\<xi> @ \<phi> # \<xi>' = [a, b]"
      using corr c list_length2_decomp wf_conn_bin_list_length by metis
    then have \<phi>: "\<phi> = a \<or> \<phi> = b"
      by (metis append.simps(1) append_is_Nil_conv list.distinct(1) list.sel(3) nth_Cons_0
        tl_append2)
    have \<zeta>: "\<forall>\<zeta>\<in> set (\<xi> @ \<phi> # \<xi>'). no_T_F \<zeta>"
      using no_T_F unfolding no_T_F_def using corr all_subformula_st_decomp by blast

    then have \<phi>': "no_T_F \<phi>'" using ab IH \<phi> by auto
    have l': "\<xi> @ \<phi>' # \<xi>' = [\<phi>', b] \<or> \<xi> @ \<phi>' # \<xi>' = [a, \<phi>']"
      by (metis (no_types, hide_lams) ab append_Cons append_Nil append_Nil2 butlast.simps(2)
        butlast_append list.distinct(1) list.sel(3))
    then have "\<forall>\<zeta> \<in> set (\<xi> @ \<phi>' # \<xi>'). no_T_F \<zeta>" using \<zeta> \<phi>' ab by fastforce
    moreover
      have "\<forall>\<zeta> \<in> set (\<xi> @ \<phi> # \<xi>'). \<zeta> \<noteq> FT \<and> \<zeta> \<noteq> FF"
        using \<zeta> corr no_T_F no_T_F_except_top_level_false no_T_F_no_T_F_except_top_level by blast
      then have "no_T_F_symb (conn c (\<xi> @ \<phi>' # \<xi>'))"
        by (metis \<phi>' l' ab all_subformula_st_test_symb_true_phi c list.distinct(1)
          list.set_intros(1,2) no_T_F_symb_except_toplevel_bin_decom
          no_T_F_symb_except_toplevel_no_T_F_symb no_T_F_symb_false(1,2) no_T_F_def wf_conn_binary
          wf_conn_list(1,2))
    ultimately have "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))"
      by (metis l' all_subformula_st_decomp_imp c no_T_F_def wf_conn_binary)
  }
  moreover {
     fix x
     assume "c = CVar x \<or> c = CF \<or> c = CT"
     then have False using corr by auto
     then have "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))" by auto
  }
  ultimately show "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))" using corr wf_conn.cases by metis
qed

lemma elim_equiv_inv':
  fixes \<phi> \<psi> :: "'v propo"
  assumes "full (propo_rew_step elim_equiv) \<phi> \<psi>" and "no_T_F_except_top_level \<phi>"
  shows "no_T_F_except_top_level \<psi>"
proof -
  {
    fix \<phi> \<psi> :: "'v propo"
    have "propo_rew_step elim_equiv \<phi> \<psi> \<Longrightarrow> no_T_F_except_top_level \<phi>
      \<Longrightarrow> no_T_F_except_top_level \<psi>"
      proof -
        assume rel: "propo_rew_step elim_equiv \<phi> \<psi>"
        and no: "no_T_F_except_top_level \<phi>"
        {
          assume "\<phi> = FT \<or> \<phi> = FF"
          from rel this have False
            apply (induct rule: propo_rew_step.induct, auto simp: wf_conn_list(1,2))
            using elim_equiv.simps by blast+
          then have "no_T_F_except_top_level \<psi>" by blast
        }
        moreover {
          assume "\<phi> \<noteq> FT \<and> \<phi> \<noteq> FF"
          then have "no_T_F \<phi>"
            by (metis no no_T_F_symb_except_toplevel_all_subformula_st_no_T_F_symb)
          then have "no_T_F \<psi>" using propo_rew_step_ElimEquiv_no_T_F rel by blast
          then have "no_T_F_except_top_level \<psi>" by (simp add: no_T_F_no_T_F_except_top_level)
        }
        ultimately show "no_T_F_except_top_level \<psi>" by metis
      qed
  }
  moreover {
     fix c :: "'v connective" and \<xi> \<xi>' :: "'v propo list" and \<zeta> \<zeta>' :: "'v propo"
     assume rel: "propo_rew_step elim_equiv \<zeta> \<zeta>'"
     and incl: "\<zeta> \<preceq> \<phi>"
     and corr: "wf_conn c (\<xi> @ \<zeta> # \<xi>')"
     and no_T_F: "no_T_F_symb_except_toplevel (conn c (\<xi> @ \<zeta> # \<xi>'))"
     and n: "no_T_F_symb_except_toplevel \<zeta>'"
     have "no_T_F_symb_except_toplevel (conn c (\<xi> @ \<zeta>' # \<xi>'))"
     proof
       have p: "no_T_F_symb (conn c (\<xi> @ \<zeta> # \<xi>'))"
         using corr wf_conn_list(1) wf_conn_list(2) no_T_F_symb_except_toplevel_no_T_F_symb no_T_F
         by blast
       have l: "\<forall>\<phi>\<in>set (\<xi> @ \<zeta> # \<xi>'). \<phi> \<noteq> FT \<and> \<phi> \<noteq> FF"
         using corr wf_conn_no_T_F_symb_iff p by blast
       from rel incl have "\<zeta>'\<noteq>FT \<and>\<zeta>'\<noteq>FF"
         apply (induction \<zeta> \<zeta>' rule: propo_rew_step.induct)
         apply (cases rule: elim_equiv.cases, auto simp: elim_equiv.simps)
         by (metis append_is_Nil_conv list.distinct wf_conn_list(1,2) wf_conn_no_arity_change
           wf_conn_no_arity_change_helper)+
       then have "\<forall>\<phi> \<in> set (\<xi> @ \<zeta>' # \<xi>'). \<phi> \<noteq> FT \<and> \<phi> \<noteq> FF" using l by auto
       moreover have "c \<noteq> CT \<and> c \<noteq> CF" using corr by auto
       ultimately show "no_T_F_symb (conn c (\<xi> @ \<zeta>' # \<xi>'))"
         by (metis corr wf_conn_no_arity_change wf_conn_no_arity_change_helper no_T_F_symb_comp)
     qed
  }
  ultimately show "no_T_F_except_top_level \<psi>"
    using full_propo_rew_step_inv_stay_with_inc[of "elim_equiv" "no_T_F_symb_except_toplevel" "\<phi>"]
      assms subformula_refl unfolding no_T_F_except_top_level_def by metis
qed


lemma propo_rew_step_ElimImp_no_T_F: "propo_rew_step elim_imp \<phi> \<psi> \<Longrightarrow> no_T_F \<phi> \<Longrightarrow>  no_T_F \<psi>"
proof (induct rule: propo_rew_step.induct)
  case (global_rel \<phi>' \<psi>')
  then show "no_T_F \<psi>'"
    using elim_imp.cases no_T_F_comp_not no_T_F_decomp(1,2)
    by (metis no_T_F_comp_expanded_explicit(2))
next
  case (propo_rew_one_step_lift \<phi> \<phi>' c \<xi> \<xi>')
  note rel = this(1) and IH = this(2) and corr = this(3) and no_T_F = this(4)
  {
    assume c: "c = CNot"
    then have empty: "\<xi> = []" "\<xi>' = []" using corr by auto
    then have "no_T_F \<phi>" using no_T_F c no_T_F_decomp_not by auto
    then have "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))" using c empty no_T_F_comp_not IH by auto
  }
  moreover {
    assume c: "c \<in> binary_connectives"
    then obtain a b where ab: "\<xi> @ \<phi> # \<xi>' = [a, b]"
      using corr list_length2_decomp wf_conn_bin_list_length by metis
    then have \<phi>: "\<phi> = a \<or> \<phi> = b"
      by (metis append_self_conv2 wf_conn_list_decomp(4) wf_conn_unary list.discI list.sel(3)
        nth_Cons_0 tl_append2)
    have \<zeta>: "\<forall>\<zeta> \<in> set (\<xi> @ \<phi> # \<xi>'). no_T_F \<zeta>" using ab c propo_rew_one_step_lift.prems by auto

    then have \<phi>': "no_T_F \<phi>'"
      using ab IH \<phi> corr no_T_F no_T_F_def all_subformula_st_decomp_explicit by auto
    have \<chi>: "\<xi> @ \<phi>' # \<xi>' = [\<phi>', b] \<or> \<xi> @ \<phi>' # \<xi>' = [a, \<phi>']"
      by (metis (no_types, hide_lams) ab append_Cons append_Nil append_Nil2 butlast.simps(2)
        butlast_append list.distinct(1) list.sel(3))
    then have "\<forall>\<zeta>\<in> set (\<xi> @ \<phi>' # \<xi>'). no_T_F \<zeta>" using \<zeta> \<phi>' ab by fastforce
    moreover
      have "no_T_F (last (\<xi> @ \<phi>' # \<xi>'))" by (simp add: calculation)
      then have "no_T_F_symb (conn c (\<xi> @ \<phi>' # \<xi>'))"
        by (metis \<chi> \<phi>' \<zeta> ab all_subformula_st_test_symb_true_phi c last.simps list.distinct(1)
          list.set_intros(1) no_T_F_bin_decomp no_T_F_def)
    ultimately have "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))" using c \<chi> by fastforce
  }
  moreover {
    fix x
    assume "c = CVar x \<or> c = CF \<or> c = CT"
    then have False using corr by auto
    then have "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))" by auto
  }
  ultimately show "no_T_F (conn c (\<xi> @ \<phi>' # \<xi>'))" using corr wf_conn.cases by blast
qed


lemma elim_imp_inv':
  fixes \<phi> \<psi> :: "'v propo"
  assumes "full (propo_rew_step elim_imp) \<phi> \<psi>" and "no_T_F_except_top_level \<phi>"
  shows"no_T_F_except_top_level \<psi>"
proof -
  {
    {
      fix \<phi> \<psi> :: "'v propo"
      have H: "elim_imp \<phi> \<psi> \<Longrightarrow> no_T_F_except_top_level \<phi> \<Longrightarrow>  no_T_F_except_top_level \<psi>"
        by (induct \<phi> \<psi> rule: elim_imp.induct, auto)
    } note H = this
    fix \<phi> \<psi> :: "'v propo"
    have "propo_rew_step elim_imp \<phi> \<psi> \<Longrightarrow> no_T_F_except_top_level \<phi> \<Longrightarrow>  no_T_F_except_top_level \<psi>"
      proof -
        assume rel: "propo_rew_step elim_imp \<phi> \<psi>"
        and no: "no_T_F_except_top_level \<phi>"
        {
          assume "\<phi> = FT \<or> \<phi> = FF"
          from rel this have False
            apply (induct rule: propo_rew_step.induct)
            by (cases rule: elim_imp.cases, auto simp: wf_conn_list(1,2))
          then have "no_T_F_except_top_level \<psi>" by blast
        }
        moreover {
          assume "\<phi> \<noteq> FT \<and> \<phi> \<noteq> FF"
          then have "no_T_F \<phi>"
            by (metis no no_T_F_symb_except_toplevel_all_subformula_st_no_T_F_symb)
          then have "no_T_F \<psi>"
            using rel propo_rew_step_ElimImp_no_T_F by blast
          then have "no_T_F_except_top_level \<psi>" by (simp add: no_T_F_no_T_F_except_top_level)
        }
        ultimately show "no_T_F_except_top_level \<psi>" by metis
      qed
  }
  moreover {
     fix c :: "'v connective" and \<xi> \<xi>' :: "'v propo list" and \<zeta> \<zeta>' :: "'v propo"
     assume rel: "propo_rew_step elim_imp \<zeta> \<zeta>'"
     and incl: "\<zeta> \<preceq> \<phi>"
     and corr: "wf_conn c (\<xi> @ \<zeta> # \<xi>')"
     and no_T_F: "no_T_F_symb_except_toplevel (conn c (\<xi> @ \<zeta> # \<xi>'))"
     and n: "no_T_F_symb_except_toplevel \<zeta>'"
     have "no_T_F_symb_except_toplevel (conn c (\<xi> @ \<zeta>' # \<xi>'))"
     proof
       have p: "no_T_F_symb (conn c (\<xi> @ \<zeta> # \<xi>'))"
         by (simp add: corr no_T_F no_T_F_symb_except_toplevel_no_T_F_symb wf_conn_list(1,2))

       have l: "\<forall>\<phi>\<in>set (\<xi> @ \<zeta> # \<xi>'). \<phi> \<noteq> FT \<and> \<phi> \<noteq> FF"
         using corr wf_conn_no_T_F_symb_iff p by blast
       from rel incl have "\<zeta>'\<noteq>FT \<and>\<zeta>'\<noteq>FF"
         apply (induction \<zeta> \<zeta>' rule: propo_rew_step.induct)
         apply (cases rule: elim_imp.cases, auto)
         using wf_conn_list(1,2) wf_conn_no_arity_change wf_conn_no_arity_change_helper
         by (metis append_is_Nil_conv list.distinct(1))+
       then have "\<forall>\<phi>\<in>set (\<xi> @ \<zeta>' # \<xi>'). \<phi> \<noteq> FT \<and> \<phi> \<noteq> FF" using l by auto
       moreover have "c \<noteq> CT \<and> c \<noteq> CF" using corr by auto
       ultimately show "no_T_F_symb (conn c (\<xi> @ \<zeta>' # \<xi>'))"
         using corr wf_conn_no_arity_change no_T_F_symb_comp
         by (metis wf_conn_no_arity_change_helper)
     qed
  }
  ultimately show "no_T_F_except_top_level \<psi>"
    using full_propo_rew_step_inv_stay_with_inc[of "elim_imp" "no_T_F_symb_except_toplevel" "\<phi>"]
    assms subformula_refl unfolding no_T_F_except_top_level_def by metis
qed


subsection \<open>The new CNF and DNF transformation\<close>

text \<open>The transformation is the same as before, but the order is not the same.\<close>
definition dnf_rew' :: "'a propo \<Rightarrow> 'a propo \<Rightarrow> bool" where
"dnf_rew' =
  (full (propo_rew_step elimTBFull)) OO
  (full (propo_rew_step elim_equiv)) OO
  (full (propo_rew_step elim_imp)) OO
  (full (propo_rew_step pushNeg)) OO
  (full (propo_rew_step pushConj))"

lemma dnf_rew'_consistent: "preserve_models dnf_rew'"
  by (simp add: dnf_rew'_def elimEquv_lifted_consistant elim_imp_lifted_consistant
    elimTBFull_consistent preserve_models_OO pushConj_consistent pushNeg_lifted_consistant)

theorem cnf_transformation_correction:
    "dnf_rew' \<phi> \<phi>' \<Longrightarrow> is_dnf \<phi>'"
  unfolding dnf_rew'_def OO_def
  by (meson and_in_or_only_conjunction_in_disj elimTBFull_full_propo_rew_step elim_equiv_inv'
    elim_imp_inv elim_imp_inv' is_dnf_def no_equiv_full_propo_rew_step_elim_equiv
    no_imp_full_propo_rew_step_elim_imp pushConj_full_propo_rew_step pushConj_inv(1-4)
    pushNeg_full_propo_rew_step pushNeg_inv(1-3))

text \<open>Given all the lemmas before the CNF transformation is easy to prove:\<close>
definition cnf_rew' :: "'a propo \<Rightarrow> 'a propo \<Rightarrow> bool" where
"cnf_rew' =
  (full (propo_rew_step elimTBFull)) OO
  (full (propo_rew_step elim_equiv)) OO
  (full (propo_rew_step elim_imp)) OO
  (full (propo_rew_step pushNeg)) OO
  (full (propo_rew_step pushDisj))"

lemma cnf_rew'_consistent: "preserve_models cnf_rew'"
  by (simp add: cnf_rew'_def elimEquv_lifted_consistant elim_imp_lifted_consistant
    elimTBFull_consistent preserve_models_OO pushDisj_consistent pushNeg_lifted_consistant)

theorem cnf'_transformation_correction:
  "cnf_rew' \<phi> \<phi>' \<Longrightarrow> is_cnf \<phi>'"
  unfolding cnf_rew'_def OO_def
  by (meson elimTBFull_full_propo_rew_step elim_equiv_inv' elim_imp_inv elim_imp_inv' is_cnf_def
    no_equiv_full_propo_rew_step_elim_equiv no_imp_full_propo_rew_step_elim_imp
    or_in_and_only_conjunction_in_disj pushDisj_full_propo_rew_step pushDisj_inv(1-4)
    pushNeg_full_propo_rew_step pushNeg_inv(1) pushNeg_inv(2) pushNeg_inv(3))

end
