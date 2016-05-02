(*  Title:       A Simple Resolution Prover for First-Order Clauses
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section {* A Simple Resolution Prover for First-Order Clauses *}

theory FO_Resolution_Prover
imports Ordered_Ground_Resolution Standard_Redundancy Substitution
begin

type_synonym 'a state = "'a clause set \<times> 'a clause set \<times> 'a clause set"

locale FO_resolution =
  unification subst_atm id_subst comp_subst mgu
  for
    subst_atm :: "'a :: wellorder \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s => 's => 's" and
    mgu :: "'a set set \<Rightarrow> 's option" +
  fixes
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    less_atm_iff: "less_atm A B \<longleftrightarrow> (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> A \<cdot>a \<sigma> < B \<cdot>a \<sigma>)"
begin

definition less_eq_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "less_eq_atm A B \<longleftrightarrow> less_atm A B \<or> A = B"

lemma ground_less_atm_iff: "is_ground_atm A \<Longrightarrow> is_ground_atm B \<Longrightarrow> less_atm A B \<longleftrightarrow> A < B"
  unfolding is_ground_atm_def less_atm_iff by (auto intro: ex_ground_subst)

lemma ground_less_eq_atm_iff: "is_ground_atm A \<Longrightarrow> is_ground_atm B \<Longrightarrow> less_eq_atm A B \<longleftrightarrow> A \<le> B"
  unfolding less_eq_atm_def ground_less_atm_iff by fastforce

definition subsumes :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "subsumes C D \<longleftrightarrow> (\<exists>\<sigma>. C \<cdot> \<sigma> \<le># D)"

definition properly_subsumes :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "properly_subsumes C D \<longleftrightarrow> subsumes C D \<and> \<not> subsumes D C"

definition variants :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "variants C D \<longleftrightarrow> subsumes C D \<and> subsumes D C"

definition clss_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "clss_of_state St = (case St of (N, P, Q) \<Rightarrow> N \<union> P \<union> Q)"

abbreviation grounding_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "grounding_of_state St \<equiv> grounding_of_clss (clss_of_state St)"

text {*
\begin{nit}
$A_{ii}$ vs.\ $A_i$
\end{nit}
*}
 
context
  fixes S :: "'a clause \<Rightarrow> 'a clause"
begin

inductive ord_resolve_raw :: "'a clause multiset \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve_raw:
  "Cf' = \<Union># {#C'. (C', A, AA') \<in># ZZ#} \<Longrightarrow>
   AA = {#A. (C', A, AA') \<in># ZZ#} \<Longrightarrow>
   AAA = {#insert A (set_mset AA'). (C', A, AA') \<in># ZZ#} \<Longrightarrow>
   CC = {#C' + poss AA'. (C', A, AA') \<in># ZZ#} \<Longrightarrow>
   D = negs AA + D' \<Longrightarrow>
   ZZ \<noteq> {#} \<Longrightarrow>
   (\<forall>(_, _, AA') \<in> set_mset ZZ. AA' \<noteq> {#}) \<Longrightarrow>
   Some \<sigma> = mgu (set_mset AAA) \<Longrightarrow>
   S D = negs AA \<or>
     S D = {#} \<and> size AA = 1 \<and> (\<forall>A. A \<in># AA \<longrightarrow> (\<forall>B \<in> atms_of (D' \<cdot> \<sigma>). \<not> less_atm (A \<cdot>a \<sigma>) B)) \<Longrightarrow>
   (\<forall>(C', A, _) \<in> set_mset ZZ. \<forall>B \<in> atms_of (C' \<cdot> \<sigma>). \<not> less_eq_atm (A \<cdot>a \<sigma>) B) \<Longrightarrow>
   (\<forall>C. C \<in># CC \<longrightarrow> S C = {#}) \<Longrightarrow>
   ord_resolve_raw CC D ((Cf' + D') \<cdot> \<sigma>)"

term mset_set

inductive ord_resolve_raw2 :: "'a clause multiset \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve_raw2:
  "length (Cs :: 'a clause list) = n \<Longrightarrow> (* list of  C1, ..., Cn *)
   length (AAs :: 'a multiset list) = n \<Longrightarrow> (* list of corresponding  Aij's *)
     (\<forall>AA \<in> set AAs. AA \<noteq> {#}) \<Longrightarrow>
   length (As :: 'a list) = n \<Longrightarrow> (* list of  A1, ..., An  *)
   (AsD :: 'a clause) = negs (mset As) + D \<Longrightarrow> (* The premise  \<not>A1 \<or> ... \<or> \<not>An \<or> D *)
   (CC :: 'a clause multiset) = {# C + poss AA . (C,AA) \<in># mset (zip Cs AAs) #} \<Longrightarrow> (* Side premises *)  
   Some \<sigma> = mgu {set_mset AA \<union> {A} | AA A. (AA,A) \<in> set (zip AAs As)} \<Longrightarrow> 
   S AsD = negs (mset As) \<or>
     S AsD = {#} \<and> length As = 1 \<and> (\<forall>B \<in> atms_of (D \<cdot> \<sigma>). \<not> less_atm ((As ! 0) \<cdot>a \<sigma>) B) \<Longrightarrow> 
   (\<forall>i < n. \<forall>B \<in> atms_of (Cs ! i \<cdot> \<sigma>). \<not> less_eq_atm (As ! i \<cdot>a \<sigma>) B) \<Longrightarrow>
   (\<forall>C. C \<in># CC \<longrightarrow> S C = {#}) \<Longrightarrow>
   ord_resolve_raw2 CC AsD ((\<Union>#(mset Cs) + D) \<cdot> \<sigma>)"

inductive ord_resolve :: "'a clause multiset \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve:
  "CC = {#C. (C, \<rho>) \<in># CCP#} \<Longrightarrow>
   P = {#\<rho>. (C, \<rho>) \<in># CCP#} \<Longrightarrow>
   CC\<rho> = {#C \<cdot> \<rho>. (C, \<rho>) \<in># CCP#} \<Longrightarrow>
   \<forall>\<rho>. \<rho> \<in># P \<longrightarrow> is_renaming \<rho> \<Longrightarrow>
   is_renaming \<rho> \<Longrightarrow>
   ord_resolve_raw CC\<rho> (D \<cdot> \<rho>) E \<Longrightarrow>
   ord_resolve CC D E"

lemma ord_resolve_raw_imp_ord_resolve: "ord_resolve_raw CC D E \<Longrightarrow> ord_resolve CC D E"
  by (rule ord_resolve[of _ "{#(C, id_subst). C \<in># CC#}" _ _ id_subst]) auto

lemma ground_prems_ord_resolve_imp_ord_resolve_raw:
  assumes 
    gr_cc: "is_ground_cls_mset CC" and
    gr_d: "is_ground_cls D" and
    res_e: "ord_resolve CC D E"
  shows "ord_resolve_raw CC D E"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve CCP P CC\<rho> \<rho>)
  note cc = this(1) and \<rho> = this(2) and cc\<rho> = this(3) and res_e_raw = this(6)

  have "CC\<rho> = CC"
    unfolding cc\<rho> cc is_ground_cls_mset_def
    apply (rule image_mset_cong_pair)
    using gr_cc unfolding cc is_ground_cls_mset_def by fastforce
  moreover have "D \<cdot> \<rho> = D"
    using gr_d by auto
  ultimately show "ord_resolve_raw CC D E"
    using res_e_raw by simp
qed

lemma ord_resolve_raw_sound:
  assumes
    res_e: "ord_resolve_raw CC D E" and
    cc_d_true: "\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile>m (CC + {#D#}) \<cdot>cc \<sigma>" and
    ground_subst_\<sigma>: "is_ground_subst \<sigma>"
  shows "I \<Turnstile> E \<cdot> \<sigma>"
using res_e proof (cases rule: ord_resolve_raw.cases)
  case (ord_resolve_raw Cf' ZZ AA AAA D' \<tau>)
  note e = this(1) and cf' = this(2) and aa = this(3) and aaa = this(4) and cc = this(5) and
    d = this(6) and \<tau> = this(9)

  have "is_ground_subst (\<tau> \<odot> \<sigma>)"
    using ground_subst_\<sigma> by (rule is_ground_comp_subst)
  hence cc_true: "I \<Turnstile>m CC \<cdot>cc \<tau> \<cdot>cc \<sigma>" and d_true: "I \<Turnstile> D \<cdot> \<tau> \<cdot> \<sigma>"
    using cc_d_true[of "\<tau> \<odot> \<sigma>"] by auto

  show ?thesis
  proof (cases "\<forall>A. A \<in># AA \<longrightarrow> A \<cdot>a \<tau> \<cdot>a \<sigma> \<in> I")
    case True
    hence "\<not> I \<Turnstile> negs AA \<cdot> \<tau> \<cdot> \<sigma>"
      unfolding true_cls_def by auto
    hence "I \<Turnstile> D' \<cdot> \<tau> \<cdot> \<sigma>"
      using d_true unfolding d by simp
    thus ?thesis
      unfolding e by simp
  next
    case False
    then obtain A where a_in_aa: "A \<in># AA" and a_false: "A \<cdot>a \<tau> \<cdot>a \<sigma> \<notin> I"
      by blast
    from a_in_aa obtain C' BB where cabb: "(C', A, BB) \<in># ZZ"
      unfolding aa by auto
    hence c_cf': "set_mset C' \<subseteq> set_mset Cf'"
      unfolding cf' by force
    hence c_in_cc: "C' + poss BB \<in># CC"
      using cabb unfolding cc by force
    have a_bb_in_aaa: "insert A (set_mset BB) \<in># AAA"
      using aaa cabb by force
    { fix B
      assume "B \<in># BB"
      moreover have "is_unifier_set \<tau> (set_mset AAA)"
        using \<tau> by (auto simp: aaa intro: is_unifier_set_mgu)
      ultimately have "B \<cdot>a \<tau> = A \<cdot>a \<tau>"
        using a_bb_in_aaa by (intro is_unifier_set_subst_atm_eqI[of "insert A (set_mset BB)"]) auto
    }
    hence "\<not> I \<Turnstile> poss BB \<cdot> \<tau> \<cdot> \<sigma>"
      using a_false by (auto simp: true_cls_def)
    moreover have "I \<Turnstile> (C' + poss BB) \<cdot> \<tau> \<cdot> \<sigma>"
      using c_in_cc cc_true unfolding true_cls_mset_def by force
    ultimately have "I \<Turnstile> C' \<cdot> \<tau> \<cdot> \<sigma>"
      by simp
    thus ?thesis
      unfolding e subst_cls_union using c_cf' by (blast intro: true_cls_mono intro!: subst_cls_mono)
  qed
qed

lemma ord_resolve_sound:
  assumes
    res_e: "ord_resolve CC D E" and
    cc_d_true: "\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile>m (CC + {#D#}) \<cdot>cc \<sigma>" and
    ground_subst_\<sigma>: "is_ground_subst \<sigma>"
  shows "I \<Turnstile> E \<cdot> \<sigma>"
using res_e proof (cases rule: ord_resolve.cases)
  case (ord_resolve CCP P CC\<rho> \<rho>)
  note cc = this(1) and p = this(2) and cc\<rho> = this(3) and renaming = this(4) and \<rho> = this(5) and
    resolve = this(6)
  { fix \<sigma>
    assume "is_ground_subst \<sigma>"
    hence "is_ground_subst (\<rho> \<odot> \<sigma>)" "\<forall>\<rho>. (\<exists>C. (C, \<rho>) \<in># CCP) \<longrightarrow> is_ground_subst (\<rho> \<odot> \<sigma>)"
      unfolding p by simp_all
    with cc_d_true have "I \<Turnstile>m (CC\<rho> + {#D \<cdot> \<rho>#}) \<cdot>cc \<sigma>"
      unfolding cc\<rho> cc p
      by (auto simp: subst_cls_comp_subst[symmetric] simp del: subst_cls_comp_subst)
  }
  thus ?thesis
    by (rule ord_resolve_raw_sound[OF resolve _ ground_subst_\<sigma>])
qed

context
  fixes M :: "'a clause set"
  assumes select: "selection S"
begin

interpretation selection
  by (rule select)

definition S_M :: "'a clause \<Rightarrow> 'a clause" where
  "S_M C = (if C \<in> grounding_of_clss M
    then (SOME C'. \<exists>D \<sigma>. D \<in> M \<and> C = D \<cdot> \<sigma> \<and> C' = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>) else S C)"

lemma S_M_grounding_of_clss:
  assumes "C \<in> grounding_of_clss M"
  obtains D \<sigma> where "D \<in> M \<and> C = D \<cdot> \<sigma> \<and> S_M C = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>"
proof (atomize_elim, unfold S_M_def eqTrueI[OF assms] if_True, rule someI_ex)
  from assms show "\<exists>C' D \<sigma>. D \<in> M \<and> C = D \<cdot> \<sigma> \<and> C' = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>"
    by (auto simp: grounding_of_clss_def grounding_of_cls_def)
qed

lemma S_M_not_grounding_of_clss:
  assumes "C \<notin> grounding_of_clss M"
  shows "S_M C = S C"
  using assms unfolding S_M_def by simp

lemma S_M_selects_subseteq: "S_M C \<le># C"
proof cases
  assume "C \<in> grounding_of_clss M"
  then obtain D \<sigma> where "C = D \<cdot> \<sigma>" "S_M C = S D \<cdot> \<sigma>"
    using S_M_grounding_of_clss by metis
  then show ?thesis
    using S_selects_subseteq by (auto intro: subst_cls_mono_mset)
qed (simp add: S_M_not_grounding_of_clss S_selects_subseteq)

lemma S_M_selects_neg_lits:
  assumes "L \<in># S_M C"
  shows "is_neg L"
using assms proof cases
  assume "C \<in> grounding_of_clss M"
  then obtain D \<sigma> where "C = D \<cdot> \<sigma>" "S_M C = S D \<cdot> \<sigma>"
    using S_M_grounding_of_clss by metis
  then show ?thesis
    using assms S_selects_neg_lits by auto
qed (simp add: S_M_not_grounding_of_clss S_selects_neg_lits)


interpretation gd: ground_resolution_with_selection S_M
  apply unfold_locales apply (auto simp: S_M_selects_subseteq S_M_selects_neg_lits) done

(*"grounding_of_clss N0"*)

interpretation src: standard_redundancy_criterion gd.ord_\<Gamma>
  "ground_resolution_with_selection.INTERP S_M"
  by unfold_locales
(*
find_theorems name: src
thm src.saturated_upto_refute_complete
*)

(*TODO change*)
definition "gd_ord_\<Gamma>' = gd.ord_\<Gamma>"

lemma gd_ord_\<Gamma>_ngd_ord_\<Gamma>: "gd.ord_\<Gamma> \<subseteq> gd_ord_\<Gamma>'"
  unfolding gd_ord_\<Gamma>'_def by simp

interpretation src_ext:
  redundancy_criterion "gd_ord_\<Gamma>'" "src.Rf" "(\<lambda>N. src.Ri N \<union> (gd_ord_\<Gamma>' - gd.ord_\<Gamma>))"
  by (rule satandard_redundancy_criterion_extension[OF gd_ord_\<Gamma>_ngd_ord_\<Gamma> src.redudancy_criterion])
(*find_theorems name: src_ext*)

end

end

text {*
The following corresponds to Lemma 4.12:
*}

lemma (in linorder) set_sorted_list_of_multiset[simp]:
  "set (sorted_list_of_multiset M) = set_mset M"
  by (induct M) (simp_all add: local.set_insort_key)

lemma (in linorder) multiset_mset_sorted_list_of_multiset[simp]:
  "mset (sorted_list_of_multiset M) = M"
  by (induct M) (simp_all add: ac_simps)

lemma ord_resolve_lifting:
  assumes resolve: "ord_resolve_raw (S_M S M) CC D E"
  and select: "selection S"
  and selection_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>"
  and M_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> C \<cdot> \<rho> \<in> M \<longleftrightarrow> C \<in> M"
  and grounding: "{D, E} \<union> set_mset CC \<subseteq> grounding_of_clss M"
  obtains \<sigma> CC' D' E' where
    "is_ground_subst \<sigma>"
    "ord_resolve_raw S CC' D' E'"
    "CC = CC' \<cdot>cc \<sigma>" "D = D' \<cdot> \<sigma>" "E = E' \<cdot> \<sigma>"
    "{D', E'} \<union> set_mset CC' \<subseteq> M"
using resolve proof (atomize_elim, cases rule: ord_resolve_raw.cases)
  case (ord_resolve_raw Cf' ZZ AA AAA D' \<sigma>)
  note e = this(1) and cf' = this(2) and aa = this(3) and aaa = this(4) and cc = this(5) and
    d = this(6) and zz_e = this(7) and aa'_ne = this(8) and \<sigma>_mgu = this(9) and s_d = this(10) and
    a_max = this(11) and s_cc_e = this(12)
  interpret S: selection S by (rule select)

  obtain Dp \<sigma>D where pickD: "Dp \<in> M" "D = Dp \<cdot> \<sigma>D" "S_M S M D = S Dp \<cdot> \<sigma>D"
    and ground_\<sigma>D: "is_ground_subst \<sigma>D"
    using S_M_grounding_of_clss[OF select, of D M thesis] grounding by blast
  have "\<forall>C \<in> set_mset CC. \<exists>C' \<sigma>. C' \<in> M \<and> C = C' \<cdot> \<sigma> \<and> S_M S M C = S C' \<cdot> \<sigma> \<and> is_ground_subst \<sigma>"
    (is "\<forall>C \<in> set_mset CC. ?P C")
  proof (intro ballI)
    fix C
    assume "C \<in> set_mset CC"
    then obtain C' \<sigma> where "C' \<in> M" "C = C' \<cdot> \<sigma>" "S_M S M C = S C' \<cdot> \<sigma>" "is_ground_subst \<sigma>"
      using S_M_grounding_of_clss[OF select, of C M thesis] grounding by blast
    then show "?P C" by blast
  qed
  then obtain pickC pick\<sigma> where pick:
    "\<And>C. C \<in># CC \<Longrightarrow> pickC C \<in> M \<and> C = pickC C \<cdot> pick\<sigma> C \<and>
    S_M S M C = S (pickC C) \<cdot> pick\<sigma> C \<and> is_ground_subst (pick\<sigma> C)"
    unfolding bchoice_iff by blast

  let ?Cs = "multiset_linorder.sorted_list_of_multiset CC"
  let ?n = "length ?Cs"
  def Cs \<equiv> "map pickC ?Cs"
  then have Cs_M: "\<forall>C \<in> set Cs. C \<in> M" and "length Cs = ?n"
    using pick by auto

  def \<sigma>s \<equiv> "map pick\<sigma> ?Cs"
  then have "length \<sigma>s = ?n" and ground_\<sigma>s: "\<forall>\<sigma> \<in> set \<sigma>s. is_ground_subst \<sigma>"
    using pick by auto

  obtain \<rho>D \<rho>s where \<rho>s: "length \<rho>s = length Cs" "is_renaming \<rho>D" "\<forall>\<rho> \<in> set \<rho>s. is_renaming \<rho>"
    "var_disjoint ((Dp \<cdot> \<rho>D) # (Cs \<cdot>cls \<rho>s))"
    using make_var_disjoint[of "Dp # Cs"] by (auto simp: length_Suc_conv)

  from \<rho>s(2,3) obtain \<rho>D' \<rho>'s where "length \<rho>'s = length \<rho>s"
    and inv: "\<rho>D \<odot> \<rho>D' = id_subst" "\<rho>s \<odot>s \<rho>'s = replicate (length \<rho>s) id_subst"
    unfolding is_renaming_def comp_substs_def bchoice_iff
    by (induct \<rho>s) (fastforce simp: length_Suc_conv)+

  note lengths = \<open>length \<rho>'s = length \<rho>s\<close> \<rho>s(1) trans[OF \<open>length Cs = ?n\<close> sym[OF \<open>length \<sigma>s = ?n\<close>]]

  then have "Cs \<cdot>cls \<rho>s \<cdot>cls \<rho>'s = Cs" "Dp \<cdot> \<rho>D \<cdot> \<rho>D' = Dp"
    unfolding subst_cls_comp_subst[symmetric] subst_cls_lists_comp_substs[symmetric] inv by auto

  with lengths var_disjoint_ground[OF \<rho>s(4), of "(\<rho>D' \<odot> \<sigma>D) # (\<rho>'s \<odot>s \<sigma>s)"] ground_\<sigma>D ground_\<sigma>s
    obtain \<tau> where \<tau>: "is_ground_subst \<tau>" "Dp \<cdot> \<sigma>D = Dp \<cdot> \<rho>D \<cdot> \<tau>" "Cs \<cdot>cls \<sigma>s = Cs \<cdot>cls \<rho>s \<cdot>cl \<tau>"
    by auto

  moreover from pick have "?Cs = Cs \<cdot>cls \<sigma>s"
    unfolding subst_cls_lists_def Cs_def \<sigma>s_def
    by (auto simp only: set_map length_map length_zip nth_map nth_zip nth_mem list_eq_iff_nth_eq
       multiset_linorder.set_sorted_list_of_multiset[symmetric])

  then have "mset ?Cs = mset (Cs \<cdot>cls \<sigma>s)"
    by simp

  ultimately have "D =  Dp \<cdot> \<rho>D \<cdot> \<tau>" "CC = mset (Cs \<cdot>cls \<rho>s) \<cdot>cc \<tau>"
    using pickD by (simp_all add: subst_cls_list_def subst_cls_mset_def mset_map)

  def CC' \<equiv> "mset Cs"
  def P \<equiv> "mset \<rho>s"
  def CC'P \<equiv> "mset (zip Cs \<rho>s)"
  def CC'\<rho> \<equiv> "mset (Cs \<cdot>cls \<rho>s)"
  def ZZ\<rho> \<equiv> "ZZ"

  show "\<exists>\<sigma> CC' D' E'. is_ground_subst \<sigma> \<and> ord_resolve_raw S CC' D' E' \<and>
    CC = CC' \<cdot>cc \<sigma> \<and> D = D' \<cdot> \<sigma> \<and> E = E' \<cdot> \<sigma> \<and> {D', E'} \<union> set_mset CC' \<subseteq> M"
  proof (intro exI conjI)
    show "is_ground_subst \<tau>" by (metis \<tau>(1))
    show "ord_resolve_raw S CC'\<rho> (Dp \<cdot> \<rho>D) ((cf + d) \<cdot> x)"
      apply (rule ord_resolve_raw.intros)
      apply (simp_all add: selection_renaming_invariant[OF \<rho>s(2)])
      sorry

    show "CC = CC'\<rho> \<cdot>cc \<tau>"
      unfolding CC'_def CC'\<rho>_def \<open>CC = mset (Cs \<cdot>cls \<rho>s) \<cdot>cc \<tau>\<close> ..
    show "D = Dp \<cdot> \<rho>D \<cdot> \<tau>"
      unfolding \<open>D =  Dp \<cdot> \<rho>D \<cdot> \<tau>\<close> ..
    show "E = (cf + d) \<cdot> x \<cdot> \<tau>"
      unfolding e sorry
    from \<rho>s \<open>Dp \<in> M\<close> Cs_M show "{Dp \<cdot> \<rho>D, (cf + d) \<cdot> x} \<union> set_mset CC'\<rho> \<subseteq> M"
      apply (auto simp: M_renaming_invariant CC'\<rho>_def subst_cls_lists_def set_zip)
      sorry
  qed
qed

end

locale FO_resolution_with_selection =
  FO_resolution subst_atm id_subst comp_subst mgu less_atm +
  selection S
  for
    S :: "('a :: wellorder) clause \<Rightarrow> _" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s => 's => 's" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes
    N0 :: "'a clause set"
  assumes
    finite_N0: "finite N0"
begin

interpretation ground_resolution_with_S: ground_resolution_with_selection S
  by unfold_locales

lemma ground_prems_ground_ord_resolve_imp_ord_resolve_raw:
  assumes
    gr_cc: "is_ground_cls_mset CC" and
    gr_d: "is_ground_cls D" and
    res_e: "ground_resolution_with_S.ord_resolve CC D E"
  shows "ord_resolve_raw S CC D E"
using res_e proof (cases rule: ground_resolution_with_S.ord_resolve.cases)
  case (ord_resolve Cf' ZZ AA D')
  note e = this(1) and cf' = this(2) and aa = this(3) and cc = this(4) and d = this(5) and
    zz_ne = this(6) and s_d = this(7) and a_max = this(8) and s_cc_e = this(9)
  note case_prod_self_distrib[simp] = prod.case_distrib[of "case_prod f" for f]

  def ZZ_fo \<equiv> "{#(C', A, replicate_mset (Suc m) A). (C', A, m) \<in># ZZ#}"
  def AAA \<equiv> "{#{A}. (C', A, AA') \<in># ZZ_fo#}"

  have cf'_fo: "Cf' = \<Union># {#C'. (C', A, AA') \<in># ZZ_fo#}"
    unfolding ZZ_fo_def cf' by (auto intro: fun_cong)
  have aa_fo: "AA = {#A. (C', A, AA') \<in># ZZ_fo#}"
    unfolding ZZ_fo_def aa by auto
  have aaa_fo: "AAA = {#insert A (set_mset AA'). (C', A, AA') \<in># ZZ_fo#}"
    unfolding AAA_def ZZ_fo_def by (auto simp: if_distrib[of "insert A" for A] cong del: if_cong)
  have cc_fo: "CC = {#C' + poss AA'. (C', A, AA') \<in># ZZ_fo#}"
    unfolding ZZ_fo_def cc by auto
  have zz_fo_ne: "ZZ_fo \<noteq> {#}"
    unfolding ZZ_fo_def using zz_ne by simp
  then obtain \<rho> where \<rho>_mgu: "Some \<rho> = mgu (set_mset AAA)" and ren_\<rho>: "is_renaming \<rho>"
    using mgu_eq_id_subst[of "set_mset AAA"] unfolding AAA_def ZZ_fo_def 
    by (fastforce simp: Ball_def)

  have aa'_ne: "\<forall>(_, _, AA') \<in> set_mset ZZ_fo. AA' \<noteq> {#}"
    unfolding ZZ_fo_def by simp

  have gr_aa: "\<And>A. A \<in># AA \<Longrightarrow> is_ground_atm A"
    using gr_d unfolding d is_ground_cls_as_atms by auto
  have gr_d': "is_ground_cls D'"
    using d by (metis add.commute gr_d is_ground_cls_mono mset_le_add_left)

  have gr_cf': "is_ground_cls Cf'"
    unfolding cf'_fo using gr_cc[unfolded cc_fo] by (auto simp: is_ground_cls_mset_def)

  { assume max: "Max (atms_of D) \<in># AA" and card: "size AA = 1"
    then obtain A where a: "AA = {#A#}"
      using size_1_singleton_mset by blast
    hence gr_a: "is_ground_atm A"
      using gr_aa by (metis multi_member_last)
    have "\<forall>B \<in> atms_of (D' \<cdot> \<rho>). \<not> less_atm (A \<cdot>a \<rho>) B"
      using max card unfolding d a
      apply (auto simp: gr_a gr_d' split: if_splits)
      apply (subst (asm) ground_less_atm_iff)
      apply (rule gr_a)
      apply (metis gr_d' is_ground_cls_imp_is_ground_atm)
      by (metis Max.coboundedI finite_atms_of finite_insert insertI2 not_le)
    hence " (\<forall>A. A \<in># AA \<longrightarrow> (\<forall>B \<in> atms_of (D' \<cdot> \<rho>). \<not> less_atm (A \<cdot>a \<rho>) B))"
      using a by simp }
  hence s_d_fo: "S D = negs AA \<or>
    S D = {#} \<and> size AA = 1 \<and> (\<forall>A. A \<in># AA \<longrightarrow> (\<forall>B\<in>atms_of (D' \<cdot> \<rho>). \<not> less_atm (A \<cdot>a \<rho>) B))"
    using s_d by fast

  have gr_c: "\<And>C. C \<in># {#C' + replicate_mset (Suc m) (Pos A). (C', A, m) \<in># ZZ#} \<Longrightarrow> is_ground_cls C"
    using gr_cc unfolding cc is_ground_cls_mset_def by auto
  have gr_c': "\<And>C' A m. (C', A, m) \<in># ZZ \<Longrightarrow> is_ground_cls C'"
    by (rule is_ground_cls_mono[rotated]) (rule gr_c, auto)

  have gr_a: "\<And>C' A m. (C', A, m) \<in># ZZ \<Longrightarrow> is_ground_atm A"
    using gr_aa[unfolded aa] by force

  have a_max_fo: "\<forall>(C', A, _) \<in> set_mset ZZ_fo. \<forall>B \<in> atms_of (C' \<cdot> \<rho>). \<not> less_eq_atm (A \<cdot>a \<rho>) B"
    unfolding ZZ_fo_def
    apply (auto simp: gr_c' gr_a)
    apply (rename_tac C' A B m)
    apply (subst (asm) ground_less_eq_atm_iff)
    apply (auto simp: gr_a)
    apply (metis gr_c' is_ground_cls_imp_is_ground_atm)
    using a_max not_le old.prod.case by fastforce
  have res_e_fo: "ord_resolve_raw S CC D ((Cf' + D') \<cdot> \<rho>)"
    using cf'_fo aa_fo aaa_fo cc_fo d zz_fo_ne aa'_ne \<rho>_mgu s_d_fo a_max_fo s_cc_e
    by (rule ord_resolve_raw.intros)

  have "(Cf' + D') \<cdot> \<rho> = Cf' + D'"
    using gr_cf' gr_d' by simp
  thus ?thesis
    unfolding e using res_e_fo by simp
qed

lemma ground_prems_ord_resolve_imp_ord_resolve:
  assumes
    gr_cc: "is_ground_cls_mset CC" and
    gr_d: "is_ground_cls D" and
    gr_res: "ground_resolution_with_S.ord_resolve CC D E"
  shows "ord_resolve S CC D E"
  by (rule ord_resolve_raw_imp_ord_resolve)
    (rule ground_prems_ground_ord_resolve_imp_ord_resolve_raw[OF gr_cc gr_d gr_res])

lemma "C \<in># {#f x y z. (x, y, z) \<in># \<Sigma>#}"
  oops

lemma ground_prems_ord_resolve_raw_imp_ground_ord_resolve:
  assumes
    gr_cc: "is_ground_cls_mset CC" and
    gr_d: "is_ground_cls D" and
    res: "ord_resolve_raw S CC D E"
  shows "ground_resolution_with_S.ord_resolve CC D E"
using res proof (cases rule: ord_resolve_raw.cases)
  case (ord_resolve_raw Cf' ZZ AA AAA D' \<sigma>)
  note e = this(1) and cf' = this(2) and aa = this(3) and aaa = this(4) and cc = this(5) and
    d = this(6) and zz_ne = this(7) and aa'_ne = this(8) and \<sigma>_mgu = this(9) and s_d = this(10) and
    a_max = this(11) and s_cc_e = this(12)
  note case_prod_self_distrib[simp] = prod.case_distrib[of "case_prod f" for f]

  have "\<forall>(_, _, AA') \<in> set_mset ZZ. \<forall>A. A \<in># AA' \<longrightarrow> is_ground_atm A"
    using gr_cc unfolding cc is_ground_cls_mset_def
    sorry

  def ZZ_gr \<equiv> "{#(C', A, size AA - 1). (C', A, AA) \<in># ZZ#}"

  have cf'_gr: "Cf' = \<Union># {#C'. (C', A, m) \<in># ZZ_gr#}"
    unfolding ZZ_gr_def cf' by (auto intro: fun_cong)
  have aa_gr: "AA = {#A. (C', A, m) \<in># ZZ_gr#}"
    unfolding ZZ_gr_def aa by auto
  have cc_gr: "CC = {#C' + replicate_mset (Suc m) (Pos A). (C', A, m) \<in># ZZ_gr#}"
    unfolding ZZ_gr_def cc
    apply simp
    apply (rule image_mset_cong)
    apply auto
    apply (rename_tac C A AA')
    sorry
  have zz_fo_ne: "ZZ_gr \<noteq> {#}"
    unfolding ZZ_gr_def using zz_ne by simp
  then obtain \<rho> where \<rho>_mgu: "Some \<rho> = mgu (set_mset AAA)" and ren_\<rho>: "is_renaming \<rho>"
    (*
    using mgu_eq_id_subst[of "set_mset AAA"] unfolding AAA_def ZZ_fo_def by auto
    *)
    sorry

  have "is_ground_cls Cf'"
    (*
    unfolding cf'_fo using gr_cc[unfolded cc_fo] by (auto simp: is_ground_cls_mset_def)
    *)
    sorry
  moreover have "is_ground_cls D'"
    sorry
  ultimately have e': "E = Cf' + D'"
    unfolding e by simp
  show ?thesis
    unfolding e' apply (rule ground_resolution_with_S.ord_resolve)
    sorry
qed



definition ord_FO_\<Gamma> :: "'a inference set" where
  "ord_FO_\<Gamma> = {Infer CC D E | CC D E. ord_resolve_raw S CC D E}"

interpretation ord_FO_resolution: inference_system ord_FO_\<Gamma> .

inductive subsume_resolve :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "subsume_resolve (D + {#L#}) (C + (D + {#- L#}) \<cdot> \<sigma>) (C + D \<cdot> \<sigma>)"

text {*
@{text O} denotes relation composition in Isabelle, so the formalization uses @{text Q} instead.
*}
inductive resolution_prover (infix "\<leadsto>" 50) where
 tautology_deletion: "(\<forall>I. I \<Turnstile> C) \<Longrightarrow> (N \<union> {C}, P, Q) \<leadsto> (N, P, Q)"
| forward_subsumption: "(\<exists>D \<in> P \<union> Q. subsumes D C) \<Longrightarrow> (N \<union> {C}, P, Q) \<leadsto> (N, P, Q)"
| backward_subsumption_P: "(\<exists>D \<in> N. properly_subsumes D C) \<Longrightarrow> (N, P \<union> {C}, Q) \<leadsto> (N, P, Q)"
| backward_subsumption_Q: "(\<exists>D \<in> N. properly_subsumes D C) \<Longrightarrow> (N, P, Q \<union> {C}) \<leadsto> (N, P, Q)"
| forward_reduction: "(\<exists>D L'. D + {#L'#} \<in> P \<union> Q \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<le># C) \<Longrightarrow>
    (N \<union> {C + {#L#}}, P, Q) \<leadsto> (N \<union> {C}, P, Q)"
| backward_reduction_P: "(\<exists>D L'. D + {#L'#} \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<le># C) \<Longrightarrow>
    (N, P \<union> {C + {#L#}}, Q) \<leadsto> (N, P \<union> {C}, Q)"
| backward_reduction_Q: "(\<exists>D L'. D + {#L'#} \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<le># C) \<Longrightarrow>
    (N, P, Q \<union> {C + {#L#}}) \<leadsto> (N, P \<union> {C}, Q)"
| clause_processing: "(N \<union> {C}, P, Q) \<leadsto> (N, P \<union> {C}, Q)"
| inference_computation:
    "N = concls_of (ord_FO_resolution.inferences_from (Q \<union> {C})) \<Longrightarrow>
     ({}, P \<union> {C}, Q) \<leadsto> (N, P, Q \<union> {C})"

definition limit_state ::
  "('a clause set \<times> 'a clause set \<times> 'a clause set) llist \<Rightarrow>
     'a clause set \<times> 'a clause set \<times> 'a clause set"
where
  "limit_state Sts = (llimit (lmap (\<lambda>(N, _, _). N) Sts), llimit (lmap (\<lambda>(_, P, _). P) Sts),
     llimit (lmap (\<lambda>(_, _, Q). Q) Sts))"

definition fair_state_seq where
  "fair_state_seq Sts = (let (N, P, _) = limit_state Sts in N = {} \<and> P = {})"

text {*
The following corresponds to Lemma 4.10:
*}

lemma resolution_prover_rtc_deriv:
  assumes "St \<leadsto> St'"
  shows True (* "src.derive S S'" *)
  oops

text {*
The following corresponds to Lemma 4.11:
*}

lemma fair_imp_limit_minus_Rf_subset_ground_limit_state:
  assumes
    deriv: "derivation (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    ns: "Ns = lmap grounding_of_state Sts"
  shows "llimit Ns - Rf (llimit Ns) \<subseteq> grounding_of_state (limit_state Sts)"
  sorry

text {*
The following corresponds to Theorem 4.13:
*}

theorem
  assumes
    deriv: "derivation (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    unsat: "\<not> satisfiable (grounding_of_state (limit_state Sts))"
  shows "{#} \<in> clss_of_state (limit_state Sts)"
  sorry

text {*
  lifted ordering to clauses satisfies characteristic equivalence
  prove wf
  fix problem N0?
  selection function S

  prove ord\_resolve with all premises ground coincides with ground ord\_resolve
  define subsumes (properly\_subsumes, variants)
  wf subsumes
  inductive resolution\_prover "~>"

  generalize derivation
  define G(C) and generalization to sets of clauses
  clss\_of\_state

  lemma 4.10
  fairness
  lemma 4.11
  define S\_M using choice
  lemma 4.12 (lifting)
  thm 4.13
*}

end




end
