(*  Title:       First-Order Ordered Resolution Calculus with Selection
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2016, 2017
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>First-Order Ordered Resolution Calculus with Selection\<close>

text \<open>
This material is based on Section 4.3 (``A Simple Resolution Prover for First-Order Clauses) of 
Bachmair and Ganzinger's chapter. Specifically, it formalizes the calculus in Figure 4 called
Ordered Resolution for First-Order Standard Clauses and its related lemmas and theorems including 
soundness and Lemma 4.12 (the lifting lemma).
\<close>

theory FO_Ordered_Resolution
  imports Abstract_Substitution Ordered_Ground_Resolution Standard_Redundancy
begin

text \<open>
The following corresponds to to pages 41 and 42 of Section 4.3, until Figure 5 and its explanation.
\<close>

locale FO_resolution = mgu subst_atm id_subst comp_subst renamings_apart mgu
  for
    subst_atm :: "'a :: wellorder \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a literal multiset list \<Rightarrow> 's list" and
    mgu :: "'a set set \<Rightarrow> 's option" +
  fixes
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    less_atm_iff: "less_atm A B \<longleftrightarrow> (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> A \<cdot>a \<sigma> < B \<cdot>a \<sigma>)"
begin


subsection \<open>Library\<close>

(* FIXME: Where do we want these lemmas? *)
lemma (in linorder) set_sorted_list_of_multiset[simp]:
  "set (sorted_list_of_multiset M) = set_mset M"
  by (induct M) (simp_all add: set_insort_key)

lemma (in linorder) multiset_mset_sorted_list_of_multiset[simp]:
  "mset (sorted_list_of_multiset M) = M"
  by (induct M) (simp_all add: ac_simps)

(* FIXME: move? *)
lemma eql_map_neg_lit_eql_atm:
  assumes "map (\<lambda>L. L \<cdot>l \<eta>) (map Neg As') = map Neg As"
  shows "As' \<cdot>al \<eta> = As"
  using assms by (induction As' arbitrary: As) auto

lemma instance_list:
  assumes "negs (mset As) = SDA' \<cdot> \<eta>"
  shows "\<exists>As'. negs (mset As') = SDA' \<and> As' \<cdot>al \<eta> = As"
proof -
  from assms have negL: "\<forall>L \<in># SDA'. is_neg L"
    using Melem_subst_cls subst_lit_in_negs_is_neg by metis

  from assms(1) have "{#L \<cdot>l \<eta>. L \<in># SDA'#} = mset (map Neg As)"
    using subst_cls_def by auto
  then have "\<exists>NAs'. map (\<lambda>L. L \<cdot>l \<eta>) NAs' = map Neg As \<and> mset NAs' = SDA'"
    using image_mset_of_subset_list[of "\<lambda>L. L \<cdot>l \<eta>" SDA' "map Neg As"] by auto
  then obtain As' where As'_p:
    "map (\<lambda>L. L \<cdot>l \<eta>) (map Neg As') = map Neg As \<and> mset (map Neg As') = SDA'"
    by (metis (no_types, lifting) Neg_atm_of_iff negL ex_map_conv set_mset_mset)

  have "negs (mset As') = SDA'"
    using As'_p by auto
  moreover have "map (\<lambda>L. L \<cdot>l \<eta>) (map Neg As') = map Neg As"
    using As'_p by auto
  then have "As' \<cdot>al \<eta> = As"
    using eql_map_neg_lit_eql_atm by auto
  ultimately show ?thesis
    by auto
qed


subsection \<open>First-order logic\<close>

definition less_eq_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "less_eq_atm A B \<longleftrightarrow> less_atm A B \<or> A = B"

lemma ground_less_atm_iff: "is_ground_atm A \<Longrightarrow> is_ground_atm B \<Longrightarrow> less_atm A B \<longleftrightarrow> A < B"
  unfolding is_ground_atm_def less_atm_iff by (auto intro: ex_ground_subst)

lemma ground_less_eq_atm_iff: "is_ground_atm A \<Longrightarrow> is_ground_atm B \<Longrightarrow> less_eq_atm A B \<longleftrightarrow> A \<le> B"
  unfolding less_eq_atm_def ground_less_atm_iff by fastforce

definition subsumes :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "subsumes C D \<longleftrightarrow> (\<exists>\<sigma>. C \<cdot> \<sigma> \<subseteq># D)"

definition strictly_subsumes :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "strictly_subsumes C D \<longleftrightarrow> subsumes C D \<and> \<not> subsumes D C"

definition variants :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "variants C D \<longleftrightarrow> subsumes C D \<and> subsumes D C"

inductive true_fo_cls :: "'a interp \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<Turnstile>fo" 50) where
  true_fo_cls: "(\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile> C \<cdot> \<sigma>) \<Longrightarrow> I \<Turnstile>fo C"

lemma true_fo_cls_inst: "I \<Turnstile>fo C \<Longrightarrow> is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile> C \<cdot> \<sigma>"
  by (rule true_fo_cls.induct)

inductive true_fo_cls_mset :: "'a interp \<Rightarrow> 'a clause multiset \<Rightarrow> bool" (infix "\<Turnstile>fom" 50) where
  true_fo_cls_mset: "(\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile>m CC \<cdot>cm \<sigma>) \<Longrightarrow> I \<Turnstile>fom CC"

lemma true_fo_cls_mset_inst: "I \<Turnstile>fom C \<Longrightarrow> is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile>m C \<cdot>cm \<sigma>"
  by (rule true_fo_cls_mset.induct)

lemma true_fo_cls_mset_def2: "I \<Turnstile>fom CC \<longleftrightarrow> (\<forall>C \<in># CC. I \<Turnstile>fo C)"
  unfolding true_fo_cls_mset.simps true_fo_cls.simps true_cls_mset_def by auto

context
  fixes S :: "'a clause \<Rightarrow> 'a clause"
begin


subsection \<open>Calculus\<close>

text \<open>
The following corresponds to Figure 4.
\<close>

definition maximal_in :: "'a \<Rightarrow> 'a literal multiset \<Rightarrow> bool" where (* Would "'a \<Rightarrow> 'a set \<Rightarrow> bool" be cleaner?  *)
   "maximal_in A C \<longleftrightarrow> (\<forall>B \<in> atms_of C. \<not> less_atm A B)"

(* FIXME: Why is the nonstrict version a definition and the strict version an abbreviation? *)
abbreviation strictly_maximal_in :: "'a \<Rightarrow> 'a literal multiset \<Rightarrow> bool" where (* Would "'a \<Rightarrow> 'a set \<Rightarrow> bool" be cleaner?  *)
  "strictly_maximal_in A C \<equiv> (\<forall>B \<in> atms_of C. \<not> less_eq_atm A B)"

lemma strictly_maximal_in_maximal_in: "strictly_maximal_in A C \<Longrightarrow> maximal_in A C"
  unfolding maximal_in_def less_eq_atm_def by auto

inductive eligible :: "'s \<Rightarrow> 'a list \<Rightarrow> 'a clause \<Rightarrow> bool" where
  eligible:
    "S DA = negs (mset As) \<or> S DA = {#} \<and> length As = 1 \<and> maximal_in ((As ! 0) \<cdot>a \<sigma>) (DA \<cdot> \<sigma>) \<Longrightarrow>
     eligible \<sigma> As DA"

inductive ord_resolve :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 's \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve:
  "length CAs = n \<Longrightarrow>
   length Cs = n \<Longrightarrow>
   length AAs = n \<Longrightarrow>
   length As = n \<Longrightarrow>
   n \<noteq> 0 \<Longrightarrow>
   \<forall>i < n. CAs ! i = Cs ! i + (poss (AAs ! i)) \<Longrightarrow> (* could be written with map *)
   \<forall>i < n. AAs ! i \<noteq> {#} \<Longrightarrow>
   Some \<sigma> = mgu (set_mset ` set (map2 add_mset As AAs)) \<Longrightarrow>
   eligible \<sigma> As (D + negs (mset As)) \<Longrightarrow>
   \<forall>i < n. strictly_maximal_in (As ! i \<cdot>a \<sigma>) ((Cs ! i) \<cdot> \<sigma>) \<Longrightarrow>
   \<forall>i < n. S (CAs ! i) = {#} \<Longrightarrow> (* Use the ! style instead maybe, or maybe us the \<forall> \<in> . style above *)
   ord_resolve CAs (D + negs (mset As)) \<sigma> (((\<Union># (mset Cs)) + D) \<cdot> \<sigma>)"

inductive ord_resolve_rename :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 's \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve_rename:
  "\<rho> = hd (renamings_apart (DA # CAs)) \<Longrightarrow>
   \<rho>s = tl (renamings_apart (DA # CAs)) \<Longrightarrow>
   ord_resolve (CAs \<cdot>\<cdot>cl \<rho>s) (DA \<cdot> \<rho>) \<sigma> E \<Longrightarrow>
   ord_resolve_rename CAs DA \<sigma> E"


subsection \<open>Soundness\<close>

text \<open>
The following is the soundness of the calculus. This is not discussed in the chapter.
\<close>

lemma ground_prems_ord_resolve_rename_imp_ord_resolve:
  assumes
    gr_cc: "is_ground_cls_list CAs" and
    gr_d: "is_ground_cls DA" and
    res_e_re: "ord_resolve_rename CAs DA \<sigma> E"
  shows "ord_resolve CAs DA \<sigma> E"
  using res_e_re
proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  note \<rho> = this(1) and P = this(2) and res = this(3)
  then have rename_P: "\<forall>\<rho> \<in> set P. is_renaming \<rho>"
    using renamings_apart_p by (metis list.sel(2) list.set_sel(2))
  from P have len: "length P = length CAs"
    using renamings_apart_p by auto
  have res_e: "ord_resolve (CAs \<cdot>\<cdot>cl P) (DA \<cdot> \<rho>) \<sigma> E"
    using res by auto
  have "CAs \<cdot>\<cdot>cl P = CAs"
    using len gr_cc by auto
  moreover
  have "DA \<cdot> \<rho> = DA"
    using gr_d by auto
  ultimately show ?thesis
    using res_e by auto
qed

text \<open>
The following lemma is used to prove first-order soundness. It is also used to prove lemma 4.10
which is a lemma of the completeness theorem.
\<close>

lemma ord_resolve_ground_inst_sound:
  assumes
    res_e: "ord_resolve CAs DA \<sigma> E"
  assumes
    cc_inst_true: "I \<Turnstile>m (mset CAs) \<cdot>cm \<sigma> \<cdot>cm \<eta>"
  assumes
    d_inst_true: "I \<Turnstile> DA \<cdot> \<sigma> \<cdot> \<eta>"
  assumes ground_subst_\<eta>: "is_ground_subst \<eta>"
  shows "I \<Turnstile> E \<cdot> \<eta>"
  using assms
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Cs AAs As D)
  note DA = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4) and 
    aas_len = this(5) and as_len = this(6) and cas = this(8) and mgu = this(10) and
    len = this(1)
    
  have len: "length CAs = length As"
    using as_len cas_len by auto
  have "is_ground_subst (\<sigma> \<odot> \<eta>)"
    using ground_subst_\<eta> by (rule is_ground_comp_subst)
  then have cc_true: "I \<Turnstile>m (mset CAs) \<cdot>cm \<sigma> \<cdot>cm \<eta>" and d_true: "I \<Turnstile> DA \<cdot> \<sigma> \<cdot> \<eta>"
    using cc_inst_true d_inst_true by auto

  from mgu have unif: "\<forall>i<n. \<forall>A\<in>#AAs ! i. A \<cdot>a \<sigma> = As ! i \<cdot>a \<sigma>"
    using mgu_unifier as_len aas_len by blast

  show "I \<Turnstile> E \<cdot> \<eta>"
  proof (cases "\<forall>A \<in> set As. A \<cdot>a \<sigma> \<cdot>a \<eta> \<in> I")
    case True
    then have "\<not> I \<Turnstile> negs (mset As) \<cdot> \<sigma> \<cdot> \<eta>"
      unfolding true_cls_def[of I] by auto
    then have "I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<eta>"
      using d_true DA by auto
    then show ?thesis
      unfolding e by auto
  next
    case False
    then obtain i where a_in_aa: "i < length CAs" and a_false: "(As ! i) \<cdot>a \<sigma> \<cdot>a \<eta> \<notin> I"
      using DA len by (metis in_set_conv_nth)
    define C where "C \<equiv> Cs ! i"
    define BB where "BB \<equiv> AAs ! i"
    have c_cf': "C \<subseteq># \<Union># mset CAs"
      unfolding C_def using a_in_aa cas cas_len
      by (metis less_subset_eq_Union_mset mset_subset_eq_add_left subset_mset.order.trans)
    have c_in_cc: "C + poss BB \<in># mset CAs"
      using C_def BB_def a_in_aa cas_len in_set_conv_nth cas by fastforce
    {
      fix B
      assume "B \<in># BB"
      then have "B \<cdot>a \<sigma> = (As ! i) \<cdot>a \<sigma>"
        using unif a_in_aa cas_len unfolding BB_def by auto
    }
    then have "\<not> I \<Turnstile> poss BB \<cdot> \<sigma> \<cdot> \<eta>"
      using a_false by (auto simp: true_cls_def)
    moreover have "I \<Turnstile> (C + poss BB) \<cdot> \<sigma> \<cdot> \<eta>"
      using c_in_cc cc_true true_cls_mset_true_cls[of I "mset CAs \<cdot>cm \<sigma> \<cdot>cm \<eta>"] by force
    ultimately have "I \<Turnstile> C \<cdot> \<sigma> \<cdot> \<eta>"
      by simp
    then show ?thesis
      unfolding e subst_cls_union using c_cf' C_def a_in_aa cas_len cs_len
      by (metis (no_types, lifting) mset_subset_eq_add_left nth_mem_mset set_mset_mono sum_mset.remove true_cls_mono subst_cls_mono)
  qed
qed

lemma ord_resolve_sound:
  assumes
    res_e: "ord_resolve CAs DA \<sigma> E" and
    cc_d_true: "I \<Turnstile>fom mset CAs + {#DA#}"
  shows "I \<Turnstile>fo E"
  apply (rule true_fo_cls)
  using assms
proof (cases rule: ord_resolve.cases)
  fix \<eta>
  assume ground_subst_\<eta>: "is_ground_subst \<eta>"
  case (ord_resolve n Cs AAs As D)
  note DA = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4)
    and aas_len = this(5) and as_len = this(6) and cas = this(8) and mgu = this(10)

  have len: "length CAs = length As"
    using as_len cas_len by auto
  have "is_ground_subst (\<sigma> \<odot> \<eta>)"
    using ground_subst_\<eta> by (rule is_ground_comp_subst)
  then have cas_true: "I \<Turnstile>m (mset CAs) \<cdot>cm \<sigma> \<cdot>cm \<eta>" and da_true: "I \<Turnstile> DA \<cdot> \<sigma> \<cdot> \<eta>"
    using true_fo_cls_mset_inst[OF cc_d_true, of "\<sigma> \<odot> \<eta>"] by auto
  show "I \<Turnstile> E \<cdot> \<eta>"
    using ord_resolve_ground_inst_sound[OF res_e cas_true da_true] ground_subst_\<eta> by auto
qed

lemma subst_sound:
  assumes "I \<Turnstile>fo C"
  shows "I \<Turnstile>fo (C \<cdot> \<rho>)"
  using assms
  by (metis is_ground_comp_subst subst_cls_comp_subst true_fo_cls true_fo_cls_inst)

lemma true_fo_cls_mset_true_fo_cls: "(I \<Turnstile>fom CC) \<Longrightarrow> C \<in># CC \<Longrightarrow> I \<Turnstile>fo C"
  using true_fo_cls_mset_def2 by auto

lemma subst_sound_scl:
  assumes len: "length P = length CAs"
  assumes true_cas: "I \<Turnstile>fom mset CAs"
  shows "I \<Turnstile>fom mset (CAs \<cdot>\<cdot>cl P)"
proof -
  from true_cas have "\<forall>CA. CA\<in># mset CAs \<longrightarrow> (I \<Turnstile>fo CA)"
    using true_fo_cls_mset_true_fo_cls by auto
  then have "\<forall>CA. CA \<in> set CAs \<longrightarrow> (I \<Turnstile>fo CA)"
    by auto
  then have "\<forall>i. i < length CAs \<longrightarrow> (I \<Turnstile>fo  (CAs ! i))"
    using in_set_conv_nth[of _ CAs] by blast
  then have "\<forall>i. i < length CAs \<longrightarrow> (I \<Turnstile>fo  (CAs ! i) \<cdot> P ! i)"
    using subst_sound len by auto
  then have true_cp: "\<forall>i. i < length CAs \<longrightarrow> (I \<Turnstile>fo (CAs ! i \<cdot> P ! i))"
    by auto
  {
    fix CA
    assume "CA \<in># mset (CAs \<cdot>\<cdot>cl P)"
    then have "CA \<in> set_mset (mset ((CAs \<cdot>\<cdot>cl P)))"
      by -
    then have "CA \<in> set (CAs \<cdot>\<cdot>cl P)"
      by auto
    then obtain i where i_x: "i < length (CAs \<cdot>\<cdot>cl P) \<and> CA = (CAs \<cdot>\<cdot>cl P) ! i"
      using in_set_conv_nth by metis
    then have "I \<Turnstile>fo CA"
      using true_cp unfolding subst_cls_lists_def by (simp add: len)
  }
  then show ?thesis unfolding true_fo_cls_mset_def2 by auto
qed

text \<open>
This is a lemma of 4.11
\<close>

lemma ord_resolve_rename_ground_inst_sound:
  assumes
    res_e: "ord_resolve_rename CAs DA \<sigma> E" and
    \<rho>s: "\<rho>s = tl (renamings_apart (DA # CAs))" and
    \<rho>: "\<rho> = hd (renamings_apart (DA # CAs))" and
    cc_inst_true: "I \<Turnstile>m (mset (CAs \<cdot>\<cdot>cl \<rho>s)) \<cdot>cm \<sigma> \<cdot>cm \<eta>" and
    d_inst_true: "I \<Turnstile> DA \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<eta>" and
    ground_subst_\<eta>: "is_ground_subst \<eta>"
  shows "I \<Turnstile> E \<cdot> \<eta>"
  using assms
proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho>_twin \<rho>s_twin)
  then show ?thesis
    using ord_resolve_ground_inst_sound[of _ _ \<sigma> E I \<eta>] \<rho>s \<rho> cc_inst_true d_inst_true ground_subst_\<eta>
    by simp
qed

lemma ord_resolve_rename_sound:
  assumes
    res_e: "ord_resolve_rename CAs DA \<sigma> E" and
    cc_d_true: "I \<Turnstile>fom (mset CAs) + {#DA#}"
  shows "I \<Turnstile>fo E"
  using res_e
proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  note \<rho> = this(1) and P = this(2) and res = this(3)
  then have len: "length P = length CAs"
    using renamings_apart_p by auto
  have "I \<Turnstile>fom (mset (CAs \<cdot>\<cdot>cl P)) + {#DA \<cdot> \<rho>#}"
    using subst_sound_scl[OF len, of I] subst_sound[of I DA] cc_d_true
    by (simp add: true_fo_cls_mset_def2)
  then show "I \<Turnstile>fo E"
    using ord_resolve_sound[of "CAs \<cdot>\<cdot>cl P" "DA \<cdot> \<rho>" \<sigma> E I, OF res] by simp
qed


subsection \<open>Lifting\<close>

text \<open>
The following corresponds to the section between lemmas 4.11 and 4.12.
\<close>

context
  fixes M :: "'a clause set"
  assumes select: "selection S"
begin

interpretation selection
  by (rule select)

definition S_M :: "'a literal multiset \<Rightarrow> 'a literal multiset" where
  "S_M C =
   (if C \<in> grounding_of_clss M then
      (SOME C'. \<exists>D \<sigma>. D \<in> M \<and> C = D \<cdot> \<sigma> \<and> C' = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>)
    else
      S C)"

lemma S_M_grounding_of_clss:
  assumes "C \<in> grounding_of_clss M"
  obtains D \<sigma> where "D \<in> M \<and> C = D \<cdot> \<sigma> \<and> S_M C = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>"
proof (atomize_elim, unfold S_M_def eqTrueI[OF assms] if_True, rule someI_ex)
  from assms show "\<exists>C' D \<sigma>. D \<in> M \<and> C = D \<cdot> \<sigma> \<and> C' = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>"
    by (auto simp: grounding_of_clss_def grounding_of_cls_def)
qed

lemma S_M_not_grounding_of_clss: "C \<notin> grounding_of_clss M \<Longrightarrow> S_M C = S C"
  unfolding S_M_def by simp

lemma S_M_selects_subseteq: "S_M C \<subseteq># C"
  by (metis S_M_grounding_of_clss S_M_not_grounding_of_clss S_selects_subseteq subst_cls_mono_mset)

lemma S_M_selects_neg_lits: "L \<in># S_M C \<Longrightarrow> is_neg L"
  by (metis Melem_subst_cls S_M_grounding_of_clss S_M_not_grounding_of_clss S_selects_neg_lits
      subst_lit_is_neg)

end

end

text \<open>
The following corresponds to Lemma 4.12:
\<close>

lemma map2_add_mset_map:
  assumes "length AAs' = n" and "length As' = n"
  shows "map2 add_mset (As' \<cdot>al \<eta>) (AAs' \<cdot>aml \<eta>) = map2 add_mset As' AAs' \<cdot>aml \<eta>"
  using assms
proof (induction n arbitrary: AAs' As')
  case (Suc n)
  then have "map2 add_mset (tl As' \<cdot>al \<eta>) (tl AAs' \<cdot>aml \<eta>) = map2 add_mset (tl As') (tl AAs') \<cdot>aml \<eta>"
    by simp
  then have "map2 add_mset (tl (As' \<cdot>al \<eta>)) (tl (AAs' \<cdot>aml \<eta>)) = map2 add_mset (tl As') (tl AAs') \<cdot>aml \<eta>"
    by simp
  moreover
  have Succ: "length (As' \<cdot>al \<eta>) = Suc n" "length (AAs' \<cdot>aml \<eta>) = Suc n"
    using Suc(3) Suc(2) by auto
  then have "length (tl (As' \<cdot>al \<eta>)) = n" "length (tl (AAs' \<cdot>aml \<eta>)) = n"
    by auto
  then have "length (map2 add_mset (tl (As' \<cdot>al \<eta>)) (tl (AAs' \<cdot>aml \<eta>))) = n"
    "length (map2 add_mset (tl As') (tl AAs') \<cdot>aml \<eta>) = n"
    using Suc(2,3) by auto
  ultimately
  have "\<forall>i < n. (map2 add_mset (tl (As' \<cdot>al \<eta>)) (tl (AAs' \<cdot>aml \<eta>))) ! i = (map2 add_mset (tl As') (tl AAs') \<cdot>aml \<eta>) ! i"
    by auto
  then have "\<forall>i < n. tl (map2 add_mset ( (As' \<cdot>al \<eta>)) ((AAs' \<cdot>aml \<eta>))) ! i = tl (map2 add_mset (As') (AAs') \<cdot>aml \<eta>) ! i"
    using Suc(2,3) Succ by (simp add: map2_tl map_tl subst_atm_mset_list_def del: subst_atm_list_tl)
  moreover
  have nn: "length (map2 add_mset ((As' \<cdot>al \<eta>)) ((AAs' \<cdot>aml \<eta>))) = Suc n"
    "length (map2 add_mset (As') (AAs') \<cdot>aml \<eta>) = Suc n"
    using Succ Suc by auto
  ultimately
  have "\<forall>i. i < Suc n \<longrightarrow> i > 0 \<longrightarrow> map2 add_mset (As' \<cdot>al \<eta>) (AAs' \<cdot>aml \<eta>) ! i = (map2 add_mset As' AAs' \<cdot>aml \<eta>) ! i"
    by (metis (no_types) Suc.prems(1) Suc.prems(2) Succ(1) Succ(2) \<open>length (map2 add_mset (tl (As' \<cdot>al \<eta>)) (tl (AAs' \<cdot>aml \<eta>))) = n\<close>
        \<open>map2 add_mset (tl (As' \<cdot>al \<eta>)) (tl (AAs' \<cdot>aml \<eta>)) = map2 add_mset (tl As') (tl AAs') \<cdot>aml \<eta>\<close> less_Suc_eq_0_disj map2_tl map_tl neq0_conv nth_tl subst_atm_mset_list_def)
  moreover
  have "add_mset (hd As' \<cdot>a \<eta>) (hd AAs' \<cdot>am \<eta>) = add_mset (hd As') (hd AAs') \<cdot>am \<eta>"
    unfolding subst_atm_mset_def by auto
  then have "(map2 add_mset (As' \<cdot>al \<eta>) (AAs' \<cdot>aml \<eta>)) ! 0  = (map2 add_mset (As') (AAs') \<cdot>aml \<eta>) ! 0"
    using Suc by (simp add: Succ(2) subst_atm_mset_def)
  ultimately
  have "\<forall>i < Suc n. (map2 add_mset (As' \<cdot>al \<eta>) (AAs' \<cdot>aml \<eta>)) ! i  = (map2 add_mset (As') (AAs') \<cdot>aml \<eta>) ! i"
    using Suc by auto
  then show ?case
    using nn list_eq_iff_nth_eq by metis
next
  case 0 then show ?case
    by auto
qed

lemma maximal_in_gen:
  assumes "maximal_in (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)"
  shows "maximal_in A C"
proof -
  from assms have "\<forall>B \<in> atms_of (C \<cdot> \<sigma>). \<not> less_atm (A \<cdot>a \<sigma>) B"
    unfolding maximal_in_def by -
  then have ll: "\<forall>B \<in> atms_of (C \<cdot> \<sigma>). \<not> (\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma>')"
    unfolding less_atm_iff by -
  have "\<forall>B \<in> atms_of C. \<not> (\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma> \<cdot>a \<sigma>')"
    using ll by auto
  then have "\<forall>B \<in> atms_of C. \<not> (\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma>' < B \<cdot>a \<sigma>')"
    using is_ground_comp_subst by fastforce
  then have "\<forall>B \<in> atms_of C. \<not> (less_atm A B)"
    unfolding less_atm_iff by -
  then show ?thesis unfolding less_eq_atm_def maximal_in_def by auto
qed

lemma strictly_maximal_in_gen:
  assumes "strictly_maximal_in (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)"
  shows "strictly_maximal_in A C"
proof -
  have "\<forall>B \<in> atms_of (C \<cdot> \<sigma>). \<not> (less_atm (A \<cdot>a \<sigma>) B \<or> A \<cdot>a \<sigma> = B)"
    using assms unfolding less_eq_atm_def by -
  then have "\<forall>B \<in> atms_of C. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma> \<cdot>a \<sigma>') \<or> A \<cdot>a \<sigma> = B \<cdot>a \<sigma>)"
    unfolding subst_atms_def less_atm_iff using atms_of_subst_atms by auto
  then have "\<forall>B \<in> atms_of C. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma>' < B \<cdot>a \<sigma>') \<or> A = B)"
    using is_ground_comp_subst by fastforce
  then have "\<forall>B \<in> atms_of C. \<not> (less_atm A B \<or> A = B)"
    unfolding less_atm_iff by -
  then show ?thesis unfolding less_eq_atm_def
    by auto
qed

lemma ground_resolvent_subset:
  assumes
    gr_cas: "is_ground_cls_list CAs" and
    gr_da: "is_ground_cls DA" and
    resolve: "ord_resolve S CAs DA \<sigma> E"
  shows "E \<subseteq># (\<Union># mset CAs) + DA"
  using resolve
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Cs AAs As D)
  note DA = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4)
    and aas_len = this(5) and as_len = this(6) and cas = this(8) and mgu = this(10)
  then have "\<forall>i<n.  Cs ! i \<subseteq># CAs ! i"
    by auto
  then have cs_sub_cas: "\<Union># mset Cs \<subseteq># \<Union># mset CAs"
    using subseteq_list_Union_mset cas_len cs_len by force
  then have cs_sub_cas: "\<Union># mset Cs \<subseteq># \<Union># mset CAs"
    using subseteq_list_Union_mset cas_len cs_len by force
  then have gr_cs: "is_ground_cls_list Cs"
    using gr_cas by simp
  have d_sub_da: "D \<subseteq># DA"
    by (simp add: DA)
  then have gr_d: "is_ground_cls D"
    using gr_da is_ground_cls_mono by auto

  have "is_ground_cls (\<Union># mset Cs + D)"
    using gr_cs gr_d by auto
  then have Cs_D_\<sigma>: "(\<Union># mset Cs + D) = (\<Union># mset Cs + D) \<cdot> \<sigma>"
    by auto
  from e have "E = (\<Union># mset Cs + D)"
    using Cs_D_\<sigma> by auto
  then show ?thesis
    using cs_sub_cas d_sub_da by (auto simp add: subset_mset.add_mono)
qed

lemma ground_resolvent_ground:
  assumes "is_ground_cls_list CAs" and "is_ground_cls DA" and "ord_resolve S CAs DA \<sigma> E"
  shows "is_ground_cls E"
  by (metis (no_types) assms ground_resolvent_subset is_ground_cls_Union_mset is_ground_cls_list_def
      is_ground_cls_mono is_ground_cls_mset_def is_ground_cls_union set_mset_mset)

lemma ord_resolve_obtain_clauses:
  assumes
    resolve: "ord_resolve (S_M S M) CAs DA \<sigma> E" and
    select: "selection S" and
    grounding: "{DA} \<union> (set CAs) \<subseteq> grounding_of_clss M" and
    n: "length CAs = n"
  obtains DA'' \<eta>'' CAs'' \<eta>s'' where
    "length CAs'' = n"
    "length \<eta>s'' = n"
    "DA'' \<in> M"
    "DA'' \<cdot> \<eta>'' = DA"
    "S DA'' \<cdot> \<eta>'' = S_M S M DA"
    "\<forall>CA'' \<in> set CAs''. CA'' \<in> M" (* Could also use subseteq *)
    "CAs'' \<cdot>\<cdot>cl \<eta>s'' = CAs"
    "(map S CAs'') \<cdot>\<cdot>cl \<eta>s'' = map (S_M S M) CAs"
    "is_ground_subst \<eta>''"
    "is_ground_subst_list \<eta>s''"
  using resolve
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n_twin Cs AAs As D)
  note DA = this(1) and e = this(2) and cas = this(8) and mgu = this(10)
  from ord_resolve have "n_twin = n"
    using n by auto
  then have nz: "n \<noteq> 0" and cs_len: "length Cs = n" and aas_len: "length AAs = n" and as_len: "length As = n"
    using ord_resolve by force+

  note n = \<open>n \<noteq> 0\<close> \<open>length CAs = n\<close> \<open>length Cs = n\<close> \<open>length AAs = n\<close> \<open>length As = n\<close>

  interpret S: selection S by (rule select)

  -- \<open>Obtain FO side premises\<close>
  have "\<forall>CA \<in> set CAs. \<exists>CA'' \<eta>c''. CA'' \<in> M \<and> CA'' \<cdot> \<eta>c'' = CA \<and> S CA'' \<cdot> \<eta>c'' = S_M S M CA \<and> is_ground_subst \<eta>c''"
    using grounding S_M_grounding_of_clss select by (metis le_supE subset_iff)
  then have "\<forall>i < n. \<exists>CA'' \<eta>c''. CA'' \<in> M \<and> CA'' \<cdot> \<eta>c'' = (CAs ! i) \<and> S CA'' \<cdot> \<eta>c'' = S_M S M (CAs ! i) \<and> is_ground_subst \<eta>c''"
    using n by force
  then obtain \<eta>s''f CAs''f where f_p:
    "\<forall>i < n. CAs''f i \<in> M"
    "\<forall>i < n. (CAs''f i) \<cdot> (\<eta>s''f i) = (CAs ! i)"
    "\<forall>i < n. S (CAs''f i)  \<cdot> (\<eta>s''f i) = S_M S M (CAs ! i)"
    "\<forall>i < n. is_ground_subst (\<eta>s''f i)"
    using n by metis

  define \<eta>s'' where "\<eta>s'' = map \<eta>s''f [0 ..<n]"
  define CAs'' where "CAs'' = map CAs''f [0 ..<n]"

  have "length \<eta>s'' = n" "length CAs'' = n"
    unfolding \<eta>s''_def CAs''_def by auto
  note n = \<open>length \<eta>s'' = n\<close> \<open>length CAs'' = n\<close> n

  -- \<open>The properties we need of the FO side premises\<close>
  have CAs''_in_M: "\<forall>CA'' \<in> set CAs''. CA'' \<in> M"
    unfolding CAs''_def using f_p(1) by auto
  have CAs''_to_CAs: "CAs'' \<cdot>\<cdot>cl \<eta>s'' = CAs"
    unfolding CAs''_def \<eta>s''_def using f_p(2)  by (auto simp: n intro: nth_equalityI)
  have SCAs''_to_SMCAs: "(map S CAs'') \<cdot>\<cdot>cl \<eta>s'' = map (S_M S M) CAs"
    unfolding CAs''_def \<eta>s''_def using f_p(3) n by (force intro: nth_equalityI)
  have sub_ground: "\<forall>\<eta>c'' \<in> set \<eta>s''. is_ground_subst \<eta>c''"
    unfolding \<eta>s''_def using f_p n by auto
  then have "is_ground_subst_list \<eta>s''"
    using n unfolding is_ground_subst_list_def by auto

  -- \<open>Obtain FO main premise\<close>
  have "\<exists>DA'' \<eta>''. DA'' \<in> M \<and> DA = DA'' \<cdot> \<eta>'' \<and> S DA'' \<cdot> \<eta>'' = S_M S M DA \<and> is_ground_subst \<eta>''"
    using grounding S_M_grounding_of_clss select by (metis le_supE singletonI subsetCE)
  then obtain DA'' \<eta>'' where DA''_\<eta>''_p: "DA'' \<in> M \<and> DA = DA'' \<cdot> \<eta>'' \<and> S DA'' \<cdot> \<eta>'' = S_M S M DA \<and> is_ground_subst \<eta>''"
    by auto
  -- \<open>The properties we need of the FO main premise\<close>
  have DA''_in_M: "DA'' \<in> M"
    using DA''_\<eta>''_p by auto
  have DA''_to_DA: "DA'' \<cdot> \<eta>'' = DA"
    using DA''_\<eta>''_p by auto
  have SDA''_to_SMDA: "S DA'' \<cdot> \<eta>'' = S_M S M DA"
    using DA''_\<eta>''_p by auto
  have "is_ground_subst \<eta>''"
    using DA''_\<eta>''_p by auto
  show ?thesis
    using that[OF n(2) n(1) DA''_in_M  DA''_to_DA SDA''_to_SMDA CAs''_in_M CAs''_to_CAs SCAs''_to_SMCAs \<open>is_ground_subst \<eta>''\<close> \<open>is_ground_subst_list \<eta>s''\<close>]
      by auto
qed

lemma ord_resolve_rename_lifting:
  fixes CAs
  assumes resolve: "ord_resolve (S_M S M) CAs DA \<sigma> E"
    and select: "selection S"
    and selection_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>"
    and grounding: "{DA} \<union> (set CAs) \<subseteq> grounding_of_clss M"
  obtains \<eta>s \<eta> \<eta>2 CAs'' DA'' E'' \<tau> where
    "is_ground_subst \<eta>"
    "is_ground_subst_list \<eta>s"
    "is_ground_subst \<eta>2"
    "ord_resolve_rename S CAs'' DA'' \<tau> E''"
    "CAs'' \<cdot>\<cdot>cl \<eta>s = CAs" "DA'' \<cdot> \<eta> = DA" "E'' \<cdot> \<eta>2 = E" (* In the previous proofs I have CAs and DA on lfs of equality... *)
    "{DA''} \<union> set CAs'' \<subseteq> M"
  using resolve
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Cs AAs As D)
  note DA = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4) and 
    aas_len = this(5) and as_len = this(6) and nz = this(7) and cas = this(8) and 
    aas_not_empt = this(9) and mgu = this(10) and eligibility = this(11) and str_max = this(12) and
    sel_empt = this(13)

  have selection_renaming_list_invariant: "\<And>\<rho>s Cs. length \<rho>s = length Cs \<Longrightarrow> is_renaming_list \<rho>s \<Longrightarrow> map S (Cs \<cdot>\<cdot>cl \<rho>s) = (map S Cs) \<cdot>\<cdot>cl \<rho>s"
    using selection_renaming_invariant unfolding is_renaming_list_def by (auto intro: nth_equalityI)

  note n = \<open>n \<noteq> 0\<close> \<open>length CAs = n\<close> \<open>length Cs = n\<close> \<open>length AAs = n\<close> \<open>length As = n\<close>

  interpret S: selection S by (rule select)

  obtain DA'' \<eta>'' CAs'' \<eta>s'' where as'':
    "length CAs'' = n"
    "length \<eta>s'' = n"

    "DA'' \<in> M"
    "DA'' \<cdot> \<eta>'' = DA"
    "S DA'' \<cdot> \<eta>'' = S_M S M DA"

    "\<forall>CA'' \<in> set CAs''. CA'' \<in> M" (* Could also use subseteq *)
    "CAs'' \<cdot>\<cdot>cl \<eta>s'' = CAs"
    "(map S CAs'') \<cdot>\<cdot>cl \<eta>s'' = map (S_M S M) CAs"

    "is_ground_subst \<eta>''"
    "is_ground_subst_list \<eta>s''"
    using resolve grounding select ord_resolve_obtain_clauses[of S M CAs DA] n
      by metis

  note n = \<open>length CAs'' = n\<close> \<open>length \<eta>s'' = n\<close> n

  have "length (renamings_apart (DA''#CAs'')) = Suc n"
    using n renamings_apart_p by auto

  note n = \<open>length (renamings_apart (DA''#CAs'')) = Suc n\<close> n

  define DA' where "DA' = DA'' \<cdot> hd (renamings_apart (DA''#CAs''))"
  define CAs' where "CAs' = CAs'' \<cdot>\<cdot>cl tl (renamings_apart (DA''#CAs''))"
  define \<eta>' where "\<eta>' = (inv_ren (hd (renamings_apart (DA''#CAs'')))) \<odot> \<eta>''"
  define \<eta>s' where "\<eta>s' = (map inv_ren (tl (renamings_apart (DA''#CAs'')))) \<odot>s \<eta>s''"

  have renames_DA'': "is_renaming (hd (renamings_apart (DA''#CAs'')))"
    using renamings_apart_p[of "DA'' # CAs''"]
    by (metis length_greater_0_conv list.exhaust_sel list.set_intros(1) list.simps(3))

  have renames_CAs'': "is_renaming_list (tl (renamings_apart (DA''#CAs'')))"
    using renamings_apart_p[of "DA'' # CAs''"]
    by (metis is_renaming_list_def length_greater_0_conv list.set_sel(2) list.simps(3))

  have "length CAs' = n"
    using as''(1) n unfolding CAs'_def by auto
  have "length \<eta>s' = n"
    using as''(2) n unfolding \<eta>s'_def by auto
  note n = \<open>length CAs' = n\<close> \<open>length \<eta>s' = n\<close> n

  have DA'_DA: "DA' \<cdot> \<eta>' = DA"
    using as''(4) unfolding \<eta>'_def DA'_def using renames_DA'' by auto
  have "S DA' \<cdot> \<eta>' = S_M S M DA"
    using as''(5) unfolding \<eta>'_def DA'_def using renames_DA'' selection_renaming_invariant by auto
  have CAs'_CAs: "CAs' \<cdot>\<cdot>cl \<eta>s' = CAs"
    using as''(7) unfolding CAs'_def \<eta>s'_def using n(3) renamings_apart_p renames_CAs'' by auto
  have "(map S CAs') \<cdot>\<cdot>cl \<eta>s' = map (S_M S M) CAs"
    unfolding CAs'_def \<eta>s'_def using as''(8) n(3,4) renames_CAs'' selection_renaming_list_invariant by auto
  have vd: "var_disjoint (DA' # CAs')"
    unfolding DA'_def CAs'_def using renamings_apart_p[of "DA'' # CAs''"]
    by (metis length_greater_0_conv list.exhaust_sel n(3) substitution.subst_cls_lists_Cons substitution_axioms zero_less_Suc)

  -- \<open>Introduce ground substitution\<close>
  from vd DA'_DA CAs'_CAs have "\<exists>\<eta>. \<forall>i<Suc n. \<forall>S. S \<subseteq># (DA' # CAs') ! i \<longrightarrow> S \<cdot> (\<eta>'#\<eta>s') ! i = S \<cdot> \<eta>"
    unfolding var_disjoint_def using n by auto
  then obtain \<eta> where \<eta>_p: "\<forall>i<Suc n. \<forall>S. S \<subseteq># (DA' # CAs') ! i \<longrightarrow> S \<cdot> (\<eta>'#\<eta>s') ! i = S \<cdot> \<eta>"
    by auto

  have DA'_DA: "DA' \<cdot> \<eta> = DA"
    using DA'_DA \<eta>_p by auto
  have "S DA' \<cdot> \<eta> = S_M S M DA"
    using \<open>S DA' \<cdot> \<eta>' = S_M S M DA\<close> \<eta>_p S.S_selects_subseteq by auto

  from \<eta>_p have "\<forall>i < n. (CAs' ! i) \<cdot> (\<eta>s' ! i) = (CAs'! i) \<cdot> \<eta>"
    using n by auto
  then have "CAs' \<cdot>\<cdot>cl \<eta>s' = CAs' \<cdot>cl \<eta>"
    using n by (auto intro: nth_equalityI)
  then have CAs'_\<eta>_fo_CAs: "CAs' \<cdot>cl \<eta> = CAs"
    using CAs'_CAs \<eta>_p n by auto

  from \<eta>_p have "\<forall>i<n. (S (CAs' ! i)) \<cdot> \<eta>s' ! i = (S (CAs' ! i)) \<cdot> \<eta>"
    using S.S_selects_subseteq n by auto
  then have "(map S CAs') \<cdot>\<cdot>cl \<eta>s' = (map S CAs') \<cdot>cl \<eta>"
    using n by (auto intro: nth_equalityI)
  then have SCAs'_\<eta>_fo_SMCAs: "(map S CAs') \<cdot>cl \<eta> = map (S_M S M) CAs"
    using \<open>(map S CAs') \<cdot>\<cdot>cl \<eta>s' = map (S_M S M) CAs\<close> by auto

  -- \<open>Split main premise in to D' and A's\<close>
  obtain As' D' where as':
    "length As' = n"

    "As' \<cdot>al \<eta> = As"
    "D' \<cdot> \<eta> = D"
    "DA' = D' + (negs (mset As'))"
    "S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As') = S DA'"
  proof -
    {
      assume a: "S_M S M (D + negs (mset As)) = {#} \<and> length As = (Suc 0) \<and> maximal_in (As ! 0 \<cdot>a \<sigma>) ((D + negs (mset As)) \<cdot> \<sigma>)"
      then have "mset As = {# As ! 0 #}"
        by (auto intro: nth_equalityI)
      then have "negs (mset As) = {# Neg (As ! 0) #}"
        by (simp add: \<open>mset As = {# As ! 0 #}\<close>)
      then have "DA = D + {#Neg (As ! 0)#}"
        using DA by auto
      then obtain L where "L \<in># DA' \<and> L \<cdot>l \<eta> = Neg (As ! 0)"
        using \<open>DA' \<cdot> \<eta> = DA\<close> by (metis Melem_subst_cls mset_subset_eq_add_right single_subset_iff)
      then have "Neg (atm_of L) \<in># DA' \<and> Neg (atm_of L) \<cdot>l \<eta> = Neg (As ! 0)"
        by (metis Neg_atm_of_iff literal.sel(2) subst_lit_is_pos)
      then have "[atm_of L] \<cdot>al \<eta> = As \<and> negs (mset [atm_of L]) \<subseteq># DA'"
        using \<open>mset As = {#As ! 0#}\<close> subst_lit_def by auto
      then have "\<exists>As'. As' \<cdot>al \<eta> = As \<and> negs (mset As') \<subseteq># DA' \<and> (S_M S M (D + negs (mset As)) \<noteq> {#} \<longrightarrow> negs (mset As') = S DA')"
        using a by blast
    }
    moreover
    {
      assume "S_M S M (D + negs (mset As)) = negs (mset As)"
      then have "negs (mset As) = S DA' \<cdot> \<eta>"
        using DA \<open>S DA' \<cdot> \<eta> = S_M S M DA\<close> by auto
      then have "\<exists>As'. negs (mset As') = S DA' \<and> As' \<cdot>al \<eta> = As"
        using instance_list[of As "S DA'" \<eta>] S.S_selects_neg_lits by auto
      then have "\<exists>As'. As' \<cdot>al \<eta> = As \<and> negs (mset As') \<subseteq># DA'  \<and> (S_M S M (D + negs (mset As)) \<noteq> {#} \<longrightarrow> negs (mset As') = S DA')"
        using S.S_selects_subseteq by auto
    }
    ultimately have "\<exists>As'. As' \<cdot>al \<eta> = As \<and> (negs (mset As')) \<subseteq># DA' \<and> (S_M S M (D + negs (mset As)) \<noteq> {#} \<longrightarrow> negs (mset As') = S DA')"
      using eligibility unfolding eligible.simps[simplified] by auto
    
    then obtain As' where As'_p: "As' \<cdot>al \<eta> = As \<and> (negs (mset As')) \<subseteq># DA' \<and> (S_M S M (D + negs (mset As)) \<noteq> {#} \<longrightarrow> negs (mset As') = S DA')"
      by blast
    then have "length As' = n"
      using as_len by auto
    note n = n \<open>length As' = n\<close>

    have "As' \<cdot>al \<eta> = As"
      using As'_p by auto

    define D' where "D' = DA' - (negs (mset As'))"
    then have DA'_u: "DA' = D' +  (negs (mset As'))"
      using As'_p by auto

    have "D' \<cdot> \<eta> = D"
      using \<open>DA' \<cdot> \<eta> = DA\<close> DA DA'_u As'_p by auto

    have "S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As') = S DA'"
      using As'_p by blast

    show ?thesis
      using that \<open>As' \<cdot>al \<eta> = As\<close> \<open>D' \<cdot> \<eta> = D\<close> \<open>DA' = D' +  (negs (mset As'))\<close>
      \<open>S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As') = S DA'\<close> \<open>length As' = n\<close>
      by metis
  qed

  note n = n \<open>length As' = n\<close>

  -- \<open>Split side premise in to C's and A's\<close>
  obtain AAs' Cs'  where AAs'_Cs'_p:
    "length AAs' = n"
    "length Cs' = n"

    "AAs' \<cdot>aml \<eta> = AAs"
    "Cs' \<cdot>cl \<eta> = Cs"
    "\<forall>i < n. CAs' ! i = Cs' ! i + poss (AAs' ! i)" (* Write in list notation? *)
  proof -
    have "\<forall>i<n. \<exists>AA'. AA' \<cdot>am \<eta> = AAs ! i \<and> (poss AA') \<subseteq># CAs' ! i"
    proof (rule, rule)
      fix i
      assume "i < n"
      have "CAs' ! i \<cdot> \<eta> = CAs ! i"
        using \<open>i < n\<close> \<open>CAs' \<cdot>cl \<eta> = CAs\<close> n by force
      moreover
      have "poss (AAs ! i) \<subseteq># CAs !i"
        using \<open>i<n\<close> cas by auto
      ultimately
      obtain poss_AA' where nn: "poss_AA' \<cdot> \<eta> = poss (AAs ! i) \<and> poss_AA' \<subseteq># CAs' ! i"
        using cas image_mset_of_subset unfolding subst_cls_def by metis
      then have l: "\<forall>L \<in># poss_AA'. is_pos L"
        unfolding subst_cls_def by (metis Melem_subst_cls imageE literal.disc(1) literal.map_disc_iff set_image_mset subst_cls_def subst_lit_def)
      define AA' where "AA' = image_mset atm_of poss_AA'"
      have na: "poss AA' = poss_AA'"
        using l unfolding AA'_def by auto
      then have "AA' \<cdot>am \<eta> = AAs ! i"
        using nn by (metis literal.inject(1) multiset.inj_map_strong subst_cls_poss)
      moreover
      have "poss AA' \<subseteq># CAs' ! i"
        using na nn by auto
      ultimately
      show "\<exists>AA'. AA' \<cdot>am \<eta> = AAs ! i \<and> poss AA' \<subseteq># CAs' ! i"
        by blast
    qed
    then obtain AAs'f where AAs'f_p: "\<forall>i<n. AAs'f i \<cdot>am \<eta> = AAs ! i \<and> (poss (AAs'f i)) \<subseteq># CAs' ! i"
      by metis

    define AAs' where "AAs' = map AAs'f [0 ..<n]"

    then have "length AAs' = n"
      by auto
    note n = n \<open>length AAs' = n\<close>

    from AAs'_def have "\<forall>i<n. AAs' ! i \<cdot>am \<eta> = AAs ! i"
      using AAs'f_p by auto
    then have AAs'_AAs: "AAs' \<cdot>aml \<eta> = AAs"
      using n unfolding subst_atm_mset_list_def by (auto intro: nth_equalityI) (* unfolding should not be necessary *)

    from AAs'_def have AAs'_in_CAs': "\<forall>i<n. (poss (AAs' ! i)) \<subseteq># CAs' ! i"
      using AAs'f_p by auto

    define Cs' where "Cs' = map2 (op -) CAs' (map poss AAs')"

    have "length Cs' = n"
      using Cs'_def n by auto
    note n = n \<open>length Cs' = n\<close>

    have "\<forall>i < n. CAs' ! i = Cs' ! i + poss (AAs' ! i)"
      using AAs'_in_CAs' Cs'_def n by auto
    then have "Cs' \<cdot>cl \<eta> = Cs"
      using \<open>CAs' \<cdot>cl \<eta> = CAs\<close> AAs'_AAs cas n by (auto intro: nth_equalityI)

    show ?thesis
      using that \<open>AAs' \<cdot>aml \<eta> = AAs\<close> \<open>Cs' \<cdot>cl \<eta> = Cs\<close> \<open>\<forall>i < n. CAs' ! i = Cs' ! i + poss (AAs' ! i)\<close>
        \<open>length AAs' = n\<close> \<open>length Cs' = n\<close>
      by blast
  qed

  note n = n \<open>length AAs' = n\<close> \<open>length Cs' = n\<close>

  -- \<open>Obtain MGU and subsitution\<close>
  obtain \<tau>  \<phi> where \<tau>\<phi>:
    "Some \<tau> = mgu (set_mset ` set (map2 add_mset As' AAs'))"
    "\<tau> \<odot> \<phi> = \<eta> \<odot> \<sigma>"
  proof -
    have "Some \<sigma> = mgu (set_mset ` set (map2 add_mset As AAs))"
      using mgu by -
    then have uu: "is_unifiers \<sigma> (set_mset ` set (map2 add_mset (As' \<cdot>al \<eta>) (AAs' \<cdot>aml \<eta>)))"
      using mgu_sound is_mgu_def unfolding \<open>AAs' \<cdot>aml \<eta> = AAs\<close> using as'(2) by auto
    have \<eta>\<sigma>uni: "is_unifiers (\<eta> \<odot> \<sigma>) (set_mset ` set (map2 add_mset As' AAs'))"
    proof -
      have eq: "(set_mset ` set (map2 add_mset As' AAs' \<cdot>aml \<eta>)) = (set_mset ` set (map2 add_mset As' AAs') \<cdot>ass \<eta>)"
        unfolding subst_atmss_def subst_atm_mset_list_def using subst_atm_mset_def subst_atms_def
        by (simp add: image_image subst_atm_mset_def subst_atms_def)
      have "is_unifiers \<sigma> (set_mset ` set ((map2 add_mset As' AAs') \<cdot>aml \<eta>))"
        using uu n map2_add_mset_map by auto
      then have "is_unifiers \<sigma> (set_mset ` set ((map2 add_mset As' AAs')) \<cdot>ass \<eta>)"
        using eq by auto
      then show ?thesis
        using is_unifiers_comp by auto
    qed
    then obtain \<tau> where
      \<tau>_p: "Some \<tau> = mgu (set_mset ` set (map2 add_mset As' AAs'))"
      using mgu_complete
      by (metis (mono_tags, hide_lams) List.finite_set finite_imageI finite_set_mset image_iff)
    moreover then obtain \<phi> where \<phi>_p: "\<tau> \<odot> \<phi> = \<eta> \<odot> \<sigma>"
      by (metis (mono_tags, hide_lams) finite_set \<eta>\<sigma>uni finite_imageI finite_set_mset image_iff
          mgu_sound set_mset_mset substitution_ops.is_mgu_def) (* should be simpler *)
    ultimately show ?thesis using that
      by auto
  qed

  -- \<open>Lifting eligibility\<close>
  have eligibility: "eligible S \<tau> As' (D' + negs (mset As'))"
  proof -
    have "eligible (S_M S M) \<sigma> As (D + negs (mset As))"
      using eligibility unfolding eligible.simps[simplified] by -
    then have "S_M S M (D + negs (mset As)) = negs (mset As) \<or> S_M S M (D + negs (mset As)) = {#} \<and>
      length As = 1 \<and> maximal_in (As ! 0 \<cdot>a \<sigma>) ((D + negs (mset As)) \<cdot> \<sigma>)"
      unfolding eligible.simps[simplified] by auto
    then show "eligible S \<tau> As' (D' + negs (mset As'))"
    proof
      assume as: "S_M S M (D + negs (mset As)) = negs (mset As)"
      then have "S_M S M (D + negs (mset As)) \<noteq> {#}"
        using n by force
      then have "negs (mset As') = S DA'"
        using as'(5) by auto
      then have "S (D'  + negs (mset As')) = negs (mset As')"
        using as' by auto
      then show "eligible S \<tau> As' (D' + negs (mset As'))"
        unfolding eligible.simps[simplified]  by auto
    next
      assume asm: "S_M S M (D + negs (mset As)) = {#} \<and> length As = 1 \<and>
        maximal_in (As ! 0 \<cdot>a \<sigma>) ((D + negs (mset As)) \<cdot> \<sigma>)"
      from asm have "S_M S M (D + negs (mset As)) = {#}"
        by auto
      then have "S (D' + negs (mset As')) = {#}"
        using \<open>D' \<cdot> \<eta> = D\<close>[symmetric] \<open>As' \<cdot>al \<eta> = As\<close>[symmetric] \<open>S (DA') \<cdot> \<eta> = S_M S M (DA)\<close>
          DA as' subst_cls_empty_iff by metis
      moreover from asm have l: "length As = 1"
        by auto
      then have l': "length As' = 1"
        using \<open>As' \<cdot>al \<eta> = As\<close>[symmetric] by auto
      moreover from asm have "maximal_in (As ! 0 \<cdot>a \<sigma>) ((D + negs (mset As)) \<cdot> \<sigma>)"
        by auto
      then have "maximal_in (As' ! 0 \<cdot>a (\<eta> \<odot> \<sigma>)) ((D' + negs (mset As')) \<cdot> (\<eta> \<odot> \<sigma>))"
        unfolding \<open>As' \<cdot>al \<eta> = As\<close>[symmetric] \<open>D' \<cdot> \<eta> = D\<close>[symmetric] using l' by auto
      then have "maximal_in (As' ! 0 \<cdot>a (\<tau> \<odot> \<phi>)) ((D' + negs (mset As')) \<cdot> (\<tau> \<odot> \<phi>))"
        unfolding \<open>As' \<cdot>al \<eta> = As\<close>[symmetric] \<open>D' \<cdot> \<eta> = D\<close>[symmetric] using \<tau>\<phi> by auto
      then have "maximal_in (As' ! 0 \<cdot>a \<tau> \<cdot>a \<phi>) ((D' + negs (mset As')) \<cdot> \<tau> \<cdot> \<phi>)"
        by auto
      then have "maximal_in (As' ! 0 \<cdot>a \<tau>) ((D' + negs (mset As')) \<cdot> \<tau>)"
        using maximal_in_gen by blast
      ultimately show "eligible S \<tau> As' (D' + negs (mset As'))"
        unfolding eligible.simps[simplified] by auto
    qed
  qed

  -- \<open>Lifting maximality\<close>
  have maximality: "\<forall>i<n. strictly_maximal_in (As' ! i \<cdot>a \<tau>) (Cs' ! i \<cdot> \<tau>)"
    (* Reformulate in list notation? *)
  proof -
    from str_max have "\<forall>i<n. strictly_maximal_in (As ! i \<cdot>a \<sigma>) (Cs ! i \<cdot> \<sigma>)"
      by -
    then have "\<forall>i<n. strictly_maximal_in ((As' \<cdot>al \<eta>) ! i \<cdot>a \<sigma>) ((Cs' \<cdot>cl \<eta>) ! i \<cdot> \<sigma>)"
      using \<open>As' \<cdot>al \<eta> = As\<close>  \<open>Cs' \<cdot>cl \<eta> = Cs\<close> by simp
    then have "\<forall>i<n. strictly_maximal_in ((As' ! i) \<cdot>a (\<eta> \<odot> \<sigma>)) ((Cs' ! i) \<cdot> (\<eta> \<odot> \<sigma>))"
      using n by auto
    then have "\<forall>i<n. strictly_maximal_in ((As' ! i) \<cdot>a (\<tau> \<odot> \<phi>)) ((Cs' ! i) \<cdot> (\<tau> \<odot> \<phi>))"
      using \<tau>\<phi> by auto
    then have "\<forall>i<n. strictly_maximal_in ((As' ! i \<cdot>a \<tau>) \<cdot>a \<phi>) ((Cs' ! i \<cdot> \<tau>) \<cdot> \<phi>)"
      by auto
    then show e: "\<forall>i<n. strictly_maximal_in (As' ! i \<cdot>a \<tau>) (Cs' ! i \<cdot> \<tau>)"
      using strictly_maximal_in_gen \<tau>\<phi> by blast
  qed

  -- \<open>Lifting nothing being selected\<close>
  have nothing_selected: "\<forall>i < n. S (CAs' ! i) = {#}"
  proof -
    have "\<forall>i < n. (map S CAs' \<cdot>cl \<eta>) ! i = (map (S_M S M) CAs) ! i"
      by (simp add: \<open>map S CAs' \<cdot>cl \<eta> = map (S_M S M) CAs\<close>)
    then have "\<forall>i < n. S (CAs' ! i) \<cdot> \<eta> = S_M S M (CAs ! i)"
      using n by auto
    then have "\<forall>i < n. S (CAs' ! i)  \<cdot> \<eta> = {#}"
      using sel_empt \<open>\<forall>i < n.  S (CAs' ! i) \<cdot> \<eta> = S_M S M (CAs ! i)\<close> by auto
    then show "\<forall>i < n. S (CAs' ! i) = {#}"
      using subst_cls_empty_iff by blast
  qed

  -- \<open>Lifting AAs's being non-empty\<close>
  have "\<forall>i<n. AAs' ! i \<noteq> {#}"
    using n aas_not_empt \<open>AAs' \<cdot>aml \<eta> = AAs\<close> by auto

 -- \<open>Resolve the lifted clauses\<close>
  define E' where "E' = ((\<Union># (mset Cs')) + D') \<cdot> \<tau>"

  have res_e: "ord_resolve S CAs' DA' \<tau> E'"
    using ord_resolve.intros[of CAs' n Cs' AAs' As' \<tau> S D',
      OF _ _ _ _ _ _ \<open>\<forall>i<n. AAs' ! i \<noteq> {#}\<close> \<tau>\<phi>(1) eligibility
        \<open>\<forall>i<n. strictly_maximal_in (As' ! i \<cdot>a \<tau>) (Cs' ! i \<cdot> \<tau>)\<close> \<open>\<forall>i<n. S (CAs' ! i) = {#}\<close>]
    unfolding E'_def using as' n AAs'_Cs'_p by blast

  -- \<open>Prove resolvent instantiates to ground resolvent\<close>
  have e'\<phi>e: "E' \<cdot> \<phi> = E"
  proof -
    have "E' \<cdot> \<phi> = ((\<Union># (mset Cs')) + D') \<cdot> (\<tau> \<odot> \<phi>)"
      unfolding E'_def by auto
    also have "... = ((\<Union># (mset Cs')) + D') \<cdot> (\<eta> \<odot> \<sigma>)"
      using \<tau>\<phi> by auto
    also have "... = ((\<Union># (mset (Cs' \<cdot>cl \<eta>))) + (D' \<cdot> \<eta>)) \<cdot> \<sigma>"
      by simp
    also have "... = ((\<Union># (mset Cs)) + D) \<cdot> \<sigma>"
      using \<open>Cs' \<cdot>cl \<eta> = Cs\<close> \<open>D' \<cdot> \<eta> = D\<close> by auto
    also have "... = E"
      using e by auto
    finally show e'\<phi>e: "E' \<cdot> \<phi> = E"
      .
  qed

  -- \<open>Replace @{term \<eta>} with a true ground substitution\<close>
  obtain \<eta>2 where ground_\<eta>2: "is_ground_subst \<eta>2" "E' \<cdot> \<eta>2 = E"
  proof -
    have "is_ground_cls_list CAs" "is_ground_cls DA"
      using grounding grounding_ground unfolding is_ground_cls_list_def by auto
    then have "is_ground_cls E"
      using resolve ground_resolvent_ground by auto
    then obtain \<eta>2 where ground_\<eta>2: "is_ground_subst \<eta>2" "E' \<cdot> \<eta>2 = E"
      using e'\<phi>e make_single_ground_subst by blast
    then show ?thesis
      using that by auto
  qed

  have res_r_e: "ord_resolve_rename S CAs'' DA'' \<tau> E'"
    using ord_resolve_rename res_e unfolding CAs'_def DA'_def by auto

  show ?thesis
    using that[of \<eta>'' \<eta>s'' \<eta>2 CAs'' DA''] \<open>is_ground_subst \<eta>''\<close> \<open>is_ground_subst_list \<eta>s''\<close>
      \<open>is_ground_subst \<eta>2\<close> res_r_e \<open>CAs'' \<cdot>\<cdot>cl \<eta>s'' = CAs\<close> \<open>DA'' \<cdot> \<eta>'' = DA\<close> \<open>E' \<cdot> \<eta>2 = E\<close> \<open>DA'' \<in> M\<close>
      \<open>\<forall>CA \<in> set CAs''. CA \<in> M\<close>
    by blast
qed

end

end
