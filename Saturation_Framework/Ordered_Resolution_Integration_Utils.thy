(*  Title:       Ordered_Resolution_Integration_Utils
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2020
 *  Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2020 *)

section \<open>Libraries for the application of the saturation framework to Bachmair and Ganzinger's RP\<close>

theory Ordered_Resolution_Integration_Utils
  imports Ordered_Resolution_Prover.FO_Ordered_Resolution_Prover
begin

context substitution
begin

(* TODO: Starting with Isabelle2021, this will be in @{thy Abstract_Substitution}. Use that
   instead. *)
lemma subst_cls_lists_append[simp]:
  "length Cs = length \<sigma>s \<Longrightarrow> length Cs' = length \<sigma>s' \<Longrightarrow>
   (Cs @ Cs') \<cdot>\<cdot>cl (\<sigma>s @ \<sigma>s') = Cs \<cdot>\<cdot>cl \<sigma>s @ Cs' \<cdot>\<cdot>cl \<sigma>s'"
  unfolding subst_cls_lists_def by auto

(* TODO: Starting with Isabelle2021, this will be in @{thy Abstract_Substitution}. Use that
   instead. *)
lemma strictly_subsumes_irrefl: "\<not> strictly_subsumes C C"
  unfolding strictly_subsumes_def by blast

(* TODO: Starting with Isabelle2021, this will be in @{thy Abstract_Substitution}. Use that
   instead. *)
lemma strictly_subsumes_antisym: "strictly_subsumes C D \<Longrightarrow> \<not> strictly_subsumes D C"
  unfolding strictly_subsumes_def by blast

(* TODO: Starting with Isabelle2021, this will be in @{thy Abstract_Substitution}. Use that
   instead. *)
lemma strictly_subsumes_trans:
  "strictly_subsumes C D \<Longrightarrow> strictly_subsumes D E \<Longrightarrow> strictly_subsumes C E"
  unfolding strictly_subsumes_def using subsumes_trans by blast

(* TODO: Starting with Isabelle2021, this will be in @{thy Abstract_Substitution}. Use that
   instead. *)
lemma wf_strictly_subsumes: "wfP strictly_subsumes"
  using strictly_subsumes_has_minimum by (metis equals0D wfP_eq_minimal)

end

context FO_resolution_prover
begin

text \<open>This proof is based on part of the proof of
@{thm FO_Ordered_Resolution_Prover.FO_resolution_prover.RP_saturated_if_fair}.\<close>

(* TODO: Starting with Isabelle2021, this will correspond to
   "FO_Ordered_Resolution_Prover.ground_ord_resolve_imp_ord_resolve". Use that instead. *)
lemma ground_ord_resolve_imp_ord_resolve:
  assumes
    ground_da: \<open>is_ground_cls DA\<close> and
    ground_cas: \<open>is_ground_cls_list CAs\<close> and
    gr: "ground_resolution_with_selection S_G" and
    gr_res: \<open>ground_resolution_with_selection.ord_resolve S_G CAs DA AAs As E\<close>
  shows \<open>\<exists>\<sigma>. ord_resolve S_G CAs DA AAs As \<sigma> E\<close>
proof (cases rule: ground_resolution_with_selection.ord_resolve.cases[OF gr gr_res])
  case (1 CAs n Cs AAs As D)
  note cas = this(1) and da = this(2) and aas = this(3) and as = this(4) and e = this(5) and
    cas_len = this(6) and cs_len = this(7) and aas_len = this(8) and as_len = this(9) and
    nz = this(10) and casi = this(11) and aas_not_empt = this(12) and as_aas = this(13) and
    eligibility = this(14) and str_max = this(15) and sel_empt = this(16)

  have len_aas_len_as: "length AAs = length As"
    using aas_len as_len by auto

  from as_aas have "\<forall>i < n. \<forall>A \<in># add_mset (As ! i) (AAs ! i). A = As ! i"
    by simp
  then have "\<forall>i < n. card (set_mset (add_mset (As ! i) (AAs ! i))) \<le> Suc 0"
    using all_the_same by metis
  then have "\<forall>i < length AAs. card (set_mset (add_mset (As ! i) (AAs ! i))) \<le> Suc 0"
    using aas_len by auto
  then have "\<forall>AA \<in> set (map2 add_mset As AAs). card (set_mset AA) \<le> Suc 0"
    using set_map2_ex[of AAs As add_mset, OF len_aas_len_as] by auto
  then have "is_unifiers id_subst (set_mset ` set (map2 add_mset As AAs))"
    unfolding is_unifiers_def is_unifier_def by auto
  moreover have "finite (set_mset ` set (map2 add_mset As AAs))"
    by auto
  moreover have "\<forall>AA \<in> set_mset ` set (map2 add_mset As AAs). finite AA"
    by auto
  ultimately obtain \<sigma> where
    \<sigma>_p: "Some \<sigma> = mgu (set_mset ` set (map2 add_mset As AAs))"
    using mgu_complete by metis

  have ground_elig: "ground_resolution_with_selection.eligible S_G As (D + negs (mset As))"
    using eligibility by simp
  have ground_cs: "\<forall>i < n. is_ground_cls (Cs ! i)"
    using cas cas_len cs_len casi ground_cas nth_mem unfolding is_ground_cls_list_def by force
  have ground_set_as: "is_ground_atms (set As)"
    using da ground_da by (metis atms_of_negs is_ground_cls_is_ground_atms_atms_of
        is_ground_cls_union set_mset_mset)
  then have ground_mset_as: "is_ground_atm_mset (mset As)"
    unfolding is_ground_atm_mset_def is_ground_atms_def by auto
  have ground_as: "is_ground_atm_list As"
    using ground_set_as is_ground_atm_list_def is_ground_atms_def by auto
  have ground_d: "is_ground_cls D"
    using ground_da da by simp

  from as_len nz have atms:
    "atms_of D \<union> set As \<noteq> {}"
    "finite (atms_of D \<union> set As)"
    by auto
  then have "Max (atms_of D \<union> set As) \<in> atms_of D \<union> set As"
    using Max_in by metis
  then have is_ground_Max: "is_ground_atm (Max (atms_of D \<union> set As))"
    using ground_d ground_mset_as is_ground_cls_imp_is_ground_atm
    unfolding is_ground_atm_mset_def by auto

  have "maximal_wrt (Max (atms_of D \<union> set As)) (D + negs (mset As))"
    unfolding maximal_wrt_def
    by clarsimp (metis atms Max_less_iff UnCI ground_d ground_set_as infinite_growing
        is_ground_Max is_ground_atms_def is_ground_cls_imp_is_ground_atm less_atm_ground)
  moreover have
    "Max (atms_of D \<union> set As) \<cdot>a \<sigma> = Max (atms_of D \<union> set As)" and
    "D \<cdot> \<sigma> + negs (mset As \<cdot>am \<sigma>) = D + negs (mset As)"
    using ground_elig is_ground_Max ground_mset_as ground_d by auto
  ultimately have fo_elig: "eligible S_G \<sigma> As (D + negs (mset As))"
    using ground_elig unfolding ground_resolution_with_selection.eligible.simps[OF gr]
      ground_resolution_with_selection.maximal_wrt_def[OF gr] eligible.simps
    by auto

  have "\<forall>i < n. strictly_maximal_wrt (As ! i) (Cs ! i)"
    using str_max[unfolded ground_resolution_with_selection.strictly_maximal_wrt_def[OF gr]]
      ground_as[unfolded is_ground_atm_list_def] ground_cs as_len less_atm_ground
    unfolding strictly_maximal_wrt_def by clarsimp (fastforce simp: is_ground_cls_as_atms)+
  then have ll: "\<forall>i < n. strictly_maximal_wrt (As ! i \<cdot>a \<sigma>) (Cs ! i \<cdot> \<sigma>)"
    by (simp add: ground_as ground_cs as_len)

  have ground_e: "is_ground_cls E"
    using ground_d ground_cs unfolding e is_ground_cls_def
    by simp (metis cs_len in_mset_sum_list2 in_set_conv_nth)

  show ?thesis
    using cas da aas as e ground_e ord_resolve.intros[OF cas_len cs_len aas_len as_len nz casi
        aas_not_empt \<sigma>_p fo_elig ll sel_empt]
    by auto
qed

(* TODO: Starting with Isabelle2021, this will correspond to
   "FO_Ordered_Resolution.ord_resolve_rename_lifting". Use that instead. *)
lemma ord_resolve_rename_lifting_with_length:
  assumes
    sel_stable: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>" and
    res_e: "ord_resolve (S_M S M) CAs DA AAs As \<sigma> E" and
    select: "selection S" and
    grounding: "{DA} \<union> set CAs \<subseteq> grounding_of_clss M"
  obtains \<eta>s \<eta> \<eta>2 CAs0 DA0 AAs0 As0 E0 \<tau> where
    "is_ground_subst \<eta>"
    "is_ground_subst_list \<eta>s"
    "is_ground_subst \<eta>2"
    "ord_resolve_rename S CAs0 DA0 AAs0 As0 \<tau> E0"
    "CAs0 \<cdot>\<cdot>cl \<eta>s = CAs" "DA0 \<cdot> \<eta> = DA" "E0 \<cdot> \<eta>2 = E" 
    "{DA0} \<union> set CAs0 \<subseteq> M"
    "length CAs0 = length CAs"
    "length \<eta>s = length CAs"
  using res_e
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Cs D)
  note da = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4) and
    aas_len = this(5) and as_len = this(6) and nz = this(7) and cas = this(8) and
    aas_not_empt = this(9) and mgu = this(10) and eligible = this(11) and str_max = this(12) and
    sel_empt = this(13)

  have sel_ren_list_inv:
    "\<And>\<rho>s Cs. length \<rho>s = length Cs \<Longrightarrow> is_renaming_list \<rho>s \<Longrightarrow> map S (Cs \<cdot>\<cdot>cl \<rho>s) = map S Cs \<cdot>\<cdot>cl \<rho>s"
    using sel_stable unfolding is_renaming_list_def by (auto intro: nth_equalityI)

  note n = \<open>n \<noteq> 0\<close> \<open>length CAs = n\<close> \<open>length Cs = n\<close> \<open>length AAs = n\<close> \<open>length As = n\<close>

  interpret S: selection S by (rule select)

  obtain DA0 \<eta>0 CAs0 \<eta>s0 As0 AAs0 D0 Cs0 where as0:
    "length CAs0 = n"
    "length \<eta>s0 = n"
    "DA0 \<in> M"
    "DA0 \<cdot> \<eta>0 = DA"
    "S DA0 \<cdot> \<eta>0 = S_M S M DA"
    "\<forall>CA0 \<in> set CAs0. CA0 \<in> M"
    "CAs0 \<cdot>\<cdot>cl \<eta>s0 = CAs"
    "map S CAs0 \<cdot>\<cdot>cl \<eta>s0 = map (S_M S M) CAs"
    "is_ground_subst \<eta>0"
    "is_ground_subst_list \<eta>s0"
    "As0 \<cdot>al \<eta>0 = As"
    "AAs0 \<cdot>\<cdot>aml \<eta>s0 = AAs"
    "length As0 = n"
    "D0 \<cdot> \<eta>0 = D"
    "DA0 = D0 + (negs (mset As0))"
    "S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As0) = S DA0"
    "length Cs0 = n"
    "Cs0 \<cdot>\<cdot>cl \<eta>s0 = Cs"
    "\<forall>i < n. CAs0 ! i = Cs0 ! i + poss (AAs0 ! i)"
    "length AAs0 = n"
    using ord_resolve_obtain_clauses[of S M CAs DA, OF res_e select grounding n(2)
      \<open>DA = D + negs (mset As)\<close> \<open>\<forall>i<n. CAs ! i = Cs ! i + poss (AAs ! i)\<close> \<open>length Cs = n\<close>
      \<open>length AAs = n\<close>, of thesis] by blast

  note n = \<open>length CAs0 = n\<close> \<open>length \<eta>s0 = n\<close> \<open>length As0 = n\<close> \<open>length AAs0 = n\<close> \<open>length Cs0 = n\<close> n

  have "length (renamings_apart (DA0 # CAs0)) = Suc n"
    using n renamings_apart_length by auto

  note n = this n

  define \<rho> where
    "\<rho> = hd (renamings_apart (DA0 # CAs0))"
  define \<rho>s where
    "\<rho>s = tl (renamings_apart (DA0 # CAs0))"
  define DA0' where
    "DA0' = DA0 \<cdot> \<rho>"
  define D0' where
    "D0' = D0 \<cdot> \<rho>"
  define As0' where
    "As0' = As0 \<cdot>al \<rho>"
  define CAs0' where
    "CAs0' = CAs0 \<cdot>\<cdot>cl \<rho>s"
  define Cs0' where
    "Cs0' = Cs0 \<cdot>\<cdot>cl \<rho>s"
  define AAs0' where
    "AAs0' = AAs0 \<cdot>\<cdot>aml \<rho>s"
  define \<eta>0' where
    "\<eta>0' = inv_renaming \<rho> \<odot> \<eta>0"
  define \<eta>s0' where
    "\<eta>s0' = map inv_renaming \<rho>s \<odot>s \<eta>s0"

  have renames_DA0: "is_renaming \<rho>"
    using renamings_apart_length renamings_apart_renaming unfolding \<rho>_def
    by (metis length_greater_0_conv list.exhaust_sel list.set_intros(1) list.simps(3))

  have renames_CAs0: "is_renaming_list \<rho>s"
    using renamings_apart_length renamings_apart_renaming unfolding \<rho>s_def
    by (metis is_renaming_list_def length_greater_0_conv list.set_sel(2) list.simps(3))

  have "length \<rho>s = n"
    unfolding \<rho>s_def using n by auto
  note n = n \<open>length \<rho>s = n\<close>
  have "length As0' = n"
    unfolding As0'_def using n by auto
  have "length CAs0' = n"
    using as0(1) n unfolding CAs0'_def by auto
  have "length Cs0' = n"
    unfolding Cs0'_def using n by auto
  have "length AAs0' = n"
    unfolding AAs0'_def using n by auto
  have "length \<eta>s0' = n"
    using as0(2) n unfolding \<eta>s0'_def by auto
  note n = \<open>length CAs0' = n\<close> \<open>length \<eta>s0' = n\<close> \<open>length As0' = n\<close> \<open>length AAs0' = n\<close> \<open>length Cs0' = n\<close> n

  have DA0'_DA: "DA0' \<cdot> \<eta>0' = DA"
    using as0(4) unfolding \<eta>0'_def DA0'_def using renames_DA0 by simp
  have D0'_D: "D0' \<cdot> \<eta>0' = D"
    using as0(14) unfolding \<eta>0'_def D0'_def using renames_DA0 by simp
  have As0'_As: "As0' \<cdot>al \<eta>0' = As"
    using as0(11) unfolding \<eta>0'_def As0'_def using renames_DA0 by auto
  have "S DA0' \<cdot> \<eta>0' = S_M S M DA"
    using as0(5) unfolding \<eta>0'_def DA0'_def using renames_DA0 sel_stable by auto
  have CAs0'_CAs: "CAs0' \<cdot>\<cdot>cl \<eta>s0' = CAs"
    using as0(7) unfolding CAs0'_def \<eta>s0'_def using renames_CAs0 n by auto
  have Cs0'_Cs: "Cs0' \<cdot>\<cdot>cl \<eta>s0' = Cs"
    using as0(18) unfolding Cs0'_def \<eta>s0'_def using renames_CAs0 n by auto
  have AAs0'_AAs: "AAs0' \<cdot>\<cdot>aml \<eta>s0' = AAs"
    using as0(12) unfolding \<eta>s0'_def AAs0'_def using renames_CAs0 using n by auto
  have "map S CAs0' \<cdot>\<cdot>cl \<eta>s0' = map (S_M S M) CAs"
    unfolding CAs0'_def \<eta>s0'_def using as0(8) n renames_CAs0 sel_ren_list_inv by auto

  have DA0'_split: "DA0' = D0' + negs (mset As0')"
    using as0(15) DA0'_def D0'_def As0'_def by auto
  then have D0'_subset_DA0': "D0' \<subseteq># DA0'"
    by auto
  from DA0'_split have negs_As0'_subset_DA0': "negs (mset As0') \<subseteq># DA0'"
    by auto

  have CAs0'_split: "\<forall>i<n. CAs0' ! i = Cs0' ! i + poss (AAs0' ! i)"
    using as0(19) CAs0'_def Cs0'_def AAs0'_def n by auto
  then have "\<forall>i<n. Cs0' ! i \<subseteq># CAs0' ! i"
    by auto
  from CAs0'_split have poss_AAs0'_subset_CAs0': "\<forall>i<n. poss (AAs0' ! i) \<subseteq># CAs0' ! i"
    by auto
  then have AAs0'_in_atms_of_CAs0': "\<forall>i < n. \<forall>A\<in>#AAs0' ! i. A \<in> atms_of (CAs0' ! i)"
    by (auto simp add: atm_iff_pos_or_neg_lit)

  have as0':
    "S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As0') = S DA0'"
  proof -
    assume a: "S_M S M (D + negs (mset As)) \<noteq> {#}"
    then have "negs (mset As0) \<cdot> \<rho> = S DA0 \<cdot> \<rho>"
      using as0(16) unfolding \<rho>_def by metis
    then show "negs (mset As0') = S DA0'"
      using  As0'_def DA0'_def using sel_stable[of \<rho> DA0] renames_DA0 by auto
  qed

  have vd: "var_disjoint (DA0' # CAs0')"
    unfolding DA0'_def CAs0'_def using renamings_apart_var_disjoint
    unfolding \<rho>_def \<rho>s_def
    by (metis length_greater_0_conv list.exhaust_sel n(6) substitution.subst_cls_lists_Cons
        substitution_axioms zero_less_Suc)

  \<comment> \<open>Introduce ground substitution\<close>
  from vd DA0'_DA CAs0'_CAs have "\<exists>\<eta>. \<forall>i < Suc n. \<forall>S. S \<subseteq># (DA0' # CAs0') ! i \<longrightarrow> S \<cdot> (\<eta>0'#\<eta>s0') ! i = S \<cdot> \<eta>"
    unfolding var_disjoint_def using n by auto
  then obtain \<eta> where \<eta>_p: "\<forall>i < Suc n. \<forall>S. S \<subseteq># (DA0' # CAs0') ! i \<longrightarrow> S \<cdot> (\<eta>0'#\<eta>s0') ! i = S \<cdot> \<eta>"
    by auto
  have \<eta>_p_lit: "\<forall>i < Suc n. \<forall>L. L \<in># (DA0' # CAs0') ! i \<longrightarrow> L \<cdot>l (\<eta>0'#\<eta>s0') ! i = L \<cdot>l \<eta>"
  proof (rule, rule, rule, rule)
    fix i :: "nat" and L :: "'a literal"
    assume a:
      "i < Suc n"
      "L \<in># (DA0' # CAs0') ! i"
    then have "\<forall>S. S \<subseteq># (DA0' # CAs0') ! i \<longrightarrow> S \<cdot> (\<eta>0' # \<eta>s0') ! i = S \<cdot> \<eta>"
      using \<eta>_p by auto
    then have "{# L #} \<cdot> (\<eta>0' # \<eta>s0') ! i = {# L #} \<cdot> \<eta>"
      using a by (meson single_subset_iff)
    then show "L \<cdot>l (\<eta>0' # \<eta>s0') ! i = L \<cdot>l \<eta>" by auto
  qed
  have \<eta>_p_atm: "\<forall>i < Suc n. \<forall>A. A \<in> atms_of ((DA0' # CAs0') ! i) \<longrightarrow> A \<cdot>a (\<eta>0'#\<eta>s0') ! i = A \<cdot>a \<eta>"
  proof (rule, rule, rule, rule)
    fix i :: "nat" and A :: "'a"
    assume a:
      "i < Suc n"
      "A \<in> atms_of ((DA0' # CAs0') ! i)"
    then obtain L where L_p: "atm_of L = A \<and> L \<in># (DA0' # CAs0') ! i"
      unfolding atms_of_def by auto
    then have "L \<cdot>l (\<eta>0'#\<eta>s0') ! i = L \<cdot>l \<eta>"
      using \<eta>_p_lit a by auto
    then show "A \<cdot>a (\<eta>0' # \<eta>s0') ! i = A \<cdot>a \<eta>"
      using L_p unfolding subst_lit_def by (cases L) auto
  qed

  have DA0'_DA: "DA0' \<cdot> \<eta> = DA"
    using DA0'_DA \<eta>_p by auto
  have "D0' \<cdot> \<eta> = D" using \<eta>_p D0'_D n D0'_subset_DA0' by auto
  have "As0' \<cdot>al \<eta> = As"
  proof (rule nth_equalityI)
    show "length (As0' \<cdot>al \<eta>) = length As"
      using n by auto
  next
    fix i
    show "i<length (As0' \<cdot>al \<eta>) \<Longrightarrow> (As0' \<cdot>al \<eta>) ! i = As ! i"
    proof - 
      assume a: "i < length (As0' \<cdot>al \<eta>)"
      have A_eq: "\<forall>A. A \<in> atms_of DA0' \<longrightarrow> A \<cdot>a \<eta>0' = A \<cdot>a \<eta>"
        using \<eta>_p_atm n by force
      have "As0' ! i \<in> atms_of DA0'"
        using negs_As0'_subset_DA0' unfolding atms_of_def
        using a n by force
      then have "As0' ! i \<cdot>a \<eta>0' = As0' ! i \<cdot>a \<eta>"
         using A_eq by simp
      then show "(As0' \<cdot>al \<eta>) ! i = As ! i"
        using As0'_As \<open>length As0' = n\<close> a by auto
    qed
  qed

  interpret selection
    by (rule select)

  have "S DA0' \<cdot> \<eta> = S_M S M DA"
    using \<open>S DA0' \<cdot> \<eta>0' = S_M S M DA\<close> \<eta>_p S_selects_subseteq by auto

  from \<eta>_p have \<eta>_p_CAs0': "\<forall>i < n. (CAs0' ! i) \<cdot> (\<eta>s0' ! i) = (CAs0'! i) \<cdot> \<eta>"
    using n by auto
  then have "CAs0' \<cdot>\<cdot>cl \<eta>s0' = CAs0' \<cdot>cl \<eta>"
    using n by (auto intro: nth_equalityI)
  then have CAs0'_\<eta>_fo_CAs: "CAs0' \<cdot>cl \<eta> = CAs"
    using CAs0'_CAs \<eta>_p n by auto

  from \<eta>_p have "\<forall>i < n. S (CAs0' ! i) \<cdot> \<eta>s0' ! i = S (CAs0' ! i) \<cdot> \<eta>"
    using S_selects_subseteq n by auto
  then have "map S CAs0' \<cdot>\<cdot>cl \<eta>s0' = map S CAs0' \<cdot>cl \<eta>"
    using n by (auto intro: nth_equalityI)
  then have SCAs0'_\<eta>_fo_SMCAs: "map S CAs0' \<cdot>cl \<eta> = map (S_M S M) CAs"
    using \<open>map S CAs0' \<cdot>\<cdot>cl \<eta>s0' = map (S_M S M) CAs\<close> by auto

  have "Cs0' \<cdot>cl \<eta> = Cs"
  proof (rule nth_equalityI)
    show "length (Cs0' \<cdot>cl \<eta>) = length Cs"
      using n by auto
  next
    fix i
    show "i<length (Cs0' \<cdot>cl \<eta>) \<Longrightarrow> (Cs0' \<cdot>cl \<eta>) ! i = Cs ! i"
    proof -
      assume "i < length (Cs0' \<cdot>cl \<eta>)"
      then have a: "i < n"
        using n by force
      have "(Cs0' \<cdot>\<cdot>cl \<eta>s0') ! i = Cs ! i"
        using Cs0'_Cs a n by force
      moreover
      have \<eta>_p_CAs0': "\<forall>S. S \<subseteq># CAs0' ! i \<longrightarrow> S \<cdot> \<eta>s0' ! i = S \<cdot> \<eta>"
        using \<eta>_p a by force
      have "Cs0' ! i \<cdot> \<eta>s0' ! i = (Cs0' \<cdot>cl \<eta>) ! i"
        using \<eta>_p_CAs0' \<open>\<forall>i<n. Cs0' ! i \<subseteq># CAs0' ! i\<close> a n by force
      then have "(Cs0' \<cdot>\<cdot>cl \<eta>s0') ! i = (Cs0' \<cdot>cl \<eta>) ! i "
        using a n by force
      ultimately show "(Cs0' \<cdot>cl \<eta>) ! i = Cs ! i"
        by auto
    qed
  qed

  have AAs0'_AAs: "AAs0' \<cdot>aml \<eta> = AAs"
  proof (rule nth_equalityI)
    show "length (AAs0' \<cdot>aml \<eta>) = length AAs"
      using n by auto
  next
    fix i
    show "i<length (AAs0' \<cdot>aml \<eta>) \<Longrightarrow> (AAs0' \<cdot>aml \<eta>) ! i = AAs ! i"
    proof -
      assume a: "i < length (AAs0' \<cdot>aml \<eta>)"
      then have "i < n"
        using n by force
      then have "\<forall>A. A \<in> atms_of ((DA0' # CAs0') ! Suc i) \<longrightarrow> A \<cdot>a (\<eta>0' # \<eta>s0') ! Suc i = A \<cdot>a \<eta>"
        using \<eta>_p_atm n by force
      then have A_eq: "\<forall>A. A \<in> atms_of (CAs0' ! i) \<longrightarrow> A \<cdot>a \<eta>s0' ! i = A \<cdot>a \<eta>"
        by auto
      have AAs_CAs0': "\<forall>A \<in># AAs0' ! i. A \<in> atms_of (CAs0' ! i)"
        using AAs0'_in_atms_of_CAs0' unfolding atms_of_def
        using a n by force
      then have "AAs0' ! i \<cdot>am  \<eta>s0' ! i = AAs0' ! i \<cdot>am \<eta>"
        unfolding subst_atm_mset_def using A_eq unfolding subst_atm_mset_def by auto
      then show "(AAs0' \<cdot>aml \<eta>) ! i = AAs ! i"
         using AAs0'_AAs \<open>length AAs0' = n\<close> \<open>length \<eta>s0' = n\<close> a by auto
    qed
  qed

  \<comment> \<open>Obtain MGU and substitution\<close>
  obtain \<tau> \<phi> where \<tau>\<phi>:
    "Some \<tau> = mgu (set_mset ` set (map2 add_mset As0' AAs0'))"
    "\<tau> \<odot> \<phi> = \<eta> \<odot> \<sigma>"
  proof -
    have uu: "is_unifiers \<sigma> (set_mset ` set (map2 add_mset (As0' \<cdot>al \<eta>) (AAs0' \<cdot>aml \<eta>)))"
      using mgu mgu_sound is_mgu_def unfolding \<open>AAs0' \<cdot>aml \<eta> = AAs\<close> using \<open>As0' \<cdot>al \<eta> = As\<close> by auto
    have \<eta>\<sigma>uni: "is_unifiers (\<eta> \<odot> \<sigma>) (set_mset ` set (map2 add_mset As0' AAs0'))"
    proof -
      have "set_mset ` set (map2 add_mset As0' AAs0' \<cdot>aml \<eta>) =
        set_mset ` set (map2 add_mset As0' AAs0') \<cdot>ass \<eta>"
        unfolding subst_atmss_def subst_atm_mset_list_def using subst_atm_mset_def subst_atms_def
        by (simp add: image_image subst_atm_mset_def subst_atms_def)
      then have "is_unifiers \<sigma> (set_mset ` set (map2 add_mset As0' AAs0') \<cdot>ass \<eta>)"
        using uu by (auto simp: n map2_add_mset_map)
      then show ?thesis
        using is_unifiers_comp by auto
    qed
    then obtain \<tau> where
      \<tau>_p: "Some \<tau> = mgu (set_mset ` set (map2 add_mset As0' AAs0'))"
      using mgu_complete
      by (metis (mono_tags, hide_lams) List.finite_set finite_imageI finite_set_mset image_iff)
    moreover then obtain \<phi> where \<phi>_p: "\<tau> \<odot> \<phi> = \<eta> \<odot> \<sigma>"
      by (metis (mono_tags, hide_lams) finite_set \<eta>\<sigma>uni finite_imageI finite_set_mset image_iff
          mgu_sound set_mset_mset substitution_ops.is_mgu_def) (* should be simpler *)
    ultimately show thesis
      using that by auto
  qed

  \<comment> \<open>Lifting eligibility\<close>
  have eligible0': "eligible S \<tau> As0' (D0' + negs (mset As0'))"
  proof -
    have "S_M S M (D + negs (mset As)) = negs (mset As) \<or> S_M S M (D + negs (mset As)) = {#} \<and>
      length As = 1 \<and> maximal_wrt (As ! 0 \<cdot>a \<sigma>) ((D + negs (mset As)) \<cdot> \<sigma>)"
      using eligible unfolding eligible.simps by auto
    then show ?thesis
    proof
      assume "S_M S M (D + negs (mset As)) = negs (mset As)"
      then have "S_M S M (D + negs (mset As)) \<noteq> {#}"
        using n by force
      then have "S (D0' + negs (mset As0')) = negs (mset As0')"
        using as0' DA0'_split by auto
      then show ?thesis
        unfolding eligible.simps[simplified]  by auto
    next
      assume asm: "S_M S M (D + negs (mset As)) = {#} \<and> length As = 1 \<and>
        maximal_wrt (As ! 0 \<cdot>a \<sigma>) ((D + negs (mset As)) \<cdot> \<sigma>)"
      then have "S (D0' + negs (mset As0')) = {#}"
        using \<open>D0' \<cdot> \<eta> = D\<close>[symmetric] \<open>As0' \<cdot>al \<eta> = As\<close>[symmetric] \<open>S (DA0') \<cdot> \<eta> = S_M S M (DA)\<close>
          da DA0'_split subst_cls_empty_iff by metis
      moreover from asm have l: "length As0' = 1"
        using \<open>As0' \<cdot>al \<eta> = As\<close> by auto
      moreover from asm have "maximal_wrt (As0' ! 0 \<cdot>a (\<tau> \<odot> \<phi>)) ((D0' + negs (mset As0')) \<cdot> (\<tau> \<odot> \<phi>))"
        using \<open>As0' \<cdot>al \<eta> = As\<close> \<open>D0' \<cdot> \<eta> = D\<close> using l \<tau>\<phi> by auto
      then have "maximal_wrt (As0' ! 0 \<cdot>a \<tau> \<cdot>a \<phi>) ((D0' + negs (mset As0')) \<cdot> \<tau> \<cdot> \<phi>)"
        by auto
      then have "maximal_wrt (As0' ! 0 \<cdot>a \<tau>) ((D0' + negs (mset As0')) \<cdot> \<tau>)"
        using maximal_wrt_subst by blast
      ultimately show ?thesis
        unfolding eligible.simps[simplified] by auto
    qed
  qed

  \<comment> \<open>Lifting maximality\<close>
  have maximality: "\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a \<tau>) (Cs0' ! i \<cdot> \<tau>)"
    (* Reformulate in list notation? *)
  proof -
    from str_max have "\<forall>i < n. strictly_maximal_wrt ((As0' \<cdot>al \<eta>) ! i \<cdot>a \<sigma>) ((Cs0' \<cdot>cl \<eta>) ! i \<cdot> \<sigma>)"
      using \<open>As0' \<cdot>al \<eta> = As\<close>  \<open>Cs0' \<cdot>cl \<eta> = Cs\<close> by simp
    then have "\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a (\<tau> \<odot> \<phi>)) (Cs0' ! i \<cdot> (\<tau> \<odot> \<phi>))"
      using n \<tau>\<phi> by simp
    then have "\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a \<tau> \<cdot>a \<phi>) (Cs0' ! i \<cdot> \<tau> \<cdot> \<phi>)"
      by auto
    then show "\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a \<tau>) (Cs0' ! i \<cdot> \<tau>)"
      using strictly_maximal_wrt_subst \<tau>\<phi> by blast
  qed

  \<comment> \<open>Lifting nothing being selected\<close>
  have nothing_selected: "\<forall>i < n. S (CAs0' ! i) = {#}"
  proof -
    have "\<forall>i < n. (map S CAs0' \<cdot>cl \<eta>) ! i = map (S_M S M) CAs ! i"
      by (simp add: \<open>map S CAs0' \<cdot>cl \<eta> = map (S_M S M) CAs\<close>)
    then have "\<forall>i < n. S (CAs0' ! i) \<cdot> \<eta> = S_M S M (CAs ! i)"
      using n by auto
    then have "\<forall>i < n. S (CAs0' ! i)  \<cdot> \<eta> = {#}"
      using sel_empt \<open>\<forall>i < n.  S (CAs0' ! i) \<cdot> \<eta> = S_M S M (CAs ! i)\<close> by auto
    then show "\<forall>i < n. S (CAs0' ! i) = {#}"
      using subst_cls_empty_iff by blast
  qed

  \<comment> \<open>Lifting AAs0's non-emptiness\<close>
  have "\<forall>i < n. AAs0' ! i \<noteq> {#}"
    using n aas_not_empt \<open>AAs0' \<cdot>aml \<eta> = AAs\<close> by auto

  \<comment> \<open>Resolve the lifted clauses\<close>
  define E0' where
    "E0' = ((\<Union># (mset Cs0')) + D0') \<cdot> \<tau>"

  have res_e0': "ord_resolve S CAs0' DA0' AAs0' As0' \<tau> E0'"
    using ord_resolve.intros[of CAs0' n Cs0' AAs0' As0' \<tau> S D0',
      OF _ _ _ _ _ _ \<open>\<forall>i < n. AAs0' ! i \<noteq> {#}\<close> \<tau>\<phi>(1) eligible0'
        \<open>\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a \<tau>) (Cs0' ! i \<cdot> \<tau>)\<close> \<open>\<forall>i < n. S (CAs0' ! i) = {#}\<close>]
    unfolding E0'_def using DA0'_split n \<open>\<forall>i<n. CAs0' ! i = Cs0' ! i + poss (AAs0' ! i)\<close> by blast

  \<comment> \<open>Prove resolvent instantiates to ground resolvent\<close>
  have e0'\<phi>e: "E0' \<cdot> \<phi> = E"
  proof -
    have "E0' \<cdot> \<phi> = ((\<Union># (mset Cs0')) + D0') \<cdot> (\<tau> \<odot> \<phi>)"
      unfolding E0'_def by auto
    also have "\<dots> = (\<Union># (mset Cs0') + D0') \<cdot> (\<eta> \<odot> \<sigma>)"
      using \<tau>\<phi> by auto
    also have "\<dots> = (\<Union># (mset Cs) + D) \<cdot> \<sigma>"
      using \<open>Cs0' \<cdot>cl \<eta> = Cs\<close> \<open>D0' \<cdot> \<eta> = D\<close> by auto
    also have "\<dots> = E"
      using e by auto
    finally show e0'\<phi>e: "E0' \<cdot> \<phi> = E"
      .
  qed

  \<comment> \<open>Replace @{term \<phi>} with a true ground substitution\<close>
  obtain \<eta>2 where
    ground_\<eta>2: "is_ground_subst \<eta>2" "E0' \<cdot> \<eta>2 = E"
  proof -
    have "is_ground_cls_list CAs" "is_ground_cls DA"
      using grounding grounding_ground unfolding is_ground_cls_list_def by auto
    then have "is_ground_cls E"
      using res_e ground_resolvent_subset by (force intro: is_ground_cls_mono)
    then show thesis
      using that e0'\<phi>e make_ground_subst by auto
  qed

  have \<open>length CAs0 = length CAs\<close>
    using n by simp

  have \<open>length \<eta>s0 = length CAs\<close>
    using n by simp

  \<comment> \<open>Wrap up the proof\<close>
  have "ord_resolve S (CAs0 \<cdot>\<cdot>cl \<rho>s) (DA0 \<cdot> \<rho>) (AAs0 \<cdot>\<cdot>aml \<rho>s) (As0 \<cdot>al \<rho>) \<tau> E0'"
    using res_e0' As0'_def \<rho>_def AAs0'_def \<rho>s_def DA0'_def \<rho>_def CAs0'_def \<rho>s_def by simp
  moreover have "\<forall>i<n. poss (AAs0 ! i) \<subseteq># CAs0 ! i"
    using as0(19) by auto
  moreover have "negs (mset As0) \<subseteq># DA0"
    using local.as0(15) by auto
  ultimately have "ord_resolve_rename S CAs0 DA0 AAs0 As0 \<tau> E0'"
    using ord_resolve_rename[of CAs0 n AAs0 As0 DA0 \<rho> \<rho>s S \<tau> E0'] \<rho>_def \<rho>s_def n by auto
  then show thesis
    using that[of \<eta>0 \<eta>s0 \<eta>2 CAs0 DA0] \<open>is_ground_subst \<eta>0\<close> \<open>is_ground_subst_list \<eta>s0\<close>
      \<open>is_ground_subst \<eta>2\<close> \<open>CAs0 \<cdot>\<cdot>cl \<eta>s0 = CAs\<close> \<open>DA0 \<cdot> \<eta>0 = DA\<close> \<open>E0' \<cdot> \<eta>2 = E\<close> \<open>DA0 \<in> M\<close>
      \<open>\<forall>CA \<in> set CAs0. CA \<in> M\<close> \<open>length CAs0 = length CAs\<close> \<open>length \<eta>s0 = length CAs\<close>
  by blast
qed

end

end
