theory PAC_Map_Rel
  imports
    Refine_Imperative_HOL.IICF
    "HOL-Library.Finite_Map"
    Weidenbach_Book_Base.WB_List_More
begin
term hm.assn
definition fmap_rel where
  [to_relAPP]:
  "fmap_rel K V \<equiv> {(m1, m2).
     (\<forall>i j. i |\<in>| fmdom m2 \<longrightarrow> (j, i) \<in> K \<longrightarrow> (the (fmlookup m1 j), the (fmlookup m2 i)) \<in> V) \<and>
     fset (fmdom m1) \<subseteq> Domain K \<and> fset (fmdom m2) \<subseteq> Range K \<and>
     (\<forall>i j. (i, j) \<in> K \<longrightarrow> j |\<in>| fmdom m2 \<longleftrightarrow> i |\<in>| fmdom m1)}"


lemma fmap_rel_alt_def:
  \<open>\<langle>K, V\<rangle>fmap_rel \<equiv>
     {(m1, m2).
      (\<forall>i j. i \<in># dom_m m2 \<longrightarrow>
             (j, i) \<in> K \<longrightarrow> (the (fmlookup m1 j), the (fmlookup m2 i)) \<in> V) \<and>
      fset (fmdom m1) \<subseteq> Domain K \<and>
      fset (fmdom m2) \<subseteq> Range K \<and>
      (\<forall>i j. (i, j) \<in> K \<longrightarrow> (j \<in># dom_m m2) = (i \<in># dom_m m1))}
\<close>
  unfolding fmap_rel_def dom_m_def fmember.rep_eq
  by auto

lemma fmap_rel_empty1_simp[simp]:
  "(fmempty,m)\<in>\<langle>K,V\<rangle>fmap_rel \<longleftrightarrow> m=fmempty"
  apply (cases \<open>fmdom m = {||}\<close>)
  apply (auto simp: fmap_rel_def)
  apply (metis fmrestrict_fset_dom fmrestrict_fset_null)
  by (meson RangeE notin_fset subsetD)

lemma fmap_rel_empty2_simp[simp]:
  "(m,fmempty)\<in>\<langle>K,V\<rangle>fmap_rel \<longleftrightarrow> m=fmempty"
  apply (cases \<open>fmdom m = {||}\<close>)
  apply (auto simp: fmap_rel_def)
  apply (metis fmrestrict_fset_dom fmrestrict_fset_null)
  by (meson DomainE notin_fset subset_iff)

sepref_decl_intf ('k,'v) f_map is "('k, 'v) fmap"

lemma [synth_rules]: "\<lbrakk>INTF_OF_REL K TYPE('k); INTF_OF_REL V TYPE('v)\<rbrakk>
  \<Longrightarrow> INTF_OF_REL (\<langle>K,V\<rangle>fmap_rel) TYPE(('k,'v) f_map)" by simp

subsection \<open>Operations\<close>
  sepref_decl_op fmap_empty: "fmempty" :: "\<langle>K,V\<rangle>fmap_rel" .


  sepref_decl_op fmap_is_empty: "(=) fmempty" :: "\<langle>K,V\<rangle>fmap_rel \<rightarrow> bool_rel"
    apply (rule fref_ncI)
    apply parametricity
    apply (rule fun_relI; auto)
    done


lemma fmap_rel_fmupd_fmap_rel:
  \<open>(A, B) \<in> \<langle>K, R\<rangle>fmap_rel \<Longrightarrow> (p, p') \<in> K \<Longrightarrow> (q, q') \<in> R \<Longrightarrow>
   (fmupd p q A, fmupd p' q' B) \<in> \<langle>K, R\<rangle>fmap_rel\<close>
  if "single_valued K" "single_valued (K\<inverse>)"
  using that
  unfolding fmap_rel_alt_def
  apply (case_tac \<open>p' \<in># dom_m B\<close>)
  apply (auto simp add: all_conj_distrib IS_RIGHT_UNIQUED dest!: multi_member_split)
  done

  sepref_decl_op fmap_update: "fmupd" :: "K \<rightarrow> V \<rightarrow> \<langle>K,V\<rangle>fmap_rel \<rightarrow> \<langle>K,V\<rangle>fmap_rel"
    where "single_valued K" "single_valued (K\<inverse>)"
    apply (rule fref_ncI)
    apply parametricity
    apply (intro fun_relI)
    by (rule fmap_rel_fmupd_fmap_rel)


lemma fmap_rel_fmdrop_fmap_rel:
  \<open>(A, B) \<in> \<langle>K, R\<rangle>fmap_rel \<Longrightarrow> (p, p') \<in> K \<Longrightarrow>
   (fmdrop p A, fmdrop p' B) \<in> \<langle>K, R\<rangle>fmap_rel\<close>
  if "single_valued K" "single_valued (K\<inverse>)"
  using that
  unfolding fmap_rel_alt_def
  apply (auto simp add: all_conj_distrib IS_RIGHT_UNIQUED dest!: multi_member_split)
  apply (metis IS_RIGHT_UNIQUED dom_m_fmdrop fmlookup_drop in_dom_m_lookup_iff union_single_eq_member)
  apply (metis IS_RIGHT_UNIQUED dom_m_fmdrop fmlookup_drop in_dom_m_lookup_iff union_single_eq_member)
  by (metis IS_RIGHT_UNIQUED converse.intros dom_m_fmdrop fmlookup_drop in_dom_m_lookup_iff union_single_eq_member)

  sepref_decl_op fmap_delete: "fmdrop" :: "K \<rightarrow> \<langle>K,V\<rangle>fmap_rel \<rightarrow> \<langle>K,V\<rangle>fmap_rel"
    where "single_valued K" "single_valued (K\<inverse>)"
    apply (rule fref_ncI)
    apply parametricity
    by (auto simp add: fmap_rel_fmdrop_fmap_rel)

  lemma fmap_rel_nat_the_fmlookup:
    \<open>(A, B) \<in> \<langle>S, R\<rangle>fmap_rel \<Longrightarrow> (p, p') \<in> S \<Longrightarrow> p' \<in># dom_m B \<Longrightarrow>
     (the (fmlookup A p), the (fmlookup B p')) \<in> R\<close>
    by (auto simp: fmap_rel_alt_def distinct_mset_dom)

  lemma fmap_rel_in_dom_iff:
    \<open>(aa, a'a) \<in> \<langle>K, V\<rangle>fmap_rel \<Longrightarrow>
    (a, a') \<in> K \<Longrightarrow>
    a' \<in># dom_m a'a \<longleftrightarrow>
    a \<in># dom_m aa\<close>
    unfolding fmap_rel_alt_def
    by auto

  lemma fmap_rel_fmlookup_rel:
    \<open>(a, a') \<in> K \<Longrightarrow> (aa, a'a) \<in> \<langle>K, V\<rangle>fmap_rel \<Longrightarrow>
         (fmlookup aa a, fmlookup a'a a') \<in> \<langle>V\<rangle>option_rel\<close>
    using fmap_rel_nat_the_fmlookup[of aa a'a K V a a']
      fmap_rel_in_dom_iff[of aa a'a K V a a']
      in_dom_m_lookup_iff[of a' a'a]
      in_dom_m_lookup_iff[of a aa]
    by (cases \<open>a' \<in># dom_m a'a\<close>)
      auto


  sepref_decl_op fmap_lookup: "fmlookup" :: "\<langle>K,V\<rangle>fmap_rel \<rightarrow> K \<rightarrow>  \<langle>V\<rangle>option_rel"
    apply (rule fref_ncI)
    apply parametricity
    apply (intro fun_relI)
    apply (rule fmap_rel_fmlookup_rel; assumption)
    done

  lemma in_fdom_alt: "k\<in>#dom_m m \<longleftrightarrow> \<not>is_None (fmlookup m k)"
    apply (auto split: option.split intro: fmdom_notI simp: dom_m_def fmember.rep_eq)
    apply (meson fmdom_notI notin_fset)
    using notin_fset by fastforce

  sepref_decl_op fmap_contains_key: "\<lambda>k m. k\<in>#dom_m m" :: "K \<rightarrow> \<langle>K,V\<rangle>fmap_rel \<rightarrow> bool_rel"
    unfolding in_fdom_alt
    apply (rule fref_ncI)
    apply parametricity
    apply (rule fmap_rel_fmlookup_rel; assumption)
    done


subsection \<open>Patterns\<close>

lemma pat_fmap_empty[pat_rules]: "fmempty \<equiv> op_fmap_empty" by simp

lemma pat_map_is_empty[pat_rules]:
  "(=) $m$fmempty \<equiv> op_fmap_is_empty$m"
  "(=) $fmempty$m \<equiv> op_fmap_is_empty$m"
  "(=) $(dom_m$m)${#} \<equiv> op_fmap_is_empty$m"
  "(=) ${#}$(dom_m$m) \<equiv> op_fmap_is_empty$m"
  unfolding atomize_eq
  by (auto dest: sym)

lemma op_map_contains_key[pat_rules]:
  "(\<in>#) $ k $ (dom_m$m) \<equiv> op_fmap_contains_key$'k$'m"
   by (auto intro!: eq_reflection)


subsection \<open>Mapping to Normal Hashmaps\<close>

abbreviation map_of_fmap :: \<open>('k \<Rightarrow> 'v option) \<Rightarrow> ('k, 'v) fmap\<close> where
\<open>map_of_fmap h \<equiv> Abs_fmap h\<close>

definition map_fmap_rel where
  \<open>map_fmap_rel = br map_of_fmap (\<lambda>a. finite (dom a))\<close>

lemma fmdrop_set_None:
  \<open>(op_map_delete, fmdrop) \<in> Id \<rightarrow> map_fmap_rel \<rightarrow> map_fmap_rel\<close>
  apply (auto simp: map_fmap_rel_def br_def)
  apply (subst fmdrop.abs_eq)
  apply (auto simp: eq_onp_def fmap.Abs_fmap_inject
    map_drop_def map_filter_finite
     intro!: ext)
  apply (auto simp: map_filter_def)
  done

lemma map_upd_fmupd:
  \<open>(op_map_update, fmupd) \<in> Id \<rightarrow> Id \<rightarrow> map_fmap_rel \<rightarrow> map_fmap_rel\<close>
  apply (auto simp: map_fmap_rel_def br_def)
  apply (subst fmupd.abs_eq)
  apply (auto simp: eq_onp_def fmap.Abs_fmap_inject
    map_drop_def map_filter_finite map_upd_def
     intro!: ext)
  done


text \<open>Technically @{term op_map_lookup} has the arguments in the wrong direction.\<close>
definition fmlookup' where
  [simp]: \<open>fmlookup' A k = fmlookup k A\<close>


lemma [def_pat_rules]:
  \<open>((\<in>#)$k$(dom_m$A)) \<equiv> Not$(is_None$(fmlookup'$k$A))\<close>
  apply (auto split: option.split simp: dom_m_def)
  by (smt domIff fmdom.rep_eq option.disc_eq_case(1))

lemma op_map_lookup_fmlookup:
  \<open>(op_map_lookup, fmlookup') \<in> Id \<rightarrow> map_fmap_rel \<rightarrow> \<langle>Id\<rangle>option_rel\<close>
  by (auto simp: map_fmap_rel_def br_def fmap.Abs_fmap_inverse)


abbreviation hm_fmap_assn where
  \<open>hm_fmap_assn K V \<equiv> hr_comp (hm.assn K V) map_fmap_rel\<close>

lemmas fmap_delete_hnr [sepref_fr_rules] =
   hm.delete_hnr[FCOMP fmdrop_set_None]

lemmas fmap_update_hnr [sepref_fr_rules] =
   hm.update_hnr[FCOMP map_upd_fmupd]


lemmas fmap_lookup_hnr [sepref_fr_rules] =
   hm.lookup_hnr[FCOMP op_map_lookup_fmlookup]

lemma fmempty_empty:
  \<open>(uncurry0 (RETURN op_map_empty), uncurry0 (RETURN fmempty)) \<in> unit_rel \<rightarrow>\<^sub>f \<langle>map_fmap_rel\<rangle>nres_rel\<close>
  by (auto simp: map_fmap_rel_def br_def fmempty_def frefI nres_relI)

lemmas [sepref_fr_rules] =
  hm.empty_hnr[FCOMP fmempty_empty, unfolded op_fmap_empty_def[symmetric]]


abbreviation iam_fmap_assn where
  \<open>iam_fmap_assn K V \<equiv> hr_comp (iam.assn K V) map_fmap_rel\<close>

lemmas iam_fmap_delete_hnr [sepref_fr_rules] =
   iam.delete_hnr[FCOMP fmdrop_set_None]

lemmas iam_ffmap_update_hnr [sepref_fr_rules] =
   iam.update_hnr[FCOMP map_upd_fmupd]


lemmas iam_ffmap_lookup_hnr [sepref_fr_rules] =
   iam.lookup_hnr[FCOMP op_map_lookup_fmlookup]

definition op_iam_fmap_empty where
  \<open>op_iam_fmap_empty = fmempty\<close>

lemma iam_fmempty_empty:
  \<open>(uncurry0 (RETURN op_map_empty), uncurry0 (RETURN op_iam_fmap_empty)) \<in> unit_rel \<rightarrow>\<^sub>f \<langle>map_fmap_rel\<rangle>nres_rel\<close>
  by (auto simp: map_fmap_rel_def br_def fmempty_def frefI nres_relI op_iam_fmap_empty_def)

lemmas [sepref_fr_rules] =
  iam.empty_hnr[FCOMP fmempty_empty, unfolded op_iam_fmap_empty_def[symmetric]]

definition upper_bound_on_dom where
  \<open>upper_bound_on_dom A = SPEC(\<lambda>n. \<forall>i \<in>#(dom_m A). i < n)\<close>

lemma [sepref_fr_rules]:
   \<open>((Array.len), upper_bound_on_dom) \<in> (iam_fmap_assn nat_assn V)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
proof -
  have [simp]: \<open>finite (dom b) \<Longrightarrow> i \<in> fset (fmdom (map_of_fmap b)) \<longleftrightarrow> i \<in> dom b\<close> for i b
    by (subst fmdom.abs_eq)
     (auto simp: eq_onp_def fset.Abs_fset_inverse)
  have 2: \<open>nat_rel = the_pure (nat_assn)\<close> and
    3: \<open>nat_assn = pure nat_rel\<close>
    by auto
  have [simp]: \<open>the_pure (\<lambda>a c :: nat. \<up> (c = a)) = nat_rel\<close>
    apply (subst 2)
    apply (subst 3)
    apply (subst pure_def)
    apply auto
    done

  have [simp]: \<open>(iam_of_list l, b) \<in> the_pure (\<lambda>a c :: nat. \<up> (c = a)) \<rightarrow> \<langle>the_pure V\<rangle>option_rel \<Longrightarrow>
       b i = Some y \<Longrightarrow> i < length l\<close>  for i b l y
    by (auto dest!: fun_relD[of _ _ _ _ i i] simp: option_rel_def
      iam_of_list_def split: if_splits)
  show ?thesis
   by sepref_to_hoare
     (sep_auto simp: upper_bound_on_dom_def hr_comp_def iam.assn_def map_rel_def
     map_fmap_rel_def is_iam_def br_def dom_m_def)
qed

end
