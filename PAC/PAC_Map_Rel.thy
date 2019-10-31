theory PAC_Map_Rel
  imports
    Refine_Imperative_HOL.IICF
    "HOL-Library.Finite_Map"
    Weidenbach_Book_Base.WB_List_More
begin

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

  sepref_decl_op fmap_update: "fmupd" :: "K \<rightarrow> V \<rightarrow> \<langle>K,V\<rangle>fmap_rel \<rightarrow> \<langle>K,V\<rangle>fmap_rel"
    where "single_valued K" "single_valued (K\<inverse>)"
    apply (rule fref_ncI)
    apply parametricity
    unfolding fmap_rel_alt_def
    apply (intro fun_relI)
    apply (case_tac \<open>a' \<in># dom_m a'b\<close>)
    apply (auto simp add: all_conj_distrib IS_RIGHT_UNIQUED dest!: multi_member_split)
    done

  sepref_decl_op fmap_delete: "fmdrop" :: "K \<rightarrow> \<langle>K,V\<rangle>fmap_rel \<rightarrow> \<langle>K,V\<rangle>fmap_rel"
    where "single_valued K" "single_valued (K\<inverse>)"
    apply (rule fref_ncI)
    apply parametricity
    unfolding fmap_rel_alt_def
    apply (auto simp add: all_conj_distrib IS_RIGHT_UNIQUED dest!: multi_member_split)
    apply (metis IS_RIGHT_UNIQUED dom_m_fmdrop fmlookup_drop in_dom_m_lookup_iff union_single_eq_member)
    apply (metis IS_RIGHT_UNIQUED dom_m_fmdrop fmlookup_drop in_dom_m_lookup_iff union_single_eq_member)
    apply (metis IS_RIGHT_UNIQUED dom_m_fmdrop fmlookup_drop in_dom_m_lookup_iff union_single_eq_member)
    by (metis IS_RIGHT_UNIQUED converse.intros dom_m_fmdrop fmlookup_drop in_dom_m_lookup_iff union_single_eq_member)

lemma fmap_rel_fmlookup_rel:
  \<open>(a, a') \<in> K \<Longrightarrow>
       (aa, a'a) \<in> \<langle>K, V\<rangle>fmap_rel \<Longrightarrow>
       (fmlookup aa a, fmlookup a'a a') \<in> \<langle>V\<rangle>option_rel\<close>
    unfolding fmap_rel_alt_def
    apply (auto)
    by (smt autoref_opt(1) fmupd_lookup fmupd_same in_dom_m_lookup_iff option_relI(2))

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


subsection \<open>Parametricity\<close>

locale fmap_custom_empty =
  fixes op_custom_empty :: "('k, 'v) fmap"
  assumes op_custom_empty_def: "op_custom_empty = op_fmap_empty"
begin
  sepref_register op_custom_empty :: "('kx,'vx) f_map"

  lemma fold_custom_empty:
    "fmempty = op_custom_empty"
    "op_fmap_empty = op_custom_empty"
    "mop_fmap_empty = RETURN op_custom_empty"
    unfolding op_custom_empty_def by simp_all
end

end
