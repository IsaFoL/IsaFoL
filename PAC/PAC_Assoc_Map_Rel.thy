theory PAC_Assoc_Map_Rel
  imports PAC_Map_Rel
begin

definition hassoc_map_rel where
  \<open>hassoc_map_rel = br map_of (\<lambda>_. True)\<close>

abbreviation hassoc_map_assn where
  \<open>hassoc_map_assn \<equiv> pure (hassoc_map_rel)\<close>

lemma hassoc_map_rel_empty[simp]:
  \<open>([], m) \<in> hassoc_map_rel \<longleftrightarrow> m = Map.empty\<close>
  \<open>(p, Map.empty) \<in> hassoc_map_rel \<longleftrightarrow> p = []\<close>
  \<open>hassoc_map_assn Map.empty [] = emp\<close>
  by (auto simp: hassoc_map_rel_def br_def pure_def)

definition hassoc_new :: \<open>('k \<times> 'v) list Heap\<close>where
  \<open>hassoc_new = return []\<close>

  lemma precise_hassoc_map_assn: \<open>precise hassoc_map_assn\<close>
    by (auto intro!: precise_pure)
     (auto simp: single_valued_def hassoc_map_rel_def
      br_def)

  definition hassoc_isEmpty :: "('k \<times> 'v) list \<Rightarrow> bool Heap" where
   "hassoc_isEmpty ht \<equiv> return (length ht = 0)"


 interpretation hassoc: bind_map_empty hassoc_map_assn hassoc_new
    by unfold_locales
     (auto intro: precise_hassoc_map_assn
         simp: ent_refl_true hassoc_new_def
       intro!: return_cons_rule)


  interpretation hassoc: bind_map_is_empty hassoc_map_assn hassoc_isEmpty
    by unfold_locales
      (auto simp: precise_hassoc_map_assn hassoc_isEmpty_def ent_refl_true
       intro!: precise_pure return_cons_rule)

  definition "op_assoc_empty \<equiv> IICF_Map.op_map_empty"
 
  interpretation hassoc: map_custom_empty op_assoc_empty
    by unfold_locales (simp add: op_assoc_empty_def)


  lemmas [sepref_fr_rules] = hassoc.empty_hnr[folded op_assoc_empty_def]

  definition hassoc_update :: "'k \<Rightarrow> 'v \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> ('k \<times> 'v) list Heap" where
   "hassoc_update k v ht = return ((k, v ) # ht)"

  lemma hassoc_map_assn_Cons:
     \<open>hassoc_map_assn (m) (p) \<Longrightarrow>\<^sub>A hassoc_map_assn (m(k \<mapsto> v)) ((k, v) # p) * true\<close>
     by (auto simp: hassoc_map_rel_def pure_def br_def)

  interpretation hassoc: bind_map_update hassoc_map_assn hassoc_update
    by unfold_locales
     (auto intro!: return_cons_rule
      simp: hassoc_update_def hassoc_map_assn_Cons)


  definition hassoc_delete :: \<open>'k \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> ('k \<times> 'v) list Heap\<close> where
    \<open>hassoc_delete k ht = return (filter (\<lambda>(a, b). a \<noteq> k) ht)\<close>

  lemma hassoc_map_of_filter_all:
    \<open>map_of p |` (- {k}) = map_of (filter (\<lambda>(a, b). a \<noteq> k) p)\<close>
    apply (induction p)
    apply (auto simp: restrict_map_def fun_eq_iff split: if_split)
    apply (metis (mono_tags, lifting))
    apply smt
    by (smt fst_conv)+

  lemma hassoc_map_assn_hassoc_delete: \<open><hassoc_map_assn m
         p> hassoc_delete k p <hassoc_map_assn (m |` (- {k}))>\<^sub>t\<close>
   by (auto simp: hassoc_delete_def hassoc_map_rel_def pure_def br_def
           hassoc_map_of_filter_all
         intro!: return_cons_rule)

  interpretation hassoc: bind_map_delete hassoc_map_assn hassoc_delete
    by unfold_locales
     (auto intro: hassoc_map_assn_hassoc_delete)


  definition hassoc_lookup :: \<open>'k \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> ('v) option Heap\<close> where
    \<open>hassoc_lookup k ht = return (map_of ht k)\<close>

  lemma hassoc_map_assn_hassoc_lookup:
    \<open><hassoc_map_assn m p> hassoc_lookup k p <\<lambda>r. hassoc_map_assn m p * \<up> (r = m k)>\<^sub>t\<close>
     by (auto simp: hassoc_lookup_def hassoc_map_rel_def pure_def br_def
             hassoc_map_of_filter_all
           intro!: return_cons_rule)

  interpretation hassoc: bind_map_lookup hassoc_map_assn hassoc_lookup
    by unfold_locales
     (rule hassoc_map_assn_hassoc_lookup)

  setup Locale_Code.open_block
  interpretation hassoc: gen_contains_key_by_lookup hassoc_map_assn hassoc_lookup
    by unfold_locales
  setup Locale_Code.close_block

  interpretation hassoc: bind_map_contains_key hassoc_map_assn hassoc.contains_key
    by unfold_locales


end
