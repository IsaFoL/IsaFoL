theory IsaSAT_Clauses
  imports IsaSAT_Arena
begin

(* TODO This file should probably be merged with IsaSAT_Arena*)


subsubsection \<open>Representation of Clauses\<close>

(* TODO kill *)
named_theorems isasat_codegen \<open>lemmas that should be unfolded to generate (efficient) code\<close>

type_synonym clause_annot = \<open>clause_status \<times> nat \<times> nat\<close>

type_synonym clause_annots = \<open>clause_annot list\<close>


definition list_fmap_rel :: \<open>_ \<Rightarrow> (arena \<times> nat clauses_l) set\<close> where
  \<open>list_fmap_rel vdom = {(arena, N). valid_arena arena N vdom}\<close>

lemma nth_clauses_l:
  \<open>(uncurry2 (RETURN ooo (\<lambda>N i j. arena_lit N (i+j))),
      uncurry2 (RETURN ooo (\<lambda>N i j. N \<propto> i ! j)))
    \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>f
      list_fmap_rel vdom \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: list_fmap_rel_def arena_lifting)

abbreviation clauses_l_fmat where
  \<open>clauses_l_fmat \<equiv> list_fmap_rel\<close>

abbreviation isasat_clauses_assn where
  \<open>isasat_clauses_assn \<equiv> arlO_assn clause_ll_assn *a arl_assn (clause_status_assn *a uint32_nat_assn *a uint32_nat_assn)\<close>

type_synonym vdom = \<open>nat set\<close>

definition clauses_ll_assn
   :: \<open>vdom \<Rightarrow> nat clauses_l \<Rightarrow> uint32 array_list \<Rightarrow> assn\<close>
where
  \<open>clauses_ll_assn vdom = hr_comp arena_assn (clauses_l_fmat vdom)\<close>

definition fmap_rll :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal" where
  [simp]: \<open>fmap_rll l i j = l \<propto> i ! j\<close>

definition fmap_rll_u :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal" where
  [simp]: \<open>fmap_rll_u  = fmap_rll\<close>

lemma nth_raa_hnr':
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 (\<lambda>(N, _) j k. nth_raa N j k), uncurry2 (RETURN \<circ>\<circ>\<circ> (\<lambda>(N, _) i. Array_List_Array.nth_rll N i))) \<in>
       [\<lambda>(((l, _),i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R) *a GG)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  using assms
  by sepref_to_hoare sep_auto

definition fmap_rll_u64 :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal" where
  [simp]: \<open>fmap_rll_u64  = fmap_rll\<close>

lemma nth_raa_i_uint64_hnr':
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 (\<lambda>(N, _) j. nth_raa_i_u64 N j), uncurry2 (RETURN \<circ>\<circ>\<circ> (\<lambda>(N, _) j. nth_rll N j))) \<in>
       [\<lambda>(((l, _),i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R) *a GG)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_raa_i_u64_def
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

sepref_definition nth_rll_u32_i64_clauses
  is \<open>uncurry2 (RETURN ooo (\<lambda>(N, _) j. nth_rll N j))\<close>
  :: \<open>[\<lambda>(((xs, _), i), j). i < length xs \<and> j < length (xs !i)]\<^sub>a
     (isasat_clauses_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  by sepref


sepref_definition nth_rll_u64_i64_clauses
  is \<open>uncurry2 (RETURN ooo (\<lambda>(N, _) j. nth_rll N j))\<close>
  :: \<open>[\<lambda>(((xs, _), i), j). i < length xs \<and> j < length (xs !i)]\<^sub>a
     (isasat_clauses_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  by sepref

(* lemma fmap_rll_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (\<lambda>(N, _) j. nth_raa_i_u64 N j), uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u64))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is ?slow is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
   fmap_rll_i32_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry2 nth_rll_u32_i64_clauses, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u64))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>) and
   fmap_rll_i64_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry2 nth_rll_u64_i64_clauses, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u64))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is ?fast' is \<open>?cfast' \<in> [?pre]\<^sub>a ?imfast' \<rightarrow> ?ffast'\<close>)
proof -
  have H:
    \<open>?c \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
         (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
        (\<lambda>_ (((l, _), i), j). i < length l \<and> j < length_rll l i)
         (\<lambda>_. True)]\<^sub>a
       hrp_comp ((isasat_clauses_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_rll_u64_def
    by (rule hfref_compI_PRE_aux[OF nth_raa_i_uint64_hnr' nth_clauses_rll, of unat_lit_assn]) simp
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def list_fmap_rel_def length_rll_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    by auto
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im fmap_rll_u_def apply assumption
    using pre ..
  have H:
    \<open>?cfast \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
         (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
        (\<lambda>_ (((l, _), i), j). i < length l \<and> j < length (l!i))
         (\<lambda>_. True)]\<^sub>a
       hrp_comp ((isasat_clauses_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_rll_u64_def
    by (rule hfref_compI_PRE_aux[OF nth_rll_u32_i64_clauses.refine nth_clauses_rll])
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?ffast\<close>
    by auto
  show ?fast
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im fmap_rll_u_def apply assumption
    using pre unfolding length_rll_def ..
  have H:
    \<open>?cfast' \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
         (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
        (\<lambda>_ (((l, _), i), j). i < length l \<and> j < length (l!i))
         (\<lambda>_. True)]\<^sub>a
       hrp_comp ((isasat_clauses_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_rll_u64_def
    by (rule hfref_compI_PRE_aux[OF nth_rll_u64_i64_clauses.refine nth_clauses_rll])
  have im: \<open>?im' = ?imfast'\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?ffast'\<close>
    by auto
  show ?fast'
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im fmap_rll_u_def apply assumption
    using pre unfolding length_rll_def ..
qed *)


definition fmap_length_rll_u :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat" where
  \<open>fmap_length_rll_u l i = length_uint32_nat (l \<propto> i)\<close>

declare fmap_length_rll_u_def[symmetric, isasat_codegen]

sepref_definition length_rll_n_uint32_clss
  is \<open>uncurry (RETURN oo (\<lambda>(N, _) i. length_rll_n_uint32 N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint_max]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref

(* lemma fmap_length_rll_u_hnr[sepref_fr_rules]:
  \<open>(uncurry length_rll_n_uint32_clss, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u))
     \<in> [\<lambda>(N, i). i \<in># dom_m N \<and> length (N \<propto> i) \<le> uint_max]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
   (is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>(uncurry length_rll_n_uint32_clss, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u))
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ ((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint_max)
            (\<lambda>_. True)]\<^sub>a
         hrp_comp ((isasat_clauses_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                  (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
         hr_comp uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_rll_n_uint32_clss.refine fmap_length_rll_u])
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def list_fmap_rel_def length_rll_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    by auto
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
qed *)

sepref_definition length_raa_i64_u_clss
  is \<open>uncurry (RETURN oo (\<lambda>(N, _) i. length_rll_n_uint32 N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint_max]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref

(* lemma fmap_length_rll_i64_u_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_i64_u_clss, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u))
     \<in> [\<lambda>(N, i). i \<in># dom_m N \<and> length (N \<propto> i) \<le> uint_max]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
   (is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>(uncurry length_raa_i64_u_clss, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u))
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ ((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint_max)
            (\<lambda>_. True)]\<^sub>a
         hrp_comp ((isasat_clauses_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)
                  (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
         hr_comp uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_raa_i64_u_clss.refine fmap_length_rll_u])
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def list_fmap_rel_def length_rll_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    by auto
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
qed *)

definition fmap_length_rll_u64 :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat" where
  \<open>fmap_length_rll_u64 l i = length_uint32_nat (l \<propto> i)\<close>


declare fmap_length_rll_u_def[symmetric, isasat_codegen]


sepref_definition length_raa_u64_clss
  is \<open>uncurry ((RETURN \<circ>\<circ>\<circ> case_prod) (\<lambda>N _. length_rll_n_uint64 N))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
        isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref

sepref_definition length_raa_u32_u64_clss
  is \<open>uncurry ((RETURN \<circ>\<circ>\<circ> case_prod) (\<lambda>N _. length_rll_n_uint64 N))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
        isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref

sepref_definition length_raa_u64_u64_clss
  is \<open>uncurry ((RETURN \<circ>\<circ>\<circ> case_prod) (\<lambda>N _. length_rll_n_uint64 N))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
        isasat_clauses_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref

(* lemma fmap_length_rll_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_u64_clss, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u64))
     \<in> [\<lambda>(N, i). i \<in># dom_m N \<and> length (N \<propto> i) \<le> uint64_max]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
   (is ?slow is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
  fmap_length_rll_u32_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_u32_u64_clss, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u64))
     \<in> [\<lambda>(N, i). i \<in># dom_m N \<and> length (N \<propto> i) \<le> uint64_max]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
   (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>) and
  fmap_length_rll_u64_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_u64_u64_clss, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u64))
     \<in> [\<lambda>(N, i). i \<in># dom_m N \<and> length (N \<propto> i) \<le> uint64_max]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
   (is ?fast' is \<open>?cfast' \<in> [?pre]\<^sub>a ?imfast' \<rightarrow> ?ffast'\<close>)
proof -
  have H:
    \<open>?c
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ ((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint64_max)
            (\<lambda>_. True)]\<^sub>a
         hrp_comp ((isasat_clauses_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k) (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
         hr_comp uint64_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_raa_u64_clss.refine fmap_length_rll_u64])
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def list_fmap_rel_def length_rll_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    by auto
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
  have H:
    \<open>?cfast
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ ((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint64_max)
            (\<lambda>_. True)]\<^sub>a
         hrp_comp (isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k) (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
         hr_comp uint64_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_raa_u32_u64_clss.refine fmap_length_rll_u64])
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?ffast\<close>
    by auto
  show ?fast
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
  have H:
    \<open>?cfast'
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ ((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint64_max)
            (\<lambda>_. True)]\<^sub>a
         hrp_comp (isasat_clauses_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k) (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
         hr_comp uint64_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_raa_u64_u64_clss.refine fmap_length_rll_u64])
  have im: \<open>?im' = ?imfast'\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?ffast'\<close>
    by auto
  show ?fast'
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
qed *)


definition fmap_length_rll :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat" where
  [simp]: \<open>fmap_length_rll l i = length (l \<propto> i)\<close>


(*TODO rename length_rll_n_uint32*)
(* lemma fmap_length_rll:
  \<open>(uncurry (RETURN oo (\<lambda>(N, _) j. length_rll N j)), uncurry (RETURN oo fmap_length_rll))
    \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>f \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def fmap_length_rll_def length_rll_def) *)



sepref_definition length_raa_u32_clss
  is \<open>uncurry (RETURN \<circ>\<circ> (\<lambda>(N, _) i. length_rll N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs]\<^sub>a isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref

sepref_definition length_raa_clss
  is \<open>uncurry (RETURN \<circ>\<circ> (\<lambda>(N, _) i. length_rll N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs]\<^sub>a isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref

(* lemma fmap_length_rll_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_clss, uncurry (RETURN \<circ>\<circ> fmap_length_rll))
     \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
   (is ?slow is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
 fmap_length_rll_u32_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_u32_clss, uncurry (RETURN \<circ>\<circ> fmap_length_rll))
     \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
   (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have H:
    \<open>?c
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel)
            (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ ((xs, _), i). i < length xs)
            (\<lambda>_. True)]\<^sub>a
          hrp_comp (isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k) (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
           hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_raa_clss.refine fmap_length_rll])
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def list_fmap_rel_def length_rll_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    by auto
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
  have H:
    \<open>?cfast
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel)
            (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ ((xs, _), i). i < length xs)
            (\<lambda>_. True)]\<^sub>a
          hrp_comp (isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k) (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
           hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_raa_u32_clss.refine fmap_length_rll])
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?ffast\<close>
    by auto
  show ?fast
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
qed *)

definition fmap_swap_ll where
  [simp]: \<open>fmap_swap_ll N i j f = (N(i \<hookrightarrow> swap (N \<propto> i) j f))\<close>

(* lemma swap_ll_fmap_swap_ll:
  \<open>(uncurry3 (RETURN oooo (\<lambda>(N, xs) i j k. (swap_ll N i j k, xs))), uncurry3 (RETURN oooo fmap_swap_ll))
    \<in> [\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i)]\<^sub>f
        \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>clauses_l_fmat\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto 5 5 simp: list_fmap_rel_def Array_List_Array.swap_ll_def
      split: if_splits) *)

sepref_definition swap_aa_clss
  is \<open>uncurry3 (RETURN oooo (\<lambda>(N, xs) i j k. (swap_ll N i j k, xs)))\<close>
  :: \<open>[\<lambda>((((xs, _), k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k]\<^sub>a
      isasat_clauses_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> isasat_clauses_assn\<close>
  by sepref

(* lemma fmap_swap_ll_hnr[sepref_fr_rules]:
  \<open>(uncurry3 swap_aa_clss, uncurry3 (RETURN oooo fmap_swap_ll))
     \<in> [\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> clauses_ll_assn\<close>
   (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>?c \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
             (\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i))
             (\<lambda>_ ((((xs, _), k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k)
             (\<lambda>_. True)]\<^sub>a
          hrp_comp ((isasat_clauses_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
          hr_comp (isasat_clauses_assn) (\<langle>Id\<rangle>clauses_l_fmat)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF swap_aa_clss.refine swap_ll_fmap_swap_ll])
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def list_fmap_rel_def length_rll_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
qed *)

text \<open>From a performance point of view, appending several time a single element is less efficient
than reserving a space that is large enough directly. However, in this case the list of clauses \<^term>\<open>N\<close>
is so large that there should not be any difference\<close>
definition fm_add_new where
 \<open>fm_add_new b C N = do {
    let st = (if b then AStatus IRRED False else AStatus LEARNED False);
    let l = length N;
    let s = length C - 2;
    let N = (if is_short_clause C then
          (((N @ [st]) @ [AActivity zero_uint32_nat]) @ [ALBD s]) @ [ASize s]
          else ((((N @ [APos zero_uint32_nat]) @ [st]) @ [AActivity zero_uint32_nat]) @ [ALBD s]) @ [ASize (s)]);
    (i, N) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, N). i < length C)
      (\<lambda>(i, N). do {
        ASSERT(i < length C);
        RETURN (i+one_uint64_nat, N @ [ALit (C ! i)])
      })
      (zero_uint64_nat, N);
    RETURN (N, l + header_size C)
  }\<close>

lemma header_size_Suc_def:
  \<open>header_size C =
    (if is_short_clause C then Suc (Suc (Suc (Suc 0))) else Suc (Suc (Suc (Suc (Suc 0)))))\<close>
  unfolding header_size_def
  by auto

lemma nth_append_clause:
  \<open>a < length C \<Longrightarrow> append_clause b C N ! (length N + header_size C + a) = ALit (C ! a)\<close>
  unfolding append_clause_def header_size_Suc_def append_clause_skeleton_def
  by (auto simp: nth_Cons nth_append)

lemma fm_add_new_append_clause:
  \<open>fm_add_new b C N \<le> RETURN (append_clause b C N, length N + header_size C)\<close>
  unfolding fm_add_new_def
  apply (rewrite at \<open>let _ = length _ in _\<close> Let_def)
  apply (refine_vcg WHILET_rule[where R = \<open>measure (\<lambda>(i, _). Suc (length C) - i)\<close> and
    I = \<open>\<lambda>(i, N'). N' = take (length N + header_size C + i) (append_clause b C N) \<and>
      i \<le> length C\<close>])
  subgoal by auto
  subgoal by (auto simp: append_clause_def header_size_def
    append_clause_skeleton_def split: if_splits)
  subgoal by simp
  subgoal by simp
  subgoal by (auto simp: take_Suc_conv_app_nth nth_append_clause)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

definition fm_add_new_at_position
   :: \<open>bool \<Rightarrow> nat \<Rightarrow> 'v clause_l \<Rightarrow> 'v clauses_l \<Rightarrow> 'v clauses_l\<close>
where
  \<open>fm_add_new_at_position b i C N = fmupd i (C, b) N\<close>

definition AStatus_IRRED where
  \<open>AStatus_IRRED = AStatus IRRED False\<close>

lemma AStatus_IRRED [sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN AStatus_IRRED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_IRRED_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
      status_rel_def bitfield_rel_def nat_0_AND)

definition AStatus_IRRED2 where
  \<open>AStatus_IRRED2 = AStatus IRRED True\<close>

lemma AStatus_IRRED2 [sepref_fr_rules]:
  \<open>(uncurry0 (return 0b100), uncurry0 (RETURN AStatus_IRRED2)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_IRRED2_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
      status_rel_def bitfield_rel_def nat_0_AND)

definition AStatus_LEARNED where
  \<open>AStatus_LEARNED = AStatus LEARNED True\<close>

lemma AStatus_LEARNED [sepref_fr_rules]:
  \<open>(uncurry0 (return 0b101), uncurry0 (RETURN AStatus_LEARNED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_LEARNED_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
      status_rel_def bitfield_rel_def)


definition AStatus_LEARNED2 where
  \<open>AStatus_LEARNED2 = AStatus LEARNED False\<close>

lemma AStatus_LEARNED2 [sepref_fr_rules]:
  \<open>(uncurry0 (return 0b001), uncurry0 (RETURN AStatus_LEARNED2)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_LEARNED2_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
    status_rel_def bitfield_rel_def)

sepref_definition is_short_clause_code
  is \<open>RETURN o is_short_clause\<close>
  :: \<open>clause_ll_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding is_short_clause_def MAX_LENGTH_SHORT_CLAUSE_def
  by sepref

lemma AActivity_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o AActivity) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_LEARNED_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
    status_rel_def)

lemma ALBD_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o ALBD) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_LEARNED_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
    status_rel_def)

lemma ASize_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o ASize) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_LEARNED_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
    status_rel_def)

lemma APos_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o APos) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
    status_rel_def)

lemma ALit_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o ALit) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  apply sepref_to_hoare
  by sep_auto
    (sep_auto simp: arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def unat_lit_rel_def)

declare is_short_clause_code.refine[sepref_fr_rules]

sepref_definition header_size_code
  is \<open>RETURN o header_size\<close>
  :: \<open>clause_ll_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding header_size_def
  by sepref

declare header_size_code.refine[sepref_fr_rules]

sepref_definition append_and_length_code
  is \<open>uncurry2 fm_add_new\<close>
  :: \<open>[\<lambda>((b, C), N). length C \<le> uint32_max+2 \<and> length C \<ge> 2]\<^sub>a bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a (arena_assn)\<^sup>d \<rightarrow>
       arena_assn *a nat_assn\<close>
  supply [[goals_limit=1]] le_uint32_max_le_uint64_max[intro]
  unfolding fm_add_new_def AStatus_IRRED_def[symmetric] AStatus_IRRED2_def[symmetric]
   AStatus_LEARNED_def[symmetric] AStatus_LEARNED2_def[symmetric]
   two_uint64_nat_def[symmetric]
   apply (rewrite in \<open>let _ = _ - _ in _\<close> length_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ in let _ = _ in let _ = \<hole> in _\<close> uint32_of_uint64_conv_def[symmetric])
   apply (rewrite in \<open>_ < length _\<close> length_uint64_nat_def[symmetric])
  by sepref

declare append_and_length_code.refine[sepref_fr_rules]


definition (in -)fm_add_new_fast where
 [simp]: \<open>fm_add_new_fast = fm_add_new\<close>

lemma (in -)append_and_length_code_fast:
  \<open>length ba \<le> Suc (Suc uint_max) \<Longrightarrow>
       2 \<le> length ba \<Longrightarrow>
       length b \<le> uint64_max - (uint_max + 5) \<Longrightarrow>
       (aa, header_size ba) \<in> uint64_nat_rel \<Longrightarrow>
       (ab, length b) \<in> uint64_nat_rel \<Longrightarrow>
       length b + header_size ba \<le> uint64_max\<close>
  by (auto simp: uint64_max_def uint32_max_def header_size_def)



definition (in -)four_uint64_nat where
  [simp]: \<open>four_uint64_nat = (4 :: nat)\<close>
definition (in -)five_uint64_nat where
  [simp]: \<open>five_uint64_nat = (5 :: nat)\<close>
lemma (in-)
  four_uint64_nat_hnr[sepref_fr_rules]:
    \<open>(uncurry0 (return 4), uncurry0 (RETURN four_uint64_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close> and
  five_uint64_nat_hnr[sepref_fr_rules]:
    \<open>(uncurry0 (return 5), uncurry0 (RETURN five_uint64_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by (sepref_to_hoare; sep_auto simp: uint64_nat_rel_def br_def)+

sepref_definition (in -) header_size_fast_code
  is \<open>RETURN o header_size\<close>
  :: \<open>clause_ll_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  supply uint64_max_def[simp]
  unfolding header_size_def  five_uint64_nat_def[symmetric] four_uint64_nat_def[symmetric]
(*
  apply (subst nat_of_uint64_loc.nat_of_uint64_numeral_def[symmetric])
  apply (simp add: uint64_max_def IsaSAT_Clauses.nat_of_uint64_def)
  apply (subst nat_of_uint64_loc.nat_of_uint64_numeral_def[symmetric])
   apply (simp add: uint64_max_def IsaSAT_Clauses.nat_of_uint64_def)
  apply (rewrite at \<open>If _ \<hole>\<close> PR_CONST_def[symmetric])
  apply (rewrite at \<open>If _ _ \<hole>\<close> PR_CONST_def[symmetric])
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints*)
  by sepref

declare (in -)header_size_fast_code.refine[sepref_fr_rules]
(* End Move *)

definition append_and_length_fast_code_pre where
  \<open>append_and_length_fast_code_pre \<equiv> \<lambda>((b, C), N). length C \<le> uint32_max+2 \<and> length C \<ge> 2 \<and>
          length N + length C + 5 \<le> uint64_max\<close>

sepref_definition (in -)append_and_length_fast_code
  is \<open>uncurry2 fm_add_new_fast\<close>
  :: \<open>[append_and_length_fast_code_pre]\<^sub>a
     bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a (arena_assn)\<^sup>d \<rightarrow>
       arena_assn *a uint64_nat_assn\<close>
  supply [[goals_limit=1]] le_uint32_max_le_uint64_max[intro] append_and_length_code_fast[intro]
    header_size_def[simp]
  unfolding fm_add_new_def AStatus_IRRED_def[symmetric] append_and_length_fast_code_pre_def
   AStatus_LEARNED_def[symmetric] AStatus_LEARNED2_def[symmetric]
   AStatus_IRRED2_def[symmetric]
   two_uint64_nat_def[symmetric] fm_add_new_fast_def
   apply (rewrite in \<open>let _ = _ - _ in _\<close> length_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ in _\<close> length_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ in let _ = _ in let _ = \<hole> in _\<close> uint32_of_uint64_conv_def[symmetric])
  apply (rewrite in \<open>_ < length _\<close> length_uint64_nat_def[symmetric])
  by sepref

declare append_and_length_fast_code.refine[sepref_fr_rules]


lemma fm_add_new_alt_def:
 \<open>fm_add_new b C N = do {
      let st = (if b then AStatus_IRRED else AStatus_LEARNED2);
      let l = length_uint64_nat N;
      let s = uint32_of_uint64_conv (length_uint64_nat C - two_uint64_nat);
      let N =
        (if is_short_clause C
          then (((N @ [st]) @ [AActivity zero_uint32_nat]) @ [ALBD s]) @
              [ASize s]
          else ((((N @ [APos zero_uint32_nat]) @ [st]) @
                [AActivity zero_uint32_nat]) @
                [ALBD s]) @
              [ASize s]);
      (i, N) \<leftarrow>
        WHILE\<^sub>T (\<lambda>(i, N). i < length_uint64_nat C)
          (\<lambda>(i, N). do {
                _ \<leftarrow> ASSERT (i < length C);
                RETURN (i + one_uint64_nat, N @ [ALit (C ! i)])
              })
          (zero_uint64_nat, N);
      RETURN (N, l + header_size C)
    }\<close>
  unfolding fm_add_new_def Let_def AStatus_LEARNED2_def AStatus_IRRED2_def
     AStatus_LEARNED_def AStatus_IRRED_def
  by auto

definition fmap_swap_ll_u64 where
  [simp]: \<open>fmap_swap_ll_u64 = fmap_swap_ll\<close>

sepref_definition fmap_swap_ll_u64_clss
  is \<open>uncurry3 (RETURN oooo (\<lambda>(N, xs) i j k. (swap_ll N i j k, xs)))\<close>
  ::\<open>[\<lambda>((((xs, _), k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k]\<^sub>a
     (isasat_clauses_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)  \<rightarrow>
           isasat_clauses_assn\<close>
  by sepref

sepref_definition fmap_rll_u_clss
  is \<open>uncurry2 (RETURN ooo (\<lambda>(N, _) i. Array_List_Array.nth_rll N i))\<close>
  :: \<open>[\<lambda>(((l, _), i), j). i < length l \<and> j < length_rll l i]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>
        unat_lit_assn\<close>
  by sepref

sepref_definition fmap_rll_u32_clss
  is \<open>uncurry2 (RETURN ooo (\<lambda>(N, _) i. Array_List_Array.nth_rll N i))\<close>
  :: \<open>[\<lambda>(((l, _), i), j). i < length l \<and> j < length_rll l i]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>
        unat_lit_assn\<close>
  supply length_rll_def[simp]
  by sepref

sepref_definition (in -) swap_lits_fast_code
  is \<open>uncurry3 isa_arena_swap\<close>
  :: \<open>[\<lambda>(((_, _), _), N). length N \<le> uint64_max]\<^sub>a
      uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>
         arl_assn uint32_assn\<close>
  unfolding isa_arena_swap_def
  by sepref

declare swap_lits_fast_code.refine[sepref_fr_rules]

lemma slice_Suc_nth:
  \<open>a < b \<Longrightarrow> a < length xs \<Longrightarrow> Suc a < b \<Longrightarrow> Misc.slice a b xs = xs ! a # Misc.slice (Suc a) b xs\<close>
  by (metis Cons_nth_drop_Suc Misc.slice_def Suc_diff_Suc take_Suc_Cons)

lemma swap_lits_refine[sepref_fr_rules]:
  \<open>(uncurry3 swap_lits_fast_code, uncurry3 (RETURN oooo swap_lits))
  \<in> [\<lambda>(((C, i), j), arena). swap_lits_pre C i j arena \<and> length arena \<le> uint64_max]\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using swap_lits_fast_code.refine[FCOMP isa_arena_swap]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp)

definition fm_mv_clause_to_new_arena where
 \<open>fm_mv_clause_to_new_arena C old_arena new_arena = do {
    ASSERT(arena_is_valid_clause_idx old_arena C);
    let st = C - (if nat_of_uint64_conv (arena_length old_arena C) \<le> 4 then 4 else 5);
    let en = C + nat_of_uint64_conv (arena_length old_arena C);
    (i, new_arena) \<leftarrow>
        WHILE\<^sub>T (\<lambda>(i, new_arena). i < en)
          (\<lambda>(i, new_arena). do {
              ASSERT (i < length old_arena);
              RETURN (i + 1, new_arena @ [old_arena ! i])
          })
          (st, new_arena);
      RETURN (new_arena)
  }\<close>

sepref_register fm_mv_clause_to_new_arena

sepref_definition fm_mv_clause_to_new_arena_code
  is \<open>uncurry2 fm_mv_clause_to_new_arena\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow>\<^sub>a arena_assn\<close>
  supply [[goals_limit=1]]
  unfolding fm_mv_clause_to_new_arena_def
  by sepref

declare fm_mv_clause_to_new_arena_code.refine[sepref_fr_rules]

lemma valid_arena_append_clause_slice:
  assumes
    \<open>valid_arena old_arena N vd\<close> and
    \<open>valid_arena new_arena N' vd'\<close> and
    \<open>C \<in># dom_m N\<close>
  shows \<open>valid_arena (new_arena @ clause_slice old_arena N C)
    (fmupd (length new_arena + header_size (N \<propto> C)) (N \<propto> C, irred N C) N')
    (insert (length new_arena + header_size (N \<propto> C)) vd')\<close>
proof -
  define pos st lbd act used where
    \<open>pos = (if is_long_clause (N \<propto> C) then arena_pos old_arena C - 2 else 0)\<close> and
    \<open>st = arena_status old_arena C\<close> and
    \<open>lbd = arena_lbd old_arena C\<close> and
    \<open>act = arena_act old_arena C\<close> and
    \<open>used = arena_used old_arena C\<close>
  have \<open>2 \<le> length (N \<propto> C)\<close>
    unfolding st_def used_def act_def lbd_def
      append_clause_skeleton_def arena_status_def
      xarena_status_def arena_used_def
      arena_act_def xarena_used_def
      xarena_act_def
      arena_lbd_def xarena_lbd_def
         unfolding st_def used_def act_def lbd_def
      append_clause_skeleton_def arena_status_def
      xarena_status_def arena_used_def
      arena_act_def xarena_used_def
      xarena_act_def pos_def arena_pos_def
      xarena_pos_def
      arena_lbd_def xarena_lbd_def
    using arena_lifting[OF assms(1,3)]
    by (auto simp: is_Status_def is_Pos_def is_Size_def is_LBD_def
      is_Act_def)
  have
    45: \<open>4 = (Suc (Suc (Suc (Suc 0))))\<close>
     \<open>5 = Suc (Suc (Suc (Suc (Suc 0))))\<close>
    by auto
  have sl: \<open>clause_slice old_arena N C =
     (if is_long_clause (N \<propto> C) then [APos pos]
     else []) @
     [AStatus st used, AActivity act, ALBD lbd, ASize (length (N \<propto> C) - 2)] @
     map ALit (N \<propto> C) \<close>
    unfolding st_def used_def act_def lbd_def
      append_clause_skeleton_def arena_status_def
      xarena_status_def arena_used_def
      arena_act_def xarena_used_def
      xarena_act_def pos_def arena_pos_def
      xarena_pos_def
      arena_lbd_def xarena_lbd_def
      arena_length_def xarena_length_def
    using arena_lifting[OF assms(1,3)]
    by (auto simp: is_Status_def is_Pos_def is_Size_def is_LBD_def
      is_Act_def header_size_def 45
      slice_Suc_nth[of \<open>C - Suc (Suc (Suc (Suc (Suc 0))))\<close>]
      slice_Suc_nth[of \<open>C - Suc (Suc (Suc (Suc 0)))\<close>]
      slice_Suc_nth[of \<open>C - Suc (Suc (Suc 0))\<close>]
      slice_Suc_nth[of \<open>C - Suc (Suc 0)\<close>]
      slice_Suc_nth[of \<open>C - Suc 0\<close>]
      SHIFTS_alt_def arena_length_def
      arena_pos_def xarena_pos_def
      arena_status_def xarena_status_def)

  have \<open>2 \<le> length (N \<propto> C)\<close> and
    \<open>pos \<le> length (N \<propto> C) - 2\<close> and
    \<open>st = IRRED \<longleftrightarrow> irred N C\<close> and
    \<open>st \<noteq> DELETED\<close>
    unfolding st_def used_def act_def lbd_def pos_def
      append_clause_skeleton_def st_def
    using arena_lifting[OF assms(1,3)]
    by (cases \<open>is_short_clause (N \<propto> C)\<close>;
      auto split: arena_el.splits if_splits
        simp: header_size_def arena_pos_def; fail)+

  then have \<open>valid_arena (append_clause_skeleton pos st used act lbd (N \<propto> C) new_arena)
    (fmupd (length new_arena + header_size (N \<propto> C)) (N \<propto> C, irred N C) N')
    (insert (length new_arena + header_size (N \<propto> C)) vd')\<close>
    apply -
    by (rule valid_arena_append_clause_skeleton[OF assms(2), of \<open>N \<propto> C\<close> _ st
      pos used act lbd]) auto
  moreover have
    \<open>append_clause_skeleton pos st used act lbd (N \<propto> C) new_arena =
      new_arena @ clause_slice old_arena N C\<close>
    by (auto simp: append_clause_skeleton_def sl)
  ultimately show ?thesis
    by auto
qed

lemma fm_mv_clause_to_new_arena:
  assumes \<open>valid_arena old_arena N vd\<close> and
    \<open>valid_arena new_arena N' vd'\<close> and
    \<open>C \<in># dom_m N\<close>
  shows \<open>fm_mv_clause_to_new_arena C old_arena new_arena \<le>
    SPEC(\<lambda>new_arena'.
      new_arena' = new_arena @ clause_slice old_arena N C \<and> 
      valid_arena (new_arena @ clause_slice old_arena N C)
        (fmupd (length new_arena + header_size (N \<propto> C)) (N \<propto> C, irred N C) N')
        (insert (length new_arena + header_size (N \<propto> C)) vd'))\<close>
proof -
  define st and en where
    \<open>st = C - (if arena_length old_arena C \<le> 4 then 4 else 5)\<close> and
    \<open>en = C + arena_length old_arena C\<close>
  have st:
    \<open>st = C - header_size (N \<propto> C)\<close>
    using assms
    unfolding st_def
    by (auto simp: st_def header_size_def
        arena_lifting)
  show ?thesis
    using assms
    unfolding fm_mv_clause_to_new_arena_def st_def[symmetric]
      en_def[symmetric] Let_def nat_of_uint64_conv_def
    apply (refine_vcg
     WHILET_rule[where R = \<open>measure (\<lambda>(i, N). en - i)\<close> and
       I = \<open>\<lambda>(i, new_arena'). i \<le> C + length (N\<propto>C) \<and> i \<ge> st \<and>
         new_arena' = new_arena @
	   Misc.slice (C - header_size (N\<propto>C)) i old_arena\<close>])
    subgoal
      unfolding arena_is_valid_clause_idx_def
      by auto
    subgoal
      by auto
    subgoal
      using arena_lifting[OF assms(1,3)]
      by (auto simp: st)
    subgoal
      by (auto simp: st arena_lifting)
    subgoal
      using arena_lifting[OF assms(1,3)]
      by (auto simp: st en_def)
    subgoal
      using arena_lifting[OF assms(1,3)]
      by (auto simp: st en_def)
    subgoal
      using arena_lifting[OF assms(1,3)]
      by (auto simp: st en_def)
    subgoal
      using arena_lifting[OF assms(1,3)]
      by (auto simp: st)
    subgoal
      by (auto simp: st en_def arena_lifting[OF assms(1,3)]
        slice_append_nth)
    subgoal by auto
    subgoal by (auto simp: en_def arena_lifting)
    subgoal
      using valid_arena_append_clause_slice[OF assms]
      by auto
    done
qed

end
