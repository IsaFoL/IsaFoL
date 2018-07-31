theory IsaSAT_Clauses
imports  Watched_Literals.Watched_Literals_Watch_List_Code_Common IsaSAT_Arena
begin

(* TODO This file should probably be merge with IsaSAT_Arena*)

subsubsection \<open>Representation of Clauses\<close>

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

definition clauses_ll_assn
   :: \<open>_ \<Rightarrow> nat clauses_l \<Rightarrow> uint32 array_list \<Rightarrow> assn\<close>
where
  \<open>clauses_ll_assn vdom = hr_comp arena_assn (clauses_l_fmat vdom)\<close>

definition fmap_rll :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal" where
  [simp]: \<open>fmap_rll l i j = l \<propto> i ! j\<close>

definition fmap_rll_u :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal" where
  [simp]: \<open>fmap_rll_u  = fmap_rll\<close>
(* 
lemma nth_clauses_rll:
  \<open>(uncurry2 (RETURN ooo (\<lambda>(N, _) i. Array_List_Array.nth_rll N i)), uncurry2 (RETURN ooo IsaSAT_Clauses.fmap_rll))
    \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>f
      \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def fmap_rll_def nth_rll_def) *)

lemma nth_raa_hnr':
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 (\<lambda>(N, _) j k. nth_raa N j k), uncurry2 (RETURN \<circ>\<circ>\<circ> (\<lambda>(N, _) i. Array_List_Array.nth_rll N i))) \<in>
       [\<lambda>(((l, _),i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R) *a GG)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  using assms
  by sepref_to_hoare  sep_auto
(* 
lemma fmap_rll_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (\<lambda>(N, _) i. nth_raa N i), uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>?c
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
         (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
        (\<lambda>_ (((l, _), i), j). i < length l \<and> j < length_rll l i)
         (\<lambda>_. True)]\<^sub>a
       hrp_comp (isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF nth_raa_hnr' nth_clauses_rll, of unat_lit_assn]) simp
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

term arena_update_status
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
  \<open>fmap_length_rll_u l i = length_u (l \<propto> i)\<close>

declare fmap_length_rll_u_def[symmetric, isasat_codegen]

(*TODO rename length_rll_n_uint32*)
(* lemma fmap_length_rll_u:
  \<open>(uncurry (RETURN oo (\<lambda>(N, _) i. length_rll_n_uint32 N i)), uncurry (RETURN oo fmap_length_rll_u))
    \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>f \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def fmap_length_rll_u_def length_rll_def) *)

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
  \<open>fmap_length_rll_u64 l i = length_u (l \<propto> i)\<close>


declare fmap_length_rll_u_def[symmetric, isasat_codegen]

(*TODO rename length_rll_n_uint32*)
(* lemma fmap_length_rll_u64:
  \<open>(uncurry (RETURN oo (\<lambda>(N, _) i. length_rll_n_uint64 N i)), uncurry (RETURN oo fmap_length_rll_u64))
    \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>f \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def fmap_length_rll_u64_def length_rll_def) *)

definition length_raa_u32_u64 :: \<open>'a::heap arrayO_raa \<Rightarrow> uint32 \<Rightarrow> uint64 Heap\<close> where
  \<open>length_raa_u32_u64 xs i = do {
     x \<leftarrow> arl_get_u xs i;
    length_u64_code x}\<close>

lemma length_raa_u32_u64_hnr[sepref_fr_rules]:
  shows \<open>(uncurry length_raa_u32_u64, uncurry (RETURN \<circ>\<circ> length_rll_n_uint64)) \<in>
     [\<lambda>(xs, i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
proof -
   have 1: \<open>a * b * c = c * a * b\<close> for a b c :: assn
    by (auto simp: ac_simps)
  have H: \<open><arlO_assn_except (array_assn R) [nat_of_uint32 bi] a (aa, ba)
        (\<lambda>r'. array_assn R (a ! nat_of_uint32 bi) x *
              \<up> (x = r' ! nat_of_uint32 bi))>
      Array.len x <\<lambda>r. \<up>(r = length (a ! nat_of_uint32 bi)) *
          arlO_assn (array_assn R) a (aa, ba)>\<close>
    if
      \<open>nat_of_uint32 bi < length a\<close> and
      \<open>length (a ! nat_of_uint32 bi) \<le> uint64_max\<close>
    for bi :: \<open>uint32\<close> and a :: \<open>'b list list\<close> and aa :: \<open>'a array array\<close> and ba :: \<open>nat\<close> and
      x :: \<open>'a array\<close>
  proof -
    show ?thesis
      using that apply -
      apply (subst arlO_assn_except_array0_index[symmetric, OF that(1)])
      by (sep_auto simp: array_assn_def arl_get_def hr_comp_def is_array_def
          list_rel_imp_same_length arlO_assn_except_def)
  qed
  show ?thesis
  apply sepref_to_hoare
  apply (sep_auto simp: uint64_nat_rel_def br_def length_rll_def
      nat_of_uint64_uint64_of_nat_id length_raa_u32_u64_def arl_get_u_def arl_get'_def
      uint32_nat_rel_def nat_of_uint32_code[symmetric] length_u64_code_def
      intro!:)+
     apply (rule H; assumption)
    apply (sep_auto simp: array_assn_def arl_get_def nat_of_uint64_uint64_of_nat_id)
    done
qed


definition length_raa_u64_u64 :: \<open>'a::heap arrayO_raa \<Rightarrow> uint64 \<Rightarrow> uint64 Heap\<close> where
  \<open>length_raa_u64_u64 xs i = do {
     x \<leftarrow> arl_get_u64 xs i;
    length_u64_code x}\<close>

lemma length_raa_u64_u64_hnr[sepref_fr_rules]:
  shows \<open>(uncurry length_raa_u64_u64, uncurry (RETURN \<circ>\<circ> length_rll_n_uint64)) \<in>
     [\<lambda>(xs, i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
proof -
   have 1: \<open>a * b * c = c * a * b\<close> for a b c :: assn
    by (auto simp: ac_simps)
  have H: \<open><arlO_assn_except (array_assn R) [nat_of_uint64 bi] a (aa, ba)
        (\<lambda>r'. array_assn R (a ! nat_of_uint64 bi) x *
              \<up> (x = r' ! nat_of_uint64 bi))>
      Array.len x <\<lambda>r. \<up>(r = length (a ! nat_of_uint64 bi)) *
          arlO_assn (array_assn R) a (aa, ba)>\<close>
    if
      \<open>nat_of_uint64 bi < length a\<close> and
      \<open>length (a ! nat_of_uint64 bi) \<le> uint64_max\<close>
    for bi :: \<open>uint64\<close> and a :: \<open>'b list list\<close> and aa :: \<open>'a array array\<close> and ba :: \<open>nat\<close> and
      x :: \<open>'a array\<close>
  proof -
    show ?thesis
      using that apply -
      apply (subst arlO_assn_except_array0_index[symmetric, OF that(1)])
      by (sep_auto simp: array_assn_def arl_get_def hr_comp_def is_array_def
          list_rel_imp_same_length arlO_assn_except_def)
  qed
  show ?thesis
  apply sepref_to_hoare
  apply (sep_auto simp: uint64_nat_rel_def br_def length_rll_def
      nat_of_uint64_uint64_of_nat_id length_raa_u32_u64_def arl_get_u64_def arl_get'_def
      uint32_nat_rel_def nat_of_uint32_code[symmetric] length_u64_code_def length_raa_u64_u64_def
      nat_of_uint64_code[symmetric]
      intro!:)+
     apply (rule H; assumption)
    apply (sep_auto simp: array_assn_def arl_get_def nat_of_uint64_uint64_of_nat_id)
    done
qed

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


definition length_raa_u32 :: \<open>'a::heap arrayO_raa \<Rightarrow> uint32 \<Rightarrow> nat Heap\<close> where
  \<open>length_raa_u32 xs i = do {
     x \<leftarrow> arl_get_u xs i;
    Array.len x}\<close>

lemma length_raa_u32_rule[sep_heap_rules]:
  \<open>b < length xs \<Longrightarrow> (b', b) \<in> uint32_nat_rel \<Longrightarrow> <arlO_assn (array_assn R) xs a> length_raa_u32 a b'
   <\<lambda>r. arlO_assn (array_assn R) xs a * \<up> (r = length_rll xs b)>\<^sub>t\<close>
  supply arrayO_raa_nth_rule[sep_heap_rules]
  unfolding length_raa_u32_def arl_get_u_def arl_get'_def uint32_nat_rel_def br_def
  apply (cases a)
  apply (sep_auto simp: nat_of_uint32_code[symmetric])
  apply (sep_auto simp: arlO_assn_except_def arl_length_def array_assn_def
      eq_commute[of \<open>(_, _)\<close>] is_array_def hr_comp_def length_rll_def
      dest: list_all2_lengthD)
   apply (sep_auto simp: arlO_assn_except_def arl_length_def arl_assn_def
      hr_comp_def[abs_def] arl_get'_def
      eq_commute[of \<open>(_, _)\<close>] is_array_list_def hr_comp_def length_rll_def list_rel_def
      dest: list_all2_lengthD)[]
  unfolding arlO_assn_def[symmetric] arl_assn_def[symmetric]
  apply (subst arlO_assn_except_array0_index[symmetric, of b])
   apply simp
  unfolding arlO_assn_except_def arl_assn_def hr_comp_def is_array_def
  apply sep_auto
  done

lemma length_raa_u32_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_u32, uncurry (RETURN \<circ>\<circ> length_rll)) \<in>
     [\<lambda>(xs, i). i < length xs]\<^sub>a (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare sep_auto


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
    let st = (if b then AStatus INIT else AStatus LEARNED);
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
  unfolding append_clause_def header_size_Suc_def
  by (auto simp: nth_Cons nth_append)

lemma fm_add_new_append_clause:
  \<open>fm_add_new b C N \<le> RETURN (append_clause b C N, length N + header_size C)\<close>
  unfolding fm_add_new_def
  apply (rewrite at \<open>let _ = length _ in _\<close> Let_def)
  apply (refine_vcg WHILET_rule[where R = \<open>measure (\<lambda>(i, _). Suc (length C) - i)\<close> and
    I = \<open>\<lambda>(i, N'). N' = take (length N + header_size C + i) (append_clause b C N) \<and>
      i \<le> length C\<close>])
  subgoal by auto
  subgoal by (auto simp: append_clause_def header_size_def)
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

(* definition append_and_length
   :: \<open>bool \<Rightarrow> 'v clause_l \<Rightarrow> 'v clause_l list \<times> clause_annots \<Rightarrow> ('v clause_l list \<times> clause_annots) \<times> nat\<close>
where
\<open>append_and_length b C = (\<lambda>(N, cs).
     let k = length N in
     let b' = (if b then INIT else LEARNED, 0, 0) in
       ((op_list_append N C, op_list_append cs b'), k))\<close> *)
(* 
lemma append_and_length_fm_add_new:
  \<open>(uncurry2 (RETURN ooo append_and_length), uncurry2 fm_add_new)
     \<in> bool_rel \<times>\<^sub>f (\<langle>Id\<rangle>list_rel) \<times>\<^sub>f (clauses_l_fmat) \<rightarrow>\<^sub>f \<langle>clauses_l_fmat \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: fm_add_new_at_position_def list_fmap_rel_def Let_def
      max_def nth_append append_and_length_def fm_add_new_def get_fresh_index_def
      RETURN_RES_refine_iff RES_RETURN_RES
      intro!: RETURN_SPEC_refine
      dest: multi_member_split
      split: if_splits)
  apply force
  apply force
  apply force
   apply force
   apply force
  apply (case_tac \<open>set_mset (dom_m bc) = {}\<close>)
  apply force
  apply force
  apply (case_tac \<open>set_mset (dom_m bc) = {}\<close>)
  apply force
   apply force
  apply (case_tac \<open>set_mset (dom_m bc) = {}\<close>)
   apply force
  apply (subst extra_clause_information_upd_irrel)
    apply force
  apply auto
  apply (case_tac \<open>set_mset (dom_m bc) = {}\<close>)
   apply force
    apply force
  apply (subst extra_clause_information_upd_irrel)
  apply auto
  done *)

definition AStatus_INIT where
  \<open>AStatus_INIT = AStatus INIT\<close>

lemma AStatus_INIT [sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN AStatus_INIT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_INIT_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
    status_rel_def)

definition AStatus_LEARNED where
  \<open>AStatus_LEARNED = AStatus LEARNED\<close>

lemma AStatus_LEARNED [sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN AStatus_LEARNED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_LEARNED_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
    status_rel_def)

sepref_definition is_short_clause_code
  is \<open>RETURN o is_short_clause\<close>
  :: \<open>clause_ll_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding is_short_clause_def
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


lemma le_uint32_max_le_uint64_max: \<open>a \<le> uint32_max + 2 \<Longrightarrow> a \<le> uint64_max\<close>
  by (auto simp: uint32_max_def uint64_max_def)

lemma nat_of_uint64_ge_minus:
  \<open>ai >= bi \<Longrightarrow>
       nat_of_uint64 (ai - bi) = nat_of_uint64 ai - nat_of_uint64 bi\<close>
  apply transfer
  unfolding unat_def
  by (subst uint_sub_lem[THEN iffD1])
    (auto simp: unat_def uint_nonnegative nat_diff_distrib word_le_def[symmetric] intro: leI)

lemma minus_uint64_nat_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (-)), uncurry (RETURN oo (-))) \<in> 
    [\<lambda>(a, b). a \<ge> b]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_ge_minus
   nat_of_uint64_le_iff)

definition uint32_of_uint64 where
  \<open>uint32_of_uint64 n = uint32_of_nat (nat_of_uint64 n)\<close>

definition uint32_of_uint64_rel where
  [simp]: \<open>uint32_of_uint64_rel n = n\<close>

lemma uint32_of_uint64_rel_hnr[sepref_fr_rules]:
  \<open>(return o uint32_of_uint64, RETURN o uint32_of_uint64_rel) \<in>
     [\<lambda>a. a \<le> uint32_max]\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_of_uint64_def uint32_nat_rel_def br_def nat_of_uint64_le_iff
      nat_of_uint32_uint32_of_nat_id uint64_nat_rel_def)

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
  unfolding fm_add_new_def AStatus_INIT_def[symmetric]
   AStatus_LEARNED_def[symmetric]
   two_uint64_nat_def[symmetric]
   apply (rewrite in \<open>let _ = _ - _ in _\<close> length_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ in let _ = _ in let _ = \<hole> in _\<close> uint32_of_uint64_rel_def[symmetric])
   apply (rewrite in \<open>_ < length _\<close> length_uint64_nat_def[symmetric])
  by sepref

declare append_and_length_code.refine[sepref_fr_rules]

(* 
lemma fm_add_new_hnr[sepref_fr_rules]:
  \<open>(uncurry2 append_and_length_code, uncurry2 fm_add_new)
    \<in> bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>d \<rightarrow>\<^sub>a clauses_ll_assn *a nat_assn\<close>
  using append_and_length_code.refine[FCOMP append_and_length_fm_add_new]
  unfolding clauses_ll_assn_def by simp *)

(* 
definition get_fresh_index_packed :: \<open>'v clauses_l \<Rightarrow> nat nres\<close> where
\<open>get_fresh_index_packed N = SPEC(\<lambda>i. i > 0 \<and> i \<notin># dom_m N \<and>
    (\<forall>j < i. j > 0 \<longrightarrow> j \<in># dom_m N))\<close>

lemma (in -)get_fresh_index_packed_alt_def: 
  assumes \<open>packed N\<close>
  shows \<open>get_fresh_index_packed N = SPEC (\<lambda>i. i = Suc (Max_dom N))\<close>
proof -
  have [iff]: \<open>j \<in># dom_m N \<longleftrightarrow> j > 0 \<and> j \<le> Max_dom N\<close> for j
    using assms in_multiset_ge_Max[of j \<open>dom_m N\<close>]
    unfolding packed_def
    by (auto simp: get_fresh_index_packed_def packed_def
        split: if_splits)
  have \<open> \<forall>j<x. 0 < j \<longrightarrow> j \<le> Max_dom N \<Longrightarrow>
         \<not> x \<le> Max_dom N \<Longrightarrow> x = Suc (Max_dom N)\<close> for x
    by (cases \<open>x > Suc (Max_dom N)\<close>)  auto
  then show ?thesis
    by (auto simp: get_fresh_index_packed_def split: if_splits
      dest: multi_member_split in_multiset_ge_Max)
qed

definition fm_add_new_packed where
 \<open>fm_add_new_packed b C N = do {
    i \<leftarrow> get_fresh_index_packed N;
    let N = fmupd i (C, b) N;
    RETURN (N, i)
  }\<close> *)

(* lemma append_and_length_fm_add_new_packed:
  \<open>(uncurry2 (RETURN ooo append_and_length), uncurry2 fm_add_new_packed)
     \<in> [\<lambda>((b, C), N). packed N]\<^sub>f
       bool_rel \<times>\<^sub>f (\<langle>Id\<rangle>list_rel) \<times>\<^sub>f (\<langle>Id\<rangle>clauses_l_fmat) \<rightarrow> \<langle>\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (force simp:  fm_add_new_at_position_def list_fmap_rel_def Let_def
      max_def nth_append append_and_length_def fm_add_new_packed_def get_fresh_index_packed_def
      RETURN_RES_refine_iff RES_RETURN_RES (* packed_def *) Max_n_upt Max_insert_Max_dom_into_packed
      Max_dom_alt_def[symmetric] Max_dom_fmupd_irrel
      intro!: RETURN_SPEC_refine
      intro: packed_in_dom_mI) *)
(* 
lemma fm_add_new_packed_hnr[sepref_fr_rules]:
  \<open>(uncurry2 append_and_length_code, uncurry2 fm_add_new_packed)
    \<in> [\<lambda>(_, N). packed N]\<^sub>a bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>d \<rightarrow> clauses_ll_assn *a nat_assn\<close>
  using append_and_length_code.refine[FCOMP append_and_length_fm_add_new_packed]
  unfolding clauses_ll_assn_def
  by simp *)

(* TODO Proper setup + Move *)
definition length_arlO_u where
  \<open>length_arlO_u xs = do {
      n \<leftarrow> length_ra xs;
      return (uint32_of_nat n)}\<close>

lemma length_arlO_u[sepref_fr_rules]:
  \<open>(length_arlO_u, RETURN o length_u) \<in> [\<lambda>xs. length xs \<le> uint32_max]\<^sub>a (arlO_assn R)\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: length_arlO_u_def arl_length_def uint32_nat_rel_def
      br_def nat_of_uint32_uint32_of_nat_id)

definition arl_length_u64_code where
\<open>arl_length_u64_code C = do {
  n \<leftarrow> arl_length C;
  return (uint64_of_nat n)
}\<close>

lemma arl_length_u64_code[sepref_fr_rules]:
  \<open>(arl_length_u64_code, RETURN o length_uint64_nat) \<in>
     [\<lambda>xs. length xs \<le> uint64_max]\<^sub>a (arl_assn R)\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: arl_length_u64_code_def arl_length_def uint64_nat_rel_def
      br_def nat_of_uint64_uint64_of_nat_id arl_assn_def hr_comp_def[abs_def]
      is_array_list_def dest: list_rel_imp_same_length)
(* End Move *)

definition convert_to_uint32 :: \<open>nat \<Rightarrow> nat\<close> where
  [simp]: \<open>convert_to_uint32 = id\<close>

lemma convert_to_uint32_hnr[sepref_fr_rules]:
  \<open>(return o uint32_of_nat, RETURN o convert_to_uint32)
    \<in> [\<lambda>n. n \<le> uint32_max]\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def uint32_max_def nat_of_uint32_uint32_of_nat_id)
(* 
definition append_and_length_u32
  :: \<open>bool \<Rightarrow> 'v clause_l \<Rightarrow> 'v clause_l list \<times> clause_annots \<Rightarrow>
    (('v clause_l list \<times> clause_annots) \<times> nat) nres\<close>
  where
\<open>append_and_length_u32 b C = (\<lambda>(N, ex). do {
    ASSERT(length N \<le> uint32_max);
    let k = length N;
    let b' = (if b then INIT else LEARNED, 0, 0);
    RETURN ((op_list_append N C, op_list_append ex b'), convert_to_uint32 k)})\<close> *)
(* 
lemma append_and_length_u32_fm_add_new:
  \<open>(uncurry2 append_and_length_u32, uncurry2 fm_add_new)
     \<in> [\<lambda>((b, C), N). Max (insert 0 (set_mset (dom_m N))) < uint32_max]\<^sub>f
     bool_rel \<times>\<^sub>f (\<langle>Id\<rangle>list_rel) \<times>\<^sub>f (\<langle>Id\<rangle>clauses_l_fmat) \<rightarrow> \<langle>\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
(* TODO Tune proof *)
  apply (intro frefI nres_relI)
  apply (auto simp: fm_add_new_at_position_def list_fmap_rel_def Let_def
      max_def nth_append append_and_length_u32_def fm_add_new_def get_fresh_index_def
      RETURN_RES_refine_iff RES_RETURN_RES
      intro!: RETURN_SPEC_refine ASSERT_refine_left
      dest: multi_member_split
      split: if_splits)
                 apply (metis Max_in_lits Suc_leI empty_iff insert_iff set_mset_add_mset_insert
      set_mset_empty)
                apply blast
               apply blast
              apply force
             apply fastforce
             apply fastforce
            apply (case_tac \<open>set_mset (dom_m bc) = {}\<close>)
             apply force
            apply force
           apply fastforce
          apply (subst extra_clause_information_upd_irrel)
            apply force
           apply force
          apply force
         apply (metis Max_in_lits Suc_leI empty_iff insert_iff set_mset_add_mset_insert
      set_mset_empty)
        apply blast
       apply blast
      apply force
     apply fastforce
     apply fastforce
    apply (case_tac \<open>set_mset (dom_m bc) = {}\<close>)
     apply force
    apply force
   apply fastforce
  apply (subst extra_clause_information_upd_irrel)
    apply force
   apply force
  apply force
  done *)

lemma fm_add_new_alt_def:
 \<open>fm_add_new b C N = do {
      let st = (if b then AStatus_INIT else AStatus_LEARNED);
      let l = length_uint64_nat N;
      let s = uint32_of_uint64_rel (length_uint64_nat C - two_uint64_nat);
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
  unfolding fm_add_new_def Let_def AStatus_LEARNED_def AStatus_INIT_def
  by auto
(* 
sepref_definition append_and_length_u32_code
  is \<open>uncurry2 (fm_add_new)\<close>
  :: \<open>[\<lambda>((b, C), N). length C \<le> uint32_max+1 \<and> length C \<ge> 2 \<and>
        length N \<le> uint64_max]\<^sub>a 
     bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a arena_assn\<^sup>d \<rightarrow>
      arena_assn *a uint64_nat_assn\<close>
  supply le_uint32_max_le_uint64_max[simp]
  unfolding fm_add_new_alt_def
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold apply (auto simp: )[]
  by sepref *)

definition fm_add_new_fast where
  [simp, symmetric]: \<open>fm_add_new_fast = fm_add_new\<close>
(* 
lemma fm_add_new_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 append_and_length_u32_code, uncurry2 fm_add_new_fast)
    \<in> [\<lambda>((b, C), N). length C \<le> uint32_max+1 \<and> length C \<ge> 2 \<and>
        length N \<le> uint64_max]\<^sub>a 
       bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn *a uint64_nat_assn\<close>
  using append_and_length_u32_code.refine by simp *)

(* 
lemma append_and_length_u32_fm_add_new_packed:
  \<open>(uncurry2 append_and_length_u32, uncurry2 fm_add_new_packed)
     \<in> [\<lambda>((b, C), N). Max (insert 0 (set_mset (dom_m N))) < uint32_max \<and> packed N]\<^sub>f
     bool_rel \<times>\<^sub>f (\<langle>Id\<rangle>list_rel) \<times>\<^sub>f (\<langle>Id\<rangle>clauses_l_fmat) \<rightarrow> \<langle>\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: list_fmap_rel_def Let_def
       nth_append append_and_length_u32_def fm_add_new_packed_def get_fresh_index_packed_def
      RETURN_RES_refine_iff RES_RETURN_RES Max_dom_alt_def[symmetric] Max_dom_fmupd_irrel
      intro!: RETURN_SPEC_refine ASSERT_refine_left extra_clause_information_upd_irrel[THEN iffD2]
      dest: multi_member_split Max_dom_le
      intro: packed_in_dom_mI
      split: if_splits) (* slow ~ 25s *)
  apply (auto simp: list_fmap_rel_def Let_def
       nth_append append_and_length_u32_def fm_add_new_packed_def get_fresh_index_packed_def
      RETURN_RES_refine_iff RES_RETURN_RES Max_dom_alt_def[symmetric] Max_dom_fmupd_irrel
      intro!: RETURN_SPEC_refine ASSERT_refine_left
      dest: multi_member_split Max_dom_le
      intro: packed_in_dom_mI
      split: if_splits)
  done *)
(* 
definition fm_add_new_packed_fast where
  [simp, symmetric]: \<open>fm_add_new_packed_fast = fm_add_new_packed\<close>

lemma fm_add_new_packed_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 append_and_length_u32_code, uncurry2 fm_add_new_packed_fast)
    \<in> [\<lambda>(_, ba). (\<forall>a\<in>#dom_m ba. a < uint_max) \<and> packed ba]\<^sub>a
       bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>d \<rightarrow> clauses_ll_assn *a uint32_nat_assn\<close>
  using append_and_length_u32_code.refine[FCOMP append_and_length_u32_fm_add_new_packed]
  unfolding clauses_ll_assn_def by (simp add: uint32_max_def) *)

definition fmap_swap_ll_u64 where
  [simp]: \<open>fmap_swap_ll_u64 = fmap_swap_ll\<close>

sepref_definition fmap_swap_ll_u64_clss
  is \<open>uncurry3 (RETURN oooo (\<lambda>(N, xs) i j k. (swap_ll N i j k, xs)))\<close>
  ::\<open>[\<lambda>((((xs, _), k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k]\<^sub>a
     (isasat_clauses_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)  \<rightarrow>
           isasat_clauses_assn\<close>
  by sepref

(* lemma fmap_swap_ll_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry3 fmap_swap_ll_u64_clss, uncurry3 (RETURN oooo fmap_swap_ll_u64))
     \<in> [\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i)]\<^sub>a
     isasat_clauses_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> isasat_clauses_assn\<close>
   (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>?c \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
             (\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i))
             (\<lambda>_ ((((xs, _), k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k)
             (\<lambda>_. True)]\<^sub>a
          hrp_comp (isasat_clauses_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
          hr_comp isasat_clauses_assn (\<langle>Id\<rangle>clauses_l_fmat)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_swap_ll_u64_def
    by (rule hfref_compI_PRE_aux[OF fmap_swap_ll_u64_clss.refine swap_ll_fmap_swap_ll])
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
qed

sepref_definition fmap_swap_ll_i32_u64_clss
  is \<open>uncurry3 (RETURN oooo (\<lambda>(N, xs) i j k. (swap_ll N i j k, xs)))\<close>
  ::\<open>[\<lambda>((((xs, _), k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k]\<^sub>a
     (isasat_clauses_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)  \<rightarrow>
           isasat_clauses_assn\<close>
  by sepref

lemma fmap_swap_ll_i32_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry3 fmap_swap_ll_i32_u64_clss, uncurry3 (RETURN oooo fmap_swap_ll_u64))
     \<in> [\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> clauses_ll_assn\<close>
   (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>?c \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
             (\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i))
             (\<lambda>_ ((((xs, _), k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k)
             (\<lambda>_. True)]\<^sub>a
          hrp_comp (isasat_clauses_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
          hr_comp isasat_clauses_assn (\<langle>Id\<rangle>clauses_l_fmat)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_swap_ll_u64_def
    by (rule hfref_compI_PRE_aux[OF fmap_swap_ll_i32_u64_clss.refine swap_ll_fmap_swap_ll])
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

(* lemma
  fmap_rll_u_hnr[sepref_fr_rules]:
    \<open>(uncurry2 fmap_rll_u_clss, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is ?slow is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
  fmap_rll_i32_u_hnr[sepref_fr_rules]:
    \<open>(uncurry2 fmap_rll_u32_clss, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have H:
    \<open>?c
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
           (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
           (\<lambda>_ (((l, _), i), j). i < length l \<and> j < length_rll l i)
          (\<lambda>_. True)]\<^sub>a
       hrp_comp (isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
       hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_rll_u_def
    by (rule hfref_compI_PRE_aux[OF fmap_rll_u_clss.refine nth_clauses_rll])
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
    \<open>?cfast
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
           (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
           (\<lambda>_ (((l, _), i), j). i < length l \<and> j < length_rll l i)
          (\<lambda>_. True)]\<^sub>a
       hrp_comp (isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
       hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_rll_u_def
    by (rule hfref_compI_PRE_aux[OF fmap_rll_u32_clss.refine nth_clauses_rll])

  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def list_fmap_rel_def length_rll_def intro!: ext)
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?ffast\<close>
    by auto
  show ?fast
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im fmap_rll_u_def apply assumption
    using pre ..
qed


sepref_definition fmap_rll_u32_un_clss
  is \<open>uncurry2 (RETURN ooo (\<lambda>(N, _) i. Array_List_Array.nth_rll N i))\<close>
  :: \<open>[\<lambda>(((l, _), i), j). i < length l \<and> j < length (l!i)]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  by sepref


lemma fmap_rll_i32_hnr[sepref_fr_rules]:
  \<open>(uncurry2 fmap_rll_u32_un_clss, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>(uncurry2 fmap_rll_u32_un_clss, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll))
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
         (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
        (\<lambda>_ (((l, _), i), j). i < length l \<and> j < length (l!i))
         (\<lambda>_. True)]\<^sub>a
       hrp_comp (isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF fmap_rll_u32_un_clss.refine nth_clauses_rll])
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def list_fmap_rel_def length_rll_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep clauses_ll_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    by auto
  show ?thesis
    unfolding fmap_rll_u_def
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
qed

sepref_definition fmap_length_rll_u32_clss
  is \<open>uncurry (RETURN oo (\<lambda>(N, _) i. length_rll_n_uint32 N i))\<close>
  :: \<open>[(\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint32_max)]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref


lemma fmap_length_rll_i32_u_hnr[sepref_fr_rules]:
  \<open>(uncurry fmap_length_rll_u32_clss, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u))
     \<in> [\<lambda>(N, i). i \<in># dom_m N \<and> length (N \<propto> i) \<le> uint_max]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
   (is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>?c
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ ((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint_max)
            (\<lambda>_. True)]\<^sub>a
         hrp_comp (isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k) (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
         hr_comp uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF fmap_length_rll_u32_clss.refine fmap_length_rll_u])
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
qed

definition irred_clauses_l_fmat where
  \<open>irred_clauses_l_fmat = (\<lambda>(N, ex) i. do {
     ASSERT(i < length ex);
     RETURN (fst (ex ! i) = INIT)
    })\<close>

lemma irred_clauses_l_fmat:
  \<open>(uncurry irred_clauses_l_fmat, uncurry (RETURN oo irred)) \<in>
    [\<lambda>(N, i). i \<in># dom_m N]\<^sub>f \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: list_fmap_rel_def extra_clause_information.simps extra_clause_information_simps
      irred_clauses_l_fmat_def
      dest!: multi_member_split)

lemma clause_status_assn_eq[sepref_fr_rules]:
  \<open>(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in>
     clause_status_assn\<^sup>k *\<^sub>a clause_status_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare sep_auto

sepref_definition irred_clauses_l_fmat_fast
  is \<open>uncurry irred_clauses_l_fmat\<close>
  :: \<open>isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding irred_clauses_l_fmat_def
  by sepref

sepref_definition irred_clauses_l_fmat_slow
  is \<open>uncurry irred_clauses_l_fmat\<close>
  :: \<open>isasat_clauses_assn\<^sup>k *\<^sub>anat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding irred_clauses_l_fmat_def
  by sepref

lemma irred_hnr[sepref_fr_rules]:
   \<open>(uncurry irred_clauses_l_fmat_fast, uncurry (RETURN \<circ>\<circ> irred'))
      \<in> [\<lambda>(a, b). b \<in># dom_m a]\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using irred_clauses_l_fmat_fast.refine[FCOMP irred_clauses_l_fmat]
  unfolding clauses_ll_assn_def irred'_def
  .

lemma irred_slow_hnr[sepref_fr_rules]:
   \<open>(uncurry irred_clauses_l_fmat_slow, uncurry (RETURN \<circ>\<circ> irred'))
      \<in> [\<lambda>(a, b). b \<in># dom_m a]\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using irred_clauses_l_fmat_slow.refine[FCOMP irred_clauses_l_fmat]
  unfolding clauses_ll_assn_def irred'_def
  .

definition set_LBD where
  \<open>set_LBD i lbd N = N\<close>

definition set_LBD_fmap where
  \<open>set_LBD_fmap i lbd = (\<lambda>(N, ex). do {
     ASSERT(i < length ex);
     let (red, _, act) = ex!i;
     RETURN (N, ex[i := (red, lbd, act)])
   })\<close>

lemma set_LBD_fmap:
  \<open>(uncurry2 set_LBD_fmap, uncurry2 (RETURN ooo set_LBD)) \<in>
    [\<lambda>((i, lbd), N). i \<in># dom_m N]\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>Id\<rangle>clauses_l_fmat \<rightarrow> \<langle> \<langle>Id\<rangle>clauses_l_fmat\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto 5 5 simp: list_fmap_rel_def extra_clause_information.simps extra_clause_information_simps
      irred_clauses_l_fmat_def set_LBD_fmap_def set_LBD_def case_prod_beta
      dest: multi_member_split)

sepref_definition set_LBD_fmap_fast
  is \<open>uncurry2 set_LBD_fmap\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a isasat_clauses_assn\<^sup>d \<rightarrow>\<^sub>a isasat_clauses_assn\<close>
  unfolding set_LBD_fmap_def
  by sepref

sepref_definition set_LBD_fmap_slow
  is \<open>uncurry2 set_LBD_fmap\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a isasat_clauses_assn\<^sup>d \<rightarrow>\<^sub>a isasat_clauses_assn\<close>
  unfolding set_LBD_fmap_def
  by sepref

lemma set_LBD_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 set_LBD_fmap_fast, uncurry2 (RETURN \<circ>\<circ>\<circ> set_LBD))
    \<in> [\<lambda>((a, b), ba). a \<in># dom_m ba]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>d \<rightarrow>
     clauses_ll_assn\<close>
  using  set_LBD_fmap_fast.refine[FCOMP set_LBD_fmap] unfolding clauses_ll_assn_def .

lemma set_LBD_slow_hnr[sepref_fr_rules]:
  \<open>(uncurry2 set_LBD_fmap_slow, uncurry2 (RETURN \<circ>\<circ>\<circ> set_LBD))
    \<in> [\<lambda>((a, b), ba). a \<in># dom_m ba]\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>d \<rightarrow>
     clauses_ll_assn\<close>
  using set_LBD_fmap_slow.refine[FCOMP set_LBD_fmap] unfolding clauses_ll_assn_def .


definition increase_activity where
  \<open>increase_activity i lbd N = N\<close>

definition increase_activity_fmap where
  \<open>increase_activity_fmap i lbd = (\<lambda>(N, ex). do {
     ASSERT(i < length ex);
     let (red, lbd, act) = ex!i;
     RETURN (N, ex[i := (red, lbd, sum_mod_uint32_max act one_uint32_nat)])
   })\<close>

lemma increase_activity_fmap:
  \<open>(uncurry2 increase_activity_fmap, uncurry2 (RETURN ooo increase_activity)) \<in>
    [\<lambda>((i, lbd), N). i \<in># dom_m N]\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>Id\<rangle>clauses_l_fmat \<rightarrow> \<langle> \<langle>Id\<rangle>clauses_l_fmat\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto 5 5 simp: list_fmap_rel_def extra_clause_information.simps extra_clause_information_simps
      irred_clauses_l_fmat_def increase_activity_fmap_def increase_activity_def case_prod_beta
      dest: multi_member_split)

sepref_definition increase_activity_fmap_fast
  is \<open>uncurry2 increase_activity_fmap\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a isasat_clauses_assn\<^sup>d \<rightarrow>\<^sub>a isasat_clauses_assn\<close>
  supply sum_mod_uint32_max[sepref_fr_rules]
  unfolding increase_activity_fmap_def
  by sepref

sepref_definition increase_activity_fmap_slow
  is \<open>uncurry2 increase_activity_fmap\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a isasat_clauses_assn\<^sup>d \<rightarrow>\<^sub>a isasat_clauses_assn\<close>
  supply sum_mod_uint32_max[sepref_fr_rules]
  unfolding increase_activity_fmap_def
  by sepref

lemma increase_activity_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 increase_activity_fmap_fast, uncurry2 (RETURN \<circ>\<circ>\<circ> increase_activity))
    \<in> [\<lambda>((a, b), ba). a \<in># dom_m ba]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>d \<rightarrow>
     clauses_ll_assn\<close>
  using  increase_activity_fmap_fast.refine[FCOMP increase_activity_fmap] unfolding clauses_ll_assn_def .

lemma increase_activity_slow_hnr[sepref_fr_rules]:
  \<open>(uncurry2 increase_activity_fmap_slow, uncurry2 (RETURN \<circ>\<circ>\<circ> increase_activity))
    \<in> [\<lambda>((a, b), ba). a \<in># dom_m ba]\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>d \<rightarrow>
     clauses_ll_assn\<close>
  using increase_activity_fmap_slow.refine[FCOMP increase_activity_fmap] unfolding clauses_ll_assn_def . *)

end
