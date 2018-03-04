theory IsaSAT_Clauses
imports IsaSAT_Trail
begin

subsubsection \<open>Representation of Clauses\<close>

text \<open>The representation of clauses relies on two important properties:
  \<^item> the empty clause indicates that the clause is not present.
  \<^item> the elements are accessed through type \<^typ>\<open>nat\<close>.
\<close>


definition length_u where
  [simp]: \<open>length_u xs = length xs\<close>

definition length_aa_u where
  [simp]: \<open>length_aa_u xs i = length_u (xs ! i)\<close>

definition nth_raa_i_u64 where
  \<open>nth_raa_i_u64 x L L' = nth_raa x L (nat_of_uint64 L')\<close>

lemma nth_raa_i_uint64_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_i_u64, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_raa_i_u64_def
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)


named_theorems isasat_codegen \<open>lemmas that should be unfolded to generate (efficient) code\<close>

definition list_fmap_rel :: \<open>_ \<Rightarrow> _ \<Rightarrow> ('a list \<times> nat clauses_l) set\<close> where
  list_fmap_rel_internal_def:
  \<open>list_fmap_rel unused R = {(NU', NU). (\<forall>i\<in>#dom_m NU. i < length NU' \<and> (NU'!i, NU \<propto> i) \<in> R) \<and>
         (\<forall>i. i \<notin># dom_m NU \<longrightarrow> i \<ge> length NU' \<or> NU'!i = unused) \<and> NU' \<noteq> []}\<close>

lemma list_fmap_rel_def:
  \<open>\<langle>R\<rangle>list_fmap_rel unused = {(NU', NU). (\<forall>i\<in>#dom_m NU. i < length NU' \<and> (NU'!i, NU \<propto> i) \<in> R) \<and>
         (\<forall>i. i \<notin># dom_m NU \<longrightarrow> i \<ge> length NU' \<or> NU'!i = unused) \<and> NU' \<noteq> []}\<close>
  by (simp add: relAPP_def list_fmap_rel_internal_def)

lemma nth_clauses_l:
  \<open>(uncurry (RETURN oo op !), uncurry (RETURN oo (\<lambda>N i. N \<propto> i)))
    \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>f \<langle>R\<rangle>list_fmap_rel unused \<times>\<^sub>r nat_rel \<rightarrow> \<langle>R\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def)

abbreviation clauses_l_fmat where
  \<open>clauses_l_fmat \<equiv> list_fmap_rel []\<close>

definition clauses_ll_assn :: \<open>nat clauses_l \<Rightarrow> uint32 array array_list \<Rightarrow> assn\<close> where
  \<open>clauses_ll_assn \<equiv> hr_comp (arlO_assn clause_ll_assn) (\<langle>Id\<rangle>clauses_l_fmat)\<close>

definition fmap_rll :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal" where
  [simp]: \<open>fmap_rll l i j = l \<propto> i ! j\<close>


definition fmap_rll_u :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal" where
  [simp]: \<open>fmap_rll_u  = fmap_rll\<close>

lemma nth_clauses_rll:
  \<open>(uncurry2 (RETURN ooo Array_List_Array.nth_rll), uncurry2 (RETURN ooo IsaSAT_Clauses.fmap_rll))
    \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>f
      \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def fmap_rll_def nth_rll_def)

lemma fmap_rll_hnr[sepref_fr_rules]:
  \<open>(uncurry2 nth_raa, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is \<open>_?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>(uncurry2 nth_raa, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll))
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
         (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
        (\<lambda>_ ((l, i), j). i < length l \<and> j < length_rll l i)
         (\<lambda>_. True)]\<^sub>a
       hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
  by (rule hfref_compI_PRE_aux[OF nth_raa_hnr nth_clauses_rll, of unat_lit_assn]) simp
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

lemma fmap_rll_u_hnr[sepref_fr_rules]:
  \<open>(uncurry2 nth_raa_u', uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is \<open>_?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>(uncurry2 nth_raa_u', uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll))
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
         (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
        (\<lambda>_ ((l, i), j). i < length l \<and> j < length_rll l i)
         (\<lambda>_. True)]\<^sub>a
       hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
  by (rule hfref_compI_PRE_aux[OF nth_raa_u'_uint_hnr nth_clauses_rll, of unat_lit_assn]) simp
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
    using H unfolding f im fmap_rll_u_def apply assumption
    using pre ..
qed

definition fmap_rll_u64 :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal" where
  [simp]: \<open>fmap_rll_u64  = fmap_rll\<close>

lemma fmap_rll_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry2 nth_raa_i_u64, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u64))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is \<open>_?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>?c \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
         (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
        (\<lambda>_ ((l, i), j). i < length l \<and> j < length_rll l i)
         (\<lambda>_. True)]\<^sub>a
       hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_rll_u64_def
    by (rule hfref_compI_PRE_aux[OF nth_raa_i_uint64_hnr nth_clauses_rll, of unat_lit_assn]) simp
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
    using H unfolding f im fmap_rll_u_def apply assumption
    using pre ..
qed

definition fmap_length_rll_u :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat" where
  \<open>fmap_length_rll_u l i = length_u (l \<propto> i)\<close>

declare fmap_length_rll_u_def[symmetric, isasat_codegen]

(*TODO rename length_rll_n_uint32*)
lemma fmap_length_rll_u:
  \<open>(uncurry (RETURN oo length_rll_n_uint32), uncurry (RETURN oo fmap_length_rll_u))
    \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>f \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def fmap_length_rll_u_def length_rll_def)

lemma fmap_length_rll_u_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_u, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u))
     \<in> [\<lambda>(N, i). i \<in># dom_m N \<and> length (N \<propto> i) \<le> uint_max]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
   (is \<open>_?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>(uncurry length_raa_u, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u))
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ (xs, i). i < length xs \<and> length (xs ! i) \<le> uint_max)
            (\<lambda>_. True)]\<^sub>a
         hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k) (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
         hr_comp uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_raa_u_hnr fmap_length_rll_u, of unat_lit_assn])
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

definition fmap_length_rll_u64 :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat" where
  \<open>fmap_length_rll_u64 l i = length_u (l \<propto> i)\<close>


declare fmap_length_rll_u_def[symmetric, isasat_codegen]

(*TODO rename length_rll_n_uint32*)
lemma fmap_length_rll_u64:
  \<open>(uncurry (RETURN oo length_rll_n_uint64), uncurry (RETURN oo fmap_length_rll_u64))
    \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>f \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def fmap_length_rll_u64_def length_rll_def)

lemma fmap_length_rll_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_u64, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u64))
     \<in> [\<lambda>(N, i). i \<in># dom_m N \<and> length (N \<propto> i) \<le> uint64_max]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
   (is \<open>_?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>?c
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ (xs, i). i < length xs \<and> length (xs ! i) \<le> uint64_max)
            (\<lambda>_. True)]\<^sub>a
         hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k) (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
         hr_comp uint64_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_raa_u64_hnr fmap_length_rll_u64, of unat_lit_assn])
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


definition fmap_length_rll :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat" where
  [simp]: \<open>fmap_length_rll l i = length (l \<propto> i)\<close>


(*TODO rename length_rll_n_uint32*)
lemma fmap_length_rll:
  \<open>(uncurry (RETURN oo length_rll), uncurry (RETURN oo fmap_length_rll))
    \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>f \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def fmap_length_rll_def length_rll_def)

lemma fmap_length_rll_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa, uncurry (RETURN \<circ>\<circ> fmap_length_rll))
     \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
   (is \<open>_?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>(uncurry length_raa, uncurry (RETURN \<circ>\<circ> fmap_length_rll))
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel)
            (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ (xs, i). i < length xs)
            (\<lambda>_. True)]\<^sub>a
          hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k) (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
           hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_raa_hnr fmap_length_rll, of unat_lit_assn])
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

definition fmap_swap_ll where
  [simp]: \<open>fmap_swap_ll N i j f = N(i \<hookrightarrow> swap (N \<propto> i) j f)\<close>

lemma swap_ll_fmap_swap_ll:
  \<open>(uncurry3 (RETURN oooo swap_ll), uncurry3 (RETURN oooo fmap_swap_ll))
    \<in> [\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i)]\<^sub>f
        \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>clauses_l_fmat\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: list_fmap_rel_def Array_List_Array.swap_ll_def)

lemma fmap_swap_ll_hnr[sepref_fr_rules]:
  \<open>(uncurry3 swap_aa, uncurry3 (RETURN oooo fmap_swap_ll))
     \<in> [\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> clauses_ll_assn\<close>
   (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>?c \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
             (\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i))
             (\<lambda>_ (((xs, k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k)
             (\<lambda>_. True)]\<^sub>a
          hrp_comp ((arlO_assn clause_ll_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
          hr_comp (arlO_assn clause_ll_assn) (\<langle>Id\<rangle>clauses_l_fmat)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF swap_aa_hnr swap_ll_fmap_swap_ll, of unat_lit_assn]) simp
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



definition arl_get_u64 :: "'a::heap array_list \<Rightarrow> uint64 \<Rightarrow> 'a Heap" where
  "arl_get_u64 \<equiv> \<lambda>a i. arl_get' a (integer_of_uint64 i)"


lemma arl_get_hnr_u[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure A\<close>
  shows \<open>(uncurry arl_get_u64, uncurry (RETURN \<circ>\<circ> op_list_get))
     \<in> [pre_list_get]\<^sub>a (arl_assn A)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> A\<close>
proof -
  obtain A' where
    A: \<open>pure A' = A\<close>
    using assms pure_the_pure by auto
  then have A': \<open>the_pure A = A'\<close>
    by auto
  have [simp]: \<open>the_pure (\<lambda>a c. \<up> ((c, a) \<in> A')) = A'\<close>
    unfolding pure_def[symmetric] by auto
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: uint64_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
        hr_comp_def list_rel_pres_length list_rel_update param_nth arl_assn_def
        A' A[symmetric] pure_def arl_get_u64_def Array.nth'_def arl_get'_def
        nat_of_uint64_code[symmetric])
qed


definition nth_raa_u64' where
  \<open>nth_raa_u64' xs x L =  nth_raa xs x (nat_of_uint64 L)\<close>

lemma nth_raa_u'_uint_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_u64', uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def nth_raa_u64'_def)


definition nth_raa_u64 where
  \<open>nth_raa_u64 x L =  nth_raa x (nat_of_uint64 L)\<close>


lemma nth_raa_uint64_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_u64, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_raa_u64_def
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

definition nth_raa_u64_u64 where
  \<open>nth_raa_u64_u64 x L L' =  nth_raa x (nat_of_uint64 L) (nat_of_uint64 L')\<close>


lemma nth_raa_uint64_uint64_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_u64_u64, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_raa_u64_u64_def
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

definition update_raa_u64
   :: "('a::{heap,default}) arrayO_raa \<Rightarrow> nat \<Rightarrow> uint64 \<Rightarrow> 'a \<Rightarrow> 'a arrayO_raa Heap" where
  \<open>update_raa_u64 a i j y = do {
      x \<leftarrow> arl_get a i;
      a' \<leftarrow> heap_array_set_u64 x j y;
      arl_set a i a'
    }\<close> -- \<open>is the Array.upd really needed?\<close>

lemma heap_array_set_u64_upd:
  \<open>heap_array_set_u64 x j xi = Array.upd (nat_of_uint64 j) xi x \<bind> (\<lambda>xa. return x) \<close>
  by (auto simp:  heap_array_set_u64_def heap_array_set'_u64_def
     Array.upd'_def nat_of_uint64_code[symmetric])

definition swap_aa_u64  :: "('a::{heap,default}) arrayO_raa \<Rightarrow> nat \<Rightarrow> uint64 \<Rightarrow> uint64 \<Rightarrow> 'a arrayO_raa Heap" where
  \<open>swap_aa_u64 xs k i j = do {
    xi \<leftarrow> arl_get xs k;
    xj \<leftarrow> swap_u64_code xi i j;
    xs \<leftarrow> arl_set xs k xj;
    return xs
  }\<close>

lemma swap_aa_u64_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry3 swap_aa_u64, uncurry3 (RETURN oooo swap_ll)) \<in>
   [\<lambda>(((xs, k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k]\<^sub>a
  (arlO_assn (array_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>
    (arlO_assn (array_assn R))\<close>
proof -
  note update_raa_rule_pure[sep_heap_rules]
  obtain R' where R': \<open>R' = the_pure R\<close> and RR': \<open>R = pure R'\<close>
    using assms by fastforce
  have [simp]: \<open>the_pure (\<lambda>a b. \<up> ((b, a) \<in> R')) = R'\<close>
    unfolding pure_def[symmetric] by auto
  have H: \<open><is_array_list p (aa, bc) *
       heap_list_all_nth (array_assn (\<lambda>a c. \<up> ((c, a) \<in> R'))) (remove1 bb [0..<length p]) a p *
       array_assn (\<lambda>a c. \<up> ((c, a) \<in> R')) (a ! bb) (p ! bb)>
      Array.nth (p ! bb) (nat_of_integer (integer_of_uint64 bia))
      <\<lambda>r. \<exists>\<^sub>A p'. is_array_list p' (aa, bc) * \<up> (bb < length p' \<and> p' ! bb = p ! bb \<and> length a = length p') *
          heap_list_all_nth (array_assn (\<lambda>a c. \<up> ((c, a) \<in> R'))) (remove1 bb [0..<length p']) a p' *
         array_assn (\<lambda>a c. \<up> ((c, a) \<in> R')) (a ! bb) (p' ! bb) *
         R (a ! bb ! (nat_of_uint64 bia)) r >\<close>
    if
      \<open>is_pure (\<lambda>a c. \<up> ((c, a) \<in> R'))\<close> and
      \<open>bb < length p\<close> and
      \<open>nat_of_uint64 bia < length (a ! bb)\<close> and
      \<open>nat_of_uint64 bi < length (a ! bb)\<close> and
      \<open>length a = length p\<close>
    for bi :: \<open>uint64\<close> and bia :: \<open>uint64\<close> and bb :: \<open>nat\<close> and a :: \<open>'a list list\<close> and
      aa :: \<open>'b array array\<close> and bc :: \<open>nat\<close> and p :: \<open>'b array list\<close>
    using that
    by (sep_auto simp: array_assn_def hr_comp_def is_array_def nat_of_uint64_code[symmetric]
        list_rel_imp_same_length RR' pure_def param_nth)
  have H': \<open>is_array_list p' (aa, ba) * p' ! bb \<mapsto>\<^sub>a b [nat_of_uint64 bia := b ! nat_of_uint64 bi,
             nat_of_uint64 bi := xa] *
      heap_list_all_nth (\<lambda>a b.  \<exists>\<^sub>Aba.  b \<mapsto>\<^sub>a ba *  \<up> ((ba, a) \<in> \<langle>R'\<rangle>list_rel))
          (remove1 bb [0..<length p']) a p' * R (a ! bb ! nat_of_uint64 bia) xa \<Longrightarrow>\<^sub>A
      is_array_list p' (aa, ba) *
      heap_list_all
       (\<lambda>a c. \<exists>\<^sub>Ab. c \<mapsto>\<^sub>a b *  \<up> ((b, a) \<in> \<langle>R'\<rangle>list_rel))
       (a[bb := (a ! bb) [nat_of_uint64 bia := a ! bb ! nat_of_uint64 bi,
             nat_of_uint64 bi := a ! bb ! nat_of_uint64 bia]])
        p' *  true\<close>
    if
      \<open>is_pure (\<lambda>a c. \<up> ((c, a) \<in> R'))\<close> and
      le: \<open>nat_of_uint64 bia < length (a ! bb)\<close> and
      le': \<open>nat_of_uint64 bi < length (a ! bb)\<close> and
      \<open>bb < length p'\<close> and
      \<open>length a = length p'\<close> and
      a: \<open>(b, a ! bb) \<in> \<langle>R'\<rangle>list_rel\<close>
    for bi :: \<open>uint64\<close> and bia :: \<open>uint64\<close> and bb :: \<open>nat\<close> and a :: \<open>'a list list\<close> and
      xa :: \<open>'b\<close> and p' :: \<open>'b array list\<close> and b :: \<open>'b list\<close> and aa :: \<open>'b array array\<close> and ba :: \<open>nat\<close>
  proof -
    have 1: \<open>(b[nat_of_uint64 bia := b ! nat_of_uint64 bi, nat_of_uint64 bi := xa],
   (a ! bb)[nat_of_uint64 bia := a ! bb ! nat_of_uint64 bi,
   nat_of_uint64 bi := a ! bb ! nat_of_uint64 bia]) \<in> \<langle>R'\<rangle>list_rel\<close>
      if \<open>(xa, a ! bb ! nat_of_uint64 bia) \<in> R'\<close>
      using that a le le'
      unfolding list_rel_def list_all2_conv_all_nth
      by auto
    have 2: \<open>heap_list_all_nth (\<lambda>a b. \<exists>\<^sub>Aba. b \<mapsto>\<^sub>a ba * \<up> ((ba, a) \<in> \<langle>R'\<rangle>list_rel)) (remove1 bb [0..<length p']) a p' =
    heap_list_all_nth (\<lambda>a c. \<exists>\<^sub>Ab. c \<mapsto>\<^sub>a b * \<up> ((b, a) \<in> \<langle>R'\<rangle>list_rel)) (remove1 bb [0..<length p'])
     (a[bb := (a ! bb)[nat_of_uint64 bia := a ! bb ! nat_of_uint64 bi, nat_of_uint64 bi := a ! bb ! nat_of_uint64 bia]]) p'\<close>
      by (rule heap_list_all_nth_cong)  auto
    show ?thesis using that
      unfolding heap_list_all_heap_list_all_nth_eq
      by (subst (2) heap_list_all_nth_remove1[of bb])
        (sep_auto simp:  heap_list_all_heap_list_all_nth_eq swap_def fr_refl RR'
          pure_def 2[symmetric] intro!: 1)+
  qed

  show ?thesis
    using assms unfolding R'[symmetric] unfolding RR'
    apply sepref_to_hoare

    apply (sep_auto simp: swap_aa_u64_def swap_ll_def arlO_assn_except_def length_rll_def
        length_rll_update_rll nth_raa_i_u64_def uint64_nat_rel_def br_def
        swap_def nth_rll_def list_update_swap swap_u64_code_def nth_u64_code_def Array.nth'_def
        heap_array_set_u64_def heap_array_set'_u64_def arl_assn_def
         Array.upd'_def)
     apply (drule_tac aa = aa and bc =bc in H[of ])
    apply assumption
    apply assumption
    apply assumption
    apply assumption
     apply assumption
    apply (sep_auto simp: array_assn_def nat_of_uint64_code[symmetric] hr_comp_def is_array_def
        list_rel_imp_same_length arlO_assn_def arl_assn_def hr_comp_def[abs_def])
    apply (rule H'; assumption?)
    done
qed

definition fm_add_new where
 \<open>fm_add_new b C N = do {
    i \<leftarrow> get_fresh_index N;
    let N = fmupd i (C, b) N;
    RETURN (N, i)
  }\<close>

definition fm_add_new_at_position
   :: \<open>bool \<Rightarrow> nat \<Rightarrow> 'v clause_l \<Rightarrow> 'v clauses_l \<Rightarrow> 'v clauses_l\<close>
where
  \<open>fm_add_new_at_position b i C N = fmupd i (C, b) N\<close>

definition append_and_length
   :: \<open>bool \<Rightarrow> 'v clause_l \<Rightarrow> 'v clause_l list \<Rightarrow> 'v clause_l list \<times> nat\<close>
where
\<open>append_and_length b C N = (let k = length N in (op_list_append N C, k))\<close>

lemma append_and_length_fm_add_new:
  \<open>(uncurry2 (RETURN ooo append_and_length), uncurry2 fm_add_new)
     \<in> bool_rel \<times>\<^sub>f (\<langle>Id\<rangle>list_rel) \<times>\<^sub>f (\<langle>Id\<rangle>clauses_l_fmat) \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (fastforce simp: fm_add_new_at_position_def list_fmap_rel_def Let_def
      max_def nth_append append_and_length_def fm_add_new_def get_fresh_index_def
      RETURN_RES_refine_iff RES_RETURN_RES
      intro!: RETURN_SPEC_refine
      dest: multi_member_split
      split: if_splits)

sepref_definition append_and_length_code
  is \<open>uncurry2 (RETURN ooo append_and_length)\<close>
  :: \<open>bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a (arlO_assn clause_ll_assn)\<^sup>d \<rightarrow>\<^sub>a
       arlO_assn clause_ll_assn *a nat_assn\<close>
  unfolding append_and_length_def
  by sepref

lemma fm_add_new_hnr[sepref_fr_rules]:
  \<open>(uncurry2 append_and_length_code, uncurry2 fm_add_new)
    \<in> bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>d \<rightarrow>\<^sub>a clauses_ll_assn *a nat_assn\<close>
  using append_and_length_code.refine[FCOMP append_and_length_fm_add_new]
  unfolding clauses_ll_assn_def by simp


definition fmap_swap_ll_u64 where
  [simp]: \<open>fmap_swap_ll_u64 = fmap_swap_ll\<close>

lemma fmap_swap_ll_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry3 swap_aa_u64, uncurry3 (RETURN oooo fmap_swap_ll_u64))
     \<in> [\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> clauses_ll_assn\<close>
   (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>?c \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
             (\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i))
             (\<lambda>_ (((xs, k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k)
             (\<lambda>_. True)]\<^sub>a
          hrp_comp ((arlO_assn clause_ll_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
          hr_comp (arlO_assn clause_ll_assn) (\<langle>Id\<rangle>clauses_l_fmat)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_swap_ll_u64_def
    by (rule hfref_compI_PRE_aux[OF swap_aa_u64_hnr swap_ll_fmap_swap_ll, of unat_lit_assn]) simp
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

end