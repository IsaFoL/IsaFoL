theory IsaSAT_Clauses
imports IsaSAT_Trail
begin

subsubsection \<open>Representation of Clauses\<close>

(* TODO Move + setup for efficient array accesses *)
definition arl_set'_u where
  \<open>arl_set'_u a i x = arl_set a (nat_of_uint32 i) x\<close>

definition arl_set_u :: \<open>'a::heap array_list \<Rightarrow> uint32 \<Rightarrow> 'a \<Rightarrow> 'a array_list Heap\<close>where
  \<open>arl_set_u a i x = arl_set'_u a i x\<close>

lemma arl_set_hnr_u[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure A \<Longrightarrow>
    (uncurry2 arl_set_u, uncurry2 (RETURN \<circ>\<circ>\<circ> op_list_set)) \<in>
     [pre_list_set]\<^sub>a (arl_assn A)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow> arl_assn A\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
      hr_comp_def list_rel_pres_length list_rel_update heap_array_set'_u_def
      heap_array_set_u_def Array.upd'_def arl_set_u_def arl_set'_u_def arl_assn_def
     nat_of_uint32_code[symmetric])
(* End Move *)

text \<open>The representation of clauses relies on two important properties:
  \<^item> the empty clause indicates that the clause is not present.
  \<^item> the elements are accessed through type \<^typ>\<open>nat\<close>.
\<close>


definition length_u where
  [simp]: \<open>length_u xs = length xs\<close>

definition length_aa_u where
  [simp]: \<open>length_aa_u xs i = length_u (xs ! i)\<close>


named_theorems isasat_codegen \<open>lemmas that should be unfolded to generate (efficient) code\<close>

definition list_fmap_rel :: \<open>_ \<Rightarrow> _ \<Rightarrow> ('a list \<times> nat clauses_l) set\<close> where
  list_fmap_rel_internal_def:
  \<open>list_fmap_rel unused R = {(NU', NU). (\<forall>i\<in>#dom_m NU. i < length NU' \<and> (NU'!i, NU \<propto> i) \<in> R) \<and>
         (\<forall>i. i \<notin># dom_m NU \<longrightarrow> i \<ge> length NU' \<or> NU'!i = unused)}\<close>

lemma list_fmap_rel_def:
  \<open>\<langle>R\<rangle>list_fmap_rel unused = {(NU', NU). (\<forall>i\<in>#dom_m NU. i < length NU' \<and> (NU'!i, NU \<propto> i) \<in> R) \<and>
         (\<forall>i. i \<notin># dom_m NU \<longrightarrow> i \<ge> length NU' \<or> NU'!i = unused)}\<close>
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


definition fmap_length_rll :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat" where
  \<open>fmap_length_rll l i = length (l \<propto> i)\<close>


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
end