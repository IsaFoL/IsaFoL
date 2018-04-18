theory IsaSAT_Clauses
imports IsaSAT_Trail
begin

subsubsection \<open>Representation of Clauses\<close>

text \<open>The representation of clauses relies on two important properties:
  \<^item> the empty clause indicates that the clause is not present.
  \<^item> the elements are accessed through type \<^typ>\<open>nat\<close>.
\<close>

named_theorems isasat_codegen \<open>lemmas that should be unfolded to generate (efficient) code\<close>

definition list_fmap_rel :: \<open>_ \<Rightarrow> _ \<Rightarrow> ('a list \<times> nat clauses_l) set\<close> where
  list_fmap_rel_internal_def:
  \<open>list_fmap_rel unused R = {(NU', NU). (\<forall>i\<in>#dom_m NU. i < length NU' \<and> (NU'!i, NU \<propto> i) \<in> R) \<and>
         (\<forall>i. i \<notin># dom_m NU \<longrightarrow> i \<ge> length NU' \<or> NU'!i = unused) \<and> NU' \<noteq> [] \<and>
         Suc (Max_mset (add_mset 0 (dom_m NU))) = length NU'}\<close>

lemma list_fmap_rel_def:
  \<open>\<langle>R\<rangle>list_fmap_rel unused = {(NU', NU). (\<forall>i\<in>#dom_m NU. i < length NU' \<and> (NU'!i, NU \<propto> i) \<in> R) \<and>
         (\<forall>i. i \<notin># dom_m NU \<longrightarrow> i \<ge> length NU' \<or> NU'!i = unused) \<and> NU' \<noteq> [] \<and>
          Suc (Max_mset (add_mset 0 (dom_m NU))) = length NU'}\<close>
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
   (is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
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


definition fmap_rll_u64 :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal" where
  [simp]: \<open>fmap_rll_u64  = fmap_rll\<close>

lemma fmap_rll_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry2 nth_raa_i_u64, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u64))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is ?slow is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
   fmap_rll_i32_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry2 nth_raa_i32_u64, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u64))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
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
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im fmap_rll_u_def apply assumption
    using pre ..
  have H:
    \<open>?cfast \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
         (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
        (\<lambda>_ ((l, i), j). i < length l \<and> j < length (l!i))
         (\<lambda>_. True)]\<^sub>a
       hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_rll_u64_def
    by (rule hfref_compI_PRE_aux[OF nth_raa_i32_u64_hnr nth_clauses_rll, of unat_lit_assn]) simp
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
   (is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
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

lemma fmap_length_rll_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_u64, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u64))
     \<in> [\<lambda>(N, i). i \<in># dom_m N \<and> length (N \<propto> i) \<le> uint64_max]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
   (is ?slow is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
  fmap_length_rll_u32_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_u32_u64, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u64))
     \<in> [\<lambda>(N, i). i \<in># dom_m N \<and> length (N \<propto> i) \<le> uint64_max]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
   (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
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
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
  have H:
    \<open>?cfast
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ (xs, i). i < length xs \<and> length (xs ! i) \<le> uint64_max)
            (\<lambda>_. True)]\<^sub>a
         hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k) (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
         hr_comp uint64_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_raa_u32_u64_hnr fmap_length_rll_u64, of unat_lit_assn])
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
qed


definition fmap_length_rll :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat" where
  [simp]: \<open>fmap_length_rll l i = length (l \<propto> i)\<close>


(*TODO rename length_rll_n_uint32*)
lemma fmap_length_rll:
  \<open>(uncurry (RETURN oo length_rll), uncurry (RETURN oo fmap_length_rll))
    \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>f \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def fmap_length_rll_def length_rll_def)


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

lemma fmap_length_rll_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa, uncurry (RETURN \<circ>\<circ> fmap_length_rll))
     \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
   (is ?slow is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
 fmap_length_rll_u32_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_u32, uncurry (RETURN \<circ>\<circ> fmap_length_rll))
     \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
   (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have H:
    \<open>?c
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
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
  have H:
    \<open>?cfast
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel)
            (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ (xs, i). i < length xs)
            (\<lambda>_. True)]\<^sub>a
          hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k) (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
           hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_raa_u32_hnr fmap_length_rll, of unat_lit_assn])
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
qed

definition fmap_swap_ll where
  [simp]: \<open>fmap_swap_ll N i j f = N(i \<hookrightarrow> swap (N \<propto> i) j f)\<close>

lemma swap_ll_fmap_swap_ll:
  \<open>(uncurry3 (RETURN oooo swap_ll), uncurry3 (RETURN oooo fmap_swap_ll))
    \<in> [\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i)]\<^sub>f
        \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>clauses_l_fmat\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (fastforce simp: list_fmap_rel_def Array_List_Array.swap_ll_def split: if_splits)

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
  apply (case_tac \<open>set_mset (dom_m bc) = {}\<close>)
   apply force
  apply force
  done

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


definition get_fresh_index_packed :: \<open>'v clauses_l \<Rightarrow> nat nres\<close> where
\<open>get_fresh_index_packed N = SPEC(\<lambda>i. i > 0 \<and> i \<notin># dom_m N \<and>
    (\<forall>j < i. j > 0 \<longrightarrow> j \<in># dom_m N))\<close>

definition fm_add_new_packed where
 \<open>fm_add_new_packed b C N = do {
    i \<leftarrow> get_fresh_index_packed N;
    let N = fmupd i (C, b) N;
    RETURN (N, i)
  }\<close>

definition packed where
  \<open>packed N \<longleftrightarrow> dom_m N = mset [1..<Max_mset (add_mset 0 (dom_m N))]\<close>

lemma append_and_length_fm_add_new_packed:
  \<open>(uncurry2 (RETURN ooo append_and_length), uncurry2 fm_add_new_packed)
     \<in> [\<lambda>((b, C), N). packed N]\<^sub>f
       bool_rel \<times>\<^sub>f (\<langle>Id\<rangle>list_rel) \<times>\<^sub>f (\<langle>Id\<rangle>clauses_l_fmat) \<rightarrow> \<langle>\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: fm_add_new_at_position_def list_fmap_rel_def Let_def
      max_def nth_append append_and_length_def fm_add_new_packed_def get_fresh_index_packed_def
      RETURN_RES_refine_iff RES_RETURN_RES packed_def
      intro!: RETURN_SPEC_refine
      dest: multi_member_split
      split: if_splits)
       apply force
      apply (metis (no_types, lifting) Max_n_upt Suc_leI Suc_pred atLeastLessThan_iff
      finite_atLeastLessThan finite_set_mset_mset_set less_Suc_eq)
  apply force
  apply force
  apply force
  apply (case_tac \<open>set_mset (dom_m bc) = {}\<close>)
   apply force
  apply force
  done

lemma fm_add_new_packed_hnr[sepref_fr_rules]:
  \<open>(uncurry2 append_and_length_code, uncurry2 fm_add_new_packed)
    \<in> [\<lambda>(_, N). packed N]\<^sub>a bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>d \<rightarrow> clauses_ll_assn *a nat_assn\<close>
  using append_and_length_code.refine[FCOMP append_and_length_fm_add_new_packed]
  unfolding clauses_ll_assn_def
  by simp

(* TODO Proper setup + Move *)
definition length_arlO_u where
  \<open>length_arlO_u xs = do {
      n \<leftarrow> length_ra xs;
      return (uint32_of_nat n)}\<close>

lemma length_arlO_u[sepref_fr_rules]:
  \<open>(length_arlO_u, RETURN o length_u) \<in>
     [\<lambda>xs. length xs \<le> uint32_max]\<^sub>a (arlO_assn R)\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: length_arlO_u_def arl_length_def uint32_nat_rel_def
      br_def nat_of_uint32_uint32_of_nat_id)
(* End Move *)

definition convert_to_uint32 :: \<open>nat \<Rightarrow> nat\<close> where
  [simp]: \<open>convert_to_uint32 = id\<close>
lemma convert_to_uint32_hnr[sepref_fr_rules]:
  \<open>(return o uint32_of_nat, RETURN o convert_to_uint32) \<in> [\<lambda>n. n \<le> uint32_max]\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def uint32_max_def nat_of_uint32_uint32_of_nat_id)

definition append_and_length_u32
   :: \<open>bool \<Rightarrow> 'v clause_l \<Rightarrow> 'v clause_l list \<Rightarrow> ('v clause_l list \<times> nat) nres\<close>
  where
\<open>append_and_length_u32 b C N = do {
    ASSERT(length N \<le> uint32_max);
    let k = length N;
    RETURN (op_list_append N C, convert_to_uint32 k)}\<close>

lemma (in -) clauses_l_fmat_not_nil[simp]:
  \<open>([], bc) \<in> \<langle>Id\<rangle>clauses_l_fmat \<longleftrightarrow> False\<close>
  by (auto simp: list_fmap_rel_def)

lemma clauses_l_fmat_length:
  \<open>(ba, bc) \<in> \<langle>Id\<rangle>clauses_l_fmat \<Longrightarrow> length ba = Suc (Max_mset (add_mset 0 (dom_m bc)))\<close>
  by (auto simp: list_fmap_rel_def)

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
  apply auto
  apply (case_tac \<open>set_mset (dom_m bc) = {}\<close>)
  apply auto
  done

sepref_definition append_and_length_u32_code
  is \<open>uncurry2 (append_and_length_u32)\<close>
  :: \<open>bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a (arlO_assn clause_ll_assn)\<^sup>d \<rightarrow>\<^sub>a
       arlO_assn clause_ll_assn *a uint32_nat_assn\<close>
  unfolding append_and_length_u32_def
  by sepref


named_theorems isasat_fast

definition fm_add_new_fast where
  [simp, symmetric, isasat_fast]: \<open>fm_add_new_fast = fm_add_new\<close>

lemma fm_add_new_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 append_and_length_u32_code, uncurry2 fm_add_new_fast)
    \<in> [\<lambda>(_, ba). (\<forall>a\<in>#dom_m ba. a < uint_max)]\<^sub>a
       bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>d \<rightarrow> clauses_ll_assn *a uint32_nat_assn\<close>
  using append_and_length_u32_code.refine[FCOMP append_and_length_u32_fm_add_new]
  unfolding clauses_ll_assn_def by (simp add: uint32_max_def)


lemma append_and_length_u32_fm_add_new_packed:
  \<open>(uncurry2 append_and_length_u32, uncurry2 fm_add_new_packed)
     \<in> [\<lambda>((b, C), N). Max (insert 0 (set_mset (dom_m N))) < uint32_max \<and> packed N]\<^sub>f
     bool_rel \<times>\<^sub>f (\<langle>Id\<rangle>list_rel) \<times>\<^sub>f (\<langle>Id\<rangle>clauses_l_fmat) \<rightarrow> \<langle>\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
(* TODO Tune proof *)
  apply (intro frefI nres_relI)
  apply (auto simp: fm_add_new_at_position_def list_fmap_rel_def Let_def
      max_def nth_append append_and_length_u32_def fm_add_new_packed_def get_fresh_index_packed_def
      RETURN_RES_refine_iff RES_RETURN_RES packed_def
      intro!: RETURN_SPEC_refine ASSERT_refine_left
      dest: multi_member_split
      split: if_splits)
       apply (metis Max_in_lits Suc_leI empty_iff insert_iff set_mset_add_mset_insert
      set_mset_empty)
       apply auto
   apply (metis (no_types, lifting) Max_n_upt Suc_leI Suc_pred atLeastLessThan_iff
      finite_atLeastLessThan finite_set_mset_mset_set less_Suc_eq)
  apply (case_tac \<open>set_mset (dom_m bc) = {}\<close>)
  apply auto
  done

definition fm_add_new_packed_fast where
  [simp, symmetric, isasat_fast]: \<open>fm_add_new_packed_fast = fm_add_new_packed\<close>

lemma fm_add_new_packed_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 append_and_length_u32_code, uncurry2 fm_add_new_packed_fast)
    \<in> [\<lambda>(_, ba). (\<forall>a\<in>#dom_m ba. a < uint_max) \<and> packed ba]\<^sub>a
       bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>d \<rightarrow> clauses_ll_assn *a uint32_nat_assn\<close>
  using append_and_length_u32_code.refine[FCOMP append_and_length_u32_fm_add_new_packed]
  unfolding clauses_ll_assn_def by (simp add: uint32_max_def)

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

definition swap_aa_i32_u64  :: "('a::{heap,default}) arrayO_raa \<Rightarrow> uint32 \<Rightarrow> uint64 \<Rightarrow> uint64 \<Rightarrow> 'a arrayO_raa Heap" where
  \<open>swap_aa_i32_u64 xs k i j = do {
    xi \<leftarrow> arl_get_u xs k;
    xj \<leftarrow> swap_u64_code xi i j;
    xs \<leftarrow> arl_set_u xs k xj;
    return xs
  }\<close>

(* TODO Move and adapt proofs *)
lemma arrayO_arl_get_u_rule[sep_heap_rules]:
  assumes i: \<open>i < length a\<close> and \<open>(i' , i) \<in> uint32_nat_rel\<close>
  shows \<open><arlO_assn (array_assn R) a ai> arl_get_u ai i' <\<lambda>r. arlO_assn_except (array_assn R) [i] a ai
   (\<lambda>r'. array_assn R (a ! i) r * \<up>(r = r' ! i))>\<close>
  using assms
  by (sep_auto simp: arl_get_u_def arl_get'_def nat_of_uint32_code[symmetric]
      uint32_nat_rel_def br_def)
(* END Move *)

lemma swap_aa_i32_u64_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry3 swap_aa_i32_u64, uncurry3 (RETURN oooo swap_ll)) \<in>
   [\<lambda>(((xs, k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k]\<^sub>a
  (arlO_assn (array_assn R))\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>
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

    apply (sep_auto simp: swap_aa_i32_u64_def swap_ll_def arlO_assn_except_def length_rll_def
        length_rll_update_rll nth_raa_i_u64_def uint64_nat_rel_def br_def
        swap_def nth_rll_def list_update_swap swap_u64_code_def nth_u64_code_def Array.nth'_def
        heap_array_set_u64_def heap_array_set'_u64_def arl_assn_def
         Array.upd'_def)
    apply (rule H; assumption)
    apply (sep_auto simp: array_assn_def nat_of_uint64_code[symmetric] hr_comp_def is_array_def
        list_rel_imp_same_length arlO_assn_def arl_assn_def hr_comp_def[abs_def] arl_set_u_def
        arl_set'_u_def list_rel_pres_length uint32_nat_rel_def br_def)
    apply (rule H'; assumption)
    done
qed

lemma fmap_swap_ll_i32_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry3 swap_aa_i32_u64, uncurry3 (RETURN oooo fmap_swap_ll_u64))
     \<in> [\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> clauses_ll_assn\<close>
   (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>?c \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
             (\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i))
             (\<lambda>_ (((xs, k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k)
             (\<lambda>_. True)]\<^sub>a
          hrp_comp ((arlO_assn clause_ll_assn)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
          hr_comp (arlO_assn clause_ll_assn) (\<langle>Id\<rangle>clauses_l_fmat)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_swap_ll_u64_def
    by (rule hfref_compI_PRE_aux[OF swap_aa_i32_u64_hnr swap_ll_fmap_swap_ll, of unat_lit_assn]) simp
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


lemma
  fmap_rll_u_hnr[sepref_fr_rules]:
    \<open>(uncurry2 nth_raa_u', uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is ?slow is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
  fmap_rll_i32_u_hnr[sepref_fr_rules]:
    \<open>(uncurry2 nth_raa_i32_u32, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have H:
    \<open>?c
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
           (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
           (\<lambda>_ ((l, i), j). i < length l \<and> j < length_rll l i)
          (\<lambda>_. True)]\<^sub>a
       hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
       hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_rll_u_def
    by (rule hfref_compI_PRE_aux[OF nth_raa_u'_uint_hnr nth_clauses_rll, of unat_lit_assn]) simp
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
           (\<lambda>_ ((l, i), j). i < length l \<and> j < length (l!i))
          (\<lambda>_. True)]\<^sub>a
       hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
       hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    unfolding fmap_rll_u_def
    by (rule hfref_compI_PRE_aux[OF nth_raa_i32_u32_hnr nth_clauses_rll, of unat_lit_assn]) simp
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


lemma fmap_rll_i32_hnr[sepref_fr_rules]:
  \<open>(uncurry2 nth_raa_i32, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll_u))
     \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
   (is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>(uncurry2 nth_raa_i32, uncurry2 (RETURN \<circ>\<circ>\<circ> fmap_rll))
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel)
         (\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i))
        (\<lambda>_ ((l, i), j). i < length l \<and> j < length (l!i))
         (\<lambda>_. True)]\<^sub>a
       hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                   (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF nth_raa_i32_hnr nth_clauses_rll, of unat_lit_assn]) simp
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


definition length_raa_i32_u :: \<open>'a::heap arrayO_raa \<Rightarrow> uint32 \<Rightarrow> uint32 Heap\<close> where
  \<open>length_raa_i32_u xs i = do {
     x \<leftarrow> arl_get_u xs i;
    length_u_code x}\<close>

lemma length_raa_i32_rule[sep_heap_rules]:
  assumes \<open>nat_of_uint32 b < length xs\<close>
  shows \<open><arlO_assn (array_assn R) xs a> length_raa_i32_u a b
   <\<lambda>r. arlO_assn (array_assn R) xs a * \<up> (r = uint32_of_nat (length_rll xs (nat_of_uint32 b)))>\<^sub>t\<close>
proof -
  have 1: \<open>a * b* c = c * a *b\<close> for a b c :: assn
    by (auto simp: ac_simps)
  have [sep_heap_rules]: \<open><arlO_assn_except (array_assn R) [nat_of_uint32 b] xs a
           (\<lambda>r'. array_assn R (xs ! nat_of_uint32 b) x *
                 \<up> (x = r' ! nat_of_uint32 b))>
         Array.len x <\<lambda>r.  arlO_assn (array_assn R) xs a *
                 \<up> (r = length (xs ! nat_of_uint32 b))>\<close>
    for x
    unfolding arlO_assn_except_def
    apply (subst arlO_assn_except_array0_index[symmetric, OF assms])
    apply sep_auto
    apply (subst 1)
    by (sep_auto simp: array_assn_def is_array_def hr_comp_def list_rel_imp_same_length
        arlO_assn_except_def)
  show ?thesis
    using assms
    unfolding length_raa_i32_u_def length_u_code_def arl_get_u_def arl_get'_def length_rll_def
    by (sep_auto simp: nat_of_uint32_code[symmetric])
qed

lemma length_raa_i32_u_hnr[sepref_fr_rules]:
  shows \<open>(uncurry length_raa_i32_u, uncurry (RETURN \<circ>\<circ> length_rll_n_uint32)) \<in>
     [\<lambda>(xs, i). i < length xs \<and> length (xs ! i) \<le> uint32_max]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def length_rll_def
      nat_of_uint32_uint32_of_nat_id)+

lemma fmap_length_rll_i32_u_hnr[sepref_fr_rules]:
  \<open>(uncurry length_raa_i32_u, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u))
     \<in> [\<lambda>(N, i). i \<in># dom_m N \<and> length (N \<propto> i) \<le> uint_max]\<^sub>a
     clauses_ll_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
   (is \<open>?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H:
    \<open>(uncurry length_raa_i32_u, uncurry (RETURN \<circ>\<circ> fmap_length_rll_u))
       \<in> [comp_PRE (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) (\<lambda>(N, i). i \<in># dom_m N)
            (\<lambda>_ (xs, i). i < length xs \<and> length (xs ! i) \<le> uint_max)
            (\<lambda>_. True)]\<^sub>a
         hrp_comp ((arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k) (\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel) \<rightarrow>
         hr_comp uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    by (rule hfref_compI_PRE_aux[OF length_raa_i32_u_hnr fmap_length_rll_u, of unat_lit_assn])
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
