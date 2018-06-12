theory IsaSAT_Clauses
imports Watched_Literals_Watch_List_Code_Common
begin

subsubsection \<open>Representation of Clauses\<close>

text \<open>The representation of clauses relies on two important properties:
  \<^item> the empty clause indicates that the clause is not present.
  \<^item> the elements are accessed through type \<^typ>\<open>nat\<close>.
\<close>

named_theorems isasat_codegen \<open>lemmas that should be unfolded to generate (efficient) code\<close>


datatype clause_status = INIT | LEARNED | DELETED

instance clause_status :: heap
proof standard
  let ?f = \<open>(\<lambda>x. case x of INIT \<Rightarrow> (0::nat) | LEARNED  \<Rightarrow> 1 | DELETED \<Rightarrow> 2)\<close>
  have \<open>inj ?f\<close>
    by (auto simp: inj_def split: clause_status.splits)
  then show \<open>\<exists>f. inj (f::clause_status \<Rightarrow> nat)\<close>
    by blast
qed

instantiation clause_status :: default
begin
definition default_clause_status where \<open>default_clause_status = DELETED\<close>
instance by standard
end

abbreviation clause_status_assn where
  \<open>clause_status_assn \<equiv> (id_assn :: clause_status \<Rightarrow> _)\<close>

lemma INIT_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return INIT), uncurry0 (RETURN INIT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

lemma LEARNED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return LEARNED), uncurry0 (RETURN LEARNED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

lemma DELETED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return DELETED), uncurry0 (RETURN DELETED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

type_synonym clause_annot = \<open>clause_status \<times> nat \<times> nat\<close>

type_synonym clause_annots = \<open>clause_annot list\<close>

fun get_status :: \<open>clause_annot \<Rightarrow> clause_status\<close> where
\<open>get_status (st, lbd, act) = st\<close>

fun get_lbd :: \<open>clause_annot \<Rightarrow> nat\<close> where
\<open>get_lbd (st, lbd, act) = lbd\<close>

fun set_lbd :: \<open>nat \<Rightarrow> clause_annot \<Rightarrow> clause_annot\<close> where
\<open>set_lbd lbd (st, _, act) = (st, lbd, act)\<close>

fun extra_clause_information where
  \<open>extra_clause_information NU i (st, lbd, act) \<longleftrightarrow>
      (st = DELETED \<longleftrightarrow> i \<notin># dom_m NU) \<and>
      (st = LEARNED \<longleftrightarrow> \<not>irred NU i) \<and>
      (st = INIT \<longleftrightarrow> irred NU i)\<close>

lemma extra_clause_information_simps:
  \<open>extra_clause_information NU i st \<longleftrightarrow>
      (fst st = DELETED \<longleftrightarrow> i \<notin># dom_m NU) \<and>
      (fst st = LEARNED \<longleftrightarrow> \<not>irred NU i) \<and>
      (fst st = INIT \<longleftrightarrow> irred NU i)
      \<close>
  by (cases st) auto

lemma extra_clause_information_update[simp]:
  \<open>i \<in># dom_m aa \<Longrightarrow> extra_clause_information (aa(bd \<hookrightarrow> C)) i (bi) \<longleftrightarrow>
    extra_clause_information aa i (bi)\<close>
  by (cases bi) auto

definition list_fmap_rel :: \<open>_ \<Rightarrow> _ \<Rightarrow> (('a list \<times> clause_annots) \<times> nat clauses_l) set\<close> where
  list_fmap_rel_internal_def:
  \<open>list_fmap_rel unused R = {((NU', extra), (NU)). (\<forall>i\<in>#dom_m NU. i < length NU' \<and> (NU'!i, NU \<propto> i) \<in> R) \<and>
         (\<forall>i. i \<notin># dom_m NU \<longrightarrow> i \<ge> length NU' \<or> (NU'!i = unused \<and> fst (extra!i) = DELETED)) \<and> NU' \<noteq> [] \<and>
         Suc (Max_mset (add_mset 0 (dom_m NU))) = length NU' \<and>
         (\<forall>i\<in>#dom_m NU. i < length extra \<and> extra_clause_information NU i (extra!i)) \<and>
         length NU' = length extra}\<close>

lemma list_fmap_rel_def:
  \<open>\<langle>R\<rangle>list_fmap_rel unused = {((NU', extra), (NU)). (\<forall>i\<in>#dom_m NU. i < length NU' \<and> (NU'!i, NU \<propto> i) \<in> R) \<and>
         (\<forall>i. i \<notin># dom_m NU \<longrightarrow> i \<ge> length NU' \<or> (NU'!i = unused \<and> fst (extra!i) = DELETED)) \<and> NU' \<noteq> [] \<and>
          Suc (Max_mset (add_mset 0 (dom_m NU))) = length NU' \<and>
         (\<forall>i\<in>#dom_m NU. i < length extra \<and> extra_clause_information NU i  (extra!i)) \<and>
         length NU' = length extra}\<close>
  by (simp add: relAPP_def list_fmap_rel_internal_def)

definition clause_nth_fmap where
  \<open>clause_nth_fmap = (\<lambda>(N, _) i. N!i)\<close>

lemma nth_clauses_l:
  \<open>(uncurry (RETURN oo clause_nth_fmap), uncurry (RETURN oo (\<lambda>N i. N \<propto> i)))
    \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>f \<langle>R\<rangle>list_fmap_rel unused \<times>\<^sub>r nat_rel \<rightarrow> \<langle>R\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def clause_nth_fmap_def)

abbreviation clauses_l_fmat where
  \<open>clauses_l_fmat \<equiv> list_fmap_rel []\<close>

abbreviation isasat_clauses_assn where
  \<open>isasat_clauses_assn \<equiv> arlO_assn clause_ll_assn *a arl_assn (clause_status_assn *a uint32_nat_assn *a uint32_nat_assn)\<close>

definition clauses_ll_assn
   :: \<open>nat clauses_l \<Rightarrow> uint32 array array_list \<times> (clause_status \<times> uint32 \<times> uint32)array_list \<Rightarrow>
      assn\<close>
where
  \<open>clauses_ll_assn = hr_comp isasat_clauses_assn (\<langle>Id\<rangle>clauses_l_fmat)\<close>

definition fmap_rll :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal" where
  [simp]: \<open>fmap_rll l i j = l \<propto> i ! j\<close>


definition fmap_rll_u :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal" where
  [simp]: \<open>fmap_rll_u  = fmap_rll\<close>

lemma nth_clauses_rll:
  \<open>(uncurry2 (RETURN ooo (\<lambda>(N, _) i. Array_List_Array.nth_rll N i)), uncurry2 (RETURN ooo IsaSAT_Clauses.fmap_rll))
    \<in> [\<lambda>((N, i), j). i \<in># dom_m N \<and> j < length (N \<propto> i)]\<^sub>f
      \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def fmap_rll_def nth_rll_def)

lemma nth_raa_hnr':
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 (\<lambda>(N, _) j k. nth_raa N j k), uncurry2 (RETURN \<circ>\<circ>\<circ> (\<lambda>(N, _) i. Array_List_Array.nth_rll N i))) \<in>
       [\<lambda>(((l, _),i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R) *a GG )\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  using assms
  by sepref_to_hoare  sep_auto

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
qed


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

lemma fmap_rll_u64_hnr[sepref_fr_rules]:
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
qed


definition fmap_length_rll_u :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat" where
  \<open>fmap_length_rll_u l i = length_u (l \<propto> i)\<close>

declare fmap_length_rll_u_def[symmetric, isasat_codegen]

(*TODO rename length_rll_n_uint32*)
lemma fmap_length_rll_u:
  \<open>(uncurry (RETURN oo (\<lambda>(N, _) i. length_rll_n_uint32 N i)), uncurry (RETURN oo fmap_length_rll_u))
    \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>f \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def fmap_length_rll_u_def length_rll_def)

sepref_definition length_rll_n_uint32_clss
  is \<open>uncurry (RETURN oo (\<lambda>(N, _) i. length_rll_n_uint32 N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint_max]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref

lemma fmap_length_rll_u_hnr[sepref_fr_rules]:
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
qed

sepref_definition length_raa_i64_u_clss
  is \<open>uncurry (RETURN oo (\<lambda>(N, _) i. length_rll_n_uint32 N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint_max]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref

lemma fmap_length_rll_i64_u_hnr[sepref_fr_rules]:
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
qed

definition fmap_length_rll_u64 :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat" where
  \<open>fmap_length_rll_u64 l i = length_u (l \<propto> i)\<close>


declare fmap_length_rll_u_def[symmetric, isasat_codegen]

(*TODO rename length_rll_n_uint32*)
lemma fmap_length_rll_u64:
  \<open>(uncurry (RETURN oo (\<lambda>(N, _) i. length_rll_n_uint64 N i)), uncurry (RETURN oo fmap_length_rll_u64))
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
thm fmap_length_rll_u64
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

lemma fmap_length_rll_u64_hnr[sepref_fr_rules]:
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
qed


definition fmap_length_rll :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat" where
  [simp]: \<open>fmap_length_rll l i = length (l \<propto> i)\<close>


(*TODO rename length_rll_n_uint32*)
lemma fmap_length_rll:
  \<open>(uncurry (RETURN oo (\<lambda>(N, _) j. length_rll N j)), uncurry (RETURN oo fmap_length_rll))
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


sepref_definition length_raa_u32_clss
  is \<open>uncurry (RETURN \<circ>\<circ> (\<lambda>(N, _) i. length_rll N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs]\<^sub>a isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref

sepref_definition length_raa_clss
  is \<open>uncurry (RETURN \<circ>\<circ> (\<lambda>(N, _) i. length_rll N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs]\<^sub>a isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref

lemma fmap_length_rll_hnr[sepref_fr_rules]:
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
qed

definition fmap_swap_ll where
  [simp]: \<open>fmap_swap_ll N i j f = (N(i \<hookrightarrow> swap (N \<propto> i) j f))\<close>

lemma swap_ll_fmap_swap_ll:
  \<open>(uncurry3 (RETURN oooo (\<lambda>(N, xs) i j k. (swap_ll N i j k, xs))), uncurry3 (RETURN oooo fmap_swap_ll))
    \<in> [\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i)]\<^sub>f
        \<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>clauses_l_fmat\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto 5 5 simp: list_fmap_rel_def Array_List_Array.swap_ll_def
      split: if_splits)

sepref_definition swap_aa_clss
  is \<open>uncurry3 (RETURN oooo (\<lambda>(N, xs) i j k. (swap_ll N i j k, xs)))\<close>
  :: \<open>[\<lambda>((((xs, _), k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k]\<^sub>a
      isasat_clauses_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> isasat_clauses_assn\<close>
  by sepref

lemma fmap_swap_ll_hnr[sepref_fr_rules]:
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
   :: \<open>bool \<Rightarrow> 'v clause_l \<Rightarrow> 'v clause_l list \<times> clause_annots \<Rightarrow> ('v clause_l list \<times> clause_annots) \<times> nat\<close>
where
\<open>append_and_length b C = (\<lambda>(N, cs).
     let k = length N in
     let b' = (if b then INIT else LEARNED, 0, 0) in
       ((op_list_append N C, op_list_append cs b'), k))\<close>

lemma extra_clause_information_upd[simp]:
  \<open>extra_clause_information (fmupd i C bc) i (ba) \<longleftrightarrow> fst ba = (if snd C then INIT else LEARNED)\<close>
  by (cases ba) (auto simp: extra_clause_information.simps)

lemma extra_clause_information_upd_irrel[simp]:
  \<open>length ba \<notin># dom_m bc \<Longrightarrow> i \<in># dom_m bc \<Longrightarrow> extra_clause_information (fmupd (length ba) C bc) i (bai) \<longleftrightarrow>
    extra_clause_information bc i (bai)\<close>
  by (cases bai)(auto simp: )

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
  done

sepref_definition append_and_length_code
  is \<open>uncurry2 (RETURN ooo append_and_length)\<close>
  :: \<open>bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a (isasat_clauses_assn)\<^sup>d \<rightarrow>\<^sub>a
       isasat_clauses_assn *a nat_assn\<close>
  unfolding append_and_length_def zero_uint32_nat_def[symmetric]
  by sepref

lemma fm_add_new_hnr[sepref_fr_rules]:
  \<open>(uncurry2 append_and_length_code, uncurry2 fm_add_new)
    \<in> bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>d \<rightarrow>\<^sub>a clauses_ll_assn *a nat_assn\<close>
  using append_and_length_code.refine[FCOMP append_and_length_fm_add_new]
  unfolding clauses_ll_assn_def by simp


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
  }\<close>

lemma append_and_length_fm_add_new_packed:
  \<open>(uncurry2 (RETURN ooo append_and_length), uncurry2 fm_add_new_packed)
     \<in> [\<lambda>((b, C), N). packed N]\<^sub>f
       bool_rel \<times>\<^sub>f (\<langle>Id\<rangle>list_rel) \<times>\<^sub>f (\<langle>Id\<rangle>clauses_l_fmat) \<rightarrow> \<langle>\<langle>Id\<rangle>clauses_l_fmat \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (force simp:  fm_add_new_at_position_def list_fmap_rel_def Let_def
      max_def nth_append append_and_length_def fm_add_new_packed_def get_fresh_index_packed_def
      RETURN_RES_refine_iff RES_RETURN_RES (* packed_def *) Max_n_upt Max_insert_Max_dom_into_packed
      Max_dom_alt_def[symmetric] Max_dom_fmupd_irrel
      intro!: RETURN_SPEC_refine
      intro: packed_in_dom_mI)

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
  \<open>(return o uint32_of_nat, RETURN o convert_to_uint32)
    \<in> [\<lambda>n. n \<le> uint32_max]\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def uint32_max_def nat_of_uint32_uint32_of_nat_id)

definition append_and_length_u32
   :: \<open>bool \<Rightarrow> 'v clause_l \<Rightarrow> 'v clause_l list \<times> clause_annots \<Rightarrow>
   (('v clause_l list \<times> clause_annots) \<times> nat) nres\<close>
  where
\<open>append_and_length_u32 b C = (\<lambda>(N, ex). do {
    ASSERT(length N \<le> uint32_max);
    let k = length N;
    let b' = (if b then INIT else LEARNED, 0, 0);
    RETURN ((op_list_append N C, op_list_append ex b'), convert_to_uint32 k)})\<close>

lemma (in -) clauses_l_fmat_not_nil[simp]:
  \<open>(([], x), bc) \<in> \<langle>Id\<rangle>clauses_l_fmat \<longleftrightarrow> False\<close>
  by (auto simp: list_fmap_rel_def)

lemma clauses_l_fmat_length:
  \<open>((ba, c), bc) \<in> \<langle>Id\<rangle>clauses_l_fmat \<Longrightarrow> length ba = Suc (Max_mset (add_mset 0 (dom_m bc)))\<close>
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
  done

sepref_definition append_and_length_u32_code
  is \<open>uncurry2 (append_and_length_u32)\<close>
  :: \<open>bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a isasat_clauses_assn\<^sup>d \<rightarrow>\<^sub>a
      isasat_clauses_assn *a uint32_nat_assn\<close>
  unfolding append_and_length_u32_def zero_uint32_nat_def[symmetric]
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
thm swap_ll_fmap_swap_ll

sepref_definition fmap_swap_ll_u64_clss
  is \<open>uncurry3 (RETURN oooo (\<lambda>(N, xs) i j k. (swap_ll N i j k, xs)))\<close>
  ::\<open>[\<lambda>((((xs, _), k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k]\<^sub>a
     (isasat_clauses_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)  \<rightarrow>
           isasat_clauses_assn\<close>
  by sepref

lemma fmap_swap_ll_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry3 fmap_swap_ll_u64_clss, uncurry3 (RETURN oooo fmap_swap_ll_u64))
     \<in> [\<lambda>(((N, i), j), k). i \<in># dom_m N \<and> j < length (N \<propto> i) \<and> k < length (N \<propto> i)]\<^sub>a
     clauses_ll_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> clauses_ll_assn\<close>
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
qed

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

lemma
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
  using increase_activity_fmap_slow.refine[FCOMP increase_activity_fmap] unfolding clauses_ll_assn_def .

end
