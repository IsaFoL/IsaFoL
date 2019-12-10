theory Array_UInt
  imports Array_List_Array WB_Word_Assn WB_More_Refinement_List
begin

lemma convert_fref:
  "WB_More_Refinement.fref = Sepref_Rules.fref"
  "WB_More_Refinement.freft = Sepref_Rules.freft"
  unfolding WB_More_Refinement.fref_def Sepref_Rules.fref_def
  by auto


subsection \<open>More about general arrays\<close>

text \<open>
  This function does not resize the array: this makes sense for our purpose, but may be not in
  general.\<close>
definition butlast_arl where
  \<open>butlast_arl = (\<lambda>(xs, i). (xs, fast_minus i 1))\<close>

lemma butlast_arl_hnr[sepref_fr_rules]:
  \<open>(return o butlast_arl, RETURN o butlast) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a (arl_assn A)\<^sup>d \<rightarrow> arl_assn A\<close>
proof -
  have [simp]: \<open>b \<le> length l' \<Longrightarrow> (take b l', x) \<in> \<langle>the_pure A\<rangle>list_rel \<Longrightarrow>
     (take (b - Suc 0) l', take (length x - Suc 0) x) \<in> \<langle>the_pure A\<rangle>list_rel\<close>
    for b l' x
    using list_rel_take[of \<open>take b l'\<close> x \<open>the_pure A\<close> \<open>b -1\<close>]
    by (auto simp: list_rel_imp_same_length[symmetric]
      butlast_conv_take min_def
      simp del: take_butlast_conv)
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: butlast_arl_def arl_assn_def hr_comp_def is_array_list_def
         butlast_conv_take
        simp del: take_butlast_conv)
qed

subsection \<open>Setup for array accesses via unsigned integer\<close>

text \<open>
  NB: not all code printing equation are defined here, but this is needed to use the (more efficient)
  array operation by avoid the conversions back and forth to infinite integer.
  \<close>

subsubsection \<open>Getters (Array accesses)\<close>

paragraph \<open>32-bit unsigned integers\<close>

definition nth_aa_u where
  \<open>nth_aa_u x L L' =  nth_aa x (nat_of_uint32 L) L'\<close>

definition nth_aa' where
  \<open>nth_aa' xs i j = do {
      x \<leftarrow> Array.nth' xs i;
      y \<leftarrow> arl_get x j;
      return y}\<close>

lemma nth_aa_u[code]:
  \<open>nth_aa_u x L L' =  nth_aa' x (integer_of_uint32 L) L'\<close>
  unfolding nth_aa_u_def nth_aa'_def nth_aa_def Array.nth'_def nat_of_uint32_code
  by auto

lemma nth_aa_uint_hnr[sepref_fr_rules]:
  fixes R :: \<open>_ \<Rightarrow> _ \<Rightarrow> assn\<close>
  assumes \<open>CONSTRAINT Sepref_Basic.is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa_u, uncurry2 (RETURN ooo nth_rll)) \<in>
       [\<lambda>((x, L), L'). L < length x \<and> L' < length (x ! L)]\<^sub>a
       (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_aa_u_def
  by sepref_to_hoare
    (use assms in \<open>sep_auto simp: uint32_nat_rel_def br_def length_ll_def nth_ll_def
     nth_rll_def\<close>)

definition nth_raa_u where
  \<open>nth_raa_u x L = nth_raa x (nat_of_uint32 L)\<close>

lemma nth_raa_uint_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_u, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_raa_u_def
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemma array_replicate_custom_hnr_u[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure A \<Longrightarrow>
   (uncurry (\<lambda>n. Array.new (nat_of_uint32 n)), uncurry (RETURN \<circ>\<circ> op_array_replicate)) \<in>
     uint32_nat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a array_assn A\<close>
  using array_replicate_custom_hnr[of A]
  unfolding hfref_def
  by (sep_auto simp: uint32_nat_assn_nat_assn_nat_of_uint32)


definition nth_u where
  \<open>nth_u xs n = nth xs (nat_of_uint32 n)\<close>

definition nth_u_code where
  \<open>nth_u_code xs n = Array.nth' xs (integer_of_uint32 n)\<close>

lemma nth_u_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure A\<close>
  shows \<open>(uncurry nth_u_code, uncurry (RETURN oo nth_u)) \<in>
     [\<lambda>(xs, n). nat_of_uint32 n < length xs]\<^sub>a (array_assn A)\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow> A\<close>
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
      (sep_auto simp: array_assn_def is_array_def
       hr_comp_def list_rel_pres_length list_rel_update param_nth A' A[symmetric] ent_refl_true
     list_rel_eq_listrel listrel_iff_nth pure_def nth_u_code_def nth_u_def Array.nth'_def
     nat_of_uint32_code)
qed

lemma array_get_hnr_u[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure A\<close>
  shows \<open>(uncurry nth_u_code,
      uncurry (RETURN \<circ>\<circ> op_list_get)) \<in> [pre_list_get]\<^sub>a (array_assn A)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> A\<close>
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
      (sep_auto simp: uint32_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
       hr_comp_def list_rel_pres_length list_rel_update param_nth A' A[symmetric] ent_refl_true
     list_rel_eq_listrel listrel_iff_nth pure_def nth_u_code_def Array.nth'_def
     nat_of_uint32_code)
qed


definition arl_get' :: "'a::heap array_list \<Rightarrow> integer \<Rightarrow> 'a Heap" where
  [code del]: "arl_get' a i = arl_get a (nat_of_integer i)"

definition arl_get_u :: "'a::heap array_list \<Rightarrow> uint32 \<Rightarrow> 'a Heap" where
  "arl_get_u \<equiv> \<lambda>a i. arl_get' a (integer_of_uint32 i)"

lemma arrayO_arl_get_u_rule[sep_heap_rules]:
  assumes i: \<open>i < length a\<close> and \<open>(i' , i) \<in> uint32_nat_rel\<close>
  shows \<open><arlO_assn (array_assn R) a ai> arl_get_u ai i' <\<lambda>r. arlO_assn_except (array_assn R) [i] a ai
   (\<lambda>r'. array_assn R (a ! i) r * \<up>(r = r' ! i))>\<close>
  using assms
  by (sep_auto simp: arl_get_u_def arl_get'_def nat_of_uint32_code[symmetric]
      uint32_nat_rel_def br_def)


definition arl_get_u' where
  [symmetric, code]: \<open>arl_get_u' = arl_get_u\<close>

code_printing constant arl_get_u' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ (fst (_),/ Word32.toInt (_)))"

lemma arl_get'_nth'[code]: \<open>arl_get' = (\<lambda>(a, n). Array.nth' a)\<close>
  unfolding arl_get_def arl_get'_def Array.nth'_def
  by (intro ext) auto

lemma arl_get_hnr_u[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure A\<close>
  shows \<open>(uncurry arl_get_u, uncurry (RETURN \<circ>\<circ> op_list_get))
     \<in> [pre_list_get]\<^sub>a (arl_assn A)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> A\<close>
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
      (sep_auto simp: uint32_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
        hr_comp_def list_rel_pres_length list_rel_update param_nth arl_assn_def
        A' A[symmetric] pure_def arl_get_u_def Array.nth'_def arl_get'_def
     nat_of_uint32_code[symmetric])
qed


definition nth_rll_nu where
  \<open>nth_rll_nu = nth_rll\<close>

definition nth_raa_u' where
  \<open>nth_raa_u' xs x L =  nth_raa xs x (nat_of_uint32 L)\<close>

lemma nth_raa_u'_uint_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_u', uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_raa_u_def
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nth_raa_u'_def)

lemma nth_nat_of_uint32_nth': \<open>Array.nth x (nat_of_uint32 L) = Array.nth' x (integer_of_uint32 L)\<close>
  by (auto simp: Array.nth'_def nat_of_uint32_code)

lemma nth_aa_u_code[code]:
  \<open>nth_aa_u x L L' = nth_u_code x L \<bind> (\<lambda>x. arl_get x L' \<bind> return)\<close>
  unfolding nth_aa_u_def nth_aa_def arl_get_u_def[symmetric]  Array.nth'_def[symmetric]
   nth_nat_of_uint32_nth' nth_u_code_def[symmetric] ..

definition nth_aa_i64_u32 where
  \<open>nth_aa_i64_u32 xs x L =  nth_aa xs (nat_of_uint64 x) (nat_of_uint32 L)\<close>

lemma nth_aa_i64_u32_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa_i64_u32, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_aa_i64_u32_def
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def nth_raa_u'_def uint64_nat_rel_def
      length_rll_def length_ll_def nth_rll_def nth_ll_def)

definition nth_aa_i64_u64 where
  \<open>nth_aa_i64_u64 xs x L =  nth_aa xs (nat_of_uint64 x) (nat_of_uint64 L)\<close>

lemma nth_aa_i64_u64_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa_i64_u64, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_aa_i64_u64_def
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare
    (sep_auto simp: br_def nth_raa_u'_def uint64_nat_rel_def
      length_rll_def length_ll_def nth_rll_def nth_ll_def)

definition nth_aa_i32_u64 where
  \<open>nth_aa_i32_u64 xs x L = nth_aa xs (nat_of_uint32 x) (nat_of_uint64 L)\<close>

lemma nth_aa_i32_u64_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa_i32_u64, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_aa_i32_u64_def
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def nth_raa_u'_def uint64_nat_rel_def
      length_rll_def length_ll_def nth_rll_def nth_ll_def)


paragraph \<open>64-bit unsigned integers\<close>

definition nth_u64 where
  \<open>nth_u64 xs n = nth xs (nat_of_uint64 n)\<close>

definition nth_u64_code where
  \<open>nth_u64_code xs n = Array.nth' xs (integer_of_uint64 n)\<close>

lemma nth_u64_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure A\<close>
  shows \<open>(uncurry nth_u64_code, uncurry (RETURN oo nth_u64)) \<in>
     [\<lambda>(xs, n). nat_of_uint64 n < length xs]\<^sub>a (array_assn A)\<^sup>k *\<^sub>a uint64_assn\<^sup>k \<rightarrow> A\<close>
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
      (sep_auto simp: array_assn_def is_array_def
        hr_comp_def list_rel_pres_length list_rel_update param_nth A' A[symmetric] ent_refl_true
        list_rel_eq_listrel listrel_iff_nth pure_def nth_u64_code_def Array.nth'_def
        nat_of_uint64_code nth_u64_def)
qed

lemma array_get_hnr_u64[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure A\<close>
  shows \<open>(uncurry nth_u64_code,
      uncurry (RETURN \<circ>\<circ> op_list_get)) \<in> [pre_list_get]\<^sub>a (array_assn A)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> A\<close>
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
        hr_comp_def list_rel_pres_length list_rel_update param_nth A' A[symmetric] ent_refl_true
        list_rel_eq_listrel listrel_iff_nth pure_def nth_u64_code_def Array.nth'_def
        nat_of_uint64_code)
qed


subsubsection \<open>Setters\<close>

paragraph \<open>32-bits\<close>

definition heap_array_set'_u where
  \<open>heap_array_set'_u a i x = Array.upd' a (integer_of_uint32 i) x\<close>

definition heap_array_set_u where
  \<open>heap_array_set_u a i x = heap_array_set'_u a i x \<then> return a\<close>

lemma array_set_hnr_u[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure A \<Longrightarrow>
    (uncurry2 heap_array_set_u, uncurry2 (RETURN \<circ>\<circ>\<circ> op_list_set)) \<in>
     [pre_list_set]\<^sub>a (array_assn A)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow> array_assn A\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
      hr_comp_def list_rel_pres_length list_rel_update heap_array_set'_u_def
      heap_array_set_u_def Array.upd'_def
     nat_of_uint32_code[symmetric])

definition update_aa_u where
  \<open>update_aa_u xs i j = update_aa xs (nat_of_uint32 i) j\<close>

lemma Array_upd_upd': \<open>Array.upd i x a = Array.upd' a (of_nat i) x \<then> return a\<close>
  by (auto simp: Array.upd'_def upd_return)

definition Array_upd_u where
  \<open>Array_upd_u i x a = Array.upd (nat_of_uint32 i) x a\<close>


lemma Array_upd_u_code[code]: \<open>Array_upd_u i x a = heap_array_set'_u a i x \<then> return a\<close>
  unfolding Array_upd_u_def heap_array_set'_u_def
  Array.upd'_def
  by (auto simp: nat_of_uint32_code upd_return)

lemma update_aa_u_code[code]:
  \<open>update_aa_u a i j y = do {
      x \<leftarrow> nth_u_code a i;
      a' \<leftarrow> arl_set x j y;
      Array_upd_u i a' a
    }\<close>
  unfolding update_aa_u_def update_aa_def nth_nat_of_uint32_nth' nth_nat_of_uint32_nth'
    arl_get_u_def[symmetric] nth_u_code_def[symmetric]
    heap_array_set'_u_def[symmetric] Array_upd_u_def[symmetric]
  by auto


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


paragraph \<open>64-bits\<close>

definition heap_array_set'_u64 where
  \<open>heap_array_set'_u64 a i x = Array.upd' a (integer_of_uint64 i) x\<close>

definition heap_array_set_u64 where
  \<open>heap_array_set_u64 a i x = heap_array_set'_u64 a i x \<then> return a\<close>

lemma array_set_hnr_u64[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure A \<Longrightarrow>
    (uncurry2 heap_array_set_u64, uncurry2 (RETURN \<circ>\<circ>\<circ> op_list_set)) \<in>
     [pre_list_set]\<^sub>a (array_assn A)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow> array_assn A\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
      hr_comp_def list_rel_pres_length list_rel_update heap_array_set'_u64_def
      heap_array_set_u64_def Array.upd'_def
     nat_of_uint64_code[symmetric])

definition arl_set'_u64 where
  \<open>arl_set'_u64 a i x = arl_set a (nat_of_uint64 i) x\<close>

definition arl_set_u64 :: \<open>'a::heap array_list \<Rightarrow> uint64 \<Rightarrow> 'a \<Rightarrow> 'a array_list Heap\<close>where
  \<open>arl_set_u64 a i x = arl_set'_u64 a i x\<close>

lemma arl_set_hnr_u64[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure A \<Longrightarrow>
    (uncurry2 arl_set_u64, uncurry2 (RETURN \<circ>\<circ>\<circ> op_list_set)) \<in>
     [pre_list_set]\<^sub>a (arl_assn A)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow> arl_assn A\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
      hr_comp_def list_rel_pres_length list_rel_update heap_array_set'_u_def
      heap_array_set_u_def Array.upd'_def arl_set_u64_def arl_set'_u64_def arl_assn_def
     nat_of_uint64_code[symmetric])

lemma nth_nat_of_uint64_nth': \<open>Array.nth x (nat_of_uint64 L) = Array.nth' x (integer_of_uint64 L)\<close>
  by (auto simp: Array.nth'_def nat_of_uint64_code)


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

definition arl_get_u64 :: "'a::heap array_list \<Rightarrow> uint64 \<Rightarrow> 'a Heap" where
  "arl_get_u64 \<equiv> \<lambda>a i. arl_get' a (integer_of_uint64 i)"


lemma arl_get_hnr_u64[sepref_fr_rules]:
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

lemma nth_raa_u64'_uint_hnr[sepref_fr_rules]:
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

lemma heap_array_set_u64_upd:
  \<open>heap_array_set_u64 x j xi = Array.upd (nat_of_uint64 j) xi x \<bind> (\<lambda>xa. return x) \<close>
  by (auto simp:  heap_array_set_u64_def heap_array_set'_u64_def
     Array.upd'_def nat_of_uint64_code[symmetric])


subsubsection \<open>Append (32 bit integers only)\<close>

definition append_el_aa_u' :: "('a::{default,heap} array_list) array \<Rightarrow>
  uint32 \<Rightarrow> 'a \<Rightarrow> ('a array_list) array Heap"where
"append_el_aa_u' \<equiv> \<lambda>a i x.
   Array.nth' a (integer_of_uint32 i) \<bind>
   (\<lambda>j. arl_append j x \<bind>
        (\<lambda>a'. Array.upd' a (integer_of_uint32 i) a' \<bind> (\<lambda>_. return a)))"

lemma append_el_aa_append_el_aa_u':
  \<open>append_el_aa xs (nat_of_uint32 i) j = append_el_aa_u' xs i j\<close>
  unfolding append_el_aa_def append_el_aa_u'_def Array.nth'_def nat_of_uint32_code Array.upd'_def
  by (auto simp add: upd'_def upd_return max_def)


lemma append_aa_hnr_u:
  fixes R ::  \<open>'a \<Rightarrow> 'b :: {heap, default} \<Rightarrow> assn\<close>
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 (\<lambda>xs i. append_el_aa xs (nat_of_uint32 i)), uncurry2 (RETURN \<circ>\<circ>\<circ> (\<lambda>xs i. append_ll xs (nat_of_uint32 i)))) \<in>
     [\<lambda>((l,i),x). nat_of_uint32 i < length l]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a uint32_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> (arrayO_assn (arl_assn R))\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have [simp]: \<open>(\<exists>\<^sub>Ax. arrayO_assn (arl_assn R) a ai * R x r * true * \<up> (x = a ! ba ! b)) =
     (arrayO_assn (arl_assn R) a ai * R (a ! ba ! b) r * true)\<close> for a ai ba b r
    by (auto simp: ex_assn_def)
  show ?thesis \<comment> \<open>TODO tune proof\<close>
    apply sepref_to_hoare
    apply (sep_auto simp: append_el_aa_def uint32_nat_rel_def br_def)
     apply (simp add: arrayO_except_assn_def)
     apply (rule sep_auto_is_stupid[OF p])
    apply (sep_auto simp: array_assn_def is_array_def append_ll_def)
    apply (simp add: arrayO_except_assn_array0[symmetric] arrayO_except_assn_def)
    apply (subst_tac (2) i = \<open>nat_of_uint32 ba\<close> in heap_list_all_nth_remove1)
     apply (solves \<open>simp\<close>)
    apply (simp add: array_assn_def is_array_def)
    apply (rule_tac x=\<open>p[nat_of_uint32 ba := (ab, bc)]\<close> in ent_ex_postI)
    apply (subst_tac (2)xs'=a and ys'=p in heap_list_all_nth_cong)
      apply (solves \<open>auto\<close>)[2]
    apply (auto simp: star_aci)
    done
qed

lemma append_el_aa_hnr'[sepref_fr_rules]:
  shows \<open>(uncurry2 append_el_aa_u', uncurry2 (RETURN ooo append_ll))
     \<in> [\<lambda>((W,L), j). L < length W]\<^sub>a
        (arrayO_assn (arl_assn nat_assn))\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> (arrayO_assn (arl_assn nat_assn))\<close>
    (is \<open>?a \<in> [?pre]\<^sub>a ?init \<rightarrow> ?post\<close>)
  using append_aa_hnr_u[of nat_assn, simplified] unfolding hfref_def uint32_nat_rel_def br_def pure_def
   hn_refine_def append_el_aa_append_el_aa_u'
  by auto

lemma append_el_aa_uint32_hnr'[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(uncurry2 append_el_aa_u', uncurry2 (RETURN ooo append_ll))
     \<in> [\<lambda>((W,L), j). L < length W]\<^sub>a
        (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow>
       (arrayO_assn (arl_assn R))\<close>
    (is \<open>?a \<in> [?pre]\<^sub>a ?init \<rightarrow> ?post\<close>)
  using append_aa_hnr_u[of R, simplified] assms
   unfolding hfref_def uint32_nat_rel_def br_def pure_def
   hn_refine_def append_el_aa_append_el_aa_u'
  by auto


lemma append_el_aa_u'_code[code]:
  "append_el_aa_u' = (\<lambda>a i x. nth_u_code a i \<bind>
     (\<lambda>j. arl_append j x \<bind>
      (\<lambda>a'. heap_array_set'_u a i a' \<bind> (\<lambda>_. return a))))"
  unfolding append_el_aa_u'_def nth_u_code_def heap_array_set'_u_def
  by auto


definition update_raa_u32 where
\<open>update_raa_u32 a i j y = do {
  x \<leftarrow> arl_get_u a i;
  Array.upd j y x \<bind> arl_set_u a i
}\<close>


lemma update_raa_u32_rule[sep_heap_rules]:
  assumes p: \<open>is_pure R\<close> and \<open>bb < length a\<close> and \<open>ba < length_rll a bb\<close> and
     \<open>(bb', bb) \<in> uint32_nat_rel\<close>
  shows \<open><R b bi * arlO_assn (array_assn R) a ai> update_raa_u32 ai bb' ba bi
      <\<lambda>r. R b bi * (\<exists>\<^sub>Ax. arlO_assn (array_assn R) x r * \<up> (x = update_rll a bb ba b))>\<^sub>t\<close>
  using assms
  apply (cases ai)
  apply (sep_auto simp add: update_raa_u32_def update_rll_def p)
  apply (sep_auto simp add: update_raa_u32_def arlO_assn_except_def array_assn_def hr_comp_def
      arl_assn_def arl_set_u_def arl_set'_u_def)
   apply (solves \<open>simp add: br_def uint32_nat_rel_def\<close>)
  apply (rule_tac x=\<open>a[bb := (a ! bb)[ba := b]]\<close> in ent_ex_postI)
  apply (subst_tac i=bb in arlO_assn_except_array0_index[symmetric])
  apply (auto simp add: br_def uint32_nat_rel_def)[]

  apply (auto simp add: update_raa_def arlO_assn_except_def array_assn_def is_array_def hr_comp_def)
  apply (rule_tac x=\<open>p[bb := xa]\<close> in ent_ex_postI)
  apply (rule_tac x=\<open>baa\<close> in ent_ex_postI)
  apply (subst_tac (2)xs'=a and ys'=p in heap_list_all_nth_cong)
    apply (solves \<open>auto\<close>)
   apply (solves \<open>auto\<close>)
  by (sep_auto simp: arl_assn_def uint32_nat_rel_def br_def)


lemma update_raa_u32_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry3 update_raa_u32, uncurry3 (RETURN oooo update_rll)) \<in>
     [\<lambda>(((l,i), j), x). i < length l \<and> j < length_rll l i]\<^sub>a (arlO_assn (array_assn R))\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> (arlO_assn (array_assn R))\<close>
  by sepref_to_hoare (sep_auto simp: assms)

lemma update_aa_u_rule[sep_heap_rules]:
  assumes p: \<open>is_pure R\<close> and \<open>bb < length a\<close> and \<open>ba < length_ll a bb\<close> and \<open>(bb', bb) \<in> uint32_nat_rel\<close>
  shows \<open><R b bi * arrayO_assn (arl_assn R) a ai> update_aa_u ai bb' ba bi
      <\<lambda>r. R b bi * (\<exists>\<^sub>Ax. arrayO_assn (arl_assn R) x r * \<up> (x = update_ll a bb ba b))>\<^sub>t\<close>
      solve_direct
  using assms
  by (sep_auto simp add: update_aa_u_def update_ll_def p uint32_nat_rel_def br_def)

lemma update_aa_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry3 update_aa_u, uncurry3 (RETURN oooo update_ll)) \<in>
     [\<lambda>(((l,i), j), x). i < length l \<and> j < length_ll l i]\<^sub>a
      (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> (arrayO_assn (arl_assn R))\<close>
  by sepref_to_hoare (sep_auto simp: assms)


subsubsection \<open>Length\<close>

paragraph \<open>32-bits\<close>

definition (in -)length_u_code where
  \<open>length_u_code C = do { n \<leftarrow> Array.len C; return (uint32_of_nat n)}\<close>

lemma (in -)length_u_hnr[sepref_fr_rules]:
  \<open>(length_u_code, RETURN o length_uint32_nat) \<in> [\<lambda>C. length C \<le> uint32_max]\<^sub>a (array_assn R)\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  supply length_rule[sep_heap_rules]
  by sepref_to_hoare
    (sep_auto simp: length_u_code_def array_assn_def hr_comp_def is_array_def
      uint32_nat_rel_def list_rel_imp_same_length br_def nat_of_uint32_uint32_of_nat_id)

definition length_arl_u_code :: \<open>('a::heap) array_list \<Rightarrow> uint32 Heap\<close> where
  \<open>length_arl_u_code xs = do {
   n \<leftarrow> arl_length xs;
   return (uint32_of_nat n)}\<close>

lemma length_arl_u_hnr[sepref_fr_rules]:
  \<open>(length_arl_u_code, RETURN o length_uint32_nat) \<in>
     [\<lambda>xs. length xs \<le> uint32_max]\<^sub>a (arl_assn R)\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: length_u_code_def nat_of_uint32_uint32_of_nat_id
      length_arl_u_code_def arl_assn_def
      arl_length_def hr_comp_def is_array_list_def list_rel_pres_length[symmetric]
      uint32_nat_rel_def br_def)


paragraph \<open>64-bits\<close>

definition (in -)length_u64_code where
  \<open>length_u64_code C = do { n \<leftarrow> Array.len C; return (uint64_of_nat n)}\<close>


lemma (in -)length_u64_hnr[sepref_fr_rules]:
  \<open>(length_u64_code, RETURN o length_uint64_nat)
   \<in> [\<lambda>C. length C \<le> uint64_max]\<^sub>a (array_assn R)\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  supply length_rule[sep_heap_rules]
  by sepref_to_hoare
    (sep_auto simp: length_u_code_def array_assn_def hr_comp_def is_array_def length_u64_code_def
      uint64_nat_rel_def list_rel_imp_same_length br_def nat_of_uint64_uint64_of_nat_id)

subsubsection \<open>Length for arrays in arrays\<close>

paragraph \<open>32-bits\<close>

definition (in -)length_aa_u :: \<open>('a::heap array_list) array \<Rightarrow> uint32 \<Rightarrow> nat Heap\<close> where
  \<open>length_aa_u xs i = length_aa xs (nat_of_uint32 i)\<close>

lemma length_aa_u_code[code]:
  \<open>length_aa_u xs i = nth_u_code xs i \<bind> arl_length\<close>
  unfolding length_aa_u_def length_aa_def nth_u_def[symmetric] nth_u_code_def
   Array.nth'_def
  by (auto simp: nat_of_uint32_code)

lemma length_aa_u_hnr[sepref_fr_rules]: \<open>(uncurry length_aa_u, uncurry (RETURN \<circ>\<circ> length_ll)) \<in>
     [\<lambda>(xs, i). i < length xs]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def length_aa_u_def br_def)


definition length_raa_u :: \<open>'a::heap arrayO_raa \<Rightarrow> nat \<Rightarrow> uint32 Heap\<close> where
  \<open>length_raa_u xs i = do {
     x \<leftarrow> arl_get xs i;
    length_u_code x}\<close>

lemma length_raa_u_alt_def: \<open>length_raa_u xs i = do {
    n \<leftarrow> length_raa xs i;
    return (uint32_of_nat n)}\<close>
  unfolding length_raa_u_def length_raa_def length_u_code_def
  by auto

definition length_rll_n_uint32 where
  [simp]: \<open>length_rll_n_uint32 = length_rll\<close>

lemma length_raa_rule[sep_heap_rules]:
  \<open>b < length xs \<Longrightarrow> <arlO_assn (array_assn R) xs a> length_raa_u a b
   <\<lambda>r. arlO_assn (array_assn R) xs a * \<up> (r = uint32_of_nat (length_rll xs b))>\<^sub>t\<close>
  unfolding length_raa_u_alt_def length_u_code_def
  by sep_auto

lemma length_raa_u_hnr[sepref_fr_rules]:
  shows \<open>(uncurry length_raa_u, uncurry (RETURN \<circ>\<circ> length_rll_n_uint32)) \<in>
     [\<lambda>(xs, i). i < length xs \<and> length (xs ! i) \<le> uint32_max]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def length_rll_def
      nat_of_uint32_uint32_of_nat_id)+

text \<open>TODO: proper fix to avoid the conversion to uint32\<close>
definition length_aa_u_code :: \<open>('a::heap array) array_list \<Rightarrow> nat \<Rightarrow> uint32 Heap\<close> where
  \<open>length_aa_u_code xs i = do {
   n \<leftarrow> length_raa xs i;
   return (uint32_of_nat n)}\<close>



paragraph \<open>64-bits\<close>

definition (in -)length_aa_u64 :: \<open>('a::heap array_list) array \<Rightarrow> uint64 \<Rightarrow> nat Heap\<close> where
  \<open>length_aa_u64 xs i = length_aa xs (nat_of_uint64 i)\<close>

lemma length_aa_u64_code[code]:
  \<open>length_aa_u64 xs i = nth_u64_code xs i \<bind> arl_length\<close>
  unfolding length_aa_u64_def length_aa_def nth_u64_def[symmetric] nth_u64_code_def
   Array.nth'_def
  by (auto simp: nat_of_uint64_code)

lemma length_aa_u64_hnr[sepref_fr_rules]: \<open>(uncurry length_aa_u64, uncurry (RETURN \<circ>\<circ> length_ll)) \<in>
     [\<lambda>(xs, i). i < length xs]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def length_aa_u64_def br_def)

definition length_raa_u64 :: \<open>'a::heap arrayO_raa \<Rightarrow> nat \<Rightarrow> uint64 Heap\<close> where
  \<open>length_raa_u64 xs i = do {
     x \<leftarrow> arl_get xs i;
    length_u64_code x}\<close>

lemma length_raa_u64_alt_def: \<open>length_raa_u64 xs i = do {
    n \<leftarrow> length_raa xs i;
    return (uint64_of_nat n)}\<close>
  unfolding length_raa_u64_def length_raa_def length_u64_code_def
  by auto


definition length_rll_n_uint64 where
  [simp]: \<open>length_rll_n_uint64 = length_rll\<close>


lemma length_raa_u64_hnr[sepref_fr_rules]:
  shows \<open>(uncurry length_raa_u64, uncurry (RETURN \<circ>\<circ> length_rll_n_uint64)) \<in>
     [\<lambda>(xs, i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare  (sep_auto simp: uint64_nat_rel_def br_def length_rll_def
      nat_of_uint64_uint64_of_nat_id length_raa_u64_alt_def)+


subsubsection \<open>Delete at index\<close>

definition delete_index_and_swap_aa where
  \<open>delete_index_and_swap_aa xs i j = do {
     x \<leftarrow> last_aa xs i;
     xs \<leftarrow> update_aa xs i j x;
     set_butlast_aa xs i
  }\<close>

lemma delete_index_and_swap_aa_ll_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry2 delete_index_and_swap_aa, uncurry2 (RETURN ooo delete_index_and_swap_ll))
     \<in> [\<lambda>((l,i), j). i < length l \<and> j < length_ll l i]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k
         \<rightarrow> (arrayO_assn (arl_assn R))\<close>
  using assms unfolding delete_index_and_swap_aa_def
  by sepref_to_hoare (sep_auto dest: le_length_ll_nemptyD
      simp: delete_index_and_swap_ll_def update_ll_def last_ll_def set_butlast_ll_def
      length_ll_def[symmetric])


subsubsection \<open>Last (arrays of arrays)\<close>

definition last_aa_u where
  \<open>last_aa_u xs i = last_aa xs (nat_of_uint32 i)\<close>

lemma last_aa_u_code[code]:
  \<open>last_aa_u xs i = nth_u_code xs i \<bind> arl_last\<close>
  unfolding last_aa_u_def last_aa_def nth_nat_of_uint32_nth' nth_nat_of_uint32_nth'
    arl_get_u_def[symmetric] nth_u_code_def[symmetric] ..

lemma length_delete_index_and_swap_ll[simp]:
  \<open>length (delete_index_and_swap_ll s i j) = length s\<close>
  by (auto simp: delete_index_and_swap_ll_def)

definition set_butlast_aa_u where
  \<open>set_butlast_aa_u xs i = set_butlast_aa xs (nat_of_uint32 i)\<close>

lemma set_butlast_aa_u_code[code]:
  \<open>set_butlast_aa_u a i = do {
      x \<leftarrow> nth_u_code a i;
      a' \<leftarrow> arl_butlast x;
      Array_upd_u i a' a
    }\<close> \<comment> \<open>Replace the \<^term>\<open>i\<close>-th element by the itself execpt the last element.\<close>
  unfolding set_butlast_aa_u_def set_butlast_aa_def
   nth_u_code_def Array_upd_u_def
  by (auto simp: Array.nth'_def nat_of_uint32_code)


definition delete_index_and_swap_aa_u where
   \<open>delete_index_and_swap_aa_u xs i = delete_index_and_swap_aa xs (nat_of_uint32 i)\<close>

lemma delete_index_and_swap_aa_u_code[code]:
\<open>delete_index_and_swap_aa_u xs i j = do {
     x \<leftarrow> last_aa_u xs i;
     xs \<leftarrow> update_aa_u xs i j x;
     set_butlast_aa_u xs i
  }\<close>
  unfolding delete_index_and_swap_aa_u_def delete_index_and_swap_aa_def
   last_aa_u_def update_aa_u_def set_butlast_aa_u_def
  by auto

lemma delete_index_and_swap_aa_ll_hnr_u[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry2 delete_index_and_swap_aa_u, uncurry2 (RETURN ooo delete_index_and_swap_ll))
     \<in> [\<lambda>((l,i), j). i < length l \<and> j < length_ll l i]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k
         \<rightarrow> (arrayO_assn (arl_assn R))\<close>
  using assms unfolding delete_index_and_swap_aa_def delete_index_and_swap_aa_u_def
  by sepref_to_hoare (sep_auto dest: le_length_ll_nemptyD
      simp: delete_index_and_swap_ll_def update_ll_def last_ll_def set_butlast_ll_def
      length_ll_def[symmetric] uint32_nat_rel_def br_def)


subsubsection \<open>Swap\<close>

definition swap_u_code :: "'a ::heap array \<Rightarrow> uint32 \<Rightarrow> uint32 \<Rightarrow> 'a array Heap" where
  \<open>swap_u_code xs i j = do {
     ki \<leftarrow> nth_u_code xs i;
     kj \<leftarrow> nth_u_code xs j;
     xs \<leftarrow> heap_array_set_u xs i kj;
     xs \<leftarrow> heap_array_set_u xs j ki;
     return xs
  }\<close>


lemma op_list_swap_u_hnr[sepref_fr_rules]:
  assumes p: \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(uncurry2 swap_u_code, uncurry2 (RETURN ooo op_list_swap)) \<in>
       [\<lambda>((xs, i), j).  i < length xs \<and> j < length xs]\<^sub>a
      (array_assn R)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k  *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> array_assn R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  show ?thesis
    by (sepref_to_hoare)
     (sep_auto simp: swap_u_code_def swap_def nth_u_code_def is_array_def
      array_assn_def hr_comp_def nth_nat_of_uint32_nth'[symmetric]
      list_rel_imp_same_length uint32_nat_rel_def br_def
      heap_array_set_u_def heap_array_set'_u_def Array.upd'_def
      nat_of_uint32_code[symmetric] R IICF_List.swap_def[symmetric] IICF_List.swap_param
      intro!: list_rel_update[of _ _ R true _ _ \<open>(_, {})\<close>, unfolded R] param_nth)
qed

definition swap_u64_code :: "'a ::heap array \<Rightarrow> uint64 \<Rightarrow> uint64 \<Rightarrow> 'a array Heap" where
  \<open>swap_u64_code xs i j = do {
     ki \<leftarrow> nth_u64_code xs i;
     kj \<leftarrow> nth_u64_code xs j;
     xs \<leftarrow> heap_array_set_u64 xs i kj;
     xs \<leftarrow> heap_array_set_u64 xs j ki;
     return xs
  }\<close>


lemma op_list_swap_u64_hnr[sepref_fr_rules]:
  assumes p: \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(uncurry2 swap_u64_code, uncurry2 (RETURN ooo op_list_swap)) \<in>
       [\<lambda>((xs, i), j).  i < length xs \<and> j < length xs]\<^sub>a
      (array_assn R)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k  *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> array_assn R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  show ?thesis
    by (sepref_to_hoare)
    (sep_auto simp: swap_u64_code_def swap_def nth_u64_code_def is_array_def
      array_assn_def hr_comp_def nth_nat_of_uint64_nth'[symmetric]
      list_rel_imp_same_length uint64_nat_rel_def br_def
      heap_array_set_u64_def heap_array_set'_u64_def Array.upd'_def
      nat_of_uint64_code[symmetric] R IICF_List.swap_def[symmetric] IICF_List.swap_param
      intro!: list_rel_update[of _ _ R true _ _ \<open>(_, {})\<close>, unfolded R] param_nth)
qed


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
        heap_array_set_u64_def heap_array_set'_u64_def arl_assn_def IICF_List.swap_def
         Array.upd'_def)
    apply (rule H; assumption)
    apply (sep_auto simp: array_assn_def nat_of_uint64_code[symmetric] hr_comp_def is_array_def
        list_rel_imp_same_length arlO_assn_def arl_assn_def hr_comp_def[abs_def])
    apply (rule H'; assumption)
    done
qed


definition arl_swap_u_code
  :: "'a ::heap array_list \<Rightarrow> uint32 \<Rightarrow> uint32 \<Rightarrow> 'a array_list Heap"
where
  \<open>arl_swap_u_code xs i j = do {
     ki \<leftarrow> arl_get_u xs i;
     kj \<leftarrow> arl_get_u xs j;
     xs \<leftarrow> arl_set_u xs i kj;
     xs \<leftarrow> arl_set_u xs j ki;
     return xs
  }\<close>

lemma arl_op_list_swap_u_hnr[sepref_fr_rules]:
  assumes p: \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(uncurry2 arl_swap_u_code, uncurry2 (RETURN ooo op_list_swap)) \<in>
       [\<lambda>((xs, i), j).  i < length xs \<and> j < length xs]\<^sub>a
      (arl_assn R)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k  *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> arl_assn R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  show ?thesis
  by (sepref_to_hoare)
    (sep_auto simp: arl_swap_u_code_def swap_def nth_u_code_def is_array_def
      array_assn_def hr_comp_def nth_nat_of_uint32_nth'[symmetric]
      list_rel_imp_same_length uint32_nat_rel_def br_def arl_assn_def
      heap_array_set_u_def heap_array_set'_u_def Array.upd'_def
      arl_set'_u_def R R' IICF_List.swap_def[symmetric] IICF_List.swap_param
      nat_of_uint32_code[symmetric] R arl_set_u_def arl_get'_def arl_get_u_def
      intro!: list_rel_update[of _ _ R true _ _ \<open>(_, {})\<close>, unfolded R] param_nth)
qed


subsubsection \<open>Take\<close>


definition shorten_take_aa_u32 where
  \<open>shorten_take_aa_u32 L j W =  do {
      (a, n) \<leftarrow> nth_u_code W L;
      heap_array_set_u W L (a, j)
    }\<close>

lemma shorten_take_aa_u32_alt_def:
  \<open>shorten_take_aa_u32 L j W = shorten_take_aa (nat_of_uint32 L) j W\<close>
  by (auto simp: shorten_take_aa_u32_def shorten_take_aa_def uint32_nat_rel_def br_def
    Array.nth'_def heap_array_set_u_def heap_array_set'_u_def Array.upd'_def
    nth_u_code_def nat_of_uint32_code[symmetric] upd_return)

lemma shorten_take_aa_u32_hnr[sepref_fr_rules]:
  \<open>(uncurry2 shorten_take_aa_u32, uncurry2 (RETURN ooo shorten_take_ll)) \<in>
     [\<lambda>((L, j), W). j \<le> length (W ! L) \<and> L < length W]\<^sub>a
    uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arrayO_assn (arl_assn R))\<^sup>d \<rightarrow> arrayO_assn (arl_assn R)\<close>
  unfolding shorten_take_aa_u32_alt_def shorten_take_ll_def nth_u_code_def uint32_nat_rel_def br_def
    Array.nth'_def heap_array_set_u_def heap_array_set'_u_def Array.upd'_def shorten_take_aa_def
  by sepref_to_hoare (sep_auto simp: nat_of_uint32_code[symmetric])


subsubsection \<open>List of Lists\<close>

paragraph \<open>Getters\<close>

definition nth_raa_i32 :: \<open>'a::heap arrayO_raa \<Rightarrow> uint32 \<Rightarrow> nat \<Rightarrow> 'a Heap\<close> where
  \<open>nth_raa_i32 xs i j = do {
      x \<leftarrow> arl_get_u xs i;
      y \<leftarrow> Array.nth x j;
      return y}\<close>

lemma nth_raa_i32_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_i32, uncurry2 (RETURN ooo nth_rll)) \<in>
      [\<lambda>((xs, i), j). i < length xs \<and> j < length (xs !i)]\<^sub>a
      (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  have 1: \<open>a * b * array_assn R x y = array_assn R x y * a * b\<close> for a b c :: assn and x y
    by (auto simp: ac_simps)
  have 2: \<open>a * arl_assn R x y * c = arl_assn R x y * a * c\<close> for a c :: assn and x y and R
    by (auto simp: ac_simps)
  have [simp]: \<open>R a b = \<up>((b,a) \<in> the_pure R)\<close> for a b
    using assms by (metis CONSTRAINT_D pure_app_eq pure_the_pure)
  show ?thesis
    using assms
    apply sepref_to_hoare
    apply (sep_auto simp: nth_raa_i32_def arl_get_u_def
        uint32_nat_rel_def br_def nat_of_uint32_code[symmetric]
        arlO_assn_except_def 1 arl_get'_def
        )
    apply (sep_auto simp: array_assn_def hr_comp_def is_array_def list_rel_imp_same_length
        param_nth nth_rll_def)
    apply (sep_auto simp: arlO_assn_def 2 )
    apply (subst mult.assoc)+
    apply (rule fr_refl')
    apply (subst heap_list_all_heap_list_all_nth_eq)
    apply (subst_tac (2) i=\<open>nat_of_uint32 bia\<close> in heap_list_all_nth_remove1)
     apply (sep_auto simp: nth_rll_def is_array_def hr_comp_def)+
    done
qed


definition nth_raa_i32_u64 :: \<open>'a::heap arrayO_raa \<Rightarrow> uint32 \<Rightarrow> uint64 \<Rightarrow> 'a Heap\<close> where
  \<open>nth_raa_i32_u64 xs i j = do {
      x \<leftarrow> arl_get_u xs i;
      y \<leftarrow> nth_u64_code x j;
      return y}\<close>

lemma nth_raa_i32_u64_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_i32_u64, uncurry2 (RETURN ooo nth_rll)) \<in>
      [\<lambda>((xs, i), j). i < length xs \<and> j < length (xs !i)]\<^sub>a
      (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  have 1: \<open>a * b * array_assn R x y = array_assn R x y * a * b\<close> for a b c :: assn and x y
    by (auto simp: ac_simps)
  have 2: \<open>a * arl_assn R x y * c = arl_assn R x y * a * c\<close> for a c :: assn and x y and R
    by (auto simp: ac_simps)
  have [simp]: \<open>R a b = \<up>((b,a) \<in> the_pure R)\<close> for a b
    using assms by (metis CONSTRAINT_D pure_app_eq pure_the_pure)
  show ?thesis
    using assms
    apply sepref_to_hoare
    apply (sep_auto simp: nth_raa_i32_u64_def arl_get_u_def
        uint32_nat_rel_def br_def nat_of_uint32_code[symmetric]
        arlO_assn_except_def 1 arl_get'_def Array.nth'_def nth_u64_code_def
        nat_of_uint64_code[symmetric] uint64_nat_rel_def)
    apply (sep_auto simp: array_assn_def hr_comp_def is_array_def list_rel_imp_same_length
        param_nth nth_rll_def)
    apply (sep_auto simp: arlO_assn_def 2 )
    apply (subst mult.assoc)+
    apply (rule fr_refl')
    apply (subst heap_list_all_heap_list_all_nth_eq)
    apply (subst_tac (2) i=\<open>nat_of_uint32 bia\<close> in heap_list_all_nth_remove1)
     apply (sep_auto simp: nth_rll_def is_array_def hr_comp_def)+
    done
qed

definition nth_raa_i32_u32 :: \<open>'a::heap arrayO_raa \<Rightarrow> uint32 \<Rightarrow> uint32 \<Rightarrow> 'a Heap\<close> where
  \<open>nth_raa_i32_u32 xs i j = do {
      x \<leftarrow> arl_get_u xs i;
      y \<leftarrow> nth_u_code x j;
      return y}\<close>

lemma nth_raa_i32_u32_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_i32_u32, uncurry2 (RETURN ooo nth_rll)) \<in>
      [\<lambda>((xs, i), j). i < length xs \<and> j < length (xs !i)]\<^sub>a
      (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  have 1: \<open>a * b * array_assn R x y = array_assn R x y * a * b\<close> for a b c :: assn and x y
    by (auto simp: ac_simps)
  have 2: \<open>a * arl_assn R x y * c = arl_assn R x y * a * c\<close> for a c :: assn and x y and R
    by (auto simp: ac_simps)
  have [simp]: \<open>R a b = \<up>((b,a) \<in> the_pure R)\<close> for a b
    using assms by (metis CONSTRAINT_D pure_app_eq pure_the_pure)
  show ?thesis
    using assms
    apply sepref_to_hoare
    apply (sep_auto simp: nth_raa_i32_u32_def arl_get_u_def
        uint32_nat_rel_def br_def nat_of_uint32_code[symmetric]
        arlO_assn_except_def 1 arl_get'_def Array.nth'_def nth_u_code_def
        nat_of_uint32_code[symmetric] uint32_nat_rel_def)
    apply (sep_auto simp: array_assn_def hr_comp_def is_array_def list_rel_imp_same_length
        param_nth nth_rll_def)
    apply (sep_auto simp: arlO_assn_def 2 )
    apply (subst mult.assoc)+
    apply (rule fr_refl')
    apply (subst heap_list_all_heap_list_all_nth_eq)
    apply (subst_tac (2) i=\<open>nat_of_uint32 bia\<close> in heap_list_all_nth_remove1)
     apply (sep_auto simp: nth_rll_def is_array_def hr_comp_def)+
    done
qed


definition nth_aa_i32_u32 where
  \<open>nth_aa_i32_u32 x L L' =  nth_aa x (nat_of_uint32 L) (nat_of_uint32 L')\<close>

definition nth_aa_i32_u32' where
  \<open>nth_aa_i32_u32' xs i j = do {
      x \<leftarrow> nth_u_code xs i;
      y \<leftarrow> arl_get_u x j;
      return y}\<close>

lemma nth_aa_i32_u32[code]:
  \<open>nth_aa_i32_u32 x L L' =  nth_aa_i32_u32' x L L'\<close>
  unfolding nth_aa_u_def nth_aa'_def nth_aa_def Array.nth'_def nat_of_uint32_code
  nth_aa_i32_u32_def nth_aa_i32_u32'_def nth_u_code_def arl_get_u_def arl_get'_def
  by (auto simp: nat_of_uint32_code[symmetric])

lemma nth_aa_i32_u32_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa_i32_u32, uncurry2 (RETURN ooo nth_rll)) \<in>
       [\<lambda>((x, L), L'). L < length x \<and> L' < length (x ! L)]\<^sub>a
       (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_aa_i32_u32_def
  by sepref_to_hoare
    (use assms in \<open>sep_auto simp: uint32_nat_rel_def br_def length_ll_def nth_ll_def
     nth_rll_def\<close>)


definition nth_raa_i64_u32 :: \<open>'a::heap arrayO_raa \<Rightarrow> uint64 \<Rightarrow> uint32 \<Rightarrow> 'a Heap\<close> where
  \<open>nth_raa_i64_u32 xs i j = do {
      x \<leftarrow> arl_get_u64 xs i;
      y \<leftarrow> nth_u_code x j;
      return y}\<close>

lemma nth_raa_i64_u32_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_i64_u32, uncurry2 (RETURN ooo nth_rll)) \<in>
      [\<lambda>((xs, i), j). i < length xs \<and> j < length (xs !i)]\<^sub>a
      (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  have 1: \<open>a * b * array_assn R x y = array_assn R x y * a * b\<close> for a b c :: assn and x y
    by (auto simp: ac_simps)
  have 2: \<open>a * arl_assn R x y * c = arl_assn R x y * a * c\<close> for a c :: assn and x y and R
    by (auto simp: ac_simps)
  have [simp]: \<open>R a b = \<up>((b,a) \<in> the_pure R)\<close> for a b
    using assms by (metis CONSTRAINT_D pure_app_eq pure_the_pure)
  show ?thesis
    using assms
    apply sepref_to_hoare
    apply (sep_auto simp: nth_raa_i64_u32_def arl_get_u64_def
        uint32_nat_rel_def br_def nat_of_uint32_code[symmetric]
        arlO_assn_except_def 1 arl_get'_def Array.nth'_def nth_u64_code_def
        nat_of_uint64_code[symmetric] uint64_nat_rel_def nth_u_code_def)
    apply (sep_auto simp: array_assn_def hr_comp_def is_array_def list_rel_imp_same_length
        param_nth nth_rll_def)
    apply (sep_auto simp: arlO_assn_def 2)
    apply (subst mult.assoc)+
    apply (rule fr_refl')
    apply (subst heap_list_all_heap_list_all_nth_eq)
    apply (subst_tac (2) i=\<open>nat_of_uint64 bia\<close> in heap_list_all_nth_remove1)
     apply (sep_auto simp: nth_rll_def is_array_def hr_comp_def)+
    done
qed

thm nth_aa_uint_hnr
find_theorems nth_aa_u

lemma nth_aa_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_ll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_ll l i]\<^sub>a
       (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have H: \<open>list_all2 (\<lambda>x x'. (x, x') \<in> the_pure (\<lambda>a c. \<up> ((c, a) \<in> R'))) bc (a ! ba) \<Longrightarrow>
       b < length (a ! ba) \<Longrightarrow>
       (bc ! b, a ! ba ! b) \<in> R'\<close> for bc a ba b
    by (auto simp add: ent_refl_true list_all2_conv_all_nth is_pure_alt_def pure_app_eq[symmetric])
  show ?thesis
  apply sepref_to_hoare
  apply (subst (2) arrayO_except_assn_array0_index[symmetric])
    apply (solves \<open>auto\<close>)[]
  apply (sep_auto simp: nth_aa_def nth_ll_def length_ll_def)
    apply (sep_auto simp: arrayO_except_assn_def arrayO_assn_def arl_assn_def hr_comp_def list_rel_def
        list_all2_lengthD
      star_aci(3) R R' pure_def H)
    done
qed

definition nth_raa_i64_u64 :: \<open>'a::heap arrayO_raa \<Rightarrow> uint64 \<Rightarrow> uint64 \<Rightarrow> 'a Heap\<close> where
  \<open>nth_raa_i64_u64 xs i j = do {
      x \<leftarrow> arl_get_u64 xs i;
      y \<leftarrow> nth_u64_code x j;
      return y}\<close>

lemma nth_raa_i64_u64_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_i64_u64, uncurry2 (RETURN ooo nth_rll)) \<in>
      [\<lambda>((xs, i), j). i < length xs \<and> j < length (xs !i)]\<^sub>a
      (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  have 1: \<open>a * b * array_assn R x y = array_assn R x y * a * b\<close> for a b c :: assn and x y
    by (auto simp: ac_simps)
  have 2: \<open>a * arl_assn R x y * c = arl_assn R x y * a * c\<close> for a c :: assn and x y and R
    by (auto simp: ac_simps)
  have [simp]: \<open>R a b = \<up>((b,a) \<in> the_pure R)\<close> for a b
    using assms by (metis CONSTRAINT_D pure_app_eq pure_the_pure)
  show ?thesis
    using assms
    apply sepref_to_hoare
    apply (sep_auto simp: nth_raa_i64_u64_def arl_get_u64_def
        uint32_nat_rel_def br_def nat_of_uint32_code[symmetric]
        arlO_assn_except_def 1 arl_get'_def Array.nth'_def nth_u64_code_def
        nat_of_uint64_code[symmetric] uint64_nat_rel_def nth_u64_code_def)
    apply (sep_auto simp: array_assn_def hr_comp_def is_array_def list_rel_imp_same_length
        param_nth nth_rll_def)
    apply (sep_auto simp: arlO_assn_def 2)
    apply (subst mult.assoc)+
    apply (rule fr_refl')
    apply (subst heap_list_all_heap_list_all_nth_eq)
    apply (subst_tac (2) i=\<open>nat_of_uint64 bia\<close> in heap_list_all_nth_remove1)
     apply (sep_auto simp: nth_rll_def is_array_def hr_comp_def)+
    done
qed


lemma nth_aa_i64_u64_code[code]:
  \<open>nth_aa_i64_u64 x L L' = nth_u64_code x L \<bind> (\<lambda>x. arl_get_u64 x L' \<bind> return)\<close>
  unfolding nth_aa_u_def nth_aa_def arl_get_u_def[symmetric]  Array.nth'_def[symmetric]
   nth_nat_of_uint32_nth' nth_u_code_def[symmetric] nth_nat_of_uint64_nth'
   nth_aa_i64_u64_def nth_u64_code_def arl_get_u64_def arl_get'_def
   nat_of_uint64_code[symmetric]
  ..


lemma nth_aa_i64_u32_code[code]:
  \<open>nth_aa_i64_u32 x L L' = nth_u64_code x L \<bind> (\<lambda>x. arl_get_u x L' \<bind> return)\<close>
  unfolding nth_aa_u_def nth_aa_def arl_get_u_def[symmetric]  Array.nth'_def[symmetric]
   nth_nat_of_uint32_nth' nth_u_code_def[symmetric] nth_nat_of_uint64_nth'
   nth_aa_i64_u32_def nth_u64_code_def arl_get_u64_def arl_get'_def
   nat_of_uint64_code[symmetric] arl_get_u_def nat_of_uint32_code[symmetric]
  ..


lemma nth_aa_i32_u64_code[code]:
  \<open>nth_aa_i32_u64 x L L' = nth_u_code x L \<bind> (\<lambda>x. arl_get_u64 x L' \<bind> return)\<close>
  unfolding nth_aa_u_def nth_aa_def arl_get_u_def[symmetric]  Array.nth'_def[symmetric]
   nth_nat_of_uint32_nth' nth_u_code_def[symmetric] nth_nat_of_uint64_nth'
   nth_aa_i32_u64_def nth_u64_code_def arl_get_u64_def arl_get'_def
   nat_of_uint64_code[symmetric] arl_get_u_def nat_of_uint32_code[symmetric]
  ..



paragraph \<open>Length\<close>
definition length_raa_i64_u :: \<open>'a::heap arrayO_raa \<Rightarrow> uint64 \<Rightarrow> uint32 Heap\<close> where
  \<open>length_raa_i64_u xs i = do {
     x \<leftarrow> arl_get_u64 xs i;
    length_u_code x}\<close>

lemma length_raa_i64_u_alt_def: \<open>length_raa_i64_u xs i = do {
    n \<leftarrow> length_raa xs (nat_of_uint64 i);
    return (uint32_of_nat n)}\<close>
  unfolding length_raa_i64_u_def length_raa_def length_u_code_def arl_get_u64_def arl_get'_def
  by (auto simp: nat_of_uint64_code)

lemma length_raa_i64_u_rule[sep_heap_rules]:
  \<open>nat_of_uint64 b < length xs \<Longrightarrow> <arlO_assn (array_assn R) xs a> length_raa_i64_u a b
   <\<lambda>r. arlO_assn (array_assn R) xs a * \<up> (r = uint32_of_nat (length_rll xs (nat_of_uint64 b)))>\<^sub>t\<close>
  unfolding length_raa_i64_u_alt_def length_u_code_def
  by sep_auto

lemma length_raa_i64_u_hnr[sepref_fr_rules]:
  shows \<open>(uncurry length_raa_i64_u, uncurry (RETURN \<circ>\<circ> length_rll_n_uint32)) \<in>
     [\<lambda>(xs, i). i < length xs \<and> length (xs ! i) \<le> uint32_max]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def length_rll_def
      nat_of_uint32_uint32_of_nat_id uint64_nat_rel_def)+


definition length_raa_i64_u64 :: \<open>'a::heap arrayO_raa \<Rightarrow> uint64 \<Rightarrow> uint64 Heap\<close> where
  \<open>length_raa_i64_u64 xs i = do {
     x \<leftarrow> arl_get_u64 xs i;
    length_u64_code x}\<close>

lemma length_raa_i64_u64_alt_def: \<open>length_raa_i64_u64 xs i = do {
    n \<leftarrow> length_raa xs (nat_of_uint64 i);
    return (uint64_of_nat n)}\<close>
  unfolding length_raa_i64_u64_def length_raa_def length_u64_code_def arl_get_u64_def arl_get'_def
  by (auto simp: nat_of_uint64_code)

lemma length_raa_i64_u64_rule[sep_heap_rules]:
  \<open>nat_of_uint64 b < length xs \<Longrightarrow> <arlO_assn (array_assn R) xs a> length_raa_i64_u64 a b
   <\<lambda>r. arlO_assn (array_assn R) xs a * \<up> (r = uint64_of_nat (length_rll xs (nat_of_uint64 b)))>\<^sub>t\<close>
  unfolding length_raa_i64_u64_alt_def length_u64_code_def
  by sep_auto

lemma length_raa_i64_u64_hnr[sepref_fr_rules]:
  shows \<open>(uncurry length_raa_i64_u64, uncurry (RETURN \<circ>\<circ> length_rll_n_uint32)) \<in>
     [\<lambda>(xs, i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def length_rll_def
      nat_of_uint64_uint64_of_nat_id uint64_nat_rel_def)+


definition length_raa_i32_u64 :: \<open>'a::heap arrayO_raa \<Rightarrow> uint32 \<Rightarrow> uint64 Heap\<close> where
  \<open>length_raa_i32_u64 xs i = do {
     x \<leftarrow> arl_get_u xs i;
    length_u64_code x}\<close>

lemma length_raa_i32_u64_alt_def: \<open>length_raa_i32_u64 xs i = do {
    n \<leftarrow> length_raa xs (nat_of_uint32 i);
    return (uint64_of_nat n)}\<close>
  unfolding length_raa_i32_u64_def length_raa_def length_u64_code_def arl_get_u_def
    arl_get'_def nat_of_uint32_code[symmetric]
  by auto


definition length_rll_n_i32_uint64 where
  [simp]: \<open>length_rll_n_i32_uint64 = length_rll\<close>

lemma length_raa_i32_u64_hnr[sepref_fr_rules]:
  shows \<open>(uncurry length_raa_i32_u64, uncurry (RETURN \<circ>\<circ> length_rll_n_i32_uint64)) \<in>
     [\<lambda>(xs, i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare  (sep_auto simp: uint64_nat_rel_def br_def length_rll_def
      nat_of_uint64_uint64_of_nat_id length_raa_i32_u64_alt_def arl_get_u_def
      arl_get'_def nat_of_uint32_code[symmetric] uint32_nat_rel_def)+

(* TODO Sort stuff *)

definition delete_index_and_swap_aa_i64 where
   \<open>delete_index_and_swap_aa_i64 xs i = delete_index_and_swap_aa xs (nat_of_uint64 i)\<close>


definition last_aa_u64 where
  \<open>last_aa_u64 xs i = last_aa xs (nat_of_uint64 i)\<close>

lemma last_aa_u64_code[code]:
  \<open>last_aa_u64 xs i = nth_u64_code xs i \<bind> arl_last\<close>
  unfolding last_aa_u64_def last_aa_def nth_nat_of_uint32_nth' nth_nat_of_uint32_nth'
    arl_get_u_def[symmetric] nth_u64_code_def Array.nth'_def comp_def
    nat_of_uint64_code[symmetric]
  ..


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

definition (in -)length_aa_u64_o64 :: \<open>('a::heap array_list) array \<Rightarrow> uint64 \<Rightarrow> uint64 Heap\<close> where
  \<open>length_aa_u64_o64 xs i = length_aa_u64 xs i >>= (\<lambda>n. return (uint64_of_nat n))\<close>

definition arl_length_o64 where
  \<open>arl_length_o64 x = do {n \<leftarrow> arl_length x;  return (uint64_of_nat n)}\<close>

lemma length_aa_u64_o64_code[code]:
  \<open>length_aa_u64_o64 xs i = nth_u64_code xs i \<bind> arl_length_o64\<close>
  unfolding length_aa_u64_o64_def length_aa_u64_def nth_u_def[symmetric] nth_u64_code_def
   Array.nth'_def arl_length_o64_def length_aa_def
  by (auto simp: nat_of_uint32_code nat_of_uint64_code[symmetric])

lemma length_aa_u64_o64_hnr[sepref_fr_rules]:
   \<open>(uncurry length_aa_u64_o64, uncurry (RETURN \<circ>\<circ> length_ll)) \<in>
     [\<lambda>(xs, i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
    (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def length_aa_u64_o64_def br_def
     length_aa_u64_def uint64_nat_rel_def nat_of_uint64_uint64_of_nat_id
     length_ll_def)


definition (in -)length_aa_u32_o64 :: \<open>('a::heap array_list) array \<Rightarrow> uint32 \<Rightarrow> uint64 Heap\<close> where
  \<open>length_aa_u32_o64 xs i = length_aa_u xs i >>= (\<lambda>n. return (uint64_of_nat n))\<close>

lemma length_aa_u32_o64_code[code]:
  \<open>length_aa_u32_o64 xs i = nth_u_code xs i \<bind> arl_length_o64\<close>
  unfolding length_aa_u32_o64_def length_aa_u64_def nth_u_def[symmetric] nth_u_code_def
   Array.nth'_def arl_length_o64_def length_aa_u_def length_aa_def
  by (auto simp: nat_of_uint64_code[symmetric] nat_of_uint32_code[symmetric])

lemma length_aa_u32_o64_hnr[sepref_fr_rules]:
   \<open>(uncurry length_aa_u32_o64, uncurry (RETURN \<circ>\<circ> length_ll)) \<in>
     [\<lambda>(xs, i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
    (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def length_aa_u32_o64_def br_def
     length_aa_u64_def uint64_nat_rel_def nat_of_uint64_uint64_of_nat_id
     length_ll_def length_aa_u_def)


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


definition length_arlO_u where
  \<open>length_arlO_u xs = do {
      n \<leftarrow> length_ra xs;
      return (uint32_of_nat n)}\<close>

lemma length_arlO_u[sepref_fr_rules]:
  \<open>(length_arlO_u, RETURN o length_uint32_nat) \<in> [\<lambda>xs. length xs \<le> uint32_max]\<^sub>a (arlO_assn R)\<^sup>k \<rightarrow> uint32_nat_assn\<close>
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


paragraph \<open>Setters\<close>

definition update_aa_u64 where
  \<open>update_aa_u64 xs i j = update_aa xs (nat_of_uint64 i) j\<close>

definition Array_upd_u64 where
  \<open>Array_upd_u64 i x a = Array.upd (nat_of_uint64 i) x a\<close>

lemma Array_upd_u64_code[code]: \<open>Array_upd_u64 i x a = heap_array_set'_u64 a i x \<then> return a\<close>
  unfolding Array_upd_u64_def heap_array_set'_u64_def
  Array.upd'_def
  by (auto simp: nat_of_uint64_code upd_return)

lemma update_aa_u64_code[code]:
  \<open>update_aa_u64 a i j y = do {
      x \<leftarrow> nth_u64_code a i;
      a' \<leftarrow> arl_set x j y;
      Array_upd_u64 i a' a
    }\<close>
  unfolding update_aa_u64_def update_aa_def nth_nat_of_uint32_nth' nth_nat_of_uint32_nth'
    arl_get_u_def[symmetric] nth_u64_code_def Array.nth'_def comp_def
    heap_array_set'_u_def[symmetric] Array_upd_u64_def nat_of_uint64_code[symmetric]
  by auto


definition set_butlast_aa_u64 where
  \<open>set_butlast_aa_u64 xs i = set_butlast_aa xs (nat_of_uint64 i)\<close>

lemma set_butlast_aa_u64_code[code]:
  \<open>set_butlast_aa_u64 a i = do {
      x \<leftarrow> nth_u64_code a i;
      a' \<leftarrow> arl_butlast x;
      Array_upd_u64 i a' a
    }\<close> \<comment> \<open>Replace the \<^term>\<open>i\<close>-th element by the itself except the last element.\<close>
  unfolding set_butlast_aa_u64_def set_butlast_aa_def
   nth_u64_code_def Array_upd_u64_def
  by (auto simp: Array.nth'_def nat_of_uint64_code)

lemma delete_index_and_swap_aa_i64_code[code]:
\<open>delete_index_and_swap_aa_i64 xs i j = do {
     x \<leftarrow> last_aa_u64 xs i;
     xs \<leftarrow> update_aa_u64 xs i j x;
     set_butlast_aa_u64 xs i
  }\<close>
  unfolding delete_index_and_swap_aa_i64_def delete_index_and_swap_aa_def
   last_aa_u64_def update_aa_u64_def set_butlast_aa_u64_def
  by auto

lemma delete_index_and_swap_aa_i64_ll_hnr_u[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry2 delete_index_and_swap_aa_i64, uncurry2 (RETURN ooo delete_index_and_swap_ll))
     \<in> [\<lambda>((l,i), j). i < length l \<and> j < length_ll l i]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k
         \<rightarrow> (arrayO_assn (arl_assn R))\<close>
  using assms unfolding delete_index_and_swap_aa_def delete_index_and_swap_aa_i64_def
  by sepref_to_hoare (sep_auto dest: le_length_ll_nemptyD
      simp: delete_index_and_swap_ll_def update_ll_def last_ll_def set_butlast_ll_def
      length_ll_def[symmetric] uint32_nat_rel_def br_def uint64_nat_rel_def)


definition delete_index_and_swap_aa_i32_u64 where
   \<open>delete_index_and_swap_aa_i32_u64 xs i j =
      delete_index_and_swap_aa xs (nat_of_uint32 i) (nat_of_uint64 j)\<close>


definition update_aa_u32_i64 where
  \<open>update_aa_u32_i64 xs i j = update_aa xs (nat_of_uint32 i) (nat_of_uint64 j)\<close>

lemma update_aa_u32_i64_code[code]:
  \<open>update_aa_u32_i64 a i j y = do {
      x \<leftarrow> nth_u_code a i;
      a' \<leftarrow> arl_set_u64 x j y;
      Array_upd_u i a' a
    }\<close>
  unfolding update_aa_u32_i64_def update_aa_def nth_nat_of_uint32_nth' nth_nat_of_uint32_nth'
    arl_get_u_def[symmetric] nth_u_code_def Array.nth'_def comp_def arl_set'_u64_def
    heap_array_set'_u_def[symmetric] Array_upd_u_def nat_of_uint64_code[symmetric]
    nat_of_uint32_code arl_set_u64_def
  by auto


lemma delete_index_and_swap_aa_i32_u64_code[code]:
\<open>delete_index_and_swap_aa_i32_u64 xs i j = do {
     x \<leftarrow> last_aa_u xs i;
     xs \<leftarrow> update_aa_u32_i64 xs i j x;
     set_butlast_aa_u xs i
  }\<close>
  unfolding delete_index_and_swap_aa_i32_u64_def delete_index_and_swap_aa_def
   last_aa_u_def update_aa_u_def set_butlast_aa_u_def update_aa_u32_i64_def
  by auto

lemma delete_index_and_swap_aa_i32_u64_ll_hnr_u[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry2 delete_index_and_swap_aa_i32_u64, uncurry2 (RETURN ooo delete_index_and_swap_ll))
     \<in> [\<lambda>((l,i), j). i < length l \<and> j < length_ll l i]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k
         \<rightarrow> (arrayO_assn (arl_assn R))\<close>
  using assms unfolding delete_index_and_swap_aa_def delete_index_and_swap_aa_i32_u64_def
  by sepref_to_hoare (sep_auto dest: le_length_ll_nemptyD
      simp: delete_index_and_swap_ll_def update_ll_def last_ll_def set_butlast_ll_def
      length_ll_def[symmetric] uint32_nat_rel_def br_def uint64_nat_rel_def)


paragraph \<open>Swap\<close>

definition swap_aa_i32_u64  :: "('a::{heap,default}) arrayO_raa \<Rightarrow> uint32 \<Rightarrow> uint64 \<Rightarrow> uint64 \<Rightarrow> 'a arrayO_raa Heap" where
  \<open>swap_aa_i32_u64 xs k i j = do {
    xi \<leftarrow> arl_get_u xs k;
    xj \<leftarrow> swap_u64_code xi i j;
    xs \<leftarrow> arl_set_u xs k xj;
    return xs
  }\<close>

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


subsubsection \<open>Conversion from list of lists of \<^typ>\<open>nat\<close> to list of lists of \<^typ>\<open>uint64\<close> \<close>


sepref_definition array_nat_of_uint64_code
  is array_nat_of_uint64
  :: \<open>(array_assn uint64_nat_assn)\<^sup>k \<rightarrow>\<^sub>a array_assn nat_assn\<close>
  unfolding op_map_def array_nat_of_uint64_def array_fold_custom_replicate
  apply (rewrite at \<open>do {let _ = \<hole>; _}\<close> annotate_assn[where A=\<open>array_assn nat_assn\<close>])
  by sepref

lemma array_nat_of_uint64_conv_hnr[sepref_fr_rules]:
  \<open>(array_nat_of_uint64_code, (RETURN \<circ> array_nat_of_uint64_conv))
    \<in> (array_assn uint64_nat_assn)\<^sup>k \<rightarrow>\<^sub>a array_assn nat_assn\<close>
  using array_nat_of_uint64_code.refine[unfolded array_nat_of_uint64_def,
    FCOMP op_map_map_rel[unfolded convert_fref]] unfolding array_nat_of_uint64_conv_alt_def
  by simp

sepref_definition array_uint64_of_nat_code
  is array_uint64_of_nat
  :: \<open>[\<lambda>xs. \<forall>a\<in>set xs. a \<le> uint64_max]\<^sub>a
       (array_assn nat_assn)\<^sup>k \<rightarrow> array_assn uint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding op_map_def array_uint64_of_nat_def array_fold_custom_replicate
  apply (rewrite at \<open>do {let _ = \<hole>; _}\<close> annotate_assn[where A=\<open>array_assn uint64_nat_assn\<close>])
  by sepref

lemma array_uint64_of_nat_conv_alt_def:
  \<open>array_uint64_of_nat_conv = map uint64_of_nat_conv\<close>
  unfolding uint64_of_nat_conv_def array_uint64_of_nat_conv_def by auto

lemma array_uint64_of_nat_conv_hnr[sepref_fr_rules]:
  \<open>(array_uint64_of_nat_code, (RETURN \<circ> array_uint64_of_nat_conv))
    \<in> [\<lambda>xs. \<forall>a\<in>set xs. a \<le> uint64_max]\<^sub>a
       (array_assn nat_assn)\<^sup>k \<rightarrow> array_assn uint64_nat_assn\<close>
  using array_uint64_of_nat_code.refine[unfolded array_uint64_of_nat_def,
    FCOMP op_map_map_rel[unfolded convert_fref]] unfolding array_uint64_of_nat_conv_alt_def
  by simp

definition swap_arl_u64 where
  \<open>swap_arl_u64  = (\<lambda>(xs, n) i j. do {
    ki \<leftarrow> nth_u64_code xs i;
    kj \<leftarrow> nth_u64_code xs j;
    xs \<leftarrow> heap_array_set_u64 xs i kj;
    xs \<leftarrow> heap_array_set_u64 xs j ki;
    return (xs, n)
  })\<close>

lemma swap_arl_u64_hnr[sepref_fr_rules]:
  \<open>(uncurry2 swap_arl_u64, uncurry2 (RETURN ooo op_list_swap)) \<in>
  [pre_list_swap]\<^sub>a (arl_assn A)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arl_assn A\<close>
  unfolding swap_arl_u64_def arl_assn_def is_array_list_def hr_comp_def
    nth_u64_code_def Array.nth'_def heap_array_set_u64_def heap_array_set_def
    heap_array_set'_u64_def Array.upd'_def
  apply sepref_to_hoare
  apply (sep_auto simp: nat_of_uint64_code[symmetric] uint64_nat_rel_def br_def
      list_rel_imp_same_length[symmetric] swap_def)
  apply (subst_tac n=\<open>bb\<close> in nth_take[symmetric])
    apply (simp; fail)
  apply (subst_tac (2) n=\<open>bb\<close> in nth_take[symmetric])
    apply (simp; fail)
  by (sep_auto simp: nat_of_uint64_code[symmetric] uint64_nat_rel_def br_def
      list_rel_imp_same_length[symmetric] swap_def IICF_List.swap_def
      simp del: nth_take
    intro!: list_rel_update' param_nth)


definition butlast_nonresizing :: \<open>'a list \<Rightarrow> 'a list\<close>where
  [simp]: \<open>butlast_nonresizing = butlast\<close>

definition arl_butlast_nonresizing :: \<open>'a array_list \<Rightarrow> 'a array_list\<close> where
  \<open>arl_butlast_nonresizing = (\<lambda>(xs, a). (xs, fast_minus a 1))\<close>

lemma butlast_nonresizing_hnr[sepref_fr_rules]:
  \<open>(return o arl_butlast_nonresizing, RETURN o butlast_nonresizing) \<in>
    [\<lambda>xs. xs \<noteq> []]\<^sub>a (arl_assn R)\<^sup>d \<rightarrow> arl_assn R\<close>
  by sepref_to_hoare
    (sep_auto simp: arl_butlast_nonresizing_def arl_assn_def hr_comp_def
    is_array_list_def  butlast_take list_rel_imp_same_length
    dest:
      list_rel_butlast[of \<open>take _ _\<close>])


lemma update_aa_u64_rule[sep_heap_rules]:
  assumes p: \<open>is_pure R\<close> and \<open>bb < length a\<close> and \<open>ba < length_ll a bb\<close> and \<open>(bb', bb) \<in> uint32_nat_rel\<close> and
    \<open>(ba', ba) \<in> uint64_nat_rel\<close>
  shows \<open><R b bi * arrayO_assn (arl_assn R) a ai> update_aa_u32_i64 ai bb' ba' bi
      <\<lambda>r. R b bi * (\<exists>\<^sub>Ax. arrayO_assn (arl_assn R) x r * \<up> (x = update_ll a bb ba b))>\<^sub>t\<close>
  using assms
  by (sep_auto simp add: update_aa_u32_i64_def update_ll_def p uint64_nat_rel_def uint32_nat_rel_def br_def)

lemma update_aa_u32_i64_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry3 update_aa_u32_i64, uncurry3 (RETURN oooo update_ll)) \<in>
     [\<lambda>(((l,i), j), x). i < length l \<and> j < length_ll l i]\<^sub>a
      (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> (arrayO_assn (arl_assn R))\<close>
  by sepref_to_hoare (sep_auto simp: assms)

lemma min_uint64_nat_assn:
  \<open>(uncurry (return oo min), uncurry (RETURN oo min)) \<in> uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by (sepref_to_hoare; sep_auto simp: br_def uint64_nat_rel_def min_def nat_of_uint64_le_iff)

lemma nat_of_uint64_shiftl:  \<open>nat_of_uint64 (xs >> a) = nat_of_uint64 xs >> a\<close>
  by transfer (auto simp: unat_shiftr nat_shifl_div)

lemma bit_lshift_uint64_nat_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (>>)), uncurry (RETURN oo (>>))) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_shiftl)

lemma [code]: "uint32_max_uint32 = 4294967295"
  using nat_of_uint32_uint32_max_uint32
  by (auto simp: uint32_max_uint32_def uint32_max_def)

end

