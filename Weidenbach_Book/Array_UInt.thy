theory Array_UInt
  imports Array_List_Array WB_Word_Assn
begin


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
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa_u, uncurry2 (RETURN ooo nth_rll)) \<in>
       [\<lambda>((x, L), L'). L < length x \<and> L' < length (x ! L)]\<^sub>a
       (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_aa_u_def
  by sepref_to_hoare
    (use assms in \<open>sep_auto simp: uint32_nat_rel_def br_def length_ll_def nth_lrl_def
     nth_rll_def\<close>)

definition nth_raa_u where
  \<open>nth_raa_u x L =  nth_raa x (nat_of_uint32 L)\<close>

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


definition append_el_aa_u' :: "('a::{default,heap} array_list) array \<Rightarrow>
  uint32 \<Rightarrow> 'a \<Rightarrow> ('a array_list) array Heap"where
"append_el_aa_u' \<equiv> \<lambda>a i x.
   Array.nth' a (integer_of_uint32 i) \<bind>
   (\<lambda>j. arl_append j x \<bind>
        (\<lambda>a'. Array.upd' a (integer_of_uint32 i) a' \<bind> (\<lambda>_. return a)))"

lemma append_el_aa_append_el_aa_u':
  \<open>append_el_aa xs (nat_of_uint32 i) j = append_el_aa_u' xs i j\<close>
  unfolding append_el_aa_def append_el_aa_u'_def Array.nth'_def nat_of_uint32_code  Array.upd'_def
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
  show ?thesis -- \<open>TODO tune proof\<close>
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
  using append_aa_hnr_u[of nat_assn, simplified] unfolding hfref_def  uint32_nat_rel_def br_def pure_def
   hn_refine_def append_el_aa_append_el_aa_u'
  by auto


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
     list_rel_eq_listrel listrel_iff_nth pure_def  nth_u_code_def nth_u_def Array.nth'_def
     nat_of_uint32_code)
qed

lemma  array_get_hnr_u[sepref_fr_rules]:
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

code_printing constant arl_get_u \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ Word32.toInt _))"

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

definition (in -)length_aa_u :: \<open>('a::heap array_list) array \<Rightarrow> uint32 \<Rightarrow> nat Heap\<close> where
  \<open>length_aa_u xs i = length_aa xs (nat_of_uint32 i)\<close>

lemma length_aa_u_code[code]:
  \<open>length_aa_u xs i = nth_u_code xs i \<bind> arl_length\<close>
  unfolding length_aa_u_def length_aa_def  nth_u_def[symmetric] nth_u_code_def
   Array.nth'_def 
  by (auto simp: nat_of_uint32_code)

lemma length_aa_u_hnr[sepref_fr_rules]: \<open>(uncurry length_aa_u, uncurry (RETURN \<circ>\<circ> length_ll)) \<in>
     [\<lambda>(xs, i). i < length xs]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def length_aa_u_def br_def)


lemma append_el_aa_u'_code[code]:
  "append_el_aa_u' = (\<lambda>a i x. nth_u_code a i \<bind>
     (\<lambda>j. arl_append j x \<bind>
      (\<lambda>a'. heap_array_set'_u a i a' \<bind> (\<lambda>_. return a))))"
  unfolding append_el_aa_u'_def nth_u_code_def heap_array_set'_u_def
  by auto

end