theory IICF_Array_List64
imports
  \<open>Refine_Imperative_HOL.IICF_List\<close>
  Separation_Logic_Imperative_HOL.Array_Blit
  Array_UInt
  WB_Word_Assn
begin

type_synonym 'a array_list64 = \<open>'a Heap.array \<times> uint64\<close>

definition \<open>is_array_list64 l \<equiv> \<lambda>(a,n). \<exists>\<^sub>Al'. a \<mapsto>\<^sub>a l' * \<up>(nat_of_uint64 n \<le> length l' \<and> l = take (nat_of_uint64 n) l' \<and> length l'>0 \<and> nat_of_uint64 n \<le> unat64_max \<and> length l' \<le> unat64_max)\<close>

lemma is_array_list64_prec[safe_constraint_rules]: \<open>precise is_array_list64\<close>
  unfolding is_array_list64_def[abs_def]
  apply(rule preciseI)
  apply(simp split: prod.splits)
	using preciseD snga_prec by fastforce

definition "arl64_empty \<equiv> do {
  a \<leftarrow> Array.new initial_capacity default;
  return (a,0)
}"

definition "arl64_empty_sz init_cap \<equiv> do {
  a \<leftarrow> Array.new (min unat64_max (max init_cap minimum_capacity)) default;
  return (a,0)
}"

definition unat64_max_uint64 :: uint64 where
  \<open>unat64_max_uint64 = 2 ^64 - 1\<close>

definition "arl64_append \<equiv> \<lambda>(a,n) x. do {
  len \<leftarrow> length_u64_code a;

  if n<len then do {
    a \<leftarrow> Array_upd_u64 n x a;
    return (a,n+1)
  } else do {
    let newcap = (if len < unat64_max_uint64 >> 1 then 2 * len else unat64_max_uint64);
    a \<leftarrow> array_grow a (nat_of_uint64 newcap) default;
    a \<leftarrow> Array_upd_u64 n x a;
    return (a,n+1)
  }
}"

definition "arl64_copy \<equiv> \<lambda>(a,n). do {
  a \<leftarrow> array_copy a;
  return (a,n)
}"

definition arl64_length :: \<open>'a::heap array_list64 \<Rightarrow> uint64 Heap\<close> where
  \<open>arl64_length \<equiv> \<lambda>(a,n). return (n)\<close>

definition arl64_is_empty :: \<open>'a::heap array_list64 \<Rightarrow> bool Heap\<close> where
  \<open>arl64_is_empty \<equiv> \<lambda>(a,n). return (n=0)\<close>

definition arl64_last :: \<open>'a::heap array_list64 \<Rightarrow> 'a Heap\<close> where
  "arl64_last \<equiv> \<lambda>(a,n). do {
    nth_u64_code a (n - 1)
  }"

definition arl64_butlast :: \<open>'a::heap array_list64 \<Rightarrow> 'a array_list64 Heap\<close> where
  "arl64_butlast \<equiv> \<lambda>(a,n). do {
    let n = n - 1;
    len \<leftarrow> length_u64_code a;
    if (n*4 < len \<and> nat_of_uint64 n*2\<ge>minimum_capacity) then do {
      a \<leftarrow> array_shrink a (nat_of_uint64 n*2);
      return (a,n)
    } else
      return (a,n)
  }"

definition arl64_get :: \<open>'a::heap array_list64 \<Rightarrow> uint64 \<Rightarrow> 'a Heap\<close> where
  \<open>arl64_get \<equiv> \<lambda>(a,n) i. nth_u64_code a i\<close>

definition arl64_set :: \<open>'a::heap array_list64 \<Rightarrow> uint64 \<Rightarrow> 'a \<Rightarrow> 'a array_list64 Heap\<close> where
  \<open>arl64_set \<equiv> \<lambda>(a,n) i x. do { a \<leftarrow> heap_array_set_u64 a i x; return (a,n)}\<close>


lemma arl64_empty_rule[sep_heap_rules]: \<open>< emp > arl64_empty <is_array_list64 []>\<close>
  by (sep_auto simp: arl64_empty_def is_array_list64_def initial_capacity_def unat64_max_def)

lemma arl64_empty_sz_rule[sep_heap_rules]: \<open>< emp > arl64_empty_sz N <is_array_list64 []>\<close>
  by (sep_auto simp: arl64_empty_sz_def is_array_list64_def minimum_capacity_def unat64_max_def)

lemma arl64_copy_rule[sep_heap_rules]: \<open>< is_array_list64 l a > arl64_copy a <\<lambda>r. is_array_list64 l a * is_array_list64 l r>\<close>
  by (sep_auto simp: arl64_copy_def is_array_list64_def)
lemma [simp]: \<open>nat_of_uint64 unat64_max_uint64 = unat64_max\<close>
  by (auto simp:  nat_of_uint64_mult_le nat_of_uint64_shiftl unat64_max_uint64_def unat64_max_def)[]
lemma \<open>2 * (unat64_max div 2) = unat64_max - 1\<close>
  by (auto simp:  nat_of_uint64_mult_le nat_of_uint64_shiftl unat64_max_uint64_def unat64_max_def)[]

lemma nat_of_uint64_0_iff: \<open>nat_of_uint64 x2 = 0 \<longleftrightarrow> x2 = 0\<close>
  using word_nat_of_uint64_Rep_inject by fastforce

lemma arl64_append_rule[sep_heap_rules]:
  assumes \<open>length l < unat64_max\<close>
  shows "< is_array_list64 l a >
      arl64_append a x
    <\<lambda>a. is_array_list64 (l@[x]) a >\<^sub>t"
proof -
  have [simp]: \<open>\<And>x1 x2 y ys.
       x2 < uint64_of_nat ys \<Longrightarrow>
       nat_of_uint64 x2 \<le> ys \<Longrightarrow>
       ys \<le> unat64_max \<Longrightarrow> nat_of_uint64 x2 < ys\<close>
    by (metis nat_of_uint64_less_iff nat_of_uint64_uint64_of_nat_id)
  have [simp]: \<open>\<And>x2 ys. x2 < uint64_of_nat (Suc (ys)) \<Longrightarrow>
       Suc (ys) \<le> unat64_max \<Longrightarrow>
       nat_of_uint64 (x2 + 1) = 1 + nat_of_uint64 x2\<close>
     by (smt ab_semigroup_add_class.add.commute le_neq_implies_less less_or_eq_imp_le
         less_trans_Suc linorder_neqE_nat nat_of_uint64_012(3) nat_of_uint64_add
          nat_of_uint64_less_iff nat_of_uint64_uint64_of_nat_id not_less_eq plus_1_eq_Suc)
  have [dest]: \<open>\<And>x2a x2 ys. x2 < uint64_of_nat (Suc (ys)) \<Longrightarrow>
       Suc (ys) \<le> unat64_max \<Longrightarrow>
       nat_of_uint64 x2 = Suc x2a \<Longrightarrow>Suc x2a \<le> ys\<close>
    by (metis less_Suc_eq_le nat_of_uint64_less_iff nat_of_uint64_uint64_of_nat_id)
  have [simp]: \<open>\<And>ys. ys \<le> unat64_max \<Longrightarrow>
       uint64_of_nat ys \<le> unat64_max_uint64 >> Suc 0 \<Longrightarrow>
       nat_of_uint64 (2 * uint64_of_nat ys) = 2 * ys\<close>
   by (subst (asm) nat_of_uint64_le_iff[symmetric])
    (auto simp: nat_of_uint64_uint64_of_nat_id unat64_max_uint64_def unat64_max_def nat_of_uint64_shiftl
       nat_of_uint64_mult_le)
  have [simp]: \<open>\<And>ys. ys \<le> unat64_max \<Longrightarrow>
       uint64_of_nat ys \<le> unat64_max_uint64 >> Suc 0 \<longleftrightarrow> ys \<le> unat64_max div 2\<close>
   by (subst nat_of_uint64_le_iff[symmetric])
    (auto simp: nat_of_uint64_uint64_of_nat_id unat64_max_uint64_def unat64_max_def nat_of_uint64_shiftl
       nat_of_uint64_mult_le)
  have [simp]: \<open>\<And>ys. ys \<le> unat64_max \<Longrightarrow>
       uint64_of_nat ys < unat64_max_uint64 >> Suc 0 \<longleftrightarrow> ys < unat64_max div 2\<close>
   by (subst nat_of_uint64_less_iff[symmetric])
    (auto simp: nat_of_uint64_uint64_of_nat_id unat64_max_uint64_def unat64_max_def nat_of_uint64_shiftl
       nat_of_uint64_mult_le)

  show ?thesis
    using assms
    apply (sep_auto
      simp: arl64_append_def is_array_list64_def take_update_last neq_Nil_conv nat_of_uint64_mult_le
        length_u64_code_def  min_def nat_of_uint64_add nat_of_uint64_uint64_of_nat_id
    take_Suc_conv_app_nth list_update_append nat_of_uint64_0_iff
      split: if_split
      split: prod.splits nat.split)
  apply (subst Array_upd_u64_def)
apply (sep_auto
      simp: arl64_append_def is_array_list64_def take_update_last neq_Nil_conv nat_of_uint64_mult_le
        length_u64_code_def  min_def nat_of_uint64_add nat_of_uint64_uint64_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_split
      split: prod.splits nat.split)
apply (sep_auto
      simp: arl64_append_def is_array_list64_def take_update_last neq_Nil_conv nat_of_uint64_mult_le
        length_u64_code_def  min_def nat_of_uint64_add nat_of_uint64_uint64_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_split
      split: prod.splits nat.split)
apply (sep_auto
      simp: arl64_append_def is_array_list64_def take_update_last neq_Nil_conv nat_of_uint64_mult_le
        length_u64_code_def  min_def nat_of_uint64_add nat_of_uint64_uint64_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_split
      split: prod.splits nat.split)
  apply (subst Array_upd_u64_def)
apply (sep_auto
      simp: arl64_append_def is_array_list64_def take_update_last neq_Nil_conv nat_of_uint64_mult_le
        length_u64_code_def  min_def nat_of_uint64_add nat_of_uint64_uint64_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_split
      split: prod.splits nat.split)
apply (sep_auto
      simp: arl64_append_def is_array_list64_def take_update_last neq_Nil_conv nat_of_uint64_mult_le
        length_u64_code_def  min_def nat_of_uint64_add nat_of_uint64_uint64_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_split
      split: prod.splits nat.split)
apply (sep_auto
      simp: arl64_append_def is_array_list64_def take_update_last neq_Nil_conv nat_of_uint64_mult_le
        length_u64_code_def  min_def nat_of_uint64_add nat_of_uint64_uint64_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_split
      split: prod.splits nat.split)
  apply (subst Array_upd_u64_def)
apply (rule frame_rule)
apply (rule upd_rule)
apply (sep_auto
      simp: arl64_append_def is_array_list64_def take_update_last neq_Nil_conv nat_of_uint64_mult_le
        length_u64_code_def  min_def nat_of_uint64_add nat_of_uint64_uint64_of_nat_id
        take_Suc_conv_app_nth list_update_append nat_of_uint64_0_iff
      split: if_splits
      split: prod.splits nat.split)
apply (sep_auto
      simp: arl64_append_def is_array_list64_def take_update_last neq_Nil_conv nat_of_uint64_mult_le
        length_u64_code_def  min_def nat_of_uint64_add nat_of_uint64_uint64_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_splits
    split: prod.splits nat.split)
  done
qed


lemma arl64_length_rule[sep_heap_rules]: "
  <is_array_list64 l a>
    arl64_length a
  <\<lambda>r. is_array_list64 l a * \<up>(nat_of_uint64 r=length l)>"
  by (sep_auto simp: arl64_length_def is_array_list64_def)

lemma arl64_is_empty_rule[sep_heap_rules]: "
  <is_array_list64 l a>
    arl64_is_empty a
  <\<lambda>r. is_array_list64 l a * \<up>(r\<longleftrightarrow>(l=[]))>"
  by (sep_auto simp: arl64_is_empty_def nat_of_uint64_0_iff is_array_list64_def)

lemma arl64_last_rule[sep_heap_rules]: "
  l\<noteq>[] \<Longrightarrow>
  <is_array_list64 l a>
    arl64_last a
  <\<lambda>r. is_array_list64 l a * \<up>(r=last l)>"
  by (sep_auto simp: arl64_last_def is_array_list64_def nth_u64_code_def Array.nth'_def last_take_nth_conv
    nat_of_integer_integer_of_nat nat_of_uint64_ge_minus  nat_of_uint64_le_iff[symmetric]
    simp flip: nat_of_uint64_code)


lemma arl64_get_rule[sep_heap_rules]: "
  i<length l \<Longrightarrow> (i', i) \<in> uint64_nat_rel \<Longrightarrow>
  <is_array_list64 l a>
    arl64_get a i'
  <\<lambda>r. is_array_list64 l a * \<up>(r=l!i)>"
  by (sep_auto simp: arl64_get_def nth_u64_code_def is_array_list64_def uint64_nat_rel_def
   Array.nth'_def br_def split: prod.split simp flip: nat_of_uint64_code)

lemma arl64_set_rule[sep_heap_rules]: "
  i<length l \<Longrightarrow> (i', i) \<in> uint64_nat_rel \<Longrightarrow>
  <is_array_list64 l a>
    arl64_set a i' x
  <is_array_list64 (l[i:=x])>"
  by (sep_auto simp: arl64_set_def is_array_list64_def heap_array_set_u64_def  uint64_nat_rel_def
   heap_array_set'_u64_def br_def Array.upd'_def split: prod.split simp flip: nat_of_uint64_code)

definition \<open>arl64_assn A \<equiv> hr_comp is_array_list64 (\<langle>the_pure A\<rangle>list_rel)\<close>
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure \<open>arl64_assn A\<close> for A]


lemma arl64_assn_comp: \<open>is_pure A \<Longrightarrow> hr_comp (arl64_assn A) (\<langle>B\<rangle>list_rel) = arl64_assn (hr_comp A B)\<close>
  unfolding arl64_assn_def
  by (auto simp: hr_comp_the_pure hr_comp_assoc list_rel_compp)

lemma arl64_assn_comp': \<open>hr_comp (arl64_assn id_assn) (\<langle>B\<rangle>list_rel) = arl64_assn (pure B)\<close>
  by (simp add: arl64_assn_comp)

context
  notes [fcomp_norm_unfold] = arl64_assn_def[symmetric] arl64_assn_comp'
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI]
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin


  lemma arl64_empty_hnr_aux: \<open>(uncurry0 arl64_empty,uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_array_list64\<close>
    by sep_auto
  sepref_decl_impl (no_register) arl64_empty: arl64_empty_hnr_aux .

  lemma arl64_empty_sz_hnr_aux: \<open>(uncurry0 (arl64_empty_sz N),uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_array_list64\<close>
    by sep_auto

  sepref_decl_impl (no_register) arl64_empty_sz: arl64_empty_sz_hnr_aux .

  definition \<open>op_arl64_empty \<equiv> op_list_empty\<close>
  definition \<open>op_arl64_empty_sz (N::nat) \<equiv> op_list_empty\<close>

  lemma arl64_copy_hnr_aux: \<open>(arl64_copy,RETURN o op_list_copy) \<in> is_array_list64\<^sup>k \<rightarrow>\<^sub>a is_array_list64\<close>
    by sep_auto
  sepref_decl_impl arl64_copy: arl64_copy_hnr_aux .

  lemma arl64_append_hnr_aux: \<open>(uncurry arl64_append,uncurry (RETURN oo op_list_append)) \<in> [\<lambda>(xs, x). length xs < unat64_max]\<^sub>a (is_array_list64\<^sup>d *\<^sub>a id_assn\<^sup>k) \<rightarrow> is_array_list64\<close>
    by sep_auto
  sepref_decl_impl arl64_append: arl64_append_hnr_aux
    unfolding fref_param1 by (auto intro!: frefI nres_relI simp: list_rel_imp_same_length)

  lemma arl64_length_hnr_aux: \<open>(arl64_length,RETURN o op_list_length) \<in> is_array_list64\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
    by (sep_auto simp: uint64_nat_rel_def br_def)
  sepref_decl_impl arl64_length: arl64_length_hnr_aux .

  lemma arl64_is_empty_hnr_aux: \<open>(arl64_is_empty,RETURN o op_list_is_empty) \<in> is_array_list64\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    by sep_auto
  sepref_decl_impl arl64_is_empty: arl64_is_empty_hnr_aux .

  lemma arl64_last_hnr_aux: \<open>(arl64_last,RETURN o op_list_last) \<in> [pre_list_last]\<^sub>a is_array_list64\<^sup>k \<rightarrow> id_assn\<close>
    by sep_auto
  sepref_decl_impl arl64_last: arl64_last_hnr_aux .

(*  lemma arl64_butlast_hnr_aux: \<open>(arl64_butlast,RETURN o op_list_butlast) \<in> [pre_list_butlast]\<^sub>a is_array_list64\<^sup>d \<rightarrow> is_array_list64\<close>
    by sep_auto
  sepref_decl_impl arl64_butlast: arl64_butlast_hnr_aux . *)

  lemma arl64_get_hnr_aux: \<open>(uncurry arl64_get,uncurry (RETURN oo op_list_get)) \<in> [\<lambda>(l,i). i<length l]\<^sub>a (is_array_list64\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k) \<rightarrow> id_assn\<close>
    by sep_auto
  sepref_decl_impl arl64_get: arl64_get_hnr_aux .

  lemma arl64_set_hnr_aux: \<open>(uncurry2 arl64_set,uncurry2 (RETURN ooo op_list_set)) \<in> [\<lambda>((l,i),_). i<length l]\<^sub>a (is_array_list64\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k) \<rightarrow> is_array_list64\<close>
    by sep_auto
  sepref_decl_impl arl64_set: arl64_set_hnr_aux .

  sepref_definition arl64_swap is \<open>uncurry2 mop_list_swap\<close> :: \<open>((arl64_assn id_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a arl64_assn id_assn)\<close>
    unfolding gen_mop_list_swap[abs_def]
    by sepref
  sepref_decl_impl (ismop) arl64_swap: arl64_swap.refine .
end


interpretation arl64: list_custom_empty \<open>arl64_assn A\<close> arl64_empty op_arl64_empty
  apply unfold_locales
  apply (rule arl64_empty_hnr)
  by (auto simp: op_arl64_empty_def)

lemma [def_pat_rules]: \<open>op_arl64_empty_sz$N \<equiv> UNPROTECT (op_arl64_empty_sz N)\<close> by simp

interpretation arl64_sz: list_custom_empty \<open>arl64_assn A\<close> \<open>arl64_empty_sz N\<close> \<open>PR_CONST (op_arl64_empty_sz N)\<close>
  apply unfold_locales
  apply (rule arl64_empty_sz_hnr)
  by (auto simp: op_arl64_empty_sz_def)


definition arl64_to_arl_conv where
  \<open>arl64_to_arl_conv S = S\<close>

definition arl64_to_arl :: \<open>'a array_list64 \<Rightarrow> 'a array_list\<close> where
  \<open>arl64_to_arl = (\<lambda>(xs, n). (xs, nat_of_uint64 n))\<close>

lemma arl64_to_arl_hnr[sepref_fr_rules]:
  \<open>(return o arl64_to_arl, RETURN o arl64_to_arl_conv) \<in> (arl64_assn R)\<^sup>d \<rightarrow>\<^sub>a arl_assn R\<close>
  by (sepref_to_hoare)
   (sep_auto simp: arl64_to_arl_def arl64_to_arl_conv_def arl_assn_def arl64_assn_def is_array_list64_def
     is_array_list_def hr_comp_def)

definition arl64_take where
  \<open>arl64_take n = (\<lambda>(xs, _). (xs, n))\<close>

lemma arl64_take[sepref_fr_rules]:
  \<open>(uncurry (return oo arl64_take), uncurry (RETURN oo take)) \<in>
    [\<lambda>(n, xs). n \<le> length xs]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a (arl64_assn R)\<^sup>d \<rightarrow> arl64_assn R\<close>
  by (sepref_to_hoare)
    (sep_auto simp: arl64_assn_def arl64_take_def is_array_list64_def hr_comp_def
      uint64_nat_rel_def br_def list_rel_def list_all2_conv_all_nth)
definition arl64_of_arl :: \<open>'a list \<Rightarrow> 'a list\<close> where
  \<open>arl64_of_arl S = S\<close>

definition arl64_of_arl_code :: \<open>'a :: heap array_list \<Rightarrow> 'a array_list64 Heap\<close> where
  \<open>arl64_of_arl_code = (\<lambda>(a, n). do {
    m \<leftarrow> Array.len a;
    if m > unat64_max then do {
        a \<leftarrow> array_shrink a unat64_max;
        return (a, (uint64_of_nat n))}
   else return (a, (uint64_of_nat n))})\<close>

lemma arl64_of_arl[sepref_fr_rules]:
  \<open>(arl64_of_arl_code, RETURN o arl64_of_arl) \<in> [\<lambda>n. length n \<le> unat64_max]\<^sub>a (arl_assn R)\<^sup>d \<rightarrow> arl64_assn R\<close>
proof -
  have [iff]: \<open>take unat64_max l' = [] \<longleftrightarrow> l' = []\<close> \<open>0 < unat64_max\<close> for l'
    by (auto simp: unat64_max_def)
  have H: \<open>x2 \<le> length l' \<Longrightarrow>
       (take x2 l', x) \<in> \<langle>the_pure R\<rangle>list_rel \<Longrightarrow> length x = x2\<close>
      \<open>x2 \<le> length l' \<Longrightarrow>
       (take x2 l', x) \<in> \<langle>the_pure R\<rangle>list_rel \<Longrightarrow> take (length x) = take x2\<close> for x x2 l'
    subgoal H by (auto dest: list_rel_imp_same_length)
    subgoal using H by blast
    done
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: arl_assn_def arl64_assn_def is_array_list_def is_array_list64_def hr_comp_def arl64_of_arl_def
       arl64_of_arl_code_def nat_of_uint64_code[symmetric] nat_of_uint64_uint64_of_nat_id
       H min_def
     split: prod.splits if_splits)
qed

definition arl_nat_of_uint64_conv :: \<open>nat list \<Rightarrow> nat list\<close> where
\<open>arl_nat_of_uint64_conv S = S\<close>

lemma arl_nat_of_uint64_conv_alt_def:
  \<open>arl_nat_of_uint64_conv = map nat_of_uint64_conv\<close>
  unfolding nat_of_uint64_conv_def arl_nat_of_uint64_conv_def by auto

sepref_definition arl_nat_of_uint64_code
  is array_nat_of_uint64
  :: \<open>(arl_assn uint64_nat_assn)\<^sup>k \<rightarrow>\<^sub>a arl_assn nat_assn\<close>
  unfolding op_map_def array_nat_of_uint64_def arl_fold_custom_replicate
  apply (rewrite at \<open>do {let _ = \<hole>; _}\<close> annotate_assn[where A=\<open>arl_assn nat_assn\<close>])
  by sepref

lemma arl_nat_of_uint64_conv_hnr[sepref_fr_rules]:
  \<open>(arl_nat_of_uint64_code, (RETURN \<circ> arl_nat_of_uint64_conv))
    \<in> (arl_assn uint64_nat_assn)\<^sup>k \<rightarrow>\<^sub>a arl_assn nat_assn\<close>
  using arl_nat_of_uint64_code.refine[unfolded array_nat_of_uint64_def,
    FCOMP op_map_map_rel] unfolding arl_nat_of_uint64_conv_alt_def
  by simp

end
