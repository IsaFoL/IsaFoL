theory IICF_Array_List32
imports
  "Refine_Imperative_HOL.IICF_List"
  Separation_Logic_Imperative_HOL.Array_Blit
  Array_UInt
  WB_Word_Assn
begin

type_synonym 'a array_list32 = "'a Heap.array \<times> uint32"

definition "is_array_list32 l \<equiv> \<lambda>(a,n). \<exists>\<^sub>Al'. a \<mapsto>\<^sub>a l' * \<up>(nat_of_uint32 n \<le> length l' \<and> l = take (nat_of_uint32 n) l' \<and> length l'>0 \<and> nat_of_uint32 n \<le> uint32_max \<and> length l' \<le> uint32_max)"

lemma is_array_list32_prec[safe_constraint_rules]: "precise is_array_list32"
  unfolding is_array_list32_def[abs_def]
  apply(rule preciseI)
  apply(simp split: prod.splits)
	using preciseD snga_prec by fastforce

definition "arl32_empty \<equiv> do {
  a \<leftarrow> Array.new initial_capacity default;
  return (a,0)
}"

definition "arl32_empty_sz init_cap \<equiv> do {
  a \<leftarrow> Array.new (min uint32_max (max init_cap minimum_capacity)) default;
  return (a,0)
}"

definition uint32_max_uint32 :: uint32 where
  \<open>uint32_max_uint32 = 2 ^32 - 1\<close>

definition "arl32_append \<equiv> \<lambda>(a,n) x. do {
  len \<leftarrow> length_u_code a;

  if n<len then do {
    a \<leftarrow> Array_upd_u n x a;
    return (a,n+1)
  } else do {
    let newcap = (if len < uint32_max_uint32 >> 1 then 2 * len else uint32_max_uint32);
    a \<leftarrow> array_grow a (nat_of_uint32 newcap) default;
    a \<leftarrow> Array_upd_u n x a;
    return (a,n+1)
  }
}"

definition "arl32_copy \<equiv> \<lambda>(a,n). do {
  a \<leftarrow> array_copy a;
  return (a,n)
}"

definition arl32_length :: "'a::heap array_list32 \<Rightarrow> uint32 Heap" where
  "arl32_length \<equiv> \<lambda>(a,n). return (n)"

definition arl32_is_empty :: "'a::heap array_list32 \<Rightarrow> bool Heap" where
  "arl32_is_empty \<equiv> \<lambda>(a,n). return (n=0)"

definition arl32_last :: "'a::heap array_list32 \<Rightarrow> 'a Heap" where
  "arl32_last \<equiv> \<lambda>(a,n). do {
    nth_u_code a (n - 1)
  }"

definition arl32_butlast :: "'a::heap array_list32 \<Rightarrow> 'a array_list32 Heap" where
  "arl32_butlast \<equiv> \<lambda>(a,n). do {
    let n = n - 1;
    len \<leftarrow> length_u_code a;
    if (n*4 < len \<and> nat_of_uint32 n*2\<ge>minimum_capacity) then do {
      a \<leftarrow> array_shrink a (nat_of_uint32 n*2);
      return (a,n)
    } else
      return (a,n)
  }"

definition arl32_get :: "'a::heap array_list32 \<Rightarrow> uint32 \<Rightarrow> 'a Heap" where
  "arl32_get \<equiv> \<lambda>(a,n) i. nth_u_code a i"

definition arl32_set :: "'a::heap array_list32 \<Rightarrow> uint32 \<Rightarrow> 'a \<Rightarrow> 'a array_list32 Heap" where
  "arl32_set \<equiv> \<lambda>(a,n) i x. do { a \<leftarrow> heap_array_set_u a i x; return (a,n)}"


lemma arl32_empty_rule[sep_heap_rules]: "< emp > arl32_empty <is_array_list32 []>"
  by (sep_auto simp: arl32_empty_def is_array_list32_def initial_capacity_def uint32_max_def)

lemma arl32_empty_sz_rule[sep_heap_rules]: "< emp > arl32_empty_sz N <is_array_list32 []>"
  by (sep_auto simp: arl32_empty_sz_def is_array_list32_def minimum_capacity_def uint32_max_def)

lemma arl32_copy_rule[sep_heap_rules]: "< is_array_list32 l a > arl32_copy a <\<lambda>r. is_array_list32 l a * is_array_list32 l r>"
  by (sep_auto simp: arl32_copy_def is_array_list32_def)

lemma nat_of_uint32_shiftl:  \<open>nat_of_uint32 (xs >> a) = nat_of_uint32 xs >> a\<close>
  by transfer (auto simp: unat_shiftr nat_shifl_div)

lemma [simp]: \<open>nat_of_uint32 uint32_max_uint32 = uint32_max\<close>
  by (auto simp:  nat_of_uint32_mult_le nat_of_uint32_shiftl uint32_max_uint32_def uint32_max_def)[]

lemma \<open>2 * (uint32_max div 2) = uint32_max - 1\<close>
  by (auto simp:  nat_of_uint32_mult_le nat_of_uint32_shiftl uint32_max_uint32_def uint32_max_def)[]

lemma arl32_append_rule[sep_heap_rules]:
  assumes \<open>length l < uint32_max\<close>
  shows "< is_array_list32 l a >
      arl32_append a x
    <\<lambda>a. is_array_list32 (l@[x]) a >\<^sub>t"
proof -
  have [simp]: \<open>\<And>x1 x2 y ys.
       x2 < uint32_of_nat ys \<Longrightarrow>
       nat_of_uint32 x2 \<le> ys \<Longrightarrow>
       ys \<le> uint32_max \<Longrightarrow> nat_of_uint32 x2 < ys\<close>
    by (metis nat_of_uint32_less_iff nat_of_uint32_uint32_of_nat_id)
  have [simp]: \<open>\<And>x2 ys. x2 < uint32_of_nat (Suc (ys)) \<Longrightarrow>
       Suc (ys) \<le> uint32_max \<Longrightarrow>
       nat_of_uint32 (x2 + 1) = 1 + nat_of_uint32 x2\<close>
     by (smt ab_semigroup_add_class.add.commute le_neq_implies_less less_or_eq_imp_le
         less_trans_Suc linorder_neqE_nat nat_of_uint32_012(3) nat_of_uint32_add
          nat_of_uint32_less_iff nat_of_uint32_uint32_of_nat_id not_less_eq plus_1_eq_Suc)
  have [dest]: \<open>\<And>x2a x2 ys. x2 < uint32_of_nat (Suc (ys)) \<Longrightarrow>
       Suc (ys) \<le> uint32_max \<Longrightarrow>
       nat_of_uint32 x2 = Suc x2a \<Longrightarrow>Suc x2a \<le> ys\<close>
    by (metis less_Suc_eq_le nat_of_uint32_less_iff nat_of_uint32_uint32_of_nat_id)
  have [simp]: \<open>\<And>ys. ys \<le> uint32_max \<Longrightarrow>
       uint32_of_nat ys \<le> uint32_max_uint32 >> Suc 0 \<Longrightarrow>
       nat_of_uint32 (2 * uint32_of_nat ys) = 2 * ys\<close>
   by (subst (asm) nat_of_uint32_le_iff[symmetric])
    (auto simp: nat_of_uint32_uint32_of_nat_id uint32_max_uint32_def uint32_max_def nat_of_uint32_shiftl
       nat_of_uint32_mult_le)
  have [simp]: \<open>\<And>ys. ys \<le> uint32_max \<Longrightarrow>
       uint32_of_nat ys \<le> uint32_max_uint32 >> Suc 0 \<longleftrightarrow> ys \<le> uint32_max div 2\<close>
   by (subst nat_of_uint32_le_iff[symmetric])
    (auto simp: nat_of_uint32_uint32_of_nat_id uint32_max_uint32_def uint32_max_def nat_of_uint32_shiftl
       nat_of_uint32_mult_le)
  have [simp]: \<open>\<And>ys. ys \<le> uint32_max \<Longrightarrow>
       uint32_of_nat ys < uint32_max_uint32 >> Suc 0 \<longleftrightarrow> ys < uint32_max div 2\<close>
   by (subst nat_of_uint32_less_iff[symmetric])
    (auto simp: nat_of_uint32_uint32_of_nat_id uint32_max_uint32_def uint32_max_def nat_of_uint32_shiftl
       nat_of_uint32_mult_le)

  show ?thesis
    using assms
    apply (sep_auto
      simp: arl32_append_def is_array_list32_def take_update_last neq_Nil_conv nat_of_uint32_mult_le
        length_u_code_def  min_def nat_of_uint32_add nat_of_uint32_uint32_of_nat_id
    take_Suc_conv_app_nth list_update_append nat_of_uint32_0_iff
      split: if_split
      split: prod.splits nat.split)
  apply (subst Array_upd_u_def)
apply (sep_auto
      simp: arl32_append_def is_array_list32_def take_update_last neq_Nil_conv nat_of_uint32_mult_le
        length_u_code_def  min_def nat_of_uint32_add nat_of_uint32_uint32_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_split
      split: prod.splits nat.split)
apply (sep_auto
      simp: arl32_append_def is_array_list32_def take_update_last neq_Nil_conv nat_of_uint32_mult_le
        length_u_code_def  min_def nat_of_uint32_add nat_of_uint32_uint32_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_split
      split: prod.splits nat.split)
apply (sep_auto
      simp: arl32_append_def is_array_list32_def take_update_last neq_Nil_conv nat_of_uint32_mult_le
        length_u_code_def  min_def nat_of_uint32_add nat_of_uint32_uint32_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_split
      split: prod.splits nat.split)
  apply (subst Array_upd_u_def)
apply (sep_auto
      simp: arl32_append_def is_array_list32_def take_update_last neq_Nil_conv nat_of_uint32_mult_le
        length_u_code_def  min_def nat_of_uint32_add nat_of_uint32_uint32_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_split
      split: prod.splits nat.split)
apply (sep_auto
      simp: arl32_append_def is_array_list32_def take_update_last neq_Nil_conv nat_of_uint32_mult_le
        length_u_code_def  min_def nat_of_uint32_add nat_of_uint32_uint32_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_split
      split: prod.splits nat.split)
apply (sep_auto
      simp: arl32_append_def is_array_list32_def take_update_last neq_Nil_conv nat_of_uint32_mult_le
        length_u_code_def  min_def nat_of_uint32_add nat_of_uint32_uint32_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_split
      split: prod.splits nat.split)
  apply (subst Array_upd_u_def)
apply (rule frame_rule)
apply (rule upd_rule)
apply (sep_auto
      simp: arl32_append_def is_array_list32_def take_update_last neq_Nil_conv nat_of_uint32_mult_le
        length_u_code_def  min_def nat_of_uint32_add nat_of_uint32_uint32_of_nat_id
        take_Suc_conv_app_nth list_update_append nat_of_uint32_0_iff
      split: if_splits
      split: prod.splits nat.split)
apply (sep_auto
      simp: arl32_append_def is_array_list32_def take_update_last neq_Nil_conv nat_of_uint32_mult_le
        length_u_code_def  min_def nat_of_uint32_add nat_of_uint32_uint32_of_nat_id
        take_Suc_conv_app_nth list_update_append
      split: if_splits
    split: prod.splits nat.split)
  done
qed


lemma arl32_length_rule[sep_heap_rules]: "
  <is_array_list32 l a>
    arl32_length a
  <\<lambda>r. is_array_list32 l a * \<up>(nat_of_uint32 r=length l)>"
  by (sep_auto simp: arl32_length_def is_array_list32_def)

lemma arl32_is_empty_rule[sep_heap_rules]: "
  <is_array_list32 l a>
    arl32_is_empty a
  <\<lambda>r. is_array_list32 l a * \<up>(r\<longleftrightarrow>(l=[]))>"
  by (sep_auto simp: arl32_is_empty_def nat_of_uint32_0_iff is_array_list32_def)

lemma nat_of_uint32_ge_minus:
  \<open>ai \<ge> bi \<Longrightarrow>
       nat_of_uint32 (ai - bi) = nat_of_uint32 ai - nat_of_uint32 bi\<close>
  apply transfer
  unfolding unat_def
  by (subst uint_sub_lem[THEN iffD1])
    (auto simp: unat_def uint_nonnegative nat_diff_distrib word_le_def[symmetric] intro: leI)

lemma arl32_last_rule[sep_heap_rules]: "
  l\<noteq>[] \<Longrightarrow>
  <is_array_list32 l a>
    arl32_last a
  <\<lambda>r. is_array_list32 l a * \<up>(r=last l)>"
  by (sep_auto simp: arl32_last_def is_array_list32_def nth_u_code_def Array.nth'_def last_take_nth_conv
    nat_of_integer_integer_of_nat nat_of_uint32_ge_minus  nat_of_uint32_le_iff[symmetric]
    simp flip: nat_of_uint32_code)


lemma arl32_get_rule[sep_heap_rules]: "
  i<length l \<Longrightarrow> (i', i) \<in> uint32_nat_rel \<Longrightarrow>
  <is_array_list32 l a>
    arl32_get a i'
  <\<lambda>r. is_array_list32 l a * \<up>(r=l!i)>"
  by (sep_auto simp: arl32_get_def nth_u_code_def is_array_list32_def uint32_nat_rel_def
   Array.nth'_def br_def split: prod.split simp flip: nat_of_uint32_code)

lemma arl32_set_rule[sep_heap_rules]: "
  i<length l \<Longrightarrow> (i', i) \<in> uint32_nat_rel \<Longrightarrow>
  <is_array_list32 l a>
    arl32_set a i' x
  <is_array_list32 (l[i:=x])>"
  by (sep_auto simp: arl32_set_def is_array_list32_def heap_array_set_u_def  uint32_nat_rel_def
   heap_array_set'_u_def br_def Array.upd'_def split: prod.split simp flip: nat_of_uint32_code)

definition "arl32_assn A \<equiv> hr_comp is_array_list32 (\<langle>the_pure A\<rangle>list_rel)"
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "arl32_assn A" for A]


lemma arl32_assn_comp: "is_pure A \<Longrightarrow> hr_comp (arl32_assn A) (\<langle>B\<rangle>list_rel) = arl32_assn (hr_comp A B)"
  unfolding arl32_assn_def
  by (auto simp: hr_comp_the_pure hr_comp_assoc list_rel_compp)

lemma arl32_assn_comp': "hr_comp (arl32_assn id_assn) (\<langle>B\<rangle>list_rel) = arl32_assn (pure B)"
  by (simp add: arl32_assn_comp)

context
  notes [fcomp_norm_unfold] = arl32_assn_def[symmetric] arl32_assn_comp'
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI]
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin


  lemma arl32_empty_hnr_aux: "(uncurry0 arl32_empty,uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_array_list32"
    by sep_auto
  sepref_decl_impl (no_register) arl32_empty: arl32_empty_hnr_aux .

  lemma arl32_empty_sz_hnr_aux: "(uncurry0 (arl32_empty_sz N),uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_array_list32"
    by sep_auto

  sepref_decl_impl (no_register) arl32_empty_sz: arl32_empty_sz_hnr_aux .

  definition "op_arl32_empty \<equiv> op_list_empty"
  definition "op_arl32_empty_sz (N::nat) \<equiv> op_list_empty"

  lemma arl32_copy_hnr_aux: "(arl32_copy,RETURN o op_list_copy) \<in> is_array_list32\<^sup>k \<rightarrow>\<^sub>a is_array_list32"
    by sep_auto
  sepref_decl_impl arl32_copy: arl32_copy_hnr_aux .

  lemma arl32_append_hnr_aux: "(uncurry arl32_append,uncurry (RETURN oo op_list_append)) \<in> [\<lambda>(xs, x). length xs < uint32_max]\<^sub>a (is_array_list32\<^sup>d *\<^sub>a id_assn\<^sup>k) \<rightarrow> is_array_list32"
    by sep_auto
  sepref_decl_impl arl32_append: arl32_append_hnr_aux
    unfolding fref_param1 by (auto intro!: frefI nres_relI simp: list_rel_imp_same_length)

  lemma arl32_length_hnr_aux: "(arl32_length,RETURN o op_list_length) \<in> is_array_list32\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
    by (sep_auto simp: uint32_nat_rel_def br_def)
  sepref_decl_impl arl32_length: arl32_length_hnr_aux .

  lemma arl32_is_empty_hnr_aux: "(arl32_is_empty,RETURN o op_list_is_empty) \<in> is_array_list32\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    by sep_auto
  sepref_decl_impl arl32_is_empty: arl32_is_empty_hnr_aux .

  lemma arl32_last_hnr_aux: "(arl32_last,RETURN o op_list_last) \<in> [pre_list_last]\<^sub>a is_array_list32\<^sup>k \<rightarrow> id_assn"
    by sep_auto
  sepref_decl_impl arl32_last: arl32_last_hnr_aux .

(*  lemma arl32_butlast_hnr_aux: "(arl32_butlast,RETURN o op_list_butlast) \<in> [pre_list_butlast]\<^sub>a is_array_list32\<^sup>d \<rightarrow> is_array_list32"
    by sep_auto
  sepref_decl_impl arl32_butlast: arl32_butlast_hnr_aux . *)

  lemma arl32_get_hnr_aux: "(uncurry arl32_get,uncurry (RETURN oo op_list_get)) \<in> [\<lambda>(l,i). i<length l]\<^sub>a (is_array_list32\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k) \<rightarrow> id_assn"
    by sep_auto
  sepref_decl_impl arl32_get: arl32_get_hnr_aux .

  lemma arl32_set_hnr_aux: "(uncurry2 arl32_set,uncurry2 (RETURN ooo op_list_set)) \<in> [\<lambda>((l,i),_). i<length l]\<^sub>a (is_array_list32\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k) \<rightarrow> is_array_list32"
    by sep_auto
  sepref_decl_impl arl32_set: arl32_set_hnr_aux .

  sepref_definition arl32_swap is "uncurry2 mop_list_swap" :: "((arl32_assn id_assn)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a arl32_assn id_assn)"
    unfolding gen_mop_list_swap[abs_def]
    by sepref
  sepref_decl_impl (ismop) arl32_swap: arl32_swap.refine .
end


interpretation arl32: list_custom_empty "arl32_assn A" arl32_empty op_arl32_empty
  apply unfold_locales
  apply (rule arl32_empty_hnr)
  by (auto simp: op_arl32_empty_def)

lemma [def_pat_rules]: "op_arl32_empty_sz$N \<equiv> UNPROTECT (op_arl32_empty_sz N)" by simp

interpretation arl32_sz: list_custom_empty "arl32_assn A" "arl32_empty_sz N" "PR_CONST (op_arl32_empty_sz N)"
  apply unfold_locales
  apply (rule arl32_empty_sz_hnr)
  by (auto simp: op_arl32_empty_sz_def)


definition arl32_to_arl_conv where
  \<open>arl32_to_arl_conv S = S\<close>

definition arl32_to_arl :: \<open>'a array_list32 \<Rightarrow> 'a array_list\<close> where
  \<open>arl32_to_arl = (\<lambda>(xs, n). (xs, nat_of_uint32 n))\<close>

lemma arl32_to_arl_hnr[sepref_fr_rules]:
  \<open>(return o arl32_to_arl, RETURN o arl32_to_arl_conv) \<in> (arl32_assn R)\<^sup>d \<rightarrow>\<^sub>a arl_assn R\<close>
  by (sepref_to_hoare)
   (sep_auto simp: arl32_to_arl_def arl32_to_arl_conv_def arl_assn_def arl32_assn_def is_array_list32_def
     is_array_list_def hr_comp_def)

definition arl32_take where
  \<open>arl32_take n = (\<lambda>(xs, _). (xs, n))\<close>

lemma arl32_take[sepref_fr_rules]:
  \<open>(uncurry (return oo arl32_take), uncurry (RETURN oo take)) \<in>
    [\<lambda>(n, xs). n < length xs]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a (arl32_assn R)\<^sup>d \<rightarrow> arl32_assn R\<close>
  by (sepref_to_hoare)
    (sep_auto simp: arl32_assn_def arl32_take_def is_array_list32_def hr_comp_def
      uint32_nat_rel_def br_def list_rel_def list_all2_conv_all_nth)

end
