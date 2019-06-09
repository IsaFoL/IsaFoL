theory Array_Array_List64
imports Array_Array_List IICF_Array_List64
begin

subsection \<open>Array of Array Lists of maximum length \<^term>\<open>uint64_max\<close>\<close>

definition length_aa64 :: \<open>('a::heap array_list64) array \<Rightarrow> uint64 \<Rightarrow> uint64 Heap\<close> where
  \<open>length_aa64 xs i = do {
     x \<leftarrow> nth_u64_code xs i;
    arl64_length x}\<close>


lemma arrayO_assn_Array_nth[sep_heap_rules]:
  \<open>b < length xs \<Longrightarrow>
    <arrayO_assn (arl64_assn R) xs a> Array.nth a b
    <\<lambda>p. arrayO_except_assn (arl64_assn R) [b] xs a (\<lambda>p'. \<up>(p=p'!b))*
     arl64_assn R (xs ! b) (p)>\<close>
  unfolding length_aa64_def nth_u64_code_def Array.nth'_def
  apply (subst arrayO_except_assn_array0_index[symmetric, of b])
  apply simp
  unfolding arrayO_except_assn_def arl_assn_def hr_comp_def
  apply (sep_auto simp: arrayO_except_assn_def arl_length_def arl_assn_def arl64_assn_def
      eq_commute[of \<open>(_, _)\<close>] is_array_list64_def hr_comp_def length_ll_def array_assn_def
      is_array_def uint64_nat_rel_def br_def
      dest: list_all2_lengthD split: prod.splits)
  done

lemma arl64_length[sep_heap_rules]:
  \<open><arl64_assn R b a> arl64_length a< \<lambda>r. arl64_assn R b a * \<up>(nat_of_uint64 r = length b)>\<close>
  by (sep_auto simp: arrayO_except_assn_def arl_length_def arl_assn_def arl64_assn_def
      eq_commute[of \<open>(_, _)\<close>] is_array_list64_def hr_comp_def length_ll_def array_assn_def
      is_array_def uint64_nat_rel_def br_def arl64_length_def list_rel_imp_same_length[symmetric]
      dest: list_all2_lengthD split: prod.splits)

lemma length_aa64_rule[sep_heap_rules]:
  \<open>b < length xs \<Longrightarrow> (b', b) \<in> uint64_nat_rel \<Longrightarrow> <arrayO_assn (arl64_assn R) xs a> length_aa64 a b'
   <\<lambda>r. arrayO_assn (arl64_assn R) xs a * \<up> (nat_of_uint64 r = length_ll xs b)>\<^sub>t\<close>
 unfolding length_aa64_def nth_u64_code_def Array.nth'_def
  apply (sep_auto simp flip: nat_of_uint64_code simp: br_def uint64_nat_rel_def length_ll_def)
  apply (subst arrayO_except_assn_array0_index[symmetric, of b])
  apply (simp add: nat_of_uint64_code br_def uint64_nat_rel_def)
   apply (sep_auto simp: arrayO_except_assn_def)
done

lemma length_aa64_hnr[sepref_fr_rules]: \<open>(uncurry length_aa64, uncurry (RETURN \<circ>\<circ> length_ll)) \<in>
     [\<lambda>(xs, i). i < length xs]\<^sub>a (arrayO_assn (arl64_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

lemma arl64_get_hnr[sep_heap_rules]:
  assumes \<open>(n', n) \<in> uint64_nat_rel\<close> and \<open>n < length a\<close> and \<open>CONSTRAINT is_pure R\<close>
  shows \<open><arl64_assn R a b>
       arl64_get b n'
     <\<lambda>r. arl64_assn R a b * R (a ! n) r>\<close>
proof -
  obtain A' where
    A: \<open>pure A' = R\<close>
    using assms pure_the_pure by auto
  then have A': \<open>the_pure R = A'\<close>
      by auto
  show ?thesis
    using param_nth[of n a n \<open>take (nat_of_uint64 (snd b)) _\<close> \<open>the_pure R\<close>, simplified] assms
    unfolding arl64_get_def arl64_assn_def nth_u64_code_def Array.nth'_def
    by (sep_auto simp flip: nat_of_uint64_code A simp: br_def uint64_nat_rel_def hr_comp_def
       is_array_list64_def list_rel_imp_same_length[symmetric] pure_app_eq dest:
     split: prod.splits)
qed


definition nth_aa64 where
  \<open>nth_aa64 xs i j = do {
      x \<leftarrow> Array.nth xs i;
      y \<leftarrow> arl64_get x j;
      return y}\<close>

lemma nth_aa64_hnr[sepref_fr_rules]:
  assumes p: \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa64, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_ll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_ll l i]\<^sub>a
       (arrayO_assn (arl64_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have H: \<open>list_all2 (\<lambda>x x'. (x, x') \<in> the_pure (\<lambda>a c. \<up> ((c, a) \<in> R'))) bc (a ! ba) \<Longrightarrow>
       b < length (a ! ba) \<Longrightarrow>
       (bc ! b, a ! ba ! b) \<in> R'\<close> for bc a ba b
    by (auto simp add: ent_refl_true list_all2_conv_all_nth is_pure_alt_def pure_app_eq[symmetric])
  show ?thesis
    using p
    apply sepref_to_hoare
    apply (sep_auto simp: nth_aa64_def length_ll_def nth_ll_def)
     apply (subst arrayO_except_assn_array0_index[symmetric, of ba])
    apply simp
    apply (sep_auto simp: arrayO_except_assn_def arrayO_assn_def arl64_assn_def hr_comp_def list_rel_def
        list_all2_lengthD
      star_aci(3) R R' pure_def H)
    done
qed

definition append64_el_aa :: "('a::{default,heap} array_list64) array \<Rightarrow>
  nat \<Rightarrow> 'a \<Rightarrow> ('a array_list64) array Heap"where
"append64_el_aa \<equiv> \<lambda>a i x. do {
  j \<leftarrow> Array.nth a i;
  a' \<leftarrow> arl64_append j x;
  Array.upd i a' a
  }"

definition append_ll :: "'a list list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list list" where
  \<open>append_ll xs i x = list_update xs i (xs ! i @ [x])\<close>


declare arrayO_nth_rule[sep_heap_rules]

lemma sep_auto_is_stupid:
  fixes R :: \<open>'a \<Rightarrow> 'b::{heap,default} \<Rightarrow> assn\<close>
  assumes p: \<open>is_pure R\<close> and \<open>length l' < uint64_max\<close>
  shows
    \<open><\<exists>\<^sub>Ap. R1 p * R2 p * arl64_assn R l' aa * R x x' * R4 p>
       arl64_append aa x' <\<lambda>r. (\<exists>\<^sub>Ap. arl64_assn R (l' @ [x]) r * R1 p * R2 p * R x x' * R4 p * true) >\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have bbi: \<open>(x', x) \<in> the_pure R\<close> if
    \<open>(aa, bb) \<Turnstile> is_array_list64 (ba @ [x']) (a, baa) * R1 p * R2 p * pure R' x x' * R4 p * true\<close>
    for aa bb a ba baa p
    using that by (auto simp: mod_star_conv R R')
  show ?thesis
    using assms(2)
    unfolding arl_assn_def hr_comp_def
    by (sep_auto simp: list_rel_def R R' arl64_assn_def hr_comp_def list_all2_lengthD
       intro!: list_all2_appendI dest!: bbi)
  qed

lemma append_aa_hnr[sepref_fr_rules]:
  fixes R ::  \<open>'a \<Rightarrow> 'b :: {heap, default} \<Rightarrow> assn\<close>
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 append64_el_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> append_ll)) \<in>
     [\<lambda>((l,i),x). i < length l \<and> length (l ! i) < uint64_max]\<^sub>a (arrayO_assn (arl64_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> (arrayO_assn (arl64_assn R))\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have [simp]: \<open>(\<exists>\<^sub>Ax. arrayO_assn (arl64_assn R) a ai * R x r * true * \<up> (x = a ! ba ! b)) =
     (arrayO_assn (arl64_assn R) a ai * R (a ! ba ! b) r * true)\<close> for a ai ba b r
    by (auto simp: ex_assn_def)
  show ?thesis \<comment> \<open>TODO tune proof\<close>
    apply sepref_to_hoare
    apply (sep_auto simp: append64_el_aa_def)
     apply (simp add: arrayO_except_assn_def)
     apply (rule sep_auto_is_stupid[OF p])
    apply simp
    apply (sep_auto simp: array_assn_def is_array_def append_ll_def)
    apply (simp add: arrayO_except_assn_array0[symmetric] arrayO_except_assn_def)
    apply (subst_tac (2) i = ba in heap_list_all_nth_remove1)
     apply (solves \<open>simp\<close>)
    apply (simp add: array_assn_def is_array_def)
    apply (rule_tac x=\<open>p[ba := (ab, bc)]\<close> in ent_ex_postI)
    apply (subst_tac (2)xs'=a and ys'=p in heap_list_all_nth_cong)
      apply (solves \<open>auto\<close>)+
    apply sep_auto
    done
qed

definition update_aa64 :: "('a::{heap} array_list64) array \<Rightarrow> nat \<Rightarrow> uint64 \<Rightarrow> 'a \<Rightarrow> ('a array_list64) array Heap" where
  \<open>update_aa64 a i j y = do {
      x \<leftarrow> Array.nth a i;
      a' \<leftarrow> arl64_set x j y;
      Array.upd i a' a
    }\<close> \<comment> \<open>is the Array.upd really needed?\<close>

declare nth_rule[sep_heap_rules del]
declare arrayO_nth_rule[sep_heap_rules]

lemma arrayO_except_assn_arl_set[sep_heap_rules]:
  fixes R :: \<open>'a \<Rightarrow> 'b :: {heap}\<Rightarrow> assn\<close>
  assumes p: \<open>is_pure R\<close> and \<open>bb < length a\<close> and
     \<open>ba < length_ll a bb\<close> and \<open>(ba' , ba) \<in> uint64_nat_rel\<close>
  shows \<open>
       <arrayO_except_assn (arl64_assn R) [bb] a ai
         (\<lambda>p'. \<up> ((aa, bc) = p' ! bb)) *
        arl64_assn R (a ! bb) (aa, bc) *
        R b bi>
       arl64_set (aa, bc) ba' bi
      <\<lambda>(aa, bc). arrayO_except_assn (arl64_assn R) [bb] a ai
        (\<lambda>r'. arl64_assn R ((a ! bb)[ba := b]) (aa, bc)) * R b bi * true>\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  show ?thesis
    using assms
    apply (sep_auto simp: arrayO_except_assn_def arl64_assn_def hr_comp_def list_rel_imp_same_length
        list_rel_update length_ll_def)
    done
qed

lemma Array_upd_arrayO_except_assn[sep_heap_rules]:
  assumes
    \<open>bb < length a\<close> and
    \<open>ba < length_ll a bb\<close> and \<open>(ba', ba) \<in> uint64_nat_rel\<close>
  shows \<open><arrayO_except_assn (arl64_assn R) [bb] a ai
         (\<lambda>r'. arl64_assn R xu (aa, bc)) *
        R b bi *
        true>
       Array.upd bb (aa, bc) ai
       <\<lambda>r. \<exists>\<^sub>Ax. R b bi * arrayO_assn (arl64_assn R) x r * true *
                  \<up> (x = a[bb := xu])>\<close>
proof -
  have H[simp, intro]: \<open>ba \<le> length l'\<close>
    if
      \<open>ba \<le> length (a ! bb)\<close> and
      aa: \<open>(take n' l', a ! bb) \<in> \<langle>the_pure R\<rangle>list_rel\<close>
    for l' :: \<open>'b list\<close> and n'
  proof -
    show ?thesis
      using list_rel_imp_same_length[OF aa] that assms(3)
      by (auto simp: uint64_nat_rel_def br_def list_rel_imp_same_length[symmetric])
  qed
  have [simp]: \<open>(take ba l', take ba (a ! bb)) \<in> \<langle>the_pure R\<rangle>list_rel\<close>
    if
      \<open>ba \<le> length (a ! bb)\<close> and
      \<open>n' \<le> length l'\<close> and
      take: \<open>(take n' l', a ! bb) \<in> \<langle>the_pure R\<rangle>list_rel\<close>
    for l' :: \<open>'b list\<close> and n'
  proof -
    have [simp]: \<open>n' = length (a ! bb)\<close>
      using list_rel_imp_same_length[OF take] that by auto
    have 1: \<open>take ba l' = take ba (take n' l')\<close>
      using that by (auto simp: min_def)
    show ?thesis
      using take
      unfolding 1
      by (rule list_rel_take)
  qed

  show ?thesis
    using assms
    unfolding arrayO_except_assn_def
    apply (subst (2) arl64_assn_def)
    apply (subst is_array_list64_def[abs_def])
    apply (subst hr_comp_def[abs_def])
    apply (subst array_assn_def)
    apply (subst is_array_def[abs_def])
    apply (subst hr_comp_def[abs_def])
    apply sep_auto
    apply (subst arrayO_except_assn_array0_index[symmetric, of bb])
    apply (solves simp)
    unfolding arrayO_except_assn_def array_assn_def is_array_def
    apply (subst (3) arl64_assn_def)
    apply (subst is_array_list64_def[abs_def])
    apply (subst (2) hr_comp_def[abs_def])
    apply (subst ex_assn_move_out)+
    apply (rule_tac x=\<open>p[bb := (aa, bc)]\<close> in ent_ex_postI)
    apply (rule_tac x=\<open>take (nat_of_uint64 bc) l'\<close> in ent_ex_postI)
    apply (sep_auto simp: uint64_nat_rel_def br_def list_rel_imp_same_length intro!: split: prod.splits)
    apply (subst (2) heap_list_all_nth_cong[of _ _ a _ p])
    apply auto
    apply sep_auto
    done
qed

lemma update_aa64_rule[sep_heap_rules]:
  assumes p: \<open>is_pure R\<close> and \<open>bb < length a\<close> and \<open>ba < length_ll a bb\<close> \<open>(ba', ba) \<in> uint64_nat_rel\<close>
  shows \<open><R b bi * arrayO_assn (arl64_assn R) a ai> update_aa64 ai bb ba' bi
      <\<lambda>r. R b bi * (\<exists>\<^sub>Ax. arrayO_assn (arl64_assn R) x r * \<up> (x = update_ll a bb ba b))>\<^sub>t\<close>
  using assms
  by (sep_auto simp add: update_aa64_def update_ll_def p)

lemma update_aa_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry3 update_aa64, uncurry3 (RETURN oooo update_ll)) \<in>
     [\<lambda>(((l,i), j), x). i < length l \<and> j < length_ll l i]\<^sub>a (arrayO_assn (arl64_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> (arrayO_assn (arl64_assn R))\<close>
  by sepref_to_hoare (sep_auto simp: assms)

definition last_aa64 :: "('a::heap array_list64) array \<Rightarrow> uint64 \<Rightarrow> 'a Heap" where
  \<open>last_aa64 xs i = do {
     x \<leftarrow> nth_u64_code xs i;
     arl64_last x
  }\<close>

lemma arl64_last_rule[sep_heap_rules]:
  assumes p: \<open>is_pure R\<close> \<open>ai \<noteq> []\<close>
  shows \<open><arl64_assn R ai a> arl64_last a
      <\<lambda>r. arl64_assn R ai a * R (last ai) r>\<^sub>t\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have [simp]: \<open>\<And>aa n l'.
       (take (nat_of_uint64 n) l', ai) \<in> \<langle>the_pure R\<rangle>list_rel \<Longrightarrow>
       l' \<noteq> [] \<Longrightarrow> nat_of_uint64 n > 0\<close>
    using assms by (cases ai; auto simp: min_def split: if_splits dest!: list_rel_imp_same_length[symmetric]
      simp flip: nat_of_uint64_le_iff simp: nat_of_uint64_ge_minus; fail)+
  have [simp]: \<open>\<And>aa n l'.
       (take (nat_of_uint64 n) l', ai) \<in> \<langle>the_pure R\<rangle>list_rel \<Longrightarrow>
       l' \<noteq> [] \<Longrightarrow> nat_of_uint64 (n - 1) = nat_of_uint64 n - 1\<close>
    using assms by (cases ai; auto simp: min_def split: if_splits dest!: list_rel_imp_same_length[symmetric]
      simp flip: nat_of_uint64_le_iff simp: nat_of_uint64_ge_minus; fail)+
  have [simp]: \<open>\<And>aa n l'.
       (take (nat_of_uint64 n) l', ai) \<in> \<langle>the_pure R\<rangle>list_rel \<Longrightarrow>
       nat_of_uint64 n \<le> length l' \<Longrightarrow>
       l' \<noteq> [] \<Longrightarrow> length l' \<le> uint64_max \<Longrightarrow> nat_of_uint64 n - Suc 0 < length l'\<close>
    using assms by (cases ai; auto simp: min_def split: if_splits dest!: list_rel_imp_same_length[symmetric]
      simp flip: nat_of_uint64_le_iff)+
  have [intro!]: \<open>(take (nat_of_uint64 n) l', ai) \<in> \<langle>R'\<rangle>list_rel \<Longrightarrow>
       a = (aa, n) \<Longrightarrow>
       nat_of_uint64 n \<le> length l' \<Longrightarrow>
       l' \<noteq> [] \<Longrightarrow>
       length l' \<le> uint64_max \<Longrightarrow>
       (aaa, b) \<Turnstile> aa \<mapsto>\<^sub>a l' \<Longrightarrow>
       (l' ! (nat_of_uint64 n - Suc 0), ai ! (length ai - Suc 0)) \<in> R'\<close> for aa n l' aaa b
     using assms
       nat_of_uint64_ge_minus[of 1 n] param_last[OF assms(2), of \<open>take (nat_of_uint64 n) l'\<close> R']
     by (auto simp: min_def R' last_conv_nth split: if_splits
     simp flip: nat_of_uint64_le_iff)
  show ?thesis
    using assms supply nth_rule[sep_heap_rules] apply -
    by (sep_auto simp add: update_aa64_def update_ll_def p arl64_last_def arl64_assn_def R'
       pure_app_eq last_take_nth_conv last_conv_nth
       nth_u64_code_def Array.nth'_def hr_comp_def is_array_list64_def nat_of_uint64_ge_minus
        simp flip: nat_of_uint64_code
    dest: list_rel_imp_same_length[symmetric])
qed

lemma last_aa64_rule[sep_heap_rules]:
  assumes
    p: \<open>is_pure R\<close> and
   \<open>b < length a\<close> and
   \<open>a ! b \<noteq> []\<close> and \<open>(b', b) \<in> uint64_nat_rel\<close>
   shows \<open>
       <arrayO_assn (arl64_assn R) a ai>
         last_aa64 ai b'
       <\<lambda>r. arrayO_assn (arl64_assn R) a ai * (\<exists>\<^sub>Ax. R x r * \<up> (x = last_ll a b))>\<^sub>t\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have \<open>\<And>b.
       b < length a \<Longrightarrow> (b', b) \<in> uint64_nat_rel \<Longrightarrow>
       a ! b \<noteq> [] \<Longrightarrow>
       <arrayO_assn (arl64_assn R) a ai>
         last_aa64 ai b'
       <\<lambda>r. arrayO_assn (arl64_assn R) a ai * (\<exists>\<^sub>Ax. R x r * \<up> (x = last_ll a b))>\<^sub>t\<close>
    apply (sep_auto simp add: last_aa64_def last_ll_def assms nth_u64_code_def Array.nth'_def
        uint64_nat_rel_def br_def
      simp flip: nat_of_uint64_code)

    apply (sep_auto simp add: last_aa64_def arrayO_except_assn_def array_assn_def is_array_def
        hr_comp_def arl64_assn_def)
    apply (subst_tac i= \<open>nat_of_uint64 b'\<close> in arrayO_except_assn_array0_index[symmetric])
     apply (solves \<open>simp\<close>)
    apply (subst arrayO_except_assn_def)
    apply (auto simp add: last_aa_def arrayO_except_assn_def array_assn_def is_array_def hr_comp_def)

    apply (rule_tac x=\<open>p\<close> in ent_ex_postI)
    apply (subst_tac (2)xs'=a and ys'=p in heap_list_all_nth_cong)
      apply (solves \<open>auto\<close>)
     apply (solves \<open>auto\<close>)

    apply (rule_tac x=\<open>ba\<close> in ent_ex_postI)
    unfolding R unfolding R'
    apply (sep_auto simp: pure_def param_last)
    done
  from this[of b] show ?thesis
    using assms unfolding R' by blast
qed

lemma last_aa_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows \<open>(uncurry last_aa64, uncurry (RETURN oo last_ll)) \<in>
     [\<lambda>(l,i). i < length l \<and> l ! i \<noteq> []]\<^sub>a (arrayO_assn (arl64_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  show ?thesis
    using assms by sepref_to_hoare sep_auto
qed


definition swap_aa64 :: "('a::heap array_list64) array \<Rightarrow> nat \<Rightarrow> uint64 \<Rightarrow> uint64 \<Rightarrow> ('a array_list64) array Heap" where
  \<open>swap_aa64 xs k i j = do {
    xi \<leftarrow> nth_aa64 xs k i;
    xj \<leftarrow> nth_aa64 xs k j;
    xs \<leftarrow> update_aa64 xs k i xj;
    xs \<leftarrow> update_aa64 xs k j xi;
    return xs
  }\<close>


lemma nth_aa64_heap[sep_heap_rules]:
  assumes p: \<open>is_pure R\<close> and \<open>b < length aa\<close> and \<open>ba < length_ll aa b\<close> and \<open>(ba', ba) \<in> uint64_nat_rel\<close>
  shows \<open>
   <arrayO_assn (arl64_assn R) aa a>
   nth_aa64 a b ba'
   <\<lambda>r. \<exists>\<^sub>Ax. arrayO_assn (arl64_assn R) aa a *
               (R x r *
                \<up> (x = nth_ll aa b ba)) *
               true>\<close>
proof -
  have \<open><arrayO_assn (arl64_assn R) aa a>
       nth_aa64 a b ba'
       <\<lambda>r. \<exists>\<^sub>Ax. arrayO_assn (arl64_assn R) aa a *
                   R x r *
                   true *
                   \<up> (x = nth_ll aa b ba)>\<close>
    using p assms nth_aa64_hnr[of R] unfolding hfref_def hn_refine_def nth_aa64_def pure_app_eq
    by auto
  then show ?thesis
    unfolding hoare_triple_def
    by (auto simp: Let_def pure_def)
qed

lemma update_aa_rule_pure:
  assumes p: \<open>is_pure R\<close> and \<open>b < length aa\<close> and \<open>ba < length_ll aa b\<close> and
    \<open>(ba', ba) \<in> uint64_nat_rel\<close>
  shows \<open>
   <arrayO_assn (arl64_assn R) aa a * R be bb>
           update_aa64 a b ba' bb
           <\<lambda>r. \<exists>\<^sub>Ax. invalid_assn (arrayO_assn (arl64_assn R)) aa a * arrayO_assn (arl64_assn R) x r *
                       true *
                       \<up> (x = update_ll aa b ba be)>\<close>
proof -
  obtain R' where R': \<open>R' = the_pure R\<close> and RR': \<open>R = pure R'\<close>
    using p by fastforce
  have bb: \<open>pure R' be bb = \<up>((bb, be) \<in> R')\<close>
    by (auto simp: pure_def)
  have \<open><arrayO_assn (arl64_assn R) aa a * R be bb>
           update_aa64 a b ba' bb
           <\<lambda>r. \<exists>\<^sub>Ax. invalid_assn (arrayO_assn (arl64_assn R)) aa a * nat_assn b b * nat_assn ba ba *
                       R be bb *
                       arrayO_assn (arl64_assn R) x r *
                       true *
                       \<up> (x = update_ll aa b ba be)>\<close>
    using p assms update_aa_hnr[of R] unfolding hfref_def hn_refine_def pure_app_eq
    by auto
  then show ?thesis
    unfolding R'[symmetric] unfolding hoare_triple_def RR' bb
    by (auto simp: Let_def pure_def)
qed

lemma arl64_set_rule_arl64_assn: "
  i<length l \<Longrightarrow> (i', i) \<in> uint64_nat_rel \<Longrightarrow> (x', x) \<in> the_pure R \<Longrightarrow>
  <arl64_assn R l a>
    arl64_set a i' x'
  <arl64_assn R (l[i:=x])>"
  supply arl64_set_rule[where i=i, sep_heap_rules]
  by (sep_auto simp: arl64_assn_def hr_comp_def list_rel_imp_same_length
     split: prod.split simp flip: nat_of_uint64_code intro!: list_rel_update')

lemma swap_aa_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry3 swap_aa64, uncurry3 (RETURN oooo swap_ll)) \<in>
   [\<lambda>(((xs, k), i), j). k < length xs \<and> i < length_ll xs k \<and> j < length_ll xs k]\<^sub>a
  (arrayO_assn (arl64_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> (arrayO_assn (arl64_assn R))\<close>
proof -
  note update_aa_rule_pure[sep_heap_rules]
  obtain R' where R': \<open>R' = the_pure R\<close> and RR': \<open>R = pure R'\<close>
    using assms by fastforce
  have [simp]: \<open>the_pure (\<lambda>a b. \<up> ((b, a) \<in> R')) = R'\<close>
    unfolding pure_def[symmetric] by auto
  show ?thesis
    using assms unfolding R'[symmetric] unfolding swap_aa64_def
    apply sepref_to_hoare
    supply nth_aa64_heap[sep_heap_rules del]
    apply (sep_auto simp: swap_ll_def arrayO_except_assn_def
        length_ll_update_ll uint64_nat_rel_def br_def)
    supply nth_aa64_heap[sep_heap_rules]
    apply (sep_auto simp: swap_ll_def arrayO_except_assn_def
        length_ll_update_ll uint64_nat_rel_def br_def)
   supply nth_aa64_heap[sep_heap_rules del]
   apply (sep_auto simp: swap_ll_def arrayO_except_assn_def
        length_ll_update_ll uint64_nat_rel_def br_def)
    apply (rule frame_rule)
    apply (rule frame_rule)
    apply (rule_tac ba= \<open>nat_of_uint64 bi\<close> in nth_aa64_heap[of ])
    apply (auto simp: swap_ll_def arrayO_except_assn_def
          length_ll_update_ll uint64_nat_rel_def br_def)
    supply update_aa_rule_pure[sep_heap_rules del] update_aa64_rule[sep_heap_rules del]
    apply (sep_auto simp: uint64_nat_rel_def br_def)
    apply (rule frame_rule, rule frame_rule)
    apply (rule update_aa_rule_pure)
    apply (auto simp: swap_ll_def arrayO_except_assn_def
          length_ll_update_ll uint64_nat_rel_def br_def)
    apply sep_auto
    apply (rule cons_post_rule)
    apply (subst assn_times_assoc)
    apply (rule frame_rule)
    apply (rule frame_rule_left)
    apply (subst assn_times_comm)
    apply (rule_tac R=R and ba= \<open>nat_of_uint64 bi\<close> in update_aa64_rule)
    apply (auto simp: length_ll_def update_ll_def uint64_nat_rel_def br_def)[4]
    apply (sep_auto simp: uint64_nat_rel_def br_def length_ll_def update_ll_def nth_ll_def swap_def)
    done
qed

text \<open>It is not possible to do a direct initialisation: there is no element that can be put
  everywhere.\<close>
definition arrayO_ara_empty_sz where
  \<open>arrayO_ara_empty_sz n =
   (let xs = fold (\<lambda>_ xs. [] # xs) [0..<n] [] in
    op_list_copy xs)
   \<close>

lemma of_list_op_list_copy_arrayO[sepref_fr_rules]:
   \<open>(Array.of_list, RETURN \<circ> op_list_copy) \<in> (list_assn (arl64_assn R))\<^sup>d \<rightarrow>\<^sub>a arrayO_assn (arl64_assn R)\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: arrayO_assn_def array_assn_def)
  apply (rule_tac ?psi=\<open>xa \<mapsto>\<^sub>a xi * list_assn (arl64_assn R) x xi \<Longrightarrow>\<^sub>A
       is_array xi xa * heap_list_all (arl64_assn R) x xi * true\<close> in asm_rl)
  by (sep_auto simp: heap_list_all_list_assn is_array_def)

sepref_definition
  arrayO_ara_empty_sz_code
  is "RETURN o arrayO_ara_empty_sz"
  :: \<open>nat_assn\<^sup>k \<rightarrow>\<^sub>a arrayO_assn (arl64_assn (R::'a \<Rightarrow> 'b::{heap, default} \<Rightarrow> assn))\<close>
  unfolding arrayO_ara_empty_sz_def op_list_empty_def[symmetric]
  apply (rewrite at \<open>(#) \<hole>\<close> op_arl64_empty_def[symmetric])
  apply (rewrite at \<open>fold _ _ \<hole>\<close> op_HOL_list_empty_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref


lemma arrayO_ara_empty_sz_init_lrl: \<open>arrayO_ara_empty_sz n = init_lrl n\<close>
  by (induction n) (auto simp: arrayO_ara_empty_sz_def init_lrl_def)

lemma arrayO_raa_empty_sz_init_lrl[sepref_fr_rules]:
  \<open>(arrayO_ara_empty_sz_code, RETURN o init_lrl) \<in>
    nat_assn\<^sup>k \<rightarrow>\<^sub>a arrayO_assn (arl64_assn R)\<close>
  using arrayO_ara_empty_sz_code.refine unfolding arrayO_ara_empty_sz_init_lrl .

definition (in -) shorten_take_aa64 where
  \<open>shorten_take_aa64 L j W =  do {
      (a, n) \<leftarrow> Array.nth W L;
      Array.upd L (a, j) W
    }\<close>


lemma Array_upd_arrayO_except_assn2[sep_heap_rules]:
  assumes
    \<open>ba \<le> length (b ! a)\<close> and
    \<open>a < length b\<close> and \<open>(ba', ba) \<in> uint64_nat_rel\<close>
  shows \<open><arrayO_except_assn (arl64_assn R) [a] b bi
           (\<lambda>r'.  \<up> ((aaa, n) = r' ! a)) * arl64_assn R (b ! a) (aaa, n)>
         Array.upd a (aaa, ba') bi
         <\<lambda>r. \<exists>\<^sub>Ax. arrayO_assn (arl64_assn R) x r * true *
                    \<up> (x = b[a := take ba (b ! a)])>\<close>
  using Array_upd_arrayO_except_assn
proof -
  have [simp]: \<open>nat_of_uint64 ba' \<le> length l'\<close>
    if
      \<open>ba \<le> length (b ! a)\<close> and
      aa: \<open>(take n' l', b ! a) \<in> \<langle>the_pure R\<rangle>list_rel\<close>
    for l' :: \<open>'b list\<close> and n'
  proof -
    show ?thesis
      using list_rel_imp_same_length[OF aa] that assms(3)
      by (auto simp: uint64_nat_rel_def br_def)
  qed
  have [simp]: \<open>(take (nat_of_uint64 ba') l', take (nat_of_uint64 ba') (b ! a)) \<in> \<langle>the_pure R\<rangle>list_rel\<close>
    if
      \<open>ba \<le> length (b ! a)\<close> and
      \<open>n' \<le> length l'\<close> and
      take: \<open>(take n' l', b ! a) \<in> \<langle>the_pure R\<rangle>list_rel\<close>
    for l' :: \<open>'b list\<close> and n'
  proof -
    have [simp]: \<open>n' = length (b ! a)\<close>
      using list_rel_imp_same_length[OF take] that by auto
    have 1: \<open>take (nat_of_uint64 ba') l' = take (nat_of_uint64 ba') (take n' l')\<close>
      using that assms(3) by (auto simp: min_def uint64_nat_rel_def br_def)
    show ?thesis
      using take
      unfolding 1
      by (rule list_rel_take)
  qed
  show ?thesis
    using assms
    unfolding arrayO_except_assn_def
    apply (subst (2) arl64_assn_def)
    apply (subst is_array_list64_def[abs_def])
    apply (subst hr_comp_def[abs_def])
    apply (subst array_assn_def)
    apply (subst is_array_def[abs_def])
    apply (subst hr_comp_def[abs_def])
    apply sep_auto
    apply (subst arrayO_except_assn_array0_index[symmetric, of a])
    apply (solves simp)
    unfolding arrayO_except_assn_def array_assn_def is_array_def
    apply (subst (3) arl64_assn_def)
    apply (subst is_array_list64_def[abs_def])
    apply (subst (2) hr_comp_def[abs_def])
    apply (subst ex_assn_move_out)+
    apply (rule_tac x=\<open>p[a := (aaa, ba')]\<close> in ent_ex_postI)
    apply (rule_tac x=\<open>take ba l'\<close> in ent_ex_postI)
    apply (sep_auto simp: uint64_nat_rel_def br_def list_rel_imp_same_length
       nat_of_uint64_le_uint64_max intro!: split: prod.splits)
    apply (subst (2) heap_list_all_nth_cong[of _ _ b _ p])
    apply auto
    apply sep_auto
    done
qed

lemma shorten_take_aa_hnr[sepref_fr_rules]:
  \<open>(uncurry2 shorten_take_aa64, uncurry2 (RETURN ooo shorten_take_ll)) \<in>
     [\<lambda>((L, j), W). j \<le> length (W ! L) \<and> L < length W]\<^sub>a
    nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a (arrayO_assn (arl64_assn R))\<^sup>d \<rightarrow> arrayO_assn (arl64_assn R)\<close>
  unfolding shorten_take_aa64_def shorten_take_ll_def
  by sepref_to_hoare sep_auto

definition nth_aa64_u where
  \<open>nth_aa64_u x L L' =  nth_aa64 x (nat_of_uint32 L) L'\<close>

lemma nth_aa_uint_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa64_u, uncurry2 (RETURN ooo nth_rll)) \<in>
       [\<lambda>((x, L), L'). L < length x \<and> L' < length (x ! L)]\<^sub>a
       (arrayO_assn (arl64_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_aa_u_def
  by sepref_to_hoare
    (use assms in \<open>sep_auto simp: uint32_nat_rel_def br_def length_ll_def nth_ll_def
     nth_rll_def nth_aa64_u_def\<close>)


lemma nth_aa64_u_code[code]:
  \<open>nth_aa64_u x L L' = nth_u_code x L \<bind> (\<lambda>x. arl64_get x L' \<bind> return)\<close>
  unfolding nth_aa64_u_def nth_aa64_def arl_get_u_def[symmetric]  Array.nth'_def[symmetric]
   nth_nat_of_uint32_nth' nth_u_code_def[symmetric] ..

definition nth_aa64_i64_u64 where
  \<open>nth_aa64_i64_u64 xs x L = nth_aa64 xs (nat_of_uint64 x) L\<close>

lemma nth_aa64_i64_u64_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa64_i64_u64, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arrayO_assn (arl64_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_aa64_i64_u64_def
  supply nth_aa64_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare
    (sep_auto simp: br_def nth_aa64_i64_u64_def uint64_nat_rel_def
      length_rll_def length_ll_def nth_rll_def nth_ll_def)

definition nth_aa64_i32_u64 where
  \<open>nth_aa64_i32_u64 xs x L = nth_aa64 xs (nat_of_uint32 x) L\<close>

lemma nth_aa64_i32_u64_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa64_i32_u64, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arrayO_assn (arl64_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_aa64_i32_u64_def
  supply nth_aa64_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def uint64_nat_rel_def
      length_rll_def length_ll_def nth_rll_def nth_ll_def)

end
