theory BigNat_UInt_Wrapper
  imports Array_UInt
begin

datatype bignat_uint = is_uint: UInt (uint_of: uint32) | is_bignat: BigNat (bignat_of: nat)

definition nat_of_bignat_uint where
  \<open>nat_of_bignat_uint n = (if is_uint n then nat_of_uint32 (uint_of n) else bignat_of n)\<close>

lemma is_uintE: \<open>is_uint b \<Longrightarrow> (\<And>n. b = UInt n \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (cases b) auto

lemma not_is_uintE: \<open>\<not>is_uint b \<Longrightarrow> (\<And>n. b = BigNat n \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (cases b) auto

instantiation bignat_uint :: default
begin
definition default_bignat_uint where
  \<open>default_bignat_uint = UInt 0\<close>
instance
  ..
end

definition bignat_uint_rel where
  \<open>bignat_uint_rel = {(n, m). m = nat_of_bignat_uint n}\<close>

abbreviation bignat_uint_assn where
  \<open>bignat_uint_assn \<equiv> pure bignat_uint_rel\<close>

definition uint32_max_uint32 :: uint32 where
  \<open>uint32_max_uint32 = - 1\<close>

lemma nat_of_uint32_uint32_max_uint32[simp]:
   \<open>nat_of_uint32 (uint32_max_uint32) = uint32_max\<close>
  by eval

fun incr_bignat_uint where
  \<open>incr_bignat_uint (UInt n) = 
      (if n < uint32_max_uint32 then UInt (n + 1) else BigNat (nat_of_uint32 n + 1))\<close> |
  \<open>incr_bignat_uint (BigNat n) = BigNat (n + 1)\<close>

lemma incr_bignat_uint_def:
  \<open>incr_bignat_uint n = 
    (if is_uint n then
      (if uint_of n < uint32_max_uint32 then UInt (uint_of n + 1)
       else BigNat (nat_of_uint32 (uint_of n) + 1))
   else
    BigNat (bignat_of n + 1)
   )\<close>
  by (cases n) auto

lemma leuint32_max_uint32_nat_of_uint32:
   \<open>x1 < uint32_max_uint32 \<longleftrightarrow> nat_of_uint32 x1 < uint32_max\<close>
  unfolding nat_of_uint32_uint32_max_uint32[symmetric] nat_of_uint32_less_iff ..

lemma incr_nat_bignat_uint_hnr[sepref_fr_rules]:
  \<open>(return o incr_bignat_uint, RETURN o Suc) \<in> bignat_uint_assn\<^sup>k \<rightarrow>\<^sub>a bignat_uint_assn\<close>
  apply sepref_to_hoare
  subgoal for x xi
    by (cases xi)
      (sep_auto simp: bignat_uint_rel_def incr_bignat_uint_def nat_of_bignat_uint_def
        nat_of_uint32_plus leuint32_max_uint32_nat_of_uint32
        split: if_splits)+
  done

definition arl_get_big_nat where
  \<open>arl_get_big_nat as n = (case n of UInt n \<Rightarrow> nth_u as n | BigNat n \<Rightarrow> nth as n)\<close>

lemma arl_get_big_nat_nth:
  \<open>(uncurry (RETURN oo arl_get_big_nat), uncurry (RETURN oo nth)) \<in> [\<lambda>(xs, i). i < length xs]\<^sub>f
   \<langle>Id\<rangle>list_rel \<times>\<^sub>f bignat_uint_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
     (auto simp: bignat_uint_rel_def nat_of_bignat_uint_def nth_u_def arl_get_big_nat_def
      elim!: is_uintE not_is_uintE)

definition arl_get_big_nat_code where
  \<open>arl_get_big_nat_code as n = (case n of UInt n \<Rightarrow> arl_get_u as n | BigNat n \<Rightarrow> arl_get as n)\<close>

lemma  arl_get_u_arl_get: "arl_get_u = (\<lambda>a i. arl_get a (nat_of_uint32 i))"
  unfolding arl_get_u_def arl_get'_def nat_of_uint32_code
  ..

lemma arl_get_big_nat_code_rule:
  assumes p: \<open>CONSTRAINT is_pure R\<close> and \<open>b = nat_of_bignat_uint bi\<close> and \<open>b < length a\<close>
  shows
  \<open>< arl_assn R a ai> arl_get_big_nat_code ai bi 
      <\<lambda>r. arl_assn R a ai * (\<exists>\<^sub>Ax. R x r * \<up> (RETURN x \<le> RETURN (op_list_get a b)))>\<^sub>t\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have pure_R': \<open>pure R' a b = \<up> ((b, a) \<in> R')\<close> for a b
    by (auto simp: pure_def)
  have param_nth': \<open>i < length l \<Longrightarrow> (i', i) \<in> nat_rel \<Longrightarrow> b \<le> length l' \<Longrightarrow>
     (take b l', l) \<in> \<langle>R'\<rangle>list_rel \<Longrightarrow> (l' ! i', l ! i) \<in> R'\<close> for i i' l l' b
    using param_nth[of i l i' \<open>take b l'\<close> R'] by (auto dest: list_rel_imp_same_length)
  show ?thesis
    using assms unfolding arl_get_u_arl_get
    apply (cases ai; cases bi)
    by (sep_auto simp: bignat_uint_rel_def nat_of_bignat_uint_def arl_get_def param_nth'
        arl_get_big_nat_code_def arl_get_u_arl_get arl_assn_def hr_comp_def R R' pure_R'
        is_array_list_def dest: list_rel_imp_same_length)+
qed
lemma op_list_get_arl_get_big_nat_code:
  assumes p: \<open>CONSTRAINT is_pure R\<close>
  shows
  \<open>(uncurry arl_get_big_nat_code, uncurry (RETURN oo op_list_get)) \<in>
   [\<lambda>(xs, i). i < length xs]\<^sub>a (arl_assn R)\<^sup>k *\<^sub>a bignat_uint_assn\<^sup>k \<rightarrow> R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have pure_R': \<open>pure R' a b = \<up> ((b, a) \<in> R')\<close> for a b
    by (auto simp: pure_def)
  have param_nth': \<open>i < length l \<Longrightarrow> (i', i) \<in> nat_rel \<Longrightarrow> b \<le> length l' \<Longrightarrow>
     (take b l', l) \<in> \<langle>R'\<rangle>list_rel \<Longrightarrow> (l' ! i', l ! i) \<in> R'\<close> for i i' l l' b
    using param_nth[of i l i' \<open>take b l'\<close> R'] by (auto dest: list_rel_imp_same_length)
  show ?thesis
    unfolding arl_get_u_arl_get
    apply sepref_to_hoare
    subgoal for i j xs' xs
      apply (cases j; cases xs)
      by (sep_auto simp: bignat_uint_rel_def nat_of_bignat_uint_def arl_get_def param_nth'
          arl_get_big_nat_code_def arl_get_u_arl_get arl_assn_def hr_comp_def R R' pure_R'
          is_array_list_def dest: list_rel_imp_same_length)+
    done
qed

definition nth_raa_big_nat :: \<open>'a::heap arrayO_raa \<Rightarrow> bignat_uint \<Rightarrow> nat \<Rightarrow> 'a Heap\<close> where
  \<open>nth_raa_big_nat xs i j = do {
      x \<leftarrow> arl_get_big_nat_code xs i;
      y \<leftarrow> Array.nth x j;
      return y}\<close>

lemma arl_get_big_nat_code_rule_arlO_assn[sep_heap_rules]:
  assumes i: \<open>nat_of_bignat_uint i < length a\<close>
  shows \<open> <arlO_assn (array_assn R) a ai> arl_get_big_nat_code ai i
    <\<lambda>r. arlO_assn_except (array_assn R) [nat_of_bignat_uint i] a ai
   (\<lambda>r'. array_assn R (a ! nat_of_bignat_uint i) r * \<up>(r = r' ! (nat_of_bignat_uint i)))>\<close>
  using arrayO_raa_nth_rule[OF assms, of R ai]
  by (cases i) (auto simp: nat_of_bignat_uint_def arl_get_big_nat_code_def arl_get_u_arl_get)

lemma nth_raa_big_nat_hnr:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_big_nat, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a bignat_uint_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have H: \<open>list_all2 (\<lambda>x x'. (x, x') \<in> the_pure (\<lambda>a c. \<up> ((c, a) \<in> R'))) bc (a ! ba) \<Longrightarrow>
       b < length (a ! ba) \<Longrightarrow>
       (bc ! b, a ! ba ! b) \<in> R'\<close> for bc a ba b
    by (auto simp add: ent_refl_true list_all2_conv_all_nth is_pure_alt_def pure_app_eq[symmetric])
  show ?thesis
    supply arl_get_big_nat_code_rule[sep_heap_rules]
    apply sepref_to_hoare
    apply (subst (2) arlO_assn_except_array0_index[symmetric])
     apply (solves \<open>auto\<close>)[]
    apply (sep_auto simp: nth_rll_def length_rll_def nth_raa_big_nat_def bignat_uint_rel_def)
    apply (sep_auto simp: arlO_assn_except_def arlO_assn_def arl_assn_def hr_comp_def list_rel_def
        list_all2_lengthD array_assn_def is_array_def hr_comp_def[abs_def]
        star_aci(3) R R' pure_def H)
    done
qed

definition nth_raa_big_nat_u :: \<open>'a::heap arrayO_raa \<Rightarrow> bignat_uint \<Rightarrow> uint32 \<Rightarrow> 'a Heap\<close> where
  \<open>nth_raa_big_nat_u xs n i = nth_raa_big_nat xs n (nat_of_uint32 i)\<close>

lemma nth_raa_big_nat_u_code[code]:
  \<open>nth_raa_big_nat_u xs i j = do {
      x \<leftarrow> arl_get_big_nat_code xs i;
      y \<leftarrow> nth_u_code x j;
      return y}\<close>
  unfolding nth_raa_big_nat_u_def nth_raa_big_nat_def nth_u_code_def Array.nth'_def
  comp_def nat_of_uint32_code ..

lemma nth_raa_big_nat_u_hnr[sepref_fr_rules]:
  assumes p: \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_big_nat_u, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a bignat_uint_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have H: \<open>list_all2 (\<lambda>x x'. (x, x') \<in> the_pure (\<lambda>a c. \<up> ((c, a) \<in> R'))) bc (a ! ba) \<Longrightarrow>
       b < length (a ! ba) \<Longrightarrow>
       (bc ! b, a ! ba ! b) \<in> R'\<close> for bc a ba b
    by (auto simp add: ent_refl_true list_all2_conv_all_nth is_pure_alt_def pure_app_eq[symmetric])
  show ?thesis
    supply arl_get_big_nat_code_rule[sep_heap_rules]
    apply sepref_to_hoare
    apply (subst (2) arlO_assn_except_array0_index[symmetric])
     apply (solves \<open>auto\<close>)[]
    apply (sep_auto simp: nth_rll_def length_rll_def nth_raa_big_nat_def bignat_uint_rel_def
        nth_raa_big_nat_u_def)
    apply (sep_auto simp: arlO_assn_except_def arlO_assn_def arl_assn_def hr_comp_def list_rel_def
        list_all2_lengthD array_assn_def is_array_def hr_comp_def[abs_def]
        uint32_nat_rel_def br_def
        star_aci(3) R R' pure_def H)
    done
qed

definition nth_get_big_nat_code where
  \<open>nth_get_big_nat_code as n = (case n of UInt n \<Rightarrow> nth_u_code as n | BigNat n \<Rightarrow> Array.nth as n)\<close>

lemma nth_get_big_nat_code_nth:
  \<open>nth_get_big_nat_code xs u = Array.nth xs (nat_of_bignat_uint u)\<close>
  by (cases u)
     (auto simp: nth_get_big_nat_code_def nth_u_code_def nat_of_bignat_uint_def
      Array.nth'_def nat_of_uint32_code)

definition nth_ara_big_nat_u :: \<open>('a :: heap array_list) array \<Rightarrow> bignat_uint \<Rightarrow> uint32 \<Rightarrow> 'a Heap\<close> where
  \<open>nth_ara_big_nat_u xs n i = nth_aa xs (nat_of_bignat_uint n) (nat_of_uint32 i)\<close>

lemma nth_ara_big_nat_u_code[code]:
  \<open>nth_ara_big_nat_u xs u =  (\<lambda>i. nth_get_big_nat_code xs u \<bind>
         (\<lambda>x. arl_get_u x i \<bind>
              return))\<close>
  unfolding nth_ara_big_nat_u_def nth_aa_def nth_get_big_nat_code_nth[symmetric]
  arl_get_u_def arl_get'_def nat_of_uint32_code ..

definition nth_aa_big_nat_u :: \<open>('a :: heap array_list) array \<Rightarrow> uint32 \<Rightarrow> bignat_uint \<Rightarrow> 'a Heap\<close> where
  \<open>nth_aa_big_nat_u xs n i = nth_aa xs (nat_of_uint32 n) (nat_of_bignat_uint i)\<close>

lemma arl_get_big_nat_code_alt_def:
  \<open>arl_get_big_nat_code x i = arl_get x (nat_of_bignat_uint i)\<close>
  unfolding arl_get_big_nat_code_def arl_get_u_def
  by (auto split: bignat_uint.splits
      simp: nat_of_bignat_uint_def arl_get'_def nat_of_uint32_code)

lemma nth_aa_big_nat_u_code[code]:
  \<open>nth_aa_big_nat_u xs u = (\<lambda>i. nth_u_code xs u \<bind>
         (\<lambda>x. arl_get_big_nat_code x i \<bind>
              return))\<close>
  unfolding nth_aa_big_nat_u_def nth_aa_def nth_get_big_nat_code_nth[symmetric]
  arl_get_u_def arl_get'_def nat_of_uint32_code[symmetric]
  arl_get_big_nat_code_def[symmetric] Array.nth'_def comp_def
  arl_get_big_nat_code_alt_def[symmetric] nth_u_code_def 
  ..

lemma nth_aa_big_nat_u_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa_big_nat_u, uncurry2 (RETURN ooo nth_lrl)) \<in>
       [\<lambda>((x, L), L'). L < length x \<and> L' < length (x ! L)]\<^sub>a
       (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a bignat_uint_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_aa_u_def
  by sepref_to_hoare
    (use assms in \<open>sep_auto simp: uint32_nat_rel_def br_def length_ll_def nth_lrl_def
     nth_rll_def nth_aa_big_nat_u_def bignat_uint_rel_def\<close>)

end