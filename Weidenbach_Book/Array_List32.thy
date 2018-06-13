theory Array_List32
imports WB_Word_Assn Array_UInt
begin
type_synonym 'a array32_list = "'a Heap.array \<times> uint32"

definition arl_ref where
  \<open>arl_ref = {((xs', i), xs). xs = take i xs' \<and> xs' \<noteq> [] \<and> i \<le> length xs'}\<close>

definition arl32_assn :: \<open>('a \<Rightarrow> 'b :: heap \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'b array32_list \<Rightarrow> assn\<close>where
  \<open>arl32_assn A xs = (\<lambda>(xs', i). (arl_assn A xs (xs', nat_of_uint32 i)))\<close>

lemma
  \<open>(\<And>a. P a \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A a. Q a)) \<Longrightarrow> (\<And>a. Q a \<Longrightarrow>\<^sub>A (\<exists>\<^sub>A a. P a)) \<Longrightarrow>(\<exists>\<^sub>A a. P a) = (\<exists>\<^sub>A a. Q a)\<close>
  by (simp add: ent_ex_preI ent_iffI)

lemma list_rel_take:
  \<open>(ba, ab) \<in> \<langle>A\<rangle>list_rel \<Longrightarrow> (take b ba, take b ab) \<in> \<langle>A\<rangle>list_rel\<close>
  by (auto simp: list_rel_def)

text \<open>
  This theorem is false since \<^term>\<open>array_assn\<close> is too strong: we would only require
  \<^term>\<open>array_assn\<close> for the first shared elements.
\<close>
lemma
  \<open>arl_assn A = hr_comp (array_assn A  *a nat_assn) arl_ref\<close>
proof -
  have H[simp]: \<open>(\<exists>\<^sub>A a b c. P a b c) = (\<exists>\<^sub>A a b. P a b b)\<close>
    if \<open>\<And>h. (\<exists>x b xa. h \<Turnstile> P x b xa) \<longleftrightarrow> (\<exists>x b.  h \<Turnstile> P x b b)\<close>
    for P
    using that
    by (subst ex_assn_def, subst (3) ex_assn_def, auto)
  have H'[simp]: \<open>(\<exists>\<^sub>A a b c. P a b c) = (\<exists>\<^sub>A a c. P a  b c)\<close>
    if \<open>\<And>h. (\<exists>x b xa. h \<Turnstile> P x b xa) \<longleftrightarrow> (\<exists>x xa.  h \<Turnstile> P x b xa)\<close>
    for P b
    using that
    by (subst ex_assn_def, subst (3) ex_assn_def, auto)
  have H''[simp]: \<open>(\<exists>\<^sub>A a b. P a b) = (\<exists>\<^sub>A a. P a  (b a))\<close>
    if \<open>\<And>h. (\<exists>x b. h \<Turnstile> P x b) \<longleftrightarrow> (\<exists>x.  h \<Turnstile> P x (b x))\<close>
    for P b
    using that
    by (subst ex_assn_def, subst (2) ex_assn_def, auto)
  show ?thesis
    unfolding array_assn_def arl_assn_def hr_comp_def is_array_list_def arl_ref_def is_array_def
    apply (auto intro!: ext simp: ex_assn_pair_split pure_def)
    subgoal for a aa b
    apply (subst H')
     apply auto
    apply (subst ex_assn_swap)
    apply (subst (2) ex_assn_swap)
    apply (subst H''[of _ \<open>take b\<close>])
       apply (auto intro!: ent_iffI ent_ex_preI)
       defer
       apply (rule_tac x=ba in ent_ex_postI)
    apply (auto simp: list_rel_imp_same_length list_rel_take)
      apply (rule_tac x=ab in ent_ex_postI)
    oops

definition arl_ref_grow where
  \<open>arl_ref_grow = (\<lambda>(xs, i) x. do {
    if i < length xs then RETURN (xs[i := x], i+1)
    else do {
      let xs = xs @ replicate (length xs) default;
      ASSERT(i < length xs);
      RETURN (xs[i:= x], i+1)
    }
  })\<close>

lemma
  \<open>(uncurry arl_ref_grow, uncurry (RETURN oo op_list_append)) \<in>
     arl_ref \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>arl_ref\<rangle>nres_rel\<close>
  unfolding arl_ref_grow_def
  by (intro frefI nres_relI nres_relI)
    (auto simp: arl_ref_def take_Suc_conv_app_nth list_update_append)

end
