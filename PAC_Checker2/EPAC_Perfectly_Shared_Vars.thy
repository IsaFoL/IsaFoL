theory EPAC_Perfectly_Shared_Vars
  imports EPAC_Perfectly_Shared
    PAC_Checker.PAC_Checker_Relation
    PAC_Checker.PAC_Map_Rel
begin
thm import_variableS_def
  term hm.assn
  term iam.assn
  term is_iam
  term iam_rel

type_synonym ('string2, 'nat) shared_vars_c = \<open>'string2 list \<times> ('string2, 'nat) fmap\<close>

definition perfect_shared_vars_rel_c :: \<open>('string2 \<times> 'string) set \<Rightarrow> (('string2, nat) shared_vars_c \<times> (nat, 'string)shared_vars) set\<close> where
  \<open>perfect_shared_vars_rel_c R =
  {((\<V>, \<A>), (\<D>', \<V>', \<A>')). (\<forall>i\<in>#dom_m \<V>'. i < length \<V>) \<and>
  (\<forall>i\<in>#dom_m \<V>'. i < length \<V> \<and> (\<V> ! i, the (fmlookup \<V>' i))\<in> R) \<and>
  (\<A>, \<A>') \<in> \<langle>R,nat_rel\<rangle>fmap_rel}\<close>

text \<open>Random conditions with the idea to use machine words eventually\<close>

definition find_new_idx_c :: \<open>('string, nat) shared_vars_c \<Rightarrow> (memory_allocation \<times> nat)  nres\<close> where
  \<open>find_new_idx_c = (\<lambda>(\<V>, \<A>). let k = length \<V> in if k < 2^63-1 then RETURN (Allocated, k) else RETURN (Mem_Out, 0) )\<close>

definition insert_variable_c :: \<open>'string \<Rightarrow> nat \<Rightarrow> ('string, nat) shared_vars_c \<Rightarrow> ('string, nat) shared_vars_c\<close>  where
  \<open>insert_variable_c v k' = (\<lambda>(\<V>, \<A>). (\<V> @ [v], fmupd v k' \<A>))\<close>

definition import_variable_c :: \<open>'string \<Rightarrow>  ('string, nat) shared_vars_c \<Rightarrow> (memory_allocation \<times> ('string, nat) shared_vars_c \<times> nat)  nres\<close> where
  \<open>import_variable_c v = (\<lambda>(\<V>\<A>). do {
  (err, k') \<leftarrow> find_new_idx_c (\<V>\<A>);
  if alloc_failed err then do {let k'=k'; RETURN (err, (\<V>\<A>), k')}
  else do{
    ASSERT(k' < 2^63-1);
    RETURN (Allocated, insert_variable_c v k' \<V>\<A>, k')
    }
    })\<close>

lemma import_variable_c_alt_def:
  \<open>import_variable_c v = (\<lambda>(\<V>, \<A>). do {
  (err, k') \<leftarrow> find_new_idx_c (\<V>, \<A>);
  if alloc_failed err then do {let k'=k'; RETURN (err, (\<V>, \<A>), k')}
  else do{
    ASSERT(k' < 2^63-1);
    RETURN (Allocated, (\<V> @ [v], fmupd v k' \<A>), k')
    }
    })\<close>
  unfolding import_variable_c_def insert_variable_c_def
  by auto


lemma import_variable_c_import_variableS:
  fixes A' :: \<open>(nat,'string) shared_vars\<close>
  assumes
    A: \<open>(A,A')\<in>perfect_shared_vars_rel_c R\<close> and
    v: \<open>(v,v')\<in>R\<close> \<open>single_valued R\<close> \<open>single_valued (R\<inverse>)\<close>
  shows \<open>import_variable_c v A \<le>\<Down>(Id \<times>\<^sub>r (perfect_shared_vars_rel_c R \<times>\<^sub>r nat_rel)) (import_variableS v' A')\<close>
proof -
  have [refine]: \<open>RETURN x2g \<le> \<Down> Id (RES UNIV)\<close> for x2g :: nat
    by auto
  have [refine]: \<open>find_new_idx_c a \<le> \<Down> {((err, k), (err', k')). err=err' \<and> k=k' \<and> (\<not>alloc_failed err \<longrightarrow> k < 2^63-1 \<and> k = length (fst a))} (find_new_idx b)\<close>
    if \<open>(a,b) \<in> perfect_shared_vars_rel_c R\<close>
    for b :: \<open>(nat,'string) shared_vars\<close> and a
    using that unfolding find_new_idx_c_def find_new_idx_def
    by (cases b; cases a)
      (auto intro!: RETURN_RES_refine simp: Let_def perfect_shared_vars_rel_c_def)

  show ?thesis
    unfolding import_variable_c_alt_def import_variableS_def find_new_idx_def[symmetric]
    apply refine_vcg
    subgoal using A by (auto simp: perfect_shared_vars_rel_c_def)
    subgoal by auto
    subgoal using A by (auto simp: perfect_shared_vars_rel_c_def)
    subgoal by auto
    subgoal
      using A v by (force simp: perfect_shared_vars_rel_c_def dest: in_diffD intro!: fmap_rel_fmupd_fmap_rel)
   done
qed


definition is_new_variable_c :: \<open>'string \<Rightarrow> ('string, 'nat) shared_vars_c \<Rightarrow> bool nres\<close> where
  \<open>is_new_variable_c v = (\<lambda>(\<V>, \<V>').
  RETURN (v \<notin># dom_m \<V>')
  )\<close>

lemma fset_fmdom_dom_m: \<open>fset (fmdom A) = set_mset (dom_m A)\<close>
  by (simp add: dom_m_def)

lemma fmap_rel_nat_rel_dom_m_iff:
  \<open>(A, B) \<in> \<langle>R, S\<rangle>fmap_rel \<Longrightarrow> (v,v')\<in>R \<Longrightarrow> v\<in>#dom_m A \<longleftrightarrow>v'\<in># dom_m B\<close>
  by (auto simp: fmap_rel_alt_def distinct_mset_dom fset_fmdom_dom_m
    dest!: multi_member_split
    simp del: fmap_rel_nat_the_fmlookup)


lemma is_new_variable_c_is_new_variableS:
  shows \<open>(uncurry is_new_variable_c, uncurry is_new_variableS) \<in> R \<times>\<^sub>r perfect_shared_vars_rel_c R \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (use  in \<open>auto simp: perfect_shared_vars_rel_c_def fmap_rel_nat_rel_dom_m
    fmap_rel_nat_rel_dom_m_iff is_new_variable_c_def is_new_variableS_def
    intro!: frefI nres_relI\<close>)


definition get_var_pos_c :: \<open> ('string, nat) shared_vars_c \<Rightarrow> _ \<Rightarrow> nat nres\<close> where
  \<open>get_var_pos_c = (\<lambda>(xs, \<V>) x. do {
    ASSERT(x \<in># dom_m \<V>);
    RETURN (the (fmlookup \<V> x))
  })\<close>


lemma get_var_pos_c_get_var_posS:
  fixes A' :: \<open>(nat,'string) shared_vars\<close>
  assumes
    V: \<open>single_valued R\<close> \<open>single_valued (R\<inverse>)\<close>
  shows \<open>(uncurry get_var_pos_c, uncurry get_var_posS) \<in> perfect_shared_vars_rel_c R \<times>\<^sub>r R \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  unfolding get_var_pos_c_def get_var_posS_def uncurry_def
    apply (clarify intro!: frefI nres_relI)
  apply refine_vcg
  subgoal using assms by (auto simp: perfect_shared_vars_rel_c_def fmap_rel_nat_rel_dom_m_iff)
  subgoal
    using assms by (auto simp: perfect_shared_vars_rel_c_def fmap_rel_nat_rel_dom_m_iff dest: fmap_rel_fmlookup_rel)
  done



definition get_var_name_c :: \<open> ('string, nat) shared_vars_c \<Rightarrow> nat \<Rightarrow> 'string nres\<close> where
  \<open>get_var_name_c = (\<lambda>(xs, \<V>) x. do {
    ASSERT(x < length xs);
    RETURN (xs ! x)
  })\<close>


lemma get_var_name_c_get_var_nameS:
  fixes A' :: \<open>(nat,'string) shared_vars\<close>
  assumes
    V: \<open>single_valued R\<close> \<open>single_valued (R\<inverse>)\<close>
  shows \<open>(uncurry get_var_name_c, uncurry get_var_nameS) \<in> perfect_shared_vars_rel_c R \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>R\<rangle>nres_rel\<close>
  unfolding get_var_name_c_def get_var_nameS_def uncurry_def
    apply (clarify intro!: frefI nres_relI)
  apply refine_vcg
  subgoal using assms by (auto dest!: multi_member_split simp: perfect_shared_vars_rel_c_def)
  subgoal
    using assms by (auto simp: perfect_shared_vars_rel_c_def fmap_rel_nat_rel_dom_m_iff
      dest: multi_member_split)
  done

abbreviation perfect_shared_vars_assn :: \<open>(string, nat) shared_vars_c \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>perfect_shared_vars_assn \<equiv> arl_assn string_assn \<times>\<^sub>a hm_fmap_assn string_assn uint64_nat_assn\<close>
abbreviation shared_vars_assn where
  \<open>shared_vars_assn \<equiv> hr_comp perfect_shared_vars_assn (perfect_shared_vars_rel_c Id)\<close>

lemmas [sepref_fr_rules] = hm.lookup_hnr[FCOMP op_map_lookup_fmlookup]

sepref_definition get_var_pos_c_impl
  is \<open>uncurry get_var_pos_c\<close>
  :: \<open>perfect_shared_vars_assn\<^sup>k *\<^sub>a string_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  supply [simp] = in_dom_m_lookup_iff
  unfolding get_var_pos_c_def fmlookup'_def[symmetric]
  by sepref

sepref_definition is_new_variable_c_impl
  is \<open>uncurry is_new_variable_c\<close>
  :: \<open>string_assn\<^sup>k  *\<^sub>a  perfect_shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [simp] = in_dom_m_lookup_iff
  unfolding is_new_variable_c_def fmlookup'_def[symmetric] in_dom_m_lookup_iff
  by sepref

definition nth_uint64 where
  \<open>nth_uint64 = (!)\<close>

definition arl_get' :: \<open>'a::heap array_list \<Rightarrow> integer \<Rightarrow> 'a Heap\<close> where
  [code del]: \<open>arl_get' a i = arl_get a (nat_of_integer i)\<close>

definition arl_get_u :: \<open>'a::heap array_list \<Rightarrow> uint64 \<Rightarrow> 'a Heap\<close> where
  \<open>arl_get_u \<equiv> \<lambda>a i. arl_get' a (integer_of_uint64 i)\<close>

lemma arl_get_hnr_u[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure A\<close>
  shows \<open>(uncurry arl_get_u, uncurry (RETURN \<circ>\<circ> op_list_get))
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
      (sep_auto simp: uint64_nat_rel_def br_def array_assn_def is_array_def
        hr_comp_def list_rel_pres_length param_nth arl_assn_def
        A' A[symmetric] pure_def arl_get_u_def Array.nth'_def arl_get'_def
     nat_of_uint64_code[symmetric])
qed


definition arl_get_u' where
  [symmetric, code]: \<open>arl_get_u' = arl_get_u\<close>

lemma arl_get'_nth'[code]: \<open>arl_get' = (\<lambda>(a, n). Array.nth' a)\<close>
  unfolding arl_get_def arl_get'_def Array.nth'_def
  by (intro ext) auto

definition nat_of_uint64_s :: \<open>nat \<Rightarrow> nat\<close> where
  [simp]: \<open>nat_of_uint64_s x = x\<close>

lemma [refine]:
  \<open>(return o nat_of_uint64, RETURN o nat_of_uint64_s) \<in> uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by (sepref_to_hoare)
    (sep_auto simp: uint64_nat_rel_def br_def)


sepref_definition get_var_name_c_impl
  is \<open>uncurry get_var_name_c\<close>
  :: \<open>perfect_shared_vars_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  supply [simp] = in_dom_m_lookup_iff
  unfolding get_var_name_c_def fmlookup'_def[symmetric]
  by sepref

lemma [sepref_fr_rules]:
  \<open>(uncurry is_new_variable_c_impl, uncurry is_new_variableS) \<in> string_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using is_new_variable_c_impl.refine[FCOMP is_new_variable_c_is_new_variableS, of Id]
  by auto

lemma [sepref_fr_rules]:
  \<open>(uncurry get_var_pos_c_impl, uncurry get_var_posS) \<in> shared_vars_assn\<^sup>k *\<^sub>a string_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  using get_var_pos_c_impl.refine[FCOMP get_var_pos_c_get_var_posS, of Id]
  by auto

lemma [sepref_fr_rules]:
  \<open>(uncurry get_var_name_c_impl, uncurry get_var_nameS) \<in> shared_vars_assn\<^sup>k *\<^sub>a  uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  using get_var_name_c_impl.refine[FCOMP get_var_name_c_get_var_nameS, of Id]
 by auto

sepref_register get_var_nameS get_var_posS is_new_variableS


abbreviation memory_allocation_rel :: \<open>(memory_allocation \<times> memory_allocation) set\<close> where
  \<open>memory_allocation_rel \<equiv> Id\<close>

abbreviation memory_allocation_assn :: \<open>memory_allocation \<Rightarrow> memory_allocation \<Rightarrow> assn\<close> where
  \<open>memory_allocation_assn \<equiv> id_assn\<close>

instantiation memory_allocation :: default
begin
  definition default_memory_allocation :: \<open>memory_allocation\<close> where
    \<open>default_memory_allocation = Allocated\<close>
instance
  ..
end

term import_polyS
lemma [sepref_import_param]:
  \<open>(Allocated, Allocated) \<in> memory_allocation_rel\<close>
  \<open>(Mem_Out, Mem_Out) \<in> memory_allocation_rel\<close>
  \<open>(alloc_failed, alloc_failed) \<in> memory_allocation_rel \<rightarrow> bool_rel\<close>
  by auto

lemma pow_2_63_1: \<open>2 ^ 63 - 1 = (9223372036854775807 :: nat)\<close>
  by auto
definition zero_uint64_nat where
  \<open>zero_uint64_nat = 0\<close>
sepref_register zero_uint64_nat
lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN zero_uint64_nat))\<in>unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding zero_uint64_nat_def uint64_nat_rel_def br_def
  by sepref_to_hoare sep_auto

definition length_uint64_nat where
 [simp]: \<open>length_uint64_nat = length\<close>

definition length_arl_u_code :: \<open>('a::heap) array_list \<Rightarrow> uint64 Heap\<close> where
  \<open>length_arl_u_code xs = do {
   n \<leftarrow> arl_length xs;
  return (uint64_of_nat n)}\<close>

definition uint64_max :: nat where
  \<open>uint64_max = 2 ^64 - 1\<close>

lemma nat_of_uint64_uint64_of_nat: \<open>b \<le> uint64_max \<Longrightarrow> nat_of_uint64 (uint64_of_nat b) = b\<close>
  unfolding uint64_of_nat_def uint64_max_def
  apply simp
  apply transfer
  apply (auto simp: unat_def)
  apply transfer
  by (auto simp: less_upper_bintrunc_id)

lemma length_arl_u_hnr[sepref_fr_rules]:
  \<open>(length_arl_u_code, RETURN o length_uint64_nat) \<in>
     [\<lambda>xs. length xs \<le> uint64_max]\<^sub>a (arl_assn R)\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def
      length_arl_u_code_def arl_assn_def nat_of_uint64_uint64_of_nat
      arl_length_def hr_comp_def is_array_list_def list_rel_pres_length[symmetric]
      br_def)

lemma find_new_idx_c_alt_def:
  \<open>find_new_idx_c = (\<lambda>(\<V>, \<A>). let k = length \<V> in if k < 2^63-1 then RETURN (Allocated, length_uint64_nat \<V>) else RETURN (Mem_Out, 0) )\<close>
  unfolding find_new_idx_c_def Let_def by auto


sepref_definition find_new_idx_c_impl
  is \<open>find_new_idx_c\<close>
  :: \<open>perfect_shared_vars_assn\<^sup>k \<rightarrow>\<^sub>aid_assn \<times>\<^sub>a uint64_nat_assn\<close>
  supply [simp] = uint64_max_def
  unfolding find_new_idx_c_alt_def pow_2_63_1 zero_uint64_nat_def[symmetric]
  by sepref

instantiation String.literal :: default
begin
definition default_literal :: \<open>String.literal\<close> where
  \<open>default_literal = String.implode ''''\<close>
instance
  ..
end

sepref_definition insert_variable_c_impl
  is \<open>uncurry2 (RETURN ooo insert_variable_c)\<close>
  :: \<open>string_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a perfect_shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a perfect_shared_vars_assn\<close>
  supply arl_append_hnr[sepref_fr_rules]
    marl_append_hnr[sepref_fr_rules del]
  unfolding insert_variable_c_def
  by sepref

lemmas [sepref_fr_rules] =
  find_new_idx_c_impl.refine insert_variable_c_impl.refine

sepref_definition import_variable_c_impl
  is \<open>uncurry import_variable_c\<close>
  :: \<open>string_assn\<^sup>k *\<^sub>a perfect_shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a id_assn \<times>\<^sub>a perfect_shared_vars_assn \<times>\<^sub>a uint64_nat_assn\<close>
  unfolding import_variable_c_def
  by sepref

lemma import_variable_c_import_variableS':
  assumes \<open>single_valued R\<close> \<open>single_valued (R\<inverse>)\<close>
  shows \<open>(uncurry import_variable_c, uncurry import_variableS) \<in> R \<times>\<^sub>r perfect_shared_vars_rel_c R \<rightarrow>\<^sub>f
    \<langle>memory_allocation_rel \<times>\<^sub>r perfect_shared_vars_rel_c R \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
  using import_variable_c_import_variableS[OF _ _ assms]
  by (auto intro!: frefI nres_relI)


lemma [sepref_fr_rules]:
  \<open>(uncurry import_variable_c_impl, uncurry import_variableS)
  \<in> string_assn\<^sup>k *\<^sub>a  shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a uint64_nat_assn\<close>
  using import_variable_c_impl.refine[FCOMP import_variable_c_import_variableS', of Id]

 by auto

end
