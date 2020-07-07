theory IsaSAT_VMTF_Setup_LLVM
imports IsaSAT_Setup IsaSAT_Literals_LLVM
begin
  (* TODO: Define vmtf_node_rel, such that sepref sees syntactically an assertion of form \<open>pure ...\<close>*)
type_synonym vmtf_node_assn = \<open>(64 word \<times> 32 word \<times> 32 word)\<close>

definition \<open>vmtf_node1_rel \<equiv> { ((a,b,c),(VMTF_Node a b c)) | a b c. True}\<close>
definition \<open>vmtf_node2_assn \<equiv> uint64_nat_assn \<times>\<^sub>a atom.option_assn \<times>\<^sub>a atom.option_assn\<close>

definition \<open>vmtf_node_assn \<equiv> hr_comp vmtf_node2_assn vmtf_node1_rel\<close>
lemmas [fcomp_norm_unfold] = vmtf_node_assn_def[symmetric]


lemma vmtf_node_assn_pure[safe_constraint_rules]: \<open>CONSTRAINT is_pure vmtf_node_assn\<close>
  unfolding vmtf_node_assn_def vmtf_node2_assn_def
  by solve_constraint


(*

  TODO: Test whether this setup is safe in general?
    E.g., synthesize destructors when side-tac can prove is_pure.

lemmas [sepref_frame_free_rules] = mk_free_is_pure
lemmas [simp] = vmtf_node_assn_pure[unfolded CONSTRAINT_def]
*)

lemmas [sepref_frame_free_rules] = mk_free_is_pure[OF vmtf_node_assn_pure[unfolded CONSTRAINT_def]]

lemma
    vmtf_Node_refine1: \<open>(\<lambda>a b c. (a,b,c), VMTF_Node) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> vmtf_node1_rel\<close>
and vmtf_stamp_refine1: \<open>(\<lambda>(a,b,c). a, stamp) \<in> vmtf_node1_rel \<rightarrow> Id\<close>
and vmtf_get_prev_refine1: \<open>(\<lambda>(a,b,c). b, get_prev) \<in> vmtf_node1_rel \<rightarrow> \<langle>Id\<rangle>option_rel\<close>
and vmtf_get_next_refine1: \<open>(\<lambda>(a,b,c). c, get_next) \<in> vmtf_node1_rel \<rightarrow> \<langle>Id\<rangle>option_rel\<close>
  by (auto simp: vmtf_node1_rel_def)

sepref_def VMTF_Node_impl is []
  \<open>uncurry2 (RETURN ooo (\<lambda>a b c. (a,b,c)))\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a (atom.option_assn)\<^sup>k *\<^sub>a (atom.option_assn)\<^sup>k \<rightarrow>\<^sub>a vmtf_node2_assn\<close>
  unfolding vmtf_node2_assn_def by sepref

sepref_def VMTF_stamp_impl
  is [] \<open>RETURN o (\<lambda>(a,b,c). a)\<close>
  :: \<open>vmtf_node2_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding vmtf_node2_assn_def
  by sepref

sepref_def VMTF_get_prev_impl
  is [] \<open>RETURN o (\<lambda>(a,b,c). b)\<close>
  :: \<open>vmtf_node2_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn\<close>
  unfolding vmtf_node2_assn_def
  by sepref

sepref_def VMTF_get_next_impl
  is [] \<open>RETURN o (\<lambda>(a,b,c). c)\<close>
  :: \<open>vmtf_node2_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn\<close>
  unfolding vmtf_node2_assn_def
  by sepref

(* TODO: This should be done automatically! For all structured ID-relations on hr_comp! *)
lemma workaround_hrcomp_id_norm[fcomp_norm_unfold]: \<open>hr_comp R (\<langle>nat_rel\<rangle>option_rel) = R\<close> by simp

lemmas [sepref_fr_rules] =
  VMTF_Node_impl.refine[FCOMP vmtf_Node_refine1]
  VMTF_stamp_impl.refine[FCOMP vmtf_stamp_refine1]
  VMTF_get_prev_impl.refine[FCOMP vmtf_get_prev_refine1]
  VMTF_get_next_impl.refine[FCOMP vmtf_get_next_refine1]




type_synonym vmtf_assn = \<open>vmtf_node_assn ptr \<times> 64 word \<times> 32 word \<times> 32 word \<times> 32 word\<close>

type_synonym vmtf_remove_assn = \<open>vmtf_assn \<times> (32 word array_list64 \<times> 1 word ptr)\<close>


abbreviation vmtf_assn :: \<open>_ \<Rightarrow> vmtf_assn \<Rightarrow> assn\<close> where
  \<open>vmtf_assn \<equiv> (array_assn vmtf_node_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a atom_assn \<times>\<^sub>a atom_assn
    \<times>\<^sub>a atom.option_assn)\<close>

abbreviation atoms_hash_assn :: \<open>bool list \<Rightarrow> 1 word ptr \<Rightarrow> assn\<close> where
  \<open>atoms_hash_assn \<equiv> array_assn bool1_assn\<close>

abbreviation distinct_atoms_assn where
  \<open>distinct_atoms_assn \<equiv> arl64_assn atom_assn \<times>\<^sub>a atoms_hash_assn\<close>

definition vmtf_remove_assn
  :: \<open>isa_vmtf_remove_int \<Rightarrow> vmtf_remove_assn \<Rightarrow> assn\<close>
where
  \<open>vmtf_remove_assn \<equiv> vmtf_assn \<times>\<^sub>a distinct_atoms_assn\<close>

end
