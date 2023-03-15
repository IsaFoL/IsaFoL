theory IsaSAT_Bump_Heuristics_LLVM
  imports IsaSAT_Bump_Heuristics
    IsaSAT_VMTF_LLVM
    Tuple4_LLVM
    IsaSAT_Bump_Heuristics_State_LLVM
begin


(*TODO remove isa_vmtf_unset = vmtf_unset *)
lemma isa_bump_unset_alt_def:
  \<open>RETURN oo isa_bump_unset = (\<lambda>L vm. case vm of Tuple4 (hstable) (focused) foc a \<Rightarrow>
  RETURN (Tuple4 (if \<not>foc then isa_vmtf_unset L hstable else hstable)
    (if foc then isa_vmtf_unset L focused else focused)
  foc a))\<close>
  unfolding isa_bump_unset_def isa_vmtf_unset_def vmtf_unset_def[symmetric]
  by (auto intro!: ext split: bump_heuristics_splits)


sepref_register vmtf_unset case_tuple4
sepref_def isa_bump_unset_impl
  is \<open>uncurry (RETURN oo isa_bump_unset)\<close>
  :: \<open>[uncurry isa_bump_unset_pre]\<^sub>a atom_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow> heuristic_bump_assn\<close>
  unfolding isa_bump_unset_alt_def isa_bump_unset_pre_def
  by sepref

end