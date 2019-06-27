theory IsaSAT_Watch_List_LLVM
  imports IsaSAT_Watch_List IsaSAT_Literals_LLVM
begin

type_synonym watched_wl_uint32 
  = \<open>(64,(64 word \<times> 32 word \<times> 1 word),64)array_array_list\<close>

abbreviation "watcher_fast_assn \<equiv> uint64_nat_assn *a unat_lit_assn *a bool1_assn   "

end
