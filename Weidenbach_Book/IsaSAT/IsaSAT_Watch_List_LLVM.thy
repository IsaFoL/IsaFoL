theory IsaSAT_Watch_List_LLVM
  imports IsaSAT_Watch_List IsaSAT_Literals_LLVM IsaSAT_Arena_Sorting_LLVM
begin

type_synonym watched_wl_uint32 = \<open>(64,(64 word \<times> 32 word \<times> 1 word),64)array_array_list\<close>

abbreviation \<open>watcher_fast_assn \<equiv> sint64_nat_assn \<times>\<^sub>a unat_lit_assn \<times>\<^sub>a bool1_assn   \<close>
abbreviation \<open>watchlist_fast_assn \<equiv> aal_assn' TYPE(64) TYPE(64) watcher_fast_assn\<close>

lemma [def_pat_rules]: \<open>append_ll \<equiv> op_list_list_push_back\<close>
  by (rule eq_reflection) (auto simp: append_ll_def fun_eq_iff)

sepref_register mop_append_ll mop_arena_length

sepref_def mop_append_ll_impl
  is \<open>uncurry2 mop_append_ll\<close>
  :: \<open>[\<lambda>((W, i), _). length (W ! (nat_of_lit i)) < snat64_max]\<^sub>a
    watchlist_fast_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a watcher_fast_assn\<^sup>k \<rightarrow> watchlist_fast_assn\<close>
  unfolding mop_append_ll_def
  by sepref

sepref_def rewatch_heur_fast_code
  is \<open>uncurry2 (rewatch_heur)\<close>
  :: \<open>[\<lambda>((vdom, arena), W). (\<forall>x \<in> set vdom. x \<le> snat64_max) \<and> length arena \<le> snat64_max \<and>
        length vdom \<le> snat64_max]\<^sub>a
        vdom_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a watchlist_fast_assn\<^sup>d \<rightarrow> watchlist_fast_assn\<close>
  supply [[goals_limit=1]]
     arena_lit_pre_le_snat64_max[dest] arena_is_valid_clause_idx_le_unat64_max[dest]
  supply [simp] = append_ll_def
  supply [dest] = arena_lit_implI(1)
  unfolding rewatch_heur_alt_def Let_def PR_CONST_def
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  unfolding if_not_swap
    FOREACH_cond_def FOREACH_body_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma aal_gen_swap:
  \<open>W[L := LLVM_More_List.swap (W ! L) i j] = 
   (let x = W ! L ! i; y = W ! L ! j; W = op_list_list_upd W L j x; W = op_list_list_upd W L i y in W)\<close>
  apply (auto simp: convert_swap LLVM_More_List.swap_def)
  by (smt (verit, best) list_update_id' list_update_overwrite list_update_swap nth_list_update')

sepref_register watchlist_put_binaries_first_one watchlist_put_binaries_first
sepref_def watchlist_put_binaries_first_one_impl
  is \<open>uncurry watchlist_put_binaries_first_one\<close>
  :: \<open>watchlist_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a watchlist_fast_assn\<close>
   unfolding watchlist_put_binaries_first_one_def
   unfolding if_not_swap convert_swap fold_op_list_list_llen
   unfolding
     convert_swap aal_gen_swap fold_op_list_list_idx op_list_get_def
     op_list_set_def fold_op_list_list_upd
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


sepref_def watchlist_put_binaries_first_impl
  is \<open>watchlist_put_binaries_first\<close>
  :: \<open>watchlist_fast_assn\<^sup>d \<rightarrow>\<^sub>a watchlist_fast_assn\<close>
   unfolding watchlist_put_binaries_first_def
   unfolding if_not_swap convert_swap fold_op_list_list_llen
   unfolding
     convert_swap aal_gen_swap fold_op_list_list_idx op_list_get_def
     op_list_set_def  op_list_list_len_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

end
