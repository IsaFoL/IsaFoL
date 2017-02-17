theory CDCL_Two_Watched_Literals_List_Watched_Trail_Code
imports CDCL_Two_Watched_Literals_List_Watched_Code
begin
context twl_array_code
begin

definition valued_atm_on_trail where
  \<open>valued_atm_on_trail M L = 
    (if Pos L \<in> lits_of_l M then Some True
    else if Neg L \<in> lits_of_l M then Some False
    else None)\<close>

type_synonym trail_int = \<open>(nat, nat) ann_lits \<times> bool option list \<times> nat\<close>

definition trail_ref :: \<open>(trail_int \<times> (nat, nat) ann_lits) set\<close> where
  \<open>trail_ref = {((M', xs, k), M). no_dup M \<and> M = M' \<and> 
    (\<forall>L \<in># N\<^sub>1. atm_of L < length xs \<and>  xs ! (atm_of L) = valued_atm_on_trail M (atm_of L)) \<and> 
    k = count_decided M}\<close>

fun cons_trail_Propagated :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Propagated L C M' = Propagated L C # M'\<close>

fun cons_trail_Propagated_tr :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> trail_int \<Rightarrow> trail_int\<close> where
  \<open>cons_trail_Propagated_tr L C (M', xs, k) =
     (Propagated L C # M', xs[atm_of L := Some (is_pos L)], k)\<close>

lemma \<open>(uncurry2 (RETURN ooo cons_trail_Propagated_tr), uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
  [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_ref  \<rightarrow> \<langle>trail_ref\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (case_tac \<open>fst (fst x)\<close>)
  by (auto simp: trail_ref_def valued_atm_on_trail_def
      Decided_Propagated_in_iff_in_lits_of_l nth_list_update')

fun cons_trail_Decided :: \<open>nat literal \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Decided L M' = Decided L # M'\<close>

fun cons_trail_Decided_tr :: \<open>nat literal \<Rightarrow> trail_int \<Rightarrow> trail_int\<close> where
  \<open>cons_trail_Decided_tr L (M', xs, k) =
     (Decided L # M', xs[atm_of L := Some (is_pos L)], k+1)\<close>

lemma \<open>(uncurry (RETURN oo cons_trail_Decided_tr), uncurry (RETURN oo cons_trail_Decided)) \<in>
  [\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f trail_ref  \<rightarrow> \<langle>trail_ref\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (case_tac \<open>fst x\<close>)
  by (auto simp: trail_ref_def valued_atm_on_trail_def
      Decided_Propagated_in_iff_in_lits_of_l nth_list_update')

end
end