theory Pointer_LLVM
  imports
    Isabelle_LLVM.LLVM_DS_Block_Alloc
    Examples.Sorting_Ex_Array_Idxs
    More_Sepref.WB_More_Refinement
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)
hide_const (open) NEMonad.ASSERT NEMonad.RETURN

text \<open> In this theory we define a refinement relation to represent pointers. On the theory side, a
  pointer does not exist. On the LLVM side, it is a real pointer.

  We define a \<open>read\<close> and a \<open>write\<close> function that reads/writes the content of the pointer. We hope
  that LLVM will be able to optimize the code in particular when changing the value. The writing
  function comes in two flavours: \<open>write\<close> that also returns a value vs \<open>update\<close> that only update the
  value of the pointer.


  Because of the way the refinement framework works, extracting the value of a pointer means
  destructing the value.

  As usual in such cases, we need to define a new constant for each function that reads or writes
  the element of the pointer.

\<close>

definition pointer_assn :: \<open>('a \<Rightarrow> 'b::llvm_rep \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b ptr \<Rightarrow> llvm_amemory \<Rightarrow> bool\<close> where
  \<open>pointer_assn R = assn_comp R (\<upharpoonleft>ll_bpto)\<close>

context
  fixes f ::  "'a::llvm_rep \<Rightarrow> _" and  R P and f' and b_assn
  assumes [vcg_rules]: \<open>P x \<Longrightarrow>
  nofail (f' x) \<Longrightarrow> llvm_htriple (R x xi) (f xi) (\<lambda>r. R x xi \<and>* (\<lambda>s. \<exists>xa. (b_assn xa r \<and>* \<up>(RETURN xa \<le> f' x)) s))\<close>
begin

definition ptr_read where
  \<open>ptr_read a = f' a\<close>


definition ptr_read_code :: "'a::llvm_rep ptr \<Rightarrow> _" where
  \<open>ptr_read_code a = doM {
    b \<leftarrow> ll_load a;
    f (b)
  }\<close>

lemma bpto_ptr_read_code: "nofail (f' ys) \<Longrightarrow> llvm_htriple
  (\<upharpoonleft>ll_bpto xs p \<and>* R ys xs \<and>* \<up>\<^sub>d (P ys))
  (ptr_read_code p)
  (\<lambda>r. (\<lambda>s. \<exists>xa. (b_assn xa r \<and>* \<up>(RETURN xa \<le> ptr_read ys)) s) \<and>* \<upharpoonleft>ll_bpto xs p \<and>* (\<lambda>s. True))"  
  unfolding ptr_read_code_def ptr_read_def
  apply vcg
  apply (auto simp: ENTAILS_def)
  by (smt (verit, del_insts) conj_entails_mono entails_def pure_true_conv sep.add.right_neutral sep_conj_left_commute)

lemma bpto_ptr_read_code2: "nofail (f' ys) \<Longrightarrow> llvm_htriple
  (pointer_assn R ys p \<and>* \<up>\<^sub>d (P ys))
  (ptr_read_code p)
  (\<lambda>r. (\<lambda>s. \<exists>xa. (b_assn xa r \<and>* \<up>(RETURN xa \<le> ptr_read ys)) s) \<and>* pointer_assn R ys p)"  
  unfolding ptr_read_code_def pointer_assn_def assn_comp_def ptr_read_def
  apply vcg
  done
end


lemma no_fail_ptr_read_iff: \<open>nofail (ptr_read f' x) \<longleftrightarrow> nofail (f' x)\<close>
 by (auto simp: ptr_read_def)

lemma exists_eq_star_conv': "(\<lambda>s. (\<exists>x. (\<up>(x = k) \<and>* F x) s)) = F k"
  by (auto simp: sep_algebra_simps sep_conj_def pred_lift_extract_simps)

locale ptr_read_loc =
  fixes f ::  "'a::llvm_rep \<Rightarrow> _" and f' and ptr_assn and b_assn and R and P
  assumes H: \<open>(f, f') \<in> [P]\<^sub>a (R)\<^sup>k \<rightarrow> b_assn\<close>
  notes [[sepref_register_adhoc f']]
  notes [fcomp_norm_unfold] = pointer_assn_def[symmetric]
begin


lemma ptr_read_code_rule:
  assumes \<open>nofail (f' ys)\<close>
  shows "llvm_htriple (pointer_assn R ys p \<and>* \<up>\<^sub>dP ys) (ptr_read_code f p)
 (\<lambda>r. (\<lambda>s. \<exists>xa. (b_assn xa r \<and>* \<up>(RETURN xa \<le> ptr_read f' ys)) s) \<and>* pointer_assn R ys p)"
  apply (rule bpto_ptr_read_code2)
  unfolding htriple_def
  apply (intro conjI impI allI)
  apply (rule wpa_monoI)
  apply (rule H[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv sep.add_assoc, rule_format])
  apply assumption
  apply assumption
  apply (auto simp: pure_def exists_eq_star_conv' assms)
  done



lemma ptr_read_code: \<open>(ptr_read_code f, ptr_read f') \<in> [P]\<^sub>a (pointer_assn R)\<^sup>k \<rightarrow> b_assn\<close>
  supply [simp] = no_fail_ptr_read_iff
  supply [vcg_rules] = ptr_read_code_rule
  apply sepref_to_hoare
  apply vcg
  done

end



context
  fixes f ::  "'a::llvm_rep \<Rightarrow> _" and  R P and f' and b_assn and S
  assumes writer_rule: \<open>P x \<Longrightarrow>
  nofail (f' x) \<Longrightarrow> llvm_htriple (R x xi) (f xi) (\<lambda>r. (\<lambda>s. \<exists>xa xb. (R xa (fst r) \<and>* S xb (snd r) \<and>* \<up>(RETURN (xa, xb) \<le> f' x)) s) \<and>* \<box>)\<close>
begin

definition ptr_write where
  \<open>ptr_write a = f' a\<close>


definition ptr_write_code :: "'a::llvm_rep ptr \<Rightarrow> ('a ptr \<times> 'e) llM" where
  \<open>ptr_write_code a = doM {
    b \<leftarrow> ll_load a;
    (c, d) \<leftarrow> f (b);
    ll_store c a;
    Mreturn (a, d)
  }\<close>

lemma bpto_ptr_write_code2: "nofail (f' ys) \<Longrightarrow> llvm_htriple
  (pointer_assn R ys p \<and>* \<up>\<^sub>d (P ys))
  (ptr_write_code p)
  (\<lambda>r. (\<lambda>s. \<exists>xa xb. (pointer_assn R xa (fst r) \<and>* S xb (snd r) \<and>* \<up>(RETURN (xa, xb) \<le> ptr_write ys)) s) \<and>* \<box>)"
  supply [vcg_rules] = writer_rule
  unfolding ptr_write_code_def pointer_assn_def assn_comp_def ptr_write_def
  apply vcg
  done

end

lemma [simp]: \<open>nofail (ptr_write f' x) \<longleftrightarrow> nofail (f' x)\<close>
  by (auto simp: ptr_write_def)

locale ptr_write_loc =
  fixes f ::  "'a::llvm_rep \<Rightarrow> _" and f' and ptr_assn and b_assn and R and P and S
  assumes H: \<open>(f, f') \<in> [P]\<^sub>a (R)\<^sup>d \<rightarrow> R \<times>\<^sub>a S\<close>
  notes [[sepref_register_adhoc f']]
  notes [fcomp_norm_unfold] = pointer_assn_def[symmetric]
begin

lemma ptr_write_code_rule:
  assumes \<open>nofail (f' ys)\<close>
  shows "llvm_htriple (pointer_assn R ys p \<and>* \<up>\<^sub>dP ys) (ptr_write_code f p)
    (\<lambda>r. (\<lambda>s. \<exists>xa xb. (pointer_assn R xa (fst r) \<and>*  S xb (snd r) \<and>* \<up>(RETURN (xa, xb) \<le> ptr_write f' ys)) s) \<and>* \<box>)"
  (*supply [vcg_rules] = bpto_ptr_write_code2 does not work it looses track of dependencies between variables*)
  apply vcg
  apply (subst POSTCOND_def)
  apply (rule bpto_ptr_write_code2[simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv sep.add_assoc, rule_format, where P=P])
defer
 apply (rule assms)
 apply (auto simp: pure_def exists_eq_star_conv' assms SOLVE_AUTO_DEFER_def
     pure_true_conv)[]

  apply (rule wpa_monoI)
  apply (rule H[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv sep.add_assoc, rule_format])
  apply assumption back
  apply assumption
  apply assumption
  apply (auto simp: pure_def exists_eq_star_conv' assms)
  apply (rule STATE_monoI)
  apply assumption
  by (simp add: STATE_extract(2) invalid_assn_def pure_true_conv)

lemma ptr_write_code: \<open>(ptr_write_code f, ptr_write f') \<in> [P]\<^sub>a (pointer_assn R)\<^sup>d \<rightarrow> pointer_assn R \<times>\<^sub>a S\<close>
  supply [vcg_rules] = ptr_write_code_rule
  apply sepref_to_hoare
  apply vcg
  done

end



context
  fixes f ::  "'a::llvm_rep \<Rightarrow> _" and  R P and f' and b_assn and S
  assumes updater_rule: \<open>P x \<Longrightarrow>
  nofail (f' x) \<Longrightarrow> llvm_htriple (R x xi) (f xi) (\<lambda>r. (\<lambda>s. \<exists>xa xb. (R xa r \<and>* \<up>(RETURN (xa) \<le> f' x)) s) \<and>* \<box>)\<close>
begin

definition ptr_update where
  \<open>ptr_update a = f' a\<close>


definition ptr_update_code :: "'a::llvm_rep ptr \<Rightarrow> ('a ptr) llM" where
  \<open>ptr_update_code a = doM {
    b \<leftarrow> ll_load a;
    c \<leftarrow> f (b);
    ll_store c a;
    Mreturn (a)
  }\<close>

lemma bpto_ptr_update_code2: "nofail (f' ys) \<Longrightarrow> llvm_htriple
  (pointer_assn R ys p \<and>* \<up>\<^sub>d (P ys))
  (ptr_update_code p)
  (\<lambda>r. (\<lambda>s. \<exists>xa xb. (pointer_assn R xa r \<and>* \<up>(RETURN (xa) \<le> ptr_update ys)) s) \<and>* \<box>)"
  supply [vcg_rules] = updater_rule
  unfolding ptr_update_code_def pointer_assn_def assn_comp_def ptr_update_def
  apply vcg
  done

end

lemma [simp]: \<open>nofail (ptr_update f' x) \<longleftrightarrow> nofail (f' x)\<close>
  by (auto simp: ptr_update_def)


locale ptr_update_loc =
  fixes f ::  "'a::llvm_rep \<Rightarrow> _" and f' and ptr_assn and b_assn and R and P and S
  assumes H: \<open>(f, f') \<in> [P]\<^sub>a (R)\<^sup>d \<rightarrow> R\<close>
  notes [fcomp_norm_unfold] = pointer_assn_def[symmetric]
begin

lemma ptr_update_code_rule:
  assumes \<open>nofail (f' ys)\<close>
  shows "llvm_htriple (pointer_assn R ys p \<and>* \<up>\<^sub>dP ys) (ptr_update_code f p)
    (\<lambda>r. (\<lambda>s. \<exists>xa xb. (pointer_assn R xa r \<and>*  \<up>(RETURN xa \<le> ptr_update f' ys)) s) \<and>* \<box>)"
  (*supply [vcg_rules] = bpto_ptr_update_code2 does not work it looses track of dependencies between variables*)
  apply vcg
  apply (subst POSTCOND_def)
  apply (rule bpto_ptr_update_code2[simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv sep.add_assoc, rule_format, where P=P])
defer
 apply (rule assms)
 apply (auto simp: pure_def exists_eq_star_conv' assms SOLVE_AUTO_DEFER_def
     pure_true_conv)[]

  apply (rule wpa_monoI)
  apply (rule H[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv sep.add_assoc, rule_format])
  apply assumption back
  apply assumption
  apply assumption
  apply (auto simp: pure_def exists_eq_star_conv' assms)
  apply (rule STATE_monoI)
  apply assumption
  by (simp add: STATE_extract(2) invalid_assn_def pure_true_conv)

lemma ptr_update_hnr: \<open>(ptr_update_code f, ptr_update f') \<in> [P]\<^sub>a (pointer_assn R)\<^sup>d \<rightarrow> pointer_assn R\<close>
  supply [vcg_rules] = ptr_update_code_rule
  apply sepref_to_hoare
  apply vcg
  done

end

end