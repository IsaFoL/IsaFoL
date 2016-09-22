section \<open>List of Lists as Flat List\<close>
theory Flat_List
imports Main "~~/src/HOL/Library/Rewrite" "$AFP/Refine_Imperative_HOL/IICF/IICF"
begin

subsection \<open>Auxiliary Lemmas\<close>
lemma dropWhile_drop_all[simp]: "\<forall>x\<in>set l. P x \<Longrightarrow> dropWhile P l = []" by simp

lemma takeWhile_append3:
  assumes "\<forall>x\<in>set l1. P x"
  assumes "\<not>P z"
  shows "takeWhile P (l1@z#l2) = l1"
  using assms
  by auto

lemma all_in_set_neq_conv[simp]: 
  "(\<forall>x\<in>set l. x\<noteq>a) \<longleftrightarrow> a\<notin>set l" 
  "(\<forall>x\<in>set l. a\<noteq>x) \<longleftrightarrow> a\<notin>set l" 
  by auto

lemma apfst_eq_conv: "apfst f p = (a,b) \<longleftrightarrow> (\<exists>a'. p=(a',b) \<and> a=f a')"
  by (cases p) auto

lemma apsnd_eq_conv: "apsnd f p = (a,b) \<longleftrightarrow> (\<exists>b'. p=(a,b') \<and> b=f b')"
  by (cases p) auto



subsection \<open>Abstraction Functions\<close>

function flat_\<alpha> :: "'a::zero list \<Rightarrow> 'a list list" where
  "flat_\<alpha> l = (if l=[] then [] else takeWhile (op\<noteq>0) l # flat_\<alpha> (tl (dropWhile (op\<noteq>0) l)))"
by pat_completeness auto
termination 
  apply (relation "measure length")
  by (auto simp: le_imp_less_Suc length_dropWhile_le less_imp_diff_less neq_Nil_conv)

declare flat_\<alpha>.simps[simp del]

function flat_idx_\<alpha> :: "'a::zero list \<Rightarrow> nat \<Rightarrow> nat\<times>nat" where
  "flat_idx_\<alpha> l k = (
    if l=[] then
      (0,0)
    else
      let
        twl = length (takeWhile (op\<noteq>0) l)
      in 
        if k \<le> twl then 
          (0,k)
        else let
            (i,j) = flat_idx_\<alpha> (tl (dropWhile (op\<noteq>0) l)) (k - twl - 1)
          in
            (i+1,j)
  )"  
  by pat_completeness auto
termination 
  apply (relation "measure (\<lambda>(l,k). length l)")
  apply auto
  by (metis (no_types, lifting) Nat.diff_le_self diff_less le_less_trans length_dropWhile_le length_greater_0_conv lessI not_le)

declare flat_idx_\<alpha>.simps[simp del]


definition "flat_invar l \<equiv> l=[] \<or> last l = 0"
definition "flat_idx_invar0 l k \<longleftrightarrow> l\<noteq>[] \<and> k<length l"
definition "flat_idx_invar l k \<longleftrightarrow> k<length l \<and> l!k\<noteq>0"

subsubsection \<open>Custom Induction Scheme\<close>

lemma flat_split:
  assumes "l\<noteq>[]"  
  assumes "flat_invar l"
  obtains l1 l2 where "l=l1@0#l2" "0\<notin>set l1" "flat_invar l2"
proof -
  from assms have "0\<in>set l" by (cases l rule: rev_cases) (auto simp: flat_invar_def)
  with in_set_conv_decomp_first[of 0 l] obtain l1 l2 where [simp]: "l=l1@0#l2" and "0\<notin>set l1"
    by auto
  moreover from assms(2) have "flat_invar l2"
    unfolding flat_invar_def
    by (auto split: split_if_asm)
  ultimately show ?thesis by (rule that)  
qed

lemma flat_induct[consumes 1, case_names empty split]:
  assumes INV: "flat_invar l"
  assumes S0: "P []"
  assumes SS: "\<And>l1 l2. \<lbrakk> 0\<notin>set l1; flat_invar l2; P l2 \<rbrakk> \<Longrightarrow> P (l1@0#l2)"
  shows "P l"
  using INV
proof (induction l rule: length_induct)
  case I: (1 l)
  show ?case proof (cases "l=[]")
    case True with assms show ?thesis by simp
  next
    case False 
    then obtain l1 l2 where [simp]: "l=l1@0#l2" and "0\<notin>set l1" and INV':  "flat_invar l2"
      using I.prems by (rule flat_split) 
    moreover from I.IH INV' have "P l2" by auto
    ultimately show ?thesis using SS[of l1 l2] by auto
  qed
qed  

text \<open>We also define the corresponding function equations\<close>

lemma flat_\<alpha>_simps[simp]:
  "flat_\<alpha> [] = []"
  "0\<notin>set l1 \<Longrightarrow> flat_\<alpha> (l1@0#l2) = l1#flat_\<alpha> l2"
  subgoal by (rewrite at "\<hole>=_" flat_\<alpha>.simps; auto)
  subgoal by (rewrite at "\<hole>=_" flat_\<alpha>.simps) (auto simp: takeWhile_tail dropWhile_append3)
  done


lemma flat_idx_\<alpha>_simp1:
  assumes "k\<le>length l1" "0\<notin>set l1"
  shows "flat_idx_\<alpha> (l1@0#l2) k = (0,k)"
  using assms
  apply (subst flat_idx_\<alpha>.simps)
  by (auto simp: Let_def takeWhile_append3 split: prod.split)

lemma flat_idx_\<alpha>_simp2:
  assumes "k>length l1" "0\<notin>set l1"
  shows "flat_idx_\<alpha> (l1@0#l2) k = apfst Suc (flat_idx_\<alpha> l2 (k - length l1 - 1))"  
  using assms
  apply (subst flat_idx_\<alpha>.simps)
  by (auto simp add: Let_def takeWhile_append3 dropWhile_append3 split: prod.split)

lemmas flat_idx_\<alpha>_simps[simp] = flat_idx_\<alpha>_simp1 flat_idx_\<alpha>_simp2

lemma flat_idx_invar0_empty[simp]: "\<not>flat_idx_invar0 [] k"
  by (auto simp: flat_idx_invar0_def)

lemma flat_idx_invar_empty[simp]: "\<not>flat_idx_invar [] k"
  by (auto simp: flat_idx_invar_def)

lemma flat_idx_invar0_split_conv[simp]: 
  assumes "0\<notin>set l1"
  shows "flat_idx_invar0 (l1@0#l2) k \<longleftrightarrow> (k\<le>length l1 \<or> k>length l1 \<and> flat_idx_invar0 l2 (k-length l1 - 1))"
  using assms
  unfolding flat_idx_invar0_def
  apply (auto simp: nth_append nth_Cons in_set_conv_nth split: nat.splits)
  done

lemma flat_idx_invar_split_conv[simp]: 
  assumes "0\<notin>set l1"
  shows "flat_idx_invar (l1@0#l2) k \<longleftrightarrow> (k<length l1 \<or> k>length l1 \<and> flat_idx_invar l2 (k-length l1 - 1))"
  using assms
  unfolding flat_idx_invar_def
  apply (clarsimp simp: nth_append nth_Cons in_set_conv_nth split: nat.splits)
  by (metis Suc_diff_Suc diff_Suc_1 diff_diff_left not_less_eq zero_less_Suc zero_less_diff)



subsection \<open>Operations\<close>

subsubsection \<open>Indexing\<close>

definition "nth0 l i \<equiv> 
  if i<length l then l!i 
  else if i=length l then 0
  else undefined"

lemma nth0_simps[simp]: 
  "i<length l \<Longrightarrow> nth0 l i = l!i"
  "nth0 l (length l) = 0"
  unfolding nth0_def by auto

definition "l2_nth \<equiv> \<lambda>l (i,j). nth0 (l!i) j"

lemma ls_nth_simps[simp]: 
  "l2_nth (l#ls) (0,k) = nth0 l k"
  "l2_nth (l#ls) (apfst Suc p) = l2_nth ls p"
  unfolding l2_nth_def
  by (auto split: prod.split)

definition "list_update2 \<equiv> \<lambda>l (i,j) x. l[i := (l!i)[j:=x]]"


lemma flat_idx_correct_aux:
  assumes "flat_invar l"
  assumes "flat_idx_invar0 l k"
  shows "l!k = l2_nth (flat_\<alpha> l) (flat_idx_\<alpha> l k)"
  using assms
  apply (induction l arbitrary: k rule: flat_induct)
  apply (auto simp: nth_append apfst_eq_conv)
  done  


lemma flat_\<alpha>_no_zero:
  assumes "flat_invar l"
  assumes "ll\<in>set (flat_\<alpha> l)"
  shows "0\<notin>set ll"
  using assms
  by (induction l rule: flat_induct) auto

lemma flat_idx_invar0_conv:
  assumes "flat_invar l"
  assumes "flat_idx_invar0 l k"
  assumes "l2_nth (flat_\<alpha> l) (flat_idx_\<alpha> l k) \<noteq> 0"
  shows "flat_idx_invar l k"
  by (metis assms flat_idx_correct_aux flat_idx_invar0_def flat_idx_invar_def)
  
lemma flat_idx_invar_conv:
  assumes "flat_idx_invar l k"
  shows "flat_idx_invar0 l k"
  using assms unfolding flat_idx_invar0_def flat_idx_invar_def
  by auto

lemma flat_idx0_\<alpha>_len1:
  assumes "flat_invar l"
  assumes "flat_idx_invar0 l k"
  assumes "flat_idx_\<alpha> l k = (i,j)"
  shows "i<length (flat_\<alpha> l)"
  using assms
  apply (induction arbitrary: k i j rule: flat_induct)
  apply (auto simp: apfst_eq_conv)
  done

lemmas flat_idx_\<alpha>_len1 = flat_idx0_\<alpha>_len1[OF _ flat_idx_invar_conv] 

lemma flat_idx0_\<alpha>_len2:
  assumes "flat_invar l"
  assumes "flat_idx_invar0 l k"
  assumes "flat_idx_\<alpha> l k = (i,j)"
  shows "j\<le>length (flat_\<alpha> l ! i)"
  using assms
  apply (induction arbitrary: k i j rule: flat_induct)
  apply (auto simp: apfst_eq_conv)
  done

lemma flat_idx_\<alpha>_len2:
  assumes "flat_invar l"
  assumes "flat_idx_invar l k"
  assumes "flat_idx_\<alpha> l k = (i,j)"
  shows "j<length (flat_\<alpha> l ! i)"
  using assms
  apply (induction arbitrary: k i j rule: flat_induct)
  apply (auto simp: apfst_eq_conv)
  done


lemma flat_idx_invar0_conv':
  assumes INV: "flat_invar l"
  assumes IINV: "flat_idx_invar0 l k"
  assumes A: "flat_idx_\<alpha> l k = (i,j)"
  assumes JL: "j < length (flat_\<alpha> l ! i)"
  shows "flat_idx_invar l k"
  by (metis assms flat_\<alpha>_no_zero flat_idx0_\<alpha>_len1 flat_idx_invar0_conv 
    in_set_conv_nth l2_nth_def nth0_simps(1) prod.simps(2))


subsubsection \<open>Updating\<close>

lemma flat_aux_in_upd_set: "\<lbrakk>a\<notin>set l; x\<noteq>a\<rbrakk> \<Longrightarrow> a\<notin>set (l[i:=x])"
  by (auto elim: in_set_upd_cases)

lemma flat_aux_kdlD: "k - l = Suc x2 \<Longrightarrow> x2 = k - Suc l" by auto

lemma flat_idx_upd_correct_aux:
  assumes "flat_invar l"
  assumes "flat_idx_invar l k"
  assumes "flat_idx_\<alpha> l k = (i,j)"
  assumes "x\<noteq>0"
  shows "flat_\<alpha> (l[k:=x]) = (flat_\<alpha> l)[ i := (flat_\<alpha> l ! i)[j := x]]"
proof -
  note [simp] = flat_aux_in_upd_set
  note [dest] = flat_aux_kdlD  

  show ?thesis
    using assms
    apply (induction l arbitrary: k i j rule: flat_induct)
    apply (auto simp: list_update_append apfst_eq_conv split: nat.split)
    done
qed
  
lemma flat_upd_pres_idx_invar:
  fixes l :: "'a::zero list"
  assumes "flat_idx_invar l k"
  assumes "x\<noteq>0"
  shows 
    "flat_idx_invar0 l k' \<Longrightarrow> flat_idx_invar0 (l[k:=x]) k'"
    "flat_idx_invar l k' \<Longrightarrow> flat_idx_invar (l[k:=x]) k'"
  using assms
  by (auto simp: flat_idx_invar_def flat_idx_invar0_def nth_list_update)

lemma flat_upd_pres_idx_\<alpha>:
  fixes l :: "'a::zero list"
  assumes "flat_invar l"
  assumes "flat_idx_invar l k"
  assumes "flat_idx_invar0 l k'"
  assumes "x\<noteq>0"
  shows "flat_idx_\<alpha> (l[k:=x]) k' = flat_idx_\<alpha> l k'"
  using assms
  apply (induction arbitrary: k k' rule: flat_induct)
  apply (auto 
    simp: list_update_append apfst_eq_conv flat_aux_in_upd_set
    split: nat.split 
    dest!: flat_aux_kdlD)
  done


lemma flat_append_pres_idx_invar:
  shows 
    "flat_idx_invar0 l k \<Longrightarrow> flat_idx_invar0 (l@ll) k"
    "flat_idx_invar l k \<Longrightarrow> flat_idx_invar (l@ll) k"
  by (auto simp: flat_idx_invar_def nth_append flat_idx_invar0_def)

lemma flat_append_pres_idx_\<alpha>:
  assumes "flat_invar l"
  assumes "flat_idx_invar l k"
  shows "flat_idx_\<alpha> (l@ll) k = flat_idx_\<alpha> l k"
  using assms
  by (induction arbitrary: k rule: flat_induct) auto

lemma flat_append_\<alpha>: 
  assumes "flat_invar l" "flat_invar ll"
  shows "flat_\<alpha> (l@ll) = flat_\<alpha> l @ flat_\<alpha> ll"
  using assms
  by (induction rule: flat_induct) auto

lemma flat_append_invar: 
  assumes "flat_invar l" "flat_invar ll"
  shows "flat_invar (l@ll)"
  using assms 
  by (auto simp: flat_invar_def last_append)

lemma flat_append_new_idx_invar:
  shows 
    "flat_idx_invar0 ll k \<Longrightarrow> flat_idx_invar0 (l@ll) (k+length l)"
    "flat_idx_invar ll k \<Longrightarrow> flat_idx_invar (l@ll) (k+length l)"
  using assms by (auto simp: flat_idx_invar_def flat_idx_invar0_def nth_append)

lemma flat_append_new_idx_\<alpha>:
  assumes "flat_invar l" "flat_invar ll"
  assumes "flat_idx_invar0 ll k"
  assumes "flat_idx_\<alpha> ll k = (i,j)"
  shows "flat_idx_\<alpha> (l@ll) (k+length l) = (length (flat_\<alpha> l)+i,j)"
  using assms 
  by (induction rule: flat_induct) auto  


lemma flat_idx_incr_invar:
  assumes "flat_invar l"
  assumes "flat_idx_invar l k"
  shows "flat_idx_invar0 l (k+1)"
  using assms
  unfolding flat_invar_def flat_idx_invar_def flat_idx_invar0_def
  apply (cases l rule: rev_cases)
  apply (auto simp: nth_append split: split_if_asm)
  done

lemma flat_idx_incr_\<alpha>:
  assumes "flat_invar l"
  assumes "flat_idx_invar l k"
  shows "flat_idx_\<alpha> l (k+1) = apsnd Suc (flat_idx_\<alpha> l k)"
  using assms
  apply (induction arbitrary: k rule: flat_induct)
  subgoal by simp
  subgoal by (force simp: apfst_eq_conv apsnd_eq_conv) 
  done

(*
subsubsection \<open>Relations\<close>

definition "flat_rel \<equiv> br flat_\<alpha> flat_invar"
definition "flat_idx_rel l \<equiv> br (flat_idx_\<alpha> l) (flat_idx_invar l)"
definition "flat_idx0_rel l \<equiv> br (flat_idx_\<alpha> l) (flat_idx_invar0 l)"

definition "flat_outer_idx_rel l \<equiv> {(k,i). (k,(i,0))\<in>flat_idx0_rel l}"
definition "flat_inner_idx_rel l i \<equiv> {(k,j). (k,(i,j))\<in>flat_idx_rel l}"
definition "flat_inner_idx0_rel l i \<equiv> {(k,j). (k,(i,j))\<in>flat_idx0_rel l}"

definition "flat_elem_rel \<equiv> br id (\<lambda>l. 0\<notin>set l)"

definition "flat_op_snoc ls l \<equiv> (length ls, ls@l@[0])"
definition "flat_op_init_idx k \<equiv> k"
definition "flat_op_incr_idx k \<equiv> k+1"
definition "flat_op_get ls k \<equiv> ls!k"
definition "flat_op_set ls k x \<equiv> list_update ls k x"



definition dprod_rel (infixr "<\<times>>" 80)
  where "dprod_rel R1 R2 \<equiv> {((ai,bi),(a,b)). (ai,a)\<in>R1 bi \<and> (bi,b)\<in>R2 ai}"

lemma dprod_rel_indep[simp]: "(\<lambda>_. R1)<\<times>>(\<lambda>_. R2) = R1\<times>\<^sub>rR2"
  unfolding dprod_rel_def prod_rel_def 
  by auto

lemma dprod_rel_simp[simp]: "((ai,bi),(a,b))\<in>R1<\<times>>R2 \<longleftrightarrow> (ai,a)\<in>R1 bi \<and> (bi,b)\<in>R2 ai"
  unfolding dprod_rel_def
  by auto

lemma dprod_relI: "\<lbrakk>(ai,a)\<in>R1 bi; (bi,b)\<in>R2 ai\<rbrakk> \<Longrightarrow> ((ai,bi),(a,b))\<in>R1<\<times>>R2"
  by simp

lemma dprod_relE:
  assumes "(pi,p)\<in>R1<\<times>>R2"
  obtains ai a bi b where "pi=(ai,bi)" "p=(a,b)" "(ai,a)\<in>R1 bi" "(bi,b)\<in>R2 ai"
  using assms by (cases pi; cases p; auto)


abbreviation dprod_rel_left (infixr "<\<times>" 80) where "R1<\<times>R2 \<equiv> R1<\<times>>(\<lambda>_. R2)"
abbreviation dprod_rel_right (infixr "\<times>>" 80) where "R1\<times>>R2 \<equiv> (\<lambda>_. R1)<\<times>>R2"

definition "op_llist_append ll l \<equiv> (length ll,ll@[l])"


lemma flat_invar_sng: "0\<notin>set l \<Longrightarrow> flat_invar (l@[0])"
  unfolding flat_invar_def by auto

lemma "(flat_op_snoc, op_llist_append) \<in> flat_rel \<rightarrow> flat_elem_rel \<rightarrow> flat_outer_idx_rel<\<times>flat_rel"
  apply (intro fun_relI)
  subgoal for ll ls li l   
    unfolding flat_op_snoc_def op_llist_append_def
    using 
      flat_append_new_idx_\<alpha>[of ll _ 0 0 0,OF _ flat_invar_sng[of li]]
      flat_append_new_idx_invar[of "li@[0]" 0 ll]
      flat_append_\<alpha>[OF _ flat_invar_sng[of li]]
      flat_append_invar[OF _ flat_invar_sng[of li]]
    by (auto simp: flat_rel_def flat_elem_rel_def br_def flat_outer_idx_rel_def flat_idx_rel_def 
      flat_idx0_rel_def)
  done

lemma   
  assumes "(k,i)\<in>flat_outer_idx_rel l"
  shows   "(flat_op_init_idx k, (i,0)) \<in> flat_idx0_rel l"
  using assms 
  unfolding flat_outer_idx_rel_def flat_inner_idx_rel_def flat_idx0_rel_def flat_idx_rel_def br_def
    flat_op_init_idx_def
  by auto

lemma 
  assumes "(l,ls)\<in>flat_rel"
  assumes "(k,(i,j))\<in>flat_idx0_rel l"
  assumes "j<length (ls!i)"
  shows "(k,(i,j))\<in>flat_idx_rel l"
  using assms
  unfolding flat_rel_def flat_idx0_rel_def flat_idx_rel_def br_def
  using flat_idx_invar0_conv'[of l k]
  by force

lemma "\<lbrakk> (l,ls)\<in>flat_rel \<rbrakk> \<Longrightarrow> (flat_op_incr_idx, apsnd Suc) \<in> flat_idx_rel l \<rightarrow> flat_idx0_rel l"
  apply (intro fun_relI)
  unfolding flat_op_incr_idx_def flat_idx_rel_def flat_idx0_rel_def br_def flat_rel_def
  using flat_idx_incr_invar flat_idx_incr_\<alpha>
  by force  

lemma " \<lbrakk> (l,ls)\<in>flat_rel; (k,ij)\<in>flat_idx0_rel l \<rbrakk> \<Longrightarrow> (flat_op_get l k, l2_nth ls ij) \<in> Id"
  unfolding flat_rel_def flat_idx0_rel_def br_def
  by (auto simp: flat_idx_correct_aux flat_op_get_def)
  
lemma " \<lbrakk> (l,ls)\<in>flat_rel; (k,ij)\<in>flat_idx_rel l; (xi,x)\<in>Id; x\<noteq>0 \<rbrakk> \<Longrightarrow> 
  (flat_op_set l k x, list_update2 ls ij x) \<in> flat_rel"
  unfolding flat_rel_def flat_idx_rel_def br_def
  using flat_idx_upd_correct_aux flat_
  apply (auto simp: flat_op_set_def list_update2_def split: prod.split)
  apply force


oops
xxx, ctd here: 
  define relations for db, outer-idx, inner-idx, idx, idx\<^sub>0
  and exactly the below operations + conversion between idx and idx\<^sub>0

  Types: 
    outer-index: Index into outer list (wrt DB)
    inner-index: Index into inner list (wrt outer-index and DB)

  Operations:
    snoc: db \<rightarrow> elem list \<rightarrow> outer-idx \<times> db
      append element list, and return its index

    compose: outer-idx \<rightarrow> inner-idx \<rightarrow> idx
      compute index
    
    increment: idx \<rightarrow> idx
      next idx

    get: db \<rightarrow> idx\<^sub>0 \<rightarrow> elem\<^sub>0  
      get element, or zero if index at length of inner list.
      (Used for iteration)

    set: db \<rightarrow> idx \<rightarrow> elem \<rightarrow> db
      set element at index



oops
xxx, ctd here:
  update preserves idx_invar



oops end end oops end end






lemma flat_idx_inv_len_aux:
  assumes INV: "flat_idx_invar l k"
  assumes GE: "k\<ge>length (takeWhile (op \<noteq> 0) l)" (is "_ \<ge> ?ltw")
  shows "k\<ge>Suc ?ltw"
proof -
  have "k\<noteq>?ltw"
  proof
    assume "k = ?ltw"
    with INV show False
      by (auto dest: nth_length_takeWhile simp: flat_idx_invar_def)
  qed  
  with GE show ?thesis by auto
qed

lemma flat_idx_inv_pres_aux:
  fixes l :: "'a::zero list"
  assumes INV: "flat_idx_invar l k"
  assumes GE: "k\<ge>length (takeWhile (op \<noteq> 0) l)" (is "_ \<ge> length ?tw")
  shows "flat_idx_invar (tl (dropWhile (op \<noteq> 0) l)) (k - length (takeWhile (op \<noteq> 0) l) - 1)"
    (is "flat_idx_invar ?dw _")
proof -
  note GE' = flat_idx_inv_len_aux[OF INV GE]
  from INV GE' show ?thesis
    unfolding flat_idx_invar_def
    apply clarsimp
    apply auto
    subgoal A
    proof -
      assume a1: "k < length l"
      assume a2: "Suc (length (takeWhile (\<lambda>y. y \<noteq> 0) l)) \<le> k"
      have "length l = length (takeWhile (\<lambda>a. a \<noteq> 0) l) + length (dropWhile (\<lambda>a. a \<noteq> 0) l)"
        by (metis (no_types) length_append takeWhile_dropWhile_id)
      then show "k - Suc (length (takeWhile (\<lambda>a. a \<noteq> 0) l)) < length (dropWhile (\<lambda>a. a \<noteq> 0) l) - Suc 0"
        using a2 a1 by linarith
    qed
    subgoal
      by (metis (no_types, lifting) List.nth_tl One_nat_def Suc_diff_Suc 
        Suc_le_lessD A leD length_tl less_SucI nth_append takeWhile_dropWhile_id)
    done
qed    
    
    

  


lemma flat_idx_nth:
  assumes "flat_idx_invar l k"
  assumes "flat_idx_\<alpha> l k = (i,j)"
  shows "l!k = (flat_\<alpha> l)!i!j"
  apply (rule sym)
  using assms
proof (induction l k arbitrary: i j rule: flat_idx_\<alpha>.induct)
  case (1 l k i j)

  note INV = \<open>flat_idx_invar l k\<close>

  from INV have "k<length l" and "l!k\<noteq>0"
    by (auto simp: flat_idx_invar_def)

  from \<open>k<length l\<close> have [simp]: "l\<noteq>[]" by (auto)

  let ?tw = "takeWhile (op \<noteq> 0) l"
  let ?dw = "tl (dropWhile (op \<noteq> 0) l)"

  {
    assume LL: "k<length ?tw"
    hence "flat_idx_\<alpha> l k = (0,k)"
      by (subst flat_idx_\<alpha>.simps) simp
    hence [simp]: "i=0" "j=k" using "1.prems" by auto

    have ?case
      apply (subst flat_\<alpha>.simps)
      using LL
      by (simp add: takeWhile_nth)
  } moreover {
    assume A: "k\<ge>length ?tw"
    note LL = flat_idx_inv_len_aux[OF INV A]
    
    obtain l' k' where FI': "flat_idx_\<alpha> ?dw (k - length ?tw - 1) = (l',k')" 
      by fastforce
    with A have "flat_idx_\<alpha> l k = (Suc l', k')"
      by (subst flat_idx_\<alpha>.simps) simp
    with "1.prems"  (2) have [simp]: "i = Suc l'" "j=k'" by auto
      
    have "flat_\<alpha> l ! i ! j = flat_\<alpha> ?dw!l'!k'"
      by (subst flat_\<alpha>.simps) simp
    also have "\<dots> = ?dw!(k - length ?tw - 1)"
      apply (rule "1.IH"[OF _ _ _ flat_idx_inv_pres_aux FI'])
      using \<open>k < length l\<close> "1.prems" A
      by (auto)
    also have "\<dots> = l!k" using LL \<open>k < length l\<close>
      apply clarsimp
      by (metis Misc.nth_tl Suc_diff_Suc Suc_le_lessD append_Nil2 less_imp_le_nat 
        not_less_eq_eq nth_append takeWhile_dropWhile_id)
    finally have ?case .  
  } ultimately show ?case using not_le by blast
qed
    
lemma takeWhile_update_eq:
  assumes "i<length l"
  assumes "P (l!i) \<longleftrightarrow> P x"
  shows "takeWhile P (l[i:=x]) = (takeWhile P l)[i:=x]"
  using assms
  by (induction l arbitrary: i) (auto split: nat.splits)

lemma takeWhile_update_left:
  assumes "i<length (takeWhile P l)" "P x"
  shows "takeWhile P (l[i:=x]) = (takeWhile P l)[i:=x]"
  apply (rule takeWhile_update_eq)
  using assms
  apply auto
  subgoal by (meson dual_order.trans leD le_less_linear length_takeWhile_le)
  subgoal by (metis nth_mem set_takeWhileD takeWhile_nth)
  done

lemma takeWhile_upd_right:
  assumes "i>length (takeWhile P l)"
  shows "takeWhile P (l[i:=x]) = takeWhile P l"
  using assms
  by (induction l arbitrary: i) (auto split: nat.splits)


lemma dropWhile_upd_left:
  assumes "i<length (takeWhile P l)"
  assumes "P x"
  shows "dropWhile P (l[i:=x]) = dropWhile P l"
  using assms
  by (induction l arbitrary: i) (auto split: nat.splits)

lemma dropWhile_upd_right:
  assumes "i>length (takeWhile P l)"
  assumes "P (l!i) \<longleftrightarrow> P x"
  shows "dropWhile P (l[i:=x]) = (dropWhile P l)[i - length (takeWhile P l):=x]"
  using assms
  by (induction l arbitrary: i) (auto split: nat.splits)


lemma tl_upd_conv: "tl (l[i:=x]) = (case i of 0 \<Rightarrow> tl l | Suc i \<Rightarrow> (tl l)[i:=x])"
  by (cases l) (auto split: nat.split)

lemma tl_upd_Suc[simp]: "tl (l[Suc i := x]) = (tl l)[i:=x]"
  by (simp add: tl_upd_conv)

lemma tl_upd_right[simp]: "i>0 \<Longrightarrow> tl (l[i:=x]) = (tl l)[i-1 := x]"
  by (simp add: tl_upd_conv split: nat.split)

lemma tl_upd_left[simp]: "tl (l[0:=x]) = tl l"
  by (simp add: tl_upd_conv)


lemma flat_idx_upd:
  assumes "flat_idx_invar l k"
  assumes "flat_idx_\<alpha> l k = (i,j)"
  assumes [simp]: "x\<noteq>0"
  shows "flat_\<alpha> (l[k:=x]) = (flat_\<alpha> l)[ i := ((flat_\<alpha> l)!i)[ j := x] ]"
  using assms(1,2)
proof (induction l k arbitrary: i j rule: flat_idx_\<alpha>.induct)
  case (1 l k i j)

  note INV = \<open>flat_idx_invar l k\<close>

  from INV have "k<length l" and [simp]: "l!k\<noteq>0"
    by (auto simp: flat_idx_invar_def)

  from \<open>k<length l\<close> have [simp]: "l\<noteq>[]" by (auto)

  let ?tw = "takeWhile (op \<noteq> 0) l"
  let ?dw = "tl (dropWhile (op \<noteq> 0) l)"

  {
    assume LL: "k<length ?tw"
    hence "flat_idx_\<alpha> l k = (0,k)"
      by (subst flat_idx_\<alpha>.simps) simp
    hence [simp]: "i=0" "j=k" using "1.prems" by auto

    have ?case
      apply (rewrite at "\<hole>=_" flat_\<alpha>.simps)
      apply (rewrite at "_=list_update \<hole> _ _" flat_\<alpha>.simps)
      apply (rewrite in "_[i:=\<hole>]" flat_\<alpha>.simps)
      using LL
      by (auto simp: takeWhile_update_left dropWhile_upd_left)
  } moreover {
    assume A: "k\<ge>length ?tw"
    note LL = flat_idx_inv_len_aux[OF INV A]
    hence LL': "k>length ?tw" by simp
    
    obtain i' j' where FI': "flat_idx_\<alpha> ?dw (k - length ?tw - 1) = (i',j')" 
      by fastforce
    with A have "flat_idx_\<alpha> l k = (Suc i', j')"
      by (subst flat_idx_\<alpha>.simps) simp
    with "1.prems"  (2) have [simp]: "i = Suc i'" "j=j'" by auto

    have "flat_\<alpha> l = ?tw#flat_\<alpha> ?dw"
      by (subst flat_\<alpha>.simps) simp
    hence "flat_\<alpha> l [i := (flat_\<alpha> l ! i)[j := x]] = 
      ?tw#(flat_\<alpha> ?dw [i' := (flat_\<alpha> ?dw!i')[j' := x] ])"
      by simp
    also have "flat_\<alpha> ?dw [i' := (flat_\<alpha> ?dw!i')[j' := x] ] = 
      flat_\<alpha> (?dw [k - length ?tw - 1 := x])"
      apply (rule sym)
      apply (rule "1.IH")
      apply (simp_all)
      subgoal using A by simp
      subgoal using flat_idx_inv_pres_aux[OF INV A] by simp
      subgoal using FI' by simp
      done
    finally have "flat_\<alpha> l[i := (flat_\<alpha> l ! i)[j := x]] =
      ?tw # flat_\<alpha> (?dw[k - length ?tw - 1 := x])" .
    also have "\<dots> = flat_\<alpha> (l[k := x])"  
      apply (rewrite at "_ = \<hole>" flat_\<alpha>.simps)
      using takeWhile_upd_right[OF LL']
      using LL
      by (simp add: dropWhile_upd_right)
    finally have ?case by simp
  } ultimately show ?case using not_le by blast
qed  
  

lemma flat_idx_append_pres_invar:
  assumes "flat_idx_invar l k"
  shows "flat_idx_invar (l@ll) k"
  using assms unfolding flat_idx_invar_def by auto

lemma length_takeWhile_append: "length (takeWhile P l) \<le> length (takeWhile P (l@ll))"
  by (induction l) auto

lemma takeWhile_append_last: "\<lbrakk>l\<noteq>[]; \<not>P (last l)\<rbrakk> \<Longrightarrow> takeWhile P (l@ll) = takeWhile P l"
  apply (rule takeWhile_append1[where x="last l"])
  apply auto
  done

lemma dropWhile_append_last: "\<lbrakk>l\<noteq>[]; \<not>P (last l)\<rbrakk> \<Longrightarrow> dropWhile P (l@ll) = dropWhile P l@ll"
  apply (rule dropWhile_append1[where x="last l"])
  by auto





lemma flat_\<alpha>_split_conv[simp]:
  assumes "0\<notin>set l1"
  shows "flat_\<alpha> (l1@0#l2) = l1#flat_\<alpha> l2"
  apply (rewrite at "\<hole>=_" flat_\<alpha>.simps)
  using assms
  by (auto simp: takeWhile_tail dropWhile_append3)

lemma flat_idx_invar_split_conv: 
  assumes "0\<notin>set l1"
  shows "flat_idx_invar (l1@0#l2) k \<longleftrightarrow> (k<length l1 \<or> k>length l1 \<and> flat_idx_invar l2 (k-length l1 - 1))"
  using assms
  unfolding flat_idx_invar_def
  apply (auto simp: nth_append nth_Cons in_set_conv_nth split: nat.splits)
  apply (metis diff_Suc_1 diff_Suc_eq_diff_pred diff_commute)+
  done


lemma flat_idx_\<alpha>_split1_conv[simp]:
  assumes "k<length l1" "0\<notin>set l1"
  shows "flat_idx_\<alpha> (l1@0#l2) k = (0,k)"
  using assms
  apply (subst flat_idx_\<alpha>.simps)
  by (auto simp: Let_def takeWhile_append3 split: prod.split)

lemma flat_idx_\<alpha>_split2_conv[simp]:
  assumes "k>length l1" "0\<notin>set l1"
  shows "flat_idx_\<alpha> (l1@0#l2) k = apfst Suc (flat_idx_\<alpha> l2 (k - length l1 - 1))"  
  using assms
  apply (subst flat_idx_\<alpha>.simps)
  by (auto simp add: Let_def takeWhile_append3 dropWhile_append3 split: prod.split)
  


lemma flat_idx_append_pres_\<alpha>:
  assumes "flat_\<alpha>_invar l"
  assumes INV: "flat_idx_invar l k"
  shows "flat_idx_\<alpha> (l@ll) k = flat_idx_\<alpha> l k"
  using assms
  apply (induction arbitrary: k rule: flat_\<alpha>_induct)
  apply (auto simp: flat_idx_invar_split_conv)
  done

lemma flat_\<alpha>_empty[simp]: "flat_\<alpha> [] = []"
  apply (subst flat_\<alpha>.simps) by simp

lemma flat_\<alpha>_append: 
  assumes "flat_\<alpha>_invar l" "flat_\<alpha>_invar ll"
  shows "flat_\<alpha> (l@ll) = flat_\<alpha> l @ flat_\<alpha> ll"
  using assms
  by (induction rule: flat_\<alpha>_induct) auto

lemma flat_\<alpha>_append_invar: 
  assumes "flat_\<alpha>_invar l" "flat_\<alpha>_invar ll"
  shows "flat_\<alpha>_invar (l@ll)"
  using assms 
  by (auto simp: flat_\<alpha>_invar_def last_append)

*)


end
