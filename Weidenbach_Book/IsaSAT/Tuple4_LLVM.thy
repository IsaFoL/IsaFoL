theory Tuple4_LLVM
  imports Tuple4 IsaSAT_Literals_LLVM
begin

hide_const (open) NEMonad.ASSERT NEMonad.RETURN

text \<open>
This is the setup for accessing and modifying the state as an abstract tuple of 15 elements.
 The construction is kept generic 
(even if still targetting only our state). There is a lot of copy-paste that would be nice to automate
at some point.


We define 3 sort of operations:

  \<^enum> extracting an element, replacing it by an default element. Modifies the state. The name starts 
with \<^text>\<open>exctr\<close>

  \<^enum> reinserting an element, freeing the current one. Modifies the state. The name starts with
 \<^text>\<open>update\<close>

  \<^enum> in-place reading a value, possibly with pure parameters. Does not modify the state. The name
starts with \<^text>\<open>read\<close>

\<close>

instantiation tuple4 ::
  (llvm_rep,llvm_rep,llvm_rep,llvm_rep) llvm_rep
begin
  definition to_val_tuple4 where
    \<open>to_val_tuple4 \<equiv> (\<lambda>S. case S of
     Tuple4 M N D i  \<Rightarrow> LL_STRUCT [to_val M, to_val N, to_val D, to_val i])\<close>

  definition from_val_tuple4 :: \<open>llvm_val \<Rightarrow> ('a, 'b, 'c, 'd) tuple4\<close> where
    \<open>from_val_tuple4 \<equiv> (\<lambda>p. case llvm_val.the_fields p of
   [M, N, D, i] \<Rightarrow>
     Tuple4 (from_val M) (from_val N) (from_val D) (from_val i))\<close>

  definition [simp]: "struct_of_tuple4 (_ :: ('a, 'b, 'c, 'd) tuple4 itself) \<equiv>
     VS_STRUCT [struct_of TYPE('a), struct_of TYPE('b), struct_of TYPE('c),
      struct_of TYPE('d)]"

  definition [simp]: "init_tuple4 :: ('a, 'b, 'c, 'd) tuple4 \<equiv> Tuple4 init init init init"

  instance
    apply standard
    unfolding from_val_tuple4_def to_val_tuple4_def struct_of_tuple4_def init_tuple4_def comp_def tuple4.case_distrib
    subgoal
      by (auto simp: init_zero fun_eq_iff from_val_tuple4_def split: tuple4.splits)
    subgoal for v
      by (cases v) (auto split: list.splits tuple4.splits)
    subgoal for v
      by (cases v)
       (simp add: LLVM_Shallow.null_def to_val_ptr_def split: tuple4.splits)
    subgoal
      by (simp add: LLVM_Shallow.null_def to_val_ptr_def to_val_word_def init_zero split: tuple4.splits)
    done
end

subsubsection \<open>Setup for LLVM code export\<close>
text \<open>Declare structure to code generator.\<close>
lemma to_val_tuple17[ll_struct_of]: "struct_of TYPE(('a, 'b, 'c, 'd) tuple4) = VS_STRUCT [
  struct_of TYPE('a::llvm_rep),
  struct_of TYPE('b::llvm_rep),
  struct_of TYPE('c::llvm_rep),
  struct_of TYPE('d::llvm_rep)]"
  by (auto)

lemma node_insert_value:
  "ll_insert_value (Tuple4 M N D i) M' 0 = Mreturn (Tuple4 M' N D i)"
  "ll_insert_value (Tuple4 M N D i) N' (Suc 0) = Mreturn (Tuple4 M N' D i)"
  "ll_insert_value (Tuple4 M N D i) D' 2 = Mreturn (Tuple4 M N D' i)"
  "ll_insert_value (Tuple4 M N D i) i' 3 = Mreturn (Tuple4 M N D i')"
  by (simp_all add: ll_insert_value_def llvm_insert_value_def Let_def checked_from_val_def
                to_val_tuple4_def from_val_tuple4_def)

lemma node_extract_value:
  "ll_extract_value (Tuple4 M N D i) 0 = Mreturn M"
  "ll_extract_value (Tuple4 M N D i) (Suc 0) = Mreturn N"
  "ll_extract_value (Tuple4 M N D i) 2 = Mreturn D"
  "ll_extract_value (Tuple4 M N D i) 3 = Mreturn i"
  apply (simp_all add: ll_extract_value_def llvm_extract_value_def Let_def checked_from_val_def
                to_val_tuple4_def from_val_tuple4_def)
  done

text \<open>Lemmas to translate node construction and destruction\<close>
lemma inline_return_node[llvm_pre_simp]: "Mreturn (Tuple4 M N D i) = doM {
    r \<leftarrow> ll_insert_value init M 0;
    r \<leftarrow> ll_insert_value r N 1;
    r \<leftarrow> ll_insert_value r D 2;
    r \<leftarrow> ll_insert_value r i 3;
    Mreturn r
  }"
  apply (auto simp: node_insert_value)
  done

lemma inline_node_case[llvm_pre_simp]: "(case r of (Tuple4 M N D i) \<Rightarrow> f M N D i) = doM {
    M \<leftarrow> ll_extract_value r 0;
    N \<leftarrow> ll_extract_value r 1;
    D \<leftarrow> ll_extract_value r 2;
    i \<leftarrow> ll_extract_value r 3;
  f M N D i
}"
  apply (cases r)
  apply (auto simp: node_extract_value)
  done

lemma inline_return_node_case[llvm_pre_simp]: "doM {Mreturn (case r of (Tuple4 M N D i) \<Rightarrow> f M N D i)} = doM {
    M \<leftarrow> ll_extract_value r 0;
    N \<leftarrow> ll_extract_value r 1;
    D \<leftarrow> ll_extract_value r 2;
    i \<leftarrow> ll_extract_value r 3;
  Mreturn (f M N D i)
}"
  apply (cases r)
  apply (auto simp: node_extract_value)
  done
lemma inline_direct_return_node_case[llvm_pre_simp]: "doM {(case r of (Tuple4 M N D i) \<Rightarrow> f M N D i)} = doM {
    M \<leftarrow> ll_extract_value r 0;
    N \<leftarrow> ll_extract_value r 1;
    D \<leftarrow> ll_extract_value r 2;
    i \<leftarrow> ll_extract_value r 3;
   (f M N D i)
}"
  apply (cases r)
  apply (auto simp: node_extract_value)
  done

lemmas [llvm_inline] =
  tuple4.Tuple4_a_def
  tuple4.Tuple4_b_def
  tuple4.Tuple4_c_def
  tuple4.Tuple4_d_def

fun tuple4_assn :: \<open>
  ('a \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('b \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('c \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('d \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('a, 'b, 'c, 'd) tuple4 \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>tuple4_assn a_assn b_assn' c_assn d_assn S T =
   (case (S, T) of
  (Tuple4 M N D i,
   Tuple4 M' N' D' i')
     \<Rightarrow>
 (a_assn M (M') \<and>* b_assn' N (N') \<and>* c_assn D (D')  \<and>* d_assn i (i')))
  \<close>

locale tuple4_state_ops =
  fixes
    a_assn :: \<open>'a \<Rightarrow> 'xa \<Rightarrow> assn\<close> and
    b_assn :: \<open>'b \<Rightarrow> 'xb \<Rightarrow> assn\<close> and
    c_assn :: \<open>'c \<Rightarrow> 'xc \<Rightarrow> assn\<close> and
    d_assn :: \<open>'d \<Rightarrow> 'xd \<Rightarrow> assn\<close> and
    a_default :: 'a and
    a :: \<open>'xa llM\<close> and
    b_default :: 'b and
    b :: \<open>'xb llM\<close> and
    c_default :: 'c and
    c :: \<open>'xc llM\<close> and
    d_default :: 'd and
    d :: \<open>'xd llM\<close>
begin

definition tuple4_int_assn :: \<open>_ \<Rightarrow> _ \<Rightarrow> assn\<close> where
\<open>tuple4_int_assn = tuple4_assn
  a_assn b_assn c_assn d_assn\<close>

definition remove_a :: \<open>('a, 'b, 'c, 'd) tuple4 \<Rightarrow> 'a \<times> ('a, 'b, 'c, 'd) tuple4\<close> where
  \<open>remove_a tuple4 = (case tuple4 of Tuple4 x1 x2 x3 x4 \<Rightarrow>
      (x1, Tuple4 a_default x2 x3 x4))\<close>

definition remove_b :: \<open>('a, 'b, 'c, 'd) tuple4 \<Rightarrow> 'b \<times> ('a, 'b, 'c, 'd) tuple4\<close> where
  \<open>remove_b tuple4 = (case tuple4 of Tuple4 x1 x2 x3 x4 \<Rightarrow>
      (x2, Tuple4 x1 b_default x3 x4))\<close>

definition remove_c :: \<open>('a, 'b, 'c, 'd) tuple4 \<Rightarrow> _ \<times> ('a, 'b, 'c, 'd) tuple4\<close> where
  \<open>remove_c tuple4 = (case tuple4 of Tuple4 x1 x2 x3 x4 \<Rightarrow>
      (x3, Tuple4 x1 x2 c_default x4))\<close>

definition remove_d :: \<open>('a, 'b, 'c, 'd) tuple4 \<Rightarrow> _ \<times> ('a, 'b, 'c, 'd) tuple4\<close> where
  \<open>remove_d tuple4 = (case tuple4 of Tuple4 x1 x2 x3 x4 \<Rightarrow>
      (x4, Tuple4 x1 x2 x3 d_default))\<close>

definition update_a :: \<open>'a \<Rightarrow> ('a, 'b, 'c, 'd) tuple4 \<Rightarrow> ('a, 'b, 'c, 'd) tuple4\<close> where
  \<open>update_a x1 tuple4 = (case tuple4 of Tuple4 M x2 x3 x4 \<Rightarrow>
    let _ = M in
    Tuple4 x1 x2 x3 x4)\<close>

definition update_b :: \<open>'b \<Rightarrow> ('a, 'b, 'c, 'd) tuple4 \<Rightarrow> ('a, 'b, 'c, 'd) tuple4\<close> where
  \<open>update_b x2 tuple4 = (case tuple4 of Tuple4 x1 M x3 x4 \<Rightarrow>
    let _ = M in
    Tuple4 x1 x2 x3 x4)\<close>

definition update_c :: \<open>'c \<Rightarrow> ('a, 'b, 'c, 'd) tuple4 \<Rightarrow> ('a, 'b, 'c, 'd) tuple4\<close> where
  \<open>update_c x3 tuple4 = (case tuple4 of Tuple4 x1 x2 M x4 \<Rightarrow>
    let _ = M in
    Tuple4 x1 x2 x3 x4)\<close>

definition update_d :: \<open>'d \<Rightarrow> ('a, 'b, 'c, 'd) tuple4 \<Rightarrow> ('a, 'b, 'c, 'd) tuple4\<close> where
  \<open>update_d x4 tuple4 = (case tuple4 of Tuple4 x1 x2 x3 M \<Rightarrow>
    let _ = M in
    Tuple4 x1 x2 x3 x4)\<close>

end
 
lemma tuple4_assn_conv[simp]: 
  "tuple4_assn P1 P2 P3 P4 (Tuple4 a1 a2 a3 a4)
  (Tuple4 a1' a2' a3' a4') =
  (P1 a1 a1' \<and>*
  P2 a2 a2' \<and>*
  P3 a3 a3' \<and>*
  P4 a4 a4')"
  unfolding tuple4_assn.simps by auto

lemma tuple4_assn_ctxt:
  \<open>tuple4_assn P1 P2 P3 P4 (Tuple4 a1 a2 a3 a4)
  (Tuple4 a1' a2' a3' a4') = z \<Longrightarrow>
  hn_ctxt (tuple4_assn P1 P2 P3 P4) (Tuple4 a1 a2 a3 a4)
  (Tuple4 a1' a2' a3' a4')= z\<close>
  by (simp add: hn_ctxt_def)

lemma hn_case_tuple4'[sepref_comb_rules]:
  assumes FR: \<open>\<Gamma> \<turnstile> hn_ctxt (tuple4_assn P1 P2 P3 P4) p' p ** \<Gamma>1\<close>
  assumes Pair: "\<And>a1 a2 a3 a4 a1' a2' a3' a4'.
        \<lbrakk>p'=Tuple4 a1' a2' a3' a4'\<rbrakk>
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 \<and>* hn_ctxt P2 a2' a2 \<and>* hn_ctxt P3 a3' a3 \<and>* hn_ctxt P4 a4' a4 \<and>* \<Gamma>1)
          (f a1 a2 a3 a4 )
          (\<Gamma>2 a1 a2 a3 a4 a1' a2' a3' a4') R
          (CP a1 a2  a3 a4 )
         (f' a1' a2' a3' a4')"
  assumes FR2: \<open>\<And>a1 a2 a3 a4  a1' a2' a3' a4'.
       \<Gamma>2 a1 a2 a3 a4  a1' a2' a3' a4' \<turnstile>
       hn_ctxt P1' a1' a1 ** hn_ctxt P2' a2' a2 ** hn_ctxt P3' a3' a3 ** hn_ctxt P4' a4' a4 ** \<Gamma>1'\<close>
  shows \<open>hn_refine \<Gamma> (case_tuple4 f p) (hn_ctxt (tuple4_assn P1' P2' P3' P4') p' p ** \<Gamma>1')
    R (case_tuple4 CP p) (case_tuple4$(\<lambda>\<^sub>2a1 a2 a3 a4 . f' a1 a2 a3 a4 )$p')\<close> (is \<open>?G \<Gamma>\<close>)
  unfolding autoref_tag_defs PROTECT2_def
  apply1 (rule hn_refine_cons_pre[OF FR])
    apply1 (cases p; cases p'; simp add: tuple4_assn_conv[THEN tuple4_assn_ctxt])
  unfolding CP_SPLIT_def prod.simps
  apply (rule hn_refine_cons[OF _ Pair _ entails_refl])
  applyS (simp add: hn_ctxt_def)
  applyS simp using FR2
  by (simp add: hn_ctxt_def)


lemma case_tuple4_arity[sepref_monadify_arity]:
  \<open>case_tuple4 \<equiv> \<lambda>\<^sub>2fp p. SP case_tuple4$(\<lambda>\<^sub>2a b. fp$a$b)$p\<close>
  by (simp_all only: SP_def APP_def PROTECT2_def RCALL_def)

lemma case_tuple4_comb[sepref_monadify_comb]:
  \<open>\<And>fp p. case_tuple4$fp$p \<equiv> Refine_Basic.bind$(EVAL$p)$(\<lambda>\<^sub>2p. (SP case_tuple4$fp$p))\<close>
  by (simp_all)

lemma case_tuple4_plain_comb[sepref_monadify_comb]:
  "EVAL$(case_tuple4$(\<lambda>\<^sub>2a1 a2 a3 a4 . fp a1 a2 a3 a4 )$p) \<equiv>
    Refine_Basic.bind$(EVAL$p)$(\<lambda>\<^sub>2p. case_tuple4$(\<lambda>\<^sub>2a1 a2 a3 a4 . EVAL$(fp a1 a2 a3 a4 ))$p)"
  apply (rule eq_reflection, simp split: list.split prod.split option.split tuple4.split)+
  done

lemma ho_tuple4_move[sepref_preproc]: \<open>case_tuple4 (\<lambda>a1 a2 a3 a4  x. f x a1 a2 a3 a4 ) =
  (\<lambda>p x. case_tuple4 (f x) p)\<close>
  by (auto split: tuple4.splits)

locale tuple4_state =
  tuple4_state_ops a_assn b_assn c_assn d_assn
  a_default a
  b_default b
  c_default c
  d_default d
  for
    a_assn :: \<open>'a \<Rightarrow> 'xa \<Rightarrow> assn\<close> and
    b_assn :: \<open>'b \<Rightarrow> 'xb \<Rightarrow> assn\<close> and
    c_assn :: \<open>'c \<Rightarrow> 'xc \<Rightarrow> assn\<close> and
    d_assn :: \<open>'d \<Rightarrow> 'xd \<Rightarrow> assn\<close> and
    a_default :: 'a and
    a :: \<open>'xa llM\<close> and
    b_default :: 'b and
    b :: \<open>'xb llM\<close> and
    c_default :: 'c and
    c :: \<open>'xc llM\<close> and
    d_default :: 'd and
    d :: \<open>'xd llM\<close> and
    a_free :: \<open>'xa \<Rightarrow> unit llM\<close> and
    b_free :: \<open>'xb \<Rightarrow> unit llM\<close> and
    c_free :: \<open>'xc \<Rightarrow> unit llM\<close> and
    d_free :: \<open>'xd \<Rightarrow> unit llM\<close> +
  assumes
    a: \<open>(uncurry0 a, uncurry0  (RETURN a_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a a_assn\<close> and
    b: \<open>(uncurry0 b, uncurry0  (RETURN b_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a b_assn\<close> and
    c: \<open>(uncurry0 c, uncurry0  (RETURN c_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a c_assn\<close> and
    d: \<open>(uncurry0 d, uncurry0  (RETURN d_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a d_assn\<close> and
    a_free: \<open>MK_FREE a_assn a_free\<close> and
    b_free: \<open>MK_FREE b_assn b_free\<close>and
    c_free: \<open>MK_FREE c_assn c_free\<close>and
    d_free: \<open>MK_FREE d_assn d_free\<close>
  notes [[sepref_register_adhoc a_default b_default c_default d_default]]
begin

lemmas [sepref_comb_rules] = hn_case_tuple4'[of _ a_assn b_assn c_assn d_assn,
  unfolded tuple4_int_assn_def[symmetric]]

lemma ex_tuple4_iff: "(\<exists>b :: (_,_,_,_)tuple4. P b) \<longleftrightarrow>
  (\<exists>a b  c d. P (Tuple4 a b  c d))"
  apply auto
    apply (case_tac b)
  by force

lemmas [sepref_frame_free_rules] = a_free b_free c_free d_free
sepref_register
  \<open>Tuple4\<close>
lemma [sepref_fr_rules]: \<open>(uncurry3 (Mreturn oooo Tuple4), uncurry3 (RETURN oooo Tuple4))
  \<in> a_assn\<^sup>d *\<^sub>a b_assn\<^sup>d *\<^sub>a c_assn\<^sup>d *\<^sub>a d_assn\<^sup>d
  \<rightarrow>\<^sub>a tuple4_int_assn\<close>
  unfolding tuple4_int_assn_def
  apply sepref_to_hoare
  apply vcg
  unfolding ex_tuple4_iff
  apply vcg'
  done

lemma [sepref_frame_match_rules]:
  \<open> hn_ctxt
     (tuple4_assn (invalid_assn a_assn) (invalid_assn b_assn) (invalid_assn c_assn) (invalid_assn d_assn)) ax bx \<turnstile> hn_val UNIV ax bx\<close>
    unfolding hn_ctxt_def invalid_assn_def tuple4_int_assn_def entails_def
    apply (auto split: prod.split tuple4.splits elim: is_pureE 
      simp: sep_algebra_simps pure_part_pure_conj_eq)
    apply (auto simp: pure_part_def)
      apply (auto simp: pure_def pure_true_conv)
    done

lemma RETURN_case_tuple4_inverse: \<open>RETURN
      (let _ = M
         in ff) =
      (do {_ \<leftarrow> mop_free M;
         RETURN (ff)})\<close>
    by (auto intro!: ext simp: mop_free_def split: tuple4.splits)

sepref_definition update_a_code
  is \<open>uncurry (RETURN oo update_a)\<close>
  :: \<open>a_assn\<^sup>d *\<^sub>a tuple4_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple4_int_assn\<close>
  supply [[goals_limit=5]]
  unfolding update_a_def tuple4.case_distrib comp_def RETURN_case_tuple4_inverse
  by sepref

sepref_definition update_b_code
  is \<open>uncurry (RETURN oo update_b)\<close>
  :: \<open>b_assn\<^sup>d *\<^sub>a tuple4_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple4_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_b_def tuple4.case_distrib comp_def RETURN_case_tuple4_inverse
  by sepref

sepref_definition update_c_code
  is \<open>uncurry (RETURN oo update_c)\<close>
  :: \<open>c_assn\<^sup>d *\<^sub>a tuple4_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple4_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_c_def tuple4.case_distrib comp_def RETURN_case_tuple4_inverse
  by sepref

sepref_definition update_d_code
  is \<open>uncurry (RETURN oo update_d)\<close>
  :: \<open>d_assn\<^sup>d *\<^sub>a tuple4_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple4_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_d_def tuple4.case_distrib comp_def RETURN_case_tuple4_inverse
  by sepref

lemma RETURN_case_tuple4_invers: \<open>(RETURN \<circ>\<circ> case_tuple4)
   (\<lambda>x1 x2 x3 x4.
  ff x1 x2 x3 x4) =
  case_tuple4
   (\<lambda>x1 x2 x3 x4.
  RETURN (ff x1 x2 x3 x4))\<close>
  by (auto intro!: ext split: tuple4.splits)

lemmas [sepref_fr_rules] = a b c d

sepref_definition remove_a_code
  is \<open>RETURN o remove_a\<close>
  :: \<open> tuple4_int_assn\<^sup>d \<rightarrow>\<^sub>a a_assn \<times>\<^sub>a tuple4_int_assn\<close>
  unfolding remove_a_def RETURN_case_tuple4_invers
  by sepref

sepref_definition remove_b_code
  is \<open>RETURN o remove_b\<close>
  :: \<open> tuple4_int_assn\<^sup>d \<rightarrow>\<^sub>a b_assn \<times>\<^sub>a tuple4_int_assn\<close>
  unfolding remove_b_def RETURN_case_tuple4_invers
  by sepref

sepref_definition remove_c_code
  is \<open>RETURN o remove_c\<close>
  :: \<open> tuple4_int_assn\<^sup>d \<rightarrow>\<^sub>a c_assn \<times>\<^sub>a tuple4_int_assn\<close>
  unfolding remove_c_def RETURN_case_tuple4_invers
  by sepref

sepref_definition remove_d_code
  is \<open>RETURN o remove_d\<close>
  :: \<open> tuple4_int_assn\<^sup>d \<rightarrow>\<^sub>a d_assn \<times>\<^sub>a tuple4_int_assn\<close>
  unfolding remove_d_def RETURN_case_tuple4_invers
  by sepref


lemmas separation_rules =
  remove_a_code.refine
  remove_b_code.refine
  remove_c_code.refine
  remove_d_code.refine

lemmas code_rules =
  remove_a_code_def
  remove_b_code_def
  remove_c_code_def
  remove_d_code_def

lemmas setter_and_getters_def =
   update_a_def remove_a_def
   update_b_def remove_b_def
   update_c_def remove_c_def
   update_d_def remove_d_def

end


context tuple4_state
begin
lemma reconstruct_isasat[sepref_frame_match_rules]:
  \<open>hn_ctxt
     (tuple4_assn (a_assn) (b_assn) (c_assn) (d_assn)) ax bx \<turnstile> hn_ctxt tuple4_int_assn ax bx\<close>
    unfolding tuple4_int_assn_def
    apply (auto split: prod.split tuple4.splits elim: is_pureE 
      simp: sep_algebra_simps pure_part_pure_conj_eq)
      done

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    read_all_code :: \<open>'xa \<Rightarrow> 'xb \<Rightarrow> 'xc \<Rightarrow> 'xd \<Rightarrow> 'q llM\<close> and
    read_all :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'r nres\<close>
begin

definition read_all_st_code :: \<open>_\<close> where
  \<open>read_all_st_code xi = (case xi of
  Tuple4 a1 a2 a3 a4  \<Rightarrow>
    read_all_code a1 a2 a3 a4 )\<close>

definition read_all_st :: \<open>('a, 'b, 'c, 'd) tuple4 \<Rightarrow> _\<close> where
  \<open>read_all_st tuple4 = (case tuple4 of Tuple4 a1 a2 a3 a4 \<Rightarrow>
  read_all a1 a2 a3 a4)\<close>

context
  fixes P
  assumes trail_read[sepref_fr_rules]: \<open>(uncurry3 read_all_code, uncurry3 read_all) \<in>
      [uncurry3 P]\<^sub>a a_assn\<^sup>k *\<^sub>a b_assn\<^sup>k *\<^sub>a c_assn\<^sup>k *\<^sub>a d_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc read_all]]
begin
sepref_definition read_all_st_code_tmp
  is read_all_st
  :: \<open>[case_tuple4 P]\<^sub>a tuple4_int_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_all_st_def
   by sepref

lemmas read_all_st_code_refine =
  read_all_st_code_tmp.refine[unfolded read_all_st_code_tmp_def
    read_all_st_code_def[symmetric]]
end

end

end

lemma Mreturn_comp_Tuple4:
  \<open>(Mreturn oooo Tuple4) a b c d =
  Mreturn (Tuple4 a b c d)\<close>
  by auto

lemma tuple4_free[sepref_frame_free_rules]:
  assumes
  \<open>MK_FREE A freea\<close> \<open>MK_FREE B freeb\<close> \<open>MK_FREE C freec\<close> \<open>MK_FREE D freed\<close>
  shows
  \<open>
  MK_FREE (tuple4_assn A B C D) (\<lambda>S. case S of Tuple4 a b c d \<Rightarrow> do\<^sub>M {
  freea a; freeb b; freec c; freed d
  })\<close>
  supply [vcg_rules] = assms[THEN MK_FREED]
  apply (rule)+
  apply (clarsimp split: tuple4.splits)
  by vcg'

end
