(*
  File:         PAC_Checker_Synthesis.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory EPAC_Checker_Synthesis
  imports EPAC_Checker EPAC_Version
    EPAC_Checker_Init
    PAC_Checker.More_Loops
    PAC_Checker.WB_Sort PAC_Checker.PAC_Checker_Relation
    PAC_Checker.PAC_Checker_Synthesis
begin
hide_fact (open) PAC_Checker.PAC_checker_l_def
hide_const (open) PAC_Checker.PAC_checker_l

section \<open>Code Synthesis of the Complete Checker\<close>

definition check_linear_combi_l_pre_err_impl :: \<open>uint64 \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> string\<close> where
  \<open>check_linear_combi_l_pre_err_impl i adom emptyl ivars =
  ''Precondition for '%' failed '' @ show (nat_of_uint64 i) @
  ''(already in domain: '' @ show adom @
  ''; empty CL'' @ show emptyl @
  ''; new vars: '' @ show ivars @ '')''\<close>

abbreviation comp4 (infixl "oooo" 55) where "f oooo g \<equiv> \<lambda>x. f ooo (g x)"

lemma [sepref_fr_rules]:
  \<open>(uncurry3 (return oooo check_linear_combi_l_pre_err_impl),
   uncurry3 check_linear_combi_l_pre_err) \<in> uint64_nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding list_assn_pure_conv check_linear_combi_l_pre_err_impl_def
    check_linear_combi_l_pre_err_def 
  apply sepref_to_hoare
  apply sep_auto
  done

definition check_linear_combi_l_dom_err_impl :: \<open> _ \<Rightarrow> uint64 \<Rightarrow> string\<close> where
  \<open>check_linear_combi_l_dom_err_impl xs i =
  ''Invalid polynomial '' @ show (nat_of_uint64 i)\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry (return oo (check_linear_combi_l_dom_err_impl)),
  uncurry (check_linear_combi_l_dom_err)) \<in> poly_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding list_assn_pure_conv check_linear_combi_l_dom_err_impl_def
    check_linear_combi_l_dom_err_def
  apply sepref_to_hoare
  apply sep_auto
  done

definition check_linear_combi_l_mult_err_impl :: \<open> _ \<Rightarrow> _ \<Rightarrow> string\<close> where
  \<open>check_linear_combi_l_mult_err_impl xs ys =
  ''Invalid calculation, found'' @ show xs @ '' instead of '' @ show ys\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry (return oo check_linear_combi_l_mult_err_impl),
  uncurry check_linear_combi_l_mult_err) \<in> poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding list_assn_pure_conv check_linear_combi_l_mult_err_impl_def
    check_linear_combi_l_mult_err_def
  apply sepref_to_hoare
  apply sep_auto
  done

sepref_definition linear_combi_l_impl
  is \<open>uncurry3 linear_combi_l\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a (list_assn (poly_assn \<times>\<^sub>a uint64_nat_assn))\<^sup>k  \<rightarrow>\<^sub>a
  poly_assn \<times>\<^sub>a (list_assn (poly_assn \<times>\<^sub>a uint64_nat_assn)) \<times>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding linear_combi_l_def  check_linear_combi_l_def conv_to_is_Nil
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    vars_llist_alt_def is_Nil_def
  unfolding
    HOL_list.fold_custom_empty
  apply (rewrite in \<open>(op_HOL_list_empty, _)\<close> annotate_assn[where A=\<open>poly_assn\<close>])
  by sepref

declare linear_combi_l_impl.refine[sepref_fr_rules]
  sepref_register check_linear_combi_l_pre_err
sepref_definition check_linear_combi_l_impl
  is \<open>uncurry5 check_linear_combi_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a
        (list_assn (poly_assn \<times>\<^sub>a uint64_nat_assn))\<^sup>k *\<^sub>a poly_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_mult_l_def  check_linear_combi_l_def conv_to_is_Nil
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    vars_llist_alt_def is_Nil_def
   by sepref

declare check_linear_combi_l_impl.refine[sepref_fr_rules]



(* lemma pac_step_rel_assn_alt_def2:
 *   \<open>hn_ctxt (pac_step_rel_assn nat_assn poly_assn id_assn) b bi =
 *        hn_val
 *         (p2rel
 *           (\<langle>nat_rel, poly_rel, Id :: (string \<times> _) set\<rangle>pac_step_rel_raw)) b bi\<close>
 *   unfolding poly_assn_list hn_ctxt_def
 *   by (induction nat_assn poly_assn \<open>id_assn :: string \<Rightarrow> _\<close> b bi rule: pac_step_rel_assn.induct)
 *    (auto simp: p2rel_def hn_val_unfold pac_step_rel_raw.simps relAPP_def
 *     pure_app_eq) *)

sepref_register is_cfailed is_Del

definition PAC_checker_l_step' ::  _ where
  \<open>PAC_checker_l_step' a b c d = PAC_checker_l_step a (b, c, d)\<close>

lemma PAC_checker_l_step_alt_def:
  \<open>PAC_checker_l_step a bcd e = (let (b,c,d) = bcd in PAC_checker_l_step' a b c d e)\<close>
  unfolding PAC_checker_l_step'_def by auto

sepref_decl_intf ('k) acode_status is "('k) code_status"
sepref_decl_intf ('k, 'b, 'lbl) apac_step is "('k, 'b, 'lbl) pac_step"

sepref_register merge_cstatus full_normalize_poly new_var is_Add



lemma is_CL_import[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure K\<close>  \<open>CONSTRAINT is_pure V\<close> \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(return o pac_res, RETURN o pac_res) \<in> [\<lambda>x. is_Extension x \<or> is_CL x]\<^sub>a
       (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> V\<close>
    \<open>(return o pac_src1, RETURN o pac_src1) \<in> [\<lambda>x. is_Del x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> K\<close>
    \<open>(return o new_id, RETURN o new_id) \<in> [\<lambda>x. is_Extension x \<or> is_CL x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> K\<close>
    \<open>(return o is_CL, RETURN o is_CL) \<in>  (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    \<open>(return o is_Del, RETURN o is_Del) \<in> (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    \<open>(return o new_var, RETURN o new_var) \<in> [\<lambda>x. is_Extension x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> R\<close>
    \<open>(return o is_Extension, RETURN o is_Extension) \<in> (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using assms
  by (sepref_to_hoare; sep_auto simp: pac_step_rel_assn_alt_def is_pure_conv ent_true_drop pure_app_eq
    split: pac_step.splits; fail)+


lemma is_CL_import2[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure K\<close>  \<open>CONSTRAINT is_pure V\<close>
  shows
    \<open>(return o pac_srcs, RETURN o pac_srcs) \<in> [\<lambda>x. is_CL x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>  list_assn (V \<times>\<^sub>a K)\<close>
  using assms
  by (sepref_to_hoare; sep_auto simp: pac_step_rel_assn_alt_def is_pure_conv ent_true_drop pure_app_eq
    assms[simplified] list_assn_pure_conv
    split: pac_step.splits)

lemma is_Mult_lastI:
  \<open>\<not> is_CL b \<Longrightarrow> \<not>is_Extension b \<Longrightarrow> is_Del b\<close>
  by (cases b) auto

sepref_register check_linear_combi_l
sepref_definition check_step_impl
  is \<open>uncurry4 PAC_checker_l_step'\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a (pac_step_rel_assn (uint64_nat_assn) poly_assn (string_assn :: string \<Rightarrow> _))\<^sup>d \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro] single_valued_uint64_nat_rel[simp]
  unfolding PAC_checker_l_step_def PAC_checker_l_step'_def
    pac_step.case_eq_if Let_def
     is_success_alt_def[symmetric]
    uminus_poly_def[symmetric]
    HOL_list.fold_custom_empty
  by sepref


declare check_step_impl.refine[sepref_fr_rules]

sepref_register PAC_checker_l_step PAC_checker_l_step' fully_normalize_poly_impl

definition PAC_checker_l' where
  \<open>PAC_checker_l' p \<V> A status steps = PAC_checker_l p (\<V>, A) status steps\<close>

lemma PAC_checker_l_alt_def:
  \<open>PAC_checker_l p \<V>A status steps =
    (let (\<V>, A) = \<V>A in PAC_checker_l' p \<V> A status steps)\<close>
  unfolding PAC_checker_l'_def by auto


lemma step_rewrite_pure:
  fixes K :: \<open>('olbl \<times> 'lbl) set\<close>
  shows
    \<open>pure (p2rel (\<langle>K, V, R\<rangle>pac_step_rel_raw)) = pac_step_rel_assn (pure K) (pure V) (pure R)\<close>
  apply (intro ext)
  apply (case_tac x; case_tac xa)
  apply simp_all
  apply (simp_all add: relAPP_def p2rel_def pure_def)
  unfolding pure_def[symmetric] list_assn_pure_conv
  apply (auto simp: pure_def relAPP_def)
  done
find_theorems list_rel list_assn

lemma safe_epac_step_rel_assn[safe_constraint_rules]:
  \<open>CONSTRAINT is_pure K \<Longrightarrow> CONSTRAINT is_pure V \<Longrightarrow> CONSTRAINT is_pure R \<Longrightarrow>
  CONSTRAINT is_pure (EPAC_Checker.pac_step_rel_assn K V R)\<close>
  by (auto simp: step_rewrite_pure(1)[symmetric] is_pure_conv)

sepref_definition PAC_checker_l_impl
  is \<open>uncurry4 PAC_checker_l'\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a
       (list_assn (pac_step_rel_assn (uint64_nat_assn) poly_assn string_assn))\<^sup>k \<rightarrow>\<^sub>a
     status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_def is_success_alt_def[symmetric] PAC_checker_l_step_alt_def
    nres_bind_let_law[symmetric] PAC_checker_l'_def
    conv_to_is_Nil is_Nil_def
  apply (subst nres_bind_let_law)
  by sepref

declare PAC_checker_l_impl.refine[sepref_fr_rules]

abbreviation polys_assn_input where
  \<open>polys_assn_input \<equiv> iam_fmap_assn nat_assn poly_assn\<close>

definition remap_polys_l_dom_err_impl :: \<open>_\<close>  where
  \<open>remap_polys_l_dom_err_impl =
    ''Error during initialisation. Too many polynomials where provided. If this happens,'' @
    ''please report the example to the authors, because something went wrong during '' @
    ''code generation (code generation to arrays is likely to be broken).''\<close>

lemma [sepref_fr_rules]:
  \<open>((uncurry0 (return (remap_polys_l_dom_err_impl))),
    uncurry0 (remap_polys_l_dom_err)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding remap_polys_l_dom_err_def
     remap_polys_l_dom_err_def
     list_assn_pure_conv
   by sepref_to_hoare sep_auto

text \<open>MLton is not able to optimise the calls to pow.\<close>
lemma pow_2_64: \<open>(2::nat) ^ 64 = 18446744073709551616\<close>
  by auto

sepref_register upper_bound_on_dom op_fmap_empty

sepref_register remap_polys_l

sepref_definition full_checker_l_impl
  is \<open>uncurry2 full_checker_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>d *\<^sub>a (list_assn (pac_step_rel_assn (uint64_nat_assn) poly_assn string_assn))\<^sup>k \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding full_checker_l_def hs.fold_custom_empty
    union_vars_poly_alt_def[symmetric]
    PAC_checker_l_alt_def
  by sepref

sepref_definition PAC_empty_impl
  is \<open>uncurry0 (RETURN fmempty)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a polys_assn_input\<close>
  unfolding op_iam_fmap_empty_def[symmetric] pat_fmap_empty
  by sepref

sepref_definition empty_vars_impl
  is \<open>uncurry0 (RETURN {})\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding hs.fold_custom_empty
  by sepref

text \<open>This is a hack for performance. There is no need to recheck that that a char is valid when
  working on chars coming from strings... It is not that important in most cases, but in our case
  the preformance difference is really large.\<close>


definition unsafe_asciis_of_literal :: \<open>_\<close> where
  \<open>unsafe_asciis_of_literal xs = String.asciis_of_literal xs\<close>

definition unsafe_asciis_of_literal' :: \<open>_\<close> where
  [simp, symmetric, code]: \<open>unsafe_asciis_of_literal' = unsafe_asciis_of_literal\<close>

code_printing
  constant unsafe_asciis_of_literal' \<rightharpoonup>
    (SML) "!(List.map (fn c => let val k = Char.ord c in IntInf.fromInt k end) /o String.explode)"

text \<open>
  Now comes the big and ugly and unsafe hack.

  Basically, we try to avoid the conversion to IntInf when calculating the hash. The performance
  gain is roughly 40\%, which is a LOT and definitively something we need to do. We are aware that the
  SML semantic encourages compilers to optimise conversions, but this does not happen here,
  corroborating our early observation on the verified SAT solver IsaSAT.x
\<close>
definition raw_explode where
  [simp]: \<open>raw_explode = String.explode\<close>
code_printing
  constant raw_explode \<rightharpoonup>
    (SML) "String.explode"

lemmas [code] =
  hashcode_literal_def[unfolded String.explode_code
    unsafe_asciis_of_literal_def[symmetric]]

definition uint32_of_char where
  [symmetric, code_unfold]: \<open>uint32_of_char x = uint32_of_int (int_of_char x)\<close>


code_printing
  constant uint32_of_char \<rightharpoonup>
    (SML) "!(Word32.fromInt /o (Char.ord))"

lemma [code]: \<open>hashcode s = hashcode_literal' s\<close>
  unfolding hashcode_literal_def hashcode_list_def
  apply (auto simp: unsafe_asciis_of_literal_def hashcode_list_def
     String.asciis_of_literal_def hashcode_literal_def hashcode_literal'_def)
  done

text \<open>We compile Pastèque in \<^file>\<open>EPAC_Checker_MLton.thy\<close>.\<close>
export_code PAC_checker_l_impl PAC_update_impl PAC_empty_impl the_error is_cfailed is_cfound
  int_of_integer Del Add Mult nat_of_integer String.implode remap_polys_l_impl
  fully_normalize_poly_impl union_vars_poly_impl empty_vars_impl
  full_checker_l_impl check_step_impl CSUCCESS
  Extension hashcode_literal' version
  in SML_imp module_name PAC_Checker


section \<open>Correctness theorem\<close>

context poly_embed
begin

definition fully_epac_assn where
  \<open>fully_epac_assn = (list_assn
        (hr_comp (pac_step_rel_assn uint64_nat_assn poly_assn string_assn)
          (p2rel
            (\<langle>nat_rel,
             fully_unsorted_poly_rel O
             mset_poly_rel, var_rel\<rangle>pac_step_rel_raw))))\<close>


text \<open>

Below is the full correctness theorems. It basically states that:

  \<^enum> assuming that the input polynomials have no duplicate variables


Then:

\<^enum> if the checker returns \<^term>\<open>CFOUND\<close>, the spec is in the ideal
  and the PAC file is correct

\<^enum> if the checker returns \<^term>\<open>CSUCCESS\<close>, the PAC file is correct (but
there is no information on the spec, aka checking failed)

\<^enum> if the checker return \<^term>\<open>CFAILED err\<close>, then checking failed (and
\<^term>\<open>err\<close> \<^emph>\<open>might\<close> give you an indication of the error, but the correctness
theorem does not say anything about that).


The input parameters are:

\<^enum> the specification polynomial represented as a list

\<^enum> the input polynomials as hash map (as an array of option polynomial)

\<^enum> a represention of the PAC proofs.

\<close>

lemma PAC_full_correctness: (* \htmllink{PAC-full-correctness} *)
  \<open>(uncurry2 full_checker_l_impl,
     uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
    \<in> (full_poly_assn)\<^sup>k *\<^sub>a (full_poly_input_assn)\<^sup>d *\<^sub>a (fully_epac_assn)\<^sup>k \<rightarrow>\<^sub>a hr_comp
      (code_status_assn \<times>\<^sub>a full_vars_assn \<times>\<^sub>a hr_comp polys_assn
                              (\<langle>nat_rel, sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
                            {((st, G), st', G').
                             st = st' \<and> (st \<noteq> FAILED \<longrightarrow> (G, G') \<in> Id \<times>\<^sub>r polys_rel)}\<close>
  using
    full_checker_l_impl.refine[FCOMP full_checker_l_full_checker',
      FCOMP full_checker_spec',
      unfolded full_poly_assn_def[symmetric]
        full_poly_input_assn_def[symmetric]
        fully_epac_assn_def[symmetric]
        code_status_assn_def[symmetric]
        full_vars_assn_def[symmetric]
        polys_rel_full_polys_rel
        hr_comp_prod_conv
        full_polys_assn_def[symmetric]]
      hr_comp_Id2
   by auto

text \<open>

It would be more efficient to move the parsing to Isabelle, as this
would be more memory efficient (and also reduce the TCB). But now
comes the fun part: It cannot work. A stream (of a file) is consumed
by side effects. Assume that this would work. The code could look like:

\<^term>\<open>
  let next_token = read_file file
  in f (next_token)
\<close>

This code is equal to (in the HOL sense of equality):
\<^term>\<open>
  let _ = read_file file;
      next_token = read_file file
  in f (next_token)
\<close>

However, as an hypothetical \<^term>\<open>read_file\<close> changes the underlying stream, we would get the next
token. Remark that this is already a weird point of ML compilers. Anyway, I see currently two
solutions to this problem:

\<^enum> The meta-argument: use it only in the Refinement Framework in a setup where copies are
disallowed. Basically, this works because we can express the non-duplication constraints on the type
level. However, we cannot forbid people from expressing things directly at the HOL level.

\<^enum> On the target language side, model the stream as the stream and the position. Reading takes two
arguments. First, the position to read. Second, the stream (and the current position) to read. If
the position to read does not match the current position, return an error. This would fit the
correctness theorem of the code generation (roughly ``if it terminates without exception, the answer
is the same''), but it is still unsatisfactory.
\<close>

end

end
