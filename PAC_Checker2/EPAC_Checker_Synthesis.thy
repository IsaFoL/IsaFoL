(*
  File:         PAC_Checker_Synthesis.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory EPAC_Checker_Synthesis
  imports EPAC_Checker EPAC_Version
    EPAC_Checker_Init
    EPAC_Steps_Refine
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

definition has_failed :: \<open>bool nres\<close> where
  \<open>has_failed = RES UNIV\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return False), uncurry0 has_failed)\<in>unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: has_failed_def)

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
    has_failed_def[symmetric]
   by sepref

declare check_linear_combi_l_impl.refine[sepref_fr_rules]

sepref_register is_cfailed is_Del

definition PAC_checker_l_step' ::  _ where
  \<open>PAC_checker_l_step' a b c d = PAC_checker_l_step a (b, c, d)\<close>

lemma PAC_checker_l_step_alt_def:
  \<open>PAC_checker_l_step a bcd e = (let (b,c,d) = bcd in PAC_checker_l_step' a b c d e)\<close>
  unfolding PAC_checker_l_step'_def by auto

sepref_decl_intf ('k) acode_status is "('k) code_status"
sepref_decl_intf ('k, 'b, 'lbl) apac_step is "('k, 'b, 'lbl) pac_step"

sepref_register merge_cstatus full_normalize_poly new_var is_Add
find_theorems is_CL RETURN

sepref_register check_linear_combi_l check_extension_l2
    term check_extension_l2

definition check_extension_l2_cond :: \<open>nat \<Rightarrow> _\<close> where
  \<open>check_extension_l2_cond i A \<V> v = SPEC (\<lambda>b. b \<longrightarrow> fmlookup' i A = None \<and> v \<notin> \<V>)\<close>

definition check_extension_l2_cond2 :: \<open>nat \<Rightarrow> _\<close> where
  \<open>check_extension_l2_cond2 i A \<V> v = RETURN (fmlookup' i A = None \<and> v \<notin> \<V>)\<close>


sepref_definition check_extension_l2_cond2_impl
  is \<open>uncurry3 check_extension_l2_cond2\<close>
    :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a string_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_extension_l2_cond2_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    not_not is_None_def
  by sepref

lemma check_extension_l2_cond2_check_extension_l2_cond:
  \<open>(uncurry3 check_extension_l2_cond2, uncurry3 check_extension_l2_cond) \<in>
  (((nat_rel \<times>\<^sub>r Id) \<times>\<^sub>r Id) \<times>\<^sub>r Id) \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (auto intro!: RES_refine nres_relI frefI
    simp: check_extension_l2_cond_def check_extension_l2_cond2_def)

lemmas [sepref_fr_rules] =
  check_extension_l2_cond2_impl.refine[FCOMP check_extension_l2_cond2_check_extension_l2_cond]


definition check_extension_l_side_cond_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_side_cond_err_impl v r s =
    ''Error while checking side conditions of extensions polynow, var is '' @ show v @
    ''side condition p*p - p = '' @ show s @ '' and should be 0''\<close>
term check_extension_l_side_cond_err
lemma [sepref_fr_rules]:
  \<open>(uncurry2 (return ooo (check_extension_l_side_cond_err_impl)),
    uncurry2 (check_extension_l_side_cond_err)) \<in> string_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_side_cond_err_impl_def check_extension_l_side_cond_err_def
     list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

definition check_extension_l_new_var_multiple_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_new_var_multiple_err_impl v p =
    ''Error while checking side conditions of extensions polynow, var is '' @ show v @
    '' but it either appears at least once in the polynomial or another new variable is created '' @
    show p @ '' but should not.''\<close>

lemma [sepref_fr_rules]:
  \<open>((uncurry (return oo (check_extension_l_new_var_multiple_err_impl))),
    uncurry (check_extension_l_new_var_multiple_err)) \<in> string_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_new_var_multiple_err_impl_def
     check_extension_l_new_var_multiple_err_def
     list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

sepref_definition check_extension_l_impl
  is \<open>uncurry5 check_extension_l2\<close>
    :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a
    string_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_extension_l2_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    not_not is_None_def
    uminus_poly_def[symmetric]
    HOL_list.fold_custom_empty
    check_extension_l2_cond_def[symmetric]
    vars_llist_alt_def
  by sepref

lemmas [sepref_fr_rules] =
  check_extension_l_impl.refine

lemma is_Mult_lastI:
  \<open>\<not> is_CL b \<Longrightarrow> \<not>is_Extension b \<Longrightarrow> is_Del b\<close>
  by (cases b) auto

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

definition full_checker_l2
  :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l2 spec A st = do {
    spec' \<leftarrow> full_normalize_poly spec;
    (b, \<V>, A) \<leftarrow> remap_polys_l spec {} A;
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      PAC_checker_l spec' (\<V>, A) b st
    }
  }\<close>

sepref_register remap_polys_l
find_theorems full_checker_l2
sepref_definition full_checker_l_impl
  is \<open>uncurry2 full_checker_l2\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>d *\<^sub>a (list_assn (pac_step_rel_assn (uint64_nat_assn) poly_assn string_assn))\<^sup>k \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding full_checker_l_def hs.fold_custom_empty
    union_vars_poly_alt_def[symmetric]
    PAC_checker_l_alt_def
    full_checker_l2_def
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
  int_of_integer Del nat_of_integer String.implode remap_polys_l_impl
  fully_normalize_poly_impl union_vars_poly_impl empty_vars_impl
  full_checker_l_impl check_step_impl CSUCCESS
  Extension hashcode_literal' version
  in SML_imp module_name PAC_Checker
  file_prefix checker


compile_generated_files _
  external_files
    \<open>code/no_sharing/parser.sml\<close>
    \<open>code/no_sharing/pasteque.sml\<close>
    \<open>code/no_sharing/pasteque.mlb\<close>
  where \<open>fn dir =>
  let

    val exec = Generated_Files.execute (Path.append (Path.append dir (Path.basic "code")) (Path.basic "no_sharing"));
    val _ = exec \<open>Copy files\<close> "ls" |> @{print}
    val _ = exec \<open>Copy files\<close> "ls .." |> @{print}
    val _ = exec \<open>Copy files\<close> "pwd" |> @{print}
    val _ = exec \<open>Copy files\<close> ("cp ../checker.ML .");
    val _ = exec \<open>Copy files\<close>
      ("cp ../checker.ML " ^ ((File.bash_path \<^path>\<open>$ISAFOL\<close>) ^ "/PAC_Checker2/code/no_sharing/checker.ML"));
(*       val _ =
        exec \<open>Compilation\<close>
          (File.bash_path \<^path>\<open>$ISABELLE_MLTON\<close> ^ " " ^
            "-const 'MLton.safe false' -verbose 1 -default-type int64 -output pasteque " ^
            "-codegen native -inline 700 -cc-opt -O3 pasteque.mlb"); *)
    in () end\<close> 


end
