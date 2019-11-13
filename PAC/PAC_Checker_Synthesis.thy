theory PAC_Checker_Synthesis
  imports PAC_Checker WB_Sort PAC_Checker_Relation
    PAC_Checker_Init
begin


fun status_assn where
  \<open>status_assn _ SUCCESS SUCCESS = emp\<close> |
  \<open>status_assn R (FAILED a) (FAILED b) = R a b\<close> |
  \<open>status_assn _ _ _ = false\<close>

lemma SUCCESS_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return SUCCESS), uncurry0 (RETURN SUCCESS)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn R\<close>
  by (sepref_to_hoare)
    sep_auto

lemma is_success_hnr[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure R \<Longrightarrow>
  ((return o is_success), (RETURN o is_success)) \<in> (status_assn R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply (sepref_to_hoare)
  apply (case_tac xi; case_tac x)
  apply  sep_auto+
  done


sepref_definition add_poly_impl
  is \<open> add_poly_l\<close>
  :: \<open>(poly_assn \<times>\<^sub>a poly_assn)\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_poly_l_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref


declare add_poly_impl.refine[sepref_fr_rules]


sepref_register mult_monomials
lemma mult_monoms_alt_def:
  \<open>(RETURN oo mult_monoms) x y = REC\<^sub>T
    (\<lambda>f (p, q).
      case (p, q) of
        ([], _) \<Rightarrow> RETURN q
       | (_, []) \<Rightarrow> RETURN p
       | (x # p, y # q) \<Rightarrow>
        (if x = y then do {
          pq \<leftarrow> f (p, q);
           RETURN (x # pq)}
        else if (x, y) \<in> var_order_rel
        then do {
          pq \<leftarrow> f (p, y # q);
          RETURN (x # pq)}
        else do {
          pq \<leftarrow>  f (x # p, q);
          RETURN (y # pq)}))
     (x, y)\<close>
  apply (induction x y rule: mult_monoms.induct)
  subgoal for p 
    apply (subst RECT_unfold)
    apply refine_mono
    apply (cases p)
    apply auto
    done
  subgoal for p 
    apply (subst RECT_unfold)
    apply refine_mono
    apply (cases p)
    apply auto
    done
  subgoal for x p y q 
    apply (subst RECT_unfold)
    apply refine_mono
    apply (auto simp: let_to_bind_conv)
    apply (metis let_to_bind_conv)+
    done
  done


sepref_definition mult_monoms_impl
  is \<open>uncurry (RETURN oo mult_monoms)\<close>
  :: \<open>(monom_assn)\<^sup>k *\<^sub>a (monom_assn)\<^sup>k \<rightarrow>\<^sub>a (monom_assn)\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_raw_def
    HOL_list.fold_custom_empty
    var_order'_def[symmetric]
    term_order_rel'_alt_def
    mult_monoms_alt_def
    var_order_rel_var_order
  by sepref

declare mult_monoms_impl.refine[sepref_fr_rules]

sepref_definition mult_monomials_impl
  is \<open>uncurry (RETURN oo mult_monomials)\<close>
  :: \<open>(monomial_assn)\<^sup>k *\<^sub>a (monomial_assn)\<^sup>k \<rightarrow>\<^sub>a (monomial_assn)\<close>
  supply [[goals_limit=1]]
  unfolding mult_monomials_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref


declare mult_monomials_impl.refine[sepref_fr_rules]

text \<open>TODO @{thm map_by_foldl} is the worst possible implementation of map!\<close>
sepref_definition mult_poly_raw_impl
  is \<open>uncurry (RETURN oo mult_poly_raw)\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  supply [[eta_contract = false, show_abbrevs=false]]
  unfolding mult_poly_raw_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    foldl_conv_fold
    fold_eq_nfoldli
    map_by_foldl[symmetric]
  apply (rewrite in "_" eta_expand[where f = \<open>(@) u\<close> for u])
  by sepref

declare mult_poly_raw_impl.refine[sepref_fr_rules]


sepref_definition mult_poly_impl
  is \<open>uncurry mult_poly_full\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_full_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref

declare mult_poly_impl.refine[sepref_fr_rules]

lemma single_valued_monom_rel: \<open>single_valued monom_rel\<close>
  by (rule list_rel_sv)
    (auto intro!: frefI simp: string_rel_def
    rel2p_def single_valued_def p2rel_def)

lemma single_valued_monomial_rel:
  \<open>single_valued monomial_rel\<close>
  using single_valued_monom_rel
  by (auto intro!: frefI simp:
    rel2p_def single_valued_def p2rel_def)

lemma single_valued_monom_rel': \<open>IS_LEFT_UNIQUE monom_rel\<close>
  unfolding IS_LEFT_UNIQUE_def inv_list_rel_eq
  by (rule list_rel_sv)
   (auto intro!: frefI simp: string_rel_def
    rel2p_def single_valued_def p2rel_def literal.explode_inject)


lemma single_valued_monomial_rel':
  \<open>IS_LEFT_UNIQUE monomial_rel\<close>
  using single_valued_monom_rel'
  unfolding IS_LEFT_UNIQUE_def inv_list_rel_eq
  by (auto intro!: frefI simp:
    rel2p_def single_valued_def p2rel_def)

lemma inverse_monomial:
  \<open>monom_rel\<inverse> \<times>\<^sub>r int_rel = (monom_rel \<times>\<^sub>r int_rel)\<inverse>\<close>
  by (auto)

lemma eq_poly_rel_eq[sepref_import_param]:
  \<open>((=), (=)) \<in> poly_rel \<rightarrow> poly_rel \<rightarrow> bool_rel\<close>
  using list_rel_sv[of \<open>monomial_rel\<close>, OF single_valued_monomial_rel]
  using list_rel_sv[OF single_valued_monomial_rel'[unfolded IS_LEFT_UNIQUE_def inv_list_rel_eq]]
  unfolding inv_list_rel_eq[symmetric]
  by (auto intro!: frefI simp: 
      rel2p_def single_valued_def p2rel_def
    simp del: inv_list_rel_eq)

sepref_definition weak_equality_p_impl
  is \<open>uncurry weak_equality_p\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding weak_equality_p_def
  by sepref

declare weak_equality_p_impl.refine[sepref_fr_rules]
sepref_register add_poly_l mult_poly_full

abbreviation raw_string_assn :: \<open>string \<Rightarrow> string \<Rightarrow> assn\<close> where
  \<open>raw_string_assn \<equiv> list_assn id_assn\<close>

definition show_nat :: \<open>nat \<Rightarrow> string\<close> where
  \<open>show_nat i = show i\<close>

lemma [sepref_import_param]:
  \<open>(show_nat, show_nat) \<in> nat_rel \<rightarrow> \<langle>Id\<rangle>list_rel\<close>
  by (auto intro: fun_relI)
  
lemma status_assn_pure_conv:
  \<open>status_assn (id_assn) a b = id_assn a b\<close>
  by (cases a; cases b)
    (auto simp: pure_def)


lemma  [sepref_fr_rules]:
  \<open>(uncurry (return oo error_msg_not_equal_dom), uncurry (RETURN oo error_msg_not_equal_dom)) \<in> poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding show_nat_def[symmetric] list_assn_pure_conv
    prod_assn_pure_conv
  apply (sepref_to_hoare; sep_auto simp: error_msg_not_equal_dom_def list_assn_aux_append)
  apply (auto simp: shows_prec_literal_def string_rel_def)
  supply[[show_types]]
  sorry

term "shows_prec"
find_theorems shows_prec "_ :: String.literal"
lemma [sepref_fr_rules]:
  \<open>(return o error_msg_notin_dom, RETURN o error_msg_notin_dom) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  \<open>(return o error_msg_reused_dom, RETURN o error_msg_reused_dom) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  \<open>(uncurry (return oo error_msg), uncurry (RETURN oo error_msg)) \<in> nat_assn\<^sup>k *\<^sub>a raw_string_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  unfolding error_msg_notin_dom_def list_assn_pure_conv list_rel_id_simp
  unfolding status_assn_pure_conv
  unfolding show_nat_def[symmetric]
  by (sepref_to_hoare; sep_auto; fail)+

sepref_definition check_addition_l_impl
  is \<open>uncurry4 check_addition_l\<close>
  :: \<open>polys_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_full_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    check_addition_l_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
  by sepref

declare check_addition_l_impl.refine[sepref_fr_rules]

sepref_register check_mult_l_dom_err

definition check_mult_l_dom_err_impl where
  \<open>check_mult_l_dom_err_impl pd p ia i =
    (if pd then ''The polynom with id '' @ show p @ '' was not found'' else '''') @
    (if ia then ''The id of the resulting id '' @ show i @ '' was was already given'' else '''')\<close>

definition check_mult_l_mult_err_impl where
  \<open>check_mult_l_mult_err_impl p q pq r =
    ''Multiplying '' @ show p @ '' by '' @ show q @ '' gives '' @ show pq @ '' and not '' @ show r\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry3 ((\<lambda>x y. return oo (check_mult_l_dom_err_impl x y))),
   uncurry3 (check_mult_l_dom_err)) \<in> bool_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_mult_l_dom_err_def check_mult_l_dom_err_impl_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

lemma [sepref_fr_rules]:
  \<open>(uncurry3 ((\<lambda>x y. return oo (check_mult_l_mult_err_impl x y))),
   uncurry3 (check_mult_l_mult_err)) \<in> poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_mult_l_mult_err_def check_mult_l_mult_err_impl_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

sepref_definition check_mult_l_impl
  is \<open>uncurry4 check_mult_l\<close>
  :: \<open>polys_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_mult_l_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    check_addition_l_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
  by sepref

declare check_mult_l_impl.refine[sepref_fr_rules]

abbreviation pac_step_rel where
  \<open>pac_step_rel \<equiv> p2rel (\<langle>Id, \<langle>monomial_rel\<rangle>list_rel\<rangle> pac_step_rel_raw)\<close>

sepref_register PAC_Polynoms_Operations.normalize_poly
  pac_src1 pac_src2 new_id pac_mult case_pac_step check_mult_l
  check_addition_l

lemma [fcomp_norm_unfold]:
  \<open>pure (p2rel (\<langle>K, V\<rangle>pac_step_rel_raw)) = pac_step_rel_assn (pure K) (pure V)\<close>
  \<open>monomial_assn = pure (monom_rel \<times>\<^sub>r int_rel)\<close> and
  poly_assn_list[fcomp_norm_unfold]:
    \<open>poly_assn = pure (\<langle>monom_rel \<times>\<^sub>r int_rel\<rangle>list_rel)\<close>
  subgoal
    apply (intro ext)
    apply (case_tac x; case_tac xa)
    apply (auto simp: relAPP_def p2rel_def pure_def)
    done
  subgoal H
    apply (intro ext)
    apply (case_tac x; case_tac xa)
    by (simp add: list_assn_pure_conv)
  subgoal
    unfolding H
    by (simp add: list_assn_pure_conv relAPP_def)
  done

term poly_rel

lemma is_AddD_import[sepref_import_param]:
  \<open>(is_AddD, is_AddD) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> bool_rel\<close>
  \<open>(pac_res, pac_res) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> V\<close>
  \<open>(pac_src1, pac_src1) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> K\<close>
  \<open>(new_id, new_id) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> K\<close>
  \<open>(is_Add, is_Add) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> bool_rel\<close>
  \<open>(is_AddD, is_AddD) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> bool_rel\<close>
  \<open>(is_Mult, is_Mult) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> bool_rel\<close>
  \<open>(is_MultD, is_MultD) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> bool_rel\<close>
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  done

lemma [sepref_fr_rules]:
  \<open>CONSTRAINT is_pure K \<Longrightarrow>
  (return o pac_src2, RETURN o pac_src2) \<in> [\<lambda>x. is_Add x \<or> is_AddD x]\<^sub>a (pac_step_rel_assn K V)\<^sup>k \<rightarrow> K\<close>
  apply sepref_to_hoare
  apply sep_auto
  apply (case_tac x; case_tac xi)
  apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
  apply (case_tac x; case_tac xi)
  apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
  done

lemma [sepref_fr_rules]:
  \<open>CONSTRAINT is_pure V \<Longrightarrow>
  (return o pac_mult, RETURN o pac_mult) \<in> [\<lambda>x. is_Mult x \<or> is_MultD x]\<^sub>a (pac_step_rel_assn K V)\<^sup>k \<rightarrow> V\<close>
  apply sepref_to_hoare
  apply sep_auto
  apply (case_tac x; case_tac xi)
  apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
  apply (case_tac x; case_tac xi)
  apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
  done

lemma is_Mult_lastI:
  \<open>\<not> is_AddD b \<Longrightarrow>
       \<not> is_Add b \<Longrightarrow>
       \<not> is_MultD b \<Longrightarrow> is_Mult b\<close>
  by (cases b) auto

sepref_definition check_step_impl
  is \<open>uncurry PAC_checker_l_step\<close>
  :: \<open>polys_assn\<^sup>d *\<^sub>a (pac_step_rel_assn (nat_assn) poly_assn)\<^sup>d \<rightarrow>\<^sub>a status_assn raw_string_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_step_def
    pac_step.case_eq_if
     is_success_alt_def[symmetric]
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply (subst poly_assn_list)
  apply (rule entt_refl)
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done

declare check_step_impl.refine[sepref_fr_rules]

instantiation pac_step :: (heap) heap
begin
  
instance
proof standard
  obtain f :: \<open>'a \<Rightarrow> nat\<close> where
    f: \<open>inj f\<close>
    by blast
  obtain g :: \<open>nat \<times> nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat\<close> where
    g: \<open>inj g\<close>
    by blast
  have [iff]: \<open>g a = g b \<longleftrightarrow> a = b\<close>  \<open>f a' = f b' \<longleftrightarrow> a' = b'\<close> for a b a' b'
    using f g unfolding inj_def by blast+
  let ?f = \<open>\<lambda>x :: 'a pac_step.
     g (case x of
        Add a b c d \<Rightarrow> (0, a, b, c, f d)
      | AddD a b c d \<Rightarrow> (1, a, b, c, f d)
      | Mult a b c d \<Rightarrow> (2, a, f b, c, f d)
      | MultD a b c d \<Rightarrow> (3, a, f b, c, f d))\<close>
   have \<open>inj ?f\<close>
     apply (auto simp: inj_def)
     apply (case_tac x; case_tac y)
     apply auto
     done
   then show \<open>\<exists>f :: 'a pac_step \<Rightarrow> nat. inj f\<close>
     by blast
qed

end

lemma safe_pac_step_rel_assn[safe_constraint_rules]:
  "is_pure K \<Longrightarrow> is_pure V \<Longrightarrow> is_pure (pac_step_rel_assn K V)"
  by (auto simp: fcomp_norm_unfold(31)[symmetric] is_pure_conv)

term bool_with_error_msg
sepref_register PAC_checker_l_step
sepref_definition PAC_checker_l_impl
  is \<open>uncurry PAC_checker_l\<close>
  :: \<open>polys_assn\<^sup>d *\<^sub>a (array_assn (pac_step_rel_assn (nat_assn) poly_assn))\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_def is_success_alt_def[symmetric]
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done

sepref_definition PAC_update_impl
  is \<open>uncurry2 (RETURN ooo fmupd)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a (polys_assn)\<^sup>d \<rightarrow>\<^sub>a polys_assn\<close>
  unfolding comp_def
  by sepref

sepref_definition PAC_empty_impl
  is \<open>uncurry0 (RETURN fmempty)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a polys_assn\<close>
  unfolding op_fmap_empty_def[symmetric] pat_fmap_empty
  by sepref

export_code PAC_checker_l_impl PAC_update_impl PAC_empty_impl is_success status_error
  int_of_integer AddD Add Mult MultD nat_of_integer String.implode fully_normalize_poly_impl
  in SML_imp module_name PAC_Checker
  file "code/checker.sml"

end