theory PAC_Checker_Init
  imports  PAC_Checker WB_Sort PAC_Checker_Relation
begin


lemma merge_coeffs_alt_def:
  \<open>(RETURN o merge_coeffs) p =
   REC\<^sub>T(\<lambda>f p.
     (case p of
       [] \<Rightarrow> RETURN []
     | [_] => RETURN p
     | ((xs, n) # (ys, m) # p) \<Rightarrow>
      (if xs = ys
       then if n + m \<noteq> 0 then f ((xs, n + m) # p) else f p
       else do {p \<leftarrow> f ((ys, m) # p); RETURN ((xs, n) # p)})))
    p\<close>
  apply (induction p rule: merge_coeffs.induct)
  subgoal
    apply (subst RECT_unfold)
    apply refine_mono
    apply auto
    done
  subgoal
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
lemma hn_invalid_recover:
  \<open>is_pure R \<Longrightarrow> hn_invalid R = (\<lambda>x y. R x y * true)\<close>
  \<open>is_pure R \<Longrightarrow> invalid_assn R = (\<lambda>x y. R x y * true)\<close>
  by (auto simp: is_pure_conv invalid_pure_recover hn_ctxt_def intro!: ext)

lemma [fcomp_norm_unfold]:
  \<open>(pure R \<times>\<^sub>a pure S) = pure (R \<times>\<^sub>r S)\<close>
  by auto

lemma safe_poly_vars:
  shows
  [safe_constraint_rules]:
    "is_pure (poly_assn)" and
  [safe_constraint_rules]:
    "is_pure (monom_assn)" and
  [safe_constraint_rules]:
    "is_pure (monomial_assn)" and
  [safe_constraint_rules]:
    "is_pure string_assn"
  by (auto intro!: pure_prod list_assn_pure simp: prod_assn_pure_conv)

lemma invalid_assn_distrib:
  \<open>invalid_assn monom_assn \<times>\<^sub>a invalid_assn int_assn = invalid_assn (monom_assn \<times>\<^sub>a int_assn)\<close>
    apply (simp add: invalid_pure_recover hn_invalid_recover
      safe_constraint_rules)
    apply (subst hn_invalid_recover)
    apply (rule safe_poly_vars(2))
    apply (subst hn_invalid_recover)
    apply (rule safe_poly_vars)
    apply (auto intro!: ext)
    done

lemma WTF_RF_recover:
  \<open>hn_ctxt (invalid_assn monom_assn \<times>\<^sub>a invalid_assn int_assn) xb
        x'a \<or>\<^sub>A
       hn_ctxt monomial_assn xb x'a \<Longrightarrow>\<^sub>t
       hn_ctxt (monomial_assn) xb x'a\<close>
   by (smt assn_aci(5) hn_ctxt_def invalid_assn_distrib invalid_pure_recover is_pure_conv merge_thms(4) merge_true_star reorder_enttI safe_poly_vars(3) star_aci(2) star_aci(3))

lemma WTF_RF:
  \<open>hn_ctxt (invalid_assn monom_assn \<times>\<^sub>a invalid_assn int_assn) xb x'a *
       (hn_invalid poly_assn la l'a * hn_invalid int_assn a2' a2 *
        hn_invalid monom_assn a1' a1 *
        hn_invalid poly_assn l l' *
        hn_invalid monomial_assn xa x' *
        hn_invalid poly_assn ax px) \<Longrightarrow>\<^sub>t
       hn_ctxt (monomial_assn) xb x'a *
       hn_ctxt poly_assn
        la l'a *
       hn_ctxt poly_assn l l' *
       (hn_invalid int_assn a2' a2 *
        hn_invalid monom_assn a1' a1 *
        hn_invalid monomial_assn xa x' *
        hn_invalid poly_assn ax px)\<close>
  \<open>hn_ctxt (invalid_assn monom_assn \<times>\<^sub>a invalid_assn int_assn) xa x' *
       (hn_ctxt poly_assn l l' * hn_invalid poly_assn ax px) \<Longrightarrow>\<^sub>t
       hn_ctxt (monomial_assn) xa x' *
       hn_ctxt poly_assn l l' *
       hn_ctxt poly_assn ax px *
       emp\<close>
  by sepref_dbg_trans_step+

sepref_definition merge_coeffs_impl
  is \<open>RETURN o merge_coeffs\<close>
  :: \<open>poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding merge_coeffs_alt_def
    HOL_list.fold_custom_empty
  apply (rewrite in \<open>_\<close> annotate_assn[where A=\<open>poly_assn\<close>])
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply (rule WTF_RF)
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply (rule WTF_RF)
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done
(*FIXME!*)

definition full_quicksort_poly where
  \<open>full_quicksort_poly = full_quicksort_ref (\<lambda>x y. x = y \<or> (x, y) \<in> term_order_rel) fst\<close>

lemma down_eq_id_list_rel: \<open>\<Down>(\<langle>Id\<rangle>list_rel) x = x\<close>
  by auto

definition quicksort_poly:: \<open>nat \<Rightarrow> nat \<Rightarrow> llist_polynom \<Rightarrow> (llist_polynom) nres\<close> where
  \<open>quicksort_poly x y  z = quicksort_ref (\<le>) fst (x, y, z)\<close>

term partition_between_ref

definition partition_between_poly :: \<open>nat \<Rightarrow> nat \<Rightarrow> llist_polynom \<Rightarrow> (llist_polynom \<times> nat) nres\<close> where
  \<open>partition_between_poly = partition_between_ref (\<le>) fst\<close>

definition partition_main_poly :: \<open>nat \<Rightarrow> nat \<Rightarrow> llist_polynom \<Rightarrow> (llist_polynom \<times> nat) nres\<close> where
  \<open>partition_main_poly = partition_main (\<le>)  fst\<close>

lemma full_quicksort_sort_poly_spec:
  \<open>(full_quicksort_poly, sort_poly_spec) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
proof -
  have xs: \<open>(xs, xs) \<in> \<langle>Id\<rangle>list_rel\<close> and \<open>\<Down>(\<langle>Id\<rangle>list_rel) x = x\<close> for x xs
    by auto
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding full_quicksort_poly_def
    apply (rule full_quicksort_ref_full_quicksort[THEN fref_to_Down_curry, THEN order_trans])
    subgoal
      apply (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def)
      apply (smt less_char_def char.less_trans less_than_char_def lexord_partial_trans p2rel_def)
      done
    subgoal
      using total_on_lexord_less_than_char_linear[unfolded var_order_rel_def]
      apply (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def less_char_def)
      done
    subgoal by fast
    apply (rule xs)
    apply (subst down_eq_id_list_rel)
    unfolding sorted_wrt_map sort_poly_spec_def
    apply (rule full_quicksort_correct_sorted[where R = \<open>(\<lambda>x y. x = y \<or> (x, y) \<in> term_order_rel)\<close> and h = \<open>fst\<close>,
       THEN order_trans])
    subgoal
      apply (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def)
      apply (smt less_char_def char.less_trans less_than_char_def lexord_partial_trans p2rel_def)
      done
    subgoal for x y
      using total_on_lexord_less_than_char_linear[unfolded var_order_rel_def]
      apply (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def
        less_char_def)
      done
   subgoal
    by (auto simp: rel2p_def p2rel_def)
   done
qed

lemma le_term_order_rel':
  \<open>(\<le>) = (\<lambda>x y. x = y \<or>  term_order_rel' x y)\<close>
  apply (intro ext)
  apply (auto simp add: less_list_def less_eq_list_def
    lexordp_eq_conv_lexord lexordp_def)
  using term_order_rel'_alt_def_lexord term_order_rel'_def apply blast
  using term_order_rel'_alt_def_lexord term_order_rel'_def apply blast
  done

sepref_definition partition_main_poly_impl
  is \<open>uncurry2 partition_main_poly\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a prod_assn poly_assn nat_assn \<close>
  unfolding partition_main_poly_def partition_main_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    le_term_order_rel'
  by sepref

declare partition_main_poly_impl.refine[sepref_fr_rules]

sepref_definition partition_between_poly_impl
  is \<open>uncurry2 partition_between_poly\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a prod_assn poly_assn nat_assn \<close>
  unfolding partition_between_poly_def partition_between_ref_def
    partition_main_poly_def[symmetric]
  unfolding choose_pivot3_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def choose_pivot_def
    le_term_order_rel'
  by sepref

declare partition_between_poly_impl.refine[sepref_fr_rules]

sepref_definition quicksort_poly_impl
  is \<open>uncurry2 quicksort_poly\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding partition_main_poly_def quicksort_ref_def quicksort_poly_def
    partition_between_poly_def[symmetric]
  by sepref

lemmas [sepref_fr_rules] = quicksort_poly_impl.refine

sepref_register quicksort_poly
sepref_definition full_quicksort_poly_impl
  is \<open>full_quicksort_poly\<close>
  :: \<open>poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding full_quicksort_poly_def full_quicksort_ref_def
    quicksort_poly_def[symmetric]
    le_term_order_rel'[symmetric]
    term_order_rel'_def[symmetric]
    List.null_def
  by sepref


lemmas sort_poly_spec_hnr[sepref_fr_rules] =
  full_quicksort_poly_impl.refine[FCOMP full_quicksort_sort_poly_spec]

declare merge_coeffs_impl.refine[sepref_fr_rules]
sepref_definition normalize_poly_impl
  is \<open>normalize_poly\<close>
  :: \<open>poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding normalize_poly_def
  by sepref

declare normalize_poly_impl.refine[sepref_fr_rules]


end