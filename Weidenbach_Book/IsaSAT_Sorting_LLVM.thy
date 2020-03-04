theory IsaSAT_Sorting_LLVM
  imports IsaSAT_Sorting IsaSAT_Setup_LLVM
    Isabelle_LLVM.Sorting_Introsort
begin

no_notation WB_More_Refinement.fref ("[_]\<^sub>f _ \<rightarrow> _" [0,60,60] 60)
no_notation WB_More_Refinement.freft ("_ \<rightarrow>\<^sub>f _" [60,60] 60)
declare \<alpha>_butlast[simp del]

locale pure_eo_adapter =
  fixes elem_assn :: "'a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn"
    and wo_assn :: "'a list \<Rightarrow> 'oi::llvm_rep \<Rightarrow> assn"
    and wo_get_impl :: "'oi \<Rightarrow> 'size::len2 word \<Rightarrow> 'ai llM"
    and wo_set_impl :: "'oi \<Rightarrow> 'size::len2 word \<Rightarrow> 'ai \<Rightarrow> 'oi llM"
  assumes pure[safe_constraint_rules]: "is_pure elem_assn"
      and get_hnr: "(uncurry wo_get_impl,uncurry mop_list_get) \<in> wo_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a elem_assn"
      and set_hnr: "(uncurry2 wo_set_impl,uncurry2 mop_list_set) \<in> wo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ ((ai,_),_). cnc_assn (\<lambda>x. x=ai) wo_assn)"
begin

  lemmas [sepref_fr_rules] = get_hnr set_hnr


  definition "only_some_rel \<equiv> {(a, Some a) | a. True} \<union> {(x, None) | x. True}"

  definition "eo_assn \<equiv> hr_comp wo_assn (\<langle>only_some_rel\<rangle>list_rel)"

  definition "eo_extract1 p i \<equiv> doN { r \<leftarrow> mop_list_get p i; RETURN (r,p) }"
  sepref_definition eo_extract_impl is "uncurry eo_extract1"
    :: "wo_assn\<^sup>d *\<^sub>a (snat_assn' TYPE('size))\<^sup>k \<rightarrow>\<^sub>a elem_assn \<times>\<^sub>a wo_assn"
    unfolding eo_extract1_def
    by sepref

  lemma mop_eo_extract_aux: "mop_eo_extract p i = doN { r \<leftarrow> mop_list_get p i; ASSERT (r\<noteq>None \<and> i<length p); RETURN (the r, p[i:=None]) }"
    by (auto simp: pw_eq_iff refine_pw_simps)

  lemma assign_none_only_some_list_rel:
    assumes SR[param]: "(a, a') \<in> \<langle>only_some_rel\<rangle>list_rel" and L: "i < length a'"
      shows "(a, a'[i := None]) \<in> \<langle>only_some_rel\<rangle>list_rel"
  proof -
    have "(a[i := a!i], a'[i := None]) \<in> \<langle>only_some_rel\<rangle>list_rel"
      apply (parametricity)
      by (auto simp: only_some_rel_def)
    also from L list_rel_imp_same_length[OF SR] have "a[i := a!i] = a" by auto
    finally show ?thesis .
  qed


  lemma eo_extract1_refine: "(eo_extract1, mop_eo_extract) \<in> \<langle>only_some_rel\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id \<times>\<^sub>r \<langle>only_some_rel\<rangle>list_rel\<rangle>nres_rel"
    unfolding eo_extract1_def mop_eo_extract_aux
    supply R = mop_list_get.fref[THEN frefD, OF TrueI prod_relI, unfolded uncurry_apply, THEN nres_relD]
    apply (refine_rcg R)
    apply assumption
    apply (clarsimp simp: assign_none_only_some_list_rel)
    by (auto simp: only_some_rel_def)

  lemma eo_list_set_refine: "(mop_list_set, mop_eo_set) \<in> \<langle>only_some_rel\<rangle>list_rel \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>\<langle>only_some_rel\<rangle>list_rel\<rangle>nres_rel"
    unfolding mop_list_set_alt mop_eo_set_alt
    apply refine_rcg
    apply (simp add: list_rel_imp_same_length)
    apply simp
    apply parametricity
    apply (auto simp: only_some_rel_def)
    done


  lemma set_hnr': "(uncurry2 wo_set_impl,uncurry2 mop_list_set) \<in> wo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k \<rightarrow>\<^sub>a wo_assn"
    apply (rule hfref_cons[OF set_hnr])
    apply (auto simp: cnc_assn_def entails_lift_extract_simps sep_algebra_simps)
    done



  context
    notes [fcomp_norm_unfold] = eo_assn_def[symmetric]
  begin
    lemmas eo_extract_refine_aux = eo_extract_impl.refine[FCOMP eo_extract1_refine]

    lemma eo_extract_refine: "(uncurry eo_extract_impl, uncurry mop_eo_extract) \<in> eo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k
      \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ (ai,_). elem_assn \<times>\<^sub>a cnc_assn (\<lambda>x. x=ai) eo_assn)"
      apply (sepref_to_hnr)
      apply (rule hn_refine_nofailI)
      unfolding cnc_assn_prod_conv
      apply (rule hnr_ceq_assnI)
      subgoal
        supply R = eo_extract_refine_aux[to_hnr, unfolded APP_def]
        apply (rule hn_refine_cons[OF _ R])
        apply (auto simp: sep_algebra_simps entails_lift_extract_simps hn_ctxt_def pure_def invalid_assn_def)
        done
      subgoal
        unfolding eo_extract_impl_def mop_eo_extract_def hn_ctxt_def eo_assn_def hr_comp_def
        supply R = get_hnr[to_hnr, THEN hn_refineD, unfolded APP_def hn_ctxt_def]
        thm R
        supply [vcg_rules] = R
        supply [simp] = refine_pw_simps list_rel_imp_same_length
        apply (vcg)
        done
      done


    lemmas eo_set_refine_aux = set_hnr'[FCOMP eo_list_set_refine]

    lemma pure_part_cnc_imp_eq: "pure_part (cnc_assn (\<lambda>x. x = cc) wo_assn a c) \<Longrightarrow> c=cc"
      by (auto simp: pure_part_def cnc_assn_def pred_lift_extract_simps)

    (* TODO: Move *)
    lemma pure_entails_empty: "is_pure A \<Longrightarrow> A a c \<turnstile> \<box>"
      by (auto simp: is_pure_def sep_algebra_simps entails_lift_extract_simps)


    lemma eo_set_refine: "(uncurry2 wo_set_impl, uncurry2 mop_eo_set) \<in> eo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a elem_assn\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ ((ai, _), _). cnc_assn (\<lambda>x. x = ai) eo_assn)"
      apply (sepref_to_hnr)
      apply (rule hn_refine_nofailI)
      apply (rule hnr_ceq_assnI)
      subgoal
        supply R = eo_set_refine_aux[to_hnr, unfolded APP_def]
        apply (rule hn_refine_cons[OF _ R])
        apply (auto simp: sep_algebra_simps entails_lift_extract_simps hn_ctxt_def pure_def invalid_assn_def pure_entails_empty[OF pure])
        done
      subgoal
        unfolding hn_ctxt_def eo_assn_def hr_comp_def
        supply R = set_hnr[to_hnr, THEN hn_refineD, unfolded APP_def hn_ctxt_def]
        supply [vcg_rules] = R
        supply [simp] = refine_pw_simps list_rel_imp_same_length pure_part_cnc_imp_eq
        apply (vcg')
        done
      done

  end

  lemma id_Some_only_some_rel: "(id, Some) \<in> Id \<rightarrow> only_some_rel"
    by (auto simp: only_some_rel_def)

  lemma map_some_only_some_rel_iff: "(xs, map Some ys) \<in> \<langle>only_some_rel\<rangle>list_rel \<longleftrightarrow> xs=ys"
    apply (rule iffI)
    subgoal
      apply (induction xs "map Some ys" arbitrary: ys rule: list_rel_induct)
      apply (auto simp: only_some_rel_def)
      done
    subgoal
      apply (rewrite in "(\<hole>,_)" list.map_id[symmetric])
      apply (parametricity add: id_Some_only_some_rel)
      by simp
    done


  lemma wo_assn_conv: "wo_assn xs ys = eo_assn (map Some xs) ys"
    unfolding eo_assn_def hr_comp_def
    by (auto simp: pred_lift_extract_simps sep_algebra_simps fun_eq_iff map_some_only_some_rel_iff)

  lemma to_eo_conv_refine: "(return, mop_to_eo_conv) \<in> wo_assn\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ ai. cnc_assn (\<lambda>x. x = ai) eo_assn)"
    unfolding mop_to_eo_conv_def cnc_assn_def
    apply sepref_to_hoare
    apply (rewrite wo_assn_conv)
    apply vcg
    done

  lemma "None \<notin> set xs \<longleftrightarrow> (\<exists>ys. xs = map Some ys)"
    using None_not_in_set_conv by auto

  lemma to_wo_conv_refine: "(return, mop_to_wo_conv) \<in> eo_assn\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ ai. cnc_assn (\<lambda>x. x = ai) wo_assn)"
    unfolding mop_to_wo_conv_def cnc_assn_def eo_assn_def hr_comp_def
    apply sepref_to_hoare
    apply (auto simp add: refine_pw_simps map_some_only_some_rel_iff elim!: None_not_in_set_conv)
    by vcg

  lemma random_access_iterator: "random_access_iterator wo_assn eo_assn elem_assn
    return return
    eo_extract_impl
    wo_set_impl"
    apply unfold_locales
    using to_eo_conv_refine to_wo_conv_refine eo_extract_refine eo_set_refine
    apply blast+
    done

  sublocale random_access_iterator wo_assn eo_assn elem_assn
    return return
    eo_extract_impl
    wo_set_impl
    by (rule random_access_iterator)

end

lemma al_pure_eo: "is_pure A \<Longrightarrow> pure_eo_adapter A (al_assn A) arl_nth arl_upd"
  apply unfold_locales
  apply assumption
  apply (rule al_nth_hnr_mop; simp)
  subgoal
    apply (sepref_to_hnr)
    apply (rule hn_refine_nofailI)
    apply (rule hnr_ceq_assnI)
    subgoal
      supply R = al_upd_hnr_mop[to_hnr, unfolded APP_def, of A]
      apply (rule hn_refine_cons[OF _ R])
      apply (auto simp: hn_ctxt_def pure_def invalid_assn_def sep_algebra_simps entails_lift_extract_simps)
      done
    subgoal
      unfolding hn_ctxt_def al_assn_def hr_comp_def pure_def in_snat_rel_conv_assn
      apply (erule is_pureE)
      apply (simp add: refine_pw_simps)
      supply [simp] = list_rel_imp_same_length
      by vcg
    done
  done


end