theory IsaSAT_Sorting_LLVM
  imports IsaSAT_Sorting
    Isabelle_LLVM.Sorting_Ex_Array_Idxs
    IsaSAT_Literals_LLVM 
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)
declare \<alpha>_butlast[simp del]
hide_const (open) NEMonad.RETURN NEMonad.ASSERT

text \<open>All the weird proofs comes from the fact that, while very useful, \<^text>\<open>vcg\<close> enjoys 
instantiating schematic variables by true, rendering proofs impossible.\<close>
locale pure_eo_adapter =
  fixes elem_assn :: \<open>'a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn\<close>
    and wo_assn :: \<open>'a list \<Rightarrow> 'oi::llvm_rep \<Rightarrow> assn\<close>
    and wo_get_impl :: \<open>'oi \<Rightarrow> 'size::len2 word \<Rightarrow> 'ai llM\<close>
    and wo_set_impl :: \<open>'oi \<Rightarrow> 'size::len2 word \<Rightarrow> 'ai \<Rightarrow> 'oi llM\<close>
  assumes pure[safe_constraint_rules]: \<open>is_pure elem_assn\<close>
      and get_hnr: \<open>(uncurry wo_get_impl,uncurry mop_list_get) \<in> wo_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a elem_assn\<close>
      and set_hnr: \<open>(uncurry2 wo_set_impl,uncurry2 mop_list_set) \<in> [\<lambda>_.True]\<^sub>c wo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k \<rightarrow> wo_assn [\<lambda>((ai,_),_) r. r=ai]\<^sub>c\<close>
begin

  lemmas [sepref_fr_rules] = get_hnr set_hnr


  definition \<open>only_some_rel \<equiv> {(a, Some a) | a. True} \<union> {(x, None) | x. True}\<close>

  definition \<open>eo_assn \<equiv> hr_comp wo_assn (\<langle>only_some_rel\<rangle>list_rel)\<close>

  definition \<open>eo_extract1 p i \<equiv> doN { r \<leftarrow> mop_list_get p i; RETURN (r,p) }\<close>
  sepref_definition eo_extract_impl is \<open>uncurry eo_extract1\<close>
    :: \<open>wo_assn\<^sup>d *\<^sub>a (snat_assn' TYPE('size))\<^sup>k \<rightarrow>\<^sub>a elem_assn \<times>\<^sub>a wo_assn\<close>
    unfolding eo_extract1_def
    by sepref

  lemma mop_eo_extract_aux: \<open>mop_eo_extract p i = doN { r \<leftarrow> mop_list_get p i; ASSERT (r\<noteq>None \<and> i<length p); RETURN (the r, p[i:=None]) }\<close>
    by (auto simp: pw_eq_iff refine_pw_simps assert_true_bind_conv summarize_ASSERT_conv intro!: bind_cong arg_cong[of _ _ ASSERT])

  lemma assign_none_only_some_list_rel:
    assumes SR[param]: \<open>(a, a') \<in> \<langle>only_some_rel\<rangle>list_rel\<close> and L: \<open>i < length a'\<close>
      shows \<open>(a, a'[i := None]) \<in> \<langle>only_some_rel\<rangle>list_rel\<close>
  proof -
    have \<open>(a[i := a!i], a'[i := None]) \<in> \<langle>only_some_rel\<rangle>list_rel\<close>
      apply (parametricity)
      by (auto simp: only_some_rel_def)
    also from L list_rel_imp_same_length[OF SR] have \<open>a[i := a!i] = a\<close> by auto
    finally show ?thesis .
  qed


  lemma eo_extract1_refine: \<open>(eo_extract1, mop_eo_extract) \<in> \<langle>only_some_rel\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id \<times>\<^sub>r \<langle>only_some_rel\<rangle>list_rel\<rangle>nres_rel\<close>
    unfolding eo_extract1_def mop_eo_extract_aux
    supply R = mop_list_get.fref[THEN frefD, OF TrueI prod_relI, unfolded uncurry_apply, THEN nres_relD]
    apply (refine_rcg R)
    apply assumption
    apply (clarsimp simp: assign_none_only_some_list_rel)
    by (auto simp: only_some_rel_def)

  lemma eo_list_set_refine: \<open>(mop_list_set, mop_eo_set) \<in> \<langle>only_some_rel\<rangle>list_rel \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>\<langle>only_some_rel\<rangle>list_rel\<rangle>nres_rel\<close>
    unfolding mop_list_set_alt mop_eo_set_alt
    apply refine_rcg
    apply (simp add: list_rel_imp_same_length)
    apply simp
    apply parametricity
    apply (auto simp: only_some_rel_def)
    done


  lemma set_hnr': \<open>(uncurry2 wo_set_impl,uncurry2 mop_list_set) \<in> wo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k \<rightarrow>\<^sub>a wo_assn\<close>
    apply (rule hfref_cons[OF set_hnr])
    apply (auto simp: entails_lift_extract_simps sep_algebra_simps)
    done



  context
    notes [fcomp_norm_unfold] = eo_assn_def[symmetric]
  begin
    lemmas eo_extract_refine_aux = eo_extract_impl.refine[FCOMP eo_extract1_refine]

    lemma eo_extract_refine: "(uncurry eo_extract_impl, uncurry mop_eo_extract) 
      \<in> [\<lambda>_. True]\<^sub>c eo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k \<rightarrow> (elem_assn \<times>\<^sub>a eo_assn) [\<lambda>(ai,_) (_,r). r=ai]\<^sub>c"
      apply (sepref_to_hnr)
      apply (rule hn_refine_nofailI)
      apply (rule hnr_ceq_assnI)
      supply R = eo_extract_refine_aux[to_hnr, unfolded APP_def]
        apply (rule hn_refine_cons[OF _ R])
      subgoal by (auto simp: sep_algebra_simps entails_lift_extract_simps hn_ctxt_def pure_def invalid_assn_def)
      subgoal by (auto simp: sep_algebra_simps entails_lift_extract_simps hn_ctxt_def pure_def invalid_assn_def)
      subgoal by (auto simp: sep_algebra_simps entails_lift_extract_simps hn_ctxt_def pure_def invalid_assn_def)
      unfolding eo_extract_impl_def mop_eo_extract_def hn_ctxt_def eo_assn_def hr_comp_def
      apply (subst (3) sep.add_commute)
      supply R = get_hnr[to_hnr, THEN hn_refineD, unfolded APP_def hn_ctxt_def]
      thm R
      apply vcg
        supply [vcg_rules] = R
(*         supply [simp] = refine_pw_simps list_rel_imp_same_length *)
       apply (vcg)
        supply [simp] = refine_pw_simps list_rel_imp_same_length 
        apply vcg[]
       apply (auto simp: POSTCOND_def EXTRACT_def)
      apply (rule STATE_monoI)
       apply assumption
      apply (auto simp: entails_def)
      by (simp add: pure_true_conv)

    lemmas eo_set_refine_aux = set_hnr'[FCOMP eo_list_set_refine]

    (* TODO: Move *)
    lemma pure_entails_empty: \<open>is_pure A \<Longrightarrow> A a c \<turnstile> \<box>\<close>
      by (auto simp: is_pure_def sep_algebra_simps entails_lift_extract_simps)

    lemma eo_set_refine: \<open>(uncurry2 wo_set_impl, uncurry2 mop_eo_set) \<in> [\<lambda>_. True]\<^sub>c eo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a elem_assn\<^sup>d \<rightarrow> (eo_assn) [\<lambda>((ai,_),_) r. r=ai]\<^sub>c\<close>
      apply (sepref_to_hnr)
      apply (rule hn_refine_nofailI)
      apply (rule hnr_ceq_assnI)
      supply R = eo_set_refine_aux[to_hnr, unfolded APP_def]
      apply (rule hn_refine_cons[OF _ R])
      subgoal by (auto simp: sep_algebra_simps entails_lift_extract_simps hn_ctxt_def pure_def invalid_assn_def pure_entails_empty[OF pure])
      subgoal by (auto simp: sep_algebra_simps entails_lift_extract_simps hn_ctxt_def pure_def invalid_assn_def pure_entails_empty[OF pure])
      subgoal by (auto simp: sep_algebra_simps entails_lift_extract_simps hn_ctxt_def pure_def invalid_assn_def pure_entails_empty[OF pure])
      unfolding hn_ctxt_def eo_assn_def hr_comp_def
       supply R = set_hnr[to_hnr, THEN hn_refineD, unfolded APP_def hn_ctxt_def]
       supply [vcg_rules] = R
       apply (vcg)
       supply [simp] = refine_pw_simps list_rel_imp_same_length
       apply (vcg)[]
       apply (auto simp: POSTCOND_def EXTRACT_def)
      apply (rule STATE_monoI)
       apply assumption
      apply (auto simp: entails_def)
      by (simp add: pure_true_conv)

  end

  lemma id_Some_only_some_rel: \<open>(id, Some) \<in> Id \<rightarrow> only_some_rel\<close>
    by (auto simp: only_some_rel_def)

  lemma map_some_only_some_rel_iff: \<open>(xs, map Some ys) \<in> \<langle>only_some_rel\<rangle>list_rel \<longleftrightarrow> xs=ys\<close>
    apply (rule iffI)
    subgoal
      apply (induction xs \<open>map Some ys\<close> arbitrary: ys rule: list_rel_induct)
      apply (auto simp: only_some_rel_def)
      done
    subgoal
      apply (rewrite in \<open>(\<hole>,_)\<close> list.map_id[symmetric])
      apply (parametricity add: id_Some_only_some_rel)
      by simp
    done


  lemma wo_assn_conv: \<open>wo_assn xs ys = eo_assn (map Some xs) ys\<close>
    unfolding eo_assn_def hr_comp_def
    by (auto simp: pred_lift_extract_simps sep_algebra_simps fun_eq_iff map_some_only_some_rel_iff)

  lemma to_eo_conv_refine: \<open>(Mreturn, mop_to_eo_conv) \<in> [\<lambda>_. True]\<^sub>c wo_assn\<^sup>d \<rightarrow> (eo_assn) [\<lambda>(ai) (r). r=ai]\<^sub>c\<close>
    unfolding mop_to_eo_conv_def
    apply sepref_to_hoare
    apply (rewrite wo_assn_conv)
    apply vcg
    done

  lemma \<open>None \<notin> set xs \<longleftrightarrow> (\<exists>ys. xs = map Some ys)\<close>
    using None_not_in_set_conv by auto

  lemma to_wo_conv_refine: \<open>(Mreturn, mop_to_wo_conv) \<in>  [\<lambda>_. True]\<^sub>c eo_assn\<^sup>d \<rightarrow> (wo_assn) [\<lambda>(ai) (r). r=ai]\<^sub>c\<close>
    unfolding mop_to_wo_conv_def eo_assn_def hr_comp_def
    apply sepref_to_hoare
    apply (auto simp add: refine_pw_simps map_some_only_some_rel_iff elim!: None_not_in_set_conv)
    by vcg

  lemma random_access_iterator: "random_access_iterator wo_assn eo_assn elem_assn
    Mreturn Mreturn
    eo_extract_impl
    wo_set_impl"
    apply unfold_locales
    using to_eo_conv_refine to_wo_conv_refine eo_extract_refine eo_set_refine
    apply blast+
    done

  sublocale random_access_iterator wo_assn eo_assn elem_assn
    Mreturn Mreturn
    eo_extract_impl
    wo_set_impl
    by (rule random_access_iterator)

end

lemma is_pureE_abs:
  assumes "is_pure P"
  obtains P' where "P = (\<lambda>x x'. \<up>(P' x x'))"
  using assms unfolding is_pure_def by blast


lemma al_pure_eo: \<open>is_pure A \<Longrightarrow> pure_eo_adapter A (al_assn A) arl_nth arl_upd\<close>
  apply unfold_locales
    apply assumption
   apply (rule al_nth_hnr_mop; simp)
  subgoal
    apply (sepref_to_hnr)
    apply (rule hn_refine_nofailI)
    apply (rule hnr_ceq_assnI)
      supply R = al_upd_hnr_mop[to_hnr, unfolded APP_def, of A]
      apply (rule hn_refine_cons[OF _ R])
    subgoal by (auto simp: hn_ctxt_def pure_def invalid_assn_def sep_algebra_simps entails_lift_extract_simps)
    subgoal by (auto simp: hn_ctxt_def pure_def invalid_assn_def sep_algebra_simps entails_lift_extract_simps)
    subgoal by (auto simp: hn_ctxt_def pure_def invalid_assn_def sep_algebra_simps entails_lift_extract_simps)
    subgoal by (auto simp: hn_ctxt_def pure_def invalid_assn_def sep_algebra_simps entails_lift_extract_simps)
    unfolding hn_ctxt_def al_assn_def hr_comp_def pure_def in_snat_rel_conv_assn
      (*     apply (erule is_pureE) *)
     apply (erule is_pureE)
     apply (auto simp add: refine_pw_simps)[]
     apply vcg
     apply (rule wpa_monoI)
       apply (rule arl_upd_rule[unfolded htriple_def, rule_format])
       apply (rule STATE_monoI)
        apply assumption
       apply (auto simp flip: in_snat_rel_conv_assn simp: fri_basic_extract_simps
        dr_assn_pure_asm_prefix_def entails_def pred_lift_extract_simps
        SOLVE_AUTO_DEFER_def list_rel_imp_same_length)[]
      apply (simp add: POSTCOND_def EXTRACT_def)
      apply (subst(asm) sep_algebra_class.sep_conj_commute)
      apply (subst STATE_monoI)
        apply assumption
       apply (rule conj_entails_mono[OF frame_rem1])
       apply simp_all
    done
  done

end
