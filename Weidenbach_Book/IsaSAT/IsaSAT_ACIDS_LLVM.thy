theory IsaSAT_ACIDS_LLVM
  imports IsaSAT_Literals_LLVM
    IsaSAT_ACIDS
    Pairing_Heaps_Impl_LLVM
    IsaSAT_Trail_LLVM
begin

definition acids_assn2 where
  \<open>acids_assn2 = acids_assn \<times>\<^sub>a uint64_nat_assn\<close>

sepref_register ACIDS.mop_prio_insert_unchanged ACIDS.mop_prio_insert_raw_unchanged
sepref_def mop_prio_insert_raw_unchanged_impl
  is \<open>uncurry ACIDS.mop_prio_insert_raw_unchanged\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a acids_assn\<^sup>d \<rightarrow>\<^sub>a acids_assn\<close>
  unfolding ACIDS.mop_prio_insert_raw_unchanged_def
  by sepref

sepref_def mop_prio_insert_unchanged_impl
  is \<open>uncurry ACIDS.mop_prio_insert_unchanged\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a acids_assn\<^sup>d \<rightarrow>\<^sub>a acids_assn\<close>
  unfolding ACIDS.mop_prio_insert_unchanged_def
  by sepref

definition mop_imp_decreases_weights_rescaling_only :: \<open>'b :: {ord,divide,zero} \<Rightarrow> ('a,'b)pairing_heaps_imp \<Rightarrow> (('a,'b)pairing_heaps_imp) nres\<close> where
 \<open>mop_imp_decreases_weights_rescaling_only a = (\<lambda>(prevs', nxts', children', parents', scores', h'). do {
   do {
     let l = length scores';
     ASSERT (a > 0);
     (_, i, scores') \<leftarrow> WHILE\<^sub>T\<^bsup>(\<lambda>(finished, i, xs).
           (\<not>finished \<longrightarrow> i < l \<and> xs = take i (map (\<lambda>x. x div a) scores') @ drop i scores') \<and> 
           (finished \<longrightarrow> (i = l - 1 \<or> l = 0) \<and> xs = (map (\<lambda>x. x div a) scores'))
            )\<^esup>
       (\<lambda>(finished, i, xs). \<not>finished)
       (\<lambda>(finished, i, xs). do { ASSERT (\<not>finished); ASSERT (l > 0); let finished = (i = l - 1) in RETURN (finished, if finished then i else Suc i, xs[i := xs ! i div a])})
       (l = 0, 0, scores');
     RETURN (prevs', nxts', children', parents', scores', h')
  }
  })\<close>

sepref_def mop_imp_decreases_weights_rescaling_only_code
  is \<open>uncurry mop_imp_decreases_weights_rescaling_only\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a (hp_assn)\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_imp_decreases_weights_rescaling_only_def hp_assn_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemmas [sepref_fr_rules] = mop_imp_needs_rescaling_code.refine[FCOMP mop_imp_needs_rescaling_mop_hp_needs_rescaling]

sepref_def mop_imp_decrease_weights_code
  is \<open>uncurry mop_imp_decreases_weights\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a (hp_assn)\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_imp_decreases_weights_def
  by sepref

sepref_def acids_tl_impl
  is \<open>uncurry acids_tl\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a acids_assn2\<^sup>d \<rightarrow>\<^sub>a acids_assn2\<close>
  unfolding acids_assn2_def acids_tl_def max_def
  by sepref

sepref_def acids_pop_min_impl
  is acids_pop_min
  :: \<open>acids_assn2\<^sup>d \<rightarrow>\<^sub>a atom_assn \<times>\<^sub>a acids_assn2\<close>
  unfolding acids_pop_min_def acids_assn2_def
  by sepref

term ACIDS.mop_prio_insert_maybe

sepref_register ACIDS.mop_prio_insert_maybe
sepref_def mop_prio_insert_maybe_impl
  is \<open>uncurry2 (PR_CONST ACIDS.mop_prio_insert_maybe)\<close>
  ::  \<open>atom_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a acids_assn\<^sup>d \<rightarrow>\<^sub>a acids_assn\<close>
  unfolding ACIDS.mop_prio_insert_maybe_def PR_CONST_def
  by sepref

definition mop_imp_change_all_weights_with_max where
  \<open>mop_imp_change_all_weights_with_max = (\<lambda>old (xs, m). do {
    rescaling \<leftarrow> Pairing_Heaps_Impl.mop_imp_needs_rescaling xs old;
    if \<not>rescaling then RETURN (xs, m)
    else do {
     xs \<leftarrow> mop_imp_decreases_weights_only old xs;
     RETURN (xs, m div old)
    }
  })\<close>

lemma mop_imp_decreases_weights_only_spec:
  \<open>((old, xsm), old', ysm')
    \<in> nat_rel \<times>\<^sub>f
       (\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel O
        acids_encoded_hmrel \<times>\<^sub>f
        nat_rel) \<Longrightarrow>
    0 < old' \<Longrightarrow>
    x2 = (x1b, x2a) \<Longrightarrow>
    x1 = (x1a, x2) \<Longrightarrow>
    ysm' = (x1, x2b) \<Longrightarrow>
    xsm = (x1c, x2c) \<Longrightarrow>
    (\<forall>x\<in>#fst (snd x1). (snd (snd (fst ysm'))) x \<le> x2c) \<Longrightarrow>
    mop_imp_decreases_weights_only old x1c
    \<le> \<Down> {(a,b). (a,b) \<in> (\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel O
        acids_encoded_hmrel) \<and>
       (snd (snd b)) = (\<lambda>x. (\<lambda>x. x div old) (snd (snd (fst ysm')) x)) \<and>
       ((\<forall>x\<in>#fst (snd b). (snd (snd b)) x \<le> x2c div old')) \<and>
       fst (b) = fst (x1) \<and>
       fst (snd b) = fst (snd x1)}
        (Refine_Basic.SPEC
          (\<lambda>uu::nat multiset \<times> nat multiset \<times> (nat \<Rightarrow> nat).
              \<exists>(w'::nat \<Rightarrow> nat) (\<A>'::nat multiset) \<B>'::nat multiset.
                 uu = (\<A>', \<B>', w') \<and> x1a = \<A>' \<and> x1b = \<B>'))\<close>
  apply auto
  subgoal for a aa ab ac ad b ae af ag ah ai ba bb
  apply (rule order_trans)
   apply (rule mop_imp_decreases_weights_only_mop_hp_decreases_weights_only[of _ \<open>(ae, (af, ag, ah, ai, ba), bb)\<close> ])
      apply (auto simp: mop_hp_decreases_weights_only_def conc_fun_RETURN conc_fun_RES
        intro: ACIDS.ordered)
    apply (rule_tac b = \<open>(ae,
        (af, ag, ah, ai, \<lambda>x. map_option (\<lambda>x. x div old') (ba x)), bb)\<close> in relcompI)
    apply (auto simp: acids_encoded_hmrel_def)
    apply (rule_tac b = \<open>(aja, map_option (hp_rescale_weight old') bca)\<close> in relcompI)
     apply (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def ACIDS.hmrel_def
        intro!: ACIDS.invar_hp_rescale_weight intro: div_le_mono
        split: option.splits)
    by (metis hp_node_None_notin2 option.map_sel score_hp_rescale_weights_hp_node)
  done

lemma (in hmstruct_with_prio) mop_hm_change_all_weights_with_max_alt_def:
\<open>mop_hm_change_all_weights_with_max = (\<lambda>old ((\<A>, \<B>, w), m). do {
  ASSERT (\<forall>x\<in>#\<B>. w x \<le> m);
  rescaling \<leftarrow> SPEC (\<lambda>_. True);
  if \<not>rescaling then RETURN ((\<A>, \<B>, w), m)
  else do {
     (\<A>, \<B>, w') \<leftarrow> RES {(\<A>', \<B>', w')|w' \<A>' \<B>'. \<A> = \<A>' \<and> \<B> = \<B>'}; 
     m \<leftarrow> SPEC (\<lambda>m. (\<forall>x\<in>#\<B>. w' x \<le> m) \<and> m \<ge> 0);
    RETURN ((\<A>, \<B>, w'), m)
  }})\<close>
  unfolding mop_hm_change_all_weights_with_max_def RES_RES_RETURN_RES RES_RETURN_RES RES_RES3_RETURN_RES
  by (force intro!: ext bind_cong[OF refl])


lemma mop_imp_change_all_weights_with_max_mop_hm_change_all_weights_with_max:
  assumes \<open>((old, xsm), (old', ysm')) \<in> nat_rel \<times>\<^sub>f (\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel O  acids_encoded_hmrel  \<times>\<^sub>f nat_rel)\<close> and
   \<open>old' > 0\<close>
  shows \<open>mop_imp_change_all_weights_with_max old (xsm) \<le> 
    \<Down>((\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel O  acids_encoded_hmrel) \<times>\<^sub>f nat_rel)
      (ACIDS.mop_hm_change_all_weights_with_max old' (ysm'))\<close>
  using assms
  unfolding mop_imp_change_all_weights_with_max_def ACIDS.mop_hm_change_all_weights_with_max_alt_def
    Pairing_Heaps_Impl.mop_imp_needs_rescaling_def
  apply (refine_vcg mop_imp_decreases_weights_only_mop_hp_decreases_weights_only
      mop_imp_decreases_weights_only_spec)
  subgoal by auto
  subgoal by auto
  apply assumption+
  subgoal by auto
  subgoal for x1 x1a x2 x1b x2a x2b x1c x2c no_rescaling no_rescalinga
    by (auto simp: conc_fun_RETURN conc_fun_RES RES_RETURN_RES Image_def)
  done

lemma mop_imp_change_all_weights_with_max_mop_hm_change_all_weights_with_max2:               
  shows \<open>(uncurry mop_imp_change_all_weights_with_max, uncurry ACIDS.mop_hm_change_all_weights_with_max) \<in>
   [\<lambda>(b,_). b > 0]\<^sub>f nat_rel \<times>\<^sub>f (\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel O acids_encoded_hmrel \<times>\<^sub>f nat_rel) \<rightarrow>
    \<langle>\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel O acids_encoded_hmrel \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
  unfolding uncurry_def
  apply (intro frefI nres_relI, (subst case_prod_beta)+)
  subgoal for a b
    by (rule order_trans, rule mop_imp_change_all_weights_with_max_mop_hm_change_all_weights_with_max[of \<open>fst a\<close> \<open>snd a\<close> \<open>fst b\<close> \<open>snd b\<close>])
      auto
  done

sepref_def mop_imp_change_all_weights_with_max_code
  is \<open>uncurry mop_imp_change_all_weights_with_max\<close>
  :: \<open>[\<lambda>(a, _). a > 0]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a (hp_assn \<times>\<^sub>a uint64_nat_assn)\<^sup>d \<rightarrow> hp_assn \<times>\<^sub>a uint64_nat_assn\<close>
  unfolding mop_imp_change_all_weights_with_max_def
  by sepref

sepref_register ACIDS.mop_hm_change_all_weights_with_max

lemmas [sepref_fr_rules] =
   mop_imp_change_all_weights_with_max_code.refine[FCOMP mop_imp_change_all_weights_with_max_mop_hm_change_all_weights_with_max2,
    unfolded hr_comp_assoc[symmetric] acids_assn_def[symmetric]]

lemma pow2_40: \<open>(2::nat) ^ 40 = 1099511627776\<close>
  by auto

sepref_def acids_push_literal_impl
  is \<open>uncurry acids_push_literal\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a acids_assn2\<^sup>d \<rightarrow>\<^sub>a acids_assn2\<close>
  unfolding acids_push_literal_def acids_assn2_def max_def
    min_def pow2_40
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

definition bottom_acids0 :: \<open>_\<close> where
  \<open>bottom_acids0 = ((replicate 0 None, replicate 0 None, replicate 0 None, replicate 0 None, replicate 0 0, None))\<close>

definition bottom_acids :: \<open>_\<close> where
  \<open>bottom_acids = (bottom_acids0, None)\<close>

sepref_def bottom_acids0_impl
  is \<open>uncurry0 (RETURN bottom_acids0)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding bottom_acids0_def
  apply (rewrite at \<open>(_, _, _, _, replicate 0 \<hole> , _)\<close>
    unat_const_fold[where 'a=64])
  apply (rewrite in \<open>(_, _, _, _, \<hole>, _)\<close> larray_fold_custom_replicate)
  unfolding hp_assn_def atom.fold_option array_fold_custom_replicate
    al_fold_custom_empty[where 'l=64]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition empty_acids0 where
  \<open>empty_acids0 = ({#}, {#}, \<lambda>_::nat. 0::nat)\<close>


definition empty_acids where
  \<open>empty_acids = (empty_acids0, 0)\<close>

lemma bottom_acids0:
  \<open>(uncurry0 (RETURN bottom_acids0), uncurry0 (RETURN empty_acids0)) \<in> 
   unit_rel \<rightarrow>\<^sub>f \<langle>((\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel)) O
   acids_encoded_hmrel\<rangle>nres_rel\<close>
proof -
  have [intro!]: \<open>Me \<in># {#} \<Longrightarrow> False\<close>for Me
    by auto
  have 1: \<open>(({#}, (\<lambda>_. None, \<lambda>_. None, \<lambda>_. None, \<lambda>_. None, \<lambda>_. None), None), empty_acids0) \<in> acids_encoded_hmrel\<close>
    by (auto simp: acids_encoded_hmrel_def bottom_acids0_def pairing_heaps_rel_def map_fun_rel_def
      ACIDS.hmrel_def encoded_hp_prop_list_conc_def encoded_hp_prop_def empty_outside_def empty_acids0_def
      intro!: relcompI)

  show ?thesis
    unfolding uncurry0_def
    apply (intro frefI nres_relI)
    apply (auto intro!:  relcompI[OF _ 1])
    by(auto simp: acids_encoded_hmrel_def bottom_acids0_def pairing_heaps_rel_def map_fun_rel_def
      ACIDS.hmrel_def encoded_hp_prop_list_conc_def encoded_hp_prop_def empty_outside_def)
qed

lemmas [sepref_fr_rules] =
  bottom_acids0_impl.refine[FCOMP bottom_acids0, unfolded hr_comp_assoc[symmetric] acids_assn_def[symmetric]]

sepref_def empty_acids_code
  is \<open>uncurry0 (RETURN empty_acids)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a acids_assn2\<close>
  unfolding empty_acids_def acids_assn2_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

schematic_goal free_acids_assn[sepref_frame_free_rules]: \<open>MK_FREE acids_assn ?a\<close>
  unfolding acids_assn_def hp_assn_def
  by synthesize_free


schematic_goal free_acids_assn2[sepref_frame_free_rules]: \<open>MK_FREE acids_assn2 ?a\<close>
  unfolding acids_assn2_def
  by synthesize_free

sepref_def free_acids
  is \<open>mop_free\<close>
  :: \<open>acids_assn2\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_acids_assn2': \<open>MK_FREE acids_assn2 free_acids\<close>
  unfolding free_acids_def
  by (rule back_subst[of \<open>MK_FREE acids_assn2\<close>, OF free_acids_assn2])
    (auto intro!: ext)

end
