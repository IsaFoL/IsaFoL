theory IsaSAT_Bump_Heuristics
  imports Watched_Literals_VMTF
    IsaSAT_VMTF
    Tuple4
    IsaSAT_Bump_Heuristics_State
begin


section \<open>Bumping\<close>

(*TODO: FIXME missing bumping for ACIDS!*)

thm isa_vmtf_find_next_undef_def
  term isa_acids_find_next_undef
definition isa_acids_find_next_undef :: \<open>(nat, nat) acids \<Rightarrow> trail_pol \<Rightarrow> (nat option \<times> (nat, nat) acids) nres\<close> where
\<open>isa_acids_find_next_undef = (\<lambda>ac M. do {
  WHILE\<^sub>T\<^bsup>\<lambda>(L, ac). True\<^esup>
      (\<lambda>(nxt, ac). nxt = None \<and> acids_mset ac \<noteq> {#})
      (\<lambda>(a, ac). do {
         ASSERT (a = None);
         (L, ac) \<leftarrow> acids_pop_min ac;
         ASSERT (defined_atm_pol_pre M L);
         if defined_atm_pol M L then RETURN (None, ac)
         else RETURN (Some L, ac)
        }
      )
      (None, ac)
  })\<close>

lemma isa_acids_find_next_undef_acids_find_next_undef:
  \<open>(uncurry isa_acids_find_next_undef, uncurry (acids_find_next_undef \<A>)) \<in>
      Id \<times>\<^sub>r trail_pol \<A>  \<rightarrow>\<^sub>f \<langle>\<langle>nat_rel\<rangle>option_rel \<times>\<^sub>r Id\<rangle>nres_rel \<close>
proof -
  have [refine]: \<open>a=b\<Longrightarrow> acids_pop_min a \<le> \<Down> Id (acids_pop_min b)\<close>for a b
    by auto
  show ?thesis
  unfolding isa_acids_find_next_undef_def acids_find_next_undef_def uncurry_def
    defined_atm_def[symmetric]
  apply (intro frefI nres_relI)
  apply refine_rcg
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (rule defined_atm_pol_pre) (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
  subgoal
    by (auto simp: undefined_atm_code[THEN fref_to_Down_unRET_uncurry_Id])
  subgoal by auto
  subgoal by auto
  done
qed

definition vmtf_rescore_body
 :: \<open>nat multiset \<Rightarrow> nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> bump_heuristics \<Rightarrow>
    (nat \<times> bump_heuristics) nres\<close>
where
  \<open>vmtf_rescore_body \<A>\<^sub>i\<^sub>n C _ vm = do {
         WHILE\<^sub>T\<^bsup>\<lambda>(i, vm). i \<le> length C\<^esup>
           (\<lambda>(i, vm). i < length C)
           (\<lambda>(i, vm). do {
               ASSERT(i < length C);
               ASSERT(atm_of (C!i) \<in># \<A>\<^sub>i\<^sub>n);
               vm' \<leftarrow> isa_bump_mark_to_rescore (atm_of (C!i)) vm;
               RETURN(i+1, vm')
             })
           (0, vm)
    }\<close>

definition vmtf_rescore
 :: \<open>nat multiset \<Rightarrow> nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> bump_heuristics \<Rightarrow>
       (bump_heuristics) nres\<close>
where
  \<open>vmtf_rescore \<A>\<^sub>i\<^sub>n C M vm = do {
      (_, vm) \<leftarrow> vmtf_rescore_body \<A>\<^sub>i\<^sub>n C M vm;
      RETURN (vm)
   }\<close>

definition isa_bump_rescore_body
 :: \<open>nat clause_l \<Rightarrow> trail_pol \<Rightarrow> bump_heuristics \<Rightarrow>
    (nat \<times> bump_heuristics) nres\<close>
where
  \<open>isa_bump_rescore_body C _ vm = do {
         WHILE\<^sub>T\<^bsup>\<lambda>(i, vm). i \<le> length C\<^esup>
           (\<lambda>(i, vm). i < length C)
           (\<lambda>(i, vm). do {
               ASSERT(i < length C);
               vm' \<leftarrow> isa_bump_mark_to_rescore (atm_of (C!i)) vm;
               RETURN(i+1, vm')
             })
           (0, vm)
    }\<close>

definition isa_bump_rescore
 :: \<open>nat clause_l \<Rightarrow> trail_pol \<Rightarrow> bump_heuristics \<Rightarrow> bump_heuristics nres\<close>
where
  \<open>isa_bump_rescore C M vm = do {
      (_, vm) \<leftarrow> isa_bump_rescore_body C M vm;
      RETURN (vm)
    }\<close>

definition isa_rescore_clause
  :: \<open>nat multiset \<Rightarrow> nat clause_l \<Rightarrow> (nat,nat)ann_lits \<Rightarrow> bump_heuristics \<Rightarrow>
    bump_heuristics nres\<close>
where
  \<open>isa_rescore_clause \<A> C M vm = SPEC (\<lambda>(vm'). vm' \<in> bump_heur \<A> M)\<close>

lemma isa_bump_mark_to_rescore:
  assumes
    \<open>L \<in># \<A>\<close> \<open>b \<in> bump_heur \<A> M\<close> \<open>length (fst (get_bumped_variables b)) < Suc (Suc (unat32_max div 2))\<close>
  shows \<open>
     isa_bump_mark_to_rescore L b \<le> SPEC (\<lambda>vm'. vm' \<in> bump_heur \<A> M)\<close>
proof -
  have [simp]: \<open>(atoms_hash_insert L x, set (fst (atoms_hash_insert L x))) \<in> distinct_atoms_rel \<A>\<close>
    if \<open>(x, set (fst x)) \<in> distinct_atoms_rel \<A>\<close>
    for x
    unfolding distinct_atoms_rel_def
    apply (rule relcompI[of _ \<open>(fst (atoms_hash_insert L x), insert L (set (fst x)))\<close>])
    using that assms(1)
    by (auto simp: distinct_atoms_rel_def atoms_hash_rel_def atoms_hash_insert_def
        distinct_hash_atoms_rel_def split: if_splits)

  show ?thesis
    using assms
    unfolding isa_bump_mark_to_rescore_def
    apply (auto split: bump_heuristics_splits simp: atms_hash_insert_pre_def
      intro!: ASSERT_leI)
    apply (auto simp: bump_heur_def distinct_atoms_rel_def atoms_hash_rel_def atoms_hash_insert_def
      distinct_hash_atoms_rel_def intro: relcompI dest!: multi_member_split[of L])[]
     apply (auto simp: bump_heur_def intro:  dest!: multi_member_split[of L])
    done
qed

lemma length_get_bumped_variables_le:
  assumes \<open>vm \<in> bump_heur \<A> M\<close> \<open>isasat_input_bounded \<A>\<close>
  shows \<open>length (fst (get_bumped_variables vm)) < Suc (Suc (unat32_max div 2))\<close>
  using assms bounded_included_le[of \<A> \<open>fst (get_bumped_variables vm)\<close>]
  by (cases vm)
   (auto simp: bump_heur_def distinct_atoms_rel_def distinct_hash_atoms_rel_def
      atoms_hash_rel_def)

lemma vmtf_rescore_score_clause:
  \<open>(uncurry2 (vmtf_rescore \<A>), uncurry2 (isa_rescore_clause \<A>)) \<in>
     [\<lambda>((C, M), vm). literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C) \<and> vm \<in> bump_heur \<A> M \<and> isasat_input_bounded \<A>]\<^sub>f
     \<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have H: \<open>vmtf_rescore_body \<A> C M vm \<le>
        SPEC (\<lambda>(n :: nat, vm').  vm' \<in> bump_heur \<A> M)\<close>
    if M: \<open>vm \<in> bump_heur \<A> M\<close> and C: \<open>\<forall>c\<in>set C. atm_of c \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and
      bounded: \<open>isasat_input_bounded \<A>\<close>
    for C vm \<phi> M
    unfolding vmtf_rescore_body_def 
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(i, _). length C - i)\<close> and
       I' = \<open>\<lambda>(i, vm'). vm' \<in> bump_heur \<A> M\<close>] isa_bump_mark_to_rescore[where \<A>=\<A> and M=M])
    subgoal by auto
    subgoal by auto
    subgoal using C M by (auto simp: vmtf_def phase_saving_def)
    subgoal using C M by auto
    subgoal using C by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    subgoal using C by auto
    subgoal using C length_get_bumped_variables_le[OF _ bounded] by auto
    subgoal using C by auto
    subgoal using C by auto
    subgoal by auto
    done
  have K: \<open>((a, b),(a', b')) \<in> A \<times>\<^sub>f B \<longleftrightarrow> (a, a') \<in> A \<and> (b, b') \<in> B\<close> for a b a' b' A B
    by auto
  show ?thesis
    unfolding vmtf_rescore_def rescore_clause_def uncurry_def
    apply (intro frefI nres_relI)
    apply clarify
    apply (rule bind_refine_spec)
     prefer 2
     apply (subst (asm) K)
     apply (rule H; auto)
    subgoal
      by (meson atm_of_lit_in_atms_of contra_subsetD in_all_lits_of_m_ain_atms_of_iff
          in_multiset_in_set literals_are_in_\<L>\<^sub>i\<^sub>n_def)
    subgoal by (auto simp: isa_rescore_clause_def)
    done
qed


lemma isa_vmtf_rescore_body:
  \<open>(uncurry2 (isa_bump_rescore_body), uncurry2 (vmtf_rescore_body \<A>)) \<in> [\<lambda>_. isasat_input_bounded \<A>]\<^sub>f
     (Id \<times>\<^sub>f trail_pol \<A> \<times>\<^sub>f Id) \<rightarrow> \<langle>Id \<times>\<^sub>r Id\<rangle> nres_rel\<close>
proof -
  show ?thesis
    unfolding isa_bump_rescore_body_def vmtf_rescore_body_def uncurry_def
    apply (intro frefI nres_relI)
    apply refine_rcg
    subgoal by auto
    subgoal by auto
    subgoal for x y x1 x1a x1b x2 x2a x2b x1c x1d x1e x2c x1g x2g
      by (cases x2g) auto
    subgoal by auto
    apply (rule refine_IdI[OF eq_refl])
    subgoal by auto
    subgoal by auto
    done
qed

lemma isa_vmtf_rescore:
  \<open>(uncurry2 (isa_bump_rescore), uncurry2 (vmtf_rescore \<A>)) \<in> [\<lambda>_. isasat_input_bounded \<A>]\<^sub>f
     (Id \<times>\<^sub>f trail_pol \<A> \<times>\<^sub>f (Id)) \<rightarrow> \<langle>(Id)\<rangle> nres_rel\<close>
proof -
  show ?thesis
    unfolding isa_bump_rescore_def vmtf_rescore_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg isa_vmtf_rescore_body[THEN fref_to_Down_curry2])
    subgoal by auto
    subgoal by auto
    done
qed


(* TODO use in vmtf_mark_to_rescore_and_unset *)

definition vmtf_mark_to_rescore_clause where
\<open>vmtf_mark_to_rescore_clause \<A>\<^sub>i\<^sub>n arena C vm = do {
    ASSERT(arena_is_valid_clause_idx arena C);
    nfoldli
      ([C..<C + (arena_length arena C)])
      (\<lambda>_. True)
      (\<lambda>i vm. do {
        ASSERT(i < length arena);
        ASSERT(arena_lit_pre arena i);
        ASSERT(atm_of (arena_lit arena i) \<in># \<A>\<^sub>i\<^sub>n);
        isa_bump_mark_to_rescore (atm_of (arena_lit arena i)) vm
      })
      vm
  }\<close>

definition isa_bump_mark_to_rescore_clause where
\<open>isa_bump_mark_to_rescore_clause arena C vm = do {
    ASSERT(arena_is_valid_clause_idx arena C);
    nfoldli
      ([C..<C + (arena_length arena C)])
      (\<lambda>_. True)
      (\<lambda>i vm. do {
        ASSERT(i < length arena);
        ASSERT(arena_lit_pre arena i);
        isa_bump_mark_to_rescore (atm_of (arena_lit arena i)) vm
      })
      vm
  }\<close>

lemma isa_bump_mark_to_rescore_clause_vmtf_mark_to_rescore_clause:
  \<open>(uncurry2 isa_bump_mark_to_rescore_clause, uncurry2 (vmtf_mark_to_rescore_clause \<A>)) \<in> [\<lambda>_. isasat_input_bounded \<A>]\<^sub>f
    Id \<times>\<^sub>f nat_rel \<times>\<^sub>f (Id) \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding isa_bump_mark_to_rescore_clause_def vmtf_mark_to_rescore_clause_def
    uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg nfoldli_refine[where R = \<open>Id\<close> and S = Id])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for x y x1 x1a x2 x2a x1b x1c x2b x2c xi xa si s
    by (cases s)
      (auto simp: isa_vmtf_mark_to_rescore_pre_def
        intro!: atms_hash_insert_pre)
  done


lemma vmtf_mark_to_rescore_clause_spec:
  \<open>vm \<in> bump_heur \<A>  M \<Longrightarrow> valid_arena arena N vdom \<Longrightarrow> C \<in># dom_m N \<Longrightarrow> isasat_input_bounded \<A> \<Longrightarrow>
   (\<forall>C \<in> set [C..<C + arena_length arena C]. arena_lit arena C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<Longrightarrow>
    vmtf_mark_to_rescore_clause \<A> arena C vm \<le> RES (bump_heur \<A> M)\<close>
  unfolding vmtf_mark_to_rescore_clause_def
  apply (subst RES_SPEC_conv)
  apply (refine_vcg nfoldli_rule[where I = \<open>\<lambda>_ _ vm. vm \<in> bump_heur \<A> M\<close>])
  subgoal
    unfolding arena_lit_pre_def arena_is_valid_clause_idx_def
    apply (rule exI[of _ N])
    apply (rule exI[of _ vdom])
    apply (fastforce simp: arena_lifting)
    done
  subgoal for x it \<sigma>
    using arena_lifting(7)[of arena N vdom C \<open>x - C\<close>]
    by (auto simp: arena_lifting(1-6) dest!: in_list_in_setD)
  subgoal for x it \<sigma>
    unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
    apply (rule exI[of _ C])
    apply (intro conjI)
    apply (solves \<open>auto dest: in_list_in_setD\<close>)
    apply (rule exI[of _ N])
    apply (rule exI[of _ vdom])
    apply (fastforce simp: arena_lifting dest: in_list_in_setD)
    done
  subgoal for x it \<sigma>
    by fastforce
  subgoal for x it _ \<sigma>
    using length_get_bumped_variables_le[of _ \<A>]
    by (cases \<sigma>)
     (auto intro!: isa_bump_mark_to_rescore[THEN order_trans] simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
       dest: in_list_in_setD)
  done

definition vmtf_mark_to_rescore_also_reasons
  :: \<open>nat multiset \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> arena \<Rightarrow> nat literal list \<Rightarrow> nat literal \<Rightarrow> _ \<Rightarrow>_\<close> where
\<open>vmtf_mark_to_rescore_also_reasons \<A> M arena outl L vm = do {
    ASSERT(length outl \<le> unat32_max);
    nfoldli
      ([0..<length outl])
      (\<lambda>_. True)
      (\<lambda>i vm. do {
        ASSERT(i < length outl); ASSERT(length outl \<le> unat32_max);
        ASSERT(-outl ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>);
        if(outl!i = L)
        then
           RETURN vm
        else do {
          C \<leftarrow> get_the_propagation_reason M (-(outl ! i));
          case C of
            None \<Rightarrow> isa_bump_mark_to_rescore (atm_of (outl ! i)) vm
          | Some C \<Rightarrow> if C = 0 then RETURN vm else vmtf_mark_to_rescore_clause \<A> arena C vm}
      })
      vm
  }\<close>

definition isa_vmtf_mark_to_rescore_also_reasons
  :: \<open>trail_pol \<Rightarrow> arena \<Rightarrow> nat literal list \<Rightarrow> nat literal \<Rightarrow> _ \<Rightarrow>_\<close> where
\<open>isa_vmtf_mark_to_rescore_also_reasons M arena outl L vm = do {
    ASSERT(length outl \<le> unat32_max);
    nfoldli
      ([0..<length outl])
      (\<lambda>_. True)
      (\<lambda>i vm. do {
        ASSERT(i < length outl); ASSERT(length outl\<le> unat32_max);
        if(outl!i = L)
        then
          RETURN vm
        else do {
              C \<leftarrow> get_the_propagation_reason_pol M (-(outl ! i));
              case C of
                None \<Rightarrow> do {
                  isa_bump_mark_to_rescore (atm_of (outl ! i)) vm
                }
              | Some C \<Rightarrow> if C = 0 then RETURN vm else isa_bump_mark_to_rescore_clause arena C vm
            }
          })
      vm
  }\<close>

lemma isa_vmtf_mark_to_rescore_also_reasons_vmtf_mark_to_rescore_also_reasons:
  \<open>(uncurry4 isa_vmtf_mark_to_rescore_also_reasons, uncurry4 (vmtf_mark_to_rescore_also_reasons \<A>)) \<in>
    [\<lambda>_. isasat_input_bounded \<A>]\<^sub>f
  trail_pol \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding isa_vmtf_mark_to_rescore_also_reasons_def vmtf_mark_to_rescore_also_reasons_def
    uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg nfoldli_refine[where R = \<open>Id\<close> and S = Id]
    get_the_propagation_reason_pol[of \<A>, THEN fref_to_Down_curry]
     isa_bump_mark_to_rescore[of _ \<A>]
     isa_bump_mark_to_rescore_clause_vmtf_mark_to_rescore_clause[of \<A>, THEN fref_to_Down_curry2])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  apply assumption
  subgoal for x y x1 x1a _ _ _ x1b x2 x2a x2b x1c x1d x1e x2c x2d x2e xi xa si s xb x'
    by (cases xb)
     (auto simp: isa_vmtf_mark_to_rescore_pre_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        intro!: atms_hash_insert_pre[of _ \<A>])
  subgoal by auto
  subgoal by auto
  done

(* TODO remove (seems to be isa_bump_mark_to_rescore)
lemma vmtf_mark_to_rescore':
 \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<Longrightarrow> vm \<in> vmtf \<A> M \<Longrightarrow> isa_bump_mark_to_rescore L vm \<in> vmtf \<A> M\<close>
  by (cases vm) (auto intro: vmtf_mark_to_rescore)
*)
lemma vmtf_mark_to_rescore_also_reasons_spec:
  \<open>vm \<in> bump_heur \<A> M \<Longrightarrow> valid_arena arena N vdom \<Longrightarrow> length outl \<le> unat32_max \<Longrightarrow> isasat_input_bounded \<A> \<Longrightarrow>
   (\<forall>L \<in> set outl. L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<Longrightarrow>
   (\<forall>L \<in> set outl. \<forall>C. (Propagated (-L) C \<in> set M \<longrightarrow> C \<noteq> 0 \<longrightarrow> (C \<in># dom_m N \<and>
       (\<forall>C \<in> set [C..<C + arena_length arena C]. arena_lit arena C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>)))) \<Longrightarrow>
    vmtf_mark_to_rescore_also_reasons \<A> M arena outl L vm \<le> RES (bump_heur \<A> M)\<close>
  unfolding vmtf_mark_to_rescore_also_reasons_def
  apply (subst RES_SPEC_conv)
  apply (refine_vcg nfoldli_rule[where I = \<open>\<lambda>_ _ vm. vm \<in> bump_heur \<A> M\<close>]
    isa_bump_mark_to_rescore[of _ \<A>])
  subgoal by (auto dest: in_list_in_setD)
  subgoal for x l1 l2 \<sigma>
    unfolding all_set_conv_nth
    by (auto simp: uminus_\<A>\<^sub>i\<^sub>n_iff dest!: in_list_in_setD)
  subgoal for x l1 l2 \<sigma>
    unfolding get_the_propagation_reason_def
    apply (rule SPEC_rule)
    apply (rename_tac reason, case_tac reason; simp only: option.simps RES_SPEC_conv[symmetric])
    subgoal
      using length_get_bumped_variables_le[of _ \<A> M]
      by (auto intro!: isa_bump_mark_to_rescore[where M=M and \<A>=\<A>, THEN order_trans]
        simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[symmetric])
    apply (rename_tac D, case_tac \<open>D = 0\<close>; simp)
    subgoal
      by (rule vmtf_mark_to_rescore_clause_spec, assumption, assumption)
       fastforce+
    done
  done

definition vmtf_mark_to_rescore_also_reasons_cl
  :: \<open>nat multiset \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> arena \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> _ \<Rightarrow>_\<close> where
\<open>vmtf_mark_to_rescore_also_reasons_cl \<A> M arena C L vm = do {
    ASSERT(arena_is_valid_clause_idx arena C);
    nfoldli
      ([0..<arena_length arena C])
      (\<lambda>_. True)
      (\<lambda>i vm. do {
        K \<leftarrow> mop_arena_lit2 arena C i;
        ASSERT(-K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>);
        if(K = L)
        then
           RETURN vm
        else do {
          C \<leftarrow> get_the_propagation_reason M (-K);
          case C of
            None \<Rightarrow> isa_bump_mark_to_rescore (atm_of K) vm
          | Some C \<Rightarrow> if C = 0 then RETURN vm else vmtf_mark_to_rescore_clause \<A> arena C vm}
      })
      vm
  }\<close>

definition isa_vmtf_bump_to_rescore_also_reasons_cl
  :: \<open>trail_pol \<Rightarrow> arena \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> _ \<Rightarrow>_\<close> where
\<open>isa_vmtf_bump_to_rescore_also_reasons_cl M arena C L vm = do {
    ASSERT(arena_is_valid_clause_idx arena C);
    nfoldli
      ([0..<arena_length arena C])
      (\<lambda>_. True)
      (\<lambda>i vm. do {
         K \<leftarrow> mop_arena_lit2 arena C i;
        if(K = L)
        then
          RETURN vm
        else do {
              C \<leftarrow> get_the_propagation_reason_pol M (-K);
              case C of
                None \<Rightarrow> do {
                  isa_bump_mark_to_rescore (atm_of K) vm
                }
              | Some C \<Rightarrow> if C = 0 then RETURN vm else isa_bump_mark_to_rescore_clause arena C vm
            }
          })
      vm
  }\<close>

lemma isa_vmtf_bump_to_rescore_also_reasons_cl_vmtf_mark_to_rescore_also_reasons_cl:
  \<open>(uncurry4 isa_vmtf_bump_to_rescore_also_reasons_cl, uncurry4 (vmtf_mark_to_rescore_also_reasons_cl \<A>)) \<in>
    [\<lambda>_. isasat_input_bounded \<A>]\<^sub>f
  trail_pol \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f (Id) \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
proof -
  have H: \<open>f = g \<Longrightarrow> (f,g) \<in> Id\<close> for f g
    by auto
  show ?thesis
    unfolding isa_vmtf_bump_to_rescore_also_reasons_cl_def vmtf_mark_to_rescore_also_reasons_cl_def
      uncurry_def mop_arena_lit2_def
    apply (intro frefI nres_relI)
    apply (refine_rcg nfoldli_refine[where R = \<open>Id\<close> and S = Id]
      get_the_propagation_reason_pol[of \<A>, THEN fref_to_Down_curry]
       isa_bump_mark_to_rescore_clause_vmtf_mark_to_rescore_clause[of \<A>, THEN fref_to_Down_curry2])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply assumption
    subgoal for x y x1 x1a _ _ _ x1b x2 x2a x2b x1c x1d x1e x2c x2d x2e xi xa si s xb x'
      by (cases xb)
       (auto simp: isa_vmtf_mark_to_rescore_pre_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
          intro!: atms_hash_insert_pre[of _ \<A>])
    subgoal by auto
    subgoal by auto
    done
qed

(*TODO*)
lemma arena_lifting_list:
  \<open>valid_arena arena N vdom \<Longrightarrow> C \<in># dom_m N \<Longrightarrow>
  N \<propto> C = map (\<lambda>i. arena_lit arena (C+i)) [0..<arena_length arena C]\<close>
  by (subst list_eq_iff_nth_eq)
   (auto simp: arena_lifting)

lemma vmtf_mark_to_rescore_also_reasons_cl_spec:
  \<open>vm \<in> bump_heur \<A> M \<Longrightarrow> valid_arena arena N vdom \<Longrightarrow> C \<in># dom_m N \<Longrightarrow> isasat_input_bounded \<A> \<Longrightarrow>
    (\<forall>L \<in> set (N \<propto> C). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<Longrightarrow>
   (\<forall>L \<in> set (N \<propto> C). \<forall>C. (Propagated (-L) C \<in> set M \<longrightarrow> C \<noteq> 0 \<longrightarrow> (C \<in># dom_m N \<and>
       (\<forall>C \<in> set [C..<C + arena_length arena C]. arena_lit arena C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>)))) \<Longrightarrow>
    vmtf_mark_to_rescore_also_reasons_cl \<A> M arena C L vm \<le> RES (bump_heur \<A> M)\<close>
  unfolding vmtf_mark_to_rescore_also_reasons_cl_def mop_arena_lit2_def
  apply (subst RES_SPEC_conv)
  apply (refine_vcg nfoldli_rule[where I = \<open>\<lambda>_ _ vm. vm \<in> bump_heur \<A> M\<close>])
  subgoal by (auto simp: arena_is_valid_clause_idx_def)
  subgoal for x l1 l2 \<sigma> by (auto simp: arena_lit_pre_def arena_lifting
    arena_is_valid_clause_idx_and_access_def intro!: exI[of _ C] exI[of _ N]
    dest: in_list_in_setD)
  subgoal by (auto simp: arena_lifting arena_lifting_list image_image uminus_\<A>\<^sub>i\<^sub>n_iff)
  subgoal for x l1 l2 \<sigma>
    unfolding get_the_propagation_reason_def
    apply (rule SPEC_rule)
    apply (rename_tac reason, case_tac reason; simp only: option.simps RES_SPEC_conv[symmetric])
    subgoal
      using length_get_bumped_variables_le[of _ \<A>]
      by (auto intro!: isa_bump_mark_to_rescore[where \<A>=\<A> and M=M, THEN order_trans]
        simp: arena_lifting_list in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[symmetric])
    apply (rename_tac D, case_tac \<open>D = 0\<close>; simp)
    subgoal
      by (rule vmtf_mark_to_rescore_clause_spec, assumption, assumption)
        (auto simp: arena_lifting arena_lifting_list image_image uminus_\<A>\<^sub>i\<^sub>n_iff)
    done
  done


section \<open>Backtrack level for Restarts\<close>

hide_const (open) find_decomp_wl_imp

lemma isa_bump_unset_pre:
  assumes
    \<open>x \<in> bump_heur \<A> M\<close> and
    \<open>L \<in># \<A>\<close>
  shows \<open>isa_bump_unset_pre L x\<close>
  using assms vmtf_unset_pre_vmtf[where \<A>=\<A> and M=M and L=L]
    acids_tl[where  \<A>=\<A> and M=M and L=L]
  by (cases \<open>get_focused_heuristics x\<close>)
    (auto simp: isa_bump_unset_pre_def bump_heur_def acids_tl_pre_def
      atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n acids_def)

definition isa_acids_flush_int :: \<open>trail_pol \<Rightarrow> (nat, nat)acids \<Rightarrow> _ \<Rightarrow> ((nat, nat)acids \<times> _) nres\<close> where
\<open>isa_acids_flush_int  = (\<lambda>M vm (to_remove, h). do {
    ASSERT(length to_remove \<le> unat32_max);
    (_, vm, h) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, vm', h). i \<le> length to_remove\<^esup>
      (\<lambda>(i, vm, h). i < length to_remove)
      (\<lambda>(i, vm, h). do {
         ASSERT(i < length to_remove);
         vm \<leftarrow> acids_push_literal (to_remove!i) vm;
	 ASSERT(atoms_hash_del_pre (to_remove!i) h);
         RETURN (i+1, vm, atoms_hash_del (to_remove!i) h)})
      (0, vm, h);
    RETURN (vm, (emptied_list to_remove, h))
  })\<close>

lemma isa_acids_flush_int:
  \<open>(uncurry2 isa_acids_flush_int, uncurry2 (acids_flush_int \<A>)) \<in> trail_pol (\<A>::nat multiset) \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>Id\<times>\<^sub>f Id\<rangle>nres_rel\<close>
proof -
  have [refine]: \<open>x2c=x2 \<Longrightarrow> x2e=x2b \<Longrightarrow> ((0, x2c::(nat, nat)acids, x2e), 0, x2, x2b) \<in> nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id\<close>
    for x2c x2 x2e x2b
    by auto
  have [refine]: \<open>(a,a')\<in>Id\<Longrightarrow>(b,b')\<in>Id \<Longrightarrow> acids_push_literal a b \<le>\<Down>Id (acids_push_literal a' b')\<close> for a a' b b'
    by auto
  show ?thesis
    unfolding isa_acids_flush_int_def acids_flush_int_def uncurry_def
    apply (intro frefI nres_relI)
    apply refine_vcg
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition isa_acids_incr_score :: \<open>(nat, nat)acids \<Rightarrow> (nat, nat)acids\<close> where
  \<open>isa_acids_incr_score = (\<lambda>(a, m). (a, if m < unat64_max then m+1 else m))\<close>

lemma isa_acids_incr_score: \<open>ac \<in> acids \<A> M \<Longrightarrow> isa_acids_incr_score ac \<in> acids \<A> M\<close>
  by (auto simp: isa_acids_incr_score_def acids_def)

definition isa_bump_heur_flush where
  \<open>isa_bump_heur_flush M x = (case x of Tuple4 stabl focused foc bumped \<Rightarrow> do {
  (stable, bumped) \<leftarrow> (if foc then RETURN (stabl, bumped) else isa_acids_flush_int M (isa_acids_incr_score stabl) bumped);
  (focused, bumped) \<leftarrow> (if \<not>foc then RETURN (focused, bumped) else isa_vmtf_flush_int M focused bumped);
  RETURN (Tuple4 stable focused foc bumped)})\<close>



definition isa_bump_flush
   :: \<open>nat multiset \<Rightarrow> (nat,nat) ann_lits \<Rightarrow>  bump_heuristics \<Rightarrow> (bump_heuristics) nres\<close>
where
  \<open>isa_bump_flush \<A>\<^sub>i\<^sub>n = (\<lambda>M vm. SPEC (\<lambda>x. x \<in> bump_heur \<A>\<^sub>i\<^sub>n M))\<close>

lemma in_distinct_atoms_rel_in_atmsD: \<open>(ba, y) \<in> distinct_atoms_rel \<A> \<Longrightarrow>
  xa \<in> set (fst ba) \<Longrightarrow> xa \<in># \<A>\<close> and
  distinct_atoms_rel_emptiedI: \<open>((ae, baa), {}) \<in> distinct_atoms_rel \<A> \<Longrightarrow>
    ((ae, baa), set ae) \<in> distinct_atoms_rel \<A>\<close>
  by (auto simp: distinct_atoms_rel_def distinct_hash_atoms_rel_def)

lemma acids_change_to_remove_order':
  \<open>(uncurry2 (acids_flush_int \<A>\<^sub>i\<^sub>n), uncurry2 (acids_flush \<A>\<^sub>i\<^sub>n)) \<in>
   [\<lambda>((M, vm), to_r). vm \<in> acids \<A>\<^sub>i\<^sub>n M \<and> isasat_input_bounded \<A>\<^sub>i\<^sub>n \<and> isasat_input_nempty \<A>\<^sub>i\<^sub>n \<and> to_r \<subseteq> set_mset \<A>\<^sub>i\<^sub>n]\<^sub>f
     Id \<times>\<^sub>f Id \<times>\<^sub>f distinct_atoms_rel \<A>\<^sub>i\<^sub>n \<rightarrow> \<langle>(Id \<times>\<^sub>r distinct_atoms_rel \<A>\<^sub>i\<^sub>n)\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (use in \<open>auto intro!: acids_change_to_remove_order\<close>)

lemma isa_bump_heur_flush_isa_bump_flush:
  \<open>(uncurry (isa_bump_heur_flush), uncurry (isa_bump_flush \<A>))
\<in> [\<lambda>(M, vm). vm \<in> bump_heur \<A> M \<and> isasat_input_bounded \<A> \<and>
  isasat_input_nempty \<A>]\<^sub>f trail_pol \<A> \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding isa_bump_heur_flush_def isa_bump_flush_def uncurry_def
  apply (intro frefI nres_relI)
  apply (case_tac x, case_tac \<open>snd x\<close>, simp only: snd_conv case_prod_beta tuple4.case)
  apply refine_vcg
  subgoal by fast
  subgoal for x y a b x1 x2 x3 x4 aa ba
    apply (cases y)
    apply (auto split: bump_heuristics_splits simp: bump_heur_def vmtf_flush_def
      conc_fun_RES distinct_atoms_rel_emptiedI
      intro!: isa_vmtf_flush_int[where \<A>=\<A>, THEN fref_to_Down_curry2, of _ _ _ , THEN order_trans]
      vmtf_change_to_remove_order'[THEN fref_to_Down_curry2, of \<A> \<open>fst y\<close>, THEN order_trans]
      dest: in_distinct_atoms_rel_in_atmsD
      )
    apply (auto split: bump_heuristics_splits simp: bump_heur_def vmtf_flush_def
      conc_fun_RES distinct_atoms_rel_emptiedI
      intro!: isa_vmtf_flush_int[where \<A>=\<A>, THEN fref_to_Down_curry2, of _ _ _ , THEN order_trans]
      vmtf_change_to_remove_order'[THEN fref_to_Down_curry2, of \<A> \<open>fst y\<close>, THEN order_trans]
      dest: in_distinct_atoms_rel_in_atmsD
      )
    done
  subgoal for x y a b x1 x2 x3 x4
    apply (cases y)
    apply (auto split: bump_heuristics_splits simp: bump_heur_def vmtf_flush_def
      conc_fun_RES distinct_atoms_rel_emptiedI
      intro!: isa_acids_flush_int[where \<A>=\<A>, THEN fref_to_Down_curry2, of _ _ _ , THEN order_trans]
      acids_change_to_remove_order'[THEN fref_to_Down_curry2, of \<A> \<open>fst y\<close>, THEN order_trans]
      dest!: isa_acids_incr_score[of x1]
      dest: in_distinct_atoms_rel_in_atmsD
      )
    apply (auto split: bump_heuristics_splits simp: bump_heur_def acids_flush_def
      conc_fun_RES distinct_atoms_rel_emptiedI
      dest: in_distinct_atoms_rel_in_atmsD)
    done
  done

text \<open>
  We here find out how many decisions can be reused. Remark that since VMTF does not reuse many levels anyway,
  the implementation might be mostly useless, but I was not aware of that when I implemented it.
\<close>
(* TODO ded-uplicate definitions *)
definition find_decomp_w_ns_pre where
  \<open>find_decomp_w_ns_pre \<A> = (\<lambda>((M, highest), vm).
       no_dup M \<and>
       highest < count_decided M \<and>
       isasat_input_bounded \<A> \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M \<and>
       vm \<in> bump_heur \<A> M)\<close>

definition find_decomp_wl_imp
  :: \<open>nat multiset \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> nat \<Rightarrow> bump_heuristics \<Rightarrow>
       ((nat, nat) ann_lits \<times> bump_heuristics) nres\<close>
where
  \<open>find_decomp_wl_imp \<A> = (\<lambda>M\<^sub>0 lev vm. do {
    let k = count_decided M\<^sub>0;
    let M\<^sub>0 = trail_conv_to_no_CS M\<^sub>0;
    let n = length M\<^sub>0;
    pos \<leftarrow> get_pos_of_level_in_trail M\<^sub>0 lev;
    ASSERT((n - pos) \<le> unat32_max);
    ASSERT(n \<ge> pos);
    let target = n - pos;
    (_, M, vm') \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M, vm'). j \<le> target \<and>
           M = drop j M\<^sub>0 \<and> target \<le> length M\<^sub>0 \<and>
           vm' \<in> bump_heur \<A> M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset M)\<^esup>
         (\<lambda>(j, M, vm). j < target)
         (\<lambda>(j, M, vm). do {
            ASSERT (count_decided M > lev);
            ASSERT(M \<noteq> []);
            ASSERT(Suc j \<le> unat32_max);
            let L = atm_of (lit_of_hd_trail M);
            ASSERT(L \<in># \<A>);
            vm \<leftarrow>isa_bump_unset L vm;
            RETURN (j + 1, tl M, vm)
         })
         (0, M\<^sub>0, vm);
    ASSERT(lev = count_decided M);
    let M = trail_conv_back lev M;
    RETURN (M, vm')
  })\<close>

(*TODO: fix me, buggy in stable mode*)
definition isa_find_decomp_wl_imp
  :: \<open>trail_pol \<Rightarrow> nat \<Rightarrow> bump_heuristics \<Rightarrow> (trail_pol \<times> bump_heuristics) nres\<close>
where
  \<open>isa_find_decomp_wl_imp = (\<lambda>M\<^sub>0 lev vm. do {
    let k = count_decided_pol M\<^sub>0;
    let M\<^sub>0 = trail_pol_conv_to_no_CS M\<^sub>0;
    ASSERT(isa_length_trail_pre M\<^sub>0);
    let n = isa_length_trail M\<^sub>0;
    pos \<leftarrow> get_pos_of_level_in_trail_imp M\<^sub>0 lev;
    ASSERT((n - pos) \<le> unat32_max);
    ASSERT(n \<ge> pos);
    let target = n - pos;
    (_, M, vm') \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M, vm'). j \<le> target\<^esup>
         (\<lambda>(j, M, vm). j < target)
         (\<lambda>(j, M, vm). do {
            ASSERT(Suc j \<le> unat32_max);
            ASSERT(case M of (M, _) \<Rightarrow> M \<noteq> []);
            ASSERT(tl_trailt_tr_no_CS_pre M);
            let L = atm_of (lit_of_last_trail_pol M);
            ASSERT(isa_bump_unset_pre L vm);
            vm \<leftarrow> isa_bump_unset L vm;
            RETURN (j + 1, tl_trailt_tr_no_CS M, vm)
         })
         (0, M\<^sub>0, vm);
    M \<leftarrow> trail_conv_back_imp lev M;
    RETURN (M, vm')
  })\<close>


abbreviation find_decomp_w_ns_prop where
  \<open>find_decomp_w_ns_prop \<A> \<equiv>
     (\<lambda>(M::(nat, nat) ann_lits) highest _.
        (\<lambda>(M1, vm). \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = Suc highest \<and> vm \<in> bump_heur \<A> M1))\<close>

definition find_decomp_w_ns where
  \<open>find_decomp_w_ns \<A> =
     (\<lambda>(M::(nat, nat) ann_lits) highest vm.
        SPEC(find_decomp_w_ns_prop \<A> M highest vm))\<close>

lemma isa_find_decomp_wl_imp_find_decomp_wl_imp:
  \<open>(uncurry2 isa_find_decomp_wl_imp, uncurry2 (find_decomp_wl_imp \<A>)) \<in>
     [\<lambda>((M, lev), vm). lev < count_decided M]\<^sub>f trail_pol \<A> \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<rightarrow>
     \<langle>trail_pol \<A> \<times>\<^sub>r (Id)\<rangle>nres_rel\<close>
proof -
  have [intro]: \<open>(M', M) \<in> trail_pol \<A> \<Longrightarrow>  (M', M) \<in> trail_pol_no_CS \<A>\<close> for M' M
    by (auto simp: trail_pol_def trail_pol_no_CS_def control_stack_length_count_dec[symmetric])

  have loop_init[refine0]: \<open>\<And>x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa.
    case y of (x, xa) \<Rightarrow> (case x of (M, lev) \<Rightarrow> \<lambda>vm. lev < count_decided M) xa \<Longrightarrow>
    (x, y) \<in> trail_pol \<A> \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<Longrightarrow>
    x1 = (x1a, x2) \<Longrightarrow>
    y = (x1, x2a) \<Longrightarrow>
    x1b = (x1c, x2b) \<Longrightarrow>
    x = (x1b, x2c) \<Longrightarrow>
    isa_length_trail_pre (trail_pol_conv_to_no_CS x1c) \<Longrightarrow>
    (pos, posa) \<in> nat_rel \<Longrightarrow>
    length (trail_conv_to_no_CS x1a) - posa \<le> unat32_max \<Longrightarrow>
    posa \<le> length (trail_conv_to_no_CS x1a) \<Longrightarrow>
    isa_length_trail (trail_pol_conv_to_no_CS x1c) - pos \<le> unat32_max \<Longrightarrow>
    pos \<le> isa_length_trail (trail_pol_conv_to_no_CS x1c) \<Longrightarrow>
    case (0, trail_conv_to_no_CS x1a, x2a) of
    (j, M, vm') \<Rightarrow>
      j \<le> length (trail_conv_to_no_CS x1a) - posa \<and>
      M = drop j (trail_conv_to_no_CS x1a) \<and>
      length (trail_conv_to_no_CS x1a) - posa
      \<le> length (trail_conv_to_no_CS x1a) \<and>
      vm' \<in> bump_heur \<A> M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset M) \<Longrightarrow>
    ((0, trail_pol_conv_to_no_CS x1c, x2c), 0, trail_conv_to_no_CS x1a, x2a)
    \<in> nat_rel \<times>\<^sub>r trail_pol_no_CS \<A> \<times>\<^sub>r Id\<close>
    supply trail_pol_conv_to_no_CS_def[simp] trail_conv_to_no_CS_def[simp]
    by auto
  have trail_pol_empty: \<open>(([], x2g), M) \<in> trail_pol_no_CS \<A> \<Longrightarrow> M = []\<close> for M x2g
    by (auto simp: trail_pol_no_CS_def ann_lits_split_reasons_def)

(*
  have isa_vmtf: \<open>(x2c, x2a) \<in> Id \<Longrightarrow>
       (h, x2e) \<in> Id \<Longrightarrow>
       x2e \<in> bump_heur \<A> (drop x1d x1a) \<Longrightarrow>
       (h, baa, ca) \<in> bump_heur \<A> (drop x1d x1a)\<close>
       for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa xa x' x1d x2d x1e x2e x1f x2f
       x1g x1h x2g x2h aa ab ac ad ba baa ca h
       by (cases x2e)
        (auto 6 6 simp: Image_iff converse_iff prod_rel_iff
         intro!: bexI[of _ x2e])
*)
  have trail_pol_no_CS_last_hd:
    \<open>((x1h, t), M) \<in> trail_pol_no_CS \<A> \<Longrightarrow> M \<noteq> [] \<Longrightarrow> (last x1h) = lit_of (hd M)\<close>
    for x1h t M
    by (auto simp: trail_pol_no_CS_def ann_lits_split_reasons_def last_map last_rev)

  have trail_conv_back: \<open>trail_conv_back_imp x2b x1g
        \<le> SPEC
           (\<lambda>c. (c, trail_conv_back x2 x1e)
                \<in> trail_pol \<A>)\<close>
    if
      \<open>case y of (x, xa) \<Rightarrow> (case x of (M, lev) \<Rightarrow> \<lambda>vm. lev < count_decided M) xa\<close> and
      \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f nat_rel \<times>\<^sub>f Id\<close> and
      \<open>x1 = (x1a, x2)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1b = (x1c, x2b)\<close> and
      \<open>x = (x1b, x2c)\<close> and
      \<open>isa_length_trail_pre (trail_pol_conv_to_no_CS x1c)\<close> and
      \<open>(pos, posa) \<in> nat_rel\<close> and
      \<open>length (trail_conv_to_no_CS x1a) - posa \<le> unat32_max\<close> and
      \<open>isa_length_trail (trail_pol_conv_to_no_CS x1c) - pos \<le> unat32_max\<close> and
      \<open>(xa, x') \<in> nat_rel \<times>\<^sub>r trail_pol_no_CS \<A> \<times>\<^sub>r Id\<close> and
       \<open>x2d = (x1e, x2e)\<close> and
      \<open>x' = (x1d, x2d)\<close> and
      \<open>x2f = (x1g, x2g)\<close> and
      \<open>xa = (x1f, x2f)\<close> and
      \<open>x2 = count_decided x1e\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa xa x' x1d x2d x1e x2e x1f x2f
       x1g x2g
   apply (rule trail_conv_back[THEN fref_to_Down_curry, THEN order_trans])
   using that by (auto simp: conc_fun_RETURN)

 have bump: \<open>(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> isa_bump_unset a b \<le>\<Down>Id (isa_bump_unset a' b')\<close> for a a' b b'
   by auto
  show ?thesis
    supply [refine del] = refine(13)
    supply trail_pol_conv_to_no_CS_def[simp] trail_conv_to_no_CS_def[simp]
    unfolding isa_find_decomp_wl_imp_def find_decomp_wl_imp_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg bump
      id_trail_conv_to_no_CS[THEN fref_to_Down, unfolded comp_def]
      get_pos_of_level_in_trail_imp_get_pos_of_level_in_trail[of \<A>, THEN fref_to_Down_curry])
    subgoal
      by (rule isa_length_trail_pre) auto
    subgoal
      by (auto simp: get_pos_of_level_in_trail_pre_def)
    subgoal
      by auto
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
      apply (assumption+)[10]
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
    subgoal
      by auto
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
    subgoal
      by auto
    subgoal
      by (auto dest!: trail_pol_empty)
    subgoal for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa
      by (rule tl_trailt_tr_no_CS_pre) auto
    subgoal for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa xa x' x1d x2d x1e x2e x1f x2f
       x1g x1h x2g x2h
       by (cases x1g, cases x2h)
         (auto intro!: isa_bump_unset_pre[of _ \<A> \<open>drop x1d x1a\<close>]
         simp: lit_of_last_trail_pol_def trail_pol_no_CS_last_hd lit_of_hd_trail_def)
    subgoal
      by (auto simp: lit_of_last_trail_pol_def trail_pol_no_CS_last_hd lit_of_hd_trail_def
        intro!: tl_trail_tr_no_CS[THEN fref_to_Down_unRET]
          isa_vmtf_unset_vmtf_unset[THEN fref_to_Down_unRET_uncurry])
    subgoal
      by (auto simp: lit_of_last_trail_pol_def trail_pol_no_CS_last_hd lit_of_hd_trail_def
        intro!: tl_trail_tr_no_CS[THEN fref_to_Down_unRET]
          isa_vmtf_unset_vmtf_unset[THEN fref_to_Down_unRET_uncurry])
    subgoal
      by (auto simp: lit_of_last_trail_pol_def trail_pol_no_CS_last_hd lit_of_hd_trail_def
        intro!: tl_trail_tr_no_CS[THEN fref_to_Down_unRET]
          isa_vmtf_unset_vmtf_unset[THEN fref_to_Down_unRET_uncurry])
    apply (rule trail_conv_back; assumption)
    subgoal
      by auto
  done
qed


definition (in -) find_decomp_wl_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>find_decomp_wl_st = (\<lambda>L (M, N, D, oth).  do{
     M' \<leftarrow> find_decomp_wl' M (the D) L;
    RETURN (M', N, D, oth)
  })\<close>

definition find_decomp_wl_st_int :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>find_decomp_wl_st_int = (\<lambda>highest S. do{
     let M = get_trail_wl_heur S;
     let vm = get_vmtf_heur S;
     (M', vm) \<leftarrow> isa_find_decomp_wl_imp M highest vm;
     let S = set_trail_wl_heur M' S;
     let S = set_vmtf_wl_heur vm S;
     RETURN S
  })\<close>

lemma
  assumes
    vm: \<open>vm \<in> bump_heur \<A> M\<^sub>0\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<^sub>0\<close> and
    target: \<open>highest < count_decided M\<^sub>0\<close> and
    n_d: \<open>no_dup M\<^sub>0\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close> and
    count:\<open>count_decided M\<^sub>0 > 0\<close>
  shows
    find_decomp_wl_imp_le_find_decomp_wl':
      \<open>find_decomp_wl_imp \<A> M\<^sub>0 highest vm \<le> find_decomp_w_ns \<A> M\<^sub>0 highest vm\<close>
     (is ?decomp)
proof -
  have length_M0:  \<open>length M\<^sub>0 \<le> unat32_max div 2 + 1\<close>
    using length_trail_unat32_max_div2[of \<A> M\<^sub>0, OF bounded]
      n_d literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[of \<A>, OF lits]
    by (auto simp: lits_of_def)
  have 1: \<open>((count_decided x1g, x1g), count_decided x1, x1) \<in> Id\<close>
    if \<open>x1g = x1\<close> for x1g x1 :: \<open>(nat, nat) ann_lits\<close>
    using that by auto
  have [simp]: \<open>\<exists>M'a. M' @ x2g = M'a @ tl x2g\<close> for M' x2g :: \<open>(nat, nat) ann_lits\<close>
    by (rule exI[of _ \<open>M' @ (if x2g = [] then [] else [hd x2g])\<close>]) auto
  have butlast_nil_iff: \<open>butlast xs = [] \<longleftrightarrow> xs = [] \<or> (\<exists>a. xs = [a])\<close> for xs :: \<open>(nat, nat) ann_lits\<close>
    by (cases xs) auto
  have butlast1: \<open>tl x2g = drop (Suc (length x1) - length x2g) x1\<close> (is \<open>?G1\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> for x2g x1 :: \<open>'a list\<close>
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that zero_le)
    show ?G1
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  have butlast2: \<open>tl x2g = drop (length x1 - (length x2g - Suc 0)) x1\<close> (is \<open>?G2\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> and x2g: \<open>x2g \<noteq> []\<close> for x2g x1 :: \<open>'a list\<close>
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that(1) zero_le)
    have [simp]: \<open>Suc (length x1) - length x2g = length x1 - (length x2g - Suc 0)\<close>
      using x2g by auto
    show ?G2
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  note butlast = butlast1 butlast2

  have count_decided_not_Nil[simp]:  \<open>0 < count_decided M \<Longrightarrow> M \<noteq> []\<close> for M :: \<open>(nat, nat) ann_lits\<close>
    by auto
  have get_lev_last: \<open>get_level (M' @ M) (lit_of (last M')) = Suc (count_decided M)\<close>
    if \<open>M\<^sub>0 = M' @ M\<close> and \<open>M' \<noteq> []\<close> and \<open>is_decided (last M')\<close> for M' M
    apply (cases M' rule: rev_cases)
    using that apply (solves simp)
    using n_d that by auto

  have atm_of_N:
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset aa) \<Longrightarrow> aa \<noteq> [] \<Longrightarrow> atm_of (lit_of (hd aa)) \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    for aa
    by (cases aa) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have Lin_drop_tl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset (drop b M\<^sub>0)) \<Longrightarrow>
      literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset (tl (drop b M\<^sub>0)))\<close> for b
    apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mono)
     apply assumption
    by (cases \<open>drop b M\<^sub>0\<close>) auto

  have highest: \<open>highest = count_decided M\<close> and
     ex_decomp: \<open>\<exists>K M2.
       (Decided K # M, M2)
       \<in> set (get_all_ann_decomposition M\<^sub>0) \<and>
       get_level M\<^sub>0 K = Suc highest \<and> vm \<in> bump_heur \<A> M\<close>
    if
      pos: \<open>pos < length M\<^sub>0 \<and> is_decided (rev M\<^sub>0 ! pos) \<and> get_level M\<^sub>0 (lit_of (rev M\<^sub>0 ! pos)) =
         highest + 1\<close> and
      \<open>length M\<^sub>0 - pos \<le> unat32_max\<close> and
      inv: \<open>case s of (j, M, vm') \<Rightarrow>
         j \<le> length M\<^sub>0 - pos \<and>
         M = drop j M\<^sub>0 \<and>
         length M\<^sub>0 - pos \<le> length M\<^sub>0 \<and>
         vm' \<in> bump_heur \<A> M \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset M)\<close> and
      cond: \<open>\<not> (case s of
         (j, M, vm) \<Rightarrow> j < length M\<^sub>0 - pos)\<close> and
      s: \<open>s = (j, s')\<close> \<open>s' = (M, vm)\<close>
    for pos s j s' M vm
  proof -
    have
      \<open>j = length M\<^sub>0 - pos\<close> and
      M: \<open>M = drop (length M\<^sub>0 - pos) M\<^sub>0\<close> and
      vm: \<open>vm \<in> bump_heur \<A> (drop (length M\<^sub>0 - pos) M\<^sub>0)\<close> and
      \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset (drop (length M\<^sub>0 - pos) M\<^sub>0))\<close>
      using cond inv unfolding s
      by auto
    define M2 and L where \<open>M2 = take (length M\<^sub>0 - Suc pos) M\<^sub>0\<close> and \<open>L = rev M\<^sub>0 ! pos\<close>
    have le_Suc_pos: \<open>length M\<^sub>0 - pos = Suc (length M\<^sub>0 - Suc pos)\<close>
      using pos by auto
    have 1: \<open>take (length M\<^sub>0 - pos) M\<^sub>0 = take (length M\<^sub>0 - Suc pos) M\<^sub>0 @ [rev M\<^sub>0 ! pos]\<close>
      unfolding le_Suc_pos
      apply (subst take_Suc_conv_app_nth)
      using pos by (auto simp: rev_nth)
    have M\<^sub>0: \<open>M\<^sub>0 = M2 @ L # M\<close>
      apply (subst append_take_drop_id[symmetric, of _ \<open>length M\<^sub>0 - pos\<close>])
      unfolding M L_def M2_def 1
      by auto
    have L': \<open>Decided (lit_of L) = L\<close>
      using pos unfolding L_def[symmetric] by (cases L) auto
    then have M\<^sub>0': \<open>M\<^sub>0 = M2 @ Decided (lit_of L) # M\<close>
      unfolding M\<^sub>0 by auto

    have \<open>highest = count_decided M\<close> and \<open>get_level M\<^sub>0 (lit_of L) = Suc highest\<close> and \<open>is_decided L\<close>
      using n_d pos unfolding L_def[symmetric] unfolding M\<^sub>0
      by (auto simp: get_level_append_if split: if_splits)
    then show
     \<open>\<exists>K M2.
       (Decided K # M, M2)
       \<in> set (get_all_ann_decomposition M\<^sub>0) \<and>
       get_level M\<^sub>0 K = Suc highest \<and> vm \<in> bump_heur \<A> M\<close>
      using get_all_ann_decomposition_ex[of \<open>lit_of L\<close> M M2] vm unfolding M\<^sub>0'[symmetric] M[symmetric]
      by blast
    show \<open>highest = count_decided M\<close>
      using  \<open>highest = count_decided M\<close> .
  qed
  have count_dec_larger: \<open>highest < count_decided M\<close>
    if
      pos: \<open>pos < length M\<^sub>0 \<and> is_decided (rev M\<^sub>0 ! pos) \<and> get_level M\<^sub>0 (lit_of (rev M\<^sub>0 ! pos)) =
         highest + 1\<close> and
      \<open>length M\<^sub>0 - pos \<le> unat32_max\<close> and
      inv: \<open>case s of (j, M, vm') \<Rightarrow>
         j \<le> length M\<^sub>0 - pos \<and>
         M = drop j M\<^sub>0 \<and>
         length M\<^sub>0 - pos \<le> length M\<^sub>0 \<and>
         vm' \<in> bump_heur \<A> M \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset M)\<close> and
      cond: \<open>(case s of
         (j, M, vm) \<Rightarrow> j < length M\<^sub>0 - pos)\<close> and
      s: \<open>s = (j, s')\<close> \<open>s' = (M, vm)\<close>
    for pos s j s' M vm
  proof -
    define M2 and L where \<open>M2 = take (length M\<^sub>0 - Suc pos) M\<^sub>0\<close> and \<open>L = rev M\<^sub>0 ! pos\<close>
    have le_Suc_pos: \<open>length M\<^sub>0 - pos = Suc (length M\<^sub>0 - Suc pos)\<close>
      using pos by auto
    have 1: \<open>take (length M\<^sub>0 - pos) M\<^sub>0 = take (length M\<^sub>0 - Suc pos) M\<^sub>0 @ [rev M\<^sub>0 ! pos]\<close>
      unfolding le_Suc_pos
      apply (subst take_Suc_conv_app_nth)
      using pos by (auto simp: rev_nth)
    have \<open>L \<in> set M\<close>
      using that inv L_def apply auto
      by (metis bot_nat_0.not_eq_extremum diff_Suc_less in_set_dropI le_Suc_pos minus_eq nat.simps(3) nat_Suc_less_le_imp rev_nth)
    moreover have \<open>count_decided M \<ge> get_level M (lit_of L)\<close>
      using count_decided_ge_get_level by blast
    moreover have \<open>get_level M\<^sub>0 (lit_of L) = Suc highest\<close> and \<open>is_decided L\<close>
      using n_d pos unfolding L_def[symmetric]
      by (auto simp: get_level_append_if split: if_splits)
    moreover have \<open>get_level M\<^sub>0 (lit_of L) = get_level M (lit_of L)\<close>
      using n_d
      apply (subst append_take_drop_id[symmetric, of M\<^sub>0 j], subst (asm)append_take_drop_id[symmetric, of M\<^sub>0 j])
      using that \<open>L \<in> set M\<close> apply (auto simp del: append_take_drop_id simp: get_level_append_if
        dest: defined_lit_no_dupD undefined_notin)
      using defined_lit_no_dupD(1) undefined_notin by blast
    ultimately show ?thesis
      by auto
  qed
find_theorems isa_bump_unset bump_heur
  show ?decomp
    unfolding find_decomp_wl_imp_def Let_def find_decomp_w_ns_def trail_conv_to_no_CS_def
      get_pos_of_level_in_trail_def trail_conv_back_def
    apply (refine_vcg 1 WHILEIT_rule[where R=\<open>measure (\<lambda>(_, M, _). length M)\<close>]
      isa_bump_unset_vmtf_tl[unfolded lit_of_hd_trail_def[symmetric], of _ \<A>, THEN order_trans])
    subgoal using length_M0 unfolding unat32_max_def by simp
    subgoal by auto
    subgoal by auto
    subgoal using target by (auto simp: count_decided_ge_get_maximum_level)
    subgoal by auto
    subgoal by auto
    subgoal using vm by auto
    subgoal using lits unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_trail_lit_of_mset by auto
    subgoal by (rule count_dec_larger)
    subgoal for target s j b M vm by simp
    subgoal using length_M0 unfolding unat32_max_def by simp
    subgoal for x s a ab aa bb
      by (cases \<open>drop a M\<^sub>0\<close>)
        (auto simp: lit_of_hd_trail_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal by auto
    subgoal by (auto simp: drop_Suc drop_tl atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    subgoal by auto
    subgoal for s a b aa ba vm x2 x1a x2a
      using target
      by (cases vm)
        (auto intro!: isa_bump_unset_vmtf_tl atm_of_N drop_tl simp: lit_of_hd_trail_def)
    subgoal for s a b aa ba x1 x2 x1a x2a
      using lits by (auto intro: Lin_drop_tl simp: drop_Suc tl_drop)
    subgoal by auto
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a
      using lits by (auto intro: Lin_drop_tl)
    subgoal by auto
    subgoal by (rule highest)
    subgoal by (rule ex_decomp) (assumption+, auto)
    done
qed


lemma find_decomp_wl_imp_find_decomp_wl':
  \<open>(uncurry2 (find_decomp_wl_imp \<A>), uncurry2 (find_decomp_w_ns \<A>)) \<in>
    [find_decomp_w_ns_pre \<A>]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: find_decomp_w_ns_pre_def simp del: twl_st_of_wl.simps
       intro!: find_decomp_wl_imp_le_find_decomp_wl')

lemma find_decomp_wl_imp_code_conbine_cond:
  \<open>(\<lambda>((b, a), c). find_decomp_w_ns_pre \<A> ((b, a), c) \<and> a < count_decided b) = (\<lambda>((b, a), c).
         find_decomp_w_ns_pre \<A> ((b, a), c))\<close>
  by (auto intro!: ext simp: find_decomp_w_ns_pre_def)

end
