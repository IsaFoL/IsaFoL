theory IsaSAT_Backtrack
  imports IsaSAT_Setup Watched_Literals_Heuristics IsaSAT_VMTF
begin
subsection \<open>Backtrack\<close>

context isasat_input_bounded_nempty
begin


subsubsection \<open>Backtrack with direct extraction of literal if highest level\<close>


definition (in -) empty_conflict_and_extract_clause
  :: \<open>(nat,nat) ann_lits \<Rightarrow> nat clause \<Rightarrow> nat clause_l \<Rightarrow>
        (nat clause option \<times> nat clause_l \<times> nat) nres\<close>
where
  \<open>empty_conflict_and_extract_clause M D outl =
     SPEC(\<lambda>(D, C, n). D = None \<and> mset C = mset outl \<and> C!0 = outl!0 \<and>
       (length C > 1 \<longrightarrow> highest_lit M (mset (tl C)) (Some (C!1, get_level M (C!1)))) \<and>
       (length C > 1 \<longrightarrow> n = get_level M (C!1)) \<and>
       (length C = 1 \<longrightarrow> n = 0)
      )\<close>

definition empty_conflict_and_extract_clause_heur where
  \<open>empty_conflict_and_extract_clause_heur M D outl = do {
     let C = replicate (length outl) (outl!0);
     (D, C, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(E, C, i). mset (take i C) = mset (take i outl) \<and> E = D - mset (take i outl) \<and>
            length C = length outl \<and> C ! 0 = outl ! 0 \<and> i \<ge> 1 \<and> i \<le> length outl \<and>
            (1 < length (take i C) \<longrightarrow>
                 highest_lit M (mset (tl (take i C)))
                  (Some (C ! 1, get_level M (C ! 1))))\<^esup>
         (\<lambda>(D, C, i). i < length_u outl)
         (\<lambda>(D, C, i). do {
           ASSERT(i < length outl);
           ASSERT(i < length C);
           ASSERT(delete_from_lookup_conflict_pre (outl ! i, D));
           let D = remove1_mset (outl ! i) D;
           let C = C[i := outl ! i];
           ASSERT(C!i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> C!1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
           let C = (if get_level M (C!i) > get_level M (C!one_uint32_nat) then swap C one_uint32_nat i else C);
           ASSERT(i+1 \<le> uint_max);
           RETURN (D, C, i+one_uint32_nat)
         })
        (D, C, one_uint32_nat);
     ASSERT(D = {#});
     ASSERT(length outl \<noteq> 1 \<longrightarrow> length C > 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow> C!1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
     RETURN (set_empty_conflict_to_none D, C, if length outl = 1 then zero_uint32_nat else get_level M (C!1))
    }\<close>

lemma empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause:
  assumes
    \<open>D = mset (tl outl)\<close> \<open>outl \<noteq> []\<close> and dist: \<open>distinct outl\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset outl)\<close> and
    consistent: \<open>\<not> tautology (mset outl)\<close>
  shows
    \<open>empty_conflict_and_extract_clause_heur M D outl \<le> empty_conflict_and_extract_clause M D outl\<close>
proof -
  have size_out: \<open>size (mset outl) \<le> 1 + uint_max div 2\<close>
    using simple_clss_size_upper_div2[OF lits _ consistent]
      \<open>distinct outl\<close> by auto

  define I where
    \<open>I \<equiv> \<lambda>(E, C, i). mset (take i C) = mset (take i outl) \<and> E = D - mset (take i outl) \<and>
            length C = length outl \<and> C ! 0 = outl ! 0 \<and> i \<ge> 1 \<and> i \<le> length outl \<and>
            (1 < length (take i C) \<longrightarrow>
                 highest_lit M (mset (tl (take i C)))
                  (Some (C ! 1, get_level M (C ! 1))))\<close>
  have I0: \<open>I (D, replicate (length outl) (outl ! 0), one_uint32_nat)\<close>
    using assms by (cases outl) (auto simp: I_def)
  have I_Loop: \<open>I (remove1_mset (outl ! i) E,
         if get_level M (C[i := outl ! i] ! one_uint32_nat)
            < get_level M (C[i := outl ! i] ! i)
         then swap (C[i := outl ! i]) one_uint32_nat i else C[i := outl ! i],
         i + one_uint32_nat)\<close>
    if
      I: \<open>I ECi\<close> and
      DCi: \<open>ECi = (E, Ci)\<close> and
      Ci: \<open>Ci = (C, i)\<close> and
      \<open>i < length outl\<close> and
      \<open>i < length C\<close>
    for ECi E Ci C i
  proof -
    have
      mset_C_outl: \<open>mset (take i C) = mset (take i outl)\<close> and
      E: \<open>E = D - mset (take i outl)\<close> and
      \<open>length C = length outl\<close> and
      C_outl_0: \<open>C ! 0 = outl ! 0\<close> and
      \<open>1 \<le> i\<close> and
      \<open>i \<le> length outl\<close> and
      highest: \<open>1 < length (take i C) \<longrightarrow> highest_lit M (mset (tl (take i C))) (Some (C ! 1, get_level M (C ! 1)))\<close>
      using I unfolding DCi Ci I_def
      by auto

    have \<open>mset (take (i + 1)
         (if get_level M (C[i := outl ! i] ! 1)
             < get_level M (C[i := outl ! i] ! i)
          then swap (C[i := outl ! i]) 1 i else C[i := outl ! i])) =
      mset (take (i + 1) outl)\<close>
    proof -
      have \<open>mset (take (Suc i) C[i := outl ! i]) = mset (take (Suc i) outl)\<close>
        using mset_C_outl \<open>1 \<le> i\<close> \<open>i < length C\<close> \<open>length C = length outl\<close>
        apply (subst take_Suc_conv_app_nth)
        subgoal by auto
        apply (subst take_Suc_conv_app_nth)
        subgoal by auto
        by (auto simp: list_update_append)
      then show ?thesis
        using mset_C_outl \<open>1 \<le> i\<close> \<open>i < length C\<close> \<open>length C = length outl\<close>
        by (auto simp: take_swap_relevant)
    qed


    moreover have \<open>remove1_mset (outl ! i) E = D - mset (take (i + 1) outl)\<close>
      using E \<open>i < length outl\<close> by (auto simp: take_Suc_conv_app_nth)

    moreover have \<open>length
       (if get_level M (C[i := outl ! i] ! 1)
           < get_level M (C[i := outl ! i] ! i)
        then swap (C[i := outl ! i]) 1 i else C[i := outl ! i]) =
      length outl\<close>
      by (auto simp: \<open>length C = length outl\<close>)

    moreover have \<open>(if get_level M (C[i := outl ! i] ! 1)
          < get_level M (C[i := outl ! i] ! i)
       then swap (C[i := outl ! i]) 1 i else C[i := outl ! i]) !
      0 =
      outl ! 0\<close>
      using C_outl_0 \<open>1 \<le> i\<close>
      by (auto simp: \<open>length C = length outl\<close> swap_nth_irrelevant)
    moreover have \<open>1 \<le> i + 1\<close>
      using  \<open>1 \<le> i\<close> by linarith

    moreover have \<open>i + 1 \<le> length outl\<close>
      using \<open>i < length outl\<close> by auto
    moreover have \<open>
      highest_lit M
       (mset
         (tl (take (i + 1)
               (if get_level M (C[i := outl ! i] ! 1)
                   < get_level M (C[i := outl ! i] ! i)
                then swap (C[i := outl ! i]) 1 i else C[i := outl ! i]))))
       (Some
         ((if get_level M (C[i := outl ! i] ! 1)
              < get_level M (C[i := outl ! i] ! i)
           then swap (C[i := outl ! i]) 1 i else C[i := outl ! i]) !
          1,
          get_level M
           ((if get_level M (C[i := outl ! i] ! 1)
                < get_level M (C[i := outl ! i] ! i)
             then swap (C[i := outl ! i]) 1 i else C[i := outl ! i]) !
            1)))\<close>
      if \<open>1 < length
           (take (i + 1)
             (if get_level M (C[i := outl ! i] ! 1)
                 < get_level M (C[i := outl ! i] ! i)
              then swap (C[i := outl ! i]) 1 i else C[i := outl ! i]))\<close>
    proof -
      have highest: \<open>Suc 0 < i \<Longrightarrow>
         highest_lit M (mset (tl (take i C)))
     (Some (C ! Suc 0, get_level M (C ! Suc 0)))\<close>
        using \<open>i < length C\<close> \<open>length C = length outl\<close> \<open>1 \<le> i\<close>
        using highest that by (auto split: if_splits)

      have \<open>outl ! 0 = outl ! i \<Longrightarrow>
       mset (take i outl) = add_mset (outl ! i) (remove1_mset (outl ! i) (mset (take i outl)))\<close>
        using \<open>i < length C\<close> \<open>length C = length outl\<close> \<open>1 \<le> i\<close>
        by (subst diff_union_swap2[symmetric])
          (auto simp: in_set_take_conv_nth intro!: exI[of _ 0])
      then have [simp]: \<open>mset (tl (take (Suc i) (swap (C[i := outl ! i]) (Suc 0) i))) =
             add_mset (outl ! i) (mset (tl (take i C)))\<close>
        using mset_C_outl \<open>1 \<le> i\<close> \<open>i < length C\<close> \<open>length C = length outl\<close> C_outl_0
        by (auto simp: take_swap_relevant mset_tl hd_conv_nth take_Suc_conv_app_nth
            list_update_append remove1_mset_add_mset_If)
      have [simp]: \<open>mset (tl (take (Suc i) C[i := outl ! i])) =
           add_mset (outl ! i) (mset (tl (take i C)))\<close>
        using mset_C_outl \<open>1 \<le> i\<close> \<open>i < length C\<close> \<open>length C = length outl\<close> C_outl_0
        by (auto simp: mset_tl hd_conv_nth take_Suc_conv_app_nth
            list_update_append remove1_mset_add_mset_If)
      show ?thesis
      proof (cases \<open>i = Suc 0\<close>)
        case False
        then have [simp]: \<open>i > Suc 0\<close> \<open>Suc 0 < length C\<close> \<open>i \<noteq> Suc 0\<close>
          using \<open>1 \<le> i\<close> \<open>i < length C\<close> by auto
        have \<open>get_level M (C ! Suc 0) < get_level M (C[i := outl ! i] ! i) \<Longrightarrow>
       highest_lit M (add_mset (outl ! i) (mset (tl (take i C))))
         (Some (swap (C[i := outl ! i]) (Suc 0) i ! Suc 0,
          get_level M (swap (C[i := outl ! i]) (Suc 0) i ! Suc 0)))\<close>
          using \<open>i < length C\<close> \<open>length C = length outl\<close> \<open>1 \<le> i\<close> highest
          by (auto simp: highest_lit_def get_maximum_level_add_mset swap_nth_relevant)
        moreover have \<open>\<not> get_level M (C ! Suc 0) < get_level M (C[i := outl ! i] ! i) \<Longrightarrow>
            highest_lit M (mset (tl (take (Suc i) C[i := outl ! i])))
                (Some (C ! Suc 0, get_level M (C ! Suc 0)))\<close>
          using \<open>i < length C\<close> \<open>length C = length outl\<close> \<open>1 \<le> i\<close> highest
          by (auto simp: highest_lit_def get_maximum_level_add_mset swap_nth_relevant)
        ultimately show ?thesis
          by auto
      next
        case [simp]: True
        show ?thesis
          using \<open>i < length C\<close> \<open>length C = length outl\<close> \<open>1 \<le> i\<close>
          by (cases C; cases \<open>tl C\<close>)
            (auto simp: highest_lit_def nth_list_update' get_maximum_level_add_mset)
      qed
    qed
    ultimately show ?thesis
      unfolding I_def one_uint32_nat_def by blast
  qed
  have delete: \<open>delete_from_lookup_conflict_pre (outl ! i, E)\<close>
    if
      I: \<open>I ECi\<close> and
      \<open>case ECi of (D, C, i) \<Rightarrow> i < length_u outl\<close> and
      DCi: \<open>ECi = (E, Ci)\<close> and
      Ci: \<open>Ci = (C, i)\<close> and
      \<open>i < length outl\<close> and
      \<open>i < length C\<close>
    for ECi E Ci C i
  proof -
    have
      mset_C_outl: \<open>mset (take i C) = mset (take i outl)\<close> and
      E: \<open>E = D - mset (take i outl)\<close> and
      \<open>length C = length outl\<close> and
      C_outl_0: \<open>C ! 0 = outl ! 0\<close> and
      \<open>1 \<le> i\<close> and
      \<open>i \<le> length outl\<close> and
      highest: \<open>1 < length (take i C) \<longrightarrow> highest_lit M (mset (tl (take i C))) (Some (C ! 1, get_level M (C ! 1)))\<close>
      using I unfolding DCi Ci I_def
      by auto
    have E': \<open>E = mset (drop i outl)\<close>
      using assms(3)
      unfolding E assms(1)
      apply (subst append_take_drop_id[symmetric, of _ \<open>i-1\<close>])
      apply (subst (asm) append_take_drop_id[symmetric, of _ i])
      unfolding mset_append distinct_append
      using \<open>1 \<le> i\<close>
      apply (cases outl; cases i)
      by auto
    have \<open>outl ! i \<in># E\<close> and outl_i: \<open>outl ! i \<in># mset outl\<close>
      using assms(3)  \<open>i < length outl\<close> unfolding E'
      by (auto simp: set_drop_conv)
    moreover have \<open>outl ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using lits multi_member_split[OF outl_i] by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    moreover have \<open>- outl ! i \<notin># E\<close>
      using E' assms(5) outl_i
      by (auto simp: consistent_interp_def dest!: in_set_dropD)
    ultimately show ?thesis
      using lits
      unfolding delete_from_lookup_conflict_pre_def assms
      by auto
  qed
  have C_1: \<open>C[i := outl ! i] ! 1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    if
      I: \<open>I ECi\<close> and
      DCi: \<open>ECi = (E, Ci)\<close> and
      Ci: \<open>Ci = (C, i)\<close> and
      \<open>i < length outl\<close>
    for ECi E Ci C i
  proof -
   have
      mset_C_outl: \<open>mset (take i C) = mset (take i outl)\<close> and
      E: \<open>E = D - mset (take i outl)\<close> and
      \<open>length C = length outl\<close> and
      C_outl_0: \<open>C ! 0 = outl ! 0\<close> and
      \<open>1 \<le> i\<close> and
      \<open>i \<le> length outl\<close> and
      highest: \<open>1 < length (take i C) \<longrightarrow> highest_lit M (mset (tl (take i C))) (Some (C ! 1, get_level M (C ! 1)))\<close>
      using I unfolding DCi Ci I_def
      by auto
    have C_1: \<open>C ! 1 \<in># mset outl\<close> if \<open>i \<noteq> Suc 0\<close>
      apply (subst (2) append_take_drop_id[symmetric, of _ i])
      unfolding mset_C_outl[symmetric] mset_append
      using \<open>i < length outl\<close> \<open>1 \<le> i\<close>  that
      by (auto simp: in_set_take_conv_nth \<open>length C = length outl\<close>
          intro!: exI[of _ 1])
    have outl_1: \<open>outl ! 1 \<in># mset outl\<close>
      unfolding mset_C_outl[symmetric] mset_append
      using \<open>i < length outl\<close> \<open>1 \<le> i\<close>
      by (auto simp: in_set_take_conv_nth)
    show ?thesis
      apply (cases \<open>i = 1\<close>)
      subgoal
        using lits multi_member_split[OF outl_1] \<open>i < length outl\<close> \<open>1 \<le> i\<close>
        by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset nth_list_update'
            \<open>length C = length outl\<close>)
      subgoal
        using lits multi_member_split[OF C_1] \<open>i < length outl\<close> \<open>1 \<le> i\<close>
        by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset nth_list_update')
      done
  qed
  have C_1': \<open>C ! 1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    if
      I: \<open>I ECi\<close> and
      DCi: \<open>ECi = (E, Ci)\<close> and
      Ci: \<open>Ci = (C, i)\<close> and
      \<open>length outl \<noteq> 1\<close> and
      cond: \<open>\<not>(case ECi of (D, C, i) \<Rightarrow> i < length_u outl)\<close>
    for ECi E Ci C i
  proof -
    have
      mset_C_outl: \<open>mset (take i C) = mset (take i outl)\<close> and
      E: \<open>E = D - mset (take i outl)\<close> and
      \<open>length C = length outl\<close> and
      C_outl_0: \<open>C ! 0 = outl ! 0\<close> and
      \<open>1 \<le> i\<close> and
      \<open>i \<le> length outl\<close> and
      highest: \<open>1 < length (take i C) \<longrightarrow> highest_lit M (mset (tl (take i C))) (Some (C ! 1, get_level M (C ! 1)))\<close>
      using I unfolding DCi Ci I_def
      by auto
    have [simp]: \<open>i = length outl\<close>
      using \<open>1 \<le> i\<close> cond \<open>length outl \<noteq> 1\<close> \<open>i \<le> length outl\<close> unfolding DCi Ci
      by auto
    have \<open>mset C = mset outl\<close>
      using mset_C_outl \<open>length C = length outl\<close> by auto
    have \<open>length C > 1\<close>
      unfolding \<open>length C = length outl\<close>
      using assms \<open>length outl \<noteq> 1\<close> by (cases outl)auto
    then have C_1: \<open>C ! 1 \<in># mset outl\<close>
      unfolding mset_C_outl[symmetric] mset_append \<open>mset C = mset outl\<close>[symmetric]
      using \<open>1 \<le> i\<close> that \<open>length outl \<noteq> 1\<close> cond
      by (auto simp: in_set_take_conv_nth \<open>length C = length outl\<close>
          intro!: exI[of _ 1])
    show ?thesis
      using lits multi_member_split[OF C_1] \<open>1 \<le> i\<close> \<open>length outl \<noteq> 1\<close>
      by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset nth_list_update')
  qed

  show ?thesis
    unfolding empty_conflict_and_extract_clause_heur_def empty_conflict_and_extract_clause_def Let_def
    I_def[symmetric]
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(_, _, i). length outl - i)\<close> and
          I = \<open>I\<close>])
    subgoal by auto
    subgoal by (rule I0)
    subgoal by auto
    subgoal by (auto simp: I_def)
    subgoal by (rule delete)
    subgoal by (auto simp: delete_from_lookup_conflict_pre_def)
    subgoal by (rule C_1)
    subgoal using size_out by (auto simp: uint_max_def)
    subgoal by (rule I_Loop)
    subgoal by auto
    subgoal using assms by (cases outl) (auto simp: I_def)
    subgoal using assms by (auto simp: I_def)
    subgoal by (rule C_1')
    subgoal by (auto simp: set_empty_conflict_to_none_def)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def)
    done
qed


sepref_thm empty_conflict_and_extract_clause_heur_code
  is \<open>uncurry2 (PR_CONST empty_conflict_and_extract_clause_heur)\<close>
  :: \<open>[\<lambda>((M, D), outl). outl \<noteq> [] \<and> length outl \<le> uint_max]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>k \<rightarrow>
       option_lookup_clause_assn *a clause_ll_assn *a uint32_nat_assn\<close>
  supply [[goals_limit=1]] image_image[simp]
  unfolding empty_conflict_and_extract_clause_heur_def PR_CONST_def
  array_fold_custom_replicate
  by sepref

concrete_definition (in -) empty_conflict_and_extract_clause_heur_code
   uses isasat_input_bounded_nempty.empty_conflict_and_extract_clause_heur_code.refine_raw
   is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) empty_conflict_and_extract_clause_heur_code_def

lemmas empty_conflict_and_extract_clause_heur_hnr[sepref_fr_rules] =
   empty_conflict_and_extract_clause_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm empty_conflict_and_extract_clause_heur_fast_code
  is \<open>uncurry2 (PR_CONST empty_conflict_and_extract_clause_heur)\<close>
  :: \<open>[\<lambda>((M, D), outl). outl \<noteq> [] \<and> length outl \<le> uint_max]\<^sub>a
      trail_fast_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>k \<rightarrow>
       option_lookup_clause_assn *a clause_ll_assn *a uint32_nat_assn\<close>
  supply [[goals_limit=1]] image_image[simp]
  unfolding empty_conflict_and_extract_clause_heur_def PR_CONST_def
  array_fold_custom_replicate
  by sepref

concrete_definition (in -) empty_conflict_and_extract_clause_heur_fast_code
   uses isasat_input_bounded_nempty.empty_conflict_and_extract_clause_heur_fast_code.refine_raw
   is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) empty_conflict_and_extract_clause_heur_fast_code_def

lemmas empty_conflict_and_extract_clause_heur_hnr_fast[sepref_fr_rules] =
   empty_conflict_and_extract_clause_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in isasat_input_ops) extract_shorter_conflict_wl_nlit where
\<open>extract_shorter_conflict_wl_nlit K M NU D NE UE =
    SPEC(\<lambda>D'. D' \<noteq> None \<and> the D' \<subseteq># the D \<and> K \<in># the D' \<and>
      mset `# ran_mf NU + NE + UE \<Turnstile>pm the D')\<close>

definition (in isasat_input_ops) extract_shorter_conflict_wl_nlit_st
  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>
where
  \<open>extract_shorter_conflict_wl_nlit_st =
     (\<lambda>(M, N, D, NE, UE, WS, Q). do {
        let K = -lit_of (hd M);
        D \<leftarrow> extract_shorter_conflict_wl_nlit K M N D NE UE;
        RETURN (M, N, D, NE, UE, WS, Q)})\<close>

definition (in isasat_input_ops) empty_lookup_conflict_and_highest
  :: \<open>'v twl_st_wl \<Rightarrow> ('v twl_st_wl \<times> nat) nres\<close>
where
  \<open>empty_lookup_conflict_and_highest  =
     (\<lambda>(M, N, D, NE, UE, WS, Q). do {
        let K = -lit_of (hd M);
        let n = get_maximum_level M (remove1_mset K (the D));
        RETURN ((M, N, D, NE, UE, WS, Q), n)})\<close>

definition (in isasat_input_ops) propagate_bt_wl_D_ext
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>propagate_bt_wl_D_ext = (\<lambda>L highest (M, N, D, NE, UE, Q, W). do {
    L' \<leftarrow> find_lit_of_max_level_wl (M, N, D, NE, UE, Q, W) L;
    D'' \<leftarrow> list_of_mset2 (-L) L' (the D);
    let b = False;
    (N, i) \<leftarrow> fm_add_new b D'' N;
    RETURN (Propagated (-L) i # M,
        N, None, NE, UE, {#L#}, W(-L:= W (-L) @ [i], L':= W L' @ [i]))
      })\<close>

definition (in isasat_input_ops) backtrack_wl_D_heur_inv where
  \<open>backtrack_wl_D_heur_inv S \<longleftrightarrow> (\<exists>S'. (S, S') \<in> twl_st_heur \<and> backtrack_wl_D_inv S')\<close>

definition extract_shorter_conflict_heur where
  \<open>extract_shorter_conflict_heur = (\<lambda>M NU NUE C outl. do {
     let K = lit_of (hd M);
     let C = Some (remove1_mset (-K) (the C));
     C \<leftarrow> iterate_over_conflict (-K) M NU NUE (the C);
     RETURN (Some (add_mset (-K) C))
  })\<close>

definition (in -) empty_cach where
  \<open>empty_cach cach = (\<lambda>_. SEEN_UNKNOWN)\<close>


definition (in isasat_input_ops) empty_conflict_and_extract_clause_pre
   :: \<open>(((nat,nat) ann_lits \<times> nat clause) \<times> nat clause_l) \<Rightarrow> bool\<close> where
  \<open>empty_conflict_and_extract_clause_pre =
    (\<lambda>((M, D), outl). D = mset (tl outl)  \<and> outl \<noteq> [] \<and> distinct outl \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset outl) \<and>
    \<not>tautology (mset outl) \<and> length outl \<le> uint_max)\<close>

definition (in isasat_input_ops) extract_shorter_conflict_list_heur_st
  :: \<open>twl_st_wl_heur \<Rightarrow> (twl_st_wl_heur \<times> nat \<times> nat clause_l) nres\<close>
where
  \<open>extract_shorter_conflict_list_heur_st = (\<lambda>(M, N, D, Q', W', vm, \<phi>, clvls, cach, lbd, outl,
       stats). do {
     ASSERT(M \<noteq> []);
     let K = lit_of (hd M);
     ASSERT(-K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
     ASSERT(D \<noteq> None \<and> delete_from_lookup_conflict_pre (-K, the D));
     let D = remove1_mset (-K) (the D);
     ASSERT(0 < length outl);
     let outl = outl[0 := -K];
     ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf N));
     (D, cach, outl) \<leftarrow> minimize_and_extract_highest_lookup_conflict M N D cach lbd outl;
     let cach = empty_cach cach;
     ASSERT(empty_conflict_and_extract_clause_pre ((M, D), outl));
     (D, C, n) \<leftarrow> empty_conflict_and_extract_clause M D outl;
     RETURN ((M, N, D, Q', W', vm, \<phi>, clvls, cach, lbd, take 1 outl, stats), n, C)
  })\<close>

lemma the_option_lookup_clause_assn[sepref_fr_rules]:
  \<open>(return o snd, RETURN o the) \<in> [\<lambda>D. D \<noteq> None]\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow> lookup_clause_assn\<close>
  by (sepref_to_hoare)
    (sep_auto simp: option_lookup_clause_assn_def option_lookup_clause_rel_def
      lookup_clause_assn_def hr_comp_def)


definition (in -) empty_cach_ref where
  \<open>empty_cach_ref = (\<lambda>(cach, support). (replicate (length cach) SEEN_UNKNOWN, []))\<close>

definition (in isasat_input_ops) empty_cach_ref_set_inv where
  \<open>empty_cach_ref_set_inv cach0 support =
    (\<lambda>(i, cach). length cach = length cach0 \<and>
         (\<forall>L \<in> set (drop i support). L < length cach) \<and>
         (\<forall>L \<in> set (take i support).  cach ! L = SEEN_UNKNOWN) \<and>
         (\<forall>L < length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set (drop i support)))\<close>

definition (in isasat_input_ops) empty_cach_ref_set where
  \<open>empty_cach_ref_set = (\<lambda>(cach0, support). do {
    let n = length support;
    (_, cach) \<leftarrow> WHILE\<^sub>T\<^bsup>empty_cach_ref_set_inv cach0 support\<^esup>
      (\<lambda>(i, cach). i < length support)
      (\<lambda>(i, cach). do {
         ASSERT(i < length support);
         ASSERT(support ! i < length cach);
         RETURN(i+1, cach[support ! i := SEEN_UNKNOWN])
      })
     (0, cach0);
    RETURN (cach, emptied_list support)
  })\<close>

lemma (in isasat_input_ops) empty_cach_ref_set_empty_cach_ref:
  \<open>(empty_cach_ref_set, RETURN o empty_cach_ref) \<in>
    [\<lambda>(cach, supp). (\<forall>L \<in> set supp. L < length cach) \<and>
      (\<forall>L < length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set supp)]\<^sub>f
    Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have H: \<open>WHILE\<^sub>T\<^bsup>empty_cach_ref_set_inv cach0 support'\<^esup> (\<lambda>(i, cach). i < length support')
       (\<lambda>(i, cach).
           ASSERT (i < length support') \<bind>
           (\<lambda>_. ASSERT (support' ! i < length cach) \<bind>
           (\<lambda>_. RETURN (i + 1, cach[support' ! i := SEEN_UNKNOWN]))))
       (0, cach0) \<bind>
      (\<lambda>(_, cach). RETURN (cach, emptied_list support'))
      \<le> \<Down> Id (RETURN (replicate (length cach0) SEEN_UNKNOWN, []))\<close>
    if
      \<open>\<forall>L\<in>set support'. L < length cach0\<close> and
      \<open>\<forall>L<length cach0. cach0 ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set support'\<close>
    for cach support cach0 support'
  proof -
    have init: \<open>empty_cach_ref_set_inv cach0 support' (0, cach0)\<close>
      using that unfolding empty_cach_ref_set_inv_def
      by auto
    have valid_length:
       \<open>empty_cach_ref_set_inv cach0 support' s \<Longrightarrow> case s of (i, cach) \<Rightarrow> i < length support' \<Longrightarrow>
          s = (cach', sup') \<Longrightarrow> support' ! cach' < length sup'\<close>  for s cach' sup'
      using that unfolding empty_cach_ref_set_inv_def
      by auto
    have set_next: \<open>empty_cach_ref_set_inv cach0 support' (i + 1, cach'[support' ! i := SEEN_UNKNOWN])\<close>
      if
        inv: \<open>empty_cach_ref_set_inv cach0 support' s\<close> and
        cond: \<open>case s of (i, cach) \<Rightarrow> i < length support'\<close> and
        s: \<open>s = (i, cach')\<close> and
        valid[simp]: \<open>support' ! i < length cach'\<close>
      for s i cach'
    proof -
      have
        le_cach_cach0: \<open>length cach' = length cach0\<close> and
        le_length: \<open>\<forall>L\<in>set (drop i support'). L < length cach'\<close> and
        UNKNOWN: \<open>\<forall>L\<in>set (take i support'). cach' ! L = SEEN_UNKNOWN\<close> and
        support: \<open>\<forall>L<length cach'. cach' ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set (drop i support')\<close> and
        [simp]: \<open>i < length support'\<close>
        using inv cond unfolding empty_cach_ref_set_inv_def s prod.case
        by auto

      show ?thesis
        unfolding empty_cach_ref_set_inv_def
        unfolding prod.case
        apply (intro conjI)
        subgoal by (simp add: le_cach_cach0)
        subgoal using le_length by (simp add: Cons_nth_drop_Suc[symmetric])
        subgoal using UNKNOWN by (auto simp add: take_Suc_conv_app_nth)
        subgoal using support by (auto simp add: Cons_nth_drop_Suc[symmetric])
        done
    qed
    have final: \<open>((cach', emptied_list support'), replicate (length cach0) SEEN_UNKNOWN, []) \<in> Id\<close>
      if
        inv: \<open>empty_cach_ref_set_inv cach0 support' s\<close> and
        cond: \<open>\<not> (case s of (i, cach) \<Rightarrow> i < length support')\<close> and
        s: \<open>s = (i, cach')\<close>
        for s cach' i
    proof -
      have
        le_cach_cach0: \<open>length cach' = length cach0\<close> and
        le_length: \<open>\<forall>L\<in>set (drop i support'). L < length cach'\<close> and
        UNKNOWN: \<open>\<forall>L\<in>set (take i support'). cach' ! L = SEEN_UNKNOWN\<close> and
        support: \<open>\<forall>L<length cach'. cach' ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set (drop i support')\<close> and
        i: \<open>\<not>i < length support'\<close>
        using inv cond unfolding empty_cach_ref_set_inv_def s prod.case
        by auto
      have \<open>\<forall>L<length cach'. cach' ! L  = SEEN_UNKNOWN\<close>
        using support i by auto
      then have [dest]: \<open>L \<in> set cach' \<Longrightarrow> L = SEEN_UNKNOWN\<close> for L
        by (metis in_set_conv_nth)
      then have [dest]: \<open>SEEN_UNKNOWN \<notin> set cach' \<Longrightarrow> cach0 = [] \<and> cach' = []\<close>
        using le_cach_cach0 by (cases cach') auto
      show ?thesis
        by (auto simp: emptied_list_def list_eq_replicate_iff le_cach_cach0)
    qed
    show ?thesis
      unfolding conc_Id id_def
      apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, _). length support' - i)\<close>])
      subgoal by auto
      subgoal by (rule init)
      subgoal by auto
      subgoal by (rule valid_length)
      subgoal by (rule set_next)
      subgoal by auto
      subgoal using final by simp
      done
  qed
  show ?thesis
  unfolding empty_cach_ref_set_def empty_cach_ref_def Let_def comp_def
  by (intro frefI nres_relI) (clarify intro!: H)
qed


lemma (in isasat_input_ops) empty_cach_ref_empty_cach:
  \<open>(RETURN o empty_cach_ref, RETURN o empty_cach) \<in> cach_refinement \<rightarrow>\<^sub>f \<langle>cach_refinement\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: empty_cach_def empty_cach_ref_def cach_refinement_alt_def cach_refinement_list_def
     map_fun_rel_def)

sepref_thm (in isasat_input_ops) empty_cach_code
  is \<open>empty_cach_ref_set\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply array_replicate_hnr[sepref_fr_rules]
  unfolding empty_cach_ref_set_def comp_def
  by sepref

concrete_definition (in -) empty_cach_code
   uses isasat_input_ops.empty_cach_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) empty_cach_code_def

lemmas (in isasat_input_ops) empty_cach_ref_hnr[sepref_fr_rules] =
   empty_cach_code.refine

theorem (in isasat_input_ops) empty_cach_code_empty_cach_ref:
  \<open>(empty_cach_code, RETURN \<circ> empty_cach_ref)
    \<in> [(\<lambda>(cach :: minimize_status list, supp :: nat list).
         (\<forall>L\<in>set supp. L < length cach) \<and>
         (\<forall>L<length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set supp))]\<^sub>a
    cach_refinement_l_assn\<^sup>d \<rightarrow> cach_refinement_l_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in>[comp_PRE Id
     (\<lambda>(cach, supp).
         (\<forall>L\<in>set supp. L < length cach) \<and>
         (\<forall>L<length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set supp))
     (\<lambda>x y. True)
     (\<lambda>x. nofail ((RETURN \<circ> empty_cach_ref) x))]\<^sub>a
      hrp_comp (cach_refinement_l_assn\<^sup>d)
                     Id \<rightarrow> hr_comp cach_refinement_l_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE[OF empty_cach_ref_hnr[unfolded PR_CONST_def]
    empty_cach_ref_set_empty_cach_ref] by simp
  have pre: \<open>?pre' h x\<close> if \<open>?pre x\<close> for x h
    using that by (auto simp: comp_PRE_def trail_pol_def
        ann_lits_split_reasons_def)
  have im: \<open>?im' = ?im\<close>
    by simp
  have f: \<open>?f' = ?f\<close>
    by auto
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

lemma (in isasat_input_ops) empty_cach_hnr[sepref_fr_rules]:
  \<open>(empty_cach_code, RETURN \<circ> empty_cach) \<in> cach_refinement_assn\<^sup>d \<rightarrow>\<^sub>a cach_refinement_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in> [comp_PRE cach_refinement (\<lambda>_. True)
     (\<lambda>x y. case y of
            (cach, supp) \<Rightarrow>
              (\<forall>L\<in>set supp. L < length cach) \<and>
              (\<forall>L<length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set supp))
     (\<lambda>x. nofail
           ((RETURN \<circ> empty_cach)
             x))]\<^sub>a hrp_comp (cach_refinement_l_assn\<^sup>d)
                     cach_refinement \<rightarrow> hr_comp cach_refinement_l_assn cach_refinement\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE[OF empty_cach_code_empty_cach_ref[unfolded PR_CONST_def]
    empty_cach_ref_empty_cach] by simp
  have pre: \<open>?pre' h x\<close> if \<open>?pre x\<close> for x h
    using that by (auto simp: comp_PRE_def trail_pol_def
        ann_lits_split_reasons_def cach_refinement_alt_def)
  have im: \<open>?im' = ?im\<close>
    unfolding cach_refinement_assn_def
     prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by simp
  have f: \<open>?f' = ?f\<close>
    unfolding cach_refinement_assn_def
    by auto
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

definition (in -) ema_update :: \<open>nat \<Rightarrow> ema \<Rightarrow> nat \<Rightarrow> ema\<close> where
  \<open>ema_update coeff ema lbd = (ema >> coeff) + uint64_of_uint32 ((uint32_of_nat lbd) << (32 - coeff))\<close>

definition (in -) ema_update_ref :: \<open>nat \<Rightarrow> ema \<Rightarrow> uint32 \<Rightarrow> ema\<close> where
  \<open>ema_update_ref coeff ema lbd = (ema >> coeff) + uint64_of_uint32 (lbd << (32 - coeff))\<close>

lemma (in -) ema_update_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo ema_update_ref), uncurry2 (RETURN ooo ema_update)) \<in>
     nat_assn\<^sup>k *\<^sub>a ema_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
     unfolding ema_update_def ema_update_ref_def
     by sepref_to_hoare
       (sep_auto simp: uint32_nat_rel_def br_def)

abbreviation(in -) ema_update_slow where
  \<open>ema_update_slow \<equiv> ema_update 14\<close>
abbreviation (in -)ema_update_fast where
  \<open>ema_update_fast \<equiv> ema_update 5\<close>

definition (in isasat_input_ops) propagate_bt_wl_D_heur
  :: \<open>nat literal \<Rightarrow> nat clause_l \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>propagate_bt_wl_D_heur = (\<lambda>L C (M, N, D, Q, W, vm, \<phi>, _, cach, lbd, outl, stats, fema, sema,
         ccount). do {
      ASSERT(phase_saving \<phi> \<and> vm \<in> vmtf M \<and> undefined_lit M (-L) \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
         nat_of_lit (C!1) < length W \<and> nat_of_lit (-L) < length W);
      ASSERT(length C > 1);
      let L' = C!1;
      ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n (mset C));
      (vm, \<phi>) \<leftarrow> rescore_clause C M vm \<phi>;
      vm \<leftarrow> flush M vm;
      glue \<leftarrow> get_LBD lbd;
      let b = False;
      (N, i) \<leftarrow> fm_add_new b C N;
      ASSERT (i \<in># dom_m N);
      let N = set_LBD i glue N;
      let W = W[nat_of_lit (- L) := W ! nat_of_lit (- L) @ [i]];
      let W = W[nat_of_lit L' := W!nat_of_lit L' @ [i]];
      lbd \<leftarrow> lbd_empty lbd;
      RETURN (Propagated (- L) i # M, N, D, {#L#}, W, vm, \<phi>, zero_uint32_nat,
         cach, lbd, outl, stats, ema_update_fast fema glue, ema_update_slow sema glue,
          ccount + one_uint32)
    })\<close>

definition (in -) lit_of_hd_trail_st_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal\<close> where
  \<open>lit_of_hd_trail_st_heur S = lit_of (hd (get_trail_wl_heur S))\<close>

definition (in isasat_input_ops) remove_last
   :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> nat clause option nres\<close>
where
  \<open>remove_last _ _  = SPEC(op = None)\<close>

definition (in isasat_input_ops) propagate_unit_bt_wl_D_int
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>propagate_unit_bt_wl_D_int = (\<lambda>L (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
      fema, sema, ccount). do {
      ASSERT(undefined_lit M L \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> vm \<in> vmtf M);
      vm \<leftarrow> flush M vm;
      glue \<leftarrow> get_LBD lbd;
      lbd \<leftarrow> lbd_empty lbd;
      RETURN (Propagated (- L) 0 # M, N, D, {#L#}, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
         ema_update_fast fema glue, ema_update_slow sema glue,
        ccount + one_uint32)})\<close>


definition (in isasat_input_ops) backtrack_wl_D_nlit_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>backtrack_wl_D_nlit_heur S\<^sub>0 =
    do {
      ASSERT(backtrack_wl_D_heur_inv S\<^sub>0);
      ASSERT(get_trail_wl_heur S\<^sub>0 \<noteq> []);
      let L = lit_of_hd_trail_st_heur S\<^sub>0;
      (S, n, C) \<leftarrow> extract_shorter_conflict_list_heur_st S\<^sub>0;
      ASSERT(get_clauses_wl_heur S = get_clauses_wl_heur S\<^sub>0);
      ASSERT(find_decomp_wl_pre (n, S));
      S \<leftarrow> find_decomp_wl_nlit n S;

      ASSERT(get_clauses_wl_heur S = get_clauses_wl_heur S\<^sub>0);
      if size C > 1
      then do {
        propagate_bt_wl_D_heur L C S
      }
      else do {
        propagate_unit_bt_wl_D_int L S
     }
  }\<close>

lemma get_all_ann_decomposition_get_level:
  assumes
    L': \<open>L' = lit_of (hd M')\<close> and
    nd: \<open>no_dup M'\<close> and
    decomp: \<open>(Decided K # a, M2) \<in> set (get_all_ann_decomposition M')\<close> and
    lev_K: \<open>get_level M' K = Suc (get_maximum_level M' (remove1_mset (- L') y))\<close> and
    L: \<open>L \<in># remove1_mset (- lit_of (hd M')) y\<close>
  shows \<open>get_level a L = get_level M' L\<close>
proof -
  obtain M3 where M3: \<open>M' = M3 @ M2 @ Decided K # a\<close>
    using decomp by blast
  from lev_K have lev_L: \<open>get_level M' L < get_level M' K\<close>
    using get_maximum_level_ge_get_level[OF L, of M'] unfolding L'[symmetric] by auto
  have [simp]: \<open>get_level (M3 @ M2 @ Decided K # a) K = Suc (count_decided a)\<close>
    using nd unfolding M3 by auto
  have undef:\<open>undefined_lit (M3 @ M2) L\<close>
    using lev_L get_level_skip_end[of \<open>M3 @ M2\<close> L \<open>Decided K # a\<close>] unfolding M3
    by auto
  then have \<open>atm_of L \<noteq> atm_of K\<close>
    using lev_L unfolding M3 by auto
  then show ?thesis
    using undef unfolding M3 by (auto simp: get_level_cons_if)
qed

end

definition del_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>del_conflict_wl = (\<lambda>(M, N, D, NE, UE, Q, W). (M, N, None, NE, UE, Q, W))\<close>

lemma [simp]:
  \<open>get_clauses_wl (del_conflict_wl S) = get_clauses_wl S\<close>
  by (cases S) (auto simp: del_conflict_wl_def)

context isasat_input_bounded_nempty
begin

definition (in isasat_input_ops) twl_st_heur_bt :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_bt =
  {((M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats), (M, N, D, NE, UE, Q, W)).
    M = M' \<and> N' = N \<and>
    D' = None \<and>
    Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D' \<and>
    cach_refinement_empty cach \<and>
    out_learned M D' outl
  }\<close>

lemma (in isasat_input_ops) twl_st_heur_bt_get_clauses_wl:
  \<open>(S, Y) \<in> twl_st_heur_bt \<Longrightarrow> get_clauses_wl_heur S = get_clauses_wl Y\<close>
  by (cases S; cases Y) (auto simp: twl_st_heur_bt_def)

lemma backtrack_wl_D_nlit_backtrack_wl_D:
  \<open>(backtrack_wl_D_nlit_heur, backtrack_wl_D) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  have backtrack_wl_D_nlit_heur_alt_def: \<open>backtrack_wl_D_nlit_heur S\<^sub>0 =
    do {
      ASSERT(backtrack_wl_D_heur_inv S\<^sub>0);
      ASSERT(get_trail_wl_heur S\<^sub>0 \<noteq> []);
      let L = lit_of_hd_trail_st_heur S\<^sub>0;
      (S, n, C) \<leftarrow> extract_shorter_conflict_list_heur_st S\<^sub>0;
      ASSERT(get_clauses_wl_heur S = get_clauses_wl_heur S\<^sub>0);
      ASSERT(find_decomp_wl_pre (n, S));
      S \<leftarrow> find_decomp_wl_nlit n S;
      ASSERT(get_clauses_wl_heur S = get_clauses_wl_heur S\<^sub>0);

      if size C > 1
      then do {
        let _ = C ! 1;
        propagate_bt_wl_D_heur L C S
      }
      else do {
        propagate_unit_bt_wl_D_int L S
     }
  }\<close> for S\<^sub>0
    unfolding backtrack_wl_D_nlit_heur_def Let_def
    by auto
  have inv: \<open>backtrack_wl_D_heur_inv S'\<close>
    if
      \<open>backtrack_wl_D_inv S\<close> and
      \<open>(S', S) \<in> twl_st_heur\<close>
    for S S'
    using that unfolding backtrack_wl_D_heur_inv_def
    by (cases S; cases S') (blast intro: exI[of _ S'])
  have shorter:
     \<open>extract_shorter_conflict_list_heur_st S'
       \<le> \<Down> {((T', n, C), T). (T', del_conflict_wl T) \<in> twl_st_heur \<and>
              n = get_maximum_level (get_trail_wl T)
                  (remove1_mset (-lit_of(hd (get_trail_wl T))) (the (get_conflict_wl T))) \<and>
              mset C = the (get_conflict_wl T) \<and>
              get_conflict_wl T \<noteq> None \<and>
              equality_except_conflict_wl T S \<and>
              (1 < length C \<longrightarrow>
                highest_lit (get_trail_wl T) (mset (tl C))
                (Some (C ! 1, get_level (get_trail_wl T) (C ! 1)))) \<and>
              C \<noteq> [] \<and> hd C = -lit_of(hd (get_trail_wl T)) \<and>
              mset C \<subseteq># the (get_conflict_wl S) \<and>
              distinct_mset (the (get_conflict_wl S)) \<and>
              literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S)) \<and>
              get_conflict_wl S \<noteq> None \<and>
              - lit_of (hd (get_trail_wl S)) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
              find_decomp_wl_pre (n, T')}
           (extract_shorter_conflict_wl S)\<close>
     (is \<open>_ \<le> \<Down> ?shorter _\<close>)
    if
      inv: \<open>backtrack_wl_D_inv S\<close> and
      S'_S: \<open>(S', S) \<in> twl_st_heur\<close>
    for S S'
  proof -
    obtain M N D NE UE Q W where
      S: \<open>S = (M, N, D, NE, UE, Q, W)\<close>
      by (cases S)
    obtain W' vm \<phi> clvls cach lbd outl stats where
      S': \<open>S' = (M, N, D, Q, W', vm, \<phi>, clvls, cach, lbd, outl, stats)\<close>
      using S'_S by (cases S') (auto simp: twl_st_heur_def S)
    have
      \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> and
      vm: \<open>vm \<in> vmtf M\<close> and
      \<open>phase_saving \<phi>\<close> and
      \<open>no_dup M\<close> and
      \<open>clvls \<in> counts_maximum_level M D\<close> and
      cach_empty: \<open>cach_refinement_empty cach\<close> and
      outl: \<open>out_learned M D outl\<close>
      using S'_S unfolding S S'
      by (auto simp: twl_st_heur_def S)
    obtain T U where
      \<L>\<^sub>i\<^sub>n :\<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
      S_T: \<open>(S, T) \<in> state_wl_l None\<close> and
      \<open>correct_watching S\<close> and
      T_U: \<open>(T, U) \<in> twl_st_l None\<close> and
      trail_nempty: \<open>get_trail_l T \<noteq> []\<close> and
      nss: \<open>\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of U) S'\<close> and
      nsr: \<open>\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of U) S'\<close> and
      not_none: \<open>get_conflict_l T \<noteq> None\<close> and
      struct_invs: \<open>twl_struct_invs U\<close> and
      stgy_invs: \<open>twl_stgy_invs U\<close> and
      list_invs: \<open>twl_list_invs T\<close> and
      not_empty: \<open>get_conflict_l T \<noteq> Some {#}\<close>
      using inv unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
      apply -
      apply normalize_goal+
      by blast

    have all_struct:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of U)\<close>
      using struct_invs
      by (auto simp: twl_struct_invs_def)
    then have uL_D: \<open>- lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S)\<close>
      using cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of
          \<open>state\<^sub>W_of U\<close>] nss not_none not_empty stgy_invs trail_nempty S_T T_U
      by (auto simp: twl_st_wl twl_st twl_stgy_invs_def)
    have
      \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close> and
      lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of U)\<close> and
      \<open>\<forall>s\<in>#learned_clss (state\<^sub>W_of U).
        \<not> tautology s\<close> and
      dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of U)\<close> and
      confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of U)\<close> and
      \<open>all_decomposition_implies_m  (cdcl\<^sub>W_restart_mset.clauses  (state\<^sub>W_of U))
        (get_all_ann_decomposition (trail (state\<^sub>W_of U)))\<close> and
      learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of U)\<close>
      using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    have n_d: \<open>no_dup M\<close>
      using lev_inv S_T T_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
       by (auto simp: twl_st S)
    have M_\<L>\<^sub>i\<^sub>n: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl S)\<close>
      apply (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail[OF S_T struct_invs T_U \<L>\<^sub>i\<^sub>n ]) .
    have dist_D: \<open>distinct_mset (the (get_conflict_wl S))\<close>
      using dist not_none S_T T_U unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def S
      by (auto simp: twl_st)
    have \<open>the (conflicting (state\<^sub>W_of U)) =
      add_mset (- lit_of (cdcl\<^sub>W_restart_mset.hd_trail (state\<^sub>W_of U)))
        {#L \<in># the (conflicting (state\<^sub>W_of U)).  get_level (trail (state\<^sub>W_of U)) L
             < backtrack_lvl (state\<^sub>W_of U)#}\<close>
      apply (rule cdcl\<^sub>W_restart_mset.no_skip_no_resolve_single_highest_level)
      subgoal using nss unfolding S by simp
      subgoal using nsr unfolding S by simp
      subgoal using struct_invs unfolding twl_struct_invs_def S by simp
      subgoal using stgy_invs unfolding twl_stgy_invs_def S by simp
      subgoal using not_none S_T T_U by (simp add: twl_st)
      subgoal using not_empty not_none S_T T_U by (auto simp add: twl_st)
      done
    then have D_filter: \<open>the D = add_mset (- lit_of (hd M)) {#L \<in># the D. get_level M L < count_decided M#}\<close>
      using trail_nempty S_T T_U by (simp add: twl_st S)
    have tl_outl_D: \<open>mset (tl (outl[0 := - lit_of (hd M)])) = remove1_mset (outl[0 := - lit_of (hd M)] ! 0) (the D)\<close>
      using outl S_T T_U not_none
      apply (subst D_filter)
      by (cases outl) (auto simp: out_learned_def S)
    let ?D = \<open>remove1_mset (- lit_of (hd M)) (the D)\<close>
    have \<L>\<^sub>i\<^sub>n_S: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S))\<close>
      apply (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_conflict[OF S_T _ T_U])
      using \<L>\<^sub>i\<^sub>n not_none struct_invs not_none S_T T_U by (auto simp: S)
    then have \<L>\<^sub>i\<^sub>n_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n ?D\<close>
      unfolding S by (auto intro: literals_are_in_\<L>\<^sub>i\<^sub>n_mono)
    have tauto_confl: \<open>\<not> tautology (the (get_conflict_wl S))\<close>
      apply (rule conflict_not_tautology[OF S_T _ T_U])
      using struct_invs not_none S_T T_U by (auto simp: twl_st)
    from not_tautology_mono[OF _ this, of ?D] have tauto_D: \<open>\<not> tautology ?D\<close>
      by (auto simp: S)
    have entailed:
      \<open>mset `# ran_mf (get_clauses_wl S) +  (get_unit_learned_clss_wl S + get_unit_init_clss_wl S) \<Turnstile>pm
        add_mset (- lit_of (hd (get_trail_wl S)))
           (remove1_mset (- lit_of (hd (get_trail_wl S))) (the (get_conflict_wl S)))\<close>
      using uL_D learned not_none S_T T_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
      by (auto simp: ac_simps twl_st get_unit_clauses_wl_alt_def)

    have mini: \<open>minimize_and_extract_highest_lookup_conflict (get_trail_wl S) (get_clauses_wl S)
              ?D cach lbd (outl[0 := - lit_of (hd M)])
          \<le> \<Down> {((E, s, outl), E'). E = E' \<and> mset (tl outl) = E \<and>
                 outl ! 0 = - lit_of (hd M) \<and> E' \<subseteq># remove1_mset (- lit_of (hd M)) (the D) \<and>
                outl \<noteq> []}
              (iterate_over_conflict (- lit_of (hd M)) (get_trail_wl S)
                (mset `# ran_mf (get_clauses_wl S))
                (get_unit_learned_clss_wl S + get_unit_init_clss_wl S) ?D)\<close>
      apply (rule minimize_and_extract_highest_lookup_conflict_iterate_over_conflict[of S T U
         \<open>outl [0 := - lit_of (hd M)]\<close>
         \<open>remove1_mset _ (the D)\<close> cach \<open>-lit_of (hd M)\<close> lbd])
      subgoal using S_T .
      subgoal using T_U .
      subgoal using \<open>out_learned M D outl\<close> tl_outl_D
        by (auto simp: out_learned_def)
      subgoal using confl not_none S_T T_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        by (auto simp: true_annot_CNot_diff twl_st S)
      subgoal
        using dist not_none S_T T_U unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        by (auto simp: twl_st S)
      subgoal using tauto_D .
      subgoal using M_\<L>\<^sub>i\<^sub>n unfolding S by simp
      subgoal using struct_invs unfolding S by simp
      subgoal using list_invs unfolding S by simp
      subgoal using M_\<L>\<^sub>i\<^sub>n cach_empty S_T T_U
        unfolding cach_refinement_empty_def conflict_min_analysis_inv_def
        by (auto dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms simp: twl_st S)
      subgoal using entailed unfolding S by simp
      subgoal using \<L>\<^sub>i\<^sub>n_D .
      subgoal using \<open>out_learned M D outl\<close> tl_outl_D
        by (auto simp: out_learned_def)
      subgoal using \<open>out_learned M D outl\<close> tl_outl_D
        by (auto simp: out_learned_def)
      done
    then have mini: \<open>minimize_and_extract_highest_lookup_conflict M N
              ?D cach lbd (outl[0 := - lit_of (hd M)])
          \<le> \<Down> {((E, s, outl), E'). E = E' \<and> mset (tl outl) = E \<and>
                 outl ! 0 = - lit_of (hd M) \<and> E' \<subseteq># remove1_mset (- lit_of (hd M)) (the D) \<and>
                  outl \<noteq> []}
              (iterate_over_conflict (- lit_of (hd M)) (get_trail_wl S)
                (mset `# ran_mf N)
                (get_unit_learned_clss_wl S + get_unit_init_clss_wl S) ?D)\<close>
      unfolding S by auto
     have mini: \<open>minimize_and_extract_highest_lookup_conflict M N
              ?D cach lbd (outl[0 := - lit_of (hd M)])
          \<le> \<Down> {((E, s, outl), E'). E = E' \<and> mset (tl outl) = E \<and>
                 outl ! 0 = - lit_of (hd M) \<and> E' \<subseteq># remove1_mset (- lit_of (hd M)) (the D) \<and>
                 outl \<noteq> []}
              (SPEC (\<lambda>D'. D' \<subseteq># ?D \<and>  mset `# ran_mf N +
                      (get_unit_learned_clss_wl S + get_unit_init_clss_wl S) \<Turnstile>pm add_mset (- lit_of (hd M)) D'))\<close>
       apply (rule order.trans)
        apply (rule mini)
       apply (rule conc_fun_mono)
       apply (rule order.trans)
        apply (rule iterate_over_conflict_spec)
       subgoal using entailed by (auto simp: S)
       subgoal
        using dist not_none S_T T_U unfolding S cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        by (auto simp: twl_st)
      subgoal by auto
      done
    have uM_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>- lit_of (hd M) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using M_\<L>\<^sub>i\<^sub>n trail_nempty S_T T_U by (cases M)
        (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons uminus_\<A>\<^sub>i\<^sub>n_iff twl_st S)

    have ref: \<open>RES (\<Union>(a, C, n)\<in>{(D, C, n).
                   D = None \<and>
                   mset C = mset outl' \<and>
                   C ! 0 = outl' ! 0 \<and>
                   (1 < length C \<longrightarrow>
                    highest_lit M (mset (tl C))
                     (Some (C ! 1, get_level M (C ! 1)))) \<and>
                   (1 < length C \<longrightarrow> n = get_level M (C ! 1)) \<and>
                   (length C = 1 \<longrightarrow> n = 0)}.
              {((M, N, a, Q, W', vm, \<phi>, clvls, empty_cach cach', lbd, take 1 outl',
                 stats),
                n, C)})
      \<le> \<Down> ?shorter
          (SPEC (\<lambda>S. \<exists>D'. D' \<subseteq># the D \<and>
                          S = (M, N, Some D', NE, UE, Q, W) \<and>
                          clauses (twl_clause_of `# ran_mf N) + NE + UE \<Turnstile>pm D' \<and>
                          - lit_of (hd M) \<in># D'))\<close>
      (is \<open>RES ?res \<le> \<Down> ?R (RES ?S)\<close>)
      if
        incl: \<open>mset (tl outl') \<subseteq># remove1_mset (- lit_of (hd M)) (the D)\<close> and
        ent: \<open>mset `# ran_mf N + (get_unit_learned_clss_wl S + get_unit_init_clss_wl S) \<Turnstile>pm
     add_mset (- lit_of (hd M)) (mset (tl outl'))\<close> and
        outl0: \<open>outl' ! 0 = - lit_of (hd M)\<close> and
        \<open>mset (tl outl') \<subseteq># remove1_mset (- lit_of (hd M)) (the D)\<close> and
        \<open>outl' \<noteq> []\<close>
      for outl' cach'
    proof -
      have H: \<open>(M, N, Some (mset (snd (snd s))), NE, UE, Q, W) \<in> ?S\<close> (is ?TS) and
        H': \<open>(s, M, N, Some (mset (snd (snd s))), NE, UE, Q, W) \<in> ?R\<close> (is ?TR)
        if \<open>s \<in> ?res\<close>
        for s :: \<open>twl_st_wl_heur \<times> nat \<times> nat clause_l\<close>
      proof -
        obtain S' n c where
          s: \<open>s = (S', n, c)\<close>
          by (cases s)
        have
          \<open>mset c = mset outl'\<close> and
          \<open>c ! 0 = outl' ! 0\<close> and
          S': \<open>S' = (M, N, None, Q, W', vm, \<phi>, clvls, empty_cach cach', lbd, take 1 outl', stats)\<close> and
          C: \<open>1 < length c \<longrightarrow> highest_lit M (mset (tl c))
                (Some (c ! 1, get_level M (c ! 1)))\<close>
            \<open>length c = 1 \<longrightarrow> n = 0\<close>
            \<open>1 < length c \<longrightarrow> n = get_level M (c ! 1)\<close>
          using that unfolding s
          by auto
        have \<open>c \<noteq> []\<close> and
            [simp]: \<open>length outl' = length c\<close>
          using \<open>mset c = mset outl'\<close>  \<open>outl' \<noteq> []\<close>
          by (auto simp del: \<open>mset c = mset outl'\<close> size_mset
              simp: size_mset[symmetric])

        then have [simp]: \<open>mset c = add_mset (c!0) (mset (tl c))\<close>
            \<open>mset (tl outl') = mset (tl c)\<close>
            \<open>mset outl' = mset c\<close>
          using \<open>outl' \<noteq> []\<close> \<open>mset c = mset outl'\<close> \<open>c ! 0 = outl' ! 0\<close>
          by (auto simp: mset_tl hd_conv_nth[symmetric])
        have ent: \<open>set_mset (mset `# (ran_mf N)) \<union> set_mset NE \<union> set_mset UE \<Turnstile>p
             add_mset (- lit_of (hd M)) (mset (tl c))\<close>
          using ent
          unfolding s by (auto simp: mset_take_mset_drop_mset outl0 S ac_simps)
        show ?TS
          using incl ent outl0 uL_D
          unfolding s \<open>mset (tl outl') = mset (tl c)\<close> \<open>c ! 0 = outl' ! 0\<close>[symmetric]
          by (auto simp: mset_take_mset_drop_mset' S insert_subset_eq_iff uL_D)
        have mset_tl_c_remove:
          \<open>(remove1_mset (- lit_of (hd M)) (add_mset (c ! 0) (mset (tl c)))) = mset (tl c)\<close>
          using C \<open>outl' \<noteq> []\<close> outl0 \<open>c \<noteq> []\<close>
          unfolding \<open>c ! 0 = outl' ! 0\<close>[symmetric] \<open>length outl' = length c\<close>
          apply (cases c)
          by (auto simp: highest_lit_def)
        have n: \<open>n = get_maximum_level M
         (remove1_mset (- lit_of (hd M)) (add_mset (c ! 0) (mset (tl c))))\<close>
          using C \<open>outl' \<noteq> []\<close> outl0 \<open>c \<noteq> []\<close>
          unfolding \<open>c ! 0 = outl' ! 0\<close>[symmetric] \<open>length outl' = length c\<close>
          apply (cases c)
          by (auto simp: highest_lit_def)
        moreover have \<open>(S', del_conflict_wl
          (M, N, Some (add_mset (outl' ! 0) (mset (tl outl'))), NE, UE, Q, W)) \<in> twl_st_heur\<close>
          using \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> \<open>vm \<in> vmtf M\<close>
            \<open>phase_saving \<phi>\<close>
            \<open>no_dup M\<close>
            \<open>cach_refinement_empty cach\<close> \<open>c \<noteq> []\<close> \<open>outl' \<noteq> []\<close>
          by (auto simp: twl_st_heur_def S' del_conflict_wl_def
              empty_cach_def cach_refinement_empty_def out_learned_def)
        moreover have \<open>Suc 0 < length c \<Longrightarrow>
             highest_lit M (mset (tl c))
               (Some (c ! Suc 0,
                get_level M (c ! Suc 0)))\<close>
          using C \<open>outl' \<noteq> []\<close> outl0 \<open>c \<noteq> []\<close>
          unfolding \<open>c ! 0 = outl' ! 0\<close>[symmetric] \<open>length outl' = length c\<close>
          apply (cases c)
          by (auto simp: highest_lit_def)
        moreover {
          have 1: \<open>{#- lit_of (hd M)#} + remove1_mset (- lit_of (hd M)) (the D) = the D\<close>
            using uL_D by (auto simp: S)
          have \<open>add_mset (- lit_of (hd M)) (mset (tl c)) \<subseteq># the D\<close>
          using subset_mset.add_left_mono[OF incl, of \<open>{#- lit_of (hd M)#}\<close>, unfolded 1] \<open>outl' \<noteq> []\<close>
          by auto
      } note incl_c_d = this
      moreover {
        have K: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of U)\<close>
          using stgy_invs not_none not_empty confl unfolding twl_stgy_invs_def
          by auto
        have \<open>get_maximum_level M (mset (tl c)) \<le> get_maximum_level M (remove1_mset (-lit_of (hd M)) (the D))\<close>
          apply (rule get_maximum_level_mono)
          using incl by auto
        also have K: \<open>get_maximum_level M (remove1_mset (-lit_of (hd M)) (the D)) < count_decided M\<close>
          using cdcl\<^sub>W_restart_mset.no_skip_no_resolve_level_get_maximum_lvl_le[OF nss nsr all_struct K]
            not_none not_empty confl trail_nempty S_T T_U
          by (auto simp: twl_st S)
        finally have \<open>get_maximum_level M (mset (tl c)) < count_decided M\<close> .
        then have \<open>n < count_decided M\<close>
          by (auto simp: n mset_tl_c_remove)
        then have \<open>find_decomp_wl_pre (n, S')\<close>
          using M_\<L>\<^sub>i\<^sub>n struct_invs vm S_T T_U n_d
          unfolding find_decomp_wl_pre_def find_decomp_w_ns_pre_def
          by (auto simp: S S' twl_st)
      }
      ultimately show ?TR
          using \<open>c \<noteq> []\<close> outl0 not_none \<L>\<^sub>i\<^sub>n_S dist_D uM_\<L>\<^sub>a\<^sub>l\<^sub>l S_T T_U
          unfolding s \<open>c ! 0 = outl' ! 0\<close>[symmetric] by (auto simp: S' S hd_conv_nth)
      qed
      show ?thesis
        apply (rule RES_refine)
        unfolding Bex_def
        apply (rule_tac x= \<open>(M, N, Some (mset (snd (snd s))), NE, UE, Q, W)\<close> in exI)
        apply (intro conjI)
         apply (rule H; assumption)
        apply (rule H'; assumption)
        done
    qed
    have \<open>0 < length outl\<close>
      using \<open>out_learned M D outl\<close>
      by (auto simp: out_learned_def)
    have True_and_True: \<open>True \<and> True \<equiv> True\<close>
      by auto
    have \<open>lit_of (hd M) \<notin># the D\<close>
      using uL_D tauto_confl
      by (auto dest!: multi_member_split simp: S add_mset_eq_add_mset tautology_add_mset)
    then have pre1: \<open>D \<noteq> None \<and> delete_from_lookup_conflict_pre (- lit_of (hd M), the D)\<close>
      using not_none uL_D uM_\<L>\<^sub>a\<^sub>l\<^sub>l S_T T_U unfolding delete_from_lookup_conflict_pre_def
      by (auto simp: twl_st S)
    have pre2: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf N) \<equiv> True\<close>
      using M_\<L>\<^sub>i\<^sub>n S_T T_U not_none \<L>\<^sub>i\<^sub>n
      unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def
      by (auto simp: twl_st S all_lits_of_mm_union)
    have empty_conflict_and_extract_clause_pre:
        \<open>empty_conflict_and_extract_clause_pre ((M, mset (tl E)), E)\<close>
      if
        E0: \<open>E ! 0 = - lit_of (hd M)\<close> and
        incl: \<open>mset (tl E) \<subseteq># remove1_mset (- lit_of (hd M)) (the D)\<close> and
        [simp]: \<open>E \<noteq> []\<close>
      for E
    proof -
      have E: \<open>mset E = {#- lit_of (hd M)#} + mset (tl E)\<close>
        using E0 by (cases E) auto
      have incl: \<open>mset E \<subseteq># the D\<close>
        using E0 subset_mset.add_left_mono[OF incl, of \<open>{#-lit_of (hd M)#}\<close>, unfolded E[symmetric]]
        uL_D by (cases E) (auto simp: S dest: multi_member_split)
      have \<open>\<not>tautology (mset E)\<close>
        using not_tautology_mono[OF incl] tauto_confl by (auto simp: S)
      have \<open>distinct_mset (mset E)\<close>
        using distinct_mset_mono[OF incl] dist_D by (auto simp: S)
      have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset E)\<close>
        using literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF _ incl] \<L>\<^sub>i\<^sub>n_S by (auto simp: S)
      have \<open>length E \<le> uint_max\<close>
        using simple_clss_size_upper_div2[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset E)\<close>
            \<open>distinct_mset (mset E)\<close> \<open>\<not>tautology (mset E)\<close>]
        by (auto simp: uint_max_def)
      then show ?thesis
        using \<open>\<not>tautology (mset E)\<close> \<open>distinct_mset (mset E)\<close> \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset E)\<close>
        unfolding empty_conflict_and_extract_clause_pre_def
        by auto
    qed
    have trail_nempty: \<open>M \<noteq> []\<close>
      using trail_nempty S_T T_U
      by (auto simp: twl_st S)
    show ?thesis
      unfolding extract_shorter_conflict_list_heur_st_def extract_shorter_conflict_wl_def
        empty_conflict_and_extract_clause_def S S' Let_def
      apply clarify
      apply (subst trail_nempty)
      apply (subst uM_\<L>\<^sub>a\<^sub>l\<^sub>l)
      apply (subst \<open>0 < length outl\<close>)
      apply (subst pre1)+
      apply (subst not_False_eq_True)+
      apply (subst True_and_True)
      apply (subst pre2)
      unfolding assert_true_bind_conv not_False_eq_True
      apply (rule bind_refine_res)
       prefer 2
       apply (rule mini[unfolded conc_fun_RES])
      apply clarify
      apply (rule ASSERT_refine_left)
      subgoal by (rule empty_conflict_and_extract_clause_pre)
      subgoal
        unfolding RES_RES3_RETURN_RES RETURN_def S'[symmetric] S[symmetric]
        supply [[unify_trace_failure]]
        apply (rule ref; assumption)
        done
      done
  qed

  have find_decomp_wl_nlit: \<open>find_decomp_wl_nlit n T
      \<le> \<Down>  {(U, U''). (U, U'') \<in> twl_st_heur_bt \<and> equality_except_trail_wl U'' T' \<and>
       (\<exists>K M2. (Decided K # (get_trail_wl U''), M2) \<in> set (get_all_ann_decomposition (get_trail_wl T')) \<and>
          get_level (get_trail_wl T') K = get_maximum_level (get_trail_wl T') (the (get_conflict_wl T') - {#-lit_of (hd (get_trail_wl T'))#}) + 1)}
          (find_decomp_wl (lit_of (hd (get_trail_wl S'))) T')\<close>
    (is \<open>_ \<le>  \<Down> ?find_decomp _\<close>)
    if
      \<open>(S, S') \<in> twl_st_heur\<close> and
      \<open>backtrack_wl_D_inv S'\<close> and
      \<open>backtrack_wl_D_heur_inv S\<close> and
      TT': \<open>(TnC, T') \<in> ?shorter S'\<close> and
      [simp]: \<open>nC = (n, C)\<close> and
      [simp]: \<open>TnC = (T, nC)\<close>
    for S S' TnC T' T nC n C
  proof -
    obtain M N U D NE UE Q W where
      T': \<open>T' = (M, N, D, NE, UE, Q, W)\<close>
      by (cases T')
    obtain W' vm \<phi> clvls cach lbd outl stats where
      T: \<open>T = (M, N, None, Q, W', vm, \<phi>, clvls, cach, lbd, outl, stats)\<close>
      using TT' by (cases T) (auto simp: twl_st_heur_def T' del_conflict_wl_def)
    have n: \<open>n = get_maximum_level M (remove1_mset (- lit_of (hd M)) (mset C))\<close> and
      eq: \<open>equality_except_conflict_wl T' S'\<close> and
      \<open>the D = mset C\<close> \<open>D \<noteq> None\<close> and
      \<open>no_dup M\<close>
      using TT' by (auto simp: T T' twl_st_heur_def)
    have [simp]: \<open>get_trail_wl S' = M\<close>
      using eq \<open>the D = mset C\<close> \<open>D \<noteq> None\<close> by (cases S'; auto simp: T')
    have H: \<open>\<exists>s'\<in>{S. \<exists>K M2 M1.
                  S = (M1, N, D, NE, UE, Q, W) \<and>
                  (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
                  get_level M K = get_maximum_level M
                    (remove1_mset (- lit_of (hd (get_trail_wl S'))) (the D)) + 1}.
         (s, s') \<in> ?find_decomp\<close>
         (is \<open>\<exists>s' \<in> ?H. _\<close>)
      if s: \<open>s \<in> Collect (find_decomp_wl_nlit_prop n (M, N, None, Q, W', vm, \<phi>, clvls, cach, lbd, outl, stats))\<close>
      for s :: \<open>twl_st_wl_heur\<close>
    proof -
      obtain K M2 M1 vm' lbd' where
        s: \<open>s = (M1, N, None,  Q, W', vm', \<phi>, clvls, cach, lbd', outl, stats)\<close> and
        decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
        n_M_K: \<open>get_level M K = Suc n\<close> and
        vm': \<open>vm' \<in> vmtf M1\<close>
        using s by auto
      let ?T' = \<open>(M1, N, D, NE, UE, Q, W)\<close>
      have \<open>?T' \<in> ?H\<close>
        using decomp n n_M_K \<open>the D = mset C\<close> by (auto simp: T')
      have [simp]: \<open>NO_MATCH [] M \<Longrightarrow> out_learned M None ai \<longleftrightarrow> out_learned [] None ai\<close> for M ai
        by (auto simp: out_learned_def)
      have \<open>no_dup M1\<close>
        using \<open>no_dup M\<close> decomp by (auto dest!: get_all_ann_decomposition_exists_prepend
            dest: no_dup_appendD)
      have twl: \<open>((M1, N, None, Q, W', vm', \<phi>, clvls, cach, lbd', outl, stats),
           M1, N, D, NE, UE, Q, W) \<in> twl_st_heur_bt\<close>
        using TT' vm' \<open>no_dup M1\<close> by (auto simp: T T' twl_st_heur_bt_def twl_st_heur_def
            del_conflict_wl_def)
      have \<open>equality_except_trail_wl (M1, N, D, NE, UE, Q, W) T'\<close>
        using eq by (auto simp: T')
      then have T': \<open>(s, ?T') \<in> ?find_decomp\<close>
        using decomp n n_M_K \<open>the D = mset C\<close> twl
        by (auto simp: s T')
      show ?thesis
        using \<open>?T' \<in> ?H\<close> \<open>(s, ?T') \<in> ?find_decomp\<close>
        by blast
    qed
    show ?thesis
      unfolding find_decomp_wl_nlit_def find_decomp_wl_def T T'
      apply clarify
      apply (rule RES_refine)
      unfolding T[symmetric] T'[symmetric]
      apply (rule H)
      by fast
  qed
  have fst_find_lit_of_max_level_wl: \<open>RETURN (C ! 1)
      \<le> \<Down> Id
          (find_lit_of_max_level_wl U'
            (lit_of (hd (get_trail_wl S'))))\<close>
    if
      \<open>(S, S') \<in> twl_st_heur\<close> and
      \<open>backtrack_wl_D_inv S'\<close> and
      \<open>backtrack_wl_D_heur_inv S\<close> and
      \<open>(TnC, T') \<in> ?shorter S'\<close> and
      [simp]: \<open>nC = (n, C)\<close> and
      [simp]: \<open>TnC = (T, nC)\<close> and
      find_decomp: \<open>(U, U') \<in> ?find_decomp T'\<close> and
      size_C: \<open>1 < length C\<close> and
      size_conflict_U': \<open>1 < size (the (get_conflict_wl U'))\<close>
    for S S' TnC T' T nC n C U U'
  proof -
    obtain M N NE UE Q W where
      T': \<open>T' = (M, N, Some (mset C), NE, UE, Q, W)\<close> and
      \<open>C \<noteq> []\<close>
      using \<open>(TnC, T') \<in> ?shorter S'\<close> \<open>1 < length C\<close> find_decomp
      apply (cases U'; cases T'; cases S')
      by (auto simp: find_lit_of_max_level_wl_def)

    obtain M' K M2 where
      U': \<open>U' = (M', N, Some (mset C), NE, UE, Q, W)\<close> and
       decomp: \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M)\<close> and
       lev_K: \<open>get_level M K = Suc (get_maximum_level M (remove1_mset (- lit_of (hd M)) (the (Some (mset C)))))\<close>
      using \<open>(TnC, T') \<in> ?shorter S'\<close> \<open>1 < length C\<close> find_decomp
      apply (cases U'; cases S')
      by (auto simp: find_lit_of_max_level_wl_def T')

    have [simp]: \<open>get_trail_wl S' = get_trail_wl T'\<close>
      using \<open>(TnC, T') \<in> ?shorter S'\<close> \<open>1 < length C\<close> find_decomp
      by (cases T'; cases S'; auto simp: find_lit_of_max_level_wl_def U'; fail)+
    have [simp]: \<open>remove1_mset (- lit_of (hd M)) (mset C) = mset (tl C)\<close>
      apply (subst mset_tl)
      using \<open>(TnC, T') \<in> ?shorter S'\<close>
      by (auto simp: find_lit_of_max_level_wl_def U' highest_lit_def T')
    have
      \<open>no_dup (get_trail_wl S')\<close>
      using that unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
      twl_struct_invs_def twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def apply -
      apply normalize_goal+
      by (simp add: twl_st)
    then have n_d: \<open>no_dup M\<close>
      using \<open>(TnC, T') \<in> ?shorter S'\<close> unfolding T'
      by (cases S') auto

    have nempty[iff]: \<open>remove1_mset (- lit_of (hd M)) (the (Some(mset C))) \<noteq> {#}\<close>
      using U' T' find_decomp size_C by (cases C) (auto simp: remove1_mset_empty_iff)
    have H[simp]: \<open>aa \<in># remove1_mset (- lit_of (hd M)) (the (Some(mset C))) \<Longrightarrow>
       get_level M' aa = get_level M aa\<close> for aa
      apply (rule get_all_ann_decomposition_get_level[of \<open>lit_of (hd M)\<close> _ K _ M2 \<open>the (Some(mset C))\<close>])
      subgoal ..
      subgoal by (rule n_d)
      subgoal by (rule decomp)
      subgoal by (rule lev_K)
      subgoal by simp
      done

    have \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) (mset C)) =
       get_maximum_level M' (remove1_mset (- lit_of (hd M)) (mset C))\<close>
      by (rule get_maximum_level_cong) auto
    then show ?thesis
      using \<open>(TnC, T') \<in> ?shorter S'\<close> \<open>1 < length C\<close> hd_conv_nth[OF \<open>C \<noteq> []\<close>, symmetric]
      by (auto simp: find_lit_of_max_level_wl_def U' highest_lit_def T')
  qed
  have propagate_bt_wl_D_heur: \<open>propagate_bt_wl_D_heur (lit_of_hd_trail_st_heur S) C U
      \<le> \<Down> twl_st_heur (propagate_bt_wl_D (lit_of (hd (get_trail_wl S'))) L' U')\<close>
    if
      SS': \<open>(S, S') \<in> twl_st_heur\<close> and
      \<open>backtrack_wl_D_inv S'\<close> and
      \<open>backtrack_wl_D_heur_inv S\<close> and
      \<open>(TnC, T') \<in> ?shorter S'\<close> and
      [simp]: \<open>nC = (n, C)\<close> and
      [simp]: \<open>TnC = (T, nC)\<close> and
      find_decomp: \<open>(U, U') \<in> ?find_decomp T'\<close> and
      \<open>1 < length C\<close> and
      \<open>1 < size (the (get_conflict_wl U'))\<close> and
      C_L': \<open>(C ! 1, L') \<in> nat_lit_lit_rel\<close>
    for S S' TnC T' T nC n C U U' L'
  proof -
    have
      TT': \<open>(T, del_conflict_wl T') \<in> twl_st_heur\<close> and
      n: \<open>n = get_maximum_level (get_trail_wl T')
          (remove1_mset (- lit_of (hd (get_trail_wl T'))) (mset C))\<close> and
      T_C: \<open>get_conflict_wl T' = Some (mset C)\<close> and
      T'S': \<open>equality_except_conflict_wl T' S'\<close> and
      \<open>C \<noteq> []\<close> and
      hd_C: \<open>hd C = - lit_of (hd (get_trail_wl T'))\<close> and
      highest: \<open>highest_lit (get_trail_wl T') (mset (tl C))
         (Some (C ! Suc 0, get_level (get_trail_wl T') (C ! Suc 0)))\<close> and
      incl: \<open>mset C \<subseteq># the (get_conflict_wl S')\<close> and
      dist_S': \<open>distinct_mset (the (get_conflict_wl S'))\<close> and
      list_confl_S': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S'))\<close> and
      \<open>get_conflict_wl S' \<noteq> None\<close> and
      uM_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>-lit_of (hd (get_trail_wl S')) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using \<open>(TnC, T') \<in> ?shorter S'\<close>  \<open>1 < length C\<close>
      by auto
    obtain K M2 where
      UU': \<open>(U, U') \<in> twl_st_heur_bt\<close> and
      U'U': \<open>equality_except_trail_wl U' T'\<close> and
      lev_K: \<open>get_level (get_trail_wl T') K = Suc (get_maximum_level (get_trail_wl T')
           (remove1_mset (- lit_of (hd (get_trail_wl T')))
             (the (get_conflict_wl T'))))\<close> and
      decomp: \<open>(Decided K # get_trail_wl U', M2) \<in> set (get_all_ann_decomposition (get_trail_wl T'))\<close>
      using find_decomp
      by auto

    obtain M N NE UE Q W where
      T': \<open>T' = (M, N, Some (mset C), NE, UE, Q, W)\<close> and
      \<open>C \<noteq> []\<close>
      using TT' T_C \<open>1 < length C\<close>
      apply (cases T'; cases S')
      by (auto simp: find_lit_of_max_level_wl_def)
    obtain D' where
      S': \<open>S' = (M, N, D', NE, UE, Q, W)\<close>
      using T'S' \<open>1 < length C\<close>
      apply (cases S')
      by (auto simp: find_lit_of_max_level_wl_def T' del_conflict_wl_def)

    obtain M1 where
      U': \<open>U' = (M1, N, Some (mset C), NE, UE, Q, W)\<close>
      using \<open>(TnC, T') \<in> ?shorter S'\<close> \<open>1 < length C\<close> find_decomp
      apply (cases U')
      by (auto simp: find_lit_of_max_level_wl_def T')
    obtain vm' W' \<phi> clvls cach lbd outl stats fema sema ccount where
        U: \<open>U = (M1, N, None, Q, W', vm', \<phi>, clvls, cach, lbd, outl, stats, fema, sema, ccount)\<close> and
        vm': \<open>vm' \<in> vmtf M1\<close> and
        \<phi>: \<open>phase_saving \<phi>\<close>
      using UU' find_decomp by (cases U) (auto simp: U' T' twl_st_heur_bt_def)
    have
      W'W: \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> and
      vmtf: \<open>vm' \<in> vmtf M1\<close> and
      \<open>phase_saving \<phi>\<close> and
      n_d_M1: \<open>no_dup M1\<close> and
      empty_cach: \<open>cach_refinement_empty cach\<close> and
      \<open>length outl = Suc 0\<close> and
      outl: \<open>out_learned M1 None outl\<close>
      using UU' by (auto simp: out_learned_def twl_st_heur_bt_def U U')
    have [simp]: \<open>get_trail_wl_heur S = M\<close> \<open>C ! 1 = L'\<close> \<open>C ! 0 = - lit_of (hd M)\<close> and
      n_d: \<open>no_dup M\<close>
      using SS' C_L' hd_C \<open>C \<noteq> []\<close> by (auto simp: S' U' T' twl_st_heur_def hd_conv_nth)
    have undef: \<open>undefined_lit M1 (lit_of (hd M))\<close>
      using decomp n_d
      by (auto dest!: get_all_ann_decomposition_exists_prepend simp: T' hd_append U' neq_Nil_conv
          split: if_splits)
    have [simp]: \<open>C ! Suc 0 \<noteq> - lit_of (hd M)\<close>
      using distinct_mset_mono[OF incl dist_S'] C_L' \<open>1 < length C\<close>  \<open>C ! 0 = - lit_of (hd M)\<close>
      by (cases C; cases \<open>tl C\<close>) (auto simp del: \<open>C ! 0 = - lit_of (hd M)\<close>)
    have H: \<open>(RES ((\<lambda>i. (fmupd i (C, False) N, i)) ` {i. 0 < i \<and> i \<notin># dom_m N}) \<bind>
                   (\<lambda>(N, i).  ASSERT (i \<in># dom_m N) \<bind> (\<lambda>_. f N i))) =
          (RES ((\<lambda>i. (fmupd i (C, False) N, i)) ` {i. 0 < i \<and> i \<notin># dom_m N}) \<bind>
                   (\<lambda>(N, i). f N i))\<close> (is \<open>?A = ?B\<close>) for f C N
    proof -
      have \<open>?B \<le> ?A\<close>
        by (auto intro: ext simp: intro_spec_iff bind_RES)
      moreover have \<open>?A \<le> ?B\<close>
        by (auto intro: ext simp: intro_spec_iff bind_RES)
      ultimately show ?thesis by auto
    qed
    have [simp]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close>
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF list_confl_S' incl] .
    then have \<open>C ! Suc 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using \<open>1 < length C\<close>
      by (cases C; cases \<open>tl C\<close>) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    then have \<open>nat_of_lit (C ! Suc 0) < length W'\<close>
      using W'W unfolding map_fun_rel_def by (auto simp: image_image)
    then show ?thesis
      supply [[goals_limit=1]]
      using empty_cach n_d_M1 C_L' W'W outl vmtf undef \<open>1 < length C\<close> uM_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding U U' H
        propagate_bt_wl_D_heur_def propagate_bt_wl_D_def set_LBD_def Let_def rescore_clause_def
      by (auto simp: propagate_bt_wl_D_heur_def twl_st_heur_def lit_of_hd_trail_st_heur_def
          propagate_bt_wl_D_def Let_def T' U' U rescore_clause_def S' map_fun_rel_def
          list_of_mset2_def flush_def RES_RES2_RETURN_RES RES_RETURN_RES \<phi> uminus_\<A>\<^sub>i\<^sub>n_iff
          fm_add_new_def get_fresh_index_def RES_RETURN_RES2 RES_RES_RETURN_RES2
          RES_RES_RETURN_RES lbd_empty_def get_LBD_def set_LBD_def H
          intro!: ASSERT_refine_left RES_refine exI[of _ C]
          intro!: vmtf_consD)
  qed

  have propagate_unit_bt_wl_D_int: \<open>propagate_unit_bt_wl_D_int
       (lit_of_hd_trail_st_heur S) U
      \<le> \<Down> twl_st_heur
          (propagate_unit_bt_wl_D
            (lit_of (hd (get_trail_wl S'))) U')\<close>
    if
      SS': \<open>(S, S') \<in> twl_st_heur\<close> and
      \<open>backtrack_wl_D_inv S'\<close> and
      \<open>backtrack_wl_D_heur_inv S\<close> and
      \<open>(TnC, T') \<in> ?shorter S'\<close> and
      [simp]: \<open>nC = (n, C)\<close> and
      [simp]: \<open>TnC = (T, nC)\<close> and
      find_decomp: \<open>(U, U') \<in> ?find_decomp T'\<close> and
      \<open>\<not> 1 < length C\<close> and
      \<open>\<not> 1 < size (the (get_conflict_wl U'))\<close>
    for S S' TnC T' T nC n C U U'
  proof -
    have
      TT': \<open>(T, del_conflict_wl T') \<in> twl_st_heur\<close> and
      n: \<open>n = get_maximum_level (get_trail_wl T')
          (remove1_mset (- lit_of (hd (get_trail_wl T'))) (mset C))\<close> and
      T_C: \<open>get_conflict_wl T' = Some (mset C)\<close> and
      T'S': \<open>equality_except_conflict_wl T' S'\<close> and
      \<open>C \<noteq> []\<close> and
      hd_C: \<open>hd C = - lit_of (hd (get_trail_wl T'))\<close> and
      incl: \<open>mset C \<subseteq># the (get_conflict_wl S')\<close> and
      dist_S': \<open>distinct_mset (the (get_conflict_wl S'))\<close> and
      list_confl_S': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S'))\<close> and
      \<open>get_conflict_wl S' \<noteq> None\<close> and
      \<open>C \<noteq> []\<close> and
      uL_M: \<open>- lit_of (hd (get_trail_wl S')) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using \<open>(TnC, T') \<in> ?shorter S'\<close>  \<open>~1 < length C\<close>
      by (auto)
    obtain K M2 where
      UU': \<open>(U, U') \<in> twl_st_heur_bt\<close> and
      U'U': \<open>equality_except_trail_wl U' T'\<close> and
      lev_K: \<open>get_level (get_trail_wl T') K = Suc (get_maximum_level (get_trail_wl T')
           (remove1_mset (- lit_of (hd (get_trail_wl T')))
             (the (get_conflict_wl T'))))\<close> and
      decomp: \<open>(Decided K # get_trail_wl U', M2) \<in> set (get_all_ann_decomposition (get_trail_wl T'))\<close>
      using find_decomp
      by (auto)

    obtain M N NE UE Q W where
      T': \<open>T' = (M, N, Some (mset C), NE, UE, Q, W)\<close>
      using TT' T_C \<open>\<not>1 < length C\<close>
      apply (cases T'; cases S')
      by (auto simp: find_lit_of_max_level_wl_def)
    obtain D' where
      S': \<open>S' = (M, N, D', NE, UE, Q, W)\<close>
      using T'S'
      apply (cases S')
      by (auto simp: find_lit_of_max_level_wl_def T' del_conflict_wl_def)

    obtain M1 where
      U': \<open>U' = (M1, N, Some (mset C), NE, UE, Q, W)\<close>
      using \<open>(TnC, T') \<in> ?shorter S'\<close> find_decomp
      apply (cases U')
      by (auto simp: find_lit_of_max_level_wl_def T')
    obtain vm' W' \<phi> clvls cach lbd outl stats fema sema ccount where
        U: \<open>U = (M1, N, None, Q, W', vm', \<phi>, clvls, cach, lbd, outl, stats, fema, sema, ccount)\<close> and
        vm': \<open>vm' \<in> vmtf M1\<close>
      using UU' find_decomp by (cases U) (auto simp: U' T' twl_st_heur_bt_def)
    have
      W'W: \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> and
      vmtf: \<open>vm' \<in> vmtf M1\<close> and
      \<phi>: \<open>phase_saving \<phi>\<close> and
      n_d_M1: \<open>no_dup M1\<close> and
      empty_cach: \<open>cach_refinement_empty cach\<close> and
      \<open>length outl = Suc 0\<close> and
      outl: \<open>out_learned M1 None outl\<close>
      using UU' by (auto simp: out_learned_def twl_st_heur_bt_def U U')
    have [simp]: \<open>get_trail_wl_heur S = M\<close> \<open>C ! 0 = - lit_of (hd M)\<close> and
      n_d: \<open>no_dup M\<close>
      using SS' hd_C \<open>C \<noteq> []\<close> by (auto simp: S' U' T' twl_st_heur_def hd_conv_nth)
    have undef: \<open>undefined_lit M1 (lit_of (hd M))\<close>
      using decomp n_d
      by (auto dest!: get_all_ann_decomposition_exists_prepend simp: T' hd_append U' neq_Nil_conv
          split: if_splits)
    have C: \<open>C = [- lit_of (hd M)]\<close>
      using \<open>C \<noteq> []\<close> \<open>C ! 0 = - lit_of (hd M)\<close> \<open>\<not>1 < length C\<close>
      by (cases C) (auto simp del: \<open>C ! 0 = - lit_of (hd M)\<close>)
    show ?thesis
      using empty_cach n_d_M1  W'W outl vmtf C \<phi> undef uL_M unfolding U U'
      by (auto simp: propagate_unit_bt_wl_D_int_def
          propagate_unit_bt_wl_D_def U U' lit_of_hd_trail_st_heur_def
          single_of_mset_def flush_def twl_st_heur_def lbd_empty_def get_LBD_def
          RES_RES2_RETURN_RES RES_RETURN_RES S' uminus_\<A>\<^sub>i\<^sub>n_iff RES_RES_RETURN_RES
          intro!: ASSERT_refine_left RES_refine exI[of _ \<open>-lit_of (hd M)\<close>]
          intro!: vmtf_consD)
  qed
  have trail_nempty: \<open>get_trail_wl_heur S \<noteq> []\<close>
    if
      \<open>(S, S') \<in> twl_st_heur\<close> and
      \<open>backtrack_wl_D_inv S'\<close>
    for S S'
  proof -
    show ?thesis
      using that unfolding backtrack_wl_D_inv_def backtrack_wl_D_heur_inv_def backtrack_wl_inv_def
        backtrack_l_inv_def apply -
      apply normalize_goal+
      by (auto simp: twl_st twl_st_heur_state_simp)
  qed
  show ?thesis
    supply [[goals_limit=1]]
    apply (intro frefI nres_relI)
    unfolding backtrack_wl_D_nlit_heur_alt_def backtrack_wl_D_def
    apply (refine_rcg shorter)
    subgoal by (rule inv)
    subgoal by (rule trail_nempty)
    subgoal by (auto simp: twl_st_heur_state_simp equality_except_conflict_wl_get_clauses_wl)
    subgoal by auto
       apply (rule find_decomp_wl_nlit; solves assumption)
    subgoal by (auto simp: twl_st_heur_state_simp equality_except_conflict_wl_get_clauses_wl
          twl_st_heur_bt_get_clauses_wl equality_except_trail_wl_get_clauses_wl)
    subgoal for x y xa S x1 x2 x1a x2a Sa Sb
      by (cases Sb; cases S) (auto simp: twl_st_heur_state_simp)
      apply (rule fst_find_lit_of_max_level_wl; solves assumption)
     apply (rule propagate_bt_wl_D_heur; assumption)
    apply (rule propagate_unit_bt_wl_D_int; assumption)
    done
qed

definition (in -) lit_of_hd_trail_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal\<close> where
  \<open>lit_of_hd_trail_st S = lit_of (hd (get_trail_wl S))\<close>

lemma (in -) lit_of_hd_trail_st_heur_alt_def:
  \<open>lit_of_hd_trail_st_heur = (\<lambda>(M, N, D, Q, W, vm, \<phi>). lit_of_hd_trail M)\<close>
  by (auto simp: lit_of_hd_trail_st_heur_def lit_of_hd_trail_def intro!: ext)

sepref_thm lit_of_hd_trail_st_heur
  is \<open>RETURN o lit_of_hd_trail_st_heur\<close>
  :: \<open>[\<lambda>S. get_trail_wl_heur S \<noteq> []]\<^sub>a isasat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_st_heur_alt_def isasat_assn_def
  by sepref

 concrete_definition (in -) lit_of_hd_trail_st_heur_code
   uses isasat_input_bounded_nempty.lit_of_hd_trail_st_heur.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) lit_of_hd_trail_st_heur_code_def

lemmas lit_of_hd_trail_st_heur_code_refine[sepref_fr_rules] =
   lit_of_hd_trail_st_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm lit_of_hd_trail_st_heur_fast
  is \<open>RETURN o lit_of_hd_trail_st_heur\<close>
  :: \<open>[\<lambda>S. get_trail_wl_heur S \<noteq> []]\<^sub>a isasat_fast_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_st_heur_alt_def isasat_fast_assn_def
  by sepref

 concrete_definition (in -) lit_of_hd_trail_st_heur_fast_code
   uses isasat_input_bounded_nempty.lit_of_hd_trail_st_heur_fast.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) lit_of_hd_trail_st_heur_fast_code_def

lemmas lit_of_hd_trail_st_heur_code_refine_fast[sepref_fr_rules] =
   lit_of_hd_trail_st_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in -) extract_shorter_conflict_l_trivial
  :: \<open>'v literal \<Rightarrow> ('v, 'a) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow>  'v cconflict \<Rightarrow>
        ('v cconflict \<times> 'v conflict_highest_conflict) nres\<close>
where
  \<open>extract_shorter_conflict_l_trivial K M NU NE UE D =
    SPEC(\<lambda>(D', highest). D' \<noteq> None \<and> the D' \<subseteq># the D \<and>
      clause `# twl_clause_of `# ran_mf NU + NE + UE \<Turnstile>pm add_mset (-K) (the D') \<and>
      highest_lit M (the D') highest)\<close>

definition extract_shorter_conflict_remove_and_add where
  \<open>extract_shorter_conflict_remove_and_add = (\<lambda>M NU C NE UE. do {
     let K = lit_of (hd M);
     let C = Some (remove1_mset (-K) (the C));
     (C, L) \<leftarrow> extract_shorter_conflict_l_trivial K M NU NE UE C;
     RETURN (map_option (add_mset (-K)) C, L)
  })\<close>


sepref_register extract_shorter_conflict_l_trivial

definition extract_shorter_conflict_remove_and_add_st
  :: \<open>nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> nat conflict_highest_conflict) nres\<close>
where
  \<open>extract_shorter_conflict_remove_and_add_st = (\<lambda>(M, N, D, NE, UE, WS, Q). do {
     (D, L) \<leftarrow> extract_shorter_conflict_remove_and_add M N D NE UE;
     RETURN ((M, N, D, NE, UE, WS, Q), L)
  })\<close>


definition extract_shorter_conflict_list_heur_st_pre where
  \<open>extract_shorter_conflict_list_heur_st_pre S \<longleftrightarrow>
    get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [] \<and>
        -lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S) \<and>
        literals_are_\<L>\<^sub>i\<^sub>n S\<close>

definition extract_shorter_conflict_list_lookup_heur_pre where
  \<open>extract_shorter_conflict_list_lookup_heur_pre =
     (\<lambda>((((M, NU), cach), D), lbd). literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and> M \<noteq> [] \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf NU) \<and>
        (\<forall>a\<in>lits_of_l M. atm_of a < length (snd (snd D))))\<close>


subsubsection \<open>Backtrack with direct extraction of literal if highest level\<close>

sepref_thm propagate_bt_wl_D_code
  is \<open>uncurry2 (PR_CONST propagate_bt_wl_D_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit = 1]] uminus_\<A>\<^sub>i\<^sub>n_iff[simp] image_image[simp] append_ll_def[simp]
  rescore_clause_def[simp] flush_def[simp]
  unfolding propagate_bt_wl_D_heur_def isasat_assn_def cons_trail_Propagated_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] append_ll_def[symmetric]
    cons_trail_Propagated_def[symmetric] PR_CONST_def
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) propagate_bt_wl_D_code
  uses isasat_input_bounded_nempty.propagate_bt_wl_D_code.refine_raw
  is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_bt_wl_D_code_def

lemmas propagate_bt_wl_D_heur_hnr[sepref_fr_rules] =
  propagate_bt_wl_D_code.refine[OF isasat_input_bounded_nempty_axioms]

sepref_thm propagate_bt_wl_D_fast_code
  is \<open>uncurry2 (PR_CONST propagate_bt_wl_D_heur)\<close>
  :: \<open>[\<lambda>((L, C), S). isasat_fast S]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> isasat_fast_assn\<close>
  supply [[goals_limit = 1]] uminus_\<A>\<^sub>i\<^sub>n_iff[simp] image_image[simp] append_ll_def[simp]
  rescore_clause_def[simp] flush_def[simp]
  unfolding propagate_bt_wl_D_heur_def isasat_fast_assn_def cons_trail_Propagated_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] append_ll_def[symmetric]
    cons_trail_Propagated_def[symmetric] PR_CONST_def
    isasat_fast
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) propagate_bt_wl_D_fast_code
  uses isasat_input_bounded_nempty.propagate_bt_wl_D_fast_code.refine_raw
  is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_bt_wl_D_fast_code_def

lemmas propagate_bt_wl_D_heur_fast_hnr[sepref_fr_rules] =
  propagate_bt_wl_D_fast_code.refine[OF isasat_input_bounded_nempty_axioms]

sepref_thm propagate_unit_bt_wl_D_code
  is \<open>uncurry (PR_CONST propagate_unit_bt_wl_D_int)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit = 1]] flush_def[simp] image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[simp]
  unfolding propagate_unit_bt_wl_D_int_def cons_trail_Propagated_def[symmetric] isasat_assn_def
  PR_CONST_def
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) propagate_unit_bt_wl_D_code
  uses isasat_input_bounded_nempty.propagate_unit_bt_wl_D_code.refine_raw
  is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_unit_bt_wl_D_code_def

lemmas propagate_unit_bt_wl_D_int_hnr[sepref_fr_rules] =
  propagate_unit_bt_wl_D_code.refine[OF isasat_input_bounded_nempty_axioms]


sepref_thm propagate_unit_bt_wl_D_fast_code
  is \<open>uncurry (PR_CONST propagate_unit_bt_wl_D_int)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow>\<^sub>a isasat_fast_assn\<close>
  supply [[goals_limit = 1]] flush_def[simp] image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[simp]
  unfolding propagate_unit_bt_wl_D_int_def cons_trail_Propagated_def[symmetric] isasat_fast_assn_def
  PR_CONST_def zero_uint32_nat_def[symmetric]
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) propagate_unit_bt_wl_D_fast_code
  uses isasat_input_bounded_nempty.propagate_unit_bt_wl_D_fast_code.refine_raw
  is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_unit_bt_wl_D_fast_code_def

lemmas propagate_unit_bt_wl_D_fast_int_hnr[sepref_fr_rules] =
  propagate_unit_bt_wl_D_fast_code.refine[OF isasat_input_bounded_nempty_axioms]

end

setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>

context isasat_input_bounded_nempty
begin

lemma empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause':
  \<open>(uncurry2 (empty_conflict_and_extract_clause_heur), uncurry2 empty_conflict_and_extract_clause) \<in>
    [empty_conflict_and_extract_clause_pre]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto intro!: empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause
      simp: empty_conflict_and_extract_clause_pre_def)

theorem
  empty_conflict_and_extract_clause_hnr[sepref_fr_rules]:
    \<open>(uncurry2 (empty_conflict_and_extract_clause_heur_code),
      uncurry2 empty_conflict_and_extract_clause) \<in>
    [empty_conflict_and_extract_clause_pre]\<^sub>a trail_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d *\<^sub>a
                        out_learned_assn\<^sup>k \<rightarrow> option_lookup_clause_assn *a
     clause_ll_assn *a uint32_nat_assn\<close>
    (is ?slow is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
  empty_conflict_and_extract_clause_fast_hnr[sepref_fr_rules]:
    \<open>(uncurry2 (empty_conflict_and_extract_clause_heur_fast_code),
      uncurry2 empty_conflict_and_extract_clause) \<in>
    [empty_conflict_and_extract_clause_pre]\<^sub>a trail_fast_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d *\<^sub>a
                        out_learned_assn\<^sup>k \<rightarrow> option_lookup_clause_assn *a
     clause_ll_assn *a uint32_nat_assn\<close>
    (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (Id \<times>\<^sub>f Id \<times>\<^sub>f Id) empty_conflict_and_extract_clause_pre
       (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (M, D) \<Rightarrow> \<lambda>outl. outl \<noteq> [] \<and> length outl \<le> uint_max)
              xa)
       (\<lambda>x. nofail (uncurry2 empty_conflict_and_extract_clause x))]\<^sub>a
     hrp_comp ((hr_comp trail_pol_assn trail_pol)\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>k)
       (Id \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow>
    hr_comp (option_lookup_clause_assn *a clause_ll_assn *a uint32_nat_assn) Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE[OF empty_conflict_and_extract_clause_heur_hnr[unfolded PR_CONST_def]
    empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause']
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def empty_conflict_and_extract_clause_pre_def)
  have im: \<open>?im' = ?im\<close>
    by simp
  have f: \<open>?f' = ?f\<close>
    by auto
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..

  have H: \<open>?cfast
    \<in> [comp_PRE (Id \<times>\<^sub>f Id \<times>\<^sub>f Id) empty_conflict_and_extract_clause_pre
       (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (M, D) \<Rightarrow> \<lambda>outl. outl \<noteq> [] \<and> length outl \<le> uint_max)
              xa)
       (\<lambda>x. nofail (uncurry2 empty_conflict_and_extract_clause x))]\<^sub>a
     hrp_comp (trail_fast_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>k)
       (Id \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow>
    hr_comp (option_lookup_clause_assn *a clause_ll_assn *a uint32_nat_assn) Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE[OF empty_conflict_and_extract_clause_heur_hnr_fast[unfolded PR_CONST_def]
    empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause']
    .
  have im: \<open>?im' = ?imfast\<close>
    by simp
  have f: \<open>?f' = ?ffast\<close>
    by auto
  show ?fast
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

sepref_thm extract_shorter_conflict_list_heur_st
  is \<open>PR_CONST extract_shorter_conflict_list_heur_st\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn *a uint32_nat_assn *a clause_ll_assn\<close>
  supply [[goals_limit=1]] empty_conflict_and_extract_clause_pre_def[simp]
  unfolding extract_shorter_conflict_list_heur_st_def PR_CONST_def isasat_assn_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    take1_def[symmetric]
  by sepref

concrete_definition (in -) extract_shorter_conflict_list_heur_st_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_list_heur_st.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_list_heur_st_code_def

lemmas extract_shorter_conflict_list_heur_st_hnr[sepref_fr_rules] =
   extract_shorter_conflict_list_heur_st_code.refine[OF isasat_input_bounded_nempty_axioms]

sepref_thm extract_shorter_conflict_list_heur_st_fast
  is \<open>PR_CONST extract_shorter_conflict_list_heur_st\<close>
  :: \<open>isasat_fast_assn\<^sup>d \<rightarrow>\<^sub>a isasat_fast_assn *a uint32_nat_assn *a clause_ll_assn\<close>
  supply [[goals_limit=1]] empty_conflict_and_extract_clause_pre_def[simp]
  unfolding extract_shorter_conflict_list_heur_st_def PR_CONST_def isasat_fast_assn_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    take1_def[symmetric]
  by sepref

concrete_definition (in -) extract_shorter_conflict_list_heur_st_fast_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_list_heur_st_fast.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_list_heur_st_fast_code_def

lemmas extract_shorter_conflict_list_heur_st_fast_hnr[sepref_fr_rules] =
   extract_shorter_conflict_list_heur_st_fast_code.refine[OF isasat_input_bounded_nempty_axioms]

sepref_register find_lit_of_max_level_wl
   extract_shorter_conflict_list_heur_st lit_of_hd_trail_st_heur propagate_bt_wl_D_heur
   propagate_unit_bt_wl_D_int
sepref_register backtrack_wl_D

sepref_thm backtrack_wl_D_code
  is \<open>PR_CONST backtrack_wl_D_nlit_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  lit_of_hd_trail_st_def[symmetric, simp]
  size_conflict_wl_def[simp]
  unfolding backtrack_wl_D_nlit_heur_def PR_CONST_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] lit_of_hd_trail_st_def[symmetric]
    cons_trail_Propagated_def[symmetric]
    size_conflict_wl_def[symmetric]
  by sepref


concrete_definition (in -) backtrack_wl_D_nlit_heur_code
   uses isasat_input_bounded_nempty.backtrack_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) backtrack_wl_D_nlit_heur_code_def

lemmas backtrack_wl_D_nlit_heur_hnr[sepref_fr_rules] =
   backtrack_wl_D_nlit_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm backtrack_wl_D_fast_code
  is \<open>PR_CONST backtrack_wl_D_nlit_heur\<close>
  :: \<open>[isasat_fast]\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> isasat_fast_assn\<close>
  supply [[goals_limit=1]]
  lit_of_hd_trail_st_def[symmetric, simp]
  size_conflict_wl_def[simp]
  unfolding backtrack_wl_D_nlit_heur_def PR_CONST_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] lit_of_hd_trail_st_def[symmetric]
    cons_trail_Propagated_def[symmetric]
    size_conflict_wl_def[symmetric]
  by sepref


concrete_definition (in -) backtrack_wl_D_nlit_heur_fast_code
   uses isasat_input_bounded_nempty.backtrack_wl_D_fast_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) backtrack_wl_D_nlit_heur_fast_code_def

lemmas backtrack_wl_D_nlit_heur_fast_hnr[sepref_fr_rules] =
   backtrack_wl_D_nlit_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

end

setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

end
