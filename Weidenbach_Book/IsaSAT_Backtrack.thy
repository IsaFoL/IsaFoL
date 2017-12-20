theory IsaSAT_Backtrack
  imports IsaSAT_Setup Watched_Literals_Heuristics
begin


(* TODO Move *)

definition swap_u_code :: "'a ::heap array \<Rightarrow> uint32 \<Rightarrow> uint32 \<Rightarrow> 'a array Heap" where
  \<open>swap_u_code xs i j = do {
     ki \<leftarrow> nth_u_code xs i;
     kj \<leftarrow> nth_u_code xs j;
     xs \<leftarrow> heap_array_set_u xs i kj;
     xs \<leftarrow> heap_array_set_u xs j ki;
     return xs
  }\<close>


lemma op_list_swap_u_hnr[sepref_fr_rules]:
  assumes p: \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(uncurry2 swap_u_code, uncurry2 (RETURN ooo op_list_swap)) \<in> 
       [\<lambda>((xs, i), j).  i < length xs \<and> j < length xs]\<^sub>a
      (array_assn R)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k  *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> array_assn R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  show ?thesis
  apply (sepref_to_hoare)
  apply (sep_auto simp: swap_u_code_def swap_def nth_u_code_def is_array_def
      array_assn_def hr_comp_def nth_nat_of_uint32_nth'[symmetric]
      list_rel_imp_same_length uint32_nat_rel_def br_def
      heap_array_set_u_def heap_array_set'_u_def Array.upd'_def
      nat_of_uint32_code[symmetric] R
      intro!: list_rel_update[of _ _ R true _ _ \<open>(_, {})\<close>, unfolded R] param_nth
      )
    subgoal for bi bia a ai bb aa b
      using param_nth[of \<open>nat_of_uint32 bi\<close> a \<open>nat_of_uint32 bi\<close> bb R']
      by (auto simp: R' pure_def)
    subgoal using p by simp
    subgoal for bi bia a ai bb aa b
      using param_nth[of \<open>nat_of_uint32 bia\<close> a \<open>nat_of_uint32 bia\<close> bb R']
      by (auto simp: R' pure_def)
    subgoal using p by simp
    done
qed

(* End Move *)

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

definition set_empty_conflict_to_none where
  \<open>set_empty_conflict_to_none D = None\<close>

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
        apply (subst  take_Suc_conv_app_nth)
        subgoal by auto
        apply (subst  take_Suc_conv_app_nth)
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
        using lits  multi_member_split[OF outl_1] \<open>i < length outl\<close> \<open>1 \<le> i\<close>
        by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset nth_list_update'
            \<open>length C = length outl\<close>)
      subgoal
        using lits  multi_member_split[OF C_1] \<open>i < length outl\<close> \<open>1 \<le> i\<close>
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
      using lits  multi_member_split[OF C_1] \<open>1 \<le> i\<close> \<open>length outl \<noteq> 1\<close>
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

(* TODO Move *)
lemma set_empty_conflict_to_none_hnr[sepref_fr_rules]:
  \<open>(return o (\<lambda>(n, xs). (True, n, xs)), RETURN o set_empty_conflict_to_none) \<in>
     [\<lambda>D. D = {#}]\<^sub>a lookup_clause_assn\<^sup>d \<rightarrow> option_lookup_clause_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: option_lookup_clause_assn_def
      option_lookup_clause_rel_def lookup_clause_assn_def
      hr_comp_def set_empty_conflict_to_none_def pure_def)
(* End Move *)

sepref_definition empty_conflict_and_extract_clause_heur_code
  is \<open>uncurry2 (PR_CONST empty_conflict_and_extract_clause_heur)\<close>
  :: \<open>[\<lambda>((M, D), outl). outl \<noteq> [] \<and> length outl \<le> uint_max]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>k \<rightarrow>
       option_lookup_clause_assn *a clause_ll_assn *a uint32_nat_assn\<close>
  supply [[goals_limit=1]] image_image[simp]
  unfolding empty_conflict_and_extract_clause_heur_def PR_CONST_def
  array_fold_custom_replicate
  by sepref

definition (in isasat_input_ops) extract_shorter_conflict_wl_nlit where
\<open>extract_shorter_conflict_wl_nlit K M NU D NE UE =
    SPEC(\<lambda>D'. D' \<noteq> None \<and> the D' \<subseteq># the D \<and> K \<in># the D' \<and>
      clause `# twl_clause_of `# mset (tl NU) + NE + UE \<Turnstile>pm the D')\<close>

definition (in isasat_input_ops) extract_shorter_conflict_wl_nlit_st
  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>
where
  \<open>extract_shorter_conflict_wl_nlit_st =
     (\<lambda>(M, N, U, D, NE, UE, WS, Q). do {
        let K = -lit_of (hd M);
        D \<leftarrow> extract_shorter_conflict_wl_nlit K M N D NE UE;
        RETURN (M, N, U, D, NE, UE, WS, Q)})\<close>

definition (in isasat_input_ops) empty_lookup_conflict_and_highest
  :: \<open>'v twl_st_wl \<Rightarrow> ('v twl_st_wl \<times> nat) nres\<close>
where
  \<open>empty_lookup_conflict_and_highest  =
     (\<lambda>(M, N, U, D, NE, UE, WS, Q). do {
        let K = -lit_of (hd M);
        let n = get_maximum_level M (remove1_mset K (the D));
        RETURN ((M, N, U, D, NE, UE, WS, Q), n)})\<close>

abbreviation (in isasat_input_ops) find_decomp_wl_nlit_prop where
  \<open>find_decomp_wl_nlit_prop \<equiv>
    (\<lambda>highest (M, N, U, D, Q', W', _, \<phi>, clvls, cach, _, outl, stats) S.
    (\<exists>K M2 M1 vm lbd. S = (M1, N, U, D, Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats) \<and> vm \<in> vmtf M1 \<and>
        (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = Suc highest))\<close>

definition (in isasat_input_ops) find_decomp_wl_nlit
:: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>find_decomp_wl_nlit highest S =
    SPEC(find_decomp_wl_nlit_prop highest S)\<close>

definition (in isasat_input_ops) propagate_bt_wl_D_ext
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>propagate_bt_wl_D_ext = (\<lambda>L highest (M, N, U, D, NE, UE, Q, W). do {
    L' \<leftarrow> find_lit_of_max_level_wl (M, N, U, D, NE, UE, Q, W) L;
    D'' \<leftarrow> list_of_mset2 (-L) L' (the D);
    RETURN (Propagated (-L) (length N) # M,
        N @ [D''], U,
          None, NE, UE, {#L#}, W(-L:= W (-L) @ [length N], L':= W L' @ [length N]))
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
  \<open>extract_shorter_conflict_list_heur_st = (\<lambda>(M, N, U, D, Q', W', vm, \<phi>, clvls, cach, lbd, outl,
       stats). do {
     ASSERT(M \<noteq> []);
     let K = lit_of (hd M);
     ASSERT(-K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
     ASSERT(D \<noteq> None \<and> delete_from_lookup_conflict_pre (-K, the D));
     let D = remove1_mset (-K) (the D);
     ASSERT(0 < length outl);
     let outl = outl[0 := -K];
     ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl N)));
     (D, cach, outl) \<leftarrow> minimize_and_extract_highest_lookup_conflict M N D cach lbd outl;
     let cach = empty_cach cach;
     ASSERT(empty_conflict_and_extract_clause_pre ((M, D), outl));
     (D, C, n) \<leftarrow> empty_conflict_and_extract_clause M D outl;
     RETURN ((M, N, U, D, Q', W', vm, \<phi>, clvls, cach, lbd, take 1 outl, stats), n, C)
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
      apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, _). length support' - i)\<close>])
      subgoal by auto
      subgoal by (rule init)
      subgoal by auto
      subgoal by (rule valid_length)
      subgoal by (rule set_next)
      subgoal by auto
      subgoal by (rule final)
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
  \<open>(empty_cach_code,
   RETURN \<circ> empty_cach_ref)
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
    using that by (auto simp: comp_PRE_def twl_st_heur_pol_def trail_pol_def
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
    using that by (auto simp: comp_PRE_def twl_st_heur_pol_def trail_pol_def
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

sepref_thm backtrack_wl_D_code
  is \<open>PR_CONST extract_shorter_conflict_list_heur_st\<close>
  :: \<open>twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_heur_assn *a uint32_nat_assn *a clause_ll_assn\<close>
  supply [[goals_limit=1]](*  backtrack_wl_D_nlit_invariants[simp] *)
  unfolding extract_shorter_conflict_list_heur_st_def PR_CONST_def twl_st_heur_assn_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
  apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
                      apply sepref_dbg_trans_step_keep
  oops

definition (in isasat_input_ops)  rescore_clause
  :: \<open>nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> phase_saver \<Rightarrow>
    (vmtf_remove_int \<times> phase_saver) nres\<close>
where
  \<open>rescore_clause C M vm \<phi> = SPEC (\<lambda>(vm', \<phi>' :: bool list). vm' \<in> vmtf M \<and> phase_saving \<phi>')\<close>


definition (in isasat_input_ops) flush
  :: \<open>(nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> vmtf_remove_int nres\<close>
where
  \<open>flush M _ = SPEC (\<lambda>vm'. vm' \<in> vmtf M)\<close>

definition (in isasat_input_ops) propagate_bt_wl_D_heur
  :: \<open>nat literal \<Rightarrow> nat clause_l \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>propagate_bt_wl_D_heur = (\<lambda>L C (M, N, U, D, Q, W, vm, \<phi>, _, cach). do {
      ASSERT(phase_saving \<phi> \<and> vm \<in> vmtf M \<and> undefined_lit M (-L) \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
         nat_of_lit (C!1) < length W \<and> nat_of_lit (-L) < length W);
      ASSERT(length C > 1);
      let L' = C!1;
      ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n (mset C));
      (vm, \<phi>) \<leftarrow> rescore_clause C M vm \<phi>;
      vm \<leftarrow> flush M vm;
      let W = W[nat_of_lit (- L) := W ! nat_of_lit (- L) @ [length N]];
      let W = W[nat_of_lit L' := W!nat_of_lit L' @ [length N]];
      RETURN (Propagated (- L) (length N) # M, N @ [C], U, D, {#L#}, W, vm, \<phi>, zero_uint32_nat,
         cach)
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
  \<open>propagate_unit_bt_wl_D_int = (\<lambda>L (M, N, U, D, Q, W, vm, \<phi>). do {
      ASSERT(undefined_lit M L \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> vm \<in> vmtf M);
      vm \<leftarrow> flush M vm;
      RETURN (Propagated (- L) 0 # M, N, U, D, {#L#}, W, vm, \<phi>)})\<close>

(* TODO ded-uplicate definitions *)
definition (in isasat_input_ops) find_decomp_wvmtf_ns_pre where
  \<open>find_decomp_wvmtf_ns_pre = (\<lambda>((M, highest), vm).
      \<exists>N U D NE UE Q W. twl_struct_invs (twl_st_of_wl None (M, N, U, D, NE, UE, Q, W)) \<and>
       highest < count_decided M \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
       vm \<in> vmtf M)\<close>

definition  (in isasat_input_ops) find_decomp_wl_pre
   :: \<open>nat \<times> twl_st_wl_heur \<Rightarrow> bool\<close>
where
   \<open>find_decomp_wl_pre =  (\<lambda>(highest, T).
       find_decomp_wvmtf_ns_pre ((get_trail_wl_heur T, highest), get_vmtf_heur T))\<close>

definition (in isasat_input_ops) backtrack_wl_D_nlit_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>backtrack_wl_D_nlit_heur S =
    do {
      ASSERT(backtrack_wl_D_heur_inv S);
      ASSERT(get_trail_wl_heur S \<noteq> []);
      let L = lit_of_hd_trail_st_heur S;
      (S, n, C) \<leftarrow> extract_shorter_conflict_list_heur_st S;

      ASSERT(find_decomp_wl_pre (n, S));
      S \<leftarrow> find_decomp_wl_nlit n S;

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
definition (in -)del_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>del_conflict_wl = (\<lambda>(M, N, U, D, NE, UE, Q, W). (M, N, U, None, NE, UE, Q, W))\<close>

context conflict_driven_clause_learning\<^sub>W
begin

lemma 
  fixes S
  assumes
     nss: \<open>no_step skip S\<close> and
     nsr: \<open>no_step resolve S\<close> and
     invs: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
     stgy: \<open>cdcl\<^sub>W_stgy_invariant S\<close> and
     confl: \<open>conflicting S \<noteq> None\<close> and
     confl': \<open>conflicting S \<noteq> Some {#}\<close>
   shows no_skip_no_resolve_single_highest_level:
    \<open>the (conflicting S) =
       add_mset (-(lit_of (hd (trail S)))) {#L \<in># the (conflicting S).
         get_level (trail S) L < local.backtrack_lvl S#}\<close> (is ?A) and
      no_skip_no_resolve_level_lvl_nonzero:
    \<open>0 < backtrack_lvl S\<close> (is ?B) and
      no_skip_no_resolve_level_get_maximum_lvl_le:
    \<open>get_maximum_level (trail S) (remove1_mset (-(lit_of (hd (trail S)))) (the (conflicting S)))
        < backtrack_lvl S\<close> (is ?C)
proof -
  define K where \<open>K \<equiv> lit_of (hd (trail S))\<close>
  have K: \<open>-K \<in># the (conflicting S)\<close>
    using no_step_skip_hd_in_conflicting[OF stgy invs nss confl confl']
    unfolding K_def .
  have
    \<open>no_strange_atm S\<close> and
    lev: \<open>cdcl\<^sub>W_M_level_inv S\<close> and
    \<open>\<forall>s\<in>#learned_clss S. \<not> tautology s\<close> and
    dist: \<open>distinct_cdcl\<^sub>W_state S\<close> and
    conf: \<open>cdcl\<^sub>W_conflicting S\<close> and
    \<open>all_decomposition_implies_m (local.clauses S)
      (get_all_ann_decomposition (trail S))\<close> and
    learned: \<open>cdcl\<^sub>W_learned_clause S\<close>
    using invs unfolding cdcl\<^sub>W_all_struct_inv_def
    by auto

  obtain D where
    D[simp]: \<open>conflicting S = Some (add_mset (-K) D)\<close>
    using confl K by (auto dest: multi_member_split)

  have dist: \<open>distinct_mset (the (conflicting S))\<close>
    using dist confl unfolding distinct_cdcl\<^sub>W_state_def by auto
  then have [iff]: \<open>L \<notin># remove1_mset L (the (conflicting S))\<close> for L
    by (meson distinct_mem_diff_mset union_single_eq_member)
  from this[of K] have [simp]: \<open>-K \<notin># D\<close> using dist by auto

  have nd: \<open>no_dup (trail S)\<close>
    using lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
  have CNot: \<open>trail S \<Turnstile>as CNot (add_mset (-K) D)\<close>
    using conf unfolding cdcl\<^sub>W_conflicting_def
    by fastforce
  then have tr: \<open>trail S \<noteq> []\<close>
    by auto
  have [simp]: \<open>K \<notin># D\<close>
    using nd K_def tr CNot unfolding true_annots_true_cls_def_iff_negation_in_model
    by (cases \<open>trail S\<close>)
       (auto simp: uminus_lit_swap Decided_Propagated_in_iff_in_lits_of_l dest!: multi_member_split)
  have H1:
    \<open>0 < backtrack_lvl S\<close>
  proof (cases \<open>is_proped (hd (trail S))\<close>)
    case proped: True
    obtain C M where
      [simp]: \<open>trail S = Propagated K C # M\<close>
      using tr proped K_def
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: K_def)
    have \<open>a @ Propagated L mark # b = Propagated K C # M \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
      using conf unfolding cdcl\<^sub>W_conflicting_def
      by fastforce
    from this[of \<open>[]\<close>] have [simp]: \<open>K \<in># C\<close> \<open>M \<Turnstile>as CNot (remove1_mset K C)\<close>
      by auto
    have [simp]: \<open>get_maximum_level (Propagated K C # M) D = get_maximum_level M D\<close>
      by (rule get_maximum_level_skip_first)
        (auto simp: atms_of_def atm_of_eq_atm_of uminus_lit_swap[symmetric])

    have \<open>get_maximum_level M D < count_decided M\<close>
      using nsr tr confl K proped count_decided_ge_get_maximum_level[of M D]
      by (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis by simp
  next
    case proped: False
    have \<open>get_maximum_level (tl (trail S)) D < count_decided (trail S)\<close>
      using tr confl K proped count_decided_ge_get_maximum_level[of \<open>tl (trail S)\<close> D]
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
         (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis
      by simp
  qed
  show H2: ?C
  proof (cases \<open>is_proped (hd (trail S))\<close>)
    case proped: True
    obtain C M where
      [simp]: \<open>trail S = Propagated K C # M\<close>
      using tr proped K_def
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: K_def)
    have \<open>a @ Propagated L mark # b = Propagated K C # M \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
      using conf unfolding cdcl\<^sub>W_conflicting_def
      by fastforce
    from this[of \<open>[]\<close>] have [simp]: \<open>K \<in># C\<close> \<open>M \<Turnstile>as CNot (remove1_mset K C)\<close>
      by auto
    have [simp]: \<open>get_maximum_level (Propagated K C # M) D = get_maximum_level M D\<close>
      by (rule get_maximum_level_skip_first)
        (auto simp: atms_of_def atm_of_eq_atm_of uminus_lit_swap[symmetric])

    have \<open>get_maximum_level M D < count_decided M\<close>
      using nsr tr confl K proped count_decided_ge_get_maximum_level[of M D]
      by (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis by simp
  next
    case proped: False
    have \<open>get_maximum_level (tl (trail S)) D = get_maximum_level (trail S) D\<close>
      apply (rule get_maximum_level_cong)
      using K_def \<open>- K \<notin># D\<close> \<open>K \<notin># D\<close> 
      apply (cases \<open>trail S\<close>)
      by (auto simp: get_level_cons_if atm_of_eq_atm_of)
    moreover have \<open>get_maximum_level (tl (trail S)) D < count_decided (trail S)\<close>
      using tr confl K proped count_decided_ge_get_maximum_level[of \<open>tl (trail S)\<close> D]
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
         (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    ultimately show ?thesis
      by (simp add: K_def)
  qed

  have H:
    \<open>get_level (trail S) L < local.backtrack_lvl S\<close>
    if \<open>L \<in># remove1_mset (-K) (the (conflicting S))\<close>
    for L
  proof (cases \<open>is_proped (hd (trail S))\<close>)
    case proped: True
    obtain C M where
      [simp]: \<open>trail S = Propagated K C # M\<close>
      using tr proped K_def
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: K_def)
    have \<open>a @ Propagated L mark # b = Propagated K C # M \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
      using conf unfolding cdcl\<^sub>W_conflicting_def
      by fastforce
    from this[of \<open>[]\<close>] have [simp]: \<open>K \<in># C\<close> \<open>M \<Turnstile>as CNot (remove1_mset K C)\<close>
      by auto
    have [simp]: \<open>get_maximum_level (Propagated K C # M) D = get_maximum_level M D\<close>
      by (rule get_maximum_level_skip_first)
        (auto simp: atms_of_def atm_of_eq_atm_of uminus_lit_swap[symmetric])

    have \<open>get_maximum_level M D < count_decided M\<close>
      using nsr tr confl K that proped count_decided_ge_get_maximum_level[of M D]
      by (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis
      using get_maximum_level_ge_get_level[of L D M] that
      by (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
  next
    case proped: False
    have L_K: \<open>L \<noteq> - K\<close> \<open>-L \<noteq> K\<close> \<open>L \<noteq> -lit_of (hd (trail S))\<close>
      using that by (auto simp: uminus_lit_swap K_def[symmetric])
    have \<open>L \<noteq> lit_of (hd (trail S))\<close>
      using tr that K_def \<open>K \<notin># D\<close>
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
         (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)

    have \<open>get_maximum_level (tl (trail S)) D < count_decided (trail S)\<close>
      using tr confl K that proped count_decided_ge_get_maximum_level[of \<open>tl (trail S)\<close> D]
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
         (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis
      using get_maximum_level_ge_get_level[of L D \<open>(trail S)\<close>] that tr L_K \<open>L \<noteq> lit_of (hd (trail S))\<close>
        count_decided_ge_get_level[of \<open>tl (trail S)\<close> L] proped
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
  qed
  have [simp]: \<open>get_level (trail S) K = local.backtrack_lvl S\<close>
    using tr K_def
    by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
      (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
  show ?A
    apply (rule distinct_set_mset_eq)
    subgoal using dist by auto
    subgoal using dist by (auto simp: distinct_mset_filter K_def[symmetric])
    subgoal using H by (auto simp: K_def[symmetric])
    done
  show ?B
    using H1 .
qed

end

(* TODO Move closer to clauses_twl_st_of_wl *)
lemma (in -) clauses_twl_st_of:
  \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (M, N, U, y, NE, UE, Q, W))) =
     mset `# mset (tl N) + NE + UE\<close>
  by (auto simp del: append_take_drop_id simp: mset_take_mset_drop_mset' clauses_def)

context isasat_input_ops
begin

lemma twl_struct_invs_conflit_not_tauto:
  assumes
    struct: \<open>twl_struct_invs (twl_st_of_wl b S)\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close>
  shows \<open>\<not>tautology (the (get_conflict_wl S))\<close>
proof -
  obtain M N U D NE UE Q W where
    S: \<open>S = (M, N, U, D, NE, UE, Q, W)\<close>
    by (cases S)
   have
      not_none: \<open>D \<noteq> None\<close>
      using assms unfolding S backtrack_wl_D_inv_def
      by (auto simp: backtrack_wl_inv_def backtrack_l_inv_def
          simp del: twl_st_of.simps)
    have
      lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl b S))\<close> and
      conf: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl b S))\<close>
      using assms unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by (auto simp: S twl_struct_invs_def simp del: twl_st_of.simps)

    show ?thesis
      apply (rule consistent_CNot_not_tautology[of \<open>lits_of_l (get_trail_wl S)\<close>])
      subgoal using lev unfolding  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        by (cases S; cases b) auto
      subgoal
        using conf confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def true_annots_true_cls
        by (cases S; cases b) auto
      done
qed

end
(* End Move *)

context isasat_input_bounded_nempty
begin

definition twl_st_heur_bt :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_bt =
  {((M', N', U', D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats), (M, N, U, D, NE, UE, Q, W)).
    M = M' \<and> N' = N \<and> U' = U \<and>
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

lemma backtrack_wl_D_nlit_backtrack_wl_D:
  \<open>(backtrack_wl_D_nlit_heur, backtrack_wl_D) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  have backtrack_wl_D_nlit_heur_alt_def: \<open>backtrack_wl_D_nlit_heur S =
    do {
      ASSERT(backtrack_wl_D_heur_inv S);
      ASSERT(get_trail_wl_heur S \<noteq> []);
      let L = lit_of_hd_trail_st_heur S;
      (S, n, C) \<leftarrow> extract_shorter_conflict_list_heur_st S;
      ASSERT(find_decomp_wl_pre (n, S));
      S \<leftarrow> find_decomp_wl_nlit n S;

      if size C > 1
      then do {
        let _ = C ! 1;
        propagate_bt_wl_D_heur L C S
      }
      else do {
        propagate_unit_bt_wl_D_int L S
     }
  }\<close> for S
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
              equality_except_conflict T S \<and>
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
    obtain M N U D NE UE Q W where
      S: \<open>S = (M, N, U, D, NE, UE, Q, W)\<close>
      by (cases S)
    obtain W' vm \<phi> clvls cach lbd outl stats where
      S': \<open>S' = (M, N, U, D, Q, W', vm, \<phi>, clvls, cach, lbd, outl, stats)\<close>
      using S'_S by (cases S') (auto simp: twl_st_heur_def S)
    have
      \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> and
      vm: \<open>vm \<in> vmtf M\<close> and
      \<open>phase_saving \<phi>\<close> and
      \<open>no_dup M\<close> and
      \<open>clvls \<in> counts_maximum_level M D\<close> and
      cach_empty: \<open>cach_refinement_empty cach\<close> and
      \<open>out_learned M D outl\<close>
      using S'_S unfolding S S'
      by (auto simp: twl_st_heur_def S)

    have
      not_none: \<open>D \<noteq> None\<close> and
      trail_nempty: \<open>M \<noteq> []\<close> and
      nss: \<open>no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None (M, N, U, D, NE, UE, {#}, Q)))\<close> and
      nsr: \<open>no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of None (M, N, U, D, NE, UE, {#}, Q)))\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of None (M, N, U, D, NE, UE, {#}, Q))\<close> and
      stgy_invs: \<open>twl_stgy_invs (twl_st_of None (M, N, U, D, NE, UE, {#}, Q))\<close> and
      list_invs: \<open>twl_list_invs (M, N, U, D, NE, UE, {#}, Q)\<close> and
      \<open>correct_watching (M, N, U, D, NE, UE, Q, W)\<close> and
      not_empty: \<open>the D \<noteq> {#}\<close> and
      \<L>\<^sub>i\<^sub>n : \<open>literals_are_\<L>\<^sub>i\<^sub>n (M, N, U, D, NE, UE, Q, W)\<close>
      using inv unfolding S backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
      by (auto simp: 
          simp del: twl_st_of.simps)
    then have all_struct:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of None (M, N, U, D, NE, UE, {#}, Q)))\<close>
      by (auto simp: backtrack_wl_D_inv_def S backtrack_wl_inv_def backtrack_l_inv_def
          twl_stgy_invs_def twl_struct_invs_def
          simp del: twl_st_of.simps)
    then have uL_D: \<open>- lit_of (hd M) \<in># the D\<close>
      using cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of
          \<open>state\<^sub>W_of (twl_st_of_wl None S)\<close>] nss not_none not_empty stgy_invs trail_nempty
      by (auto simp: S twl_stgy_invs_def)
    have
      \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of None (M, N, U, D, NE, UE, {#}, Q)))\<close> and
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of None (M, N, U, D, NE, UE, {#}, Q)))\<close> and
      \<open>\<forall>s\<in>#learned_clss (state\<^sub>W_of (twl_st_of None (M, N, U, D, NE, UE, {#}, Q))).
        \<not> tautology s\<close> and
      dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state
      (state\<^sub>W_of (twl_st_of None (M, N, U, D, NE, UE, {#}, Q)))\<close> and
      confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting
      (state\<^sub>W_of (twl_st_of None (M, N, U, D, NE, UE, {#}, Q)))\<close> and
      \<open>all_decomposition_implies_m
      (cdcl\<^sub>W_restart_mset.clauses
        (state\<^sub>W_of (twl_st_of None (M, N, U, D, NE, UE, {#}, Q))))
      (get_all_ann_decomposition
        (trail (state\<^sub>W_of (twl_st_of None (M, N, U, D, NE, UE, {#}, Q)))))\<close> and
      learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause
      (state\<^sub>W_of (twl_st_of None (M, N, U, D, NE, UE, {#}, Q)))\<close>
      using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    have M_\<L>\<^sub>i\<^sub>n: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl (M, N, U, D, NE, UE, Q, W))\<close>
      using literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail[OF \<L>\<^sub>i\<^sub>n, of None] struct_invs
      by auto
    have dist_D: \<open>distinct_mset (the (get_conflict_wl S))\<close>
      using dist not_none unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def S
      by auto
    have \<open>the (conflicting (state\<^sub>W_of (twl_st_of_wl None S))) =
     add_mset (- lit_of (cdcl\<^sub>W_restart_mset.hd_trail (state\<^sub>W_of (twl_st_of_wl None S))))
        {#L \<in># the (conflicting (state\<^sub>W_of (twl_st_of_wl None S))).
          get_level (trail (state\<^sub>W_of (twl_st_of_wl None S))) L
             < backtrack_lvl (state\<^sub>W_of (twl_st_of_wl None S))#}\<close>
      apply (rule cdcl\<^sub>W_restart_mset.no_skip_no_resolve_single_highest_level)
      subgoal using nss unfolding S by simp
      subgoal using nsr unfolding S by simp
      subgoal using struct_invs unfolding twl_struct_invs_def S by simp
      subgoal using stgy_invs unfolding twl_stgy_invs_def S by simp
      subgoal using not_none by (simp add: S)
      subgoal using not_empty not_none by (auto simp add: S)
      done
    then have D_filter: \<open>the D = add_mset (- lit_of (hd M)) {#L \<in># the D. get_level M L < count_decided M#}\<close>
      using trail_nempty by (simp add: S)
    have tl_outl_D: \<open>mset (tl (outl[0 := - lit_of (hd M)])) = remove1_mset (outl[0 := - lit_of (hd M)] ! 0) (the D)\<close>
      using \<open>out_learned M D outl\<close> \<open>D \<noteq> None\<close>
      apply (subst D_filter)
      by (cases outl) (auto simp: out_learned_def S)
    let ?D = \<open>remove1_mset (- lit_of (hd M)) (the D)\<close>
    have \<L>\<^sub>i\<^sub>n_S: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S))\<close>
      apply (rule literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[of _ None])
      using \<L>\<^sub>i\<^sub>n not_none struct_invs by (auto simp: S)
    then have \<L>\<^sub>i\<^sub>n_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n ?D\<close>
      unfolding S by (auto intro: literals_are_in_\<L>\<^sub>i\<^sub>n_mono)
    have tauto_confl: \<open>\<not> tautology (the (get_conflict_wl S))\<close>
      apply (rule twl_struct_invs_conflit_not_tauto[of None S])
      using struct_invs not_none unfolding S by auto
    from not_tautology_mono[OF _ this, of ?D] have tauto_D: \<open>\<not> tautology ?D\<close>
      by (auto simp: S)
    have entailed:
      \<open>mset `# mset (tl (get_clauses_wl S)) +
    (get_unit_learned S + get_unit_init_clss S) \<Turnstile>pm
    add_mset (- lit_of (hd M)) (remove1_mset (- lit_of (hd M)) (the D))\<close>
      using uL_D learned not_none unfolding  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
        clauses_twl_st_of
      by (auto simp: S ac_simps mset_take_mset_drop_mset get_unit_learned_def
          get_unit_init_clss_def)
    have mini: \<open>minimize_and_extract_highest_lookup_conflict (get_trail_wl S) (get_clauses_wl S)
              ?D cach lbd (outl[0 := - lit_of (hd M)])
          \<le> \<Down> {((E, s, outl), E'). E = E' \<and> mset (tl outl) = E \<and>
                 outl ! 0 = - lit_of (hd M) \<and> E' \<subseteq># remove1_mset (- lit_of (hd M)) (the D) \<and>
                outl \<noteq> []}
              (iterate_over_conflict (- lit_of (hd M)) (get_trail_wl S)
                (mset `# mset (tl (get_clauses_wl S)))
                (get_unit_learned S + get_unit_init_clss S) ?D)\<close>
      apply (rule minimize_and_extract_highest_lookup_conflict_iterate_over_conflict[of
         \<open>outl [0 := - lit_of (hd M)]\<close>
         \<open>remove1_mset _ (the D)\<close> S cach \<open>-lit_of (hd M)\<close> lbd])
      subgoal using \<open>out_learned M D outl\<close> tl_outl_D
        by (auto simp: out_learned_def)
      subgoal using confl not_none unfolding S cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        by (auto simp: true_annot_CNot_diff)
      subgoal
        using dist not_none unfolding S cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        by auto
      subgoal using tauto_D .
      subgoal using M_\<L>\<^sub>i\<^sub>n unfolding S by simp
      subgoal using struct_invs unfolding S by simp
      subgoal using list_invs unfolding S by simp
      subgoal using M_\<L>\<^sub>i\<^sub>n cach_empty unfolding S cach_refinement_empty_def conflict_min_analysis_inv_def
        by (auto dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms)
      subgoal by (rule entailed)
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
                (mset `# mset (tl N))
                (get_unit_learned S + get_unit_init_clss S) ?D)\<close>
      unfolding S by auto
     have mini: \<open>minimize_and_extract_highest_lookup_conflict M N
              ?D cach lbd (outl[0 := - lit_of (hd M)])
          \<le> \<Down> {((E, s, outl), E'). E = E' \<and> mset (tl outl) = E \<and>
                 outl ! 0 = - lit_of (hd M) \<and> E' \<subseteq># remove1_mset (- lit_of (hd M)) (the D) \<and>
                 outl \<noteq> []}
              (SPEC (\<lambda>D'. D' \<subseteq># ?D \<and>  mset `# mset (tl N) +
                      (get_unit_learned S + get_unit_init_clss S) \<Turnstile>pm add_mset (- lit_of (hd M)) D'))\<close>
       apply (rule order.trans)
        apply (rule mini)
       apply (rule conc_fun_mono)
       apply (rule order.trans)
        apply (rule iterate_over_conflict_spec)
       subgoal using entailed by (auto simp: S)
       subgoal
        using dist not_none unfolding S cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        by auto
      subgoal by auto
      done
    have uM_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>- lit_of (hd M) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using M_\<L>\<^sub>i\<^sub>n trail_nempty by (cases M)
        (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons uminus_\<A>\<^sub>i\<^sub>n_iff)
 
    have ref: \<open>RES (\<Union>(a, C,
              n)\<in>{(D, C, n).
                   D = None \<and>
                   mset C = mset outl' \<and>
                   C ! 0 = outl' ! 0 \<and>
                   (1 < length C \<longrightarrow>
                    highest_lit M (mset (tl C))
                     (Some (C ! 1, get_level M (C ! 1)))) \<and>
                   (1 < length C \<longrightarrow> n = get_level M (C ! 1)) \<and>
                   (length C = 1 \<longrightarrow> n = 0)}.
              {((M, N, U, a, Q, W', vm, \<phi>, clvls, empty_cach cach', lbd, take 1 outl',
                 stats),
                n, C)})
      \<le> \<Down> ?shorter
          (SPEC (\<lambda>S. \<exists>D'. D' \<subseteq># the D \<and>
                          S = (M, N, U, Some D', NE, UE, Q, W) \<and>
                          clauses (twl_clause_of `# mset (tl N)) + NE + UE \<Turnstile>pm D' \<and>
                          - lit_of (hd M) \<in># D'))\<close>
      (is \<open>RES ?res \<le> \<Down> ?R (RES ?S)\<close>)
      if
        incl: \<open>mset (tl outl') \<subseteq># remove1_mset (- lit_of (hd M)) (the D)\<close> and
        ent: \<open>mset `# mset (tl N) + (get_unit_learned S + get_unit_init_clss S) \<Turnstile>pm
     add_mset (- lit_of (hd M)) (mset (tl outl'))\<close> and
        outl0: \<open>outl' ! 0 = - lit_of (hd M)\<close> and
        \<open>mset (tl outl') \<subseteq># remove1_mset (- lit_of (hd M)) (the D)\<close> and
        \<open>outl' \<noteq> []\<close>
      for outl' cach'
    proof -
      have H: \<open>(M, N, U, Some (mset (snd (snd s))), NE, UE, Q, W) \<in> ?S\<close> (is ?TS) and
        H': \<open>(s, M, N, U, Some (mset (snd (snd s))), NE, UE, Q, W) \<in> ?R\<close> (is ?TR)
        if \<open>s \<in> ?res\<close>
        for s :: \<open>twl_st_wl_heur \<times> nat \<times> nat clause_l\<close>
      proof -
        obtain S' n c where
          s: \<open>s = (S', n, c)\<close>
          by (cases s)
        have
          \<open>mset c = mset outl'\<close> and
          \<open>c ! 0 = outl' ! 0\<close> and
          S': \<open>S' = (M, N, U, None, Q, W', vm, \<phi>, clvls, empty_cach cach', lbd, take 1 outl', stats)\<close> and
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
        have ent: \<open>mset ` set (tl N) \<union> set_mset NE \<union> set_mset UE \<Turnstile>p add_mset (- lit_of (hd M)) (mset (tl c))\<close>
          using ent
          unfolding s by (auto simp: mset_take_mset_drop_mset outl0 S
              get_unit_learned_def get_unit_init_clss_def ac_simps)
        show ?TS
          using incl ent outl0
          unfolding s \<open>mset (tl outl') = mset (tl c)\<close> \<open>c ! 0 = outl' ! 0\<close>[symmetric]
          by (auto simp: mset_take_mset_drop_mset S
              get_unit_learned_def get_unit_init_clss_def insert_subset_eq_iff uL_D)
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
          (M, N, U, Some (add_mset (outl' ! 0) (mset (tl outl'))), NE, UE, Q, W)) \<in> twl_st_heur\<close>
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
            using uL_D by auto
          have \<open>add_mset (- lit_of (hd M)) (mset (tl c)) \<subseteq># the D\<close>
          using subset_mset.add_left_mono[OF incl, of \<open>{#- lit_of (hd M)#}\<close>, unfolded 1] \<open>outl' \<noteq> []\<close>
          by auto
      } note incl_c_d = this
      moreover {
        have H: \<open>twl_struct_invs (twl_st_of None (M, N, U, D, NE, UE, {#}, Q))\<close>
          using M_\<L>\<^sub>i\<^sub>n struct_invs
          by (auto 5 5 simp: S' simp del: twl_st_of.simps)
        have K: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant 
              (state\<^sub>W_of (twl_st_of None (M, N, U, D, NE, UE, {#}, Q)))\<close>
          using stgy_invs not_none not_empty confl unfolding twl_stgy_invs_def
          by auto
        have \<open>get_maximum_level M (mset (tl c)) \<le> get_maximum_level M (remove1_mset (-lit_of (hd M)) (the D))\<close>
          apply (rule get_maximum_level_mono)
          using incl by auto
        also have K: \<open>get_maximum_level M (remove1_mset (-lit_of (hd M)) (the D)) < count_decided M\<close>
          using cdcl\<^sub>W_restart_mset.no_skip_no_resolve_level_get_maximum_lvl_le[OF nss nsr all_struct K]
            not_none not_empty confl trail_nempty
          by auto
        finally have \<open>get_maximum_level M (mset (tl c)) < count_decided M\<close> .
        then  have \<open>n < count_decided M\<close>
          by (auto simp: n mset_tl_c_remove)
        then have \<open>find_decomp_wl_pre (n, S')\<close>
          using M_\<L>\<^sub>i\<^sub>n struct_invs vm
          unfolding find_decomp_wl_pre_def find_decomp_wvmtf_ns_pre_def
          by (fastforce simp: S' simp del: twl_st_of.simps)
      }
      ultimately show ?TR
          using \<open>c \<noteq> []\<close> outl0 not_none \<L>\<^sub>i\<^sub>n_S dist_D uM_\<L>\<^sub>a\<^sub>l\<^sub>l 
          unfolding s \<open>c ! 0 = outl' ! 0\<close>[symmetric] by (auto simp: S' S hd_conv_nth)
      qed
      show ?thesis
        apply (rule RES_refine)
        unfolding Bex_def
        apply (rule_tac x= \<open>(M, N, U, Some (mset (snd (snd s))), NE, UE, Q, W)\<close> in exI)
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
      using not_none uL_D uM_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding delete_from_lookup_conflict_pre_def
      by auto
    have pre2: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl N)) \<equiv> True\<close>
      using M_\<L>\<^sub>i\<^sub>n literals_are_\<L>\<^sub>i\<^sub>n_clauses_literals_are_in_\<L>\<^sub>i\<^sub>n[OF \<L>\<^sub>i\<^sub>n, of None]
        struct_invs
      by (auto simp: S)
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
        uL_D by (cases E) auto
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
      \<le> \<Down>  {(U, U''). (U, U'') \<in> twl_st_heur_bt \<and> equality_except_trail U'' T' \<and>
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
      T': \<open>T' = (M, N, U, D, NE, UE, Q, W)\<close>
      by (cases T')
    obtain W' vm \<phi> clvls cach lbd outl stats where
      T: \<open>T = (M, N, U, None, Q, W', vm, \<phi>, clvls, cach, lbd, outl, stats)\<close>
      using TT' by (cases T) (auto simp: twl_st_heur_def T' del_conflict_wl_def)
    have n: \<open>n = get_maximum_level M (remove1_mset (- lit_of (hd M)) (mset C))\<close> and
      eq: \<open>equality_except_conflict T' S'\<close> and
      \<open>the D = mset C\<close> \<open>D \<noteq> None\<close> and
      \<open>no_dup M\<close>
      using TT' by (auto simp: T T' twl_st_heur_def)
    have [simp]: \<open>get_trail_wl S' = M\<close>
      using eq \<open>the D = mset C\<close> \<open>D \<noteq> None\<close> by (cases S'; auto simp: T')
    have H: \<open>\<exists>s'\<in>{S. \<exists>K M2 M1.
                  S = (M1, N, U, D, NE, UE, Q, W) \<and>
                  (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
                  get_level M K = get_maximum_level M
                    (remove1_mset (- lit_of (hd (get_trail_wl S'))) (the D)) + 1}.
         (s, s') \<in> ?find_decomp\<close>
         (is \<open>\<exists>s' \<in> ?H. _\<close>)
      if s: \<open>s \<in> Collect (find_decomp_wl_nlit_prop n (M, N, U, None, Q, W', vm, \<phi>, clvls, cach, lbd, outl, stats))\<close>
      for s :: \<open>twl_st_wl_heur\<close>
    proof -
      obtain K M2 M1 vm' lbd' where
        s: \<open>s = (M1, N, U, None,  Q, W', vm', \<phi>, clvls, cach, lbd', outl, stats)\<close> and
        decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
        n_M_K: \<open>get_level M K = Suc n\<close> and
        vm': \<open>vm' \<in> vmtf M1\<close>
        using s by auto
      let ?T' = \<open>(M1, N, U, D, NE, UE, Q, W)\<close>
      have \<open>?T' \<in> ?H\<close>
        using decomp n n_M_K \<open>the D = mset C\<close> by (auto simp: T')
      have [simp]: \<open>NO_MATCH [] M \<Longrightarrow> out_learned M None ai \<longleftrightarrow> out_learned [] None ai\<close> for M ai
        by (auto simp: out_learned_def)
      have \<open>no_dup M1\<close>
        using \<open>no_dup M\<close> decomp by (auto dest!: get_all_ann_decomposition_exists_prepend
            dest: no_dup_appendD)
      have twl: \<open>((M1, N, U, None, Q, W', vm', \<phi>, clvls, cach, lbd', outl, stats),
           M1, N, U, D, NE, UE, Q, W) \<in> twl_st_heur_bt\<close>
        using TT' vm' \<open>no_dup M1\<close> by (auto simp: T T' twl_st_heur_bt_def twl_st_heur_def
            del_conflict_wl_def)
      have \<open>equality_except_trail (M1, N, U, D, NE, UE, Q, W) T'\<close>
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
    obtain M N u NE UE Q W where
      T': \<open>T' = (M, N, u, Some (mset C), NE, UE, Q, W)\<close> and
      \<open>C \<noteq> []\<close>
      using \<open>(TnC, T') \<in> ?shorter S'\<close> \<open>1 < length C\<close> find_decomp
      apply (cases U'; cases T'; cases S')
      by (auto simp: find_lit_of_max_level_wl_def)

    obtain M' K M2 where
      U': \<open>U' = (M', N, u, Some (mset C), NE, UE, Q, W)\<close> and
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
      \<open>no_dup (trail (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S'))))\<close>
      using that unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
      twl_struct_invs_def twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by fast+
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
      T'S': \<open>equality_except_conflict T' S'\<close> and
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
      U'U': \<open>equality_except_trail U' T'\<close> and
      lev_K: \<open>get_level (get_trail_wl T') K = Suc (get_maximum_level (get_trail_wl T')
           (remove1_mset (- lit_of (hd (get_trail_wl T')))
             (the (get_conflict_wl T'))))\<close> and
      decomp: \<open>(Decided K # get_trail_wl U', M2) \<in> set (get_all_ann_decomposition (get_trail_wl T'))\<close>
      using find_decomp
      by (auto)

    obtain M N u NE UE Q W where
      T': \<open>T' = (M, N, u, Some (mset C), NE, UE, Q, W)\<close> and
      \<open>C \<noteq> []\<close>
      using TT' T_C \<open>1 < length C\<close>
      apply (cases T'; cases S')
      by (auto simp: find_lit_of_max_level_wl_def)
    obtain D' where
      S': \<open>S' = (M, N, u, D', NE, UE, Q, W)\<close>
      using T'S' \<open>1 < length C\<close>
      apply (cases S')
      by (auto simp: find_lit_of_max_level_wl_def T' del_conflict_wl_def)

    obtain M1 where
      U': \<open>U' = (M1, N, u, Some (mset C), NE, UE, Q, W)\<close>
      using \<open>(TnC, T') \<in> ?shorter S'\<close> \<open>1 < length C\<close> find_decomp
      apply (cases U')
      by (auto simp: find_lit_of_max_level_wl_def T')
    obtain vm' W' \<phi> clvls cach lbd outl stats where
        U: \<open>U = (M1, N, u, None, Q, W', vm', \<phi>, clvls, cach, lbd, outl, stats)\<close> and
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

    have [simp]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close>
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF list_confl_S' incl] .
    then have \<open>C ! Suc 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using \<open>1 < length C\<close>
      by (cases C; cases \<open>tl C\<close>) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    then have \<open>nat_of_lit (C ! Suc 0) < length W'\<close>
      using W'W unfolding map_fun_rel_def by (auto simp: image_image)
    then show ?thesis
      using empty_cach n_d_M1 C_L' W'W outl vmtf undef \<open>1 < length C\<close> uM_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding U U'
      by (auto simp: propagate_bt_wl_D_heur_def twl_st_heur_def lit_of_hd_trail_st_heur_def
          propagate_bt_wl_D_def Let_def T' U' U rescore_clause_def S' map_fun_rel_def
          list_of_mset2_def flush_def RES_RES2_RETURN_RES RES_RETURN_RES \<phi> uminus_\<A>\<^sub>i\<^sub>n_iff
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
      T'S': \<open>equality_except_conflict T' S'\<close> and
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
      U'U': \<open>equality_except_trail U' T'\<close> and
      lev_K: \<open>get_level (get_trail_wl T') K = Suc (get_maximum_level (get_trail_wl T')
           (remove1_mset (- lit_of (hd (get_trail_wl T')))
             (the (get_conflict_wl T'))))\<close> and
      decomp: \<open>(Decided K # get_trail_wl U', M2) \<in> set (get_all_ann_decomposition (get_trail_wl T'))\<close>
      using find_decomp
      by (auto)

    obtain M N u NE UE Q W where
      T': \<open>T' = (M, N, u, Some (mset C), NE, UE, Q, W)\<close>
      using TT' T_C \<open>\<not>1 < length C\<close>
      apply (cases T'; cases S')
      by (auto simp: find_lit_of_max_level_wl_def)
    obtain D' where
      S': \<open>S' = (M, N, u, D', NE, UE, Q, W)\<close>
      using T'S'
      apply (cases S')
      by (auto simp: find_lit_of_max_level_wl_def T' del_conflict_wl_def)

    obtain M1 where
      U': \<open>U' = (M1, N, u, Some (mset C), NE, UE, Q, W)\<close>
      using \<open>(TnC, T') \<in> ?shorter S'\<close> find_decomp
      apply (cases U')
      by (auto simp: find_lit_of_max_level_wl_def T')
    obtain vm' W' \<phi> clvls cach lbd outl stats where
        U: \<open>U = (M1, N, u, None, Q, W', vm', \<phi>, clvls, cach, lbd, outl, stats)\<close> and
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
          single_of_mset_def flush_def twl_st_heur_def
          RES_RES2_RETURN_RES RES_RETURN_RES S' uminus_\<A>\<^sub>i\<^sub>n_iff
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
        backtrack_l_inv_def
      by (auto simp: twl_st_heur_def)
  qed
  show ?thesis
    supply [[goals_limit=1]]
    apply (intro frefI nres_relI)
    unfolding backtrack_wl_D_nlit_heur_alt_def backtrack_wl_D_def
    apply (refine_rcg shorter)
    subgoal by (rule inv)
    subgoal by (rule trail_nempty)
    subgoal
      
      sorry
       apply (rule find_decomp_wl_nlit; solves assumption)
    subgoal for x y xa S x1 x2 x1a x2a Sa Sb
      by (cases Sb; cases S) (auto simp: twl_st_heur_state_simp)
      apply (rule fst_find_lit_of_max_level_wl; solves assumption)
     apply (rule propagate_bt_wl_D_heur; assumption)
    apply (rule propagate_unit_bt_wl_D_int; assumption)
    done
qed

definition (in -) lit_of_hd_trail_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal\<close> where
  \<open>lit_of_hd_trail_st S = lit_of (hd (get_trail_wl S))\<close>

term lit_of_hd_trail_st_heur
term lit_of_hd_trail
lemma (in -) lit_of_hd_trail_st_heur_alt_def:
  \<open>lit_of_hd_trail_st_heur = (\<lambda>(M, N, U, D, Q, W, vm, \<phi>). lit_of_hd_trail M)\<close>
  by (auto simp: lit_of_hd_trail_st_heur_def lit_of_hd_trail_def intro!: ext)

sepref_thm lit_of_hd_trail_st_heur
  is \<open>RETURN o lit_of_hd_trail_st_heur\<close>
  :: \<open>[\<lambda>S. get_trail_wl_heur S \<noteq> []]\<^sub>a twl_st_heur_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_st_heur_alt_def twl_st_heur_assn_def
  by sepref

 concrete_definition (in -) lit_of_hd_trail_st_heur_code
   uses isasat_input_bounded_nempty.lit_of_hd_trail_st_heur.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) lit_of_hd_trail_st_heur_code_def

lemmas lit_of_hd_trail_st_heur_code_refine[sepref_fr_rules] =
   lit_of_hd_trail_st_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in -) extract_shorter_conflict_l_trivial
  :: \<open>'v literal \<Rightarrow> ('v, 'a) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow>  'v cconflict \<Rightarrow>
        ('v cconflict \<times> 'v conflict_highest_conflict) nres\<close>
where
  \<open>extract_shorter_conflict_l_trivial K M NU NE UE D =
    SPEC(\<lambda>(D', highest). D' \<noteq> None \<and> the D' \<subseteq># the D \<and>
      clause `# twl_clause_of `# mset (tl NU) + NE + UE \<Turnstile>pm add_mset (-K) (the D') \<and>
      highest_lit M (the D') highest)\<close>

definition extract_shorter_conflict_remove_and_add where
  \<open>extract_shorter_conflict_remove_and_add = (\<lambda>M NU C NE UE. do {
     let K = lit_of (hd M);
     let C = Some (remove1_mset (-K) (the C));
     (C, L) \<leftarrow> extract_shorter_conflict_l_trivial K M NU NE UE C;
     RETURN (map_option (add_mset (-K)) C, L)
  })\<close>



(* 
definition extract_shorter_conflict_list_lookup_heur where
  \<open>extract_shorter_conflict_list_lookup_heur = (\<lambda>M NU cach (b, (n, xs)) lbd. do {
     let K = lit_of (hd M);
     ASSERT(atm_of K < length xs);
     ASSERT(n \<ge> 1);
     let xs = xs[atm_of K := None];
     ((n, xs), cach, L) \<leftarrow>
        minimize_and_extract_highest_lookup_conflict M NU (n - 1, xs) cach lbd;
     ASSERT(atm_of K < length xs);
     ASSERT(n + 1 \<le> uint_max);
     RETURN ((b, (n + 1, xs[atm_of K := Some (is_neg K)])), cach, L)
  })\<close>

abbreviation extract_shorter_conflict_l_trivial_pre where
\<open>extract_shorter_conflict_l_trivial_pre \<equiv> \<lambda>(M, D). literals_are_in_\<L>\<^sub>i\<^sub>n (mset (fst D))\<close>
 *)
sepref_register extract_shorter_conflict_l_trivial

(* definition extract_shorter_conflict_list_heur_st'
  :: \<open>twl_st_wl_heur \<Rightarrow>
       (twl_st_wl_heur \<times> nat conflict_highest_conflict) nres\<close>
where
  \<open>extract_shorter_conflict_list_heur_st' = (\<lambda>(M, N, U, D, WS, Q). do {
     (D, L) \<leftarrow> extract_shorter_conflict_heur M (mset `# mset (tl N)) (NE + UE) D;
     RETURN ((M, N, U, D, NE, UE, WS, Q), L)
  })\<close> *)

definition extract_shorter_conflict_remove_and_add_st
  :: \<open>nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> nat conflict_highest_conflict) nres\<close>
where
  \<open>extract_shorter_conflict_remove_and_add_st = (\<lambda>(M, N, U, D, NE, UE, WS, Q). do {
     (D, L) \<leftarrow> extract_shorter_conflict_remove_and_add M N D NE UE;
     RETURN ((M, N, U, D, NE, UE, WS, Q), L)
  })\<close>


(* lemma iterate_over_conflict_extract_shorter_conflict_l_trivial:
  assumes
    D: \<open>the D = add_mset (- lit_of (hd M)) A\<close> \<open>D = Some E\<close> and
    invs: \<open>twl_struct_invs (twl_st_of_wl None (M, NU, u, D, NE, UE, W, Q))\<close> and
    \<open>twl_stgy_invs (twl_st_of_wl None (M, NU, u, D, NE, UE, W, Q))\<close>
  shows \<open>iterate_over_conflict (-lit_of (hd M)) M (mset `# mset (tl NU)) (NE + UE) A
         \<le> \<Down> {((D', highest'), (D, highest)). the D = D' \<and> D \<noteq> None \<and>
              highest_lit M (the D) highest \<and> highest' = highest}
            (extract_shorter_conflict_l_trivial (lit_of (hd M)) M NU NE UE (Some A))\<close>
proof -
  have
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state
    (state\<^sub>W_of (twl_st_of_wl None (M, NU, u, D, NE, UE, W, Q)))\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause
    (state\<^sub>W_of (twl_st_of_wl None (M, NU, u, D, NE, UE, W, Q)))\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
   by fast+
  have [simp]: \<open>mset ` set (take u (tl NU)) \<union> mset ` set (drop u (tl NU)) = mset ` set (tl NU)\<close>
     apply (subst (5) append_take_drop_id[symmetric, of _ u], subst set_append)
     using confl D by (auto simp: drop_Suc)
  then have [simp]: \<open>mset ` set (take u (tl NU)) \<union> (set_mset NE \<union> (mset ` set (drop u (tl NU))
       \<union> set_mset UE)) = mset ` set (tl NU) \<union> set_mset NE \<union> set_mset UE\<close>
     apply (subst (5) append_take_drop_id[symmetric, of _ u], subst set_append)
     using confl D by (auto simp: drop_Suc)
  have entailed: \<open>mset `# mset (tl NU) + (NE + UE) \<Turnstile>pm add_mset (- lit_of (hd M)) A\<close>
     apply (subst append_take_drop_id[symmetric, of _ u], subst mset_append)
     using confl D by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
      mset_take_mset_drop_mset' clauses_def drop_Suc Un_assoc)
  have dist_A: \<open>distinct_mset A\<close>
     using dist D
     by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      mset_take_mset_drop_mset')
  show ?thesis
    apply (rule order.trans)
    apply (rule iterate_over_conflict_spec)
    subgoal by (rule entailed)
    subgoal by (rule dist_A)
    subgoal using D
      by (auto 5 5 simp: extract_shorter_conflict_l_trivial_def conc_fun_RES Un_assoc
      mset_take_mset_drop_mset')
    done
qed
 *)
(* lemma extract_shorter_conflict_remove_and_add_st_extract_shorter_conflict_wl_nlit_st:
  \<open>(extract_shorter_conflict_remove_and_add_st, extract_shorter_conflict_wl_nlit_st) \<in>
     [\<lambda>S. -lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S)]\<^sub>f Id \<rightarrow>
         \<langle>Id\<rangle>nres_rel\<close>
   unfolding extract_shorter_conflict_remove_and_add_st_def extract_shorter_conflict_wl_nlit_st_def
   extract_shorter_conflict_remove_and_add_def extract_shorter_conflict_wl_nlit_def
   extract_shorter_conflict_l_trivial_def
   by (intro frefI nres_relI)
      (auto simp: Let_def RES_RETURN_RES2 RES_RETURN_RES bind_RES_RETURN2_eq
        dest!: multi_member_split)

lemma extract_shorter_conflict_list_heur_st_extract_shorter_conflict_list_st:
  \<open>(extract_shorter_conflict_list_heur_st, extract_shorter_conflict_remove_and_add_st) \<in>
     [\<lambda>S. -lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S) \<and> get_conflict_wl S \<noteq> None \<and>
        twl_struct_invs (twl_st_of_wl None S) \<and> twl_stgy_invs (twl_st_of_wl None S)]\<^sub>f
     Id \<rightarrow>
    \<langle>{((S, L'), (S', L)). S = S' \<and> L' = L \<and>
       highest_lit (get_trail_wl S)
         (remove1_mset (- lit_of (hd (get_trail_wl S))) (the (get_conflict_wl S))) L}\<rangle> nres_rel\<close>
  unfolding extract_shorter_conflict_list_heur_st_def extract_shorter_conflict_wl_nlit_st_def
    extract_shorter_conflict_heur_def extract_shorter_conflict_remove_and_add_def
    extract_shorter_conflict_remove_and_add_st_def
  by (intro frefI nres_relI)
     (auto simp: Let_def image_image mset_take_mset_drop_mset'
      dest!: multi_member_split simp del: twl_st_of_wl.simps
      intro!: bind_refine[OF iterate_over_conflict_extract_shorter_conflict_l_trivial])

definition (in isasat_input_ops) twl_st_heur_confl
  :: \<open>(twl_st_wl_heur_lookup_conflict \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur_confl = twl_st_wl_heur_lookup_lookup_clause_rel O twl_st_heur\<close>


definition (in isasat_input_ops) twl_st_heur_no_clvls_confl
  :: \<open>(twl_st_wl_heur_lookup_conflict \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur_no_clvls_confl =
  {((M', N', U', D', Q', W', vm, \<phi>, clvls, cach, lbd, stats), (M, N, U, D, NE, UE, Q, W)).
    M = M' \<and> N' = N \<and> U' = U \<and>
    (D', D) \<in> option_lookup_clause_rel \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach
  }\<close>
 *)
definition extract_shorter_conflict_list_heur_st_pre where
  \<open>extract_shorter_conflict_list_heur_st_pre S \<longleftrightarrow>
    get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [] \<and>
        -lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S) \<and>
        twl_struct_invs (twl_st_of_wl None S) \<and>
        twl_stgy_invs (twl_st_of_wl None S) \<and>
        literals_are_\<L>\<^sub>i\<^sub>n S \<and>
        twl_list_invs (st_l_of_wl None S)\<close>


(* lemma extract_shorter_conflict_list_lookup_heur_st_extract_shorter_conflict_st_trivial_heur:
  \<open>(extract_shorter_conflict_list_lookup_heur_st, extract_shorter_conflict_list_heur_st) \<in>
     [extract_shorter_conflict_list_heur_st_pre]\<^sub>f
      (twl_st_heur_confl) \<rightarrow> \<langle>twl_st_heur_no_clvls_confl \<times>\<^sub>r Id\<rangle>nres_rel\<close>
proof -
  have
    atm_M'_le_D': \<open>atm_of (lit_of (hd M')) < length D'\<close> (is ?A) and
    n'_ge: \<open>1 \<le> n'\<close> (is ?B) and
    minimize_and_extract_highest_lookup_conflict:
     \<open>minimize_and_extract_highest_lookup_conflict M' N'
       (n' - 1, D'[atm_of (lit_of (hd M')) := None]) cach lbd
      \<le> \<Down> {((E, s, L'), E', L). (E, E') \<in> lookup_clause_rel \<and> L' = L \<and>
               length (snd E) = length (snd (n' - 1, D'[atm_of (lit_of (hd M')) := None])) \<and>
               E' \<subseteq># (the (Some (remove1_mset (- lit_of (hd M)) (the D))))}
          (iterate_over_conflict (- lit_of (hd M)) M (mset `# mset (tl N))
            (NE + UE)
            (the (Some (remove1_mset (- lit_of (hd M)) (the D)))))\<close> (is ?mini is \<open>_ \<le> \<Down> ?min _\<close>)
    if
      pre: \<open>extract_shorter_conflict_list_heur_st_pre (M, N, U, D, NE, UE, Q, W)\<close> and
      rel: \<open>((M', N', u', (b', n', D'), Q', W', vm, \<phi>,
       clvls, cach, lbd, stats), M, N, U, D, NE, UE, Q, W) \<in> twl_st_heur_confl\<close>
    for M' N' u' b' n' D' Q' W' vm \<phi> clvls cach M N U D NE UE Q W lbd stats
  proof -
    let ?S = \<open>(M, N, U, D, NE, UE, Q, W)\<close>
    have
      MM': \<open>M' = M\<close> and
      N'N: \<open>N' = N\<close> and
      u'U: \<open>u' = U\<close> and
      olr: \<open>((b', n', D'), D) \<in> option_lookup_clause_rel\<close> and
      \<open>Q' = Q\<close> and
      \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> and
      \<open>vm \<in> vmtf M'\<close> and
      \<open>phase_saving \<phi>\<close> and
      \<open>no_dup M'\<close> and
      empty_cach: \<open>cach_refinement_empty cach\<close>
      using rel unfolding twl_st_heur_confl_def twl_st_wl_heur_lookup_lookup_clause_rel_def
      twl_st_heur_def by auto
    have
      None: \<open>get_conflict_wl ?S \<noteq> None\<close> and
      \<open>get_trail_wl ?S \<noteq> []\<close> and
      lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n ?S\<close> and
      uL_D: \<open>- lit_of (hd (get_trail_wl ?S))
       \<in># the (get_conflict_wl ?S)\<close> and
      invs: \<open>twl_struct_invs (twl_st_of_wl None ?S)\<close> and
      add_invs: \<open>twl_list_invs (st_l_of_wl None ?S)\<close>
      using pre unfolding extract_shorter_conflict_list_heur_st_pre_def
      by clarify+

    have
      lits_M: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl ?S)\<close> and
      lits_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl ?S))\<close>
      using literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail[OF lits, of None]
        literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits, of None] invs None by auto
    show ?A
      using olr uL_D None lits_M lits_D
      by (auto simp: option_lookup_clause_rel_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
          lookup_clause_rel_def MM' dest!: multi_member_split[of \<open>- lit_of (hd M)\<close>])
    show ?B
      using olr uL_D None
      by (auto simp: twl_st_heur_no_clvls_confl_def extract_shorter_conflict_list_heur_st_pre_def
          option_lookup_clause_rel_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset lookup_clause_rel_def
          dest!: multi_member_split[of \<open>- lit_of (hd M)\<close>])
    have NUE: \<open>UE + NE = NE + UE\<close>
      by simp
    note H = minimize_and_extract_highest_lookup_conflict_iterate_over_conflict[of _ _
        \<open>?S\<close> _ _,
        unfolded get_unit_learned_def get_unit_init_clss_def get_trail_wl.simps
        get_clauses_wl.simps prod.case NUE]
    have M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None ?S))\<close> and
      confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None ?S))\<close> and
      learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of (twl_st_of_wl None ?S))\<close>
      using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    have M_D: \<open>M \<Turnstile>as CNot (the D)\<close>
      using confl None unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def by auto
    moreover have \<open>no_dup M\<close>
      using M_lev None unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by auto

    ultimately have \<open>lit_of (hd M) \<notin># the D\<close>
      using uL_D by (auto simp: add_mset_eq_add_mset dest!: multi_member_split no_dup_consistentD)

    then have lcr':
      \<open>((n' - 1, D'[atm_of (lit_of (hd M)) := None]),
     the (Some (remove1_mset (- lit_of (hd M)) (the D)))) \<in> lookup_clause_rel\<close>
      using uL_D olr None mset_as_position_remove[of D' \<open>the D\<close> \<open>atm_of (lit_of (hd M))\<close>] \<open>?A\<close>
      by (cases \<open>lit_of (hd M)\<close>)
         (auto simp: lookup_clause_rel_def size_remove1_mset_If option_lookup_clause_rel_def MM'
          dest!: multi_member_split)
    have M_rem_D: \<open>M \<Turnstile>as CNot (the (Some (remove1_mset (- lit_of (hd M)) (the D))))\<close>
      using M_D by (simp add: true_annot_CNot_diff)
    have cach_analyse: \<open>conflict_min_analysis_inv
           (trail (state\<^sub>W_of (twl_st_of_wl None ?S))) cach (mset `# mset (tl N) + (NE + UE))
            (the (Some (remove1_mset (- lit_of (hd M)) (the D))))\<close>
      using empty_cach lits_M
      by (auto simp: conflict_min_analysis_inv_def cach_refinement_empty_def
          dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms)
    have confl_entailed: \<open>mset `# mset (tl N) + (NE + UE) \<Turnstile>pm
    add_mset (- lit_of (hd M))
     (the (Some (remove1_mset (- lit_of (hd M)) (the D))))\<close>
      using learned None uL_D
      by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def mset_take_mset_drop_mset'
          clauses_def clauses_twl_st_of_wl conflicting_twl_st_of_wl Un_assoc
          simp del: twl_st_of_wl.simps)
    show ?mini
      unfolding MM' N'N
      apply (rule H)
      subgoal by (rule lcr')
      subgoal by (rule M_rem_D)
      subgoal by (rule lits_M[unfolded get_trail_wl.simps])
      subgoal by (rule invs)
      subgoal by (rule add_invs)
      subgoal by (rule cach_analyse)
      subgoal by (rule confl_entailed)
      subgoal using literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF lits_D] by auto
      done
  qed
  have re_add:
     \<open>(((b', m + 1, E' [atm_of (lit_of (hd M')) := Some (is_neg (lit_of (hd M')))]),
        cach2, highest),
       Some (add_mset (- lit_of (hd M)) E), SL)
      \<in> {((E, s, L'), E', L). (E, E') \<in> option_lookup_clause_rel \<and> L' = L \<and>
               length (snd (snd E)) = length (snd (n' - 1, D'[atm_of (lit_of (hd M')) := None]))}\<close>
      (is ?readd) and
     le_uint_max: \<open>m + 1 \<le> uint_max\<close> (is ?le)
    if
      pre: \<open>extract_shorter_conflict_list_heur_st_pre (M, N, U, D, NE, UE, Q, W)\<close> and
      ref: \<open>((M', N', u', (b', n', D'), Q', W', vm, \<phi>, clvls, cach), M, N, U, D, NE, UE, Q, W)
         \<in> twl_st_heur_confl\<close> and
      hd_le_D': \<open>atm_of (lit_of (hd M')) < length D'\<close> and
      \<open>1 \<le> n'\<close> and
      mini: \<open>(ESL', ESL) \<in> ?min M' n' D' M D\<close> and
      \<open>ESL = (E, SL)\<close> and
      \<open>mE' = (m, E')\<close> and
      \<open>x2b = (cach2, highest)\<close> and
      \<open>ESL' = (mE', x2b)\<close> and
      \<open>atm_of (lit_of (hd M')) < length E'\<close>
    for M' N' u' b' n' D' Q' W' \<phi> clvls cach M N U D NE UE Q
      W ESL' ESL E SL mE' m E' x2b cach2 highest vm
  proof -
    let ?S = \<open>(M, N, U, D, NE, UE, Q, W)\<close>
    have
      [simp]: \<open>b' = False\<close> and
      MM': \<open>M' = M\<close> and
      N'N: \<open>N' = N\<close> and
      u'U: \<open>u' = U\<close> and
      \<open>- lit_of (hd M') \<in># the D\<close> and
      None: \<open>D \<noteq> None\<close> and
      invs: \<open>twl_struct_invs (twl_st_of_wl None ?S)\<close> and
      lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n ?S\<close> and
      uL_D: \<open>- lit_of (hd M') \<in># the D\<close>
      using pre ref by (auto simp: option_lookup_clause_rel_def
          extract_shorter_conflict_list_heur_st_pre_def twl_st_heur_confl_def twl_st_wl_heur_lookup_lookup_clause_rel_def
          twl_st_heur_def)
    have
      ESL: \<open>ESL = (E, SL)\<close> and
      \<open>mE' = (m, E')\<close> and
      \<open>x2b = (cach2, SL)\<close> and
      ESL': \<open>ESL' = ((m, E'), cach2, SL)\<close> and
      lcr: \<open>((m, E'), E) \<in> lookup_clause_rel\<close> and
      [simp]: \<open>highest = SL\<close> and
      [simp]: \<open>length E' = length D'\<close>
      using that
      by auto
    have E: \<open>E \<subseteq># the (Some (remove1_mset (- lit_of (hd M')) (the D)))\<close>
      using mini unfolding ESL ESL' MM' by auto

    have M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None ?S))\<close> and
      confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None ?S))\<close> and
      learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of (twl_st_of_wl None ?S))\<close> and
      dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None ?S))\<close>
      using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+

    have M_D: \<open>M \<Turnstile>as CNot (the D)\<close>
      using confl None unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def by auto
    moreover have \<open>no_dup M\<close>
      using M_lev None unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by auto
    ultimately have L_D: \<open>lit_of (hd M') \<notin># the D\<close>
      using uL_D by (auto dest: in_CNot_implies_uminus(2) no_dup_consistentD)
    have \<open>distinct_mset (the D)\<close>
      using dist None unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      by auto
    then have \<open>- lit_of (hd M') \<notin># E\<close>
      using E uL_D by (auto dest!: multi_member_split[of _ \<open>the D\<close>])
    moreover have \<open>lit_of (hd M') \<notin># E\<close>
      using L_D E by auto
    ultimately have \<open>((b', Suc m, E' [atm_of (lit_of (hd M')) := Some (is_neg (lit_of (hd M')))]),
        Some (add_mset (- lit_of (hd M)) E)) \<in> option_lookup_clause_rel\<close>
      using lcr hd_le_D'
      mset_as_position.add[of E' E \<open>-lit_of (hd M')\<close>
        \<open>E' [atm_of (lit_of (hd M')) := Some (is_pos (- lit_of (hd M')))]\<close>]
      unfolding option_lookup_clause_rel_def lookup_clause_rel_def
      by (auto simp: is_pos_neg_not_is_pos MM')
    then show ?readd
      by auto
    have
      lits_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl ?S))\<close>
      using literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail[OF lits, of None]
        literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits, of None] invs None by auto
    have \<open>E \<subseteq># the D\<close>
      using E by (auto intro: subset_mset.order_trans)
    then show ?le
      using lcr lits_D None lookup_clause_rel_size[of m E' E]
        literals_are_in_\<L>\<^sub>i\<^sub>n_mono[of \<open>the D\<close> E]
      by (auto simp: uint_max_def lookup_clause_rel_def)
  qed
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding extract_shorter_conflict_list_lookup_heur_st_def
        extract_shorter_conflict_list_heur_st_def extract_shorter_conflict_heur_def
        extract_shorter_conflict_list_lookup_heur_def Let_def
        option_lookup_clause_rel_def lookup_clause_rel_def
    apply clarify
    apply (refine_rcg H)
    subgoal by (rule atm_M'_le_D')
    subgoal by (rule n'_ge)
        apply (rule minimize_and_extract_highest_lookup_conflict; assumption)
    subgoal by auto
    subgoal by (rule le_uint_max)
     apply (rule re_add; solves assumption)
    subgoal by (auto simp: twl_st_heur_confl_def twl_st_wl_heur_lookup_lookup_clause_rel_def
          twl_st_heur_def twl_st_heur_no_clvls_confl_def
          cach_refinement_empty_def empty_cach_def)
    done
qed *)

definition extract_shorter_conflict_list_lookup_heur_pre where
  \<open>extract_shorter_conflict_list_lookup_heur_pre =
     (\<lambda>((((M, NU), cach), D), lbd). literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and> M \<noteq> [] \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl NU)) \<and>
        (\<forall>a\<in>lits_of_l M. atm_of a < length (snd (snd D))))\<close>

(* 
theorem extract_shorter_conflict_list_heur_st_extract_shorter_conflict_wl_nlit_st:
  \<open>(extract_shorter_conflict_list_heur_st,
   extract_shorter_conflict_wl_nlit_st)
    \<in> [\<lambda>S. - lit_of (hd (get_trail_wl S))
           \<in># the (get_conflict_wl S) \<and>
           get_conflict_wl S \<noteq> None \<and>
           twl_struct_invs (twl_st_of_wl None S) \<and>
           twl_stgy_invs (twl_st_of_wl None S)]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    (is \<open>?c \<in> [?pre]\<^sub>f ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE Id
       (\<lambda>S. - lit_of (hd (get_trail_wl S))
            \<in># the (get_conflict_wl S))
       (\<lambda>_ S.
           - lit_of (hd (get_trail_wl S))
           \<in># the (get_conflict_wl S) \<and>
           get_conflict_wl S \<noteq> None \<and>
           twl_struct_invs (twl_st_of_wl None S) \<and>
           twl_stgy_invs (twl_st_of_wl None S))
       (\<lambda>_. True)]\<^sub>f Id O Id \<rightarrow>
     \<langle>{((S, L'), S', L). S = S' \<and> L' = L \<and>
        highest_lit (get_trail_wl S)
          (remove1_mset (- lit_of (hd (get_trail_wl S))) (the (get_conflict_wl S))) L}
     \<rangle>nres_rel O \<langle>Id\<rangle>nres_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>f ?im' \<rightarrow> ?f'\<close>)
    using fref_compI_PRE[OF extract_shorter_conflict_list_heur_st_extract_shorter_conflict_list_st
    extract_shorter_conflict_remove_and_add_st_extract_shorter_conflict_wl_nlit_st] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_pol_def trail_pol_def
        ann_lits_split_reasons_def)
  have im: \<open>?im' = ?im\<close>
    by simp
  have f: \<open>?f' \<subseteq> ?f\<close>
    unfolding nres_rel_comp
    by (rule nres_rel_mono) auto
  show ?thesis
    apply (rule fref_weaken_pre_weaken[OF ])
     defer
    using H unfolding im PR_CONST_def apply assumption
    apply (rule f)
    using pre ..
qed *)

(* theorem extract_shorter_conflict_list_lookup_heur_st_extract_shorter_conflict_wl_nlit_st:
  \<open>(extract_shorter_conflict_list_lookup_heur_st,
   extract_shorter_conflict_wl_nlit_st)
    \<in> [extract_shorter_conflict_list_heur_st_pre]\<^sub>f twl_st_heur_confl \<rightarrow>
     \<langle>twl_st_heur_no_clvls_confl \<times>\<^sub>r Id\<rangle>nres_rel\<close>
    (is \<open>?c \<in> [?pre]\<^sub>f ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE Id
     (\<lambda>S. - lit_of (hd (get_trail_wl S))
          \<in># the (get_conflict_wl S) \<and>
          get_conflict_wl S \<noteq> None \<and>
          twl_struct_invs (twl_st_of_wl None S) \<and>
          twl_stgy_invs (twl_st_of_wl None S))
     (\<lambda>_. extract_shorter_conflict_list_heur_st_pre)
     (\<lambda>_. True)]\<^sub>f twl_st_heur_confl O
                   Id \<rightarrow> \<langle>twl_st_heur_no_clvls_confl \<times>\<^sub>f
                          Id\<rangle>nres_rel O
                         \<langle>Id\<rangle>nres_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>f ?im' \<rightarrow> ?f'\<close>)
    using fref_compI_PRE[OF
       extract_shorter_conflict_list_lookup_heur_st_extract_shorter_conflict_st_trivial_heur
       extract_shorter_conflict_list_heur_st_extract_shorter_conflict_wl_nlit_st] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def extract_shorter_conflict_list_heur_st_pre_def )
  have im: \<open>?im' = ?im\<close>
    by simp
  have f: \<open>?f' \<subseteq> ?f\<close>
    unfolding nres_rel_comp
    by (rule nres_rel_mono) auto
  show ?thesis
    apply (rule fref_weaken_pre_weaken[OF ])
     defer
    using H unfolding im PR_CONST_def apply assumption
    apply (rule f)
    using pre ..
qed *)

(* 
definition (in isasat_input_ops) twl_st_no_clvls_assn
  :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close>
where
  \<open>twl_st_no_clvls_assn = hr_comp twl_st_heur_lookup_lookup_clause_assn twl_st_heur_no_clvls_confl\<close>
 *)

(* definition (in -) target_level (* :: \<open>nat conflict_highest_conflict \<Rightarrow> nat\<close> *) where
  \<open>target_level highest = (case highest of None \<Rightarrow> 0 | Some (_, lev) \<Rightarrow> lev)\<close>
 *)



subsubsection \<open>Backtrack with direct extraction of literal if highest level\<close>

(*
State Function                                |  Minimisation Function
----------------------------------------------|---------------------------------------------
extract_shorter_conflict_wl                   |  extract_shorter_conflict_list_st
extract_shorter_conflict_list_st              |  extract_shorter_conflict_remove_and_add
extract_shorter_conflict_list_heur_st         |  extract_shorter_conflict_heur
extract_shorter_conflict_list_lookup_heur_st  |  extract_shorter_conflict_list_lookup_heur
*)

(* sepref_register extract_shorter_conflict_list_lookup_heur
sepref_thm extract_shorter_conflict_list_lookup_heur_code
  is \<open>uncurry4 (PR_CONST extract_shorter_conflict_list_lookup_heur)\<close>
  :: \<open>[extract_shorter_conflict_list_lookup_heur_pre]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a
      cach_refinement_assn\<^sup>d *\<^sub>a conflict_option_rel_assn\<^sup>d  *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      conflict_option_rel_assn *a cach_refinement_assn *a
        highest_lit_assn\<close>
  unfolding extract_shorter_conflict_list_lookup_heur_def fast_minus_def[symmetric]
    one_uint32_nat_def[symmetric] PR_CONST_def extract_shorter_conflict_list_lookup_heur_pre_def
  by sepref

concrete_definition (in -) extract_shorter_conflict_list_lookup_heur_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_list_lookup_heur_code.refine_raw
   is \<open>(uncurry4 ?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_list_lookup_heur_code_def

lemmas extract_shorter_conflict_list_lookup_heur_code_hnr[sepref_fr_rules] =
   extract_shorter_conflict_list_lookup_heur_code.refine[OF isasat_input_bounded_nempty_axioms]
 *)
(* sepref_register extract_shorter_conflict_list_lookup_heur_st
sepref_thm extract_shorter_conflict_list_lookup_heur_st_code
  is \<open>PR_CONST extract_shorter_conflict_list_lookup_heur_st\<close>
  :: \<open>[\<lambda>(M, N, U, D, Q', W', vm, \<phi>, clvls, cach, lbd, stats).
         extract_shorter_conflict_list_lookup_heur_pre ((((M, N), cach), D), lbd)]\<^sub>a
      twl_st_heur_lookup_lookup_clause_assn\<^sup>d \<rightarrow>
       twl_st_heur_lookup_lookup_clause_assn *a highest_lit_assn\<close>
  unfolding extract_shorter_conflict_list_lookup_heur_st_def twl_st_heur_lookup_lookup_clause_assn_def
  PR_CONST_def
  by sepref

concrete_definition (in -) extract_shorter_conflict_list_lookup_heur_st_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_list_lookup_heur_st_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_list_lookup_heur_st_code_def

lemmas extract_shorter_conflict_list_lookup_heur_st_hnr[sepref_fr_rules] =
   extract_shorter_conflict_list_lookup_heur_st_code.refine[OF isasat_input_bounded_nempty_axioms]
 *)
definition find_decomp_wl_imp
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat \<Rightarrow> vmtf_remove_int \<Rightarrow>
       ((nat, nat) ann_lits \<times> vmtf_remove_int) nres\<close>
where
  \<open>find_decomp_wl_imp = (\<lambda>M\<^sub>0 lev vm. do {
    let k = count_decided M\<^sub>0;
    (_, M, vm') \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M, vm'). j = count_decided M \<and> j \<ge> lev \<and>
           (M = [] \<longrightarrow> j = lev) \<and>
           (\<exists>M'. M\<^sub>0 = M' @ M \<and> (j = lev \<longrightarrow> M' \<noteq> [] \<and> is_decided (last M'))) \<and>
           vm' \<in> vmtf M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M)\<^esup>
         (\<lambda>(j, M, vm). j > lev)
         (\<lambda>(j, M, vm). do {
            ASSERT(M \<noteq> []);
            ASSERT(j \<ge> 1);
            if is_decided (hd M)
            then let L = atm_of (lit_of (hd M)) in RETURN (fast_minus j 1, tl M, vmtf_unset L vm)
            else let L = atm_of (lit_of (hd M)) in RETURN (j, tl M, vmtf_unset L vm)}
         )
         (k, M\<^sub>0, vm);
    RETURN (M, vm')
  })\<close>

(* 
lemma extract_shorter_conflict_l_trivial_code_extract_shorter_conflict_l_trivial[sepref_fr_rules]:
  \<open>(extract_shorter_conflict_list_lookup_heur_st_code, extract_shorter_conflict_wl_nlit_st)
    \<in> [extract_shorter_conflict_list_heur_st_pre]\<^sub>a
       twl_st_assn\<^sup>d \<rightarrow> (twl_st_no_clvls_assn *a highest_lit_assn)\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
  \<in> [comp_PRE twl_st_heur_confl
     extract_shorter_conflict_list_heur_st_pre
     (\<lambda>_ (M, N, U, D, Q', W', vm, \<phi>, clvls, cach,
         lbd, stats).
         extract_shorter_conflict_list_lookup_heur_pre
          ((((M, N), cach), D), lbd))
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (twl_st_heur_lookup_lookup_clause_assn\<^sup>d)
                     twl_st_heur_confl \<rightarrow> hr_comp
                 (twl_st_heur_lookup_lookup_clause_assn *a
                  highest_lit_assn)
                 (twl_st_heur_no_clvls_confl \<times>\<^sub>f
                  Id)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF extract_shorter_conflict_list_lookup_heur_st_hnr[unfolded PR_CONST_def]
          extract_shorter_conflict_list_lookup_heur_st_extract_shorter_conflict_wl_nlit_st] .
  have [simp]: \<open>\<And>a ac ad b y af ag ah ai aj ba bb ak bc al am ao ap
       aq bd ar.
       literals_are_in_\<L>\<^sub>i\<^sub>n_trail a \<Longrightarrow> ((ac, ad, b), Some y) \<in> option_lookup_clause_rel \<Longrightarrow>
       ar \<in> lits_of_l a \<Longrightarrow> atm_of ar < length b\<close>
    by (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
        dest!: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms )

  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    using literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail[of x, of None]
      literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[of x]
      literals_are_\<L>\<^sub>i\<^sub>n_clauses_literals_are_in_\<L>\<^sub>i\<^sub>n[of x]
    unfolding comp_PRE_def
    by (auto simp: comp_PRE_def list_mset_rel_def br_def extract_shorter_conflict_list_heur_st_pre_def
        map_fun_rel_def twl_st_heur_no_clvls_confl_def extract_shorter_conflict_list_lookup_heur_pre_def
        twl_st_heur_confl_def twl_st_wl_heur_lookup_lookup_clause_rel_def
        twl_st_heur_def
        simp del: twl_st_of_wl.simps
        intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_no_clvls_assn_def[symmetric]
    twl_st_assn_confl_assn twl_st_heur_confl_def ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_no_clvls_assn_def[symmetric]
       hr_comp_prod_conv hr_comp_Id2 ..
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed
 *)
definition find_decomp_wl_imp_pre where
  \<open>find_decomp_wl_imp_pre = (\<lambda>(((M, D), L), vm). M \<noteq> [] \<and> D \<noteq> None \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> -L \<in># the D \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and> vm \<in> vmtf M)\<close>

(* definition (in -) get_maximum_level_remove_int :: \<open>(nat, 'a) ann_lits \<Rightarrow>
    lookup_clause_rel_with_cls_with_highest \<Rightarrow> nat literal \<Rightarrow>  nat\<close> where
  \<open>get_maximum_level_remove_int = (\<lambda>_ (_, D) _.
    (if D = None then 0 else snd (the D)))\<close>

lemma (in -) target_level_hnr[sepref_fr_rules]:
  \<open>(return o target_level, RETURN o target_level) \<in>
     highest_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: target_level_def uint32_nat_rel_def br_def split: option.splits)
 *)
sepref_register find_decomp_wl_imp
sepref_thm find_decomp_wl_imp_code
  is \<open>uncurry2 (PR_CONST find_decomp_wl_imp)\<close>
  :: \<open>trail_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d
    \<rightarrow>\<^sub>a trail_assn *a vmtf_remove_conc\<close>
  unfolding find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    find_decomp_wl_imp_pre_def
  supply [[goals_limit=1]] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  supply uint32_nat_assn_one[sepref_fr_rules]
  supply uint32_nat_assn_minus[sepref_fr_rules]
  by sepref

concrete_definition (in -) find_decomp_wl_imp_code
   uses isasat_input_bounded_nempty.find_decomp_wl_imp_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp_code_def

lemmas find_decomp_wl_imp_code[sepref_fr_rules] =
   find_decomp_wl_imp_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition find_decomp_wvmtf_ns  where
  \<open>find_decomp_wvmtf_ns =
     (\<lambda>(M::(nat, nat) ann_lits) highest _.
        SPEC(\<lambda>(M1, vm). \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = Suc highest \<and> vm \<in> vmtf M1))\<close>


definition (in -) find_decomp_wl_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>find_decomp_wl_st = (\<lambda>L (M, N, U, D, oth).  do{
     M' \<leftarrow> find_decomp_wl' M (the D) L;
    RETURN (M', N, U, D, oth)
  })\<close>

definition find_decomp_wl_st_int :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow>
    twl_st_wl_heur nres\<close> where
  \<open>find_decomp_wl_st_int = (\<lambda>highest (M, N, U, D, W, Q, vm, \<phi>, clvls, cach, lbd, stats). do{
     (M', vm) \<leftarrow> find_decomp_wvmtf_ns M highest vm;
     lbd \<leftarrow> lbd_empty lbd;
     RETURN (M', N, U, D, W, Q, vm, \<phi>, clvls, cach, lbd, stats)
  })\<close>


lemma (in isasat_input_ops) literals_are_in_\<L>\<^sub>i\<^sub>n_trail_empty[simp]:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail []\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def)

lemma (in isasat_input_ops) literals_are_in_\<L>\<^sub>i\<^sub>n_Cons:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (a # M) \<longleftrightarrow> lit_of a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_trail M\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def)

lemma (in isasat_input_ops) literals_are_in_\<L>\<^sub>i\<^sub>n_trail_lit_of_mset:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M = literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M)\<close>
  by (induction M) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset literals_are_in_\<L>\<^sub>i\<^sub>n_Cons)

lemma
  assumes
    struct: \<open>twl_struct_invs (twl_st_of_wl None (M\<^sub>0, N, U, D, NE, UE, Q, W))\<close> and
    vm: \<open>vm \<in> vmtf M\<^sub>0\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M\<^sub>0\<close> and
    target: \<open>highest < count_decided M\<^sub>0\<close>
  shows
    find_decomp_wl_imp_le_find_decomp_wl':
      \<open>find_decomp_wl_imp M\<^sub>0 highest vm \<le> find_decomp_wvmtf_ns M\<^sub>0 highest vm\<close>
     (is ?decomp)
proof -
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
  have [iff]: \<open>convert_lits_l N M = [] \<longleftrightarrow> M = []\<close> for M
    by (cases M) auto
  have
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NE, UE, Q, W)))\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NE, UE, Q, W)))\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NE, UE, Q, W)))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+

  have n_d: \<open>no_dup M\<^sub>0\<close>
    using lev_inv by (auto simp: mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def)

  have count_decided_not_Nil[simp]:  \<open>0 < count_decided M \<Longrightarrow> M \<noteq> []\<close> for M :: \<open>(nat, nat) ann_lits\<close>
    by auto
  have get_lev_last: \<open>get_level (M' @ M) (lit_of (last M')) = Suc (count_decided M)\<close>
    if \<open>M\<^sub>0 = M' @ M\<close> and \<open>M' \<noteq> []\<close> and \<open>is_decided (last M')\<close> for M' M
    apply (cases M' rule: rev_cases)
    using that apply simp
    using n_d that by auto

  have atm_of_N:
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset aa) \<Longrightarrow> aa \<noteq> [] \<Longrightarrow> atm_of (lit_of (hd aa)) \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    for aa
    by (cases aa) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

  show ?decomp
    unfolding find_decomp_wl_imp_def Let_def find_decomp_wvmtf_ns_def
    apply (refine_vcg 1 WHILEIT_rule[where R=\<open>measure (\<lambda>(_, M, _). length M)\<close>])
    subgoal by simp
    subgoal by auto
    subgoal using target by (auto simp: count_decided_ge_get_maximum_level)
    subgoal using target by (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] intro: butlast
          cong: if_cong split: if_splits)
    subgoal
      using get_level_neq_Suc_count_decided target
      by (auto simp: count_decided_butlast butlast_nil_iff eq_commute[of \<open>[_]\<close>] mset_le_subtract
          intro: butlast)
    subgoal using vm by auto
    subgoal using lits unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_trail_lit_of_mset by auto
    subgoal using lits by auto
    subgoal using lits by auto
    subgoal for s a b aa ba x1 x2 x1a x2a
      using lits by (cases aa) (auto intro: butlast count_decided_tl_if)
    subgoal by (auto simp: count_decided_butlast count_decided_tl_if)[]
    subgoal for s a b aa ba x1 x2 x1a x2a by (cases aa) (auto simp: count_decided_ge_get_maximum_level)
    subgoal for s a b aa ba x1 x2 x1a x2a
      by (cases aa) (auto simp: butlast_nil_iff count_decided_butlast)
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases ba)
        (auto intro!: vmtf_unset_vmtf_tl atm_of_N)
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases aa)
        (auto  simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases aa) (auto intro: butlast count_decided_tl_if)
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a
      by (cases aa) (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] intro: butlast
          cong: if_cong split: if_splits)
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases ba)
        (auto intro!: vmtf_unset_vmtf_tl atm_of_N)
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases aa)
        (auto  simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal by auto
    subgoal for s D M
      apply (auto simp: count_decided_ge_get_maximum_level ex_decomp_get_ann_decomposition_iff
          get_lev_last)
       apply (rule_tac x=\<open>lit_of (last M')\<close> in exI)
       apply auto
        apply (rule_tac x=\<open>butlast M'\<close> in exI)
        apply (case_tac \<open>last M'\<close>)
         apply (auto simp: nth_append simp del: append_butlast_last_id)
        apply (metis append_butlast_last_id)
       defer
       apply (rule_tac x=\<open>lit_of (last M')\<close> in exI)
       apply auto
        apply (rule_tac x=\<open>butlast M'\<close> in exI)
        apply (case_tac \<open>last M'\<close>)
         apply (auto simp: nth_append snoc_eq_iff_butlast' count_decided_ge_get_maximum_level
          ex_decomp_get_ann_decomposition_iff get_lev_last)
      done
    done
qed


lemma find_decomp_wl_imp_find_decomp_wl':
  \<open>(uncurry2 find_decomp_wl_imp, uncurry2 find_decomp_wvmtf_ns) \<in>
    [find_decomp_wvmtf_ns_pre]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: find_decomp_wvmtf_ns_pre_def simp del: twl_st_of_wl.simps
       intro!: find_decomp_wl_imp_le_find_decomp_wl')


definition find_decomp_wvmtf_ns_pre_full where
  \<open>find_decomp_wvmtf_ns_pre_full M' = (\<lambda>(((M, E), L), vm).
      \<exists>N U D NE UE Q W. twl_struct_invs (twl_st_of_wl None (M, N, U, D, NE, UE, Q, W)) \<and>
       E \<noteq> None \<and> the E \<noteq> {#} \<and> L = lit_of (hd M) \<and>
       M \<noteq> [] \<and> ex_decomp_of_max_lvl M D L \<and>
       the E \<subseteq># the D \<and> D \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and>
      vm \<in> vmtf M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the E) \<and> -L \<in># the E \<and> M = M')\<close>

sepref_register find_decomp_wvmtf_ns
lemma find_decomp_wl_imp_code_find_decomp_wl'[sepref_fr_rules]:
  \<open>(uncurry2 find_decomp_wl_imp_code, uncurry2 (PR_CONST find_decomp_wvmtf_ns))
     \<in> [\<lambda>((b, a), c). find_decomp_wvmtf_ns_pre ((b, a), c)]\<^sub>a
     trail_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>
    trail_assn *a vmtf_remove_conc\<close>
  using find_decomp_wl_imp_code[unfolded PR_CONST_def, FCOMP find_decomp_wl_imp_find_decomp_wl']
  unfolding PR_CONST_def
  .

sepref_thm find_decomp_wl_imp'_code
  is \<open>uncurry (PR_CONST find_decomp_wl_st_int)\<close>
  :: \<open>[\<lambda>(highest, (M', N, U, D, W, Q, vm, \<phi>)).
         find_decomp_wvmtf_ns_pre ((M', highest), vm)]\<^sub>a
       uint32_nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d  \<rightarrow>
        (twl_st_heur_assn)\<close>
  unfolding find_decomp_wl_st_int_def PR_CONST_def twl_st_heur_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) find_decomp_wl_imp'_code
   uses isasat_input_bounded_nempty.find_decomp_wl_imp'_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp'_code_def

lemmas find_decomp_wl_imp'_code_hnr[sepref_fr_rules] =
  find_decomp_wl_imp'_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


lemma find_decomp_wl_st_int_find_decomp_wl_nlit:
  \<open>(uncurry find_decomp_wl_st_int, uncurry find_decomp_wl_nlit) \<in>
      [\<lambda>(highest, S). True]\<^sub>f
      Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have [simp]: \<open>(Decided K # aq, M2) \<in> set (get_all_ann_decomposition ba) \<Longrightarrow> no_dup ba \<Longrightarrow>
       no_dup aq\<close> for ba K aq M2
    by (auto dest!: get_all_ann_decomposition_exists_prepend dest: no_dup_appendD)
  show ?thesis
  unfolding no_resolve_def no_skip_def find_decomp_wl_nlit_def
    find_decomp_wl_st_int_def find_decomp_wvmtf_ns_def
  apply (intro frefI nres_relI)
  subgoal premises p for S S'
    using p
    by (cases S, cases S')
      (auto 5 5 intro!: SPEC_rule
        simp: find_decomp_wl_st_def find_decomp_wl'_def find_decomp_wl_def lbd_empty_def
        RES_RETURN_RES2 conc_fun_SPEC)
  done
qed

sepref_register find_decomp_wl_nlit
lemma find_decomp_wl_imp'_code_find_decomp_wl[sepref_fr_rules]:
  fixes M :: \<open>(nat, nat) ann_lits\<close>
  shows \<open>(uncurry find_decomp_wl_imp'_code, uncurry (PR_CONST find_decomp_wl_nlit)) \<in>
    [find_decomp_wl_pre]\<^sub>a
       uint32_nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow>
     twl_st_heur_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  define L where L: \<open>L \<equiv> -lit_of (hd M)\<close>
  have H: \<open>?c
       \<in> [comp_PRE (nat_rel \<times>\<^sub>f Id) (\<lambda>(highest, S). True)
     (\<lambda>_ (highest, M', N, U, D, W, Q, vm, \<phi>).
         find_decomp_wvmtf_ns_pre ((M', highest), vm))
     (\<lambda>_. True)]\<^sub>a hrp_comp (uint32_nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d)
                    (nat_rel \<times>\<^sub>f Id) \<rightarrow> hr_comp twl_st_heur_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF find_decomp_wl_imp'_code_hnr[unfolded PR_CONST_def]
         find_decomp_wl_st_int_find_decomp_wl_nlit]
    unfolding PR_CONST_def
    .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def find_decomp_wl_pre_def find_decomp_wvmtf_ns_pre_def highest_lit_def
        twl_st_heur_no_clvls_def
    by (fastforce simp del: twl_st_of_wl.simps)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
       hr_comp_prod_conv hr_comp_Id2 ..
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

definition extract_shorter_conflict_wl_pre where
  \<open>extract_shorter_conflict_wl_pre S \<longleftrightarrow>
      twl_struct_invs (twl_st_of_wl None S) \<and>
            twl_stgy_invs (twl_st_of_wl None S) \<and>
            get_conflict_wl S \<noteq> None \<and> get_conflict_wl S \<noteq> Some {#} \<and> no_skip S \<and> no_resolve S \<and>
            literals_are_\<L>\<^sub>i\<^sub>n S\<close>

definition size_conflict_wl :: \<open>nat twl_st_wl \<Rightarrow> nat\<close> where
  \<open>size_conflict_wl S = size (the (get_conflict_wl S))\<close>

sepref_thm size_conflict_wl_code
  is \<open>RETURN o size_conflict_wl_heur\<close>
  :: \<open>twl_st_heur_lookup_lookup_clause_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding size_conflict_wl_heur_def twl_st_heur_lookup_lookup_clause_assn_def
  by sepref

concrete_definition (in -) size_conflict_wl_code
   uses isasat_input_bounded_nempty.size_conflict_wl_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) size_conflict_wl_code_def

lemmas size_conflict_wl_code_hnr[sepref_fr_rules] =
   size_conflict_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

(* TODO Kill *)
lemma size_conflict_wl_heur_size_conflict_wl:
  \<open>(RETURN o size_conflict_wl_heur, RETURN o size_conflict_wl) \<in>
   [\<lambda>S. get_conflict_wl S \<noteq> None]\<^sub>f twl_st_wl_heur_lookup_lookup_clause_rel O twl_st_heur_no_clvls \<rightarrow>
    \<langle>nat_rel\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: size_conflict_wl_heur_def size_conflict_wl_def
      twl_st_wl_heur_lookup_lookup_clause_rel_def size_lookup_conflict_def
      option_lookup_clause_rel_def
      lookup_clause_rel_def twl_st_heur_no_clvls_def)

(* 
theorem size_conflict_wl_hnr[sepref_fr_rules]:
  \<open>(size_conflict_wl_code, RETURN o size_conflict_wl)
    \<in> [\<lambda>S. get_conflict_wl S \<noteq> None]\<^sub>a
      twl_st_no_clvls_assn\<^sup>k  \<rightarrow> uint32_nat_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE
       (twl_st_wl_heur_lookup_lookup_clause_rel O
        twl_st_heur_no_clvls)
       (\<lambda>S. get_conflict_wl S \<noteq> None) (\<lambda>_ _. True)
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       (twl_st_heur_lookup_lookup_clause_assn\<^sup>k)
                       (twl_st_wl_heur_lookup_lookup_clause_rel O
                        twl_st_heur_no_clvls) \<rightarrow> hr_comp
                     uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF size_conflict_wl_code_hnr
    size_conflict_wl_heur_size_conflict_wl] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_pol_def trail_pol_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_no_clvls_assn_alt_def
    ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed
 *)

(* type_synonym (in -) lookup_clause_rel_with_cls = \<open>nat clause_l \<times> bool option list\<close>
type_synonym (in -) conflict_with_cls_assn = \<open>uint32 array \<times> bool option array\<close>

type_synonym twl_st_wll_confl_with_cls =
  \<open>trail_pol_assn \<times> clauses_wl \<times> nat \<times> conflict_with_cls_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn\<close>

definition option_lookup_clause_rel_with_cls_removed
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> (lookup_clause_rel_with_cls \<times> nat clause option) set\<close>
where
  \<open>option_lookup_clause_rel_with_cls_removed L L' = {((C, xs), D). D \<noteq> None \<and> (unwatched_l C, the D) \<in> list_mset_rel \<and>
    mset_as_position xs {#} \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs) \<and> C!0 = L \<and> C!1 = L' \<and> length C \<ge> 2}\<close>


definition option_lookup_clause_rel_with_cls
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> (lookup_clause_rel_with_cls \<times> nat clause option) set\<close>
where
  \<open>option_lookup_clause_rel_with_cls L L' = {((C, xs), D). D \<noteq> None \<and> (C, the D) \<in> list_mset_rel \<and>
    mset_as_position xs {#} \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs) \<and> C!0 = L \<and> C!1 = L' \<and> length C \<ge> 2}\<close>

definition option_lookup_clause_rel_with_cls_removed1 :: \<open>(nat clause_l \<times> nat clause option) set\<close> where
  \<open>option_lookup_clause_rel_with_cls_removed1 = {(C, D). D \<noteq> None \<and> (C, the D) \<in> list_mset_rel}\<close>

abbreviation (in -) conflict_with_cls_int_assn :: \<open>lookup_clause_rel_with_cls \<Rightarrow> conflict_with_cls_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_int_assn \<equiv>
    (array_assn unat_lit_assn *a array_assn (option_assn bool_assn))\<close>

definition conflict_with_cls_assn_removed
 :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat clause option \<Rightarrow> conflict_with_cls_assn \<Rightarrow> assn\<close>
where
 \<open>conflict_with_cls_assn_removed L L' \<equiv>
   hr_comp conflict_with_cls_int_assn (option_lookup_clause_rel_with_cls_removed L L')\<close>

definition conflict_with_cls_assn :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat clause option \<Rightarrow>
   conflict_with_cls_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_assn L L' \<equiv> hr_comp conflict_with_cls_int_assn (option_lookup_clause_rel_with_cls L L')\<close>

definition option_lookup_clause_rel_removed :: \<open>_ set\<close> where
  \<open>option_lookup_clause_rel_removed =
   {((b, n, xs), C). C \<noteq> None \<and> n \<ge> 2 \<and> n \<le> length xs \<and>
      ((b, n - 2, xs), C) \<in> option_lookup_clause_rel}\<close>


type_synonym (in -) twl_st_wl_heur_W_confl_with_cls =
  \<open>(nat,nat) ann_lits \<times> nat clause_l list \<times> nat \<times>
    lookup_clause_rel_with_cls \<times> nat clause \<times> nat list list \<times> vmtf_remove_int \<times> bool list\<close>

text \<open>
  \<^item> We are filling D starting from the end (index \<^term>\<open>n\<close>)
  \<^item> We are changing position one and two.
\<close>
definition conflict_to_conflict_with_cls
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat literal list \<Rightarrow> conflict_option_rel \<Rightarrow> (nat literal list \<times> conflict_option_rel) nres\<close>
where
  \<open>conflict_to_conflict_with_cls = (\<lambda>_ _ D (_, n, xs). do {
     (_, _, C, zs) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, m, C, zs). i \<le> length zs \<and> length zs = length xs \<and>
          length C = n \<and> m \<le> length C \<and> C!0 = D!0 \<and> C!1 = D!1\<^esup>
       (\<lambda>(i, m, C, zs). m > 2)
       (\<lambda>(i, m, C, zs). do {
           ASSERT(i < length xs);
           ASSERT(i \<le> uint_max div 2);
           ASSERT(m > 2);
           ASSERT(zs ! i \<noteq> None \<longrightarrow> Pos i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
           case zs ! i of
             None \<Rightarrow> RETURN (i+1, m, C, zs)
           | Some b \<Rightarrow> RETURN (i+1, m-1, C[m-1 := (if b then Pos i else Neg i)], zs[i := None])
       })
       (0, n, D, xs);
     RETURN (C, (True, zero_uint32_nat, zs))
  }
  )\<close>

definition conflict_to_conflict_with_cls_spec where
  \<open>conflict_to_conflict_with_cls_spec _ D = D\<close>

definition list_of_mset2_None_droped where
  \<open>list_of_mset2_None_droped L L' _ D = SPEC(\<lambda>(E, F). mset (unwatched_l E) = the D \<and> E!0 = L \<and> E!1 = L' \<and>
     F = None \<and> length E \<ge> 2)\<close>
 *)

(* lemma conflict_to_conflict_with_cls_id:
  \<open>(uncurry3 conflict_to_conflict_with_cls, uncurry3 list_of_mset2_None_droped) \<in>
    [\<lambda>(((L, L'),D), C). C \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> length D = size (the C) + 2 \<and>
      L = D!0 \<and> L' = D!1]\<^sub>f
      Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f option_lookup_clause_rel_removed  \<rightarrow>
       \<langle>Id \<times>\<^sub>f option_lookup_clause_rel\<rangle> nres_rel\<close>
   (is \<open>_ \<in> [_]\<^sub>f _ \<rightarrow> \<langle>?R\<rangle>nres_rel\<close>)
proof -
  have H: \<open>conflict_to_conflict_with_cls L L' D (b, n, xs) \<le> \<Down> ?R (list_of_mset2_None_droped L L' D (Some C))\<close>
    if
      ocr: \<open>((b, n, xs), Some C) \<in> option_lookup_clause_rel_removed\<close> and
      lits_\<A>\<^sub>i\<^sub>n: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C\<close> and
      len_D: \<open>length D = size C + 2\<close> and
      [simp]: \<open>D!0 = L\<close>\<open>D!Suc 0 = L'\<close>
    for b n xs C D L L'
  proof -
    define I' where
      [simp]: \<open>I' = (\<lambda>(i, m, D, zs).
              ((b, m, zs), Some (filter_mset (\<lambda>L. atm_of L \<ge> i) C)) \<in> option_lookup_clause_rel_removed \<and>
               m - 2 = length (filter (op \<noteq> None) zs) \<and>
               i + (m - 2) + length (filter (op = None) (drop i zs)) = length zs \<and> (\<forall>k < i. zs ! k = None) \<and>
               mset (drop m D) = filter_mset (\<lambda>L. atm_of L < i) C \<and>
               length D \<ge> 2 \<and>
               m \<ge> 2)\<close>
    let ?I' = I'
    let ?C = \<open>C\<close>
    let ?I = \<open>\<lambda>xs n (i, m, E, zs). i \<le> length zs \<and> length zs = length xs \<and> length E = n \<and>
          m \<le> length E \<and> E!0 = D!0 \<and> E!1 = D!1\<close>
    let ?cond = \<open>\<lambda>s. case s of (i, m, C, zs) \<Rightarrow> 2 < m\<close>
    have n_le: \<open>n \<le> length xs\<close> and b: \<open>b = False\<close> and
       dist_C: \<open>distinct_mset C\<close> and
       tauto_C: \<open>\<not> tautology C\<close> and
       atms_le_xs: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close> and
       n_size: \<open>n = 2 + size C\<close> and
       map: \<open>mset_as_position xs C\<close>
      using mset_as_position_length_not_None[of xs ?C] that  mset_as_position_distinct_mset[of xs ?C]
        mset_as_position_tautology[of xs ?C] len_D
      by (auto simp: option_lookup_clause_rel_def option_lookup_clause_rel_removed_def lookup_clause_rel_def
          tautology_add_mset)
    have size_C: \<open>size C \<le> 1 + uint_max div 2\<close>
      using simple_clss_size_upper_div2[OF lits_\<A>\<^sub>i\<^sub>n dist_C tauto_C] .

    have final: \<open>\<not> (case s of (i, m, C, zs) \<Rightarrow> 2 < m) \<Longrightarrow>
    s \<in> {x. (case x of (_, _, C, zs) \<Rightarrow> RETURN (C, True, zero_uint32_nat, zs))
              \<le> RES ((Id \<times>\<^sub>f option_lookup_clause_rel)\<inverse> ``
                      {(E, F).
                       mset (unwatched_l E) = the (Some C) \<and>
                       E ! 0 = L \<and> E ! 1 = L' \<and> F = None \<and> 2 \<le> length E})}\<close>
      if
        s0: \<open>?I baa aa s\<close> and
        s1: \<open>?I' s\<close> and
        s:
          \<open>\<not> ?cond s\<close>
          \<open>(b, n, xs) = (a, ba)\<close>
          \<open>ba = (aa, baa)\<close>
      for a ba aa baa s
    proof -
      obtain ab bb ac bc ad bd where
        s': \<open>s = (ab, bb)\<close>
          \<open>bb = (ac, bc)\<close>
          \<open>bc = (ad, bd)\<close>
        by (cases s) auto
      then have [simp]: \<open>ac = 2\<close> \<open>s = (ab, 2, ad, bd)\<close> \<open>bb = (2, ad, bd)\<close> \<open>bc = (ad, bd)\<close> \<open>ba = (aa, baa)\<close>
        \<open>n = aa\<close>\<open>xs = baa\<close>
        using s s1 by auto
      have \<open>((b, 2, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close> and
         le_ad: \<open>length ad \<ge> 2\<close>
        using s1 by auto
      then have [simp]: \<open>{#L \<in># C. ab \<le> atm_of L#} = {#}\<close> and map': \<open>mset_as_position bd {#}\<close>
        unfolding option_lookup_clause_rel_removed_def option_lookup_clause_rel_def lookup_clause_rel_def by auto
      have [simp]: \<open>length bd = length xs\<close>
        using s0 by auto
      have [iff]: \<open>\<not>x < ab \<longleftrightarrow> ab \<le> x\<close> for x
        by auto
      have \<open>{#L \<in># C. atm_of L < ab#} = C\<close>
        using multiset_partition[of C \<open>\<lambda>L. atm_of L < ab\<close>] by auto
      then have [simp]: \<open>mset (unwatched_l ad) = C\<close>
        using s1 by auto
      have [simp]: \<open>ad ! 0 = L\<close> \<open>ad ! Suc 0 = L'\<close>
        using s0 unfolding s by auto
      show ?thesis
        using map' atms_le_xs le_ad by (auto simp: option_lookup_clause_rel_with_cls_removed_def
            list_mset_rel_def br_def Image_iff option_lookup_clause_rel_def lookup_clause_rel_def)
    qed
    have init: \<open>I' (0, aa, D, baa)\<close>
      if
        \<open>(b, n, xs) = (a, ba)\<close> and
        \<open>ba = (aa, baa)\<close>
      for a ba aa baa
      using ocr that n_le n_size size_C len_D mset_as_position_length_not_None[OF map]
      sum_length_filter_compl[of \<open>op = None\<close> xs]
      by auto

    have in_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      if
        I: \<open>?I baa aa s\<close> and
        I': \<open>I' s\<close> and
        cond: \<open>?cond s\<close> and
        s: \<open>s = (ab, bb)\<close>
          \<open>bb = (ac, bc)\<close>
          \<open>bc = (ad, bd)\<close>
          \<open>(b, n, xs) = (a, ba)\<close>
          \<open>ba = (aa, baa)\<close> and
        ab_baa: \<open>ab < length baa\<close> and
        bd_ab: \<open>bd ! ab \<noteq> None\<close>
      for a ba aa baa s ab bb ac bc ad bd
    proof -
      have \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close>
        using I' unfolding I'_def s by auto
      then have map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close> and
        le_bd: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length bd\<close>
        using b unfolding option_lookup_clause_rel_removed_def option_lookup_clause_rel_def lookup_clause_rel_def
        by auto
      have \<open>ab < length bd\<close>
        using I I' cond s unfolding I' by auto
      then have ab_in_C: \<open>Pos ab \<in># C \<or> Neg ab \<in># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>]
          bd_ab lits_\<A>\<^sub>i\<^sub>n by auto
      then show ?thesis
        using lits_\<A>\<^sub>i\<^sub>n
        by (auto dest!: multi_member_split simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    qed
    have le_uint_max_div2: \<open>ab \<le> uint_max div 2\<close>
      if
        \<open>(b, n, xs) = (a, ba)\<close> and
        \<open>ba = (aa, baa)\<close> and
        \<open>?I baa aa s\<close> and
        I': \<open>I' s\<close> and
        m: \<open>?cond s\<close> and
        s:
          \<open>s = (ab, bb)\<close>
          \<open>bb = (ac, bc)\<close>
          \<open>bc = (ad, bd)\<close> and
        \<open>ab < length baa\<close>
      for a ba aa baa s ab bb ac bc ad bd
    proof (rule ccontr)
      assume le: \<open>\<not> ?thesis\<close>
      have \<open>mset (drop ac ad) = {#L \<in># C. atm_of L < ab#}\<close> and
        ocr: \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close>
        using I' s unfolding I'_def by auto
      have \<open>L \<in># C \<Longrightarrow> atm_of L \<le> uint_max div 2\<close> for L
        using lits_\<A>\<^sub>i\<^sub>n in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max
        by (cases L)  (auto dest!: multi_member_split simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset uint_max_def)
      then have \<open>{#L \<in># C. ab \<le> atm_of L#} = {#}\<close>
        using le by (force simp: filter_mset_empty_conv)
      then show False
        using m s ocr unfolding option_lookup_clause_rel_removed_def option_lookup_clause_rel_def lookup_clause_rel_def by auto
    qed
    have IH_I': \<open>I' (ab + 1, ac, ad, bd)\<close>
      if
        I: \<open>?I baa aa s\<close> and
        I': \<open>I' s\<close> and
        m: \<open>?cond s\<close> and
        s: \<open>s = (ab, bb)\<close>
          \<open>bb = (ac, bc)\<close>
          \<open>bc = (ad, bd)\<close>
          \<open>(b, n, xs) = (a, ba)\<close>
          \<open>ba = (aa, baa)\<close> and
        ab_le: \<open>ab < length baa\<close> and
        \<open>ab \<le> uint_max div 2\<close> and
        \<open>2 < ac\<close> and
        \<open>bd ! ab \<noteq> None \<longrightarrow> Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
        bd_ab: \<open>bd ! ab = None\<close>
      for a ba aa baa s ab bb ac bc ad bd
    proof -
      have [simp]: \<open>s = (ab, ac, ad, bd)\<close> \<open>bb = (ac, ad, bd)\<close> \<open>bc = (ad, bd)\<close>
        \<open>ba = (aa, baa)\<close> \<open>n = aa\<close> \<open>xs = baa \<close> \<open>length bd = length baa\<close>
        using s I by auto
      have
        ocr: \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close> and
        eq: \<open>ab + length (filter (op \<noteq> None) bd) + length (filter (op = None) (drop ab bd)) = length baa\<close> and
        le_ab_None: \<open>\<forall>k<ab. bd ! k = None\<close> and
        ac: \<open>ac - 2 = length (filter (op \<noteq> None) bd)\<close> and
        ac2: \<open>ac \<ge> 2\<close> and
        le_ad: \<open>length ad \<ge> 2\<close>
        using I' unfolding I'_def by auto
      then have map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close> and
        le_bd: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length bd\<close>
        using b unfolding option_lookup_clause_rel_removed_def option_lookup_clause_rel_def lookup_clause_rel_def by auto
      have \<open>ab < length bd\<close>
        using I I' m by auto
      then have ab_in_C: \<open>Pos ab \<notin># C\<close> \<open>Neg ab \<notin># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>]
          bd_ab lits_\<A>\<^sub>i\<^sub>n by auto
      have [simp]: \<open>{#L \<in># C. atm_of L < ab#} = {#L \<in># C. atm_of L < Suc ab#}\<close>
        unfolding less_Suc_eq_le unfolding le_eq_less_or_eq
        using ab_in_C dist_C tauto_C filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Neg ab#}\<close>]
          filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Pos ab#}\<close>]
        by (auto dest!: multi_member_split
            simp: filter_union_or_split tautology_add_mset filter_mset_empty_conv less_Suc_eq_le
              order.order_iff_strict
            intro!: filter_mset_cong2)
      then have mset_drop: \<open>mset (drop ac ad) = {#L \<in># C. atm_of L < Suc ab#}\<close>
        using I' by auto

      have \<open>x \<in>#C \<Longrightarrow> atm_of x \<noteq> ab\<close> for x
        using bd_ab ocr
        mset_as_position_nth[of bd \<open>{#L \<in># C. ab \<le> atm_of L#}\<close> x]
        mset_as_position_nth[of bd \<open>{#L \<in># C. ab \<le> atm_of L#}\<close> \<open>-x\<close>]
        unfolding option_lookup_clause_rel_def lookup_clause_rel_def option_lookup_clause_rel_removed_def
        by force
      then have \<open>{#L \<in># C. ab \<le> atm_of L#} = {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using s by (force intro!: filter_mset_cong2)
      then have ocr': \<open>((b, ac, bd), Some {#L \<in># C. Suc ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close>
        using I' s by auto

      have
        x1a: \<open>ac - 2 = size {#L \<in># C. ab \<le> atm_of L#}\<close> \<open>ac \<ge> 2\<close> and
        map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close>
        using ocr unfolding option_lookup_clause_rel_def lookup_clause_rel_def option_lookup_clause_rel_removed_def
        by auto

      have [iff]: \<open>ab + length (filter (op \<noteq> None) x2b) = length x2b \<longleftrightarrow> ab = length (filter (op = None) x2b)\<close> for x2b
        using sum_length_filter_compl[of \<open>op \<noteq> None\<close> x2b] by auto
      have filter_take_ab: \<open>filter (op = None) (take ab bd) = take ab bd\<close>
        apply (rule filter_id_conv[THEN iffD2])
        using le_ab_None by (auto simp: nth_append take_set split: if_splits)
      have Suc_le_bd: \<open>Suc ab + length (filter (op \<noteq> None) bd) + length (filter (op = None) (drop (Suc ab )bd)) =
          length baa\<close>
        using b ac Cons_nth_drop_Suc[of ab bd, symmetric] ab_le eq bd_ab by auto
      have le_Suc_None: \<open>k < Suc ab \<Longrightarrow> bd ! k = None\<close> for k
        using le_ab_None bd_ab  by (auto simp: less_Suc_eq)

      show ?thesis using le_ad mset_drop ocr' Suc_le_bd le_Suc_None ac ac2 unfolding I'_def by auto
    qed
    have IH_I'_notin: \<open>I' (ab + 1, ac - 1, ad[ac - 1 := if x then Pos ab else Neg ab],
          bd[ab := None])\<close>
      if
        I: \<open>?I baa aa s\<close> and
        I': \<open>I' s\<close> and
        m: \<open>?cond s\<close> and
        s:
          \<open>s = (ab, bb)\<close>
          \<open>bb = (ac, bc)\<close>
          \<open>bc = (ad, bd)\<close>
          \<open>(b, n, xs) = (a, ba)\<close>
          \<open>ba = (aa, baa)\<close> and
        ab_le: \<open>ab < length baa\<close> and
        \<open>ab \<le> uint_max div 2\<close> and
        \<open>2 < ac\<close> and
        \<open>bd ! ab \<noteq> None \<longrightarrow> Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
        bd_ab_x: \<open>bd ! ab = Some x\<close>
      for a ba aa baa s ab bb ac bc ad bd x
    proof -
      have [simp]: \<open>bb = (ac, ad, bd)\<close> \<open>bc = (ad, bd)\<close> \<open>ba = (aa, baa)\<close> \<open>n = aa\<close> \<open>xs = baa\<close>
        \<open>s = (ab, (ac, (ad, bd)))\<close>
        \<open>length baa = length bd\<close>
        using I s by auto
      have \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close> and
        ac: \<open>ac - 2 = length (filter (op \<noteq> None) bd)\<close> and
        eq: \<open>ab + (ac - 2) + length (filter (op = None) (drop ab bd)) = length bd\<close> and
        ac2: \<open>ac \<ge> 2\<close> and
        le_ad: \<open>length ad \<ge> 2\<close>
        using I' unfolding I'_def s by auto
      then have map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close> and
        le_bd: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length bd\<close> and
        ocr: \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close>
        using b unfolding option_lookup_clause_rel_def lookup_clause_rel_def option_lookup_clause_rel_removed_def
        by auto
      have \<open>ab < length bd\<close>
        using I I' m by auto
      then have ab_in_C: \<open>(if x then Pos ab else Neg ab) \<in># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>]
          bd_ab_x lits_\<A>\<^sub>i\<^sub>n by auto
      have \<open>distinct_mset {#L \<in># C. ab \<le> atm_of L#}\<close> \<open>\<not> tautology {#L \<in># C. ab \<le> atm_of L#}\<close>
        using mset_as_position_distinct_mset[OF map] mset_as_position_tautology[OF map] by fast+
      have [iff]: \<open>\<not> ab < atm_of a \<and> ab = atm_of a \<longleftrightarrow>  (ab = atm_of a)\<close> for a :: \<open>nat literal\<close> and ab
        by auto
      have H1: \<open>{#L \<in># C.  ab \<le> atm_of L#} = (if x then add_mset (Pos ab) else add_mset (Neg ab)) {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using ab_in_C unfolding Suc_le_eq unfolding le_eq_less_or_eq
        using dist_C tauto_C filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Neg ab#}\<close>]
          filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Pos ab#}\<close>]
        by (auto dest!: multi_member_split simp: filter_union_or_split tautology_add_mset filter_mset_empty_conv)
      have H2: \<open>{#L \<in># C. Suc ab \<le> atm_of L#} = remove1_mset (Pos ab) (remove1_mset (Neg ab) {#L \<in># C. ab \<le> atm_of L#})\<close>
        by (auto simp: H1)
      have map': \<open>mset_as_position (bd[ab := None]) {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        unfolding H2
        apply (rule mset_as_position_remove)
        using map ab_le by auto
      have c_r: \<open>((b, ac - Suc 0, bd[ab := None]), Some {#L \<in># C. Suc ab \<le> atm_of L#}) \<in> option_lookup_clause_rel_removed\<close>
        using ocr b map' m ac by (cases x) (auto simp: option_lookup_clause_rel_removed_def
            option_lookup_clause_rel_def lookup_clause_rel_def H1)
      have H3: \<open>(if x then add_mset (Pos ab) else add_mset (Neg ab)) {#L \<in># C. atm_of L < ab#} = {#L \<in># C. atm_of L < Suc ab#}\<close>
        using ab_in_C unfolding Suc_le_eq unfolding le_eq_less_or_eq
        using dist_C tauto_C filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Neg ab#}\<close>]
          filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Pos ab#}\<close>]
        by (auto dest!: multi_member_split
            simp: filter_union_or_split tautology_add_mset filter_mset_empty_conv less_Suc_eq_le
              order.order_iff_strict
            intro!: filter_mset_cong2)
      have ac_ge0: \<open>ac > 0\<close>
        using m by auto
      then have \<open>ac - Suc 0 < length ad\<close> and \<open>mset (drop ac ad) = {#L \<in># C. atm_of L < ab#}\<close>
        using I' I m by auto
      then have 3: \<open>mset (drop (ac - Suc 0) (ad[ac - Suc 0 := (if x then Pos ab else Neg ab)])) = {#L \<in># C. atm_of L < Suc ab#}\<close>
        using Cons_nth_drop_Suc[symmetric, of \<open>ac - 1\<close> \<open>ad\<close>] ac_ge0
        by (auto simp: drop_update_swap H3[symmetric])
      have ac_filter: \<open>ac - Suc (Suc (Suc 0)) = length (filter (op \<noteq> None) (bd[ab := None]))\<close>
        apply (subst length_filter_update_true)
        using ac bd_ab_x ab_le by auto
      have \<open>length (filter (op \<noteq> None) bd) \<ge> Suc 0\<close>
        using bd_ab_x ab_le nth_mem by (fastforce simp: filter_empty_conv)
      then have eq': \<open>Suc ab + length (filter (op \<noteq> None) (bd[ab := None])) + length (filter (op = None) (drop (Suc ab) bd)) = length bd\<close>
        using b ac Cons_nth_drop_Suc[of ab bd, symmetric] ab_le eq bd_ab_x ac2
        by (auto simp: length_filter_update_true)
      show ?thesis
        using b c_r that s ac_filter 3 eq' le_ad unfolding I'_def by auto
    qed
    show ?thesis
      supply WHILEIT_rule[refine_vcg del]
      unfolding conflict_to_conflict_with_cls_def Let_def list_of_mset2_None_droped_def conc_fun_RES
      apply refine_rcg
      unfolding bind_rule_complete_RES
      apply (refine_vcg WHILEIT_rule_stronger_inv_RES[where
            R = \<open>measure (\<lambda>(i :: nat, m :: nat, D :: nat clause_l, zs :: bool option list). length zs - i)\<close> and
            I' = \<open>I'\<close>] bind_rule_complete_RES)
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal using len_D n_size by auto
      subgoal using len_D n_size by auto
      subgoal by simp
      subgoal by simp
      subgoal by (rule init)
      subgoal using n_le by auto
      subgoal by (rule le_uint_max_div2)
      subgoal by auto
      subgoal by (rule in_\<L>\<^sub>a\<^sub>l\<^sub>l) assumption+
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (rule IH_I')
      subgoal by auto
      subgoal using b by (auto simp: less_Suc_eq)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (rule IH_I'_notin)
      subgoal by auto
      subgoal by (rule final) assumption+
      done
    qed

  show ?thesis
    apply (intro frefI nres_relI)
    apply clarify
    subgoal for a aa ab b ac ba y
      using H by (auto simp: conflict_to_conflict_with_cls_spec_def)
    done
qed
 *)

lemma conflict_to_conflict_with_cls_code_helper:
  \<open>a1'b \<le> uint_max div 2 \<Longrightarrow> Suc a1'b \<le> uint_max\<close>
  \<open> 0 < a1'c \<Longrightarrow> one_uint32_nat \<le> a1'c\<close>
  \<open>fast_minus a1'c one_uint32_nat  = a1'c - 1\<close>
  by (auto simp: uint_max_def)

(* sepref_register conflict_to_conflict_with_cls
sepref_thm conflict_to_conflict_with_cls_code
  is \<open>uncurry3 (PR_CONST conflict_to_conflict_with_cls)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a(array_assn unat_lit_assn)\<^sup>d *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow>\<^sub>a
      array_assn unat_lit_assn *a conflict_option_rel_assn\<close>
  supply uint32_nat_assn_zero_uint32_nat[sepref_fr_rules] [[goals_limit=1]]
   Pos_unat_lit_assn'[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
   conflict_to_conflict_with_cls_code_helper[simp] uint32_2_hnr[sepref_fr_rules]
  unfolding conflict_to_conflict_with_cls_def array_fold_custom_replicate
    fast_minus_def[of \<open>_ :: nat\<close>, symmetric] PR_CONST_def
  apply (rewrite at \<open>\<hole> < length _\<close> annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at \<open>_ ! \<hole> \<noteq> None\<close> annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at \<open>\<hole> < _\<close> two_uint32_nat_def[symmetric])
  apply (rewrite at \<open>\<hole> < _\<close> annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at \<open>(\<hole>, _, _, _)\<close> zero_uint32_nat_def[symmetric])
  apply (rewrite at \<open>(zero_uint32_nat, \<hole>, _, _)\<close> annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at \<open>_ + \<hole>\<close> one_uint32_nat_def[symmetric])+
  apply (rewrite at \<open>fast_minus _ \<hole>\<close> one_uint32_nat_def[symmetric])+
  by sepref

concrete_definition (in -) conflict_to_conflict_with_cls_code
   uses isasat_input_bounded_nempty.conflict_to_conflict_with_cls_code.refine_raw
   is \<open>(uncurry3 ?f, _)\<in>_\<close>

prepare_code_thms (in -) conflict_to_conflict_with_cls_code_def

lemmas conflict_to_conflict_with_cls_code_refine[sepref_fr_rules] =
   conflict_to_conflict_with_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
 *)

(* lemma extract_shorter_conflict_with_cls_code_conflict_to_conflict_with_cls_spec[sepref_fr_rules]:
  \<open>(uncurry3 conflict_to_conflict_with_cls_code, uncurry3 list_of_mset2_None_droped)
    \<in> [\<lambda>(((L, L'), D), C). C \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and>
           length D = size (the C) + 2 \<and> L = D ! 0 \<and> L' = D ! 1]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a
     (hr_comp conflict_option_rel_assn option_lookup_clause_rel_removed)\<^sup>d \<rightarrow>
     clause_ll_assn *a option_lookup_clause_assn\<close>
  using conflict_to_conflict_with_cls_code_refine[unfolded PR_CONST_def,
    FCOMP conflict_to_conflict_with_cls_id]
  unfolding option_lookup_clause_assn_def
  by simp
 *)
(* definition remove2_from_conflict :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat cconflict \<Rightarrow> nat cconflict\<close> where
  \<open>remove2_from_conflict L L' C = Some (remove1_mset L (remove1_mset L' (the C)))\<close>

definition remove2_from_conflict_int
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> conflict_option_rel \<Rightarrow> conflict_option_rel\<close>
where
  \<open>remove2_from_conflict_int L L' = (\<lambda>(b, n, xs). (b, n, xs[atm_of L := None, atm_of L' := None]))\<close>

lemma remove2_from_conflict_int_remove2_from_conflict:
  \<open>(uncurry2 (RETURN ooo remove2_from_conflict_int), uncurry2 (RETURN ooo remove2_from_conflict)) \<in>
   [\<lambda>((L, L'), C). L \<in># the C \<and> L' \<in># the C \<and> C \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L \<noteq> L']\<^sub>f
    Id \<times>\<^sub>f Id \<times>\<^sub>f option_lookup_clause_rel \<rightarrow> \<langle>option_lookup_clause_rel_removed\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for K K' b n xs L L' bc C
    using mset_as_position_length_not_None[of xs C] mset_as_position_tautology[of xs C]
      mset_as_position_remove[of xs C \<open>atm_of L\<close>]
      mset_as_position_remove[of \<open>xs[atm_of L := None]\<close> \<open>remove1_mset L C\<close> \<open>atm_of L'\<close>]
    apply (cases L; cases L')
    by (auto simp: remove2_from_conflict_int_def remove2_from_conflict_def
      option_lookup_clause_rel_def lookup_clause_rel_def option_lookup_clause_rel_removed_def
      add_mset_eq_add_mset tautology_add_mset
      dest!: multi_member_split)
  done

sepref_thm remove2_from_conflict_code
  is \<open>uncurry2 (RETURN ooo remove2_from_conflict_int)\<close>
  :: \<open>[\<lambda>((L, L'), (b, n, xs)). atm_of L < length xs \<and> atm_of L' < length xs]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn\<close>
  unfolding remove2_from_conflict_int_def
  by sepref

concrete_definition (in -) remove2_from_conflict_code
   uses isasat_input_bounded_nempty.remove2_from_conflict_code.refine_raw
   is \<open>(uncurry2 ?f, _)\<in>_\<close>

prepare_code_thms (in -) remove2_from_conflict_code_def

lemmas remove2_from_conflict_code_hnr[sepref_fr_rules] =
   remove2_from_conflict_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

theorem remove2_from_conflict_hnr[sepref_fr_rules]:
  \<open>(uncurry2 remove2_from_conflict_code, uncurry2 (RETURN ooo remove2_from_conflict))
    \<in> [\<lambda>((L, L'), C). L \<in># the C \<and> L' \<in># the C \<and> C \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L \<noteq> L']\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow>
      hr_comp conflict_option_rel_assn option_lookup_clause_rel_removed\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f option_lookup_clause_rel)
          (\<lambda>((L, L'), C).
              L \<in># the C \<and>
              L' \<in># the C \<and>
              C \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L \<noteq> L')
          (\<lambda>_ ((L, L'), b, n, xs).
              atm_of L < length xs \<and> atm_of L' < length xs)
          (\<lambda>_. True)]\<^sub>a
      hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d)
                     (nat_lit_lit_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f option_lookup_clause_rel) \<rightarrow>
      hr_comp conflict_option_rel_assn option_lookup_clause_rel_removed\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF remove2_from_conflict_code_hnr
    remove2_from_conflict_int_remove2_from_conflict] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_pol_def trail_pol_def option_lookup_clause_rel_def
        lookup_clause_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep option_lookup_clause_assn_def by auto
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im PR_CONST_def apply assumption
    using pre ..
qed
 *)
(* definition list_of_mset2_None_int where
  \<open>list_of_mset2_None_int L L' C\<^sub>0 =  do {
     let n = size (the C\<^sub>0);
     ASSERT(n \<ge> 2);
     let D = replicate n L;
     let D = D[1 := L'];
     let C = remove2_from_conflict L L' C\<^sub>0;
     ASSERT(C \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> size (the C\<^sub>0) = size (the C) + 2 \<and>
       D!0 = L \<and> D!1 = L');
     list_of_mset2_None_droped L L' D C}\<close>

lemma (in -) list_length2E:
  \<open>length xs \<ge> 2 \<Longrightarrow> (\<And>x y zs. xs = x # y # zs \<Longrightarrow> zs = tl (tl xs) \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (cases xs; cases \<open>tl xs\<close>) auto

lemma list_of_mset2_None_int_list_of_mset2_None:
  \<open>(uncurry2 (list_of_mset2_None_int), uncurry2 list_of_mset2_None) \<in>
     [\<lambda>((L, L'), C). C \<noteq> None \<and> L \<in># the C \<and> L' \<in># the C \<and> L \<noteq> L' \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> distinct_mset (the C)]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: list_of_mset2_None_int_def list_of_mset2_None_def
      list_of_mset2_def conflict_to_conflict_with_cls_spec_def
      remove2_from_conflict_def add_mset_eq_add_mset RES_RETURN_RES
      literals_are_in_\<L>\<^sub>i\<^sub>n_sub literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset list_of_mset2_None_droped_def
      dest!: multi_member_split
      elim!: list_length2E)
 *)
definition size_conflict :: \<open>nat clause option \<Rightarrow> nat\<close> where
  \<open>size_conflict D = size (the D)\<close>

definition size_conflict_int :: \<open>conflict_option_rel \<Rightarrow> nat\<close> where
  \<open>size_conflict_int = (\<lambda>(_, n, _). n)\<close>

lemma size_conflict_code_refine_raw:
  \<open>(return o (\<lambda>(_, n, _). n), RETURN o size_conflict_int) \<in> conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare  (sep_auto simp: size_conflict_int_def)

concrete_definition (in -) size_conflict_code
   uses isasat_input_bounded_nempty.size_conflict_code_refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) size_conflict_code_def

lemmas size_conflict_code_hnr[sepref_fr_rules] =
   size_conflict_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma size_conflict_int_size_conflict:
  \<open>(RETURN o size_conflict_int, RETURN o size_conflict) \<in> [\<lambda>D. D \<noteq> None]\<^sub>f option_lookup_clause_rel \<rightarrow>
     \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: size_conflict_int_def size_conflict_def option_lookup_clause_rel_def
      lookup_clause_rel_def)

lemma size_conflict_hnr[sepref_fr_rules]:
  \<open>(size_conflict_code, RETURN \<circ> size_conflict) \<in> [\<lambda>x. x \<noteq> None]\<^sub>a option_lookup_clause_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using size_conflict_code_hnr[FCOMP size_conflict_int_size_conflict]
  unfolding option_lookup_clause_assn_def[symmetric]
  by simp

(* sepref_thm list_of_mset2_None_code
  is \<open>uncurry2 (PR_CONST list_of_mset2_None_int)\<close>
  :: \<open>[\<lambda>((L, L'), C). C \<noteq> None \<and> L \<in># the C \<and> L' \<in># the C \<and> L \<noteq> L' \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (the C)]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
         option_lookup_clause_assn\<^sup>d \<rightarrow> clause_ll_assn *a option_lookup_clause_assn\<close>
  supply [[goals_limit=1]] size_conflict_def[simp]
  unfolding list_of_mset2_None_int_def size_conflict_def[symmetric]
    array_fold_custom_replicate PR_CONST_def
  by sepref *)

(* concrete_definition (in -) list_of_mset2_None_code
   uses isasat_input_bounded_nempty.list_of_mset2_None_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) list_of_mset2_None_code_def

lemmas list_of_mset2_None_int_hnr[sepref_fr_rules] =
  list_of_mset2_None_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma list_of_mset2_None_hnr[sepref_fr_rules]:
  \<open>(uncurry2 list_of_mset2_None_code, uncurry2 list_of_mset2_None)
   \<in> [\<lambda>((a, b), ba). ba \<noteq> None \<and> a \<in># the ba \<and> b \<in># the ba \<and> a \<noteq> b \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (the ba) \<and> distinct_mset (the ba) \<and> a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> b \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow>
      clause_ll_assn *a option_lookup_clause_assn\<close>
  using list_of_mset2_None_int_hnr[unfolded PR_CONST_def, FCOMP list_of_mset2_None_int_list_of_mset2_None]
  by simp
 *)
definition (in isasat_input_ops) vmtf_rescore_body
 :: \<open>nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> phase_saver \<Rightarrow>
    (nat \<times> vmtf_remove_int \<times> phase_saver) nres\<close>
where
  \<open>vmtf_rescore_body C _ vm \<phi> = do {
         WHILE\<^sub>T\<^bsup>\<lambda>(i, vm, \<phi>). i \<le> length C  \<and>
            (\<forall>c \<in> set C. atm_of c < length \<phi> \<and> atm_of c < length (fst (fst vm)))\<^esup>
           (\<lambda>(i, vm, \<phi>). i < length C)
           (\<lambda>(i, vm, \<phi>). do {
               ASSERT(i < length C);
               let vm' = vmtf_mark_to_rescore (atm_of (C!i)) vm;
               let \<phi>' = save_phase_inv (C!i) \<phi>;
               RETURN(i+1, vm', \<phi>')
             })
           (0, vm, \<phi>)
    }\<close>

definition (in isasat_input_ops) vmtf_rescore
 :: \<open>nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> phase_saver \<Rightarrow>
       (vmtf_remove_int \<times> phase_saver) nres\<close>
where
  \<open>vmtf_rescore C M vm \<phi> = do {
      (_, vm, \<phi>) \<leftarrow> vmtf_rescore_body C M vm \<phi>;
      RETURN (vm, \<phi>)
    }\<close>

sepref_thm vmtf_rescore_code
  is \<open>uncurry3 vmtf_rescore\<close>
  :: \<open>(array_assn unat_lit_assn)\<^sup>k *\<^sub>a trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>\<^sub>a
       vmtf_remove_conc *a phase_saver_conc\<close>
  unfolding vmtf_rescore_def vmtf_mark_to_rescore_and_unset_def save_phase_inv_def vmtf_mark_to_rescore_def vmtf_unset_def
  vmtf_rescore_body_def
  supply [[goals_limit = 1]] fold_is_None[simp]
  by sepref

concrete_definition (in -) vmtf_rescore_code
   uses isasat_input_bounded_nempty.vmtf_rescore_code.refine_raw
   is \<open>(uncurry3 ?f, _)\<in>_\<close>

prepare_code_thms (in -) vmtf_rescore_code_def

lemmas vmtf_rescore_code_refine[sepref_fr_rules] =
   vmtf_rescore_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma vmtf_rescore_score_clause:
  \<open>(uncurry3 vmtf_rescore, uncurry3 rescore_clause) \<in>
     [\<lambda>(((C, M), vm), \<phi>). literals_are_in_\<L>\<^sub>i\<^sub>n (mset C) \<and> vm \<in> vmtf M \<and> phase_saving \<phi>]\<^sub>f
     (\<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle> nres_rel\<close>
proof -
  have H: \<open>vmtf_rescore_body C M vm \<phi> \<le>
        SPEC (\<lambda>(n :: nat, vm', \<phi>' :: bool list). phase_saving \<phi>' \<and> vm' \<in> vmtf M)\<close>
    if M: \<open>vm \<in> vmtf M\<close>\<open>phase_saving \<phi>\<close> and C: \<open>\<forall>c\<in>set C. atm_of c \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    for C vm \<phi> M
    unfolding vmtf_rescore_body_def vmtf_mark_to_rescore_def
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(i, _). length C - i)\<close> and
       I' = \<open>\<lambda>(i, vm', \<phi>'). phase_saving \<phi>' \<and> vm' \<in> vmtf M\<close>])
    subgoal by auto
    subgoal by auto
    subgoal using C M by (auto simp: vmtf_def phase_saving_def)
    subgoal using C M by auto
    subgoal using M by auto
    subgoal by auto
    subgoal unfolding save_phase_inv_def by auto
    subgoal using C unfolding phase_saving_def save_phase_inv_def by auto
    subgoal unfolding save_phase_inv_def phase_saving_def by auto
    subgoal using C by (auto simp: vmtf_append_remove_iff')
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
    subgoal by auto
    done
qed

lemma vmtf_rescore_code_rescore_clause[sepref_fr_rules]:
  \<open>(uncurry3 vmtf_rescore_code, uncurry3 (PR_CONST rescore_clause))
     \<in> [\<lambda>(((b, a), c), d). literals_are_in_\<L>\<^sub>i\<^sub>n (mset b) \<and> c \<in> vmtf a \<and>
         phase_saving d]\<^sub>a
       clause_ll_assn\<^sup>k *\<^sub>a trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>
        vmtf_remove_conc *a phase_saver_conc\<close>
  using vmtf_rescore_code_refine[FCOMP vmtf_rescore_score_clause]
  by auto

definition vmtf_flush' where
   \<open>vmtf_flush' _ = vmtf_flush\<close>

sepref_thm vmtf_flush_all_code
  is \<open>uncurry vmtf_flush'\<close>
  :: \<open>[\<lambda>(M, vm). vm \<in> vmtf M]\<^sub>a trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply [[goals_limit=1]] trail_dump_code_refine[sepref_fr_rules]
  unfolding vmtf_flush'_def
  by sepref

concrete_definition (in -) vmtf_flush_all_code
   uses isasat_input_bounded_nempty.vmtf_flush_all_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_flush_all_code_def

lemmas vmtf_flush_all_code_hnr[sepref_fr_rules] =
   vmtf_flush_all_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


lemma trail_bump_rescore:
  \<open>(uncurry vmtf_flush', uncurry flush) \<in> [\<lambda>(M, vm). vm \<in> vmtf M]\<^sub>f Id \<times>\<^sub>r Id  \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding vmtf_flush'_def flush_def
  apply (intro nres_relI frefI)
  apply clarify
  subgoal for a aa ab ac b ba ad ae af ag bb bc
    using vmtf_change_to_remove_order
    by auto
  done

lemma trail_dump_code_rescore[sepref_fr_rules]:
   \<open>(uncurry vmtf_flush_all_code, uncurry (PR_CONST flush)) \<in> [\<lambda>(M, vm). vm \<in> vmtf M]\<^sub>a
        trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
   (is \<open>_ \<in> [?cond]\<^sub>a ?pre \<rightarrow> ?im\<close>)
  using vmtf_flush_all_code_hnr[FCOMP trail_bump_rescore] by simp

definition st_remove_highest_lvl_from_confl :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl\<close> where
   \<open>st_remove_highest_lvl_from_confl S = S\<close>


sepref_register rescore_clause flush

sepref_thm propagate_bt_wl_D_code
  is \<open>uncurry2 (PR_CONST propagate_bt_wl_D_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_heur_assn\<close>
  supply [[goals_limit = 1]] uminus_\<A>\<^sub>i\<^sub>n_iff[simp] image_image[simp] append_ll_def[simp]
  rescore_clause_def[simp] flush_def[simp]
  unfolding propagate_bt_wl_D_heur_def twl_st_heur_assn_def cons_trail_Propagated_def[symmetric]
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

definition remove_last_int :: \<open>nat literal \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>remove_last_int = (\<lambda>L (b, n, xs). (True, 0, xs[atm_of L := None]))\<close>

lemma remove_last_int_remove_last:
  \<open>(uncurry (RETURN oo remove_last_int), uncurry remove_last) \<in>
    [\<lambda>(L, D). D \<noteq> None \<and> -L \<in># the D \<and> size (the D) = 1 \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>f Id \<times>\<^sub>r option_lookup_clause_rel \<rightarrow>
      \<langle>option_lookup_clause_rel\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (clarify dest!: size_1_singleton_mset)
  subgoal for a aa ab b ac ba y L
    using mset_as_position_remove[of b \<open>{#L#}\<close> \<open>atm_of L\<close>]
    by (cases L)
     (auto simp: remove_last_int_def remove_last_def option_lookup_clause_rel_def
        RETURN_RES_refine_iff lookup_clause_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
       uminus_lit_swap)
  done

sepref_thm remove_last_code
  is \<open>uncurry (RETURN oo (PR_CONST remove_last_int))\<close>
  :: \<open>[\<lambda>(L, (b, n, xs)). atm_of L < length xs]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow>
     conflict_option_rel_assn\<close>
  supply [[goals_limit=1]] uint32_nat_assn_zero_uint32_nat[sepref_fr_rules]
  unfolding remove_last_int_def PR_CONST_def zero_uint32_nat_def[symmetric]
  by sepref

concrete_definition (in -) remove_last_code
   uses isasat_input_bounded_nempty.remove_last_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) remove_last_code_def

lemmas remove_last_int_hnr[sepref_fr_rules] =
   remove_last_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

(* TODO Kill *)
theorem remove_last_hnr[sepref_fr_rules]:
  \<open>(uncurry remove_last_code, uncurry remove_last)
    \<in> [\<lambda>(L, D). D \<noteq> None \<and> -L \<in># the D \<and> size (the D) = 1 \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow> option_lookup_clause_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in>
    [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f option_lookup_clause_rel)
       (\<lambda>(L, D). D \<noteq> None \<and> -L \<in># the D \<and> size (the D) = 1 \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l)
       (\<lambda>_ (L, b, n, xs). atm_of L < length xs)
       (\<lambda>_. True)]\<^sub>a
     hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d)
              (nat_lit_lit_rel \<times>\<^sub>f option_lookup_clause_rel) \<rightarrow>
    hr_comp conflict_option_rel_assn option_lookup_clause_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF remove_last_int_hnr[unfolded PR_CONST_def]
    remove_last_int_remove_last] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def option_lookup_clause_rel_def lookup_clause_rel_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep option_lookup_clause_assn_def by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep option_lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_thm propagate_unit_bt_wl_D_code
  is \<open>uncurry (PR_CONST propagate_unit_bt_wl_D_int)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_heur_assn\<close>
  supply [[goals_limit = 1]] flush_def[simp] image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[simp]
  unfolding propagate_unit_bt_wl_D_int_def cons_trail_Propagated_def[symmetric] twl_st_heur_assn_def
  PR_CONST_def
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) propagate_unit_bt_wl_D_code
  uses isasat_input_bounded_nempty.propagate_unit_bt_wl_D_code.refine_raw
  is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_unit_bt_wl_D_code_def

lemmas propagate_unit_bt_wl_D_int_hnr[sepref_fr_rules] =
  propagate_unit_bt_wl_D_code.refine[OF isasat_input_bounded_nempty_axioms]

end

setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>

context isasat_input_bounded_nempty
begin

(* lemma backtrack_wl_D_nlit_invariants:
  assumes inv: \<open>backtrack_wl_D_inv S\<close>
  shows
   \<open>get_trail_wl S \<noteq> []\<close> (is ?Trail) and
  \<open>extract_shorter_conflict_wl_pre S\<close> (is ?extract_shorter) and
   \<open>extract_shorter_conflict_list_heur_st_pre S\<close> (is ?A) and
     \<open>RETURN (T, highest) \<le> extract_shorter_conflict_wl_nlit_st S \<Longrightarrow>
       find_decomp_wl_pre ((lit_of_hd_trail_st S, highest), T)\<close> (is \<open>_ \<Longrightarrow> ?B\<close>) and
   \<open>RETURN (T, highest) \<le> extract_shorter_conflict_wl_nlit_st S \<Longrightarrow>
       RETURN V \<le> find_decomp_wl_nlit (lit_of_hd_trail_st S) highest T \<Longrightarrow>
       \<exists>y. get_conflict_wl V = Some y\<close>
       (is \<open>_ \<Longrightarrow> _ \<Longrightarrow> ?C\<close>) and
    \<open>RETURN (T, highest) \<le> extract_shorter_conflict_wl_nlit_st S \<Longrightarrow>
       RETURN V \<le> find_decomp_wl_nlit (lit_of_hd_trail_st S) highest T \<Longrightarrow>
        Suc 0 < size (the (get_conflict_wl V)) \<Longrightarrow>
       \<exists>a b. highest = Some (a, b)\<close>
       (is \<open>_ \<Longrightarrow> _ \<Longrightarrow>  _ \<Longrightarrow> ?D\<close>) and
   \<open>RETURN (T, highest) \<le> extract_shorter_conflict_wl_nlit_st S \<Longrightarrow>
       RETURN V \<le> find_decomp_wl_nlit (lit_of_hd_trail_st S) highest T \<Longrightarrow>
       Suc 0 < size (the (get_conflict_wl V)) \<Longrightarrow>
       propagate_bt_wl_D_pre ((lit_of_hd_trail_st S, fst (the highest)), V)\<close>
       (is \<open>_ \<Longrightarrow> _ \<Longrightarrow>  _ \<Longrightarrow> ?E\<close>) and
   \<open>RETURN (T, highest) \<le> extract_shorter_conflict_wl_nlit_st S \<Longrightarrow>
       RETURN V \<le> find_decomp_wl_nlit (lit_of_hd_trail_st S) highest T \<Longrightarrow>
       \<not> Suc 0 < size (the (get_conflict_wl V)) \<Longrightarrow>
       propagate_unit_bt_wl_D_pre (lit_of_hd_trail_st S, V)\<close>
      (is \<open>_ \<Longrightarrow> _ \<Longrightarrow>  _ \<Longrightarrow>  ?F\<close>)
proof -
  obtain M N U D NE UE WS Q where
    S: \<open>S = (M, N, U, D, NE, UE, WS, Q)\<close>
    by (cases S)
  have
    M: \<open>M \<noteq> []\<close> and
    trail_S: \<open>get_trail_wl S \<noteq> []\<close> and
    nss: \<open>no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close> and
    nsr: \<open>no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of None (st_l_of_wl None S))\<close> and
    add_invs: \<open>twl_list_invs (st_l_of_wl None S)\<close> and
    D: \<open>D \<noteq> None\<close> \<open>the D \<noteq> {#}\<close> and
    confl_S: \<open>get_conflict_wl S \<noteq> None\<close> \<open>get_conflict_wl S \<noteq> Some {#}\<close> and
    \<open>correct_watching S\<close> and
    lits: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses
       (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))))\<close>
    using inv
    unfolding extract_shorter_conflict_list_heur_st_pre_def backtrack_wl_D_inv_def S
    backtrack_l_inv_def backtrack_wl_inv_def
    by (auto simp del:)
  show ?Trail
    using M by (simp add: S)
  show ?extract_shorter
    using struct_invs stgy_invs confl_S lits nss nsr
    unfolding extract_shorter_conflict_wl_pre_def no_skip_def no_resolve_def
    by simp
  have
    struct:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close> and
    stgy:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close>
    using struct_invs stgy_invs unfolding twl_struct_invs_def twl_stgy_invs_def by fast+
  have uL_D: \<open>- lit_of (hd M) \<in># the D\<close>
    using cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of
       \<open>state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))\<close>, OF stgy struct nss] D M
    unfolding S
    by auto
  then have \<open>- lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S)\<close>
    unfolding S by simp
  then show ?A
    using confl_S add_invs lits stgy_invs struct_invs trail_S
    unfolding extract_shorter_conflict_list_heur_st_pre_def
    by simp
  have lits_M: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M\<close> and
    lits_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the D)\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail[of S None] struct_invs lits S
      literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[of S None] D
    by auto
  have
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
    conf: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      twl_st_of_wl.simps by simp_all
  have n_d: \<open>no_dup M\<close>
    using lev unfolding S cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by auto
  have dist_D: \<open>distinct_mset (the D)\<close>
    using dist D unfolding S cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by auto
  have max: \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) (the D))
      < backtrack_lvl (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NE, UE, WS, Q)))\<close>
  proof (cases \<open>is_proped (hd M)\<close>)
    case True
    then obtain K C M' where
      M': \<open>M = Propagated K C # M'\<close>
      using M by (cases M; cases \<open>hd M\<close>) auto
    have [simp]: \<open>get_maximum_level (Propagated K F # convert_lits_l N M') =
        get_maximum_level (Propagated K C # M')\<close> for F
      apply (rule ext)
      apply (rule get_maximum_level_cong)
      by (auto simp: get_level_cons_if)
    have \<open>0 < C \<Longrightarrow> K \<in> set (N ! C)\<close>
      using conf unfolding S M' by (auto 5 5 simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
    then show ?thesis
      using nsr uL_D count_decided_ge_get_maximum_level[of M \<open>remove1_mset (- K) (the D)\<close>] D M
      unfolding no_resolve_def M' S
      by (fastforce simp:  cdcl\<^sub>W_restart_mset.resolve.simps elim!: convert_lit.elims)
  next
    case False
    then obtain K M' where
       M': \<open>M = Decided K # M'\<close>
      using M by (cases M; cases \<open>hd M\<close>) auto
    have tr: \<open>M \<Turnstile>as CNot (the D)\<close>
      using conf confl D by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def S)
    have cons: \<open>consistent_interp (lits_of_l M)\<close>
      using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def S
      by (auto dest!: distinct_consistent_interp)
    have tauto: \<open>\<not> tautology (the D)\<close>
      using consistent_CNot_not_tautology[OF cons tr[unfolded true_annots_true_cls]] .
    moreover have \<open>distinct_mset (the D)\<close>
      using dist D unfolding S cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by auto
    ultimately have \<open>atm_of K \<notin> atms_of (remove1_mset (- K) (the D))\<close>
      using uL_D unfolding M'
      by (auto simp: atms_of_def tautology_add_mset atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
          add_mset_eq_add_mset dest!: multi_member_split)
    then show ?thesis
      unfolding M'
      apply (subst get_maximum_level_skip_first)
      using count_decided_ge_get_maximum_level[of M' \<open>remove1_mset (- K) (the D)\<close>]
      by auto
  qed
  then have max_lvl: \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) (the D)) < count_decided M\<close>
    by auto

  assume \<open>RETURN (T, highest) \<le> extract_shorter_conflict_wl_nlit_st S\<close>
  then obtain D' where
     T: \<open>T = (M, N, U, D', NE, UE, WS, Q)\<close> and
     D': \<open>D' \<noteq> None\<close> \<open>the D' \<subseteq># the D\<close> \<open>- lit_of (hd M) \<in># the D'\<close> and
     ent_D': \<open>clause `# twl_clause_of `# mset (tl N) + NE + UE \<Turnstile>pm the D'\<close> and
     highest: \<open>highest_lit M (remove1_mset (- lit_of (hd M)) (the D')) highest\<close>
    unfolding extract_shorter_conflict_wl_nlit_st_def  extract_shorter_conflict_wl_nlit_def Let_def
      S
    by (cases T) (auto simp: nres_order_simps RES_RETURN_RES2)
  have max_D'_D: \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) (the D')) \<le>
          get_maximum_level M (remove1_mset (- lit_of (hd M)) (the D))\<close>
    by (rule get_maximum_level_mono) (use D D' in \<open>auto simp: mset_le_subtract\<close>)
  show \<open>?B\<close>
    unfolding find_decomp_wl_pre_def prod.case lit_of_hd_trail_st_def
    apply (rule exI[of _ S])
    using struct_invs highest M lits_M max_lvl max_D'_D
    unfolding S T
    by (auto simp: highest_lit_def)

  assume \<open>RETURN V \<le> find_decomp_wl_nlit (lit_of_hd_trail_st S) highest T\<close>
  then obtain M1 M2 K where
     V: \<open>V = (M1, N, U, D', NE, UE, WS, Q)\<close> and
     decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
     \<open>get_level M K = (if highest = None then 1 else 1 + snd (the highest))\<close>
    unfolding T find_decomp_wl_nlit_def
    by (cases V) (auto simp: nres_order_simps RES_RETURN_RES2)
  have lits_hd_M: \<open>lit_of (hd M) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using lits_M M by (cases M) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_Cons)
  moreover have undef_hd_M1: \<open>\<not>defined_lit M1 (lit_of (hd M))\<close>
    using decomp n_d apply (auto dest!: get_all_ann_decomposition_exists_prepend simp: hd_append
        split: if_splits)
     apply (metis (no_types, lifting) defined_lit_no_dupD(1) list.sel(1) list.set_cases list.set_sel(1)
        undefined_lit_cons)
    by (metis (no_types, lifting) defined_lit_no_dupD(2) list.sel(1) list.set_cases list.set_sel(1)
        undefined_lit_cons)
 ultimately show ?F if \<open>\<not> Suc 0 < size (the (get_conflict_wl V))\<close>
    using that D' unfolding propagate_unit_bt_wl_D_pre_def S lit_of_hd_trail_st_def V
    by (cases \<open>the D'\<close>) auto

  show ?C
    using D' unfolding V by auto

  assume nempty: \<open>Suc 0 < size (the (get_conflict_wl V))\<close>
  then show ?D
    using highest by (auto simp: highest_lit_def V remove1_mset_empty_iff)
  then obtain L' blev where
    highest_Some: \<open>highest = Some (L', blev)\<close>
    by blast
  have lits_D': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the D')\<close>
    using D' D literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF lits_D, of \<open>the D'\<close>] by auto
  have dist_D': \<open>distinct_mset (the D')\<close>
    using D' distinct_mset_mono[OF _ dist_D] by blast
  then have uL_D': \<open>- lit_of (hd M) \<notin># remove1_mset (- lit_of (hd M)) (the D')\<close>
    by (cases \<open>- lit_of (hd M) \<notin># the D'\<close>) (auto dest!: multi_member_split)
  show ?E
    using D' highest nempty lits_hd_M undef_hd_M1 uL_D' lits_D' dist_D'
    unfolding propagate_bt_wl_D_pre_def V S lit_of_hd_trail_st_def highest_lit_def highest_Some
    by (auto dest: in_diffD)
qed
 *)

lemma empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause':
  \<open>(uncurry2 (empty_conflict_and_extract_clause_heur), uncurry2 empty_conflict_and_extract_clause) \<in>
    [empty_conflict_and_extract_clause_pre]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto intro!: empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause
      simp: empty_conflict_and_extract_clause_pre_def)

theorem empty_conflict_and_extract_clause_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (empty_conflict_and_extract_clause_heur_code),
      uncurry2 empty_conflict_and_extract_clause) \<in>
    [empty_conflict_and_extract_clause_pre]\<^sub>a trail_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d *\<^sub>a
                        out_learned_assn\<^sup>k \<rightarrow> option_lookup_clause_assn *a
     clause_ll_assn *a uint32_nat_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (Id \<times>\<^sub>f Id \<times>\<^sub>f Id) empty_conflict_and_extract_clause_pre
       (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (M, D) \<Rightarrow> \<lambda>outl. outl \<noteq> [] \<and> length outl \<le> uint_max)
                 xa)
       (\<lambda>x. nofail
             (uncurry2 empty_conflict_and_extract_clause
               x))]\<^sub>a
    hrp_comp ((hr_comp trail_pol_assn trail_pol)\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>k)
      (Id \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow>
    hr_comp (option_lookup_clause_assn *a clause_ll_assn *a uint32_nat_assn) Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE[OF empty_conflict_and_extract_clause_heur_code.refine[unfolded PR_CONST_def]
    empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause']
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x h
    using that by (auto simp: comp_PRE_def empty_conflict_and_extract_clause_pre_def)
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

definition (in -) take1 where
  \<open>take1 xs = take 1 xs\<close>

lemma (in -) take1_hnr[sepref_fr_rules]:
  \<open>(return o (\<lambda>(a, _). (a, 1::nat)), RETURN o take1) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a (arl_assn R)\<^sup>d \<rightarrow> arl_assn R\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: arl_assn_def hr_comp_def take1_def list_rel_def
      is_array_list_def
      intro!: list_all2_takeI)
  apply (case_tac xi; case_tac x)
   apply (auto simp: entails_def)
  apply (rule_tac x=l' in exI)
  apply (auto dest!: list_all2_lengthD intro: mod_star_trueI)
  done

sepref_thm extract_shorter_conflict_list_heur_st
  is \<open>PR_CONST extract_shorter_conflict_list_heur_st\<close>
  :: \<open>twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_heur_assn *a uint32_nat_assn *a clause_ll_assn\<close>
  supply [[goals_limit=1]]
empty_conflict_and_extract_clause_pre_def[simp](* TODO: cheating *)
  unfolding extract_shorter_conflict_list_heur_st_def PR_CONST_def twl_st_heur_assn_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    take1_def[symmetric]
  by sepref

concrete_definition (in -) extract_shorter_conflict_list_heur_st_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_list_heur_st.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_list_heur_st_code_def

lemmas extract_shorter_conflict_list_heur_st_hnr[sepref_fr_rules] =
   extract_shorter_conflict_list_heur_st_code.refine[OF isasat_input_bounded_nempty_axioms]

sepref_register find_lit_of_max_level_wl
   extract_shorter_conflict_list_heur_st lit_of_hd_trail_st_heur propagate_bt_wl_D_heur
   propagate_unit_bt_wl_D_int
sepref_register backtrack_wl_D

sepref_thm backtrack_wl_D_code
  is \<open>PR_CONST backtrack_wl_D_nlit_heur\<close>
  :: \<open>twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_heur_assn\<close>
  supply [[goals_limit=1]]
  lit_of_hd_trail_st_def[symmetric, simp]
  size_conflict_wl_def[simp] st_remove_highest_lvl_from_confl_def[simp]
  unfolding backtrack_wl_D_nlit_heur_def PR_CONST_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] lit_of_hd_trail_st_def[symmetric]
    cons_trail_Propagated_def[symmetric]
    size_conflict_wl_def[symmetric]
  by sepref

concrete_definition (in -) backtrack_wl_D_code
   uses isasat_input_bounded_nempty.backtrack_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) backtrack_wl_D_code_def

lemmas backtrack_wl_D_nlit_code_refine[sepref_fr_rules] =
   backtrack_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

end

setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

end