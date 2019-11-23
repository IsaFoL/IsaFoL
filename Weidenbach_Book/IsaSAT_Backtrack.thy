theory IsaSAT_Backtrack
  imports IsaSAT_Setup IsaSAT_VMTF
begin


subsection \<open>Backtrack\<close>

subsubsection \<open>Backtrack with direct extraction of literal if highest level\<close>

paragraph \<open>Empty conflict\<close>

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

definition empty_conflict_and_extract_clause_heur_inv where
  \<open>empty_conflict_and_extract_clause_heur_inv M outl =
    (\<lambda>(E, C, i). mset (take i C) = mset (take i outl) \<and>
            length C = length outl \<and> C ! 0 = outl ! 0 \<and> i \<ge> 1 \<and> i \<le> length outl \<and>
            (1 < length (take i C) \<longrightarrow>
                 highest_lit M (mset (tl (take i C)))
                  (Some (C ! 1, get_level M (C ! 1)))))\<close>

definition empty_conflict_and_extract_clause_heur ::
  "nat multiset \<Rightarrow> (nat, nat) ann_lits
     \<Rightarrow> lookup_clause_rel
       \<Rightarrow> nat literal list \<Rightarrow> (_ \<times> nat literal list \<times> nat) nres"
  where
    \<open>empty_conflict_and_extract_clause_heur \<A> M D outl = do {
     let C = replicate (length outl) (outl!0);
     (D, C, _) \<leftarrow> WHILE\<^sub>T\<^bsup>empty_conflict_and_extract_clause_heur_inv M outl\<^esup>
         (\<lambda>(D, C, i). i < length_uint32_nat outl)
         (\<lambda>(D, C, i). do {
           ASSERT(i < length outl);
           ASSERT(i < length C);
           ASSERT(lookup_conflict_remove1_pre (outl ! i, D));
           let D = lookup_conflict_remove1 (outl ! i) D;
           let C = C[i := outl ! i];
           ASSERT(C!i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> C!1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> 1 < length C);
           let C = (if get_level M (C!i) > get_level M (C!1) then swap C 1 i else C);
           ASSERT(i+1 \<le> uint32_max);
           RETURN (D, C, i+1)
         })
        (D, C, 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow> length C > 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow> C!1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>);
     RETURN ((True, D), C, if length outl = 1 then 0 else get_level M (C!1))
  }\<close>

lemma empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause:
  assumes
    D: \<open>D = mset (tl outl)\<close> and
    outl: \<open>outl \<noteq> []\<close> and
    dist: \<open>distinct outl\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset outl)\<close> and
    DD': \<open>(D', D) \<in> lookup_clause_rel \<A>\<close> and
    consistent: \<open>\<not> tautology (mset outl)\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
  shows
    \<open>empty_conflict_and_extract_clause_heur \<A> M D' outl \<le> \<Down> (option_lookup_clause_rel \<A> \<times>\<^sub>r Id \<times>\<^sub>r Id)
        (empty_conflict_and_extract_clause M D outl)\<close>
proof -
  have size_out: \<open>size (mset outl) \<le> 1 + uint32_max div 2\<close>
    using simple_clss_size_upper_div2[OF bounded lits _ consistent]
      \<open>distinct outl\<close> by auto
  have empty_conflict_and_extract_clause_alt_def:
    \<open>empty_conflict_and_extract_clause M D outl = do {
      (D', outl') \<leftarrow> SPEC (\<lambda>(E, F). E = {#} \<and> mset F = D);
      SPEC
        (\<lambda>(D, C, n).
            D = None \<and>
            mset C = mset outl \<and>
            C ! 0 = outl ! 0 \<and>
            (1 < length C \<longrightarrow>
              highest_lit M (mset (tl C)) (Some (C ! 1, get_level M (C ! 1)))) \<and>
            (1 < length C \<longrightarrow> n = get_level M (C ! 1)) \<and> (length C = 1 \<longrightarrow> n = 0))
    }\<close> for M D outl
    unfolding empty_conflict_and_extract_clause_def RES_RES2_RETURN_RES
    by (auto simp: ex_mset)
  define I where
    \<open>I \<equiv> \<lambda>(E, C, i). mset (take i C) = mset (take i outl) \<and>
       (E, D - mset (take i outl)) \<in> lookup_clause_rel \<A> \<and>
            length C = length outl \<and> C ! 0 = outl ! 0 \<and> i \<ge> 1 \<and> i \<le> length outl \<and>
            (1 < length (take i C) \<longrightarrow>
                 highest_lit M (mset (tl (take i C)))
                  (Some (C ! 1, get_level M (C ! 1))))\<close>
  have I0: \<open>I (D', replicate (length outl) (outl ! 0), 1)\<close>
    using assms by (cases outl) (auto simp: I_def)

  have [simp]: \<open>ba \<ge> 1 \<Longrightarrow> mset (tl outl) - mset (take ba outl) = mset ((drop ba outl))\<close>
    for ba
    apply (subst append_take_drop_id[of \<open>ba - 1\<close>, symmetric])
    using dist
    unfolding mset_append
    by (cases outl; cases ba)
      (auto simp: take_tl drop_Suc[symmetric] remove_1_mset_id_iff_notin dest: in_set_dropD)
  have empty_conflict_and_extract_clause_heur_inv:
    \<open>empty_conflict_and_extract_clause_heur_inv M outl
     (D', replicate (length outl) (outl ! 0), 1)\<close>
    using assms
    unfolding empty_conflict_and_extract_clause_heur_inv_def
    by (cases outl) auto
  have I0: \<open>I (D', replicate (length outl) (outl ! 0), 1)\<close>
    using assms
    unfolding I_def
    by (cases outl) auto
  have
    C1_L: \<open>aa[ba := outl ! ba] ! 1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> (is ?A1inL) and
    ba_le:  \<open>ba + 1 \<le> uint32_max\<close> (is ?ba_le) and
    I_rec: \<open>I (lookup_conflict_remove1 (outl ! ba) a,
          if get_level M (aa[ba := outl ! ba] ! 1)
             < get_level M (aa[ba := outl ! ba] ! ba)
          then swap (aa[ba := outl ! ba]) 1 ba
          else aa[ba := outl ! ba],
          ba + 1)\<close> (is ?I) and
    inv: \<open>empty_conflict_and_extract_clause_heur_inv M outl
        (lookup_conflict_remove1 (outl ! ba) a,
         if get_level M (aa[ba := outl ! ba] ! 1)
            < get_level M (aa[ba := outl ! ba] ! ba)
         then swap (aa[ba := outl ! ba]) 1 ba
         else aa[ba := outl ! ba],
         ba + 1)\<close> (is ?inv)
    if
      \<open>empty_conflict_and_extract_clause_heur_inv M outl s\<close> and
      I: \<open>I s\<close> and
      \<open>case s of (D, C, i) \<Rightarrow> i < length_uint32_nat outl\<close> and
      st:
      \<open>s = (a, b)\<close>
      \<open>b = (aa, ba)\<close> and
      ba_le: \<open>ba < length outl\<close> and
      \<open>ba < length aa\<close> and
      \<open>lookup_conflict_remove1_pre (outl ! ba, a)\<close>
    for s a b aa ba
  proof -
    have
      mset_aa: \<open>mset (take ba aa) = mset (take ba outl)\<close> and
      aD: \<open>(a, D - mset (take ba outl)) \<in> lookup_clause_rel \<A>\<close> and
      l_aa_outl: \<open>length aa = length outl\<close> and
      aa0: \<open>aa ! 0 = outl ! 0\<close> and
      ba_ge1: \<open>1 \<le> ba\<close> and
      ba_lt: \<open>ba \<le> length outl\<close> and
      highest: \<open>1 < length (take ba aa) \<longrightarrow>
      highest_lit M (mset (tl (take ba aa)))
        (Some (aa ! 1, get_level M (aa ! 1)))\<close>
      using I unfolding st I_def prod.case
      by auto
    have set_aa_outl:  \<open>set (take ba aa) = set (take ba outl)\<close>
      using mset_aa by (blast dest: mset_eq_setD)
    show ?ba_le
      using ba_le assms size_out
      by (auto simp: uint32_max_def)
    have ba_ge1_aa_ge:  \<open>ba > 1 \<Longrightarrow> aa ! 1 \<in> set (take ba aa)\<close>
      using ba_ge1 ba_le l_aa_outl
      by (auto simp: in_set_take_conv_nth intro!: bex_lessI[of _ \<open>Suc 0\<close>])
    then have \<open>aa[ba := outl ! ba] ! 1 \<in>  set outl\<close>
      using ba_le l_aa_outl ba_ge1
      unfolding mset_aa in_multiset_in_set[symmetric]
      by (cases \<open>ba > 1\<close>)
        (auto simp: mset_aa dest: in_set_takeD)
    then show ?A1inL
      using literals_are_in_\<L>\<^sub>i\<^sub>n_in_mset_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lits, of \<open>aa[ba := outl ! ba] ! 1\<close>] by auto

    define aa2 where \<open>aa2 \<equiv> tl (tl (take ba aa))\<close>
    have tl_take_nth_con:  \<open>tl (take ba aa) = aa ! Suc 0 # aa2\<close> if \<open>ba > Suc 0\<close>
      using ba_le ba_ge1 that l_aa_outl unfolding aa2_def
      by (cases aa; cases \<open>tl aa\<close>; cases ba; cases \<open>ba - 1\<close>)
        auto
    have no_tauto_nth:  \<open> i < length outl \<Longrightarrow> - outl ! ba = outl ! i \<Longrightarrow> False\<close> for i
      using consistent ba_le nth_mem
      by (force simp: tautology_decomp' uminus_lit_swap)
    have outl_ba__L: \<open>outl ! ba \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
      using ba_le literals_are_in_\<L>\<^sub>i\<^sub>n_in_mset_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lits, of \<open>outl ! ba\<close>] by auto
    have \<open>(lookup_conflict_remove1 (outl ! ba) a,
        remove1_mset (outl ! ba)  (D -(mset (take ba outl)))) \<in> lookup_clause_rel \<A>\<close>
      by (rule lookup_conflict_remove1[THEN fref_to_Down_unRET_uncurry])
        (use ba_ge1 ba_le aD   outl_ba__L in
          \<open>auto simp: D in_set_drop_conv_nth image_image dest: no_tauto_nth
        intro!: bex_geI[of _ ba]\<close>)
    then have \<open>(lookup_conflict_remove1 (outl ! ba) a,
      D - mset (take (Suc ba) outl))
      \<in> lookup_clause_rel \<A>\<close>
      using aD ba_le ba_ge1 ba_ge1_aa_ge aa0
      by (auto simp: take_Suc_conv_app_nth)
    moreover have \<open>1 < length
          (take (ba + 1)
            (if get_level M (aa[ba := outl ! ba] ! 1)
                < get_level M (aa[ba := outl ! ba] ! ba)
             then swap (aa[ba := outl ! ba]) 1 ba
             else aa[ba := outl ! ba])) \<longrightarrow>
      highest_lit M
      (mset
        (tl (take (ba + 1)
              (if get_level M (aa[ba := outl ! ba] ! 1)
                  < get_level M (aa[ba := outl ! ba] ! ba)
               then swap (aa[ba := outl ! ba]) 1 ba
               else aa[ba := outl ! ba]))))
      (Some
        ((if get_level M (aa[ba := outl ! ba] ! 1)
             < get_level M (aa[ba := outl ! ba] ! ba)
          then swap (aa[ba := outl ! ba]) 1 ba
          else aa[ba := outl ! ba]) !
         1,
         get_level M
          ((if get_level M (aa[ba := outl ! ba] ! 1)
               < get_level M (aa[ba := outl ! ba] ! ba)
            then swap (aa[ba := outl ! ba]) 1 ba
            else aa[ba := outl ! ba]) !
           1)))\<close>
      using highest ba_le ba_ge1
      by (cases \<open>ba = Suc 0\<close>)
        (auto simp: highest_lit_def take_Suc_conv_app_nth l_aa_outl
          get_maximum_level_add_mset swap_nth_relevant max_def take_update_swap
          swap_only_first_relevant tl_update_swap mset_update nth_tl
          get_maximum_level_remove_non_max_lvl tl_take_nth_con
          aa2_def[symmetric])
    moreover have \<open>mset
      (take (ba + 1)
        (if get_level M (aa[ba := outl ! ba] ! 1)
            < get_level M (aa[ba := outl ! ba] ! ba)
          then swap (aa[ba := outl ! ba]) 1 ba
          else aa[ba := outl ! ba])) =
      mset (take (ba + 1) outl)\<close>
      using ba_le ba_ge1 ba_ge1_aa_ge aa0
      unfolding mset_aa
      by (cases \<open>ba = 1\<close>)
        (auto simp: take_Suc_conv_app_nth l_aa_outl
          take_swap_relevant swap_only_first_relevant mset_aa set_aa_outl
          mset_update add_mset_remove_trivial_If)
    ultimately show ?I
      using ba_ge1 ba_le
      unfolding I_def prod.simps
      by (auto simp: l_aa_outl aa0)

    then show ?inv
      unfolding empty_conflict_and_extract_clause_heur_inv_def I_def
      by (auto simp: l_aa_outl aa0)
  qed
  have mset_tl_out:  \<open>mset (tl outl) - mset outl = {#}\<close>
    by (cases outl) auto
  have H1: \<open>WHILE\<^sub>T\<^bsup>empty_conflict_and_extract_clause_heur_inv M outl\<^esup>
     (\<lambda>(D, C, i). i < length_uint32_nat outl)
     (\<lambda>(D, C, i). do {
           _ \<leftarrow> ASSERT (i < length outl);
           _ \<leftarrow> ASSERT (i < length C);
           _ \<leftarrow> ASSERT (lookup_conflict_remove1_pre (outl ! i, D));
           _ \<leftarrow> ASSERT
                (C[i := outl ! i] ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and>
                 C[i := outl ! i] ! 1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and>
                1 < length (C[i := outl ! i]));
           _ \<leftarrow> ASSERT (i + 1 \<le> uint32_max);
           RETURN
            (lookup_conflict_remove1 (outl ! i) D,
             if get_level M (C[i := outl ! i] ! 1)
                < get_level M (C[i := outl ! i] ! i)
             then swap (C[i := outl ! i]) 1 i
             else C[i := outl ! i],
             i + 1)
         })
     (D', replicate (length outl) (outl ! 0), 1)
    \<le> \<Down> {((E, C, n), (E', F')). (E, E') \<in> lookup_clause_rel \<A> \<and> mset C = mset outl \<and>
             C ! 0 = outl ! 0 \<and>
            (1 < length C \<longrightarrow>
              highest_lit M (mset (tl C)) (Some (C ! 1, get_level M (C ! 1)))) \<and>
            n = length outl \<and>
            I (E, C, n)}
          (SPEC (\<lambda>(E, F). E = {#} \<and> mset F = D))\<close>
    unfolding conc_fun_RES
    apply (refine_vcg WHILEIT_rule_stronger_inv_RES[where R = \<open>measure (\<lambda>(_, _, i). length outl - i)\<close>  and
          I' = \<open>I\<close>])
    subgoal by auto
    subgoal by (rule empty_conflict_and_extract_clause_heur_inv)
    subgoal by (rule I0)
    subgoal using assms by (cases outl; auto)
    subgoal
      by (auto simp: I_def)
    subgoal for s a b aa ba
      using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l lits
      unfolding lookup_conflict_remove1_pre_def prod.simps
      by (auto simp: I_def empty_conflict_and_extract_clause_heur_inv_def
          lookup_clause_rel_def D atms_of_def)
    subgoal for s a b aa ba
      using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l lits
      unfolding lookup_conflict_remove1_pre_def prod.simps
      by (auto simp: I_def empty_conflict_and_extract_clause_heur_inv_def
          lookup_clause_rel_def D atms_of_def)
    subgoal for s a b aa ba
      by (rule C1_L)
    subgoal for s a b aa ba
      using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l lits
      unfolding lookup_conflict_remove1_pre_def prod.simps
      by (auto simp: I_def empty_conflict_and_extract_clause_heur_inv_def
          lookup_clause_rel_def D atms_of_def)
    subgoal for s a b aa ba
      by (rule ba_le)
    subgoal
      by (rule inv)
    subgoal
      by (rule I_rec)
    subgoal
      by auto
    subgoal for s
      unfolding prod.simps
      apply (cases s)
      apply clarsimp
      apply (intro conjI)
      subgoal
        by (rule ex_mset)
      subgoal
        using assms
        by (auto simp: empty_conflict_and_extract_clause_heur_inv_def I_def mset_tl_out)
      subgoal
        using assms
        by (auto simp: empty_conflict_and_extract_clause_heur_inv_def I_def mset_tl_out)
      subgoal
        using assms
        by (auto simp: empty_conflict_and_extract_clause_heur_inv_def I_def mset_tl_out)
      subgoal
        using assms
        by (auto simp: empty_conflict_and_extract_clause_heur_inv_def I_def mset_tl_out)
      subgoal
        using assms
        by (auto simp: empty_conflict_and_extract_clause_heur_inv_def I_def mset_tl_out)
      done
    done
  have x1b_lall:  \<open>x1b ! 1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
    if
      inv: \<open>(x, x')
      \<in> {((E, C, n), E', F').
          (E, E') \<in> lookup_clause_rel \<A> \<and>
          mset C = mset outl \<and>
          C ! 0 = outl ! 0 \<and>
          (1 < length C \<longrightarrow>
          highest_lit M (mset (tl C)) (Some (C ! 1, get_level M (C ! 1)))) \<and>
            n = length outl  \<and>
          I (E, C, n)}\<close> and
      \<open>x' \<in> {(E, F). E = {#} \<and> mset F = D}\<close> and
      st:
      \<open>x' = (x1, x2)\<close>
      \<open>x2a = (x1b, x2b)\<close>
      \<open>x = (x1a, x2a)\<close> and
      \<open>length outl \<noteq> 1 \<longrightarrow> 1 < length x1b\<close> and
      \<open>length outl \<noteq> 1\<close>
    for x x' x1 x2 x1a x2a x1b x2b
  proof -
    have
      \<open>(x1a, x1) \<in> lookup_clause_rel \<A>\<close> and
      \<open>mset x1b = mset outl\<close> and
      \<open>x1b ! 0 = outl ! 0\<close> and
      \<open>Suc 0 < length x1b \<longrightarrow>
      highest_lit M (mset (tl x1b))
        (Some (x1b ! Suc 0, get_level M (x1b ! Suc 0)))\<close> and
      mset_aa: \<open>mset (take x2b x1b) = mset (take x2b outl)\<close> and
      \<open>(x1a, D - mset (take x2b outl)) \<in> lookup_clause_rel \<A>\<close> and
      l_aa_outl: \<open>length x1b = length outl\<close> and
      \<open>x1b ! 0 = outl ! 0\<close> and
      ba_ge1: \<open>Suc 0 \<le> x2b\<close> and
      ba_le: \<open>x2b \<le> length outl\<close> and
      \<open>Suc 0 < length x1b \<and> Suc 0 < x2b \<longrightarrow>
     highest_lit M (mset (tl (take x2b x1b)))
      (Some (x1b ! Suc 0, get_level M (x1b ! Suc 0)))\<close>
      using inv unfolding st I_def prod.case st
      by auto

    have set_aa_outl: \<open>set (take x2b x1b) = set (take x2b outl)\<close>
      using mset_aa by (blast dest: mset_eq_setD)
    have ba_ge1_aa_ge:  \<open>x2b > 1 \<Longrightarrow> x1b ! 1 \<in> set (take x2b x1b)\<close>
      using ba_ge1 ba_le l_aa_outl
      by (auto simp: in_set_take_conv_nth intro!: bex_lessI[of _ \<open>Suc 0\<close>])
    then have \<open>x1b ! 1 \<in> set outl\<close>
      using ba_le l_aa_outl ba_ge1 that
      unfolding mset_aa in_multiset_in_set[symmetric]
      by (cases \<open>x2b > 1\<close>)
        (auto simp: mset_aa dest: in_set_takeD)
    then show ?thesis
      using literals_are_in_\<L>\<^sub>i\<^sub>n_in_mset_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lits, of \<open>x1b ! 1\<close>] by auto
  qed

  show ?thesis
    unfolding empty_conflict_and_extract_clause_heur_def empty_conflict_and_extract_clause_alt_def
      Let_def I_def[symmetric]
    apply (subst empty_conflict_and_extract_clause_alt_def)
    unfolding conc_fun_RES
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(_, _, i). length outl - i)\<close> and
          I' = \<open>I\<close>] H1)
    subgoal using assms by (auto simp: I_def)
    subgoal by (rule x1b_lall)
    subgoal using assms
      by (auto intro!: RETURN_RES_refine simp: option_lookup_clause_rel_def I_def)
    done
qed

definition isa_empty_conflict_and_extract_clause_heur ::
  "trail_pol \<Rightarrow> lookup_clause_rel \<Rightarrow> nat literal list \<Rightarrow> (_ \<times> nat literal list \<times> nat) nres"
  where
    \<open>isa_empty_conflict_and_extract_clause_heur M D outl = do {
     let C = replicate (length outl) (outl!0);
     (D, C, _) \<leftarrow> WHILE\<^sub>T
         (\<lambda>(D, C, i). i < length_uint32_nat outl)
         (\<lambda>(D, C, i). do {
           ASSERT(i < length outl);
           ASSERT(i < length C);
           ASSERT(lookup_conflict_remove1_pre (outl ! i, D));
           let D = lookup_conflict_remove1 (outl ! i) D;
           let C = C[i := outl ! i];
	   ASSERT(get_level_pol_pre (M, C!i));
	   ASSERT(get_level_pol_pre (M, C!1));
	   ASSERT(1 < length C);
           let C = (if get_level_pol M (C!i) > get_level_pol M (C!1) then swap C 1 i else C);
           ASSERT(i+1 \<le> uint32_max);
           RETURN (D, C, i+1)
         })
        (D, C, 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow> length C > 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow>  get_level_pol_pre (M, C!1));
     RETURN ((True, D), C, if length outl = 1 then 0 else get_level_pol M (C!1))
  }\<close>

lemma isa_empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause_heur:
  \<open>(uncurry2 isa_empty_conflict_and_extract_clause_heur, uncurry2 (empty_conflict_and_extract_clause_heur \<A>)) \<in>
     trail_pol \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel \<close>
proof -
  have [refine0]: \<open>((x2b, replicate (length x2c) (x2c ! 0), 1), x2,
	 replicate (length x2a) (x2a ! 0), 1)
	\<in> Id \<times>\<^sub>f Id \<times>\<^sub>f Id\<close>
    if
      \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f Id \<times>\<^sub>f Id\<close> and    \<open>x1 = (x1a, x2)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1b = (x1c, x2b)\<close> and
      \<open>x = (x1b, x2c)\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c
    using that by auto

  show ?thesis
    supply [[goals_limit=1]]
    unfolding isa_empty_conflict_and_extract_clause_heur_def empty_conflict_and_extract_clause_heur_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg)
                    apply (assumption+)[5]
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal
      by (rule get_level_pol_pre) auto
    subgoal
      by (rule get_level_pol_pre) auto
    subgoal by auto
    subgoal by auto
    subgoal
      by (auto simp: get_level_get_level_pol[of _ _ \<A>])
    subgoal by auto
    subgoal
      by (rule get_level_pol_pre) auto
    subgoal by (auto simp: get_level_get_level_pol[of _ _ \<A>])
    done
qed


definition extract_shorter_conflict_wl_nlit where
  \<open>extract_shorter_conflict_wl_nlit K M NU D NE UE =
    SPEC(\<lambda>D'. D' \<noteq> None \<and> the D' \<subseteq># the D \<and> K \<in># the D' \<and>
      mset `# ran_mf NU + NE + UE \<Turnstile>pm the D')\<close>

definition extract_shorter_conflict_wl_nlit_st
  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>
  where
    \<open>extract_shorter_conflict_wl_nlit_st =
     (\<lambda>(M, N, D, NE, UE, WS, Q). do {
        let K = -lit_of (hd M);
        D \<leftarrow> extract_shorter_conflict_wl_nlit K M N D NE UE;
        RETURN (M, N, D, NE, UE, WS, Q)})\<close>

definition empty_lookup_conflict_and_highest
  :: \<open>'v twl_st_wl \<Rightarrow> ('v twl_st_wl \<times> nat) nres\<close>
  where
    \<open>empty_lookup_conflict_and_highest  =
     (\<lambda>(M, N, D, NE, UE, WS, Q). do {
        let K = -lit_of (hd M);
        let n = get_maximum_level M (remove1_mset K (the D));
        RETURN ((M, N, D, NE, UE, WS, Q), n)})\<close>

definition backtrack_wl_D_heur_inv where
  \<open>backtrack_wl_D_heur_inv S \<longleftrightarrow> (\<exists>S'. (S, S') \<in> twl_st_heur_conflict_ana \<and> backtrack_wl_inv S')\<close>

definition extract_shorter_conflict_heur where
  \<open>extract_shorter_conflict_heur = (\<lambda>M NU NUE C outl. do {
     let K = lit_of (hd M);
     let C = Some (remove1_mset (-K) (the C));
     C \<leftarrow> iterate_over_conflict (-K) M NU NUE (the C);
     RETURN (Some (add_mset (-K) C))
  })\<close>

definition (in -) empty_cach where
  \<open>empty_cach cach = (\<lambda>_. SEEN_UNKNOWN)\<close>

definition empty_conflict_and_extract_clause_pre
  :: \<open>(((nat,nat) ann_lits \<times> nat clause) \<times> nat clause_l) \<Rightarrow> bool\<close> where
  \<open>empty_conflict_and_extract_clause_pre =
    (\<lambda>((M, D), outl). D = mset (tl outl)  \<and> outl \<noteq> [] \<and> distinct outl \<and>
    \<not>tautology (mset outl) \<and> length outl \<le> uint32_max)\<close>

definition (in -) empty_cach_ref where
  \<open>empty_cach_ref = (\<lambda>(cach, support). (replicate (length cach) SEEN_UNKNOWN, []))\<close>


definition empty_cach_ref_set_inv where
  \<open>empty_cach_ref_set_inv cach0 support =
    (\<lambda>(i, cach). length cach = length cach0 \<and>
         (\<forall>L \<in> set (drop i support). L < length cach) \<and>
         (\<forall>L \<in> set (take i support).  cach ! L = SEEN_UNKNOWN) \<and>
         (\<forall>L < length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set (drop i support)))\<close>

definition empty_cach_ref_set where
  \<open>empty_cach_ref_set = (\<lambda>(cach0, support). do {
    let n = length support;
    ASSERT(n \<le> Suc (uint32_max div 2));
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

lemma empty_cach_ref_set_empty_cach_ref:
  \<open>(empty_cach_ref_set, RETURN o empty_cach_ref) \<in>
    [\<lambda>(cach, supp). (\<forall>L \<in> set supp. L < length cach) \<and> length supp \<le> Suc (uint32_max div 2) \<and>
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
    by (intro frefI nres_relI ASSERT_leI) (clarify intro!: H ASSERT_leI)

qed


lemma empty_cach_ref_empty_cach:
  \<open>isasat_input_bounded \<A> \<Longrightarrow> (RETURN o empty_cach_ref, RETURN o empty_cach) \<in> cach_refinement \<A> \<rightarrow>\<^sub>f \<langle>cach_refinement \<A>\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: empty_cach_def empty_cach_ref_def cach_refinement_alt_def cach_refinement_list_def
      map_fun_rel_def intro: bounded_included_le)


definition empty_cach_ref_pre where
  \<open>empty_cach_ref_pre = (\<lambda>(cach :: minimize_status list, supp :: nat list).
         (\<forall>L\<in>set supp. L < length cach) \<and>
         length supp \<le> Suc (uint32_max div 2) \<and>
         (\<forall>L<length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set supp))\<close>


paragraph \<open>Minimisation of the conflict\<close>

definition extract_shorter_conflict_list_heur_st
  :: \<open>twl_st_wl_heur \<Rightarrow> (twl_st_wl_heur \<times> _ \<times> _) nres\<close>
  where
    \<open>extract_shorter_conflict_list_heur_st = (\<lambda>(M, N, (_, D), Q', W', vm, \<phi>, clvls, cach, lbd, outl,
       stats, ccont, vdom). do {
     ASSERT(fst M \<noteq> []);
     let K = lit_of_last_trail_pol M;
     ASSERT(0 < length outl);
     ASSERT(lookup_conflict_remove1_pre (-K, D));
     let D = lookup_conflict_remove1 (-K) D;
     let outl = outl[0 := -K];
     vm \<leftarrow> isa_vmtf_mark_to_rescore_also_reasons M N outl vm;
     (D, cach, outl) \<leftarrow> isa_minimize_and_extract_highest_lookup_conflict M N D cach lbd outl;
     ASSERT(empty_cach_ref_pre cach);
     let cach = empty_cach_ref cach;
     ASSERT(outl \<noteq> [] \<and> length outl \<le> uint32_max);
     (D, C, n) \<leftarrow> isa_empty_conflict_and_extract_clause_heur M D outl;
     RETURN ((M, N, D, Q', W', vm, \<phi>, clvls, cach, lbd, take 1 outl, stats, ccont, vdom), n, C)
  })\<close>

lemma the_option_lookup_clause_assn:
  \<open>(RETURN o snd, RETURN o the) \<in> [\<lambda>D. D \<noteq> None]\<^sub>f option_lookup_clause_rel \<A> \<rightarrow> \<langle>lookup_clause_rel \<A>\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: option_lookup_clause_rel_def)

definition update_heuristics where
  \<open>update_heuristics = (\<lambda>glue (fema, sema, res_info, wasted).
     (ema_update glue fema, ema_update glue sema,
          incr_conflict_count_since_last_restart res_info, wasted))\<close>

lemma heuristic_rel_update_heuristics[intro!]:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (update_heuristics glue heur)\<close>
  by (auto simp: heuristic_rel_def)

definition propagate_bt_wl_D_heur
  :: \<open>nat literal \<Rightarrow> nat clause_l \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>propagate_bt_wl_D_heur = (\<lambda>L C (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur, vdom, avdom, lcount, opts). do {
      ASSERT(length vdom \<le> length N0);
      ASSERT(length avdom \<le> length N0);
      ASSERT(nat_of_lit (C!1) < length W0 \<and> nat_of_lit (-L) < length W0);
      ASSERT(length C > 1);
      let L' = C!1;
      ASSERT(length C \<le> uint32_max div 2 + 1);
      (vm, \<phi>) \<leftarrow> isa_vmtf_rescore C M vm0 \<phi>0;
      glue \<leftarrow> get_LBD lbd;
      let b = False;
      let b' = (length C = 2);
      ASSERT(isasat_fast (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
        vdom, avdom, lcount, opts) \<longrightarrow> append_and_length_fast_code_pre ((b, C), N0));
      ASSERT(isasat_fast (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
        vdom, avdom, lcount, opts) \<longrightarrow> lcount < sint64_max);
      (N, i) \<leftarrow> fm_add_new b C N0;
      ASSERT(update_lbd_pre ((i, glue), N));
      let N = update_lbd i glue N;
      ASSERT(isasat_fast (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
         vdom, avdom, lcount, opts) \<longrightarrow> length_ll W0 (nat_of_lit (-L)) < sint64_max);
      let W = W0[nat_of_lit (- L) := W0 ! nat_of_lit (- L) @ [(i, L', b')]];
      ASSERT(isasat_fast (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
         vdom, avdom, lcount, opts) \<longrightarrow> length_ll W (nat_of_lit L') < sint64_max);
      let W = W[nat_of_lit L' := W!nat_of_lit L' @ [(i, -L, b')]];
      lbd \<leftarrow> lbd_empty lbd;
      ASSERT(isa_length_trail_pre M);
      let j = isa_length_trail M;
      ASSERT(i \<noteq> DECISION_REASON);
      ASSERT(cons_trail_Propagated_tr_pre ((-L, i), M));
      M \<leftarrow> cons_trail_Propagated_tr (- L) i M;
      vm \<leftarrow> isa_vmtf_flush_int M vm;
      ASSERT(atm_of L < length \<phi>);
      RETURN (M, N, D, j, W, vm, save_phase (-L) \<phi>, 0,
         cach, lbd, outl, add_lbd (of_nat glue) stats, update_heuristics glue heur, vdom @ [ i],
          avdom @ [ i],
          lcount + 1, opts)
    })\<close>

definition (in -) lit_of_hd_trail_st_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal nres\<close> where
  \<open>lit_of_hd_trail_st_heur S = do {ASSERT (fst (get_trail_wl_heur S) \<noteq> []); RETURN (lit_of_last_trail_pol (get_trail_wl_heur S))}\<close>

definition remove_last
  :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> nat clause option nres\<close>
  where
    \<open>remove_last _ _  = SPEC((=) None)\<close>

definition propagate_unit_bt_wl_D_int
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
  where
    \<open>propagate_unit_bt_wl_D_int = (\<lambda>L (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
        heur, vdom). do {
      vm \<leftarrow> isa_vmtf_flush_int M vm;
      glue \<leftarrow> get_LBD lbd;
      lbd \<leftarrow> lbd_empty lbd;
      ASSERT(isa_length_trail_pre M);
      let j = isa_length_trail M;
      ASSERT(0 \<noteq> DECISION_REASON);
      ASSERT(cons_trail_Propagated_tr_pre ((- L, 0::nat), M));
      M \<leftarrow> cons_trail_Propagated_tr (- L) 0 M;
      let stats = incr_uset stats;
      RETURN (M, N, D, j, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
        (update_heuristics glue heur), vdom)})\<close>


paragraph \<open>Full function\<close>

definition backtrack_wl_D_nlit_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
  where
    \<open>backtrack_wl_D_nlit_heur S\<^sub>0 =
    do {
      ASSERT(backtrack_wl_D_heur_inv S\<^sub>0);
      ASSERT(fst (get_trail_wl_heur S\<^sub>0) \<noteq> []);
      L \<leftarrow> lit_of_hd_trail_st_heur S\<^sub>0;
      (S, n, C) \<leftarrow> extract_shorter_conflict_list_heur_st S\<^sub>0;
      ASSERT(get_clauses_wl_heur S = get_clauses_wl_heur S\<^sub>0);
      S \<leftarrow> find_decomp_wl_st_int n S;

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

definition del_conflict_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>del_conflict_wl = (\<lambda>(M, N, D, NE, UE, Q, W). (M, N, None, NE, UE, Q, W))\<close>

lemma [simp]:
  \<open>get_clauses_wl (del_conflict_wl S) = get_clauses_wl S\<close>
  by (cases S) (auto simp: del_conflict_wl_def)

lemma lcount_add_clause[simp]: \<open>i \<notin># dom_m N \<Longrightarrow>
    size (learned_clss_l (fmupd i (C, False) N)) = Suc (size (learned_clss_l N))\<close>
  by (simp add: learned_clss_l_mapsto_upd_notin)

lemma length_watched_le:
  assumes
    prop_inv: \<open>correct_watching x1\<close> and
    xb_x'a: \<open>(x1a, x1) \<in> twl_st_heur_conflict_ana\<close> and
    x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x1)\<close>
  shows \<open>length (watched_by x1 x2) \<le> length (get_clauses_wl_heur x1a) - 2\<close>
proof -
  have \<open>correct_watching x1\<close>
    using prop_inv unfolding unit_propagation_outer_loop_wl_inv_def
      unit_propagation_outer_loop_wl_inv_def
    by auto
  then have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using x2 unfolding all_atms_def[symmetric] all_lits_alt_def[symmetric]
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps
        \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits
      simp flip: all_lits_alt_def2 all_lits_def all_atms_def)
  then have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using xb_x'a
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps)
  have dist_vdom: \<open>distinct (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_conflict_ana_def twl_st_heur'_def)
  have x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x1)\<close>
    using x2 xb_x'a unfolding all_atms_def
    by auto

  have
      valid: \<open>valid_arena (get_clauses_wl_heur x1a) (get_clauses_wl x1) (set (get_vdom x1a))\<close>
    using xb_x'a unfolding all_atms_def all_lits_def
    by (cases x1)
     (auto simp: twl_st_heur'_def twl_st_heur_conflict_ana_def)

  have \<open>vdom_m (all_atms_st x1) (get_watched_wl x1) (get_clauses_wl x1) \<subseteq> set (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_conflict_ana_def twl_st_heur'_def all_atms_def[symmetric])
  then have subset: \<open>set (map fst (watched_by x1 x2)) \<subseteq> set (get_vdom x1a)\<close>
    using x2 unfolding vdom_m_def
    by (cases x1)
      (force simp: twl_st_heur'_def twl_st_heur_def simp flip: all_atms_def
        dest!: multi_member_split)
  have watched_incl: \<open>mset (map fst (watched_by x1 x2)) \<subseteq># mset (get_vdom x1a)\<close>
    by (rule distinct_subseteq_iff[THEN iffD1])
      (use dist[unfolded distinct_watched_alt_def] dist_vdom subset in
         \<open>simp_all flip: distinct_mset_mset_distinct\<close>)
  have vdom_incl: \<open>set (get_vdom x1a) \<subseteq> {4..< length (get_clauses_wl_heur x1a)}\<close>
    using valid_arena_in_vdom_le_arena[OF valid] arena_dom_status_iff[OF valid] by auto

  have \<open>length (get_vdom x1a) \<le> length (get_clauses_wl_heur x1a) - 4\<close>
    by (subst distinct_card[OF dist_vdom, symmetric])
      (use card_mono[OF _ vdom_incl] in auto)
  then show ?thesis
    using size_mset_mono[OF watched_incl] xb_x'a
    by (auto intro!: order_trans[of \<open>length (watched_by x1 x2)\<close> \<open>length (get_vdom x1a)\<close>])
qed

definition single_of_mset where
  \<open>single_of_mset D = SPEC(\<lambda>L. D = mset [L])\<close>

(* TODO Move *)
lemma length_list_ge2: \<open>length S \<ge> 2 \<longleftrightarrow> (\<exists>a b S'. S = [a, b] @ S')\<close>
  apply (cases S)
   apply (simp; fail)
  apply (rename_tac a S')
  apply (case_tac S')
  by simp_all


lemma backtrack_wl_D_nlit_backtrack_wl_D:
  \<open>(backtrack_wl_D_nlit_heur, backtrack_wl) \<in>
  {(S, T). (S, T) \<in> twl_st_heur_conflict_ana \<and> length (get_clauses_wl_heur S) = r} \<rightarrow>\<^sub>f
  \<langle>{(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) \<le> 6 + r + uint32_max div 2}\<rangle>nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>?S\<rangle>nres_rel\<close>)
proof -
  have backtrack_wl_D_nlit_heur_alt_def: \<open>backtrack_wl_D_nlit_heur S\<^sub>0 =
    do {
      ASSERT(backtrack_wl_D_heur_inv S\<^sub>0);
      ASSERT(fst (get_trail_wl_heur S\<^sub>0) \<noteq> []);
      L \<leftarrow> lit_of_hd_trail_st_heur S\<^sub>0;
      (S, n, C) \<leftarrow> extract_shorter_conflict_list_heur_st S\<^sub>0;
      ASSERT(get_clauses_wl_heur S = get_clauses_wl_heur S\<^sub>0);
      S \<leftarrow> find_decomp_wl_st_int n S;
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
      \<open>backtrack_wl_inv S\<close> and
      \<open>(S', S) \<in> ?R\<close>
    for S S'
    using that unfolding backtrack_wl_D_heur_inv_def
    by (cases S; cases S') (blast intro: exI[of _ S'])
  have shorter:
    \<open>extract_shorter_conflict_list_heur_st S'
       \<le> \<Down> {((T', n, C), T). (T', del_conflict_wl T) \<in> twl_st_heur_bt  \<and>
              n = get_maximum_level (get_trail_wl T)
                  (remove1_mset (-lit_of(hd (get_trail_wl T))) (the (get_conflict_wl T))) \<and>
              mset C = the (get_conflict_wl T) \<and>
              get_conflict_wl T \<noteq> None\<and>
              equality_except_conflict_wl T S \<and>
              get_clauses_wl_heur T' = get_clauses_wl_heur S' \<and>
              (1 < length C \<longrightarrow>
                highest_lit (get_trail_wl T) (mset (tl C))
                (Some (C ! 1, get_level (get_trail_wl T) (C ! 1)))) \<and>
              C \<noteq> [] \<and> hd C = -lit_of(hd (get_trail_wl T)) \<and>
              mset C \<subseteq># the (get_conflict_wl S) \<and>
              distinct_mset (the (get_conflict_wl S)) \<and>
              literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S) (the (get_conflict_wl S)) \<and>
              literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st T) (get_trail_wl T) \<and>
              get_conflict_wl S \<noteq> None \<and>
              - lit_of (hd (get_trail_wl S)) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S) \<and>
              literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st T) T \<and>
              n < count_decided (get_trail_wl T) \<and>
	            get_trail_wl T \<noteq> [] \<and>
              \<not> tautology (mset C) \<and>
              correct_watching S \<and> length (get_clauses_wl_heur T') = length (get_clauses_wl_heur S')}
           (extract_shorter_conflict_wl S)\<close>
    (is \<open>_ \<le> \<Down> ?shorter _\<close>)
    if
      inv: \<open>backtrack_wl_inv S\<close> and
      S'_S: \<open>(S', S) \<in> ?R\<close>
    for S S'
  proof -
    obtain M N D NE UE NS US Q W where
      S: \<open>S = (M, N, D, NE, UE, NS, US, Q, W)\<close>
      by (cases S)
    obtain M' W' vm \<phi> clvls cach lbd outl stats heur avdom vdom lcount D' arena b Q' opts where
      S': \<open>S' = (M', arena, (b, D'), Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats, heur, vdom,
        avdom, lcount, opts)\<close>
      using S'_S by (cases S') (auto simp: twl_st_heur_conflict_ana_def S)
    have
      M'_M: \<open>(M', M) \<in> trail_pol (all_atms_st S)\<close>  and
      \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms_st S))\<close> and
      vm: \<open>vm \<in> isa_vmtf (all_atms_st S) M\<close> and
      \<open>phase_saving (all_atms_st S) \<phi>\<close> and
      n_d: \<open>no_dup M\<close> and
      \<open>clvls \<in> counts_maximum_level M D\<close> and
      cach_empty: \<open>cach_refinement_empty (all_atms_st S) cach\<close> and
      outl: \<open>out_learned M D outl\<close> and
      lcount: \<open>lcount = size (learned_clss_l N)\<close> and
      \<open>vdom_m (all_atms_st S) W N \<subseteq> set vdom\<close> and
      D': \<open>((b, D'), D) \<in> option_lookup_clause_rel (all_atms_st S)\<close> and
      arena: \<open>valid_arena arena N (set vdom)\<close> and
      avdom: \<open>mset avdom \<subseteq># mset vdom\<close> and
      bounded: \<open>isasat_input_bounded (all_atms_st S)\<close>
      using S'_S unfolding S S' twl_st_heur_conflict_ana_def
      by (auto simp: S all_atms_def[symmetric])
    obtain T U where
      \<L>\<^sub>i\<^sub>n :\<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close> and
      S_T: \<open>(S, T) \<in> state_wl_l None\<close> and
      corr: \<open>correct_watching S\<close> and
      T_U: \<open>(T, U) \<in> twl_st_l None\<close> and
      trail_nempty: \<open>get_trail_l T \<noteq> []\<close> and
      not_none: \<open>get_conflict_l T \<noteq> None\<close> and
      struct_invs: \<open>twl_struct_invs U\<close> and
      stgy_invs: \<open>twl_stgy_invs U\<close> and
      list_invs: \<open>twl_list_invs T\<close> and
      not_empty: \<open>get_conflict_l T \<noteq> Some {#}\<close> and
      uL_D: \<open>- lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S)\<close> and
      nss: \<open>no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of U)\<close> and
      nsr: \<open>no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of U)\<close>
      using inv unfolding backtrack_wl_inv_def backtrack_wl_inv_def backtrack_l_inv_def backtrack_inv_def
      apply -
      apply normalize_goal+ by simp
    have D_none: \<open>D \<noteq> None\<close>
      using S_T not_none by (auto simp: S)
    have b: \<open>\<not>b\<close>
      using D' not_none S_T by (auto simp: option_lookup_clause_rel_def S state_wl_l_def)
    have all_struct:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of U)\<close>
      using struct_invs
      by (auto simp: twl_struct_invs_def)
    have
      \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close> and
      lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of U)\<close> and
      \<open>\<forall>s\<in>#learned_clss (state\<^sub>W_of U). \<not> tautology s\<close> and
      dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of U)\<close> and
      confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of U)\<close> and
      \<open>all_decomposition_implies_m  (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of U))
        (get_all_ann_decomposition (trail (state\<^sub>W_of U)))\<close> and
      learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of U)\<close>
      using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    have n_d: \<open>no_dup M\<close>
      using lev_inv S_T T_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (auto simp: twl_st S)
    have M_\<L>\<^sub>i\<^sub>n: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st S) (get_trail_wl S)\<close>
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
    have \<L>\<^sub>i\<^sub>n_S: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S) (the (get_conflict_wl S))\<close>
      apply (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_conflict[OF S_T _ T_U])
      using \<L>\<^sub>i\<^sub>n not_none struct_invs not_none S_T T_U by (auto simp: S)
    then have \<L>\<^sub>i\<^sub>n_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S) ?D\<close>
      unfolding S by (auto intro: literals_are_in_\<L>\<^sub>i\<^sub>n_mono)
    have \<L>\<^sub>i\<^sub>n_NU: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (all_atms_st S) (mset `# ran_mf (get_clauses_wl S))\<close>
      (*TODO proof*)
      by (auto simp: all_atms_def all_lits_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def
          \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm)
        (simp add: all_lits_of_mm_union)
    have tauto_confl: \<open>\<not> tautology (the (get_conflict_wl S))\<close>
      apply (rule conflict_not_tautology[OF S_T _ T_U])
      using struct_invs not_none S_T T_U by (auto simp: twl_st)
    from not_tautology_mono[OF _ this, of ?D] have tauto_D: \<open>\<not> tautology ?D\<close>
      by (auto simp: S)
    have entailed:
      \<open>mset `# ran_mf (get_clauses_wl S) +  (get_unit_learned_clss_wl S + get_unit_init_clss_wl S) +
         (get_subsumed_init_clauses_wl S + get_subsumed_learned_clauses_wl S)\<Turnstile>pm
        add_mset (- lit_of (hd (get_trail_wl S)))
           (remove1_mset (- lit_of (hd (get_trail_wl S))) (the (get_conflict_wl S)))\<close>
      using uL_D learned not_none S_T T_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
      by (auto simp: ac_simps twl_st get_unit_clauses_wl_alt_def)
    define cach' where \<open>cach' = (\<lambda>_::nat. SEEN_UNKNOWN)\<close>
    have mini: \<open>minimize_and_extract_highest_lookup_conflict (all_atms_st S) (get_trail_wl S) (get_clauses_wl S)
              ?D cach' lbd (outl[0 := - lit_of (hd M)])
          \<le> \<Down> {((E, s, outl), E'). E = E' \<and> mset (tl outl) = E \<and>
                 outl ! 0 = - lit_of (hd M) \<and> E' \<subseteq># remove1_mset (- lit_of (hd M)) (the D) \<and>
                outl \<noteq> []}
              (iterate_over_conflict (- lit_of (hd M)) (get_trail_wl S)
                (mset `# ran_mf (get_clauses_wl S))
                (get_unit_learned_clss_wl S + get_unit_init_clss_wl S +
                 (get_subsumed_learned_clauses_wl S + get_subsumed_init_clauses_wl S))
              ?D)\<close>
      apply (rule minimize_and_extract_highest_lookup_conflict_iterate_over_conflict[of S T U
            \<open>outl [0 := - lit_of (hd M)]\<close>
            \<open>remove1_mset _ (the D)\<close> \<open>all_atms_st S\<close> cach' \<open>-lit_of (hd M)\<close> lbd])
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
        by (auto dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms simp: cach'_def twl_st S)
      subgoal using entailed unfolding S by (simp add: ac_simps)
      subgoal using \<L>\<^sub>i\<^sub>n_D .
      subgoal using \<L>\<^sub>i\<^sub>n_NU .
      subgoal using \<open>out_learned M D outl\<close> tl_outl_D
        by (auto simp: out_learned_def)
      subgoal using \<open>out_learned M D outl\<close> tl_outl_D
        by (auto simp: out_learned_def)
      subgoal using bounded unfolding all_atms_def by (simp add: S)
      done
    then have mini: \<open>minimize_and_extract_highest_lookup_conflict (all_atms_st S) M N
              ?D cach' lbd (outl[0 := - lit_of (hd M)])
          \<le> \<Down> {((E, s, outl), E'). E = E' \<and> mset (tl outl) = E \<and>
                 outl ! 0 = - lit_of (hd M) \<and> E' \<subseteq># remove1_mset (- lit_of (hd M)) (the D) \<and>
                  outl \<noteq> []}
              (iterate_over_conflict (- lit_of (hd M)) (get_trail_wl S)
                (mset `# ran_mf N)
                (get_unit_learned_clss_wl S + get_unit_init_clss_wl S +
                (get_subsumed_learned_clauses_wl S +
                    get_subsumed_init_clauses_wl S)) ?D)\<close>
      unfolding S by auto
    have mini: \<open>minimize_and_extract_highest_lookup_conflict (all_atms_st S) M N
              ?D cach' lbd (outl[0 := - lit_of (hd M)])
          \<le> \<Down> {((E, s, outl), E'). E = E' \<and> mset (tl outl) = E \<and>
                 outl ! 0 = - lit_of (hd M) \<and> E' \<subseteq># remove1_mset (- lit_of (hd M)) (the D) \<and>
                 outl \<noteq> []}
              (SPEC (\<lambda>D'. D' \<subseteq># ?D \<and>  mset `# ran_mf N +
                      (get_unit_learned_clss_wl S + get_unit_init_clss_wl S +
                       (get_subsumed_learned_clauses_wl S +
                         get_subsumed_init_clauses_wl S)) \<Turnstile>pm add_mset (- lit_of (hd M)) D'))\<close>
      apply (rule order.trans)
       apply (rule mini)
      apply (rule ref_two_step')
      apply (rule order.trans)
       apply (rule iterate_over_conflict_spec)
      subgoal using entailed by (auto simp: S ac_simps)
      subgoal
        using dist not_none S_T T_U unfolding S cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        by (auto simp: twl_st)
      subgoal by (auto simp: ac_simps)
      done
    have uM_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>- lit_of (hd M) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)\<close>
      using M_\<L>\<^sub>i\<^sub>n trail_nempty S_T T_U by (cases M)
        (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons uminus_\<A>\<^sub>i\<^sub>n_iff twl_st S)

    have L_D: \<open>lit_of (hd M) \<notin># the D\<close> and
      tauto_confl':  \<open>\<not>tautology (remove1_mset (- lit_of (hd M)) (the D))\<close>
      using uL_D tauto_confl
      by (auto dest!: multi_member_split simp: S add_mset_eq_add_mset tautology_add_mset)
    then have pre1: \<open>D \<noteq> None \<and> delete_from_lookup_conflict_pre (all_atms_st S) (- lit_of (hd M), the D)\<close>
      using not_none uL_D uM_\<L>\<^sub>a\<^sub>l\<^sub>l S_T T_U unfolding delete_from_lookup_conflict_pre_def
      by (auto simp: twl_st S)
    have pre2: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st S) M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_mm (all_atms_st S) (mset `# ran_mf N) \<equiv> True\<close>
      and lits_N: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (all_atms_st S) (mset `# ran_mf N)\<close>
      using M_\<L>\<^sub>i\<^sub>n S_T T_U not_none \<L>\<^sub>i\<^sub>n
      unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def literals_are_\<L>\<^sub>i\<^sub>n_def all_atms_def all_lits_def
      by (auto simp: twl_st S all_lits_of_mm_union)
    have \<open>0 < length outl\<close>
      using \<open>out_learned M D outl\<close>
      by (auto simp: out_learned_def)
    have trail_nempty: \<open>M \<noteq> []\<close>
      using trail_nempty S_T T_U
      by (auto simp: twl_st S)

    have lookup_conflict_remove1_pre: \<open>lookup_conflict_remove1_pre (-lit_of (hd M), D')\<close>
      using D' not_none not_empty S_T uM_\<L>\<^sub>a\<^sub>l\<^sub>l
      unfolding lookup_conflict_remove1_pre_def
      by (cases \<open>the D\<close>)
        (auto simp: option_lookup_clause_rel_def lookup_clause_rel_def S
          state_wl_l_def atms_of_def)
    then have lookup_conflict_remove1_pre: \<open>lookup_conflict_remove1_pre (-lit_of_last_trail_pol M', D')\<close>
      by (subst lit_of_last_trail_pol_lit_of_last_trail[THEN fref_to_Down_unRET_Id, of M M'])
        (use M'_M trail_nempty in \<open>auto simp: lit_of_hd_trail_def\<close>)

    have \<open>- lit_of (hd M) \<in># (the D)\<close>
      using uL_D by (auto simp: S)
    then have extract_shorter_conflict_wl_alt_def:
      \<open>extract_shorter_conflict_wl (M, N, D, NE, UE, NS, US, Q, W) = do {
        let K = lit_of (hd M);
        let D = (remove1_mset (-K) (the D));
        _ \<leftarrow> RETURN (); \<^cancel>\<open>vmtf rescoring\<close>
        E' \<leftarrow> (SPEC
          (\<lambda>(E'). E' \<subseteq># add_mset (-K) D \<and> - lit_of (hd M) :#  E' \<and>
             mset `# ran_mf N +
             (get_unit_learned_clss_wl S + get_unit_init_clss_wl S +
                (get_subsumed_learned_clauses_wl S +
                    get_subsumed_init_clauses_wl S)) \<Turnstile>pm E'));
        D \<leftarrow> RETURN (Some E');
        RETURN  (M, N, D, NE, UE, NS, US, Q, W)
      }\<close>
      unfolding extract_shorter_conflict_wl_def
      by (auto simp: RES_RETURN_RES image_iff mset_take_mset_drop_mset' S union_assoc
          Un_commute Let_def Un_assoc sup_left_commute)

    have lookup_clause_rel_unique: \<open>(D', a) \<in> lookup_clause_rel \<A> \<Longrightarrow> (D', b) \<in> lookup_clause_rel \<A> \<Longrightarrow> a = b\<close>
      for a b \<A>
      by (auto simp: lookup_clause_rel_def mset_as_position_right_unique)
    have isa_minimize_and_extract_highest_lookup_conflict:
      \<open>isa_minimize_and_extract_highest_lookup_conflict M' arena
         (lookup_conflict_remove1 (-lit_of (hd M)) D') cach lbd (outl[0 := - lit_of (hd M)])
      \<le> \<Down> {((E, s, outl), E').
            (E, mset (tl outl)) \<in> lookup_clause_rel (all_atms_st S) \<and>
            mset outl = E' \<and>
            outl ! 0 = - lit_of (hd M) \<and>
            E' \<subseteq># the D \<and> outl \<noteq> [] \<and> distinct outl \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S) (mset outl) \<and>
            \<not>tautology (mset outl) \<and>
	    (\<exists>cach'. (s, cach') \<in> cach_refinement (all_atms_st S))}
          (SPEC (\<lambda>E'. E' \<subseteq># add_mset (- lit_of (hd M)) (remove1_mset (- lit_of (hd M)) (the D)) \<and>
              - lit_of (hd M) \<in># E' \<and>
              mset `# ran_mf N +
              (get_unit_learned_clss_wl S + get_unit_init_clss_wl S +
                (get_subsumed_learned_clauses_wl S +
                    get_subsumed_init_clauses_wl S)) \<Turnstile>pm
              E'))\<close>
      (is \<open>_ \<le> \<Down> ?minimize (RES ?E)\<close>)
      apply (rule order_trans)
       apply (rule
          isa_minimize_and_extract_highest_lookup_conflict_minimize_and_extract_highest_lookup_conflict
          [THEN fref_to_Down_curry5,
            of \<open>all_atms_st S\<close> M N \<open>remove1_mset (-lit_of (hd M)) (the D)\<close> cach' lbd \<open>outl[0 := - lit_of (hd M)]\<close>
            _ _ _ _ _ _ \<open>set vdom\<close>])
      subgoal using bounded by (auto simp: S all_atms_def)
      subgoal using tauto_confl' pre2 by auto
      subgoal using D' not_none arena S_T uL_D uM_\<L>\<^sub>a\<^sub>l\<^sub>l not_empty D' L_D b cach_empty M'_M unfolding all_atms_def
        by (auto simp: option_lookup_clause_rel_def S state_wl_l_def image_image cach_refinement_empty_def cach'_def
            intro!: lookup_conflict_remove1[THEN fref_to_Down_unRET_uncurry]
            dest: multi_member_split lookup_clause_rel_unique)
      apply (rule order_trans)
       apply (rule mini[THEN ref_two_step'])
      subgoal
        using uL_D dist_D tauto_D \<L>\<^sub>i\<^sub>n_S \<L>\<^sub>i\<^sub>n_D tauto_D L_D
        by (fastforce simp: conc_fun_chain conc_fun_RES image_iff S union_assoc insert_subset_eq_iff
            neq_Nil_conv literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset tautology_add_mset
            intro: literals_are_in_\<L>\<^sub>i\<^sub>n_mono
            dest: distinct_mset_mono not_tautology_mono
            dest!: multi_member_split)
      done

    have empty_conflict_and_extract_clause_heur: \<open>isa_empty_conflict_and_extract_clause_heur M' x1 x2a
          \<le> \<Down>  ({((E, outl, n), E').
         (E, None) \<in> option_lookup_clause_rel (all_atms_st S) \<and>
         mset outl = the E' \<and>
         outl ! 0 = - lit_of (hd M) \<and>
         the E' \<subseteq># the D \<and> outl \<noteq> [] \<and> E' \<noteq> None \<and>
         (1 < length outl \<longrightarrow>
            highest_lit M (mset (tl outl)) (Some (outl ! 1, get_level M (outl ! 1)))) \<and>
         (1 < length outl \<longrightarrow> n = get_level M (outl ! 1)) \<and> (length outl = 1 \<longrightarrow> n = 0)}) (RETURN (Some E'))\<close>
      (is \<open>_ \<le> \<Down> ?empty_conflict _\<close>)
      if
        \<open>M \<noteq> []\<close> and
        \<open>- lit_of (hd M) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)\<close> and
        \<open>0 < length outl\<close> and
        \<open>lookup_conflict_remove1_pre (- lit_of (hd M), D')\<close> and
        \<open>(x, E')  \<in> ?minimize\<close> and
        \<open>E' \<in> ?E\<close> and
        \<open>x2 = (x1a, x2a)\<close> and
        \<open>x = (x1, x2)\<close>
      for x :: \<open>(nat \<times> bool option list) \<times>  (minimize_status list \<times> nat list) \<times> nat literal list\<close> and
        E' :: \<open>nat literal multiset\<close> and
        x1 :: \<open>nat \<times> bool option list\<close> and
        x2 :: \<open>(minimize_status list \<times> nat list) \<times>  nat literal list\<close> and
        x1a :: \<open>minimize_status list \<times> nat list\<close> and
        x2a :: \<open>nat literal list\<close>
    proof -
      show ?thesis
        apply (rule order_trans)
         apply (rule isa_empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause_heur
            [THEN fref_to_Down_curry2, of _ _ _ M x1 x2a \<open>all_atms_st S\<close>])
          apply fast
        subgoal using M'_M by auto
        apply (subst Down_id_eq)
        apply (rule order.trans)
         apply (rule empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause[of \<open>mset (tl x2a)\<close>])
        subgoal by auto
        subgoal using that by auto
        subgoal using that by auto
        subgoal using that by auto
        subgoal using that by auto
        subgoal using that by auto
        subgoal using bounded unfolding S all_atms_def by simp
        subgoal unfolding empty_conflict_and_extract_clause_def
          using that
          by (auto simp: conc_fun_RES RETURN_def)
        done
    qed

    have final: \<open>(((M', arena, x1b, Q', W', vm', \<phi>, clvls, empty_cach_ref x1a, lbd, take 1 x2a,
            stats, heur, vdom, avdom, lcount, opts),
            x2c, x1c),
          M, N, Da, NE, UE, NS, US, Q, W)
          \<in> ?shorter\<close>
      if
        \<open>M \<noteq> []\<close> and
        \<open>- lit_of (hd M) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)\<close> and
        \<open>0 < length outl\<close> and
        \<open>lookup_conflict_remove1_pre (- lit_of (hd M), D')\<close> and
        mini: \<open>(x, E')  \<in> ?minimize\<close> and
        \<open>E' \<in> ?E\<close> and
        \<open>(xa, Da) \<in> ?empty_conflict\<close> and
        st[simp]:
        \<open>x2b = (x1c, x2c)\<close>
        \<open>x2 = (x1a, x2a)\<close>
        \<open>x = (x1, x2)\<close>
        \<open>xa = (x1b, x2b)\<close> and
        vm': \<open>(vm', uu) \<in> {(c, uu). c \<in> isa_vmtf (all_atms_st S) M}\<close>
      for x E' x1 x2 x1a x2a xa Da x1b x2b x1c x2c vm' uu
    proof -
      have x1b_None: \<open>(x1b, None) \<in> option_lookup_clause_rel (all_atms_st S)\<close>
        using that apply (auto simp: S simp flip: all_atms_def)
        done
      have cach[simp]: \<open>cach_refinement_empty (all_atms_st S) (empty_cach_ref x1a)\<close>
        using empty_cach_ref_empty_cach[of \<open>all_atms_st S\<close>, THEN fref_to_Down_unRET, of x1a]
          mini bounded
        by (auto simp add: cach_refinement_empty_def empty_cach_def cach'_def S
            simp flip: all_atms_def)

      have
        out: \<open>out_learned M None (take (Suc 0) x2a)\<close>  and
        x1c_Da: \<open>mset x1c = the Da\<close> and
        Da_None: \<open>Da \<noteq> None\<close> and
        Da_D: \<open>the Da \<subseteq># the D\<close> and
        x1c_D: \<open>mset x1c \<subseteq># the D\<close> and
        x1c: \<open>x1c \<noteq> []\<close> and
        hd_x1c: \<open>hd x1c = - lit_of (hd M)\<close> and
        highest: \<open>Suc 0 < length x1c \<Longrightarrow> x2c = get_level M (x1c ! 1) \<and>
          highest_lit M (mset (tl x1c))
          (Some (x1c ! Suc 0, get_level M (x1c ! Suc 0)))\<close> and
        highest2: \<open>length x1c = Suc 0 \<Longrightarrow> x2c = 0\<close> and
        \<open>E' = mset x2a\<close> and
        \<open>- lit_of (M ! 0) \<in> set x2a\<close> and
        \<open>(\<lambda>x. mset (fst x)) ` set_mset (ran_m N) \<union>
        (set_mset (get_unit_learned_clss_wl S) \<union>
          set_mset (get_unit_init_clss_wl S)) \<union>
        (set_mset (get_subsumed_learned_clauses_wl S) \<union>
          set_mset (get_subsumed_init_clauses_wl S)) \<Turnstile>p
        mset x2a\<close> and
        \<open>x2a ! 0 = - lit_of (M ! 0)\<close> and
        \<open>x1c ! 0 = - lit_of (M ! 0)\<close> and
        \<open>mset x2a \<subseteq># the D\<close> and
        \<open>mset x1c \<subseteq># the D\<close> and
        \<open>x2a \<noteq> []\<close> and
        x1c_nempty: \<open>x1c \<noteq> []\<close> and
        \<open>distinct x2a\<close> and
        Da: \<open>Da = Some (mset x1c)\<close> and
        \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S) (mset x2a)\<close> and
        \<open>\<not> tautology (mset x2a)\<close>
        using that
        unfolding out_learned_def
       	by (auto simp add: hd_conv_nth S ac_simps simp flip: all_atms_def)
      have Da_D': \<open>remove1_mset (- lit_of (hd M)) (the Da) \<subseteq># remove1_mset (- lit_of (hd M)) (the D)\<close>
        using Da_D mset_le_subtract by blast

      have K: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of U)\<close>
        using stgy_invs unfolding twl_stgy_invs_def by fast
      have \<open>get_maximum_level M {#L \<in># the D. get_level M L < count_decided M#}
        < count_decided M\<close>
        using cdcl\<^sub>W_restart_mset.no_skip_no_resolve_level_get_maximum_lvl_le[OF nss nsr all_struct K]
          not_none not_empty confl trail_nempty S_T T_U
        unfolding get_maximum_level_def by (auto simp: twl_st S)
      then have
        \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) (the D)) < count_decided M\<close>
        by (subst D_filter) auto
      then have max_lvl_le:
        \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) (the Da)) < count_decided M\<close>
        using get_maximum_level_mono[OF Da_D', of M] by auto
      have \<open>((M', arena, x1b, Q', W', vm', \<phi>, clvls, empty_cach_ref x1a, lbd, take (Suc 0) x2a,
          stats, heur, vdom, avdom, lcount, opts),
        del_conflict_wl (M, N, Da, NE, UE, NS, US, Q, W))
        \<in> twl_st_heur_bt\<close>
        using S'_S x1b_None cach out vm' unfolding twl_st_heur_bt_def
        by (auto simp: twl_st_heur_def del_conflict_wl_def S S' twl_st_heur_bt_def
            twl_st_heur_conflict_ana_def S simp flip: all_atms_def)
      moreover have x2c: \<open>x2c = get_maximum_level M (remove1_mset (- lit_of (hd M)) (the Da))\<close>
        using highest highest2 x1c_nempty hd_x1c
        by (cases \<open>length x1c = Suc 0\<close>; cases x1c)
          (auto simp: highest_lit_def Da mset_tl)
      moreover have \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) (M, N, Some (mset x1c), NE, UE, NS, US, Q, W)\<close>
        using \<L>\<^sub>i\<^sub>n
        by (auto simp: S x2c literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def simp flip: all_atms_def)
      moreover have \<open>\<not>tautology (mset x1c)\<close>
        using tauto_confl  not_tautology_mono[OF x1c_D]
        by (auto simp: S x2c S')
      ultimately show ?thesis
        using \<L>\<^sub>i\<^sub>n_S x1c_Da Da_None dist_D D_none x1c_D x1c hd_x1c highest uM_\<L>\<^sub>a\<^sub>l\<^sub>l vm' M_\<L>\<^sub>i\<^sub>n
          max_lvl_le corr trail_nempty unfolding literals_are_\<L>\<^sub>i\<^sub>n_def
        by (simp add:  S x2c S')
    qed
    have hd_M'_M: \<open>lit_of_last_trail_pol M' = lit_of (hd M)\<close>
      by (subst lit_of_last_trail_pol_lit_of_last_trail[THEN fref_to_Down_unRET_Id, of M M'])
        (use M'_M trail_nempty in \<open>auto simp: lit_of_hd_trail_def\<close>)

    have vmtf_mark_to_rescore_also_reasons:
      \<open>isa_vmtf_mark_to_rescore_also_reasons M' arena (outl[0 := - lit_of (hd M)]) vm
          \<le> SPEC (\<lambda>c. (c, ()) \<in> {(c, _). c \<in> isa_vmtf (all_atms_st S) M})\<close>
      if
        \<open>M \<noteq> []\<close> and
        \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st S) M\<close> and
        \<open>- lit_of (hd M) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)\<close> and
        \<open>0 < length outl\<close> and
        \<open>lookup_conflict_remove1_pre (- lit_of (hd M), D')\<close>
    proof -
      have outl_hd_tl: \<open>outl[0 := - lit_of (hd M)] = - lit_of (hd M) # tl (outl[0 := - lit_of (hd M)])\<close> and
        [simp]: \<open>outl \<noteq> []\<close>
        using outl unfolding out_learned_def
        by (cases outl; auto; fail)+
      have uM_D: \<open>- lit_of (hd M) \<in># the D\<close>
        by (subst D_filter) auto
      have mset_outl_D: \<open>mset (outl[0 := - lit_of (hd M)]) = (the D)\<close>
        by (subst outl_hd_tl, subst mset.simps, subst tl_outl_D, subst D_filter)
          (use uM_D D_filter[symmetric] in auto)
      from arg_cong[OF this, of set_mset] have set_outl_D: \<open>set (outl[0 := - lit_of (hd M)]) = set_mset (the D)\<close>
        by auto

      have outl_Lall: \<open>\<forall>L\<in>set (outl[0 := - lit_of (hd M)]). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)\<close>
        using \<L>\<^sub>i\<^sub>n_S unfolding set_outl_D
        by (auto simp: S all_lits_of_m_add_mset
            all_atms_def literals_are_in_\<L>\<^sub>i\<^sub>n_def literals_are_in_\<L>\<^sub>i\<^sub>n_in_mset_\<L>\<^sub>a\<^sub>l\<^sub>l
            dest: multi_member_split)
      have \<open>distinct (outl[0 := - lit_of (hd M)])\<close> using dist_D by(auto simp: S mset_outl_D[symmetric])
      then have length_outl: \<open>length outl \<le> uint32_max\<close>
        using bounded tauto_confl \<L>\<^sub>i\<^sub>n_S simple_clss_size_upper_div2[OF bounded, of \<open>mset (outl[0 := - lit_of (hd M)])\<close>]
        by (auto simp: out_learned_def S  mset_outl_D[symmetric] uint32_max_def simp flip: all_atms_def)
      have lit_annots: \<open>\<forall>L\<in>set (outl[0 := - lit_of (hd M)]).
        \<forall>C. Propagated (- L) C \<in> set M \<longrightarrow>
           C \<noteq> 0 \<longrightarrow>
           C \<in># dom_m N \<and>
           (\<forall>C\<in>set [C..<C + arena_length arena C]. arena_lit arena C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S))\<close>
        unfolding set_outl_D
        apply (intro ballI allI impI conjI)
        subgoal
          using list_invs S_T unfolding twl_list_invs_def
          by (auto simp: S)
        subgoal for L C i
          using list_invs S_T arena lits_N literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<open>(all_atms_st S)\<close> N C \<open>i - C\<close>]
          unfolding twl_list_invs_def
          by (auto simp: S arena_lifting all_atms_def[symmetric])
        done
      obtain vm0 where
        vm_vm0: \<open>(vm, vm0) \<in> Id \<times>\<^sub>f distinct_atoms_rel (all_atms_st S)\<close> and
        vm0: \<open>vm0 \<in> vmtf (all_atms_st S) M\<close>
        using vm by (cases vm) (auto simp: isa_vmtf_def S simp flip: all_atms_def)
      show ?thesis
        apply (cases vm)
        apply (rule order.trans,
            rule isa_vmtf_mark_to_rescore_also_reasons_vmtf_mark_to_rescore_also_reasons[of \<open>all_atms_st S\<close>,
              THEN fref_to_Down_curry3,
              of _ _ _ vm M arena \<open>outl[0 := - lit_of (hd M)]\<close> vm0])
        subgoal using bounded S by (auto simp: all_atms_def)
        subgoal using vm arena M'_M vm_vm0 by (auto simp: isa_vmtf_def)[]
        apply (rule order.trans, rule ref_two_step')
         apply (rule vmtf_mark_to_rescore_also_reasons_spec[OF vm0 arena _ outl_Lall lit_annots])
        subgoal using length_outl by auto
        by (auto simp: isa_vmtf_def conc_fun_RES S all_atms_def)
    qed

    show ?thesis
      unfolding extract_shorter_conflict_list_heur_st_def
        empty_conflict_and_extract_clause_def S S' prod.simps hd_M'_M
      apply (rewrite at  \<open>let _ = list_update _ _ _ in _ \<close>Let_def)
      apply (rewrite at  \<open>let _ = empty_cach_ref _ in _ \<close> Let_def)
      apply (subst extract_shorter_conflict_wl_alt_def)
      apply (refine_vcg isa_minimize_and_extract_highest_lookup_conflict
          empty_conflict_and_extract_clause_heur)
      subgoal using trail_nempty using M'_M by (auto simp: trail_pol_def ann_lits_split_reasons_def)
      subgoal using \<open>0 < length outl\<close> .
      subgoal unfolding hd_M'_M[symmetric] by (rule lookup_conflict_remove1_pre)
               apply (rule vmtf_mark_to_rescore_also_reasons; assumption?)
      subgoal using trail_nempty .
      subgoal using pre2  by (auto simp: S all_atms_def)
      subgoal using uM_\<L>\<^sub>a\<^sub>l\<^sub>l by (auto simp: S all_atms_def)
      subgoal premises p
        using bounded p(5,7-) by (auto simp: S empty_cach_ref_pre_def cach_refinement_alt_def
       intro!: IsaSAT_Lookup_Conflict.bounded_included_le simp: all_atms_def simp del: isasat_input_bounded_def)
      subgoal by auto
      subgoal using bounded pre2
        by (auto dest!: simple_clss_size_upper_div2 simp: uint32_max_def S all_atms_def[symmetric]
            simp del: isasat_input_bounded_def)
      subgoal using trail_nempty by fast
      subgoal using uM_\<L>\<^sub>a\<^sub>l\<^sub>l .
         apply assumption+
      subgoal
        using trail_nempty uM_\<L>\<^sub>a\<^sub>l\<^sub>l
        unfolding S[symmetric] S'[symmetric]
        by (rule final)
      done
  qed

  have find_decomp_wl_nlit: \<open>find_decomp_wl_st_int n T
      \<le> \<Down>  {(U, U''). (U, U'') \<in> twl_st_heur_bt \<and> equality_except_trail_wl U'' T' \<and>
       (\<exists>K M2. (Decided K # (get_trail_wl U''), M2) \<in> set (get_all_ann_decomposition (get_trail_wl T')) \<and>
          get_level (get_trail_wl T') K = get_maximum_level (get_trail_wl T') (the (get_conflict_wl T') - {#-lit_of (hd (get_trail_wl T'))#}) + 1 \<and>
          get_clauses_wl_heur U = get_clauses_wl_heur S) \<and>
	  (get_trail_wl U'', get_vmtf_heur U) \<in> (Id \<times>\<^sub>f (Id \<times>\<^sub>f (distinct_atoms_rel (all_atms_st T'))\<inverse>)) ``
	    (Collect (find_decomp_w_ns_prop (all_atms_st T') (get_trail_wl T') n (get_vmtf_heur T)))}
          (find_decomp_wl LK' T')\<close>
    (is \<open>_ \<le>  \<Down> ?find_decomp _\<close>)
    if
      \<open>(S, S') \<in> ?R\<close> and
      \<open>backtrack_wl_inv S'\<close> and
      \<open>backtrack_wl_D_heur_inv S\<close> and
      TT': \<open>(TnC, T') \<in> ?shorter S' S\<close> and
      [simp]: \<open>nC = (n, C)\<close> and
      [simp]: \<open>TnC = (T, nC)\<close> and
       KK': \<open>(LK, LK') \<in> {(L, L'). L = L' \<and> L = lit_of (hd (get_trail_wl S'))}\<close>
    for S S' TnC T' T nC n C LK LK'
  proof -
    obtain M N D NE UE NS US Q W where
      T': \<open>T' = (M, N, D, NE, UE, NS, US, Q, W)\<close>
      by (cases T')
    obtain M' W' vm \<phi> clvls cach lbd outl stats arena D' Q' where
      T: \<open>T = (M', arena, D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats)\<close>
      using TT' by (cases T) (auto simp: twl_st_heur_bt_def T' del_conflict_wl_def)
    have
      vm: \<open>vm \<in> isa_vmtf (all_atms_st T') M\<close> and
      M'M: \<open>(M', M) \<in> trail_pol (all_atms_st T')\<close> and
      lits_trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st T') (get_trail_wl T')\<close>
      using TT' by (auto simp: twl_st_heur_bt_def del_conflict_wl_def
          all_atms_def[symmetric] T T')

    obtain vm0 where
      vm: \<open>(vm, vm0) \<in> Id \<times>\<^sub>r distinct_atoms_rel (all_atms_st T')\<close> and
      vm0: \<open>vm0 \<in> vmtf (all_atms_st T') M\<close>
      using vm unfolding isa_vmtf_def by (cases vm) auto

    have [simp]:
       \<open>LK' = lit_of (hd (get_trail_wl T'))\<close>
       \<open>LK = LK'\<close>
       using KK' TT' by (auto simp: equality_except_conflict_wl_get_trail_wl)

    have n: \<open>n = get_maximum_level M (remove1_mset (- lit_of (hd M)) (mset C))\<close> and
      eq: \<open>equality_except_conflict_wl T' S'\<close> and
      \<open>the D = mset C\<close> \<open>D \<noteq> None\<close> and
      clss_eq: \<open>get_clauses_wl_heur S = arena\<close> and
      n: \<open>n < count_decided (get_trail_wl T')\<close> and
      bounded: \<open>isasat_input_bounded (all_atms_st T')\<close> and
      T_T': \<open>(T, del_conflict_wl T') \<in> twl_st_heur_bt\<close> and
      n2: \<open>n = get_maximum_level M (remove1_mset (- lit_of (hd M)) (the D))\<close>
      using TT' KK' by (auto simp: T T' twl_st_heur_bt_def del_conflict_wl_def simp flip: all_atms_def
          simp del: isasat_input_bounded_def)
    have [simp]: \<open>get_trail_wl S' = M\<close>
      using eq \<open>the D = mset C\<close> \<open>D \<noteq> None\<close> by (cases S'; auto simp: T')
    have [simp]: \<open>get_clauses_wl_heur S = arena\<close>
      using TT' by (auto simp: T T')

    have n_d: \<open>no_dup M\<close>
      using M'M unfolding trail_pol_def by auto

    have [simp]: \<open>NO_MATCH [] M \<Longrightarrow> out_learned M None ai \<longleftrightarrow> out_learned [] None ai\<close> for M ai
      by (auto simp: out_learned_def)

    show ?thesis
      unfolding T' find_decomp_wl_st_int_def prod.case T
      apply (rule bind_refine_res)
       prefer 2
       apply (rule order.trans)
        apply (rule isa_find_decomp_wl_imp_find_decomp_wl_imp[THEN fref_to_Down_curry2, of M n vm0
            _ _ _ \<open>all_atms_st T'\<close>])
      subgoal using n by (auto simp: T')
      subgoal using M'M vm by auto
       apply (rule order.trans)
        apply (rule ref_two_step')
        apply (rule find_decomp_wl_imp_le_find_decomp_wl')
      subgoal using vm0 .
      subgoal using lits_trail by (auto simp: T')
      subgoal using n by (auto simp: T')
      subgoal using n_d .
      subgoal using bounded .
      unfolding find_decomp_w_ns_def conc_fun_RES
       apply (rule order.refl)
      using T_T' n_d (*TODO Tune proof*)
      apply (cases \<open>get_vmtf_heur T\<close>)
      apply (auto simp: find_decomp_wl_def twl_st_heur_bt_def T T' del_conflict_wl_def
          dest: no_dup_appendD
          simp flip: all_atms_def n2
          intro!: RETURN_RES_refine
          intro: isa_vmtfI)
      apply (rule_tac x=an in exI)
      apply (auto dest: no_dup_appendD intro: isa_vmtfI simp: T')
      apply (auto simp: Image_iff T')
      done
  qed

  have fst_find_lit_of_max_level_wl: \<open>RETURN (C ! 1)
      \<le> \<Down> Id
          (find_lit_of_max_level_wl U' LK')\<close>
    if
      \<open>(S, S') \<in> ?R\<close> and
      \<open>backtrack_wl_inv S'\<close> and
      \<open>backtrack_wl_D_heur_inv S\<close> and
      TT': \<open>(TnC, T') \<in> ?shorter S' S\<close> and
      [simp]: \<open>nC = (n, C)\<close> and
      [simp]: \<open>TnC = (T, nC)\<close> and
      find_decomp: \<open>(U, U') \<in> ?find_decomp S T' n\<close> and
      size_C: \<open>1 < length C\<close> and
      size_conflict_U': \<open>1 < size (the (get_conflict_wl U'))\<close> and
       KK': \<open>(LK, LK') \<in> {(L, L'). L = L' \<and> L = lit_of (hd (get_trail_wl S'))}\<close>
    for S S' TnC T' T nC n C U U' LK LK'
  proof -
    obtain M N NE UE Q W NS US where
      T': \<open>T' = (M, N, Some (mset C), NE, UE, NS, US,  Q, W)\<close> and
      \<open>C \<noteq> []\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> \<open>1 < length C\<close> find_decomp
      apply (cases U'; cases T'; cases S')
      by (auto simp: find_lit_of_max_level_wl_def)

    obtain M' K M2 where
      U': \<open>U' = (M', N, Some (mset C), NE, UE, NS, US, Q, W)\<close> and
      decomp: \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M)\<close> and
      lev_K: \<open>get_level M K = Suc (get_maximum_level M (remove1_mset (- lit_of (hd M)) (the (Some (mset C)))))\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> \<open>1 < length C\<close> find_decomp
      by (cases U'; cases S')
        (auto simp: find_lit_of_max_level_wl_def T')

    have [simp]:
       \<open>LK' = lit_of (hd (get_trail_wl T'))\<close>
       \<open>LK = LK'\<close>
       using KK' TT' by (auto simp: equality_except_conflict_wl_get_trail_wl)

    have n_d: \<open>no_dup (get_trail_wl S')\<close>
      using \<open>(S, S') \<in> ?R\<close>
      by (auto simp: twl_st_heur_conflict_ana_def trail_pol_def)

    have [simp]: \<open>get_trail_wl S' = get_trail_wl T'\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> \<open>1 < length C\<close> find_decomp
      by (cases T'; cases S'; auto simp: find_lit_of_max_level_wl_def U'; fail)+
    have [simp]: \<open>remove1_mset (- lit_of (hd M)) (mset C) = mset (tl C)\<close>
      apply (subst mset_tl)
      using \<open>(TnC, T') \<in> ?shorter S' S\<close>
      by (auto simp: find_lit_of_max_level_wl_def U' highest_lit_def T')

    have n_d: \<open>no_dup M\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> n_d unfolding T'
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
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> \<open>1 < length C\<close> hd_conv_nth[OF \<open>C \<noteq> []\<close>, symmetric]
      by (auto simp: find_lit_of_max_level_wl_def U' highest_lit_def T')
  qed

  have propagate_bt_wl_D_heur: \<open>propagate_bt_wl_D_heur LK C U
      \<le> \<Down> ?S (propagate_bt_wl LK' L' U')\<close>
    if
      SS': \<open>(S, S') \<in> ?R\<close> and
      \<open>backtrack_wl_inv S'\<close> and
      \<open>backtrack_wl_D_heur_inv S\<close> and
      \<open>(TnC, T') \<in> ?shorter S' S\<close> and
      [simp]: \<open>nC = (n, C)\<close> and
      [simp]: \<open>TnC = (T, nC)\<close> and
      find_decomp: \<open>(U, U') \<in> ?find_decomp S T' n\<close> and
      le_C: \<open>1 < length C\<close> and
      \<open>1 < size (the (get_conflict_wl U'))\<close> and
      C_L': \<open>(C ! 1, L') \<in> nat_lit_lit_rel\<close> and
      KK': \<open>(LK, LK') \<in> {(L, L'). L = L' \<and> L = lit_of (hd (get_trail_wl S'))}\<close>
    for S S' TnC T' T nC n C U U' L' LK LK'
  proof -

    have
      TT': \<open>(T, del_conflict_wl T') \<in> twl_st_heur_bt\<close> and
      n: \<open>n = get_maximum_level (get_trail_wl T')
          (remove1_mset (- lit_of (hd (get_trail_wl T'))) (mset C))\<close> and
      T_C: \<open>get_conflict_wl T' = Some (mset C)\<close> and
      T'S': \<open>equality_except_conflict_wl T' S'\<close> and
      C_nempty: \<open>C \<noteq> []\<close> and
      hd_C: \<open>hd C = - lit_of (hd (get_trail_wl T'))\<close> and
      highest: \<open>highest_lit (get_trail_wl T') (mset (tl C))
         (Some (C ! Suc 0, get_level (get_trail_wl T') (C ! Suc 0)))\<close> and
      incl: \<open>mset C \<subseteq># the (get_conflict_wl S')\<close> and
      dist_S': \<open>distinct_mset (the (get_conflict_wl S'))\<close> and
      list_confl_S': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S') (the (get_conflict_wl S'))\<close> and
      \<open>get_conflict_wl S' \<noteq> None\<close> and
      uM_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>-lit_of (hd (get_trail_wl S')) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S')\<close> and
      lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st T') T'\<close> and
      tr_nempty: \<open>get_trail_wl T' \<noteq> []\<close> and
      r: \<open>length (get_clauses_wl_heur S) = r\<close> \<open>length (get_clauses_wl_heur T) = r\<close> and
      corr: \<open>correct_watching S'\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close>  \<open>1 < length C\<close> \<open>(S, S') \<in> ?R\<close>
      by auto

    obtain K M2 where
      UU': \<open>(U, U') \<in> twl_st_heur_bt\<close> and
      U'U': \<open>equality_except_trail_wl U' T'\<close> and
      lev_K: \<open>get_level (get_trail_wl T') K = Suc (get_maximum_level (get_trail_wl T')
           (remove1_mset (- lit_of (hd (get_trail_wl T')))
             (the (get_conflict_wl T'))))\<close> and
      decomp: \<open>(Decided K # get_trail_wl U', M2) \<in> set (get_all_ann_decomposition (get_trail_wl T'))\<close> and
      r': \<open>length (get_clauses_wl_heur U) = r\<close> and
      S_arena: \<open>get_clauses_wl_heur U = get_clauses_wl_heur S\<close>
      using find_decomp r
      by auto

    obtain M N NE UE Q NS US W where
      T': \<open>T' = (M, N, Some (mset C), NE, UE, NS, US, Q, W)\<close> and
      \<open>C \<noteq> []\<close>
      using TT' T_C \<open>1 < length C\<close>
      apply (cases T'; cases S')
      by (auto simp: find_lit_of_max_level_wl_def)
    obtain D where
      S': \<open>S' = (M, N, D, NE, UE, NS, US, Q, W)\<close>
      using T'S' \<open>1 < length C\<close>
      apply (cases S')
      by (auto simp: find_lit_of_max_level_wl_def T' del_conflict_wl_def)

    obtain M1 where
      U': \<open>U' = (M1, N, Some (mset C), NE, UE, NS, US, Q, W)\<close> and
      lits_confl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S') (mset C)\<close> and
      \<open>mset C \<subseteq># the (get_conflict_wl S')\<close> and
      tauto: \<open>\<not> tautology (mset C)\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> \<open>1 < length C\<close> find_decomp
      apply (cases U')
      by (auto simp: find_lit_of_max_level_wl_def T' intro: literals_are_in_\<L>\<^sub>i\<^sub>n_mono)
    obtain M1' vm' W' \<phi> clvls cach lbd outl stats heur avdom vdom lcount arena D'
        Q' opts
      where
        U: \<open>U = (M1', arena, D', Q', W', vm', \<phi>, clvls, cach, lbd, outl, stats, heur,
           vdom, avdom, lcount, opts, [])\<close>
      using UU' find_decomp by (cases U) (auto simp: U' T' twl_st_heur_bt_def all_atms_def[symmetric])

    have [simp]:
       \<open>LK' = lit_of (hd M)\<close>
       \<open>LK = LK'\<close>
       using KK' SS' by (auto simp: equality_except_conflict_wl_get_trail_wl S')
    have
      M1'_M1: \<open>(M1', M1) \<in> trail_pol (all_atms_st U')\<close> and
      W'W: \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms_st U'))\<close> and
      vmtf: \<open>vm' \<in> isa_vmtf (all_atms_st U') M1\<close> and
      \<phi>: \<open>phase_saving (all_atms_st U') \<phi>\<close> and
      n_d_M1: \<open>no_dup M1\<close> and
      empty_cach: \<open>cach_refinement_empty (all_atms_st U') cach\<close> and
      \<open>length outl = Suc 0\<close> and
      outl: \<open>out_learned M1 None outl\<close> and
      vdom: \<open>vdom_m (all_atms_st U') W N \<subseteq> set vdom\<close> and
      lcount: \<open>lcount = size (learned_clss_l N)\<close> and
      vdom_m: \<open>vdom_m (all_atms_st U') W N \<subseteq> set vdom\<close> and
      D': \<open>(D', None) \<in> option_lookup_clause_rel (all_atms_st U')\<close> and
      valid: \<open>valid_arena arena N (set vdom)\<close> and
      avdom: \<open>mset avdom \<subseteq># mset vdom\<close> and
      bounded: \<open>isasat_input_bounded (all_atms_st U')\<close> and
      nempty: \<open>isasat_input_nempty (all_atms_st U')\<close> and
      dist_vdom: \<open>distinct vdom\<close> and
      heur: \<open>heuristic_rel (all_atms_st U') heur\<close>
      using UU' by (auto simp: out_learned_def twl_st_heur_bt_def U U' all_atms_def[symmetric])
    have [simp]: \<open>C ! 1 = L'\<close> \<open>C ! 0 = - lit_of (hd M)\<close> and
      n_d: \<open>no_dup M\<close>
      using SS' C_L' hd_C \<open>C \<noteq> []\<close> by (auto simp: S' U' T' twl_st_heur_conflict_ana_def hd_conv_nth)
    have undef: \<open>undefined_lit M1 (lit_of (hd M))\<close>
      using decomp n_d
      by (auto dest!: get_all_ann_decomposition_exists_prepend simp: T' hd_append U' neq_Nil_conv
          split: if_splits)
    have C_1_neq_hd: \<open>C ! Suc 0 \<noteq> - lit_of (hd M)\<close>
      using distinct_mset_mono[OF incl dist_S'] C_L' \<open>1 < length C\<close>  \<open>C ! 0 = - lit_of (hd M)\<close>
      by (cases C; cases \<open>tl C\<close>) (auto simp del: \<open>C ! 0 = - lit_of (hd M)\<close>)
    have H: \<open>(RES ((\<lambda>i. (fmupd i (C, False) N, i)) ` {i. 0 < i \<and> i \<notin># dom_m N}) \<bind>
                   (\<lambda>(N, i).  ASSERT (i \<in># dom_m N) \<bind> (\<lambda>_. f N i))) =
          (RES ((\<lambda>i. (fmupd i (C, False) N, i)) ` {i. 0 < i \<and> i \<notin># dom_m N}) \<bind>
                   (\<lambda>(N, i). f N i))\<close> (is \<open>?A = ?B\<close>) for f C N
    proof -
      have \<open>?B \<le> ?A\<close>
        by (force intro: ext complete_lattice_class.Sup_subset_mono
          simp: intro_spec_iff bind_RES)
      moreover have \<open>?A \<le> ?B\<close>
        by (force intro: ext complete_lattice_class.Sup_subset_mono
          simp: intro_spec_iff bind_RES)
      ultimately show ?thesis by auto
    qed

    have propagate_bt_wl_D_heur_alt_def:
      \<open>propagate_bt_wl_D_heur = (\<lambda>L C (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
           vdom, avdom, lcount, opts). do {
          ASSERT(length vdom \<le> length N0);
          ASSERT(length avdom \<le> length N0);
          ASSERT(nat_of_lit (C!1) < length W0 \<and> nat_of_lit (-L) < length W0);
          ASSERT(length C > 1);
          let L' = C!1;
          ASSERT (length C \<le> uint32_max div 2 + 1);
          (vm, \<phi>) \<leftarrow> isa_vmtf_rescore C M vm0 \<phi>0;
          glue \<leftarrow> get_LBD lbd;
          let _ = C;
          let b = False;
          ASSERT(isasat_fast (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
            vdom, avdom, lcount, opts) \<longrightarrow> append_and_length_fast_code_pre ((b, C), N0));
          ASSERT(isasat_fast (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
             vdom, avdom, lcount, opts) \<longrightarrow> lcount < sint64_max);
          (N, i) \<leftarrow> fm_add_new b C N0;
          ASSERT(update_lbd_pre ((i, glue), N));
          let N = update_lbd i glue N;
          ASSERT(isasat_fast (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
            vdom, avdom, lcount, opts) \<longrightarrow> length_ll W0 (nat_of_lit (-L)) < sint64_max);
          let W = W0[nat_of_lit (- L) := W0 ! nat_of_lit (- L) @ [(i, L', length C = 2)]];
          ASSERT(isasat_fast (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
            vdom, avdom, lcount, opts) \<longrightarrow> length_ll W (nat_of_lit L') < sint64_max);
          let W = W[nat_of_lit L' := W!nat_of_lit L' @ [(i, -L, length C = 2)]];
          lbd \<leftarrow> lbd_empty lbd;
	         ASSERT(isa_length_trail_pre M);
          let j = isa_length_trail M;
          ASSERT(i \<noteq> DECISION_REASON);
          ASSERT(cons_trail_Propagated_tr_pre ((-L, i), M));
          M \<leftarrow> cons_trail_Propagated_tr (- L) i M;
          vm \<leftarrow> isa_vmtf_flush_int M vm;
          ASSERT(atm_of L < length \<phi>);
          RETURN (M, N, D, j, W, vm, save_phase (-L) \<phi>, 0,
            cach, lbd, outl, add_lbd (of_nat glue) stats, update_heuristics glue heur, vdom @ [ i],
              avdom @ [i], Suc lcount, opts)
      })\<close>
      unfolding propagate_bt_wl_D_heur_def Let_def
      by auto
    have find_new_alt: \<open>SPEC
                 (\<lambda>(N', i). N' = fmupd i (D'', False) N \<and> 0 < i \<and>
                      i \<notin># dom_m N \<and>
                      (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE) + (NS + US)).
                          i \<notin> fst ` set (W L))) = do {

          i \<leftarrow> SPEC
                 (\<lambda>i. 0 < i \<and>
                      i \<notin># dom_m N \<and>
                      (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE) + (NS + US)).
                          i \<notin> fst ` set (W L)));
         N' \<leftarrow> RETURN (fmupd i (D'', False) N);
         RETURN (N', i)
      }\<close> for D''
      by (auto simp: RETURN_def RES_RES_RETURN_RES2
       RES_RES_RETURN_RES)
    have propagate_bt_wl_D_alt_def:
      \<open>propagate_bt_wl LK' L' U' = do {
            ASSERT (propagate_bt_wl_pre LK' L' (M1, N, Some (mset C), NE, UE, NS, US, Q, W));
            _ \<leftarrow> RETURN (); \<^cancel>\<open>phase saving\<close>
            _ \<leftarrow> RETURN (); \<^cancel>\<open>LBD\<close>
            D'' \<leftarrow>
              list_of_mset2 (- LK') L'
               (the (Some (mset C)));
            (N, i) \<leftarrow> SPEC
                 (\<lambda>(N', i). N' = fmupd i (D'', False) N \<and> 0 < i \<and>
                      i \<notin># dom_m N \<and>
                      (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE) + (NS + US)).
                          i \<notin> fst ` set (W L)));
            _ \<leftarrow> RETURN (); \<^cancel>\<open>lbd empty\<close>
            _ \<leftarrow> RETURN (); \<^cancel>\<open>lbd empty\<close>
	     M2 \<leftarrow> cons_trail_propagate_l (- LK') i M1;
            _ \<leftarrow> RETURN (); \<^cancel>\<open>vmtf_flush\<close>
            RETURN
              (M2,
                N, None, NE, UE, NS, US, {#LK'#},
                W(- LK' := W (- LK') @ [(i, L', length D'' = 2)],
                  L' := W L' @ [(i, - LK', length D'' = 2)]))
          }\<close>
      unfolding propagate_bt_wl_def Let_def find_new_alt nres_monad3
        U U' H get_fresh_index_wl_def prod.case
        propagate_bt_wl_def Let_def rescore_clause_def
      by (auto simp: U' RES_RES2_RETURN_RES RES_RETURN_RES \<phi> uminus_\<A>\<^sub>i\<^sub>n_iff
          uncurry_def RES_RES_RETURN_RES length_list_ge2 C_1_neq_hd
          get_fresh_index_def RES_RETURN_RES2 RES_RES_RETURN_RES2 list_of_mset2_def
          cons_trail_propagate_l_def
          intro!: bind_cong[OF refl]
          simp flip: all_lits_alt_def2 all_lits_alt_def all_lits_def)

    have [refine0]: \<open>SPEC (\<lambda>(vm', \<phi>'). vm' \<in> vmtf \<A> M1 \<and> phase_saving \<A> \<phi>')
       \<le> \<Down>{((vm', \<phi>'), ()). vm' \<in> vmtf \<A> M1 \<and> phase_saving \<A> \<phi>'} (RETURN ())\<close> for \<A>
      by (auto intro!: RES_refine simp: RETURN_def)

    obtain vm0 where
      vm: \<open>(vm', vm0) \<in> Id \<times>\<^sub>r distinct_atoms_rel (all_atms_st U')\<close> and
      vm0: \<open>vm0 \<in> vmtf (all_atms_st U') M1\<close>
      using vmtf unfolding isa_vmtf_def by (cases vm') auto
    have [refine0]:
      \<open>isa_vmtf_rescore C M1' vm' \<phi> \<le> SPEC (\<lambda>c. (c, ()) \<in> {((vm, \<phi>), _).
         vm \<in> isa_vmtf (all_atms_st U') M1 \<and>
	       phase_saving (all_atms_st U') \<phi>})\<close>
      apply (rule order.trans)
       apply (rule isa_vmtf_rescore[of \<open>all_atms_st U'\<close>, THEN fref_to_Down_curry3, of _ _ _ _ C M1 vm0 \<phi>])
      subgoal using bounded by auto
      subgoal using vm M1'_M1 by auto
      apply (rule order.trans)
       apply (rule ref_two_step')
       apply (rule vmtf_rescore_score_clause[THEN fref_to_Down_curry3, of \<open>all_atms_st U'\<close> C M1 vm0 \<phi>])
      subgoal using vm0 lits_confl \<phi> by (auto simp: S' U')
      subgoal using vm M1'_M1 by auto
      subgoal by (auto simp: rescore_clause_def conc_fun_RES intro!: isa_vmtfI)
      done

    have [refine0]: \<open>isa_vmtf_flush_int Ma vm \<le>
         SPEC(\<lambda>c. (c, ()) \<in> {(vm', _). vm' \<in> isa_vmtf (all_atms_st U') M2})\<close>
      if vm: \<open>vm \<in> isa_vmtf (all_atms_st U') M1\<close> and
       Ma: \<open>(Ma, M2)
       \<in> {(M0, M0'').
         (M0, M0'') \<in> trail_pol (all_atms_st U') \<and>
         M0'' = Propagated (- L) i # M1 \<and>
         no_dup M0''}\<close>
      for vm i L Ma M2
    proof -
      let ?M1' = \<open>cons_trail_Propagated_tr L i M1'\<close>
      let ?M1 = \<open>Propagated (-L) i # M1\<close>

      have M1'_M1: \<open>(Ma, M2) \<in> trail_pol (all_atms_st U')\<close>
        using Ma by auto

      have vm: \<open>vm \<in> isa_vmtf (all_atms_st U') ?M1\<close>
        using vm by (auto simp: isa_vmtf_def dest: vmtf_consD)
      obtain vm0 where
        vm: \<open>(vm, vm0) \<in> Id \<times>\<^sub>r distinct_atoms_rel (all_atms_st U')\<close> and
        vm0: \<open>vm0 \<in> vmtf (all_atms_st U') ?M1\<close>
        using vm unfolding isa_vmtf_def by (cases vm) auto
      show ?thesis
      	apply (rule order.trans)
      	 apply (rule isa_vmtf_flush_int[THEN fref_to_Down_curry, of _ _ ?M1 vm])
      	  apply ((solves \<open>use M1'_M1 Ma in auto\<close>)+)[2]
      	apply (subst Down_id_eq)
      	apply (rule order.trans)
      	 apply (rule vmtf_change_to_remove_order'[THEN fref_to_Down_curry, of \<open>all_atms_st U'\<close> ?M1 vm0 ?M1 vm])
      	subgoal using vm0 bounded nempty by auto
      	subgoal using vm by auto
      	subgoal using Ma by (auto simp: vmtf_flush_def conc_fun_RES RETURN_def intro: isa_vmtfI)
      	done
    qed

    have [refine0]: \<open>(isa_length_trail M1', ()) \<in> {(j, _). j = length M1}\<close>
      by (subst isa_length_trail_length_u[THEN fref_to_Down_unRET_Id, OF _ M1'_M1]) auto
    have [refine0]: \<open>get_LBD lbd \<le> \<Down> {(_, _). True}(RETURN ())\<close>
      unfolding get_LBD_def by (auto intro!: RES_refine simp: RETURN_def)
    have [refine0]: \<open>RETURN C
       \<le> \<Down> Id
          (list_of_mset2 (- LK') L'
            (the (Some (mset C))))\<close>
      using that
      by (auto simp: list_of_mset2_def S')
    have [simp]: \<open>0 < header_size D''\<close> for D''
      by (auto simp: header_size_def)
    have [simp]: \<open>length arena + header_size D'' \<notin> set vdom\<close>
      \<open>length arena + header_size D'' \<notin> vdom_m (all_atms_st U') W N\<close>
      \<open>length arena + header_size D'' \<notin># dom_m N\<close> for D''
      using valid_arena_in_vdom_le_arena(1)[OF valid] vdom
      by (auto 5 1 simp: vdom_m_def)
    have add_new_alt_def: \<open>(SPEC
            (\<lambda>(N', i).
                N' = fmupd i (D'', False) N \<and>
                0 < i \<and>
                i \<notin># dom_m N \<and>
                (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE) + (NS + US)).
                    i \<notin> fst ` set (W L)))) =
          (SPEC
            (\<lambda>(N', i).
                N' = fmupd i (D'', False) N \<and>
                0 < i \<and>
                i \<notin> vdom_m (all_atms_st U') W N))\<close> for D''
      using lits
      by (auto simp: T' vdom_m_def literals_are_\<L>\<^sub>i\<^sub>n_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def U' all_atms_def
        all_lits_def ac_simps)
    have [refine0]: \<open>fm_add_new False C arena
       \<le> \<Down> {((arena', i), (N', i')). valid_arena arena' N' (insert i (set vdom)) \<and> i = i' \<and>
             i \<notin># dom_m N \<and> i \<notin> set vdom \<and> length arena' = length arena + header_size D'' + length D''}
          (SPEC
            (\<lambda>(N', i).
                N' = fmupd i (D'', False) N \<and>
                0 < i \<and>
                i \<notin># dom_m N \<and>
                (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE) + (NS + US)).
                    i \<notin> fst ` set (W L))))\<close>
      if \<open>(C, D'') \<in> Id\<close> for D''
      apply (subst add_new_alt_def)
      apply (rule order_trans)
       apply (rule fm_add_new_append_clause)
      using that valid le_C vdom
      by (auto simp: intro!: RETURN_RES_refine valid_arena_append_clause)
    have [refine0]:
      \<open>lbd_empty lbd \<le> SPEC (\<lambda>c. (c, ()) \<in> {(c, _). c = replicate (length lbd) False})\<close>
      by (auto simp: lbd_empty_def)

    have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S') (mset C)\<close>
      using incl list_confl_S' literals_are_in_\<L>\<^sub>i\<^sub>n_mono by blast
    then have C_Suc1_in: \<open>C ! Suc 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S')\<close>
      using \<open>1 < length C\<close>
      by (cases C; cases \<open>tl C\<close>) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    then have \<open>nat_of_lit (C ! Suc 0) < length W'\<close> \<open>nat_of_lit (- lit_of (hd (get_trail_wl S'))) < length W'\<close> and
     W'_eq:  \<open>W' ! (nat_of_lit (C ! Suc 0)) = W (C! Suc 0)\<close>
        \<open>W' ! (nat_of_lit (- lit_of (hd (get_trail_wl S')))) = W (- lit_of (hd (get_trail_wl S')))\<close>
      using uM_\<L>\<^sub>a\<^sub>l\<^sub>l W'W unfolding map_fun_rel_def by (auto simp: image_image S' U')
    have le_C_ge: \<open>length C \<le> uint32_max div 2 + 1\<close>
      using clss_size_uint32_max[OF bounded, of \<open>mset C\<close>] \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S') (mset C)\<close> list_confl_S'
        dist_S' incl size_mset_mono[OF incl] distinct_mset_mono[OF incl]
        simple_clss_size_upper_div2[OF bounded _ _ tauto]
      by (auto simp: uint32_max_def S' U' all_atms_def[symmetric])
    have tr_SS': \<open>(get_trail_wl_heur S, M) \<in> trail_pol (all_atms_st S')\<close>
      using \<open>(S, S') \<in> ?R\<close> unfolding twl_st_heur_conflict_ana_def
      by (auto simp: all_atms_def S')
    have All_atms_rew: \<open>set_mset (all_atms (fmupd x' (C', b) N) (NE + UE + NS + US)) =
        set_mset (all_atms N (NE + UE + NS + US))\<close> (is ?A)
      \<open>trail_pol (all_atms (fmupd x' (C', b) N) (NE + UE + NS + US)) =
        trail_pol (all_atms N (NE + UE + NS + US))\<close> (is ?B)
      \<open>isa_vmtf (all_atms (fmupd x' (C', b) N) (NE + UE + NS + US)) =
        isa_vmtf (all_atms N (NE + UE + NS + US))\<close> (is ?C)
      \<open>option_lookup_clause_rel  (all_atms (fmupd x' (C', b) N) (NE + UE + NS + US)) =
        option_lookup_clause_rel (all_atms N (NE + UE + NS + US))\<close> (is ?D)
      \<open>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms (fmupd x' (C', b) N) (NE + UE + NS + US))) =
         \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms N (NE + UE + NS + US)))\<close> (is ?E)
      \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms (fmupd x' (C', b) N) (NE + UE + NS + US))) =
        set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N (NE + UE + NS + US)))\<close>
      \<open>phase_saving ((all_atms (fmupd x' (C', b) N) (NE + UE + NS + US))) =
        phase_saving ((all_atms N (NE + UE + NS + US)))\<close> (is ?F)
      \<open>cach_refinement_empty ((all_atms (fmupd x' (C', b) N) (NE + UE + NS + US))) =
        cach_refinement_empty ((all_atms N (NE + UE + NS + US)))\<close> (is ?G) (*cach_refinement_nonull*)
      \<open>cach_refinement_nonull ((all_atms (fmupd x' (C', b) N) (NE + UE + NS + US))) =
        cach_refinement_nonull ((all_atms N (NE + UE + NS + US)))\<close> (is ?G2)
      \<open>vdom_m ((all_atms (fmupd x' (C', b) N) (NE + UE + NS + US))) =
        vdom_m ((all_atms N (NE + UE + NS + US)))\<close> (is ?H)
      \<open>isasat_input_bounded ((all_atms (fmupd x' (C', b) N) (NE + UE + NS + US))) =
        isasat_input_bounded ((all_atms N (NE + UE + NS + US)))\<close> (is ?I)
      \<open>isasat_input_nempty ((all_atms (fmupd x' (C', b) N) (NE + UE + NS + US))) =
        isasat_input_nempty ((all_atms N (NE + UE + NS + US)))\<close> (is ?J)
      \<open>vdom_m (all_atms N (NE + UE + NS + US)) W (fmupd x' (C', b) N) =
        insert x' (vdom_m (all_atms N (NE + UE + NS + US)) W N)\<close> (is ?K)
      \<open>heuristic_rel ((all_atms (fmupd x' (C', b) N) (NE + UE + NS + US))) =
        heuristic_rel (all_atms N (NE + UE + NS + US))\<close> (is ?L)
      if \<open>x' \<notin># dom_m N\<close> and C: \<open>C' = C\<close> for b x' C'
    proof -
      show A: ?A
        using \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S')  (mset C)\<close> that
        by (auto simp: all_atms_def all_lits_def ran_m_mapsto_upd_notin all_lits_of_mm_add_mset
            U' S'  in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n literals_are_in_\<L>\<^sub>i\<^sub>n_def ac_simps)
      have  A2: \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms (fmupd x' (C, b) N) (NE + UE + NS + US))) =
        set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N (NE + UE + NS + US)))\<close>
        using A unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_def C by (auto simp: A)
      then show \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms (fmupd x' (C', b) N) (NE + UE + NS + US))) =
        set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N (NE + UE + NS + US)))\<close>
        using A unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_def C by (auto simp: A)
      have A3: \<open>set_mset (all_atms (fmupd x' (C, b) N) (NE + UE + NS + US)) =
        set_mset (all_atms N (NE + UE + NS + US))\<close>
        using A unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_def C by (auto simp: A)

      show ?B and ?C and ?D and ?E and ?F and ?G and ?G2 and ?H and ?I and ?J and ?L
        unfolding trail_pol_def A A2 ann_lits_split_reasons_def isasat_input_bounded_def
          isa_vmtf_def vmtf_def distinct_atoms_rel_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def atms_of_def
          distinct_hash_atoms_rel_def
          atoms_hash_rel_def A A2 A3 C option_lookup_clause_rel_def
          lookup_clause_rel_def phase_saving_def cach_refinement_empty_def
          cach_refinement_def heuristic_rel_def
          cach_refinement_list_def vdom_m_def
          isasat_input_bounded_def
          isasat_input_nempty_def cach_refinement_nonull_def
        unfolding trail_pol_def[symmetric] ann_lits_split_reasons_def[symmetric]
          isasat_input_bounded_def[symmetric]
          vmtf_def[symmetric]
          isa_vmtf_def[symmetric]
          distinct_atoms_rel_def[symmetric]
          vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def[symmetric] atms_of_def[symmetric]
          distinct_hash_atoms_rel_def[symmetric]
          atoms_hash_rel_def[symmetric]
          option_lookup_clause_rel_def[symmetric]
          lookup_clause_rel_def[symmetric]
          phase_saving_def[symmetric] cach_refinement_empty_def[symmetric]
          cach_refinement_def[symmetric] cach_refinement_nonull_def[symmetric]
          cach_refinement_list_def[symmetric]
          vdom_m_def[symmetric]
          isasat_input_bounded_def[symmetric]
          isasat_input_nempty_def[symmetric]
          heuristic_rel_def[symmetric]
        apply auto
        done
      show ?K
        using that
        by (auto simp: vdom_m_simps5 vdom_m_def)
    qed

    have arena_le: \<open>length arena + header_size C + length C \<le> 6 + r + uint32_max div 2\<close>
      using r r' le_C_ge by (auto simp: uint32_max_def header_size_def S' U)
    have vm: \<open>vm \<in> isa_vmtf (all_atms N (NE + UE)) M1 \<Longrightarrow>
       vm \<in> isa_vmtf (all_atms N (NE + UE)) (Propagated (- lit_of (hd M)) x2a # M1)\<close> for x2a vm
      by (cases vm)
        (auto intro!: vmtf_consD simp: isa_vmtf_def)
    then show ?thesis
      supply [[goals_limit=1]]
      using empty_cach n_d_M1 C_L' W'W outl vmtf undef \<open>1 < length C\<close> lits
        uM_\<L>\<^sub>a\<^sub>l\<^sub>l vdom lcount vdom_m dist_vdom heur
      apply (subst propagate_bt_wl_D_alt_def)
      unfolding U U' H get_fresh_index_wl_def prod.case
        propagate_bt_wl_D_heur_alt_def rescore_clause_def
      apply (rewrite in \<open>let _ = _!1 in _\<close> Let_def)
      apply (rewrite in \<open>let _ = update_lbd _ _ _ in _\<close> Let_def)
      apply (rewrite in \<open>let _ = list_update _ (nat_of_lit _) _ in _\<close> Let_def)
      apply (rewrite in \<open>let _ = list_update _ (nat_of_lit _) _ in _\<close> Let_def)
      apply (rewrite in \<open>let _ = False in _\<close> Let_def)
      apply (refine_rcg cons_trail_Propagated_tr2[of _ _ _ _ _ _ \<open>all_atms_st U'\<close>])
      subgoal using valid by (auto dest!: valid_arena_vdom_subset)
      subgoal  using valid size_mset_mono[OF avdom] by (auto dest!: valid_arena_vdom_subset)
      subgoal using \<open>nat_of_lit (C ! Suc 0) < length W'\<close> by simp
      subgoal using \<open>nat_of_lit (- lit_of (hd (get_trail_wl S'))) < length W'\<close>
        by (simp add: S' lit_of_hd_trail_def)
      subgoal using le_C_ge .
      subgoal by (auto simp: append_and_length_fast_code_pre_def isasat_fast_def
        sint64_max_def uint32_max_def)
      subgoal
        using D' C_1_neq_hd vmtf avdom M1'_M1 size_learned_clss_dom_m[of N] valid_arena_size_dom_m_le_arena[OF valid]
        by (auto simp: propagate_bt_wl_D_heur_def twl_st_heur_def lit_of_hd_trail_st_heur_def
            phase_saving_def atms_of_def S' U' lit_of_hd_trail_def all_atms_def[symmetric] isasat_fast_def
            sint64_max_def uint32_max_def)
      subgoal for x uu x1 x2 vm uua_ glue uub D'' xa x' x1a x2a
        by (auto simp: update_lbd_pre_def arena_is_valid_clause_idx_def)
      subgoal using length_watched_le[of S' S \<open>-lit_of_hd_trail M\<close>] corr SS' uM_\<L>\<^sub>a\<^sub>l\<^sub>l W'_eq S_arena
         by (auto simp: isasat_fast_def length_ll_def S' U lit_of_hd_trail_def simp flip: all_atms_def)
      subgoal using length_watched_le[of S' S \<open>C ! Suc 0\<close>] corr SS' W'_eq S_arena C_1_neq_hd C_Suc1_in
         by (auto simp: length_ll_def S' U lit_of_hd_trail_def isasat_fast_def simp flip: all_atms_def)
      subgoal
        using M1'_M1 by (rule isa_length_trail_pre)
      subgoal using D' C_1_neq_hd vmtf avdom
        by (auto simp: DECISION_REASON_def
            dest: valid_arena_one_notin_vdomD
            intro!: vm)
      subgoal
        using M1'_M1
        by (rule cons_trail_Propagated_tr_pre)
          (use undef uM_\<L>\<^sub>a\<^sub>l\<^sub>l in \<open>auto simp: lit_of_hd_trail_def S' U' all_atms_def[symmetric]\<close>)
      subgoal using M1'_M1 by (auto simp: lit_of_hd_trail_def S' U' all_atms_def[symmetric])
      subgoal using uM_\<L>\<^sub>a\<^sub>l\<^sub>l by (auto simp: S' U' uminus_\<A>\<^sub>i\<^sub>n_iff lit_of_hd_trail_def)
      subgoal
        using D' C_1_neq_hd vmtf avdom
        by (auto simp: propagate_bt_wl_D_heur_def twl_st_heur_def lit_of_hd_trail_st_heur_def
            intro!: ASSERT_refine_left ASSERT_leI RES_refine exI[of _ C] valid_arena_update_lbd
            dest: valid_arena_one_notin_vdomD
            intro!: vm)
      apply assumption
      subgoal
        using D' C_1_neq_hd vmtf avdom M1'_M1
        by (auto simp: propagate_bt_wl_D_heur_def twl_st_heur_def lit_of_hd_trail_st_heur_def
            phase_saving_def atms_of_def S' U' lit_of_hd_trail_def all_atms_def[symmetric])
      subgoal
        supply All_atms_rew[simp]
        unfolding twl_st_heur_def
        using D' C_1_neq_hd vmtf avdom M1'_M1 bounded nempty r arena_le
        by (clarsimp simp add: propagate_bt_wl_D_heur_def twl_st_heur_def
            Let_def T' U' U rescore_clause_def S' map_fun_rel_def
            list_of_mset2_def vmtf_flush_def RES_RES2_RETURN_RES RES_RETURN_RES \<phi> uminus_\<A>\<^sub>i\<^sub>n_iff
            get_fresh_index_def RES_RETURN_RES2 RES_RES_RETURN_RES2 lit_of_hd_trail_def
            RES_RES_RETURN_RES lbd_empty_def get_LBD_def DECISION_REASON_def
            all_atms_def[symmetric] All_atms_rew
            intro!: valid_arena_update_lbd
            simp del: isasat_input_bounded_def isasat_input_nempty_def
            dest: valid_arena_one_notin_vdomD)
           (intro conjI, clarsimp_all
            intro!: valid_arena_update_lbd
            simp del: isasat_input_bounded_def isasat_input_nempty_def
            dest: valid_arena_one_notin_vdomD, auto simp: 
            dest: valid_arena_one_notin_vdomD
            simp del: isasat_input_bounded_def isasat_input_nempty_def)
      done
  qed

  have propagate_unit_bt_wl_D_int: \<open>propagate_unit_bt_wl_D_int LK U
      \<le> \<Down> ?S
          (propagate_unit_bt_wl LK' U')\<close>
    if
      SS': \<open>(S, S') \<in> ?R\<close> and
      \<open>backtrack_wl_inv S'\<close> and
      \<open>backtrack_wl_D_heur_inv S\<close> and
      \<open>(TnC, T') \<in> ?shorter S' S\<close> and
      [simp]: \<open>nC = (n, C)\<close> and
      [simp]: \<open>TnC = (T, nC)\<close> and
      find_decomp: \<open>(U, U') \<in> ?find_decomp S T' n\<close> and
      \<open>\<not> 1 < length C\<close> and
      \<open>\<not> 1 < size (the (get_conflict_wl U'))\<close> and
      KK': \<open>(LK, LK') \<in> {(L, L'). L = L' \<and> L = lit_of (hd (get_trail_wl S'))}\<close>
    for S S' TnC T' T nC n C U U' LK LK'
  proof -
    have
      TT': \<open>(T, del_conflict_wl T') \<in> twl_st_heur_bt\<close> and
      n: \<open>n = get_maximum_level (get_trail_wl T')
          (remove1_mset (- lit_of (hd (get_trail_wl T'))) (mset C))\<close> and
      T_C: \<open>get_conflict_wl T' = Some (mset C)\<close> and
      T'S': \<open>equality_except_conflict_wl T' S'\<close> and
      \<open>C \<noteq> []\<close> and
      hd_C: \<open>hd C = - lit_of (hd (get_trail_wl T'))\<close> and
      incl: \<open>mset C \<subseteq># the (get_conflict_wl S')\<close> and
      dist_S': \<open>distinct_mset (the (get_conflict_wl S'))\<close> and
      list_confl_S': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S') (the (get_conflict_wl S'))\<close> and
      \<open>get_conflict_wl S' \<noteq> None\<close> and
      \<open>C \<noteq> []\<close> and
      uL_M: \<open>- lit_of (hd (get_trail_wl S')) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S')\<close> and
      tr_nempty: \<open>get_trail_wl T' \<noteq> []\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close>  \<open>~1 < length C\<close>
      by (auto)
    obtain K M2 where
      UU': \<open>(U, U') \<in> twl_st_heur_bt\<close> and
      U'U': \<open>equality_except_trail_wl U' T'\<close> and
      lev_K: \<open>get_level (get_trail_wl T') K = Suc (get_maximum_level (get_trail_wl T')
           (remove1_mset (- lit_of (hd (get_trail_wl T')))
             (the (get_conflict_wl T'))))\<close> and
      decomp: \<open>(Decided K # get_trail_wl U', M2) \<in> set (get_all_ann_decomposition (get_trail_wl T'))\<close> and
      r: \<open>length (get_clauses_wl_heur S) = r\<close>
      using find_decomp SS'
      by (auto)

    obtain M N NE UE NS US Q W where
      T': \<open>T' = (M, N, Some (mset C), NE, UE, NS, US, Q, W)\<close>
      using TT' T_C \<open>\<not>1 < length C\<close>
      apply (cases T'; cases S')
      by (auto simp: find_lit_of_max_level_wl_def)
    obtain D' where
      S': \<open>S' = (M, N, D', NE, UE, NS, US, Q, W)\<close>
      using T'S'
      apply (cases S')
      by (auto simp: find_lit_of_max_level_wl_def T' del_conflict_wl_def)

    obtain M1 where
      U': \<open>U' = (M1, N, Some (mset C), NE, UE, NS, US, Q, W)\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> find_decomp
      apply (cases U')
      by (auto simp: find_lit_of_max_level_wl_def T')
    have [simp]:
       \<open>LK' = lit_of (hd (get_trail_wl T'))\<close>
       \<open>LK = LK'\<close>
       using KK' SS' S' by (auto simp: T')
    obtain vm' W' \<phi> clvls cach lbd outl stats heur vdom avdom lcount arena D' Q' opts
      M1'
      where
        U: \<open>U = (M1', arena, D', Q', W', vm', \<phi>, clvls, cach, lbd, outl, stats, heur,
           vdom, avdom, lcount, opts, [])\<close> and
        avdom: \<open>mset avdom \<subseteq># mset vdom\<close> and
        r': \<open>length (get_clauses_wl_heur U) = r\<close>
      using UU' find_decomp r by (cases U) (auto simp: U' T' twl_st_heur_bt_def)
    have
      M'M: \<open>(M1', M1) \<in> trail_pol (all_atms_st U')\<close> and
      W'W: \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0  (all_atms_st U'))\<close> and
      vmtf: \<open>vm' \<in> isa_vmtf  (all_atms_st U') M1\<close> and
      \<phi>: \<open>phase_saving  (all_atms_st U') \<phi>\<close> and
      n_d_M1: \<open>no_dup M1\<close> and
      empty_cach: \<open>cach_refinement_empty  (all_atms_st U') cach\<close> and
      \<open>length outl = Suc 0\<close> and
      outl: \<open>out_learned M1 None outl\<close> and
      lcount: \<open>lcount = size (learned_clss_l N)\<close> and
      vdom: \<open>vdom_m (all_atms_st U') W N \<subseteq> set vdom\<close> and
      valid: \<open>valid_arena arena N (set vdom)\<close> and
      D': \<open>(D', None) \<in> option_lookup_clause_rel (all_atms_st U')\<close> and
      bounded: \<open>isasat_input_bounded (all_atms_st U')\<close> and
      nempty: \<open>isasat_input_nempty (all_atms_st U')\<close> and
      dist_vdom: \<open>distinct vdom\<close> and
      heur: \<open>heuristic_rel (all_atms_st U') heur\<close>
      using UU' by (auto simp: out_learned_def twl_st_heur_bt_def U U' all_atms_def[symmetric])
    have [simp]: \<open>C ! 0 = - lit_of (hd M)\<close> and
      n_d: \<open>no_dup M\<close>
      using SS' hd_C \<open>C \<noteq> []\<close> by (auto simp: S' U' T' twl_st_heur_conflict_ana_def hd_conv_nth)
    have undef: \<open>undefined_lit M1 (lit_of (hd M))\<close>
      using decomp n_d
      by (auto dest!: get_all_ann_decomposition_exists_prepend simp: T' hd_append U' neq_Nil_conv
          split: if_splits)
    have C: \<open>C = [- lit_of (hd M)]\<close>
      using \<open>C \<noteq> []\<close> \<open>C ! 0 = - lit_of (hd M)\<close> \<open>\<not>1 < length C\<close>
      by (cases C) (auto simp del: \<open>C ! 0 = - lit_of (hd M)\<close>)
    have propagate_unit_bt_wl_alt_def:
      \<open>propagate_unit_bt_wl = (\<lambda>L (M, N, D, NE, UE, NS, US, Q, W). do {
        ASSERT(L \<in># all_lits_st (M, N, D, NE, UE, NS, US, Q, W));
        ASSERT(propagate_unit_bt_wl_pre L (M, N, D, NE, UE, NS, US, Q, W));
	_ \<leftarrow> RETURN ();
	_ \<leftarrow> RETURN ();
	_ \<leftarrow> RETURN ();
	_ \<leftarrow> RETURN ();
	M \<leftarrow> cons_trail_propagate_l (-L) 0 M;
        RETURN (M, N, None, NE, add_mset (the D) UE, NS, US, {#L#}, W)
      })\<close>
      unfolding propagate_unit_bt_wl_def Let_def by (auto intro!: ext bind_cong[OF refl]
       simp: propagate_unit_bt_wl_pre_def propagate_unit_bt_l_pre_def
         single_of_mset_def RES_RETURN_RES image_iff)

    have [refine0]:
      \<open>lbd_empty lbd \<le> SPEC (\<lambda>c. (c, ()) \<in> {(c, _). c = replicate (length lbd) False})\<close>
      by (auto simp: lbd_empty_def)
    have [refine0]: \<open>(isa_length_trail M1', ()) \<in> {(j, _). j = length M1}\<close>
      by (subst isa_length_trail_length_u[THEN fref_to_Down_unRET_Id, OF _ M'M]) auto

    have [refine0]: \<open>isa_vmtf_flush_int M1' vm' \<le>
         SPEC(\<lambda>c. (c, ()) \<in> {(vm', _). vm' \<in> isa_vmtf (all_atms_st U') M1})\<close>
      for vm i L
    proof -
      obtain vm0 where
        vm: \<open>(vm', vm0) \<in> Id \<times>\<^sub>r distinct_atoms_rel (all_atms_st U')\<close> and
        vm0: \<open>vm0 \<in> vmtf (all_atms_st U') M1\<close>
        using vmtf unfolding isa_vmtf_def by (cases vm') auto
      show ?thesis
        apply (rule order.trans)
        apply (rule isa_vmtf_flush_int[THEN fref_to_Down_curry, of _ _ M1 vm'])
        apply ((solves \<open>use M'M in auto\<close>)+)[2]
        apply (subst Down_id_eq)
        apply (rule order.trans)
        apply (rule vmtf_change_to_remove_order'[THEN fref_to_Down_curry, of \<open>all_atms_st U'\<close> M1 vm0 M1 vm'])
        subgoal using vm0 bounded nempty by auto
        subgoal using vm by auto
        subgoal by (auto simp: vmtf_flush_def conc_fun_RES RETURN_def intro: isa_vmtfI)
        done
    qed
    have [refine0]: \<open>get_LBD lbd \<le> SPEC(\<lambda>c. (c, ()) \<in> UNIV)\<close>
      by (auto simp: get_LBD_def)

    have tr_S: \<open>(get_trail_wl_heur S, M) \<in> trail_pol (all_atms_st S')\<close>
      using SS' by (auto simp: S' twl_st_heur_conflict_ana_def all_atms_def)

    have hd_SM: \<open>lit_of_last_trail_pol (get_trail_wl_heur S) = lit_of (hd M)\<close>
      unfolding lit_of_hd_trail_def lit_of_hd_trail_st_heur_def
      by (subst lit_of_last_trail_pol_lit_of_last_trail[THEN fref_to_Down_unRET_Id])
        (use M'M tr_S tr_nempty in \<open>auto simp: lit_of_hd_trail_def T' S'\<close>)
    have uL_M: \<open>- lit_of (hd (get_trail_wl S')) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st U')\<close>
      using uL_M by (simp add: S' U')
    let ?NE = \<open>add_mset {#- lit_of (hd M)#} (NE + UE + NS + US)\<close>
    have All_atms_rew: \<open>set_mset (all_atms (N) (?NE)) =
        set_mset (all_atms N (NE + UE + NS + US))\<close> (is ?A)
      \<open>trail_pol (all_atms (N) (?NE)) =
        trail_pol (all_atms N (NE + UE + NS + US))\<close> (is ?B)
      \<open>isa_vmtf (all_atms (N) (?NE)) =
        isa_vmtf (all_atms N (NE + UE + NS + US))\<close> (is ?C)
      \<open>option_lookup_clause_rel  (all_atms (N) (?NE)) =
        option_lookup_clause_rel (all_atms N (NE + UE + NS + US))\<close> (is ?D)
      \<open>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms (N) (?NE))) =
         \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms N (NE + UE + NS + US)))\<close> (is ?E)
      \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms (N) (?NE))) =
        set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N (NE + UE + NS + US)))\<close>
      \<open>phase_saving ((all_atms (N) (?NE))) =
        phase_saving ((all_atms N (NE + UE + NS + US)))\<close> (is ?F)
      \<open>cach_refinement_empty ((all_atms (N) (?NE))) =
        cach_refinement_empty ((all_atms N (NE + UE + NS + US)))\<close> (is ?G)
      \<open>vdom_m ((all_atms (N) (?NE))) =
        vdom_m ((all_atms N (NE + UE + NS + US)))\<close> (is ?H)
      \<open>isasat_input_bounded ((all_atms (N) (?NE))) =
        isasat_input_bounded ((all_atms N (NE + UE + NS + US)))\<close> (is ?I)
      \<open>isasat_input_nempty ((all_atms (N) (?NE))) =
        isasat_input_nempty ((all_atms N (NE + UE + NS + US)))\<close> (is ?J)
      \<open>vdom_m (all_atms N ?NE) W (N) =
        (vdom_m (all_atms N (NE + UE + NS + US)) W N)\<close> (is ?K)
      \<open>heuristic_rel ((all_atms (N) (?NE))) =
        heuristic_rel ((all_atms N (NE + UE + NS + US)))\<close> (is ?L)
      for b x' C'
    proof -
      show A: ?A
        using  uL_M
        apply (cases \<open>hd M\<close>)
        by (auto simp: all_atms_def all_lits_def ran_m_mapsto_upd_notin all_lits_of_mm_add_mset
            U' S'  in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n literals_are_in_\<L>\<^sub>i\<^sub>n_def atm_of_eq_atm_of
            all_lits_of_m_add_mset ac_simps lits_of_def)
      have  A2: \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N (?NE))) =
        set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N (NE + UE + NS + US)))\<close>
        using A unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_def C by (auto simp: A)
      then show \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms (N) (?NE))) =
        set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N (NE + UE + NS + US)))\<close>
        using A unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_def C by (auto simp: A)
      have A3: \<open>set_mset (all_atms N (?NE)) =
        set_mset (all_atms N (NE + UE + NS + US))\<close>
        using A unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_def C by (auto simp: A)

      show ?B and ?C and ?D and ?E and ?F and ?G and ?H and ?I and ?J and ?K and ?L
        unfolding trail_pol_def A A2 ann_lits_split_reasons_def isasat_input_bounded_def
          isa_vmtf_def vmtf_def distinct_atoms_rel_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def atms_of_def
          distinct_hash_atoms_rel_def
          atoms_hash_rel_def A A2 A3 C option_lookup_clause_rel_def
          lookup_clause_rel_def phase_saving_def cach_refinement_empty_def
          cach_refinement_def
          cach_refinement_list_def vdom_m_def
          isasat_input_bounded_def heuristic_rel_def
          isasat_input_nempty_def cach_refinement_nonull_def vdom_m_def
        unfolding trail_pol_def[symmetric] ann_lits_split_reasons_def[symmetric]
          isasat_input_bounded_def[symmetric]
          vmtf_def[symmetric]
          isa_vmtf_def[symmetric]
          distinct_atoms_rel_def[symmetric]
          vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def[symmetric] atms_of_def[symmetric]
          distinct_hash_atoms_rel_def[symmetric]
          atoms_hash_rel_def[symmetric]
          option_lookup_clause_rel_def[symmetric]
          lookup_clause_rel_def[symmetric]
          phase_saving_def[symmetric] cach_refinement_empty_def[symmetric]
          cach_refinement_def[symmetric]
          cach_refinement_list_def[symmetric]
          vdom_m_def[symmetric]
          isasat_input_bounded_def[symmetric] cach_refinement_nonull_def[symmetric]
          isasat_input_nempty_def[symmetric] heuristic_rel_def[symmetric]
        apply auto
        done
    qed

    show ?thesis
      using empty_cach n_d_M1 W'W outl vmtf C \<phi> undef uL_M vdom lcount valid D' avdom
      unfolding U U' propagate_unit_bt_wl_D_int_def prod.simps hd_SM
        propagate_unit_bt_wl_alt_def
      apply (rewrite at \<open>let _ = incr_uset _ in _\<close> Let_def)
      apply (refine_rcg cons_trail_Propagated_tr2[where \<A> = \<open>all_atms_st U'\<close>])
      subgoal using M'M by (rule isa_length_trail_pre)
      subgoal by (auto simp: DECISION_REASON_def)
      subgoal
        using M'M by (rule cons_trail_Propagated_tr_pre)
           (use undef uL_M in \<open>auto simp: hd_SM all_atms_def[symmetric] T'
	    lit_of_hd_trail_def S'\<close>)
     subgoal
       using M'M by (auto simp: U U' lit_of_hd_trail_st_heur_def RETURN_def
           single_of_mset_def vmtf_flush_def twl_st_heur_def lbd_empty_def get_LBD_def
           RES_RES2_RETURN_RES RES_RETURN_RES S' uminus_\<A>\<^sub>i\<^sub>n_iff RES_RES_RETURN_RES
           DECISION_REASON_def hd_SM lit_of_hd_trail_st_heur_def
           intro!: ASSERT_refine_left RES_refine exI[of _ \<open>-lit_of (hd M)\<close>]
           intro!: vmtf_consD
           simp del: isasat_input_bounded_def isasat_input_nempty_def)
     subgoal
       by (auto simp: U U' lit_of_hd_trail_st_heur_def RETURN_def
           single_of_mset_def vmtf_flush_def twl_st_heur_def lbd_empty_def get_LBD_def
           RES_RES2_RETURN_RES RES_RETURN_RES S' uminus_\<A>\<^sub>i\<^sub>n_iff RES_RES_RETURN_RES
           DECISION_REASON_def hd_SM T'
           intro!: ASSERT_refine_left RES_refine exI[of _ \<open>-lit_of (hd M)\<close>]
           intro!: vmtf_consD
           simp del: isasat_input_bounded_def isasat_input_nempty_def)
     subgoal
       using bounded nempty dist_vdom r' heur
       by (auto simp: U U' lit_of_hd_trail_st_heur_def RETURN_def
           single_of_mset_def vmtf_flush_def twl_st_heur_def lbd_empty_def get_LBD_def
           RES_RES2_RETURN_RES RES_RETURN_RES S' uminus_\<A>\<^sub>i\<^sub>n_iff RES_RES_RETURN_RES
           DECISION_REASON_def hd_SM All_atms_rew all_atms_def[symmetric]
           intro!: ASSERT_refine_left RES_refine exI[of _ \<open>-lit_of (hd M)\<close>]
           intro!: isa_vmtf_consD2
           simp del: isasat_input_bounded_def isasat_input_nempty_def)
       done
  qed

  have trail_nempty: \<open>fst (get_trail_wl_heur S) \<noteq> []\<close>
    if
      \<open>(S, S') \<in> ?R\<close> and
      \<open>backtrack_wl_inv S'\<close>
    for S S'
  proof -
    show ?thesis
      using that unfolding backtrack_wl_inv_def backtrack_wl_D_heur_inv_def backtrack_l_inv_def backtrack_inv_def
        backtrack_l_inv_def apply -
      by normalize_goal+
        (auto simp:  twl_st_heur_conflict_ana_def trail_pol_def ann_lits_split_reasons_def)
  qed


  have [refine]: \<open>\<And>x y. (x, y)
          \<in> {(S, T).
             (S, T) \<in> twl_st_heur_conflict_ana \<and>
             length (get_clauses_wl_heur S) = r} \<Longrightarrow>
          lit_of_hd_trail_st_heur x
          \<le> \<Down> {(L, L'). L = L' \<and> L = lit_of (hd (get_trail_wl y))} (mop_lit_hd_trail_wl y)\<close>
    unfolding mop_lit_hd_trail_wl_def lit_of_hd_trail_st_heur_def
    apply refine_rcg
    subgoal unfolding mop_lit_hd_trail_wl_pre_def mop_lit_hd_trail_l_pre_def mop_lit_hd_trail_pre_def
     by (auto simp:  twl_st_heur_conflict_ana_def mop_lit_hd_trail_wl_pre_def mop_lit_hd_trail_l_pre_def trail_pol_alt_def
           mop_lit_hd_trail_pre_def state_wl_l_def twl_st_l_def lit_of_hd_trail_def RETURN_RES_refine_iff)
    subgoal for  x y
      apply simp_all
      by (subst lit_of_last_trail_pol_lit_of_last_trail[THEN fref_to_Down_unRET_Id, of \<open>get_trail_wl y\<close> \<open>get_trail_wl_heur x\<close> \<open>all_atms_st y\<close>])
        (auto simp:  twl_st_heur_conflict_ana_def mop_lit_hd_trail_wl_pre_def mop_lit_hd_trail_l_pre_def
           mop_lit_hd_trail_pre_def state_wl_l_def twl_st_l_def lit_of_hd_trail_def RETURN_RES_refine_iff)
    done
  show ?thesis
    supply [[goals_limit=1]]
    apply (intro frefI nres_relI)
    unfolding backtrack_wl_D_nlit_heur_alt_def backtrack_wl_def
    apply (refine_rcg shorter)
    subgoal by (rule inv)
    subgoal by (rule trail_nempty)
    subgoal for x y xa S x1 x2 x1a x2a
      by (auto simp: twl_st_heur_state_simp equality_except_conflict_wl_get_clauses_wl)
    apply (rule find_decomp_wl_nlit; assumption)
    subgoal by (auto simp: twl_st_heur_state_simp equality_except_conflict_wl_get_clauses_wl
          equality_except_trail_wl_get_clauses_wl)
    subgoal for x y L La xa S x1 x2 x1a x2a Sa Sb
      by (auto simp: twl_st_heur_state_simp equality_except_trail_wl_get_conflict_wl)
    apply (rule fst_find_lit_of_max_level_wl; solves assumption)
    apply (rule propagate_bt_wl_D_heur; assumption)
    apply (rule propagate_unit_bt_wl_D_int; assumption)
    done
qed


subsubsection \<open>Backtrack with direct extraction of literal if highest level\<close>

lemma le_uint32_max_div_2_le_uint32_max: \<open>a \<le> uint32_max div 2 + 1 \<Longrightarrow> a \<le> uint32_max\<close>
  by (auto simp: uint32_max_def sint64_max_def)


lemma propagate_bt_wl_D_heur_alt_def:
  \<open>propagate_bt_wl_D_heur = (\<lambda>L C (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
         vdom, avdom, lcount, opts). do {
      ASSERT(length vdom \<le> length N0);
      ASSERT(length avdom \<le> length N0);
      ASSERT(nat_of_lit (C!1) < length W0 \<and> nat_of_lit (-L) < length W0);
      ASSERT(length C > 1);
      let L' = C!1;
      ASSERT(length C \<le> uint32_max div 2 + 1);
      (vm, \<phi>) \<leftarrow> isa_vmtf_rescore C M vm0 \<phi>0;
      glue \<leftarrow> get_LBD lbd;
      let b = False;
      let b' = (length C = 2);
      ASSERT(isasat_fast (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
         vdom, avdom, lcount, opts) \<longrightarrow> append_and_length_fast_code_pre ((b, C), N0));
      ASSERT(isasat_fast (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
         vdom, avdom, lcount, opts) \<longrightarrow> lcount < sint64_max);
      (N, i) \<leftarrow> fm_add_new_fast b C N0;
      ASSERT(update_lbd_pre ((i, glue), N));
      let N = update_lbd i glue N;
      ASSERT(isasat_fast (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
         vdom, avdom, lcount, opts) \<longrightarrow> length_ll W0 (nat_of_lit (-L)) < sint64_max);
      let W = W0[nat_of_lit (- L) := W0 ! nat_of_lit (- L) @ [(i, L', b')]];
      ASSERT(isasat_fast (M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, heur,
         vdom, avdom, lcount, opts) \<longrightarrow> length_ll W (nat_of_lit L') < sint64_max);
      let W = W[nat_of_lit L' := W!nat_of_lit L' @ [(i, -L, b')]];
      lbd \<leftarrow> lbd_empty lbd;
      ASSERT(isa_length_trail_pre M);
      let j = isa_length_trail M;
      ASSERT(i \<noteq> DECISION_REASON);
      ASSERT(cons_trail_Propagated_tr_pre ((-L, i), M));
      M \<leftarrow> cons_trail_Propagated_tr (- L) i M;
      vm \<leftarrow> isa_vmtf_flush_int M vm;
      ASSERT(atm_of L < length \<phi>);
      RETURN (M, N, D, j, W, vm, save_phase (-L) \<phi>, 0,
         cach, lbd, outl, add_lbd (of_nat glue) stats, update_heuristics glue heur, vdom @ [i],
          avdom @ [i],
          lcount + 1, opts)
    })\<close>
  unfolding propagate_bt_wl_D_heur_def Let_def by (auto intro!: ext)


lemma propagate_bt_wl_D_fast_code_isasat_fastI2: \<open>isasat_fast b \<Longrightarrow>
       b = (a1', a2') \<Longrightarrow>
       a2' = (a1'a, a2'a) \<Longrightarrow>
       a < length a1'a \<Longrightarrow> a \<le> sint64_max\<close>
  by (cases b) (auto simp: isasat_fast_def)

lemma propagate_bt_wl_D_fast_code_isasat_fastI3: \<open>isasat_fast b \<Longrightarrow>
       b = (a1', a2') \<Longrightarrow>
       a2' = (a1'a, a2'a) \<Longrightarrow>
       a \<le> length a1'a \<Longrightarrow> a < sint64_max\<close>
  by (cases b) (auto simp: isasat_fast_def sint64_max_def uint32_max_def)

lemma lit_of_hd_trail_st_heur_alt_def:
  \<open>lit_of_hd_trail_st_heur = (\<lambda>(M, N, D, Q, W, vm, \<phi>). do {ASSERT (fst M \<noteq> []); RETURN (lit_of_last_trail_pol M)})\<close>
  by (auto simp: lit_of_hd_trail_st_heur_def lit_of_hd_trail_def intro!: ext)

end
