theory IsaSAT_Backtrack
  imports IsaSAT_Setup Watched_Literals_Heuristics IsaSAT_VMTF
begin
subsection \<open>Backtrack\<close>
(* TODO Move *)
lemma (in -)bex_lessI: "P j \<Longrightarrow> j < n \<Longrightarrow> \<exists>j<n. P j"
  by auto

lemma (in -)bex_gtI: "P j \<Longrightarrow> j > n \<Longrightarrow> \<exists>j>n. P j"
  by auto

lemma (in -)bex_geI: "P j \<Longrightarrow> j \<ge> n \<Longrightarrow> \<exists>j\<ge>n. P j"
  by auto

lemma swap_only_first_relevant:
  \<open>b \<ge> i \<Longrightarrow> a < length xs  \<Longrightarrow>take i (swap xs a b) = take i (xs[a := xs ! b])\<close>
  by (auto simp: swap_def)

lemma get_maximum_level_remove_non_max_lvl:
   \<open>get_level M a < get_maximum_level M D \<Longrightarrow> 
  get_maximum_level M (remove1_mset a D) = get_maximum_level M D\<close>
  by (cases \<open>a \<in># D\<close>)
    (auto dest!: multi_member_split simp: get_maximum_level_add_mset)
(* End Move *)

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

definition (in isasat_input_ops) empty_conflict_and_extract_clause_heur_inv where
  \<open>empty_conflict_and_extract_clause_heur_inv M outl = (\<lambda>(E, C, i). mset (take i C) = mset (take i outl) \<and> 
            length C = length outl \<and> C ! 0 = outl ! 0 \<and> i \<ge> 1 \<and> i \<le> length outl \<and>
            (1 < length (take i C) \<longrightarrow>
                 highest_lit M (mset (tl (take i C)))
                  (Some (C ! 1, get_level M (C ! 1)))))\<close>

definition (in isasat_input_ops) empty_conflict_and_extract_clause_heur ::
    "(nat, nat) ann_lits
     \<Rightarrow> lookup_clause_rel
       \<Rightarrow> nat literal list \<Rightarrow> (_ \<times> nat literal list \<times> nat) nres" 
where
  \<open>empty_conflict_and_extract_clause_heur M D outl = do {
     let C = replicate (length outl) (outl!0);
     (D, C, _) \<leftarrow> WHILE\<^sub>T\<^bsup>empty_conflict_and_extract_clause_heur_inv M outl\<^esup>
         (\<lambda>(D, C, i). i < length_u outl)
         (\<lambda>(D, C, i). do {
           ASSERT(i < length outl);
           ASSERT(i < length C);
           ASSERT(lookup_conflict_remove1_pre (outl ! i, D));
           let D = lookup_conflict_remove1 (outl ! i) D;
           let C = C[i := outl ! i];
           ASSERT(C!i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> C!1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> 1 < length C);
           let C = (if get_level M (C!i) > get_level M (C!one_uint32_nat) then swap C one_uint32_nat i else C);
           ASSERT(i+1 \<le> uint_max);
           RETURN (D, C, i+one_uint32_nat)
         })
        (D, C, one_uint32_nat);
     ASSERT(length outl \<noteq> 1 \<longrightarrow> length C > 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow> C!1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
     RETURN ((True, D), C, if length outl = 1 then zero_uint32_nat else get_level M (C!1))
    }\<close>

lemma empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause:
  assumes
    D: \<open>D = mset (tl outl)\<close> and
    outl: \<open>outl \<noteq> []\<close> and
    dist: \<open>distinct outl\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset outl)\<close> and
    DD': \<open>(D', D) \<in> lookup_clause_rel\<close> and
     consistent: \<open>\<not> tautology (mset outl)\<close> 
  shows
    \<open>empty_conflict_and_extract_clause_heur M D' outl \<le> \<Down> (option_lookup_clause_rel \<times>\<^sub>r Id \<times>\<^sub>r Id)
        (empty_conflict_and_extract_clause M D outl)\<close>
proof -
  have size_out: \<open>size (mset outl) \<le> 1 + uint_max div 2\<close>
    using simple_clss_size_upper_div2[OF lits _ consistent]
      \<open>distinct outl\<close> by auto
      thm empty_conflict_and_extract_clause_def[of M D outl]
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
       (E, D - mset (take i outl)) \<in> lookup_clause_rel \<and>
            length C = length outl \<and> C ! 0 = outl ! 0 \<and> i \<ge> 1 \<and> i \<le> length outl \<and>
            (1 < length (take i C) \<longrightarrow>
                 highest_lit M (mset (tl (take i C)))
                  (Some (C ! 1, get_level M (C ! 1))))\<close>
  have I0: \<open>I (D', replicate (length outl) (outl ! 0), one_uint32_nat)\<close>
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
     (D', replicate (length outl) (outl ! 0), one_uint32_nat)\<close>
    using assms
    unfolding empty_conflict_and_extract_clause_heur_inv_def
    by (cases outl) auto
  have I0: \<open>I (D', replicate (length outl) (outl ! 0), one_uint32_nat)\<close>
    using assms
    unfolding I_def
    by (cases outl) auto
  have
     C1_L: \<open>aa[ba := outl ! ba] ! 1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> (is ?A1inL) and
     ba_le:  \<open>ba + 1 \<le> uint_max\<close> (is ?ba_le) and
     I_rec: \<open>I (lookup_conflict_remove1 (outl ! ba) a,
          if get_level M (aa[ba := outl ! ba] ! one_uint32_nat)
             < get_level M (aa[ba := outl ! ba] ! ba)
          then swap (aa[ba := outl ! ba]) one_uint32_nat ba
          else aa[ba := outl ! ba],
          ba + one_uint32_nat)\<close> (is ?I) and
      inv: \<open>empty_conflict_and_extract_clause_heur_inv M outl
        (lookup_conflict_remove1 (outl ! ba) a,
         if get_level M (aa[ba := outl ! ba] ! one_uint32_nat)
            < get_level M (aa[ba := outl ! ba] ! ba)
         then swap (aa[ba := outl ! ba]) one_uint32_nat ba
         else aa[ba := outl ! ba],
         ba + one_uint32_nat)\<close> (is ?inv)
    if 
      \<open>empty_conflict_and_extract_clause_heur_inv M outl s\<close> and
      I: \<open>I s\<close> and
      \<open>case s of (D, C, i) \<Rightarrow> i < length_u outl\<close> and
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
      aD: \<open>(a, D - mset (take ba outl)) \<in> lookup_clause_rel\<close> and
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
      using literals_are_in_\<L>\<^sub>i\<^sub>n_in_mset_\<L>\<^sub>a\<^sub>l\<^sub>l lits by auto
    
    define aa2 where \<open>aa2 \<equiv> tl (tl (take ba aa))\<close>
    have tl_take_nth_con:  \<open>tl (take ba aa) = aa ! Suc 0 # aa2\<close> if \<open>ba > Suc 0\<close>
      using ba_le ba_ge1 that l_aa_outl unfolding aa2_def
      by (cases aa; cases \<open>tl aa\<close>; cases ba; cases \<open>ba - 1\<close>)
        auto
    have no_tauto_nth:  \<open> i < length outl \<Longrightarrow> - outl ! ba = outl ! i \<Longrightarrow> False\<close> for i
      using consistent ba_le nth_mem
      by (force simp: tautology_decomp' uminus_lit_swap)
    have outl_ba__L: \<open>outl ! ba \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using lits ba_le literals_are_in_\<L>\<^sub>i\<^sub>n_in_mset_\<L>\<^sub>a\<^sub>l\<^sub>l by auto
    have \<open>(lookup_conflict_remove1 (outl ! ba) a,
        remove1_mset (outl ! ba)  (D -(mset (take ba outl)))) \<in> lookup_clause_rel\<close>
      by (rule lookup_conflict_remove1[THEN fref_to_Down_unRET_uncurry])
        (use ba_ge1 ba_le aD   outl_ba__L in 
       \<open>auto simp: D in_set_drop_conv_nth image_image dest: no_tauto_nth 
        intro!: bex_geI[of _ ba]\<close>)
    then have \<open>(lookup_conflict_remove1 (outl ! ba) a,
      D - mset (take (Suc ba) outl))
      \<in> lookup_clause_rel\<close>
      using aD ba_le ba_ge1 ba_ge1_aa_ge aa0
      by (auto simp: take_Suc_conv_app_nth)
    moreover have \<open>1 < length
          (take (ba + one_uint32_nat)
            (if get_level M (aa[ba := outl ! ba] ! one_uint32_nat)
                < get_level M (aa[ba := outl ! ba] ! ba)
             then swap (aa[ba := outl ! ba]) one_uint32_nat ba
             else aa[ba := outl ! ba])) \<longrightarrow>
     highest_lit M
      (mset
        (tl (take (ba + one_uint32_nat)
              (if get_level M (aa[ba := outl ! ba] ! one_uint32_nat)
                  < get_level M (aa[ba := outl ! ba] ! ba)
               then swap (aa[ba := outl ! ba]) one_uint32_nat ba
               else aa[ba := outl ! ba]))))
      (Some
        ((if get_level M (aa[ba := outl ! ba] ! one_uint32_nat)
             < get_level M (aa[ba := outl ! ba] ! ba)
          then swap (aa[ba := outl ! ba]) one_uint32_nat ba
          else aa[ba := outl ! ba]) !
         1,
         get_level M
          ((if get_level M (aa[ba := outl ! ba] ! one_uint32_nat)
               < get_level M (aa[ba := outl ! ba] ! ba)
            then swap (aa[ba := outl ! ba]) one_uint32_nat ba
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
      (take (ba + one_uint32_nat)
        (if get_level M (aa[ba := outl ! ba] ! one_uint32_nat)
            < get_level M (aa[ba := outl ! ba] ! ba)
          then swap (aa[ba := outl ! ba]) one_uint32_nat ba
          else aa[ba := outl ! ba])) =
      mset (take (ba + one_uint32_nat) outl)\<close>
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
     (\<lambda>(D, C, i). i < length_u outl)
     (\<lambda>(D, C, i). do {
           _ \<leftarrow> ASSERT (i < length outl);
           _ \<leftarrow> ASSERT (i < length C);
           _ \<leftarrow> ASSERT (lookup_conflict_remove1_pre (outl ! i, D));
           _ \<leftarrow> ASSERT
                (C[i := outl ! i] ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
                 C[i := outl ! i] ! 1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
                1 < length (C[i := outl ! i]));
           _ \<leftarrow> ASSERT (i + 1 \<le> uint_max);
           RETURN
            (lookup_conflict_remove1 (outl ! i) D,
             if get_level M (C[i := outl ! i] ! one_uint32_nat)
                < get_level M (C[i := outl ! i] ! i)
             then swap (C[i := outl ! i]) one_uint32_nat i
             else C[i := outl ! i],
             i + one_uint32_nat)
         })
     (D', replicate (length outl) (outl ! 0), one_uint32_nat)
    \<le> \<Down> {((E, C, n), (E', F')). (E, E') \<in> lookup_clause_rel \<and> mset C = mset outl \<and>
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
  have x1b_lall:  \<open>x1b ! 1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    if 
      inv: \<open>(x, x')
      \<in> {((E, C, n), E', F').
          (E, E') \<in> lookup_clause_rel \<and>
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
      \<open>(x1a, x1) \<in> lookup_clause_rel\<close> and
      \<open>mset x1b = mset outl\<close> and
      \<open>x1b ! 0 = outl ! 0\<close> and
      \<open>Suc 0 < length x1b \<longrightarrow>
      highest_lit M (mset (tl x1b))
        (Some (x1b ! Suc 0, get_level M (x1b ! Suc 0)))\<close> and
      mset_aa: \<open>mset (take x2b x1b) = mset (take x2b outl)\<close> and
      \<open>(x1a, D - mset (take x2b outl)) \<in> lookup_clause_rel\<close> and
      l_aa_outl: \<open>length x1b = length outl\<close> and
      \<open>x1b ! 0 = outl ! 0\<close> and
      ba_ge1: \<open>Suc 0 \<le> x2b\<close> and
      ba_le: \<open>x2b \<le> length outl\<close> and
      \<open>Suc 0 < length x1b \<and> Suc 0 < x2b \<longrightarrow>
     highest_lit M (mset (tl (take x2b x1b)))
      (Some (x1b ! Suc 0, get_level M (x1b ! Suc 0)))\<close>
      using inv unfolding st I_def prod.case st
      by auto

    have set_aa_outl:  \<open>set (take x2b x1b) = set (take x2b outl)\<close>
      using mset_aa by (blast dest: mset_eq_setD)
   have ba_ge1_aa_ge:  \<open>x2b > 1 \<Longrightarrow> x1b ! 1 \<in> set (take x2b x1b)\<close>
      using ba_ge1 ba_le l_aa_outl
      by (auto simp: in_set_take_conv_nth intro!: bex_lessI[of _ \<open>Suc 0\<close>])
    then have \<open>x1b ! 1 \<in>  set outl\<close>
      using ba_le l_aa_outl ba_ge1 that
      unfolding mset_aa in_multiset_in_set[symmetric]
      by (cases \<open>x2b > 1\<close>)
        (auto simp: mset_aa dest: in_set_takeD)
    then show ?thesis
      using literals_are_in_\<L>\<^sub>i\<^sub>n_in_mset_\<L>\<^sub>a\<^sub>l\<^sub>l lits by auto
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


sepref_thm empty_conflict_and_extract_clause_heur_code
  is \<open>uncurry2 (PR_CONST empty_conflict_and_extract_clause_heur)\<close>
  :: \<open>[\<lambda>((M, D), outl). outl \<noteq> [] \<and> length outl \<le> uint_max]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>k \<rightarrow>
       (bool_assn *a uint32_nat_assn *a array_assn option_bool_assn) *a clause_ll_assn *a uint32_nat_assn\<close>
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


(* sepref_thm empty_conflict_and_extract_clause_heur_fast_code
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
   empty_conflict_and_extract_clause_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms] *)

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
(* 
definition (in isasat_input_ops) propagate_bt_wl_D_ext
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>propagate_bt_wl_D_ext = (\<lambda>L highest (M, N, D, NE, UE, Q, W). do {
    L' \<leftarrow> find_lit_of_max_level_wl (M, N, D, NE, UE, Q, W) L;
    D'' \<leftarrow> list_of_mset2 (-L) L' (the D);
    let b = False;
    (N, i) \<leftarrow> RETURN (append_clause b C N, length N);
    RETURN (Propagated (-L) i # M,
        N, None, NE, UE, {#L#}, W(-L:= W (-L) @ [(i, L')], L':= W L' @ [(i, L)]))
      })\<close> *)

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

definition (in isasat_input_ops) extract_shorter_conflict_list_heur_st
  :: \<open>twl_st_wl_heur \<Rightarrow> (twl_st_wl_heur \<times> _ \<times> _) nres\<close>
where
  \<open>extract_shorter_conflict_list_heur_st = (\<lambda>(M, N, (_, D), Q', W', vm, \<phi>, clvls, cach, lbd, outl,
       stats, ccont, vdom). do {
     ASSERT(M \<noteq> []);
     ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n_trail M);
     let K = lit_of (hd M);
     ASSERT(-K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
     ASSERT(0 < length outl);
     ASSERT(lookup_conflict_remove1_pre (-K, D));
     let D = lookup_conflict_remove1 (-K) D;
     let outl = outl[0 := -K];
     (D, cach, outl) \<leftarrow> isa_minimize_and_extract_highest_lookup_conflict M N D cach lbd outl;
     let cach = empty_cach cach;
     ASSERT(outl \<noteq> [] \<and> length outl \<le> uint_max);
     (D, C, n) \<leftarrow> empty_conflict_and_extract_clause_heur M D outl;
     RETURN ((M, N, D, Q', W', vm, \<phi>, clvls, cach, lbd, take 1 outl, stats, ccont, vdom), n, C)
  })\<close>

lemma the_option_lookup_clause_assn[sepref_fr_rules]:
  \<open>(return o snd, RETURN o the) \<in> [\<lambda>D. D \<noteq> None]\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow> lookup_clause_assn\<close>
  by (sepref_to_hoare)
    (sep_auto simp: option_lookup_clause_assn_def option_lookup_clause_rel_def
      lookup_clause_assn_def hr_comp_def)


definition (in isasat_input_ops) empty_conflict_and_extract_clause_pre
   :: \<open>(((nat,nat) ann_lits \<times> nat clause) \<times> nat clause_l) \<Rightarrow> bool\<close> where
  \<open>empty_conflict_and_extract_clause_pre =
    (\<lambda>((M, D), outl). D = mset (tl outl)  \<and> outl \<noteq> [] \<and> distinct outl \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset outl) \<and>
    \<not>tautology (mset outl) \<and> length outl \<le> uint_max)\<close>

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
  \<open>ema_update coeff ema lbd = (ema >> coeff) + ((uint64_of_nat lbd) << (48 - coeff))\<close>

definition (in -) ema_update_ref :: \<open>nat \<Rightarrow> ema \<Rightarrow> uint32 \<Rightarrow> ema\<close> where
  \<open>ema_update_ref coeff ema lbd = (ema >> coeff) +  ((uint64_of_uint32 lbd) << (48 - coeff))\<close>

lemma (in -) ema_update_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo ema_update_ref), uncurry2 (RETURN ooo ema_update)) \<in>
     nat_assn\<^sup>k *\<^sub>a ema_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding ema_update_def ema_update_ref_def
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def uint64_of_uint32_def)

abbreviation(in -) ema_update_slow where
  \<open>ema_update_slow \<equiv> ema_update 14\<close>
abbreviation (in -)ema_update_fast where
  \<open>ema_update_fast \<equiv> ema_update 5\<close>

definition (in isasat_input_ops) propagate_bt_wl_D_heur
  :: \<open>nat literal \<Rightarrow> nat clause_l \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>propagate_bt_wl_D_heur = (\<lambda>L C (M, N, D, Q, W, vm, \<phi>, _, cach, lbd, outl, stats, fema, sema,
         ccount, vdom, lcount). do {
      ASSERT(phase_saving \<phi> \<and> vm \<in> vmtf M \<and> undefined_lit M (-L) \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
         nat_of_lit (C!1) < length W \<and> nat_of_lit (-L) < length W);
      ASSERT(length C > 1);
      let L' = C!1;
      ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n (mset C));
      ASSERT(length C \<le> uint32_max + 2);
      (vm, \<phi>) \<leftarrow> rescore_clause C M vm \<phi>;
      vm \<leftarrow> flush M vm;
      glue \<leftarrow> get_LBD lbd;
      let b = False;
      (N, i) \<leftarrow> fm_add_new b C N;
      ASSERT(update_lbd_pre ((i, glue), N));
      let N = update_lbd i glue N;
      let W = W[nat_of_lit (- L) := W ! nat_of_lit (- L) @ [(i, L')]];
      let W = W[nat_of_lit L' := W!nat_of_lit L' @ [(i, -L)]];
      lbd \<leftarrow> lbd_empty lbd;
      RETURN (Propagated (- L) i # M, N, D, {#L#}, W, vm, \<phi>, zero_uint32_nat,
         cach, lbd, outl, stats, ema_update_fast fema glue, ema_update_slow sema glue,
          ccount + one_uint32, vdom @ [nat_of_uint32_conv i], Suc lcount)
    })\<close>

definition (in -) lit_of_hd_trail_st_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal\<close> where
  \<open>lit_of_hd_trail_st_heur S = lit_of (hd (get_trail_wl_heur S))\<close>

definition (in isasat_input_ops) remove_last
   :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> nat clause option nres\<close>
where
  \<open>remove_last _ _  = SPEC((=) None)\<close>

definition (in isasat_input_ops) propagate_unit_bt_wl_D_int
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>propagate_unit_bt_wl_D_int = (\<lambda>L (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
      fema, sema, ccount, vdom). do {
      ASSERT(undefined_lit M L \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> vm \<in> vmtf M);
      vm \<leftarrow> flush M vm;
      glue \<leftarrow> get_LBD lbd;
      lbd \<leftarrow> lbd_empty lbd;
      RETURN (Propagated (- L) 0 # M, N, D, {#L#}, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
         ema_update_fast fema glue, ema_update_slow sema glue,
        ccount + one_uint32, vdom)})\<close>


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

text \<open>This relations decouples the conflict that has been minimised and appears abstractly
from the refined state, where the conflict has been removed from the data structure to a 
separate array.\<close>
definition (in isasat_input_ops) twl_st_heur_bt :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_bt =
  {((M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats, _, _, _, vdom, lcount),
     (M, N, D, NE, UE, Q, W)).
    M = M' \<and>
    valid_arena N' N (set vdom) \<and>
    (D', None) \<in> option_lookup_clause_rel \<and>
    Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M None \<and>
    cach_refinement_empty cach \<and>
    out_learned M None outl \<and>
    lcount = size (learned_clss_l N) \<and>
    vdom_m W N \<subseteq> set vdom
  }\<close>

lemma lcount_add_clause[simp]: \<open>i \<notin># dom_m N \<Longrightarrow>
       size (learned_clss_l (fmupd i (C, False) N)) = Suc (size (learned_clss_l N))\<close>
  by (simp add: learned_clss_l_mapsto_upd_notin)

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
              get_clauses_wl_heur T' = get_clauses_wl_heur S' \<and>
              (1 < length C \<longrightarrow>
                highest_lit (get_trail_wl T) (mset (tl C))
                (Some (C ! 1, get_level (get_trail_wl T) (C ! 1)))) \<and>
              C \<noteq> [] \<and> hd C = -lit_of(hd (get_trail_wl T)) \<and>
              mset C \<subseteq># the (get_conflict_wl S) \<and>
              distinct_mset (the (get_conflict_wl S)) \<and>
              literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S)) \<and>
              get_conflict_wl S \<noteq> None \<and>
              - lit_of (hd (get_trail_wl S)) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
              find_decomp_wl_pre (n, T') \<and>
              literals_are_\<L>\<^sub>i\<^sub>n T}
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
    obtain W' vm \<phi> clvls cach lbd outl stats cc cc2 cc3 vdom lcount D' arena b where
      S': \<open>S' = (M, arena, (b, D'), Q, W', vm, \<phi>, clvls, cach, lbd, outl, stats, cc, cc2, cc3, vdom,
        lcount)\<close>
      using S'_S by (cases S') (auto simp: twl_st_heur_def S)
    have
      \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> and
      vm: \<open>vm \<in> vmtf M\<close> and
      \<open>phase_saving \<phi>\<close> and
      n_d: \<open>no_dup M\<close> and
      \<open>clvls \<in> counts_maximum_level M D\<close> and
      cach_empty: \<open>cach_refinement_empty cach\<close> and
      outl: \<open>out_learned M D outl\<close> and
      lcount: \<open>lcount = size (learned_clss_l N)\<close> and
      \<open>vdom_m W N \<subseteq> set vdom\<close> and
      D': \<open>((b, D'), D) \<in> option_lookup_clause_rel\<close> and
      arena: \<open>valid_arena arena N (set vdom)\<close>
      using S'_S unfolding S S' twl_st_heur_def
      by (auto simp: S)
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
    have D_none: \<open>D \<noteq> None\<close>
      using S_T not_none by (auto simp: S)
    have b: \<open>\<not>b\<close>
      using D' not_none S_T by (auto simp: option_lookup_clause_rel_def S state_wl_l_def)
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

    have L_D: \<open>lit_of (hd M) \<notin># the D\<close> and
      tauto_confl':  \<open>\<not>tautology (remove1_mset (- lit_of (hd M)) (the D))\<close>
      using uL_D tauto_confl
      by (auto dest!: multi_member_split simp: S add_mset_eq_add_mset tautology_add_mset)
    then have pre1: \<open>D \<noteq> None \<and> delete_from_lookup_conflict_pre (- lit_of (hd M), the D)\<close>
      using not_none uL_D uM_\<L>\<^sub>a\<^sub>l\<^sub>l S_T T_U unfolding delete_from_lookup_conflict_pre_def
      by (auto simp: twl_st S)
    have pre2: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf N) \<equiv> True\<close>
      using M_\<L>\<^sub>i\<^sub>n S_T T_U not_none \<L>\<^sub>i\<^sub>n
      unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def literals_are_\<L>\<^sub>i\<^sub>n_def
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
    have \<open>- lit_of (hd M) \<in># (the D)\<close>
      using uL_D by (auto simp: S)
    then have extract_shorter_conflict_wl_alt_def:
      \<open>extract_shorter_conflict_wl (M, N, D, NE, UE, Q, W) = do {
        let K = lit_of (hd M);
        let D = (remove1_mset (-K) (the D));
        E' \<leftarrow> (SPEC
          (\<lambda>(E'). E' \<subseteq># add_mset (-K) D \<and> - lit_of (hd M) :#  E' \<and>
             mset `# ran_mf N +
             (get_unit_learned_clss_wl S + get_unit_init_clss_wl S) \<Turnstile>pm E'));
        D \<leftarrow> RETURN (Some E');
        RETURN  (M, N, D, NE, UE, Q, W) 
      }\<close>
      unfolding extract_shorter_conflict_wl_def
      by (auto simp: RES_RETURN_RES image_iff mset_take_mset_drop_mset' S union_assoc
        Un_commute Let_def)
    have lookup_clause_rel_unique: \<open>(D', a) \<in> lookup_clause_rel \<Longrightarrow> (D', b) \<in> lookup_clause_rel \<Longrightarrow> a = b\<close>
      for a b
      by (auto simp: lookup_clause_rel_def mset_as_position_right_unique)
    have isa_minimize_and_extract_highest_lookup_conflict:
     \<open>isa_minimize_and_extract_highest_lookup_conflict M arena
         (lookup_conflict_remove1 (-lit_of (hd M)) D') cach lbd (outl[0 := - lit_of (hd M)])
      \<le> \<Down> ({((E, s, outl), E').
            (E, mset (tl outl)) \<in> lookup_clause_rel \<and>
            mset outl = E' \<and>
            outl ! 0 = - lit_of (hd M) \<and>
            E' \<subseteq># the D \<and> outl \<noteq> [] \<and> distinct outl \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset outl) \<and>
            \<not>tautology (mset outl)})
          (SPEC (\<lambda>E'. E' \<subseteq># add_mset (- lit_of (hd M)) (remove1_mset (- lit_of (hd M)) (the D)) \<and>
              - lit_of (hd M) \<in># E' \<and>
              mset `# ran_mf N +
              (get_unit_learned_clss_wl S + get_unit_init_clss_wl S) \<Turnstile>pm
              E'))\<close>
        (is \<open>_ \<le> \<Down> ?minimize (RES ?E)\<close>)
      apply (rule order_trans)
      apply (rule
       isa_minimize_and_extract_highest_lookup_conflict_minimize_and_extract_highest_lookup_conflict
         [THEN fref_to_Down_curry5,
        of M N \<open>remove1_mset (-lit_of (hd M)) (the D)\<close> cach lbd \<open>outl[0 := - lit_of (hd M)]\<close>
           _ _ _ _ _ _ \<open>set vdom\<close>])
      subgoal using tauto_confl' pre2 by auto
      subgoal using D' not_none arena S_T uL_D  uM_\<L>\<^sub>a\<^sub>l\<^sub>l  not_empty D' L_D b
        by (auto simp: option_lookup_clause_rel_def S state_wl_l_def image_image
          intro!: lookup_conflict_remove1[THEN fref_to_Down_unRET_uncurry]
          dest: multi_member_split lookup_clause_rel_unique)
      apply (rule order_trans)
      apply (rule mini[THEN conc_fun_mono])
      subgoal
        using uL_D dist_D tauto_D \<L>\<^sub>i\<^sub>n_S \<L>\<^sub>i\<^sub>n_D tauto_D L_D
        by (fastforce simp: conc_fun_chain conc_fun_RES image_iff S union_assoc insert_subset_eq_iff
          neq_Nil_conv literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset tautology_add_mset
          intro: literals_are_in_\<L>\<^sub>i\<^sub>n_mono
          dest: distinct_mset_mono not_tautology_mono
          dest!: multi_member_split)
      done
    have empty_conflict_and_extract_clause_heur: \<open>empty_conflict_and_extract_clause_heur M x1 x2a
          \<le> \<Down>  ({((E, outl, n), E').
         (E, None) \<in> option_lookup_clause_rel \<and>
         mset outl = the E' \<and>
         outl ! 0 = - lit_of (hd M) \<and>
         the E' \<subseteq># the D \<and> outl \<noteq> [] \<and> E' \<noteq> None \<and>
         (1 < length outl \<longrightarrow>
            highest_lit M (mset (tl outl)) (Some (outl ! 1, get_level M (outl ! 1)))) \<and>
         (1 < length outl \<longrightarrow> n = get_level M (outl ! 1)) \<and> (length outl = 1 \<longrightarrow> n = 0)}) (RETURN (Some E'))\<close>
      (is \<open>_ \<le> \<Down> ?empty_conflict _\<close>)
      if 
        \<open>M \<noteq> []\<close> and
        \<open>- lit_of (hd M) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
        \<open>0 < length outl\<close> and
        \<open>lookup_conflict_remove1_pre (- lit_of (hd M), D')\<close> and
        \<open>(x, E')  \<in> ?minimize\<close> and
        \<open>E' \<in> ?E\<close> and
        \<open>x2 = (x1a, x2a)\<close> and
        \<open>x = (x1, x2)\<close>
      for x :: \<open>(nat \<times> bool option list) \<times>  (nat \<Rightarrow> minimize_status) \<times> nat literal list\<close> and
        E' :: \<open>nat literal multiset\<close> and
        x1 :: \<open>nat \<times> bool option list\<close> and
        x2 :: \<open>(nat \<Rightarrow> minimize_status) \<times>  nat literal list\<close> and
        x1a :: \<open>nat \<Rightarrow> minimize_status\<close> and
        x2a :: \<open>nat literal list\<close>
    proof -
      show ?thesis
        apply (rule order_trans)
        apply (rule empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause[of \<open>mset (tl x2a)\<close>])
        subgoal by auto
        subgoal using that by auto
        subgoal using that by auto
        subgoal using that by auto
        subgoal using that by auto
        subgoal using that by auto
        subgoal unfolding empty_conflict_and_extract_clause_def
          using that
          by (auto simp: conc_fun_RES RETURN_def)
       done
    qed

    have final: \<open>(((M, arena, x1b, Q, W', vm, \<phi>, clvls, empty_cach x1a, lbd, take 1 x2a,
            stats, cc, cc2, cc3, vdom, lcount),
            x2c, x1c),
          M, N, Da, NE, UE, Q, W)
          \<in> {((T', n, C), T).
            (T', del_conflict_wl T) \<in> twl_st_heur \<and>
            n =
            get_maximum_level (get_trail_wl T)
              (remove1_mset (- lit_of (hd (get_trail_wl T)))
                (the (get_conflict_wl T))) \<and>
            mset C = the (get_conflict_wl T) \<and>
            get_conflict_wl T \<noteq> None \<and>
            equality_except_conflict_wl T (M, N, D, NE, UE, Q, W) \<and>
            get_clauses_wl_heur T' = get_clauses_wl_heur (M, arena, (b, D'), Q, W', vm, \<phi>, clvls, cach, lbd, outl, stats, cc,
              cc2, cc3, vdom, lcount)  \<and>
            (1 < length C \<longrightarrow>
              highest_lit (get_trail_wl T) (mset (tl C))
              (Some (C ! 1, get_level (get_trail_wl T) (C ! 1)))) \<and>
            C \<noteq> [] \<and>
            hd C = - lit_of (hd (get_trail_wl T)) \<and>
            mset C \<subseteq># the (get_conflict_wl (M, N, D, NE, UE, Q, W)) \<and>
            distinct_mset (the (get_conflict_wl (M, N, D, NE, UE, Q, W))) \<and>
            literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl (M, N, D, NE, UE, Q, W))) \<and>
            get_conflict_wl (M, N, D, NE, UE, Q, W) \<noteq> None \<and>
            - lit_of (hd (get_trail_wl (M, N, D, NE, UE, Q, W))) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
            find_decomp_wl_pre (n, T') \<and> literals_are_\<L>\<^sub>i\<^sub>n T}\<close>
      if 
        \<open>M \<noteq> []\<close> and
        \<open>- lit_of (hd M) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
        \<open>0 < length outl\<close> and
        \<open>lookup_conflict_remove1_pre (- lit_of (hd M), D')\<close> and
        \<open>(x, E')
        \<in> {((E, s, outl), E').
            (E, mset (tl outl)) \<in> lookup_clause_rel \<and>
            mset outl = E' \<and>
            outl ! 0 = - lit_of (hd M) \<and>
            E' \<subseteq># the D \<and>
            outl \<noteq> [] \<and>
            distinct outl \<and>
            literals_are_in_\<L>\<^sub>i\<^sub>n (mset outl) \<and> \<not> tautology (mset outl)}\<close> and
        \<open>E' \<in> ?E\<close> and
        \<open>(xa, Da) \<in> ?empty_conflict\<close> and
        st[simp]:
          \<open>x2b = (x1c, x2c)\<close>
          \<open>x2 = (x1a, x2a)\<close>
          \<open>x = (x1, x2)\<close> 
          \<open>xa = (x1b, x2b)\<close>
      for x E' x1 x2 x1a x2a xa Da x1b x2b x1c x2c
    proof -
      have x1b_None: \<open>(x1b, None) \<in> option_lookup_clause_rel\<close>
        using that apply auto
        done
      have cach: \<open>cach_refinement_empty (empty_cach x1a)\<close> and
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
          set_mset (get_unit_init_clss_wl S)) \<Turnstile>p
        mset x2a\<close> and
        \<open>x2a ! 0 = - lit_of (M ! 0)\<close> and
        \<open>x1c ! 0 = - lit_of (M ! 0)\<close> and
        \<open>mset x2a \<subseteq># the D\<close> and
        \<open>mset x1c \<subseteq># the D\<close> and
        \<open>x2a \<noteq> []\<close> and
        x1c_nempty: \<open>x1c \<noteq> []\<close> and
        \<open>distinct x2a\<close> and
        Da: \<open>Da = Some (mset x1c)\<close> and
        \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset x2a)\<close> and
        \<open>\<not> tautology (mset x2a)\<close> 
        using that
        unfolding cach_refinement_empty_def empty_cach_def out_learned_def
        apply (auto simp: hd_conv_nth)
        done
      have Da_D': \<open>remove1_mset (- lit_of (hd M)) (the Da) \<subseteq># remove1_mset (- lit_of (hd M)) (the D)\<close>
        using Da_D mset_le_subtract by blast
      (* from get_maximum_level_mono[OF this, of M] *)
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
      have \<open>((M, arena, x1b, Q, W', vm, \<phi>, clvls, empty_cach x1a, lbd, take (Suc 0) x2a,
          stats, cc, cc2, cc3, vdom, lcount),
        del_conflict_wl (M, N, Da, NE, UE, Q, W))
        \<in> twl_st_heur\<close>
        using S'_S x1b_None cach out
        by (auto simp: twl_st_heur_def del_conflict_wl_def S S')
      moreover have x2c: \<open>x2c = get_maximum_level M (remove1_mset (- lit_of (hd M)) (the Da))\<close>
        using highest highest2 x1c_nempty hd_x1c
        by (cases \<open>length x1c = Suc 0\<close>; cases x1c)
          (auto simp: highest_lit_def Da mset_tl)
      moreover have \<open>find_decomp_wl_pre
          (x2c, M, arena, x1b, Q, W', vm, \<phi>, clvls, empty_cach x1a, lbd,
           take (Suc 0) x2a, stats, cc, cc2, cc3, vdom, lcount)\<close>
        using vm n_d M_\<L>\<^sub>i\<^sub>n highest max_lvl_le
        unfolding find_decomp_wl_pre_def find_decomp_w_ns_pre_def
        by (auto simp: S x2c)
      moreover have \<open>literals_are_\<L>\<^sub>i\<^sub>n (M, N, Some (mset x1c), NE, UE, Q, W)\<close>
        using \<L>\<^sub>i\<^sub>n
        by (auto simp: S x2c literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def)
      ultimately show ?thesis
        using \<L>\<^sub>i\<^sub>n_S x1c_Da Da_None dist_D D_none x1c_D x1c hd_x1c highest uM_\<L>\<^sub>a\<^sub>l\<^sub>l
        by (auto simp: S x2c)
    qed

    show ?thesis
      unfolding extract_shorter_conflict_list_heur_st_def 
        empty_conflict_and_extract_clause_def S S' prod.simps
      apply (rewrite at  \<open>let _ = list_update _ _ _ in _ \<close>Let_def)
      apply (rewrite at  \<open>let _ = empty_cach  _ in _ \<close> Let_def)
      apply (subst extract_shorter_conflict_wl_alt_def)
      apply (refine_vcg isa_minimize_and_extract_highest_lookup_conflict empty_conflict_and_extract_clause_heur)
      subgoal using trail_nempty .
      subgoal using pre2 by blast
      subgoal using  uM_\<L>\<^sub>a\<^sub>l\<^sub>l .
      subgoal using  \<open>0 < length outl\<close> .
      subgoal by (rule lookup_conflict_remove1_pre)
      subgoal by auto
      subgoal by (auto dest!: simple_clss_size_upper_div2 simp: uint32_max_def)
      apply assumption+
      subgoal by (rule final)
      done
  qed

  have find_decomp_wl_nlit: \<open>find_decomp_wl_nlit n T
      \<le> \<Down>  {(U, U''). (U, U'') \<in> twl_st_heur_bt \<and> equality_except_trail_wl U'' T' \<and>
       (\<exists>K M2. (Decided K # (get_trail_wl U''), M2) \<in> set (get_all_ann_decomposition (get_trail_wl T')) \<and>
          get_level (get_trail_wl T') K = get_maximum_level (get_trail_wl T') (the (get_conflict_wl T') - {#-lit_of (hd (get_trail_wl T'))#}) + 1 \<and>
          get_clauses_wl_heur U = get_clauses_wl_heur S)}
          (find_decomp_wl (lit_of (hd (get_trail_wl S'))) T')\<close>
    (is \<open>_ \<le>  \<Down> ?find_decomp _\<close>)
    if
      \<open>(S, S') \<in> twl_st_heur\<close> and
      \<open>backtrack_wl_D_inv S'\<close> and
      \<open>backtrack_wl_D_heur_inv S\<close> and
      TT': \<open>(TnC, T') \<in> ?shorter S' S\<close> and
      [simp]: \<open>nC = (n, C)\<close> and
      [simp]: \<open>TnC = (T, nC)\<close>
    for S S' TnC T' T nC n C
  proof -
    obtain M N D NE UE Q W where
      T': \<open>T' = (M, N, D, NE, UE, Q, W)\<close>
      by (cases T')
    obtain W' vm \<phi> clvls cach lbd outl stats arena D' where
      T: \<open>T = (M, arena, D', Q, W', vm, \<phi>, clvls, cach, lbd, outl, stats)\<close>
      using TT' by (cases T) (auto simp: twl_st_heur_def T' del_conflict_wl_def)
    have n: \<open>n = get_maximum_level M (remove1_mset (- lit_of (hd M)) (mset C))\<close> and
      eq: \<open>equality_except_conflict_wl T' S'\<close> and
      \<open>the D = mset C\<close> \<open>D \<noteq> None\<close> and
      \<open>no_dup M\<close> and
      clss_eq: \<open>get_clauses_wl_heur S = arena\<close>
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
      if s: \<open>s \<in> Collect (find_decomp_wl_nlit_prop n (M, arena, D', Q, W', vm, \<phi>, clvls, cach, lbd, outl, stats))\<close>
      for s :: \<open>twl_st_wl_heur\<close>
    proof -
      obtain K M2 M1 vm' lbd' where
        s: \<open>s = (M1, arena, D',  Q, W', vm', \<phi>, clvls, cach, lbd', outl, stats)\<close> and
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
      have twl: \<open>((M1, arena, D', Q, W', vm', \<phi>, clvls, cach, lbd', outl, stats),
           M1, N, D, NE, UE, Q, W) \<in> twl_st_heur_bt\<close>
        using TT' vm' \<open>no_dup M1\<close> by (auto simp: T T' twl_st_heur_bt_def twl_st_heur_def
            del_conflict_wl_def)
      have \<open>equality_except_trail_wl (M1, N, D, NE, UE, Q, W) T'\<close>
        using eq by (auto simp: T')
      then have T': \<open>(s, ?T') \<in> ?find_decomp\<close>
        using decomp n n_M_K \<open>the D = mset C\<close> twl clss_eq
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
      \<open>(TnC, T') \<in> ?shorter S' S\<close> and
      [simp]: \<open>nC = (n, C)\<close> and
      [simp]: \<open>TnC = (T, nC)\<close> and
      find_decomp: \<open>(U, U') \<in> ?find_decomp S T'\<close> and
      size_C: \<open>1 < length C\<close> and
      size_conflict_U': \<open>1 < size (the (get_conflict_wl U'))\<close>
    for S S' TnC T' T nC n C U U'
  proof -
    obtain M N NE UE Q W where
      T': \<open>T' = (M, N, Some (mset C), NE, UE, Q, W)\<close> and
      \<open>C \<noteq> []\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> \<open>1 < length C\<close> find_decomp
      apply (cases U'; cases T'; cases S')
      by (auto simp: find_lit_of_max_level_wl_def)

    obtain M' K M2 where
      U': \<open>U' = (M', N, Some (mset C), NE, UE, Q, W)\<close> and
       decomp: \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M)\<close> and
       lev_K: \<open>get_level M K = Suc (get_maximum_level M (remove1_mset (- lit_of (hd M)) (the (Some (mset C)))))\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> \<open>1 < length C\<close> find_decomp
      apply (cases U'; cases S')
      by (auto simp: find_lit_of_max_level_wl_def T')

    have [simp]: \<open>get_trail_wl S' = get_trail_wl T'\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> \<open>1 < length C\<close> find_decomp
      by (cases T'; cases S'; auto simp: find_lit_of_max_level_wl_def U'; fail)+
    have [simp]: \<open>remove1_mset (- lit_of (hd M)) (mset C) = mset (tl C)\<close>
      apply (subst mset_tl)
      using \<open>(TnC, T') \<in> ?shorter S' S\<close>
      by (auto simp: find_lit_of_max_level_wl_def U' highest_lit_def T')
    have
      \<open>no_dup (get_trail_wl S')\<close>
      using that unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
      twl_struct_invs_def twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def apply -
      apply normalize_goal+
      by (simp add: twl_st)
    then have n_d: \<open>no_dup M\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> unfolding T'
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
  have propagate_bt_wl_D_heur: \<open>propagate_bt_wl_D_heur (lit_of_hd_trail_st_heur S) C U
      \<le> \<Down> twl_st_heur (propagate_bt_wl_D (lit_of (hd (get_trail_wl S'))) L' U')\<close>
    if
      SS': \<open>(S, S') \<in> twl_st_heur\<close> and
      \<open>backtrack_wl_D_inv S'\<close> and
      \<open>backtrack_wl_D_heur_inv S\<close> and
      \<open>(TnC, T') \<in> ?shorter S' S\<close> and
      [simp]: \<open>nC = (n, C)\<close> and
      [simp]: \<open>TnC = (T, nC)\<close> and
      find_decomp: \<open>(U, U') \<in> ?find_decomp S T'\<close> and
      le_C: \<open>1 < length C\<close> and
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
      C_nempty: \<open>C \<noteq> []\<close> and
      hd_C: \<open>hd C = - lit_of (hd (get_trail_wl T'))\<close> and
      highest: \<open>highest_lit (get_trail_wl T') (mset (tl C))
         (Some (C ! Suc 0, get_level (get_trail_wl T') (C ! Suc 0)))\<close> and
      incl: \<open>mset C \<subseteq># the (get_conflict_wl S')\<close> and
      dist_S': \<open>distinct_mset (the (get_conflict_wl S'))\<close> and
      list_confl_S': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S'))\<close> and
      \<open>get_conflict_wl S' \<noteq> None\<close> and
      uM_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>-lit_of (hd (get_trail_wl S')) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
      lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n T'\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close>  \<open>1 < length C\<close>
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
    obtain D where
      S': \<open>S' = (M, N, D, NE, UE, Q, W)\<close>
      using T'S' \<open>1 < length C\<close>
      apply (cases S')
      by (auto simp: find_lit_of_max_level_wl_def T' del_conflict_wl_def)

    obtain M1 where
      U': \<open>U' = (M1, N, Some (mset C), NE, UE, Q, W)\<close>
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> \<open>1 < length C\<close> find_decomp
      apply (cases U')
      by (auto simp: find_lit_of_max_level_wl_def T')
    obtain vm' W' \<phi> clvls cach lbd outl stats fema sema ccount vdom lcount arena D' where
        U: \<open>U = (M1, arena, D', Q, W', vm', \<phi>, clvls, cach, lbd, outl, stats, fema, sema, ccount,
           vdom, lcount)\<close> and
        vm': \<open>vm' \<in> vmtf M1\<close> and
        \<phi>: \<open>phase_saving \<phi>\<close> and
        vdom: \<open>vdom_m W N \<subseteq> set vdom\<close> and
        valid: \<open>valid_arena arena N (set vdom)\<close>
      using UU' find_decomp by (cases U) (auto simp: U' T' twl_st_heur_bt_def)
    have
      W'W: \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> and
      vmtf: \<open>vm' \<in> vmtf M1\<close> and
      \<phi>: \<open>phase_saving \<phi>\<close> and
      n_d_M1: \<open>no_dup M1\<close> and
      empty_cach: \<open>cach_refinement_empty cach\<close> and
      \<open>length outl = Suc 0\<close> and
      outl: \<open>out_learned M1 None outl\<close>and
      vdom: \<open>vdom_m W N \<subseteq> set vdom\<close> and
      lcount: \<open>lcount = size (learned_clss_l N)\<close> and
      vdom_m: \<open>vdom_m W N \<subseteq> set vdom\<close> and
      D': \<open>(D', None) \<in> option_lookup_clause_rel\<close>
      using UU' by (auto simp: out_learned_def twl_st_heur_bt_def U U')
    have [simp]: \<open>get_trail_wl_heur S = M\<close> \<open>C ! 1 = L'\<close> \<open>C ! 0 = - lit_of (hd M)\<close> and
      n_d: \<open>no_dup M\<close>
      using SS' C_L' hd_C \<open>C \<noteq> []\<close> by (auto simp: S' U' T' twl_st_heur_def hd_conv_nth)
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
        by (auto intro: ext simp: intro_spec_iff bind_RES)
      moreover have \<open>?A \<le> ?B\<close>
        by (auto intro: ext simp: intro_spec_iff bind_RES)
      ultimately show ?thesis by auto
    qed
    have propagate_bt_wl_D_heur_alt_def:
       \<open>propagate_bt_wl_D_heur = (\<lambda>L C (M, N, D, Q, W, vm, \<phi>, _, cach, lbd, outl, stats, fema, sema,
         ccount, vdom, lcount). do {
          ASSERT(phase_saving \<phi> \<and> vm \<in> vmtf M \<and> undefined_lit M (-L) \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
            nat_of_lit (C!1) < length W \<and> nat_of_lit (-L) < length W);
          ASSERT(length C > 1);
          let L' = C!1;
          ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n (mset C));
          ASSERT (length C \<le> uint32_max + 2);
          (vm, \<phi>) \<leftarrow> rescore_clause C M vm \<phi>;
          vm \<leftarrow> flush M vm;
          glue \<leftarrow> get_LBD lbd;
          let _ = C;
          let b = False;
          (N, i) \<leftarrow> fm_add_new b C N;
          ASSERT(update_lbd_pre ((i, glue), N));
          let N = update_lbd i glue N;
          let W = W[nat_of_lit (- L) := W ! nat_of_lit (- L) @ [(i, L')]];
          let W = W[nat_of_lit L' := W!nat_of_lit L' @ [(i, -L)]];
          lbd \<leftarrow> lbd_empty lbd;
          RETURN (Propagated (- L) i # M, N, D, {#L#}, W, vm, \<phi>, zero_uint32_nat,
            cach, lbd, outl, stats, ema_update_fast fema glue, ema_update_slow sema glue,
              ccount + one_uint32, vdom @ [nat_of_uint32_conv i], Suc lcount)
      })\<close>
      unfolding propagate_bt_wl_D_heur_def
      by auto
    have propagate_bt_wl_D_alt_def:
      \<open>propagate_bt_wl_D (lit_of (hd (get_trail_wl S'))) L' U' = do {
            _ \<leftarrow> RETURN (); \<^cancel>\<open>phase saving\<close>
            _ \<leftarrow> RETURN (); \<^cancel>\<open>flush\<close>
            _ \<leftarrow> RETURN (); \<^cancel>\<open>LBD\<close>
            D'' \<leftarrow>
              list_of_mset2 (- lit_of (hd (get_trail_wl S'))) L'
               (the (Some (mset C)));
            (N, i) \<leftarrow> SPEC
                 (\<lambda>(N', i). N' = fmupd i (D'', False) N \<and> 0 < i \<and>
                      i \<notin># dom_m N \<and>
                      (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE)).
                          i \<notin> fst ` set (W L)));
            RETURN
             (Propagated (- lit_of (hd (get_trail_wl S'))) i # M1,
              N, None, NE, UE,
              unmark (hd (get_trail_wl S')), W
              (- lit_of (hd (get_trail_wl S')) :=
                 W (- lit_of (hd (get_trail_wl S'))) @ [(i, L')],
               L' := W L' @ [(i, - lit_of (hd (get_trail_wl S')))]))
          }\<close>
      unfolding propagate_bt_wl_D_def Let_def
         U U' H get_fresh_index_wl_def prod.case
        propagate_bt_wl_D_heur_def propagate_bt_wl_D_def Let_def rescore_clause_def
      apply (auto simp: U' RES_RES2_RETURN_RES RES_RETURN_RES \<phi> uminus_\<A>\<^sub>i\<^sub>n_iff
          uncurry_def RES_RES_RETURN_RES
          get_fresh_index_def RES_RETURN_RES2 RES_RES_RETURN_RES2 list_of_mset2_def)
      done
    have [refine0]: \<open>SPEC (\<lambda>(vm', \<phi>'). vm' \<in> vmtf M1 \<and> phase_saving \<phi>') \<le> \<Down>{((vm', \<phi>'), ()). vm' \<in> vmtf M1 \<and> phase_saving \<phi>'} (RETURN ())\<close>
      by (auto intro!: RES_refine simp: RETURN_def)
    have [refine0]: \<open>flush M1 x1 \<le> \<Down> {(vm', _). vm' \<in> vmtf M1} (RETURN ())\<close> for x1
      unfolding flush_def by (auto intro!: RES_refine simp: RETURN_def)
    have [refine0]: \<open>get_LBD lbd \<le> \<Down> {(_, _). True}(RETURN ())\<close>
      unfolding get_LBD_def by (auto intro!: RES_refine simp: RETURN_def)
    have [refine0]: \<open>RETURN C
       \<le> \<Down> Id
          (list_of_mset2 (- lit_of (hd (get_trail_wl S'))) L'
            (the (Some (mset C))))\<close>
      using that
      by (auto simp: list_of_mset2_def S')
    have [simp]: \<open>0 < header_size D''\<close> for D''
      by (auto simp: header_size_def)
    have [simp]: \<open>length arena + header_size D'' \<notin> set vdom\<close> 
      \<open>length arena + header_size D'' \<notin> vdom_m W N\<close>
      \<open>length arena + header_size D'' \<notin># dom_m N\<close> for D''
      using valid_arena_in_vdom_le_arena[OF valid] vdom
      by (auto 5 1 simp: vdom_m_def)
    have add_new_alt_def: \<open>(SPEC
            (\<lambda>(N', i).
                N' = fmupd i (D'', False) N \<and>
                0 < i \<and>
                i \<notin># dom_m N \<and>
                (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE)).
                    i \<notin> fst ` set (W L)))) =
          (SPEC
            (\<lambda>(N', i).
                N' = fmupd i (D'', False) N \<and>
                0 < i \<and>
                i \<notin> vdom_m W N))\<close> for D''
      using lits
      by (auto simp: T' vdom_m_def literals_are_\<L>\<^sub>i\<^sub>n_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
    have [refine0]: \<open>fm_add_new False C arena
       \<le> \<Down> {((arena, i), (N', i')). valid_arena arena N' (insert i (set vdom)) \<and> i = i' \<and>
             i \<notin># dom_m N}
          (SPEC
            (\<lambda>(N', i).
                N' = fmupd i (D'', False) N \<and>
                0 < i \<and>
                i \<notin># dom_m N \<and>
                (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + (NE + UE)).
                    i \<notin> fst ` set (W L))))\<close>
      if \<open>(C, D'') \<in> Id\<close> for D''
      apply (subst add_new_alt_def)
      apply (rule order_trans)
      apply (rule fm_add_new_append_clause)
      using that valid le_C vdom
      by (auto simp: intro!: RETURN_RES_refine valid_arena_append_clause)
    have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close>
      using incl list_confl_S' literals_are_in_\<L>\<^sub>i\<^sub>n_mono by blast
    have le_C_ge: \<open>length C \<le> uint32_max + 2\<close>
      using clss_size_uint_max[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close>] list_confl_S' dist_S' incl
      size_mset_mono[OF incl] distinct_mset_mono[OF incl]
      by (auto simp: uint32_max_def S')
    have vm: \<open>vm \<in> vmtf M1 \<Longrightarrow> vm \<in> vmtf (Propagated (- lit_of (hd M)) x2a # M1)\<close> for x2a vm
      by (cases vm)
        (auto intro!: vmtf_consD)
    have [simp]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close>
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF list_confl_S' incl] .
    then have \<open>C ! Suc 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using \<open>1 < length C\<close>
      by (cases C; cases \<open>tl C\<close>) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    then have \<open>nat_of_lit (C ! Suc 0) < length W'\<close>
      using W'W unfolding map_fun_rel_def by (auto simp: image_image)
    then show ?thesis
      supply [[goals_limit=1]]
      using empty_cach n_d_M1 C_L' W'W outl vmtf undef \<open>1 < length C\<close> lits
        uM_\<L>\<^sub>a\<^sub>l\<^sub>l vdom lcount vdom_m
      apply (subst propagate_bt_wl_D_alt_def)
      unfolding U U' H get_fresh_index_wl_def prod.case 
        propagate_bt_wl_D_heur_alt_def rescore_clause_def
      apply (rewrite in \<open>let _ = _!1 in _\<close> Let_def)
      apply (rewrite in \<open>let _ = False in _\<close> Let_def)
      apply refine_rcg
      subgoal using \<phi> .
      subgoal using undef 
        by (auto simp: lit_of_hd_trail_st_heur_def T' U' U S')
      subgoal
        by (auto simp: lit_of_hd_trail_st_heur_def T' U' U S' uminus_\<A>\<^sub>i\<^sub>n_iff)
      subgoal by auto
      subgoal
        by (auto simp: lit_of_hd_trail_st_heur_def T' U' U rescore_clause_def S' map_fun_rel_def)
      subgoal by auto
      subgoal using le_C_ge .
      subgoal for x uu x1 x2 vm uua_ glue uub D'' xa x' x1a x2a x1b x2b
        by (auto simp: update_lbd_pre_def arena_is_valid_clause_idx_def)
      subgoal for x uu x1 x2 vm uua_ glue uub D'' xa x' x1a x2a x1b x2b
        using D' C_1_neq_hd vmtf
        apply (auto simp: propagate_bt_wl_D_heur_def twl_st_heur_def lit_of_hd_trail_st_heur_def
          propagate_bt_wl_D_def Let_def T' U' U rescore_clause_def S' map_fun_rel_def
          list_of_mset2_def flush_def RES_RES2_RETURN_RES RES_RETURN_RES \<phi> uminus_\<A>\<^sub>i\<^sub>n_iff
          get_fresh_index_def RES_RETURN_RES2 RES_RES_RETURN_RES2
          RES_RES_RETURN_RES lbd_empty_def get_LBD_def nat_of_uint32_conv_def
          intro!: ASSERT_refine_left RES_refine exI[of _ C] valid_arena_update_lbd
          intro!: vm)
        apply (auto simp: vdom_m_simps5)
        done \<comment> \<open>@{thm vdom_m_simps5} must apply after the other simp rules.\<close>
      done
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
      \<open>(TnC, T') \<in> ?shorter S' S\<close> and
      [simp]: \<open>nC = (n, C)\<close> and
      [simp]: \<open>TnC = (T, nC)\<close> and
      find_decomp: \<open>(U, U') \<in> ?find_decomp S T'\<close> and
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
      using \<open>(TnC, T') \<in> ?shorter S' S\<close>  \<open>~1 < length C\<close>
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
      using \<open>(TnC, T') \<in> ?shorter S' S\<close> find_decomp
      apply (cases U')
      by (auto simp: find_lit_of_max_level_wl_def T')
    obtain vm' W' \<phi> clvls cach lbd outl stats fema sema ccount vdom lcount arena D' where
        U: \<open>U = (M1, arena, D', Q, W', vm', \<phi>, clvls, cach, lbd, outl, stats, fema, sema, ccount,
           vdom, lcount)\<close> and
        vm': \<open>vm' \<in> vmtf M1\<close>
      using UU' find_decomp by (cases U) (auto simp: U' T' twl_st_heur_bt_def)
    have
      W'W: \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> and
      vmtf: \<open>vm' \<in> vmtf M1\<close> and
      \<phi>: \<open>phase_saving \<phi>\<close> and
      n_d_M1: \<open>no_dup M1\<close> and
      empty_cach: \<open>cach_refinement_empty cach\<close> and
      \<open>length outl = Suc 0\<close> and
      outl: \<open>out_learned M1 None outl\<close> and
      lcount: \<open>lcount = size (learned_clss_l N)\<close> and
      vdom: \<open>vdom_m W N \<subseteq> set vdom\<close> and
      valid: \<open>valid_arena arena N (set vdom)\<close> and
      D': \<open>(D', None) \<in> option_lookup_clause_rel\<close>
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
      using empty_cach n_d_M1  W'W outl vmtf C \<phi> undef uL_M vdom lcount valid D'
      unfolding U U'
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
    subgoal for x  y xa S x1 x2 x1a x2a
      by (auto simp: twl_st_heur_state_simp equality_except_conflict_wl_get_clauses_wl)
    subgoal by auto
       apply (rule find_decomp_wl_nlit; solves assumption)
    subgoal by (auto simp: twl_st_heur_state_simp equality_except_conflict_wl_get_clauses_wl
           equality_except_trail_wl_get_clauses_wl)
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
    append_ll_def[symmetric] append_ll_def[symmetric] nat_of_uint32_conv_def
    cons_trail_Propagated_def[symmetric] PR_CONST_def
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref \<comment> \<open>slow\<close>

concrete_definition (in -) propagate_bt_wl_D_code
  uses isasat_input_bounded_nempty.propagate_bt_wl_D_code.refine_raw
  is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_bt_wl_D_code_def

lemmas propagate_bt_wl_D_heur_hnr[sepref_fr_rules] =
  propagate_bt_wl_D_code.refine[OF isasat_input_bounded_nempty_axioms]
(* 
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
  propagate_bt_wl_D_fast_code.refine[OF isasat_input_bounded_nempty_axioms] *)

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

(* 
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
  propagate_unit_bt_wl_D_fast_code.refine[OF isasat_input_bounded_nempty_axioms] *)

end

setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>

context isasat_input_bounded_nempty
begin

(* lemma empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause':
  \<open>(uncurry2 (empty_conflict_and_extract_clause_heur), uncurry2 empty_conflict_and_extract_clause) \<in>
    [empty_conflict_and_extract_clause_pre]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto intro!: empty_conflict_and_extract_clause_heur_empty_conflict_and_extract_clause
      simp: empty_conflict_and_extract_clause_pre_def) *)

(* theorem
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
qed *)

sepref_register isa_minimize_and_extract_highest_lookup_conflict
  empty_conflict_and_extract_clause_heur
  find_theorems empty_conflict_and_extract_clause_heur
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
(* 
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
   extract_shorter_conflict_list_heur_st_fast_code.refine[OF isasat_input_bounded_nempty_axioms] *)

sepref_register find_lit_of_max_level_wl
   extract_shorter_conflict_list_heur_st lit_of_hd_trail_st_heur propagate_bt_wl_D_heur
   propagate_unit_bt_wl_D_int
sepref_register backtrack_wl_D
find_theorems extract_shorter_conflict_list_heur_st
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
(* 
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
   backtrack_wl_D_nlit_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms] *)

end

setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

end
