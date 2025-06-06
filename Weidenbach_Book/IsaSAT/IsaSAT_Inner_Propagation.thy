theory IsaSAT_Inner_Propagation
  imports IsaSAT_Setup
     IsaSAT_Clauses IsaSAT_VMTF IsaSAT_LBD
     IsaSAT_Inner_Propagation_Defs
begin

chapter \<open>Propagation: Inner Loop\<close>

declare all_atms_def[symmetric,simp]
lemma map_fun_rel_def2:
  \<open>\<langle>R\<rangle>map_fun_rel (D\<^sub>0 (all_atms_st u)) =
    {(m, f). \<forall>(i, j)\<in>(\<lambda>L. (nat_of_lit L, L)) ` set_mset (all_lits_st u). i < length m \<and> (m ! i, f j) \<in> R}\<close>
  unfolding map_fun_rel_def[of \<open>D\<^sub>0 (all_atms_st u)\<close> R] unfolding all_lits_st_alt_def[symmetric] ..

section \<open>Find replacement\<close>

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_nth2:
  fixes C :: nat
  assumes dom: \<open>C \<in># dom_m (get_clauses_wl S)\<close>
  shows \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S) (mset (get_clauses_wl S \<propto> C))\<close>
proof -
  let ?N = \<open>get_clauses_wl S\<close>
  have \<open>?N \<propto> C \<in># ran_mf ?N\<close>
    using dom by (auto simp: ran_m_def)
  then have \<open>mset (?N \<propto> C) \<in># mset `# (ran_mf ?N)\<close>
    by blast
  from all_lits_of_m_subset_all_lits_of_mmD[OF this] show ?thesis
    unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_def literals_are_\<L>\<^sub>i\<^sub>n_def
      all_lits_st_alt_def[symmetric]
    by (auto simp add: all_lits_st_def all_lits_of_mm_union all_lits_def)
qed


lemma isa_find_unwatched_between_find_in_list_between_spec:
  assumes \<open>a \<le> length (N \<propto> C)\<close> and \<open>b \<le> length (N \<propto> C)\<close> and \<open>a \<le> b\<close> and
    \<open>valid_arena arena N vdom\<close> and \<open>C \<in># dom_m N\<close> and eq: \<open>a' = a\<close> \<open>b' = b\<close>  \<open>C' = C\<close> and
    \<open>\<And>L. L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> P' L = P L\<close> and
    M'M: \<open>(M', M) \<in> trail_pol \<A>\<close>
  assumes lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (N \<propto> C))\<close>
  shows
    \<open>isa_find_unwatched_between P' M' arena a' b' C' \<le> \<Down> Id (find_in_list_between P a b (N \<propto> C))\<close>
proof -
  have find_in_list_between_alt:
      \<open>find_in_list_between P a b C = do {
          (x, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> a \<and> i \<le> length C \<and> i \<le> b \<and> (\<forall>j\<in>{a..<i}. \<not>P (C!j)) \<and>
            (\<forall>j. found = Some j \<longrightarrow> (i = j \<and> P (C ! j) \<and> j < b \<and> j \<ge> a))\<^esup>
            (\<lambda>(found, i). found = None \<and> i < b)
            (\<lambda>(_, i). do {
              ASSERT(i < length C);
              let L = C!i;
              if P L then RETURN (Some i, i) else RETURN (None, i+1)
            })
            (None, a);
          RETURN x
      }\<close> for P a b c C
    by (auto simp: find_in_list_between_def)
  have [refine0]: \<open>((None, x2m + a), None, a) \<in> \<langle>Id\<rangle>option_rel \<times>\<^sub>r {(n', n). n' = x2m + n}\<close>
    for x2m
    by auto
  have [simp]: \<open>arena_lit arena (C + x2) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> if \<open>x2 < length (N \<propto> C)\<close> for x2
    using that lits assms by (auto simp: arena_lifting
       dest!: literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<A> _ x2])
  have arena_lit_pre: \<open>arena_lit_pre arena x2a\<close>
    if
      \<open>(x, x') \<in> \<langle>nat_rel\<rangle>option_rel \<times>\<^sub>f {(n', n). n' = C + n}\<close> and
      \<open>case x of (found, i) \<Rightarrow> found = None \<and> i < C + b\<close> and
      \<open>case x' of (found, i) \<Rightarrow> found = None \<and> i < b\<close> and
      \<open>case x of (found, i) \<Rightarrow> True\<close> and
      \<open>case x' of
      (found, i) \<Rightarrow>
        a \<le> i \<and>
        i \<le> length (N \<propto> C) \<and>
        i \<le> b \<and>
        (\<forall>j\<in>{a..<i}. \<not> P (N \<propto> C ! j)) \<and>
        (\<forall>j. found = Some j \<longrightarrow> i = j \<and> P (N \<propto> C ! j) \<and> j < b \<and> a \<le> j)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x = (x1a, x2a)\<close> and
      \<open>x2 < length (N \<propto> C)\<close> and
      \<open>x2a < C + (arena_length arena C)\<close> and
      \<open>C \<le> x2a\<close>
    for x x' x1 x2 x1a x2a
  proof -
    show ?thesis
      unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
      apply (rule bex_leI[of _ C])
      apply (rule exI[of _ N])
      apply (rule exI[of _ vdom])
      using assms that by auto
  qed

  show ?thesis
    unfolding isa_find_unwatched_between_def find_in_list_between_alt eq
    apply (refine_vcg mop_arena_lit)
    subgoal using assms by (auto dest!: arena_lifting(10))
    subgoal using assms by (auto dest!: arena_lifting(10))
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto simp: arena_lifting)
    subgoal using assms by (auto simp: arena_lifting)
    subgoal by auto
    subgoal by (rule arena_lit_pre)
    apply (rule assms)
    subgoal using assms by (auto simp: arena_lifting)
    subgoal using assms by (auto simp: arena_lifting)
    subgoal
       by (rule polarity_pol_pre[OF M'M]) (use assms in \<open>auto simp: arena_lifting\<close>)
    subgoal using assms by (auto simp: arena_lifting)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition isa_find_non_false_literal_between where
  \<open>isa_find_non_false_literal_between M arena a b C =
     isa_find_unwatched_between (\<lambda>L. polarity_pol M L \<noteq> Some False) M arena a b C\<close>

definition find_unwatched
  :: \<open>(nat literal \<Rightarrow> bool) \<Rightarrow> (nat, nat literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> (nat option) nres\<close> where
\<open>find_unwatched M N C = do {
    ASSERT(C \<in># dom_m N);
    b \<leftarrow> SPEC(\<lambda>b::bool. True); \<comment> \<open>non-deterministic between full iteration (used in minisat),
      or starting in the middle (use in cadical)\<close>
    if b then find_in_list_between M 2 (length (N \<propto> C)) (N \<propto> C)
    else do {
      pos \<leftarrow> SPEC (\<lambda>i. i \<le> length (N \<propto> C) \<and> i \<ge> 2);
      n \<leftarrow> find_in_list_between M pos (length (N \<propto> C)) (N \<propto> C);
      if n = None then find_in_list_between M 2 pos (N \<propto> C)
      else RETURN n
    }
  }
\<close>

definition find_unwatched_wl_st_heur_pre where
  \<open>find_unwatched_wl_st_heur_pre =
     (\<lambda>(S, i). arena_is_valid_clause_idx (get_clauses_wl_heur S) i)\<close>

definition find_unwatched_wl_st'
  :: \<open>nat twl_st_wl \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_st' = (\<lambda>(M, N, D, Q, W, vm, \<phi>) i. do {
    find_unwatched (\<lambda>L. polarity M L \<noteq> Some False) N i
  })\<close>


(* TODO change to return the iterator (i) instead of the position in the clause *)

lemma find_unwatched_alt_def:
\<open>find_unwatched M N C = do {
    ASSERT(C \<in># dom_m N);
    _ \<leftarrow> RETURN(length (N \<propto> C));
    b \<leftarrow> SPEC(\<lambda>b::bool. True); \<comment> \<open>non-deterministic between full iteration (used in minisat),
      or starting in the middle (use in cadical)\<close>
    if b then find_in_list_between M 2 (length (N \<propto> C)) (N \<propto> C)
    else do {
      pos \<leftarrow> SPEC (\<lambda>i. i \<le> length (N \<propto> C) \<and> i \<ge> 2);
      n \<leftarrow> find_in_list_between M pos (length (N \<propto> C)) (N \<propto> C);
      if n = None then find_in_list_between M 2 pos (N \<propto> C)
      else RETURN n
    }
  }
\<close>
  unfolding find_unwatched_def by auto


lemma isa_find_unwatched_find_unwatched:
  assumes valid: \<open>valid_arena arena N vdom\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (N \<propto> C))\<close> and
    ge2: \<open>2 \<le> length (N \<propto> C)\<close> and
    M'M: \<open>(M', M) \<in> trail_pol \<A>\<close>
  shows \<open>isa_find_unwatched P M' arena C \<le> \<Down> Id (find_unwatched P N C)\<close>
proof -
  have [refine0]:
    \<open>C \<in># dom_m N \<Longrightarrow> (l, l') \<in> {(l, l'). (l, l') \<in> nat_rel \<and> l' = length (N \<propto> C)} \<Longrightarrow> RETURN(l \<le> MAX_LENGTH_SHORT_CLAUSE) \<le>
      \<Down> {(b,b'). b = b' \<and> (b \<longleftrightarrow> is_short_clause (N\<propto>C))}
        (SPEC (\<lambda>_. True))\<close>
    for l l'
    using assms
    by (auto simp: RETURN_RES_refine_iff is_short_clause_def arena_lifting)
  have [refine]: \<open>C \<in># dom_m N \<Longrightarrow> mop_arena_length arena C \<le> SPEC (\<lambda>c. (c, length (N \<propto> C)) \<in> {(l, l'). (l, l') \<in> nat_rel \<and> l' = length (N \<propto> C)})\<close>
    using assms unfolding mop_arena_length_def
    by refine_vcg (auto simp: arena_lifting arena_is_valid_clause_idx_def)
  show ?thesis
    unfolding isa_find_unwatched_def find_unwatched_alt_def
    apply (refine_vcg isa_find_unwatched_between_find_in_list_between_spec[of _ _ _ _ _ vdom _ _ _ \<A> _ _ ])
    apply assumption
    subgoal by auto
    subgoal using ge2 .
    subgoal by auto
    subgoal using ge2 .
    subgoal using valid .
    subgoal by fast
    subgoal using assms by (auto simp: arena_lifting)
    subgoal using assms by auto
    subgoal using assms by (auto simp: arena_lifting)
    apply (rule M'M)
    subgoal using assms by auto
    subgoal using assms unfolding get_saved_pos_pre_def arena_is_valid_clause_idx_def
      by (auto simp: arena_lifting)
    subgoal using assms arena_lifting[OF valid] unfolding get_saved_pos_pre_def
        mop_arena_pos_def
      by (auto simp: arena_lifting arena_pos_def)
    subgoal by (auto simp: arena_pos_def)
    subgoal using assms arena_lifting[OF valid] by auto
    subgoal using assms by auto
    subgoal using assms arena_lifting[OF valid] by auto
    subgoal using assms by auto
    subgoal using assms by (auto simp: arena_lifting)
    subgoal using assms by auto
    subgoal using assms arena_lifting[OF valid] by auto
    apply (rule M'M)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms arena_lifting[OF valid] by auto
    subgoal by (auto simp: arena_pos_def)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    apply (rule M'M)
    subgoal using assms by auto
    done
qed


lemma find_unwatched:
  assumes n_d: \<open>no_dup M\<close> and \<open>length (N \<propto> C) \<ge> 2\<close> and \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (N \<propto> C))\<close>
  shows \<open>find_unwatched (\<lambda>L. polarity M L \<noteq> Some False) N C \<le> \<Down> Id (find_unwatched_l M N C)\<close>
proof -
  have [refine0]: \<open>find_in_list_between (\<lambda>L. polarity M L \<noteq> Some False) 2 (length (N \<propto> C)) (N \<propto> C)
        \<le> SPEC
          (\<lambda>found.
              (found = None) = (\<forall>L\<in>set (unwatched_l (N \<propto> C) ). - L \<in> lits_of_l M) \<and>
              (\<forall>j. found = Some j \<longrightarrow>
                    j < length (N \<propto> C) \<and>
                    (undefined_lit M ((N \<propto> C) ! j) \<or> (N \<propto> C) ! j \<in> lits_of_l M) \<and> 2 \<le> j))\<close>
  proof -
    show ?thesis
      apply (rule order_trans)
      apply (rule find_in_list_between_spec)
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal
        using n_d
        by (auto simp add: polarity_def in_set_drop_conv_nth Ball_def
          Decided_Propagated_in_iff_in_lits_of_l split: if_splits dest: no_dup_consistentD)
      done
  qed
  have [refine0]: \<open>find_in_list_between (\<lambda>L. polarity M L \<noteq> Some False) xa (length (N \<propto> C)) (N \<propto> C)
        \<le> SPEC
          (\<lambda>n. (if n = None
                then find_in_list_between (\<lambda>L. polarity M L \<noteq> Some False) 2 xa (N \<propto> C)
                else RETURN n)
                \<le> SPEC
                  (\<lambda>found.
                      (found = None) =
                      (\<forall>L\<in>set (unwatched_l (N \<propto> C)). - L \<in> lits_of_l M) \<and>
                      (\<forall>j. found = Some j \<longrightarrow>
                            j < length (N \<propto> C) \<and>
                            (undefined_lit M ((N \<propto> C) ! j) \<or> (N \<propto> C) ! j \<in> lits_of_l M) \<and>
                            2 \<le> j)))\<close>
    if
      \<open>xa \<le> length (N \<propto> C) \<and> 2 \<le> xa\<close>
    for xa
  proof -
    show ?thesis
      apply (rule order_trans)
      apply (rule find_in_list_between_spec)
      subgoal using that by auto
      subgoal using assms by auto
      subgoal using that by auto
      subgoal
        apply (rule SPEC_rule)
        subgoal for x
          apply (cases \<open>x = None\<close>; simp only: if_True if_False refl)
        subgoal
          apply (rule order_trans)
          apply (rule find_in_list_between_spec)
          subgoal using that by auto
          subgoal using that by auto
          subgoal using that by auto
          subgoal
            apply (rule SPEC_rule)
            apply (intro impI conjI iffI ballI)
            unfolding in_set_drop_conv_nth Ball_def
            apply normalize_goal
            subgoal for x L xaa
              apply (cases \<open>xaa \<ge> xa\<close>)
              subgoal
                using n_d
                by (auto simp add: polarity_def  Ball_def all_conj_distrib
                Decided_Propagated_in_iff_in_lits_of_l split: if_splits dest: no_dup_consistentD)
              subgoal
                using n_d
                by (auto simp add: polarity_def  Ball_def all_conj_distrib
                Decided_Propagated_in_iff_in_lits_of_l split: if_splits dest: no_dup_consistentD)
              done
            subgoal for x  (* TODO Proof *)
              using n_d that assms
              apply (auto simp add: polarity_def  Ball_def all_conj_distrib
              Decided_Propagated_in_iff_in_lits_of_l split: if_splits dest: no_dup_consistentD,
                force)
              by (blast intro: dual_order.strict_trans1 dest: no_dup_consistentD)
            subgoal
              using n_d assms that
              by (auto simp add: polarity_def Ball_def all_conj_distrib
                Decided_Propagated_in_iff_in_lits_of_l
                  split: if_splits dest: no_dup_consistentD)
            done
          done
        subgoal (* TODO Proof *)
          using n_d that assms le_trans
          by (auto simp add: polarity_def  Ball_def all_conj_distrib in_set_drop_conv_nth
               Decided_Propagated_in_iff_in_lits_of_l split: if_splits dest: no_dup_consistentD)
            (use le_trans no_dup_consistentD in blast)+
        done
      done
    done
  qed

  show ?thesis
    unfolding find_unwatched_def find_unwatched_l_def
    apply (refine_vcg)
    subgoal by blast
    subgoal by blast
    subgoal by blast
    done
qed

definition find_unwatched_wl_st_pre where
  \<open>find_unwatched_wl_st_pre =  (\<lambda>(S, i).
    i \<in># dom_m (get_clauses_wl S) \<and> 2 \<le> length (get_clauses_wl S \<propto> i) \<and>
    literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S) (mset (get_clauses_wl S \<propto> i))
    )\<close>

theorem find_unwatched_wl_st_heur_find_unwatched_wl_s:
  \<open>(uncurry isa_find_unwatched_wl_st_heur, uncurry find_unwatched_wl_st')
    \<in> [find_unwatched_wl_st_pre]\<^sub>f
      twl_st_heur \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>((None, x2m + 2), None, 2) \<in> \<langle>Id\<rangle>option_rel \<times>\<^sub>r {(n', n). n' = x2m + n}\<close>
    for x2m
    by auto
  have [refine0]:
    \<open>(polarity M (arena_lit arena i'), polarity M' (N \<propto> C' ! j)) \<in> \<langle>Id\<rangle>option_rel\<close>
    if \<open>\<exists>vdom. valid_arena arena N vdom\<close> and
      \<open>C' \<in># dom_m N\<close> and
      \<open>i' = C' + j \<and> j < length (N \<propto> C')\<close> and
       \<open>M = M'\<close>
    for M arena i i' N j M' C'
    using that by (auto simp: arena_lifting)
  have [refine0]: \<open>RETURN (arena_pos arena C) \<le> \<Down> {(pos, pos'). pos = pos' \<and> pos \<ge> 2 \<and> pos \<le> length (N \<propto> C)}
         (SPEC (\<lambda>i. i \<le> length (N \<propto> C') \<and> 2 \<le> i))\<close>
    if valid: \<open>valid_arena arena N vdom\<close> and C: \<open>C \<in># dom_m N\<close> and \<open>C = C'\<close> and
       \<open>is_long_clause (N \<propto> C')\<close>
    for arena N vdom C C'
    using that arena_lifting[OF valid C] by (auto simp: RETURN_RES_refine_iff
      arena_pos_def)
  have [refine0]:
    \<open>RETURN (arena_length arena C \<le> MAX_LENGTH_SHORT_CLAUSE) \<le> \<Down> {(b, b'). b = b' \<and> (b \<longleftrightarrow> is_short_clause (N \<propto> C))}
     (SPEC(\<lambda>_. True))\<close>
    if valid: \<open>valid_arena arena N vdom\<close> and C: \<open>C \<in># dom_m N\<close>
    for arena N vdom C
    using that arena_lifting[OF valid C] by (auto simp: RETURN_RES_refine_iff is_short_clause_def)

  have [refine0]:
    \<open>C \<in># dom_m N \<Longrightarrow> (l, l') \<in> {(l, l'). (l, l') \<in> nat_rel \<and> l' = length (N \<propto> C)} \<Longrightarrow> RETURN(l \<le> MAX_LENGTH_SHORT_CLAUSE) \<le>
      \<Down> {(b,b'). b = b' \<and> (b \<longleftrightarrow> is_short_clause (N\<propto>C))}
        (SPEC (\<lambda>_. True))\<close>
    for l l' C N
    by (auto simp: RETURN_RES_refine_iff is_short_clause_def arena_lifting)
  have [refine]: \<open>C \<in># dom_m N \<Longrightarrow> valid_arena arena N vdom \<Longrightarrow>
     mop_arena_length arena C \<le> SPEC (\<lambda>c. (c, length (N \<propto> C)) \<in> {(l, l'). (l, l') \<in> nat_rel \<and> l' = length (N \<propto> C)})\<close>
    for N C arena vdom
    unfolding mop_arena_length_def
    by refine_vcg (auto simp: arena_lifting arena_is_valid_clause_idx_def)

  have H: \<open>isa_find_unwatched P M' arena C \<le> \<Down> Id (find_unwatched P' N C')\<close>
    if \<open>valid_arena arena N vdom\<close>
      \<open>\<And>L. L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> P L = P' L\<close> and
      \<open>C = C'\<close> and
      \<open>2 \<le> length (N \<propto> C')\<close> and \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (N \<propto> C'))\<close> and
      \<open>(M', M) \<in> trail_pol \<A>\<close>
    for arena P N C vdom P' C'  \<A> M' M
    using that unfolding isa_find_unwatched_def find_unwatched_alt_def supply [[goals_limit=1]]
    apply (refine_vcg isa_find_unwatched_between_find_in_list_between_spec[of _ _ _ _ _ vdom, where \<A>=\<A>])
    unfolding that apply assumption+
    subgoal by simp
    subgoal by auto
    subgoal using that by (simp add: arena_lifting)
    subgoal using that by auto
    subgoal using that by (auto simp: arena_lifting)
    apply assumption
    subgoal using that by (auto simp: arena_lifting get_saved_pos_pre_def
       arena_is_valid_clause_idx_def)
    subgoal using arena_lifting[OF \<open>valid_arena arena N vdom\<close>] unfolding get_saved_pos_pre_def
        mop_arena_pos_def
      by (auto simp: arena_lifting arena_pos_def)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    apply assumption
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    apply assumption
    done

  show ?thesis
    unfolding isa_find_unwatched_wl_st_heur_def find_unwatched_wl_st'_def
       uncurry_def twl_st_heur_def
      find_unwatched_wl_st_pre_def
    apply (intro frefI nres_relI)
    apply refine_vcg
    subgoal for x y
      apply (case_tac x, case_tac y)
      by (rule H[where \<A>3 = \<open>all_atms_st (fst y)\<close>, of _ _ \<open>set (get_vdom (fst x))\<close>])
        (auto simp: polarity_pol_polarity[of \<open>all_atms_st (fst y)\<close>,
	   unfolded option_rel_id_simp, THEN fref_to_Down_unRET_uncurry_Id]
	    all_atms_def[symmetric] literals_are_in_\<L>\<^sub>i\<^sub>n_nth2)
    done
qed


lemma isa_save_pos_is_Id:
  assumes
     \<open>(S, T) \<in> twl_st_heur\<close>
     \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
     \<open>i \<le> length (get_clauses_wl T \<propto> C)\<close> and
     \<open>i \<ge> 2\<close>
  shows \<open>isa_save_pos C i S \<le> \<Down> {(S', T'). (S', T') \<in> twl_st_heur \<and> length (get_clauses_wl_heur S') = length (get_clauses_wl_heur S) \<and>
       get_watched_wl_heur S' = get_watched_wl_heur S \<and> get_vdom S' = get_vdom S \<and> get_learned_count S' = get_learned_count S}
      (RETURN T)\<close>
proof -
  have  \<open>isa_update_pos_pre ((C, i), get_clauses_wl_heur S)\<close> if \<open>is_long_clause (get_clauses_wl T \<propto> C)\<close>
    unfolding isa_update_pos_pre_def
    using assms that
    by (cases S; cases T)
      (auto simp: isa_save_pos_def twl_st_heur_def arena_update_pos_alt_def
          isa_update_pos_pre_def arena_is_valid_clause_idx_def arena_lifting)
  then show ?thesis
    using assms
    by (cases S; cases T)
      (auto simp: isa_save_pos_def twl_st_heur_def arena_update_pos_alt_def
          isa_update_pos_pre_def arena_is_valid_clause_idx_def arena_lifting
          intro!: valid_arena_update_pos ASSERT_leI)
qed


section \<open>Updates\<close>

lemma isa_vmtf_bump_to_rescore_also_reasons_cl_isa_vmtf:
  assumes \<open>(M,M')\<in>trail_pol \<A>\<close> \<open>isasat_input_bounded \<A>\<close> and vm: \<open>vm \<in> bump_heur \<A> M'\<close> and
    valid: \<open>valid_arena N N' vd\<close> and
    C: \<open>C \<in># dom_m N'\<close> and
    H:\<open> \<forall>L\<in>set (N' \<propto> C). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
    \<open>\<forall>L\<in>set (N' \<propto> C).
    \<forall>C. Propagated (- L) C \<in> set M' \<longrightarrow>
    C \<noteq> 0 \<longrightarrow> C \<in># dom_m N' \<and> (\<forall>C\<in>set [C..<C + arena_length N C]. arena_lit N C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and
    bound: \<open>isasat_input_bounded \<A>\<close>
  shows
    \<open>isa_vmtf_bump_to_rescore_also_reasons_cl M N C L vm \<le> RES (bump_heur \<A> M')\<close>
proof -
  show ?thesis
    apply (rule order_trans)
    apply (rule isa_vmtf_bump_to_rescore_also_reasons_cl_vmtf_mark_to_rescore_also_reasons_cl[
        where \<A> = \<A>,
        THEN fref_to_Down_curry4,
          of  _ _  _ _ _ \<open>M'\<close> \<open>N\<close> C L vm])
   subgoal using assms by auto
   subgoal using assms by auto
   subgoal
     apply (rule order_trans)
     apply (rule ref_two_step')
     apply (rule vmtf_mark_to_rescore_also_reasons_cl_spec[OF vm valid C bound H])
     subgoal by (auto simp: conc_fun_RES)
     done
  done
qed

lemma mark_conflict_to_rescore:
  assumes \<open>(S,T)\<in>twl_st_heur_up'' \<D> r s K lcount\<close>
    \<open>set_conflict_wl_pre C T\<close>
  shows \<open>mark_conflict_to_rescore C S \<le> SPEC(\<lambda>S'. (S', T)\<in> twl_st_heur_up'' \<D> r s K lcount)\<close>
proof -
  obtain U V b where
    TU: \<open>(T, U) \<in> state_wl_l b\<close> and
    C: \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    list: \<open>twl_list_invs U\<close>
    using assms(2) unfolding set_conflict_wl_pre_def set_conflict_l_pre_def apply -
    apply normalize_goal+
    by auto
  have valid: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl T) (set (get_vdom S))\<close> and
    vm: \<open>get_vmtf_heur S \<in> bump_heur (all_atms_st T) (get_trail_wl T)\<close> and
    bounded: \<open>isasat_input_bounded (all_atms_st T)\<close> and
    trail: \<open> (get_trail_wl_heur S, get_trail_wl T) \<in> trail_pol (all_atms_st T)\<close>
    using assms unfolding arena_is_valid_clause_idx_def unfolding twl_st_heur'_def
      twl_st_heur_def by auto
  have H:\<open> \<forall>L\<in>set (get_clauses_wl T \<propto> C). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st T)\<close>
    \<open>\<forall>L\<in>set (get_clauses_wl T \<propto> C).
    \<forall>C. Propagated (- L) C \<in> set (get_trail_wl T) \<longrightarrow>
    C \<noteq> 0 \<longrightarrow> C \<in># dom_m (get_clauses_wl T) \<and> (\<forall>C\<in>set [C..<C + arena_length (get_clauses_wl_heur S) C]. arena_lit (get_clauses_wl_heur S) C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st T))\<close>
    subgoal
      using valid C by (auto simp: arena_lifting in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
        all_atms_st_def all_atms_def all_lits_def all_lits_of_mm_union ran_m_def all_lits_of_mm_add_mset image_Un
        atm_of_all_lits_of_m(2)
        dest!: multi_member_split[of C]
        simp del: all_atms_def[symmetric])[]
    apply (intro ballI allI)
    subgoal for L D
      apply (intro conjI ballI impI)
      subgoal
        using TU list by (auto simp: twl_list_invs_def dest!: spec[of _ \<open>-L\<close>] spec[of _ \<open>D\<close>])
      subgoal for C
        apply (subgoal_tac \<open>C - D < length (get_clauses_wl T \<propto> D)\<close>)
        using TU list arena_lifting(5)[OF valid, of D \<open>C - D\<close>,symmetric]
        apply (auto simp: twl_list_invs_def dest!: spec[of _ \<open>-L\<close>] spec[of _ \<open>D\<close>])
        using valid
        apply (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
          all_atms_st_def all_atms_def all_lits_def all_lits_of_mm_union ran_m_def all_lits_of_mm_add_mset image_Un
          atm_of_all_lits_of_m(2) arena_lifting
          dest!: multi_member_split[of D] spec[of _ \<open>-L\<close>] spec[of _ \<open>D\<close>]
          simp del: all_atms_def[symmetric])
        apply (metis (no_types, opaque_lifting) \<open>\<lbrakk>D \<in># dom_m (get_clauses_wl T); C - D < length (get_clauses_wl T \<propto> D)\<rbrakk> \<Longrightarrow> arena_lit (get_clauses_wl_heur S) (D + (C - D)) = get_clauses_wl T \<propto> D ! (C - D)\<close> add.commute add.right_neutral add_diff_inverse_nat arena_lifting(4) imageI less_diff_conv2 less_nat_zero_code member_add_mset nth_mem)
        apply (metis (no_types, opaque_lifting) \<open>\<lbrakk>D \<in># dom_m (get_clauses_wl T); C - D < length (get_clauses_wl T \<propto> D)\<rbrakk> \<Longrightarrow> arena_lit (get_clauses_wl_heur S) (D + (C - D)) = get_clauses_wl T \<propto> D ! (C - D)\<close> add.commute add.right_neutral add_diff_inverse_nat arena_lifting(4) imageI less_diff_conv2 less_nat_zero_code member_add_mset nth_mem)
        done
      done
    done
  have H': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st T) (mset (get_clauses_wl T \<propto> C))\<close>
    by (simp add: C literals_are_in_\<L>\<^sub>i\<^sub>n_nth2)
  show ?thesis
    unfolding mark_conflict_to_rescore_def mop_arena_length_def nres_monad3 mop_arena_lit2_def
    apply (refine_vcg WHILET_rule[where \<Phi> = \<open>\<lambda>(i,vm). vm \<in> bump_heur (all_atms_st T) (get_trail_wl T)\<close> and
      I = \<open>\<lambda>(i,vm). i \<le> length (get_clauses_wl T \<propto> C) \<and> vm \<in> bump_heur (all_atms_st T) (get_trail_wl T)\<close> and
      R = \<open>measure (\<lambda>(i,vm). length (get_clauses_wl T \<propto> C) -i)\<close>] trail bounded valid
      isa_vmtf_bump_to_rescore_also_reasons_cl_isa_vmtf[THEN order_trans]
      calculate_LBD_heur_st_calculate_LBD_st[where
        vdom = \<open>set (get_vdom (S))\<close> and \<A> = \<open>all_atms_st T\<close> and C'=C, unfolded calculate_LBD_st_def conc_fun_RES RETURN_def, THEN order_trans])
    subgoal using C valid unfolding arena_is_valid_clause_idx_def by auto
    subgoal using valid C arena_lifting(7)[OF valid C, of \<open>length (get_clauses_wl T \<propto> C) - 1\<close>] by (auto simp: arena_lifting)
    subgoal by auto
    subgoal by auto
    subgoal using vm by auto
    subgoal by auto
    subgoal using valid C by (auto simp:arena_lifting arena_lit_pre_def
      arena_is_valid_clause_idx_and_access_def intro!: exI[of _ C] exI[of _ \<open>get_clauses_wl T\<close>])
    subgoal by auto
    subgoal using C by auto
    subgoal by (rule H)
    subgoal by (rule H)
    subgoal using valid C by (auto simp: arena_lifting)
    subgoal by auto
    subgoal using valid C by (auto simp: arena_lifting)
    subgoal by auto
    subgoal using C by auto
    subgoal by (rule H')
    subgoal by auto
    subgoal using assms unfolding twl_st_heur'_def twl_st_heur_def by auto
    done
qed



definition set_conflict_wl_heur_pre where
  \<open>set_conflict_wl_heur_pre =
     (\<lambda>(C, S). True)\<close>

definition update_clause_wl_pre where
  \<open>update_clause_wl_pre K r = (\<lambda>((((((((L, L'), C), b), j), w), i), f), S).
     L = K)\<close>
lemma arena_lit_pre:
  \<open>valid_arena NU N vdom \<Longrightarrow> C \<in># dom_m N \<Longrightarrow> i < length (N \<propto> C) \<Longrightarrow> arena_lit_pre NU (C + i)\<close>
  unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
  by (rule bex_leI[of _ C], rule exI[of _ N], rule exI[of _ vdom]) auto

lemma all_atms_swap[simp]:
  \<open>C \<in># dom_m N \<Longrightarrow> i < length (N \<propto> C) \<Longrightarrow> j < length (N \<propto> C) \<Longrightarrow>
  all_atms (N(C \<hookrightarrow> swap (N \<propto> C) i j)
) = all_atms N\<close>
  unfolding all_atms_def
  by (auto simp del: all_atms_def[symmetric] simp: all_atms_def  intro!: ext)

lemma mop_arena_swap[mop_arena_lit]:
  assumes valid: \<open>valid_arena arena N vdom\<close> and
    i: \<open>(C, C') \<in> nat_rel\<close> \<open>(i, i') \<in> nat_rel\<close> \<open>(j, j') \<in> nat_rel\<close>
  shows
    \<open>mop_arena_swap C i j arena \<le> \<Down>{(N'', N'). valid_arena N'' N' vdom \<and> N'' = swap_lits C' i' j' arena
      \<and> N' = op_clauses_swap N C' i' j' \<and> all_atms N' = all_atms N \<and> i' < length (N \<propto> C') \<and>
      j' < length (N \<propto> C')} (mop_clauses_swap N C' i' j')\<close>
  using assms unfolding mop_clauses_swap_def mop_arena_swap_def swap_lits_pre_def
  by refine_rcg
    (auto simp: arena_lifting valid_arena_swap_lits op_clauses_swap_def)

lemma update_clause_wl_alt_def:
  \<open>update_clause_wl = (\<lambda>(L::'v literal) L' C b j w i f (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
     ASSERT(C \<in># dom_m N \<and> j \<le> w \<and> w < length (W L) \<and>
        correct_watching_except (Suc j) (Suc w) L (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
     ASSERT(L \<in># all_lits_st (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
     ASSERT(L' \<in># all_lits_st (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
     K' \<leftarrow> mop_clauses_at N C f;
     ASSERT(K' \<in>#  all_lits_st (M, N,  D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<and> L \<noteq> K');
     N' \<leftarrow> mop_clauses_swap N C i f;
     RETURN (j, w+1, (M, N', D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W(K' := W K' @ [(C, L, b)])))
  })\<close>
  unfolding update_clause_wl_def by (auto intro!: ext bind_cong[OF refl] simp flip: all_lits_alt_def2)

lemma all_atms_st_simps[simp]:
   \<open>all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W(K := WK)) =
   all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
   \<open>all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, add_mset K Q, W) =
   all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close> \<comment> \<open>actually covered below, but still useful for 'unfolding' by hand\<close>
  \<open>x1 \<in># dom_m x1aa \<Longrightarrow> n < length (x1aa \<propto> x1) \<Longrightarrow> n' < length (x1aa \<propto> x1) \<Longrightarrow>
     all_atms_st (x1b, x1aa(x1 \<hookrightarrow> WB_More_Refinement_List.swap (x1aa \<propto> x1) n n'), D, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e,
             x2e) =
   all_atms_st
            (x1b, x1aa, D, x1c, x1d, NEk, UEk, NS, US, N0, U0, x1e,
             x2e)\<close>
  \<open>all_atms_st (L # M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
    all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>NO_MATCH {#} Q \<Longrightarrow> all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
     all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, W)\<close>
  \<open>NO_MATCH [] M \<Longrightarrow> all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
     all_atms_st ([], N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>NO_MATCH None D \<Longrightarrow> all_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) =
  all_atms_st (M, N, None, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)\<close>
  \<open>all_atms_st (set_literals_to_update_wl WS S) = all_atms_st S\<close>
  by (cases S; auto simp: all_atms_st_def all_atms_def ran_m_clause_upd
    image_mset_remove1_mset_if simp del: all_atms_def[symmetric]; fail)+


lemma update_clause_wl_heur_update_clause_wl:
  \<open>(uncurry8 update_clause_wl_heur, uncurry8 (update_clause_wl)) \<in>
   [update_clause_wl_pre K r]\<^sub>f
   Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur_up'' \<D> r s K lcount \<rightarrow>
  \<langle>nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r twl_st_heur_up'' \<D> r s K lcount\<rangle>nres_rel\<close>
  unfolding update_clause_wl_heur_def update_clause_wl_alt_def uncurry_def
    update_clause_wl_pre_def all_lits_of_all_atms_of all_lits_of_all_atms_of Let_def
  apply (intro frefI nres_relI, case_tac x, case_tac y)
  apply (refine_rcg)
  apply (rule mop_arena_lit2')
  subgoal by  (auto 0 0 simp: update_clause_wl_heur_def update_clause_wl_def twl_st_heur_def Let_def
      map_fun_rel_def2 twl_st_heur'_def update_clause_wl_pre_def arena_lifting arena_lit_pre_def
      arena_is_valid_clause_idx_and_access_def swap_lits_pre_def
    intro!: ASSERT_refine_left valid_arena_swap_lits
    intro!: bex_leI exI)
  subgoal by auto
  subgoal by auto
  subgoal by
     (auto 0 0 simp: update_clause_wl_heur_def update_clause_wl_def twl_st_heur_def Let_def
      map_fun_rel_def2 twl_st_heur'_def update_clause_wl_pre_def arena_lifting arena_lit_pre_def
      arena_is_valid_clause_idx_and_access_def swap_lits_pre_def
    intro!: ASSERT_refine_left valid_arena_swap_lits
    intro!: bex_leI exI)
  apply (rule_tac vdom= \<open>set (get_vdom ((\<lambda>(((((((L,C),b),j),w),_),_),x). x) x))\<close> in mop_arena_swap)
  subgoal
    by (auto 0 0 simp: twl_st_heur_def Let_def
      map_fun_rel_def2 twl_st_heur'_def update_clause_wl_pre_def arena_lifting arena_lit_pre_def
    intro!: ASSERT_refine_left valid_arena_swap_lits dest!: multi_member_split[of \<open>arena_lit _ _\<close>])
  subgoal
    by (auto 0 0 simp: twl_st_heur_def Let_def
      map_fun_rel_def2 twl_st_heur'_def update_clause_wl_def arena_lifting arena_lit_pre_def
    intro!: ASSERT_refine_left valid_arena_swap_lits dest!: multi_member_split[of \<open>arena_lit _ _\<close>])
  subgoal
    by (auto 0 0 simp: twl_st_heur_def Let_def
      map_fun_rel_def2 twl_st_heur'_def update_clause_wl_def arena_lifting arena_lit_pre_def
    intro!: ASSERT_refine_left valid_arena_swap_lits dest!: multi_member_split[of \<open>arena_lit _ _\<close>])
  subgoal
    by (auto 0 0 simp: twl_st_heur_def Let_def
      map_fun_rel_def2 twl_st_heur'_def update_clause_wl_pre_def arena_lifting arena_lit_pre_def
    intro!: ASSERT_refine_left valid_arena_swap_lits dest!: multi_member_split[of \<open>arena_lit _ _\<close>])
  subgoal
    by (auto simp: twl_st_heur_def Let_def add_mset_eq_add_mset all_lits_of_all_atms_of ac_simps
      twl_st_heur'_def update_clause_wl_pre_def arena_lifting arena_lit_pre_def map_fun_rel_def2
    dest: multi_member_split simp flip: all_lits_def all_lits_alt_def2
    intro!: ASSERT_refine_left valid_arena_swap_lits)
  subgoal for x y a b aa ba c d e f g h i j k l m n x1 x1a x1b x1c x1d x1e x1f x2 x2a x2b x2c x2d x2e x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m
    x1n x2n x1o x2o x1p x2p x1q x2q x1r x2r x1s x1t x1u x1v x1w x1x x1y x2s x2t x2u x2v x2w x2x x2y _ _ _ _ K' K'a N' N'a
    by (auto dest!: length_watched_le2[of _ _ _ _ \<open>b\<close> \<D> r lcount K'a])
      (simp_all add: twl_st_heur'_def twl_st_heur_def map_fun_rel_def2)
  subgoal
    by
     (clarsimp simp: twl_st_heur_def Let_def
      map_fun_rel_def2 twl_st_heur'_def update_clause_wl_pre_def
      op_clauses_swap_def)
  done



definition propagate_lit_wl_heur_pre where
  \<open>propagate_lit_wl_heur_pre =
     (\<lambda>((L, C), S). C \<noteq> DECISION_REASON)\<close>

definition propagate_lit_wl_pre where
  \<open>propagate_lit_wl_pre = (\<lambda>(((L, C), i), S).
     undefined_lit (get_trail_wl S) L \<and> get_conflict_wl S = None \<and>
     C \<in># dom_m (get_clauses_wl S) \<and> L \<in># all_lits_st S \<and>
    1 - i < length (get_clauses_wl S \<propto> C) \<and>
    0 < length (get_clauses_wl S \<propto> C))\<close>

lemma propagate_lit_wl_heur_propagate_lit_wl:
  \<open>(uncurry3 propagate_lit_wl_heur, uncurry3 (propagate_lit_wl)) \<in>
  [\<lambda>_. True]\<^sub>f
  Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur_up'' \<D> r s K lcount \<rightarrow> \<langle>twl_st_heur_up'' \<D> r s K lcount\<rangle>nres_rel\<close>
  supply [[goals_limit=1]]
  unfolding propagate_lit_wl_heur_def propagate_lit_wl_def Let_def
  apply (intro frefI nres_relI) unfolding uncurry_def mop_save_phase_heur_def
    nres_monad3
  apply (refine_rcg)
  subgoal by auto
  apply (rule_tac \<A> = \<open>all_atms_st (snd y)\<close> in cons_trail_Propagated_tr2)
  subgoal by (auto 4 3 simp: twl_st_heur_def propagate_lit_wl_heur_def propagate_lit_wl_def
        isa_vmtf_consD twl_st_heur'_def propagate_lit_wl_pre_def swap_lits_pre_def
        valid_arena_swap_lits arena_lifting phase_saving_def atms_of_def save_phase_def
     ac_simps
      intro!: ASSERT_refine_left cons_trail_Propagated_tr2 cons_trail_Propagated_tr_pre
      dest: multi_member_split valid_arena_DECISION_REASON)
  subgoal
   by  (auto simp: twl_st_heur_def twl_st_heur'_def all_lits_st_alt_def[symmetric]
     ac_simps)
  subgoal by (auto 4 3 simp: twl_st_heur_def propagate_lit_wl_heur_def propagate_lit_wl_def
        isa_vmtf_consD twl_st_heur'_def propagate_lit_wl_pre_def swap_lits_pre_def
        valid_arena_swap_lits arena_lifting phase_saving_def atms_of_def save_phase_def
      intro!: ASSERT_refine_left cons_trail_Propagated_tr2 cons_trail_Propagated_tr_pre
      dest: multi_member_split valid_arena_DECISION_REASON)
  apply (rule_tac vdom = \<open>set (get_vdom (snd x))\<close> in mop_arena_swap)
  subgoal by (auto 4 3 simp: twl_st_heur_def propagate_lit_wl_heur_def propagate_lit_wl_def
        isa_vmtf_consD twl_st_heur'_def propagate_lit_wl_pre_def swap_lits_pre_def
        valid_arena_swap_lits arena_lifting phase_saving_def atms_of_def save_phase_def
      intro!: ASSERT_refine_left cons_trail_Propagated_tr2 cons_trail_Propagated_tr_pre
      dest: multi_member_split valid_arena_DECISION_REASON)
  subgoal by (auto 4 3 simp: twl_st_heur_def propagate_lit_wl_heur_def propagate_lit_wl_def
        isa_vmtf_consD twl_st_heur'_def propagate_lit_wl_pre_def swap_lits_pre_def
        valid_arena_swap_lits arena_lifting phase_saving_def atms_of_def save_phase_def
      intro!: ASSERT_refine_left cons_trail_Propagated_tr2 cons_trail_Propagated_tr_pre
      dest: multi_member_split valid_arena_DECISION_REASON)
  subgoal by (auto 4 3 simp: twl_st_heur_def propagate_lit_wl_heur_def propagate_lit_wl_def
        isa_vmtf_consD twl_st_heur'_def propagate_lit_wl_pre_def swap_lits_pre_def
        valid_arena_swap_lits arena_lifting phase_saving_def atms_of_def save_phase_def
      intro!: ASSERT_refine_left cons_trail_Propagated_tr2 cons_trail_Propagated_tr_pre
      dest: multi_member_split valid_arena_DECISION_REASON)
  subgoal by (auto simp: twl_st_heur_def propagate_lit_wl_heur_def propagate_lit_wl_def
        isa_vmtf_consD twl_st_heur'_def propagate_lit_wl_pre_def swap_lits_pre_def
        valid_arena_swap_lits arena_lifting phase_saving_def atms_of_def save_phase_def
      intro!: ASSERT_refine_left cons_trail_Propagated_tr2 cons_trail_Propagated_tr_pre
      dest: multi_member_split valid_arena_DECISION_REASON)
  subgoal by (auto simp: twl_st_heur_def propagate_lit_wl_heur_def propagate_lit_wl_def
        isa_vmtf_consD twl_st_heur'_def propagate_lit_wl_pre_def swap_lits_pre_def
        valid_arena_swap_lits arena_lifting phase_saving_def
        all_lits_st_alt_def[symmetric] ac_simps
        intro!: save_phase_heur_preI)
  subgoal for x y
    by (cases x; cases y; hypsubst)
     (clarsimp simp add: twl_st_heur_def twl_st_heur'_def isa_vmtf_consD
      op_clauses_swap_def ac_simps)
   done

definition propagate_lit_wl_bin_pre where
  \<open>propagate_lit_wl_bin_pre = (\<lambda>(((L, C), i), S).
     undefined_lit (get_trail_wl S) L \<and> get_conflict_wl S = None \<and>
     C \<in># dom_m (get_clauses_wl S) \<and> L \<in># all_lits_st S)\<close>

lemma propagate_lit_wl_bin_heur_propagate_lit_wl_bin:
  \<open>(uncurry2 propagate_lit_wl_bin_heur, uncurry2 (propagate_lit_wl_bin)) \<in>
  [\<lambda>_. True]\<^sub>f
  nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur_up'' \<D> r s K lcount \<rightarrow> \<langle>twl_st_heur_up'' \<D> r s K lcount\<rangle>nres_rel\<close>
  supply [[goals_limit=1]]
  unfolding propagate_lit_wl_bin_heur_def propagate_lit_wl_bin_def Let_def
  apply (intro frefI nres_relI) unfolding uncurry_def mop_save_phase_heur_def nres_monad3
  apply (refine_rcg)
  apply (rule_tac \<A> = \<open>all_atms_st (snd y)\<close> in cons_trail_Propagated_tr2)
  subgoal by (auto 4 3 simp: twl_st_heur_def propagate_lit_wl_bin_heur_def propagate_lit_wl_bin_def
        isa_vmtf_consD twl_st_heur'_def propagate_lit_wl_bin_pre_def swap_lits_pre_def
        arena_lifting phase_saving_def atms_of_def save_phase_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits
        all_lits_def ac_simps
      intro!: ASSERT_refine_left cons_trail_Propagated_tr2 cons_trail_Propagated_tr_pre
      dest: multi_member_split valid_arena_DECISION_REASON)
  subgoal by (auto 4 3 simp: twl_st_heur_def twl_st_heur'_def propagate_lit_wl_bin_pre_def swap_lits_pre_def
        arena_lifting phase_saving_def atms_of_def save_phase_def all_lits_st_alt_def[symmetric]
      intro!: ASSERT_refine_left cons_trail_Propagated_tr2 cons_trail_Propagated_tr_pre
      dest: multi_member_split valid_arena_DECISION_REASON
        intro!: save_phase_heur_preI)
  subgoal by (auto 4 3 simp: twl_st_heur_def twl_st_heur'_def propagate_lit_wl_bin_pre_def swap_lits_pre_def
        arena_lifting phase_saving_def atms_of_def save_phase_def  all_lits_st_alt_def[symmetric] ac_simps
      intro!: ASSERT_refine_left cons_trail_Propagated_tr2 cons_trail_Propagated_tr_pre
      dest: multi_member_split valid_arena_DECISION_REASON)
  subgoal by (auto 4 3 simp: twl_st_heur_def twl_st_heur'_def propagate_lit_wl_bin_pre_def swap_lits_pre_def
        arena_lifting phase_saving_def atms_of_def save_phase_def all_lits_st_alt_def[symmetric]
      intro!: ASSERT_refine_left cons_trail_Propagated_tr2 cons_trail_Propagated_tr_pre
      dest: multi_member_split valid_arena_DECISION_REASON
        intro!: save_phase_heur_preI)
  subgoal for x y
    by (cases x; cases y; hypsubst)
     (clarsimp simp add: ac_simps twl_st_heur_def twl_st_heur'_def isa_vmtf_consD
      op_clauses_swap_def)
  done

lemma pos_of_watched_alt:
  \<open>pos_of_watched N C L = do {
     ASSERT(length (N \<propto> C) > 0 \<and> C \<in># dom_m N);
     let L' = (N \<propto> C) ! 0;
     RETURN (if L' = L then 0 else 1)
  }\<close>
  unfolding pos_of_watched_def Let_def by auto

lemma pos_of_watched_heur:
  \<open>(S, S') \<in> {(T, T').  get_vdom T = get_vdom x2e \<and> (T, T') \<in> twl_st_heur_up'' \<D> r s t lcount} \<Longrightarrow>
   ((C, L), (C', L')) \<in> Id \<times>\<^sub>r Id \<Longrightarrow>
   pos_of_watched_heur S C L \<le> \<Down> nat_rel (pos_of_watched (get_clauses_wl S') C' L')\<close>
   unfolding pos_of_watched_heur_def pos_of_watched_alt mop_access_lit_in_clauses_heur_def
   by (refine_rcg mop_arena_lit[where vdom = \<open>set (get_vdom S)\<close>])
     (auto simp: twl_st_heur'_def twl_st_heur_def)

lemma other_watched_heur:
  \<open>(S, S') \<in> {(T, T').  get_vdom T = get_vdom x2e \<and> (T, T') \<in> twl_st_heur_up'' \<D> r s t lcount} \<Longrightarrow>
   ((L, C, i), (L', C', i')) \<in> Id \<times>\<^sub>r Id \<Longrightarrow>
   other_watched_wl_heur S L C i \<le> \<Down> Id (other_watched_wl S' L' C' i')\<close>
   using arena_lifting(5,7)[of \<open>get_clauses_wl_heur S\<close> \<open>get_clauses_wl S'\<close> _ C i]
   unfolding other_watched_wl_heur_def other_watched_wl_def
     mop_access_lit_in_clauses_heur_def
   by (refine_rcg mop_arena_lit[where vdom = \<open>set (get_vdom S)\<close>])
     (auto simp: twl_st_heur'_def twl_st_heur_def
     arena_lit_pre2_def
     intro!: exI[of _ \<open>get_clauses_wl S'\<close>])


section \<open>Full inner loop\<close>

declare RETURN_as_SPEC_refine[refine2 del]

definition set_conflict_wl'_pre where
  \<open>set_conflict_wl'_pre i S \<longleftrightarrow>
    get_conflict_wl S = None \<and> i \<in># dom_m (get_clauses_wl S) \<and>
    literals_are_in_\<L>\<^sub>i\<^sub>n_mm (all_atms_st S) (mset `# ran_mf (get_clauses_wl S)) \<and>
    \<not> tautology (mset (get_clauses_wl S \<propto> i)) \<and>
    distinct (get_clauses_wl S \<propto> i) \<and>
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st S) (get_trail_wl S)\<close>

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mm_clauses[simp]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (all_atms_st S) (mset `# ran_mf (get_clauses_wl S))\<close>
   \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (all_atms_st S) ((\<lambda>x. mset (fst x)) `# ran_m (get_clauses_wl S))\<close>
  apply (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def  all_lits_st_alt_def[symmetric]
    all_lits_st_def all_lits_def all_lits_of_mm_union)
  done

lemma set_conflict_wl_alt_def:
  \<open>set_conflict_wl = (\<lambda>C S. do {
     ASSERT(set_conflict_wl_pre C S);
     let (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) = S;
     let D = Some (mset (N \<propto> C));
     j \<leftarrow> RETURN (length M);
     RETURN (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, W)
    })\<close>
  unfolding set_conflict_wl_def Let_def by (auto simp: ac_simps)

lemma set_conflict_wl_pre_set_conflict_wl'_pre:
  assumes \<open>set_conflict_wl_pre C S\<close>
  shows \<open>set_conflict_wl'_pre C S\<close>
proof -
  obtain S' T b b'  where
    SS': \<open>(S, S') \<in> state_wl_l b\<close> and
    \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close> and
    confl: \<open>get_conflict_l  S'= None\<close> and
    dom: \<open>C \<in># dom_m (get_clauses_l S')\<close> and
    tauto: \<open>\<not> tautology (mset (get_clauses_l S' \<propto> C))\<close> and
    dist: \<open>distinct (get_clauses_l S' \<propto> C)\<close> and
    \<open>get_trail_l S' \<Turnstile>as CNot (mset (get_clauses_l S'  \<propto> C))\<close> and
    T: \<open>(set_clauses_to_update_l (clauses_to_update_l S' + {#C#}) S', T)
     \<in> twl_st_l b'\<close> and
    struct: \<open>twl_struct_invs T\<close> and
    \<open>twl_stgy_invs T\<close>
    using assms
    unfolding set_conflict_wl_pre_def set_conflict_l_pre_def apply -
    by blast
  have lits_trail: \<open>lits_of_l (get_trail T) \<subseteq> set_mset (all_lits_of_st T)\<close>
    using twl_struct_invs_no_alien_in_trail[OF struct] by auto
  then have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st S) (get_trail_wl S)\<close>
    using T SS'
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_atm_of lits_of_def all_lits_st_alt_def)
  then show ?thesis
     using SS'  T dom tauto dist confl unfolding set_conflict_wl'_pre_def
     by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def twl_st_l
       mset_take_mset_drop_mset' simp del: all_atms_def[symmetric])
qed

lemma set_conflict_wl_heur_set_conflict_wl':
  \<open>(uncurry set_conflict_wl_heur, uncurry (set_conflict_wl)) \<in>
    [\<lambda>_. True]\<^sub>f
    nat_rel \<times>\<^sub>r twl_st_heur_up'' \<D> r s K lcount \<rightarrow> \<langle>twl_st_heur_up'' \<D> r s K lcount\<rangle>nres_rel\<close>
proof -
  have H:
    \<open>isa_set_lookup_conflict_aa x y z a b d
        \<le> \<Down> (option_lookup_clause_rel \<A> \<times>\<^sub>f (nat_rel \<times>\<^sub>f Id))
           (set_conflict_m x' y' z' a' b' d')\<close>
    if
      \<open>(((((((x, y), z), a), b)), d), (((((x', y'), z'), a'), b')), d')
      \<in> trail_pol \<A> \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f
        nat_rel \<times>\<^sub>f
        option_lookup_clause_rel \<A> \<times>\<^sub>f
        nat_rel \<times>\<^sub>f Id\<close> and
        \<open>z' \<in># dom_m y' \<and> a' = None \<and> distinct (y' \<propto> z') \<and>
          literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf y') \<and>
         \<not> tautology (mset (y' \<propto> z')) \<and> b' = 0 \<and> out_learned x' None d' \<and>
	 isasat_input_bounded \<A>\<close>
      for x x' y y' z z' a a' b b' c c' d d' vdom \<A>
    by (rule isa_set_lookup_conflict[THEN fref_to_Down_curry5,
      unfolded prod.case, OF that(2,1)])

  have [refine0]: \<open>isa_set_lookup_conflict_aa (get_trail_wl_heur x2g) (get_clauses_wl_heur x2g) x1g
     (get_conflict_wl_heur x2g) 0 (get_outlearned_heur x2g)
        \<le> \<Down> {((C, n, outl), D). (C, D) \<in> option_lookup_clause_rel (all_atms_st x2) \<and>
	       n = card_max_lvl x1a (the D) \<and> out_learned x1a D outl}
          (RETURN (Some (mset (x1b \<propto> x1))))\<close>
    if
      \<open>(x, y) \<in> nat_rel \<times>\<^sub>f twl_st_heur_up'' \<D> r s K lcount\<close> and
      \<open>x2i' = (x1j', x2j')\<close> and
      \<open>x2h' = (x1i', x2i')\<close> and
      \<open>x2g' = (x1h', x2h')\<close> and
      \<open>x2f = (x1g', x2g')\<close> and
      \<open>x2e = (x1f, x2f)\<close> and
      \<open>x2d = (x1e, x2e)\<close> and
      \<open>x2c = (x1d, x2d)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x = (x1g, S)\<close> and
      \<open>(x2g, x2) \<in> twl_st_heur_up'' \<D> r s K lcount\<close>
      \<open>case y of (x, xa) \<Rightarrow> set_conflict_wl'_pre x xa\<close>
    for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h
       x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q x2q
       x1r x2r x1s x2s x1t x2t x1g' x2g' x1h' x2h' x1i' x2i' x1j' x2j' S
  proof -
    have [iff]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm
             (all_atms_st ([], x1b, None, x1d, x1e, x1f, xaa, af, ag, ah, ai, {#}, bb))
      {#mset (fst x). x \<in># ran_m x1b#}\<close> for xaa af ag ah ai bb
      by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n all_atms_st_def
        in_all_lits_of_mm_ain_atms_of_iff all_atms_def all_lits_def
        simp del: all_atms_def[symmetric])

    show ?thesis
      apply (rule order_trans)
      apply (rule H[of _ _ _ _ _ _ x1a x1b x1g x1c 0 \<open>get_outlearned_heur x2g\<close> \<open>all_atms_st x2\<close>
         \<open>set (get_vdom (x2g))\<close>])
      subgoal
        using that
        by (auto simp: twl_st_heur'_def twl_st_heur_def get_clauses_wl.simps ac_simps)
      subgoal
        using that apply auto
        by (auto 0 0 simp add: RETURN_def conc_fun_RES  set_conflict_m_def twl_st_heur'_def
          twl_st_heur_def set_conflict_wl'_pre_def ac_simps)
      subgoal
        using that
        by (auto 0 0 simp add: RETURN_def conc_fun_RES set_conflict_m_def twl_st_heur'_def
          twl_st_heur_def)
      done
  qed

  have isa_set_lookup_conflict_aa_pre:
    \<open>(x, y) \<in> nat_rel \<times>\<^sub>f twl_st_heur_up'' \<D> r s K lcount \<Longrightarrow>
    y = (x1, x2) \<Longrightarrow>
    x = (x1a, x2a) \<Longrightarrow>
    set_conflict_wl'_pre x1 x2 \<Longrightarrow>
    (S, x2) \<in> twl_st_heur_up'' \<D> r s K lcount \<Longrightarrow>
    curry2 (curry2 (curry isa_set_lookup_conflict_aa_pre)) (get_trail_wl_heur S)
    (get_clauses_wl_heur S) x1a (get_conflict_wl_heur S) 0 (get_outlearned_heur S)\<close>
    for x1 x2 x1a x2a S y x
    unfolding isa_set_lookup_conflict_aa_pre_def set_conflict_wl'_pre_def
      twl_st_heur'_def twl_st_heur_def
    by (auto simp: arena_lifting)


  have set_conflict_wl_heur_alt_def: \<open>set_conflict_wl_heur = (\<lambda>C S. do {
    let S = S;
    let n = 0;
    let M = get_trail_wl_heur S;
    let N = get_clauses_wl_heur S;
    let D = get_conflict_wl_heur S;
    let outl = get_outlearned_heur S;
    ASSERT(curry5 isa_set_lookup_conflict_aa_pre M N C D n outl);
    (D, clvls, outl) \<leftarrow> isa_set_lookup_conflict_aa M N C D n outl;
    j \<leftarrow> mop_isa_length_trail M;
    let S = IsaSAT_Setup.set_conflict_wl_heur D S;
    let S = set_outl_wl_heur outl S;
    let S = set_count_max_wl_heur clvls S;
    let S = set_literals_to_update_wl_heur j S;
      RETURN S})\<close>
    unfolding set_conflict_wl_heur_def by auto

  show ?thesis
    supply [[goals_limit=1]]
    apply (intro nres_relI frefI)
    subgoal for x y
    unfolding uncurry_def RES_RETURN_RES4 set_conflict_wl_alt_def  set_conflict_wl_heur_alt_def
    apply (rewrite at \<open>let _ = 0 in _\<close> Let_def)
    apply (rewrite at \<open>let _ = get_trail_wl_heur _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ = get_clauses_wl_heur _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ = get_conflict_wl_heur _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ = get_outlearned_heur _ in _\<close> Let_def)
    apply (refine_vcg mop_isa_length_trail_length_u[of \<open>all_atms_st (snd y)\<close>, THEN fref_to_Down_Id_keep, unfolded length_uint32_nat_def
      comp_def] mark_conflict_to_rescore[where \<D> = \<D> and r=r and s=s and K=K and lcount=lcount, unfolded conc_fun_RETURN[symmetric]])
    subgoal for x1 x2 x1a x2a
      by (rule isa_set_lookup_conflict_aa_pre) (auto dest!: set_conflict_wl_pre_set_conflict_wl'_pre)
    apply assumption+
    subgoal by auto
    subgoal by (auto dest!: set_conflict_wl_pre_set_conflict_wl'_pre)
    subgoal for x y
      unfolding arena_is_valid_clause_idx_def
      by (auto simp: twl_st_heur'_def twl_st_heur_def)
    subgoal
      by (auto simp: twl_st_heur'_def twl_st_heur_def counts_maximum_level_def ac_simps
        set_conflict_wl'_pre_def dest!: set_conflict_wl_pre_set_conflict_wl'_pre
	intro!: valid_arena_mark_used)
    done
    done
qed

lemma in_Id_in_Id_option_rel[refine]:
  \<open>(f, f') \<in> Id \<Longrightarrow> (f, f') \<in> \<langle>Id\<rangle> option_rel\<close>
  by auto

text \<open>The assumption that that accessed clause is active has not been checked at this point!\<close>
definition keep_watch_heur_pre where
  \<open>keep_watch_heur_pre =
     (\<lambda>(((L, j), w), S).
        L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S))\<close>


lemma vdom_m_update_subset':
  \<open>fst C \<in> vdom_m \<A> bh N \<Longrightarrow> vdom_m \<A> (bh(ap := (bh ap)[bf := C])) N \<subseteq> vdom_m \<A> bh N\<close>
  unfolding vdom_m_def
  by (fastforce split: if_splits elim!: in_set_upd_cases)

lemma vdom_m_update_subset:
  \<open>bg < length (bh ap) \<Longrightarrow> vdom_m \<A> (bh(ap := (bh ap)[bf := bh ap ! bg])) N \<subseteq> vdom_m \<A> bh N\<close>
  unfolding vdom_m_def
  by (fastforce split: if_splits elim!: in_set_upd_cases)

lemma keep_watch_heur_keep_watch:
  \<open>(uncurry3 keep_watch_heur, uncurry3 (mop_keep_watch)) \<in>
      [\<lambda>_. True]\<^sub>f
       Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur_up'' \<D> r s K lcount \<rightarrow> \<langle>twl_st_heur_up'' \<D> r s K lcount\<rangle> nres_rel\<close>
  unfolding keep_watch_heur_def mop_keep_watch_def uncurry_def
    \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits[symmetric]
  apply (intro frefI nres_relI)
  apply refine_rcg
  subgoal
    by (auto 5 4 simp: keep_watch_heur_def keep_watch_def twl_st_heur'_def keep_watch_heur_pre_def
      twl_st_heur_def map_fun_rel_def2 all_atms_def[symmetric] mop_keep_watch_def
      intro!: ASSERT_leI
      dest: vdom_m_update_subset)
  subgoal
    by (auto 5 4 simp: keep_watch_heur_def keep_watch_def twl_st_heur'_def keep_watch_heur_pre_def
      twl_st_heur_def map_fun_rel_def2 all_atms_def[symmetric] mop_keep_watch_def watched_by_alt_def
      intro!: ASSERT_leI
      dest: vdom_m_update_subset)
  subgoal
    by (auto 5 4 simp: keep_watch_heur_def keep_watch_def twl_st_heur'_def keep_watch_heur_pre_def
      twl_st_heur_def map_fun_rel_def2 all_atms_def[symmetric] mop_keep_watch_def watched_by_alt_def
      intro!: ASSERT_leI
      dest: vdom_m_update_subset)
  subgoal
    by (clarsimp simp: keep_watch_heur_def keep_watch_def twl_st_heur'_def keep_watch_heur_pre_def
      twl_st_heur_def map_fun_rel_def2 all_atms_def[symmetric] mop_keep_watch_def watched_by_alt_def
      intro!: ASSERT_leI split: prod.splits)
     (auto dest!: vdom_m_update_subset)
  done

text \<open>This is a slightly stronger version of the previous lemma:\<close>
lemma keep_watch_heur_keep_watch':
  \<open>((((L', j'), w'), S'), ((L, j), w), S)
       \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur_up'' \<D> r s K lcount \<Longrightarrow>
  keep_watch_heur L' j' w' S' \<le> \<Down> {(T, T'). get_vdom T = get_vdom S' \<and>
     (T, T') \<in> twl_st_heur_up'' \<D> r s K lcount}
     (mop_keep_watch L j w S)\<close>
 unfolding keep_watch_heur_def mop_keep_watch_def uncurry_def
    \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits[symmetric]
  apply refine_rcg
  subgoal
    by (auto 5 4 simp: keep_watch_heur_def keep_watch_def twl_st_heur'_def keep_watch_heur_pre_def
      twl_st_heur_def map_fun_rel_def2 all_atms_def[symmetric] mop_keep_watch_def
      intro!: ASSERT_leI
      dest: vdom_m_update_subset)
  subgoal
    by (auto 5 4 simp: keep_watch_heur_def keep_watch_def twl_st_heur'_def keep_watch_heur_pre_def
      twl_st_heur_def map_fun_rel_def2 all_atms_def[symmetric] mop_keep_watch_def watched_by_alt_def
      intro!: ASSERT_leI
      dest: vdom_m_update_subset)
  subgoal
    by (auto 5 4 simp: keep_watch_heur_def keep_watch_def twl_st_heur'_def keep_watch_heur_pre_def
      twl_st_heur_def map_fun_rel_def2 all_atms_def[symmetric] mop_keep_watch_def watched_by_alt_def
      intro!: ASSERT_leI
      dest: vdom_m_update_subset)
  subgoal
    by (clarsimp simp: keep_watch_heur_def keep_watch_def twl_st_heur'_def keep_watch_heur_pre_def
      twl_st_heur_def map_fun_rel_def2 all_atms_def[symmetric] mop_keep_watch_def watched_by_alt_def
      intro!: ASSERT_leI split: prod.splits
      dest: vdom_m_update_subset)
     (auto dest!: vdom_m_update_subset)
  done

definition update_blit_wl_heur_pre where
  \<open>update_blit_wl_heur_pre r K' = (\<lambda>((((((L, C), b), j), w), K), S). L = K')\<close>

 lemma update_blit_wl_heur_update_blit_wl:
  \<open>(uncurry6 update_blit_wl_heur, uncurry6 update_blit_wl) \<in>
      [update_blit_wl_heur_pre r K]\<^sub>f
       nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<times>\<^sub>f
          twl_st_heur_up'' \<D> r s K lcount \<rightarrow>
       \<langle>nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r twl_st_heur_up'' \<D> r s K lcount\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI) \<comment> \<open>TODO proof\<close>
  apply (auto simp: update_blit_wl_heur_def update_blit_wl_def twl_st_heur'_def keep_watch_heur_pre_def
       twl_st_heur_def map_fun_rel_def2 update_blit_wl_heur_pre_def all_atms_def[symmetric]
        \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits
      simp flip: all_lits_alt_def2
      intro!: ASSERT_leI ASSERT_refine_right
      simp: vdom_m_update_subset)
  subgoal for aa ab ac ad ae be af ag ah bf aj ak al am an bg ao bh ap
    apply (subgoal_tac \<open>vdom_m (all_atms_st ([], ag, None, ah, bf, aj, ak, al, am, an, bg, {#}, ao)) (ao(K := (ao K)[ac := (aa, ae, ab)])) ag  \<subseteq>
       vdom_m (all_atms_st ([], ag, None, ah, bf, aj, ak, al, am, an, bg, {#}, ao)) ao ag\<close>)
    apply fast
    apply (rule vdom_m_update_subset')
    apply auto
    done
  subgoal for aa ab ac ad ae be af ag ah bf aj ak al am an bg ao bh ap
    apply (subgoal_tac \<open>vdom_m (all_atms_st ([], ag, None, bf, aj, ak, al, am, an, bg, ao, {#}, bh)) (bh(K := (bh K)[ac := (aa, ae, ab)])) ag  \<subseteq>
      vdom_m (all_atms_st ([], ag, None, bf, aj, ak, al, am, an, bg, ao, {#}, bh)) bh ag \<close>)
    apply fast
    apply (rule vdom_m_update_subset')
    apply auto
    done
  done

lemma mop_access_lit_in_clauses_heur:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> (i, i') \<in> Id \<Longrightarrow> (j, j') \<in> Id \<Longrightarrow> mop_access_lit_in_clauses_heur S i j
    \<le> \<Down> Id
       (mop_clauses_at (get_clauses_wl T) i' j')\<close>
  unfolding mop_access_lit_in_clauses_heur_def
  by (rule mop_arena_lit2[where vdom=\<open>set (get_vdom S)\<close>])
   (auto simp: twl_st_heur_def intro!: mop_arena_lit2)


 lemma isa_find_unwatched_wl_st_heur_find_unwatched_wl_st:
     \<open>isa_find_unwatched_wl_st_heur x' y'
        \<le> \<Down> Id (find_unwatched_l (get_trail_wl x) (get_clauses_wl x) y)\<close>
    if
      xy: \<open>((x', y'), x, y) \<in> twl_st_heur \<times>\<^sub>f nat_rel\<close>
      for x y x' y'
  proof -
    have  find_unwatched_l_alt_def: \<open>find_unwatched_l M N C = do {
        ASSERT(C \<in># dom_m N \<and> length (N \<propto> C) \<ge> 2 \<and> distinct (N \<propto> C) \<and> no_dup M);
        find_unwatched_l M N C
       }\<close> for M N C
      unfolding find_unwatched_l_def by (auto simp: summarize_ASSERT_conv)
    have K: \<open>find_unwatched_wl_st' x y \<le> find_unwatched_l (get_trail_wl x) (get_clauses_wl x) y\<close>
      unfolding find_unwatched_wl_st'_def
      apply (subst find_unwatched_l_alt_def)
      unfolding le_ASSERT_iff
      apply (cases x)
      apply clarify
      apply (rule order_trans)
      apply (rule find_unwatched[of _ _ _ \<open>all_atms_st x\<close>])
      subgoal
        by simp
      subgoal
        by auto
      subgoal
        using literals_are_in_\<L>\<^sub>i\<^sub>n_nth2[of y x]
        by simp
      subgoal by auto
      done
    show ?thesis
      apply (subst find_unwatched_l_alt_def)
      apply (intro ASSERT_refine_right)
      apply (rule order_trans)
        apply (rule find_unwatched_wl_st_heur_find_unwatched_wl_s[THEN fref_to_Down_curry,
          OF _ that(1)])
      by (simp_all add: K find_unwatched_wl_st_pre_def literals_are_in_\<L>\<^sub>i\<^sub>n_nth2)
  qed


lemma unit_propagation_inner_loop_body_wl_alt_def:
  \<open>unit_propagation_inner_loop_body_wl L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_pre L (j, w, S));
      (C, K, b) \<leftarrow> mop_watched_by_at S L w;
      S \<leftarrow> mop_keep_watch L j w S;
      ASSERT(is_nondeleted_clause_pre C L S);
      val_K \<leftarrow> mop_polarity_wl S K;
      if val_K = Some True
      then RETURN (j+1, w+1, S)
      else do {
        if b then do {
           ASSERT(propagate_proper_bin_case L K S C);
           if val_K = Some False
           then do {S \<leftarrow> set_conflict_wl C S;
             RETURN (j+1, w+1, S)}
           else do {
             S \<leftarrow> propagate_lit_wl_bin K C S;
             RETURN (j+1, w+1, S)}
        }  \<comment>\<open>Now the costly operations:\<close>
        else if C \<notin># dom_m (get_clauses_wl S)
        then RETURN (j, w+1, S)
        else do {
          ASSERT(unit_prop_body_wl_inv S j w L);
          i \<leftarrow> pos_of_watched (get_clauses_wl S) C L;
          ASSERT(i \<le> 1);
          L' \<leftarrow> other_watched_wl S L C i;
          val_L' \<leftarrow> mop_polarity_wl S L';
          if val_L' = Some True
          then do{T \<leftarrow> update_blit_wl L C b j w L' S; RETURN T}
          else do {
            f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S) C;
            ASSERT (unit_prop_body_wl_find_unwatched_inv f C S);
            case f of
              None \<Rightarrow> do {
                if val_L' = Some False
                then do {S \<leftarrow> set_conflict_wl C S;
                   RETURN (j+1, w+1, S)}
                else do {S \<leftarrow> propagate_lit_wl L' C i S; RETURN (j+1, w+1, S)}
              }
            | Some f \<Rightarrow> do {
                 ASSERT(C \<in># dom_m (get_clauses_wl S) \<and> f < length (get_clauses_wl S \<propto> C) \<and> f \<ge> 2);
                let S = S; \<comment> \<open>position saving\<close>
                K \<leftarrow> mop_clauses_at (get_clauses_wl S) C f;
                val_L' \<leftarrow> mop_polarity_wl S K;
                if val_L' = Some True
                then do{S \<leftarrow> update_blit_wl L C b j w K S; RETURN S}
                else do{S \<leftarrow> update_clause_wl L L' C b j w i f S; RETURN S}
              }
          }
        }
      }
   }\<close>
  unfolding unit_propagation_inner_loop_body_wl_def Let_def nres_monad2 by auto

lemma fref_to_Down_curry8:
  \<open>(uncurry8 ff, uncurry8 g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' y y' z z' a a' b b' c c' d d' e e' f f'. P ((((((((x', y'), z'), a'), b'), c'), d'), e'), f') \<Longrightarrow>
       (((((((((x, y), z), a), b), c), d), e), f), ((((((((x', y'), z'), a'), b'), c'), d'), e'), f')) \<in> A \<Longrightarrow>
         ff x y z a b c d e f \<le> \<Down> B (g x' y' z' a' b' c' d' e' f'))\<close>
  unfolding fref_def uncurry_def nres_rel_def by auto


lemma unit_propagation_inner_loop_body_wl_heur_unit_propagation_inner_loop_body_wl_D:
  \<open>(uncurry3 (unit_propagation_inner_loop_body_wl_heur ticks),
    uncurry3 unit_propagation_inner_loop_body_wl)
    \<in> [\<lambda>(((L, i), j), S). length (watched_by S L) \<le> r - MIN_HEADER_SIZE \<and> L = K \<and>
        length (watched_by S L) = s]\<^sub>f
       nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur_up'' \<D> r s K lcount \<rightarrow>
     \<langle>{((ticks, S), T). (S,T) \<in> nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r twl_st_heur_up'' \<D> r s K lcount}\<rangle>nres_rel\<close>
proof -

  have [refine]: \<open>clause_not_marked_to_delete_heur_pre (S', C')\<close>
    if \<open>is_nondeleted_clause_pre C L S\<close> and \<open>((C', S'), (C, S)) \<in> nat_rel \<times>\<^sub>r twl_st_heur\<close> for C C' S S' L
    using that apply -
    unfolding clause_not_marked_to_delete_heur_pre_def prod.case arena_is_valid_clause_vdom_def
    by (rule exI[of _ \<open>get_clauses_wl S\<close>], rule exI[of _ \<open>set (get_vdom S')\<close>])
     (use that in \<open>auto 5 3 simp: is_nondeleted_clause_pre_def twl_st_heur_def vdom_m_def watched_by_alt_def
           simp flip: all_lits_st_alt_def dest!: multi_member_split[of L]\<close>)

  note [refine] = mop_watched_by_app_heur_mop_watched_by_at''[of \<D> r lcount K s, THEN fref_to_Down_curry2]
      keep_watch_heur_keep_watch'[of _ _ _ _ _ _ _ _ \<D> r lcount K s]
     mop_polarity_st_heur_mop_polarity_wl''[of \<D> r lcount K s, THEN fref_to_Down_curry, unfolded comp_def]
      set_conflict_wl_heur_set_conflict_wl'[of \<D> r lcount K s, THEN fref_to_Down_curry, unfolded comp_def]
      propagate_lit_wl_bin_heur_propagate_lit_wl_bin
    [of \<D> r lcount K s, THEN fref_to_Down_curry2, unfolded comp_def]
     pos_of_watched_heur[of _ _ _ \<D> r lcount K s]
     mop_access_lit_in_clauses_heur
     update_blit_wl_heur_update_blit_wl[of r K \<D> lcount s, THEN fref_to_Down_curry6]
     isa_find_unwatched_wl_st_heur_find_unwatched_wl_st
     propagate_lit_wl_heur_propagate_lit_wl[of \<D> r lcount K s, THEN fref_to_Down_curry3, unfolded comp_def]
     isa_save_pos_is_Id
      update_clause_wl_heur_update_clause_wl[of K r \<D> lcount s, THEN fref_to_Down_curry8]
     other_watched_heur[of _ _ _ \<D> r lcount K s]

  have [simp]: \<open>is_nondeleted_clause_pre x1f x1b Sa \<Longrightarrow>
    clause_not_marked_to_delete_pre (Sa, x1f)\<close> for x1f x1b Sa
    unfolding is_nondeleted_clause_pre_def clause_not_marked_to_delete_pre_def vdom_m_def
      all_lits_st_alt_def[symmetric] by (cases Sa; auto dest!: multi_member_split)

  show ?thesis
    supply [[goals_limit=1]] twl_st_heur'_def[simp]
    supply RETURN_as_SPEC_refine[refine2 del]
    apply (intro frefI nres_relI)
    unfolding unit_propagation_inner_loop_body_wl_heur_def
      unit_propagation_inner_loop_body_wl_alt_def
      uncurry_def  clause_not_marked_to_delete_def[symmetric]
      watched_by_app_heur_def access_lit_in_clauses_heur_def Let_def[of "_ + 1 :: 64 word"]

    apply (refine_rcg (*find_unw isa_save_pos mop_access_lit_in_clauses_heur pos_of_watched_heur*))
    subgoal unfolding unit_propagation_inner_loop_wl_loop_D_heur_inv0_def twl_st_heur'_def
      unit_propagation_inner_loop_wl_loop_pre_def
      by fastforce
    subgoal by fast
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by fast
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by fast
    subgoal by simp
    subgoal by simp
    subgoal by fast
    subgoal by simp
    subgoal by simp
    apply assumption
    subgoal by auto
    subgoal
       unfolding Not_eq_iff
       by (rule clause_not_marked_to_delete_rel[THEN fref_to_Down_unRET_Id_uncurry])
        (simp_all add: clause_not_marked_to_delete_rel[THEN fref_to_Down_unRET_Id_uncurry])
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal by auto
    apply assumption
    subgoal by auto
    subgoal by fast
    subgoal by simp
    subgoal by simp
    subgoal
      unfolding update_blit_wl_heur_pre_def unit_propagation_inner_loop_wl_loop_D_heur_inv0_def
      prod.case unit_propagation_inner_loop_wl_loop_pre_def
      by normalize_goal+ simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by force
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: clause_not_marked_to_delete_def)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: update_blit_wl_heur_pre_def)
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: update_clause_wl_pre_def)
    subgoal by simp
    subgoal by simp
    done
qed
(*TODO Move*)

lemma unit_propagation_inner_loop_wl_loop_D_heur_unit_propagation_inner_loop_wl_loop_D:
  \<open>(uncurry (unit_propagation_inner_loop_wl_loop_D_heur),
       uncurry unit_propagation_inner_loop_wl_loop)
   \<in> [\<lambda>(L, S). length (watched_by S L) \<le> r - MIN_HEADER_SIZE \<and> L = K \<and> length (watched_by S L) = s \<and>
         length (watched_by S L) \<le> r]\<^sub>f
     nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_up'' \<D> r s K lcount \<rightarrow>
     \<langle>{((ticks, S), T). (S, T)\<in>(nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r twl_st_heur_up'' \<D> r s K lcount)}\<rangle>nres_rel\<close>
proof -
  have unit_propagation_inner_loop_wl_loop_D_heur_inv:
    \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv x2a x1a xa\<close>
    if
      \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_up'' \<D> r s K lcount\<close> and
      st: \<open>y = (x1, x2)\<close>
        \<open>x = (x1a, x2a)\<close> 
      \<open>(xa, x') \<in> {((ticks, S), T).
           (S, T) \<in> nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f twl_st_heur_up'' \<D> r s K lcount)} \<close> and
      H: \<open>unit_propagation_inner_loop_wl_loop_inv x1 x'\<close>
    for x y x1 x2 x1a x2a xa x' ya
  proof -
    obtain w S w' S' j j' ticks where
      xa: \<open>xa = (ticks, j, w, S)\<close> and x': \<open>x' = (j', w', S')\<close>
      using st
      by (cases xa; cases x') auto
    show ?thesis
      unfolding xa unit_propagation_inner_loop_wl_loop_D_heur_inv_def prod.case
      apply (rule exI[of _ x2])
      apply (rule exI[of _ S'])
      using that xa x' that apply -
      unfolding  prod.case apply hypsubst
      apply (auto simp: twl_st_heur'_def
        dest!: twl_struct_invs_no_alien_in_trail[of _ \<open>-x1\<close>] simp flip: all_lits_st_alt_def)
      unfolding unit_propagation_inner_loop_wl_loop_inv_def unit_propagation_inner_loop_l_inv_def
      unfolding prod.case apply normalize_goal+
      apply (drule twl_struct_invs_no_alien_in_trail[of _ \<open>-x1\<close>])
      apply (simp_all only: twl_st_l multiset.map_comp comp_def
        clause_twl_clause_of twl_st_wl in_all_lits_of_mm_uminus_iff ac_simps in_all_lits_uminus_iff
        flip: all_lits_st_alt_def)
     done
  qed
  have length: \<open>\<And>x y x1 x2 x1a x2a.
       case y of
       (L, S) \<Rightarrow>
         length (watched_by S L) \<le> r - MIN_HEADER_SIZE \<and>
         L = K \<and> length (watched_by S L) = s \<and> length (watched_by S L) \<le> r \<Longrightarrow>
       (x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_up'' \<D> r s K lcount \<Longrightarrow>  y = (x1, x2) \<Longrightarrow>
       x = (x1a, x2a) \<Longrightarrow>
       x1 \<in># all_lits_st x2 \<Longrightarrow>
       length (watched_by_int x2a x1a) \<le> length (get_clauses_wl_heur x2a) \<Longrightarrow>
       mop_length_watched_by_int x2a x1a
       \<le> \<Down> Id (RETURN (length (watched_by x2 x1)))\<close>
    unfolding mop_length_watched_by_int_def
    by refine_rcg
      (auto simp:   twl_st_heur'_def map_fun_rel_def2 twl_st_heur_def
      simp flip: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits intro!: ASSERT_leI)

  note H[refine] = unit_propagation_inner_loop_body_wl_heur_unit_propagation_inner_loop_body_wl_D
     [THEN fref_to_Down_curry3] init
  show ?thesis
    unfolding unit_propagation_inner_loop_wl_loop_D_heur_def
      unit_propagation_inner_loop_wl_loop_def uncurry_def
      unit_propagation_inner_loop_wl_loop_inv_def[symmetric]
    apply (intro frefI nres_relI)
    apply (refine_vcg)
    subgoal by (auto simp: twl_st_heur'_def twl_st_heur_state_simp_watched watched_by_alt_def
      simp flip: all_lits_st_alt_def)
    apply (rule length; assumption)
    subgoal by auto
    subgoal by (rule unit_propagation_inner_loop_wl_loop_D_heur_inv)
    subgoal
      by (subst get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id])
        (auto simp: get_conflict_wl_is_None_heur_get_conflict_wl_is_None twl_st_heur_state_simp_watched twl_st_heur'_def
          get_conflict_wl_is_None_def simp flip: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


lemma cut_watch_list_heur2_cut_watch_list_heur:
  shows
    \<open>cut_watch_list_heur2 j w L S \<le> \<Down> Id (cut_watch_list_heur j w L S)\<close>
proof -

  let ?N = \<open>get_clauses_wl_heur S\<close>
  let ?W = \<open>get_watched_wl_heur S\<close>
  define n where n: \<open>n = length (?W ! nat_of_lit L)\<close>
  let ?R = \<open>measure (\<lambda>(j'::nat, w' :: nat, _ :: (nat \<times> nat literal \<times> bool) list list). length (?W!nat_of_lit L) - w')\<close>
  define I' where
    \<open>I' \<equiv> \<lambda>(j', w', W'). length (W' ! (nat_of_lit L)) = length (?W ! (nat_of_lit L)) \<and> j' \<le> w' \<and> w' \<ge> w \<and>
        w' - w = j' - j \<and> j' \<ge> j \<and>
        drop w' (W' ! (nat_of_lit L)) = drop w' (?W ! (nat_of_lit L)) \<and>
        w' \<le> length (W' ! (nat_of_lit L)) \<and>
        W'[nat_of_lit L := take (j + w' - w) (W' ! nat_of_lit L)] =
        ?W[nat_of_lit L := take (j + w' - w) ((take j (?W!(nat_of_lit L)) @ drop w (?W!(nat_of_lit L))))]\<close>

  have cut_watch_list_heur_alt_def:
  \<open>cut_watch_list_heur j w L =(\<lambda>S. do {
      ASSERT(j \<le> length (get_watched_wl_heur S!nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length (get_watched_wl_heur S) \<and>
         w \<le> length (get_watched_wl_heur S ! (nat_of_lit L)));
      let W = (get_watched_wl_heur S)[nat_of_lit L := take j (get_watched_wl_heur S!(nat_of_lit L)) @ drop w (get_watched_wl_heur S!(nat_of_lit L))];
      RETURN (set_watched_wl_heur W S)
    })\<close>
    unfolding cut_watch_list_heur_def Let_def by auto
  have REC: \<open>ASSERT (x1k < length (x2k ! nat_of_lit L)) \<bind>
      (\<lambda>_. RETURN (x1j + 1, x1k + 1, x2k [nat_of_lit L := (x2k ! nat_of_lit L) [x1j :=
                    x2k ! nat_of_lit L !
                    x1k]]))
      \<le> SPEC (\<lambda>s'. \<forall>x1 x2 x1a x2a. x2 = (x1a, x2a) \<longrightarrow> s' = (x1, x2) \<longrightarrow>
          (x1 \<le> x1a \<and> nat_of_lit L < length x2a) \<and> I' s' \<and>
          (s', s) \<in> measure (\<lambda>(j', w', _). length (?W ! nat_of_lit L) - w'))\<close>
    if
      \<open>j \<le> length (?W ! nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length ?W \<and>
          w \<le> length (?W ! nat_of_lit L)\<close> and
      pre: \<open>j \<le> length (?W ! nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length ?W \<and>
          w \<le> length (?W ! nat_of_lit L)\<close> and
      I: \<open>case s of (j, w, W) \<Rightarrow> j \<le> w \<and> nat_of_lit L < length W\<close> and
      I': \<open>I' s\<close> and
      cond: \<open>case s of (j, w, W) \<Rightarrow> w < length (W ! nat_of_lit L)\<close> and
      [simp]: \<open>x2 = (x1k, x2k)\<close> and
      [simp]: \<open>s = (x1j, x2)\<close>
    for s x1j x2 x1k x2k
  proof -
      have [simp]: \<open>x1k < length (x2k ! nat_of_lit L)\<close> and
        \<open>length (?W ! nat_of_lit L) - Suc x1k < length (?W ! nat_of_lit L) - x1k\<close>
        using cond I I' unfolding I'_def by auto
      moreover have \<open>x1j \<le> x1k\<close> \<open>nat_of_lit L < length x2k\<close>
        using I I' unfolding I'_def by auto
      moreover have \<open>I' (Suc x1j, Suc x1k, x2k
        [nat_of_lit L := (x2k ! nat_of_lit L)[x1j := x2k ! nat_of_lit L ! x1k]])\<close>
      proof -
        have ball_leI:  \<open>(\<And>x. x < A \<Longrightarrow> P x) \<Longrightarrow> (\<forall>x < A. P x)\<close> for A P
          by auto
        have H: \<open>\<And>i. x2k[nat_of_lit L := take (j + x1k - w) (x2k ! nat_of_lit L)] ! i = ?W
    [nat_of_lit L :=
       take (min (j + x1k - w) j) (?W ! nat_of_lit L) @
       take (j + x1k - (w + min (length (?W ! nat_of_lit L)) j))
        (drop w (?W ! nat_of_lit L))] ! i\<close> and
          H': \<open>x2k[nat_of_lit L := take (j + x1k - w) (x2k ! nat_of_lit L)] = ?W
          [nat_of_lit L :=
       take (min (j + x1k - w) j) (?W ! nat_of_lit L) @
       take (j + x1k - (w + min (length (?W ! nat_of_lit L)) j))
        (drop w (?W ! nat_of_lit L))]\<close> and
          \<open>j < length (?W ! nat_of_lit L)\<close> and
          \<open>(length (?W ! nat_of_lit L) - w) \<ge> (Suc x1k - w)\<close> and
          \<open>x1k \<ge> w\<close>
          \<open>nat_of_lit L < length ?W\<close> and
          \<open>j + x1k - w = x1j\<close> and
          \<open>x1j - j = x1k - w\<close> and
          \<open>x1j < length (?W ! nat_of_lit L)\<close> and
          \<open>length (x2k ! nat_of_lit L) = length (?W ! nat_of_lit L)\<close> and
          \<open>drop x1k (x2k ! (nat_of_lit L)) = drop x1k (?W ! (nat_of_lit L))\<close>
          \<open>x1j \<ge> j\<close>  and
          \<open>w + x1j - j = x1k\<close>
          using I I' pre cond unfolding I'_def by auto
        have
          [simp]: \<open>min x1j j = j\<close>
          using \<open>x1j \<ge> j\<close> unfolding min_def by auto
        have \<open>x2k[nat_of_lit L := take (Suc (j + x1k) - w) (x2k[nat_of_lit L := (x2k ! nat_of_lit L)
                  [x1j := x2k ! nat_of_lit L ! x1k]] ! nat_of_lit L)] =
           ?W[nat_of_lit L := take j (?W ! nat_of_lit L) @ take (Suc (j + x1k) - (w + min (length (?W ! nat_of_lit L)) j))
               (drop w (?W ! nat_of_lit L))]\<close>
          using cond I \<open>j < length (?W ! nat_of_lit L)\<close> and
           \<open>(length (?W ! nat_of_lit L) - w) \<ge> (Suc x1k - w)\<close> and
            \<open>x1k \<ge> w\<close>
            \<open>nat_of_lit L < length ?W\<close>
            \<open>j + x1k - w = x1j\<close> \<open>x1j < length (?W ! nat_of_lit L)\<close>
          apply (subst list_eq_iff_nth_eq)
          apply -
          apply (intro conjI ball_leI)
          subgoal using arg_cong[OF H', of length] by auto
          subgoal for k
            apply (cases \<open>k \<noteq> nat_of_lit L\<close>)
            subgoal using H[of k] by auto
            subgoal
              using H[of k] \<open>x1j < length (?W ! nat_of_lit L)\<close>
                \<open>length (x2k ! nat_of_lit L) = length (?W ! nat_of_lit L)\<close>
                arg_cong[OF \<open>drop x1k (x2k ! (nat_of_lit L)) = drop x1k (?W ! (nat_of_lit L))\<close>,
                   of \<open>\<lambda>xs. xs ! 0\<close>] \<open>x1j \<ge> j\<close>
              apply (cases \<open>Suc x1j = length (?W ! nat_of_lit L)\<close>)
              apply (auto simp add: Suc_diff_le take_Suc_conv_app_nth \<open>j + x1k - w = x1j\<close>
                 \<open>x1j - j = x1k - w\<close>[symmetric] \<open>w + x1j - j = x1k\<close>)
                apply (metis (no_types, lifting) append_eq_appendI append_eq_append_conv_if
                  nat_in_between_eq(1) take_update_last)
                by (metis (no_types, lifting) \<open>x1j < length (?W ! nat_of_lit L)\<close> append.assoc
                  take_Suc_conv_app_nth take_update_last)
            done
          done
        then show ?thesis
          unfolding I'_def prod.case
          using I I' cond unfolding I'_def by (auto simp: Cons_nth_drop_Suc[symmetric])
      qed
      ultimately show ?thesis
        by auto
    qed

    have step: \<open>(s, ?W[nat_of_lit L := take j (?W ! nat_of_lit L) @ drop w (?W ! nat_of_lit L)])
      \<in>  {((i, j, W'), W). (W'[nat_of_lit L := take i (W' ! nat_of_lit L)], W) \<in> Id \<and>
         i \<le> length (W' ! nat_of_lit L) \<and> nat_of_lit L < length W' \<and>
	 n = length (W' ! nat_of_lit L)}\<close>
      if
        pre: \<open>j \<le> length (?W ! nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length ?W \<and>
     w \<le> length (?W ! nat_of_lit L)\<close> and
        \<open>j \<le> length (?W ! nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length ?W \<and>
     w \<le> length (?W ! nat_of_lit L)\<close> and
        \<open>case s of (j, w, W) \<Rightarrow> j \<le> w \<and> nat_of_lit L < length W\<close> and
        \<open>I' s\<close> and
        \<open>\<not> (case s of (j, w, W) \<Rightarrow> w < length (W ! nat_of_lit L))\<close>
      for s
    proof -
      obtain j' w' W' where s: \<open>s = (j', w', W')\<close> by (cases s)
      have
        \<open>\<not> w' < length (W' ! nat_of_lit L)\<close> and
        \<open>j \<le> length (?W ! nat_of_lit L)\<close> and
        \<open>j' \<le> w'\<close> and
        \<open>nat_of_lit L < length W'\<close> and
        [simp]: \<open>length (W' ! nat_of_lit L) = length (?W ! nat_of_lit L)\<close> and
        \<open>j \<le> w\<close> and
        \<open>j' \<le> w'\<close> and
        \<open>nat_of_lit L < length ?W\<close> and
        \<open>w \<le> length (?W ! nat_of_lit L)\<close> and
        \<open>w \<le> w'\<close> and
        \<open>w' - w = j' - j\<close> and
        \<open>j \<le> j'\<close> and
        \<open>drop w' (W' ! nat_of_lit L) = drop w' (?W ! nat_of_lit L)\<close> and
        \<open>w' \<le> length (W' ! nat_of_lit L)\<close> and
        L_le_W: \<open>nat_of_lit L < length ?W\<close> and
        eq: \<open>W'[nat_of_lit L := take (j + w' - w) (W' ! nat_of_lit L)] =
            ?W[nat_of_lit L := take (j + w' - w) (take j (?W ! nat_of_lit L) @ drop w (?W ! nat_of_lit L))]\<close>
        using that unfolding I'_def that prod.case s
        by blast+
      then have
        j_j': \<open>j + w' - w = j'\<close> and
        j_le: \<open>j + w' - w = length (take j (?W ! nat_of_lit L) @ drop w (?W ! nat_of_lit L))\<close> and
        w': \<open>w' = length (?W ! nat_of_lit L)\<close>
        by auto
      have [simp]: \<open>length ?W = length W'\<close>
        using arg_cong[OF eq, of length] by auto
      show ?thesis
        using eq \<open>j \<le> w\<close> \<open>w \<le> length (?W ! nat_of_lit L)\<close> \<open>j \<le> j'\<close> \<open>w' - w = j' - j\<close>
          \<open>w \<le> w'\<close> w' L_le_W
        unfolding j_j' j_le s n
        by (auto simp: min_def split: if_splits)
  qed

  have HHH: \<open>X \<le> RES (R\<inverse> `` {S}) \<Longrightarrow> X \<le> \<Down> R (RETURN S)\<close> for X S R
    by (auto simp: RETURN_def conc_fun_RES)

  show ?thesis
    unfolding cut_watch_list_heur2_def cut_watch_list_heur_alt_def prod.case
    apply (rewrite at \<open>let _ = get_watched_wl_heur _ in _\<close> Let_def)
    unfolding n[symmetric]
    apply (rewrite at \<open>let _ = n in _\<close> Let_def)
    apply (refine_vcg WHILEIT_rule_stronger_inv_RES[where R = ?R and
      I' = I' and \<Phi> = \<open>{((i, j, W'), W). (W'[nat_of_lit L := take i (W' ! nat_of_lit L)], W) \<in> Id \<and>
         i \<le> length (W' ! nat_of_lit L) \<and> nat_of_lit L < length W' \<and>
	 n = length (W' ! nat_of_lit L)}\<inverse> `` _\<close>] HHH)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: )
    subgoal by auto
    subgoal by auto
    subgoal unfolding I'_def by (auto simp: n)
    subgoal unfolding I'_def by (auto simp: n)
    subgoal unfolding I'_def by (auto simp: n)
    subgoal unfolding I'_def by auto
    subgoal unfolding I'_def by auto
    subgoal unfolding I'_def by (auto simp: n)
    subgoal using REC by (auto simp: n)
    subgoal unfolding I'_def by (auto simp: n)
    subgoal for s using step[of \<open>s\<close>] unfolding I'_def by (auto simp: n)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma vdom_m_cut_watch_list:
  \<open>set xs \<subseteq> set (W L) \<Longrightarrow> vdom_m \<A> (W(L := xs)) d \<subseteq> vdom_m \<A> W d\<close>
  by (cases \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>)
    (force simp: vdom_m_def split: if_splits)+

text \<open>The following order allows the rule to be used as a destruction rule, make it more
useful for refinement proofs.\<close>
lemma vdom_m_cut_watch_listD:
  \<open>x \<in> vdom_m \<A> (W(L := xs)) d \<Longrightarrow> set xs \<subseteq> set (W L) \<Longrightarrow> x \<in> vdom_m \<A> W d\<close>
  using vdom_m_cut_watch_list[of xs W L] by auto

lemma cut_watch_list_heur_cut_watch_list_heur:
  \<open>(uncurry3 cut_watch_list_heur, uncurry3 cut_watch_list) \<in>
  [\<lambda>(((j, w), L), S). True]\<^sub>f
    nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f twl_st_heur'' \<D> r lcount \<rightarrow> \<langle>twl_st_heur'' \<D> r lcount\<rangle>nres_rel\<close>
  unfolding cut_watch_list_heur_def cut_watch_list_def uncurry_def
    \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits[symmetric]
  apply (intro frefI nres_relI)
  apply refine_vcg
  subgoal
    by (auto simp: cut_watch_list_heur_def cut_watch_list_def twl_st_heur'_def
      twl_st_heur_def map_fun_rel_def2)
  subgoal
    by (auto simp: cut_watch_list_heur_def cut_watch_list_def twl_st_heur'_def
      twl_st_heur_def map_fun_rel_def2)
  subgoal
    by (auto simp: cut_watch_list_heur_def cut_watch_list_def twl_st_heur'_def
      twl_st_heur_def map_fun_rel_def2)
  subgoal
    by (auto simp: cut_watch_list_heur_def cut_watch_list_def twl_st_heur'_def
      twl_st_heur_def map_fun_rel_def2)
  subgoal
    by (auto simp: cut_watch_list_heur_def cut_watch_list_def twl_st_heur'_def
      twl_st_heur_def map_fun_rel_def2 vdom_m_cut_watch_list set_take_subset
        set_drop_subset dest!: vdom_m_cut_watch_listD
        dest!: in_set_dropD in_set_takeD)
  done

lemma unit_propagation_inner_loop_wl_alt_def:
  \<open>unit_propagation_inner_loop_wl L S\<^sub>0 = do {
     (j, w, S) \<leftarrow> unit_propagation_inner_loop_wl_loop L S\<^sub>0;
     ASSERT(j \<le> w \<and> w \<le> length (watched_by S L) \<and> L \<in># all_lits_st S);
     T \<leftarrow> cut_watch_list j w L S;
     RETURN T
  }\<close>
  unfolding unit_propagation_inner_loop_wl_def nres_monad2 by auto

lemma unit_propagation_inner_loop_wl_D_heur_unit_propagation_inner_loop_wl_D:
  \<open>(uncurry unit_propagation_inner_loop_wl_D_heur, uncurry unit_propagation_inner_loop_wl) \<in>
    [\<lambda>(L, S). length(watched_by S L) \<le> r-MIN_HEADER_SIZE]\<^sub>f
    nat_lit_lit_rel \<times>\<^sub>f twl_st_heur'' \<D> r lcount \<rightarrow> \<langle>{((ticks,S), T). (S,T) \<in> twl_st_heur'' \<D> r lcount}\<rangle> nres_rel\<close>
proof -
  have length_le: \<open>length (watched_by x2b x1b) \<le> r - MIN_HEADER_SIZE\<close> and
    length_eq: \<open>length (watched_by x2b x1b) = length (watched_by (snd y) (fst y))\<close> and
    eq: \<open>x1b = fst y\<close>
    if
      \<open>case y of (L, S) \<Rightarrow> length (watched_by S L) \<le> r-MIN_HEADER_SIZE\<close> and
      \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f twl_st_heur'' \<D> r lcount\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x = (x1a, x2a)\<close> and
      \<open>(x1, x2) = (x1b, x2b)\<close>
    for x y x1 x2 x1a x2a x1b x2b r
      using that by auto
  show ?thesis
    unfolding unit_propagation_inner_loop_wl_D_heur_def
      unit_propagation_inner_loop_wl_alt_def uncurry_def
      apply (intro frefI nres_relI)
    apply (refine_vcg cut_watch_list_heur_cut_watch_list_heur[of \<D> r, THEN fref_to_Down_curry3]
	unit_propagation_inner_loop_wl_loop_D_heur_unit_propagation_inner_loop_wl_loop_D[of r _ _ \<D> lcount,
	   THEN fref_to_Down_curry])

    apply (rule length_le; assumption)
    apply (rule eq; assumption)
    apply (rule length_eq; assumption)
    subgoal by auto
    subgoal by (auto simp: twl_st_heur'_def twl_st_heur_state_simp_watched)
    subgoal
      by (auto simp: twl_st_heur'_def twl_st_heur_state_simp_watched watched_by_alt_def
       simp flip: all_lits_st_alt_def[symmetric])
    apply (rule order.trans)
    apply (rule cut_watch_list_heur2_cut_watch_list_heur)
    apply (subst Down_id_eq)
    apply (rule cut_watch_list_heur_cut_watch_list_heur[of \<D>, THEN fref_to_Down_curry3])
    by auto
qed

lemma select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl:
  \<open>literals_to_update_wl y \<noteq> {#} \<Longrightarrow>
  (x, y) \<in> twl_st_heur'' \<D>1 r1 lcount \<Longrightarrow>
  select_and_remove_from_literals_to_update_wl_heur x
      \<le> \<Down>{((S, L), (S', L')). ((S, L), (S', L')) \<in> twl_st_heur'' \<D>1 r1 lcount \<times>\<^sub>f nat_lit_lit_rel \<and>
            S' = set_literals_to_update_wl (literals_to_update_wl y - {#L#}) y \<and>
            get_clauses_wl_heur S = get_clauses_wl_heur x}
         (select_and_remove_from_literals_to_update_wl y)\<close>
  supply RETURN_as_SPEC_refine[refine2]
  unfolding select_and_remove_from_literals_to_update_wl_heur_def
    select_and_remove_from_literals_to_update_wl_def
  apply (refine_vcg)
  subgoal
    by (subst trail_pol_same_length[of \<open>get_trail_wl_heur x\<close> \<open>get_trail_wl y\<close> \<open>all_atms_st y\<close>])
     (auto simp: twl_st_heur_def twl_st_heur'_def RETURN_RES_refine_iff)
  subgoal
    by (auto simp: twl_st_heur_def twl_st_heur'_def RETURN_RES_refine_iff trail_pol_alt_def)
  subgoal
    apply (subst (asm) trail_pol_same_length[of \<open>get_trail_wl_heur x\<close> \<open>get_trail_wl y\<close> \<open>all_atms_st y\<close>])
    apply (auto simp: twl_st_heur_def twl_st_heur'_def; fail)[]
    apply (rule bind_refine_res)
    prefer 2
    apply (rule isa_trail_nth_rev_trail_nth[THEN fref_to_Down_curry, unfolded comp_def RETURN_def,
      unfolded conc_fun_RES, of \<open>get_trail_wl y\<close> _ _ _ \<open>all_atms_st y\<close>])
    apply ((auto simp: twl_st_heur_def twl_st_heur'_def; fail)+)[2]
    subgoal for z
      apply (cases x; cases y)
      by (auto simp add: Cons_nth_drop_Suc[symmetric] twl_st_heur_def twl_st_heur'_def
        RETURN_RES_refine_iff rev_trail_nth_def)
    done
  done

(*TODO move*)
lemma watched_by_set_literals_to_update_wl: \<open>watched_by (set_literals_to_update_wl xs S) = watched_by S\<close>
  by (cases S) auto

lemma outer_loop_length_watched_le_length_arena:
  fixes xa :: \<open>isasat \<times> 64 word\<close>
  assumes 
    xa_x': \<open>(xa, x') \<in> {((S, ticks), T). (S, T) \<in> twl_st_heur'' \<D> r lcount}\<close> and
    prop_heur_inv: \<open>case xa of (S, ticks) \<Rightarrow> literals_to_update_wl_heur S < isa_length_trail (get_trail_wl_heur S)\<close> and
    prop_inv: \<open>unit_propagation_outer_loop_wl_inv x'\<close> and
   xb_x'a: \<open>(xb, x'a)
  \<in> {((S, L), S', L').
     ((S, L), S', L') \<in> twl_st_heur'' \<D> r lcount \<times>\<^sub>f nat_lit_lit_rel \<and>
     S' = set_literals_to_update_wl (remove1_mset L (literals_to_update_wl x')) x' \<and>
     get_clauses_wl_heur S = get_clauses_wl_heur x1a}\<close> and
    x2: \<open>x2a \<in># all_lits_st x1\<close> and
    st: \<open>x'a = (x1, x2a)\<close> \<open>xa = (x1a, xa_ticks)\<close>  \<open>xb = (x1b, x2b)\<close>
  shows \<open>length (watched_by x1 x2b) \<le> r - TIER_ONE_MAXIMUM\<close> and
     \<open>mop_length_watched_by_int x1b x2b \<le> \<Down> Id (RES UNIV)\<close>
proof -
  let ?xa1 = \<open>fst xb\<close>
  have corr: \<open>correct_watching x'\<close>
    using prop_inv unfolding unit_propagation_outer_loop_wl_inv_def
      unit_propagation_outer_loop_wl_inv_def
    by auto
  moreover have \<open>x2a \<in># all_lits_st x'\<close>
    using x2 assms unfolding all_atms_def all_lits_def
    by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps)
  ultimately have dist: \<open>distinct_watched (watched_by x' x2a)\<close>
    using x2 xb_x'a unfolding all_atms_def all_lits_def
    by (cases x'; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps ac_simps)
  then have dist: \<open>distinct_watched (watched_by x1 x2a)\<close>
    using xb_x'a unfolding st
    by (cases x'; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps)
  have dist_vdom: \<open>distinct (get_vdom x1b)\<close>
    using xb_x'a unfolding st
    by (cases x')
      (auto simp: twl_st_heur_def twl_st_heur'_def st aivdom_inv_dec_alt_def)

  have
      valid: \<open>valid_arena (get_clauses_wl_heur ?xa1) (get_clauses_wl x1) (set (get_vdom x1b))\<close>
    using xb_x'a unfolding all_atms_def all_lits_def st
    by (cases x')
     (auto simp: twl_st_heur'_def twl_st_heur_def)

  have \<open>vdom_m (all_atms_st x1) (get_watched_wl x1) (get_clauses_wl x1) \<subseteq> set (get_vdom x1b)\<close>
    using xb_x'a
    by (cases x')
      (auto simp: twl_st_heur_def twl_st_heur'_def st)
  then have subset: \<open>set (map fst (watched_by x1 x2a)) \<subseteq> set (get_vdom x1b)\<close>
    using x2 unfolding vdom_m_def st all_lits_st_alt_def[symmetric]
    by (cases x1)
      (force simp: twl_st_heur'_def twl_st_heur_def
        dest!: multi_member_split)
  have watched_incl: \<open>mset (map fst (watched_by x1 x2a)) \<subseteq># mset (get_vdom x1b)\<close>
    by (rule distinct_subseteq_iff[THEN iffD1])
      (use dist[unfolded distinct_watched_alt_def] dist_vdom subset in
         \<open>simp_all flip: distinct_mset_mset_distinct\<close>)
  have vdom_incl: \<open>set (get_vdom x1b) \<subseteq> {MIN_HEADER_SIZE..< length (get_clauses_wl_heur ?xa1)}\<close>
    using valid_arena_in_vdom_le_arena[OF valid] arena_dom_status_iff[OF valid] by auto

  have \<open>length (get_vdom x1b) \<le> length (get_clauses_wl_heur ?xa1) - MIN_HEADER_SIZE\<close>
    by (subst distinct_card[OF dist_vdom, symmetric])
      (use card_mono[OF _ vdom_incl] in auto)
  then show \<open>length (watched_by x1 x2b) \<le> r - TIER_ONE_MAXIMUM\<close>
    using size_mset_mono[OF watched_incl] xb_x'a st
    by (auto simp add: watched_by_set_literals_to_update_wl)
  have \<open>(get_watched_wl_heur x1b, get_watched_wl x') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms_st x'))\<close>
    using xb_x'a corr st
    by (cases x') (auto simp: correct_watching.simps twl_st_heur_def twl_st_heur'_def)
  moreover have \<open>correct_watching x1\<close> and \<open>x2a \<in># all_lits_st x'\<close>
    using corr xb_x'a x2 unfolding unit_propagation_outer_loop_wl_inv_def
      unit_propagation_outer_loop_wl_inv_def st
    by auto
  ultimately have \<open>nat_of_lit x2a < length (get_watched_wl_heur x1b)\<close>
    unfolding st
    by (auto simp: correct_watching.simps map_fun_rel_def simp flip: all_lits_st_alt_def  dest!: multi_member_split)

  then show \<open>mop_length_watched_by_int x1b x2b \<le> \<Down> Id (RES UNIV)\<close>
    using st xb_x'a
    unfolding mop_length_watched_by_int_def
    by refine_vcg auto
qed


lemma unit_propagation_outer_loop_wl_D_heur_alt_def:
  \<open>unit_propagation_outer_loop_wl_D_heur S\<^sub>0 = do {
    let j1 = isa_length_trail (get_trail_wl_heur S\<^sub>0);
    (S, ticks) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(T, ticks::64 word). unit_propagation_outer_loop_wl_D_heur_inv S\<^sub>0 T\<^esup>
      (\<lambda>(S, ticks). literals_to_update_wl_heur S < isa_length_trail (get_trail_wl_heur S))
      (\<lambda>(S, ticks). do {
        ASSERT(literals_to_update_wl_heur S < isa_length_trail (get_trail_wl_heur S));
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update_wl_heur S;
        ASSERT(length (get_clauses_wl_heur S') = length (get_clauses_wl_heur S));
        n \<leftarrow> mop_length_watched_by_int S' L;
        let ticks' = ticks + 8*of_nat n;
        (t, S) \<leftarrow> unit_propagation_inner_loop_wl_D_heur L S';
        RETURN (S, ticks' + t)
      })
     (S\<^sub>0, 0);
  let j2 = isa_length_trail (get_trail_wl_heur S);
  unit_propagation_update_statistics (of_nat j1) (of_nat j2) ticks S}\<close>
  unfolding unit_propagation_outer_loop_wl_D_heur_def IsaSAT_Profile.start_def IsaSAT_Profile.stop_def
    Let_def
  by auto

lemma unit_propagation_outer_loop_wl_alt_def:
  \<open>unit_propagation_outer_loop_wl S\<^sub>0 = do {
    S \<leftarrow> WHILE\<^sub>T\<^bsup>unit_propagation_outer_loop_wl_inv\<^esup>
      (\<lambda>S. literals_to_update_wl S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT(literals_to_update_wl S \<noteq> {#});
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update_wl S;
        ASSERT(L \<in># all_lits_st S');
        _ \<leftarrow> RES (UNIV:: nat set);
        T \<leftarrow> unit_propagation_inner_loop_wl L S';
        RETURN T
      })
      (S\<^sub>0 :: 'v twl_st_wl);
   RETURN S}
\<close>
  unfolding unit_propagation_outer_loop_wl_def by auto

lemma unit_propagation_update_statistics_twl_st_heur'':
  \<open>(S, x') \<in> twl_st_heur'' \<D> r lcount \<Longrightarrow>
  unit_propagation_update_statistics a b ticks S \<le> \<Down>(twl_st_heur'' \<D> r lcount) (RETURN x')\<close>
  unfolding unit_propagation_update_statistics_def Let_def conc_fun_RETURN
  apply (refine_vcg trail_height_before_conflict[where \<A> = \<open>all_atms_st x'\<close>, THEN fref_to_Down, of _ \<open>get_trail_wl x'\<close>, THEN order_trans])
  subgoal
    by (auto simp: twl_st_heur_def twl_st_heur'_def)
  subgoal
    by (auto simp: twl_st_heur_def twl_st_heur'_def)
  subgoal
    by (auto simp: twl_st_heur_def twl_st_heur'_def)
  subgoal
     by (auto simp: twl_st_heur_def twl_st_heur'_def trail_height_before_conflict_spec_def)
  done

theorem unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D':
  \<open>(unit_propagation_outer_loop_wl_D_heur, unit_propagation_outer_loop_wl) \<in>
    twl_st_heur'' \<D> r lcount \<rightarrow>\<^sub>f \<langle>twl_st_heur'' \<D> r lcount\<rangle> nres_rel\<close>
  supply [[goals_limit=1]]
  unfolding unit_propagation_outer_loop_wl_D_heur_alt_def[unfolded Let_def]
    unit_propagation_outer_loop_wl_alt_def all_lits_alt_def2[symmetric] nres_monad3
  apply (intro frefI nres_relI)
  apply (refine_vcg
      unit_propagation_update_statistics_twl_st_heur''
      unit_propagation_inner_loop_wl_D_heur_unit_propagation_inner_loop_wl_D[of r \<D> lcount, THEN fref_to_Down_curry]
      select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl
    [of _ _ \<D> r lcount]
    WHILEIT_refine[where R = \<open>{((S, ticks), T). (S, T) \<in> twl_st_heur'' \<D> r lcount}\<close>])
  subgoal by auto
  subgoal for x y S T
    using isa_length_trail_pre[of \<open>get_trail_wl_heur (fst S)\<close> \<open>get_trail_wl T\<close> \<open>all_atms_st T\<close>] apply -
    unfolding unit_propagation_outer_loop_wl_D_heur_inv_def twl_st_heur'_def
    apply (rule_tac x=y in exI)
    apply (rule_tac x=T in exI)
    by (auto 5 2 simp: twl_st_heur_def twl_st_heur'_def)
  subgoal for _ _ x y
    by (subst isa_length_trail_length_u[THEN fref_to_Down_unRET_Id, of _ \<open>get_trail_wl y\<close> \<open>all_atms_st y\<close>])
      (auto simp: twl_st_heur_def twl_st_heur'_def simp flip: all_lits_st_alt_def)
  subgoal by (auto simp: twl_st_heur'_def)
  subgoal by (auto simp: )
  subgoal by (auto simp: )
  apply (rule outer_loop_length_watched_le_length_arena(2); assumption)
  subgoal for x y xa x' x1 x2 xb x'a x1a x2a x1b x2b n _ x1c x2c
    by (rule_tac x'=x' and \<D>=\<D> and lcount=lcount in outer_loop_length_watched_le_length_arena(1)) auto
  subgoal by (auto simp: )
  subgoal by (auto simp: twl_st_heur'_def)
  subgoal by (auto simp: twl_st_heur'_def)
  done

lemma twl_st_heur'D_twl_st_heurD:
  assumes H: \<open>(\<And>\<D>. f \<in> twl_st_heur' \<D> \<rightarrow>\<^sub>f \<langle>twl_st_heur' \<D>\<rangle> nres_rel)\<close>
  shows \<open>f \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle> nres_rel\<close>  (is \<open>_ \<in> ?A B\<close>)
proof -
  obtain f1 f2 where f: \<open>f = (f1, f2)\<close>
    by (cases f) auto
  show ?thesis
    using assms unfolding f
    apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
    apply (intro conjI impI allI)
    subgoal for x y
      apply (rule "weaken_\<Down>'"[of _ \<open>twl_st_heur' (dom_m (get_clauses_wl y))\<close>])
      apply (fastforce simp: twl_st_heur'_def)+
      done
    done
qed

lemma watched_by_app_watched_by_app_heur:
  \<open>(uncurry2 (RETURN ooo watched_by_app_heur), uncurry2 (RETURN ooo watched_by_app)) \<in>
    [\<lambda>((S, L), K). L \<in># all_lits_st S \<and> K < length (get_watched_wl S L)]\<^sub>f
     twl_st_heur \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: watched_by_app_heur_def watched_by_app_def twl_st_heur_def map_fun_rel_def2)

lemma update_clause_wl_heur_pre_le_sint64:
  assumes
    \<open>arena_is_valid_clause_idx_and_access (get_clauses_wl_heur S) bf baa\<close> and
    \<open>length (get_clauses_wl_heur S)\<le> snat64_max\<close> and
    \<open>arena_lit_pre (get_clauses_wl_heur S) (bf + baa)\<close>
  shows \<open>bf + baa \<le> snat64_max\<close>
       \<open>length (get_clauses_wl_heur S) \<le> snat64_max\<close>
  using assms
  by (auto simp: arena_is_valid_clause_idx_and_access_def isasat_fast_def
    dest!: arena_lifting(10))

end
