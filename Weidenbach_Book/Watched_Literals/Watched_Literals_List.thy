theory Watched_Literals_List
  imports More_Sepref.WB_More_Refinement_List Watched_Literals_Algorithm CDCL.DPLL_CDCL_W_Implementation
    Watched_Literals_Clauses
begin


chapter \<open>Second Refinement: Lists as Clause\<close>

declare RETURN_as_SPEC_refine[refine2]

lemma mset_take_mset_drop_mset: \<open>(\<lambda>x. mset (take 2 x) + mset (drop 2 x)) = mset\<close>
  unfolding mset_append[symmetric] append_take_drop_id ..

lemma mset_take_mset_drop_mset': \<open>mset (take 2 x) + mset (drop 2 x) = mset x\<close>
  unfolding mset_append[symmetric] append_take_drop_id ..

lemma uminus_lit_of_image_mset:
  \<open>{#- lit_of x . x \<in># A#} = {#- lit_of x. x \<in># B#} \<longleftrightarrow>
     {#lit_of x . x \<in># A#} = {#lit_of x. x \<in># B#}\<close>
  for A :: \<open>('a literal, 'a literal, 'b) annotated_lit multiset\<close>
proof -
  have 1: \<open>(\<lambda>x. -lit_of x) `# A = uminus `# lit_of `# A\<close>
    for A :: \<open>('d::uminus, 'd, 'e) annotated_lit multiset\<close>
    by auto
  show ?thesis
    unfolding 1
    by (rule inj_image_mset_eq_iff) (auto simp: inj_on_def)
qed

lemma twl_struct_invs_no_alien_in_trail:
  assumes \<open>twl_struct_invs S\<close>
  shows \<open>L \<in> lits_of_l (get_trail S) \<Longrightarrow>
    L \<in># all_lits_of_mm (clauses (get_clauses S) +
       unit_clss S + subsumed_clauses S)\<close>
  using assms by (cases S)
   (auto simp: twl_struct_invs_def pcdcl_all_struct_invs_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.no_strange_atm_def trail.simps
    init_clss.simps learned_clss.simps
    in_all_lits_of_mm_ain_atms_of_iff)


section \<open>Types\<close>
type_synonym 'v clauses_to_update_l = \<open>nat multiset\<close>

type_synonym 'v cconflict = \<open>'v clause option\<close>
type_synonym 'v cconflict_l = \<open>'v literal list option\<close>

type_synonym 'v twl_st_l =
  \<open>('v, nat) ann_lits \<times> 'v clauses_l \<times> 'v cconflict \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times>
   'v clauses \<times> 'v clauses_to_update_l \<times> 'v lit_queue\<close>

fun clauses_to_update_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses_to_update_l\<close> where
  \<open>clauses_to_update_l (_, _, _, _, _, _, _, WS, _) = WS\<close>

fun get_trail_l :: \<open>'v twl_st_l \<Rightarrow> ('v, nat) ann_lit list\<close> where
  \<open>get_trail_l (M, _, _, _, _, _, _) = M\<close>

fun set_clauses_to_update_l :: \<open>'v clauses_to_update_l \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>set_clauses_to_update_l WS (M, N, D, NE, UE, NS, US, _, Q) = (M, N, D, NE, UE, NS, US, WS, Q)\<close>

fun literals_to_update_l :: \<open>'v twl_st_l \<Rightarrow> 'v clause\<close> where
  \<open>literals_to_update_l (_, _, _, _, _, _, _, _, Q) = Q\<close>

fun set_literals_to_update_l :: \<open>'v clause \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>set_literals_to_update_l Q (M, N, D, NE, UE, NS, US, WS, _) = (M, N, D, NE, UE, NS, US, WS, Q)\<close>

fun get_conflict_l :: \<open>'v twl_st_l \<Rightarrow> 'v cconflict\<close> where
  \<open>get_conflict_l (_, _, D, _, _, _, _) = D\<close>

fun get_clauses_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses_l\<close> where
  \<open>get_clauses_l (M, N, D, NE, UE, NS, US, WS, Q) = N\<close>

fun get_unit_clauses_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_clauses_l (M, N, D, NE, UE, NS, US, WS, Q) = NE + UE\<close>

fun get_unit_init_clauses_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_init_clauses_l (M, N, D, NE, UE, NS, US, WS, Q) = NE\<close>

fun get_unit_learned_clss_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_learned_clss_l (M, N, D, NE, UE, NS, US, WS, Q) = UE\<close>

fun get_init_clauses :: \<open>'v twl_st \<Rightarrow> 'v twl_clss\<close> where
  \<open>get_init_clauses (M, N, U, D, NE, UE, NS, US, WS, Q) = N\<close>

fun get_unit_init_clauses :: \<open>'v twl_st_l \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_init_clauses (M, N, D, NE, UE, NS, US, WS, Q) = NE\<close>

definition get_learned_clss_l :: \<open>'v twl_st_l \<Rightarrow> 'v clause_l multiset\<close> where
  \<open>get_learned_clss_l S = learned_clss_lf (get_clauses_l S)\<close>

definition get_init_clss_l :: \<open>'v twl_st_l \<Rightarrow> 'v clause_l multiset\<close> where
  \<open>get_init_clss_l S = init_clss_lf (get_clauses_l S)\<close>

fun get_subsumed_init_clauses_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_init_clauses_l (M, N, D, NE, UE, NS, US, WS, Q) = NS\<close>

fun get_subsumed_learned_clauses_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_learned_clauses_l (M, N, D, NE, UE, NS, US, WS, Q) = US\<close>

fun get_subsumed_clauses_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_clauses_l (M, N, D, NE, UE, NS, US, WS, Q) = NS + US\<close>

abbreviation get_all_clss_l :: \<open>'v twl_st_l \<Rightarrow> 'v clause multiset\<close> where
  \<open>get_all_clss_l S \<equiv>
     mset `# ran_mf (get_clauses_l S) + get_unit_clauses_l S + get_subsumed_clauses_l S\<close>

abbreviation get_all_init_clss_l :: \<open>'v twl_st_l \<Rightarrow> 'v clause multiset\<close> where
  \<open>get_all_init_clss_l S \<equiv> mset `# get_init_clss_l S + get_unit_init_clauses_l S + get_subsumed_init_clauses_l S\<close>

abbreviation get_all_learned_clss_l :: \<open>'v twl_st_l \<Rightarrow> 'v clause multiset\<close> where
  \<open>get_all_learned_clss_l S \<equiv> mset `# get_learned_clss_l S + get_unit_learned_clss_l S + get_subsumed_learned_clauses_l S\<close>

lemma state_decomp_to_state:
  \<open>(case S of (M, N, U, D, NE, UE, NS, US, WS, Q) \<Rightarrow> P M N U D NE UE NS US WS Q) =
     P (get_trail S) (get_init_clauses S) (get_learned_clss S) (get_conflict S)
        (unit_init_clauses S) (get_init_learned_clss S)
        (subsumed_init_clauses S) (subsumed_learned_clauses S)
        (clauses_to_update S)
        (literals_to_update S)\<close>
  by (cases S) auto


lemma state_decomp_to_state_l:
  \<open>(case S of (M, N, D, NE, UE, NS, US, WS, Q) \<Rightarrow> P M N D NE UE NS US WS Q) =
     P (get_trail_l S) (get_clauses_l S) (get_conflict_l S)
        (get_unit_init_clauses_l S) (get_unit_learned_clss_l S)
        (get_subsumed_init_clauses_l S) (get_subsumed_learned_clauses_l S)
        (clauses_to_update_l S)
        (literals_to_update_l S)\<close>
  by (cases S) auto

definition set_conflict' :: \<open>'v clause option \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>set_conflict' = (\<lambda>C (M, N, U, D, NE, UE, NS, US, WS, Q). (M, N, U, C, NE, UE, NS, US, WS, Q))\<close>

inductive convert_lit
  :: \<open>'v clauses_l \<Rightarrow> 'v clauses \<Rightarrow>  ('v, nat) ann_lit \<Rightarrow> ('v, 'v clause) ann_lit \<Rightarrow> bool\<close>
where
  \<open>convert_lit N E (Decided K) (Decided K)\<close> |
  \<open>convert_lit N E (Propagated K C) (Propagated K C')\<close>
    if \<open>C' = mset (N \<propto> C)\<close> \<open>C \<in># dom_m N\<close> and \<open>C \<noteq> 0\<close> |
  \<open>convert_lit N E (Propagated K C) (Propagated K C')\<close>
    if \<open>C = 0\<close> and \<open>C' \<in># E\<close>

definition convert_lits_l where
  \<open>convert_lits_l N E = \<langle>p2rel (convert_lit N E)\<rangle> list_rel\<close>

lemma convert_lits_l_nil[simp]:
  \<open>([], a) \<in> convert_lits_l N E \<longleftrightarrow> a = []\<close>
  \<open>(b, []) \<in> convert_lits_l N E \<longleftrightarrow> b = []\<close>
  by (auto simp: convert_lits_l_def)

lemma convert_lits_l_cons[simp]:
  \<open>(L # M, L' # M') \<in> convert_lits_l N E \<longleftrightarrow>
     convert_lit N E L L' \<and> (M, M') \<in> convert_lits_l N E\<close>
  by (auto simp: convert_lits_l_def p2rel_def)


lemma take_convert_lits_lD:
  \<open>(M, M') \<in> convert_lits_l N E \<Longrightarrow>
     (take n M, take n M') \<in> convert_lits_l N E\<close>
  by (auto simp: convert_lits_l_def list_rel_def)

lemma convert_lits_l_consE:
  \<open>(Propagated L C # M, x) \<in> convert_lits_l N E \<Longrightarrow>
    (\<And>L' C' M'. x = Propagated L' C' # M' \<Longrightarrow> (M, M') \<in> convert_lits_l N E \<Longrightarrow>
       convert_lit N E (Propagated L C) (Propagated L' C') \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (cases x) (auto simp: convert_lit.simps)

lemma convert_lits_l_append[simp]:
  \<open>length M1 = length M1' \<Longrightarrow>
  (M1 @ M2, M1' @ M2') \<in> convert_lits_l N E \<longleftrightarrow> (M1, M1') \<in> convert_lits_l N E \<and>
           (M2, M2') \<in> convert_lits_l N E \<close>
  by (auto simp: convert_lits_l_def list_rel_append2 list_rel_imp_same_length)

lemma convert_lits_l_map_lit_of: \<open>(ay, bq) \<in> convert_lits_l N e \<Longrightarrow> map lit_of ay = map lit_of bq\<close>
  apply (induction ay arbitrary: bq)
  subgoal by auto
  subgoal for L M bq by (cases bq) (auto simp: convert_lit.simps)
  done

lemma convert_lits_l_tlD:
  \<open>(M, M') \<in> convert_lits_l N E \<Longrightarrow>
     (tl M, tl M') \<in> convert_lits_l N E\<close>
  by (cases M; cases M') auto

lemma convert_lits_l_swap:
  \<open>i < length (N \<propto> C) \<Longrightarrow> j < length (N \<propto> C) \<Longrightarrow> C \<in># dom_m N \<Longrightarrow>
    (M, M') \<in> convert_lits_l (N(C \<hookrightarrow>swap (N \<propto> C) i j)) E \<longleftrightarrow>
     (M, M') \<in> convert_lits_l N E\<close>
  by (fastforce simp: convert_lits_l_def list_rel_def p2rel_def
      convert_lit.simps list_all2_conv_all_nth)

lemma get_clauses_l_set_clauses_to_update_l[simp]:
  \<open>get_clauses_l (set_clauses_to_update_l WC S) = get_clauses_l S\<close>
  by (cases S) auto

lemma get_trail_l_set_clauses_to_update_l[simp]:
  \<open>get_trail_l (set_clauses_to_update_l WC S) = get_trail_l S\<close>
  by (cases S) auto

lemma get_trail_set_clauses_to_update[simp]:
  \<open>get_trail (set_clauses_to_update WC S) = get_trail S\<close>
  by (cases S) auto

lemma convert_lits_l_add_mset:
  \<open>(M, M') \<in> convert_lits_l N E \<Longrightarrow>
     (M, M') \<in> convert_lits_l N (add_mset C E)\<close>
  by (fastforce simp: convert_lits_l_def list_rel_def p2rel_def
      convert_lit.simps list_all2_conv_all_nth)

lemma convert_lit_bind_new:
  \<open>C \<notin># dom_m N \<Longrightarrow> C > 0 \<Longrightarrow>
    convert_lit N E L L'\<Longrightarrow>
    convert_lit (N(C \<hookrightarrow> C')) E L L'\<close>
  \<open>C \<notin># dom_m N \<Longrightarrow> C > 0 \<Longrightarrow>
    convert_lit N E L L'\<Longrightarrow>
    convert_lit (fmupd C C'' N) E L L'\<close>
  by (auto simp: convert_lit.simps)

lemma convert_lits_l_bind_new:
  \<open>C \<notin># dom_m N \<Longrightarrow> C > 0 \<Longrightarrow>
    (M, M') \<in> convert_lits_l N E \<Longrightarrow>
    (M, M') \<in> convert_lits_l (N(C \<hookrightarrow> C')) E\<close>
  \<open>C \<notin># dom_m N \<Longrightarrow> C > 0 \<Longrightarrow>
    (M, M') \<in> convert_lits_l N E \<Longrightarrow>
    (M, M') \<in> convert_lits_l (fmupd C C'' N) E\<close>
  by (auto simp: convert_lits_l_def list_rel_def p2rel_def
     list_all2_conv_all_nth convert_lit_bind_new)

abbreviation resolve_cls_l where
  \<open>resolve_cls_l L D' E \<equiv> union_mset_list (remove1 (-L) D') (remove1 L E)\<close>

lemma mset_resolve_cls_l_resolve_cls[iff]:
  \<open>mset (resolve_cls_l L D' E) = cdcl\<^sub>W_restart_mset.resolve_cls L (mset D') (mset E)\<close>
  by (auto simp: union_mset_list[symmetric])

lemma resolve_cls_l_nil_iff:
  \<open>resolve_cls_l L D' E = [] \<longleftrightarrow> cdcl\<^sub>W_restart_mset.resolve_cls L (mset D') (mset E) = {#}\<close>
  by (metis mset_resolve_cls_l_resolve_cls mset_zero_iff)


lemma lit_of_convert_lit[simp]:
  \<open>convert_lit N E L L' \<Longrightarrow> lit_of L' = lit_of L\<close>
  by (auto simp: p2rel_def convert_lit.simps)

lemma is_decided_convert_lit[simp]:
  \<open>convert_lit N E L L' \<Longrightarrow> is_decided L' \<longleftrightarrow> is_decided L\<close>
  by (cases L) (auto simp: p2rel_def convert_lit.simps)

lemma defined_lit_convert_lits_l[simp]: \<open>(M, M') \<in> convert_lits_l N E \<Longrightarrow>
  defined_lit M' = defined_lit M\<close>
  apply (induction M arbitrary: M')
   subgoal by auto
   subgoal for L M M'
     by (cases M')
       (auto simp: defined_lit_cons)
  done

lemma no_dup_convert_lits_l[simp]: \<open>(M, M') \<in> convert_lits_l N E \<Longrightarrow>
  no_dup M' \<longleftrightarrow> no_dup M\<close>
  apply (induction M arbitrary: M')
   subgoal by auto
   subgoal for L M M'
     by (cases M') auto
  done

lemma
  assumes \<open>(M, M') \<in> convert_lits_l N E\<close>
  shows
    count_decided_convert_lits_l[simp]:
      \<open>count_decided M' = count_decided M\<close>
  using assms
  apply (induction M arbitrary: M' rule: ann_lit_list_induct)
  subgoal by auto
  subgoal for L M M'
    by (cases M')
      (auto simp: convert_lits_l_def p2rel_def)
  subgoal for L C M M'
    by (cases M') (auto simp: convert_lits_l_def p2rel_def)
  done

lemma
  assumes \<open>(M, M') \<in> convert_lits_l N E\<close>
  shows
    get_level_convert_lits_l[simp]:
      \<open>get_level M' = get_level M\<close>
  using assms
  apply (induction M arbitrary: M' rule: ann_lit_list_induct)
  subgoal by auto
  subgoal for L M M'
    by (cases M')
       (fastforce simp: convert_lits_l_def p2rel_def get_level_cons_if split: if_splits)+
  subgoal for L C M M'
    by (cases M') (auto simp: convert_lits_l_def p2rel_def get_level_cons_if)
  done

lemma
  assumes \<open>(M, M') \<in> convert_lits_l N E\<close>
  shows
    get_maximum_level_convert_lits_l[simp]:
      \<open>get_maximum_level M' = get_maximum_level M\<close>
  by (intro ext, rule get_maximum_level_cong)
    (use assms in auto)

lemma list_of_l_convert_map_lit_of:
  assumes \<open>(M, M') \<in> convert_lits_l N E\<close>
  shows
      \<open>map lit_of M' = map lit_of M\<close>
  using assms
  apply (induction M arbitrary: M' rule: ann_lit_list_induct)
  subgoal by auto
  subgoal for L M M'
    by (cases M')
      (auto simp: convert_lits_l_def p2rel_def)
  subgoal for L C M M'
    by (cases M') (auto simp: convert_lits_l_def p2rel_def)
  done

lemma list_of_l_convert_lits_l[simp]:
  assumes \<open>(M, M') \<in> convert_lits_l N E\<close>
  shows
      \<open>lits_of_l M' = lits_of_l M\<close>
  using assms
  apply (induction M arbitrary: M' rule: ann_lit_list_induct)
  subgoal by auto
  subgoal for L M M'
    by (cases M')
      (auto simp: convert_lits_l_def p2rel_def)
  subgoal for L C M M'
    by (cases M') (auto simp: convert_lits_l_def p2rel_def)
  done

lemma is_proped_hd_convert_lits_l[simp]:
  assumes \<open>(M, M') \<in> convert_lits_l N E\<close> and \<open>M \<noteq> []\<close>
  shows \<open>is_proped (hd M') \<longleftrightarrow> is_proped (hd M)\<close>
  using assms
  apply (induction M arbitrary: M' rule: ann_lit_list_induct)
  subgoal by auto
  subgoal for L M M'
    by (cases M')
      (auto simp: convert_lits_l_def p2rel_def)
  subgoal for L C M M'
    by (cases M') (auto simp: convert_lits_l_def p2rel_def convert_lit.simps)
  done

lemma is_decided_hd_convert_lits_l[simp]:
  assumes \<open>(M, M') \<in> convert_lits_l N E\<close> and \<open>M \<noteq> []\<close>
  shows
    \<open>is_decided (hd M') \<longleftrightarrow> is_decided (hd M)\<close>
  by (meson assms(1) assms(2) is_decided_no_proped_iff is_proped_hd_convert_lits_l)

lemma lit_of_hd_convert_lits_l[simp]:
  assumes \<open>(M, M') \<in> convert_lits_l N E\<close> and \<open>M \<noteq> []\<close>
  shows
    \<open>lit_of (hd M') = lit_of (hd M)\<close>
  by (cases M; cases M') (use assms in auto)

lemma lit_of_l_convert_lits_l[simp]:
  assumes \<open>(M, M') \<in> convert_lits_l N E\<close>
  shows
      \<open>lit_of ` set M' = lit_of ` set M\<close>
  using assms
  apply (induction M arbitrary: M' rule: ann_lit_list_induct)
  subgoal by auto
  subgoal for L M M'
    by (cases M')
      (auto simp: convert_lits_l_def p2rel_def)
  subgoal for L C M M'
    by (cases M') (auto simp: convert_lits_l_def p2rel_def)
  done

text \<open>The order of the assumption is important for simpler use.\<close>
lemma convert_lits_l_extend_mono:
  assumes \<open>(a,b) \<in> convert_lits_l N E\<close>
     \<open>\<forall>L i. Propagated L i \<in> set a \<and> i \<in># dom_m N \<longrightarrow>
        mset (N\<propto>i) = mset (N'\<propto>i) \<and> i \<in># dom_m N'\<close> and
     \<open>E \<subseteq># E'\<close>
  shows
    \<open>(a,b) \<in> convert_lits_l N' E'\<close>
  using assms
  apply (induction a arbitrary: b rule: ann_lit_list_induct)
  subgoal by auto
  subgoal for l A b
    by (cases b)
      (auto simp: convert_lits_l_def p2rel_def convert_lit.simps)
  subgoal for l C A b
    by (cases b)
      (auto simp: convert_lits_l_def p2rel_def convert_lit.simps)
  done

lemma convert_lits_l_nil_iff[simp]:
  assumes \<open>(M, M') \<in> convert_lits_l N E\<close>
  shows
      \<open>M' = [] \<longleftrightarrow> M = []\<close>
  using assms by auto

lemma convert_lits_l_atm_lits_of_l:
  assumes \<open>(M, M') \<in> convert_lits_l N E\<close>
  shows \<open>atm_of ` lits_of_l M =  atm_of ` lits_of_l M'\<close>
  using assms by auto

lemma convert_lits_l_true_clss_clss[simp]:
  \<open>(M, M') \<in> convert_lits_l N E \<Longrightarrow> M' \<Turnstile>as C \<longleftrightarrow> M \<Turnstile>as C\<close>
  unfolding true_annots_true_cls
  by (auto simp: p2rel_def)

lemma convert_lit_propagated_decided[iff]:
  \<open>convert_lit b d (Propagated x21 x22) (Decided x1) \<longleftrightarrow> False\<close>
  by (auto simp: convert_lit.simps)

lemma convert_lit_decided[iff]:
  \<open>convert_lit b d (Decided x1) (Decided x2) \<longleftrightarrow> x1 = x2\<close>
  by (auto simp: convert_lit.simps)

lemma convert_lit_decided_propagated[iff]:
  \<open>convert_lit b d (Decided x1) (Propagated x21 x22) \<longleftrightarrow> False\<close>
  by (auto simp: convert_lit.simps)

lemma convert_lits_l_lit_of_mset[simp]:
  \<open>(a, af) \<in> convert_lits_l N E \<Longrightarrow> lit_of `# mset af = lit_of `# mset a\<close>
  apply (induction a arbitrary: af)
  subgoal by auto
  subgoal for L M af
    by (cases af) auto
  done


lemma convert_lits_l_imp_same_length:
  \<open>(a, b) \<in> convert_lits_l N E \<Longrightarrow> length a = length b\<close>
  by (auto simp: convert_lits_l_def list_rel_imp_same_length)

lemma convert_lits_l_decomp_ex:
  assumes
    H: \<open>(Decided K # a, M2) \<in> set (get_all_ann_decomposition x)\<close> and
    xxa: \<open>(x, xa) \<in> convert_lits_l aa ac\<close>
  shows \<open>\<exists>M2. (Decided K # drop (length xa - length a) xa, M2)
              \<in> set (get_all_ann_decomposition xa)\<close> (is ?decomp) and
        \<open>(a, drop (length xa - length a) xa) \<in> convert_lits_l aa ac\<close> (is ?a)
proof -
  from H obtain M3 where
     x: \<open>x = M3 @ M2 @ Decided K # a\<close>
    by blast
  obtain M3' M2' a' where
     xa: \<open>xa = M3' @ M2' @ Decided K # a'\<close> and
     \<open>(M3, M3') \<in> convert_lits_l aa ac\<close> and
     \<open>(M2, M2') \<in> convert_lits_l aa ac\<close> and
     aa': \<open>(a, a') \<in> convert_lits_l aa ac\<close>
    using xxa unfolding x
    by (auto simp: list_rel_append1 convert_lits_l_def p2rel_def convert_lit.simps
        list_rel_split_right_iff)
  then have a': \<open>a' = drop (length xa - length a) xa\<close> and [simp]: \<open>length xa \<ge> length a\<close>
    unfolding xa by (auto simp: convert_lits_l_imp_same_length)
  show ?decomp
    using get_all_ann_decomposition_ex[of K a' \<open>M3' @ M2'\<close>]
    unfolding xa
    unfolding a'
    by auto
  show ?a
    using aa' unfolding a' .
qed

lemma in_convert_lits_lD:
  \<open>K \<in> set TM \<Longrightarrow>
    (M, TM) \<in> convert_lits_l N NE \<Longrightarrow>
      \<exists>K'. K' \<in> set M \<and> convert_lit N NE K' K\<close>
  by (auto 5 5 simp: convert_lits_l_def list_rel_append2 dest!: split_list p2relD
    elim!: list_relE)

lemma in_convert_lits_lD2:
  \<open>K \<in> set M \<Longrightarrow>
    (M, TM) \<in> convert_lits_l N NE \<Longrightarrow>
      \<exists>K'. K' \<in> set TM \<and> convert_lit N NE K K'\<close>
  by (auto 5 5 simp: convert_lits_l_def list_rel_append1 dest!: split_list p2relD
    elim!: list_relE)

lemma convert_lits_l_filter_decided: \<open>(S, S') \<in> convert_lits_l M N \<Longrightarrow>
   map lit_of (filter is_decided S') = map lit_of (filter is_decided S)\<close>
  apply (induction S arbitrary: S')
  subgoal by auto
  subgoal for L S S'
    by (cases S') auto
  done

lemma convert_lits_lI:
  \<open>length M = length M' \<Longrightarrow> (\<And>i. i < length M \<Longrightarrow> convert_lit N NE (M!i) (M'!i)) \<Longrightarrow>
     (M, M') \<in> convert_lits_l N NE\<close>
  by (auto simp: convert_lits_l_def list_rel_def p2rel_def list_all2_conv_all_nth)

fun get_learned_clauses_l :: \<open>'v twl_st_l \<Rightarrow> 'v clause_l multiset\<close> where
  \<open>get_learned_clauses_l (M, N, D, NE, UE, WS, Q) = learned_clss_lf N\<close>

lemma get_subsumed_clauses_l_simps[simp]:
  \<open>get_subsumed_init_clauses_l (set_clauses_to_update_l K S) = get_subsumed_init_clauses_l S\<close>
  \<open>get_subsumed_learned_clauses_l (set_clauses_to_update_l K S) = get_subsumed_learned_clauses_l S\<close>
  \<open>get_subsumed_clauses_l (set_clauses_to_update_l K S) = get_subsumed_clauses_l S\<close>
  by (solves \<open>cases S; auto\<close>)+

definition twl_st_l   :: \<open>_ \<Rightarrow> ('v twl_st_l \<times> 'v twl_st) set\<close> where
\<open>twl_st_l L =
  {((M, N, C, NE, UE, NS, US, WS, Q),  (M', N', U', C', NE', UE', NS', US', WS', Q')).
      (M, M') \<in> convert_lits_l N (NE+UE) \<and>
      N' = twl_clause_of `# init_clss_lf N \<and>
      U' = twl_clause_of `# learned_clss_lf N \<and>
      C' = C \<and>
      NE' = NE \<and>
      UE' = UE \<and>
      NS' = NS \<and>
      US' = US \<and>
      WS' = (case L of None \<Rightarrow> {#} | Some L \<Rightarrow> image_mset (\<lambda>j. (L, twl_clause_of (N \<propto> j))) WS) \<and>
      Q' = Q
  }\<close>

lemma clss_state\<^sub>W_of[twl_st]:
  assumes \<open>(S, R) \<in> twl_st_l L\<close>
  shows
  \<open>init_clss (state\<^sub>W_of R) = mset `# (init_clss_lf (get_clauses_l S)) +
     get_unit_init_clauses_l S + get_subsumed_init_clauses_l S\<close>
  \<open>learned_clss (state\<^sub>W_of R) = mset `# (learned_clss_lf (get_clauses_l S)) +
     get_unit_learned_clss_l S + get_subsumed_learned_clauses_l S\<close>
 using assms
 by (cases S; cases R; cases L; auto simp: init_clss.simps learned_clss.simps twl_st_l_def
   mset_take_mset_drop_mset')+

named_theorems twl_st_l \<open>Conversions simp rules\<close>

lemma [twl_st_l]:
  assumes \<open>(S, T) \<in> twl_st_l L\<close>
  shows
    \<open>(get_trail_l S, get_trail T) \<in> convert_lits_l (get_clauses_l S) (get_unit_clauses_l S)\<close> and
    \<open>get_clauses T = twl_clause_of `# fst `# ran_m (get_clauses_l S)\<close> and
    \<open>get_conflict T = get_conflict_l S\<close> and
    \<open>L = None \<Longrightarrow> clauses_to_update T = {#}\<close>
    \<open>L \<noteq> None \<Longrightarrow> clauses_to_update T =
        (\<lambda>j. (the L, twl_clause_of (get_clauses_l S \<propto> j))) `# clauses_to_update_l S\<close> and
    \<open>literals_to_update T = literals_to_update_l S\<close>
    \<open>backtrack_lvl (state\<^sub>W_of T) = count_decided (get_trail_l S)\<close>
    \<open>unit_clss T = get_unit_clauses_l S\<close>
    \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of T) =
        mset `# ran_mf (get_clauses_l S) + get_unit_clauses_l S + get_subsumed_clauses_l S\<close> and
    \<open>no_dup (get_trail T) \<longleftrightarrow> no_dup (get_trail_l S)\<close> and
    \<open>lits_of_l (get_trail T) = lits_of_l (get_trail_l S)\<close> and
    \<open>count_decided (get_trail T) = count_decided (get_trail_l S)\<close> and
    \<open>get_trail T = [] \<longleftrightarrow> get_trail_l S = []\<close> and
    \<open>get_trail T \<noteq> [] \<longleftrightarrow> get_trail_l S \<noteq> []\<close> and
    \<open>get_trail T \<noteq> [] \<Longrightarrow> is_proped (hd (get_trail T)) \<longleftrightarrow> is_proped (hd (get_trail_l S))\<close>
    \<open>get_trail T \<noteq> [] \<Longrightarrow> is_decided (hd (get_trail T)) \<longleftrightarrow> is_decided (hd (get_trail_l S))\<close>
    \<open>get_trail T \<noteq> [] \<Longrightarrow> lit_of (hd (get_trail T)) = lit_of (hd (get_trail_l S))\<close>
    \<open>get_level (get_trail T) = get_level (get_trail_l S)\<close>
    \<open>get_maximum_level (get_trail T) = get_maximum_level (get_trail_l S)\<close>
    \<open>get_trail T \<Turnstile>as D \<longleftrightarrow> get_trail_l S \<Turnstile>as D\<close>
    \<open>subsumed_init_clauses T = get_subsumed_init_clauses_l S\<close>
    \<open>subsumed_learned_clauses T = get_subsumed_learned_clauses_l S\<close>
    \<open>subsumed_clauses T = get_subsumed_clauses_l S\<close>
    \<open>get_all_clss T = get_all_clss_l S\<close>
  using assms unfolding twl_st_l_def all_clss_lf_ran_m[symmetric]
  by (auto split: option.splits simp: trail.simps clauses_def mset_take_mset_drop_mset')

lemma (in -) [twl_st_l]:
 \<open>(S, T)\<in>twl_st_l b \<Longrightarrow>
   get_all_init_clss T = mset `# init_clss_lf (get_clauses_l S) + get_unit_init_clauses S +
     subsumed_init_clauses T\<close>
 \<open>(S, T)\<in>twl_st_l b \<Longrightarrow> get_all_learned_clss T = mset `# learned_clss_lf (get_clauses_l S) +
   get_unit_learned_clss_l S + get_subsumed_learned_clauses_l S\<close>
  by (cases S; cases T; cases b; auto simp: twl_st_l_def mset_take_mset_drop_mset'; fail)+


lemma [twl_st_l]:
  assumes \<open>(S, T) \<in> twl_st_l L\<close>
  shows \<open>lit_of ` set (get_trail T) = lit_of ` set (get_trail_l S)\<close>
  using twl_st_l[OF assms] unfolding lits_of_def
  by simp

lemma [twl_st_l]:
  \<open>get_trail_l (set_literals_to_update_l D S) = get_trail_l S\<close>
  by (cases S) auto

fun remove_one_lit_from_wq :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>remove_one_lit_from_wq L (M, N, D, NE, UE, NS, US, WS, Q) =
    (M, N, D, NE, UE, NS, US, remove1_mset L WS, Q)\<close>

lemma [twl_st_l]: \<open>get_conflict_l (set_clauses_to_update_l W S) = get_conflict_l S\<close>
  by (cases S) auto

lemma  [twl_st_l]: \<open>get_conflict_l (remove_one_lit_from_wq L S) = get_conflict_l S\<close>
  by (cases S) auto

lemma [twl_st_l]: \<open>literals_to_update_l (set_clauses_to_update_l Cs S) = literals_to_update_l S\<close>
  by (cases S) auto

lemma [twl_st_l]: \<open>get_unit_clauses_l (set_clauses_to_update_l Cs S) = get_unit_clauses_l S\<close>
  by (cases S) auto

lemma  [twl_st_l]: \<open>get_unit_clauses_l (remove_one_lit_from_wq L S) = get_unit_clauses_l S\<close>
  by (cases S) auto

lemma [twl_st_l]:
  \<open>get_unit_init_clauses_l (set_clauses_to_update_l Cs S) = get_unit_init_clauses_l S\<close>
  by (cases S; auto; fail)+

lemma [twl_st_l]:
  \<open>get_unit_init_clauses_l (remove_one_lit_from_wq L S) = get_unit_init_clauses_l S\<close>
  by (cases S; auto; fail)+

lemma [twl_st_l]:
  \<open>get_clauses_l (remove_one_lit_from_wq L S) = get_clauses_l S\<close>
  \<open>get_trail_l (remove_one_lit_from_wq L S) = get_trail_l S\<close>
  by (cases S; auto; fail)+

lemma [twl_st_l]:
  \<open>get_unit_learned_clss_l (set_clauses_to_update_l Cs S) = get_unit_learned_clss_l S\<close>
  by (cases S) auto

lemma [twl_st_l]:
  \<open>get_unit_learned_clss_l (remove_one_lit_from_wq L S) = get_unit_learned_clss_l S\<close>
  by (cases S) auto

lemma literals_to_update_l_remove_one_lit_from_wq[simp]:
  \<open>literals_to_update_l (remove_one_lit_from_wq L T) = literals_to_update_l T\<close>
  by (cases T) auto

lemma clauses_to_update_l_remove_one_lit_from_wq[simp]:
  \<open>clauses_to_update_l (remove_one_lit_from_wq L T) = remove1_mset L (clauses_to_update_l T)\<close>
  by (cases T) auto

declare twl_st_l[simp]

lemma unit_init_clauses_get_unit_init_clauses_l[twl_st_l]:
    \<open>(S, T) \<in> twl_st_l L \<Longrightarrow> unit_init_clauses T = get_unit_init_clauses_l S\<close> and
  get_init_learned_clss_get_init_learned_clss_l[twl_st_l]:
    \<open>(S, T) \<in> twl_st_l L \<Longrightarrow> get_init_learned_clss T = get_unit_learned_clss_l S\<close>
  by (cases S) (auto simp: twl_st_l_def init_clss.simps)

lemma clauses_state_to_l[twl_st_l]: \<open>(S, S') \<in> twl_st_l L \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of S') = mset `# ran_mf (get_clauses_l S) +
     get_unit_init_clauses_l S + get_unit_learned_clss_l S + get_subsumed_init_clauses_l S +
     get_subsumed_learned_clauses_l S\<close>
  apply (subst all_clss_l_ran_m[symmetric])
  unfolding image_mset_union
  by (cases S) (auto simp: twl_st_l_def init_clss.simps mset_take_mset_drop_mset' clauses_def)

lemma clauses_to_update_l_set_clauses_to_update_l[twl_st_l]:
  \<open>clauses_to_update_l (set_clauses_to_update_l WS S) = WS\<close>
  by (cases S) auto

lemma hd_get_trail_twl_st_of_get_trail_l:
  \<open>(S, T) \<in> twl_st_l L \<Longrightarrow> get_trail_l S \<noteq> [] \<Longrightarrow>
    lit_of (hd (get_trail T)) = lit_of (hd (get_trail_l S))\<close>
  by (cases S; cases \<open>get_trail_l S\<close>; cases \<open>get_trail T\<close>) (auto simp: twl_st_l_def)

lemma twl_st_l_mark_of_hd:
  \<open>(x, y) \<in> twl_st_l b \<Longrightarrow>
       get_trail_l x \<noteq> [] \<Longrightarrow>
       is_proped (hd (get_trail_l x)) \<Longrightarrow>
       mark_of (hd (get_trail_l x)) > 0 \<Longrightarrow>
       mark_of (hd (get_trail y)) = mset (get_clauses_l x \<propto> mark_of (hd (get_trail_l x)))\<close>
  by (cases \<open>get_trail_l x\<close>; cases \<open>get_trail y\<close>; cases \<open>hd (get_trail_l x)\<close>;
     cases \<open>hd (get_trail y)\<close>)
   (auto simp: twl_st_l_def convert_lit.simps)

lemma twl_st_l_lits_of_tl:
  \<open>(x, y) \<in> twl_st_l b \<Longrightarrow>
       lits_of_l (tl (get_trail y)) = (lits_of_l (tl (get_trail_l x)))\<close>
  by (cases \<open>get_trail_l x\<close>; cases \<open>get_trail y\<close>; cases \<open>hd (get_trail_l x)\<close>;
     cases \<open>hd (get_trail y)\<close>)
   (auto simp: twl_st_l_def convert_lit.simps)

lemma twl_st_l_mark_of_is_decided:
  \<open>(x, y) \<in> twl_st_l b \<Longrightarrow>
       get_trail_l x \<noteq> [] \<Longrightarrow>
       is_decided (hd (get_trail y)) = is_decided (hd (get_trail_l x))\<close>
  by (cases \<open>get_trail_l x\<close>; cases \<open>get_trail y\<close>; cases \<open>hd (get_trail_l x)\<close>;
     cases \<open>hd (get_trail y)\<close>)
   (auto simp: twl_st_l_def convert_lit.simps)

lemma twl_st_l_mark_of_is_proped:
  \<open>(x, y) \<in> twl_st_l b \<Longrightarrow>
       get_trail_l x \<noteq> [] \<Longrightarrow>
       is_proped (hd (get_trail y)) = is_proped (hd (get_trail_l x))\<close>
  by (cases \<open>get_trail_l x\<close>; cases \<open>get_trail y\<close>; cases \<open>hd (get_trail_l x)\<close>;
     cases \<open>hd (get_trail y)\<close>)
   (auto simp: twl_st_l_def convert_lit.simps)

lemma [simp]:
  \<open>get_clauses_l (set_literals_to_update_l L T) = get_clauses_l T\<close>
  \<open>get_unit_clauses_l (set_literals_to_update_l L T) = get_unit_clauses_l T\<close>
  \<open>get_subsumed_clauses_l (set_literals_to_update_l L T) = get_subsumed_clauses_l T\<close>
  by (cases T; auto; fail)+

fun equality_except_trail :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
\<open>equality_except_trail (M, N, D, NE, UE, NS, US, WS, Q) (M', N', D', NE', UE', NS', US', WS', Q') \<longleftrightarrow>
    N = N' \<and> D = D' \<and> NE = NE' \<and> UE = UE' \<and> NS = NS' \<and> US = US' \<and> WS = WS' \<and> Q = Q'\<close>

fun equality_except_conflict_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
\<open>equality_except_conflict_l (M, N, D, NE, UE, NS, US, WS, Q) (M', N', D', NE', UE', NS', US', WS', Q') \<longleftrightarrow>
    M = M' \<and> N = N' \<and> NE = NE' \<and> UE = UE' \<and> NS = NS' \<and> US = US' \<and> WS = WS' \<and> Q = Q'\<close>

lemma equality_except_conflict_l_rewrite:
  assumes \<open>equality_except_conflict_l S T\<close>
  shows
    \<open>get_trail_l S = get_trail_l T\<close> and
    \<open>get_clauses_l S = get_clauses_l T\<close>
  using assms by (cases S; cases T; auto; fail)+

lemma equality_except_conflict_l_alt_def:
 \<open>equality_except_conflict_l S T \<longleftrightarrow>
   get_trail_l S = get_trail_l T \<and> get_clauses_l S = get_clauses_l T \<and>
      get_unit_init_clauses_l S = get_unit_init_clauses_l T \<and>
      get_unit_learned_clss_l S = get_unit_learned_clss_l T \<and>
      literals_to_update_l S = literals_to_update_l T \<and>
      clauses_to_update_l S = clauses_to_update_l T \<and>
      get_subsumed_learned_clauses_l S = get_subsumed_learned_clauses_l T \<and>
      get_subsumed_init_clauses_l S = get_subsumed_init_clauses_l T\<close>
  by (cases S, cases T) auto

lemma equality_except_conflict_alt_def:
 \<open>equality_except_conflict S T \<longleftrightarrow>
   get_trail S = get_trail T \<and> get_init_clauses S = get_init_clauses T \<and>
      get_learned_clss S = get_learned_clss T \<and>
      get_init_learned_clss S = get_init_learned_clss T \<and>
      unit_init_clauses S = unit_init_clauses T \<and>
      literals_to_update S = literals_to_update T \<and>
      clauses_to_update S = clauses_to_update T \<and>
      subsumed_learned_clauses S = subsumed_learned_clauses T \<and>
      subsumed_init_clauses S = subsumed_init_clauses T\<close>
  by (cases S, cases T) auto


section \<open>Additional Invariants and Definitions\<close>

definition twl_list_invs where
  \<open>twl_list_invs S \<longleftrightarrow>
    (\<forall>C \<in># clauses_to_update_l S. C \<in># dom_m (get_clauses_l S)) \<and>
    0 \<notin># dom_m (get_clauses_l S) \<and>
    (\<forall>L C. Propagated L C \<in> set (get_trail_l S) \<longrightarrow> (C > 0 \<longrightarrow> C \<in># dom_m (get_clauses_l S) \<and>
      (C > 0 \<longrightarrow> L \<in> set (watched_l (get_clauses_l S \<propto> C)) \<and>
          (length (get_clauses_l S \<propto> C) > 2 \<longrightarrow> L = get_clauses_l S \<propto> C ! 0)))) \<and>
    distinct_mset (clauses_to_update_l S)\<close>

definition polarity where
  \<open>polarity M L =
    (if undefined_lit M L then None else if L \<in> lits_of_l M then Some True else Some False)\<close>

lemma polarity_None_undefined_lit: \<open>is_None (polarity M L) \<Longrightarrow> undefined_lit M L\<close>
  by (auto simp: polarity_def split: if_splits)

lemma polarity_spec:
  assumes \<open>no_dup M\<close>
  shows
    \<open>RETURN (polarity M L) \<le> SPEC(\<lambda>v. (v = None \<longleftrightarrow> undefined_lit M L) \<and>
      (v = Some True \<longleftrightarrow> L \<in> lits_of_l M) \<and> (v = Some False \<longleftrightarrow> -L \<in> lits_of_l M))\<close>
  unfolding polarity_def
  by refine_vcg
    (use assms in \<open>auto simp: defined_lit_map lits_of_def atm_of_eq_atm_of uminus_lit_swap
      no_dup_cannot_not_lit_and_uminus
      split: option.splits\<close>)

lemma polarity_spec':
  assumes \<open>no_dup M\<close>
  shows
    \<open>polarity M L = None \<longleftrightarrow> undefined_lit M L\<close> and
    \<open>polarity M L = Some True \<longleftrightarrow> L \<in> lits_of_l M\<close> and
    \<open>polarity M L = Some False \<longleftrightarrow> -L \<in> lits_of_l M\<close>
  unfolding polarity_def
  by (use assms in \<open>auto simp: defined_lit_map lits_of_def atm_of_eq_atm_of uminus_lit_swap
      no_dup_cannot_not_lit_and_uminus
      split: option.splits\<close>)

definition mop_polarity_l :: \<open>'v twl_st_l \<Rightarrow> 'v literal \<Rightarrow> bool option nres\<close> where
\<open>mop_polarity_l S L = do {
    ASSERT(L \<in># all_lits_of_mm (get_all_clss_l S));
    ASSERT(no_dup (get_trail_l S));
    RETURN(polarity (get_trail_l S) L)
}\<close>

definition find_unwatched_l :: \<open>('v, _) ann_lits \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
  \<open>find_unwatched_l M N C = do {
    ASSERT(C \<in># dom_m N \<and> length (N \<propto> C) \<ge> 2 \<and> distinct (N \<propto> C) \<and> no_dup M);
    SPEC (\<lambda>(found).
      (found = None \<longleftrightarrow> (\<forall>L\<in>set (unwatched_l (N \<propto> C)). -L \<in> lits_of_l M)) \<and>
      (\<forall>j. found = Some j \<longrightarrow> (j < length (N \<propto> C) \<and> (undefined_lit M (N \<propto> C!j) \<or> N \<propto> C!j \<in> lits_of_l M) \<and> j \<ge> 2)))
   }\<close>

definition set_conflict_l_pre :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
\<open>set_conflict_l_pre C S \<longleftrightarrow>
  get_conflict_l S = None \<and> C \<in># dom_m (get_clauses_l S) \<and> \<not>tautology (mset (get_clauses_l S \<propto> C)) \<and> distinct (get_clauses_l S \<propto> C) \<and>
  get_trail_l S \<Turnstile>as CNot (mset (get_clauses_l S \<propto> C)) \<and>
  (\<exists>S' b. (set_clauses_to_update_l (clauses_to_update_l S + {#C#}) S, S') \<in> twl_st_l b \<and> twl_struct_invs S' \<and> twl_stgy_invs S')\<close>

definition set_conflict_l :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>set_conflict_l = (\<lambda>C (M, N, D, NE, UE, NS, US, WS, Q). do {
      ASSERT(set_conflict_l_pre C (M, N, D, NE, UE, NS, US, WS, Q));
      RETURN (M, N, Some (mset (N \<propto> C)), NE, UE, NS, US, {#}, {#})
   })\<close>


definition cons_trail_propagate_l where
  \<open>cons_trail_propagate_l L C M = do {
     ASSERT(undefined_lit M L);
     RETURN (Propagated L C # M)
}\<close>

definition propagate_lit_l :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>propagate_lit_l = (\<lambda>L' C i (M, N, D, NE, UE, NS, US, WS, Q). do {
      ASSERT(C \<in># dom_m N);
      ASSERT(L' \<in># all_lits_of_mm (get_all_clss_l (M, N, D, NE, UE, NS, US, WS, Q)));
      ASSERT(i \<le> 1);
      M \<leftarrow> cons_trail_propagate_l L' C M;
      N \<leftarrow> (if length (N \<propto> C) > 2 then mop_clauses_swap N C 0 (Suc 0 - i) else RETURN N);
      RETURN (M, N, D, NE, UE, NS, US, WS, add_mset (-L') Q)})\<close>

definition update_clause_l_pre :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>update_clause_l_pre C i f S \<longleftrightarrow>
    (\<exists>S' L. (S, S') \<in> twl_st_l (Some L) \<and> C \<in># dom_m (get_clauses_l S) \<and>
     i < length (get_clauses_l S \<propto> C) \<and> f < length (get_clauses_l S \<propto> C) \<and>
    update_clauseS_pre (get_clauses_l S \<propto> C ! i) (twl_clause_of (get_clauses_l S \<propto> C))  S')\<close>

definition update_clause_l :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>update_clause_l = (\<lambda>C i f (M, N, D, NE, UE, NS, US, WS, Q). do {
       ASSERT(update_clause_l_pre C i f (M, N, D, NE, UE, NS, US, WS, Q));
       N' \<leftarrow> mop_clauses_swap N C i f;
       RETURN (M, N', D, NE, UE, NS, US, WS, Q)
  })\<close>

definition unit_propagation_inner_loop_body_l_inv
  :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close>
where
  \<open>unit_propagation_inner_loop_body_l_inv L C S \<longleftrightarrow>
   (\<exists>S'. (set_clauses_to_update_l (clauses_to_update_l S + {#C#}) S, S') \<in> twl_st_l (Some L) \<and>
    twl_struct_invs S' \<and>
    twl_stgy_invs S' \<and>
    C \<in># dom_m (get_clauses_l S) \<and>
    C > 0 \<and>
    0 < length (get_clauses_l S \<propto> C) \<and>
    no_dup (get_trail_l S) \<and>
    (if (get_clauses_l S \<propto> C) ! 0 = L then 0 else 1) < length (get_clauses_l S \<propto> C) \<and>
    1 - (if (get_clauses_l S \<propto> C) ! 0 = L then 0 else 1) < length (get_clauses_l S \<propto> C) \<and>
    L \<in> set (watched_l (get_clauses_l S \<propto> C)) \<and>
    get_conflict_l S = None
  )
  \<close>

definition pos_of_watched :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> nat nres\<close> where
  \<open>pos_of_watched N C L = do {
     ASSERT(length (N \<propto> C) > 0 \<and> C \<in># dom_m N);
     RETURN (if (N \<propto> C) ! 0 = L then 0 else 1)
  }\<close>

definition other_watched_l :: \<open>'v twl_st_l \<Rightarrow> 'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v literal nres\<close> where
  \<open>other_watched_l S L C i = do {
    ASSERT(get_clauses_l S \<propto> C ! i = L \<and> i < length (get_clauses_l S \<propto> C) \<and> i < 2 \<and>
      C \<in># dom_m (get_clauses_l S) \<and> 1-i < length (get_clauses_l S \<propto> C));
    mop_clauses_at (get_clauses_l S) C (1 - i)
  }\<close>

definition unit_propagation_inner_loop_body_l :: \<open>'v literal \<Rightarrow> nat \<Rightarrow>
  'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>unit_propagation_inner_loop_body_l L C S = do {
      ASSERT(unit_propagation_inner_loop_body_l_inv L C S);
      K \<leftarrow> SPEC(\<lambda>K. K \<in> set (get_clauses_l S \<propto> C));
      val_K \<leftarrow> mop_polarity_l S K;
      if val_K = Some True
      then RETURN S
      else do {
        i \<leftarrow> pos_of_watched (get_clauses_l S) C L;
        L' \<leftarrow> other_watched_l S L C i;
        val_L' \<leftarrow> mop_polarity_l S L';
        if val_L' = Some True
        then RETURN S
        else do {
            f \<leftarrow> find_unwatched_l (get_trail_l S) (get_clauses_l S) C;
            case f of
              None \<Rightarrow>
                if val_L' = Some False
                then set_conflict_l C S
                else propagate_lit_l L' C i S
            | Some f \<Rightarrow> do {
                ASSERT(f < length (get_clauses_l S \<propto> C));
                K \<leftarrow> mop_clauses_at (get_clauses_l S) C f;
                val_K \<leftarrow> mop_polarity_l S K;
                if val_K = Some True then
                  RETURN S
                else
                  update_clause_l C i f S
              }
          }
      }
   }\<close>

lemma refine_add_invariants:
  assumes
    \<open>(f S) \<le> SPEC(\<lambda>S'. Q S')\<close> and
    \<open>y \<le> \<Down> {(S, S'). P S S'} (f S)\<close>
  shows \<open>y \<le> \<Down> {(S, S'). P S S' \<and> Q S'} (f S)\<close>
  using assms unfolding pw_le_iff pw_conc_inres pw_conc_nofail by force

lemma clauses_tuple[simp]:
  \<open>cdcl\<^sub>W_restart_mset.clauses (M, {#f x . x \<in># init_clss_l N#} + NE,
     {#f x . x \<in># learned_clss_l N#} + UE, D) = {#f x. x \<in># all_clss_l N#} + NE + UE\<close>
  by (auto simp: clauses_def simp flip: image_mset_union)

lemma valid_enqueued_alt_simps[simp]:
  \<open>valid_enqueued S \<longleftrightarrow>
    (\<forall>(L, C) \<in># clauses_to_update S. L \<in># watched C \<and> C \<in># get_clauses S \<and>
       -L \<in> lits_of_l (get_trail S) \<and> get_level (get_trail S) L = count_decided (get_trail S)) \<and>
     (\<forall>L \<in># literals_to_update S.
          -L \<in> lits_of_l (get_trail S) \<and> get_level (get_trail S) L = count_decided (get_trail S))\<close>
  by (cases S) auto

declare valid_enqueued.simps[simp del]

lemma unit_propagation_inner_loop_body_alt_def:
  \<open>unit_propagation_inner_loop_body L C S = do {
      bL' \<leftarrow> SPEC (\<lambda>K. K \<in># clause C);
      val_bL' \<leftarrow> mop_lit_is_pos bL' S;
      if val_bL'
      then RETURN S
      else do {
        i \<leftarrow> RETURN ();
        L' \<leftarrow> SPEC (\<lambda>K. K \<in># watched C - {#L#});
        ASSERT (watched C = {#L, L'#});
        val_L' \<leftarrow> mop_lit_is_pos L' S;
        if val_L'
        then RETURN S
        else
          if \<forall>L \<in># unwatched C. -L \<in> lits_of_l (get_trail S)
          then
            if -L' \<in> lits_of_l (get_trail S)
            then do {mop_set_conflicting C S}
            else do {mop_propagate_lit L' C S}
          else do {
            update_clauseS L C S
          }
      }
    }\<close>
  unfolding unit_propagation_inner_loop_body_def bind_to_let_conv Let_def
  by (auto intro!: ext)

lemma [twl_st, simp]:
  \<open>get_clauses (set_clauses_to_update C S') = get_clauses S'\<close>
  \<open>unit_clss (set_clauses_to_update C S') = unit_clss S'\<close>
  \<open>(S, S') \<in> twl_st_l (Some L) \<Longrightarrow>
     clauses (get_clauses S') = {#mset (fst x). x \<in># ran_m (get_clauses_l S)#}\<close>
  apply (cases S'; auto simp: twl_st_l_def clauses_def)
  apply (cases S'; auto simp: twl_st_l_def clauses_def)
  apply (cases S'; auto simp: twl_st_l_def clauses_def mset_take_mset_drop_mset'
    simp flip: image_mset_union)
  done

lemma in_set_takeI:
   \<open>i < j \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i \<in> set (take j xs)\<close>
  by (auto simp: in_set_take_conv_nth intro!: exI[of _ i])

lemma unit_propagation_inner_loop_body_l:
  fixes i C :: nat and S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st\<close> and L :: \<open>'v literal\<close>
  defines
    C'[simp]: \<open>C' \<equiv> get_clauses_l S \<propto> C\<close>
  assumes
    SS': \<open>(S, S') \<in> twl_st_l (Some L)\<close> and
    WS: \<open>C \<in># clauses_to_update_l S\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    add_inv: \<open>twl_list_invs S\<close> and
    stgy_inv: \<open>twl_stgy_invs S'\<close>
  shows
    \<open>unit_propagation_inner_loop_body_l L C
        (set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S) \<le>
        \<Down> {(S, S'). ((S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S) \<and>
           (twl_stgy_invs S' \<and> twl_struct_invs S')}
          (unit_propagation_inner_loop_body L (twl_clause_of C')
             (set_clauses_to_update (clauses_to_update (S') - {#(L, twl_clause_of C')#}) S'))\<close>
    (is \<open>?A \<le> \<Down> _ ?B\<close>)
proof -

  have C_0: \<open>C > 0\<close> and C_neq_0[iff]: \<open>C \<noteq> 0\<close>
    using assms(3,5) unfolding twl_list_invs_def by (auto dest!: multi_member_split)

  have C_N_U: \<open>C \<in># dom_m (get_clauses_l S)\<close>
    using add_inv WS SS' by (auto simp: twl_list_invs_def)

  let ?S = \<open>set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S\<close>
  define i :: nat where \<open>i \<equiv> (if get_clauses_l S\<propto>C!0 = L then 0 else 1)\<close>
  let ?L = \<open>C' ! i\<close>
  let ?L' = \<open>C' ! (Suc 0 - i)\<close>
  have inv: \<open>twl_st_inv S'\<close> and
    cdcl_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S')\<close> and
    valid: \<open>valid_enqueued S'\<close>
    using struct_invs WS by (auto simp: twl_struct_invs_def pcdcl_all_struct_invs_def)
  have
    w_q_inv: \<open>clauses_to_update_inv S'\<close> and
    dist: \<open>distinct_queued S'\<close> and
    no_dup: \<open>no_duplicate_queued S'\<close> and
    confl: \<open>get_conflict S' \<noteq> None \<Longrightarrow> clauses_to_update S' = {#} \<and> literals_to_update S' = {#}\<close> and
    st_inv: \<open>twl_st_inv S'\<close>
    using struct_invs unfolding twl_struct_invs_def by fast+
  have dist_C: \<open>distinct (get_clauses_l S \<propto> C)\<close>
    using cdcl_inv SS' C_N_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_alt_def pcdcl_all_struct_invs_def
    by (auto simp: ran_m_def dest!: multi_member_split)

  let ?M = \<open>get_trail_l S\<close>
  let ?N = \<open>get_clauses_l S\<close>
  let ?WS = \<open>clauses_to_update_l S\<close>
  let ?Q = \<open>literals_to_update_l S\<close>


  have n_d: \<open>no_dup ?M\<close> and confl_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of S')\<close>
    using cdcl_inv SS' unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: trail.simps comp_def twl_st)

  then have consistent: \<open>- L \<notin> lits_of_l ?M\<close> if \<open>L \<in> lits_of_l ?M\<close> for L
    using consistent_interp_def distinct_consistent_interp that by blast

  have cons_M: \<open>consistent_interp (lits_of_l ?M)\<close>
    using n_d distinct_consistent_interp by fast
  let ?C' = \<open>twl_clause_of C'\<close>
  have C'_N_U_or: \<open>?C' \<in># twl_clause_of `# (init_clss_lf ?N) \<or>
      ?C' \<in># twl_clause_of `# learned_clss_lf ?N\<close>
    using WS valid SS'
    unfolding union_iff[symmetric] image_mset_union[symmetric]  mset_append[symmetric]
    by (auto simp: twl_struct_invs_def
        split: prod.splits simp del: twl_clause_of.simps)
  have struct: \<open>struct_wf_twl_cls ?C'\<close>
    using C_N_U inv SS' WS valid unfolding valid_enqueued_alt_simps
    by (auto simp: twl_st_inv_alt_def Ball_ran_m_dom_struct_wf
      simp del: twl_clause_of.simps)
  have C'_N_U: \<open>?C' \<in># twl_clause_of `# all_clss_lf ?N\<close>
    using C'_N_U_or
    unfolding union_iff[symmetric] image_mset_union[symmetric]  mset_append[symmetric] .
  have watched_C': \<open>mset (watched_l C') = {#?L, ?L'#}\<close>
    using struct i_def SS' by (cases C) (auto simp: length_list_2 take_2_if)
  then have mset_watched_C: \<open>mset (watched_l C') = {#watched_l C' ! i, watched_l C' ! (Suc 0 - i)#}\<close>
    using i_def by (cases \<open>twl_clause_of (get_clauses_l S \<propto> C)\<close>) (auto simp: take_2_if)
  have two_le_length_C: \<open>2 \<le> length C'\<close>
    by (metis length_take linorder_not_le min_less_iff_conj numeral_2_eq_2 order_less_irrefl
    size_add_mset size_eq_0_iff_empty size_mset watched_C')
  then have i_le_length_C: \<open>i < length C'\<close>
    by (auto simp: i_def)
  obtain WS' where WS'_def: \<open>?WS = add_mset C WS'\<close>
    using multi_member_split[OF WS] by auto
  then have WS'_def': \<open>?WS = add_mset C WS'\<close>
    by auto
  have L: \<open>L \<in> set (watched_l C')\<close> and uL_M: \<open>-L \<in> lits_of_l (get_trail_l S)\<close>
    using valid SS' by (auto simp: WS'_def)
  have C'_i[simp]: \<open>C'!i = L\<close>
    using L two_le_length_C by (auto simp: take_2_if i_def split: if_splits)
  then have [simp]: \<open>?N\<propto>C!i = L\<close>
    by auto
  have C_neq_0[iff]: \<open>C \<noteq> 0\<close>
    using assms(3,5) unfolding twl_list_invs_def by (auto dest!: multi_member_split)
  then have C_0: \<open>C > 0\<close>
    by linarith
  have pre_inv: \<open>unit_propagation_inner_loop_body_l_inv L C ?S\<close>
    unfolding unit_propagation_inner_loop_body_l_inv_def
  proof (rule exI[of _ S'], intro conjI)
    have S_readd_C_S: \<open>set_clauses_to_update_l (clauses_to_update_l ?S + {#C#}) ?S = S\<close>
      using WS by (cases S) auto
    show \<open>(set_clauses_to_update_l
      (clauses_to_update_l ?S + {#C#})
      (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S),
     S') \<in> twl_st_l (Some L)\<close>
      using SS' unfolding S_readd_C_S .
    show \<open>twl_stgy_invs S'\<close> \<open>twl_struct_invs S'\<close>
      using assms by fast+
    show \<open>C \<in># dom_m (get_clauses_l ?S)\<close>
      using assms C_N_U by auto
    show \<open>C > 0\<close>
      by (rule C_0)
    show \<open>(if get_clauses_l ?S \<propto> C ! 0 = L then 0 else 1) < length (get_clauses_l ?S \<propto> C)\<close>
      using two_le_length_C by auto
    show \<open>1 - (if get_clauses_l ?S \<propto> C ! 0 = L then 0 else 1) < length (get_clauses_l ?S \<propto> C)\<close>
      using two_le_length_C by auto
    show \<open>length (get_clauses_l ?S \<propto> C) > 0\<close>
      using two_le_length_C by auto
    show \<open>no_dup (get_trail_l ?S)\<close>
      using n_d by auto
    show \<open>L \<in> set (watched_l (get_clauses_l ?S \<propto> C))\<close>
      using L by auto
    show \<open>get_conflict_l ?S = None\<close>
      using confl SS' WS by (cases \<open>get_conflict_l S\<close>) (auto dest: in_diffD)
  qed

  define pol_spec where
    \<open>pol_spec bL' = {(b, b'). (b = None \<longrightarrow> \<not>b') \<and> (b = Some True \<longleftrightarrow> b') \<and>
      (b' \<longleftrightarrow> bL'
          \<in> lits_of_l
           (get_trail
            (set_clauses_to_update
             (remove1_mset (L, twl_clause_of C')
              (clauses_to_update S'))
             S'))) \<and>
      (b = Some False \<longleftrightarrow> -bL'
          \<in> lits_of_l
           (get_trail
            (set_clauses_to_update
             (remove1_mset (L, twl_clause_of C')
              (clauses_to_update S'))
             S')))}\<close> for bL'

  have [refine]: \<open>mop_polarity_l
     (set_clauses_to_update_l
       (remove1_mset C (clauses_to_update_l S)) S)
     K
    \<le>  \<Down>(pol_spec L')
        (mop_lit_is_pos L'
          (set_clauses_to_update
            (remove1_mset (L, twl_clause_of C')
              (clauses_to_update S'))
            S'))\<close>
    if \<open>(K,L') \<in> Id\<close> for K L'
    using that SS' unfolding mop_polarity_l_def mop_lit_is_pos_def
    by refine_rcg
      (auto simp: polarity_def mop_polarity_l_def twl_st mset_take_mset_drop_mset'
        Decided_Propagated_in_iff_in_lits_of_l pol_spec_def dest: no_dup_consistentD
      intro!: ASSERT_leI)

  let ?S = \<open>set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S\<close>
  obtain M N D NE UE NS US WS Q where S: \<open>S = (M, N, D, NE, UE, NS, US, WS, Q)\<close>
    by (cases S) auto

  have C_N_U: \<open>C \<in># dom_m (get_clauses_l S)\<close>
    using add_inv WS SS' by (auto simp: twl_list_invs_def)
  let ?M = \<open>get_trail_l S\<close>
  let ?N = \<open>get_clauses_l S\<close>
  let ?WS = \<open>clauses_to_update_l S\<close>
  let ?Q = \<open>literals_to_update_l S\<close>

  define i :: nat where \<open>i \<equiv> (if get_clauses_l S\<propto>C!0 = L then 0 else 1)\<close>
  let ?L = \<open>C' ! i\<close>
  let ?L' = \<open>C' ! (Suc 0 - i)\<close>
  have inv: \<open>twl_st_inv S'\<close> and
    cdcl_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S')\<close> and
    valid: \<open>valid_enqueued S'\<close>
    using struct_invs WS by (auto simp: twl_struct_invs_def pcdcl_all_struct_invs_def)
  have
    w_q_inv: \<open>clauses_to_update_inv S'\<close> and
    dist: \<open>distinct_queued S'\<close> and
    no_dup: \<open>no_duplicate_queued S'\<close> and
    confl: \<open>get_conflict S' \<noteq> None \<Longrightarrow> clauses_to_update S' = {#} \<and> literals_to_update S' = {#}\<close> and
    st_inv: \<open>twl_st_inv S'\<close>
    using struct_invs unfolding twl_struct_invs_def by fast+
  have dist_C: \<open>distinct (get_clauses_l S \<propto> C)\<close>
    using cdcl_inv SS' C_N_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_alt_def
    by (auto simp: ran_m_def dest!: multi_member_split)
  have n_d: \<open>no_dup ?M\<close> and confl_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of S')\<close>
    using cdcl_inv SS' unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: trail.simps comp_def twl_st)

  then have consistent: \<open>- L \<notin> lits_of_l ?M\<close> if \<open>L \<in> lits_of_l ?M\<close> for L
    using consistent_interp_def distinct_consistent_interp that by blast

  have cons_M: \<open>consistent_interp (lits_of_l ?M)\<close>
    using n_d distinct_consistent_interp by fast
  let ?C' = \<open>twl_clause_of C'\<close>
  have C'_N_U_or: \<open>?C' \<in># twl_clause_of `# (init_clss_lf ?N) \<or>
      ?C' \<in># twl_clause_of `# learned_clss_lf ?N\<close>
    using WS valid SS'
    unfolding union_iff[symmetric] image_mset_union[symmetric]  mset_append[symmetric]
    by (auto simp: twl_struct_invs_def
        split: prod.splits simp del: twl_clause_of.simps)
  have struct: \<open>struct_wf_twl_cls ?C'\<close>
    using C_N_U inv SS' WS valid unfolding valid_enqueued_alt_simps
    by (auto simp: twl_st_inv_alt_def Ball_ran_m_dom_struct_wf
      simp del: twl_clause_of.simps)
  have C'_N_U: \<open>?C' \<in># twl_clause_of `# all_clss_lf ?N\<close>
    using C'_N_U_or
    unfolding union_iff[symmetric] image_mset_union[symmetric]  mset_append[symmetric] .
  have watched_C': \<open>mset (watched_l C') = {#?L, ?L'#}\<close>
    using struct i_def SS' by (cases C) (auto simp: length_list_2 take_2_if)
  then have mset_watched_C: \<open>mset (watched_l C') = {#watched_l C' ! i, watched_l C' ! (Suc 0 - i)#}\<close>
    using i_def by (cases \<open>twl_clause_of (get_clauses_l S \<propto> C)\<close>) (auto simp: take_2_if)
  have two_le_length_C: \<open>2 \<le> length C'\<close>
    by (metis length_take linorder_not_le min_less_iff_conj numeral_2_eq_2 order_less_irrefl
    size_add_mset size_eq_0_iff_empty size_mset watched_C')
  then have i_le_length_C: \<open>i < length C'\<close>
    by (auto simp: i_def)
  obtain WS' where WS'_def: \<open>?WS = add_mset C WS'\<close>
    using multi_member_split[OF WS] by auto
  then have WS'_def': \<open>WS = add_mset C WS'\<close>
    unfolding S by auto
  have L: \<open>L \<in> set (watched_l C')\<close> and uL_M: \<open>-L \<in> lits_of_l (get_trail_l S)\<close>
    using valid SS' by (auto simp: WS'_def)
  have C'_i[simp]: \<open>C'!i = L\<close>
    using L two_le_length_C by (auto simp: take_2_if i_def split: if_splits)
  then have [simp]: \<open>?N\<propto>C!i = L\<close>
    by auto

  have i_def': \<open>i = (if get_clauses_l ?S \<propto> C ! 0 = L then 0 else 1)\<close>
    unfolding i_def by auto
  have \<open>twl_list_invs ?S\<close>
    using add_inv C_N_U unfolding twl_list_invs_def S
    by (auto dest: in_diffD)
  then have upd_rel: \<open>(?S,
     set_clauses_to_update (remove1_mset (L, twl_clause_of C') (clauses_to_update S')) S')
    \<in> {(S, S'). (S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S}\<close>
    using SS' WS
    by (auto simp: twl_st_l_def image_mset_remove1_mset_if)
  have D_None: \<open>get_conflict_l S = None\<close>
    using confl SS' by (cases \<open>get_conflict_l S\<close>) (auto simp: S WS'_def')
  have [simp]: \<open>twl_st_inv (set_conflicting C' (set_clauses_to_update
      (remove1_mset LC (clauses_to_update S')) S'))\<close>
    if \<open>twl_st_inv S'\<close> for S' C' LC
    using that
     by (cases S') (auto simp: twl_st_inv.simps set_conflicting_def)

  have pre: \<open>set_conflict_l_pre C (M, N, None, NE, UE, NS, US, remove1_mset C WS, Q)\<close>
    if \<open>M \<Turnstile>as CNot (mset (N \<propto> C))\<close>
     using pre_inv C_N_U dist_C that
     unfolding set_conflict_l_pre_def unit_propagation_inner_loop_body_l_inv_def apply -
     apply normalize_goal+
     apply (intro conjI)
     apply (auto simp: S true_annots_true_cls dest: consistent_CNot_not_tautology distinct_consistent_interp)[5]
     apply (rule_tac x=x in exI, rule_tac x = \<open>Some L\<close> in exI)
     apply (simp add: S)
     done
  have \<open>set_conflict_l C ?S \<le> SPEC twl_list_invs\<close> if \<open>M \<Turnstile>as CNot (mset (N \<propto> C))\<close>
    using add_inv C_N_U D_None pre that unfolding twl_list_invs_def
    by (auto dest: in_diffD simp: set_conflicting_def S
      set_conflict_l_def mset_take_mset_drop_mset' intro!: ASSERT_leI)
  then have confl_rel: \<open>set_conflict_l C ?S \<le>
     \<Down> {(S, S').
          (S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S}
        (mop_set_conflicting (twl_clause_of C')
          (set_clauses_to_update
            (remove1_mset (L, twl_clause_of C')
              (clauses_to_update S'))
            S'))\<close>
    using SS' WS D_None C_N_U pre
    by (auto simp: twl_st_l_def image_mset_remove1_mset_if set_conflicting_def S Let_def
      set_conflict_l_def mset_take_mset_drop_mset' mop_set_conflicting_def set_conflict_pre_def
      intro!: ASSERT_leI ASSERT_refine_right)

  have propa_rel:
    \<open>propagate_lit_l K C j
     (set_clauses_to_update_l
       (remove1_mset C (clauses_to_update_l S)) S)
    \<le> \<Down> {(S, S').
          (S, S') \<in> twl_st_l (Some L) \<and>
          twl_list_invs S}
        (mop_propagate_lit L' (twl_clause_of C')
          (set_clauses_to_update
            (remove1_mset (L, twl_clause_of C')
              (clauses_to_update S'))
            S'))\<close>
    if
      \<open>(K, L') \<in> Id\<close> and  \<open>L' \<in> {K. K \<in># remove1_mset L {#L, L'a#}}\<close> and
      \<open>watched (twl_clause_of C') = {#L, L'a#}\<close>
     \<open>(j, j') \<in> {(j, j'). j = i \<and> i < 2}\<close>
    for L' K L'a j j'
    unfolding S clauses_to_update_l.simps set_clauses_to_update_l.simps
      propagate_lit_l_def mop_propagate_lit_def prod.case
  proof refine_rcg
    assume \<open>propagate_lit_pre L' (twl_clause_of C')
     (set_clauses_to_update
       (remove1_mset (L, twl_clause_of C') (clauses_to_update S'))
       S')\<close>
    then have L'_undef: \<open>- L' \<notin> lits_of_l
       (get_trail
         (set_clauses_to_update
           (remove1_mset (L, twl_clause_of C') (clauses_to_update S')) S')) \<close>
        \<open>L' \<notin> lits_of_l
           (get_trail
             (set_clauses_to_update
               (remove1_mset (L, twl_clause_of C') (clauses_to_update S'))
               S'))\<close>
      unfolding propagate_lit_pre_def Let_def
      by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
    show \<open>C \<in># dom_m N\<close>
      using C_N_U by (auto simp: S)

    have [simp]: \<open>L' = L'a\<close> \<open>K = L'\<close> \<open>L'a = (N \<propto> C ! (Suc 0 - i))\<close> \<open>j = i\<close>
      using that two_le_length_C unfolding i_def
      by (auto simp: take_2_if S add_mset_eq_add_mset split: if_splits)
    have [simp]: \<open>mset (swap (N \<propto> C) 0 (Suc 0 - i)) = mset (N \<propto> C)\<close>
      apply (subst swap_multiset)
      using two_le_length_C unfolding i_def
      by (auto simp: S)
    have mset_un_watched_swap:
        \<open>mset (watched_l (swap (N \<propto> C) 0 (Suc 0 - i))) = mset (watched_l (N \<propto> C))\<close>
        \<open>mset (unwatched_l (swap (N \<propto> C) 0 (Suc 0 - i))) = mset (unwatched_l (N \<propto> C))\<close>
      using two_le_length_C unfolding i_def
      apply (auto simp: S take_2_if)
      by (auto simp: S swap_def)
    have irred_init: \<open>irred N C \<Longrightarrow> (N \<propto> C, True) \<in># init_clss_l N\<close>
      using C_N_U by (auto simp: S ran_def)
    have init_unchanged: \<open>{#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
    . x \<in># init_clss_l (N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i)))#} =
    {#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
    . x \<in># init_clss_l N#}\<close>
      using C_N_U
      by (cases \<open>irred N C\<close>) (auto simp: init_clss_l_mapsto_upd S image_mset_remove1_mset_if
        mset_un_watched_swap init_clss_l_mapsto_upd_irrel
        dest: multi_member_split[OF irred_init])


    have irred_init: \<open>\<not>irred N C \<Longrightarrow> (N \<propto> C, False) \<in># learned_clss_l N\<close>
      using C_N_U by (auto simp: S ran_def)
    have learned_unchanged: \<open>{#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
    . x \<in># learned_clss_l (N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i)))#} =
     {#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
    . x \<in># learned_clss_l N#}\<close>
      using C_N_U
      by (cases \<open>irred N C\<close>) (auto simp: init_clss_l_mapsto_upd S image_mset_remove1_mset_if
        mset_un_watched_swap learned_clss_l_mapsto_upd
        learned_clss_l_mapsto_upd_irrel
        dest: multi_member_split[OF irred_init])
    have [simp]: \<open>{#(L, TWL_Clause (mset (watched_l
                    (fst (the (if C = x
                               then Some (swap (N \<propto> C) 0 (Suc 0 - i), irred N C)
                               else fmlookup N x)))))
            (mset (unwatched_l
                    (fst (the (if C = x
                               then Some (swap (N \<propto> C) 0 (Suc 0 - i), irred N C)
                               else fmlookup N x))))))
     . x \<in># WS#} = {#(L, TWL_Clause (mset (watched_l (N \<propto> x))) (mset (unwatched_l (N \<propto> x))))
     . x \<in># WS#}\<close>
      by (rule image_mset_cong) (auto simp: mset_un_watched_swap)
    have C'_0i: \<open>C' ! (Suc 0 - i) \<in> set (watched_l C')\<close>
      using two_le_length_C by (auto simp: take_2_if S i_def)
      (* WTF *)
    have nth_swap_isabelle: \<open>length a \<ge> 2 \<Longrightarrow> swap a 0 (Suc 0 - i) ! 0 = a ! (Suc 0 - i)\<close>
      for a :: \<open>'a list\<close>
      using two_le_length_C that apply (auto simp: swap_def S i_def)
      by (metis (full_types) le0 neq0_conv not_less_eq_eq nth_list_update_eq numeral_2_eq_2)
    have [simp]: \<open>Propagated La C \<notin> set M\<close> for La
    proof (rule ccontr)
      assume H:\<open>\<not> ?thesis\<close>
      then have \<open>La \<in> set (watched_l (N \<propto> C))\<close> and
        \<open>2 < length (N \<propto> C) \<longrightarrow> La = N \<propto> C ! 0\<close>
        using add_inv C_N_U two_le_length_C mset_un_watched_swap C'_0i
        unfolding twl_list_invs_def S by auto
      moreover have \<open>La \<in> lits_of_l M\<close>
        using H by (force simp: lits_of_def)
      ultimately show False
        using L'_undef that SS' uL_M n_d C'_i S watched_C' two_le_length_C
        apply (auto simp: S i_def dest: no_dup_consistentD split: if_splits)
	      apply (metis in_multiset_nempty member_add_mset no_dup_consistentD  set_mset_mset)
	      by (metis (mono_tags) in_multiset_nempty member_add_mset no_dup_consistentD set_mset_mset)
    qed
    have \<open>twl_list_invs
     (Propagated (N \<propto> C ! (Suc 0 - i)) C # M, N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i)),
      D, NE, UE, NS, US, remove1_mset C WS, add_mset (- N \<propto> C ! (Suc 0 - i)) Q)\<close>
      using add_inv C_N_U two_le_length_C mset_un_watched_swap C'_0i
      unfolding twl_list_invs_def
      by (auto dest: in_diffD simp: set_conflicting_def
      set_conflict_l_def mset_take_mset_drop_mset' S nth_swap_isabelle
      dest!: mset_eq_setD)
    moreover have
      \<open>convert_lit (N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i))) (NE + UE)
         (Propagated (N \<propto> C ! (Suc 0 - i)) C)
         (Propagated (N \<propto> C ! (Suc 0 - i)) (mset (N \<propto> C)))\<close>
      by (auto simp: convert_lit.simps C_0)
    moreover have \<open>(M, x) \<in> convert_lits_l N (NE + UE) \<Longrightarrow>
        (M, x) \<in> convert_lits_l (N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i))) (NE + UE)\<close> for x
       apply (rule convert_lits_l_extend_mono)
       apply assumption
       apply auto
       done
    moreover have
      \<open>convert_lit N (NE + UE)
         (Propagated (N \<propto> C ! (Suc 0 - i)) C)
         (Propagated (N \<propto> C ! (Suc 0 - i)) (mset (N \<propto> C)))\<close>
      using C_N_U by (auto simp: S convert_lit.simps C_0)
    moreover have \<open>twl_list_invs
         (Propagated (N \<propto> C ! (Suc 0 - i)) C # M, N, D, NE, UE,
          NS, US, remove1_mset C WS, add_mset (- N \<propto> C ! (Suc 0 - i)) Q)\<close>
      if \<open>\<not> 2 < length (N \<propto> C)\<close>
      using add_inv C_N_U two_le_length_C mset_un_watched_swap C'_0i that
      unfolding twl_list_invs_def
      by (auto dest: in_diffD simp: set_conflicting_def
      set_conflict_l_def mset_take_mset_drop_mset' S nth_swap_isabelle
      dest!: mset_eq_setD)
    moreover have \<open>swap (N \<propto> C) 0 (Suc 0) = swap (N \<propto> C) i (1 -i)\<close>
       using i_def two_le_length_C by (cases \<open>N \<propto> C\<close>)(auto simp: swap_def)
    moreover have \<open>i < length (N \<propto> C)\<close> \<open>i \<le> 1\<close>
       using i_def two_le_length_C by (auto simp: S)
    moreover have \<open>undefined_lit M L'\<close>
      using L'_undef SS' by (auto simp: S Decided_Propagated_in_iff_in_lits_of_l)
    moreover have \<open>N \<propto> C ! (Suc 0 - i)
                   \<in># all_lits_of_mm
                       ({#mset (fst x). x \<in># ran_m N#} + (NE + UE) + (NS + US))\<close>
     using C_N_U two_le_length_C by (auto simp: S ran_m_def all_lits_of_mm_add_mset i_def
       intro!: in_clause_in_all_lits_of_m nth_mem dest!: multi_member_split)
   moreover have \<open>add_mset L (add_mset (N \<propto> C ! (Suc 0 - i)) (mset (unwatched_l (N \<propto> C)))) =
       mset (N \<propto> C)\<close>
     apply (subst (4) append_take_drop_id[of 2, symmetric])
     using that unfolding mset_append
     by (auto simp: S)
    ultimately show
       \<open>K \<in># all_lits_of_mm (get_all_clss_l (M, N, D, NE, UE, NS, US, remove1_mset C WS, Q))\<close>
       \<open>j \<le> 1\<close>
       \<open>do {
               M \<leftarrow> cons_trail_propagate_l K C M;
               N \<leftarrow> if 2 < length (N \<propto> C)
                   then mop_clauses_swap N C 0 (Suc 0 - j) else RETURN N;
               RETURN
                (M, N, D, NE, UE, NS, US, remove1_mset C WS,
                 add_mset (- K) Q)
             } \<le> SPEC(\<lambda>C.
                  (C,
                    (propagate_lit L' (twl_clause_of C')
                      (set_clauses_to_update
                        (remove1_mset (L, twl_clause_of C')
                          (clauses_to_update S'))
                        S'))) \<in> {(S, S').
                     (S, S') \<in> twl_st_l (Some L) \<and>
                     twl_list_invs S})\<close>
      using SS' WS C_N_U that unfolding propagate_lit_l_def apply (auto simp: S)
      by (auto simp: twl_st_l_def image_mset_remove1_mset_if propagate_lit_def
           propagate_lit_l_def mset_take_mset_drop_mset' S learned_unchanged mop_clauses_swap_def
           cons_trail_propagate_l_def mop_propagate_lit_def
        init_unchanged mset_un_watched_swap intro: convert_lit.intros
        intro!: ASSERT_leI ASSERT_refine_right)
  qed
  have update_clause_rel: \<open>do {
      K' \<leftarrow> mop_clauses_at
           (get_clauses_l
             (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S))
               S))
           C (the K);
     val_K \<leftarrow> mop_polarity_l
        (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S) K';
     (if val_K = Some True
     then RETURN (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S)
     else update_clause_l C j (the K) (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S))}
    \<le> \<Down> {(S, S'). (S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S}
        (update_clauseS L (twl_clause_of C')
          (set_clauses_to_update (remove1_mset (L, twl_clause_of C') (clauses_to_update S')) S'))\<close>
    (is \<open>?update_clss \<le> \<Down> _ _\<close>)
  if
    L': \<open>L' \<in> {K. K \<in># clause (twl_clause_of C')}\<close> and
    K: \<open>K \<in> {found. (found = None) =
          (\<forall>L\<in>set (unwatched_l (get_clauses_l ?S \<propto> C)).
              - L \<in> lits_of_l (get_trail_l ?S)) \<and>
          (\<forall>j. found = Some j \<longrightarrow>
               j < length (get_clauses_l ?S \<propto> C) \<and>
               (undefined_lit (get_trail_l ?S) (get_clauses_l ?S \<propto> C ! j) \<or>
                get_clauses_l ?S \<propto> C ! j \<in> lits_of_l (get_trail_l ?S)) \<and>
               2 \<le> j)}\<close> and
    K_None: \<open>K \<noteq> None\<close> and
    \<open>watched (twl_clause_of C') = {#L, L'a#}\<close> and
    val: \<open>(val_L', False) \<in> pol_spec L'a\<close> and
    \<open>(j, j') \<in> {(j, j'). j = i \<and> i < 2}\<close>
    for L' and K and L'a and j j' and val_L'
  proof -
    have  L'a: \<open>L'a
      \<notin> lits_of_l
       (get_trail
         (set_clauses_to_update
           (remove1_mset (L, twl_clause_of C') (clauses_to_update S')) S'))\<close>
      using n_d val SS' by (auto simp: pol_spec_def dest: no_dup_consistentD)
    have [simp]: \<open>j = i\<close>
      using that by auto
    obtain K' where [simp]: \<open>K = Some K'\<close>
      using K_None by auto
    have
      K'_le: \<open>K' < length (N \<propto> C)\<close> and
      K'_2: \<open>2 \<le> K'\<close> and
      K'_M: \<open>undefined_lit M (N \<propto> C ! K') \<or>
         N \<propto> C ! K' \<in> lits_of_l (get_trail_l S) \<close>
      using K by (auto simp: S)
    have [simp]: \<open>N \<propto> C ! K' \<in> set (unwatched_l (N \<propto> C))\<close>
      using K'_le K'_2 by (auto simp: set_drop_conv S)
    have [simp]: \<open>- N \<propto> C ! K' \<notin> lits_of_l M \<close>
      using n_d K'_M by (auto simp: S Decided_Propagated_in_iff_in_lits_of_l
        dest: no_dup_consistentD)

    have irred_init: \<open>irred N C \<Longrightarrow> (N \<propto> C, True) \<in># init_clss_l N\<close>
      using C_N_U by (auto simp: S)
    have init_unchanged: \<open>update_clauses
     ({#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
      . x \<in># init_clss_l N#},
      {#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
      . x \<in># learned_clss_l N#})
     (TWL_Clause (mset (watched_l (N \<propto> C))) (mset (unwatched_l (N \<propto> C)))) L
     (N \<propto> C ! K')
     ({#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
      . x \<in># init_clss_l (N(C \<hookrightarrow> swap (N \<propto> C) i K'))#},
      {#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
      . x \<in># learned_clss_l (N(C \<hookrightarrow> swap (N \<propto> C) i K'))#})\<close>
    proof (cases \<open>irred N C\<close>)
      case J_NE: True
      have L_L'_UW_N: \<open>C' \<in># init_clss_lf N\<close>
        using C_N_U J_NE unfolding take_set
        by (auto simp: S ran_m_def)

      let ?UW = \<open>unwatched_l C'\<close>
      have TWL_L_L'_UW_N: \<open>TWL_Clause {#?L, ?L'#} (mset ?UW) \<in># twl_clause_of `# init_clss_lf N\<close>
        using imageI[OF L_L'_UW_N, of twl_clause_of] watched_C' by force
      let ?k' = \<open>the K - 2\<close>
      have \<open>?k' < length (unwatched_l C')\<close>
        using K'_le two_le_length_C K'_2 by (auto simp: S)
      then have H0: \<open>TWL_Clause {#?UW ! ?k', ?L'#} (mset (list_update ?UW ?k' ?L)) =
        update_clause (TWL_Clause {#?L, ?L'#} (mset ?UW)) ?L (?UW ! ?k')\<close>
         by (auto simp: mset_update)

      have H3: \<open>{#L, C' ! (Suc 0 - i)#} = mset (watched_l (N \<propto> C))\<close>
        using K'_2 K'_le \<open>C > 0\<close> C'_i by (auto simp: S take_2_if C_N_U nth_tl i_def)
      have H4: \<open>mset (unwatched_l C') = mset (unwatched_l (N \<propto> C))\<close>
        by (auto simp: S take_2_if C_N_U nth_tl)

      let ?New_C = \<open>(TWL_Clause {#L, C' ! (Suc 0 - i)#} (mset (unwatched_l C')))\<close>

      have wo: "a = a' \<Longrightarrow> b = b' \<Longrightarrow> L = L'  \<Longrightarrow>  K = K'  \<Longrightarrow> c = c' \<Longrightarrow>
         update_clauses a K L b c \<Longrightarrow>
         update_clauses a' K' L' b' c'" for a a' b b' K L K' L' c c'
        by auto
      have [simp]: \<open>C' \<in> fst ` {a. a \<in># ran_m N \<and> snd a}  \<longleftrightarrow> irred N C\<close>
        using C_N_U J_NE unfolding C' S ran_m_def
        by auto
      have C'_ran_N: \<open>(C', True) \<in># ran_m N\<close>
        using C_N_U J_NE unfolding C' S S
        by auto
      have upd: \<open>update_clauses
          (twl_clause_of `# init_clss_lf N, twl_clause_of `# learned_clss_lf N)
          (TWL_Clause {#C' ! i, C' ! (Suc 0 - i)#} (mset (unwatched_l C'))) (C' ! i) (C' ! the K)
             (add_mset (update_clause (TWL_Clause {#C' ! i, C' ! (Suc 0 - i)#}
                (mset (unwatched_l C'))) (C' ! i) (C' ! the K))
               (remove1_mset
                 (TWL_Clause {#C' ! i, C' ! (Suc 0 - i)#} (mset (unwatched_l C')))
                 (twl_clause_of `# init_clss_lf N)), twl_clause_of `# learned_clss_lf N)\<close>
        by (rule update_clauses.intros(1)[OF TWL_L_L'_UW_N])
      have K1: \<open>mset (watched_l (swap (N\<propto>C) i K')) = {#N\<propto>C!K', N\<propto>C!(1 - i)#}\<close>
        using J_NE C_N_U C' K'_2 K'_le two_le_length_C
          by (auto simp: init_clss_l_mapsto_upd S image_mset_remove1_mset_if
            take_2_if swap_def i_def)
      have K2: \<open>mset (unwatched_l (swap (N\<propto>C) i K')) = add_mset (N\<propto>C ! i)
                   (remove1_mset (N\<propto>C ! K') (mset (unwatched_l (N\<propto>C))))\<close>
        using J_NE C_N_U C' K'_2 K'_le two_le_length_C
        by (auto simp: init_clss_l_mapsto_upd S image_mset_remove1_mset_if mset_update
            take_2_if swap_def i_def drop_upd_irrelevant drop_Suc drop_update_swap)
      have K3: \<open>mset (watched_l (N\<propto>C)) = {#N\<propto>C!i, N\<propto>C!(1 - i)#}\<close>
        using J_NE C_N_U C' K'_2 K'_le two_le_length_C
          by (auto simp: init_clss_l_mapsto_upd S image_mset_remove1_mset_if
            take_2_if swap_def i_def)

      show ?thesis
        apply (rule wo[OF _ _ _ _ _ upd])
        subgoal by auto
        subgoal by (auto simp: S)
        subgoal by auto
        subgoal unfolding S H3[symmetric] H4[symmetric] by auto
        subgoal
        using J_NE C_N_U C' K'_2 K'_le two_le_length_C K1 K2 K3 C'_ran_N
          by (auto simp: init_clss_l_mapsto_upd S image_mset_remove1_mset_if
            learned_clss_l_mapsto_upd_irrel)
        done
    next
      assume J_NE: \<open>\<not>irred N C\<close>
      have L_L'_UW_N: \<open>C' \<in># learned_clss_lf N\<close>
        using C_N_U J_NE unfolding take_set
        by (auto simp: S ran_m_def)

      let ?UW = \<open>unwatched_l C'\<close>
      have TWL_L_L'_UW_N: \<open>TWL_Clause {#?L, ?L'#} (mset ?UW) \<in># twl_clause_of `# learned_clss_lf N\<close>
        using imageI[OF L_L'_UW_N, of twl_clause_of] watched_C' by force
      let ?k' = \<open>the K - 2\<close>
      have \<open>?k' < length (unwatched_l C')\<close>
        using K'_le two_le_length_C K'_2 by (auto simp: S)
      then have H0: \<open>TWL_Clause {#?UW ! ?k', ?L'#} (mset (list_update ?UW ?k' ?L)) =
        update_clause (TWL_Clause {#?L, ?L'#} (mset ?UW)) ?L (?UW ! ?k')\<close>
         by (auto simp: mset_update)

      have H3:  \<open>{#L, C' ! (Suc 0 - i)#} = mset (watched_l (N \<propto> C))\<close>
        using K'_2 K'_le \<open>C > 0\<close> C'_i by (auto simp: S take_2_if C_N_U nth_tl i_def)
      have H4: \<open>mset (unwatched_l C') = mset (unwatched_l (N \<propto> C))\<close>
        by (auto simp: S take_2_if C_N_U nth_tl)

      let ?New_C = \<open>(TWL_Clause {#L, C' ! (Suc 0 - i)#} (mset (unwatched_l C')))\<close>

      have wo: "a = a' \<Longrightarrow> b = b' \<Longrightarrow> L = L'  \<Longrightarrow>  K = K'  \<Longrightarrow> c = c' \<Longrightarrow>
        update_clauses a K L b c \<Longrightarrow>
        update_clauses a' K' L' b' c'" for a a' b b' K L K' L' c c'
        by auto
      have [simp]: \<open>C' \<in> fst ` {a. a \<in># ran_m N \<and> \<not>snd a}  \<longleftrightarrow> \<not>irred N C\<close>
        using C_N_U J_NE unfolding C' S ran_m_def
        by auto
      have C'_ran_N: \<open>(C', False) \<in># ran_m N\<close>
        using C_N_U J_NE unfolding C' S S
        by auto
      have upd: \<open>update_clauses
        (twl_clause_of `# init_clss_lf N, twl_clause_of `# learned_clss_lf N)
        (TWL_Clause {#C' ! i, C' ! (Suc 0 - i)#} (mset (unwatched_l C'))) (C' ! i)
        (C' ! the K)
        (twl_clause_of `# init_clss_lf N,
        add_mset
          (update_clause
            (TWL_Clause {#C' ! i, C' ! (Suc 0 - i)#} (mset (unwatched_l C'))) (C' ! i)
            (C' ! the K))
          (remove1_mset
            (TWL_Clause {#C' ! i, C' ! (Suc 0 - i)#} (mset (unwatched_l C')))
            (twl_clause_of `# learned_clss_lf N)))
        \<close>
        by (rule update_clauses.intros(2)[OF TWL_L_L'_UW_N])
      have K1: \<open>mset (watched_l (swap (N\<propto>C) i K')) = {#N\<propto>C!K', N\<propto>C!(1 - i)#}\<close>
        using J_NE C_N_U C' K'_2 K'_le two_le_length_C
          by (auto simp: init_clss_l_mapsto_upd S image_mset_remove1_mset_if
            take_2_if swap_def i_def)
      have K2: \<open>mset (unwatched_l (swap (N\<propto>C) i K')) = add_mset (N\<propto>C ! i)
                   (remove1_mset (N\<propto>C ! K') (mset (unwatched_l (N\<propto>C))))\<close>
        using J_NE C_N_U C' K'_2 K'_le two_le_length_C
        by (auto simp: init_clss_l_mapsto_upd S image_mset_remove1_mset_if mset_update
            take_2_if swap_def i_def drop_upd_irrelevant drop_Suc drop_update_swap)
      have K3: \<open>mset (watched_l (N\<propto>C)) = {#N\<propto>C!i, N\<propto>C!(1 - i)#}\<close>
        using J_NE C_N_U C' K'_2 K'_le two_le_length_C
          by (auto simp: init_clss_l_mapsto_upd S image_mset_remove1_mset_if
            take_2_if swap_def i_def)

      show ?thesis
        apply (rule wo[OF _ _ _ _ _ upd])
        subgoal by auto
        subgoal by (auto simp: S)
        subgoal by auto
        subgoal unfolding S H3[symmetric] H4[symmetric] by auto
        subgoal
        using J_NE C_N_U C' K'_2 K'_le two_le_length_C K1 K2 K3 C'_ran_N
          by (auto simp: learned_clss_l_mapsto_upd S image_mset_remove1_mset_if
            init_clss_l_mapsto_upd_irrel)
        done
    qed
    have \<open>distinct_mset WS\<close>
      by (metis (full_types) WS'_def WS'_def' add_inv twl_list_invs_def)
    then have [simp]: \<open>C \<notin># WS'\<close>
       by (auto simp: WS'_def')
    have H: \<open>{#(L, TWL_Clause
           (mset (watched_l
                   (fst (the (if C = x then Some (swap (N \<propto> C) i K', irred N C)
                              else fmlookup N x)))))
           (mset (unwatched_l
                   (fst (the (if C = x then Some (swap (N \<propto> C) i K', irred N C)
                              else fmlookup N x)))))). x \<in># WS'#} =
     {#(L, TWL_Clause (mset (watched_l (N \<propto> x))) (mset (unwatched_l (N \<propto> x)))). x \<in># WS'#}\<close>
      by (rule image_mset_cong) auto
    have [simp]: \<open>Propagated La C \<notin> set M\<close> for La
    proof (rule ccontr)
      assume H:\<open>\<not> ?thesis\<close>
      then have \<open>length (N \<propto> C) > 2 \<Longrightarrow> La = N \<propto> C ! 0\<close> and
        \<open>La \<in> set (watched_l (N \<propto> C))\<close>
        using add_inv C_N_U two_le_length_C
        unfolding twl_list_invs_def S by auto
      moreover have \<open>La \<in> lits_of_l M\<close>
        using H by (force simp: lits_of_def)
      ultimately show False
        using SS' uL_M n_d K'_2 K'_le two_le_length_C arg_cong[OF that(4), of set_mset] L'a
        by (auto simp: S i_def polarity_spec' dest: no_dup_consistentD split: if_splits)
    qed
    have A: \<open>?update_clss = do {x \<leftarrow> mop_clauses_at N C K';
         if x \<in> lits_of_l (get_trail_l (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S))
        then RETURN (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S)
        else update_clause_l C i
              (the K) (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S)}\<close>
      using C_N_U K'_le n_d unfolding i_def
      by (auto simp add: S i_def polarity_def mop_clauses_at_def mop_polarity_l_def
            ran_m_def all_lits_of_mm_add_mset in_clause_in_all_lits_of_m dest!: multi_member_split[of C]
         dest: in_lits_of_l_defined_litD)

    have alt_defs: \<open>C' = N \<propto> C\<close>
      unfolding C' S by auto
    have list_invs_blit: \<open>twl_list_invs (M, N, D, NE, UE, NS, US, WS', Q)\<close>
      using add_inv C_N_U two_le_length_C
      unfolding twl_list_invs_def
      by (auto dest: in_diffD simp: S WS'_def')
    define pick_lit where
       \<open>pick_lit a = SPEC (\<lambda>L. L \<in># unwatched (twl_clause_of C') \<and> - L \<notin> lits_of_l a)\<close>
      for a  ::  \<open>('v, 'v clause) ann_lit list\<close>
    have [refine]:
      \<open>a = get_trail S' \<Longrightarrow> mop_clauses_at N C K' \<le> \<Down> {(L, L'). L = L' \<and> L' = op_clauses_at N C K'} (pick_lit a)\<close> for a
     using C_N_U K'_le K'_M n_d SS' unfolding C' S by (auto simp: mop_clauses_at_def twl_st_l_def pick_lit_def
       RETURN_RES_refine_iff S op_clauses_at_def)

    have \<open>twl_list_invs (M, N(C \<hookrightarrow> swap (N \<propto> C) i K'), D, NE, UE, NS, US, WS', Q)\<close>
      using add_inv C_N_U two_le_length_C
      unfolding twl_list_invs_def
      by (auto dest: in_diffD simp: set_conflicting_def
      set_conflict_l_def mset_take_mset_drop_mset' S WS'_def'
      dest!: mset_eq_setD)
    moreover have \<open>(M, x) \<in> convert_lits_l N (NE + UE) \<Longrightarrow>
        (M, x) \<in> convert_lits_l (N(C \<hookrightarrow> swap (N \<propto> C) i K')) (NE + UE)\<close> for x
      apply (rule convert_lits_l_extend_mono)
      by auto
    ultimately show ?thesis
      apply (cases S')
      unfolding update_clauseS_def unfolding pick_lit_def[symmetric]
      apply (clarsimp simp only: clauses_to_update.simps set_clauses_to_update.simps)
      apply (subst A)
      apply refine_vcg
      subgoal using C_N_U K'_le K'_M n_d SS' unfolding C' S by (auto simp: mop_clauses_at_def twl_st_l_def)
      subgoal using SS' K'_M unfolding C' S by (auto simp: twl_st_l_def)
      subgoal using SS' K'_M add_inv list_invs_blit unfolding C' S
        by (auto simp: twl_st_l_def WS'_def')
      subgoal for a b c d e f g h x Ka
        using SS' init_unchanged C_N_U i_le_length_C K'_le C'_i
        unfolding i_def[symmetric] get_clauses_l_set_clauses_to_update_l
        unfolding update_clause_l_pre_def
        by (auto simp: S update_clause_l_def update_clauseS_def twl_st_l_def WS'_def'
          RETURN_SPEC_refine RES_RES_RETURN_RES RETURN_def RES_RES2_RETURN_RES H
          mop_clauses_swap_def op_clauses_at_def WS'_def' update_clause_l_pre_def
            intro!: RES_refine exI[of _ \<open>N \<propto> C ! the K\<close>] ASSERT_leI
              exI[of _ \<open>set_clauses_to_update (remove1_mset (L, twl_clause_of (N \<propto> C))
                (clauses_to_update S')) S'\<close>] exI[of _ L] image_mset_cong)
      done
  qed


  have pos_of_watched: \<open>unit_propagation_inner_loop_body_l_inv L C
     (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S) \<Longrightarrow> pos_of_watched
        (get_clauses_l
          (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S))
        C L
       \<le> SPEC (\<lambda>c. (c, ()) \<in> {(j, j'). j = i \<and> i < 2})\<close>
    unfolding pos_of_watched_def
    by (auto simp: S unit_propagation_inner_loop_body_l_inv_def i_def
       intro!: ASSERT_leI)

  have [refine]: \<open>unit_propagation_inner_loop_body_l_inv L C
     (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S) \<Longrightarrow>
   (K, bL') \<in> Id \<Longrightarrow>
    bL' \<in> { K. K\<in># clause (twl_clause_of C')} \<Longrightarrow>
   mop_polarity_l
    (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S)
    K
    \<le> SPEC
     (\<lambda> c. (c, bL'
          \<in> lits_of_l
           (get_trail
            (set_clauses_to_update
             (remove1_mset (L, twl_clause_of C')
              (clauses_to_update S'))
             S')))
        \<in> pol_spec bL')\<close> for bL' K
     using assms n_d L C_N_U consistent unfolding pol_spec_def
     by (auto simp: mop_polarity_l_def polarity_def ran_m_def all_lits_of_mm_add_mset
         true_annot_iff_decided_or_true_lit dest!: in_set_takeD in_set_dropD
       dest!: multi_member_split[of C \<open>dom_m (get_clauses_l S)\<close>]
       intro!: ASSERT_leI intro!: in_clause_in_all_lits_of_m)

   have I: \<open>(x, ()) \<in> {_. True}\<close> for x
     by auto
   have L_i0: \<open>L = get_clauses_l S \<propto> C ! 0 \<Longrightarrow> Suc 0 - i = Suc 0\<close>
     by (auto simp: i_def)
   have other_watched_l: \<open>(i', ia) \<in> {(j, j'). j = i \<and> i < 2} \<Longrightarrow>
    other_watched_l
     (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S) L
     C i'
    \<le> SPEC (\<lambda>K. K \<in># remove1_mset L (watched (twl_clause_of C')))\<close> for i' ia
    unfolding other_watched_l_def
    by (refine_vcg mop_clauses_at[THEN fref_to_Down_curry2, unfolded comp_def, THEN order_trans])
     (use mset_watched_C pre_inv in \<open>auto simp: op_clauses_at_def C_N_U
            unit_propagation_inner_loop_body_l_inv_def L_i0
          intro!: ASSERT_leI split: if_splits
          intro!: mop_clauses_at[THEN fref_to_Down_curry2, unfolded comp_def, THEN order_trans]
          simp: other_watched_l_def\<close>)

   have H: \<open>?A \<le> \<Down> {(S, S'). (S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S} ?B\<close>
    unfolding unit_propagation_inner_loop_body_l_def unit_propagation_inner_loop_body_alt_def
      option.case_eq_if find_unwatched_l_def op_clauses_at_def[symmetric]
      nres_monad3
    apply (refine_vcg pos_of_watched
        case_prod_bind[of _ \<open>If _ _\<close>]; remove_dummy_vars)
    subgoal by (rule pre_inv)
    subgoal unfolding C' clause_twl_clause_of by auto
    subgoal using SS' by (auto simp: pol_spec_def)
    subgoal by (rule upd_rel)
    subgoal
      by (rule other_watched_l)
    subgoal for L'
      using assms by (auto simp: pol_spec_def)
    subgoal by (rule upd_rel)
    subgoal using SS' C_N_U by auto
    subgoal using SS' C_N_U two_le_length_C by auto
    subgoal using SS' C_N_U dist_C by auto
    subgoal using SS' C_N_U dist_C n_d by auto
    subgoal using SS' by auto
    subgoal using SS' by (auto simp: pol_spec_def)
    subgoal by (rule confl_rel)
    subgoal for K bL' j j' L' L'a2 L'a3 unfolding i_def[symmetric] op_clauses_at_def i_def'[symmetric]
      by (rule propa_rel)
    subgoal by auto
    subgoal for L' K unfolding i_def[symmetric]  i_def'[symmetric] op_clauses_at_def Let_def
      by (rule update_clause_rel)
    done
  have *: \<open>unit_propagation_inner_loop_body (C' ! i) (twl_clause_of C')
   (set_clauses_to_update (remove1_mset (C' ! i, twl_clause_of C') (clauses_to_update S')) S')
   \<le> SPEC (\<lambda>S''. twl_struct_invs S'' \<and>
                 twl_stgy_invs S'' \<and>
                 cdcl_twl_cp\<^sup>*\<^sup>* S' S'' \<and>
              (S'', S') \<in> measure (size \<circ> clauses_to_update))\<close>
    apply (rule unit_propagation_inner_loop_body(1)[of S' \<open>C' ! i\<close> \<open>twl_clause_of C'\<close>])
    using imageI[OF WS, of \<open>(\<lambda>j. (L, twl_clause_of (N \<propto> j)))\<close>]
      struct_invs stgy_inv C_N_U WS SS' D_None by auto
  have H': \<open>?B \<le> SPEC (\<lambda>S'. twl_stgy_invs S' \<and> twl_struct_invs S')\<close>
    using *
    by (simp add: weaken_SPEC)
  have \<open>?A
    \<le> \<Down> {(S, S'). ((S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S) \<and>
           (twl_stgy_invs S' \<and> twl_struct_invs S')}
         ?B\<close>
    apply (rule refine_add_invariants)
     apply (rule H')
    by (rule H)
  then show ?thesis by simp
qed

lemma unit_propagation_inner_loop_body_l2:
  assumes
    SS': \<open>(S, S') \<in> twl_st_l (Some L)\<close> and
    WS: \<open>C \<in># clauses_to_update_l S\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    add_inv: \<open>twl_list_invs S\<close> and
    stgy_inv: \<open>twl_stgy_invs S'\<close>
  shows
    \<open>(unit_propagation_inner_loop_body_l L C
        (set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S),
      unit_propagation_inner_loop_body L (twl_clause_of (get_clauses_l S \<propto> C))
        (set_clauses_to_update
          (remove1_mset (L, twl_clause_of (get_clauses_l S \<propto> C))
          (clauses_to_update S')) S'))
    \<in> \<langle>{(S, S'). (S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S \<and> twl_stgy_invs S' \<and>
         twl_struct_invs S'}\<rangle>nres_rel\<close>
  using unit_propagation_inner_loop_body_l[OF assms]
  by (auto simp: nres_rel_def)

text \<open>This a work around equality: it allows to instantiate variables that appear in goals by
  hand in a reasonable way (\<^text>\<open>rule\_tac I=x in EQI)\<close>.\<close>
definition EQ where
  [simp]: \<open>EQ = (=)\<close>

lemma EQI: "EQ I I"
  by auto

lemma unit_propagation_inner_loop_body_l_unit_propagation_inner_loop_body:
  \<open>EQ L'' L'' \<Longrightarrow>
    (uncurry2 unit_propagation_inner_loop_body_l, uncurry2 unit_propagation_inner_loop_body) \<in>
      {(((L, C), S0), ((L', C'), S0')). \<exists>S S'. L = L' \<and> C' = (twl_clause_of (get_clauses_l S \<propto> C)) \<and>
        S0 = (set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S) \<and>
        S0' = (set_clauses_to_update
          (remove1_mset (L, twl_clause_of (get_clauses_l S \<propto> C))
          (clauses_to_update S')) S') \<and>
       (S, S') \<in> twl_st_l (Some L) \<and> L = L'' \<and>
       C \<in># clauses_to_update_l S \<and> twl_struct_invs S' \<and> twl_list_invs S \<and> twl_stgy_invs S'} \<rightarrow>\<^sub>f
      \<langle>{(S, S'). (S, S') \<in> twl_st_l (Some L'') \<and> twl_list_invs S \<and> twl_stgy_invs S' \<and>
         twl_struct_invs S'}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using unit_propagation_inner_loop_body_l
  by fastforce

definition select_from_clauses_to_update :: \<open>'v twl_st_l \<Rightarrow> ('v twl_st_l \<times> nat) nres\<close> where
  \<open>select_from_clauses_to_update S = SPEC (\<lambda>(S', C). C \<in># clauses_to_update_l S \<and>
     S' = set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S)\<close>

definition unit_propagation_inner_loop_l_inv where
  \<open>unit_propagation_inner_loop_l_inv L = (\<lambda>(S, n).
    (\<exists>S'. (S, S') \<in> twl_st_l (Some L) \<and> twl_struct_invs S' \<and> twl_stgy_invs S' \<and>
      twl_list_invs S \<and> (clauses_to_update S' \<noteq> {#} \<or> n > 0 \<longrightarrow> get_conflict S' = None) \<and>
      -L \<in> lits_of_l (get_trail_l S)))\<close>

definition unit_propagation_inner_loop_body_l_with_skip where
  \<open>unit_propagation_inner_loop_body_l_with_skip L = (\<lambda>(S, n). do {
    ASSERT (clauses_to_update_l S \<noteq> {#} \<or> n > 0);
    ASSERT(unit_propagation_inner_loop_l_inv L (S, n));
    b \<leftarrow> SPEC(\<lambda>b. (b \<longrightarrow> n > 0) \<and> (\<not>b \<longrightarrow> clauses_to_update_l S \<noteq> {#}));
    if \<not>b then do {
      ASSERT (clauses_to_update_l S \<noteq> {#});
      (S', C) \<leftarrow> select_from_clauses_to_update S;
      T \<leftarrow> unit_propagation_inner_loop_body_l L C S';
      RETURN (T, if get_conflict_l T = None then n else 0)
    } else RETURN (S, n-1)
  })\<close>

definition unit_propagation_inner_loop_l :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>unit_propagation_inner_loop_l L S\<^sub>0 = do {
    ASSERT(L \<in># all_lits_of_mm (get_all_clss_l S\<^sub>0));
    n \<leftarrow> SPEC(\<lambda>_::nat. True);
    (S, n) \<leftarrow> WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_l_inv L\<^esup>
      (\<lambda>(S, n). clauses_to_update_l S \<noteq> {#} \<or> n > 0)
      (unit_propagation_inner_loop_body_l_with_skip L)
      (S\<^sub>0, n);
    RETURN S
  }\<close>

lemma set_mset_clauses_to_update_l_set_mset_clauses_to_update_spec:
  assumes \<open>(S, S') \<in> twl_st_l (Some L)\<close>
  shows
    \<open>RES (set_mset (clauses_to_update_l S)) \<le> \<Down> {(C, (L', C')). L' = L \<and>
      C' = twl_clause_of (get_clauses_l S \<propto> C)}
    (RES (set_mset (clauses_to_update S')))\<close>
proof -
  obtain M N D NE UE WS Q where
    S: \<open>S = (M, N, D, NE, UE, WS, Q)\<close>
    by (cases S) auto
  show ?thesis
    using assms unfolding S by (auto simp add: Bex_def twl_st_l_def intro!: RES_refine)
qed

lemma clauses_to_update_l_empty_tw_st_of_Some_None[simp]:
  \<open>clauses_to_update_l S = {#} \<Longrightarrow> (S, S')\<in> twl_st_l (Some L) \<longleftrightarrow> (S, S') \<in> twl_st_l None\<close>
  by (cases S) (auto simp: twl_st_l_def)

lemma cdcl_twl_cp_in_trail_stays_in:
  \<open>cdcl_twl_cp\<^sup>*\<^sup>* S' aa \<Longrightarrow> - x1 \<in> lits_of_l (get_trail S') \<Longrightarrow> - x1 \<in> lits_of_l (get_trail aa)\<close>
  by (induction rule: rtranclp_induct)
     (auto elim!: cdcl_twl_cpE)

lemma cdcl_twl_cp_in_trail_stays_in_l:
  \<open>(x2, S') \<in> twl_st_l (Some x1)  \<Longrightarrow> cdcl_twl_cp\<^sup>*\<^sup>* S' aa \<Longrightarrow> - x1 \<in> lits_of_l (get_trail_l x2) \<Longrightarrow>
       (a, aa) \<in> twl_st_l (Some x1) \<Longrightarrow>  - x1 \<in> lits_of_l (get_trail_l a)\<close>
  using cdcl_twl_cp_in_trail_stays_in[of S' aa \<open>x1\<close>]
  by (auto simp: twl_st twl_st_l)

lemma unit_propagation_inner_loop_l:
  \<open>(uncurry unit_propagation_inner_loop_l, unit_propagation_inner_loop) \<in>
  {((L, S), S'). (S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S \<and> -L \<in> lits_of_l (get_trail_l S) \<and>
     L  \<in># all_lits_of_mm (get_all_clss_l S)} \<rightarrow>\<^sub>f
  \<langle>{(T, T'). (T, T') \<in> twl_st_l None \<and> clauses_to_update_l T = {#} \<and>
    twl_list_invs T}\<rangle> nres_rel\<close>
  (is \<open>?unit_prop_inner \<in> ?A \<rightarrow>\<^sub>f \<langle>?B\<rangle>nres_rel\<close>)
proof -
  have SPEC_remove: \<open>select_from_clauses_to_update S
       \<le> \<Down> {((T', C), C').
             (T', set_clauses_to_update (clauses_to_update S'' - {#C'#}) S'') \<in> twl_st_l (Some L) \<and>
              T' = set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S \<and>
              C' \<in># clauses_to_update S'' \<and>
              C \<in># clauses_to_update_l S \<and>
              snd C' = twl_clause_of (get_clauses_l S \<propto> C)}
             (SPEC (\<lambda>C. C \<in># clauses_to_update S''))\<close>
    if \<open>(S, S'') \<in> {(T, T'). (T, T') \<in> twl_st_l (Some L) \<and> twl_list_invs T}\<close>
    for S :: \<open>'v twl_st_l\<close> and S'' L
    using that unfolding select_from_clauses_to_update_def
    by (auto simp: conc_fun_def image_mset_remove1_mset_if twl_st_l_def)
  show ?thesis
    unfolding unit_propagation_inner_loop_l_def unit_propagation_inner_loop_def uncurry_def
      unit_propagation_inner_loop_body_l_with_skip_def
    apply (intro frefI nres_relI)
    subgoal for LS S'
      apply (rewrite in \<open>let _ = set_clauses_to_update _ _ in _\<close> Let_def)
      apply (refine_vcg set_mset_clauses_to_update_l_set_mset_clauses_to_update_spec
        WHILEIT_refine_genR[where
           R = \<open>{(T, T'). (T, T') \<in> twl_st_l None \<and> twl_list_invs T \<and> clauses_to_update_l T = {#}}
              \<times>\<^sub>f nat_rel\<close> and
           R' = \<open>{(T, T'). (T, T') \<in> twl_st_l (Some (fst LS)) \<and> twl_list_invs T}
          \<times>\<^sub>f nat_rel\<close>]
          unit_propagation_inner_loop_body_l_unit_propagation_inner_loop_body[THEN fref_to_Down_curry2]
        SPEC_remove;
        remove_dummy_vars)
      subgoal for x1 x2
        by (auto simp add: in_all_lits_of_mm_uminus_iff twl_st_l
         mset_take_mset_drop_mset')
      subgoal by simp
      subgoal for x1 x2 n na x x' unfolding unit_propagation_inner_loop_l_inv_def
        apply (case_tac x; case_tac x')
        apply (simp only: prod.simps)
        by (rule exI[of _ \<open>fst x'\<close>]) (auto intro: cdcl_twl_cp_in_trail_stays_in_l)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
          apply (subst (asm) prod_rel_iff)
          apply normalize_goal
           apply assumption
      apply (rule_tac I=x1 in EQI)
      subgoal for x1 x2 n na x1a x2a x1b x2b b ba x1c x2c x1d x2d
        apply (subst in_pair_collect_simp)
        apply (subst prod.case)+
        apply (rule_tac x = x1b in exI)
        apply (rule_tac x = x1a in exI)
        apply (intro conjI)
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
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      done
    done
qed

definition clause_to_update :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v clauses_to_update_l\<close>where
  \<open>clause_to_update L S =
    filter_mset
      (\<lambda>C::nat. L \<in> set (watched_l (get_clauses_l S \<propto> C)))
      (dom_m (get_clauses_l S))\<close>

lemma distinct_mset_clause_to_update: \<open>distinct_mset (clause_to_update L C)\<close>
  unfolding clause_to_update_def
  apply (rule distinct_mset_filter)
  using distinct_mset_dom by blast

lemma in_clause_to_updateD: \<open>b \<in># clause_to_update L' T \<Longrightarrow> b \<in># dom_m (get_clauses_l T)\<close>
  by (auto simp: clause_to_update_def)

lemma in_clause_to_update_iff:
  \<open>C \<in># clause_to_update L S \<longleftrightarrow>
     C \<in># dom_m (get_clauses_l S) \<and> L \<in> set (watched_l (get_clauses_l S \<propto> C))\<close>
  by (auto simp: clause_to_update_def)

definition select_and_remove_from_literals_to_update :: \<open>'v twl_st_l \<Rightarrow>
    ('v twl_st_l \<times> 'v literal) nres\<close> where
  \<open>select_and_remove_from_literals_to_update S = SPEC(\<lambda>(S', L). L \<in># literals_to_update_l S \<and>
    S' = set_clauses_to_update_l (clause_to_update L S)
          (set_literals_to_update_l (literals_to_update_l S - {#L#}) S))\<close>

definition unit_propagation_outer_loop_l_inv where
  \<open>unit_propagation_outer_loop_l_inv S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_l None \<and> twl_struct_invs S' \<and> twl_stgy_invs S' \<and>
      clauses_to_update_l S = {#})\<close>

definition unit_propagation_outer_loop_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>unit_propagation_outer_loop_l S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>unit_propagation_outer_loop_l_inv\<^esup>
      (\<lambda>S. literals_to_update_l S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT(literals_to_update_l S \<noteq> {#});
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update S;
        unit_propagation_inner_loop_l L S'
      })
      (S\<^sub>0 :: 'v twl_st_l)
\<close>

lemma watched_twl_clause_of_watched: \<open>watched (twl_clause_of x) = mset (watched_l x)\<close>
  by (cases x) auto

lemma twl_st_of_clause_to_update:
  assumes
    TT': \<open>(T, T') \<in> twl_st_l None\<close> and
    \<open>twl_struct_invs T'\<close>
  shows
  \<open>(set_clauses_to_update_l
       (clause_to_update L' T)
       (set_literals_to_update_l (remove1_mset L' (literals_to_update_l T)) T),
    set_clauses_to_update
      (Pair L' `# {#C \<in># get_clauses T'. L' \<in># watched C#})
      (set_literals_to_update (remove1_mset L' (literals_to_update T'))
        T'))
    \<in> twl_st_l (Some L')\<close>
proof -
  obtain M N D NE UE NS US WS Q where
    T: \<open>T = (M, N, D, NE, UE, NS, US, WS, Q)\<close>
    by (cases T) auto

  have
    \<open>{#(L', TWL_Clause (mset (watched_l (N \<propto> x)))
          (mset (unwatched_l (N \<propto> x)))).
      x \<in># {#C \<in># dom_m N. L' \<in> set (watched_l (N \<propto> C))#}#} =
    Pair L' `#
      {#C \<in># {#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># init_clss_lf N#} +
            {#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)). x \<in># learned_clss_lf N#}.
      L' \<in># watched C#}\<close>
    (is \<open>{#(L', ?C x). x \<in># ?S#} = Pair L' `# ?C'\<close>)
  proof -
    have H: \<open>{#f (N \<propto> x). x \<in>#  {#x \<in># dom_m N. P (N \<propto> x)#}#} =
       {#f (fst x). x \<in># {#C \<in># ran_m N. P (fst C)#}#}\<close> for P and f :: \<open>'a literal list \<Rightarrow> 'b\<close>
        unfolding ran_m_def image_mset_filter_swap2 by auto

    have H: \<open>{#f (N\<propto>x). x \<in># ?S#} =
        {#f (fst x). x \<in># {#C \<in># init_clss_l N. L' \<in> set (watched_l (fst C))#}#} +
        {#f (fst x). x \<in># {#C \<in># learned_clss_l N. L' \<in> set (watched_l (fst C))#}#}\<close>
       for f :: \<open>'a literal list \<Rightarrow> 'b\<close>
      unfolding image_mset_union[symmetric] filter_union_mset[symmetric]
      apply auto
      apply (subst H)
      ..

    have L'': \<open>{#(L', ?C x). x \<in># ?S#} = Pair L' `# {#?C x. x \<in># ?S#}\<close>
      by auto
    also have \<open>\<dots> = Pair L' `# ?C'\<close>
      apply (rule arg_cong[of _ _ \<open>(`#) (Pair L')\<close>])
      unfolding image_mset_union[symmetric] mset_append[symmetric] drop_Suc H
      apply simp
      apply (subst H)
      unfolding image_mset_union[symmetric] mset_append[symmetric] drop_Suc H
        filter_union_mset[symmetric] image_mset_filter_swap2
      by auto
    finally show ?thesis .
  qed
  then show ?thesis
    using TT'
    by (cases T') (auto simp del: filter_union_mset
       simp: T split_beta clause_to_update_def twl_st_l_def
       split: if_splits)
qed

lemma twl_list_invs_set_clauses_to_update_iff:
  assumes \<open>twl_list_invs T\<close>
  shows \<open>twl_list_invs (set_clauses_to_update_l WS (set_literals_to_update_l Q T)) \<longleftrightarrow>
     ((\<forall>x\<in>#WS. case x of C \<Rightarrow> C \<in># dom_m (get_clauses_l T)) \<and>
     distinct_mset WS)\<close>
proof -
  obtain M N C NE UE WS NS US Q where
    T: \<open>T = (M, N, C, NE, UE, NS, US, WS, Q)\<close>
    by (cases T) auto
  show ?thesis
    using assms
    unfolding twl_list_invs_def T by auto
qed


lemma unit_propagation_outer_loop_l_spec:
  \<open>(unit_propagation_outer_loop_l, unit_propagation_outer_loop) \<in>
  {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f
  \<langle>{(S, S').
          (S, S') \<in> twl_st_l None \<and>
          clauses_to_update_l S = {#} \<and>
          twl_list_invs S}\<rangle> nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f ?I\<close> is \<open>_ \<in> _ \<rightarrow>\<^sub>f \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have twl_struct_invs_no_alien_in_trail: \<open>unit_propagation_outer_loop_l_inv T \<Longrightarrow>
    -x2a \<in> lits_of_l (get_trail_l T) \<Longrightarrow>
    x2a
    \<in># all_lits_of_mm
        ({#mset (fst x). x \<in># ran_m (get_clauses_l T)#} +
         get_unit_clauses_l T +
         get_subsumed_clauses_l
          T)\<close> for T x2a
    unfolding unit_propagation_outer_loop_l_inv_def
    apply normalize_goal+
    by (drule  twl_struct_invs_no_alien_in_trail[of _ \<open>-x2a\<close>])
      (simp_all add: mset_take_mset_drop_mset' in_all_lits_of_mm_uminus_iff)

  have H:
    \<open>select_and_remove_from_literals_to_update x
       \<le> \<Down> {((S', L'), (L, S)). L = L' \<and>  S' = set_clauses_to_update_l (clause_to_update L x)
              (set_literals_to_update_l (remove1_mset L (literals_to_update_l x)) x) \<and>
             L' \<in># literals_to_update_l x \<and>
             S = set_clauses_to_update {#(L, C)|C \<in># get_clauses x'. L \<in># watched C#}
           (set_literals_to_update (literals_to_update x' - {#L#}) x')}
           (mop_pop_literal_to_update x')\<close>
     if \<open>(x, x') \<in> twl_st_l None\<close> for x :: \<open>'v twl_st_l\<close> and x' :: \<open>'v twl_st\<close>
    using that unfolding select_and_remove_from_literals_to_update_def mop_pop_literal_to_update_def
      Let_def RES_RETURN_RES
    apply (cases x; cases x')
    apply refine_rcg
    by (clarsimp simp add: twl_st_l_def intro!: RES_refine)
  have H': \<open>unit_propagation_outer_loop_l_inv T \<Longrightarrow>
    x2 \<in># literals_to_update_l T \<Longrightarrow> - x2 \<in> lits_of_l (get_trail_l T)\<close>
    for S S' T T' L L' C x2
    by (auto simp: unit_propagation_outer_loop_l_inv_def twl_st_l_def twl_struct_invs_def)
  show H:
    \<open>(unit_propagation_outer_loop_l, unit_propagation_outer_loop) \<in>?R \<rightarrow>\<^sub>f
      \<langle>{(S, S').
          (S, S') \<in> twl_st_l None \<and>
          clauses_to_update_l S = {#} \<and>
          twl_list_invs S}\<rangle> nres_rel\<close>
    unfolding unit_propagation_outer_loop_l_def unit_propagation_outer_loop_def fref_param1[symmetric]
    apply (refine_vcg unit_propagation_inner_loop_l[THEN fref_to_Down_curry_left]
       H)
    subgoal by simp
    subgoal unfolding unit_propagation_outer_loop_l_inv_def by fastforce
    subgoal by auto
    subgoal by simp
    subgoal for S S' T T' L L' C x2
      by (auto simp add: twl_st_of_clause_to_update twl_list_invs_set_clauses_to_update_iff
          intro: cdcl_twl_cp_twl_struct_invs cdcl_twl_cp_twl_stgy_invs
          distinct_mset_clause_to_update H'
          dest: in_clause_to_updateD)
    subgoal for S S' T T' L L' C x2 x1a x2a
      using twl_struct_invs_no_alien_in_trail[of T \<open>snd L\<close>] H'[of T \<open>snd L\<close>]
      by (auto simp add: twl_st_of_clause_to_update twl_list_invs_set_clauses_to_update_iff
          intro: cdcl_twl_cp_twl_struct_invs cdcl_twl_cp_twl_stgy_invs
          distinct_mset_clause_to_update 
          dest: in_clause_to_updateD)
    done
qed

lemma get_conflict_l_get_conflict_state_spec:
  assumes \<open>(S, S') \<in> twl_st_l None\<close> and \<open>twl_list_invs S\<close> and \<open>clauses_to_update_l S = {#}\<close>
  shows \<open>((False, S), (False, S'))
  \<in> {((brk, S), (brk', S')). brk = brk' \<and> (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
    clauses_to_update_l S = {#}}\<close>
  using assms by auto

fun lit_and_ann_of_propagated where
  \<open>lit_and_ann_of_propagated (Propagated L C) = (L, C)\<close> |
  \<open>lit_and_ann_of_propagated (Decided _) = undefined\<close>
     \<comment>\<open>we should never call the function in that context\<close>

definition tl_state_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>tl_state_l = (\<lambda>(M, N, D, NE, UE, NS, US, WS, Q). (tl M, N, D, NE, UE, NS, US, WS, Q))\<close>

definition resolve_cls_l' :: \<open>'v twl_st_l \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> 'v clause\<close> where
\<open>resolve_cls_l' S C L  =
  remove1_mset L (remove1_mset (-L) (the (get_conflict_l S) \<union># mset (get_clauses_l S \<propto> C)))\<close>

definition update_confl_tl_l :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_l \<Rightarrow> bool \<times> 'v twl_st_l\<close> where
  \<open>update_confl_tl_l = (\<lambda>L C (M, N, D, NE, UE, NS, US, WS, Q).
     let D = resolve_cls_l' (M, N, D, NE, UE, NS, US, WS, Q) C L in
        (False, (tl M, N, Some D, NE, UE, NS, US, WS, Q)))\<close>

definition update_confl_tl_l_pre :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
\<open>update_confl_tl_l_pre L C S \<longleftrightarrow>
   (\<exists>S'. (S, S') \<in> twl_st_l None \<and> update_confl_tl_pre L (mset (get_clauses_l S \<propto> C)) S' \<and>
      twl_list_invs S \<and> C \<in># dom_m (get_clauses_l S) \<and> get_trail_l S \<noteq> [] \<and> hd (get_trail_l S) = Propagated L C \<and> C > 0)\<close>

definition mop_update_confl_tl_l :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> 'v twl_st_l \<Rightarrow> (bool \<times> 'v twl_st_l) nres\<close> where
  \<open>mop_update_confl_tl_l = (\<lambda>L C S. do {
     ASSERT(update_confl_tl_l_pre L C S);
     RETURN (update_confl_tl_l L C S)})\<close>

definition mop_hd_trail_l_pre :: \<open>'v twl_st_l \<Rightarrow> bool\<close> where
\<open>mop_hd_trail_l_pre S \<longleftrightarrow>
   (\<exists>S'. (S, S') \<in> twl_st_l None \<and> mop_hd_trail_pre S' \<and>
      twl_list_invs S \<and> mark_of (hd (get_trail_l S)) > 0)\<close>

definition mop_hd_trail_l :: \<open>'v twl_st_l \<Rightarrow> ('v literal \<times> nat) nres\<close> where
  \<open>mop_hd_trail_l S = do{
     ASSERT(mop_hd_trail_l_pre S);
     SPEC(\<lambda>(L, C). Propagated L C = hd (get_trail_l S))
  }\<close>

definition mop_lit_notin_conflict_l :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> bool nres\<close> where
  \<open>mop_lit_notin_conflict_l L S = do {
    ASSERT(get_conflict_l S \<noteq> None \<and> -L \<notin># the (get_conflict_l S) \<and>
         L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_l S) + get_unit_clauses_l S +
           get_subsumed_clauses_l S));
    RETURN (L \<notin># the (get_conflict_l S))
  }\<close>

definition mop_tl_state_l_pre :: \<open>'v twl_st_l \<Rightarrow> bool\<close> where
\<open>mop_tl_state_l_pre S \<longleftrightarrow>
   (\<exists>S'. (S, S') \<in> twl_st_l None \<and> mop_tl_state_pre S' \<and>
      twl_list_invs S)\<close>

definition mop_tl_state_l :: \<open>'v twl_st_l \<Rightarrow> (bool \<times> 'v twl_st_l) nres\<close> where
  \<open>mop_tl_state_l = (\<lambda>S. do {
    ASSERT(mop_tl_state_l_pre S);
    RETURN(False, tl_state_l S)})\<close>

definition mop_maximum_level_removed_l_pre :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
\<open>mop_maximum_level_removed_l_pre L S \<longleftrightarrow>
   (\<exists>S'. (S, S') \<in> twl_st_l None \<and> mop_maximum_level_removed_pre L S' \<and>
      twl_list_invs S)\<close>

definition mop_maximum_level_removed_l :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> bool nres\<close> where
\<open>mop_maximum_level_removed_l L S = do {
   ASSERT (mop_maximum_level_removed_l_pre L S);
   RETURN (get_maximum_level (get_trail_l S) (remove1_mset (-L) (the (get_conflict_l S))) =
      count_decided (get_trail_l S))
}\<close>

definition skip_and_resolve_loop_inv_l where
  \<open>skip_and_resolve_loop_inv_l S\<^sub>0 brk S \<longleftrightarrow>
   (\<exists>S' S\<^sub>0'. (S, S') \<in> twl_st_l None \<and> (S\<^sub>0, S\<^sub>0') \<in> twl_st_l None \<and>
     skip_and_resolve_loop_inv S\<^sub>0' (brk, S') \<and>
        twl_list_invs S \<and> clauses_to_update_l S = {#} \<and>
        (\<not>is_decided (hd (get_trail_l S)) \<longrightarrow> mark_of (hd(get_trail_l S)) > 0))\<close>

definition skip_and_resolve_loop_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>skip_and_resolve_loop_l S\<^sub>0 =
    do {
      ASSERT(get_conflict_l S\<^sub>0 \<noteq> None);
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). skip_and_resolve_loop_inv_l S\<^sub>0 brk S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_l S)))
        (\<lambda>(_, S).
          do {
            (L, C) \<leftarrow> mop_hd_trail_l S;
            b \<leftarrow> mop_lit_notin_conflict_l (-L) S;
            if b then
              mop_tl_state_l S
            else do {
              b \<leftarrow> mop_maximum_level_removed_l L S;
              if b
              then
                mop_update_confl_tl_l L C S
              else
                RETURN (True, S)
            }
          }
        )
        (False, S\<^sub>0);
      RETURN S
    }
  \<close>

lemma get_level_same_lits_cong:
  assumes
    \<open>map (atm_of o lit_of) M = map (atm_of o lit_of) M'\<close> and
    \<open>map is_decided M = map is_decided M'\<close>
  shows \<open>get_level M L = get_level M' L\<close>
proof -
  have [dest]: \<open>map is_decided M = map is_decided zsa \<Longrightarrow>
       length (filter is_decided M) = length (filter is_decided zsa)\<close>
    for M :: \<open>('d, 'e, 'f) annotated_lit list\<close> and zsa :: \<open>('g, 'h, 'i) annotated_lit list\<close>
    by (induction M arbitrary: zsa) (auto simp: get_level_def)

  show ?thesis
    using assms
    by (induction M arbitrary: M') (auto simp: get_level_def )
qed

lemma clauses_in_unit_clss_have_level0:
  assumes
    struct_invs: \<open>twl_struct_invs T\<close> and
    C: \<open>C \<in># unit_clss T\<close> and
    LC_T: \<open>Propagated L C \<in> set (get_trail T)\<close> and
    count_dec: \<open>0 < count_decided (get_trail T)\<close>
  shows
     \<open>get_level (get_trail T) L = 0\<close> (is ?lev_L) and
     \<open>\<forall>K\<in># C. get_level (get_trail T) K = 0\<close> (is ?lev_K)
proof -
  have
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of T)\<close> and
    ent: \<open>entailed_clss_inv (pstate\<^sub>W_of T)\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      pcdcl_all_struct_invs_def state\<^sub>W_of_def[symmetric]
    by fast+
  obtain K where
    \<open>K \<in># C\<close> and lev_K: \<open>get_level (get_trail T) K = 0\<close> and K_M: \<open>K \<in> lits_of_l (get_trail T)\<close>
    using ent C count_dec by (cases T; cases \<open>get_conflict T\<close>) (auto simp: entailed_clss_inv.simps)

  obtain M1 M2 where
    M: \<open>get_trail T = M2 @ Propagated L C # M1\<close>
    using LC_T by (blast elim: in_set_list_format)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of T)\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of T) \<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have M1: \<open>M1 \<Turnstile>as CNot (remove1_mset L C)\<close> and \<open>L \<in># C\<close>
    using M unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (auto simp: twl_st)
  moreover have n_d: \<open>no_dup (get_trail T)\<close>
    using lev_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by simp
  ultimately have \<open>L = K\<close>
    using \<open>K \<in># C\<close> M K_M
    by (auto dest!: multi_member_split simp: add_mset_eq_add_mset
      dest: in_lits_of_l_defined_litD no_dup_uminus_append_in_atm_notin
      no_dup_appendD no_dup_consistentD)
  then show ?lev_L
    using lev_K by simp
  have count_dec_M1: \<open>count_decided M1 = 0\<close>
    using M n_d \<open>?lev_L\<close> by auto
  have \<open>get_level (get_trail T) K = 0\<close> if \<open>K \<in># C\<close> for K
  proof -
    have \<open>-K \<in> lits_of_l (Propagated (-L) C # M1)\<close>
     using M1 M that by (auto simp: true_annots_true_cls_def_iff_negation_in_model remove1_mset_add_mset_If
      dest!: multi_member_split dest: in_diffD split: if_splits)
    then have \<open>get_level (get_trail T) K = get_level (Propagated (-L) C # M1) K\<close>
      apply -
      apply (subst (2) get_level_skip[symmetric, of M2])
      using n_d M by (auto dest: no_dup_uminus_append_in_atm_notin
        intro: get_level_same_lits_cong)
    then show ?thesis
      using count_decided_ge_get_level[of \<open>Propagated (-L) C # M1\<close> K] count_dec_M1
      by (auto simp: get_level_cons_if split: if_splits)
  qed
  then show ?lev_K
    by fast
qed

lemma clauses_clss_have_level1_notin_unit:
  assumes
    struct_invs: \<open>twl_struct_invs T\<close> and
    LC_T: \<open>Propagated L C \<in> set (get_trail T)\<close> and
    count_dec: \<open>0 < count_decided (get_trail T)\<close> and
     \<open>get_level (get_trail T) L > 0\<close>
  shows
     \<open>C \<notin># unit_clss T\<close>
  using clauses_in_unit_clss_have_level0[of T C, OF struct_invs _ LC_T count_dec] assms
  by linarith

lemma skip_and_resolve_loop_l_spec:
  \<open>(skip_and_resolve_loop_l, skip_and_resolve_loop) \<in>
    {(S::'v twl_st_l, S'). (S, S') \<in> twl_st_l None \<and> twl_struct_invs S' \<and>
       twl_stgy_invs S' \<and>
       twl_list_invs S \<and> clauses_to_update_l S = {#} \<and> literals_to_update_l S = {#} \<and>
       get_conflict S' \<noteq> None \<and>
       0 < count_decided (get_trail_l S)} \<rightarrow>\<^sub>f
  \<langle>{(T, T'). (T, T') \<in> twl_st_l None \<and> twl_list_invs T \<and>
    (twl_struct_invs T' \<and> twl_stgy_invs T' \<and>
    no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of T') \<and>
    no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of T') \<and>
    literals_to_update T' = {#} \<and>
    clauses_to_update_l T = {#} \<and> get_conflict T' \<noteq> None)}\<rangle> nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f _\<close>)
proof -
  let ?R' = \<open>{(T::'v twl_st_l, T'). (T, T') \<in> twl_st_l None \<and> twl_list_invs T \<and>
        clauses_to_update_l T = {#}}\<close>
  have H: \<open>((False, x), False, y) \<in> bool_rel \<times>\<^sub>f ?R'\<close> if \<open>(x, y) \<in> ?R'\<close> for x y
    using that by auto

  have
    mark_ge_0: \<open>0 < mark_of (hd (get_trail_l T))\<close> (is ?ge) and
    nempty: \<open>get_trail_l T \<noteq> []\<close> \<open>get_trail (snd brkT') \<noteq> []\<close> (is ?nempty)
  if
    SS': \<open>(S, S') \<in> ?R\<close> and
    \<open>get_conflict_l S \<noteq> None\<close> and
    brk_TT': \<open>(brkT, brkT')
     \<in> {((brk, S), brk', S'). brk = brk' \<and> (S, S') \<in> twl_st_l None \<and>
        twl_list_invs S \<and> clauses_to_update_l S = {#}}\<close> (is \<open>_ \<in> ?brk\<close>) and
    loop_inv: \<open>skip_and_resolve_loop_inv S' brkT'\<close> and
    brkT: \<open>brkT = (brk, T)\<close> and
    dec: \<open>\<not> is_decided (hd (get_trail_l T))\<close>
    for S S' brkT brkT' brk T
  proof -
    obtain brk' T' where brkT': \<open>brkT' = (brk', T')\<close> by (cases brkT')
    have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of T')\<close> and
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of T')\<close> and
      tr: \<open>get_trail T' \<noteq> []\<close> \<open>get_trail_l T \<noteq> []\<close> and
      count_dec: \<open>count_decided (get_trail_l T) \<noteq> 0\<close> \<open>count_decided (get_trail T') \<noteq> 0\<close> and
      TT': \<open>(T,T') \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs T'\<close>
      using loop_inv brk_TT' unfolding twl_struct_invs_def skip_and_resolve_loop_inv_def brkT brkT'
        prod.simps state\<^sub>W_of_def[symmetric] pcdcl_all_struct_invs_def
      by auto
    moreover have \<open>Suc 0 \<le> backtrack_lvl (state\<^sub>W_of T')\<close>
      using count_dec TT' by (auto simp: trail.simps)
    moreover have proped: \<open>is_proped (cdcl\<^sub>W_restart_mset.hd_trail (state\<^sub>W_of T'))\<close>
      using dec tr TT' by (cases \<open>get_trail_l T\<close>)
      (auto simp: trail.simps is_decided_no_proped_iff twl_st)
    moreover have \<open>mark_of (hd (get_trail T')) \<notin># unit_clss T'\<close>
      using clauses_clss_have_level1_notin_unit(1)[of T' \<open>lit_of (hd (get_trail T'))\<close>
          \<open>mark_of (hd (get_trail T'))\<close>] dec struct_invs count_dec tr proped TT'
      by (cases \<open>get_trail T'\<close>; cases \<open>hd (get_trail T')\<close>)
        (auto simp: twl_st)
    moreover have \<open>convert_lit (get_clauses_l T) (unit_clss T') (hd (get_trail_l T))
         (hd (get_trail T'))\<close>
      using tr dec TT'
      by (cases \<open>get_trail T'\<close>; cases \<open>get_trail_l T\<close>)
        (auto simp: twl_st_l_def)
    ultimately have \<open>mark_of (hd (get_trail_l T)) = 0 \<Longrightarrow> False\<close>
      using tr dec TT' by (cases \<open>get_trail_l T\<close>; cases \<open>hd (get_trail_l T)\<close>)
        (auto simp: trail.simps twl_st convert_lit.simps)
    then show ?ge by blast
    show \<open>get_trail_l T \<noteq> []\<close> \<open>get_trail (snd brkT') \<noteq> []\<close>
      using tr TT' brkT' by auto
  qed

  have mop_hd_trail_l:
    \<open>mop_hd_trail_l S \<le> \<Down>{((L, C), (L', C')). L = L' \<and>
           C' = mset (get_clauses_l S \<propto> C) \<and> C \<in># dom_m (get_clauses_l S) \<and> get_trail_l S \<noteq> [] \<and>
          hd (get_trail_l S) = Propagated L C \<and> C > 0} (mop_hd_trail S')\<close>
    (is \<open>_ \<le> \<Down> ?hd _\<close>)
    if \<open>(brkS, brkS') \<in> bool_rel \<times>\<^sub>f ?R'\<close> and
     \<open>case brkS of (brk, S) \<Rightarrow> skip_and_resolve_loop_inv_l S\<^sub>0 brk S\<close> and
     \<open>case brkS of (brk, S) \<Rightarrow> \<not>brk \<and> \<not> is_decided (hd (get_trail_l S))\<close> and
     \<open>brkS = (brk, S)\<close> and
     \<open>brkS' = (brk', S')\<close>
    for S S' S\<^sub>0 brk brkS brkS' brk'
    using that
    unfolding mop_hd_trail_l_def mop_hd_trail_def
    apply refine_rcg
    subgoal unfolding mop_hd_trail_l_pre_def skip_and_resolve_loop_inv_l_def
        mop_hd_trail_def
      by (rule exI[of _ S']) auto
    subgoal
      apply (rule RES_refine)
      using mark_ge_0[of S S' brkS brkS']
      apply (cases \<open>get_trail S'\<close>; cases \<open>get_trail_l S\<close>;
        cases \<open>hd (get_trail S')\<close>)
      by (auto simp: mop_hd_trail_pre_def twl_st_l_def
        convert_lit.simps mop_hd_trail_l_pre_def)
    done

 have mop_lit_notin_conflict_l:
    \<open>mop_lit_notin_conflict_l (-L) S \<le> \<Down>Id (mop_lit_notin_conflict (-L') S')\<close>
    if \<open>(brkS, brkS') \<in> bool_rel \<times>\<^sub>f ?R'\<close> and
      \<open>case brkS of (brk, S) \<Rightarrow> skip_and_resolve_loop_inv_l S\<^sub>0 brk S\<close> and
      \<open>case brkS of (brk, S) \<Rightarrow> \<not>brk \<and> \<not> is_decided (hd (get_trail_l S))\<close> and
      \<open>brkS = (brk, S)\<close> and
      \<open>brkS' = (brk', S')\<close> and
      \<open>LC = (L, C)\<close> and
      \<open>LC' = (L', C')\<close> and
      \<open>((LC), (LC')) \<in> ?hd S\<close>
    for S S' S\<^sub>0 brk brkS brkS' brk' L L' C C' LC LC'
    using that
    unfolding mop_lit_notin_conflict_l_def mop_lit_notin_conflict_def
    apply refine_rcg
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: mset_take_mset_drop_mset')
    subgoal
      by auto
    done

 have mop_maximum_level_removed_l:
    \<open>mop_maximum_level_removed_l L S \<le> \<Down>bool_rel (mop_maximum_level_removed L' S')\<close>
    if \<open>(brkS, brkS') \<in> bool_rel \<times>\<^sub>f ?R'\<close> and
      \<open>case brkS of (brk, S) \<Rightarrow> skip_and_resolve_loop_inv_l S\<^sub>0 brk S\<close> and
      \<open>case brkS of (brk, S) \<Rightarrow> \<not>brk \<and> \<not> is_decided (hd (get_trail_l S))\<close> and
      \<open>brkS = (brk, S)\<close> and
      \<open>brkS' = (brk', S')\<close> and
      \<open>LC = (L, C)\<close> and
      \<open>LC' = (L', C')\<close> and
      \<open>((LC), (LC')) \<in> ?hd S\<close>
    for S S' S\<^sub>0 brk brkS brkS' brk' L L' C C' LC LC'
    using that
    unfolding mop_maximum_level_removed_l_def mop_maximum_level_removed_def
    apply refine_rcg
    subgoal
      unfolding mop_maximum_level_removed_l_pre_def
      by (rule exI[of _ \<open>S'\<close>]) auto
    subgoal
      by auto
    done

  have mop_tl_state_l:
   \<open>mop_tl_state_l S \<le> \<Down> (bool_rel \<times>\<^sub>f ?R') (mop_tl_state S')\<close>
    if \<open>(brkS, brkS') \<in> bool_rel \<times>\<^sub>f ?R'\<close> and
      \<open>case brkS of (brk, S) \<Rightarrow> skip_and_resolve_loop_inv_l S\<^sub>0 brk S\<close> and
      \<open>case brkS of (brk, S) \<Rightarrow> \<not>brk \<and> \<not> is_decided (hd (get_trail_l S))\<close> and
      \<open>brkS = (brk, S)\<close> and
      \<open>brkS' = (brk', S')\<close> and
      \<open>LC = (L, C)\<close> and
      \<open>LC' = (L', C')\<close> and
      \<open>((LC), (LC')) \<in> ?hd S\<close>
    for S S' S\<^sub>0 brk brkS brkS' brk' L L' C C' LC LC'
    using that unfolding mop_tl_state_l_def mop_tl_state_def
    apply refine_rcg
    subgoal
      unfolding mop_tl_state_l_pre_def
      by (rule exI[of _ \<open>S'\<close>]) auto
    subgoal
      by (cases S; cases S'; cases \<open>get_trail_l S\<close>; cases \<open>get_trail S'\<close>)
        (auto simp: tl_state_l_def tl_state_def twl_st_l_def
         convert_lits_l_tlD mop_tl_state_pre_def twl_list_invs_def)
    done

  have mop_update_confl_tl_l:
   \<open>mop_update_confl_tl_l L C S \<le> \<Down> (bool_rel \<times>\<^sub>f ?R') (mop_update_confl_tl L' C' S')\<close>
    if \<open>(brkS, brkS') \<in> bool_rel \<times>\<^sub>f ?R'\<close> and
      \<open>case brkS of (brk, S) \<Rightarrow> skip_and_resolve_loop_inv_l S\<^sub>0 brk S\<close> and
      \<open>case brkS of (brk, S) \<Rightarrow> \<not>brk \<and> \<not> is_decided (hd (get_trail_l S))\<close> and
      \<open>brkS = (brk, S)\<close> and
      \<open>brkS' = (brk', S')\<close> and
      \<open>LC = (L, C)\<close> and
      \<open>LC' = (L', C')\<close> and
      \<open>((LC), (LC')) \<in> ?hd S\<close>
    for S S' S\<^sub>0 brk brkS brkS' brk' L L' C C' LC LC'
    using that unfolding mop_update_confl_tl_l_def mop_update_confl_tl_def
    apply refine_rcg
    subgoal
      unfolding update_confl_tl_l_pre_def
      by (rule exI[of _ \<open>S'\<close>]) (auto simp: twl_struct_invs_def)
    subgoal
      by (cases S; cases S'; cases \<open>get_trail_l S\<close>; cases \<open>get_trail S'\<close>)
        (auto simp: update_confl_tl_l_def update_confl_tl_def twl_st_l_def
         convert_lits_l_tlD mop_tl_state_pre_def twl_list_invs_def resolve_cls_l'_def)
    done


  have H:
    \<open>(skip_and_resolve_loop_l, skip_and_resolve_loop) \<in> ?R \<rightarrow>\<^sub>f
      \<langle>{(T::'v twl_st_l, T'). (T, T') \<in> twl_st_l None \<and> twl_list_invs T \<and>
        clauses_to_update_l T = {#}}\<rangle> nres_rel\<close>
    apply (intro frefI nres_relI)
    unfolding skip_and_resolve_loop_l_def skip_and_resolve_loop_def
    apply (refine_rcg H)
    subgoal by auto
    subgoal by auto
    subgoal for x y xa x' x1 x2
      unfolding skip_and_resolve_loop_inv_l_def
      apply (cases x')
      apply(rule exI[of _ \<open>snd x'\<close>])
      apply(rule exI[of _ y])
      apply (intro conjI impI)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (rule mark_ge_0) auto
      done
    subgoal by (auto simp: twl_st_l twl_st skip_and_resolve_loop_inv_def)
    apply (rule mop_hd_trail_l; assumption)
    apply (rule mop_lit_notin_conflict_l; assumption)
    subgoal by auto
    apply (rule mop_tl_state_l; assumption)
    apply (rule mop_maximum_level_removed_l; assumption)
    subgoal by auto
    apply (rule mop_update_confl_tl_l; assumption)
    subgoal by auto
    subgoal by auto
    done

  have H: \<open>(skip_and_resolve_loop_l, skip_and_resolve_loop)
    \<in> ?R \<rightarrow>\<^sub>f
       \<langle>{(T::'v twl_st_l, T').
         (T, T') \<in> {(T, T'). (T, T') \<in> twl_st_l None \<and> (twl_list_invs T \<and>
         clauses_to_update_l T = {#})} \<and>
         T' \<in> {T'. twl_struct_invs T' \<and> twl_stgy_invs T' \<and>
         (no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of T')) \<and>
         (no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of T')) \<and>
         literals_to_update T' = {#} \<and>
         get_conflict T' \<noteq> None}}\<rangle>nres_rel\<close>
    apply (rule refine_add_inv_generalised)
    subgoal by (rule H)
    subgoal for S S'
      apply (rule order_trans)
      apply (rule skip_and_resolve_loop_spec[of S'])
      by auto
    done
  show ?thesis
    using H apply -
    apply (match_spec; (match_fun_rel; match_fun_rel?)+)
    by blast+
qed

definition find_decomp :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>find_decomp =  (\<lambda>L (M, N, D, NE, UE, NS, US, WS, Q).
    SPEC(\<lambda>S. \<exists>K M2 M1. S = (M1, N, D, NE, UE, NS, US, WS, Q) \<and>
       (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (the D - {#-L#}) + 1))\<close>

lemma find_decomp_alt_def:
  \<open>find_decomp L S =
     SPEC(\<lambda>T. \<exists>K M2 M1. equality_except_trail S T \<and> get_trail_l T = M1 \<and>
       (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_l S)) \<and>
          get_level (get_trail_l S) K =
            get_maximum_level (get_trail_l S) (the (get_conflict_l S) - {#-L#}) + 1)\<close>
  unfolding find_decomp_def
  by (cases S) force

definition find_lit_of_max_level_l :: \<open>'v twl_st_l \<Rightarrow> 'v literal \<Rightarrow> 'v literal nres\<close> where
  \<open>find_lit_of_max_level_l =  (\<lambda>(M, N, D, NE, UE, WS, Q) L.
    SPEC(\<lambda>L'. L' \<in># the D - {#-L#} \<and> get_level M L' = get_maximum_level M (the D - {#-L#})))\<close>

lemma find_lit_of_max_level_l_alt_def:
   \<open>find_lit_of_max_level_l = (\<lambda>S L.
    SPEC(\<lambda>L'. L' \<in># the (get_conflict_l S) - {#-L#} \<and>
      get_level (get_trail_l S) L' = get_maximum_level (get_trail_l S) (the (get_conflict_l S) - {#-L#})))\<close>
  by (auto simp: find_lit_of_max_level_l_def intro!: ext)

definition ex_decomp_of_max_lvl :: \<open>('v, nat) ann_lits \<Rightarrow> 'v cconflict \<Rightarrow> 'v literal \<Rightarrow> bool\<close> where
  \<open>ex_decomp_of_max_lvl M D L \<longleftrightarrow>
       (\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (remove1_mset (-L) (the D)) + 1)\<close>

fun add_mset_list :: \<open>'a list \<Rightarrow> 'a multiset multiset \<Rightarrow> 'a multiset multiset\<close>  where
  \<open>add_mset_list L UE = add_mset (mset L) UE\<close>

definition (in -)list_of_mset :: \<open>'v clause \<Rightarrow> 'v clause_l nres\<close> where
  \<open>list_of_mset D = SPEC(\<lambda>D'. D = mset D')\<close>

definition extract_shorter_conflict_l_pre :: \<open>'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>extract_shorter_conflict_l_pre S \<longleftrightarrow> (\<exists>S'. (S, S') \<in> twl_st_l None \<and>
      extract_shorter_conflict_pre S')\<close>

fun extract_shorter_conflict_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close>
   where
  \<open>extract_shorter_conflict_l (M, N, D, NE, UE, NS, US, WS, Q) = do {
    ASSERT(extract_shorter_conflict_l_pre (M, N, D, NE, UE, NS, US, WS, Q));
    SPEC(\<lambda>S.
       \<exists>D'. D' \<subseteq># the D \<and> S = (M, N, Some D', NE, UE, NS, US, WS, Q) \<and>
       clause `# twl_clause_of `# ran_mf N + NE + UE + NS + US \<Turnstile>pm D' \<and> -(lit_of (hd M)) \<in># D')
  }\<close>

declare extract_shorter_conflict_l.simps[simp del]
lemmas extract_shorter_conflict_l_def = extract_shorter_conflict_l.simps

lemma extract_shorter_conflict_l_alt_def:
   \<open>extract_shorter_conflict_l S =  do {
   ASSERT(extract_shorter_conflict_l_pre S);
    SPEC(\<lambda>T.
     \<exists>D'. D' \<subseteq># the (get_conflict_l S) \<and> equality_except_conflict_l S T \<and>
      get_conflict_l T = Some D' \<and>
     get_all_clss_l S \<Turnstile>pm D' \<and>
     -lit_of (hd (get_trail_l S)) \<in># D') }\<close>
  by (cases S) (auto simp: extract_shorter_conflict_l_def
    mset_take_mset_drop_mset mset_take_mset_drop_mset' Un_assoc
    intro: bind_cong)

definition backtrack_l_inv where
  \<open>backtrack_l_inv S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_l None \<and>
      backtrack_inv S' \<and>
      twl_list_invs S \<and>
      literals_to_update_l S = {#})
  \<close>

definition get_fresh_index :: \<open>'v clauses_l \<Rightarrow> nat nres\<close> where
\<open>get_fresh_index N = SPEC(\<lambda>i. i > 0 \<and> i \<notin># dom_m N)\<close>

definition propagate_bt_l_pre where
  \<open>propagate_bt_l_pre L L' S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_l None \<and> propagate_bt_pre L L' S')\<close>

definition propagate_bt_l :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>propagate_bt_l = (\<lambda>L L' (M, N, D, NE, UE, NS, US, WS, Q). do {
    ASSERT(propagate_bt_l_pre L L' (M, N, D, NE, UE, NS, US, WS, Q));
    ASSERT(L \<in># all_lits_of_mm (get_all_clss_l (M, N, D, NE, UE, NS, US, WS, Q)));
    ASSERT(L' \<in># all_lits_of_mm (get_all_clss_l (M, N, D, NE, UE, NS, US, WS, Q)));
    D'' \<leftarrow> list_of_mset (the D);
    i \<leftarrow> get_fresh_index N;
    M \<leftarrow> cons_trail_propagate_l (-L) i M;
    RETURN (M,
        fmupd i ([-L, L'] @ (remove1 (-L) (remove1 L' D'')), False) N,
          None, NE, UE, NS, US, WS, {#L#})
      })\<close>

definition propagate_unit_bt_l_pre where
  \<open>propagate_unit_bt_l_pre L S \<longleftrightarrow>
     (\<exists>S'. (S, S') \<in> twl_st_l None \<and> propagate_unit_bt_pre L S')\<close>

definition propagate_unit_bt_l :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>propagate_unit_bt_l = (\<lambda>L (M, N, D, NE, UE, NS, US, WS, Q). do {
    ASSERT(L \<in># all_lits_of_mm (get_all_clss_l (M, N, D, NE, UE, NS, US, WS, Q)));
    ASSERT(propagate_unit_bt_l_pre L (M, N, D, NE, UE, NS, US, WS, Q));
    M \<leftarrow> cons_trail_propagate_l (-L) 0 M;
    RETURN (M, N, None, NE, add_mset (the D) UE, NS, US, WS, {#L#})})\<close>

definition mop_lit_hd_trail_l_pre :: \<open>'v twl_st_l \<Rightarrow> bool\<close> where
\<open>mop_lit_hd_trail_l_pre S \<longleftrightarrow>
  (\<exists>S'. (S, S') \<in> twl_st_l None \<and> mop_lit_hd_trail_pre S' \<and>
     twl_list_invs S)\<close>

definition mop_lit_hd_trail_l :: \<open>'v twl_st_l \<Rightarrow> ('v literal) nres\<close> where
  \<open>mop_lit_hd_trail_l S = do{
     ASSERT(mop_lit_hd_trail_l_pre S);
     SPEC(\<lambda>L. L = lit_of (hd (get_trail_l S)))
  }\<close>

definition backtrack_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>backtrack_l S =
    do {
      ASSERT(backtrack_l_inv S);
      L \<leftarrow> mop_lit_hd_trail_l S;
      S \<leftarrow> extract_shorter_conflict_l S;
      S \<leftarrow> find_decomp L S;

      if size (the (get_conflict_l S)) > 1
      then do {
        L' \<leftarrow> find_lit_of_max_level_l S L;
        propagate_bt_l L L' S
      }
      else do {
        propagate_unit_bt_l L S
     }
  }\<close>

lemma backtrack_l_spec:
  \<open>(backtrack_l, backtrack) \<in>
    {(S::'v twl_st_l, S'). (S, S') \<in> twl_st_l None \<and> get_conflict_l S \<noteq> None \<and>
       get_conflict_l S \<noteq> Some {#} \<and>
       clauses_to_update_l S = {#} \<and> literals_to_update_l S = {#} \<and> twl_list_invs S \<and>
       twl_struct_invs S' \<and> twl_stgy_invs S' \<and>
       no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of S') \<and>
       no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of S')} \<rightarrow>\<^sub>f
    \<langle>{(T::'v twl_st_l, T'). (T, T') \<in> twl_st_l None \<and> get_conflict_l T = None \<and> twl_list_invs T \<and>
       twl_struct_invs T' \<and> twl_stgy_invs T' \<and> clauses_to_update_l T = {#} \<and>
       literals_to_update_l T \<noteq> {#}}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow>\<^sub>f ?I\<close>)
proof -
  let ?J = \<open>{(T::'v twl_st_l, T'). (T, T') \<in> twl_st_l None \<and> twl_list_invs T \<and>
       clauses_to_update_l T = {#} \<and> literals_to_update_l T \<noteq> {#}}\<close>
  let ?J' = \<open>{(T::'v twl_st_l, T'). (T, T') \<in> twl_st_l None \<and> twl_list_invs T \<and>
       clauses_to_update_l T = {#} \<and> literals_to_update_l T = {#}}\<close>
  have mop_lit_hd_trail_l:
    \<open>mop_lit_hd_trail_l x \<le> \<Down> Id (mop_lit_hd_trail y)\<close>
    if \<open>(x,y) \<in> ?R\<close>
    for x y
    using that
    unfolding mop_lit_hd_trail_l_def mop_lit_hd_trail_def
    apply refine_vcg
    subgoal
      unfolding mop_lit_hd_trail_l_pre_def
      by (rule exI[of _ y]) auto
    subgoal by (auto simp: mop_lit_hd_trail_pre_def)
    done
  have [simp]: \<open>(\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m aa \<and> snd a} \<union>
       (\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m aa \<and> \<not> snd a} \<union> A =
      (\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m aa}\<union> A\<close> for aa A
    by auto
  have extract_shorter_conflict_l: \<open>extract_shorter_conflict_l x
       \<le> \<Down> ?J'
           (extract_shorter_conflict y)\<close>
    if \<open>(x,y) \<in> ?R\<close>
    for x y
    using that
    unfolding extract_shorter_conflict_l_alt_def extract_shorter_conflict_alt_def
    apply refine_vcg
    subgoal
      unfolding extract_shorter_conflict_l_pre_def
      by (rule exI[of _ y]) auto
    subgoal
      by (rule RES_refine, rule_tac x = \<open>set_conflict (the (get_conflict_l s)) y\<close> in bexI)
        (auto simp: twl_st_l_def image_image image_Un mset_take_mset_drop_mset'
         extract_shorter_conflict_pre_def twl_list_invs_def)
    done

  have find_decomp: \<open>(L, La) \<in> Id \<Longrightarrow>
       (S, Sa) \<in> ?J' \<Longrightarrow>
       find_decomp L S
       \<le> \<Down> ?J' (reduce_trail_bt La Sa)\<close> for L La S Sa
    unfolding find_decomp_def reduce_trail_bt_def
      RES_RETURN_RES
    apply refine_vcg
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f
       x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l
      apply (rule RES_refine)
      apply (rule_tac x=\<open>(drop (length (get_trail Sa) - length (get_trail_l s)) (get_trail Sa),
         x1a, x1b, x1c, x1d, x1e, x1f,  x2f)\<close> in bexI)
    apply (auto simp: twl_st_l_def image_iff twl_list_invs_def
       intro: convert_lits_l_decomp_ex)
    apply (rule_tac x=K in exI)
      apply (auto simp: twl_st_l_def image_image image_Un mset_take_mset_drop_mset'
         extract_shorter_conflict_pre_def convert_lits_l_decomp_ex)
    done
  done

  have find_lit_of_max_level_l: \<open>(L, La) \<in> Id \<Longrightarrow>
       (S, Sa) \<in> ?J' \<Longrightarrow>
       (Sb, Sc) \<in> ?J' \<Longrightarrow>
       find_lit_of_max_level_l Sb L
       \<le> \<Down> Id (find_lit_of_max_level Sc La)\<close>
    for L La S Sa Sb Sc
    unfolding find_lit_of_max_level_l_alt_def
     find_lit_of_max_level_def
    by refine_rcg auto

  have [intro!]: \<open>mset x =
       add_mset (La) (add_mset L'a (mset x - {#La, L'a#}))\<close>
    if \<open>La \<in> set x\<close> and \<open>L'a \<in> set x\<close> \<open>La \<noteq> L'a\<close> for x La L'a
    using that
    by (metis add_mset_add_single diff_diff_add_mset in_multiset_in_set mset_add
        remove1_mset_add_mset_If)
  have propagate_bt_l: \<open>(Sb, Sc) \<in> ?J' \<Longrightarrow>
       (L', L'a) \<in> Id \<Longrightarrow>
       (L, La) \<in> Id \<Longrightarrow>
       propagate_bt_l L L' Sb
       \<le> \<Down> ?J
           (mop_propagate_bt La L'a Sc)\<close>
    for L La S Sa Sb Sc L' L'a
    unfolding propagate_bt_l_def
     mop_propagate_bt_def list_of_mset_def
     get_fresh_index_def cons_trail_propagate_l_def
    apply refine_vcg
    subgoal unfolding propagate_bt_l_pre_def by fast
    subgoal by (auto simp: propagate_bt_pre_def twl_st_l_def
       mset_take_mset_drop_mset' simp flip: image_mset_union)
        (simp add: union_assoc union_commute add.left_commute)
    subgoal by (auto simp: propagate_bt_pre_def twl_st_l_def
       mset_take_mset_drop_mset' simp flip: image_mset_union)
        (simp add: union_assoc union_commute add.left_commute)
    subgoal by (auto simp: propagate_bt_pre_def twl_st_l_def
       mset_take_mset_drop_mset' simp flip: image_mset_union)
    subgoal apply (auto simp: twl_list_invs_def propagate_bt_def twl_st_l_def
        propagate_bt_pre_def init_clss_l_mapsto_upd_irrel_notin
        learned_clss_l_mapsto_upd_notin
      intro!: convert_lit.intros(2)
      intro: convert_lit_bind_new convert_lits_l_bind_new)
      defer
      apply (rule convert_lits_l_bind_new)
      apply (auto simp: init_clss_l_mapsto_upd_irrel_notin
       learned_clss_l_mapsto_upd_notin)
      by (metis insert_DiffM member_add_mset set_mset_mset)
    done

  have propagate_unit_bt_l: \<open>(Sb, Sc) \<in> ?J' \<Longrightarrow>
       (L, La) \<in> Id \<Longrightarrow>
       propagate_unit_bt_l L Sb
       \<le> \<Down> ?J
           (mop_propagate_unit_bt La Sc)\<close>
    for L La S Sa Sb Sc L' L'a
    unfolding propagate_unit_bt_l_def
     mop_propagate_unit_bt_def cons_trail_propagate_l_def
    apply refine_vcg
    subgoal by (auto simp: propagate_unit_bt_pre_def twl_st_l_def
       mset_take_mset_drop_mset' simp flip: image_mset_union)
        (simp add: union_assoc union_commute add.left_commute)
    subgoal
      unfolding propagate_unit_bt_l_pre_def
      by blast
    subgoal by (auto simp: propagate_unit_bt_pre_def twl_st_l_def
       mset_take_mset_drop_mset' simp flip: image_mset_union)
    subgoal by (auto simp: twl_list_invs_def propagate_unit_bt_def twl_st_l_def
       convert_lits_l_add_mset intro!: convert_lit.intros)
    done

  have bt: \<open>(backtrack_l, backtrack) \<in>
      ?R \<rightarrow>\<^sub>f  \<langle>?J\<rangle> nres_rel\<close>
    unfolding backtrack_l_def backtrack_def
    apply (intro frefI nres_relI)
    apply (refine_rcg mop_lit_hd_trail_l)
    subgoal for x y
      unfolding backtrack_l_inv_def
      by (rule exI[of _ y]) auto
    apply (rule extract_shorter_conflict_l; assumption)
    apply (rule find_decomp; assumption)
    subgoal by auto
    apply (rule find_lit_of_max_level_l; assumption)
    apply (rule propagate_bt_l; assumption)
    apply (rule propagate_unit_bt_l; assumption)
    done

  have SPEC_Id: \<open>SPEC \<Phi> = \<Down> {(T, T'). \<Phi> T} (SPEC \<Phi>)\<close> for \<Phi>
    unfolding conc_fun_RES
    by auto
  have \<open>(backtrack_l S, backtrack S') \<in> ?I\<close> if \<open>(S, S') \<in> ?R\<close> for S S'
  proof -
    have \<open>backtrack_l S \<le> \<Down> ?J (backtrack S')\<close>
      by (rule bt[unfolded fref_param1[symmetric], "to_\<Down>", rule_format, of S S'])
        (use that in auto)
    moreover have \<open>backtrack S' \<le> SPEC (\<lambda>T. cdcl_twl_o S' T \<and>
               get_conflict T = None \<and>
               (\<forall>S'. \<not> cdcl_twl_o T S') \<and>
               twl_struct_invs T \<and>
               twl_stgy_invs T \<and> clauses_to_update T = {#} \<and> literals_to_update T \<noteq> {#})\<close>
      by (rule backtrack_spec["to_\<Down>", of S']) (use that in \<open>auto simp: twl_st_l\<close>)
    ultimately show ?thesis
      apply -
      apply (unfold refine_rel_defs nres_rel_def in_pair_collect_simp;
          (unfold Ball2_split_def all_to_meta)?;
          (intro allI impI)?)
      apply (subst (asm) SPEC_Id)
      apply unify_Down_invs2+
      unfolding nofail_simps
      apply unify_Down_invs2_normalisation_post
      apply (rule "weaken_\<Down>")
       prefer 2 apply assumption
      subgoal premises p by (auto simp: twl_st_l_def)
      done
  qed
  then show ?thesis
    by (intro frefI)
qed

definition find_unassigned_lit_l :: \<open>'v twl_st_l \<Rightarrow> 'v literal option nres\<close> where
  \<open>find_unassigned_lit_l = (\<lambda>(M, N, D, NE, UE, NS, US, WS, Q).
     SPEC (\<lambda>L.
         (L \<noteq> None \<longrightarrow>
            undefined_lit M (the L) \<and>
            atm_of (the L) \<in> atms_of_mm (mset `# ran_mf N + (NE+UE) + (NS+US))) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit M L' \<and>
            atm_of L' \<in> atms_of_mm (mset `# ran_mf N + (NE+UE) + (NS+US)))))
     )\<close>

definition decide_l_or_skip_pre where
\<open>decide_l_or_skip_pre S \<longleftrightarrow> (\<exists>S'. (S, S') \<in> twl_st_l None \<and>
   decide_or_skip_pre S' \<and>
   twl_list_invs S \<and>
   clauses_to_update_l S = {#} \<and>
   literals_to_update_l S = {#})
  \<close>


definition decide_lit_l :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>decide_lit_l = (\<lambda>L' (M, N, D, NE, UE, NS, US, WS, Q).
      (Decided L' # M, N, D, NE, UE, NS, US, WS, {#- L'#}))\<close>

definition decide_l_or_skip :: \<open>'v twl_st_l \<Rightarrow> (bool \<times> 'v twl_st_l) nres\<close> where
  \<open>decide_l_or_skip S = (do {
    ASSERT(decide_l_or_skip_pre S);
    L \<leftarrow> find_unassigned_lit_l S;
    case L of
      None \<Rightarrow> RETURN (True, S)
    | Some L \<Rightarrow> RETURN (False, decide_lit_l L S)
  })
\<close>
method "match_\<Down>" =
  (match conclusion in \<open>f \<le> \<Down> R g\<close> for f :: \<open>'a nres\<close> and R :: \<open>('a \<times> 'b) set\<close> and
    g :: \<open>'b nres\<close> \<Rightarrow>
    \<open>match premises in
      I[thin,uncurry]: \<open>f \<le> \<Down> R' g\<close> for R' :: \<open>('a \<times> 'b) set\<close>
          \<Rightarrow> \<open>rule refinement_trans_long[of f f g g R' R, OF refl refl _ I]\<close>
    \<bar> I[thin,uncurry]: \<open>_ \<Longrightarrow> f \<le> \<Down> R' g\<close> for R' :: \<open>('a \<times> 'b) set\<close>
          \<Rightarrow> \<open>rule refinement_trans_long[of f f g g R' R, OF refl refl _ I]\<close>
    \<close>)

lemma decide_l_or_skip_spec:
  \<open>(decide_l_or_skip, decide_or_skip) \<in>
    {(S, S'). (S, S') \<in> twl_st_l None \<and> get_conflict_l S = None \<and>
       clauses_to_update_l S = {#} \<and> literals_to_update_l S = {#} \<and> no_step cdcl_twl_cp S' \<and>
       twl_struct_invs S' \<and> twl_stgy_invs S' \<and> twl_list_invs S} \<rightarrow>\<^sub>f
    \<langle>{((brk, T), (brk', T')). (T, T') \<in> twl_st_l None \<and> brk = brk' \<and> twl_list_invs T \<and>
      clauses_to_update_l T = {#} \<and>
      (get_conflict_l T \<noteq> None \<longrightarrow> get_conflict_l T = Some {#})\<and>
         twl_struct_invs T' \<and> twl_stgy_invs T' \<and>
         (\<not>brk \<longrightarrow> literals_to_update_l T \<noteq> {#})\<and>
         (brk \<longrightarrow> literals_to_update_l T = {#})}\<rangle> nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f \<langle>?S\<rangle>nres_rel\<close>)
proof -
  have find_unassigned_lit_l: \<open>find_unassigned_lit_l S \<le> \<Down> Id (find_unassigned_lit S')\<close>
    if SS': \<open>(S, S') \<in> ?R\<close>
    for S S'
    using that
    unfolding find_unassigned_lit_l_def find_unassigned_lit_def
    apply (subst all_clss_l_ran_m[symmetric])
    apply (subst (3) all_clss_l_ran_m[symmetric])
    unfolding image_mset_union
    by (auto simp add:
          mset_take_mset_drop_mset' image_image twl_st_l_def)

  have I: \<open>(x, x') \<in> Id \<Longrightarrow> (x, x') \<in> \<langle>Id\<rangle>option_rel\<close> for x x' by auto
  have dec: \<open>(decide_l_or_skip, decide_or_skip) \<in> ?R \<rightarrow>
    \<langle>{((brk, T), (brk', T')). (T, T') \<in> twl_st_l None \<and> brk = brk' \<and> twl_list_invs T \<and>
      clauses_to_update_l T = {#} \<and>
       (\<not>brk \<longrightarrow> literals_to_update_l T \<noteq> {#})\<and>
       (brk \<longrightarrow> literals_to_update_l T = {#}) }\<rangle> nres_rel\<close>
    unfolding decide_l_or_skip_def decide_or_skip_def
    apply (refine_vcg find_unassigned_lit_l I)
    subgoal unfolding decide_l_or_skip_pre_def by (auto simp: twl_st_l_def)
    subgoal by auto
    subgoal for S S'
      by (cases S)
       (auto simp: decide_lit_l_def propagate_dec_def twl_list_invs_def twl_st_l_def)
    done
  have KK: \<open>SPEC (\<lambda>(brk, T). cdcl_twl_o\<^sup>*\<^sup>* S' T \<and> P brk T) = \<Down> {(S, S'). snd S = S' \<and>
     P (fst S) (snd S)} (SPEC (cdcl_twl_o\<^sup>*\<^sup>* S'))\<close>
    for S' P
    by (auto simp: conc_fun_def)
  have nf: \<open>nofail (SPEC (cdcl_twl_o\<^sup>*\<^sup>* S'))\<close> \<open>nofail (SPEC (cdcl_twl_o\<^sup>*\<^sup>* S'))\<close> for S S'
    by auto
  have set: \<open>{((a,b), (a', b')). P a b a' b'} = {(a, b). P (fst a) (snd a) (fst b) (snd b)}\<close> for P
    by auto

  show ?thesis
  proof (intro frefI nres_relI)
    fix S S'
    assume SS': \<open>(S, S') \<in> ?R\<close>
    have \<open>decide_l_or_skip S
    \<le> \<Down> {((brk, T), brk', T').
          (T, T') \<in> twl_st_l None \<and>
          brk = brk' \<and>
          twl_list_invs T \<and>
          clauses_to_update_l T = {#} \<and>
          (\<not> brk \<longrightarrow> literals_to_update_l T \<noteq> {#}) \<and> (brk \<longrightarrow> literals_to_update_l T = {#})}
        (decide_or_skip S')\<close>
      apply (rule dec["to_\<Down>", of S S'])
      using SS' by auto
    moreover have \<open>decide_or_skip S'
    \<le> \<Down> {(S, S'a).
          snd S = S'a \<and>
          get_conflict (snd S) = None \<and>
          (\<forall>S'. \<not> cdcl_twl_o (snd S) S') \<and>
          (fst S \<longrightarrow> (\<forall>S'. \<not> cdcl_twl_stgy (snd S) S')) \<and>
          twl_struct_invs (snd S) \<and>
          twl_stgy_invs (snd S) \<and>
          clauses_to_update (snd S) = {#} \<and>
          (\<not> fst S \<longrightarrow> literals_to_update (snd S) \<noteq> {#}) \<and>
          (\<not> (\<forall>S'a. \<not> cdcl_twl_o S' S'a) \<longrightarrow> cdcl_twl_o\<^sup>+\<^sup>+ S' (snd S))}
        (SPEC (cdcl_twl_o\<^sup>*\<^sup>* S'))\<close>
      by (rule decide_or_skip_spec[of S', unfolded KK]) (use SS' in auto)
    ultimately show \<open>decide_l_or_skip S \<le> \<Down> ?S (decide_or_skip S')\<close>
      apply -
      apply unify_Down_invs2+
      apply (simp only: set nf)
      apply ("match_\<Down>")
      subgoal
        apply (rule; rule)
        apply (clarsimp simp: twl_st_l_def)
        done
      subgoal by fast
      done
  qed
qed

lemma refinement_trans_eq:
  \<open>A = A' \<Longrightarrow> B = B' \<Longrightarrow> R' = R \<Longrightarrow> A \<le> \<Down> R B \<Longrightarrow> A' \<le> \<Down> R' B'\<close>
  by (auto simp: pw_ref_iff)

definition cdcl_twl_o_prog_l_pre where
  \<open>cdcl_twl_o_prog_l_pre S \<longleftrightarrow>
  (\<exists>S' . (S, S') \<in> twl_st_l None \<and>
     twl_struct_invs S' \<and>
     twl_stgy_invs S' \<and>
     twl_list_invs S)\<close>

definition cdcl_twl_o_prog_l :: \<open>'v twl_st_l \<Rightarrow> (bool \<times> 'v twl_st_l) nres\<close> where
  \<open>cdcl_twl_o_prog_l S =
    do {
      ASSERT(cdcl_twl_o_prog_l_pre S);
      do {
        if get_conflict_l S = None
        then decide_l_or_skip S
        else if count_decided (get_trail_l S) > 0
        then do {
          T \<leftarrow> skip_and_resolve_loop_l S;
          ASSERT(get_conflict_l T \<noteq> None \<and> get_conflict_l T \<noteq> Some {#});
          U \<leftarrow> backtrack_l T;
          RETURN (False, U)
        }
        else RETURN (True, S)
      }
    }
  \<close>


lemma twl_st_lE:
  \<open>(\<And>M N D NE UE WS Q. T = (M, N, D, NE, UE, WS, Q) \<Longrightarrow> P (M, N, D, NE, UE, WS, Q)) \<Longrightarrow> P T\<close>
  for T :: \<open>'a twl_st_l\<close>
  by (cases T) auto


lemma "weaken_\<Down>'": \<open>f \<le> \<Down> R' g \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> f \<le> \<Down> R g\<close>
  by (meson pw_ref_iff subset_eq)
(*
       clauses_to_update_l S = {#} \<and> literals_to_update_l S = {#} \<and> no_step cdcl_twl_cp S' \<and>
       twl_struct_invs S' \<and> twl_stgy_invs S' \<and>*) 
lemma cdcl_twl_o_prog_l_spec:
  \<open>(cdcl_twl_o_prog_l, cdcl_twl_o_prog) \<in>
    {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f
    \<langle>{((brk, T), (brk', T')). (T, T') \<in> twl_st_l None \<and> brk = brk' \<and> twl_list_invs T \<and>
      clauses_to_update_l T = {#}}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow>\<^sub>f ?I\<close> is \<open> _ \<in> ?R \<rightarrow>\<^sub>f \<langle>?J\<rangle>nres_rel\<close>)
proof -
  show ?thesis
     (is \<open>_ \<in> _ \<rightarrow>\<^sub>f \<langle>?I'\<rangle> nres_rel\<close>)
    supply [[goals_limit=3]]
    unfolding cdcl_twl_o_prog_l_def cdcl_twl_o_prog_def
      find_unassigned_lit_def fref_param1[symmetric]
    apply (refine_vcg
        decide_l_or_skip_spec[THEN fref_to_Down, THEN "weaken_\<Down>'"]
        skip_and_resolve_loop_l_spec[THEN fref_to_Down]
        backtrack_l_spec[THEN fref_to_Down]; remove_dummy_vars)
    subgoal for S S'
      unfolding cdcl_twl_o_prog_l_pre_def cdcl_twl_o_prog_pre_def by (rule exI[of _ S']) (force simp: twl_st_l)
    subgoal by auto
    subgoal unfolding cdcl_twl_o_prog_pre_def by auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding cdcl_twl_o_prog_pre_def by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


section \<open>Full Strategy\<close>

definition cdcl_twl_stgy_prog_l_inv :: \<open>'v twl_st_l \<Rightarrow> bool \<times> 'v twl_st_l  \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_stgy_prog_l_inv S\<^sub>0 \<equiv> \<lambda>(brk, T). \<exists>S\<^sub>0' T'. (T, T') \<in> twl_st_l None \<and>
       (S\<^sub>0, S\<^sub>0') \<in> twl_st_l None \<and>
       twl_struct_invs T' \<and>
        twl_stgy_invs T' \<and>
        (brk \<longrightarrow> final_twl_state T') \<and>
        cdcl_twl_stgy\<^sup>*\<^sup>* S\<^sub>0' T' \<and>
        clauses_to_update_l T = {#} \<and>
        (\<not>brk \<longrightarrow> get_conflict_l T = None)\<close>

definition cdcl_twl_stgy_prog_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>cdcl_twl_stgy_prog_l S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_prog_l_inv S\<^sub>0\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_l S;
          cdcl_twl_o_prog_l T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>

lemma cdcl_twl_stgy_prog_l_spec:
  \<open>(cdcl_twl_stgy_prog_l, cdcl_twl_stgy_prog) \<in>
    {(S, S'). (S, S') \<in> twl_st_l None  \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f
    \<langle>{(T, T'). (T, T') \<in> {(T, T'). (T, T') \<in> twl_st_l None \<and> twl_list_invs T} \<and> True}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow>\<^sub>f ?I\<close> is \<open> _ \<in> ?R \<rightarrow>\<^sub>f \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have R: \<open>(a, b) \<in> ?R \<Longrightarrow>
    ((False, a), (False, b)) \<in> {((brk, S), (brk', S')). brk = brk' \<and> (S, S') \<in> ?R}\<close>
    for a b by auto

  show ?thesis
    unfolding cdcl_twl_stgy_prog_l_def cdcl_twl_stgy_prog_def cdcl_twl_o_prog_l_spec
      fref_param1[symmetric] cdcl_twl_stgy_prog_l_inv_def
    apply (refine_rcg R cdcl_twl_o_prog_l_spec[THEN fref_to_Down, THEN "weaken_\<Down>'"]
        unit_propagation_outer_loop_l_spec[THEN fref_to_Down]; remove_dummy_vars)
    subgoal for S\<^sub>0 S\<^sub>0' T T'
      apply (rule exI[of _ S\<^sub>0'])
      apply (rule exI[of _ \<open>snd T\<close>])
      by (auto simp add: case_prod_beta)
    subgoal by auto
    subgoal by fastforce
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma refine_pair_to_SPEC:
  fixes f :: \<open>'s \<Rightarrow> 's nres\<close> and g :: \<open>'b \<Rightarrow> 'b nres\<close>
  assumes \<open>(f, g) \<in> {(S, S'). (S, S') \<in> H \<and> R S S'} \<rightarrow>\<^sub>f \<langle>{(S, S'). (S, S') \<in> H' \<and> P' S}\<rangle>nres_rel\<close>
    (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f ?I\<close>)
  assumes \<open>R S S'\<close> and [simp]: \<open>(S, S') \<in> H\<close>
  shows \<open>f S \<le> \<Down> {(S, S'). (S, S') \<in> H' \<and> P' S} (g S')\<close>
proof -
  have \<open>(f S, g S') \<in> ?I\<close>
    using assms unfolding fref_def nres_rel_def by auto
  then show ?thesis
    unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
    by auto
qed

definition cdcl_twl_stgy_prog_l_pre where
  \<open>cdcl_twl_stgy_prog_l_pre S S' \<longleftrightarrow>
    ((S, S') \<in> twl_st_l None \<and> twl_struct_invs S' \<and> twl_stgy_invs S' \<and>
      clauses_to_update_l S = {#} \<and> get_conflict_l S = None \<and> twl_list_invs S)\<close>

lemma cdcl_twl_stgy_prog_l_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_l_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_l S \<le> \<Down> (twl_st_l None) (conclusive_TWL_run S')\<close>
  apply (rule order_trans[OF cdcl_twl_stgy_prog_l_spec[THEN refine_pair_to_SPEC,
          of S S']])
  subgoal using assms unfolding cdcl_twl_stgy_prog_l_pre_def by auto
  subgoal using assms unfolding cdcl_twl_stgy_prog_l_pre_def by auto
  subgoal
    apply (rule ref_two_step)
     prefer 2
     apply (rule cdcl_twl_stgy_prog_spec)
    using assms unfolding cdcl_twl_stgy_prog_l_pre_def by (auto intro: conc_fun_R_mono)
  done

lemma cdcl_twl_stgy_prog_l_spec_final':
  assumes
    \<open>cdcl_twl_stgy_prog_l_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_l S \<le> \<Down> {(S, T). (S, T) \<in> twl_st_l None \<and> twl_list_invs S \<and>
       twl_struct_invs S' \<and> twl_stgy_invs S'} (conclusive_TWL_run S')\<close>
  apply (rule order_trans[OF cdcl_twl_stgy_prog_l_spec[THEN refine_pair_to_SPEC,
          of S S']])
  subgoal using assms unfolding cdcl_twl_stgy_prog_l_pre_def by auto
  subgoal using assms unfolding cdcl_twl_stgy_prog_l_pre_def by auto
  subgoal
    apply (rule ref_two_step)
     prefer 2
     apply (rule cdcl_twl_stgy_prog_spec)
    using assms unfolding cdcl_twl_stgy_prog_l_pre_def by (auto intro: conc_fun_R_mono)
  done

definition cdcl_twl_stgy_prog_break_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>cdcl_twl_stgy_prog_break_l S\<^sub>0 =
  do {
    b \<leftarrow> SPEC(\<lambda>_. True);
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(b, S). cdcl_twl_stgy_prog_l_inv S\<^sub>0 S\<^esup>
      (\<lambda>(b, brk, _). b \<and> \<not>brk)
      (\<lambda>(_, brk, S). do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        T \<leftarrow> cdcl_twl_o_prog_l T;
        b \<leftarrow> SPEC(\<lambda>_. True);
        RETURN (b, T)
      })
      (b, False, S\<^sub>0);
    if brk then RETURN T
    else cdcl_twl_stgy_prog_l T
  }\<close>

lemma cdcl_twl_stgy_prog_break_l_spec:
  \<open>(cdcl_twl_stgy_prog_break_l, cdcl_twl_stgy_prog_break) \<in>
    {(S, S'). (S, S') \<in> twl_st_l None  \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f
    \<langle>{(T, T'). (T, T') \<in> {(T, T'). (T, T') \<in> twl_st_l None \<and> twl_list_invs T} \<and> True}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow>\<^sub>f ?I\<close> is \<open> _ \<in> ?R \<rightarrow>\<^sub>f \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have R: \<open>(a, b) \<in> ?R \<Longrightarrow> (bb, bb') \<in> bool_rel \<Longrightarrow>
    ((bb, False, a), (bb', False, b)) \<in> {((b, brk, S), (b', brk', S')). b = b' \<and> brk = brk' \<and>
       (S, S') \<in> ?R}\<close>
    for a b bb bb' by auto

  show ?thesis
  supply [[goals_limit=1]]
    unfolding cdcl_twl_stgy_prog_break_l_def cdcl_twl_stgy_prog_break_def cdcl_twl_o_prog_l_spec
      fref_param1[symmetric] cdcl_twl_stgy_prog_l_inv_def
    apply (refine_rcg cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
        unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
        cdcl_twl_stgy_prog_l_spec[THEN fref_to_Down]; remove_dummy_vars)
    apply (rule R)
    subgoal by auto
    subgoal by auto
    subgoal for S\<^sub>0 S\<^sub>0' b b' T T'
      apply (rule exI[of _ S\<^sub>0'])
      apply (rule exI[of _ \<open>snd (snd T)\<close>])
      by (auto simp add: case_prod_beta)
    subgoal
     by auto
    subgoal by fastforce
    subgoal by (auto simp: twl_st_l)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma cdcl_twl_stgy_prog_break_l_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_l_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_break_l S \<le> \<Down> (twl_st_l None) (conclusive_TWL_run S')\<close>
  apply (rule order_trans[OF cdcl_twl_stgy_prog_break_l_spec[THEN refine_pair_to_SPEC,
          of S S']])
  subgoal using assms unfolding cdcl_twl_stgy_prog_l_pre_def by auto
  subgoal using assms unfolding cdcl_twl_stgy_prog_l_pre_def by auto
  subgoal
    apply (rule ref_two_step)
     prefer 2
     apply (rule cdcl_twl_stgy_prog_break_spec)
    using assms unfolding cdcl_twl_stgy_prog_l_pre_def
    by (auto intro: conc_fun_R_mono)
  done


definition cdcl_twl_stgy_prog_early_l :: \<open>'v twl_st_l \<Rightarrow> (bool \<times> 'v twl_st_l) nres\<close> where
  \<open>cdcl_twl_stgy_prog_early_l S\<^sub>0 =
  do {
    b \<leftarrow> SPEC(\<lambda>_. True);
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(b, S). cdcl_twl_stgy_prog_l_inv S\<^sub>0 S\<^esup>
      (\<lambda>(b, brk, _). b \<and> \<not>brk)
      (\<lambda>(_, brk, S). do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        T \<leftarrow> cdcl_twl_o_prog_l T;
        b \<leftarrow> SPEC(\<lambda>_. True);
        RETURN (b, T)
      })
      (b, False, S\<^sub>0);
    RETURN (brk, T)
  }\<close>

lemma cdcl_twl_stgy_prog_early_l_spec:
  \<open>(cdcl_twl_stgy_prog_early_l, cdcl_twl_stgy_prog_early) \<in>
    {(S, S'). (S, S') \<in> twl_st_l None  \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f
    \<langle>bool_rel \<times>\<^sub>r {(T, T'). (T, T') \<in> {(T, T'). (T, T') \<in> twl_st_l None \<and> twl_list_invs T} \<and> True}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow>\<^sub>f ?I\<close> is \<open> _ \<in> ?R \<rightarrow>\<^sub>f \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have R: \<open>(a, b) \<in> ?R \<Longrightarrow> (bb, bb') \<in> bool_rel \<Longrightarrow>
    ((bb, False, a), (bb', False, b)) \<in> {((b, brk, S), (b', brk', S')). b = b' \<and> brk = brk' \<and>
       (S, S') \<in> ?R}\<close>
    for a b bb bb' by auto

  show ?thesis
  supply [[goals_limit=1]]
    unfolding cdcl_twl_stgy_prog_early_l_def cdcl_twl_stgy_prog_early_def cdcl_twl_o_prog_l_spec
      fref_param1[symmetric] cdcl_twl_stgy_prog_l_inv_def
    apply (refine_rcg cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
        unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
        cdcl_twl_stgy_prog_l_spec[THEN fref_to_Down]; remove_dummy_vars)
    apply (rule R)
    subgoal by auto
    subgoal by auto
    subgoal for S\<^sub>0 S\<^sub>0' b b' T T'
      apply (rule exI[of _ S\<^sub>0'])
      apply (rule exI[of _ \<open>snd (snd T)\<close>])
      by (auto simp add: case_prod_beta)
    subgoal
     by auto
    subgoal by fastforce
    subgoal by (auto simp: twl_st_l)
    subgoal by auto
    subgoal by auto
    done
qed

lemma refine_pair_to_SPEC2:
  fixes f :: \<open>'s \<Rightarrow>  _ nres\<close> and g :: \<open>'b \<Rightarrow> (_) nres\<close>
  assumes \<open>(f, g) \<in> {(S, S'). (S, S') \<in> H \<and> R S S'} \<rightarrow>\<^sub>f \<langle>Id \<times>\<^sub>r {(S, S'). (S, S') \<in> H' \<and> P' S}\<rangle>nres_rel\<close>
    (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f ?I\<close>)
  assumes \<open>R S S'\<close> and [simp]: \<open>(S, S') \<in> H\<close>
  shows \<open>f S \<le> \<Down> (Id \<times>\<^sub>r {(S, S'). (S, S') \<in> H' \<and> P' S}) (g S')\<close>
proof -
  have \<open>(f S, g S') \<in> ?I\<close>
    using assms unfolding fref_def nres_rel_def by auto
  then show ?thesis
    unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
    by auto
qed

lemma cdcl_twl_stgy_prog_early_l_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_l_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_early_l S \<le> \<Down> (bool_rel \<times>\<^sub>r twl_st_l None) (partial_conclusive_TWL_run S')\<close>
  apply (rule order_trans[OF cdcl_twl_stgy_prog_early_l_spec[THEN refine_pair_to_SPEC2,
          of S S']])
  subgoal using assms unfolding cdcl_twl_stgy_prog_l_pre_def by auto
  subgoal using assms unfolding cdcl_twl_stgy_prog_l_pre_def by auto
  subgoal
    apply (rule ref_two_step)
     prefer 2
     apply (rule cdcl_twl_stgy_prog_early_spec)
    using assms unfolding cdcl_twl_stgy_prog_l_pre_def
    by (auto intro: conc_fun_R_mono)
  done

end
