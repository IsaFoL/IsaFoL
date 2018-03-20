theory Watched_Literals_List
  imports Watched_Literals_Algorithm CDCL.DPLL_CDCL_W_Implementation
  "HOL-Library.Finite_Map"
begin

lemma mset_take_mset_drop_mset: \<open>(\<lambda>x. mset (take 2 x) + mset (drop 2 x)) = mset\<close>
  unfolding mset_append[symmetric] append_take_drop_id ..
lemma mset_take_mset_drop_mset': \<open>mset (take 2 x) + mset (drop 2 x) = mset x\<close>
  unfolding mset_append[symmetric] append_take_drop_id ..


section \<open>Second Refinement: Lists as Clause\<close>

subsection \<open>Types\<close>
type_synonym 'v clauses_to_update_l = \<open>nat multiset\<close>

type_synonym 'v clause_l = \<open>'v literal list\<close>
type_synonym 'v clauses_l = \<open>(nat, ('v clause_l \<times> bool)) fmap\<close>
type_synonym 'v cconflict = \<open>'v clause option\<close>
type_synonym 'v cconflict_l = \<open>'v literal list option\<close>

type_synonym 'v twl_st_l =
  \<open>('v, nat) ann_lits \<times> 'v clauses_l \<times>
    'v cconflict \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses_to_update_l \<times> 'v lit_queue\<close>

fun clauses_to_update_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses_to_update_l\<close> where
  \<open>clauses_to_update_l (_, _, _, _, _, WS, _) = WS\<close>

fun get_trail_l :: \<open>'v twl_st_l \<Rightarrow> ('v, nat) ann_lit list\<close> where
  \<open>get_trail_l (M, _, _, _, _, _, _) = M\<close>

fun set_clauses_to_update_l :: \<open>'v clauses_to_update_l \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>set_clauses_to_update_l WS (M, N, D, NE, UE, _, Q) = (M, N, D, NE, UE, WS, Q)\<close>

fun literals_to_update_l :: \<open>'v twl_st_l \<Rightarrow> 'v clause\<close> where
  \<open>literals_to_update_l (_, _, _, _, _, _, Q) = Q\<close>

fun set_literals_to_update_l :: \<open>'v clause \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>set_literals_to_update_l Q (M, N, D, NE, UE, WS, _) = (M, N, D, NE, UE, WS, Q)\<close>

fun get_conflict_l :: \<open>'v twl_st_l \<Rightarrow> 'v cconflict\<close> where
  \<open>get_conflict_l (_, _, D, _, _, _, _) = D\<close>

fun get_clauses_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses_l\<close> where
  \<open>get_clauses_l (M, N, D, NE, UE, WS, Q) = N\<close>

fun get_unit_clauses_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_clauses_l (M, N, D, NE, UE, WS, Q) = NE + UE\<close>

fun get_unit_init_clauses_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses\<close> where
\<open>get_unit_init_clauses_l (M, N, D, NE, UE, WS, Q) = NE\<close>

fun get_unit_learned_clauses_l :: \<open>'v twl_st_l \<Rightarrow> 'v clauses\<close> where
\<open>get_unit_learned_clauses_l (M, N, D, NE, UE, WS, Q) = UE\<close>

fun get_init_clauses :: \<open>'v twl_st \<Rightarrow> 'v twl_clss\<close> where
  \<open>get_init_clauses (M, N, U, D, NE, UE, WS, Q) = N\<close>

fun get_unit_init_clauses :: \<open>'v twl_st_l \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_init_clauses (M, N, D, NE, UE, WS, Q) = NE\<close>

fun get_unit_learned_clss :: \<open>'v twl_st_l \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_learned_clss (M, N, D, NE, UE, WS, Q) = UE\<close>

lemma state_decomp_to_state:
  \<open>(case S of (M, N, U, D, NE, UE, WS, Q) \<Rightarrow> P M N U D NE UE WS Q) =
     P (get_trail S) (get_init_clauses S) (get_learned_clss S) (get_conflict S)
        (unit_init_clauses S) (get_init_learned_clss S)
        (clauses_to_update S)
        (literals_to_update S)\<close>
  by (cases S) auto


lemma state_decomp_to_state_l:
  \<open>(case S of (M, N, D, NE, UE, WS, Q) \<Rightarrow> P M N D NE UE WS Q) =
     P (get_trail_l S) (get_clauses_l S) (get_conflict_l S)
        (get_unit_init_clauses_l S) (get_unit_learned_clauses_l S)
        (clauses_to_update_l S)
        (literals_to_update_l S)\<close>
  by (cases S) auto

definition set_conflict' :: \<open>'v clause option \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>set_conflict' = (\<lambda>C (M, N, U, D, NE, UE, WS, Q). (M, N, U, C, NE, UE, WS, Q))\<close>

abbreviation watched_l :: \<open>'a clause_l \<Rightarrow> 'a clause_l\<close> where
  \<open>watched_l l \<equiv> take 2 l\<close>

abbreviation unwatched_l :: \<open>'a clause_l \<Rightarrow> 'a clause_l\<close>  where
  \<open>unwatched_l l \<equiv> drop 2 l\<close>

fun twl_clause_of :: \<open>'a clause_l \<Rightarrow> 'a clause twl_clause\<close> where
  \<open>twl_clause_of l = TWL_Clause (mset (watched_l l)) (mset (unwatched_l l))\<close>

fun clause_of :: \<open>'a::plus twl_clause \<Rightarrow> 'a\<close> where
  \<open>clause_of (TWL_Clause W UW) = W + UW\<close>

abbreviation clause_in :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> 'v clause_l\<close> (infix "\<propto>" 101) where
  \<open>N \<propto> i \<equiv> fst (the (fmlookup N i))\<close>

abbreviation clause_upd :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> 'v clause_l \<Rightarrow> 'v clauses_l\<close>  where
  \<open>clause_upd N i C \<equiv> fmupd i (C, snd (the (fmlookup N i))) N\<close>

text \<open>Taken from \<^term>\<open>fun_upd\<close>.\<close>
nonterminal updclsss and updclss

syntax
  "_updclss" :: "'a clauses_l \<Rightarrow> 'a \<Rightarrow> updclss"             ("(2_ \<hookrightarrow>/ _)")
  ""         :: "updbind \<Rightarrow> updbinds"             ("_")
  "_updclsss":: "updclss \<Rightarrow> updclsss \<Rightarrow> updclsss" ("_,/ _")
  "_Updateclss"  :: "'a \<Rightarrow> updclss \<Rightarrow> 'a"            ("_/'((_)')" [1000, 0] 900)

translations
  "_Updateclss f (_updclsss b bs)" \<rightleftharpoons> "_Updateclss (_Updateclss f b) bs"
  "f(x \<hookrightarrow> y)" \<rightleftharpoons> "CONST clause_upd f x y"

fun convert_lit :: \<open>'v clauses_l \<Rightarrow> ('v, nat) ann_lit \<Rightarrow> ('v, 'v clause) ann_lit\<close> where
  \<open>convert_lit N (Decided K) = Decided K\<close>
| \<open>convert_lit N (Propagated K j) =
  (if j = 0 then Propagated K {#K#} else Propagated K (mset (N \<propto> j)))\<close>

definition convert_lits_l :: \<open>'v clauses_l \<Rightarrow> ('v, nat) ann_lits \<Rightarrow> ('v, 'v clause) ann_lits\<close> where
  \<open>convert_lits_l N M = map (convert_lit N) M\<close>

lemma convert_lits_l_nil[simp]: \<open>convert_lits_l N [] = []\<close>
  by (auto simp: convert_lits_l_def)

lemma convert_lits_l_cons[simp]: \<open>convert_lits_l N (L # M) = convert_lit N L # convert_lits_l N M\<close>
  by (auto simp: convert_lits_l_def)

lemma convert_lits_l_append[simp]:
  \<open>convert_lits_l N (M @ M') = convert_lits_l N M @ convert_lits_l N M'\<close>
  by (auto simp: convert_lits_l_def)

lemma convert_lits_l_cong:
  \<open>M = M' \<Longrightarrow> (\<And>L C. Propagated L C \<in> set M \<Longrightarrow> mset (N \<propto> C) = mset (N' \<propto> C)) \<Longrightarrow>
    convert_lits_l N M = convert_lits_l N' M'\<close>
    unfolding convert_lits_l_def
    apply auto
    subgoal for L
      by (cases L) auto
    done

lemma get_all_ann_decomposition_convert_lits_l:
  shows \<open>get_all_ann_decomposition (convert_lits_l N M) =
    map (\<lambda>(M, M'). (convert_lits_l N M, convert_lits_l N M')) (get_all_ann_decomposition M)\<close>
  apply (induction M rule: ann_lit_list_induct)
  subgoal by auto
  subgoal by auto
  subgoal for L m M by (cases \<open>get_all_ann_decomposition M\<close>) auto
  done

lemma get_clauses_l_set_clauses_to_update_l[simp]:
  \<open>get_clauses_l (set_clauses_to_update_l WC S) = get_clauses_l S\<close>
  by (cases S) auto

lemma get_trail_l_set_clauses_to_update_l[simp]:
  \<open>get_trail_l (set_clauses_to_update_l WC S) = get_trail_l S\<close>
  by (cases S) auto

lemma get_trail_set_clauses_to_update[simp]:
  \<open>get_trail (set_clauses_to_update WC S) = get_trail S\<close>
  by (cases S) auto

abbreviation resolve_cls_l where
  \<open>resolve_cls_l L D' E \<equiv> union_mset_list (remove1 (-L) D') (remove1 L E)\<close>

lemma mset_resolve_cls_l_resolve_cls[iff]:
  \<open>mset (resolve_cls_l L D' E) = cdcl\<^sub>W_restart_mset.resolve_cls L (mset D') (mset E)\<close>
  by (auto simp: union_mset_list[symmetric])

lemma resolve_cls_l_nil_iff:
  \<open>resolve_cls_l L D' E = [] \<longleftrightarrow> cdcl\<^sub>W_restart_mset.resolve_cls L (mset D') (mset E) = {#}\<close>
  by (metis mset_resolve_cls_l_resolve_cls mset_zero_iff)


lemma lit_of_convert_lit[iff]:
  \<open>lit_of (convert_lit N x) = lit_of x\<close>
  by (cases x) auto

lemma lit_of_o_convert_lit[iff]:
  \<open>lit_of o (convert_lit N) = lit_of\<close>
  by auto

lemma is_decided_convert_lit[iff]: \<open>is_decided (convert_lit N L) = is_decided L\<close>
  by (cases L) auto

lemma is_decided_o_convert_lit[iff]: \<open>is_decided \<circ> (convert_lit N) = is_decided\<close>
  by auto

lemma no_dup_convert_lits_l[iff]: \<open>no_dup (convert_lits_l N M) \<longleftrightarrow> no_dup M\<close>
  by (auto simp: defined_lit_map comp_def no_dup_def convert_lits_l_def)

lemma lits_of_convert_lit[iff]: \<open>lits_of (convert_lit N ` set M) = lits_of_l M\<close>
  by (induction M) auto

lemma lits_of_l_convert_lits_l[simp]: \<open>lits_of_l (convert_lits_l N M) = lits_of_l M\<close>
  by (induction M) auto

lemma convert_lits_l_true_annot[simp]: \<open>convert_lits_l N M \<Turnstile>a A \<longleftrightarrow> M \<Turnstile>a A\<close>
  unfolding true_annot_def by auto

lemma convert_lits_l_true_annots[simp]: \<open>convert_lits_l N M \<Turnstile>as A \<longleftrightarrow> M \<Turnstile>as A\<close>
  unfolding true_annots_def by auto

lemma defined_lit_convert_lits_l[iff]: \<open>defined_lit (convert_lits_l N M) = defined_lit M\<close>
  by (auto simp: defined_lit_map image_image convert_lits_l_def)

lemma get_level_convert_lits_l[simp]: \<open>get_level (convert_lits_l N M) = get_level M\<close>
  apply (rule ext)
  by (induction M) (auto simp: get_level_def convert_lits_l_def)

lemma get_level_convert_lits_l2[simp]:
  \<open>get_level (convert_lits_l N M') K = get_level M' K\<close>
  using get_level_convert_lits_l[of N M'] by simp

lemma count_decided_convert_lits_l[simp]:
  \<open>count_decided (convert_lits_l N M) = count_decided M\<close>
  by (auto simp: count_decided_def convert_lits_l_def)

lemma get_maximum_level_convert_lits_l[simp]:
  \<open>get_maximum_level (convert_lits_l N M) = get_maximum_level M\<close>
  unfolding get_maximum_level_def by auto

lemma lit_of_hd_convert_lits_l[simp]: \<open>M \<noteq> [] \<Longrightarrow> lit_of (hd (convert_lits_l N M)) = lit_of (hd M)\<close>
  by (cases M) auto

lemma convert_lits_l_Nil_off[iff]: \<open>convert_lits_l b a = [] \<longleftrightarrow> a = []\<close>
  by (auto simp: convert_lits_l_def)

lemma is_decided_hd_convert_lits_l[simp]:
  \<open>M \<noteq> [] \<Longrightarrow> is_decided (hd (convert_lits_l N M)) = is_decided (hd M)\<close>
  by (cases M) auto

lemma is_proped_convert_lit[simp]: \<open>is_proped (convert_lit b a) \<longleftrightarrow> is_proped a\<close>
  by (cases a) auto

text \<open>Roughly the same as \<^term>\<open>ran\<close>, but with duplication and works only on finite domains.\<close>
abbreviation mset_fset :: \<open>'a fset \<Rightarrow> 'a multiset\<close> where
  \<open>mset_fset N \<equiv> mset_set (fset N)\<close>

definition fset_mset :: \<open>'a multiset \<Rightarrow> 'a fset\<close> where
  \<open>fset_mset N \<equiv> Abs_fset (set_mset N)\<close>

lemma fset_mset_mset_fset: \<open>fset_mset (mset_fset N) = N\<close>
  by (auto simp: fset.fset_inverse fset_mset_def)


lemma mset_fset_fset_mset[simp]:
  \<open>mset_fset (fset_mset N) = remdups_mset N\<close>
  by (auto simp: fset.fset_inverse fset_mset_def Abs_fset_inverse
      remdups_mset_def)

lemma in_mset_fset_fmember[simp]: \<open>x \<in># mset_fset N \<longleftrightarrow> x |\<in>| N\<close>
  by (auto simp: fmember.rep_eq)

lemma in_fset_mset_mset[simp]: \<open>x |\<in>| fset_mset N \<longleftrightarrow> x \<in># N\<close>
  by (auto simp: fmember.rep_eq fset_mset_def Abs_fset_inverse)

definition dom_m where
  \<open>dom_m N = mset_fset (fmdom N)\<close>

definition ran_m where
  \<open>ran_m N =  the `# fmlookup N `# dom_m N\<close>

abbreviation ran_mf :: \<open>'v clauses_l \<Rightarrow> 'v clause_l multiset\<close> where
  \<open>ran_mf N \<equiv> fst `# ran_m N\<close>

abbreviation learned_clss_l :: \<open>'v clauses_l \<Rightarrow> ('v clause_l \<times> bool) multiset\<close> where
  \<open>learned_clss_l N \<equiv> {#C \<in># ran_m N. \<not>snd C#}\<close>

abbreviation learned_clss_lf :: \<open>'v clauses_l \<Rightarrow> 'v clause_l multiset\<close> where
  \<open>learned_clss_lf N \<equiv> fst `# learned_clss_l N\<close>

abbreviation init_clss_l :: \<open>'v clauses_l \<Rightarrow> ('v clause_l \<times> bool) multiset\<close> where
  \<open>init_clss_l N \<equiv> {#C \<in># ran_m N. snd C#}\<close>

abbreviation init_clss_lf :: \<open>'v clauses_l \<Rightarrow> 'v clause_l multiset\<close> where
  \<open>init_clss_lf N \<equiv> fst `# init_clss_l N\<close>

abbreviation all_clss_l :: \<open>'v clauses_l \<Rightarrow> ('v clause_l \<times> bool) multiset\<close> where
  \<open>all_clss_l N \<equiv> init_clss_l N + learned_clss_l N\<close>

lemma all_clss_l_ran_m[simp]:
  \<open>all_clss_l N = ran_m N\<close>
  by (metis multiset_partition)

abbreviation all_clss_lf :: \<open>'v clauses_l \<Rightarrow> 'v clause_l multiset\<close> where
  \<open>all_clss_lf N \<equiv> init_clss_lf N + learned_clss_lf N\<close>

lemma all_clss_lf_ran_m: \<open>all_clss_lf N = fst `# ran_m N\<close>
  by (metis (no_types) image_mset_union multiset_partition)

abbreviation irred :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>irred N C \<equiv> snd (the (fmlookup N C))\<close>

lemma ran_m_ran: \<open>fset_mset (ran_m N) = fmran N\<close>
  unfolding ran_m_def ran_def
  apply (auto simp: fmlookup_ran_iff dom_m_def elim!: fmdomE)
   apply (metis fmdomE notin_fset option.sel)
  by (metis (no_types, lifting) fmdomI fmember.rep_eq image_iff option.sel)

lemma dom_m_fmdrop[simp]: \<open>dom_m (fmdrop C N) = remove1_mset C (dom_m N)\<close>
  unfolding dom_m_def
  by (cases \<open>C |\<in>| fmdom N\<close>)
    (auto simp: mset_set.remove fmember.rep_eq)

lemma dom_m_fmupd[simp]: \<open>dom_m (fmupd k C N) = add_mset k (remove1_mset k (dom_m N))\<close>
  unfolding dom_m_def
  by (cases \<open>k |\<in>| fmdom N\<close>)
    (auto simp: mset_set.remove fmember.rep_eq mset_set.insert
    mset_set.insert_remove)
lemma distinct_mset_dom: \<open>distinct_mset (dom_m N)\<close>
  by (simp add: distinct_mset_mset_set dom_m_def)

lemma in_dom_m_lookup_iff: \<open>C \<in># dom_m N' \<longleftrightarrow> fmlookup N' C \<noteq> None\<close>
  by (auto simp: dom_m_def fmdom.rep_eq)

lemma in_dom_in_ran_m[simp]: \<open>i \<in># dom_m N \<Longrightarrow> the (fmlookup N i) \<in># ran_m N\<close>
  by (auto simp: ran_m_def)

lemma ran_m_clause_upd:
  assumes
    NC: \<open>C \<in># dom_m N\<close>
  shows \<open>ran_m (N(C \<hookrightarrow> C')) =
         add_mset (C', irred N C) (remove1_mset (N \<propto> C, irred N C) (ran_m N))\<close>
proof -
  define N' where
    \<open>N' = fmdrop C N\<close>
  have N_N': \<open>dom_m N = add_mset C (dom_m N')\<close>
    using NC unfolding N'_def by auto
  have \<open>C \<notin># dom_m N'\<close>
    using NC distinct_mset_dom[of N] unfolding N_N' by auto
  then show ?thesis
    by (auto simp: N_N' ran_m_def mset_set.insert_remove image_mset_remove1_mset_if
      intro!: image_mset_cong)
qed

lemma ran_m_mapsto_upd:
  assumes
    NC: \<open>C \<in># dom_m N\<close>
  shows \<open>ran_m (fmupd C C' N) =
         add_mset C' (remove1_mset (N \<propto> C, irred N C) (ran_m N))\<close>
proof -
  define N' where
    \<open>N' = fmdrop C N\<close>
  have N_N': \<open>dom_m N = add_mset C (dom_m N')\<close>
    using NC unfolding N'_def by auto
  have \<open>C \<notin># dom_m N'\<close>
    using NC distinct_mset_dom[of N] unfolding N_N' by auto
  then show ?thesis
    by (auto simp: N_N' ran_m_def mset_set.insert_remove image_mset_remove1_mset_if
      intro!: image_mset_cong)
qed

lemma ran_m_mapsto_upd_notin:
  assumes
    NC: \<open>C \<notin># dom_m N\<close>
  shows \<open>ran_m (fmupd C C' N) = add_mset C' (ran_m N)\<close>
  using NC
  by (auto simp: ran_m_def mset_set.insert_remove image_mset_remove1_mset_if
      intro!: image_mset_cong split: if_splits)

lemma Ball_ran_m_dom:
  \<open>(\<forall>x\<in>#ran_m N. P (fst x)) \<longleftrightarrow> (\<forall>x\<in>#dom_m N. P (N \<propto> x))\<close>
  by (auto simp: ran_m_def)

lemma Ball_ran_m_dom_struct_wf:
  \<open>(\<forall>x\<in>#ran_m N. struct_wf_twl_cls (twl_clause_of (fst x))) \<longleftrightarrow>
     (\<forall>x\<in># dom_m N. struct_wf_twl_cls (twl_clause_of (N \<propto> x)))\<close>
  by (rule Ball_ran_m_dom)

definition twl_st_l   :: \<open>_ \<Rightarrow> ('v twl_st_l \<times> 'v twl_st) set\<close> where
\<open>twl_st_l L =
  {((M, N, C, NE, UE, WS, Q),  (M', N', U', C', NE', UE', WS', Q')).
      M' = convert_lits_l N M \<and>
      N' = twl_clause_of `# init_clss_lf N \<and>
      U' = twl_clause_of `# learned_clss_lf N \<and>
      C' = C \<and>
      NE' = NE \<and>
      UE' = UE \<and>
      WS' = (case L of None \<Rightarrow> {#} | Some L \<Rightarrow> image_mset (\<lambda>j. (L, twl_clause_of (N \<propto> j))) WS) \<and>
      Q' = Q
  }\<close>

lemma clss_state\<^sub>W_of[twl_st]:
  assumes \<open>(S, R) \<in> twl_st_l L\<close>
  shows
  \<open>init_clss (state\<^sub>W_of R) = mset `# (init_clss_lf (get_clauses_l S)) +
     get_unit_init_clauses_l S\<close>
  \<open>learned_clss (state\<^sub>W_of R) = mset `# (learned_clss_lf (get_clauses_l S)) +
     get_unit_learned_clauses_l S\<close>
 using assms
 by (cases S; cases L; auto simp: init_clss.simps learned_clss.simps twl_st_l_def
   mset_take_mset_drop_mset'; fail)+

named_theorems twl_st_l \<open>Conversions simp rules\<close>

lemma [twl_st_l]:
  assumes \<open>(S, T) \<in> twl_st_l L\<close>
  shows
    \<open>get_trail T = convert_lits_l (get_clauses_l S) (get_trail_l S)\<close> and
    \<open>get_clauses T = twl_clause_of `# fst `# ran_m (get_clauses_l S)\<close> and
    \<open>get_conflict T = get_conflict_l S\<close> and
    \<open>L = None \<Longrightarrow> clauses_to_update T = {#}\<close>
    \<open>L \<noteq> None \<Longrightarrow> clauses_to_update T =
        (\<lambda>j. (the L, twl_clause_of (get_clauses_l S \<propto> j))) `# clauses_to_update_l S\<close> and
    \<open>literals_to_update T = literals_to_update_l S\<close>
    \<open>backtrack_lvl (state\<^sub>W_of T) = count_decided (get_trail_l S)\<close>
    \<open>unit_clss T = get_unit_clauses_l S\<close>
   \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of T) = mset `# ran_mf (get_clauses_l S) + get_unit_clauses_l S\<close>
  using assms unfolding twl_st_l_def all_clss_lf_ran_m[symmetric]
  by (auto split: option.splits simp: trail.simps clauses_def mset_take_mset_drop_mset')

lemma clauses_to_update_l_set_clauses_to_update_l:
  \<open>clauses_to_update_l (set_clauses_to_update_l WS S) = WS\<close>
  by (cases S) auto

lemma get_conflict_l_set_clauses_to_update_l[twl_st_l]:
  \<open>get_conflict_l (set_clauses_to_update_l Cs S) = get_conflict_l S\<close>
  by (cases S) auto

lemma hd_get_trail_twl_st_of_get_trail_l:
  \<open>(S, T) \<in> twl_st_l L \<Longrightarrow> get_trail_l S \<noteq> [] \<Longrightarrow>
    lit_of (hd (get_trail T)) = lit_of (hd (get_trail_l S))\<close>
  by (cases S; cases \<open>get_trail_l S\<close>) (auto simp: twl_st_l_def)

fun equality_except_trail :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
\<open>equality_except_trail (M, N, D, NE, UE, WS, Q) (M', N', D', NE', UE', WS', Q') \<longleftrightarrow>
    N = N' \<and> D = D' \<and> NE = NE' \<and> UE = UE' \<and> WS = WS' \<and> Q = Q'\<close>

fun equality_except_conflict_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l \<Rightarrow> bool\<close> where
\<open>equality_except_conflict_l (M, N, D, NE, UE, WS, Q) (M', N', D', NE', UE', WS', Q') \<longleftrightarrow>
    M = M' \<and> N = N' \<and> NE = NE' \<and> UE = UE' \<and> WS = WS' \<and> Q = Q'\<close>

fun equality_except_conflict :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
\<open>equality_except_conflict (M, N, U, D, NE, UE, WS, Q) (M', N', U', D', NE', UE', WS', Q') \<longleftrightarrow>
    M = M' \<and> N = N' \<and> U = U' \<and> NE = NE' \<and> UE = UE' \<and> WS = WS' \<and> Q = Q'\<close>

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
      get_unit_learned_clauses_l S = get_unit_learned_clauses_l T \<and>
      literals_to_update_l S = literals_to_update_l T \<and>
      clauses_to_update_l S = clauses_to_update_l T\<close>
  by (cases S, cases T) auto

lemma equality_except_conflict_alt_def:
 \<open>equality_except_conflict S T \<longleftrightarrow>
   get_trail S = get_trail T \<and> get_init_clauses S = get_init_clauses T \<and>
      get_learned_clss S = get_learned_clss T \<and>
      get_init_learned_clss S = get_init_learned_clss T \<and>
      unit_init_clauses S = unit_init_clauses T \<and>
      literals_to_update S = literals_to_update T \<and>
      clauses_to_update S = clauses_to_update T\<close>
  by (cases S, cases T) auto


subsection \<open>Additional Invariants and Definitions\<close>

definition twl_list_invs where
  \<open>twl_list_invs S \<longleftrightarrow>
    (\<forall>C \<in># clauses_to_update_l S. C \<in># dom_m (get_clauses_l S)) \<and>
    0 \<notin># dom_m (get_clauses_l S) \<and>
    (\<forall>L C. Propagated L C \<in> set (get_trail_l S) \<longrightarrow> (C > 0 \<longrightarrow> C \<in># dom_m (get_clauses_l S) \<and>
      (C > 0 \<longrightarrow> L \<in> set (watched_l (get_clauses_l S \<propto> C)) \<and> L = get_clauses_l S \<propto> C ! 0))) \<and>
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

definition find_unwatched_l where
  \<open>find_unwatched_l M C = SPEC (\<lambda>(found).
      (found = None \<longleftrightarrow> (\<forall>L\<in>set (unwatched_l C). -L \<in> lits_of_l M)) \<and>
      (\<forall>j. found = Some j \<longrightarrow> (j < length C \<and> (undefined_lit M (C!j) \<or> C!j \<in> lits_of_l M) \<and> j \<ge> 2)))\<close>


definition set_conflict_l :: \<open>'v clause_l \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>set_conflict_l = (\<lambda>C (M, N, D, NE, UE, WS, Q). (M, N, Some (mset C), NE, UE, {#}, {#}))\<close>

definition propagate_lit_l :: \<open>'v literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>propagate_lit_l = (\<lambda>L' C i (M, N, D, NE, UE, WS, Q).
      let N = N(C \<hookrightarrow> (swap (N \<propto> C) 0 (Suc 0 - i))) in
      (Propagated L' C # M, N, D, NE, UE, WS, add_mset (-L') Q))\<close>

definition update_clause_l :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>update_clause_l = (\<lambda>C i f (M, N, D, NE, UE, WS, Q). do {
       let N' = N (C \<hookrightarrow> (swap (N\<propto>C) i f));
       RETURN (M, N', D, NE, UE, WS, Q)
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

definition unit_propagation_inner_loop_body_l :: \<open>'v literal \<Rightarrow> nat \<Rightarrow>
  'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>unit_propagation_inner_loop_body_l L C S = do {
      ASSERT(unit_propagation_inner_loop_body_l_inv L C S);
      let i = (if (get_clauses_l S \<propto> C) ! 0 = L then 0 else 1);
      let L' = (get_clauses_l S \<propto> C) ! (1 - i);
      let val_L' = polarity (get_trail_l S) L';
      if val_L' = Some True
      then RETURN S
      else do {
          f \<leftarrow> find_unwatched_l (get_trail_l S) (get_clauses_l S \<propto> C);
          case f of
            None \<Rightarrow>
               if val_L' = Some False
               then RETURN (set_conflict_l (get_clauses_l S \<propto> C) S)
               else RETURN (propagate_lit_l L' C i S)
          | Some f \<Rightarrow> do {
               ASSERT(f < length (get_clauses_l S \<propto> C));
               update_clause_l C i f S
            }
       }
   }\<close>

lemma refine_add_invariants:
  assumes
    \<open>(f S) \<le> SPEC(\<lambda>S'. Q S')\<close> and
    \<open>y \<le> \<Down> {(S, S'). P S S'} (f S)\<close>
  shows \<open>y \<le> \<Down> {(S, S'). P S S' \<and> Q S'} (f S)\<close>
  using assms unfolding pw_le_iff pw_conc_inres pw_conc_nofail by force

context conflict_driven_clause_learning\<^sub>W
begin
(* TODO Move + use instead of distinct_cdcl\<^sub>W_state_def *)
lemma distinct_cdcl\<^sub>W_state_alt_def:
  \<open>distinct_cdcl\<^sub>W_state S =
    ((\<forall>T. conflicting S = Some T \<longrightarrow> distinct_mset T) \<and>
     distinct_mset_mset (clauses S) \<and>
     (\<forall>L mark. Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset mark))\<close>
  unfolding distinct_cdcl\<^sub>W_state_def clauses_def
  by auto
end

lemma clauses_tuple[simp]:
  \<open>cdcl\<^sub>W_restart_mset.clauses (M, {#f x . x \<in># init_clss_l N#} + NE,
     {#f x . x \<in># learned_clss_l N#} + UE, D) = {#f x. x \<in># all_clss_l N#} + NE + UE\<close>
  by (auto simp: clauses_def simp del: all_clss_l_ran_m)

lemma valid_enqueued_alt_simps[simp]:
  \<open>valid_enqueued S \<longleftrightarrow>
    (\<forall>(L, C) \<in># clauses_to_update S. L \<in># watched C \<and> C \<in># get_clauses S \<and>
       -L \<in> lits_of_l (get_trail S) \<and> get_level (get_trail S) L = count_decided (get_trail S)) \<and>
     (\<forall>L \<in># literals_to_update S.
          -L \<in> lits_of_l (get_trail S) \<and> get_level (get_trail S) L = count_decided (get_trail S))\<close>
  by (cases S) auto

declare valid_enqueued.simps[simp del]

lemma set_clauses_simp[simp]:
  \<open>f ` {a. a \<in># ran_m N \<and> \<not> snd a} \<union> f ` {a. a \<in># ran_m N \<and> snd a} \<union> A =
   f ` {a. a \<in># ran_m N} \<union> A\<close>
  by auto

lemma twl_st_inv_alt_def:
  \<open>twl_st_inv S \<longleftrightarrow>
  (\<forall>C \<in># get_clauses S. struct_wf_twl_cls C) \<and>
  (\<forall>C \<in># get_clauses S. get_conflict S = None \<longrightarrow>
     \<not>twl_is_an_exception C (literals_to_update S) (clauses_to_update S) \<longrightarrow>
     (twl_lazy_update (get_trail S) C \<and> twl_inv (get_trail S) C)) \<and>
  (\<forall>C \<in># get_clauses S. get_conflict S = None \<longrightarrow>
     watched_literals_false_of_max_level (get_trail S) C)\<close>
  by (cases S) (auto simp: twl_st_inv.simps)

lemma init_clss_l_clause_upd:
  \<open>C \<in># dom_m N \<Longrightarrow> irred N C \<Longrightarrow>
   init_clss_l (N(C \<hookrightarrow> C')) =
     add_mset (C', irred N C) (remove1_mset (N \<propto> C, irred N C) (init_clss_l N))\<close>
  by (auto simp: ran_m_mapsto_upd)

lemma init_clss_l_mapsto_upd:
  \<open>C \<in># dom_m N \<Longrightarrow> irred N C \<Longrightarrow>
   init_clss_l (fmupd C (C', True) N) =
     add_mset (C', irred N C) (remove1_mset (N \<propto> C, irred N C) (init_clss_l N))\<close>
  by (auto simp: ran_m_mapsto_upd)

lemma learned_clss_l_mapsto_upd:
  \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow>
   learned_clss_l (fmupd C (C', False) N) =
      add_mset (C', irred N C) (remove1_mset (N \<propto> C, irred N C) (learned_clss_l N))\<close>
  by (auto simp: ran_m_mapsto_upd)

lemma init_clss_l_mapsto_upd_irrel: \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow>
  init_clss_l (fmupd C (C', False) N) = init_clss_l N\<close>
  by (auto simp: ran_m_mapsto_upd)

lemma init_clss_l_mapsto_upd_irrel_notin: \<open>C \<notin># dom_m N \<Longrightarrow>
  init_clss_l (fmupd C (C', False) N) = init_clss_l N\<close>
  by (auto simp: ran_m_mapsto_upd_notin)

lemma learned_clss_l_mapsto_upd_irrel: \<open>C \<in># dom_m N \<Longrightarrow> irred N C \<Longrightarrow>
  learned_clss_l (fmupd C (C', True) N) = learned_clss_l N\<close>
  by (auto simp: ran_m_mapsto_upd)

lemma learned_clss_l_mapsto_upd_notin: \<open>C \<notin># dom_m N \<Longrightarrow>
  learned_clss_l (fmupd C  (C', False) N) = add_mset (C', False) (learned_clss_l N)\<close>
  by (auto simp: ran_m_mapsto_upd_notin)

lemma in_ran_mf_clause_inI[intro]:
  \<open>C \<in># dom_m N \<Longrightarrow> i = irred N C \<Longrightarrow> (N \<propto> C, i) \<in># ran_m N\<close>
  by (auto simp: ran_m_def dom_m_def)

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
        \<Down> {(S, S''). (S, S'') \<in> twl_st_l (Some L) \<and> twl_list_invs S \<and> twl_stgy_invs S'' \<and>
             twl_struct_invs S''}
          (unit_propagation_inner_loop_body (L, twl_clause_of C')
             (set_clauses_to_update (clauses_to_update (S') - {#(L, twl_clause_of C')#}) S'))\<close>
    (is \<open>?A \<le> \<Down> _ ?B\<close>)
proof -
  let ?S = \<open>set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S\<close>
  obtain M N D NE UE WS Q where S: \<open>S = (M, N, D, NE, UE, WS, Q)\<close>
    by (cases S) auto

  have C_N_U: \<open>C \<in># dom_m (get_clauses_l S)\<close>
    using add_inv WS SS' by (auto simp: twl_st_l twl_list_invs_def)
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
    using struct_invs WS by (auto simp: twl_struct_invs_def)
  have
    w_q_inv: \<open>clauses_to_update_inv S'\<close> and
    dist: \<open>distinct_queued S'\<close> and
    no_dup: \<open>no_duplicate_queued S'\<close> and
    confl: \<open>get_conflict S' \<noteq> None \<Longrightarrow> clauses_to_update S' = {#} \<and> literals_to_update S' = {#}\<close>
    using struct_invs unfolding twl_struct_invs_def by fast+
  have n_d: \<open>no_dup ?M\<close> and confl_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of S')\<close>
    using cdcl_inv SS' unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: trail.simps comp_def twl_st_l twl_st)

  then have consistent: \<open>- L \<notin> lits_of_l ?M\<close> if \<open>L \<in> lits_of_l ?M\<close> for L
    using consistent_interp_def distinct_consistent_interp that by blast

  have cons_M: \<open>consistent_interp (lits_of_l ?M)\<close>
    using n_d distinct_consistent_interp by fast
  let ?C' = \<open>twl_clause_of C'\<close>
  have C'_N_U_or: \<open>?C' \<in># twl_clause_of `# (init_clss_lf ?N) \<or>
      ?C' \<in># twl_clause_of `# learned_clss_lf ?N\<close>
    using WS valid SS'
    unfolding union_iff[symmetric] image_mset_union[symmetric]  mset_append[symmetric]
    by (auto simp: twl_struct_invs_def twl_st_l
        split: prod.splits simp del: twl_clause_of.simps)
  have struct: \<open>struct_wf_twl_cls ?C'\<close>
    using C_N_U inv SS' WS valid unfolding valid_enqueued_alt_simps
    by (auto simp: twl_st_inv_alt_def twl_st_l Ball_ran_m_dom_struct_wf
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
  obtain WS' where WS'_def: \<open>?WS = add_mset C WS'\<close>
    using multi_member_split[OF WS] by auto
  then have WS'_def': \<open>WS = add_mset C WS'\<close>
    unfolding S by auto
  have L: \<open>L \<in> set (watched_l C')\<close> and uL_M: \<open>-L \<in> lits_of_l (get_trail_l S)\<close>
    using valid SS' by (auto simp: twl_st_l WS'_def)
  have C'_i[simp]: \<open>C'!i = L\<close>
    using L two_le_length_C by (auto simp: take_2_if i_def split: if_splits)
  then have [simp]: \<open>?N\<propto>C!i = L\<close>
    by auto
  have C_0: \<open>C > 0\<close> and C_neq_0[iff]: \<open>C \<noteq> 0\<close>
    using assms(3,5) unfolding twl_list_invs_def by (auto dest!: multi_member_split)

  have pre_inv: \<open>unit_propagation_inner_loop_body_l_inv L C ?S\<close>
    unfolding unit_propagation_inner_loop_body_l_inv_def
  proof (rule exI[of _ S'], intro conjI)
    have S_readd_C_S: \<open>set_clauses_to_update_l (clauses_to_update_l ?S + {#C#}) ?S = S\<close>
     unfolding S WS'_def' by auto
    show \<open>(set_clauses_to_update_l
      (clauses_to_update_l ?S + {#C#})
      (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S),
     S') \<in> twl_st_l (Some L)\<close>
      using SS' unfolding S_readd_C_S .
    show \<open>twl_stgy_invs S'\<close> \<open>twl_struct_invs S'\<close>
      using assms by fast+
    show \<open>C \<in># dom_m (get_clauses_l ?S)\<close>
      using assms C_N_U by (auto simp: twl_st_l)
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
      using confl SS' WS by (cases \<open>get_conflict_l S\<close>) (auto simp: twl_st_l dest: in_diffD)
  qed
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
  have \<open>twl_list_invs (set_conflict_l (get_clauses_l ?S \<propto> C) ?S)\<close>
    using add_inv C_N_U unfolding twl_list_invs_def
    by (auto dest: in_diffD simp: set_conflict_def S
      set_conflict_l_def mset_take_mset_drop_mset')
  then have confl_rel: \<open>(set_conflict_l (get_clauses_l ?S \<propto> C) ?S,
     Watched_Literals_Algorithm.set_conflict (twl_clause_of C')
      (set_clauses_to_update
        (remove1_mset (L, twl_clause_of C') (clauses_to_update S')) S'))
    \<in> {(S, S'). (S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S}\<close>
    using SS' WS by (auto simp: twl_st_l_def image_mset_remove1_mset_if set_conflict_def
      set_conflict_l_def mset_take_mset_drop_mset')
  have propa_rel:
    \<open>(propagate_lit_l (get_clauses_l ?S \<propto> C ! (1 - i)) C i
         (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S),
     propagate_lit L' (twl_clause_of C')
      (set_clauses_to_update
        (remove1_mset (L, twl_clause_of C') (clauses_to_update S')) S'))
    \<in> {(S, S'). (S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S}\<close>
    if
      \<open>(get_clauses_l ?S \<propto> C ! (1 - i), L') \<in> Id\<close> and
      L'_undef: \<open>- L' \<notin> lits_of_l
       (get_trail
         (set_clauses_to_update
           (remove1_mset (L, twl_clause_of C') (clauses_to_update S')) S')) \<close>
        \<open>L' \<notin> lits_of_l
           (get_trail
             (set_clauses_to_update
               (remove1_mset (L, twl_clause_of C') (clauses_to_update S'))
               S'))\<close>
    for L'
  proof -
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
    have [simp]: \<open>convert_lits_l (N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i))) M = convert_lits_l N M\<close>
      by (rule convert_lits_l_cong) auto
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
    have nth_swap_isabelle: \<open>length a \<ge> 2 \<Longrightarrow> swap a 0 (Suc 0 - i) ! 0 = a ! (Suc 0 - i)\<close> for a
      using two_le_length_C that apply (auto simp: swap_def S i_def)
      by (metis (full_types) le0 neq0_conv not_less_eq_eq nth_list_update_eq numeral_2_eq_2)
    have [simp]: \<open>Propagated La C \<notin> set M\<close> for La
    proof (rule ccontr)
      assume H:\<open>\<not> ?thesis\<close>
      then have \<open>La = N \<propto> C ! 0\<close>
        using add_inv C_N_U two_le_length_C mset_un_watched_swap C'_0i
        unfolding twl_list_invs_def S by auto
      moreover have \<open>La \<in> lits_of_l M\<close>
        using H by (force simp: lits_of_def)
      ultimately show False
        using L'_undef that SS' uL_M n_d
        by (auto simp: twl_st_l S i_def dest: no_dup_consistentD split: if_splits)
    qed
    have \<open>twl_list_invs
     (Propagated (N \<propto> C ! (Suc 0 - i)) C # M, N(C \<hookrightarrow> swap (N \<propto> C) 0 (Suc 0 - i)),
      D, NE, UE, remove1_mset C WS, add_mset (- N \<propto> C ! (Suc 0 - i)) Q)\<close>
      using add_inv C_N_U two_le_length_C mset_un_watched_swap C'_0i
      unfolding twl_list_invs_def
      by (auto dest: in_diffD simp: set_conflict_def
      set_conflict_l_def mset_take_mset_drop_mset' S nth_swap_isabelle
      dest!: mset_eq_setD)
    then show ?thesis
      using SS' WS that by (auto simp: twl_st_l_def image_mset_remove1_mset_if propagate_lit_def
      propagate_lit_l_def mset_take_mset_drop_mset' S learned_unchanged
      init_unchanged mset_un_watched_swap)
  qed
  have update_clause_rel: \<open>update_clause_l C i (the K)
       (set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S)
      \<le> \<Down> {(S, S'). (S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S}
         (update_clauseS L (twl_clause_of C')
           (set_clauses_to_update
             (remove1_mset (L, twl_clause_of C') (clauses_to_update S')) S'))\<close>
  if
    L': \<open>(get_clauses_l ?S \<propto> C ! (1 - i), L') \<in> Id\<close> and
    L'_M: \<open>L' \<notin> lits_of_l
           (get_trail
             (set_clauses_to_update
               (remove1_mset (L, twl_clause_of C') (clauses_to_update S'))
               S'))\<close> and
    K: \<open>K \<in> {found. (found = None) =
          (\<forall>L\<in>set (unwatched_l (get_clauses_l ?S \<propto> C)).
              - L \<in> lits_of_l (get_trail_l ?S)) \<and>
          (\<forall>j. found = Some j \<longrightarrow>
               j < length (get_clauses_l ?S \<propto> C) \<and>
               (undefined_lit (get_trail_l ?S) (get_clauses_l ?S \<propto> C ! j) \<or>
                get_clauses_l ?S \<propto> C ! j \<in> lits_of_l (get_trail_l ?S)) \<and>
               2 \<le> j)}\<close> and
    K_None: \<open>K \<noteq> None\<close>
    for L' and K
  proof -
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
    have [simp]: \<open>convert_lits_l (N(C \<hookrightarrow> swap (N \<propto> C) i K')) M = convert_lits_l N M\<close>
      apply (rule convert_lits_l_cong)
      using K'_le K'_2 by (auto simp: i_def)
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

      have H3:  \<open>{#L, C' ! (Suc 0 - i)#} = mset (watched_l (N \<propto> C))\<close>
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
      then have \<open>La = N \<propto> C ! 0\<close>
        using add_inv C_N_U two_le_length_C
        unfolding twl_list_invs_def S by auto
      moreover have \<open>La \<in> lits_of_l M\<close>
        using H by (force simp: lits_of_def)
      ultimately show False
        using L' L'_M SS' uL_M n_d
        by (auto simp: twl_st_l S i_def dest: no_dup_consistentD split: if_splits)
    qed
    have \<open>twl_list_invs (M, N(C \<hookrightarrow> swap (N \<propto> C) i K'), D, NE, UE, WS', Q)\<close>
      using add_inv C_N_U two_le_length_C
      unfolding twl_list_invs_def
      by (auto dest: in_diffD simp: set_conflict_def
      set_conflict_l_def mset_take_mset_drop_mset' S WS'_def'
      dest!: mset_eq_setD)
    then show ?thesis
      using SS' init_unchanged
      by (auto simp: S update_clause_l_def update_clauseS_def twl_st_l_def WS'_def'
        RETURN_SPEC_refine RES_RES_RETURN_RES RETURN_def RES_RES2_RETURN_RES H
        intro!: RES_refine exI[of _ \<open>N \<propto> C ! the K\<close>])
  qed

  have H: \<open>?A \<le> \<Down> {(S, S'). (S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S} ?B\<close>
    unfolding unit_propagation_inner_loop_body_l_def unit_propagation_inner_loop_body_def
      option.case_eq_if find_unwatched_l_def
    apply (rewrite at \<open>let _ = if _ ! _ = _then _ else _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ =  polarity _ _ in _\<close> Let_def)
    apply clarify
    apply (refine_vcg
        bind_refine_spec[where M' = \<open>RETURN (polarity _ _)\<close>, OF _ polarity_spec]
        case_prod_bind[of _ \<open>If _ _\<close>]; remove_dummy_vars)
    subgoal by (rule pre_inv)
    subgoal
      using mset_watched_C by (auto simp: i_def)
    subgoal for L'
      using assms by (auto simp: twl_st_l polarity_def Decided_Propagated_in_iff_in_lits_of_l)
    subgoal by (rule upd_rel)
    subgoal using SS' by (auto simp: twl_st_l)
    subgoal using SS' by (auto simp: twl_st_l Decided_Propagated_in_iff_in_lits_of_l
      polarity_def)
    subgoal by (rule confl_rel)
    subgoal unfolding i_def[symmetric]  i_def'[symmetric] by (rule propa_rel)
    subgoal by auto
    subgoal for L' K unfolding i_def[symmetric]  i_def'[symmetric]
      by (rule update_clause_rel)
    done
  have D_None: \<open>get_conflict_l S = None\<close>
    using confl SS' by (cases \<open>get_conflict_l S\<close>) (auto simp: S twl_st_l WS'_def')
  have *: \<open>unit_propagation_inner_loop_body (C' ! i, twl_clause_of C')
   (set_clauses_to_update (remove1_mset (C' ! i, twl_clause_of C') (clauses_to_update S')) S')
   \<le> SPEC (\<lambda>S''. twl_struct_invs S'' \<and>
                 twl_stgy_invs S'' \<and>
                 cdcl_twl_cp\<^sup>*\<^sup>* S' S'' \<and>
              (S'', S') \<in> measure (size \<circ> clauses_to_update))\<close>
    apply (rule unit_propagation_inner_loop_body(1)[of S' \<open>(C' ! i, twl_clause_of C')\<close>])
    using imageI[OF WS, of \<open>(\<lambda>j. (L, twl_clause_of (N \<propto> j)))\<close>]
      struct_invs stgy_inv C_N_U WS SS' D_None by (auto simp: twl_st_l)
  have H': \<open>?B \<le> SPEC (\<lambda>S'. twl_stgy_invs S' \<and> twl_struct_invs S')\<close>
    using * unfolding conj.left_assoc
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
      unit_propagation_inner_loop_body (L, twl_clause_of (get_clauses_l S \<propto> C))
        (set_clauses_to_update
          (remove1_mset (L, twl_clause_of (get_clauses_l S \<propto> C))
          (clauses_to_update S')) S'))
    \<in> \<langle>{(S, S'). (S, S') \<in> twl_st_l (Some L) \<and> twl_list_invs S \<and> twl_stgy_invs S' \<and>
         twl_struct_invs S'}\<rangle>nres_rel\<close>
  using unit_propagation_inner_loop_body_l[OF assms]
  by (auto simp: nres_rel_def)

definition select_from_clauses_to_update :: \<open>'v twl_st_l \<Rightarrow> ('v twl_st_l \<times> nat) nres\<close> where
  \<open>select_from_clauses_to_update S = SPEC (\<lambda>(S', C). C \<in># clauses_to_update_l S \<and>
     S' = set_clauses_to_update_l (clauses_to_update_l S - {#C#}) S)\<close>

definition unit_propagation_inner_loop_l_inv where
  \<open>unit_propagation_inner_loop_l_inv L S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_l (Some L) \<and> twl_struct_invs S' \<and> twl_stgy_invs S' \<and>
      twl_list_invs S)\<close>

definition unit_propagation_inner_loop_l :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>unit_propagation_inner_loop_l L S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_l_inv L\<^esup>
      (\<lambda>S. clauses_to_update_l S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT (clauses_to_update_l S \<noteq> {#});
        (S', C) \<leftarrow> select_from_clauses_to_update S;
        unit_propagation_inner_loop_body_l L C S'
      })
      S\<^sub>0
  \<close>

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
    using assms unfolding S by (auto simp add: RES_refine Bex_def twl_st_l_def)
qed

lemma refine_add_inv:
  fixes f :: \<open>'a \<Rightarrow> 'a nres\<close> and f' :: \<open>'b \<Rightarrow> 'b nres\<close> and h :: \<open>'b \<Rightarrow> 'a\<close>
  assumes
    \<open>(f', f) \<in> {(S, S'). S' = h S \<and> R S} \<rightarrow> \<langle>{(T, T'). T' = h T \<and> P' T}\<rangle> nres_rel\<close>
    (is \<open>_ \<in> ?R \<rightarrow> \<langle>{(T, T'). ?H T T' \<and> P' T}\<rangle> nres_rel\<close>)
  assumes
    \<open>\<And>S. R S \<Longrightarrow> f (h S) \<le> SPEC (\<lambda>T. Q T)\<close>
  shows
    \<open>(f', f) \<in> ?R \<rightarrow> \<langle>{(T, T'). ?H T T' \<and> P' T \<and> Q (h T)}\<rangle> nres_rel\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by fastforce

lemma refine_add_inv_generalised:
  fixes f :: \<open>'a \<Rightarrow> 'b nres\<close> and f' :: \<open>'c \<Rightarrow> 'd nres\<close>
  assumes
    \<open>(f', f) \<in> A \<rightarrow>\<^sub>f \<langle>B\<rangle> nres_rel\<close>
  assumes
    \<open>\<And>S S'. (S, S') \<in> A \<Longrightarrow> f S' \<le> RES C\<close>
  shows
    \<open>(f', f) \<in> A \<rightarrow>\<^sub>f \<langle>{(T, T'). (T, T') \<in> B \<and> T' \<in> C}\<rangle> nres_rel\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
   fref_param1[symmetric]
  by fastforce

lemma refine_add_inv_pair:
  fixes f :: \<open>'a \<Rightarrow> ('c \<times> 'a) nres\<close> and f' :: \<open>'b \<Rightarrow> ('c \<times> 'b) nres\<close> and h :: \<open>'b \<Rightarrow> 'a\<close>
  assumes
    \<open>(f', f) \<in> {(S, S'). S' = h S \<and> R S} \<rightarrow> \<langle>{(S, S'). (fst S' = h' (fst S) \<and>
    snd S' = h (snd S)) \<and> P' S}\<rangle> nres_rel\<close>  (is \<open>_ \<in> ?R \<rightarrow> \<langle>{(S, S'). ?H S S' \<and> P' S}\<rangle> nres_rel\<close>)
  assumes
    \<open>\<And>S. R S \<Longrightarrow> f (h S) \<le> SPEC (\<lambda>T. Q (snd T))\<close>
  shows
    \<open>(f', f) \<in> ?R \<rightarrow> \<langle>{(S, S'). ?H S S' \<and> P' S \<and> Q (h (snd S))}\<rangle> nres_rel\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by fastforce

lemma clauses_to_update_l_empty_tw_st_of_Some_None[simp]:
  \<open>clauses_to_update_l S = {#} \<Longrightarrow> (S, S')\<in> twl_st_l (Some L) \<longleftrightarrow> (S, S') \<in> twl_st_l None\<close>
  by (cases S) (auto simp: twl_st_l_def)
thm frefI
lemma unit_propagation_inner_loop_l:
  \<open>(uncurry unit_propagation_inner_loop_l,  unit_propagation_inner_loop) \<in>
  {((L, S), S'). (S, S') \<in> twl_st_l (Some L) \<and> twl_struct_invs S' \<and>
     twl_stgy_invs S' \<and> twl_list_invs S} \<rightarrow>\<^sub>f
  \<langle>{(T, T'). (T, T') \<in> twl_st_l None \<and> clauses_to_update_l T = {#} \<and>
    twl_list_invs T \<and> twl_struct_invs T' \<and> twl_stgy_invs T'}\<rangle> nres_rel\<close>
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
    if \<open>(S, S'') \<in> {(T, T'). (T, T') \<in> twl_st_l (Some L) \<and> twl_list_invs T}\<close> for S S'' L
    using that unfolding select_from_clauses_to_update_def
    by (auto simp: conc_fun_def image_mset_remove1_mset_if twl_st_l_def)
  show ?thesis
    unfolding unit_propagation_inner_loop_l_def unit_propagation_inner_loop_def uncurry_def
    apply (intro frefI nres_relI)
    subgoal for LS S'
      apply (refine_vcg set_mset_clauses_to_update_l_set_mset_clauses_to_update_spec
        WHILEIT_refine_genR[where R=\<open>?B\<close> and R' = \<open>{(T, T'). (T, T') \<in> twl_st_l (Some (fst LS)) \<and>
          twl_list_invs T}\<close>]
        SPEC_remove;
        remove_dummy_vars)
      subgoal by simp
      subgoal unfolding unit_propagation_inner_loop_l_inv_def by fastforce
      subgoal by (auto simp add: twl_st_l)
      subgoal for L S T T' C' U C
        apply (rule refinement_trans_long[OF _ _ _ unit_propagation_inner_loop_body_l[of T T' L C,
          unfolded prod.collapse]])
        subgoal by auto
        subgoal by (auto simp: twl_st_l)
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        done
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
  obtain M N D NE UE WS Q where
    T: \<open>T = (M, N, D , NE, UE, WS, Q)\<close>
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
       {#f (fst x). x \<in># {#C \<in># ran_m N. P (fst C)#}#}\<close> for P f
        unfolding ran_m_def image_mset_filter_swap2 by auto

    have H: \<open>{#f (N\<propto>x). x \<in># ?S#} =
        {#f (fst x). x \<in># {#C \<in># init_clss_l N. L' \<in> set (watched_l (fst C))#}#} +
        {#f (fst x). x \<in># {#C \<in># learned_clss_l N. L' \<in> set (watched_l (fst C))#}#}\<close>
      for f
      unfolding image_mset_union[symmetric] filter_union_mset[symmetric]
      apply auto
      apply (subst H)
      ..

    have L'': \<open>{#(L', ?C x). x \<in># ?S#} = Pair L' `# {#?C x. x \<in># ?S#}\<close>
      by auto
    also have \<open>\<dots> = Pair L' `# ?C'\<close>
      apply (rule arg_cong[of _ _ \<open>op `# (Pair L')\<close>])
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
  obtain M N C NE UE WS Q where
    T: \<open>T = (M, N, C, NE, UE, WS, Q)\<close>
    by (cases T) auto
  show ?thesis
    using assms
    unfolding twl_list_invs_def T by auto
qed

lemma unit_propagation_outer_loop_l_spec:
  \<open>(unit_propagation_outer_loop_l, unit_propagation_outer_loop) \<in>
  {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_struct_invs S' \<and>
    twl_stgy_invs S' \<and> twl_list_invs S \<and> clauses_to_update_l S = {#} \<and>
    get_conflict_l S = None} \<rightarrow>\<^sub>f
  \<langle>{(T, T'). (T, T') \<in> twl_st_l None \<and>
    (twl_list_invs T \<and> twl_struct_invs T' \<and> twl_stgy_invs T' \<and>
          clauses_to_update_l T = {#}) \<and>
    literals_to_update T' = {#} \<and> clauses_to_update T' = {#} \<and>
    no_step cdcl_twl_cp T'}\<rangle> nres_rel\<close>
  (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f ?I\<close> is \<open>_ \<in> _ \<rightarrow>\<^sub>f \<langle>?B\<rangle> nres_rel\<close>)
proof -
  have H:
   \<open>select_and_remove_from_literals_to_update x
       \<le> \<Down> {((S', L'), L). L = L' \<and>  S' = set_clauses_to_update_l (clause_to_update L x)
              (set_literals_to_update_l (remove1_mset L (literals_to_update_l x)) x)}
           (SPEC (\<lambda>L. L \<in># literals_to_update x'))\<close>
     if \<open>(x, x') \<in> twl_st_l None\<close> for x :: \<open>'v twl_st_l\<close> and x' :: \<open>'v twl_st\<close>
    using that unfolding select_and_remove_from_literals_to_update_def
    apply (cases x; cases x')
    unfolding conc_fun_def by (clarsimp simp add: twl_st_l_def conc_fun_def)
  have H:
    \<open>(unit_propagation_outer_loop_l, unit_propagation_outer_loop) \<in>?R \<rightarrow>\<^sub>f
      \<langle>{(S, S').
          (S, S') \<in> twl_st_l None \<and>
          clauses_to_update_l S = {#} \<and>
          twl_list_invs S \<and>
          twl_struct_invs S' \<and>
          twl_stgy_invs S'}\<rangle> nres_rel\<close>
    unfolding unit_propagation_outer_loop_l_def unit_propagation_outer_loop_def fref_param1[symmetric]
    apply (refine_vcg unit_propagation_inner_loop_l[THEN fref_to_Down_curry_left]
       H)
    subgoal by simp
    subgoal unfolding unit_propagation_outer_loop_l_inv_def by fastforce
    subgoal by (auto simp: twl_st_l)
    subgoal by simp
    subgoal by fast
    subgoal for S S' T T' L L' C
      by (auto simp add: twl_st_of_clause_to_update twl_list_invs_set_clauses_to_update_iff
          intro: cdcl_twl_cp_twl_struct_invs cdcl_twl_cp_twl_stgy_invs
          distinct_mset_clause_to_update
          dest: in_clause_to_updateD)
    done
  have B: \<open>?B = {(T, T'). (T, T') \<in> {(T, T'). (T, T') \<in> twl_st_l None \<and>
                   twl_list_invs T \<and>
                    twl_struct_invs T' \<and>
                    twl_stgy_invs T' \<and> clauses_to_update_l T = {#} } \<and>
                   T' \<in> {T'. literals_to_update T' = {#} \<and>
                   clauses_to_update T' = {#} \<and>
                   (\<forall>S'. \<not> cdcl_twl_cp T' S')}}\<close>
    by auto
  show ?thesis
    unfolding B
    apply (rule refine_add_inv_generalised)
    subgoal
      using H apply -
      apply (match_spec; (match_fun_rel; match_fun_rel?)+)
       apply blast+
      done
    subgoal for S S'
      apply (rule weaken_SPEC[OF unit_propagation_outer_loop[of S']])
      apply ((auto simp: twl_st_l; fail)+)[4]
      using no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp by blast
    done
qed

lemma get_conflict_l_get_conflict_state_spec:
  assumes \<open>(S, S') \<in> twl_st_l None\<close> and \<open>twl_list_invs S\<close> and \<open>clauses_to_update_l S = {#}\<close>
  shows \<open>((False, S), (False, S'))
  \<in> {((brk, S), (brk', S')). brk = brk' \<and> (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
    clauses_to_update_l S = {#}}\<close>
  using assms by auto

fun lit_and_ann_of_propagated where
  \<open>lit_and_ann_of_propagated (Propagated L C) = (L, C)\<close>

definition tl_state_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>tl_state_l = (\<lambda>(M, N, D, NE, UE, WS, Q). (tl M, N, D, NE, UE, WS, Q))\<close>

definition resolve_cls_l' :: \<open>'v twl_st_l \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> 'v clause\<close> where
\<open>resolve_cls_l' S C L  =
   remove1_mset (-L) (the (get_conflict_l S) \<union># mset (tl (get_clauses_l S \<propto> C)))\<close>

definition update_confl_tl_l :: \<open>nat \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> bool \<times> 'v twl_st_l\<close> where
  \<open>update_confl_tl_l = (\<lambda>C L (M, N, D, NE, UE, WS, Q).
     let D = resolve_cls_l' (M, N, D, NE, UE, WS, Q) C L in
        (False, (tl M, N, Some D, NE, UE, WS, Q)))\<close>

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
            let D' = the (get_conflict_l S);
            let (L, C) = lit_and_ann_of_propagated (hd (get_trail_l S));
            if -L \<notin># D' then
              do {RETURN (False, tl_state_l S)}
            else
              if get_maximum_level (get_trail_l S) (remove1_mset (-L) D') = count_decided (get_trail_l S)
              then
                do {RETURN (update_confl_tl_l C L S)}
              else
                do {RETURN (True, S)}
          }
        )
        (False, S\<^sub>0);
      RETURN S
    }
  \<close>

context
begin

private lemma skip_and_resolve_l_refines:
  \<open>((brkS), brk'S') \<in> {((brk, S), brk', S'). brk = brk' \<and> (S, S') \<in> twl_st_l None \<and>
       twl_list_invs S \<and> clauses_to_update_l S = {#}} \<Longrightarrow>
    brkS = (brk, S) \<Longrightarrow> brk'S' = (brk', S') \<Longrightarrow>
  ((False, tl_state_l S), False, tl_state S') \<in> {((brk, S), brk', S'). brk = brk' \<and>
       (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}}\<close>
  by (cases S; cases \<open>get_trail_l S\<close>)
   (auto simp: twl_list_invs_def twl_st_l_def
      resolve_cls_l_nil_iff tl_state_l_def tl_state_def)

private lemma skip_and_resolve_skip_refine:
  assumes
    rel: \<open>((nrk, S), brk', S') \<in> {((brk, S), brk', S'). brk = brk' \<and>
         (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}}\<close> and
    dec: \<open>\<not> is_decided (hd (get_trail S'))\<close> and
    rel': \<open>((L, C), L', C') \<in> {((L, C), L', C'). L = L' \<and>
        C' = (if C = 0 then {#L#} else mset (get_clauses_l S \<propto>  C))}\<close> and
    LC: \<open>lit_and_ann_of_propagated (hd (get_trail_l S)) = (L, C)\<close> and
    tr: \<open>get_trail_l S \<noteq> []\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    stgy_invs: \<open>twl_stgy_invs S'\<close> and
    lev: \<open>count_decided (get_trail_l S) > 0\<close>
  shows
   \<open>(update_confl_tl_l C L S, False,
     update_confl_tl (Some (remove1_mset (- L') (the (get_conflict S')) \<union># remove1_mset L' C')) S')
         \<in> {((brk, S), brk', S').
             brk = brk' \<and>
             (S, S') \<in> twl_st_l None \<and>
             twl_list_invs S \<and>
             clauses_to_update_l S = {#}}\<close>
proof -
  obtain M N D NE UE Q where S: \<open>S = (Propagated L C # M, N, D, NE, UE, {#}, Q)\<close>
    using dec LC tr rel
    by (cases S; cases \<open>get_trail_l S\<close>; cases \<open>hd (get_trail_l S)\<close>)
      (auto simp: twl_st_l)
  have S': \<open>(S, S') \<in> twl_st_l None\<close> and [simp]: \<open>L = L'\<close> and
    C': \<open>C' = (if C = 0 then {#L#} else mset (get_clauses_l S \<propto> C))\<close> and
    invs_S: \<open>twl_list_invs S\<close>
    using rel rel' unfolding S by auto
  have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of S')\<close> and
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S')\<close>
    using struct_invs unfolding twl_struct_invs_def by fast+
  moreover have \<open>Suc 0 \<le> backtrack_lvl (state\<^sub>W_of S')\<close>
    using lev S' by (cases S) (auto simp: trail.simps twl_st_l_def)
  moreover have \<open>is_proped (cdcl\<^sub>W_restart_mset.hd_trail (state\<^sub>W_of S'))\<close>
    using dec tr S' by (cases \<open>get_trail_l S\<close>)
     (auto simp: trail.simps is_decided_no_proped_iff twl_st_l_def)
  moreover have \<open>mark_of (cdcl\<^sub>W_restart_mset.hd_trail (state\<^sub>W_of S')) = C'\<close>
    using dec S' unfolding C' by (auto simp: S trail.simps twl_st_l_def)
  ultimately have False: \<open>C = 0 \<Longrightarrow> False\<close>
    using C' cdcl\<^sub>W_restart_mset.hd_trail_level_ge_1_length_gt_1[of \<open>state\<^sub>W_of S'\<close>]
    by (auto simp: is_decided_no_proped_iff)
  then have L: \<open>L = N \<propto> C ! 0\<close> and C_dom: \<open>C \<in># dom_m N\<close>
    using invs_S
    unfolding S C' by (auto simp: twl_list_invs_def)
  moreover {
    have \<open>twl_st_inv S'\<close>
      using struct_invs unfolding S twl_struct_invs_def
      by fast
    then have
      \<open>\<forall>x\<in>#ran_m N. struct_wf_twl_cls (twl_clause_of (fst x))\<close>
      using struct_invs S' unfolding S twl_st_inv_alt_def
      by (simp add: twl_st_l)
    then have \<open>Multiset.Ball (dom_m N) (\<lambda>C. length (N \<propto> C) \<ge> 2)\<close>
      by (subst (asm) Ball_ran_m_dom_struct_wf) auto
    then have \<open>length (N \<propto> C) \<ge> 2\<close>
      using \<open>C \<in># dom_m N\<close>  unfolding S by (auto simp: twl_list_invs_def)
  }
  moreover {
    have
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of S')\<close> and
      M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of S')\<close>
      using struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
    then have \<open>M \<Turnstile>as CNot (remove1_mset L (mset (N \<propto> C)))\<close>
      using S' False
      by (cases \<open>C = 0\<close>)
         (force simp: S twl_st_l_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset_state)+
    then have \<open>-L' \<in># mset (N \<propto> C) \<Longrightarrow> False\<close>
      apply - apply (drule multi_member_split)
      using S' M_lev False unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (auto simp: S twl_st_l_def cdcl\<^sub>W_restart_mset_state split: if_splits
          dest: in_lits_of_l_defined_litD)
    then have \<open>remove1_mset (- L') (the D) \<union># mset (tl (N \<propto> C)) =
       remove1_mset (- L') (the D \<union># mset (tl (N \<propto> C)))\<close>
      using L by(cases \<open>N \<propto> C\<close>; cases \<open>-L' \<in># mset (N \<propto> C)\<close>)
         (auto simp: remove1_mset_union_distrib)
  }
  ultimately show ?thesis
    using invs_S S'
    by (cases \<open>N \<propto> C\<close>)
      (auto simp: skip_and_resolve_loop_inv_def twl_list_invs_def resolve_cls_l'_def
        resolve_cls_l_nil_iff update_confl_tl_l_def update_confl_tl_def twl_st_l_def
        S S' C' dest!: False)
qed

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
  have is_proped[iff]: \<open>is_proped (hd (get_trail S')) \<longleftrightarrow> is_proped (hd (get_trail_l S))\<close>
    if \<open>get_trail_l S \<noteq> []\<close> and
      \<open>(S, S') \<in> twl_st_l None\<close>
    for S :: \<open>'v twl_st_l\<close> and S'
    by (cases S, cases \<open>get_trail_l S\<close>; cases \<open>hd (get_trail_l S)\<close>)
      (use that in \<open>auto split: if_splits simp: twl_st_l_def\<close>)
  have H: \<open>RETURN (lit_and_ann_of_propagated (hd (get_trail_l S)))
    \<le> \<Down> {((L, C), (L', C')). L = L' \<and> C' = (if C = 0 then {#L#} else mset (get_clauses_l S \<propto> C))}
    (SPEC (\<lambda>(L, C). Propagated L C = hd (get_trail S')))\<close>
    if \<open>(S, S') \<in> twl_st_l None\<close> and \<open>get_trail_l S \<noteq> []\<close> and
      p: \<open>is_proped (hd (get_trail_l S))\<close>
    for S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st\<close>
    using that apply (cases S; cases S'; cases \<open>get_trail_l S\<close>; cases \<open>hd (get_trail_l S)\<close> ;
        cases \<open>get_trail S'\<close>; cases \<open>hd (get_trail S')\<close>)
                   apply ((solves \<open>force split: if_splits\<close>)+)[15]
    unfolding RETURN_def
    by (rule RES_refine; solves \<open>auto split: if_splits simp: twl_st_l_def\<close>)+
  have skip_and_resolve_loop_inv_trail_nempty: \<open>skip_and_resolve_loop_inv S' (False, S) \<Longrightarrow>
        get_trail S \<noteq> []\<close> for S S'
    unfolding skip_and_resolve_loop_inv_def
    by auto

  have twl_list_invs_tl_state_l: \<open>twl_list_invs S \<Longrightarrow> twl_list_invs (tl_state_l S)\<close> for S
    by (cases S, cases \<open>get_trail_l S\<close>) (auto simp: tl_state_l_def twl_list_invs_def)
  have clauses_to_update_l_tl_state: \<open>clauses_to_update_l (tl_state_l S) = clauses_to_update_l S\<close>
    for S
    by (cases S, cases \<open>get_trail_l S\<close>) (auto simp: tl_state_l_def)
  have mark_ge_0: \<open>0 < mark_of (hd (get_trail_l T))\<close>
  if
    SS': \<open>(S, S') \<in> ?R\<close> and
    \<open>get_conflict_l S \<noteq> None\<close> and
    brk_TT': \<open>(brkT, brkT')
     \<in> {((brk, S), brk', S').
        brk = brk' \<and>
        (S, S') \<in> twl_st_l None \<and>
        twl_list_invs S \<and> clauses_to_update_l S = {#}}\<close> and
    loop_inv: \<open>skip_and_resolve_loop_inv S' brkT'\<close> and
    brkT: \<open>brkT = (brk, T)\<close> and
    dec: \<open>\<not> is_decided (hd (get_trail_l T))\<close>
    for S S' brkT brkT' brk T
  proof -
    obtain brk' T' where brkT': \<open>brkT' = (brk', T')\<close> by (cases brkT')
    have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of T')\<close> and
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of T')\<close> and
      tr: \<open>get_trail T' \<noteq> []\<close> and
      count_dec: \<open>count_decided (get_trail_l T) \<noteq> 0\<close> and
      TT': \<open>(T,T') \<in> twl_st_l None \<close>
      using loop_inv brk_TT' unfolding twl_struct_invs_def skip_and_resolve_loop_inv_def brkT brkT'
      by (force simp: twl_st_l)+
    moreover have \<open>Suc 0 \<le> backtrack_lvl (state\<^sub>W_of T')\<close>
      using count_dec TT' by (auto simp: twl_st_l trail.simps)
    moreover have \<open>is_proped (cdcl\<^sub>W_restart_mset.hd_trail (state\<^sub>W_of T'))\<close>
      using dec tr TT' by (cases \<open>get_trail_l T\<close>)
      (auto simp: trail.simps is_decided_no_proped_iff twl_st_l twl_st)
    moreover have \<open>mark_of (hd (get_trail_l T)) = 0 \<Longrightarrow>
      size (mark_of (cdcl\<^sub>W_restart_mset.hd_trail (state\<^sub>W_of T'))) = Suc 0\<close>
      using tr dec TT' by (cases \<open>get_trail_l T\<close>; cases \<open>hd (get_trail_l T)\<close>)
        (auto simp: trail.simps twl_st_l twl_st)
    ultimately have False: \<open>mark_of (hd (get_trail_l T)) = 0 \<Longrightarrow> False\<close>
      using cdcl\<^sub>W_restart_mset.hd_trail_level_ge_1_length_gt_1[of \<open>state\<^sub>W_of T'\<close>] TT'
      by (auto simp: is_decided_no_proped_iff twl_st twl_st_l)
    then show ?thesis by blast
  qed
  have H:
    \<open>(skip_and_resolve_loop_l, skip_and_resolve_loop) \<in> ?R \<rightarrow>\<^sub>f
      \<langle>{(T::'v twl_st_l, T'). (T, T') \<in> twl_st_l None \<and> twl_list_invs T \<and>
        clauses_to_update_l T = {#}}\<rangle> nres_rel\<close>
    supply [[goals_limit=1]]
    unfolding skip_and_resolve_loop_l_def skip_and_resolve_loop_def fref_param1[symmetric]
    apply (refine_vcg get_conflict_l_get_conflict_state_spec H)
    subgoal by (auto simp: twl_st_l) \<comment> \<open>conflict is not none\<close>
    subgoal by auto \<comment> \<open>loop invariant init: @{term skip_and_resolve_loop_inv}\<close>
    subgoal by auto \<comment> \<open>loop invariant init: @{term twl_list_invs}\<close>
    subgoal by auto \<comment> \<open>loop invariant init: @{term \<open>clauses_to_update S = {#}\<close>}\<close>
    subgoal for S S' brkT brkT'
      unfolding skip_and_resolve_loop_inv_l_def
      apply(rule exI[of _ \<open>snd brkT'\<close>])
      apply(rule exI[of _ S'])
      apply (intro conjI impI)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (rule mark_ge_0)  (auto simp: twl_st_l)
      done
      \<comment> \<open>align loop conditions\<close>
    subgoal by (auto simp: twl_st_l dest!: skip_and_resolve_loop_inv_trail_nempty)
    subgoal by auto
    subgoal by (auto simp: twl_st_l)
    subgoal by (auto simp: twl_st_l is_decided_no_proped_iff)
    subgoal by (auto simp: is_decided_no_proped_iff twl_st_l
      dest!: skip_and_resolve_loop_inv_trail_nempty)
    subgoal by (drule skip_and_resolve_l_refines) blast+
    subgoal by (auto simp: twl_list_invs_tl_state_l)
    subgoal by (auto simp: twl_st_l clauses_to_update_l_tl_state)
    subgoal by (auto simp: twl_st_l)
   subgoal by (rule skip_and_resolve_skip_refine)
     (auto simp: skip_and_resolve_loop_inv_def twl_st_l)
      \<comment> \<open>annotations are valid\<close>
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
         thm refine_add_inv_generalised
    apply (rule refine_add_inv_generalised)
    subgoal by (rule H)
    subgoal for S S'
      apply (rule order_trans)
      apply (rule skip_and_resolve_loop_spec[of S'])
      by (auto simp: twl_st_l)
    done
  show ?thesis
    using H apply -
    apply (match_spec; (match_fun_rel; match_fun_rel?)+)
    by blast+
qed

end


definition find_decomp :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>find_decomp =  (\<lambda>L (M, N, D, NE, UE, WS, Q).
    SPEC(\<lambda>S. \<exists>K M2 M1. S = (M1, N, D, NE, UE, WS, Q) \<and>
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

definition find_lit_of_max_level :: \<open>'v twl_st_l \<Rightarrow> 'v literal \<Rightarrow> 'v literal nres\<close> where
  \<open>find_lit_of_max_level =  (\<lambda>(M, N, D, NE, UE, WS, Q) L.
    SPEC(\<lambda>L'. L' \<in># the D - {#-L#} \<and> get_level M L' = get_maximum_level M (the D - {#-L#})))\<close>

definition ex_decomp_of_max_lvl :: \<open>('v, nat) ann_lits \<Rightarrow> 'v cconflict \<Rightarrow> 'v literal \<Rightarrow> bool\<close> where
  \<open>ex_decomp_of_max_lvl M D L \<longleftrightarrow>
       (\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (remove1_mset (-L) (the D)) + 1)\<close>

fun add_mset_list :: \<open>'a list \<Rightarrow> 'a multiset multiset \<Rightarrow> 'a multiset multiset\<close>  where
  \<open>add_mset_list L UE = add_mset (mset L) UE\<close>

definition (in -)list_of_mset :: \<open>'v clause \<Rightarrow> 'v clause_l nres\<close> where
  \<open>list_of_mset D = SPEC(\<lambda>D'. D = mset D')\<close>

fun extract_shorter_conflict_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close>
   where
  \<open>extract_shorter_conflict_l (M, N, D, NE, UE, WS, Q) = SPEC(\<lambda>S.
     \<exists>D'. D' \<subseteq># the D \<and> S = (M, N, Some D', NE, UE, WS, Q) \<and>
     clause `# twl_clause_of `# ran_mf N + NE + UE \<Turnstile>pm D' \<and> -(lit_of (hd M)) \<in># D')\<close>

declare extract_shorter_conflict_l.simps[simp del]
lemmas extract_shorter_conflict_l_def = extract_shorter_conflict_l.simps

lemma extract_shorter_conflict_l_alt_def:
   \<open>extract_shorter_conflict_l S = SPEC(\<lambda>T.
     \<exists>D'. D' \<subseteq># the (get_conflict_l S) \<and> equality_except_conflict_l S T \<and> get_conflict_l T = Some D' \<and>
     clause `# twl_clause_of `# ran_mf (get_clauses_l S) + get_unit_clauses_l S \<Turnstile>pm D' \<and>
     -lit_of (hd (get_trail_l S)) \<in># D')\<close>
  by (cases S) (auto simp: extract_shorter_conflict_l_def ac_simps)

definition backtrack_l_inv where
  \<open>backtrack_l_inv S \<longleftrightarrow>
      (\<exists>S'. (S, S') \<in> twl_st_l None \<and>
      get_trail_l S \<noteq> [] \<and>
      no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of S')\<and>
      no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of S') \<and>
      get_conflict_l S \<noteq> None \<and>
      twl_struct_invs S' \<and>
      twl_stgy_invs S' \<and>
      twl_list_invs S \<and>
      get_conflict_l S \<noteq> Some {#})
  \<close>

definition get_fresh_index :: \<open>'v clauses_l \<Rightarrow> nat nres\<close> where
\<open>get_fresh_index N = SPEC(\<lambda>i. i > 0 \<and> i \<notin># dom_m N)\<close>

definition propagate_bt_l :: \<open>'v literal \<Rightarrow> 'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>propagate_bt_l = (\<lambda>L L' (M, N, D, NE, UE, WS, Q). do {
    D'' \<leftarrow> list_of_mset (the D);
    i \<leftarrow> get_fresh_index N;
    RETURN (Propagated (-L) i # M,
        fmupd i ([-L, L'] @ (remove1 (-L) (remove1 L' D'')), False) N,
          None, NE, UE, WS, {#L#})
      })\<close>

definition propagate_unit_bt_l :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>propagate_unit_bt_l = (\<lambda>L (M, N, D, NE, UE, WS, Q).
    (Propagated (-L) 0 # M, N, None, NE, add_mset (the D) UE, WS, {#L#}))\<close>

definition backtrack_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>backtrack_l S =
    do {
      ASSERT(backtrack_l_inv S);
      let L = lit_of (hd (get_trail_l S));
      S \<leftarrow> extract_shorter_conflict_l S;
      S \<leftarrow> find_decomp L S;

      if size (the (get_conflict_l S)) > 1
      then do {
        L' \<leftarrow> find_lit_of_max_level S L;
        propagate_bt_l L L' S
      }
      else do {
        RETURN (propagate_unit_bt_l L S)
     }
  }\<close>

text \<open>TODO Move\<close>
lemma extract_shorter_conflict_alt_def:
  \<open>extract_shorter_conflict S =
    SPEC(\<lambda>S'. \<exists>D'. equality_except_conflict S S' \<and> Some D' = get_conflict S' \<and>
       D' \<subseteq># the (get_conflict S) \<and> clause `# (get_clauses S) + unit_clss S \<Turnstile>pm D' \<and>
       -lit_of (hd (get_trail S)) \<in># D')\<close>
  unfolding extract_shorter_conflict_def
  by (cases S) (auto simp: ac_simps)
text \<open>END Move\<close>

lemma backtrack_l_spec:
  \<open>(backtrack_l, backtrack) \<in>
    {(S::'v twl_st_l, S'). (S, S') \<in> twl_st_l None \<and> get_conflict_l S \<noteq> None \<and> get_conflict_l S \<noteq> Some {#} \<and>
       clauses_to_update_l S = {#} \<and> literals_to_update_l S = {#} \<and> twl_list_invs S \<and>
       no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of S') \<and>
       no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of S') \<and>
       twl_struct_invs S' \<and> twl_stgy_invs S'} \<rightarrow>\<^sub>f
    \<langle>{(T::'v twl_st_l, T'). (T, T') \<in> twl_st_l None \<and> get_conflict_l T = None \<and> twl_list_invs T \<and>
       twl_struct_invs T' \<and> twl_stgy_invs T' \<and> clauses_to_update_l T = {#} \<and>
       literals_to_update_l T \<noteq> {#}}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow>\<^sub>f ?I\<close>)
proof -
  have obtain_decom': \<open>\<exists>K. \<exists>M1. (\<exists>M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M')) \<and>
    get_level M' K = Suc (get_maximum_level M' (remove1_mset (- lit_of (hd M'))
    E))\<close> if
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (convert_lits_l N M')) \<and>
    get_level M' K = Suc (get_maximum_level M' (remove1_mset (- lit_of (hd (convert_lits_l N M')))
    E))\<close> (is \<open>?P K M1 M2 \<and> ?Q K\<close> ) and
    M': \<open>M' \<noteq> []\<close>
    for M' E N K M1 M2
  proof -
    obtain K M1 M2 where
      \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (convert_lits_l N M'))\<close> and
      Q: \<open>?Q K\<close>
      using decomp by auto
    then obtain K' M1' M2' where
      \<open>(K' # M1', M2') \<in> set (get_all_ann_decomposition M')\<close> and
      \<open>Decided K # M1 = convert_lits_l N (K' # M1')\<close> and
      \<open>M2 = convert_lits_l N M2'\<close>
      unfolding get_all_ann_decomposition_convert_lits_l
      by (auto simp: convert_lits_l_def case_prod_beta)
    then show ?thesis
      using M' apply -
      by (cases K') (use Q in \<open>auto split: if_splits\<close>)
  qed
  have H: \<open>find_decomp L S
       \<le> \<Down> {(T, T'). (T, T') \<in> twl_st_l None \<and> equality_except_trail S T \<and>
       (\<exists>M. get_trail_l S = M @ get_trail_l T)}
       (reduce_trail_bt L' S')\<close>
    (is \<open>_ \<le>  \<Down> ?find_decomp _\<close>)
    if
      SS': \<open>(S, S') \<in> twl_st_l None\<close> and \<open>L = lit_of (hd (get_trail_l S))\<close> and
      \<open>L' = lit_of (hd (get_trail S'))\<close> \<open>get_trail_l S \<noteq> []\<close>
    for S S' L' L
    unfolding find_decomp_alt_def reduce_trail_bt_def
      state_decomp_to_state
    apply (subst RES_RETURN_RES)
    apply (rule RES_refine)
    unfolding in_pair_collect_simp bex_simps
    using that apply (auto 5 5 simp:  get_all_ann_decomposition_convert_lits_l twl_st_l
        intro!: RES_refine exI[of _ \<open>convert_lits_l (get_clauses_l S)  _\<close>])
    apply force
    apply (auto simp: twl_st_l_def)
    done

  have list_of_mset: \<open>list_of_mset D' \<le> SPEC (\<lambda>c. (c, D'') \<in> {(c, D). D = mset c})\<close>
    if \<open>D' = D''\<close> for D' :: \<open>'v clause\<close> and D''
    using that by (cases D'') (auto simp: list_of_mset_def)
  have ext: \<open>extract_shorter_conflict_l T
    \<le> \<Down> {(S, S'). (S, S') \<in> twl_st_l None \<and> -lit_of (hd (get_trail_l S)) \<in># the (get_conflict_l S) \<and>
       the (get_conflict_l S) \<subseteq># the D\<^sub>0 \<and> equality_except_conflict_l T S \<and> get_conflict_l S \<noteq> None}
       (extract_shorter_conflict T')\<close>
    (is \<open>_ \<le>  \<Down> ?extract _\<close>)
    if \<open>(T, T') \<in> twl_st_l None\<close> and
      \<open>D\<^sub>0 = get_conflict_l T\<close> and
      \<open>get_trail_l T \<noteq> []\<close>
    for T T' and D\<^sub>0
    unfolding extract_shorter_conflict_l_alt_def extract_shorter_conflict_alt_def
    apply (rule RES_refine)
    unfolding in_pair_collect_simp bex_simps
    apply clarify
    apply (rule_tac x=\<open>set_conflict' (Some D') T'\<close> in bexI)
    using that
     apply (auto simp del: split_paired_Ex equality_except_conflict_l.simps
        simp: set_conflict'_def[unfolded state_decomp_to_state] twl_st_l
        intro!: RES_refine equality_except_conflict_alt_def[THEN iffD2]
        del: split_paired_all)
    apply (auto simp: twl_st_l_def equality_except_conflict_l_alt_def)
    done

  have uhd_in_D: \<open>L \<in># the D\<close>
    if
      inv_s: \<open>twl_stgy_invs S'\<close> and
      inv: \<open>twl_struct_invs S'\<close> and
      ns: \<open>no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of S')\<close> and
      confl:
         \<open>conflicting (state\<^sub>W_of S') \<noteq> None\<close>
         \<open>conflicting (state\<^sub>W_of S') \<noteq> Some {#}\<close> and
      M_nempty: \<open>get_trail_l S \<noteq> []\<close> and
      D: \<open>D = get_conflict_l S\<close>
         \<open>L = - lit_of (hd (get_trail_l S))\<close> and
      SS': \<open>(S, S') \<in> twl_st_l None\<close>
    for L M D and S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st\<close>
    unfolding D
    using cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of \<open>state\<^sub>W_of S'\<close>,
      OF _ _ ns confl] that
    by (auto simp: cdcl\<^sub>W_restart_mset_state twl_stgy_invs_def
       twl_struct_invs_def twl_st_l twl_st)

  have find_lit:
    \<open>find_lit_of_max_level U (lit_of (hd (get_trail_l S)))
    \<le> SPEC (\<lambda>L''. L'' \<in># remove1_mset (- lit_of (hd (get_trail S'))) (the (get_conflict U')) \<and>
              lit_of (hd (get_trail S')) \<noteq> - L'' \<and>
              get_level (get_trail U') L'' = get_maximum_level (get_trail U')
                (remove1_mset (- lit_of (hd (get_trail S'))) (the (get_conflict U'))))\<close>
   (is \<open>_ \<le> RES ?find_lit_of_max_level\<close>)
    if
      UU': \<open>(S, S') \<in> ?R\<close> and
      bt_inv: \<open>backtrack_l_inv S\<close> and
      RR': \<open>(T, T') \<in> ?extract S (get_conflict_l S)\<close> and
      T: \<open>(U, U') \<in> ?find_decomp T\<close>
    for S S' T T' U U'
  proof -
    have SS': \<open>(S, S') \<in> twl_st_l None\<close> \<open>get_trail_l S \<noteq> []\<close> and
      struct_invs: \<open>twl_struct_invs S'\<close> \<open>get_conflict_l S \<noteq> None\<close>
      using UU' bt_inv by (auto simp: backtrack_l_inv_def)
    have \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of S')\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    then have dist: \<open>distinct_mset (the (get_conflict_l S))\<close>
      using struct_invs SS' unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      by (cases S) (auto simp: cdcl\<^sub>W_restart_mset_state twl_st_l twl_st)
    then have dist: \<open>distinct_mset (the (get_conflict_l U))\<close>
      using UU' RR' T by (cases S, cases T, cases U, auto intro: distinct_mset_mono)
    show ?thesis
      using T distinct_mem_diff_mset[OF dist, of _ \<open>{#_#}\<close>] SS'
      unfolding find_lit_of_max_level_def
        state_decomp_to_state_l
      by (force simp: twl_st_l uminus_lit_swap)
  qed

  have propagate_bt:
    \<open>propagate_bt_l (lit_of (hd (get_trail_l S))) L U
    \<le> SPEC (\<lambda>c. (c, propagate_bt (lit_of (hd (get_trail S'))) L' U') \<in>
        {(T, T'). (T, T') \<in> twl_st_l None \<and> clauses_to_update_l T = {#} \<and> twl_list_invs T})\<close>
    if
      SS': \<open>(S, S') \<in> ?R\<close> and
      bt_inv: \<open>backtrack_l_inv S\<close> and
      TT': \<open>(T, T') \<in> ?extract S (get_conflict_l S)\<close> and
      UU': \<open>(U, U') \<in> ?find_decomp T\<close> and
      L': \<open>L' \<in> ?find_lit_of_max_level S' U'\<close> and
      LL':  \<open>(L, L') \<in> Id\<close> and
      size: \<open>size (the (get_conflict_l U)) > 1\<close>
     for S S' T T' U U' L L'
  proof -
    obtain MS NS DS NES UES where
      S: \<open>S = (MS, NS, Some DS, NES, UES, {#}, {#})\<close> and
      S_S': \<open>(S, S') \<in> twl_st_l None\<close> and
      add_invs: \<open>twl_list_invs S\<close>
      using SS' by (cases S; cases \<open>get_conflict_l S\<close>) auto
    then obtain DT where
      T: \<open>T = (MS, NS, Some DT, NES, UES, {#}, {#})\<close> and
      T_T': \<open>(T, T') \<in> twl_st_l None\<close>
      using TT' by (cases T; cases \<open>get_conflict_l T\<close>) auto
    then obtain MU MU' where
      U: \<open>U = (MU, NS, Some DT, NES, UES, {#}, {#})\<close> and
      MU: \<open>MS = MU' @ MU\<close> and
      U_U': \<open>(U, U') \<in> twl_st_l None\<close>
      using UU' by (cases U) auto
    have [simp]: \<open>L = L'\<close>
      using LL' by simp
    have [simp]: \<open>convert_lits_l (fmupd i C' NS) MU = convert_lits_l NS MU\<close>
      if \<open>i \<notin># dom_m NS\<close> for NS' i C'
      unfolding convert_lits_l_def
      apply (rule map_cong)
      subgoal by simp
      subgoal for x using add_invs that
        by (cases x; auto 5 5 simp: twl_list_invs_def nth_append S MU)
      done
    have [simp]: \<open>MS \<noteq> []\<close> and add_invs: \<open>twl_list_invs S\<close>
      using SS' bt_inv unfolding twl_list_invs_def backtrack_l_inv_def S by auto
    have \<open>Suc 0 < size DT\<close>
      using size by (auto simp: U)
    then have \<open>DS \<noteq> {#}\<close>
      using TT' by (auto simp: S T)
    then have \<open>- lit_of (hd MS) \<in># DS\<close>
      using bt_inv cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of \<open>state\<^sub>W_of S'\<close>]
        size S_S'
      unfolding backtrack_l_inv_def by (auto simp: twl_struct_invs_def twl_stgy_invs_def
        cdcl\<^sub>W_restart_mset_state U S twl_st_l_def)
    then have \<open>- lit_of (hd MS) \<in># DT\<close>
      using TT' by (auto simp: T)
    moreover have \<open>L' \<in># remove1_mset (- lit_of (hd MS)) DT\<close>
      using L' S_S' U_U' by (auto simp: S U twl_st_l)
    ultimately have DT:
      \<open>DT = add_mset (- lit_of (hd MS)) (add_mset L' (DT - {#- lit_of (hd MS), L'#}))\<close>
      by (metis (no_types, lifting) add_mset_diff_bothsides diff_single_eq_union)

    have Propa:
      \<open>((Propagated (- lit_of (hd MS)) i # MU,
         fmupd i (- lit_of (hd MS) # L # remove1 (- lit_of (hd MS)) (remove1 L xa), False) NS,
             None, NES, UES, {#}, unmark (hd MS)),
            case U' of
            (M, N, U, D, NE, UE, WS, Q) \<Rightarrow>
              (Propagated (- lit_of (hd (get_trail S'))) (the D) # M, N,
               add_mset
                (TWL_Clause {#- lit_of (hd (get_trail S')), L'#}
                  (the D - {#- lit_of (hd (get_trail S')), L'#}))
                U,
               None, NE, UE, WS, unmark (hd (get_trail S'))))
           \<in> twl_st_l None\<close>
      if
       [symmetric, simp]: \<open>DT = mset xa\<close> and
       i_dom: \<open>i \<notin># dom_m NS\<close> and
      \<open>i > 0\<close>
      for i xa
      using U_U' S_S' T_T' i_dom  \<open>i > 0\<close> DT apply (cases U')
      by (auto simp: U twl_st_l_def hd_get_trail_twl_st_of_get_trail_l S
        init_clss_l_mapsto_upd_irrel_notin learned_clss_l_mapsto_upd_notin)
    have [simp]: \<open>Ex Not\<close>
      by auto
    show ?thesis
      unfolding propagate_bt_l_def list_of_mset_def propagate_bt_def U RES_RETURN_RES
        get_fresh_index_def RES_RES_RETURN_RES
      apply clarify
      apply (rule RES_rule)
      apply (subst in_pair_collect_simp)
      apply (intro conjI)
      subgoal using Propa
         by (auto simp: hd_get_trail_twl_st_of_get_trail_l S T U)
      subgoal by auto
      subgoal using add_invs \<open>L = L'\<close> by (auto simp: S twl_list_invs_def MU simp del: \<open>L = L'\<close>)
      done
  qed

  have propagate_unit_bt:
    \<open>(propagate_unit_bt_l (lit_of (hd (get_trail_l S))) U,
      propagate_unit_bt (lit_of (hd (get_trail S'))) U')
     \<in> {(T, T'). (T, T') \<in> twl_st_l None \<and> clauses_to_update_l T = {#} \<and> twl_list_invs T}\<close>
    if
      SS': \<open>(S, S') \<in> ?R\<close> and
      bt_inv: \<open>backtrack_l_inv S\<close> and
      TT': \<open>(T, T') \<in> ?extract S (get_conflict_l S)\<close> and
      UU': \<open>(U, U') \<in> ?find_decomp T\<close> and
      size: \<open>\<not>size (the (get_conflict_l U)) > 1\<close>
     for S S' T T' U U' L L'
  proof -
    obtain MS NS DS NES UES where
      S: \<open>S = (MS, NS, Some DS, NES, UES, {#}, {#})\<close>
      using SS' by (cases S; cases \<open>get_conflict_l S\<close>) auto
    then obtain DT where
      T: \<open>T = (MS, NS, Some DT, NES, UES, {#}, {#})\<close>
      using TT' by (cases T; cases \<open>get_conflict_l T\<close>) auto
    then obtain MU MU' where
      U: \<open>U = (MU, NS, Some DT, NES, UES, {#}, {#})\<close> and
      MU: \<open>MS = MU' @ MU\<close>
      using UU' by (cases U) auto
    have S'_S: \<open>(S, S') \<in> twl_st_l None\<close>
      using SS' by simp
    have U'_U: \<open>(U, U') \<in> twl_st_l None\<close>
      using UU' by simp

    have [simp]: \<open>MS \<noteq> []\<close> and add_invs: \<open>twl_list_invs S\<close>
      using SS' bt_inv unfolding twl_list_invs_def backtrack_l_inv_def S by auto
    have DT: \<open>DT = {#- lit_of (hd MS)#}\<close>
      using TT' size by (cases DT, auto simp: U T)
    show ?thesis
      apply (subst in_pair_collect_simp)
      apply (intro conjI)
      subgoal
        using S'_S U'_U by (auto simp: twl_st_l_def propagate_unit_bt_def propagate_unit_bt_l_def
         S T U DT)
      subgoal by (auto simp: propagate_unit_bt_def propagate_unit_bt_l_def S T U DT)
      subgoal using add_invs S'_S unfolding S T U twl_list_invs_def propagate_unit_bt_l_def
        by (auto 5 5 simp: propagate_unit_bt_l_def DT
        twl_list_invs_def MU twl_st_l_def)
      done
  qed

  have bt:
    \<open>(backtrack_l, backtrack) \<in> ?R \<rightarrow>\<^sub>f
    \<langle>{(T::'v twl_st_l, T'). (T, T') \<in> twl_st_l None \<and> clauses_to_update_l T = {#} \<and>
        twl_list_invs T}\<rangle> nres_rel\<close>
    (is \<open>_ \<in> _ \<rightarrow>\<^sub>f \<langle>?I'\<rangle>nres_rel\<close>)
    supply [[goals_limit=1]]
    unfolding backtrack_l_def backtrack_def fref_param1[symmetric]
    apply (refine_vcg H list_of_mset ext; remove_dummy_vars)
    subgoal for S S'
      unfolding backtrack_l_inv_def
      apply (rule_tac x=S' in exI)
     by (auto simp: backtrack_inv_def backtrack_l_inv_def twl_st_l)
    subgoal by (auto simp: convert_lits_l_def elim: neq_NilE)
    subgoal unfolding backtrack_inv_def by (auto simp add: twl_st_l)
    subgoal by simp
    subgoal by (auto simp: backtrack_inv_def equality_except_conflict_l_rewrite)
    subgoal by (auto simp: hd_get_trail_twl_st_of_get_trail_l backtrack_l_inv_def equality_except_conflict_l_rewrite)
    subgoal by (auto simp: propagate_bt_l_def propagate_bt_def backtrack_l_inv_def equality_except_conflict_l_rewrite)
    subgoal by (auto simp: twl_st_l)
    subgoal by (rule find_lit) assumption+
    subgoal by (rule propagate_bt) assumption+
    subgoal by (rule propagate_unit_bt) assumption+
    done
  have SPEC_Id: \<open>SPEC \<Phi> = \<Down> {(T, T'). \<Phi> T} (SPEC \<Phi>)\<close> for \<Phi>
    unfolding conc_fun_RES
    by auto
  have \<open>(backtrack_l S, backtrack S') \<in> ?I\<close> if \<open>(S, S') \<in> ?R\<close> for S S'
  proof -
    have \<open>backtrack_l S \<le> \<Down> ?I' (backtrack S')\<close>
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
  \<open>find_unassigned_lit_l = (\<lambda>(M, N, D, NE, UE, WS, Q).
     SPEC (\<lambda>L.
         (L \<noteq> None \<longrightarrow>
            undefined_lit M (the L) \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf N + NE)) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit M L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf N + NE))))
     )\<close>

definition decide_l_or_skip_pre where
\<open>decide_l_or_skip_pre S \<longleftrightarrow> (\<exists>S'. (S, S') \<in> twl_st_l None \<and>
   twl_struct_invs S' \<and>
   twl_stgy_invs S' \<and>
   twl_list_invs S \<and>
   get_conflict_l S = None \<and>
   clauses_to_update_l S = {#} \<and>
   literals_to_update_l S = {#})
  \<close>


definition decide_lit_l :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>decide_lit_l = (\<lambda>L' (M, N, D, NE, UE, WS, Q).
      (Decided L' # M, N, D, NE, UE, WS, {#- L'#}))\<close>

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
    by (cases S)
      (auto simp: find_unassigned_lit_l_def find_unassigned_lit_def
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
    moreover have \<open> decide_or_skip S'
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
      by (rule decide_or_skip_spec[of S', unfolded KK]) (use SS' in \<open>auto simp: twl_st_l\<close>)
    ultimately show \<open>decide_l_or_skip S \<le> \<Down> ?S (decide_or_skip S')\<close>
      apply -
      apply unify_Down_invs2+
      apply (simp only: nf set)
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

lemma cdcl_twl_o_prog_l_spec:
  \<open>(cdcl_twl_o_prog_l, cdcl_twl_o_prog) \<in>
    {(S, S'). (S, S') \<in> twl_st_l None \<and>
       clauses_to_update_l S = {#} \<and> literals_to_update_l S = {#} \<and> no_step cdcl_twl_cp S' \<and>
       twl_struct_invs S' \<and> twl_stgy_invs S' \<and> twl_list_invs S} \<rightarrow>\<^sub>f
    \<langle>{((brk, T), (brk', T')). (T, T') \<in> twl_st_l None \<and> brk = brk' \<and> twl_list_invs T \<and> clauses_to_update_l T = {#} \<and>
    (get_conflict_l T \<noteq> None \<longrightarrow> count_decided (get_trail_l T) = 0)\<and>
       twl_struct_invs T' \<and> twl_stgy_invs T'}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow>\<^sub>f ?I\<close> is \<open> _ \<in> ?R \<rightarrow>\<^sub>f \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have twl_prog:
    \<open>(cdcl_twl_o_prog_l, cdcl_twl_o_prog) \<in> ?R \<rightarrow>\<^sub>f
      \<langle>{((brk, S), (brk', S')).
         (brk = brk' \<and> (S, S') \<in> twl_st_l None) \<and> twl_list_invs S \<and>
         clauses_to_update_l S = {#}}\<rangle> nres_rel\<close>
     (is \<open>_ \<in> _ \<rightarrow>\<^sub>f \<langle>?I'\<rangle> nres_rel\<close>)
    supply [[goals_limit=3]]
    unfolding cdcl_twl_o_prog_l_def cdcl_twl_o_prog_def
      find_unassigned_lit_def fref_param1[symmetric]
    apply (refine_vcg
        decide_l_or_skip_spec[THEN fref_to_Down, THEN "weaken_\<Down>'"]
        skip_and_resolve_loop_l_spec[THEN fref_to_Down]
        backtrack_l_spec[THEN fref_to_Down]; remove_dummy_vars)
    subgoal for S S'
      unfolding cdcl_twl_o_prog_l_pre_def by (rule exI[of _ S']) (force simp: twl_st_l)
    subgoal by (auto simp: twl_st_l)
    subgoal by simp
    subgoal by (auto simp: twl_st_l)
    subgoal by (auto simp: twl_st_l)
    subgoal by (auto simp: twl_st_l)
    subgoal by (auto simp: twl_st_l)
    subgoal by (auto simp: twl_st_l)
    subgoal by (auto simp: twl_st_l)
    subgoal by (auto simp: twl_st_l)
    subgoal by (auto simp: twl_st_l)
    done
  have set: \<open>{((a,b), (a', b')). P a b a' b'} = {(a, b). P (fst a) (snd a) (fst b) (snd b)}\<close> for P
    by auto
  have SPEC_Id: \<open>SPEC \<Phi> = \<Down> {(T, T'). \<Phi> T} (SPEC \<Phi>)\<close> for \<Phi>
    unfolding conc_fun_RES
    by auto
  show bt': ?thesis
  proof (intro frefI nres_relI)
    fix S S'
    assume SS': \<open>(S, S') \<in> ?R\<close>
    have \<open>cdcl_twl_o_prog S' \<le> SPEC (cdcl_twl_o_prog_spec S')\<close>
      by (rule cdcl_twl_o_prog_spec[of S']) (use SS' in \<open>auto simp: twl_st_l\<close>)
    moreover have \<open>cdcl_twl_o_prog_l S \<le> \<Down> ?I' (cdcl_twl_o_prog S')\<close>
      by (rule twl_prog[unfolded fref_param1[symmetric], "to_\<Down>"])
        (use SS' in \<open>auto simp: twl_st_l\<close>)
    ultimately show \<open>cdcl_twl_o_prog_l S \<le> \<Down> ?J (cdcl_twl_o_prog S')\<close>
      apply -
      unfolding set
      apply (subst(asm) SPEC_Id)
      apply unify_Down_invs2+
      apply ("match_\<Down>")
      subgoal by (clarsimp simp del: split_paired_All simp: twl_st_l_def)
      subgoal by simp
      done
  qed
qed


subsection \<open>Full Strategy\<close>

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
    {(S, S'). (S, S') \<in> twl_st_l None  \<and> twl_list_invs S \<and>
       clauses_to_update_l S = {#} \<and>
       twl_struct_invs S' \<and> twl_stgy_invs S'} \<rightarrow>\<^sub>f
    \<langle>{(T, T'). (T, T') \<in> twl_st_l None \<and> True}\<rangle> nres_rel\<close>
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
      by (auto simp: twl_st_l[symmetric])
    subgoal by auto
    subgoal by fastforce
    subgoal by (auto simp: twl_st_l)
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
    using assms unfolding cdcl_twl_stgy_prog_l_pre_def by (auto simp: twl_st_l)
  done

end
