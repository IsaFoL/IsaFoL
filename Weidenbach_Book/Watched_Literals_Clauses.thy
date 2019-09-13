theory Watched_Literals_Clauses
imports WB_More_Refinement_List  Watched_Literals_Algorithm
begin

type_synonym 'v clause_l = \<open>'v literal list\<close>
type_synonym 'v clauses_l = \<open>(nat, ('v clause_l \<times> bool)) fmap\<close>

abbreviation watched_l :: \<open>'a clause_l \<Rightarrow> 'a clause_l\<close> where
  \<open>watched_l l \<equiv> take 2 l\<close>

abbreviation unwatched_l :: \<open>'a clause_l \<Rightarrow> 'a clause_l\<close>  where
  \<open>unwatched_l l \<equiv> drop 2 l\<close>

fun twl_clause_of :: \<open>'a clause_l \<Rightarrow> 'a clause twl_clause\<close> where
  \<open>twl_clause_of l = TWL_Clause (mset (watched_l l)) (mset (unwatched_l l))\<close>

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

definition irred' where \<open>irred' = irred\<close>

lemma ran_m_ran: \<open>fset_mset (ran_m N) = fmran N\<close>
  unfolding ran_m_def ran_def
  apply (auto simp: fmlookup_ran_iff dom_m_def elim!: fmdomE)
   apply (metis fmdomE notin_fset option.sel)
  by (metis (no_types, lifting) fmdomI fmember.rep_eq image_iff option.sel)

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

lemma learned_clss_l_update[simp]:
  \<open>bh \<in># dom_m ax \<Longrightarrow> size (learned_clss_l (ax(bh \<hookrightarrow> C))) = size (learned_clss_l ax)\<close>
  by (auto simp: ran_m_clause_upd size_Diff_singleton_if dest!: multi_member_split)
     (auto simp: ran_m_def)

lemma Ball_ran_m_dom:
  \<open>(\<forall>x\<in>#ran_m N. P (fst x)) \<longleftrightarrow> (\<forall>x\<in>#dom_m N. P (N \<propto> x))\<close>
  by (auto simp: ran_m_def)

lemma Ball_ran_m_dom_struct_wf:
  \<open>(\<forall>x\<in>#ran_m N. struct_wf_twl_cls (twl_clause_of (fst x))) \<longleftrightarrow>
     (\<forall>x\<in># dom_m N. struct_wf_twl_cls (twl_clause_of (N \<propto> x)))\<close>
  by (rule Ball_ran_m_dom)

lemma init_clss_lf_fmdrop[simp]:
  \<open>irred N C \<Longrightarrow> C \<in># dom_m N \<Longrightarrow> init_clss_lf (fmdrop C N) = remove1_mset (N\<propto>C) (init_clss_lf N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)

lemma init_clss_lf_fmdrop_irrelev[simp]:
  \<open>\<not>irred N C \<Longrightarrow> init_clss_lf (fmdrop C N) = init_clss_lf N\<close>
  using distinct_mset_dom[of N]
  apply (cases \<open>C \<in># dom_m N\<close>)
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)

lemma learned_clss_lf_lf_fmdrop[simp]:
  \<open>\<not>irred N C \<Longrightarrow> C \<in># dom_m N \<Longrightarrow> learned_clss_lf (fmdrop C N) = remove1_mset (N\<propto>C) (learned_clss_lf N)\<close>
  using distinct_mset_dom[of N]
  apply (cases \<open>C \<in># dom_m N\<close>)
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)

lemma learned_clss_l_l_fmdrop: \<open>\<not> irred N C \<Longrightarrow> C \<in># dom_m N \<Longrightarrow>
  learned_clss_l (fmdrop C N) = remove1_mset (the (fmlookup N C)) (learned_clss_l N)\<close>
  using distinct_mset_dom[of N]
  apply (cases \<open>C \<in># dom_m N\<close>)
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)

lemma learned_clss_lf_lf_fmdrop_irrelev[simp]:
  \<open>irred N C \<Longrightarrow> learned_clss_lf (fmdrop C N) = learned_clss_lf N\<close>
  using distinct_mset_dom[of N]
  apply (cases \<open>C \<in># dom_m N\<close>)
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)

lemma ran_mf_lf_fmdrop[simp]:
  \<open>C \<in># dom_m N \<Longrightarrow>  ran_mf (fmdrop C N) = remove1_mset (N\<propto>C) (ran_mf N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ \<open>\<lambda>x. fst (the x)\<close>] dest!: multi_member_split)

lemma ran_mf_lf_fmdrop_notin[simp]:
  \<open>C \<notin># dom_m N \<Longrightarrow>  ran_mf (fmdrop C N) = ran_mf N\<close>
  using distinct_mset_dom[of N]
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ \<open>\<lambda>x. fst (the x)\<close>] dest!: multi_member_split)

lemma lookup_None_notin_dom_m[simp]:
  \<open>fmlookup N i = None \<longleftrightarrow> i \<notin># dom_m N\<close>
  by (auto simp: dom_m_def fmlookup_dom_iff fmember.rep_eq[symmetric])

text \<open>While it is tempting to mark the two following theorems as [simp], this would break more
  simplifications since \<^term>\<open>ran_mf\<close> is only an abbreviation for \<^term>\<open>ran_m\<close>.
\<close>
lemma ran_m_fmdrop:
  \<open>C \<in># dom_m N \<Longrightarrow>  ran_m (fmdrop C N) = remove1_mset (N \<propto> C, irred N C) (ran_m N)\<close>
  using distinct_mset_dom[of N]
  by (cases \<open>fmlookup N C\<close>)
    (auto simp: ran_m_def image_mset_If_eq_notin[of C _ \<open>\<lambda>x. fst (the x)\<close>]
     dest!: multi_member_split
    intro!: filter_mset_cong2 image_mset_cong2)

lemma ran_m_fmdrop_notin:
  \<open>C \<notin># dom_m N \<Longrightarrow> ran_m (fmdrop C N) = ran_m N\<close>
  using distinct_mset_dom[of N]
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ \<open>\<lambda>x. fst (the x)\<close>]
    dest!: multi_member_split
    intro!: filter_mset_cong2 image_mset_cong2)

lemma init_clss_l_fmdrop_irrelev:
  \<open>\<not>irred N C \<Longrightarrow> init_clss_l (fmdrop C N) = init_clss_l N\<close>
  using distinct_mset_dom[of N]
  apply (cases \<open>C \<in># dom_m N\<close>)
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)

lemma init_clss_l_fmdrop:
  \<open>irred N C \<Longrightarrow> C \<in># dom_m N \<Longrightarrow> init_clss_l (fmdrop C N) = remove1_mset (the (fmlookup N C)) (init_clss_l N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)

lemma ran_m_lf_fmdrop:
  \<open>C \<in># dom_m N \<Longrightarrow> ran_m (fmdrop C N) = remove1_mset (the (fmlookup N C)) (ran_m N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ \<open>\<lambda>x. fst (the x)\<close>] dest!: multi_member_split
    intro!: image_mset_cong)
lemma set_clauses_simp[simp]:
  \<open>f ` {a. a \<in># ran_m N \<and> \<not> snd a} \<union> f ` {a. a \<in># ran_m N \<and> snd a} \<union> A =
   f ` {a. a \<in># ran_m N} \<union> A\<close>
  by auto

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

lemma init_clss_l_mapsto_upd_notin:
  \<open>C \<notin># dom_m N \<Longrightarrow> init_clss_l (fmupd C (C', True) N) =
     add_mset (C', True) (init_clss_l N)\<close>
  by (auto simp: ran_m_mapsto_upd_notin)

lemma learned_clss_l_mapsto_upd_notin_irrelev: \<open>C \<notin># dom_m N \<Longrightarrow>
  learned_clss_l (fmupd C  (C', True) N) = learned_clss_l N\<close>
  by (auto simp: ran_m_mapsto_upd_notin)

lemma clause_twl_clause_of:  \<open>clause (twl_clause_of C) = mset C\<close> for C
    by (cases C; cases \<open>tl C\<close>) auto

lemma learned_clss_l_l_fmdrop_irrelev: \<open>irred N C \<Longrightarrow>
  learned_clss_l (fmdrop C N) = learned_clss_l N\<close>
  using distinct_mset_dom[of N]
  apply (cases \<open>C \<in># dom_m N\<close>)
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ the] dest!: multi_member_split)

lemma init_clss_l_fmdrop_if:
  \<open>C \<in># dom_m N \<Longrightarrow> init_clss_l (fmdrop C N) = (if irred N C then remove1_mset (the (fmlookup N C)) (init_clss_l N)
    else init_clss_l N)\<close>
  by (auto simp: init_clss_l_fmdrop init_clss_l_fmdrop_irrelev)

lemma init_clss_l_fmupd_if:
  \<open>C' \<notin># dom_m new \<Longrightarrow> init_clss_l (fmupd C' D new) = (if snd D then add_mset D (init_clss_l new) else init_clss_l new)\<close>
  by (cases D) (auto simp: init_clss_l_mapsto_upd_irrel_notin init_clss_l_mapsto_upd_notin)

lemma learned_clss_l_fmdrop_if:
  \<open>C \<in># dom_m N \<Longrightarrow> learned_clss_l (fmdrop C N) = (if \<not>irred N C then remove1_mset (the (fmlookup N C)) (learned_clss_l N)
    else learned_clss_l N)\<close>
  by (auto simp: learned_clss_l_l_fmdrop learned_clss_l_l_fmdrop_irrelev)

lemma learned_clss_l_fmupd_if:
  \<open>C' \<notin># dom_m new \<Longrightarrow> learned_clss_l (fmupd C' D new) = (if \<not>snd D then add_mset D (learned_clss_l new) else learned_clss_l new)\<close>
  by (cases D) (auto simp: learned_clss_l_mapsto_upd_notin_irrelev
    learned_clss_l_mapsto_upd_notin)



definition op_clauses_at :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v literal\<close> where
\<open>op_clauses_at N C i = N \<propto> C ! i\<close>

definition mop_clauses_at :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v literal nres\<close> where
\<open>mop_clauses_at N C i = do {
   ASSERT(C \<in># dom_m N);
   ASSERT(i < length (N \<propto> C));
   RETURN (N \<propto> C ! i)
}\<close>

lemma mop_clauses_at:
   \<open>(uncurry2 mop_clauses_at, uncurry2 (RETURN ooo op_clauses_at)) \<in>
   [\<lambda>((N, C), i). C \<in># dom_m N \<and> i < length (N \<propto> C)]\<^sub>f
   Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (auto simp: mop_clauses_at_def op_clauses_at_def intro!: frefI nres_relI)

definition mop_clauses_swap :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v clauses_l nres\<close> where
\<open>mop_clauses_swap N C i j = do {
   ASSERT(C \<in># dom_m N);
   ASSERT(i < length (N \<propto> C));
   ASSERT(j < length (N \<propto> C));
   RETURN (N(C \<hookrightarrow> (swap (N \<propto> C) i j)))
}\<close>

definition op_clauses_swap :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v clauses_l\<close> where
\<open>op_clauses_swap N C i j = (N(C \<hookrightarrow> (swap (N \<propto> C) i j)))\<close>

lemma mop_clauses_swap:
   \<open>(uncurry3 mop_clauses_swap, uncurry3 (RETURN oooo op_clauses_swap)) \<in>
   [\<lambda>(((N, C), i), j). C \<in># dom_m N \<and> i < length (N \<propto> C) \<and> j < length (N \<propto> C)]\<^sub>f
   Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (auto simp: mop_clauses_swap_def op_clauses_swap_def intro!: frefI nres_relI)


lemma mop_clauses_at_itself:
  \<open>(uncurry2 mop_clauses_at, uncurry2 mop_clauses_at) \<in> Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (auto intro!: frefI nres_relI)

lemma mop_clauses_at_itself_spec:
  \<open>((N, C, i), (N', C', i')) \<in> Id \<Longrightarrow>
     mop_clauses_at N C i \<le> \<Down> {(L, L'). L = L' \<and> L = N \<propto> C ! i} (mop_clauses_at N' C' i')\<close>
  by (auto intro!: frefI nres_relI ASSERT_refine_right simp: mop_clauses_at_def)

lemma mop_clauses_at_itself_spec2:
  \<open>((N, C, i), (N', C', i')) \<in> Id \<Longrightarrow>
     mop_clauses_at N C i \<le> \<Down> {(L, L'). L = L' \<and> L = N \<propto> C ! i \<and> C \<in># dom_m N \<and> i < length (N \<propto> C)}
      (mop_clauses_at N' C' i')\<close>
  by (auto intro!: frefI nres_relI ASSERT_refine_right simp: mop_clauses_at_def)

lemma mop_clauses_at_op_clauses_at_spec2:
  \<open>((N, C, i), (N', C', i')) \<in> Id \<Longrightarrow> C \<in># dom_m N \<and> i < length (N \<propto> C) \<Longrightarrow>
     mop_clauses_at N C i \<le> \<Down> {(L, L'). L = L' \<and> L = N \<propto> C ! i}
      (RETURN (op_clauses_at N' C' i'))\<close>
  by (auto intro!: frefI nres_relI ASSERT_refine_right
   simp: mop_clauses_at_def op_clauses_at_def)

lemma mop_clauses_swap_itself:
  \<open>(uncurry3 mop_clauses_swap, uncurry3 mop_clauses_swap) \<in> Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (auto intro!: frefI nres_relI)

lemma mop_clauses_swap_itself_spec:
  \<open>((N, C, i, j), (N', C', i', j')) \<in> Id \<Longrightarrow>
     mop_clauses_swap N C i j \<le> \<Down> {(L, L'). L = L' \<and> L = op_clauses_swap N' C' i' j' \<and> C' \<in># dom_m N} (mop_clauses_swap N' C' i' j')\<close>
  by (auto intro!: frefI nres_relI ASSERT_refine_right simp: mop_clauses_swap_def
    op_clauses_swap_def)

lemma mop_clauses_swap_itself_spec2:
  \<open>((N, C, i, j), (N', C', i', j')) \<in> Id \<Longrightarrow>
     mop_clauses_swap N C i j \<le> \<Down> {(L, L'). L = L' \<and> L = op_clauses_swap N' C' i' j' \<and> C' \<in># dom_m N \<and>
       i < length (N \<propto> C) \<and> j < length (N \<propto> C)} (mop_clauses_swap N' C' i' j')\<close>
  by (auto intro!: frefI nres_relI ASSERT_refine_right simp: mop_clauses_swap_def
    op_clauses_swap_def)


definition all_lits_of_mm :: \<open>'a clauses \<Rightarrow> 'a literal multiset\<close> where
\<open>all_lits_of_mm Ls = Pos `# (atm_of `# (\<Union># Ls)) + Neg `# (atm_of `# (\<Union># Ls))\<close>

lemma all_lits_of_mm_empty[simp]: \<open>all_lits_of_mm {#} = {#}\<close>
  by (auto simp: all_lits_of_mm_def)
lemma in_all_lits_of_mm_ain_atms_of_iff:
  \<open>L \<in># all_lits_of_mm N \<longleftrightarrow> atm_of L \<in> atms_of_mm N\<close>
  by (cases L) (auto simp: all_lits_of_mm_def atms_of_ms_def atms_of_def)

lemma all_lits_of_mm_union:
  \<open>all_lits_of_mm (M + N) = all_lits_of_mm M + all_lits_of_mm N\<close>
  unfolding all_lits_of_mm_def by auto

definition all_lits_of_m :: \<open>'a clause \<Rightarrow> 'a literal multiset\<close> where
  \<open>all_lits_of_m Ls = Pos `# (atm_of `# Ls) + Neg `# (atm_of `# Ls)\<close>

lemma all_lits_of_m_empty[simp]: \<open>all_lits_of_m {#} = {#}\<close>
  by (auto simp: all_lits_of_m_def)

lemma all_lits_of_m_empty_iff[iff]: \<open>all_lits_of_m A = {#} \<longleftrightarrow> A = {#}\<close>
  by (cases A) (auto simp: all_lits_of_m_def)

lemma in_all_lits_of_m_ain_atms_of_iff: \<open>L \<in># all_lits_of_m N \<longleftrightarrow> atm_of L \<in> atms_of N\<close>
  by (cases L) (auto simp: all_lits_of_m_def atms_of_ms_def atms_of_def)

lemma in_clause_in_all_lits_of_m: \<open>x \<in># C \<Longrightarrow> x \<in># all_lits_of_m C\<close>
  using atm_of_lit_in_atms_of in_all_lits_of_m_ain_atms_of_iff by blast

lemma all_lits_of_mm_add_mset:
  \<open>all_lits_of_mm (add_mset C N) = (all_lits_of_m C) + (all_lits_of_mm N)\<close>
  by (auto simp: all_lits_of_mm_def all_lits_of_m_def)

lemma all_lits_of_m_add_mset:
  \<open>all_lits_of_m (add_mset L C) = add_mset L (add_mset (-L) (all_lits_of_m C))\<close>
  by (cases L) (auto simp: all_lits_of_m_def)

lemma all_lits_of_m_union:
  \<open>all_lits_of_m (A + B) = all_lits_of_m A + all_lits_of_m B\<close>
  by (auto simp: all_lits_of_m_def)

lemma all_lits_of_m_mono:
  \<open>D \<subseteq># D' \<Longrightarrow> all_lits_of_m D \<subseteq># all_lits_of_m D'\<close>
  by (auto elim!: mset_le_addE simp: all_lits_of_m_union)

lemma in_all_lits_of_mm_uminusD: \<open>x2 \<in># all_lits_of_mm N \<Longrightarrow> -x2 \<in># all_lits_of_mm N\<close>
  by (auto simp: all_lits_of_mm_def)

lemma in_all_lits_of_mm_uminus_iff: \<open>-x2 \<in># all_lits_of_mm N \<longleftrightarrow> x2 \<in># all_lits_of_mm N\<close>
  by (cases x2) (auto simp: all_lits_of_mm_def)

lemma all_lits_of_mm_diffD:
  \<open>L \<in># all_lits_of_mm (A - B) \<Longrightarrow> L \<in># all_lits_of_mm A\<close>
  apply (induction A arbitrary: B)
  subgoal by auto
  subgoal for a A' B
    by (cases \<open>a \<in># B\<close>)
      (fastforce dest!: multi_member_split[of a B] simp: all_lits_of_mm_add_mset)+
  done

lemma all_lits_of_mm_mono:
  \<open>set_mset A \<subseteq> set_mset B \<Longrightarrow> set_mset (all_lits_of_mm A) \<subseteq> set_mset (all_lits_of_mm B)\<close>
  by (auto simp: all_lits_of_mm_def)

end