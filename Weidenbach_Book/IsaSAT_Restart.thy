theory IsaSAT_Restart
  imports Watched_Literals_Watch_List_Domain_Restart  IsaSAT_Setup
begin

context isasat_restart_bounded
begin

paragraph \<open>Handle true clauses from the trail\<close>

text \<open>
  Once of the first thing we do, is removing clauses we know to be true. We do in two ways:
    \<^item> along the trail (at level 0);
    \<^item> along the watch list.

  This is obviously not complete but is fast by avoiding iterating over all clauses.
\<close>

definition (in -) extract_and_remove
  :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> ('v clauses_l \<times> 'v clause_l \<times> bool) nres\<close>
where
  \<open>extract_and_remove N j = do {
      ASSERT((j :: nat) \<in># dom_m (N :: 'v clauses_l));
      SPEC(\<lambda>(N' :: 'v clauses_l, C' :: 'v clause_l, b :: bool). N' = N(j \<hookrightarrow> []) \<and> C' = N\<propto>j \<and> b = irred N j)
    }\<close>

fun (in -) partial_correct_watching where
  [simp del]: \<open>partial_correct_watching (M, N, D, NE, UE, Q, W)  \<longleftrightarrow>
     (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + NE).
       (\<forall>i\<in>set (W L). i \<notin># dom_m N \<or> L \<in> set (watched_l (N\<propto>i))))\<close>

lemma (in -) in_set_mset_eq_in:
  \<open>i \<in> set A \<Longrightarrow> mset A = B \<Longrightarrow> i \<in># B\<close>
  by fastforce

lemma (in -) \<open>correct_watching S \<Longrightarrow> partial_correct_watching S\<close>
  by (cases S)
    (auto simp: correct_watching.simps partial_correct_watching.simps clause_to_update_def
    simp del: set_mset_mset dest: in_set_mset_eq_in)

definition remove_all_clause_watched_by :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close> where
\<open>remove_all_clause_watched_by L = (\<lambda>(M, N, D, NE, UE, Q, W). do {
    (_, N, NE, UE) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, N, NE, UE). partial_correct_watching (M, N, D, NE, UE, Q, W)\<^esup>
      (\<lambda>(i, N, NE, UE). i < length (W L))
      (\<lambda>(i, N, NE, UE). do {
          if i \<in># dom_m N
          then do {
            (N', C, b) \<leftarrow> extract_and_remove N (W L!i);
            if b then RETURN (i+1, N', add_mset (mset C) NE, UE)
            else RETURN (i+1, N', NE, add_mset (mset C) UE)
          }
          else (* The clause might have already been deleted *)
            RETURN (i+1, N, NE, UE)
      })
      (0, N, NE, UE);
    RETURN (M, N, D, NE, UE, Q, W)
  })\<close>

end

end