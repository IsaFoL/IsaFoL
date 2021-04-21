theory IsaSAT_Restart_Inprocessing
  imports IsaSAT_Restart
    Watched_Literals.Watched_Literals_Watch_List_Inprocessing
begin
thm simplify_clause_with_unit_def

definition simplify_clause_with_unit2 where
  \<open>simplify_clause_with_unit2 C M N = do {
      ASSERT(C \<in># dom_m N);
      (i, j, N, is_true) \<leftarrow> WHILE\<^sub>T(\<lambda>(i, j, N, b). \<not>b \<and> j < length (N \<propto> C))
        (\<lambda>(i, j, N, b). do {
           let L = N \<propto> C ! i;
           if L \<in> lits_of_l M then RETURN (i, j+1, fmdrop C N, True)
           else if  -L \<in> lits_of_l M
         then RETURN (i, j+1, fmdrop C N, True)
           else RETURN (i+1, j+1, N(C \<hookrightarrow> ((N \<propto> C)[i := L])), True)
        })
        (0, 0, N, False);
     if is_true \<or> i \<le> 1
    then  RETURN (fmdrop C N, is_true)
    else RETURN (N(C \<hookrightarrow> (take i (N \<propto> C))), is_true)
  }\<close>
end