theory IsaSAT_Restart
  imports Watched_Literals_Watch_List_Domain_Restart  IsaSAT_Setup
begin


fun (in -) partial_correct_watching :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  [simp del]: \<open>partial_correct_watching (M, N, D, NE, UE, Q, W)  \<longleftrightarrow>
     (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf N + NE + UE).
       (\<forall>i\<in>set (W L). i \<notin># dom_m N \<or> L \<in> set (

end