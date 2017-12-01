theory Two_Watched_Literals_List_Restart
  imports Two_Watched_Literals_List Two_Watched_Literals_Algorithm_Restart
begin

abbreviation map_proped_lits :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> ('v, nat) ann_lits \<Rightarrow> ('v, nat) ann_lits\<close> where
  \<open>map_proped_lits f \<equiv> map (map_annotated_lit id id f)\<close>

context twl_restart
begin

definition restart_prog_clss_list :: \<open>'v twl_st_l  \<times> nat \<Rightarrow> ('v twl_st_l \<times> nat) nres\<close> where
  \<open>restart_prog_clss_list = (\<lambda>((M, N, U, D, NP, UP, WS, Q), n). do {
     (N', new_pos) \<leftarrow> SPEC(\<lambda>(N', new_pos). 
             (\<forall>i\<in>{1..<length N}. new_pos i \<noteq> None \<longrightarrow> the (new_pos i) < length N' \<and>
                      N'!(the (new_pos i)) = N !i) \<and>
             mset (tl N') \<subseteq># mset (tl N) \<and>
             (\<forall>L C. Propagated L C  \<in> set M \<longrightarrow> new_pos C \<noteq> None) \<and>
             (\<forall>i < U. new_pos i = Some i) \<and>
             (\<forall>i < length N'. \<exists>j < length N. new_pos j = Some i \<and> N'!i = N!j)
           );
     RETURN ((map_proped_lits (the o new_pos) M, N', U, D, NP, UP, WS, Q), Suc n)
  })\<close>


end

end