theory Two_Watched_Literals_List_Restart
  imports Two_Watched_Literals_List Two_Watched_Literals_Algorithm_Restart
begin

abbreviation map_proped_lits :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> ('v, nat) ann_lits \<Rightarrow> ('v, nat) ann_lits\<close> where
  \<open>map_proped_lits f \<equiv> map (map_annotated_lit id id f)\<close>

context twl_restart
begin

definition (in -) derive_literals_and_clauses where
 \<open>derive_literals_and_clauses M N U N' new_pos \<longleftrightarrow>
    (\<forall>i\<in>{1..<length N}. new_pos i \<noteq> None \<longrightarrow> the (new_pos i) < length N' \<and>
                      N'!(the (new_pos i)) = N !i) \<and>
             mset (tl N') \<subseteq># mset (tl N) \<and>
             (\<forall>L C. Propagated L C  \<in> set M \<longrightarrow> new_pos C \<noteq> None) \<and>
             (\<forall>i < U. new_pos i = Some i) \<and>
             (\<forall>i < length N'. \<exists>j < length N. new_pos j = Some i \<and> N'!i = N!j)\<close>

definition restart_prog_clss_list :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>restart_prog_clss_list = (\<lambda>(M, N, U, D, NP, UP, WS, Q). do {
     (N', new_pos) \<leftarrow> SPEC(\<lambda>(N', new_pos).
             derive_literals_and_clauses M N U N' new_pos);
     RETURN ((map_proped_lits (the o new_pos) M, N', U, D, NP, UP, WS, Q))
  })\<close>

definition cdcl_twl_restart_only:: \<open>'v twl_st \<Rightarrow> ('v twl_st) nres\<close>  where
  \<open>cdcl_twl_restart_only = (\<lambda>S. SPEC(\<lambda>T. cdcl_twl_restart S T))\<close>

lemma cdcl_twl_o_prog_l_spec:
  \<open>(restart_prog_clss_list, cdcl_twl_restart_only) \<in>
    {(S, S'). S' = twl_st_of None S \<and> literals_to_update_l S = {#} \<and>
       twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and> twl_list_invs S} \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of None T \<and> twl_list_invs T \<and> clauses_to_update_l T = {#} \<and>
       twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T)}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close> is \<open> _ \<in> ?R \<rightarrow> \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have corr:
    \<open>RETURN (map_proped_lits (the \<circ> new_pos) M, N', u, D, NP, UP, WS, Q)
      \<le> \<Down> {(T, T').
            T' = twl_st_of None T \<and>
            twl_list_invs T \<and>
            clauses_to_update_l T = {#} \<and>
            twl_struct_invs (twl_st_of None T) \<and>
            twl_stgy_invs (twl_st_of None T)}
          (SPEC (cdcl_twl_restart S))\<close>
    if
      \<open>((M, N, u, D, NP, UP, WS, Q), S)
     \<in> {(S, S').
         S' = twl_st_of None S \<and>
         literals_to_update_l S = {#} \<and>
         twl_struct_invs (twl_st_of None S) \<and>
         twl_stgy_invs (twl_st_of None S) \<and> twl_list_invs S}\<close> and
      \<open>(N', new_pos) \<in> {(x, y). derive_literals_and_clauses M N u x y}\<close>
    for S M N u D NP UP WS Q N' new_pos
  proof -
    show ?thesis
      apply (subst RETURN_RES_refine_iff)
      apply (auto intro!: cdcl_twl_restart.intros(2))
      sorry
  qed
  show ?thesis
    unfolding restart_prog_clss_list_def cdcl_twl_restart_only_def
    by (refine_vcg corr; remove_dummy_vars)
  oops

end

end