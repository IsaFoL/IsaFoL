theory IsaSAT_Show
  imports
    Show.Show_Instances
    IsaSAT_Setup
begin

chapter \<open>Printing information about progress\<close>

text \<open>We provide a function to print some information about the state.
  This is mostly meant to ease extracting statistics and printing information
  during the run.
  Remark that this function is basically an FFI (to follow Andreas Lochbihler words) and is
  not unsafe (since printing has not side effects), but we do not need any correctness theorems.

  However, it seems that the PolyML as targeted by \<open>export_code checking\<close> does
  not support that print function. Therefore, we cannot provide the code printing equations
  by default.

  For the LLVM version code equations are not supported and hence we replace the function by
  hand.
\<close>
definition println_string :: \<open>String.literal \<Rightarrow> unit\<close> where
  \<open>println_string _ = ()\<close>

definition print_c :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_c _ = ()\<close>


definition print_char :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_char _ = ()\<close>

definition print_uint64 :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_uint64 _ = ()\<close>


subsection \<open>Print Information for IsaSAT\<close>

text \<open>Printing the information slows down the solver by a huge factor.\<close>
definition isasat_banner_content where
\<open>isasat_banner_content =
''c  conflicts       decisions     restarts   uset    avg_lbd
'' @
''c        propagations     reductions     GC    Learnt
''  @
''c                                             clauses ''\<close>

definition isasat_information_banner :: \<open>_ \<Rightarrow> unit nres\<close> where
\<open>isasat_information_banner _ =
    RETURN (println_string (String.implode (show isasat_banner_content)))\<close>

definition isasat_current_information_stats :: \<open>64 word \<Rightarrow> isasat_stats \<Rightarrow> clss_size \<Rightarrow> isasat_stats\<close> where
  \<open>isasat_current_information_stats =
   (\<lambda>curr_phase stats (lcount, lcountUE, lcountUEk, lcountUS, _).
     if (stats_conflicts stats) AND 8191 = 8191 \<comment> \<open>\<^term>\<open>8191 = 8192 - 1\<close>, i.e., we print when all first bits are 1.\<close>
     then do{
       let _ = print_c (stats_propagations stats);
         _ = if curr_phase = 1 then print_open_colour 33 else ();
         _ = print_char 126;
         _ = print_uint64 (stats_propagations stats);
         _ = print_uint64 (stats_conflicts stats);
         _ = print_uint64 (of_nat lcount);
         _ = print_uint64 (irredundant_clss stats);
         _ = print_uint64 (stats_restarts stats);
         _ = print_uint64 (stats_reductions stats);
         _ = print_uint64 (stats_fixed stats);
         _ = print_uint64 (stats_gcs stats);
         _ = print_uint64 (ema_extract_value (stats_avg_lbd stats));
         _ = print_uint64 (of_nat lcountUE);
         _ = print_uint64 (of_nat lcountUEk);
         _ = print_uint64 (of_nat lcountUS);
         _ = print_close_colour 0
       in
         stats}
      else stats
    )\<close>

definition isasat_current_information :: \<open>64 word \<Rightarrow> isasat_stats \<Rightarrow> clss_size \<Rightarrow> isasat_stats\<close> where
\<open>isasat_current_information =
  (\<lambda>curr_phase stats count. (isasat_current_information_stats curr_phase stats count)
    )\<close>



definition isasat_current_status :: \<open>isasat \<Rightarrow> isasat nres\<close> where
\<open>isasat_current_status =
   (\<lambda>S.
     let curr_phase = current_restart_phase (get_heur S);
        stats = (isasat_current_information curr_phase (get_stats_heur S) (get_learned_count S))
     in RETURN (set_stats_wl_heur stats S))\<close>

lemma isasat_current_status_id:
  \<open>(isasat_current_status, RETURN o id) \<in>
  {(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) \<le> r \<and> learned_clss_count S \<le> u}  \<rightarrow>\<^sub>f
   \<langle>{(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) \<le> r \<and> learned_clss_count S \<le> u}\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_def isasat_current_status_def learned_clss_count_def)

definition isasat_print_progress :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> isasat_stats \<Rightarrow> clss_size \<Rightarrow> unit\<close> where
\<open>isasat_print_progress c curr_phase =
  (\<lambda>stats (lcount, lcountUE, lcountUEk, lcountUS, _).
     let _ = print_c (stats_propagations stats);
         _ = if curr_phase = 1 then print_open_colour 33 else ();
         _ = print_char c;
         _ = print_uint64 (stats_propagations stats);
         _ = print_uint64 (stats_conflicts stats);
         _ = print_uint64 (of_nat lcount);
         _ = print_uint64 (irredundant_clss stats);
         _ = print_uint64 (stats_restarts stats);
         _ = print_uint64 (stats_reductions stats);
         _ = print_uint64 (stats_fixed stats);
         _ = print_uint64 (stats_gcs stats);
         _ = print_uint64 (ema_extract_value (stats_avg_lbd stats));
         _ = print_uint64 (of_nat lcountUE);
         _ = print_uint64 (of_nat lcountUEk);
         _ = print_uint64 (of_nat lcountUS);
         _ = print_close_colour 0
     in
       ())\<close>

definition isasat_current_progress :: \<open>64 word \<Rightarrow> isasat \<Rightarrow> unit nres\<close> where
\<open>isasat_current_progress =
   (\<lambda>c S.
     let
       curr_phase = current_restart_phase (get_heur S);
       _ = isasat_print_progress c curr_phase (get_stats_heur S) (get_learned_count S)
     in RETURN ())\<close>


end