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

definition print_open_colour :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_open_colour _ = ()\<close>

definition print_close_colour :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_close_colour _ = ()\<close>

definition isasat_current_information :: \<open>64 word \<Rightarrow> stats \<Rightarrow> clss_size \<Rightarrow> stats\<close> where
\<open>isasat_current_information =
   (\<lambda>curr_phase (propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds) (lcount, lcountUE, lcountUS).
     if confl AND 8191 = 8191 \<comment> \<open>\<^term>\<open>8191 = 8192 - 1\<close>, i.e., we print when all first bits are 1.\<close>
     then do{
       let _ = print_c propa;
         _ = if curr_phase = 1 then print_open_colour 33 else ();
         _ = print_char 126;
         _ = print_uint64 propa;
         _ = print_uint64 confl;
         _ = print_uint64 (of_nat lcount);
         _ = print_uint64 frestarts;
         _ = print_uint64 lrestarts;
         _ = print_uint64 uset;
         _ = print_uint64 gcs;
         _ = print_uint64 (ema_extract_value lbds);
         _ = print_uint64 (of_nat lcountUE);
         _ = print_uint64 (of_nat lcountUS);
         _ = print_close_colour 0
       in
         (propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds)}
      else (propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds)
    )\<close>


definition isasat_current_status :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
\<open>isasat_current_status =
   (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats,
       heur, avdom,
       vdom, lcount, opts, old_arena).
     let curr_phase = current_restart_phase heur;
        stats = (isasat_current_information curr_phase stats lcount)
     in RETURN (M', N', D', j, W', vm, clvls, cach, lbd, outl, stats,
       heur, avdom,
       vdom, lcount, opts, old_arena))\<close>

lemma isasat_current_status_id:
  \<open>(isasat_current_status, RETURN o id) \<in>
  {(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) \<le> r \<and> learned_clss_count S \<le> u}  \<rightarrow>\<^sub>f
   \<langle>{(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) \<le> r \<and> learned_clss_count S \<le> u}\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_def isasat_current_status_def learned_clss_count_def)

definition isasat_print_progress :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> stats \<Rightarrow> clss_size \<Rightarrow> unit\<close> where
\<open>isasat_print_progress c curr_phase =
   (\<lambda>(propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds) (lcount, lcountUE, lcountUS).
     let
         _ = print_c propa;
         _ = if curr_phase = 1 then print_open_colour 33 else ();
         _ = print_char (48 + c);
         _ = print_uint64 propa;
         _ = print_uint64 confl;
         _ = print_uint64 (of_nat lcount);
         _ = print_uint64 frestarts;
         _ = print_uint64 lrestarts;
         _ = print_uint64 uset;
         _ = print_uint64 gcs;
         _ = print_uint64 (ema_extract_value lbds);
         _ = print_uint64 (of_nat lcountUE);
         _ = print_uint64 (of_nat lcountUS);
         _ = print_close_colour 0
     in
       ())\<close>


definition isasat_current_progress :: \<open>64 word \<Rightarrow> twl_st_wl_heur \<Rightarrow> unit nres\<close> where
\<open>isasat_current_progress =
   (\<lambda>c (M', N', D', j, W', vm, clvls, cach, lbd, outl, stats,
       heur, avdom,
       vdom, lcount, opts, old_arena).
     let
       curr_phase = current_restart_phase heur;
       _ = isasat_print_progress c curr_phase stats lcount
     in RETURN ())\<close>


end