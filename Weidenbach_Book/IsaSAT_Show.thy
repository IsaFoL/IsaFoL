theory IsaSAT_Show
  imports
    Show.Show_Instances
    IsaSAT_Setup
begin

subsection \<open>Printing information about progress\<close>

text \<open>We provide a function to print some information about the state.
  This is mostly meant to ease extracting statistics and printing information
  during the run.
  Remark that this function is basically an FFI (to follow Andreas Lochbihler words) and is
  not unsafe (since printing has not side effects), but we do not need any correctness theorems.

  However, it seems that the PolyML as targeted by \<open>export_code checking\<close> does
  not support that print function. Therefore, we cannot provide the code printing equations
  by default.\<close>
definition println_string :: \<open>String.literal \<Rightarrow> unit\<close> where
  \<open>println_string _ = ()\<close>



subsection \<open>Print Information for IsaSAT\<close>

definition isasat_header :: string where
  \<open>isasat_header = show ''Conflict | Decision | Propagation | Restarts''\<close>

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

definition zero_some_stats :: \<open>stats \<Rightarrow> stats\<close> where
\<open>zero_some_stats = (\<lambda>(propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds).
     (propa, confl, decs, frestarts, lrestarts, uset, gcs, 0))\<close>

definition isasat_current_information :: \<open>stats \<Rightarrow> _ \<Rightarrow> stats\<close> where
\<open>isasat_current_information =
   (\<lambda>(propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds) lcount.
     if confl AND 8191 = 8191 \<comment> \<open>\<^term>\<open>8191 = 8192 - 1\<close>, i.e., we print when all first bits are 1.\<close>
     then zero_some_stats (propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds)
      else (propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds)
    )\<close>


definition print_current_information :: \<open>stats \<Rightarrow> _ \<Rightarrow> stats\<close> where
\<open>print_current_information = (\<lambda>(propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds) _.
     if confl AND 8191 = 8191 then (propa, confl, decs, frestarts, lrestarts, uset, gcs, 0)
     else (propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds))\<close>


definition isasat_current_status :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
\<open>isasat_current_status =
   (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
       fast_ema, slow_ema, ccount, avdom,
       vdom, lcount, opts, old_arena).
     let stats = (print_current_information stats lcount)
     in RETURN (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
       fast_ema, slow_ema, ccount, avdom,
       vdom, lcount, opts, old_arena))\<close>

lemma isasat_current_status_id:
  \<open>(isasat_current_status, RETURN o id) \<in>
  {(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) \<le> r}  \<rightarrow>\<^sub>f
   \<langle>{(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) \<le> r}\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_def isasat_current_status_def)

end