theory IsaSAT_Restart
  imports Watched_Literals_Watch_List_Domain_Restart  IsaSAT_Setup
begin


text \<open>
  This is a list of comments (how does it work for glucose and cadical) to prepare the future
  refinement:
  \<^enum> Reduction
     \<^item> every 2000+300*n (rougly since inprocessing changes the real number, cadical)
           (split over initialisation file); don't restart if level < 2 or if the level is less
       than the fast average
     \<^item> curRestart * nbclausesbeforereduce;
          curRestart = (conflicts / nbclausesbeforereduce) + 1 (glucose)
  \<^enum> Killed
     \<^item> half of the clauses that \<^bold>\<open>can\<close> be deleted (i.e., not used since last restart), not strictly
       LBD, but a probability of being useful.
     \<^item> half of the clauses
  \<^enum> Restarts:
     \<^item> EMA-14, aka restart if enough clauses and slow_glue_avg * opts.restartmargin > fast_glue (file ema.cpp)
     \<^item> (lbdQueue.getavg() * K) > (sumLBD / conflictsRestarts),
       \<^text>\<open>conflictsRestarts > LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid() && trail.size() > R * trailQueue.getavg()\<close>
\<close>

context isasat_restart_bounded
begin

definition remove_all_annot_true_clause_imp_wl_D_heur_inv
  :: \<open>twl_st_wl_heur \<Rightarrow> nat list \<Rightarrow> nat \<times> twl_st_wl_heur \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_heur_inv S xs = (\<lambda>(i, T).
       \<exists>S' T'. (S, S') \<in> twl_st_heur \<and> (T, T') \<in> twl_st_heur \<and>
         remove_all_annot_true_clause_imp_wl_D_inv S' xs (i, T'))
     \<close>
definition remove_all_annot_true_clause_one_imp_heur
where
\<open>remove_all_annot_true_clause_one_imp_heur = (\<lambda>(C, N). do {
      if C \<in># dom_m N then RETURN (fmdrop C N)
      else do {
        RETURN N
      }
  })\<close>

definition remove_all_annot_true_clause_imp_wl_D_heur_pre where
  \<open>remove_all_annot_true_clause_imp_wl_D_heur_pre L S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_heur \<and> remove_all_annot_true_clause_imp_wl_D_pre L S')\<close>

(* TODO: unfold Let when generating code! *)
definition remove_all_annot_true_clause_imp_wl_D_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>remove_all_annot_true_clause_imp_wl_D_heur = (\<lambda>L (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats). do {
    ASSERT(remove_all_annot_true_clause_imp_wl_D_heur_pre L (M, N0, D, Q, W, vm, \<phi>, clvls,
       cach, lbd, outl, stats));
    let xs = W!(nat_of_lit L);
    (_, N) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, N).
        remove_all_annot_true_clause_imp_wl_D_heur_inv
           (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats) xs
           (i, M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats)\<^esup>
      (\<lambda>(i, N). i < length xs)
      (\<lambda>(i, N). do {
        ASSERT(i < length xs);
        if xs!i \<in># dom_m N
        then do {
          N \<leftarrow> remove_all_annot_true_clause_one_imp_heur (xs!i, N);
          ASSERT(remove_all_annot_true_clause_imp_wl_D_heur_inv
             (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats) xs
             (i, M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats));
          RETURN (i+1, N)
        }
        else
          RETURN (i+1, N)
      })
      (0, N0);
    RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats)
  })\<close>

definition minimum_number_between_restarts :: \<open>uint32\<close> where
  \<open>minimum_number_between_restarts = 50\<close>

definition restart_required_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_heur S n =
    RETURN (
       ((get_slow_ema_heur S * 5) >> 2) > get_fast_ema_heur S \<and>
        get_conflict_count_heur S > minimum_number_between_restarts \<and>
        size (get_clauses_wl_heur S) > f n)\<close>


end

end