theory IsaSAT_Rephase
  imports IsaSAT_Setup
begin

definition rephase_init :: \<open>bool \<Rightarrow> bool list \<Rightarrow> bool list nres\<close> where
\<open>rephase_init b \<phi> = do {
  let n = length \<phi>;
  nfoldli [0..<n]
    (\<lambda>_. True)
    (\<lambda> a \<phi>. do {
       ASSERT(a < length \<phi>);
       RETURN (\<phi>[a := b])
   })
   \<phi>
 }\<close>

lemma rephase_init_spec:
  \<open>rephase_init b \<phi> \<le> SPEC(\<lambda>\<psi>. length \<psi> = length \<phi>)\<close>
proof -
  show ?thesis
  unfolding rephase_init_def Let_def
  apply (rule nfoldli_rule[where I = \<open>\<lambda>_ _ \<psi>. length \<phi> = length \<psi>\<close>])
  apply (auto dest: in_list_in_setD)
  done
qed


definition copy_phase :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool list nres\<close> where
\<open>copy_phase \<phi> \<phi>' = do {
  ASSERT(length \<phi> = length \<phi>');
  let n = length \<phi>';
  nfoldli [0..<n]
    (\<lambda>_. True)
    (\<lambda> a \<phi>'. do {
       ASSERT(a < length \<phi>);
       ASSERT(a < length \<phi>');
       RETURN (\<phi>'[a := \<phi>'!a])
   })
   \<phi>'
 }\<close>

lemma copy_phase_spec:
  \<open>length \<phi> = length \<phi>' \<Longrightarrow> copy_phase \<phi> \<phi>' \<le> SPEC(\<lambda>\<psi>. length \<psi> = length \<phi>)\<close>
  unfolding copy_phase_def Let_def
  apply (intro ASSERT_leI)
  subgoal by auto
  apply (rule nfoldli_rule[where I = \<open>\<lambda>_ _ \<psi>. length \<phi> = length \<psi>\<close>])
  apply (auto dest: in_list_in_setD)
  done


definition rephase_random :: \<open>64 word \<Rightarrow> bool list \<Rightarrow> bool list nres\<close> where
\<open>rephase_random b \<phi> = do {
  let n = length \<phi>;
  (_, \<phi>) \<leftarrow> nfoldli [0..<n]
      (\<lambda>_. True)
      (\<lambda>a (state, \<phi>). do {
        ASSERT(a < length \<phi>);
       let state = state * 6364136223846793005 + 1442695040888963407;
       RETURN (state, \<phi>[a := (state < 2147483648)])
     })
     (b, \<phi>);
  RETURN \<phi>
 }\<close>


lemma rephase_random_spec:
  \<open>rephase_random b \<phi> \<le> SPEC(\<lambda>\<psi>. length \<psi> = length \<phi>)\<close>
  unfolding rephase_random_def Let_def
  apply (refine_vcg nfoldli_rule[where I = \<open>\<lambda>_ _ (_, \<psi>). length \<phi> = length \<psi>\<close>])
  apply (auto dest: in_list_in_setD)
  done


definition phase_rephase :: \<open>phase_save_heur \<Rightarrow> phase_save_heur nres\<close> where
\<open>phase_rephase = (\<lambda>(\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase).
    if curr_phase = 0
    then do {
       \<phi> \<leftarrow> rephase_init False \<phi>;
       RETURN (\<phi>, target_assigned, target, best_assigned, best, 10000+end_of_phase, 1)
    }
    else if curr_phase = 1
    then do {
       \<phi> \<leftarrow> copy_phase best \<phi>;
       RETURN (\<phi>, target_assigned, target, best_assigned, best, 10000+end_of_phase, 2)
    }
    else if curr_phase = 2
    then do {
       \<phi> \<leftarrow> rephase_init True \<phi>;
       RETURN (\<phi>, target_assigned, target, best_assigned, best, 10000+end_of_phase, 3)
    }
    else if curr_phase = 3
    then do {
       \<phi> \<leftarrow> rephase_random end_of_phase \<phi>;
       RETURN (\<phi>, target_assigned, target, best_assigned, best, 10000+end_of_phase, 4)
    }
    else do {
       \<phi> \<leftarrow> copy_phase best \<phi>;
       RETURN (\<phi>, target_assigned, target, best_assigned, best, 10000+end_of_phase, 0)
    })\<close>

lemma phase_rephase_spec:
  assumes \<open>phase_save_heur_rel \<A> \<phi>\<close>
  shows \<open>phase_rephase \<phi> \<le> \<Down>Id (SPEC(phase_save_heur_rel \<A>))\<close>
proof -
  obtain \<phi>' target_assigned target best_assigned best end_of_phase curr_phase where
    \<phi>: \<open>\<phi> = (\<phi>', target_assigned, target, best_assigned, best, end_of_phase, curr_phase)\<close>
    by (cases \<phi>) auto
  then have [simp]: \<open>length \<phi>' = length best\<close>
    using assms by (auto simp: phase_save_heur_rel_def)
  have 1: \<open>\<Down>Id (SPEC(phase_save_heur_rel \<A>)) \<ge>
    \<Down>Id((\<lambda>(\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase).
      if curr_phase = 0 then  do {
        \<phi>' \<leftarrow> SPEC (\<lambda>\<phi>'. length \<phi> = length \<phi>');
        RETURN (\<phi>', target_assigned, target, best_assigned, best, 10000+end_of_phase, 1)
      }
     else if curr_phase = 1 then  do {
        \<phi>' \<leftarrow> SPEC (\<lambda>\<phi>'. length \<phi> = length \<phi>');
        RETURN (\<phi>', target_assigned, target, best_assigned, best, 10000+end_of_phase, 2)
     }
     else if curr_phase = 2 then  do {
        \<phi>' \<leftarrow> SPEC (\<lambda>\<phi>'. length \<phi> = length \<phi>');
        RETURN (\<phi>', target_assigned, target, best_assigned, best, 10000+end_of_phase, 3)
     }
     else if curr_phase = 3 then  do {
        \<phi>' \<leftarrow> SPEC (\<lambda>\<phi>'. length \<phi> = length \<phi>');
        RETURN (\<phi>', target_assigned, target, best_assigned, best, 10000+end_of_phase, 4)
     }
     else do {
        \<phi>' \<leftarrow> SPEC (\<lambda>\<phi>'. length \<phi> = length \<phi>');
        RETURN (\<phi>', target_assigned, target, best_assigned, best, 10000+end_of_phase, 0)
     }) \<phi>)\<close>
   using assms
   by (cases \<phi>)
    (auto simp: phase_save_heur_rel_def phase_saving_def RES_RETURN_RES)

  show ?thesis
    unfolding phase_rephase_def \<phi>
    apply (simp only: prod.case)
    apply (rule order_trans)
    defer
    apply (rule 1)
    apply (simp only: prod.case \<phi>)
    apply (refine_vcg if_mono rephase_init_spec copy_phase_spec rephase_random_spec)
    apply (auto simp: phase_rephase_def)
    done
qed

definition rephase_heur :: \<open>restart_heuristics \<Rightarrow> restart_heuristics nres\<close> where
  \<open>rephase_heur = (\<lambda>(fast_ema, slow_ema, restart_info, wasted, \<phi>).
    do {
      \<phi> \<leftarrow> phase_rephase \<phi>;
      RETURN (fast_ema, slow_ema, restart_info, wasted, \<phi>)
   })\<close>

lemma rephase_heur_spec:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> rephase_heur heur \<le>  \<Down>Id (SPEC(heuristic_rel \<A>))\<close>
  unfolding rephase_heur_def
  apply (refine_vcg phase_rephase_spec[THEN order_trans])
  apply (auto simp: heuristic_rel_def)
  done

definition rephase_heur_st :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>rephase_heur_st = (\<lambda>(M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena). do {
      heur \<leftarrow> rephase_heur heur;
      RETURN (M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena)
   })\<close>

lemma rephase_heur_st_spec:
  \<open>(S, S') \<in> twl_st_heur \<Longrightarrow> rephase_heur_st S \<le> SPEC(\<lambda>S. (S, S') \<in> twl_st_heur)\<close>
  unfolding rephase_heur_st_def
  apply (cases S')
  apply (refine_vcg rephase_heur_spec[THEN order_trans, of \<open>all_atms_st S'\<close>])
  apply (simp_all add:  twl_st_heur_def)
  done

definition phase_save_phase :: \<open>nat \<Rightarrow> phase_save_heur \<Rightarrow> phase_save_heur nres\<close> where
\<open>phase_save_phase = (\<lambda>n (\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase). do {
       target \<leftarrow> (if n > target_assigned
          then copy_phase \<phi> target else RETURN target);
       target_assigned \<leftarrow> (if n > target_assigned
          then RETURN n else RETURN target_assigned);
       best \<leftarrow> (if n > best_assigned
          then copy_phase \<phi> best else RETURN best);
       best_assigned \<leftarrow> (if n > best_assigned
          then RETURN n else RETURN best_assigned);
       RETURN (\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase)
   })\<close>

lemma phase_save_phase_spec:
  assumes \<open>phase_save_heur_rel \<A> \<phi>\<close>
  shows \<open>phase_save_phase n \<phi> \<le> \<Down>Id (SPEC(phase_save_heur_rel \<A>))\<close>
proof -
  obtain \<phi>' target_assigned target best_assigned best end_of_phase curr_phase where
    \<phi>: \<open>\<phi> = (\<phi>', target_assigned, target, best_assigned, best, end_of_phase, curr_phase)\<close>
    by (cases \<phi>) auto
  then have [simp]: \<open>length \<phi>' = length best\<close>  \<open>length target = length best\<close>
    using assms by (auto simp: phase_save_heur_rel_def)
  have 1: \<open>\<Down>Id (SPEC(phase_save_heur_rel \<A>)) \<ge>
    \<Down>Id((\<lambda>(\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase). do {
        target \<leftarrow> (if n > target_assigned
          then SPEC (\<lambda>\<phi>'. length \<phi> = length \<phi>') else RETURN target);
        target_assigned \<leftarrow> (if n > target_assigned
          then RETURN n else RETURN target_assigned);
        best \<leftarrow> (if n > best_assigned
          then SPEC (\<lambda>\<phi>'. length \<phi> = length \<phi>') else RETURN best);
        best_assigned \<leftarrow> (if n > best_assigned
          then RETURN n else RETURN best_assigned);
        RETURN (\<phi>', target_assigned, target, best_assigned, best, end_of_phase, curr_phase)
     }) \<phi>)\<close>
   using assms
   by  (auto simp: phase_save_heur_rel_def phase_saving_def RES_RETURN_RES \<phi> RES_RES_RETURN_RES)

  show ?thesis
    unfolding phase_save_phase_def \<phi>
    apply (simp only: prod.case)
    apply (rule order_trans)
    defer
    apply (rule 1)
    apply (simp only: prod.case \<phi>)
    apply (refine_vcg if_mono rephase_init_spec copy_phase_spec rephase_random_spec)
    apply (auto simp: phase_rephase_def)
    done
qed

definition save_rephase_heur :: \<open>nat \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics nres\<close> where
  \<open>save_rephase_heur = (\<lambda>n (fast_ema, slow_ema, restart_info, wasted, \<phi>).
    do {
      \<phi> \<leftarrow> phase_save_phase n \<phi>;
      RETURN (fast_ema, slow_ema, restart_info, wasted, \<phi>)
   })\<close>

lemma save_phase_heur_spec:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> save_rephase_heur n heur \<le>  \<Down>Id (SPEC(heuristic_rel \<A>))\<close>
  unfolding save_rephase_heur_def
  apply (refine_vcg phase_save_phase_spec[THEN order_trans])
  apply (auto simp: heuristic_rel_def)
  done


definition save_phase_st :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>save_phase_st = (\<lambda>(M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena). do {
      let n = count_decided_pol M';
      heur \<leftarrow> save_rephase_heur n heur;
      RETURN (M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena)
   })\<close>

lemma save_phase_st_spec:
  \<open>(S, S') \<in> twl_st_heur \<Longrightarrow> save_phase_st S \<le> SPEC(\<lambda>S. (S, S') \<in> twl_st_heur)\<close>
  unfolding save_phase_st_def
  apply (cases S')
  apply (refine_vcg save_phase_heur_spec[THEN order_trans, of \<open>all_atms_st S'\<close>])
  apply (simp_all add:  twl_st_heur_def)
  done



end