theory IsaSAT_Rephase
  imports IsaSAT_Literals Watched_Literals_VMTF
begin

chapter \<open>Phase Saving\<close>

section \<open>Rephasing\<close>

type_synonym phase_save_heur = \<open>phase_saver \<times> nat \<times> phase_saver \<times> nat \<times> phase_saver \<times> 64 word \<times> 64 word \<times> 64 word\<close>

definition phase_save_heur_rel :: \<open>nat multiset \<Rightarrow> phase_save_heur \<Rightarrow> bool\<close> where
\<open>phase_save_heur_rel \<A> = (\<lambda>(\<phi>, target_assigned, target, best_assigned, best,
    end_of_phase, curr_phase). phase_saving \<A> \<phi> \<and>
  phase_saving \<A> target \<and> phase_saving \<A> best \<and> length \<phi> = length best \<and>
  length target = length best)\<close>

definition end_of_rephasing_phase :: \<open>phase_save_heur \<Rightarrow> 64 word\<close> where
  \<open>end_of_rephasing_phase = (\<lambda>(\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase,
     length_phase). end_of_phase)\<close>


definition phase_current_rephasing_phase :: \<open>phase_save_heur \<Rightarrow> 64 word\<close> where
  \<open>phase_current_rephasing_phase =
    (\<lambda>(\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase, length_phase). curr_phase)\<close>


text \<open>
  We implement the idea in CaDiCaL of rephasing:
  \<^item> We remember the best model found so far. It is used as base.
  \<^item> We flip the phase saving heuristics between \<^term>\<open>True\<close>,
   \<^term>\<open>False\<close>, and random.
\<close>

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
       RETURN (\<phi>'[a := \<phi>!a])
   })
   \<phi>'
 }\<close>

lemma copy_phase_alt_def:
\<open>copy_phase \<phi> \<phi>' = do {
  ASSERT(length \<phi> = length \<phi>');
  let n = length \<phi>;
  nfoldli [0..<n]
    (\<lambda>_. True)
    (\<lambda> a \<phi>'. do {
       ASSERT(a < length \<phi>);
       ASSERT(a < length \<phi>');
       RETURN (\<phi>'[a := \<phi>!a])
   })
   \<phi>'
 }\<close>
  unfolding copy_phase_def
  by (auto simp: ASSERT_same_eq_conv)

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

definition rephase_flipped :: \<open>bool list \<Rightarrow> bool list nres\<close> where
\<open>rephase_flipped \<phi> = do {
  let n = length \<phi>;
  (\<phi>) \<leftarrow> nfoldli [0..<n]
      (\<lambda>_. True)
      (\<lambda>a  \<phi>. do {
        ASSERT(a < length \<phi>);
       let v = \<phi> ! a;
       RETURN (\<phi>[a := \<not>v])
     })
     \<phi>;
  RETURN \<phi>
 }\<close>


lemma rephase_flipped_spec:
  \<open>rephase_flipped \<phi> \<le> SPEC(\<lambda>\<psi>. length \<psi> = length \<phi>)\<close>
  unfolding rephase_flipped_def Let_def
  apply (refine_vcg nfoldli_rule[where I = \<open>\<lambda>_ _ \<psi>. length \<phi> = length \<psi>\<close>])
  apply (auto dest: in_list_in_setD)
  done


definition reset_target_phase :: \<open>phase_save_heur \<Rightarrow> phase_save_heur nres\<close> where
\<open>reset_target_phase = (\<lambda>(\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase).
       RETURN (\<phi>, 0, target, best_assigned, best, end_of_phase, curr_phase)
   )\<close>


definition reset_best_phase :: \<open>phase_save_heur \<Rightarrow> phase_save_heur nres\<close> where
\<open>reset_best_phase = (\<lambda>(\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase).
       RETURN (\<phi>, target_assigned, target, 0, best, end_of_phase, curr_phase)
   )\<close>


lemma reset_target_phase_spec:
  assumes \<open>phase_save_heur_rel \<A> \<phi>\<close>
  shows \<open>reset_target_phase \<phi> \<le> \<Down>Id (SPEC(phase_save_heur_rel \<A>))\<close>
  using assms by (cases \<phi>) (auto simp: reset_target_phase_def phase_save_heur_rel_def)


lemma reset_best_phase_spec:
  assumes \<open>phase_save_heur_rel \<A> \<phi>\<close>
  shows \<open>reset_best_phase \<phi> \<le> \<Down>Id (SPEC(phase_save_heur_rel \<A>))\<close>
  using assms by (cases \<phi>) (auto simp: reset_best_phase_def phase_save_heur_rel_def)

definition current_phase_letter :: \<open>64 word \<Rightarrow> 64 word\<close> where
  \<open>current_phase_letter curr_phase =
      (if curr_phase = 0 \<or> curr_phase = 2 \<or> curr_phase = 4 \<or> curr_phase = 6
      then 66
      else if curr_phase = 1
      then 73
      else if curr_phase = 3
      then 35
      else if curr_phase = 5
      then 79
      else 70)
     \<close>

definition phase_rephase :: \<open>64 word \<Rightarrow> phase_save_heur \<Rightarrow> phase_save_heur nres\<close> where
\<open>phase_rephase = (\<lambda>b (\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase,
     length_phase).
  do {
      let target_assigned = 0;
      if curr_phase = 0 \<or> curr_phase = 2 \<or> curr_phase = 4 \<or> curr_phase = 6
      then do {
         \<phi> \<leftarrow> copy_phase best \<phi>;
         RETURN (\<phi>, target_assigned, target, best_assigned, best, length_phase*1000+end_of_phase, curr_phase + 1, length_phase)
      }
      else if curr_phase = 1
      then do {
         \<phi> \<leftarrow> rephase_init True \<phi>;
         RETURN (\<phi>, target_assigned, target, best_assigned, best, length_phase*1000+end_of_phase, curr_phase + 1, length_phase)
      }
      else if curr_phase = 3
      then do {
         \<phi> \<leftarrow> rephase_random end_of_phase \<phi>;
         RETURN (\<phi>, target_assigned, target, best_assigned, best, length_phase*1000+end_of_phase, curr_phase + 1, length_phase)
      }
      else if curr_phase = 5
      then do {
         \<phi> \<leftarrow> rephase_init False \<phi>;
         RETURN (\<phi>, target_assigned, target, best_assigned, best, length_phase*1000+end_of_phase, curr_phase + 1, length_phase)
      }
      else do {
         \<phi> \<leftarrow> rephase_flipped \<phi>;
         RETURN (\<phi>, target_assigned, target, best_assigned, best, (1+length_phase)*1000+end_of_phase, 0,
            length_phase+1)
      }
    })\<close>

lemma phase_rephase_spec:
  assumes \<open>phase_save_heur_rel \<A> \<phi>\<close>
  shows \<open>phase_rephase b \<phi> \<le> \<Down>Id (SPEC(phase_save_heur_rel \<A>))\<close>
proof -
  obtain \<phi>' target_assigned target best_assigned best end_of_phase curr_phase where
    \<phi>: \<open>\<phi> = (\<phi>', target_assigned, target, best_assigned, best, end_of_phase, curr_phase)\<close>
    by (cases \<phi>) auto
  then have [simp]: \<open>length \<phi>' = length best\<close>
    using assms by (auto simp: phase_save_heur_rel_def)
  show ?thesis
    using assms
    unfolding phase_rephase_def
    by (refine_vcg lhs_step_If rephase_init_spec[THEN order_trans]
      copy_phase_spec[THEN order_trans] rephase_random_spec[THEN order_trans]
      rephase_flipped_spec[THEN order_trans])
      (auto simp: phase_save_heur_rel_def phase_saving_def)
qed


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

definition get_next_phase_pre :: \<open>bool \<Rightarrow> nat \<Rightarrow> phase_save_heur \<Rightarrow> bool\<close> where
  \<open>get_next_phase_pre = (\<lambda>b L (\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase).
    L < length \<phi> \<and> L < length target)\<close>

definition get_next_phase :: \<open>bool \<Rightarrow> nat \<Rightarrow> phase_save_heur \<Rightarrow> bool nres\<close>  where
  \<open>get_next_phase = (\<lambda>b L (\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase).
  if b then do {
    ASSERT(L < length \<phi>);
    RETURN(\<phi> ! L)
  } else  do {
    ASSERT(L < length target);
    RETURN(target ! L)
  })\<close>

end