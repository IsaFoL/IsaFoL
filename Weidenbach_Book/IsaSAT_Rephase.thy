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

end