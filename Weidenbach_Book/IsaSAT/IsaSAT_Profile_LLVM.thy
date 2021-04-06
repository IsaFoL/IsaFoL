theory IsaSAT_Profile_LLVM
  imports IsaSAT_Profile IsaSAT_Literals_LLVM
begin

sepref_register IsaSAT_Profile.start
  IsaSAT_Profile.stop
  IsaSAT_Profile.PROPAGATE
  IsaSAT_Profile.ANALYZE
  IsaSAT_Profile.GC
  IsaSAT_Profile.REDUCE

sepref_def start_profile
  is \<open>RETURN o IsaSAT_Profile.start\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding IsaSAT_Profile.start_def
  by sepref

sepref_def stop_profile
  is \<open>RETURN o IsaSAT_Profile.stop\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding IsaSAT_Profile.stop_def
  by sepref


sepref_def IsaSAT_Profile_PROPAGATE
  is \<open>uncurry0 (RETURN IsaSAT_Profile.PROPAGATE)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding IsaSAT_Profile.PROPAGATE_def
  by sepref

sepref_def IsaSAT_Profile_ANALYZE
  is \<open>uncurry0 (RETURN IsaSAT_Profile.ANALYZE)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding IsaSAT_Profile.ANALYZE_def
  by sepref

sepref_def IsaSAT_Profile_GC
  is \<open>uncurry0 (RETURN IsaSAT_Profile.GC)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding IsaSAT_Profile.GC_def
  by sepref

sepref_def IsaSAT_Profile_REDUCE
  is \<open>uncurry0 (RETURN IsaSAT_Profile.REDUCE)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding IsaSAT_Profile.REDUCE_def
  by sepref


experiment begin

export_llvm
    IsaSAT_Profile_PROPAGATE is \<open>PROFILE_CST IsaSAT_Profile_PROPAGATE\<close>
    IsaSAT_Profile_REDUCE is \<open>PROFILE_CST IsaSAT_Profile_REDUCE\<close>
    IsaSAT_Profile_GC is \<open>PROFILE_CST IsaSAT_Profile_GC\<close>
    IsaSAT_Profile_ANALYZE is \<open>PROFILE_CST IsaSAT_Profile_ANALYZE\<close>
    defines \<open>
       typedef int8_t PROFILE_CST;
  \<close>
end
end