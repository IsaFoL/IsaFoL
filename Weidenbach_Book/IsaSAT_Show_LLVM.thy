theory IsaSAT_Show_LLVM
  imports
    IsaSAT_Show
    IsaSAT_Setup_LLVM
begin

text \<open>The printing has been removed.\<close>
lemma isasat_current_information_alt_def:
\<open>isasat_current_information =
   (\<lambda>(propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds) lcount.
     if confl AND 8191 = 8191 \<comment> \<open>\<^term>\<open>8191 = 8192 - 1\<close>, i.e., we print when all first bits are 1.\<close>
     then
        zero_some_stats (propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds)
      else (propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds)
      )\<close>
  unfolding isasat_current_information_def by auto

sepref_register print_current_information print_c print_uint64

sepref_def print_c_impl
  is \<open>RETURN o print_c\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_c_def
  by sepref

sepref_def print_uint64_impl
  is \<open>RETURN o print_uint64\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_uint64_def
  by sepref


sepref_def zero_some_stats_impl
  is \<open>RETURN o zero_some_stats\<close>
  :: \<open>stats_assn\<^sup>d \<rightarrow>\<^sub>a stats_assn\<close>
  unfolding zero_some_stats_def
  by sepref

sepref_def isasat_current_information_impl [llvm_code]
  is \<open>uncurry (RETURN oo print_current_information)\<close>
  :: \<open>stats_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a stats_assn\<close>
  unfolding print_current_information_isasat_current
    isasat_current_information_def
  by sepref

declare isasat_current_information_impl.refine[sepref_fr_rules]


sepref_def isasat_current_status_fast_code
  is \<open>isasat_current_status\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_bounded_assn_def isasat_current_status_def
  unfolding fold_tuple_optimizations
  by sepref

declare isasat_current_status_fast_code.refine[sepref_fr_rules]

end