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

lemma current_restart_phase_alt_def:
  \<open>current_restart_phase =
    (\<lambda>(fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>).
      restart_phase)\<close>
  by (auto intro!: ext)

sepref_def current_restart_phase_impl
  is \<open>RETURN o current_restart_phase\<close>
  :: \<open>heuristic_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding current_restart_phase_alt_def heuristic_assn_def
  by sepref

sepref_def isasat_current_status_fast_code
  is \<open>isasat_current_status\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_bounded_assn_def isasat_current_status_def
  unfolding fold_tuple_optimizations
  by sepref


sepref_def print_open_colour_impl
  is \<open>RETURN o print_open_colour\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_open_colour_def
  by sepref


sepref_def print_close_colour_impl
  is \<open>RETURN o print_close_colour\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_close_colour_def
  by sepref

sepref_def print_char_impl
  is \<open>RETURN o print_char\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_char_def
  by sepref

sepref_def isasat_print_progress_impl
  is \<open>uncurry3 (RETURN oooo isasat_print_progress)\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a stats_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding isasat_print_progress_def
  by sepref

term isasat_current_progress

sepref_def isasat_current_progress_impl
  is \<open>uncurry isasat_current_progress\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_bounded_assn_def isasat_current_progress_def
  unfolding fold_tuple_optimizations
  by sepref

end