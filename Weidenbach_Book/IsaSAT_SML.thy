theory IsaSAT_SML
  imports IsaSAT Version IsaSAT_Restart_SML
begin

sepref_definition  empty_conflict_code'
  is \<open>uncurry0 (empty_conflict_code)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  unfolding empty_conflict_code_def
  apply (rewrite in \<open>let _ =  \<hole> in _\<close> annotate_assn[where A=\<open>arl_assn unat_lit_assn\<close>])
  by sepref

declare empty_conflict_code'.refine[sepref_fr_rules]

sepref_definition  empty_init_code'
  is \<open>uncurry0 (RETURN empty_init_code)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  unfolding empty_init_code_def
  by sepref

declare empty_init_code'.refine[sepref_fr_rules]

sepref_register init_dt_wl_heur_full

declare extract_model_of_state_stat_hnr[sepref_fr_rules]
sepref_register to_init_state from_init_state get_conflict_wl_is_None_init extract_stats
  init_dt_wl_heur


declare
  init_dt_wl_heur_code.refine[sepref_fr_rules]
  get_stats_code[sepref_fr_rules]

sepref_definition isasat_fast_init_code
  is \<open>RETURN o isasat_fast_init\<close>
  :: \<open>isasat_init_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding isasat_fast_init_alt_def isasat_init_assn_def
  by sepref

declare isasat_fast_init_code.refine[sepref_fr_rules]

declare convert_state_hnr[sepref_fr_rules]
  convert_state_hnr_unb[sepref_fr_rules]

sepref_register
   cdcl_twl_stgy_restart_prog_wl_heur

declare init_state_wl_D'_code.refine[FCOMP init_state_wl_D',
  unfolded lits_with_max_assn_alt_def[symmetric],
  unfolded init_state_wl_D'_code_isasat, sepref_fr_rules]
declare init_state_wl_D'_code.refine[FCOMP init_state_wl_D', sepref_fr_rules]


sepref_definition isasat_init_fast_slow_code
  is \<open>isasat_init_fast_slow\<close>
  :: \<open>isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_init_unbounded_assn_def isasat_init_assn_def isasat_init_fast_slow_def
  by sepref

declare isasat_init_fast_slow_code.refine[sepref_fr_rules]


sepref_definition IsaSAT_code
  is \<open>uncurry IsaSAT_heur\<close>
  :: \<open>opts_assn\<^sup>d *\<^sub>a (list_assn (list_assn unat_lit_assn))\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  supply [[goals_limit=1]]
  unfolding IsaSAT_heur_def empty_conflict_def[symmetric]
    get_conflict_wl_is_None extract_model_of_state_def[symmetric]
    extract_stats_def[symmetric]
    length_get_clauses_wl_heur_init_def[symmetric]
  supply get_conflict_wl_is_None_heur_init_def[simp]
  supply id_mset_list_assn_list_mset_assn[sepref_fr_rules] get_conflict_wl_is_None_def[simp]
   option.splits[split]
   extract_stats_def[simp del]
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  by sepref

theorem IsaSAT_full_correctness:
  \<open>(uncurry IsaSAT_code, uncurry (\<lambda>_. model_if_satisfiable))
     \<in> [\<lambda>(_, a). Multiset.Ball a distinct_mset \<and>
      (\<forall>C\<in>#a.  \<forall>L\<in>#C. nat_of_lit L  \<le> uint_max)]\<^sub>a opts_assn\<^sup>d *\<^sub>a  clauses_l_assn\<^sup>k \<rightarrow> model_assn\<close>
  using IsaSAT_code.refine[FCOMP IsaSAT_heur_model_if_sat',
    unfolded list_assn_list_mset_rel_clauses_l_assn]
  unfolding model_assn_def
  apply auto
  done


subsubsection \<open>Code Export\<close>

definition nth_u_code' where
  [symmetric, code]: \<open>nth_u_code' = nth_u_code\<close>

code_printing constant nth_u_code' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ Word32.toInt (_)))"

definition nth_u64_code' where
  [symmetric, code]: \<open>nth_u64_code' = nth_u64_code\<close>

code_printing constant nth_u64_code' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ Uint64.toFixedInt (_)))"

definition heap_array_set'_u' where
  [symmetric, code]: \<open>heap_array_set'_u' = heap_array_set'_u\<close>

code_printing constant heap_array_set'_u' \<rightharpoonup>
   (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ (Word32.toInt (_)),/ (_)))"

definition heap_array_set'_u64' where
  [symmetric, code]: \<open>heap_array_set'_u64' = heap_array_set'_u64\<close>

code_printing constant heap_array_set'_u64' \<rightharpoonup>
   (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ (Word64.toInt (_)),/ (_)))"

(* code_printing constant two_uint32 \<rightharpoonup> (SML) "(Word32.fromInt 2)"
 *)
definition length_u_code' where
  [symmetric, code]: \<open>length_u_code' = length_u_code\<close>

code_printing constant length_u_code' \<rightharpoonup> (SML_imp) "(fn/ ()/ =>/ Word32.fromInt (Array.length (_)))"

definition length_aa_u_code' where
  [symmetric, code]: \<open>length_aa_u_code' = length_aa_u_code\<close>

code_printing constant length_aa_u_code' \<rightharpoonup> (SML_imp)
   "(fn/ ()/ =>/ Word32.fromInt (Array.length (Array.sub/ ((fn/ (a,b)/ =>/ a) (_),/ IntInf.toInt (integer'_of'_nat (_))))))"

definition nth_raa_i_u64' where
  [symmetric, code]: \<open>nth_raa_i_u64' = nth_raa_i_u64\<close>

code_printing constant nth_raa_i_u64' \<rightharpoonup> (SML_imp)
   "(fn/ ()/ =>/ Array.sub (Array.sub/ ((fn/ (a,b)/ =>/ a) (_),/ IntInf.toInt (integer'_of'_nat (_))), Uint64.toFixedInt (_)))"

definition length_u64_code' where
  [symmetric, code]: \<open>length_u64_code' = length_u64_code\<close>

code_printing constant length_u64_code' \<rightharpoonup> (SML_imp)
   "(fn/ ()/ =>/ Uint64.fromFixedInt (Array.length (_)))"

code_printing constant arl_get_u \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((fn/ (a,b)/ =>/ a) ((_)),/ Word32.toInt ((_))))"

definition uint32_of_uint64' where
  [symmetric, code]: \<open>uint32_of_uint64' = uint32_of_uint64\<close>

code_printing constant uint32_of_uint64' \<rightharpoonup> (SML_imp)
   "Word32.fromLargeWord (_)"

lemma arl_set_u64_code[code]: \<open>arl_set_u64 a i x =
   Array_upd_u64 i x (fst a) \<bind> (\<lambda>b. return (b, (snd a)))\<close>
  unfolding arl_set_u64_def arl_set_def heap_array_set'_u64_def arl_set'_u64_def
     heap_array_set_u64_def Array.upd'_def Array_upd_u64_def
  by (cases a) (auto simp: nat_of_uint64_code[symmetric])

lemma arl_set_u_code[code]: \<open>arl_set_u a i x =
   Array_upd_u i x (fst a) \<bind> (\<lambda>b. return (b, (snd a)))\<close>
  unfolding arl_set_u_def arl_set_def heap_array_set'_u64_def arl_set'_u_def
     heap_array_set_u_def Array.upd'_def Array_upd_u_def
  by (cases a) (auto simp: nat_of_uint64_code[symmetric])

definition arl_get_u64' where
  [symmetric, code]: \<open>arl_get_u64' = arl_get_u64\<close>

code_printing constant arl_get_u64' \<rightharpoonup> (SML)
  "(fn/ ()/ =>/ Array.sub/ ((fn (a,b) => a) (_),/ Uint64.toFixedInt (_)))"

export_code IsaSAT_code checking SML_imp

code_printing constant \<comment> \<open>print with line break\<close>
  println_string \<rightharpoonup> (SML) "ignore/ (print/ ((_) ^ \"\\n\"))"

export_code IsaSAT_code
    int_of_integer
    integer_of_int
    integer_of_nat
    nat_of_integer
    uint32_of_nat
    Version.version
  in SML_imp module_name SAT_Solver file_prefix "IsaSAT_solver"

external_file \<open>code/Unsynchronized.sml\<close>
external_file \<open>code/IsaSAT.mlb\<close>
external_file \<open>code/IsaSAT.sml\<close>
external_file \<open>code/dimacs_parser.sml\<close>


compile_generated_files _
  external_files
    \<open>code/IsaSAT.mlb\<close>
    \<open>code/Unsynchronized.sml\<close>
    \<open>code/IsaSAT.sml\<close>
    \<open>code/dimacs_parser.sml\<close>
  where \<open>fn dir =>
    let
      val exec = Generated_Files.execute (Path.append dir (Path.basic "code"));
      val _ = exec \<open>rename file\<close> "mv IsaSAT_solver.ML IsaSAT_solver.sml"
      val _ =
        exec \<open>Copy files\<close>
          ("cp IsaSAT_solver.sml " ^
            ((File.bash_path \<^path>\<open>$ISAFOL\<close>) ^ "/Weidenbach_Book/code/IsaSAT_solver.sml"));
      val _ =
        exec \<open>Compilation\<close>
          (File.bash_path \<^path>\<open>$ISABELLE_MLTON\<close> ^
            " -const 'MLton.safe false' -verbose 1 -default-type int64 -output IsaSAT " ^
            " -codegen native -inline 700 -cc-opt -O3 IsaSAT.mlb");
      val _ =
        exec \<open>Copy binary files\<close>
          ("cp IsaSAT " ^
            File.bash_path \<^path>\<open>$ISAFOL\<close> ^ "/Weidenbach_Book/code/");
    in () end\<close>

end