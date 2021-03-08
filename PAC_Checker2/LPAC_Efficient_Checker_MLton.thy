theory LPAC_Efficient_Checker_MLton
  imports LPAC_Efficient_Checker_Synthesis
begin

export_code
  full_checker_l_s2_impl int_of_integer Del CL nat_of_integer String.implode remap_polys_l2_with_err_s_impl
  PAC_update_impl PAC_empty_impl the_error is_cfailed is_cfound
  fully_normalize_poly_impl empty_shared_vars_int_impl
  PAC_checker_l_s_impl PAC_checker_l_step_s_impl version
  in SML_imp module_name PAC_Checker
  file_prefix "checker"

compile_generated_files _
  external_files
  \<open>code/parser.sml\<close>
  \<open>code/pasteque.sml\<close>
  \<open>code/pasteque.mlb\<close>
  where \<open>fn dir =>
  let
    val exec = Generated_Files.execute (Path.append dir (Path.basic "code"));
    val _ = exec \<open>Copy files\<close>
    ("cp checker.ML " ^ ((File.bash_path \<^path>\<open>$ISAFOL\<close>) ^ "/PAC_Checker2/code/checker.ML"));
    val _ =
    exec \<open>Compilation\<close>
    (File.bash_path \<^path>\<open>/usr/bin/mlton\<close> ^ " " ^
    "-const 'MLton.safe false' -verbose 1 -default-type int64 -output pasteque " ^
    "-codegen native -inline 700 -cc-opt -O3 pasteque.mlb");
    in () end\<close>

end