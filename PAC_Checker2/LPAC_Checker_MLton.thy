(*
  File:         PAC_Checker_MLton.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory LPAC_Checker_MLton
  imports LPAC_Checker_Synthesis
begin

export_code PAC_checker_l_impl PAC_update_impl PAC_empty_impl the_error is_cfailed is_cfound
  int_of_integer Del CL nat_of_integer String.implode remap_polys_l_impl
  fully_normalize_poly_impl union_vars_poly_impl empty_vars_impl
  full_checker_l_impl check_step_impl CSUCCESS
  Extension version
  in SML_imp module_name PAC_Checker
  file_prefix "checker"

text \<open>Here is how to compile it:\<close>

lemma
  [code_abbrev del]: \<open>uint32_of_char x = uint32_of_int (int_of_char x)\<close>
  sorry

lemma [code del]: \<open>hashcode s = hashcode_literal' s\<close>
  unfolding hashcode_literal_def hashcode_list_def
  apply (auto simp: unsafe_asciis_of_literal_def hashcode_list_def
     String.asciis_of_literal_def hashcode_literal_def hashcode_literal'_def)
  done
code_printing
  constant uint32_of_char \<rightharpoonup>
    (SML) "!(Word32.fromInt /o (nononoChar.ord))"
(*
seen broken Isabelle2025-2, without changing the code.
compile_generated_files _
  external_files
    \<open>code/no_sharing/parser.sml\<close>
    \<open>code/no_sharing/pasteque.sml\<close>
    \<open>code/no_sharing/pasteque.mlb\<close>
  where \<open>fn dir =>
  let
    val exec = Generated_Files.execute (Path.append dir (Path.append (Path.basic "code") (Path.basic "no_sharing")));

    val _ = exec \<open>Copy files\<close>
    ("cp ../checker.ML " ^ ((File.bash_path \<^path>\<open>$ISAFOL\<close>) ^ "/PAC_Checker2/code/no_sharing/checker.ML"));
    val _ = exec \<open>Copy files\<close> ("cp ../checker.ML .");
    val _ =
        exec \<open>Compilation\<close>
    (File.bash_path \<^path>\<open>$ISABELLE_MLTON\<close> ^ " " ^
            "-const 'MLton.safe false' -verbose 1 -default-type int64 -output pasteque " ^
            "-codegen native -inline 700 -cc-opt -O3 pasteque.mlb");
    in () end\<close>
*)

text \<open>The second copy is required because the code is generate in the wrong directory.\<close>
end
