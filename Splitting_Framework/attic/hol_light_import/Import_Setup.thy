(*  Title:      HOL/Import/Import_Setup.thy
    Author:     Cezary Kaliszyk, University of Innsbruck
    Author:     Alexander Krauss, QAware GmbH
*)

section \<open>Importer machinery and required theorems\<close>

theory Import_Setup
imports Main
keywords "import_type_map" "import_const_map" "import_file" :: thy_decl
begin

ML_file \<open>~~/src/HOL/Import/import_data.ML\<close>

lemma light_ex_imp_nonempty:
  "P t \<Longrightarrow> \<exists>x. x \<in> Collect P"
  by auto

lemma typedef_hol2hollight:
  assumes a: "type_definition Rep Abs (Collect P)"
  shows "Abs (Rep a) = a \<and> P r = (Rep (Abs r) = r)"
  by (metis type_definition.Rep_inverse type_definition.Abs_inverse
      type_definition.Rep a mem_Collect_eq)

lemma ext2:
  "(\<And>x. f x = g x) \<Longrightarrow> f = g"
  by auto

ML_file \<open>~~/src/HOL/Import/import_rule.ML\<close>

end

