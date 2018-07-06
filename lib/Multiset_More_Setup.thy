theory "Multiset_More_Setup"
imports "/home/zmaths/isabelle/isabelle/src/HOL/Mirabelle/Mirabelle" "Main"
begin

ML_file "/home/zmaths/isabelle/isabelle/src/HOL/Mirabelle/Tools/mirabelle_sledgehammer.ML"


setup {*
  Config.put_global Mirabelle.logfile "lib/Multiset_More.log" #>
  Config.put_global Mirabelle.timeout 30 #>
  Config.put_global Mirabelle.start_line 0 #>
  Config.put_global Mirabelle.end_line ~1
*}

setup {* Mirabelle_Sledgehammer.invoke [("prover", "verit"), ("isar_proofs", ""), ("minimize", "")] *}

end