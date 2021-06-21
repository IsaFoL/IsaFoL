theory Version
  imports Main
begin

text \<open>This code was taken from IsaFoR and adapted to git. \<close>
local_setup \<open>
  let
    val version =
    trim_line (#1 (Isabelle_System.bash_output ("cd $ISAFOL/ && git rev-parse --short HEAD || echo unknown")))
  in
    Local_Theory.define
      ((\<^binding>\<open>version\<close>, NoSyn),
        ((\<^binding>\<open>version_def\<close>, []), HOLogic.mk_literal version)) #> #2
  end
\<close>

declare version_def [code]

end
