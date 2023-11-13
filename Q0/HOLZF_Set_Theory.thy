section \<open>Isabelle/HOLZF lives up to CakeML's set theory specification\<close>

theory HOLZF_Set_Theory imports "HOL-ZF.MainZF" Set_Theory begin

interpretation set_theory Elem Sep Power Sum Upair
  using Ext Sep Power subset_def Sum Upair by unfold_locales auto

end
