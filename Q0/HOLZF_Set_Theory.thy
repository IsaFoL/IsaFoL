theory HOLZF_Set_Theory imports "HOL-ZF.MainZF" Set_Theory begin

(* We prove that the set theory in MainZF lives up to our specification. *)
interpretation set_theory Elem Sep Power Sum Upair
  using Ext Sep Power subset_def Sum Upair by unfold_locales auto

 \<comment> \<open>but no interpretation of @{term model}\<close>

end
