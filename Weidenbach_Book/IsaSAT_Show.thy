theory IsaSAT_Show
  imports
    Show.Show_Instances
    IsaSAT_Setup
begin

subsection \<open>Printing information about progress\<close>

text \<open>We provide a function to print some information about the state.
  This is mostly meant to ease extracting statistics and printing information
  during the run. 
  Remark that this function is basically an FFI (to follow Andreas Lochbihler words) and is
  not unsafe (since printing has not side effects), but we do not need any correctness theorems.
  
  However, it seems that the PolyML by \<open>export_code checking\<close> does
  not support that print function. Therefore, we cannot provide the code printing equations
  by default.\<close>
definition print_string :: \<open>String.literal \<Rightarrow> unit\<close> where
  \<open>print_string _ = ()\<close>

definition print_lvl where
  \<open>print_lvl n = print_string (String.implode (show n))\<close>

instantiation uint64 :: "show"
begin
definition shows_prec_uint64 :: \<open>nat \<Rightarrow> uint64 \<Rightarrow> char list \<Rightarrow> char list\<close> where
  \<open>shows_prec_uint64 n m xs = shows_prec n (nat_of_uint64 m) xs\<close>

definition shows_list_uint64 :: \<open>uint64 list \<Rightarrow> char list \<Rightarrow> char list\<close> where
  \<open>shows_list_uint64 xs ys = shows_list (map nat_of_uint64 xs) ys\<close>
instance
  by standard
    (auto simp: shows_prec_uint64_def shows_list_uint64_def
      shows_prec_append shows_list_append)
end

instantiation uint32 :: "show"
begin
definition shows_prec_uint32 :: \<open>nat \<Rightarrow> uint32 \<Rightarrow> char list \<Rightarrow> char list\<close> where
  \<open>shows_prec_uint32 n m xs = shows_prec n (nat_of_uint32 m) xs\<close>

definition shows_list_uint32 :: \<open>uint32 list \<Rightarrow> char list \<Rightarrow> char list\<close> where
  \<open>shows_list_uint32 xs ys = shows_list (map nat_of_uint32 xs) ys\<close>
instance
  by standard
    (auto simp: shows_prec_uint32_def shows_list_uint32_def
      shows_prec_append shows_list_append)
end

code_printing constant
  print_string \<rightharpoonup> (SML) "ignore/ (print/ ((_)))"

export_code print_lvl in SML
code_printing constant
  print_string \<rightharpoonup> (SML)
export_code print_lvl checking SML

end