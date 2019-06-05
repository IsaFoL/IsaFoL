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

  However, it seems that the PolyML as targeted by \<open>export_code checking\<close> does
  not support that print function. Therefore, we cannot provide the code printing equations
  by default.\<close>
definition println_string :: \<open>String.literal \<Rightarrow> unit\<close> where
  \<open>println_string _ = ()\<close>

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
  println_string \<rightharpoonup> (SML) "ignore/ (PolyML.print/ ((_) ^ \"\\n\"))"

definition test where
\<open>test  = println_string\<close>

code_printing constant
  println_string \<rightharpoonup> (SML)



subsection \<open>Print Information for IsaSAT\<close>

definition isasat_header :: string where
  \<open>isasat_header = show ''Conflict | Decision | Propagation | Restarts''\<close>

text \<open>Printing the information slows down the solver by a huge factor.\<close>
definition isasat_banner_content where
\<open>isasat_banner_content =
''c  conflicts       decisions     restarts     uset
c        propagations     reductions         GC    Learnt clauses ''\<close>

definition isasat_information_banner :: \<open>_ \<Rightarrow> unit nres\<close> where
\<open>isasat_information_banner _ =
    RETURN (println_string (String.implode (show isasat_banner_content)))\<close>

definition isasat_information_banner_code :: \<open>_ \<Rightarrow> unit Heap\<close> where
\<open>isasat_information_banner_code _ =
    return (println_string (String.implode (show isasat_banner_content)))\<close>

sepref_register isasat_information_banner
lemma isasat_information_banner_hnr[sepref_fr_rules]:
   \<open>(isasat_information_banner_code, isasat_information_banner) \<in>
   R\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by sepref_to_hoare (sep_auto simp: isasat_information_banner_code_def isasat_information_banner_def)

definition isasat_current_information :: \<open>stats \<Rightarrow> nat \<Rightarrow> unit\<close> where
\<open>isasat_current_information =
   (\<lambda>(propa, confl, decs, frestarts, lrestarts, uset, gcs) lcount.
      if confl AND 8191 = 8191 \<comment> \<open>\<^term>\<open>8191 = 8192 - 1\<close>, i.e., we print when all first bits are 1.\<close>
     then let c = '' | '' in
        println_string (String.implode (show ''c | '' @ show confl @ show c @ show propa @
          show c @ show decs @ show c @ show frestarts @ show c @ show lrestarts
          @ show c @ show gcs @ show c @ show uset @ show c @ show lcount))
      else ()
      )\<close>


definition print_current_information :: \<open>stats \<Rightarrow> nat \<Rightarrow> unit\<close> where
\<open>print_current_information _ _ = ()\<close>

lemma print_current_information_hnr[sepref_fr_rules]:
   \<open>(uncurry (return oo isasat_current_information), uncurry (RETURN oo print_current_information)) \<in>
   stats_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by sepref_to_hoare sep_auto

definition isasat_current_status :: \<open>twl_st_wl_heur \<Rightarrow> unit nres\<close> where
\<open>isasat_current_status =
   (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
       fast_ema, slow_ema, ccount, avdom,
       vdom, lcount, opts). RETURN (print_current_information stats lcount))\<close>

sepref_definition isasat_current_status_code
  is \<open>isasat_current_status\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_unbounded_assn_def isasat_current_status_def
  by sepref

declare isasat_current_status_code.refine[sepref_fr_rules]

sepref_definition isasat_current_status_fast_code
  is \<open>isasat_current_status\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_bounded_assn_def isasat_current_status_def
  by sepref

declare isasat_current_status_fast_code.refine[sepref_fr_rules]

end