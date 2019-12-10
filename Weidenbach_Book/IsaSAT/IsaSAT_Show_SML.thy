theory IsaSAT_Show_SML
  imports
    IsaSAT_Show
    IsaSAT_Setup_SML
begin

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


lemma isasat_current_information_alt_def:
\<open>isasat_current_information =
   (\<lambda>(propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds) lcount.
     if confl AND 8191 = 8191 \<comment> \<open>\<^term>\<open>8191 = 8192 - 1\<close>, i.e., we print when all first bits are 1.\<close>
     then let c = '' | '' in
        let _ = println_string (String.implode (show ''c | '' @ show confl @ show c @ show propa @
          show c @ show decs @ show c @ show frestarts @ show c @ show lrestarts
          @ show c @ show gcs @ show c @ show uset @ show c @ show lcount @ show c @ show (lbds >> 13))) in
        zero_some_stats (propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds)
      else (propa, confl, decs, frestarts, lrestarts, uset, gcs, lbds)
      )\<close>
  unfolding isasat_current_information_def by auto

definition isasat_information_banner_code :: \<open>_ \<Rightarrow> unit Heap\<close> where
\<open>isasat_information_banner_code _ =
    return (println_string (String.implode (show isasat_banner_content)))\<close>

sepref_register isasat_information_banner
lemma isasat_information_banner_hnr[sepref_fr_rules]:
   \<open>(isasat_information_banner_code, isasat_information_banner) \<in>
   R\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by sepref_to_hoare (sep_auto simp: isasat_information_banner_code_def isasat_information_banner_def)

sepref_register print_current_information


lemma print_current_information_hnr[sepref_fr_rules]:
   \<open>(uncurry (return oo isasat_current_information), uncurry (RETURN oo print_current_information)) \<in>
   stats_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a stats_assn\<close>
  by sepref_to_hoare (sep_auto simp: isasat_current_information_def print_current_information_def
    zero_some_stats_def)

lemma print_current_information_fast_hnr[sepref_fr_rules]:
   \<open>(uncurry (return oo isasat_current_information), uncurry (RETURN oo print_current_information)) \<in>
   stats_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a stats_assn\<close>
  by sepref_to_hoare (sep_auto simp: isasat_current_information_def print_current_information_def
    zero_some_stats_def)


sepref_definition isasat_current_status_code
  is \<open>isasat_current_status\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_unbounded_assn_def isasat_current_status_def
  by sepref

declare isasat_current_status_code.refine[sepref_fr_rules]

sepref_definition isasat_current_status_fast_code
  is \<open>isasat_current_status\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_bounded_assn_def isasat_current_status_def
  by sepref

declare isasat_current_status_fast_code.refine[sepref_fr_rules]

end