theory Ceta_SAT_Code
  imports CeTA_SAT_Import.Ceta_SAT
begin

lemma [code del]: "mset xs - mset ys = mset (fold remove1 ys xs)"
  by (rule sym, induct ys arbitrary: xs) (simp_all add: diff_add diff_right_commute diff_diff_add)

(* export_code certify_proof
(* Certified Unsupported Error Inl Inr sumbot
(* remove, after defining an XML format: *)
  Yes No Terminating Upperbound Nonterminating Confluent Nonconfluent Completed Anything
  nat_of_integer *)
  in SML module_name Ceta file "code/test.sml" *)

lemma list_assn_pure_conv':
  \<open>list_assn (\<lambda>a c. \<up> (c = a)) = pure (\<langle>Id\<rangle>list_rel)\<close>
  unfolding pure_def[symmetric] list_assn_pure_conv
  pair_in_Id_conv[symmetric]
  ..

lemma id_assn_eq_iff: \<open>id_assn a b = (\<up> (a = b))\<close>
  unfolding pure_def by auto


lemma id_assn_alt': \<open>(\<lambda>a c. \<up> (c = a)) = id_assn\<close>
  unfolding pure_def[symmetric] pair_in_Id_conv[symmetric]
  by auto

abbreviation char_assn :: \<open>char \<Rightarrow> char \<Rightarrow> assn\<close> where
  \<open>char_assn \<equiv> id_assn\<close>

abbreviation string_assn where
  \<open>string_assn \<equiv> list_assn char_assn\<close>

lemma unfold_to_id_assn:
  \<open>option_assn id_assn = id_assn\<close>
  \<open>string_assn = id_assn\<close>
  \<open>(\<lambda>a c. \<up> (c = a)) = id_assn\<close>
  \<open>(\<lambda>a c. emp) = unit_assn\<close>
     apply (intro ext; auto simp: option_assn_alt_def list_assn_pure_conv' id_assn_eq_iff
      split: option.splits; fail)
    apply (intro ext; auto simp: option_assn_alt_def list_assn_pure_conv; fail)
   apply (intro ext; auto simp: option_assn_alt_def list_assn_pure_conv id_assn_eq_iff; fail)
  apply (intro ext; auto simp: option_assn_alt_def list_assn_pure_conv id_assn_eq_iff; fail)
  done

lemma plain_name_hnr[sepref_fr_rules]:
  \<open>(return o plain_name, RETURN o plain_name) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn +\<^sub>a id_assn\<close>
  supply plain_name.simps[simp del]
  unfolding sum_assn_id
  by (sepref_to_hoare) sep_auto

abbreviation cert_result_assn :: \<open>cert_result \<Rightarrow> cert_result \<Rightarrow> assn\<close> where
  \<open>cert_result_assn \<equiv> id_assn\<close>

definition parse_xtc_plain_name where
  \<open>parse_xtc_plain_name = parse_xtc plain_name\<close>


definition pure_fun_assn :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> assn\<close> where
  \<open>pure_fun_assn = id_assn\<close>

definition fun_comp where
  \<open>fun_comp f x = f x\<close>

lemma fun_comp_hnr:
  \<open>(uncurry (return oo (\<lambda>f x. f x)), uncurry (RETURN oo fun_comp)) \<in>
     pure_fun_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by sepref_to_hoare (sep_auto simp: pure_fun_assn_def fun_comp_def)

lemma fun_comp_list_hnr:
  \<open>(uncurry (return oo (\<lambda>f x. f x)), uncurry (RETURN oo fun_comp)) \<in>
     pure_fun_assn\<^sup>k *\<^sub>a (list_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a list_assn id_assn\<close>
  by sepref_to_hoare (sep_auto simp: pure_fun_assn_def fun_comp_def id_assn_eq_iff list_assn_pure_conv')



definition input_assn
  :: \<open>((string, nat list) lab, string) input \<Rightarrow> ((string, nat list) lab, string) input \<Rightarrow> assn\<close>
where
  \<open>input_assn = id_assn\<close>


lemma parse_xtc_plain_name_hnr[sepref_fr_rules]:
  \<open>(return o parse_xtc_plain_name, RETURN o (parse_xtc_plain_name)) \<in>
    string_assn\<^sup>k \<rightarrow>\<^sub>a (sum_assn string_assn input_assn)\<close>
  by (sepref_to_hoare) (sep_auto elim!: sum_assn.elims simp: input_assn_def id_assn_eq_iff
      list_assn_pure_conv')


lemma Error_hnr[sepref_fr_rules]:
  \<open>(return o Error, RETURN o Error) \<in> string_assn\<^sup>k \<rightarrow>\<^sub>a cert_result_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: list_assn_pure_conv')

definition parse_claim_plain_name :: "string \<Rightarrow> string + ('a, 'b) claim" where
  \<open>parse_claim_plain_name = parse_claim plain_name\<close>


lemma parse_claim_plain_name_hnr[sepref_fr_rules]:
  \<open>(return o parse_claim_plain_name, RETURN o (parse_claim_plain_name)) \<in>
    string_assn\<^sup>k \<rightarrow>\<^sub>a (sum_assn string_assn id_assn)\<close>
  unfolding sum_assn_id unfold_to_id_assn
  by (sepref_to_hoare) (sep_auto elim!: sum_assn.elims
      simp: input_assn_def id_assn_eq_iff list_assn_pure_conv')

lemma parse_cert_problem_hnr[sepref_fr_rules]:
  \<open>(return o parse_cert_problem, RETURN o (parse_cert_problem)) \<in>
    string_assn\<^sup>k \<rightarrow>\<^sub>a (sum_assn string_assn (option_assn input_assn *a id_assn))\<close>
  by (sepref_to_hoare) (sep_auto elim!: sum_assn.elims simp: input_assn_def id_assn_eq_iff id_assn_alt'
      unfold_to_id_assn)

definition no_input_pb where
  \<open>no_input_pb = ''missing input problem''\<close>

lemma no_input_pb_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return no_input_pb), uncurry0 (RETURN no_input_pb)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

definition certify_prob where
  \<open>certify_prob = certify_cert_problem tp_impl
               Ceta_Verifier.dpp_impl ac_tp_impl
               Ceta_Verifier.ac_dpp_impl\<close>

definition check_cert_args where
  \<open>check_cert_args = check_cert tp_impl Ceta_Verifier.dpp_impl ac_tp_impl
                      Ceta_Verifier.ac_dpp_impl\<close>

lemma certify_prob_hnr[sepref_fr_rules]:
  \<open>(uncurry3 (return oooo check_cert_args), uncurry3 (RETURN oooo check_cert_args)) \<in>
        bool_assn\<^sup>k *\<^sub>a input_assn\<^sup>k  *\<^sub>a id_assn\<^sup>k  *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a pure_fun_assn +\<^sub>a unit_assn\<close>
  by sepref_to_hoare (sep_auto simp: input_assn_def unfold_to_id_assn pure_fun_assn_def
      id_assn_eq_iff list_assn_pure_conv')

lemma Certified_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return Certified), uncurry0 (RETURN Certified)) \<in>
   unit_assn\<^sup>k \<rightarrow>\<^sub>a cert_result_assn\<close>
  by sepref_to_hoare (sep_auto)

sepref_definition  certify_prob_code
  is \<open>uncurry3 (RETURN oooo certify_prob)\<close>
  :: \<open>bool_assn\<^sup>k *\<^sub>a input_assn\<^sup>k  *\<^sub>a id_assn\<^sup>k  *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a cert_result_assn\<close>
  supply fun_comp_list_hnr[sepref_fr_rules]
  unfolding certify_prob_def certify_cert_problem_def check_cert_args_def[symmetric]
    HOL_list.fold_custom_empty
  apply (rewrite at \<open>Error(_  \<hole>)\<close> annotate_assn[where A = \<open>string_assn\<close>])
  apply (rewrite at \<open>Error(\<hole>)\<close> fun_comp_def[symmetric])
  by sepref

declare certify_prob_code.refine[sepref_fr_rules]

(* "bool \<Rightarrow> string option \<Rightarrow> (_,_)claim + string \<Rightarrow> string \<Rightarrow> cert_result" where *)
sepref_definition certify_proof_code
  is \<open>uncurry3 (RETURN oooo certify_proof)\<close>
  :: \<open>bool_assn\<^sup>k *\<^sub>a (option_assn string_assn)\<^sup>k *\<^sub>a (sum_assn id_assn string_assn)\<^sup>k *\<^sub>a string_assn\<^sup>k \<rightarrow>\<^sub>a
      cert_result_assn\<close>
  supply[[goals_limit=1]]
  unfolding certify_proof_def parse_xtc_plain_name_def[symmetric]
    parse_claim_plain_name_def[symmetric] certify_prob_def[symmetric]
    no_input_pb_def[symmetric]
  by sepref

lemma prod_assn_id_assn_id_assn:
  \<open>id_assn *a id_assn = id_assn\<close>
  by auto

theorem certify_proof_code_sound:
  assumes ret: "certify_proof_code False (Some input_str) (Inr claim_str) proof_str = return Certified"
  shows "\<exists>input claim.
    parse_xtc plain_name input_str = Inr input \<and>
    parse_claim plain_name claim_str = Inr claim \<and>
    desired_property input claim"
proof -
  have [simp]: \<open>id_assn a b = \<up>(a =b)\<close> for a b
    by (auto simp: pure_def)
  have H:
    \<open><emp>
       certify_proof_code a b ba bb
       <\<lambda>r. \<exists>\<^sub>Ax. true *
                   \<up> (x = r \<and>
                      x =
                      certify_proof a b ba
                       bb)>\<close>
    for a b ba bb
    using certify_proof_code.refine
    unfolding hfref_def unfold_to_id_assn sum_assn_id hfprod_fst_snd keep_drop_sels
      prod_assn_id_assn_id_assn
    by (auto simp: unfold_to_id_assn hn_refine_def)
  have H:\<open>(h, as) \<Turnstile> emp \<and>
       Run.run (Heap_Monad.return Certified)
        (Some h) \<sigma> r \<longrightarrow>
       \<not> is_exn \<sigma> \<and>
       in_range
        (the_state \<sigma>,
         new_addrs h as (the_state \<sigma>)) \<and>
       r =
       certify_proof False (Some input_str)
        (Inr claim_str) proof_str \<and>
       relH {a. a < heap.lim h \<and> a \<notin> as} h
        (the_state \<sigma>) \<and>
       heap.lim h \<le> heap.lim (the_state \<sigma>)\<close>
    for h as r \<sigma>
    using ret H[of False \<open>Some input_str\<close> \<open>Inr claim_str\<close> \<open>proof_str\<close>]
    by (auto simp: unfold_to_id_assn hn_refine_def hoare_triple_def)


  show ?thesis
    apply (rule certify_proof_sound[where proof_str = \<open>proof_str\<close>])
    using ret H[of \<open>_\<close> \<open>{}\<close>]
    by (auto simp: run.simps return_def Heap_Monad.heap_def)
qed

thm certify_proof_def
thm check_cert_def
thm certify_cert_problem_def
thm certify_proof_def
(*
  apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
           apply sepref_dbg_trans_step_keep
           apply sepref_dbg_side_unfold apply (auto simp: )[]
 *)

(* export_code certify_proof_code in Haskell module_name Ceta *)

text \<open>Function that shoul be replaced @{term pre_logic_checker.check_valid_formula}
  @{term pre_logic_checker.check_valid_formula} is called by
  @{term pre_logic_checker.check_valid_formula} called by
  @{term pre_logic_checker.check_formula} called by
  @{term pre_art_checker.check_simulation_cond} and @{term pre_logic_checker.safe_by_assertion_checker}

    for @{term pre_art_checker.check_simulation_cond}
    @{term pre_art_checker.check_art_invariants}  called by
    @{term pre_art_checker.check_art_invariants_impl} called by
    @{term pre_art_checker.invariant_proof_checker}  called by
      @{term pre_art_checker.check_safety} (in the other call too)
      @{term pre_termination_checker.check_cooperation_proof} called by
       @{term pre_termination_checker.check_termination_proof} called by
       @{term pre_termination_checker.check} called by
       @{term IA_locale.check_termination} called by
       @{term check_cert} called by
       @{term certify_cert_problem}


     for @{term pre_logic_checker.safe_by_assertion_checker}, calls by
     @{term pre_art_checker.check_safety_proof} called by
     @{term pre_art_checker.check_safety} called by
     @{term check_cert} called by
     @{term certify_cert_problem}
  \<close>

end