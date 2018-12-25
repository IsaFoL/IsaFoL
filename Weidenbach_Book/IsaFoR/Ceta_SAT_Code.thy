theory Ceta_SAT_Code
  imports CeTA_SAT_Slow.Ceta_SAT
begin




ML \<open>@{term pre_logic_checker.check_valid_formula}\<close>
term pre_logic_checker.check_valid_formula
thm pre_logic_checker.check_valid_formula_def
thm IA.check_valid_formula
thm IA.check_valid_formula[unfolded IA.valid_def IA.assignment_def]
thm IA.formula.simps
term IA.check_clause
thm IA.check_clause_def
term flatten
thm flatten.simps
thm simplex
term simplex
thm pre_logic_checker.check_valid_formula_def
term pre_logic_checker.remove_Atom
thm pre_logic_checker.remove_Atom.simps
term check_allm
term IA_locale.check_clause
term IA_locale.unsat_checker
term IA_locale.unsat_via_simplex
thm IA_locale.unsat_via_simplex_def

text \<open>Function that should be replaced @{term pre_logic_checker.check_valid_formula}
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
\<close>
term check_valid_formula
thm IA.to_simplex_constraint_def
term simplex
thm simplex_def

term \<open>v \<Turnstile>\<^sub>c c\<close>
lemma \<open>simplex A = None\<close>
  unfolding
    simplex_def
    solve_exec_code_def
    [unfolded SolveExec'.solve_exec_def[OF SolveExec'Default.SolveExec'_axioms]]
    solve_exec_ns_code_def
    Solve_exec_ns'.solve_exec_ns_def[OF Solve_exec_ns'Default.Solve_exec_ns'_axioms]
  unfolding
    (* assert_all_code_def *) AssertAllState.assert_all_def[OF AssertAllStateDefault.AssertAllState_axioms]
  AssertAllStateDefault.assert_all_def
  AssertAllStateDefault.assert_all_state_def
  AssertAllStateDefault.assert_bound_loop_def
RhsEqValDefault.assert_bound_def
  apply (cases \<open>preprocess (to_ns A)\<close>)
  apply auto

  thm AssertAllStateDefault.assert_all_def
  thm 
AssertAllState.assert_all_def[OF AssertAllStateDefault.AssertAllState_axioms]
    Solve_exec_ns'.solve_exec_ns_def
    Solve_exec_ns'.solve_exec_ns_def[OF Solve_exec_ns'Default.Solve_exec_ns'_axioms]
  AssertAllStateDefault.assert_all_state_def[unfolded AssertAllStateDefault.assert_bound_loop_def]
   SolveExec'Default.simplex_sat0
   AssertAllStateDefault.assert_all_state_def
   AssertAllStateDefault.assert_bound_loop_def
ML \<open>
  BNF_FP_Def_Sugar.fp_sugar_of @{context} @{type_name dp_termination_proof}
  |> the 
  |> #fp_ctr_sugar
  |> #ctr_sugar
  |> #ctrs
\<close>
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

abbreviation claim_assn :: \<open>('f, 'l) claim \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>claim_assn \<equiv> id_assn\<close>

abbreviation proof_assn :: \<open>('f, 'l, 'v) proof \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>proof_assn \<equiv> id_assn\<close>

named_theorems isafor_string_names "various strings for code generation"

definition string_eq_of where
  \<open>string_eq_of = '' of ''\<close>

declare string_eq_of_def[symmetric, isafor_string_names]

lemma string_eq_of_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_of), uncurry0 (RETURN string_eq_of)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)


definition string_eq_by where
  \<open>string_eq_by = '' by ''\<close>

declare string_eq_by_def[symmetric, isafor_string_names]

lemma string_eq_by_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_by), uncurry0 (RETURN string_eq_by)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

definition string_eq_mes3 where
  \<open>string_eq_mes3 = ''Confluence with start term not supported''\<close>

declare string_eq_mes3_def[symmetric, isafor_string_names]

lemma string_eq_mes3_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes3), uncurry0 (RETURN string_eq_mes3)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

definition string_eq_mes4 where
  \<open>string_eq_mes4 = ''Claiming ''\<close>

declare string_eq_mes4_def[symmetric, isafor_string_names]

lemma string_eq_mes4_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes4), uncurry0 (RETURN string_eq_mes4)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

definition string_eq_mes5 where
  \<open>string_eq_mes5 = ''1''\<close>

declare string_eq_mes5_def[symmetric, isafor_string_names]

lemma string_eq_mes5_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes5), uncurry0 (RETURN string_eq_mes5)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

definition string_eq_mes6 where
  \<open>string_eq_mes6 =  ''Confluence under strategy not supported''\<close>

declare string_eq_mes6_def[symmetric, isafor_string_names]

lemma string_eq_mes6_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes6), uncurry0 (RETURN string_eq_mes6)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

definition string_eq_mes7 where
  \<open>string_eq_mes7 =  ''Relative confluence not supported''\<close>

declare string_eq_mes7_def[symmetric, isafor_string_names]

lemma string_eq_mes7_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes7), uncurry0 (RETURN string_eq_mes7)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

thm ac_simps

definition string_eq_mes8 where
  \<open>string_eq_mes8 =  ''complexity class mismatch''\<close>

declare string_eq_mes8_def[symmetric, isafor_string_names]

lemma string_eq_mes8_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes8), uncurry0 (RETURN string_eq_mes8)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)


definition string_eq_mes9 where
  \<open>string_eq_mes9 =  ''Nonconfluence with start term not supported''\<close>

declare string_eq_mes9_def[symmetric, isafor_string_names]

lemma string_eq_mes9_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes9), uncurry0 (RETURN string_eq_mes9)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)


definition string_eq_mes10 where
  \<open>string_eq_mes10 =  ''Relative nonconfluence not supported''\<close>

declare string_eq_mes10_def[symmetric, isafor_string_names]

lemma string_eq_mes10_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes10), uncurry0 (RETURN string_eq_mes10)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

(*
''complexity class mismatch''
''Relative nonconfluence not supported''

 *)
lemma case_input_swap:
  \<open>f (case x of
        DP_input x xa xb xc \<Rightarrow> f10 x xa xb xc
      | Inn_TRS_input x xa xb xc \<Rightarrow> f20 x xa xb xc
      | CPX_input x xa xb xc xd \<Rightarrow> f30 x xa xb xc xd
      | COMP_input x xa \<Rightarrow> f40 x xa
      | OCOMP_input x xa xb xc \<Rightarrow> f50 x xa xb xc
      | EQ_input x xa \<Rightarrow> f60 x xa
      | FP_TRS_input x xa \<Rightarrow> f70 x xa
      | CTRS_input x \<Rightarrow> f80 x
      | TA_input x xa \<Rightarrow> f90 x xa
      | AC_input x xa xb \<Rightarrow> f100 x xa xb
      | LTS_input x \<Rightarrow> f110 x
      | LTS_safety_input x xa \<Rightarrow> f120 x xa
      | Unknown_input x \<Rightarrow> f130 x) =
   (case x of
        DP_input x xa xb xc \<Rightarrow> f (f10 x xa xb xc)
      | Inn_TRS_input x xa xb xc \<Rightarrow> f (f20 x xa xb xc)
      | CPX_input x xa xb xc xd \<Rightarrow> f (f30 x xa xb xc xd)
      | COMP_input x xa \<Rightarrow> f (f40 x xa)
      | OCOMP_input x xa xb xc \<Rightarrow> f (f50 x xa xb xc)
      | EQ_input x xa \<Rightarrow> f (f60 x xa)
      | FP_TRS_input x xa \<Rightarrow> f (f70 x xa)
      | CTRS_input x \<Rightarrow> f (f80 x)
      | TA_input x xa \<Rightarrow> f (f90 x xa )
      | AC_input x xa xb \<Rightarrow> f (f100 x xa xb)
      | LTS_input x \<Rightarrow> f (f110 x)
      | LTS_safety_input x xa \<Rightarrow> f (f120 x xa)
      | Unknown_input x \<Rightarrow> f (f130 x))\<close>
  by (cases x) auto

lemma case_proof_swap:
  \<open>P (case proof of
       TRS_Termination_Proof x \<Rightarrow> f10 x
     | Complexity_Proof x \<Rightarrow> f20 x
     | DP_Termination_Proof x \<Rightarrow> f30 x
     | DP_Nontermination_Proof x \<Rightarrow> f40 x
     | TRS_Nontermination_Proof x \<Rightarrow> f50 x
     | FP_Termination_Proof x \<Rightarrow> f60 x
     | Relative_TRS_Nontermination_Proof x \<Rightarrow> f70 x
     | TRS_Confluence_Proof x \<Rightarrow> f80 x
     | TRS_Non_Confluence_Proof x \<Rightarrow> f90 x
     | Completion_Proof x \<Rightarrow> f100 x
     | Ordered_Completion_Proof x \<Rightarrow> f110 x
     | Equational_Proof x \<Rightarrow> f120 x
     | Equational_Disproof x \<Rightarrow> f130 x
     | Quasi_Reductive_Proof x \<Rightarrow> f140 x
     | Conditional_CR_Proof x \<Rightarrow> f150 x
     | Conditional_Non_CR_Proof x \<Rightarrow> f160 x
     | Tree_Automata_Closed_Proof x \<Rightarrow> f170 x
     | AC_Termination_Proof x \<Rightarrow> f180 x
     | LTS_Termination_Proof x \<Rightarrow> f190 x
     | LTS_Safety_Proof x \<Rightarrow> f200 x
     | Unknown_Proof x \<Rightarrow> f210 x
     | Unknown_Disproof x \<Rightarrow> f220 x) =
  (case proof of
      TRS_Termination_Proof x \<Rightarrow> P (f10 x )
    | Complexity_Proof x \<Rightarrow> P (f20 x )
    | DP_Termination_Proof x \<Rightarrow> P (f30 x)
    | DP_Nontermination_Proof x \<Rightarrow> P (f40 x)
    | TRS_Nontermination_Proof x \<Rightarrow> P (f50 x )
    | FP_Termination_Proof x \<Rightarrow> P (f60 x )
    | Relative_TRS_Nontermination_Proof x \<Rightarrow> P (f70 x)
    | TRS_Confluence_Proof x \<Rightarrow> P (f80 x)
    | TRS_Non_Confluence_Proof x \<Rightarrow> P (f90 x)
    | Completion_Proof x \<Rightarrow> P (f100 x)
    | Ordered_Completion_Proof x \<Rightarrow> P (f110 x)
    | Equational_Proof x \<Rightarrow> P (f120 x)
    | Equational_Disproof x \<Rightarrow> P (f130 x)
    | Quasi_Reductive_Proof x \<Rightarrow> P (f140 x)
    | Conditional_CR_Proof x \<Rightarrow> P (f150 x)
    | Conditional_Non_CR_Proof x \<Rightarrow> P (f160 x)
    | Tree_Automata_Closed_Proof x \<Rightarrow> P (f170 x)
    | AC_Termination_Proof x \<Rightarrow> P (f180 x)
    | LTS_Termination_Proof x \<Rightarrow> P (f190 x )
    | LTS_Safety_Proof x \<Rightarrow> P (f200 x)
    | Unknown_Proof x \<Rightarrow> P (f210 x)
    | Unknown_Disproof x \<Rightarrow> P (f220 x))\<close>
  by (cases "proof") auto

definition check_cert_args_mismatch where
   \<open>check_cert_args_mismatch input claim proof =
      (shows (''Claiming '' @ claim_to_string claim @ '' of '' @ input_to_string input @ '' by '' @ proof_to_string proof))\<close>

lemma [sepref_fr_rules]:
 \<open>(uncurry3 (return oooo check_cert_args_mismatch), uncurry3 (RETURN oooo check_cert_args_mismatch)) \<in>
   input_assn\<^sup>k  *\<^sub>a claim_assn\<^sup>k  *\<^sub>a proof_assn\<^sup>k *\<^sub>a string_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  unfolding unfold_to_id_assn input_assn_def
  by sepref_to_hoare (sep_auto)
(* 
datatype (dead 'f, dead 'v) input =
  DP_input "bool" "('f, 'v) rules" "('f, 'v) strategy" "('f, 'v) rules"
| Inn_TRS_input "('f, 'v) strategy" "('f, 'v) rules" "('f, 'v) rules" "start_term"
| CPX_input  "('f, 'v) strategy" "('f, 'v) rules" "('f, 'v) rules" "('f,'v) complexity_measure" complexity_class (* TODO: improve CPF and remove*)
| COMP_input "('f, 'v) equation list" "('f, 'v) rules"
| OCOMP_input "('f, 'v) equation list" "('f, 'v) equation list" "('f, 'v) rules" "'f reduction_order_input"
| EQ_input "('f, 'v) equation list" "('f, 'v) equation_literal"
| FP_TRS_input "('f, 'v) fp_strategy" "('f, 'v) rules"
| CTRS_input "('f, 'v) crules"
| TA_input "(string,'f)tree_automaton" "('f,'v)rules"
| AC_input "('f,'v) rules" "'f list" "'f list"
| LTS_input "(IA.sig, 'v, IA.ty, string, string) lts_impl"
| LTS_safety_input "(IA.sig, 'v, IA.ty, string, string) lts_impl" "string list"
| Unknown_input unknown_info
 *)
lemma 1:
  \<open>RETURN o (\<lambda>x. f x) = (\<lambda>x. RETURN (f x))\<close>
  by auto
(* sepref_definition certify_prob_code
  is \<open>uncurry3 (RETURN oooo check_cert_args)\<close>
  :: \<open>bool_assn\<^sup>k *\<^sub>a input_assn\<^sup>k  *\<^sub>a claim_assn\<^sup>k  *\<^sub>a proof_assn\<^sup>k \<rightarrow>\<^sub>a pure_fun_assn +\<^sub>a unit_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_cert_args_def check_cert_def pull_out_let_conv check_cert_args_mismatch_def[symmetric]
    case_input_swap 1 case_proof_swap Let_def
  unfolding isafor_string_names
  apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  oops *)
          (*  apply sepref_dbg_side_unfold apply (auto simp: )[] *)

term sum_assn
lemma certify_prob_hnr[sepref_fr_rules]:
  \<open>(uncurry3 (return oooo check_cert_args), uncurry3 (RETURN oooo check_cert_args)) \<in>
        bool_assn\<^sup>k *\<^sub>a input_assn\<^sup>k  *\<^sub>a id_assn\<^sup>k  *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a pure_fun_assn +\<^sub>a unit_assn\<close>
  by sepref_to_hoare (sep_auto simp: input_assn_def unfold_to_id_assn pure_fun_assn_def
      id_assn_eq_iff list_assn_pure_conv')

lemma Certified_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return Certified), uncurry0 (RETURN Certified)) \<in>
   unit_assn\<^sup>k \<rightarrow>\<^sub>a cert_result_assn\<close>
  by sepref_to_hoare (sep_auto)

sepref_definition certify_prob_code
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

(* export_code certify_proof_code in Haskell module_name Ceta file "code/ceta.hs"
export_code certify_proof in Haskell module_name Ceta file "code/ceta_normal.hs" *)
export_code certify_proof_code in SML module_name Ceta file "code/ceta.sml"
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