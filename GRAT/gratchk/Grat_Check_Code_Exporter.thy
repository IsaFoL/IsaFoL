section \<open>Code Generation and Summary of Correctness Theorems\<close>
theory Grat_Check_Code_Exporter
imports Unsat_Check Sat_Check
begin
  subsection \<open>Code Generation\<close>
  text \<open>We generate code for @{const verify_unsat_impl_wrapper} 
    and @{const verify_sat_impl_wrapper}.

    The first statement is a sanity check, that will make our automated 
    regression tests fail if the generated code does not compile.

    The second statement actually exports the two main functions, and 
    some auxiliary functions to convert between SML and Isabelle integers,
    and to access the sum data type of Isabelle, which is used to encode 
    the checker's result.
  \<close>
  
  export_code verify_unsat_impl_wrapper verify_sat_impl_wrapper checking SML_imp  
    
  export_code 
    verify_sat_impl_wrapper 
    verify_unsat_impl_wrapper 
    int_of_integer
    integer_of_int
    integer_of_nat
    nat_of_integer    
    
    isl projl projr Inr Inl
  in SML_imp module_name Grat_Check file "code/gratchk_export.sml"

  subsection \<open>Summary of Correctness Theorems\<close>
  text \<open>In this section, we re-prove the correctness theorems that are 
    proved elsewhere, slightly adapting them for optimal presentation.

    The goal of this section is to provide a step-by-step justification of
    the trusted base of our specification, only building on well-known 
    standard functions.
  \<close>
    
  text \<open>
    As we only prove soundness, our lemmas do not mention the structure of 
    the certificate at all. However, in order not to fail, we expect a 
    non-contradictory list of literals that satisfy the formula, 
    or a GRAT unsat certificate, respectively.
  \<close>
    
  subsubsection \<open>Interpreting an Integer List as Formula\<close>    
  text \<open>First, we show how to interpret a formula.
    A formula is represented according to the de facto standard for 
    encoding CNF formulas: Variables are identified by positive integers. 
    Negative integers encode negated variables. A clause is a 
    null-terminated string of integers, and the formula is simply the 
    concatenation of its clauses.
 
    Any list that is empty, or ends with a null, can be interpreted as formula.
    To this end, we define:
  \<close>
  definition intlist_invar :: "int list \<Rightarrow> bool" 
    where "intlist_invar lst \<equiv> lst\<noteq>[] \<longrightarrow> last lst = 0"  

  text \<open>  
    Next, we have to define how to split the list into clauses.
    As splitting is harder to define than composition, we simply define 
    splitting as the (unique) inverse of concatenating the lists again.
    
    For a flat list \<open>lst\<close>, and a list of lists \<open>ll\<close>, the following predicate
    states that \<open>ll\<close> contains no nulls, and \<open>lst\<close> can be constructed by 
    concatenating \<open>ll\<close>, terminating each part with a null.
  \<close>
  definition is_concatenation :: "int list \<Rightarrow> int list list \<Rightarrow> bool"
    where "is_concatenation lst ll 
      \<equiv> (\<forall>l\<in>set ll. 0\<notin>set l) \<and> concat (map (\<lambda>l . l@[0]) ll) = lst"  

  text \<open>We show that for each valid flat \<open>lst\<close>, 
    there is exactly one list of lists \<open>ll\<close> with 
    @{prop \<open>is_concatenation lst ll\<close>}. 
    We call this list of lists \<open>tokenize 0 lst\<close>.
    \<close>
  lemma 
    assumes "intlist_invar lst"
    shows "\<exists>!ll. is_concatenation lst ll"  
      and "tokenize 0 lst = (THE ll. is_concatenation lst ll)"
    using assms unique_tokenization[of lst 0] tokenize_spec[of lst 0] 
    unfolding intlist_invar_def concat_sep_by_concat_map 
    unfolding is_concatenation_def
    by auto  
    
  text \<open>
    As last step, we convert the list of lists to a set of sets, 
    i.e., we identify equal literals in clauses, and equal clauses in 
    the formula. Obviously, this does not affect satisfiability.
  \<close>
  definition parse_intlist :: "int list \<Rightarrow> int set set" 
    where "parse_intlist lst \<equiv> set ` set (tokenize 0 lst)"  

  subsubsection \<open>Satisfiable Formulas\<close>
  text \<open>
    Next, we define satisfiable formulas. 
    A concise way is to use a mapping \<open>\<sigma>\<close> from literals (i.e. integers) to
    Booleans, which is required to be consistent, i.e., opposite literals 
    are mapped to opposite values. Then, the formula is satisfiable iff 
    there exists a consistent mapping, such that every clause has a literal
    mapped to \<open>True\<close>.
  \<close>    
  lemma "assn_consistent \<sigma> \<longleftrightarrow> (\<forall>l. l\<noteq>0 \<longrightarrow> \<sigma> l = (\<not> \<sigma> (-l)))"  
    unfolding assn_consistent_def by blast
  definition intset_sat :: "int set set \<Rightarrow> bool"
    where "intset_sat F \<equiv> \<exists>\<sigma>. assn_consistent \<sigma> \<and> (\<forall>C\<in>F. \<exists>l\<in>C. \<sigma> l)"
    
  text \<open>Finally, we get predicates that state that an integer list 
    represents a valid (un)satisfiable formula\<close>  
  definition intlist_repr_sat :: "int list \<Rightarrow> bool"
    where "intlist_repr_sat lst 
      \<equiv> intlist_invar lst \<and> intset_sat (parse_intlist lst)"
  definition intlist_repr_unsat :: "int list \<Rightarrow> bool"
    where "intlist_repr_unsat lst 
      \<equiv> intlist_invar lst \<and> \<not>intset_sat (parse_intlist lst)"
    
  text \<open>
    We choose the type @{typ "int set set"} to represent formulas.
    However, this type does not prevent us from having a null in a clause.
    
    The motivation for this choice was to avoid the introduction of 
    an additional literal data type in the specification, which would add 
    another level of indirection, and thus make it harder to read.

    Considering the possible null in a clause, we remark that, first, our 
    notion of satisfiability still makes sense, as it treats a null like any 
    other positive literal. Second, formulas that have been parsed from integer
    lists contain no nulls anyway:
  \<close>  
  lemma parse_intlist_contains_no_null:
    "intlist_invar lst \<Longrightarrow> \<forall>C\<in>parse_intlist lst. 0\<notin>C"  
    unfolding parse_intlist_def intlist_invar_def 
    using tokenize_complete[of lst 0] 
    by auto
    
    
  subsubsection \<open>Extracting the Formula from the Input Array\<close>    
  text \<open>
    Having defined predicates for an integer list representing a 
    satisfiable/unsatisfiable formula, we extend them to the actual input
    expected by our checker functions.

    These functions expect an integer array \<open>DBi\<close> (clause database) and an 
    index \<open>F_end\<close> (formula end).
    The first element of the array is unused (to have index \<open>0\<close> as a special value).
    The elements \<open>[1..<F_end]\<close> contain the formula, and the remaining array 
    contains the certificate.

    In order to extract the elements \<open>[1..<F_end]\<close> from a list, we use
    the term @{term "tl (take F_end DB)"}, i.e., take the 
    first \<open>F_end\<close> elements, and then throw away the first one. 
    This is a concise specification only using the standard list functions 
    of Isabelle/HOL.

    Thus, we get:
  \<close>
  definition DBF_sat :: "int list \<Rightarrow> nat \<Rightarrow> bool"
    where "DBF_sat DB F_end 
    \<equiv> F_end \<le> length DB \<and> intlist_repr_sat (tl (take F_end DB))"  
  definition DBF_unsat :: "int list \<Rightarrow> nat \<Rightarrow> bool"
    where "DBF_unsat DB F_end 
    \<equiv> F_end \<le> length DB \<and> intlist_repr_unsat (tl (take F_end DB))"  

  text \<open>  
    Note, that there are other, equivalent, ways to specify the 
      elements \<open>[1..<F_end]\<close> of a list, e.g.:
  \<close>
  lemma formula_sublist_by_map_nth_upt:
    "F_end \<le> length DB \<Longrightarrow> map (nth DB) [1..<F_end] = tl (take F_end DB)"
    using map_nth_upt_drop_take_conv[of F_end DB 1] by (auto simp: drop_Suc)
    
    
  subsubsection \<open>Hoare-Triples for our Checkers\<close>  
  text \<open>
    Finally, we prove Hoare-triples for the checker functions.
    The precondition just states that \<open>DBi\<close> points to an array containing the 
    elements \<open>DB\<close>:
  \<close>  
  theorem verify_sat_impl_wrapper_sound:
    shows "
      <DBi \<mapsto>\<^sub>a DB> 
        verify_sat_impl_wrapper DBi F_end 
      <\<lambda>result. DBi \<mapsto>\<^sub>a DB * \<up>(\<not>isl result \<longrightarrow> DBF_sat DB F_end) >\<^sub>t"
  proof -
    txt \<open>Note, also this proof is a bit more verbose, it's actually 
      only unfolding of definitions.\<close>
    
    have [simp]: "\<exists>\<sigma>. assn_consistent \<sigma>"
      apply (rule exI[where x="\<lambda>x. x<0"])
      unfolding assn_consistent_def by auto 
      
    have [simp]: "intlist_repr_sat []" 
      unfolding intlist_repr_sat_def intlist_invar_def 
                intset_sat_def parse_intlist_def 
      by auto  
      
    show ?thesis
      unfolding DBF_sat_def
      apply (rule cons_post_rule)
      apply (rule verify_sat_impl_wrapper_correct)
      apply solve_entails  
      subgoal unfolding formula_sat_spec_def Let_def by auto
      subgoal unfolding formula_sat_spec_def Let_def    
        apply1 (cases "F_end = 1"; clarsimp)  
        apply1 (clarsimp simp: F_\<alpha>_def alt_sat_sat_eq[OF tokenize_complete])
        unfolding alt_sat_def intlist_repr_sat_def intlist_invar_def 
                  intset_sat_def parse_intlist_def  
        by auto          
      done
  qed
    
  theorem verify_unsat_impl_wrapper_sound: 
    shows "
      <DBi \<mapsto>\<^sub>a DB> 
        verify_unsat_impl_wrapper DBi F_end it 
      <\<lambda>result. DBi \<mapsto>\<^sub>a DB * \<up>(\<not>isl result \<longrightarrow> DBF_unsat DB F_end) >\<^sub>t"
    apply (rule cons_post_rule)
    apply (rule verify_unsat_impl_wrapper_correct)
    apply (sep_auto 
        simp: formula_unsat_spec_alt' Let_def DBF_unsat_def
        simp: intlist_repr_unsat_def intlist_invar_def intset_sat_def parse_intlist_def)
    done
    
      
end
