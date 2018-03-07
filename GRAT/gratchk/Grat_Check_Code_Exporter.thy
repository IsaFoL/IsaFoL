section \<open>Code Generation and Summary of Correctness Theorems\<close>
theory Grat_Check_Code_Exporter
imports Unsat_Check Unsat_Check_Split_MM Sat_Check
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
  
  export_code 
    verify_unsat_impl_wrapper 
    verify_unsat_split_impl_wrapper 
    verify_sat_impl_wrapper 
    checking SML_imp  
    
  export_code 
    verify_sat_impl_wrapper 
    verify_unsat_impl_wrapper 
    verify_unsat_split_impl_wrapper 
    int_of_integer
    integer_of_int
    integer_of_nat
    nat_of_integer    
    
    isl projl projr Inr Inl Pair
  in SML_imp module_name Grat_Check file "code/gratchk_export.sml"

subsection \<open>Summary of Correctness Theorems\<close> text_raw \<open>\label{sec:correctness_summary}\<close>
text \<open>In this section, we summarize the correctness theorems for our checker

  The precondition of the triples just state that their is an integer array, 
  which contains the DIMACS representation of the formula in the 
  segment from indexes @{term "[1..<F_end]"}. 
  The postcondition states that the array is not changed, 
  and, if the checker does not fail, the @{term F_end} index will be in range,
  the DIMACS representation of the formula is valid, and the represented 
  formula is satisfiable or unsatisfiable, respectively.

  Note that this only proved soundness of the checker, that is, the checker
  may always fail, but if it does not, we guarantee a valid 
  and (un)satisfiable formula.
\<close>
theorem 
  "<DBi \<mapsto>\<^sub>a DB> 
      verify_sat_impl_wrapper DBi F_end 
   <\<lambda>result. DBi \<mapsto>\<^sub>a DB * \<up>(\<not>isl result \<longrightarrow> verify_sat_spec DB F_end) >\<^sub>t"
  by (rule verify_sat_impl_wrapper_correct)    

theorem  
  "<DBi \<mapsto>\<^sub>a DB> 
      verify_unsat_impl_wrapper DBi F_end it
   <\<lambda>result. DBi \<mapsto>\<^sub>a DB * \<up>(\<not>isl result \<longrightarrow> verify_unsat_spec DB F_end) >\<^sub>t"
  by (rule verify_unsat_impl_wrapper_correct)
  
theorem  
  shows "
    <DBi \<mapsto>\<^sub>a DB> 
      verify_unsat_split_impl_wrapper DBi prf_next F_end it prf
    <\<lambda>result. DBi \<mapsto>\<^sub>a DB * \<up>(\<not>isl result \<longrightarrow> verify_unsat_spec DB F_end) >\<^sub>t"
  by (rule verify_unsat_split_impl_wrapper_correct)
  
text \<open>The specifications for a formula being valid and satisfiable/unsatisfiable
  can be written up in a very concise way, only relying on basic 
  list operations and the notion of a consistent assignment of truth values 
  to integers.
\<close>  

text \<open>An assignment is consistent, if each non-zero integer is assigned the 
  opposite of its negated value.\<close>
lemma "assn_consistent \<sigma> \<longleftrightarrow> (\<forall>l. l\<noteq>0 \<longrightarrow> \<sigma> l = (\<not> \<sigma> (-l)))"  
  by (rule assn_consistent_def)

text \<open>The input described a valid and satisfiable formula, iff the 
  @{term F_end} index is in range, the corresponding DIMACS string is empty
  or ends with a zero, and there is a consistent assignment such that each 
  represented clause contains a true literal.
\<close>    
lemma 
  "verify_sat_spec DB F_end \<equiv> 1\<le>F_end \<and> F_end \<le> length DB \<and> (
    let lst = tl (take F_end DB) in 
      (lst\<noteq>[] \<longrightarrow> last lst = 0)
    \<and> (\<exists>\<sigma>. assn_consistent \<sigma> \<and> (\<forall>C\<in>set (tokenize 0 lst). \<exists>l\<in>set C. \<sigma> l)))"
  by (rule verify_sat_spec_concise)

text \<open>
  The input describes a valid and unsatisfiable formula, iff @{term F_end} 
  is in range and does not describe the empty DIMACS string, the DIMACS string 
  ends with zero, and there exists no consistent assignment such that every 
  clause contains at least one literal assigned to true.
\<close>    
lemma
  "verify_unsat_spec DB F_end \<equiv> 1 < F_end \<and> F_end \<le> length DB \<and> (
    let lst = tl (take F_end DB) in 
       last lst = 0
    \<and> (\<nexists>\<sigma>. assn_consistent \<sigma> \<and> (\<forall>C\<in>set (tokenize 0 lst). \<exists>l\<in>set C. \<sigma> l)))"
  by (rule verify_unsat_spec_concise) 
                
end
