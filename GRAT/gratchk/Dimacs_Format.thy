theory Dimacs_Format
imports SAT_Basic Tokenization
begin

    
section \<open>Parsing to Formulas\<close>
  text \<open>
    A formula is represented according to DIMACS, the de facto standard for 
    encoding CNF formulas: Variables are identified by positive integers. 
    Negative integers encode negated variables. A clause is a 
    null-terminated string of integers, and the formula is simply the 
    concatenation of its clauses.
  \<close>  
  type_synonym var = nat  
    
  abbreviation (input) litZ :: int where "litZ \<equiv> 0"
    
  text \<open>Interpreting an integer as literal\<close>        
  definition lit_invar :: "int \<Rightarrow> bool" 
    where "lit_invar l \<equiv> l\<noteq>0"
  definition lit_\<alpha> :: "int \<Rightarrow> nat literal" 
    where "lit_\<alpha> l \<equiv> if l<0 then Neg (nat (-l)) else Pos (nat l)"

  text \<open>Interpreting a list of integers (without terminating zero) as clause\<close>        
  definition "clause_invar l \<equiv> \<forall>x\<in>set l. lit_invar x"
  definition "clause_\<alpha> l \<equiv> lit_\<alpha>`set l"

  text \<open>Interpreting a list of integers as formula\<close>
  definition "F_invar lst \<equiv> lst\<noteq>[] \<longrightarrow> last lst = litZ"
  definition "F_\<alpha> lst \<equiv> set (map clause_\<alpha> (tokenize litZ lst))"

  lemma F_invar_imp_clause_invar: 
    "F_invar lst \<Longrightarrow> \<forall>c\<in>set (tokenize litZ lst). clause_invar c"
    unfolding clause_invar_def lit_invar_def F_invar_def
    using tokenize_complete[of lst litZ]
    by auto
    
  lemma clause_\<alpha>_empty[simp]: "clause_\<alpha> [] = {}" 
    unfolding clause_\<alpha>_def by auto
  lemma clause_\<alpha>_cons[simp]: "clause_\<alpha> (x#l) = insert (lit_\<alpha> x) (clause_\<alpha> l)" 
    unfolding clause_\<alpha>_def by auto
  lemma clause_\<alpha>_conc[simp]: "clause_\<alpha> (l1@l2) = clause_\<alpha> l1 \<union> clause_\<alpha> l2" 
    unfolding clause_\<alpha>_def by auto
  
  lemma F_\<alpha>_empty[simp]: "F_\<alpha> [] = {}" unfolding F_\<alpha>_def by auto

  lemma var_of_lit_\<alpha>_Z_iff[simp]: "var_of_lit (lit_\<alpha> x) = 0 \<longleftrightarrow> x=0"  
    unfolding var_of_lit_alt lit_\<alpha>_def by auto
  
      
subsection \<open>Pretty-Printing Literals\<close>
  definition "lit_\<gamma> l \<equiv> case l of Pos l \<Rightarrow> int l | Neg l \<Rightarrow> - int l"
  
  lemma lit_\<gamma>_\<alpha>_inv[simp]: "lit_\<gamma> (lit_\<alpha> i) = i"
    unfolding lit_\<gamma>_def lit_\<alpha>_def by auto
  
  lemma lit_\<alpha>_\<gamma>_inv[simp]: "lit_invar (lit_\<gamma> l) \<Longrightarrow> lit_\<alpha> (lit_\<gamma> l) = l"
    unfolding lit_\<gamma>_def lit_\<alpha>_def lit_invar_def 
    by (cases l) auto
  
  lemma map_lit_\<gamma>_\<alpha>_eq[simp]: "0\<notin>set l \<Longrightarrow> map (lit_\<gamma> \<circ> lit_\<alpha>) l = l"
    by (induction l) auto
  
  lemma map_map_lit_\<gamma>_\<alpha>_eq[simp]: 
    "0 \<notin> \<Union>(set (map set l)) \<Longrightarrow> map (map (lit_\<gamma> \<circ> lit_\<alpha>)) l = l"
    by (induction l) auto  
      
  lemma lit_invar_\<gamma>_iff[simp]: "lit_invar (lit_\<gamma> l) \<longleftrightarrow> var_of_lit l \<noteq> 0"
    by (cases l) (auto simp: lit_invar_def lit_\<gamma>_def)
    
  
    
    
section \<open>Direct Representation of Satisfiable Formulas\<close>
  text \<open>
    Instead of parsing a DIMACS formatted list to a formula, and then 
    stating that the formula is satisfiable, there is a more direct 
    equivalent characterization of satisfiability: 
    The formula is tokenized to a set of sets of integers, and 
    we have to find an assignment from integers to Booleans that is consistent,
    i.e., a negative integer is assigned the negation of what is assigned 
    to the positive integer, such that each clause contains at least one integer
    assigned to true.
    
    This gives a concise semantic reference point within a few lines of code.
  \<close>


  definition direct_invar :: "int list \<Rightarrow> bool"
    where "direct_invar lst \<equiv> lst\<noteq>[] \<longrightarrow> last lst = 0"  
  definition parse_direct :: "int list \<Rightarrow> int set set"
    where "parse_direct lst \<equiv> set ` set (tokenize 0 lst)"  
  
  definition assn_consistent :: "(int \<Rightarrow> bool) \<Rightarrow> bool"
    where "assn_consistent \<sigma> \<longleftrightarrow> (\<forall>l. l\<noteq>0 \<longrightarrow> \<sigma> l = (\<not> \<sigma> (-l)))"  
  definition direct_sat :: "int set set \<Rightarrow> bool"
    where "direct_sat F \<equiv> \<exists>\<sigma>. assn_consistent \<sigma> \<and> (\<forall>C\<in>F. \<exists>l\<in>C. \<sigma> l)"
  
  definition "direct_valid_sat l \<equiv> direct_invar l \<and> direct_sat (parse_direct l)"
  definition "direct_valid_unsat l \<equiv> direct_invar l \<and> \<not>direct_sat (parse_direct l)"
  
  
  text \<open>We show equivalence to the standard semantics\<close>
  
  theorem direct_invar_eq: "direct_invar l = F_invar l"
    unfolding direct_invar_def F_invar_def by simp
  
  lemma ex_assn_consistent[intro,simp]: "\<not>(\<forall>x. \<not>assn_consistent x)"  
    apply (clarsimp)
    apply (rule exI[where x="(<) 0"])
    by (auto simp: assn_consistent_def)
    
  theorem direct_sat_iff_sat:
    (*assumes "direct_invar l"  *)
    shows "direct_sat (parse_direct l) \<longleftrightarrow> sat (F_\<alpha> l)"
  proof -
    have F_\<alpha>_alt: "F_\<alpha> l = (\<lambda>x. lit_\<alpha>`x)`set`set (tokenize 0 l)"
      unfolding F_\<alpha>_def clause_\<alpha>_def
      by auto
  
    have X1: "\<exists>\<sigma>. \<forall>l. l \<noteq> (0::int) \<longrightarrow> \<sigma> l = (\<not> \<sigma> (- l))"
      by (rule exI[where x="(<) 0"]) auto
    
    show ?thesis
    proof
      assume "direct_sat (parse_direct l)"
      then obtain \<sigma> where CONS: "assn_consistent \<sigma>" and SAT: "\<forall>C\<in>set`set (tokenize 0 l). \<exists>x\<in>C. \<sigma> x"
        unfolding direct_sat_def parse_direct_def by blast
      
      from CONS have X2: "\<sigma> (-x) \<longleftrightarrow> \<not>(\<sigma> x)" if "x\<noteq>0" for x
        unfolding assn_consistent_def using that
        apply (cases "x=0")
        apply simp
        apply blast
        done
        
      let ?\<sigma>' = "\<sigma> o int"
        
      have "sem_cnf (F_\<alpha> l) ?\<sigma>'"
        unfolding sem_cnf_def F_\<alpha>_def clause_\<alpha>_def
      proof   
        fix C
        assume "C \<in> set (map (\<lambda>l. lit_\<alpha> ` set l) (tokenize 0 l))"
        then obtain C' where "C' \<in> set`set (tokenize 0 l)" and [simp]: "C = lit_\<alpha> ` C'"
          by auto
        with SAT obtain x where "x\<in>C'" "\<sigma> x" by auto
        then show "sem_clause C (\<sigma> \<circ> int)"
          unfolding sem_clause_def sem_lit_alt
          by simp (auto simp: X2 lit_\<alpha>_def intro: bexI[where x=x])
          
      qed 
      then show "sat (F_\<alpha> l)"
        unfolding sat_def by blast
    next
      assume "sat (F_\<alpha> l)"
      then obtain \<sigma> where SAT: "sem_cnf (F_\<alpha> l) \<sigma>" unfolding sat_def by auto

      let ?\<sigma>' = "\<lambda>i. if i<0 then \<not>\<sigma> (nat (-i)) else \<sigma> (nat i)"
      
      have "assn_consistent ?\<sigma>'"
        unfolding assn_consistent_def by auto
      moreover have "\<exists>l\<in>C. ?\<sigma>' l" if "C\<in>set ` set (tokenize 0 l)" for C
        using SAT that 
        unfolding sem_cnf_def F_\<alpha>_alt sem_clause_def clause_\<alpha>_def sem_lit_alt lit_\<alpha>_def
        by (fastforce split: literal.splits)
      ultimately show "direct_sat (parse_direct l)"
        unfolding direct_sat_def parse_direct_def by auto
    qed
  qed

  
  
  

end
