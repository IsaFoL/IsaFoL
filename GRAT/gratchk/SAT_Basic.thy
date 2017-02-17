section \<open>Basics of Boolean Formulas in CNF\<close>
theory SAT_Basic
imports Main
begin
  datatype 'a literal = is_pos: Pos 'a | Neg 'a

  type_synonym 'a clause = "'a literal set"

  type_synonym 'a cnf = "'a clause set"

  type_synonym 'a valuation = "'a \<Rightarrow> bool"

  fun sem_lit :: "'a literal \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_lit (Pos x) \<sigma> = \<sigma> x"
  | "sem_lit (Neg x) \<sigma> = (\<not> \<sigma> x)"

  lemma sem_lit_alt: "sem_lit l \<sigma> = (case l of Pos x \<Rightarrow> \<sigma> x | Neg x \<Rightarrow> \<not>\<sigma> x)"
    by (auto split: literal.split)

  definition sem_clause :: "'a clause \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_clause C \<sigma> \<equiv> \<exists>l\<in>C. sem_lit l \<sigma>"

  definition sem_cnf :: "'a cnf \<Rightarrow> 'a valuation \<Rightarrow> bool" where
    "sem_cnf F \<sigma> \<equiv> \<forall>C\<in>F. sem_clause C \<sigma>"

  definition sat :: "'a cnf \<Rightarrow> bool" where
    "sat F \<equiv> \<exists>\<sigma>. sem_cnf F \<sigma>"

  definition models :: "'a cnf \<Rightarrow> 'a valuation set" where
    "models F \<equiv> {\<sigma>. sem_cnf F \<sigma>}"
    
  fun neg_lit where
    "neg_lit (Pos x) = Neg x" | "neg_lit (Neg x) = Pos x"

  lemma neg_neg_lit[simp]: "neg_lit (neg_lit l) = l" by (cases l) auto  
  lemma neg_lit_neq[simp]: 
    "neg_lit l \<noteq> l" 
    "l \<noteq> neg_lit l" 
    by (cases l; auto)+


  definition mk_lit where "mk_lit p x \<equiv> if p then Pos x else Neg x"  

  lemma is_pos_mk_lit[simp]: "is_pos (mk_lit p x) \<longleftrightarrow> p"
    unfolding mk_lit_def by auto

  lemma sem_clause_empty[simp]: "sem_clause {} \<sigma> = False"  
    unfolding sem_clause_def by auto

  lemma sem_clause_insert[simp]: "sem_clause (insert l C) \<sigma> \<longleftrightarrow> sem_lit l \<sigma> \<or> sem_clause C \<sigma>"  
    by (auto simp: sem_clause_def)

  lemma sem_clause_union[simp]: "sem_clause (C\<^sub>1\<union>C\<^sub>2) \<sigma> \<longleftrightarrow> sem_clause C\<^sub>1 \<sigma> \<or> sem_clause C\<^sub>2 \<sigma>"  
    by (auto simp: sem_clause_def)

  lemma sem_cnf_empty[simp]: "sem_cnf {} \<sigma>" by (auto simp: sem_cnf_def)
  lemma sem_cnf_insert[simp]: "sem_cnf (insert C F) \<sigma> \<longleftrightarrow> sem_clause C \<sigma> \<and> sem_cnf F \<sigma>"
    by (auto simp: sem_cnf_def)
  lemma sem_cnf_union[simp]: "sem_cnf (F\<^sub>1 \<union> F\<^sub>2) \<sigma> \<longleftrightarrow> sem_cnf F\<^sub>1 \<sigma> \<and> sem_cnf F\<^sub>2 \<sigma>"
    by (auto simp: sem_cnf_def)

  lemma sem_clauseI: "\<lbrakk>l\<in>C; sem_lit l \<sigma>\<rbrakk> \<Longrightarrow> sem_clause C \<sigma>"
    by (auto simp: sem_clause_def)

  lemma sem_cnfI: "\<lbrakk>\<And>C. C\<in>F \<Longrightarrow> sem_clause C \<sigma>\<rbrakk> \<Longrightarrow> sem_cnf F \<sigma>"    
    by (auto simp: sem_cnf_def)

  lemma sem_neg_lit[simp]: "sem_lit (neg_lit l) \<sigma> \<longleftrightarrow> \<not>sem_lit l \<sigma>"  
    by (cases l) auto

  lemma unsat_empty_clause: "{}\<in>F \<Longrightarrow> \<not>sat F"  
    unfolding sat_def sem_cnf_def
    by fastforce

  lemma sat_empty[simp, intro!]: "sat {}"  
    unfolding sat_def sem_cnf_def by auto

  lemma unsat_emptyc[simp, intro!]: "\<not>sat {{}}"
    by (simp add: unsat_empty_clause)


  subsection \<open>Used Variables\<close>
  fun var_of_lit :: "'a literal \<Rightarrow> 'a" where
    "var_of_lit (Pos x) = x" | "var_of_lit (Neg x) = x"
  lemma var_of_lit_alt: "var_of_lit l = (case l of Pos x \<Rightarrow> x | Neg x \<Rightarrow> x)"
    by (cases l) auto
  definition vars_of_clause :: "'a clause \<Rightarrow> 'a set" 
    where "vars_of_clause C = var_of_lit ` C"
  definition vars_of_cnf :: "'a cnf \<Rightarrow> 'a set" where "vars_of_cnf F \<equiv> \<Union>(vars_of_clause`F)"

  lemma vars_of_clause_simps[simp]:
    "vars_of_clause {} = {}"
    "vars_of_clause (insert l C) = insert (var_of_lit l) (vars_of_clause C)"
    "vars_of_clause (C\<^sub>1 \<union> C\<^sub>2) = vars_of_clause C\<^sub>1 \<union> vars_of_clause C\<^sub>2"
    by (auto simp: vars_of_clause_def)

  lemma vars_of_cnf_simps[simp]: 
    "vars_of_cnf {} = {}"
    "vars_of_cnf (insert C F) = vars_of_clause C \<union> vars_of_cnf F"
    "vars_of_cnf (F\<^sub>1\<union>F\<^sub>2) = vars_of_cnf F\<^sub>1 \<union> vars_of_cnf F\<^sub>2"
    by (auto simp: vars_of_cnf_def)

  lemma vars_of_clause_empty_iff[simp]: "vars_of_clause C = {} \<longleftrightarrow> C={}"  
    by (auto simp: vars_of_clause_def)

  lemma vars_of_cnf_empty_iff[simp]: "vars_of_cnf F = {} \<longleftrightarrow> (F={} \<or> F={{}})"
    by (auto simp: vars_of_cnf_def)
    
  lemma var_of_lit_neg_eq[simp]: "var_of_lit (neg_lit l) = var_of_lit l" by (cases l) auto
  

  lemma syn_indep_lit: "x\<noteq>var_of_lit l \<Longrightarrow> sem_lit l (\<sigma>(x:=v)) = sem_lit l \<sigma>"
    by (cases l) auto

  lemma syn_indep_clause: "x\<notin>vars_of_clause C \<Longrightarrow> sem_clause C (\<sigma>(x:=v)) = sem_clause C \<sigma>"
    unfolding sem_clause_def vars_of_clause_def 
    by (force simp: syn_indep_lit)

  lemma syn_indep_cnf: "x\<notin>vars_of_cnf F \<Longrightarrow> sem_cnf F (\<sigma>(x:=v)) = sem_cnf F \<sigma>"
    unfolding sem_cnf_def vars_of_cnf_def
    by (auto simp: syn_indep_clause)


  subsection \<open>Assigning Valuations\<close>  
  definition "set_lit F l \<equiv> { C - {neg_lit l} | C. C\<in>F \<and> l \<notin> C }"

  lemma sem_clause_set: "sem_clause C (\<sigma>(var_of_lit l := is_pos l)) 
    \<longleftrightarrow> l\<in>C \<or> sem_clause (C - {neg_lit l}) \<sigma>"
    unfolding sem_clause_def 
    apply (cases l)
    apply safe
    apply (auto simp: sem_lit_alt split: literal.splits if_split_asm)
    done

  lemma sem_cnf_set: "sem_cnf F (\<sigma>(var_of_lit l := is_pos l)) \<longleftrightarrow> sem_cnf (set_lit F l) \<sigma>"
    unfolding sem_cnf_def set_lit_def mk_lit_def
    by (auto simp: sem_clause_set)

  lemma upd_sigma_true[simp]: "\<sigma> x \<Longrightarrow> \<sigma>(x:=True) = \<sigma>" by (auto simp: fun_upd_def)
  lemma upd_sigma_false[simp]: "\<not>\<sigma> x \<Longrightarrow> \<sigma>(x:=False) = \<sigma>" by (auto simp: fun_upd_def)
    
  lemma set_lit_no_var: "var_of_lit l \<notin> vars_of_cnf (set_lit F l)"  
    unfolding set_lit_def vars_of_cnf_def
    by (auto simp: vars_of_clause_def var_of_lit_alt split: literal.splits)

  lemmas indep_set_lit = syn_indep_cnf[OF set_lit_no_var]

end
