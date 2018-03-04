theory Cert_Sat
imports Sat_Check Unsat_Check
begin

  definition "certified_sat oracle a \<equiv> do {
    l \<leftarrow> Array.len a;
    b \<leftarrow> array_copy a;

    (res,b) \<leftarrow> oracle b;
    bl \<leftarrow> Array.len b;

    if bl<l then
      return (Inl (STR ''Oracle shrinked array'',None,None))
    else do {
      blit a 0 b 0 l;
  
      if res then do {
        r \<leftarrow> verify_sat_impl_wrapper b l;
        case r of Inl x \<Rightarrow> return (Inl x) | Inr _ \<Rightarrow> return (Inr True)
      } else do {
        r \<leftarrow> verify_unsat_impl_wrapper b l bl;
        case r of Inl x \<Rightarrow> return (Inl x) | Inr _ \<Rightarrow> return (Inr False)
      }
    }
  }"
  
  lemma tl_lst_nn_eq: "tl lst \<noteq> [] \<longleftrightarrow> length lst > 1" by (cases lst) auto  

  text \<open>
    Note that we have to assume that the oracle actually returns some array.
    This assumption, however, is not too bad: The oracle can only violate it by
    throwing an exception (which will go through uncaught). 
  \<close>
  theorem certified_sat_correct[sep_heap_rules]:
    assumes [sep_heap_rules]: "\<And>b lst lst'. <b \<mapsto>\<^sub>a lst> oracle b <\<lambda>(r,b'). b' \<mapsto>\<^sub>a lst'>\<^sub>t"
    shows "< a \<mapsto>\<^sub>a lst > certified_sat oracle a <\<lambda>r. a \<mapsto>\<^sub>a lst * \<up>(
      case r of 
        Inl _ \<Rightarrow> True
      | Inr r \<Rightarrow> lst\<noteq>[] \<and> F_invar (tl lst) \<and> (r \<longleftrightarrow> sat (F_\<alpha> (tl lst)))
    ) >\<^sub>t"
    unfolding certified_sat_def
    by (sep_auto 
        simp: verify_sat_spec_def verify_unsat_spec_def clause_DB_valid_def clause_DB_sat_def
        )
      
      
      
      
end
