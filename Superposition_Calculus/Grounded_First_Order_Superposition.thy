theory Grounded_First_Order_Superposition
  imports First_Order_Superposition
begin

locale grounded_first_order_superposition_calculus =
  first_order_superposition_calculus +
  grounded_first_order_select
begin

sublocale ground: ground_superposition_calculus "(\<prec>\<^sub>t\<^sub>G)" select\<^sub>G
  by unfold_locales (rule ground_critical_pair_theorem)

definition inference_groundings
  where "inference_groundings inference = 
  { ground_inference | ground_inference \<theta> \<rho>\<^sub>1 \<rho>\<^sub>2.
    (case inference of 
        Infer [premise] conclusion \<Rightarrow>
          is_ground_clause (premise \<cdot> \<theta>) 
        \<and> is_ground_clause (conclusion \<cdot> \<theta>)
        \<and> ground_inference = 
            Infer [to_ground_clause (premise \<cdot> \<theta>)] (to_ground_clause (conclusion \<cdot> \<theta>))
      | Infer [premise\<^sub>1, premise\<^sub>2] conclusion \<Rightarrow> 
          term_subst.is_renaming \<rho>\<^sub>1
        \<and> term_subst.is_renaming \<rho>\<^sub>2
        \<and> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}
        \<and> is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>) 
        \<and> is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>) 
        \<and> is_ground_clause (conclusion \<cdot> \<theta>)
        \<and> ground_inference = 
            Infer 
              [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)] 
              (to_ground_clause (conclusion \<cdot> \<theta>))
      | _ \<Rightarrow> False
     )
  \<and> ground_inference \<in> ground.G_Inf
}"

end

end

    