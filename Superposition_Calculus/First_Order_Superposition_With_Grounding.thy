theory First_Order_Superposition_With_Grounding
  imports First_Order_Superposition
begin

locale first_order_superposition_calculus_with_grounding =
  first_order_superposition_calculus +
  first_order_select_with_grounding
begin

sublocale ground: ground_superposition_calculus "(\<prec>\<^sub>t\<^sub>G)" select\<^sub>G
  apply(unfold_locales)
  by(auto simp: select\<^sub>G_subset select\<^sub>G_negative ground_critical_pair_theorem)

end

end

    