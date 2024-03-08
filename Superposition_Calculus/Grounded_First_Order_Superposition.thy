theory Grounded_First_Order_Superposition
  imports First_Order_Superposition
begin

locale grounded_first_order_superposition_calculus =
  first_order_superposition_calculus +
  grounded_first_order_select
begin

sublocale ground: ground_superposition_calculus "(\<prec>\<^sub>t\<^sub>G)" select\<^sub>G
  apply(unfold_locales)
  by(auto simp: ground_critical_pair_theorem)

end

end

    