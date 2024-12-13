theory Ground_Order
  imports Ground_Term_Order Term_Order_Lifting
begin

locale ground_order =
  term.order: ground_term_order +
  term_order_lifting

(* TODO: Name *)
locale ground_order_with_equality = 
  term.order: ground_term_order 
begin

sublocale ground_order 
  where literal_to_mset = mset_lit
  by unfold_locales (rule inj_mset_lit)

end

end
