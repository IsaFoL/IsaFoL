theory Ground_Order
  imports Ground_Term_Order Term_Order_Lifting
begin

locale ground_order =
  term.order: ground_term_order +
  term_order_lifting

end
