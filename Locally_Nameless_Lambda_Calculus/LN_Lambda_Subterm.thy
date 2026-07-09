theory LN_Lambda_Subterm
  imports LN_Lambda_Term
begin

inductive is_orange_subterm_of_at where
  refl: "is_orange_subterm_of_at u u []" |

  App_arg: "is_orange_subterm_of_at v t (Suc i # p)" if
    "strip_comb' t = (t', us)" and
    "t' = Const _ _ _ \<or> t' = Bound _"
    "i < length us" and
    "is_orange_subterm_of_at v (us ! i) p" |

  Lam: "is_orange_subterm_of_at v t (1 # p)" if
    "t = Abs \<tau> u" and
    "is_orange_subterm_of_at v u p"

end