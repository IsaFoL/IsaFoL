(* Title:        Fair DISCOUNT Loop
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
*)

section \<open>Fair DISCOUNT Loop\<close>

theory Fair_DISCOUNT_Loop
  imports
    DISCOUNT_Loop
    Weighted_Path_Order.Multiset_Extension_Pair
begin

context discount_loop
begin

thm DL.intros

end

end
