theory PAC_Polynoms_Term
  imports PAC_Polynoms_List
    Refine_Imperative_HOL.IICF
begin

type_synonym term_poly_list = \<open>string list\<close>
type_synonym llist_polynom = \<open>(term_poly_list \<times> int) list\<close>


text \<open>We instantiate the characters with typeclass linorder to be able to talk abourt sorted and
  so on.\<close>

definition less_than_char :: \<open>(char \<times> char) set\<close> where
  \<open>less_than_char = {(a, b). of_char a < (of_char b :: nat) } \<close>

definition term_poly_list_rel :: \<open>(term_poly_list \<times> term_poly) set\<close> where
  \<open>term_poly_list_rel = {(xs, ys).
     ys = mset xs \<and>
     sorted_wrt (rel2p (lexord less_than_char)) xs}\<close>

definition poly_list_rel :: \<open>_ \<Rightarrow> (_ \<times> mset_polynom) set\<close> where
  \<open>poly_list_rel R = {(xs, ys).
     (xs, ys) \<in> \<langle>R\<rangle>list_rel O list_mset_rel}\<close>

definition sorted_poly_list_rel_wrt :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool)
     \<Rightarrow> ('a \<times> string multiset) set \<Rightarrow> (('a \<times> int) list \<times> list_polynom) set\<close> where
  \<open>sorted_poly_list_rel_wrt S R = {(xs, ys).
     (xs, ys) \<in> \<langle>R \<times>\<^sub>r int_rel\<rangle>list_rel \<and>
     sorted_wrt S (map fst xs)}\<close>

abbreviation sorted_poly_list_rel where
  \<open>sorted_poly_list_rel R \<equiv> sorted_poly_list_rel_wrt R term_poly_list_rel\<close>


fun add_poly_l :: \<open>llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> llist_polynom\<close> where
  \<open>add_poly_l [] p = p\<close> |
  \<open>add_poly_l p [] = p\<close> |
  \<open>add_poly_l ((xs, n) # p) ((ys, m) # q) =
    (if xs = ys then if n + m = 0 then add_poly_l p q else (xs, n + m) # add_poly_l p q
    else if (xs, ys) \<in> lexord (lexord less_than_char) then (xs, n) # add_poly_l p ((ys, m) # q)
    else (ys, m) # add_poly_l ((xs, n) # p) q)\<close>


lemma
  \<open>(add_poly_l, add_poly (\<lambda>_ _. True)) \<in> sorted_poly_list_rel S \<rightarrow> sorted_poly_list_rel S \<rightarrow> sorted_poly_list_rel S\<close>
  apply (intro fun_relI)

instantiation char :: linorder
begin
  definition less_eq_char :: \<open>char \<Rightarrow> char \<Rightarrow> bool\<close> where
    \<open>less_eq_char c d = (((of_char c) :: nat) \<le> of_char d)\<close>

  definition less_char :: \<open>char \<Rightarrow> char \<Rightarrow> bool\<close> where
    \<open>less_char c d = (((of_char c) :: nat) < of_char d)\<close>

instance
  using linorder_char
  unfolding linorder_class_def class.linorder_def
    less_eq_char_def[symmetric] less_char_def[symmetric]
    class.order_def order_class_def
    class.preorder_def preorder_class_def
    ord_class_def
  apply auto
  apply standard
  done
end

end