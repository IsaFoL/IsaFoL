theory LN_HO_Term
  imports
    Main
    "HOL-Library.Uprod"
    "HOL-Library.Multiset"
    "First_Order_Terms.Term"
    "HOL-ex.Sketch_and_Explore"
begin

declare foldl_inject[simp]

datatype (* (plugins del: size) *) (funs_term: 'f, vars_term: 'v) "term" =
  is_Const: Const 'f |
  is_Free: Free 'v |
  is_Bound: Bound nat |
  is_App: App "('f, 'v) term" "('f, 'v) term" |
  is_Abs: Abs "('f, 'v) term"

(* instantiation "term" :: (type, type) size
begin
  primrec size_term :: "('f, 'v) term \<Rightarrow> nat" where
    "size_term (Const _) = 1" |
    "size_term (Free _) = 1" |
    "size_term (Bound _) = 1" |
    "size_term (App t\<^sub>1 t\<^sub>2) = size_term t\<^sub>1 + size_term t\<^sub>2" |
    "size_term (Abs t) = 1 + size_term t"

  instance ..
end *)

primrec head where
  "head (Const f) = Const f" |
  "head (Free x) = Free x" |
  "head (Bound n) = Bound n" |
  "head (App t\<^sub>1 t\<^sub>2) = head t\<^sub>1" |
  "head (Abs t) = head t"

primrec subterms where
  "subterms (Const f) = {#Const f#}" |
  "subterms (Free x) = {#Free x#}" |
  "subterms (Bound n) = {#Bound n#}" |
  "subterms (App t\<^sub>1 t\<^sub>2) = add_mset (App t\<^sub>1 t\<^sub>2) (subterms t\<^sub>1 + subterms t\<^sub>2)" |
  "subterms (Abs t) = add_mset (Abs t) (subterms t)"

primrec shift_bound :: "nat \<Rightarrow> ('c, 'f) term \<Rightarrow> ('c, 'f) term" where
  "shift_bound n (Const c) = Const c" |
  "shift_bound n (Free f) = Free f" |
  "shift_bound n (Bound k) = Bound (if k < n then k else Suc k)" |
  "shift_bound n (App t\<^sub>1 t\<^sub>2) = App (shift_bound n t\<^sub>1) (shift_bound n t\<^sub>2)" |
  "shift_bound n (Abs t) = Abs (shift_bound (Suc n) t)"

primrec subst_bound :: "nat \<Rightarrow> ('c, 'f) term \<Rightarrow> ('c, 'f) term \<Rightarrow> ('c, 'f) term" where
  "subst_bound n t (Const c) = Const c"|
  "subst_bound n t (Free f) = Free f" |
  "subst_bound n t (Bound k) = (if k = n then t else Bound k)" |
  "subst_bound n t (App t\<^sub>1 t\<^sub>2) = App (subst_bound n t t\<^sub>1) (subst_bound n t t\<^sub>2)" |
  "subst_bound n t (Abs t\<^sub>1) = Abs (subst_bound (Suc n) (shift_bound 0 t) t\<^sub>1)"

fun beta_reduce where
  "beta_reduce (App (Abs t\<^sub>1) t\<^sub>2) = subst_bound 0 t\<^sub>2 t\<^sub>1" |
  "beta_reduce (App t\<^sub>1 t\<^sub>2) = (App (beta_reduce t\<^sub>1) t\<^sub>2)" |
  "beta_reduce t = t"

primrec is_hnf_App where                                  
  "is_hnf_App (Const _) \<longleftrightarrow> True" |
  "is_hnf_App (Free _) \<longleftrightarrow> True" |
  "is_hnf_App (Bound _) \<longleftrightarrow> True" |
  "is_hnf_App (App t _) \<longleftrightarrow> is_hnf_App t" |
  "is_hnf_App (Abs t) \<longleftrightarrow> False"

primrec is_hnf where                                  
  "is_hnf (Const _) \<longleftrightarrow> True" |
  "is_hnf (Free _) \<longleftrightarrow> True" |
  "is_hnf (Bound _) \<longleftrightarrow> True" |
  "is_hnf (App t _) \<longleftrightarrow> is_hnf_App t" |
  "is_hnf (Abs t) \<longleftrightarrow> is_hnf t"

experiment begin

lemma "is_hnf (App (Const c\<^sub>1) (Const c\<^sub>2))"
  by simp

end
 
lemma "is_hnf t \<Longrightarrow> beta_reduce t = t"
proof (induction t)
  case (App t1 t2)
  then show ?case
    by (smt (verit, best) beta_reduce.simps(2,3,4,5,6,7,8)
        is_hnf.simps(4) is_hnf_App.simps(4,5) term.rel_cases
        term.rel_eq)
qed simp_all

end