structure SAT_Solver : sig
  type nat
  datatype 'a literal = Pos of 'a | Neg of 'a
  type ('a, 'b, 'c) annotated_lit
  datatype int = Int_of_integer of IntInf.int
  type natural
  type 'a cdcl_W_restart_state_inv_from_init_state
  val nat_of_integer : IntInf.int -> nat
  val integer_of_int : int -> IntInf.int
  val natural_of_nat : nat -> natural
  val init_state_init_state_of :
    (nat literal list) list -> nat cdcl_W_restart_state_inv_from_init_state
  val do_all_cdcl_W_stgy_nat :
    nat cdcl_W_restart_state_inv_from_init_state ->
      nat cdcl_W_restart_state_inv_from_init_state
end = struct

datatype nat = Nata of IntInf.int;

fun integer_of_nat (Nata x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

fun equal_optiona A_ NONE (SOME x2) = false
  | equal_optiona A_ (SOME x2) NONE = false
  | equal_optiona A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_optiona A_ NONE NONE = true;

fun equal_option A_ = {equal = equal_optiona A_} : ('a option) equal;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype 'a literal = Pos of 'a | Neg of 'a;

fun equal_literala A_ (Pos x1) (Neg x2) = false
  | equal_literala A_ (Neg x2) (Pos x1) = false
  | equal_literala A_ (Neg x2) (Neg y2) = eq A_ x2 y2
  | equal_literala A_ (Pos x1) (Pos y1) = eq A_ x1 y1;

fun equal_literal A_ = {equal = equal_literala A_} : 'a literal equal;

datatype ('a, 'b, 'c) annotated_lit = Decided of 'a | Propagated of 'b * 'c;

fun equal_annotated_lita A_ B_ C_ (Decided x1) (Propagated (x21, x22)) = false
  | equal_annotated_lita A_ B_ C_ (Propagated (x21, x22)) (Decided x1) = false
  | equal_annotated_lita A_ B_ C_ (Propagated (x21, x22))
    (Propagated (y21, y22)) = eq B_ x21 y21 andalso eq C_ x22 y22
  | equal_annotated_lita A_ B_ C_ (Decided x1) (Decided y1) = eq A_ x1 y1;

fun equal_annotated_lit A_ B_ C_ = {equal = equal_annotated_lita A_ B_ C_} :
  ('a, 'b, 'c) annotated_lit equal;

datatype int = Int_of_integer of IntInf.int;

datatype num = One | Bit0 of num | Bit1 of num;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype 'a multiset = Mset of 'a list;

datatype natural = Nat of IntInf.int;

datatype 'a cdcl_W_restart_state_inv =
  Con of
    (('a literal, 'a literal, ('a literal list)) annotated_lit list *
      (('a literal list) list *
        (('a literal list) list * ('a literal list) option)));

datatype 'a cdcl_W_restart_state_inv_from_init_state =
  ConI of
    (('a literal, 'a literal, ('a literal list)) annotated_lit list *
      (('a literal list) list *
        (('a literal list) list * ('a literal list) option)));

fun plus_nat m n = Nata (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nata (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun find uu [] = NONE
  | find p (x :: xs) = (if p x then SOME x else find p xs);

fun null [] = true
  | null (x :: xs) = false;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun remove1 A_ x [] = []
  | remove1 A_ x (y :: xs) = (if eq A_ x y then xs else y :: remove1 A_ x xs);

fun dropWhile p [] = []
  | dropWhile p (x :: xs) = (if p x then dropWhile p xs else x :: xs);

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun is_decided (Decided x1) = true
  | is_decided (Propagated (x21, x22)) = false;

fun lit_of (Decided l) = l
  | lit_of (Propagated (l, uu)) = l;

val zero_nat : nat = Nata (0 : IntInf.int);

fun size_list x = gen_length zero_nat x;

fun atm_of (Pos x1) = x1
  | atm_of (Neg x2) = x2;

fun get_level A_ s l =
  size_list
    (filter is_decided
      (dropWhile (fn sa => not (eq A_ (atm_of (lit_of sa)) (atm_of l))) s));

fun max A_ a b = (if less_eq A_ a b then b else a);

fun count_decided l = size_list (filter is_decided l);

fun nat_of_integer k = Nata (max ord_integer (0 : IntInf.int) k);

fun is_pos (Pos x1) = true
  | is_pos (Neg x2) = false;

fun maximum_level_codea A_ [] uu = zero_nat
  | maximum_level_codea A_ (l :: ls) m =
    max ord_nat (get_level A_ m l) (maximum_level_codea A_ ls m);

fun get_maximum_level A_ m (Mset d) = maximum_level_codea A_ d m;

fun natural_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun rough_state_from_init_state_of (ConI x) = x;

fun id_of_I_to s = Con (rough_state_from_init_state_of s);

fun bt_cut i (Propagated (uu, uv) :: ls) = bt_cut i ls
  | bt_cut i (Decided k :: ls) =
    (if equal_nata (count_decided ls) i then SOME (Decided k :: ls)
      else bt_cut i ls)
  | bt_cut i [] = NONE;

fun find_level_decomp A_ m [] d k = NONE
  | find_level_decomp A_ m (l :: ls) d k =
    let
      val (i, j) = (get_level A_ m l, maximum_level_codea A_ (d @ ls) m);
    in
      (if equal_nata i k andalso less_nat j i then SOME (l, j)
        else find_level_decomp A_ m ls (l :: d) k)
    end;

fun do_backtrack_step A_ (m, (n, (u, SOME d))) =
  (case find_level_decomp A_ m d [] (count_decided m)
    of NONE => (m, (n, (u, SOME d)))
    | SOME (l, j) =>
      (case bt_cut j m of NONE => (m, (n, (u, SOME d)))
        | SOME [] => (m, (n, (u, SOME d)))
        | SOME (Decided _ :: ls) =>
          (Propagated (l, d) :: ls, (n, (d :: u, NONE)))
        | SOME (Propagated (_, _) :: _) => (m, (n, (u, SOME d)))))
  | do_backtrack_step A_ (v, (vb, (vd, NONE))) = (v, (vb, (vd, NONE)));

fun uminus_literal l = (if is_pos l then Neg else Pos) (atm_of l);

fun lits_of ls = image lit_of ls;

fun is_unit_clause_code A_ l m =
  (case filter
          (fn a => not (member A_ (atm_of a) (image atm_of (lits_of (Set m)))))
          l
    of [] => NONE
    | [a] =>
      (if list_all
            (fn c =>
              member (equal_literal A_) (uminus_literal c) (lits_of (Set m)))
            (remove1 (equal_literal A_) a l)
        then SOME a else NONE)
    | _ :: _ :: _ => NONE);

fun is_unit_clause A_ l m = is_unit_clause_code A_ l m;

fun find_first_unit_clause A_ (a :: l) m =
  (case is_unit_clause A_ a m of NONE => find_first_unit_clause A_ l m
    | SOME la => SOME (la, a))
  | find_first_unit_clause A_ [] uu = NONE;

fun do_propagate_step A_ s =
  (case s
    of (m, (n, (u, NONE))) =>
      (case find_first_unit_clause A_ (n @ u) m of NONE => (m, (n, (u, NONE)))
        | SOME (l, c) => (Propagated (l, c) :: m, (n, (u, NONE))))
    | (m, (n, (u, SOME af))) => (m, (n, (u, SOME af))));

fun find_conflict A_ m [] = NONE
  | find_conflict A_ m (n :: ns) =
    (if list_all
          (fn c =>
            member (equal_literal A_) (uminus_literal c) (lits_of (Set m)))
          n
      then SOME n else find_conflict A_ m ns);

fun do_conflict_step A_ s =
  (case s
    of (m, (n, (u, NONE))) =>
      (case find_conflict A_ m (n @ u) of NONE => (m, (n, (u, NONE)))
        | SOME a => (m, (n, (u, SOME a))))
    | (m, (n, (u, SOME af))) => (m, (n, (u, SOME af))));

fun maximum_level_code A_ d m = get_maximum_level A_ m (Mset d);

fun do_resolve_step A_ (Propagated (l, c) :: ls, (n, (u, SOME d))) =
  (if membera (equal_literal A_) d (uminus_literal l) andalso
        equal_nata
          (maximum_level_code A_
            (remove1 (equal_literal A_) (uminus_literal l) d)
            (Propagated (l, c) :: ls))
          (count_decided ls)
    then (ls, (n, (u, SOME (remdups (equal_literal A_)
                             (remove1 (equal_literal A_) l c @
                               remove1 (equal_literal A_) (uminus_literal l)
                                 d)))))
    else (Propagated (l, c) :: ls, (n, (u, SOME d))))
  | do_resolve_step A_ ([], va) = ([], va)
  | do_resolve_step A_ (Decided vd :: vc, va) = (Decided vd :: vc, va)
  | do_resolve_step A_ (v, (vb, (vd, NONE))) = (v, (vb, (vd, NONE)));

fun do_if_not_equal A_ [] s = s
  | do_if_not_equal A_ (f :: fs) s =
    let
      val t = f s;
    in
      (if not (eq A_ t s) then t else do_if_not_equal A_ fs s)
    end;

fun find_first_unused_var A_ (a :: l) m =
  (case find (fn lit =>
               not (member (equal_literal A_) lit m) andalso
                 not (member (equal_literal A_) (uminus_literal lit) m))
          a
    of NONE => find_first_unused_var A_ l m | SOME aa => SOME aa)
  | find_first_unused_var A_ [] uu = NONE;

fun do_decide_step A_ (m, (n, (u, NONE))) =
  (case find_first_unused_var A_ n (lits_of (Set m))
    of NONE => (m, (n, (u, NONE))) | SOME l => (Decided l :: m, (n, (u, NONE))))
  | do_decide_step A_ (v, (vb, (vd, SOME vf))) = (v, (vb, (vd, SOME vf)));

fun do_skip_step A_ (Propagated (l, c) :: ls, (n, (u, SOME d))) =
  (if not (membera (equal_literal A_) d (uminus_literal l)) andalso not (null d)
    then (ls, (n, (u, SOME d)))
    else (Propagated (l, c) :: ls, (n, (u, SOME d))))
  | do_skip_step A_ ([], va) = ([], va)
  | do_skip_step A_ (Decided vd :: vc, va) = (Decided vd :: vc, va)
  | do_skip_step A_ (v, (vb, (vd, NONE))) = (v, (vb, (vd, NONE)));

fun do_cdcl_step A_ s =
  do_if_not_equal
    (equal_prod
      (equal_list
        (equal_annotated_lit (equal_literal A_) (equal_literal A_)
          (equal_list (equal_literal A_))))
      (equal_prod (equal_list (equal_list (equal_literal A_)))
        (equal_prod (equal_list (equal_list (equal_literal A_)))
          (equal_option (equal_list (equal_literal A_))))))
    [do_conflict_step A_, do_propagate_step A_, do_skip_step A_,
      do_resolve_step A_, do_backtrack_step A_, do_decide_step A_]
    s;

fun integer_of_int (Int_of_integer k) = k;

fun natural_of_nat n = natural_of_integer (integer_of_nat n);

fun equal_cdcl_W_restart_state_inv_from_init_state A_ sa s =
  equal_proda
    (equal_list
      (equal_annotated_lit (equal_literal A_) (equal_literal A_)
        (equal_list (equal_literal A_))))
    (equal_prod (equal_list (equal_list (equal_literal A_)))
      (equal_prod (equal_list (equal_list (equal_literal A_)))
        (equal_option (equal_list (equal_literal A_)))))
    (rough_state_from_init_state_of sa) (rough_state_from_init_state_of s);

fun rough_state_of (Con x) = x;

fun do_cdcl_W_stgy_step A_ s = Con (do_cdcl_step A_ (rough_state_of s));

fun do_cdcl_W_stgy_stepa A_ s =
  ConI (rough_state_of (do_cdcl_W_stgy_step A_ (id_of_I_to s)));

fun do_all_cdcl_W_stgy A_ s =
  let
    val t = do_cdcl_W_stgy_stepa A_ s;
  in
    (if equal_cdcl_W_restart_state_inv_from_init_state A_ t s then s
      else do_all_cdcl_W_stgy A_ t)
  end;

fun init_state_init_state_of n =
  ConI ([], (map (remdups (equal_literal equal_nat)) n, ([], NONE)));

fun do_all_cdcl_W_stgy_nat x = do_all_cdcl_W_stgy equal_nat x;

end; (*struct SAT_Solver*)
