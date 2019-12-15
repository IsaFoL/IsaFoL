(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val set_bit : Word32.word -> IntInf.int -> bool -> Word32.word
  val shiftl : Word32.word -> IntInf.int -> Word32.word
  val shiftr : Word32.word -> IntInf.int -> Word32.word
  val shiftr_signed : Word32.word -> IntInf.int -> Word32.word
  val test_bit : Word32.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word32.orb (x, mask)
     else Word32.andb (x, Word32.notb mask)
  end

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)


   fun array_blit src si dst di len = (
      src=dst andalso raise Fail ("array_blit: Same arrays");
      ArraySlice.copy {
        di = IntInf.toInt di,
        src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
        dst = dst})

    fun array_nth_oo v a i () = Array.sub(a,IntInf.toInt i) handle Subscript => v | Overflow => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,IntInf.toInt i,x); a) handle Subscript => f () | Overflow => f ()



structure Bits_Integer : sig
  val set_bit : IntInf.int -> IntInf.int -> bool -> IntInf.int
  val shiftl : IntInf.int -> IntInf.int -> IntInf.int
  val shiftr : IntInf.int -> IntInf.int -> IntInf.int
  val test_bit : IntInf.int -> IntInf.int -> bool
end = struct

val maxWord = IntInf.pow (2, Word.wordSize);

fun set_bit x n b =
  if n < maxWord then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

end; (*struct Bits_Integer*)

structure PAC_Checker : sig
  datatype int = Int_of_integer of IntInf.int
  type nat
  val nat_of_integer : IntInf.int -> nat
  type char
  type ('a, 'b) hashtable
  datatype 'a code_status = CFAILED of 'a | CSUCCESS | CFOUND
  datatype 'a pac_step = Add of nat * nat * nat * 'a |
    Mult of nat * 'a * nat * 'a | Extension of nat * 'a | Del of nat
  val implode : char list -> string
  val is_cfound : 'a code_status -> bool
  val the_error : 'a code_status -> 'a
  val is_cfailed : 'a code_status -> bool
  val pAC_empty_impl : (unit -> ((((string list * int) list) option) array))
  val pAC_update_impl :
    nat ->
      (string list * int) list ->
        (((string list * int) list) option) array ->
          (unit -> ((((string list * int) list) option) array))
  val fully_normalize_poly_impl :
    (string list * int) list -> (unit -> ((string list * int) list))
  val check_step_impl :
    (string list * int) list ->
      (char list) code_status ->
        (string, unit) hashtable ->
          (nat, ((string list * int) list)) hashtable ->
            ((string list * int) list) pac_step ->
              (unit ->
                ((char list) code_status *
                  ((string, unit) hashtable *
                    (nat, ((string list * int) list)) hashtable)))
  val empty_vars_impl : (unit -> (string, unit) hashtable)
  val pAC_checker_l_impl :
    (string list * int) list ->
      (string, unit) hashtable ->
        (nat, ((string list * int) list)) hashtable ->
          (char list) code_status ->
            ((string list * int) list) pac_step list ->
              (unit ->
                ((char list) code_status *
                  ((string, unit) hashtable *
                    (nat, ((string list * int) list)) hashtable)))
  val union_vars_poly_impl :
    (string list * int) list ->
      (string, unit) hashtable -> (unit -> (string, unit) hashtable)
  val remap_polys_l_impl :
    (string list * int) list ->
      (string, unit) hashtable ->
        (((string list * int) list) option) array ->
          (unit ->
            ((char list) code_status *
              ((string, unit) hashtable *
                (nat, ((string list * int) list)) hashtable)))
  val full_checker_l_impl :
    (string list * int) list ->
      (((string list * int) list) option) array ->
        ((string list * int) list) pac_step list ->
          (unit ->
            ((char list) code_status *
              ((string, unit) hashtable *
                (nat, ((string list * int) list)) hashtable)))
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

datatype typerepa = Typerep of string * typerepa list;

datatype 'a itself = Type;

fun typerep_inta t = Typerep ("Int.int", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_int = {} : int countable;

val typerep_int = {typerep = typerep_inta} : int typerep;

val heap_int = {countable_heap = countable_int, typerep_heap = typerep_int} :
  int heap;

fun uminus_int k = Int_of_integer (IntInf.~ (integer_of_int k));

val zero_int : int = Int_of_integer (0 : IntInf.int);

fun apsnd f (x, y) = (x, f y);

datatype num = One | Bit0 of num | Bit1 of num;

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

val zero_nat : nat = Nat (0 : IntInf.int);

val one_nat : nat = Nat (1 : IntInf.int);

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun string_of_digit n =
  (if equal_nata n zero_nat
    then [Chara (false, false, false, false, true, true, false, false)]
    else (if equal_nata n one_nat
           then [Chara (true, false, false, false, true, true, false, false)]
           else (if equal_nata n (nat_of_integer (2 : IntInf.int))
                  then [Chara (false, true, false, false, true, true, false,
                                false)]
                  else (if equal_nata n (nat_of_integer (3 : IntInf.int))
                         then [Chara (true, true, false, false, true, true,
                                       false, false)]
                         else (if equal_nata n (nat_of_integer (4 : IntInf.int))
                                then [Chara
(false, false, true, false, true, true, false, false)]
                                else (if equal_nata n
   (nat_of_integer (5 : IntInf.int))
                                       then [Chara
       (true, false, true, false, true, true, false, false)]
                                       else (if equal_nata n
          (nat_of_integer (6 : IntInf.int))
      then [Chara (false, true, true, false, true, true, false, false)]
      else (if equal_nata n (nat_of_integer (7 : IntInf.int))
             then [Chara (true, true, true, false, true, true, false, false)]
             else (if equal_nata n (nat_of_integer (8 : IntInf.int))
                    then [Chara (false, false, false, true, true, true, false,
                                  false)]
                    else [Chara (true, false, false, true, true, true, false,
                                  false)])))))))));

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun shows_string x = (fn a => x @ a);

fun showsp_nat p n =
  (if less_nat n (nat_of_integer (10 : IntInf.int))
    then shows_string (string_of_digit n)
    else showsp_nat p (divide_nat n (nat_of_integer (10 : IntInf.int))) o
           shows_string
             (string_of_digit
               (modulo_nat n (nat_of_integer (10 : IntInf.int)))));

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun nat k = Nat (max ord_integer (0 : IntInf.int) (integer_of_int k));

fun showsp_int p i =
  (if less_int i zero_int
    then shows_string
           [Chara (true, false, true, true, false, true, false, false)] o
           showsp_nat p (nat (uminus_int i))
    else showsp_nat p (nat i));

fun shows_prec_int x = showsp_int x;

fun shows_sep s sep [] = shows_string []
  | shows_sep s sep [x] = s x
  | shows_sep s sep (x :: v :: va) = s x o sep o shows_sep s sep (v :: va);

fun null [] = true
  | null (x :: xs) = false;

fun shows_list_gen showsx e l s r xs =
  (if null xs then shows_string e
    else shows_string l o shows_sep showsx (shows_string s) xs o
           shows_string r);

fun showsp_list s p xs =
  shows_list_gen (s zero_nat)
    [Chara (true, true, false, true, true, false, true, false),
      Chara (true, false, true, true, true, false, true, false)]
    [Chara (true, true, false, true, true, false, true, false)]
    [Chara (false, false, true, true, false, true, false, false),
      Chara (false, false, false, false, false, true, false, false)]
    [Chara (true, false, true, true, true, false, true, false)] xs;

fun shows_list_int x = showsp_list shows_prec_int zero_nat x;

type 'a show =
  {shows_prec : nat -> 'a -> char list -> char list,
    shows_list : 'a list -> char list -> char list};
val shows_prec = #shows_prec : 'a show -> nat -> 'a -> char list -> char list;
val shows_list = #shows_list : 'a show -> 'a list -> char list -> char list;

val show_int = {shows_prec = shows_prec_int, shows_list = shows_list_int} :
  int show;

val equal_nat = {equal = equal_nata} : nat equal;

fun typerep_nata t = Typerep ("Nat.nat", []);

val countable_nat = {} : nat countable;

val typerep_nat = {typerep = typerep_nata} : nat typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  nat heap;

fun shows_prec_nat x = showsp_nat x;

fun shows_list_nat x = showsp_list shows_prec_nat zero_nat x;

val show_nat = {shows_prec = shows_prec_nat, shows_list = shows_list_nat} :
  nat show;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

fun def_hashmap_size_nat x = (fn _ => nat_of_integer (16 : IntInf.int)) x;

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a itself -> nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size : 'a hashable -> 'a itself -> nat;

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun uint32_of_int i = Word32.fromLargeInt (IntInf.toLarge (integer_of_int i));

fun hashcode_nat n = uint32_of_int (int_of_nat n);

val hashable_nat =
  {hashcode = hashcode_nat, def_hashmap_size = def_hashmap_size_nat} :
  nat hashable;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

fun typerep_lista A_ t = Typerep ("List.list", [typerep A_ Type]);

fun countable_list A_ = {} : ('a list) countable;

fun typerep_list A_ = {typerep = typerep_lista A_} : ('a list) typerep;

fun heap_list A_ =
  {countable_heap = countable_list (countable_heap A_),
    typerep_heap = typerep_list (typerep_heap A_)}
  : ('a list) heap;

fun shows_prec_list A_ p xs = shows_list A_ xs;

fun shows_list_list A_ xss = showsp_list (shows_prec_list A_) zero_nat xss;

fun show_list A_ =
  {shows_prec = shows_prec_list A_, shows_list = shows_list_list A_} :
  ('a list) show;

fun def_hashmap_size_char x = (fn _ => nat_of_integer (32 : IntInf.int)) x;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

fun of_bool A_ true = one (one_zero_neq_one A_)
  | of_bool A_ false = zero (zero_zero_neq_one A_);

val one_integera : IntInf.int = (1 : IntInf.int);

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

val one_integer = {one = one_integera} : IntInf.int one;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (of_bool
                        zero_neq_one_integer
                        b7, (2 : IntInf.int)), of_bool zero_neq_one_integer
         b6), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                   b5), (2 : IntInf.int)), of_bool
                     zero_neq_one_integer
                     b4), (2 : IntInf.int)), of_bool zero_neq_one_integer
       b3), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                 b2), (2 : IntInf.int)), of_bool
                   zero_neq_one_integer
                   b1), (2 : IntInf.int)), of_bool zero_neq_one_integer b0);

fun int_of_char x = (Int_of_integer o integer_of_char) x;

fun hashcode_char c = uint32_of_int (int_of_char c);

val hashable_char =
  {hashcode = hashcode_char, def_hashmap_size = def_hashmap_size_char} :
  char hashable;

fun typerep_optiona A_ t = Typerep ("Option.option", [typerep A_ Type]);

fun countable_option A_ = {} : ('a option) countable;

fun typerep_option A_ = {typerep = typerep_optiona A_} : ('a option) typerep;

fun heap_option A_ =
  {countable_heap = countable_option (countable_heap A_),
    typerep_heap = typerep_option (typerep_heap A_)}
  : ('a option) heap;

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string equal;

fun typerep_literala t = Typerep ("String.literal", []);

val countable_literal = {} : string countable;

val typerep_literal = {typerep = typerep_literala} : string typerep;

val heap_literal =
  {countable_heap = countable_literal, typerep_heap = typerep_literal} :
  string heap;

fun bit_cut_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), false)
    else let
           val (r, s) =
             IntInf.divMod (IntInf.abs k, IntInf.abs (2 : IntInf.int));
         in
           ((if IntInf.< ((0 : IntInf.int), k) then r
              else IntInf.- (IntInf.~ r, s)),
             ((s : IntInf.int) = (1 : IntInf.int)))
         end);

fun char_of_integer k = let
                          val (q0, b0) = bit_cut_integer k;
                          val (q1, b1) = bit_cut_integer q0;
                          val (q2, b2) = bit_cut_integer q1;
                          val (q3, b3) = bit_cut_integer q2;
                          val (q4, b4) = bit_cut_integer q3;
                          val (q5, b5) = bit_cut_integer q4;
                          val (q6, b6) = bit_cut_integer q5;
                          val a = bit_cut_integer q6;
                          val (_, aa) = a;
                        in
                          Chara (b0, b1, b2, b3, b4, b5, b6, aa)
                        end;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun explode s =
  map char_of_integer
    ((List.map (fn c => let val k = Char.ord c in if k < 128 then IntInf.fromInt k else raise Fail "Non-ASCII character in literal" end) 
       o String.explode)
      s);

fun shows_prec_literal p s = shows_string (explode s);

fun id x = (fn xa => xa) x;

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun shows_list_literal x = foldr (fn s => shows_string (explode s)) x;

val show_literal =
  {shows_prec = shows_prec_literal, shows_list = shows_list_literal} :
  string show;

val ord_literal =
  {less_eq = (fn a => fn b => ((a : string) <= b)),
    less = (fn a => fn b => ((a : string) < b))}
  : string ord;

fun def_hashmap_size_literal uu = nat_of_integer (10 : IntInf.int);

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun hashcode_list A_ =
  foldl (fn h => fn x =>
          Word32.+ (Word32.* (h, Word32.fromLargeInt (IntInf.toLarge (33 : IntInf.int))), hashcode
            A_ x))
    (Word32.fromLargeInt (IntInf.toLarge (5381 : IntInf.int)));

fun hashcode_literal s = hashcode_list hashable_char (explode s);

val hashable_literal =
  {hashcode = hashcode_literal, def_hashmap_size = def_hashmap_size_literal} :
  string hashable;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun typerep_proda A_ B_ t =
  Typerep ("Product_Type.prod", [typerep A_ Type, typerep B_ Type]);

fun countable_prod A_ B_ = {} : ('a * 'b) countable;

fun typerep_prod A_ B_ = {typerep = typerep_proda A_ B_} : ('a * 'b) typerep;

fun heap_prod A_ B_ =
  {countable_heap = countable_prod (countable_heap A_) (countable_heap B_),
    typerep_heap = typerep_prod (typerep_heap A_) (typerep_heap B_)}
  : ('a * 'b) heap;

fun showsp_prod s1 s2 p (x, y) =
  shows_string [Chara (false, false, false, true, false, true, false, false)] o
    s1 one_nat x o
    shows_string
      [Chara (false, false, true, true, false, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] o
    s2 one_nat y o
    shows_string [Chara (true, false, false, true, false, true, false, false)];

fun shows_prec_prod A_ B_ = showsp_prod (shows_prec A_) (shows_prec B_);

fun shows_list_prod A_ B_ = showsp_list (shows_prec_prod A_ B_) zero_nat;

fun show_prod A_ B_ =
  {shows_prec = shows_prec_prod A_ B_, shows_list = shows_list_prod A_ B_} :
  ('a * 'b) show;

fun typerep_unita t = Typerep ("Product_Type.unit", []);

val countable_unit = {} : unit countable;

val typerep_unit = {typerep = typerep_unita} : unit typerep;

val heap_unit = {countable_heap = countable_unit, typerep_heap = typerep_unit} :
  unit heap;

datatype ('a, 'b) hashtable = HashTable of (('a * 'b) list) array * nat;

datatype 'a code_status = CFAILED of 'a | CSUCCESS | CFOUND;

datatype 'a pac_step = Add of nat * nat * nat * 'a | Mult of nat * 'a * nat * 'a
  | Extension of nat * 'a | Del of nat;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun suc n = plus_nat n one_nat;

fun len A_ a =
  (fn () => let
              val i = (fn () => IntInf.fromInt (Array.length a)) ();
            in
              nat_of_integer i
            end);

fun new A_ =
  (fn a => fn b => (fn () => Array.array (IntInf.toInt a, b))) o integer_of_nat;

fun nth A_ a n = (fn () => Array.sub (a, IntInf.toInt (integer_of_nat n)));

fun upd A_ i x a =
  (fn () =>
    let
      val _ =
        (fn () => Array.update (a, IntInf.toInt (integer_of_nat i), x)) ();
    in
      a
    end);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun drop n [] = []
  | drop n (x :: xs) =
    (if equal_nata n zero_nat then x :: xs else drop (minus_nat n one_nat) xs);

fun take n [] = []
  | take n (x :: xs) =
    (if equal_nata n zero_nat then [] else x :: take (minus_nat n one_nat) xs);

fun lexordp A_ r (x :: xs) (y :: ys) =
  r x y orelse eq A_ x y andalso lexordp A_ r xs ys
  | lexordp A_ r [] (y :: ys) = true
  | lexordp A_ r xs [] = false;

fun hd (x21 :: x22) = x21;

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun remove1 A_ x [] = []
  | remove1 A_ x (y :: xs) = (if eq A_ x y then xs else y :: remove1 A_ x xs);

fun replicate n x =
  (if equal_nata n zero_nat then []
    else x :: replicate (minus_nat n one_nat) x);

fun implode cs =
  (String.implode
    o List.map (fn k => if 0 <= k andalso k < 128 then (Char.chr o IntInf.toInt) k else raise Fail "Non-ASCII character in literal"))
    (map integer_of_char cs);

fun blit A_ src si dst di len =
  (fn () => 
    array_blit src (integer_of_nat
                     si) dst (integer_of_nat di) (integer_of_nat len));

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun nth_oo A_ v a = (fn b => array_nth_oo v a b) o integer_of_nat;

fun upd_oo A_ f =
  (fn a => fn b => fn c => array_upd_oo f a b c) o integer_of_nat;

fun ht_new_sz (A1_, A2_) B_ n =
  let
    val l = replicate n [];
  in
    (fn () => let
                val a = (fn () => Array.fromList l) ();
              in
                HashTable (a, zero_nat)
              end)
  end;

fun ht_new (A1_, A2_) B_ = ht_new_sz (A1_, A2_) B_ (def_hashmap_size A1_ Type);

fun nat_of_uint32 x =
  nat_of_integer (IntInf.fromLarge (Word32.toLargeInt x) : IntInf.int);

fun nat_of_hashcode x = nat_of_uint32 x;

fun bounded_hashcode_nat A_ n x =
  modulo_nat (nat_of_hashcode (hashcode A_ x)) n;

fun the_array (HashTable (a, uu)) = a;

fun ls_update A_ k v [] = ([(k, v)], false)
  | ls_update A_ k v ((l, w) :: ls) =
    (if eq A_ k l then ((k, v) :: ls, true)
      else let
             val r = ls_update A_ k v ls;
           in
             ((l, w) :: fst r, snd r)
           end);

fun the_size (HashTable (uu, n)) = n;

fun ht_upd (A1_, A2_, A3_) B_ k v ht =
  (fn () =>
    let
      val m = len (heap_list (heap_prod A3_ B_)) (the_array ht) ();
    in
      let
        val i = bounded_hashcode_nat A2_ m k;
      in
        (fn f_ => fn () => f_
          ((nth (heap_list (heap_prod A3_ B_)) (the_array ht) i) ()) ())
          (fn l =>
            let
              val la = ls_update A1_ k v l;
            in
              (fn f_ => fn () => f_
                ((upd (heap_list (heap_prod A3_ B_)) i (fst la) (the_array ht))
                ()) ())
                (fn _ =>
                  let
                    val n = (if snd la then the_size ht else suc (the_size ht));
                  in
                    (fn () => (HashTable (the_array ht, n)))
                  end)
            end)
      end
        ()
    end);

fun the (SOME x2) = x2;

fun ht_insls (A1_, A2_, A3_) B_ [] ht = (fn () => ht)
  | ht_insls (A1_, A2_, A3_) B_ ((k, v) :: l) ht =
    (fn () => let
                val x = ht_upd (A1_, A2_, A3_) B_ k v ht ();
              in
                ht_insls (A1_, A2_, A3_) B_ l x ()
              end);

fun ht_copy (A1_, A2_, A3_) B_ n src dst =
  (if equal_nata n zero_nat then (fn () => dst)
    else (fn () =>
           let
             val l =
               nth (heap_list (heap_prod A3_ B_)) (the_array src)
                 (minus_nat n one_nat) ();
             val x = ht_insls (A1_, A2_, A3_) B_ l dst ();
           in
             ht_copy (A1_, A2_, A3_) B_ (minus_nat n one_nat) src x ()
           end));

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

val load_factor : nat = nat_of_integer (75 : IntInf.int);

fun ht_rehash (A1_, A2_, A3_) B_ ht =
  (fn () =>
    let
      val n = len (heap_list (heap_prod A3_ B_)) (the_array ht) ();
      val x =
        ht_new_sz (A2_, A3_) B_ (times_nat (nat_of_integer (2 : IntInf.int)) n)
          ();
    in
      ht_copy (A1_, A2_, A3_) B_ n ht x ()
    end);

fun ht_update (A1_, A2_, A3_) B_ k v ht =
  (fn () =>
    let
      val m = len (heap_list (heap_prod A3_ B_)) (the_array ht) ();
      val x =
        (if less_eq_nat (times_nat m load_factor)
              (times_nat (the_size ht) (nat_of_integer (100 : IntInf.int)))
          then ht_rehash (A1_, A2_, A3_) B_ ht else (fn () => ht))
          ();
    in
      ht_upd (A1_, A2_, A3_) B_ k v x ()
    end);

fun hs_ins (A1_, A2_, A3_) x ht = ht_update (A1_, A2_, A3_) heap_unit x () ht;

fun hs_new (A1_, A2_) = ht_new (A1_, A2_) heap_unit;

fun ls_delete A_ k [] = ([], false)
  | ls_delete A_ k ((l, w) :: ls) =
    (if eq A_ k l then (ls, true) else let
 val r = ls_delete A_ k ls;
                                       in
 ((l, w) :: fst r, snd r)
                                       end);

fun ht_delete (A1_, A2_, A3_) B_ k ht =
  (fn () =>
    let
      val m = len (heap_list (heap_prod A3_ B_)) (the_array ht) ();
    in
      let
        val i = bounded_hashcode_nat A2_ m k;
      in
        (fn f_ => fn () => f_
          ((nth (heap_list (heap_prod A3_ B_)) (the_array ht) i) ()) ())
          (fn l =>
            let
              val la = ls_delete A1_ k l;
            in
              (fn f_ => fn () => f_
                ((upd (heap_list (heap_prod A3_ B_)) i (fst la) (the_array ht))
                ()) ())
                (fn _ =>
                  let
                    val n =
                      (if snd la then minus_nat (the_size ht) one_nat
                        else the_size ht);
                  in
                    (fn () => (HashTable (the_array ht, n)))
                  end)
            end)
      end
        ()
    end);

fun ls_lookup A_ x [] = NONE
  | ls_lookup A_ x ((k, v) :: l) =
    (if eq A_ x k then SOME v else ls_lookup A_ x l);

fun ht_lookup (A1_, A2_, A3_) B_ x ht =
  (fn () =>
    let
      val m = len (heap_list (heap_prod A3_ B_)) (the_array ht) ();
    in
      let
        val i = bounded_hashcode_nat A2_ m x;
      in
        (fn f_ => fn () => f_
          ((nth (heap_list (heap_prod A3_ B_)) (the_array ht) i) ()) ())
          (fn l => (fn () => (ls_lookup A1_ x l)))
      end
        ()
    end);

fun op_list_hd x = hd x;

fun op_list_tl x = tl x;

fun array_grow A_ a s x =
  (fn () =>
    let
      val l = len A_ a ();
    in
      (if equal_nata l s then (fn () => a)
        else (fn f_ => fn () => f_ ((new A_ s x) ()) ())
               (fn aa =>
                 (fn f_ => fn () => f_ ((blit A_ a zero_nat aa zero_nat l) ())
                   ())
                   (fn _ => (fn () => aa))))
        ()
    end);

fun hs_memb (A1_, A2_, A3_) x s =
  (fn () => let
              val r = ht_lookup (A1_, A2_, A3_) heap_unit x s ();
            in
              (case r of NONE => false | SOME _ => true)
            end);

fun error_msg A_ i msg =
  CFAILED
    ([Chara (true, true, false, false, true, true, true, false),
       Chara (false, false, false, false, false, true, false, false),
       Chara (true, true, false, false, false, false, true, false),
       Chara (false, false, false, true, false, false, true, false),
       Chara (true, false, true, false, false, false, true, false),
       Chara (true, true, false, false, false, false, true, false),
       Chara (true, true, false, true, false, false, true, false),
       Chara (true, false, false, true, false, false, true, false),
       Chara (false, true, true, true, false, false, true, false),
       Chara (true, true, true, false, false, false, true, false),
       Chara (false, false, false, false, false, true, false, false),
       Chara (false, true, true, false, false, true, true, false),
       Chara (true, false, false, false, false, true, true, false),
       Chara (true, false, false, true, false, true, true, false),
       Chara (false, false, true, true, false, true, true, false),
       Chara (true, false, true, false, false, true, true, false),
       Chara (false, false, true, false, false, true, true, false),
       Chara (false, false, false, false, false, true, false, false),
       Chara (true, false, false, false, false, true, true, false),
       Chara (false, false, true, false, true, true, true, false),
       Chara (false, false, false, false, false, true, false, false),
       Chara (false, false, true, true, false, true, true, false),
       Chara (true, false, false, true, false, true, true, false),
       Chara (false, true, true, true, false, true, true, false),
       Chara (true, false, true, false, false, true, true, false),
       Chara (false, false, false, false, false, true, false, false)] @
      shows_prec A_ zero_nat i [] @
        [Chara (false, false, false, false, false, true, false, false),
          Chara (true, true, true, false, true, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (false, false, false, true, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (false, false, false, false, false, true, false, false)] @
          msg);

val iam_initial_size : nat = nat_of_integer (8 : IntInf.int);

fun iam_new_sz A_ sz = new (heap_option A_) sz NONE;

fun iam_new A_ = iam_new_sz A_ iam_initial_size;

fun merge f (x :: xs) (y :: ys) =
  (if f x y then x :: merge f xs (y :: ys) else y :: merge f (x :: xs) ys)
  | merge f xs [] = xs
  | merge f [] (v :: va) = v :: va;

fun size_list x = gen_length zero_nat x;

fun msort f [] = []
  | msort f [x] = [x]
  | msort f (v :: vb :: vc) =
    merge f
      (msort f
        (take (divide_nat (size_list (v :: vb :: vc))
                (nat_of_integer (2 : IntInf.int)))
          (v :: vb :: vc)))
      (msort f
        (drop (divide_nat (size_list (v :: vb :: vc))
                (nat_of_integer (2 : IntInf.int)))
          (v :: vb :: vc)));

fun msort2 f (v :: vb :: va :: vd) =
  merge f
    (msort f
      (v :: take (divide_nat (suc (size_list vd))
                   (nat_of_integer (2 : IntInf.int)))
              (vb :: va :: vd)))
    (msort f
      (drop (divide_nat (suc (size_list vd)) (nat_of_integer (2 : IntInf.int)))
        (vb :: va :: vd)))
  | msort2 f [x, y] = (if f x y then [x, y] else [y, x])
  | msort2 f [x] = [x]
  | msort2 f [] = [];

fun op_list_concat x = (fn a => x @ a);

val one_int : int = Int_of_integer (1 : IntInf.int);

fun iam_lookup A_ k a = nth_oo (heap_option A_) NONE a k;

fun iam_update A_ k v a =
  upd_oo (heap_option A_)
    (fn () =>
      let
        val l = len (heap_option A_) a ();
      in
        let
          val newsz =
            max ord_nat (plus_nat k one_nat)
              (plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) l)
                (nat_of_integer (3 : IntInf.int)));
        in
          (fn f_ => fn () => f_ ((array_grow (heap_option A_) a newsz NONE) ())
            ())
            (upd (heap_option A_) k (SOME v))
        end
          ()
      end)
    k (SOME v) a;

fun op_list_prepend x = (fn a => x :: a);

fun merge_cstatus (CFAILED a) uu = CFAILED a
  | merge_cstatus CSUCCESS (CFAILED a) = CFAILED a
  | merge_cstatus CFOUND (CFAILED a) = CFAILED a
  | merge_cstatus CFOUND CSUCCESS = CFOUND
  | merge_cstatus CFOUND CFOUND = CFOUND
  | merge_cstatus CSUCCESS CFOUND = CFOUND
  | merge_cstatus CSUCCESS CSUCCESS = CSUCCESS;

fun op_list_is_empty x = null x;

fun plus_int k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

fun lexord_eq (A1_, A2_) [] uu = true
  | lexord_eq (A1_, A2_) (x :: xs) (y :: ys) =
    less A2_ x y orelse eq A1_ x y andalso lexord_eq (A1_, A2_) xs ys
  | lexord_eq (A1_, A2_) (v :: va) [] = false;

fun imp_nfoldli (x :: ls) c f s =
  (fn () =>
    let
      val b = c s ();
    in
      (if b then (fn f_ => fn () => f_ ((f x s) ()) ()) (imp_nfoldli ls c f)
        else (fn () => s))
        ()
    end)
  | imp_nfoldli [] c f s = (fn () => s);

fun is_None a = (case a of NONE => true | SOME _ => false);

fun times_int k l =
  Int_of_integer (IntInf.* (integer_of_int k, integer_of_int l));

fun heap_WHILET b f s =
  (fn () =>
    let
      val bv = b s ();
    in
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s))
        ()
    end);

val error_msg_notin_dom_err : char list =
  [Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false)];

fun error_msg_notin_dom i =
  shows_prec_nat zero_nat i [] @ error_msg_notin_dom_err;

fun error_msg_reused_dom A_ i =
  shows_prec A_ zero_nat i [] @
    [Chara (false, false, false, false, false, true, false, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, false, true, true, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (true, false, false, true, true, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (true, false, true, true, false, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false)];

fun msort_poly_impl x =
  msort (fn a => fn b => lexord_eq (equal_literal, ord_literal) (fst a) (fst b))
    x;

fun is_cfound (CFAILED x1) = false
  | is_cfound CSUCCESS = false
  | is_cfound CFOUND = true;

fun the_error (CFAILED x1) = x1;

fun is_cfailed (CFAILED x1) = true
  | is_cfailed CSUCCESS = false
  | is_cfailed CFOUND = false;

fun merge_coeffs_impl_0 x =
  (case x of [] => (fn () => []) | [(_, _)] => (fn () => x)
    | (a1, a2) :: (a1a, a2a) :: l_a =>
      (if equal_lista equal_literal a1 a1a
        then (if not (equal_inta (plus_int a2 a2a) zero_int)
               then merge_coeffs_impl_0
                      (op_list_prepend (a1, plus_int a2 a2a) l_a)
               else merge_coeffs_impl_0 l_a)
        else (fn () =>
               let
                 val x_c =
                   merge_coeffs_impl_0 (op_list_prepend (a1a, a2a) l_a) ();
               in
                 op_list_prepend (a1, a2) x_c
               end)));

fun merge_coeffs_impl x = merge_coeffs_impl_0 x;

fun msort_monoms_impl x = msort2 (fn a => fn b => ((a : string) <= b)) x;

fun error_msg_not_equal_dom A_ B_ C_ D_ p q pq r =
  shows_prec A_ zero_nat p [] @
    [Chara (false, false, false, false, false, true, false, false),
      Chara (true, true, false, true, false, true, false, false),
      Chara (false, false, false, false, false, true, false, false)] @
      shows_prec B_ zero_nat q [] @
        [Chara (false, false, false, false, false, true, false, false),
          Chara (true, false, true, true, true, true, false, false),
          Chara (false, false, false, false, false, true, false, false)] @
          shows_prec C_ zero_nat pq [] @
            [Chara (false, false, false, false, false, true, false, false),
              Chara (false, true, true, true, false, true, true, false),
              Chara (true, true, true, true, false, true, true, false),
              Chara (false, false, true, false, true, true, true, false),
              Chara (false, false, false, false, false, true, false, false),
              Chara (true, false, true, false, false, true, true, false),
              Chara (true, false, false, false, true, true, true, false),
              Chara (true, false, true, false, true, true, true, false),
              Chara (true, false, false, false, false, true, true, false),
              Chara (false, false, true, true, false, true, true, false)] @
              shows_prec D_ zero_nat r [];

fun merge_coeffs0_impl_0 x =
  (case x of [] => (fn () => [])
    | [(a1, a2)] =>
      (fn () =>
        (if equal_inta (snd (a1, a2)) zero_int then []
          else op_list_prepend (a1, a2) []))
    | (a1, a2) :: (a1a, a2a) :: l_a =>
      (if equal_lista equal_literal a1 a1a
        then (if not (equal_inta (plus_int a2 a2a) zero_int)
               then merge_coeffs0_impl_0
                      (op_list_prepend (a1, plus_int a2 a2a) l_a)
               else merge_coeffs0_impl_0 l_a)
        else (if equal_inta a2 zero_int
               then merge_coeffs0_impl_0 (op_list_prepend (a1a, a2a) l_a)
               else (fn () =>
                      let
                        val x_d =
                          merge_coeffs0_impl_0 (op_list_prepend (a1a, a2a) l_a)
                            ();
                      in
                        op_list_prepend (a1, a2) x_d
                      end))));

fun merge_coeffs0_impl x = merge_coeffs0_impl_0 x;

fun less_list (A1_, A2_) = lexordp A1_ (less A2_);

fun add_poly_impl_0 x =
  (case x
    of ([], a2) =>
      (fn () => (case a2 of [] => [] | a :: b => op_list_prepend a b))
    | ((a1a, a2a) :: l, []) => (fn () => (op_list_prepend (a1a, a2a) l))
    | ((a1a, a2a) :: l, (a1b, a2b) :: l_a) =>
      (if equal_lista equal_literal a1a a1b
        then (if equal_inta (plus_int a2a a2b) zero_int
               then add_poly_impl_0 (l, l_a)
               else (fn () => let
                                val x_d = add_poly_impl_0 (l, l_a) ();
                              in
                                op_list_prepend (a1a, plus_int a2a a2b) x_d
                              end))
        else (if less_list (equal_literal, ord_literal) a1a a1b
               then (fn () =>
                      let
                        val x_d =
                          add_poly_impl_0 (l, op_list_prepend (a1b, a2b) l_a)
                            ();
                      in
                        op_list_prepend (a1a, a2a) x_d
                      end)
               else (fn () =>
                      let
                        val x_d =
                          add_poly_impl_0 (op_list_prepend (a1a, a2a) l, l_a)
                            ();
                      in
                        op_list_prepend (a1b, a2b) x_d
                      end))));

fun add_poly_impl x = add_poly_impl_0 x;

fun normalize_poly_impl x = (fn xi => merge_coeffs_impl (msort_poly_impl xi)) x;

val pAC_empty_impl : (unit -> ((((string list * int) list) option) array)) =
  iam_new (heap_list (heap_prod (heap_list heap_literal) heap_int));

fun mult_monoms_impl_0 x =
  let
    val (a1, a2) = x;
  in
    (case a1 of [] => (fn () => a2)
      | x_a :: l =>
        (case a2 of [] => (fn () => a1)
          | x_b :: l_a =>
            (if ((x_a : string) = x_b)
              then (fn () => let
                               val x_d = mult_monoms_impl_0 (l, l_a) ();
                             in
                               op_list_prepend x_a x_d
                             end)
              else (if ((x_a : string) < x_b)
                     then (fn () =>
                            let
                              val x_e =
                                mult_monoms_impl_0 (l, op_list_prepend x_b l_a)
                                  ();
                            in
                              op_list_prepend x_a x_e
                            end)
                     else (fn () =>
                            let
                              val x_e =
                                mult_monoms_impl_0 (op_list_prepend x_a l, l_a)
                                  ();
                            in
                              op_list_prepend x_b x_e
                            end)))))
  end;

fun mult_monoms_impl x = (fn ai => fn bi => mult_monoms_impl_0 (ai, bi)) x;

fun mult_monomials_impl x =
  (fn ai => fn bi => let
                       val (a1, a2) = ai;
                       val (a1a, a2a) = bi;
                     in
                       (fn () => let
                                   val xa = mult_monoms_impl a1 a1a ();
                                 in
                                   (xa, times_int a2 a2a)
                                 end)
                     end)
    x;

fun map_append_poly_mult_impl_0 bia ai x =
  (case x of [] => (fn () => bia)
    | xa :: l =>
      (fn () => let
                  val x_a = map_append_poly_mult_impl_0 bia ai l ();
                  val x_b = mult_monomials_impl ai xa ();
                in
                  op_list_prepend x_b x_a
                end));

fun map_append_poly_mult_impl x =
  (fn ai => fn bia => map_append_poly_mult_impl_0 bia ai) x;

fun mult_poly_raw_impl x =
  (fn ai => fn bi =>
    imp_nfoldli ai (fn _ => (fn () => true))
      (fn xa => fn sigma => map_append_poly_mult_impl xa sigma bi) [])
    x;

fun mult_poly_impl x =
  (fn ai => fn bi => fn () => let
                                val xa = mult_poly_raw_impl ai bi ();
                              in
                                normalize_poly_impl xa ()
                              end)
    x;

fun sort_all_coeffs_impl x =
  (fn xi =>
    imp_nfoldli xi (fn _ => (fn () => true))
      (fn xb => fn sigma =>
        (fn () => let
                    val (a1, a2) = xb;
                  in
                    op_list_prepend (msort_monoms_impl a1, a2) sigma
                  end))
      [])
    x;

fun pAC_update_impl x =
  iam_update (heap_list (heap_prod (heap_list heap_literal) heap_int)) x;

fun is_Extension (Add (x11, x12, x13, x14)) = false
  | is_Extension (Mult (x21, x22, x23, x24)) = false
  | is_Extension (Extension (x31, x32)) = true
  | is_Extension (Del x4) = false;

fun check_extension_l_new_var_multiple_err_impl A_ B_ v p =
  [Chara (true, false, true, false, false, false, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, true, false, true, true, true, false),
    Chara (false, false, false, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (false, false, false, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (true, true, false, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, true, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, true, true, false, true, true, true, false),
    Chara (false, false, true, true, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, false, true, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false)] @
    shows_prec A_ zero_nat v [] @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (true, false, true, false, true, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, false, false, false, true, true, true, false),
        Chara (false, false, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, true, false, false, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, false, false, true, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (true, false, false, true, true, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (true, false, true, true, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, true, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, true, false, true, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, true, false, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_prec B_ zero_nat p [] @
          [Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, false, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, true, true, true, false),
            Chara (false, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (false, true, true, true, false, true, false, false)];

fun check_extension_l_no_new_var_err_impl A_ p =
  [Chara (false, true, true, true, false, false, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, true, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, false, true, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, true, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, false, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, false, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false)] @
    shows_prec A_ zero_nat p [];

fun check_extension_l_side_cond_err_impl A_ B_ D_ v p r s =
  [Chara (true, false, true, false, false, false, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, true, false, true, true, true, false),
    Chara (false, false, false, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (false, false, false, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (true, true, false, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, true, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, true, true, false, true, true, true, false),
    Chara (false, false, true, true, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, false, true, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false)] @
    shows_prec A_ zero_nat v [] @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, false, false, true, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (true, false, false, true, true, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (true, false, true, true, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_prec B_ zero_nat p [] @
          [Chara (true, true, false, false, true, true, true, false),
            Chara (true, false, false, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, false, true, false, true, true, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (true, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, false, false, true, true, true, false),
            Chara (false, true, false, true, false, true, false, false),
            Chara (false, false, false, false, true, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, false, true, true, false, true, false, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, false, false, true, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, false, true, true, true, true, false, false),
            Chara (false, false, false, false, false, true, false, false)] @
            shows_prec D_ zero_nat s [] @
              [Chara (false, false, false, false, false, true, false, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (false, false, true, false, false, true, true, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (true, true, false, false, true, true, true, false),
                Chara (false, false, false, true, false, true, true, false),
                Chara (true, true, true, true, false, true, true, false),
                Chara (true, false, true, false, true, true, true, false),
                Chara (false, false, true, true, false, true, true, false),
                Chara (false, false, true, false, false, true, true, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (false, true, false, false, false, true, true, false),
                Chara (true, false, true, false, false, true, true, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (false, false, false, false, true, true, false, false)];

fun find_undefined_var_l_only_impl_0 ai x =
  (case x of [] => (fn () => NONE)
    | ([], _) :: l => find_undefined_var_l_only_impl_0 ai l
    | ([x_a], a2) :: l =>
      (fn () =>
        let
          val xa =
            hs_memb (equal_literal, hashable_literal, heap_literal) x_a ai ();
        in
          (if not xa andalso
                (equal_inta a2 one_int orelse
                  equal_inta a2 (uminus_int one_int))
            then (fn () => (SOME (x_a, a2)))
            else find_undefined_var_l_only_impl_0 ai l)
            ()
        end)
    | (_ :: _ :: _, _) :: l => find_undefined_var_l_only_impl_0 ai l);

fun find_undefined_var_l_only_impl x = find_undefined_var_l_only_impl_0 x;

fun find_undefined_var_l_fun_impl x =
  (fn ai => fn bi => fn () =>
    let
      val xa = find_undefined_var_l_only_impl ai bi ();
    in
      (if is_None xa then NONE
        else let
               val (a1, a2) = the xa;
             in
               SOME (a1, (a2, remove1
                                (equal_prod (equal_list equal_literal)
                                  equal_int)
                                (op_list_prepend a1 [], a2) bi))
             end)
    end)
    x;

fun check_ext_l_dom_err_impl p =
  [Chara (false, false, true, false, true, false, true, false),
    Chara (false, false, false, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, false, false, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, true, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false)] @
    shows_prec_nat zero_nat p [];

fun weak_equality_p_impl x =
  (fn ai => fn bi =>
    (fn () =>
      (equal_lista (equal_prod (equal_list equal_literal) equal_int) ai bi)))
    x;

fun vars_of_monom_in_impl x =
  (fn ai => fn bi =>
    imp_nfoldli ai (fn _ => (fn () => true))
      (fn xa => fn sigma => fn () =>
        let
          val x_b =
            hs_memb (equal_literal, hashable_literal, heap_literal) xa bi ();
        in
          sigma andalso x_b
        end)
      true)
    x;

fun vars_of_poly_in_impl x =
  (fn ai => fn bi =>
    imp_nfoldli ai (fn _ => (fn () => true))
      (fn xa => fn sigma =>
        let
          val (a1, _) = xa;
        in
          (fn () => let
                      val x_b = vars_of_monom_in_impl a1 bi ();
                    in
                      sigma andalso x_b
                    end)
        end)
      true)
    x;

fun check_extension_l_impl x =
  (fn _ => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val xa =
        ht_lookup (equal_nat, hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) bia bic ();
    in
      (if not (is_None xa)
        then (fn () =>
               (error_msg show_nat bia (check_ext_l_dom_err_impl bia), NONE))
        else (fn f_ => fn () => f_ ((find_undefined_var_l_fun_impl bib bi) ())
               ())
               (fn x_b =>
                 (if is_None x_b
                   then (fn () =>
                          (error_msg show_nat bia
                             (check_extension_l_no_new_var_err_impl
                               (show_list
                                 (show_prod (show_list show_literal) show_int))
                               bi),
                            NONE))
                   else let
                          val (a1, (a1a, a2a)) = the x_b;
                        in
                          (fn f_ => fn () => f_ ((vars_of_poly_in_impl a2a bib)
                            ()) ())
                            (fn x_e =>
                              (if not x_e
                                then (fn () =>
                                       (error_msg show_nat bia
  (check_extension_l_new_var_multiple_err_impl show_literal
    (show_list (show_prod (show_list show_literal) show_int)) a1 a2a),
 NONE))
                                else (fn f_ => fn () => f_
                                       ((mult_poly_impl a2a a2a) ()) ())
                                       (fn x_h =>
 (fn f_ => fn () => f_
   ((add_poly_impl
      (x_h, (if equal_inta a1a (uminus_int one_int)
              then map (fn (a, b) => (a, uminus_int b)) a2a else a2a)))
   ()) ())
   (fn x_k =>
     (fn f_ => fn () => f_ ((weak_equality_p_impl x_k []) ()) ())
       (fn x_l =>
         (fn () =>
           (if x_l then (CSUCCESS, SOME a1)
             else (error_msg show_nat bia
                     (check_extension_l_side_cond_err_impl show_literal
                       (show_list (show_prod (show_list show_literal) show_int))
                       (show_list (show_prod (show_list show_literal) show_int))
                       a1 bi a2a x_k),
                    NONE))))))))
                        end)))
        ()
    end)
    x;

fun check_addition_l_impl x =
  (fn ai => fn bie => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val xa =
        ht_lookup (equal_nat, hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) bic bie ();
      val xaa =
        ht_lookup (equal_nat, hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) bib bie ();
      val xb =
        ht_lookup (equal_nat, hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) bia bie ();
      val xc = vars_of_poly_in_impl bi bid ();
    in
      (if not (not (is_None xa) andalso
                (not (is_None xaa) andalso (not (not (is_None xb)) andalso xc)))
        then (fn f_ => fn () => f_
               ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                  (heap_list (heap_prod (heap_list heap_literal) heap_int)) bic
                  bie)
               ()) ())
               (fn xd =>
                 (fn f_ => fn () => f_
                   ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                      (heap_list (heap_prod (heap_list heap_literal) heap_int))
                      bib bie)
                   ()) ())
                   (fn xab =>
                     (fn f_ => fn () => f_
                       ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                          (heap_list
                            (heap_prod (heap_list heap_literal) heap_int))
                          bia bie)
                       ()) ())
                       (fn xba =>
                         (fn () =>
                           (error_msg show_nat bia
                             (op_list_concat
                               (if not (not (is_None xd))
                                 then error_msg_notin_dom bic else [])
                               (op_list_concat
                                 (if not (not (is_None xab))
                                   then error_msg_notin_dom bic else [])
                                 (if not (is_None xba)
                                   then error_msg_reused_dom show_nat bic
                                   else []))))))))
        else (fn f_ => fn () => f_
               ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                  (heap_list (heap_prod (heap_list heap_literal) heap_int)) bic
                  bie)
               ()) ())
               (fn xd =>
                 let
                   val x_c = the xd;
                 in
                   (fn f_ => fn () => f_
                     ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                        (heap_list
                          (heap_prod (heap_list heap_literal) heap_int))
                        bib bie)
                     ()) ())
                     (fn xe =>
                       let
                         val x_e = the xe;
                       in
                         (fn f_ => fn () => f_ ((add_poly_impl (x_c, x_e)) ())
                           ())
                           (fn x_g =>
                             (fn f_ => fn () => f_
                               ((weak_equality_p_impl x_g bi) ()) ())
                               (fn x_h =>
                                 (fn f_ => fn () => f_
                                   ((weak_equality_p_impl bi ai) ()) ())
                                   (fn x_i =>
                                     (fn () =>
                                       (if x_h
 then (if x_i then CFOUND else CSUCCESS)
 else error_msg show_nat bia
        (error_msg_not_equal_dom
          (show_list (show_prod (show_list show_literal) show_int))
          (show_list (show_prod (show_list show_literal) show_int))
          (show_list (show_prod (show_list show_literal) show_int))
          (show_list (show_prod (show_list show_literal) show_int)) x_c x_e x_g
          bi))))))
                       end)
                 end))
        ()
    end)
    x;

fun pac_src2 (Add (x11, x12, x13, x14)) = x12;

fun pac_src1 (Add (x11, x12, x13, x14)) = x11
  | pac_src1 (Mult (x21, x22, x23, x24)) = x21
  | pac_src1 (Del x4) = x4;

fun pac_mult (Mult (x21, x22, x23, x24)) = x22;

fun pac_res (Add (x11, x12, x13, x14)) = x14
  | pac_res (Mult (x21, x22, x23, x24)) = x24
  | pac_res (Extension (x31, x32)) = x32;

fun is_Mult (Add (x11, x12, x13, x14)) = false
  | is_Mult (Mult (x21, x22, x23, x24)) = true
  | is_Mult (Extension (x31, x32)) = false
  | is_Mult (Del x4) = false;

fun fully_normalize_poly_impl x =
  (fn xi => fn () => let
                       val xa = sort_all_coeffs_impl xi ();
                     in
                       merge_coeffs0_impl (msort_poly_impl xa) ()
                     end)
    x;

fun new_id (Add (x11, x12, x13, x14)) = x13
  | new_id (Mult (x21, x22, x23, x24)) = x23
  | new_id (Extension (x31, x32)) = x31;

fun is_Add (Add (x11, x12, x13, x14)) = true
  | is_Add (Mult (x21, x22, x23, x24)) = false
  | is_Add (Extension (x31, x32)) = false
  | is_Add (Del x4) = false;

fun check_mult_l_mult_err_impl A_ B_ C_ D_ p q pq r =
  [Chara (true, false, true, true, false, false, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false)] @
    shows_prec A_ zero_nat p [] @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (true, false, false, true, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_prec B_ zero_nat q [] @
          [Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, true, false, false, true, true, false),
            Chara (true, false, false, true, false, true, true, false),
            Chara (false, true, true, false, true, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (true, true, false, false, true, true, true, false),
            Chara (false, false, false, false, false, true, false, false)] @
            shows_prec C_ zero_nat pq [] @
              [Chara (false, false, false, false, false, true, false, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (false, false, true, false, false, true, true, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (true, true, true, true, false, true, true, false),
                Chara (false, false, true, false, true, true, true, false),
                Chara (false, false, false, false, false, true, false, false)] @
                shows_prec D_ zero_nat r [];

fun check_mult_l_dom_err_impl A_ B_ pd p ia i =
  (if pd
    then [Chara (false, false, true, false, true, false, true, false),
           Chara (false, false, false, true, false, true, true, false),
           Chara (true, false, true, false, false, true, true, false),
           Chara (false, false, false, false, false, true, false, false),
           Chara (false, false, false, false, true, true, true, false),
           Chara (true, true, true, true, false, true, true, false),
           Chara (false, false, true, true, false, true, true, false),
           Chara (true, false, false, true, true, true, true, false),
           Chara (false, true, true, true, false, true, true, false),
           Chara (true, true, true, true, false, true, true, false),
           Chara (true, false, true, true, false, true, true, false),
           Chara (false, false, false, false, false, true, false, false),
           Chara (true, true, true, false, true, true, true, false),
           Chara (true, false, false, true, false, true, true, false),
           Chara (false, false, true, false, true, true, true, false),
           Chara (false, false, false, true, false, true, true, false),
           Chara (false, false, false, false, false, true, false, false),
           Chara (true, false, false, true, false, true, true, false),
           Chara (false, false, true, false, false, true, true, false),
           Chara (false, false, false, false, false, true, false, false)] @
           shows_prec A_ zero_nat p [] @
             [Chara (false, false, false, false, false, true, false, false),
               Chara (true, true, true, false, true, true, true, false),
               Chara (true, false, false, false, false, true, true, false),
               Chara (true, true, false, false, true, true, true, false),
               Chara (false, false, false, false, false, true, false, false),
               Chara (false, true, true, true, false, true, true, false),
               Chara (true, true, true, true, false, true, true, false),
               Chara (false, false, true, false, true, true, true, false),
               Chara (false, false, false, false, false, true, false, false),
               Chara (false, true, true, false, false, true, true, false),
               Chara (true, true, true, true, false, true, true, false),
               Chara (true, false, true, false, true, true, true, false),
               Chara (false, true, true, true, false, true, true, false),
               Chara (false, false, true, false, false, true, true, false)]
    else []) @
    (if ia
      then [Chara (false, false, true, false, true, false, true, false),
             Chara (false, false, false, true, false, true, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (true, false, false, true, false, true, true, false),
             Chara (false, false, true, false, false, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (true, true, true, true, false, true, true, false),
             Chara (false, true, true, false, false, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (false, false, true, false, true, true, true, false),
             Chara (false, false, false, true, false, true, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (false, true, false, false, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (true, true, false, false, true, true, true, false),
             Chara (true, false, true, false, true, true, true, false),
             Chara (false, false, true, true, false, true, true, false),
             Chara (false, false, true, false, true, true, true, false),
             Chara (true, false, false, true, false, true, true, false),
             Chara (false, true, true, true, false, true, true, false),
             Chara (true, true, true, false, false, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (true, false, false, true, false, true, true, false),
             Chara (false, false, true, false, false, true, true, false),
             Chara (false, false, false, false, false, true, false, false)] @
             shows_prec B_ zero_nat i [] @
               [Chara (false, false, false, false, false, true, false, false),
                 Chara (true, true, true, false, true, true, true, false),
                 Chara (true, false, false, false, false, true, true, false),
                 Chara (true, true, false, false, true, true, true, false),
                 Chara (false, false, false, false, false, true, false, false),
                 Chara (true, true, true, false, true, true, true, false),
                 Chara (true, false, false, false, false, true, true, false),
                 Chara (true, true, false, false, true, true, true, false),
                 Chara (false, false, false, false, false, true, false, false),
                 Chara (true, false, false, false, false, true, true, false),
                 Chara (false, false, true, true, false, true, true, false),
                 Chara (false, true, false, false, true, true, true, false),
                 Chara (true, false, true, false, false, true, true, false),
                 Chara (true, false, false, false, false, true, true, false),
                 Chara (false, false, true, false, false, true, true, false),
                 Chara (true, false, false, true, true, true, true, false),
                 Chara (false, false, false, false, false, true, false, false),
                 Chara (true, true, true, false, false, true, true, false),
                 Chara (true, false, false, true, false, true, true, false),
                 Chara (false, true, true, false, true, true, true, false),
                 Chara (true, false, true, false, false, true, true, false),
                 Chara (false, true, true, true, false, true, true, false)]
      else []);

fun check_mult_l_impl x =
  (fn ai => fn bie => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val xa =
        ht_lookup (equal_nat, hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) bic bie ();
      val xaa =
        ht_lookup (equal_nat, hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) bia bie ();
      val xb = vars_of_poly_in_impl bib bid ();
      val xc = vars_of_poly_in_impl bi bid ();
    in
      (if not (not (is_None xa) andalso
                (not (not (is_None xaa)) andalso (xb andalso xc)))
        then (fn f_ => fn () => f_
               ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                  (heap_list (heap_prod (heap_list heap_literal) heap_int)) bic
                  bie)
               ()) ())
               (fn xd =>
                 (fn f_ => fn () => f_
                   ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                      (heap_list (heap_prod (heap_list heap_literal) heap_int))
                      bia bie)
                   ()) ())
                   (fn xab =>
                     (fn () =>
                       (error_msg show_nat bia
                         (check_mult_l_dom_err_impl show_nat show_nat
                           (not (not (is_None xd))) bic (not (is_None xab))
                           bia)))))
        else (fn f_ => fn () => f_
               ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                  (heap_list (heap_prod (heap_list heap_literal) heap_int)) bic
                  bie)
               ()) ())
               (fn xd =>
                 let
                   val x_c = the xd;
                 in
                   (fn f_ => fn () => f_ ((mult_poly_impl x_c bib) ()) ())
                     (fn x_e =>
                       (fn f_ => fn () => f_ ((weak_equality_p_impl x_e bi) ())
                         ())
                         (fn x_f =>
                           (fn f_ => fn () => f_ ((weak_equality_p_impl bi ai)
                             ()) ())
                             (fn x_g =>
                               (fn () =>
                                 (if x_f then (if x_g then CFOUND else CSUCCESS)
                                   else error_msg show_nat bia
  (check_mult_l_mult_err_impl
    (show_list (show_prod (show_list show_literal) show_int))
    (show_list (show_prod (show_list show_literal) show_int))
    (show_list (show_prod (show_list show_literal) show_int))
    (show_list (show_prod (show_list show_literal) show_int)) x_c bib x_e
    bi))))))
                 end))
        ()
    end)
    x;

fun check_del_l_dom_err_impl A_ p =
  [Chara (false, false, true, false, true, false, true, false),
    Chara (false, false, false, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, false, false, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false)] @
    shows_prec A_ zero_nat p [] @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (true, true, true, false, true, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, true, false, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (true, false, true, false, true, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false)];

fun check_del_l_impl x =
  (fn _ => fn bia => fn bi => fn () =>
    let
      val xa =
        ht_lookup (equal_nat, hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) bi bia ();
    in
      (if not (not (is_None xa))
        then error_msg show_nat bi (check_del_l_dom_err_impl show_nat bi)
        else CSUCCESS)
    end)
    x;

fun check_step_impl x =
  (fn ai => fn bic => fn bib => fn bia => fn bi =>
    (if is_Add bi
      then (fn () =>
             let
               val x_a = fully_normalize_poly_impl (pac_res bi) ();
               val x_b =
                 check_addition_l_impl ai bia bib (pac_src1 bi) (pac_src2 bi)
                   (new_id bi) x_a ();
             in
               (if not (is_cfailed x_b)
                 then (fn f_ => fn () => f_
                        ((ht_update (equal_nat, hashable_nat, heap_nat)
                           (heap_list
                             (heap_prod (heap_list heap_literal) heap_int))
                           (new_id bi) x_a bia)
                        ()) ())
                        (fn xa => (fn () => (merge_cstatus bic x_b, (bib, xa))))
                 else (fn () => (x_b, (bib, bia))))
                 ()
             end)
      else (if is_Mult bi
             then (fn () =>
                    let
                      val x_b = fully_normalize_poly_impl (pac_res bi) ();
                      val x_c = fully_normalize_poly_impl (pac_mult bi) ();
                      val x_d =
                        check_mult_l_impl ai bia bib (pac_src1 bi) x_c
                          (new_id bi) x_b ();
                    in
                      (if not (is_cfailed x_d)
                        then (fn f_ => fn () => f_
                               ((ht_update (equal_nat, hashable_nat, heap_nat)
                                  (heap_list
                                    (heap_prod (heap_list heap_literal)
                                      heap_int))
                                  (new_id bi) x_b bia)
                               ()) ())
                               (fn xa =>
                                 (fn () => (merge_cstatus bic x_d, (bib, xa))))
                        else (fn () => (x_d, (bib, bia))))
                        ()
                    end)
             else (if is_Extension bi
                    then (fn () =>
                           let
                             val x_c =
                               fully_normalize_poly_impl (pac_res bi) ();
                             val a =
                               check_extension_l_impl ai bia bib (new_id bi) x_c
                                 ();
                           in
                             let
                               val (a1, a2) = a;
                             in
                               (if not (is_cfailed a1)
                                 then (fn f_ => fn () => f_
((hs_ins (equal_literal, hashable_literal, heap_literal) (the a2) bib) ()) ())
(fn xa =>
  (fn f_ => fn () => f_
    ((ht_update (equal_nat, hashable_nat, heap_nat)
       (heap_list (heap_prod (heap_list heap_literal) heap_int)) (new_id bi) x_c
       bia)
    ()) ())
    (fn xaa => (fn () => (bic, (xa, xaa)))))
                                 else (fn () => (a1, (bib, bia))))
                             end
                               ()
                           end)
                    else (fn () =>
                           let
                             val x_c = check_del_l_impl ai bia (pac_src1 bi) ();
                           in
                             (if not (is_cfailed x_c)
                               then (fn f_ => fn () => f_
                                      ((ht_delete
 (equal_nat, hashable_nat, heap_nat)
 (heap_list (heap_prod (heap_list heap_literal) heap_int)) (pac_src1 bi) bia)
                                      ()) ())
                                      (fn xa =>
(fn () => (merge_cstatus bic x_c, (bib, xa))))
                               else (fn () => (x_c, (bib, bia))))
                               ()
                           end)))))
    x;

val empty_vars_impl : (unit -> (string, unit) hashtable) =
  hs_new (hashable_literal, heap_literal);

fun pAC_checker_l_impl x =
  (fn ai => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn () => let
                        val (a1a, _) = a1;
                      in
                        not (is_cfailed a1a) andalso not (op_list_is_empty a2)
                      end))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              (let
                 val (a1a, (a1b, a2b)) = a1;
               in
                 check_step_impl ai a1a a1b a2b (op_list_hd a2)
               end
              ()) ())
              (fn x_b => (fn () => (x_b, op_list_tl a2))))
          ((bia, (bic, bib)), bi) ();
    in
      let
        val (a1, _) = a;
      in
        (fn () => a1)
      end
        ()
    end)
    x;

fun union_vars_monom_impl x =
  (fn ai =>
    imp_nfoldli ai (fn _ => (fn () => true))
      (hs_ins (equal_literal, hashable_literal, heap_literal)))
    x;

fun union_vars_poly_impl x =
  (fn ai =>
    imp_nfoldli ai (fn _ => (fn () => true))
      (fn xa => fn sigma => let
                              val (a1, _) = xa;
                            in
                              union_vars_monom_impl a1 sigma
                            end))
    x;

fun remap_polys_l_impl x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa =
        len (heap_option
              (heap_list (heap_prod (heap_list heap_literal) heap_int)))
          bi ();
      val xaa =
        ht_new (hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) ();
      val xb =
        heap_WHILET (fn (a1, _) => (fn () => (less_nat a1 xa andalso true)))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              (let
                 val (a1a, (a1b, a2b)) = a2;
               in
                 (fn f_ => fn () => f_
                   ((iam_lookup
                      (heap_list (heap_prod (heap_list heap_literal) heap_int))
                      a1 bi)
                   ()) ())
                   (fn xb =>
                     (if not (is_None xb)
                       then (fn f_ => fn () => f_
                              ((iam_lookup
                                 (heap_list
                                   (heap_prod (heap_list heap_literal)
                                     heap_int))
                                 a1 bi)
                              ()) ())
                              (fn xc =>
                                (fn f_ => fn () => f_
                                  ((fully_normalize_poly_impl (the xc)) ()) ())
                                  (fn x_c =>
                                    (fn f_ => fn () => f_
                                      ((weak_equality_p_impl x_c ai) ()) ())
                                      (fn x_d =>
(fn f_ => fn () => f_
  ((iam_lookup (heap_list (heap_prod (heap_list heap_literal) heap_int)) a1 bi)
  ()) ())
  (fn xd =>
    (fn f_ => fn () => f_ ((union_vars_poly_impl (the xd) a1b) ()) ())
      (fn x_e =>
        (fn f_ => fn () => f_
          ((ht_update (equal_nat, hashable_nat, heap_nat)
             (heap_list (heap_prod (heap_list heap_literal) heap_int)) a1 x_c
             a2b)
          ()) ())
          (fn xe => (fn () => (a1a orelse x_d, (x_e, xe)))))))))
                       else (fn () => (a1a, (a1b, a2b)))))
               end
              ()) ())
              (fn x_b => (fn () => (plus_nat a1 one_nat, x_b))))
          (zero_nat, (false, (bia, xaa))) ();
      val (a1, (a1a, a2a)) = let
                               val (_, b) = xb;
                             in
                               b
                             end;
    in
      ((if a1 then CFOUND else CSUCCESS), (a1a, a2a))
    end)
    x;

fun full_checker_l_impl x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = fully_normalize_poly_impl ai ();
      val xaa = hs_new (hashable_literal, heap_literal) ();
      val a = remap_polys_l_impl xa xaa bia ();
    in
      let
        val (a1, (a1a, a2a)) = a;
      in
        (fn f_ => fn () => f_ ((union_vars_poly_impl ai a1a) ()) ())
          (fn x_b => let
                       val (a1b, a2b) = (x_b, a2a);
                     in
                       pAC_checker_l_impl xa a1b a2b a1 bi
                     end)
      end
        ()
    end)
    x;

end; (*struct PAC_Checker*)
