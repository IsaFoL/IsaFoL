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
  datatype 'a pac_step = AddD of nat * nat * nat * 'a |
    Add of nat * nat * nat * 'a | MultD of nat * 'a * nat * 'a |
    Mult of nat * 'a * nat * 'a
  type ('a, 'b) hashtable
  type 'a code_status
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
  val pAC_checker_l_impl :
    (string list * int) list ->
      (nat, ((string list * int) list)) hashtable ->
        ((string list * int) list) pac_step array ->
          (unit ->
            ((char list) code_status *
              (nat, ((string list * int) list)) hashtable))
  val full_checker_l_impl :
    (string list * int) list ->
      (((string list * int) list) option) array ->
        ((string list * int) list) pac_step array ->
          (unit ->
            ((char list) code_status *
              (nat, ((string list * int) list)) hashtable))
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

val one_integera : IntInf.int = (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_integer = {one = one_integera} : IntInf.int one;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype 'a pac_step = AddD of nat * nat * nat * 'a |
  Add of nat * nat * nat * 'a | MultD of nat * 'a * nat * 'a |
  Mult of nat * 'a * nat * 'a;

fun typerep_pac_stepa A_ t =
  Typerep ("PAC_Checker_Specification.pac_step", [typerep A_ Type]);

fun countable_pac_step A_ = {} : 'a pac_step countable;

fun typerep_pac_step A_ = {typerep = typerep_pac_stepa A_} :
  'a pac_step typerep;

fun heap_pac_step A_ =
  {countable_heap = countable_pac_step A_,
    typerep_heap = typerep_pac_step (typerep_heap A_)}
  : 'a pac_step heap;

datatype ('a, 'b) hashtable = HashTable of (('a * 'b) list) array * nat;

datatype 'a code_status = CFAILED of 'a | CSUCCESS | CFOUND;

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

fun replicate n x =
  (if equal_nata n zero_nat then []
    else x :: replicate (minus_nat n one_nat) x);

fun of_bool A_ true = one (one_zero_neq_one A_)
  | of_bool A_ false = zero (zero_zero_neq_one A_);

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

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

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

val load_factor : nat = nat_of_integer (75 : IntInf.int);

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

fun op_list_concat x = (fn a => x @ a);

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

fun plus_int k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

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

fun less_list (A1_, A2_) = lexordp A1_ (less A2_);

fun msort_poly_impl x =
  msort (fn a => fn b =>
          less_list (equal_literal, ord_literal) (fst a) (fst b) orelse
            equal_lista equal_literal (fst a) (fst b))
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

fun msort_monoms_impl x =
  msort (fn xa => fn y => ((xa : string) < y) orelse ((xa : string) = y)) x;

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
        (fn () =>
          let
            val (a1, a2) = xb;
          in
            op_list_concat sigma (op_list_prepend (msort_monoms_impl a1, a2) [])
          end))
      [])
    x;

fun pAC_update_impl x =
  iam_update (heap_list (heap_prod (heap_list heap_literal) heap_int)) x;

fun weak_equality_p_impl x =
  (fn ai => fn bi =>
    (fn () =>
      (equal_lista (equal_prod (equal_list equal_literal) equal_int) ai bi)))
    x;

fun check_addition_l_impl x =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val xa =
        ht_lookup (equal_nat, hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) bic bid ();
      val xaa =
        ht_lookup (equal_nat, hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) bib bid ();
      val xb =
        ht_lookup (equal_nat, hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) bia bid ();
    in
      (if not (not (is_None xa)) orelse
            (not (not (is_None xaa)) orelse not (is_None xb))
        then (fn f_ => fn () => f_
               ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                  (heap_list (heap_prod (heap_list heap_literal) heap_int)) bic
                  bid)
               ()) ())
               (fn xc =>
                 (fn f_ => fn () => f_
                   ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                      (heap_list (heap_prod (heap_list heap_literal) heap_int))
                      bib bid)
                   ()) ())
                   (fn xab =>
                     (fn f_ => fn () => f_
                       ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                          (heap_list
                            (heap_prod (heap_list heap_literal) heap_int))
                          bia bid)
                       ()) ())
                       (fn xba =>
                         (fn () =>
                           (error_msg show_nat bia
                             (op_list_concat
                               (if not (not (is_None xc))
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
                  bid)
               ()) ())
               (fn xc =>
                 let
                   val x_a = the xc;
                 in
                   (fn f_ => fn () => f_
                     ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                        (heap_list
                          (heap_prod (heap_list heap_literal) heap_int))
                        bib bid)
                     ()) ())
                     (fn xd =>
                       let
                         val x_c = the xd;
                       in
                         (fn f_ => fn () => f_ ((add_poly_impl (x_a, x_c)) ())
                           ())
                           (fn x_e =>
                             (fn f_ => fn () => f_
                               ((weak_equality_p_impl x_e bi) ()) ())
                               (fn x_f =>
                                 (fn f_ => fn () => f_
                                   ((weak_equality_p_impl bi ai) ()) ())
                                   (fn x_g =>
                                     (fn () =>
                                       (if x_f
 then (if x_g then CFOUND else CSUCCESS)
 else error_msg show_nat bia
        (error_msg_not_equal_dom
          (show_list (show_prod (show_list show_literal) show_int))
          (show_list (show_prod (show_list show_literal) show_int))
          (show_list (show_prod (show_list show_literal) show_int))
          (show_list (show_prod (show_list show_literal) show_int)) x_a x_c x_e
          bi))))))
                       end)
                 end))
        ()
    end)
    x;

fun pac_src2 (AddD (x11, x12, x13, x14)) = x12
  | pac_src2 (Add (x21, x22, x23, x24)) = x22;

fun pac_src1 (AddD (x11, x12, x13, x14)) = x11
  | pac_src1 (Add (x21, x22, x23, x24)) = x21
  | pac_src1 (MultD (x31, x32, x33, x34)) = x31
  | pac_src1 (Mult (x41, x42, x43, x44)) = x41;

fun pac_mult (MultD (x31, x32, x33, x34)) = x32
  | pac_mult (Mult (x41, x42, x43, x44)) = x42;

fun is_MultD (AddD (x11, x12, x13, x14)) = false
  | is_MultD (Add (x21, x22, x23, x24)) = false
  | is_MultD (MultD (x31, x32, x33, x34)) = true
  | is_MultD (Mult (x41, x42, x43, x44)) = false;

fun pac_res (AddD (x11, x12, x13, x14)) = x14
  | pac_res (Add (x21, x22, x23, x24)) = x24
  | pac_res (MultD (x31, x32, x33, x34)) = x34
  | pac_res (Mult (x41, x42, x43, x44)) = x44;

fun is_AddD (AddD (x11, x12, x13, x14)) = true
  | is_AddD (Add (x21, x22, x23, x24)) = false
  | is_AddD (MultD (x31, x32, x33, x34)) = false
  | is_AddD (Mult (x41, x42, x43, x44)) = false;

fun fully_normalize_poly_impl x =
  (fn xi => fn () => let
                       val xa = sort_all_coeffs_impl xi ();
                     in
                       merge_coeffs0_impl (msort_poly_impl xa) ()
                     end)
    x;

fun new_id (AddD (x11, x12, x13, x14)) = x13
  | new_id (Add (x21, x22, x23, x24)) = x23
  | new_id (MultD (x31, x32, x33, x34)) = x33
  | new_id (Mult (x41, x42, x43, x44)) = x43;

fun is_Add (AddD (x11, x12, x13, x14)) = false
  | is_Add (Add (x21, x22, x23, x24)) = true
  | is_Add (MultD (x31, x32, x33, x34)) = false
  | is_Add (Mult (x41, x42, x43, x44)) = false;

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
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val xa =
        ht_lookup (equal_nat, hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) bic bid ();
      val xaa =
        ht_lookup (equal_nat, hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) bia bid ();
    in
      (if not (not (is_None xa)) orelse not (is_None xaa)
        then (fn f_ => fn () => f_
               ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                  (heap_list (heap_prod (heap_list heap_literal) heap_int)) bic
                  bid)
               ()) ())
               (fn xb =>
                 (fn f_ => fn () => f_
                   ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                      (heap_list (heap_prod (heap_list heap_literal) heap_int))
                      bia bid)
                   ()) ())
                   (fn xab =>
                     (fn () =>
                       (error_msg show_nat bia
                         (check_mult_l_dom_err_impl show_nat show_nat
                           (not (not (is_None xb))) bic (not (is_None xab))
                           bia)))))
        else (fn f_ => fn () => f_
               ((ht_lookup (equal_nat, hashable_nat, heap_nat)
                  (heap_list (heap_prod (heap_list heap_literal) heap_int)) bic
                  bid)
               ()) ())
               (fn xb =>
                 let
                   val x_a = the xb;
                 in
                   (fn f_ => fn () => f_ ((mult_poly_impl x_a bib) ()) ())
                     (fn x_c =>
                       (fn f_ => fn () => f_ ((weak_equality_p_impl x_c bi) ())
                         ())
                         (fn x_d =>
                           (fn f_ => fn () => f_ ((weak_equality_p_impl bi ai)
                             ()) ())
                             (fn x_e =>
                               (fn () =>
                                 (if x_d then (if x_e then CFOUND else CSUCCESS)
                                   else error_msg show_nat bia
  (check_mult_l_mult_err_impl
    (show_list (show_prod (show_list show_literal) show_int))
    (show_list (show_prod (show_list show_literal) show_int))
    (show_list (show_prod (show_list show_literal) show_int))
    (show_list (show_prod (show_list show_literal) show_int)) x_a bib x_c
    bi))))))
                 end))
        ()
    end)
    x;

fun check_step_impl x =
  (fn ai => fn bib => fn bia => fn bi =>
    (if is_AddD bi
      then (fn () =>
             let
               val x_a = fully_normalize_poly_impl (pac_res bi) ();
               val x_b =
                 check_addition_l_impl ai bia (pac_src1 bi) (pac_src2 bi)
                   (new_id bi) x_a ();
             in
               (if not (is_cfailed x_b)
                 then (fn f_ => fn () => f_
                        ((ht_delete (equal_nat, hashable_nat, heap_nat)
                           (heap_list
                             (heap_prod (heap_list heap_literal) heap_int))
                           (pac_src2 bi) bia)
                        ()) ())
                        (fn xa =>
                          (fn f_ => fn () => f_
                            ((ht_delete (equal_nat, hashable_nat, heap_nat)
                               (heap_list
                                 (heap_prod (heap_list heap_literal) heap_int))
                               (pac_src1 bi) xa)
                            ()) ())
                            (fn xb =>
                              (fn f_ => fn () => f_
                                ((ht_update (equal_nat, hashable_nat, heap_nat)
                                   (heap_list
                                     (heap_prod (heap_list heap_literal)
                                       heap_int))
                                   (new_id bi) x_a xb)
                                ()) ())
                                (fn x_e =>
                                  (fn () => (merge_cstatus bib x_b, x_e)))))
                 else (fn () => (x_b, bia)))
                 ()
             end)
      else (if is_Add bi
             then (fn () =>
                    let
                      val x_b = fully_normalize_poly_impl (pac_res bi) ();
                      val x_c =
                        check_addition_l_impl ai bia (pac_src1 bi) (pac_src2 bi)
                          (new_id bi) x_b ();
                    in
                      (if not (is_cfailed x_c)
                        then (fn f_ => fn () => f_
                               ((ht_update (equal_nat, hashable_nat, heap_nat)
                                  (heap_list
                                    (heap_prod (heap_list heap_literal)
                                      heap_int))
                                  (new_id bi) x_b bia)
                               ()) ())
                               (fn x_f =>
                                 (fn () => (merge_cstatus bib x_c, x_f)))
                        else (fn () => (x_c, bia)))
                        ()
                    end)
             else (if is_MultD bi
                    then (fn () =>
                           let
                             val x_c =
                               fully_normalize_poly_impl (pac_res bi) ();
                             val x_d =
                               fully_normalize_poly_impl (pac_mult bi) ();
                             val x_e =
                               check_mult_l_impl ai bia (pac_src1 bi) x_d
                                 (new_id bi) x_c ();
                           in
                             (if not (is_cfailed x_e)
                               then (fn f_ => fn () => f_
                                      ((ht_delete
 (equal_nat, hashable_nat, heap_nat)
 (heap_list (heap_prod (heap_list heap_literal) heap_int)) (pac_src1 bi) bia)
                                      ()) ())
                                      (fn xa =>
(fn f_ => fn () => f_
  ((ht_update (equal_nat, hashable_nat, heap_nat)
     (heap_list (heap_prod (heap_list heap_literal) heap_int)) (new_id bi) x_c
     xa)
  ()) ())
  (fn x_h => (fn () => (merge_cstatus bib x_e, x_h))))
                               else (fn () => (x_e, bia)))
                               ()
                           end)
                    else (fn () =>
                           let
                             val x_c =
                               fully_normalize_poly_impl (pac_res bi) ();
                             val x_d =
                               fully_normalize_poly_impl (pac_mult bi) ();
                             val x_e =
                               check_mult_l_impl ai bia (pac_src1 bi) x_d
                                 (new_id bi) x_c ();
                           in
                             (if not (is_cfailed x_e)
                               then (fn f_ => fn () => f_
                                      ((ht_update
 (equal_nat, hashable_nat, heap_nat)
 (heap_list (heap_prod (heap_list heap_literal) heap_int)) (new_id bi) x_c bia)
                                      ()) ())
                                      (fn x_h =>
(fn () => (merge_cstatus bib x_e, x_h)))
                               else (fn () => (x_e, bia)))
                               ()
                           end)))))
    x;

fun pAC_checker_l_impl x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn ((a1a, _), a2) =>
            (fn f_ => fn () => f_
              ((len (heap_pac_step
                      (heap_list (heap_prod (heap_list heap_literal) heap_int)))
                 bi)
              ()) ())
              (fn xa =>
                (fn () => (not (is_cfailed a1a) andalso less_nat a2 xa))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              (let
                 val (a1a, a2a) = a1;
               in
                 (fn f_ => fn () => f_
                   ((nth (heap_pac_step
                           (heap_list
                             (heap_prod (heap_list heap_literal) heap_int)))
                      bi a2)
                   ()) ())
                   (check_step_impl ai a1a a2a)
               end
              ()) ())
              (fn x_b => (fn () => (x_b, plus_nat a2 one_nat))))
          ((CSUCCESS, bia), zero_nat) ();
    in
      let
        val (a1, _) = a;
      in
        (fn () => a1)
      end
        ()
    end)
    x;

fun remap_polys_l_impl x =
  (fn xi => fn () =>
    let
      val xa =
        len (heap_option
              (heap_list (heap_prod (heap_list heap_literal) heap_int)))
          xi ();
      val xaa =
        ht_new (hashable_nat, heap_nat)
          (heap_list (heap_prod (heap_list heap_literal) heap_int)) ();
      val a =
        heap_WHILET (fn (a1, _) => (fn () => (less_nat a1 xa andalso true)))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((iam_lookup
                 (heap_list (heap_prod (heap_list heap_literal) heap_int)) a1
                 xi)
              ()) ())
              (fn xb =>
                (fn f_ => fn () => f_
                  ((if not (is_None xb)
                     then (fn f_ => fn () => f_
                            ((iam_lookup
                               (heap_list
                                 (heap_prod (heap_list heap_literal) heap_int))
                               a1 xi)
                            ()) ())
                            (fn xc =>
                              (fn f_ => fn () => f_
                                ((fully_normalize_poly_impl (the xc)) ()) ())
                                (fn x_c =>
                                  ht_update (equal_nat, hashable_nat, heap_nat)
                                    (heap_list
                                      (heap_prod (heap_list heap_literal)
heap_int))
                                    a1 x_c a2))
                     else (fn () => a2))
                  ()) ())
                  (fn x_b => (fn () => (plus_nat a1 one_nat, x_b)))))
          (zero_nat, xaa) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun full_checker_l_impl x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = remap_polys_l_impl bia ();
      val x_a = fully_normalize_poly_impl ai ();
    in
      pAC_checker_l_impl x_a xa bi ()
    end)
    x;

end; (*struct PAC_Checker*)
