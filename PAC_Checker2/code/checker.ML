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

(* Test that words can handle numbers between 0 and 63 *)
val _ = if 6 <= Word.wordSize then () else raise (Fail ("wordSize less than 6"));

structure Uint64 : sig
  eqtype uint64;
  val zero : uint64;
  val one : uint64;
  val fromInt : IntInf.int -> uint64;
  val toInt : uint64 -> IntInf.int;
  val toFixedInt : uint64 -> Int.int;
  val toLarge : uint64 -> LargeWord.word;
  val fromLarge : LargeWord.word -> uint64
  val fromFixedInt : Int.int -> uint64
  val toWord32: uint64 -> Word32.word
  val plus : uint64 -> uint64 -> uint64;
  val minus : uint64 -> uint64 -> uint64;
  val times : uint64 -> uint64 -> uint64;
  val divide : uint64 -> uint64 -> uint64;
  val modulus : uint64 -> uint64 -> uint64;
  val negate : uint64 -> uint64;
  val less_eq : uint64 -> uint64 -> bool;
  val less : uint64 -> uint64 -> bool;
  val notb : uint64 -> uint64;
  val andb : uint64 -> uint64 -> uint64;
  val orb : uint64 -> uint64 -> uint64;
  val xorb : uint64 -> uint64 -> uint64;
  val shiftl : uint64 -> IntInf.int -> uint64;
  val shiftr : uint64 -> IntInf.int -> uint64;
  val shiftr_signed : uint64 -> IntInf.int -> uint64;
  val set_bit : uint64 -> IntInf.int -> bool -> uint64;
  val test_bit : uint64 -> IntInf.int -> bool;
end = struct

type uint64 = Word64.word;

val zero = (0wx0 : uint64);

val one = (0wx1 : uint64);

fun fromInt x = Word64.fromLargeInt (IntInf.toLarge x);

fun toInt x = IntInf.fromLarge (Word64.toLargeInt x);

fun toFixedInt x = Word64.toInt x;

fun fromLarge x = Word64.fromLarge x;

fun fromFixedInt x = Word64.fromInt x;

fun toLarge x = Word64.toLarge x;

fun toWord32 x = Word32.fromLarge x

fun plus x y = Word64.+(x, y);

fun minus x y = Word64.-(x, y);

fun negate x = Word64.~(x);

fun times x y = Word64.*(x, y);

fun divide x y = Word64.div(x, y);

fun modulus x y = Word64.mod(x, y);

fun less_eq x y = Word64.<=(x, y);

fun less x y = Word64.<(x, y);

fun set_bit x n b =
  let val mask = Word64.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word64.orb (x, mask)
     else Word64.andb (x, Word64.notb mask)
  end

fun shiftl x n =
  Word64.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word64.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word64.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word64.andb (x, Word64.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word64.fromInt 0

val notb = Word64.notb

fun andb x y = Word64.andb(x, y);

fun orb x y = Word64.orb(x, y);

fun xorb x y = Word64.xorb(x, y);

end (*struct Uint64*)



   fun array_blit src si dst di len = (
      src=dst andalso raise Fail ("array_blit: Same arrays");
      ArraySlice.copy {
        di = IntInf.toInt di,
        src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
        dst = dst})

    fun array_nth_oo v a i () = if IntInf.toInt i >= Array.length a then v 
       else Array.sub(a,IntInf.toInt i) handle Overflow => v
    fun array_upd_oo f i x a () = 
      if IntInf.toInt i >= Array.length a then f ()
      else
        (Array.update(a,IntInf.toInt i,x); a) handle Overflow => f ()



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
  type num
  type nat
  val nat_of_integer : IntInf.int -> nat
  type char
  val implode : char list -> string
  type ('a, 'b) hashtable
  type 'a code_status
  datatype ('a, 'b, 'c) pac_step = CL of ('a * 'c) list * 'c * 'a |
    Extension of 'c * 'b * 'a | Del of 'c
  type memory_allocation
  val is_cfound : 'a code_status -> bool
  val the_error : 'a code_status -> 'a
  val is_cfailed : 'a code_status -> bool
  val pAC_empty_impl : (unit -> ((((string list * int) list) option) array))
  val pAC_update_impl :
    nat ->
      (string list * int) list ->
        (((string list * int) list) option) array ->
          (unit -> ((((string list * int) list) option) array))
  val version : string
  val fully_normalize_poly_impl :
    (string list * int) list -> (unit -> ((string list * int) list))
  val pAC_checker_l_step_s_impl :
    (Uint64.uint64 list * int) list ->
      (char list) code_status *
        (((string array * nat) * (string, Uint64.uint64) hashtable) *
          (Uint64.uint64, ((Uint64.uint64 list * int) list)) hashtable) ->
        (((string list * int) list), string, Uint64.uint64) pac_step ->
          (unit ->
            ((char list) code_status *
              (((string array * nat) * (string, Uint64.uint64) hashtable) *
                (Uint64.uint64, ((Uint64.uint64 list * int) list)) hashtable)))
  val pAC_checker_l_s_impl :
    (Uint64.uint64 list * int) list ->
      ((string array * nat) * (string, Uint64.uint64) hashtable) *
        (Uint64.uint64, ((Uint64.uint64 list * int) list)) hashtable ->
        (char list) code_status ->
          (((string list * int) list), string, Uint64.uint64) pac_step list ->
            (unit ->
              ((char list) code_status *
                (((string array * nat) * (string, Uint64.uint64) hashtable) *
                  (Uint64.uint64, ((Uint64.uint64 list * int) list))
                    hashtable)))
  val empty_shared_vars_int_impl :
    (unit -> ((string array * nat) * (string, Uint64.uint64) hashtable))
  val remap_polys_l2_with_err_s_impl :
    (string list * int) list ->
      (string list * int) list ->
        (((string list * int) list) option) array ->
          (string array * nat) * (string, Uint64.uint64) hashtable ->
            (unit ->
              ((char list) code_status *
                (((string array * nat) * (string, Uint64.uint64) hashtable) *
                  ((Uint64.uint64, ((Uint64.uint64 list * int) list))
                     hashtable *
                    (Uint64.uint64 list * int) list))))
  val full_checker_l_s2_impl :
    (string list * int) list ->
      (((string list * int) list) option) array ->
        (((string list * int) list), string, Uint64.uint64) pac_step list ->
          (unit ->
            ((char list) code_status *
              (((string array * nat) * (string, Uint64.uint64) hashtable) *
                (Uint64.uint64, ((Uint64.uint64 list * int) list)) hashtable)))
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

fun uminus_inta k = Int_of_integer (IntInf.~ (integer_of_int k));

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

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

val zero_nata : nat = Nat (0 : IntInf.int);

val one_nat : nat = Nat (1 : IntInf.int);

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun string_of_digit n =
  (if equal_nat n zero_nata
    then [Chara (false, false, false, false, true, true, false, false)]
    else (if equal_nat n one_nat
           then [Chara (true, false, false, false, true, true, false, false)]
           else (if equal_nat n (nat_of_integer (2 : IntInf.int))
                  then [Chara (false, true, false, false, true, true, false,
                                false)]
                  else (if equal_nat n (nat_of_integer (3 : IntInf.int))
                         then [Chara (true, true, false, false, true, true,
                                       false, false)]
                         else (if equal_nat n (nat_of_integer (4 : IntInf.int))
                                then [Chara
(false, false, true, false, true, true, false, false)]
                                else (if equal_nat n
   (nat_of_integer (5 : IntInf.int))
                                       then [Chara
       (true, false, true, false, true, true, false, false)]
                                       else (if equal_nat n
          (nat_of_integer (6 : IntInf.int))
      then [Chara (false, true, true, false, true, true, false, false)]
      else (if equal_nat n (nat_of_integer (7 : IntInf.int))
             then [Chara (true, true, true, false, true, true, false, false)]
             else (if equal_nat n (nat_of_integer (8 : IntInf.int))
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
           showsp_nat p (nat (uminus_inta i))
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
  shows_list_gen (s zero_nata)
    [Chara (true, true, false, true, true, false, true, false),
      Chara (true, false, true, true, true, false, true, false)]
    [Chara (true, true, false, true, true, false, true, false)]
    [Chara (false, false, true, true, false, true, false, false),
      Chara (false, false, false, false, false, true, false, false)]
    [Chara (true, false, true, true, true, false, true, false)] xs;

fun shows_list_int x = showsp_list shows_prec_int zero_nata x;

type 'a show =
  {shows_prec : nat -> 'a -> char list -> char list,
    shows_list : 'a list -> char list -> char list};
val shows_prec = #shows_prec : 'a show -> nat -> 'a -> char list -> char list;
val shows_list = #shows_list : 'a show -> 'a list -> char list -> char list;

val show_int = {shows_prec = shows_prec_int, shows_list = shows_list_int} :
  int show;

type 'a uminus = {uminus : 'a -> 'a};
val uminus = #uminus : 'a uminus -> 'a -> 'a;

val uminus_int = {uminus = uminus_inta} : int uminus;

fun shows_prec_nat x = showsp_nat x;

fun shows_list_nat x = showsp_list shows_prec_nat zero_nata x;

val show_nat = {shows_prec = shows_prec_nat, shows_list = shows_list_nat} :
  nat show;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

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

fun shows_list_list A_ xss = showsp_list (shows_prec_list A_) zero_nata xss;

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

val equal_uint64 = {equal = (fn a => fn b => ((a : Uint64.uint64) = b))} :
  Uint64.uint64 equal;

fun typerep_uint64a t = Typerep ("Uint64.uint64", []);

val countable_uint64 = {} : Uint64.uint64 countable;

val typerep_uint64 = {typerep = typerep_uint64a} : Uint64.uint64 typerep;

val heap_uint64 =
  {countable_heap = countable_uint64, typerep_heap = typerep_uint64} :
  Uint64.uint64 heap;

fun def_hashmap_size_uint64 x = (fn _ => nat_of_integer (16 : IntInf.int)) x;

fun uint32_of_uint64 x = Uint64.toWord32 (x);

fun hashcode_uint64 n =
  uint32_of_uint64 (Uint64.andb n (Uint64.fromInt (4294967295 : IntInf.int)));

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a itself -> nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size : 'a hashable -> 'a itself -> nat;

val hashable_uint64 =
  {hashcode = hashcode_uint64, def_hashmap_size = def_hashmap_size_uint64} :
  Uint64.uint64 hashable;

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string equal;

fun typerep_literala t = Typerep ("String.literal", []);

val countable_literal = {} : string countable;

val typerep_literal = {typerep = typerep_literala} : string typerep;

val heap_literal =
  {countable_heap = countable_literal, typerep_heap = typerep_literal} :
  string heap;

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

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun implode cs =
  (String.implode
    o List.map (fn k => if 0 <= k andalso k < 128 then (Char.chr o IntInf.toInt) k else raise Fail "Non-ASCII character in literal"))
    (map integer_of_char cs);

val default_literala : string = implode [];

type 'a default = {default : 'a};
val default = #default : 'a default -> 'a;

val default_literal = {default = default_literala} : string default;

val ord_literal =
  {less_eq = (fn a => fn b => ((a : string) <= b)),
    less = (fn a => fn b => ((a : string) < b))}
  : string ord;

fun def_hashmap_size_literal uu = nat_of_integer (10 : IntInf.int);

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun string_nth s x =
  (String.sub (s, IntInf.toInt ((integer_of_int (int_of_nat x)))));

fun hashcode_char c = (Word32.fromInt  o (Char.ord)) c;

fun string_size x = nat_of_integer ((IntInf.fromInt ((String.size (x)))));

fun size_literal x = string_size x;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun hashcode_eff s h i =
  (if less_eq_nat (size_literal s) i then h
    else hashcode_eff s
           (Word32.+ (Word32.* (h, Word32.fromLargeInt (IntInf.toLarge (33 : IntInf.int))), hashcode_char
              (string_nth s i)))
           (plus_nat i one_nat));

fun hashcode_literal s =
  hashcode_eff s (Word32.fromLargeInt (IntInf.toLarge (5381 : IntInf.int)))
    zero_nata;

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

fun shows_list_prod A_ B_ = showsp_list (shows_prec_prod A_ B_) zero_nata;

fun show_prod A_ B_ =
  {shows_prec = shows_prec_prod A_ B_, shows_list = shows_list_prod A_ B_} :
  ('a * 'b) show;

datatype ('a, 'b) hashtable = HashTable of (('a * 'b) list) array * nat;

datatype 'a code_status = CFAILED of 'a | CSUCCESS | CFOUND;

datatype ordered = LESS | EQUAL | GREATER | UNKNOWN;

datatype ('a, 'b, 'c) pac_step = CL of ('a * 'c) list * 'c * 'a |
  Extension of 'c * 'b * 'a | Del of 'c;

datatype memory_allocation = Allocated | Mem_Out;

fun suc n = plus_nat n one_nat;

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun rev xs = fold (fn a => fn b => a :: b) xs [];

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
    (if equal_nat n zero_nata then x :: xs else drop (minus_nat n one_nat) xs);

fun take n [] = []
  | take n (x :: xs) =
    (if equal_nat n zero_nata then [] else x :: take (minus_nat n one_nat) xs);

fun hd (x21 :: x22) = x21;

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun replicate n x =
  (if equal_nat n zero_nata then []
    else x :: replicate (minus_nat n one_nat) x);

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
                HashTable (a, zero_nata)
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
  (if equal_nat n zero_nata then (fn () => dst)
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

fun op_list_hd x = hd x;

fun op_list_tl x = tl x;

fun nat_of_uint64 x = nat_of_integer (Uint64.toInt x);

fun uint64_of_int i = Uint64.fromInt (integer_of_int i);

fun uint64_of_nat x = (uint64_of_int o int_of_nat) x;

fun array_grow A_ a s x =
  (fn () =>
    let
      val l = len A_ a ();
    in
      (if equal_nat l s then (fn () => a)
        else (fn f_ => fn () => f_ ((new A_ s x) ()) ())
               (fn aa =>
                 (fn f_ => fn () => f_ ((blit A_ a zero_nata aa zero_nata l) ())
                   ())
                   (fn _ => (fn () => aa))))
        ()
    end);

fun op_list_rev x = rev x;

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
      shows_prec A_ zero_nata i [] @
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

fun size_list x = gen_length zero_nata x;

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

fun explode s =
  map char_of_integer
    ((List.map (fn c => let val k = Char.ord c in if k < 128 then IntInf.fromInt k else raise Fail "Non-ASCII character in literal" end) 
       o String.explode)
      s);

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

fun op_list_length x = size_list x;

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

val initial_capacity : nat = nat_of_integer (16 : IntInf.int);

fun arl_empty (A1_, A2_) B_ =
  (fn () => let
              val a = new A2_ initial_capacity (default A1_) ();
            in
              (a, zero B_)
            end);

fun op_list_prepend x = (fn a => x :: a);

fun merge_cstatus (CFAILED a) uu = CFAILED a
  | merge_cstatus CSUCCESS (CFAILED a) = CFAILED a
  | merge_cstatus CFOUND (CFAILED a) = CFAILED a
  | merge_cstatus CFOUND CSUCCESS = CFOUND
  | merge_cstatus CFOUND CFOUND = CFOUND
  | merge_cstatus CSUCCESS CFOUND = CFOUND
  | merge_cstatus CSUCCESS CSUCCESS = CSUCCESS;

fun arl_append (A1_, A2_) =
  (fn (a, n) => fn x => fn () =>
    let
      val lena = len A2_ a ();
    in
      (if less_nat n lena
        then (fn f_ => fn () => f_ ((upd A2_ n x a) ()) ())
               (fn aa => (fn () => (aa, plus_nat n one_nat)))
        else let
               val newcap = times_nat (nat_of_integer (2 : IntInf.int)) lena;
             in
               (fn f_ => fn () => f_ ((array_grow A2_ a newcap (default A1_))
                 ()) ())
                 (fn aa =>
                   (fn f_ => fn () => f_ ((upd A2_ n x aa) ()) ())
                     (fn ab => (fn () => (ab, plus_nat n one_nat))))
             end)
        ()
    end);

fun arl_length A_ = (fn (_, a) => (fn () => a));

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

fun is_Nil a = (case a of [] => true | _ :: _ => false);

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

fun msort_monoms_impl x = msort2 (fn a => fn b => ((a : string) <= b)) x;

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

fun arl_get_u A_ =
  (fn a => fn b =>
    (fn () => Array.sub ((fn (a,b) => a) (a),
      Word64.toInt (Uint64.toLarge (b)))));

val pAC_empty_impl : (unit -> ((((string list * int) list) option) array)) =
  iam_new (heap_list (heap_prod (heap_list heap_literal) heap_int));

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

val version : string = "8f639b73";

fun is_CL (CL (x11, x12, x13)) = true
  | is_CL (Extension (x21, x22, x23)) = false
  | is_CL (Del x3) = false;

fun shows_prec_literal p s = shows_string (explode s);

fun new_id (CL (x11, x12, x13)) = x12
  | new_id (Extension (x21, x22, x23)) = x21;

fun fully_normalize_poly_impl x =
  (fn xi => fn () => let
                       val xa = sort_all_coeffs_impl xi ();
                     in
                       merge_coeffs0_impl (msort_poly_impl xa) ()
                     end)
    x;

fun new_var (Extension (x21, x22, x23)) = x22;

fun pac_res (CL (x11, x12, x13)) = x13
  | pac_res (Extension (x21, x22, x23)) = x23;

fun pac_src1 (Del x3) = x3;

fun pac_srcs (CL (x11, x12, x13)) = x11;

fun uminus_poly B_ p = map (fn (a, b) => (a, uminus B_ b)) p;

fun length_arl_u_code A_ xs = (fn () => let
  val n = arl_length A_ xs ();
in
  uint64_of_nat n
end);

fun get_var_pos_c_impl x =
  (fn ai => fn bi =>
    let
      val (_, a2) = ai;
    in
      (fn () =>
        let
          val xa =
            ht_lookup (equal_literal, hashable_literal, heap_literal)
              heap_uint64 bi a2 ();
        in
          the xa
        end)
    end)
    x;

fun vars_llist_s2 [] = []
  | vars_llist_s2 ((a, uu) :: xs) = a @ vars_llist_s2 xs;

fun find_new_idx_c_impl x =
  (fn (a1, _) => fn () =>
    let
      val xa = arl_length heap_literal a1 ();
    in
      (if less_nat xa (nat_of_integer (9223372036854775807 : IntInf.int))
        then (fn f_ => fn () => f_ ((length_arl_u_code heap_literal a1) ()) ())
               (fn x_d => (fn () => (Allocated, x_d)))
        else (fn () => (Mem_Out, Uint64.zero)))
        ()
    end)
    x;

fun get_var_name_c_impl x =
  (fn ai => fn bi => let
                       val (a1, _) = ai;
                     in
                       arl_get_u heap_literal a1 bi
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
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
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
    shows_prec_nat zero_nata (nat_of_uint64 p) [];

val memory_out_msg : char list =
  [Chara (true, false, true, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, false, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false)];

fun is_Extension (CL (x11, x12, x13)) = false
  | is_Extension (Extension (x21, x22, x23)) = true
  | is_Extension (Del x3) = false;

val remap_polys_l_dom_err_impl : char list =
  [Chara (true, false, true, false, false, false, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, true, false, true, false, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, true, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, true, false, true, true, true, false),
    Chara (false, false, false, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (false, true, true, true, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, true, false, false, true, false),
    Chara (false, true, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, false, false, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, true, true, false, true, false, false)] @
    [Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, true, true, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (false, false, false, true, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, false, true, true, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (true, false, true, true, false, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, true, true, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (false, false, false, true, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (false, false, false, true, false, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (false, false, true, true, false, true, false, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (false, true, false, false, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (true, false, true, true, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (false, false, false, true, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, true, false, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (true, true, true, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (true, true, true, false, true, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, true, false, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, true, false, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false)] @
      [Chara (true, true, false, false, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, true, true, false, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, false, true, false, true, false, false),
        Chara (true, true, false, false, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, true, true, false, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (true, false, false, true, true, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (true, true, false, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (true, false, false, true, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (true, true, false, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, false, false, true, false, true, false, false),
        Chara (false, true, true, true, false, true, false, false)];

fun check_del_l_impl x = (fn _ => fn _ => fn _ => (fn () => CSUCCESS)) x;

fun perfect_shared_var_order_s_impl x =
  (fn ai => fn bia => fn bi =>
    (if ((bia : Uint64.uint64) = bi) then (fn () => EQUAL)
      else (fn () => let
                       val x_a = get_var_name_c_impl ai bia ();
                       val x_b = get_var_name_c_impl ai bi ();
                     in
                       (if ((x_a : string) < x_b) then LESS else GREATER)
                     end)))
    x;

fun equal_ordered GREATER UNKNOWN = false
  | equal_ordered UNKNOWN GREATER = false
  | equal_ordered EQUAL UNKNOWN = false
  | equal_ordered UNKNOWN EQUAL = false
  | equal_ordered EQUAL GREATER = false
  | equal_ordered GREATER EQUAL = false
  | equal_ordered LESS UNKNOWN = false
  | equal_ordered UNKNOWN LESS = false
  | equal_ordered LESS GREATER = false
  | equal_ordered GREATER LESS = false
  | equal_ordered LESS EQUAL = false
  | equal_ordered EQUAL LESS = false
  | equal_ordered UNKNOWN UNKNOWN = true
  | equal_ordered GREATER GREATER = true
  | equal_ordered EQUAL EQUAL = true
  | equal_ordered LESS LESS = true;

fun perfect_shared_term_order_rel_s_impl x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET (fn (a1, (_, _)) => (fn () => (equal_ordered a1 UNKNOWN)))
          (fn (a1, (a1a, a2a)) =>
            (if op_list_is_empty a1a andalso op_list_is_empty a2a
              then (fn () => (EQUAL, (a1a, a2a)))
              else (if op_list_is_empty a1a then (fn () => (LESS, (a1a, a2a)))
                     else (if op_list_is_empty a2a
                            then (fn () => (GREATER, (a1a, a2a)))
                            else (fn f_ => fn () => f_
                                   ((perfect_shared_var_order_s_impl ai
                                      (op_list_hd a1a) (op_list_hd a2a))
                                   ()) ())
                                   (fn x_d =>
                                     (fn () =>
                                       (if equal_ordered x_d EQUAL
 then (a1, (op_list_tl a1a, op_list_tl a2a)) else (x_d, (a1a, a2a)))))))))
          (UNKNOWN, (bia, bi)) ();
    in
      let
        val (a1, (_, _)) = a;
      in
        (fn () => a1)
      end
        ()
    end)
    x;

fun mergeR_vars_impl_0 ai x =
  (case x of ([], a2) => (fn () => a2)
    | (x_a :: l, []) => (fn () => (op_list_prepend x_a l))
    | (x_a :: l, x_b :: l_a) =>
      (fn () =>
        let
          val xa =
            perfect_shared_term_order_rel_s_impl ai (fst x_a) (fst x_b) ();
        in
          (if not (equal_ordered xa GREATER)
            then (fn f_ => fn () => f_
                   ((mergeR_vars_impl_0 ai (l, op_list_prepend x_b l_a)) ()) ())
                   (fn x_d => (fn () => (op_list_prepend x_a x_d)))
            else (fn f_ => fn () => f_
                   ((mergeR_vars_impl_0 ai (op_list_prepend x_a l, l_a)) ()) ())
                   (fn x_d => (fn () => (op_list_prepend x_b x_d))))
            ()
        end));

fun mergeR_vars_impl x =
  (fn ai => fn bia => fn bi => mergeR_vars_impl_0 ai (bia, bi)) x;

fun msortR_vars_impl_0 ai x =
  (if less_eq_nat (op_list_length x) one_nat then (fn () => x)
    else (fn () =>
           let
             val x_e =
               msortR_vars_impl_0 ai
                 (take (divide_nat (op_list_length x)
                         (nat_of_integer (2 : IntInf.int)))
                   x)
                 ();
             val xa =
               msortR_vars_impl_0 ai
                 (drop (divide_nat (op_list_length x)
                         (nat_of_integer (2 : IntInf.int)))
                   x)
                 ();
           in
             mergeR_vars_impl ai x_e xa ()
           end));

fun msortR_vars_impl x = msortR_vars_impl_0 x;

fun mult_monoms_s_impl_0 ai x =
  let
    val (a1, a2) = x;
  in
    (if is_Nil a1 then (fn () => a2)
      else (if is_Nil a2 then (fn () => a1)
             else (fn () =>
                    let
                      val x_c =
                        perfect_shared_var_order_s_impl ai (op_list_hd a1)
                          (op_list_hd a2) ();
                    in
                      (if equal_ordered x_c EQUAL
                        then (fn f_ => fn () => f_
                               ((mult_monoms_s_impl_0 ai
                                  (op_list_tl a1, op_list_tl a2))
                               ()) ())
                               (fn x_e =>
                                 (fn () =>
                                   (op_list_prepend (op_list_hd a1) x_e)))
                        else (if equal_ordered x_c LESS
                               then (fn f_ => fn () => f_
                                      ((mult_monoms_s_impl_0 ai
 (op_list_tl a1, a2))
                                      ()) ())
                                      (fn x_f =>
(fn () => (op_list_prepend (op_list_hd a1) x_f)))
                               else (fn f_ => fn () => f_
                                      ((mult_monoms_s_impl_0 ai
 (a1, op_list_tl a2))
                                      ()) ())
                                      (fn x_f =>
(fn () => (op_list_prepend (op_list_hd a2) x_f)))))
                        ()
                    end)))
  end;

fun mult_monoms_s_impl x =
  (fn ai => fn bia => fn bi => mult_monoms_s_impl_0 ai (bia, bi)) x;

fun mult_term_s_impl x =
  (fn ai => fn bib => fn bia => fn bi =>
    let
      val (a1, a2) = bia;
    in
      imp_nfoldli bib (fn _ => (fn () => true))
        (fn xa => fn sigma =>
          let
            val (a1a, a2a) = xa;
          in
            (fn () => let
                        val x_a = mult_monoms_s_impl ai a1 a1a ();
                      in
                        op_list_prepend (x_a, times_int a2 a2a) sigma
                      end)
          end)
        bi
    end)
    x;

fun mult_poly_s_impl x =
  (fn ai => fn bia => fn bi =>
    imp_nfoldli bia (fn _ => (fn () => true)) (mult_term_s_impl ai bi) [])
    x;

fun alloc_failed Allocated = false
  | alloc_failed Mem_Out = true;

fun insert_variable_c_impl x =
  (fn ai => fn bia => fn (a1, a2) => fn () =>
    let
      val xa = arl_append (default_literal, heap_literal) a1 ai ();
      val x_a =
        ht_update (equal_literal, hashable_literal, heap_literal) heap_uint64 ai
          bia a2 ();
    in
      (xa, x_a)
    end)
    x;

fun import_variable_c_impl x =
  (fn ai => fn bi => fn () =>
    let
      val a = find_new_idx_c_impl bi ();
    in
      let
        val (a1, a2) = a;
      in
        (if alloc_failed a1 then (fn () => (a1, (bi, a2)))
          else (fn f_ => fn () => f_ ((insert_variable_c_impl ai a2 bi) ()) ())
                 (fn xa => (fn () => (Allocated, (xa, a2)))))
      end
        ()
    end)
    x;

fun is_new_variable_c_impl x =
  (fn ai => fn (_, a2) => fn () =>
    let
      val xa =
        ht_lookup (equal_literal, hashable_literal, heap_literal) heap_uint64 ai
          a2 ();
    in
      not (not (is_None xa))
    end)
    x;

fun import_monomS_impl x =
  (fn ai => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, (a1a, (_, _))) =>
            (fn () => (not (alloc_failed a1) andalso not (null a1a))))
          (fn (_, (a1a, (a1b, a2b))) =>
            let
              val x_a = op_list_hd a1a;
            in
              (fn f_ => fn () => f_ ((is_new_variable_c_impl x_a a2b) ()) ())
                (fn x_c =>
                  (if x_c
                    then (fn f_ => fn () => f_ ((import_variable_c_impl x_a a2b)
                           ()) ())
                           (fn (a1c, (a1d, a2d)) =>
                             (fn () =>
                               (if alloc_failed a1c
                                 then (a1c, (a1a, (a1b, a1d)))
                                 else (a1c,
(op_list_tl a1a, (op_list_prepend a2d a1b, a1d))))))
                    else (fn f_ => fn () => f_ ((get_var_pos_c_impl a2b x_a) ())
                           ())
                           (fn x_d =>
                             (fn () =>
                               (Allocated,
                                 (op_list_tl a1a,
                                   (op_list_prepend x_d a1b, a2b)))))))
            end)
          (Allocated, (bi, ([], ai))) ();
    in
      let
        val (a1, (_, (a1b, a2b))) = a;
      in
        (fn () => (a1, (op_list_rev a1b, a2b)))
      end
        ()
    end)
    x;

fun import_polyS_impl x =
  (fn ai => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, (a1a, (_, _))) =>
            (fn () => (not (alloc_failed a1) andalso not (null a1a))))
          (fn (_, (a1a, (a1b, a2b))) =>
            let
              val (a1c, a2c) = op_list_hd a1a;
            in
              (fn f_ => fn () => f_ ((import_monomS_impl a2b a1c) ()) ())
                (fn (a1d, (a1e, a2e)) =>
                  (fn () =>
                    (if alloc_failed a1d then (a1d, (a1a, (a1b, a2e)))
                      else (a1d, (op_list_tl a1a,
                                   (op_list_prepend (a1e, a2c) a1b, a2e))))))
            end)
          (Allocated, (bi, ([], ai))) ();
    in
      let
        val (a1, (_, (a1b, a2b))) = a;
      in
        (fn () => (a1, (op_list_rev a1b, a2b)))
      end
        ()
    end)
    x;

fun merge_coeff_s_impl_0 ai x =
  (case x of ([], a2) => (fn () => a2)
    | (x_a :: l, []) => (fn () => (op_list_prepend x_a l))
    | (x_a :: l, x_b :: l_a) =>
      (fn () =>
        let
          val xa = get_var_name_c_impl ai x_a ();
          val xaa = get_var_name_c_impl ai x_b ();
        in
          (if ((x_a : Uint64.uint64) = x_b) orelse ((xa : string) < xaa)
            then (fn f_ => fn () => f_
                   ((merge_coeff_s_impl_0 ai (l, op_list_prepend x_b l_a)) ())
                   ())
                   (fn x_d => (fn () => (op_list_prepend x_a x_d)))
            else (fn f_ => fn () => f_
                   ((merge_coeff_s_impl_0 ai (op_list_prepend x_a l, l_a)) ())
                   ())
                   (fn x_d => (fn () => (op_list_prepend x_b x_d))))
            ()
        end));

fun merge_coeff_s_impl x =
  (fn ai => fn _ => fn bia => fn bi => merge_coeff_s_impl_0 ai (bia, bi)) x;

fun msort_coeff_s_impl_0 ai bi x =
  (if less_eq_nat (op_list_length x) one_nat then (fn () => x)
    else (fn () =>
           let
             val x_g =
               msort_coeff_s_impl_0 ai bi
                 (take (divide_nat (op_list_length x)
                         (nat_of_integer (2 : IntInf.int)))
                   x)
                 ();
             val xa =
               msort_coeff_s_impl_0 ai bi
                 (drop (divide_nat (op_list_length x)
                         (nat_of_integer (2 : IntInf.int)))
                   x)
                 ();
           in
             merge_coeff_s_impl ai bi x_g xa ()
           end));

fun msort_coeff_s_impl x = (fn ai => fn bi => msort_coeff_s_impl_0 ai bi bi) x;

fun merge_coeffs_s_impl_0 x =
  (case x of [] => (fn () => []) | [(_, _)] => (fn () => x)
    | (a1, a2) :: (a1a, a2a) :: l_a =>
      (if equal_lista equal_uint64 a1 a1a
        then (if not (equal_inta (plus_int a2 a2a) zero_int)
               then merge_coeffs_s_impl_0
                      (op_list_prepend (a1, plus_int a2 a2a) l_a)
               else merge_coeffs_s_impl_0 l_a)
        else (fn () =>
               let
                 val x_c =
                   merge_coeffs_s_impl_0 (op_list_prepend (a1a, a2a) l_a) ();
               in
                 op_list_prepend (a1, a2) x_c
               end)));

fun merge_coeffs_s_impl x = merge_coeffs_s_impl_0 x;

fun check_linear_combi_l_s_mult_err_impl A_ B_ x p =
  [Chara (true, false, true, false, true, false, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, false, false, false, true, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, true, false, true, true, false),
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
    Chara (true, true, false, false, false, false, true, false),
    Chara (false, false, true, true, false, false, true, false),
    Chara (false, false, false, false, false, true, false, false)] @
    shows_prec_list (show_prod (show_list show_nat) B_) zero_nata
      (map (fn (a, b) => (map nat_of_uint64 a, b)) p) [] @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (true, false, true, false, true, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_prec_list (show_prod (show_list show_nat) A_) zero_nata
          (map (fn (a, b) => (map nat_of_uint64 a, b)) x) [];

fun check_linear_combi_l_pre_err_impl i pd p mem =
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
           Chara (true, false, false, true, false, true, true, false),
           Chara (true, false, false, false, false, true, true, false),
           Chara (false, false, true, true, false, true, true, false),
           Chara (false, false, false, false, false, true, false, false),
           Chara (true, true, true, false, true, true, true, false),
           Chara (true, false, false, true, false, true, true, false),
           Chara (false, false, true, false, true, true, true, false),
           Chara (false, false, false, true, false, true, true, false),
           Chara (false, false, false, false, false, true, false, false),
           Chara (true, false, false, true, false, true, true, false),
           Chara (false, false, true, false, false, true, true, false),
           Chara (false, false, false, false, false, true, false, false)] @
           shows_prec_nat zero_nata (nat_of_uint64 i) [] @
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
    (if p then [Chara (false, false, true, false, true, false, true, false),
                 Chara (false, false, false, true, false, true, true, false),
                 Chara (true, false, true, false, false, true, true, false),
                 Chara (false, false, false, false, false, true, false, false),
                 Chara (true, true, false, false, false, true, true, false),
                 Chara (true, true, true, true, false, true, true, false),
                 Chara (true, false, true, true, false, true, false, false),
                 Chara (false, true, true, false, false, true, true, false),
                 Chara (true, false, false, false, false, true, true, false),
                 Chara (true, true, false, false, false, true, true, false),
                 Chara (false, false, true, false, true, true, true, false),
                 Chara (true, true, true, true, false, true, true, false),
                 Chara (false, true, false, false, true, true, true, false),
                 Chara (false, false, false, false, false, true, false, false),
                 Chara (false, true, true, false, false, true, true, false),
                 Chara (false, true, false, false, true, true, true, false),
                 Chara (true, true, true, true, false, true, true, false),
                 Chara (true, false, true, true, false, true, true, false),
                 Chara (false, false, false, false, false, true, false,
                         false)] @
                 shows_prec_nat zero_nata (nat_of_uint64 i) [] @
                   [Chara (false, false, false, false, false, true, false,
                            false),
                     Chara (true, true, true, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (true, true, false, false, true, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (true, false, true, true, false, true, true, false),
                     Chara (false, false, false, false, true, true, true,
                             false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, false, true, true, true, true, false)]
      else []) @
      (if mem
        then [Chara (true, false, true, true, false, false, true, false),
               Chara (true, false, true, false, false, true, true, false),
               Chara (true, false, true, true, false, true, true, false),
               Chara (true, true, true, true, false, true, true, false),
               Chara (false, true, false, false, true, true, true, false),
               Chara (true, false, false, true, true, true, true, false),
               Chara (false, false, false, false, false, true, false, false),
               Chara (true, true, true, true, false, true, true, false),
               Chara (true, false, true, false, true, true, true, false),
               Chara (false, false, true, false, true, true, true, false),
               Chara (false, false, false, false, false, true, false, false),
               Chara (true, true, true, true, false, true, true, false),
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
               Chara (true, false, true, false, false, true, true, false)]
        else []);

fun check_linear_combi_l_s_dom_err_impl x p =
  [Chara (false, false, false, false, true, false, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
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
    Chara (true, true, false, false, false, false, true, false),
    Chara (false, false, true, true, false, false, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, true, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false)] @
    shows_prec_nat zero_nata (nat_of_uint64 p) [];

fun import_monom_no_newS_impl x =
  (fn ai => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, (a1a, _)) => (fn () => (not a1 andalso not (null a1a))))
          (fn (_, (a1a, a2a)) =>
            let
              val x_a = op_list_hd a1a;
            in
              (fn f_ => fn () => f_ ((is_new_variable_c_impl x_a ai) ()) ())
                (fn x_c =>
                  (if x_c then (fn () => (true, (op_list_tl a1a, a2a)))
                    else (fn f_ => fn () => f_ ((get_var_pos_c_impl ai x_a) ())
                           ())
                           (fn x_d =>
                             (fn () =>
                               (false,
                                 (op_list_tl a1a, op_list_prepend x_d a2a))))))
            end)
          (false, (bi, [])) ();
    in
      let
        val (a1, (_, a2a)) = a;
      in
        (fn () => (a1, op_list_rev a2a))
      end
        ()
    end)
    x;

fun import_poly_no_newS_impl x =
  (fn ai => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, (a1a, _)) => (fn () => (not a1 andalso not (null a1a))))
          (fn (_, (a1a, a2a)) =>
            let
              val (a1b, a2b) = op_list_hd a1a;
            in
              (fn f_ => fn () => f_ ((import_monom_no_newS_impl ai a1b) ()) ())
                (fn (a1c, a2c) =>
                  (fn () =>
                    (if a1c then (true, (op_list_tl a1a, a2a))
                      else (false,
                             (op_list_tl a1a,
                               op_list_prepend (a2c, a2b) a2a)))))
            end)
          (false, (bi, [])) ();
    in
      let
        val (a1, (_, a2a)) = a;
      in
        (fn () => (a1, op_list_rev a2a))
      end
        ()
    end)
    x;

fun normalize_poly_sharedS_impl x =
  (fn ai => fn bi => fn () => let
                                val xa = fully_normalize_poly_impl bi ();
                              in
                                import_poly_no_newS_impl ai xa ()
                              end)
    x;

fun normalize_poly_s_impl x =
  (fn ai => fn bi => fn () => let
                                val xa = msortR_vars_impl ai bi ();
                              in
                                merge_coeffs_s_impl xa ()
                              end)
    x;

fun mult_poly_full_s_impl x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = mult_poly_s_impl ai bia bi ();
    in
      normalize_poly_s_impl ai xa ()
    end)
    x;

fun vars_llist_in_s_impl_0 ai x =
  (case x of [] => (fn () => true)
    | x_a :: l_a =>
      (fn () =>
        let
          val x_b = is_new_variable_c_impl x_a ai ();
        in
          (if x_b then (fn () => false) else vars_llist_in_s_impl_0 ai l_a) ()
        end));

fun vars_llist_in_s_impl_1 ai x =
  (case x of [] => (fn () => true)
    | (a1, _) :: l =>
      (fn () =>
        let
          val x_a = vars_llist_in_s_impl_0 ai a1 ();
        in
          (if not x_a then (fn () => false) else vars_llist_in_s_impl_1 ai l) ()
        end));

fun vars_llist_in_s_impl x = vars_llist_in_s_impl_1 x;

fun add_poly_l_prep_impl_0 ai x =
  (case x
    of ([], a2) =>
      (fn () => (case a2 of [] => [] | a :: b => op_list_prepend a b))
    | ((a1a, a2a) :: l, []) => (fn () => (op_list_prepend (a1a, a2a) l))
    | ((a1a, a2a) :: l, (a1b, a2b) :: l_a) =>
      (fn () =>
        let
          val x_b = perfect_shared_term_order_rel_s_impl ai a1a a1b ();
        in
          (if equal_ordered x_b EQUAL
            then (if equal_inta (plus_int a2a a2b) zero_int
                   then add_poly_l_prep_impl_0 ai (l, l_a)
                   else (fn f_ => fn () => f_
                          ((add_poly_l_prep_impl_0 ai (l, l_a)) ()) ())
                          (fn x_e =>
                            (fn () =>
                              (op_list_prepend (a1a, plus_int a2a a2b) x_e))))
            else (if equal_ordered x_b LESS
                   then (fn f_ => fn () => f_
                          ((add_poly_l_prep_impl_0 ai
                             (l, op_list_prepend (a1b, a2b) l_a))
                          ()) ())
                          (fn x_e =>
                            (fn () => (op_list_prepend (a1a, a2a) x_e)))
                   else (fn f_ => fn () => f_
                          ((add_poly_l_prep_impl_0 ai
                             (op_list_prepend (a1a, a2a) l, l_a))
                          ()) ())
                          (fn x_e =>
                            (fn () => (op_list_prepend (a1b, a2b) x_e)))))
            ()
        end));

fun add_poly_l_prep_impl x = add_poly_l_prep_impl_0 x;

fun linear_combi_l_prep_s_impl x =
  (fn _ => fn bib => fn bia => fn bi =>
    heap_WHILET
      (fn (_, (a1a, a2a)) =>
        (fn () =>
          (not (case a1a of [] => true | _ :: _ => false) andalso
            not (is_cfailed a2a))))
      (fn (a1, (a1a, _)) =>
        let
          val (a1b, a2b) = op_list_hd a1a;
        in
          (fn () =>
            let
              val xa =
                ht_lookup (equal_uint64, hashable_uint64, heap_uint64)
                  (heap_list (heap_prod (heap_list heap_uint64) heap_int)) a2b
                  bib ();
              val xaa = vars_llist_in_s_impl bia a1b ();
            in
              (if not (not (is_None xa)) orelse not xaa
                then (fn () =>
                       (a1, (a1a, error_msg show_nat (nat_of_uint64 a2b)
                                    (check_linear_combi_l_s_dom_err_impl a1
                                      a2b))))
                else (fn f_ => fn () => f_
                       ((ht_lookup (equal_uint64, hashable_uint64, heap_uint64)
                          (heap_list
                            (heap_prod (heap_list heap_uint64) heap_int))
                          a2b bib)
                       ()) ())
                       (fn xb =>
                         let
                           val x_d = the xb;
                         in
                           (if equal_lista
                                 (equal_prod (equal_list equal_literal)
                                   equal_int)
                                 a1b (op_list_prepend ([], one_int) [])
                             then (fn f_ => fn () => f_
                                    ((add_poly_l_prep_impl bia (a1, x_d)) ())
                                    ())
                                    (fn x_g =>
                                      (fn () =>
(x_g, (op_list_tl a1a, CSUCCESS))))
                             else (fn f_ => fn () => f_
                                    ((normalize_poly_sharedS_impl bia a1b) ())
                                    ())
                                    (fn (_, a2c) =>
                                      (fn f_ => fn () => f_
((mult_poly_full_s_impl bia a2c x_d) ()) ())
(fn x_h =>
  (fn f_ => fn () => f_ ((add_poly_l_prep_impl bia (a1, x_h)) ()) ())
    (fn x_i => (fn () => (x_i, (op_list_tl a1a, CSUCCESS)))))))
                         end))
                ()
            end)
        end)
      ([], (bi, CSUCCESS)))
    x;

fun weak_equality_l_s_impl x =
  (fn ai => fn bi =>
    (fn () =>
      (equal_lista (equal_prod (equal_list equal_uint64) equal_int) ai bi)))
    x;

fun check_linear_combi_l_s_impl x =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val a = import_poly_no_newS_impl bic bi ();
    in
      let
        val (a1, a2) = a;
      in
        (fn f_ => fn () => f_
          ((ht_lookup (equal_uint64, hashable_uint64, heap_uint64)
             (heap_list (heap_prod (heap_list heap_uint64) heap_int)) bib bid)
          ()) ())
          (fn xa =>
            (if a1 orelse (not (is_None xa) orelse op_list_is_empty bia)
              then (fn f_ => fn () => f_
                     ((ht_lookup (equal_uint64, hashable_uint64, heap_uint64)
                        (heap_list (heap_prod (heap_list heap_uint64) heap_int))
                        bib bid)
                     ()) ())
                     (fn xb =>
                       (fn () =>
                         (error_msg show_nat (nat_of_uint64 bib)
                            (check_linear_combi_l_pre_err_impl bib
                              (not (is_None xb)) (op_list_is_empty bia) a1),
                           a2)))
              else (fn f_ => fn () => f_
                     ((linear_combi_l_prep_s_impl bib bid bic bia) ()) ())
                     (fn (a1a, (_, a2b)) =>
                       (if is_cfailed a2b then (fn () => (a2b, a2))
                         else (fn f_ => fn () => f_
                                ((weak_equality_l_s_impl a1a a2) ()) ())
                                (fn x_d =>
                                  (fn f_ => fn () => f_
                                    ((weak_equality_l_s_impl a2 ai) ()) ())
                                    (fn x_e =>
                                      (fn () =>
(if x_d then (if x_e then (CFOUND, a2) else (CSUCCESS, a2))
  else (error_msg show_nat (nat_of_uint64 bib)
          (check_linear_combi_l_s_mult_err_impl show_int show_int a1a a2),
         a2)))))))))
      end
        ()
    end)
    x;

fun check_extension_l_s_new_var_multiple_err_impl A_ x p =
  [Chara (false, true, true, false, true, false, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, true, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, true, true, false, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false)] @
    shows_prec_literal zero_nata x [] @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (true, false, true, false, true, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_prec_list (show_prod (show_list show_nat) A_) zero_nata
          (map (fn (a, b) => (map nat_of_uint64 a, b)) p) [];

fun check_extension_l_s_side_cond_err_impl A_ B_ C_ x pa p q =
  [Chara (false, false, false, false, true, true, true, false),
    Chara (false, true, true, true, true, false, true, false),
    Chara (false, true, false, false, true, true, false, false),
    Chara (true, false, true, true, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, false, false, true, false, false),
    Chara (true, false, true, true, true, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, true, true, false, false),
    Chara (false, false, false, false, false, true, false, false)] @
    shows_prec_literal zero_nata x [] @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (true, false, true, false, true, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_prec_list (show_prod (show_list show_nat) A_) zero_nata
          (map (fn (a, b) => (map nat_of_uint64 a, b)) pa) [] @
          [Chara (false, false, false, false, false, true, false, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false)] @
            shows_prec_list (show_prod (show_list show_nat) B_) zero_nata
              (map (fn (a, b) => (map nat_of_uint64 a, b)) p) [] @
              [Chara (false, false, false, false, false, true, false, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (false, false, true, false, false, true, true, false),
                Chara (false, false, false, false, false, true, false, false)] @
                shows_prec_list (show_prod (show_list show_nat) C_) zero_nata
                  (map (fn (a, b) => (map nat_of_uint64 a, b)) q) [];

fun check_extension_l_impl x =
  (fn _ => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = is_new_variable_c_impl bia bic ();
      val x_a =
        ht_lookup (equal_uint64, hashable_uint64, heap_uint64)
          (heap_list (heap_prod (heap_list heap_uint64) heap_int)) bib bid ();
      val x_f = vars_llist_in_s_impl bic bi ();
      val a = import_polyS_impl bic bi ();
    in
      let
        val (a1, (a1a, a2a)) = a;
      in
        (if not (is_None x_a andalso xa andalso not (alloc_failed a1))
          then (fn () =>
                 (error_msg show_nat (nat_of_uint64 bib)
                    (check_ext_l_dom_err_impl bib),
                   ([], (a2a, Uint64.zero))))
          else (if not x_f
                 then (fn () =>
                        (error_msg show_nat (nat_of_uint64 bib)
                           (check_extension_l_s_new_var_multiple_err_impl
                             show_int bia a1a),
                          ([], (a2a, Uint64.zero))))
                 else (fn f_ => fn () => f_ ((import_variable_c_impl bia a2a)
                        ()) ())
                        (fn (a1b, (a1c, a2c)) =>
                          (if alloc_failed a1b
                            then (fn () =>
                                   (error_msg show_nat (nat_of_uint64 bib)
                                      (check_ext_l_dom_err_impl bib),
                                     ([], (a1c, Uint64.zero))))
                            else (fn f_ => fn () => f_
                                   ((mult_poly_full_s_impl a1c a1a a1a) ()) ())
                                   (fn x_o =>
                                     let
                                       val x_p = uminus_poly uminus_int a1a;
                                     in
                                       (fn f_ => fn () => f_
 ((add_poly_l_prep_impl a1c (x_o, x_p)) ()) ())
 (fn x_r =>
   (fn f_ => fn () => f_ ((weak_equality_l_s_impl x_r []) ()) ())
     (fn x_s =>
       (fn () =>
         (if x_s then (CSUCCESS, (a1a, (a1c, a2c)))
           else (error_msg show_nat (nat_of_uint64 bib)
                   (check_extension_l_s_side_cond_err_impl show_int show_int
                     show_int bia a1a x_p x_r),
                  ([], (a1c, a2c)))))))
                                     end)))))
      end
        ()
    end)
    x;

fun pAC_checker_l_step_s_impl x =
  (fn ai => fn bia => fn bi =>
    let
      val (a1, (a1a, a2a)) = bia;
    in
      (if is_CL bi
        then (fn () =>
               let
                 val x_a = fully_normalize_poly_impl (pac_res bi) ();
                 val a =
                   check_linear_combi_l_s_impl ai a2a a1a (new_id bi)
                     (pac_srcs bi) x_a ();
               in
                 let
                   val (a1b, a2b) = a;
                 in
                   (if not (is_cfailed a1b)
                     then (fn f_ => fn () => f_
                            ((ht_update
                               (equal_uint64, hashable_uint64, heap_uint64)
                               (heap_list
                                 (heap_prod (heap_list heap_uint64) heap_int))
                               (new_id bi) a2b a2a)
                            ()) ())
                            (fn xa =>
                              (fn () => (merge_cstatus a1 a1b, (a1a, xa))))
                     else (fn () => (a1b, (a1a, a2a))))
                 end
                   ()
               end)
        else (if is_Extension bi
               then (fn () =>
                      let
                        val x_b = fully_normalize_poly_impl (pac_res bi) ();
                        val a =
                          check_extension_l_impl ai a2a a1a (new_id bi)
                            (new_var bi) x_b ();
                      in
                        let
                          val (a1b, (a1c, (a1d, a2d))) = a;
                        in
                          (if not (is_cfailed a1b)
                            then (fn f_ => fn () => f_
                                   ((add_poly_l_prep_impl a1d
                                      (op_list_prepend
 (op_list_prepend a2d [], uminus_inta one_int) [],
a1c))
                                   ()) ())
                                   (fn x_e =>
                                     (fn f_ => fn () => f_
                                       ((ht_update
  (equal_uint64, hashable_uint64, heap_uint64)
  (heap_list (heap_prod (heap_list heap_uint64) heap_int)) (new_id bi) x_e a2a)
                                       ()) ())
                                       (fn xa => (fn () => (a1, (a1d, xa)))))
                            else (fn () => (a1b, (a1d, a2a))))
                        end
                          ()
                      end)
               else (fn () =>
                      let
                        val x_b = check_del_l_impl ai a2a (pac_src1 bi) ();
                      in
                        (if not (is_cfailed x_b)
                          then (fn f_ => fn () => f_
                                 ((ht_delete
                                    (equal_uint64, hashable_uint64, heap_uint64)
                                    (heap_list
                                      (heap_prod (heap_list heap_uint64)
heap_int))
                                    (pac_src1 bi) a2a)
                                 ()) ())
                                 (fn xa =>
                                   (fn () => (merge_cstatus a1 x_b, (a1a, xa))))
                          else (fn () => (x_b, (a1a, a2a))))
                          ()
                      end)))
    end)
    x;

fun pAC_checker_l_s_impl x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn () =>
              let
                val (a1a, _) = a1;
              in
                not (is_cfailed a1a) andalso
                  not (case a2 of [] => true | _ :: _ => false)
              end))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((pAC_checker_l_step_s_impl ai a1 (op_list_hd a2)) ()) ())
              (fn x_a => (fn () => (x_a, op_list_tl a2))))
          ((bia, bib), bi) ();
    in
      let
        val (a1, _) = a;
      in
        (fn () => a1)
      end
        ()
    end)
    x;

fun merge_coeffs0_s_impl_0 x =
  (case x of [] => (fn () => [])
    | [xa] =>
      (fn () =>
        (if equal_inta (snd xa) zero_int then [] else op_list_prepend xa []))
    | xa :: x_a :: l_a =>
      let
        val (a1, a2) = xa;
        val (a1a, a2a) = x_a;
      in
        (if equal_lista equal_uint64 a1 a1a
          then (if not (equal_inta (plus_int a2 a2a) zero_int)
                 then merge_coeffs0_s_impl_0
                        (op_list_prepend (a1, plus_int a2 a2a) l_a)
                 else merge_coeffs0_s_impl_0 l_a)
          else (if equal_inta a2 zero_int
                 then merge_coeffs0_s_impl_0 (op_list_prepend x_a l_a)
                 else (fn () =>
                        let
                          val x_h =
                            merge_coeffs0_s_impl_0 (op_list_prepend x_a l_a) ();
                        in
                          op_list_prepend xa x_h
                        end)))
      end);

fun merge_coeffs0_s_impl x = merge_coeffs0_s_impl_0 x;

val empty_shared_vars_int_impl :
  (unit -> ((string array * nat) * (string, Uint64.uint64) hashtable))
  = (fn () =>
      let
        val x = arl_empty (default_literal, heap_literal) zero_nat ();
        val x_a = ht_new (hashable_literal, heap_literal) heap_uint64 ();
      in
        (x, x_a)
      end);

fun sort_all_coeffs_s_impl x =
  (fn ai => fn bi =>
    imp_nfoldli bi (fn _ => (fn () => true))
      (fn xa => fn sigma =>
        let
          val (a1, a2) = xa;
        in
          (fn () => let
                      val x_b = msort_coeff_s_impl ai a1 ();
                    in
                      op_list_prepend (x_b, a2) sigma
                    end)
        end)
      [])
    x;

fun full_normalize_poly_impl x =
  (fn ai => fn bi => fn () => let
                                val xa = sort_all_coeffs_s_impl ai bi ();
                                val xb = msortR_vars_impl ai xa ();
                              in
                                merge_coeffs0_s_impl xb ()
                              end)
    x;

fun import_variablesS_impl x =
  (fn ai => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, (_, a2a)) =>
            (fn () =>
              (not (alloc_failed a1) andalso not (op_list_is_empty a2a))))
          (fn (_, (a1a, a2a)) =>
            let
              val x_a = op_list_hd a2a;
            in
              (fn f_ => fn () => f_ ((is_new_variable_c_impl x_a a1a) ()) ())
                (fn x_c =>
                  (if not x_c then (fn () => (Allocated, (a1a, op_list_tl a2a)))
                    else (fn f_ => fn () => f_ ((import_variable_c_impl x_a a1a)
                           ()) ())
                           (fn (a1b, (a1c, _)) =>
                             (fn () => (a1b, (a1c, op_list_tl a2a))))))
            end)
          (Allocated, (bi, ai)) ();
    in
      let
        val (a1, (a1a, _)) = a;
      in
        (fn () => (a1, a1a))
      end
        ()
    end)
    x;

fun remap_polys_l2_with_err_s_impl x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val xa =
        len (heap_option
              (heap_list (heap_prod (heap_list heap_literal) heap_int)))
          bia ();
      val a = import_variablesS_impl (vars_llist_s2 bib) bi ();
    in
      let
        val (a1, a2) = a;
      in
        (fn f_ => fn () => f_
          ((if not (alloc_failed a1) then import_polyS_impl a2 ai
             else (fn () => (a1, ([], a2))))
          ()) ())
          (fn (a1a, (a1b, a2b)) =>
            (if alloc_failed a1 orelse
                  (alloc_failed a1a orelse
                    less_eq_nat
                      (nat_of_integer (18446744073709551616 : IntInf.int)) xa)
              then (fn f_ => fn () => f_
                     ((ht_new (hashable_uint64, heap_uint64)
                        (heap_list
                          (heap_prod (heap_list heap_uint64) heap_int)))
                     ()) ())
                     (fn xb =>
                       (fn () =>
                         (error_msg show_nat zero_nata
                            remap_polys_l_dom_err_impl,
                           (a2b, (xb, [])))))
              else (fn f_ => fn () => f_
                     ((ht_new (hashable_uint64, heap_uint64)
                        (heap_list
                          (heap_prod (heap_list heap_uint64) heap_int)))
                     ()) ())
                     (fn xaa =>
                       (fn f_ => fn () => f_
                         ((heap_WHILET
                            (fn (a1c, a2c) =>
                              (fn () =>
                                (less_nat a1c xa andalso
                                  let
                                    val (a1d, (_, _)) = a2c;
                                  in
                                    not (is_cfailed a1d)
                                  end)))
                            (fn (a1c, a2c) =>
                              (fn f_ => fn () => f_
                                (let
                                   val (a1d, (a1e, a2e)) = a2c;
                                 in
                                   (fn f_ => fn () => f_
                                     ((iam_lookup
(heap_list (heap_prod (heap_list heap_literal) heap_int)) a1c bia)
                                     ()) ())
                                     (fn xb =>
                                       (if not (is_None xb)
 then (fn f_ => fn () => f_
        ((iam_lookup (heap_list (heap_prod (heap_list heap_literal) heap_int))
           a1c bia)
        ()) ())
        (fn xc =>
          (fn f_ => fn () => f_ ((import_polyS_impl a2e (the xc)) ()) ())
            (fn (a1f, (a1g, a2g)) =>
              (if alloc_failed a1f
                then (fn () => (CFAILED memory_out_msg, (a1e, a2g)))
                else (fn f_ => fn () => f_ ((full_normalize_poly_impl a2g a1g)
                       ()) ())
                       (fn x_h =>
                         (fn f_ => fn () => f_ ((weak_equality_l_s_impl x_h a1b)
                           ()) ())
                           (fn x_i =>
                             (fn f_ => fn () => f_
                               ((ht_update
                                  (equal_uint64, hashable_uint64, heap_uint64)
                                  (heap_list
                                    (heap_prod (heap_list heap_uint64)
                                      heap_int))
                                  (uint64_of_nat a1c) x_h a1e)
                               ()) ())
                               (fn xd =>
                                 (fn () =>
                                   ((if x_i then CFOUND else CSUCCESS),
                                     (xd, a2g)))))))))
 else (fn () => (a1d, (a1e, a2e)))))
                                 end
                                ()) ())
                                (fn x_e =>
                                  (fn () => (plus_nat a1c one_nat, x_e))))
                            (zero_nata, (CSUCCESS, (xaa, a2b))))
                         ()) ())
                         (fn xb =>
                           (fn () =>
                             let
                               val (a1c, (a1d, a2d)) = let
                 val (_, b) = xb;
               in
                 b
               end;
                             in
                               (a1c, (a2d, (a1d, a1b)))
                             end)))))
      end
        ()
    end)
    x;

fun full_checker_l_s2_impl x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = fully_normalize_poly_impl ai ();
      val xaa = empty_shared_vars_int_impl ();
      val a = remap_polys_l2_with_err_s_impl xa ai bia xaa ();
    in
      let
        val (a1, (a1a, (a1b, a2b))) = a;
      in
        (if is_cfailed a1 then (fn () => (a1, (a1a, a1b)))
          else pAC_checker_l_s_impl a2b (a1a, a1b) a1 bi)
      end
        ()
    end)
    x;

end; (*struct PAC_Checker*)
