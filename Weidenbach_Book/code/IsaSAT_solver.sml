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

structure SAT_Solver : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  val nat_of_integer : IntInf.int -> nat
  type ('a, 'b) vmtf_node
  type minimize_status
  datatype int = Int_of_integer of IntInf.int
  val version : string
  val integer_of_int : int -> IntInf.int
  val uint32_of_nat : nat -> Word32.word
  val isaSAT_code :
    bool * (bool * bool) ->
      (Word32.word list) list ->
        (unit ->
          ((Word32.word array * nat) option *
            (Uint64.uint64 *
              (Uint64.uint64 *
                (Uint64.uint64 *
                  (Uint64.uint64 * (Uint64.uint64 * Uint64.uint64)))))))
end = struct

datatype typerepa = Typerep of string * typerepa list;

datatype nat = Nat of IntInf.int;

datatype 'a itself = Type;

fun typerep_nata t = Typerep ("Nat.nat", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_nat = {} : nat countable;

val typerep_nat = {typerep = typerep_nata} : nat typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  nat heap;

val zero_nata : nat = Nat (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

val default_nata : nat = zero_nata;

type 'a default = {default : 'a};
val default = #default : 'a default -> 'a;

val default_nat = {default = default_nata} : nat default;

fun integer_of_nat (Nat x) = x;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun minus_nata m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_nat = {minus = minus_nata} : nat minus;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

fun typerep_boola t = Typerep ("HOL.bool", []);

val countable_bool = {} : bool countable;

val typerep_bool = {typerep = typerep_boola} : bool typerep;

val heap_bool = {countable_heap = countable_bool, typerep_heap = typerep_bool} :
  bool heap;

fun typerep_arraya A_ t = Typerep ("Heap.array", [typerep A_ Type]);

val countable_array = {} : ('a array) countable;

fun typerep_array A_ = {typerep = typerep_arraya A_} : ('a array) typerep;

fun heap_array A_ =
  {countable_heap = countable_array, typerep_heap = typerep_array A_} :
  ('a array) heap;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun shows_prec_char p c = (fn a => c :: a);

fun shows_string x = (fn a => x @ a);

fun shows_list_char cs = shows_string cs;

type 'a show =
  {shows_prec : nat -> 'a -> char list -> char list,
    shows_list : 'a list -> char list -> char list};
val shows_prec = #shows_prec : 'a show -> nat -> 'a -> char list -> char list;
val shows_list = #shows_list : 'a show -> 'a list -> char list -> char list;

val show_char = {shows_prec = shows_prec_char, shows_list = shows_list_char} :
  char show;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_uint32 = {equal = (fn a => fn b => ((a : Word32.word) = b))} :
  Word32.word equal;

fun typerep_uint32a t = Typerep ("Uint32.uint32", []);

val countable_uint32 = {} : Word32.word countable;

val typerep_uint32 = {typerep = typerep_uint32a} : Word32.word typerep;

val heap_uint32 =
  {countable_heap = countable_uint32, typerep_heap = typerep_uint32} :
  Word32.word heap;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_uint32 = {one = (Word32.fromInt 1)} : Word32.word one;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_uint32 = {plus = (fn a => fn b => Word32.+ (a, b))} : Word32.word plus;

val zero_uint32 = {zero = (Word32.fromInt 0)} : Word32.word zero;

val default_uint32a : Word32.word = (Word32.fromInt 0);

val default_uint32 = {default = default_uint32a} : Word32.word default;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_uint32 = {plus_semigroup_add = plus_uint32} :
  Word32.word semigroup_add;

val numeral_uint32 =
  {one_numeral = one_uint32, semigroup_add_numeral = semigroup_add_uint32} :
  Word32.word numeral;

val minus_uint32 = {minus = (fn a => fn b => Word32.- (a, b))} :
  Word32.word minus;

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

val times_uint32 = {times = (fn a => fn b => Word32.* (a, b))} :
  Word32.word times;

val ord_uint32 =
  {less_eq = (fn a => fn b => Word32.<= (a, b)),
    less = (fn a => fn b => Word32.< (a, b))}
  : Word32.word ord;

type 'a bit =
  {bitNOT : 'a -> 'a, bitAND : 'a -> 'a -> 'a, bitOR : 'a -> 'a -> 'a,
    bitXOR : 'a -> 'a -> 'a};
val bitNOT = #bitNOT : 'a bit -> 'a -> 'a;
val bitAND = #bitAND : 'a bit -> 'a -> 'a -> 'a;
val bitOR = #bitOR : 'a bit -> 'a -> 'a -> 'a;
val bitXOR = #bitXOR : 'a bit -> 'a -> 'a -> 'a;

val bit_uint64 =
  {bitNOT = Uint64.notb, bitAND = Uint64.andb, bitOR = Uint64.orb,
    bitXOR = Uint64.xorb}
  : Uint64.uint64 bit;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

datatype num = One | Bit0 of num | Bit1 of num;

fun test_bit_uint64 x n =
  less_nat n (nat_of_integer (64 : IntInf.int)) andalso
    Uint64.test_bit x (integer_of_nat n);

fun shiftl_uint64 x n =
  (if less_nat n (nat_of_integer (64 : IntInf.int))
    then Uint64.shiftl x (integer_of_nat n) else Uint64.zero);

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun uint64_set_bits f w n =
  (if equal_nat n zero_nata then w
    else let
           val na = minus_nata n one_nat;
         in
           uint64_set_bits f
             (Uint64.orb (shiftl_uint64 w one_nat)
               (if f na then Uint64.one else Uint64.zero))
             na
         end);

fun set_bits_uint64 f =
  uint64_set_bits f Uint64.zero (nat_of_integer (64 : IntInf.int));

fun set_bit_uint64 x n b =
  (if less_nat n (nat_of_integer (64 : IntInf.int))
    then Uint64.set_bit x (integer_of_nat n) b else x);

fun shiftr_uint64 x n =
  (if less_nat n (nat_of_integer (64 : IntInf.int))
    then Uint64.shiftr x (integer_of_nat n) else Uint64.zero);

fun lsb_uint64 x = test_bit_uint64 x zero_nata;

type 'a bits =
  {bit_bits : 'a bit, test_bit : 'a -> nat -> bool, lsb : 'a -> bool,
    set_bit : 'a -> nat -> bool -> 'a, set_bits : (nat -> bool) -> 'a,
    shiftl : 'a -> nat -> 'a, shiftr : 'a -> nat -> 'a};
val bit_bits = #bit_bits : 'a bits -> 'a bit;
val test_bit = #test_bit : 'a bits -> 'a -> nat -> bool;
val lsb = #lsb : 'a bits -> 'a -> bool;
val set_bit = #set_bit : 'a bits -> 'a -> nat -> bool -> 'a;
val set_bits = #set_bits : 'a bits -> (nat -> bool) -> 'a;
val shiftl = #shiftl : 'a bits -> 'a -> nat -> 'a;
val shiftr = #shiftr : 'a bits -> 'a -> nat -> 'a;

val bits_uint64 =
  {bit_bits = bit_uint64, test_bit = test_bit_uint64, lsb = lsb_uint64,
    set_bit = set_bit_uint64, set_bits = set_bits_uint64,
    shiftl = shiftl_uint64, shiftr = shiftr_uint64}
  : Uint64.uint64 bits;

fun typerep_uint64a t = Typerep ("Uint64.uint64", []);

val countable_uint64 = {} : Uint64.uint64 countable;

val typerep_uint64 = {typerep = typerep_uint64a} : Uint64.uint64 typerep;

val heap_uint64 =
  {countable_heap = countable_uint64, typerep_heap = typerep_uint64} :
  Uint64.uint64 heap;

val one_uint64 = {one = Uint64.one} : Uint64.uint64 one;

val zero_uint64 = {zero = Uint64.zero} : Uint64.uint64 zero;

val default_uint64a : Uint64.uint64 = Uint64.zero;

val default_uint64 = {default = default_uint64a} : Uint64.uint64 default;

val minus_uint64 = {minus = Uint64.minus} : Uint64.uint64 minus;

fun typerep_proda A_ B_ t =
  Typerep ("Product_Type.prod", [typerep A_ Type, typerep B_ Type]);

fun countable_prod A_ B_ = {} : ('a * 'b) countable;

fun typerep_prod A_ B_ = {typerep = typerep_proda A_ B_} : ('a * 'b) typerep;

fun heap_prod A_ B_ =
  {countable_heap = countable_prod (countable_heap A_) (countable_heap B_),
    typerep_heap = typerep_prod (typerep_heap A_) (typerep_heap B_)}
  : ('a * 'b) heap;

fun default_proda A_ B_ = (default A_, default B_);

fun default_prod A_ B_ = {default = default_proda A_ B_} : ('a * 'b) default;

val one_integera : IntInf.int = (1 : IntInf.int);

val one_integer = {one = one_integera} : IntInf.int one;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype ('a, 'b) vmtf_node = VMTF_Node of 'b * 'a option * 'a option;

fun typerep_vmtf_nodea A_ B_ t =
  Typerep
    ("Watched_Literals_VMTF.vmtf_node", [typerep A_ Type, typerep B_ Type]);

fun countable_vmtf_node A_ B_ = {} : ('a, 'b) vmtf_node countable;

fun typerep_vmtf_node A_ B_ = {typerep = typerep_vmtf_nodea A_ B_} :
  ('a, 'b) vmtf_node typerep;

fun heap_vmtf_node A_ B_ =
  {countable_heap = countable_vmtf_node A_ B_,
    typerep_heap = typerep_vmtf_node (typerep_heap A_) (typerep_heap B_)}
  : ('a, 'b) vmtf_node heap;

datatype minimize_status = SEEN_FAILED | SEEN_REMOVABLE | SEEN_UNKNOWN;

fun typerep_minimize_statusa t =
  Typerep ("CDCL_Conflict_Minimisation.minimize_status", []);

val countable_minimize_status = {} : minimize_status countable;

val typerep_minimize_status = {typerep = typerep_minimize_statusa} :
  minimize_status typerep;

val heap_minimize_status =
  {countable_heap = countable_minimize_status,
    typerep_heap = typerep_minimize_status}
  : minimize_status heap;

datatype int = Int_of_integer of IntInf.int;

fun eq A_ a b = equal A_ a b;

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

fun null [] = true
  | null (x :: xs) = false;

fun hd (x21 :: x22) = x21;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

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
    o map (fn k => if 0 <= k andalso k < 128 then (Char.chr o IntInf.toInt) k else raise Fail "Non-ASCII character in literal"))
    (map integer_of_char cs);

fun blit A_ src si dst di len =
  (fn () => 
    array_blit src (integer_of_nat
                     si) dst (integer_of_nat di) (integer_of_nat len));

val version : string = "ee9b81f8";

fun heap_WHILET b f s =
  (fn () =>
    let
      val bv = b s ();
    in
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s))
        ()
    end);

fun nth_u_code A_ = (fn a => fn b => (fn () => Array.sub (a, Word32.toInt b)));

fun get_LBD_code x =
  (fn (a1, a2) => fn () =>
    let
      val a =
        heap_WHILET (fn (a1a, _) => (fn () => (Word32.<= (a1a, a2))))
          (fn (a1a, a2a) =>
            (fn f_ => fn () => f_ ((nth_u_code heap_bool a1 a1a) ()) ())
              (fn xa =>
                (fn () =>
                  (Word32.+ (a1a, (Word32.fromInt 1)),
                    (if xa then Word32.+ (a2a, (Word32.fromInt 1)) else a2a)))))
          ((Word32.fromInt 0), (Word32.fromInt 0)) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun the (SOME x2) = x2;

fun arl_length A_ = (fn (_, a) => (fn () => a));

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun integer_of_int (Int_of_integer k) = k;

fun uint32_of_int i = Word32.fromLargeInt (IntInf.toLarge (integer_of_int i));

fun uint32_of_nat x = (uint32_of_int o int_of_nat) x;

fun length_arl_u_code A_ xs = (fn () => let
  val n = arl_length A_ xs ();
in
  uint32_of_nat n
end);

fun isa_length_trail_fast_code x =
  (fn (a1, (_, (_, (_, (_, _))))) => length_arl_u_code heap_uint32 a1) x;

fun literals_to_update_wl_literals_to_update_wl_empty_fast_code x =
  (fn (a1, (_, (_, (a1c, (_, (_, (_, (_, (_,
   (_, (_, (_, (_, (_, (_, (_, _))))))))))))))))
     =>
    fn () => let
               val xa = isa_length_trail_fast_code a1 ();
             in
               Word32.< (a1c, xa)
             end)
    x;

fun isa_trail_nth_fast_code x =
  (fn ai => fn bi =>
    let
      val (a1, _) = ai;
    in
      (fn () => Array.sub ((fn (a,b) => a) (a1), Word32.toInt (bi)))
    end)
    x;

fun uminus_code l = Word32.xorb (l, (Word32.fromInt 1));

fun select_and_remove_from_literals_to_update_wlfast_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, (a1n, (a1o, a2o))))))))))))))))
     =>
    fn () =>
    let
      val xa = isa_trail_nth_fast_code a1 a1c ();
    in
      ((a1, (a1a, (a1b, (Word32.+ (a1c, (Word32.fromInt 1)),
                          (a1d, (a1e, (a1f,
(a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, (a1n, (a1o, a2o)))))))))))))))),
        uminus_code xa)
    end)
    x;

fun fast_minus A_ m n = minus A_ m n;

fun arl_get_u64 A_ =
  (fn a => fn b =>
    (fn () => Array.sub ((fn (a,b) => a) a, Uint64.toFixedInt b)));

fun arena_status_fast_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        arl_get_u64 heap_uint32 ai
          (fast_minus minus_uint64 bi (Uint64.fromInt (4 : IntInf.int))) ();
    in
      Word32.andb (xa, Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int)))
    end)
    x;

fun clause_not_marked_to_delete_heur_fast_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, _))) = ai;
    in
      (fn () =>
        let
          val xa = arena_status_fast_code a1a bi ();
        in
          not ((xa : Word32.word) = (Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int))))
        end)
    end)
    x;

fun isa_arena_lit_fast_code x = arl_get_u64 heap_uint32 x;

fun polarity_pol_fast_code x =
  (fn ai => fn bi => let
                       val (_, (a1a, (_, _))) = ai;
                     in
                       nth_u_code heap_uint32 a1a bi
                     end)
    x;

fun is_None a = (case a of NONE => true | SOME _ => false);

val sET_FALSE_code : Word32.word =
  Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int));

fun isa_find_unwatched_between_fast_code x =
  (fn ai => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn () => (is_None a1 andalso Uint64.less a2 (Uint64.plus bi bia))))
          (fn (_, a2) =>
            (fn f_ => fn () => f_ ((isa_arena_lit_fast_code bic a2) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_ ((polarity_pol_fast_code ai xa) ()) ())
                  (fn xb =>
                    (fn () =>
                      (if not ((xb : Word32.word) = sET_FALSE_code)
                        then (SOME (Uint64.minus a2 bi), a2)
                        else (NONE, Uint64.plus a2 Uint64.one))))))
          (NONE, Uint64.plus bi bib) ();
    in
      let
        val (a1, _) = a;
      in
        (fn () => a1)
      end
        ()
    end)
    x;

fun uint64_of_uint32 x = (Uint64.fromLarge (Word32.toLarge x));

fun isa_get_saved_pos_fast_code2 x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        arl_get_u64 heap_uint32 ai
          (Uint64.minus bi (Uint64.fromInt (5 : IntInf.int))) ();
    in
      Uint64.plus (uint64_of_uint32 xa) (Uint64.fromInt (2 : IntInf.int))
    end)
    x;

fun isa_arena_length_fast_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = arl_get_u64 heap_uint32 ai (Uint64.minus bi Uint64.one) ();
    in
      Uint64.plus (Uint64.fromInt (2 : IntInf.int)) (uint64_of_uint32 xa)
    end)
    x;

fun find_unwatched_wl_st_heur_fast_code x =
  (fn ai => fn bi =>
    let
      val (a1, (a1a, (_, (_, (_, (_, _)))))) = ai;
    in
      (fn () =>
        let
          val xa = isa_arena_length_fast_code a1a bi ();
          val xaa = isa_arena_length_fast_code a1a bi ();
        in
          (if Uint64.less_eq xaa (Uint64.fromInt (4 : IntInf.int))
            then isa_find_unwatched_between_fast_code a1 a1a
                   (Uint64.fromInt (2 : IntInf.int)) xa bi
            else (fn f_ => fn () => f_ ((isa_get_saved_pos_fast_code2 a1a bi)
                   ()) ())
                   (fn x_c =>
                     (fn f_ => fn () => f_
                       ((isa_find_unwatched_between_fast_code a1 a1a x_c xa bi)
                       ()) ())
                       (fn x_d =>
                         (if is_None x_d
                           then isa_find_unwatched_between_fast_code a1 a1a
                                  (Uint64.fromInt (2 : IntInf.int)) x_c bi
                           else (fn () => x_d)))))
            ()
        end)
    end)
    x;

fun shiftr_uint32 x n =
  (if less_nat n (nat_of_integer (32 : IntInf.int))
    then Uint32.shiftr x (integer_of_nat n) else (Word32.fromInt 0));

fun atm_of_code l = shiftr_uint32 l one_nat;

fun is_in_conflict_code x =
  (fn ai => fn bi =>
    let
      val (_, a2) = ai;
    in
      (fn () => let
                  val xa = nth_u_code heap_bool a2 (atm_of_code bi) ();
                in
                  not (not xa)
                end)
    end)
    x;

fun get_level_atm_fast_code x =
  (fn ai => fn bi => let
                       val (_, (_, (a1b, _))) = ai;
                     in
                       nth_u_code heap_uint32 a1b bi
                     end)
    x;

fun get_level_fast_code x =
  (fn ai => fn bi => get_level_atm_fast_code ai (atm_of_code bi)) x;

fun count_decided_pol x = (fn (_, (_, (_, (_, (k, _))))) => k) x;

fun heap_array_set_ua A_ =
  (fn a => fn b => fn c => (fn () => Array.update (a, (Word32.toInt b), c)));

fun heap_array_set_u A_ a i x =
  (fn () => let
              val _ = heap_array_set_ua A_ a i x ();
            in
              a
            end);

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

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

fun length_u_code A_ = (fn a => (fn () => Word32.fromInt (Array.length a)));

fun nat_of_uint32 x =
  nat_of_integer (IntInf.fromLarge (Word32.toLargeInt x) : IntInf.int);

fun lbd_write_code x =
  (fn ai => fn bia => fn bi =>
    let
      val (a1, a2) = ai;
    in
      (fn () =>
        let
          val xa = length_u_code heap_bool a1 ();
        in
          (if Word32.< (bia, xa)
            then (fn f_ => fn () => f_ ((heap_array_set_u heap_bool a1 bia bi)
                   ()) ())
                   (fn x_a => (fn () => (x_a, max ord_uint32 bia a2)))
            else (fn f_ => fn () => f_
                   ((array_grow heap_bool a1
                      (nat_of_uint32 (Word32.+ (bia, (Word32.fromInt 1))))
                      false)
                   ()) ())
                   (fn xb =>
                     (fn f_ => fn () => f_
                       ((heap_array_set_u heap_bool xb bia bi) ()) ())
                       (fn x_a => (fn () => (x_a, max ord_uint32 bia a2)))))
            ()
        end)
    end)
    x;

fun set_lookup_conflict_aa_fast_code x =
  (fn ai => fn bie => fn bid => fn bic => fn bib => fn bia => fn bi =>
    let
      val (_, a2) = bic;
    in
      (fn () =>
        let
          val a =
            heap_WHILET
              (fn (a1a, (_, (_, (_, _)))) =>
                (fn f_ => fn () => f_ ((isa_arena_length_fast_code bie bid) ())
                  ())
                  (fn xa => (fn () => (Uint64.less a1a (Uint64.plus bid xa)))))
              (fn (a1a, (a1b, (a1c, (a1d, a2d)))) =>
                (fn f_ => fn () => f_ ((isa_arena_lit_fast_code bie a1a) ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((get_level_fast_code ai xa) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((lbd_write_code a1d xb true) ())
                          ())
                          (fn x_a =>
                            (fn f_ => fn () => f_
                              ((isa_arena_lit_fast_code bie a1a) ()) ())
                              (fn xc =>
                                (fn f_ => fn () => f_
                                  ((get_level_fast_code ai xc) ()) ())
                                  (fn xd =>
                                    (fn f_ => fn () => f_
                                      ((isa_arena_lit_fast_code bie a1a) ()) ())
                                      (fn xaa =>
(fn f_ => fn () => f_ ((is_in_conflict_code a1c xaa) ()) ())
  (fn xab =>
    (fn f_ => fn () => f_
      ((if Word32.< (xd, count_decided_pol ai) andalso not xab
         then (fn f_ => fn () => f_ ((isa_arena_lit_fast_code bie a1a) ()) ())
                (arl_append (default_uint32, heap_uint32) a2d)
         else (fn () => a2d))
      ()) ())
      (fn x_c =>
        (fn f_ => fn () => f_ ((isa_arena_lit_fast_code bie a1a) ()) ())
          (fn xe =>
            (fn f_ => fn () => f_ ((get_level_fast_code ai xe) ()) ())
              (fn xf =>
                (fn f_ => fn () => f_ ((isa_arena_lit_fast_code bie a1a) ()) ())
                  (fn xac =>
                    (fn f_ => fn () => f_ ((is_in_conflict_code a1c xac) ()) ())
                      (fn xad =>
                        (fn f_ => fn () => f_
                          (let
                             val (a1e, a2e) = a1c;
                           in
                             (fn f_ => fn () => f_
                               ((isa_arena_lit_fast_code bie a1a) ()) ())
                               (fn xg =>
                                 (fn f_ => fn () => f_
                                   ((nth_u_code heap_bool a2e (atm_of_code xg))
                                   ()) ())
                                   (fn xh =>
                                     (fn f_ => fn () => f_
                                       ((isa_arena_lit_fast_code bie a1a) ())
                                       ())
                                       (fn xae =>
 (fn f_ => fn () => f_ ((isa_arena_lit_fast_code bie a1a) ()) ())
   (fn _ =>
     (fn f_ => fn () => f_
       ((heap_array_set_u heap_bool a2e (atm_of_code xae) true) ()) ())
       (fn x_h =>
         (fn () =>
           ((if not xh then Word32.+ (a1e, (Word32.fromInt 1)) else a1e),
             x_h)))))))
                           end
                          ()) ())
                          (fn x_g =>
                            (fn () =>
                              (Uint64.plus a1a Uint64.one,
                                ((if ((xf : Word32.word) = (count_decided_pol
                     ai)) andalso
                                       not xad
                                   then Word32.+ (a1b, (Word32.fromInt 1))
                                   else a1b),
                                  (x_g, (x_a, x_c)))))))))))))))))))
              (Uint64.plus bid Uint64.zero, (bib, (a2, (bia, bi)))) ();
        in
          let
            val (_, (a1b, (a1c, (a1d, a2d)))) = a;
          in
            (fn () => ((false, a1c), (a1b, (a1d, a2d))))
          end
            ()
        end)
    end)
    x;

fun heap_array_set_u64a A_ =
  (fn a => fn b => fn c => (fn () => Array.update (a, (Word64.toInt b), c)));

fun array_upd_u64 A_ i x a =
  (fn () => let
              val _ = heap_array_set_u64a A_ a i x ();
            in
              a
            end);

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun arl_set_u64 A_ a i x =
  (fn () => let
              val b = array_upd_u64 A_ i x (fst a) ();
            in
              (b, snd a)
            end);

fun isa_arena_incr_act_fast_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        arl_get_u64 heap_uint32 ai
          (Uint64.minus bi (Uint64.fromInt (3 : IntInf.int))) ();
    in
      arl_set_u64 heap_uint32 ai
        (Uint64.minus bi (Uint64.fromInt (3 : IntInf.int)))
        (Word32.+ (xa, (Word32.fromInt 1))) ()
    end)
    x;

fun incr_conflict x =
  (fn (propa, (confl, dec)) => (propa, (Uint64.plus confl Uint64.one, dec))) x;

fun set_conflict_wl_heur_fast_code x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (_, (a1d, (a1e, (a1f,
  (_, (a1h, (a1i, (a1j, (a1k, (a1l, a2l)))))))))))))
      =>
    fn () =>
    let
      val a =
        set_lookup_conflict_aa_fast_code a1 a1a ai a1b (Word32.fromInt 0) a1i
          a1j ();
    in
      let
        val (a1m, (a1n, (a1o, a2o))) = a;
      in
        (fn f_ => fn () => f_ ((isa_arena_incr_act_fast_code a1a ai) ()) ())
          (fn xa =>
            (fn f_ => fn () => f_ ((isa_length_trail_fast_code a1) ()) ())
              (fn xaa =>
                (fn () =>
                  (a1, (xa, (a1m, (xaa, (a1d,
  (a1e, (a1f, (a1n, (a1h, (a1o, (a2o, (incr_conflict a1k,
(a1l, a2l))))))))))))))))
      end
        ()
    end)
    x;

val sET_TRUE_code : Word32.word =
  Word32.fromLargeInt (IntInf.toLarge (2 : IntInf.int));

fun cons_trail_Propagated_tr_fast_code x =
  (fn ai => fn bia => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = arl_append (default_uint32, heap_uint32) a1 ai ();
      val xaa = heap_array_set_u heap_uint32 a1a ai sET_TRUE_code ();
      val xab =
        heap_array_set_u heap_uint32 xaa (uminus_code ai) sET_FALSE_code ();
      val xb = heap_array_set_u heap_uint32 a1b (atm_of_code ai) a1d ();
      val xc = heap_array_set_u heap_uint64 a1c (atm_of_code ai) bia ();
    in
      (xa, (xab, (xb, (xc, (a1d, a2d)))))
    end)
    x;

fun incr_propagation x =
  (fn (propa, (confl, dec)) => (Uint64.plus propa Uint64.one, (confl, dec))) x;

fun is_pos_code l =
  (((Word32.andb (l, (Word32.fromInt 1))) : Word32.word) = (Word32.fromInt 0));

fun incr_uset x =
  (fn (propa, (confl, (dec, (res, (lres, uset))))) =>
    (propa, (confl, (dec, (res, (lres, Uint64.plus uset Uint64.one))))))
    x;

fun propagate_lit_wl_bin_fast_code x =
  (fn ai => fn bib => fn _ =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, a2l)))))))))))))
      =>
    fn () =>
    let
      val x_b = cons_trail_Propagated_tr_fast_code ai bib a1 ();
      val xa =
        heap_array_set_u heap_bool a1f (atm_of_code ai) (is_pos_code ai) ();
    in
      (x_b, (a1a, (a1b, (a1c, (a1d, (a1e, (xa,
    (a1g, (a1h, (a1i, (a1j, (incr_propagation
                               (if (((count_decided_pol
                                       a1) : Word32.word) = (Word32.fromInt 0))
                                 then incr_uset a1k else a1k),
                              (a1l, a2l)))))))))))))
    end)
    x;

fun nth_aa_i32_u64 A_ x la l =
  (fn () =>
    let
      val xa =
        nth_u_code (heap_prod (heap_array (typerep_heap A_)) heap_nat) x la ();
      val xb = arl_get_u64 A_ xa l ();
    in
      xb
    end);

fun watched_by_app_heur_fast_code x =
  (fn ai => fn bia => fn bi =>
    let
      val (_, (_, (_, (_, (a1d, _))))) = ai;
    in
      nth_aa_i32_u64 (heap_prod heap_uint64 heap_uint64) a1d bia bi
    end)
    x;

fun to_watcher_fast_code x =
  (fn a => fn l => fn b =>
    (a, Uint64.orb (uint64_of_uint32 l)
          (if b then shiftl_uint64 Uint64.one (nat_of_integer (32 : IntInf.int))
            else Uint64.zero)))
    x;

fun array_upd_u A_ i x a = (fn () => let
                                       val _ = heap_array_set_ua A_ a i x ();
                                     in
                                       a
                                     end);

fun update_aa_u32_i64 A_ a i j y =
  (fn () =>
    let
      val x =
        nth_u_code (heap_prod (heap_array (typerep_heap A_)) heap_nat) a i ();
      val aa = arl_set_u64 A_ x j y ();
    in
      array_upd_u (heap_prod (heap_array (typerep_heap A_)) heap_nat) i aa a ()
    end);

fun update_blit_wl_heur_fast_code x =
  (fn ai => fn bie => fn bid => fn bic => fn bib => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa =
        update_aa_u32_i64 (heap_prod heap_uint64 heap_uint64) a1d ai bic
          (to_watcher_fast_code bie bia bid) ();
    in
      (Uint64.plus bic Uint64.one,
        (Uint64.plus bib Uint64.one, (a1, (a1a, (a1b, (a1c, (xa, a2d)))))))
    end)
    x;

fun heap_array_set_u64 A_ a i x =
  (fn () => let
              val _ = heap_array_set_u64a A_ a i x ();
            in
              a
            end);

fun nth_u64_code A_ =
  (fn a => fn b => (fn () => Array.sub (a, Uint64.toFixedInt b)));

fun swap_arl_u64 A_ =
  (fn (xs, n) => fn i => fn j => fn () =>
    let
      val ki = nth_u64_code A_ xs i ();
      val kj = nth_u64_code A_ xs j ();
      val xsa = heap_array_set_u64 A_ xs i kj ();
      val xsb = heap_array_set_u64 A_ xsa j ki ();
    in
      (xsb, n)
    end);

fun swap_lits_fast_code x =
  (fn ai => fn bib => fn bia => fn bi =>
    swap_arl_u64 heap_uint32 bi (Uint64.plus ai bib) (Uint64.plus ai bia))
    x;

fun append_el_aa_u (A1_, A2_) =
  (fn a => fn i => fn x => fn () =>
    let
      val j =
        nth_u_code (heap_prod (heap_array (typerep_heap A2_)) heap_nat) a i ();
      val aa = arl_append (A1_, A2_) j x ();
      val _ =
        heap_array_set_ua (heap_prod (heap_array (typerep_heap A2_)) heap_nat) a
          i aa ();
    in
      a
    end);

fun update_clause_wl_fast_code x =
  (fn ai => fn bif => fn bie => fn bid => fn bic => fn bib => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = isa_arena_lit_fast_code a1a (Uint64.plus bif bia) ();
      val x_b = swap_lits_fast_code bif bib bia a1a ();
      val x_d =
        append_el_aa_u
          (default_prod default_uint64 default_uint64,
            heap_prod heap_uint64 heap_uint64)
          a1d xa (to_watcher_fast_code bif ai bie) ();
    in
      (bid, (Uint64.plus bic Uint64.one, (a1, (x_b, (a1b, (a1c, (x_d, a2d)))))))
    end)
    x;

fun propagate_lit_wl_fast_code x =
  (fn ai => fn bib => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, a2l)))))))))))))
      =>
    fn () =>
    let
      val xa =
        swap_lits_fast_code bib Uint64.zero
          (fast_minus minus_uint64 Uint64.one bia) a1a ();
      val x_d = cons_trail_Propagated_tr_fast_code ai bib a1 ();
      val xaa =
        heap_array_set_u heap_bool a1f (atm_of_code ai) (is_pos_code ai) ();
    in
      (x_d, (xa, (a1b, (a1c, (a1d, (a1e, (xaa,
   (a1g, (a1h, (a1i, (a1j, (incr_propagation
                              (if (((count_decided_pol
                                      a1) : Word32.word) = (Word32.fromInt 0))
                                then incr_uset a1k else a1k),
                             (a1l, a2l)))))))))))))
    end)
    x;

fun keep_watch_heur_fast_code x =
  (fn ai => fn bib => fn bia => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) =>
    fn () =>
    let
      val xa = nth_aa_i32_u64 (heap_prod heap_uint64 heap_uint64) a1d ai bia ();
      val xb =
        update_aa_u32_i64 (heap_prod heap_uint64 heap_uint64) a1d ai bib xa ();
    in
      (a1, (a1a, (a1b, (a1c, (xb, a2d)))))
    end)
    x;

fun access_lit_in_clauses_heur_fast_code x =
  (fn ai => fn bia => fn bi =>
    let
      val (_, (a1a, _)) = ai;
    in
      isa_arena_lit_fast_code a1a (Uint64.plus bia bi)
    end)
    x;

fun uint32_of_uint64 x = Word32.fromLargeWord x;

fun isa_update_pos_fast_code x =
  (fn ai => fn bia => fn bi =>
    arl_set_u64 heap_uint32 bi
      (Uint64.minus ai (Uint64.fromInt (5 : IntInf.int)))
      (uint32_of_uint64 (Uint64.minus bia (Uint64.fromInt (2 : IntInf.int)))))
    x;

fun isa_save_pos_fast_code x =
  (fn ai => fn bia => fn (a1, (a1a, a2a)) => fn () =>
    let
      val xa = isa_arena_length_fast_code a1a ai ();
    in
      (if Uint64.less (Uint64.fromInt (4 : IntInf.int)) xa
        then (fn f_ => fn () => f_ ((isa_update_pos_fast_code ai bia a1a) ())
               ())
               (fn xb => (fn () => (a1, (xb, a2a))))
        else (fn () => (a1, (a1a, a2a))))
        ()
    end)
    x;

fun is_marked_binary_code (n, bL) =
  not (((Uint64.andb bL
          (Uint64.fromInt
            (4294967296 : IntInf.int))) : Uint64.uint64) = Uint64.zero);

fun take_only_lower32 n =
  Uint64.andb n (Uint64.fromInt (4294967295 : IntInf.int));

fun blit_of_code (n, bL) = uint32_of_uint64 (take_only_lower32 bL);

fun watcher_of_fast_code x =
  (fn (a, b) => (a, (blit_of_code (a, b), is_marked_binary_code (a, b)))) x;

fun polarity_st_heur_pol_fast x =
  (fn ai => fn bi => let
                       val (a1, _) = ai;
                     in
                       polarity_pol_fast_code a1 bi
                     end)
    x;

fun unit_propagation_inner_loop_body_wl_fast_heur_code x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = watched_by_app_heur_fast_code bi ai bia ();
    in
      let
        val (a1, (a1a, a2a)) = watcher_of_fast_code xa;
      in
        (fn f_ => fn () => f_ ((keep_watch_heur_fast_code ai bib bia bi) ()) ())
          (fn x_b =>
            (fn f_ => fn () => f_ ((polarity_st_heur_pol_fast x_b a1a) ()) ())
              (fn x_c =>
                (if ((x_c : Word32.word) = sET_TRUE_code)
                  then (fn () =>
                         (Uint64.plus bib Uint64.one,
                           (Uint64.plus bia Uint64.one, x_b)))
                  else (if a2a
                         then (if ((x_c : Word32.word) = sET_FALSE_code)
                                then (fn f_ => fn () => f_
                                       ((set_conflict_wl_heur_fast_code a1 x_b)
                                       ()) ())
                                       (fn x_g =>
 (fn () => (Uint64.plus bib Uint64.one, (Uint64.plus bia Uint64.one, x_g))))
                                else (fn f_ => fn () => f_
                                       ((access_lit_in_clauses_heur_fast_code
  x_b a1 Uint64.zero)
                                       ()) ())
                                       (fn xb =>
 (fn f_ => fn () => f_
   ((propagate_lit_wl_bin_fast_code a1a a1
      (if ((xb : Word32.word) = ai) then Uint64.zero else Uint64.one) x_b)
   ()) ())
   (fn x_i =>
     (fn () =>
       (Uint64.plus bib Uint64.one, (Uint64.plus bia Uint64.one, x_i))))))
                         else (fn f_ => fn () => f_
                                ((clause_not_marked_to_delete_heur_fast_code x_b
                                   a1)
                                ()) ())
                                (fn xb =>
                                  (if not xb
                                    then (fn () =>
   (bib, (Uint64.plus bia Uint64.one, x_b)))
                                    else (fn f_ => fn () => f_
   ((access_lit_in_clauses_heur_fast_code x_b a1 Uint64.zero) ()) ())
   (fn xc =>
     let
       val x_g =
         (if ((xc : Word32.word) = ai) then Uint64.zero else Uint64.one);
     in
       (fn f_ => fn () => f_
         ((access_lit_in_clauses_heur_fast_code x_b a1
            (fast_minus minus_uint64 Uint64.one x_g))
         ()) ())
         (fn x_i =>
           (fn f_ => fn () => f_ ((polarity_st_heur_pol_fast x_b x_i) ()) ())
             (fn x_k =>
               (if ((x_k : Word32.word) = sET_TRUE_code)
                 then update_blit_wl_heur_fast_code ai a1 a2a bib bia x_i x_b
                 else (fn f_ => fn () => f_
                        ((find_unwatched_wl_st_heur_fast_code x_b a1) ()) ())
                        (fn a =>
                          (case a
                            of NONE =>
                              (if ((x_k : Word32.word) = sET_FALSE_code)
                                then (fn f_ => fn () => f_
                                       ((set_conflict_wl_heur_fast_code a1 x_b)
                                       ()) ())
                                       (fn x_p =>
 (fn () => (Uint64.plus bib Uint64.one, (Uint64.plus bia Uint64.one, x_p))))
                                else (fn f_ => fn () => f_
                                       ((propagate_lit_wl_fast_code x_i a1 x_g
  x_b)
                                       ()) ())
                                       (fn x_p =>
 (fn () => (Uint64.plus bib Uint64.one, (Uint64.plus bia Uint64.one, x_p)))))
                            | SOME x_o =>
                              (fn f_ => fn () => f_
                                ((isa_save_pos_fast_code a1 x_o x_b) ()) ())
                                (fn x_p =>
                                  (fn f_ => fn () => f_
                                    ((access_lit_in_clauses_heur_fast_code x_p
                                       a1 x_o)
                                    ()) ())
                                    (fn x_q =>
                                      (fn f_ => fn () => f_
((polarity_st_heur_pol_fast x_p x_q) ()) ())
(fn x_s =>
  (if ((x_s : Word32.word) = sET_TRUE_code)
    then update_blit_wl_heur_fast_code ai a1 a2a bib bia x_q x_p
    else update_clause_wl_fast_code ai a1 a2a bib bia x_g x_o x_p)))))))))
     end)))))))
      end
        ()
    end)
    x;

fun length_aa_u A_ xs i =
  (fn () =>
    let
      val x =
        nth_u_code (heap_prod (heap_array (typerep_heap A_)) heap_nat) xs i ();
    in
      arl_length A_ x ()
    end);

fun length_ll_fs_heur_fast_code x =
  (fn ai => fn bi => let
                       val (_, (_, (_, (_, (a1d, _))))) = ai;
                     in
                       length_aa_u (heap_prod heap_uint64 heap_uint64) a1d bi
                     end)
    x;

fun get_conflict_wl_is_None_fast_code x =
  (fn xi => (fn () => let
                        val (_, (_, ((a1c, _), (_, (_, _))))) = xi;
                      in
                        a1c
                      end))
    x;

fun uint64_of_int i = Uint64.fromInt (integer_of_int i);

fun uint64_of_nat x = (uint64_of_int o int_of_nat) x;

fun unit_propagation_inner_loop_wl_loop_D_fast x =
  (fn ai => fn bi => fn () =>
    let
      val xa = length_ll_fs_heur_fast_code bi ai ();
    in
      heap_WHILET
        (fn (_, (a1a, a2a)) =>
          (fn f_ => fn () => f_ ((get_conflict_wl_is_None_fast_code a2a) ()) ())
            (fn x_d =>
              (fn () => (Uint64.less a1a (uint64_of_nat xa) andalso x_d))))
        (fn (a1, a) =>
          let
            val (aa, b) = a;
          in
            unit_propagation_inner_loop_body_wl_fast_heur_code ai a1 aa b
          end)
        (Uint64.zero, (Uint64.zero, bi)) ()
    end)
    x;

fun shorten_take_aa_u32 A_ B_ l j w =
  (fn () => let
              val a = nth_u_code (heap_prod B_ A_) w l ();
            in
              let
                val (aa, _) = a;
              in
                heap_array_set_u (heap_prod B_ A_) w l (aa, j)
              end
                ()
            end);

fun arl_length_o64 A_ x = (fn () => let
                                      val n = arl_length A_ x ();
                                    in
                                      uint64_of_nat n
                                    end);

fun length_aa_u32_o64 A_ xs i =
  (fn () =>
    let
      val x =
        nth_u_code (heap_prod (heap_array (typerep_heap A_)) heap_nat) xs i ();
    in
      arl_length_o64 A_ x ()
    end);

fun nat_of_uint64 x = nat_of_integer (Uint64.toInt x);

fun cut_watch_list_heur2_fast_code x =
  (fn ai => fn bib => fn bia => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) =>
    fn () =>
    let
      val xa = length_aa_u32_o64 (heap_prod heap_uint64 heap_uint64) a1d bia ();
      val a =
        heap_WHILET (fn (_, (a1f, _)) => (fn () => (Uint64.less a1f xa)))
          (fn (a1e, (a1f, a2f)) =>
            (fn f_ => fn () => f_
              ((nth_aa_i32_u64 (heap_prod heap_uint64 heap_uint64) a2f bia a1f)
              ()) ())
              (fn xb =>
                (fn f_ => fn () => f_
                  ((update_aa_u32_i64 (heap_prod heap_uint64 heap_uint64) a2f
                     bia a1e xb)
                  ()) ())
                  (fn xc =>
                    (fn () =>
                      (Uint64.plus a1e Uint64.one,
                        (Uint64.plus a1f Uint64.one, xc))))))
          (ai, (bib, a1d)) ();
    in
      let
        val (a1e, (_, a2f)) = a;
      in
        (fn f_ => fn () => f_
          ((shorten_take_aa_u32 heap_nat
             (heap_array (typerep_prod typerep_uint64 typerep_uint64)) bia
             (nat_of_uint64 a1e) a2f)
          ()) ())
          (fn x_c => (fn () => (a1, (a1a, (a1b, (a1c, (x_c, a2d)))))))
      end
        ()
    end)
    x;

fun unit_propagation_inner_loop_wl_D_fast_code x =
  (fn ai => fn bi => fn () =>
    let
      val a = unit_propagation_inner_loop_wl_loop_D_fast ai bi ();
    in
      let
        val (a1, aa) = a;
        val (a1a, ab) = aa;
      in
        cut_watch_list_heur2_fast_code a1 a1a ai ab
      end
        ()
    end)
    x;

fun unit_propagation_outer_loop_wl_D_fast_code x =
  heap_WHILET literals_to_update_wl_literals_to_update_wl_empty_fast_code
    (fn s => fn () =>
      let
        val a = select_and_remove_from_literals_to_update_wlfast_code s ();
      in
        let
          val (a1, a2) = a;
        in
          unit_propagation_inner_loop_wl_D_fast_code a2 a1
        end
          ()
      end)
    x;

fun isa_length_trail_code x =
  (fn (a1, (_, (_, (_, (_, _))))) => length_arl_u_code heap_uint32 a1) x;

fun literals_to_update_wl_literals_to_update_wl_empty_code x =
  (fn (a1, (_, (_, (a1c, (_, (_, (_, (_, (_,
   (_, (_, (_, (_, (_, (_, (_, _))))))))))))))))
     =>
    fn () => let
               val xa = isa_length_trail_code a1 ();
             in
               Word32.< (a1c, xa)
             end)
    x;

fun isa_trail_nth_code x =
  (fn ai => fn bi =>
    let
      val (a1, _) = ai;
    in
      (fn () => Array.sub ((fn (a,b) => a) (a1), Word32.toInt (bi)))
    end)
    x;

fun select_and_remove_from_literals_to_update_wl_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, (a1n, (a1o, a2o))))))))))))))))
     =>
    fn () =>
    let
      val xa = isa_trail_nth_code a1 a1c ();
    in
      ((a1, (a1a, (a1b, (Word32.+ (a1c, (Word32.fromInt 1)),
                          (a1d, (a1e, (a1f,
(a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, (a1n, (a1o, a2o)))))))))))))))),
        uminus_code xa)
    end)
    x;

fun fast_minus_nat x = (fn a => (Nat(integer_of_nat x - integer_of_nat a)));

fun arl_get A_ = (fn (a, _) => nth A_ a);

fun arena_status_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        arl_get heap_uint32 ai
          (fast_minus_nat bi (nat_of_integer (4 : IntInf.int))) ();
    in
      Word32.andb (xa, Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int)))
    end)
    x;

fun clause_not_marked_to_delete_heur_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, _))) = ai;
    in
      (fn () =>
        let
          val xa = arena_status_code a1a bi ();
        in
          not ((xa : Word32.word) = (Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int))))
        end)
    end)
    x;

fun isa_arena_lit_code x = arl_get heap_uint32 x;

fun polarity_pol_code x = (fn ai => fn bi => let
       val (_, (a1a, (_, _))) = ai;
     in
       nth_u_code heap_uint32 a1a bi
     end)
                            x;

fun isa_find_unwatched_between_code x =
  (fn ai => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn () => (is_None a1 andalso less_nat a2 (plus_nat bi bia))))
          (fn (_, a2) =>
            (fn f_ => fn () => f_ ((isa_arena_lit_code bic a2) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_ ((polarity_pol_code ai xa) ()) ())
                  (fn xb =>
                    (fn () =>
                      (if not ((xb : Word32.word) = sET_FALSE_code)
                        then (SOME (minus_nata a2 bi), a2)
                        else (NONE, plus_nat a2 one_nat))))))
          (NONE, plus_nat bi bib) ();
    in
      let
        val (a1, _) = a;
      in
        (fn () => a1)
      end
        ()
    end)
    x;

fun isa_get_saved_pos_fast_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        arl_get heap_uint32 ai (minus_nata bi (nat_of_integer (5 : IntInf.int)))
          ();
    in
      Uint64.plus (uint64_of_uint32 xa) (Uint64.fromInt (2 : IntInf.int))
    end)
    x;

fun isa_arena_length_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = arl_get heap_uint32 ai (fast_minus_nat bi one_nat) ();
    in
      Uint64.plus (Uint64.fromInt (2 : IntInf.int)) (uint64_of_uint32 xa)
    end)
    x;

fun find_unwatched_wl_st_heur_code x =
  (fn ai => fn bi =>
    let
      val (a1, (a1a, (_, (_, (_, (_, _)))))) = ai;
    in
      (fn () =>
        let
          val xa = isa_arena_length_code a1a bi ();
        in
          let
            val xb = nat_of_uint64 xa;
          in
            (fn f_ => fn () => f_ ((isa_arena_length_code a1a bi) ()) ())
              (fn xaa =>
                (if Uint64.less_eq xaa (Uint64.fromInt (4 : IntInf.int))
                  then isa_find_unwatched_between_code a1 a1a
                         (nat_of_integer (2 : IntInf.int)) xb bi
                  else (fn f_ => fn () => f_
                         ((isa_get_saved_pos_fast_code a1a bi) ()) ())
                         (fn xab =>
                           let
                             val x_c = nat_of_uint64 xab;
                           in
                             (fn f_ => fn () => f_
                               ((isa_find_unwatched_between_code a1 a1a x_c xb
                                  bi)
                               ()) ())
                               (fn x_d =>
                                 (if is_None x_d
                                   then isa_find_unwatched_between_code a1 a1a
  (nat_of_integer (2 : IntInf.int)) x_c bi
                                   else (fn () => x_d)))
                           end)))
          end
            ()
        end)
    end)
    x;

fun get_level_atm_code x =
  (fn ai => fn bi => let
                       val (_, (_, (a1b, _))) = ai;
                     in
                       nth_u_code heap_uint32 a1b bi
                     end)
    x;

fun get_level_code x =
  (fn ai => fn bi => get_level_atm_code ai (atm_of_code bi)) x;

fun set_lookup_conflict_aa_code x =
  (fn ai => fn bie => fn bid => fn bic => fn bib => fn bia => fn bi =>
    let
      val (_, a2) = bic;
    in
      (fn () =>
        let
          val a =
            heap_WHILET
              (fn (a1a, (_, (_, (_, _)))) =>
                (fn f_ => fn () => f_ ((isa_arena_length_code bie bid) ()) ())
                  (fn xa =>
                    (fn () =>
                      (less_nat a1a (plus_nat bid (nat_of_uint64 xa))))))
              (fn (a1a, (a1b, (a1c, (a1d, a2d)))) =>
                (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a) ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((get_level_code ai xa) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((lbd_write_code a1d xb true) ())
                          ())
                          (fn x_a =>
                            (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a)
                              ()) ())
                              (fn xc =>
                                (fn f_ => fn () => f_ ((get_level_code ai xc)
                                  ()) ())
                                  (fn xd =>
                                    (fn f_ => fn () => f_
                                      ((isa_arena_lit_code bie a1a) ()) ())
                                      (fn xaa =>
(fn f_ => fn () => f_ ((is_in_conflict_code a1c xaa) ()) ())
  (fn xab =>
    (fn f_ => fn () => f_
      ((if Word32.< (xd, count_decided_pol ai) andalso not xab
         then (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a) ()) ())
                (arl_append (default_uint32, heap_uint32) a2d)
         else (fn () => a2d))
      ()) ())
      (fn x_c =>
        (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a) ()) ())
          (fn xe =>
            (fn f_ => fn () => f_ ((get_level_code ai xe) ()) ())
              (fn xf =>
                (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a) ()) ())
                  (fn xac =>
                    (fn f_ => fn () => f_ ((is_in_conflict_code a1c xac) ()) ())
                      (fn xad =>
                        (fn f_ => fn () => f_
                          (let
                             val (a1e, a2e) = a1c;
                           in
                             (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a)
                               ()) ())
                               (fn xg =>
                                 (fn f_ => fn () => f_
                                   ((nth_u_code heap_bool a2e (atm_of_code xg))
                                   ()) ())
                                   (fn xh =>
                                     (fn f_ => fn () => f_
                                       ((isa_arena_lit_code bie a1a) ()) ())
                                       (fn xae =>
 (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a) ()) ())
   (fn _ =>
     (fn f_ => fn () => f_
       ((heap_array_set_u heap_bool a2e (atm_of_code xae) true) ()) ())
       (fn x_h =>
         (fn () =>
           ((if not xh then Word32.+ (a1e, (Word32.fromInt 1)) else a1e),
             x_h)))))))
                           end
                          ()) ())
                          (fn x_g =>
                            (fn () =>
                              (suc a1a,
                                ((if ((xf : Word32.word) = (count_decided_pol
                     ai)) andalso
                                       not xad
                                   then Word32.+ (a1b, (Word32.fromInt 1))
                                   else a1b),
                                  (x_g, (x_a, x_c)))))))))))))))))))
              (plus_nat bid zero_nata, (bib, (a2, (bia, bi)))) ();
        in
          let
            val (_, (a1b, (a1c, (a1d, a2d)))) = a;
          in
            (fn () => ((false, a1c), (a1b, (a1d, a2d))))
          end
            ()
        end)
    end)
    x;

fun arl_set A_ =
  (fn (a, n) => fn i => fn x => fn () => let
   val aa = upd A_ i x a ();
 in
   (aa, n)
 end);

fun isa_arena_incr_act_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        arl_get heap_uint32 ai (minus_nata bi (nat_of_integer (3 : IntInf.int)))
          ();
    in
      arl_set heap_uint32 ai (minus_nata bi (nat_of_integer (3 : IntInf.int)))
        (Word32.+ (xa, (Word32.fromInt 1))) ()
    end)
    x;

fun set_conflict_wl_heur_code x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (_, (a1d, (a1e, (a1f,
  (_, (a1h, (a1i, (a1j, (a1k, (a1l, a2l)))))))))))))
      =>
    fn () =>
    let
      val a =
        set_lookup_conflict_aa_code a1 a1a ai a1b (Word32.fromInt 0) a1i a1j ();
    in
      let
        val (a1m, (a1n, (a1o, a2o))) = a;
      in
        (fn f_ => fn () => f_ ((isa_arena_incr_act_code a1a ai) ()) ())
          (fn xa =>
            (fn f_ => fn () => f_ ((isa_length_trail_code a1) ()) ())
              (fn xaa =>
                (fn () =>
                  (a1, (xa, (a1m, (xaa, (a1d,
  (a1e, (a1f, (a1n, (a1h, (a1o, (a2o, (incr_conflict a1k,
(a1l, a2l))))))))))))))))
      end
        ()
    end)
    x;

fun cons_trail_Propagated_tr_code x =
  (fn ai => fn bia => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = arl_append (default_uint32, heap_uint32) a1 ai ();
      val xaa = heap_array_set_u heap_uint32 a1a ai sET_TRUE_code ();
      val xab =
        heap_array_set_u heap_uint32 xaa (uminus_code ai) sET_FALSE_code ();
      val xb = heap_array_set_u heap_uint32 a1b (atm_of_code ai) a1d ();
      val xc = heap_array_set_u heap_nat a1c (atm_of_code ai) bia ();
    in
      (xa, (xab, (xb, (xc, (a1d, a2d)))))
    end)
    x;

fun propagate_lit_wl_bin_code x =
  (fn ai => fn bib => fn _ =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, a2l)))))))))))))
      =>
    fn () =>
    let
      val x_b = cons_trail_Propagated_tr_code ai bib a1 ();
      val xa =
        heap_array_set_u heap_bool a1f (atm_of_code ai) (is_pos_code ai) ();
    in
      (x_b, (a1a, (a1b, (a1c, (a1d, (a1e, (xa,
    (a1g, (a1h, (a1i, (a1j, (incr_propagation
                               (if (((count_decided_pol
                                       a1) : Word32.word) = (Word32.fromInt 0))
                                 then incr_uset a1k else a1k),
                              (a1l, a2l)))))))))))))
    end)
    x;

fun nth_aa_u A_ x la l =
  (fn () =>
    let
      val xa =
        nth_u_code (heap_prod (heap_array (typerep_heap A_)) heap_nat) x la ();
      val xb = arl_get A_ xa l ();
    in
      xb
    end);

fun watched_by_app_heur_code x =
  (fn ai => fn bia => fn bi =>
    let
      val (_, (_, (_, (_, (a1d, _))))) = ai;
    in
      nth_aa_u (heap_prod heap_nat heap_uint64) a1d bia bi
    end)
    x;

fun to_watcher_code a l b =
  (a, Uint64.orb (uint64_of_uint32 l)
        (if b then Uint64.fromInt (4294967296 : IntInf.int) else Uint64.zero));

fun update_aa_u A_ a i j y =
  (fn () =>
    let
      val x =
        nth_u_code (heap_prod (heap_array (typerep_heap A_)) heap_nat) a i ();
      val aa = arl_set A_ x j y ();
    in
      array_upd_u (heap_prod (heap_array (typerep_heap A_)) heap_nat) i aa a ()
    end);

fun update_blit_wl_heur_code x =
  (fn ai => fn bie => fn bid => fn bic => fn bib => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa =
        update_aa_u (heap_prod heap_nat heap_uint64) a1d ai bic
          (to_watcher_code bie bia bid) ();
    in
      (plus_nat bic one_nat,
        (plus_nat bib one_nat, (a1, (a1a, (a1b, (a1c, (xa, a2d)))))))
    end)
    x;

fun arl_swap A_ =
  (fn ai => fn bia => fn bi => fn () => let
  val x = arl_get A_ ai bia ();
  val x_a = arl_get A_ ai bi ();
  val x_b = arl_set A_ ai bia x_a ();
in
  arl_set A_ x_b bi x ()
end);

fun swap_lits_code x =
  (fn ai => fn bib => fn bia => fn bi =>
    arl_swap heap_uint32 bi (plus_nat ai bib) (plus_nat ai bia))
    x;

fun update_clause_wl_code x =
  (fn ai => fn bif => fn bie => fn bid => fn bic => fn bib => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = isa_arena_lit_code a1a (plus_nat bif bia) ();
      val x_b = swap_lits_code bif bib bia a1a ();
      val x_d =
        append_el_aa_u
          (default_prod default_nat default_uint64,
            heap_prod heap_nat heap_uint64)
          a1d xa (to_watcher_code bif ai bie) ();
    in
      (bid, (plus_nat bic one_nat, (a1, (x_b, (a1b, (a1c, (x_d, a2d)))))))
    end)
    x;

fun propagate_lit_wl_code x =
  (fn ai => fn bib => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, a2l)))))))))))))
      =>
    fn () =>
    let
      val xa = swap_lits_code bib zero_nata (fast_minus_nat one_nat bia) a1a ();
      val x_d = cons_trail_Propagated_tr_code ai bib a1 ();
      val xaa =
        heap_array_set_u heap_bool a1f (atm_of_code ai) (is_pos_code ai) ();
    in
      (x_d, (xa, (a1b, (a1c, (a1d, (a1e, (xaa,
   (a1g, (a1h, (a1i, (a1j, (incr_propagation
                              (if (((count_decided_pol
                                      a1) : Word32.word) = (Word32.fromInt 0))
                                then incr_uset a1k else a1k),
                             (a1l, a2l)))))))))))))
    end)
    x;

fun keep_watch_heur_code x =
  (fn ai => fn bib => fn bia => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) =>
    fn () =>
    let
      val xa = nth_aa_u (heap_prod heap_nat heap_uint64) a1d ai bia ();
      val xb = update_aa_u (heap_prod heap_nat heap_uint64) a1d ai bib xa ();
    in
      (a1, (a1a, (a1b, (a1c, (xb, a2d)))))
    end)
    x;

fun access_lit_in_clauses_heur_code x =
  (fn ai => fn bia => fn bi => let
                                 val (_, (a1a, _)) = ai;
                               in
                                 isa_arena_lit_code a1a (plus_nat bia bi)
                               end)
    x;

fun isa_update_pos_code x =
  (fn ai => fn bia => fn bi =>
    arl_set heap_uint32 bi (minus_nata ai (nat_of_integer (5 : IntInf.int)))
      (uint32_of_nat (minus_nata bia (nat_of_integer (2 : IntInf.int)))))
    x;

fun isa_save_pos_code x =
  (fn ai => fn bia => fn (a1, (a1a, a2a)) => fn () =>
    let
      val xa = isa_arena_length_code a1a ai ();
    in
      (if Uint64.less (Uint64.fromInt (4 : IntInf.int)) xa
        then (fn f_ => fn () => f_ ((isa_update_pos_code ai bia a1a) ()) ())
               (fn xb => (fn () => (a1, (xb, a2a))))
        else (fn () => (a1, (a1a, a2a))))
        ()
    end)
    x;

fun watcher_of_code x =
  (fn (a, b) => (a, (blit_of_code (a, b), is_marked_binary_code (a, b)))) x;

fun polarity_st_heur_pol x = (fn ai => fn bi => let
          val (a1, _) = ai;
        in
          polarity_pol_code a1 bi
        end)
                               x;

fun unit_propagation_inner_loop_body_wl_heur_code x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = watched_by_app_heur_code bi ai bia ();
    in
      let
        val (a1, (a1a, a2a)) = watcher_of_code xa;
      in
        (fn f_ => fn () => f_ ((keep_watch_heur_code ai bib bia bi) ()) ())
          (fn x_b =>
            (fn f_ => fn () => f_ ((polarity_st_heur_pol x_b a1a) ()) ())
              (fn x_c =>
                (if ((x_c : Word32.word) = sET_TRUE_code)
                  then (fn () =>
                         (plus_nat bib one_nat, (plus_nat bia one_nat, x_b)))
                  else (if a2a
                         then (if ((x_c : Word32.word) = sET_FALSE_code)
                                then (fn f_ => fn () => f_
                                       ((set_conflict_wl_heur_code a1 x_b) ())
                                       ())
                                       (fn x_g =>
 (fn () => (plus_nat bib one_nat, (plus_nat bia one_nat, x_g))))
                                else (fn f_ => fn () => f_
                                       ((access_lit_in_clauses_heur_code x_b a1
  zero_nata)
                                       ()) ())
                                       (fn xb =>
 (fn f_ => fn () => f_
   ((propagate_lit_wl_bin_code a1a a1
      (if ((xb : Word32.word) = ai) then zero_nata else one_nat) x_b)
   ()) ())
   (fn x_i => (fn () => (plus_nat bib one_nat, (plus_nat bia one_nat, x_i))))))
                         else (fn f_ => fn () => f_
                                ((clause_not_marked_to_delete_heur_code x_b a1)
                                ()) ())
                                (fn xb =>
                                  (if not xb
                                    then (fn () =>
   (bib, (plus_nat bia one_nat, x_b)))
                                    else (fn f_ => fn () => f_
   ((access_lit_in_clauses_heur_code x_b a1 zero_nata) ()) ())
   (fn xc =>
     let
       val x_g = (if ((xc : Word32.word) = ai) then zero_nata else one_nat);
     in
       (fn f_ => fn () => f_
         ((access_lit_in_clauses_heur_code x_b a1 (fast_minus_nat one_nat x_g))
         ()) ())
         (fn x_i =>
           (fn f_ => fn () => f_ ((polarity_st_heur_pol x_b x_i) ()) ())
             (fn x_k =>
               (if ((x_k : Word32.word) = sET_TRUE_code)
                 then update_blit_wl_heur_code ai a1 a2a bib bia x_i x_b
                 else (fn f_ => fn () => f_
                        ((find_unwatched_wl_st_heur_code x_b a1) ()) ())
                        (fn a =>
                          (case a
                            of NONE =>
                              (if ((x_k : Word32.word) = sET_FALSE_code)
                                then (fn f_ => fn () => f_
                                       ((set_conflict_wl_heur_code a1 x_b) ())
                                       ())
                                       (fn x_p =>
 (fn () => (plus_nat bib one_nat, (plus_nat bia one_nat, x_p))))
                                else (fn f_ => fn () => f_
                                       ((propagate_lit_wl_code x_i a1 x_g x_b)
                                       ()) ())
                                       (fn x_p =>
 (fn () => (plus_nat bib one_nat, (plus_nat bia one_nat, x_p)))))
                            | SOME x_o =>
                              (fn f_ => fn () => f_
                                ((isa_save_pos_code a1 x_o x_b) ()) ())
                                (fn x_p =>
                                  (fn f_ => fn () => f_
                                    ((access_lit_in_clauses_heur_code x_p a1
                                       x_o)
                                    ()) ())
                                    (fn x_q =>
                                      (fn f_ => fn () => f_
((polarity_st_heur_pol x_p x_q) ()) ())
(fn x_s =>
  (if ((x_s : Word32.word) = sET_TRUE_code)
    then update_blit_wl_heur_code ai a1 a2a bib bia x_q x_p
    else update_clause_wl_code ai a1 a2a bib bia x_g x_o x_p)))))))))
     end)))))))
      end
        ()
    end)
    x;

fun length_ll_fs_heur_code x =
  (fn ai => fn bi => let
                       val (_, (_, (_, (_, (a1d, _))))) = ai;
                     in
                       length_aa_u (heap_prod heap_nat heap_uint64) a1d bi
                     end)
    x;

fun get_conflict_wl_is_None_code x =
  (fn xi => (fn () => let
                        val (_, (_, ((a1c, _), (_, (_, _))))) = xi;
                      in
                        a1c
                      end))
    x;

fun unit_propagation_inner_loop_wl_loop_D x =
  (fn ai => fn bi => fn () =>
    let
      val xa = length_ll_fs_heur_code bi ai ();
    in
      heap_WHILET
        (fn (_, (a1a, a2a)) =>
          (fn f_ => fn () => f_ ((get_conflict_wl_is_None_code a2a) ()) ())
            (fn x_d => (fn () => (less_nat a1a xa andalso x_d))))
        (fn (a1, a) =>
          let
            val (aa, b) = a;
          in
            unit_propagation_inner_loop_body_wl_heur_code ai a1 aa b
          end)
        (zero_nata, (zero_nata, bi)) ()
    end)
    x;

fun cut_watch_list_heur2_code x =
  (fn ai => fn bib => fn bia => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) =>
    fn () =>
    let
      val xa = length_aa_u (heap_prod heap_nat heap_uint64) a1d bia ();
      val a =
        heap_WHILET (fn (_, (a1f, _)) => (fn () => (less_nat a1f xa)))
          (fn (a1e, (a1f, a2f)) =>
            (fn f_ => fn () => f_
              ((nth_aa_u (heap_prod heap_nat heap_uint64) a2f bia a1f) ()) ())
              (fn xb =>
                (fn f_ => fn () => f_
                  ((update_aa_u (heap_prod heap_nat heap_uint64) a2f bia a1e xb)
                  ()) ())
                  (fn xc =>
                    (fn () =>
                      (plus_nat a1e one_nat, (plus_nat a1f one_nat, xc))))))
          (ai, (bib, a1d)) ();
    in
      let
        val (a1e, (_, a2f)) = a;
      in
        (fn f_ => fn () => f_
          ((shorten_take_aa_u32 heap_nat
             (heap_array (typerep_prod typerep_nat typerep_uint64)) bia a1e a2f)
          ()) ())
          (fn x_c => (fn () => (a1, (a1a, (a1b, (a1c, (x_c, a2d)))))))
      end
        ()
    end)
    x;

fun unit_propagation_inner_loop_wl_D_code x =
  (fn ai => fn bi => fn () =>
    let
      val a = unit_propagation_inner_loop_wl_loop_D ai bi ();
    in
      let
        val (a1, aa) = a;
        val (a1a, ab) = aa;
      in
        cut_watch_list_heur2_code a1 a1a ai ab
      end
        ()
    end)
    x;

fun unit_propagation_outer_loop_wl_D_code x =
  heap_WHILET literals_to_update_wl_literals_to_update_wl_empty_code
    (fn s => fn () =>
      let
        val a = select_and_remove_from_literals_to_update_wl_code s ();
      in
        let
          val (a1, a2) = a;
        in
          unit_propagation_inner_loop_wl_D_code a2 a1
        end
          ()
      end)
    x;

fun get_conflict_count_since_last_restart_heur_fast_code x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (_, ((a1o, _), _)))))))))))))))
          = xi;
      in
        a1o
      end))
    x;

fun upper_restart_bound_not_reached_fast_impl x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, ((_, (_, (_, (a1o, _)))),
                (_, (_, (_, (_, (_, (a1u, _))))))))))))))))))
          = xi;
      in
        less_nat a1u
          (plus_nat (nat_of_integer (3000 : IntInf.int))
            (times_nat (nat_of_integer (1000 : IntInf.int))
              (nat_of_uint64 a1o)))
      end))
    x;

val minimum_number_between_restarts : Uint64.uint64 =
  Uint64.fromInt (50 : IntInf.int);

fun opts_reduce x = (fn (_, (b, _)) => b) x;

fun opts_reduction_st_fast_code x = (fn xi => (fn () => let
                  val (_, a) = xi;
                  val (_, aa) = a;
                  val (_, ab) = aa;
                  val (_, ac) = ab;
                  val (_, ad) = ac;
                  val (_, ae) = ad;
                  val (_, af) = ae;
                  val (_, ag) = af;
                  val (_, ah) = ag;
                  val (_, ai) = ah;
                  val (_, aj) = ai;
                  val (_, ak) = aj;
                  val (_, al) = ak;
                  val (_, am) = al;
                  val (_, an) = am;
                  val (_, ao) = an;
                  val (_, ap) = ao;
                  val (_, aq) = ap;
                in
                  opts_reduce aq
                end))
                                      x;

fun get_slow_ema_heur_fast_code x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (a1m, ((_, _), _)))))))))))))))
          = xi;
      in
        a1m
      end))
    x;

fun get_learned_count_fast_code x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (_, (_, (_, (_, (a1q, _))))))))))))))))))
          = xi;
      in
        a1q
      end))
    x;

fun get_fast_ema_heur_fast_code x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (a1l, (_, (_, _)))))))))))))))
          = xi;
      in
        a1l
      end))
    x;

fun opts_restart x = (fn (a, _) => a) x;

fun opts_restart_st_fast_code x = (fn xi => (fn () => let
                val (_, a) = xi;
                val (_, aa) = a;
                val (_, ab) = aa;
                val (_, ac) = ab;
                val (_, ad) = ac;
                val (_, ae) = ad;
                val (_, af) = ae;
                val (_, ag) = af;
                val (_, ah) = ag;
                val (_, ai) = ah;
                val (_, aj) = ai;
                val (_, ak) = aj;
                val (_, al) = ak;
                val (_, am) = al;
                val (_, an) = am;
                val (_, ao) = an;
                val (_, ap) = ao;
                val (_, aq) = ap;
              in
                opts_restart aq
              end))
                                    x;

fun count_decided_st_heur x =
  (fn (a, b) => let
                  val (_, (_, (_, (_, (n, _))))) = a;
                in
                  (fn _ => n)
                end
                  b)
    x;

fun ema_get_value (v, uu) = v;

val two_uint32 : Word32.word =
  Word32.fromLargeInt (IntInf.toLarge (2 : IntInf.int));

fun restart_required_heur_fast_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = opts_reduction_st_fast_code ai ();
      val x_b = opts_restart_st_fast_code ai ();
      val xaa = get_slow_ema_heur_fast_code ai ();
      val xb = get_fast_ema_heur_fast_code ai ();
    in
      let
        val x_h = ema_get_value xb;
      in
        (fn f_ => fn () => f_
          ((get_conflict_count_since_last_restart_heur_fast_code ai) ()) ())
          (fn x_j =>
            (fn f_ => fn () => f_ ((get_learned_count_fast_code ai) ()) ())
              (fn x_l =>
                let
                  val x_r = count_decided_st_heur ai;
                in
                  (fn f_ => fn () => f_
                    ((upper_restart_bound_not_reached_fast_impl ai) ()) ())
                    (fn xba =>
                      (fn () =>
                        ((x_b orelse xa) andalso
                          ((if not xa orelse xba
                             then Uint64.less x_h
                                    (shiftr_uint64
                                      (Uint64.times
(Uint64.fromInt (11 : IntInf.int)) (ema_get_value xaa))
                                      (nat_of_integer (4 : IntInf.int)))
                             else true) andalso
                            (Uint64.less minimum_number_between_restarts
                               x_j andalso
                              (less_nat bi x_l andalso
                                (Word32.< (two_uint32, x_r) andalso
                                  Uint64.less
                                    (shiftr_uint64 x_h
                                      (nat_of_integer (32 : IntInf.int)))
                                    (uint64_of_uint32 x_r))))))))
                end))
      end
        ()
    end)
    x;

fun stamp (VMTF_Node (x1, x2, x3)) = x1;

fun find_local_restart_target_level_fast_code x =
  (fn ai => fn bi =>
    let
      val (a1, (_, (_, (_, (_, a2d))))) = ai;
      val ((a1f, (a1g, (_, (_, _)))), _) = bi;
    in
      (fn () =>
        let
          val a =
            heap_WHILET
              (fn (a1j, a2j) =>
                (fn f_ => fn () => f_ ((length_arl_u_code heap_uint32 a2d) ())
                  ())
                  (fn xa => (fn () => (not a1j andalso Word32.< (a2j, xa)))))
              (fn (_, a2j) =>
                (fn f_ => fn () => f_
                  (((fn () => Array.sub ((fn (a,b) => a) (a2d),
                     Word32.toInt (a2j))))
                  ()) ())
                  (fn x_a =>
                    (fn f_ => fn () => f_
                      (((fn () => Array.sub ((fn (a,b) => a) (a1),
                         Word32.toInt (x_a))))
                      ()) ())
                      (fn xa =>
                        (fn f_ => fn () => f_
                          ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64)
                             a1f (atm_of_code xa))
                          ()) ())
                          (fn xb =>
                            let
                              val x_e = Uint64.less (stamp xb) a1g;
                            in
                              (fn () =>
                                (x_e, (if x_e then a2j
else Word32.+ (a2j, (Word32.fromInt 1)))))
                            end))))
              (false, (Word32.fromInt 0)) ();
        in
          let
            val (_, aa) = a;
          in
            (fn () => aa)
          end
            ()
        end)
    end)
    x;

fun find_local_restart_target_level_st_fast_code x =
  (fn (a1, (_, (_, (_, (_, (a1e, (_, (_, (_, (_, _)))))))))) =>
    find_local_restart_target_level_fast_code a1 a1e)
    x;

fun restart_info_restart_done x = (fn (_, a) => (Uint64.zero, a)) x;

fun incr_lrestart x =
  (fn (propa, (confl, (dec, (res, (lres, uset))))) =>
    (propa, (confl, (dec, (res, (Uint64.plus lres Uint64.one, uset))))))
    x;

fun incr_lrestart_stat_fast_code x =
  (fn xi =>
    (fn () =>
      let
        val (a1, (a1a, (a1b, (a1c, (a1d, (a1e,
   (a1f, (a1g, (a1h, (a1i, (a1j, (a1k, (a1l,
 (a1m, (a1n, (a1o, (a1p, a2p)))))))))))))))))
          = xi;
      in
        (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
     (a1g, (a1h, (a1i, (a1j, (incr_lrestart a1k,
                               (a1l, (a1m, (restart_info_restart_done a1n,
     (a1o, (a1p, a2p)))))))))))))))))
      end))
    x;

fun empty_Q_fast_code x =
  (fn (a1, (a1a, (a1b, (_, (a1d, (a1e, (a1f,
 (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, (a1n, (a1o, a2o))))))))))))))))
     =>
    fn () =>
    let
      val xa = isa_length_trail_fast_code a1 ();
    in
      (a1, (a1a, (a1b, (xa, (a1d, (a1e, (a1f,
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
(restart_info_restart_done a1n, (a1o, a2o))))))))))))))))
    end)
    x;

fun get_pos_of_level_in_trail_imp_fast_code x =
  (fn ai => fn bi =>
    let
      val (_, (_, (_, (_, (_, a2d))))) = ai;
    in
      (fn () => Array.sub ((fn (a,b) => a) (a2d), Word32.toInt (bi)))
    end)
    x;

fun take_arl x = (fn i => fn (xs, _) => (xs, i)) x;

fun trail_conv_back_imp_fast_code x =
  (fn ai => fn bi =>
    (fn () =>
      let
        val (a1, (a1a, (a1b, (a1c, (_, a2d))))) = bi;
      in
        (a1, (a1a, (a1b, (a1c, (ai, take_arl (nat_of_uint32 ai) a2d)))))
      end))
    x;

fun arl_butlast_nonresizing x =
  (fn (xs, a) => (xs, fast_minus minus_nat a one_nat)) x;

fun arl_last A_ = (fn (a, n) => nth A_ a (minus_nata n one_nat));

val uNSET_code : Word32.word = (Word32.fromInt 0);

fun tl_trail_tr_no_CS_fast_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = arl_last heap_uint32 a1 ();
      val xaa = heap_array_set_u heap_uint32 a1a xa uNSET_code ();
      val xab = heap_array_set_u heap_uint32 xaa (uminus_code xa) uNSET_code ();
      val xb =
        heap_array_set_u heap_uint32 a1b (atm_of_code xa) (Word32.fromInt 0) ();
    in
      (arl_butlast_nonresizing a1, (xab, (xb, (a1c, (a1d, a2d)))))
    end)
    x;

fun lit_of_last_trail_fast_code x = (fn (a1, _) => arl_last heap_uint32 a1) x;

fun isa_vmtf_unset_code x =
  (fn ai => fn ((a1a, (a1b, (a1c, (a1d, a2d)))), a2) => fn () =>
    let
      val xa =
        (if is_None a2d then (fn () => true)
          else (fn f_ => fn () => f_
                 ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) a1a
                    (the a2d))
                 ()) ())
                 (fn xa =>
                   (fn f_ => fn () => f_
                     ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) a1a
                        ai)
                     ()) ())
                     (fn xaa =>
                       (fn () => (Uint64.less (stamp xa) (stamp xaa))))))
          ();
    in
      (if xa then ((a1a, (a1b, (a1c, (a1d, SOME ai)))), a2)
        else ((a1a, (a1b, (a1c, (a1d, a2d)))), a2))
    end)
    x;

fun uint32_safe_minus (A1_, A2_, A3_) m n =
  (if less A3_ m n then zero A2_ else minus A1_ m n);

fun find_decomp_wl_imp_fast_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val x_c = isa_length_trail_fast_code ai ();
      val x_e = get_pos_of_level_in_trail_imp_fast_code ai bia ();
      val a =
        heap_WHILET
          (fn (a1, (_, _)) =>
            (fn () =>
              (Word32.< (a1, uint32_safe_minus
                               (minus_uint32, zero_uint32, ord_uint32) x_c
                               x_e))))
          (fn (a1, (a1a, a2a)) =>
            (fn f_ => fn () => f_ ((lit_of_last_trail_fast_code a1a) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_ ((tl_trail_tr_no_CS_fast_code a1a) ()) ())
                  (fn xaa =>
                    (fn f_ => fn () => f_
                      ((isa_vmtf_unset_code (atm_of_code xa) a2a) ()) ())
                      (fn xb =>
                        (fn () =>
                          (Word32.+ (a1, (Word32.fromInt 1)), (xaa, xb)))))))
          ((Word32.fromInt 0), (ai, bi)) ();
    in
      let
        val (_, (a1a, a2a)) = a;
      in
        (fn f_ => fn () => f_ ((trail_conv_back_imp_fast_code bia a1a) ()) ())
          (fn x_i => (fn () => (x_i, a2a)))
      end
        ()
    end)
    x;

fun find_decomp_wl_imp_fast_codea x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, (a1h, (a1i, a2i))))))))))
      =>
    fn () =>
    let
      val a = find_decomp_wl_imp_fast_code a1 ai a1e ();
    in
      let
        val (a1j, a2j) = a;
      in
        (fn () =>
          (a1j, (a1a, (a1b, (a1c, (a1d, (a2j,
  (a1f, (a1g, (a1h, (a1i, a2i)))))))))))
      end
        ()
    end)
    x;

fun cdcl_twl_local_restart_wl_D_heur_fast_code x =
  (fn xi => fn () =>
    let
      val xa = find_local_restart_target_level_st_fast_code xi ();
    in
      (if ((xa : Word32.word) = (count_decided_st_heur xi)) then (fn () => xi)
        else (fn f_ => fn () => f_ ((find_decomp_wl_imp_fast_codea xa xi) ())
               ())
               (fn x_b =>
                 (fn f_ => fn () => f_ ((empty_Q_fast_code x_b) ()) ())
                   incr_lrestart_stat_fast_code))
        ()
    end)
    x;

fun lower_restart_bound_not_reached_fast_impl x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, ((_, (_, (_, (a1o, _)))),
                (_, (_, (_, (_, (_, (a1u, a2u))))))))))))))))))
          = xi;
      in
        not (opts_reduce a2u) orelse
          opts_restart a2u andalso
            less_nat a1u
              (plus_nat (nat_of_integer (2000 : IntInf.int))
                (times_nat (nat_of_integer (1000 : IntInf.int))
                  (nat_of_uint64 a1o)))
      end))
    x;

fun clause_not_marked_to_delete_heur_fast_code2 x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, _))) = ai;
    in
      (fn () =>
        let
          val xa = arena_status_code a1a bi ();
        in
          not ((xa : Word32.word) = (Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int))))
        end)
    end)
    x;

fun delete_index_vdom_heur_fast_code2 x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
  (a1n, (a1o, (a1p, a2p)))))))))))))))))
      =>
    fn () =>
    let
      val xa = arl_last heap_nat a1p ();
      val xb = arl_set heap_nat a1p ai xa ();
    in
      (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
 (a1n, (a1o, (arl_butlast_nonresizing xb, a2p)))))))))))))))))
    end)
    x;

fun isa_arena_decr_act_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        arl_get heap_uint32 ai (minus_nata bi (nat_of_integer (3 : IntInf.int)))
          ();
    in
      arl_set heap_uint32 ai (minus_nata bi (nat_of_integer (3 : IntInf.int)))
        (shiftr_uint32 xa one_nat) ()
    end)
    x;

fun isa_mark_unused_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        arl_get heap_uint32 ai
          (fast_minus_nat bi (nat_of_integer (4 : IntInf.int))) ();
    in
      arl_set heap_uint32 ai
        (fast_minus_nat bi (nat_of_integer (4 : IntInf.int)))
        (Word32.andb (xa,
          Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int))))
        ()
    end)
    x;

fun mark_unused_st_fast_code2 x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
  (a1n, (a1o, (a1p, (a1q, a2q))))))))))))))))))
      =>
    fn () =>
    let
      val xa = isa_mark_unused_code a1a ai ();
      val xb = isa_arena_decr_act_code xa ai ();
    in
      (a1, (xb, (a1b, (a1c, (a1d, (a1e, (a1f,
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
(a1n, (a1o, (a1p, (a1q, a2q))))))))))))))))))
    end)
    x;

fun access_vdom_at_fast_code x =
  (fn ai => fn bi =>
    let
      val (_, (_, (_, (_, (_, (_, (_, (_,
(_, (_, (_, (_, (_, (_, (_, (_, (a1p, _)))))))))))))))))
        = ai;
    in
      arl_get heap_nat a1p bi
    end)
    x;

fun length_avdom_fast_code x =
  (fn (_, (_, (_, (_, (_, (_, (_, (_, (_,
(_, (_, (_, (_, (_, (_, (_, (a1p, _)))))))))))))))))
     =>
    arl_length heap_nat a1p)
    x;

fun mark_clauses_as_unused_wl_D_heur_fast_code x =
  (fn ai => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((length_avdom_fast_code a2) ()) ())
              (fn x_a => (fn () => (less_nat a1 x_a))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((access_vdom_at_fast_code a2 a1) ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_
                  ((clause_not_marked_to_delete_heur_fast_code2 a2 x_a) ()) ())
                  (fn xa =>
                    (if not xa
                      then (fn f_ => fn () => f_
                             ((delete_index_vdom_heur_fast_code2 a1 a2) ()) ())
                             (fn x_d => (fn () => (a1, x_d)))
                      else (fn f_ => fn () => f_
                             ((mark_unused_st_fast_code2 x_a a2) ()) ())
                             (fn x_e =>
                               (fn () => (plus_nat a1 one_nat, x_e)))))))
          (ai, bi) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun get_the_propagation_reason_fast_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, (a1c, _)))) = ai;
    in
      (fn () =>
        let
          val xa = nth_u_code heap_uint64 a1c (atm_of_code bi) ();
          val xaa = nth_u_code heap_uint32 a1a bi ();
        in
          (if ((xaa : Word32.word) = sET_TRUE_code) andalso
                not ((xa : Uint64.uint64) = Uint64.one)
            then SOME xa else NONE)
        end)
    end)
    x;

fun get_the_propagation_reason_heur_fast_code x =
  (fn ai => fn bi =>
    let
      val (a1, (_, (_, (_, (_, (_, (_, (_,
 (_, (_, (_, (_, (_, (_, (_, (_, _))))))))))))))))
        = ai;
    in
      get_the_propagation_reason_fast_code a1 bi
    end)
    x;

fun incr_restart x =
  (fn (propa, (confl, (dec, (res, lres)))) =>
    (propa, (confl, (dec, (Uint64.plus res Uint64.one, lres)))))
    x;

fun ema_reinit (F1_, F2_) G_ H_ (value, (alpha, (beta, (wait, period)))) =
  (value,
    (alpha,
      (shiftl F1_ (one F2_) (nat_of_integer (32 : IntInf.int)),
        (zero G_, zero H_))));

fun incr_restart_stat_fast_code x =
  (fn xi =>
    (fn () =>
      let
        val (a1, (a1a, (a1b, (a1c, (a1d, (a1e,
   (a1f, (a1g, (a1h, (a1i, (a1j, (a1k, (a1l,
 (a1m, (a1n, (a1o, (a1p, a2p)))))))))))))))))
          = xi;
      in
        (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
     (a1g, (a1h, (a1i, (a1j, (incr_restart a1k,
                               (ema_reinit (bits_uint64, one_uint64) zero_uint64
                                  zero_uint64 a1l,
                                 (ema_reinit (bits_uint64, one_uint64)
                                    zero_uint64 zero_uint64 a1m,
                                   (restart_info_restart_done a1n,
                                     (a1o, (a1p, a2p)))))))))))))))))
      end))
    x;

fun access_lit_in_clauses_heur_fast_code2 x =
  (fn ai => fn bia => fn bi => let
                                 val (_, (a1a, _)) = ai;
                               in
                                 isa_arena_lit_code a1a (plus_nat bia bi)
                               end)
    x;

fun number_clss_to_keep_fast_impl x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, ((_, (_, (_, (a1o, _)))), (_, (_, (_, (_, (_, _)))))))))))))))))
          = xi;
      in
        plus_nat (nat_of_integer (1000 : IntInf.int))
          (times_nat (nat_of_integer (150 : IntInf.int)) (nat_of_uint64 a1o))
      end))
    x;

fun access_length_heur_fast_code2 x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (_, (_, (_, _))))))))))))))))
        = ai;
    in
      isa_arena_length_code a1a bi
    end)
    x;

fun isa_marked_as_used_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        arl_get heap_uint32 ai
          (fast_minus_nat bi (nat_of_integer (4 : IntInf.int))) ();
    in
      not (((Word32.andb (xa,
              Word32.fromLargeInt (IntInf.toLarge (4 : IntInf.int)))) : Word32.word) = (Word32.fromInt 0))
    end)
    x;

fun marked_as_used_st_fast_code2 x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (_, (_, (_, _))))))))))))))))
        = ai;
    in
      isa_marked_as_used_code a1a bi
    end)
    x;

fun clause_is_learned_heur_code2 x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (_, (_, (_, _))))))))))))))))
        = ai;
    in
      (fn () => let
                  val xa = arena_status_code a1a bi ();
                in
                  ((xa : Word32.word) = (Word32.fromInt 1))
                end)
    end)
    x;

fun isa_get_clause_LBD_code x =
  (fn ai => fn bi =>
    arl_get heap_uint32 ai
      (fast_minus_nat bi (nat_of_integer (2 : IntInf.int))))
    x;

fun isa_arena_act_code x =
  (fn ai => fn bi =>
    arl_get heap_uint32 ai
      (fast_minus_nat bi (nat_of_integer (3 : IntInf.int))))
    x;

fun clause_score_extract_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = arena_status_code ai bi ();
    in
      (if ((xa : Word32.word) = (Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int))))
        then (fn () =>
               (Word32.fromLargeInt (IntInf.toLarge (4294967295 : IntInf.int)),
                 (Word32.fromInt 0)))
        else (fn f_ => fn () => f_ ((isa_get_clause_LBD_code ai bi) ()) ())
               (fn x_a =>
                 (fn f_ => fn () => f_ ((isa_arena_act_code ai bi) ()) ())
                   (fn x_b => (fn () => (x_a, x_b)))))
        ()
    end)
    x;

fun clause_score_ordering (A1_, A2_) B_ =
  (fn (lbd, act) => fn (lbda, acta) =>
    less A2_ lbd lbda orelse eq A1_ lbd lbda andalso eq B_ act acta);

fun sgn_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then (0 : IntInf.int)
    else (if IntInf.< (k, (0 : IntInf.int)) then (~1 : IntInf.int)
           else (1 : IntInf.int)));

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if ((l : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), k)
           else (apsnd o (fn a => fn b => IntInf.* (a, b)) o sgn_integer) l
                  (if (((sgn_integer k) : IntInf.int) = (sgn_integer l))
                    then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                    else let
                           val (r, s) =
                             IntInf.divMod (IntInf.abs k, IntInf.abs l);
                         in
                           (if ((s : IntInf.int) = (0 : IntInf.int))
                             then (IntInf.~ r, (0 : IntInf.int))
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (IntInf.abs l, s)))
                         end)));

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun imp_for i u f s =
  (if less_eq_nat u i then (fn () => s)
    else (fn () => let
                     val x = f i s ();
                   in
                     imp_for (plus_nat i one_nat) u f x ()
                   end));

fun partition_clause_code x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val xa =
        let
          val x_b =
            plus_nat bib
              (divide_nat (minus_nata bia bib)
                (nat_of_integer (2 : IntInf.int)));
        in
          (fn f_ => fn () => f_ ((arl_get heap_nat bi bib) ()) ())
            (fn xa =>
              (fn f_ => fn () => f_ ((clause_score_extract_code ai xa) ()) ())
                (fn x_d =>
                  (fn f_ => fn () => f_ ((arl_get heap_nat bi x_b) ()) ())
                    (fn xb =>
                      (fn f_ => fn () => f_ ((clause_score_extract_code ai xb)
                        ()) ())
                        (fn x_f =>
                          (fn f_ => fn () => f_ ((arl_get heap_nat bi bia) ())
                            ())
                            (fn xc =>
                              (fn f_ => fn () => f_
                                ((clause_score_extract_code ai xc) ()) ())
                                (fn x_h =>
                                  (fn () =>
                                    (if clause_score_ordering
  (equal_uint32, ord_uint32) equal_uint32 x_d x_f andalso
  clause_score_ordering (equal_uint32, ord_uint32) equal_uint32 x_f x_h orelse
  clause_score_ordering (equal_uint32, ord_uint32) equal_uint32 x_h x_f andalso
    clause_score_ordering (equal_uint32, ord_uint32) equal_uint32 x_f x_d
                                      then x_b
                                      else (if clause_score_ordering
         (equal_uint32, ord_uint32) equal_uint32 x_d x_h andalso
         clause_score_ordering (equal_uint32, ord_uint32) equal_uint32 x_h
           x_f orelse
         clause_score_ordering (equal_uint32, ord_uint32) equal_uint32 x_f
           x_h andalso
           clause_score_ordering (equal_uint32, ord_uint32) equal_uint32 x_h x_d
     then bia else bib)))))))))
        end
          ();
      val x_a = arl_swap heap_nat bi xa bia ();
      val xb = arl_get heap_nat x_a bia ();
      val x_b = clause_score_extract_code ai xb ();
      val a =
        imp_for bib bia
          (fn xe => fn (a1, a2) =>
            (fn f_ => fn () => f_ ((arl_get heap_nat a2 xe) ()) ())
              (fn xc =>
                (fn f_ => fn () => f_ ((clause_score_extract_code ai xc) ()) ())
                  (fn xd =>
                    (if clause_score_ordering (equal_uint32, ord_uint32)
                          equal_uint32 xd x_b
                      then (fn f_ => fn () => f_ ((arl_swap heap_nat a2 a1 xe)
                             ()) ())
                             (fn x_h => (fn () => (plus_nat a1 one_nat, x_h)))
                      else (fn () => (a1, a2))))))
          (bib, x_a) ();
    in
      let
        val (a1, a2) = a;
      in
        (fn f_ => fn () => f_ ((arl_swap heap_nat a2 a1 bia) ()) ())
          (fn x_d => (fn () => (x_d, a1)))
      end
        ()
    end)
    x;

fun sort_clauses_by_score_code_0 ai x =
  let
    val (a1, (a1a, a2a)) = x;
  in
    (if less_eq_nat a1a a1 then (fn () => a2a)
      else (fn () =>
             let
               val a = partition_clause_code ai a1 a1a a2a ();
             in
               let
                 val (a1b, a2b) = a;
               in
                 (fn f_ => fn () => f_
                   ((sort_clauses_by_score_code_0 ai
                      (a1, (minus_nata a2b one_nat, a1b)))
                   ()) ())
                   (fn x_d =>
                     sort_clauses_by_score_code_0 ai
                       (plus_nat a2b one_nat, (a1a, x_d)))
               end
                 ()
             end))
  end;

fun arl_is_empty A_ = (fn (_, n) => (fn () => (equal_nat n zero_nata)));

fun sort_clauses_by_score_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = arl_is_empty heap_nat bi ();
    in
      (if xa then (fn () => bi)
        else (fn f_ => fn () => f_ ((arl_length heap_nat bi) ()) ())
               (fn xb =>
                 sort_clauses_by_score_code_0 ai
                   (zero_nata, (minus_nata xb one_nat, bi))))
        ()
    end)
    x;

fun sort_vdom_heur_fast_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
 (a1n, (a1o, (a1p, a2p)))))))))))))))))
     =>
    fn () =>
    let
      val xa = sort_clauses_by_score_code a1a a1p ();
    in
      (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
 (a1n, (a1o, (xa, a2p)))))))))))))))))
    end)
    x;

fun mark_garbage_code x =
  (fn ai => fn bi =>
    arl_set heap_uint32 ai (fast_minus_nat bi (nat_of_integer (4 : IntInf.int)))
      (Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int))))
    x;

val minimum_capacity : nat = nat_of_integer (16 : IntInf.int);

fun array_shrink A_ a s =
  (fn () =>
    let
      val l = len A_ a ();
    in
      (if equal_nat l s then (fn () => a)
        else (if equal_nat l zero_nata then (fn () => Array.fromList [])
               else (fn f_ => fn () => f_ ((nth A_ a zero_nata) ()) ())
                      (fn x =>
                        (fn f_ => fn () => f_ ((new A_ s x) ()) ())
                          (fn aa =>
                            (fn f_ => fn () => f_
                              ((blit A_ a zero_nata aa zero_nata s) ()) ())
                              (fn _ => (fn () => aa))))))
        ()
    end);

fun arl_butlast A_ =
  (fn (a, n) =>
    let
      val na = minus_nata n one_nat;
    in
      (fn () =>
        let
          val lena = len A_ a ();
        in
          (if less_nat (times_nat na (nat_of_integer (4 : IntInf.int)))
                lena andalso
                less_eq_nat minimum_capacity
                  (times_nat na (nat_of_integer (2 : IntInf.int)))
            then (fn f_ => fn () => f_
                   ((array_shrink A_ a
                      (times_nat na (nat_of_integer (2 : IntInf.int))))
                   ()) ())
                   (fn aa => (fn () => (aa, na)))
            else (fn () => (a, na)))
            ()
        end)
    end);

fun mark_garbage_heur_code2 x =
  (fn ai => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
  (a1n, (a1o, (a1p, (a1q, a2q))))))))))))))))))
      =>
    fn () =>
    let
      val xa = mark_garbage_code a1a ai ();
      val xaa = arl_last heap_nat a1p ();
      val xab = arl_set heap_nat a1p bia xaa ();
      val xac = arl_butlast heap_nat xab ();
    in
      (a1, (xa, (a1b, (a1c, (a1d, (a1e, (a1f,
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
(a1n, (a1o, (xac, (minus_nata a1q one_nat, a2q))))))))))))))))))
    end)
    x;

fun clause_lbd_heur_code2 x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (_, (_, (_, _))))))))))))))))
        = ai;
    in
      isa_get_clause_LBD_code a1a bi
    end)
    x;

fun mark_to_delete_clauses_wl_D_heur_fast_impl x =
  (fn xi => fn () =>
    let
      val xa = sort_vdom_heur_fast_code xi ();
      val x_a = number_clss_to_keep_fast_impl xa ();
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((length_avdom_fast_code a2) ()) ())
              (fn x_d => (fn () => (less_nat a1 x_d))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((access_vdom_at_fast_code a2 a1) ()) ())
              (fn x_d =>
                (fn f_ => fn () => f_
                  ((clause_not_marked_to_delete_heur_fast_code2 a2 x_d) ()) ())
                  (fn xb =>
                    (if not xb
                      then (fn f_ => fn () => f_
                             ((delete_index_vdom_heur_fast_code2 a1 a2) ()) ())
                             (fn x_g => (fn () => (a1, x_g)))
                      else (fn f_ => fn () => f_
                             ((access_lit_in_clauses_heur_fast_code2 a2 x_d
                                zero_nata)
                             ()) ())
                             (fn x_g =>
                               (fn f_ => fn () => f_
                                 ((get_the_propagation_reason_heur_fast_code a2
                                    x_g)
                                 ()) ())
                                 (fn x_i =>
                                   (fn f_ => fn () => f_
                                     ((if not
    (if not (is_None x_i) then equal_nat (nat_of_uint64 (the x_i)) x_d
      else false)
then (fn f_ => fn () => f_ ((clause_lbd_heur_code2 a2 x_d) ()) ())
       (fn xc =>
         (if Word32.< (Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int)), xc)
           then (fn f_ => fn () => f_ ((clause_is_learned_heur_code2 a2 x_d) ())
                  ())
                  (fn x_l =>
                    (if x_l
                      then (fn f_ => fn () => f_
                             ((access_length_heur_fast_code2 a2 x_d) ()) ())
                             (fn xd =>
                               (if not ((xd : Uint64.uint64) = (Uint64.fromInt
                         (2 : IntInf.int)))
                                 then (fn f_ => fn () => f_
((marked_as_used_st_fast_code2 a2 x_d) ()) ())
(fn x_n => (fn () => (not x_n)))
                                 else (fn () => false)))
                      else (fn () => false)))
           else (fn () => false)))
else (fn () => false))
                                     ()) ())
                                     (fn x_j =>
                                       (if x_j
 then (fn f_ => fn () => f_ ((mark_garbage_heur_code2 x_d a1 a2) ()) ())
        (fn x_l => (fn () => (a1, x_l)))
 else (fn f_ => fn () => f_ ((mark_unused_st_fast_code2 x_d a2) ()) ())
        (fn x_m => (fn () => (plus_nat a1 one_nat, x_m)))))))))))
          (x_a, xa) ();
    in
      let
        val (a1, a2) = a;
      in
        (fn f_ => fn () => f_
          ((mark_clauses_as_unused_wl_D_heur_fast_code a1 a2) ()) ())
          incr_restart_stat_fast_code
      end
        ()
    end)
    x;

fun cdcl_twl_full_restart_wl_prog_heur_fast_code x =
  mark_to_delete_clauses_wl_D_heur_fast_impl x;

fun cdcl_twl_restart_wl_heur_fast_code x =
  (fn xi => fn () =>
    let
      val xa = lower_restart_bound_not_reached_fast_impl xi ();
    in
      (if xa then cdcl_twl_local_restart_wl_D_heur_fast_code xi
        else cdcl_twl_full_restart_wl_prog_heur_fast_code xi)
        ()
    end)
    x;

fun restart_prog_wl_D_heur_fast_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = restart_required_heur_fast_code ai bia ();
    in
      (if not bi andalso xa
        then (fn f_ => fn () => f_ ((cdcl_twl_restart_wl_heur_fast_code ai) ())
               ())
               (fn x_b => (fn () => (x_b, plus_nat bia one_nat)))
        else (fn () => (ai, bia)))
        ()
    end)
    x;

fun get_conflict_count_since_last_restart_heur_slow_code x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (_, ((a1o, _), _)))))))))))))))
          = xi;
      in
        a1o
      end))
    x;

fun upper_restart_bound_not_reached_impl x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, ((_, (_, (_, (a1o, _)))),
                (_, (_, (_, (_, (_, (a1u, _))))))))))))))))))
          = xi;
      in
        less_nat a1u
          (plus_nat (nat_of_integer (3000 : IntInf.int))
            (times_nat (nat_of_integer (1000 : IntInf.int))
              (nat_of_uint64 a1o)))
      end))
    x;

fun get_slow_ema_heur_slow_code x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (a1m, ((_, _), _)))))))))))))))
          = xi;
      in
        a1m
      end))
    x;

fun get_learned_count_slow_code x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (_, (_, (_, (_, (a1q, _))))))))))))))))))
          = xi;
      in
        a1q
      end))
    x;

fun get_fast_ema_heur_slow_code x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (a1l, (_, (_, _)))))))))))))))
          = xi;
      in
        a1l
      end))
    x;

fun opts_reduction_st_code x = (fn xi => (fn () => let
             val (_, a) = xi;
             val (_, aa) = a;
             val (_, ab) = aa;
             val (_, ac) = ab;
             val (_, ad) = ac;
             val (_, ae) = ad;
             val (_, af) = ae;
             val (_, ag) = af;
             val (_, ah) = ag;
             val (_, ai) = ah;
             val (_, aj) = ai;
             val (_, ak) = aj;
             val (_, al) = ak;
             val (_, am) = al;
             val (_, an) = am;
             val (_, ao) = an;
             val (_, ap) = ao;
             val (_, aq) = ap;
           in
             opts_reduce aq
           end))
                                 x;

fun opts_restart_st_code x = (fn xi => (fn () => let
           val (_, a) = xi;
           val (_, aa) = a;
           val (_, ab) = aa;
           val (_, ac) = ab;
           val (_, ad) = ac;
           val (_, ae) = ad;
           val (_, af) = ae;
           val (_, ag) = af;
           val (_, ah) = ag;
           val (_, ai) = ah;
           val (_, aj) = ai;
           val (_, ak) = aj;
           val (_, al) = ak;
           val (_, am) = al;
           val (_, an) = am;
           val (_, ao) = an;
           val (_, ap) = ao;
           val (_, aq) = ap;
         in
           opts_restart aq
         end))
                               x;

fun restart_required_heur_slow_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = opts_reduction_st_code ai ();
      val x_b = opts_restart_st_code ai ();
      val xaa = get_slow_ema_heur_slow_code ai ();
      val xb = get_fast_ema_heur_slow_code ai ();
    in
      let
        val x_h = ema_get_value xb;
      in
        (fn f_ => fn () => f_
          ((get_conflict_count_since_last_restart_heur_slow_code ai) ()) ())
          (fn x_j =>
            (fn f_ => fn () => f_ ((get_learned_count_slow_code ai) ()) ())
              (fn x_l =>
                let
                  val x_r = count_decided_st_heur ai;
                in
                  (fn f_ => fn () => f_
                    ((upper_restart_bound_not_reached_impl ai) ()) ())
                    (fn xba =>
                      (fn () =>
                        ((x_b orelse xa) andalso
                          ((if not xa orelse xba
                             then Uint64.less x_h
                                    (shiftr_uint64
                                      (Uint64.times
(Uint64.fromInt (11 : IntInf.int)) (ema_get_value xaa))
                                      (nat_of_integer (4 : IntInf.int)))
                             else true) andalso
                            (Uint64.less minimum_number_between_restarts
                               x_j andalso
                              (less_nat bi x_l andalso
                                (Word32.< (two_uint32, x_r) andalso
                                  Uint64.less
                                    (shiftr_uint64 x_h
                                      (nat_of_integer (32 : IntInf.int)))
                                    (uint64_of_uint32 x_r))))))))
                end))
      end
        ()
    end)
    x;

fun find_local_restart_target_level_code x =
  (fn ai => fn bi =>
    let
      val (a1, (_, (_, (_, (_, a2d))))) = ai;
      val ((a1f, (a1g, (_, (_, _)))), _) = bi;
    in
      (fn () =>
        let
          val a =
            heap_WHILET
              (fn (a1j, a2j) =>
                (fn f_ => fn () => f_ ((length_arl_u_code heap_uint32 a2d) ())
                  ())
                  (fn xa => (fn () => (not a1j andalso Word32.< (a2j, xa)))))
              (fn (_, a2j) =>
                (fn f_ => fn () => f_
                  (((fn () => Array.sub ((fn (a,b) => a) (a2d),
                     Word32.toInt (a2j))))
                  ()) ())
                  (fn x_a =>
                    (fn f_ => fn () => f_
                      (((fn () => Array.sub ((fn (a,b) => a) (a1),
                         Word32.toInt (x_a))))
                      ()) ())
                      (fn xa =>
                        (fn f_ => fn () => f_
                          ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64)
                             a1f (atm_of_code xa))
                          ()) ())
                          (fn xb =>
                            let
                              val x_e = Uint64.less (stamp xb) a1g;
                            in
                              (fn () =>
                                (x_e, (if x_e then a2j
else Word32.+ (a2j, (Word32.fromInt 1)))))
                            end))))
              (false, (Word32.fromInt 0)) ();
        in
          let
            val (_, aa) = a;
          in
            (fn () => aa)
          end
            ()
        end)
    end)
    x;

fun find_local_restart_target_level_st_code x =
  (fn (a1, (_, (_, (_, (_, (a1e, (_, (_, (_, (_, _)))))))))) =>
    find_local_restart_target_level_code a1 a1e)
    x;

fun incr_lrestart_stat_slow_code x =
  (fn xi =>
    (fn () =>
      let
        val (a1, (a1a, (a1b, (a1c, (a1d, (a1e,
   (a1f, (a1g, (a1h, (a1i, (a1j, (a1k, (a1l,
 (a1m, (a1n, (a1o, (a1p, a2p)))))))))))))))))
          = xi;
      in
        (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
     (a1g, (a1h, (a1i, (a1j, (incr_lrestart a1k,
                               (a1l, (a1m, (restart_info_restart_done a1n,
     (a1o, (a1p, a2p)))))))))))))))))
      end))
    x;

fun empty_Q_code x =
  (fn (a1, (a1a, (a1b, (_, (a1d, (a1e, (a1f,
 (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, (a1n, (a1o, a2o))))))))))))))))
     =>
    fn () =>
    let
      val xa = isa_length_trail_code a1 ();
    in
      (a1, (a1a, (a1b, (xa, (a1d, (a1e, (a1f,
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
(restart_info_restart_done a1n, (a1o, a2o))))))))))))))))
    end)
    x;

fun get_pos_of_level_in_trail_imp_code x =
  (fn ai => fn bi =>
    let
      val (_, (_, (_, (_, (_, a2d))))) = ai;
    in
      (fn () => Array.sub ((fn (a,b) => a) (a2d), Word32.toInt (bi)))
    end)
    x;

fun trail_conv_back_imp_code x =
  (fn ai => fn bi =>
    (fn () =>
      let
        val (a1, (a1a, (a1b, (a1c, (_, a2d))))) = bi;
      in
        (a1, (a1a, (a1b, (a1c, (ai, take_arl (nat_of_uint32 ai) a2d)))))
      end))
    x;

fun tl_trail_tr_no_CS_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = arl_last heap_uint32 a1 ();
      val xaa = heap_array_set_u heap_uint32 a1a xa uNSET_code ();
      val xab = heap_array_set_u heap_uint32 xaa (uminus_code xa) uNSET_code ();
      val xb =
        heap_array_set_u heap_uint32 a1b (atm_of_code xa) (Word32.fromInt 0) ();
    in
      (arl_butlast_nonresizing a1, (xab, (xb, (a1c, (a1d, a2d)))))
    end)
    x;

fun lit_of_last_trail_code x = (fn (a1, _) => arl_last heap_uint32 a1) x;

fun find_decomp_wl_imp_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val x_c = isa_length_trail_code ai ();
      val x_e = get_pos_of_level_in_trail_imp_code ai bia ();
      val a =
        heap_WHILET
          (fn (a1, (_, _)) =>
            (fn () =>
              (Word32.< (a1, uint32_safe_minus
                               (minus_uint32, zero_uint32, ord_uint32) x_c
                               x_e))))
          (fn (a1, (a1a, a2a)) =>
            (fn f_ => fn () => f_ ((lit_of_last_trail_code a1a) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_ ((tl_trail_tr_no_CS_code a1a) ()) ())
                  (fn xaa =>
                    (fn f_ => fn () => f_
                      ((isa_vmtf_unset_code (atm_of_code xa) a2a) ()) ())
                      (fn xb =>
                        (fn () =>
                          (Word32.+ (a1, (Word32.fromInt 1)), (xaa, xb)))))))
          ((Word32.fromInt 0), (ai, bi)) ();
    in
      let
        val (_, (a1a, a2a)) = a;
      in
        (fn f_ => fn () => f_ ((trail_conv_back_imp_code bia a1a) ()) ())
          (fn x_i => (fn () => (x_i, a2a)))
      end
        ()
    end)
    x;

fun find_decomp_wl_imp_codea x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, (a1h, (a1i, a2i))))))))))
      =>
    fn () =>
    let
      val a = find_decomp_wl_imp_code a1 ai a1e ();
    in
      let
        val (a1j, a2j) = a;
      in
        (fn () =>
          (a1j, (a1a, (a1b, (a1c, (a1d, (a2j,
  (a1f, (a1g, (a1h, (a1i, a2i)))))))))))
      end
        ()
    end)
    x;

fun cdcl_twl_local_restart_wl_D_heur_code x =
  (fn xi => fn () =>
    let
      val xa = find_local_restart_target_level_st_code xi ();
    in
      (if ((xa : Word32.word) = (count_decided_st_heur xi)) then (fn () => xi)
        else (fn f_ => fn () => f_ ((find_decomp_wl_imp_codea xa xi) ()) ())
               (fn x_b =>
                 (fn f_ => fn () => f_ ((empty_Q_code x_b) ()) ())
                   incr_lrestart_stat_slow_code))
        ()
    end)
    x;

fun lower_restart_bound_not_reached_impl x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, ((_, (_, (_, (a1o, _)))),
                (_, (_, (_, (_, (_, (a1u, a2u))))))))))))))))))
          = xi;
      in
        not (opts_reduce a2u) orelse
          opts_restart a2u andalso
            less_nat a1u
              (plus_nat (nat_of_integer (2000 : IntInf.int))
                (times_nat (nat_of_integer (1000 : IntInf.int))
                  (nat_of_uint64 a1o)))
      end))
    x;

fun incr_restart_stat_slow_code x =
  (fn xi =>
    (fn () =>
      let
        val (a1, (a1a, (a1b, (a1c, (a1d, (a1e,
   (a1f, (a1g, (a1h, (a1i, (a1j, (a1k, (a1l,
 (a1m, (a1n, (a1o, (a1p, a2p)))))))))))))))))
          = xi;
      in
        (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
     (a1g, (a1h, (a1i, (a1j, (incr_restart a1k,
                               (ema_reinit (bits_uint64, one_uint64) zero_uint64
                                  zero_uint64 a1l,
                                 (ema_reinit (bits_uint64, one_uint64)
                                    zero_uint64 zero_uint64 a1m,
                                   (restart_info_restart_done a1n,
                                     (a1o, (a1p, a2p)))))))))))))))))
      end))
    x;

fun delete_index_vdom_heur_code x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
  (a1n, (a1o, (a1p, a2p)))))))))))))))))
      =>
    fn () =>
    let
      val xa = arl_last heap_nat a1p ();
      val xb = arl_set heap_nat a1p ai xa ();
    in
      (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
 (a1n, (a1o, (arl_butlast_nonresizing xb, a2p)))))))))))))))))
    end)
    x;

fun mark_unused_st_code x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
  (a1n, (a1o, (a1p, (a1q, a2q))))))))))))))))))
      =>
    fn () =>
    let
      val xa = isa_mark_unused_code a1a ai ();
      val xb = isa_arena_decr_act_code xa ai ();
    in
      (a1, (xb, (a1b, (a1c, (a1d, (a1e, (a1f,
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
(a1n, (a1o, (a1p, (a1q, a2q))))))))))))))))))
    end)
    x;

fun access_vdom_at_code x =
  (fn ai => fn bi =>
    let
      val (_, (_, (_, (_, (_, (_, (_, (_,
(_, (_, (_, (_, (_, (_, (_, (_, (a1p, _)))))))))))))))))
        = ai;
    in
      arl_get heap_nat a1p bi
    end)
    x;

fun length_avdom_code x =
  (fn (_, (_, (_, (_, (_, (_, (_, (_, (_,
(_, (_, (_, (_, (_, (_, (_, (a1p, _)))))))))))))))))
     =>
    arl_length heap_nat a1p)
    x;

fun mark_clauses_as_unused_wl_D_heur_code x =
  (fn ai => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((length_avdom_code a2) ()) ())
              (fn x_a => (fn () => (less_nat a1 x_a))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((access_vdom_at_code a2 a1) ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_
                  ((clause_not_marked_to_delete_heur_code a2 x_a) ()) ())
                  (fn xa =>
                    (if not xa
                      then (fn f_ => fn () => f_
                             ((delete_index_vdom_heur_code a1 a2) ()) ())
                             (fn x_d => (fn () => (a1, x_d)))
                      else (fn f_ => fn () => f_ ((mark_unused_st_code x_a a2)
                             ()) ())
                             (fn x_e =>
                               (fn () => (plus_nat a1 one_nat, x_e)))))))
          (ai, bi) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun get_the_propagation_reason_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, (a1c, _)))) = ai;
    in
      (fn () =>
        let
          val xa = nth_u_code heap_nat a1c (atm_of_code bi) ();
          val xaa = nth_u_code heap_uint32 a1a bi ();
        in
          (if ((xaa : Word32.word) = sET_TRUE_code) andalso
                not (equal_nat xa one_nat)
            then SOME xa else NONE)
        end)
    end)
    x;

fun get_the_propagation_reason_heur_code x =
  (fn ai => fn bi =>
    let
      val (a1, (_, (_, (_, (_, (_, (_, (_,
 (_, (_, (_, (_, (_, (_, (_, (_, _))))))))))))))))
        = ai;
    in
      get_the_propagation_reason_code a1 bi
    end)
    x;

fun sort_vdom_heur_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
 (a1n, (a1o, (a1p, a2p)))))))))))))))))
     =>
    fn () =>
    let
      val xa = sort_clauses_by_score_code a1a a1p ();
    in
      (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
 (a1n, (a1o, (xa, a2p)))))))))))))))))
    end)
    x;

fun clause_is_learned_heur_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (_, (_, (_, _))))))))))))))))
        = ai;
    in
      (fn () => let
                  val xa = arena_status_code a1a bi ();
                in
                  ((xa : Word32.word) = (Word32.fromInt 1))
                end)
    end)
    x;

fun number_clss_to_keep_impl x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, ((_, (_, (_, (a1o, _)))), (_, (_, (_, (_, (_, _)))))))))))))))))
          = xi;
      in
        plus_nat (nat_of_integer (1000 : IntInf.int))
          (times_nat (nat_of_integer (150 : IntInf.int)) (nat_of_uint64 a1o))
      end))
    x;

fun access_length_heur_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (_, (_, (_, _))))))))))))))))
        = ai;
    in
      isa_arena_length_code a1a bi
    end)
    x;

fun marked_as_used_st_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (_, (_, (_, _))))))))))))))))
        = ai;
    in
      isa_marked_as_used_code a1a bi
    end)
    x;

fun mark_garbage_heur_code x =
  (fn ai => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
  (a1n, (a1o, (a1p, (a1q, a2q))))))))))))))))))
      =>
    fn () =>
    let
      val xa = mark_garbage_code a1a ai ();
      val xaa = arl_last heap_nat a1p ();
      val xab = arl_set heap_nat a1p bia xaa ();
      val xac = arl_butlast heap_nat xab ();
    in
      (a1, (xa, (a1b, (a1c, (a1d, (a1e, (a1f,
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m,
(a1n, (a1o, (xac, (minus_nata a1q one_nat, a2q))))))))))))))))))
    end)
    x;

fun clause_lbd_heur_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (_, (_, (_, (_, (_, _))))))))))))))))
        = ai;
    in
      isa_get_clause_LBD_code a1a bi
    end)
    x;

fun imp_option_eq eq a b =
  (case (a, b) of (NONE, NONE) => (fn () => true)
    | (NONE, SOME _) => (fn () => false) | (SOME _, NONE) => (fn () => false)
    | (SOME aa, SOME ba) => eq aa ba);

fun mark_to_delete_clauses_wl_D_heur_impl x =
  (fn xi => fn () =>
    let
      val xa = sort_vdom_heur_code xi ();
      val x_a = number_clss_to_keep_impl xa ();
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((length_avdom_code a2) ()) ())
              (fn x_d => (fn () => (less_nat a1 x_d))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((access_vdom_at_code a2 a1) ()) ())
              (fn x_d =>
                (fn f_ => fn () => f_
                  ((clause_not_marked_to_delete_heur_code a2 x_d) ()) ())
                  (fn xb =>
                    (if not xb
                      then (fn f_ => fn () => f_
                             ((delete_index_vdom_heur_code a1 a2) ()) ())
                             (fn x_g => (fn () => (a1, x_g)))
                      else (fn f_ => fn () => f_
                             ((access_lit_in_clauses_heur_code a2 x_d zero_nata)
                             ()) ())
                             (fn x_g =>
                               (fn f_ => fn () => f_
                                 ((get_the_propagation_reason_heur_code a2 x_g)
                                 ()) ())
                                 (fn x_i =>
                                   (fn f_ => fn () => f_
                                     ((imp_option_eq
(fn va => fn vb => (fn () => (equal_nat va vb))) x_i (SOME x_d))
                                     ()) ())
                                     (fn xc =>
                                       (fn f_ => fn () => f_
 ((if not xc
    then (fn f_ => fn () => f_ ((clause_lbd_heur_code a2 x_d) ()) ())
           (fn xd =>
             (if Word32.< (Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int)), xd)
               then (fn f_ => fn () => f_ ((clause_is_learned_heur_code a2 x_d)
                      ()) ())
                      (fn x_l =>
                        (if x_l
                          then (fn f_ => fn () => f_
                                 ((access_length_heur_code a2 x_d) ()) ())
                                 (fn xe =>
                                   (if not
 ((xe : Uint64.uint64) = (Uint64.fromInt (2 : IntInf.int)))
                                     then (fn f_ => fn () => f_
    ((marked_as_used_st_code a2 x_d) ()) ())
    (fn x_n => (fn () => (not x_n)))
                                     else (fn () => false)))
                          else (fn () => false)))
               else (fn () => false)))
    else (fn () => false))
 ()) ())
 (fn x_j =>
   (if x_j
     then (fn f_ => fn () => f_ ((mark_garbage_heur_code x_d a1 a2) ()) ())
            (fn x_l => (fn () => (a1, x_l)))
     else (fn f_ => fn () => f_ ((mark_unused_st_code x_d a2) ()) ())
            (fn x_m => (fn () => (plus_nat a1 one_nat, x_m))))))))))))
          (x_a, xa) ();
    in
      let
        val (a1, a2) = a;
      in
        (fn f_ => fn () => f_ ((mark_clauses_as_unused_wl_D_heur_code a1 a2) ())
          ())
          incr_restart_stat_slow_code
      end
        ()
    end)
    x;

fun cdcl_twl_full_restart_wl_prog_heur_code x =
  mark_to_delete_clauses_wl_D_heur_impl x;

fun cdcl_twl_restart_wl_heur_code x =
  (fn xi => fn () =>
    let
      val xa = lower_restart_bound_not_reached_impl xi ();
    in
      (if xa then cdcl_twl_local_restart_wl_D_heur_code xi
        else cdcl_twl_full_restart_wl_prog_heur_code xi)
        ()
    end)
    x;

fun restart_wl_D_heur_slow_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = restart_required_heur_slow_code ai bia ();
    in
      (if not bi andalso xa
        then (fn f_ => fn () => f_ ((cdcl_twl_restart_wl_heur_code ai) ()) ())
               (fn x_b => (fn () => (x_b, plus_nat bia one_nat)))
        else (fn () => (ai, bia)))
        ()
    end)
    x;

fun get_count_max_lvls_code x =
  (fn (_, (_, (_, (_, (_, (_, (_, (clvls, _)))))))) => clvls) x;

fun maximum_level_removed_eq_count_dec_fast_code x =
  (fn _ => fn bi =>
    (fn () => (Word32.< ((Word32.fromInt 1), get_count_max_lvls_code bi))))
    x;

fun lit_and_ann_of_propagated_st_heur_fast_code x =
  (fn ((a1a, (_, (_, (a1d, _)))), _) => fn () =>
    let
      val xa = arl_last heap_uint32 a1a ();
      val xaa = arl_last heap_uint32 a1a ();
      val x_a = nth_u_code heap_uint64 a1d (atm_of_code xaa) ();
    in
      (xa, x_a)
    end)
    x;

fun last_trail_fast_code x =
  (fn (a1, (_, (_, (a1c, _)))) => fn () =>
    let
      val xa = arl_last heap_uint32 a1 ();
      val xb = nth_u_code heap_uint64 a1c (atm_of_code xa) ();
      val x_a = arl_last heap_uint32 a1 ();
    in
      (x_a, (if ((xb : Uint64.uint64) = Uint64.one) then NONE else SOME xb))
    end)
    x;

fun is_decided_hd_trail_wl_fast_code x =
  (fn (a1, _) => fn () => let
                            val xa = last_trail_fast_code a1 ();
                          in
                            is_None (snd xa)
                          end)
    x;

fun atm_is_in_conflict_st_heur_code x =
  (fn ai => fn (_, (_, ((_, (_, a2d)), _))) => fn () =>
    let
      val xa = nth_u_code heap_bool a2d (atm_of_code ai) ();
    in
      not (not xa)
    end)
    x;

fun isasat_lookup_merge_eq2_fast_code x =
  (fn ai => fn bif => fn bie => fn bid => fn bic => fn bib => fn bia => fn bi =>
    let
      val (_, a2) = bic;
    in
      (fn () =>
        let
          val xa = isa_arena_lit_fast_code bie bid ();
          val xb =
            (if ((xa : Word32.word) = ai)
              then isa_arena_lit_fast_code bie (Uint64.plus bid Uint64.one)
              else isa_arena_lit_fast_code bie bid)
              ();
          val xaa = get_level_fast_code bif xb ();
          val x_b = lbd_write_code bia xaa true ();
          val xab = get_level_fast_code bif xb ();
          val xba = is_in_conflict_code a2 xb ();
          val x_d =
            (if Word32.< (xab, count_decided_pol bif) andalso not xba
              then arl_append (default_uint32, heap_uint32) bi xb
              else (fn () => bi))
              ();
          val xac = get_level_fast_code bif xb ();
          val xbb = is_in_conflict_code a2 xb ();
          val x_h =
            let
              val (a1a, a2a) = a2;
            in
              (fn f_ => fn () => f_ ((nth_u_code heap_bool a2a (atm_of_code xb))
                ()) ())
                (fn xad =>
                  (fn f_ => fn () => f_
                    ((heap_array_set_u heap_bool a2a (atm_of_code xb) true) ())
                    ())
                    (fn x_i =>
                      (fn () =>
                        ((if not xad then Word32.+ (a1a, (Word32.fromInt 1))
                           else a1a),
                          x_i))))
            end
              ();
        in
          ((false, x_h),
            ((if ((xac : Word32.word) = (count_decided_pol bif)) andalso not xbb
               then Word32.+ (bib, (Word32.fromInt 1)) else bib),
              (x_b, x_d)))
        end)
    end)
    x;

fun resolve_merge_conflict_fast_code x =
  (fn ai => fn bie => fn bid => fn bic => fn bib => fn bia => fn bi =>
    let
      val (_, a2) = bic;
    in
      (fn () =>
        let
          val a =
            heap_WHILET
              (fn (a1a, (_, (_, (_, _)))) =>
                (fn f_ => fn () => f_ ((isa_arena_length_fast_code bie bid) ())
                  ())
                  (fn xa => (fn () => (Uint64.less a1a (Uint64.plus bid xa)))))
              (fn (a1a, (a1b, (a1c, (a1d, a2d)))) =>
                (fn f_ => fn () => f_ ((isa_arena_lit_fast_code bie a1a) ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((get_level_fast_code ai xa) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((lbd_write_code a1d xb true) ())
                          ())
                          (fn x_a =>
                            (fn f_ => fn () => f_
                              ((isa_arena_lit_fast_code bie a1a) ()) ())
                              (fn xc =>
                                (fn f_ => fn () => f_
                                  ((get_level_fast_code ai xc) ()) ())
                                  (fn xd =>
                                    (fn f_ => fn () => f_
                                      ((isa_arena_lit_fast_code bie a1a) ()) ())
                                      (fn xaa =>
(fn f_ => fn () => f_ ((is_in_conflict_code a1c xaa) ()) ())
  (fn xab =>
    (fn f_ => fn () => f_
      ((if Word32.< (xd, count_decided_pol ai) andalso not xab
         then (fn f_ => fn () => f_ ((isa_arena_lit_fast_code bie a1a) ()) ())
                (arl_append (default_uint32, heap_uint32) a2d)
         else (fn () => a2d))
      ()) ())
      (fn x_c =>
        (fn f_ => fn () => f_ ((isa_arena_lit_fast_code bie a1a) ()) ())
          (fn xe =>
            (fn f_ => fn () => f_ ((get_level_fast_code ai xe) ()) ())
              (fn xf =>
                (fn f_ => fn () => f_ ((isa_arena_lit_fast_code bie a1a) ()) ())
                  (fn xac =>
                    (fn f_ => fn () => f_ ((is_in_conflict_code a1c xac) ()) ())
                      (fn xad =>
                        (fn f_ => fn () => f_
                          (let
                             val (a1e, a2e) = a1c;
                           in
                             (fn f_ => fn () => f_
                               ((isa_arena_lit_fast_code bie a1a) ()) ())
                               (fn xg =>
                                 (fn f_ => fn () => f_
                                   ((nth_u_code heap_bool a2e (atm_of_code xg))
                                   ()) ())
                                   (fn xh =>
                                     (fn f_ => fn () => f_
                                       ((isa_arena_lit_fast_code bie a1a) ())
                                       ())
                                       (fn xae =>
 (fn f_ => fn () => f_ ((isa_arena_lit_fast_code bie a1a) ()) ())
   (fn _ =>
     (fn f_ => fn () => f_
       ((heap_array_set_u heap_bool a2e (atm_of_code xae) true) ()) ())
       (fn x_h =>
         (fn () =>
           ((if not xh then Word32.+ (a1e, (Word32.fromInt 1)) else a1e),
             x_h)))))))
                           end
                          ()) ())
                          (fn x_g =>
                            (fn () =>
                              (Uint64.plus a1a Uint64.one,
                                ((if ((xf : Word32.word) = (count_decided_pol
                     ai)) andalso
                                       not xad
                                   then Word32.+ (a1b, (Word32.fromInt 1))
                                   else a1b),
                                  (x_g, (x_a, x_c)))))))))))))))))))
              (Uint64.plus bid Uint64.one, (bib, (a2, (bia, bi)))) ();
        in
          let
            val (_, (a1b, (a1c, (a1d, a2d)))) = a;
          in
            (fn () => ((false, a1c), (a1b, (a1d, a2d))))
          end
            ()
        end)
    end)
    x;

fun fast_minus_uint32 x = fast_minus minus_uint32 x;

fun conflict_remove1_code x =
  (fn ai => fn (a1, a2) => fn () =>
    let
      val x_a = heap_array_set_u heap_bool a2 (atm_of_code ai) false ();
    in
      (fast_minus_uint32 a1 (Word32.fromInt 1), x_a)
    end)
    x;

fun isa_mark_used_fast_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        arl_get_u64 heap_uint32 ai
          (Uint64.minus bi (Uint64.fromInt (4 : IntInf.int))) ();
    in
      arl_set_u64 heap_uint32 ai
        (Uint64.minus bi (Uint64.fromInt (4 : IntInf.int)))
        (Word32.orb (xa, Word32.fromLargeInt (IntInf.toLarge (4 : IntInf.int))))
        ()
    end)
    x;

fun tl_trail_tr_fast_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = arl_last heap_uint32 a1 ();
      val xaa = heap_array_set_u heap_uint32 a1a xa uNSET_code ();
      val xab = heap_array_set_u heap_uint32 xaa (uminus_code xa) uNSET_code ();
      val xb =
        heap_array_set_u heap_uint32 a1b (atm_of_code xa) (Word32.fromInt 0) ();
      val xc = nth_u_code heap_uint64 a1c (atm_of_code xa) ();
      val xd = nth_u_code heap_uint64 a1c (atm_of_code xa) ();
    in
      (arl_butlast_nonresizing a1,
        (xab, (xb, (a1c, ((if ((xc : Uint64.uint64) = Uint64.one)
                            then fast_minus_uint32 a1d (Word32.fromInt 1)
                            else a1d),
                           (if ((xd : Uint64.uint64) = Uint64.one)
                             then arl_butlast_nonresizing a2d else a2d))))))
    end)
    x;

fun update_confl_tl_wl_fast_code x =
  (fn ai => fn bia =>
    fn (a1, (a1a, ((a1c, (a1d, a2d)),
                    (a1e, (a1f, (a1g, (a1h,
(a1i, (a1j, (a1k, (a1l, a2l)))))))))))
      =>
    fn () =>
    let
      val xa = isa_arena_length_fast_code a1a ai ();
      val a =
        (if ((xa : Uint64.uint64) = (Uint64.fromInt (2 : IntInf.int)))
          then isasat_lookup_merge_eq2_fast_code bia a1 a1a ai (a1c, (a1d, a2d))
                 a1i a1k a1l
          else resolve_merge_conflict_fast_code a1 a1a ai (a1c, (a1d, a2d)) a1i
                 a1k a1l)
          ();
    in
      let
        val ((a1n, (a1o, a2o)), (a1p, (a1q, a2q))) = a;
      in
        (fn f_ => fn () => f_ ((conflict_remove1_code bia (a1o, a2o)) ()) ())
          (fn (a1r, a2r) =>
            (fn f_ => fn () => f_ ((isa_mark_used_fast_code a1a ai) ()) ())
              (fn x_e =>
                (fn f_ => fn () => f_ ((isa_arena_incr_act_fast_code x_e ai) ())
                  ())
                  (fn x_g =>
                    (fn f_ => fn () => f_ ((tl_trail_tr_fast_code a1) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_
                          ((isa_vmtf_unset_code (atm_of_code bia) a1g) ()) ())
                          (fn xaa =>
                            (fn () =>
                              (false,
                                (xb, (x_g, ((a1n, (a1r, a2r)),
     (a1e, (a1f, (xaa, (a1h, (fast_minus_uint32 a1p (Word32.fromInt 1),
                               (a1j, (a1q, (a2q, a2l))))))))))))))))))
      end
        ()
    end)
    x;

fun tl_state_wl_heur_fast_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) => fn () =>
    let
      val xa = let
                 val (a1g, _) = a1;
               in
                 arl_last heap_uint32 a1g
               end
                 ();
      val x_a = tl_trail_tr_fast_code a1 ();
      val xb = isa_vmtf_unset_code (atm_of_code xa) a1e ();
    in
      (x_a, (a1a, (a1b, (a1c, (a1d, (xb, (a1f, a2f)))))))
    end)
    x;

fun skip_and_resolve_loop_wl_D_fast x =
  (fn xi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (if not a1
              then (fn f_ => fn () => f_ ((is_decided_hd_trail_wl_fast_code a2)
                     ()) ())
                     (fn x_b => (fn () => (not x_b)))
              else (fn () => false)))
          (fn (_, a2) =>
            (fn f_ => fn () => f_
              ((lit_and_ann_of_propagated_st_heur_fast_code a2) ()) ())
              (fn (a1a, a2a) =>
                (fn f_ => fn () => f_
                  ((atm_is_in_conflict_st_heur_code (uminus_code a1a) a2) ())
                  ())
                  (fn xa =>
                    (if not xa
                      then (fn f_ => fn () => f_
                             ((tl_state_wl_heur_fast_code a2) ()) ())
                             (fn x_e => (fn () => (false, x_e)))
                      else (fn f_ => fn () => f_
                             ((maximum_level_removed_eq_count_dec_fast_code
                                (uminus_code a1a) a2)
                             ()) ())
                             (fn x_d =>
                               (if x_d
                                 then update_confl_tl_wl_fast_code a2a a1a a2
                                 else (fn () => (true, a2))))))))
          (false, xi) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

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

fun showsp_nat p n =
  (if less_nat n (nat_of_integer (10 : IntInf.int))
    then shows_string (string_of_digit n)
    else showsp_nat p (divide_nat n (nat_of_integer (10 : IntInf.int))) o
           shows_string
             (string_of_digit
               (modulo_nat n (nat_of_integer (10 : IntInf.int)))));

fun shows_prec_nat x = showsp_nat x;

fun shows_prec_uint64 n m xs = shows_prec_nat n (nat_of_uint64 m) xs;

fun shows_prec_list A_ p xs = shows_list A_ xs;

fun isasat_current_information x =
  (fn (propa, (confl, (decs, (frestarts, (lrestarts, uset))))) => fn lcount =>
    (if (((Uint64.andb confl
            (Uint64.fromInt
              (8191 : IntInf.int))) : Uint64.uint64) = (Uint64.fromInt
                 (8191 : IntInf.int)))
      then ignore (print
             (implode
                (shows_prec_list show_char zero_nata
                   [Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, false, true, true, true, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false)]
                   [] @
                  shows_prec_uint64 zero_nata confl [] @
                    shows_prec_list show_char zero_nata
                      [Chara (false, false, false, false, false, true, false,
                               false),
                        Chara (false, false, true, true, true, true, true,
                                false),
                        Chara (false, false, false, false, false, true, false,
                                false)]
                      [] @
                      shows_prec_uint64 zero_nata propa [] @
                        shows_prec_list show_char zero_nata
                          [Chara (false, false, false, false, false, true,
                                   false, false),
                            Chara (false, false, true, true, true, true, true,
                                    false),
                            Chara (false, false, false, false, false, true,
                                    false, false)]
                          [] @
                          shows_prec_uint64 zero_nata decs [] @
                            shows_prec_list show_char zero_nata
                              [Chara (false, false, false, false, false, true,
                                       false, false),
                                Chara (false, false, true, true, true, true,
true, false),
                                Chara (false, false, false, false, false, true,
false, false)]
                              [] @
                              shows_prec_uint64 zero_nata frestarts [] @
                                shows_prec_list show_char zero_nata
                                  [Chara (false, false, false, false, false,
   true, false, false),
                                    Chara (false, false, true, true, true, true,
    true, false),
                                    Chara (false, false, false, false, false,
    true, false, false)]
                                  [] @
                                  shows_prec_uint64 zero_nata lrestarts [] @
                                    shows_prec_list show_char zero_nata
                                      [Chara
 (false, false, false, false, false, true, false, false),
Chara (false, false, true, true, true, true, true, false),
Chara (false, false, false, false, false, true, false, false)]
                                      [] @
                                      shows_prec_nat zero_nata lcount [] @
shows_prec_list show_char zero_nata
  [Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, true, true, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false)]
  [] @
  shows_prec_uint64 zero_nata uset []) ^ "\n"))
      else ()))
    x;

fun isasat_current_status_fast_code x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (a1k, (_, (_, (_, (_, (_, (a1q, _))))))))))))))))))
          = xi;
      in
        isasat_current_information a1k a1q
      end))
    x;

fun get_next (VMTF_Node (x1, x2, x3)) = x3;

fun defined_atm_fast_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, _))) = ai;
    in
      (fn () =>
        let
          val xa = nth_u_code heap_uint32 a1a (Word32.* (two_uint32, bi)) ();
        in
          not ((xa : Word32.word) = uNSET_code)
        end)
    end)
    x;

fun vmtf_find_next_undef_fast_code x =
  (fn ai => fn bi =>
    let
      val ((a1a, a), _) = ai;
      val (_, aa) = a;
      val (_, ab) = aa;
      val (_, ac) = ab;
    in
      heap_WHILET
        (fn s =>
          (if not (is_None s) then defined_atm_fast_code bi (the s)
            else (fn () => false)))
        (fn s => fn () =>
          let
            val x_b =
              nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) a1a (the s)
                ();
          in
            get_next x_b
          end)
        ac
    end)
    x;

fun update_next_search l =
  (fn (a, b) => let
                  val (ns, (m, (fst_As, (lst_As, _)))) = a;
                in
                  (fn aa => ((ns, (m, (fst_As, (lst_As, l)))), aa))
                end
                  b);

fun vmtf_find_next_undef_upd_fast_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = vmtf_find_next_undef_fast_code bi ai ();
    in
      ((ai, update_next_search xa bi), xa)
    end)
    x;

fun lit_of_found_atm_D_code x =
  (fn ai => fn a =>
    (case a of NONE => (fn () => NONE)
      | SOME xa =>
        (fn () =>
          let
            val x_a = nth_u_code heap_bool ai xa ();
          in
            (if x_a then SOME (Word32.* (two_uint32, xa))
              else SOME (Word32.+ (Word32.* (two_uint32, xa), (Word32.fromInt 1))))
          end)))
    x;

fun find_unassigned_lit_wl_D_fast_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) => fn () =>
    let
      val a = vmtf_find_next_undef_upd_fast_code a1 a1e ();
    in
      let
        val ((a1h, a2h), a2g) = a;
      in
        (fn f_ => fn () => f_ ((lit_of_found_atm_D_code a1f a2g) ()) ())
          (fn x_a =>
            (fn () =>
              ((a1h, (a1a, (a1b, (a1c, (a1d, (a2h, (a1f, a2f))))))), x_a)))
      end
        ()
    end)
    x;

fun cons_trail_Decided_tr_fast_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = arl_length heap_uint32 a1 ();
      val x_a = arl_append (default_uint32, heap_uint32) a1 ai ();
      val xaa = heap_array_set_u heap_uint32 a1a ai sET_TRUE_code ();
      val xab =
        heap_array_set_u heap_uint32 xaa (uminus_code ai) sET_FALSE_code ();
      val xb =
        heap_array_set_u heap_uint32 a1b (atm_of_code ai)
          (Word32.+ (a1d, (Word32.fromInt 1))) ();
      val xc = heap_array_set_u heap_uint64 a1c (atm_of_code ai) Uint64.one ();
      val xd =
        arl_append (default_uint32, heap_uint32) a2d (uint32_of_nat xa) ();
    in
      (x_a, (xab, (xb, (xc, (Word32.+ (a1d, (Word32.fromInt 1)), xd)))))
    end)
    x;

fun incr_decision x =
  (fn (propa, (confl, (dec, res))) =>
    (propa, (confl, (Uint64.plus dec Uint64.one, res))))
    x;

fun decide_lit_wl_fast_code x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (_, (a1d, (a1e, (a1f,
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, a2l)))))))))))))
      =>
    fn () =>
    let
      val xa = isa_length_trail_fast_code a1 ();
      val x_b = cons_trail_Decided_tr_fast_code ai a1 ();
    in
      (x_b, (a1a, (a1b, (xa, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (incr_decision a1k, (a1l, a2l)))))))))))))
    end)
    x;

fun decide_wl_or_skip_D_fast_code x =
  (fn xi => fn () =>
    let
      val a = find_unassigned_lit_wl_D_fast_code xi ();
    in
      (case a of (a1, NONE) => (fn () => (true, a1))
        | (a1, SOME x_a) =>
          (fn f_ => fn () => f_ ((decide_lit_wl_fast_code x_a a1) ()) ())
            (fn x_b => (fn () => (false, x_b))))
        ()
    end)
    x;

fun equal_minimize_status SEEN_REMOVABLE SEEN_UNKNOWN = false
  | equal_minimize_status SEEN_UNKNOWN SEEN_REMOVABLE = false
  | equal_minimize_status SEEN_FAILED SEEN_UNKNOWN = false
  | equal_minimize_status SEEN_UNKNOWN SEEN_FAILED = false
  | equal_minimize_status SEEN_FAILED SEEN_REMOVABLE = false
  | equal_minimize_status SEEN_REMOVABLE SEEN_FAILED = false
  | equal_minimize_status SEEN_UNKNOWN SEEN_UNKNOWN = true
  | equal_minimize_status SEEN_REMOVABLE SEEN_REMOVABLE = true
  | equal_minimize_status SEEN_FAILED SEEN_FAILED = true;

fun to_ana_ref x =
  (fn a => fn c => fn b =>
    (a, Uint64.orb (uint64_of_uint32 c)
          (if b then shiftl_uint64 Uint64.one (nat_of_integer (32 : IntInf.int))
            else Uint64.zero)))
    x;

fun lit_redundant_reason_stack_wl_lookup_fast_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = isa_arena_length_fast_code bia bi ();
    in
      (if Uint64.less (Uint64.fromInt (2 : IntInf.int)) xa
        then (fn () => (to_ana_ref bi (Word32.fromInt 1) false))
        else (fn f_ => fn () => f_ ((isa_arena_lit_fast_code bia bi) ()) ())
               (fn xb =>
                 (fn () =>
                   (if ((xb : Word32.word) = ai)
                     then to_ana_ref bi (Word32.fromInt 1) false
                     else to_ana_ref bi (Word32.fromInt 0) true))))
        ()
    end)
    x;

fun from_ana_ref x =
  (fn (a, b) =>
    (a, (uint32_of_uint64 (take_only_lower32 b), is_marked_binary_code (a, b))))
    x;

fun isa_get_literal_and_remove_of_analyse_wl_fast_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = arl_last (heap_prod heap_uint64 heap_uint64) bi ();
    in
      let
        val (a1, (a1a, a2a)) = from_ana_ref xa;
      in
        (fn f_ => fn () => f_
          ((isa_arena_lit_fast_code ai (Uint64.plus a1 (uint64_of_uint32 a1a)))
          ()) ())
          (fn x_a =>
            (fn f_ => fn () => f_
              ((arl_length (heap_prod heap_uint64 heap_uint64) bi) ()) ())
              (fn xb =>
                (fn f_ => fn () => f_
                  ((arl_set (heap_prod heap_uint64 heap_uint64) bi
                     (fast_minus_nat xb one_nat)
                     (to_ana_ref a1 (Word32.+ (a1a, (Word32.fromInt 1))) a2a))
                  ()) ())
                  (fn x_b => (fn () => (x_a, x_b)))))
      end
        ()
    end)
    x;

fun conflict_min_cach_set_removable_l_code x =
  (fn ai => fn bi =>
    let
      val (a1, a2) = ai;
    in
      (fn () =>
        let
          val xa =
            heap_array_set_u heap_minimize_status a1 bi SEEN_REMOVABLE ();
          val x_a = arl_append (default_uint32, heap_uint32) a2 bi ();
        in
          (xa, x_a)
        end)
    end)
    x;

fun isa_mark_failed_lits_stack_fast_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = arl_length (heap_prod heap_uint64 heap_uint64) bia ();
      val a =
        heap_WHILET (fn (a1, _) => (fn () => (less_nat a1 xa)))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((arl_get (heap_prod heap_uint64 heap_uint64) bia a1) ()) ())
              (fn xb =>
                let
                  val (a1a, (a1b, _)) = from_ana_ref xb;
                in
                  (fn f_ => fn () => f_
                    (let
                       val (a1c, a2c) = a2;
                     in
                       (fn f_ => fn () => f_
                         ((isa_arena_lit_fast_code ai
                            (fast_minus minus_uint64
                              (Uint64.plus a1a (uint64_of_uint32 a1b))
                              Uint64.one))
                         ()) ())
                         (fn xc =>
                           (fn f_ => fn () => f_
                             ((heap_array_set_u heap_minimize_status a1c
                                (atm_of_code xc) SEEN_FAILED)
                             ()) ())
                             (fn x_e =>
                               (fn f_ => fn () => f_
                                 ((isa_arena_lit_fast_code ai
                                    (fast_minus minus_uint64
                                      (Uint64.plus a1a (uint64_of_uint32 a1b))
                                      Uint64.one))
                                 ()) ())
                                 (fn xd =>
                                   (fn f_ => fn () => f_
                                     ((arl_append (default_uint32, heap_uint32)
a2c (atm_of_code xd))
                                     ()) ())
                                     (fn x_f => (fn () => (x_e, x_f))))))
                     end
                    ()) ())
                    (fn x_e => (fn () => (plus_nat a1 one_nat, x_e)))
                end))
          (zero_nata, bi) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun ana_lookup_conv_lookup_fast_code x =
  (fn ai => fn (a1, (a1a, a2a)) => fn () =>
    let
      val xa =
        (if a2a then (fn () => Uint64.one)
          else isa_arena_length_fast_code ai a1)
          ();
    in
      (a1, ((if a2a then Uint64.one else Uint64.zero),
             (uint64_of_uint32 a1a, xa)))
    end)
    x;

fun conflict_min_cach_l_code x =
  (fn ai => fn bi => let
                       val (a1, _) = ai;
                     in
                       nth_u_code heap_minimize_status a1 bi
                     end)
    x;

fun get_propagation_reason_fast_code x =
  (fn ai => fn bi =>
    let
      val (_, (_, (_, (a1c, _)))) = ai;
    in
      (fn () =>
        let
          val xa = nth_u_code heap_uint64 a1c (atm_of_code bi) ();
        in
          (if ((xa : Uint64.uint64) = Uint64.one) then NONE else SOME xa)
        end)
    end)
    x;

fun atm_in_conflict_code x =
  (fn ai => fn (_, a2) => fn () => let
                                     val xa = nth_u_code heap_bool a2 ai ();
                                   in
                                     not (not xa)
                                   end)
    x;

val initial_capacity : nat = nat_of_integer (16 : IntInf.int);

fun arl_empty (A1_, A2_) B_ =
  (fn () => let
              val a = new A2_ initial_capacity (default A1_) ();
            in
              (a, zero B_)
            end);

fun level_in_lbd_code x =
  (fn ai => fn (a1, _) => fn () =>
    let
      val xa = length_u_code heap_bool a1 ();
    in
      (if Word32.< (ai, xa) then nth_u_code heap_bool a1 ai
        else (fn () => false))
        ()
    end)
    x;

fun lit_redundant_rec_wl_lookup_fast_code x =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi =>
    heap_WHILET
      (fn (_, (a1a, _)) => fn () =>
        let
          val x_a = arl_is_empty (heap_prod heap_uint64 heap_uint64) a1a ();
        in
          not x_a
        end)
      (fn (a1, (a1a, _)) => fn () =>
        let
          val xa = arl_last (heap_prod heap_uint64 heap_uint64) a1a ();
          val a = ana_lookup_conv_lookup_fast_code bid (from_ana_ref xa) ();
        in
          let
            val (a1b, (a1c, (a1d, a2d))) = a;
          in
            (if Uint64.less_eq a2d a1d
              then (fn f_ => fn () => f_
                     ((isa_arena_lit_fast_code bid (Uint64.plus a1b a1c)) ())
                     ())
                     (fn xb =>
                       (fn f_ => fn () => f_
                         ((conflict_min_cach_set_removable_l_code a1
                            (atm_of_code xb))
                         ()) ())
                         (fn x_d =>
                           (fn () =>
                             (x_d, (arl_butlast_nonresizing a1a, true)))))
              else (fn f_ => fn () => f_
                     ((isa_get_literal_and_remove_of_analyse_wl_fast_code bid
                        a1a)
                     ()) ())
                     (fn (a1e, a2e) =>
                       (fn f_ => fn () => f_ ((get_level_fast_code ai a1e) ())
                         ())
                         (fn xb =>
                           (fn f_ => fn () => f_ ((level_in_lbd_code xb bi) ())
                             ())
                             (fn xc =>
                               (fn f_ => fn () => f_
                                 ((get_level_fast_code ai a1e) ()) ())
                                 (fn xaa =>
                                   (fn f_ => fn () => f_
                                     ((conflict_min_cach_l_code a1
(atm_of_code a1e))
                                     ()) ())
                                     (fn xba =>
                                       (fn f_ => fn () => f_
 ((atm_in_conflict_code (atm_of_code a1e) bic) ()) ())
 (fn xca =>
   (if ((xaa : Word32.word) = (Word32.fromInt 0)) orelse
         (equal_minimize_status xba SEEN_REMOVABLE orelse xca)
     then (fn () => (a1, (a2e, false)))
     else (fn f_ => fn () => f_ ((conflict_min_cach_l_code a1 (atm_of_code a1e))
            ()) ())
            (fn xab =>
              (if not xc orelse equal_minimize_status xab SEEN_FAILED
                then (fn f_ => fn () => f_
                       ((isa_mark_failed_lits_stack_fast_code bid a2e a1) ())
                       ())
                       (fn x_j =>
                         (fn f_ => fn () => f_
                           ((arl_empty
                              (default_prod default_uint64 default_uint64,
                                heap_prod heap_uint64 heap_uint64)
                              zero_nat)
                           ()) ())
                           (fn xd => (fn () => (x_j, (xd, false)))))
                else (fn f_ => fn () => f_
                       ((get_propagation_reason_fast_code ai (uminus_code a1e))
                       ()) ())
                       (fn aa =>
                         (case aa
                           of NONE =>
                             (fn f_ => fn () => f_
                               ((isa_mark_failed_lits_stack_fast_code bid a2e
                                  a1)
                               ()) ())
                               (fn x_k =>
                                 (fn f_ => fn () => f_
                                   ((arl_empty
                                      (default_prod default_uint64
 default_uint64,
heap_prod heap_uint64 heap_uint64)
                                      zero_nat)
                                   ()) ())
                                   (fn xd => (fn () => (x_k, (xd, false)))))
                           | SOME x_k =>
                             (fn f_ => fn () => f_
                               ((lit_redundant_reason_stack_wl_lookup_fast_code
                                  (uminus_code a1e) bid x_k)
                               ()) ())
                               (fn xd =>
                                 (fn f_ => fn () => f_
                                   ((arl_append
                                      (default_prod default_uint64
 default_uint64,
heap_prod heap_uint64 heap_uint64)
                                      a2e xd)
                                   ()) ())
                                   (fn xe =>
                                     (fn () => (a1, (xe, false)))))))))))))))))
          end
            ()
        end)
      (bib, (bia, false)))
    x;

fun literal_redundant_wl_lookup_fast_code x =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = get_level_fast_code ai bia ();
      val xaa = conflict_min_cach_l_code bib (atm_of_code bia) ();
    in
      (if ((xa : Word32.word) = (Word32.fromInt 0)) orelse
            equal_minimize_status xaa SEEN_REMOVABLE
        then (fn f_ => fn () => f_
               ((arl_empty
                  (default_prod default_uint64 default_uint64,
                    heap_prod heap_uint64 heap_uint64)
                  zero_nat)
               ()) ())
               (fn xb => (fn () => (bib, (xb, true))))
        else (fn f_ => fn () => f_
               ((conflict_min_cach_l_code bib (atm_of_code bia)) ()) ())
               (fn xb =>
                 (if equal_minimize_status xb SEEN_FAILED
                   then (fn f_ => fn () => f_
                          ((arl_empty
                             (default_prod default_uint64 default_uint64,
                               heap_prod heap_uint64 heap_uint64)
                             zero_nat)
                          ()) ())
                          (fn xc => (fn () => (bib, (xc, false))))
                   else (fn f_ => fn () => f_
                          ((get_propagation_reason_fast_code ai
                             (uminus_code bia))
                          ()) ())
                          (fn a =>
                            (case a
                              of NONE =>
                                (fn f_ => fn () => f_
                                  ((arl_empty
                                     (default_prod default_uint64
default_uint64,
                                       heap_prod heap_uint64 heap_uint64)
                                     zero_nat)
                                  ()) ())
                                  (fn xc => (fn () => (bib, (xc, false))))
                              | SOME x_c =>
                                (fn f_ => fn () => f_
                                  ((arl_empty
                                     (default_prod default_uint64
default_uint64,
                                       heap_prod heap_uint64 heap_uint64)
                                     zero_nat)
                                  ()) ())
                                  (fn xc =>
                                    (fn f_ => fn () => f_
                                      ((lit_redundant_reason_stack_wl_lookup_fast_code
 (uminus_code bia) bid x_c)
                                      ()) ())
                                      (fn xab =>
(fn f_ => fn () => f_
  ((arl_append
     (default_prod default_uint64 default_uint64,
       heap_prod heap_uint64 heap_uint64)
     xc xab)
  ()) ())
  (fn x_d => lit_redundant_rec_wl_lookup_fast_code ai bid bic bib x_d bi))))))))
        ()
    end)
    x;

fun arl_set_u A_ a i x = (fn () => let
                                     val b = array_upd_u A_ i x (fst a) ();
                                   in
                                     (b, snd a)
                                   end);

fun delete_index_and_swap_code x =
  (fn ai => fn bi => fn () => let
                                val xa = arl_last heap_uint32 ai ();
                                val xb = arl_set_u heap_uint32 ai bi xa ();
                              in
                                arl_butlast heap_uint32 xb ()
                              end)
    x;

fun minimize_and_extract_highest_lookup_conflict_fast_code x =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (_, (a1a, (_, a2b))) =>
            (fn f_ => fn () => f_ ((length_arl_u_code heap_uint32 a2b) ()) ())
              (fn x_a => (fn () => (Word32.< (a1a, x_a)))))
          (fn (a1, (a1a, (a1b, a2b))) =>
            (fn f_ => fn () => f_
              (((fn () => Array.sub ((fn (a,b) => a) (a2b),
                 Word32.toInt (a1a))))
              ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_
                  ((literal_redundant_wl_lookup_fast_code ai bid a1 a1b x_a bia)
                  ()) ())
                  (fn (a1c, (_, a2d)) =>
                    (if not a2d
                      then (fn () =>
                             (a1, (Word32.+ (a1a, (Word32.fromInt 1)),
                                    (a1c, a2b))))
                      else (fn f_ => fn () => f_ ((conflict_remove1_code x_a a1)
                             ()) ())
                             (fn x_e =>
                               (fn f_ => fn () => f_
                                 ((delete_index_and_swap_code a2b a1a) ()) ())
                                 (fn xa =>
                                   (fn () => (x_e, (a1a, (a1c, xa))))))))))
          (bic, ((Word32.fromInt 1), (bib, bi))) ();
    in
      let
        val (a1, (_, (a1b, a2b))) = a;
      in
        (fn () => (a1, (a1b, a2b)))
      end
        ()
    end)
    x;

fun swap_u_code A_ xs i j =
  (fn () => let
              val ki = nth_u_code A_ xs i ();
              val kj = nth_u_code A_ xs j ();
              val xsa = heap_array_set_u A_ xs i kj ();
              val x = heap_array_set_u A_ xsa j ki ();
            in
              x
            end);

fun empty_conflict_and_extract_clause_heur_fast_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = arl_length heap_uint32 bi ();
      val xaa = arl_get heap_uint32 bi zero_nata ();
      val xb = new heap_uint32 xa xaa ();
      val a =
        heap_WHILET
          (fn (_, (_, a2a)) =>
            (fn f_ => fn () => f_ ((length_arl_u_code heap_uint32 bi) ()) ())
              (fn x_c => (fn () => (Word32.< (a2a, x_c)))))
          (fn (a1, (a1a, a2a)) =>
            (fn f_ => fn () => f_
              (((fn () => Array.sub ((fn (a,b) => a) (bi), Word32.toInt (a2a))))
              ()) ())
              (fn xc =>
                (fn f_ => fn () => f_ ((conflict_remove1_code xc a1) ()) ())
                  (fn x_c =>
                    (fn f_ => fn () => f_
                      (((fn () => Array.sub ((fn (a,b) => a) (bi),
                         Word32.toInt (a2a))))
                      ()) ())
                      (fn xd =>
                        (fn f_ => fn () => f_
                          ((heap_array_set_u heap_uint32 a1a a2a xd) ()) ())
                          (fn x_e =>
                            (fn f_ => fn () => f_
                              ((nth_u_code heap_uint32 x_e (Word32.fromInt 1))
                              ()) ())
                              (fn xe =>
                                (fn f_ => fn () => f_
                                  ((get_level_fast_code ai xe) ()) ())
                                  (fn xf =>
                                    (fn f_ => fn () => f_
                                      ((nth_u_code heap_uint32 x_e a2a) ()) ())
                                      (fn xab =>
(fn f_ => fn () => f_ ((get_level_fast_code ai xab) ()) ())
  (fn xac =>
    (fn f_ => fn () => f_
      ((if Word32.< (xf, xac)
         then swap_u_code heap_uint32 x_e (Word32.fromInt 1) a2a
         else (fn () => x_e))
      ()) ())
      (fn x_g =>
        (fn () => (x_c, (x_g, Word32.+ (a2a, (Word32.fromInt 1)))))))))))))))
          (bia, (xb, (Word32.fromInt 1))) ();
    in
      let
        val (a1, (a1a, _)) = a;
      in
        (fn f_ => fn () => f_ ((arl_length heap_uint32 bi) ()) ())
          (fn xc =>
            (fn f_ => fn () => f_
              ((if equal_nat xc one_nat then (fn () => (Word32.fromInt 0))
                 else (fn f_ => fn () => f_ ((nth heap_uint32 a1a one_nat) ())
                        ())
                        (get_level_fast_code ai))
              ()) ())
              (fn xd => (fn () => ((true, a1), (a1a, xd)))))
      end
        ()
    end)
    x;

fun atoms_hash_insert_code x =
  (fn ai => fn (a1, a2) => fn () =>
    let
      val xa = nth_u_code heap_bool a2 ai ();
    in
      (if xa then (fn () => (a1, a2))
        else (fn f_ => fn () => f_
               ((arl_append (default_uint32, heap_uint32) a1 ai) ()) ())
               (fn x_a =>
                 (fn f_ => fn () => f_ ((heap_array_set_u heap_bool a2 ai true)
                   ()) ())
                   (fn x_b => (fn () => (x_a, x_b)))))
        ()
    end)
    x;

fun isa_vmtf_mark_to_rescore_code x =
  (fn ai => fn ((a1a, (a1b, (a1c, a2c))), a2) => fn () =>
    let
      val x_a = atoms_hash_insert_code ai a2 ();
    in
      ((a1a, (a1b, (a1c, a2c))), x_a)
    end)
    x;

fun vmtf_mark_to_rescore_clause_fast_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = isa_arena_length_fast_code ai bia ();
    in
      imp_for (nat_of_uint64 bia) (nat_of_uint64 (Uint64.plus bia xa))
        (fn xaa => fn sigma =>
          (fn f_ => fn () => f_ ((isa_arena_lit_code ai xaa) ()) ())
            (fn xb => isa_vmtf_mark_to_rescore_code (atm_of_code xb) sigma))
        bi ()
    end)
    x;

fun vmtf_mark_to_rescore_also_reasons_fast_code x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = arl_length heap_uint32 bia ();
    in
      imp_for zero_nata xa
        (fn xaa => fn sigma =>
          (fn f_ => fn () => f_ ((arl_get heap_uint32 bia xaa) ()) ())
            (fn xb =>
              (fn f_ => fn () => f_
                ((get_the_propagation_reason_fast_code ai (uminus_code xb)) ())
                ())
                (fn a =>
                  (case a
                    of NONE =>
                      (fn f_ => fn () => f_ ((arl_get heap_uint32 bia xaa) ())
                        ())
                        (fn xc =>
                          isa_vmtf_mark_to_rescore_code (atm_of_code xc) sigma)
                    | SOME x_c =>
                      (if ((x_c : Uint64.uint64) = Uint64.zero)
                        then (fn () => sigma)
                        else vmtf_mark_to_rescore_clause_fast_code bib x_c
                               sigma)))))
        bi ()
    end)
    x;

fun emptied_arl x = (fn (a, _) => (a, zero_nata)) x;

fun empty_cach_code x =
  (fn (a1, a2) => fn () =>
    let
      val _ = arl_length heap_uint32 a2 ();
      val a =
        heap_WHILET
          (fn (a1a, _) =>
            (fn f_ => fn () => f_ ((arl_length heap_uint32 a2) ()) ())
              (fn x_c => (fn () => (less_nat a1a x_c))))
          (fn (a1a, a2a) =>
            (fn f_ => fn () => f_ ((arl_get heap_uint32 a2 a1a) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((heap_array_set_u heap_minimize_status a2a xa SEEN_UNKNOWN)
                  ()) ())
                  (fn x_d => (fn () => (plus_nat a1a one_nat, x_d)))))
          (zero_nata, a1) ();
    in
      let
        val (_, a2a) = a;
      in
        (fn () => (a2a, emptied_arl a2))
      end
        ()
    end)
    x;

fun extract_shorter_conflict_list_heur_st_fast x =
  (fn (a1, (a1a, ((_, a2c),
                   (a1d, (a1e, (a1f, (a1g, (a1h,
     (a1i, (a1j, (a1k, (a1l, (a1m, a2m)))))))))))))
     =>
    fn () =>
    let
      val xa = lit_of_last_trail_fast_code a1 ();
      val x_b = conflict_remove1_code (uminus_code xa) a2c ();
      val x_d = arl_set heap_uint32 a1k zero_nata (uminus_code xa) ();
      val x_f = vmtf_mark_to_rescore_also_reasons_fast_code a1 a1a x_d a1f ();
      val a =
        minimize_and_extract_highest_lookup_conflict_fast_code a1 a1a x_b a1i
          a1j x_d ();
    in
      let
        val (a1n, (a1o, a2o)) = a;
      in
        (fn f_ => fn () => f_ ((empty_cach_code a1o) ()) ())
          (fn x_h =>
            (fn f_ => fn () => f_
              ((empty_conflict_and_extract_clause_heur_fast_code a1 a1n a2o) ())
              ())
              (fn (a1p, (a1q, a2q)) =>
                (fn () =>
                  ((a1, (a1a, (a1p, (a1d, (a1e,
    (x_f, (a1g, (a1h, (x_h, (a1j, (let
                                     val (aa, _) = a2o;
                                   in
                                     (aa, one_nat)
                                   end,
                                    (a1l, (a1m, a2m))))))))))))),
                    (a2q, a1q)))))
      end
        ()
    end)
    x;

fun lit_of_hd_trail_st_heur_fast_code x =
  (fn (a1, (_, (_, (_, (_, (_, _)))))) => lit_of_last_trail_fast_code a1) x;

fun incr_conflict_count_since_last_restart x =
  (fn (ccount, a) => (Uint64.plus ccount Uint64.one, a)) x;

fun vmtf_enqueue_fast_code x =
  (fn ai => fn bia => fn (a1, (a1a, (a1b, (a1c, a2c)))) => fn () =>
    let
      val xa = defined_atm_fast_code ai bia ();
    in
      (case a1b
        of NONE =>
          (fn f_ => fn () => f_
            ((heap_array_set_u (heap_vmtf_node heap_uint32 heap_uint64) a1 bia
               (VMTF_Node (a1a, a1b, NONE)))
            ()) ())
            (fn x_a =>
              (fn () =>
                (x_a, (Uint64.plus a1a Uint64.one,
                        (bia, (bia, (if xa then NONE else SOME bia)))))))
        | SOME x_a =>
          (fn f_ => fn () => f_
            ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) a1 x_a) ())
            ())
            (fn xaa =>
              (fn f_ => fn () => f_
                ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) a1 x_a)
                ()) ())
                (fn xb =>
                  (fn f_ => fn () => f_
                    ((heap_array_set_u (heap_vmtf_node heap_uint32 heap_uint64)
                       a1 bia
                       (VMTF_Node (Uint64.plus a1a Uint64.one, NONE, SOME x_a)))
                    ()) ())
                    (fn xc =>
                      (fn f_ => fn () => f_
                        ((heap_array_set_u
                           (heap_vmtf_node heap_uint32 heap_uint64) xc x_a
                           (VMTF_Node (stamp xaa, SOME bia, get_next xb)))
                        ()) ())
                        (fn x_c =>
                          (fn () =>
                            (x_c, (Uint64.plus a1a Uint64.one,
                                    (bia, (the a1c,
    (if xa then a2c else SOME bia)))))))))))
        ()
    end)
    x;

fun get_prev (VMTF_Node (x1, x2, x3)) = x2;

fun ns_vmtf_dequeue_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) bi ai ();
      val x_a =
        (case get_prev xa of NONE => (fn () => bi)
          | SOME x_b =>
            (fn f_ => fn () => f_
              ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) bi x_b) ())
              ())
              (fn xaa =>
                (fn f_ => fn () => f_
                  ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) bi x_b)
                  ()) ())
                  (fn xb =>
                    heap_array_set_u (heap_vmtf_node heap_uint32 heap_uint64) bi
                      x_b (VMTF_Node (stamp xaa, get_prev xb, get_next xa)))))
          ();
      val x_b =
        (case get_next xa of NONE => (fn () => x_a)
          | SOME x_c =>
            (fn f_ => fn () => f_
              ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) x_a x_c) ())
              ())
              (fn xaa =>
                (fn f_ => fn () => f_
                  ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) x_a x_c)
                  ()) ())
                  (fn xb =>
                    heap_array_set_u (heap_vmtf_node heap_uint32 heap_uint64)
                      x_a x_c
                      (VMTF_Node (stamp xaa, get_prev xa, get_next xb)))))
          ();
      val xb = nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) x_b ai ();
    in
      heap_array_set_u (heap_vmtf_node heap_uint32 heap_uint64) x_b ai
        (VMTF_Node (stamp xb, NONE, NONE)) ()
    end)
    x;

fun vmtf_dequeue_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, a2c)))) => fn () =>
    let
      val xa =
        (if ((a1b : Word32.word) = ai)
          then (fn f_ => fn () => f_
                 ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) a1 ai)
                 ()) ())
                 (fn x_a => (fn () => (get_next x_a)))
          else (fn () => (SOME a1b)))
          ();
      val xaa =
        imp_option_eq (fn va => fn vb => (fn () => ((va : Word32.word) = vb)))
          a2c (SOME ai) ();
      val x_a =
        (if xaa
          then (fn f_ => fn () => f_
                 ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) a1 ai)
                 ()) ())
                 (fn x_b => (fn () => (get_next x_b)))
          else (fn () => a2c))
          ();
      val x_b =
        (if ((a1c : Word32.word) = ai)
          then (fn f_ => fn () => f_
                 ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) a1 ai)
                 ()) ())
                 (fn x_c => (fn () => (get_prev x_c)))
          else (fn () => (SOME a1c)))
          ();
      val x_c = ns_vmtf_dequeue_code ai a1 ();
    in
      (x_c, (a1a, (xa, (x_b, x_a))))
    end)
    x;

fun vmtf_en_dequeue_fast_code x =
  (fn ai => fn bia => fn bi => fn () => let
  val xa = vmtf_dequeue_code bia bi ();
in
  vmtf_enqueue_fast_code ai bia xa ()
end)
    x;

fun partition_vmtf_nth_code x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val xa =
        let
          val x_b =
            plus_nat bib
              (divide_nat (fast_minus_nat bia bib)
                (nat_of_integer (2 : IntInf.int)));
        in
          (fn f_ => fn () => f_ ((arl_get heap_uint32 bi bib) ()) ())
            (fn xa =>
              (fn f_ => fn () => f_
                ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) ai xa) ())
                ())
                (fn xb =>
                  let
                    val x_d = stamp xb;
                  in
                    (fn f_ => fn () => f_ ((arl_get heap_uint32 bi x_b) ()) ())
                      (fn xc =>
                        (fn f_ => fn () => f_
                          ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64)
                             ai xc)
                          ()) ())
                          (fn xd =>
                            let
                              val x_f = stamp xd;
                            in
                              (fn f_ => fn () => f_
                                ((arl_get heap_uint32 bi bia) ()) ())
                                (fn xe =>
                                  (fn f_ => fn () => f_
                                    ((nth_u_code
                                       (heap_vmtf_node heap_uint32 heap_uint64)
                                       ai xe)
                                    ()) ())
                                    (fn xf =>
                                      let
val x_h = stamp xf;
                                      in
(fn () =>
  (if Uint64.less x_d x_f andalso Uint64.less x_f x_h orelse
        Uint64.less x_h x_f andalso Uint64.less x_f x_d
    then x_b
    else (if Uint64.less x_d x_h andalso Uint64.less x_h x_f orelse
               Uint64.less x_f x_h andalso Uint64.less x_h x_d
           then bia else bib)))
                                      end))
                            end))
                  end))
        end
          ();
      val x_a = arl_swap heap_uint32 bi xa bia ();
      val xb = arl_get heap_uint32 x_a bia ();
      val xc = nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) ai xb ();
      val a =
        imp_for bib bia
          (fn xe => fn (a1, a2) =>
            (fn f_ => fn () => f_ ((arl_get heap_uint32 a2 xe) ()) ())
              (fn xaa =>
                (fn f_ => fn () => f_
                  ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) ai xaa)
                  ()) ())
                  (fn xab =>
                    (if Uint64.less (stamp xab) (stamp xc)
                      then (fn f_ => fn () => f_
                             ((arl_swap heap_uint32 a2 a1 xe) ()) ())
                             (fn x_h => (fn () => (plus_nat a1 one_nat, x_h)))
                      else (fn () => (a1, a2))))))
          (bib, x_a) ();
    in
      let
        val (a1, a2) = a;
      in
        (fn f_ => fn () => f_ ((arl_swap heap_uint32 a2 a1 bia) ()) ())
          (fn x_d => (fn () => (x_d, a1)))
      end
        ()
    end)
    x;

fun quicksort_vmtf_nth_code_0 a1 x =
  let
    val (a1a, (a1b, a2b)) = x;
  in
    (if less_eq_nat a1b a1a then (fn () => a2b)
      else (fn () =>
             let
               val a = partition_vmtf_nth_code a1 a1a a1b a2b ();
             in
               let
                 val (a1c, a2c) = a;
               in
                 (fn f_ => fn () => f_
                   ((quicksort_vmtf_nth_code_0 a1
                      (a1a, (minus_nata a2c one_nat, a1c)))
                   ()) ())
                   (fn x_d =>
                     quicksort_vmtf_nth_code_0 a1
                       (plus_nat a2c one_nat, (a1b, x_d)))
               end
                 ()
             end))
  end;

fun quicksort_vmtf_nth_code x =
  (fn ai => fn bi =>
    let
      val (a1, _) = ai;
    in
      (fn () =>
        let
          val xa = arl_is_empty heap_uint32 bi ();
        in
          (if xa then (fn () => bi)
            else (fn f_ => fn () => f_ ((arl_length heap_uint32 bi) ()) ())
                   (fn xb =>
                     quicksort_vmtf_nth_code_0 a1
                       (zero_nata, (minus_nata xb one_nat, bi))))
            ()
        end)
    end)
    x;

fun atoms_hash_del_code x =
  (fn ai => fn bi => heap_array_set_u heap_bool bi ai false) x;

fun vmtf_rescale_code x =
  (fn (a1, (_, (a1b, (a1c, a2c)))) => fn () =>
    let
      val a =
        heap_WHILET (fn (_, (_, a2e)) => (fn () => (not (is_None a2e))))
          (fn (a1d, (a1e, a2e)) =>
            let
              val x_a = the a2e;
            in
              (fn f_ => fn () => f_
                ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) a1d x_a)
                ()) ())
                (fn x_c =>
                  let
                    val x_g = get_prev x_c;
                  in
                    (fn f_ => fn () => f_
                      ((heap_array_set_u
                         (heap_vmtf_node heap_uint32 heap_uint64) a1d x_a
                         (VMTF_Node (a1e, x_g, get_next x_c)))
                      ()) ())
                      (fn x_i =>
                        (fn () => (x_i, (Uint64.plus a1e Uint64.one, x_g))))
                  end)
            end)
          (a1, (Uint64.zero, SOME a1c)) ();
    in
      let
        val (a1d, (a1e, _)) = a;
      in
        (fn () => (a1d, (a1e, (a1b, (a1c, a2c)))))
      end
        ()
    end)
    x;

fun current_stamp vm = fst (snd vm);

fun isa_vmtf_flush_fast_code x =
  (fn ai => fn (a1, (a1a, a2a)) => fn () =>
    let
      val xa = quicksort_vmtf_nth_code a1 a1a ();
      val xaa = arl_length heap_uint32 xa ();
      val x_a =
        (if less_eq_nat (nat_of_integer (18446744073709551615 : IntInf.int))
              (plus_nat xaa (nat_of_uint64 (current_stamp a1)))
          then vmtf_rescale_code a1 else (fn () => a1))
          ();
      val a =
        heap_WHILET
          (fn (a1b, (_, _)) =>
            (fn f_ => fn () => f_ ((length_arl_u_code heap_uint32 xa) ()) ())
              (fn x_c => (fn () => (Word32.< (a1b, x_c)))))
          (fn (a1b, (a1c, a2c)) =>
            (fn f_ => fn () => f_
              (((fn () => Array.sub ((fn (a,b) => a) (xa), Word32.toInt (a1b))))
              ()) ())
              (fn xab =>
                (fn f_ => fn () => f_ ((vmtf_en_dequeue_fast_code ai xab a1c)
                  ()) ())
                  (fn x_c =>
                    (fn f_ => fn () => f_
                      (((fn () => Array.sub ((fn (a,b) => a) (xa),
                         Word32.toInt (a1b))))
                      ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((atoms_hash_del_code xb a2c) ())
                          ())
                          (fn xc =>
                            (fn () =>
                              (Word32.+ (a1b, (Word32.fromInt 1)),
                                (x_c, xc))))))))
          ((Word32.fromInt 0), (x_a, a2a)) ();
    in
      let
        val (_, (a1c, a2c)) = a;
      in
        (fn () => (a1c, (emptied_arl xa, a2c)))
      end
        ()
    end)
    x;

fun ema_bitshifting (A1_, A2_) =
  shiftl A1_ (one A2_) (nat_of_integer (32 : IntInf.int));

fun ema_update_ref x =
  (fn lbd => fn (value, (alpha, (beta, (wait, period)))) =>
    let
      val lbda =
        Uint64.times (uint64_of_uint32 lbd)
          (ema_bitshifting (bits_uint64, one_uint64));
      val valuea =
        (if Uint64.less value lbda
          then Uint64.plus value
                 (shiftr_uint64 (Uint64.times beta (Uint64.minus lbda value))
                   (nat_of_integer (32 : IntInf.int)))
          else Uint64.minus value
                 (shiftr_uint64 (Uint64.times beta (Uint64.minus value lbda))
                   (nat_of_integer (32 : IntInf.int))));
    in
      (if Uint64.less_eq beta alpha orelse Uint64.less Uint64.zero wait
        then (valuea, (alpha, (beta, (Uint64.minus wait Uint64.one, period))))
        else let
               val waita =
                 Uint64.plus
                   (Uint64.times (Uint64.fromInt (2 : IntInf.int)) period)
                   Uint64.one;
               val perioda = waita;
               val betaa = shiftr_uint64 beta one_nat;
               val betab =
                 (if Uint64.less_eq betaa alpha then alpha else betaa);
             in
               (valuea, (alpha, (betab, (waita, perioda))))
             end)
    end)
    x;

fun lbd_empty_code x =
  (fn (a1, a2) => fn () =>
    let
      val a =
        heap_WHILET (fn (_, a2a) => (fn () => (Word32.<= (a2a, a2))))
          (fn (a1a, a2a) =>
            (fn f_ => fn () => f_ ((heap_array_set_u heap_bool a1a a2a false)
              ()) ())
              (fn x_a => (fn () => (x_a, Word32.+ (a2a, (Word32.fromInt 1))))))
          (a1, (Word32.fromInt 0)) ();
    in
      let
        val (a1a, _) = a;
      in
        (fn () => (a1a, (Word32.fromInt 0)))
      end
        ()
    end)
    x;

fun propagate_unit_bt_wl_D_fast_code x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (_, (a1d, (a1e, (a1f,
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, (a1n, a2n)))))))))))))))
      =>
    fn () =>
    let
      val xa = isa_vmtf_flush_fast_code a1 a1e ();
      val x_a = get_LBD_code a1i ();
      val x_b = lbd_empty_code a1i ();
      val x_c = isa_length_trail_fast_code a1 ();
      val x_e =
        cons_trail_Propagated_tr_fast_code (uminus_code ai) Uint64.zero a1 ();
    in
      (x_e, (a1a, (a1b, (x_c, (a1d, (xa, (a1f,
   (a1g, (a1h, (x_b, (a1j, (incr_uset a1k,
                             (ema_update_ref x_a a1l,
                               (ema_update_ref x_a a1m,
                                 (incr_conflict_count_since_last_restart a1n,
                                   a2n)))))))))))))))
    end)
    x;

fun is_short_clause_code x =
  (fn xi => fn () => let
                       val xa = len heap_uint32 xi ();
                     in
                       less_eq_nat xa (nat_of_integer (4 : IntInf.int))
                     end)
    x;

fun header_size_fast_code x =
  (fn xi => fn () =>
    let
      val xa = is_short_clause_code xi ();
    in
      (if xa then Uint64.fromInt (4 : IntInf.int)
        else Uint64.fromInt (5 : IntInf.int))
    end)
    x;

fun arl_length_u64_code A_ c = (fn () => let
   val n = arl_length A_ c ();
 in
   uint64_of_nat n
 end);

fun length_u64_code A_ =
  (fn a => (fn () => Uint64.fromFixedInt (Array.length a)));

fun append_and_length_fast_code x =
  (fn ai => fn bia => fn bi =>
    let
      val xa = (if ai then (Word32.fromInt 0) else (Word32.fromInt 1));
    in
      (fn () =>
        let
          val x_b = arl_length_u64_code heap_uint32 bi ();
          val xaa = length_u64_code heap_uint32 bia ();
        in
          let
            val x_d =
              uint32_of_uint64
                (Uint64.minus xaa (Uint64.fromInt (2 : IntInf.int)));
          in
            (fn f_ => fn () => f_ ((is_short_clause_code bia) ()) ())
              (fn xab =>
                (fn f_ => fn () => f_
                  ((if xab
                     then (fn f_ => fn () => f_
                            ((arl_append (default_uint32, heap_uint32) bi xa)
                            ()) ())
                            (fn xb =>
                              (fn f_ => fn () => f_
                                ((arl_append (default_uint32, heap_uint32) xb
                                   (Word32.fromInt 0))
                                ()) ())
                                (fn xc =>
                                  (fn f_ => fn () => f_
                                    ((arl_append (default_uint32, heap_uint32)
                                       xc x_d)
                                    ()) ())
                                    (fn x_g =>
                                      arl_append (default_uint32, heap_uint32)
x_g x_d)))
                     else (fn f_ => fn () => f_
                            ((arl_append (default_uint32, heap_uint32) bi
                               (Word32.fromInt 0))
                            ()) ())
                            (fn xac =>
                              (fn f_ => fn () => f_
                                ((arl_append (default_uint32, heap_uint32) xac
                                   xa)
                                ()) ())
                                (fn xb =>
                                  (fn f_ => fn () => f_
                                    ((arl_append (default_uint32, heap_uint32)
                                       xb (Word32.fromInt 0))
                                    ()) ())
                                    (fn xc =>
                                      (fn f_ => fn () => f_
((arl_append (default_uint32, heap_uint32) xc x_d) ()) ())
(fn x_g => arl_append (default_uint32, heap_uint32) x_g x_d)))))
                  ()) ())
                  (fn x_f =>
                    (fn f_ => fn () => f_
                      ((heap_WHILET
                         (fn (a1, _) =>
                           (fn f_ => fn () => f_
                             ((length_u64_code heap_uint32 bia) ()) ())
                             (fn x_i => (fn () => (Uint64.less a1 x_i))))
                         (fn (a1, a2) =>
                           (fn f_ => fn () => f_
                             ((nth_u64_code heap_uint32 bia a1) ()) ())
                             (fn xb =>
                               (fn f_ => fn () => f_
                                 ((arl_append (default_uint32, heap_uint32) a2
                                    xb)
                                 ()) ())
                                 (fn x_j =>
                                   (fn () =>
                                     (Uint64.plus a1 Uint64.one, x_j)))))
                         (Uint64.zero, x_f))
                      ()) ())
                      (fn (_, a2) =>
                        (fn f_ => fn () => f_ ((header_size_fast_code bia) ())
                          ())
                          (fn xb => (fn () => (a2, Uint64.plus x_b xb))))))
          end
            ()
        end)
    end)
    x;

fun isa_update_lbd_fast_code x =
  (fn ai => fn bia => fn bi =>
    arl_set_u64 heap_uint32 bi
      (Uint64.minus ai (Uint64.fromInt (2 : IntInf.int))) bia)
    x;

fun vmtf_rescore_fast_code x =
  (fn ai => fn _ => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, (_, _)) =>
            (fn f_ => fn () => f_ ((len heap_uint32 ai) ()) ())
              (fn x_a => (fn () => (less_nat a1 x_a))))
          (fn (a1, (a1a, a2a)) =>
            (fn f_ => fn () => f_ ((nth heap_uint32 ai a1) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((isa_vmtf_mark_to_rescore_code (atm_of_code xa) a1a) ()) ())
                  (fn x_a => (fn () => (plus_nat a1 one_nat, (x_a, a2a))))))
          (zero_nata, (bia, bi)) ();
    in
      let
        val (_, aa) = a;
        val (ab, b) = aa;
      in
        (fn () => (ab, b))
      end
        ()
    end)
    x;

fun propagate_bt_wl_D_fast_code x =
  (fn ai => fn bia =>
    fn (a1, (a1a, (a1b, (_, (a1d, (a1e, (a1f,
  (_, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, (a1n,
    (a1o, (a1p, (a1q, a2q))))))))))))))))))
      =>
    fn () =>
    let
      val xa = nth heap_uint32 bia one_nat ();
      val a = vmtf_rescore_fast_code bia a1 a1e a1f ();
    in
      let
        val (a1r, a2r) = a;
      in
        (fn f_ => fn () => f_ ((get_LBD_code a1i) ()) ())
          (fn x_c =>
            (fn f_ => fn () => f_ ((len heap_uint32 bia) ()) ())
              (fn xaa =>
                let
                  val x_f = equal_nat xaa (nat_of_integer (2 : IntInf.int));
                in
                  (fn f_ => fn () => f_
                    ((append_and_length_fast_code false bia a1a) ()) ())
                    (fn (a1s, a2s) =>
                      (fn f_ => fn () => f_
                        ((isa_update_lbd_fast_code a2s x_c a1s) ()) ())
                        (fn x_i =>
                          (fn f_ => fn () => f_
                            ((append_el_aa_u
                               (default_prod default_uint64 default_uint64,
                                 heap_prod heap_uint64 heap_uint64)
                               a1d (uminus_code ai)
                               (to_watcher_fast_code a2s xa x_f))
                            ()) ())
                            (fn x_k =>
                              (fn f_ => fn () => f_
                                ((append_el_aa_u
                                   (default_prod default_uint64 default_uint64,
                                     heap_prod heap_uint64 heap_uint64)
                                   x_k xa
                                   (to_watcher_fast_code a2s (uminus_code ai)
                                     x_f))
                                ()) ())
                                (fn x_m =>
                                  (fn f_ => fn () => f_ ((lbd_empty_code a1i)
                                    ()) ())
                                    (fn x_o =>
                                      (fn f_ => fn () => f_
((isa_length_trail_fast_code a1) ()) ())
(fn x_p =>
  (fn f_ => fn () => f_
    ((cons_trail_Propagated_tr_fast_code (uminus_code ai) a2s a1) ()) ())
    (fn x_r =>
      (fn f_ => fn () => f_ ((isa_vmtf_flush_fast_code x_r a1r) ()) ())
        (fn x_t =>
          (fn f_ => fn () => f_
            ((heap_array_set_u heap_bool a2r (atm_of_code (uminus_code ai))
               (is_pos_code (uminus_code ai)))
            ()) ())
            (fn xb =>
              (fn f_ => fn () => f_
                ((arl_append (default_nat, heap_nat) a1o (nat_of_uint64 a2s))
                ()) ())
                (fn xab =>
                  (fn f_ => fn () => f_
                    ((arl_append (default_nat, heap_nat) a1p
                       (nat_of_uint64 a2s))
                    ()) ())
                    (fn xba =>
                      (fn () =>
                        (x_r, (x_i, (a1b, (x_p,
    (x_m, (x_t, (xb, ((Word32.fromInt 0),
                       (a1h, (x_o, (a1j, (a1k,
   (ema_update_ref x_c a1l,
     (ema_update_ref x_c a1m,
       (incr_conflict_count_since_last_restart a1n,
         (xab, (xba, (suc a1q, a2q))))))))))))))))))))))))))))))
                end))
      end
        ()
    end)
    x;

fun backtrack_wl_D_fast_code x =
  (fn xi => fn () =>
    let
      val xa = lit_of_hd_trail_st_heur_fast_code xi ();
      val a = extract_shorter_conflict_list_heur_st_fast xi ();
    in
      let
        val (a1, (a1a, a2a)) = a;
      in
        (fn f_ => fn () => f_ ((find_decomp_wl_imp_fast_codea a1a a1) ()) ())
          (fn x_c =>
            (fn f_ => fn () => f_ ((len heap_uint32 a2a) ()) ())
              (fn xaa =>
                (if less_nat one_nat xaa
                  then propagate_bt_wl_D_fast_code xa a2a x_c
                  else propagate_unit_bt_wl_D_fast_code xa x_c)))
      end
        ()
    end)
    x;

fun cdcl_twl_o_prog_wl_D_fast_code x =
  (fn xi => fn () =>
    let
      val xa = get_conflict_wl_is_None_fast_code xi ();
    in
      (if xa then decide_wl_or_skip_D_fast_code xi
        else (if Word32.< ((Word32.fromInt 0), count_decided_st_heur xi)
               then (fn f_ => fn () => f_ ((skip_and_resolve_loop_wl_D_fast xi)
                      ()) ())
                      (fn x_b =>
                        (fn f_ => fn () => f_ ((backtrack_wl_D_fast_code x_b)
                          ()) ())
                          (fn x_c =>
                            (fn f_ => fn () => f_
                              ((isasat_current_status_fast_code x_c) ()) ())
                              (fn _ => (fn () => (false, x_c)))))
               else (fn () => (true, xi))))
        ()
    end)
    x;

fun maximum_level_removed_eq_count_dec_code x =
  (fn _ => fn bi =>
    (fn () => (Word32.< ((Word32.fromInt 1), get_count_max_lvls_code bi))))
    x;

fun lit_and_ann_of_propagated_st_heur_code x =
  (fn ((a1a, (_, (_, (a1d, _)))), _) => fn () =>
    let
      val xa = arl_last heap_uint32 a1a ();
      val xaa = arl_last heap_uint32 a1a ();
      val x_a = nth_u_code heap_nat a1d (atm_of_code xaa) ();
    in
      (xa, x_a)
    end)
    x;

fun atm_is_in_conflict_st_heur_fast_code x =
  (fn ai => fn (_, (_, ((_, (_, a2d)), _))) => fn () =>
    let
      val xa = nth_u_code heap_bool a2d (atm_of_code ai) ();
    in
      not (not xa)
    end)
    x;

fun last_trail_code x =
  (fn (a1, (_, (_, (a1c, _)))) => fn () =>
    let
      val xa = arl_last heap_uint32 a1 ();
      val xb = nth_u_code heap_nat a1c (atm_of_code xa) ();
      val x_a = arl_last heap_uint32 a1 ();
    in
      (x_a, (if equal_nat xb one_nat then NONE else SOME xb))
    end)
    x;

fun is_decided_hd_trail_wl_code x =
  (fn (a1, _) => fn () => let
                            val xa = last_trail_code a1 ();
                          in
                            is_None (snd xa)
                          end)
    x;

fun isasat_lookup_merge_eq2_code x =
  (fn ai => fn bif => fn bie => fn bid => fn bic => fn bib => fn bia => fn bi =>
    let
      val (_, a2) = bic;
    in
      (fn () =>
        let
          val xa = isa_arena_lit_code bie bid ();
          val xb =
            (if ((xa : Word32.word) = ai)
              then isa_arena_lit_code bie (plus_nat bid one_nat)
              else isa_arena_lit_code bie bid)
              ();
          val xaa = get_level_code bif xb ();
          val x_b = lbd_write_code bia xaa true ();
          val xab = get_level_code bif xb ();
          val xba = is_in_conflict_code a2 xb ();
          val x_d =
            (if Word32.< (xab, count_decided_pol bif) andalso not xba
              then arl_append (default_uint32, heap_uint32) bi xb
              else (fn () => bi))
              ();
          val xac = get_level_code bif xb ();
          val xbb = is_in_conflict_code a2 xb ();
          val x_h =
            let
              val (a1a, a2a) = a2;
            in
              (fn f_ => fn () => f_ ((nth_u_code heap_bool a2a (atm_of_code xb))
                ()) ())
                (fn xad =>
                  (fn f_ => fn () => f_
                    ((heap_array_set_u heap_bool a2a (atm_of_code xb) true) ())
                    ())
                    (fn x_i =>
                      (fn () =>
                        ((if not xad then Word32.+ (a1a, (Word32.fromInt 1))
                           else a1a),
                          x_i))))
            end
              ();
        in
          ((false, x_h),
            ((if ((xac : Word32.word) = (count_decided_pol bif)) andalso not xbb
               then Word32.+ (bib, (Word32.fromInt 1)) else bib),
              (x_b, x_d)))
        end)
    end)
    x;

fun resolve_merge_conflict_code x =
  (fn ai => fn bie => fn bid => fn bic => fn bib => fn bia => fn bi =>
    let
      val (_, a2) = bic;
    in
      (fn () =>
        let
          val a =
            heap_WHILET
              (fn (a1a, (_, (_, (_, _)))) =>
                (fn f_ => fn () => f_ ((isa_arena_length_code bie bid) ()) ())
                  (fn xa =>
                    (fn () =>
                      (less_nat a1a (plus_nat bid (nat_of_uint64 xa))))))
              (fn (a1a, (a1b, (a1c, (a1d, a2d)))) =>
                (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a) ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((get_level_code ai xa) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((lbd_write_code a1d xb true) ())
                          ())
                          (fn x_a =>
                            (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a)
                              ()) ())
                              (fn xc =>
                                (fn f_ => fn () => f_ ((get_level_code ai xc)
                                  ()) ())
                                  (fn xd =>
                                    (fn f_ => fn () => f_
                                      ((isa_arena_lit_code bie a1a) ()) ())
                                      (fn xaa =>
(fn f_ => fn () => f_ ((is_in_conflict_code a1c xaa) ()) ())
  (fn xab =>
    (fn f_ => fn () => f_
      ((if Word32.< (xd, count_decided_pol ai) andalso not xab
         then (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a) ()) ())
                (arl_append (default_uint32, heap_uint32) a2d)
         else (fn () => a2d))
      ()) ())
      (fn x_c =>
        (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a) ()) ())
          (fn xe =>
            (fn f_ => fn () => f_ ((get_level_code ai xe) ()) ())
              (fn xf =>
                (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a) ()) ())
                  (fn xac =>
                    (fn f_ => fn () => f_ ((is_in_conflict_code a1c xac) ()) ())
                      (fn xad =>
                        (fn f_ => fn () => f_
                          (let
                             val (a1e, a2e) = a1c;
                           in
                             (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a)
                               ()) ())
                               (fn xg =>
                                 (fn f_ => fn () => f_
                                   ((nth_u_code heap_bool a2e (atm_of_code xg))
                                   ()) ())
                                   (fn xh =>
                                     (fn f_ => fn () => f_
                                       ((isa_arena_lit_code bie a1a) ()) ())
                                       (fn xae =>
 (fn f_ => fn () => f_ ((isa_arena_lit_code bie a1a) ()) ())
   (fn _ =>
     (fn f_ => fn () => f_
       ((heap_array_set_u heap_bool a2e (atm_of_code xae) true) ()) ())
       (fn x_h =>
         (fn () =>
           ((if not xh then Word32.+ (a1e, (Word32.fromInt 1)) else a1e),
             x_h)))))))
                           end
                          ()) ())
                          (fn x_g =>
                            (fn () =>
                              (suc a1a,
                                ((if ((xf : Word32.word) = (count_decided_pol
                     ai)) andalso
                                       not xad
                                   then Word32.+ (a1b, (Word32.fromInt 1))
                                   else a1b),
                                  (x_g, (x_a, x_c)))))))))))))))))))
              (plus_nat bid one_nat, (bib, (a2, (bia, bi)))) ();
        in
          let
            val (_, (a1b, (a1c, (a1d, a2d)))) = a;
          in
            (fn () => ((false, a1c), (a1b, (a1d, a2d))))
          end
            ()
        end)
    end)
    x;

fun isa_mark_used_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        arl_get heap_uint32 ai
          (fast_minus_nat bi (nat_of_integer (4 : IntInf.int))) ();
    in
      arl_set heap_uint32 ai
        (fast_minus_nat bi (nat_of_integer (4 : IntInf.int)))
        (Word32.orb (xa, Word32.fromLargeInt (IntInf.toLarge (4 : IntInf.int))))
        ()
    end)
    x;

fun tl_trail_tr_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = arl_last heap_uint32 a1 ();
      val xaa = heap_array_set_u heap_uint32 a1a xa uNSET_code ();
      val xab = heap_array_set_u heap_uint32 xaa (uminus_code xa) uNSET_code ();
      val xb =
        heap_array_set_u heap_uint32 a1b (atm_of_code xa) (Word32.fromInt 0) ();
      val xc = nth_u_code heap_nat a1c (atm_of_code xa) ();
      val xd = nth_u_code heap_nat a1c (atm_of_code xa) ();
    in
      (arl_butlast_nonresizing a1,
        (xab, (xb, (a1c, ((if equal_nat xc one_nat
                            then fast_minus_uint32 a1d (Word32.fromInt 1)
                            else a1d),
                           (if equal_nat xd one_nat
                             then arl_butlast_nonresizing a2d else a2d))))))
    end)
    x;

fun update_confl_tl_wl_code x =
  (fn ai => fn bia =>
    fn (a1, (a1a, ((a1c, (a1d, a2d)),
                    (a1e, (a1f, (a1g, (a1h,
(a1i, (a1j, (a1k, (a1l, a2l)))))))))))
      =>
    fn () =>
    let
      val xa = isa_arena_length_code a1a ai ();
      val a =
        (if ((xa : Uint64.uint64) = (Uint64.fromInt (2 : IntInf.int)))
          then isasat_lookup_merge_eq2_code bia a1 a1a ai (a1c, (a1d, a2d)) a1i
                 a1k a1l
          else resolve_merge_conflict_code a1 a1a ai (a1c, (a1d, a2d)) a1i a1k
                 a1l)
          ();
    in
      let
        val ((a1n, (a1o, a2o)), (a1p, (a1q, a2q))) = a;
      in
        (fn f_ => fn () => f_ ((conflict_remove1_code bia (a1o, a2o)) ()) ())
          (fn (a1r, a2r) =>
            (fn f_ => fn () => f_ ((isa_mark_used_code a1a ai) ()) ())
              (fn x_e =>
                (fn f_ => fn () => f_ ((isa_arena_incr_act_code x_e ai) ()) ())
                  (fn x_g =>
                    (fn f_ => fn () => f_ ((tl_trail_tr_code a1) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_
                          ((isa_vmtf_unset_code (atm_of_code bia) a1g) ()) ())
                          (fn xaa =>
                            (fn () =>
                              (false,
                                (xb, (x_g, ((a1n, (a1r, a2r)),
     (a1e, (a1f, (xaa, (a1h, (fast_minus_uint32 a1p (Word32.fromInt 1),
                               (a1j, (a1q, (a2q, a2l))))))))))))))))))
      end
        ()
    end)
    x;

fun tl_state_wl_heur_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) => fn () =>
    let
      val xa = lit_of_last_trail_code a1 ();
      val x_a = tl_trail_tr_code a1 ();
      val xb = isa_vmtf_unset_code (atm_of_code xa) a1e ();
    in
      (x_a, (a1a, (a1b, (a1c, (a1d, (xb, (a1f, a2f)))))))
    end)
    x;

fun skip_and_resolve_loop_wl_D x =
  (fn xi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (if not a1
              then (fn f_ => fn () => f_ ((is_decided_hd_trail_wl_code a2) ())
                     ())
                     (fn x_b => (fn () => (not x_b)))
              else (fn () => false)))
          (fn (_, a2) =>
            (fn f_ => fn () => f_ ((lit_and_ann_of_propagated_st_heur_code a2)
              ()) ())
              (fn (a1a, a2a) =>
                (fn f_ => fn () => f_
                  ((atm_is_in_conflict_st_heur_fast_code (uminus_code a1a) a2)
                  ()) ())
                  (fn xa =>
                    (if not xa
                      then (fn f_ => fn () => f_ ((tl_state_wl_heur_code a2) ())
                             ())
                             (fn x_e => (fn () => (false, x_e)))
                      else (fn f_ => fn () => f_
                             ((maximum_level_removed_eq_count_dec_code
                                (uminus_code a1a) a2)
                             ()) ())
                             (fn x_d =>
                               (if x_d then update_confl_tl_wl_code a2a a1a a2
                                 else (fn () => (true, a2))))))))
          (false, xi) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun isasat_current_status_code x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (_, (_, (_, (_, (_,
  (_, (_, (_, (a1k, (_, (_, (_, (_, (_, (a1q, _))))))))))))))))))
          = xi;
      in
        isasat_current_information a1k a1q
      end))
    x;

fun defined_atm_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, _))) = ai;
    in
      (fn () =>
        let
          val xa = nth_u_code heap_uint32 a1a (Word32.* (two_uint32, bi)) ();
        in
          not ((xa : Word32.word) = uNSET_code)
        end)
    end)
    x;

fun vmtf_find_next_undef_code x =
  (fn ai => fn bi =>
    let
      val ((a1a, a), _) = ai;
      val (_, aa) = a;
      val (_, ab) = aa;
      val (_, ac) = ab;
    in
      heap_WHILET
        (fn s =>
          (if not (is_None s) then defined_atm_code bi (the s)
            else (fn () => false)))
        (fn s => fn () =>
          let
            val x_b =
              nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) a1a (the s)
                ();
          in
            get_next x_b
          end)
        ac
    end)
    x;

fun vmtf_find_next_undef_upd_code x =
  (fn ai => fn bi => fn () => let
                                val xa = vmtf_find_next_undef_code bi ai ();
                              in
                                ((ai, update_next_search xa bi), xa)
                              end)
    x;

fun find_unassigned_lit_wl_D_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) => fn () =>
    let
      val a = vmtf_find_next_undef_upd_code a1 a1e ();
    in
      let
        val ((a1h, a2h), a2g) = a;
      in
        (fn f_ => fn () => f_ ((lit_of_found_atm_D_code a1f a2g) ()) ())
          (fn x_a =>
            (fn () =>
              ((a1h, (a1a, (a1b, (a1c, (a1d, (a2h, (a1f, a2f))))))), x_a)))
      end
        ()
    end)
    x;

fun cons_trail_Decided_tr_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = arl_length heap_uint32 a1 ();
      val x_a = arl_append (default_uint32, heap_uint32) a1 ai ();
      val xaa = heap_array_set_u heap_uint32 a1a ai sET_TRUE_code ();
      val xab =
        heap_array_set_u heap_uint32 xaa (uminus_code ai) sET_FALSE_code ();
      val xb =
        heap_array_set_u heap_uint32 a1b (atm_of_code ai)
          (Word32.+ (a1d, (Word32.fromInt 1))) ();
      val xc = heap_array_set_u heap_nat a1c (atm_of_code ai) one_nat ();
      val xd =
        arl_append (default_uint32, heap_uint32) a2d (uint32_of_nat xa) ();
    in
      (x_a, (xab, (xb, (xc, (Word32.+ (a1d, (Word32.fromInt 1)), xd)))))
    end)
    x;

fun decide_lit_wl_code x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (_, (a1d, (a1e, (a1f,
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, a2l)))))))))))))
      =>
    fn () =>
    let
      val xa = isa_length_trail_code a1 ();
      val x_b = cons_trail_Decided_tr_code ai a1 ();
    in
      (x_b, (a1a, (a1b, (xa, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (incr_decision a1k, (a1l, a2l)))))))))))))
    end)
    x;

fun decide_wl_or_skip_D_code x =
  (fn xi => fn () =>
    let
      val a = find_unassigned_lit_wl_D_code xi ();
    in
      (case a of (a1, NONE) => (fn () => (true, a1))
        | (a1, SOME x_a) =>
          (fn f_ => fn () => f_ ((decide_lit_wl_code x_a a1) ()) ())
            (fn x_b => (fn () => (false, x_b))))
        ()
    end)
    x;

fun lit_redundant_reason_stack_wl_lookup_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = isa_arena_length_code bia bi ();
    in
      (if less_nat (nat_of_integer (2 : IntInf.int)) (nat_of_uint64 xa)
        then (fn () => (to_ana_ref bi (Word32.fromInt 1) false))
        else (fn f_ => fn () => f_ ((isa_arena_lit_code bia bi) ()) ())
               (fn xb =>
                 (fn () =>
                   (if ((xb : Word32.word) = ai)
                     then to_ana_ref bi (Word32.fromInt 1) false
                     else to_ana_ref bi (Word32.fromInt 0) true))))
        ()
    end)
    x;

fun isa_get_literal_and_remove_of_analyse_wl_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = arl_last (heap_prod heap_nat heap_uint64) bi ();
    in
      let
        val (a1, (a1a, a2a)) = from_ana_ref xa;
      in
        (fn f_ => fn () => f_
          ((isa_arena_lit_code ai (plus_nat a1 (nat_of_uint32 a1a))) ()) ())
          (fn x_a =>
            (fn f_ => fn () => f_
              ((arl_length (heap_prod heap_nat heap_uint64) bi) ()) ())
              (fn xb =>
                (fn f_ => fn () => f_
                  ((arl_set (heap_prod heap_nat heap_uint64) bi
                     (fast_minus_nat xb one_nat)
                     (to_ana_ref a1 (Word32.+ (a1a, (Word32.fromInt 1))) a2a))
                  ()) ())
                  (fn x_b => (fn () => (x_a, x_b)))))
      end
        ()
    end)
    x;

fun isa_mark_failed_lits_stack_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = arl_length (heap_prod heap_nat heap_uint64) bia ();
      val a =
        heap_WHILET (fn (a1, _) => (fn () => (less_nat a1 xa)))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((arl_get (heap_prod heap_nat heap_uint64) bia a1) ()) ())
              (fn xb =>
                let
                  val (a1a, (a1b, _)) = from_ana_ref xb;
                in
                  (fn f_ => fn () => f_
                    (let
                       val (a1c, a2c) = a2;
                     in
                       (fn f_ => fn () => f_
                         ((isa_arena_lit_code ai
                            (minus_nata (plus_nat a1a (nat_of_uint32 a1b))
                              one_nat))
                         ()) ())
                         (fn xc =>
                           (fn f_ => fn () => f_
                             ((heap_array_set_u heap_minimize_status a1c
                                (atm_of_code xc) SEEN_FAILED)
                             ()) ())
                             (fn x_e =>
                               (fn f_ => fn () => f_
                                 ((isa_arena_lit_code ai
                                    (minus_nata
                                      (plus_nat a1a (nat_of_uint32 a1b))
                                      one_nat))
                                 ()) ())
                                 (fn xd =>
                                   (fn f_ => fn () => f_
                                     ((arl_append (default_uint32, heap_uint32)
a2c (atm_of_code xd))
                                     ()) ())
                                     (fn x_f => (fn () => (x_e, x_f))))))
                     end
                    ()) ())
                    (fn x_e => (fn () => (plus_nat a1 one_nat, x_e)))
                end))
          (zero_nata, bi) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun ana_lookup_conv_lookup_code x =
  (fn ai => fn (a1, (a1a, a2a)) => fn () =>
    let
      val xa =
        (if a2a then (fn () => Uint64.one) else isa_arena_length_code ai a1) ();
    in
      (a1, ((if a2a then Uint64.one else Uint64.zero),
             (uint64_of_uint32 a1a, xa)))
    end)
    x;

fun get_propagation_reason_code x =
  (fn ai => fn bi =>
    let
      val (_, (_, (_, (a1c, _)))) = ai;
    in
      (fn () => let
                  val xa = nth_u_code heap_nat a1c (atm_of_code bi) ();
                in
                  (if equal_nat xa one_nat then NONE else SOME xa)
                end)
    end)
    x;

fun lit_redundant_rec_wl_lookup_code x =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi =>
    heap_WHILET
      (fn (_, (a1a, _)) => fn () =>
        let
          val x_a = arl_is_empty (heap_prod heap_nat heap_uint64) a1a ();
        in
          not x_a
        end)
      (fn (a1, (a1a, _)) => fn () =>
        let
          val xa = arl_last (heap_prod heap_nat heap_uint64) a1a ();
          val a = ana_lookup_conv_lookup_code bid (from_ana_ref xa) ();
        in
          let
            val (a1b, (a1c, (a1d, a2d))) = a;
          in
            (if Uint64.less_eq a2d a1d
              then (fn f_ => fn () => f_
                     ((isa_arena_lit_code bid
                        (plus_nat a1b (nat_of_uint64 a1c)))
                     ()) ())
                     (fn xb =>
                       (fn f_ => fn () => f_
                         ((conflict_min_cach_set_removable_l_code a1
                            (atm_of_code xb))
                         ()) ())
                         (fn x_d =>
                           (fn () =>
                             (x_d, (arl_butlast_nonresizing a1a, true)))))
              else (fn f_ => fn () => f_
                     ((isa_get_literal_and_remove_of_analyse_wl_code bid a1a)
                     ()) ())
                     (fn (a1e, a2e) =>
                       (fn f_ => fn () => f_ ((get_level_code ai a1e) ()) ())
                         (fn xb =>
                           (fn f_ => fn () => f_ ((level_in_lbd_code xb bi) ())
                             ())
                             (fn xc =>
                               (fn f_ => fn () => f_ ((get_level_code ai a1e)
                                 ()) ())
                                 (fn xaa =>
                                   (fn f_ => fn () => f_
                                     ((conflict_min_cach_l_code a1
(atm_of_code a1e))
                                     ()) ())
                                     (fn xba =>
                                       (fn f_ => fn () => f_
 ((atm_in_conflict_code (atm_of_code a1e) bic) ()) ())
 (fn xca =>
   (if ((xaa : Word32.word) = (Word32.fromInt 0)) orelse
         (equal_minimize_status xba SEEN_REMOVABLE orelse xca)
     then (fn () => (a1, (a2e, false)))
     else (fn f_ => fn () => f_ ((conflict_min_cach_l_code a1 (atm_of_code a1e))
            ()) ())
            (fn xab =>
              (if not xc orelse equal_minimize_status xab SEEN_FAILED
                then (fn f_ => fn () => f_
                       ((isa_mark_failed_lits_stack_code bid a2e a1) ()) ())
                       (fn x_j =>
                         (fn f_ => fn () => f_
                           ((arl_empty
                              (default_prod default_nat default_uint64,
                                heap_prod heap_nat heap_uint64)
                              zero_nat)
                           ()) ())
                           (fn xd => (fn () => (x_j, (xd, false)))))
                else (fn f_ => fn () => f_
                       ((get_propagation_reason_code ai (uminus_code a1e)) ())
                       ())
                       (fn aa =>
                         (case aa
                           of NONE =>
                             (fn f_ => fn () => f_
                               ((isa_mark_failed_lits_stack_code bid a2e a1) ())
                               ())
                               (fn x_k =>
                                 (fn f_ => fn () => f_
                                   ((arl_empty
                                      (default_prod default_nat default_uint64,
heap_prod heap_nat heap_uint64)
                                      zero_nat)
                                   ()) ())
                                   (fn xd => (fn () => (x_k, (xd, false)))))
                           | SOME x_k =>
                             (fn f_ => fn () => f_
                               ((lit_redundant_reason_stack_wl_lookup_code
                                  (uminus_code a1e) bid x_k)
                               ()) ())
                               (fn xd =>
                                 (fn f_ => fn () => f_
                                   ((arl_append
                                      (default_prod default_nat default_uint64,
heap_prod heap_nat heap_uint64)
                                      a2e xd)
                                   ()) ())
                                   (fn xe =>
                                     (fn () => (a1, (xe, false)))))))))))))))))
          end
            ()
        end)
      (bib, (bia, false)))
    x;

fun literal_redundant_wl_lookup_code x =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = get_level_code ai bia ();
      val xaa = conflict_min_cach_l_code bib (atm_of_code bia) ();
    in
      (if ((xa : Word32.word) = (Word32.fromInt 0)) orelse
            equal_minimize_status xaa SEEN_REMOVABLE
        then (fn f_ => fn () => f_
               ((arl_empty
                  (default_prod default_nat default_uint64,
                    heap_prod heap_nat heap_uint64)
                  zero_nat)
               ()) ())
               (fn xb => (fn () => (bib, (xb, true))))
        else (fn f_ => fn () => f_
               ((conflict_min_cach_l_code bib (atm_of_code bia)) ()) ())
               (fn xb =>
                 (if equal_minimize_status xb SEEN_FAILED
                   then (fn f_ => fn () => f_
                          ((arl_empty
                             (default_prod default_nat default_uint64,
                               heap_prod heap_nat heap_uint64)
                             zero_nat)
                          ()) ())
                          (fn xc => (fn () => (bib, (xc, false))))
                   else (fn f_ => fn () => f_
                          ((get_propagation_reason_code ai (uminus_code bia))
                          ()) ())
                          (fn a =>
                            (case a
                              of NONE =>
                                (fn f_ => fn () => f_
                                  ((arl_empty
                                     (default_prod default_nat default_uint64,
                                       heap_prod heap_nat heap_uint64)
                                     zero_nat)
                                  ()) ())
                                  (fn xc => (fn () => (bib, (xc, false))))
                              | SOME x_c =>
                                (fn f_ => fn () => f_
                                  ((arl_empty
                                     (default_prod default_nat default_uint64,
                                       heap_prod heap_nat heap_uint64)
                                     zero_nat)
                                  ()) ())
                                  (fn xc =>
                                    (fn f_ => fn () => f_
                                      ((lit_redundant_reason_stack_wl_lookup_code
 (uminus_code bia) bid x_c)
                                      ()) ())
                                      (fn xab =>
(fn f_ => fn () => f_
  ((arl_append
     (default_prod default_nat default_uint64, heap_prod heap_nat heap_uint64)
     xc xab)
  ()) ())
  (fn x_d => lit_redundant_rec_wl_lookup_code ai bid bic bib x_d bi))))))))
        ()
    end)
    x;

fun minimize_and_extract_highest_lookup_conflict_code x =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (_, (a1a, (_, a2b))) =>
            (fn f_ => fn () => f_ ((length_arl_u_code heap_uint32 a2b) ()) ())
              (fn x_a => (fn () => (Word32.< (a1a, x_a)))))
          (fn (a1, (a1a, (a1b, a2b))) =>
            (fn f_ => fn () => f_
              (((fn () => Array.sub ((fn (a,b) => a) (a2b),
                 Word32.toInt (a1a))))
              ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_
                  ((literal_redundant_wl_lookup_code ai bid a1 a1b x_a bia) ())
                  ())
                  (fn (a1c, (_, a2d)) =>
                    (if not a2d
                      then (fn () =>
                             (a1, (Word32.+ (a1a, (Word32.fromInt 1)),
                                    (a1c, a2b))))
                      else (fn f_ => fn () => f_ ((conflict_remove1_code x_a a1)
                             ()) ())
                             (fn x_e =>
                               (fn f_ => fn () => f_
                                 ((delete_index_and_swap_code a2b a1a) ()) ())
                                 (fn xa =>
                                   (fn () => (x_e, (a1a, (a1c, xa))))))))))
          (bic, ((Word32.fromInt 1), (bib, bi))) ();
    in
      let
        val (a1, (_, (a1b, a2b))) = a;
      in
        (fn () => (a1, (a1b, a2b)))
      end
        ()
    end)
    x;

fun empty_conflict_and_extract_clause_heur_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = arl_length heap_uint32 bi ();
      val xaa = arl_get heap_uint32 bi zero_nata ();
      val xb = new heap_uint32 xa xaa ();
      val a =
        heap_WHILET
          (fn (_, (_, a2a)) =>
            (fn f_ => fn () => f_ ((length_arl_u_code heap_uint32 bi) ()) ())
              (fn x_c => (fn () => (Word32.< (a2a, x_c)))))
          (fn (a1, (a1a, a2a)) =>
            (fn f_ => fn () => f_
              (((fn () => Array.sub ((fn (a,b) => a) (bi), Word32.toInt (a2a))))
              ()) ())
              (fn xc =>
                (fn f_ => fn () => f_ ((conflict_remove1_code xc a1) ()) ())
                  (fn x_c =>
                    (fn f_ => fn () => f_
                      (((fn () => Array.sub ((fn (a,b) => a) (bi),
                         Word32.toInt (a2a))))
                      ()) ())
                      (fn xd =>
                        (fn f_ => fn () => f_
                          ((heap_array_set_u heap_uint32 a1a a2a xd) ()) ())
                          (fn x_e =>
                            (fn f_ => fn () => f_
                              ((nth_u_code heap_uint32 x_e (Word32.fromInt 1))
                              ()) ())
                              (fn xe =>
                                (fn f_ => fn () => f_ ((get_level_code ai xe)
                                  ()) ())
                                  (fn xf =>
                                    (fn f_ => fn () => f_
                                      ((nth_u_code heap_uint32 x_e a2a) ()) ())
                                      (fn xab =>
(fn f_ => fn () => f_ ((get_level_code ai xab) ()) ())
  (fn xac =>
    (fn f_ => fn () => f_
      ((if Word32.< (xf, xac)
         then swap_u_code heap_uint32 x_e (Word32.fromInt 1) a2a
         else (fn () => x_e))
      ()) ())
      (fn x_g =>
        (fn () => (x_c, (x_g, Word32.+ (a2a, (Word32.fromInt 1)))))))))))))))
          (bia, (xb, (Word32.fromInt 1))) ();
    in
      let
        val (a1, (a1a, _)) = a;
      in
        (fn f_ => fn () => f_ ((arl_length heap_uint32 bi) ()) ())
          (fn xc =>
            (fn f_ => fn () => f_
              ((if equal_nat xc one_nat then (fn () => (Word32.fromInt 0))
                 else (fn f_ => fn () => f_ ((nth heap_uint32 a1a one_nat) ())
                        ())
                        (get_level_code ai))
              ()) ())
              (fn xd => (fn () => ((true, a1), (a1a, xd)))))
      end
        ()
    end)
    x;

fun vmtf_mark_to_rescore_clause_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = isa_arena_length_code ai bia ();
    in
      imp_for bia (plus_nat bia (nat_of_uint64 xa))
        (fn xaa => fn sigma =>
          (fn f_ => fn () => f_ ((isa_arena_lit_code ai xaa) ()) ())
            (fn xb => isa_vmtf_mark_to_rescore_code (atm_of_code xb) sigma))
        bi ()
    end)
    x;

fun vmtf_mark_to_rescore_also_reasons_code x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = arl_length heap_uint32 bia ();
    in
      imp_for zero_nata xa
        (fn xaa => fn sigma =>
          (fn f_ => fn () => f_ ((arl_get heap_uint32 bia xaa) ()) ())
            (fn xb =>
              (fn f_ => fn () => f_
                ((get_the_propagation_reason_code ai (uminus_code xb)) ()) ())
                (fn a =>
                  (case a
                    of NONE =>
                      (fn f_ => fn () => f_ ((arl_get heap_uint32 bia xaa) ())
                        ())
                        (fn xc =>
                          isa_vmtf_mark_to_rescore_code (atm_of_code xc) sigma)
                    | SOME x_c =>
                      (if equal_nat x_c zero_nata then (fn () => sigma)
                        else vmtf_mark_to_rescore_clause_code bib x_c sigma)))))
        bi ()
    end)
    x;

fun extract_shorter_conflict_list_heur_st_code x =
  (fn (a1, (a1a, ((_, a2c),
                   (a1d, (a1e, (a1f, (a1g, (a1h,
     (a1i, (a1j, (a1k, (a1l, (a1m, a2m)))))))))))))
     =>
    fn () =>
    let
      val xa = lit_of_last_trail_code a1 ();
      val x_b = conflict_remove1_code (uminus_code xa) a2c ();
      val x_d = arl_set heap_uint32 a1k zero_nata (uminus_code xa) ();
      val x_f = vmtf_mark_to_rescore_also_reasons_code a1 a1a x_d a1f ();
      val a =
        minimize_and_extract_highest_lookup_conflict_code a1 a1a x_b a1i a1j x_d
          ();
    in
      let
        val (a1n, (a1o, a2o)) = a;
      in
        (fn f_ => fn () => f_ ((empty_cach_code a1o) ()) ())
          (fn x_h =>
            (fn f_ => fn () => f_
              ((empty_conflict_and_extract_clause_heur_code a1 a1n a2o) ()) ())
              (fn (a1p, (a1q, a2q)) =>
                (fn () =>
                  ((a1, (a1a, (a1p, (a1d, (a1e,
    (x_f, (a1g, (a1h, (x_h, (a1j, (let
                                     val (aa, _) = a2o;
                                   in
                                     (aa, one_nat)
                                   end,
                                    (a1l, (a1m, a2m))))))))))))),
                    (a2q, a1q)))))
      end
        ()
    end)
    x;

fun lit_of_hd_trail_st_heur_code x =
  (fn (a1, (_, (_, (_, (_, (_, _)))))) => lit_of_last_trail_code a1) x;

fun vmtf_enqueue_code x =
  (fn ai => fn bia => fn (a1, (a1a, (a1b, (a1c, a2c)))) => fn () =>
    let
      val xa = defined_atm_code ai bia ();
    in
      (case a1b
        of NONE =>
          (fn f_ => fn () => f_
            ((heap_array_set_u (heap_vmtf_node heap_uint32 heap_uint64) a1 bia
               (VMTF_Node (a1a, a1b, NONE)))
            ()) ())
            (fn x_a =>
              (fn () =>
                (x_a, (Uint64.plus a1a Uint64.one,
                        (bia, (bia, (if xa then NONE else SOME bia)))))))
        | SOME x_a =>
          (fn f_ => fn () => f_
            ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) a1 x_a) ())
            ())
            (fn xaa =>
              (fn f_ => fn () => f_
                ((nth_u_code (heap_vmtf_node heap_uint32 heap_uint64) a1 x_a)
                ()) ())
                (fn xb =>
                  (fn f_ => fn () => f_
                    ((heap_array_set_u (heap_vmtf_node heap_uint32 heap_uint64)
                       a1 bia
                       (VMTF_Node (Uint64.plus a1a Uint64.one, NONE, SOME x_a)))
                    ()) ())
                    (fn xc =>
                      (fn f_ => fn () => f_
                        ((heap_array_set_u
                           (heap_vmtf_node heap_uint32 heap_uint64) xc x_a
                           (VMTF_Node (stamp xaa, SOME bia, get_next xb)))
                        ()) ())
                        (fn x_c =>
                          (fn () =>
                            (x_c, (Uint64.plus a1a Uint64.one,
                                    (bia, (the a1c,
    (if xa then a2c else SOME bia)))))))))))
        ()
    end)
    x;

fun vmtf_en_dequeue_code x =
  (fn ai => fn bia => fn bi => fn () => let
  val xa = vmtf_dequeue_code bia bi ();
in
  vmtf_enqueue_code ai bia xa ()
end)
    x;

fun isa_vmtf_flush_code x =
  (fn ai => fn (a1, (a1a, a2a)) => fn () =>
    let
      val xa = quicksort_vmtf_nth_code a1 a1a ();
      val xaa = arl_length heap_uint32 xa ();
      val x_a =
        (if less_eq_nat (nat_of_integer (18446744073709551615 : IntInf.int))
              (plus_nat xaa (nat_of_uint64 (current_stamp a1)))
          then vmtf_rescale_code a1 else (fn () => a1))
          ();
      val a =
        heap_WHILET
          (fn (a1b, (_, _)) =>
            (fn f_ => fn () => f_ ((length_arl_u_code heap_uint32 xa) ()) ())
              (fn x_c => (fn () => (Word32.< (a1b, x_c)))))
          (fn (a1b, (a1c, a2c)) =>
            (fn f_ => fn () => f_
              (((fn () => Array.sub ((fn (a,b) => a) (xa), Word32.toInt (a1b))))
              ()) ())
              (fn xab =>
                (fn f_ => fn () => f_ ((vmtf_en_dequeue_code ai xab a1c) ()) ())
                  (fn x_c =>
                    (fn f_ => fn () => f_
                      (((fn () => Array.sub ((fn (a,b) => a) (xa),
                         Word32.toInt (a1b))))
                      ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((atoms_hash_del_code xb a2c) ())
                          ())
                          (fn xc =>
                            (fn () =>
                              (Word32.+ (a1b, (Word32.fromInt 1)),
                                (x_c, xc))))))))
          ((Word32.fromInt 0), (x_a, a2a)) ();
    in
      let
        val (_, (a1c, a2c)) = a;
      in
        (fn () => (a1c, (emptied_arl xa, a2c)))
      end
        ()
    end)
    x;

fun propagate_unit_bt_wl_D_code x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (_, (a1d, (a1e, (a1f,
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, (a1n, a2n)))))))))))))))
      =>
    fn () =>
    let
      val xa = isa_vmtf_flush_code a1 a1e ();
      val x_a = get_LBD_code a1i ();
      val x_b = lbd_empty_code a1i ();
      val x_c = isa_length_trail_code a1 ();
      val x_e = cons_trail_Propagated_tr_code (uminus_code ai) zero_nata a1 ();
    in
      (x_e, (a1a, (a1b, (x_c, (a1d, (xa, (a1f,
   (a1g, (a1h, (x_b, (a1j, (incr_uset a1k,
                             (ema_update_ref x_a a1l,
                               (ema_update_ref x_a a1m,
                                 (incr_conflict_count_since_last_restart a1n,
                                   a2n)))))))))))))))
    end)
    x;

fun header_size_code x =
  (fn xi => fn () =>
    let
      val xa = is_short_clause_code xi ();
    in
      (if xa then nat_of_integer (4 : IntInf.int)
        else nat_of_integer (5 : IntInf.int))
    end)
    x;

fun append_and_length_code x =
  (fn ai => fn bia => fn bi =>
    let
      val xa = (if ai then (Word32.fromInt 0) else (Word32.fromInt 1));
    in
      (fn () =>
        let
          val x_b = arl_length heap_uint32 bi ();
          val xaa = length_u64_code heap_uint32 bia ();
        in
          let
            val x_d =
              uint32_of_uint64
                (Uint64.minus xaa (Uint64.fromInt (2 : IntInf.int)));
          in
            (fn f_ => fn () => f_ ((is_short_clause_code bia) ()) ())
              (fn xab =>
                (fn f_ => fn () => f_
                  ((if xab
                     then (fn f_ => fn () => f_
                            ((arl_append (default_uint32, heap_uint32) bi xa)
                            ()) ())
                            (fn xb =>
                              (fn f_ => fn () => f_
                                ((arl_append (default_uint32, heap_uint32) xb
                                   (Word32.fromInt 0))
                                ()) ())
                                (fn xc =>
                                  (fn f_ => fn () => f_
                                    ((arl_append (default_uint32, heap_uint32)
                                       xc x_d)
                                    ()) ())
                                    (fn x_g =>
                                      arl_append (default_uint32, heap_uint32)
x_g x_d)))
                     else (fn f_ => fn () => f_
                            ((arl_append (default_uint32, heap_uint32) bi
                               (Word32.fromInt 0))
                            ()) ())
                            (fn xac =>
                              (fn f_ => fn () => f_
                                ((arl_append (default_uint32, heap_uint32) xac
                                   xa)
                                ()) ())
                                (fn xb =>
                                  (fn f_ => fn () => f_
                                    ((arl_append (default_uint32, heap_uint32)
                                       xb (Word32.fromInt 0))
                                    ()) ())
                                    (fn xc =>
                                      (fn f_ => fn () => f_
((arl_append (default_uint32, heap_uint32) xc x_d) ()) ())
(fn x_g => arl_append (default_uint32, heap_uint32) x_g x_d)))))
                  ()) ())
                  (fn x_f =>
                    (fn f_ => fn () => f_
                      ((heap_WHILET
                         (fn (a1, _) =>
                           (fn f_ => fn () => f_
                             ((length_u64_code heap_uint32 bia) ()) ())
                             (fn x_i => (fn () => (Uint64.less a1 x_i))))
                         (fn (a1, a2) =>
                           (fn f_ => fn () => f_
                             ((nth_u64_code heap_uint32 bia a1) ()) ())
                             (fn xb =>
                               (fn f_ => fn () => f_
                                 ((arl_append (default_uint32, heap_uint32) a2
                                    xb)
                                 ()) ())
                                 (fn x_j =>
                                   (fn () =>
                                     (Uint64.plus a1 Uint64.one, x_j)))))
                         (Uint64.zero, x_f))
                      ()) ())
                      (fn (_, a2) =>
                        (fn f_ => fn () => f_ ((header_size_code bia) ()) ())
                          (fn xb => (fn () => (a2, plus_nat x_b xb))))))
          end
            ()
        end)
    end)
    x;

fun isa_update_lbd_code x =
  (fn ai => fn bia => fn bi =>
    arl_set heap_uint32 bi (minus_nata ai (nat_of_integer (2 : IntInf.int)))
      bia)
    x;

fun vmtf_rescore_code x =
  (fn ai => fn _ => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, (_, _)) =>
            (fn f_ => fn () => f_ ((len heap_uint32 ai) ()) ())
              (fn x_a => (fn () => (less_nat a1 x_a))))
          (fn (a1, (a1a, a2a)) =>
            (fn f_ => fn () => f_ ((nth heap_uint32 ai a1) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((isa_vmtf_mark_to_rescore_code (atm_of_code xa) a1a) ()) ())
                  (fn x_a => (fn () => (plus_nat a1 one_nat, (x_a, a2a))))))
          (zero_nata, (bia, bi)) ();
    in
      let
        val (_, aa) = a;
        val (ab, b) = aa;
      in
        (fn () => (ab, b))
      end
        ()
    end)
    x;

fun propagate_bt_wl_D_code x =
  (fn ai => fn bia =>
    fn (a1, (a1a, (a1b, (_, (a1d, (a1e, (a1f,
  (_, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, (a1n,
    (a1o, (a1p, (a1q, a2q))))))))))))))))))
      =>
    fn () =>
    let
      val xa = nth heap_uint32 bia one_nat ();
      val a = vmtf_rescore_code bia a1 a1e a1f ();
    in
      let
        val (a1r, a2r) = a;
      in
        (fn f_ => fn () => f_ ((get_LBD_code a1i) ()) ())
          (fn x_c =>
            (fn f_ => fn () => f_ ((length_u_code heap_uint32 bia) ()) ())
              (fn xaa =>
                let
                  val x_f = ((xaa : Word32.word) = two_uint32);
                in
                  (fn f_ => fn () => f_ ((append_and_length_code false bia a1a)
                    ()) ())
                    (fn (a1s, a2s) =>
                      (fn f_ => fn () => f_ ((isa_update_lbd_code a2s x_c a1s)
                        ()) ())
                        (fn x_i =>
                          (fn f_ => fn () => f_
                            ((append_el_aa_u
                               (default_prod default_nat default_uint64,
                                 heap_prod heap_nat heap_uint64)
                               a1d (uminus_code ai)
                               (to_watcher_code a2s xa x_f))
                            ()) ())
                            (fn x_k =>
                              (fn f_ => fn () => f_
                                ((append_el_aa_u
                                   (default_prod default_nat default_uint64,
                                     heap_prod heap_nat heap_uint64)
                                   x_k xa
                                   (to_watcher_code a2s (uminus_code ai) x_f))
                                ()) ())
                                (fn x_m =>
                                  (fn f_ => fn () => f_ ((lbd_empty_code a1i)
                                    ()) ())
                                    (fn x_o =>
                                      (fn f_ => fn () => f_
((isa_length_trail_code a1) ()) ())
(fn x_p =>
  (fn f_ => fn () => f_ ((cons_trail_Propagated_tr_code (uminus_code ai) a2s a1)
    ()) ())
    (fn x_r =>
      (fn f_ => fn () => f_ ((isa_vmtf_flush_code x_r a1r) ()) ())
        (fn x_t =>
          (fn f_ => fn () => f_
            ((heap_array_set_u heap_bool a2r (atm_of_code (uminus_code ai))
               (is_pos_code (uminus_code ai)))
            ()) ())
            (fn xb =>
              (fn f_ => fn () => f_
                ((arl_append (default_nat, heap_nat) a1o a2s) ()) ())
                (fn xab =>
                  (fn f_ => fn () => f_
                    ((arl_append (default_nat, heap_nat) a1p a2s) ()) ())
                    (fn xba =>
                      (fn () =>
                        (x_r, (x_i, (a1b, (x_p,
    (x_m, (x_t, (xb, ((Word32.fromInt 0),
                       (a1h, (x_o, (a1j, (a1k,
   (ema_update_ref x_c a1l,
     (ema_update_ref x_c a1m,
       (incr_conflict_count_since_last_restart a1n,
         (xab, (xba, (suc a1q, a2q))))))))))))))))))))))))))))))
                end))
      end
        ()
    end)
    x;

fun backtrack_wl_D_code x =
  (fn xi => fn () =>
    let
      val xa = lit_of_hd_trail_st_heur_code xi ();
      val a = extract_shorter_conflict_list_heur_st_code xi ();
    in
      let
        val (a1, (a1a, a2a)) = a;
      in
        (fn f_ => fn () => f_ ((find_decomp_wl_imp_codea a1a a1) ()) ())
          (fn x_c =>
            (fn f_ => fn () => f_ ((len heap_uint32 a2a) ()) ())
              (fn xaa =>
                (if less_nat one_nat xaa then propagate_bt_wl_D_code xa a2a x_c
                  else propagate_unit_bt_wl_D_code xa x_c)))
      end
        ()
    end)
    x;

fun cdcl_twl_o_prog_wl_D_code x =
  (fn xi => fn () =>
    let
      val xa = get_conflict_wl_is_None_code xi ();
    in
      (if xa then decide_wl_or_skip_D_code xi
        else (if Word32.< ((Word32.fromInt 0), count_decided_st_heur xi)
               then (fn f_ => fn () => f_ ((skip_and_resolve_loop_wl_D xi) ())
                      ())
                      (fn x_b =>
                        (fn f_ => fn () => f_ ((backtrack_wl_D_code x_b) ()) ())
                          (fn x_c =>
                            (fn f_ => fn () => f_
                              ((isasat_current_status_code x_c) ()) ())
                              (fn _ => (fn () => (false, x_c)))))
               else (fn () => (true, xi))))
        ()
    end)
    x;

fun array_nat_of_uint64_code x =
  (fn xi => fn () =>
    let
      val xa = len heap_uint64 xi ();
      val xb = new heap_nat xa zero_nata ();
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((len heap_nat a2) ()) ())
              (fn x_c => (fn () => (less_nat a1 x_c))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((nth heap_uint64 xi a1) ()) ())
              (fn xc =>
                (fn f_ => fn () => f_ ((upd heap_nat a1 (nat_of_uint64 xc) a2)
                  ()) ())
                  (fn x_d => (fn () => (plus_nat a1 one_nat, x_d)))))
          (zero_nata, xb) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun trail_pol_slow_of_fast_code x =
  (fn (a1, (a1a, (a1b, (a1c, a2c)))) => fn () =>
    let
      val xa = array_nat_of_uint64_code a1c ();
    in
      (a1, (a1a, (a1b, (xa, a2c))))
    end)
    x;

fun append_el_aa (A1_, A2_) =
  (fn a => fn i => fn x => fn () =>
    let
      val j = nth (heap_prod (heap_array (typerep_heap A2_)) heap_nat) a i ();
      val aa = arl_append (A1_, A2_) j x ();
    in
      upd (heap_prod (heap_array (typerep_heap A2_)) heap_nat) i aa a ()
    end);

fun length_aa A_ xs i =
  (fn () =>
    let
      val x = nth (heap_prod (heap_array (typerep_heap A_)) heap_nat) xs i ();
    in
      arl_length A_ x ()
    end);

fun nth_aa A_ xs i j =
  (fn () =>
    let
      val x = nth (heap_prod (heap_array (typerep_heap A_)) heap_nat) xs i ();
      val xa = arl_get A_ x j ();
    in
      xa
    end);

fun convert_single_wl_to_nat_code x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, _) =>
            (fn f_ => fn () => f_
              ((length_aa (heap_prod heap_uint64 heap_uint64) ai bib) ()) ())
              (fn x_a => (fn () => (less_nat a1 x_a))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((nth_aa (heap_prod heap_uint64 heap_uint64) ai bib a1) ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_
                  ((append_el_aa
                     (default_prod default_nat default_uint64,
                       heap_prod heap_nat heap_uint64)
                     a2 bi let
                             val (a1a, a) = x_a;
                           in
                             (nat_of_uint64 a1a, a)
                           end)
                  ()) ())
                  (fn x_d => (fn () => (plus_nat a1 one_nat, x_d)))))
          (zero_nata, bia) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun arrayO_ara_empty_sz_code (A1_, A2_) =
  (fn xi => fn () =>
    let
      val x =
        imp_for zero_nata xi
          (fn _ => fn sigma =>
            (fn f_ => fn () => f_ ((arl_empty (A1_, A2_) zero_nat) ()) ())
              (fn x_c => (fn () => (x_c :: sigma))))
          [] ();
    in
      (fn () => Array.fromList x) ()
    end);

fun length_a A_ xs = len A_ xs;

fun convert_wlists_to_nat_code x =
  (fn xi => fn () =>
    let
      val xa =
        length_a
          (heap_prod (heap_array (typerep_prod typerep_uint64 typerep_uint64))
            heap_nat)
          xi ();
      val x_b =
        arrayO_ara_empty_sz_code
          (default_prod default_nat default_uint64,
            heap_prod heap_nat heap_uint64)
          xa ();
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((length_a
                 (heap_prod
                   (heap_array (typerep_prod typerep_nat typerep_uint64))
                   heap_nat)
                 a2)
              ()) ())
              (fn x_e => (fn () => (less_nat a1 x_e))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((convert_single_wl_to_nat_code xi a1 a2 a1)
              ()) ())
              (fn x_f => (fn () => (plus_nat a1 one_nat, x_f))))
          (zero_nata, x_b) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun isasat_fast_slow_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, (a1n, (a1o, a2o))))))))))))))))
     =>
    fn () =>
    let
      val xa = trail_pol_slow_of_fast_code a1 ();
      val xaa = convert_wlists_to_nat_code a1d ();
    in
      (xa, (a1a, (a1b, (a1c, (xaa, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, (a1n, (a1o, a2o))))))))))))))))
    end)
    x;

val uint32_maxa : nat = nat_of_integer (4294967295 : IntInf.int);

val uint32_max : nat = uint32_maxa;

fun isasat_fast_code x =
  (fn (_, (a1a, _)) => fn () =>
    let
      val xa = arl_length heap_uint32 a1a ();
    in
      less_eq_nat xa
        (minus_nata (nat_of_integer (18446744073709551615 : IntInf.int))
          (plus_nat (divide_nat uint32_max (nat_of_integer (2 : IntInf.int)))
            (nat_of_integer (6 : IntInf.int))))
    end)
    x;

fun cdcl_twl_stgy_restart_prog_wl_heur_fast_code x =
  (fn xi => fn () =>
    let
      val xa = isasat_fast_code xi ();
      val a =
        heap_WHILET (fn (a1, (a1a, _)) => (fn () => (not a1a andalso not a1)))
          (fn (_, (_, (a1b, a2b))) =>
            (fn f_ => fn () => f_
              ((unit_propagation_outer_loop_wl_D_fast_code a1b) ()) ())
              (fn x_b =>
                (fn f_ => fn () => f_ ((cdcl_twl_o_prog_wl_D_fast_code x_b) ())
                  ())
                  (fn (a1c, a2c) =>
                    (fn f_ => fn () => f_
                      ((restart_prog_wl_D_heur_fast_code a2c a2b a1c) ()) ())
                      (fn (a1d, a2d) =>
                        (fn f_ => fn () => f_ ((isasat_fast_code a1d) ()) ())
                          (fn xb => (fn () => (not xb, (a1c, (a1d, a2d)))))))))
          (not xa, (false, (xi, zero_nata))) ();
    in
      let
        val (_, (a1a, (a1b, a2b))) = a;
      in
        (if not a1a
          then (fn f_ => fn () => f_ ((isasat_fast_slow_code a1b) ()) ())
                 (fn x_c =>
                   (fn f_ => fn () => f_
                     ((heap_WHILET (fn (a1c, _) => (fn () => (not a1c)))
                        (fn (_, (a1d, a2d)) =>
                          (fn f_ => fn () => f_
                            ((unit_propagation_outer_loop_wl_D_code a1d) ()) ())
                            (fn x_e =>
                              (fn f_ => fn () => f_
                                ((cdcl_twl_o_prog_wl_D_code x_e) ()) ())
                                (fn (a1e, a2e) =>
                                  (fn f_ => fn () => f_
                                    ((restart_wl_D_heur_slow_code a2e a2d a1e)
                                    ()) ())
                                    (fn (a1f, a2f) =>
                                      (fn () => (a1e, (a1f, a2f)))))))
                        (false, (x_c, a2b)))
                     ()) ())
                     (fn (_, (a1d, _)) => (fn () => a1d)))
          else isasat_fast_slow_code a1b)
      end
        ()
    end)
    x;

fun get_conflict_wl_is_None_init_code_unb x =
  (fn xi => (fn () => let
                        val (_, (_, ((a1c, _), (_, (_, _))))) = xi;
                      in
                        a1c
                      end))
    x;

fun get_conflict_wl_is_None_init_code x =
  (fn xi => (fn () => let
                        val (_, (_, ((a1c, _), (_, (_, _))))) = xi;
                      in
                        a1c
                      end))
    x;

fun cdcl_twl_stgy_restart_prog_wl_heur_code x =
  (fn xi => fn () =>
    let
      val a =
        heap_WHILET (fn (a1, _) => (fn () => (not a1)))
          (fn (_, (a1a, a2a)) =>
            (fn f_ => fn () => f_ ((unit_propagation_outer_loop_wl_D_code a1a)
              ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_ ((cdcl_twl_o_prog_wl_D_code x_a) ()) ())
                  (fn (a1b, a2b) =>
                    (fn f_ => fn () => f_
                      ((restart_wl_D_heur_slow_code a2b a2a a1b) ()) ())
                      (fn (a1c, a2c) => (fn () => (a1b, (a1c, a2c)))))))
          (false, (xi, zero_nata)) ();
    in
      let
        val (_, (a1a, _)) = a;
      in
        (fn () => a1a)
      end
        ()
    end)
    x;

val extract_atms_clss_imp_empty_assn :
  (unit -> (Uint64.uint64 array * (Word32.word * (Word32.word array * nat))))
  = (fn () =>
      let
        val x =
          new heap_uint64 (nat_of_integer (1024 : IntInf.int)) Uint64.zero ();
        val xa = arl_empty (default_uint32, heap_uint32) zero_nat ();
      in
        (x, ((Word32.fromInt 0), xa))
      end);

fun rewatch_heur_fast_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = arl_length heap_nat ai ();
    in
      imp_for zero_nata xa
        (fn xaa => fn sigma =>
          (fn f_ => fn () => f_ ((arl_get heap_nat ai xaa) ()) ())
            (fn xb =>
              (fn f_ => fn () => f_ ((arena_status_code bia xb) ()) ())
                (fn xc =>
                  (if not ((xc : Word32.word) = (Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int))))
                    then (fn f_ => fn () => f_ ((arl_get heap_nat ai xaa) ())
                           ())
                           (fn xd =>
                             (fn f_ => fn () => f_
                               ((isa_arena_lit_fast_code bia (uint64_of_nat xd))
                               ()) ())
                               (fn xe =>
                                 (fn f_ => fn () => f_
                                   ((arl_get heap_nat ai xaa) ()) ())
                                   (fn xba =>
                                     (fn f_ => fn () => f_
                                       ((arl_get heap_nat ai xaa) ()) ())
                                       (fn xca =>
 (fn f_ => fn () => f_
   ((isa_arena_lit_fast_code bia (Uint64.plus (uint64_of_nat xca) Uint64.one))
   ()) ())
   (fn xcb =>
     (fn f_ => fn () => f_ ((arl_get heap_nat ai xaa) ()) ())
       (fn xda =>
         (fn f_ => fn () => f_
           ((isa_arena_length_fast_code bia (uint64_of_nat xda)) ()) ())
           (fn xdb =>
             (fn f_ => fn () => f_
               ((append_el_aa_u
                  (default_prod default_uint64 default_uint64,
                    heap_prod heap_uint64 heap_uint64)
                  sigma xe
                  (to_watcher_fast_code (uint64_of_nat xba) xcb
                    ((xdb : Uint64.uint64) = (Uint64.fromInt
       (2 : IntInf.int)))))
               ()) ())
               (fn x_c =>
                 (fn f_ => fn () => f_ ((arl_get heap_nat ai xaa) ()) ())
                   (fn xf =>
                     (fn f_ => fn () => f_
                       ((isa_arena_lit_fast_code bia
                          (Uint64.plus (uint64_of_nat xf) Uint64.one))
                       ()) ())
                       (fn x_d =>
                         (fn f_ => fn () => f_ ((arl_get heap_nat ai xaa) ())
                           ())
                           (fn xg =>
                             (fn f_ => fn () => f_ ((arl_get heap_nat ai xaa)
                               ()) ())
                               (fn xbb =>
                                 (fn f_ => fn () => f_
                                   ((isa_arena_lit_fast_code bia
                                      (uint64_of_nat xbb))
                                   ()) ())
                                   (fn xbc =>
                                     (fn f_ => fn () => f_
                                       ((arl_get heap_nat ai xaa) ()) ())
                                       (fn xab =>
 (fn f_ => fn () => f_ ((isa_arena_length_fast_code bia (uint64_of_nat xab)) ())
   ())
   (fn xac =>
     append_el_aa_u
       (default_prod default_uint64 default_uint64,
         heap_prod heap_uint64 heap_uint64)
       x_c x_d
       (to_watcher_fast_code (uint64_of_nat xg) xbc
         ((xac : Uint64.uint64) = (Uint64.fromInt
                                    (2 : IntInf.int)))))))))))))))))))
                    else (fn () => sigma)))))
        bi ()
    end)
    x;

fun rewatch_heur_st_fast_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, (a1h, (a1i, a2i))))))))))
     =>
    fn () =>
    let
      val xa = rewatch_heur_fast_code a2i a1a a1d ();
    in
      (a1, (a1a, (a1b, (a1c, (xa, (a1e, (a1f, (a1g, (a1h, (a1i, a2i))))))))))
    end)
    x;

fun extract_lits_sorted_code x =
  (fn xi => (fn () => let
                        val (_, (a1a, a2a)) = xi;
                      in
                        (a2a, a1a)
                      end))
    x;

fun arl_replicate A_ init_cap x =
  let
    val n = max ord_nat init_cap minimum_capacity;
  in
    (fn () => let
                val a = new A_ n x ();
              in
                (a, init_cap)
              end)
  end;

val restart_info_init : Uint64.uint64 * Uint64.uint64 =
  (Uint64.zero, Uint64.zero);

fun ema_init alpha =
  (Uint64.zero,
    (alpha,
      (shiftl_uint64 Uint64.one (nat_of_integer (32 : IntInf.int)),
        (Uint64.zero, Uint64.zero))));

fun finalise_init_code_unb x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (((a1g, (a1h, (a1i, (a1j, a2j)))), a2f),
                                      (a1k, (a1l, (a1m, (a1n, a2n))))))))))
      =>
    fn () =>
    let
      val xa =
        arl_replicate heap_uint32 (nat_of_integer (160 : IntInf.int))
          (Word32.* (two_uint32, (Word32.fromInt 0))) ();
      val xaa = arl_empty (default_nat, heap_nat) zero_nat ();
    in
      (a1, (a1a, (a1b, (a1c, (a1d, (((a1g, (a1h, (the a1i, (the a1j, a2j)))),
                                      a2f),
                                     (a1k, (a1l,
     (a1m, (a1n, (let
                    val (a, _) = xa;
                  in
                    (a, one_nat)
                  end,
                   ((Uint64.zero,
                      (Uint64.zero,
                        (Uint64.zero,
                          (Uint64.zero, (Uint64.zero, Uint64.zero))))),
                     (ema_init (Uint64.fromInt (128849010 : IntInf.int)),
                       (ema_init (Uint64.fromInt (429450 : IntInf.int)),
                         (restart_info_init,
                           (a2n, (xaa, (zero_nata, ai))))))))))))))))))
    end)
    x;

fun init_trail_D_fast_code x =
  (fn _ => fn bia => fn bi => fn () =>
    let
      val xa = arl_empty (default_uint32, heap_uint32) zero_nat ();
      val x_b = arl_empty (default_uint32, heap_uint32) zero_nat ();
      val x_d = new heap_uint32 bi uNSET_code ();
      val x_f = new heap_uint32 bia (Word32.fromInt 0) ();
      val x_h = new heap_uint64 bia Uint64.one ();
    in
      (xa, (x_d, (x_f, (x_h, ((Word32.fromInt 0), x_b)))))
    end)
    x;

fun distinct_atms_empty_code x =
  (fn xi => fn () =>
    let
      val xa = arl_empty (default_uint32, heap_uint32) zero_nat ();
      val x_a = new heap_bool xi false ();
    in
      (xa, x_a)
    end)
    x;

fun initialise_VMTF_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        new (heap_vmtf_node heap_uint32 heap_uint64) bi
          (VMTF_Node (Uint64.zero, NONE, NONE)) ();
      val x_b = distinct_atms_empty_code bi ();
      val a =
        heap_WHILET
          (fn (a1, (_, _)) =>
            (fn f_ => fn () => f_ ((length_arl_u_code heap_uint32 ai) ()) ())
              (fn x_d => (fn () => (Word32.< (a1, x_d)))))
          (fn (a1, (a1a, a2a)) =>
            (fn f_ => fn () => f_
              (((fn () => Array.sub ((fn (a,b) => a) (ai), Word32.toInt (a1))))
              ()) ())
              (fn x_d =>
                (fn f_ => fn () => f_
                  ((heap_array_set_u (heap_vmtf_node heap_uint32 heap_uint64)
                     a1a x_d
                     (VMTF_Node
                       (Uint64.plus (uint64_of_uint32 a1) Uint64.one, NONE,
                         a2a)))
                  ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_
                      ((case a2a of NONE => (fn () => xb)
                         | SOME x_h =>
                           (fn f_ => fn () => f_
                             ((nth_u_code
                                (heap_vmtf_node heap_uint32 heap_uint64) xb x_h)
                             ()) ())
                             (fn xaa =>
                               (fn f_ => fn () => f_
                                 ((nth_u_code
                                    (heap_vmtf_node heap_uint32 heap_uint64) xb
                                    x_h)
                                 ()) ())
                                 (fn xba =>
                                   heap_array_set_u
                                     (heap_vmtf_node heap_uint32 heap_uint64) xb
                                     x_h (VMTF_Node
   (stamp xaa, SOME x_d, get_next xba)))))
                      ()) ())
                      (fn xc =>
                        (fn () =>
                          (Word32.+ (a1, (Word32.fromInt 1)),
                            (xc, SOME x_d)))))))
          ((Word32.fromInt 0), (xa, NONE)) ();
    in
      let
        val (a1, (a1a, a2a)) = a;
      in
        (fn f_ => fn () => f_ ((arl_is_empty heap_uint32 ai) ()) ())
          (fn xb =>
            (fn f_ => fn () => f_
              ((if xb then (fn () => NONE)
                 else (fn f_ => fn () => f_ ((arl_get heap_uint32 ai zero_nata)
                        ()) ())
                        (fn x_f => (fn () => (SOME x_f))))
              ()) ())
              (fn xc =>
                (fn () =>
                  ((a1a, (uint64_of_uint32 a1, (a2a, (xc, a2a)))), x_b))))
      end
        ()
    end)
    x;

val empty_lbd_code : (unit -> (bool array * Word32.word)) =
  (fn () =>
    let
      val x = new heap_bool (nat_of_integer (32 : IntInf.int)) false ();
    in
      (x, (Word32.fromInt 0))
    end);

fun init_state_wl_D_code x =
  (fn (a1, a2) =>
    let
      val xa = suc (nat_of_uint32 a2);
      val x_b = times_nat (nat_of_integer (2 : IntInf.int)) xa;
    in
      (fn () =>
        let
          val x_d = init_trail_D_fast_code a1 xa x_b ();
          val x_e = arl_empty (default_uint32, heap_uint32) zero_nat ();
          val xaa = new heap_bool xa false ();
          val x_i =
            arrayO_ara_empty_sz_code
              (default_prod default_uint64 default_uint64,
                heap_prod heap_uint64 heap_uint64)
              x_b ();
          val x_k = initialise_VMTF_code a1 xa ();
          val x_l = new heap_bool xa false ();
          val xb = new heap_minimize_status xa SEEN_UNKNOWN ();
          val xba = arl_empty (default_uint32, heap_uint32) zero_nat ();
          val x_p = empty_lbd_code ();
          val x_r = arl_empty (default_nat, heap_nat) zero_nat ();
        in
          (x_d, (x_e, ((true, ((Word32.fromInt 0), xaa)),
                        ((Word32.fromInt 0),
                          (x_i, (x_k, (x_l,
((Word32.fromInt 0), ((xb, xba), (x_p, x_r))))))))))
        end)
    end)
    x;

fun numeral A_ (Bit1 n) =
  let
    val m = numeral A_ n;
  in
    plus ((plus_semigroup_add o semigroup_add_numeral) A_)
      (plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m)
      (one (one_numeral A_))
  end
  | numeral A_ (Bit0 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m
    end
  | numeral A_ One = one (one_numeral A_);

fun init_next_size (A1_, A2_) l = times A1_ (numeral A2_ (Bit0 One)) l;

fun nat_lit_lits_init_assn_assn_in x =
  (fn ai => fn (a1, (a1a, a2a)) =>
    let
      val xa = max ord_uint32 ai a1a;
    in
      (fn () =>
        let
          val xaa = length_u_code heap_uint64 a1 ();
        in
          (if Word32.< (ai, xaa)
            then (fn f_ => fn () => f_ ((nth_u_code heap_uint64 a1 ai) ()) ())
                   (fn xab =>
                     (fn f_ => fn () => f_
                       ((if (((Uint64.andb xab
                                Uint64.one) : Uint64.uint64) = Uint64.one)
                          then (fn () => a2a)
                          else arl_append (default_uint32, heap_uint32) a2a ai)
                       ()) ())
                       (fn x_c =>
                         (fn f_ => fn () => f_ ((nth_u_code heap_uint64 a1 ai)
                           ()) ())
                           (fn xac =>
                             (fn f_ => fn () => f_
                               ((heap_array_set_u heap_uint64 a1 ai
                                  (Uint64.orb
                                    (Uint64.plus xac
                                      (Uint64.fromInt (2 : IntInf.int)))
                                    Uint64.one))
                               ()) ())
                               (fn x_e => (fn () => (x_e, (xa, x_c)))))))
            else (fn f_ => fn () => f_
                   ((array_grow heap_uint64 a1
                      (nat_of_uint32
                        (init_next_size (times_uint32, numeral_uint32) ai))
                      Uint64.zero)
                   ()) ())
                   (fn xab =>
                     (fn f_ => fn () => f_
                       ((heap_array_set_u heap_uint64 xab ai Uint64.one) ()) ())
                       (fn x_c =>
                         (fn f_ => fn () => f_
                           ((arl_append (default_uint32, heap_uint32) a2a ai)
                           ()) ())
                           (fn xac => (fn () => (x_c, (xa, xac)))))))
            ()
        end)
    end)
    x;

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

fun extract_atms_cls_imp x =
  (fn ai =>
    imp_nfoldli ai (fn _ => (fn () => true))
      (fn xa => nat_lit_lits_init_assn_assn_in (atm_of_code xa)))
    x;

fun extract_atms_clss_imp x =
  (fn ai => imp_nfoldli ai (fn _ => (fn () => true)) extract_atms_cls_imp) x;

val isasat_banner_content : char list =
  [Chara (true, true, false, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, true, true, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, true, false, true, false, false, false, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (true, true, true, false, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, true, true, false, false, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false)];

fun isasat_information_banner_code uu =
  (fn () =>
    (ignore (print
      (implode
         (shows_prec_list show_char zero_nata isasat_banner_content
           []) ^ "\n"))));

fun rewatch_heur_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = arl_length heap_nat ai ();
    in
      imp_for zero_nata xa
        (fn xaa => fn sigma =>
          (fn f_ => fn () => f_ ((arl_get heap_nat ai xaa) ()) ())
            (fn xb =>
              (fn f_ => fn () => f_ ((arena_status_code bia xb) ()) ())
                (fn xc =>
                  (if not ((xc : Word32.word) = (Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int))))
                    then (fn f_ => fn () => f_ ((arl_get heap_nat ai xaa) ())
                           ())
                           (fn xd =>
                             (fn f_ => fn () => f_ ((isa_arena_lit_code bia xd)
                               ()) ())
                               (fn xe =>
                                 (fn f_ => fn () => f_
                                   ((arl_get heap_nat ai xaa) ()) ())
                                   (fn xba =>
                                     (fn f_ => fn () => f_
                                       ((arl_get heap_nat ai xaa) ()) ())
                                       (fn xca =>
 (fn f_ => fn () => f_ ((isa_arena_lit_code bia (plus_nat xca one_nat)) ()) ())
   (fn xcb =>
     (fn f_ => fn () => f_ ((arl_get heap_nat ai xaa) ()) ())
       (fn xda =>
         (fn f_ => fn () => f_ ((isa_arena_length_code bia xda) ()) ())
           (fn xdb =>
             (fn f_ => fn () => f_
               ((append_el_aa_u
                  (default_prod default_nat default_uint64,
                    heap_prod heap_nat heap_uint64)
                  sigma xe
                  (to_watcher_code xba xcb
                    ((xdb : Uint64.uint64) = (Uint64.fromInt
       (2 : IntInf.int)))))
               ()) ())
               (fn x_c =>
                 (fn f_ => fn () => f_ ((arl_get heap_nat ai xaa) ()) ())
                   (fn xf =>
                     (fn f_ => fn () => f_
                       ((isa_arena_lit_code bia (plus_nat xf one_nat)) ()) ())
                       (fn x_d =>
                         (fn f_ => fn () => f_ ((arl_get heap_nat ai xaa) ())
                           ())
                           (fn xg =>
                             (fn f_ => fn () => f_ ((arl_get heap_nat ai xaa)
                               ()) ())
                               (fn xbb =>
                                 (fn f_ => fn () => f_
                                   ((isa_arena_lit_code bia xbb) ()) ())
                                   (fn xbc =>
                                     (fn f_ => fn () => f_
                                       ((arl_get heap_nat ai xaa) ()) ())
                                       (fn xab =>
 (fn f_ => fn () => f_ ((isa_arena_length_code bia xab) ()) ())
   (fn xac =>
     append_el_aa_u
       (default_prod default_nat default_uint64, heap_prod heap_nat heap_uint64)
       x_c x_d
       (to_watcher_code xg xbc
         ((xac : Uint64.uint64) = (Uint64.fromInt
                                    (2 : IntInf.int)))))))))))))))))))
                    else (fn () => sigma)))))
        bi ()
    end)
    x;

fun rewatch_heur_st_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, (a1h, (a1i, a2i))))))))))
     =>
    fn () =>
    let
      val xa = rewatch_heur_code a2i a1a a1d ();
    in
      (a1, (a1a, (a1b, (a1c, (xa, (a1e, (a1f, (a1g, (a1h, (a1i, a2i))))))))))
    end)
    x;

fun set_empty_clause_as_conflict_code x =
  (fn (a1, (a1a, ((_, (a1d, a2d)), (_, a2e)))) => fn () =>
    let
      val xa = isa_length_trail_fast_code a1 ();
    in
      (a1, (a1a, ((false, (a1d, a2d)), (xa, a2e))))
    end)
    x;

fun set_conflict_unit_code x =
  (fn ai => fn (_, (_, a2a)) => fn () =>
    let
      val xa = heap_array_set_u heap_bool a2a (atm_of_code ai) true ();
    in
      (false, ((Word32.fromInt 1), xa))
    end)
    x;

fun conflict_propagated_unit_cls_code x =
  (fn ai => fn (a1, (a1a, (a1b, (_, a2c)))) => fn () =>
    let
      val xa = set_conflict_unit_code ai a1b ();
      val xaa = isa_length_trail_fast_code a1 ();
    in
      (a1, (a1a, (xa, (xaa, a2c))))
    end)
    x;

fun already_propagated_unit_cls_code x =
  (fn _ => fn bi => (fn () => let
                                val (a1, (a1a, (a1b, (a1c, a2c)))) = bi;
                              in
                                (a1, (a1a, (a1b, (a1c, a2c))))
                              end))
    x;

fun polarity_st_heur_init_code x =
  (fn ai => fn bi => let
                       val (a1, _) = ai;
                     in
                       polarity_pol_fast_code a1 bi
                     end)
    x;

fun add_clause_to_others_code x =
  (fn _ => fn bi => (fn () => let
                                val (a1, (a1a, (a1b, (a1c, a2c)))) = bi;
                              in
                                (a1, (a1a, (a1b, (a1c, a2c))))
                              end))
    x;

fun propagate_unit_cls_code x =
  (fn ai => fn (a1, (a1a, (a1b, a2b))) => fn () =>
    let
      val xa = cons_trail_Propagated_tr_fast_code ai Uint64.zero a1 ();
    in
      (xa, (a1a, (a1b, a2b)))
    end)
    x;

fun list_length_1_code c =
  (case c of [] => false | [_] => true | _ :: _ :: _ => false);

fun add_init_cls_code x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, (a1h, (a1i, a2i))))))))))
      =>
    fn () =>
    let
      val xa = (fn () => Array.fromList ai) ();
      val a = append_and_length_code true xa a1a ();
    in
      let
        val (a1j, a2j) = a;
      in
        (fn f_ => fn () => f_ ((arl_append (default_nat, heap_nat) a2i a2j) ())
          ())
          (fn xb =>
            (fn () =>
              (a1, (a1j, (a1b, (a1c, (a1d, (a1e,
     (a1f, (a1g, (a1h, (a1i, xb))))))))))))
      end
        ()
    end)
    x;

fun is_Nil a = (case a of [] => true | _ :: _ => false);

fun op_list_hd x = hd x;

fun init_dt_step_wl_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = get_conflict_wl_is_None_init_code bi ();
    in
      (if xa
        then (if is_Nil ai then set_empty_clause_as_conflict_code bi
               else (if list_length_1_code ai
                      then let
                             val x_c = op_list_hd ai;
                           in
                             (fn f_ => fn () => f_
                               ((polarity_st_heur_init_code bi x_c) ()) ())
                               (fn x_e =>
                                 (if ((x_e : Word32.word) = uNSET_code)
                                   then propagate_unit_cls_code x_c bi
                                   else (if ((x_e : Word32.word) = sET_TRUE_code)
  then already_propagated_unit_cls_code ai bi
  else conflict_propagated_unit_cls_code x_c bi)))
                           end
                      else add_init_cls_code ai bi))
        else add_clause_to_others_code ai bi)
        ()
    end)
    x;

fun init_dt_wl_heur_code x =
  (fn ai => imp_nfoldli ai (fn _ => (fn () => true)) init_dt_step_wl_code) x;

fun finalise_init_code x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (((a1g, (a1h, (a1i, (a1j, a2j)))), a2f),
                                      (a1k, (a1l, (a1m, (a1n, a2n))))))))))
      =>
    fn () =>
    let
      val xa =
        arl_replicate heap_uint32 (nat_of_integer (160 : IntInf.int))
          (Word32.* (two_uint32, (Word32.fromInt 0))) ();
      val xaa = arl_empty (default_nat, heap_nat) zero_nat ();
    in
      (a1, (a1a, (a1b, (a1c, (a1d, (((a1g, (a1h, (the a1i, (the a1j, a2j)))),
                                      a2f),
                                     (a1k, (a1l,
     (a1m, (a1n, (let
                    val (a, _) = xa;
                  in
                    (a, one_nat)
                  end,
                   ((Uint64.zero,
                      (Uint64.zero,
                        (Uint64.zero,
                          (Uint64.zero, (Uint64.zero, Uint64.zero))))),
                     (ema_init (Uint64.fromInt (128849010 : IntInf.int)),
                       (ema_init (Uint64.fromInt (429450 : IntInf.int)),
                         (restart_info_init,
                           (a2n, (xaa, (zero_nata, ai))))))))))))))))))
    end)
    x;

fun isasat_init_fast_slow_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, (a1h, (a1i, a2i))))))))))
     =>
    fn () =>
    let
      val xa = trail_pol_slow_of_fast_code a1 ();
      val xaa = convert_wlists_to_nat_code a1d ();
    in
      (xa, (a1a, (a1b, (a1c, (xaa, (a1e, (a1f, (a1g, (a1h, (a1i, a2i))))))))))
    end)
    x;

fun opts_unbounded_mode x = (fn (_, (_, c)) => c) x;

fun isasat_fast_init_code x =
  (fn (_, (a1a, _)) => fn () =>
    let
      val xa = arl_length heap_uint32 a1a ();
    in
      less_eq_nat xa (nat_of_integer (18446744071562067962 : IntInf.int))
    end)
    x;

val empty_conflict_code :
  (unit ->
    ((Word32.word array * nat) option *
      (Uint64.uint64 *
        (Uint64.uint64 *
          (Uint64.uint64 *
            (Uint64.uint64 * (Uint64.uint64 * Uint64.uint64)))))))
  = (fn () =>
      let
        val x = arl_empty (default_uint32, heap_uint32) zero_nat ();
      in
        (SOME x,
          (Uint64.zero,
            (Uint64.zero,
              (Uint64.zero, (Uint64.zero, (Uint64.zero, Uint64.zero))))))
      end);

fun op_list_is_empty x = null x;

fun get_trail_wl_code x =
  (fn (a, b) =>
    let
      val (m, _) = a;
    in
      (fn (_, (_, (_, (_, (_, (_, (_, (_, (_, (_, (stat, _))))))))))) =>
        (SOME m, stat))
    end
      b)
    x;

val empty_init_code :
  (unit ->
    ((Word32.word array * nat) option *
      (Uint64.uint64 *
        (Uint64.uint64 *
          (Uint64.uint64 *
            (Uint64.uint64 * (Uint64.uint64 * Uint64.uint64)))))))
  = (fn () =>
      (NONE,
        (Uint64.zero,
          (Uint64.zero,
            (Uint64.zero, (Uint64.zero, (Uint64.zero, Uint64.zero)))))));

fun get_stats_code x =
  (fn (a, b) =>
    let
      val (_, _) = a;
    in
      (fn (_, (_, (_, (_, (_, (_, (_, (_, (_, (_, (stat, _))))))))))) =>
        (NONE, stat))
    end
      b)
    x;

fun isaSAT_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = extract_atms_clss_imp_empty_assn ();
      val xb = extract_atms_clss_imp bi xa ();
      val xc = extract_lits_sorted_code xb ();
    in
      (if opts_unbounded_mode ai
        then (fn f_ => fn () => f_ ((init_state_wl_D_code xc) ()) ())
               (fn x_f =>
                 (fn f_ => fn () => f_ ((init_dt_wl_heur_code bi x_f) ()) ())
                   (fn x_g =>
                     (fn f_ => fn () => f_ ((isasat_init_fast_slow_code x_g) ())
                       ())
                       (fn x_h =>
                         (fn f_ => fn () => f_ ((rewatch_heur_st_code x_h) ())
                           ())
                           (fn x_i =>
                             (fn f_ => fn () => f_
                               ((get_conflict_wl_is_None_init_code_unb x_i) ())
                               ())
                               (fn xd =>
                                 (if not xd then empty_init_code
                                   else (if op_list_is_empty bi
  then empty_conflict_code
  else (fn f_ => fn () => f_ ((isasat_information_banner_code x_i) ()) ())
         (fn _ =>
           (fn f_ => fn () => f_ ((finalise_init_code_unb ai x_i) ()) ())
             (fn x_o =>
               (fn f_ => fn () => f_
                 ((cdcl_twl_stgy_restart_prog_wl_heur_code x_o) ()) ())
                 (fn x_p =>
                   (fn f_ => fn () => f_ ((get_conflict_wl_is_None_code x_p) ())
                     ())
                     (fn x_q =>
                       (fn () =>
                         (if x_q then get_trail_wl_code x_p
                           else get_stats_code x_p)))))))))))))
        else (fn f_ => fn () => f_ ((init_state_wl_D_code xc) ()) ())
               (fn x_f =>
                 (fn f_ => fn () => f_ ((init_dt_wl_heur_code bi x_f) ()) ())
                   (fn x_g =>
                     (fn f_ => fn () => f_
                       ((get_conflict_wl_is_None_init_code x_g) ()) ())
                       (fn xd =>
                         (if not xd then empty_init_code
                           else (if op_list_is_empty bi then empty_conflict_code
                                  else (fn f_ => fn () => f_
 ((isasat_fast_init_code x_g) ()) ())
 (fn xe =>
   (if not xe
     then (fn f_ => fn () => f_ ((isasat_information_banner_code x_g) ()) ())
            (fn _ =>
              (fn f_ => fn () => f_ ((isasat_init_fast_slow_code x_g) ()) ())
                (fn x_n =>
                  (fn f_ => fn () => f_ ((rewatch_heur_st_code x_n) ()) ())
                    (fn x_o =>
                      (fn f_ => fn () => f_ ((finalise_init_code_unb ai x_o) ())
                        ())
                        (fn x_p =>
                          (fn f_ => fn () => f_
                            ((cdcl_twl_stgy_restart_prog_wl_heur_code x_p) ())
                            ())
                            (fn x_q =>
                              (fn f_ => fn () => f_
                                ((get_conflict_wl_is_None_code x_q) ()) ())
                                (fn x_r =>
                                  (fn () =>
                                    (if x_r then get_trail_wl_code x_q
                                      else get_stats_code x_q))))))))
     else (fn f_ => fn () => f_ ((isasat_information_banner_code x_g) ()) ())
            (fn _ =>
              (fn f_ => fn () => f_ ((rewatch_heur_st_fast_code x_g) ()) ())
                (fn x_n =>
                  (fn f_ => fn () => f_ ((finalise_init_code ai x_n) ()) ())
                    (fn x_o =>
                      (fn f_ => fn () => f_
                        ((cdcl_twl_stgy_restart_prog_wl_heur_fast_code x_o) ())
                        ())
                        (fn x_p =>
                          (fn f_ => fn () => f_
                            ((get_conflict_wl_is_None_code x_p) ()) ())
                            (fn x_q =>
                              (fn () =>
                                (if x_q then get_trail_wl_code x_p
                                  else get_stats_code x_p)))))))))))))))
        ()
    end)
    x;

end; (*struct SAT_Solver*)
