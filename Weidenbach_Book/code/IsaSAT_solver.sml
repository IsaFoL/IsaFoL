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
  val toLarge : uint64 -> LargeWord.word;
  val fromLarge : LargeWord.word -> uint64
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

type uint64 = IntInf.int;

val mask = 0xFFFFFFFFFFFFFFFF : IntInf.int;

val zero = 0 : IntInf.int;

val one = 1 : IntInf.int;

fun fromInt x = IntInf.andb(x, mask);

fun toInt x = x

fun toLarge x = LargeWord.fromLargeInt (IntInf.toLarge x);

fun fromLarge x = IntInf.fromLarge (LargeWord.toLargeInt x);

fun plus x y = IntInf.andb(IntInf.+(x, y), mask);

fun minus x y = IntInf.andb(IntInf.-(x, y), mask);

fun negate x = IntInf.andb(IntInf.~(x), mask);

fun times x y = IntInf.andb(IntInf.*(x, y), mask);

fun divide x y = IntInf.div(x, y);

fun modulus x y = IntInf.mod(x, y);

fun less_eq x y = IntInf.<=(x, y);

fun less x y = IntInf.<(x, y);

fun notb x = IntInf.andb(IntInf.notb(x), mask);

fun orb x y = IntInf.orb(x, y);

fun andb x y = IntInf.andb(x, y);

fun xorb x y = IntInf.xorb(x, y);

val maxWord = IntInf.pow (2, Word.wordSize);

fun shiftl x n = 
  if n < maxWord then IntInf.andb(IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n)), mask)
  else 0;

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else 0;

val msb_mask = 0x8000000000000000 : IntInf.int;

fun shiftr_signed x i =
  if IntInf.andb(x, msb_mask) = 0 then shiftr x i
  else if i >= 64 then 0xFFFFFFFFFFFFFFFF
  else let
    val x' = shiftr x i
    val m' = IntInf.andb(IntInf.<<(mask, Word.max(0w64 - Word.fromLargeInt (IntInf.toLarge i), 0w0)), mask)
  in IntInf.orb(x', m') end;

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else false;

fun set_bit x n b =
  if n < 64 then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else x;

end



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
  type ('a, 'b) hashtable
  val isaSAT_code :
    (Word32.word list) list -> (unit -> ((Word32.word list) option))
  val integer_of_int : int -> IntInf.int
  val uint32_of_nat : nat -> Word32.word
end = struct

datatype typerepa = Typerep of string * typerepa list;

datatype num = One | Bit0 of num | Bit1 of num;

datatype char = Zero_char | Char of num;

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

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

fun equal_boola p true = p
  | equal_boola p false = not p
  | equal_boola true p = p
  | equal_boola false p = not p;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_bool = {equal = equal_boola} : bool equal;

fun typerep_boola t = Typerep ("HOL.bool", []);

val countable_bool = {} : bool countable;

val typerep_bool = {typerep = typerep_boola} : bool typerep;

val heap_bool = {countable_heap = countable_bool, typerep_heap = typerep_bool} :
  bool heap;

fun typerep_lista A_ t = Typerep ("List.list", [typerep A_ Type]);

fun countable_list A_ = {} : ('a list) countable;

fun typerep_list A_ = {typerep = typerep_lista A_} : ('a list) typerep;

fun heap_list A_ =
  {countable_heap = countable_list (countable_heap A_),
    typerep_heap = typerep_list (typerep_heap A_)}
  : ('a list) heap;

fun typerep_arraya A_ t = Typerep ("Heap.array", [typerep A_ Type]);

val countable_array = {} : ('a array) countable;

fun typerep_array A_ = {typerep = typerep_arraya A_} : ('a array) typerep;

fun heap_array A_ =
  {countable_heap = countable_array, typerep_heap = typerep_array A_} :
  ('a array) heap;

fun typerep_optiona A_ t = Typerep ("Option.option", [typerep A_ Type]);

fun countable_option A_ = {} : ('a option) countable;

fun typerep_option A_ = {typerep = typerep_optiona A_} : ('a option) typerep;

fun heap_option A_ =
  {countable_heap = countable_option (countable_heap A_),
    typerep_heap = typerep_option (typerep_heap A_)}
  : ('a option) heap;

val equal_uint32 = {equal = (fn a => fn b => ((a : Word32.word) = b))} :
  Word32.word equal;

fun typerep_uint32a t = Typerep ("Uint32.uint32", []);

val countable_uint32 = {} : Word32.word countable;

val typerep_uint32 = {typerep = typerep_uint32a} : Word32.word typerep;

val heap_uint32 =
  {countable_heap = countable_uint32, typerep_heap = typerep_uint32} :
  Word32.word heap;

val zero_uint32 = {zero = (Word32.fromInt 0)} : Word32.word zero;

val default_uint32a : Word32.word = (Word32.fromInt 0);

val default_uint32 = {default = default_uint32a} : Word32.word default;

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_uint32 = {minus = (fn a => fn b => Word32.- (a, b))} :
  Word32.word minus;

val ord_uint32 =
  {less_eq = (fn a => fn b => Word32.<= (a, b)),
    less = (fn a => fn b => Word32.< (a, b))}
  : Word32.word ord;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun def_hashmap_size_uint32 x = (fn _ => nat_of_integer (16 : IntInf.int)) x;

fun hashcode_uint32 n = n;

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a itself -> nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size : 'a hashable -> 'a itself -> nat;

val hashable_uint32 =
  {hashcode = hashcode_uint32, def_hashmap_size = def_hashmap_size_uint32} :
  Word32.word hashable;

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

fun typerep_unita t = Typerep ("Product_Type.unit", []);

val countable_unit = {} : unit countable;

val typerep_unit = {typerep = typerep_unita} : unit typerep;

val heap_unit = {countable_heap = countable_unit, typerep_heap = typerep_unit} :
  unit heap;

datatype ('a, 'b) vmtf_node = VMTF_Node of 'b * 'a option * 'a option;

fun typerep_vmtf_nodea A_ B_ t =
  Typerep
    ("Two_Watched_Literals_VMTF.vmtf_node", [typerep A_ Type, typerep B_ Type]);

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

datatype ('a, 'b) hashtable = HashTable of (('a * 'b) list) array * nat;

fun id x = (fn xa => xa) x;

fun eq A_ a b = equal A_ a b;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

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

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

fun replicate n x =
  (if equal_nat n zero_nata then []
    else x :: replicate (minus_nat n one_nat) x);

fun blit A_ src si dst di len =
  (fn () => 
    array_blit src (integer_of_nat
                     si) dst (integer_of_nat di) (integer_of_nat len));

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

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

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun nat_of_uint32 x =
  nat_of_integer (IntInf.fromLarge (Word32.toLargeInt x) : IntInf.int);

fun nat_of_hashcode x = nat_of_uint32 x;

fun bounded_hashcode_nat A_ n x =
  modulo_nat (nat_of_hashcode (hashcode A_ x)) n;

fun fst (x1, x2) = x1;

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

fun lookup_clause_assn_is_None x = (fn (b, (_, _)) => b) x;

fun get_conflict_wl_is_None_init_code x =
  (fn xi => (fn () => let
                        val (_, (_, (_, (a1c, (_, (_, _)))))) = xi;
                      in
                        lookup_clause_assn_is_None a1c
                      end))
    x;

fun hs_new (A1_, A2_) = ht_new (A1_, A2_) heap_unit;

val extract_atms_clss_imp_empty_assn :
  (unit -> ((Word32.word, unit) hashtable * Word32.word list))
  = (fn () => let
                val x = hs_new (hashable_uint32, heap_uint32) ();
              in
                (x, [])
              end);

fun op_list_prepend x = (fn a => x :: a);

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

fun nat_lit_lits_init_assn_assn_prepend x =
  (fn ai => fn (a1, a2) => fn () =>
    let
      val xa = hs_ins (equal_uint32, hashable_uint32, heap_uint32) ai a1 ();
    in
      (xa, op_list_prepend ai a2)
    end)
    x;

fun shiftr_uint32 x n =
  (if less_nat n (nat_of_integer (32 : IntInf.int))
    then Uint32.shiftr x (integer_of_nat n) else (Word32.fromInt 0));

fun atm_of_code l = shiftr_uint32 l one_nat;

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

fun hs_memb (A1_, A2_, A3_) x s =
  (fn () => let
              val r = ht_lookup (A1_, A2_, A3_) heap_unit x s ();
            in
              (case r of NONE => false | SOME _ => true)
            end);

fun nat_lit_lits_init_assn_assn_in x =
  (fn ai => fn (a1, _) =>
    hs_memb (equal_uint32, hashable_uint32, heap_uint32) ai a1)
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
      (fn xa => fn sigma => fn () =>
        let
          val x_a = nat_lit_lits_init_assn_assn_in (atm_of_code xa) sigma ();
        in
          (if x_a then (fn () => sigma)
            else nat_lit_lits_init_assn_assn_prepend (atm_of_code xa) sigma)
            ()
        end))
    x;

fun extract_atms_clss_imp x =
  (fn ai => imp_nfoldli ai (fn _ => (fn () => true)) extract_atms_cls_imp) x;

fun extract_atms_clss_imp_list_assn x =
  (fn ai => fn bi => fn () => let
                                val xa = extract_atms_clss_imp ai bi ();
                              in
                                snd xa
                              end)
    x;

fun get_next (VMTF_Node (x1, x2, x3)) = x3;

fun stamp (VMTF_Node (x1, x2, x3)) = x1;

fun heap_WHILET b f s =
  (fn () =>
    let
      val bv = b s ();
    in
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s))
        ()
    end);

fun heap_array_set_u A_ a i x =
  (fn () => let
              val _ = (fn () => Array.update (a, (Word32.toInt i), x)) ();
            in
              a
            end);

fun op_list_is_empty x = null x;

val initial_capacity : nat = nat_of_integer (16 : IntInf.int);

fun arl_empty (A1_, A2_) B_ =
  (fn () => let
              val a = new A2_ initial_capacity (default A1_) ();
            in
              (a, zero B_)
            end);

fun op_list_tl x = tl x;

fun op_list_hd x = hd x;

fun initialise_VMTF_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        new (heap_vmtf_node heap_uint32 heap_nat) bi
          (VMTF_Node (zero_nata, NONE, NONE)) ();
      val a =
        heap_WHILET
          (fn (a1, (_, (_, _))) => (fn () => (not (op_list_is_empty a1))))
          (fn (a1, (a1a, (a1b, a2b))) =>
            let
              val x_c = op_list_hd a1;
            in
              (fn f_ => fn () => f_
                ((heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) a1a x_c
                   (VMTF_Node (suc a1b, NONE, a2b)))
                ()) ())
                (fn xb =>
                  (fn f_ => fn () => f_
                    ((case a2b of NONE => (fn () => xb)
                       | SOME x_g =>
                         (fn f_ => fn () => f_
                           (((fn () => Array.sub (xb, Word32.toInt x_g))) ())
                           ())
                           (fn xaa =>
                             (fn f_ => fn () => f_
                               (((fn () => Array.sub (xb, Word32.toInt x_g)))
                               ()) ())
                               (fn xba =>
                                 heap_array_set_u
                                   (heap_vmtf_node heap_uint32 heap_nat) xb x_g
                                   (VMTF_Node
                                     (stamp xaa, SOME x_c, get_next xba)))))
                    ()) ())
                    (fn xc =>
                      (fn () =>
                        (op_list_tl a1,
                          (xc, (plus_nat a1b one_nat, SOME x_c))))))
            end)
          (ai, (xa, (zero_nata, NONE))) ();
    in
      let
        val (_, (a1a, (a1b, a2b))) = a;
      in
        (fn f_ => fn () => f_
          ((arl_empty (default_uint32, heap_uint32) zero_nat) ()) ())
          (fn x_d =>
            (fn () =>
              ((a1a, (a1b, (a2b, ((if op_list_is_empty ai then NONE
                                    else SOME (op_list_hd ai)),
                                   a2b)))),
                x_d)))
      end
        ()
    end)
    x;

fun imp_for i u f s =
  (if less_eq_nat u i then (fn () => s)
    else (fn () => let
                     val x = f i s ();
                   in
                     imp_for (plus_nat i one_nat) u f x ()
                   end));

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

fun init_trail_D_code x =
  (fn _ => fn bi => fn () =>
    let
      val xa = new (heap_option heap_bool) bi NONE ();
      val x_b = new heap_uint32 bi (Word32.fromInt 0) ();
      val x_d = new (heap_option heap_nat) bi NONE ();
    in
      ([], (xa, (x_b, (x_d, (Word32.fromInt 0)))))
    end)
    x;

val minimum_capacity : nat = nat_of_integer (16 : IntInf.int);

fun arrayO_raa_empty_sz (A1_, A2_) B_ init_cap =
  (fn () =>
    let
      val defaulta = new A2_ zero_nata (default A1_) ();
      val a =
        new (heap_array (typerep_heap A2_))
          (max ord_nat init_cap minimum_capacity) defaulta ();
    in
      (a, zero B_)
    end);

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

fun arrayO_raa_append (A1_, A2_) =
  (fn (a, n) => fn x => fn () =>
    let
      val lena = len (heap_array (typerep_heap A2_)) a ();
    in
      (if less_nat n lena
        then (fn f_ => fn () => f_ ((upd (heap_array (typerep_heap A2_)) n x a)
               ()) ())
               (fn aa => (fn () => (aa, plus_nat n one_nat)))
        else let
               val newcap = times_nat (nat_of_integer (2 : IntInf.int)) lena;
             in
               (fn f_ => fn () => f_ ((new A2_ zero_nata (default A1_)) ()) ())
                 (fn defaulta =>
                   (fn f_ => fn () => f_
                     ((array_grow (heap_array (typerep_heap A2_)) a newcap
                        defaulta)
                     ()) ())
                     (fn aa =>
                       (fn f_ => fn () => f_
                         ((upd (heap_array (typerep_heap A2_)) n x aa) ()) ())
                         (fn ab => (fn () => (ab, plus_nat n one_nat)))))
             end)
        ()
    end);

fun init_state_wl_D_code x =
  (fn xi => fn () =>
    let
      val xa =
        imp_nfoldli xi (fn _ => (fn () => true))
          (fn xb => fn sigma => (fn () => (max ord_uint32 xb sigma)))
          (Word32.fromInt 0) ();
    in
      let
        val xb = suc (nat_of_uint32 xa);
      in
        (fn f_ => fn () => f_ ((init_trail_D_code xi xb) ()) ())
          (fn x_d =>
            (fn f_ => fn () => f_ (((fn () => Array.fromList [])) ()) ())
              (fn x_e =>
                (fn f_ => fn () => f_
                  ((arrayO_raa_empty_sz (default_uint32, heap_uint32) zero_nat
                     xb)
                  ()) ())
                  (fn x_g =>
                    (fn f_ => fn () => f_
                      ((arrayO_raa_append (default_uint32, heap_uint32) x_g x_e)
                      ()) ())
                      (fn x_i =>
                        (fn f_ => fn () => f_
                          ((new (heap_option heap_bool) xb NONE) ()) ())
                          (fn xaa =>
                            (fn f_ => fn () => f_
                              ((arrayO_ara_empty_sz_code (default_nat, heap_nat)
                                 (times_nat (nat_of_integer (2 : IntInf.int))
                                   xb))
                              ()) ())
                              (fn x_m =>
                                (fn f_ => fn () => f_
                                  ((initialise_VMTF_code xi xb) ()) ())
                                  (fn x_o =>
                                    (fn f_ => fn () => f_
                                      ((new heap_bool xb false) ()) ())
                                      (fn x_p =>
(fn f_ => fn () => f_ ((new heap_minimize_status xb SEEN_UNKNOWN) ()) ())
  (fn xc =>
    (fn f_ => fn () => f_ ((arl_empty (default_uint32, heap_uint32) zero_nat)
      ()) ())
      (fn xba =>
        (fn () =>
          (x_d, (x_i, (zero_nata,
                        ((true, ((Word32.fromInt 0), xaa)),
                          ([], (x_m, (x_o, (x_p,
     ((Word32.fromInt 0), (xc, xba)))))))))))))))))))))
      end
        ()
    end)
    x;

fun from_init_state_code x = id x;

fun get_conflict_wl_is_None_code x =
  (fn xi => (fn () => let
                        val (_, (_, (_, (a1c, (_, (_, _)))))) = xi;
                      in
                        lookup_clause_assn_is_None a1c
                      end))
    x;

fun finalise_init_code x =
  (fn xi =>
    (fn () =>
      let
        val (a1, (a1a, (a1b, (a1c, (a1d, (a1e,
   (((a1h, (a1i, (a1j, (a1k, a2k)))), a2g), (a1l, a2l))))))))
          = xi;
      in
        (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (((a1h,
       (a1i, (the a1j, (the a1k, a2k)))),
      a2g),
     (a1l, a2l))))))))
      end))
    x;

fun to_init_state_code x = id x;

fun select_and_remove_from_literals_to_update_wl_code x =
  (fn xi =>
    (fn () =>
      let
        val (a1, (a1a, (a1b, (a1c, (a1d, (a1e, a2e)))))) = xi;
      in
        ((a1, (a1a, (a1b, (a1c, (op_list_tl a1d, (a1e, a2e)))))),
          op_list_hd a1d)
      end))
    x;

fun arl_get A_ = (fn (a, _) => nth A_ a);

fun nth_raa A_ xs i j =
  (fn () => let
              val x = arl_get (heap_array (typerep_heap A_)) xs i ();
              val xa = nth A_ x j ();
            in
              xa
            end);

fun access_lit_in_clauses_heur_code x =
  (fn ai => fn bia => fn bi => let
                                 val (_, (a1a, _)) = ai;
                               in
                                 nth_raa heap_uint32 a1a bia bi
                               end)
    x;

fun is_pos_code l =
  (((Word32.andb (l, (Word32.fromInt 1))) : Word32.word) = (Word32.fromInt 0));

fun polarity_pol_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, _))) = ai;
    in
      (fn () =>
        let
          val xa = (fn () => Array.sub (a1a, Word32.toInt (atm_of_code bi))) ();
        in
          (case xa of NONE => NONE
            | SOME x_a => (if is_pos_code bi then SOME x_a else SOME (not x_a)))
        end)
    end)
    x;

fun is_None a = (case a of NONE => true | SOME _ => false);

fun length_raa A_ xs i =
  (fn () => let
              val x = arl_get (heap_array (typerep_heap A_)) xs i ();
            in
              len A_ x ()
            end);

fun find_unwatched_wl_st_heur_code x =
  (fn ai => fn bi =>
    let
      val (a1, (a1a, (_, (_, (_, (_, (_, _))))))) = ai;
    in
      (fn () =>
        let
          val xa =
            heap_WHILET
              (fn (a1g, a2g) =>
                (fn f_ => fn () => f_ ((length_raa heap_uint32 a1a bi) ()) ())
                  (fn xa => (fn () => (is_None a1g andalso less_nat a2g xa))))
              (fn (_, a2g) =>
                (fn f_ => fn () => f_ ((nth_raa heap_uint32 a1a bi a2g) ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((polarity_pol_code a1 xa) ()) ())
                      (fn x_a =>
                        (fn () =>
                          (case x_a of NONE => (SOME a2g, a2g)
                            | SOME true => (SOME a2g, a2g)
                            | SOME false => (NONE, plus_nat a2g one_nat))))))
              (NONE, nat_of_integer (2 : IntInf.int)) ();
        in
          fst xa
        end)
    end)
    x;

fun is_in_conflict_code x =
  (fn ai => fn bi =>
    let
      val (_, a2) = ai;
    in
      (fn () =>
        let
          val xa = (fn () => Array.sub (a2, Word32.toInt (atm_of_code bi))) ();
        in
          not (is_None xa)
        end)
    end)
    x;

fun count_decided_pol x = (fn (_, (_, (_, (_, k)))) => k) x;

fun get_level_atm_code x =
  (fn ai => fn bi => let
                       val (_, (_, (a1b, _))) = ai;
                     in
                       (fn () => Array.sub (a1b, Word32.toInt bi))
                     end)
    x;

fun get_level_code x =
  (fn ai => fn bi => get_level_atm_code ai (atm_of_code bi)) x;

fun lookup_conflict_merge_code x =
  (fn ai => fn bic => fn bib => fn bia => fn bi =>
    let
      val (_, a2) = bia;
    in
      (fn () =>
        let
          val a =
            heap_WHILET
              (fn (a1a, (_, _)) =>
                (fn f_ => fn () => f_ ((length_raa heap_uint32 bic bib) ()) ())
                  (fn x_a => (fn () => (less_nat a1a x_a))))
              (fn (a1a, (a1b, a2b)) =>
                (fn f_ => fn () => f_ ((nth_raa heap_uint32 bic bib a1a) ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((get_level_code ai xa) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((nth_raa heap_uint32 bic bib a1a)
                          ()) ())
                          (fn xaa =>
                            (fn f_ => fn () => f_ ((is_in_conflict_code a2b xaa)
                              ()) ())
                              (fn xab =>
                                (if ((xb : Word32.word) = (count_decided_pol
                    ai)) andalso
                                      not xab
                                  then (fn f_ => fn () => f_
 (let
    val (a1c, a2c) = a2b;
  in
    (fn f_ => fn () => f_ ((nth_raa heap_uint32 bic bib a1a) ()) ())
      (fn xc =>
        (fn f_ => fn () => f_
          (((fn () => Array.sub (a2c, Word32.toInt (atm_of_code xc)))) ()) ())
          (fn xd =>
            (fn f_ => fn () => f_ ((nth_raa heap_uint32 bic bib a1a) ()) ())
              (fn xac =>
                (fn f_ => fn () => f_ ((nth_raa heap_uint32 bic bib a1a) ()) ())
                  (fn xba =>
                    (fn f_ => fn () => f_
                      ((heap_array_set_u (heap_option heap_bool) a2c
                         (atm_of_code xac) (SOME (is_pos_code xba)))
                      ()) ())
                      (fn x_e =>
                        (fn () =>
                          ((if is_None xd
                             then Word32.+ (a1c, (Word32.fromInt 1)) else a1c),
                            x_e)))))))
  end
 ()) ())
 (fn xc => (fn () => (suc a1a, (Word32.+ (a1b, (Word32.fromInt 1)), xc))))
                                  else (fn f_ => fn () => f_
 (let
    val (a1c, a2c) = a2b;
  in
    (fn f_ => fn () => f_ ((nth_raa heap_uint32 bic bib a1a) ()) ())
      (fn xc =>
        (fn f_ => fn () => f_
          (((fn () => Array.sub (a2c, Word32.toInt (atm_of_code xc)))) ()) ())
          (fn xd =>
            (fn f_ => fn () => f_ ((nth_raa heap_uint32 bic bib a1a) ()) ())
              (fn xac =>
                (fn f_ => fn () => f_ ((nth_raa heap_uint32 bic bib a1a) ()) ())
                  (fn xba =>
                    (fn f_ => fn () => f_
                      ((heap_array_set_u (heap_option heap_bool) a2c
                         (atm_of_code xac) (SOME (is_pos_code xba)))
                      ()) ())
                      (fn x_d =>
                        (fn () =>
                          ((if is_None xd
                             then Word32.+ (a1c, (Word32.fromInt 1)) else a1c),
                            x_d)))))))
  end
 ()) ())
 (fn xc => (fn () => (suc a1a, (a1b, xc))))))))))
              (zero_nata, (bi, a2)) ();
        in
          let
            val (_, (a1b, a2b)) = a;
          in
            (fn () => ((false, a2b), a1b))
          end
            ()
        end)
    end)
    x;

fun set_conflict_wl_int_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, (_, (a1e, (a1f, (a1g, (_, a2h))))))))) =>
    fn () =>
    let
      val a = lookup_conflict_merge_code a1 a1a ai a1c (Word32.fromInt 0) ();
    in
      let
        val (a1i, a2i) = a;
      in
        (fn () =>
          (a1, (a1a, (a1b, (a1i, ([], (a1e, (a1f, (a1g, (a2i, a2h))))))))))
      end
        ()
    end)
    x;

fun nth_aa_u A_ x la l =
  (fn () => let
              val xa = (fn () => Array.sub (x, Word32.toInt la)) ();
              val xb = arl_get A_ xa l ();
            in
              xb
            end);

fun watched_by_app_heur_code x =
  (fn ai => fn bia => fn bi => let
                                 val (_, (_, (_, (_, (_, (a1e, _)))))) = ai;
                               in
                                 nth_aa_u heap_nat a1e bia bi
                               end)
    x;

fun array_upd_u A_ i x a =
  (fn () => let
              val _ = (fn () => Array.update (a, (Word32.toInt i), x)) ();
            in
              a
            end);

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
      val na = minus_nat n one_nat;
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

fun set_butlast_aa_u A_ a i =
  (fn () =>
    let
      val x = (fn () => Array.sub (a, Word32.toInt i)) ();
      val aa = arl_butlast A_ x ();
    in
      array_upd_u (heap_prod (heap_array (typerep_heap A_)) heap_nat) i aa a ()
    end);

fun arl_set A_ =
  (fn (a, n) => fn i => fn x => fn () => let
   val aa = upd A_ i x a ();
 in
   (aa, n)
 end);

fun update_aa_u A_ a i j y =
  (fn () =>
    let
      val x = (fn () => Array.sub (a, Word32.toInt i)) ();
      val aa = arl_set A_ x j y ();
    in
      array_upd_u (heap_prod (heap_array (typerep_heap A_)) heap_nat) i aa a ()
    end);

fun arl_last A_ = (fn (a, n) => nth A_ a (minus_nat n one_nat));

fun last_aa_u A_ xs i =
  (fn () => let
              val x = (fn () => Array.sub (xs, Word32.toInt i)) ();
            in
              arl_last A_ x ()
            end);

fun delete_index_and_swap_aa_u A_ xs i j =
  (fn () => let
              val x = last_aa_u A_ xs i ();
              val xsa = update_aa_u A_ xs i j x ();
            in
              set_butlast_aa_u A_ xsa i ()
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

fun append_el_aa_u (A1_, A2_) =
  (fn a => fn i => fn x => fn () =>
    let
      val j = (fn () => Array.sub (a, Word32.toInt i)) ();
      val aa = arl_append (A1_, A2_) j x ();
      val _ = (fn () => Array.update (a, (Word32.toInt i), aa)) ();
    in
      a
    end);

fun update_raa (A1_, A2_) a i j y =
  (fn () => let
              val x = arl_get (heap_array (typerep_heap A2_)) a i ();
              val xa = upd A2_ j y x ();
            in
              arl_set (heap_array (typerep_heap A2_)) a i xa ()
            end);

fun swap_aa (A1_, A2_) xs k i j =
  (fn () => let
              val xi = nth_raa A2_ xs k i ();
              val xj = nth_raa A2_ xs k j ();
              val xsa = update_raa (A1_, A2_) xs k i xj ();
              val x = update_raa (A1_, A2_) xsa k j xi ();
            in
              x
            end);

fun update_clause_wl_code x =
  (fn ai => fn bid => fn bic => fn bib => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, a2e)))))) => fn () =>
    let
      val xa = nth_raa heap_uint32 a1a bid bia ();
      val x_b = swap_aa (default_uint32, heap_uint32) a1a bid bib bia ();
      val x_d = delete_index_and_swap_aa_u heap_nat a1e ai bic ();
      val xb = append_el_aa_u (default_nat, heap_nat) x_d xa bid ();
    in
      (bic, (a1, (x_b, (a1b, (a1c, (a1d, (xb, a2e)))))))
    end)
    x;

fun uminus_code l = Word32.xorb (l, (Word32.fromInt 1));

fun cons_trail_Propagated_tr_code x =
  (fn ai => fn bia => fn (a1, (a1a, (a1b, (a1c, a2c)))) => fn () =>
    let
      val xa =
        heap_array_set_u (heap_option heap_bool) a1a (atm_of_code ai)
          (SOME (is_pos_code ai)) ();
      val xaa = heap_array_set_u heap_uint32 a1b (atm_of_code ai) a2c ();
      val xb =
        heap_array_set_u (heap_option heap_nat) a1c (atm_of_code ai) (SOME bia)
          ();
    in
      (op_list_prepend ai a1, (xa, (xaa, (xb, a2c))))
    end)
    x;

fun fast_minus_nat x = (fn a => (Nat(integer_of_nat x - integer_of_nat a)));

fun propagate_lit_wl_code x =
  (fn ai => fn bib => fn bia => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) =>
    fn () =>
    let
      val xa =
        swap_aa (default_uint32, heap_uint32) a1a bib zero_nata
          (fast_minus_nat one_nat bia) ();
      val x_a = cons_trail_Propagated_tr_code ai bib a1 ();
    in
      (x_a, (xa, (a1b, (a1c, (uminus_code ai :: a1d, a2d)))))
    end)
    x;

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun polarity_st_heur_code x = (fn ai => fn bi => let
           val (a1, _) = ai;
         in
           polarity_pol_code a1 bi
         end)
                                x;

fun unit_propagation_inner_loop_body_wl_D_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = watched_by_app_heur_code bi ai bia ();
      val xaa = access_lit_in_clauses_heur_code bi xa zero_nata ();
    in
      let
        val x_b = (if ((xaa : Word32.word) = ai) then zero_nata else one_nat);
      in
        (fn f_ => fn () => f_
          ((access_lit_in_clauses_heur_code bi xa (fast_minus_nat one_nat x_b))
          ()) ())
          (fn x_d =>
            (fn f_ => fn () => f_ ((polarity_st_heur_code bi x_d) ()) ())
              (fn x_f =>
                (if equal_option equal_bool x_f (SOME true)
                  then (fn () => (plus_nat bia one_nat, bi))
                  else (fn f_ => fn () => f_
                         ((find_unwatched_wl_st_heur_code bi xa) ()) ())
                         (fn a =>
                           (case a
                             of NONE =>
                               (if equal_option equal_bool x_f (SOME false)
                                 then (fn f_ => fn () => f_
((set_conflict_wl_int_code xa bi) ()) ())
(fn x_l => (fn () => (plus_nat bia one_nat, x_l)))
                                 else (fn f_ => fn () => f_
((propagate_lit_wl_code x_d xa x_b bi) ()) ())
(fn x_l => (fn () => (plus_nat bia one_nat, x_l))))
                             | SOME x_j =>
                               update_clause_wl_code ai xa bia x_b x_j bi)))))
      end
        ()
    end)
    x;

fun arl_length A_ = (fn (_, a) => (fn () => a));

fun length_aa_u A_ xs i =
  (fn () => let
              val x = (fn () => Array.sub (xs, Word32.toInt i)) ();
            in
              arl_length A_ x ()
            end);

fun length_ll_fs_heur_code x =
  (fn ai => fn bi => let
                       val (_, (_, (_, (_, (_, (a1e, _)))))) = ai;
                     in
                       length_aa_u heap_nat a1e bi
                     end)
    x;

fun unit_propagation_inner_loop_wl_loop_D_code x =
  (fn ai => fn bi =>
    heap_WHILET
      (fn (a1, a2) => fn () => let
                                 val xa = length_ll_fs_heur_code a2 ai ();
                                 val x_b = get_conflict_wl_is_None_code a2 ();
                               in
                                 less_nat a1 xa andalso x_b
                               end)
      (fn (a, b) => unit_propagation_inner_loop_body_wl_D_code ai a b)
      (zero_nata, bi))
    x;

fun unit_propagation_inner_loop_wl_D_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = unit_propagation_inner_loop_wl_loop_D_code ai bi ();
    in
      snd xa
    end)
    x;

fun literals_to_update_wl_empty_heur_code x =
  (fn xi => (fn () => let
                        val (_, (_, (_, (_, (a1d, (_, _)))))) = xi;
                      in
                        op_list_is_empty a1d
                      end))
    x;

fun unit_propagation_outer_loop_wl_D x =
  heap_WHILET
    (fn s => fn () => let
                        val xa = literals_to_update_wl_empty_heur_code s ();
                      in
                        not xa
                      end)
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

fun get_count_max_lvls_code x =
  (fn (_, (_, (_, (_, (_, (_, (_, (_, (clvls, _))))))))) => clvls) x;

fun count_decided_st_code x = (fn xi => (fn () => let
            val (a1, _) = xi;
          in
            count_decided_pol a1
          end))
                                x;

fun maximum_level_removed_eq_count_dec_code x =
  (fn _ => fn bi => fn () =>
    let
      val xa = count_decided_st_code bi ();
    in
      ((xa : Word32.word) = (Word32.fromInt 0)) orelse
        Word32.< ((Word32.fromInt 1), get_count_max_lvls_code bi)
    end)
    x;

fun hd_trail_code x =
  (fn (a1, (_, (_, (a1c, _)))) => fn () =>
    let
      val x_a =
        (fn () => Array.sub (a1c, Word32.toInt (atm_of_code (op_list_hd a1))))
          ();
    in
      (op_list_hd a1, x_a)
    end)
    x;

fun lit_and_ann_of_propagated_st_heur_code x =
  (fn (a1, _) => fn () => let
                            val xa = hd_trail_code a1 ();
                            val xaa = hd_trail_code a1 ();
                          in
                            (fst xa, the (snd xaa))
                          end)
    x;

fun lookup_clause_assn_is_empty (B1_, B2_) =
  (fn (_, (n, _)) => eq B2_ n (zero B1_));

fun get_conflict_wll_is_Nil_code x =
  (fn xi =>
    (fn () =>
      let
        val (_, (_, (_, (a1c, (_, (_, _)))))) = xi;
      in
        (if lookup_clause_assn_is_None a1c then false
          else lookup_clause_assn_is_empty (zero_uint32, equal_uint32) a1c)
      end))
    x;

fun is_decided_wl_code x = (fn xi => (fn () => (is_None (snd xi)))) x;

fun is_decided_hd_trail_wl_code x =
  (fn (a1, _) => fn () => let
                            val xa = hd_trail_code a1 ();
                          in
                            is_decided_wl_code xa ()
                          end)
    x;

fun vmtf_mark_to_rescore_and_unset_code x =
  (fn ai => fn bi => fn () =>
    let
      val a =
        let
          val ((a1a, (a1b, (a1c, (a1d, a2d)))), a2) = bi;
        in
          (fn f_ => fn () => f_
            ((if is_None a2d then (fn () => true)
               else (fn f_ => fn () => f_
                      (((fn () => Array.sub (a1a, Word32.toInt (the a2d)))) ())
                      ())
                      (fn xa =>
                        (fn f_ => fn () => f_
                          (((fn () => Array.sub (a1a, Word32.toInt ai))) ()) ())
                          (fn xaa =>
                            (fn () => (less_nat (stamp xa) (stamp xaa))))))
            ()) ())
            (fn xa =>
              (fn () =>
                (if xa then ((a1a, (a1b, (a1c, (a1d, SOME ai)))), a2)
                  else ((a1a, (a1b, (a1c, (a1d, a2d)))), a2))))
        end
          ();
    in
      let
        val ((a1a, (a1b, (a1c, a2c))), a2) = a;
      in
        (fn f_ => fn () => f_ ((arl_append (default_uint32, heap_uint32) a2 ai)
          ()) ())
          (fn x_b => (fn () => ((a1a, (a1b, (a1c, a2c))), x_b)))
      end
        ()
    end)
    x;

fun fast_minus A_ m n = minus A_ m n;

fun fast_minus_uint32 x = fast_minus minus_uint32 x;

fun conflict_remove1_code x =
  (fn ai => fn (a1, a2) => fn () =>
    let
      val xa = (fn () => Array.sub (a2, Word32.toInt (atm_of_code ai))) ();
    in
      (if is_None xa then (fn () => (a1, a2))
        else (fn f_ => fn () => f_
               ((heap_array_set_u (heap_option heap_bool) a2 (atm_of_code ai)
                  NONE)
               ()) ())
               (fn x_b =>
                 (fn () => (fast_minus_uint32 a1 (Word32.fromInt 1), x_b))))
        ()
    end)
    x;

fun tl_trail_tr_code x =
  (fn (a1, (a1a, (a1b, (a1c, a2c)))) => fn () =>
    let
      val xa =
        heap_array_set_u (heap_option heap_bool) a1a
          (atm_of_code (op_list_hd a1)) NONE ();
      val xaa =
        heap_array_set_u heap_uint32 a1b (atm_of_code (op_list_hd a1))
          (Word32.fromInt 0) ();
      val xb =
        (fn () => Array.sub (a1c, Word32.toInt (atm_of_code (op_list_hd a1))))
          ();
    in
      (op_list_tl a1,
        (xa, (xaa, (a1c, (if is_None xb
                           then fast_minus_uint32 a2c (Word32.fromInt 1)
                           else a2c)))))
    end)
    x;

fun update_confl_tl_wl_code x =
  (fn ai => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, (a1h, a2h))))))))) =>
    (if equal_nat ai zero_nata
      then (fn () =>
             let
               val x_a = conflict_remove1_code (uminus_code bia) (snd a1c) ();
               val xa = tl_trail_tr_code a1 ();
               val xaa =
                 vmtf_mark_to_rescore_and_unset_code (atm_of_code bia) a1f ();
               val xb =
                 heap_array_set_u heap_bool a1g (atm_of_code bia)
                   (is_pos_code bia) ();
             in
               (let
                  val (n, _) = x_a;
                in
                  ((n : Word32.word) = (Word32.fromInt 0))
                end,
                 (xa, (a1a, (a1b, ((false, x_a),
                                    (a1d, (a1e,
    (xaa, (xb, (fast_minus_uint32 a1h (Word32.fromInt 1), a2h))))))))))
             end)
      else (fn () =>
             let
               val a = lookup_conflict_merge_code a1 a1a ai a1c a1h ();
             in
               let
                 val (a1i, a2i) = a;
               in
                 (fn f_ => fn () => f_ ((conflict_remove1_code bia (snd a1i))
                   ()) ())
                   (fn x_d =>
                     (fn f_ => fn () => f_ ((tl_trail_tr_code a1) ()) ())
                       (fn xa =>
                         (fn f_ => fn () => f_
                           ((vmtf_mark_to_rescore_and_unset_code
                              (atm_of_code bia) a1f)
                           ()) ())
                           (fn xaa =>
                             (fn f_ => fn () => f_
                               ((heap_array_set_u heap_bool a1g
                                  (atm_of_code bia) (is_pos_code bia))
                               ()) ())
                               (fn xb =>
                                 (fn () =>
                                   (let
                                      val (n, _) = x_d;
                                    in
                                      ((n : Word32.word) = (Word32.fromInt 0))
                                    end,
                                     (xa, (a1a,
    (a1b, ((false, x_d),
            (a1d, (a1e, (xaa, (xb, (fast_minus_uint32 a2i (Word32.fromInt 1),
                                     a2h)))))))))))))))
               end
                 ()
             end)))
    x;

fun tl_state_wl_heur_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, a2g)))))))) => fn () =>
    let
      val xa = hd_trail_code a1 ();
    in
      let
        val xb = fst xa;
      in
        (fn f_ => fn () => f_ ((tl_trail_tr_code a1) ()) ())
          (fn x_a =>
            (fn f_ => fn () => f_
              (let
                 val ((a1i, (a1j, (a1k, (a1l, a2l)))), a2h) = a1f;
               in
                 (fn f_ => fn () => f_
                   ((if is_None a2l then (fn () => true)
                      else (fn f_ => fn () => f_
                             (((fn () => Array.sub (a1i,
                                Word32.toInt (the a2l))))
                             ()) ())
                             (fn xaa =>
                               (fn f_ => fn () => f_
                                 (((fn () => Array.sub (a1i,
                                    Word32.toInt (atm_of_code xb))))
                                 ()) ())
                                 (fn xc =>
                                   (fn () =>
                                     (less_nat (stamp xaa) (stamp xc))))))
                   ()) ())
                   (fn x_b =>
                     (fn () =>
                       (if x_b
                         then ((a1i, (a1j, (a1k,
     (a1l, SOME (atm_of_code xb))))),
                                a2h)
                         else ((a1i, (a1j, (a1k, (a1l, a2l)))), a2h))))
               end
              ()) ())
              (fn xc =>
                (fn () =>
                  (x_a, (a1a, (a1b, (a1c, (a1d, (a1e, (xc, (a1g, a2g)))))))))))
      end
        ()
    end)
    x;

fun imp_option_eq eq a b =
  (case (a, b) of (NONE, NONE) => (fn () => true)
    | (NONE, SOME _) => (fn () => false) | (SOME _, NONE) => (fn () => false)
    | (SOME aa, SOME ba) => eq aa ba);

fun is_in_lookup_option_conflict_code x =
  (fn ai => fn (_, (_, a2a)) => fn () =>
    let
      val xa = (fn () => Array.sub (a2a, Word32.toInt (atm_of_code ai))) ();
    in
      imp_option_eq (fn va => fn vb => (fn () => (equal_boola va vb))) xa
        (SOME (is_pos_code ai)) ()
    end)
    x;

fun literal_is_in_conflict_heur_code x =
  (fn ai => fn (_, (_, (_, (a1c, _)))) =>
    is_in_lookup_option_conflict_code ai a1c)
    x;

fun skip_and_resolve_loop_wl_D_code x =
  (fn xi => fn () =>
    let
      val xa = get_conflict_wll_is_Nil_code xi ();
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
                  ((literal_is_in_conflict_heur_code (uminus_code a1a) a2) ())
                  ())
                  (fn xb =>
                    (if not xb
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
          (xa, xi) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun update_next_search l =
  (fn (a, b) => let
                  val (ns, (m, (fst_As, (lst_As, _)))) = a;
                in
                  (fn aa => ((ns, (m, (fst_As, (lst_As, l)))), aa))
                end
                  b);

fun defined_atm_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, _))) = ai;
    in
      (fn () => let
                  val xa = (fn () => Array.sub (a1a, Word32.toInt bi)) ();
                in
                  not (is_None xa)
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
            val x_b = (fn () => Array.sub (a1a, Word32.toInt (the s))) ();
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

fun lit_of_found_atm_D_code x =
  (fn ai => fn a =>
    (case a of NONE => (fn () => NONE)
      | SOME xa =>
        (fn () =>
          let
            val x_a = (fn () => Array.sub (ai, Word32.toInt xa)) ();
          in
            (if x_a then SOME (Word32.* ((Word32.fromInt 2), xa))
              else SOME (Word32.+ (Word32.* ((Word32.fromInt 2), xa), (Word32.fromInt 1))))
          end)))
    x;

fun find_unassigned_lit_wl_D_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, a2g)))))))) => fn () =>
    let
      val a = vmtf_find_next_undef_upd_code a1 a1f ();
    in
      let
        val ((a1i, a2i), a2h) = a;
      in
        (fn f_ => fn () => f_ ((lit_of_found_atm_D_code a1g a2h) ()) ())
          (fn x_a =>
            (fn () =>
              ((a1i, (a1a, (a1b, (a1c, (a1d, (a1e, (a2i, (a1g, a2g)))))))),
                x_a)))
      end
        ()
    end)
    x;

fun cons_trail_Decided_tr_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, a2c)))) => fn () =>
    let
      val xa =
        heap_array_set_u (heap_option heap_bool) a1a (atm_of_code ai)
          (SOME (is_pos_code ai)) ();
      val xaa =
        heap_array_set_u heap_uint32 a1b (atm_of_code ai)
          (Word32.+ (a2c, (Word32.fromInt 1))) ();
      val xb =
        heap_array_set_u (heap_option heap_nat) a1c (atm_of_code ai) NONE ();
    in
      (op_list_prepend ai a1,
        (xa, (xaa, (xb, Word32.+ (a2c, (Word32.fromInt 1))))))
    end)
    x;

fun decide_lit_wl_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, (_, a2d))))) => fn () =>
    let
      val xa = cons_trail_Decided_tr_code ai a1 ();
    in
      (xa, (a1a, (a1b, (a1c, ([uminus_code ai], a2d)))))
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
            (fn x_c => (fn () => (false, x_c))))
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

fun conflict_min_cach_l_code x =
  (fn ai => fn bi => let
                       val (a1, _) = ai;
                     in
                       (fn () => Array.sub (a1, Word32.toInt bi))
                     end)
    x;

fun conflict_min_cach_set_failed_l_code x =
  (fn ai => fn bi =>
    let
      val (a1, a2) = ai;
    in
      (fn () =>
        let
          val xa = heap_array_set_u heap_minimize_status a1 bi SEEN_FAILED ();
          val x_a = arl_append (default_uint32, heap_uint32) a2 bi ();
        in
          (xa, x_a)
        end)
    end)
    x;

fun array_copy A_ a =
  (fn () =>
    let
      val l = len A_ a ();
    in
      (if equal_nat l zero_nata then (fn () => Array.fromList [])
        else (fn f_ => fn () => f_ ((nth A_ a zero_nata) ()) ())
               (fn s =>
                 (fn f_ => fn () => f_ ((new A_ l s) ()) ())
                   (fn aa =>
                     (fn f_ => fn () => f_ ((blit A_ a zero_nata aa zero_nata l)
                       ()) ())
                       (fn _ => (fn () => aa)))))
        ()
    end);

fun nth_rl A_ xs n =
  (fn () => let
              val x = arl_get (heap_array (typerep_heap A_)) xs n ();
            in
              array_copy A_ x ()
            end);

fun mark_failed_lits_stack_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, _) =>
            (fn f_ => fn () => f_
              ((arl_length (heap_prod heap_nat heap_nat) bia) ()) ())
              (fn x_a => (fn () => (less_nat a1 x_a))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((arl_get (heap_prod heap_nat heap_nat) bia a1) ()) ())
              (fn (a1a, a2a) =>
                (fn f_ => fn () => f_ ((nth_rl heap_uint32 ai a1a) ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_
                      ((nth heap_uint32 xa (minus_nat a2a one_nat)) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_
                          ((conflict_min_cach_set_failed_l_code a2
                             (atm_of_code xb))
                          ()) ())
                          (fn x_d => (fn () => (plus_nat a1 one_nat, x_d)))))))
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

fun get_propagation_reason_code x =
  (fn ai => fn bi =>
    let
      val (_, (_, (_, (a1c, _)))) = ai;
    in
      (fn () => Array.sub (a1c, Word32.toInt (atm_of_code bi)))
    end)
    x;

fun arl_is_empty A_ = (fn (_, n) => (fn () => (equal_nat n zero_nata)));

fun lit_redundant_rec_wl_lookup_code x =
  (fn ai => fn bic => fn bib => fn bia => fn bi =>
    heap_WHILET
      (fn (_, (a1a, _)) => fn () =>
        let
          val x_a = arl_is_empty (heap_prod heap_nat heap_nat) a1a ();
        in
          not x_a
        end)
      (fn (a1, (a1a, _)) => fn () =>
        let
          val xa = arl_last (heap_prod heap_nat heap_nat) a1a ();
          val x_a = nth_rl heap_uint32 bic (fst xa) ();
          val xb = arl_last (heap_prod heap_nat heap_nat) a1a ();
          val xaa = len heap_uint32 x_a ();
        in
          (if less_eq_nat xaa (snd xb)
            then (fn f_ => fn () => f_ ((nth heap_uint32 x_a zero_nata) ()) ())
                   (fn xc =>
                     (fn f_ => fn () => f_
                       ((conflict_min_cach_set_removable_l_code a1
                          (atm_of_code xc))
                       ()) ())
                       (fn x_f =>
                         (fn f_ => fn () => f_
                           ((arl_butlast (heap_prod heap_nat heap_nat) a1a) ())
                           ())
                           (fn xd => (fn () => (x_f, (xd, true))))))
            else (fn f_ => fn () => f_
                   ((arl_last (heap_prod heap_nat heap_nat) a1a) ()) ())
                   (fn xc =>
                     (fn f_ => fn () => f_
                       (let
                          val (a1b, a2b) = xc;
                        in
                          (fn f_ => fn () => f_ ((nth heap_uint32 x_a a2b) ())
                            ())
                            (fn x_g =>
                              (fn f_ => fn () => f_
                                ((arl_length (heap_prod heap_nat heap_nat) a1a)
                                ()) ())
                                (fn xd =>
                                  (fn f_ => fn () => f_
                                    ((arl_set (heap_prod heap_nat heap_nat) a1a
                                       (minus_nat xd one_nat)
                                       (a1b, plus_nat a2b one_nat))
                                    ()) ())
                                    (fn x_h => (fn () => (x_g, x_h)))))
                        end
                       ()) ())
                       (fn (a1b, a2b) =>
                         (fn f_ => fn () => f_ ((get_level_code ai a1b) ()) ())
                           (fn xd =>
                             (fn f_ => fn () => f_
                               ((conflict_min_cach_l_code a1 (atm_of_code a1b))
                               ()) ())
                               (fn xab =>
                                 (fn f_ => fn () => f_
                                   ((is_in_conflict_code bib a1b) ()) ())
                                   (fn xba =>
                                     (if ((xd : Word32.word) = (Word32.fromInt 0)) orelse
   (equal_minimize_status xab SEEN_REMOVABLE orelse xba)
                                       then (fn () => (a1, (a2b, false)))
                                       else (fn f_ => fn () => f_
      ((get_propagation_reason_code ai (uminus_code a1b)) ()) ())
      (fn a =>
        (case a
          of NONE =>
            (fn f_ => fn () => f_ ((mark_failed_lits_stack_code bic a2b a1) ())
              ())
              (fn x_j =>
                (fn f_ => fn () => f_
                  ((arl_empty
                     (default_prod default_nat default_nat,
                       heap_prod heap_nat heap_nat)
                     zero_nat)
                  ()) ())
                  (fn xe => (fn () => (x_j, (xe, false)))))
          | SOME x_j =>
            (fn f_ => fn () => f_
              ((arl_append
                 (default_prod default_nat default_nat,
                   heap_prod heap_nat heap_nat)
                 a2b (x_j, one_nat))
              ()) ())
              (fn xe => (fn () => (a1, (xe, false)))))))))))))
            ()
        end)
      (bia, (bi, false)))
    x;

fun literal_redundant_wl_lookup_code x =
  (fn ai => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = get_level_code ai bi ();
      val xaa = conflict_min_cach_l_code bia (atm_of_code bi) ();
    in
      (if ((xa : Word32.word) = (Word32.fromInt 0)) orelse
            equal_minimize_status xaa SEEN_REMOVABLE
        then (fn f_ => fn () => f_
               ((arl_empty
                  (default_prod default_nat default_nat,
                    heap_prod heap_nat heap_nat)
                  zero_nat)
               ()) ())
               (fn xb => (fn () => (bia, (xb, true))))
        else (fn f_ => fn () => f_
               ((conflict_min_cach_l_code bia (atm_of_code bi)) ()) ())
               (fn xb =>
                 (if equal_minimize_status xb SEEN_FAILED
                   then (fn f_ => fn () => f_
                          ((arl_empty
                             (default_prod default_nat default_nat,
                               heap_prod heap_nat heap_nat)
                             zero_nat)
                          ()) ())
                          (fn xc => (fn () => (bia, (xc, false))))
                   else (fn f_ => fn () => f_
                          ((get_propagation_reason_code ai (uminus_code bi)) ())
                          ())
                          (fn a =>
                            (case a
                              of NONE =>
                                (fn f_ => fn () => f_
                                  ((arl_empty
                                     (default_prod default_nat default_nat,
                                       heap_prod heap_nat heap_nat)
                                     zero_nat)
                                  ()) ())
                                  (fn xc => (fn () => (bia, (xc, false))))
                              | SOME x_c =>
                                (fn f_ => fn () => f_
                                  ((arl_empty
                                     (default_prod default_nat default_nat,
                                       heap_prod heap_nat heap_nat)
                                     zero_nat)
                                  ()) ())
                                  (fn xc =>
                                    (fn f_ => fn () => f_
                                      ((arl_append
 (default_prod default_nat default_nat, heap_prod heap_nat heap_nat) xc
 (x_c, one_nat))
                                      ()) ())
                                      (lit_redundant_rec_wl_lookup_code ai bic
bib bia)))))))
        ()
    end)
    x;

fun lookup_conflict_upd_None_code x =
  (fn ai => fn bi =>
    let
      val (a1, a2) = ai;
    in
      (fn () =>
        let
          val x_a = heap_array_set_u (heap_option heap_bool) a2 bi NONE ();
        in
          (fast_minus_uint32 a1 (Word32.fromInt 1), x_a)
        end)
    end)
    x;

fun confl_find_next_index_code x =
  (fn ai => fn bi =>
    let
      val (_, a2) = ai;
    in
      heap_WHILET
        (fn s => fn () =>
          let
            val xa = (fn () => Array.sub (a2, Word32.toInt s)) ();
          in
            is_None xa
          end)
        (fn s => (fn () => (Word32.+ (s, (Word32.fromInt 1))))) bi
    end)
    x;

fun lookup_conflict_nth_code x =
  (fn ai => fn bi => let
                       val (_, a2) = ai;
                     in
                       (fn () => Array.sub (a2, Word32.toInt bi))
                     end)
    x;

fun minimize_and_extract_highest_lookup_conflict_code x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (_, (a1a, (_, (_, _)))) =>
            (fn () => (Word32.< ((Word32.fromInt 0), a1a))))
          (fn (a1, (a1a, (a1b, (a1c, a2c)))) =>
            (fn f_ => fn () => f_ ((confl_find_next_index_code a1 a1b) ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_ ((lookup_conflict_nth_code a1 x_a) ()) ())
                  (fn xa =>
                    let
                      val x_b =
                        (if the xa then Word32.* ((Word32.fromInt 2), x_a)
                          else Word32.+ (Word32.* ((Word32.fromInt 2), x_a), (Word32.fromInt 1)));
                    in
                      (fn f_ => fn () => f_
                        ((literal_redundant_wl_lookup_code ai bib a1 a1c x_b)
                        ()) ())
                        (fn (a1d, (_, a2e)) =>
                          (if not a2e
                            then (fn f_ => fn () => f_
                                   ((case a2c
                                      of NONE =>
(fn f_ => fn () => f_ ((get_level_code ai x_b) ()) ())
  (fn xb => (fn () => (SOME (x_b, xb))))
                                      | SOME (_, a2f) =>
(fn f_ => fn () => f_ ((get_level_code ai x_b) ()) ())
  (fn x_i =>
    (if Word32.< (a2f, x_i)
      then (fn f_ => fn () => f_ ((get_level_code ai x_b) ()) ())
             (fn xb => (fn () => (SOME (x_b, xb))))
      else (fn () => a2c))))
                                   ()) ())
                                   (fn xb =>
                                     (fn () =>
                                       (a1,
 (fast_minus_uint32 a1a (Word32.fromInt 1),
   (Word32.+ (x_a, (Word32.fromInt 1)), (a1d, xb))))))
                            else (fn f_ => fn () => f_
                                   ((lookup_conflict_upd_None_code a1 x_a) ())
                                   ())
                                   (fn x_f =>
                                     (fn () =>
                                       (x_f,
 (fast_minus_uint32 a1a (Word32.fromInt 1),
   (Word32.+ (x_a, (Word32.fromInt 1)), (a1d, a2c))))))))
                    end)))
          (bia, (fst bia, ((Word32.fromInt 0), (bi, NONE)))) ();
    in
      let
        val (a1, (_, (_, (a1c, a2c)))) = a;
      in
        (fn () => (a1, (a1c, a2c)))
      end
        ()
    end)
    x;

fun extract_shorter_conflict_list_lookup_heur_code x =
  (fn ai => fn bib => fn bia => fn (a1, (a1a, a2a)) => fn () =>
    let
      val xa = hd_trail_code ai ();
    in
      let
        val xb = fst xa;
      in
        (fn f_ => fn () => f_
          ((heap_array_set_u (heap_option heap_bool) a2a (atm_of_code xb) NONE)
          ()) ())
          (fn x_b =>
            (fn f_ => fn () => f_
              ((minimize_and_extract_highest_lookup_conflict_code ai bib
                 (fast_minus_uint32 a1a (Word32.fromInt 1), x_b) bia)
              ()) ())
              (fn ((a1c, a2c), (a1d, a2d)) =>
                (fn f_ => fn () => f_
                  ((heap_array_set_u (heap_option heap_bool) a2c
                     (atm_of_code xb) (SOME (not (is_pos_code xb))))
                  ()) ())
                  (fn xc =>
                    (fn () =>
                      ((a1, (Word32.+ (a1c, (Word32.fromInt 1)), xc)),
                        (a1d, a2d))))))
      end
        ()
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

fun extract_shorter_conflict_list_lookup_heur_st_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, (a1h, a2h))))))))) =>
    fn () =>
    let
      val a = extract_shorter_conflict_list_lookup_heur_code a1 a1a a2h a1c ();
    in
      let
        val (a1i, (a1j, a2j)) = a;
      in
        (fn f_ => fn () => f_ ((empty_cach_code a1j) ()) ())
          (fn x_a =>
            (fn () =>
              ((a1, (a1a, (a1b, (a1i, (a1d,
(a1e, (a1f, (a1g, (a1h, x_a))))))))),
                a2j)))
      end
        ()
    end)
    x;

fun vmtf_enqueue_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, _)))) =>
    (case a1b
      of NONE =>
        (fn () =>
          let
            val xa =
              heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) a1 ai
                (VMTF_Node (a1a, a1b, NONE)) ();
          in
            (xa, (plus_nat a1a one_nat, (ai, (ai, SOME ai))))
          end)
      | SOME xa =>
        (fn () =>
          let
            val xaa = (fn () => Array.sub (a1, Word32.toInt xa)) ();
            val xb = (fn () => Array.sub (a1, Word32.toInt xa)) ();
            val xc =
              heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) a1 ai
                (VMTF_Node (plus_nat a1a one_nat, NONE, SOME xa)) ();
            val x_b =
              heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) xc xa
                (VMTF_Node (stamp xaa, SOME ai, get_next xb)) ();
          in
            (x_b, (plus_nat a1a one_nat, (ai, (the a1c, SOME ai))))
          end)))
    x;

fun get_prev (VMTF_Node (x1, x2, x3)) = x2;

fun ns_vmtf_dequeue_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = (fn () => Array.sub (bi, Word32.toInt ai)) ();
      val x_a =
        (case get_prev xa of NONE => (fn () => bi)
          | SOME x_b =>
            (fn f_ => fn () => f_ (((fn () => Array.sub (bi, Word32.toInt x_b)))
              ()) ())
              (fn xaa =>
                (fn f_ => fn () => f_
                  (((fn () => Array.sub (bi, Word32.toInt x_b))) ()) ())
                  (fn xb =>
                    heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) bi
                      x_b (VMTF_Node (stamp xaa, get_prev xb, get_next xa)))))
          ();
      val x_b =
        (case get_next xa of NONE => (fn () => x_a)
          | SOME x_c =>
            (fn f_ => fn () => f_
              (((fn () => Array.sub (x_a, Word32.toInt x_c))) ()) ())
              (fn xaa =>
                (fn f_ => fn () => f_
                  (((fn () => Array.sub (x_a, Word32.toInt x_c))) ()) ())
                  (fn xb =>
                    heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) x_a
                      x_c (VMTF_Node (stamp xaa, get_prev xa, get_next xb)))))
          ();
      val xb = (fn () => Array.sub (x_b, Word32.toInt ai)) ();
    in
      heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) x_b ai
        (VMTF_Node (stamp xb, NONE, NONE)) ()
    end)
    x;

fun vmtf_dequeue_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, a2c)))) => fn () =>
    let
      val xa =
        (if ((a1b : Word32.word) = ai)
          then (fn f_ => fn () => f_
                 (((fn () => Array.sub (a1, Word32.toInt ai))) ()) ())
                 (fn x_a => (fn () => (get_next x_a)))
          else (fn () => (SOME a1b)))
          ();
      val xaa =
        imp_option_eq (fn va => fn vb => (fn () => ((va : Word32.word) = vb)))
          a2c (SOME ai) ();
      val x_a =
        (if xaa
          then (fn f_ => fn () => f_
                 (((fn () => Array.sub (a1, Word32.toInt ai))) ()) ())
                 (fn x_b => (fn () => (get_next x_b)))
          else (fn () => a2c))
          ();
      val x_b =
        (if ((a1c : Word32.word) = ai)
          then (fn f_ => fn () => f_
                 (((fn () => Array.sub (a1, Word32.toInt ai))) ()) ())
                 (fn x_c => (fn () => (get_prev x_c)))
          else (fn () => (SOME a1c)))
          ();
      val x_c = ns_vmtf_dequeue_code ai a1 ();
    in
      (x_c, (a1a, (xa, (x_b, x_a))))
    end)
    x;

fun vmtf_en_dequeue_code x =
  (fn ai => fn bi => fn () => let
                                val xa = vmtf_dequeue_code ai bi ();
                              in
                                vmtf_enqueue_code ai xa ()
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

fun insert_sort_inner_nth_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((arl_get heap_uint32 a2 bi) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  (((fn () => Array.sub (ai, Word32.toInt xa))) ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_ ((arl_get heap_uint32 a2 a1) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          (((fn () => Array.sub (ai, Word32.toInt xaa))) ()) ())
                          (fn xab =>
                            (fn () =>
                              (less_nat zero_nata a1 andalso
                                less_nat (stamp xb) (stamp xab))))))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((arl_swap heap_uint32 a2 a1 (fast_minus_nat a1 one_nat)) ()) ())
              (fn x_a => (fn () => (fast_minus_nat a1 one_nat, x_a))))
          (bi, bia) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun insert_sort_nth_code x =
  (fn ai => fn bi =>
    let
      val (a1, _) = ai;
    in
      (fn () =>
        let
          val a =
            heap_WHILET
              (fn (a1a, a2a) =>
                (fn f_ => fn () => f_ ((arl_length heap_uint32 a2a) ()) ())
                  (fn x_a => (fn () => (less_nat a1a x_a))))
              (fn (a1a, a2a) =>
                (fn f_ => fn () => f_ ((insert_sort_inner_nth_code a1 a2a a1a)
                  ()) ())
                  (fn x_a => (fn () => (plus_nat a1a one_nat, x_a))))
              (one_nat, bi) ();
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

fun vmtf_flush_code x =
  (fn (a1, a2) => fn () =>
    let
      val xa = insert_sort_nth_code a1 a2 ();
      val a =
        heap_WHILET
          (fn (a1a, _) =>
            (fn f_ => fn () => f_ ((arl_length heap_uint32 xa) ()) ())
              (fn x_b => (fn () => (less_nat a1a x_b))))
          (fn (a1a, a2a) =>
            (fn f_ => fn () => f_ ((arl_get heap_uint32 xa a1a) ()) ())
              (fn xb =>
                (fn f_ => fn () => f_ ((vmtf_en_dequeue_code xb a2a) ()) ())
                  (fn x_c => (fn () => (plus_nat a1a one_nat, x_c)))))
          (zero_nata, a1) ();
    in
      let
        val (_, a2a) = a;
      in
        (fn () => (a2a, emptied_arl xa))
      end
        ()
    end)
    x;

fun vmtf_flush_all_code x = (fn _ => vmtf_flush_code) x;

fun remove_last_code x =
  (fn ai => fn (_, (_, a2a)) => fn () =>
    let
      val xa =
        heap_array_set_u (heap_option heap_bool) a2a (atm_of_code ai) NONE ();
    in
      (true, ((Word32.fromInt 0), xa))
    end)
    x;

fun propagate_unit_bt_wl_D_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, (_, (a1e, (a1f, a2f))))))) => fn () =>
    let
      val xa = remove_last_code ai a1c ();
      val x_a = vmtf_flush_all_code a1 a1f ();
      val x_b = cons_trail_Propagated_tr_code (uminus_code ai) zero_nata a1 ();
    in
      (x_b, (a1a, (a1b, (xa, ([ai], (a1e, (x_a, a2f)))))))
    end)
    x;

fun vmtf_unset_code x =
  (fn ai => fn ((a1a, (a1b, (a1c, (a1d, a2d)))), a2) => fn () =>
    let
      val xa =
        (if is_None a2d then (fn () => true)
          else (fn f_ => fn () => f_
                 (((fn () => Array.sub (a1a, Word32.toInt (the a2d)))) ()) ())
                 (fn xa =>
                   (fn f_ => fn () => f_
                     (((fn () => Array.sub (a1a, Word32.toInt ai))) ()) ())
                     (fn xaa => (fn () => (less_nat (stamp xa) (stamp xaa))))))
          ();
    in
      (if xa then ((a1a, (a1b, (a1c, (a1d, SOME ai)))), a2)
        else ((a1a, (a1b, (a1c, (a1d, a2d)))), a2))
    end)
    x;

fun uint32_safe_minus (A1_, A2_, A3_) m n =
  (if less A3_ m n then zero A2_ else minus A1_ m n);

fun target_level B_ highest =
  (case highest of NONE => zero B_ | SOME (_, lev) => lev);

fun find_decomp_wl_imp_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, (_, _)) =>
            (fn () => (Word32.< (target_level zero_uint32 bia, a1))))
          (fn (a1, (a1a, a2a)) =>
            (fn f_ => fn () => f_ ((hd_trail_code a1a) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_ ((is_decided_wl_code xa) ()) ())
                  (fn x_e =>
                    (if x_e
                      then (fn f_ => fn () => f_ ((hd_trail_code a1a) ()) ())
                             (fn xb =>
                               (fn f_ => fn () => f_ ((tl_trail_tr_code a1a) ())
                                 ())
                                 (fn xaa =>
                                   (fn f_ => fn () => f_
                                     ((vmtf_unset_code (atm_of_code (fst xb))
a2a)
                                     ()) ())
                                     (fn xc =>
                                       (fn () =>
 (uint32_safe_minus (minus_uint32, zero_uint32, ord_uint32) a1
    (Word32.fromInt 1),
   (xaa, xc))))))
                      else (fn f_ => fn () => f_ ((hd_trail_code a1a) ()) ())
                             (fn xb =>
                               (fn f_ => fn () => f_ ((tl_trail_tr_code a1a) ())
                                 ())
                                 (fn xaa =>
                                   (fn f_ => fn () => f_
                                     ((vmtf_unset_code (atm_of_code (fst xb))
a2a)
                                     ()) ())
                                     (fn xc => (fn () => (a1, (xaa, xc))))))))))
          (count_decided_pol ai, (ai, bi)) ();
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

fun find_decomp_wl_imp_codea x =
  (fn _ => fn bia => fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) =>
    fn () =>
    let
      val a = find_decomp_wl_imp_code a1 bia a1f ();
    in
      let
        val (a1g, a2g) = a;
      in
        (fn () => (a1g, (a1a, (a1b, (a1c, (a1d, (a1e, (a2g, a2f))))))))
      end
        ()
    end)
    x;

fun lit_of_hd_trail_st_code x =
  (fn xi => (fn () => let
                        val ((a1a, _), _) = xi;
                      in
                        op_list_hd a1a
                      end))
    x;

fun conflict_to_conflict_with_cls_code x =
  (fn _ => fn _ => fn bia => fn (_, (a1a, a2a)) => fn () =>
    let
      val a =
        heap_WHILET
          (fn (_, (a1c, (_, _))) =>
            (fn () => (Word32.< ((Word32.fromInt 2), a1c))))
          (fn (a1b, (a1c, (a1d, a2d))) =>
            (fn f_ => fn () => f_
              (((fn () => Array.sub (a2d, Word32.toInt a1b))) ()) ())
              (fn a =>
                (case a
                  of NONE =>
                    (fn () =>
                      (Word32.+ (a1b, (Word32.fromInt 1)), (a1c, (a1d, a2d))))
                  | SOME x_b =>
                    (fn f_ => fn () => f_
                      ((heap_array_set_u heap_uint32 a1d
                         (fast_minus_uint32 a1c (Word32.fromInt 1))
                         (if x_b then Word32.* ((Word32.fromInt 2), a1b)
                           else Word32.+ (Word32.* ((Word32.fromInt 2), a1b), (Word32.fromInt 1))))
                      ()) ())
                      (fn xa =>
                        (fn f_ => fn () => f_
                          ((heap_array_set_u (heap_option heap_bool) a2d a1b
                             NONE)
                          ()) ())
                          (fn xaa =>
                            (fn () =>
                              (Word32.+ (a1b, (Word32.fromInt 1)),
                                (fast_minus_uint32 a1c (Word32.fromInt 1),
                                  (xa, xaa)))))))))
          ((Word32.fromInt 0), (a1a, (bia, a2a))) ();
    in
      let
        val (_, (_, (a1d, a2d))) = a;
      in
        (fn () => (a1d, (true, ((Word32.fromInt 0), a2d))))
      end
        ()
    end)
    x;

fun remove2_from_conflict_code x =
  (fn ai => fn bia => fn (a1, (a1a, a2a)) => fn () =>
    let
      val xa =
        heap_array_set_u (heap_option heap_bool) a2a (atm_of_code ai) NONE ();
      val xb =
        heap_array_set_u (heap_option heap_bool) xa (atm_of_code bia) NONE ();
    in
      (a1, (a1a, xb))
    end)
    x;

fun size_conflict_code x = ((fn a => (fn () => a)) o (fn (_, (n, _)) => n)) x;

fun list_of_mset2_None_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = size_conflict_code bi ();
      val x_b = new heap_uint32 (nat_of_uint32 xa) ai ();
      val x_d = upd heap_uint32 one_nat bia x_b ();
      val xb = remove2_from_conflict_code ai bia bi ();
    in
      conflict_to_conflict_with_cls_code ai bia x_d xb ()
    end)
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
            (fn f_ => fn () => f_
              (let
                 val ((a1c, (a1d, (a1e, a2e))), a2b) = a1a;
               in
                 (fn f_ => fn () => f_ ((nth heap_uint32 ai a1) ()) ())
                   (fn xa =>
                     (fn f_ => fn () => f_
                       ((arl_append (default_uint32, heap_uint32) a2b
                          (atm_of_code xa))
                       ()) ())
                       (fn x_b => (fn () => ((a1c, (a1d, (a1e, a2e))), x_b))))
               end
              ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_ ((nth heap_uint32 ai a1) ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((nth heap_uint32 ai a1) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          ((heap_array_set_u heap_bool a2a (atm_of_code xa)
                             (not (is_pos_code xaa)))
                          ()) ())
                          (fn x_c =>
                            (fn () => (plus_nat a1 one_nat, (x_a, x_c))))))))
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

fun length_ra A_ xs = arl_length (heap_array (typerep_heap A_)) xs;

fun propagate_bt_wl_D_code x =
  (fn ai => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (_, (a1e, (a1f, (a1g, (_, a2h))))))))) => fn () =>
    let
      val a = list_of_mset2_None_code (uminus_code ai) bia a1c ();
    in
      let
        val (a1i, a2i) = a;
      in
        (fn f_ => fn () => f_ ((vmtf_rescore_code a1i a1 a1f a1g) ()) ())
          (fn (a1j, a2j) =>
            (fn f_ => fn () => f_ ((vmtf_flush_all_code a1 a1j) ()) ())
              (fn x_b =>
                (fn f_ => fn () => f_ ((length_ra heap_uint32 a1a) ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_
                      ((append_el_aa_u (default_nat, heap_nat) a1e
                         (uminus_code ai) xa)
                      ()) ())
                      (fn x_c =>
                        (fn f_ => fn () => f_ ((length_ra heap_uint32 a1a) ())
                          ())
                          (fn xb =>
                            (fn f_ => fn () => f_
                              ((append_el_aa_u (default_nat, heap_nat) x_c bia
                                 xb)
                              ()) ())
                              (fn x_e =>
                                (fn f_ => fn () => f_
                                  ((length_ra heap_uint32 a1a) ()) ())
                                  (fn xc =>
                                    (fn f_ => fn () => f_
                                      ((cons_trail_Propagated_tr_code
 (uminus_code ai) xc a1)
                                      ()) ())
                                      (fn x_g =>
(fn f_ => fn () => f_ ((arrayO_raa_append (default_uint32, heap_uint32) a1a a1i)
  ()) ())
  (fn xd =>
    (fn () =>
      (x_g, (xd, (a1b, (a2i, ([ai],
                               (x_e, (x_b, (a2j,
     ((Word32.fromInt 0), a2h)))))))))))))))))))
      end
        ()
    end)
    x;

fun size_conflict_wl_code x =
  (fn xi =>
    (fn () => let
                val (_, (_, (_, ((_, (n, _)), (_, (_, (_, _))))))) = xi;
              in
                n
              end))
    x;

fun backtrack_wl_D_code x =
  (fn xi => fn () =>
    let
      val xa = lit_of_hd_trail_st_code xi ();
      val a = extract_shorter_conflict_list_lookup_heur_st_code xi ();
    in
      let
        val (a1, a2) = a;
      in
        (fn f_ => fn () => f_ ((find_decomp_wl_imp_codea xa a2 a1) ()) ())
          (fn x_c =>
            (fn f_ => fn () => f_ ((size_conflict_wl_code x_c) ()) ())
              (fn xaa =>
                (if Word32.< ((Word32.fromInt 1), xaa)
                  then propagate_bt_wl_D_code xa (fst (the a2)) x_c
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
        else (fn f_ => fn () => f_ ((skip_and_resolve_loop_wl_D_code xi) ()) ())
               (fn x_a =>
                 (fn f_ => fn () => f_ ((get_conflict_wll_is_Nil_code x_a) ())
                   ())
                   (fn xb =>
                     (if not xb
                       then (fn f_ => fn () => f_ ((backtrack_wl_D_code x_a) ())
                              ())
                              (fn x_c => (fn () => (false, x_c)))
                       else (fn () => (true, x_a))))))
        ()
    end)
    x;

fun cdcl_twl_stgy_prog_wl_D_code x =
  (fn xi => fn () =>
    let
      val a =
        heap_WHILET (fn (a1, _) => (fn () => (not a1)))
          (fn (_, a2) =>
            (fn f_ => fn () => f_ ((unit_propagation_outer_loop_wl_D a2) ()) ())
              cdcl_twl_o_prog_wl_D_code)
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

fun set_conflict_empty_code x = (fn xi => (fn () => let
              val (_, a) = xi;
            in
              (false, a)
            end))
                                  x;

fun set_empty_clause_as_conflict_code x =
  (fn (a1, (a1a, (a1b, (a1c, (_, a2d))))) => fn () =>
    let
      val xa = set_conflict_empty_code a1c ();
    in
      (a1, (a1a, (a1b, (xa, ([], a2d)))))
    end)
    x;

fun set_conflict_unit_code x =
  (fn ai => fn (_, (_, a2a)) => fn () =>
    let
      val xa =
        heap_array_set_u (heap_option heap_bool) a2a (atm_of_code ai)
          (SOME (is_pos_code ai)) ();
    in
      (false, ((Word32.fromInt 1), xa))
    end)
    x;

fun conflict_propagated_unit_cls_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, (_, a2d))))) => fn () =>
    let
      val xa = set_conflict_unit_code ai a1c ();
    in
      (a1, (a1a, (a1b, (xa, ([], a2d)))))
    end)
    x;

fun already_propagated_unit_cls_code x =
  (fn _ => fn bi =>
    (fn () => let
                val (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) = bi;
              in
                (a1, (a1a, (a1b, (a1c, (a1d, a2d)))))
              end))
    x;

fun polarity_st_heur_init_code x =
  (fn ai => fn bi => let
                       val (a1, _) = ai;
                     in
                       polarity_pol_code a1 bi
                     end)
    x;

fun add_clause_to_others_code x =
  (fn _ => fn bi => (fn () => let
                                val (a1, (a1a, (a1b, (a1c, (_, a2d))))) = bi;
                              in
                                (a1, (a1a, (a1b, (a1c, ([], a2d)))))
                              end))
    x;

fun propagate_unit_cls_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = cons_trail_Propagated_tr_code ai zero_nata a1 ();
    in
      (xa, (a1a, (a1b, (a1c, (uminus_code ai :: a1d, a2d)))))
    end)
    x;

fun add_init_cls_code x =
  (fn ai => fn (a1, (a1a, (_, (a1c, (a1d, (a1e, a2e)))))) => fn () =>
    let
      val xa = length_ra heap_uint32 a1a ();
      val x_b =
        append_el_aa_u (default_nat, heap_nat) a1e (op_list_hd ai) xa ();
      val x_d =
        append_el_aa_u (default_nat, heap_nat) x_b (op_list_hd (op_list_tl ai))
          xa ();
      val xaa = (fn () => Array.fromList ai) ();
      val xab = arrayO_raa_append (default_uint32, heap_uint32) a1a xaa ();
    in
      (a1, (xab, (xa, (a1c, (a1d, (x_d, a2e))))))
    end)
    x;

fun size_list x = gen_length zero_nata x;

fun op_list_length x = size_list x;

fun init_dt_step_wl_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = get_conflict_wl_is_None_init_code bi ();
    in
      (if xa
        then (if equal_nat (op_list_length ai) zero_nata
               then set_empty_clause_as_conflict_code bi
               else (if equal_nat (op_list_length ai) one_nat
                      then let
                             val x_c = op_list_hd ai;
                           in
                             (fn f_ => fn () => f_
                               ((polarity_st_heur_init_code bi x_c) ()) ())
                               (fn x_e =>
                                 (if is_None x_e
                                   then propagate_unit_cls_code x_c bi
                                   else (fn f_ => fn () => f_
  ((imp_option_eq (fn va => fn vb => (fn () => (equal_boola va vb))) x_e
     (SOME true))
  ()) ())
  (fn x_h =>
    (if x_h then already_propagated_unit_cls_code x_c bi
      else conflict_propagated_unit_cls_code x_c bi))))
                           end
                      else add_init_cls_code ai bi))
        else add_clause_to_others_code ai bi)
        ()
    end)
    x;

fun init_dt_wl_code x =
  (fn ai => imp_nfoldli ai (fn _ => (fn () => true)) init_dt_step_wl_code) x;

fun get_trail_wl_code x = (fn (a, b) => let
  val (m, _) = a;
in
  (fn _ => m)
end
  b)
                            x;

fun isaSAT_code x =
  (fn xi => fn () =>
    let
      val xa = extract_atms_clss_imp_empty_assn ();
      val xb = extract_atms_clss_imp_list_assn xi xa ();
      val x_b = init_state_wl_D_code xb ();
      val x_f = init_dt_wl_code xi (to_init_state_code x_b) ();
    in
      let
        val x_g = from_init_state_code x_f;
      in
        (fn f_ => fn () => f_ ((get_conflict_wl_is_None_init_code x_g) ()) ())
          (fn xc =>
            (if not xc then (fn () => NONE)
              else (if op_list_is_empty xi then (fn () => (SOME []))
                     else (fn f_ => fn () => f_ ((finalise_init_code x_g) ())
                            ())
                            (fn x_k =>
                              (fn f_ => fn () => f_
                                ((cdcl_twl_stgy_prog_wl_D_code x_k) ()) ())
                                (fn x_m =>
                                  (fn f_ => fn () => f_
                                    ((get_conflict_wl_is_None_code x_m) ()) ())
                                    (fn x_n =>
                                      (fn () =>
(if x_n then SOME (get_trail_wl_code x_m) else NONE))))))))
      end
        ()
    end)
    x;

fun integer_of_int (Int_of_integer k) = k;

fun uint32_of_int i = Word32.fromLargeInt (IntInf.toLarge (integer_of_int i));

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun uint32_of_nat x = (uint32_of_int o int_of_nat) x;

end; (*struct SAT_Solver*)
