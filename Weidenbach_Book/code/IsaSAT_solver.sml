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
  type ('a, 'b) vmtf_node
  type minimize_status
  datatype int = Int_of_integer of IntInf.int
  val nat_of_integer : IntInf.int -> nat
  val integer_of_int : int -> IntInf.int
  val uint32_of_nat : nat -> Word32.word
  val isaSAT_code :
    (Word32.word list) list ->
      (unit ->
        ((Word32.word array * nat) option *
          (Uint64.uint64 * (Uint64.uint64 * Uint64.uint64))))
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

val one_nata : nat = Nat (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

val zero_nata : nat = Nat (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

val default_nata : nat = zero_nata;

type 'a default = {default : 'a};
val default = #default : 'a default -> 'a;

val default_nat = {default = default_nata} : nat default;

fun integer_of_nat (Nat x) = x;

fun times_nata m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_nat = {times = times_nata} : nat times;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

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

fun typerep_optiona A_ t = Typerep ("Option.option", [typerep A_ Type]);

fun countable_option A_ = {} : ('a option) countable;

fun typerep_option A_ = {typerep = typerep_optiona A_} : ('a option) typerep;

fun heap_option A_ =
  {countable_heap = countable_option (countable_heap A_),
    typerep_heap = typerep_option (typerep_heap A_)}
  : ('a option) heap;

fun typerep_uint32a t = Typerep ("Uint32.uint32", []);

val countable_uint32 = {} : Word32.word countable;

val typerep_uint32 = {typerep = typerep_uint32a} : Word32.word typerep;

val heap_uint32 =
  {countable_heap = countable_uint32, typerep_heap = typerep_uint32} :
  Word32.word heap;

val one_uint32 = {one = (Word32.fromInt 1)} : Word32.word one;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_uint32 = {plus = (fn a => fn b => Word32.+ (a, b))} : Word32.word plus;

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

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_uint32 = {minus = (fn a => fn b => Word32.- (a, b))} :
  Word32.word minus;

val times_uint32 = {times = (fn a => fn b => Word32.* (a, b))} :
  Word32.word times;

val ord_uint32 =
  {less_eq = (fn a => fn b => Word32.<= (a, b)),
    less = (fn a => fn b => Word32.< (a, b))}
  : Word32.word ord;

fun typerep_uint64a t = Typerep ("Uint64.uint64", []);

val countable_uint64 = {} : Uint64.uint64 countable;

val typerep_uint64 = {typerep = typerep_uint64a} : Uint64.uint64 typerep;

val heap_uint64 =
  {countable_heap = countable_uint64, typerep_heap = typerep_uint64} :
  Uint64.uint64 heap;

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

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

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

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun suc n = plus_nat n one_nata;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

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

fun blit A_ src si dst di len =
  (fn () => 
    array_blit src (integer_of_nat
                     si) dst (integer_of_nat di) (integer_of_nat len));

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

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

fun lookup_clause_assn_is_None x = (fn (b, (_, _)) => b) x;

fun get_conflict_wl_is_None_init_fast_code x =
  (fn xi => (fn () => let
                        val (_, (_, (a1b, (_, (_, _))))) = xi;
                      in
                        lookup_clause_assn_is_None a1b
                      end))
    x;

fun get_conflict_wl_is_None_init_code x =
  (fn xi => (fn () => let
                        val (_, (_, (a1b, (_, (_, _))))) = xi;
                      in
                        lookup_clause_assn_is_None a1b
                      end))
    x;

val initial_capacity : nat = nat_of_integer (16 : IntInf.int);

fun arl_empty (A1_, A2_) B_ =
  (fn () => let
              val a = new A2_ initial_capacity (default A1_) ();
            in
              (a, zero B_)
            end);

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

val uNSET_code : Word32.word = (Word32.fromInt 0);

fun init_trail_D_fast_code x =
  (fn _ => fn bia => fn bi => fn () =>
    let
      val xa = arl_empty (default_uint32, heap_uint32) zero_nat ();
      val x_b = arl_empty (default_uint32, heap_uint32) zero_nat ();
      val x_d = new heap_uint32 bi uNSET_code ();
      val x_f = new heap_uint32 bia (Word32.fromInt 0) ();
      val x_h = new (heap_option heap_uint32) bia NONE ();
    in
      (xa, (x_d, (x_f, (x_h, ((Word32.fromInt 0), x_b)))))
    end)
    x;

fun get_next (VMTF_Node (x1, x2, x3)) = x3;

fun stamp (VMTF_Node (x1, x2, x3)) = x1;

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

fun arl_is_empty A_ = (fn (_, n) => (fn () => (equal_nat n zero_nata)));

fun heap_array_set_ua A_ =
  (fn a => fn b => fn c => (fn () => Array.update (a, (Word32.toInt b), c)));

fun heap_array_set_u A_ a i x =
  (fn () => let
              val _ = heap_array_set_ua A_ a i x ();
            in
              a
            end);

fun arl_get A_ = (fn (a, _) => nth A_ a);

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

fun initialise_VMTF_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        new (heap_vmtf_node heap_uint32 heap_nat) bi
          (VMTF_Node (zero_nata, NONE, NONE)) ();
      val a =
        heap_WHILET
          (fn (a1, (_, (_, _))) =>
            (fn f_ => fn () => f_ ((length_arl_u_code heap_uint32 ai) ()) ())
              (fn x_c => (fn () => (Word32.< (a1, x_c)))))
          (fn (a1, (a1a, (a1b, a2b))) =>
            (fn f_ => fn () => f_
              (((fn () => Array.sub ((fn (a,b) => a) ai, Word32.toInt a1))) ())
              ())
              (fn x_c =>
                (fn f_ => fn () => f_
                  ((heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) a1a
                     x_c (VMTF_Node (suc a1b, NONE, a2b)))
                  ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_
                      ((case a2b of NONE => (fn () => xb)
                         | SOME x_g =>
                           (fn f_ => fn () => f_
                             ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat)
                                xb x_g)
                             ()) ())
                             (fn xaa =>
                               (fn f_ => fn () => f_
                                 ((nth_u_code
                                    (heap_vmtf_node heap_uint32 heap_nat) xb
                                    x_g)
                                 ()) ())
                                 (fn xba =>
                                   heap_array_set_u
                                     (heap_vmtf_node heap_uint32 heap_nat) xb
                                     x_g (VMTF_Node
   (stamp xaa, SOME x_c, get_next xba)))))
                      ()) ())
                      (fn xc =>
                        (fn () =>
                          (Word32.+ (a1, (Word32.fromInt 1)),
                            (xc, (plus_nat a1b one_nata, SOME x_c))))))))
          ((Word32.fromInt 0), (xa, (zero_nata, NONE))) ();
    in
      let
        val (_, (a1a, (a1b, a2b))) = a;
      in
        (fn f_ => fn () => f_ ((arl_is_empty heap_uint32 ai) ()) ())
          (fn xb =>
            (fn f_ => fn () => f_
              ((if xb then (fn () => NONE)
                 else (fn f_ => fn () => f_ ((arl_get heap_uint32 ai zero_nata)
                        ()) ())
                        (fn x_d => (fn () => (SOME x_d))))
              ()) ())
              (fn xc =>
                (fn f_ => fn () => f_
                  ((arl_empty (default_uint32, heap_uint32) zero_nat) ()) ())
                  (fn x_d => (fn () => ((a1a, (a1b, (a2b, (xc, a2b)))), x_d)))))
      end
        ()
    end)
    x;

fun imp_for i u f s =
  (if less_eq_nat u i then (fn () => s)
    else (fn () => let
                     val x = f i s ();
                   in
                     imp_for (plus_nat i one_nata) u f x ()
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
               (fn aa => (fn () => (aa, plus_nat n one_nata)))
        else let
               val newcap = times_nata (nat_of_integer (2 : IntInf.int)) lena;
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
                         (fn ab => (fn () => (ab, plus_nat n one_nata)))))
             end)
        ()
    end);

fun init_rll_list_code x =
  (fn xi => fn () =>
    let
      val xa = (fn () => Array.fromList []) ();
      val x_b =
        arrayO_raa_empty_sz (default_uint32, heap_uint32) zero_nat xi ();
    in
      arrayO_raa_append (default_uint32, heap_uint32) x_b xa ()
    end)
    x;

fun nat_of_uint32 x =
  nat_of_integer (IntInf.fromLarge (Word32.toLargeInt x) : IntInf.int);

val empty_lbd_code : (unit -> (bool array * Word32.word)) =
  (fn () =>
    let
      val x = new heap_bool (nat_of_integer (32 : IntInf.int)) false ();
    in
      (x, (Word32.fromInt 0))
    end);

fun init_state_wl_D_fast_code x =
  (fn (a1, a2) =>
    let
      val x_a = suc (nat_of_uint32 a2);
      val x_c = times_nata (nat_of_integer (2 : IntInf.int)) x_a;
    in
      (fn () =>
        let
          val x_e = init_trail_D_fast_code a1 x_a x_c ();
          val x_f = init_rll_list_code x_a ();
          val xa = new heap_bool x_a false ();
          val x_j =
            arrayO_ara_empty_sz_code (default_uint32, heap_uint32) x_c ();
          val x_l = initialise_VMTF_code a1 x_a ();
          val x_m = new heap_bool x_a false ();
          val xaa = new heap_minimize_status x_a SEEN_UNKNOWN ();
          val xb = arl_empty (default_uint32, heap_uint32) zero_nat ();
          val x_q = empty_lbd_code ();
        in
          (x_e, (x_f, ((true, ((Word32.fromInt 0), xa)),
                        ([], (x_j, (x_l, (x_m,
   ((Word32.fromInt 0), ((xaa, xb), x_q)))))))))
        end)
    end)
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

fun finalise_init_fast_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (((a1g, (a1h, (a1i, (a1j, a2j)))), a2f),
                                     (a1k, (a1l, (a1m, a2m)))))))))
     =>
    fn () =>
    let
      val xa =
        arl_replicate heap_uint32 (nat_of_integer (160 : IntInf.int))
          (Word32.* ((Word32.fromInt 2), (Word32.fromInt 0))) ();
    in
      (a1, (a1a, (a1b, (a1c, (a1d, (((a1g, (a1h, (the a1i, (the a1j, a2j)))),
                                      a2f),
                                     (a1k, (a1l,
     (a1m, (a2m, (let
                    val (a, _) = xa;
                  in
                    (a, one_nata)
                  end,
                   ((Uint64.zero, (Uint64.zero, Uint64.zero)),
                     (Uint64.zero,
                       (Uint64.zero, (Word32.fromInt 0)))))))))))))))
    end)
    x;

fun extract_lits_sorted_code x =
  (fn xi => (fn () => let
                        val (_, (a1a, a2a)) = xi;
                      in
                        (a2a, a1a)
                      end))
    x;

fun op_list_tl x = tl x;

fun op_list_hd x = hd x;

fun select_and_remove_from_literals_to_update_wl_fast_code x =
  (fn xi =>
    (fn () =>
      let
        val (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) = xi;
      in
        ((a1, (a1a, (a1b, (op_list_tl a1c, (a1d, a2d))))), op_list_hd a1c)
      end))
    x;

fun nth_u64_code A_ =
  (fn a => fn b => (fn () => Array.sub (a, Uint64.toFixedInt b)));

fun nth_raa_i32_u64 A_ xs i j =
  (fn () =>
    let
      val x = (fn () => Array.sub ((fn (a,b) => a) xs, Word32.toInt i)) ();
      val xa = nth_u64_code A_ x j ();
    in
      xa
    end);

fun access_lit_in_clauses_heur_fast_code x =
  (fn ai => fn bia => fn bi => let
                                 val (_, (a1a, _)) = ai;
                               in
                                 nth_raa_i32_u64 heap_uint32 a1a bia bi
                               end)
    x;

fun polarity_pol_fast_code x =
  (fn ai => fn bi => let
                       val (_, (a1a, (_, _))) = ai;
                     in
                       nth_u_code heap_uint32 a1a bi
                     end)
    x;

fun length_u64_code A_ =
  (fn a => (fn () => Uint64.fromFixedInt (Array.length a)));

fun length_raa_u32_u64 A_ xs i =
  (fn () =>
    let
      val x = (fn () => Array.sub ((fn (a,b) => a) xs, Word32.toInt i)) ();
    in
      length_u64_code A_ x ()
    end);

fun is_None a = (case a of NONE => true | SOME _ => false);

val sET_TRUE_code : Word32.word =
  Word32.fromLargeInt (IntInf.toLarge (2 : IntInf.int));

fun fst (x1, x2) = x1;

fun find_unwatched_wl_st_heur_fast_code x =
  (fn ai => fn bi =>
    let
      val (a1, (a1a, (_, (_, (_, (_, _)))))) = ai;
    in
      (fn () =>
        let
          val xa =
            heap_WHILET
              (fn (a1f, a2f) =>
                (fn f_ => fn () => f_ ((length_raa_u32_u64 heap_uint32 a1a bi)
                  ()) ())
                  (fn xa =>
                    (fn () => (is_None a1f andalso Uint64.less a2f xa))))
              (fn (_, a2f) =>
                (fn f_ => fn () => f_ ((nth_raa_i32_u64 heap_uint32 a1a bi a2f)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((polarity_pol_fast_code a1 xa) ())
                      ())
                      (fn x_a =>
                        (fn () =>
                          (if ((x_a : Word32.word) = uNSET_code)
                            then (SOME a2f, a2f)
                            else (if ((x_a : Word32.word) = sET_TRUE_code)
                                   then (SOME a2f, a2f)
                                   else (NONE, Uint64.plus a2f Uint64.one)))))))
              (NONE, Uint64.fromInt (2 : IntInf.int)) ();
        in
          fst xa
        end)
    end)
    x;

fun shiftr_uint32 x n =
  (if less_nat n (nat_of_integer (32 : IntInf.int))
    then Uint32.shiftr x (integer_of_nat n) else (Word32.fromInt 0));

fun atm_of_code l = shiftr_uint32 l one_nata;

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

fun length_u_code A_ = (fn a => (fn () => Word32.fromInt (Array.length a)));

fun length_raa_i32_u A_ xs i =
  (fn () =>
    let
      val x = (fn () => Array.sub ((fn (a,b) => a) xs, Word32.toInt i)) ();
    in
      length_u_code A_ x ()
    end);

fun count_decided_pol x = (fn (_, (_, (_, (_, (k, _))))) => k) x;

fun arl_append (A1_, A2_) =
  (fn (a, n) => fn x => fn () =>
    let
      val lena = len A2_ a ();
    in
      (if less_nat n lena
        then (fn f_ => fn () => f_ ((upd A2_ n x a) ()) ())
               (fn aa => (fn () => (aa, plus_nat n one_nata)))
        else let
               val newcap = times_nata (nat_of_integer (2 : IntInf.int)) lena;
             in
               (fn f_ => fn () => f_ ((array_grow A2_ a newcap (default A1_))
                 ()) ())
                 (fn aa =>
                   (fn f_ => fn () => f_ ((upd A2_ n x aa) ()) ())
                     (fn ab => (fn () => (ab, plus_nat n one_nata))))
             end)
        ()
    end);

fun nth_raa_i32_u32 A_ xs i j =
  (fn () =>
    let
      val x = (fn () => Array.sub ((fn (a,b) => a) xs, Word32.toInt i)) ();
      val xa = nth_u_code A_ x j ();
    in
      xa
    end);

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
                (fn f_ => fn () => f_ ((length_raa_i32_u heap_uint32 bie bid)
                  ()) ())
                  (fn x_a => (fn () => (Word32.< (a1a, x_a)))))
              (fn (a1a, (a1b, (a1c, (a1d, a2d)))) =>
                (fn f_ => fn () => f_ ((nth_raa_i32_u32 heap_uint32 bie bid a1a)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((get_level_fast_code ai xa) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((lbd_write_code a1d xb true) ())
                          ())
                          (fn x_a =>
                            (fn f_ => fn () => f_
                              ((nth_raa_i32_u32 heap_uint32 bie bid a1a) ()) ())
                              (fn xc =>
                                (fn f_ => fn () => f_
                                  ((get_level_fast_code ai xc) ()) ())
                                  (fn xd =>
                                    (fn f_ => fn () => f_
                                      ((nth_raa_i32_u32 heap_uint32 bie bid a1a)
                                      ()) ())
                                      (fn xaa =>
(fn f_ => fn () => f_ ((is_in_conflict_code a1c xaa) ()) ())
  (fn xab =>
    (fn f_ => fn () => f_
      ((if Word32.< (xd, count_decided_pol ai) andalso not xab
         then (fn f_ => fn () => f_ ((nth_raa_i32_u32 heap_uint32 bie bid a1a)
                ()) ())
                (arl_append (default_uint32, heap_uint32) a2d)
         else (fn () => a2d))
      ()) ())
      (fn x_c =>
        (fn f_ => fn () => f_ ((nth_raa_i32_u32 heap_uint32 bie bid a1a) ()) ())
          (fn xe =>
            (fn f_ => fn () => f_ ((get_level_fast_code ai xe) ()) ())
              (fn xf =>
                (fn f_ => fn () => f_ ((nth_raa_i32_u32 heap_uint32 bie bid a1a)
                  ()) ())
                  (fn xac =>
                    (fn f_ => fn () => f_ ((is_in_conflict_code a1c xac) ()) ())
                      (fn xad =>
                        (fn f_ => fn () => f_
                          (let
                             val (a1e, a2e) = a1c;
                           in
                             (fn f_ => fn () => f_
                               ((nth_raa_i32_u32 heap_uint32 bie bid a1a) ())
                               ())
                               (fn xg =>
                                 (fn f_ => fn () => f_
                                   ((nth_u_code heap_bool a2e (atm_of_code xg))
                                   ()) ())
                                   (fn xh =>
                                     (fn f_ => fn () => f_
                                       ((nth_raa_i32_u32 heap_uint32 bie bid
  a1a)
                                       ()) ())
                                       (fn xae =>
 (fn f_ => fn () => f_ ((nth_raa_i32_u32 heap_uint32 bie bid a1a) ()) ())
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
                              (Word32.+ (a1a, (Word32.fromInt 1)),
                                ((if ((xf : Word32.word) = (count_decided_pol
                     ai)) andalso
                                       not xad
                                   then Word32.+ (a1b, (Word32.fromInt 1))
                                   else a1b),
                                  (x_g, (x_a, x_c)))))))))))))))))))
              ((Word32.fromInt 0), (bib, (a2, (bia, bi)))) ();
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
        (fn () =>
          (a1, (a1a, (a1m, ([], (a1d, (a1e,
(a1f, (a1n, (a1h, (a1o, (a2o, (incr_conflict a1k, (a1l, a2l))))))))))))))
      end
        ()
    end)
    x;

fun arl_get_u64 A_ =
  (fn a => fn b =>
    (fn () => Array.sub ((fn (a,b) => a) a, Uint64.toFixedInt b)));

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
  (fn ai => fn bia => fn bi => let
                                 val (_, (_, (_, (_, (a1d, _))))) = ai;
                               in
                                 nth_aa_i32_u64 heap_uint32 a1d bia bi
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

fun arl_set_u64 A_ a i x =
  (fn () => let
              val b = array_upd_u64 A_ i x (fst a) ();
            in
              (b, snd a)
            end);

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

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

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
      val na = minus_nat n one_nata;
    in
      (fn () =>
        let
          val lena = len A_ a ();
        in
          (if less_nat (times_nata na (nat_of_integer (4 : IntInf.int)))
                lena andalso
                less_eq_nat minimum_capacity
                  (times_nata na (nat_of_integer (2 : IntInf.int)))
            then (fn f_ => fn () => f_
                   ((array_shrink A_ a
                      (times_nata na (nat_of_integer (2 : IntInf.int))))
                   ()) ())
                   (fn aa => (fn () => (aa, na)))
            else (fn () => (a, na)))
            ()
        end)
    end);

fun set_butlast_aa_u A_ a i =
  (fn () =>
    let
      val x =
        nth_u_code (heap_prod (heap_array (typerep_heap A_)) heap_nat) a i ();
      val aa = arl_butlast A_ x ();
    in
      array_upd_u (heap_prod (heap_array (typerep_heap A_)) heap_nat) i aa a ()
    end);

fun arl_last A_ = (fn (a, n) => nth A_ a (minus_nat n one_nata));

fun last_aa_u A_ xs i =
  (fn () =>
    let
      val x =
        nth_u_code (heap_prod (heap_array (typerep_heap A_)) heap_nat) xs i ();
    in
      arl_last A_ x ()
    end);

fun delete_index_and_swap_aa_i32_u64 A_ xs i j =
  (fn () => let
              val x = last_aa_u A_ xs i ();
              val xsa = update_aa_u32_i64 A_ xs i j x ();
            in
              set_butlast_aa_u A_ xsa i ()
            end);

fun heap_array_set_u64 A_ a i x =
  (fn () => let
              val _ = heap_array_set_u64a A_ a i x ();
            in
              a
            end);

fun swap_u64_code A_ xs i j =
  (fn () => let
              val ki = nth_u64_code A_ xs i ();
              val kj = nth_u64_code A_ xs j ();
              val xsa = heap_array_set_u64 A_ xs i kj ();
              val x = heap_array_set_u64 A_ xsa j ki ();
            in
              x
            end);

fun arl_set_u A_ a i x = (fn () => let
                                     val b = array_upd_u A_ i x (fst a) ();
                                   in
                                     (b, snd a)
                                   end);

fun swap_aa_i32_u64 (A1_, A2_) xs k i j =
  (fn () =>
    let
      val xi = (fn () => Array.sub ((fn (a,b) => a) xs, Word32.toInt k)) ();
      val xj = swap_u64_code A2_ xi i j ();
      val x = arl_set_u (heap_array (typerep_heap A2_)) xs k xj ();
    in
      x
    end);

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
  (fn ai => fn bid => fn bic => fn bib => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = nth_raa_i32_u64 heap_uint32 a1a bid bia ();
      val x_b =
        swap_aa_i32_u64 (default_uint32, heap_uint32) a1a bid bib bia ();
      val x_d = delete_index_and_swap_aa_i32_u64 heap_uint32 a1d ai bic ();
      val xb = append_el_aa_u (default_uint32, heap_uint32) x_d xa bid ();
    in
      (bic, (a1, (x_b, (a1b, (a1c, (xb, a2d))))))
    end)
    x;

fun uminus_code l = Word32.xorb (l, (Word32.fromInt 1));

val sET_FALSE_code : Word32.word =
  Word32.fromLargeInt (IntInf.toLarge (3 : IntInf.int));

fun cons_trail_Propagated_tr_fast_code x =
  (fn ai => fn bia => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = arl_append (default_uint32, heap_uint32) a1 ai ();
      val xaa = heap_array_set_u heap_uint32 a1a ai sET_TRUE_code ();
      val xab =
        heap_array_set_u heap_uint32 xaa (uminus_code ai) sET_FALSE_code ();
      val xb = heap_array_set_u heap_uint32 a1b (atm_of_code ai) a1d ();
      val xc =
        heap_array_set_u (heap_option heap_uint32) a1c (atm_of_code ai)
          (SOME bia) ();
    in
      (xa, (xab, (xb, (xc, (a1d, a2d)))))
    end)
    x;

fun incr_propagation x =
  (fn (propa, (confl, dec)) => (Uint64.plus propa Uint64.one, (confl, dec))) x;

fun fast_minus A_ m n = minus A_ m n;

fun propagate_lit_wl_fast_code x =
  (fn ai => fn bib => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, a2l)))))))))))))
      =>
    fn () =>
    let
      val xa =
        swap_aa_i32_u64 (default_uint32, heap_uint32) a1a bib Uint64.zero
          (fast_minus minus_uint64 Uint64.one bia) ();
      val x_a = cons_trail_Propagated_tr_fast_code ai bib a1 ();
    in
      (x_a, (xa, (a1b, (uminus_code ai :: a1c,
                         (a1d, (a1e, (a1f, (a1g,
     (a1h, (a1i, (a1j, (incr_propagation a1k, (a1l, a2l)))))))))))))
    end)
    x;

fun polarity_st_heur_pol_fast_code x =
  (fn ai => fn bi => let
                       val (a1, _) = ai;
                     in
                       polarity_pol_fast_code a1 bi
                     end)
    x;

fun unit_propagation_inner_loop_body_wl_heur_fast_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = watched_by_app_heur_fast_code bi ai bia ();
      val xaa = access_lit_in_clauses_heur_fast_code bi xa Uint64.zero ();
    in
      let
        val x_b =
          (if ((xaa : Word32.word) = ai) then Uint64.zero else Uint64.one);
      in
        (fn f_ => fn () => f_
          ((access_lit_in_clauses_heur_fast_code bi xa
             (fast_minus minus_uint64 Uint64.one x_b))
          ()) ())
          (fn x_d =>
            (fn f_ => fn () => f_ ((polarity_st_heur_pol_fast_code bi x_d) ())
              ())
              (fn x_f =>
                (if ((x_f : Word32.word) = sET_TRUE_code)
                  then (fn () => (Uint64.plus bia Uint64.one, bi))
                  else (fn f_ => fn () => f_
                         ((find_unwatched_wl_st_heur_fast_code bi xa) ()) ())
                         (fn a =>
                           (case a
                             of NONE =>
                               (if ((x_f : Word32.word) = sET_FALSE_code)
                                 then (fn f_ => fn () => f_
((set_conflict_wl_heur_fast_code xa bi) ()) ())
(fn x_k => (fn () => (Uint64.plus bia Uint64.one, x_k)))
                                 else (fn f_ => fn () => f_
((propagate_lit_wl_fast_code x_d xa x_b bi) ()) ())
(fn x_k => (fn () => (Uint64.plus bia Uint64.one, x_k))))
                             | SOME x_j =>
                               update_clause_wl_fast_code ai xa bia x_b x_j
                                 bi)))))
      end
        ()
    end)
    x;

fun uint64_of_int i = Uint64.fromInt (integer_of_int i);

fun uint64_of_nat x = (uint64_of_int o int_of_nat) x;

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

fun length_ll_fs_heur_fast_code x =
  (fn ai => fn bi => let
                       val (_, (_, (_, (_, (a1d, _))))) = ai;
                     in
                       length_aa_u32_o64 heap_uint32 a1d bi
                     end)
    x;

fun get_conflict_wl_is_None_fast_code x =
  (fn xi => (fn () => let
                        val (_, (_, (a1b, (_, (_, _))))) = xi;
                      in
                        lookup_clause_assn_is_None a1b
                      end))
    x;

fun unit_propagation_inner_loop_wl_loop_D_fast_code x =
  (fn ai => fn bi =>
    heap_WHILET
      (fn (a1, a2) => fn () =>
        let
          val xa = length_ll_fs_heur_fast_code a2 ai ();
          val x_c = get_conflict_wl_is_None_fast_code a2 ();
        in
          Uint64.less a1 xa andalso x_c
        end)
      (fn (a, b) => unit_propagation_inner_loop_body_wl_heur_fast_code ai a b)
      (Uint64.zero, bi))
    x;

fun unit_propagation_inner_loop_wl_D_fast_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = unit_propagation_inner_loop_wl_loop_D_fast_code ai bi ();
    in
      snd xa
    end)
    x;

fun op_list_is_empty x = null x;

fun literals_to_update_wl_empty_heur_fast_code x =
  (fn xi => (fn () => let
                        val (_, (_, (_, (a1c, (_, _))))) = xi;
                      in
                        op_list_is_empty a1c
                      end))
    x;

fun unit_propagation_outer_loop_wl_D_fast x =
  heap_WHILET
    (fn s => fn () =>
      let
        val xa = literals_to_update_wl_empty_heur_fast_code s ();
      in
        not xa
      end)
    (fn s => fn () =>
      let
        val a = select_and_remove_from_literals_to_update_wl_fast_code s ();
      in
        let
          val (a1, a2) = a;
        in
          unit_propagation_inner_loop_wl_D_fast_code a2 a1
        end
          ()
      end)
    x;

fun get_count_max_lvls_code x =
  (fn (_, (_, (_, (_, (_, (_, (_, (clvls, _)))))))) => clvls) x;

fun maximum_level_removed_eq_count_dec_fast_code x =
  (fn _ => fn bi =>
    (fn () => (Word32.< ((Word32.fromInt 1), get_count_max_lvls_code bi))))
    x;

fun last_trail_fast_code x =
  (fn (a1, (_, (_, (a1c, _)))) => fn () =>
    let
      val xa = arl_last heap_uint32 a1 ();
      val xaa = arl_last heap_uint32 a1 ();
      val x_a = nth_u_code (heap_option heap_uint32) a1c (atm_of_code xaa) ();
    in
      (xa, x_a)
    end)
    x;

fun lit_and_ann_of_propagated_st_heur_fast_code x =
  (fn (a1, _) => fn () => let
                            val xa = last_trail_fast_code a1 ();
                            val xaa = last_trail_fast_code a1 ();
                          in
                            (fst xa, the (snd xaa))
                          end)
    x;

fun is_in_option_lookup_conflict_code x =
  (fn ai => fn (_, (_, a2a)) => fn () =>
    let
      val xa = nth_u_code heap_bool a2a (atm_of_code ai) ();
    in
      not (not xa)
    end)
    x;

fun atm_is_in_option_lookup_conflict_fast_code x =
  (fn ai => fn (_, (_, (a1b, _))) => is_in_option_lookup_conflict_code ai a1b)
    x;

fun is_decided_wl_fast_code x = (fn xi => (fn () => (is_None (snd xi)))) x;

fun is_decided_hd_trail_wl_fast_code x =
  (fn (a1, _) => fn () => let
                            val xa = last_trail_fast_code a1 ();
                          in
                            is_decided_wl_fast_code xa ()
                          end)
    x;

fun resolve_lookup_conflict_merge_fast_code x =
  (fn ai => fn bie => fn bid => fn bic => fn bib => fn bia => fn bi =>
    let
      val (_, a2) = bic;
    in
      (fn () =>
        let
          val a =
            heap_WHILET
              (fn (a1a, (_, (_, (_, _)))) =>
                (fn f_ => fn () => f_ ((length_raa_i32_u heap_uint32 bie bid)
                  ()) ())
                  (fn x_a => (fn () => (Word32.< (a1a, x_a)))))
              (fn (a1a, (a1b, (a1c, (a1d, a2d)))) =>
                (fn f_ => fn () => f_ ((nth_raa_i32_u32 heap_uint32 bie bid a1a)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((get_level_fast_code ai xa) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((lbd_write_code a1d xb true) ())
                          ())
                          (fn x_a =>
                            (fn f_ => fn () => f_
                              ((nth_raa_i32_u32 heap_uint32 bie bid a1a) ()) ())
                              (fn xc =>
                                (fn f_ => fn () => f_
                                  ((get_level_fast_code ai xc) ()) ())
                                  (fn xd =>
                                    (fn f_ => fn () => f_
                                      ((nth_raa_i32_u32 heap_uint32 bie bid a1a)
                                      ()) ())
                                      (fn xaa =>
(fn f_ => fn () => f_ ((is_in_conflict_code a1c xaa) ()) ())
  (fn xab =>
    (fn f_ => fn () => f_
      ((if Word32.< (xd, count_decided_pol ai) andalso not xab
         then (fn f_ => fn () => f_ ((nth_raa_i32_u32 heap_uint32 bie bid a1a)
                ()) ())
                (arl_append (default_uint32, heap_uint32) a2d)
         else (fn () => a2d))
      ()) ())
      (fn x_c =>
        (fn f_ => fn () => f_ ((nth_raa_i32_u32 heap_uint32 bie bid a1a) ()) ())
          (fn xe =>
            (fn f_ => fn () => f_ ((get_level_fast_code ai xe) ()) ())
              (fn xf =>
                (fn f_ => fn () => f_ ((nth_raa_i32_u32 heap_uint32 bie bid a1a)
                  ()) ())
                  (fn xac =>
                    (fn f_ => fn () => f_ ((is_in_conflict_code a1c xac) ()) ())
                      (fn xad =>
                        (fn f_ => fn () => f_
                          (let
                             val (a1e, a2e) = a1c;
                           in
                             (fn f_ => fn () => f_
                               ((nth_raa_i32_u32 heap_uint32 bie bid a1a) ())
                               ())
                               (fn xg =>
                                 (fn f_ => fn () => f_
                                   ((nth_u_code heap_bool a2e (atm_of_code xg))
                                   ()) ())
                                   (fn xh =>
                                     (fn f_ => fn () => f_
                                       ((nth_raa_i32_u32 heap_uint32 bie bid
  a1a)
                                       ()) ())
                                       (fn xae =>
 (fn f_ => fn () => f_ ((nth_raa_i32_u32 heap_uint32 bie bid a1a) ()) ())
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
                              (Word32.+ (a1a, (Word32.fromInt 1)),
                                ((if ((xf : Word32.word) = (count_decided_pol
                     ai)) andalso
                                       not xad
                                   then Word32.+ (a1b, (Word32.fromInt 1))
                                   else a1b),
                                  (x_g, (x_a, x_c)))))))))))))))))))
              ((Word32.fromInt 1), (bib, (a2, (bia, bi)))) ();
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
                      ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat) a1a
                         (the a2d))
                      ()) ())
                      (fn xa =>
                        (fn f_ => fn () => f_
                          ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat) a1a
                             ai)
                          ()) ())
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

fun is_pos_code l =
  (((Word32.andb (l, (Word32.fromInt 1))) : Word32.word) = (Word32.fromInt 0));

fun fast_minus_uint32 x = fast_minus minus_uint32 x;

fun conflict_remove1_code x =
  (fn ai => fn (a1, a2) => fn () =>
    let
      val x_a = heap_array_set_u heap_bool a2 (atm_of_code ai) false ();
    in
      (fast_minus_uint32 a1 (Word32.fromInt 1), x_a)
    end)
    x;

fun tl_trail_tr_fast_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = arl_last heap_uint32 a1 ();
      val x_a = arl_butlast heap_uint32 a1 ();
      val xaa = heap_array_set_u heap_uint32 a1a xa uNSET_code ();
      val xab = heap_array_set_u heap_uint32 xaa (uminus_code xa) uNSET_code ();
      val xb =
        heap_array_set_u heap_uint32 a1b (atm_of_code xa) (Word32.fromInt 0) ();
      val xc = nth_u_code (heap_option heap_uint32) a1c (atm_of_code xa) ();
      val xd = nth_u_code (heap_option heap_uint32) a1c (atm_of_code xa) ();
      val xe =
        (if is_None xd then arl_butlast heap_uint32 a2d else (fn () => a2d)) ();
    in
      (x_a, (xab, (xb, (a1c, ((if is_None xc
                                then fast_minus_uint32 a1d (Word32.fromInt 1)
                                else a1d),
                               xe)))))
    end)
    x;

fun update_confl_tl_wl_fast_code x =
  (fn ai => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, a2j)))))))))))
      =>
    fn () =>
    let
      val a =
        resolve_lookup_conflict_merge_fast_code a1 a1a ai a1b a1g a1i a1j ();
    in
      let
        val (a1k, (a1l, (a1m, a2m))) = a;
      in
        (fn f_ => fn () => f_
          ((conflict_remove1_code (uminus_code bia) (snd a1k)) ()) ())
          (fn x_c =>
            (fn f_ => fn () => f_ ((tl_trail_tr_fast_code a1) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((vmtf_mark_to_rescore_and_unset_code (atm_of_code bia) a1e)
                  ()) ())
                  (fn xaa =>
                    (fn f_ => fn () => f_
                      ((heap_array_set_u heap_bool a1f (atm_of_code bia)
                         (is_pos_code bia))
                      ()) ())
                      (fn xb =>
                        (fn () =>
                          (false,
                            (xa, (a1a, ((false, x_c),
 (a1c, (a1d, (xaa, (xb, (fast_minus_uint32 a1l (Word32.fromInt 1),
                          (a1h, (a1m, (a2m, a2j)))))))))))))))))
      end
        ()
    end)
    x;

fun tl_state_wl_heur_fast_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) => fn () =>
    let
      val xa = last_trail_fast_code a1 ();
    in
      let
        val xb = fst xa;
      in
        (fn f_ => fn () => f_ ((tl_trail_tr_fast_code a1) ()) ())
          (fn x_a =>
            (fn f_ => fn () => f_
              (let
                 val ((a1h, (a1i, (a1j, (a1k, a2k)))), a2g) = a1e;
               in
                 (fn f_ => fn () => f_
                   ((if is_None a2k then (fn () => true)
                      else (fn f_ => fn () => f_
                             ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat)
                                a1h (the a2k))
                             ()) ())
                             (fn xaa =>
                               (fn f_ => fn () => f_
                                 ((nth_u_code
                                    (heap_vmtf_node heap_uint32 heap_nat) a1h
                                    (atm_of_code xb))
                                 ()) ())
                                 (fn xc =>
                                   (fn () =>
                                     (less_nat (stamp xaa) (stamp xc))))))
                   ()) ())
                   (fn x_b =>
                     (fn () =>
                       (if x_b
                         then ((a1h, (a1i, (a1j,
     (a1k, SOME (atm_of_code xb))))),
                                a2g)
                         else ((a1h, (a1i, (a1j, (a1k, a2k)))), a2g))))
               end
              ()) ())
              (fn xc =>
                (fn () => (x_a, (a1a, (a1b, (a1c, (a1d, (xc, (a1f, a2f))))))))))
      end
        ()
    end)
    x;

fun skip_and_resolve_loop_wl_D_fast_code x =
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
                  ((atm_is_in_option_lookup_conflict_fast_code (uminus_code a1a)
                     a2)
                  ()) ())
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

fun nth_raa_i32 A_ xs i j =
  (fn () =>
    let
      val x = (fn () => Array.sub ((fn (a,b) => a) xs, Word32.toInt i)) ();
      val xa = nth A_ x j ();
    in
      xa
    end);

fun mark_failed_lits_stack_fast_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, _) =>
            (fn f_ => fn () => f_
              ((arl_length (heap_prod heap_uint32 heap_nat) bia) ()) ())
              (fn x_a => (fn () => (less_nat a1 x_a))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((arl_get (heap_prod heap_uint32 heap_nat) bia a1) ()) ())
              (fn (a1a, a2a) =>
                (fn f_ => fn () => f_
                  ((nth_raa_i32 heap_uint32 ai a1a (minus_nat a2a one_nata)) ())
                  ())
                  (fn xa =>
                    (fn f_ => fn () => f_
                      ((conflict_min_cach_set_failed_l_code a2 (atm_of_code xa))
                      ()) ())
                      (fn x_d => (fn () => (plus_nat a1 one_nata, x_d))))))
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
      nth_u_code (heap_option heap_uint32) a1c (atm_of_code bi)
    end)
    x;

fun atm_in_conflict_code x =
  (fn ai => fn (_, a2) => fn () => let
                                     val xa = nth_u_code heap_bool a2 ai ();
                                   in
                                     not (not xa)
                                   end)
    x;

fun length_raa_u32 A_ xs i =
  (fn () =>
    let
      val x = (fn () => Array.sub ((fn (a,b) => a) xs, Word32.toInt i)) ();
    in
      len A_ x ()
    end);

fun arl_set A_ =
  (fn (a, n) => fn i => fn x => fn () => let
   val aa = upd A_ i x a ();
 in
   (aa, n)
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
          val x_a = arl_is_empty (heap_prod heap_uint32 heap_nat) a1a ();
        in
          not x_a
        end)
      (fn (a1, (a1a, _)) => fn () =>
        let
          val xa = arl_last (heap_prod heap_uint32 heap_nat) a1a ();
          val xaa = arl_last (heap_prod heap_uint32 heap_nat) a1a ();
          val xab = length_raa_u32 heap_uint32 bid (fst xaa) ();
        in
          (if less_eq_nat xab (snd xa)
            then (fn f_ => fn () => f_
                   ((arl_last (heap_prod heap_uint32 heap_nat) a1a) ()) ())
                   (fn xb =>
                     (fn f_ => fn () => f_
                       ((nth_raa_i32_u32 heap_uint32 bid (fst xb)
                          (Word32.fromInt 0))
                       ()) ())
                       (fn xc =>
                         (fn f_ => fn () => f_
                           ((conflict_min_cach_set_removable_l_code a1
                              (atm_of_code xc))
                           ()) ())
                           (fn x_d =>
                             (fn f_ => fn () => f_
                               ((arl_butlast (heap_prod heap_uint32 heap_nat)
                                  a1a)
                               ()) ())
                               (fn xd => (fn () => (x_d, (xd, true)))))))
            else (fn f_ => fn () => f_
                   ((arl_last (heap_prod heap_uint32 heap_nat) a1a) ()) ())
                   (fn xb =>
                     (fn f_ => fn () => f_
                       (let
                          val (a1b, a2b) = xb;
                        in
                          (fn f_ => fn () => f_
                            ((arl_last (heap_prod heap_uint32 heap_nat) a1a) ())
                            ())
                            (fn xc =>
                              (fn f_ => fn () => f_
                                ((nth_raa_i32 heap_uint32 bid (fst xc) a2b) ())
                                ())
                                (fn x_e =>
                                  (fn f_ => fn () => f_
                                    ((arl_length
                                       (heap_prod heap_uint32 heap_nat) a1a)
                                    ()) ())
                                    (fn xd =>
                                      (fn f_ => fn () => f_
((arl_set (heap_prod heap_uint32 heap_nat) a1a (minus_nat xd one_nata)
   (a1b, plus_nat a2b one_nata))
()) ())
(fn x_f => (fn () => (x_e, x_f))))))
                        end
                       ()) ())
                       (fn (a1b, a2b) =>
                         (fn f_ => fn () => f_ ((get_level_fast_code ai a1b) ())
                           ())
                           (fn xc =>
                             (fn f_ => fn () => f_ ((level_in_lbd_code xc bi)
                               ()) ())
                               (fn xd =>
                                 (fn f_ => fn () => f_
                                   ((get_level_fast_code ai a1b) ()) ())
                                   (fn xac =>
                                     (fn f_ => fn () => f_
                                       ((conflict_min_cach_l_code a1
  (atm_of_code a1b))
                                       ()) ())
                                       (fn xba =>
 (fn f_ => fn () => f_ ((atm_in_conflict_code (atm_of_code a1b) bic) ()) ())
   (fn xca =>
     (if ((xac : Word32.word) = (Word32.fromInt 0)) orelse
           (equal_minimize_status xba SEEN_REMOVABLE orelse xca)
       then (fn () => (a1, (a2b, false)))
       else (fn f_ => fn () => f_
              ((conflict_min_cach_l_code a1 (atm_of_code a1b)) ()) ())
              (fn xad =>
                (if not xd orelse equal_minimize_status xad SEEN_FAILED
                  then (fn f_ => fn () => f_
                         ((mark_failed_lits_stack_fast_code bid a2b a1) ()) ())
                         (fn x_j =>
                           (fn f_ => fn () => f_
                             ((arl_empty
                                (default_prod default_uint32 default_nat,
                                  heap_prod heap_uint32 heap_nat)
                                zero_nat)
                             ()) ())
                             (fn xe => (fn () => (x_j, (xe, false)))))
                  else (fn f_ => fn () => f_
                         ((get_propagation_reason_fast_code ai
                            (uminus_code a1b))
                         ()) ())
                         (fn a =>
                           (case a
                             of NONE =>
                               (fn f_ => fn () => f_
                                 ((mark_failed_lits_stack_fast_code bid a2b a1)
                                 ()) ())
                                 (fn x_k =>
                                   (fn f_ => fn () => f_
                                     ((arl_empty
(default_prod default_uint32 default_nat, heap_prod heap_uint32 heap_nat)
zero_nat)
                                     ()) ())
                                     (fn xe => (fn () => (x_k, (xe, false)))))
                             | SOME x_k =>
                               (fn f_ => fn () => f_
                                 ((arl_append
                                    (default_prod default_uint32 default_nat,
                                      heap_prod heap_uint32 heap_nat)
                                    a2b (x_k, one_nata))
                                 ()) ())
                                 (fn xe =>
                                   (fn () => (a1, (xe, false)))))))))))))))))
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
                  (default_prod default_uint32 default_nat,
                    heap_prod heap_uint32 heap_nat)
                  zero_nat)
               ()) ())
               (fn xb => (fn () => (bib, (xb, true))))
        else (fn f_ => fn () => f_
               ((conflict_min_cach_l_code bib (atm_of_code bia)) ()) ())
               (fn xb =>
                 (if equal_minimize_status xb SEEN_FAILED
                   then (fn f_ => fn () => f_
                          ((arl_empty
                             (default_prod default_uint32 default_nat,
                               heap_prod heap_uint32 heap_nat)
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
                                     (default_prod default_uint32 default_nat,
                                       heap_prod heap_uint32 heap_nat)
                                     zero_nat)
                                  ()) ())
                                  (fn xc => (fn () => (bib, (xc, false))))
                              | SOME x_c =>
                                (fn f_ => fn () => f_
                                  ((arl_empty
                                     (default_prod default_uint32 default_nat,
                                       heap_prod heap_uint32 heap_nat)
                                     zero_nat)
                                  ()) ())
                                  (fn xc =>
                                    (fn f_ => fn () => f_
                                      ((arl_append
 (default_prod default_uint32 default_nat, heap_prod heap_uint32 heap_nat) xc
 (x_c, one_nata))
                                      ()) ())
                                      (fn x_d =>
lit_redundant_rec_wl_lookup_fast_code ai bid bic bib x_d bi)))))))
        ()
    end)
    x;

fun delete_from_lookup_conflict_code x =
  (fn ai => fn (a1, a2) => fn () =>
    let
      val x_a = heap_array_set_u heap_bool a2 (atm_of_code ai) false ();
    in
      (fast_minus_uint32 a1 (Word32.fromInt 1), x_a)
    end)
    x;

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
              (((fn () => Array.sub ((fn (a,b) => a) a2b, Word32.toInt a1a)))
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
                      else (fn f_ => fn () => f_
                             ((delete_from_lookup_conflict_code x_a a1) ()) ())
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
              (((fn () => Array.sub ((fn (a,b) => a) bi, Word32.toInt a2a))) ())
              ())
              (fn xc =>
                (fn f_ => fn () => f_ ((delete_from_lookup_conflict_code xc a1)
                  ()) ())
                  (fn x_c =>
                    (fn f_ => fn () => f_
                      (((fn () => Array.sub ((fn (a,b) => a) bi,
                         Word32.toInt a2a)))
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
              ((if equal_nat xc one_nata then (fn () => (Word32.fromInt 0))
                 else (fn f_ => fn () => f_ ((nth heap_uint32 a1a one_nata) ())
                        ())
                        (get_level_fast_code ai))
              ()) ())
              (fn xd => (fn () => (let
                                     val (n, xs) = a1;
                                   in
                                     (true, (n, xs))
                                   end,
                                    (a1a, xd)))))
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
                  (fn x_d => (fn () => (plus_nat a1a one_nata, x_d)))))
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

fun extract_shorter_conflict_list_heur_st_fast_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, a2j)))))))))))
     =>
    fn () =>
    let
      val xa = last_trail_fast_code a1 ();
    in
      let
        val xb = fst xa;
      in
        (fn f_ => fn () => f_
          ((delete_from_lookup_conflict_code (uminus_code xb) (snd a1b)) ()) ())
          (fn x_b =>
            (fn f_ => fn () => f_
              ((arl_set heap_uint32 a1j zero_nata (uminus_code xb)) ()) ())
              (fn x_d =>
                (fn f_ => fn () => f_
                  ((minimize_and_extract_highest_lookup_conflict_fast_code a1
                     a1a x_b a1h a1i x_d)
                  ()) ())
                  (fn (a1k, (a1l, a2l)) =>
                    (fn f_ => fn () => f_ ((empty_cach_code a1l) ()) ())
                      (fn x_g =>
                        (fn f_ => fn () => f_
                          ((empty_conflict_and_extract_clause_heur_fast_code a1
                             a1k a2l)
                          ()) ())
                          (fn (a1m, (a1n, a2n)) =>
                            (fn () =>
                              ((a1, (a1a, (a1m,
    (a1c, (a1d, (a1e, (a1f, (a1g, (x_g, (a1i,
  (let
     val (a, _) = a2l;
   in
     (a, one_nata)
   end,
    a2j))))))))))),
                                (a2n, a1n))))))))
      end
        ()
    end)
    x;

fun lit_of_last_trail_fast_code x = (fn (a1, _) => arl_last heap_uint32 a1) x;

fun lit_of_hd_trail_st_heur_fast_code x =
  (fn (a1, (_, (_, (_, (_, (_, _)))))) => lit_of_last_trail_fast_code a1) x;

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
            (xa, (plus_nat a1a one_nata, (ai, (ai, SOME ai))))
          end)
      | SOME xa =>
        (fn () =>
          let
            val xaa = nth_u_code (heap_vmtf_node heap_uint32 heap_nat) a1 xa ();
            val xb = nth_u_code (heap_vmtf_node heap_uint32 heap_nat) a1 xa ();
            val xc =
              heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) a1 ai
                (VMTF_Node (plus_nat a1a one_nata, NONE, SOME xa)) ();
            val x_b =
              heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) xc xa
                (VMTF_Node (stamp xaa, SOME ai, get_next xb)) ();
          in
            (x_b, (plus_nat a1a one_nata, (ai, (the a1c, SOME ai))))
          end)))
    x;

fun get_prev (VMTF_Node (x1, x2, x3)) = x2;

fun ns_vmtf_dequeue_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = nth_u_code (heap_vmtf_node heap_uint32 heap_nat) bi ai ();
      val x_a =
        (case get_prev xa of NONE => (fn () => bi)
          | SOME x_b =>
            (fn f_ => fn () => f_
              ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat) bi x_b) ()) ())
              (fn xaa =>
                (fn f_ => fn () => f_
                  ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat) bi x_b) ())
                  ())
                  (fn xb =>
                    heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) bi
                      x_b (VMTF_Node (stamp xaa, get_prev xb, get_next xa)))))
          ();
      val x_b =
        (case get_next xa of NONE => (fn () => x_a)
          | SOME x_c =>
            (fn f_ => fn () => f_
              ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat) x_a x_c) ())
              ())
              (fn xaa =>
                (fn f_ => fn () => f_
                  ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat) x_a x_c)
                  ()) ())
                  (fn xb =>
                    heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) x_a
                      x_c (VMTF_Node (stamp xaa, get_prev xa, get_next xb)))))
          ();
      val xb = nth_u_code (heap_vmtf_node heap_uint32 heap_nat) x_b ai ();
    in
      heap_array_set_u (heap_vmtf_node heap_uint32 heap_nat) x_b ai
        (VMTF_Node (stamp xb, NONE, NONE)) ()
    end)
    x;

fun imp_option_eq eq a b =
  (case (a, b) of (NONE, NONE) => (fn () => true)
    | (NONE, SOME _) => (fn () => false) | (SOME _, NONE) => (fn () => false)
    | (SOME aa, SOME ba) => eq aa ba);

fun vmtf_dequeue_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, a2c)))) => fn () =>
    let
      val xa =
        (if ((a1b : Word32.word) = ai)
          then (fn f_ => fn () => f_
                 ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat) a1 ai) ())
                 ())
                 (fn x_a => (fn () => (get_next x_a)))
          else (fn () => (SOME a1b)))
          ();
      val xaa =
        imp_option_eq (fn va => fn vb => (fn () => ((va : Word32.word) = vb)))
          a2c (SOME ai) ();
      val x_a =
        (if xaa
          then (fn f_ => fn () => f_
                 ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat) a1 ai) ())
                 ())
                 (fn x_b => (fn () => (get_next x_b)))
          else (fn () => a2c))
          ();
      val x_b =
        (if ((a1c : Word32.word) = ai)
          then (fn f_ => fn () => f_
                 ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat) a1 ai) ())
                 ())
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

fun fast_minus_nat x = (fn a => (Nat(integer_of_nat x - integer_of_nat a)));

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
            (if less_nat zero_nata a1
              then (fn f_ => fn () => f_ ((arl_get heap_uint32 a2 a1) ()) ())
                     (fn xa =>
                       (fn f_ => fn () => f_
                         ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat) ai
                            xa)
                         ()) ())
                         (fn xb =>
                           (fn f_ => fn () => f_
                             ((arl_get heap_uint32 a2
                                (fast_minus_nat a1 one_nata))
                             ()) ())
                             (fn xaa =>
                               (fn f_ => fn () => f_
                                 ((nth_u_code
                                    (heap_vmtf_node heap_uint32 heap_nat) ai
                                    xaa)
                                 ()) ())
                                 (fn xab =>
                                   (fn () =>
                                     (less_nat (stamp xb) (stamp xab)))))))
              else (fn () => false)))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((arl_swap heap_uint32 a2 a1 (fast_minus_nat a1 one_nata)) ()) ())
              (fn x_a => (fn () => (fast_minus_nat a1 one_nata, x_a))))
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
                  (fn x_a => (fn () => (plus_nat a1a one_nata, x_a))))
              (one_nata, bi) ();
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
                  (fn x_c => (fn () => (plus_nat a1a one_nata, x_c)))))
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

fun vmtf_flush_all_fast_code x = (fn _ => vmtf_flush_code) x;

fun shiftr_uint64 x n =
  (if less_nat n (nat_of_integer (64 : IntInf.int))
    then Uint64.shiftr x (integer_of_nat n) else Uint64.zero);

fun shiftl_uint32 x n =
  (if less_nat n (nat_of_integer (32 : IntInf.int))
    then Uint32.shiftl x (integer_of_nat n) else (Word32.fromInt 0));

fun uint64_of_uint32 x = (Uint64.fromLarge (Word32.toLarge x));

fun ema_update_ref coeff ema lbd =
  Uint64.plus (shiftr_uint64 ema coeff)
    (uint64_of_uint32
      (shiftl_uint32 lbd (minus_nat (nat_of_integer (32 : IntInf.int)) coeff)));

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
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, a2m))))))))))))))
      =>
    fn () =>
    let
      val xa = vmtf_flush_all_fast_code a1 a1e ();
      val x_a = get_LBD_code a1i ();
      val x_b = lbd_empty_code a1i ();
      val x_c =
        cons_trail_Propagated_tr_fast_code (uminus_code ai) (Word32.fromInt 0)
          a1 ();
    in
      (x_c, (a1a, (a1b, ([ai],
                          (a1d, (xa, (a1f, (a1g,
     (a1h, (x_b, (a1j, (a1k, (ema_update_ref (nat_of_integer (5 : IntInf.int))
                                a1l x_a,
                               (ema_update_ref
                                  (nat_of_integer (14 : IntInf.int)) a1m x_a,
                                 Word32.+ (a2m, (Word32.fromInt 1))))))))))))))))
    end)
    x;

fun vmtf_unset_code x =
  (fn ai => fn ((a1a, (a1b, (a1c, (a1d, a2d)))), a2) => fn () =>
    let
      val xa =
        (if is_None a2d then (fn () => true)
          else (fn f_ => fn () => f_
                 ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat) a1a
                    (the a2d))
                 ()) ())
                 (fn xa =>
                   (fn f_ => fn () => f_
                     ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat) a1a ai)
                     ()) ())
                     (fn xaa => (fn () => (less_nat (stamp xa) (stamp xaa))))))
          ();
    in
      (if xa then ((a1a, (a1b, (a1c, (a1d, SOME ai)))), a2)
        else ((a1a, (a1b, (a1c, (a1d, a2d)))), a2))
    end)
    x;

fun find_decomp_wl_imp_fast_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET (fn (a1, (_, _)) => (fn () => (Word32.< (bia, a1))))
          (fn (a1, (a1a, a2a)) =>
            (fn f_ => fn () => f_ ((last_trail_fast_code a1a) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_ ((is_decided_wl_fast_code xa) ()) ())
                  (fn x_c =>
                    (if x_c
                      then (fn f_ => fn () => f_ ((last_trail_fast_code a1a) ())
                             ())
                             (fn xb =>
                               (fn f_ => fn () => f_
                                 ((tl_trail_tr_fast_code a1a) ()) ())
                                 (fn xaa =>
                                   (fn f_ => fn () => f_
                                     ((vmtf_unset_code (atm_of_code (fst xb))
a2a)
                                     ()) ())
                                     (fn xc =>
                                       (fn () =>
 (fast_minus_uint32 a1 (Word32.fromInt 1), (xaa, xc))))))
                      else (fn f_ => fn () => f_ ((last_trail_fast_code a1a) ())
                             ())
                             (fn xb =>
                               (fn f_ => fn () => f_
                                 ((tl_trail_tr_fast_code a1a) ()) ())
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

fun length_ra A_ xs = arl_length (heap_array (typerep_heap A_)) xs;

fun append_and_length_u32_code x =
  (fn _ => fn bia => fn bi => fn () =>
    let
      val xa = length_ra heap_uint32 bi ();
      val x_b = arrayO_raa_append (default_uint32, heap_uint32) bi bia ();
    in
      (x_b, uint32_of_nat xa)
    end)
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
                            (fn () => (plus_nat a1 one_nata, (x_a, x_c))))))))
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
  (_, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, a2m))))))))))))))
      =>
    fn () =>
    let
      val xa = nth heap_uint32 bia one_nata ();
      val a = vmtf_rescore_fast_code bia a1 a1e a1f ();
    in
      let
        val (a1n, a2n) = a;
      in
        (fn f_ => fn () => f_ ((vmtf_flush_all_fast_code a1 a1n) ()) ())
          (fn x_c =>
            (fn f_ => fn () => f_ ((get_LBD_code a1i) ()) ())
              (fn x_d =>
                (fn f_ => fn () => f_
                  ((append_and_length_u32_code false bia a1a) ()) ())
                  (fn (a1o, a2o) =>
                    (fn f_ => fn () => f_
                      ((append_el_aa_u (default_uint32, heap_uint32) a1d
                         (uminus_code ai) a2o)
                      ()) ())
                      (fn x_h =>
                        (fn f_ => fn () => f_
                          ((append_el_aa_u (default_uint32, heap_uint32) x_h xa
                             a2o)
                          ()) ())
                          (fn x_j =>
                            (fn f_ => fn () => f_ ((lbd_empty_code a1i) ()) ())
                              (fn x_l =>
                                (fn f_ => fn () => f_
                                  ((cons_trail_Propagated_tr_fast_code
                                     (uminus_code ai) a2o a1)
                                  ()) ())
                                  (fn x_m =>
                                    (fn () =>
                                      (x_m,
(a1o, (a1b, ([ai],
              (x_j, (x_c, (a2n, ((Word32.fromInt 0),
                                  (a1h, (x_l,
  (a1j, (a1k, (ema_update_ref (nat_of_integer (5 : IntInf.int)) a1l x_d,
                (ema_update_ref (nat_of_integer (14 : IntInf.int)) a1m x_d,
                  Word32.+ (a2m, (Word32.fromInt 1))))))))))))))))))))))))
      end
        ()
    end)
    x;

fun backtrack_wl_D_nlit_heur_fast_code x =
  (fn xi => fn () =>
    let
      val xa = lit_of_hd_trail_st_heur_fast_code xi ();
      val a = extract_shorter_conflict_list_heur_st_fast_code xi ();
    in
      let
        val (a1, (a1a, a2a)) = a;
      in
        (fn f_ => fn () => f_ ((find_decomp_wl_imp_fast_codea a1a a1) ()) ())
          (fn x_c =>
            (fn f_ => fn () => f_ ((len heap_uint32 a2a) ()) ())
              (fn xaa =>
                (if less_nat one_nata xaa
                  then propagate_bt_wl_D_fast_code xa a2a x_c
                  else propagate_unit_bt_wl_D_fast_code xa x_c)))
      end
        ()
    end)
    x;

fun defined_atm_fast_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, _))) = ai;
    in
      (fn () =>
        let
          val xa =
            nth_u_code heap_uint32 a1a (Word32.* ((Word32.fromInt 2), bi)) ();
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
              nth_u_code (heap_vmtf_node heap_uint32 heap_nat) a1a (the s) ();
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
            (if x_a then SOME (Word32.* ((Word32.fromInt 2), xa))
              else SOME (Word32.+ (Word32.* ((Word32.fromInt 2), xa), (Word32.fromInt 1))))
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
      val xc =
        heap_array_set_u (heap_option heap_uint32) a1c (atm_of_code ai) NONE ();
      val xd =
        arl_append (default_uint32, heap_uint32) a2d (uint32_of_nat xa) ();
    in
      (x_a, (xab, (xb, (xc, (Word32.+ (a1d, (Word32.fromInt 1)), xd)))))
    end)
    x;

fun incr_decision x =
  (fn (propa, (confl, dec)) => (propa, (confl, Uint64.plus dec Uint64.one))) x;

fun decide_lit_wl_fast_code x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (_, (a1d, (a1e, (a1f,
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, a2l)))))))))))))
      =>
    fn () =>
    let
      val xa = cons_trail_Decided_tr_fast_code ai a1 ();
    in
      (xa, (a1a, (a1b, ([uminus_code ai],
                         (a1d, (a1e, (a1f, (a1g,
     (a1h, (a1i, (a1j, (incr_decision a1k, (a1l, a2l)))))))))))))
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
            (fn x_c => (fn () => (false, x_c))))
        ()
    end)
    x;

fun count_decided_st_fast_code x =
  (fn xi => (fn () => let
                        val (a1, _) = xi;
                      in
                        count_decided_pol a1
                      end))
    x;

fun cdcl_twl_o_prog_wl_D_fast_code x =
  (fn xi => fn () =>
    let
      val xa = get_conflict_wl_is_None_fast_code xi ();
    in
      (if xa then decide_wl_or_skip_D_fast_code xi
        else (fn f_ => fn () => f_ ((count_decided_st_fast_code xi) ()) ())
               (fn xb =>
                 (if Word32.< ((Word32.fromInt 0), xb)
                   then (fn f_ => fn () => f_
                          ((skip_and_resolve_loop_wl_D_fast_code xi) ()) ())
                          (fn x_b =>
                            (fn f_ => fn () => f_
                              ((backtrack_wl_D_nlit_heur_fast_code x_b) ()) ())
                              (fn x_c => (fn () => (false, x_c))))
                   else (fn () => (true, xi)))))
        ()
    end)
    x;

fun select_and_remove_from_literals_to_update_wl_code x =
  (fn xi =>
    (fn () =>
      let
        val (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) = xi;
      in
        ((a1, (a1a, (a1b, (op_list_tl a1c, (a1d, a2d))))), op_list_hd a1c)
      end))
    x;

fun nth_raa_i_u64 A_ =
  (fn a => fn b => fn c =>
    (fn () => Array.sub (Array.sub ((fn (a,b) => a) a,
      IntInf.toInt (integer_of_nat b)), Uint64.toFixedInt c)));

fun access_lit_in_clauses_heur_code x =
  (fn ai => fn bia => fn bi => let
                                 val (_, (a1a, _)) = ai;
                               in
                                 nth_raa_i_u64 heap_uint32 a1a bia bi
                               end)
    x;

fun polarity_pol_code x = (fn ai => fn bi => let
       val (_, (a1a, (_, _))) = ai;
     in
       nth_u_code heap_uint32 a1a bi
     end)
                            x;

fun length_raa_u64 A_ xs i =
  (fn () => let
              val x = arl_get (heap_array (typerep_heap A_)) xs i ();
            in
              length_u64_code A_ x ()
            end);

fun find_unwatched_wl_st_heur_code x =
  (fn ai => fn bi =>
    let
      val (a1, (a1a, (_, (_, (_, (_, _)))))) = ai;
    in
      (fn () =>
        let
          val xa =
            heap_WHILET
              (fn (a1f, a2f) =>
                (fn f_ => fn () => f_ ((length_raa_u64 heap_uint32 a1a bi) ())
                  ())
                  (fn xa =>
                    (fn () => (is_None a1f andalso Uint64.less a2f xa))))
              (fn (_, a2f) =>
                (fn f_ => fn () => f_ ((nth_raa_i_u64 heap_uint32 a1a bi a2f)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((polarity_pol_code a1 xa) ()) ())
                      (fn x_a =>
                        (fn () =>
                          (if ((x_a : Word32.word) = uNSET_code)
                            then (SOME a2f, a2f)
                            else (if ((x_a : Word32.word) = sET_TRUE_code)
                                   then (SOME a2f, a2f)
                                   else (NONE, Uint64.plus a2f Uint64.one)))))))
              (NONE, Uint64.fromInt (2 : IntInf.int)) ();
        in
          fst xa
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

fun length_raa_u A_ xs i =
  (fn () => let
              val x = arl_get (heap_array (typerep_heap A_)) xs i ();
            in
              length_u_code A_ x ()
            end);

fun nth_raa A_ xs i j =
  (fn () => let
              val x = arl_get (heap_array (typerep_heap A_)) xs i ();
              val xa = nth A_ x j ();
            in
              xa
            end);

fun nth_raa_u A_ xs x l = nth_raa A_ xs x (nat_of_uint32 l);

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
                (fn f_ => fn () => f_ ((length_raa_u heap_uint32 bie bid) ())
                  ())
                  (fn x_a => (fn () => (Word32.< (a1a, x_a)))))
              (fn (a1a, (a1b, (a1c, (a1d, a2d)))) =>
                (fn f_ => fn () => f_ ((nth_raa_u heap_uint32 bie bid a1a) ())
                  ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((get_level_code ai xa) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((lbd_write_code a1d xb true) ())
                          ())
                          (fn x_a =>
                            (fn f_ => fn () => f_
                              ((nth_raa_u heap_uint32 bie bid a1a) ()) ())
                              (fn xc =>
                                (fn f_ => fn () => f_ ((get_level_code ai xc)
                                  ()) ())
                                  (fn xd =>
                                    (fn f_ => fn () => f_
                                      ((nth_raa_u heap_uint32 bie bid a1a) ())
                                      ())
                                      (fn xaa =>
(fn f_ => fn () => f_ ((is_in_conflict_code a1c xaa) ()) ())
  (fn xab =>
    (fn f_ => fn () => f_
      ((if Word32.< (xd, count_decided_pol ai) andalso not xab
         then (fn f_ => fn () => f_ ((nth_raa_u heap_uint32 bie bid a1a) ()) ())
                (arl_append (default_uint32, heap_uint32) a2d)
         else (fn () => a2d))
      ()) ())
      (fn x_c =>
        (fn f_ => fn () => f_ ((nth_raa_u heap_uint32 bie bid a1a) ()) ())
          (fn xe =>
            (fn f_ => fn () => f_ ((get_level_code ai xe) ()) ())
              (fn xf =>
                (fn f_ => fn () => f_ ((nth_raa_u heap_uint32 bie bid a1a) ())
                  ())
                  (fn xac =>
                    (fn f_ => fn () => f_ ((is_in_conflict_code a1c xac) ()) ())
                      (fn xad =>
                        (fn f_ => fn () => f_
                          (let
                             val (a1e, a2e) = a1c;
                           in
                             (fn f_ => fn () => f_
                               ((nth_raa_u heap_uint32 bie bid a1a) ()) ())
                               (fn xg =>
                                 (fn f_ => fn () => f_
                                   ((nth_u_code heap_bool a2e (atm_of_code xg))
                                   ()) ())
                                   (fn xh =>
                                     (fn f_ => fn () => f_
                                       ((nth_raa_u heap_uint32 bie bid a1a) ())
                                       ())
                                       (fn xae =>
 (fn f_ => fn () => f_ ((nth_raa_u heap_uint32 bie bid a1a) ()) ())
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
                              (Word32.+ (a1a, (Word32.fromInt 1)),
                                ((if ((xf : Word32.word) = (count_decided_pol
                     ai)) andalso
                                       not xad
                                   then Word32.+ (a1b, (Word32.fromInt 1))
                                   else a1b),
                                  (x_g, (x_a, x_c)))))))))))))))))))
              ((Word32.fromInt 0), (bib, (a2, (bia, bi)))) ();
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
        (fn () =>
          (a1, (a1a, (a1m, ([], (a1d, (a1e,
(a1f, (a1n, (a1h, (a1o, (a2o, (incr_conflict a1k, (a1l, a2l))))))))))))))
      end
        ()
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
  (fn ai => fn bia => fn bi => let
                                 val (_, (_, (_, (_, (a1d, _))))) = ai;
                               in
                                 nth_aa_u heap_nat a1d bia bi
                               end)
    x;

fun update_aa_u A_ a i j y =
  (fn () =>
    let
      val x =
        nth_u_code (heap_prod (heap_array (typerep_heap A_)) heap_nat) a i ();
      val aa = arl_set A_ x j y ();
    in
      array_upd_u (heap_prod (heap_array (typerep_heap A_)) heap_nat) i aa a ()
    end);

fun delete_index_and_swap_aa_u A_ xs i j =
  (fn () => let
              val x = last_aa_u A_ xs i ();
              val xsa = update_aa_u A_ xs i j x ();
            in
              set_butlast_aa_u A_ xsa i ()
            end);

fun swap_aa_u64 (A1_, A2_) xs k i j =
  (fn () => let
              val xi = arl_get (heap_array (typerep_heap A2_)) xs k ();
              val xj = swap_u64_code A2_ xi i j ();
              val x = arl_set (heap_array (typerep_heap A2_)) xs k xj ();
            in
              x
            end);

fun update_clause_wl_code x =
  (fn ai => fn bid => fn bic => fn bib => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = nth_raa_i_u64 heap_uint32 a1a bid bia ();
      val x_b = swap_aa_u64 (default_uint32, heap_uint32) a1a bid bib bia ();
      val x_d = delete_index_and_swap_aa_u heap_nat a1d ai bic ();
      val xb = append_el_aa_u (default_nat, heap_nat) x_d xa bid ();
    in
      (bic, (a1, (x_b, (a1b, (a1c, (xb, a2d))))))
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
      val xc =
        heap_array_set_u (heap_option heap_nat) a1c (atm_of_code ai) (SOME bia)
          ();
    in
      (xa, (xab, (xb, (xc, (a1d, a2d)))))
    end)
    x;

fun propagate_lit_wl_code x =
  (fn ai => fn bib => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, a2l)))))))))))))
      =>
    fn () =>
    let
      val xa =
        swap_aa_u64 (default_uint32, heap_uint32) a1a bib Uint64.zero
          (fast_minus minus_uint64 Uint64.one bia) ();
      val x_a = cons_trail_Propagated_tr_code ai bib a1 ();
    in
      (x_a, (xa, (a1b, (uminus_code ai :: a1c,
                         (a1d, (a1e, (a1f, (a1g,
     (a1h, (a1i, (a1j, (incr_propagation a1k, (a1l, a2l)))))))))))))
    end)
    x;

fun polarity_st_heur_pol_code x =
  (fn ai => fn bi => let
                       val (a1, _) = ai;
                     in
                       polarity_pol_code a1 bi
                     end)
    x;

fun unit_propagation_inner_loop_body_wl_heur_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = watched_by_app_heur_code bi ai bia ();
      val xaa = access_lit_in_clauses_heur_code bi xa Uint64.zero ();
    in
      let
        val x_b =
          (if ((xaa : Word32.word) = ai) then Uint64.zero else Uint64.one);
      in
        (fn f_ => fn () => f_
          ((access_lit_in_clauses_heur_code bi xa
             (fast_minus minus_uint64 Uint64.one x_b))
          ()) ())
          (fn x_d =>
            (fn f_ => fn () => f_ ((polarity_st_heur_pol_code bi x_d) ()) ())
              (fn x_f =>
                (if ((x_f : Word32.word) = sET_TRUE_code)
                  then (fn () => (plus_nat bia one_nata, bi))
                  else (fn f_ => fn () => f_
                         ((find_unwatched_wl_st_heur_code bi xa) ()) ())
                         (fn a =>
                           (case a
                             of NONE =>
                               (if ((x_f : Word32.word) = sET_FALSE_code)
                                 then (fn f_ => fn () => f_
((set_conflict_wl_heur_code xa bi) ()) ())
(fn x_k => (fn () => (plus_nat bia one_nata, x_k)))
                                 else (fn f_ => fn () => f_
((propagate_lit_wl_code x_d xa x_b bi) ()) ())
(fn x_k => (fn () => (plus_nat bia one_nata, x_k))))
                             | SOME x_j =>
                               update_clause_wl_code ai xa bia x_b x_j bi)))))
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

fun length_ll_fs_heur_code x =
  (fn ai => fn bi => let
                       val (_, (_, (_, (_, (a1d, _))))) = ai;
                     in
                       length_aa_u heap_nat a1d bi
                     end)
    x;

fun get_conflict_wl_is_None_code x =
  (fn xi => (fn () => let
                        val (_, (_, (a1b, (_, (_, _))))) = xi;
                      in
                        lookup_clause_assn_is_None a1b
                      end))
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
      (fn (a, b) => unit_propagation_inner_loop_body_wl_heur_code ai a b)
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
                        val (_, (_, (_, (a1c, (_, _))))) = xi;
                      in
                        op_list_is_empty a1c
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

fun maximum_level_removed_eq_count_dec_code x =
  (fn _ => fn bi =>
    (fn () => (Word32.< ((Word32.fromInt 1), get_count_max_lvls_code bi))))
    x;

fun last_trail_code x =
  (fn (a1, (_, (_, (a1c, _)))) => fn () =>
    let
      val xa = arl_last heap_uint32 a1 ();
      val xaa = arl_last heap_uint32 a1 ();
      val x_a = nth_u_code (heap_option heap_nat) a1c (atm_of_code xaa) ();
    in
      (xa, x_a)
    end)
    x;

fun lit_and_ann_of_propagated_st_heur_code x =
  (fn (a1, _) => fn () => let
                            val xa = last_trail_code a1 ();
                            val xaa = last_trail_code a1 ();
                          in
                            (fst xa, the (snd xaa))
                          end)
    x;

fun atm_is_in_option_lookup_conflict_code x =
  (fn ai => fn (_, (_, (a1b, _))) => is_in_option_lookup_conflict_code ai a1b)
    x;

fun is_decided_wl_code x = (fn xi => (fn () => (is_None (snd xi)))) x;

fun is_decided_hd_trail_wl_code x =
  (fn (a1, _) => fn () => let
                            val xa = last_trail_code a1 ();
                          in
                            is_decided_wl_code xa ()
                          end)
    x;

fun resolve_lookup_conflict_merge_code x =
  (fn ai => fn bie => fn bid => fn bic => fn bib => fn bia => fn bi =>
    let
      val (_, a2) = bic;
    in
      (fn () =>
        let
          val a =
            heap_WHILET
              (fn (a1a, (_, (_, (_, _)))) =>
                (fn f_ => fn () => f_ ((length_raa_u heap_uint32 bie bid) ())
                  ())
                  (fn x_a => (fn () => (Word32.< (a1a, x_a)))))
              (fn (a1a, (a1b, (a1c, (a1d, a2d)))) =>
                (fn f_ => fn () => f_ ((nth_raa_u heap_uint32 bie bid a1a) ())
                  ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((get_level_code ai xa) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((lbd_write_code a1d xb true) ())
                          ())
                          (fn x_a =>
                            (fn f_ => fn () => f_
                              ((nth_raa_u heap_uint32 bie bid a1a) ()) ())
                              (fn xc =>
                                (fn f_ => fn () => f_ ((get_level_code ai xc)
                                  ()) ())
                                  (fn xd =>
                                    (fn f_ => fn () => f_
                                      ((nth_raa_u heap_uint32 bie bid a1a) ())
                                      ())
                                      (fn xaa =>
(fn f_ => fn () => f_ ((is_in_conflict_code a1c xaa) ()) ())
  (fn xab =>
    (fn f_ => fn () => f_
      ((if Word32.< (xd, count_decided_pol ai) andalso not xab
         then (fn f_ => fn () => f_ ((nth_raa_u heap_uint32 bie bid a1a) ()) ())
                (arl_append (default_uint32, heap_uint32) a2d)
         else (fn () => a2d))
      ()) ())
      (fn x_c =>
        (fn f_ => fn () => f_ ((nth_raa_u heap_uint32 bie bid a1a) ()) ())
          (fn xe =>
            (fn f_ => fn () => f_ ((get_level_code ai xe) ()) ())
              (fn xf =>
                (fn f_ => fn () => f_ ((nth_raa_u heap_uint32 bie bid a1a) ())
                  ())
                  (fn xac =>
                    (fn f_ => fn () => f_ ((is_in_conflict_code a1c xac) ()) ())
                      (fn xad =>
                        (fn f_ => fn () => f_
                          (let
                             val (a1e, a2e) = a1c;
                           in
                             (fn f_ => fn () => f_
                               ((nth_raa_u heap_uint32 bie bid a1a) ()) ())
                               (fn xg =>
                                 (fn f_ => fn () => f_
                                   ((nth_u_code heap_bool a2e (atm_of_code xg))
                                   ()) ())
                                   (fn xh =>
                                     (fn f_ => fn () => f_
                                       ((nth_raa_u heap_uint32 bie bid a1a) ())
                                       ())
                                       (fn xae =>
 (fn f_ => fn () => f_ ((nth_raa_u heap_uint32 bie bid a1a) ()) ())
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
                              (Word32.+ (a1a, (Word32.fromInt 1)),
                                ((if ((xf : Word32.word) = (count_decided_pol
                     ai)) andalso
                                       not xad
                                   then Word32.+ (a1b, (Word32.fromInt 1))
                                   else a1b),
                                  (x_g, (x_a, x_c)))))))))))))))))))
              ((Word32.fromInt 1), (bib, (a2, (bia, bi)))) ();
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

fun tl_trail_tr_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val xa = arl_last heap_uint32 a1 ();
      val x_a = arl_butlast heap_uint32 a1 ();
      val xaa = heap_array_set_u heap_uint32 a1a xa uNSET_code ();
      val xab = heap_array_set_u heap_uint32 xaa (uminus_code xa) uNSET_code ();
      val xb =
        heap_array_set_u heap_uint32 a1b (atm_of_code xa) (Word32.fromInt 0) ();
      val xc = nth_u_code (heap_option heap_nat) a1c (atm_of_code xa) ();
      val xd = nth_u_code (heap_option heap_nat) a1c (atm_of_code xa) ();
      val xe =
        (if is_None xd then arl_butlast heap_uint32 a2d else (fn () => a2d)) ();
    in
      (x_a, (xab, (xb, (a1c, ((if is_None xc
                                then fast_minus_uint32 a1d (Word32.fromInt 1)
                                else a1d),
                               xe)))))
    end)
    x;

fun update_confl_tl_wl_code x =
  (fn ai => fn bia =>
    fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
    (a1g, (a1h, (a1i, (a1j, a2j)))))))))))
      =>
    fn () =>
    let
      val a = resolve_lookup_conflict_merge_code a1 a1a ai a1b a1g a1i a1j ();
    in
      let
        val (a1k, (a1l, (a1m, a2m))) = a;
      in
        (fn f_ => fn () => f_
          ((conflict_remove1_code (uminus_code bia) (snd a1k)) ()) ())
          (fn x_c =>
            (fn f_ => fn () => f_ ((tl_trail_tr_code a1) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((vmtf_mark_to_rescore_and_unset_code (atm_of_code bia) a1e)
                  ()) ())
                  (fn xaa =>
                    (fn f_ => fn () => f_
                      ((heap_array_set_u heap_bool a1f (atm_of_code bia)
                         (is_pos_code bia))
                      ()) ())
                      (fn xb =>
                        (fn () =>
                          (false,
                            (xa, (a1a, ((false, x_c),
 (a1c, (a1d, (xaa, (xb, (fast_minus_uint32 a1l (Word32.fromInt 1),
                          (a1h, (a1m, (a2m, a2j)))))))))))))))))
      end
        ()
    end)
    x;

fun tl_state_wl_heur_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) => fn () =>
    let
      val xa = last_trail_code a1 ();
    in
      let
        val xb = fst xa;
      in
        (fn f_ => fn () => f_ ((tl_trail_tr_code a1) ()) ())
          (fn x_a =>
            (fn f_ => fn () => f_
              (let
                 val ((a1h, (a1i, (a1j, (a1k, a2k)))), a2g) = a1e;
               in
                 (fn f_ => fn () => f_
                   ((if is_None a2k then (fn () => true)
                      else (fn f_ => fn () => f_
                             ((nth_u_code (heap_vmtf_node heap_uint32 heap_nat)
                                a1h (the a2k))
                             ()) ())
                             (fn xaa =>
                               (fn f_ => fn () => f_
                                 ((nth_u_code
                                    (heap_vmtf_node heap_uint32 heap_nat) a1h
                                    (atm_of_code xb))
                                 ()) ())
                                 (fn xc =>
                                   (fn () =>
                                     (less_nat (stamp xaa) (stamp xc))))))
                   ()) ())
                   (fn x_b =>
                     (fn () =>
                       (if x_b
                         then ((a1h, (a1i, (a1j,
     (a1k, SOME (atm_of_code xb))))),
                                a2g)
                         else ((a1h, (a1i, (a1j, (a1k, a2k)))), a2g))))
               end
              ()) ())
              (fn xc =>
                (fn () => (x_a, (a1a, (a1b, (a1c, (a1d, (xc, (a1f, a2f))))))))))
      end
        ()
    end)
    x;

fun skip_and_resolve_loop_wl_D_code x =
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
                  ((atm_is_in_option_lookup_conflict_code (uminus_code a1a) a2)
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
                (fn f_ => fn () => f_
                  ((nth_raa heap_uint32 ai a1a (minus_nat a2a one_nata)) ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_
                      ((conflict_min_cach_set_failed_l_code a2 (atm_of_code xa))
                      ()) ())
                      (fn x_d => (fn () => (plus_nat a1 one_nata, x_d))))))
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
  (fn ai => fn bi => let
                       val (_, (_, (_, (a1c, _)))) = ai;
                     in
                       nth_u_code (heap_option heap_nat) a1c (atm_of_code bi)
                     end)
    x;

fun length_raa A_ xs i =
  (fn () => let
              val x = arl_get (heap_array (typerep_heap A_)) xs i ();
            in
              len A_ x ()
            end);

fun lit_redundant_rec_wl_lookup_code x =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi =>
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
          val xaa = arl_last (heap_prod heap_nat heap_nat) a1a ();
          val xab = length_raa heap_uint32 bid (fst xaa) ();
        in
          (if less_eq_nat xab (snd xa)
            then (fn f_ => fn () => f_
                   ((arl_last (heap_prod heap_nat heap_nat) a1a) ()) ())
                   (fn xb =>
                     (fn f_ => fn () => f_
                       ((nth_raa heap_uint32 bid (fst xb) zero_nata) ()) ())
                       (fn xc =>
                         (fn f_ => fn () => f_
                           ((conflict_min_cach_set_removable_l_code a1
                              (atm_of_code xc))
                           ()) ())
                           (fn x_d =>
                             (fn f_ => fn () => f_
                               ((arl_butlast (heap_prod heap_nat heap_nat) a1a)
                               ()) ())
                               (fn xd => (fn () => (x_d, (xd, true)))))))
            else (fn f_ => fn () => f_
                   ((arl_last (heap_prod heap_nat heap_nat) a1a) ()) ())
                   (fn xb =>
                     (fn f_ => fn () => f_
                       (let
                          val (a1b, a2b) = xb;
                        in
                          (fn f_ => fn () => f_
                            ((arl_last (heap_prod heap_nat heap_nat) a1a) ())
                            ())
                            (fn xc =>
                              (fn f_ => fn () => f_
                                ((nth_raa heap_uint32 bid (fst xc) a2b) ()) ())
                                (fn x_e =>
                                  (fn f_ => fn () => f_
                                    ((arl_length (heap_prod heap_nat heap_nat)
                                       a1a)
                                    ()) ())
                                    (fn xd =>
                                      (fn f_ => fn () => f_
((arl_set (heap_prod heap_nat heap_nat) a1a (minus_nat xd one_nata)
   (a1b, plus_nat a2b one_nata))
()) ())
(fn x_f => (fn () => (x_e, x_f))))))
                        end
                       ()) ())
                       (fn (a1b, a2b) =>
                         (fn f_ => fn () => f_ ((get_level_code ai a1b) ()) ())
                           (fn xc =>
                             (fn f_ => fn () => f_ ((level_in_lbd_code xc bi)
                               ()) ())
                               (fn xd =>
                                 (fn f_ => fn () => f_ ((get_level_code ai a1b)
                                   ()) ())
                                   (fn xac =>
                                     (fn f_ => fn () => f_
                                       ((conflict_min_cach_l_code a1
  (atm_of_code a1b))
                                       ()) ())
                                       (fn xba =>
 (fn f_ => fn () => f_ ((atm_in_conflict_code (atm_of_code a1b) bic) ()) ())
   (fn xca =>
     (if ((xac : Word32.word) = (Word32.fromInt 0)) orelse
           (equal_minimize_status xba SEEN_REMOVABLE orelse xca)
       then (fn () => (a1, (a2b, false)))
       else (fn f_ => fn () => f_
              ((conflict_min_cach_l_code a1 (atm_of_code a1b)) ()) ())
              (fn xad =>
                (if not xd orelse equal_minimize_status xad SEEN_FAILED
                  then (fn f_ => fn () => f_
                         ((mark_failed_lits_stack_code bid a2b a1) ()) ())
                         (fn x_j =>
                           (fn f_ => fn () => f_
                             ((arl_empty
                                (default_prod default_nat default_nat,
                                  heap_prod heap_nat heap_nat)
                                zero_nat)
                             ()) ())
                             (fn xe => (fn () => (x_j, (xe, false)))))
                  else (fn f_ => fn () => f_
                         ((get_propagation_reason_code ai (uminus_code a1b)) ())
                         ())
                         (fn a =>
                           (case a
                             of NONE =>
                               (fn f_ => fn () => f_
                                 ((mark_failed_lits_stack_code bid a2b a1) ())
                                 ())
                                 (fn x_k =>
                                   (fn f_ => fn () => f_
                                     ((arl_empty
(default_prod default_nat default_nat, heap_prod heap_nat heap_nat) zero_nat)
                                     ()) ())
                                     (fn xe => (fn () => (x_k, (xe, false)))))
                             | SOME x_k =>
                               (fn f_ => fn () => f_
                                 ((arl_append
                                    (default_prod default_nat default_nat,
                                      heap_prod heap_nat heap_nat)
                                    a2b (x_k, one_nata))
                                 ()) ())
                                 (fn xe =>
                                   (fn () => (a1, (xe, false)))))))))))))))))
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
                  (default_prod default_nat default_nat,
                    heap_prod heap_nat heap_nat)
                  zero_nat)
               ()) ())
               (fn xb => (fn () => (bib, (xb, true))))
        else (fn f_ => fn () => f_
               ((conflict_min_cach_l_code bib (atm_of_code bia)) ()) ())
               (fn xb =>
                 (if equal_minimize_status xb SEEN_FAILED
                   then (fn f_ => fn () => f_
                          ((arl_empty
                             (default_prod default_nat default_nat,
                               heap_prod heap_nat heap_nat)
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
                                     (default_prod default_nat default_nat,
                                       heap_prod heap_nat heap_nat)
                                     zero_nat)
                                  ()) ())
                                  (fn xc => (fn () => (bib, (xc, false))))
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
 (x_c, one_nata))
                                      ()) ())
                                      (fn x_d =>
lit_redundant_rec_wl_lookup_code ai bid bic bib x_d bi)))))))
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
              (((fn () => Array.sub ((fn (a,b) => a) a2b, Word32.toInt a1a)))
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
                      else (fn f_ => fn () => f_
                             ((delete_from_lookup_conflict_code x_a a1) ()) ())
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
              (((fn () => Array.sub ((fn (a,b) => a) bi, Word32.toInt a2a))) ())
              ())
              (fn xc =>
                (fn f_ => fn () => f_ ((delete_from_lookup_conflict_code xc a1)
                  ()) ())
                  (fn x_c =>
                    (fn f_ => fn () => f_
                      (((fn () => Array.sub ((fn (a,b) => a) bi,
                         Word32.toInt a2a)))
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
              ((if equal_nat xc one_nata then (fn () => (Word32.fromInt 0))
                 else (fn f_ => fn () => f_ ((nth heap_uint32 a1a one_nata) ())
                        ())
                        (get_level_code ai))
              ()) ())
              (fn xd => (fn () => (let
                                     val (n, xs) = a1;
                                   in
                                     (true, (n, xs))
                                   end,
                                    (a1a, xd)))))
      end
        ()
    end)
    x;

fun extract_shorter_conflict_list_heur_st_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, a2j)))))))))))
     =>
    fn () =>
    let
      val xa = last_trail_code a1 ();
    in
      let
        val xb = fst xa;
      in
        (fn f_ => fn () => f_
          ((delete_from_lookup_conflict_code (uminus_code xb) (snd a1b)) ()) ())
          (fn x_b =>
            (fn f_ => fn () => f_
              ((arl_set heap_uint32 a1j zero_nata (uminus_code xb)) ()) ())
              (fn x_d =>
                (fn f_ => fn () => f_
                  ((minimize_and_extract_highest_lookup_conflict_code a1 a1a x_b
                     a1h a1i x_d)
                  ()) ())
                  (fn (a1k, (a1l, a2l)) =>
                    (fn f_ => fn () => f_ ((empty_cach_code a1l) ()) ())
                      (fn x_g =>
                        (fn f_ => fn () => f_
                          ((empty_conflict_and_extract_clause_heur_code a1 a1k
                             a2l)
                          ()) ())
                          (fn (a1m, (a1n, a2n)) =>
                            (fn () =>
                              ((a1, (a1a, (a1m,
    (a1c, (a1d, (a1e, (a1f, (a1g, (x_g, (a1i,
  (let
     val (a, _) = a2l;
   in
     (a, one_nata)
   end,
    a2j))))))))))),
                                (a2n, a1n))))))))
      end
        ()
    end)
    x;

fun lit_of_last_trail_code x = (fn (a1, _) => arl_last heap_uint32 a1) x;

fun lit_of_hd_trail_st_heur_code x =
  (fn (a1, (_, (_, (_, (_, (_, _)))))) => lit_of_last_trail_code a1) x;

fun vmtf_flush_all_code x = (fn _ => vmtf_flush_code) x;

fun propagate_unit_bt_wl_D_code x =
  (fn ai =>
    fn (a1, (a1a, (a1b, (_, (a1d, (a1e, (a1f,
  (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, a2m))))))))))))))
      =>
    fn () =>
    let
      val xa = vmtf_flush_all_code a1 a1e ();
      val x_a = get_LBD_code a1i ();
      val x_b = lbd_empty_code a1i ();
      val x_c = cons_trail_Propagated_tr_code (uminus_code ai) zero_nata a1 ();
    in
      (x_c, (a1a, (a1b, ([ai],
                          (a1d, (xa, (a1f, (a1g,
     (a1h, (x_b, (a1j, (a1k, (ema_update_ref (nat_of_integer (5 : IntInf.int))
                                a1l x_a,
                               (ema_update_ref
                                  (nat_of_integer (14 : IntInf.int)) a1m x_a,
                                 Word32.+ (a2m, (Word32.fromInt 1))))))))))))))))
    end)
    x;

fun find_decomp_wl_imp_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET (fn (a1, (_, _)) => (fn () => (Word32.< (bia, a1))))
          (fn (a1, (a1a, a2a)) =>
            (fn f_ => fn () => f_ ((last_trail_code a1a) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_ ((is_decided_wl_code xa) ()) ())
                  (fn x_c =>
                    (if x_c
                      then (fn f_ => fn () => f_ ((last_trail_code a1a) ()) ())
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
 (fast_minus_uint32 a1 (Word32.fromInt 1), (xaa, xc))))))
                      else (fn f_ => fn () => f_ ((last_trail_code a1a) ()) ())
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

fun append_and_length_code x =
  (fn _ => fn bia => fn bi => fn () =>
    let
      val xa = length_ra heap_uint32 bi ();
      val x_a = arrayO_raa_append (default_uint32, heap_uint32) bi bia ();
    in
      (x_a, xa)
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
                            (fn () => (plus_nat a1 one_nata, (x_a, x_c))))))))
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
  (_, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, a2m))))))))))))))
      =>
    fn () =>
    let
      val xa = nth heap_uint32 bia one_nata ();
      val a = vmtf_rescore_code bia a1 a1e a1f ();
    in
      let
        val (a1n, a2n) = a;
      in
        (fn f_ => fn () => f_ ((vmtf_flush_all_code a1 a1n) ()) ())
          (fn x_c =>
            (fn f_ => fn () => f_ ((get_LBD_code a1i) ()) ())
              (fn x_d =>
                (fn f_ => fn () => f_ ((append_and_length_code false bia a1a)
                  ()) ())
                  (fn (a1o, a2o) =>
                    (fn f_ => fn () => f_
                      ((append_el_aa_u (default_nat, heap_nat) a1d
                         (uminus_code ai) a2o)
                      ()) ())
                      (fn x_h =>
                        (fn f_ => fn () => f_
                          ((append_el_aa_u (default_nat, heap_nat) x_h xa a2o)
                          ()) ())
                          (fn x_j =>
                            (fn f_ => fn () => f_ ((lbd_empty_code a1i) ()) ())
                              (fn x_l =>
                                (fn f_ => fn () => f_
                                  ((cons_trail_Propagated_tr_code
                                     (uminus_code ai) a2o a1)
                                  ()) ())
                                  (fn x_m =>
                                    (fn () =>
                                      (x_m,
(a1o, (a1b, ([ai],
              (x_j, (x_c, (a2n, ((Word32.fromInt 0),
                                  (a1h, (x_l,
  (a1j, (a1k, (ema_update_ref (nat_of_integer (5 : IntInf.int)) a1l x_d,
                (ema_update_ref (nat_of_integer (14 : IntInf.int)) a1m x_d,
                  Word32.+ (a2m, (Word32.fromInt 1))))))))))))))))))))))))
      end
        ()
    end)
    x;

fun backtrack_wl_D_nlit_heur_code x =
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
                (if less_nat one_nata xaa then propagate_bt_wl_D_code xa a2a x_c
                  else propagate_unit_bt_wl_D_code xa x_c)))
      end
        ()
    end)
    x;

fun defined_atm_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, _))) = ai;
    in
      (fn () =>
        let
          val xa =
            nth_u_code heap_uint32 a1a (Word32.* ((Word32.fromInt 2), bi)) ();
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
              nth_u_code (heap_vmtf_node heap_uint32 heap_nat) a1a (the s) ();
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
      val xc =
        heap_array_set_u (heap_option heap_nat) a1c (atm_of_code ai) NONE ();
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
      val xa = cons_trail_Decided_tr_code ai a1 ();
    in
      (xa, (a1a, (a1b, ([uminus_code ai],
                         (a1d, (a1e, (a1f, (a1g,
     (a1h, (a1i, (a1j, (incr_decision a1k, (a1l, a2l)))))))))))))
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

fun count_decided_st_code x = (fn xi => (fn () => let
            val (a1, _) = xi;
          in
            count_decided_pol a1
          end))
                                x;

fun cdcl_twl_o_prog_wl_D_code x =
  (fn xi => fn () =>
    let
      val xa = get_conflict_wl_is_None_code xi ();
    in
      (if xa then decide_wl_or_skip_D_code xi
        else (fn f_ => fn () => f_ ((count_decided_st_code xi) ()) ())
               (fn xb =>
                 (if Word32.< ((Word32.fromInt 0), xb)
                   then (fn f_ => fn () => f_
                          ((skip_and_resolve_loop_wl_D_code xi) ()) ())
                          (fn x_b =>
                            (fn f_ => fn () => f_
                              ((backtrack_wl_D_nlit_heur_code x_b) ()) ())
                              (fn x_c => (fn () => (false, x_c))))
                   else (fn () => (true, xi)))))
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

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun option_nat_of_uint32 x = map_option nat_of_uint32 x;

fun array_option_nat_of_uint32_code x =
  (fn xi => fn () =>
    let
      val xa = len (heap_option heap_uint32) xi ();
      val xb = new (heap_option heap_nat) xa NONE ();
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((len (heap_option heap_nat) a2) ()) ())
              (fn x_c => (fn () => (less_nat a1 x_c))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((nth (heap_option heap_uint32) xi a1) ()) ())
              (fn xc =>
                (fn f_ => fn () => f_
                  ((upd (heap_option heap_nat) a1 (option_nat_of_uint32 xc) a2)
                  ()) ())
                  (fn x_d => (fn () => (plus_nat a1 one_nata, x_d)))))
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
      val xa = array_option_nat_of_uint32_code a1c ();
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
            (fn f_ => fn () => f_ ((length_aa heap_uint32 ai bib) ()) ())
              (fn x_a => (fn () => (less_nat a1 x_a))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((nth_aa heap_uint32 ai bib a1) ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_
                  ((append_el_aa (default_nat, heap_nat) a2 bi
                     (nat_of_uint32 x_a))
                  ()) ())
                  (fn x_d => (fn () => (plus_nat a1 one_nata, x_d)))))
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

fun length_a A_ xs = len A_ xs;

fun convert_wlists_to_nat_code x =
  (fn xi => fn () =>
    let
      val xa = length_a (heap_prod (heap_array typerep_uint32) heap_nat) xi ();
      val xb = arrayO_ara_empty_sz_code (default_nat, heap_nat) xa ();
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((length_a (heap_prod (heap_array typerep_nat) heap_nat) a2) ())
              ())
              (fn x_c => (fn () => (less_nat a1 x_c))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((convert_single_wl_to_nat_code xi a1 a2 a1)
              ()) ())
              (fn x_d => (fn () => (plus_nat a1 one_nata, x_d))))
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

fun isasat_fast_slow_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, a2m))))))))))))))
     =>
    fn () =>
    let
      val xa = trail_pol_slow_of_fast_code a1 ();
      val xaa = convert_wlists_to_nat_code a1d ();
    in
      (xa, (a1a, (a1b, (a1c, (xaa, (a1e, (a1f,
   (a1g, (a1h, (a1i, (a1j, (a1k, (a1l, (a1m, a2m))))))))))))))
    end)
    x;

fun power A_ a n =
  (if equal_nat n zero_nata then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nat n one_nata)));

val uint32_max : nat =
  minus_nat
    (power power_nat (nat_of_integer (2 : IntInf.int))
      (nat_of_integer (32 : IntInf.int)))
    one_nata;

fun isasat_fast2_code x = (fn xi => (fn () => let
        val (_, ((_, n), _)) = xi;
      in
        less_eq_nat n uint32_max
      end))
                            x;

fun cdcl_twl_stgy_prog_wl_D_fast_code x =
  (fn xi => fn () =>
    let
      val xa = isasat_fast2_code xi ();
      val a =
        heap_WHILET (fn (a1, (a1a, _)) => (fn () => (a1 andalso not a1a)))
          (fn (_, (_, a2a)) =>
            (fn f_ => fn () => f_ ((unit_propagation_outer_loop_wl_D_fast a2a)
              ()) ())
              (fn x_c =>
                (fn f_ => fn () => f_ ((cdcl_twl_o_prog_wl_D_fast_code x_c) ())
                  ())
                  (fn (a1b, a2b) =>
                    (fn f_ => fn () => f_ ((isasat_fast2_code a2b) ()) ())
                      (fn x_e => (fn () => (x_e, (a1b, a2b)))))))
          (xa, (false, xi)) ();
    in
      (case a of (_, (true, a2a)) => isasat_fast_slow_code a2a
        | (_, (false, a2a)) =>
          (fn f_ => fn () => f_ ((isasat_fast_slow_code a2a) ()) ())
            cdcl_twl_stgy_prog_wl_D_code)
        ()
    end)
    x;

fun init_trail_D_code x =
  (fn _ => fn bia => fn bi => fn () =>
    let
      val xa = arl_empty (default_uint32, heap_uint32) zero_nat ();
      val x_b = arl_empty (default_uint32, heap_uint32) zero_nat ();
      val x_d = new heap_uint32 bi uNSET_code ();
      val x_f = new heap_uint32 bia (Word32.fromInt 0) ();
      val x_h = new (heap_option heap_nat) bia NONE ();
    in
      (xa, (x_d, (x_f, (x_h, ((Word32.fromInt 0), x_b)))))
    end)
    x;

fun init_state_wl_D_code x =
  (fn (a1, a2) =>
    let
      val x_a = suc (nat_of_uint32 a2);
      val x_c = times_nata (nat_of_integer (2 : IntInf.int)) x_a;
    in
      (fn () =>
        let
          val x_e = init_trail_D_code a1 x_a x_c ();
          val x_f = init_rll_list_code x_a ();
          val xa = new heap_bool x_a false ();
          val x_j = arrayO_ara_empty_sz_code (default_nat, heap_nat) x_c ();
          val x_l = initialise_VMTF_code a1 x_a ();
          val x_m = new heap_bool x_a false ();
          val xaa = new heap_minimize_status x_a SEEN_UNKNOWN ();
          val xb = arl_empty (default_uint32, heap_uint32) zero_nat ();
          val x_q = empty_lbd_code ();
        in
          (x_e, (x_f, ((true, ((Word32.fromInt 0), xa)),
                        ([], (x_j, (x_l, (x_m,
   ((Word32.fromInt 0), ((xaa, xb), x_q)))))))))
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

fun set_conflict_empty_code x = (fn xi => (fn () => let
              val (_, a) = xi;
            in
              (false, a)
            end))
                                  x;

fun set_empty_clause_as_conflict_fast_code x =
  (fn (a1, (a1a, (a1b, (_, a2c)))) => fn () =>
    let
      val xa = set_conflict_empty_code a1b ();
    in
      (a1, (a1a, (xa, ([], a2c))))
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

fun conflict_propagated_unit_cls_fast_code x =
  (fn ai => fn (a1, (a1a, (a1b, (_, a2c)))) => fn () =>
    let
      val xa = set_conflict_unit_code ai a1b ();
    in
      (a1, (a1a, (xa, ([], a2c))))
    end)
    x;

fun already_propagated_unit_cls_fast_code x =
  (fn _ => fn bi => (fn () => let
                                val (a1, (a1a, (a1b, (a1c, a2c)))) = bi;
                              in
                                (a1, (a1a, (a1b, (a1c, a2c))))
                              end))
    x;

fun polarity_st_heur_init_fast_code x =
  (fn ai => fn bi => let
                       val (a1, _) = ai;
                     in
                       polarity_pol_fast_code a1 bi
                     end)
    x;

fun add_clause_to_others_fast_code x =
  (fn _ => fn bi => (fn () => let
                                val (a1, (a1a, (a1b, (a1c, a2c)))) = bi;
                              in
                                (a1, (a1a, (a1b, (a1c, a2c))))
                              end))
    x;

fun propagate_unit_cls_fast_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, a2c)))) => fn () =>
    let
      val xa = cons_trail_Propagated_tr_fast_code ai (Word32.fromInt 0) a1 ();
    in
      (xa, (a1a, (a1b, (uminus_code ai :: a1c, a2c))))
    end)
    x;

fun add_init_cls_fast_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val x_f = (fn () => Array.fromList ai) ();
      val a = append_and_length_u32_code true x_f a1a ();
    in
      let
        val (a1e, a2e) = a;
      in
        (fn f_ => fn () => f_
          ((append_el_aa_u (default_uint32, heap_uint32) a1d (op_list_hd ai)
             a2e)
          ()) ())
          (fn x_i =>
            (fn f_ => fn () => f_
              ((append_el_aa_u (default_uint32, heap_uint32) x_i
                 (op_list_hd (op_list_tl ai)) a2e)
              ()) ())
              (fn x_k => (fn () => (a1, (a1e, (a1b, (a1c, (x_k, a2d))))))))
      end
        ()
    end)
    x;

fun list_length_1_code c =
  (case c of [] => false | [_] => true | _ :: _ :: _ => false);

fun is_Nil a = (case a of [] => true | _ :: _ => false);

fun init_dt_step_wl_fast_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = get_conflict_wl_is_None_init_fast_code bi ();
    in
      (if xa
        then (if is_Nil ai then set_empty_clause_as_conflict_fast_code bi
               else (if list_length_1_code ai
                      then let
                             val x_c = op_list_hd ai;
                           in
                             (fn f_ => fn () => f_
                               ((polarity_st_heur_init_fast_code bi x_c) ()) ())
                               (fn x_e =>
                                 (if ((x_e : Word32.word) = uNSET_code)
                                   then propagate_unit_cls_fast_code x_c bi
                                   else (if ((x_e : Word32.word) = sET_TRUE_code)
  then already_propagated_unit_cls_fast_code ai bi
  else conflict_propagated_unit_cls_fast_code x_c bi)))
                           end
                      else add_init_cls_fast_code ai bi))
        else add_clause_to_others_fast_code ai bi)
        ()
    end)
    x;

fun init_dt_wl_fast_code x =
  (fn ai => imp_nfoldli ai (fn _ => (fn () => true)) init_dt_step_wl_fast_code)
    x;

fun finalise_init_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (((a1g, (a1h, (a1i, (a1j, a2j)))), a2f),
                                     (a1k, (a1l, (a1m, a2m)))))))))
     =>
    fn () =>
    let
      val xa =
        arl_replicate heap_uint32 (nat_of_integer (160 : IntInf.int))
          (Word32.* ((Word32.fromInt 2), (Word32.fromInt 0))) ();
    in
      (a1, (a1a, (a1b, (a1c, (a1d, (((a1g, (a1h, (the a1i, (the a1j, a2j)))),
                                      a2f),
                                     (a1k, (a1l,
     (a1m, (a2m, (let
                    val (a, _) = xa;
                  in
                    (a, one_nata)
                  end,
                   ((Uint64.zero, (Uint64.zero, Uint64.zero)),
                     (Uint64.zero,
                       (Uint64.zero, (Word32.fromInt 0)))))))))))))))
    end)
    x;

fun set_empty_clause_as_conflict_code x =
  (fn (a1, (a1a, (a1b, (_, a2c)))) => fn () =>
    let
      val xa = set_conflict_empty_code a1b ();
    in
      (a1, (a1a, (xa, ([], a2c))))
    end)
    x;

fun conflict_propagated_unit_cls_code x =
  (fn ai => fn (a1, (a1a, (a1b, (_, a2c)))) => fn () =>
    let
      val xa = set_conflict_unit_code ai a1b ();
    in
      (a1, (a1a, (xa, ([], a2c))))
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
                       polarity_pol_code a1 bi
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
  (fn ai => fn (a1, (a1a, (a1b, (a1c, a2c)))) => fn () =>
    let
      val xa = cons_trail_Propagated_tr_code ai zero_nata a1 ();
    in
      (xa, (a1a, (a1b, (uminus_code ai :: a1c, a2c))))
    end)
    x;

fun add_init_cls_code x =
  (fn ai => fn (a1, (a1a, (a1b, (a1c, (a1d, a2d))))) => fn () =>
    let
      val x_f = (fn () => Array.fromList ai) ();
      val a = append_and_length_code true x_f a1a ();
    in
      let
        val (a1e, a2e) = a;
      in
        (fn f_ => fn () => f_
          ((append_el_aa_u (default_nat, heap_nat) a1d (op_list_hd ai) a2e) ())
          ())
          (fn x_i =>
            (fn f_ => fn () => f_
              ((append_el_aa_u (default_nat, heap_nat) x_i
                 (op_list_hd (op_list_tl ai)) a2e)
              ()) ())
              (fn x_k => (fn () => (a1, (a1e, (a1b, (a1c, (x_k, a2d))))))))
      end
        ()
    end)
    x;

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

fun init_dt_wl_code x =
  (fn ai => imp_nfoldli ai (fn _ => (fn () => true)) init_dt_step_wl_code) x;

val empty_conflict_code :
  (unit ->
    ((Word32.word array * nat) option *
      (Uint64.uint64 * (Uint64.uint64 * Uint64.uint64))))
  = (fn () => let
                val x = arl_empty (default_uint32, heap_uint32) zero_nat ();
              in
                (SOME x, (Uint64.zero, (Uint64.zero, Uint64.zero)))
              end);

val isaSAT_use_fast_mode : bool = true;

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

fun size_list x = gen_length zero_nata x;

fun op_list_length x = size_list x;

val empty_init_code :
  (unit ->
    ((Word32.word array * nat) option *
      (Uint64.uint64 * (Uint64.uint64 * Uint64.uint64))))
  = (fn () => (NONE, (Uint64.zero, (Uint64.zero, Uint64.zero))));

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
  (fn xi => fn () =>
    let
      val xa = extract_atms_clss_imp_empty_assn ();
      val xb = extract_atms_clss_imp xi xa ();
      val xc = extract_lits_sorted_code xb ();
    in
      (if isaSAT_use_fast_mode andalso
            less_nat (op_list_length xi) (minus_nat uint32_max one_nata)
        then (fn f_ => fn () => f_ ((init_state_wl_D_fast_code xc) ()) ())
               (fn x_e =>
                 (fn f_ => fn () => f_ ((init_dt_wl_fast_code xi x_e) ()) ())
                   (fn x_f =>
                     (fn f_ => fn () => f_
                       ((get_conflict_wl_is_None_init_fast_code x_f) ()) ())
                       (fn xd =>
                         (if not xd then empty_init_code
                           else (if op_list_is_empty xi then empty_conflict_code
                                  else (fn f_ => fn () => f_
 ((finalise_init_fast_code x_f) ()) ())
 (fn x_k =>
   (fn f_ => fn () => f_ ((cdcl_twl_stgy_prog_wl_D_fast_code x_k) ()) ())
     (fn x_l =>
       (fn f_ => fn () => f_ ((get_conflict_wl_is_None_code x_l) ()) ())
         (fn x_m =>
           (fn () =>
             (if x_m then get_trail_wl_code x_l
               else get_stats_code x_l))))))))))
        else (fn f_ => fn () => f_ ((init_state_wl_D_code xc) ()) ())
               (fn x_e =>
                 (fn f_ => fn () => f_ ((init_dt_wl_code xi x_e) ()) ())
                   (fn x_f =>
                     (fn f_ => fn () => f_
                       ((get_conflict_wl_is_None_init_code x_f) ()) ())
                       (fn xd =>
                         (if not xd then empty_init_code
                           else (if op_list_is_empty xi then empty_conflict_code
                                  else (fn f_ => fn () => f_
 ((finalise_init_code x_f) ()) ())
 (fn x_k =>
   (fn f_ => fn () => f_ ((cdcl_twl_stgy_prog_wl_D_code x_k) ()) ())
     (fn x_l =>
       (fn f_ => fn () => f_ ((get_conflict_wl_is_None_code x_l) ()) ())
         (fn x_m =>
           (fn () =>
             (if x_m then get_trail_wl_code x_l
               else get_stats_code x_l)))))))))))
        ()
    end)
    x;

end; (*struct SAT_Solver*)
