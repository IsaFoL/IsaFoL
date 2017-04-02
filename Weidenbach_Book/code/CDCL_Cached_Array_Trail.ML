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


    fun array_blit src si dst di len = 
      ArraySlice.copy {
        di=di,
        src = ArraySlice.slice (src,si,SOME len),
        dst=dst}

    fun array_nth_oo v a i () = Array.sub(a,i) handle Subscript => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,i,x); a) handle Subscript => f ()

    

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
  val cdcl_twl_stgy_prog_wl_D_code :
    Word32.word list ->
      ((Word32.word * nat option) list *
        ((bool option) array * (Word32.word array * Word32.word))) *
        (((Word32.word array) array * nat) *
          (nat *
            ((Word32.word array * nat) option *
              ((Word32.word list) list *
                ((Word32.word list) list *
                  (Word32.word list * (nat array * nat) array)))))) ->
        (unit ->
          (((Word32.word * nat option) list *
             ((bool option) array * (Word32.word array * Word32.word))) *
            (((Word32.word array) array * nat) *
              (nat *
                ((Word32.word array * nat) option *
                  ((Word32.word list) list *
                    ((Word32.word list) list *
                      (Word32.word list * (nat array * nat) array))))))))
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

val zero_uint32 = {zero = (Word32.fromInt 0)} : Word32.word zero;

val default_uint32a : Word32.word = (Word32.fromInt 0);

val default_uint32 = {default = default_uint32a} : Word32.word default;

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_uint32 = {minus = (fn a => fn b => Word32.- (a, b))} :
  Word32.word minus;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_uint32 =
  {less_eq = (fn a => fn b => Word32.<= (a, b)),
    less = (fn a => fn b => Word32.< (a, b))}
  : Word32.word ord;

fun typerep_proda A_ B_ t =
  Typerep ("Product_Type.prod", [typerep A_ Type, typerep B_ Type]);

fun countable_prod A_ B_ = {} : ('a * 'b) countable;

fun typerep_prod A_ B_ = {typerep = typerep_proda A_ B_} : ('a * 'b) typerep;

fun heap_prod A_ B_ =
  {countable_heap = countable_prod (countable_heap A_) (countable_heap B_),
    typerep_heap = typerep_prod (typerep_heap A_) (typerep_heap B_)}
  : ('a * 'b) heap;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun eq A_ a b = equal A_ a b;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun len A_ a = (fn () => let
                           val i = (fn () => Array.length a) ();
                         in
                           nat_of_integer i
                         end);

fun integer_of_nat (Nat x) = x;

fun new A_ = (fn a => fn b => (fn () => Array.array (a, b))) o integer_of_nat;

fun nth A_ a n = (fn () => Array.sub (a, integer_of_nat n));

fun upd A_ i x a =
  (fn () => let
              val _ = (fn () => Array.update (a, integer_of_nat i, x)) ();
            in
              a
            end);

fun null [] = true
  | null (x :: xs) = false;

fun hd (x21 :: x22) = x21;

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun is_none (SOME x) = false
  | is_none NONE = true;

fun blit A_ src si dst di len =
  (fn () => 
    array_blit src (integer_of_nat
                     si) dst (integer_of_nat di) (integer_of_nat len));

fun the (SOME x2) = x2;

fun op_list_hd x = hd x;

fun op_list_tl x = tl x;

fun nat_of_uint32 x =
  nat_of_integer (IntInf.fromLarge (Word32.toLargeInt x) : IntInf.int);

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

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

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

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

fun arl_get A_ = (fn (a, _) => nth A_ a);

fun nth_aa A_ xs i j =
  (fn () =>
    let
      val x = nth (heap_prod (heap_array (typerep_heap A_)) heap_nat) xs i ();
      val xa = arl_get A_ x j ();
    in
      xa
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

fun nth_rl A_ xs n =
  (fn () => let
              val x = arl_get (heap_array (typerep_heap A_)) xs n ();
            in
              array_copy A_ x ()
            end);

fun arl_set A_ =
  (fn (a, n) => fn i => fn x => fn () => let
   val aa = upd A_ i x a ();
 in
   (aa, n)
 end);

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun imp_for i u f s =
  (if less_eq_nat u i then (fn () => s)
    else (fn () => let
                     val x = f i s ();
                   in
                     imp_for (plus_nat i one_nat) u f x ()
                   end));

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun arl_last A_ = (fn (a, n) => nth A_ a (minus_nat n one_nat));

fun last_aa A_ xs i =
  (fn () =>
    let
      val x = nth (heap_prod (heap_array (typerep_heap A_)) heap_nat) xs i ();
    in
      arl_last A_ x ()
    end);

fun nth_raa A_ xs i j =
  (fn () => let
              val x = arl_get (heap_array (typerep_heap A_)) xs i ();
              val xa = nth A_ x j ();
            in
              xa
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

fun arl_copy A_ = (fn (a, n) => fn () => let
   val aa = array_copy A_ a ();
 in
   (aa, n)
 end);

fun arl_swap A_ =
  (fn ai => fn bia => fn bi => fn () => let
  val x = arl_get A_ ai bia ();
  val x_a = arl_get A_ ai bi ();
  val x_b = arl_set A_ ai bia x_a ();
in
  arl_set A_ x_b bi x ()
end);

val initial_capacity : nat = nat_of_integer (16 : IntInf.int);

fun arl_empty (A1_, A2_) B_ =
  (fn () => let
              val a = new A2_ initial_capacity (default A1_) ();
            in
              (a, zero B_)
            end);

fun op_list_prepend x = (fn a => x :: a);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun arl_length A_ = (fn (_, a) => (fn () => a));

fun length_aa A_ xs i =
  (fn () =>
    let
      val x = nth (heap_prod (heap_array (typerep_heap A_)) heap_nat) xs i ();
    in
      arl_length A_ x ()
    end);

fun update_aa A_ a i j y =
  (fn () =>
    let
      val x = nth (heap_prod (heap_array (typerep_heap A_)) heap_nat) a i ();
      val aa = arl_set A_ x j y ();
    in
      upd (heap_prod (heap_array (typerep_heap A_)) heap_nat) i aa a ()
    end);

fun length_ra A_ xs = arl_length (heap_array (typerep_heap A_)) xs;

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

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

fun op_list_is_empty x = null x;

fun length_raa A_ xs i =
  (fn () => let
              val x = arl_get (heap_array (typerep_heap A_)) xs i ();
            in
              len A_ x ()
            end);

fun is_Nil a = (case a of [] => true | _ :: _ => false);

val minimum_capacity : nat = nat_of_integer (16 : IntInf.int);

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

fun is_None a = (case a of NONE => true | SOME _ => false);

fun arl_is_empty A_ = (fn (_, n) => (fn () => (equal_nat n zero_nata)));

fun heap_WHILET b f s =
  (fn () =>
    let
      val bv = b s ();
    in
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s))
        ()
    end);

fun append_el_aa (A1_, A2_) =
  (fn a => fn i => fn x => fn () =>
    let
      val j = nth (heap_prod (heap_array (typerep_heap A2_)) heap_nat) a i ();
      val aa = arl_append (A1_, A2_) j x ();
    in
      upd (heap_prod (heap_array (typerep_heap A2_)) heap_nat) i aa a ()
    end);

fun uint32_safe_minus (A1_, A2_, A3_) m n =
  (if less A3_ m n then zero A2_ else minus A1_ m n);

fun set_butlast_aa A_ a i =
  (fn () =>
    let
      val x = nth (heap_prod (heap_array (typerep_heap A_)) heap_nat) a i ();
      val aa = arl_butlast A_ x ();
    in
      upd (heap_prod (heap_array (typerep_heap A_)) heap_nat) i aa a ()
    end);

fun arl_of_array_raa A_ xs = (fn () => let
 val n = len A_ xs ();
                                       in
 (xs, n)
                                       end);

fun array_of_arl_raa A_ = (fn (a, b) => array_shrink A_ a b);

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

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun shiftr_uint32 x n =
  (if less_nat n (nat_of_integer (32 : IntInf.int))
    then Uint32.shiftr x (integer_of_nat n) else (Word32.fromInt 0));

fun decided l = (l, NONE);

fun propagated l c = (l, SOME c);

fun get_level_code x =
  (fn ai => fn bi =>
    let
      val (_, (_, (a1b, _))) = ai;
    in
      nth heap_uint32 a1b (nat_of_uint32 (shiftr_uint32 bi one_nat))
    end)
    x;

fun is_in_arl_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        heap_WHILET
          (fn s =>
            (fn f_ => fn () => f_ ((arl_length heap_uint32 bi) ()) ())
              (fn xa =>
                (if less_nat s xa
                  then (fn f_ => fn () => f_ ((arl_get heap_uint32 bi s) ()) ())
                         (fn xb => (fn () => (not ((xb : Word32.word) = ai))))
                  else (fn () => false))))
          (fn s => (fn () => (plus_nat s one_nat))) zero_nata ();
      val x_a = arl_length heap_uint32 bi ();
    in
      less_nat xa x_a
    end)
    x;

fun find_first_eq_code x =
  (fn ai => fn bi =>
    heap_WHILET
      (fn s => fn () =>
        let
          val xa = arl_length heap_uint32 bi ();
        in
          (if less_nat s xa
            then (fn f_ => fn () => f_ ((arl_get heap_uint32 bi s) ()) ())
                   (fn xb => (fn () => (not ((xb : Word32.word) = ai))))
            else (fn () => false))
            ()
        end)
      (fn s => (fn () => (plus_nat s one_nat))) zero_nata)
    x;

fun remove1_wl_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = find_first_eq_code ai bi ();
      val x_a = arl_length heap_uint32 bi ();
    in
      (if equal_nat xa x_a then (fn () => bi)
        else (fn f_ => fn () => f_
               ((arl_swap heap_uint32 bi xa (minus_nat x_a one_nat)) ()) ())
               (arl_butlast heap_uint32))
        ()
    end)
    x;

fun is_decided_wl_code x = (fn xi => (fn () => (is_None (snd xi)))) x;

fun tl_trail_tr_code x =
  (fn (a1, (a1a, (a1b, a2b))) => fn () =>
    let
      val xa =
        upd (heap_option heap_bool)
          (nat_of_uint32 (shiftr_uint32 (fst (op_list_hd a1)) one_nat)) NONE a1a
          ();
      val xaa =
        upd heap_uint32
          (nat_of_uint32 (shiftr_uint32 (fst (op_list_hd a1)) one_nat))
          (Word32.fromInt 0) a1b ();
      val xb = is_decided_wl_code (op_list_hd a1) ();
    in
      (op_list_tl a1,
        (xa, (xaa, (if xb
                     then uint32_safe_minus
                            (minus_uint32, zero_uint32, ord_uint32) a2b
                            (Word32.fromInt 1)
                     else a2b))))
    end)
    x;

fun valued_trail_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, _))) = ai;
    in
      (fn () =>
        let
          val xa =
            nth (heap_option heap_bool) a1a
              (nat_of_uint32 (shiftr_uint32 bi one_nat)) ();
        in
          (case xa of NONE => NONE
            | SOME x_a =>
              (if (((Word32.andb (bi,
                      (Word32.fromInt 1))) : Word32.word) = (Word32.fromInt 0))
                then SOME x_a else SOME (not x_a)))
        end)
    end)
    x;

fun maximum_level_remove_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = arl_length heap_uint32 bia ();
      val xb =
        imp_for zero_nata xa
          (fn xb => fn (a1, a2) =>
            (fn f_ => fn () => f_ ((arl_get heap_uint32 bia xb) ()) ())
              (fn xc =>
                (if ((xc : Word32.word) = bi) andalso not a1
                  then (fn () => (true, a2))
                  else (fn f_ => fn () => f_ ((arl_get heap_uint32 bia xb) ())
                         ())
                         (fn xd =>
                           (fn f_ => fn () => f_ ((get_level_code ai xd) ()) ())
                             (fn xe =>
                               (fn () => (a1, max ord_uint32 xe a2)))))))
          (false, (Word32.fromInt 0)) ();
    in
      snd xb
    end)
    x;

fun find_lit_of_max_level_wl_imp_code x =
  (fn ai => fn _ => fn _ => fn bie => fn _ => fn _ => fn _ => fn _ => fn bi =>
    fn () =>
    let
      val xa =
        maximum_level_remove_code ai bie (Word32.xorb (bi, (Word32.fromInt 1)))
          ();
      val xb =
        heap_WHILET
          (fn s =>
            (fn f_ => fn () => f_ ((arl_get heap_uint32 bie s) ()) ())
              (fn xaa =>
                (fn f_ => fn () => f_ ((arl_get heap_uint32 bie s) ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_ ((get_level_code ai xb) ()) ())
                      (fn xba =>
                        (fn () =>
                          (if not ((xaa : Word32.word) = (Word32.xorb (bi,
                   (Word32.fromInt 1))))
                            then not ((xba : Word32.word) = xa) else true))))))
          (fn s => (fn () => (plus_nat s one_nat))) zero_nata ();
    in
      arl_get heap_uint32 bie xb ()
    end)
    x;

fun cons_trail_Propagated_tr_code x =
  (fn ai => fn bia => fn (a1, (a1a, (a1b, a2b))) => fn () =>
    let
      val xa =
        upd (heap_option heap_bool) (nat_of_uint32 (shiftr_uint32 ai one_nat))
          (SOME (((Word32.andb (ai,
                    (Word32.fromInt 1))) : Word32.word) = (Word32.fromInt 0)))
          a1a ();
      val xaa =
        upd heap_uint32 (nat_of_uint32 (shiftr_uint32 ai one_nat)) a2b a1b ();
    in
      (op_list_prepend (propagated ai bia) a1, (xa, (xaa, a2b)))
    end)
    x;

fun remove1_and_add_first_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = find_first_eq_code ai bi ();
      val x_b = find_first_eq_code bia bi ();
      val x_d = arl_swap heap_uint32 bi zero_nata xa ();
    in
      arl_swap heap_uint32 x_d one_nat
        (if equal_nat x_b zero_nata then xa else x_b) ()
    end)
    x;

fun find_decomp_wl_imp_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa =
        maximum_level_remove_code ai bia (Word32.xorb (bi, (Word32.fromInt 1)))
          ();
      val a =
        heap_WHILET (fn (a1, _) => (fn () => (Word32.< (xa, a1))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((((fn a => (fn () => a)) o hd o fst) a2) ())
              ())
              (fn xb =>
                (fn f_ => fn () => f_ ((is_decided_wl_code xb) ()) ())
                  (fn x_e =>
                    (if x_e
                      then (fn f_ => fn () => f_ ((tl_trail_tr_code a2) ()) ())
                             (fn x_g =>
                               (fn () =>
                                 (uint32_safe_minus
                                    (minus_uint32, zero_uint32, ord_uint32) a1
                                    (Word32.fromInt 1),
                                   x_g)))
                      else (fn f_ => fn () => f_ ((tl_trail_tr_code a2) ()) ())
                             (fn x_f => (fn () => (a1, x_f)))))))
          (let
             val (_, (_, (_, k))) = ai;
           in
             k
           end,
            ai)
          ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun find_decomp_wl_imp_codea x =
  (fn ai => fn _ => fn _ => fn bie => fn _ => fn _ => fn _ => fn _ =>
    find_decomp_wl_imp_code ai bie)
    x;

fun single_of_mset_imp_code x = (fn xi => arl_get heap_uint32 xi zero_nata) x;

fun backtrack_wl_D_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) => fn () =>
    let
      val xa = ((fn a => (fn () => a)) o hd o fst) a1 ();
    in
      let
        val x_a = fst xa;
        val x_c = the a1c;
      in
        (fn f_ => fn () => f_
          ((find_decomp_wl_imp_codea a1 a1a a1b x_c a1d a1e a1f a2f x_a) ()) ())
          (fn x_e =>
            (fn f_ => fn () => f_ ((arl_length heap_uint32 x_c) ()) ())
              (fn xb =>
                (if less_nat one_nat xb
                  then (fn f_ => fn () => f_
                         ((find_lit_of_max_level_wl_imp_code x_e a1a a1b x_c a1d
                            a1e a1f a2f x_a)
                         ()) ())
                         (fn x_g =>
                           (fn f_ => fn () => f_
                             ((remove1_and_add_first_code
                                (Word32.xorb (x_a, (Word32.fromInt 1))) x_g x_c)
                             ()) ())
                             (fn x_j =>
                               (fn f_ => fn () => f_
                                 ((length_ra heap_uint32 a1a) ()) ())
                                 (fn xc =>
                                   (fn f_ => fn () => f_
                                     ((append_el_aa (default_nat, heap_nat) a2f
(nat_of_uint32 x_g) xc)
                                     ()) ())
                                     (fn x_k =>
                                       (fn f_ => fn () => f_
 ((length_ra heap_uint32 a1a) ()) ())
 (fn xd =>
   (fn f_ => fn () => f_
     ((append_el_aa (default_nat, heap_nat) x_k
        (nat_of_uint32 (Word32.xorb (x_a, (Word32.fromInt 1)))) xd)
     ()) ())
     (fn x_m =>
       (fn f_ => fn () => f_ ((length_ra heap_uint32 a1a) ()) ())
         (fn xe =>
           (fn f_ => fn () => f_
             ((cons_trail_Propagated_tr_code
                (Word32.xorb (x_a, (Word32.fromInt 1))) xe x_e)
             ()) ())
             (fn x_o =>
               (fn f_ => fn () => f_ ((array_of_arl_raa heap_uint32 x_j) ()) ())
                 (fn xf =>
                   (fn f_ => fn () => f_
                     ((arrayO_raa_append (default_uint32, heap_uint32) a1a xf)
                     ()) ())
                     (fn xg =>
                       (fn () =>
                         (x_o, (xg, (a1b, (NONE,
    (a1d, (a1e, ([x_a], x_m))))))))))))))))))
                  else (fn f_ => fn () => f_ ((single_of_mset_imp_code x_c) ())
                         ())
                         (fn x_g =>
                           (fn f_ => fn () => f_
                             ((cons_trail_Propagated_tr_code
                                (Word32.xorb (x_a, (Word32.fromInt 1)))
                                zero_nata x_e)
                             ()) ())
                             (fn x_h =>
                               (fn () =>
                                 (x_h, (a1a,
 (a1b, (NONE, (a1d, ([x_g] :: a1e, ([x_a], a2f)))))))))))))
      end
        ()
    end)
    x;

fun find_unwatched_code x =
  (fn ai => fn bia => fn bi =>
    heap_WHILET
      (fn (a1, a2) => fn () => let
                                 val xa = length_raa heap_uint32 bia bi ();
                               in
                                 is_none a1 andalso less_nat a2 xa
                               end)
      (fn (_, a2) => fn () =>
        let
          val xa = nth_raa heap_uint32 bia bi a2 ();
          val x_a = valued_trail_code ai xa ();
        in
          (case x_a of NONE => (SOME false, a2) | SOME true => (SOME true, a2)
            | SOME false => (NONE, plus_nat a2 one_nat))
        end)
      (NONE, nat_of_integer (2 : IntInf.int)))
    x;

fun find_unassigned_lit_wl_D_code n_0 =
  (fn (a1, (_, (_, (_, (_, (_, (_, _))))))) => fn () =>
    let
      val x =
        heap_WHILET
          (fn (a1g, a2g) =>
            (fn () => (is_None a1g andalso not (op_list_is_empty a2g))))
          (fn (_, a2g) =>
            (fn f_ => fn () => f_ ((valued_trail_code a1 (op_list_hd a2g)) ())
              ())
              (fn x =>
                (fn () =>
                  ((if is_None x then SOME (op_list_hd a2g) else NONE),
                    op_list_tl a2g))))
          (NONE, n_0) ();
    in
      fst x
    end);

fun cons_trail_Decided_tr_code x =
  (fn ai => fn (a1, (a1a, (a1b, a2b))) => fn () =>
    let
      val xa =
        upd (heap_option heap_bool) (nat_of_uint32 (shiftr_uint32 ai one_nat))
          (SOME (((Word32.andb (ai,
                    (Word32.fromInt 1))) : Word32.word) = (Word32.fromInt 0)))
          a1a ();
      val xaa =
        upd heap_uint32 (nat_of_uint32 (shiftr_uint32 ai one_nat))
          (Word32.+ (a2b, (Word32.fromInt 1))) a1b ();
    in
      (op_list_prepend (decided ai) a1,
        (xa, (xaa, Word32.+ (a2b, (Word32.fromInt 1)))))
    end)
    x;

fun decide_wl_or_skip_D_code n_0 =
  (fn xi => fn () =>
    let
      val x = find_unassigned_lit_wl_D_code n_0 xi ();
    in
      (if not (is_None x)
        then let
               val (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (_, a2f))))))) = xi;
               val x_c = the x;
             in
               (fn f_ => fn () => f_ ((cons_trail_Decided_tr_code x_c a1) ())
                 ())
                 (fn xa =>
                   (fn () =>
                     (false,
                       (xa, (a1a, (a1b, (a1c,
  (a1d, (a1e, ([Word32.xorb (x_c, (Word32.fromInt 1))], a2f))))))))))
             end
        else (fn () => (true, xi)))
        ()
    end);

fun delete_index_and_swap_aa A_ xs i j =
  (fn () => let
              val x = last_aa A_ xs i ();
              val xsa = update_aa A_ xs i j x ();
            in
              set_butlast_aa A_ xsa i ()
            end);

fun is_decided_hd_trail_wll_code x =
  (fn (a1, (_, (_, (_, (_, (_, (_, _))))))) => fn () =>
    let
      val xa = ((fn a => (fn () => a)) o hd o fst) a1 ();
    in
      is_decided_wl_code xa ()
    end)
    x;

fun get_conflict_wll_is_Nil_code x =
  (fn (_, (_, (_, (a1c, (_, (_, (_, _))))))) =>
    (if is_None a1c then (fn () => false)
      else (arl_is_empty heap_uint32 o the) a1c))
    x;

fun union_mset_list_fold_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = arl_copy heap_uint32 ai ();
      val xaa = arl_length heap_uint32 bi ();
    in
      imp_for zero_nata xaa
        (fn xb => fn sigma =>
          (fn f_ => fn () => f_ ((arl_get heap_uint32 bi xb) ()) ())
            (fn xab =>
              (fn f_ => fn () => f_ ((is_in_arl_code xab xa) ()) ())
                (fn x_c =>
                  (if x_c then (fn () => sigma)
                    else (fn f_ => fn () => f_ ((arl_get heap_uint32 bi xb) ())
                           ())
                           (arl_append (default_uint32, heap_uint32) sigma)))))
        ai ()
    end)
    x;

fun skip_and_resolve_loop_wl_D_code x =
  (fn xi => fn () =>
    let
      val xa = get_conflict_wll_is_Nil_code xi ();
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (if not a1
              then (fn f_ => fn () => f_ ((is_decided_hd_trail_wll_code a2) ())
                     ())
                     (fn x_b => (fn () => (not x_b)))
              else (fn () => false)))
          (fn (_, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, a2g)))))))) =>
            let
              val x_b = the a1d;
            in
              (fn f_ => fn () => f_ ((((fn a => (fn () => a)) o hd o fst) a1a)
                ()) ())
                (fn xb =>
                  let
                    val (a1h, a2h) = (fst xb, the (snd xb));
                  in
                    (fn f_ => fn () => f_
                      ((is_in_arl_code (Word32.xorb (a1h, (Word32.fromInt 1)))
                         x_b)
                      ()) ())
                      (fn xc =>
                        (if not xc
                          then (fn f_ => fn () => f_ ((tl_trail_tr_code a1a) ())
                                 ())
                                 (fn xd =>
                                   (fn () =>
                                     (false,
                                       (xd,
 (a1b, (a1c, (SOME x_b, (a1e, (a1f, (a1g, a2g))))))))))
                          else (fn f_ => fn () => f_
                                 ((maximum_level_remove_code a1a x_b
                                    (Word32.xorb (a1h, (Word32.fromInt 1))))
                                 ()) ())
                                 (fn xd =>
                                   (if ((xd : Word32.word) = let
                       val (_, (_, (_, k))) = a1a;
                     in
                       k
                     end)
                                     then (fn f_ => fn () => f_
    ((remove1_wl_code (Word32.xorb (a1h, (Word32.fromInt 1))) x_b) ()) ())
    (fn x_h =>
      (fn f_ => fn () => f_
        ((if equal_nat a2h zero_nata
           then arl_empty (default_uint32, heap_uint32) zero_nat
           else (fn f_ => fn () => f_ ((nth_rl heap_uint32 a1b a2h) ()) ())
                  (fn xe =>
                    (fn f_ => fn () => f_ ((arl_of_array_raa heap_uint32 xe) ())
                      ())
                      (remove1_wl_code a1h)))
        ()) ())
        (fn x_j =>
          (fn f_ => fn () => f_ ((union_mset_list_fold_code x_h x_j) ()) ())
            (fn x_l =>
              (fn f_ => fn () => f_ ((arl_is_empty heap_uint32 x_l) ()) ())
                (fn x_n =>
                  (fn f_ => fn () => f_ ((tl_trail_tr_code a1a) ()) ())
                    (fn xe =>
                      (fn () =>
                        (x_n, (xe, (a1b, (a1c,
   (SOME x_l, (a1e, (a1f, (a1g, a2g))))))))))))))
                                     else (fn () =>
    (true, (a1a, (a1b, (a1c, (SOME x_b, (a1e, (a1f, (a1g, a2g)))))))))))))
                  end)
            end)
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

fun get_conflict_wl_is_None_code x =
  (fn xi => (fn () => let
                        val (_, (_, (_, (a1c, (_, (_, (_, _))))))) = xi;
                      in
                        is_None a1c
                      end))
    x;

fun cdcl_twl_o_prog_wl_D_code n_0 =
  (fn xi => fn () =>
    let
      val x = get_conflict_wl_is_None_code xi ();
    in
      (if x then decide_wl_or_skip_D_code n_0 xi
        else (fn f_ => fn () => f_ ((skip_and_resolve_loop_wl_D_code xi) ()) ())
               (fn x_a =>
                 (fn f_ => fn () => f_ ((get_conflict_wll_is_Nil_code x_a) ())
                   ())
                   (fn xa =>
                     (if not xa
                       then (fn f_ => fn () => f_ ((backtrack_wl_D_code x_a) ())
                              ())
                              (fn x_c => (fn () => (false, x_c)))
                       else (fn () => (true, x_a))))))
        ()
    end);

fun hd_select_and_remove_from_literals_to_update_wl x =
  ((fn a => (fn () => a)) o
    (fn (m, (n, (u, (d, (np, (up, (q, w))))))) =>
      ((m, (n, (u, (d, (np, (up, (tl q, w))))))), hd q)))
    x;

fun unit_propagation_inner_loop_body_wl_D_code x =
  (fn ai => fn bia => fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) =>
    fn () =>
    let
      val x_a = nth_aa heap_nat a2f (nat_of_uint32 ai) bia ();
      val xa = nth_raa heap_uint32 a1a x_a zero_nata ();
    in
      let
        val x_c = (if ((xa : Word32.word) = ai) then zero_nata else one_nat);
      in
        (fn f_ => fn () => f_
          ((nth_raa heap_uint32 a1a x_a (minus_nat one_nat x_c)) ()) ())
          (fn x_f =>
            (fn f_ => fn () => f_ ((valued_trail_code a1 x_f) ()) ())
              (fn x_h =>
                (if equal_option equal_bool x_h (SOME true)
                  then (fn () =>
                         (plus_nat bia one_nat,
                           (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f)))))))))
                  else (fn f_ => fn () => f_ ((find_unwatched_code a1 a1a x_a)
                         ()) ())
                         (fn x_j =>
                           (if is_none (fst x_j)
                             then (if equal_option equal_bool x_h (SOME false)
                                    then (fn f_ => fn () => f_
   ((nth_rl heap_uint32 a1a x_a) ()) ())
   (fn xb =>
     (fn f_ => fn () => f_ ((arl_of_array_raa heap_uint32 xb) ()) ())
       (fn xc =>
         (fn () =>
           (plus_nat bia one_nat,
             (a1, (a1a, (a1b, (SOME xc, (a1d, (a1e, ([], a2f)))))))))))
                                    else (fn f_ => fn () => f_
   ((cons_trail_Propagated_tr_code x_f x_a a1) ()) ())
   (fn xb =>
     (fn () =>
       (plus_nat bia one_nat,
         (xb, (a1a, (a1b, (a1c, (a1d, (a1e,
(Word32.xorb (x_f, (Word32.fromInt 1)) :: a1f, a2f)))))))))))
                             else (fn f_ => fn () => f_
                                    ((nth_raa heap_uint32 a1a x_a (snd x_j)) ())
                                    ())
                                    (fn x_l =>
                                      (fn f_ => fn () => f_
((swap_aa (default_uint32, heap_uint32) a1a x_a x_c (snd x_j)) ()) ())
(fn x_n =>
  (fn f_ => fn () => f_
    ((delete_index_and_swap_aa heap_nat a2f (nat_of_uint32 ai) bia) ()) ())
    (fn x_p =>
      (fn f_ => fn () => f_
        ((append_el_aa (default_nat, heap_nat) x_p (nat_of_uint32 x_l) x_a) ())
        ())
        (fn x_r =>
          (fn () =>
            (bia, (a1, (x_n, (a1b, (a1c, (a1d, (a1e, (a1f, x_r))))))))))))))))))
      end
        ()
    end)
    x;

fun unit_propagation_inner_loop_wl_loop_D_code x =
  (fn ai => fn bi =>
    heap_WHILET
      (fn (a1, (_, (_, (_, (a1d, (_, (_, (_, a2g)))))))) => fn () =>
        let
          val xa = length_aa heap_nat a2g (nat_of_uint32 ai) ();
        in
          less_nat a1 xa andalso is_None a1d
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

fun literals_to_update_wll_empty x =
  ((fn a => (fn () => a)) o
    (fn (_, (_, (_, (_, (_, (_, (q, _))))))) => is_Nil q))
    x;

fun unit_propagation_outer_loop_wl_D_code x =
  heap_WHILET (fn s => fn () => let
                                  val xa = literals_to_update_wll_empty s ();
                                in
                                  not xa
                                end)
    (fn s => fn () =>
      let
        val a = hd_select_and_remove_from_literals_to_update_wl s ();
      in
        let
          val (a1, a2) = a;
        in
          unit_propagation_inner_loop_wl_D_code a2 a1
        end
          ()
      end)
    x;

fun cdcl_twl_stgy_prog_wl_D_code n_0 =
  (fn xi => fn () =>
    let
      val a =
        heap_WHILET (fn (a1, _) => (fn () => (not a1)))
          (fn (_, a2) =>
            (fn f_ => fn () => f_ ((unit_propagation_outer_loop_wl_D_code a2)
              ()) ())
              (cdcl_twl_o_prog_wl_D_code n_0))
          (false, xi) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end);

end; (*struct SAT_Solver*)
