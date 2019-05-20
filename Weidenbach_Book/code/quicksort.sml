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

structure IsaQuicksort : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  val nat_of_integer : IntInf.int -> nat
  val partition_between_code :
    nat -> nat -> nat array * nat -> (unit -> ((nat array * nat) * nat))
  val full_quicksort_code : nat array * nat -> (unit -> (nat array * nat))
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

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype num = One | Bit0 of num | Bit1 of num;

fun integer_of_nat (Nat x) = x;

fun nth A_ a n = (fn () => Array.sub (a, IntInf.toInt (integer_of_nat n)));

fun upd A_ i x a =
  (fn () =>
    let
      val _ =
        (fn () => Array.update (a, IntInf.toInt (integer_of_nat i), x)) ();
    in
      a
    end);

fun apsnd f (x, y) = (x, f y);

fun fst (x1, x2) = x1;

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

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun arl_get A_ = (fn (a, _) => nth A_ a);

fun choose_pivot3_impl_code x =
  (fn ai => fn bia => fn bi =>
    let
      val x_b =
        plus_nat bia
          (divide_nat (minus_nat bi bia) (nat_of_integer (2 : IntInf.int)));
    in
      (fn () =>
        let
          val x_d = arl_get heap_nat ai bia ();
          val x_f = arl_get heap_nat ai x_b ();
          val x_h = arl_get heap_nat ai bi ();
        in
          (if less_nat x_d x_f andalso less_nat x_f x_h orelse
                less_nat x_h x_f andalso less_nat x_f x_d
            then x_b
            else (if less_nat x_d x_h andalso less_nat x_h x_f orelse
                       less_nat x_f x_h andalso less_nat x_h x_d
                   then bi else bia))
        end)
    end)
    x;

val one_nat : nat = Nat (1 : IntInf.int);

fun arl_set A_ =
  (fn (a, n) => fn i => fn x => fn () => let
   val aa = upd A_ i x a ();
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

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun imp_for i u f s =
  (if less_eq_nat u i then (fn () => s)
    else (fn () => let
                     val x = f i s ();
                   in
                     imp_for (plus_nat i one_nat) u f x ()
                   end));

fun partition_between_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = choose_pivot3_impl_code bi ai bia ();
      val x_a = arl_swap heap_nat bi xa bia ();
      val x_b = arl_get heap_nat x_a bia ();
      val a =
        imp_for ai bia
          (fn xe => fn (a1, a2) =>
            (fn f_ => fn () => f_ ((arl_get heap_nat a2 xe) ()) ())
              (fn xb =>
                (if less_nat xb x_b
                  then (fn f_ => fn () => f_ ((arl_swap heap_nat a2 a1 xe) ())
                         ())
                         (fn x_h => (fn () => (plus_nat a1 one_nat, x_h)))
                  else (fn () => (a1, a2)))))
          (ai, x_a) ();
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

fun quicksort_code_0 x =
  let
    val (a1, (a1a, a2a)) = x;
  in
    (if less_eq_nat a1a a1 then (fn () => a2a)
      else (fn () =>
             let
               val a = partition_between_code a1 a1a a2a ();
             in
               let
                 val (a1b, a2b) = a;
               in
                 (fn f_ => fn () => f_
                   ((quicksort_code_0 (a1, (minus_nat a2b one_nat, a1b))) ())
                   ())
                   (fn x_c =>
                     quicksort_code_0 (plus_nat a2b one_nat, (a1a, x_c)))
               end
                 ()
             end))
  end;

fun quicksort_code x =
  (fn ai => fn bia => fn bi => quicksort_code_0 (ai, (bia, bi))) x;

fun arl_length A_ = (fn (_, a) => (fn () => a));

val zero_nat : nat = Nat (0 : IntInf.int);

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

fun arl_is_empty A_ = (fn (_, n) => (fn () => (equal_nat n zero_nat)));

fun full_quicksort_code x =
  (fn xi => fn () =>
    let
      val xa = arl_is_empty heap_nat xi ();
    in
      (if xa then (fn () => xi)
        else (fn f_ => fn () => f_ ((arl_length heap_nat xi) ()) ())
               (fn xb => quicksort_code zero_nat (minus_nat xb one_nat) xi))
        ()
    end)
    x;

end; (*struct IsaQuicksort*)
