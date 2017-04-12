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


  (* Locally patched version  *)
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
  datatype int = Int_of_integer of IntInf.int
  val integer_of_int : int -> IntInf.int
  type ('a, 'b) hashtable
  val sAT_wl_code : (nat list) list -> (unit -> bool)
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

datatype typerepa = Typerep of string * typerepa list;

datatype num = One | Bit0 of num | Bit1 of num;

datatype char = Zero_char | Char of num;

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

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun def_hashmap_size_nat x = (fn _ => nat_of_integer (16 : IntInf.int)) x;

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a itself -> nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size : 'a hashable -> 'a itself -> nat;

datatype int = Int_of_integer of IntInf.int;

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun integer_of_int (Int_of_integer k) = k;

fun uint32_of_int i = Word32.fromLargeInt (IntInf.toLarge (integer_of_int i));

fun hashcode_nat n = uint32_of_int (int_of_nat n);

val hashable_nat =
  {hashcode = hashcode_nat, def_hashmap_size = def_hashmap_size_nat} :
  nat hashable;

fun equal_boola p true = p
  | equal_boola p false = not p
  | equal_boola true p = p
  | equal_boola false p = not p;

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

fun typerep_proda A_ B_ t =
  Typerep ("Product_Type.prod", [typerep A_ Type, typerep B_ Type]);

fun countable_prod A_ B_ = {} : ('a * 'b) countable;

fun typerep_prod A_ B_ = {typerep = typerep_proda A_ B_} : ('a * 'b) typerep;

fun heap_prod A_ B_ =
  {countable_heap = countable_prod (countable_heap A_) (countable_heap B_),
    typerep_heap = typerep_prod (typerep_heap A_) (typerep_heap B_)}
  : ('a * 'b) heap;

fun typerep_unita t = Typerep ("Product_Type.unit", []);

val countable_unit = {} : unit countable;

val typerep_unit = {typerep = typerep_unita} : unit typerep;

val heap_unit = {countable_heap = countable_unit, typerep_heap = typerep_unit} :
  unit heap;

datatype ('a, 'b) hashtable = HashTable of (('a * 'b) list) array * nat;

fun eq A_ a b = equal A_ a b;

fun nat k = Nat (max ord_integer (0 : IntInf.int) (integer_of_int k));

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

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun null [] = true
  | null (x :: xs) = false;

fun hd (x21 :: x22) = x21;

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun replicate n x =
  (if equal_nata n zero_nata then []
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
  (if equal_nata n zero_nata then (fn () => dst)
    else (fn () =>
           let
             val l =
               nth (heap_list (heap_prod A3_ B_)) (the_array src)
                 (minus_nat n one_nat) ();
             val x = ht_insls (A1_, A2_, A3_) B_ l dst ();
           in
             ht_copy (A1_, A2_, A3_) B_ (minus_nat n one_nat) src x ()
           end));

fun shiftr1 n =
  (nat_of_integer(IntInf.~>> (integer_of_nat(n),
    Word.fromLargeInt (integer_of_nat(one_nat)))));

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
                 (fn f_ => fn () => f_ ((blit A_ a zero_nata aa zero_nata l) ())
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

fun array_copy A_ a =
  (fn () =>
    let
      val l = len A_ a ();
    in
      (if equal_nata l zero_nata then (fn () => Array.fromList [])
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
      (if equal_nata l s then (fn () => a)
        else (if equal_nata l zero_nata then (fn () => Array.fromList [])
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

fun imp_for i u f s =
  (if less_eq_nat u i then (fn () => s)
    else (fn () => let
                     val x = f i s ();
                   in
                     imp_for (plus_nat i one_nat) u f x ()
                   end));

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

fun size_list x = gen_length zero_nata x;

fun op_list_length x = size_list x;

val initial_capacity : nat = nat_of_integer (16 : IntInf.int);

fun arl_empty (A1_, A2_) B_ =
  (fn () => let
              val a = new A2_ initial_capacity (default A1_) ();
            in
              (a, zero B_)
            end);

fun op_list_prepend x = (fn a => x :: a);

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

fun arl_is_empty A_ = (fn (_, n) => (fn () => (equal_nata n zero_nata)));

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

fun set_butlast_aa A_ a i =
  (fn () =>
    let
      val x = nth (heap_prod (heap_array (typerep_heap A_)) heap_nat) a i ();
      val aa = arl_butlast A_ x ();
    in
      upd (heap_prod (heap_array (typerep_heap A_)) heap_nat) i aa a ()
    end);

fun bitAND_int (Int_of_integer i) (Int_of_integer j) =
  Int_of_integer (IntInf.andb (i, j));

fun bitXOR_int (Int_of_integer i) (Int_of_integer j) =
  Int_of_integer (IntInf.xorb (i, j));

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

fun bitAND_nat i j = nat (bitAND_int (int_of_nat i) (int_of_nat j));

fun bitXOR_nat i j = nat (bitXOR_int (int_of_nat i) (int_of_nat j));

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

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

fun decided l = (l, NONE);

fun propagated l c = (l, SOME c);

fun get_level_code x =
  (fn ai => fn bi =>
    let
      val (_, (_, (a1b, _))) = ai;
    in
      nth heap_nat a1b
        ((nat_of_integer(IntInf.~>> (integer_of_nat(bi),
          Word.fromLargeInt (integer_of_nat(one_nat))))))
    end)
    x;

fun is_in_arl_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        heap_WHILET
          (fn s =>
            (fn f_ => fn () => f_ ((arl_length heap_nat bi) ()) ())
              (fn xa =>
                (if less_nat s xa
                  then (fn f_ => fn () => f_ ((arl_get heap_nat bi s) ()) ())
                         (fn xb => (fn () => (not (equal_nata xb ai))))
                  else (fn () => false))))
          (fn s => (fn () => (plus_nat s one_nat))) zero_nata ();
      val x_a = arl_length heap_nat bi ();
    in
      less_nat xa x_a
    end)
    x;

fun find_first_eq_code x =
  (fn ai => fn bi =>
    heap_WHILET
      (fn s => fn () =>
        let
          val xa = arl_length heap_nat bi ();
        in
          (if less_nat s xa
            then (fn f_ => fn () => f_ ((arl_get heap_nat bi s) ()) ())
                   (fn xb => (fn () => (not (equal_nata xb ai))))
            else (fn () => false))
            ()
        end)
      (fn s => (fn () => (plus_nat s one_nat))) zero_nata)
    x;

fun remove1_wl_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = find_first_eq_code ai bi ();
      val x_a = arl_length heap_nat bi ();
    in
      (if equal_nata xa x_a then (fn () => bi)
        else (fn f_ => fn () => f_
               ((arl_swap heap_nat bi xa (minus_nat x_a one_nat)) ()) ())
               (arl_butlast heap_nat))
        ()
    end)
    x;

val extract_lits_clss_imp_empty_assn :
  (unit -> ((nat, unit) hashtable * nat list))
  = (fn () => let
                val x = hs_new (hashable_nat, heap_nat) ();
              in
                (x, [])
              end);

fun nat_lit_lits_init_assn_assn_prepend x =
  (fn ai => fn (a1, a2) => fn () =>
    let
      val xa =
        hs_ins (equal_nat, hashable_nat, heap_nat)
          ((nat_of_integer(IntInf.~>> (integer_of_nat(ai),
            Word.fromLargeInt (integer_of_nat(one_nat))))))
          a1 ();
    in
      (xa, op_list_prepend ai a2)
    end)
    x;

fun nat_lit_lits_init_assn_assn_in x =
  (fn ai => fn (a1, _) => hs_memb (equal_nat, hashable_nat, heap_nat) ai a1) x;

fun extract_lits_cls_imp x =
  (fn ai =>
    imp_nfoldli ai (fn _ => (fn () => true))
      (fn xa => fn sigma => fn () =>
        let
          val x_a =
            nat_lit_lits_init_assn_assn_in
              ((nat_of_integer(IntInf.~>> (integer_of_nat(xa),
                Word.fromLargeInt (integer_of_nat(one_nat))))))
              sigma ();
        in
          (if x_a then (fn () => sigma)
            else nat_lit_lits_init_assn_assn_prepend (bitXOR_nat xa one_nat)
                   sigma)
            ()
        end))
    x;

fun extract_lits_clss_imp x =
  (fn ai => imp_nfoldli ai (fn _ => (fn () => true)) extract_lits_cls_imp) x;

fun extract_lits_clss_imp_list_assn x =
  (fn ai => fn bi => fn () => let
                                val xa = extract_lits_clss_imp ai bi ();
                              in
                                snd xa
                              end)
    x;

fun get_conflict_wl_is_None_code x =
  (fn xi => (fn () => let
                        val (_, (_, (_, (a1c, (_, (_, (_, _))))))) = xi;
                      in
                        is_None a1c
                      end))
    x;

fun hd_select_and_remove_from_literals_to_update_wl x =
  ((fn a => (fn () => a)) o
    (fn (m, (n, (u, (d, (np, (up, (q, w))))))) =>
      ((m, (n, (u, (d, (np, (up, (tl q, w))))))), hd q)))
    x;

fun cons_trail_Propagated_tr_code x =
  (fn ai => fn bia => fn (a1, (a1a, (a1b, a2b))) => fn () =>
    let
      val xa =
        upd (heap_option heap_bool)
          ((nat_of_integer(IntInf.~>> (integer_of_nat(ai),
            Word.fromLargeInt (integer_of_nat(one_nat))))))
          (SOME (equal_nata (bitAND_nat ai one_nat) zero_nata)) a1a ();
      val xaa =
        upd heap_nat
          ((nat_of_integer(IntInf.~>> (integer_of_nat(ai),
            Word.fromLargeInt (integer_of_nat(one_nat))))))
          a2b a1b ();
    in
      (op_list_prepend (propagated ai bia) a1, (xa, (xaa, a2b)))
    end)
    x;

fun delete_index_and_swap_aa A_ xs i j =
  (fn () => let
              val x = last_aa A_ xs i ();
              val xsa = update_aa A_ xs i j x ();
            in
              set_butlast_aa A_ xsa i ()
            end);

fun valued_trail_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, _))) = ai;
    in
      (fn () =>
        let
          val xa =
            nth (heap_option heap_bool) a1a
              ((nat_of_integer(IntInf.~>> (integer_of_nat(bi),
                Word.fromLargeInt (integer_of_nat(one_nat))))))
              ();
        in
          (case xa of NONE => NONE
            | SOME x_a =>
              (if equal_nata (bitAND_nat bi one_nat) zero_nata then SOME x_a
                else SOME (not x_a)))
        end)
    end)
    x;

fun find_unwatched_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((length_raa heap_nat bia bi) ()) ())
              (fn xa => (fn () => (is_None a1 andalso less_nat a2 xa))))
          (fn (_, a2) =>
            (fn f_ => fn () => f_ ((nth_raa heap_nat bia bi a2) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_ ((valued_trail_code ai xa) ()) ())
                  (fn x_a =>
                    (fn () =>
                      (case x_a of NONE => (SOME a2, a2)
                        | SOME true => (SOME a2, a2)
                        | SOME false => (NONE, plus_nat a2 one_nat))))))
          (NONE, nat_of_integer (2 : IntInf.int)) ();
    in
      fst xa
    end)
    x;

fun unit_propagation_inner_loop_body_wl_D_code x =
  (fn ai => fn bia => fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) =>
    fn () =>
    let
      val x_a = nth_aa heap_nat a2f ai bia ();
      val xa = nth_raa heap_nat a1a x_a zero_nata ();
    in
      let
        val x_c = (if equal_nata xa ai then zero_nata else one_nat);
      in
        (fn f_ => fn () => f_
          ((nth_raa heap_nat a1a x_a (minus_nat one_nat x_c)) ()) ())
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
                           (if is_None x_j
                             then (if equal_option equal_bool x_h (SOME false)
                                    then (fn f_ => fn () => f_
   ((nth_rl heap_nat a1a x_a) ()) ())
   (fn xb =>
     (fn f_ => fn () => f_ ((arl_of_array_raa heap_nat xb) ()) ())
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
(bitXOR_nat x_f one_nat :: a1f, a2f)))))))))))
                             else (fn f_ => fn () => f_
                                    ((nth_raa heap_nat a1a x_a (the x_j)) ())
                                    ())
                                    (fn x_l =>
                                      (fn f_ => fn () => f_
((swap_aa (default_nat, heap_nat) a1a x_a x_c (the x_j)) ()) ())
(fn x_n =>
  (fn f_ => fn () => f_ ((delete_index_and_swap_aa heap_nat a2f ai bia) ()) ())
    (fn x_p =>
      (fn f_ => fn () => f_ ((append_el_aa (default_nat, heap_nat) x_p x_l x_a)
        ()) ())
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
          val xa = length_aa heap_nat a2g ai ();
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

fun is_decided_wl_code x = (fn xi => (fn () => (is_None (snd xi)))) x;

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
      else (arl_is_empty heap_nat o the) a1c))
    x;

fun union_mset_list_fold_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = arl_copy heap_nat ai ();
      val xaa = arl_length heap_nat bi ();
    in
      imp_for zero_nata xaa
        (fn xb => fn sigma =>
          (fn f_ => fn () => f_ ((arl_get heap_nat bi xb) ()) ())
            (fn xab =>
              (fn f_ => fn () => f_ ((is_in_arl_code xab xa) ()) ())
                (fn x_c =>
                  (if x_c then (fn () => sigma)
                    else (fn f_ => fn () => f_ ((arl_get heap_nat bi xb) ()) ())
                           (arl_append (default_nat, heap_nat) sigma)))))
        ai ()
    end)
    x;

fun maximum_level_remove_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = arl_length heap_nat bia ();
      val xb =
        imp_for zero_nata xa
          (fn xb => fn (a1, a2) =>
            (fn f_ => fn () => f_ ((arl_get heap_nat bia xb) ()) ())
              (fn xc =>
                (if equal_nata xc bi andalso not a1 then (fn () => (true, a2))
                  else (fn f_ => fn () => f_ ((arl_get heap_nat bia xb) ()) ())
                         (fn xd =>
                           (fn f_ => fn () => f_ ((get_level_code ai xd) ()) ())
                             (fn xe => (fn () => (a1, max ord_nat xe a2)))))))
          (false, zero_nata) ();
    in
      snd xb
    end)
    x;

fun tl_trail_tr_code x =
  (fn (a1, (a1a, (a1b, a2b))) => fn () =>
    let
      val xa =
        upd (heap_option heap_bool)
          ((nat_of_integer(IntInf.~>> (integer_of_nat(fst (op_list_hd a1)),
            Word.fromLargeInt (integer_of_nat(one_nat))))))
          NONE a1a ();
      val xaa =
        upd heap_nat
          ((nat_of_integer(IntInf.~>> (integer_of_nat(fst (op_list_hd a1)),
            Word.fromLargeInt (integer_of_nat(one_nat))))))
          zero_nata a1b ();
      val xb = is_decided_wl_code (op_list_hd a1) ();
    in
      (op_list_tl a1, (xa, (xaa, (if xb then minus_nat a2b one_nat else a2b))))
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
                      ((is_in_arl_code (bitXOR_nat a1h one_nat) x_b) ()) ())
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
                                    (bitXOR_nat a1h one_nat))
                                 ()) ())
                                 (fn xd =>
                                   (if equal_nata xd
 let
   val (_, (_, (_, k))) = a1a;
 in
   k
 end
                                     then (fn f_ => fn () => f_
    ((remove1_wl_code (bitXOR_nat a1h one_nat) x_b) ()) ())
    (fn x_h =>
      (fn f_ => fn () => f_
        ((if equal_nata a2h zero_nata
           then arl_empty (default_nat, heap_nat) zero_nat
           else (fn f_ => fn () => f_ ((nth_rl heap_nat a1b a2h) ()) ())
                  (fn xe =>
                    (fn f_ => fn () => f_ ((arl_of_array_raa heap_nat xe) ())
                      ())
                      (remove1_wl_code a1h)))
        ()) ())
        (fn x_j =>
          (fn f_ => fn () => f_ ((union_mset_list_fold_code x_h x_j) ()) ())
            (fn x_l =>
              (fn f_ => fn () => f_ ((arl_is_empty heap_nat x_l) ()) ())
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
        upd (heap_option heap_bool)
          ((nat_of_integer(IntInf.~>> (integer_of_nat(ai),
            Word.fromLargeInt (integer_of_nat(one_nat))))))
          (SOME (equal_nata (bitAND_nat ai one_nat) zero_nata)) a1a ();
      val xaa =
        upd heap_nat
          ((nat_of_integer(IntInf.~>> (integer_of_nat(ai),
            Word.fromLargeInt (integer_of_nat(one_nat))))))
          (plus_nat a2b one_nat) a1b ();
    in
      (op_list_prepend (decided ai) a1, (xa, (xaa, plus_nat a2b one_nat)))
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
  (a1d, (a1e, ([bitXOR_nat x_c one_nat], a2f))))))))))
             end
        else (fn () => (true, xi)))
        ()
    end);

fun find_lit_of_max_level_wl_imp_code x =
  (fn ai => fn _ => fn _ => fn bie => fn _ => fn _ => fn _ => fn _ => fn bi =>
    fn () =>
    let
      val xa = maximum_level_remove_code ai bie (bitXOR_nat bi one_nat) ();
      val xb =
        heap_WHILET
          (fn s =>
            (fn f_ => fn () => f_ ((arl_get heap_nat bie s) ()) ())
              (fn xaa =>
                (fn f_ => fn () => f_ ((arl_get heap_nat bie s) ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_ ((get_level_code ai xb) ()) ())
                      (fn xba =>
                        (fn () =>
                          (if not (equal_nata xaa (bitXOR_nat bi one_nat))
                            then not (equal_nata xba xa) else true))))))
          (fn s => (fn () => (plus_nat s one_nat))) zero_nata ();
    in
      arl_get heap_nat bie xb ()
    end)
    x;

fun remove1_and_add_first_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = find_first_eq_code ai bi ();
      val x_b = find_first_eq_code bia bi ();
      val x_d = arl_swap heap_nat bi zero_nata xa ();
    in
      arl_swap heap_nat x_d one_nat
        (if equal_nata x_b zero_nata then xa else x_b) ()
    end)
    x;

fun find_decomp_wl_imp_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = maximum_level_remove_code ai bia (bitXOR_nat bi one_nat) ();
      val a =
        heap_WHILET (fn (a1, _) => (fn () => (less_nat xa a1)))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((((fn a => (fn () => a)) o hd o fst) a2) ())
              ())
              (fn xb =>
                (fn f_ => fn () => f_ ((is_decided_wl_code xb) ()) ())
                  (fn x_e =>
                    (if x_e
                      then (fn f_ => fn () => f_ ((tl_trail_tr_code a2) ()) ())
                             (fn x_g => (fn () => (minus_nat a1 one_nat, x_g)))
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

fun single_of_mset_imp_code x = (fn xi => arl_get heap_nat xi zero_nata) x;

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
            (fn f_ => fn () => f_ ((arl_length heap_nat x_c) ()) ())
              (fn xb =>
                (if less_nat one_nat xb
                  then (fn f_ => fn () => f_
                         ((find_lit_of_max_level_wl_imp_code x_e a1a a1b x_c a1d
                            a1e a1f a2f x_a)
                         ()) ())
                         (fn x_g =>
                           (fn f_ => fn () => f_
                             ((remove1_and_add_first_code
                                (bitXOR_nat x_a one_nat) x_g x_c)
                             ()) ())
                             (fn x_j =>
                               (fn f_ => fn () => f_ ((length_ra heap_nat a1a)
                                 ()) ())
                                 (fn xc =>
                                   (fn f_ => fn () => f_
                                     ((append_el_aa (default_nat, heap_nat) a2f
x_g xc)
                                     ()) ())
                                     (fn x_k =>
                                       (fn f_ => fn () => f_
 ((length_ra heap_nat a1a) ()) ())
 (fn xd =>
   (fn f_ => fn () => f_
     ((append_el_aa (default_nat, heap_nat) x_k (bitXOR_nat x_a one_nat) xd) ())
     ())
     (fn x_m =>
       (fn f_ => fn () => f_ ((length_ra heap_nat a1a) ()) ())
         (fn xe =>
           (fn f_ => fn () => f_
             ((cons_trail_Propagated_tr_code (bitXOR_nat x_a one_nat) xe x_e)
             ()) ())
             (fn x_o =>
               (fn f_ => fn () => f_ ((array_of_arl_raa heap_nat x_j) ()) ())
                 (fn xf =>
                   (fn f_ => fn () => f_
                     ((arrayO_raa_append (default_nat, heap_nat) a1a xf) ()) ())
                     (fn xg =>
                       (fn () =>
                         (x_o, (xg, (a1b, (NONE,
    (a1d, (a1e, ([x_a], x_m))))))))))))))))))
                  else (fn f_ => fn () => f_ ((single_of_mset_imp_code x_c) ())
                         ())
                         (fn x_g =>
                           (fn f_ => fn () => f_
                             ((cons_trail_Propagated_tr_code
                                (bitXOR_nat x_a one_nat) zero_nata x_e)
                             ()) ())
                             (fn x_h =>
                               (fn () =>
                                 (x_h, (a1a,
 (a1b, (NONE, (a1d, ([x_g] :: a1e, ([x_a], a2f)))))))))))))
      end
        ()
    end)
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

fun init_state_wl_D n_0 l_Ns =
  let
    val n = suc (suc (fold (max ord_nat) n_0 zero_nata));
  in
    (fn () =>
      let
        val na = arrayO_raa_empty_sz (default_nat, heap_nat) zero_nat l_Ns ();
        val e = new heap_nat zero_nata zero_nata ();
        val naa = arrayO_raa_append (default_nat, heap_nat) na e ();
        val ws = arrayO_ara_empty_sz_code (default_nat, heap_nat) n ();
        val m = new (heap_option heap_bool) (shiftr1 n) NONE ();
        val ma = new heap_nat (shiftr1 n) zero_nata ();
      in
        (([], (m, (ma, zero_nata))),
          (naa, (zero_nata, (NONE, ([], ([], ([], ws)))))))
      end)
  end;

fun init_state_wl_D_code n_0 = init_state_wl_D n_0;

fun arl_of_list_raa A_ xs =
  (fn () => let
              val x = (fn () => Array.fromList xs) ();
            in
              arl_of_array_raa A_ x ()
            end);

fun init_dt_step_wl_code x =
  (fn _ => fn bia => fn a =>
    (case a
      of (a1, (a1a, (a1b, (NONE, (a1d, (a1e, (a1f, a2f))))))) =>
        (if equal_nata (op_list_length bia) one_nat
          then let
                 val x_b = op_list_hd bia;
               in
                 (fn () =>
                   let
                     val x_d = valued_trail_code a1 x_b ();
                   in
                     (if is_None x_d
                       then (fn f_ => fn () => f_
                              ((cons_trail_Propagated_tr_code x_b zero_nata a1)
                              ()) ())
                              (fn x_g =>
                                (fn () =>
                                  (x_g, (a1a,
  (a1b, (NONE, ([x_b] :: a1d, (a1e, (bitXOR_nat x_b one_nat :: a1f, a2f)))))))))
                       else (if equal_option equal_bool x_d (SOME true)
                              then (fn () =>
                                     (a1, (a1a,
    (a1b, (NONE, ([x_b] :: a1d, (a1e, (a1f, a2f))))))))
                              else (fn f_ => fn () => f_
                                     ((arl_of_list_raa heap_nat bia) ()) ())
                                     (fn xa =>
                                       (fn () =>
 (a1, (a1a, (a1b, (SOME xa, ([x_b] :: a1d, (a1e, ([], a2f)))))))))))
                       ()
                   end)
               end
          else (fn () =>
                 let
                   val x_b = length_ra heap_nat a1a ();
                   val x_d =
                     append_el_aa (default_nat, heap_nat) a2f (op_list_hd bia)
                       x_b ();
                   val x_f =
                     append_el_aa (default_nat, heap_nat) x_d
                       (op_list_hd (op_list_tl bia)) x_b ();
                   val xa = (fn () => Array.fromList bia) ();
                   val xb = arrayO_raa_append (default_nat, heap_nat) a1a xa ();
                 in
                   (a1, (xb, (x_b, (NONE, (a1d, (a1e, (a1f, x_f)))))))
                 end))
      | (a1, (a1a, (a1b, (SOME x_a, (a1d, (a1e, (_, a2f))))))) =>
        (if equal_nata (op_list_length bia) one_nat
          then (fn () =>
                 (a1, (a1a, (a1b, (SOME x_a,
                                    ([op_list_hd bia] :: a1d,
                                      (a1e, ([], a2f))))))))
          else (fn () =>
                 let
                   val x_c = length_ra heap_nat a1a ();
                   val x_e =
                     append_el_aa (default_nat, heap_nat) a2f (op_list_hd bia)
                       x_c ();
                   val x_g =
                     append_el_aa (default_nat, heap_nat) x_e
                       (op_list_hd (op_list_tl bia)) x_c ();
                   val xa = (fn () => Array.fromList bia) ();
                   val xb = arrayO_raa_append (default_nat, heap_nat) a1a xa ();
                 in
                   (a1, (xb, (x_c, (SOME x_a, (a1d, (a1e, ([], x_g)))))))
                 end))))
    x;

fun init_dt_wl_code x =
  (fn ai => fn bia =>
    imp_nfoldli bia (fn _ => (fn () => true)) (init_dt_step_wl_code ai))
    x;

fun sAT_wl_code x =
  (fn xi => fn () =>
    let
      val xa = extract_lits_clss_imp_empty_assn ();
      val x_b = extract_lits_clss_imp_list_assn xi xa ();
      val x_d = init_state_wl_D_code x_b (op_list_length xi) ();
      val x_f = init_dt_wl_code x_b xi x_d ();
      val x_g = get_conflict_wl_is_None_code x_f ();
    in
      (if x_g
        then (fn f_ => fn () => f_ ((cdcl_twl_stgy_prog_wl_D_code x_b x_f) ())
               ())
               get_conflict_wl_is_None_code
        else (fn () => false))
        ()
    end)
    x;

end; (*struct SAT_Solver*)
