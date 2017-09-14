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

structure SAT_Solver : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  val nat_of_integer : IntInf.int -> nat
  type 'a al_vmtf_atm
  datatype int = Int_of_integer of IntInf.int
  type ('a, 'b) hashtable
  val integer_of_int : int -> IntInf.int
  val uint32_of_nat : nat -> Word32.word
  val sAT_wl_code :
    (Word32.word list) list -> (unit -> ((Word32.word list) option))
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

fun typerep_unita t = Typerep ("Product_Type.unit", []);

val countable_unit = {} : unit countable;

val typerep_unit = {typerep = typerep_unita} : unit typerep;

val heap_unit = {countable_heap = countable_unit, typerep_heap = typerep_unit} :
  unit heap;

datatype 'a al_vmtf_atm = L_vmtf_ATM of nat * 'a option * 'a option;

fun typerep_al_vmtf_atma A_ t =
  Typerep ("CDCL_Two_Watched_Literals_VMTF.al_vmtf_atm", [typerep A_ Type]);

fun countable_al_vmtf_atm A_ = {} : 'a al_vmtf_atm countable;

fun typerep_al_vmtf_atm A_ = {typerep = typerep_al_vmtf_atma A_} :
  'a al_vmtf_atm typerep;

fun heap_al_vmtf_atm A_ =
  {countable_heap = countable_al_vmtf_atm A_,
    typerep_heap = typerep_al_vmtf_atm (typerep_heap A_)}
  : 'a al_vmtf_atm heap;

datatype int = Int_of_integer of IntInf.int;

datatype ('a, 'b) hashtable = HashTable of (('a * 'b) list) array * nat;

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

fun is_none (SOME x) = false
  | is_none NONE = true;

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

fun integer_of_int (Int_of_integer k) = k;

fun uint32_of_int i = Word32.fromLargeInt (IntInf.toLarge (integer_of_int i));

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun uint32_of_nat x = (uint32_of_int o int_of_nat) x;

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

fun hs_memb (A1_, A2_, A3_) x s =
  (fn () => let
              val r = ht_lookup (A1_, A2_, A3_) heap_unit x s ();
            in
              (case r of NONE => false | SOME _ => true)
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

fun imp_for i u f s =
  (if less_eq_nat u i then (fn () => s)
    else (fn () => let
                     val x = f i s ();
                   in
                     imp_for (plus_nat i one_nat) u f x ()
                   end));

fun fast_minus A_ m n = minus A_ m n;

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

fun op_list_concat x = (fn a => x @ a);

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

fun fast_minus_uint32 x = fast_minus minus_uint32 x;

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

fun imp_option_eq eq a b =
  (case (a, b) of (NONE, NONE) => (fn () => true)
    | (NONE, SOME _) => (fn () => false) | (SOME _, NONE) => (fn () => false)
    | (SOME aa, SOME ba) => eq aa ba);

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

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun shiftr_uint32 x n =
  (if less_nat n (nat_of_integer (32 : IntInf.int))
    then Uint32.shiftr x (integer_of_nat n) else (Word32.fromInt 0));

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

fun emptied_arl x = (fn (a, _) => (a, zero_nata)) x;

fun stamp (L_vmtf_ATM (x1, x2, x3)) = x1;

fun get_next (L_vmtf_ATM (x1, x2, x3)) = x3;

fun get_prev (L_vmtf_ATM (x1, x2, x3)) = x2;

fun decided l = (l, NONE);

fun propagated l c = (l, SOME c);

fun get_level_code x =
  (fn ai => fn bi =>
    let
      val ((_, (_, (a1c, _))), (_, _)) = ai;
    in
      nth heap_uint32 a1c (nat_of_uint32 (shiftr_uint32 bi one_nat))
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

fun vmtf_enqueue_code x =
  (fn ai => fn (a1, (a1a, (a1b, _))) =>
    (case a1b
      of NONE =>
        (fn () =>
          let
            val xa =
              upd (heap_al_vmtf_atm heap_uint32) (nat_of_uint32 ai)
                (L_vmtf_ATM (a1a, a1b, NONE)) a1 ();
          in
            (xa, (plus_nat a1a one_nat, (SOME ai, SOME ai)))
          end)
      | SOME xa =>
        (fn () =>
          let
            val xaa =
              nth (heap_al_vmtf_atm heap_uint32) a1 (nat_of_uint32 xa) ();
            val xb =
              nth (heap_al_vmtf_atm heap_uint32) a1 (nat_of_uint32 xa) ();
            val xc =
              upd (heap_al_vmtf_atm heap_uint32) (nat_of_uint32 ai)
                (L_vmtf_ATM (plus_nat a1a one_nat, NONE, SOME xa)) a1 ();
            val x_b =
              upd (heap_al_vmtf_atm heap_uint32) (nat_of_uint32 xa)
                (L_vmtf_ATM (stamp xaa, SOME ai, get_next xb)) xc ();
          in
            (x_b, (plus_nat a1a one_nat, (SOME ai, SOME ai)))
          end)))
    x;

fun l_vmtf_dequeue_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = nth (heap_al_vmtf_atm heap_uint32) bi (nat_of_uint32 ai) ();
      val x_a =
        (case get_prev xa of NONE => (fn () => bi)
          | SOME x_b =>
            (fn f_ => fn () => f_
              ((nth (heap_al_vmtf_atm heap_uint32) bi (nat_of_uint32 x_b)) ())
              ())
              (fn xaa =>
                (fn f_ => fn () => f_
                  ((nth (heap_al_vmtf_atm heap_uint32) bi (nat_of_uint32 x_b))
                  ()) ())
                  (fn xb =>
                    upd (heap_al_vmtf_atm heap_uint32) (nat_of_uint32 x_b)
                      (L_vmtf_ATM (stamp xaa, get_prev xb, get_next xa)) bi)))
          ();
      val x_b =
        (case get_next xa of NONE => (fn () => x_a)
          | SOME x_c =>
            (fn f_ => fn () => f_
              ((nth (heap_al_vmtf_atm heap_uint32) x_a (nat_of_uint32 x_c)) ())
              ())
              (fn xaa =>
                (fn f_ => fn () => f_
                  ((nth (heap_al_vmtf_atm heap_uint32) x_a (nat_of_uint32 x_c))
                  ()) ())
                  (fn xb =>
                    upd (heap_al_vmtf_atm heap_uint32) (nat_of_uint32 x_c)
                      (L_vmtf_ATM (stamp xaa, get_prev xa, get_next xb)) x_a)))
          ();
      val xb = nth (heap_al_vmtf_atm heap_uint32) x_b (nat_of_uint32 ai) ();
    in
      upd (heap_al_vmtf_atm heap_uint32) (nat_of_uint32 ai)
        (L_vmtf_ATM (stamp xb, NONE, NONE)) x_b ()
    end)
    x;

fun vmtf_dequeue_code x =
  (fn ai => fn (a1, (a1a, (a1b, a2b))) => fn () =>
    let
      val xa =
        imp_option_eq (fn va => fn vb => (fn () => ((va : Word32.word) = vb)))
          a1b (SOME ai) ();
      val xb =
        (if xa
          then (fn f_ => fn () => f_
                 ((nth (heap_al_vmtf_atm heap_uint32) a1 (nat_of_uint32 ai)) ())
                 ())
                 (fn x_a => (fn () => (get_next x_a)))
          else (fn () => a1b))
          ();
      val xaa =
        imp_option_eq (fn va => fn vb => (fn () => ((va : Word32.word) = vb)))
          a2b (SOME ai) ();
      val x_a =
        (if xaa
          then (fn f_ => fn () => f_
                 ((nth (heap_al_vmtf_atm heap_uint32) a1 (nat_of_uint32 ai)) ())
                 ())
                 (fn x_b => (fn () => (get_next x_b)))
          else (fn () => a2b))
          ();
      val x_b = l_vmtf_dequeue_code ai a1 ();
    in
      (x_b, (a1a, (xb, x_a)))
    end)
    x;

fun vmtf_en_dequeue_code x =
  (fn ai => fn bi => fn () => let
                                val xa = vmtf_dequeue_code ai bi ();
                              in
                                vmtf_enqueue_code ai xa ()
                              end)
    x;

fun insert_sort_inner_nth_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((arl_get heap_uint32 a2 bi) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((nth (heap_al_vmtf_atm heap_uint32) ai (nat_of_uint32 xa))
                  ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_ ((arl_get heap_uint32 a2 a1) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          ((nth (heap_al_vmtf_atm heap_uint32) ai
                             (nat_of_uint32 xaa))
                          ()) ())
                          (fn xab =>
                            (fn () =>
                              (less_nat zero_nata a1 andalso
                                less_nat (stamp xb) (stamp xab))))))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((arl_swap heap_uint32 a2 a1 (minus_nat a1 one_nat)) ()) ())
              (fn x_a => (fn () => (minus_nat a1 one_nat, x_a))))
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

fun trail_dump_code x =
  (fn (a1, (a1a, a2a)) => fn () => let
                                     val xa = vmtf_flush_code a1a ();
                                   in
                                     (a1, (xa, a2a))
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

val extract_atms_clss_imp_empty_assn :
  (unit -> ((Word32.word, unit) hashtable * Word32.word list))
  = (fn () => let
                val x = hs_new (hashable_uint32, heap_uint32) ();
              in
                (x, [])
              end);

fun nat_lit_lits_init_assn_assn_prepend x =
  (fn ai => fn (a1, a2) => fn () =>
    let
      val xa = hs_ins (equal_uint32, hashable_uint32, heap_uint32) ai a1 ();
    in
      (xa, op_list_prepend ai a2)
    end)
    x;

fun nat_lit_lits_init_assn_assn_in x =
  (fn ai => fn (a1, _) =>
    hs_memb (equal_uint32, hashable_uint32, heap_uint32) ai a1)
    x;

fun extract_atms_cls_imp x =
  (fn ai =>
    imp_nfoldli ai (fn _ => (fn () => true))
      (fn xa => fn sigma => fn () =>
        let
          val x_a =
            nat_lit_lits_init_assn_assn_in (shiftr_uint32 xa one_nat) sigma ();
        in
          (if x_a then (fn () => sigma)
            else nat_lit_lits_init_assn_assn_prepend (shiftr_uint32 xa one_nat)
                   sigma)
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

fun extract_model_of_state_code x =
  (fn xi =>
    imp_nfoldli let
                  val (a, b) = xi;
                in
                  let
                    val (aa, ba) = a;
                  in
                    let
                      val (m, _) = aa;
                    in
                      (fn _ => fn _ => m)
                    end
                      ba
                  end
                    b
                end
      (fn _ => (fn () => true))
      (fn xc => fn sigma =>
        (fn () => (op_list_concat sigma (op_list_prepend (fst xc) []))))
      [])
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
  (fn ai => fn bia => fn (a1, (a1a, a2a)) => fn () =>
    let
      val xa =
        let
          val (a1b, (a1c, (a1d, a2d))) = a1;
        in
          (fn f_ => fn () => f_
            ((upd (heap_option heap_bool)
               (nat_of_uint32 (shiftr_uint32 ai one_nat))
               (SOME (((Word32.andb (ai,
                         (Word32.fromInt 1))) : Word32.word) = (Word32.fromInt 0)))
               a1c)
            ()) ())
            (fn xa =>
              (fn f_ => fn () => f_
                ((upd heap_uint32 (nat_of_uint32 (shiftr_uint32 ai one_nat)) a2d
                   a1d)
                ()) ())
                (fn xaa =>
                  (fn () =>
                    (op_list_prepend (propagated ai bia) a1b,
                      (xa, (xaa, a2d))))))
        end
          ();
    in
      (xa, (a1a, a2a))
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
      val ((_, (a1b, (_, _))), (_, _)) = ai;
    in
      (fn () =>
        let
          val xa =
            nth (heap_option heap_bool) a1b
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

fun find_unwatched_code x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((length_raa heap_uint32 bia bi) ()) ())
              (fn xa => (fn () => (is_None a1 andalso less_nat a2 xa))))
          (fn (_, a2) =>
            (fn f_ => fn () => f_ ((nth_raa heap_uint32 bia bi a2) ()) ())
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
                         (fn a =>
                           (case a
                             of NONE =>
                               (if equal_option equal_bool x_h (SOME false)
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
      (xb, (a1a, (a1b, (a1c, (a1d, (a1e, (Word32.xorb (x_f,
    (Word32.fromInt 1)) ::
    a1f,
   a2f)))))))))))
                             | SOME x_k =>
                               (fn f_ => fn () => f_
                                 ((nth_raa heap_uint32 a1a x_a x_k) ()) ())
                                 (fn x_l =>
                                   (fn f_ => fn () => f_
                                     ((swap_aa (default_uint32, heap_uint32) a1a
x_a x_c x_k)
                                     ()) ())
                                     (fn x_n =>
                                       (fn f_ => fn () => f_
 ((delete_index_and_swap_aa heap_nat a2f (nat_of_uint32 ai) bia) ()) ())
 (fn x_p =>
   (fn f_ => fn () => f_
     ((append_el_aa (default_nat, heap_nat) x_p (nat_of_uint32 x_l) x_a) ()) ())
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

fun is_decided_wl_code x = (fn xi => (fn () => (is_None (snd xi)))) x;

fun is_decided_hd_trail_wll_code x =
  (fn (a1, (_, (_, (_, (_, (_, (_, _))))))) => fn () =>
    let
      val xa = ((fn a => (fn () => a)) o hd o fst o fst) a1 ();
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

fun tl_trail_tr_dump_code x =
  (fn ((a1a, (a1b, (a1c, a2c))), (((a1f, (a1g, (a1h, a2h))), a2e), a2d)) =>
    let
      val x_a = op_list_hd a1a;
      val x_b = shiftr_uint32 (fst x_a) one_nat;
    in
      (fn () =>
        let
          val xa = upd (heap_option heap_bool) (nat_of_uint32 x_b) NONE a1b ();
          val xaa =
            upd heap_uint32 (nat_of_uint32 x_b) (Word32.fromInt 0) a1c ();
          val xb = is_decided_wl_code x_a ();
          val xc =
            (if is_None a2h then (fn () => true)
              else (fn f_ => fn () => f_
                     ((nth (heap_al_vmtf_atm heap_uint32) a1f
                        (nat_of_uint32 (the a2h)))
                     ()) ())
                     (fn xc =>
                       (fn f_ => fn () => f_
                         ((nth (heap_al_vmtf_atm heap_uint32) a1f
                            (nat_of_uint32 x_b))
                         ()) ())
                         (fn xab =>
                           (fn () => (less_nat (stamp xc) (stamp xab))))))
              ();
          val xca =
            let
              val ((a1j, (a1k, (a1l, a2l))), a2i) =
                (if xc then ((a1f, (a1g, (a1h, SOME x_b))), a2e)
                  else ((a1f, (a1g, (a1h, a2h))), a2e));
            in
              (fn f_ => fn () => f_
                ((arl_append (default_uint32, heap_uint32) a2i x_b) ()) ())
                (fn x_f => (fn () => ((a1j, (a1k, (a1l, a2l))), x_f)))
            end
              ();
          val xd =
            upd heap_bool (nat_of_uint32 x_b)
              (((Word32.andb (fst x_a,
                  (Word32.fromInt 1))) : Word32.word) = (Word32.fromInt 0))
              a2d ();
        in
          ((op_list_tl a1a,
             (xa, (xaa, (if xb then fast_minus_uint32 a2c (Word32.fromInt 1)
                          else a2c)))),
            (xca, xd))
        end)
    end)
    x;

fun tl_trail_tr_code x =
  (fn ((a1a, (a1b, (a1c, a2c))), (((a1f, (a1g, (a1h, a2h))), a2e), a2d)) =>
    let
      val x_a = op_list_hd a1a;
      val x_b = shiftr_uint32 (fst x_a) one_nat;
    in
      (fn () =>
        let
          val xa = upd (heap_option heap_bool) (nat_of_uint32 x_b) NONE a1b ();
          val xaa =
            upd heap_uint32 (nat_of_uint32 x_b) (Word32.fromInt 0) a1c ();
          val xb = is_decided_wl_code x_a ();
          val xc =
            (if is_None a2h then (fn () => true)
              else (fn f_ => fn () => f_
                     ((nth (heap_al_vmtf_atm heap_uint32) a1f
                        (nat_of_uint32 (the a2h)))
                     ()) ())
                     (fn xc =>
                       (fn f_ => fn () => f_
                         ((nth (heap_al_vmtf_atm heap_uint32) a1f
                            (nat_of_uint32 x_b))
                         ()) ())
                         (fn xab =>
                           (fn () => (less_nat (stamp xc) (stamp xab))))))
              ();
        in
          ((op_list_tl a1a,
             (xa, (xaa, (if xb then fast_minus_uint32 a2c (Word32.fromInt 1)
                          else a2c)))),
            ((if xc then ((a1f, (a1g, (a1h, SOME x_b))), a2e)
               else ((a1f, (a1g, (a1h, a2h))), a2e)),
              a2d))
        end)
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
              (fn f_ => fn () => f_
                ((((fn a => (fn () => a)) o hd o fst o fst) a1a) ()) ())
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
                       val (a, b) = a1a;
                     in
                       let
                         val (_, (_, (_, k))) = a;
                       in
                         (fn _ => k)
                       end
                         b
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
                  (fn f_ => fn () => f_ ((tl_trail_tr_dump_code a1a) ()) ())
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

fun defined_atm_code x =
  (fn ai => fn bi =>
    let
      val (_, (a1a, (_, _))) = ai;
    in
      (fn () =>
        let
          val xa = nth (heap_option heap_bool) a1a (nat_of_uint32 bi) ();
        in
          not (is_none xa)
        end)
    end)
    x;

fun vmtf_find_next_undef_code x =
  (fn ai => fn bi =>
    let
      val ((a1a, a), _) = ai;
      val (_, aa) = a;
      val (_, ab) = aa;
    in
      heap_WHILET
        (fn s =>
          (if not (is_None s) then defined_atm_code bi (the s)
            else (fn () => false)))
        (fn s =>
          let
            val xa = the s;
          in
            (fn () =>
              let
                val xaa = defined_atm_code bi xa ();
              in
                (if not xaa then (fn () => (SOME xa))
                  else (fn f_ => fn () => f_
                         ((nth (heap_al_vmtf_atm heap_uint32) a1a
                            (nat_of_uint32 xa))
                         ()) ())
                         (fn x_c => (fn () => (get_next x_c))))
                  ()
              end)
          end)
        ab
    end)
    x;

fun update_next_search l =
  (fn (a, b) => let
                  val (aa, (m, (lst, _))) = a;
                in
                  (fn ba => ((aa, (m, (lst, l))), ba))
                end
                  b);

fun vmtf_find_next_undef_upd_code x =
  (fn (a1, (a1a, a2a)) => fn () =>
    let
      val xa = vmtf_find_next_undef_code a1a a1 ();
    in
      ((a1, (update_next_search xa a1a, a2a)), xa)
    end)
    x;

fun lit_of_found_atm_D_code x =
  (fn ai => fn bi =>
    let
      val (_, (_, a2a)) = ai;
    in
      (case bi of NONE => (fn () => NONE)
        | SOME xa =>
          (fn () =>
            let
              val x_a = nth heap_bool a2a (nat_of_uint32 xa) ();
            in
              (if x_a
                then SOME (Word32.* (Word32.fromLargeInt (IntInf.toLarge (2 : IntInf.int)), xa))
                else SOME (Word32.+ (Word32.* (Word32.fromLargeInt (IntInf.toLarge (2 : IntInf.int)), xa), (Word32.fromInt 1))))
            end))
    end)
    x;

fun find_unassigned_lit_wl_D_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) => fn () =>
    let
      val a = vmtf_find_next_undef_upd_code a1 ();
    in
      let
        val (a1g, a2g) = a;
      in
        (fn f_ => fn () => f_ ((lit_of_found_atm_D_code a1g a2g) ()) ())
          (fn x_a =>
            (fn () =>
              ((a1g, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))), x_a)))
      end
        ()
    end)
    x;

fun cons_trail_Decided_tr_code x =
  (fn ai => fn (a1, (a1a, a2a)) => fn () =>
    let
      val xa =
        let
          val (a1b, (a1c, (a1d, a2d))) = a1;
        in
          (fn f_ => fn () => f_
            ((upd (heap_option heap_bool)
               (nat_of_uint32 (shiftr_uint32 ai one_nat))
               (SOME (((Word32.andb (ai,
                         (Word32.fromInt 1))) : Word32.word) = (Word32.fromInt 0)))
               a1c)
            ()) ())
            (fn xa =>
              (fn f_ => fn () => f_
                ((upd heap_uint32 (nat_of_uint32 (shiftr_uint32 ai one_nat))
                   (Word32.+ (a2d, (Word32.fromInt 1))) a1d)
                ()) ())
                (fn xaa =>
                  (fn () =>
                    (op_list_prepend (decided ai) a1b,
                      (xa, (xaa, Word32.+ (a2d, (Word32.fromInt 1))))))))
        end
          ();
    in
      (xa, (a1a, a2a))
    end)
    x;

fun decide_wl_or_skip_D_code x =
  (fn xi => fn () =>
    let
      val a = find_unassigned_lit_wl_D_code xi ();
    in
      let
        val (a1, a2) = a;
      in
        (if not (is_None a2)
          then let
                 val (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (_, a2g))))))) = a1;
                 val x_c = the a2;
               in
                 (fn f_ => fn () => f_ ((cons_trail_Decided_tr_code x_c a1a) ())
                   ())
                   (fn xa =>
                     (fn () =>
                       (false,
                         (xa, (a1b, (a1c, (a1d,
    (a1e, (a1f, ([Word32.xorb (x_c, (Word32.fromInt 1))], a2g))))))))))
               end
          else (fn () => (true, a1)))
      end
        ()
    end)
    x;

fun extract_shorter_conflict_l_trivial_code x =
  (fn ai => fn _ => fn _ => fn bid => fn _ => fn _ => fn _ => fn _ =>
    let
      val xa = the bid;
    in
      (fn () =>
        let
          val xaa = arl_empty (default_uint32, heap_uint32) zero_nat ();
          val x_b =
            heap_WHILET
              (fn (a1, _) =>
                (fn f_ => fn () => f_ ((arl_length heap_uint32 xa) ()) ())
                  (fn x_c => (fn () => (less_nat a1 x_c))))
              (fn (a1, a2) =>
                (fn f_ => fn () => f_ ((arl_get heap_uint32 xa a1) ()) ())
                  (fn xab =>
                    (fn f_ => fn () => f_ ((get_level_code ai xab) ()) ())
                      (fn xac =>
                        (if less_nat zero_nata (nat_of_uint32 xac)
                          then (fn f_ => fn () => f_
                                 ((arl_get heap_uint32 xa a1) ()) ())
                                 (fn xb =>
                                   (fn f_ => fn () => f_
                                     ((arl_append (default_uint32, heap_uint32)
a2 xb)
                                     ()) ())
                                     (fn x_e =>
                                       (fn () => (plus_nat a1 one_nat, x_e))))
                          else (fn () => (plus_nat a1 one_nat, a2))))))
              (zero_nata, xaa) ();
        in
          snd x_b
        end)
    end)
    x;

fun extract_shorter_conflict_l_trivial_code_wl x =
  extract_shorter_conflict_l_trivial_code x;

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
            (fn f_ => fn () => f_
              ((((fn a => (fn () => a)) o hd o fst o fst) a2) ()) ())
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
             val (a, b) = ai;
           in
             let
               val (_, (_, (_, k))) = a;
             in
               (fn _ => k)
             end
               b
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

fun vmtf_rescore_code x =
  (fn ai => fn (a1, (a1a, a2a)) => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1b, (_, _)) =>
            (fn f_ => fn () => f_ ((len heap_uint32 ai) ()) ())
              (fn x_a => (fn () => (less_nat a1b x_a))))
          (fn (a1b, (a1c, a2c)) =>
            (fn f_ => fn () => f_
              (let
                 val ((a1e, (a1f, (a1g, a2g))), a2d) = a1c;
               in
                 (fn f_ => fn () => f_ ((nth heap_uint32 ai a1b) ()) ())
                   (fn xa =>
                     (fn f_ => fn () => f_
                       ((arl_append (default_uint32, heap_uint32) a2d
                          (shiftr_uint32 xa one_nat))
                       ()) ())
                       (fn x_b => (fn () => ((a1e, (a1f, (a1g, a2g))), x_b))))
               end
              ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_ ((nth heap_uint32 ai a1b) ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((nth heap_uint32 ai a1b) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          ((upd heap_bool
                             (nat_of_uint32 (shiftr_uint32 xa one_nat))
                             (not (((Word32.andb (xaa,
                                      (Word32.fromInt 1))) : Word32.word) = (Word32.fromInt 0)))
                             a2c)
                          ()) ())
                          (fn x_c =>
                            (fn () => (plus_nat a1b one_nat, (x_a, x_c))))))))
          (zero_nata, (a1a, a2a)) ();
    in
      let
        val (_, (a1c, a2c)) = a;
      in
        (fn () => (a1, (a1c, a2c)))
      end
        ()
    end)
    x;

fun backtrack_wl_D_code x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) => fn () =>
    let
      val xa = ((fn a => (fn () => a)) o hd o fst o fst) a1 ();
    in
      let
        val x_a = fst xa;
      in
        (fn f_ => fn () => f_
          ((extract_shorter_conflict_l_trivial_code_wl a1 a1a a1b a1c a1d a1e
             a1f a2f)
          ()) ())
          (fn x_c =>
            (fn f_ => fn () => f_
              ((find_decomp_wl_imp_codea a1 a1a a1b x_c a1d a1e a1f a2f x_a) ())
              ())
              (fn x_d =>
                (fn f_ => fn () => f_ ((arl_length heap_uint32 x_c) ()) ())
                  (fn xb =>
                    (if less_nat one_nat xb
                      then (fn f_ => fn () => f_
                             ((find_lit_of_max_level_wl_imp_code x_d a1a a1b x_c
                                a1d a1e a1f a2f x_a)
                             ()) ())
                             (fn x_f =>
                               (fn f_ => fn () => f_
                                 ((remove1_and_add_first_code
                                    (Word32.xorb (x_a, (Word32.fromInt 1))) x_f
                                    x_c)
                                 ()) ())
                                 (fn x_i =>
                                   (fn f_ => fn () => f_
                                     ((length_ra heap_uint32 a1a) ()) ())
                                     (fn xc =>
                                       (fn f_ => fn () => f_
 ((append_el_aa (default_nat, heap_nat) a2f (nat_of_uint32 x_f) xc) ()) ())
 (fn x_j =>
   (fn f_ => fn () => f_ ((length_ra heap_uint32 a1a) ()) ())
     (fn xd =>
       (fn f_ => fn () => f_
         ((append_el_aa (default_nat, heap_nat) x_j
            (nat_of_uint32 (Word32.xorb (x_a, (Word32.fromInt 1)))) xd)
         ()) ())
         (fn x_l =>
           (fn f_ => fn () => f_ ((array_of_arl_raa heap_uint32 x_i) ()) ())
             (fn x_n =>
               (fn f_ => fn () => f_ ((length_ra heap_uint32 a1a) ()) ())
                 (fn xe =>
                   (fn f_ => fn () => f_
                     ((cons_trail_Propagated_tr_code
                        (Word32.xorb (x_a, (Word32.fromInt 1))) xe x_d)
                     ()) ())
                     (fn xf =>
                       (fn f_ => fn () => f_ ((vmtf_rescore_code x_n xf) ()) ())
                         (fn xg =>
                           (fn f_ => fn () => f_ ((trail_dump_code xg) ()) ())
                             (fn x_p =>
                               (fn f_ => fn () => f_
                                 ((arrayO_raa_append
                                    (default_uint32, heap_uint32) a1a x_n)
                                 ()) ())
                                 (fn xh =>
                                   (fn () =>
                                     (x_p, (xh,
     (a1b, (NONE, (a1d, (a1e, ([x_a], x_l))))))))))))))))))))
                      else (fn f_ => fn () => f_ ((single_of_mset_imp_code x_c)
                             ()) ())
                             (fn x_f =>
                               (fn f_ => fn () => f_
                                 ((cons_trail_Propagated_tr_code
                                    (Word32.xorb (x_a, (Word32.fromInt 1)))
                                    zero_nata x_d)
                                 ()) ())
                                 (fn xc =>
                                   (fn f_ => fn () => f_ ((trail_dump_code xc)
                                     ()) ())
                                     (fn x_g =>
                                       (fn () =>
 (x_g, (a1a, (a1b, (NONE, (a1d, ([x_f] :: a1e, ([x_a], a2f)))))))))))))))
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
            (fn f_ => fn () => f_ ((unit_propagation_outer_loop_wl_D_code a2)
              ()) ())
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

fun initialise_VMTF_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa =
        new (heap_al_vmtf_atm heap_uint32) bi
          (L_vmtf_ATM (zero_nata, NONE, NONE)) ();
      val a =
        heap_WHILET
          (fn (a1, (_, (_, _))) => (fn () => (not (op_list_is_empty a1))))
          (fn (a1, (a1a, (a1b, a2b))) =>
            let
              val x_c = op_list_hd a1;
            in
              (fn f_ => fn () => f_
                ((upd (heap_al_vmtf_atm heap_uint32) (nat_of_uint32 x_c)
                   (L_vmtf_ATM (suc a1b, NONE, a2b)) a1a)
                ()) ())
                (fn xb =>
                  (fn f_ => fn () => f_
                    ((case a2b of NONE => (fn () => xb)
                       | SOME x_g =>
                         (fn f_ => fn () => f_
                           ((nth (heap_al_vmtf_atm heap_uint32) xb
                              (nat_of_uint32 x_g))
                           ()) ())
                           (fn xaa =>
                             (fn f_ => fn () => f_
                               ((nth (heap_al_vmtf_atm heap_uint32) xb
                                  (nat_of_uint32 x_g))
                               ()) ())
                               (fn xba =>
                                 upd (heap_al_vmtf_atm heap_uint32)
                                   (nat_of_uint32 x_g)
                                   (L_vmtf_ATM
                                     (stamp xaa, SOME x_c, get_next xba))
                                   xb)))
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
          (fn x_d => (fn () => ((a1a, (a1b, (a2b, a2b))), x_d)))
      end
        ()
    end)
    x;

fun init_trail_D_code x =
  (fn ai => fn bi => fn () =>
    let
      val xa = new (heap_option heap_bool) bi NONE ();
      val x_b = new heap_uint32 bi (Word32.fromInt 0) ();
      val x_d = new heap_bool bi false ();
      val x_f = initialise_VMTF_code ai bi ();
    in
      (([], (xa, (x_b, (Word32.fromInt 0)))), (x_f, x_d))
    end)
    x;

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
                          ((arrayO_ara_empty_sz_code (default_nat, heap_nat)
                             (times_nat (nat_of_integer (2 : IntInf.int)) xb))
                          ()) ())
                          (fn x_k =>
                            (fn () =>
                              (x_d, (x_i, (zero_nata,
    (NONE, ([], ([], ([], x_k)))))))))))))
      end
        ()
    end)
    x;

fun arl_of_list_raa A_ xs =
  (fn () => let
              val x = (fn () => Array.fromList xs) ();
            in
              arl_of_array_raa A_ x ()
            end);

fun init_dt_step_wl_code x =
  (fn ai => fn a =>
    (case a
      of (a1, (a1a, (a1b, (NONE, (a1d, (a1e, (a1f, a2f))))))) =>
        (if equal_nat (op_list_length ai) one_nat
          then let
                 val x_b = op_list_hd ai;
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
  (a1b, (NONE,
          ([x_b] :: a1d,
            (a1e, (Word32.xorb (x_b, (Word32.fromInt 1)) :: a1f, a2f)))))))))
                       else (if equal_option equal_bool x_d (SOME true)
                              then (fn () =>
                                     (a1, (a1a,
    (a1b, (NONE, ([x_b] :: a1d, (a1e, (a1f, a2f))))))))
                              else (fn f_ => fn () => f_
                                     ((arl_of_list_raa heap_uint32 ai) ()) ())
                                     (fn xa =>
                                       (fn () =>
 (a1, (a1a, (a1b, (SOME xa, ([x_b] :: a1d, (a1e, ([], a2f)))))))))))
                       ()
                   end)
               end
          else (fn () =>
                 let
                   val x_b = length_ra heap_uint32 a1a ();
                   val x_d =
                     append_el_aa (default_nat, heap_nat) a2f
                       (nat_of_uint32 (op_list_hd ai)) x_b ();
                   val x_f =
                     append_el_aa (default_nat, heap_nat) x_d
                       (nat_of_uint32 (op_list_hd (op_list_tl ai))) x_b ();
                   val xa = (fn () => Array.fromList ai) ();
                   val xb =
                     arrayO_raa_append (default_uint32, heap_uint32) a1a xa ();
                 in
                   (a1, (xb, (x_b, (NONE, (a1d, (a1e, (a1f, x_f)))))))
                 end))
      | (a1, (a1a, (a1b, (SOME x_a, (a1d, (a1e, (_, a2f))))))) =>
        (if equal_nat (op_list_length ai) one_nat
          then (fn () =>
                 (a1, (a1a, (a1b, (SOME x_a,
                                    ([op_list_hd ai] :: a1d,
                                      (a1e, ([], a2f))))))))
          else (fn () =>
                 let
                   val x_c = length_ra heap_uint32 a1a ();
                   val x_e =
                     append_el_aa (default_nat, heap_nat) a2f
                       (nat_of_uint32 (op_list_hd ai)) x_c ();
                   val x_g =
                     append_el_aa (default_nat, heap_nat) x_e
                       (nat_of_uint32 (op_list_hd (op_list_tl ai))) x_c ();
                   val xa = (fn () => Array.fromList ai) ();
                   val xb =
                     arrayO_raa_append (default_uint32, heap_uint32) a1a xa ();
                 in
                   (a1, (xb, (x_c, (SOME x_a, (a1d, (a1e, ([], x_g)))))))
                 end))))
    x;

fun init_dt_wl_code x =
  (fn ai => imp_nfoldli ai (fn _ => (fn () => true)) init_dt_step_wl_code) x;

fun sAT_wl_code x =
  (fn xi => fn () =>
    let
      val xa = extract_atms_clss_imp_empty_assn ();
      val x_b = extract_atms_clss_imp_list_assn xi xa ();
      val x_d = init_state_wl_D_code x_b ();
      val x_f = init_dt_wl_code xi x_d ();
      val x_g = get_conflict_wl_is_None_code x_f ();
    in
      (if x_g
        then (fn f_ => fn () => f_ ((cdcl_twl_stgy_prog_wl_D_code x_f) ()) ())
               (fn x_h =>
                 (fn f_ => fn () => f_ ((get_conflict_wl_is_None_code x_h) ())
                   ())
                   (fn x_i =>
                     (if x_i
                       then (fn f_ => fn () => f_
                              ((extract_model_of_state_code x_h) ()) ())
                              (fn x_j => (fn () => (SOME x_j)))
                       else (fn () => NONE))))
        else (fn () => NONE))
        ()
    end)
    x;

end; (*struct SAT_Solver*)
