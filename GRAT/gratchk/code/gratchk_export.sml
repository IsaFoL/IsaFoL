
structure Uint : sig
  val set_bit : Word.word -> IntInf.int -> bool -> Word.word
  val shiftl : Word.word -> IntInf.int -> Word.word
  val shiftr : Word.word -> IntInf.int -> Word.word
  val shiftr_signed : Word.word -> IntInf.int -> Word.word
  val test_bit : Word.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word.orb (x, mask)
     else Word.andb (x, Word.notb mask)
  end

fun shiftl x n =
  Word.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word.andb (x, Word.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word.fromInt 0

end; (* struct Uint *)

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


structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a array = 'a Cell Unsynchronized.ref;

fun fromList l = Unsynchronized.ref (Value (Array.fromList l));
fun array (size, v) = Unsynchronized.ref (Value (Array.array (size,v)));
fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
fun sub (Unsynchronized.ref Invalid, idx) = raise AccessedOldVersion |
    sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
    (Unsynchronized.ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      Unsynchronized.ref (Value a)
    );

fun length (Unsynchronized.ref Invalid) = raise AccessedOldVersion |
    length (Unsynchronized.ref (Value a)) = Array.length a

fun grow (aref, i, x) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    let val len=Array.length a;
        val na = Array.array (len+i,x)
    in
      aref := Invalid;
      Array.copy {src=a, dst=na, di=0};
      Unsynchronized.ref (Value na)
    end
    );

fun shrink (aref, sz) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    if sz > Array.length a then
      raise Size
    else (
      aref:=Invalid;
      Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
    )
  );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:IntInf.int) = array (IntInf.toInt n, a);

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:IntInf.int) (x:'a) = grow (a, IntInf.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:IntInf.int) = shrink (a,IntInf.toInt sz);

end;

end;

structure FArray = struct
  datatype 'a Cell = Value of 'a Array.array | Upd of (int*'a*'a Cell Unsynchronized.ref);

  type 'a array = 'a Cell Unsynchronized.ref;

  fun array (size,v) = Unsynchronized.ref (Value (Array.array (size,v)));
  fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
  fun fromList l = Unsynchronized.ref (Value (Array.fromList l));

  fun sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx) |
      sub (Unsynchronized.ref (Upd (i,v,cr)),idx) =
        if i=idx then v
        else sub (cr,idx);

  fun length (Unsynchronized.ref (Value a)) = Array.length a |
      length (Unsynchronized.ref (Upd (i,v,cr))) = length cr;

  fun realize_aux (aref, v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let
          val len = Array.length a;
          val a' = Array.array (len,v);
        in
          Array.copy {src=a, dst=a', di=0};
          Unsynchronized.ref (Value a')
        end
      ) |
      (Unsynchronized.ref (Upd (i,v,cr))) => (
        let val res=realize_aux (cr,v) in
          case res of
            (Unsynchronized.ref (Value a)) => (Array.update (a,i,v); res)
        end
      );

  fun realize aref =
    case aref of
      (Unsynchronized.ref (Value _)) => aref |
      (Unsynchronized.ref (Upd (i,v,cr))) => realize_aux(aref,v);

  fun update (aref,idx,v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let val nref=Unsynchronized.ref (Value a) in
          aref := Upd (idx,Array.sub(a,idx),nref);
          Array.update (a,idx,v);
          nref
        end
      ) |
      (Unsynchronized.ref (Upd _)) =>
        let val ra = realize_aux(aref,v) in
          case ra of
            (Unsynchronized.ref (Value a)) => Array.update (a,idx,v);
          ra
        end
      ;

  fun grow (aref, inc, x) = case aref of
    (Unsynchronized.ref (Value a)) => (
      let val len=Array.length a;
          val na = Array.array (len+inc,x)
      in
        Array.copy {src=a, dst=na, di=0};
        Unsynchronized.ref (Value na)
      end
      )
  | (Unsynchronized.ref (Upd _)) => (
    grow (realize aref, inc, x)
  );

  fun shrink (aref, sz) = case aref of
    (Unsynchronized.ref (Value a)) => (
      if sz > Array.length a then
        raise Size
      else (
        Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
      )
    ) |
    (Unsynchronized.ref (Upd _)) => (
      shrink (realize aref,sz)
    );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:IntInf.int) = array (IntInf.toInt n, a);

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:IntInf.int) (x:'a) = grow (a, IntInf.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:IntInf.int) = shrink (a,IntInf.toInt sz);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:IntInf.int) =
  sub (a,IntInf.toInt i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:IntInf.int) (e:'a) =
  update (a, IntInf.toInt i, e) handle Subscript => d ()

end;
end;





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

structure Grat_Check : sig
  datatype int = Int_of_integer of IntInf.int
  type nat
  val integer_of_nat : nat -> IntInf.int
  datatype ('a, 'b) sum = Inl of 'a | Inr of 'b
  val integer_of_int : int -> IntInf.int
  val nat_of_integer : IntInf.int -> nat
  val isl : ('a, 'b) sum -> bool
  val projl : ('a, 'b) sum -> 'a
  val projr : ('a, 'b) sum -> 'b
  val verify_sat_impl_wrapper :
    int array ->
      nat -> (unit -> ((string * (int option * nat option)), unit) sum)
  val verify_unsat_impl_wrapper :
    int array ->
      nat -> nat -> (unit -> ((string * (int option * nat option)), unit) sum)
  val verify_unsat_split_impl_wrapper :
    int array ->
      ('a -> int * 'a) ->
        nat ->
          nat ->
            nat * 'a ->
              (unit -> ((string * (int option * (nat * 'a) option)), unit) sum)
end = struct

datatype typerepa = Typerep of string * typerepa list;

datatype int = Int_of_integer of IntInf.int;

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

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun typerep_nata t = Typerep ("Nat.nat", []);

val countable_nat = {} : nat countable;

val typerep_nat = {typerep = typerep_nata} : nat typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  nat heap;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

fun typerep_lista A_ t = Typerep ("List.list", [typerep A_ Type]);

fun countable_list A_ = {} : ('a list) countable;

fun typerep_list A_ = {typerep = typerep_lista A_} : ('a list) typerep;

fun heap_list A_ =
  {countable_heap = countable_list (countable_heap A_),
    typerep_heap = typerep_list (typerep_heap A_)}
  : ('a list) heap;

fun typerep_optiona A_ t = Typerep ("Option.option", [typerep A_ Type]);

fun countable_option A_ = {} : ('a option) countable;

fun typerep_option A_ = {typerep = typerep_optiona A_} : ('a option) typerep;

fun heap_option A_ =
  {countable_heap = countable_option (countable_heap A_),
    typerep_heap = typerep_option (typerep_heap A_)}
  : ('a option) heap;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype num = One | Bit0 of num | Bit1 of num;

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

fun eq A_ a b = equal A_ a b;

fun integer_of_int (Int_of_integer k) = k;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun nat k = Nat (max ord_integer (0 : IntInf.int) (integer_of_int k));

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

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

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun hd (x21 :: x22) = x21;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if member A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun blit A_ src si dst di len =
  (fn () => 
    array_blit src (integer_of_nat
                     si) dst (integer_of_nat di) (integer_of_nat len));

fun isl (Inl x1) = true
  | isl (Inr x2) = false;

fun the (SOME x2) = x2;

fun projl (Inl x1) = x1;

fun projr (Inr x2) = x2;

fun array_get_dyn A_ dflt a i =
  (fn () => let
              val l = len A_ a ();
            in
              (if less_nat i l then nth A_ a i else (fn () => dflt)) ()
            end);

val zero_nat : nat = Nat (0 : IntInf.int);

val zero_int : int = Int_of_integer (0 : IntInf.int);

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun uminus_int k = Int_of_integer (IntInf.~ (integer_of_int k));

fun abs_int i = (if less_int i zero_int then uminus_int i else i);

fun op_lit_is_true_impl x =
  (fn ai => fn bi => fn () =>
    let
      val xa = array_get_dyn heap_nat zero_nat bi ((nat o abs_int) ai) ();
    in
      let
        val x_a = less_int zero_int ai;
      in
        (fn () =>
          (if equal_nata zero_nat xa then false
            else x_a andalso
                   equal_nata xa (nat_of_integer (2 : IntInf.int)) orelse
                   not x_a andalso
                     not (equal_nata xa (nat_of_integer (2 : IntInf.int)))))
      end
        ()
    end)
    x;

fun heap_WHILET b f s =
  (fn () =>
    let
      val bv = b s ();
    in
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s))
        ()
    end);

fun equal_int k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

fun read_clause_check_sat3 x =
  (fn ai => fn bib => fn bia => fn bi =>
    (if not (equal_nata bia bib)
      then (fn () =>
             let
               val a =
                 heap_WHILET
                   (fn a =>
                     (case a of Inl _ => (fn () => false)
                       | Inr (a1, _) =>
                         (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                           (fn xa =>
                             (fn () =>
                               (not (equal_int xa zero_int) andalso true)))))
                   (fn s =>
                     let
                       val (a1, a2) = projr s;
                     in
                       (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                         (fn x_d =>
                           let
                             val x_h = plus_nat one_nat a1;
                           in
                             (if not (equal_nata x_h bib)
                               then (fn f_ => fn () => f_
                                      ((op_lit_is_true_impl x_d bi) ()) ())
                                      (fn xa =>
(fn () => (Inr (x_h, a2 orelse xa))))
                               else (fn () =>
                                      (Inl
("Parsed beyond end", (NONE, SOME bia)))))
                           end)
                     end)
                   (Inr (bia, false)) ();
             in
               (case a of Inl x1a => (fn () => (Inl x1a))
                 | Inr x2a => (fn () => (Inr let
       val (a1, aa) = x2a;
     in
       (plus_nat one_nat a1, aa)
     end)))
                 ()
             end)
      else (fn () => (Inl ("Parsed beyond end", (NONE, SOME bia))))))
    x;

fun check_sat3 x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn a =>
            (case a of Inl _ => (fn () => false)
              | Inr (a1, _) => (fn () => (not (equal_nata a1 bia)))))
          (fn s =>
            let
              val (a1, _) = projr s;
            in
              (fn f_ => fn () => f_ ((read_clause_check_sat3 ai bia a1 bi) ())
                ())
                (fn a =>
                  (case a of Inl x1a => (fn () => (Inl x1a))
                    | Inr (a1a, a2a) =>
                      (fn () =>
                        (if a2a then Inr (a1a, ())
                          else Inl ("Clause not satisfied by given assignment",
                                     (NONE, SOME a1))))))
            end)
          (Inr (bib, ())) ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr x2a => (fn () => (Inr let
                                      val (_, b) = x2a;
                                    in
                                      b
                                    end)))
        ()
    end)
    x;

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

fun mbhd_insert A_ x l =
  (if null l then [x] else (if eq A_ x (hd l) then l else x :: l));

val creg_dflt_size : nat = nat_of_integer (16 : IntInf.int);

val creg_empty : (unit -> (((nat list) option) array)) =
  new (heap_option (heap_list heap_nat)) creg_dflt_size NONE;

val assignment_empty_impl : (unit -> (nat array)) =
  new heap_nat (nat_of_integer (16 : IntInf.int)) zero_nat;

fun op_lit_is_false_impl x =
  (fn ai => fn bi => fn () =>
    let
      val xa = array_get_dyn heap_nat zero_nat bi ((nat o abs_int) ai) ();
    in
      let
        val x_a = less_int zero_int ai;
      in
        (fn () =>
          (if equal_nata zero_nat xa then false
            else x_a andalso
                   not (equal_nata xa (nat_of_integer (2 : IntInf.int))) orelse
                   not x_a andalso
                     equal_nata xa (nat_of_integer (2 : IntInf.int))))
      end
        ()
    end)
    x;

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

fun array_set_dyn A_ dflt a i v =
  (fn () =>
    let
      val l = len A_ a ();
    in
      (if less_nat i l then upd A_ i v a
        else let
               val ns =
                 max ord_nat (times_nat (nat_of_integer (2 : IntInf.int)) l)
                   (plus_nat i one_nat);
             in
               (fn f_ => fn () => f_ ((array_grow A_ a ns dflt) ()) ())
                 (upd A_ i v)
             end)
        ()
    end);

fun assign_lit_impl x =
  (fn ai => fn bi =>
    array_set_dyn heap_nat zero_nat ai ((nat o abs_int) bi)
      (if less_int zero_int bi then nat_of_integer (2 : IntInf.int)
        else one_nat))
    x;

fun read_assignment3 x =
  (fn ai => fn bi => fn () =>
    let
      val xa = assignment_empty_impl ();
      val xaa = len heap_int ai ();
    in
      (if not (equal_nata bi xaa)
        then (fn f_ => fn () => f_
               ((heap_WHILET
                  (fn a =>
                    (case a of Inl _ => (fn () => false)
                      | Inr (_, a2) =>
                        (fn f_ => fn () => f_ ((nth heap_int ai a2) ()) ())
                          (fn xb => (fn () => (not (equal_int xb zero_int))))))
                  (fn s =>
                    let
                      val (a1, a2) = projr s;
                    in
                      (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                        (fn xb =>
                          (if not (equal_nata (plus_nat one_nat a2) xb)
                            then (fn f_ => fn () => f_ ((nth heap_int ai a2) ())
                                   ())
                                   (fn xc =>
                                     (fn f_ => fn () => f_
                                       ((op_lit_is_false_impl xc a1) ()) ())
                                       (fn xd =>
 (if not xd
   then (fn f_ => fn () => f_ ((nth heap_int ai a2) ()) ())
          (fn xe =>
            (fn f_ => fn () => f_ ((assign_lit_impl a1 xe) ()) ())
              (fn xf => (fn () => (Inr (xf, plus_nat one_nat a2)))))
   else (fn () =>
          (Inl ("Contradictory assignment",
                 (NONE, SOME (plus_nat one_nat a2))))))))
                            else (fn () =>
                                   (Inl ("Parsed beyond end", (NONE, NONE))))))
                    end)
                  (Inr (xa, bi)))
               ()) ())
               (fn a =>
                 (case a of Inl x1a => (fn () => (Inl x1a))
                   | Inr x2a => (fn () => (Inr let
         val (a1, _) = x2a;
       in
         a1
       end))))
        else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))
        ()
    end)
    x;

fun verify_sat3 x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val a = read_assignment3 ai bi ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr aa => check_sat3 ai bib bia aa)
        ()
    end)
    x;

fun at_item_end frml_end it = less_eq_nat it frml_end;

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

fun unset_var_impl x =
  (fn ai => fn bi => array_set_dyn heap_nat zero_nat bi ai zero_nat) x;

fun backtrack3 x =
  (fn ai => fn bi => imp_nfoldli bi (fn _ => (fn () => true)) unset_var_impl ai)
    x;

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

fun minus_int k l =
  Int_of_integer (IntInf.- (integer_of_int k, integer_of_int l));

fun sum_encode x =
  (case x of Inl a => times_nat (nat_of_integer (2 : IntInf.int)) a
    | Inr b => suc (times_nat (nat_of_integer (2 : IntInf.int)) b));

val one_int : int = Int_of_integer (1 : IntInf.int);

fun int_encode i =
  sum_encode
    (if less_eq_int zero_int i then Inl (nat i)
      else Inr (nat (minus_int (uminus_int i) one_int)));

fun creg_register (A1_, A2_) l cid cr =
  (fn () =>
    let
      val a =
        array_get_dyn (heap_option (heap_list A2_)) NONE cr (int_encode l) ();
    in
      (case a of NONE => (fn () => cr)
        | SOME s =>
          array_set_dyn (heap_option (heap_list A2_)) NONE cr (int_encode l)
            (SOME (mbhd_insert A1_ cid s)))
        ()
    end);

fun add_clause3 x =
  (fn ai => fn bib => fn bia => fn (a1, a2) => fn () =>
    let
      val xa = array_set_dyn heap_nat zero_nat a1 bib bia ();
      val x_b =
        heap_WHILET
          (fn (a1a, _) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1a) ()) ())
              (fn xb => (fn () => (not (equal_int xb zero_int) andalso true))))
          (fn (a1a, a2a) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1a) ()) ())
              (fn x_c =>
                (fn f_ => fn () => f_
                  ((creg_register (equal_nat, heap_nat) x_c bib a2a) ()) ())
                  (fn x_g => (fn () => (plus_nat one_nat a1a, x_g)))))
          (bia, a2) ();
    in
      (xa, let
             val (_, b) = x_b;
           in
             b
           end)
    end)
    x;

fun check_conflict_clause3 x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn a =>
            (case a of Inl _ => (fn () => false)
              | Inr (a1, _) =>
                (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                  (fn xa =>
                    (fn () => (not (equal_int xa zero_int) andalso true)))))
          (fn s =>
            let
              val (a1, _) = projr s;
            in
              (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                (fn x_c =>
                  (fn f_ => fn () => f_ ((op_lit_is_false_impl x_c bia) ()) ())
                    (fn xa =>
                      (case (if xa then Inr ()
                              else Inl ("Expected conflict clause",
 (NONE, SOME bib)))
                        of Inl x1a => (fn () => (Inl x1a))
                        | Inr x2a =>
                          (fn () => (Inr (plus_nat one_nat a1, x2a))))))
            end)
          (Inr (bi, ())) ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr x2a => (fn () => (Inr let
                                      val (_, b) = x2a;
                                    in
                                      b
                                    end)))
        ()
    end)
    x;

fun parse_check_blocked3 x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = len heap_int ai ();
    in
      (if not (equal_nata bi xa)
        then (fn f_ => fn () => f_
               ((heap_WHILET
                  (fn a =>
                    (case a of Inl _ => (fn () => false)
                      | Inr (a1, a2) =>
                        (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                          (fn xb =>
                            (fn () =>
                              (not (equal_int xb zero_int) andalso
                                let
                                  val (a1a, (_, _)) = a2;
                                in
                                  not a1a
                                end)))))
                  (fn s =>
                    let
                      val (a1, a2) = projr s;
                    in
                      (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                        (fn x_d =>
                          (fn f_ => fn () => f_
                            (let
                               val (_, (a1b, a2b)) = a2;
                             in
                               (fn f_ => fn () => f_
                                 ((op_lit_is_true_impl x_d a1b) ()) ())
                                 (fn x_h =>
                                   (if x_h then (fn () => (true, (a1b, a2b)))
                                     else (fn f_ => fn () => f_
    ((op_lit_is_false_impl x_d a1b) ()) ())
    (fn x_i =>
      (if x_i then (fn () => (false, (a1b, a2b)))
        else (fn f_ => fn () => f_ ((assign_lit_impl a1b (uminus_int x_d)) ())
               ())
               (fn xb =>
                 (fn () => (false, (xb, (nat o abs_int) x_d :: a2b))))))))
                             end
                            ()) ())
                            (fn x_h =>
                              let
                                val x_i = plus_nat one_nat a1;
                              in
                                (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                                  (fn xb =>
                                    (fn () =>
                                      (if not (equal_nata x_i xb)
then Inr (x_i, x_h) else Inl ("Parsed beyond end", (NONE, NONE)))))
                              end))
                    end)
                  (Inr (bi, (false, (bia, [])))))
               ()) ())
               (fn a =>
                 (case a of Inl x1a => (fn () => (Inl x1a))
                   | Inr x2a =>
                     (fn () =>
                       let
                         val ((a1a, (a1b, a2b)), a2) =
                           let
                             val (a1, a2) = let
      val (a1, aa) = x2a;
    in
      (plus_nat one_nat a1, aa)
    end;
                           in
                             (a2, a1)
                           end;
                       in
                         Inr (a1a, (bi, ((a1b, a2b), a2)))
                       end)))
        else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))
        ()
    end)
    x;

fun check_unit_clause3 x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn a =>
            (case a of Inl _ => (fn () => false)
              | Inr (a1, _) =>
                (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                  (fn xa =>
                    (fn () => (not (equal_int xa zero_int) andalso true)))))
          (fn s =>
            let
              val (a1, a2) = projr s;
            in
              (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                (fn x_c =>
                  (fn f_ => fn () => f_ ((op_lit_is_true_impl x_c bia) ()) ())
                    (fn xa =>
                      (if not xa
                        then (fn f_ => fn () => f_
                               ((op_lit_is_false_impl x_c bia) ()) ())
                               (fn xb =>
                                 (case (if xb then Inr a2
 else (if equal_int zero_int a2 orelse equal_int a2 x_c then Inr x_c
        else Inl ("2-undec in clause assumed to be unit", (NONE, NONE))))
                                   of Inl x1a => (fn () => (Inl x1a))
                                   | Inr x2a =>
                                     (fn () =>
                                       (Inr (plus_nat one_nat a1, x2a)))))
                        else (fn () =>
                               (Inl ("True literal in clause assumed to be unit",
                                      (NONE, NONE)))))))
            end)
          (Inr (bi, zero_int)) ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr x2a =>
          let
            val x_a = let
                        val (_, b) = x2a;
                      in
                        b
                      end;
          in
            (fn () =>
              (if not (equal_int zero_int x_a) then Inr x_a
                else Inl ("Conflict in clause assumed to be unit",
                           (NONE, NONE))))
          end)
        ()
    end)
    x;

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun resolve_id3 x =
  (fn ai => fn bi =>
    let
      val (a1, _) = ai;
    in
      (fn () =>
        let
          val xa = array_get_dyn heap_nat zero_nat a1 bi ();
        in
          (if equal_nata zero_nat xa
            then Inl ("Invalid clause id", (SOME (int_of_nat bi), NONE))
            else Inr xa)
        end)
    end)
    x;

fun apply_units3_bt x =
  (fn ai => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = len heap_int ai ();
    in
      (if not (equal_nata bi xa)
        then (fn f_ => fn () => f_
               ((heap_WHILET
                  (fn a =>
                    (case a of Inl _ => (fn () => false)
                      | Inr ((_, _), a2) =>
                        (fn f_ => fn () => f_ ((nth heap_int ai a2) ()) ())
                          (fn xb => (fn () => (not (equal_int xb zero_int))))))
                  (fn s =>
                    let
                      val ((a1a, a2a), a2) = projr s;
                    in
                      (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                        (fn xb =>
                          (if not (equal_nata a2 xb)
                            then (fn f_ => fn () => f_ ((nth heap_int ai a2) ())
                                   ())
                                   (fn xc =>
                                     (fn f_ => fn () => f_
                                       ((if less_int zero_int xc
  then (fn f_ => fn () => f_ ((nth heap_int ai a2) ()) ())
         (fn xd => (fn () => (Inr (nat xd, plus_nat one_nat a2))))
  else (fn f_ => fn () => f_ ((nth heap_int ai a2) ()) ())
         (fn xd => (fn () => (Inl ("Invalid id", (SOME xd, SOME a2))))))
                                       ()) ())
                                       (fn a =>
 (case a of Inl x1a => (fn () => (Inl x1a))
   | Inr (a1b, a2b) =>
     (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
       (fn xd =>
         (if not (equal_nata a2b xd)
           then (fn f_ => fn () => f_ ((resolve_id3 bic a1b) ()) ())
                  (fn xe =>
                    (fn f_ => fn () => f_
                      ((case xe of Inl x1a => (fn () => (Inl x1a))
                         | Inr x2aa =>
                           (fn f_ => fn () => f_
                             ((check_unit_clause3 ai a1a x2aa) ()) ())
                             (fn aa =>
                               (case aa of Inl x1a => (fn () => (Inl x1a))
                                 | Inr x2ab =>
                                   (fn f_ => fn () => f_
                                     ((assign_lit_impl a1a x2ab) ()) ())
                                     (fn xf =>
                                       (fn () =>
 (Inr (xf, (nat o abs_int) x2ab :: a2a)))))))
                      ()) ())
                      (fn aa =>
                        (case aa of Inl x1a => (fn () => (Inl x1a))
                          | Inr x2aa =>
                            (fn () => (Inr let
     val (a1c, a2c) = x2aa;
   in
     ((a1c, a2c), a2b)
   end)))))
           else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))))))
                            else (fn () =>
                                   (Inl ("Parsed beyond end", (NONE, NONE))))))
                    end)
                  (Inr ((bib, bia), bi)))
               ()) ())
               (fn a =>
                 (case a of Inl x1a => (fn () => (Inl x1a))
                   | Inr ((a1a, a2a), a2) =>
                     (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                       (fn xb =>
                         (fn () =>
                           (if not (equal_nata a2 xb)
                             then Inr ((a1a, a2a), plus_nat one_nat a2)
                             else Inl ("Parsed beyond end", (NONE, NONE)))))))
        else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))
        ()
    end)
    x;

fun check_rup_proof3 x =
  (fn ai => fn bia => fn bi =>
    let
      val (a1, (a1a, a2a)) = bia;
    in
      (fn () =>
        let
          val xa = len heap_int ai ();
        in
          (if not (equal_nata bi xa)
            then (fn f_ => fn () => f_ ((nth heap_int ai bi) ()) ())
                   (fn xb =>
                     (fn f_ => fn () => f_
                       ((if less_int zero_int xb
                          then (fn f_ => fn () => f_ ((nth heap_int ai bi) ())
                                 ())
                                 (fn xc =>
                                   (fn () =>
                                     (Inr (nat xc, plus_nat one_nat bi))))
                          else (fn f_ => fn () => f_ ((nth heap_int ai bi) ())
                                 ())
                                 (fn xc =>
                                   (fn () =>
                                     (Inl ("Invalid id", (SOME xc, SOME bi))))))
                       ()) ())
                       (fn a =>
                         (case a of Inl x1a => (fn () => (Inl x1a))
                           | Inr (a1b, a2b) =>
                             (if less_nat a1 a1b
                               then (fn f_ => fn () => f_
                                      ((parse_check_blocked3 ai a2a a2b) ()) ())
                                      (fn aa =>
(case aa of Inl x1a => (fn () => (Inl x1a))
  | Inr (true, (_, ((a1f, a2f), _))) =>
    (fn f_ => fn () => f_ ((backtrack3 a1f a2f) ()) ())
      (fn x_f => (fn () => (Inr (a1b, (a1a, x_f)))))
  | Inr (false, (a1d, ((a1f, a2f), a2e))) =>
    (fn f_ => fn () => f_ ((apply_units3_bt ai a1a a1f a2f a2e) ()) ())
      (fn ab =>
        (case ab of Inl x1a => (fn () => (Inl x1a))
          | Inr ((a1h, a2h), a2g) =>
            (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
              (fn xc =>
                (if not (equal_nata a2g xc)
                  then (fn f_ => fn () => f_ ((nth heap_int ai a2g) ()) ())
                         (fn xd =>
                           (fn f_ => fn () => f_
                             ((if less_int zero_int xd
                                then (fn f_ => fn () => f_
                                       ((nth heap_int ai a2g) ()) ())
                                       (fn xe =>
 (fn () => (Inr (nat xe, plus_nat one_nat a2g))))
                                else (fn f_ => fn () => f_
                                       ((nth heap_int ai a2g) ()) ())
                                       (fn xe =>
 (fn () => (Inl ("Invalid id", (SOME xe, SOME a2g))))))
                             ()) ())
                             (fn ac =>
                               (case ac of Inl x1a => (fn () => (Inl x1a))
                                 | Inr (a1i, _) =>
                                   (fn f_ => fn () => f_ ((resolve_id3 a1a a1i)
                                     ()) ())
                                     (fn ad =>
                                       (case ad
 of Inl x1a => (fn () => (Inl x1a))
 | Inr x2ad =>
   (fn f_ => fn () => f_ ((check_conflict_clause3 ai bi a1h x2ad) ()) ())
     (fn ae =>
       (case ae of Inl x1a => (fn () => (Inl x1a))
         | Inr _ =>
           (fn f_ => fn () => f_ ((add_clause3 ai a1b a1d a1a) ()) ())
             (fn x_k =>
               (fn f_ => fn () => f_ ((backtrack3 a1h a2h) ()) ())
                 (fn x_l => (fn () => (Inr (a1b, (x_k, x_l)))))))))))))
                  else (fn () =>
                         (Inl ("Parsed beyond end", (NONE, NONE))))))))))
                               else (fn () =>
                                      (Inl
("Ids must be strictly increasing", (SOME (int_of_nat a1b), SOME bi))))))))
            else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))
            ()
        end)
    end)
    x;

fun and_not_C_excl3 x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, _) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
              (fn xa => (fn () => (not (equal_int xa zero_int) andalso true))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_
                  (let
                     val (a1a, a2a) = a2;
                   in
                     (if not (equal_int x_a bi)
                       then (fn f_ => fn () => f_
                              ((op_lit_is_false_impl x_a a1a) ()) ())
                              (fn xa =>
                                (if not xa
                                  then (fn f_ => fn () => f_
 ((assign_lit_impl a1a (uminus_int x_a)) ()) ())
 (fn x_e => (fn () => (x_e, (nat o abs_int) x_a :: a2a)))
                                  else (fn () => (a1a, a2a))))
                       else (fn () => (a1a, a2a)))
                   end
                  ()) ())
                  (fn x_c => (fn () => (plus_nat one_nat a1, x_c)))))
          (bia, (bib, [])) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun is_Nil a = (case a of [] => true | _ :: _ => false);

fun glist_member eq x [] = false
  | glist_member eq x (y :: ys) = eq x y orelse glist_member eq x ys;

fun rev_append [] ac = ac
  | rev_append (x :: xs) ac = rev_append xs (x :: ac);

fun glist_delete_aux eq x [] asa = asa
  | glist_delete_aux eq x (y :: ys) asa =
    (if eq x y then rev_append asa ys else glist_delete_aux eq x ys (y :: asa));

fun glist_delete eq x l = glist_delete_aux eq x l [];

fun check_rat_candidates_part3 x =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = len heap_int ai ();
    in
      (if not (equal_nata bi xa)
        then (fn f_ => fn () => f_
               ((heap_WHILET
                  (fn a =>
                    (case a of Inl _ => (fn () => false)
                      | Inr (_, (_, a2a)) =>
                        (fn f_ => fn () => f_ ((nth heap_int ai a2a) ()) ())
                          (fn xb => (fn () => (not (equal_int xb zero_int))))))
                  (fn s =>
                    let
                      val (a1, (a1a, a2a)) = projr s;
                    in
                      (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                        (fn xb =>
                          (if not (equal_nata a2a xb)
                            then (fn f_ => fn () => f_ ((nth heap_int ai a2a)
                                   ()) ())
                                   (fn xc =>
                                     (fn f_ => fn () => f_
                                       ((if less_int zero_int xc
  then (fn f_ => fn () => f_ ((nth heap_int ai a2a) ()) ())
         (fn xd => (fn () => (Inr (nat xd, plus_nat one_nat a2a))))
  else (fn f_ => fn () => f_ ((nth heap_int ai a2a) ()) ())
         (fn xd => (fn () => (Inl ("Invalid id", (SOME xd, SOME a2a))))))
                                       ()) ())
                                       (fn a =>
 (case a of Inl x1a => (fn () => (Inl x1a))
   | Inr (a1b, a2b) =>
     (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
       (fn xd =>
         (if not (equal_nata a2b xd)
           then (if glist_member equal_nata a1b a1
                  then (fn f_ => fn () => f_ ((resolve_id3 bid a1b) ()) ())
                         (fn xe =>
                           (fn f_ => fn () => f_
                             ((case xe of Inl x1a => (fn () => (Inl x1a))
                                | Inr x2aa =>
                                  (fn f_ => fn () => f_
                                    ((and_not_C_excl3 ai a1a x2aa
                                       (uminus_int bic))
                                    ()) ())
                                    (fn (a1c, a2c) =>
                                      (fn f_ => fn () => f_
((apply_units3_bt ai bid a1c a2c a2b) ()) ())
(fn aa =>
  (case aa of Inl x1a => (fn () => (Inl x1a))
    | Inr ((a1e, a2e), a2d) =>
      (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
        (fn xf =>
          (if not (equal_nata a2d xf)
            then (fn f_ => fn () => f_ ((nth heap_int ai a2d) ()) ())
                   (fn xg =>
                     (fn f_ => fn () => f_
                       ((if less_int zero_int xg
                          then (fn f_ => fn () => f_ ((nth heap_int ai a2d) ())
                                 ())
                                 (fn xh =>
                                   (fn () =>
                                     (Inr (nat xh, plus_nat one_nat a2d))))
                          else (fn f_ => fn () => f_ ((nth heap_int ai a2d) ())
                                 ())
                                 (fn xh =>
                                   (fn () =>
                                     (Inl ("Invalid id",
    (SOME xh, SOME a2d))))))
                       ()) ())
                       (fn ab =>
                         (case ab of Inl x1a => (fn () => (Inl x1a))
                           | Inr (a1f, a2f) =>
                             (fn f_ => fn () => f_ ((resolve_id3 bid a1f) ())
                               ())
                               (fn ac =>
                                 (case ac of Inl x1a => (fn () => (Inl x1a))
                                   | Inr x2ad =>
                                     (fn f_ => fn () => f_
                                       ((check_conflict_clause3 ai a2b a1e x2ad)
                                       ()) ())
                                       (fn ad =>
 (case ad of Inl x1a => (fn () => (Inl x1a))
   | Inr _ =>
     (fn f_ => fn () => f_ ((backtrack3 a1e a2e) ()) ())
       (fn x_s => (fn () => (Inr (x_s, a2f)))))))))))
            else (fn () => (Inl ("Parsed beyond end", (NONE, NONE))))))))))
                             ()) ())
                             (fn aa =>
                               (case aa of Inl x1a => (fn () => (Inl x1a))
                                 | Inr (a1c, a2c) =>
                                   (fn f_ => fn () => f_ ((len heap_int ai) ())
                                     ())
                                     (fn xf =>
                                       (fn () =>
 (if not (equal_nata a2c xf)
   then Inr (glist_delete equal_nata a1b a1, (a1c, a2c))
   else Inl ("Parsed beyond end", (NONE, NONE))))))))
                  else (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                         (fn xe =>
                           (if not (equal_nata a2b xe)
                             then (fn f_ => fn () => f_
                                    ((heap_WHILET
                                       (fn aa =>
 (case aa of Inl _ => (fn () => false)
   | Inr (a1c, _) =>
     (fn f_ => fn () => f_ ((nth heap_int ai a1c) ()) ())
       (fn xf => (fn () => (not (equal_int xf zero_int) andalso true)))))
                                       (fn sa =>
 let
   val (a1c, _) = projr sa;
 in
   (fn f_ => fn () => f_ ((nth heap_int ai a1c) ()) ())
     (fn _ =>
       let
         val x_n = plus_nat one_nat a1c;
       in
         (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
           (fn xf =>
             (fn () =>
               (if not (equal_nata x_n xf) then Inr (x_n, ())
                 else Inl ("Parsed beyond end", (NONE, NONE)))))
       end)
 end)
                                       (Inr (a2b, ())))
                                    ()) ())
                                    (fn aa =>
                                      (case aa
of Inl x1a => (fn () => (Inl x1a))
| Inr x2aa =>
  let
    val x_k = let
                val (a1c, _) = let
                                 val (a1c, ab) = x2aa;
                               in
                                 (plus_nat one_nat a1c, ab)
                               end;
              in
                a1c
              end;
  in
    (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
      (fn xf =>
        (if not (equal_nata x_k xf)
          then (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                 (fn xg =>
                   (fn () =>
                     (if not (equal_nata (plus_nat one_nat x_k) xg)
                       then Inr (a1, (a1a, plus_nat one_nat x_k))
                       else Inl ("Parsed beyond end", (NONE, NONE)))))
          else (fn () => (Inl ("Parsed beyond end", (NONE, NONE))))))
  end))
                             else (fn () =>
                                    (Inl ("Parsed beyond end",
   (NONE, NONE)))))))
           else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))))))
                            else (fn () =>
                                   (Inl ("Parsed beyond end", (NONE, NONE))))))
                    end)
                  (Inr (bib, (bia, bi))))
               ()) ())
               (fn a =>
                 (case a of Inl x1a => (fn () => (Inl x1a))
                   | Inr (a1, (a1a, a2a)) =>
                     (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                       (fn xb =>
                         (fn () =>
                           (if not (equal_nata a2a xb)
                             then (if is_Nil a1
                                    then Inr (a1a, plus_nat one_nat a2a)
                                    else Inl
   ("Too few RAT-candidates in proof", (NONE, NONE)))
                             else Inl ("Parsed beyond end", (NONE, NONE)))))))
        else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))
        ()
    end)
    x;

fun lit_in_clause_and_not_true3 x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val xa =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
              (fn xa =>
                (fn () =>
                  (not (equal_int xa zero_int) andalso
                    not (equal_nata a2 (nat_of_integer (2 : IntInf.int)))))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_
                  ((if equal_int x_a bi then (fn () => one_nat)
                     else (fn f_ => fn () => f_ ((op_lit_is_true_impl x_a bib)
                            ()) ())
                            (fn x_d =>
                              (fn () =>
                                (if x_d then nat_of_integer (2 : IntInf.int)
                                  else a2))))
                  ()) ())
                  (fn x_c => (fn () => (plus_nat one_nat a1, x_c)))))
          (bia, zero_nat) ();
    in
      equal_nata let
                   val (_, b) = xa;
                 in
                   b
                 end
        one_nat
    end)
    x;

fun is_None a = (case a of NONE => true | SOME _ => false);

fun op_creg_lookup A_ i a =
  array_get_dyn (heap_option A_) NONE a (int_encode i);

fun get_rat_candidates3 x =
  (fn ai => fn bib => fn bia => fn bi =>
    let
      val (a1, a2) = bib;
      val xa = uminus_int bi;
    in
      (fn () =>
        let
          val x_b = op_creg_lookup (heap_list heap_nat) xa a2 ();
        in
          (if not (is_None x_b)
            then (fn f_ => fn () => f_
                   ((imp_nfoldli (the x_b) (fn _ => (fn () => true))
                      (fn xh => fn sigma =>
                        (fn f_ => fn () => f_
                          ((array_get_dyn heap_nat zero_nat a1 xh) ()) ())
                          (fn x_i =>
                            (if not (equal_nata zero_nat x_i)
                              then (fn f_ => fn () => f_
                                     ((lit_in_clause_and_not_true3 ai bia x_i
xa)
                                     ()) ())
                                     (fn x_n =>
                                       (fn () =>
 (if x_n then xh :: sigma else sigma)))
                              else (fn () => sigma))))
                      [])
                   ()) ())
                   (fn x_e => (fn () => (Inr x_e)))
            else (fn () =>
                   (Inl ("Resolution literal not declared", (NONE, NONE)))))
            ()
        end)
    end)
    x;

fun lit_in_clause3 x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
              (fn xa =>
                (fn () => (not (equal_int xa zero_int) andalso not a2))))
          (fn (a1, _) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
              (fn x_a => (fn () => (plus_nat one_nat a1, equal_int bi x_a))))
          (bia, false) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun check_rat_proof3 x =
  (fn ai => fn bia => fn bi =>
    let
      val (a1, (a1a, a2a)) = bia;
    in
      (fn () =>
        let
          val xa = len heap_int ai ();
          val x_b =
            (if not (equal_nata bi xa)
              then (fn f_ => fn () => f_ ((nth heap_int ai bi) ()) ())
                     (fn xb => (fn () => (not (equal_int xb zero_int))))
              else (fn () => false))
              ();
        in
          (if x_b
            then (fn f_ => fn () => f_ ((nth heap_int ai bi) ()) ())
                   (fn xb =>
                     (fn f_ => fn () => f_ ((op_lit_is_false_impl xb a2a) ())
                       ())
                       (fn xc =>
                         (if not xc
                           then (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                                  (fn xd =>
                                    (if not
  (equal_nata (plus_nat one_nat bi) xd)
                                      then (fn f_ => fn () => f_
     ((nth heap_int ai (plus_nat one_nat bi)) ()) ())
     (fn xe =>
       (fn f_ => fn () => f_
         ((if less_int zero_int xe
            then (fn f_ => fn () => f_ ((nth heap_int ai (plus_nat one_nat bi))
                   ()) ())
                   (fn xf =>
                     (fn () =>
                       (Inr (nat xf, plus_nat one_nat (plus_nat one_nat bi)))))
            else (fn f_ => fn () => f_ ((nth heap_int ai (plus_nat one_nat bi))
                   ()) ())
                   (fn xf =>
                     (fn () =>
                       (Inl ("Invalid id",
                              (SOME xf, SOME (plus_nat one_nat bi)))))))
         ()) ())
         (fn a =>
           (case a of Inl x1a => (fn () => (Inl x1a))
             | Inr (a1b, a2b) =>
               (if less_nat a1 a1b
                 then (fn f_ => fn () => f_ ((parse_check_blocked3 ai a2a a2b)
                        ()) ())
                        (fn aa =>
                          (case aa of Inl x1a => (fn () => (Inl x1a))
                            | Inr (true, (_, ((a1f, a2f), _))) =>
                              (fn f_ => fn () => f_ ((backtrack3 a1f a2f) ())
                                ())
                                (fn x_h => (fn () => (Inr (a1b, (a1a, x_h)))))
                            | Inr (false, (a1d, ((a1f, a2f), a2e))) =>
                              (fn f_ => fn () => f_ ((nth heap_int ai bi) ())
                                ())
                                (fn xf =>
                                  (fn f_ => fn () => f_
                                    ((lit_in_clause3 ai a1d xf) ()) ())
                                    (fn x_h =>
                                      (case
(if x_h then Inr ()
  else Inl ("Resolution literal not in clause", (NONE, SOME bi)))
of Inl x1a => (fn () => (Inl x1a))
| Inr _ =>
  (fn f_ => fn () => f_ ((apply_units3_bt ai a1a a1f a2f a2e) ()) ())
    (fn ab =>
      (case ab of Inl x1a => (fn () => (Inl x1a))
        | Inr ((a1h, a2h), a2g) =>
          (fn f_ => fn () => f_ ((nth heap_int ai bi) ()) ())
            (fn xg =>
              (fn f_ => fn () => f_ ((get_rat_candidates3 ai a1a a1h xg) ()) ())
                (fn ac =>
                  (case ac of Inl x1a => (fn () => (Inl x1a))
                    | Inr x2ad =>
                      (fn f_ => fn () => f_ ((nth heap_int ai bi) ()) ())
                        (fn xh =>
                          (fn f_ => fn () => f_
                            ((check_rat_candidates_part3 ai a1a xh x2ad a1h a2g)
                            ()) ())
                            (fn ad =>
                              (case ad of Inl x1a => (fn () => (Inl x1a))
                                | Inr x2ae =>
                                  (fn f_ => fn () => f_
                                    (let
                                       val (a1i, _) = x2ae;
                                     in
                                       (fn f_ => fn () => f_
 ((add_clause3 ai a1b a1d a1a) ()) ())
 (fn x_m =>
   (fn f_ => fn () => f_ ((backtrack3 a1i a2h) ()) ())
     (fn x_n => (fn () => (a1b, (x_m, x_n)))))
                                     end
                                    ()) ())
                                    (fn x_m =>
                                      (fn () => (Inr x_m))))))))))))))))
                 else (fn () =>
                        (Inl ("Ids must be strictly increasing",
                               (SOME (int_of_nat a1b), SOME bi))))))))
                                      else (fn () =>
     (Inl ("Parsed beyond end", (NONE, NONE))))))
                           else (fn () =>
                                  (Inl ("Resolution literal is false",
 (NONE, SOME bi)))))))
            else (fn () =>
                   (Inl ("Expected resolution literal", (NONE, SOME bi)))))
            ()
        end)
    end)
    x;

fun apply_units3 x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = len heap_int ai ();
    in
      (if not (equal_nata bi xa)
        then (fn f_ => fn () => f_
               ((heap_WHILET
                  (fn a =>
                    (case a of Inl _ => (fn () => false)
                      | Inr (_, a2) =>
                        (fn f_ => fn () => f_ ((nth heap_int ai a2) ()) ())
                          (fn xb => (fn () => (not (equal_int xb zero_int))))))
                  (fn s =>
                    let
                      val (a1, a2) = projr s;
                    in
                      (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                        (fn xb =>
                          (if not (equal_nata a2 xb)
                            then (fn f_ => fn () => f_ ((nth heap_int ai a2) ())
                                   ())
                                   (fn xc =>
                                     (fn f_ => fn () => f_
                                       ((if less_int zero_int xc
  then (fn f_ => fn () => f_ ((nth heap_int ai a2) ()) ())
         (fn xd => (fn () => (Inr (nat xd, plus_nat one_nat a2))))
  else (fn f_ => fn () => f_ ((nth heap_int ai a2) ()) ())
         (fn xd => (fn () => (Inl ("Invalid id", (SOME xd, SOME a2))))))
                                       ()) ())
                                       (fn a =>
 (case a of Inl x1a => (fn () => (Inl x1a))
   | Inr (a1a, a2a) =>
     (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
       (fn xd =>
         (if not (equal_nata a2a xd)
           then (fn f_ => fn () => f_ ((resolve_id3 bib a1a) ()) ())
                  (fn xe =>
                    (fn f_ => fn () => f_
                      ((case xe of Inl x1a => (fn () => (Inl x1a))
                         | Inr x2aa =>
                           (fn f_ => fn () => f_
                             ((check_unit_clause3 ai a1 x2aa) ()) ())
                             (fn aa =>
                               (case aa of Inl x1a => (fn () => (Inl x1a))
                                 | Inr x2ab =>
                                   (fn f_ => fn () => f_
                                     ((assign_lit_impl a1 x2ab) ()) ())
                                     (fn x_i => (fn () => (Inr x_i))))))
                      ()) ())
                      (fn aa =>
                        (case aa of Inl x1a => (fn () => (Inl x1a))
                          | Inr x2aa => (fn () => (Inr (x2aa, a2a))))))
           else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))))))
                            else (fn () =>
                                   (Inl ("Parsed beyond end", (NONE, NONE))))))
                    end)
                  (Inr (bia, bi)))
               ()) ())
               (fn a =>
                 (case a of Inl x1a => (fn () => (Inl x1a))
                   | Inr (a1, a2) =>
                     (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                       (fn xb =>
                         (fn () =>
                           (if not (equal_nata a2 xb)
                             then Inr (a1, plus_nat one_nat a2)
                             else Inl ("Parsed beyond end", (NONE, NONE)))))))
        else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))
        ()
    end)
    x;

fun remove_ids3 x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = len heap_int ai ();
    in
      (if not (equal_nata bi xa)
        then (fn f_ => fn () => f_
               ((heap_WHILET
                  (fn a =>
                    (case a of Inl _ => (fn () => false)
                      | Inr (_, a2) =>
                        (fn f_ => fn () => f_ ((nth heap_int ai a2) ()) ())
                          (fn xb => (fn () => (not (equal_int xb zero_int))))))
                  (fn s =>
                    let
                      val (a1, a2) = projr s;
                    in
                      (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                        (fn xb =>
                          (if not (equal_nata a2 xb)
                            then (fn f_ => fn () => f_ ((nth heap_int ai a2) ())
                                   ())
                                   (fn xc =>
                                     (fn f_ => fn () => f_
                                       ((if less_int zero_int xc
  then (fn f_ => fn () => f_ ((nth heap_int ai a2) ()) ())
         (fn xd => (fn () => (Inr (nat xd, plus_nat one_nat a2))))
  else (fn f_ => fn () => f_ ((nth heap_int ai a2) ()) ())
         (fn xd => (fn () => (Inl ("Invalid id", (SOME xd, SOME a2))))))
                                       ()) ())
                                       (fn a =>
 (case a of Inl x1a => (fn () => (Inl x1a))
   | Inr (a1a, a2a) =>
     (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
       (fn xd =>
         (if not (equal_nata a2a xd)
           then (fn f_ => fn () => f_
                  (let
                     val (a1b, a2b) = a1;
                   in
                     (fn f_ => fn () => f_
                       ((array_set_dyn heap_nat zero_nat a1b a1a zero_nat) ())
                       ())
                       (fn x_g => (fn () => (x_g, a2b)))
                   end
                  ()) ())
                  (fn x_g => (fn () => (Inr (x_g, a2a))))
           else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))))))
                            else (fn () =>
                                   (Inl ("Parsed beyond end", (NONE, NONE))))))
                    end)
                  (Inr (bia, bi)))
               ()) ())
               (fn a =>
                 (case a of Inl x1a => (fn () => (Inl x1a))
                   | Inr (a1, a2) =>
                     (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                       (fn xb =>
                         (fn () =>
                           (if not (equal_nata a2 xb) then Inr a1
                             else Inl ("Parsed beyond end", (NONE, NONE)))))))
        else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))
        ()
    end)
    x;

fun check_item3 x =
  (fn ai => fn bia => fn bi =>
    let
      val (a1, (a1a, a2a)) = bia;
    in
      (fn () =>
        let
          val xa = len heap_int ai ();
        in
          (if not (equal_nata bi xa)
            then (fn f_ => fn () => f_ ((nth heap_int ai bi) ()) ())
                   (fn xb =>
                     (fn f_ => fn () => f_
                       ((if less_eq_int zero_int xb
                          then (fn f_ => fn () => f_ ((nth heap_int ai bi) ())
                                 ())
                                 (fn xc =>
                                   (fn () =>
                                     (Inr (nat xc, plus_nat one_nat bi))))
                          else (fn f_ => fn () => f_ ((nth heap_int ai bi) ())
                                 ())
                                 (fn xc =>
                                   (fn () =>
                                     (Inl ("Invalid nat",
    (SOME xc, SOME bi))))))
                       ()) ())
                       (fn a =>
                         (case a of Inl x1a => (fn () => (Inl x1a))
                           | Inr (a1b, a2b) =>
                             (if equal_nata a1b one_nat
                               then (fn f_ => fn () => f_
                                      ((apply_units3 ai a1a a2a a2b) ()) ())
                                      (fn aa =>
(case aa of Inl x1a => (fn () => (Inl x1a))
  | Inr x2aa => (fn () => (Inr let
                                 val (a1c, _) = x2aa;
                               in
                                 SOME (a1, (a1a, a1c))
                               end))))
                               else (if equal_nata a1b
  (nat_of_integer (2 : IntInf.int))
                                      then (fn f_ => fn () => f_
     ((remove_ids3 ai a1a a2b) ()) ())
     (fn aa =>
       (case aa of Inl x1a => (fn () => (Inl x1a))
         | Inr x2aa => (fn () => (Inr (SOME (a1, (x2aa, a2a)))))))
                                      else (if equal_nata a1b
         (nat_of_integer (3 : IntInf.int))
     then (fn f_ => fn () => f_ ((check_rup_proof3 ai (a1, (a1a, a2a)) a2b) ())
            ())
            (fn aa =>
              (case aa of Inl x1a => (fn () => (Inl x1a))
                | Inr x2aa => (fn () => (Inr (SOME x2aa)))))
     else (if equal_nata a1b (nat_of_integer (4 : IntInf.int))
            then (fn f_ => fn () => f_
                   ((check_rat_proof3 ai (a1, (a1a, a2a)) a2b) ()) ())
                   (fn aa =>
                     (case aa of Inl x1a => (fn () => (Inl x1a))
                       | Inr x2aa => (fn () => (Inr (SOME x2aa)))))
            else (if equal_nata a1b (nat_of_integer (5 : IntInf.int))
                   then (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                          (fn xc =>
                            (if not (equal_nata a2b xc)
                              then (fn f_ => fn () => f_ ((nth heap_int ai a2b)
                                     ()) ())
                                     (fn xd =>
                                       (fn f_ => fn () => f_
 ((if less_int zero_int xd
    then (fn f_ => fn () => f_ ((nth heap_int ai a2b) ()) ())
           (fn xe => (fn () => (Inr (nat xe, plus_nat one_nat a2b))))
    else (fn f_ => fn () => f_ ((nth heap_int ai a2b) ()) ())
           (fn xe => (fn () => (Inl ("Invalid id", (SOME xe, SOME a2b))))))
 ()) ())
 (fn aa =>
   (case aa of Inl x1a => (fn () => (Inl x1a))
     | Inr (a1c, _) =>
       (fn f_ => fn () => f_ ((resolve_id3 a1a a1c) ()) ())
         (fn ab =>
           (case ab of Inl x1a => (fn () => (Inl x1a))
             | Inr x2ab =>
               (fn f_ => fn () => f_ ((check_conflict_clause3 ai bi a2a x2ab)
                 ()) ())
                 (fn ac =>
                   (case ac of Inl x1a => (fn () => (Inl x1a))
                     | Inr _ => (fn () => (Inr NONE)))))))))
                              else (fn () =>
                                     (Inl ("Parsed beyond end",
    (NONE, NONE))))))
                   else (fn () =>
                          (if equal_nata a1b (nat_of_integer (6 : IntInf.int))
                            then Inl ("Not expecting rat-counts in the middle of proof",
                                       (NONE, SOME bi))
                            else Inl ("Invalid item type",
                                       (SOME (int_of_nat a1b),
 SOME bi))))))))))))
            else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))
            ()
        end)
    end)
    x;

fun read_clause_check_taut3 x =
  (fn ai => fn bib => fn bia => fn bi =>
    (if not (equal_nata bia bib)
      then (fn () =>
             let
               val a =
                 heap_WHILET
                   (fn a =>
                     (case a of Inl _ => (fn () => false)
                       | Inr (a1, _) =>
                         (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                           (fn xa =>
                             (fn () =>
                               (not (equal_int xa zero_int) andalso true)))))
                   (fn s =>
                     let
                       val (a1, a2) = projr s;
                     in
                       (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                         (fn x_d =>
                           (fn f_ => fn () => f_
                             (let
                                val (a1a, a2a) = a2;
                              in
                                (fn f_ => fn () => f_
                                  ((op_lit_is_false_impl x_d a2a) ()) ())
                                  (fn x_h =>
                                    (if x_h then (fn () => (true, a2a))
                                      else (fn f_ => fn () => f_
     ((assign_lit_impl a2a x_d) ()) ())
     (fn x_i => (fn () => (a1a, x_i)))))
                              end
                             ()) ())
                             (fn x_f =>
                               let
                                 val x_g = plus_nat one_nat a1;
                               in
                                 (fn () =>
                                   (if not (equal_nata x_g bib)
                                     then Inr (x_g, x_f)
                                     else Inl
    ("Parsed beyond end", (NONE, SOME bia))))
                               end))
                     end)
                   (Inr (bia, (false, bi))) ();
             in
               (case a of Inl x1a => (fn () => (Inl x1a))
                 | Inr x2a =>
                   (fn f_ => fn () => f_
                     (let
                        val (a1, (a1a, a2a)) = let
         val (a1, aa) = x2a;
       in
         (plus_nat one_nat a1, aa)
       end;
                      in
                        (fn f_ => fn () => f_
                          ((heap_WHILET
                             (fn (a1b, _) =>
                               (fn f_ => fn () => f_ ((nth heap_int ai a1b) ())
                                 ())
                                 (fn xa =>
                                   (fn () =>
                                     (not (equal_int xa zero_int) andalso
                                       true))))
                             (fn (a1b, a2b) =>
                               (fn f_ => fn () => f_ ((nth heap_int ai a1b) ())
                                 ())
                                 (fn x_d =>
                                   (fn f_ => fn () => f_
                                     ((unset_var_impl ((nat o abs_int) x_d) a2b)
                                     ()) ())
                                     (fn x_f =>
                                       (fn () => (plus_nat one_nat a1b, x_f)))))
                             (bia, a2a))
                          ()) ())
                          (fn x_c =>
                            (fn () => (a1, (a1a, let
           val (_, b) = x_c;
         in
           b
         end))))
                      end
                     ()) ())
                     (fn x_c => (fn () => (Inr x_c))))
                 ()
             end)
      else (fn () => (Inl ("Parsed beyond end", (NONE, SOME bia))))))
    x;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun read_cnf_new3 x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = assignment_empty_impl ();
      val a =
        heap_WHILET
          (fn a =>
            (case a of Inl _ => (fn () => false)
              | Inr (a1, _) => (fn () => (not (equal_nata a1 bib)))))
          (fn s =>
            let
              val (a1, (a1a, (a1b, a2b))) = projr s;
            in
              (fn f_ => fn () => f_ ((read_clause_check_taut3 ai bib a1 a2b) ())
                ())
                (fn a =>
                  (case a of Inl x1a => (fn () => (Inl x1a))
                    | Inr x2a =>
                      (fn f_ => fn () => f_
                        ((case x2a
                           of (a1c, (true, a2d)) =>
                             (fn () =>
                               (a1c, (a1a, (plus_nat a1b one_nat, a2d))))
                           | (a1c, (false, a2d)) =>
                             (fn f_ => fn () => f_ ((add_clause3 ai a1b a1 a1a)
                               ()) ())
                               (fn x_e =>
                                 (fn () =>
                                   (a1c, (x_e, (plus_nat a1b one_nat, a2d))))))
                        ()) ())
                        (fn x_d => (fn () => (Inr x_d)))))
            end)
          (Inr (bia, (bi, (one_nat, xa)))) ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr x2a =>
          (fn () => (Inr let
                           val (a1, (a1a, _)) = let
          val (_, b) = x2a;
        in
          b
        end;
                         in
                           (a1, minus_nat a1a one_nat)
                         end)))
        ()
    end)
    x;

fun item_next_impl a it =
  (fn () =>
    let
      val sz = nth heap_int a (minus_nat it one_nat) ();
    in
      (if less_int zero_int sz andalso less_nat (plus_nat (nat sz) one_nat) it
        then (fn () => (minus_nat (minus_nat it (nat sz)) one_nat))
        else (fn () => zero_nat))
        ()
    end);

fun creg_initialize l cr =
  (fn () =>
    let
      val x =
        array_set_dyn (heap_option (heap_list heap_nat)) NONE cr (int_encode l)
          (SOME []) ();
    in
      x
    end);

fun init_rat_counts3 x =
  (fn ai => fn bi => fn () =>
    let
      val xa = len heap_int ai ();
    in
      (if not (equal_nata bi xa)
        then (fn f_ => fn () => f_ ((nth heap_int ai bi) ()) ())
               (fn xb =>
                 (fn f_ => fn () => f_
                   ((if less_eq_int zero_int xb
                      then (fn f_ => fn () => f_ ((nth heap_int ai bi) ()) ())
                             (fn xc =>
                               (fn () => (Inr (nat xc, plus_nat one_nat bi))))
                      else (fn f_ => fn () => f_ ((nth heap_int ai bi) ()) ())
                             (fn xc =>
                               (fn () =>
                                 (Inl ("Invalid nat", (SOME xc, SOME bi))))))
                   ()) ())
                   (fn a =>
                     (case a of Inl x1a => (fn () => (Inl x1a))
                       | Inr (a1, a2) =>
                         (if equal_nata a1 one_nat orelse
                               (equal_nata a1
                                  (nat_of_integer (2 : IntInf.int)) orelse
                                 (equal_nata a1
                                    (nat_of_integer (3 : IntInf.int)) orelse
                                   (equal_nata a1
                                      (nat_of_integer (4 : IntInf.int)) orelse
                                     (equal_nata a1
(nat_of_integer (5 : IntInf.int)) orelse
                                       equal_nata a1
 (nat_of_integer (6 : IntInf.int))))))
                           then (if equal_nata a1
                                      (nat_of_integer (6 : IntInf.int))
                                  then (fn f_ => fn () => f_ ((len heap_int ai)
 ()) ())
 (fn xc =>
   (if not (equal_nata a2 xc)
     then (fn f_ => fn () => f_
            ((new heap_nat (nat_of_integer (16 : IntInf.int)) zero_nat) ()) ())
            (fn xd =>
              (fn f_ => fn () => f_ (creg_empty ()) ())
                (fn xaa =>
                  (fn f_ => fn () => f_
                    ((heap_WHILET
                       (fn aa =>
                         (case aa of Inl _ => (fn () => false)
                           | Inr (_, a2a) =>
                             (fn f_ => fn () => f_ ((nth heap_int ai a2a) ())
                               ())
                               (fn xe =>
                                 (fn () => (not (equal_int xe zero_int))))))
                       (fn s =>
                         let
                           val (a1a, a2a) = projr s;
                         in
                           (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
                             (fn xe =>
                               (if not (equal_nata (plus_nat one_nat a2a) xe)
                                 then (fn f_ => fn () => f_ ((len heap_int ai)
()) ())
(fn xf =>
  (if not (equal_nata (plus_nat one_nat (plus_nat one_nat a2a)) xf)
    then (fn f_ => fn () => f_ ((nth heap_int ai a2a) ()) ())
           (fn xg =>
             (fn f_ => fn () => f_
               (let
                  val (a1b, a2b) = a1a;
                in
                  (fn f_ => fn () => f_ ((creg_initialize (uminus_int xg) a2b)
                    ()) ())
                    (fn x_l => (fn () => (a1b, x_l)))
                end
               ()) ())
               (fn xh =>
                 (fn () =>
                   (Inr (xh, plus_nat one_nat (plus_nat one_nat a2a))))))
    else (fn () => (Inl ("Parsed beyond end", (NONE, NONE))))))
                                 else (fn () =>
(Inl ("Parsed beyond end", (NONE, NONE))))))
                         end)
                       (Inr ((xd, xaa), a2)))
                    ()) ())
                    (fn aa =>
                      (case aa of Inl x1a => (fn () => (Inl x1a))
                        | Inr x2aa =>
                          (fn () => (Inr let
   val (a1a, _) = x2aa;
 in
   a1a
 end))))))
     else (fn () => (Inl ("Parsed beyond end", (NONE, NONE))))))
                                  else (fn () =>
 (Inl ("Expected RAT counts item", (NONE, SOME bi)))))
                           else (fn () =>
                                  (Inl ("Invalid item type",
 (SOME (int_of_nat a1), SOME bi))))))))
        else (fn () => (Inl ("Parsed beyond end", (NONE, NONE)))))
        ()
    end)
    x;

fun verify_unsat3 x =
  (fn ai => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = assignment_empty_impl ();
    in
      (if not (at_item_end bic bi)
        then (fn f_ => fn () => f_ ((item_next_impl ai bi) ()) ())
               (fn xaa =>
                 (case (if not (equal_nata zero_nat xaa) then Inr xaa
                         else Inl ("Invalid item structure", (NONE, SOME bi)))
                   of Inl x1a => (fn () => (Inl x1a))
                   | Inr x2a =>
                     (fn f_ => fn () => f_ ((init_rat_counts3 ai x2a) ()) ())
                       (fn a =>
                         (case a of Inl x1a => (fn () => (Inl x1a))
                           | Inr x2aa =>
                             (fn f_ => fn () => f_
                               ((read_cnf_new3 ai bia bib x2aa) ()) ())
                               (fn aa =>
                                 (case aa of Inl x1a => (fn () => (Inl x1a))
                                   | Inr (a1, a2) =>
                                     (fn f_ => fn () => f_
                                       ((heap_WHILET
  (fn ab =>
    (case ab of Inl _ => (fn () => false)
      | Inr (a1a, a2a) =>
        (fn () => (not (is_None a1a) andalso not (at_item_end bic a2a)))))
  (fn s =>
    let
      val (a1a, a2a) = projr s;
    in
      (fn f_ => fn () => f_ ((item_next_impl ai a2a) ()) ())
        (fn xb =>
          (case (if not (equal_nata zero_nat xb) then Inr xb
                  else Inl ("Invalid item structure", (NONE, SOME a2a)))
            of Inl x1a => (fn () => (Inl x1a))
            | Inr x2ac =>
              (fn f_ => fn () => f_ ((check_item3 ai (the a1a) x2ac) ()) ())
                (fn ab =>
                  (case ab of Inl x1a => (fn () => (Inl x1a))
                    | Inr x2ad => (fn () => (Inr (x2ad, x2ac)))))))
    end)
  (Inr (SOME (a2, (a1, xa)), x2a)))
                                       ()) ())
                                       (fn ab =>
 (case ab of Inl x1a => (fn () => (Inl x1a))
   | Inr (a1a, _) =>
     (fn () =>
       (if is_None a1a then Inr ()
         else Inl ("Proof did not contain conflict declaration",
                    (NONE, NONE))))))))))))
        else (fn () => (Inl ("Invalid item structure", (NONE, NONE)))))
        ()
    end)
    x;

fun backtrack3a x =
  (fn ai => fn bi => imp_nfoldli bi (fn _ => (fn () => true)) unset_var_impl ai)
    x;

fun creg_register_ndj A_ l cid cr =
  (fn () =>
    let
      val a =
        array_get_dyn (heap_option (heap_list A_)) NONE cr (int_encode l) ();
    in
      (case a of NONE => (fn () => cr)
        | SOME s =>
          array_set_dyn (heap_option (heap_list A_)) NONE cr (int_encode l)
            (SOME (cid :: s)))
        ()
    end);

fun add_clause3a x =
  (fn ai => fn bib => fn bia => fn (a1, a2) => fn () =>
    let
      val xa = array_set_dyn heap_nat zero_nat a1 bib bia ();
      val x_b =
        heap_WHILET
          (fn (a1a, _) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1a) ()) ())
              (fn xb => (fn () => (not (equal_int xb zero_int) andalso true))))
          (fn (a1a, a2a) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1a) ()) ())
              (fn x_c =>
                (fn f_ => fn () => f_ ((creg_register_ndj heap_nat x_c bib a2a)
                  ()) ())
                  (fn x_g => (fn () => (plus_nat one_nat a1a, x_g)))))
          (bia, a2) ();
    in
      (xa, let
             val (_, b) = x_b;
           in
             b
           end)
    end)
    x;

fun mkp_raw_err msg i p = (msg, (i, p));

fun check_conflict_clause3a x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn a =>
            (case a of Inl _ => (fn () => false)
              | Inr (a1, _) =>
                (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                  (fn xa =>
                    (fn () => (not (equal_int xa zero_int) andalso true)))))
          (fn s =>
            let
              val (a1, _) = projr s;
            in
              (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                (fn x_c =>
                  (fn f_ => fn () => f_ ((op_lit_is_false_impl x_c bia) ()) ())
                    (fn xa =>
                      (case (if xa then Inr ()
                              else Inl (mkp_raw_err "Expected conflict clause"
 NONE (SOME bib)))
                        of Inl x1a => (fn () => (Inl x1a))
                        | Inr x2a =>
                          (fn () => (Inr (plus_nat one_nat a1, x2a))))))
            end)
          (Inr (bi, ())) ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr x2a => (fn () => (Inr let
                                      val (_, b) = x2a;
                                    in
                                      b
                                    end)))
        ()
    end)
    x;

fun parse_check_blocked3a x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = len heap_int ai ();
    in
      (if not (equal_nata bi xa)
        then (fn f_ => fn () => f_
               ((heap_WHILET
                  (fn a =>
                    (case a of Inl _ => (fn () => false)
                      | Inr (a1, _) =>
                        (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                          (fn xb =>
                            (fn () =>
                              (not (equal_int xb zero_int) andalso true)))))
                  (fn s =>
                    let
                      val (a1, a2) = projr s;
                    in
                      (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                        (fn x_d =>
                          (fn f_ => fn () => f_
                            (let
                               val (a1a, a2a) = a2;
                             in
                               (fn f_ => fn () => f_
                                 ((op_lit_is_true_impl x_d a1a) ()) ())
                                 (fn xb =>
                                   (if not xb
                                     then (fn f_ => fn () => f_
    ((op_lit_is_false_impl x_d a1a) ()) ())
    (fn xc =>
      (fn f_ => fn () => f_
        ((if xc then (fn () => (a1a, a2a))
           else (fn f_ => fn () => f_ ((assign_lit_impl a1a (uminus_int x_d))
                  ()) ())
                  (fn x_j => (fn () => (x_j, (nat o abs_int) x_d :: a2a))))
        ()) ())
        (fn x_i => (fn () => (Inr x_i))))
                                     else (fn () =>
    (Inl (mkp_raw_err "Blocked lemma clause" NONE NONE)))))
                             end
                            ()) ())
                            (fn a =>
                              (case a of Inl x1a => (fn () => (Inl x1a))
                                | Inr x2a =>
                                  let
                                    val x_g = plus_nat one_nat a1;
                                  in
                                    (fn f_ => fn () => f_ ((len heap_int ai) ())
                                      ())
                                      (fn xb =>
(fn () =>
  (if not (equal_nata x_g xb) then Inr (x_g, x2a)
    else Inl (mkp_raw_err "Parsed beyond end" NONE NONE))))
                                  end)))
                    end)
                  (Inr (bi, (bia, []))))
               ()) ())
               (fn a =>
                 (case a of Inl x1a => (fn () => (Inl x1a))
                   | Inr x2a =>
                     (fn () =>
                       let
                         val ((a1a, a2a), a2) =
                           let
                             val (a1, a2) = let
      val (a1, aa) = x2a;
    in
      (plus_nat one_nat a1, aa)
    end;
                           in
                             (a2, a1)
                           end;
                       in
                         Inr (bi, ((a1a, a2a), a2))
                       end)))
        else (fn () => (Inl (mkp_raw_err "Parsed beyond end" NONE NONE))))
        ()
    end)
    x;

fun check_unit_clause3a x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn a =>
            (case a of Inl _ => (fn () => false)
              | Inr (a1, _) =>
                (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                  (fn xa =>
                    (fn () => (not (equal_int xa zero_int) andalso true)))))
          (fn s =>
            let
              val (a1, a2) = projr s;
            in
              (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                (fn x_c =>
                  (fn f_ => fn () => f_ ((op_lit_is_true_impl x_c bia) ()) ())
                    (fn xa =>
                      (if not xa
                        then (fn f_ => fn () => f_
                               ((op_lit_is_false_impl x_c bia) ()) ())
                               (fn xb =>
                                 (case (if xb then Inr a2
 else (if equal_int zero_int a2 orelse equal_int a2 x_c then Inr x_c
        else Inl (mkp_raw_err "2-undec in clause assumed to be unit" NONE
                   NONE)))
                                   of Inl x1a => (fn () => (Inl x1a))
                                   | Inr x2a =>
                                     (fn () =>
                                       (Inr (plus_nat one_nat a1, x2a)))))
                        else (fn () =>
                               (Inl (mkp_raw_err
                                      "True literal in clause assumed to be unit"
                                      NONE NONE))))))
            end)
          (Inr (bi, zero_int)) ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr x2a =>
          let
            val x_a = let
                        val (_, b) = x2a;
                      in
                        b
                      end;
          in
            (fn () =>
              (if not (equal_int zero_int x_a) then Inr x_a
                else Inl (mkp_raw_err "Conflict in clause assumed to be unit"
                           NONE NONE)))
          end)
        ()
    end)
    x;

fun parse_prf_impl prfn =
  (fn (fuel, prf) =>
    (if less_nat zero_nat fuel
      then let
             val (x, prfa) = prfn prf;
           in
             (fn () => (Inr (x, (minus_nat fuel one_nat, prfa))))
           end
      else (fn () =>
             (Inl (mkp_raw_err "Out of fuel" NONE (SOME (fuel, prf)))))));

fun resolve_id3a x =
  (fn ai => fn bi =>
    let
      val (a1, _) = ai;
    in
      (fn () =>
        let
          val xa = array_get_dyn heap_nat zero_nat a1 bi ();
        in
          (if equal_nata zero_nat xa
            then Inl (mkp_raw_err "Invalid clause id" (SOME (int_of_nat bi))
                       NONE)
            else Inr xa)
        end)
    end)
    x;

fun apply_units3_bta x =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val a = parse_prf_impl bid bi ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr x2a =>
          (case let
                  val (a1, a2) = x2a;
                in
                  (if less_eq_int zero_int a1 then Inr (nat a1, a2)
                    else Inl (mkp_raw_err "Invalid idZ" (SOME a1) (SOME a2)))
                end
            of Inl x1a => (fn () => (Inl x1a))
            | Inr (a1, a2) =>
              (fn f_ => fn () => f_
                ((heap_WHILET
                   (fn aa =>
                     (case aa of Inl _ => (fn () => false)
                       | Inr (a1a, a2a) =>
                         (fn () => let
                                     val (_, _) = a1a;
                                     val (a1c, _) = a2a;
                                   in
                                     not (equal_nata a1c zero_nat)
                                   end)))
                   (fn s =>
                     let
                       val ((a1b, a2b), (a1c, a2c)) = projr s;
                     in
                       (fn f_ => fn () => f_ ((resolve_id3a bic a1c) ()) ())
                         (fn xa =>
                           (fn f_ => fn () => f_
                             ((case xa of Inl x1a => (fn () => (Inl x1a))
                                | Inr x2ab =>
                                  (fn f_ => fn () => f_
                                    ((check_unit_clause3a ai a1b x2ab) ()) ())
                                    (fn aa =>
                                      (case aa
of Inl x1a => (fn () => (Inl x1a))
| Inr x2ac =>
  (fn f_ => fn () => f_ ((assign_lit_impl a1b x2ac) ()) ())
    (fn xb => (fn () => (Inr (xb, (nat o abs_int) x2ac :: a2b)))))))
                             ()) ())
                             (fn aa =>
                               (case aa of Inl x1a => (fn () => (Inl x1a))
                                 | Inr (a1d, a2d) =>
                                   (fn f_ => fn () => f_
                                     ((parse_prf_impl bid a2c) ()) ())
                                     (fn ab =>
                                       (case ab
 of Inl x1a => (fn () => (Inl x1a))
 | Inr x2ac =>
   (case let
           val (a1e, a2e) = x2ac;
         in
           (if less_eq_int zero_int a1e then Inr (nat a1e, a2e)
             else Inl (mkp_raw_err "Invalid idZ" (SOME a1e) (SOME a2e)))
         end
     of Inl x1a => (fn () => (Inl x1a))
     | Inr x2ad => (fn () => (Inr let
                                    val (a1e, a2e) = x2ad;
                                  in
                                    ((a1d, a2d), (a1e, a2e))
                                  end))))))))
                     end)
                   (Inr ((bib, bia), (a1, a2))))
                ()) ())
                (fn aa =>
                  (case aa of Inl x1a => (fn () => (Inl x1a))
                    | Inr (a1a, a2a) =>
                      (fn () => let
                                  val (a1b, a2b) = a1a;
                                in
                                  Inr let
val (_, ab) = a2a;
                                      in
((a1b, a2b), ab)
                                      end
                                end)))))
        ()
    end)
    x;

fun check_rup_proof3a x =
  (fn ai => fn bic => fn bib => fn bia => fn bi =>
    let
      val (a1, a2) = bib;
    in
      (fn () =>
        let
          val a = parse_prf_impl bic bi ();
        in
          (case a of Inl x1a => (fn () => (Inl x1a))
            | Inr x2a =>
              (case let
                      val (a1a, a2a) = x2a;
                    in
                      (if less_int zero_int a1a then Inr (nat a1a, a2a)
                        else Inl (mkp_raw_err "Invalid id" (SOME a1a)
                                   (SOME a2a)))
                    end
                of Inl x1a => (fn () => (Inl x1a))
                | Inr (a1a, a2a) =>
                  (fn f_ => fn () => f_
                    (let
                       val (a1b, _) = a1;
                     in
                       (fn f_ => fn () => f_
                         ((array_get_dyn heap_nat zero_nat a1b a1a) ()) ())
                         (fn x_b => (fn () => (equal_nata zero_nat x_b)))
                     end
                    ()) ())
                    (fn x_b =>
                      (if x_b
                        then (fn f_ => fn () => f_
                               ((parse_check_blocked3a ai a2 bia) ()) ())
                               (fn aa =>
                                 (case aa of Inl x1a => (fn () => (Inl x1a))
                                   | Inr (a1b, ((a1d, a2d), a2c)) =>
                                     (fn f_ => fn () => f_
                                       ((apply_units3_bta ai bic a1 a1d a2d a2a)
                                       ()) ())
                                       (fn ab =>
 (case ab of Inl x1a => (fn () => (Inl x1a))
   | Inr ((a1f, a2f), a2e) =>
     (fn f_ => fn () => f_ ((parse_prf_impl bic a2e) ()) ())
       (fn ac =>
         (case ac of Inl x1a => (fn () => (Inl x1a))
           | Inr x2ad =>
             (case let
                     val (a1g, a2g) = x2ad;
                   in
                     (if less_int zero_int a1g then Inr (nat a1g, a2g)
                       else Inl (mkp_raw_err "Invalid id" (SOME a1g)
                                  (SOME a2g)))
                   end
               of Inl x1a => (fn () => (Inl x1a))
               | Inr (a1g, a2g) =>
                 (fn f_ => fn () => f_ ((resolve_id3a a1 a1g) ()) ())
                   (fn ad =>
                     (case ad of Inl x1a => (fn () => (Inl x1a))
                       | Inr x2af =>
                         (fn f_ => fn () => f_
                           ((check_conflict_clause3a ai a2g a1f x2af) ()) ())
                           (fn ae =>
                             (case ae of Inl x1a => (fn () => (Inl x1a))
                               | Inr _ =>
                                 (fn f_ => fn () => f_
                                   ((add_clause3a ai a1a a1b a1) ()) ())
                                   (fn x_i =>
                                     (fn f_ => fn () => f_
                                       ((backtrack3a a1f a2f) ()) ())
                                       (fn x_j =>
 (fn () => (Inr ((x_i, x_j), (a2c, a2g)))))))))))))))))
                        else (fn () =>
                               (Inl (mkp_raw_err "Duplicate ID"
                                      (SOME (int_of_nat a1a)) (SOME a2a))))))))
            ()
        end)
    end)
    x;

fun and_not_C_excl3a x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, _) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
              (fn xa => (fn () => (not (equal_int xa zero_int) andalso true))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_
                  (let
                     val (a1a, a2a) = a2;
                   in
                     (if not (equal_int x_a bi)
                       then (fn f_ => fn () => f_
                              ((op_lit_is_false_impl x_a a1a) ()) ())
                              (fn xa =>
                                (if not xa
                                  then (fn f_ => fn () => f_
 ((assign_lit_impl a1a (uminus_int x_a)) ()) ())
 (fn x_e => (fn () => (x_e, (nat o abs_int) x_a :: a2a)))
                                  else (fn () => (a1a, a2a))))
                       else (fn () => (a1a, a2a)))
                   end
                  ()) ())
                  (fn x_c => (fn () => (plus_nat one_nat a1, x_c)))))
          (bia, (bib, [])) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun check_rat_candidates_part3a x =
  (fn ai => fn bie => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val a = parse_prf_impl bie bi ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr x2a =>
          (case let
                  val (a1, a2) = x2a;
                in
                  (if less_eq_int zero_int a1 then Inr (nat a1, a2)
                    else Inl (mkp_raw_err "Invalid idZ" (SOME a1) (SOME a2)))
                end
            of Inl x1a => (fn () => (Inl x1a))
            | Inr (a1, a2) =>
              (fn f_ => fn () => f_
                ((heap_WHILET
                   (fn aa =>
                     (case aa of Inl _ => (fn () => false)
                       | Inr (_, (_, (a1c, _))) =>
                         (fn () => (not (equal_nata a1c zero_nat)))))
                   (fn s =>
                     let
                       val (a1a, (a1b, (a1c, a2c))) = projr s;
                     in
                       (if glist_member equal_nata a1c a1a
                         then (fn f_ => fn () => f_ ((resolve_id3a bid a1c) ())
                                ())
                                (fn aa =>
                                  (case aa of Inl x1a => (fn () => (Inl x1a))
                                    | Inr x2ab =>
                                      (fn f_ => fn () => f_
((and_not_C_excl3a ai a1b x2ab (uminus_int bic)) ()) ())
(fn x_i =>
  (fn f_ => fn () => f_
    (let
       val (a1d, a2d) = x_i;
     in
       (fn f_ => fn () => f_ ((apply_units3_bta ai bie bid a1d a2d a2c) ()) ())
         (fn ab =>
           (case ab of Inl x1a => (fn () => (Inl x1a))
             | Inr ((a1f, a2f), a2e) =>
               (fn f_ => fn () => f_ ((parse_prf_impl bie a2e) ()) ())
                 (fn ac =>
                   (case ac of Inl x1a => (fn () => (Inl x1a))
                     | Inr x2ad =>
                       (case let
                               val (a1g, a2g) = x2ad;
                             in
                               (if less_int zero_int a1g then Inr (nat a1g, a2g)
                                 else Inl
(mkp_raw_err "Invalid id" (SOME a1g) (SOME a2g)))
                             end
                         of Inl x1a => (fn () => (Inl x1a))
                         | Inr (a1g, a2g) =>
                           (fn f_ => fn () => f_ ((resolve_id3a bid a1g) ()) ())
                             (fn ad =>
                               (case ad of Inl x1a => (fn () => (Inl x1a))
                                 | Inr x2af =>
                                   (fn f_ => fn () => f_
                                     ((check_conflict_clause3a ai a2g a1f x2af)
                                     ()) ())
                                     (fn ae =>
                                       (case ae
 of Inl x1a => (fn () => (Inl x1a))
 | Inr _ =>
   (fn f_ => fn () => f_ ((backtrack3a a1f a2f) ()) ())
     (fn x_o => (fn () => (Inr (x_o, a2g)))))))))))))
     end
    ()) ())
    (fn ab =>
      (case ab of Inl x1a => (fn () => (Inl x1a))
        | Inr (a1d, a2d) =>
          (fn f_ => fn () => f_ ((parse_prf_impl bie a2d) ()) ())
            (fn ac =>
              (case ac of Inl x1a => (fn () => (Inl x1a))
                | Inr x2ad =>
                  (case let
                          val (a1e, a2e) = x2ad;
                        in
                          (if less_eq_int zero_int a1e then Inr (nat a1e, a2e)
                            else Inl (mkp_raw_err "Invalid idZ" (SOME a1e)
                                       (SOME a2e)))
                        end
                    of Inl x1a => (fn () => (Inl x1a))
                    | Inr x2ae =>
                      (fn () =>
                        (Inr let
                               val (a1e, a2e) = x2ae;
                             in
                               (glist_delete equal_nata a1c a1a,
                                 (a1d, (a1e, a2e)))
                             end))))))))))
                         else (fn f_ => fn () => f_ ((parse_prf_impl bie a2c)
                                ()) ())
                                (fn aa =>
                                  (case aa of Inl x1a => (fn () => (Inl x1a))
                                    | Inr x2ab =>
                                      (fn f_ => fn () => f_
(let
   val (a1d, a2d) = x2ab;
 in
   (fn f_ => fn () => f_
     ((heap_WHILET
        (fn ab =>
          (case ab of Inl _ => (fn () => false)
            | Inr (a1e, _) => (fn () => (not (equal_int a1e zero_int)))))
        (fn sa => let
                    val (_, ab) = projr sa;
                  in
                    parse_prf_impl bie ab
                  end)
        (Inr (a1d, a2d)))
     ()) ())
     (fn ab =>
       (case ab of Inl x1a => (fn () => (Inl x1a))
         | Inr x2ac => (fn () => (Inr let
val (_, b) = x2ac;
                                      in
b
                                      end))))
 end
()) ())
(fn ab =>
  (case ab of Inl x1a => (fn () => (Inl x1a))
    | Inr x2ac =>
      (fn f_ => fn () => f_ ((parse_prf_impl bie x2ac) ()) ())
        (fn ac =>
          (case ac of Inl x1a => (fn () => (Inl x1a))
            | Inr (_, a2d) =>
              (fn f_ => fn () => f_ ((parse_prf_impl bie a2d) ()) ())
                (fn ad =>
                  (case ad of Inl x1a => (fn () => (Inl x1a))
                    | Inr x2ae =>
                      (case let
                              val (a1e, a2e) = x2ae;
                            in
                              (if less_eq_int zero_int a1e
                                then Inr (nat a1e, a2e)
                                else Inl (mkp_raw_err "Invalid idZ" (SOME a1e)
   (SOME a2e)))
                            end
                        of Inl x1a => (fn () => (Inl x1a))
                        | Inr x2af =>
                          (fn () => (Inr let
   val (a1e, a2e) = x2af;
 in
   (a1a, (a1b, (a1e, a2e)))
 end))))))))))))
                     end)
                   (Inr (bib, (bia, (a1, a2)))))
                ()) ())
                (fn aa =>
                  (case aa of Inl x1a => (fn () => (Inl x1a))
                    | Inr (a1a, (a1b, (_, a2c))) =>
                      (fn () =>
                        (if is_Nil a1a then Inr (a1b, a2c)
                          else Inl (mkp_raw_err
                                     "Too few RAT-candidates in proof" NONE
                                     (SOME a2c))))))))
        ()
    end)
    x;

fun lit_in_clause_and_not_true3a x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val xa =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
              (fn xa =>
                (fn () =>
                  (not (equal_int xa zero_int) andalso
                    not (equal_nata a2 (nat_of_integer (2 : IntInf.int)))))))
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_
                  ((if equal_int x_a bi then (fn () => one_nat)
                     else (fn f_ => fn () => f_ ((op_lit_is_true_impl x_a bib)
                            ()) ())
                            (fn x_d =>
                              (fn () =>
                                (if x_d then nat_of_integer (2 : IntInf.int)
                                  else a2))))
                  ()) ())
                  (fn x_c => (fn () => (plus_nat one_nat a1, x_c)))))
          (bia, zero_nat) ();
    in
      equal_nata let
                   val (_, b) = xa;
                 in
                   b
                 end
        one_nat
    end)
    x;

fun get_rat_candidates3a x =
  (fn ai => fn bib => fn bia => fn bi =>
    let
      val (a1, a2) = bib;
      val xa = uminus_int bi;
    in
      (fn () =>
        let
          val x_b = op_creg_lookup (heap_list heap_nat) xa a2 ();
        in
          (if not (is_None x_b)
            then (fn f_ => fn () => f_
                   ((imp_nfoldli (the x_b) (fn _ => (fn () => true))
                      (fn xh => fn sigma =>
                        (fn f_ => fn () => f_
                          ((array_get_dyn heap_nat zero_nat a1 xh) ()) ())
                          (fn x_i =>
                            (if not (equal_nata zero_nat x_i)
                              then (fn f_ => fn () => f_
                                     ((lit_in_clause_and_not_true3a ai bia x_i
xa)
                                     ()) ())
                                     (fn x_n =>
                                       (fn () =>
 (if x_n then xh :: sigma else sigma)))
                              else (fn () => sigma))))
                      [])
                   ()) ())
                   (fn x_e => (fn () => (Inr (remdups equal_nat x_e))))
            else (fn () =>
                   (Inl (mkp_raw_err "Resolution literal not declared" NONE
                          NONE))))
            ()
        end)
    end)
    x;

fun lit_in_clause3a x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
              (fn xa =>
                (fn () => (not (equal_int xa zero_int) andalso not a2))))
          (fn (a1, _) =>
            (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
              (fn x_a => (fn () => (plus_nat one_nat a1, equal_int bi x_a))))
          (bia, false) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end)
    x;

fun check_rat_proof3a x =
  (fn ai => fn bic => fn bib => fn bia => fn bi =>
    let
      val (a1, a2) = bib;
    in
      (fn () =>
        let
          val a = parse_prf_impl bic bi ();
        in
          (case a of Inl x1a => (fn () => (Inl x1a))
            | Inr x2a =>
              (case let
                      val (a1a, a2a) = x2a;
                    in
                      (if not (equal_int a1a zero_int) then Inr (a1a, a2a)
                        else Inl (mkp_raw_err "Expected literal but found 0"
                                   NONE (SOME a2a)))
                    end
                of Inl x1a => (fn () => (Inl x1a))
                | Inr (a1a, a2a) =>
                  (fn f_ => fn () => f_ ((op_lit_is_false_impl a1a a2) ()) ())
                    (fn xa =>
                      (if not xa
                        then (fn f_ => fn () => f_ ((parse_prf_impl bic a2a) ())
                               ())
                               (fn aa =>
                                 (case aa of Inl x1a => (fn () => (Inl x1a))
                                   | Inr x2ab =>
                                     (case let
     val (a1b, a2b) = x2ab;
   in
     (if less_int zero_int a1b then Inr (nat a1b, a2b)
       else Inl (mkp_raw_err "Invalid id" (SOME a1b) (SOME a2b)))
   end
                                       of Inl x1a => (fn () => (Inl x1a))
                                       | Inr (a1b, a2b) =>
 (fn f_ => fn () => f_
   (let
      val (a1c, _) = a1;
    in
      (fn f_ => fn () => f_ ((array_get_dyn heap_nat zero_nat a1c a1b) ()) ())
        (fn x_e => (fn () => (equal_nata zero_nat x_e)))
    end
   ()) ())
   (fn x_e =>
     (if x_e
       then (fn f_ => fn () => f_ ((parse_check_blocked3a ai a2 bia) ()) ())
              (fn ab =>
                (case ab of Inl x1a => (fn () => (Inl x1a))
                  | Inr (a1c, ((a1e, a2e), a2d)) =>
                    (fn f_ => fn () => f_ ((lit_in_clause3a ai a1c a1a) ()) ())
                      (fn x_g =>
                        (case (if x_g then Inr ()
                                else Inl (mkp_raw_err
   "Resolution literal not in clause" NONE (SOME a2b)))
                          of Inl x1a => (fn () => (Inl x1a))
                          | Inr _ =>
                            (fn f_ => fn () => f_
                              ((apply_units3_bta ai bic a1 a1e a2e a2b) ()) ())
                              (fn ac =>
                                (case ac of Inl x1a => (fn () => (Inl x1a))
                                  | Inr ((a1g, a2g), a2f) =>
                                    (fn f_ => fn () => f_
                                      ((get_rat_candidates3a ai a1 a1g a1a) ())
                                      ())
                                      (fn ad =>
(case ad of Inl x1a => (fn () => (Inl x1a))
  | Inr x2ag =>
    (fn f_ => fn () => f_
      ((check_rat_candidates_part3a ai bic a1 a1a x2ag a1g a2f) ()) ())
      (fn ae =>
        (case ae of Inl x1a => (fn () => (Inl x1a))
          | Inr x2ah =>
            (fn f_ => fn () => f_
              (let
                 val (a1h, a2h) = x2ah;
               in
                 (fn f_ => fn () => f_ ((add_clause3a ai a1b a1c a1) ()) ())
                   (fn x_l =>
                     (fn f_ => fn () => f_ ((backtrack3a a1h a2g) ()) ())
                       (fn x_m => (fn () => ((x_l, x_m), (a2d, a2h)))))
               end
              ()) ())
              (fn x_l => (fn () => (Inr x_l)))))))))))))
       else (fn () =>
              (Inl (mkp_raw_err "Ids must be strictly increasing"
                     (SOME (int_of_nat a1b)) (SOME a2b)))))))))
                        else (fn () =>
                               (Inl (mkp_raw_err "Resolution literal is false"
                                      NONE (SOME a2a))))))))
            ()
        end)
    end)
    x;

fun apply_units3a x =
  (fn ai => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val a = parse_prf_impl bic bi ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr x2a =>
          (case let
                  val (a1, a2) = x2a;
                in
                  (if less_eq_int zero_int a1 then Inr (nat a1, a2)
                    else Inl (mkp_raw_err "Invalid idZ" (SOME a1) (SOME a2)))
                end
            of Inl x1a => (fn () => (Inl x1a))
            | Inr (a1, a2) =>
              (fn f_ => fn () => f_
                ((heap_WHILET
                   (fn aa =>
                     (case aa of Inl _ => (fn () => false)
                       | Inr (_, (a1b, _)) =>
                         (fn () => (not (equal_nata a1b zero_nat)))))
                   (fn s =>
                     let
                       val (a1a, (a1b, a2b)) = projr s;
                     in
                       (fn f_ => fn () => f_ ((resolve_id3a bib a1b) ()) ())
                         (fn xa =>
                           (fn f_ => fn () => f_
                             ((case xa of Inl x1a => (fn () => (Inl x1a))
                                | Inr x2ab =>
                                  (fn f_ => fn () => f_
                                    ((check_unit_clause3a ai a1a x2ab) ()) ())
                                    (fn aa =>
                                      (case aa
of Inl x1a => (fn () => (Inl x1a))
| Inr x2ac =>
  (fn f_ => fn () => f_ ((assign_lit_impl a1a x2ac) ()) ())
    (fn x_g => (fn () => (Inr x_g))))))
                             ()) ())
                             (fn aa =>
                               (case aa of Inl x1a => (fn () => (Inl x1a))
                                 | Inr x2ab =>
                                   (fn f_ => fn () => f_
                                     ((parse_prf_impl bic a2b) ()) ())
                                     (fn ab =>
                                       (case ab
 of Inl x1a => (fn () => (Inl x1a))
 | Inr x2ac =>
   (case let
           val (a1c, a2c) = x2ac;
         in
           (if less_eq_int zero_int a1c then Inr (nat a1c, a2c)
             else Inl (mkp_raw_err "Invalid idZ" (SOME a1c) (SOME a2c)))
         end
     of Inl x1a => (fn () => (Inl x1a))
     | Inr x2ad => (fn () => (Inr let
                                    val (a1c, a2c) = x2ad;
                                  in
                                    (x2ab, (a1c, a2c))
                                  end))))))))
                     end)
                   (Inr (bia, (a1, a2))))
                ()) ())
                (fn aa =>
                  (case aa of Inl x1a => (fn () => (Inl x1a))
                    | Inr x2ab => (fn () => (Inr let
           val (a1a, ab) = x2ab;
           val (_, ac) = ab;
         in
           (a1a, ac)
         end))))))
        ()
    end)
    x;

fun remove_ids3a x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val a = parse_prf_impl ai bi ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr x2a =>
          (case let
                  val (a1, a2) = x2a;
                in
                  (if less_eq_int zero_int a1 then Inr (nat a1, a2)
                    else Inl (mkp_raw_err "Invalid idZ" (SOME a1) (SOME a2)))
                end
            of Inl x1a => (fn () => (Inl x1a))
            | Inr (a1, a2) =>
              (fn f_ => fn () => f_
                ((heap_WHILET
                   (fn aa =>
                     (case aa of Inl _ => (fn () => false)
                       | Inr (_, (a1b, _)) =>
                         (fn () => (not (equal_nata a1b zero_nat)))))
                   (fn s =>
                     let
                       val (a1a, (a1b, a2b)) = projr s;
                     in
                       (fn f_ => fn () => f_
                         (let
                            val (a1c, a2c) = a1a;
                          in
                            (fn f_ => fn () => f_
                              ((array_set_dyn heap_nat zero_nat a1c a1b
                                 zero_nat)
                              ()) ())
                              (fn x_e => (fn () => (x_e, a2c)))
                          end
                         ()) ())
                         (fn x_e =>
                           (fn f_ => fn () => f_ ((parse_prf_impl ai a2b) ())
                             ())
                             (fn aa =>
                               (case aa of Inl x1a => (fn () => (Inl x1a))
                                 | Inr x2ab =>
                                   (case let
   val (a1c, a2c) = x2ab;
 in
   (if less_eq_int zero_int a1c then Inr (nat a1c, a2c)
     else Inl (mkp_raw_err "Invalid idZ" (SOME a1c) (SOME a2c)))
 end
                                     of Inl x1a => (fn () => (Inl x1a))
                                     | Inr x2ac =>
                                       (fn () =>
 (Inr let
        val (a1c, a2c) = x2ac;
      in
        (x_e, (a1c, a2c))
      end))))))
                     end)
                   (Inr (bia, (a1, a2))))
                ()) ())
                (fn aa =>
                  (case aa of Inl x1a => (fn () => (Inl x1a))
                    | Inr x2ab => (fn () => (Inr let
           val (a1a, ab) = x2ab;
           val (_, ac) = ab;
         in
           (a1a, ac)
         end))))))
        ()
    end)
    x;

fun check_item3a x =
  (fn ai => fn bic => fn bib => fn bia => fn bi =>
    let
      val (a1, a2) = bib;
    in
      (fn () =>
        let
          val a = parse_prf_impl bic bi ();
        in
          (case a of Inl x1a => (fn () => (Inl x1a))
            | Inr (a1a, a2a) =>
              (if equal_int a1a one_int
                then (fn f_ => fn () => f_ ((apply_units3a ai bic a1 a2 a2a) ())
                       ())
                       (fn aa =>
                         (case aa of Inl x1a => (fn () => (Inl x1a))
                           | Inr x2aa =>
                             (fn () => (Inr let
      val (a1b, a2b) = x2aa;
    in
      SOME ((a1, a1b), (bia, a2b))
    end))))
                else (if equal_int a1a (Int_of_integer (2 : IntInf.int))
                       then (fn f_ => fn () => f_ ((remove_ids3a bic a1 a2a) ())
                              ())
                              (fn aa =>
                                (case aa of Inl x1a => (fn () => (Inl x1a))
                                  | Inr x2aa =>
                                    (fn () =>
                                      (Inr let
     val (a1b, a2b) = x2aa;
   in
     SOME ((a1b, a2), (bia, a2b))
   end))))
                       else (if equal_int a1a (Int_of_integer (3 : IntInf.int))
                              then (fn f_ => fn () => f_
                                     ((check_rup_proof3a ai bic (a1, a2) bia
a2a)
                                     ()) ())
                                     (fn aa =>
                                       (case aa
 of Inl x1a => (fn () => (Inl x1a)) | Inr x2aa => (fn () => (Inr (SOME x2aa)))))
                              else (if equal_int a1a
 (Int_of_integer (4 : IntInf.int))
                                     then (fn f_ => fn () => f_
    ((check_rat_proof3a ai bic (a1, a2) bia a2a) ()) ())
    (fn aa =>
      (case aa of Inl x1a => (fn () => (Inl x1a))
        | Inr x2aa => (fn () => (Inr (SOME x2aa)))))
                                     else (if equal_int a1a
        (Int_of_integer (5 : IntInf.int))
    then (fn f_ => fn () => f_ ((parse_prf_impl bic a2a) ()) ())
           (fn aa =>
             (case aa of Inl x1a => (fn () => (Inl x1a))
               | Inr x2aa =>
                 (case let
                         val (a1b, a2b) = x2aa;
                       in
                         (if less_int zero_int a1b then Inr (nat a1b, a2b)
                           else Inl (mkp_raw_err "Invalid id" (SOME a1b)
                                      (SOME a2b)))
                       end
                   of Inl x1a => (fn () => (Inl x1a))
                   | Inr (a1b, a2b) =>
                     (fn f_ => fn () => f_ ((resolve_id3a a1 a1b) ()) ())
                       (fn ab =>
                         (case ab of Inl x1a => (fn () => (Inl x1a))
                           | Inr x2ac =>
                             (fn f_ => fn () => f_
                               ((check_conflict_clause3a ai a2b a2 x2ac) ()) ())
                               (fn ac =>
                                 (case ac of Inl x1a => (fn () => (Inl x1a))
                                   | Inr _ => (fn () => (Inr NONE)))))))))
    else (fn () =>
           (if equal_int a1a (Int_of_integer (6 : IntInf.int))
             then Inl (mkp_raw_err
                        "Not expecting rat-counts in the middle of proof" NONE
                        (SOME a2a))
             else Inl (mkp_raw_err "Invalid item type" (SOME a1a)
                        (SOME a2a))))))))))
            ()
        end)
    end)
    x;

fun verify_sat_impl_wrapper dBi f_end =
  (fn () =>
    let
      val lenDBi = len heap_int dBi ();
    in
      (if less_nat zero_nat f_end andalso less_eq_nat f_end lenDBi
        then verify_sat3 dBi one_nat f_end f_end
        else (fn () => (Inl ("Invalid arguments", (NONE, NONE)))))
        ()
    end);

fun read_clause_check_taut3a x =
  (fn ai => fn bib => fn bia => fn bi =>
    (if not (equal_nata bia bib)
      then (fn () =>
             let
               val a =
                 heap_WHILET
                   (fn a =>
                     (case a of Inl _ => (fn () => false)
                       | Inr (a1, _) =>
                         (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                           (fn xa =>
                             (fn () =>
                               (not (equal_int xa zero_int) andalso true)))))
                   (fn s =>
                     let
                       val (a1, a2) = projr s;
                     in
                       (fn f_ => fn () => f_ ((nth heap_int ai a1) ()) ())
                         (fn x_d =>
                           (fn f_ => fn () => f_
                             (let
                                val (a1a, a2a) = a2;
                              in
                                (fn f_ => fn () => f_
                                  ((op_lit_is_false_impl x_d a2a) ()) ())
                                  (fn x_h =>
                                    (if x_h then (fn () => (true, a2a))
                                      else (fn f_ => fn () => f_
     ((assign_lit_impl a2a x_d) ()) ())
     (fn x_i => (fn () => (a1a, x_i)))))
                              end
                             ()) ())
                             (fn x_f =>
                               let
                                 val x_g = plus_nat one_nat a1;
                               in
                                 (fn () =>
                                   (if not (equal_nata x_g bib)
                                     then Inr (x_g, x_f)
                                     else Inl
    (mkp_raw_err "Parsed beyond end" NONE NONE)))
                               end))
                     end)
                   (Inr (bia, (false, bi))) ();
             in
               (case a of Inl x1a => (fn () => (Inl x1a))
                 | Inr x2a =>
                   (fn f_ => fn () => f_
                     (let
                        val (a1, (a1a, a2a)) = let
         val (a1, aa) = x2a;
       in
         (plus_nat one_nat a1, aa)
       end;
                      in
                        (fn f_ => fn () => f_
                          ((heap_WHILET
                             (fn (a1b, _) =>
                               (fn f_ => fn () => f_ ((nth heap_int ai a1b) ())
                                 ())
                                 (fn xa =>
                                   (fn () =>
                                     (not (equal_int xa zero_int) andalso
                                       true))))
                             (fn (a1b, a2b) =>
                               (fn f_ => fn () => f_ ((nth heap_int ai a1b) ())
                                 ())
                                 (fn x_d =>
                                   (fn f_ => fn () => f_
                                     ((unset_var_impl ((nat o abs_int) x_d) a2b)
                                     ()) ())
                                     (fn x_f =>
                                       (fn () => (plus_nat one_nat a1b, x_f)))))
                             (bia, a2a))
                          ()) ())
                          (fn x_c =>
                            (fn () => (a1, (a1a, let
           val (_, b) = x_c;
         in
           b
         end))))
                      end
                     ()) ())
                     (fn x_c => (fn () => (Inr x_c))))
                 ()
             end)
      else (fn () => (Inl (mkp_raw_err "Parsed beyond end" NONE NONE)))))
    x;

fun read_cnf_new3a x =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val xa = assignment_empty_impl ();
      val a =
        heap_WHILET
          (fn a =>
            (case a of Inl _ => (fn () => false)
              | Inr (a1, _) => (fn () => (not (equal_nata a1 bib)))))
          (fn s =>
            let
              val (a1, (a1a, (a1b, a2b))) = projr s;
            in
              (fn f_ => fn () => f_ ((read_clause_check_taut3a ai bib a1 a2b)
                ()) ())
                (fn a =>
                  (case a of Inl x1a => (fn () => (Inl x1a))
                    | Inr x2a =>
                      (fn f_ => fn () => f_
                        ((case x2a
                           of (a1c, (true, a2d)) =>
                             (fn () =>
                               (a1c, (a1a, (plus_nat a1b one_nat, a2d))))
                           | (a1c, (false, a2d)) =>
                             (fn f_ => fn () => f_ ((add_clause3a ai a1b a1 a1a)
                               ()) ())
                               (fn x_e =>
                                 (fn () =>
                                   (a1c, (x_e, (plus_nat a1b one_nat, a2d))))))
                        ()) ())
                        (fn x_d => (fn () => (Inr x_d)))))
            end)
          (Inr (bia, (bi, (one_nat, xa)))) ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr x2a => (fn () => (Inr let
                                      val (a1, (_, _)) = let
                   val (_, b) = x2a;
                 in
                   b
                 end;
                                    in
                                      a1
                                    end)))
        ()
    end)
    x;

fun init_rat_counts3a x =
  (fn ai => fn bi => fn () =>
    let
      val a = parse_prf_impl ai bi ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr (a1, a2) =>
          (if equal_int a1 one_int orelse
                (equal_int a1 (Int_of_integer (2 : IntInf.int)) orelse
                  (equal_int a1 (Int_of_integer (3 : IntInf.int)) orelse
                    (equal_int a1 (Int_of_integer (4 : IntInf.int)) orelse
                      (equal_int a1 (Int_of_integer (5 : IntInf.int)) orelse
                        equal_int a1 (Int_of_integer (6 : IntInf.int))))))
            then (if equal_int a1 (Int_of_integer (6 : IntInf.int))
                   then (fn f_ => fn () => f_ ((parse_prf_impl ai a2) ()) ())
                          (fn aa =>
                            (case aa of Inl x1a => (fn () => (Inl x1a))
                              | Inr x2aa =>
                                let
                                  val (a1a, a2a) =
                                    let
                                      val (a1a, a2a) = x2aa;
                                    in
                                      (if equal_int a1a zero_int
then (zero_int, a2a) else (a1a, a2a))
                                    end;
                                in
                                  (fn f_ => fn () => f_
                                    ((new heap_nat
                                       (nat_of_integer (16 : IntInf.int))
                                       zero_nat)
                                    ()) ())
                                    (fn xa =>
                                      (fn f_ => fn () => f_ (creg_empty ()) ())
(fn xaa =>
  (fn f_ => fn () => f_
    ((heap_WHILET
       (fn ab =>
         (case ab of Inl _ => (fn () => false)
           | Inr (_, (a1c, _)) => (fn () => (not (equal_int zero_int a1c)))))
       (fn s =>
         let
           val (a1b, (a1c, a2c)) = projr s;
         in
           (fn f_ => fn () => f_ ((parse_prf_impl ai a2c) ()) ())
             (fn ab =>
               (case ab of Inl x1a => (fn () => (Inl x1a))
                 | Inr (_, a2d) =>
                   (fn f_ => fn () => f_
                     (let
                        val (a1e, a2e) = a1b;
                      in
                        (fn f_ => fn () => f_
                          ((creg_initialize (uminus_int a1c) a2e) ()) ())
                          (fn x_m => (fn () => (a1e, x_m)))
                      end
                     ()) ())
                     (fn x_m =>
                       (fn f_ => fn () => f_ ((parse_prf_impl ai a2d) ()) ())
                         (fn ac =>
                           (case ac of Inl x1a => (fn () => (Inl x1a))
                             | Inr x2ac =>
                               (fn () =>
                                 (Inr let
val (a1e, a2e) =
  let
    val (a1e, a2e) = x2ac;
  in
    (if equal_int a1e zero_int then (zero_int, a2e) else (a1e, a2e))
  end;
                                      in
(x_m, (a1e, a2e))
                                      end)))))))
         end)
       (Inr ((xa, xaa), (a1a, a2a))))
    ()) ())
    (fn ab =>
      (case ab of Inl x1a => (fn () => (Inl x1a))
        | Inr x2ab => (fn () => (Inr let
                                       val (a1b, ac) = x2ab;
                                       val (_, ad) = ac;
                                     in
                                       (a1b, ad)
                                     end))))))
                                end))
                   else (fn () =>
                          (Inl (mkp_raw_err "Expected RAT counts item" NONE
                                 (SOME a2)))))
            else (fn () =>
                   (Inl (mkp_raw_err "Invalid item type" (SOME a1)
                          (SOME a2))))))
        ()
    end)
    x;

fun verify_unsat3a x =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val a = init_rat_counts3a bid bi ();
    in
      (case a of Inl x1a => (fn () => (Inl x1a))
        | Inr (a1, a2) =>
          (fn f_ => fn () => f_ ((read_cnf_new3a ai bib bic a1) ()) ())
            (fn aa =>
              (case aa of Inl x1a => (fn () => (Inl x1a))
                | Inr x2aa =>
                  (fn f_ => fn () => f_ (assignment_empty_impl ()) ())
                    (fn xa =>
                      (fn f_ => fn () => f_
                        ((heap_WHILET
                           (fn ab =>
                             (case ab of Inl _ => (fn () => false)
                               | Inr x2ab => (fn () => (not (is_None x2ab)))))
                           (fn s => let
                                      val (a1a, ab) = the (projr s);
                                      val (ac, b) = ab;
                                    in
                                      check_item3a ai bid a1a ac b
                                    end)
                           (Inr (SOME ((x2aa, xa), (bia, a2)))))
                        ()) ())
                        (fn ab =>
                          (case ab of Inl x1a => (fn () => (Inl x1a))
                            | Inr _ => (fn () => (Inr ()))))))))
        ()
    end)
    x;

fun verify_unsat_impl_wrapper dBi f_end it =
  (fn () =>
    let
      val lenDBi = len heap_int dBi ();
    in
      (if less_nat zero_nat f_end andalso
            (less_eq_nat f_end lenDBi andalso
              (less_nat zero_nat it andalso less_eq_nat it lenDBi))
        then verify_unsat3 dBi f_end one_nat f_end it
        else (fn () => (Inl ("Invalid arguments", (NONE, NONE)))))
        ()
    end);

fun verify_unsat_split_impl_wrapper dBi prf_next f_end it prf =
  (fn () =>
    let
      val lenDBi = len heap_int dBi ();
    in
      (if less_nat zero_nat f_end andalso
            (less_eq_nat f_end lenDBi andalso
              (less_nat zero_nat it andalso less_eq_nat it lenDBi))
        then verify_unsat3a dBi prf_next one_nat f_end it prf
        else (fn () => (Inl ("Invalid arguments", (NONE, NONE)))))
        ()
    end);

end; (*struct Grat_Check*)
