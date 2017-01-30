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

structure CDCL_Non_Cached_List : sig
  type nat
  type 'a literal
  type ('a, 'b, 'c) annotated_lit
  val cdcl_twl_stgy_prog_l_impl :
    (nat literal, nat literal, nat) annotated_lit list *
      ((nat literal list) list *
        (nat *
          ((nat literal list) option *
            ((nat literal list) list *
              ((nat literal list) list * (nat list * nat literal list)))))) ->
      (unit ->
        ((nat literal, nat literal, nat) annotated_lit list *
          ((nat literal list) list *
            (nat *
              ((nat literal list) option *
                ((nat literal list) list *
                  ((nat literal list) list *
                    (nat list * nat literal list))))))))
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype 'a literal = Pos of 'a | Neg of 'a;

fun eq A_ a b = equal A_ a b;

fun equal_literala A_ (Pos x1) (Neg x2) = false
  | equal_literala A_ (Neg x2) (Pos x1) = false
  | equal_literala A_ (Neg x2) (Neg y2) = eq A_ x2 y2
  | equal_literala A_ (Pos x1) (Pos y1) = eq A_ x1 y1;

fun equal_literal A_ = {equal = equal_literala A_} : 'a literal equal;

datatype num = One | Bit0 of num | Bit1 of num;

datatype 'a multiset = Mset of 'a list;

datatype ('a, 'b, 'c) annotated_lit = Decided of 'a | Propagated of 'b * 'c;

fun id x = (fn xa => xa) x;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat (0 : IntInf.int);

fun nth (x :: xs) n =
  (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun find uu [] = NONE
  | find p (x :: xs) = (if p x then SOME x else find p xs);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun funpow n f =
  (if equal_nata n zero_nat then id else f o funpow (minus_nat n one_nat) f);

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun hd (x21 :: x22) = x21;

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun remove1 A_ x [] = []
  | remove1 A_ x (y :: xs) = (if eq A_ x y then xs else y :: remove1 A_ x xs);

fun list_update [] i y = []
  | list_update (x :: xs) i y =
    (if equal_nata i zero_nat then y :: xs
      else x :: list_update xs (minus_nat i one_nat) y);

fun swap l i j = list_update (list_update l i (nth l j)) j (nth l i);

fun dropWhile p [] = []
  | dropWhile p (x :: xs) = (if p x then dropWhile p xs else x :: xs);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun add_mset x (Mset xs) = Mset (x :: xs);

fun the (SOME x2) = x2;

fun op_list_hd x = hd x;

fun op_list_tl x = tl x;

fun op_list_get x = nth x;

fun op_list_set x = list_update x;

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

fun is_decided (Decided x1) = true
  | is_decided (Propagated (x21, x22)) = false;

fun lit_of (Decided l) = l
  | lit_of (Propagated (l, uu)) = l;

fun size_list x = gen_length zero_nat x;

fun atm_of (Pos x1) = x1
  | atm_of (Neg x2) = x2;

fun get_level A_ s l =
  size_list
    (filter is_decided
      (dropWhile (fn sa => not (eq A_ (atm_of (lit_of sa)) (atm_of l))) s));

fun op_list_swap x = swap x;

fun count A_ (Mset xs) x =
  fold (fn y => (if eq A_ x y then suc else id)) xs zero_nat;

val zero_multiset : 'a multiset = Mset [];

fun replicate_mset n x = funpow n (add_mset x) zero_multiset;

fun op_list_concat x = (fn a => x @ a);

fun op_list_length x = size_list x;

fun op_list_prepend x = (fn a => x :: a);

fun count_decided l = size_list (filter is_decided l);

fun op_list_contains A_ = (fn x => fn l => member A_ l x);

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

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun is_None a = (case a of NONE => true | SOME _ => false);

fun is_pos (Pos x1) = true
  | is_pos (Neg x2) = false;

fun heap_WHILET b f s =
  (fn () =>
    let
      val bv = b s ();
    in
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s))
        ()
    end);

fun union_mset_list A_ xs ys =
  let
    val (a, b) =
      fold (fn x => fn (ysa, zs) => (remove1 A_ x ysa, x :: zs)) xs (ys, []);
  in
    a @ b
  end;

fun maximum_level_code A_ [] uu = zero_nat
  | maximum_level_code A_ (l :: ls) m =
    max ord_nat (get_level A_ m l) (maximum_level_code A_ ls m);

fun get_maximum_level A_ m (Mset d) = maximum_level_code A_ d m;

fun bt_cut i (Propagated (uu, uv) :: ls) = bt_cut i ls
  | bt_cut i (Decided k :: ls) =
    (if equal_nata (count_decided ls) i then SOME (Decided k :: ls)
      else bt_cut i ls)
  | bt_cut i [] = NONE;

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

fun minus_multiset A_ (Mset xs) (Mset ys) = Mset (fold (remove1 A_) ys xs);

fun find_level_decomp A_ m [] d k = NONE
  | find_level_decomp A_ m (l :: ls) d k =
    let
      val (i, j) = (get_level A_ m l, maximum_level_code A_ (d @ ls) m);
    in
      (if equal_nata i k andalso less_nat j i then SOME (l, j)
        else find_level_decomp A_ m ls (l :: d) k)
    end;

fun uminus_literal l = (if is_pos l then Neg else Pos) (atm_of l);

fun atm_of_impl l = (case l of Pos k => k | Neg k => k);

fun lit_of_impl l = (case l of Decided k => k | Propagated (k, _) => k);

fun op_Decided x = Decided x;

fun nat_lit_eq_cases k l =
  (case (k, l) of (Pos ka, Pos a) => equal_nata ka a | (Pos _, Neg _) => false
    | (Neg _, Pos _) => false | (Neg ka, Neg a) => equal_nata ka a);

fun option_bool_eq_impl la l =
  (if is_None la then (if is_None l then true else false)
    else (if is_None l then false else equal_bool (the la) (the l)));

fun valued_impl x =
  (fn ai => fn bi =>
    imp_nfoldli ai (fn sigma => (fn () => (option_bool_eq_impl sigma NONE)))
      (fn xa => fn _ =>
        (fn () =>
          (if nat_lit_eq_cases bi (lit_of_impl xa) then SOME true
            else (if equal_nata (atm_of_impl bi) (atm_of_impl (lit_of_impl xa))
                   then SOME false else NONE))))
      NONE)
    x;

fun lit_and_ann_of_propagated (Propagated (l, c)) = (l, c);

fun find_decomp_l x =
  (fn (m, (_, (_, (d, (_, (_, (_, _))))))) => fn _ =>
    let
      val j =
        snd (the (find_level_decomp equal_nat m (the d) [] (count_decided m)));
      val a = tl (the (bt_cut j m));
    in
      (fn () => a)
    end)
    x;

fun op_Propagated x = (fn a => Propagated (x, a));

fun op_uminus_lit x = uminus_literal x;

fun get_clauses_ll (m, (n, (u, (d, (np, (up, (ws, q))))))) = n;

fun get_conflict_ll (uu, (uv, (uw, (d, (ux, (uy, (uz, va))))))) = d;

fun hd_of_pending_l x = (fn (_, a) => let
val (_, aa) = a;
val (_, ab) = aa;
val (_, ac) = ab;
val (_, ad) = ac;
val (_, ae) = ad;
val (_, af) = ae;
                                      in
hd af
                                      end)
                          x;

fun clause_to_update_l l s =
  filter
    (fn c =>
      equal_literala equal_nat (nth (nth (get_clauses_ll s) c) zero_nat)
        l orelse
        equal_literala equal_nat (nth (nth (get_clauses_ll s) c) one_nat) l)
    (upt one_nat (size_list (get_clauses_ll s)));

fun tl_of_pending_l x =
  (fn (m, (n, (u, (d, (np, (up, (ws, q))))))) =>
    (m, (n, (u, (d, (np, (up, (clause_to_update_l (hd q)
                                 (m, (n, (u, (d, (np, (up, (ws, q))))))),
                                tl q))))))))
    x;

fun find_lit_of_max_level_l x =
  (fn (m, (_, (_, (d, (_, (_, (_, _))))))) => fn l =>
    (fn () =>
      (the (find (fn la =>
                   equal_nata (get_level equal_nat m la)
                     (get_maximum_level equal_nat m
                       (minus_multiset (equal_literal equal_nat) (Mset (the d))
                         (add_mset (uminus_literal l) zero_multiset))))
             (the d)))))
    x;

fun backtrack_l_impl x =
  (fn (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) =>
    let
      val x_a = lit_of_impl (op_list_hd a1);
    in
      (fn () =>
        let
          val x_c =
            find_decomp_l (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f)))))))
              x_a ();
        in
          (if less_nat one_nat (op_list_length (the a1c))
            then (fn f_ => fn () => f_
                   ((find_lit_of_max_level_l
                      (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) x_a)
                   ()) ())
                   (fn x_e =>
                     (fn () =>
                       (op_list_prepend
                          (op_Propagated (op_uminus_lit x_a)
                            (op_list_length a1a))
                          x_c,
                         (op_list_concat a1a
                            (op_list_prepend
                              (op_list_concat
                                (op_list_prepend (op_uminus_lit x_a)
                                  (op_list_prepend x_e []))
                                (remove1 (equal_literal equal_nat)
                                  (op_uminus_lit x_a)
                                  (remove1 (equal_literal equal_nat) x_e
                                    (the a1c))))
                              []),
                           (a1b, (NONE, (a1d, (a1e, (a1f, [x_a])))))))))
            else (fn () =>
                   (op_list_prepend (op_Propagated (op_uminus_lit x_a) zero_nat)
                      x_c,
                     (a1a, (a1b, (NONE,
                                   (a1d, (the a1c :: a1e, (a1f, [x_a])))))))))
            ()
        end)
    end)
    x;

fun find_unwatched_impl x =
  (fn ai => fn bi =>
    heap_WHILET
      (fn (a1, a2) =>
        (fn () =>
          (option_bool_eq_impl a1 NONE andalso
            less_nat a2 (op_list_length bi))))
      (fn (_, a2) => fn () =>
        let
          val x_a = valued_impl ai (op_list_get bi a2) ();
        in
          (case x_a of NONE => (SOME false, a2) | SOME true => (SOME true, a2)
            | SOME false => (NONE, plus_nat a2 one_nat))
        end)
      (NONE, nat_of_integer (2 : IntInf.int)))
    x;

fun find_unassigned_lit_l_impl x =
  (fn xi => fn () =>
    let
      val a =
        let
          val (a1, (a1a, (_, (_, (_, (_, (_, _))))))) = xi;
        in
          heap_WHILET
            (fn (a1g, a2g) =>
              (fn () =>
                (is_None a2g andalso less_nat a1g (op_list_length a1a))))
            (fn (a1g, _) =>
              (fn f_ => fn () => f_
                ((heap_WHILET
                   (fn (a1h, a2h) =>
                     (fn () =>
                       (is_None a2h andalso
                         less_nat a1h (op_list_length (op_list_get a1a a1g)))))
                   (fn (a1h, _) =>
                     (fn f_ => fn () => f_
                       ((valued_impl a1 (op_list_get (op_list_get a1a a1g) a1h))
                       ()) ())
                       (fn x_b =>
                         (fn () =>
                           (if option_bool_eq_impl x_b NONE
                             then (a1h, SOME
  (op_list_get (op_list_get a1a a1g) a1h))
                             else (plus_nat a1h one_nat, NONE)))))
                   (zero_nat, NONE))
                ()) ())
                (fn (_, a2h) =>
                  (fn () =>
                    (if is_None a2h then (plus_nat a1g one_nat, NONE)
                      else (a1g, a2h)))))
            (one_nat, NONE)
        end
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

fun decide_l_or_skip_impl x =
  (fn xi => fn () =>
    let
      val xa = find_unassigned_lit_l_impl xi ();
    in
      (if not (is_None xa)
        then let
               val (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, _))))))) = xi;
               val x_c = the xa;
             in
               (fn () =>
                 (false,
                   (op_list_prepend (op_Decided x_c) a1,
                     (a1a, (a1b, (a1c, (a1d,
 (a1e, (a1f, [op_uminus_lit x_c])))))))))
             end
        else (fn () => (true, xi)))
        ()
    end)
    x;

fun hd_of_working_queue_l x =
  (fn (_, (_, (_, (_, (_, (_, (ws, _))))))) => hd ws) x;

fun tl_of_working_queue_l x =
  (fn (m, (n, (u, (d, (np, (up, (ws, q))))))) =>
    (m, (n, (u, (d, (np, (up, (tl ws, q))))))))
    x;

fun skip_and_resolve_loop_l_impl x =
  (fn xi => fn () =>
    let
      val a =
        heap_WHILET
          (fn (a1, a2) =>
            (fn () =>
              (if not a1 then not (is_decided (op_list_hd (fst a2)))
                else false)))
          (fn (_, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, a2g)))))))) =>
            let
              val x_b =
                the (get_conflict_ll
                      (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, a2g))))))));
            in
              (fn () =>
                let
                  val (a1h, a2h) =
                    lit_and_ann_of_propagated
                      (op_list_hd
                        (fst (a1a, (a1b, (a1c,
   (a1d, (a1e, (a1f, (a1g, a2g)))))))));
                in
                  (if not (op_list_contains (equal_literal equal_nat)
                            (op_uminus_lit a1h) x_b)
                    then (false,
                           (op_list_tl a1a,
                             (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, a2g))))))))
                    else (if equal_nata
                               (maximum_level_code equal_nat
                                 (remove1 (equal_literal equal_nat)
                                   (op_uminus_lit a1h) x_b)
                                 a1a)
                               (count_decided a1a)
                           then (is_Nil
                                   (union_mset_list (equal_literal equal_nat)
                                     (remove1 (equal_literal equal_nat)
                                       (op_uminus_lit a1h) x_b)
                                     (remove1 (equal_literal equal_nat) a1h
                                       (if equal_nata a2h zero_nat
 then op_list_prepend a1h [] else op_list_get a1b a2h))),
                                  (op_list_tl a1a,
                                    (a1b, (a1c,
    (SOME (union_mset_list (equal_literal equal_nat)
            (remove1 (equal_literal equal_nat) (op_uminus_lit a1h) x_b)
            (remove1 (equal_literal equal_nat) a1h
              (if equal_nata a2h zero_nat then op_list_prepend a1h []
                else op_list_get a1b a2h))),
      (a1e, (a1f, (a1g, a2g))))))))
                           else (true,
                                  (a1a, (a1b,
  (a1c, (a1d, (a1e, (a1f, (a1g, a2g))))))))))
                end)
            end)
          ((if not (is_None (get_conflict_ll xi))
             then is_Nil (the (get_conflict_ll xi)) else false),
            xi)
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

fun cdcl_twl_o_prog_l_impl x =
  (fn xi =>
    (if is_None (get_conflict_ll xi) then decide_l_or_skip_impl xi
      else (fn () =>
             let
               val x_a = skip_and_resolve_loop_l_impl xi ();
             in
               (if not (if not (is_None (get_conflict_ll x_a))
                         then is_Nil (the (get_conflict_ll x_a)) else false)
                 then (fn f_ => fn () => f_ ((backtrack_l_impl x_a) ()) ())
                        (fn x_c => (fn () => (false, x_c)))
                 else (fn () => (true, x_a)))
                 ()
             end)))
    x;

fun unit_propagation_inner_loop_l_impl x =
  (fn ai =>
    heap_WHILET
      (fn s =>
        (fn () => (not (is_Nil ((fst o snd o snd o snd o snd o snd o snd) s)))))
      (fn s =>
        let
          val (a1, a2) = (tl_of_working_queue_l s, hd_of_working_queue_l s);
          val (a1g, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))) = a1;
          val x_a =
            (if nat_lit_eq_cases (op_list_get (op_list_get a1a a2) zero_nat) ai
              then zero_nat else one_nat);
          val x_e = op_list_get (op_list_get a1a a2) (minus_nat one_nat x_a);
        in
          (fn () =>
            let
              val x_g = valued_impl a1g x_e ();
            in
              (if option_bool_eq_impl x_g (SOME true)
                then (fn () =>
                       (a1g, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))))
                else (fn f_ => fn () => f_
                       ((find_unwatched_impl a1g (op_list_get a1a a2)) ()) ())
                       (fn x_i =>
                         (fn () =>
                           (if option_bool_eq_impl (fst x_i) NONE
                             then (if option_bool_eq_impl x_g (SOME false)
                                    then (a1g,
   (a1a, (a1b, (SOME (op_list_get a1a a2), (a1d, (a1e, ([], [])))))))
                                    else (op_list_prepend (op_Propagated x_e a2)
    a1g,
   (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, op_uminus_lit x_e :: a2f))))))))
                             else (a1g, (op_list_set a1a a2
   (op_list_swap (op_list_get a1a a2) x_a (snd x_i)),
  (a1b, (a1c, (a1d, (a1e, (a1f, a2f)))))))))))
                ()
            end)
        end))
    x;

fun unit_propagation_outer_loop_l_impl x =
  heap_WHILET
    (fn s =>
      (fn () => (not (is_Nil ((snd o snd o snd o snd o snd o snd o snd) s)))))
    (fn s => let
               val (a1, a2) = (tl_of_pending_l s, hd_of_pending_l s);
             in
               unit_propagation_inner_loop_l_impl a2 a1
             end)
    x;

fun cdcl_twl_stgy_prog_l_impl x =
  (fn xi => fn () =>
    let
      val a =
        heap_WHILET (fn (a1, _) => (fn () => (not a1)))
          (fn (_, a2) =>
            (fn f_ => fn () => f_ ((unit_propagation_outer_loop_l_impl a2) ())
              ())
              cdcl_twl_o_prog_l_impl)
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

end; (*struct CDCL_Non_Cached_List*)
