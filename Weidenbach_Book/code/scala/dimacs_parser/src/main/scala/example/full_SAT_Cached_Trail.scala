package example

object Heap {
  def bind[A, B](f: Unit => A, g: A => Unit => B): Unit => B = (_: Unit) => g (f ()) ()
}

class Ref[A](x: A) {
  var value = x
}

object Ref {
  def apply[A](x: A): Ref[A] =
    new Ref[A](x)
  def lookup[A](r: Ref[A]): A =
    r.value
  def update[A](r: Ref[A], x: A): Unit =
    { r.value = x }
}

object Array {
  import collection.mutable.ArraySeq
  def alloc[A](n: BigInt)(x: A): ArraySeq[A] =
    ArraySeq.fill(n.toInt)(x)
  def make[A](n: BigInt)(f: BigInt => A): ArraySeq[A] =
    ArraySeq.tabulate(n.toInt)((k: Int) => f(BigInt(k)))
  def len[A](a: ArraySeq[A]): BigInt =
    BigInt(a.length)
  def nth[A](a: ArraySeq[A], n: BigInt): A =
    a(n.toInt)
  def upd[A](a: ArraySeq[A], n: BigInt, x: A): Unit =
    a.update(n.toInt, x)
  def freeze[A](a: ArraySeq[A]): List[A] =
    a.toList
}


object Uint32 {

def less(x: Int, y: Int) : Boolean =
  if (x < 0) y < 0 && x < y
  else y < 0 || x < y

def less_eq(x: Int, y: Int) : Boolean =
  if (x < 0) y < 0 && x <= y
  else y < 0 || x <= y

def set_bit(x: Int, n: BigInt, b: Boolean) : Int =
  if (b)
    x | (1 << n.intValue)
  else
    x & (1 << n.intValue).unary_~

def shiftl(x: Int, n: BigInt) : Int = x << n.intValue

def shiftr(x: Int, n: BigInt) : Int = x >>> n.intValue

def shiftr_signed(x: Int, n: BigInt) : Int = x >> n.intValue

def test_bit(x: Int, n: BigInt) : Boolean =
  (x & (1 << n.intValue)) != 0

} /* object Uint32 */

object Bits_Integer {

def setBit(x: BigInt, n: BigInt, b: Boolean) : BigInt =
  if (n.isValidInt)
    if (b)
      x.setBit(n.toInt)
    else
      x.clearBit(n.toInt)
  else
    sys.error("Bit index too large: " + n.toString)

def shiftl(x: BigInt, n: BigInt) : BigInt =
  if (n.isValidInt)
    x << n.toInt
  else
    sys.error("Shift index too large: " + n.toString)

def shiftr(x: BigInt, n: BigInt) : BigInt =
  if (n.isValidInt)
    x << n.toInt
  else
    sys.error("Shift index too large: " + n.toString)

def testBit(x: BigInt, n: BigInt) : Boolean =
  if (n.isValidInt)
    x.testBit(n.toInt) 
  else
    sys.error("Bit index too large: " + n.toString)

} /* object Bits_Integer */

object SAT_Solver {

abstract sealed class int
final case class int_of_integer(a: BigInt) extends int

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def one_inta: int = int_of_integer(BigInt(1))

trait one[A] {
  val `SAT_Solver.one`: A
}
def one[A](implicit A: one[A]): A = A.`SAT_Solver.one`
object one {
  implicit def `SAT_Solver.one_int`: one[int] = new one[int] {
    val `SAT_Solver.one` = one_inta
  }
}

def integer_of_int(x0: int): BigInt = x0 match {
  case int_of_integer(k) => k
}

def times_inta(k: int, l: int): int =
  int_of_integer(integer_of_int(k) * integer_of_int(l))

trait times[A] {
  val `SAT_Solver.times`: (A, A) => A
}
def times[A](a: A, b: A)(implicit A: times[A]): A = A.`SAT_Solver.times`(a, b)
object times {
  implicit def `SAT_Solver.times_int`: times[int] = new times[int] {
    val `SAT_Solver.times` = (a: int, b: int) => times_inta(a, b)
  }
}

trait power[A] extends one[A] with times[A] {
}
object power {
  implicit def `SAT_Solver.power_int`: power[int] = new power[int] {
    val `SAT_Solver.times` = (a: int, b: int) => times_inta(a, b)
    val `SAT_Solver.one` = one_inta
  }
}

abstract sealed class nat
final case class Nat(a: BigInt) extends nat

def integer_of_nat(x0: nat): BigInt = x0 match {
  case Nat(x) => x
}

def equal_nata(m: nat, n: nat): Boolean = integer_of_nat(m) == integer_of_nat(n)

trait equal[A] {
  val `SAT_Solver.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean =
  A.`SAT_Solver.equal`(a, b)
object equal {
  implicit def `SAT_Solver.equal_bool`: equal[Boolean] = new equal[Boolean] {
    val `SAT_Solver.equal` = (a: Boolean, b: Boolean) => equal_boola(a, b)
  }
  implicit def `SAT_Solver.equal_nat`: equal[nat] = new equal[nat] {
    val `SAT_Solver.equal` = (a: nat, b: nat) => equal_nata(a, b)
  }
}

abstract sealed class typerepa
final case class Typerep(a: String, b: List[typerepa]) extends typerepa

abstract sealed class char
final case class zero_char() extends char
final case class Char(a: num) extends char

abstract sealed class itself[A]
final case class typea[A]() extends itself[A]

def typerep_nata(t: itself[nat]): typerepa = Typerep("Nat.nat", Nil)

trait typerep[A] {
  val `SAT_Solver.typerep`: (itself[A]) => typerepa
}
def typerep[A](a: itself[A])(implicit A: typerep[A]): typerepa =
  A.`SAT_Solver.typerep`(a)
object typerep {
  implicit def `SAT_Solver.typerep_unit`: typerep[Unit] = new typerep[Unit] {
    val `SAT_Solver.typerep` = (a: itself[Unit]) => typerep_unita(a)
  }
  implicit def
    `SAT_Solver.typerep_prod`[A : typerep, B : typerep]: typerep[(A, B)] = new
    typerep[(A, B)] {
    val `SAT_Solver.typerep` = (a: itself[(A, B)]) => typerep_proda[A, B](a)
  }
  implicit def `SAT_Solver.typerep_option`[A : typerep]: typerep[Option[A]] =
    new typerep[Option[A]] {
    val `SAT_Solver.typerep` = (a: itself[Option[A]]) => typerep_optiona[A](a)
  }
  implicit def
    `SAT_Solver.typerep_array`[A : typerep]:
      typerep[collection.mutable.ArraySeq[A]]
    = new typerep[collection.mutable.ArraySeq[A]] {
    val `SAT_Solver.typerep` = (a: itself[collection.mutable.ArraySeq[A]]) =>
      typerep_arraya[A](a)
  }
  implicit def `SAT_Solver.typerep_list`[A : typerep]: typerep[List[A]] = new
    typerep[List[A]] {
    val `SAT_Solver.typerep` = (a: itself[List[A]]) => typerep_lista[A](a)
  }
  implicit def `SAT_Solver.typerep_bool`: typerep[Boolean] = new
    typerep[Boolean] {
    val `SAT_Solver.typerep` = (a: itself[Boolean]) => typerep_boola(a)
  }
  implicit def `SAT_Solver.typerep_nat`: typerep[nat] = new typerep[nat] {
    val `SAT_Solver.typerep` = (a: itself[nat]) => typerep_nata(a)
  }
}

trait countable[A] {
}
object countable {
  implicit def `SAT_Solver.countable_unit`: countable[Unit] = new
    countable[Unit] {
  }
  implicit def
    `SAT_Solver.countable_prod`[A : countable, B : countable]: countable[(A, B)]
    = new countable[(A, B)] {
  }
  implicit def
    `SAT_Solver.countable_option`[A : countable]: countable[Option[A]] = new
    countable[Option[A]] {
  }
  implicit def
    `SAT_Solver.countable_array`[A]: countable[collection.mutable.ArraySeq[A]] =
    new countable[collection.mutable.ArraySeq[A]] {
  }
  implicit def `SAT_Solver.countable_list`[A : countable]: countable[List[A]] =
    new countable[List[A]] {
  }
  implicit def `SAT_Solver.countable_bool`: countable[Boolean] = new
    countable[Boolean] {
  }
  implicit def `SAT_Solver.countable_nat`: countable[nat] = new countable[nat] {
  }
}

trait heap[A] extends countable[A] with typerep[A] {
}
object heap {
  implicit def `SAT_Solver.heap_unit`: heap[Unit] = new heap[Unit] {
    val `SAT_Solver.typerep` = (a: itself[Unit]) => typerep_unita(a)
  }
  implicit def `SAT_Solver.heap_prod`[A : heap, B : heap]: heap[(A, B)] = new
    heap[(A, B)] {
    val `SAT_Solver.typerep` = (a: itself[(A, B)]) => typerep_proda[A, B](a)
  }
  implicit def `SAT_Solver.heap_option`[A : heap]: heap[Option[A]] = new
    heap[Option[A]] {
    val `SAT_Solver.typerep` = (a: itself[Option[A]]) => typerep_optiona[A](a)
  }
  implicit def
    `SAT_Solver.heap_array`[A : typerep]: heap[collection.mutable.ArraySeq[A]] =
    new heap[collection.mutable.ArraySeq[A]] {
    val `SAT_Solver.typerep` = (a: itself[collection.mutable.ArraySeq[A]]) =>
      typerep_arraya[A](a)
  }
  implicit def `SAT_Solver.heap_list`[A : heap]: heap[List[A]] = new
    heap[List[A]] {
    val `SAT_Solver.typerep` = (a: itself[List[A]]) => typerep_lista[A](a)
  }
  implicit def `SAT_Solver.heap_bool`: heap[Boolean] = new heap[Boolean] {
    val `SAT_Solver.typerep` = (a: itself[Boolean]) => typerep_boola(a)
  }
  implicit def `SAT_Solver.heap_nat`: heap[nat] = new heap[nat] {
    val `SAT_Solver.typerep` = (a: itself[nat]) => typerep_nata(a)
  }
}

def zero_nata: nat = Nat(BigInt(0))

trait zero[A] {
  val `SAT_Solver.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`SAT_Solver.zero`
object zero {
  implicit def `SAT_Solver.zero_nat`: zero[nat] = new zero[nat] {
    val `SAT_Solver.zero` = zero_nata
  }
}

def default_nata: nat = zero_nata

trait default[A] {
  val `SAT_Solver.default`: A
}
def default[A](implicit A: default[A]): A = A.`SAT_Solver.default`
object default {
  implicit def `SAT_Solver.default_nat`: default[nat] = new default[nat] {
    val `SAT_Solver.default` = default_nata
  }
}

def less_eq_nat(m: nat, n: nat): Boolean =
  integer_of_nat(m) <= integer_of_nat(n)

trait ord[A] {
  val `SAT_Solver.less_eq`: (A, A) => Boolean
  val `SAT_Solver.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`SAT_Solver.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`SAT_Solver.less`(a, b)
object ord {
  implicit def `SAT_Solver.ord_integer`: ord[BigInt] = new ord[BigInt] {
    val `SAT_Solver.less_eq` = (a: BigInt, b: BigInt) => a <= b
    val `SAT_Solver.less` = (a: BigInt, b: BigInt) => a < b
  }
  implicit def `SAT_Solver.ord_nat`: ord[nat] = new ord[nat] {
    val `SAT_Solver.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
    val `SAT_Solver.less` = (a: nat, b: nat) => less_nat(a, b)
  }
}

def less_nat(m: nat, n: nat): Boolean = integer_of_nat(m) < integer_of_nat(n)

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def nat_of_integer(k: BigInt): nat = Nat(max[BigInt](BigInt(0), k))

def def_hashmap_size_nat: (itself[nat]) => nat =
  ((_: itself[nat]) => nat_of_integer(BigInt(16)))

trait hashable[A] {
  val `SAT_Solver.hashcode`: A => Int
  val `SAT_Solver.def_hashmap_size`: (itself[A]) => nat
}
def hashcode[A](a: A)(implicit A: hashable[A]): Int = A.`SAT_Solver.hashcode`(a)
def def_hashmap_size[A](a: itself[A])(implicit A: hashable[A]): nat =
  A.`SAT_Solver.def_hashmap_size`(a)
object hashable {
  implicit def `SAT_Solver.hashable_nat`: hashable[nat] = new hashable[nat] {
    val `SAT_Solver.hashcode` = (a: nat) => hashcode_nat(a)
    val `SAT_Solver.def_hashmap_size` = (a: itself[nat]) =>
      def_hashmap_size_nat.apply(a)
  }
}

def int_of_nat(n: nat): int = int_of_integer(integer_of_nat(n))

def uint32_of_int(i: int): Int = (integer_of_int(i)).intValue

def hashcode_nat(n: nat): Int = uint32_of_int(int_of_nat(n))

def equal_boola(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

def typerep_boola(t: itself[Boolean]): typerepa = Typerep("HOL.bool", Nil)

def typerep_lista[A : typerep](t: itself[List[A]]): typerepa =
  Typerep("List.list", List(typerep[A](typea[A]())))

def typerep_arraya[A : typerep](t: itself[collection.mutable.ArraySeq[A]]):
      typerepa
  =
  Typerep("Heap.array", List(typerep[A](typea[A]())))

def typerep_optiona[A : typerep](t: itself[Option[A]]): typerepa =
  Typerep("Option.option", List(typerep[A](typea[A]())))

def typerep_proda[A : typerep, B : typerep](t: itself[(A, B)]): typerepa =
  Typerep("Product_Type.prod",
           List(typerep[A](typea[A]()), typerep[B](typea[B]())))

def typerep_unita(t: itself[Unit]): typerepa = Typerep("Product_Type.unit", Nil)

abstract sealed class hashtable[A, B]
final case class
  HashTable[A, B](a: collection.mutable.ArraySeq[(List[(A, B)])], b: nat)
  extends hashtable[A, B]

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

def nat(k: int): nat = Nat(max[BigInt](BigInt(0), integer_of_int(k)))

def plus_nat(m: nat, n: nat): nat = Nat(integer_of_nat(m) + integer_of_nat(n))

def one_nat: nat = Nat(BigInt(1))

def Suc(n: nat): nat = plus_nat(n, one_nat)

def comp[A, B, C](f: A => B, g: C => A): C => B = ((x: C) => f(g(x)))

def minus_nat(m: nat, n: nat): nat =
  Nat(max[BigInt](BigInt(0), integer_of_nat(m) - integer_of_nat(n)))

def nth[A](x0: List[A], n: nat): A = (x0, n) match {
  case (x :: xs, n) =>
    (if (equal_nata(n, zero_nata)) x else nth[A](xs, minus_nat(n, one_nat)))
}

def len[A : heap](a: collection.mutable.ArraySeq[A]): (Unit => nat) =
  ((b: Unit) => {
                  val (): Unit = b
                  val i: BigInt = ((_: Unit) => Array.len(a)).apply(());
                  nat_of_integer(i)
                })

def newa[A : heap]: nat => A => (Unit => collection.mutable.ArraySeq[A]) =
  comp[BigInt, A => (Unit => collection.mutable.ArraySeq[A]),
        nat](((a: BigInt) => (b: A) => (_: Unit) =>  Array.alloc(a)(b)),
              ((a: nat) => integer_of_nat(a)))

def ntha[A : heap](a: collection.mutable.ArraySeq[A], n: nat): (Unit => A) =
  (_: Unit) => Array.nth(a, integer_of_nat(n))

def upd[A : heap](i: nat, x: A, a: collection.mutable.ArraySeq[A]):
      (Unit => collection.mutable.ArraySeq[A])
  =
  ((b: Unit) => {
                  val (): Unit = b;
                  ((_: Unit) => Array.upd(a, integer_of_nat(i), x)).apply(());
                  a
                })

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def nulla[A](x0: List[A]): Boolean = x0 match {
  case Nil => true
  case x :: xs => false
}

def make[A : heap](n: nat, f: nat => A):
      (Unit => collection.mutable.ArraySeq[A])
  =
  (_: Unit) =>
    Array.make(integer_of_nat(n))(comp[nat, A,
BigInt](f, ((a: BigInt) => nat_of_integer(a))))

def hd[A](x0: List[A]): A = x0 match {
  case x21 :: x22 => x21
}

def tl[A](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x21 :: x22 => x22
}

def gen_length[A](n: nat, x1: List[A]): nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Suc(n), xs)
  case (n, Nil) => n
}

def size_list[A]: (List[A]) => nat =
  ((a: List[A]) => gen_length[A](zero_nata, a))

def of_list[A : heap](xs: List[A]): (Unit => collection.mutable.ArraySeq[A]) =
  make[A](size_list[A].apply(xs), ((a: nat) => nth[A](xs, a)))

def replicate[A](n: nat, x: A): List[A] =
  (if (equal_nata(n, zero_nata)) Nil
    else x :: replicate[A](minus_nat(n, one_nat), x))

def is_none[A](x0: Option[A]): Boolean = x0 match {
  case Some(x) => false
  case None => true
}

def blit[A : heap](src: collection.mutable.ArraySeq[A], si: nat,
                    dst: collection.mutable.ArraySeq[A], di: nat, len: nat):
      (Unit => Unit)
  =
  { (_: Unit) =>
    
    def safecopy(src: Array[_], srci: Int, dst: Array[_], dsti: Int, len: Int) = {
      if (src eq dst)
        sys.error("array_blit: Same arrays")
      else
        System.arraycopy(src, srci, dst, dsti, len)
    }
    safecopy(src.array,(integer_of_nat(si)).toInt,dst.array,(integer_of_nat(di)).toInt,(integer_of_nat(len)).toInt)
  }

def ht_new_sz[A : hashable : heap, B : heap](n: nat):
      (Unit => (hashtable[A, B]))
  =
  {
    val l: List[List[(A, B)]] = replicate[List[(A, B)]](n, Nil);
    ((a: Unit) =>
      {
        val (): Unit = a
        val aa: collection.mutable.ArraySeq[(List[(A, B)])] =
          (of_list[List[(A, B)]](l)).apply(());
        HashTable[A, B](aa, zero_nata)
      })
  }

def ht_new[A : hashable : heap, B : heap]: (Unit => (hashtable[A, B])) =
  ht_new_sz[A, B](def_hashmap_size[A](typea[A]()))

def sgn_integer(k: BigInt): BigInt =
  (if (k == BigInt(0)) BigInt(0)
    else (if (k < BigInt(0)) BigInt(-1) else BigInt(1)))

def apsnd[A, B, C](f: A => B, x1: (C, A)): (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

def divmod_integer(k: BigInt, l: BigInt): (BigInt, BigInt) =
  (if (k == BigInt(0)) (BigInt(0), BigInt(0))
    else (if (l == BigInt(0)) (BigInt(0), k)
           else (comp[BigInt, ((BigInt, BigInt)) => (BigInt, BigInt),
                       BigInt](comp[BigInt => BigInt,
                                     ((BigInt, BigInt)) => (BigInt, BigInt),
                                     BigInt](((a: BigInt => BigInt) =>
       (b: (BigInt, BigInt)) => apsnd[BigInt, BigInt, BigInt](a, b)),
      ((a: BigInt) => (b: BigInt) => a * b)),
                                ((a: BigInt) =>
                                  sgn_integer(a)))).apply(l).apply((if (sgn_integer(k) ==
                                  sgn_integer(l))
                             ((k: BigInt) => (l: BigInt) => if (l == 0)
                               (BigInt(0), k) else
                               (k.abs /% l.abs)).apply(k).apply(l)
                             else {
                                    val (r, s): (BigInt, BigInt) =
                                      ((k: BigInt) => (l: BigInt) => if (l == 0)
(BigInt(0), k) else (k.abs /% l.abs)).apply(k).apply(l);
                                    (if (s == BigInt(0)) ((- r), BigInt(0))
                                      else ((- r) - BigInt(1), l.abs - s))
                                  }))))

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

def modulo_integer(k: BigInt, l: BigInt): BigInt =
  snd[BigInt, BigInt](divmod_integer(k, l))

def modulo_nat(m: nat, n: nat): nat =
  Nat(modulo_integer(integer_of_nat(m), integer_of_nat(n)))

def test_bit_uint32(x: Int, n: nat): Boolean =
  less_nat(n, nat_of_integer(BigInt(32))) &&
    Uint32.test_bit(x, integer_of_nat(n))

def integer_of_uint32(n: Int): BigInt =
  (if (test_bit_uint32(n, nat_of_integer(BigInt(31))))
    BigInt(n & BigInt(2147483647).intValue) | BigInt("2147483648")
    else BigInt(n))

def nat_of_uint32(x: Int): nat = nat_of_integer(integer_of_uint32(x))

def nat_of_hashcode: Int => nat = ((a: Int) => nat_of_uint32(a))

def bounded_hashcode_nat[A : hashable](n: nat, x: A): nat =
  modulo_nat(nat_of_hashcode.apply(hashcode[A](x)), n)

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def the_array[A, B](x0: hashtable[A, B]):
      collection.mutable.ArraySeq[(List[(A, B)])]
  =
  x0 match {
  case HashTable(a, uu) => a
}

def ls_update[A : equal, B](k: A, v: B, x2: List[(A, B)]):
      (List[(A, B)], Boolean)
  =
  (k, v, x2) match {
  case (k, v, Nil) => (List((k, v)), false)
  case (k, v, (l, w) :: ls) =>
    (if (eq[A](k, l)) ((k, v) :: ls, true)
      else {
             val r: (List[(A, B)], Boolean) = ls_update[A, B](k, v, ls);
             ((l, w) :: fst[List[(A, B)], Boolean](r),
               snd[List[(A, B)], Boolean](r))
           })
}

def the_size[A, B](x0: hashtable[A, B]): nat = x0 match {
  case HashTable(uu, n) => n
}

def ht_upd[A : equal : hashable : heap,
            B : heap](k: A, v: B, ht: hashtable[A, B]):
      (Unit => (hashtable[A, B]))
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val m: nat = (len[List[(A, B)]](the_array[A, B](ht))).apply(());
      ({
         val i: nat = bounded_hashcode_nat[A](m, k);
         Heap.bind[List[(A, B)],
                    hashtable[A, B]](ntha[List[(A, B)]](the_array[A, B](ht), i),
                                      ((l: List[(A, B)]) =>
{
  val la: (List[(A, B)], Boolean) = ls_update[A, B](k, v, l);
  Heap.bind[collection.mutable.ArraySeq[(List[(A, B)])],
             hashtable[A, B]](upd[List[(A,
 B)]](i, fst[List[(A, B)], Boolean](la), the_array[A, B](ht)),
                               ((_: collection.mutable.ArraySeq[(List[(A, B)])])
                                  =>
                                 {
                                   val n: nat =
                                     (if (snd[List[(A, B)], Boolean](la))
                                       the_size[A, B](ht)
                                       else Suc(the_size[A, B](ht)));
                                   (_: Unit) =>
                                     (HashTable[A, B](the_array[A, B](ht), n))
                                 }))
}))
       })(())
    })

def the[A](x0: Option[A]): A = x0 match {
  case Some(x2) => x2
}

def ht_insls[A : equal : hashable : heap,
              B : heap](x0: List[(A, B)], ht: hashtable[A, B]):
      (Unit => (hashtable[A, B]))
  =
  (x0, ht) match {
  case (Nil, ht) => (_: Unit) => ht
  case ((k, v) :: l, ht) =>
    ((a: Unit) =>
      {
        val (): Unit = a
        val x: hashtable[A, B] = (ht_upd[A, B](k, v, ht)).apply(());
        (ht_insls[A, B](l, x)).apply(())
      })
}

def ht_copy[A : equal : hashable : heap,
             B : heap](n: nat, src: hashtable[A, B], dst: hashtable[A, B]):
      (Unit => (hashtable[A, B]))
  =
  (if (equal_nata(n, zero_nata)) (_: Unit) => dst
    else ((a: Unit) =>
           {
             val (): Unit = a
             val l: List[(A, B)] =
               (ntha[List[(A, B)]](the_array[A, B](src),
                                    minus_nat(n, one_nat))).apply(())
             val x: hashtable[A, B] = (ht_insls[A, B](l, dst)).apply(());
             (ht_copy[A, B](minus_nat(n, one_nat), src, x)).apply(())
           }))

def divide_integer(k: BigInt, l: BigInt): BigInt =
  fst[BigInt, BigInt](divmod_integer(k, l))

def divide_int(k: int, l: int): int =
  int_of_integer(divide_integer(integer_of_int(k), integer_of_int(l)))

def power[A : power](a: A, n: nat): A =
  (if (equal_nata(n, zero_nata)) one[A]
    else times[A](a, power[A](a, minus_nat(n, one_nat))))

def shiftr_nat(x: nat, n: nat): nat =
  nat(divide_int(int_of_nat(x), power[int](int_of_integer(BigInt(2)), n)))

def shiftr1(n: nat): nat = shiftr_nat(n, one_nat)

def times_nat(m: nat, n: nat): nat = Nat(integer_of_nat(m) * integer_of_nat(n))

def load_factor: nat = nat_of_integer(BigInt(75))

def ht_rehash[A : equal : hashable : heap, B : heap](ht: hashtable[A, B]):
      (Unit => (hashtable[A, B]))
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val n: nat = (len[List[(A, B)]](the_array[A, B](ht))).apply(())
      val x: hashtable[A, B] =
        (ht_new_sz[A, B](times_nat(nat_of_integer(BigInt(2)), n))).apply(());
      (ht_copy[A, B](n, ht, x)).apply(())
    })

def ht_update[A : equal : hashable : heap,
               B : heap](k: A, v: B, ht: hashtable[A, B]):
      (Unit => (hashtable[A, B]))
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val m: nat = (len[List[(A, B)]](the_array[A, B](ht))).apply(())
      val x: hashtable[A, B] =
        (if (less_eq_nat(times_nat(m, load_factor),
                          times_nat(the_size[A, B](ht),
                                     nat_of_integer(BigInt(100)))))
          ht_rehash[A, B](ht) else (_: Unit) => ht)(());
      (ht_upd[A, B](k, v, x)).apply(())
    })

def hs_ins[A : equal : hashable : heap](x: A, ht: hashtable[A, Unit]):
      (Unit => (hashtable[A, Unit]))
  =
  ht_update[A, Unit](x, (), ht)

def hs_new[A : hashable : heap]: (Unit => (hashtable[A, Unit])) =
  ht_new[A, Unit]

def ls_lookup[A : equal, B](x: A, xa1: List[(A, B)]): Option[B] = (x, xa1) match
  {
  case (x, Nil) => None
  case (x, (k, v) :: l) =>
    (if (eq[A](x, k)) Some[B](v) else ls_lookup[A, B](x, l))
}

def ht_lookup[A : equal : hashable : heap, B : heap](x: A, ht: hashtable[A, B]):
      (Unit => Option[B])
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val m: nat = (len[List[(A, B)]](the_array[A, B](ht))).apply(());
      ({
         val i: nat = bounded_hashcode_nat[A](m, x);
         Heap.bind[List[(A, B)],
                    Option[B]](ntha[List[(A, B)]](the_array[A, B](ht), i),
                                ((l: List[(A, B)]) =>
                                  (_: Unit) => (ls_lookup[A, B](x, l))))
       })(())
    })

def op_list_hd[A]: (List[A]) => A = ((a: List[A]) => hd[A](a))

def op_list_tl[A]: (List[A]) => List[A] = ((a: List[A]) => tl[A](a))

def array_grow[A : heap](a: collection.mutable.ArraySeq[A], s: nat, x: A):
      (Unit => collection.mutable.ArraySeq[A])
  =
  ((b: Unit) =>
    {
      val (): Unit = b
      val l: nat = (len[A](a)).apply(());
      (if (equal_nata(l, s)) (_: Unit) => a
        else Heap.bind[collection.mutable.ArraySeq[A],
                        collection.mutable.ArraySeq[A]](newa[A].apply(s).apply(x),
                 ((aa: collection.mutable.ArraySeq[A]) =>
                   Heap.bind[Unit,
                              collection.mutable.ArraySeq[A]](blit[A](a,
                               zero_nata, aa, zero_nata, l),
                       ((_: Unit) => (_: Unit) => aa)))))(())
    })

def hs_memb[A : equal : hashable : heap](x: A, s: hashtable[A, Unit]):
      (Unit => Boolean)
  =
  ((a: Unit) => {
                  val (): Unit = a
                  val r: Option[Unit] = (ht_lookup[A, Unit](x, s)).apply(());
                  (r match {
                     case None => false
                     case Some(_) => true
                   })
                })

def op_list_get[A]: (List[A]) => nat => A =
  ((a: List[A]) => (b: nat) => nth[A](a, b))

def array_copy[A : heap](a: collection.mutable.ArraySeq[A]):
      (Unit => collection.mutable.ArraySeq[A])
  =
  ((b: Unit) =>
    {
      val (): Unit = b
      val l: nat = (len[A](a)).apply(());
      (if (equal_nata(l, zero_nata)) of_list[A](Nil)
        else Heap.bind[A, collection.mutable.ArraySeq[A]](ntha[A](a, zero_nata),
                   ((s: A) =>
                     Heap.bind[collection.mutable.ArraySeq[A],
                                collection.mutable.ArraySeq[A]](newa[A].apply(l).apply(s),
                         ((aa: collection.mutable.ArraySeq[A]) =>
                           Heap.bind[Unit,
                                      collection.mutable.ArraySeq[A]](blit[A](a,
                                       zero_nata, aa, zero_nata, l),
                               ((_: Unit) => (_: Unit) => aa)))))))(())
    })

def arl_get[A : heap]:
      ((collection.mutable.ArraySeq[A], nat)) => nat => (Unit => A)
  =
  ((a: (collection.mutable.ArraySeq[A], nat)) =>
    {
      val (aa, _): (collection.mutable.ArraySeq[A], nat) = a;
      ((b: nat) => ntha[A](aa, b))
    })

def nth_aa[A : heap](xs: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A],
               nat))],
                      i: nat, j: nat):
      (Unit => A)
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val x: (collection.mutable.ArraySeq[A], nat) =
        (ntha[(collection.mutable.ArraySeq[A], nat)](xs, i)).apply(())
      val xa: A = arl_get[A].apply(x).apply(j).apply(());
      xa
    })

def array_shrink[A : heap](a: collection.mutable.ArraySeq[A], s: nat):
      (Unit => collection.mutable.ArraySeq[A])
  =
  ((b: Unit) =>
    {
      val (): Unit = b
      val l: nat = (len[A](a)).apply(());
      (if (equal_nata(l, s)) (_: Unit) => a
        else (if (equal_nata(l, zero_nata)) of_list[A](Nil)
               else Heap.bind[A, collection.mutable.ArraySeq[A]](ntha[A](a,
                                  zero_nata),
                          ((x: A) =>
                            Heap.bind[collection.mutable.ArraySeq[A],
                                       collection.mutable.ArraySeq[A]](newa[A].apply(s).apply(x),
                                ((aa: collection.mutable.ArraySeq[A]) =>
                                  Heap.bind[Unit,
     collection.mutable.ArraySeq[A]](blit[A](a, zero_nata, aa, zero_nata, s),
                                      ((_: Unit) => (_: Unit) => aa))))))))(())
    })

def nth_rl[A : heap](xs: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
                           nat),
                      n: nat):
      (Unit => collection.mutable.ArraySeq[A])
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val x: collection.mutable.ArraySeq[A] =
        arl_get[collection.mutable.ArraySeq[A]].apply(xs).apply(n).apply(());
      (array_copy[A](x)).apply(())
    })

def arl_set[A : heap]:
      ((collection.mutable.ArraySeq[A], nat)) =>
        nat => A => (Unit => ((collection.mutable.ArraySeq[A], nat)))
  =
  ((a: (collection.mutable.ArraySeq[A], nat)) =>
    {
      val (aa, n): (collection.mutable.ArraySeq[A], nat) = a;
      ((i: nat) => (x: A) => (b: Unit) =>
        {
          val (): Unit = b
          val ab: collection.mutable.ArraySeq[A] = (upd[A](i, x, aa)).apply(());
          (ab, n)
        })
    })

def imp_for[A](i: nat, u: nat, f: nat => A => (Unit => A), s: A): (Unit => A) =
  (if (less_eq_nat(u, i)) (_: Unit) => s
    else ((a: Unit) => {
                         val (): Unit = a
                         val x: A = ((f(i))(s))(());
                         (imp_for[A](plus_nat(i, one_nat), u, f, x)).apply(())
                       }))

def arl_last[A : heap]: ((collection.mutable.ArraySeq[A], nat)) => (Unit => A) =
  ((a: (collection.mutable.ArraySeq[A], nat)) =>
    {
      val (aa, n): (collection.mutable.ArraySeq[A], nat) = a;
      ntha[A](aa, minus_nat(n, one_nat))
    })

def last_aa[A : heap](xs: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A],
                nat))],
                       i: nat):
      (Unit => A)
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val x: (collection.mutable.ArraySeq[A], nat) =
        (ntha[(collection.mutable.ArraySeq[A], nat)](xs, i)).apply(());
      arl_last[A].apply(x).apply(())
    })

def nth_raa[A : heap](xs: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
                            nat),
                       i: nat, j: nat):
      (Unit => A)
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val x: collection.mutable.ArraySeq[A] =
        arl_get[collection.mutable.ArraySeq[A]].apply(xs).apply(i).apply(())
      val xa: A = (ntha[A](x, j)).apply(());
      xa
    })

def update_raa[A : default : heap](a: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
nat),
                                    i: nat, j: nat, y: A):
      (Unit =>
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]], nat)))
  =
  ((b: Unit) =>
    {
      val (): Unit = b
      val x: collection.mutable.ArraySeq[A] =
        arl_get[collection.mutable.ArraySeq[A]].apply(a).apply(i).apply(())
      val xa: collection.mutable.ArraySeq[A] = (upd[A](j, y, x)).apply(());
      arl_set[collection.mutable.ArraySeq[A]].apply(a).apply(i).apply(xa).apply(())
    })

def swap_aa[A : default : heap](xs: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
                                      nat),
                                 k: nat, i: nat, j: nat):
      (Unit =>
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]], nat)))
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val xi: A = (nth_raa[A](xs, k, i)).apply(())
      val xj: A = (nth_raa[A](xs, k, j)).apply(())
      val xsa: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
                 nat)
        = (update_raa[A](xs, k, i, xj)).apply(())
      val x: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]], nat)
        = (update_raa[A](xsa, k, j, xi)).apply(());
      x
    })

def arl_copy[A : heap, B]:
      ((collection.mutable.ArraySeq[A], B)) =>
        (Unit => ((collection.mutable.ArraySeq[A], B)))
  =
  ((a: (collection.mutable.ArraySeq[A], B)) =>
    {
      val (aa, n): (collection.mutable.ArraySeq[A], B) = a;
      ((b: Unit) =>
        {
          val (): Unit = b
          val ab: collection.mutable.ArraySeq[A] =
            (array_copy[A](aa)).apply(());
          (ab, n)
        })
    })

def arl_swap[A : heap]:
      ((collection.mutable.ArraySeq[A], nat)) =>
        nat => nat => (Unit => ((collection.mutable.ArraySeq[A], nat)))
  =
  ((ai: (collection.mutable.ArraySeq[A], nat)) => (bia: nat) => (bi: nat) =>
    (a: Unit) =>
    {
      val (): Unit = a
      val x: A = arl_get[A].apply(ai).apply(bia).apply(())
      val x_a: A = arl_get[A].apply(ai).apply(bi).apply(())
      val x_b: (collection.mutable.ArraySeq[A], nat) =
        arl_set[A].apply(ai).apply(bia).apply(x_a).apply(());
      arl_set[A].apply(x_b).apply(bi).apply(x).apply(())
    })

def op_list_length[A]: (List[A]) => nat = size_list[A]

def initial_capacity: nat = nat_of_integer(BigInt(16))

def arl_empty[A : default : heap, B : zero]:
      (Unit => ((collection.mutable.ArraySeq[A], B)))
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val aa: collection.mutable.ArraySeq[A] =
        newa[A].apply(initial_capacity).apply(default[A]).apply(());
      (aa, zero[B])
    })

def op_list_prepend[A]: A => (List[A]) => List[A] =
  ((a: A) => (b: List[A]) => a :: b)

def arl_length[A : heap]:
      ((collection.mutable.ArraySeq[A], nat)) => (Unit => nat)
  =
  ((a: (collection.mutable.ArraySeq[A], nat)) =>
    {
      val (_, aa): (collection.mutable.ArraySeq[A], nat) = a;
      (_: Unit) => aa
    })

def length_aa[A : heap](xs: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A],
                  nat))],
                         i: nat):
      (Unit => nat)
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val x: (collection.mutable.ArraySeq[A], nat) =
        (ntha[(collection.mutable.ArraySeq[A], nat)](xs, i)).apply(());
      arl_length[A].apply(x).apply(())
    })

def update_aa[A : heap](a: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A],
                 nat))],
                         i: nat, j: nat, y: A):
      (Unit =>
        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A], nat))])
  =
  ((b: Unit) =>
    {
      val (): Unit = b
      val x: (collection.mutable.ArraySeq[A], nat) =
        (ntha[(collection.mutable.ArraySeq[A], nat)](a, i)).apply(())
      val aa: (collection.mutable.ArraySeq[A], nat) =
        arl_set[A].apply(x).apply(j).apply(y).apply(());
      (upd[(collection.mutable.ArraySeq[A], nat)](i, aa, a)).apply(())
    })

def length_ra[A : heap](xs: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
                              nat)):
      (Unit => nat)
  =
  arl_length[collection.mutable.ArraySeq[A]].apply(xs)

def arl_append[A : default : heap]:
      ((collection.mutable.ArraySeq[A], nat)) =>
        A => (Unit => ((collection.mutable.ArraySeq[A], nat)))
  =
  ((a: (collection.mutable.ArraySeq[A], nat)) =>
    {
      val (aa, n): (collection.mutable.ArraySeq[A], nat) = a;
      ((x: A) => (b: Unit) =>
        {
          val (): Unit = b
          val lena: nat = (len[A](aa)).apply(());
          (if (less_nat(n, lena))
            Heap.bind[collection.mutable.ArraySeq[A],
                       (collection.mutable.ArraySeq[A],
                         nat)](upd[A](n, x, aa),
                                ((ab: collection.mutable.ArraySeq[A]) =>
                                  (_: Unit) => (ab, plus_nat(n, one_nat))))
            else {
                   val newcap: nat = times_nat(nat_of_integer(BigInt(2)), lena);
                   Heap.bind[collection.mutable.ArraySeq[A],
                              (collection.mutable.ArraySeq[A],
                                nat)](array_grow[A](aa, newcap, default[A]),
                                       ((ab: collection.mutable.ArraySeq[A]) =>
 Heap.bind[collection.mutable.ArraySeq[A],
            (collection.mutable.ArraySeq[A],
              nat)](upd[A](n, x, ab),
                     ((ac: collection.mutable.ArraySeq[A]) =>
                       (_: Unit) => (ac, plus_nat(n, one_nat))))))
                 })(())
        })
    })

def op_list_is_empty[A]: (List[A]) => Boolean = ((a: List[A]) => nulla[A](a))

def imp_nfoldli[A, B](x0: List[A], c: B => (Unit => Boolean),
                       f: A => B => (Unit => B), s: B):
      (Unit => B)
  =
  (x0, c, f, s) match {
  case (x :: ls, c, f, s) =>
    ((a: Unit) =>
      {
        val (): Unit = a
        val b: Boolean = (c(s))(());
        (if (b)
          Heap.bind[B, B]((f(x))(s),
                           ((aa: B) => imp_nfoldli[A, B](ls, c, f, aa)))
          else (_: Unit) => s)(())
      })
  case (Nil, c, f, s) => (_: Unit) => s
}

def is_Nil[A](a: List[A]): Boolean = (a match {
case Nil => true
case _ :: _ => false
                                      })

def minimum_capacity: nat = nat_of_integer(BigInt(16))

def arl_butlast[A : heap]:
      ((collection.mutable.ArraySeq[A], nat)) =>
        (Unit => ((collection.mutable.ArraySeq[A], nat)))
  =
  ((a: (collection.mutable.ArraySeq[A], nat)) =>
    {
      val (aa, n): (collection.mutable.ArraySeq[A], nat) = a
      val na: nat = minus_nat(n, one_nat);
      ((b: Unit) =>
        {
          val (): Unit = b
          val lena: nat = (len[A](aa)).apply(());
          (if (less_nat(times_nat(na, nat_of_integer(BigInt(4))), lena) &&
                 less_eq_nat(minimum_capacity,
                              times_nat(na, nat_of_integer(BigInt(2)))))
            Heap.bind[collection.mutable.ArraySeq[A],
                       (collection.mutable.ArraySeq[A],
                         nat)](array_shrink[A](aa,
        times_nat(na, nat_of_integer(BigInt(2)))),
                                ((ab: collection.mutable.ArraySeq[A]) =>
                                  (_: Unit) => (ab, na)))
            else (_: Unit) => (aa, na))(())
        })
    })

def is_None[A](a: Option[A]): Boolean = (a match {
   case None => true
   case Some(_) => false
 })

def arl_is_empty[A : heap]:
      ((collection.mutable.ArraySeq[A], nat)) => (Unit => Boolean)
  =
  ((a: (collection.mutable.ArraySeq[A], nat)) =>
    {
      val (_, n): (collection.mutable.ArraySeq[A], nat) = a;
      (_: Unit) => (equal_nata(n, zero_nata))
    })

def heap_WHILET[A](b: A => (Unit => Boolean), f: A => (Unit => A), s: A):
      (Unit => A)
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val bv: Boolean = (b(s))(());
      (if (bv) Heap.bind[A, A](f(s), ((aa: A) => heap_WHILET[A](b, f, aa)))
        else (_: Unit) => s)(())
    })

def append_el_aa[A : default : heap]:
      collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A], nat))] =>
        nat =>
          A => (Unit =>
                 collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A],
       nat))])
  =
  ((a: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A], nat))]) =>
    (i: nat) => (x: A) => (b: Unit) =>
    {
      val (): Unit = b
      val j: (collection.mutable.ArraySeq[A], nat) =
        (ntha[(collection.mutable.ArraySeq[A], nat)](a, i)).apply(())
      val aa: (collection.mutable.ArraySeq[A], nat) =
        arl_append[A].apply(j).apply(x).apply(());
      (upd[(collection.mutable.ArraySeq[A], nat)](i, aa, a)).apply(())
    })

def set_butlast_aa[A : heap](a: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A],
                      nat))],
                              i: nat):
      (Unit =>
        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A], nat))])
  =
  ((b: Unit) =>
    {
      val (): Unit = b
      val x: (collection.mutable.ArraySeq[A], nat) =
        (ntha[(collection.mutable.ArraySeq[A], nat)](a, i)).apply(())
      val aa: (collection.mutable.ArraySeq[A], nat) =
        arl_butlast[A].apply(x).apply(());
      (upd[(collection.mutable.ArraySeq[A], nat)](i, aa, a)).apply(())
    })

def bitAND_int(x0: int, x1: int): int = (x0, x1) match {
  case (int_of_integer(i), int_of_integer(j)) => int_of_integer(i & j)
}

def bitXOR_int(x0: int, x1: int): int = (x0, x1) match {
  case (int_of_integer(i), int_of_integer(j)) => int_of_integer(i ^ j)
}

def arl_of_array_raa[A : heap](xs: collection.mutable.ArraySeq[A]):
      (Unit => ((collection.mutable.ArraySeq[A], nat)))
  =
  ((a: Unit) => {
                  val (): Unit = a
                  val n: nat = (len[A](xs)).apply(());
                  (xs, n)
                })

def array_of_arl_raa[A : heap]:
      ((collection.mutable.ArraySeq[A], nat)) =>
        (Unit => collection.mutable.ArraySeq[A])
  =
  ((a: (collection.mutable.ArraySeq[A], nat)) =>
    {
      val (aa, b): (collection.mutable.ArraySeq[A], nat) = a;
      array_shrink[A](aa, b)
    })

def arrayO_raa_append[A : default : heap]:
      ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]], nat)) =>
        collection.mutable.ArraySeq[A] =>
          (Unit =>
            ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
              nat)))
  =
  ((a: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]], nat)) =>
    {
      val (aa, n):
            (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]], nat)
        = a;
      ((x: collection.mutable.ArraySeq[A]) => (b: Unit) =>
        {
          val (): Unit = b
          val lena: nat = (len[collection.mutable.ArraySeq[A]](aa)).apply(());
          (if (less_nat(n, lena))
            Heap.bind[collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
                       (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
                         nat)](upd[collection.mutable.ArraySeq[A]](n, x, aa),
                                ((ab: collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]])
                                   =>
                                  (_: Unit) => (ab, plus_nat(n, one_nat))))
            else {
                   val newcap: nat = times_nat(nat_of_integer(BigInt(2)), lena);
                   Heap.bind[collection.mutable.ArraySeq[A],
                              (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
                                nat)](newa[A].apply(zero_nata).apply(default[A]),
                                       ((defaulta:
   collection.mutable.ArraySeq[A])
  =>
 Heap.bind[collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
            (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
              nat)](array_grow[collection.mutable.ArraySeq[A]](aa, newcap,
                        defaulta),
                     ((ab: collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]])
                        =>
                       Heap.bind[collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
                                  (collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]],
                                    nat)](upd[collection.mutable.ArraySeq[A]](n,
                                       x, ab),
   ((ac: collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]]) =>
     (_: Unit) => (ac, plus_nat(n, one_nat))))))))
                 })(())
        })
    })

def arrayO_raa_empty_sz[A : default : heap, B : zero](init_cap: nat):
      (Unit =>
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]], B)))
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val defaulta: collection.mutable.ArraySeq[A] =
        newa[A].apply(zero_nata).apply(default[A]).apply(())
      val aa: collection.mutable.ArraySeq[collection.mutable.ArraySeq[A]] =
        newa[collection.mutable.ArraySeq[A]].apply(max[nat](init_cap,
                     minimum_capacity)).apply(defaulta).apply(());
      (aa, zero[B])
    })

def bitAND_nat(i: nat, j: nat): nat =
  nat(bitAND_int(int_of_nat(i), int_of_nat(j)))

def bitXOR_nat(i: nat, j: nat): nat =
  nat(bitXOR_int(int_of_nat(i), int_of_nat(j)))

def equal_option[A : equal](x0: Option[A], x1: Option[A]): Boolean = (x0, x1)
  match {
  case (None, Some(x2)) => false
  case (Some(x2), None) => false
  case (Some(x2), Some(y2)) => eq[A](x2, y2)
  case (None, None) => true
}

def arrayO_ara_empty_sz_code[A : default : heap]:
      nat =>
        (Unit =>
          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A], nat))])
  =
  ((xi: nat) => (a: Unit) =>
    {
      val (): Unit = a
      val x: List[(collection.mutable.ArraySeq[A], nat)] =
        (imp_for[List[(collection.mutable.ArraySeq[A],
                        nat)]](zero_nata, xi,
                                ((_: nat) =>
                                  (sigma:
                                     List[(collection.mutable.ArraySeq[A],
    nat)])
                                    =>
                                  Heap.bind[(collection.mutable.ArraySeq[A],
      nat),
     List[(collection.mutable.ArraySeq[A],
            nat)]](arl_empty[A, nat],
                    ((x_c: (collection.mutable.ArraySeq[A], nat)) =>
                      (_: Unit) => (x_c :: sigma)))),
                                Nil)).apply(());
      (of_list[(collection.mutable.ArraySeq[A], nat)](x)).apply(())
    })

def decided[A, B](l: A): (A, Option[B]) = (l, None)

def propagated[A, B](l: A, c: B): (A, Option[B]) = (l, Some[B](c))

def is_in_arl_code:
      nat => ((collection.mutable.ArraySeq[nat], nat)) => (Unit => Boolean)
  =
  ((ai: nat) => (bi: (collection.mutable.ArraySeq[nat], nat)) => (a: Unit) =>
    {
      val (): Unit = a
      val x: nat =
        (heap_WHILET[nat](((s: nat) =>
                            Heap.bind[nat, Boolean](arl_length[nat].apply(bi),
             ((x: nat) =>
               (if (less_nat(s, x))
                 Heap.bind[nat, Boolean](arl_get[nat].apply(bi).apply(s),
  ((xa: nat) => (_: Unit) => (! (equal_nata(xa, ai)))))
                 else (_: Unit) => false)))),
                           ((s: nat) => (_: Unit) => (plus_nat(s, one_nat))),
                           zero_nata)).apply(())
      val x_a: nat = arl_length[nat].apply(bi).apply(());
      less_nat(x, x_a)
    })

def uminus_lit_imp(l: nat): nat = bitXOR_nat(l, one_nat)

def find_first_eq_code:
      nat => ((collection.mutable.ArraySeq[nat], nat)) => (Unit => nat)
  =
  ((ai: nat) => (bi: (collection.mutable.ArraySeq[nat], nat)) =>
    heap_WHILET[nat](((s: nat) => (a: Unit) =>
                       {
                         val (): Unit = a
                         val x: nat = arl_length[nat].apply(bi).apply(());
                         (if (less_nat(s, x))
                           Heap.bind[nat, Boolean](arl_get[nat].apply(bi).apply(s),
            ((xa: nat) => (_: Unit) => (! (equal_nata(xa, ai)))))
                           else (_: Unit) => false)(())
                       }),
                      ((s: nat) => (_: Unit) => (plus_nat(s, one_nat))),
                      zero_nata))

def remove1_wl_code:
      nat =>
        ((collection.mutable.ArraySeq[nat], nat)) =>
          (Unit => ((collection.mutable.ArraySeq[nat], nat)))
  =
  ((ai: nat) => (bi: (collection.mutable.ArraySeq[nat], nat)) => (a: Unit) =>
    {
      val (): Unit = a
      val x: nat = find_first_eq_code.apply(ai).apply(bi).apply(())
      val x_a: nat = arl_length[nat].apply(bi).apply(());
      (if (equal_nata(x, x_a)) (_: Unit) => bi
        else Heap.bind[(collection.mutable.ArraySeq[nat], nat),
                        (collection.mutable.ArraySeq[nat],
                          nat)](arl_swap[nat].apply(bi).apply(x).apply(minus_nat(x_a,
  one_nat)),
                                 arl_butlast[nat]))(())
    })

def extract_lits_clss_imp_empty_assn:
      (Unit => ((hashtable[nat, Unit], List[nat])))
  =
  ((a: Unit) => {
                  val (): Unit = a
                  val x: hashtable[nat, Unit] = hs_new[nat].apply(());
                  (x, Nil)
                })

def nat_lit_lits_init_assn_assn_prepend:
      nat =>
        ((hashtable[nat, Unit], List[nat])) =>
          (Unit => ((hashtable[nat, Unit], List[nat])))
  =
  ((ai: nat) => (a: (hashtable[nat, Unit], List[nat])) =>
    {
      val (a1, a2): (hashtable[nat, Unit], List[nat]) = a;
      ((b: Unit) =>
        {
          val (): Unit = b
          val x: hashtable[nat, Unit] =
            (hs_ins[nat](shiftr1(ai), a1)).apply(());
          (x, op_list_prepend[nat].apply(ai).apply(a2))
        })
    })

def nat_lit_lits_init_assn_assn_in:
      nat => ((hashtable[nat, Unit], List[nat])) => (Unit => Boolean)
  =
  ((ai: nat) => (a: (hashtable[nat, Unit], List[nat])) =>
    {
      val (a1, _): (hashtable[nat, Unit], List[nat]) = a;
      hs_memb[nat](ai, a1)
    })

def extract_lits_cls_imp:
      (List[nat]) =>
        ((hashtable[nat, Unit], List[nat])) =>
          (Unit => ((hashtable[nat, Unit], List[nat])))
  =
  ((ai: List[nat]) =>
    ((a: (hashtable[nat, Unit], List[nat])) =>
      imp_for[(hashtable[nat, Unit],
                List[nat])](zero_nata, op_list_length[nat].apply(ai),
                             ((xa: nat) =>
                               (sigma: (hashtable[nat, Unit], List[nat])) =>
                               (b: Unit) =>
                               {
                                 val (): Unit = b
                                 val x_b: Boolean =
                                   nat_lit_lits_init_assn_assn_in.apply(shiftr1(op_list_get[nat].apply(ai).apply(xa))).apply(sigma).apply(());
                                 (if (x_b) (_: Unit) => sigma
                                   else nat_lit_lits_init_assn_assn_prepend.apply(op_list_get[nat].apply(ai).apply(xa)).apply(sigma))(())
                               }),
                             a)))

def extract_lits_clss_imp:
      (List[List[nat]]) =>
        ((hashtable[nat, Unit], List[nat])) =>
          (Unit => ((hashtable[nat, Unit], List[nat])))
  =
  ((ai: List[List[nat]]) =>
    ((a: (hashtable[nat, Unit], List[nat])) =>
      imp_for[(hashtable[nat, Unit],
                List[nat])](zero_nata, op_list_length[List[nat]].apply(ai),
                             ((xa: nat) =>
                               extract_lits_cls_imp.apply(op_list_get[List[nat]].apply(ai).apply(xa))),
                             a)))

def extract_lits_clss_imp_list_assn:
      (List[List[nat]]) =>
        ((hashtable[nat, Unit], List[nat])) => (Unit => (List[nat]))
  =
  ((ai: List[List[nat]]) => (bi: (hashtable[nat, Unit], List[nat])) =>
    (a: Unit) =>
    {
      val (): Unit = a
      val x: (hashtable[nat, Unit], List[nat]) =
        extract_lits_clss_imp.apply(ai).apply(bi).apply(());
      snd[hashtable[nat, Unit], List[nat]](x)
    })

def get_conflict_wl_is_None_code:
      (((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
          (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                  (List[List[nat]],
                    (List[List[nat]],
                      (List[nat],
                        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
              nat))])))))))) =>
        (Unit => Boolean)
  =
  ((xi: ((List[(nat, Option[nat])],
           (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))]))))))))
     =>
    (_: Unit) =>
      ({
         val (_, (_, (_, (a1c, (_, (_, (_, _))))))):
               ((List[(nat, Option[nat])],
                  (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                 ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                    nat),
                   (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                           (List[List[nat]],
                             (List[List[nat]],
                               (List[nat],
                                 collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                       nat))])))))))
           = xi;
         is_None[(collection.mutable.ArraySeq[nat], nat)](a1c)
       }))

def hd_select_and_remove_from_pending_wl:
      (((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
          (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                  (List[List[nat]],
                    (List[List[nat]],
                      (List[nat],
                        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
              nat))])))))))) =>
        (Unit =>
          ((((List[(nat, Option[nat])],
               (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                 nat),
                (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                        (List[List[nat]],
                          (List[List[nat]],
                            (List[nat],
                              collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                    nat))]))))))),
            nat)))
  =
  comp[(((List[(nat, Option[nat])],
           (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))]))))))),
         nat),
        (Unit =>
          ((((List[(nat, Option[nat])],
               (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                 nat),
                (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                        (List[List[nat]],
                          (List[List[nat]],
                            (List[nat],
                              collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                    nat))]))))))),
            nat))),
        ((List[(nat, Option[nat])],
           (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))])))))))](((a: (((List[(nat, Option[nat])],
(collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                                       ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
  nat),
 (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
         (List[List[nat]],
           (List[List[nat]],
             (List[nat],
               collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
     nat))]))))))),
                                      nat))
                                  =>
                                 (_: Unit) => a),
                                ((a: ((List[(nat, Option[nat])],
(collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                                       ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
  nat),
 (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
         (List[List[nat]],
           (List[List[nat]],
             (List[nat],
               collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
     nat))]))))))))
                                   =>
                                  {
                                    val (m, (n, (u, (d, (np, (up, (q, w))))))):
  ((List[(nat, Option[nat])],
     (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
              (List[List[nat]],
                (List[List[nat]],
                  (List[nat],
                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
          nat))])))))))
                                      = a;
                                    ((m, (n,
   (u, (d, (np, (up, (tl[nat](q), w))))))),
                                      hd[nat](q))
                                  }))

def cons_trail_Propagated_tr_code:
      nat =>
        nat =>
          ((List[(nat, Option[nat])],
            (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))) =>
            (Unit =>
              ((List[(nat, Option[nat])],
                (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))))
  =
  ((ai: nat) => (bia: nat) =>
    (a: (List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
      =>
    {
      val (a1, (a1a, a2a)):
            (List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))
        = a;
      ((b: Unit) =>
        {
          val (): Unit = b
          val x: collection.mutable.ArraySeq[((Option[Boolean], nat))] =
            (upd[(Option[Boolean],
                   nat)](shiftr1(ai),
                          (Some[Boolean](equal_nata(bitAND_nat(ai, one_nat),
             zero_nata)),
                            a2a),
                          a1a)).apply(());
          (op_list_prepend[(nat, Option[nat])].apply(propagated[nat,
                         nat](ai, bia)).apply(a1),
            (x, a2a))
        })
    })

def delete_index_and_swap_aa[A : heap](xs:
 collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A], nat))],
i: nat, j: nat):
      (Unit =>
        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A], nat))])
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val x: A = (last_aa[A](xs, i)).apply(())
      val xsa: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[A],
     nat))]
        = (update_aa[A](xs, i, j, x)).apply(());
      (set_butlast_aa[A](xsa, i)).apply(())
    })

def valued_trail_code:
      ((List[(nat, Option[nat])],
        (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))) =>
        nat => (Unit => Option[Boolean])
  =
  ((ai: (List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
     =>
    (bi: nat) =>
    {
      val (_, (a1a, _)):
            (List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))
        = ai;
      ((a: Unit) =>
        {
          val (): Unit = a
          val x: (Option[Boolean], nat) =
            (ntha[(Option[Boolean], nat)](a1a, shiftr1(bi))).apply(());
          (fst[Option[Boolean], nat](x) match {
             case None => None
             case Some(x_a) =>
               (if (equal_nata(bitAND_nat(bi, one_nat), zero_nata))
                 Some[Boolean](x_a) else Some[Boolean](! x_a))
           })
        })
    })

def find_unwatched_code:
      ((List[(nat, Option[nat])],
        (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))) =>
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
          nat)) =>
          nat => (Unit => ((Option[Boolean], nat)))
  =
  ((ai: (List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
     =>
    (bia: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat))
      =>
    (bi: nat) =>
    heap_WHILET[(Option[Boolean],
                  nat)](((a: (Option[Boolean], nat)) =>
                          {
                            val (a1, a2): (Option[Boolean], nat) = a;
                            ((b: Unit) =>
                              {
                                val (): Unit = b
                                val x: collection.mutable.ArraySeq[nat] =
                                  (nth_rl[nat](bia, bi)).apply(())
                                val xa: nat = (len[nat](x)).apply(());
                                is_none[Boolean](a1) && less_nat(a2, xa)
                              })
                          }),
                         ((a: (Option[Boolean], nat)) =>
                           {
                             val (_, a2): (Option[Boolean], nat) = a;
                             ((b: Unit) =>
                               {
                                 val (): Unit = b
                                 val x: collection.mutable.ArraySeq[nat] =
                                   (nth_rl[nat](bia, bi)).apply(())
                                 val xa: nat = (ntha[nat](x, a2)).apply(())
                                 val x_a: Option[Boolean] =
                                   valued_trail_code.apply(ai).apply(xa).apply(());
                                 (x_a match {
                                    case None => (Some[Boolean](false), a2)
                                    case Some(true) => (Some[Boolean](true), a2)
                                    case Some(false) =>
                                      (None, plus_nat(a2, one_nat))
                                  })
                               })
                           }),
                         (None, nat_of_integer(BigInt(2)))))

def unit_propagation_inner_loop_body_wl_D_code:
      nat =>
        nat =>
          (((List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
            ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
               nat),
              (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                      (List[List[nat]],
                        (List[List[nat]],
                          (List[nat],
                            collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                  nat))])))))))) =>
            (Unit =>
              ((nat,
                ((List[(nat, Option[nat])],
                   (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                     nat)),
                  ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                     nat),
                    (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                            (List[List[nat]],
                              (List[List[nat]],
                                (List[nat],
                                  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                        nat))]))))))))))
  =
  ((ai: nat) => (bia: nat) =>
    (a: ((List[(nat, Option[nat])],
           (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))]))))))))
      =>
    {
      val (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))):
            ((List[(nat, Option[nat])],
               (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                 nat),
                (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                        (List[List[nat]],
                          (List[List[nat]],
                            (List[nat],
                              collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                    nat))])))))))
        = a;
      ((b: Unit) =>
        {
          val (): Unit = b
          val x_a: nat = (nth_aa[nat](a2f, ai, bia)).apply(())
          val x: nat = (nth_raa[nat](a1a, x_a, zero_nata)).apply(());
          ({
             val x_c: nat = (if (equal_nata(x, ai)) zero_nata else one_nat);
             Heap.bind[nat, (nat, ((List[(nat, Option[nat])],
                                     (collection.mutable.ArraySeq[((Option[Boolean],
                            nat))],
                                       nat)),
                                    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                                       nat),
                                      (nat,
(Option[(collection.mutable.ArraySeq[nat], nat)],
  (List[List[nat]],
    (List[List[nat]],
      (List[nat],
        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                      nat))]))))))))](nth_raa[nat](a1a, x_a,
                            minus_nat(one_nat, x_c)),
               ((x_f: nat) =>
                 Heap.bind[Option[Boolean],
                            (nat, ((List[(nat, Option[nat])],
                                     (collection.mutable.ArraySeq[((Option[Boolean],
                            nat))],
                                       nat)),
                                    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                                       nat),
                                      (nat,
(Option[(collection.mutable.ArraySeq[nat], nat)],
  (List[List[nat]],
    (List[List[nat]],
      (List[nat],
        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                      nat))]))))))))](valued_trail_code.apply(a1).apply(x_f),
               ((x_h: Option[Boolean]) =>
                 (if (equal_option[Boolean](x_h, Some[Boolean](true)))
                   (_: Unit) =>
                     (plus_nat(bia, one_nat),
                       (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))))
                   else Heap.bind[(Option[Boolean], nat),
                                   (nat, ((List[(nat, Option[nat])],
    (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
   ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
     (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
             (List[List[nat]],
               (List[List[nat]],
                 (List[nat],
                   collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
         nat))]))))))))](find_unwatched_code.apply(a1).apply(a1a).apply(x_a),
                          ((x_j: (Option[Boolean], nat)) =>
                            (if (is_none[Boolean](fst[Option[Boolean],
               nat](x_j)))
                              (if (equal_option[Boolean](x_h,
                  Some[Boolean](false)))
                                Heap.bind[collection.mutable.ArraySeq[nat],
   (nat, ((List[(nat, Option[nat])],
            (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
           ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
              nat),
             (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                     (List[List[nat]],
                       (List[List[nat]],
                         (List[nat],
                           collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                 nat))]))))))))](nth_rl[nat](a1a, x_a),
                                  ((xa: collection.mutable.ArraySeq[nat]) =>
                                    Heap.bind[(collection.mutable.ArraySeq[nat],
        nat),
       (nat, ((List[(nat, Option[nat])],
                (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
               ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                  nat),
                 (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                         (List[List[nat]],
                           (List[List[nat]],
                             (List[nat],
                               collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                     nat))]))))))))](arl_of_array_raa[nat](xa),
                                      ((xb:
  (collection.mutable.ArraySeq[nat], nat))
 =>
(_: Unit) =>
  (plus_nat(bia, one_nat),
    (a1, (a1a, (a1b, (Some[(collection.mutable.ArraySeq[nat], nat)](xb),
                       (a1d, (a1e, (Nil, a2f))))))))))))
                                else Heap.bind[(List[(nat, Option[nat])],
         (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        (nat, ((List[(nat, Option[nat])],
                 (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                   nat),
                  (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                          (List[List[nat]],
                            (List[List[nat]],
                              (List[nat],
                                collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                      nat))]))))))))](cons_trail_Propagated_tr_code.apply(x_f).apply(x_a).apply(a1),
                                       ((xa:
   (List[(nat, Option[nat])],
     (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
  =>
 (_: Unit) =>
   (plus_nat(bia, one_nat),
     (xa, (a1a, (a1b, (a1c, (a1d, (a1e, (uminus_lit_imp(x_f) :: a1f,
  a2f)))))))))))
                              else Heap.bind[nat,
      (nat, ((List[(nat, Option[nat])],
               (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                 nat),
                (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                        (List[List[nat]],
                          (List[List[nat]],
                            (List[nat],
                              collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                    nat))]))))))))](nth_raa[nat](a1a, x_a,
          snd[Option[Boolean], nat](x_j)),
                                     ((x_l: nat) =>
                                       Heap.bind[(collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
           nat),
          (nat, ((List[(nat, Option[nat])],
                   (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                     nat)),
                  ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                     nat),
                    (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                            (List[List[nat]],
                              (List[List[nat]],
                                (List[nat],
                                  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                        nat))]))))))))](swap_aa[nat](a1a, x_a, x_c,
              snd[Option[Boolean], nat](x_j)),
 ((x_n: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat)) =>
   Heap.bind[collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
   nat))],
              (nat, ((List[(nat, Option[nat])],
                       (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                         nat)),
                      ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                         nat),
                        (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                                (List[List[nat]],
                                  (List[List[nat]],
                                    (List[nat],
                                      collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                            nat))]))))))))](delete_index_and_swap_aa[nat](a2f,
                                   ai, bia),
     ((x_p: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
  nat))])
        =>
       Heap.bind[collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
       nat))],
                  (nat, ((List[(nat, Option[nat])],
                           (collection.mutable.ArraySeq[((Option[Boolean],
                  nat))],
                             nat)),
                          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                             nat),
                            (nat, (Option[(collection.mutable.ArraySeq[nat],
    nat)],
                                    (List[List[nat]],
                                      (List[List[nat]],
(List[nat],
  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                nat))]))))))))](append_el_aa[nat].apply(x_p).apply(x_l).apply(x_a),
         ((x_r: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
      nat))])
            =>
           (_: Unit) =>
             (bia, (a1, (x_n, (a1b, (a1c, (a1d,
    (a1e, (a1f, x_r))))))))))))))))))))))))
           })(())
        })
    })

def unit_propagation_inner_loop_wl_loop_D_code:
      nat =>
        (((List[(nat, Option[nat])],
            (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))])))))))) =>
          (Unit =>
            ((nat,
              ((List[(nat, Option[nat])],
                 (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                   nat),
                  (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                          (List[List[nat]],
                            (List[List[nat]],
                              (List[nat],
                                collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                      nat))]))))))))))
  =
  ((ai: nat) =>
    (bi: ((List[(nat, Option[nat])],
            (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
           ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
              nat),
             (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                     (List[List[nat]],
                       (List[List[nat]],
                         (List[nat],
                           collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                 nat))]))))))))
      =>
    heap_WHILET[(nat, ((List[(nat, Option[nat])],
                         (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                           nat)),
                        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                           nat),
                          (nat, (Option[(collection.mutable.ArraySeq[nat],
  nat)],
                                  (List[List[nat]],
                                    (List[List[nat]],
                                      (List[nat],
collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                              nat))]))))))))](((a:
          (nat, ((List[(nat, Option[nat])],
                   (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                     nat)),
                  ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                     nat),
                    (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                            (List[List[nat]],
                              (List[List[nat]],
                                (List[nat],
                                  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                        nat))])))))))))
         =>
        {
          val (a1, (_, (_, (_, (a1d, (_, (_, (_, a2g)))))))):
                (nat, ((List[(nat, Option[nat])],
                         (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                           nat)),
                        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                           nat),
                          (nat, (Option[(collection.mutable.ArraySeq[nat],
  nat)],
                                  (List[List[nat]],
                                    (List[List[nat]],
                                      (List[nat],
collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat], nat))]))))))))
            = a;
          ((b: Unit) =>
            {
              val (): Unit = b
              val x: nat = (length_aa[nat](a2g, ai)).apply(());
              less_nat(a1, x) &&
                is_None[(collection.mutable.ArraySeq[nat], nat)](a1d)
            })
        }),
       ((a: (nat, ((List[(nat, Option[nat])],
                     (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                       nat)),
                    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                       nat),
                      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                              (List[List[nat]],
                                (List[List[nat]],
                                  (List[nat],
                                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                          nat))])))))))))
          =>
         {
           val (aa, b):
                 (nat, ((List[(nat, Option[nat])],
                          (collection.mutable.ArraySeq[((Option[Boolean],
                 nat))],
                            nat)),
                         ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                            nat),
                           (nat, (Option[(collection.mutable.ArraySeq[nat],
   nat)],
                                   (List[List[nat]],
                                     (List[List[nat]],
                                       (List[nat],
 collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat], nat))]))))))))
             = a;
           unit_propagation_inner_loop_body_wl_D_code.apply(ai).apply(aa).apply(b)
         }),
       (zero_nata, bi)))

def unit_propagation_inner_loop_wl_D_code:
      nat =>
        (((List[(nat, Option[nat])],
            (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))])))))))) =>
          (Unit =>
            (((List[(nat, Option[nat])],
                (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                 nat),
                (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                        (List[List[nat]],
                          (List[List[nat]],
                            (List[nat],
                              collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                    nat))])))))))))
  =
  ((ai: nat) =>
    (bi: ((List[(nat, Option[nat])],
            (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
           ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
              nat),
             (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                     (List[List[nat]],
                       (List[List[nat]],
                         (List[nat],
                           collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                 nat))]))))))))
      =>
    (a: Unit) =>
    {
      val (): Unit = a
      val x: (nat, ((List[(nat, Option[nat])],
                      (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                        nat)),
                     ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                        nat),
                       (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                               (List[List[nat]],
                                 (List[List[nat]],
                                   (List[nat],
                                     collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                           nat))]))))))))
        = unit_propagation_inner_loop_wl_loop_D_code.apply(ai).apply(bi).apply(());
      snd[nat, ((List[(nat, Option[nat])],
                  (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                 ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                    nat),
                   (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                           (List[List[nat]],
                             (List[List[nat]],
                               (List[nat],
                                 collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                       nat))])))))))](x)
    })

def pending_wll_empty:
      (((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
          (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                  (List[List[nat]],
                    (List[List[nat]],
                      (List[nat],
                        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
              nat))])))))))) =>
        (Unit => Boolean)
  =
  comp[Boolean, (Unit => Boolean),
        ((List[(nat, Option[nat])],
           (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))])))))))](((a: Boolean) => (_: Unit) => a),
                                ((a: ((List[(nat, Option[nat])],
(collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                                       ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
  nat),
 (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
         (List[List[nat]],
           (List[List[nat]],
             (List[nat],
               collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
     nat))]))))))))
                                   =>
                                  {
                                    val (_, (_, (_, (_, (_, (_, (q, _))))))):
  ((List[(nat, Option[nat])],
     (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
              (List[List[nat]],
                (List[List[nat]],
                  (List[nat],
                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
          nat))])))))))
                                      = a;
                                    is_Nil[nat](q)
                                  }))

def unit_propagation_outer_loop_wl_D_code:
      (((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
          (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                  (List[List[nat]],
                    (List[List[nat]],
                      (List[nat],
                        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
              nat))])))))))) =>
        (Unit =>
          (((List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
            ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
               nat),
              (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                      (List[List[nat]],
                        (List[List[nat]],
                          (List[nat],
                            collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                  nat))])))))))))
  =
  ((a: ((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
         ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
           (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                   (List[List[nat]],
                     (List[List[nat]],
                       (List[nat],
                         collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
               nat))]))))))))
     =>
    heap_WHILET[((List[(nat, Option[nat])],
                   (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                     nat)),
                  ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                     nat),
                    (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                            (List[List[nat]],
                              (List[List[nat]],
                                (List[nat],
                                  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                        nat))])))))))](((s:
   ((List[(nat, Option[nat])],
      (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
     ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
       (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
               (List[List[nat]],
                 (List[List[nat]],
                   (List[nat],
                     collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
           nat))]))))))))
  =>
 (b: Unit) => {
                val (): Unit = b
                val x: Boolean = pending_wll_empty.apply(s).apply(());
                ! x
              }),
((s: ((List[(nat, Option[nat])],
        (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
       ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
         (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                 (List[List[nat]],
                   (List[List[nat]],
                     (List[nat],
                       collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
             nat))]))))))))
   =>
  (b: Unit) =>
  {
    val (): Unit = b
    val aa: (((List[(nat, Option[nat])],
                (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
               ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                  nat),
                 (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                         (List[List[nat]],
                           (List[List[nat]],
                             (List[nat],
                               collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                     nat))]))))))),
              nat)
      = hd_select_and_remove_from_pending_wl.apply(s).apply(());
    ({
       val (a1, a2):
             (((List[(nat, Option[nat])],
                 (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                   nat),
                  (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                          (List[List[nat]],
                            (List[List[nat]],
                              (List[nat],
                                collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                      nat))]))))))),
               nat)
         = aa;
       unit_propagation_inner_loop_wl_D_code.apply(a2).apply(a1)
     })(())
  }),
a))

def is_decided_wl_code: ((nat, Option[nat])) => (Unit => Boolean) =
  ((xi: (nat, Option[nat])) =>
    (_: Unit) => (is_None[nat](snd[nat, Option[nat]](xi))))

def is_decided_hd_trail_wll_code:
      (((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
          (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                  (List[List[nat]],
                    (List[List[nat]],
                      (List[nat],
                        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
              nat))])))))))) =>
        (Unit => Boolean)
  =
  ((a: ((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
         ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
           (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                   (List[List[nat]],
                     (List[List[nat]],
                       (List[nat],
                         collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
               nat))]))))))))
     =>
    {
      val (a1, (_, (_, (_, (_, (_, (_, _))))))):
            ((List[(nat, Option[nat])],
               (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                 nat),
                (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                        (List[List[nat]],
                          (List[List[nat]],
                            (List[nat],
                              collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                    nat))])))))))
        = a;
      ((b: Unit) =>
        {
          val (): Unit = b
          val x: (nat, Option[nat]) =
            (comp[List[(nat, Option[nat])], (Unit => ((nat, Option[nat]))),
                   (List[(nat, Option[nat])],
                     (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                       nat))](comp[(nat, Option[nat]),
                                    (Unit => ((nat, Option[nat]))),
                                    List[(nat,
   Option[nat])]](((aa: (nat, Option[nat])) => (_: Unit) => aa),
                   ((aa: List[(nat, Option[nat])]) =>
                     hd[(nat, Option[nat])](aa))),
                               ((aa: (List[(nat, Option[nat])],
                                       (collection.mutable.ArraySeq[((Option[Boolean],
                              nat))],
 nat)))
                                  =>
                                 fst[List[(nat, Option[nat])],
                                      (collection.mutable.ArraySeq[((Option[Boolean],
                             nat))],
nat)](aa)))).apply(a1).apply(());
          is_decided_wl_code.apply(x).apply(())
        })
    })

def get_conflict_wll_is_Nil_code:
      (((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
          (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                  (List[List[nat]],
                    (List[List[nat]],
                      (List[nat],
                        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
              nat))])))))))) =>
        (Unit => Boolean)
  =
  ((a: ((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
         ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
           (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                   (List[List[nat]],
                     (List[List[nat]],
                       (List[nat],
                         collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
               nat))]))))))))
     =>
    {
      val (_, (_, (_, (a1c, (_, (_, (_, _))))))):
            ((List[(nat, Option[nat])],
               (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                 nat),
                (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                        (List[List[nat]],
                          (List[List[nat]],
                            (List[nat],
                              collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                    nat))])))))))
        = a;
      (if (is_None[(collection.mutable.ArraySeq[nat], nat)](a1c))
        (_: Unit) => false
        else (comp[(collection.mutable.ArraySeq[nat], nat), (Unit => Boolean),
                    Option[(collection.mutable.ArraySeq[nat],
                             nat)]](arl_is_empty[nat],
                                     ((aa:
 Option[(collection.mutable.ArraySeq[nat], nat)])
=>
                                       the[(collection.mutable.ArraySeq[nat],
     nat)](aa)))).apply(a1c))
    })

def union_mset_list_fold_code:
      ((collection.mutable.ArraySeq[nat], nat)) =>
        ((collection.mutable.ArraySeq[nat], nat)) =>
          (Unit => ((collection.mutable.ArraySeq[nat], nat)))
  =
  ((ai: (collection.mutable.ArraySeq[nat], nat)) =>
    (bi: (collection.mutable.ArraySeq[nat], nat)) => (a: Unit) =>
    {
      val (): Unit = a
      val x: (collection.mutable.ArraySeq[nat], nat) =
        arl_copy[nat, nat].apply(ai).apply(())
      val xa: nat = arl_length[nat].apply(bi).apply(());
      (imp_for[(collection.mutable.ArraySeq[nat],
                 nat)](zero_nata, xa,
                        ((xb: nat) =>
                          (sigma: (collection.mutable.ArraySeq[nat], nat)) =>
                          Heap.bind[nat, (collection.mutable.ArraySeq[nat],
   nat)](arl_get[nat].apply(bi).apply(xb),
          ((xaa: nat) =>
            Heap.bind[Boolean,
                       (collection.mutable.ArraySeq[nat],
                         nat)](is_in_arl_code.apply(xaa).apply(x),
                                ((x_c: Boolean) =>
                                  (if (x_c) (_: Unit) => sigma
                                    else Heap.bind[nat,
            (collection.mutable.ArraySeq[nat],
              nat)](arl_get[nat].apply(bi).apply(xb),
                     arl_append[nat].apply(sigma)))))))),
                        ai)).apply(())
    })

def get_level_code_get_level_code:
      ((List[(nat, Option[nat])],
        (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))) =>
        nat => (Unit => nat)
  =
  ((ai: (List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
     =>
    (bi: nat) =>
    {
      val (_, (a1a, _)):
            (List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))
        = ai;
      ((a: Unit) =>
        {
          val (): Unit = a
          val x: (Option[Boolean], nat) =
            (ntha[(Option[Boolean], nat)](a1a, shiftr1(bi))).apply(());
          snd[Option[Boolean], nat](x)
        })
    })

def maximum_level_remove_code:
      ((List[(nat, Option[nat])],
        (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))) =>
        ((collection.mutable.ArraySeq[nat], nat)) => nat => (Unit => nat)
  =
  ((ai: (List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
     =>
    (bia: (collection.mutable.ArraySeq[nat], nat)) => (bi: nat) => (a: Unit) =>
    {
      val (): Unit = a
      val x: nat = arl_length[nat].apply(bia).apply(())
      val xa: (Boolean, nat) =
        (imp_for[(Boolean,
                   nat)](zero_nata, x,
                          ((xb: nat) => (aa: (Boolean, nat)) =>
                            {
                              val (a1, a2): (Boolean, nat) = aa;
                              Heap.bind[nat,
 (Boolean,
   nat)](arl_get[nat].apply(bia).apply(xb),
          ((xa: nat) =>
            (if (equal_nata(xa, bi) && ! a1) (_: Unit) => (true, a2)
              else Heap.bind[nat, (Boolean,
                                    nat)](arl_get[nat].apply(bia).apply(xb),
   ((xc: nat) =>
     Heap.bind[nat, (Boolean,
                      nat)](get_level_code_get_level_code.apply(ai).apply(xc),
                             ((xd: nat) =>
                               (_: Unit) => (a1, max[nat](xd, a2)))))))))
                            }),
                          (false, zero_nata))).apply(());
      snd[Boolean, nat](xa)
    })

def tl_trail_tr_code:
      ((List[(nat, Option[nat])],
        (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))) =>
        (Unit =>
          ((List[(nat, Option[nat])],
            (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))))
  =
  ((a: (List[(nat, Option[nat])],
         (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
     =>
    {
      val (a1, (a1a, a2a)):
            (List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))
        = a;
      ((b: Unit) =>
        {
          val (): Unit = b
          val x: collection.mutable.ArraySeq[((Option[Boolean], nat))] =
            (upd[(Option[Boolean],
                   nat)](shiftr1(fst[nat, Option[nat]](op_list_hd[(nat,
                            Option[nat])].apply(a1))),
                          (None, zero_nata), a1a)).apply(())
          val xa: Boolean =
            is_decided_wl_code.apply(op_list_hd[(nat,
          Option[nat])].apply(a1)).apply(());
          (op_list_tl[(nat, Option[nat])].apply(a1),
            (x, (if (xa) minus_nat(a2a, one_nat) else a2a)))
        })
    })

def skip_and_resolve_loop_wl_D_code:
      (((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
          (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                  (List[List[nat]],
                    (List[List[nat]],
                      (List[nat],
                        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
              nat))])))))))) =>
        (Unit =>
          (((List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
            ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
               nat),
              (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                      (List[List[nat]],
                        (List[List[nat]],
                          (List[nat],
                            collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                  nat))])))))))))
  =
  ((xi: ((List[(nat, Option[nat])],
           (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))]))))))))
     =>
    (a: Unit) =>
    {
      val (): Unit = a
      val x: Boolean = get_conflict_wll_is_Nil_code.apply(xi).apply(())
      val aa: (Boolean,
                ((List[(nat, Option[nat])],
                   (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                     nat)),
                  ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                     nat),
                    (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                            (List[List[nat]],
                              (List[List[nat]],
                                (List[nat],
                                  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                        nat))]))))))))
        = (heap_WHILET[(Boolean,
                         ((List[(nat, Option[nat])],
                            (collection.mutable.ArraySeq[((Option[Boolean],
                   nat))],
                              nat)),
                           ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                              nat),
                             (nat, (Option[(collection.mutable.ArraySeq[nat],
     nat)],
                                     (List[List[nat]],
                                       (List[List[nat]],
 (List[nat],
   collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                 nat))]))))))))](((aa:
             (Boolean,
               ((List[(nat, Option[nat])],
                  (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                 ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                    nat),
                   (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                           (List[List[nat]],
                             (List[List[nat]],
                               (List[nat],
                                 collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                       nat))])))))))))
            =>
           {
             val (a1, a2):
                   (Boolean,
                     ((List[(nat, Option[nat])],
                        (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                          nat)),
                       ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                          nat),
                         (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                                 (List[List[nat]],
                                   (List[List[nat]],
                                     (List[nat],
                                       collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                             nat))]))))))))
               = aa;
             (if (! a1)
               Heap.bind[Boolean,
                          Boolean](is_decided_hd_trail_wll_code.apply(a2),
                                    ((x_b: Boolean) => (_: Unit) => (! x_b)))
               else (_: Unit) => false)
           }),
          ((aa: (Boolean,
                  ((List[(nat, Option[nat])],
                     (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                       nat)),
                    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                       nat),
                      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                              (List[List[nat]],
                                (List[List[nat]],
                                  (List[nat],
                                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                          nat))])))))))))
             =>
            {
              val (_, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, (a1g, a2g)))))))):
                    (Boolean,
                      ((List[(nat, Option[nat])],
                         (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                           nat)),
                        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                           nat),
                          (nat, (Option[(collection.mutable.ArraySeq[nat],
  nat)],
                                  (List[List[nat]],
                                    (List[List[nat]],
                                      (List[nat],
collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat], nat))]))))))))
                = aa
              val x_b: (collection.mutable.ArraySeq[nat], nat) =
                the[(collection.mutable.ArraySeq[nat], nat)](a1d);
              Heap.bind[(nat, Option[nat]),
                         (Boolean,
                           ((List[(nat, Option[nat])],
                              (collection.mutable.ArraySeq[((Option[Boolean],
                     nat))],
                                nat)),
                             ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                                nat),
                               (nat, (Option[(collection.mutable.ArraySeq[nat],
       nat)],
                                       (List[List[nat]],
 (List[List[nat]],
   (List[nat],
     collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                   nat))]))))))))]((comp[List[(nat,
                        Option[nat])],
                  (Unit => ((nat, Option[nat]))),
                  (List[(nat, Option[nat])],
                    (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                      nat))](comp[(nat, Option[nat]),
                                   (Unit => ((nat, Option[nat]))),
                                   List[(nat,
  Option[nat])]](((ab: (nat, Option[nat])) => (_: Unit) => ab),
                  ((ab: List[(nat, Option[nat])]) =>
                    hd[(nat, Option[nat])](ab))),
                              ((ab: (List[(nat, Option[nat])],
                                      (collection.mutable.ArraySeq[((Option[Boolean],
                             nat))],
nat)))
                                 =>
                                fst[List[(nat, Option[nat])],
                                     (collection.mutable.ArraySeq[((Option[Boolean],
                            nat))],
                                       nat)](ab)))).apply(a1a),
            ((xa: (nat, Option[nat])) =>
              {
                val (a1h, a2h): (nat, nat) =
                  (fst[nat, Option[nat]](xa),
                    the[nat](snd[nat, Option[nat]](xa)));
                Heap.bind[Boolean,
                           (Boolean,
                             ((List[(nat, Option[nat])],
                                (collection.mutable.ArraySeq[((Option[Boolean],
                       nat))],
                                  nat)),
                               ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                                  nat),
                                 (nat, (Option[(collection.mutable.ArraySeq[nat],
         nat)],
 (List[List[nat]],
   (List[List[nat]],
     (List[nat],
       collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                     nat))]))))))))](is_in_arl_code.apply(uminus_lit_imp(a1h)).apply(x_b),
              ((xb: Boolean) =>
                (if (! xb)
                  Heap.bind[(List[(nat, Option[nat])],
                              (collection.mutable.ArraySeq[((Option[Boolean],
                     nat))],
                                nat)),
                             (Boolean,
                               ((List[(nat, Option[nat])],
                                  (collection.mutable.ArraySeq[((Option[Boolean],
                         nat))],
                                    nat)),
                                 ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                                    nat),
                                   (nat, (Option[(collection.mutable.ArraySeq[nat],
           nat)],
   (List[List[nat]],
     (List[List[nat]],
       (List[nat],
         collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                       nat))]))))))))](tl_trail_tr_code.apply(a1a),
                ((xc: (List[(nat, Option[nat])],
                        (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                          nat)))
                   =>
                  (_: Unit) =>
                    (false,
                      (xc, (a1b, (a1c, (Some[(collection.mutable.ArraySeq[nat],
       nat)](x_b),
 (a1e, (a1f, (a1g, a2g))))))))))
                  else Heap.bind[nat, (Boolean,
((List[(nat, Option[nat])],
   (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
  ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
    (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
            (List[List[nat]],
              (List[List[nat]],
                (List[nat],
                  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
        nat))]))))))))](maximum_level_remove_code.apply(a1a).apply(x_b).apply(uminus_lit_imp(a1h)),
                         ((xc: nat) =>
                           (if (equal_nata(xc,
    {
      val (_, (_, k)):
            (List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))
        = a1a;
      k
    }))
                             Heap.bind[(collection.mutable.ArraySeq[nat], nat),
(Boolean,
  ((List[(nat, Option[nat])],
     (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
              (List[List[nat]],
                (List[List[nat]],
                  (List[nat],
                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
          nat))]))))))))](remove1_wl_code.apply(uminus_lit_imp(a1h)).apply(x_b),
                           ((x_h: (collection.mutable.ArraySeq[nat], nat)) =>
                             Heap.bind[(collection.mutable.ArraySeq[nat], nat),
(Boolean,
  ((List[(nat, Option[nat])],
     (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
              (List[List[nat]],
                (List[List[nat]],
                  (List[nat],
                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
          nat))]))))))))]((if (equal_nata(a2h, zero_nata)) arl_empty[nat, nat]
                            else Heap.bind[collection.mutable.ArraySeq[nat],
    (collection.mutable.ArraySeq[nat],
      nat)](nth_rl[nat](a1b, a2h),
             ((xd: collection.mutable.ArraySeq[nat]) =>
               Heap.bind[(collection.mutable.ArraySeq[nat], nat),
                          (collection.mutable.ArraySeq[nat],
                            nat)](arl_of_array_raa[nat](xd),
                                   remove1_wl_code.apply(a1h))))),
                           ((x_j: (collection.mutable.ArraySeq[nat], nat)) =>
                             Heap.bind[(collection.mutable.ArraySeq[nat], nat),
(Boolean,
  ((List[(nat, Option[nat])],
     (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
              (List[List[nat]],
                (List[List[nat]],
                  (List[nat],
                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
          nat))]))))))))](union_mset_list_fold_code.apply(x_h).apply(x_j),
                           ((x_l: (collection.mutable.ArraySeq[nat], nat)) =>
                             Heap.bind[Boolean,
(Boolean,
  ((List[(nat, Option[nat])],
     (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
              (List[List[nat]],
                (List[List[nat]],
                  (List[nat],
                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
          nat))]))))))))](arl_is_empty[nat].apply(x_l),
                           ((x_n: Boolean) =>
                             Heap.bind[(List[(nat, Option[nat])],
 (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
(Boolean,
  ((List[(nat, Option[nat])],
     (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
              (List[List[nat]],
                (List[List[nat]],
                  (List[nat],
                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
          nat))]))))))))](tl_trail_tr_code.apply(a1a),
                           ((xd: (List[(nat, Option[nat])],
                                   (collection.mutable.ArraySeq[((Option[Boolean],
                          nat))],
                                     nat)))
                              =>
                             (_: Unit) =>
                               (x_n, (xd, (a1b,
    (a1c, (Some[(collection.mutable.ArraySeq[nat], nat)](x_l),
            (a1e, (a1f, (a1g, a2g))))))))))))))))))
                             else (_: Unit) =>
                                    (true,
                                      (a1a,
(a1b, (a1c, (Some[(collection.mutable.ArraySeq[nat], nat)](x_b),
              (a1e, (a1f, (a1g, a2g))))))))))))))
              }))
            }),
          (x, xi))).apply(());
      ({
         val (_, ab):
               (Boolean,
                 ((List[(nat, Option[nat])],
                    (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                      nat)),
                   ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                      nat),
                     (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                             (List[List[nat]],
                               (List[List[nat]],
                                 (List[nat],
                                   collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                         nat))]))))))))
           = aa;
         (_: Unit) => ab
       })(())
    })

def find_unassigned_lit_wl_D_code(n_0: List[nat]):
      (((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
          (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                  (List[List[nat]],
                    (List[List[nat]],
                      (List[nat],
                        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
              nat))])))))))) =>
        (Unit => Option[nat])
  =
  ((a: ((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
         ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
           (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                   (List[List[nat]],
                     (List[List[nat]],
                       (List[nat],
                         collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
               nat))]))))))))
     =>
    {
      val (a1, (_, (_, (_, (_, (_, (_, _))))))):
            ((List[(nat, Option[nat])],
               (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                 nat),
                (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                        (List[List[nat]],
                          (List[List[nat]],
                            (List[nat],
                              collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                    nat))])))))))
        = a;
      ((b: Unit) =>
        {
          val (): Unit = b
          val x: (Option[nat], List[nat]) =
            (heap_WHILET[(Option[nat],
                           List[nat])](((aa: (Option[nat], List[nat])) =>
 {
   val (a1g, a2g): (Option[nat], List[nat]) = aa;
   (_: Unit) => (is_None[nat](a1g) && ! op_list_is_empty[nat].apply(a2g))
 }),
((aa: (Option[nat], List[nat])) =>
  {
    val (_, a2g): (Option[nat], List[nat]) = aa;
    Heap.bind[Option[Boolean],
               (Option[nat],
                 List[nat])](valued_trail_code.apply(a1).apply(op_list_hd[nat].apply(a2g)),
                              ((x: Option[Boolean]) =>
                                (_: Unit) =>
                                  ((if (is_None[Boolean](x))
                                     Some[nat](op_list_hd[nat].apply(a2g))
                                     else None),
                                    op_list_tl[nat].apply(a2g))))
  }),
(None, n_0))).apply(());
          fst[Option[nat], List[nat]](x)
        })
    })

def cons_trail_Decided_tr_code:
      nat =>
        ((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))) =>
          (Unit =>
            ((List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))))
  =
  ((ai: nat) =>
    (a: (List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
      =>
    {
      val (a1, (a1a, a2a)):
            (List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))
        = a;
      ((b: Unit) =>
        {
          val (): Unit = b
          val x: collection.mutable.ArraySeq[((Option[Boolean], nat))] =
            (upd[(Option[Boolean],
                   nat)](shiftr1(ai),
                          (Some[Boolean](equal_nata(bitAND_nat(ai, one_nat),
             zero_nata)),
                            plus_nat(a2a, one_nat)),
                          a1a)).apply(());
          (op_list_prepend[(nat, Option[nat])].apply(decided[nat,
                      nat](ai)).apply(a1),
            (x, plus_nat(a2a, one_nat)))
        })
    })

def decide_wl_or_skip_D_code(n_0: List[nat]):
      (((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
          (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                  (List[List[nat]],
                    (List[List[nat]],
                      (List[nat],
                        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
              nat))])))))))) =>
        (Unit =>
          ((Boolean,
            ((List[(nat, Option[nat])],
               (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                 nat),
                (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                        (List[List[nat]],
                          (List[List[nat]],
                            (List[nat],
                              collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                    nat))]))))))))))
  =
  ((xi: ((List[(nat, Option[nat])],
           (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))]))))))))
     =>
    (a: Unit) =>
    {
      val (): Unit = a
      val x: Option[nat] =
        (find_unassigned_lit_wl_D_code(n_0)).apply(xi).apply(());
      (if (! (is_None[nat](x)))
        {
          val (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (_, a2f))))))):
                ((List[(nat, Option[nat])],
                   (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                     nat)),
                  ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                     nat),
                    (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                            (List[List[nat]],
                              (List[List[nat]],
                                (List[nat],
                                  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                        nat))])))))))
            = xi
          val x_c: nat = the[nat](x);
          Heap.bind[(List[(nat, Option[nat])],
                      (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                        nat)),
                     (Boolean,
                       ((List[(nat, Option[nat])],
                          (collection.mutable.ArraySeq[((Option[Boolean],
                 nat))],
                            nat)),
                         ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                            nat),
                           (nat, (Option[(collection.mutable.ArraySeq[nat],
   nat)],
                                   (List[List[nat]],
                                     (List[List[nat]],
                                       (List[nat],
 collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                               nat))]))))))))](cons_trail_Decided_tr_code.apply(x_c).apply(a1),
        ((xa: (List[(nat, Option[nat])],
                (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
           =>
          (_: Unit) =>
            (false,
              (xa, (a1a, (a1b, (a1c, (a1d, (a1e,
     (List(uminus_lit_imp(x_c)), a2f))))))))))
        }
        else (_: Unit) => (true, xi))(())
    })

def find_lit_of_max_level_wl_imp_code:
      ((List[(nat, Option[nat])],
        (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))) =>
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
          nat)) =>
          nat =>
            ((collection.mutable.ArraySeq[nat], nat)) =>
              (List[List[nat]]) =>
                (List[List[nat]]) =>
                  (List[nat]) =>
                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
          nat))] =>
                      nat => (Unit => nat)
  =
  ((ai: (List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
     =>
    (_: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat)) =>
    (_: nat) => (bie: (collection.mutable.ArraySeq[nat], nat)) =>
    (_: List[List[nat]]) => (_: List[List[nat]]) => (_: List[nat]) =>
    (_: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat], nat))])
      =>
    (bi: nat) => (a: Unit) =>
    {
      val (): Unit = a
      val x: nat =
        maximum_level_remove_code.apply(ai).apply(bie).apply(uminus_lit_imp(bi)).apply(())
      val xa: nat =
        (heap_WHILET[nat](((s: nat) =>
                            Heap.bind[nat, Boolean](arl_get[nat].apply(bie).apply(s),
             ((xa: nat) =>
               Heap.bind[nat, Boolean](arl_get[nat].apply(bie).apply(s),
((xb: nat) =>
  Heap.bind[nat, Boolean](get_level_code_get_level_code.apply(ai).apply(xb),
                           ((xba: nat) =>
                             (_: Unit) =>
                               (if (! (equal_nata(xa, uminus_lit_imp(bi))))
                                 ! (equal_nata(xba, x)) else true)))))))),
                           ((s: nat) => (_: Unit) => (plus_nat(s, one_nat))),
                           zero_nata)).apply(());
      arl_get[nat].apply(bie).apply(xa).apply(())
    })

def remove1_and_add_first_code:
      nat =>
        nat =>
          ((collection.mutable.ArraySeq[nat], nat)) =>
            (Unit => ((collection.mutable.ArraySeq[nat], nat)))
  =
  ((ai: nat) => (bia: nat) => (bi: (collection.mutable.ArraySeq[nat], nat)) =>
    (a: Unit) =>
    {
      val (): Unit = a
      val x: nat = find_first_eq_code.apply(ai).apply(bi).apply(())
      val x_b: nat = find_first_eq_code.apply(bia).apply(bi).apply(())
      val x_d: (collection.mutable.ArraySeq[nat], nat) =
        arl_swap[nat].apply(bi).apply(zero_nata).apply(x).apply(());
      arl_swap[nat].apply(x_d).apply(one_nat).apply((if (equal_nata(x_b,
                             zero_nata))
              x else x_b)).apply(())
    })

def find_decomp_wl_imp_code:
      ((List[(nat, Option[nat])],
        (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))) =>
        ((collection.mutable.ArraySeq[nat], nat)) =>
          nat =>
            (Unit =>
              ((List[(nat, Option[nat])],
                (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))))
  =
  ((ai: (List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
     =>
    (bia: (collection.mutable.ArraySeq[nat], nat)) => (bi: nat) => (a: Unit) =>
    {
      val (): Unit = a
      val x: nat =
        maximum_level_remove_code.apply(ai).apply(bia).apply(uminus_lit_imp(bi)).apply(())
      val aa: (nat, (List[(nat, Option[nat])],
                      (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                        nat)))
        = (heap_WHILET[(nat, (List[(nat, Option[nat])],
                               (collection.mutable.ArraySeq[((Option[Boolean],
                      nat))],
                                 nat)))](((aa:
     (nat, (List[(nat, Option[nat])],
             (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))))
    =>
   {
     val (a1, _):
           (nat, (List[(nat, Option[nat])],
                   (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                     nat)))
       = aa;
     (_: Unit) => (less_nat(x, a1))
   }),
  ((aa: (nat, (List[(nat, Option[nat])],
                (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))))
     =>
    {
      val (a1, a2):
            (nat, (List[(nat, Option[nat])],
                    (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                      nat)))
        = aa;
      Heap.bind[(nat, Option[nat]),
                 (nat, (List[(nat, Option[nat])],
                         (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                           nat)))]((comp[List[(nat, Option[nat])],
  (Unit => ((nat, Option[nat]))),
  (List[(nat, Option[nat])],
    (collection.mutable.ArraySeq[((Option[Boolean], nat))],
      nat))](comp[(nat, Option[nat]), (Unit => ((nat, Option[nat]))),
                   List[(nat, Option[nat])]](((ab: (nat, Option[nat])) =>
       (_: Unit) => ab),
      ((ab: List[(nat, Option[nat])]) => hd[(nat, Option[nat])](ab))),
              ((ab: (List[(nat, Option[nat])],
                      (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                        nat)))
                 =>
                fst[List[(nat, Option[nat])],
                     (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                       nat)](ab)))).apply(a2),
                                    ((xa: (nat, Option[nat])) =>
                                      Heap.bind[Boolean,
         (nat, (List[(nat, Option[nat])],
                 (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                   nat)))](is_decided_wl_code.apply(xa),
                            ((x_e: Boolean) =>
                              (if (x_e)
                                Heap.bind[(List[(nat, Option[nat])],
    (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
   (nat, (List[(nat, Option[nat])],
           (collection.mutable.ArraySeq[((Option[Boolean], nat))],
             nat)))](tl_trail_tr_code.apply(a2),
                      ((x_g: (List[(nat, Option[nat])],
                               (collection.mutable.ArraySeq[((Option[Boolean],
                      nat))],
                                 nat)))
                         =>
                        (_: Unit) => (minus_nat(a1, one_nat), x_g)))
                                else Heap.bind[(List[(nat, Option[nat])],
         (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        (nat, (List[(nat, Option[nat])],
                (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                  nat)))](tl_trail_tr_code.apply(a2),
                           ((x_f: (List[(nat, Option[nat])],
                                    (collection.mutable.ArraySeq[((Option[Boolean],
                           nat))],
                                      nat)))
                              =>
                             (_: Unit) => (a1, x_f))))))))
    }),
  ({
     val (_, (_, k)):
           (List[(nat, Option[nat])],
             (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))
       = ai;
     k
   },
    ai))).apply(());
      ({
         val (_, ab):
               (nat, (List[(nat, Option[nat])],
                       (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                         nat)))
           = aa;
         (_: Unit) => ab
       })(())
    })

def find_decomp_wl_imp_codea:
      ((List[(nat, Option[nat])],
        (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat))) =>
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
          nat)) =>
          nat =>
            ((collection.mutable.ArraySeq[nat], nat)) =>
              (List[List[nat]]) =>
                (List[List[nat]]) =>
                  (List[nat]) =>
                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
          nat))] =>
                      nat =>
                        (Unit =>
                          ((List[(nat, Option[nat])],
                            (collection.mutable.ArraySeq[((Option[Boolean],
                   nat))],
                              nat))))
  =
  ((ai: (List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
     =>
    (_: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat)) =>
    (_: nat) => (bie: (collection.mutable.ArraySeq[nat], nat)) =>
    (_: List[List[nat]]) => (_: List[List[nat]]) => (_: List[nat]) =>
    (_: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat], nat))])
      =>
    find_decomp_wl_imp_code.apply(ai).apply(bie))

def single_of_mset_imp_code:
      ((collection.mutable.ArraySeq[nat], nat)) => (Unit => nat)
  =
  ((xi: (collection.mutable.ArraySeq[nat], nat)) =>
    arl_get[nat].apply(xi).apply(zero_nata))

def backtrack_wl_D_code:
      (((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
          (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                  (List[List[nat]],
                    (List[List[nat]],
                      (List[nat],
                        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
              nat))])))))))) =>
        (Unit =>
          (((List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
            ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
               nat),
              (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                      (List[List[nat]],
                        (List[List[nat]],
                          (List[nat],
                            collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                  nat))])))))))))
  =
  ((a: ((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
         ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
           (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                   (List[List[nat]],
                     (List[List[nat]],
                       (List[nat],
                         collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
               nat))]))))))))
     =>
    {
      val (a1, (a1a, (a1b, (a1c, (a1d, (a1e, (a1f, a2f))))))):
            ((List[(nat, Option[nat])],
               (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                 nat),
                (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                        (List[List[nat]],
                          (List[List[nat]],
                            (List[nat],
                              collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                    nat))])))))))
        = a;
      ((b: Unit) =>
        {
          val (): Unit = b
          val x: (nat, Option[nat]) =
            (comp[List[(nat, Option[nat])], (Unit => ((nat, Option[nat]))),
                   (List[(nat, Option[nat])],
                     (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                       nat))](comp[(nat, Option[nat]),
                                    (Unit => ((nat, Option[nat]))),
                                    List[(nat,
   Option[nat])]](((aa: (nat, Option[nat])) => (_: Unit) => aa),
                   ((aa: List[(nat, Option[nat])]) =>
                     hd[(nat, Option[nat])](aa))),
                               ((aa: (List[(nat, Option[nat])],
                                       (collection.mutable.ArraySeq[((Option[Boolean],
                              nat))],
 nat)))
                                  =>
                                 fst[List[(nat, Option[nat])],
                                      (collection.mutable.ArraySeq[((Option[Boolean],
                             nat))],
nat)](aa)))).apply(a1).apply(());
          ({
             val x_a: nat = fst[nat, Option[nat]](x)
             val x_c: (collection.mutable.ArraySeq[nat], nat) =
               the[(collection.mutable.ArraySeq[nat], nat)](a1c);
             Heap.bind[(List[(nat, Option[nat])],
                         (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                           nat)),
                        ((List[(nat, Option[nat])],
                           (collection.mutable.ArraySeq[((Option[Boolean],
                  nat))],
                             nat)),
                          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                             nat),
                            (nat, (Option[(collection.mutable.ArraySeq[nat],
    nat)],
                                    (List[List[nat]],
                                      (List[List[nat]],
(List[nat],
  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                nat))])))))))](find_decomp_wl_imp_codea.apply(a1).apply(a1a).apply(a1b).apply(x_c).apply(a1d).apply(a1e).apply(a1f).apply(a2f).apply(x_a),
        ((x_e: (List[(nat, Option[nat])],
                 (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
           =>
          Heap.bind[nat, ((List[(nat, Option[nat])],
                            (collection.mutable.ArraySeq[((Option[Boolean],
                   nat))],
                              nat)),
                           ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                              nat),
                             (nat, (Option[(collection.mutable.ArraySeq[nat],
     nat)],
                                     (List[List[nat]],
                                       (List[List[nat]],
 (List[nat],
   collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                 nat))])))))))](arl_length[nat].apply(x_c),
         ((xa: nat) =>
           (if (less_nat(one_nat, xa))
             Heap.bind[nat, ((List[(nat, Option[nat])],
                               (collection.mutable.ArraySeq[((Option[Boolean],
                      nat))],
                                 nat)),
                              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                                 nat),
                                (nat, (Option[(collection.mutable.ArraySeq[nat],
        nat)],
(List[List[nat]],
  (List[List[nat]],
    (List[nat],
      collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                    nat))])))))))](find_lit_of_max_level_wl_imp_code.apply(x_e).apply(a1a).apply(a1b).apply(x_c).apply(a1d).apply(a1e).apply(a1f).apply(a2f).apply(x_a),
            ((x_g: nat) =>
              Heap.bind[(collection.mutable.ArraySeq[nat], nat),
                         ((List[(nat, Option[nat])],
                            (collection.mutable.ArraySeq[((Option[Boolean],
                   nat))],
                              nat)),
                           ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                              nat),
                             (nat, (Option[(collection.mutable.ArraySeq[nat],
     nat)],
                                     (List[List[nat]],
                                       (List[List[nat]],
 (List[nat],
   collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                 nat))])))))))](remove1_and_add_first_code.apply(uminus_lit_imp(x_a)).apply(x_g).apply(x_c),
         ((x_j: (collection.mutable.ArraySeq[nat], nat)) =>
           Heap.bind[nat, ((List[(nat, Option[nat])],
                             (collection.mutable.ArraySeq[((Option[Boolean],
                    nat))],
                               nat)),
                            ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                               nat),
                              (nat, (Option[(collection.mutable.ArraySeq[nat],
      nat)],
                                      (List[List[nat]],
(List[List[nat]],
  (List[nat],
    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                  nat))])))))))](length_ra[nat](a1a),
          ((xb: nat) =>
            Heap.bind[collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
            nat))],
                       ((List[(nat, Option[nat])],
                          (collection.mutable.ArraySeq[((Option[Boolean],
                 nat))],
                            nat)),
                         ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                            nat),
                           (nat, (Option[(collection.mutable.ArraySeq[nat],
   nat)],
                                   (List[List[nat]],
                                     (List[List[nat]],
                                       (List[nat],
 collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                               nat))])))))))](append_el_aa[nat].apply(a2f).apply(x_g).apply(xb),
       ((x_k: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
    nat))])
          =>
         Heap.bind[nat, ((List[(nat, Option[nat])],
                           (collection.mutable.ArraySeq[((Option[Boolean],
                  nat))],
                             nat)),
                          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                             nat),
                            (nat, (Option[(collection.mutable.ArraySeq[nat],
    nat)],
                                    (List[List[nat]],
                                      (List[List[nat]],
(List[nat],
  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                nat))])))))))](length_ra[nat](a1a),
        ((xc: nat) =>
          Heap.bind[collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
          nat))],
                     ((List[(nat, Option[nat])],
                        (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                          nat)),
                       ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                          nat),
                         (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                                 (List[List[nat]],
                                   (List[List[nat]],
                                     (List[nat],
                                       collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                             nat))])))))))](append_el_aa[nat].apply(x_k).apply(uminus_lit_imp(x_a)).apply(xc),
     ((x_m: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
  nat))])
        =>
       Heap.bind[nat, ((List[(nat, Option[nat])],
                         (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                           nat)),
                        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                           nat),
                          (nat, (Option[(collection.mutable.ArraySeq[nat],
  nat)],
                                  (List[List[nat]],
                                    (List[List[nat]],
                                      (List[nat],
collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                              nat))])))))))](length_ra[nat](a1a),
      ((xd: nat) =>
        Heap.bind[(List[(nat, Option[nat])],
                    (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                      nat)),
                   ((List[(nat, Option[nat])],
                      (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                        nat)),
                     ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                        nat),
                       (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                               (List[List[nat]],
                                 (List[List[nat]],
                                   (List[nat],
                                     collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                           nat))])))))))](cons_trail_Propagated_tr_code.apply(uminus_lit_imp(x_a)).apply(xd).apply(x_e),
   ((x_o: (List[(nat, Option[nat])],
            (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)))
      =>
     Heap.bind[collection.mutable.ArraySeq[nat],
                ((List[(nat, Option[nat])],
                   (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                     nat)),
                  ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                     nat),
                    (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                            (List[List[nat]],
                              (List[List[nat]],
                                (List[nat],
                                  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                        nat))])))))))](array_of_arl_raa[nat].apply(x_j),
((xe: collection.mutable.ArraySeq[nat]) =>
  Heap.bind[(collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
              nat),
             ((List[(nat, Option[nat])],
                (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
               ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                  nat),
                 (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                         (List[List[nat]],
                           (List[List[nat]],
                             (List[nat],
                               collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                     nat))])))))))](arrayO_raa_append[nat].apply(a1a).apply(xe),
                                     ((xf:
 (collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat))
=>
                                       (_: Unit) =>
 (x_o, (xf, (a1b, (None, (a1d, (a1e, (List(x_a), x_m)))))))))))))))))))))))))))
             else Heap.bind[nat, ((List[(nat, Option[nat])],
                                    (collection.mutable.ArraySeq[((Option[Boolean],
                           nat))],
                                      nat)),
                                   ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                                      nat),
                                     (nat, (Option[(collection.mutable.ArraySeq[nat],
             nat)],
     (List[List[nat]],
       (List[List[nat]],
         (List[nat],
           collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
 nat))])))))))](single_of_mset_imp_code.apply(x_c),
                 ((x_g: nat) =>
                   Heap.bind[(List[(nat, Option[nat])],
                               (collection.mutable.ArraySeq[((Option[Boolean],
                      nat))],
                                 nat)),
                              ((List[(nat, Option[nat])],
                                 (collection.mutable.ArraySeq[((Option[Boolean],
                        nat))],
                                   nat)),
                                ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                                   nat),
                                  (nat, (Option[(collection.mutable.ArraySeq[nat],
          nat)],
  (List[List[nat]],
    (List[List[nat]],
      (List[nat],
        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                      nat))])))))))](cons_trail_Propagated_tr_code.apply(uminus_lit_imp(x_a)).apply(zero_nata).apply(x_e),
              ((x_h: (List[(nat, Option[nat])],
                       (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                         nat)))
                 =>
                (_: Unit) =>
                  (x_h, (a1a, (a1b, (None,
                                      (a1d,
(List(x_g) :: a1e, (List(x_a), a2f))))))))))))))))
           })(())
        })
    })

def cdcl_twl_o_prog_wl_D_code(n_0: List[nat]):
      (((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
          (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                  (List[List[nat]],
                    (List[List[nat]],
                      (List[nat],
                        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
              nat))])))))))) =>
        (Unit =>
          ((Boolean,
            ((List[(nat, Option[nat])],
               (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                 nat),
                (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                        (List[List[nat]],
                          (List[List[nat]],
                            (List[nat],
                              collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                    nat))]))))))))))
  =
  ((xi: ((List[(nat, Option[nat])],
           (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))]))))))))
     =>
    (a: Unit) =>
    {
      val (): Unit = a
      val x: Boolean = get_conflict_wl_is_None_code.apply(xi).apply(());
      (if (x) (decide_wl_or_skip_D_code(n_0)).apply(xi)
        else Heap.bind[((List[(nat, Option[nat])],
                          (collection.mutable.ArraySeq[((Option[Boolean],
                 nat))],
                            nat)),
                         ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                            nat),
                           (nat, (Option[(collection.mutable.ArraySeq[nat],
   nat)],
                                   (List[List[nat]],
                                     (List[List[nat]],
                                       (List[nat],
 collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat], nat))]))))))),
                        (Boolean,
                          ((List[(nat, Option[nat])],
                             (collection.mutable.ArraySeq[((Option[Boolean],
                    nat))],
                               nat)),
                            ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                               nat),
                              (nat, (Option[(collection.mutable.ArraySeq[nat],
      nat)],
                                      (List[List[nat]],
(List[List[nat]],
  (List[nat],
    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                  nat))]))))))))](skip_and_resolve_loop_wl_D_code.apply(xi),
           ((x_a: ((List[(nat, Option[nat])],
                     (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                       nat)),
                    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                       nat),
                      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                              (List[List[nat]],
                                (List[List[nat]],
                                  (List[nat],
                                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                          nat))]))))))))
              =>
             Heap.bind[Boolean,
                        (Boolean,
                          ((List[(nat, Option[nat])],
                             (collection.mutable.ArraySeq[((Option[Boolean],
                    nat))],
                               nat)),
                            ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                               nat),
                              (nat, (Option[(collection.mutable.ArraySeq[nat],
      nat)],
                                      (List[List[nat]],
(List[List[nat]],
  (List[nat],
    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                  nat))]))))))))](get_conflict_wll_is_Nil_code.apply(x_a),
           ((xa: Boolean) =>
             (if (! xa)
               Heap.bind[((List[(nat, Option[nat])],
                            (collection.mutable.ArraySeq[((Option[Boolean],
                   nat))],
                              nat)),
                           ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                              nat),
                             (nat, (Option[(collection.mutable.ArraySeq[nat],
     nat)],
                                     (List[List[nat]],
                                       (List[List[nat]],
 (List[nat],
   collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                 nat))]))))))),
                          (Boolean,
                            ((List[(nat, Option[nat])],
                               (collection.mutable.ArraySeq[((Option[Boolean],
                      nat))],
                                 nat)),
                              ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                                 nat),
                                (nat, (Option[(collection.mutable.ArraySeq[nat],
        nat)],
(List[List[nat]],
  (List[List[nat]],
    (List[nat],
      collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                    nat))]))))))))](backtrack_wl_D_code.apply(x_a),
             ((x_c: ((List[(nat, Option[nat])],
                       (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                         nat)),
                      ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                         nat),
                        (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                                (List[List[nat]],
                                  (List[List[nat]],
                                    (List[nat],
                                      collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                            nat))]))))))))
                =>
               (_: Unit) => (false, x_c)))
               else (_: Unit) => (true, x_a)))))))(())
    })

def cdcl_twl_stgy_prog_wl_D_code(n_0: List[nat]):
      (((List[(nat, Option[nat])],
          (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
          (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                  (List[List[nat]],
                    (List[List[nat]],
                      (List[nat],
                        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
              nat))])))))))) =>
        (Unit =>
          (((List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
            ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
               nat),
              (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                      (List[List[nat]],
                        (List[List[nat]],
                          (List[nat],
                            collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                  nat))])))))))))
  =
  ((xi: ((List[(nat, Option[nat])],
           (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))]))))))))
     =>
    (a: Unit) =>
    {
      val (): Unit = a
      val aa: (Boolean,
                ((List[(nat, Option[nat])],
                   (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                     nat)),
                  ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                     nat),
                    (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                            (List[List[nat]],
                              (List[List[nat]],
                                (List[nat],
                                  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                        nat))]))))))))
        = (heap_WHILET[(Boolean,
                         ((List[(nat, Option[nat])],
                            (collection.mutable.ArraySeq[((Option[Boolean],
                   nat))],
                              nat)),
                           ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                              nat),
                             (nat, (Option[(collection.mutable.ArraySeq[nat],
     nat)],
                                     (List[List[nat]],
                                       (List[List[nat]],
 (List[nat],
   collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                 nat))]))))))))](((aa:
             (Boolean,
               ((List[(nat, Option[nat])],
                  (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                 ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                    nat),
                   (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                           (List[List[nat]],
                             (List[List[nat]],
                               (List[nat],
                                 collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                       nat))])))))))))
            =>
           {
             val (a1, _):
                   (Boolean,
                     ((List[(nat, Option[nat])],
                        (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                          nat)),
                       ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                          nat),
                         (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                                 (List[List[nat]],
                                   (List[List[nat]],
                                     (List[nat],
                                       collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                             nat))]))))))))
               = aa;
             (_: Unit) => (! a1)
           }),
          ((aa: (Boolean,
                  ((List[(nat, Option[nat])],
                     (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                       nat)),
                    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                       nat),
                      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                              (List[List[nat]],
                                (List[List[nat]],
                                  (List[nat],
                                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                          nat))])))))))))
             =>
            {
              val (_, a2):
                    (Boolean,
                      ((List[(nat, Option[nat])],
                         (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                           nat)),
                        ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                           nat),
                          (nat, (Option[(collection.mutable.ArraySeq[nat],
  nat)],
                                  (List[List[nat]],
                                    (List[List[nat]],
                                      (List[nat],
collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat], nat))]))))))))
                = aa;
              Heap.bind[((List[(nat, Option[nat])],
                           (collection.mutable.ArraySeq[((Option[Boolean],
                  nat))],
                             nat)),
                          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                             nat),
                            (nat, (Option[(collection.mutable.ArraySeq[nat],
    nat)],
                                    (List[List[nat]],
                                      (List[List[nat]],
(List[nat],
  collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat], nat))]))))))),
                         (Boolean,
                           ((List[(nat, Option[nat])],
                              (collection.mutable.ArraySeq[((Option[Boolean],
                     nat))],
                                nat)),
                             ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                                nat),
                               (nat, (Option[(collection.mutable.ArraySeq[nat],
       nat)],
                                       (List[List[nat]],
 (List[List[nat]],
   (List[nat],
     collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                   nat))]))))))))](unit_propagation_outer_loop_wl_D_code.apply(a2),
            cdcl_twl_o_prog_wl_D_code(n_0))
            }),
          (false, xi))).apply(());
      ({
         val (_, ab):
               (Boolean,
                 ((List[(nat, Option[nat])],
                    (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                      nat)),
                   ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                      nat),
                     (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                             (List[List[nat]],
                               (List[List[nat]],
                                 (List[nat],
                                   collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                         nat))]))))))))
           = aa;
         (_: Unit) => ab
       })(())
    })

def init_state_wl_D(n: List[nat], l_Ns: nat):
      (Unit =>
        (((List[(nat, Option[nat])],
            (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))])))))))))
  =
  {
    val na: nat =
      Suc(Suc(fold[nat, nat](((a: nat) => (b: nat) => max[nat](a, b)), n,
                              zero_nata)));
    ((a: Unit) =>
      {
        val (): Unit = a
        val naa: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                   nat)
          = (arrayO_raa_empty_sz[nat, nat](l_Ns)).apply(())
        val e: collection.mutable.ArraySeq[nat] =
          newa[nat].apply(zero_nata).apply(zero_nata).apply(())
        val nab: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                   nat)
          = arrayO_raa_append[nat].apply(naa).apply(e).apply(())
        val ws: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
      nat))]
          = arrayO_ara_empty_sz_code[nat].apply(na).apply(())
        val m: collection.mutable.ArraySeq[((Option[Boolean], nat))] =
          newa[(Option[Boolean],
                 nat)].apply(shiftr1(na)).apply((None, zero_nata)).apply(());
        ((Nil, (m, zero_nata)),
          (nab, (zero_nata, (None, (Nil, (Nil, (Nil, ws)))))))
      })
  }

def init_state_wl_D_code(n: List[nat]):
      nat =>
        (Unit =>
          (((List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
            ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
               nat),
              (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                      (List[List[nat]],
                        (List[List[nat]],
                          (List[nat],
                            collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                  nat))])))))))))
  =
  ((a: nat) => init_state_wl_D(n, a))

def arl_of_list_raa[A : heap](xs: List[A]):
      (Unit => ((collection.mutable.ArraySeq[A], nat)))
  =
  ((a: Unit) =>
    {
      val (): Unit = a
      val x: collection.mutable.ArraySeq[A] = (of_list[A](xs)).apply(());
      (arl_of_array_raa[A](x)).apply(())
    })

def init_dt_step_wl_code:
      (List[nat]) =>
        (List[nat]) =>
          (((List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
            ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
               nat),
              (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                      (List[List[nat]],
                        (List[List[nat]],
                          (List[nat],
                            collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                  nat))])))))))) =>
            (Unit =>
              (((List[(nat, Option[nat])],
                  (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                   nat),
                  (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                          (List[List[nat]],
                            (List[List[nat]],
                              (List[nat],
                                collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                      nat))])))))))))
  =
  ((_: List[nat]) => (bia: List[nat]) =>
    (a: ((List[(nat, Option[nat])],
           (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))]))))))))
      =>
    (a match {
       case (a1, (a1a, (a1b, (None, (a1d, (a1e, (a1f, a2f))))))) =>
         (if (equal_nata(op_list_length[nat].apply(bia), one_nat))
           {
             val x_b: nat = op_list_hd[nat].apply(bia);
             ((b: Unit) =>
               {
                 val (): Unit = b
                 val x_d: Option[Boolean] =
                   valued_trail_code.apply(a1).apply(x_b).apply(());
                 (if (is_None[Boolean](x_d))
                   Heap.bind[(List[(nat, Option[nat])],
                               (collection.mutable.ArraySeq[((Option[Boolean],
                      nat))],
                                 nat)),
                              ((List[(nat, Option[nat])],
                                 (collection.mutable.ArraySeq[((Option[Boolean],
                        nat))],
                                   nat)),
                                ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                                   nat),
                                  (nat, (Option[(collection.mutable.ArraySeq[nat],
          nat)],
  (List[List[nat]],
    (List[List[nat]],
      (List[nat],
        collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                                      nat))])))))))](cons_trail_Propagated_tr_code.apply(x_b).apply(zero_nata).apply(a1),
              ((x_g: (List[(nat, Option[nat])],
                       (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                         nat)))
                 =>
                (_: Unit) =>
                  (x_g, (a1a, (a1b, (None,
                                      (List(x_b) :: a1d,
(a1e, (uminus_lit_imp(x_b) :: a1f, a2f)))))))))
                   else (if (equal_option[Boolean](x_d, Some[Boolean](true)))
                          (_: Unit) =>
                            (a1, (a1a, (a1b,
 (None, (List(x_b) :: a1d, (a1e, (a1f, a2f)))))))
                          else Heap.bind[(collection.mutable.ArraySeq[nat],
   nat),
  ((List[(nat, Option[nat])],
     (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
              (List[List[nat]],
                (List[List[nat]],
                  (List[nat],
                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
          nat))])))))))](arl_of_list_raa[nat](bia),
                          ((x: (collection.mutable.ArraySeq[nat], nat)) =>
                            (_: Unit) =>
                              (a1, (a1a, (a1b,
   (Some[(collection.mutable.ArraySeq[nat], nat)](x),
     (List(x_b) :: a1d, (a1e, (Nil, a2f)))))))))))(())
               })
           }
           else ((b: Unit) =>
                  {
                    val (): Unit = b
                    val x_b: nat = (length_ra[nat](a1a)).apply(())
                    val x_d: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                   nat))]
                      = append_el_aa[nat].apply(a2f).apply(op_list_hd[nat].apply(bia)).apply(x_b).apply(())
                    val x_f: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                   nat))]
                      = append_el_aa[nat].apply(x_d).apply(op_list_hd[nat].apply(op_list_tl[nat].apply(bia))).apply(x_b).apply(())
                    val x: collection.mutable.ArraySeq[nat] =
                      (of_list[nat](bia)).apply(())
                    val xa: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                              nat)
                      = arrayO_raa_append[nat].apply(a1a).apply(x).apply(());
                    (a1, (xa, (x_b, (None, (a1d, (a1e, (a1f, x_f)))))))
                  }))
       case (a1, (a1a, (a1b, (Some(x_a), (a1d, (a1e, (_, a2f))))))) =>
         (if (equal_nata(op_list_length[nat].apply(bia), one_nat))
           (_: Unit) =>
             (a1, (a1a, (a1b, (Some[(collection.mutable.ArraySeq[nat],
                                      nat)](x_a),
                                (List(op_list_hd[nat].apply(bia)) :: a1d,
                                  (a1e, (Nil, a2f)))))))
           else ((b: Unit) =>
                  {
                    val (): Unit = b
                    val x_c: nat = (length_ra[nat](a1a)).apply(())
                    val x_e: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                   nat))]
                      = append_el_aa[nat].apply(a2f).apply(op_list_hd[nat].apply(bia)).apply(x_c).apply(())
                    val x_g: collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                   nat))]
                      = append_el_aa[nat].apply(x_e).apply(op_list_hd[nat].apply(op_list_tl[nat].apply(bia))).apply(x_c).apply(())
                    val x: collection.mutable.ArraySeq[nat] =
                      (of_list[nat](bia)).apply(())
                    val xa: (collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                              nat)
                      = arrayO_raa_append[nat].apply(a1a).apply(x).apply(());
                    (a1, (xa, (x_c, (Some[(collection.mutable.ArraySeq[nat],
    nat)](x_a),
                                      (a1d, (a1e, (Nil, x_g)))))))
                  }))
     }))

def init_dt_wl_code:
      (List[nat]) =>
        (List[List[nat]]) =>
          (((List[(nat, Option[nat])],
              (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
            ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
               nat),
              (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                      (List[List[nat]],
                        (List[List[nat]],
                          (List[nat],
                            collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                  nat))])))))))) =>
            (Unit =>
              (((List[(nat, Option[nat])],
                  (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                   nat),
                  (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                          (List[List[nat]],
                            (List[List[nat]],
                              (List[nat],
                                collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                      nat))])))))))))
  =
  ((ai: List[nat]) => (bia: List[List[nat]]) =>
    ((a: ((List[(nat, Option[nat])],
            (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
           ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
              nat),
             (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                     (List[List[nat]],
                       (List[List[nat]],
                         (List[nat],
                           collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                 nat))]))))))))
       =>
      imp_nfoldli[List[nat],
                   ((List[(nat, Option[nat])],
                      (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                        nat)),
                     ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                        nat),
                       (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                               (List[List[nat]],
                                 (List[List[nat]],
                                   (List[nat],
                                     collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                           nat))])))))))](bia,
   ((_: ((List[(nat, Option[nat])],
           (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
          ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]], nat),
            (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                    (List[List[nat]],
                      (List[List[nat]],
                        (List[nat],
                          collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                nat))]))))))))
      =>
     (_: Unit) => true),
   init_dt_step_wl_code.apply(ai), a)))

def SAT_wl_code: (List[List[nat]]) => (Unit => Boolean) =
  ((xi: List[List[nat]]) => (a: Unit) =>
    {
      val (): Unit = a
      val x: (hashtable[nat, Unit], List[nat]) =
        extract_lits_clss_imp_empty_assn.apply(())
      val x_b: List[nat] =
        extract_lits_clss_imp_list_assn.apply(xi).apply(x).apply(())
      val x_d: ((List[(nat, Option[nat])],
                  (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                 ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                    nat),
                   (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                           (List[List[nat]],
                             (List[List[nat]],
                               (List[nat],
                                 collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                       nat))])))))))
        = (init_state_wl_D_code(x_b)).apply(op_list_length[List[nat]].apply(xi)).apply(())
      val x_f: ((List[(nat, Option[nat])],
                  (collection.mutable.ArraySeq[((Option[Boolean], nat))], nat)),
                 ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                    nat),
                   (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                           (List[List[nat]],
                             (List[List[nat]],
                               (List[nat],
                                 collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                       nat))])))))))
      = init_dt_wl_code.apply(x_b).apply(xi).apply(x_d).apply(())
      val _ = println("end of init")
      val x_g: Boolean = get_conflict_wl_is_None_code.apply(x_f).apply(());
      (if (x_g)
        Heap.bind[((List[(nat, Option[nat])],
                     (collection.mutable.ArraySeq[((Option[Boolean], nat))],
                       nat)),
                    ((collection.mutable.ArraySeq[collection.mutable.ArraySeq[nat]],
                       nat),
                      (nat, (Option[(collection.mutable.ArraySeq[nat], nat)],
                              (List[List[nat]],
                                (List[List[nat]],
                                  (List[nat],
                                    collection.mutable.ArraySeq[((collection.mutable.ArraySeq[nat],
                          nat))]))))))),
                   Boolean]((cdcl_twl_stgy_prog_wl_D_code(x_b)).apply(x_f),
                             get_conflict_wl_is_None_code)
        else (_: Unit) => false)(())
    })

} /* object SAT_Solver */
