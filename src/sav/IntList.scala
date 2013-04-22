import leon.Utils._

object obj {
   sealed abstract class IntList
   case object Nil extends IntList
   case class Cons(hd: Int, tl: IntList) extends IntList

   sealed abstract class IntPairList
   case object Nil2 extends IntPairList
   case class Cons2(hd: (Int, Int), tl: IntPairList) extends IntPairList

   def min(a: Int, b: Int): Int = {
      if (a <= b) a else b
   } ensuring (m => m <= a && m <= b && (m == a || m == b))

   def max(a: Int, b: Int): Int = {
      if (a >= b) a else b
   } ensuring (m => m >= a && m >= b && (m == a || m == b))

   def isEmpty(l: IntList) = (l match {
      case Nil => true
      case _   => false
   }) ensuring (res => (res && l == Nil) || (!res && l.isInstanceOf[Cons]))

   def head(l: IntList) = (l match {
      case Nil        => error("head of emtpy list")
      case Cons(x, t) => x
   })

   def tail(l: IntList) = l match {
      case Nil        => error("tail of emtpy list")
      case Cons(x, t) => t
   }

   def contains(l: IntList, x: Int): Boolean = (l match {
      case Nil                  => false
      case Cons(y, t) if x == y => true
      case Cons(_, t)           => contains(t, x)
   })

   def _isTotalIntInt(l: IntList, f: Map[Int, Int]): Boolean = (l match {
      case Nil                               => true
      case Cons(hd, tl) if f.isDefinedAt(hd) => _isTotalIntInt(tl, f)
      case _                                 => false
   })

   def _isTotalIntBool(l: IntList, f: Map[Int, Boolean]): Boolean = (l match {
      case Nil                               => true
      case Cons(hd, tl) if f.isDefinedAt(hd) => _isTotalIntBool(tl, f)
      case _                                 => false
   })

   def _forAll(l: IntList, f: Map[Int, Boolean]): Boolean = {
      require(_isTotalIntBool(l, f))
      l match {
         case Nil                   => true
         case Cons(hd, tl) if f(hd) => _forAll(tl, f)
         case _                     => false
      }
   }

   def map(l: IntList, f: Map[Int, Int]): IntList = {
      require(_isTotalIntInt(l, f))
      l match {
         case Nil          => Nil
         case Cons(hd, tl) => Cons(f(hd), map(tl, f))
      }
   } ensuring (res => size(l) == size(res))

   def filter(l: IntList, f: Map[Int, Boolean]): IntList = {
      require(_isTotalIntBool(l, f))
      l match {
         case Nil                => Nil
         case Cons(y, t) if f(y) => Cons(y, filter(t, f))
         case Cons(_, t)         => filter(t, f)
      }
   } ensuring (res => size(l) >= size(res) && _isTotalIntBool(res, f) && _forAll(res, f))

   def exists(l: IntList, f: Map[Int, Boolean]): Boolean = {
      require(_isTotalIntBool(l, f))
      l match {

         case Nil                => false
         case Cons(y, t) if f(y) => true
         case Cons(_, t)         => exists(t, f)
      }
   } // ensuring (res => (l == Nil && !res) || (l.isInstanceOf[Cons] && ((res && (f.apply(l.asInstanceOf[Cons].hd) || exists(l.asInstanceOf[Cons].tl, f)))) || (!res && (!f.apply(l.asInstanceOf[Cons].hd) && !exists(l.asInstanceOf[Cons].tl, f)))))

   def get(l: IntList, n: Int): Int = ({
      require(0 <= n && n < size(l))

      l match {
         case Cons(x, t) if n == 0 => x
         case Cons(_, t)           => get(t, n - 1)
      }
   }) ensuring (x => contains(l, x))

   def size(l: IntList): Int = (l match {
      case Nil        => 0
      case Cons(_, t) => 1 + size(t)
   }) ensuring (size => (size == 0 && l == Nil) || (size > 0 && l.isInstanceOf[Cons]))

   def isPrefix(p: IntList, l: IntList): Boolean = {
      val (p2, l2) = unzip(zip(p, l))
      p == p2 && p == l2
   }

   def drop(l: IntList, n: Int): IntList = ({
      require(n >= 0)

      l match {
         case Cons(x, t) if n > 0 => drop(t, n - 1)
         case Nil if n > 0        => Nil
         case _ if n == 0         => l
      }
   }) ensuring (res => size(res) == max(0, size(l) - n))

   def concat(l1: IntList, l2: IntList): IntList = (l1 match {
      case Nil        => l2
      case Cons(x, t) => Cons(x, concat(t, l2))
   }) ensuring (l => size(l) == size(l1) + size(l2) && isPrefix(l1, l) && drop(l, size(l1)) == l2)

   def isEmpty2(l: IntPairList) = l match {
      case Nil2 => true
      case _    => false
   }

   def head2(l: IntPairList) = l match {
      case Nil2        => error("head of emtpy list")
      case Cons2(x, t) => x
   }

   def tail2(l: IntPairList) = l match {
      case Nil2        => error("tail of emtpy list")
      case Cons2(x, t) => t
   }

   def size2(l: IntPairList): Int = (l match {
      case Nil2        => 0
      case Cons2(_, t) => 1 + size2(t)
   }) ensuring (size => size >= 0)

   def concat2(l1: IntPairList, l2: IntPairList): IntPairList = (l1 match {
      case Nil2        => l2
      case Cons2(x, t) => Cons2(x, concat2(t, l2))
   }) ensuring (l => size2(l) == size2(l1) + size2(l2))

   def zip(l1: IntList, l2: IntList): IntPairList = ((l1, l2) match {
      case (Nil, _)                     => Nil2
      case (_, Nil)                     => Nil2
      case (Cons(x1, t1), Cons(x2, t2)) => Cons2((x1, x2), zip(t1, t2))
   }) ensuring (l => size2(l) == min(size(l1), size(l2)))

   def zipWithAll(l1: IntList, l2: IntList, d1: Int, d2: Int): IntPairList = ({
    def innerZip(l1: IntList, l2: IntList): IntPairList = ((l1, l2) match {
      case (Nil, Nil)                   => Nil2
      case (Nil, Cons(x2, t2))          => Cons2((d1, x2), innerZip(Nil, t2))
      case (Cons(x1, t1), Nil)          => Cons2((x1, d2), innerZip(t1, Nil))
      case (Cons(x1, t1), Cons(x2, t2)) => Cons2((x1, x2), innerZip(t1, t2))
    }) ensuring (l => size2(l) == max(size(l1), size(l2)))

    innerZip(l1, l2)
  }) ensuring (l => size2(l) == max(size(l1), size(l2)))

   def unzip(l: IntPairList): (IntList, IntList) = (l match {
      case Nil2 => (Nil, Nil)
      case Cons2((x1, x2), t) =>
         val (t1, t2) = unzip(t)
         (Cons(x1, t1), Cons(x2, t2))
   }) ensuring (p => size(p._1) == size2(l) && size(p._2) == size2(l))

   def isLowerBound(l: IntList, x: Int): Boolean = (l match {
    case Nil => true
    case Cons(y, t) if x > y => false
    case Cons(_, t) => isLowerBound(t, x)
  })
  
  def minList1(l: IntList, x: Int): Int = (l match {
    case Nil => x
    case Cons(y, t) if y < x => minList1(t, y)
    case Cons(_, t) => minList1(t, x)
  }) ensuring (res => isLowerBound(l, res) && res <= x && (res == x || contains(l, res)))
  
  def minList(l: IntList, x: Int): Int = {
    require(size(l) > 0)
    
    l match {
      case Cons(x, t) => minList1(t, x)
    }
  } ensuring (res => isLowerBound(l, res) && contains(l, res))
}
