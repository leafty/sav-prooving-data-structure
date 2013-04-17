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

  def isEmpty(l: IntList) = l match {
    case Nil => true
    case _   => false
  }

  def head(l: IntList) = l match {
    case Nil        => error("head of emtpy list")
    case Cons(x, t) => x
  }

  def tail(l: IntList) = l match {
    case Nil        => error("tail of emtpy list")
    case Cons(x, t) => t
  }

  def size(l: IntList): Int = (l match {
    case Nil        => 0
    case Cons(_, t) => 1 + size(t)
  }) ensuring (size => size >= 0)

  def concat(l1: IntList, l2: IntList): IntList = (l1 match {
    case Nil        => l2
    case Cons(x, t) => Cons(x, concat(t, l2))
  }) ensuring (l => size(l) == size(l1) + size(l2))

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
}
