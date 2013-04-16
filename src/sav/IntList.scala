import leon.Utils._

object obj {

  abstract class IntList

  case object Nil extends IntList

  case class Cons(hd: Int, tl: IntList) extends IntList

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
}
