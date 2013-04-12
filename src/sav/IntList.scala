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
}