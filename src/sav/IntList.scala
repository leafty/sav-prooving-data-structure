package sav

object IntList {
  
  abstract class IntList {}
  
  case object Nil extends IntList
  
  case class Cons(hd: Int, tl: IntList) extends IntList
  
  def isEmpty(l: IntList) = l match {
    case Nil => true
    case _ => false
  }
  
  def head(l: IntList) = l match {
    case Nil => throw new NoSuchElementException("head of emtpy list")
    case Cons(x, _) => x
  }
  
  
  def tail(l: IntList) = l match {
    case Nil => throw new UnsupportedOperationException("tail of emtpy list")
    case Cons(_, t) => t
  }
}