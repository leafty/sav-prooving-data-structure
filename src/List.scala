abstract class List[+A] {
  def isEmpty: Boolean
  def head: A
  def tail: List[A]
  
  def ::[B >: A](x: B) =
    new ::(x, this)
    
  def /:[B](z: B)(op: (B, A) => B): B = this match {
    case Nil => z
    case x :: t => (op(z, x) /: t)(op)
  }
  
  override def toString() = this match {
    case Nil => Nil.toString
    case x :: t => "List(" + stringElems + ")"
  }
  
  def stringElems = this match {
    case Nil => ""
    case x :: t => x + ("" /: t)((s, x) => s + "," + x)
  }
}

case object Nil extends List[Nothing] {
  def isEmpty = true
  def head =
    throw new NoSuchElementException("head of empty list")
  def tail =
    throw new UnsupportedOperationException("tail of empty list")
}

case class ::[B](hd: B, tl: List[B]) extends List[B] {
  def isEmpty = false
  def head = hd
  def tail = tl
}

object List {
  
}
