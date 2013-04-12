abstract class List[+A] {
  def isEmpty: Boolean
  def head: A
  def tail: List[A]
  
  def ::[B >: A](x: B): List[B] =
    new ::(x, this)
  
  def ++[B >: A](suffix: List[B]): List[B] = this match {
    case Nil => suffix
    case x :: t => x :: (t ++ suffix)
  }
    
  def :::[B >: A](prefix: List[B]): List[B] = prefix ++ this
    
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
  
  def size: Int = this match {
    case Nil => 0
    case _ :: t => 1 + t.size
  }
  
  def length = size
  
  def contains(x: Any): Boolean = this match {
    case Nil => false
    case y :: t => (x == y) || (t contains x)
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
  def apply[A](xs: A*): List[A] = {
    try {
      new ::(xs.head, apply(xs.tail:_*))
    } catch {
      case e: NoSuchElementException => Nil
    }
  }
  
  def concat[A](xss: Traversable[A]*): List[A] = ???
  
  def empty = Nil
}
