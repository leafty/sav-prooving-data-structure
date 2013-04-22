import leon.Utils._

object obj {
  sealed abstract class IntList
  case object Nil extends IntList
  case class Cons(hd: Int, tl: IntList) extends IntList

  sealed abstract class IntPairList
  case object Nil2 extends IntPairList
  case class Cons2(hd: (Int, Int), tl: IntPairList) extends IntPairList

  def _minInt(x: Int, y: Int): Int = {
    if (x <= y) x else y
  } ensuring (res => res <= x && res <= y && (res == x || res == y))

  def _maxInt(x: Int, y: Int): Int = {
    if (x >= y) x else y
  } ensuring (res => res >= x && res >= y && (res == x || res == y))

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
    case Nil                            => true
    case Cons(x, t) if f.isDefinedAt(x) => _isTotalIntInt(t, f)
    case _                              => false
  })

  def _isTotalIntBool(l: IntList, p: Map[Int, Boolean]): Boolean = (l match {
    case Nil                            => true
    case Cons(x, t) if p.isDefinedAt(x) => _isTotalIntBool(t, p)
    case _                              => false
  })

  def forall(l: IntList, p: Map[Int, Boolean]): Boolean = {
    require(_isTotalIntBool(l, p))

    l match {
      case Nil                => true
      case Cons(x, t) if p(x) => forall(t, p)
      case _                  => false
    }
  }

  def map(l: IntList, f: Map[Int, Int]): IntList = {
    require(_isTotalIntInt(l, f))

    l match {
      case Nil        => Nil
      case Cons(x, t) => Cons(f(x), map(t, f))
    }
  } ensuring (res => size(l) == size(res))

  def filter(l: IntList, p: Map[Int, Boolean]): IntList = {
    require(_isTotalIntBool(l, p))

    l match {
      case Nil                => Nil
      case Cons(x, t) if p(x) => Cons(x, filter(t, p))
      case Cons(_, t)         => filter(t, p)
    }
  } ensuring (res => size(res) <= size(l) && _isTotalIntBool(res, p) && forall(res, p))

  def exists(l: IntList, p: Map[Int, Boolean]): Boolean = {
    require(_isTotalIntBool(l, p))

    l match {
      case Nil                => false
      case Cons(x, t) if p(x) => true
      case Cons(_, t)         => exists(t, p)
    }
  }

  def get(l: IntList, n: Int): Int = ({
    require(0 <= n && n < size(l))

    l match {
      case Cons(x, t) if n == 0 => x
      case Cons(_, t)           => get(t, n - 1)
    }
  }) ensuring (res => contains(l, res))

  def size(l: IntList): Int = (l match {
    case Nil        => 0
    case Cons(_, t) => 1 + size(t)
  }) ensuring (res => (res == 0 && l == Nil) || (res > 0 && l.isInstanceOf[Cons]))

  def _isPrefix(l1: IntList, l2: IntList): Boolean = {
    val (ll1, ll2) = unzip(zip(l1, l2))
    l1 == ll1 && l1 == ll2
  }

  def drop(l: IntList, n: Int): IntList = ({
    require(n >= 0)

    l match {
      case Cons(x, t) if n > 0 => drop(t, n - 1)
      case Nil if n > 0        => Nil
      case _ if n == 0         => l
    }
  }) ensuring (res => size(res) == _maxInt(0, size(l) - n))

  def concat(l1: IntList, l2: IntList): IntList = (l1 match {
    case Nil        => l2
    case Cons(x, t) => Cons(x, concat(t, l2))
  }) ensuring (res => size(res) == size(l1) + size(l2) && _isPrefix(l1, res) && drop(res, size(l1)) == l2)

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
  }) ensuring (res => (res == 0 && l == Nil2) || (res > 0 && l.isInstanceOf[Cons2]))

  def concat2(l1: IntPairList, l2: IntPairList): IntPairList = (l1 match {
    case Nil2        => l2
    case Cons2(x, t) => Cons2(x, concat2(t, l2))
  }) ensuring (res => size2(res) == size2(l1) + size2(l2))

  def zip(l1: IntList, l2: IntList): IntPairList = ((l1, l2) match {
    case (Nil, _)                     => Nil2
    case (_, Nil)                     => Nil2
    case (Cons(x1, t1), Cons(x2, t2)) => Cons2((x1, x2), zip(t1, t2))
  }) ensuring (res => size2(res) == _minInt(size(l1), size(l2)))

  def zipWithAll(l1: IntList, l2: IntList, x1: Int, x2: Int): IntPairList = ((l1, l2) match {
    case (Nil, Nil)                   => Nil2
    case (Cons(y1, t1), Nil)          => Cons2((y1, x2), zipWithAll(t1, Nil, x1, x2))
    case (Nil, Cons(y2, t2))          => Cons2((x1, y2), zipWithAll(Nil, t2, x1, x2))
    case (Cons(y1, t1), Cons(y2, t2)) => Cons2((y1, y2), zipWithAll(t1, t2, x1, x2))
  }) ensuring (res => size2(res) == _maxInt(size(l1), size(l2)))

  def unzip(l: IntPairList): (IntList, IntList) = (l match {
    case Nil2 => (Nil, Nil)
    case Cons2((x1, x2), t) =>
      val (t1, t2) = unzip(t)
      (Cons(x1, t1), Cons(x2, t2))
  }) ensuring (res => size(res._1) == size2(l) && size(res._2) == size2(l))

  def _isLowerBound(l: IntList, x: Int): Boolean = (l match {
    case Nil                 => true
    case Cons(y, t) if x > y => false
    case Cons(_, t)          => _isLowerBound(t, x)
  })

  def _min1(l: IntList, x: Int): Int = (l match {
    case Nil                 => x
    case Cons(y, t) if y < x => _min1(t, y)
    case Cons(_, t)          => _min1(t, x)
  }) ensuring (res => _isLowerBound(l, res) && res <= x && (res == x || contains(l, res)))

  def min(l: IntList): Int = {
    require(size(l) > 0)

    l match {
      case Cons(x, t) => _min1(t, x)
      case Nil        => 0 // avoid match warning
    }
  } ensuring (res => _isLowerBound(l, res) && contains(l, res))
}
