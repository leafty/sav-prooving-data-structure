import leon.Utils._

object polylist {

  case class TypeA(x: Set[Int])
  case class TypeB(x: Map[Int, Boolean])

  //
  // List of elements of type A
  //
  sealed abstract class ListA
  case object NilA extends ListA
  case class ConsA(hd: TypeA, tl: ListA) extends ListA

  //
  // List of elements of type B
  //
  sealed abstract class ListB
  case object NilB extends ListB
  case class ConsB(hd: TypeB, tl: ListB) extends ListB

  def size(l: ListA): Int = (l match {
    case NilA        => 0
    case ConsA(_, t) => 1 + size(t)
  }) ensuring (res => (res == 0 && l == NilA) || (res > 0 && l.isInstanceOf[ConsA]))

  def sizeB(l: ListB): Int = (l match {
    case NilB        => 0
    case ConsB(_, t) => 1 + sizeB(t)
  }) ensuring (res => (res == 0 && l == NilB) || (res > 0 && l.isInstanceOf[ConsB]))

  def isEmpty(l: ListA): Boolean = (l match {
    case NilA => true
    case _    => false
  }) ensuring (res => (res && l == NilA) || (!res && l.isInstanceOf[ConsA]))

  def tail(l: ListA) = l match {
    case NilA        => error("tail of emtpy list")
    case ConsA(x, t) => t
  }

  def drop(l: ListA, n: Int): ListA = {
    require(n >= 0)
    l match {
      case ConsA(x, t) if n > 0 => drop(t, n - 1)
      case _                    => l
    }
  } ensuring (res => size(res) == _maxInt(0, size(l) - n))

  def dropRight(l: ListA, n: Int): ListA = {
    require(n >= 0)
    val s = size(l)
    val m = _maxInt(s - n, 0)
    take(l, m)
  } ensuring (res => size(res) == _maxInt(0, size(l) - n))

  def take(l: ListA, n: Int): ListA = {
    require(n >= 0)
    l match {
      case ConsA(x, t) if n > 0 => ConsA(x, take(t, n - 1))
      case _Int                 => NilA
    }
  } ensuring (res => size(res) == _minInt(n, size(l)))

  def takeRight(l: ListA, n: Int): ListA = {
    require(n >= 0)
    val s = size(l)
    val m = _maxInt(s - n, 0)
    drop(l, m)
  } ensuring (res => size(res) == _minInt(n, size(l)))

  def contains(l: ListA, x: TypeA): Boolean = (l match {
    case NilA        => false
    case ConsA(y, t) => (x == y) || contains(t, x)
  })

  def startsWith(l1: ListA, l2: ListA): Boolean = {
    take(l1, size(l2)) == l2
  }

  def endsWith(l1: ListA, l2: ListA): Boolean = {
    takeRight(l1, size(l2)) == l2
  }

  def head(l: ListA): TypeA = {
    require(size(l) > 0)
    l match {
      case ConsA(x, t) => x
    }
  } ensuring (res => contains(l, res))

  def headOption(l: ListA): OptionA = (l match {
    case NilA        => NoneA
    case ConsA(x, _) => SomeA(x)
  }) ensuring (res => (res == NoneA && isEmpty(l)) || (res.isInstanceOf[SomeA] && !isEmpty(l)))

  def last(l: ListA): TypeA = {
    require(size(l) > 0)
    l match {
      case ConsA(x, NilA) => x
      case ConsA(x, t)    => last(t)
    }
  } ensuring (res => contains(l, res) && head(drop(l, size(l) - 1)) == res)

  def prepend(l: ListA, x: TypeA): ListA = {
    ConsA(x, l)
  } ensuring (res => size(res) == size(l) + 1 && drop(res, 1) == l && head(res) == x)

  def append(l: ListA, x: TypeA): ListA = {
    l match {
      case ConsA(y, t) => ConsA(y, append(t, x))
      case NilA        => ConsA(x, NilA)
    }
  } ensuring (res => size(res) == size(l) + 1 && take(res, size(res) - 1) == l && last(res) == x)

  def concat(l1: ListA, l2: ListA): ListA = (l1 match {
    case NilA        => l2
    case ConsA(x, t) => ConsA(x, concat(t, l2))
  }) ensuring (res => size(res) == size(l1) + size(l2) && take(res, size(l1)) == l1 && drop(res, size(l1)) == l2)

  def get(l: ListA, n: Int): TypeA = ({
    require(0 <= n && n < size(l))
    l match {
      case ConsA(x, t) if n == 0 => x
      case ConsA(_, t)           => get(t, n - 1)
    }
  }) ensuring (res => contains(l, res) && head(drop(l, n)) == res && last(take(l, n + 1)) == res)

  def exists(l: ListA, p: ListABool): Boolean = {
    require(_isTotalABool(l, p))
    l match {
      case NilA        => false
      case ConsA(x, t) => get(p, x) || exists(t, p)
    }
  }

  def forall(l: ListA, p: ListABool): Boolean = {
    require(_isTotalABool(l, p))
    l match {
      case NilA        => true
      case ConsA(x, t) => get(p, x) && forall(t, p)
    }
  }

  def count(l: ListA, p: ListABool): Int = {
    require(_isTotalABool(l, p))
    l match {
      case NilA                       => 0
      case ConsA(x, t) if (get(p, x)) => 1 + count(t, p)
      case ConsA(_, t)                => count(t, p)
    }
  } ensuring (res => (res > 0 && exists(l, p)) || (res == 0 && !exists(l, p)))

  def filter(l: ListA, p: ListABool): ListA = {
    require(_isTotalABool(l, p))
    l match {
      case NilA                     => NilA
      case ConsA(x, t) if get(p, x) => ConsA(x, filter(t, p))
      case ConsA(_, t)              => filter(t, p)
    }
  } ensuring (res => size(res) <= size(l) && _isTotalABool(res, p) && forall(res, p))

  def filterNot(l: ListA, p: ListABool): ListA = {
    require(_isTotalABool(l, p))
    l match {
      case NilA                      => NilA
      case ConsA(x, t) if !get(p, x) => ConsA(x, filterNot(t, p))
      case ConsA(_, t)               => filterNot(t, p)
    }
  } ensuring (res => size(res) <= size(l) && _isTotalABool(res, p) && !exists(res, p))

  def find(l: ListA, p: ListABool): OptionA = {
    require(_isTotalABool(l, p))
    l match {
      case NilA                     => NoneA
      case ConsA(x, _) if get(p, x) => SomeA(x)
      case ConsA(_, t)              => find(t, p)
    }
  } ensuring (res => (res == NoneA && !exists(l, p)) || (res.isInstanceOf[SomeA] && exists(l, p)))

  def partition(l: ListA, p: ListABool): (ListA, ListA) = {
    require(_isTotalABool(l, p))
    l match {
      case NilA => (NilA, NilA)
      case ConsA(x, t) =>
        val (l1, l2) = partition(t, p)
        if (get(p, x)) (ConsA(x, l1), l2) else (l1, ConsA(x, l2))
    }
  } ensuring (res => size(res._1) + size(res._2) == size(l) && res._1 == filter(l, p) && res._2 == filterNot(l, p)
    && forall(res._1, p) && !exists(res._2, p))

  def map(l: ListA, f: ListAB): ListB = {
    require(_isTotalAB(l, f))
    l match {
      case NilA        => NilB
      case ConsA(x, t) => ConsB(get(f, x), map(t, f))
    }
  } ensuring (res => size(l) == sizeB(res))

  def collect(l: ListA, f: ListAB): ListB = (l match {
    case NilA => NilB
    case ConsA(x, t) => getOption(f, x) match {
      case NoneB    => collect(t, f)
      case SomeB(y) => ConsB(y, collect(t, f))
    }
  }) ensuring (res => sizeB(res) <= size(l))

  def collectFirst(l: ListA, f: ListAB): OptionB = (l match {
    case NilA => NoneB
    case ConsA(x, t) => getOption(f, x) match {
      case NoneB         => collectFirst(t, f)
      case sy @ SomeB(y) => sy
    }
  })

  // Pair of elements of type A
  case class PairAA(l: TypeA, r: TypeA)

  //
  // List of pairs of elements of type A
  //
  sealed abstract class ListAA
  case object NilAA extends ListAA
  case class ConsAA(hd: PairAA, tl: ListAA) extends ListAA

  def sizeAA(l: ListAA): Int = (l match {
    case NilAA        => 0
    case ConsAA(_, t) => 1 + sizeAA(t)
  }) ensuring (res => (res == 0 && l == NilAA) || (res > 0 && l.isInstanceOf[ConsAA]))

  def zipAA(l1: ListA, l2: ListA): ListAA = ((l1, l2) match {
    case (NilA, _)                      => NilAA
    case (_, NilA)                      => NilAA
    case (ConsA(x1, t1), ConsA(x2, t2)) => ConsAA(PairAA(x1, x2), zipAA(t1, t2))
  }) ensuring (res => sizeAA(res) == _minInt(size(l1), size(l2)))

  def zipWithAllAA(l1: ListA, l2: ListA, x1: TypeA, x2: TypeA): ListAA = ((l1, l2) match {
    case (NilA, NilA)                   => NilAA
    case (ConsA(y1, t1), NilA)          => ConsAA(PairAA(y1, x2), zipWithAllAA(t1, NilA, x1, x2))
    case (NilA, ConsA(y2, t2))          => ConsAA(PairAA(x1, y2), zipWithAllAA(NilA, t2, x1, x2))
    case (ConsA(y1, t1), ConsA(y2, t2)) => ConsAA(PairAA(y1, y2), zipWithAllAA(t1, t2, x1, x2))
  }) ensuring (res => sizeAA(res) == _maxInt(size(l1), size(l2)))

  def unzipAA(l: ListAA): (ListA, ListA) = (l match {
    case NilAA => (NilA, NilA)
    case ConsAA(PairAA(x1, x2), t) =>
      val (t1, t2) = unzipAA(t)
      (ConsA(x1, t1), ConsA(x2, t2))
  }) ensuring (res => size(res._1) == sizeAA(l) && size(res._2) == sizeAA(l))

  //
  // Optional boolean
  //
  sealed abstract class OptionBool
  case object NoneBool extends OptionBool
  case class SomeBool(bool: Boolean) extends OptionBool

  def equal(o: OptionBool, b: Boolean): Boolean = o match {
    case NoneBool     => false
    case SomeBool(b2) => b == b2
  }

  // Pair of an element of type A and a boolean
  case class PairABool(l: TypeA, r: Boolean)

  //
  // Lists of pairs of elements of type A and booleans,
  // used to represent Map[A, Boolean],
  // in turn used to represent predicates
  //
  sealed abstract class ListABool
  case object NilABool extends ListABool
  case class ConsABool(hd: PairABool, tl: ListABool) extends ListABool

  def isDefinedAt(p: ListABool, x: TypeA): Boolean = (p match {
    case NilABool                      => false
    case ConsABool(PairABool(y, _), t) => (x == y) || isDefinedAt(t, x)
  })

  def get(p: ListABool, x: TypeA): Boolean = {
    require(isDefinedAt(p, x))
    p match {
      case ConsABool(PairABool(y, b), _) if x == y => b
      case ConsABool(_, t)                         => get(t, x)
    }
  }

  def getOption(p: ListABool, x: TypeA): OptionBool = (p match {
    case NilABool                                => NoneBool
    case ConsABool(PairABool(y, b), _) if x == y => SomeBool(b)
    case ConsABool(_, t)                         => getOption(t, x)
  }) ensuring (res => (res == NoneBool && !isDefinedAt(p, x)) || (res.isInstanceOf[SomeBool] && isDefinedAt(p, x) && equal(res, get(p, x))))

  //
  // Optional element of type A
  //
  sealed abstract class OptionA
  case object NoneA extends OptionA
  case class SomeA(x: TypeA) extends OptionA

  def equal(o: OptionA, x: TypeA): Boolean = o match {
    case NoneA    => false
    case SomeA(y) => x == y
  }

  //
  // Optional element of type B
  //
  sealed abstract class OptionB
  case object NoneB extends OptionB
  case class SomeB(x: TypeB) extends OptionB

  def equal(o: OptionB, x: TypeB): Boolean = o match {
    case NoneB    => false
    case SomeB(y) => x == y
  }

  // Pair of an element of type A and an element of type B
  case class PairAB(l: TypeA, r: TypeB)

  //
  // Lists of pairs of elements of type A and elements of type B,
  // used to represent Map[A, B],
  // in turn used to represent partial functions
  //
  sealed abstract class ListAB
  case object NilAB extends ListAB
  case class ConsAB(hd: PairAB, tl: ListAB) extends ListAB

  def isDefinedAt(f: ListAB, x: TypeA): Boolean = (f match {
    case NilAB                   => false
    case ConsAB(PairAB(y, _), t) => (x == y) || isDefinedAt(t, x)
  })

  def get(f: ListAB, x: TypeA): TypeB = {
    require(isDefinedAt(f, x))
    f match {
      case ConsAB(PairAB(y, z), _) if x == y => z
      case ConsAB(_, t)                      => get(t, x)
    }
  }

  def getOption(f: ListAB, x: TypeA): OptionB = (f match {
    case NilAB                             => NoneB
    case ConsAB(PairAB(y, z), _) if x == y => SomeB(z)
    case ConsAB(_, t)                      => getOption(t, x)
  }) ensuring (res => (res == NoneB && !isDefinedAt(f, x)) || (res.isInstanceOf[SomeB] && isDefinedAt(f, x) && equal(res, get(f, x))))

  def size2(l: ListAB): Int = (l match {
    case NilAB        => 0
    case ConsAB(_, t) => 1 + size2(t)
  }) ensuring (res => (res == 0 && l == NilAB) || (res > 0 && l.isInstanceOf[ConsAB]))

  def zip(l1: ListA, l2: ListB): ListAB = ((l1, l2) match {
    case (NilA, _)                      => NilAB
    case (_, NilB)                      => NilAB
    case (ConsA(x1, t1), ConsB(x2, t2)) => ConsAB(PairAB(x1, x2), zip(t1, t2))
  }) ensuring (res => size2(res) == _minInt(size(l1), sizeB(l2)))

  def zipWithAll(l1: ListA, l2: ListB, x1: TypeA, x2: TypeB): ListAB = ((l1, l2) match {
    case (NilA, NilB)                   => NilAB
    case (ConsA(y1, t1), NilB)          => ConsAB(PairAB(y1, x2), zipWithAll(t1, NilB, x1, x2))
    case (NilA, ConsB(y2, t2))          => ConsAB(PairAB(x1, y2), zipWithAll(NilA, t2, x1, x2))
    case (ConsA(y1, t1), ConsB(y2, t2)) => ConsAB(PairAB(y1, y2), zipWithAll(t1, t2, x1, x2))
  }) ensuring (res => size2(res) == _maxInt(size(l1), sizeB(l2)))

  def unzip(l: ListAB): (ListA, ListB) = (l match {
    case NilAB => (NilA, NilB)
    case ConsAB(PairAB(x1, x2), t) =>
      val (t1, t2) = unzip(t)
      (ConsA(x1, t1), ConsB(x2, t2))
  }) ensuring (res => size(res._1) == size2(l) && sizeB(res._2) == size2(l))

  //
  // Utils
  //

  def _minInt(x: Int, y: Int): Int = {
    if (x <= y) x else y
  } ensuring (res => res <= x && res <= y && (res == x || res == y))

  def _maxInt(x: Int, y: Int): Int = {
    if (x >= y) x else y
  } ensuring (res => res >= x && res >= y && (res == x || res == y))

  def _isTotalABool(l: ListA, p: ListABool): Boolean = (l match {
    case NilA        => true
    case ConsA(x, t) => isDefinedAt(p, x) && _isTotalABool(t, p)
  })

  def _isTotalAB(l: ListA, f: ListAB): Boolean = (l match {
    case NilA                             => true
    case ConsA(x, t) if isDefinedAt(f, x) => _isTotalAB(t, f)
    case _                                => false
  })
}
