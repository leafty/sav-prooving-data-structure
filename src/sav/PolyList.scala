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

  def take(l: ListA, n: Int): ListA = {
    require(n >= 0)
    l match {
      case ConsA(x, t) if n > 0 => ConsA(x, take(t, n - 1))
      case _Int                 => NilA
    }
  } ensuring (res => size(res) == _minInt(n, size(l)))

  def contains(l: ListA, x: TypeA): Boolean = (l match {
    case NilA        => false
    case ConsA(y, t) => (x == y) || contains(t, x)
  })

  def head(l: ListA): TypeA = {
    require(size(l) > 0)
    l match {
      case ConsA(x, t) => x
    }
  } ensuring (res => contains(l, res))

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
  }) ensuring (res => size(res) == size(l1) + size(l2) && _isPrefix(l1, res) && drop(res, size(l1)) == l2)

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

  def filter(l: ListA, p: ListABool): ListA = {
    require(_isTotalABool(l, p))
    l match {
      case NilA                     => NilA
      case ConsA(x, t) if get(p, x) => ConsA(x, filter(t, p))
      case ConsA(_, t)              => filter(t, p)
    }
  } ensuring (res => size(res) <= size(l) && _isTotalABool(res, p) && forall(res, p))

  def map(l: ListA, f: ListAB): ListB = {
    require(_isTotalAB(l, f))
    l match {
      case NilA        => NilB
      case ConsA(x, t) => ConsB(get(f, x), map(t, f))
    }
  } ensuring (res => size(l) == sizeB(res))

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

  def _isPrefix(l1: ListA, l2: ListA): Boolean = {
    val (ll1, ll2) = unzipAA(zipAA(l1, l2))
    l1 == ll1 && l1 == ll2
  }

  def _isTotalABool(l: ListA, p: ListABool): Boolean = (l match {
    case NilA        => true
    case ConsA(x, t) => isDefinedAt(p, x) && _isTotalABool(t, p)
  })

  def _isTotalAB(l: ListA, f: ListAB): Boolean = (l match {
    case NilA                             => true
    case ConsA(x, t) if isDefinedAt(f, x) => _isTotalAB(t, f)
    case _                                => false
  })

  /*

  def map(l: IntList, f: IntIntMap): IntList = {
    require(_isTotalIntInt(l, f))
    l match {
      case Nil        => Nil
      case Cons(x, t) => Cons(get(f, x), map(t, f))
    }
  } ensuring (res => size(l) == size(res))

  def forall(l: IntList, p: ListABool): Boolean = {
    require(_isTotalIntBool(l, p))
    l match {
      case Nil                     => true
      case Cons(x, t) if get(p, x) => forall(t, p)
      case _                       => false
    }
  }

  def get(l: IntList, n: Int): Int = ({
    require(0 <= n && n < size(l))
    l match {
      case Cons(x, t) if n == 0 => x
      case Cons(_, t)           => get(t, n - 1)
    }
  }) ensuring (res => contains(l, res) && head(drop(l, n)) == res && last(take(l, n + 1)) == res)

  def filter(l: IntList, p: ListABool): IntList = {
    require(_isTotalIntBool(l, p))
    l match {
      case Nil                     => Nil
      case Cons(x, t) if get(p, x) => Cons(x, filter(t, p))
      case Cons(_, t)              => filter(t, p)
    }
  } ensuring (res => size(res) <= size(l) && _isTotalIntBool(res, p) && forall(res, p))

  def exists(l: IntList, p: ListABool): Boolean = {
    require(_isTotalIntBool(l, p))
    l match {
      case Nil                     => false
      case Cons(x, t) if get(p, x) => true
      case Cons(_, t)              => exists(t, p)
    }
  }

  def drop(l: IntList, n: Int): IntList = {
    require(n >= 0)
    l match {
      case Cons(x, t) if n > 0 => drop(t, n - 1)
      case Nil if n > 0        => Nil
      case _ if n == 0         => l
    }
  } ensuring (res => size(res) == _maxInt(0, size(l) - n))

  def take(l: IntList, n: Int): IntList = {
    require(n >= 0)
    l match {
      case Cons(x, t) if n > 0 => Cons(x, take(t, n - 1))
      case _                   => Nil
    }
  } ensuring (res => size(res) == _minInt(n, size(l)))

  def contains(l: IntList, x: Int): Boolean = (l match {
    case Nil                  => false
    case Cons(y, t) if x == y => true
    case Cons(_, t)           => contains(t, x)
  })

  def head(l: IntList): Int = {
    require(size(l) > 0)
    l match {
      case Nil        => 0 // will never be the case
      case Cons(x, t) => x
    }
  } ensuring (res => contains(l, res))

  def last(l: IntList): Int = {
    require(size(l) > 0)
    l match {
      case Nil          => 0 // will never be the case
      case Cons(x, Nil) => x
      case Cons(x, t)   => last(t)
    }
  } ensuring (res => contains(l, res) && head(drop(l, size(l) - 1)) == res)

  def prepend(l: IntList, x: Int): IntList = {
    Cons(x, l)
  } ensuring (res => size(res) == size(l) + 1 && drop(res, 1) == l && head(res) == x)

  def append(l: IntList, x: Int): IntList = {
    l match {
      case Cons(y, t) => Cons(y, append(t, x))
      case Nil        => Cons(x, Nil)
    }
  } ensuring (res => size(res) == size(l) + 1 && take(res, size(res) - 1) == l && last(res) == x)

  def concat(l1: IntList, l2: IntList): IntList = (l1 match {
    case Nil        => l2
    case Cons(x, t) => Cons(x, concat(t, l2))
  }) ensuring (res => size(res) == size(l1) + size(l2) && _isPrefix(l1, res) && drop(res, size(l1)) == l2)


//   def _concatRightNil(l1: IntList): Boolean = {
//    concat(l1, Nil) == l1
//  } holds
//  
//    def _concatAso(l1: IntList, l2: IntList, l3: IntList): Boolean = {
//    concat(concat(l1, l2),l3) == concat(l1,concat(l2,l3))
//  } holds
  
  def min(l: IntList): Int = {
    require(size(l) > 0)
    l match {
      case Cons(x, t) => _min1(t, x)
      case Nil        => 0 // avoid match warning
    }
  } ensuring (res => _isLowerBound(l, res) && contains(l, res))

  def _hasAscendingOrder(l: IntList): Boolean = {
    l match {
      case Cons(x, t @ Cons(y, _)) => x <= y && _hasAscendingOrder(t)
      case _                       => true
    }
  } ensuring (res => (res || size(l) > 1))

  def _hasStrictAscendingOrder(l: IntList): Boolean = l match {
    case Cons(x, t @ Cons(y, _)) => x < y && _hasStrictAscendingOrder(t)
    case _                       => true
  }

  def _hasDescendingOrder(l: IntList): Boolean = l match {
    case Cons(x, t @ Cons(y, _)) => x >= y && _hasDescendingOrder(t)
    case _                       => true
  }

  def _hasStrictDescendingOrder(l: IntList): Boolean = l match {
    case Cons(x, t @ Cons(y, _)) => x > y && _hasStrictDescendingOrder(t)
    case _                       => true
  }

  def _mergeAscending(l1: IntList, l2: IntList): IntList = {
    require(_hasAscendingOrder(l1) && _hasAscendingOrder(l2))
    (l1, l2) match {
      case (Nil, Nil) => Nil
      case (_, Nil) => l1
      case (Nil, _) => l2
      case (Cons(y1, t1), Cons(y2, _)) if y1 < y2 =>
        val t = _mergeAscending(t1, l2)
        Cons(y1, t)
      case (Cons(y1, _), Cons(y2, t2)) =>
        val t = _mergeAscending(l1, t2)
        Cons(y2, t)
    }
  } ensuring (res => size(res) == size(l1) + size(l2) && _hasAscendingOrder(res))
  
  def sortAscending(l: IntList): IntList = (l match {
    case Nil => Nil
    case Cons(x, t) => _mergeAscending(Cons(x, Nil), sortAscending(t))
  }) ensuring (res => size(res) == size(l) && _hasAscendingOrder(res))

  //
  // INT PAIR LIST
  //
  sealed abstract class IntIntMap
  case object NilIntIntMap extends IntIntMap
  case class ConsIntIntMap(hd: (Int, Int), tl: IntIntMap) extends IntIntMap

  def isDefinedAt(p: IntIntMap, x: Int): Boolean = (p match {
    case NilIntIntMap                       => false
    case ConsIntIntMap((y, _), _) if x == y => true
    case ConsIntIntMap(_, t)                => isDefinedAt(t, x)
  })

  def get(p: IntIntMap, x: Int): Int = {
    require(isDefinedAt(p, x))
    p match {
      case ConsIntIntMap((y, z), _) if x == y => z
      case ConsIntIntMap(_, t)                => get(t, x)
    }
  }

  def getOption(f: IntIntMap, x: Int): OptionInt = {
    (f match {
      case NilIntIntMap                       => NoneInt
      case ConsIntIntMap((y, z), _) if x == y => SomeInt(z)
      case ConsIntIntMap(_, t)                => getOption(t, x)
    })
  } ensuring (res => (res == NoneInt && !isDefinedAt(f, x)) || (res.isInstanceOf[SomeInt] && isDefinedAt(f, x) && equal(res, get(f, x))))

  //
  // INT BOOL MAP 
  //
  sealed abstract class ListABool
  case object NilABool extends ListABool
  case class ConsABool(hd: (Int, Boolean), tl: ListABool) extends ListABool

  def isDefinedAt(p: ListABool, x: Int): Boolean = (p match {
    case NilABool                       => false
    case ConsABool((y, _), _) if x == y => true
    case ConsABool(_, t)                => isDefinedAt(t, x)
  })

  def get(p: ListABool, x: Int): Boolean = {
    require(isDefinedAt(p, x))
    p match {
      case ConsABool((y, b), _) if x == y => b
      case ConsABool(_, t)                => get(t, x)
    }
  }

  def getOption(p: ListABool, x: Int): OptionBool = {
    (p match {
      case NilABool                       => NoneBool
      case ConsABool((y, b), _) if x == y => SomeBool(b)
      case ConsABool(_, t)                => getOption(t, x)
    })
  } ensuring (res => (res == NoneBool && !isDefinedAt(p, x)) || (res.isInstanceOf[SomeBool] && isDefinedAt(p, x) && equal(res, get(p, x))))

  //
  // OPTION BOOLEAN
  //
  sealed abstract class OptionBool
  case object NoneBool extends OptionBool
  case class SomeBool(bool: Boolean) extends OptionBool

  def equal(o: OptionBool, b: Boolean): Boolean = o match {
    case NoneBool     => false
    case SomeBool(b2) => b == b2
  }

  //
  // OPTION INT
  //
  sealed abstract class OptionInt
  case object NoneInt extends OptionInt
  case class SomeInt(n: Int) extends OptionInt

  def equal(o: OptionInt, n: Int): Boolean = o match {
    case NoneInt     => false
    case SomeInt(n2) => n == n2
  }

  //
  // UTILS
  // 

  def _minInt(x: Int, y: Int): Int = {
    if (x <= y) x else y
  } ensuring (res => res <= x && res <= y && (res == x || res == y))

  def _maxInt(x: Int, y: Int): Int = {
    if (x >= y) x else y
  } ensuring (res => res >= x && res >= y && (res == x || res == y))

  def tail(l: IntList) = l match {
    case Nil        => error("tail of emtpy list")
    case Cons(x, t) => t
  }

  def _isTotalIntInt(l: IntList, f: IntIntMap): Boolean = (l match {
    case Nil                             => true
    case Cons(x, t) if isDefinedAt(f, x) => _isTotalIntInt(t, f)
    case _                               => false
  })

  def _isTotalIntBool(l: IntList, p: ListABool): Boolean = (l match {
    case Nil                             => true
    case Cons(x, t) if isDefinedAt(p, x) => _isTotalIntBool(t, p)
    case _                               => false
  })

  def _isPrefix(l1: IntList, l2: IntList): Boolean = {
    val (ll1, ll2) = unzip(zip(l1, l2))
    l1 == ll1 && l1 == ll2
  }

  def isEmpty2(l: IntIntMap) = l match {
    case NilIntIntMap => true
    case _            => false
  }

  def head2(l: IntIntMap) = l match {
    case NilIntIntMap        => error("head of emtpy list")
    case ConsIntIntMap(x, t) => x
  }

  def tail2(l: IntIntMap) = l match {
    case NilIntIntMap        => error("tail of emtpy list")
    case ConsIntIntMap(x, t) => t
  }

  def size2(l: IntIntMap): Int = (l match {
    case NilIntIntMap        => 0
    case ConsIntIntMap(_, t) => 1 + size2(t)
  }) ensuring (res => (res == 0 && l == NilIntIntMap) || (res > 0 && l.isInstanceOf[ConsIntIntMap]))

  def concat2(l1: IntIntMap, l2: IntIntMap): IntIntMap = (l1 match {
    case NilIntIntMap        => l2
    case ConsIntIntMap(x, t) => ConsIntIntMap(x, concat2(t, l2))
  }) ensuring (res => size2(res) == size2(l1) + size2(l2))

  def zip(l1: IntList, l2: IntList): IntIntMap = ((l1, l2) match {
    case (Nil, _)                     => NilIntIntMap
    case (_, Nil)                     => NilIntIntMap
    case (Cons(x1, t1), Cons(x2, t2)) => ConsIntIntMap((x1, x2), zip(t1, t2))
  }) ensuring (res => size2(res) == _minInt(size(l1), size(l2)))

  def zipWithAll(l1: IntList, l2: IntList, x1: Int, x2: Int): IntIntMap = ((l1, l2) match {
    case (Nil, Nil)                   => NilIntIntMap
    case (Cons(y1, t1), Nil)          => ConsIntIntMap((y1, x2), zipWithAll(t1, Nil, x1, x2))
    case (Nil, Cons(y2, t2))          => ConsIntIntMap((x1, y2), zipWithAll(Nil, t2, x1, x2))
    case (Cons(y1, t1), Cons(y2, t2)) => ConsIntIntMap((y1, y2), zipWithAll(t1, t2, x1, x2))
  }) ensuring (res => size2(res) == _maxInt(size(l1), size(l2)))

  def unzip(l: IntIntMap): (IntList, IntList) = (l match {
    case NilIntIntMap => (Nil, Nil)
    case ConsIntIntMap((x1, x2), t) =>
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

  */
}
