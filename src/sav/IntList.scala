import leon.Utils._

object obj {

  //
  // INT LIST
  //
  sealed abstract class IntList
  case object Nil extends IntList
  case class Cons(hd: Int, tl: IntList) extends IntList

  def size(l: IntList): Int = (l match {
    case Nil        => 0
    case Cons(_, t) => 1 + size(t)
  }) ensuring (res => (res == 0 && l == Nil) || (res > 0 && l.isInstanceOf[Cons]))

  def isEmpty(l: IntList) = (l match {
    case Nil => true
    case _   => false
  }) ensuring (res => (res && l == Nil) || (!res && l.isInstanceOf[Cons]))

  def map(l: IntList, f: IntIntMap): IntList = {
    require(_isTotalIntInt(l, f))
    l match {
      case Nil        => Nil
      case Cons(x, t) => Cons(get(f, x), map(t, f))
    }
  } ensuring (res => size(l) == size(res))

  def forall(l: IntList, p: IntBoolMap): Boolean = {
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

  def filter(l: IntList, p: IntBoolMap): IntList = {
    require(_isTotalIntBool(l, p))
    l match {
      case Nil                     => Nil
      case Cons(x, t) if get(p, x) => Cons(x, filter(t, p))
      case Cons(_, t)              => filter(t, p)
    }
  } ensuring (res => size(res) <= size(l) && _isTotalIntBool(res, p) && forall(res, p))

  def exists(l: IntList, p: IntBoolMap): Boolean = {
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
  } // ensuring (res => _isLowerBound(l, res) && contains(l, res))

  //   def _isPermutationOf(l1: IntList, l2: IntList): Boolean = {
  //      sortAscending(l1) == sortAscending(l2)
  //   }

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

  //     def _sortAscending_merge(l1: IntList, l2: IntList, acum: IntList): IntList = {
  //        require(_hasAscendingOrder(acum))
  //        (sortAscending(l1), sortAscending(l2)) match {
  //           case (Nil, Nil)                              => acum
  //           case (Cons(x1, t1), Nil)                     => _sortAscending_merge(t1, Nil, append(acum, x1))
  //           case (Nil, Cons(x2, t2))                     => _sortAscending_merge(Nil, t2, append(acum, x2))
  //           case (Cons(x1, t1), Cons(x2, _)) if x1 <= x2 => _sortAscending_merge(t1, l2, append(acum, x1))
  //           case (Cons(x1, _), Cons(x2, t2)) if x1 > x2  => _sortAscending_merge(l1, t2, append(acum, x2))
  //        }
  //     } ensuring (res => size(res) == size(l1) + size(l2) + size(acum) && _hasAscendingOrder(res))
  //  
  //     def sortAscending(l: IntList): IntList = {
  //        l match {
  //           case Nil                   => Nil
  //           case Cons(x, Nil)          => l
  //           case Cons(x, Cons(y, Nil)) => if (x <= y) l else Cons(y, Cons(x, Nil))
  //           case Cons(x, t) =>
  //              val mid = size(l) / 2
  //              val l1 = take(l, mid)
  //              val l2 = drop(l, mid)
  //              _sortAscending_merge(l1, l2, Nil)
  //        }
  //     } ensuring (res => size(res) == size(l) && _hasAscendingOrder(res))

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
  sealed abstract class IntBoolMap
  case object NilIntBoolMap extends IntBoolMap
  case class ConsIntBoolMap(hd: (Int, Boolean), tl: IntBoolMap) extends IntBoolMap

  def isDefinedAt(p: IntBoolMap, x: Int): Boolean = (p match {
    case NilIntBoolMap                       => false
    case ConsIntBoolMap((y, _), _) if x == y => true
    case ConsIntBoolMap(_, t)                => isDefinedAt(t, x)
  })

  def get(p: IntBoolMap, x: Int): Boolean = {
    require(isDefinedAt(p, x))
    p match {
      case ConsIntBoolMap((y, b), _) if x == y => b
      case ConsIntBoolMap(_, t)                => get(t, x)
    }
  }

  def getOption(p: IntBoolMap, x: Int): OptionBool = {
    (p match {
      case NilIntBoolMap                       => NoneBool
      case ConsIntBoolMap((y, b), _) if x == y => SomeBool(b)
      case ConsIntBoolMap(_, t)                => getOption(t, x)
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

  def _isTotalIntBool(l: IntList, p: IntBoolMap): Boolean = (l match {
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

}
