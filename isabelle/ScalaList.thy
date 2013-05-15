theory ScalaList
imports Main Datatype ScalaOption ScalaPartialFunction

begin

datatype 'a List = Nil | Cons 'a "'a List"  (infixr "::" 65)

primrec toIsabelleList :: "'a List \<Rightarrow> 'a list" where
"toIsabelleList Nil      = []" |
"toIsabelleList(x :: xs) = x # (toIsabelleList xs)" 

type_synonym Boolean = bool

(* def size: Int
The size of this list, equivalent to length.
returns: the number of elements in this list. *)
primrec size :: "'a List \<Rightarrow> nat" where 
"size(Nil)     = 0" | 
"size(x :: xs) = 1 + size(xs)"

lemma "size(xs) \<ge> 0"
apply(auto)
done

lemma "size(x :: xs) > 0"
apply(auto)
done

theorem [simp]: "size(xs) = 0 \<longleftrightarrow> xs = Nil"
apply(case_tac xs)
apply(auto)
done





(* def isDefinedAt(x: Int): Boolean
Tests whether this list contains given index.
The implementations of methods apply and isDefinedAt turn a Seq[A] into a PartialFunction[Int, A].
returns: true if this list contains an element at position idx, false otherwise.*)
primrec isDefinedAt :: "'a List \<Rightarrow> nat \<Rightarrow> Boolean" (infix "isDefinedAt" 65)  where
"      Nil isDefinedAt n = False" |
"(x :: xs) isDefinedAt n = (n < size(x :: xs))"

theorem [simp]: "\<not>(xs isDefinedAt(0)) \<longleftrightarrow> xs = Nil"
apply(induct_tac xs)
apply(auto)
done

theorem [simp]: "xs isDefinedAt(0) \<longleftrightarrow> xs \<noteq> Nil"
apply(induct_tac xs)
apply(auto)
done

theorem [simp]: "\<not>( \<exists>n. xs isDefinedAt(n) \<and> n \<ge> size(xs) )"
apply(induct_tac xs)
apply(auto)
done





(* def isEmpty: Boolean 
Tests whether this list is empty.
returns true if the list contain no elements, false otherwise. *)
primrec isEmpty :: "'a List => Boolean" where
"isEmpty(Nil)     = True" | 
"isEmpty(x :: xs) = False"

(* A list is empty iff the list is Nil  *)
lemma [simp]: "isEmpty(xs) \<longleftrightarrow> xs = Nil"
apply(induct_tac xs)
apply(auto)
done

(* A list is empty iff the list has size 0  *)
lemma "\<forall>xs. isEmpty(xs) \<longleftrightarrow> size xs = 0"
apply(simp)
done

(* A list is empty iff the there is no value defined at the first position *)
lemma "\<forall>xs. isEmpty(xs) \<longleftrightarrow> \<not>(xs isDefinedAt 0) "
apply(simp)
done




(* def nonEmpty: Boolean
Tests whether the list is not empty.
returns: true if the list contains at least one element, false otherwise. *)
primrec nonEmpty :: "'a List => Boolean" where
"nonEmpty(Nil)     = False" | 
"nonEmpty(x :: xs) = True"

lemma [simp]: "nonEmpty(xs) \<longleftrightarrow> ( \<not>isEmpty(xs) )"
apply(case_tac xs)
apply(auto)
done

theorem "\<forall>xs. isEmpty(xs) \<noteq> nonEmpty(xs)"
apply(auto)
done




(* def :::(prefix: List[A]): List[A]
[use case] 
  Adds the elements of a given list in front of this list.
  Example: List(1, 2) ::: List(3, 4) = List(3, 4).:::(List(1, 2)) = List(1, 2, 3, 4)
prefix: The list elements to prepend.
returns: a list resulting from the concatenation of the given list prefix and this list.
Full Signature: def :::[B >: A](prefix: List[B]): List[B] *)
primrec append :: "'a List => 'a List => 'a List" (infixr ":::" 65) where 
"      Nil ::: ys = ys" | 
"(x :: xs) ::: ys = x :: (xs ::: ys)" 

lemma [simp]: "xs ::: Nil = xs"
apply(induct_tac xs)
apply(auto)
done

lemma [simp]: "\<forall>ys. size(xs ::: ys) = size(xs) + size(ys)"
apply(induct_tac xs)
apply(auto)
done

lemma [simp]: "\<forall>ys zs. (xs ::: ys) ::: zs = xs ::: (ys ::: zs)" 
apply(induct_tac xs)
apply(auto)
done




(* def reverse: List[A]
Returns new list wih elements in reversed order.
returns: A new list with all elements of this list in reversed order. *)
primrec reverse :: "'a List => 'a List" where 
"reverse(Nil)     = Nil" | 
"reverse(x :: xs) = reverse(xs) ::: (x::Nil)"

lemma [simp]: "\<forall>ys. reverse(xs ::: ys) = reverse(ys) ::: reverse(xs)"
apply(induct_tac xs)
apply(auto)
done

lemma [simp]: "size(reverse(xs)) = size(xs)"
apply(induct_tac xs)
apply(auto)
done

(* reverse coposed with referse yiels the identity function on lists *)
theorem [simp]: "reverse(reverse(xs)) = xs"
apply(induct_tac xs)
apply(auto)
done

theorem [simp]: "reverse(xs ::: (reverse xs) ) = xs ::: (reverse xs)"
apply(induct_tac xs)
apply(auto)
done

theorem [simp]: "reverse( (reverse xs) ::: xs ) = (reverse xs) ::: xs"
apply(induct_tac xs)
apply(auto)
done





(* def exists(p: (A) \<Rightarrow> Boolean): Boolean
Tests whether a predicate holds for some of the elements of this list.
p: the predicate used to test elements.
returns: true if the given predicate p holds for some of the elements of this list, otherwise false. *)
primrec exists :: "'a List \<Rightarrow> ('a \<Rightarrow> Boolean) \<Rightarrow> Boolean" (infix "exists" 65)  where
"      Nil exists(p) = False" |
"(x :: xs) exists(p) = ( p(x) \<or> ( xs exists(p) ) )"

theorem "\<forall>p. xs exists(p) = (\<exists>y ys. (xs = y :: ys) \<and> ( p(y) \<or> ys exists(p) ) ) "
apply(induct_tac xs)
apply(auto)
done





primrec forall :: "'a List \<Rightarrow> ('a \<Rightarrow> Boolean) \<Rightarrow> Boolean" (infix "forall" 65) where
"      Nil forall(p) = True" |
"(x :: xs) forall(p) = ( p(x) \<and>  xs forall(p) )"

theorem "\<forall>p. xs forall(p) \<longleftrightarrow> xs = Nil \<or> (\<exists>y ys. xs = y::ys \<and>  p(y) \<and> ys forall(p)  ) "
apply(induct_tac xs)
apply(auto)
done

theorem [simp]: "\<forall>p. \<not>( xs forall(p) ) = xs exists(\<lambda>x. \<not>(p x))"
apply(induct_tac xs)
apply(auto)
done

theorem [simp]: "\<forall>p. \<not>( xs exists(p) ) = xs forall(\<lambda>x. \<not>(p x))"
apply(induct_tac xs)
apply(auto)
done





primrec contains :: "'a List \<Rightarrow> 'a \<Rightarrow> Boolean" (infix "contains" 65) where
"      Nil contains(elem) = False" |
"(x :: xs) contains(elem) = ( (x = elem) \<or> ( xs contains(elem) ) )"

theorem [simp]: "\<forall>elem. xs contains(elem) = xs exists(\<lambda>a. a = elem)"
apply(induct_tac xs)
apply(auto)
done





primrec count :: "'a List \<Rightarrow> ('a \<Rightarrow> Boolean) \<Rightarrow> nat" (infix "count" 65) where
"      Nil count(p) = 0" |
"(x :: xs) count(p) = ( let c = xs count(p) in (if p(x) then c+1 else c) )"

lemma "xs count(p) \<le> size xs"
apply(induct_tac xs)
apply(auto)
apply(simp add: Let_def)
done






primrec filter :: "'a List \<Rightarrow> ('a \<Rightarrow> Boolean) \<Rightarrow> 'a List" (infix "filter" 65) where
"      Nil filter(p) = Nil" |
"(x :: xs) filter(p) = ( if p(x) then x :: ( xs filter p) else xs filter(p) )"

lemma [simp]: "size(xs filter p) \<le> size(xs)"
apply(induct_tac xs)
apply(auto)
done

theorem "\<forall>p. (xs filter p) forall p"
apply(induct_tac xs)
apply(auto)
done

theorem [simp]: "\<forall>p. size(xs filter p) = xs count(p)"
apply(induct_tac xs)
apply(auto)
done





primrec filterNot :: "'a List \<Rightarrow> ('a \<Rightarrow> Boolean) \<Rightarrow> 'a List" (infix "filterNot" 65) where
"      Nil filterNot p = Nil" |
"(x :: xs) filterNot p = ( if \<not>(p x) then x :: (xs filterNot p) else xs filterNot p )"

lemma "size(xs filterNot p) \<le> size(xs)"
apply(induct_tac xs)
apply(auto)
done

theorem "\<forall>p. (xs filterNot(p)) forall(\<lambda>x. \<not> p x)"
apply(induct_tac xs)
apply(auto)
done

theorem [simp]: "\<forall>p. size(xs filterNot(p)) = xs count(\<lambda>x. \<not> p x)"
apply(induct_tac xs)
apply(auto)
done





primrec headOption :: "'a List \<Rightarrow> 'a Option" where
"headOption(Nil)     = None" |
"headOption(x :: xs) = Some(x)"

lemma [simp]: "headOption(xs) = None \<longleftrightarrow> xs = Nil"
apply(case_tac xs)
apply(auto)
done




primrec lastOption_rec :: "'a List \<Rightarrow> 'a \<Rightarrow> 'a" where
"lastOption_rec   Nil      x = x" |
"lastOption_rec (x :: xs)  _ = lastOption_rec xs x"

primrec lastOption :: "'a List \<Rightarrow> 'a Option" where
"lastOption(Nil)     = None" |
"lastOption(x :: xs) = Some(lastOption_rec xs x)"

lemma [simp]: "lastOption(xs) = None \<longleftrightarrow> xs = Nil"
apply(case_tac xs)
apply(auto)
done

lemma [simp]: "\<forall>x ys. lastOption_rec(xs ::: (x :: Nil)) ys = x"
apply(induct_tac xs)
apply(auto)
done

lemma [simp]: "\<forall>x. lastOption( xs ::: (x :: Nil) ) = Some(x)"
apply(case_tac xs)
apply(auto)
done

theorem [simp]: "lastOption(reverse(xs)) = headOption(xs)"
apply(case_tac xs)
apply(auto)
done





primrec tailOption :: "'a List \<Rightarrow> 'a List Option" where
"tailOption(Nil)     = None" |
"tailOption(x :: xs) = Some xs"

theorem [simp]: " \<lbrakk> xs \<noteq> Nil \<rbrakk> \<Longrightarrow> \<exists>ys. tailOption(xs) = Some(ys)"
apply(case_tac xs)
apply(auto)
done

theorem " xs = Nil \<longleftrightarrow> tailOption(xs) = None"
apply(case_tac xs)
apply(auto)
done



primrec getOrElse :: "'a List \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
"getOrElse       Nil n e = e" |
"getOrElse (x :: xs) n e = (case n of 0 \<Rightarrow> x | Suc n1 \<Rightarrow> getOrElse xs n1 e )"

lemma [simp]: "\<forall>e. getOrElse Nil n e = e"
apply(induct_tac n)
apply(auto)
done

lemma [simp]: "\<forall>e. getOrElse xs (size xs) e = e"
apply(induct_tac xs)
apply(auto)
done





primrec drop :: "'a List \<Rightarrow> nat \<Rightarrow> 'a List" (infix "drop" 65) where
"      Nil drop(n) = Nil" |
"(x :: xs) drop(n) = ( case n of 0 \<Rightarrow> x :: xs | Suc m \<Rightarrow> xs drop(m) )"

lemma [simp]: "xs drop(0) = xs"
apply(case_tac xs)
apply(auto)
done

lemma [simp]: "xs drop(size xs) = Nil"
apply(induct_tac xs)
apply(auto)
done





primrec take :: "'a List \<Rightarrow> nat \<Rightarrow> 'a List" (infix "take" 65) where
"      Nil take(n) = Nil" |
"(x :: xs) take(n) = ( case n of 0 \<Rightarrow> Nil | Suc m \<Rightarrow> x :: (xs take(m)) )"

lemma [simp]: "xs take(0) = Nil"
apply(induct_tac xs)
apply(auto)
done

lemma [simp]: "xs take(size xs) = xs"
apply(induct_tac xs)
apply(auto)
done




primrec slice :: "'a List \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a List"  where
"slice       Nil a b = Nil" |
"slice (x :: xs) a b =  ( (x :: xs) take(b) ) drop(a)"

lemma [simp]: "\<forall>b. slice xs 0 b = xs take(b)"
apply(case_tac xs)
apply(auto)
done

lemma [simp]: "slice xs 0 (size xs) = xs"
apply(case_tac xs)
apply(auto)
done

lemma [simp]: "\<forall>n. slice xs n (size xs) = xs drop n"
apply(induct_tac xs)
apply(auto)
done





primrec find :: "'a List \<Rightarrow> ('a \<Rightarrow> Boolean) \<Rightarrow> 'a Option" (infix "find" 65) where
"      Nil find(p) = None" |
"(x :: xs) find(p) = (if (p x) then Some x else xs find(p) )"

lemma [simp]: "\<forall>p. (xs find(p) = None) = xs forall(\<lambda>x. \<not>(p x))"
apply(induct_tac xs)
apply(auto)
done

lemma "\<forall>x. xs contains(x) = (xs find(\<lambda>a. a = x) = Some x)"
apply(induct_tac xs)
apply(auto)
done




(* def map[B](f: (A) \<Rightarrow> B): List[B]
[use case]
  Builds a new collection by applying a function to all elements of this list.
B: the element type of the returned collection.
f: the function to apply to each element.
returns: a new list resulting from applying the given function f to each element of this list and collecting the results. *)
primrec map :: "'a List \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b List" (infix "map" 65) where
"      Nil map(_) = Nil" |
"(x :: xs) map(f) = (f x) :: (xs map(f))"

lemma [simp]: "\<forall>p. size (xs map(p)) = size xs"
apply(induct_tac xs)
apply(auto)
done



(* def mapConserve(f: (A) \<Rightarrow> A): List[A]
[use case]
  Builds a new list by applying a function to all elements of this list. Like xs map f, but returns xs unchanged if function f maps all elements to themselves (as determined by eq).
f: the function to apply to each element.
returns: a list resulting from applying the given function f to each element of this list and collecting the results. *)
primrec mapConverse :: "'a List \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a List" (infix "mapConverse" 65) where
"      Nil mapConverse(f) = Nil" |
"(x :: xs) mapConverse(f) = (f x) :: (xs mapConverse(f))"

lemma [simp]: "\<forall>p. size (xs mapConverse(p)) = size xs"
apply(induct_tac xs)
apply(auto)
done

lemma "\<forall>p::('a \<Rightarrow> 'a). xs map(p) = xs mapConverse(p)"
apply(induct_tac xs)
apply(auto)
done


(* def collect[B](pf: PartialFunction[A, B]): List[B]
[use case]
  Builds a new collection by applying a partial function to all elements of this list on which the function is defined.
B: the element type of the returned collection.
pf:the partial function which filters and maps the list.
returns: a new list resulting from applying the given partial function pf to each element on which it is defined and collecting the results. The order of the elements is preserved. *)
primrec collect :: "'a List \<Rightarrow> (('a, 'b) PartialFunction) \<Rightarrow> 'b List" (infix "collect" 65) where
"      Nil collect(_) = Nil" |
"(x :: xs) collect(pf) = ( if pf isDefAt x then (pf apply x) :: ( xs collect(pf)) else ( xs collect(pf)) )"

lemma [simp]: "\<forall>pf. size (xs collect(pf)) = size (xs filter (\<lambda>p. pf isDefAt p))"
apply(induct_tac xs)
apply(auto)
done

lemma "size (xs collect(pf)) \<le> size xs"
apply(induct_tac xs)
apply(auto)
done

theorem [simp]: "\<forall>pf. xs collect(pf) =  (xs filter (\<lambda>p. pf isDefAt p)) map(\<lambda>p. pf apply p)"
apply(induct_tac xs)
apply(auto)
done





(* def collectFirst[B](pf: PartialFunction[A, B]): Option[B]
Finds the first element of the list for which the given partial function is defined, and applies the partial function to it.
pf: the partial function
returns: an option value containing pf applied to the first value for which it is defined, or None if none exists. *)
primrec collectFirst :: "'a List \<Rightarrow> (('a, 'b) PartialFunction) \<Rightarrow> 'b Option" (infix "collectFirst" 65) where
"      Nil collectFirst(_) = None" |
"(x :: xs) collectFirst(pf) = ( if pf isDefAt x then Some(pf apply x) else xs collectFirst(pf) )"

lemma "\<forall>pf. xs collectFirst(pf) = None \<longleftrightarrow> xs filter(\<lambda>p. pf isDefAt p) = Nil "
apply(induct_tac xs)
apply(auto)
done

lemma [simp]: "\<forall>pf. headOption(xs collect(pf)) = xs collectFirst(pf)"
apply(induct_tac xs)
apply(auto)
done






primrec getOption :: "'a List \<Rightarrow> nat \<Rightarrow> 'a Option" (infix "getOption" 65) where
"    Nil getOption(n) = None" |
"(x::xs) getOption(n) = (case n of 0 \<Rightarrow> Some x | Suc m \<Rightarrow> xs getOption(m))"

(* 
lemma [simp]: "\<lbrakk> xs isDefinedAt(n); n < size(xs) \<rbrakk> \<Longrightarrow> \<exists>y. xs getOption(n) = Some(y) \<and> xs contains(y)"
apply(auto)
done*)

(* lemma "\<forall>n. xs getOption(n) = None \<longleftrightarrow> \<not> (xs isDefinedAt(n))"
apply(induct_tac xs)
apply(auto)
done *)




primrec lift :: "'a List \<Rightarrow> (nat \<Rightarrow> 'a Option)" where
"lift Nil       = (\<lambda>n. None)" |
"lift (x :: xs) = (\<lambda>n. (case n of 0 \<Rightarrow> Some x | Suc m \<Rightarrow> (lift xs) m) )"

lemma "(lift xs) 0 = xs getOption(0)"
apply(case_tac xs)
apply(auto)
done

lemma  "(lift xs) (size(xs)) = xs getOption(size(xs))"
apply(induct_tac xs)
apply(auto)
done





primrec sum :: "int List => int" where
"sum(Nil)     = 0" |
"sum(x :: xs) = x + sum(xs)"

lemma [simp]: "\<forall>ys. sum(xs ::: ys) = sum(xs) + sum(ys)"
apply(induct_tac xs)
apply(auto)
done

lemma  "\<forall>ys. sum(xs ::: ys) = sum(ys ::: xs)"
apply(induct_tac xs)
apply(auto)
done





(* def distinct: List[A]
Builds a new list from this list without any duplicate elements.
returns: A new list which contains the first occurrence of every element of this list. *)
primrec distinct :: "'a List \<Rightarrow> 'a List" where
"distinct(Nil)   = Nil" |
"distinct(x::xs) = (if distinct(xs) contains(x) then distinct(xs) else x :: (distinct(xs)) )" 

lemma "size(distinct(xs)) \<le> size(xs)"
apply(induct_tac xs)
apply(auto)
done

theorem [simp]: "distinct(distinct(xs)) = distinct(xs)"
apply(induct_tac xs)
apply(auto)
done

lemma [simp]: "(distinct xs) contains(x) = xs contains(x)"
apply(induct_tac xs)
apply(auto)
done

lemma [simp]: "\<forall>x. distinct(x :: (distinct xs)) = distinct(x::xs)"
apply(induct_tac xs)
apply(auto)
done

lemma [simp]: "\<forall>ys. distinct(xs ::: (distinct ys)) = distinct(xs ::: ys)"
apply(induct_tac xs)
apply(auto)
done

(* lemma [simp]: "\<forall>xs. distinct( (distinct xs) ::: ys) = distinct(xs ::: ys)"
apply(induct_tac ys)
apply(auto)
done *)






primrec minBy_helper :: "'a List \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> Boolean) \<Rightarrow> 'a \<Rightarrow> 'a" where
"minBy_helper Nil ord m       = m " |
"minBy_helper (x :: xs) ord m = minBy_helper xs ord (if (ord x m) then x else m)"

primrec minBy :: "'a List \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> Boolean) \<Rightarrow> 'a Option" (infix "minBy" 65) where
"      Nil minBy(ord) = None" |
"(x :: xs) minBy(ord) = Some(minBy_helper (x :: xs) ord x)" 

lemma [simp]: "(xs minBy(ord) = None) = (xs = Nil)"
apply(induct_tac xs)
apply(auto)
done

lemma [simp]: "\<lbrakk> xs = y :: ys \<rbrakk> \<Longrightarrow> \<forall>ord. \<exists>x. xs minBy(ord) = Some(x)"
apply(auto)
done

lemma [simp]: "\<lbrakk> \<forall>ord a. ord a a \<rbrakk> \<Longrightarrow> \<forall>ord a. ord (minBy_helper xs ord a) a = True  "
apply(induct_tac xs)
apply(auto)
done

theorem "\<lbrakk> \<forall>ord a. ord a a \<rbrakk> \<Longrightarrow> \<forall>m ord. Some(m) = xs minBy(ord) \<longleftrightarrow> xs forall(\<lambda>x. ord m x)"
apply(induct_tac xs)
apply(auto)
done

theorem "\<lbrakk> \<forall>ord a. \<not>ord a a \<rbrakk> \<Longrightarrow> \<forall>m ord. Some(m) = xs minBy(ord) \<longleftrightarrow> xs forall(\<lambda>x. ord m x \<or> m=x) \<and> (xs count(\<lambda>x. m=x) = 1)"
apply(induct_tac xs)
apply(auto)
done





primrec maxBy_helper :: "'a List \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> Boolean) \<Rightarrow> 'a \<Rightarrow> 'a" where
"maxBy_helper Nil ord m       = m " |
"maxBy_helper (x :: xs) ord m = maxBy_helper xs ord (if (ord x m) then m else x)"

primrec maxBy :: "'a List \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> Boolean) \<Rightarrow> 'a Option" (infix "maxBy" 65) where
"      Nil maxBy(ord) = None" |
"(x :: xs) maxBy(ord) = Some(maxBy_helper (x :: xs) ord x)" 

lemma [simp]: "(xs maxBy(ord) = None) = (xs = Nil)"
apply(induct_tac xs)
apply(auto)
done

lemma [simp]: "\<lbrakk> xs = y :: ys \<rbrakk> \<Longrightarrow> \<forall>ord. \<exists>x. xs maxBy(ord) = Some(x)"
apply(auto)
done

lemma [simp]: "\<lbrakk> \<forall>ord a. ord a a \<rbrakk> \<Longrightarrow> \<forall>ord a. ord (maxBy_helper xs ord a) a = True  "
apply(induct_tac xs)
apply(auto)
done

theorem "\<lbrakk> \<forall>ord a. ord a a \<rbrakk> \<Longrightarrow> \<forall>m ord. Some(m) = xs maxBy(ord) \<longleftrightarrow> xs forall(\<lambda>x. ord m x)"
apply(induct_tac xs)
apply(auto)
done

theorem "\<lbrakk> \<forall>ord a. \<not>ord a a \<rbrakk> \<Longrightarrow> \<forall>m ord. Some(m) = xs maxBy(ord) \<longleftrightarrow> xs forall(\<lambda>x. ord m x \<or> m=x) \<and> (xs count(\<lambda>x. m=x) = 1)"
apply(induct_tac xs)
apply(auto)
done





primrec sortedBy :: "'a List \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> Boolean) \<Rightarrow> Boolean" (infix "sortedBy" 65) where
"      Nil sortedBy(ord) = True" |
"(x :: xs) sortedBy(ord) = (case xs of Nil \<Rightarrow> True | y :: ys \<Rightarrow> (ord x y \<and> xs sortedBy(ord)) )"

lemma [simp]: "\<lbrakk> \<forall>ord a. ord a a \<rbrakk> \<Longrightarrow> \<forall>ord x. (x :: xs) sortedBy(ord) \<longleftrightarrow> Some(x) = (x :: xs) minBy(ord) \<and> xs sortedBy(ord)"
apply(induct_tac xs)
apply(auto)
done

lemma [simp]: "\<lbrakk> \<forall>ord a. \<not>ord a a \<rbrakk> \<Longrightarrow> \<forall>ord x. (x :: xs) sortedBy(ord) \<longleftrightarrow> Some(x) = (x :: xs) minBy(ord) \<and> xs sortedBy(ord)"
apply(induct_tac xs)
apply(auto)
done





(* def andThen[C](k: (A) \<Rightarrow> C): PartialFunction[Int, C]
Composes this partial function with a transformation function that gets applied to results of this partial function.
C: the result type of the transformation function.
k: the transformation function
returns: a partial function with the same domain as this partial function, which maps arguments x to k(this(x)). *)
primrec andThen :: "'a List \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> ((nat, 'c) PartialFunction)" where
"andThen Nil k dummy = PartialFunction (\<lambda>n. False) (\<lambda>n. dummy)" |
"andThen (x::xs) k _ = PartialFunction (\<lambda>n. (x::xs) isDefinedAt(n)) (\<lambda>n. k (((x::xs) getOption(n)) get x ) )" 



end



