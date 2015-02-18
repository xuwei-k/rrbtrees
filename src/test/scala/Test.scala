package rrbvector

import scalaz._
import std.AllInstances._
import scalaz.scalacheck.ScalazProperties._
import scalaz.scalacheck.ScalazArbitrary._
import org.scalacheck.{Arbitrary, Prop, Gen}
import org.scalacheck.Prop.forAll
import syntax.bifunctor._, syntax.foldable._

object Test extends SpecLite {

  checkAll(equal.laws[rrbvector.Vector[Int]])
  checkAll(monoid.laws[rrbvector.Vector[Int]])
  checkAll(monadPlus.strongLaws[rrbvector.Vector])
  checkAll(traverse.laws[rrbvector.Vector])
//  checkAll(zip.laws[rrbvector.Vector])
//  checkAll(align.laws[rrbvector.Vector])
  checkAll(isEmpty.laws[rrbvector.Vector])
//  checkAll(cobind.laws[rrbvector.Vector])
//  checkAll(order.laws[rrbvector.Vector[Int]])

  implicit def vectorArb[A: Arbitrary]: Arbitrary[rrbvector.Vector[A]] =
    Arbitrary(implicitly[Arbitrary[List[A]]].arbitrary.map(xs => rrbvector.Vector(xs: _*)))

  implicit val intBooleanArb: Arbitrary[Int => Boolean] = {
    val intGen = implicitly[Arbitrary[Int]].arbitrary
    Arbitrary(Gen.oneOf(
      Gen.const((_: Int) => true),
      Gen.const((_: Int) => false),
      Gen.choose(2, 5).map(n => (a: Int) => a % n == 0),
      Gen.choose(2, 5).map(n => (a: Int) => a % n != 0),
      intGen.map(n => (_: Int) > n),
      intGen.map(n => (_: Int) < n)
    ))
  }

  "intercalate empty list is flatten" ! forAll { (a: rrbvector.Vector[rrbvector.Vector[Int]]) =>
    a.intercalate(rrbvector.Vector[Int]()) must_===(a.flatten)
  }

  "foldl is foldLeft" ! forAll {(rnge: rrbvector.Vector[rrbvector.Vector[Int]]) =>
    val F = Foldable[List]
    rnge.foldLeft(rrbvector.Vector[Int]())(_++_) must_=== F.foldLeft(rnge.toList, rrbvector.Vector[Int]())(_++_)
  }

  "foldr is foldRight" ! forAll {(rnge: rrbvector.Vector[rrbvector.Vector[Int]]) =>
    val F = Foldable[List]
    rnge.foldRight(rrbvector.Vector[Int]())(_++_) must_=== F.foldRight(rnge.toList, rrbvector.Vector[Int]())(_++_)
  }

  "foldLeft1Opt" ! forAll { ns: rrbvector.Vector[List[Int]] =>
    ns.foldLeft1Opt(_ ::: _) must_=== ns.toList.reduceLeftOption(_ ::: _)
  }

  "foldRight1Opt" ! forAll { ns: rrbvector.Vector[List[Int]] =>
    ns.foldRight1Opt(_ ::: _) must_=== ns.toList.reduceRightOption(_ ::: _)
  }

  "foldMap1Opt" ! forAll { ns: rrbvector.Vector[List[Int]] =>
    ns.foldMap1Opt(identity) must_=== ns.toList.reduceLeftOption(_ ::: _)
  }

  "++" ! forAll { (ns: rrbvector.Vector[Int], ms: rrbvector.Vector[Int]) =>
    (ns ++ ms).toList must_=== ns.toList ++ ms.toList
  }

  "++:" ! forAll { (ns: rrbvector.Vector[Int], ms: rrbvector.Vector[Int]) =>
    (ns ++: ms).toList must_=== ns.toList ++: ms.toList
  }

  "+:" ! forAll { (n: Int, ns: rrbvector.Vector[Int]) =>
    (n +: ns).toList must_=== n +: ns.toList
  }

  "/:" ! forAll { (ns: rrbvector.Vector[Int], s: String, f: (String, Int) => String) =>
    (s /: ns)(f) == (s /: ns.toList)(f)
  }

  ":+" ! forAll { (n: Int, ns: rrbvector.Vector[Int]) =>
    (ns :+ n).toList must_=== ns.toList :+ n
  }

  "+:" ! forAll { (n: Int, ns: rrbvector.Vector[Int]) =>
    (n +: ns).toList must_=== n +: ns.toList
  }

  ":\\" ! forAll { (ns: rrbvector.Vector[Int], s: String, f: (Int, String) => String) =>
    (ns :\ s)(f) == (ns.toList :\ s)(f)
  }

  "++" ! forAll { (ns: rrbvector.Vector[Int], ms: rrbvector.Vector[Int]) =>
    (ns ++ ms).toList must_=== ns.toList ++ ms.toList
  }

  "collect" ! forAll { (ns: rrbvector.Vector[Int]) =>
    val pf: PartialFunction[Int, Int] = { case n if n % 2 == 0 => n + 1 }
    ns.collect(pf).toList must_=== ns.toList.collect(pf)
  }

  "collectFirst" ! forAll { (ns: rrbvector.Vector[Int]) =>
    val pf: PartialFunction[Int, Int] = { case n if n % 2 == 0 => n + 1 }
    ns.collectFirst(pf) must_=== ns.toList.collectFirst(pf)
  }

  "concat" ! forAll { (ns: rrbvector.Vector[Int], ms: rrbvector.Vector[Int]) =>
    (ns ++ ms).toList must_=== ns.toList ++ ms.toList
  }

  "containsSlice" ! forAll { (ns: rrbvector.Vector[Int], ms: rrbvector.Vector[Int]) =>
    ns.containsSlice(ms) must_=== ns.toList.containsSlice(ms.toList)
  }

  "count" ! forAll { (ns: rrbvector.Vector[Int], p: Int => Boolean) =>
    ns.count(p) must_=== ns.toList.count(p)
  }

  "distinct" ! forAll { xs: rrbvector.Vector[Int] =>
    xs.distinct.toList must_=== xs.toList.distinct
  }

  "drop" ! forAll { (ns: rrbvector.Vector[Int], n: Int) =>
    ns.drop(n).toList must_=== ns.toList.drop(n)
  }

  "dropRight" ! forAll { (ns: rrbvector.Vector[Int], n: Int) =>
    ns.dropRight(n).toList must_=== ns.toList.dropRight(n)
  }

  "dropWhile" ! forAll { (ns: rrbvector.Vector[Int], p: Int => Boolean) =>
    ns.dropWhile(p).toList must_=== ns.toList.dropWhile(p)
  }

  "endsWith" ! forAll { (ns: rrbvector.Vector[Int], ms: rrbvector.Vector[Int]) =>
    ns.endsWith(ms) must_=== ns.toList.endsWith(ms.toList)
  }

  "fill" ! forAll { (a: Byte, b: Int) =>
    rrbvector.Vector.fill(a)(b).toList must_=== List.fill(a)(b)
  }

  "filter" ! forAll { (ns: rrbvector.Vector[Int], p: Int => Boolean) =>
    ns.filter(p).toList must_=== ns.toList.filter(p)
  }

  "filterNot" ! forAll { (ns: rrbvector.Vector[Int], f: Int => Boolean) =>
    ns.filterNot(f).toList must_=== ns.toList.filterNot(f)
  }

  "find" ! forAll { (ns: rrbvector.Vector[Int], f: Int => Boolean) =>
    ns.find(f) must_=== ns.toList.find(f)
  }

  "headOption" ! forAll { ns: rrbvector.Vector[Int] =>
    ns.headOption must_=== ns.toList.headOption
  }

  "index" ! forAll { (ns: rrbvector.Vector[Int], n: Int) =>
    ns.index(n) must_=== ns.toList.lift(n)
  }

  "indexOf" ! forAll { (ns: rrbvector.Vector[Int], n: Int) =>
    ns.indexOf(n) must_=== ns.toList.indexOf(n)
  }

  "indexOfSlice" ! forAll { (ns: rrbvector.Vector[Int], ms: rrbvector.Vector[Int]) =>
    ns.indexOfSlice(ms) must_=== ns.toList.indexOfSlice(ms.toList)
  }

  "indexWhere" ! forAll { (ns: rrbvector.Vector[Int], f: Int => Boolean) =>
    ns.indexWhere(f) must_=== ns.toList.indexWhere(f)
  }

  "initOption" ! forAll { ns: rrbvector.Vector[Int] =>
    if(ns.nonEmpty){
      ns.init.toList must_=== ns.toList.init
    }
  }

  "inits" ! forAll { ns: rrbvector.Vector[Int] =>
    ns.inits.map(_.toList).toList must_=== ns.toList.inits.toList
  }

  "lastIndexOf" ! forAll { (ns: rrbvector.Vector[Int], n: Int) =>
    ns.lastIndexOf(n) must_=== ns.toList.lastIndexOf(n)
  }

  "lastIndexOfSlice" ! forAll { (ns: rrbvector.Vector[Int], ms: rrbvector.Vector[Int]) =>
    ns.lastIndexOfSlice(ms) must_=== ns.toList.lastIndexOfSlice(ms.toList)
  }

  "lastIndexWhere" ! forAll { (ns: rrbvector.Vector[Int], f: Int => Boolean) =>
    ns.lastIndexWhere(f) must_=== ns.toList.lastIndexWhere(f)
  }

  "lastOption" ! forAll { ns: rrbvector.Vector[Int] =>
    ns.lastOption must_=== ns.toList.lastOption
  }

  "length" ! forAll { ns: rrbvector.Vector[Int] =>
    ns.length must_=== ns.toList.length
  }

  // map is tested by functor laws

  "nonEmpty" ! forAll { ns: rrbvector.Vector[Int] =>
    ns.nonEmpty must_=== ns.toList.nonEmpty
  }

  "padTo" ! forAll { (ns: rrbvector.Vector[Int], n: Int) =>
    ns.padTo(100, n).toList must_=== ns.toList.padTo(100, n)
  }

  "patch" ! forAll { (ns: rrbvector.Vector[Int], a: Int, ms: rrbvector.Vector[Int], b: Int) =>
    ns.patch(a, ms, b).toList must_=== ns.toList.patch(a, ms.toList, b)
  }

  "prefixLength" ! forAll { (ns: rrbvector.Vector[Int], f: Int => Boolean) =>
    ns.prefixLength(f) must_=== ns.toList.prefixLength(f)
  }

  "reduceLeftOption" ! forAll { (ns: rrbvector.Vector[Int], f: (Int, Int) => Int) =>
    ns.reduceLeftOption(f) must_=== (try Some(ns.toList.reduceLeft(f)) catch { case e:Exception => None })
  }

  "reduceRightOption" ! forAll { (ns: rrbvector.Vector[Int], f: (Int, Int) => Int) =>
    ns.reduceRightOption(f) must_=== (try Some(ns.toList.reduceRight(f)) catch { case e:Exception => None })
  }

  "prefixLength" ! forAll { (ns: rrbvector.Vector[Int], f: Int => Boolean) =>
    ns.prefixLength(f) must_=== ns.toList.prefixLength(f)
  }

  "reverse" ! forAll { ns: rrbvector.Vector[Int] =>
    ns.reverse.toList must_=== ns.toList.reverse
  }

  "reverseMap" ! forAll { (ns: rrbvector.Vector[Int], f: Int => Int) =>
    ns.reverseMap(f).toList must_=== ns.toList.reverseMap(f)
  }

  "scanLeft" ! forAll { (ss: rrbvector.Vector[String], f: (Int, String) => Int) =>
    ss.scanLeft(0)(f).toList must_=== ss.toList.scanLeft(0)(f)
    ss.scanLeft("z")(_ + _).toList must_=== ss.toList.scanLeft("z")(_ + _)
    ss.scanLeft(rrbvector.Vector.empty[String])(_ :+ _).toList must_=== ss.toList.scanLeft(rrbvector.Vector.empty[String])(_ :+ _)
  }

  "scanRight" ! forAll { (ss: rrbvector.Vector[String], f: (String, Int) => Int)  =>
    ss.scanRight(0)(f).toList must_=== ss.toList.scanRight(0)(f)
    ss.scanRight("z")(_ + _).toList must_=== ss.toList.scanRight("z")(_ + _)
    ss.scanRight(rrbvector.Vector.empty[String])(_ +: _).toList must_=== ss.toList.scanRight(rrbvector.Vector.empty[String])(_ +: _)
  }

  "slice" ! forAll { (ns: rrbvector.Vector[Int], a: Int, b: Int) =>
    ns.slice(a, b).toList must_=== ns.toList.slice(a, b)
  }

  "sortBy" ! forAll { (ss: rrbvector.Vector[String], f: String => Int) =>
    ss.sortBy(f).toList must_=== ss.toList.sortBy(f)
  }

  "sorted" ! forAll { (ss: rrbvector.Vector[String]) =>
    ss.sorted.toList must_=== ss.toList.sorted
  }

  "span" ! forAll { (ns: rrbvector.Vector[Int], f: Int => Boolean) =>
    ns.span(f).umap(_.toList) must_=== ns.toList.span(f)
  }

  "splitAt" ! forAll { (ns: rrbvector.Vector[Int], n: Int) =>
    ns.splitAt(n).umap(_.toList) must_=== ns.toList.splitAt(n)
  }

  "startsWith" ! forAll { (ns: rrbvector.Vector[Int], ms: rrbvector.Vector[Int]) =>
    ns.startsWith(ms) must_=== ns.toList.startsWith(ms.toList)
  }

  "tails" ! forAll { ns: rrbvector.Vector[Int] =>
    ns.tails.map(_.toList).toList must_=== ns.toList.tails.toList
  }

  "take" ! forAll { (ns: rrbvector.Vector[Int], n: Byte) =>
    ns.take(n).toList must_=== ns.toList.take(n)
  }

  "takeRight" ! forAll { (ns: rrbvector.Vector[Int], n: Byte) =>
    ns.takeRight(n).toList must_=== ns.toList.takeRight(n)
  }

  "takeWhile" ! forAll { (ns: rrbvector.Vector[Int], f: Int => Boolean) =>
    ns.takeWhile(f).toList must_=== ns.toList.takeWhile(f)
  }

  "toEphemeralStream" ! forAll { ns: List[Int] =>
    rrbvector.Vector(ns: _*).toEphemeralStream.toList must_=== EphemeralStream(ns: _*).toList
  }

  "toList" ! forAll { ns: List[Int] =>
    rrbvector.Vector(ns: _*).toList must_=== ns
  }

  "toMap" ! forAll { ps: List[(String, Int)] =>
    rrbvector.Vector(ps: _*).toMap must_=== Map(ps: _*)
  }

  "toStream" ! forAll { ns: List[Int] =>
    rrbvector.Vector(ns: _*).toStream must_=== ns.toStream
  }

  "toVector" ! forAll { ns: scala.Vector[Int] =>
    rrbvector.Vector(ns: _*).toVector must_=== ns
  }

  "updated" ! forAll { (ns: rrbvector.Vector[Int], i: Int, n: Int) =>
    if (i < 0 || i >= ns.length) {
      ns.updated(i, n) must_=== ns
    } else {
      ns.updated(i, n).toList must_=== ns.toList.updated(i, n)
    }
  }

  "unzip" ! forAll { (ns: rrbvector.Vector[(Int, String)]) =>
    ns.unzip.bimap(_.toList, _.toList) must_=== ns.toList.unzip
  }

  "zipWithIndex" ! forAll { ns: rrbvector.Vector[Int] =>
    ns.zipWithIndex.toList must_=== ns.toList.zipWithIndex
  }

}
