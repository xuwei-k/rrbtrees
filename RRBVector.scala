/**
 *  Copyright © 2011 Phil Bagwell and Tiark Rompf. This is a prototype implementation, use at your own risk.
 */

package rrbvector

import scala.collection._
import scala.collection.generic._
import scala.collection.immutable.{IndexedSeq,_}
import scala.collection.mutable.Builder
import java.lang.Math.{max => mmax, min => mmin}

object Vector extends SeqFactory[Vector] {
  @inline implicit def canBuildFrom[A]: CanBuildFrom[Coll, A, Vector[A]] =
    ReusableCBF.asInstanceOf[CanBuildFrom[Coll, A, Vector[A]]]
  def newBuilder[A]: Builder[A, Vector[A]] = new VectorBuilder[A]
  private[rrbvector] val NIL = new Vector[Nothing](null, 0, 0)
  @inline override def empty[A]: Vector[A] = NIL
  
  def apply() = NIL

  def apply[A](elem: A): Vector[A] = {
    val data = new Array[AnyRef](1)
    data(0) = elem.asInstanceOf[AnyRef]
    new Vector[A](data, 1, 32)
  }

}

final class VectorBuilder[A]() extends Builder[A,Vector[A]] {

  var acc = Vector.empty[A]

  def += (elem: A): this.type = {
    acc = acc ++ Vector(elem)
    this
  }

  override def ++=(xs: TraversableOnce[A]): this.type = xs match {
    case v: Vector[A] => acc = acc ++ v; this
    case _ => super.++=(xs)
  }

  def result: Vector[A] = acc
  
  def clear(): Unit = {
    acc = Vector.empty[A]
  }
}

final class Vector[+A] private
extends IndexedSeq[A]
   with GenericTraversableTemplate[A, Vector]
   with IndexedSeqLike[A, Vector[A]] {

  private final val Width = 32
  private final val Invar = 1
  private final val Extras = 2

  type TreeNode = AnyRef

  type Ara = Array[AnyRef]
  type GTa = Array[AnyRef]

  var root: TreeNode = null
  var vSize = 0
  var vHw = 0

  private def this(r: AnyRef, s: Int, hw: Int) = {
    this()
    root = r
    vSize = s
    vHw = hw
  }

  override def companion: GenericCompanion[Vector] = Vector

  def length = vSize

  def apply(index: Int): A = {
    indexAt(index).asInstanceOf[A]
  }

  @inline override def updated[B >: A, That](index: Int, elem: B)(implicit bf: CanBuildFrom[Vector[A], B, That]): That = {
    updateAt(index, elem).asInstanceOf[That]
  }

  override def take(n: Int): Vector[A] = {
    if (n <= 0)
      Vector.empty
    else if (n < vSize)
      sliceR(n)
    else
      this
  }

  override def drop(n: Int): Vector[A] = {
    if (n <= 0)
      this
    else if (n < vSize)
      sliceL(n)
    else
      Vector.empty
  }

  override def takeRight(n: Int): Vector[A] = {
    if (n <= 0)
      Vector.empty
    else if (vSize - n > 0)
      sliceL(vSize - n)
    else
      this
  }

  override def dropRight(n: Int): Vector[A] = {
    if (n <= 0)
      this
    else if (vSize - n > 0)
      sliceR(vSize - n)
    else
      Vector.empty
  }

  override /*IterableLike*/ def head: A = {
    if (isEmpty) throw new UnsupportedOperationException("empty.head")
    apply(0)
  }

  override /*TraversableLike*/ def tail: Vector[A] = {
    if (isEmpty) throw new UnsupportedOperationException("empty.tail")
    drop(1)
  }

  override /*TraversableLike*/ def last: A = {
    if (isEmpty) throw new UnsupportedOperationException("empty.last")
    apply(length - 1)
  }

  override /*TraversableLike*/ def init: Vector[A] = {
    if (isEmpty) throw new UnsupportedOperationException("empty.init")
    dropRight(1)
  }

  override /*IterableLike*/ def slice(from: Int, until: Int): Vector[A] =
    take(until).drop(from)

  override /*IterableLike*/ def splitAt(n: Int): (Vector[A], Vector[A]) = (take(n), drop(n))

  def ++[U >: A](b: Vector[U]): Vector[U] = {
    val a = this
    if (a.vSize == 0) b
    else if (b.vSize == 0) a
    else {
      val nvec = new Vector[U]
      val tnca = nvec.concatSubTree(a.root, a.vHw, b.root, b.vHw, true)
      nvec.root = if ((a.vHw == Width) && (b.vHw == Width) && (a.vSize + b.vSize <= Width))
        tnca.asInstanceOf[Ara](1)
      else
        setSizes(tnca, mmax(a.vHw, b.vHw))
      nvec.vSize = a.vSize + b.vSize
      nvec.vHw = findhw(nvec.root)
      nvec
    }
  }

  override def ++[B >: A, That](that: GenTraversableOnce[B])(implicit bf: CanBuildFrom[Vector[A], B, That]): That = {
    that match {
      case v: Vector[B] => this.++[B](v).asInstanceOf[That]
      case _ => super.++(that)
    }
  }

  @inline override def +:[B >: A, That](elem: B)(implicit bf: CanBuildFrom[Vector[A], B, That]): That = {
    (Vector(elem) ++ this).asInstanceOf[That]
  }

  @inline override def :+[B >: A, That](elem: B)(implicit bf: CanBuildFrom[Vector[A], B, That]): That = {
    (this ++ Vector(elem)).asInstanceOf[That]
  }

  override def patch[B >: A, That](from: Int, patch: GenSeq[B], replaced: Int)(implicit bf: CanBuildFrom[Vector[A], B, That]): That = {
    val insert = patch.nonEmpty
    val delete = replaced != 0
    if (insert || delete) {
      val prefix = take(from)
      val rest = drop(from + replaced)
      ((prefix ++ patch).asInstanceOf[Vector[B]] ++ rest).asInstanceOf[That]
    } else this.asInstanceOf[That]
  }

  private def concatSubTree(til: TreeNode, hwl: Int, tir: TreeNode, hwr: Int, isTop: Boolean): Ara = {
    if (hwl > hwr) {
      val tnla = til.asInstanceOf[Ara]
      val tnca = concatSubTree(tnla(tnla.length - 1), hwl / Width, tir, hwr, false)
      rebalance(tnla, tnca, null, hwl, isTop)
    } else if (hwl < hwr) {
      val tnra = tir.asInstanceOf[Ara]
      val tnca = concatSubTree(til, hwl, tnra(1), hwr / Width, false)
      rebalance(null, tnca, tnra, hwr, isTop)
    } else {
      if (hwl == Width) {
        val gnla = til.asInstanceOf[GTa]
        val gnra = tir.asInstanceOf[GTa]
        val lenl = gtaLength(gnla)
        val lenr = gtaLength(gnra)
        if (isTop && (lenr + lenl <= Width)) {
          araNewAbove(gtaNewJoin(gnla, gnra))
        } else {
          araNewAbove(til, tir)
        }
      } else {
        val tnla = til.asInstanceOf[Ara]
        val tnra = tir.asInstanceOf[Ara]
        val tnca = concatSubTree(tnla(tnla.length - 1), hwl / Width, tnra(1), hwr / Width, false)
        rebalance(tnla, tnca, tnra, hwl, isTop)
      }
    }
  }

  private def gtaLength(a: GTa) = a.length

  private def gtaNewJoin(gnla: GTa, gnra: GTa): GTa = {
    val lenl = gnla.length
    val lenr = gnra.length
    val gal = new GTa(lenr + lenl)
    System.arraycopy(gnla, 0, gal, 0, lenl)
    System.arraycopy(gnra, 0, gal, lenl, lenr)
    gal
  }

  private def araNewAbove(gal: TreeNode): Ara = {
    val na = new Ara(2)
    na(0) = null
    na(1) = gal
    na
  }

  private def araNewAbove(til: TreeNode, tir: TreeNode): Ara = {
    val na = new Ara(3)
    na(0) = null
    na(1) = til
    na(2) = tir
    na
  }

  private def araNewJoin(al: Ara, ac: Ara, ar: Ara): Ara = {
    val lenl = if (al != null) al.length - 2 else 0
    val lenc = if (ac != null) ac.length - 1 else 0
    val lenr = if (ar != null) ar.length - 2 else 0
    var allx = 0
    val all = new Ara(lenl + lenc + lenr)
    if (lenl > 0) {
      System.arraycopy(al, 1, all, 0, lenl)
      allx += lenl
    }
    System.arraycopy(ac, 1, all, allx, lenc)
    allx += lenc
    if (lenr > 0) {
      System.arraycopy(ar, 2, all, allx, lenr)
    }
    all
  }

  private def araNewCopy(nall: Ara, start: Int, len: Int) = {
    val na = new Ara(len + 1)
    System.arraycopy(nall, start + 1, na, 1, len)
    na
  }

  private def rebalance(al: Ara, ac: Ara, ar: Ara, hw: Int, IsTop: Boolean): Ara = {
    val all = araNewJoin(al, ac, ar)
    val szs = shuffle(all, hw)
    val slen = this.vSize
    val nall = copyAcross(all, szs, slen, hw)

    if (slen <= Width) {
      if (!IsTop) {
        araNewAbove(setSizes(nall, hw))
      } else {
        nall
      }
    } else {
      val nal = araNewCopy(nall, 0, Width)
      val nar = araNewCopy(nall, Width, slen - Width)
      araNewAbove(setSizes(nal, hw), setSizes(nar, hw))
    }
  }

  private def shuffle(all: Ara, hw: Int): Array[Int] = {
    val alen = all.length
    val szs = new Array[Int](alen)

    var tcnt = 0
    var i = 0
    while (i < alen) {
      val sz = sizeSlot(all(i), hw / Width)
      szs(i) = sz
      tcnt += sz
      i += 1
    }
    val effslt = tcnt / Width + 1
    val MinWidth = Width - Invar

    var nalen = alen
    while (nalen > effslt + Extras) {
      var ix = 0
      while (szs(ix) > MinWidth) ix += 1

      var el = szs(ix)
      do {
        val msz = mmin(el + szs(ix + 1), Width)
        szs(ix) = msz
        el = el + szs(ix + 1) - msz

        ix += 1
      } while (el > 0)

      while (ix < nalen - 1) {
        szs(ix) = szs(ix + 1)
        ix += 1
      }
      nalen -= 1
    }

    this.vSize = nalen
    szs
  }

  private def copyAcross(all: Ara, szs: Array[Int], slen: Int, hw: Int): Ara = {

    val nall = new Ara(slen + 1)
    var ix = 0
    var offset = 0

    val isOneAboveBottom = hw == Width * Width
    if (isOneAboveBottom) {
      var i = 0
      while (i < slen) {
        val nsize = szs(i)
        val ge = all(ix).asInstanceOf[GTa]
        val asIs = (offset == 0) && (nsize == ge.length)

        if (asIs) {
          ix += 1; nall(i + 1) = ge
        } else {
          var fillcnt = 0
          var offs = offset
          var nix = ix
          var rta: GTa = null

          var ga: GTa = null
          while ((fillcnt < nsize) && (nix < all.length)) {
            val gaa = all(nix).asInstanceOf[GTa]
            ga = if (fillcnt == 0) new GTa(nsize) else ga
            val lena = gaa.length
            if (nsize - fillcnt >= lena - offs) {
              System.arraycopy(gaa, offs, ga, fillcnt, lena - offs)
              fillcnt += lena - offs
              nix += 1
              offs = 0
            } else {
              System.arraycopy(gaa, offs, ga, fillcnt, nsize - fillcnt)
              offs += nsize - fillcnt
              fillcnt = nsize
            }
            rta = ga
          }

          ix = nix
          offset = offs
          nall(i + 1) = rta
        }
        i += 1
      }

    } else {
      var i = 0
      while (i < slen) {
        val nsize = szs(i)
        val ae = all(ix).asInstanceOf[Ara]
        val asIs = (offset == 0) && (nsize == ae.length - 1)

        if (asIs) {
          ix += 1; nall(i + 1) = ae
        } else {
          var fillcnt = 0
          var offs = offset
          var nix = ix
          var rta: Ara = null

          var aa: Ara = null
          while ((fillcnt < nsize) && (nix < all.length)) {
            val aaa = all(nix).asInstanceOf[Ara]
            aa = if (fillcnt == 0) new Ara(nsize + 1) else aa
            val lena = aaa.length - 1
            if (nsize - fillcnt >= lena - offs) {
              System.arraycopy(aaa, offs + 1, aa, fillcnt + 1, lena - offs)
              nix += 1
              fillcnt += lena - offs
              offs = 0
            } else {
              System.arraycopy(aaa, offs + 1, aa, fillcnt + 1, nsize - fillcnt)
              offs += nsize - fillcnt
              fillcnt = nsize
            }
            rta = aa
          }

          rta = setSizes(rta, hw / Width)
          ix = nix
          offset = offs
          nall(i + 1) = rta
        }
        i += 1
      }
    }
    nall
  }

  private def findhw(n: TreeNode): Int = n match {
    case a: Array[AnyRef] if a.length > 0 && ((a(0) eq null) || a(0).isInstanceOf[Array[Int]]) => findhw(a(1)) * Width
    case _ => Width
  }

  private def setSizes(a: Ara, hw: Int) = {
    var sigma = 0
    val lena = a.length - 1
    val szs = new Array[Int](lena)
    var i = 0
    while (i < lena) {
      sigma += sizeSubTrie(a(i + 1), hw / Width)
      szs(i) = sigma
      i += 1
    }
    a(0) = szs
    a
  }

  private def sizeSlot(a: TreeNode, hw: Int) = {
    if (a == null) {
      throw new IllegalArgumentException("sizeSlot NULL")
      0
    }
    else {
      if (hw > Width)
        a.asInstanceOf[Ara].length - 1
      else
        a.asInstanceOf[GTa].length
    }
  }

  private def sztohw(sz: Int) = {
    var hw = Width
    while (sz > hw) hw *= Width
    hw
  }

  private def sizeSubTrie(tn: TreeNode, hw: Int): Int = {
    if (hw > Width) {
      val in = tn.asInstanceOf[Ara]
      if (in(0) == null) {
        val len = in.length
        val sltsz = hw / Width
        sltsz * (len - 2) + sizeSubTrie(in(len - 1), sltsz)
      } else {
        val sn = in(0).asInstanceOf[Array[Int]]
        sn(sn.length - 1)
      }
    } else {
      val vn = tn.asInstanceOf[GTa]
      vn.length
    }
  }

  private def sliceR(right: Int): Vector[A] = {
    if ((right < vSize) && (right >= 0) && (root != null)) {
      val nv = new Vector[A]
      val n = nv.rSliceDown2(root, right - 1, vHw, false)
      nv.vSize = right
      nv.root = n
      nv
    } else this
  }

  private def rSliceDown2(n: AnyRef, right: Int, hw: Int, hasLeft: Boolean): AnyRef = {
    val sw = hw / Width
    var is = right / sw
    if (hw > Width) {
      val in = n.asInstanceOf[Ara]
      val len = in.length - 1
      if (in(0) == null) {
        val rhn = rSliceDown2(in(is + 1), right - is * sw, hw / Width, (is != 0) || hasLeft)
        val hwr = this.vHw
        if (is == 0) {
          if (hasLeft) {
            val rcnodes = new Array[AnyRef](2)
            rcnodes(1) = rhn
            rcnodes(0) = null
            this.vHw = hw
            rcnodes
          } else {
            this.vHw = hwr
            rhn
          }
        } else {
          val cnodes = new Array[AnyRef](is + 2)
          System.arraycopy(in, 1, cnodes, 1, is)
          cnodes(is + 1) = rhn
          cnodes(0) = null
          this.vHw = hw
          cnodes
        }
      } else {
        val szs = in(0).asInstanceOf[Array[Int]]
        var ix = right

        while (szs(is) <= ix) is += 1
        ix = ix - (if (is == 0) 0 else szs(is - 1))
        val nn = in.asInstanceOf[Ara](is + 1)

        val rhn = rSliceDown2(nn, ix, hw / Width, (is != 0) || hasLeft)
        val hwr = this.vHw
        if (is == 0) {
          if (hasLeft) {
            val rcnodes = new Array[AnyRef](2)
            val rsizes = new Array[Int](1)
            rcnodes(1) = rhn
            rsizes(0) = right + 1
            rcnodes(0) = rsizes
            this.vHw = hw
            rcnodes
          } else {
            this.vHw = hwr
            rhn
          }
        } else {
          val cnodes = new Array[AnyRef](is + 2)
          val sizes = new Array[Int](is + 1)
          System.arraycopy(in, 1, cnodes, 1, is)
          System.arraycopy(szs, 0, sizes, 0, is)
          cnodes(0) = sizes
          sizes(is) = right + 1
          cnodes(is + 1) = rhn
          this.vHw = hw
          cnodes
        }
      }
    } else {
      val vn = n.asInstanceOf[GTa]
      val lvals = new GTa(is + 1)
      System.arraycopy(vn, 0, lvals, 0, is + 1)
      this.vHw = hw
      lvals
    }
  }

  private def sliceL(left: Int): Vector[A] = {
    if (left >= vSize) new Vector[A]
    else if ((left > 0) && (root != null)) {
      val nv = new Vector[A]
      val n = nv.lSliceDown2(root, left, vHw, false)
      nv.vSize = vSize - left
      nv.root = n
      nv
    } else this
  }

  private def lSliceDown2(n: AnyRef, left: Int, hw: Int, hasRight: Boolean): AnyRef = {
    val sw = hw / Width
    var is = left / sw
    if (hw > Width) {
      val in = n.asInstanceOf[Ara]
      val len = in.length - 1
      var inl = null: AnyRef
      var ist = 0
      var ix = 0
      if (in(0) != null) {
        val szs = in(0).asInstanceOf[Array[Int]]
        ix = left
        ist = is
        while (szs(ist) <= ix) ist += 1
        ix = ix - (if (ist == 0) 0 else szs(ist - 1))
        inl = in.asInstanceOf[Ara](ist + 1)
      } else {
        inl = in(is + 1)
        ist = is
        ix = left - is * sw
      }

      val lastslt = len - 1
      val lhn = lSliceDown2(inl, ix, hw / Width, (ist != lastslt) || hasRight)
      val hwr = this.vHw
      if (ist == lastslt) {
        if (hasRight) {
          val rcnodes = new Array[AnyRef](2)
          rcnodes(1) = lhn
          rcnodes(0) = null
          this.vHw = hw
          rcnodes
        } else {
          this.vHw = hwr
          lhn
        }
      } else {
        val cnodes = new Array[AnyRef](len - ist + 1)
        System.arraycopy(in, ist + 2, cnodes, 2, len - ist - 1)
        val szs = in(0).asInstanceOf[Array[Int]]
        val rsizes = new Array[Int](len - ist)
        if (in(0) != null) {
          var i = 0
          while (i < (len - ist)) {
            rsizes(i) = szs(ist + i) - left
            i += 1
          }
        } else {
          var i = 0
          while (i < (len - ist)) {
            rsizes(i) = sw * (ist + 1 + i)
            i += 1
          }
        }
        cnodes(0) = rsizes
        cnodes(1) = lhn
        this.vHw = hw
        cnodes
      }
    } else {
      val vn = n.asInstanceOf[GTa]
      val lenv = vn.length
      var lvals = new GTa(lenv - is)
      System.arraycopy(vn, is, lvals, 0, lenv - is)
      this.vHw = hw
      lvals
    }
  }

  private def updateAt[B >: A](index: Int, value: B): Vector[B] = {
    if ((index < 0) || (index >= vSize) || (root == null)) this
    else {
      val nvec = new Vector[B]
      nvec.root = updateTrie(root, index, value.asInstanceOf[AnyRef], vHw)
      nvec.vSize = vSize
      nvec.vHw = vHw
      nvec
    }
  }

  private def updateTrie(tn: TreeNode, ix: Int, value: AnyRef /* A */ , hw: Int): AnyRef = {
    val sw = hw / Width
    var is = ix / sw
    if (hw > Width) {
      val in = tn.asInstanceOf[Ara]
      val subn = if (in(0) == null) updateTrie(in(is), ix - is * sw, value, hw / Width)
      else {
        val szs = in(0).asInstanceOf[Array[Int]]
        while (szs(is) <= ix) is += 1
        val nix = ix - (if (is == 0) 0 else szs(is - 1))
        updateTrie(in(1 + is), nix, value, hw / Width)
      }
      val len = in.length - 1
      val cnodes = new Ara(len + 1)
      System.arraycopy(in, 0, cnodes, 0, len + 1)
      cnodes(is + 1) = subn
      cnodes
    } else {
      val vn = tn.asInstanceOf[GTa]
      val len = vn.length
      val lvals = new GTa(len)
      System.arraycopy(vn, 0, lvals, 0, len)
      lvals(is) = value
      lvals
    }
  }

  final val S5 = 1 << 5
  final val S10 = 1 << 10
  final val S15 = 1 << 15
  final val S20 = 1 << 20
  final val S25 = 1 << 25
  final val S30 = 1 << 30

  private def indexAt(index: Int): AnyRef = {
    var ix = index
    def sized(ia: AnyRef, sp: Int): AnyRef = {
      val szs = ia.asInstanceOf[Ara](0).asInstanceOf[Array[Int]]
      var is = ix >> sp
      while (szs(is) <= ix) is += 1
      ix = ix - (if (is == 0) 0 else szs(is - 1))
      ia.asInstanceOf[Ara](is + 1)
    }
    if ((ix < 0) || (ix >= vSize)) throw new IndexOutOfBoundsException(ix.toString)
    else {
      vHw match {
        case S5 => root.asInstanceOf[GTa](ix)
        case S10 =>
          val n1 = if (root.asInstanceOf[Ara](0) == null) root.asInstanceOf[Ara]((ix >> 5) + 1) else sized(root, 5)
          n1.asInstanceOf[GTa](ix & 31)
        case S15 =>
          val n1 = if (root.asInstanceOf[Ara](0) == null) root.asInstanceOf[Ara]((ix >> 10) + 1) else sized(root, 10)
          val n2 = if (n1.asInstanceOf[Ara](0) == null) n1.asInstanceOf[Ara](((ix >> 5) & 31) + 1) else sized(n1, 5)
          n2.asInstanceOf[GTa](ix & 31)
        case S20 =>
          val n1 = if (root.asInstanceOf[Ara](0) == null) root.asInstanceOf[Ara]((ix >> 15) + 1) else sized(root, 15)
          val n2 = if (n1.asInstanceOf[Ara](0) == null) n1.asInstanceOf[Ara](((ix >> 10) & 31) + 1) else sized(n1, 10)
          val n3 = if (n2.asInstanceOf[Ara](0) == null) n2.asInstanceOf[Ara](((ix >> 5) & 31) + 1) else sized(n2, 5)
          n3.asInstanceOf[GTa](ix & 31)
        case S25 =>
          val n1 = if (root.asInstanceOf[Ara](0) == null) root.asInstanceOf[Ara]((ix >> 20) + 1) else sized(root, 20)
          val n2 = if (n1.asInstanceOf[Ara](0) == null) n1.asInstanceOf[Ara](((ix >> 15) & 31) + 1) else sized(n1, 15)
          val n3 = if (n2.asInstanceOf[Ara](0) == null) n2.asInstanceOf[Ara](((ix >> 10) & 31) + 1) else sized(n2, 10)
          val n4 = if (n3.asInstanceOf[Ara](0) == null) n3.asInstanceOf[Ara](((ix >> 5) & 31) + 1) else sized(n3, 5)
          n4.asInstanceOf[GTa](ix & 31)
        case S30 =>
          val n1 = if (root.asInstanceOf[Ara](0) == null) root.asInstanceOf[Ara]((ix >> 25) + 1) else sized(root, 25)
          val n2 = if (n1.asInstanceOf[Ara](0) == null) n1.asInstanceOf[Ara](((ix >> 20) & 31) + 1) else sized(n1, 20)
          val n3 = if (n2.asInstanceOf[Ara](0) == null) n2.asInstanceOf[Ara](((ix >> 15) & 31) + 1) else sized(n2, 15)
          val n4 = if (n3.asInstanceOf[Ara](0) == null) n3.asInstanceOf[Ara](((ix >> 10) & 31) + 1) else sized(n3, 10)
          val n5 = if (n4.asInstanceOf[Ara](0) == null) n4.asInstanceOf[Ara](((ix >> 5) & 31) + 1) else sized(n4, 5)
          n5.asInstanceOf[GTa](ix & 31)
        case _ => throw new IllegalArgumentException()
      }
    }
  }
}

