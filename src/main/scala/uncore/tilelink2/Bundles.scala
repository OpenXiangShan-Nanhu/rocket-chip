// See LICENSE for license details.

package uncore.tilelink2

import Chisel._

abstract class GenericParameterizedBundle[T <: Object](val params: T) extends Bundle
{
  override def cloneType = {
    try {
      this.getClass.getConstructors.head.newInstance(params).asInstanceOf[this.type]
    } catch {
      case e: java.lang.IllegalArgumentException =>
        throwException("Unable to use GenericParameterizedBundle.cloneType on " +
                       this.getClass + ", probably because " + this.getClass +
                       "() takes more than one argument.  Consider overriding " +
                       "cloneType() on " + this.getClass, e)
    }
  }
}

abstract class TLBundleBase(params: TLBundleParameters) extends GenericParameterizedBundle(params)

// common combos in lazy policy:
//   Put + Acquire
//   Release + AccessAck

object TLMessages 
{
  //                                  A    B    C    D    E
  val PutFullData    = UInt(0) //     .    .                   => AccessAck
  val PutPartialData = UInt(1) //     .    .                   => AccessAck
  val ArithmeticData = UInt(2) //     .    .                   => AccessAckData
  val LogicalData    = UInt(3) //     .    .                   => AccessAckData
  val Get            = UInt(4) //     .    .                   => AccessAckData
  val Hint           = UInt(5) //     .    .                   => HintAck
  val Acquire        = UInt(6) //     .                        => Grant[Data]
  val Probe          = UInt(6) //          .                   => ProbeAck[Data]
  val AccessAck      = UInt(0) //               .    .
  val AccessAckData  = UInt(1) //               .    .
  val HintAck        = UInt(2) //               .    .
//val PutThroughData = UInt(3) //               .              // future extension ?
  val ProbeAck       = UInt(4) //               .
  val ProbeAckData   = UInt(5) //               .
  val Release        = UInt(6) //               .              => ReleaseAck
  val ReleaseData    = UInt(7) //               .              => ReleaseAck
  val Grant          = UInt(4) //                    .         => GrantAck
  val GrantData      = UInt(5) //                    .         => GrantAck
  val ReleaseAck     = UInt(6) //                    .
  val GrantAck       = UInt(0) //                         .
 
  def isA(x: UInt) = x <= Acquire
  def isB(x: UInt) = x <= Probe
  def isC(x: UInt) = x <= ReleaseData
  def isD(x: UInt) = x <= ReleaseAck
}

object TLPermissions
{
  // Cap types (Grant = new permissions, Probe = permisions <= target)
  val toT = UInt(0)
  val toB = UInt(1)
  val toN = UInt(2)
  def isCap(x: UInt) = x <= toN

  // Grow types (Acquire = permissions >= target)
  val NtoB = UInt(0)
  val NtoT = UInt(1)
  val BtoT = UInt(2)
  def isGrow(x: UInt) = x <= BtoT

  // Shrink types (ProbeAck, Release)
  val TtoB = UInt(0)
  val TtoN = UInt(1)
  val BtoN = UInt(2)
  def isShrink(x: UInt) = x <= BtoN

  // Report types (ProbeAck)
  val TtoT = UInt(3)
  val BtoB = UInt(4)
  val NtoN = UInt(5)
  def isReport(x: UInt) = x <= NtoN
}

object TLAtomics
{
  // Arithmetic types
  val MIN  = UInt(0)
  val MAX  = UInt(1)
  val MINU = UInt(2)
  val MAXU = UInt(3)
  val ADD  = UInt(4)
  def isArithmetic(x: UInt) = x <= ADD

  // Logical types
  val XOR  = UInt(0)
  val OR   = UInt(1)
  val AND  = UInt(2)
  val SWAP = UInt(3)
  def isLogical(x: UInt) = x <= SWAP
}

sealed trait TLChannel extends TLBundleBase
sealed trait TLDataChannel extends TLChannel
sealed trait TLAddrChannel extends TLDataChannel

final class TLBundleA(params: TLBundleParameters)
  extends TLBundleBase(params) with TLAddrChannel
{
  // fixed fields during multibeat:
  val opcode  = UInt(width = 3)
  val param   = UInt(width = 3) // amo_opcode || perms || hint
  val size    = UInt(width = params.sizeBits)
  val source  = UInt(width = params.sourceBits) // from
  val addr_hi = UInt(width = params.addrHiBits) // to
  // variable fields during multibeat:
  val mask    = UInt(width = params.dataBits/8)
  val data    = UInt(width = params.dataBits)
}

final class TLBundleB(params: TLBundleParameters)
  extends TLBundleBase(params) with TLAddrChannel
{
  // fixed fields during multibeat:
  val opcode  = UInt(width = 3)
  val param   = UInt(width = 3)
  val size    = UInt(width = params.sizeBits)
  val source  = UInt(width = params.sourceBits) // to
  val addr_hi = UInt(width = params.addrHiBits) // from
  // variable fields during multibeat:
  val mask    = UInt(width = params.dataBits/8)
  val data    = UInt(width = params.dataBits)
}

final class TLBundleC(params: TLBundleParameters)
  extends TLBundleBase(params) with TLAddrChannel
{
  // fixed fields during multibeat:
  val opcode  = UInt(width = 3)
  val param   = UInt(width = 3)
  val size    = UInt(width = params.sizeBits)
  val source  = UInt(width = params.sourceBits) // from
  val addr_hi = UInt(width = params.addrHiBits) // to
  val addr_lo = UInt(width = params.addrLoBits) // instead of mask
  // variable fields during multibeat:
  val data    = UInt(width = params.dataBits)
  val error   = Bool() // AccessAck[Data]
}

final class TLBundleD(params: TLBundleParameters)
  extends TLBundleBase(params) with TLDataChannel
{
  // fixed fields during multibeat:
  val opcode  = UInt(width = 3)
  val param   = UInt(width = 2)
  val size    = UInt(width = params.sizeBits)
  val source  = UInt(width = params.sourceBits) // to
  val sink    = UInt(width = params.sinkBits)   // from
  val addr_lo = UInt(width = params.addrLoBits) // instead of mask
  // variable fields during multibeat:
  val data    = UInt(width = params.dataBits)
  val error   = Bool() // AccessAck[Data], Grant[Data]
}

final class TLBundleE(params: TLBundleParameters)
  extends TLBundleBase(params) with TLChannel
{
  val sink = UInt(width = params.sourceBits) // to
}

class TLBundle(params: TLBundleParameters) extends TLBundleBase(params)
{
  val a = Decoupled(new TLBundleA(params))
  val b = Decoupled(new TLBundleB(params)).flip
  val c = Decoupled(new TLBundleC(params))
  val d = Decoupled(new TLBundleD(params)).flip
  val e = Decoupled(new TLBundleE(params))
}

object TLBundle
{
  def apply(params: TLBundleParameters) = new TLBundle(params)
}
