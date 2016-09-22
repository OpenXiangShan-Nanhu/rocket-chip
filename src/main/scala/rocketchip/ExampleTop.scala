// See LICENSE for license details.

package rocketchip

import Chisel._
import cde.{Parameters, Field}
import junctions._
import coreplex._
import rocketchip._

/** Example Top with Periphery */
class ExampleTop(q: Parameters) extends BaseTop(q)
    with PeripheryBootROM
    with PeripheryDebug
    with PeripheryExtInterrupts
    with PeripheryCoreplexLocalInterrupter
    with PeripheryMasterMem
    with PeripheryMasterMMIO
    with PeripherySlave {
  override lazy val module = Module(new ExampleTopModule(p, this, new ExampleTopBundle(p)))
}

class ExampleTopBundle(p: Parameters) extends BaseTopBundle(p)
    with PeripheryBootROMBundle
    with PeripheryDebugBundle
    with PeripheryExtInterruptsBundle
    with PeripheryCoreplexLocalInterrupterBundle
    with PeripheryMasterMemBundle
    with PeripheryMasterMMIOBundle
    with PeripherySlaveBundle

class ExampleTopModule[+L <: ExampleTop, +B <: ExampleTopBundle](p: Parameters, l: L, b: => B) extends BaseTopModule(p, l, b)
    with PeripheryBootROMModule
    with PeripheryDebugModule
    with PeripheryExtInterruptsModule
    with PeripheryCoreplexLocalInterrupterModule
    with PeripheryMasterMemModule
    with PeripheryMasterMMIOModule
    with PeripherySlaveModule
    with HardwiredResetVector

/** Example Top with TestRAM */
class ExampleTopWithTestRAM(q: Parameters) extends ExampleTop(q)
    with PeripheryTestRAM {
  override lazy val module = Module(new ExampleTopWithTestRAMModule(p, this, new ExampleTopWithTestRAMBundle(p)))
}

class ExampleTopWithTestRAMBundle(p: Parameters) extends ExampleTopBundle(p)
    with PeripheryTestRAMBundle

class ExampleTopWithTestRAMModule[+L <: ExampleTopWithTestRAM, +B <: ExampleTopWithTestRAMBundle](p: Parameters, l: L, b: => B) extends ExampleTopModule(p, l, b)
    with PeripheryTestRAMModule

/** Example Top with Multi Clock */
class ExampleMultiClockTop(q: Parameters) extends ExampleTop(q)
    with PeripheryTestRAM {
  override lazy val module = Module(new ExampleMultiClockTopModule(p, this, new ExampleMultiClockTopBundle(p)))
}

class ExampleMultiClockTopBundle(p: Parameters) extends ExampleTopBundle(p)

class ExampleMultiClockTopModule[+L <: ExampleMultiClockTop, +B <: ExampleMultiClockTopBundle](p: Parameters, l: L, b: => B) extends ExampleTopModule(p, l, b) {
  val multiClockCoreplexIO = coreplexIO.asInstanceOf[MultiClockCoreplexBundle]

  multiClockCoreplexIO.trcs foreach { trc =>
    trc.clock := clock
    trc.reset := reset
  }
}
