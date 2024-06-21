// See LICENSE.SiFive for license details.

package freechips.rocketchip.util

import chisel3._
import chisel3.util.log2Ceil
import scala.collection.mutable.{HashMap}

@deprecated("moved to standalone rocketutils library", "rocketchip 2.0.0")
case class ROMConfig(name: String, depth: Int, width: Int)

@deprecated("moved to standalone rocketutils library", "rocketchip 2.0.0")
class BlackBoxedROM(c: ROMConfig) extends BlackBox {
  val io = IO(new Bundle {
    val clock = Input(Clock())
    val address = Input(UInt(log2Ceil(c.depth).W))
    val oe = Input(Bool())
    val me = Input(Bool())
    val q = Output(UInt(c.width.W))
  })

  override def desiredName: String = c.name
}

@deprecated("moved to standalone rocketutils library", "rocketchip 2.0.0")
object ROMGenerator {
  private var finalized = false
  private val roms = HashMap[BlackBoxedROM, ROMConfig]()
  def apply(c: ROMConfig): BlackBoxedROM = {
    require(!finalized)
    val m = Module(new BlackBoxedROM(c))
    roms(m) = c
    m
  }
  def lookup(m: BlackBoxedROM): ROMConfig = {
    finalized = true
    roms(m)
  }
}
