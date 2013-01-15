package rocket

import Chisel._
import Node._
import Constants._
import uncore._
import Util._

case class RocketConfiguration(lnConf: LogicalNetworkConfiguration, co: CoherencePolicyWithUncached,
                               icache: ICacheConfig, dcache: DCacheConfig,
                               fpu: Boolean, vec: Boolean,
                               fastLoadWord: Boolean = true,
                               fastLoadByte: Boolean = false,
                               fastMulDiv: Boolean = true)
{
  val dcacheReqTagBits = 9 // enforce compliance with require()
  val xprlen = 64
  val nxpr = 32
  val nxprbits = log2Up(nxpr)
  val rvc = false
  if (fastLoadByte) require(fastLoadWord)
}

class Tile(resetSignal: Bool = null)(confIn: RocketConfiguration) extends Component(resetSignal) with ClientCoherenceAgent
{
  val memPorts = 2 + confIn.vec
  implicit val dcConf = confIn.dcache.copy(reqtagbits = confIn.dcacheReqTagBits + log2Up(memPorts), databits = confIn.xprlen)
  implicit val lnConf = confIn.lnConf
  implicit val conf = confIn.copy(dcache = dcConf)

  val io = new Bundle {
    val tilelink = new TileLinkIO
    val host = new HTIFIO(lnConf.nTiles)
  }

  val core      = new Core
  val icache    = new Frontend()(confIn.icache, lnConf)
  val dcache    = new HellaCache

  val arbiter   = new MemArbiter(memPorts)
  arbiter.io.requestor(0) <> dcache.io.mem
  arbiter.io.requestor(1) <> icache.io.mem

  io.tilelink.xact_init <> arbiter.io.mem.xact_init
  io.tilelink.xact_init_data <> dcache.io.mem.xact_init_data
  arbiter.io.mem.xact_abort <> io.tilelink.xact_abort
  arbiter.io.mem.xact_rep <> io.tilelink.xact_rep
  io.tilelink.xact_finish <> arbiter.io.mem.xact_finish
  dcache.io.mem.probe_req <> io.tilelink.probe_req
  io.tilelink.probe_rep <> dcache.io.mem.probe_rep
  io.tilelink.probe_rep_data <> dcache.io.mem.probe_rep_data

  if (conf.vec) {
    val vicache = new Frontend()(ICacheConfig(128, 1, conf.co), lnConf) // 128 sets x 1 ways (8KB)
    arbiter.io.requestor(2) <> vicache.io.mem
    core.io.vimem <> vicache.io.cpu
  }

  core.io.host <> io.host
  core.io.imem <> icache.io.cpu
  core.io.dmem <> dcache.io.cpu
}
