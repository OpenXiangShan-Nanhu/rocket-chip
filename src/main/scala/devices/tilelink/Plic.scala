// See LICENSE.SiFive for license details.

package freechips.rocketchip.devices.tilelink

import chisel3._
import chisel3.experimental._
import chisel3.util._

import org.chipsalliance.cde.config._
import org.chipsalliance.diplomacy.lazymodule._

import freechips.rocketchip.diplomacy.{AddressSet}
import freechips.rocketchip.resources.{Description, Resource, ResourceBinding, ResourceBindings, ResourceInt, SimpleDevice}
import freechips.rocketchip.interrupts.{IntNexusNode, IntSinkParameters, IntSinkPortParameters, IntSourceParameters, IntSourcePortParameters}
import freechips.rocketchip.regmapper.{RegField, RegFieldDesc, RegFieldRdAction, RegFieldWrType, RegReadFn, RegWriteFn}
import freechips.rocketchip.subsystem.{BaseSubsystem, CBUS, TLBusWrapperLocation}
import freechips.rocketchip.tilelink.{TLFragmenter, TLRegisterNode}
import freechips.rocketchip.util.{MuxT, property}

import scala.math.min

import freechips.rocketchip.util.UIntToAugmentedUInt
import freechips.rocketchip.util.SeqToAugmentedSeq

class GatewayPLICIO extends Bundle {
  val valid = Output(Bool())
  val ready = Input(Bool())
  val complete = Input(Bool())
}

class LevelGateway extends Module {
  val io = IO(new Bundle {
    val interrupt = Input(Bool())
    val plic = new GatewayPLICIO
  })

  val inFlight = RegInit(false.B)
  when (io.interrupt && io.plic.ready) { inFlight := true.B }
  when (io.plic.complete) { inFlight := false.B }
  io.plic.valid := io.interrupt && !inFlight
}

/** Tracks the in-service interrupt for a hart, used for secure interrupt claim/complete validation */
class IrqTrackEntry(nDevices: Int) extends Bundle {
  val irq_id     = UInt(log2Ceil(nDevices + 1).W)  // interrupt ID currently in service (0 = none)
  val req_sec    = Bool()                           // whether the in-service interrupt is secure
  val in_service = Bool()                           // whether an interrupt is currently being serviced
}

object PLICConsts
{
  def maxDevices = 1023
  def maxMaxHarts = 15872
  def priorityBase = 0x0
  def pendingBase = 0x1000
  def enableBase = 0x2000
  def hartBase = 0x200000

  def claimOffset = 4
  def priorityBytes = 4

  // Secure interrupt extension register bases
  def secSrcBase     = 0x1F4000   // security attribute per interrupt source (after enable region)
  def worldStateBase = 0x1F8000   // world state per hart (TEE=1 / REE=0)

  def enableOffset(i: Int) = i * ((maxDevices+7)/8)
  def hartOffset(i: Int) = i * 0x1000
  def enableBase(i: Int):Int = enableOffset(i) + enableBase
  def hartBase(i: Int):Int = hartOffset(i) + hartBase

  def size(maxHarts: Int): Int = {
    require(maxHarts > 0 && maxHarts <= maxMaxHarts, s"Must be: maxHarts=$maxHarts > 0 && maxHarts <= PLICConsts.maxMaxHarts=${PLICConsts.maxMaxHarts}")
    1 << log2Ceil(hartBase(maxHarts))
  }

  require(hartBase >= enableBase(maxMaxHarts))
}

case class PLICParams(baseAddress: BigInt = 0xC000000, maxPriorities: Int = 7, intStages: Int = 0, maxHarts: Int = PLICConsts.maxMaxHarts)
{
  require (maxPriorities >= 0)
  def address = AddressSet(baseAddress, PLICConsts.size(maxHarts)-1)
}

case object PLICKey extends Field[Option[PLICParams]](None)

case class PLICAttachParams(
  slaveWhere: TLBusWrapperLocation = CBUS
)

case object PLICAttachKey extends Field(PLICAttachParams())

/** Platform-Level Interrupt Controller */
class TLPLIC(params: PLICParams, beatBytes: Int)(implicit p: Parameters) extends LazyModule
{
  // plic0 => max devices 1023
  val device: SimpleDevice = new SimpleDevice("interrupt-controller", Seq("riscv,plic0")) {
    override val alwaysExtended = true
    override def describe(resources: ResourceBindings): Description = {
      val Description(name, mapping) = super.describe(resources)
      val extra = Map(
        "interrupt-controller" -> Nil,
        "riscv,ndev" -> Seq(ResourceInt(nDevices)),
        "riscv,max-priority" -> Seq(ResourceInt(nPriorities)),
        "#interrupt-cells" -> Seq(ResourceInt(1)))
      Description(name, mapping ++ extra)
    }
  }

  val node : TLRegisterNode = TLRegisterNode(
    address   = Seq(params.address),
    device    = device,
    beatBytes = beatBytes,
    undefZero = true,
    concurrency = 1) // limiting concurrency handles RAW hazards on claim registers

  val intnode: IntNexusNode = IntNexusNode(
    sourceFn = { _ => IntSourcePortParameters(Seq(IntSourceParameters(1, Seq(Resource(device, "int"))))) },
    sinkFn   = { _ => IntSinkPortParameters(Seq(IntSinkParameters())) },
    outputRequiresInput = false,
    inputRequiresOutput = false)

  /* Negotiated sizes */
  def nDevices: Int = intnode.edges.in.map(_.source.num).sum
  def minPriorities = min(params.maxPriorities, nDevices)
  def nPriorities = (1 << log2Ceil(minPriorities+1)) - 1 // round up to next 2^n-1
  def nHarts = intnode.edges.out.map(_.source.num).sum

  // Assign all the devices unique ranges
  lazy val sources = intnode.edges.in.map(_.source)
  lazy val flatSources = (sources zip sources.map(_.num).scanLeft(0)(_+_).init).map {
    case (s, o) => s.sources.map(z => z.copy(range = z.range.offset(o)))
  }.flatten

  ResourceBinding {
    flatSources.foreach { s => s.resources.foreach { r =>
      // +1 because interrupt 0 is reserved
      (s.range.start until s.range.end).foreach { i => r.bind(device, ResourceInt(i+1)) }
    } }
  }

  lazy val module = new Impl
  class Impl extends LazyModuleImp(this) {
    val (io_devices, edgesIn) = intnode.in.unzip
    val (io_harts, _) = intnode.out.unzip

    // Compact the interrupt vector the same way
    val interrupts = intnode.in.map { case (i, e) => i.take(e.source.num) }.flatten
    // This flattens the harts into an MSMSMSMSMS... or MMMMM.... sequence
    val harts = io_harts.flatten

    def getNInterrupts = interrupts.size

    println(s"Interrupt map (${nHarts} harts ${nDevices} interrupts):")
    flatSources.foreach { s =>
      // +1 because 0 is reserved, +1-1 because the range is half-open
      println(s"  [${s.range.start+1}, ${s.range.end}] => ${s.name}")
    }
    println("")

    require (nDevices == interrupts.size, s"Must be: nDevices=$nDevices == interrupts.size=${interrupts.size}")
    require (nHarts == harts.size, s"Must be: nHarts=$nHarts == harts.size=${harts.size}")

    require(nDevices <= PLICConsts.maxDevices, s"Must be: nDevices=$nDevices <= PLICConsts.maxDevices=${PLICConsts.maxDevices}")
    require(nHarts > 0 && nHarts <= params.maxHarts, s"Must be: nHarts=$nHarts > 0 && nHarts <= PLICParams.maxHarts=${params.maxHarts}")

    // For now, use LevelGateways for all TL2 interrupts
    val gateways = interrupts.map { case i =>
      val gateway = Module(new LevelGateway)
      gateway.io.interrupt := i
      gateway.io.plic
    }

    val prioBits = log2Ceil(nPriorities+1)
    val priority =
      if (nPriorities > 0) RegInit(VecInit(Seq.fill(nDevices)(0.U(prioBits.W))))
      else WireDefault(VecInit.fill(nDevices max 1)(1.U))
    val threshold =
      if (nPriorities > 0) RegInit(VecInit(Seq.fill(nHarts)(0.U(prioBits.W))))
      else WireDefault(VecInit.fill(nHarts)(0.U))
    val pending = RegInit(VecInit.fill(nDevices max 1){false.B})

    /* Construct the enable registers, chunked into 8-bit segments to reduce verilog size */
    val firstEnable = nDevices min 7
    val fullEnables = (nDevices - firstEnable) / 8
    val tailEnable  = nDevices - firstEnable - 8*fullEnables
    def enableRegs = (RegInit(0.U(firstEnable.W)) +:
                      Seq.fill(fullEnables) { RegInit(0.U(8.W)) }) ++
                     (if (tailEnable > 0) Some(RegInit(0.U(tailEnable.W))) else None)
    val enables = Seq.fill(nHarts) { enableRegs }
    val enableVec = VecInit(enables.map(x => Cat(x.reverse)))
    val enableVec0 = VecInit(enableVec.map(x => Cat(x, 0.U(1.W))))

    // --- Secure interrupt extension registers ---
    // sec_src: 1-bit security attribute per interrupt source (0=Non-secure, 1=Secure)
    val sec_src = RegInit(VecInit(Seq.fill(nDevices max 1)(false.B)))
    // world_state: 1-bit world state per hart (0=REE, 1=TEE), synced from hart CSR
    val world_state = RegInit(VecInit(Seq.fill(nHarts)(false.B)))
    // irq_track: tracks the in-service interrupt for claim/complete validation
    val irq_track = RegInit(VecInit(Seq.fill(nHarts)(0.U.asTypeOf(new IrqTrackEntry(nDevices)))))

    val maxDevs = Reg(Vec(nHarts, UInt(log2Ceil(nDevices+1).W)))
    val pendingUInt = Cat(pending.reverse)
    if(nDevices > 0) {
      val sec_src_uint = Cat(sec_src.reverse)   // nDevices bits, MSB-first like pendingUInt
      val sec_busy = VecInit(irq_track.map(t => t.in_service && t.req_sec))

      for (hart <- 0 until nHarts) {
        val fanin = Module(new PLICFanIn(nDevices, prioBits))
        fanin.io.prio := priority
        // Security filtering:
        //   Secure interrupts  (sec_src=1): always visible
        //   Non-secure interrupts (sec_src=0): blocked when hart is in TEE (world_state=1) AND servicing a secure interrupt (sec_busy=1)
        val blocked = ~sec_src_uint & Fill(nDevices, world_state(hart) & sec_busy(hart))
        fanin.io.ip := enableVec(hart) & pendingUInt & ~blocked
        maxDevs(hart) := fanin.io.dev
        harts(hart) := ShiftRegister(RegNext(fanin.io.max) > threshold(hart), params.intStages)
      }
    }

    // Priority registers are 32-bit aligned so treat each as its own group.
    // Otherwise, the off-by-one nature of the priority registers gets confusing.
    require(PLICConsts.priorityBytes == 4,
      s"PLIC Priority register descriptions assume 32-bits per priority, not ${PLICConsts.priorityBytes}")

    def priorityRegDesc(i: Int) =
      RegFieldDesc(
        name      = s"priority_$i",
        desc      = s"Acting priority of interrupt source $i",
        group     = Some(s"priority_${i}"),
        groupDesc = Some(s"Acting priority of interrupt source ${i}"),
        reset     = if (nPriorities > 0) None else Some(1))

    def pendingRegDesc(i: Int) =
      RegFieldDesc(
        name      = s"pending_$i",
        desc      = s"Set to 1 if interrupt source $i is pending, regardless of its enable or priority setting.",
        group     = Some("pending"),
        groupDesc = Some("Pending Bit Array. 1 Bit for each interrupt source."),
        volatile = true)

    def enableRegDesc(i: Int, j: Int, wide: Int) = {
      val low = if (j == 0) 1 else j*8
      val high = low + wide - 1
      RegFieldDesc(
        name      = s"enables_${j}",
        desc      = s"Targets ${low}-${high}. Set bits to 1 if interrupt should be enabled.",
        group     = Some(s"enables_${i}"),
        groupDesc = Some(s"Enable bits for each interrupt source for target $i. 1 bit for each interrupt source."))
    }

    def secSrcRegDesc(i: Int) =
      RegFieldDesc(
        name      = s"sec_src_$i",
        desc      = s"Security attribute of interrupt source $i. 0=Non-secure, 1=Secure.",
        group     = Some("sec_src"),
        groupDesc = Some("Security attribute for each interrupt source. 1 bit per source."))

    def worldStateRegDesc(i: Int) =
      RegFieldDesc(
        name      = s"world_state_$i",
        desc      = s"Current world state of hart $i. 0=REE, 1=TEE.",
        group     = Some("world_state"),
        groupDesc = Some("World state for each hart. 1 bit per hart."))

    def priorityRegField(x: UInt, i: Int) =
      if (nPriorities > 0) {
        RegField(prioBits, x, priorityRegDesc(i))
      } else {
        RegField.r(prioBits, x, priorityRegDesc(i))
      }

    val priorityRegFields = priority.zipWithIndex.map { case (p, i) =>
      PLICConsts.priorityBase+PLICConsts.priorityBytes*(i+1) ->
      Seq(priorityRegField(p, i+1)) }
    val pendingRegFields = Seq(PLICConsts.pendingBase ->
      (RegField(1) +: pending.zipWithIndex.map { case (b, i) => RegField.r(1, b, pendingRegDesc(i+1))}))
    val enableRegFields = enables.zipWithIndex.map { case (e, i) =>
      PLICConsts.enableBase(i) -> (RegField(1) +: e.zipWithIndex.map { case (x, j) =>
        RegField(x.getWidth, x, enableRegDesc(i, j, x.getWidth)) }) }

    val secSrcRegFields = Seq(PLICConsts.secSrcBase ->
      (RegField(1) +: sec_src.zipWithIndex.map { case (s, i) =>
        RegField(1, s, secSrcRegDesc(i+1)) }))

    val worldStateRegFields = Seq(PLICConsts.worldStateBase ->
      (RegField(1) +: world_state.zipWithIndex.map { case (w, i) =>
        RegField(1, w, worldStateRegDesc(i)) }))

    // When a hart reads a claim/complete register, then the
    // device which is currently its highest priority is no longer pending.
    // This code exploits the fact that, practically, only one claim/complete
    // register can be read at a time. We check for this because if the address map
    // were to change, it may no longer be true.
    // Note: PLIC doesn't care which hart reads the register.
    val claimer = Wire(Vec(nHarts, Bool()))
    assert((claimer.asUInt & (claimer.asUInt - 1.U)) === 0.U) // One-Hot
    val claiming = Seq.tabulate(nHarts){i => Mux(claimer(i), maxDevs(i), 0.U)}.reduceLeft(_|_)
    val claimedDevs = VecInit(UIntToOH(claiming, nDevices+1).asBools)

    ((pending zip gateways) zip claimedDevs.tail) foreach { case ((p, g), c) =>
      g.ready := !p
      when (c || g.valid) { p := !c }
    }

    // Latch irq_track on successful claim: record which interrupt was claimed and its security attribute
    for (i <- 0 until nHarts) {
      when (claimer(i) && maxDevs(i) =/= 0.U) {
        irq_track(i).irq_id     := maxDevs(i)
        irq_track(i).req_sec    := sec_src(maxDevs(i) - 1.U)
        irq_track(i).in_service := true.B
      }
    }

    // When a hart writes a claim/complete register, then
    // the written device (as long as it is actually enabled for that
    // hart) is marked complete.
    // This code exploits the fact that, practically, only one claim/complete register
    // can be written at a time. We check for this because if the address map
    // were to change, it may no longer be true.
    // Note -- PLIC doesn't care which hart writes the register.
    val completer = Wire(Vec(nHarts, Bool()))
    assert((completer.asUInt & (completer.asUInt - 1.U)) === 0.U) // One-Hot
    val completerDev = Wire(UInt(log2Up(nDevices + 1).W))
    val completedDevs = Mux(completer.reduce(_ || _), UIntToOH(completerDev, nDevices+1), 0.U)
    (gateways zip completedDevs.asBools.tail) foreach { case (g, c) =>
       g.complete := c
    }

    def thresholdRegDesc(i: Int) =
      RegFieldDesc(
        name = s"threshold_$i",
        desc = s"Interrupt & claim threshold for target $i. Maximum value is ${nPriorities}.",
        reset    = if (nPriorities > 0) None else Some(1))

    def thresholdRegField(x: UInt, i: Int) =
      if (nPriorities > 0) {
        RegField(prioBits, x, thresholdRegDesc(i))
      } else {
        RegField.r(prioBits, x, thresholdRegDesc(i))
      }

    val hartRegFields = Seq.tabulate(nHarts) { i =>
      PLICConsts.hartBase(i) -> Seq(
        thresholdRegField(threshold(i), i),
        RegField(32-prioBits),
        RegField(32,
          RegReadFn { valid =>
            claimer(i) := valid
            (true.B, maxDevs(i))
          },
          RegWriteFn { (valid, data) =>
            assert(Mux(valid, completerDev === data.extract(log2Ceil(nDevices+1)-1, 0), true.B),
                   "completerDev should be consistent for all harts")
            completerDev := data.extract(log2Ceil(nDevices+1)-1, 0)
            // Validate complete against irq_track: must have an in-service interrupt with matching ID
            val track_ok = irq_track(i).in_service && (completerDev === irq_track(i).irq_id)
            completer(i) := valid && enableVec0(i)(completerDev) && track_ok
            when (valid && enableVec0(i)(completerDev) && track_ok) {
              irq_track(i).in_service := false.B
            }
            true.B
          },
          Some(RegFieldDesc(s"claim_complete_$i",
            s"Claim/Complete register for Target $i. Reading this register returns the claimed interrupt number and makes it no longer pending." +
            s"Writing the interrupt number back completes the interrupt.",
            reset = None,
            wrType = Some(RegFieldWrType.MODIFY),
            rdAction = Some(RegFieldRdAction.MODIFY),
            volatile = true))
        )
      )
    }

    node.regmap((priorityRegFields ++ pendingRegFields ++ enableRegFields ++ secSrcRegFields ++ worldStateRegFields ++ hartRegFields):_*)

    if (nDevices >= 2) {
      val claimed = claimer(0) && maxDevs(0) > 0.U
      val completed = completer(0)
      property.cover(claimed && RegEnable(claimed, false.B, claimed || completed), "TWO_CLAIMS", "two claims with no intervening complete")
      property.cover(completed && RegEnable(completed, false.B, claimed || completed), "TWO_COMPLETES", "two completes with no intervening claim")

      val ep = enables(0).asUInt & pending.asUInt
      val ep2 = RegNext(ep)
      val diff = ep & ~ep2
      property.cover((diff & (diff - 1.U)) =/= 0.U, "TWO_INTS_PENDING", "two enabled interrupts became pending on same cycle")

      if (nPriorities > 0)
        ccover(maxDevs(0) > (1.U << priority(0).getWidth) && maxDevs(0) <= Cat(1.U, threshold(0)),
               "THRESHOLD", "interrupt pending but less than threshold")
    }

    def ccover(cond: Bool, label: String, desc: String)(implicit sourceInfo: SourceInfo) =
      property.cover(cond, s"PLIC_$label", "Interrupts;;" + desc)
  }
}

class PLICFanIn(nDevices: Int, prioBits: Int) extends Module {
  val io = IO(new Bundle {
    val prio = Flipped(Vec(nDevices, UInt(prioBits.W)))
    val ip   = Flipped(UInt(nDevices.W))
    val dev  = UInt(log2Ceil(nDevices+1).W)
    val max  = UInt(prioBits.W)
  })

  def findMax(x: Seq[UInt]): (UInt, UInt) = {
    if (x.length > 1) {
      val half = 1 << (log2Ceil(x.length) - 1)
      val left = findMax(x take half)
      val right = findMax(x drop half)
      MuxT(left._1 >= right._1, left, (right._1, half.U | right._2))
    } else (x.head, 0.U)
  }

  val effectivePriority = (1.U << prioBits) +: (io.ip.asBools zip io.prio).map { case (p, x) => Cat(p, x) }
  val (maxPri, maxDev) = findMax(effectivePriority)
  io.max := maxPri // strips the always-constant high '1' bit
  io.dev := maxDev
}

/** Trait that will connect a PLIC to a subsystem */
trait CanHavePeripheryPLIC { this: BaseSubsystem =>
  val (plicOpt, plicDomainOpt) = p(PLICKey).map { params =>
    val tlbus = locateTLBusWrapper(p(PLICAttachKey).slaveWhere)
    val plicDomainWrapper = tlbus.generateSynchronousDomain("PLIC").suggestName("plic_domain")

    val plic = plicDomainWrapper { LazyModule(new TLPLIC(params, tlbus.beatBytes)) }
    plicDomainWrapper { plic.node := tlbus.coupleTo("plic") { TLFragmenter(tlbus, Some("PLIC")) := _ } }
    plicDomainWrapper { plic.intnode :=* ibus.toPLIC }

    (plic, plicDomainWrapper)
  }.unzip
}
