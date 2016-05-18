package junctions

import Chisel._
import cde.{Parameters, Field}

trait HastiConstants
{
  // Values for htrans
  val SZ_HTRANS     = 2
  val HTRANS_IDLE   = UInt(0, SZ_HTRANS) // No transfer requested, not in a burst
  val HTRANS_BUSY   = UInt(1, SZ_HTRANS) // No transfer requested, in a burst
  val HTRANS_NONSEQ = UInt(2, SZ_HTRANS) // First (potentially only) request in a burst
  val HTRANS_SEQ    = UInt(3, SZ_HTRANS) // Following requests in a burst

  // Values for hburst
  val SZ_HBURST     = 3
  val HBURST_SINGLE = UInt(0, SZ_HBURST) // Single access (no burst)
  val HBURST_INCR   = UInt(1, SZ_HBURST) // Incrementing burst of arbitrary length, not crossing 1KB
  val HBURST_WRAP4  = UInt(2, SZ_HBURST) // 4-beat wrapping burst
  val HBURST_INCR4  = UInt(3, SZ_HBURST) // 4-beat incrementing burst
  val HBURST_WRAP8  = UInt(4, SZ_HBURST) // 8-beat wrapping burst
  val HBURST_INCR8  = UInt(5, SZ_HBURST) // 8-beat incrementing burst
  val HBURST_WRAP16 = UInt(6, SZ_HBURST) // 16-beat wrapping burst
  val HBURST_INCR16 = UInt(7, SZ_HBURST) // 16-beat incrementing burst

  // Values for hresp
  val SZ_HRESP      = 1
  val HRESP_OKAY    = UInt(0, SZ_HRESP)
  val HRESP_ERROR   = UInt(1, SZ_HRESP)

  // Values for hsize are identical to TileLink MT_SZ
  // ie: 8*2^SZ_HSIZE bit transfers
  val SZ_HSIZE = 3
  
  // Values for hprot (a bitmask)
  val SZ_HPROT = 4
  def HPROT_DATA       = UInt("b0001") // Data access or Opcode fetch
  def HPROT_PRIVILEGED = UInt("b0010") // Privileged or User access
  def HPROT_BUFFERABLE = UInt("b0100") // Bufferable or non-bufferable
  def HPROT_CACHEABLE  = UInt("b1000") // Cacheable or non-cacheable

  def dgate(valid: Bool, b: UInt) = Fill(b.getWidth, valid) & b
}

case class HastiParameters(dataBits: Int, addrBits: Int)
case object HastiId extends Field[String]
case class HastiKey(id: String) extends Field[HastiParameters]

trait HasHastiParameters {
  implicit val p: Parameters
  val hastiParams = p(HastiKey(p(HastiId)))
  val hastiAddrBits = hastiParams.addrBits
  val hastiDataBits = hastiParams.dataBits
}

abstract class HastiModule(implicit val p: Parameters) extends Module
  with HasHastiParameters
abstract class HastiBundle(implicit val p: Parameters) extends ParameterizedBundle()(p)
  with HasHastiParameters

class HastiMasterIO(implicit p: Parameters) extends HastiBundle()(p) {
  val haddr     = UInt(OUTPUT, hastiAddrBits)
  val hwrite    = Bool(OUTPUT)
  val hsize     = UInt(OUTPUT, SZ_HSIZE)
  val hburst    = UInt(OUTPUT, SZ_HBURST)
  val hprot     = UInt(OUTPUT, SZ_HPROT)
  val htrans    = UInt(OUTPUT, SZ_HTRANS)
  val hmastlock = Bool(OUTPUT)

  val hwdata = Bits(OUTPUT, hastiDataBits)
  val hrdata = Bits(INPUT, hastiDataBits)

  val hready = Bool(INPUT)
  val hresp  = UInt(INPUT, SZ_HRESP)
}

class HastiSlaveIO(implicit p: Parameters) extends HastiBundle()(p) {
  val haddr     = UInt(INPUT, hastiAddrBits)
  val hwrite    = Bool(INPUT)
  val hsize     = UInt(INPUT, SZ_HSIZE)
  val hburst    = UInt(INPUT, SZ_HBURST)
  val hprot     = UInt(INPUT, SZ_HPROT)
  val htrans    = UInt(INPUT, SZ_HTRANS)
  val hmastlock = Bool(INPUT)

  val hwdata = Bits(INPUT, hastiDataBits)
  val hrdata = Bits(OUTPUT, hastiDataBits)

  val hsel      = Bool(INPUT)
  val hreadyin  = Bool(INPUT)
  val hreadyout = Bool(OUTPUT)
  val hresp     = UInt(OUTPUT, SZ_HRESP)
}

class HastiBus(amap: Seq[UInt=>Bool])(implicit p: Parameters) extends HastiModule()(p) {
  val io = new Bundle {
    val master = new HastiMasterIO().flip
    val slaves = Vec(amap.size, new HastiSlaveIO).flip
  }

  // skid buffer
  val skb_valid = Reg(init = Bool(false))
  val skb_haddr = Reg(UInt(width = hastiAddrBits))
  val skb_hwrite = Reg(Bool())
  val skb_hsize = Reg(UInt(width = SZ_HSIZE))
  val skb_hburst = Reg(UInt(width = SZ_HBURST))
  val skb_hprot = Reg(UInt(width = SZ_HPROT))
  val skb_htrans = Reg(UInt(width = SZ_HTRANS))
  val skb_hmastlock = Reg(Bool())
  val skb_hwdata = Reg(UInt(width = hastiDataBits))

  val master_haddr = Mux(skb_valid, skb_haddr, io.master.haddr)
  val master_hwrite = Mux(skb_valid, skb_hwrite, io.master.hwrite)
  val master_hsize = Mux(skb_valid, skb_hsize, io.master.hsize)
  val master_hburst = Mux(skb_valid, skb_hburst, io.master.hburst)
  val master_hprot = Mux(skb_valid, skb_hprot, io.master.hprot)
  val master_htrans = Mux(skb_valid, skb_htrans, io.master.htrans)
  val master_hmastlock = Mux(skb_valid, skb_hmastlock, io.master.hmastlock)
  val master_hwdata = Mux(skb_valid, skb_hwdata, io.master.hwdata)

  val hsels = PriorityEncoderOH(
    (io.slaves zip amap) map { case (s, afn) => {
      s.haddr := master_haddr
      s.hwrite := master_hwrite
      s.hsize := master_hsize
      s.hburst := master_hburst
      s.hprot := master_hprot
      s.htrans := master_htrans
      s.hmastlock := master_hmastlock
      s.hwdata := master_hwdata
      afn(master_haddr) && master_htrans.orR
    }})

  (io.slaves zip hsels) foreach { case (s, hsel) => {
    s.hsel := hsel
    s.hreadyin := skb_valid || io.master.hready
  } }

  val s1_hsels = Array.fill(amap.size){Reg(init = Bool(false))}
  val hreadyouts = io.slaves.map(_.hreadyout)
  val master_hready = s1_hsels.reduce(_||_) === Bool(false) || Mux1H(s1_hsels, hreadyouts)

  when (master_hready) {
    val skid = s1_hsels.reduce(_||_) && (hsels zip hreadyouts).map{ case (s, r) => s && !r }.reduce(_||_)
    skb_valid := skid
    when (skid) {
      skb_haddr := io.master.haddr
      skb_hwrite := io.master.hwrite
      skb_hsize := io.master.hsize
      skb_hburst := io.master.hburst
      skb_hprot := io.master.hprot
      skb_htrans := io.master.htrans
      skb_hmastlock := io.master.hmastlock
    }

    (s1_hsels zip hsels) foreach { case (s1, s) =>
      s1 := s
    }
  }

  io.master.hready := !skb_valid && master_hready
  io.master.hrdata := Mux1H(s1_hsels, io.slaves.map(_.hrdata))
  io.master.hresp := Mux1H(s1_hsels, io.slaves.map(_.hresp))
}

class HastiSlaveMux(n: Int)(implicit p: Parameters) extends HastiModule()(p) {
  val io = new Bundle {
    val ins = Vec(n, new HastiSlaveIO)
    val out = new HastiSlaveIO().flip
  }

  // skid buffers
  val skb_valid = Array.fill(n){Reg(init = Bool(false))}
  val skb_haddr = Array.fill(n){Reg(UInt(width = hastiAddrBits))}
  val skb_hwrite = Array.fill(n){Reg(Bool())}
  val skb_hsize = Array.fill(n){Reg(UInt(width = SZ_HSIZE))}
  val skb_hburst = Array.fill(n){Reg(UInt(width = SZ_HBURST))}
  val skb_hprot = Array.fill(n){Reg(UInt(width = SZ_HPROT))}
  val skb_htrans = Array.fill(n){Reg(UInt(width = SZ_HTRANS))}
  val skb_hmastlock = Array.fill(n){Reg(Bool())}

  val requests = (io.ins zip skb_valid) map { case (in, v) => in.hsel && in.hreadyin || v }
  val grants = PriorityEncoderOH(requests)

  val s1_grants = Array.fill(n){Reg(init = Bool(true))}

  (s1_grants zip grants) foreach { case (g1, g) =>
    when (io.out.hreadyout) { g1 := g }
  }

  def sel[T <: Data](in: Seq[T], s1: Seq[T]) =
    Vec((skb_valid zip s1 zip in) map { case ((v, s), in) => Mux(v, s, in) })

  io.out.haddr := Mux1H(grants, sel(io.ins.map(_.haddr), skb_haddr))
  io.out.hwrite := Mux1H(grants, sel(io.ins.map(_.hwrite), skb_hwrite))
  io.out.hsize := Mux1H(grants, sel(io.ins.map(_.hsize), skb_hsize))
  io.out.hburst := Mux1H(grants, sel(io.ins.map(_.hburst), skb_hburst))
  io.out.hprot := Mux1H(grants, sel(io.ins.map(_.hprot), skb_hprot))
  io.out.htrans := Mux1H(grants, sel(io.ins.map(_.htrans), skb_htrans))
  io.out.hmastlock := Mux1H(grants, sel(io.ins.map(_.hmastlock), skb_hmastlock))
  io.out.hsel := grants.reduce(_||_)

  (io.ins zipWithIndex) map { case (in, i) => {
    when (io.out.hreadyout) {
      when (grants(i)) {
        skb_valid(i) := Bool(false)
      }
      when (!grants(i) && !skb_valid(i)) {
        val valid = in.hsel && in.hreadyin
        skb_valid(i) := valid
        when (valid) { // clock-gate
          skb_haddr(i) := in.haddr
          skb_hwrite(i) := in.hwrite
          skb_hsize(i) := in.hsize
          skb_hburst(i) := in.hburst
          skb_hprot(i) := in.hprot
          skb_htrans(i) := in.htrans
          skb_hmastlock(i) := in.hmastlock
        }
      }
    }
  } }

  io.out.hwdata := Mux1H(s1_grants, io.ins.map(_.hwdata))
  io.out.hreadyin := io.out.hreadyout

  (io.ins zipWithIndex) foreach { case (in, i) => {
    val g1 = s1_grants(i)
    in.hrdata := dgate(g1, io.out.hrdata)
    in.hreadyout := io.out.hreadyout && (!skb_valid(i) || g1)
    in.hresp := dgate(g1, io.out.hresp)
  } }
}

class HastiXbar(nMasters: Int, addressMap: Seq[UInt=>Bool])
               (implicit p: Parameters) extends HastiModule()(p) {
  val io = new Bundle {
    val masters = Vec(nMasters, new HastiMasterIO).flip
    val slaves = Vec(addressMap.size, new HastiSlaveIO).flip
  }

  val buses = List.fill(nMasters){Module(new HastiBus(addressMap))}
  val muxes = List.fill(addressMap.size){Module(new HastiSlaveMux(nMasters))}

  (buses.map(b => b.io.master) zip io.masters) foreach { case (b, m) => b <> m }
  (muxes.map(m => m.io.out)    zip io.slaves ) foreach { case (x, s) => x <> s }
  for (m <- 0 until nMasters; s <- 0 until addressMap.size) yield {
    buses(m).io.slaves(s) <> muxes(s).io.ins(m)
  }
}

class HastiSlaveToMaster(implicit p: Parameters) extends HastiModule()(p) {
  val io = new Bundle {
    val in = new HastiSlaveIO
    val out = new HastiMasterIO
  }

  io.out.haddr := io.in.haddr
  io.out.hwrite := io.in.hwrite
  io.out.hsize := io.in.hsize
  io.out.hburst := io.in.hburst
  io.out.hprot := io.in.hprot
  io.out.htrans := Mux(io.in.hsel && io.in.hreadyin, io.in.htrans, HTRANS_IDLE)
  io.out.hmastlock := io.in.hmastlock
  io.out.hwdata := io.in.hwdata
  io.in.hrdata := io.out.hrdata
  io.in.hreadyout := io.out.hready
  io.in.hresp := io.out.hresp
}

class HastiMasterIONastiIOConverter(implicit p: Parameters) extends HastiModule()(p)
    with HasNastiParameters {
  val io = new Bundle {
    val nasti = new NastiIO().flip
    val hasti = new HastiMasterIO
  }

  require(hastiAddrBits == nastiXAddrBits)
  require(hastiDataBits == nastiXDataBits)

  val s_idle :: s_read :: s_write :: s_write_resp :: Nil = Enum(Bits(), 4)
  val state = Reg(init = s_idle)

  val addr = Reg(UInt(width = hastiAddrBits))
  val id = Reg(UInt(width = nastiXIdBits))
  val size = Reg(UInt(width = nastiXSizeBits))
  val len = Reg(UInt(width = nastiXLenBits))
  val data = Reg(UInt(width = nastiXDataBits))
  val first = Reg(init = Bool(false))
  val rvalid = Reg(init = Bool(false))

  io.nasti.aw.ready := (state === s_idle)
  io.nasti.ar.ready := (state === s_idle) && !io.nasti.aw.valid
  io.nasti.w.ready := (state === s_write) && io.hasti.hready
  io.nasti.b.valid := (state === s_write_resp)
  io.nasti.b.bits := NastiWriteResponseChannel(id = id)
  io.nasti.r.valid := (state === s_read) && io.hasti.hready && !first
  io.nasti.r.bits := NastiReadDataChannel(
    id = id,
    data = io.hasti.hrdata,
    last = (len === UInt(0)))


  io.hasti.haddr := addr
  io.hasti.hsize := size
  io.hasti.hwrite := (state === s_write)
  io.hasti.hburst := HBURST_INCR
  io.hasti.hprot := UInt(0)
  io.hasti.hwdata := data
  io.hasti.htrans := MuxLookup(state, HTRANS_IDLE, Seq(
    s_write -> Mux(io.nasti.w.valid,
      Mux(first, HTRANS_NONSEQ, HTRANS_SEQ),
      Mux(first, HTRANS_IDLE, HTRANS_BUSY)),
    s_read -> MuxCase(HTRANS_BUSY, Seq(
      first -> HTRANS_NONSEQ,
      (len === UInt(0)) -> HTRANS_IDLE,
      io.nasti.r.ready -> HTRANS_SEQ))))

  when (io.nasti.aw.fire()) {
    first := Bool(true)
    addr := io.nasti.aw.bits.addr
    id := io.nasti.aw.bits.id
    size := io.nasti.aw.bits.size
    state := s_write
  }

  when (io.nasti.ar.fire()) {
    first := Bool(true)
    addr := io.nasti.ar.bits.addr
    id := io.nasti.ar.bits.id
    size := io.nasti.ar.bits.size
    len := io.nasti.ar.bits.len
    state := s_read
  }

  when (io.nasti.w.fire()) {
    first := Bool(false)
    addr := addr + (UInt(1) << size)
    data := io.nasti.w.bits.data
    when (io.nasti.w.bits.last) { state := s_write_resp }
  }

  when (io.nasti.b.fire()) { state := s_idle }

  when (state === s_read && first) {
    first := Bool(false)
    addr := addr + (UInt(1) << size)
  }

  when (io.nasti.r.fire()) {
    addr := addr + (UInt(1) << size)
    len := len - UInt(1)
    when (len === UInt(0)) { state := s_idle }
  }
}
