// See LICENSE.SiFive for license details.

package freechips.rocketchip.util

import Chisel._
import chisel3.internal.InstanceId
import chisel3.experimental.{annotate, ChiselAnnotation, RawModule}
import firrtl.annotations._

import freechips.rocketchip.diplomacy._
import freechips.rocketchip.regmapper._
import freechips.rocketchip.tilelink.TLToAXI4IdMapEntry

import org.json4s.JsonDSL._
import org.json4s.jackson.JsonMethods.{pretty, render}

/** Record a set of interrupts. */
case class InterruptsPortAnnotation(target: Named, nInterrupts: Seq[Int]) extends SingleTargetAnnotation[Named] {
  def duplicate(n: Named) = this.copy(n)
}
/** Record a case class that was used to parameterize this target. */
case class ParamsAnnotation(target: Named, paramsClassName: String, params: Map[String,Any]) extends SingleTargetAnnotation[Named] {
  def duplicate(n: Named) = this.copy(n)
}

case class ParamsChiselAnnotation[T <: Product](target: InstanceId, params: T) extends ChiselAnnotation {
  private val paramMap = params.getClass.getDeclaredFields.map(_.getName).zip(params.productIterator.to).toMap
  def toFirrtl = ParamsAnnotation(target.toNamed, params.getClass.getName, paramMap)
}

/** Record an address map. */
case class AddressMapAnnotation(target: Named, mapping: Seq[AddressMapEntry], label: String) extends SingleTargetAnnotation[Named] {
  def duplicate(n: Named) = this.copy(n)

  def toUVM: String =
    s"// Instance Name: ${target.serialize}\n" +
      mapping.map(_.range.toUVM).mkString("\n")

  def toJSON: String =
    s"""{\n  "${label}":  [\n""" +
      mapping.map(_.range.toJSON).mkString(",\n") +
      "\n  ]\n}"
}

/** Record a conversion of TL source ids to AXI4 ids. */
case class TLToAXI4IdMapAnnotation(target: Named, mapping: Seq[TLToAXI4IdMapEntry]) extends SingleTargetAnnotation[Named] {
  def duplicate(n: Named) = this.copy(n)
}

/** Marks this module as a candidate for register retiming */
case class RetimeModuleAnnotation(target: ModuleName) extends SingleTargetAnnotation[ModuleName] {
  def duplicate(n: ModuleName) = this.copy(n)
}

/** Annotation capturing information about port slave devices. */
case class SlaveAddressMapChiselAnnotation(
    target: InstanceId,
    addresses: Seq[AddressSet],
    perms: ResourcePermissions) extends ChiselAnnotation {
  private val range = AddressRange.fromSets(addresses)
  def toFirrtl = AddressMapAnnotation(
    target = target.toNamed,
    mapping = range.map { r => AddressMapEntry(r, perms, Nil) },
    label = "slaves")
}

/** Record information about a top-level port of the design */
case class TopLevelPortAnnotation(
    target: ComponentName,
    protocol: String,
    tags: Seq[String],
    mapping: Seq[AddressMapEntry]) extends SingleTargetAnnotation[ComponentName] {
  def duplicate(n: ComponentName): TopLevelPortAnnotation = this.copy(n)
}

/** Record the resetVector. */
case class ResetVectorAnnotation(target: Named, resetVec: BigInt) extends SingleTargetAnnotation[Named] {
  def duplicate(n: Named): ResetVectorAnnotation = this.copy(n)
}

/** Helper object containing methods for applying annotations to targets */
object Annotated {
  def interrupts(component: InstanceId, interrupts: Seq[Int]): Unit = {
    annotate(new ChiselAnnotation {def toFirrtl: Annotation = InterruptsPortAnnotation(
      component.toNamed,
      interrupts
    )})
  }

  def resetVector(component: InstanceId, resetVec: BigInt): Unit = {
    annotate(new ChiselAnnotation {def toFirrtl: Annotation = ResetVectorAnnotation(component.toNamed, resetVec)})
  }

  def params[T <: Product](component: InstanceId, params: T): T = {
    annotate(ParamsChiselAnnotation(component, params))
    params
  }

  def addressMapping(component: InstanceId, mapping: Seq[AddressMapEntry]): Seq[AddressMapEntry] = {
    annotate(new ChiselAnnotation { def toFirrtl = AddressMapAnnotation(component.toNamed, mapping, "mapping") })
    mapping
  }

  def idMapping(component: InstanceId, mapping: Seq[TLToAXI4IdMapEntry]): Seq[TLToAXI4IdMapEntry] = {
    annotate(new ChiselAnnotation { def toFirrtl = TLToAXI4IdMapAnnotation(component.toNamed, mapping) })
    mapping
  }

  def port[T <: Data](
      data: T,
      protocol: String,
      tags: Seq[String],
      mapping: Seq[AddressMapEntry]): T = {
    annotate(new ChiselAnnotation { def toFirrtl = TopLevelPortAnnotation(data.toNamed, protocol, tags, mapping) })
    data
  }
}

/** Mix this into a Module class or instance to mark its ports as untouchable */
trait DontTouch { self: RawModule =>
  // TODO: replace this with an implicit class from UserModule that uses getPorts
  // TODO: this is a workaround for firrtl #756
  def dontTouch(data: Data): Unit = data match {
     case agg: Aggregate => agg.getElements.foreach(dontTouch)
     case elt: Element => chisel3.core.dontTouch(elt)
  }

  /** Marks every port as don't touch
    *
    * @note This method can only be called after the Module has been fully constructed
    *   (after Module(...))
    */
  def dontTouchPorts(): this.type = {
    self.getModulePorts.foreach(dontTouch(_))
    self
  }

  def dontTouchPortsExcept(f: Data => Boolean): this.type = {
    self.getModulePorts.filterNot(f).foreach(dontTouch(_))
    self
  }
}

/** Mix this into a Module class or instance to mark it for register retiming */
trait ShouldBeRetimed { self: RawModule =>
  chisel3.experimental.annotate(new ChiselAnnotation { def toFirrtl = RetimeModuleAnnotation(self.toNamed) })
}


case class RegFieldDescMappingAnnotation(
  target: ModuleName,
  regMappingSer: RegistersSer) extends SingleTargetAnnotation[ModuleName] {
  def duplicate(n: ModuleName): RegFieldDescMappingAnnotation = this.copy(target = n)
}

object GenRegDescsAnno {

  def makeRegMappingSer(
    rawModule: RawModule,
    moduleName: String,
    baseAddress: BigInt,
    width: Int,
    byteOffset: Int,
    bitOffset: Int,
    regField: RegField): RegFieldSer = {

    val anonRegFieldName = s"unnamedRegField${byteOffset.toHexString}_${bitOffset}"
    val selectedRegFieldName = regField.desc.map(_.name).getOrElse(anonRegFieldName)

    val map = Map[BigInt, (String, String)]() // TODO

    val desc = regField.desc

    val regFieldDescSer = RegFieldDescSer(
      byteOffset = s"0x${byteOffset.toInt.toHexString}",
      bitOffset = bitOffset,
      bitWidth = width,
      name = selectedRegFieldName,
      desc = desc.map {_.desc}.getOrElse("None"),
      group = desc.map {_.group.getOrElse("None")}.getOrElse("None"),
      groupDesc = desc.map {_.groupDesc.getOrElse("None")}.getOrElse("None"),
      accessType = desc.map {_.access.toString}.getOrElse("None"),
      wrType = desc.map(_.wrType.toString).getOrElse("None"),
      rdAction = desc.map(_.rdAction.toString).getOrElse("None"),
      volatile = desc.map(_.volatile).getOrElse(false),
      hasReset = desc.map {_.reset != None }.getOrElse(false),
      resetValue = desc.map{_.reset.getOrElse(BigInt(0))}.getOrElse(BigInt(0)),
      enumerations = map
    )

    RegFieldSer(
      moduleName, //selectedName,
      regFieldDescSer
    )
  }


  def anno(
    rawModule: RawModule,
    baseAddress: BigInt,
    mapping: RegField.Map*): Seq[RegField.Map] = {

    val moduleName = rawModule.name
    val baseHex = s"0x${baseAddress.toInt.toHexString}"
    val displayName = s"${moduleName}.${baseHex}"

    val regFieldSers = mapping.flatMap {
      case (byteOffset, seq) =>
        seq.map(_.width).scanLeft(0)(_ + _).zip(seq).map { case (bitOffset, regField) =>
          makeRegMappingSer(
            rawModule,
            moduleName,
            baseAddress,
            regField.width,
            byteOffset,
            bitOffset,
            regField
          )
        }
    }

    val registersSer = RegistersSer(
      displayName = moduleName,
      baseAddress = baseAddress,
      regFields = regFieldSers // Seq[RegFieldSer]()
    )

//    annotate(RegFieldDescMappingAnnotation(rawModule.toNamed, registersSer))
    annotate(new ChiselAnnotation { def toFirrtl = RegFieldDescMappingAnnotation(rawModule.toNamed, registersSer) })

    mapping
  }


  def serialize(base: BigInt, name: String, mapping: RegField.Map*): String = {


    val regDescs = mapping.flatMap { case (byte, seq) =>
      seq.map(_.width).scanLeft(0)(_ + _).zip(seq).map { case (bit, f) =>
        val anonName = s"unnamedRegField${byte.toHexString}_${bit}"
        (f.desc.map{ _.name}.getOrElse(anonName)) -> f.toJson(byte, bit)
      }
    }

    pretty(render(
      ("peripheral" -> (
        ("displayName" -> name) ~
          ("baseAddress" -> s"0x${base.toInt.toHexString}") ~
          ("regfields" -> regDescs)))))
  }
}

