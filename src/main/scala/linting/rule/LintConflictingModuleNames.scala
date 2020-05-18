// See LICENSE.SiFive for license details.

package freechips.rocketchip.linting
package rule

import firrtl._
import firrtl.annotations.{CircuitTarget, HasSerializationHints, IsModule, SingleTargetAnnotation, Target}
import firrtl.ir._
import firrtl.options.{Dependency, HasShellOptions, PreservesAll, ShellOption}
import firrtl.stage.Forms
import firrtl.transforms.DedupModules

import chisel3.aop.{Aspect, Select}
import chisel3.RawModule
import chisel3.util.Queue

import freechips.rocketchip.diplomacy.{LazyModule, LazyModuleImpLike}
import freechips.rocketchip.tilelink._
import freechips.rocketchip.system.TestHarness

import scala.collection.mutable

/** A helper to rename modules in a [[Circuit]]
  */
object RenameModules {
  def onStmt(moduleNameMap: Map[String, String])(stmt: Statement): Statement = stmt match {
    case inst: WDefInstance if moduleNameMap.contains(inst.module) => inst.copy(module = moduleNameMap(inst.module))
    case inst: DefInstance if moduleNameMap.contains(inst.module) => inst.copy(module = moduleNameMap(inst.module))
    case other => other.mapStmt(onStmt(moduleNameMap))
  }

  /** Renames the modules in a circuit given a mapping of old names to new names
    *
    * @param nameMappings mapping of old to new names
    * @param circuit the circuit to rename
    */
  def apply(nameMappings: Map[String, String], circuit: Circuit): Circuit = {
    val modules = circuit.modules.map {
      case mod: Module => mod.mapStmt(onStmt(nameMappings)).mapString(m => nameMappings.getOrElse(m, m))
      case ext: ExtModule => ext
    }
    val main = nameMappings.getOrElse(circuit.main, circuit.main)
    circuit.copy(main = main, modules = modules)
  }
}

/** A strategy for generating a new names for modules
  */
sealed trait NamingStrategy {

  /** Generates a new stable module name based on the desired name and the module IR node
    *
    * called by [[LintConflictingModuleNames]] to rename modules
    *
    * @param desiredName the requested name for the module, generated name should contain this name
    * @param module the module targeted by the desiredName
    */
  def getName(desiredName: String)(module: Module): String
}

/** A naming strategy that always returns the desired name
  */
case object ExactNamingStrategy extends NamingStrategy {
  def getName(desiredName: String)(module: Module): String = desiredName
}

/** A naming strategy that appends the port structure hash to the desired name i.e. "{desiredName}_p{hash}"
  */
case object PortStructureNamingStrategy extends NamingStrategy {
  def getName(desiredName: String)(module: Module): String = {
    val noNamePorts = module.ports.map(NamingStrategy.removePortNames(_))
     NamingStrategy.appendHashCode(desiredName, "p", noNamePorts.hashCode)
  }
}

/** A naming strategy that appends the name-agnostic module content hash to the desired name i.e. "{desiredName}_c{hash}"
  */
case object ContentStructureNamingStrategy extends NamingStrategy {
  def getName(desiredName: String)(module: Module): String = {
    val noNameModule = NamingStrategy.removeModuleNames(module)
    NamingStrategy.appendHashCode(desiredName, "c", noNameModule.hashCode)
  }
}

/** A naming strategy that appends the module content hash to the desired name i.e. "{desiredName}_C{hash}"
  */
case object ContentNamingStrategy extends NamingStrategy {
  def getName(desiredName: String)(module: Module): String = {
    val noInfoModule = NamingStrategy.removeModuleInfo(module).copy(name = NamingStrategy.emptyName)
    NamingStrategy.appendHashCode(desiredName, "C", noInfoModule.hashCode)
  }
}

object NamingStrategy {

  final val emptyName: String = ""

  def appendHashCode(desiredName: String, hashPrefix: String, hashCode: Int): String = {
    s"${desiredName}_$hashPrefix" + f"${hashCode}%08X"
  }


  // remove name helpers

  def removeTypeNames(tpe: Type): Type = tpe match {
    case g: GroundType => g
    case v: VectorType => v
    case b: BundleType => b.copy(fields = b.fields.map { field =>
      field.copy(name = emptyName)
    })
  }

  def removeStatementNames(stmt: Statement): Statement = stmt match {
    case i: DefInstance => i.copy(
      name = emptyName,
      module = emptyName,
      info = NoInfo)
    case i: WDefInstance => i.copy(
      name = emptyName,
      module = emptyName,
      tpe = removeTypeNames(i.tpe),
      info = NoInfo)
    case _ => stmt
      .mapStmt(removeStatementNames)
      .mapString(_ => emptyName)
      .mapInfo(_ => NoInfo)
      .mapType(removeTypeNames)
  }

  def removePortNames(port: Port): Port = {
    port.copy(name = emptyName, tpe = removeTypeNames(port.tpe), info = NoInfo)
  }

  def removeModuleNames(mod: Module): Module = {
    mod.copy(
      ports = mod.ports.map(removePortNames(_)),
      body = removeStatementNames(mod.body),
      name = emptyName,
      info = NoInfo)
  }

  // remove Info helpers

  def removeStatementInfo(stmt: Statement): Statement = {
    stmt.mapStmt(removeStatementInfo).mapInfo(_ => NoInfo)
  }

  def removePortInfo(port: Port): Port = {
    port.copy(info = NoInfo)
  }

  def removeModuleInfo(mod: Module): Module = {
    mod.copy(
      ports = mod.ports.map(removePortInfo(_)),
      body = removeStatementInfo(mod.body),
      info = NoInfo)
  }
}

/** Specifies a naming strategy to use for a module and the modules that it collides with
  */
case class NamingStrategyAnnotation(
  strategy: NamingStrategy,
  target: IsModule
) extends SingleTargetAnnotation[IsModule] with HasSerializationHints {
  def typeHints: Seq[Class[_]] = Seq(
    ExactNamingStrategy.getClass,
    PortStructureNamingStrategy.getClass,
    ContentStructureNamingStrategy.getClass,
    ContentNamingStrategy.getClass
  )

  def duplicate(newTarget: IsModule): NamingStrategyAnnotation = {
    this.copy(target = newTarget)
  }
}

/** Specifies a desired name for a module
  */
case class ModuleNameAnnotation(
  desiredName: String,
  target: IsModule
) extends SingleTargetAnnotation[IsModule] {
  def duplicate(newTarget: IsModule): ModuleNameAnnotation = {
    this.copy(target = newTarget)
  }
}

/** An example of how to customize the names of certain modules using an Aspect
  */
case object StabilizeNamesAspect extends Aspect[RawModule] {
  def toAnnotation(top: RawModule): AnnotationSeq = {
    Select.collectDeep(top) {
      // annotating all Queues with a more descriptive desired name
      case m: Queue[_] => Seq(new ModuleNameAnnotation(s"Queue_${m.genType.getClass.getSimpleName}_entries_${m.entries}", m.toTarget))
      case m: TLMonitor => Seq(new ModuleNameAnnotation(m.desiredName, m.toTarget))

      // annotating specific instances
      case th: TestHarness =>
        val core = th.ldut.rocketTiles.head.module.core
        Seq(
          ModuleNameAnnotation("Rocket_Core_0", core.toTarget),
          NamingStrategyAnnotation(ExactNamingStrategy, core.toTarget),
        )
    }.flatten.toSeq
  }
}

/** This LintRule checks for module name collisions and optionally renames them to stable hash names
  *
  * Module name collisions occur when different [[Module]]s are annotated with
  * [[ModuleNameAnnotation]]s that have the same desiredName. By default all
  * module name conflicts will cause a [[LintViolation]] (using
  * [[ExactNamingStrategy]]). If one of the modules is targeted by
  * [[NamingStrategyAnnotation]] then the transform will attempt to rename
  * modules according to that naming strategy. If the conflicting modules
  * cannot be disambiguated by the naming strategy then a [[LintViolation]] is
  * emitted.
  */
final class LintConflictingModuleNames extends LintRule {
  val recommendedFix: String = "override desiredName based on module parameters"

  val lintName: String = "conflicting-module-names"

  private val strategyOrder = Seq(
    ExactNamingStrategy,
    PortStructureNamingStrategy,
    ContentStructureNamingStrategy,
    ContentNamingStrategy,
  )

  private def checkStrategy(
    strategy: NamingStrategy,
    desiredName: String,
    modules: Seq[Module]): Option[Map[String, String]] = {
    val fn = strategy.getName(desiredName)(_)
    val nameMap = modules.map(m => m.name -> fn(m)).toMap
    if (nameMap.values.toSet.size == modules.size) Some(nameMap) else None
  }

  private def pickStrategies(
    violations: Violations,
    strategies: Seq[NamingStrategy],
    desiredName: String,
    modules: Seq[Module]): Map[String, String] = {
    val result = strategies.foldLeft(None: Option[Map[String, String]]) {
      case (None, strategy) => checkStrategy(strategy, desiredName, modules)
      case (some, _) => some
    }
    if (result.isDefined) {
      result.get
    } else {
      val msg = s"No naming strategy resolves module collisions for desired name: $desiredName"
      val info = MultiInfo(modules.map(_.info))
      val mods = violations.getOrElse((info, msg), Set.empty)
      violations((info, msg)) = mods ++ modules.map(_.name)
      Map.empty
    }
  }

  override def execute(state: CircuitState): CircuitState = {
    val violations = new Violations()

    val modMap = state.circuit.modules.collect {
      case m: Module => m.name -> m
    }.toMap

    val namingStrategyAnnos = state.annotations.collect {
      case a: NamingStrategyAnnotation if a.target.circuit == state.circuit.main => a
    }

    val strategyMap = namingStrategyAnnos.groupBy { a =>
      val referringModule = Target.referringModule(a.target).module
      require(modMap.contains(referringModule), "NamingStrategyAnnotation may not refer to blackboxes")
      referringModule
    }.map { case (module, annos) =>
      val strategies = annos.map(_.strategy).distinct
      require(strategies.size == 1, s"Conflicting naming strategies for module $module: ${strategies.mkString(", ")}")
      module -> strategies.head
    }

    val moduleNameAnnos = state.annotations.collect {
      case a: ModuleNameAnnotation if a.target.circuit == state.circuit.main => a
    }

    val moduleToDesiredName: mutable.Map[String, mutable.Set[String]] = mutable.Map()

    val nameMap = moduleNameAnnos.groupBy(_.desiredName).mapValues { annos =>
      annos.map(a => Target.referringModule(a.target).module).distinct.map { referringModule =>
        require(modMap.contains(referringModule), "ModuleNameAnnotations may not refer to blackboxes")
        val desiredNames = moduleToDesiredName.getOrElseUpdate(referringModule, mutable.Set())
        desiredNames += annos.head.desiredName
        modMap(referringModule)
      }
    }

    val conflictingDesiredNames = moduleToDesiredName.collect {
      case kv@ (moduleName, desiredName) if desiredName.size > 1 => kv
    }

    require(conflictingDesiredNames.size == 0, {
      val expanation = conflictingDesiredNames.map {
        case (modName, desiredNames) => s"  ${modName}: ${desiredNames.mkString(", ")}"
      }.mkString("\n")
      s"Modules may not have more than one desiredName:\n${expanation}"
    })

    val nameMappings = nameMap.map { case (desiredName, modules) =>
      val strategyOpt = modules.collectFirst {
        case m if strategyMap.contains(m.name) => strategyMap(m.name)
      }
      val strategy = strategyOpt.getOrElse(ExactNamingStrategy)
      val result = checkStrategy(strategy, desiredName, modules)
      if (result.isDefined) {
        result.get
      } else {
        val msg = s"Requested naming strategy $strategy does not resolve module collisions for desired name: $desiredName"
        val info = MultiInfo(modules.map(_.info))
        val mods = violations.getOrElse((info, msg), Set.empty)
        violations((info, msg)) = mods ++ modules.map(_.name)
        Map.empty[String, String]
      }
    }.flatten.toMap

    val circuit = RenameModules(nameMappings, state.circuit)

    val newMain = CircuitTarget(circuit.main)
    val oldMain = CircuitTarget(state.circuit.main)
    val renames = RenameMap()
    nameMappings.foreach { case (from, to) =>
      renames.record(oldMain.module(from), newMain.module(to))
    }

    val whitelist = collectWhitelist(state.annotations)
    val errorList = violations.collect {
      case ((info, message), mods) if !isWhitelisted(info, whitelist) => Violation(this, info, message, mods)
    }.toSeq.sortBy { _.toString }
    val newAnnos = errorList ++ state.annotations

    state.copy(circuit = circuit, annotations = newAnnos, renames = Some(renames))
  }
}