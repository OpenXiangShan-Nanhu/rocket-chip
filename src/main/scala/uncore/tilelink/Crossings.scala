package uncore.tilelink

import Chisel._
import junctions._

object AsyncClientUncachedTileLinkCrossing {
  def apply(from_clock: Clock, from_reset: Bool, from_source: ClientUncachedTileLinkIO,
            to_clock: Clock, to_reset: Bool,
            depth: Int = 8, sync: Int = 3): ClientUncachedTileLinkIO = {
    val to_sink = Wire(new ClientUncachedTileLinkIO()(from_source.p))

    to_sink.acquire <> AsyncDecoupledCrossing(
      from_clock, from_reset, from_source.acquire,
      to_clock, to_reset, depth, sync)
    from_source.grant <> AsyncDecoupledCrossing(
      to_clock, to_reset, to_sink.grant,
      from_clock, from_reset, depth, sync)

    to_sink
  }
}

object AsyncClientTileLinkCrossing {
  def apply(from_clock: Clock, from_reset: Bool, from_source: ClientTileLinkIO,
            to_clock: Clock, to_reset: Bool,
            depth: Int = 8, sync: Int = 3): ClientTileLinkIO = {
    val to_sink = Wire(new ClientTileLinkIO()(from_source.p))

    to_sink.acquire <> AsyncDecoupledCrossing(
      from_clock, from_reset, from_source.acquire,
      to_clock, to_reset, depth, sync)
    to_sink.release <> AsyncDecoupledCrossing(
      from_clock, from_reset, from_source.release,
      to_clock, to_reset, depth, sync)
    to_sink.finish <> AsyncDecoupledCrossing(
      from_clock, from_reset, from_source.finish,
      to_clock, to_reset, depth, sync)
    from_source.grant <> AsyncDecoupledCrossing(
      to_clock, to_reset, to_sink.grant,
      from_clock, from_reset, depth, sync)
    from_source.probe <> AsyncDecoupledCrossing(
      to_clock, to_reset, to_sink.probe,
      from_clock, from_reset, depth, sync)

    to_sink
  }

}

object AsyncManagerTileLinkCrossing {
  def apply(from_clock: Clock, from_reset: Bool, from_source: ManagerTileLinkIO,
            to_clock: Clock, to_reset: Bool,
            depth: Int = 8, sync: Int = 3): ManagerTileLinkIO = {
    val to_sink = Wire(new ManagerTileLinkIO()(from_source.p))

    from_source.acquire <> AsyncDecoupledCrossing(
      to_clock, to_reset, to_sink.acquire,
      from_clock, from_reset, depth, sync)
    from_source.release <> AsyncDecoupledCrossing(
      to_clock, to_reset, to_sink.release,
      from_clock, from_reset, depth, sync)
    from_source.finish <> AsyncDecoupledCrossing(
      to_clock, to_reset, to_sink.finish,
      from_clock, from_reset, depth, sync)
    to_sink.grant <> AsyncDecoupledCrossing(
      from_clock, from_reset, from_source.grant,
      to_clock, to_reset, depth, sync)
    to_sink.probe <> AsyncDecoupledCrossing(
      from_clock, from_reset, from_source.probe,
      to_clock, to_reset, depth, sync)

    to_sink
  }
}

object AsyncClientUncachedTileLinkTo {
  def apply(to_clock: Clock, to_reset: Bool, source: ClientUncachedTileLinkIO,
            depth: Int = 8, sync: Int = 3): ClientUncachedTileLinkIO = {
    val scope = AsyncScope()
    AsyncClientUncachedTileLinkCrossing(scope.clock, scope.reset, source, to_clock, to_reset, depth, sync)
  }
}

object AsyncClientTileLinkTo {
  def apply(to_clock: Clock, to_reset: Bool, source: ClientTileLinkIO,
            depth: Int = 8, sync: Int = 3): ClientTileLinkIO = {
    val scope = AsyncScope()
    AsyncClientTileLinkCrossing(scope.clock, scope.reset, source, to_clock, to_reset, depth, sync)
  }
}

object AsyncManagerTileLinkTo {
  def apply(to_clock: Clock, to_reset: Bool, source: ManagerTileLinkIO,
            depth: Int = 8, sync: Int = 3): ManagerTileLinkIO = {
    val scope = AsyncScope()
    AsyncManagerTileLinkCrossing(scope.clock, scope.reset, source, to_clock, to_reset, depth, sync)
  }
}

object AsyncClientUncachedTileLinkFrom {
  def apply(from_clock: Clock, from_reset: Bool, from_source: ClientUncachedTileLinkIO,
            depth: Int = 8, sync: Int = 3): ClientUncachedTileLinkIO = {
    val scope = AsyncScope()
    AsyncClientUncachedTileLinkCrossing(from_clock, from_reset, from_source, scope.clock, scope.reset, depth, sync)
  }
}

object AsyncClientTileLinkFrom {
  def apply(from_clock: Clock, from_reset: Bool, from_source: ClientTileLinkIO,
            depth: Int = 8, sync: Int = 3): ClientTileLinkIO = {
    val scope = AsyncScope()
    AsyncClientTileLinkCrossing(from_clock, from_reset, from_source, scope.clock, scope.reset, depth, sync)
  }
}

object AsyncManagerTileLinkFrom {
  def apply(from_clock: Clock, from_reset: Bool, from_source: ManagerTileLinkIO,
            depth: Int = 8, sync: Int = 3): ManagerTileLinkIO = {
    val scope = AsyncScope()
    AsyncManagerTileLinkCrossing(from_clock, from_reset, from_source, scope.clock, scope.reset, depth, sync)
  }
}
