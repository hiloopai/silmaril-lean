module

public import Silmaril.Compiler.CompilesTo.Sim.Defs
public import Silmaril.Proofs.Compiler.CompilesTo.Sim.Compose

/-!
# Cut-point simulation: theorems

* `Corr.whole_of_segments`: every segment simulated ⇒ the whole run simulated, from every point.
* `Source.Safe.of_reaches`: safety is inherited along source runs.
* `Hop.transGen`, `Seg.transGen`, `acc_transGen`.
-/
