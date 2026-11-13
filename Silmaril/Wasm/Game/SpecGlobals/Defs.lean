module

public import Silmaril.Wasm.Game.Linking.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare

/-!
# Static linking through the specification's instantiation, modules with globals

A linking setup `Linking.Setup` instantiates the provider, the consumer against host stubs and
the linked module with silmaril-lean's `instantiateOnce?`, which allocates every global once.
The specification's `$instantiate` (silmaril-lean's `prepare?` followed by the segment and
start code) allocates every global twice, `$evalglobals` and `$allocmodule`, and the module
instances name the second copies.

* `Setup.SpecStores S`: the configurations that `prepare?` gives the provider (into `base`),
  the consumer against host stubs (into the stubbed **spec** provider store) and the linked
  module (into `base`), none with a start function. In the linker's fragment there are no
  data or element segments, so these configurations have no code: they are the
  specification's instantiations (`Instantiate P host`, every profile and host).
The instances at these stores are the setup's `S.providerI`, `S.consumerI`, `S.linkedI`
(same imports, exports and export addresses) run from the spec stores `X.cp.store`,
`X.ccs.store`, `X.cl.store` (`ScalarInstance.strategy P s` does not read the instance's
recorded store).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Game.Linking

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Link.GC

namespace Setup

variable (S : Setup)

/-- The configurations of the specification's instantiations of a linking setup: the provider
prepared into `base`, the consumer against host stubs prepared into the stubbed spec provider
store, the linked module prepared into `base`; no start function. -/
structure SpecStores where
  /-- The provider's configuration. -/
  cp : Config Nat
  /-- The configuration of the consumer against host stubs. -/
  ccs : Config Nat
  /-- The linked module's configuration. -/
  cl : Config Nat
  prov : prepare? evalConst? S.base S.provider (Preparation.imports []) = some (cp, none)
  cons : prepare? evalConst? (stubOut S.base.funcs.length S.stubs cp.store) S.consumer
    (Preparation.imports (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat))) =
      some (ccs, none)
  linked : prepare? evalConst? S.base S.linked (Preparation.imports []) = some (cl, none)

end Setup

end Silmaril.Wasm.Game.Linking
