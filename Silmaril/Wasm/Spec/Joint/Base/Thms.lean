module

public import Silmaril.Wasm.Spec.Joint.Base.Defs
public import Silmaril.Proofs.Wasm.Spec.Joint.Base

@[expose] public section

/-!
# Change of base: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Joint.Base` (and short ones in
`Silmaril.Wasm.Spec.Joint.Base.Defs`).

* `Iface.mapF τ`: interfaces along a type map form a functor; for injective `τ` it is fully
  faithful (`Iface.unmapHom_mapHom`, `Iface.mapHom_unmapHom`, `Iface.mapHom_comp_eq`,
  `Iface.unmapHom_mapHom_comp`).
* `Good.image_map`: the image of a good trace set under a map of events is good.
* `back_mapP`: **observation commutes with change of base**: reading a translated trace through a
  mapped morphism is translating the reading; hence `reduct_evImage`
  (`reduct (mapHom τ f) (evImage τ α β T) = evImage τ α β (reduct f T)`), and `evImage_mono`.
-/
