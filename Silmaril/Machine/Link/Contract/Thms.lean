module

public import Silmaril.Machine.Link.Contract.Defs
public import Silmaril.Proofs.Machine.Link.Compose
public import Silmaril.Machine.Link.Unit.Thms

/-! # Contracts of translation units: theorems (header)

PROVED (`Silmaril.Proofs.Machine.Link.Compose`, standard axioms), for any program
logic `L : Logic Spec`, any `SectionLocal` relocator and any successful link of
the imported linker:

* `link_compose`: if every unit satisfies `TU.Sat`, the units are
  `AbiCompatible`, and `ImportsClosed` holds (every import served, up to
  `L.Sub`, by some unit's export or by an assumed external that is safe in the
  context), then every export of every unit is `L.Safe n` at its address in the
  linked layout, for **every** `n`, in every context extending the linked image.
  Cyclic imports (mutual recursion across units) are covered: the proof is
  induction on the step index, there is no acyclicity hypothesis, and so no
  `Task.link_compose_cyclic` is needed. The acyclic case is a special case;
* `link_compose_valuation`, `linkUnits_compose`: the same conclusion at the
  link's one valuation `σ*`, and for the ABI-checked `Unit.linkUnits`;
* `restrict_wellPlaced`: after a successful link, `restrict layout slot` is
  `WellPlaced` (closes the L3 gap `image_not_wellPlaced` for the placements
  `link_compose` uses);
* `globalValuation_export`: the valuation of a name a unit defines is that
  unit's `TU.exportAddr` under `restrict` (connects `TU.exportAddr` to
  `globalValuation_owner`);
* `exports_defined`: under `AbiCompatible`, every declared export is a defined
  global of its object;
* `image_congr_valuation`: an image depends on `σ` only on the unit's undefined
  globals (locality in the valuation);
* `ownershipDisjoint_of_link`: `OwnershipDisjoint` follows from a successful
  link, so it is not a hypothesis of `link_compose`;
* `TU.Sat.of_frame`: a unit whose exports are safe in its own image satisfies
  its contract (by `Logic.frame`);
* flag-aware inclusion (F3): `Extends` keeps section flags (`ContainsF`);
  `Extends.contains` (byte-level inclusion), `Extends.refl`, `Extends.trans`,
  `Extends.of_subset`, `extends_of_unit`.

Assumed: nothing beyond the hypotheses stated. Not covered here: a validator of
`ld` output (`validate_sound`), relocatable partial links (`ld -r`), and the
semantic content of ownership (other units not writing owned memory), which
belongs to the instantiated logic. A toy instance with real gcc objects and both
the bfd and the gold layouts is `Silmaril.Machine.Link.Examples.TwoTu.Thms`.
-/
