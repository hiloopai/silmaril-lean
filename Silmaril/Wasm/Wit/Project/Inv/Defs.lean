module

public import Silmaril.Wasm.Wit.Project.Ext.Defs

/-!
# Invariance of the extended projection: definitions

* `nfSec`: the WAT normal form of a section of one element (`Wat.normSection` of a
  section is `nfSec` on its split, `Silmaril.Wasm.Wit.Project.normSection_eq`);
* `ascribed`: every export of a function or a nested component carries a type
  ascription. `projectX` reads the type of an unascribed function export from the
  `canon lift` that defined the function, and that of an unascribed component
  export from its import, so dropping code (`stripCode`, which drops `canon`)
  changes `projectX` exactly when such an export exists
  (`Silmaril.Wasm.Wit.Project.Inv.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat (normName normDefType normInstance norm)

/-- The WAT normal form of a section of one element: names without attributes spelled
`0x00`, type definitions in normal form, nested components normalised. -/
def nfSec : Section → Section
  | .component c => .component (norm c)
  | .instances xs => .instances (xs.map normInstance)
  | .types xs => .types (xs.map normDefType)
  | .imports xs => .imports (xs.map fun x => ⟨normName x.name, x.desc⟩)
  | .exports xs => .exports (xs.map fun x => ⟨normName x.name, x.item, x.desc⟩)
  | s => s

/-- Whether an export of a function or component carries a type ascription. -/
def exportAscribed (e : Export) : Bool :=
  match e.item.sort with
  | .func | .component => e.desc.isSome
  | _ => true

/-- Whether every export in a section carries the ascriptions `stripCode` needs. -/
def secAscribed : Section → Bool
  | .exports xs => xs.all exportAscribed
  | _ => true

/-- Every export of a function or nested component of `c` has a type ascription. -/
def ascribed (c : Ast) : Bool := c.sections.all secAscribed

end Silmaril.Wasm.Wit.Project
