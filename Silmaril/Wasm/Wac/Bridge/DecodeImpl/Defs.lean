module

public import Silmaril.Wasm.Wac.Bridge.DecodeNamed.Defs
public import Silmaril.Wasm.Wit.Project.Defs
public import Silmaril.Wasm.Wac.Bridge.Encode.Defs

/-!
# WAC bridge: component (implementation) binaries

`Bridge.DecodeNamed.decodePkg_world` and `Bridge.DecodeItems.decodePkg_itemsPackage` are
about WIT packages, whose binaries only declare types. A component that implements a
world also has code: core modules and instances, `canon` definitions, aliases of core
exports, instantiations, nested components, custom sections. `decodePkg` reads such a
component through its projection (`Wit.Project.projectI`), which skips the code.

`Impl ss ds` says that the sections `ss` (split into sections of one element, as the
projection reads them) declare exactly the declarations `ds` of a world, interleaved
with sections the projection replays without declaring anything (`Silent`: code,
instantiations, aliases of functions, values, …):

* an import declaration `(import n d)` is an import section of that import;
* a type definition is a type section of it (not a resource definition);
* an export declaration `(export n d)` is an export section whose type is `d`, by its
  ascription or, for a type export without ascription, `(type (eq i))` of its index
  (`Wit.Project.exportDesc`); the exported item itself (a lifted function, an
  instance, …) is arbitrary.

The theorems are in `Bridge.DecodeImpl.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary

namespace DecodeImpl

/-- A section of one element the projection replays without declaring anything. -/
def Silent (s : Section) : Prop :=
  ∀ st : Wit.Project.PState, ∃ st', Wit.Project.step st s = some st' ∧ st'.decls = st.decls

/-- **The sections `ss` declare the world declarations `ds`**, among silent ones. -/
inductive Impl : List Section → List ComponentDecl → Prop
  | nil : Impl [] []
  | silent {s : Section} {ss : List Section} {ds : List ComponentDecl} :
      Silent s → Impl ss ds → Impl (s :: ss) ds
  | imp {i : Silmaril.Wasm.Component.Binary.Import} {ss : List Section} {ds : List ComponentDecl} :
      Wit.Project.isValueEq i.desc = false → Impl ss ds →
      Impl (.imports [i] :: ss) (.import i.name i.desc :: ds)
  | ty {t : DefType} {ss : List Section} {ds : List ComponentDecl} :
      Wit.Project.isResource t = false → Impl ss ds → Impl (.types [t] :: ss) (.inst (.type t) :: ds)
  | exp {e : Silmaril.Wasm.Component.Binary.Export} {d : ExternDesc} {ss : List Section} {ds : List ComponentDecl} :
      Wit.Project.exportDesc e = some d → Wit.Project.isValueEq d = false → Impl ss ds →
      Impl (.exports [e] :: ss) (.inst (.export e.name d) :: ds)

/-- A component implements the declarations `ds`: its sections, split, are `Impl`. -/
def Implements (c : Ast) (ds : List ComponentDecl) : Prop :=
  Impl (c.sections.flatMap Wit.Project.splitSection) ds

/-! ## Type shells -/

/-- The section declaring one world declaration, in a component that implements it
(exports export item `0` of their sort, with the declaration as ascription). -/
def shellSec : ComponentDecl → Option Section
  | .import n d => some (.imports [⟨n, d⟩])
  | .inst (.type t) => some (.types [t])
  | .inst (.export n d) => some (.exports [⟨n, ⟨descSort d, 0⟩, some d⟩])
  | _ => none

/-- The declarations `shellSec` covers: imports, exports (not `(value (eq i))`) and type
definitions (not resources). -/
def shellOk : ComponentDecl → Bool
  | .import _ d => !Wit.Project.isValueEq d
  | .inst (.type t) => !Wit.Project.isResource t
  | .inst (.export _ d) => !Wit.Project.isValueEq d
  | _ => false

/-- A component with code `code` followed by the sections of the declarations `ds`. -/
def shell (code : List Section) (ds : List ComponentDecl) : Ast := .mk (code ++ ds.filterMap shellSec)

end DecodeImpl

end Silmaril.Wasm.Wac.Bridge
