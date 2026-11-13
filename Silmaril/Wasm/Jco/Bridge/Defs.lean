module

public import Silmaril.Wasm.Jco.Fuse.Defs
public import Silmaril.Wasm.Jco.Thin.Canon.Defs

/-!
# Relating the two settings of the jco part on the memory-free fragment

The jco part has two settings (`docs/projects/wasm-components.md`):

* the **memory-based model**: an abstract core instance `CoreInst`, behaviours as relations `RM`,
  the construction `wrap md` and the thin wrapper `thinComp md r`;
* the **component IR**: game semantics `Comp.denU` over a core semantics `C : CoreSem M`, the
  adaptor-style component `Fuse.adaptorComp`/`Fuse.simpleComp`, the single core module and the
  wrapper-style component (`Fuse.simpleWrapper`).

They meet on **pure modules** (`PMod`): core modules without imports whose exports are stateless
deterministic functions of their flat arguments, given by name (`PMod.fn`). A pure module is both

* a core module of the IR, with the semantics `pureSem` (each export answers at once), and
* a core instance `PMod.inst` (state `Unit`, an empty memory, `call n` is `fn n` for an export `n`
  and traps for any other name).

On the **memory-free fragment** (`Meta.memFree`: no `string` or `list<u8>` parameter or result)
a world `md` gives the IR interface `Meta.iface md` (`Sig.toFuncTy`). Both settings then compute
the same partial function `pureCall md m s vs`: type check and lower the arguments
(`checkLower`), call the module's export named `s.name`, lift the result (`liftRes`). The results
(`Silmaril.Wasm.Jco.Bridge.Thms`) are that the IR strategy of `simpleComp [] (Meta.iface md) m` is the
handler answering `pureCall` (`bridgeAns`), and that every lift of `wrap md` (and of
`thinComp md r`) over `PMod.inst m` is `RM.ofOption (pureCall md m s vs)`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Bridge

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco.Fuse

/-! ## Pure modules -/

/-- A pure core module: no imports, stateless deterministic exports given by name. -/
structure PMod where
  exports : CoreIface
  fn : String → List Flat → Option (List Flat)

instance : CoreModule PMod where
  imports _ := []
  exports := PMod.exports

namespace PMod

/-- Calling the export named `n` (a trap if there is none). -/
def callN (m : PMod) (n : String) (xs : List Flat) : Option (List Flat) :=
  if m.exports.any (·.1 == n) then m.fn n xs else none

/-- The IR semantics of a pure module: export `i` on flat arguments answers `fn` at once. -/
def handler (m : PMod) : Handler (sigN 0) (sigN m.exports.length) := fun q =>
  match q.2 with
  | .flat xs => .pure ((m.fn (m.exports[q.1]).1 xs).map .flat)
  | .vals _ => .pure none

/-- The memory-based instance of a pure module. -/
def inst (m : PMod) : Silmaril.Wasm.Jco.CoreInst where
  St := Unit
  mem _ := []
  setMem s _ := s
  call n xs := Silmaril.Wasm.Jco.RM.ofOption (m.callN n xs)

end PMod

/-- The core semantics of pure modules. -/
def pureSem : CoreSem PMod := ⟨fun m => Strategy.ofHandler m.handler⟩

/-! ## The world as an IR interface -/

open Silmaril.Wasm.Jco (PTy PVal Sig Meta)

/-- The memory-free type of a fragment type (`string` and `list<u8>`, outside the memory-free
fragment, are sent to `bool`). -/
def PTy.toVal : PTy → ValTy
  | .val t => t
  | _ => .bool

/-- The IR function type of a world function. -/
def Sig.toFuncTy (s : Sig) : FuncTy :=
  ⟨s.params.map PTy.toVal, match s.result with
    | some t => [PTy.toVal t]
    | none => []⟩

/-- The world as an IR interface. -/
def Meta.iface (md : Meta) : Iface := md.world.map fun s => (s.name, Sig.toFuncTy s)

/-! ## The common partial function -/

/-- Lifting a memory-free result. -/
def liftRes : Option PTy → List Flat → Option (Option PVal)
  | none, [] => some none
  | some (.val t), ys =>
    match t.lift ys with
    | some (v, []) => some (some (.val v))
    | _ => none
  | _, _ => none

/-- **A call of a world function of a pure module**, on the memory-free fragment. -/
def pureCall (m : PMod) (s : Sig) (vs : List Val) : Option (Option PVal) :=
  (checkLower (s.params.map PTy.toVal) vs).bind fun xs =>
    (m.callN s.name xs).bind fun ys => liftRes s.result ys

/-- The IR payload of a result. -/
def resPayload : Option PVal → Payload
  | some (.val v) => .vals [v]
  | _ => .vals []

/-- **The IR answers of the component**: export `i` on component values is `pureCall` of world
function `i`; anything else traps. -/
def bridgeAns (md : Meta) (m : PMod) : sigU.Op → Option Payload
  | (i, .vals vs) =>
    match md.world[i]? with
    | some s => (pureCall m s vs).map resPayload
    | none => none
  | (_, .flat _) => none

/-- **The memory-based answers**: export `name` on component values is `pureCall` of the first
world function named `name`; a missing name traps. -/
def specPure (md : Meta) (m : PMod) (name : String) (vs : List Val) :
    Silmaril.Wasm.Jco.RM Unit (Option PVal) :=
  match md.world.find? (·.name == name) with
  | some s => Silmaril.Wasm.Jco.RM.ofOption (pureCall m s vs)
  | none => Silmaril.Wasm.Jco.RM.fail

end Silmaril.Wasm.Jco.Bridge
