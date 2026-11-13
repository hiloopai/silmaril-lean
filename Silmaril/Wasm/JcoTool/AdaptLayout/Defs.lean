module

public import Silmaril.Wasm.JcoTool.Adapt.Defs
public import Silmaril.Wasm.JcoTool.Layout.Defs

/-!
# A layout certificate for the general layout (`Adapt.emit`)

`Layout` reads the certified layout of `NewI.emit` (one core module, the shim and fixup
modules) back from the parsed bytes and compares the reading with what the plan describes.
This module does the same for the general layout of `Adapt.emit`: the main module, the
collected adapters, the task-hook wrappers, the shim and fixup modules and the `_initialize`
module.

* **The reading** (`readA`), on the index spaces of `Layout.spaces`: for the instance of every
  core module `m` of the plan (`0` the main module, `k + 1` adapter `k`), each of its core
  function imports resolved to what defines it (`Src`): a lower, a resource built-in or an
  async built-in (`Layout.coreR`, as in the certified layout), an export of the instance of
  module `m'` (`modExport m' name`), or a task-hook wrapper of such an export
  (`hook inst name`, from the hook module's export `hook-<inst>-<name>`). A core function
  exported by the shim is followed through the `fixup` instantiation (`actual`) to the function
  that fills the slot. Every export: a function export to its `canon lift` (the core function,
  async, callback and post-return resolved the same way), an instance export to the lifts given
  to its shim component. Every resource definition with its destructor.
* **The layout the plan describes** (`expectedA p`): the main module's imports as the plan
  classified them (`MainReq`: a request, or an export of an adapter), each adapter's imports
  (`AdReq`: a request, or an export of the main module), the world's exports and exported
  interfaces lifted from the module the plan chose (`Impl.by_`), through the task-hook wrapper
  when the plan has one for that function, and the destructors.

`layoutOkA p x` is `readA … x = some (expectedA p)`; `checkA` runs it on the bytes `newAdapt`
writes (`AdaptLayout.Thms`: `newAdaptL_layout`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.AdaptLayout

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.JcoTool.Layout (RS CF CI FF II TT CoreR ResRef lookupS)
open Silmaril.Wasm.JcoTool.NewI (IReq ifaces keyName fname funcImportName)
open Silmaril.Wasm.JcoTool.Adapt (Plan MainReq AdReq Impl)

/-- What defines a core function of the general layout. -/
inductive Src where
  /-- A lower, a resource built-in or an async built-in, read as in the certified layout. -/
  | core (c : CoreR)
  /-- Export `name` of the instance of core module `m` (`0` main, `k + 1` adapter `k`). -/
  | modExport (m : Nat) (name : String)
  /-- The task-hook wrapper of export `name` of `inst` (`main`, `adapter<k>`). -/
  | hook (inst name : String)
  deriving Repr, DecidableEq

/-- A `canon lift`. -/
structure LiftA where
  core : Src
  async : Bool
  callback : Option Src
  postReturn : Option Src
  deriving Repr, DecidableEq

/-- An export. -/
inductive ExpA where
  | func (l : LiftA)
  | iface (fs : List (String × LiftA))
  deriving Repr, DecidableEq

/-- **A reading of the general layout**: per core module of the plan, its core imports; the
exports; the resource definitions with their destructors. -/
structure ReadingA where
  imports : List (List ((String × String) × Src))
  exports : List (String × ExpA)
  dtors : List (ResRef × Option Src)
  deriving Repr, DecidableEq

/-- A hook wrapper's export name `hook-<inst>-<name>` as `(inst, name)` (`inst` has no `-`). -/
def hookName (n : String) : Option (String × String) :=
  match (n.dropPrefix? "hook-").map (·.toString) with
  | some r => match r.splitOn "-" with
    | i :: rest => if rest.isEmpty then none else some (i, "-".intercalate rest)
    | [] => none
  | none => none

/-- The names of the type imports, by type index (`none` for every other type): the type index
space of `Layout.spaces`, where a type import is `.other`. A world-level resource
(`resource a;` in a world) is such an import. -/
def typeImportNames (x : XComp) : Array (Option String) :=
  x.sections.foldl (fun acc s => match s with
    | .sec (.aliases xs) => xs.foldl (fun acc a => if a.sort == .type then acc.push none else acc) acc
    | .sec (.imports xs) => xs.foldl (fun acc i => match i.desc with
        | .type _ => acc.push (some i.name.name)
        | _ => acc) acc
    | .sec (.exports xs) => xs.foldl (fun acc e => if e.item.sort == .type then acc.push none else acc) acc
    | .sec (.types xs) => xs.foldl (fun acc _ => acc.push none) acc
    | _ => acc) #[]

section
variable (r : RS) (nA : Nat) (tn : Array (Option String))

/-- A resource: `Layout.resRef`, or a world-level resource imported as a type. -/
def resRefA (t : Nat) : Option ResRef :=
  match Layout.resRef r t with
  | some x => some x
  | none => match tn[t]? with
    | some (some n) => some (.imported "" n)
    | _ => none

/-- A core function defined as in the certified layout, world-level resources included. -/
def coreRA (i : Nat) : Option CoreR :=
  match r.cf[i]? with
  | some (.resNew t) => (resRefA r tn t).map .resNew
  | some (.resRep t) => (resRefA r tn t).map .resRep
  | some (.resDrop t) => (resRefA r tn t).map .resDrop
  | _ => Layout.coreR r 1 i

/-- What defines core function `i` (`fuel` bounds the shim indirections followed). -/
def srcR : Nat → Nat → Option Src
  | 0, _ => none
  | fuel + 1, i =>
    match r.cf[i]? with
    | some (.alias inst n) => match r.ci[inst]? with
      | some (.inst m args) =>
        if m ≤ nA then some (.modExport m n)
        else if args.isEmpty then
          -- a slot of the shim: the function the fixup instantiation puts there
          r.ci.toList.findSome? fun c => match c with
            | .inst _ args' =>
              if lookupS "shim" args' == some inst then
                match (lookupS "actual" args').bind (r.ci[·]?) with
                | some (.exps es) => match lookupS n es with
                  | some si => if si.sort == .func then srcR fuel si.idx else none
                  | none => none
                | _ => none
              else none
            | _ => none
        else (hookName n).map fun (i, f) => .hook i f
      | _ => none
    | some _ => (coreRA r tn i).map .core
    | none => none

/-- A lift, its core functions resolved. -/
def liftA (f : Nat) : Option LiftA :=
  match r.ff[f]? with
  | some (.lift cf opts) => do
    let core ← srcR r nA tn 4 cf
    let cb ← match opts.findSome? (fun | .callback c => some c | _ => none) with
      | some c => (srcR r nA tn 4 c).map some
      | none => pure none
    let pr ← match opts.findSome? (fun | .postReturn c => some c | _ => none) with
      | some c => (srcR r nA tn 4 c).map some
      | none => pure none
    pure ⟨core, opts.contains .async, cb, pr⟩
  | _ => none

def expA (si : SortIdx) : Option ExpA :=
  match si.sort with
  | .func => (liftA r nA tn si.idx).map .func
  | .instance => match r.ii[si.idx]? with
    | some (.inst _ args) =>
      let fs := args.filter fun (a : String × SortIdx) => a.2.sort == ItemSort.func
      (fs.mapM fun (a : String × SortIdx) => (liftA r nA tn a.2.idx).map ((a.1, ·))).map .iface
    | _ => none
  | _ => none

/-- The core imports of the instance of core module `m`, resolved. -/
def importsOf (m : Nat) (names : List (String × String)) : Option (List ((String × String) × Src)) := do
  let args ← r.ci.toList.findSome? fun c => match c with
    | .inst m' args => if m' == m then some args else none
    | _ => none
  names.mapM fun (mn, n) => do
    let inst ← lookupS mn args
    let es ← match r.ci[inst]? with
      | some (.exps es) => some es
      | _ => none
    let si ← lookupS n es
    if si.sort != .func then none
    let c ← srcR r nA tn 4 si.idx
    pure ((mn, n), c)

end

/-- **The reading** of a parsed general-layout output: `names` are the function imports of the
main module and of each adapter, in module order. -/
def readA (names : List (List (String × String))) (x : XComp) : Option ReadingA := do
  let r := Layout.spaces x
  let tn := typeImportNames x
  let nA := names.length - 1
  let imports ← (names.zipIdx).mapM fun (ns, m) => importsOf r nA tn m ns
  let exports ← r.exports.toList.mapM fun (n, si) => do pure (n, ← expA r nA tn si)
  let dtors ← (r.tt.toList.zipIdx.filterMap fun (t, i) => match t with
      | .resource d => some (i, d)
      | _ => none).mapM fun (i, d) => do
    let rr ← resRefA r tn i
    let dc ← match d with
      | some c => (srcR r nA tn 4 c).map some
      | none => pure none
    pure (rr, dc)
  pure ⟨imports, exports, dtors⟩

/-! ## The layout the plan describes -/

/-- The function imports of the main module and of each adapter, in module order. -/
def namesOf (p : Plan) : List (List (String × String)) :=
  p.mod.importNames :: p.adapters.map (·.mod.importNames)

/-- A function of the main module (`none`) or of adapter `k`, through its task-hook wrapper when
the plan has one. -/
def fnSrc (p : Plan) (who : Option Nat) (n : String) : Src :=
  let (iname, m) := match who with
    | some k => (s!"adapter{k}", k + 1)
    | none => ("main", 0)
  if p.hooks.any fun f => f.inst == iname && f.name == n then .hook iname n else .modExport m n

def liftOfA (p : Plan) (im : Impl) : LiftA :=
  match im.lift with
  | .sync c pr => ⟨fnSrc p im.by_ c, false, none, pr.map (fnSrc p im.by_)⟩
  | .stackful c => ⟨fnSrc p im.by_ c, true, none, none⟩
  | .callback c cb => ⟨fnSrc p im.by_ c, true, some (fnSrc p im.by_ cb), none⟩

def mainSrc (p : Plan) : MainReq → Src
  | .req r => .core (Layout.reqR p.wf r)
  | .adp a e => .modExport (a + 1) e

def adSrc (p : Plan) : AdReq → Src
  | .req r => .core (Layout.reqR p.wf r)
  | .main n => .modExport 0 n

/-- **The layout the plan describes.** -/
def expectedA (p : Plan) : ReadingA :=
  let world := (p.impls.filter (·.x.sc == .world)).map fun im => (im.x.core, ExpA.func (liftOfA p im))
  let ifs := ((ifaces p.wf).filter (!·.imported)).map fun i =>
    (keyName i.key, ExpA.iface ((p.impls.filter (·.x.sc == .iface i.key)).map fun im =>
      (funcImportName (fname im.x.f), liftOfA p im)))
  ⟨(p.reqs.map fun (n, r, _) => (n, mainSrc p r)) ::
      p.adapters.map (fun a => a.reqs.map fun (n, r, _) => (n, adSrc p r)),
    world ++ ifs,
    p.dtors.map fun (r, d) => (Layout.resOfE p.wf r, d.map (fnSrc p none))⟩

/-- The layout of a parsed output is the one the plan describes. -/
def layoutOkA (p : Plan) (x : XComp) : Bool :=
  readA (namesOf p) x == some (expectedA p)

/-- The layout check of a general-layout output: the bytes parse (`xparse`) to a component whose
reading is the layout the plan describes. -/
def checkA (p : Plan) (b : ByteArray) : Except String Unit :=
  match xparse b with
  | .ok x =>
    if layoutOkA p x then pure ()
    else throw s!"the general layout's reading differs from the plan: read {repr (readA (namesOf p) x)}, expected {repr (expectedA p)}"
  | .error _ => throw "the general layout's output does not parse back (xparse)"

/-- **`wasm-jco new --adapt` (and the general layout) with the layout checked**:
`Adapt.newAdapt`'s bytes, refused unless they also parse to a component whose reading is the
layout the plan describes (`newAdaptL_layout`). -/
def newAdaptL (core : ByteArray) (wit : Option ((String × String) × List (String × String) × String))
    (ads : List (String × ByteArray)) (growRealloc : Bool := false) :
    Except String (ByteArray × List String) := do
  let p ← Adapt.plan core wit ads growRealloc
  let (b, ls) ← Adapt.newAdaptOf p
  checkA p b
  pure (b, ls ++ ["layout: every core import of the main module and the adapters, the lifts and the destructors are those the plan describes (AdaptLayout.newAdaptL_layout)"])

end Silmaril.Wasm.JcoTool.AdaptLayout
