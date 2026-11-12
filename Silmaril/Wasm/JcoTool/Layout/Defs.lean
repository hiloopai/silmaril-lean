module

public import Silmaril.Wasm.JcoTool.Helpers.Defs
public import Silmaril.Wasm.JcoTool.XParse.Defs

/-!
# A component-level reading of `wasm-jco`'s outputs, and the layout the world describes

`xparse` reads the bytes of an output back as the emitted component, section by section; it
does not say what the sections *mean*. This module reads a parsed output (`XComp`) at the
component level, by its index spaces, and compares the reading with what the world and the plan
describe:

* **The reading** (`read`): the component's top-level index spaces (core functions, core
  instances, core modules, functions, instances, types, components), filled section by section
  as the Component Model's binary format defines them (imports, aliases, `canon` definitions,
  instantiations, type definitions and exports each add to their sort's index space). From
  them, the reading resolves:
  * every **export**: a function export to its `canon lift` (`LiftR`: the core export of the main
    instance it lifts, async or not, the callback and the post-return by their core export
    names); an instance export to the component instantiated for it and, for each function
    argument, the lift it is given;
  * every **core import of the main module** (the instance of core module `0`), through the
    inline instance given for its module name, to what defines that core function (`CoreR`):
    a `canon lower` of a top-level function — itself resolved to a world import or to a
    function of an imported instance —, sync or async; a resource built-in of a resource —
    resolved to a resource of an imported instance or to a resource defined for an exported
    interface (the type argument `import-type-r` of its shim component) —; an async built-in by
    its kind; or a core export of the main instance. A core function that is an export of the
    `shim` instance is followed through the `fixup` instantiation (`actual`) to the function
    that fills the slot.
  * every **resource definition**: its destructor, resolved in the same way.
* **The layout the world describes** (`expected p`, for a `NewI` plan): the world functions
  exported in order, each lifted from the core export the plan chose (`Lift`); then one instance
  export per exported interface, named by its key, whose functions are lifted the same way; and
  for each core import of the module, in order, the request the plan classified it as
  (`IReq`): the lower of that world or interface function, the built-in of that kind, the
  resource built-in of that resource.

`layoutOk p x` is `read x = some (expected p)`. `ToolV.newFullL` runs `newFullV` and, for worlds
outside an earlier fragment (interfaces, named types, resources), checks the layout of what the
output's bytes parse to; `Layout.Thms` states it at the entry point. The type indices of
lifts and built-ins are not part of the reading (the validator and the world comparison of
the tests check them).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Layout

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.JcoTool.NewI (Iface IReq XFn ifaces keyName fname funcImportName)
open Silmaril.Wasm.Wit.Binary (WorldFull)

/-! ## Readings -/

/-- A top-level function: a world import, or a function of an imported instance. -/
inductive FnRef where
  | world (name : String)
  | iface (inst name : String)
  deriving Repr, DecidableEq

/-- A resource: of an imported instance, or defined for an exported interface. -/
inductive ResRef where
  | imported (inst name : String)
  | exported (iface name : String)
  deriving Repr, DecidableEq

/-- What defines a core function. -/
inductive CoreR where
  | lower (f : FnRef) (async : Bool)
  | resNew (r : ResRef)
  | resRep (r : ResRef)
  | resDrop (r : ResRef)
  | builtin (kind : String)
  | mainExport (name : String)
  deriving Repr, DecidableEq

/-- A `canon lift`. -/
structure LiftR where
  core : String
  async : Bool
  callback : Option String
  postReturn : Option String
  deriving Repr, DecidableEq

/-- An export. -/
inductive ExpR where
  | func (l : LiftR)
  | iface (fs : List (String × LiftR))
  deriving Repr, DecidableEq

/-- **A reading**: the exports, the core imports of the main module, the resource definitions
(with their destructors). -/
structure Reading where
  exports : List (String × ExpR)
  imports : List ((String × String) × CoreR)
  dtors : List (ResRef × Option CoreR)
  deriving Repr, DecidableEq

/-- The kind of a built-in (type indices and memory options left out). -/
def bkind : Builtin → String
  | .taskReturn _ _ => "task.return"
  | .taskCancel => "task.cancel"
  | .backpressureInc => "backpressure.inc"
  | .backpressureDec => "backpressure.dec"
  | .contextGet i => s!"context.get {i}"
  | .contextSet i => s!"context.set {i}"
  | .threadYield _ => "thread.yield"
  | .subtaskDrop => "subtask.drop"
  | .subtaskCancel _ => "subtask.cancel"
  | .streamNew _ => "stream.new"
  | .streamRead _ o => if o.contains .async then "stream.read async" else "stream.read"
  | .streamWrite _ o => if o.contains .async then "stream.write async" else "stream.write"
  | .streamCancelRead _ a => if a then "stream.cancel-read async" else "stream.cancel-read"
  | .streamCancelWrite _ a => if a then "stream.cancel-write async" else "stream.cancel-write"
  | .streamDropReadable _ => "stream.drop-readable"
  | .streamDropWritable _ => "stream.drop-writable"
  | .futureNew _ => "future.new"
  | .futureRead _ o => if o.contains .async then "future.read async" else "future.read"
  | .futureWrite _ o => if o.contains .async then "future.write async" else "future.write"
  | .futureCancelRead _ a => if a then "future.cancel-read async" else "future.cancel-read"
  | .futureCancelWrite _ a => if a then "future.cancel-write async" else "future.cancel-write"
  | .futureDropReadable _ => "future.drop-readable"
  | .futureDropWritable _ => "future.drop-writable"
  | .waitableSetNew => "waitable-set.new"
  | .waitableSetWait _ _ => "waitable-set.wait"
  | .waitableSetPoll _ _ => "waitable-set.poll"
  | .waitableSetDrop => "waitable-set.drop"
  | .waitableJoin => "waitable.join"
  | .errorContextNew _ => "error-context.new"
  | .errorContextDebugMessage _ => "error-context.debug-message"
  | .errorContextDrop => "error-context.drop"

/-! ## Index spaces -/

/-- A core function. -/
inductive CF where
  | lower (f : Nat) (opts : List CanonOpt)
  | resNew (t : Nat)
  | resRep (t : Nat)
  | resDrop (t : Nat)
  | builtin (b : Builtin)
  | alias (inst : Nat) (name : String)
  deriving Inhabited

/-- A core instance. -/
inductive CI where
  | inst (m : Nat) (args : List (String × Nat))
  | exps (es : List (String × CoreSortIdx))
  | other
  deriving Inhabited

/-- A function. -/
inductive FF where
  | imp (name : String)
  | alias (inst : Nat) (name : String)
  | lift (cf : Nat) (opts : List CanonOpt)
  | other
  deriving Inhabited

/-- An instance. -/
inductive II where
  | imp (name : String)
  | inst (comp : Nat) (args : List (String × SortIdx))
  | other
  deriving Inhabited

/-- A type. -/
inductive TT where
  | alias (inst : Nat) (name : String)
  | resource (dtor : Option Nat)
  | other
  deriving Inhabited

/-- The index spaces read so far. -/
structure RS where
  cf : Array CF := #[]
  ci : Array CI := #[]
  ff : Array FF := #[]
  ii : Array II := #[]
  tt : Array TT := #[]
  exports : Array (String × SortIdx) := #[]

def alias1 (r : RS) (a : Alias) : RS :=
  match a.sort, a.target with
  | .core .func, .coreExport i n => { r with cf := r.cf.push (.alias i n) }
  | .func, .export i n => { r with ff := r.ff.push (.alias i n) }
  | .func, _ => { r with ff := r.ff.push .other }
  | .type, .export i n => { r with tt := r.tt.push (.alias i n) }
  | .type, _ => { r with tt := r.tt.push .other }
  | .instance, _ => { r with ii := r.ii.push .other }
  | .core .instance, _ => { r with ci := r.ci.push .other }
  | _, _ => r

def canon1 (r : RS) : XCanon → RS
  | .canon (.lift cf opts _) => { r with ff := r.ff.push (.lift cf opts) }
  | .canon (.lower f opts) => { r with cf := r.cf.push (.lower f opts) }
  | .canon (.resourceNew t) => { r with cf := r.cf.push (.resNew t) }
  | .canon (.resourceRep t) => { r with cf := r.cf.push (.resRep t) }
  | .canon (.resourceDrop t) => { r with cf := r.cf.push (.resDrop t) }
  | .builtin b => { r with cf := r.cf.push (.builtin b) }

def import1 (r : RS) (i : Import) : RS :=
  match i.desc with
  | .func _ => { r with ff := r.ff.push (.imp i.name.name) }
  | .instance _ => { r with ii := r.ii.push (.imp i.name.name) }
  | .type _ => { r with tt := r.tt.push .other }
  | _ => r

def export1 (r : RS) (e : Export) : RS :=
  let r := { r with exports := r.exports.push (e.name.name, e.item) }
  match e.item.sort with
  | .func => { r with ff := r.ff.push .other }
  | .instance => { r with ii := r.ii.push .other }
  | .type => { r with tt := r.tt.push .other }
  | _ => r

def type1 (r : RS) : DefType → RS
  | .resource _ d => { r with tt := r.tt.push (.resource d) }
  | _ => { r with tt := r.tt.push .other }

/-- One section. -/
def sec1 (r : RS) : XSec → RS
  | .canons xs => xs.foldl canon1 r
  | .sec (.coreInstances xs) => xs.foldl (fun r x => match x with
      | .instantiate m args => { r with ci := r.ci.push (.inst m args) }
      | .exports es => { r with ci := r.ci.push (.exps es) }) r
  | .sec (.instances xs) => xs.foldl (fun r x => match x with
      | .instantiate c args => { r with ii := r.ii.push (.inst c args) }
      | .exports _ => { r with ii := r.ii.push .other }) r
  | .sec (.aliases xs) => xs.foldl alias1 r
  | .sec (.types xs) => xs.foldl type1 r
  | .sec (.imports xs) => xs.foldl import1 r
  | .sec (.exports xs) => xs.foldl export1 r
  | .sec _ => r

/-- The index spaces of a parsed component. -/
def spaces (x : XComp) : RS := x.sections.foldl sec1 {}

/-! ## Resolution -/

section
variable (r : RS)

/-- The main instance: the instance of core module `0`. -/
def mainInst : Option Nat := (r.ci.toList.zipIdx.find? fun (c, _) => match c with
  | .inst 0 _ => true
  | _ => false).map (·.2)

def lookupS {α : Type} (n : String) (xs : List (String × α)) : Option α := (xs.find? (·.1 == n)).map (·.2)

def fnRef (f : Nat) : Option FnRef :=
  match r.ff[f]? with
  | some (.imp n) => some (.world n)
  | some (.alias i n) => match r.ii[i]? with
    | some (.imp k) => some (.iface k n)
    | _ => none
  | _ => none

/-- The exported interface whose shim component takes type `t` as `import-type-n`. -/
def exportedRes (t : Nat) : Option ResRef :=
  r.exports.toList.findSome? fun (k, si) => match si.sort, r.ii[si.idx]? with
    | .instance, some (.inst _ args) => args.findSome? fun (an, ai) =>
        if ai.sort == .type && ai.idx == t then
          (an.dropPrefix? "import-type-").map fun s => .exported k s.toString
        else none
    | _, _ => none

def resRef (t : Nat) : Option ResRef :=
  match r.tt[t]? with
  | some (.alias i n) => match r.ii[i]? with
    | some (.imp k) => some (.imported k n)
    | _ => none
  | some (.resource _) => exportedRes r t
  | _ => none

/-- What defines core function `i` (`fuel` bounds the shim indirections followed). -/
def coreR : Nat → Nat → Option CoreR
  | 0, _ => none
  | fuel + 1, i =>
    match r.cf[i]? with
    | some (.lower f opts) => (fnRef r f).map fun fr => .lower fr (opts.contains .async)
    | some (.resNew t) => (resRef r t).map .resNew
    | some (.resRep t) => (resRef r t).map .resRep
    | some (.resDrop t) => (resRef r t).map .resDrop
    | some (.builtin b) => some (.builtin (bkind b))
    | some (.alias inst n) => match r.ci[inst]? with
      | some (.inst 0 _) => some (.mainExport n)
      | some (.inst _ []) =>
        -- a slot of the shim: the function the fixup instantiation puts there
        r.ci.toList.findSome? fun c => match c with
          | .inst _ args =>
            if lookupS "shim" args == some inst then
              match (lookupS "actual" args).bind (r.ci[·]?) with
              | some (.exps es) => match lookupS n es with
                | some si => if si.sort == .func then coreR fuel si.idx else none
                | none => none
              | _ => none
            else none
          | _ => none
      | _ => none
    | none => none

/-- The core export name a core function aliases from the main instance. -/
def mainName (i : Nat) : Option String :=
  match r.cf[i]?, mainInst r with
  | some (.alias inst n), some m => if inst == m then some n else none
  | _, _ => none

def liftR (f : Nat) : Option LiftR :=
  match r.ff[f]? with
  | some (.lift cf opts) => do
    let core ← mainName r cf
    let cb ← match opts.findSome? (fun | .callback c => some c | _ => none) with
      | some c => (mainName r c).map some
      | none => pure none
    let pr ← match opts.findSome? (fun | .postReturn c => some c | _ => none) with
      | some c => (mainName r c).map some
      | none => pure none
    pure ⟨core, opts.contains .async, cb, pr⟩
  | _ => none

def expR (si : SortIdx) : Option ExpR :=
  match si.sort with
  | .func => (liftR r si.idx).map .func
  | .instance => match r.ii[si.idx]? with
    | some (.inst _ args) =>
      let fs := args.filter fun (a : String × SortIdx) => a.2.sort == ItemSort.func
      (fs.mapM fun (a : String × SortIdx) => (liftR r a.2.idx).map ((a.1, ·))).map .iface
    | _ => none
  | _ => none

end

/-- **The reading** of a parsed output: exports, the main module's core imports (`names`, from
the module), resources defined with their destructors. -/
def read (names : List (String × String)) (x : XComp) : Option Reading := do
  let r := spaces x
  let m ← mainInst r
  let args ← match r.ci[m]? with
    | some (.inst _ args) => some args
    | _ => none
  let imports ← names.mapM fun (mn, n) => do
    let inst ← lookupS mn args
    let es ← match r.ci[inst]? with
      | some (.exps es) => some es
      | _ => none
    let si ← lookupS n es
    let c ← coreR r 4 si.idx
    pure ((mn, n), c)
  let exports ← r.exports.toList.mapM fun (n, si) => do pure (n, ← expR r si)
  let dtors ← (r.tt.toList.zipIdx.filterMap fun (t, i) => match t with
      | .resource d => some (i, d)
      | _ => none).mapM fun (i, d) => do
    let rr ← resRef r i
    let dc ← match d with
      | some c => (coreR r 4 c).map some
      | none => pure none
    pure (rr, dc)
  pure ⟨exports, imports, dtors⟩

/-! ## The layout the world describes -/

def liftOf : New.Lift → LiftR
  | .sync c pr => ⟨c, false, none, pr⟩
  | .stackful c => ⟨c, true, none, none⟩
  | .callback c cb => ⟨c, true, some cb, none⟩

def fnOf : Silmaril.Wasm.JcoTool.Scope → Silmaril.Wasm.Wit.Binary.Func → FnRef
  | .world, f => .world (fname f)
  | .iface k, f => .iface (keyName k) (fname f)

def resOf (wf : WorldFull) : Silmaril.Wasm.JcoTool.Scope × String → ResRef
  | (.iface k, n) =>
    if (ifaces wf).any (fun i => i.key == k && i.imported) then .imported (keyName k) n
    else .exported (keyName k) n
  | (.world, n) => .imported "" n

/-- A resource the component defines (`resource.new`/`rep`, a destructor, the drop an exported
interface requests): an interface's resource is the exported one even when the interface is
also imported. -/
def resOfE (wf : WorldFull) : Silmaril.Wasm.JcoTool.Scope × String → ResRef
  | (.iface k, n) => .exported (keyName k) n
  | r => resOf wf r

/-- The kind a general built-in request asks for. -/
def genKind : New.Req → String
  | .errorContextNew _ => "error-context.new"
  | .errorContextDebugMessage _ => "error-context.debug-message"
  | .errorContextDrop => "error-context.drop"
  | .taskReturn _ => "task.return"
  | .taskCancel => "task.cancel"
  | .backpressureInc => "backpressure.inc"
  | .backpressureDec => "backpressure.dec"
  | .contextGet i => s!"context.get {i}"
  | .contextSet i => s!"context.set {i}"
  | .threadYield => "thread.yield"
  | .subtaskDrop => "subtask.drop"
  | .subtaskCancel => "subtask.cancel"
  | .waitableSetNew => "waitable-set.new"
  | .waitableSetWait => "waitable-set.wait"
  | .waitableSetPoll => "waitable-set.poll"
  | .waitableSetDrop => "waitable-set.drop"
  | .waitableJoin => "waitable.join"
  | .chan _ _ _ _ | .lower _ _ | .lowerAsync _ _ => ""

def chanKind (op : New.ChanOp) (async : Bool) (c : Silmaril.Wasm.JcoTool.Chan) : String :=
  let base := match c with
    | .stream _ => "stream."
    | .future _ => "future."
  let o := match op with
    | .new => "new" | .read => "read" | .write => "write" | .cancelRead => "cancel-read"
    | .cancelWrite => "cancel-write" | .dropReadable => "drop-readable" | .dropWritable => "drop-writable"
  let a := match op with
    | .read | .write | .cancelRead | .cancelWrite => if async then " async" else ""
    | _ => ""
  base ++ o ++ a

/-- What a planned request is, at the component level. -/
def reqR (wf : WorldFull) : IReq → CoreR
  | .lower _ sc f async => .lower (fnOf sc f) async
  | .taskReturn _ _ => .builtin "task.return"
  | .resNew r => .resNew (resOfE wf r)
  | .resRep r => .resRep (resOfE wf r)
  | .resDrop r ex => .resDrop (if ex then resOfE wf r else resOf wf r)
  | .chan op async _ c _ => .builtin (chanKind op async c)
  | .gen r => .builtin (genKind r)

/-- **The layout the world describes**, for a `NewI` plan. -/
def expected (p : NewI.Plan) : Reading :=
  let pairs := p.fns.zip p.lifts
  let world := (pairs.filter (·.1.sc == .world)).map fun (x, l) => (x.core, ExpR.func (liftOf l))
  let ifs := ((ifaces p.wf).filter (!·.imported)).map fun i =>
    (keyName i.key, ExpR.iface ((pairs.filter (·.1.sc == .iface i.key)).map fun (x, l) =>
      (funcImportName (fname x.f), liftOf l)))
  ⟨world ++ ifs, p.reqs.map fun (n, r) => (n, reqR p.wf r),
    p.dtors.map fun (r, d) => (resOfE p.wf r, d.map .mainExport)⟩

/-- The layout of a parsed output is the one the plan describes. -/
def layoutOk (p : NewI.Plan) (x : XComp) : Bool :=
  read (p.mod.importNames) x == some (expected p)

end Silmaril.Wasm.JcoTool.Layout

namespace Silmaril.Wasm.JcoTool.ToolV

open Silmaril.Wasm.JcoTool.Layout

/-- The layout check of an output: for worlds outside an earlier fragment, the bytes parse
(`xparse`) to a component whose reading is the layout the plan describes. -/
def checkLayout (core : ByteArray) (wf : Silmaril.Wasm.Wit.Binary.WorldFull) (o : Tool.Out) :
    Except String Unit :=
  if ToolI.inOld wf.world then pure ()
  else match NewI.plan core wf, xparse o.bytes with
    | .ok p, .ok x =>
      if layoutOk p x then pure ()
      else throw s!"the emitted component's layout differs from the world's: read {repr (read p.mod.importNames x)}, expected {repr (expected p)}"
    | _, _ => throw "the emitted component does not parse back"

/-- **`wasm-jco new`** with the helper modules and the layout checked. -/
def newFullL (core : ByteArray) (wf : Silmaril.Wasm.Wit.Binary.WorldFull) : Except String Tool.Out := do
  let o ← newFullV core wf
  checkLayout core wf o
  pure { o with summary := o.summary ++ (if ToolI.inOld wf.world then [] else
    ["layout: the component's exports, lifts, lowers, resource built-ins and shim indirections are those the world describes (Layout.newFullL_correct)"]) }

end Silmaril.Wasm.JcoTool.ToolV
