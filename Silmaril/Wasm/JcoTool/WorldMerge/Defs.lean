module

public import Silmaril.Wasm.Wit.Binary.DecodeLax.Defs
public import Silmaril.Wasm.Component.Binary.Lower.Defs
public import Silmaril.Wasm.JcoTool.New.Defs

/-!
# The world of a core module as wit-component computes it: merged, deduplicated, live

`wasm-tools component new` (wit-component) does not use a module's `component-type` custom
section as it is. Real producers write several: a `cargo build --target wasm32-wasip2` module
built by `wit-bindgen` 0.62.0 and Rust 1.99.1 carries five (the crate's world, three worlds of
libstd and one of wasi-libc), naming the WASI interfaces at two versions (`@0.2.0` from
wasi-libc, `@0.2.12` from libstd). wit-component

1. decodes every section and merges the worlds (`Resolve::merge`, `merge_worlds`): the union of
   the imports and of the exports, an interface present twice having the union of its types and
   functions;
2. merges imports by semantic version (`merge_world_imports_based_on_semver`): of two
   interfaces `ns:pkg/i@v` and `ns:pkg/i@w` with compatible versions (equal major version, or
   for `0.x` equal minor version) only the later one is kept, and the core module's imports of
   the earlier one are satisfied by it;
3. keeps only the **live** part of the imports (`ComponentWorld` with `LiveTypes`): the world
   functions and the interface functions the core module imports, the resources whose
   `[resource-drop]` it imports, and the named types (and interfaces) these and the world's
   exports need. Exports are kept whole.

This module computes that world (`liveWorld`) from the decoded sections and the core module's
import names, as a `WorldFull` re-encoded by the WIT binary encoder
(`Silmaril.Wasm.Wit.Binary.encodeWorldType`) and decoded again (`decodeWorldFull`), so `wasm-jco`
runs unchanged on it. It is the tool's reading of wit-component's behaviour and is tested
against it (`tools/wasm-jco/tests/corpus.sh`); no theorem relates it to wit-component.

`coreImportKey` and `compatible` give the semver matching that `NewI.classify` uses to find the
interface of a core import named at an earlier compatible version.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.WorldMerge

open Silmaril.Wasm.Wit.Binary

/-! ## Semantic versions -/

/-- `major.minor.patch` with an optional pre-release or build suffix (kept as text). -/
structure Ver where
  major : Nat
  minor : Nat
  patch : Nat
  pre : String
  deriving Repr, DecidableEq, Inhabited

/-- Parse `a.b.c[-pre][+build]`. -/
def parseVer (s : String) : Option Ver :=
  let core := (s.splitOn "+").headD s
  let (num, pre) := match core.splitOn "-" with
    | n :: rest => (n, "-".intercalate rest)
    | [] => (core, "")
  match num.splitOn "." with
  | [a, b, c] => do pure ⟨← a.toNat?, ← b.toNat?, ← c.toNat?, pre⟩
  | _ => none

/-- The part of a version that semver-compatible versions share: the major version, or for
`0.x` the minor version too, or for `0.0.x` the whole version. A pre-release is only compatible
with itself. -/
def Ver.compatKey (v : Ver) : Nat × Nat × Nat × String :=
  if v.pre ≠ "" then (v.major, v.minor, v.patch, v.pre)
  else if v.major ≠ 0 then (v.major, 0, 0, "")
  else if v.minor ≠ 0 then (0, v.minor, 0, "")
  else (0, 0, v.patch, "")

/-- `v < w` on release versions (lexicographic on the numbers). -/
def Ver.lt (v w : Ver) : Bool :=
  v.major < w.major || (v.major == w.major &&
    (v.minor < w.minor || (v.minor == w.minor && v.patch < w.patch)))

/-- Two interface names that wit-component merges: the same namespace, package and interface,
and compatible versions. -/
def compatible (i j : IfaceName) : Bool :=
  i.pkg.ns == j.pkg.ns && i.pkg.name == j.pkg.name && i.name == j.name &&
  match i.pkg.version, j.pkg.version with
  | none, none => true
  | some a, some b => match parseVer a, parseVer b with
    | some va, some vb => va.compatKey == vb.compatKey
    | _, _ => a == b
  | _, _ => false

/-- Whether `i`'s version is later than `j`'s. -/
def later (i j : IfaceName) : Bool :=
  match i.pkg.version, j.pkg.version with
  | some a, some b => match parseVer a, parseVer b with
    | some va, some vb => vb.lt va
    | _, _ => false
  | _, _ => false

/-- Parse a core import module name `ns:pkg/iface@v` (with an optional `[export]` prefix
removed by the caller). -/
def ifaceOfModule (m : String) : Option IfaceName := parseIfaceName m.toList

/-! ## Renaming interfaces in types, functions and worlds -/

section rename
variable (f : IfaceName → IfaceName)

def Owner.rn : Owner → Owner
  | .local => .local
  | .iface i => .iface (f i)

def TyRef.rn (r : TyRef) : TyRef := ⟨Owner.rn f r.owner, r.name⟩

def Ty.rn : Ty → Ty
  | .prim p => .prim p
  | .ref r => .ref (TyRef.rn f r)
  | .list t => .list (Ty.rn t)
  | .fixedList t n => .fixedList (Ty.rn t) n
  | .map k v => .map (Ty.rn k) (Ty.rn v)
  | .option t => .option (Ty.rn t)
  | .result a b => .result (a.attach.map fun ⟨t, _⟩ => Ty.rn t) (b.attach.map fun ⟨t, _⟩ => Ty.rn t)
  | .tuple ts => .tuple (ts.attach.map fun ⟨t, _⟩ => Ty.rn t)
  | .own r => .own (TyRef.rn f r)
  | .borrow r => .borrow (TyRef.rn f r)
  | .future t => .future (t.attach.map fun ⟨t, _⟩ => Ty.rn t)
  | .stream t => .stream (t.attach.map fun ⟨t, _⟩ => Ty.rn t)

def TyDefKind.rn : TyDefKind → TyDefKind
  | .record fs => .record (fs.map fun l => { l with ty := Ty.rn f l.ty })
  | .variant cs => .variant (cs.map fun l => { l with ty := l.ty.map (Ty.rn f) })
  | .enum cs => .enum cs
  | .flags fs => .flags fs
  | .resource => .resource
  | .type t => .type (Ty.rn f t)

def TypeDef.rn (t : TypeDef) : TypeDef := { t with kind := TyDefKind.rn f t.kind }

def Func.rn (g : Silmaril.Wasm.Wit.Binary.Func) : Silmaril.Wasm.Wit.Binary.Func :=
  { g with params := g.params.map fun (n, t) => (n, Ty.rn f t), result := g.result.map (Ty.rn f) }

def Interface.rn (b : Interface) : Interface :=
  { b with types := b.types.map (TypeDef.rn f), funcs := b.funcs.map (Func.rn f) }

def DItem.rn : DItem → DItem
  | .iface (.inl i) b => .iface (.inl (f i)) (Interface.rn f b)
  | .iface (.inr n) b => .iface (.inr n) (Interface.rn f b)
  | .func g => .func (Func.rn f g)
  | .type t => .type (TypeDef.rn f t)

end rename

/-! ## Merging -/

/-- The key of a world item: interfaces by name, functions and types by name (distinct
namespaces). -/
def itemKey : DItem → String
  | .iface (.inl i) _ => "i:" ++ i.id
  | .iface (.inr n) _ => "n:" ++ n
  | .func g => "f:" ++ g.mangled
  | .type t => "t:" ++ t.name

/-- The union of two interface bodies: the first one's types and functions, then those of the
second one not already present (by name). -/
def ifUnion (a b : Interface) : Interface :=
  { a with
    types := a.types ++ b.types.filter fun t => !a.types.any (·.name == t.name)
    funcs := a.funcs ++ b.funcs.filter fun g => !a.funcs.any (·.mangled == g.mangled) }

/-- Add an item to a list of items, merging an interface present already. -/
def addItem (xs : List DItem) (x : DItem) : List DItem :=
  if xs.any (itemKey · == itemKey x) then
    xs.map fun y => if itemKey y == itemKey x then
      match y, x with
      | .iface k a, .iface _ b => .iface k (ifUnion a b)
      | _, _ => y
    else y
  else xs ++ [x]

/-- The union of item lists, in order of first occurrence. -/
def unionItems (xss : List (List DItem)) : List DItem :=
  xss.foldl (fun acc xs => xs.foldl addItem acc) []

/-- The interface names a list of items mentions as interface items. -/
def ifaceNames (xs : List DItem) : List IfaceName :=
  xs.filterMap fun
    | .iface (.inl i) _ => some i
    | _ => none

/-- The canonical name of an interface among `all`: the latest compatible one. -/
def canon (all : List IfaceName) (i : IfaceName) : IfaceName :=
  all.foldl (fun c j => if compatible c j && later j c then j else c) i

/-! ## Live imports -/

/-- What one core import asks of a scope (the world, or an imported interface). -/
inductive Use where
  /-- A function, by its plain name (`f`, `[method]r.f`, `[static]r.f`, `[constructor]r`). -/
  | fn (name : String)
  /-- `[resource-drop]r`. -/
  | drop (res : String)
  /-- A stream or future built-in `[stream-op-N]f` / `[future-op-N]f`: element `N` of `f`. -/
  | chan (fn : String) (idx : Nat)
  deriving Repr, BEq, Inhabited

/-- What the core imports ask of the world: of `$root`, and per interface module name. -/
structure CoreUse where
  rootUses : List Use
  ifaceUses : List (String × List Use)
  /-- The uses in the order wit-component visits them (its `ImportMap`): per group of import
  names (the main module's, then each adapter's), per module name in order of first
  appearance, the uses in order. -/
  seq : List (String × List Use) := []

/-- The use of a core import name (after the module is known not to be `[export]…`). -/
def useOf (n : String) : Use :=
  let n := (Silmaril.Wasm.JcoTool.New.strip? "[async-lower]" n).getD n
  match Silmaril.Wasm.JcoTool.New.strip? "[resource-drop]" n with
  | some r => .drop r
  | none =>
    let chan := (Silmaril.Wasm.JcoTool.New.strip? "[stream-" n).orElse fun _ =>
      Silmaril.Wasm.JcoTool.New.strip? "[future-" n
    match chan with
    | some r =>
      match r.splitOn "]" with
      | op :: rest =>
        match ((op.splitOn "-").getLast?.bind String.toNat?) with
        | some k => .chan ("]".intercalate rest) k
        | none => .fn n
      | [] => .fn n
    | none => .fn n

/-- The uses of a core module's import names. -/
def coreUses (names : List (String × String)) : CoreUse :=
  let add (us : List (String × List Use)) (m : String) (x : Use) :=
    if us.any (·.1 == m) then us.map fun (k, a) => if k == m then (k, a ++ [x]) else (k, a)
    else us ++ [(m, [x])]
  let u : CoreUse := names.foldl (fun (u : CoreUse) (m, n) =>
    if m == "$root" then { u with rootUses := u.rootUses ++ [useOf n] }
    else if m.startsWith "[export]" then u
    else { u with ifaceUses := add u.ifaceUses m (useOf n) }) (⟨[], [], []⟩ : CoreUse)
  { u with seq := names.foldl (fun us (m, n) =>
      if m.startsWith "[export]" then us else add us m (useOf n)) [] }

/-- The uses of several groups of import names (the main module's, then each adapter's): the
uses of their concatenation, visited group by group. -/
def coreUsesSeq (groups : List (List (String × String))) : CoreUse :=
  { coreUses groups.flatten with seq := groups.flatMap fun g => (coreUses g).seq }

/-- The plain name of a function (async prefixes removed), as core imports name it. -/
def plainFn (g : Silmaril.Wasm.Wit.Binary.Func) : String := { g with async := false }.mangled

/-- Named type references of a type, in order. -/
def tyRefs : Ty → List TyRef
  | .prim _ => []
  | .ref r => [r]
  | .list t => tyRefs t
  | .fixedList t _ => tyRefs t
  | .map k v => tyRefs k ++ tyRefs v
  | .option t => tyRefs t
  | .result a b => (a.attach.map fun ⟨t, _⟩ => tyRefs t).getD [] ++
      (b.attach.map fun ⟨t, _⟩ => tyRefs t).getD []
  | .tuple ts => (ts.attach.map fun ⟨t, _⟩ => tyRefs t).flatten
  | .own r => [r]
  | .borrow r => [r]
  | .future t => (t.attach.map fun ⟨t, _⟩ => tyRefs t).getD []
  | .stream t => (t.attach.map fun ⟨t, _⟩ => tyRefs t).getD []

def kindRefs : TyDefKind → List TyRef
  | .record fs => fs.flatMap (fun l => tyRefs l.ty)
  | .variant cs => cs.flatMap fun l => (l.ty.map tyRefs).getD []
  | .type t => tyRefs t
  | _ => []

def funcRefs (g : Silmaril.Wasm.Wit.Binary.Func) : List TyRef :=
  g.params.flatMap (fun p => tyRefs p.2) ++ (g.result.map tyRefs).getD [] ++
  match g.kind with
  | .method r | .static r | .constructor r => [⟨.local, r⟩]
  | .freestanding => []

/-- A live type: its scope (`none`: the world) and name. -/
abbrev LKey := Option (IfaceName ⊕ String) × String

/-- The state of the liveness closure. -/
structure Live where
  /-- Live types in the order wit-component encodes them: dependencies first (post-order). -/
  types : List LKey := []
  /-- Types visited (the closure is cut at them). -/
  seen : List LKey := []
  ifaces : List (IfaceName ⊕ String) := []
  deriving Inhabited

/-- The body of an interface among the items. -/
def bodyIn (xs : List DItem) (k : IfaceName ⊕ String) : Option Interface :=
  xs.findSome? fun
    | .iface k' b => if k' == k then some b else none
    | _ => none

/-- The kind of a named type among the items. -/
def kindIn (xs : List DItem) : LKey → Option TyDefKind
  | (some k, n) => (bodyIn xs k).bind fun b => (b.types.find? (·.name == n)).map (·.kind)
  | (none, n) => xs.findSome? fun
    | .type t => if t.name == n then some t.kind else none
    | _ => none

/-- The key of a reference occurring in scope `sc`. -/
def refKey (sc : Option (IfaceName ⊕ String)) (r : TyRef) : LKey :=
  match r.owner with
  | .local => (sc, r.name)
  | .iface i => (some (.inl i), r.name)

/-- Mark the references `rs` (occurring in `sc`) and what their types refer to live, `fuel`
bounding the depth. -/
def markRefs (xs : List DItem) : Nat → Live → Option (IfaceName ⊕ String) → List TyRef → Live
  | 0, l, _, _ => l
  | _, l, _, [] => l
  | fuel + 1, l, sc, r :: rs =>
    let k := refKey sc r
    if l.seen.contains k then markRefs xs (fuel + 1) l sc rs
    else
      let l := { l with seen := l.seen ++ [k] }
      let inner := ((kindIn xs k).map kindRefs).getD []
      let l := markRefs xs fuel l k.1 inner
      let l := { l with types := l.types ++ [k],
                        ifaces := match k.1 with
                          | some i => if l.ifaces.contains i then l.ifaces else l.ifaces ++ [i]
                          | none => l.ifaces }
      markRefs xs (fuel + 1) l sc rs
termination_by fuel _ _ rs => (fuel, rs.length)

/-- The filtered imports and exports: for each imported interface the live functions and types,
for the world the live functions and types; exports whole. -/
structure LiveWorld where
  imports : List DItem
  exports : List DItem

/-- The uses of scope `k` (`none`: the world), through any compatible module name. -/
def usesOf (u : CoreUse) : Option (IfaceName ⊕ String) → List Use
  | none => u.rootUses
  | some k => u.ifaceUses.foldl (fun acc (m, xs) =>
    let hit := match k with
      | .inl i => match ifaceOfModule m with
        | some j => j == i || compatible i j
        | none => false
      | .inr n => m == n
    if hit then acc ++ xs else acc) []

/-- The functions of `fs` a list of uses imports. -/
def usedFns (us : List Use) (fs : List Silmaril.Wasm.Wit.Binary.Func) : List Silmaril.Wasm.Wit.Binary.Func :=
  fs.filter fun g => us.contains (.fn (plainFn g))

/-- The roots of the type closure of a scope's uses: the resources dropped, the types of the
functions imported, the element types of the streams and futures whose built-ins are imported
(wit-component's `LiveTypes` over the required functions and intrinsics). -/
def useRefs (us : List Use) (fs : List Silmaril.Wasm.Wit.Binary.Func) : List TyRef :=
  us.flatMap fun
    | .drop r => [⟨.local, r⟩]
    | .fn n => ((fs.find? (plainFn · == n)).map funcRefs).getD []
    | .chan n k => match (fs.find? (plainFn · == n)).bind fun g => (funcChans g)[k]? with
      | some (.stream (some t)) | some (.future (some t)) => tyRefs t
      | _ => []

/-- The references of an exported interface to other interfaces (its own types stay in it). -/
def externalRefs (k : IfaceName ⊕ String) (b : Interface) : List TyRef :=
  (b.funcs.flatMap funcRefs ++ b.types.flatMap (fun t => kindRefs t.kind)).filter fun r =>
    match r.owner with
    | .iface i => (Sum.inl i : IfaceName ⊕ String) != k
    | .local => false

/-- Compute the live world: `xsI` the merged imports, `xsE` the merged exports. World type
imports are kept. -/
def liveOf (u : CoreUse) (xsI xsE : List DItem) : LiveWorld :=
  let fuel := 10000
  let rootFns := xsI.filterMap fun
    | .func g => some g
    | _ => none
  -- as wit-component's `add_live_imports`: the world's types first, then the uses in the
  -- order of `u.seq` (module by module, in order of first appearance)
  let l0 : Live := markRefs xsI fuel {} none (xsI.filterMap fun
    | .type t => some ⟨.local, t.name⟩
    | _ => none)
  let ifaceFor (m : String) : Option ((IfaceName ⊕ String) × Interface) :=
    xsI.findSome? fun
      | .iface k b =>
        let hit := match k with
          | .inl i => match ifaceOfModule m with
            | some j => j == i || compatible i j
            | none => false
          | .inr n => m == n
        if hit then some (k, b) else none
      | _ => none
  let l3 := u.seq.foldl (fun l (m, us) =>
    if m == "$root" then markRefs xsI fuel l none (useRefs us rootFns)
    else match ifaceFor m with
      | some (k, b) =>
        let l := if (usedFns us b.funcs).isEmpty then l else
          { l with ifaces := if l.ifaces.contains k then l.ifaces else l.ifaces ++ [k] }
        markRefs xsI fuel l (some k) (useRefs us b.funcs)
      | none => l) l0
  -- exports: what they refer to outside themselves
  let live := xsE.foldl (fun l x => match x with
    | .iface k b => markRefs xsI fuel l none (externalRefs k b)
    | .func g => markRefs xsI fuel l none (funcRefs g)
    | _ => l) l3
  let imports := xsI.filterMap fun
    | .iface k b =>
      if live.ifaces.contains k then
        some (.iface k { b with
          types := live.types.filterMap fun (sc, n) =>
            if sc == some k then b.types.find? (·.name == n) else none
          funcs := usedFns (usesOf u (some k)) b.funcs })
      else none
    | .func g => if (usesOf u none).contains (.fn (plainFn g)) then some (.func g) else none
    | .type t => some (.type t)
  ⟨imports, xsE⟩

/-- The interfaces an item's body refers to. -/
def depsOf : DItem → List IfaceName
  | .iface _ b => (b.funcs.flatMap funcRefs ++ b.types.flatMap (fun t => kindRefs t.kind)).filterMap fun r =>
      match r.owner with
      | .iface i => some i
      | .local => none
  | .func g => (funcRefs g).filterMap fun r => match r.owner with
      | .iface i => some i
      | .local => none
  | .type t => (kindRefs t.kind).filterMap fun r => match r.owner with
      | .iface i => some i
      | .local => none

/-- Order imports so that every interface comes after the interfaces it refers to (a stable
depth-first insertion, as wit-parser's world elaboration). -/
def topo (xs : List DItem) : List DItem :=
  let rec ins (fuel : Nat) (acc : List DItem) (x : DItem) : List DItem :=
    match fuel with
    | 0 => if acc.any (itemKey · == itemKey x) then acc else acc ++ [x]
    | fuel + 1 =>
      if acc.any (itemKey · == itemKey x) then acc
      else
        let acc := (depsOf x).foldl (fun acc i =>
          match xs.find? (itemKey · == "i:" ++ i.id) with
          | some y => if itemKey y == itemKey x then acc else ins fuel acc y
          | none => acc) acc
        if acc.any (itemKey · == itemKey x) then acc else acc ++ [x]
  xs.foldl (ins 64) []

/-! ## The merged, live world of a core module -/

/-- Decode every `component-type` section of a core module. -/
def sectionWorlds (core : ByteArray) : Except String (List WorldFull) := do
  let cs ← customSections core
  let ps := (cs.filter (·.1.startsWith componentTypeSection)).map (·.2)
  if ps.isEmpty then throw "no component-type custom section"
  ps.mapM decodeWorldFull

/-- Whether two lists of items are the same (by key and, for interfaces, by body). -/
def sameItems (a b : List DItem) : Bool :=
  a.length == b.length && (a.zip b).all fun
    | (.iface k x, .iface k' y) => k == k' && x == y
    | (x, y) => itemKey x == itemKey y

/-- `liveWorld` for several groups of import names (the main module's, then each adapter's), as
wit-component visits them; the imports are merged in the order of `importOrder` (default
`wfs`). -/
def liveWorldSeq (wfs : List WorldFull) (groups : List (List (String × String)))
    (importOrder : Option (List WorldFull) := none) : Except String WorldFull := do
  let some w0 := wfs.head? | throw "no world"
  let allNames := wfs.flatMap fun wf => ifaceNames (wf.imports ++ wf.exports)
  let rn := canon allNames
  let imps := unionItems ((importOrder.getD wfs).map fun wf => wf.imports.map (DItem.rn rn))
  let exps := unionItems (wfs.map fun wf => wf.exports.map (DItem.rn rn))
  let lw := liveOf (coreUsesSeq groups) imps exps
  let imports := topo lw.imports
  if wfs.length == 1 && sameItems imports w0.imports && sameItems lw.exports w0.exports then
    return w0
  -- an interface both imported and exported is one interface of the package, whose body is
  -- the exported (full) one, as wit-component prints it (`import-partial-export-full`)
  -- (its types: the imported, live ones first, then the others, in wit-component's order)
  let fullOf (k : IfaceName ⊕ String) (b : Interface) : Interface :=
    match bodyIn imports k with
    | some ib =>
      let first := ib.types.filterMap fun t => b.types.find? (·.name == t.name)
      { b with types := first ++ b.types.filter fun t => !first.any (·.name == t.name) }
    | none => b
  let env : Env := (lw.exports ++ imports).filterMap fun
    | .iface (.inl i) b => some (i, fullOf (.inl i) b)
    | _ => none
  let w : World := { imports := imports.map DItem.toWorldItem, exports := lw.exports.map DItem.toWorldItem }
  let payload ← encodeWorldType env w0.pkg w0.name w w0.encoding
  let wf ← decodeWorldFull payload
  pure wf

/-- **The world of a core module, as wit-component builds the component's type.** `wfs` are
the decoded worlds (the module's sections, or the world of `--wit`), `names` the core module's
import names. The first world's package and name are kept. If there is one world and every
import is live, the world is returned unchanged (its declarations as written); otherwise the
merged, deduplicated, live world is encoded and decoded again (`liveWorldSeq`). -/
def liveWorld (wfs : List WorldFull) (names : List (String × String)) :
    Except String WorldFull := liveWorldSeq wfs [names]

/-- The import names of a core module (decoded by silmaril's verified decoder). -/
def coreImportNames (core : ByteArray) : Except String (List (String × String)) := do
  let m ← Silmaril.Wasm.Component.Binary.Lower.coreMod core
  pure m.importNames

end Silmaril.Wasm.JcoTool.WorldMerge
