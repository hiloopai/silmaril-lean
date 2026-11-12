module

public import Silmaril.Wasm.Tools.Gen.API.Defs
public import Silmaril.Wasm.Wit.Valid.Defs

/-!
# A WIT instance of the generator API (`wit-smith`)

The language is a universe of WIT packages (`Silmaril.Wasm.Wit.Universe`, the syntax of
`Silmaril.Wasm.Wit.Syntax`) at a point `F` of the WIT feature flags of `wit-smith` (`WitFeat`:
`--async`, `--futures`, `--streams`, `--error-context`, `--fixed-length-lists`):

* `WitValidIn F U`: `U` is valid (`Silmaril.Wasm.Wit.Valid`: unique valid names, resolution of
  every name, `use`, path and `include`, acyclic `use`, type and `include` graphs) and uses
  only the features of `F` (`Universe.inF`); `witCheck F` decides it (`Thms`: `witCheck_iff`,
  from `Silmaril.Wasm.Wit.check_iff`), so `witLang F` is a `DecLang`;
* `Raw.univ F size`: one package `wit-smith:pkg` of interfaces (records, variants, enums,
  flags, aliases, resources with constructors, methods and static functions, functions, and
  `use` of the types of earlier interfaces) and worlds (imports and exports of interfaces by
  path, of functions and of inline interfaces). Names are distinct by construction and types
  refer only to earlier definitions;
* `Raw.mutate`: add an interface, add a function, drop the last item; `Raw.cands`: drop an item
  of the package or of an interface; `Raw.size`;
* `witGenRun F`, `witMutRun F`, `witShrinker`: what the checked objects compute (the raw output
  when `witCheck F` accepts it, else the empty package `emptyU` or the input).

This module holds only what runs. `Thms`: the verified objects `witLang F`, `witGen F`,
`witMut F` (computing `witGenRun F`, `witMutRun F`; the fallback is proved valid:
`emptyU_valid`), restriction along `F ≤ G`, shrinking.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Wit

open Silmaril.Wasm.Wit

/-! ## Feature flags -/

/-- The WIT feature flags of `wasm-tools wit-smith`. -/
structure WitFeat where
  async : Bool := false
  futures : Bool := false
  streams : Bool := false
  errorContext : Bool := false
  fixedLists : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Inclusion of feature flags. -/
def WitFeat.le (a b : WitFeat) : Prop :=
  (a.async → b.async) ∧ (a.futures → b.futures) ∧ (a.streams → b.streams) ∧
    (a.errorContext → b.errorContext) ∧ (a.fixedLists → b.fixedLists)

/-- Every flag on. -/
def WitFeat.all : WitFeat := ⟨true, true, true, true, true⟩

/-- Union of flags. -/
def WitFeat.or (a b : WitFeat) : WitFeat :=
  ⟨a.async || b.async, a.futures || b.futures, a.streams || b.streams,
    a.errorContext || b.errorContext, a.fixedLists || b.fixedLists⟩

/-- No flag. -/
def WitFeat.none : WitFeat := {}

/-- Inclusion of flags, as a Boolean. -/
def WitFeat.leB (a b : WitFeat) : Bool :=
  (!a.async || b.async) && (!a.futures || b.futures) && (!a.streams || b.streams) &&
    (!a.errorContext || b.errorContext) && (!a.fixedLists || b.fixedLists)

/-- The union of a list of flags. -/
def WitFeat.any (l : List WitFeat) : WitFeat := l.foldr WitFeat.or {}

/-- The flags a type needs. -/
def tyNeeds (t : Ty) : WitFeat :=
  { futures := !Ty.all (fun | .future _ => false | _ => true) t
    streams := !Ty.all (fun | .stream _ => false | _ => true) t
    errorContext := !Ty.all (fun | .errorContext => false | _ => true) t
    fixedLists := !Ty.all (fun | .fixedList _ _ => false | _ => true) t }

/-- The flags an optional type needs. -/
def optNeeds : Option Ty → WitFeat
  | some t => tyNeeds t
  | none => {}

/-- The flags a function type needs. -/
def funcNeeds (f : Func) : WitFeat :=
  WitFeat.any ([{ async := f.async }, optNeeds f.result] ++ f.params.map fun p => tyNeeds p.2)

/-- The flags a type definition needs. -/
def typeDefNeeds (d : TypeDef) : WitFeat :=
  match d.kind with
  | .alias t => tyNeeds t
  | .record fs => WitFeat.any (fs.map fun f => tyNeeds f.ty)
  | .variant cs => WitFeat.any (cs.map fun c => optNeeds c.ty)
  | .enum _ | .flags _ => {}
  | .resource fs => WitFeat.any (fs.map fun f => funcNeeds f.func)

/-- The flags an interface item needs. -/
def ifaceItemNeeds : IfaceItem → WitFeat
  | .type d => typeDefNeeds d
  | .use _ => {}
  | .func f => funcNeeds f.func

/-- The flags a world item needs. -/
def worldItemNeeds : WorldItem → WitFeat
  | .import e | .export e => match e.ext with
    | .func _ f => funcNeeds f
    | .iface _ items => WitFeat.any (items.map ifaceItemNeeds)
    | .path _ => {}
  | .type d => typeDefNeeds d
  | .use _ | .include _ => {}

/-- The flags a package needs. -/
def packageNeeds (P : Package) : WitFeat :=
  WitFeat.any (P.items.map fun
    | .iface I => WitFeat.any (I.items.map ifaceItemNeeds)
    | .world W => WitFeat.any (W.items.map worldItemNeeds)
    | .use _ => {})

/-- The flags a universe needs. -/
def universeNeeds (U : Universe) : WitFeat := WitFeat.any (U.map packageNeeds)

/-- A universe uses only the features of `F`. -/
def universeInF (F : WitFeat) (U : Universe) : Bool := (universeNeeds U).leB F

/-! ## The language -/

/-- **A valid WIT universe at the flags `F`**. -/
def WitValidIn (F : WitFeat) (U : Universe) : Prop := Valid U ∧ universeInF F U = true

/-- Its checker. -/
def witCheck (F : WitFeat) (U : Universe) : Bool := check U && universeInF F U

/-- The package `wit-smith:pkg` with the given items. -/
def pkgName : PackageName := ⟨"wit-smith", "pkg", none⟩

/-- The fallback: one empty package. -/
def emptyU : Universe := [⟨pkgName, [], {}⟩]

/-! ## Raw generation -/

namespace Raw

/-- The primitive types. -/
def prims : List Ty := [.bool, .s8, .s16, .s32, .s64, .u8, .u16, .u32, .u64, .f32, .f64, .char,
  .string]

/-- The scope of a type: named non-resource types and resources visible. -/
structure Scope where
  types : List Name := []
  resources : List Name := []

/-- A type expression over `sc`, of depth at most `n`; `borrow` only when `params`. -/
def ty (F : WitFeat) (sc : Scope) (params : Bool) : Nat → Rand Ty
  | 0 => do
    let named := sc.types.map Ty.named ++ sc.resources.map Ty.named
    Rand.pick (prims ++ named) .u32
  | n + 1 => do
    let sub := ty F sc params n
    let base : List (Rand Ty) :=
      [ ty F sc params 0, do return .list (← sub), do return .option (← sub),
        do return .tuple (← Rand.list (← Rand.range 1 3) sub),
        do
          let ok ← if ← Rand.bool then some <$> sub else pure none
          let er ← if ← Rand.bool then some <$> sub else pure none
          return .result ok er ] ++
      (if sc.resources.isEmpty then [] else
        [do return .own (← Rand.pick sc.resources "")] ++
        (if params then [do return .borrow (← Rand.pick sc.resources "")] else [])) ++
      (if F.fixedLists then [do return .fixedList (← sub) (← Rand.range 1 4)] else []) ++
      (if F.futures then [do
          -- payloads: no handles (wasmparser: "`future` payload cannot contain a `borrow`")
          let t ← ty F {} false n
          return .future (if ← Rand.bool then some t else none)] else []) ++
      (if F.streams then [do
          -- wasmparser refuses `stream<char>`
          let t ← ty F {} false n
          let t := match t with | .char => Ty.u8 | t => t
          return .stream (if ← Rand.bool then some t else none)] else []) ++
      (if F.errorContext then [pure .errorContext] else [])
    (base.getD (← Rand.nat base.length) (ty F sc params 0))

/-- A function type. -/
def func (F : WitFeat) (sc : Scope) : Rand Func := do
  let np ← Rand.nat 4
  let params ← (List.range np).mapM fun i => do return (s!"p{i}", ← ty F sc true 2)
  let result ← if ← Rand.bool then some <$> ty F sc false 2 else pure none
  let async ← if F.async then Rand.chance 1 4 else pure false
  return { params, result, async }

/-- `k` labels with a prefix. -/
def labels (pre : String) (k : Nat) : List Label := (List.range k).map fun i => ⟨s!"{pre}{i}", {}⟩

/-- The `j`th type definition of an interface (name `t{j}`) over `sc`. -/
def typeDef (F : WitFeat) (sc : Scope) (j : Nat) : Rand TypeDef := do
  let name := s!"t{j}"
  let sel ← Rand.nat 6
  let kind : TypeDefKind ←
    if sel = 0 then do
      let t ← ty F sc false 2
      pure (TypeDefKind.alias t)
    else if sel = 1 then do
      let k ← Rand.range 1 4
      let fs ← (List.range k).mapM fun i => do
        let t ← ty F sc false 2
        pure ({ name := s!"f{i}", ty := t } : Field)
      pure (TypeDefKind.record fs)
    else if sel = 2 then do
      let k ← Rand.range 1 4
      let cs ← (List.range k).mapM fun i => do
        let t ← if ← Rand.bool then some <$> ty F sc false 2 else pure none
        pure ({ name := s!"c{i}", ty := t } : Case)
      pure (TypeDefKind.variant cs)
    else if sel = 3 then do
      let k ← Rand.range 1 5
      pure (TypeDefKind.enum (labels "e" k))
    else if sel = 4 then do
      let k ← Rand.range 1 6
      pure (TypeDefKind.flags (labels "g" k))
    else do
      let sc' : Scope := { sc with resources := sc.resources ++ [name] }
      let ctor ← if ← Rand.bool then do
          let f ← func F sc
          pure [({ kind := .ctor, func := { params := f.params } } : ResourceFunc)]
        else pure []
      let nm ← Rand.nat 3
      let ms ← (List.range nm).mapM fun i => do
        let f ← func F sc'
        let k : ResourceFuncKind := if ← Rand.bool then .method s!"m{i}" else .static s!"m{i}"
        pure ({ kind := k, func := f } : ResourceFunc)
      pure (TypeDefKind.resource (ctor ++ ms))
  return { name, kind }

/-- The items of an interface: type definitions `t*`, `use`s `u*` of the earlier interfaces'
types (`exported`: name and the names of its non-resource types), and functions `f*`. The
scope grows as types are defined. -/
def ifaceItems (F : WitFeat) (exported : List (Name × List Name)) (size : Nat) :
    Rand (List IfaceItem × Scope) := do
  let mut sc : Scope := {}
  let mut items : List IfaceItem := []
  -- uses
  let mut u := 0
  for (iname, ts) in exported do
    if !ts.isEmpty && (← Rand.chance 1 3) then
      let t ← Rand.pick ts ""
      let b := s!"u{u}"
      u := u + 1
      items := items ++ [.use ⟨.local iname, [⟨t, some b⟩], []⟩]
      sc := { sc with types := sc.types ++ [b] }
  -- types
  let nt ← Rand.nat (1 + min 4 size)
  for j in List.range nt do
    let d ← typeDef F sc j
    items := items ++ [.type d]
    match d.kind with
    | .resource _ => sc := { sc with resources := sc.resources ++ [d.name] }
    | _ => sc := { sc with types := sc.types ++ [d.name] }
  -- functions
  let nf ← Rand.nat (1 + min 4 size)
  for j in List.range nf do
    items := items ++ [.func ⟨s!"f{j}", ← func F sc, {}, []⟩]
  return (items, sc)

/-- The local interfaces an interface's items `use`. -/
def usesOf (items : List IfaceItem) : List Name :=
  items.filterMap fun
    | .use ⟨.local i, _, _⟩ => some i
    | _ => none

/-- The interfaces `i` depends on through `use`, transitively (`deps` lists earlier
interfaces first, so one pass over it in reverse order closes the relation). -/
def depsClosure (deps : List (Name × List Name)) (i : Name) : List Name :=
  let direct := (deps.find? (·.1 == i)).map (·.2) |>.getD []
  (deps.reverse.foldl (fun acc (j, ds) => if acc.contains j then acc ++ ds else acc) direct)

/-- A world `w{k}` over the interfaces `ifaces` (by name, with their `use` dependencies). An
interface is imported, exported or left out; the dependencies of an exported interface are
imported by it implicitly, so they are never exported (wit-parser: "an interface is both
imported and exported by the dependencies of an export"). -/
def world (F : WitFeat) (ifaces : List (Name × List Name)) (k : Nat) (size : Nat) :
    Rand World := do
  let mut items : List WorldItem := []
  let mut choice : List (Name × Nat) := []
  for (i, _) in ifaces do
    choice := choice ++ [(i, ← Rand.nat 3)]
  let exported := (choice.filter (·.2 == 1)).map (·.1)
  let implicit := exported.flatMap (depsClosure ifaces)
  for (i, c) in choice do
    let c := if c == 1 && implicit.contains i then 0 else c
    match c with
    | 0 => items := items ++ [.import ⟨.path (.local i), {}, []⟩]
    | 1 => items := items ++ [.export ⟨.path (.local i), {}, []⟩]
    | _ => pure ()
  let nf ← Rand.nat (1 + min 3 size)
  for j in List.range nf do
    let f ← func F {}
    let e : WorldExtern := ⟨.func s!"x{j}" f, {}, []⟩
    items := items ++ [if ← Rand.bool then .import e else .export e]
  if ← Rand.chance 1 3 then
    let (its, _) ← ifaceItems F [] 2
    let e : WorldExtern := ⟨.iface s!"inline{k}" its, {}, []⟩
    items := items ++ [if ← Rand.bool then .import e else .export e]
  return ⟨s!"w{k}", items, {}, []⟩

/-- The non-resource types an interface's items define. -/
def plainTypes (items : List IfaceItem) : List Name :=
  items.filterMap fun
    | .type d => match d.kind with
      | .resource _ => none
      | _ => some d.name
    | _ => none

/-- **A raw universe**: one package of interfaces `i*` and worlds `w*`. -/
def univ (F : WitFeat) (size : Nat) : Rand Universe := do
  let ni ← Rand.range 1 (1 + min 4 (size / 4))
  let mut ifaces : List Interface := []
  let mut exported : List (Name × List Name) := []
  for k in List.range ni do
    let (items, _) ← ifaceItems F exported (size / 4)
    let name := s!"i{k}"
    ifaces := ifaces ++ [⟨name, items, {}, []⟩]
    exported := exported ++ [(name, plainTypes items)]
  let nw ← Rand.nat 3
  let deps := ifaces.map fun I => (I.name, usesOf I.items)
  let worlds ← (List.range nw).mapM fun k => world F deps k (size / 4)
  return [⟨pkgName, ifaces.map PackageItem.iface ++ worlds.map PackageItem.world, {}⟩]

/-- The number of items, nested ones included. -/
def size (U : Universe) : Nat :=
  (U.map fun P => P.items.length + (P.items.map fun
    | .iface I => I.items.length
    | .world W => W.items.length
    | .use _ => 0).sum).sum

/-- Drop the `i`th element. -/
def dropAt {α : Type} (l : List α) (i : Nat) : List α := l.eraseIdx i

/-- **Shrink candidates**: drop a package item, or an item of an interface or world. -/
def cands (U : Universe) : List Universe :=
  match U with
  | [P] =>
    ((List.range P.items.length).map fun i => [{ P with items := dropAt P.items i }]) ++
    (List.range P.items.length).flatMap fun i =>
      match P.items.getD i (.use ⟨.local "", none, []⟩) with
      | .iface I => (List.range I.items.length).map fun j =>
          [{ P with items := P.items.set i (.iface { I with items := dropAt I.items j }) }]
      | .world W => (List.range W.items.length).map fun j =>
          [{ P with items := P.items.set i (.world { W with items := dropAt W.items j }) }]
      | .use _ => []
  | _ => []

/-- **Raw mutation**: add a function to an interface, add an interface, or drop an item. -/
def mutate (F : WitFeat) (r : Rng) (U : Universe) : Universe := Rand.run (do
  match U with
  | [P] =>
    match ← Rand.nat 3 with
    | 0 =>
      -- a new function in an interface (named past the existing ones)
      let is := (List.range P.items.length).filter fun i =>
        match P.items.getD i (.use ⟨.local "", none, []⟩) with | .iface _ => true | _ => false
      if is.isEmpty then return U
      let i ← Rand.pick is 0
      match P.items.getD i (.use ⟨.local "", none, []⟩) with
      | .iface I =>
        let f ← func F {}
        let it : IfaceItem := .func ⟨s!"mut{I.items.length}", f, {}, []⟩
        return [{ P with items := P.items.set i (.iface { I with items := I.items ++ [it] }) }]
      | _ => return U
    | 1 =>
      let (items, _) ← ifaceItems F [] 2
      let name := s!"mut-i{P.items.length}"
      return [{ P with items := P.items ++ [.iface ⟨name, items, {}, []⟩] }]
    | _ =>
      let cs := cands U
      if cs.isEmpty then return U
      return cs.getD (← Rand.nat cs.length) U
  | _ => return U) r

end Raw

/-- **The WIT generator** of the flags `F`, checked (fallback: the empty package); `Thms`:
`witGen`, `witGen_run_eq`. -/
def witGenRun (F : WitFeat) : Rng → Nat → Universe :=
  Generator.guardedRun (witCheck F) (fun r n => Rand.run (Raw.univ F n) r) emptyU

/-- **The WIT mutator**, checked; `Thms`: `witMut`, `witMut_run_eq`. -/
def witMutRun (F : WitFeat) : Rng → Universe → Universe :=
  Mutator.guardedRun (witCheck F) (Raw.mutate F)

/-- The WIT shrinker. -/
def witShrinker : Shrinker Universe := ⟨Raw.size, Raw.cands⟩

end Silmaril.Wasm.Tools.Gen.Wit
