module

public import Silmaril.Wasm.Tools.Component.Cmd.Defs

/-!
# `component wit --merge-world-imports-based-on-semver WORLD`

wit-parser's `Resolve::merge_world_imports_based_on_semver` (`crates/wit-parser/src/resolve/mod.rs`
of wasm-tools 1.262.0) on a world:

1. **Tracks.** Every import of the elaborated world that is an interface of a versioned package
   is on a *semver track*: its package with the version replaced by
   `PackageName::version_compat_track` (`M.0.0` for `M ≠ 0`, `0.m.0` for `m ≠ 0`, else the
   version; a pre-release version is its own track), and the interface's name. Going through the
   imports in order, each track keeps its greatest version (`semver` order); every other version
   met is *replaced* by the track's greatest (`replacements`).
2. **Imports.** The replaced imports keyed by their interface are removed from the world.
3. **Dependencies.** In every remaining import and every export (and the world's own `use`s), a
   `use` of a replaced interface is redirected to its replacement
   (`update_interface_deps_of_world_item`). This changes the interfaces themselves, so the
   printed packages show it.
4. Every world is elaborated again.

Here steps 2 and 3 are done on the **source** (`mergeDocs`), and the verified elaborator does
step 4 (`WitFast.encodeDocsFast`), as `Ize` does for `--importize`. Step 1 reads the world the
verified elaborator produced (`Tool.decode`). Not done: `merge_world_item`'s check that a
replacement has every item of the replaced interface (wasm-tools 1.262.0 accepts the corpus's
`invalid-semver` case anyway), imports that come from an `include` (they stay), and the
labeled imports with `implements` (kept as upstream keeps them, since only interface-keyed
imports are removed).

Theorems: `Silmaril.Wasm.Tools.Component.SemverMerge.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.SemverMerge

open Silmaril.Wasm.Wit

/-! ## Versions -/

/-- A pre-release identifier precedes another (`semver`: numeric ones numerically and before
alphanumeric ones, alphanumeric ones in ASCII order). -/
def identLt (a b : String) : Bool :=
  match a.toNat?, b.toNat? with
  | some x, some y => x < y
  | some _, none => true
  | none, some _ => false
  | none, none => decide (a < b)

/-- Lexicographic order of pre-release identifier lists (a prefix comes first). -/
def preListLt : List String → List String → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => identLt a b || (a == b && preListLt as bs)

/-- `semver` precedence: `major.minor.patch`, then a pre-release before none, then the
pre-release identifiers. -/
def versionLt (a b : Version) : Bool :=
  if a.major ≠ b.major then a.major < b.major
  else if a.minor ≠ b.minor then a.minor < b.minor
  else if a.patch ≠ b.patch then a.patch < b.patch
  else match a.pre, b.pre with
    | [], [] => false
    | [], _ :: _ => false
    | _ :: _, [] => true
    | p, q => preListLt p q

/-- `PackageName::version_compat_track` (build metadata dropped). -/
def compatTrack (v : Version) : Version :=
  let v := { v with build := [] }
  if !v.pre.isEmpty then v
  else if v.major ≠ 0 then { v with minor := 0, patch := 0 }
  else if v.minor ≠ 0 then { v with patch := 0 }
  else v

/-! ## Tracks -/

/-- An interface of a source package: its package and name. -/
structure Id where
  pkg : PackageName
  name : Name
  deriving Repr, DecidableEq, Inhabited

/-- The semver track of an interface of a versioned package. -/
def track (i : Id) : Option (Name × Name × Version × Name) :=
  i.pkg.version.map fun v => (i.pkg.ns, i.pkg.name, compatTrack v, i.name)

/-- The interface-keyed imports of an elaborated world with versioned packages, as source ids. -/
def importIds (pkgs : List PackageName) (w : Binary.World) : List Id :=
  w.imports.filterMap fun
    | .ifaceRef i _ _ =>
      (pkgs.find? (fun p => Elab.pkgName p == i.pkg)).map fun p => ⟨p, i.name⟩
    | _ => none

/-- Step 1: going through the imports in order, the greatest version of each track (`tops`)
and the interfaces met that are not their track's greatest (`removed`). -/
def tracks : List Id → List ((Name × Name × Version × Name) × Id) → List Id →
    List ((Name × Name × Version × Name) × Id) × List Id
  | [], tops, removed => (tops, removed)
  | i :: is, tops, removed =>
    match track i with
    | none => tracks is tops removed
    | some t =>
      match tops.lookup t with
      | none => tracks is (tops ++ [(t, i)]) removed
      | some j =>
        match i.pkg.version, j.pkg.version with
        | some vi, some vj =>
          if versionLt vj vi then
            tracks is (tops.map fun (t', k) => if t' == t then (t', i) else (t', k)) (removed ++ [j])
          else if versionLt vi vj then tracks is tops (removed ++ [i])
          else tracks is tops removed
        | _, _ => tracks is tops removed

/-- **The replacements**: every removed interface and its track's greatest. -/
def replacements (is : List Id) : List (Id × Id) :=
  let (tops, removed) := tracks is [] []
  removed.filterMap fun i => (track i).bind fun t => (tops.lookup t).map (i, ·)

/-! ## The source transformation -/

/-- The interface a source path names, in package `cur`. -/
def pathId (cur : PackageName) : UsePath → Id
  | .local n => ⟨cur, n⟩
  | .foreign p n => ⟨p, n⟩

/-- A `use` redirected to the replacement of its interface. -/
def fixUse (rp : List (Id × Id)) (cur : PackageName) (u : Use) : Use :=
  match rp.lookup (pathId cur u.path) with
  | some j => { u with path := .foreign j.pkg j.name }
  | none => u

def fixIfaceItems (rp : List (Id × Id)) (cur : PackageName) (items : List IfaceItem) :
    List IfaceItem :=
  items.map fun
    | .use u => .use (fixUse rp cur u)
    | it => it

/-- Redirect the `use`s of the interfaces in `keep` (step 3). -/
def fixPackage (rp : List (Id × Id)) (keep : List Id) (P : Package) : Package :=
  { P with items := P.items.map fun
      | .iface i =>
        if keep.contains ⟨P.name, i.name⟩ then .iface { i with items := fixIfaceItems rp P.name i.items }
        else .iface i
      | it => it }

/-- Is a world item an interface-keyed import of a replaced interface? -/
def removedImport (rp : List (Id × Id)) (cur : PackageName) : WorldItem → Bool
  | .import ⟨.path p, _, _⟩ => (rp.lookup (pathId cur p)).isSome
  | _ => false

/-- **The world transformed** (steps 2 and 3 on its own items): replaced imports removed, the
`use`s of the world and of its inline interfaces redirected. -/
def mergeWorld (rp : List (Id × Id)) (cur : PackageName) (w : World) : World :=
  { w with items := (w.items.filter fun it => !removedImport rp cur it).map fun
      | .use u => .use (fixUse rp cur u)
      | .import e => match e.ext with
        | .iface n items => .import { e with ext := .iface n (fixIfaceItems rp cur items) }
        | _ => .import e
      | .export e => match e.ext with
        | .iface n items => .export { e with ext := .iface n (fixIfaceItems rp cur items) }
        | _ => .export e
      | it => it }

/-! ## Imports kept by re-elaboration

`elaborate_world` works on the world's elaborated imports: an import stays even when nothing
needs it any more (world `b` of `merge-semver-update-all-worlds.wit` keeps `a:b/foo@0.1.0`
next to the `a:b/foo@0.1.1` its redirected dependency adds). Elaborating the source again would
drop such imports, so every interface import the elaborated world has and its source does not
write is written explicitly (`explicitImports`), before the source item that comes next in the
elaborated order; the replaced imports of the merged world are not (they are removed). -/

/-- What identifies a world item across source and elaborated form. -/
inductive Key where
  | iface (i : Id)
  | name (n : String)
  deriving DecidableEq

def srcKeys (cur : PackageName) : WorldItem → List Key
  | .import ⟨.path p, _, _⟩ => [.iface (pathId cur p)]
  | .import ⟨.func n _, _, _⟩ => [.name n]
  | .import ⟨.iface n _, _, _⟩ => [.name n]
  | .type d => [.name d.name]
  | .use u => u.names.map fun n => .name n.bound
  | _ => []

def elabKey (pkgs : List PackageName) : Binary.WorldItem → Option Key
  | .ifaceRef i _ _ =>
    (pkgs.find? (fun p => Elab.pkgName p == i.pkg)).map fun p => .iface ⟨p, i.name⟩
  | .ifaceInline n _ => some (.name n)
  | .func f => some (.name f.name)
  | .type t => some (.name t.name)

/-- The world's source with the interface imports of its elaborated form (`ew`) written
explicitly, except those in `drop`. -/
def explicitImports (pkgs : List PackageName) (cur : PackageName) (drop : List Id)
    (ew : Binary.World) (w : World) : World :=
  let srcAll := w.items.flatMap (srcKeys cur)
  let keys := ew.imports.map (elabKey pkgs)
  -- (synthesized id, the key of the source item it goes before, if any)
  let synth : List (Id × Option Key) := (keys.zipIdx).filterMap fun (k, idx) =>
    match k with
    | some (.iface i) =>
      if srcAll.contains (.iface i) || drop.contains i then none
      else some (i, (keys.drop (idx + 1)).findSome? fun k' =>
        match k' with
        | some k' => if srcAll.contains k' then some k' else none
        | none => none)
    | _ => none
  let mk (i : Id) : WorldItem := .import ⟨.path (.foreign i.pkg i.name), {}, []⟩
  let before (it : WorldItem) : List WorldItem :=
    (synth.filter fun (_, a) => match a with
      | some a => (srcKeys cur it).contains a
      | none => false).map (mk ·.1)
  let placed := w.items.flatMap fun it => before it ++ [it]
  -- an anchor can name several source items (a `use` binding several names): keep the first
  let placed := placed.foldl (fun acc it => match it with
    | .import ⟨.path (.foreign p n), _, _⟩ =>
      if acc.contains it && (synth.any fun (i, _) => i == ⟨p, n⟩) then acc else acc ++ [it]
    | it => acc ++ [it]) []
  let rest := (synth.filter fun (_, a) => a.isNone).map (mk ·.1)
  { w with items := placed ++ rest }

/-- The source packages of the main document, of its nested packages and of the dependencies. -/
def allPackages (d : Document) (ds : List Document) : List PackageName :=
  (d.packages ++ ds.flatMap (·.packages)).map (·.name)

/-- The kept interfaces of the elaborated world: its interface imports that are not replaced,
and its interface exports. -/
def keptIds (pkgs : List PackageName) (rp : List (Id × Id)) (w : Binary.World) : List Id :=
  let ids (l : List Binary.WorldItem) : List Id := l.filterMap fun
    | .ifaceRef i _ _ =>
      (pkgs.find? (fun p => Elab.pkgName p == i.pkg)).map fun p => ⟨p, i.name⟩
    | _ => none
  (ids w.imports).filter (fun i => (rp.lookup i).isNone) ++ ids w.exports

/-- **The documents transformed** for the world `wname` of the main package, whose elaborated
form is `ew` (steps 1 to 3); `ews` are the elaborated worlds of the main package, whose implicit
interface imports are written explicitly (`explicitImports`). -/
def mergeDocs (d : Document) (ds : List Document) (wname : String) (ew : Binary.World)
    (ews : List (String × Binary.World)) : Except String (Document × List Document) := do
  let pkgs := allPackages d ds
  let rp := replacements (importIds pkgs ew)
  let keep := keptIds pkgs rp ew
  let w ← Ize.findWorld d.main wname
  let main := fixPackage rp keep d.main
  let ewOf (n : String) : Option Binary.World := ews.lookup n
  let main := { main with items := main.items.map fun
    | .world v =>
      if v.name == wname then
        .world (mergeWorld rp d.main.name (explicitImports pkgs d.main.name (rp.map (·.1)) ew w))
      else match ewOf v.name with
        | some e => .world (explicitImports pkgs d.main.name [] e v)
        | none => .world v
    | it => it }
  pure ({ main, nested := d.nested.map (fixPackage rp keep) },
    ds.map fun e => { main := fixPackage rp keep e.main, nested := e.nested.map (fixPackage rp keep) })

/-- **`component wit --merge-world-imports-based-on-semver WORLD`** on WIT text: the world
selected and elaborated, its imports merged on the source (`mergeDocs`), the source elaborated
and encoded again. -/
def mergeBytes (main : List (String × String)) (deps : List (List (String × String)))
    (fs : List String) (world : Option String) : Except String ByteArray := do
  let d ← Wac.WitDir.parseFiles main
  let ds ← deps.mapM Wac.WitDir.parseFiles
  let pb ← WitFast.encodeDocsFast d ds fs
  let dec ← Tool.decode pb
  let wname ← Cmd.selectWorld dec.pkg world
  let some ew := dec.pkg.worlds.lookup wname | throw s!"World `{wname}` not found in package"
  let (d', ds') ← mergeDocs d ds wname ew dec.pkg.worlds
  WitFast.encodeDocsFast d' ds' fs

/-! ## The text printed

wit-parser prints every package of the resolve. The package binary of the merged source shows
only the packages its main package still refers to, so a package whose interfaces are all
replaced (`a:b@0.1.0` when every use moved to `a:b@0.1.1`) would disappear. The nested
packages printed are therefore those of the source before the merge (`ns0`), each interface
with its merged body when the merged binary still shows it (its `use`s redirected), else its
body before the merge (it was not changed: only kept interfaces are), then the packages only
the merged binary shows. -/

abbrev Foreign := List (Binary.PackageName × List (String × Binary.Interface))

/-- The nested packages to print (see above). -/
def unionForeign (ns0 ns1 : Foreign) : Foreign :=
  let pick (q : Binary.PackageName) (n : String) (b : Binary.Interface) : Binary.Interface :=
    ((ns1.lookup q).bind (·.lookup n)).getD b
  let extra (q : Binary.PackageName) : List (String × Binary.Interface) :=
    ((ns1.lookup q).getD []).filter fun (n, _) => ((ns0.lookup q).getD []).all (·.1 != n)
  ns0.map (fun (q, ifs) => (q, ifs.map (fun (n, b) => (n, pick q n b)) ++ extra q)) ++
    ns1.filter fun (q, _) => ns0.all (·.1 != q)

/-- A stable topological order: repeatedly the first element, in the given order, all of whose
dependencies (among the elements) are already placed; on a cycle, the first one left. -/
def stableTopo {α : Type} (key : α → String) (deps : α → List String) (xs : List α) : List α :=
  go xs.length [] xs
where
  go : Nat → List α → List α → List α
    | 0, done, rest => done ++ rest
    | k + 1, done, rest =>
      match rest with
      | [] => done
      | r :: rs =>
        let ready (x : α) : Bool := (deps x).all fun n =>
          n == key x || done.any (key · == n) || !xs.any (key · == n)
        match rest.find? ready with
        | some x => go k (done ++ [x]) (rest.filter fun y => key y != key x)
        | none => go k (done ++ [r]) rs

/-- The paths a package's source names. -/
def pathsOf (P : Package) : List UsePath :=
  let ifaceItems (items : List IfaceItem) : List UsePath := items.filterMap fun
    | .use u => some u.path
    | _ => none
  P.items.flatMap fun
    | .iface i => ifaceItems i.items
    | .world w => w.items.flatMap fun
      | .import ⟨.path p, _, _⟩ | .export ⟨.path p, _, _⟩ => [p]
      | .import ⟨.iface _ items, _, _⟩ | .export ⟨.iface _ items, _, _⟩ => ifaceItems items
      | .use u => [u.path]
      | .include i => [i.path]
      | _ => []
    | .use u => [u.path]

def pkgKey (p : PackageName) : String := toString (repr (Elab.pkgName p))

/-- The other packages a package's source refers to. -/
def pkgDeps (P : Package) : List String :=
  (pathsOf P).filterMap fun
    | .foreign q _ => if q == P.name then none else some (pkgKey q)
    | .local _ => none

/-- The interfaces of the same package an interface's source `use`s. -/
def ifaceDeps (P : Package) (i : Interface) : List String :=
  i.items.filterMap fun
    | .use ⟨.local n, _, _⟩ => some n
    | .use ⟨.foreign q n, _, _⟩ => if q == P.name then some n else none
    | _ => none

/-- Every interface of every nested package and dependency of the merged source, each package
elaborated as the main one (`WitFast.elaborateFast`). The packages come in wit-parser's resolve
order, taken from the source **before** the merge (`d0`, `ds0`: the order is fixed when the
source is read): the dependencies, then the nested packages, each group sorted topologically
(`stableTopo`); the interfaces of a package likewise, by their `use`s inside the package. -/
def fullForeign (d0 : Document) (ds0 : List Document) (d : Document) (ds : List Document)
    (fs : List String) : Except String Foreign := do
  let U := Tool.sourceUniverse d ds
  let src0 := ds0.flatMap (·.packages) ++ d0.nested
  let order := stableTopo (fun P => pkgKey P.name) pkgDeps src0
  let srcNew := ds.flatMap (·.packages) ++ d.nested
  order.mapM fun P0 => do
    let (P, _) ← WitFast.elaborateFast U P0.name fs
    let ifs := match srcNew.find? (·.name == P0.name) with
      | some Q =>
        let srcIfs := Q.items.filterMap fun | .iface i => some i | _ => none
        let sorted := stableTopo (·.name) (ifaceDeps Q) srcIfs
        sorted.filterMap fun i => (P.interfaces.lookup i.name).map (i.name, ·)
      | none => P.interfaces
    pure (P.name, ifs)

/-- **`component wit --merge-world-imports-based-on-semver WORLD`** on WIT text: the merged
package binary (for `--wasm`/`--wat`) and the text printed. -/
def mergeOut (main : List (String × String)) (deps : List (List (String × String)))
    (fs : List String) (world : Option String) : Except String (ByteArray × String) := do
  let d ← Wac.WitDir.parseFiles main
  let ds ← deps.mapM Wac.WitDir.parseFiles
  let pb ← WitFast.encodeDocsFast d ds fs
  let dec ← Tool.decode pb
  let wname ← Cmd.selectWorld dec.pkg world
  let some ew := dec.pkg.worlds.lookup wname | throw s!"World `{wname}` not found in package"
  let (d', ds') ← mergeDocs d ds wname ew dec.pkg.worlds
  let b ← WitFast.encodeDocsFast d' ds' fs
  let p1 ← Binary.decodePackage b
  let ns1 ← Binary.decodeForeign b p1.name
  let ns0 ← Binary.decodeForeign pb dec.pkg.name
  let ns := match fullForeign d ds d' ds' fs with
    | .ok ns => ns
    | .error _ => unionForeign ns0 ns1
  pure (b, Binary.printPackageAll p1 ns)

end Silmaril.Wasm.Tools.Component.SemverMerge
