module

public import Silmaril.Wasm.Wac.TargetsT.Defs
public import Silmaril.Wasm.JcoTool.Cm32.Defs

/-!
# `wasm-tools component semver-check` and `targets --semver-compatible`

**`semver-check --prev P --new N`** (wit-component's `semver_check`, wasm-tools 1.262.0):
upstream erases the version of every package, encodes a component of the shape of world `P`
and a component importing a component of world `N`'s type, and validates the instantiation of
the second with the first: the check is that `P`'s component type is a subtype of `N`'s, with
versions erased. Here (`semverCheck`): both worlds' kinds from the WIT package
(`Bridge.decodePkg`, `TargetsT.worldOf`), interface names and ids without their versions
(`eraseVersions`), and the verdict WIT subtyping (`TargetsT.fitsB`, so `Sub` by
`TargetsT.fitsB_iff`).

**`targets --semver-compatible`**: upstream merges each side's imports that differ only by a
semver-compatible version (`merge_world_imports_based_on_semver`) and encodes both worlds with
canonical interface names (`a:b/i@1.2.3` as `a:b/i@1`). Here (`targetsSemver`): every interface
name and id is canonicalized (`Cm32.canonVer`), imports of the same canonical name are merged
keeping the last one (the import order lists older versions first), and the verdict is
`TargetsT.fitsB` on that view. This is an approximation of the merge: upstream picks the
highest version and checks that the merged interfaces are compatible; see
docs/projects/wasm-components.md.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Semver

open Silmaril.Wasm.Wac (Kind Externs)

/-- A name without its version: `a:b/i@1.0.0 ↦ a:b/i`. -/
def eraseVer (s : String) : String := (s.splitOn "@").headD s

/-- A name with its canonical version: `a:b/i@1.2.3 ↦ a:b/i@1`. -/
def canonName (s : String) : String :=
  match s.splitOn "@" with
  | [a, v] => a ++ "@" ++ JcoTool.Cm32.canonVer v
  | _ => s

/-- Rename the interface ids of a kind (instances, components, at the top). -/
def mapIds (f : String → String) : Kind → Kind
  | .inst i es => .inst (i.map f) es
  | .comp i is es => .comp (i.map f) is es
  | .type k => .type (mapIds f k)
  | k => k

/-- Rename the items of a world and their interface ids. -/
def mapNames (f : String → String) (es : Externs) : Externs :=
  es.map fun (n, k) => (f n, mapIds f k)

def eraseVersions (es : Externs) : Externs := mapNames eraseVer es

/-- Keep the last item of each name, in the order of their last occurrences. -/
def lastOfEach (es : Externs) : Externs :=
  (es.reverse.foldl (fun acc (n, k) => if acc.any (·.1 == n) then acc else acc ++ [(n, k)]) []).reverse

def canonical (es : Externs) : Externs := lastOfEach (mapNames canonName es)

/-- The error of a failed check, as upstream's first line, then our misfits. -/
def semverErr (w : String) (mis : List String) : String :=
  ("new world is not semver-compatible with the previous world\n\nCaused by:\n    0: type mismatch for import `" ++
    w ++ "`\n" ++ String.join (mis.map fun m => "       " ++ m ++ "\n")).trimAsciiEnd.toString

/-- The verdict of `semver-check` on the two worlds' items. -/
def semverFits (pi pe ni ne : Externs) : Bool :=
  Wac.TargetsT.fitsB (Wac.TargetsT.promoteEx (eraseVersions pi))
    (Wac.TargetsT.promoteEx (eraseVersions pe)) (eraseVersions ni) (eraseVersions ne)

/-- **`component semver-check`**: world `prev`'s type (versions erased) is a subtype of world
`new`'s, of the WIT package `pb`. -/
def semverCheck (pb : ByteArray) (prev new : String) : Except String Unit := do
  let (q, _) ← Wac.Bridge.decodePkg pb
  let (pi, pe) ← Wac.TargetsT.worldOf q.defs (some prev)
  let (ni, ne) ← Wac.TargetsT.worldOf q.defs (some new)
  if semverFits pi pe ni ne then pure ()
  else throw (semverErr new (Wac.TargetsT.misfits
    (Wac.TargetsT.promoteEx (eraseVersions pi)) (Wac.TargetsT.promoteEx (eraseVersions pe))
    (eraseVersions ni) (eraseVersions ne)))

/-- **`component targets --semver-compatible`**: the component's type is a subtype of the
world's, both with canonical interface names and imports merged by them. -/
def targetsSemver (comp pb : ByteArray) (w : String) : Except String (Bool × List String) := do
  let (p, _) ← Wac.TypeOf.decodeAny comp
  let (q, _) ← Wac.Bridge.decodePkg pb
  let (wi, we) ← Wac.TargetsT.worldOf q.defs (some w)
  let (ci, ce) := (canonical p.imports, canonical p.exports)
  let (wi, we) := (canonical wi, canonical we)
  pure (Wac.TargetsT.fitsB ci ce wi we, Wac.TargetsT.misfits ci ce wi we)

end Silmaril.Wasm.Tools.Component.Semver
