module

public import Silmaril.Wasm.Tools.Component.WitFast.Defs

/-!
# `component wit --importize[-world]` and `--exportize[-world]`

wit-parser's `Resolve::importize` (`exportize`) renames the world (`W-importized`, or the
`--…-out-world-name`), moves it to the end of its package's worlds, keeps of its imports only
the types (all imports are kept by `exportize`, less those a filter keeps as imports), turns its
exports into imports (its imports into exports), and elaborates the world again, which adds the
interfaces the new items depend on.

Here the same is done on the **source** of the world, before the verified elaborator runs
(`importizeWorld`, `exportizeWorld`, `transformPackage`), so the elaboration that adds the
dependencies is the verified one (`WitFast.encodeDocsFast`, equal to `Tool.encodeDocs`). A world
with `include` is refused (its included items would have to move too). Exports named like a kept
type fail as upstream (`world export `x` conflicts with import of same name`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Ize

open Silmaril.Wasm.Wit

/-- The key of a world import or export, as the filter of `--exportize-import` matches it: a
named item's name, an interface's name. -/
def externName : Extern → String
  | .func n _ => n
  | .iface n _ => n
  | .path (.local n) => n
  | .path (.foreign _ n) => n

/-- The names of a world's types (`type` definitions and `use`d names). -/
def typeNames (items : List WorldItem) : List String :=
  items.flatMap fun
    | .type d => [d.name]
    | .use u => u.names.map fun n => n.as.getD n.name
    | _ => []

def noInclude (w : World) : Except String Unit :=
  if w.items.any (fun | .include _ => true | _ => false) then
    throw s!"world `{w.name}` includes other worlds: --importize/--exportize of it is not implemented by this wasm-tools"
  else pure ()

/-- **`Resolve::importize`** on a world's source. -/
def importizeWorld (w : World) (out : Option String) : Except String World := do
  noInclude w
  let kept := w.items.filter fun
    | .type _ | .use _ => true
    | _ => false
  let exps := w.items.filterMap fun
    | .export e => some e
    | _ => none
  for e in exps do
    match e.ext with
    | .func n _ | .iface n _ =>
      if (typeNames kept).contains n then
        throw s!"failed to move world exports to imports\n\nCaused by:\n    0: world export `{n}` conflicts with import of same name"
    | _ => pure ()
  pure { w with name := out.getD (w.name ++ "-importized"), items := kept ++ exps.map .import }

/-- **`Resolve::exportize`** on a world's source: the imports whose names are in `names` (all
when `names` is empty) become exports; the exports are dropped. -/
def exportizeWorld (w : World) (out : Option String) (names : List String) : Except String World := do
  noInclude w
  let moves (e : WorldExtern) : Bool := names.isEmpty || names.contains (externName e.ext)
  let keep := w.items.filterMap fun
    | .import e => if moves e then none else some (.import e)
    | .export _ => none
    | it => some it
  let exps := w.items.filterMap fun
    | .import e => if moves e then some (.export e) else none
    | _ => none
  pure { w with name := out.getD (w.name ++ "-exportized"), items := keep ++ exps }

/-- Apply `f` to the world `wname` of a package and move it to the end of the package's items
(`rename_world`'s `shift_remove` and `insert`). -/
def findWorld (P : Package) (wname : String) : Except String World :=
  match P.items.findSome? (fun | .world w => if w.name == wname then some w else none | _ => none) with
  | some w => pure w
  | none => throw s!"World `{wname}` not found in package"

def transformPackage (P : Package) (wname : String) (f : World → Except String World) :
    Except String Package := do
  let w ← findWorld P wname
  let w' ← f w
  let rest := P.items.filter fun
    | .world v => v.name != wname
    | _ => true
  pure { P with items := rest ++ [.world w'] }

/-- The package binary of the source files (`main`, `deps`) with the main package's world
transformed (`transformPackage`), elaborated and encoded by the verified pipeline. -/
def encodeTransformed (main : List (String × String)) (deps : List (List (String × String)))
    (fs : List String) (wname : String) (f : World → Except String World) :
    Except String ByteArray := do
  let d ← Wac.WitDir.parseFiles main
  let ds ← deps.mapM Wac.WitDir.parseFiles
  let P ← transformPackage d.main wname f
  WitFast.encodeDocsFast { d with main := P } ds fs

end Silmaril.Wasm.Tools.Component.Ize
