module

public import Silmaril.Wasi.Versions.WitImport.KImport.Defs
public import Silmaril.Wasi.Versions.WitImport.RImport.Defs

@[expose] public section

/-!
# The kernel importer, in steps

`importKD sel cs` is `importK` (`Silmaril.Wasi.Versions.WitImport.KImport`) keeping both results of
`Elab.elaborate`: the package and the dependency interfaces. `kRPkg` is the resolved package of
`importRPkg` (`wit_rpkg%`) on it. `kUniv` is the universe the importer elaborates, and
`envItems` lists the interfaces `Elab.elabEnv` elaborates. The theorems of `KSplit.Thms` split
an evaluation of `importKD` into steps (parsing per file, the validity check, one interface
body per step, the worlds, the binary checks), so that the kernel can check each step in a
separate module.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-- The universe the importer elaborates, from the parsed documents (worlds dropped when
`sel`). -/
def kUniv (sel : Bool) (ds : List Document) : Universe :=
  if sel then (mergeDocs ds).map dropWorlds else mergeDocs ds

/-- Parsing one glued source, as in `importK`. -/
def parseStep (cs : List Char) : Except String Document :=
  match parseCharsK cs with
  | some d => .ok d
  | none => .error "not WIT text this parser accepts"

/-- The importer on glued source characters, with the dependency interfaces. -/
def importKD (sel : Bool) (srcs : List (List Char)) : Except String (Binary.Package × Binary.Env) := do
  let ds ← srcs.mapM parseStep
  let U := kUniv sel ds
  let P ← U.head?.elim (.error "no package") pure
  Elab.elaborate U P.name []

/-- The resolved package (`importRPkg`) the kernel importer gives, if it succeeds. -/
def kRPkg (ver sel : Bool) (srcs : List (List Char)) : Option RPkg :=
  match importKD sel srcs with
  | .ok (B, deps) => some (rtable ver B, envOf B deps)
  | .error _ => none

/-- The interfaces of a universe with their packages, in the order of `Elab.elabEnv`. -/
def envItems (U : Universe) : List (PackageName × Interface) :=
  U.flatMap (fun P => P.items.filterMap fun | .iface I => some (P.name, I) | _ => none)

/-- The step of `Elab.elabEnv` on one interface. -/
def envStep (c : Elab.Ctx) (x : PackageName × Interface) : Except String (Binary.IfaceName × Binary.Interface) :=
  match Elab.elabBody c (.iface ⟨x.1, x.2.name⟩) x.2.items x.2.docs x.2.gates with
  | some b => pure (Elab.ifaceName ⟨x.1, x.2.name⟩, b)
  | none => throw s!"interface `{x.2.name}`: cyclic or undefined types"

/-- The environment `Elab.elabEnv` gives from the interface bodies `bs`. -/
def envOfBodies (xs : List (PackageName × Interface)) (bs : List Binary.Interface) : Binary.Env :=
  List.zipWith (fun x b => (Elab.ifaceName ⟨x.1, x.2.name⟩, b)) xs bs

/-- The dependency interfaces `Elab.elaborate` returns with the package `p`. -/
def depsOf (env : Binary.Env) (p : PackageName) : Binary.Env :=
  env.filter (·.1.pkg != Elab.pkgName p)

end Silmaril.Wasi.Versions.WitImport
