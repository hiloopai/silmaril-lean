module

public import Silmaril.Compiler.C.Sem.Runtime.Defs
public import Silmaril.Compiler.Target.RenameCheck.Defs
@[expose] public section

/-!
# Definitions of the renamer targets (frozen)

`TargetsRename.lean` states the renamer targets over `RegAlloc.renumberChecked`, defined with
the checker `checkCert` in `Compile/Target/RenameCheck.lean` (ccomp's checker, ccomp commit
2b7c60839). This file defines what the evaluator measures on the corpus:

* `ccompLir p`: ccomp's linked Lir program for `p`, with ccomp's C library (`ccompMirRt p`
  linked at `mirConfig`, as `checkC0` links it); this is the program ccomp's backend renumbers;
* `renumberCheckedStats p`: the functions of `ccompLir p` whose numbering by `renumber renameK`
  the checker accepts, and all its functions (`(0, 0)` when ccomp does not compile or link
  `p`). `renameK = 7` is ccomp's x86-64 register count (`Backends.lean`).
-/

namespace Silmaril.Compile.C.Sem

open Silmaril.Machine Silmaril.Compile.Target.RegAlloc

/-- The register homes ccomp's x86-64 backend renumbers for. -/
def renameK : Nat := 7

/-- ccomp's linked Lir program for `p`, with its C library. -/
def ccompLir (p : Silmaril.Cerberus.Ail.TypedProgram) : Option (Lir.Prog Nat) :=
  match ccompMirRt p with
  | none => none
  | some us =>
    match Mir.link mirConfig.layout us with
    | .ok l => some l.prog
    | .error _ => none

/-- The functions of ccomp's Lir for `p` that `checkCert renameK` accepts, and all of them. -/
def renumberCheckedStats (p : Silmaril.Cerberus.Ail.TypedProgram) : Nat × Nat :=
  match ccompLir p with
  | none => (0, 0)
  | some q => ((q.funcs.filter (checkFunc renameK)).length, q.funcs.length)

end Silmaril.Compile.C.Sem
