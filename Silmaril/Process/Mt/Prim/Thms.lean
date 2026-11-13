module

public import Silmaril.Process.Mt.Prim.Defs
import Silmaril.Proofs.Process.Mt.Prim

/-!
# Standard primitives: the executable ones meet their specifications

PROVED (standard axioms; proofs in `Silmaril.Proofs.Process.Mt.Prim`): `execTable_sound`,
whenever the executable primitive (`execTable`) returns, the standard table has the primitive
and the result is an outcome of its specification, inside its precondition.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Prim

open Silmaril.X86 (Word)

theorem execTable_sound {γ : Type} {p t : Nat} {args : List Word} {sh sh2 : Sh γ} {w : Word}
    (h : execTable p t args sh = some (w, sh2)) :
    ∃ sp, (table : PrimTable γ) p = some sp ∧ sp.pre t args sh ∧ sp.post t args sh w sh2 :=
  Silmaril.Proofs.Process.Mt.Prim.execTable_sound h

end Silmaril.Process.Mt.Prim
