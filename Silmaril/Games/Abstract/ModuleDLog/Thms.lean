module

public import Silmaril.Games.Abstract.ModuleDLog.Defs
import Silmaril.Proofs.Games.Abstract.ModuleDLog.Basic

/-!
# Closing with logged local divergence: theorems

Proofs in `Silmaril.Proofs.Games.Abstract.ModuleDLog`.

* `closeD_le_closeDLog`: `closeDLog` extends `closeD`;
* `closeDLog_nil`: with an empty log (`u = []`), `closeDLog` is `closeDL`;
* `mem_closeDLog_of_ne_div`: off `div`, the behaviours of `closeDLog m LDL` are those of
  `close m`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.Shape

open Silmaril.Games

universe u

variable {sh : Shape.{u}}

/-- `closeDLog` extends `closeD`. -/
theorem closeD_le_closeDLog (m : sh.OpenMod)
    (LDL : sh.self.Op → List (Call (sh.E ⊕ₛ sh.self)) → Prop) : closeD m ≤ closeDLog m LDL :=
  fun _ _ _ _ h => .inl h

/-- **The log-free case is `closeDL`.** -/
theorem closeDLog_nil (m : sh.OpenMod) (LD : sh.self.Op → Prop) :
    closeDLog m (fun z u => u = [] ∧ LD z) = closeDL m LD :=
  Silmaril.Proofs.Games.Abstract.ModuleDLog.closeDLog_nil m LD

/-- **`closeDLog` keeps the finite behaviours of `close`**: off `div`, they agree. -/
theorem mem_closeDLog_of_ne_div {m : sh.OpenMod}
    {LDL : sh.self.Op → List (Call (sh.E ⊕ₛ sh.self)) → Prop} {f : sh.F} {s : sh.S}
    {a : sh.A f} {y : CallBeh sh.E sh.S (sh.B f)} (hy : y.2 ≠ .div) :
    y ∈ closeDLog m LDL f s a ↔ y ∈ close m f s a :=
  Silmaril.Proofs.Games.Abstract.ModuleDLog.mem_closeDLog_of_ne_div hy

end Silmaril.Games.Abstract.Shape
