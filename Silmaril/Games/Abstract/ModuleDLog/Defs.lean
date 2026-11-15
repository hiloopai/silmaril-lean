module

public import Silmaril.Games.Abstract.Module.Defs

/-!
# Closing with logged local divergence

`Shape.closeDL m LD` observes local divergence of a call `z` (`LD z`) only *at the start* of
`z`'s function: the import calls are those of the descent path to `z`. A function that first
makes some calls, then diverges within itself (a loop after a host call, say) needs the calls
it makes before diverging. `closeDLog m LDL` takes them as a log: `LDL z u` says the call `z`
diverges within its own function after the open-module calls `u` (imports and internal
calls, each with its answer). The internal calls of `u` are resolved by `close m`
(`Shape.SubstPre`), exactly as the prefix of a descent.

Theorems in `Silmaril.Games.Abstract.ModuleDLog.Thms`: the log-free case is `closeDL`, and off
`div` the behaviours are those of `close m`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.Shape

open Silmaril.Games

universe u

variable {sh : Shape.{u}}

/-- **Closing with logged local divergence.** `closeD m` plus `div` after the import calls of
every finite descent path to a call `z` that diverges within its own function after the
open-module calls `u` (`LDL z u`), those calls resolved by `close m`. -/
def closeDLog (m : sh.OpenMod) (LDL : sh.self.Op → List (Call (sh.E ⊕ₛ sh.self)) → Prop) :
    sh.ClosedMod := fun f s a =>
  closeD m f s a ∪ {y | y.2 = .div ∧ ∃ z qs u q, DescPath m (close m) ⟨f, (a, s)⟩ qs z ∧
    LDL z u ∧ SubstPre (close m) u q ∧ y.1 = qs ++ q}

end Silmaril.Games.Abstract.Shape
