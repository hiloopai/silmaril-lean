module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.Defs

/-!
# Round 7: `HostModsSub` is strictly weaker than `HostExportParam` (round 5, pass 3)

Round 5's `Round7.HostMods.stepValidREM_holds` replaces `HostExportParam` with `HostModsSub`.
`HostModsSub` follows from `HostFinite` and `HostExportParam`
(`Round7.HostMods.hostModsSub_of_param`). This topic shows that the converse fails, even for
hosts that are finite, `HostOk` and export-blind.

The witness is `cloneHost`. A call either diverges or returns the calling store with one of its own
function instances appended again (a clone), and the result `trap`. The clone may be any
`Clonable` instance. That is an instance whose module exports nothing, or one for which no instance
with the same stripped form (`stripFI`) exports nothing. So whenever two instances differ only in
their module's exports and one of them exports nothing, only the export-free one may be cloned.

* It invents no module (`HostModsSub`): the clone's module is one of the store's.
* It is `HostOk`. A clone of a valid instance is valid in the larger store, and appending is a
  store extension.
* It is export-blind (`HostExportBlind`). Stripping a clonable instance gives a clonable instance
  of the stripped store, and every instance of the stripped store has a clonable preimage.
* It is not export-parametric. Take a store with two instances that differ only in their module's
  exports, `[]` against `[e]`. Swap the two modules. That is an export-only rewriting, and the
  clone of the export-free instance becomes a clone that is not allowed.

Clonability reads export lists only through "is empty", so `cloneHost` reads exports. But
stripping the calling store strips its outcomes exactly.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict

open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **`fi` may be cloned from `s`**: it is an instance of `s`, and its module exports nothing,
or no instance of `s` with the same stripped form exports nothing. -/
def Clonable (s : Store H) (fi : FuncInst H) : Prop :=
  fi ∈ s.funcs ∧
    (fi.module.exports = [] ∨ ∀ fi' ∈ s.funcs, stripFI fi' = stripFI fi → fi'.module.exports ≠ [])

/-- `s` with `fi` appended to its function instances. -/
def cloneStore (s : Store H) (fi : FuncInst H) : Store H := { s with funcs := s.funcs ++ [fi] }

/-- **The cloning host**: a call diverges, or appends a clonable instance of the calling store
again and returns `trap`. -/
def cloneHost : HostSemantics H := fun _ s _ o =>
  o = .diverged ∨ ∃ fi, Clonable s fi ∧ o = .returned (cloneStore s fi) .trap

end Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict
