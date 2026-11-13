module

public import Silmaril.Wasm.Resource.Handle.Defs
public import Silmaril.Wasm.Spec.Component.Logic.Defs

@[expose] public section

/-!
# Resource protocols for components

Component Model resources are handles with ownership: `own r` and `borrow r` values
(`Silmaril.Wasm.Spec.Component`, reference values `RVal`, handle representations `r : ℕ`), created by
`resource.new`, dropped by a destructor (`resource.drop`), read by `resource.rep`. This file
presents the component handle logics of `Silmaril.Wasm.Spec.Component.Logic` as protocols and
states the sentence a component **defining** a resource must satisfy.

* `ownedReps vs`: the representations passed `own` in `vs`.
* `nudProto d`: the protocol "no call mentions a representation dropped by an earlier call of the
  destructor `d`" (state: the dropped representations). It presents `noUseAfterDrop d`
  (`nudProto_accepts_iff`, `models_noUseAfterDrop_iff`).
* `compProviderEv new drop`: for a component exporting a resource with constructor `new` and
  destructor `drop`, the return `returns (some [own r])` of `new` is `alloc r`, a call of `drop`
  with `[own r]` is `free r`, any other export call with a single handle argument `use`s it;
  `compProviderSpec`: the provider handle sentence (fresh representations: `new` never returns a
  live representation; uses and drops of dead representations are the client's fault).

A verified component defining a resource satisfies `compProviderSpec new drop` (it hands out
fresh handles) and `borrowScoped` (it never returns a handle it was only lent); its clients are
held to `nudProto drop` (equivalently `noUseAfterDrop drop`) and, on maximal traces, to
`droppedEventually (new, drop)`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component

/-- The representations passed `own` in a list of values. -/
def ownedReps (vs : List RVal) : List ℕ :=
  (valsHandles vs).filterMap fun p => if p.1 then some p.2 else none

/-- One step of `nudProto d`: the state is the list of dropped representations. -/
def nudStep {X : CIface} (d : X.Exp) (D : List ℕ) : CEvent X → Option (List ℕ)
  | .inr (.ask j a) =>
    if (valsReps a).any (· ∈ D) then none else some (if j = d then ownedReps a ++ D else D)
  | _ => some D

/-- **No use after drop, as a protocol.** -/
def nudProto {X : CIface} (d : X.Exp) : Protocol (List ℕ) (CEvent X) := ⟨[], nudStep d⟩

/-- The handle event of a component event (provider orientation). -/
def compProviderEv {X : CIface} (new drop : X.Exp) : CEvent X → HEv ℕ
  | .inr (.ans j (.returns (some [.own r]))) => if j = new then .alloc r else .skip
  | .inr (.ask j [.own r]) => if j = drop then .free r else .use r
  | .inr (.ask _ [.borrow r]) => .use r
  | _ => .skip

/-- **The sentence of a component defining a resource**: fresh representations. -/
def compProviderSpec {X : CIface} (new drop : X.Exp) :
    Protocol (Option (List ℕ)) (CEvent X) :=
  (handleProto ℕ .provider).comap (compProviderEv new drop)

end Silmaril.Wasm.Resource
