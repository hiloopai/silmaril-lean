module

public import Silmaril.Wasm.Resource.MachineTab.Defs
public import Silmaril.Wasm.Spec.Component.RefMulti.Defs

/-!
# Configurations reached by multi-call runs of the reference component machine

`Reached prof h σ0 p m`: `m` is reached by a run of `refMultiSem`'s shape for the reference
program `p`: the root instantiation from the empty store (`instBehaviours`), resolved export
calls (`RunCalls`), and then any machine run without a host-frame program (`HostEvent.run`),
for instance a prefix of a further call, whatever its outcome. These are the configurations at
which the reference machine runs its programs on a component, in particular the stores from
which the borrow programs of `Silmaril.Wasm.Component.FXRes.Borrow` start.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.Reach

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Component.Reference

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- **The configurations reached by multi-call runs** of the reference program `p`. -/
def Reached (prof : ProfileKind) (h : Host E σ) (σ0 : σ) {X : CIface} (p : RefProg E X)
    (m : Config E σ) : Prop :=
  ∃ (m₀ : Config E σ) (inst : InstId) (es : List (String × FuncId)) (ds : List (DoneCall X))
    (mₙ : Config E σ) (tr : List (Label E σ)),
    InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) p.comp p.args ∧
    RunCalls prof h p.names es m₀ 0 ds mₙ ∧ Steps prof h.hr h.dispatch mₙ tr m ∧
    ∀ q, Label.host (.run q) ∉ tr

end Silmaril.Wasm.Component.FXRes.Reach
