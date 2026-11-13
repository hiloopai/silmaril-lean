module

public import Silmaril.Wasm.Component.Lime1Ref.Defs
public import Silmaril.Proofs.Wasm.Component.Lime1Ref.Spec

/-!
# The reference-machine half for the Lime1 engine: theorems

All proved; proofs in `Silmaril.Proofs.Wasm.Component.Lime1Ref`. The statements are in `Defs`.

* `lime1G_emb`: the Lime1 game engine runs `ofCoreL` of the IR module's Core syntax;
* `RefToSpec.on`: the unrestricted half gives the half on every domain;
* `refToSpecOn_of_specE`: for every engine, the machine half against its own specification
  (`RefToSpecEOn`) and the engine-run half (`SpecSubOn`) give the half on a domain;
* `returned_core`, `diverges_core`: **a returned, trapping or diverging run of the Lime1 engine
  from an invocation is a Core 3.0 behaviour of the image store** at `Profile.spec`;
* `Simple.sound_lime1_of`: soundness of the IR over `modSem Profile.spec` for the reference
  machine over the Lime1 engine, on the Lime1 domain, from `RefToSpecLime1`.

The engine-run half and its combination with the machine half are in
`Silmaril.Wasm.Component.Lime1Bridge` (`specSub_of_instBridgeE`, `refToSpec_lime1_of_E`).

Open: `RefToSpecELime1` (see `docs/projects/wasm-components.md`, "Port: lime1ref").

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps Diverges)

theorem lime1G_emb (m : NumModule) : Lime1G.lime1G.emb m = ofCoreL m.mod := rfl

/-- The reference-machine half gives the half on every domain. -/
theorem RefToSpec.on {E : Engine} [∀ a b, Decidable (E.ExternSub a b)]
    {ofCore : Silmaril.Wasm.Module → E.Module} {P : Profile} (h : RefToSpec E ofCore P)
    (D : Simple → Prop) : RefToSpecOn E ofCore P D :=
  fun prof c _ hc hf hi ha => h prof c hc hf hi ha

/-- **The reduction**: the machine half against the engine's own specification and the
engine-run half give the reference-machine half on a domain. -/
theorem refToSpecOn_of_specE {E : Engine} [∀ a b, Decidable (E.ExternSub a b)]
    {ofCore : Silmaril.Wasm.Module → E.Module} {emb : NumModule → E.Module} {P : Profile}
    {D : Simple → Prop} (hR : RefToSpecEOn E ofCore emb D) (hS : SpecSubOn E emb P D) :
    RefToSpecOn E ofCore P D :=
  Silmaril.Proofs.Wasm.Component.Lime1Ref.refToSpecOn_of_specE hR hS

/-- **A returned or trapping Lime1 engine run of an invocation is a Core 3.0 behaviour of the
image store.** -/
theorem returned_core {s : Silmaril.Wasm.Models.V10.LStore Nat}
    (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s) {a : Silmaril.Wasm.Execution.Runtime.FuncAddr}
    (ha : a.value < s.funcs.length) (xs : List Silmaril.Wasm.Execution.Runtime.Value)
    {s' : Silmaril.Wasm.Models.V10.LStore Nat} {t' : lime1.Thread Nat}
    (run : Steps lime1 (s, lime1.invoke a xs) (s', t'))
    {r : Silmaril.Wasm.Component.Engine.CallResult} (hst : lime1.status s' t' = .returned r) :
    ((Silmaril.Wasm.Component.Engine.Lime1.toResult r).toBehaviour).map
        Silmaril.Wasm.Execution.Runtime.Value.toCore ∈
      Silmaril.Wasm.Execution.Core.behaviours Profile.spec
        Silmaril.Wasm.SingleThreaded.Det.noHost s.toCore a.value
        (xs.map Silmaril.Wasm.Execution.Runtime.Value.toCore) :=
  Silmaril.Proofs.Wasm.Component.Lime1Ref.returned_core hwf ha xs run hst

/-- **A diverging Lime1 engine run of an invocation is a Core 3.0 divergence of the image
store.** -/
theorem diverges_core {s : Silmaril.Wasm.Models.V10.LStore Nat}
    (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s) {a : Silmaril.Wasm.Execution.Runtime.FuncAddr}
    (ha : a.value < s.funcs.length) (xs : List Silmaril.Wasm.Execution.Runtime.Value)
    (hd : Diverges lime1 (s, lime1.invoke a xs)) :
    Silmaril.Wasm.Behaviour.diverges ∈
      Silmaril.Wasm.Execution.Core.behaviours Profile.spec
        Silmaril.Wasm.SingleThreaded.Det.noHost s.toCore a.value
        (xs.map Silmaril.Wasm.Execution.Runtime.Value.toCore) :=
  Silmaril.Proofs.Wasm.Component.Lime1Ref.diverges_core hwf ha xs hd

/-- **Soundness of the IR for the reference machine over the Lime1 engine**, on the Lime1
domain, from `RefToSpecLime1`. -/
theorem Simple.sound_lime1_of (hT : RefToSpecLime1)
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hD : Lime1Dom c) (hc : c.Good)
    (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE lime1) () (c.toRef.map ofCoreL) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem Profile.spec))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  specToIR Profile.spec c hc j vs b
    (hT prof c hD hc hf hi ha _ (List.getElem_mem j.isLt) vs hvs hb)

end Silmaril.Wasm.Component.Lime1Ref
