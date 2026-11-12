module

public import Silmaril.Wasm.Component.FXTyped.Defs
public import Silmaril.Wasm.Component.FXRefV.Thms
import Silmaril.Proofs.Wasm.Component.FXTyped.Typed

/-!
# Discharging `SimpleFX.Typed`

`FXRefV.refToSpecFX` proves the machine half for components whose modules carry FX functions,
over the WasmFX engine with suspension `fxEV P`, under the hypothesis `SimpleFX.Typed P c`. This
module discharges that hypothesis on a fragment and states what remains.

**Core exports** (`typedAt_core`). The engine allocates the FX functions after the Core
instance, so a Core export runs in the instance's store *extended* by the FX functions, and
`FXRefE`'s renaming to the `IsInst` store does not apply. The store split of
`Silmaril.Wasm.Game.Linking` (`PartRel`, `reach_link_back`) relates the extended store to the
instance's own store, with the Core instance as the only part; this needs the Core part in the
split fragment (`Linked2.ModSplitOk`: no tags, memories, tables or segments). Then:
a Core thread never calls an FX function (it never reaches a host-call redex), so it is never
turned into an FX thread, and its returned values are typed by Core type soundness at the
instance (`run_typed_at`).

**FX exports** (`arityAt_fx`, `typedAt_fx`). `StepFX'` is untyped. What it does fix is the
**arity**: the rule `invoke` puts an FX function's body in a frame of arity `F.nresults`, the
only steps from a single frame are the frame rules (`stepFX'_frame`), and quiet FX code (values,
traps, exceptions) does not step. So every returned call of an FX export returns exactly as many
values as the export has flat results, whatever FX code runs (`suspend`, `resume`, `switch`,
`cont.bind`, `resume_throw`). With no flat results this is typing.

**The fragment** (`typed_of_frag`, `refToSpecFX_frag`): with `SimpleFX.Frag c` (Core exports
over a split-fragment Core part, FX exports without results), `c.Typed P` holds, and the machine
half holds with no typing hypothesis.

Not covered: FX exports with results. There `Typed` needs the types, not only the arity, of the
returned values, and the model has no validation of FX function bodies (an FX function declared
`[] → [i32]` may return an `i64`; see `Silmaril.Wasm.Component.FXTypedEx`, `bad_not_typed`).

Proofs: `Silmaril.Proofs.Wasm.Component.FXTyped.{Frame,Enter,Arity,CoreSplit,Typed}`.
New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXTyped

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV Silmaril.Wasm.Component.FXRefV
open Silmaril.Wasm.Numerics (Profile)

/-- **`Typed` at a Core export of a Core part in the split fragment.** -/
theorem typedAt_core {P : Profile} {c : FXRefV.SimpleFX} (hi : c.Inst)
    (hsplit : Linked2.ModSplitOk c.core.mod) (hc : c.toSimple.Good) {x : SimpleExport}
    (hx : x ∈ c.exports) (hk : x.core < c.core.exports.length) : SimpleFX.TypedAt P c x :=
  Silmaril.Proofs.Wasm.Component.FXTyped.typedAt_core hi hsplit hc hx hk

/-- **Arity at an FX export**: every returned call returns as many values as the export has
flat results. -/
theorem arityAt_fx {P : Profile} {c : FXRefV.SimpleFX} (hi : c.Inst) (hc : c.toSimple.Good)
    {x : SimpleExport} (hx : x ∈ c.exports) (hk : c.core.exports.length ≤ x.core) :
    SimpleFX.ArityAt P c x :=
  Silmaril.Proofs.Wasm.Component.FXTyped.arityAt_fx hi hc hx hk

/-- **`Typed` at an FX export without flat results.** -/
theorem typedAt_fx {P : Profile} {c : FXRefV.SimpleFX} (hi : c.Inst) (hc : c.toSimple.Good)
    {x : SimpleExport} (hx : x ∈ c.exports) (hk : c.core.exports.length ≤ x.core)
    (h0 : ValTy.flatList x.ty.results = []) : SimpleFX.TypedAt P c x :=
  Silmaril.Proofs.Wasm.Component.FXTyped.typedAt_fx hi hc hx hk h0

/-- **`SimpleFX.Typed` on the typed fragment.** -/
theorem typed_of_frag {P : Profile} {c : FXRefV.SimpleFX} (hi : c.Inst) (hc : c.toSimple.Good)
    (hF : SimpleFX.Frag c) : c.Typed P :=
  Silmaril.Proofs.Wasm.Component.FXTyped.typed_of_frag hi hc hF

/-- **The machine half on the typed fragment, with no typing hypothesis.** -/
theorem refToSpecFX_frag (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : FXRefV.SimpleFX) (hc : c.toSimple.Good) (hf : c.toSimple.FloatFree) (hi : c.Inst)
    (ha : c.toSimple.Arity) (hF : SimpleFX.Frag c) (x : SimpleExport) (hx : x ∈ c.exports)
    (vs : List Silmaril.Wasm.Component.Val) (hvs : ValTy.checkList x.ty.params vs = true) :
    exportBehaviours prof (refHostE (fxEV P)) () (c.toSimple.toRef.map c.ofCore) [] x.name
        (vs.map toRefVal) ⊆
      exportSpecE (fxEV P) c.emb c.toSimple x vs :=
  FXRefV.refToSpecFX P prof c hc hf hi ha (typed_of_frag hi hc hF) x hx vs hvs

/-- **IR soundness over the suspending engine on the typed fragment**, with no typing
hypothesis. -/
theorem sound_fxEV_frag (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : FXRefV.SimpleFX) (hc : c.toSimple.Good) (hf : c.toSimple.FloatFree) (hi : c.Inst)
    (ha : c.toSimple.Arity) (hF : SimpleFX.Frag c) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE (fxEV P)) () (c.toSimple.toRef.map c.ofCore) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toSimple.toComp.exports.length)
      (c.toSimple.toComp.den (engineSem (fxEV P) NumModule c.emb))
      ⟨j, by simp [Simple.toComp, FXRefV.SimpleFX.toSimple]⟩ vs b :=
  FXRefV.SimpleFX.sound_fxEV P prof c hc hf hi ha (typed_of_frag hi hc hF) j vs hvs b hb

/-- info: 'Silmaril.Wasm.Component.FXTyped.refToSpecFX_frag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refToSpecFX_frag

end Silmaril.Wasm.Component.FXTyped
