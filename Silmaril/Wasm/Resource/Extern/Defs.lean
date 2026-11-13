module

public import Silmaril.Wasm.Resource.Handle.Defs
public import Silmaril.Wasm.Resource.Link.Defs
public import Silmaril.Wasm.Game.Untyped.Defs

@[expose] public section

/-!
# Handle protocols for `externref` handles

Reference-typed interfaces are outside the scalar game (`Silmaril.Wasm.Game.Strategy`); their game is
the untyped one of `Silmaril.Wasm.Game.Untyped` (moves carry raw Core values and the store,
store-relative typing). Handles are opaque references such as `ref.extern a`, compared only for
equality (`Val` equality), exactly as `i32` handles.

* `uClientEv ha hu hf`: on the moves of `UImp ↠ untypedSig ι`, the answer `values [h]` to a call
  of host code `ha` is `alloc h`, a call of host code `hu` (`hf`) with arguments `[h]` is `use h`
  (`free h`);
* `uProviderEv ja ju jf`: the same at the exports `ja`, `ju`, `jf : ι`;
* `uClientSpec`, `uProviderSpec`: the sentences, protocols over untyped moves.

The plays of an untyped instance are `Strategy.ofLTS (U.lts P)`, so `LTSInv` applies directly.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core

/-- The handle allocated by a raw result `values [h]`. -/
def HEv.allocOfResult : Result → HEv Val
  | .values [h] => .alloc h
  | _ => .skip

/-- Client classifier on untyped moves: host codes `ha` (allocate), `hu` (use), `hf` (free). -/
def uClientEv {ι : Type} (ha hu hf : Nat) : Move UImp (untypedSig ι) → HEv Val
  | .inl (.ans e a) => if e.target = ha then HEv.allocOfResult a.result else .skip
  | .inl (.ask e) =>
    if e.target = hu then HEv.useOf e.args else if e.target = hf then HEv.freeOf e.args else .skip
  | .inr _ => .skip

/-- Provider classifier on untyped moves: exports `ja` (allocate), `ju` (use), `jf` (free). -/
def uProviderEv {ι : Type} [DecidableEq ι] (ja ju jf : ι) : Move UImp (untypedSig ι) → HEv Val
  | .inr (.ans f a) => if f.target = ja then HEv.allocOfResult a.result else .skip
  | .inr (.ask f) =>
    if f.target = ju then HEv.useOf f.args else if f.target = jf then HEv.freeOf f.args else .skip
  | .inl _ => .skip

/-- **The client sentence for reference handles.** -/
def uClientSpec {ι : Type} (ha hu hf : Nat) :
    Protocol (Option (List Val)) (Move UImp (untypedSig ι)) :=
  (handleProto Val .client).comap (uClientEv ha hu hf)

/-- **The provider sentence for reference handles.** -/
def uProviderSpec {ι : Type} [DecidableEq ι] (ja ju jf : ι) :
    Protocol (Option (List Val)) (Move UImp (untypedSig ι)) :=
  (handleProto Val .provider).comap (uProviderEv ja ju jf)

end Silmaril.Wasm.Resource
