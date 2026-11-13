module

public import Silmaril.Wasm.Component.Reference.Link.Defs

/-!
# Soundness of two linked components: definitions

For `l : Linked2` (the exporter `l.exp` answering the importer `l.imp`'s imports, wired by
`l.wire`), the reference side is the parent component `l.toRef`, instantiated without imports
and called at export `j`; the IR side is the denotation of `l.toComp` over `impSem P`, which
has no imports.

* `linkHost impl`: a reference host without ready host waitables and with host functions
  `impl` (`l.toRef` imports nothing, so `impl` is never called; `refHost P` is the instance
  with no host functions and host state `()`);
* `Linked2.IRObs P l j vs b`: what the IR must exhibit for the reference outcome `b` of calling
  export `j` of `l.toRef` on the reference images of `vs`: a returned call answers the IR values
  whose images are the results, a trap answers `none`, in the two-move play of `l.toComp`.
  Divergence and deadlock impose nothing.

* `Linked2.seqMoves`, `Linked2.SeqIRObs`: the IR play of a sequence of resolved calls on one
  instance of the linked component, and what the IR must exhibit for the last call.

Proved (`Silmaril.Wasm.Component.Reference.LinkSound.Thms`): `Linked2.sound`, for single calls, and
`Linked2.sound_seq`, for sequences of calls on one instance.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

/-- A reference host without ready host waitables and with the host functions `impl`. -/
def linkHost {P : Profile} {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) : Host (core3P P) σ :=
  { hr := fun _ _ => false, impl := impl }

namespace Linked2

/-- **What the IR must exhibit for a reference outcome** `b` of calling export `j` of the
linked component on `vs`: the results of a returned call are the reference images of IR values
`ws` and the IR plays `ask (j, vals vs) · ans (vals ws)`; a trap is the play answering `none`. -/
def IRObs (P : Profile) (l : Linked2) (j : Fin l.imp.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) : Outcome → Prop
  | .returns (some rs) => ∃ ws : List Silmaril.Wasm.Component.Val, rs = ws.map toRefVal ∧
      [.inr (.ask (⟨j, by simp [exports_length_toComp]⟩, .vals vs)),
        .inr (.ans (m := (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) (some (.vals ws)))] ∈
        l.toComp.den (impSem P)
  | .traps =>
      [.inr (.ask (⟨j, by simp [exports_length_toComp]⟩, .vals vs)),
        .inr (.ans (m := (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) none)] ∈
        l.toComp.den (impSem P)
  | _ => True

/-- **The IR play of resolved calls** `calls` of the linked component with IR results `wss`:
for each call, `ask (j, vals vs) · ans (vals ws)`. -/
def seqMoves (l : Linked2) :
    List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val) →
    List (List Silmaril.Wasm.Component.Val) →
    List (Silmaril.Games.Move l.toComp.imports.sig
      (Silmaril.Wasm.Component.sigN l.toComp.exports.length))
  | (j, vs) :: cs, ws :: wss =>
    .inr (.ask (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) ::
      .inr (.ans (m := (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) (some (.vals ws))) ::
      seqMoves l cs wss
  | _, _ => []

/-- **What the IR must exhibit for the last call of a sequence** with reference outcome `b`,
after the resolved calls `calls` with IR results `wss`: for returned results, the IR play of all
calls; for a trap, the IR play of the earlier calls followed by `ask (j, vals vs) · ans none`.
Divergence, deadlock and cancellation impose nothing. -/
def SeqIRObs (P : Profile) (l : Linked2)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (wss : List (List Silmaril.Wasm.Component.Val)) (j : Fin l.imp.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) : Outcome → Prop
  | .returns (some rs) => ∃ ws : List Silmaril.Wasm.Component.Val, rs = ws.map toRefVal ∧
      seqMoves l (calls ++ [(j, vs)]) (wss ++ [ws]) ∈ l.toComp.den (impSem P)
  | .traps => seqMoves l calls wss ++
      [.inr (.ask (⟨j, by simp [exports_length_toComp]⟩, .vals vs)),
        .inr (.ans (m := (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) none)] ∈
        l.toComp.den (impSem P)
  | _ => True

end Linked2

end Silmaril.Wasm.Component.Reference
