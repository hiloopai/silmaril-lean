module

public import Silmaril.Wasm.Execution.Core.Soundness.RefOkClosed
public import Silmaril.Wasm.Execution.Core.Soundness.StateFacts
public import Silmaril.Wasm.Validation.Subtyping.Closed

@[expose] public section

/-! # Values reaching closed types are typed at them

Replaces the (false) `sub_strengthen_closed_stub` and `SubChainTransfer`: a chain
`Sub C.toTypeCtx`-subtypings from a value's runtime type to a closed type is
transferred to `{}` by starting from the value's *principal* runtime type, which is
closed and never an abstract bottom (`Ty.NoBotAbs`), and applying
`Sub.chain_to_empty_val` (`Validation/Subtyping/Closed.lean`).

`ValTo`/`ValsTo` live in `ProgressAux.lean`, which (transitively) imports
`TableMemoryTyping.lean`, a client of this file; so the statements below use the
unfolded form of `ValTo` (definitionally equal).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

/-- The type context of a well-typed state is closed and valid in `{}`. -/
theorem StateOk.emptyOk {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C) :
    C.toTypeCtx.EmptyOk := fun d hd =>
  have h := hst.2.types_tyOk_empty d hd
  ⟨SubClosed.closed_of_empty h, h⟩

theorem RefBase.closed_of_storeOk {s : Store H} (hs : StoreOk s) {r : Ref} {rt : CRefType}
    (hb : RefBase s r rt) : TyOk {} rt := by
  cases hb with
  | null => exact .ref .bot
  | i31 => exact .ref (.abs _)
  | struct h => exact .ref (.use (.dt (hs.struct_closed h)))
  | array h => exact .ref (.use (.dt (hs.array_closed h)))
  | func h => exact .ref (.use (.dt (hs.func_closed h)))
  | exn => exact .ref (.abs _)
  | host => exact .ref (.abs _)
  | extern => exact .ref (.abs _)

theorem RefBase.noBotAbs {s : Store H} {r : Ref} {rt : CRefType} (hb : RefBase s r rt) :
    rt.NoBotAbs := by
  cases hb <;> simp [Ty.NoBotAbs, Ty.defHeap]

/-- A value reaching a closed type by a chain of subtypings in the context of a
well-typed state is typed at that type. (`h` is `ValTo s C.toTypeCtx v t`.) -/
theorem StateOk.valTo_valOk {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C)
    {v : Val} {t : CValType}
    (h : ∃ t₀, ValOk s v t₀ ∧ Relation.ReflTransGen (Sub C.toTypeCtx) t₀ t)
    (ht : TyOk {} t) : ValOk s v t := by
  obtain ⟨t₀, hv, hc⟩ := h
  cases hv with
  | num w =>
    have : ∀ c, Relation.ReflTransGen (Sub C.toTypeCtx) (Ty.num w.type : CValType) c →
        c = .num w.type := by
      intro c hc
      induction hc with
      | refl => rfl
      | tail _ hs ih => subst ih; cases hs; rfl
    rw [this _ hc]; exact .num w
  | vec b =>
    have : ∀ c, Relation.ReflTransGen (Sub C.toTypeCtx) (Ty.vec .v128 : CValType) c →
        c = .vec .v128 := by
      intro c hc
      induction hc with
      | refl => rfl
      | tail _ hs ih => subst ih; cases hs; rfl
    rw [this _ hc]; exact .vec b
  | @ref r rt hr =>
    obtain ⟨rt₀, hb, h0⟩ := hr.principalRT
    have hc' : Relation.ReflTransGen (Sub C.toTypeCtx) (.refv rt₀ : CValType) t := by
      rcases h0 with rfl | ⟨hs0, -⟩
      · exact hc
      · exact Relation.ReflTransGen.head (.refv (Sub.of_empty hs0 _)) hc
    have hok := hb.closed_of_storeOk hst.1
    have hs := Sub.chain_to_empty_val (StateOk.emptyOk hst) hc' (.refv hok) ht hb.noBotAbs
    cases hs with
    | refv hs => cases ht with | refv ht => exact .ref (.sub hb.refOk ht hs)

/-- List form of `StateOk.valTo_valOk`. (`h` is `ValsTo s C.toTypeCtx vs ts`.) -/
theorem StateOk.valsTo_valOk {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C)
    {vs : List Val} {ts : List CValType}
    (h : List.Forall₂ (fun v t => ∃ t₀, ValOk s v t₀ ∧
      Relation.ReflTransGen (Sub C.toTypeCtx) t₀ t) vs ts)
    (hts : ∀ t ∈ ts, TyOk {} t) : List.Forall₂ (ValOk s) vs ts := by
  induction h with
  | nil => exact .nil
  | cons ha _ ih =>
    exact .cons (hst.valTo_valOk ha (hts _ (by simp)))
      (ih fun t ht => hts t (by simp [ht]))

end Silmaril.Wasm.Execution.Core
