module

public import Silmaril.Wasm.Execution.Core.Soundness.StoreClosed

@[expose] public section

/-! # Runtime reference types are closed

Under `StoreOk`, every runtime type of a reference (`Ref_ok`) or value
(`Val_ok`) is valid in the empty context. Struct/array instance types rely on
the `StoreOk.structsClosed`/`StoreOk.arraysClosed` deviation; function instance
types on `Funcinst_ok` (`FuncInstOk.hdt`).

(The former `sub_strengthen_closed_stub` was false, since `RECS` is unconstrained;
it is replaced by `StateOk.valTo_valOk` in `ValToClosed.lean`.)
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

theorem FuncInstOk.type_closed {s : Store H} {fi : FuncInst H} (h : FuncInstOk s fi) :
    TyOk {} fi.type := by
  cases h with
  | wasm hdt => exact hdt
  | host hdt => exact hdt

theorem StoreOk.func_closed {s : Store H} (hs : StoreOk s) {a : Nat} {fi : FuncInst H}
    (h : s.funcs[a]? = some fi) : TyOk {} fi.type :=
  (hs.funcs fi (List.mem_of_getElem? h)).type_closed

/-- Every runtime type of a reference is closed. -/
theorem RefOk.tyOk_empty {s : Store H} (hs : StoreOk s) {r : Ref} {rt : CRefType}
    (h : RefOk s r rt) : TyOk {} rt := by
  induction h with
  | null => exact .ref .bot
  | i31 _ => exact .ref (.abs _)
  | struct h => exact .ref (.use (.dt (hs.struct_closed h)))
  | array h => exact .ref (.use (.dt (hs.array_closed h)))
  | func h => exact .ref (.use (.dt (hs.func_closed h)))
  | exn _ => exact .ref (.abs _)
  | host _ => exact .ref (.abs _)
  | extern _ _ _ => exact .ref (.abs _)
  | sub _ hok _ _ => exact hok

/-- Every runtime type of a value is closed. -/
theorem ValOk.tyOk_empty {s : Store H} (hs : StoreOk s) {v : Val} {t : CValType}
    (h : ValOk s v t) : TyOk {} t := by
  cases h with
  | num n => exact .num _
  | vec _ => exact .vec _
  | ref h => exact .refv (h.tyOk_empty hs)

/-- The defined types of a frame context are valid in the empty context. -/
theorem FrameOk.types_tyOk_empty {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    ∀ d ∈ C.toTypeCtx.types, TyOk {} d := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := h
  cases hm with
  | mk htypes => exact htypes

end Silmaril.Wasm.Execution.Core
