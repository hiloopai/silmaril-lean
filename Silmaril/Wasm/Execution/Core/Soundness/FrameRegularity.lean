module

public import Silmaril.Wasm.Execution.Core.Soundness.StateFacts
public import Silmaril.Wasm.Validation.Subtyping.Properties

@[expose] public section

/-! # Regularity of frame contexts

Primitive facts about the context `C` that `Frame_ok` assigns to a frame, to be
assembled into `CtxWf C` (`Soundness/Preservation.lean`) as `FrameOk.ctxWf`.

**Locals.** `Localval_ok/set` (spec §7.1) only requires `Val_ok: s ⊢ val : t`,
and `Ref_ok/struct` / `Ref_ok/array` type a reference at the store instance's
`TYPE dt` while `Structinst_ok` / `Arrayinst_ok` never require `{} ⊢ dt : OK`.
So `∀ lt ∈ C.locals, TyOk C.toTypeCtx lt.type` does **not** follow from
`StoreOk s ∧ FrameOk s f C`. It does follow under the extra store invariant
`StoreHeapTypesOk s` (every struct/array instance has a valid type), which is
preserved by `struct.new*`/`array.new*` since their types come from
`C.type? x` and are `TyOk {}` (`FrameOk.type_ok`).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

/-- `TyOk {} t` implies closedness (no free type indices). -/
theorem TyOk.closed_of_empty {k : TKind} {t : Ty k} (h : TyOk {} t) : t.Closed := by
  have := TyOk.freeIdx_lt h
  unfold Ty.Closed
  rcases hf : t.freeIdx with _ | ⟨y, _⟩
  · rfl
  · have := this y (by simp [hf])
    simp at this

theorem ModuleInstOk.shape {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.locals = [] ∧ C.labels = [] ∧ C.return_ = none := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem FrameOk.labels_nil {s : Store H} {f : Frame} {C : Context} (hf : FrameOk s f C) :
    C.labels = [] := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  exact hm.shape.2.1

theorem FrameOk.return_none {s : Store H} {f : Frame} {C : Context} (hf : FrameOk s f C) :
    C.return_ = none := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  exact hm.shape.2.2

/-- (1) The type field of a frame context is well formed. -/
theorem FrameOk.types_closed_okReg {s : Store H} {f : Frame} {C : Context}
    (_hs : StoreOk s) (hf : FrameOk s f C) :
    ∀ d ∈ C.types, d.Closed ∧ TyOk C.toTypeCtx d := by
  intro d hd
  obtain ⟨C₀, hm, -⟩ := hf.inv
  obtain ⟨-, hok, -⟩ := hm.inv
  rw [hf.types_eq] at hd
  exact ⟨TyOk.closed_of_empty (hok d hd), TyOk.ofEmpty (hok d hd) _⟩

/-- `TypeCtx.Ok` of a frame context. -/
theorem FrameOk.toTypeCtx_okReg {s : Store H} {f : Frame} {C : Context}
    (hs : StoreOk s) (hf : FrameOk s f C) : C.toTypeCtx.Ok :=
  FrameOk.types_closed_okReg hs hf

/-- (2) Labels of a frame context (there are none). -/
theorem FrameOk.labels_okReg {s : Store H} {f : Frame} {C : Context}
    (_hs : StoreOk s) (hf : FrameOk s f C) : ∀ ts ∈ C.labels, ResultOk C.toTypeCtx ts := by
  rw [hf.labels_nil]; simp

/-- (3) Return type of a frame context (there is none). -/
theorem FrameOk.ret_okReg {s : Store H} {f : Frame} {C : Context}
    (_hs : StoreOk s) (hf : FrameOk s f C) :
    ∀ ts, C.return_ = some ts → ResultOk C.toTypeCtx ts := by
  rw [hf.return_none]; simp

/-- (5) The module part of a frame context is a module-instance context. -/
theorem FrameOk.module_reprReg {s : Store H} {f : Frame} {C : Context}
    (hs : StoreOk s) (hf : FrameOk s f C) :
    ∃ C₀, StoreOk s ∧ ModuleInstOk s f.module C₀ ∧
      C = { C₀ with locals := C.locals, labels := C.labels, return_ := C.return_ } := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  refine ⟨C₀, hs, hm, ?_⟩
  cases C₀; rfl

/-! ## Locals -/

theorem forall₂_mem_right {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons h hs, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨a, ha, hr⟩ := forall₂_mem_right hs b hb
        exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem forall₂_getElem? {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ (i : Nat) {a : α} {b : β},
      l₁[i]? = some a → l₂[i]? = some b → R a b
  | _, _, .nil, _, _, _, ha, _ => by simp at ha
  | _, _, .cons h _, 0, _, _, ha, hb => by
      simp at ha hb; subst ha; subst hb; exact h
  | _, _, .cons _ hs, i + 1, _, _, ha, hb => by
      simp at ha hb; exact forall₂_getElem? hs i ha hb

/-- Extra store invariant: struct and array instances have valid types. -/
def StoreHeapTypesOk (s : Store H) : Prop :=
  (∀ si ∈ s.structs, TyOk {} si.type) ∧ (∀ ai ∈ s.arrays, TyOk {} ai.type)

/-- A typed reference has a valid type, given `StoreHeapTypesOk`. -/
theorem RefOk.tyOk {s : Store H} (hs : StoreOk s) (hh : StoreHeapTypesOk s) :
    ∀ {r : Ref} {rt : CRefType}, RefOk s r rt → TyOk {} rt
  | _, _, .null => .ref .bot
  | _, _, .i31 _ => .ref (.abs _)
  | _, _, .struct h => .ref (.use (.dt (hh.1 _ (List.mem_of_getElem? h))))
  | _, _, .array h => .ref (.use (.dt (hh.2 _ (List.mem_of_getElem? h))))
  | _, _, @RefOk.func _ _ _ fi h => by
      have hfi := hs.funcs _ (List.mem_of_getElem? h)
      have hdt : TyOk {} fi.type := by cases hfi <;> assumption
      exact .ref (.use (.dt hdt))
  | _, _, .exn _ => .ref (.abs _)
  | _, _, .host _ => .ref (.abs _)
  | _, _, .extern _ _ => .ref (.abs _)
  | _, _, .sub _ hok _ => hok

theorem ValOk.tyOk {s : Store H} (hs : StoreOk s) (hh : StoreHeapTypesOk s) {v : Val}
    {t : CValType} (h : ValOk s v t) : TyOk {} t := by
  cases h with
  | num => exact .num _
  | vec => exact .vec _
  | ref hr => exact .refv (hr.tyOk hs hh)

/-- An *unset* local's type is always valid (`Localval_ok/unset`). -/
theorem LocalValOk.tyOk_unset {s : Store H} {lt : LocalType} (h : LocalValOk s none lt) :
    TyOk {} lt.type := by
  cases h with
  | unset h => exact h

theorem LocalValOk.tyOk {s : Store H} (hs : StoreOk s) (hh : StoreHeapTypesOk s)
    {ov : Option Val} {lt : LocalType} (h : LocalValOk s ov lt) : TyOk {} lt.type := by
  cases h with
  | set h => exact h.tyOk hs hh
  | unset h => exact h

/-- (4) Locals of a frame context, **under the extra hypothesis** `StoreHeapTypesOk s`
(see the module doc: the field is not provable from `StoreOk` and `FrameOk` alone). -/
theorem FrameOk.locals_okReg {s : Store H} {f : Frame} {C : Context}
    (hs : StoreOk s) (hh : StoreHeapTypesOk s) (hf : FrameOk s f C) :
    ∀ lt ∈ C.locals, TyOk C.toTypeCtx lt.type := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := hf
  intro lt hlt
  simp only [hm.shape.1, List.nil_append] at hlt
  obtain ⟨ov, -, hv⟩ := forall₂_mem_right hl lt hlt
  exact TyOk.ofEmpty (hv.tyOk hs hh) _

/-- The locals whose value is `none` (unset) are always valid, without extra hypotheses;
together with `LocalValOk.set` this pins the failure of (4) to set struct/array refs. -/
theorem FrameOk.unset_locals_okReg {s : Store H} {f : Frame} {C : Context}
    (hf : FrameOk s f C) :
    ∀ (i : Nat) (lt : LocalType), f.locals[i]? = some none → C.locals[i]? = some lt →
      TyOk C.toTypeCtx lt.type := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := hf
  intro i lt hi hlt
  simp only [hm.shape.1, List.nil_append] at hlt
  have hr := forall₂_getElem? hl i hi hlt
  exact TyOk.ofEmpty hr.tyOk_unset _

end Silmaril.Wasm.Execution.Core
