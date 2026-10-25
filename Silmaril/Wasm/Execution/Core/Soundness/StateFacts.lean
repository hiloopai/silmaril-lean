module

public import Silmaril.Wasm.Execution.Core.Soundness.RefTyping

@[expose] public section

/-! # Facts about typed states used by the reference/aggregate soundness units

* the typing context of a frame agrees with its module instance
  (types, functions, element and data segments);
* reference-family instruction typings are `RefInstrOk` typings;
* kinds of the instance types in a typed store.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Reference-family instructions -/

/-- The instructions typed by `RefInstrOk`. -/
def RefInstr : Instr → Prop
  | .refNull _ | .refIsNull | .refAsNonNull | .refEq | .refTest _ | .refCast _ | .refFunc _
  | .refI31 | .i31Get _ | .structNew _ | .structNewDefault _ | .structGet _ _ _
  | .structSet _ _ | .arrayNew _ | .arrayNewDefault _ | .arrayNewFixed _ _
  | .arrayNewData _ _ | .arrayNewElem _ _ | .arrayGet _ _ | .arraySet _ | .arrayLen
  | .arrayFill _ | .arrayCopy _ _ | .arrayInitData _ _ | .arrayInitElem _ _
  | .externConvertAny | .anyConvertExtern => True
  | _ => False

theorem InstrOk.refInstr {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it)
    (hi : RefInstr i) : RefInstrOk C i it := by
  cases h with
  | reference h => exact h
  | parametric h => cases h <;> simp [RefInstr] at hi
  | numeric h => cases h <;> simp [RefInstr] at hi
  | vector h => cases h <;> simp [RefInstr] at hi
  | «variable» h => cases h <;> simp [RefInstr] at hi
  | memory h => cases h <;> simp [RefInstr] at hi
  | table h => cases h <;> simp [RefInstr] at hi
  | _ => simp [RefInstr] at hi

/-! ## Module instances and frames -/

theorem ModuleInstOk.inv {s : Store H} {mi : ModuleInst} {C : Context} (h : ModuleInstOk s mi C) :
    C.types = mi.types ∧ (∀ d ∈ mi.types, TyOk {} d) ∧
    List.Forall₂ (fun a d => ExternAddrOk s (.func a) (.func d)) mi.funcs C.funcs ∧
    List.Forall₂ (fun a rt => ∃ ei, s.elems[a]? = some ei ∧ ElemInstOk s ei ∧ ei.type = rt)
      mi.elems C.elems ∧
    C.datas = mi.datas.map (fun _ => ()) ∧ (∀ a ∈ mi.datas, ∃ di, s.datas[a]? = some di) := by
  cases h with
  | mk htypes _ _ hfuncs _ _ hdatas helems => exact ⟨rfl, htypes, hfuncs, helems, rfl, hdatas⟩

theorem ModuleInstOk.typesOk {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) :
    ∀ (x : Nat) (d : DefType), C.toTypeCtx.types[x]? = some d → TyOk C.toTypeCtx d := by
  obtain ⟨ht, hok, -⟩ := h.inv
  intro x d hx
  have : d ∈ mi.types := by
    rw [← ht]; exact List.mem_of_getElem? hx
  exact TyOk.ofEmpty (hok d this) _

theorem FrameOk.inv {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    ∃ C₀, ModuleInstOk s f.module C₀ ∧ C.toTypeCtx = C₀.toTypeCtx ∧ C.funcs = C₀.funcs ∧
      C.elems = C₀.elems ∧ C.datas = C₀.datas := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := h
  exact ⟨C₀, hm, rfl, rfl, rfl, rfl⟩

theorem FrameOk.types_eq {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    C.types = f.module.types := by
  obtain ⟨C₀, hm, hΔ, -⟩ := h.inv
  have : C.types = C₀.types := congrArg TypeCtx.types hΔ
  rw [this, hm.inv.1]

theorem FrameOk.typesOk {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    ∀ (x : Nat) (d : DefType), C.toTypeCtx.types[x]? = some d → TyOk C.toTypeCtx d := by
  obtain ⟨C₀, hm, hΔ, -⟩ := h.inv
  rw [hΔ]; exact hm.typesOk

theorem FrameOk.type?_eq {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    (x : TypeIdx) : C.type? x = f.type? x := by
  simp [Context.type?, Frame.type?, h.types_eq]

theorem FrameOk.closeRef {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    (rt : RefType) : C.closeRef rt = f.module.instRef rt := by
  simp [Context.closeRef, ModuleInst.instRef, h.types_eq]

/-- Types of the context are valid in the empty context. -/
theorem FrameOk.type_ok {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    {x : TypeIdx} {d : DefType} (hx : C.type? x = some d) : TyOk {} d := by
  obtain ⟨C₀, hm, hΔ, -⟩ := h.inv
  obtain ⟨ht, hok, -⟩ := hm.inv
  have hmem : d ∈ C.types := List.mem_of_getElem? hx
  rw [h.types_eq] at hmem
  exact hok d hmem

theorem FrameOk.func {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    {x : FuncIdx} {d : DefType} (hx : C.funcs[x.toNat]? = some d) :
    ∃ a, f.module.funcs[x.toNat]? = some a ∧ ExternAddrOk s (.func a) (.func d) := by
  obtain ⟨C₀, hm, -, hf, -⟩ := h.inv
  obtain ⟨-, -, hfuncs, -⟩ := hm.inv
  rw [hf] at hx
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hx
  have hl := hfuncs.length_eq
  refine ⟨f.module.funcs[x.toNat]'(by omega), by simp, ?_⟩
  have := List.Forall₂.get hfuncs (by omega) hlt
  simpa [List.get_eq_getElem, hget] using this

theorem FrameOk.elem {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    {y : ElemIdx} {rt : CRefType} (hy : C.elems[y.toNat]? = some rt) :
    ∃ ea ei, s.elem? f y = some (ea, ei) ∧ ElemInstOk s ei ∧ ei.type = rt := by
  obtain ⟨C₀, hm, -, -, he, -⟩ := h.inv
  obtain ⟨-, -, -, helems, -⟩ := hm.inv
  rw [he] at hy
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hy
  have hl := helems.length_eq
  have := List.Forall₂.get helems (by omega) hlt
  simp only [List.get_eq_getElem, hget] at this
  obtain ⟨ei, hei, hok, hty⟩ := this
  refine ⟨f.module.elems[y.toNat]'(by omega), ei, ?_, hok, hty⟩
  simp [Store.elem?, hei, List.getElem?_eq_getElem (show y.toNat < f.module.elems.length by omega)]

theorem FrameOk.data {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    {y : DataIdx} (hy : C.datas[y.toNat]? = some ()) :
    ∃ da di, s.data? f y = some (da, di) := by
  obtain ⟨C₀, hm, -, -, -, hd⟩ := h.inv
  obtain ⟨-, -, -, -, hds, hdatas⟩ := hm.inv
  rw [hd, hds] at hy
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hy
  obtain ⟨a, ha, -⟩ := hy
  obtain ⟨di, hdi⟩ := hdatas a (List.mem_of_getElem? ha)
  exact ⟨a, di, by simp [Store.data?, ha, hdi]⟩

/-! ## Function references -/

theorem ExternAddrOk.func_ref {s : Store H} {xa : ExternAddr} {xt : CExternType}
    (h : ExternAddrOk s xa xt) :
    ∀ a d, xa = .func a → xt = .func d → RefOk s (.func a) (.ref false (.defHeap d)) := by
  induction h with
  | func h => intro a d ha hd; cases ha; cases hd; exact .func h
  | sub _ hok hs ih =>
    intro a d ha hd
    subst hd
    cases hs with
    | func hsub =>
      cases hok with
      | func hd _ => exact .sub (ih a _ ha rfl) (.ref (.use (.dt hd))) (.refNonNull (.defDef hsub))
  | _ => intro a d ha; cases ha

/-! ## Kinds of instance types -/

theorem StoreOk.func_kind {s : Store H} (hs : StoreOk s) {a : Nat} {fi : FuncInst H}
    (h : s.funcs[a]? = some fi) : TyOk {} fi.type ∧ defKind fi.type = some .func := by
  have := hs.funcs fi (List.mem_of_getElem? h)
  cases this with
  | host hdt he _ => exact ⟨hdt, expand_defKind he⟩
  | wasm hdt hm _ hf hsub =>
    refine ⟨hdt, ?_⟩
    cases hf with
    | mk hd he _ _ =>
      have hT := hm.typesOk
      have hok := hT _ _ hd
      have := Sub.up hT hsub
      dsimp only [UpMotive] at this
      exact this hok _ (expand_defKind he)

theorem StoreOk.struct_expand {s : Store H} (hs : StoreOk s) {a : Nat} {si : StructInst}
    (h : s.structs[a]? = some si) : ∃ fs, Expand si.type (.struct fs) := by
  obtain ⟨fs, he, -⟩ := hs.structs si (List.mem_of_getElem? h)
  exact ⟨fs, he⟩

theorem StoreOk.array_expand {s : Store H} (hs : StoreOk s) {a : Nat} {ai : ArrayInst}
    (h : s.arrays[a]? = some ai) : ∃ ft, Expand ai.type (.array ft) := by
  obtain ⟨ft, he, -⟩ := hs.arrays ai (List.mem_of_getElem? h)
  exact ⟨ft, he⟩

/-! ## Redexes of reference-family instructions -/

theorem RefInstrOk.inits {C : Context} {i : Instr} {it : InstrType} (h : RefInstrOk C i it) :
    it.inits = [] := by
  cases h <;> rfl

/-- `redex_inv` specialised to reference-family instructions. -/
theorem redex_ref {s : Store H} {C : Context} {i : Instr} {vs : List Val} {it : InstrType}
    (hi : RefInstr i) (hlen : ∀ it', RefInstrOk C i it' → it'.params.length = vs.length)
    (h : AdminsOk s C (vals vs ++ [.plain i]) it) :
    ∃ t₁ t₂ ts, RefInstrOk C i ⟨t₁, [], t₂⟩ ∧ List.Forall₂ (ValOk s) vs ts ∧
      ResultSub C.toTypeCtx ts t₁ ∧
      ∀ (s' : Store H) (out : List Admin), AdminsOk s' C out ⟨[], [], t₂⟩ → AdminsOk s' C out it := by
  obtain ⟨t₁, t₂, ts, h1, h2, h3, h4⟩ := redex_inv (fun it' h =>
    ⟨RefInstrOk.inits (InstrOk.refInstr h hi), hlen _ (InstrOk.refInstr h hi)⟩) h
  exact ⟨t₁, t₂, ts, InstrOk.refInstr h1 hi, h2, h3, h4⟩

theorem ValOk.refv_inv {s : Store H} {v : Val} {rt : CRefType} (h : ValOk s v (.refv rt)) :
    ∃ r, v = .ref r ∧ RefOk s r rt := by
  cases h with | ref h => exact ⟨_, rfl, h⟩

theorem ValOk.i32_invRT' {s : Store H} {v : Val} (h : ValOk s v Ty.i32) : ∃ b, v = Val.i32 b :=
  ValOk.i32_invRT (Δ := {}) h .num

theorem Sub.ref_false_le {Δ : TypeCtx} (n : Bool) (h : CHeapType) :
    Sub Δ (Ty.ref false h) (Ty.ref n h) := by
  cases n
  · exact .refNonNull .heapRefl
  · exact .refNull .heapRefl

theorem TyOk.refT_abs {Δ : TypeCtx} (n : Bool) (a : AbsHeapType) : TyOk Δ (Ty.refT n (.abs a)) :=
  .refv (.ref (.abs a))

/-- A non-null reference typed below `any` in a frame's context is typed at `any`. -/
theorem RefBase.to_any {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C) {r : Ref}
    {n : Bool} {h₀ : CHeapType} (hb : RefBase s r (.ref n h₀)) (hr : r ≠ .null)
    (hsub : Sub C.toTypeCtx h₀ (.abs .any)) : RefOk s r (.ref false (.abs .any)) := by
  have hT := hst.2.typesOk
  cases hb with
  | null => exact absurd rfl hr
  | i31 b => exact .sub (.i31 b) (.ref (.abs _)) (.refNonNull (.heapTrans (.abs _) .i31Eq .eqAny))
  | struct h =>
    obtain ⟨fs, he⟩ := hst.1.struct_expand h
    exact .sub (.struct h) (.ref (.abs _))
      (.refNonNull (.heapTrans (.abs .eq) (.heapTrans (.abs _) (.defStruct he) .structEq) .eqAny))
  | array h =>
    obtain ⟨ft, he⟩ := hst.1.array_expand h
    exact .sub (.array h) (.ref (.abs _))
      (.refNonNull (.heapTrans (.abs .eq) (.heapTrans (.abs _) (.defArray he) .arrayEq) .eqAny))
  | func h =>
    obtain ⟨hok, hk⟩ := hst.1.func_kind h
    have := Sub.up hT hsub
    dsimp only [UpMotive] at this
    have := this .func ⟨by simpa [HeapUp, useKind, Ty.defHeap] using hk,
      fun d hd => by cases hd; exact TyOk.ofEmpty hok _⟩
    simp [HeapUp, absUp] at this
  | exn h =>
    have := Sub.up hT hsub
    dsimp only [UpMotive] at this
    have := this .exn ⟨by simp [HeapUp, absUp], fun d hd => by cases hd⟩
    simp [HeapUp, absUp] at this
  | host a => exact .host a
  | extern h hn =>
    have := Sub.up hT hsub
    dsimp only [UpMotive] at this
    have := this .extern ⟨by simp [HeapUp, absUp], fun d hd => by cases hd⟩
    simp [HeapUp, absUp] at this

end Silmaril.Wasm.Execution.Core
