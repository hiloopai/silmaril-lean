module

public import Silmaril.Wasm.Execution.Core.Soundness.StateFacts
public import Silmaril.Wasm.Validation.Check.TyOkComplete
public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # Deciding `Externaddr_ok`

`externAddrType?` computes the principal (instance) type of an external address;
`externAddrOk?` checks validity of the target type and subtyping from the principal
type. Sound unconditionally, complete for well-typed stores.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

/-- The principal (instance) type of an external address. -/
def externAddrType? (s : Store H) : ExternAddr → Option CExternType
  | .tag a => s.tags[a]?.map fun ti => .tag ti.type
  | .global a => s.globals[a]?.map fun gi => .global gi.type
  | .mem a => s.mems[a]?.map fun mi => .mem mi.type
  | .table a => s.tables[a]?.map fun ti => .table ti.type
  | .func a => s.funcs[a]?.map fun fi => .func fi.type

/-- Boolean `Externaddr_ok` checker. -/
def externAddrOk? (s : Store H) (xa : ExternAddr) (xt : CExternType) : Bool :=
  match externAddrType? s xa with
  | some xt' => ExternTypeOk.check {} xt && ExternSub.check {} xt' xt
  | none => false

/-- Pointwise `Externaddr_ok` checker. -/
def externAddrsOk? (s : Store H) : List ExternAddr → List CExternType → Bool
  | [], [] => true
  | xa :: xas, xt :: xts => externAddrOk? s xa xt && externAddrsOk? s xas xts
  | _, _ => false

theorem externAddrType?_ok {s : Store H} {xa : ExternAddr} {xt : CExternType}
    (h : externAddrType? s xa = some xt) : ExternAddrOk s xa xt := by
  cases xa <;> simp only [externAddrType?, Option.map_eq_some_iff] at h <;>
    obtain ⟨_, h, rfl⟩ := h
  · exact .tag h
  · exact .global h
  · exact .mem h
  · exact .table h
  · exact .func h

theorem externAddrOk?_sound {s : Store H} {xa : ExternAddr} {xt : CExternType}
    (h : externAddrOk? s xa xt = true) : ExternAddrOk s xa xt := by
  unfold externAddrOk? at h
  split at h
  · rename_i xt' e
    simp only [Bool.and_eq_true] at h
    exact .sub (externAddrType?_ok e) (ExternTypeOk.check_sound h.1) (ExternSub.check_sound h.2)
  · simp at h

theorem externAddrsOk?_sound {s : Store H} :
    ∀ {xas : List ExternAddr} {xts : List CExternType},
      externAddrsOk? s xas xts = true → List.Forall₂ (ExternAddrOk s) xas xts
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => by
    simp only [externAddrsOk?, Bool.and_eq_true] at h
    exact .cons (externAddrOk?_sound h.1) (externAddrsOk?_sound h.2)
  | [], _ :: _, h => by simp [externAddrsOk?] at h
  | _ :: _, [], h => by simp [externAddrsOk?] at h

theorem expand_of_defKind_func {d : DefType} (h : defKind d = some .func) :
    ∃ ps rs, Expand d (.func ps rs) := by
  simp only [defKind, Option.map_eq_some_iff] at h
  obtain ⟨st, hu, hk⟩ := h
  cases st with
  | sub fin sups ct =>
    cases ct with
    | func ps rs => exact ⟨ps, rs, ⟨hu⟩⟩
    | struct _ => simp [compKind, Ty.body] at hk
    | array _ => simp [compKind, Ty.body] at hk

/-- Principal types of a typed store are valid. -/
theorem externAddrType?_typeOk {s : Store H} (hs : StoreOk s) {xa : ExternAddr}
    {xt : CExternType} (h : externAddrType? s xa = some xt) : ExternTypeOk {} xt := by
  cases xa <;> simp only [externAddrType?, Option.map_eq_some_iff] at h <;>
    obtain ⟨i, h, rfl⟩ := h
  · exact .tag (hs.tags i (List.mem_of_getElem? h))
  · exact .global (hs.globals i (List.mem_of_getElem? h)).1
  · exact .mem (hs.mems i (List.mem_of_getElem? h)).1
  · exact .table (hs.tables i (List.mem_of_getElem? h)).1
  · obtain ⟨hdt, hk⟩ := hs.func_kind h
    obtain ⟨ps, rs, he⟩ := expand_of_defKind_func hk
    exact .func hdt he

theorem ExternAddrOk.principal {s : Store H} (hs : StoreOk s) {xa : ExternAddr}
    {xt : CExternType} (h : ExternAddrOk s xa xt) :
    ∃ xt', externAddrType? s xa = some xt' ∧ ExternSub {} xt' xt ∧ ExternTypeOk {} xt := by
  have base : ∀ {xa xt}, externAddrType? s xa = some xt →
      ∃ xt', externAddrType? s xa = some xt' ∧ ExternSub {} xt' xt ∧ ExternTypeOk {} xt :=
    fun e => ⟨_, e, .refl _ _, externAddrType?_typeOk hs e⟩
  induction h with
  | tag h => exact base (by simp [externAddrType?, h])
  | global h => exact base (by simp [externAddrType?, h])
  | mem h => exact base (by simp [externAddrType?, h])
  | table h => exact base (by simp [externAddrType?, h])
  | func h => exact base (by simp [externAddrType?, h])
  | sub _ hok hsub ih =>
    obtain ⟨xt₀, e, h₀, hmid⟩ := ih
    exact ⟨xt₀, e, ExternSub.trans TypeCtx.ok_empty hmid h₀ hsub, hok⟩

theorem externAddrOk?_complete {s : Store H} (hs : StoreOk s) {xa : ExternAddr}
    {xt : CExternType} (h : ExternAddrOk s xa xt) : externAddrOk? s xa xt = true := by
  obtain ⟨xt', e, hsub, hok⟩ := h.principal hs
  have hok' := externAddrType?_typeOk hs e
  unfold externAddrOk?
  rw [e]
  simp only [Bool.and_eq_true]
  exact ⟨ExternTypeOk.check_complete (TyOk.check_complete TypeCtx.ok_empty rfl) hok,
    ExternSub.check_complete TypeCtx.ok_empty rfl hok' hok hsub⟩

theorem externAddrOk?_iff {s : Store H} (hs : StoreOk s) {xa : ExternAddr}
    {xt : CExternType} : externAddrOk? s xa xt = true ↔ ExternAddrOk s xa xt :=
  ⟨externAddrOk?_sound, externAddrOk?_complete hs⟩

theorem externAddrsOk?_complete {s : Store H} (hs : StoreOk s) :
    ∀ {xas : List ExternAddr} {xts : List CExternType},
      List.Forall₂ (ExternAddrOk s) xas xts → externAddrsOk? s xas xts = true
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs' => by
    simp only [externAddrsOk?, Bool.and_eq_true]
    exact ⟨externAddrOk?_complete hs h, externAddrsOk?_complete hs hs'⟩

theorem externAddrsOk?_iff {s : Store H} (hs : StoreOk s) {xas : List ExternAddr}
    {xts : List CExternType} :
    externAddrsOk? s xas xts = true ↔ List.Forall₂ (ExternAddrOk s) xas xts :=
  ⟨externAddrsOk?_sound, externAddrsOk?_complete hs⟩

end Silmaril.Wasm.Execution.Core
