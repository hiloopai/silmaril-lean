module

public import Silmaril.Wasm.Execution.Core.Exec.ExternAddrCheck
public import Silmaril.Wasm.Execution.Core.Instantiation
public import Silmaril.Wasm.Execution.Core.Soundness.RefOkClosed
public import Silmaril.Wasm.Execution.Core.Soundness.StoreClosed

@[expose] public section

/-! # Deciding `Ref_ok`, `Val_ok` and the `$invoke` precondition

`refType?` computes the principal type of a reference (checking the inner
reference of an `extern` against `any`); `refOk?` checks validity of the target
type and subtyping from the principal type. `valOk?`/`valsOk?` lift this to
values, and `invokeOk?` decides `InvokeOk`. All checkers are sound
unconditionally and complete for well-typed stores.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

/-- The principal type of a reference, if it is typable at all. -/
def refType? (s : Store H) : Ref → Option CRefType
  | .null => some (.ref true .bot)
  | .i31 _ => some (.ref false (.abs .i31))
  | .struct a => s.structs[a]?.map fun si => .ref false (.defHeap si.type)
  | .array a => s.arrays[a]?.map fun ai => .ref false (.defHeap ai.type)
  | .func a => s.funcs[a]?.map fun fi => .ref false (.defHeap fi.type)
  | .exn a => s.exns[a]?.map fun _ => .ref false (.abs .exn)
  | .host _ => some (.ref false (.abs .any))
  | .extern r =>
    if r = .null then none else
      match refType? s r with
      | some rt => if Sub.check {} rt (.ref false (.abs .any)) then
          some (.ref false (.abs .extern)) else none
      | none => none

/-- Boolean `Ref_ok` checker. -/
def refOk? (s : Store H) (r : Ref) (rt : CRefType) : Bool :=
  match refType? s r with
  | some rt' => TyOk.check {} rt && Sub.check {} rt' rt
  | none => false

/-- Boolean `Val_ok` checker. -/
def valOk? (s : Store H) : Val → CValType → Bool
  | .num n, t => decide (t = .num n.type)
  | .vec _, t => decide (t = .vec .v128)
  | .ref r, .refv rt => refOk? s r rt
  | .ref _, _ => false

/-- Pointwise `Val_ok` checker. -/
def valsOk? (s : Store H) : List Val → List CValType → Bool
  | [], [] => true
  | v :: vs, t :: ts => valOk? s v t && valsOk? s vs ts
  | _, _ => false

/-- Boolean checker for the premises of `$invoke`. -/
def invokeOk? (s : Store H) (a : Nat) (vs : List Val) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    match fi.type.expand? with
    | some (.func ps _) => valsOk? s vs ps.toList
    | _ => false
  | none => false

theorem tyOk_any : TyOk ({} : TypeCtx) (Ty.ref false (.abs .any)) := .ref (.abs _)

theorem refType?_ok {s : Store H} :
    ∀ {r : Ref} {rt : CRefType}, refType? s r = some rt → RefOk s r rt
  | .null, _, h => by cases h; exact .null
  | .i31 b, _, h => by cases h; exact .i31 b
  | .struct a, _, h => by
    simp only [refType?, Option.map_eq_some_iff] at h
    obtain ⟨si, h, rfl⟩ := h; exact .struct h
  | .array a, _, h => by
    simp only [refType?, Option.map_eq_some_iff] at h
    obtain ⟨ai, h, rfl⟩ := h; exact .array h
  | .func a, _, h => by
    simp only [refType?, Option.map_eq_some_iff] at h
    obtain ⟨fi, h, rfl⟩ := h; exact .func h
  | .exn a, _, h => by
    simp only [refType?, Option.map_eq_some_iff] at h
    obtain ⟨ei, h, rfl⟩ := h; exact .exn h
  | .host a, _, h => by cases h; exact .host a
  | .extern r, rt, h => by
    simp only [refType?] at h
    split at h
    · simp at h
    · rename_i hn
      split at h
      · rename_i rt' e
        split at h
        · rename_i hc
          cases h
          exact .extern (.sub (refType?_ok e) tyOk_any (Sub.check_sound hc)) hn
        · simp at h
      · simp at h

theorem refType?_typeOk {s : Store H} (hs : StoreOk s) :
    ∀ {r : Ref} {rt : CRefType}, refType? s r = some rt → TyOk {} rt
  | .null, _, h => by cases h; exact .ref .bot
  | .i31 b, _, h => by cases h; exact .ref (.abs _)
  | .struct a, _, h => by
    simp only [refType?, Option.map_eq_some_iff] at h
    obtain ⟨si, h, rfl⟩ := h; exact .ref (.use (.dt (hs.struct_closed h)))
  | .array a, _, h => by
    simp only [refType?, Option.map_eq_some_iff] at h
    obtain ⟨ai, h, rfl⟩ := h; exact .ref (.use (.dt (hs.array_closed h)))
  | .func a, _, h => by
    simp only [refType?, Option.map_eq_some_iff] at h
    obtain ⟨fi, h, rfl⟩ := h; exact .ref (.use (.dt (hs.func_closed h)))
  | .exn a, _, h => by
    simp only [refType?, Option.map_eq_some_iff] at h
    obtain ⟨ei, h, rfl⟩ := h; exact .ref (.abs _)
  | .host a, _, h => by cases h; exact .ref (.abs _)
  | .extern r, rt, h => by
    simp only [refType?] at h
    split at h
    · simp at h
    · split at h
      · split at h
        · cases h; exact .ref (.abs _)
        · simp at h
      · simp at h

/-- Under a typed store, `refType?` agrees with `Ref.type?` on typable references. -/
theorem refType?_of_refOk {s : Store H} (hs : StoreOk s) :
    ∀ {r : Ref} {rt : CRefType}, RefOk s r rt → refType? s r = Ref.type? s r
  | .null, _, _ => rfl
  | .i31 _, _, _ => rfl
  | .struct _, _, _ => rfl
  | .array _, _, _ => rfl
  | .func _, _, _ => rfl
  | .exn _, _, _ => rfl
  | .host _, _, _ => rfl
  | .extern r, rt, h => by
    obtain ⟨_, _, _, hx⟩ := h.principal
    obtain ⟨hr, hn⟩ := hx r rfl
    have e := refType?_of_refOk hs hr
    obtain ⟨rt₀, e₀, hrt, -⟩ := hr.principal
    rw [← e] at e₀
    have hsub : Sub ({} : TypeCtx) rt₀ (Ty.ref false (.abs .any)) := by
      rcases hrt with h' | ⟨_, h'⟩
      · rw [← h']; exact Sub.refl _ (k := .ref) trivial _
      · exact h'
    have hc : Sub.check {} rt₀ (Ty.ref false (.abs .any)) = true :=
      Sub.check_complete TypeCtx.ok_empty rfl hsub (refType?_typeOk hs e₀) tyOk_any
    simp [refType?, hn, e₀, hc, Ref.type?]

/-- Principal typing: every typing of a reference in a typed store is a supertype of
`refType?`. -/
theorem RefOk.principal' {s : Store H} (hs : StoreOk s) {r : Ref} {rt : CRefType}
    (h : RefOk s r rt) : ∃ rt', refType? s r = some rt' ∧ Sub {} rt' rt ∧ TyOk {} rt := by
  obtain ⟨rt₀, e, hrt, -⟩ := h.principal
  rw [← refType?_of_refOk hs h] at e
  rcases hrt with rfl | ⟨hok, h'⟩
  · exact ⟨_, e, Sub.refl _ (k := .ref) trivial _, refType?_typeOk hs e⟩
  · exact ⟨_, e, h', hok⟩

theorem refOk?_sound {s : Store H} {r : Ref} {rt : CRefType} (h : refOk? s r rt = true) :
    RefOk s r rt := by
  unfold refOk? at h
  split at h
  · rename_i rt' e
    simp only [Bool.and_eq_true] at h
    exact .sub (refType?_ok e) (TyOk.check_sound h.1) (Sub.check_sound h.2)
  · simp at h

theorem refOk?_complete {s : Store H} (hs : StoreOk s) {r : Ref} {rt : CRefType}
    (h : RefOk s r rt) : refOk? s r rt = true := by
  obtain ⟨rt', e, hsub, hok⟩ := h.principal' hs
  unfold refOk?
  rw [e]
  simp only [Bool.and_eq_true]
  exact ⟨TyOk.check_complete TypeCtx.ok_empty rfl hok,
    Sub.check_complete TypeCtx.ok_empty rfl hsub (refType?_typeOk hs e) hok⟩

theorem refOk?_iff {s : Store H} (hs : StoreOk s) {r : Ref} {rt : CRefType} :
    refOk? s r rt = true ↔ RefOk s r rt :=
  ⟨refOk?_sound, refOk?_complete hs⟩

theorem valOk?_sound {s : Store H} {v : Val} {t : CValType} (h : valOk? s v t = true) :
    ValOk s v t := by
  cases v with
  | num n =>
    simp only [valOk?, decide_eq_true_eq] at h
    subst h; exact .num n
  | vec b =>
    simp only [valOk?, decide_eq_true_eq] at h
    subst h; exact .vec b
  | ref r =>
    cases t with
    | refv rt => exact .ref (refOk?_sound h)
    | _ => simp [valOk?] at h

theorem valOk?_complete {s : Store H} (hs : StoreOk s) {v : Val} {t : CValType}
    (h : ValOk s v t) : valOk? s v t = true := by
  cases h with
  | num n => simp [valOk?]
  | vec b => simp [valOk?]
  | ref h => exact refOk?_complete hs h

theorem valOk?_iff {s : Store H} (hs : StoreOk s) {v : Val} {t : CValType} :
    valOk? s v t = true ↔ ValOk s v t :=
  ⟨valOk?_sound, valOk?_complete hs⟩

theorem valsOk?_sound {s : Store H} :
    ∀ {vs : List Val} {ts : List CValType},
      valsOk? s vs ts = true → List.Forall₂ (ValOk s) vs ts
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => by
    simp only [valsOk?, Bool.and_eq_true] at h
    exact .cons (valOk?_sound h.1) (valsOk?_sound h.2)
  | [], _ :: _, h => by simp [valsOk?] at h
  | _ :: _, [], h => by simp [valsOk?] at h

theorem valsOk?_complete {s : Store H} (hs : StoreOk s) :
    ∀ {vs : List Val} {ts : List CValType},
      List.Forall₂ (ValOk s) vs ts → valsOk? s vs ts = true
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs' => by
    simp only [valsOk?, Bool.and_eq_true]
    exact ⟨valOk?_complete hs h, valsOk?_complete hs hs'⟩

theorem valsOk?_iff {s : Store H} (hs : StoreOk s) {vs : List Val} {ts : List CValType} :
    valsOk? s vs ts = true ↔ List.Forall₂ (ValOk s) vs ts :=
  ⟨valsOk?_sound, valsOk?_complete hs⟩

theorem invokeOk?_sound {s : Store H} {a : Nat} {vs : List Val}
    (h : invokeOk? s a vs = true) : InvokeOk s a vs := by
  unfold invokeOk? at h
  split at h
  · rename_i fi hf
    split at h
    · rename_i ps rs he
      exact ⟨fi, ps, rs, hf, Expand.iff.mpr he, valsOk?_sound h⟩
    · simp at h
  · simp at h

theorem invokeOk?_complete {s : Store H} (hs : StoreOk s) {a : Nat} {vs : List Val}
    (h : InvokeOk s a vs) : invokeOk? s a vs = true := by
  obtain ⟨fi, ps, rs, hf, he, hv⟩ := h
  simp only [invokeOk?, hf, Expand.iff.mp he]
  exact valsOk?_complete hs hv

theorem invokeOk?_iff {s : Store H} (hs : StoreOk s) {a : Nat} {vs : List Val} :
    invokeOk? s a vs = true ↔ InvokeOk s a vs :=
  ⟨invokeOk?_sound, invokeOk?_complete hs⟩

/-- `InvokeOk` is decidable over a typed store. -/
def decInvokeOk {s : Store H} (hs : StoreOk s) (a : Nat) (vs : List Val) :
    Decidable (InvokeOk s a vs) :=
  decidable_of_iff _ (invokeOk?_iff hs)

/-- `Ref_ok` is decidable over a typed store. -/
def decRefOk {s : Store H} (hs : StoreOk s) (r : Ref) (rt : CRefType) :
    Decidable (RefOk s r rt) :=
  decidable_of_iff _ (refOk?_iff hs)

/-- `Val_ok` is decidable over a typed store. -/
def decValOk {s : Store H} (hs : StoreOk s) (v : Val) (t : CValType) :
    Decidable (ValOk s v t) :=
  decidable_of_iff _ (valOk?_iff hs)

end Silmaril.Wasm.Execution.Core
