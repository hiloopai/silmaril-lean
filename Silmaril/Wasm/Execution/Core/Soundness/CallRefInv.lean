module

public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux
public import Silmaril.Wasm.Execution.Core.Soundness.RefTyping
public import Silmaril.Wasm.Execution.Core.Soundness.StoreClosed
public import Silmaril.Wasm.Validation.Instructions.Properties

@[expose] public section

/-! # Inversion for `call_ref` on a typed reference, modulo subtyping metatheory

`callRef_inv` (`ProgressAux.lean`) is false under the current store typing
without closedness of runtime types and a `Sub` strengthening/inversion theory.
Closedness of struct/array instance types is now part of `StoreOk`
(`structsClosed`/`arraysClosed`). This file proves `callRef_inv_of`: the
conclusion of `callRef_inv` under the same hypotheses plus two explicit
hypotheses about subtyping in the frame context `Δ = C.toTypeCtx`:

* `hV` (value transfer to closed types):
  `∀ v t, ValTo s C.toTypeCtx v t → TyOk {} t → ValOk s v t`.
  A value typed up to a `Sub Δ` chain at a closed type has that runtime type.
  (Same fact that `StateOk.redexSubOk` in `TableMemoryTyping.lean` needs.)
* `hD` (defined-type inversion along a `Sub Δ` chain into a function type
  `d`, `Expand d (.func ps rs)`):
  `∀ d₁, TyOk {} d₁ → Relation.ReflTransGen (Sub C.toTypeCtx) (Ty.defHeap d₁) (Ty.defHeap d) →
     ∃ ps' rs', Expand d₁ (.func ps' rs') ∧ ResultSub C.toTypeCtx ps.toList ps'.toList`.
  Kind preservation (a closed struct/array type is never below a function
  type) and parameter contravariance along declared supertypes.

Everything else (null, `i31`, `exn`, `host`, `extern` references, and the
projection of value-type chains onto heap-type chains) is proved here: an
abstract, non-bottom heap type is only ever below abstract heap types
(`Sub.absTop_aux`), so it is never below `defHeap d`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

/-- Abstract heap types that are not bottoms (`none`, `nofunc`, `noexn`, `noextern`). -/
def absTop : {k : TKind} → Ty k → Bool
  | _, .abs .none => false
  | _, .abs .nofunc => false
  | _, .abs .noexn => false
  | _, .abs .noextern => false
  | _, .abs _ => true
  | _, _ => false

/-- A non-bottom abstract heap type is only below non-bottom abstract heap types. -/
theorem Sub.absTop_aux {Δ : TypeCtx} {k : TKind} {a b : Ty k} (h : Sub Δ a b) :
    absTop a = true → absTop b = true := by
  apply Silmaril.Wasm.Validation.Sub.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ a b _ => absTop a = true → absTop b = true) (t := h)
  case heapTrans =>
    intro _ _ _ _ _ _ _ _ ih1 ih2 ha
    exact ih2 (ih1 ha)
  all_goals intros
  all_goals first
    | trivial
    | simp_all [absTop]

theorem rtg_absTop {Δ : TypeCtx} {a b : CHeapType} (h : Relation.ReflTransGen (Sub Δ) a b)
    (ha : absTop a = true) : absTop b = true := by
  induction h with
  | refl => exact ha
  | tail _ hs ih => exact Sub.absTop_aux hs ih

theorem absTop_defHeap (d : DefType) : absTop (Ty.defHeap d) = false := by
  simp [absTop, Ty.defHeap]

theorem sub_refv_ref_inv {Δ : TypeCtx} {n : Bool} {h : CHeapType} {x : CValType}
    (hs : Sub Δ (Ty.refv (.ref n h)) x) :
    ∃ n' h', x = .refv (.ref n' h') ∧ Sub Δ h h' := by
  cases hs with
  | refv hr =>
    cases hr with
    | refNonNull hh => exact ⟨_, _, rfl, hh⟩
    | refNull hh => exact ⟨_, _, rfl, hh⟩

/-- Project a chain of value subtypings out of a reference type onto heap types. -/
theorem rtg_refv_heap {Δ : TypeCtx} {n : Bool} {h : CHeapType} {x : CValType}
    (hc : Relation.ReflTransGen (Sub Δ) (Ty.refv (.ref n h)) x) :
    ∃ n' h', x = .refv (.ref n' h') ∧ Relation.ReflTransGen (Sub Δ) h h' := by
  induction hc with
  | refl => exact ⟨_, _, rfl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨n', h', rfl, hc⟩ := ih
    obtain ⟨n'', h'', rfl, hh⟩ := sub_refv_ref_inv hs
    exact ⟨_, _, rfl, hc.tail hh⟩

/-- A heap chain into `defHeap d` from a reference type into the nullable `defHeap d` type. -/
theorem rtg_heap_defHeap {Δ : TypeCtx} {n : Bool} {h : CHeapType} {d : DefType}
    (hc : Relation.ReflTransGen (Sub Δ) (Ty.refv (.ref n h)) (Ty.refT true (Ty.defHeap d))) :
    Relation.ReflTransGen (Sub Δ) h (Ty.defHeap d) := by
  obtain ⟨n', h', e, hc⟩ := rtg_refv_heap hc
  simp only [Ty.refT, Ty.refv.injEq, Ty.ref.injEq] at e
  obtain ⟨-, rfl⟩ := e
  exact hc

theorem abs_not_below_defHeap {Δ : TypeCtx} {n : Bool} {a : AbsHeapType} {d : DefType}
    (ha : absTop (Ty.abs a : CHeapType) = true)
    (hc : Relation.ReflTransGen (Sub Δ) (Ty.refv (.ref n (.abs a))) (Ty.refT true (Ty.defHeap d))) :
    False := by
  have := rtg_absTop (rtg_heap_defHeap hc) ha
  rw [absTop_defHeap] at this
  exact Bool.false_ne_true this

theorem valsTo_sub_valOk {s : Store H} {Δ : TypeCtx}
    (hV : ∀ (v : Val) (t : CValType), ValTo s Δ v t → TyOk {} t → ValOk s v t) :
    ∀ {vs : List Val} {ts ts' : List CValType}, List.Forall₂ (ValTo s Δ) vs ts →
      List.Forall₂ (Sub Δ) ts ts' → ResultOk {} ts' → List.Forall₂ (ValOk s) vs ts'
  | _, _, _, .nil, .nil, _ => .nil
  | _, _, _, .cons ⟨t₀, h0, hc⟩ hvs, .cons hs hss, hok =>
    .cons (hV _ _ ⟨t₀, h0, hc.tail hs⟩ (hok _ (by simp)))
      (valsTo_sub_valOk hV hvs hss (fun x hx => hok x (by simp [hx])))

/-- `call_ref` on a typed reference: null, or a function whose parameters type the
arguments. The conclusion and first four hypotheses are exactly those of
`callRef_inv`; `hV` and `hD` are the subtyping facts it is missing (see the module
doc for their meaning). -/
theorem callRef_inv_of {s : Store H} {f : Frame} {C : Context} {d : DefType}
    {ps rs : Ty (.list .val)} {vs : List Val} {r : Ref}
    (hst : StateOk s f C) (he : Expand d (.func ps rs))
    (hv : ValsTo s C.toTypeCtx vs ps.toList)
    (hr : ValTo s C.toTypeCtx (.ref r) (Ty.refT true (Ty.defHeap d)))
    (hV : ∀ (v : Val) (t : CValType), ValTo s C.toTypeCtx v t → TyOk {} t → ValOk s v t)
    (hD : ∀ d₁ : DefType, TyOk {} d₁ →
      Relation.ReflTransGen (Sub C.toTypeCtx) (Ty.defHeap d₁) (Ty.defHeap d) →
      ∃ ps' rs', Expand d₁ (.func ps' rs') ∧ ResultSub C.toTypeCtx ps.toList ps'.toList) :
    r = .null ∨ ∃ a fi ps' rs', r = .func a ∧ s.funcs[a]? = some fi ∧
      Expand fi.type (.func ps' rs') ∧ List.Forall₂ (ValOk s) vs ps'.toList := by
  have _ := he
  have hs : StoreOk s := hst.1
  obtain ⟨t₀, hv0, hc⟩ := hr
  cases hv0 with
  | @ref _ rt hro =>
  obtain ⟨rt₀, e, hrt, -⟩ := hro.principal
  have hc' : Relation.ReflTransGen (Sub C.toTypeCtx) (Ty.refv rt₀)
      (Ty.refT true (Ty.defHeap d)) := by
    rcases hrt with rfl | ⟨_, hsub⟩
    · exact hc
    · exact .head (.refv (Sub.of_empty hsub _)) hc
  cases r with
  | null => exact .inl rfl
  | i31 b =>
    cases e
    exact (abs_not_below_defHeap (by simp [absTop]) hc').elim
  | host a =>
    cases e
    exact (abs_not_below_defHeap (by simp [absTop]) hc').elim
  | extern r' =>
    cases e
    exact (abs_not_below_defHeap (by simp [absTop]) hc').elim
  | exn a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨_, _, rfl⟩ := e
    exact (abs_not_below_defHeap (by simp [absTop]) hc').elim
  | struct a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨si, h, rfl⟩ := e
    obtain ⟨ps', rs', he', -⟩ := hD si.type (hs.struct_closed h) (rtg_heap_defHeap hc')
    obtain ⟨fs, hfs, -⟩ := hs.structs si (List.mem_of_getElem? h)
    cases Expand.func_eq he' hfs
  | array a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨ai, h, rfl⟩ := e
    obtain ⟨ps', rs', he', -⟩ := hD ai.type (hs.array_closed h) (rtg_heap_defHeap hc')
    obtain ⟨ft, hft, -⟩ := hs.arrays ai (List.mem_of_getElem? h)
    cases Expand.func_eq he' hft
  | func a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨fi, h, rfl⟩ := e
    have hdt : TyOk {} fi.type := by
      cases hs.funcs fi (List.mem_of_getElem? h) with
      | wasm hdt => exact hdt
      | host hdt => exact hdt
    obtain ⟨ps', rs', he', hps⟩ := hD fi.type hdt (rtg_heap_defHeap hc')
    exact .inr ⟨a, fi, ps', rs', rfl, h, he',
      valsTo_sub_valOk hV hv hps (Expand.func_ok hdt he').1⟩

end Silmaril.Wasm.Execution.Core
