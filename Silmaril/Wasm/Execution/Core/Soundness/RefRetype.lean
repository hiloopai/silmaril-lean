module

public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux
public import Silmaril.Wasm.Validation.Instructions.Properties

@[expose] public section

/-! # Retyping reference instructions at their operands' runtime types

`RefInstrOk.retype` (`ProgressAux.lean`) is false under the current `StoreOk`
(see its docstring). This file proves it under three explicit extra hypotheses:

* `hsc : ∀ si ∈ s.structs, TyOk {} si.type` (supplied by the store-closed unit
  as `StoreOk.structsClosed`);
* `hac : ∀ ai ∈ s.arrays, TyOk {} ai.type` (`StoreOk.arraysClosed`);
* `htr`, a transfer of subtyping *chains* between closed value types from the
  frame context to `{}`:

  `∀ {a b : CValType}, TyOk {} a → TyOk {} b →
     Relation.ReflTransGen (Sub C.toTypeCtx) a b → Sub {} a b`

  (`SubChainTransfer C.toTypeCtx`). A chain is needed because `ValTo` only gives
  a chain and `Sub.trans` needs a valid middle type, which `ValTo` does not
  record. Given the sub-strengthen unit's single-step transfer
  `Sub Δ a b → Sub {} a b` for closed `a b` plus validity of the intermediate
  types (or a transitivity without middle validity), this follows by collapsing
  the chain.

Strategy: every operand type of a reference instruction is closed except the
operand of `ref.is_null`/`ref.as_non_null` (retyped at the principal runtime
heap type) and of `ref.test`/`ref.cast` (retyped at the top of the operand's
hierarchy, `ref null <abs>`). Closed operand types are reached from the
(closed) type of the value by the transferred chain.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

/-- The transfer of subtyping chains between closed value types to `{}`. -/
def SubChainTransfer (Δ : TypeCtx) : Prop :=
  ∀ {a b : CValType}, TyOk {} a → TyOk {} b → Relation.ReflTransGen (Sub Δ) a b → Sub {} a b

/-! ## Closedness of runtime types -/

theorem RefBase.closed {s : Store H} (hs : StoreOk s)
    (hsc : ∀ si ∈ s.structs, TyOk {} si.type) (hac : ∀ ai ∈ s.arrays, TyOk {} ai.type)
    {r : Ref} {rt : CRefType} (hb : RefBase s r rt) : TyOk {} rt := by
  cases hb with
  | null => exact .ref .bot
  | i31 => exact .ref (.abs _)
  | struct h => exact .ref (.use (.dt (hsc _ (List.mem_of_getElem? h))))
  | array h => exact .ref (.use (.dt (hac _ (List.mem_of_getElem? h))))
  | func h => exact .ref (.use (.dt (hs.func_kind h).1))
  | exn => exact .ref (.abs _)
  | host => exact .ref (.abs _)
  | extern => exact .ref (.abs _)

theorem RefOk.closed {s : Store H} (hs : StoreOk s)
    (hsc : ∀ si ∈ s.structs, TyOk {} si.type) (hac : ∀ ai ∈ s.arrays, TyOk {} ai.type)
    {r : Ref} {rt : CRefType} (h : RefOk s r rt) : TyOk {} rt := by
  obtain ⟨rt₀, hb, h0⟩ := h.principalRT
  rcases h0 with rfl | ⟨-, hok⟩
  · exact hb.closed hs hsc hac
  · exact hok

theorem ValOk.closed {s : Store H} (hs : StoreOk s)
    (hsc : ∀ si ∈ s.structs, TyOk {} si.type) (hac : ∀ ai ∈ s.arrays, TyOk {} ai.type)
    {v : Val} {t : CValType} (h : ValOk s v t) : TyOk {} t := by
  cases h with
  | num => exact .num _
  | vec => exact .vec _
  | ref h => exact .refv (h.closed hs hsc hac)

/-- Subsumption of value typing in `{}`. -/
theorem ValOk.sub_empty {s : Store H} {v : Val} {t t' : CValType} (h : ValOk s v t)
    (hs : Sub {} t t') (ht' : TyOk {} t') : ValOk s v t' := by
  cases h with
  | num w => cases hs; exact .num w
  | vec b => cases hs; exact .vec b
  | ref h =>
    cases hs with
    | refv hs => cases ht' with | refv hok => exact .ref (.sub h hok hs)

/-- A value reaching a closed type by a chain is typed at it. -/
theorem ValTo.valOk_closed {s : Store H} {Δ : TypeCtx} (hs : StoreOk s)
    (hsc : ∀ si ∈ s.structs, TyOk {} si.type) (hac : ∀ ai ∈ s.arrays, TyOk {} ai.type)
    (htr : SubChainTransfer Δ) {v : Val} {t : CValType} (h : ValTo s Δ v t)
    (ht : TyOk {} t) : ValOk s v t := by
  obtain ⟨t₀, hv, hc⟩ := h
  exact hv.sub_empty (htr (hv.closed hs hsc hac) ht hc) ht

theorem ValsTo.valOk_closed {s : Store H} {Δ : TypeCtx} (hs : StoreOk s)
    (hsc : ∀ si ∈ s.structs, TyOk {} si.type) (hac : ∀ ai ∈ s.arrays, TyOk {} ai.type)
    (htr : SubChainTransfer Δ) {vs : List Val} {ts : List CValType} (h : ValsTo s Δ vs ts)
    (hts : ∀ t ∈ ts, TyOk {} t) : List.Forall₂ (ValOk s) vs ts := by
  induction h with
  | nil => exact .nil
  | cons ha _ ih =>
    exact .cons (ha.valOk_closed hs hsc hac htr (hts _ (by simp)))
      (ih fun t ht => hts t (by simp [ht]))

/-- A value reaching a reference type is a reference typed at `ref null h₀` for
its closed principal heap type `h₀`. -/
theorem ValTo.ref_principal {s : Store H} {Δ : TypeCtx} (hs : StoreOk s)
    (hsc : ∀ si ∈ s.structs, TyOk {} si.type) (hac : ∀ ai ∈ s.arrays, TyOk {} ai.type)
    {v : Val} {rt : CRefType} (h : ValTo s Δ v (.refv rt)) :
    ∃ r h₀, v = .ref r ∧ RefOk s r (.ref true h₀) ∧ TyOk {} h₀ := by
  obtain ⟨t₀, hv, hc⟩ := h
  rcases sub_ref_inv hc with ⟨rt', rfl⟩ | rfl
  · cases hv with
    | ref hr =>
      obtain ⟨rt₀, hb, -⟩ := hr.principalRT
      have hok := hb.closed hs hsc hac
      cases rt₀ with
      | ref n₀ h₀ =>
        cases hok with
        | ref hh => exact ⟨_, h₀, rfl, .sub hb.refOk (.ref hh) (.refNull .heapRefl), hh⟩
  · cases hv

/-! ## Tops of heap-type hierarchies -/

theorem TyOk.exists_expand {Δ : TypeCtx} {d : DefType} (hd : TyOk Δ d) : ∃ ct, Expand d ct := by
  cases hd with
  | @defn _ subs i hg hi =>
    have hi' : i < subs.toList.length := by simpa [Ty.length] using hi
    obtain ⟨st, hst⟩ : ∃ st, subs.toList[i]? = some st := ⟨_, List.getElem?_eq_getElem hi'⟩
    cases st with
    | sub fin sups ct =>
      refine ⟨ct.subst (unrollSubst subs), .mk (fin := fin) (sups := sups.subst (unrollSubst subs)) ?_⟩
      rw [unrolldt_defn, hst]; rfl

theorem Sub.def_top {Δ : TypeCtx} {d : DefType} {ct : CCompType} (he : Expand d ct) :
    Sub Δ (.use (.dt d) : CHeapType) (.abs (compKind ct)) := by
  cases ct with
  | struct fs => exact .defStruct he
  | array f => exact .defArray he
  | func ps rs => exact .defFunc he

/-- Every valid heap type lies below an abstract heap type. -/
theorem Sub.heap_top {Δ : TypeCtx}
    (hT : ∀ (x : Nat) (d : DefType), Δ.types[x]? = some d → TyOk Δ d)
    {h : CHeapType} (hh : TyOk Δ h) : ∃ a, Sub Δ h (.abs a) := by
  cases hh with
  | abs a => exact ⟨a, .heapRefl⟩
  | bot => exact ⟨.any, .bot⟩
  | use hu =>
    cases hu with
    | idx hx =>
      obtain ⟨ct, he⟩ := TyOk.exists_expand (hT _ _ hx)
      exact ⟨_, .idxL hx (Sub.def_top he)⟩
    | @recv _ i st hr =>
      cases st with
      | sub fin sups ct =>
        cases ct with
        | struct fs => exact ⟨_, .recStruct hr⟩
        | array f => exact ⟨_, .recArray hr⟩
        | func ps rs => exact ⟨_, .recFunc hr⟩
    | dt hd =>
      obtain ⟨ct, he⟩ := TyOk.exists_expand hd
      exact ⟨_, Sub.def_top he⟩

/-! ## Retyping -/

/-- `RefInstrOk.retype` under explicit closedness/transfer hypotheses.

Extra hypotheses (to be discharged once the store-closed and sub-strengthen
units land):
* `hsc : ∀ si ∈ s.structs, TyOk {} si.type` — `hst.1.structsClosed`;
* `hac : ∀ ai ∈ s.arrays, TyOk {} ai.type` — `hst.1.arraysClosed`;
* `htr : SubChainTransfer C.toTypeCtx`, i.e.
  `∀ {a b : CValType}, TyOk {} a → TyOk {} b →
     Relation.ReflTransGen (Sub C.toTypeCtx) a b → Sub {} a b`. -/
theorem RefInstrOk.retype_of {s : Store H} {f : Frame} {C : Context} {i : Instr}
    {t₁ t₂ : List CValType} {xs : List Nat} {vs : List Val}
    (hst : StateOk s f C) (hi : RefInstrOk C i ⟨t₁, xs, t₂⟩)
    (hv : ValsTo s C.toTypeCtx vs t₁)
    (hsc : ∀ si ∈ s.structs, TyOk {} si.type) (hac : ∀ ai ∈ s.arrays, TyOk {} ai.type)
    (htr : SubChainTransfer C.toTypeCtx) :
    ∃ t₁' xs' t₂', RefInstrOk C i ⟨t₁', xs', t₂'⟩ ∧ List.Forall₂ (ValOk s) vs t₁' := by
  have hs := hst.1
  have hT := hst.2.typesOk
  have hdef : ∀ {x : TypeIdx} {d : DefType}, C.type? x = some d → TyOk {} d :=
    fun hx => hst.2.type_ok hx
  have hi' := hi
  cases hi with
  | refIsNull hh =>
    cases hv with
    | cons h1 hn =>
      cases hn
      obtain ⟨r, h₀, rfl, hr, hh0⟩ := ValTo.ref_principal hs hsc hac h1
      exact ⟨[.refT true h₀], _, _, .refIsNull (TyOk.ofEmpty hh0 _), .cons (.ref hr) .nil⟩
  | refAsNonNull hh =>
    cases hv with
    | cons h1 hn =>
      cases hn
      obtain ⟨r, h₀, rfl, hr, hh0⟩ := ValTo.ref_principal hs hsc hac h1
      exact ⟨[.refT true h₀], _, _, .refAsNonNull (TyOk.ofEmpty hh0 _), .cons (.ref hr) .nil⟩
  | @refTest rt rt' hok hok' hsub =>
    cases hv with
    | cons h1 hn =>
      cases hn
      cases rt' with
      | ref n h' =>
        have hh' : TyOk C.toTypeCtx h' := by cases hok' with | ref hh => exact hh
        obtain ⟨a, htop⟩ := Sub.heap_top hT hh'
        obtain ⟨t₀, hv0, hc⟩ := h1
        refine ⟨[.refv (.ref true (.abs a))], _, _,
          .refTest hok (.ref (.abs a)) (Sub.trans_ref hok' hsub (.refNull htop)), .cons ?_ .nil⟩
        exact ValTo.valOk_closed hs hsc hac htr ⟨t₀, hv0, hc.tail (.refv (.refNull htop))⟩
          (.refv (.ref (.abs a)))
  | @refCast rt rt' hok hok' hsub =>
    cases hv with
    | cons h1 hn =>
      cases hn
      cases rt' with
      | ref n h' =>
        have hh' : TyOk C.toTypeCtx h' := by cases hok' with | ref hh => exact hh
        obtain ⟨a, htop⟩ := Sub.heap_top hT hh'
        obtain ⟨t₀, hv0, hc⟩ := h1
        refine ⟨[.refv (.ref true (.abs a))], _, _,
          .refCast hok (.ref (.abs a)) (Sub.trans_ref hok' hsub (.refNull htop)), .cons ?_ .nil⟩
        exact ValTo.valOk_closed hs hsc hac htr ⟨t₀, hv0, hc.tail (.refv (.refNull htop))⟩
          (.refv (.ref (.abs a)))
  | structNew hd he =>
    refine ⟨_, _, _, hi', ValsTo.valOk_closed hs hsc hac htr hv ?_⟩
    intro t ht
    obtain ⟨fl, hfl, rfl⟩ := List.mem_map.mp ht
    exact TyOk.fieldUnpack (Expand.struct_ok (hdef hd) he fl hfl)
  | arrayNewFixed hd he =>
    refine ⟨_, _, _, hi', ValsTo.valOk_closed hs hsc hac htr hv ?_⟩
    intro t ht
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp ht
    exact TyOk.unpack (Expand.array_ok (hdef hd) he)
  | @structSet x fi d fs z hd he hfi =>
    refine ⟨_, _, _, hi', ValsTo.valOk_closed hs hsc hac htr hv ?_⟩
    have hf := Expand.struct_ok (hdef hd) he _ (List.mem_of_getElem? hfi)
    have hz : TyOk {} z.unpack := by cases hf with | field h => exact TyOk.unpack h
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact .refv (.ref (.use (.dt (hdef hd))))
    · exact hz
  | _ =>
    refine ⟨_, _, _, hi', ValsTo.valOk_closed hs hsc hac htr hv ?_⟩
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    repeat' rcases ht with rfl | ht
    all_goals first
      | exact .num _
      | exact TyOk.refT_abs _ _
      | exact .refv (.ref (.use (.dt (hdef ‹_›))))
      | exact TyOk.unpack (Expand.array_ok (hdef ‹_›) ‹_›)

end Silmaril.Wasm.Execution.Core
