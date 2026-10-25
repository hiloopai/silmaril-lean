module

public import Silmaril.Wasm.Execution.Core.Soundness.RefRetype
public import Silmaril.Wasm.Execution.Core.Soundness.ValToClosed

@[expose] public section

/-! # Retyping reference instructions (closed)

`RefInstrOk.retype`: `RefInstrOk.retype_of` (`RefRetype.lean`) with its extra
hypotheses discharged: `hsc`/`hac` are `StoreOk.structsClosed`/`arraysClosed`,
and the (false in general) `SubChainTransfer` is replaced by
`StateOk.valTo_valOk` (`ValToClosed.lean`), which transfers chains starting at a
value's principal runtime type.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

variable {s : Store H} {f : Frame} {C : Context} {i : Instr} {t₁ t₂ : List CValType}
  {xs : List Nat} {vs : List Val}

/-- Retyping of reference instructions at their operands' runtime types. -/
theorem RefInstrOk.retype (hst : StateOk s f C) (hi : RefInstrOk C i ⟨t₁, xs, t₂⟩)
    (hv : ValsTo s C.toTypeCtx vs t₁) :
    ∃ t₁' xs' t₂', RefInstrOk C i ⟨t₁', xs', t₂'⟩ ∧ List.Forall₂ (ValOk s) vs t₁' := by
  have hs := hst.1
  have hsc : ∀ si ∈ s.structs, TyOk {} si.type := hs.structsClosed
  have hac : ∀ ai ∈ s.arrays, TyOk {} ai.type := hs.arraysClosed
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
        exact hst.valTo_valOk ⟨t₀, hv0, hc.tail (.refv (.refNull htop))⟩
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
        exact hst.valTo_valOk ⟨t₀, hv0, hc.tail (.refv (.refNull htop))⟩
          (.refv (.ref (.abs a)))
  | structNew hd he =>
    refine ⟨_, _, _, hi', hst.valsTo_valOk hv ?_⟩
    intro t ht
    obtain ⟨fl, hfl, rfl⟩ := List.mem_map.mp ht
    exact TyOk.fieldUnpack (Expand.struct_ok (hdef hd) he fl hfl)
  | arrayNewFixed hd he =>
    refine ⟨_, _, _, hi', hst.valsTo_valOk hv ?_⟩
    intro t ht
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp ht
    exact TyOk.unpack (Expand.array_ok (hdef hd) he)
  | @structSet x fi d fs z hd he hfi =>
    refine ⟨_, _, _, hi', hst.valsTo_valOk hv ?_⟩
    have hf := Expand.struct_ok (hdef hd) he _ (List.mem_of_getElem? hfi)
    have hz : TyOk {} z.unpack := by cases hf with | field h => exact TyOk.unpack h
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact .refv (.ref (.use (.dt (hdef hd))))
    · exact hz
  | _ =>
    refine ⟨_, _, _, hi', hst.valsTo_valOk hv ?_⟩
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    repeat' rcases ht with rfl | ht
    all_goals first
      | exact .num _
      | exact TyOk.refT_abs _ _
      | exact .refv (.ref (.use (.dt (hdef ‹_›))))
      | exact TyOk.unpack (Expand.array_ok (hdef ‹_›) ‹_›)

end Silmaril.Wasm.Execution.Core
