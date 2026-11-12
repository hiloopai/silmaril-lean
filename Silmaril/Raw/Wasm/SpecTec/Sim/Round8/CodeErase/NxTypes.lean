module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.CodeErase.Value
public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# Round 8 (copy of round 7 for `CODE` fields), the export swap: the type encoders build no `CODE` records

Copied mechanically from round 7 (export erasure) with `EXPORTS` read as `CODE` and
`eraseV` as `eraseC`; where the prose below speaks of export lists, module records or the swap
set `QC c`, it describes the original. Here every value is in the swap set (`fun _ => True`).

A copy of `Round7/ExpEnc/Types.lean` with `ncB` (no record has an `CODE` field) in place of
`efB` (every `CODE` field is `[]`). The proofs are unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm

@[simp] theorem ncB_numType (t : NumType) : ncB (Encode.toValue t) = true := by
  rcases t with (_ | _) | (_ | _) <;> rfl

@[simp] theorem ncB_idx {k : IndexKind} (x : Idx k) : ncB (Encode.toValue x) = true := rfl

@[simp] theorem ncB_heapType (t : HeapType) : ncB (Encode.toValue t) = true := by
  rcases t with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) | x <;> rfl

@[simp] theorem ncB_refType (t : RefType) : ncB (Encode.toValue t) = true := by
  obtain ⟨n, h⟩ := t
  cases n <;> rcases h with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) | x <;> rfl

@[simp] theorem ncB_vecType (t : VecType) : ncB (Encode.toValue t) = true := by cases t; rfl

@[simp] theorem ncB_absHeapType (t : AbsHeapType) : ncB (Encode.toValue t) = true := by cases t <;> rfl

@[simp] theorem ncB_valType (t : ValType) : ncB (Encode.toValue t) = true := by
  rcases t with t | t | t
  · exact ncB_numType t
  · exact ncB_vecType t
  · exact ncB_refType t

@[simp] theorem ncB_packType (t : PackType) : ncB (Encode.toValue t) = true := by cases t <;> rfl

@[simp] theorem ncB_addrType (t : AddrType) : ncB (Encode.toValue t) = true := by cases t <;> rfl

@[simp] theorem ncB_mutability (t : Mutability) : ncB (Encode.toValue t) = true := by cases t <;> rfl

@[simp] theorem ncB_fin64 (x : Fin (2 ^ 64)) : ncB (Encode.toValue x) = true := rfl

@[simp] theorem ncB_limits (l : Limits) : ncB (Encode.toValue l) = true := by
  obtain ⟨n, m⟩ := l
  cases m <;> rfl

@[simp] theorem ncB_memoryType (t : MemoryType) : ncB (Encode.toValue t) = true := by
  obtain ⟨a, ⟨n, m⟩⟩ := t
  cases a <;> cases m <;> rfl

@[simp] theorem ncB_blockType (t : BlockType) : ncB (Encode.toValue t) = true := by
  rcases t with _ | t | x
  · rfl
  · exact ncB_valType t
  · rfl

@[simp] theorem ncB_catch (c : Catch) : ncB (Encode.toValue c) = true := by cases c <;> rfl

open Silmaril.SpecTec.Equiv.Validation in
@[simp] theorem ncB_tyV : ∀ {k : Validation.TKind} (t : Validation.Ty k), ncB (tyV t) = true
  | _, .nil => rfl
  | _, .cons a l => by
    have ha := ncB_tyV a
    have hl := ncB_tyV l
    simp only [tyV, consV] at hl ⊢
    split
    · simp_all
    · simp_all
  | _, .idx _ => rfl
  | _, .recv _ => rfl
  | _, .dt d => ncB_tyV d
  | _, .defn g _ => by simp [tyV, ncB_tyV g, natV]
  | _, .abs a => by cases a <;> rfl
  | _, .bot => rfl
  | _, .use u => ncB_tyV u
  | _, .ref n h => by cases n <;> simp [tyV, ncB_tyV h, nullV]
  | _, .num t => by rcases t with (_ | _) | (_ | _) <;> rfl
  | _, .vec t => by cases t; rfl
  | _, .refv r => ncB_tyV r
  | _, .botv => rfl
  | _, .val t => ncB_tyV t
  | _, .pack p => by cases p <;> rfl
  | _, .field m s => by cases m <;> simp [tyV, ncB_tyV s, mutV]
  | _, .struct fs => by simp [tyV, ncB_tyV fs, Silmaril.SpecTec.Sem.percentV, caseV]
  | _, .array f => by simp [tyV, ncB_tyV f]
  | _, .func ps rs => by simp [tyV, ncB_tyV ps, ncB_tyV rs, Silmaril.SpecTec.Sem.percentV, caseV]
  | _, .sub fin sups ct => by cases fin <;> simp [tyV, ncB_tyV sups, ncB_tyV ct, finalV]
  | _, .group subs => by simp [tyV, ncB_tyV subs, Silmaril.SpecTec.Sem.percentV, caseV]

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
