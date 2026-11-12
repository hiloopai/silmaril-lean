module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Basic
public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# Round 7, the export swap: the type encoders build no `EXPORTS` records

A copy of `Round7/ExpEnc/Types.lean` with `nxB` (no record has an `EXPORTS` field) in place of
`efB` (every `EXPORTS` field is `[]`). The proofs are unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm

@[simp] theorem nxB_numType (t : NumType) : nxB (Encode.toValue t) = true := by
  rcases t with (_ | _) | (_ | _) <;> rfl

@[simp] theorem nxB_idx {k : IndexKind} (x : Idx k) : nxB (Encode.toValue x) = true := rfl

@[simp] theorem nxB_heapType (t : HeapType) : nxB (Encode.toValue t) = true := by
  rcases t with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) | x <;> rfl

@[simp] theorem nxB_refType (t : RefType) : nxB (Encode.toValue t) = true := by
  obtain ⟨n, h⟩ := t
  cases n <;> rcases h with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) | x <;> rfl

@[simp] theorem nxB_vecType (t : VecType) : nxB (Encode.toValue t) = true := by cases t; rfl

@[simp] theorem nxB_absHeapType (t : AbsHeapType) : nxB (Encode.toValue t) = true := by cases t <;> rfl

@[simp] theorem nxB_valType (t : ValType) : nxB (Encode.toValue t) = true := by
  rcases t with t | t | t
  · exact nxB_numType t
  · exact nxB_vecType t
  · exact nxB_refType t

@[simp] theorem nxB_packType (t : PackType) : nxB (Encode.toValue t) = true := by cases t <;> rfl

@[simp] theorem nxB_addrType (t : AddrType) : nxB (Encode.toValue t) = true := by cases t <;> rfl

@[simp] theorem nxB_mutability (t : Mutability) : nxB (Encode.toValue t) = true := by cases t <;> rfl

@[simp] theorem nxB_fin64 (x : Fin (2 ^ 64)) : nxB (Encode.toValue x) = true := rfl

@[simp] theorem nxB_limits (l : Limits) : nxB (Encode.toValue l) = true := by
  obtain ⟨n, m⟩ := l
  cases m <;> rfl

@[simp] theorem nxB_memoryType (t : MemoryType) : nxB (Encode.toValue t) = true := by
  obtain ⟨a, ⟨n, m⟩⟩ := t
  cases a <;> cases m <;> rfl

@[simp] theorem nxB_blockType (t : BlockType) : nxB (Encode.toValue t) = true := by
  rcases t with _ | t | x
  · rfl
  · exact nxB_valType t
  · rfl

@[simp] theorem nxB_catch (c : Catch) : nxB (Encode.toValue c) = true := by cases c <;> rfl

open Silmaril.SpecTec.Equiv.Validation in
@[simp] theorem nxB_tyV : ∀ {k : Validation.TKind} (t : Validation.Ty k), nxB (tyV t) = true
  | _, .nil => rfl
  | _, .cons a l => by
    have ha := nxB_tyV a
    have hl := nxB_tyV l
    simp only [tyV, consV] at hl ⊢
    split
    · simp_all
    · simp_all
  | _, .idx _ => rfl
  | _, .recv _ => rfl
  | _, .dt d => nxB_tyV d
  | _, .defn g _ => by simp [tyV, nxB_tyV g, natV]
  | _, .abs a => by cases a <;> rfl
  | _, .bot => rfl
  | _, .use u => nxB_tyV u
  | _, .ref n h => by cases n <;> simp [tyV, nxB_tyV h, nullV]
  | _, .num t => by rcases t with (_ | _) | (_ | _) <;> rfl
  | _, .vec t => by cases t; rfl
  | _, .refv r => nxB_tyV r
  | _, .botv => rfl
  | _, .val t => nxB_tyV t
  | _, .pack p => by cases p <;> rfl
  | _, .field m s => by cases m <;> simp [tyV, nxB_tyV s, mutV]
  | _, .struct fs => by simp [tyV, nxB_tyV fs, Silmaril.SpecTec.Sem.percentV, caseV]
  | _, .array f => by simp [tyV, nxB_tyV f]
  | _, .func ps rs => by simp [tyV, nxB_tyV ps, nxB_tyV rs, Silmaril.SpecTec.Sem.percentV, caseV]
  | _, .sub fin sups ct => by cases fin <;> simp [tyV, nxB_tyV sups, nxB_tyV ct, finalV]
  | _, .group subs => by simp [tyV, nxB_tyV subs, Silmaril.SpecTec.Sem.percentV, caseV]

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
