module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.ExpEnc.Basic
public import Silmaril.Wasm.SpecTec.Sim.Defs

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm

@[simp] theorem efB_numType (t : NumType) : efB (Encode.toValue t) = true := by
  rcases t with (_ | _) | (_ | _) <;> rfl

@[simp] theorem efB_idx {k : IndexKind} (x : Idx k) : efB (Encode.toValue x) = true := rfl

@[simp] theorem efB_heapType (t : HeapType) : efB (Encode.toValue t) = true := by
  rcases t with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) | x <;> rfl

@[simp] theorem efB_refType (t : RefType) : efB (Encode.toValue t) = true := by
  obtain ⟨n, h⟩ := t
  cases n <;> rcases h with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) | x <;> rfl

@[simp] theorem efB_vecType (t : VecType) : efB (Encode.toValue t) = true := by cases t; rfl

@[simp] theorem efB_absHeapType (t : AbsHeapType) : efB (Encode.toValue t) = true := by cases t <;> rfl

@[simp] theorem efB_valType (t : ValType) : efB (Encode.toValue t) = true := by
  rcases t with t | t | t
  · exact efB_numType t
  · exact efB_vecType t
  · exact efB_refType t

@[simp] theorem efB_packType (t : PackType) : efB (Encode.toValue t) = true := by cases t <;> rfl

@[simp] theorem efB_addrType (t : AddrType) : efB (Encode.toValue t) = true := by cases t <;> rfl

@[simp] theorem efB_mutability (t : Mutability) : efB (Encode.toValue t) = true := by cases t <;> rfl

@[simp] theorem efB_fin64 (x : Fin (2 ^ 64)) : efB (Encode.toValue x) = true := rfl

@[simp] theorem efB_limits (l : Limits) : efB (Encode.toValue l) = true := by
  obtain ⟨n, m⟩ := l
  cases m <;> rfl

@[simp] theorem efB_memoryType (t : MemoryType) : efB (Encode.toValue t) = true := by
  obtain ⟨a, ⟨n, m⟩⟩ := t
  cases a <;> cases m <;> rfl

@[simp] theorem efB_blockType (t : BlockType) : efB (Encode.toValue t) = true := by
  rcases t with _ | t | x
  · rfl
  · exact efB_valType t
  · rfl

@[simp] theorem efB_catch (c : Catch) : efB (Encode.toValue c) = true := by cases c <;> rfl

open Silmaril.SpecTec.Equiv.Validation in
@[simp] theorem efB_tyV : ∀ {k : Validation.TKind} (t : Validation.Ty k), efB (tyV t) = true
  | _, .nil => rfl
  | _, .cons a l => by
    have ha := efB_tyV a
    have hl := efB_tyV l
    simp only [tyV, consV] at hl ⊢
    split
    · simp_all
    · simp_all
  | _, .idx _ => rfl
  | _, .recv _ => rfl
  | _, .dt d => efB_tyV d
  | _, .defn g _ => by simp [tyV, efB_tyV g, natV]
  | _, .abs a => by cases a <;> rfl
  | _, .bot => rfl
  | _, .use u => efB_tyV u
  | _, .ref n h => by cases n <;> simp [tyV, efB_tyV h, nullV]
  | _, .num t => by rcases t with (_ | _) | (_ | _) <;> rfl
  | _, .vec t => by cases t; rfl
  | _, .refv r => efB_tyV r
  | _, .botv => rfl
  | _, .val t => efB_tyV t
  | _, .pack p => by cases p <;> rfl
  | _, .field m s => by cases m <;> simp [tyV, efB_tyV s, mutV]
  | _, .struct fs => by simp [tyV, efB_tyV fs, Silmaril.SpecTec.Sem.percentV, caseV]
  | _, .array f => by simp [tyV, efB_tyV f]
  | _, .func ps rs => by simp [tyV, efB_tyV ps, efB_tyV rs, Silmaril.SpecTec.Sem.percentV, caseV]
  | _, .sub fin sups ct => by cases fin <;> simp [tyV, efB_tyV sups, efB_tyV ct, finalV]
  | _, .group subs => by simp [tyV, efB_tyV subs, Silmaril.SpecTec.Sem.percentV, caseV]

end Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc
